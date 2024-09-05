//! An implementation for the string data structure described in [Umbra: A Disk-Based System with In-Memory Performance].
//!
//! [Umbra: A Disk-Based System with In-Memory Performance]: https://www.cidrdb.org/cidr2020/papers/p29-neumann-cidr20.pdf

#![warn(
    rustdoc::all,
    clippy::cargo,
    clippy::pedantic,
    clippy::nursery,
    missing_debug_implementations
)]
#![deny(clippy::all, missing_docs, rust_2018_idioms, rust_2021_compatibility)]

#[cfg(feature = "serde")]
pub mod serde;

mod heap;

use std::{borrow::Borrow, cmp, mem::ManuallyDrop};

use heap::{SharedDynBytes, ThinAsBytes, ThinClone, ThinDrop, UniqueDynBytes};

const INLINED_LENGTH: usize = 12;
const PREFIX_LENGTH: usize = 4;
const SUFFIX_LENGTH: usize = 8;

/// A type for all possible errors that can occur when using [`UmbraString`].
#[derive(Debug)]
pub enum Error {
    /// An error occurs when converting from a string whose length exceeds the maximum value of a
    /// 32-bit unsigned integer.
    TooLong,
}

impl std::error::Error for Error {}
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TooLong => write!(f, "String is too long"),
        }
    }
}

union Trailing<B> {
    buf: [u8; SUFFIX_LENGTH],
    ptr: ManuallyDrop<B>,
}

/// # Safety:
///
/// + The inlined content is always copied.
/// + The heap-allocated content is `Send`.
unsafe impl<B> Send for Trailing<B> where B: Send {}

/// # Safety:
///
/// + The inlined content is immutable.
/// + The heap-allocated content is `Sync`.
unsafe impl<B> Sync for Trailing<B> where B: Sync {}

/// An Umbra-style string that owns its underlying bytes and does not share the bytes among
/// different instances.
pub type UniqueString = UmbraString<UniqueDynBytes>;

/// An Umbra-style string that shares its underlying bytes and keeps track of the number of
/// references using an atomic counter.
pub type SharedString = UmbraString<SharedDynBytes>;

/// A string data structure optimized for analytical processing workload. Unlike [`String`], which
/// uses 24 bytes on the stack, this data structure uses only 16 bytes and is immutable.
#[repr(C)]
pub struct UmbraString<B: ThinDrop> {
    len: u32,
    prefix: [u8; PREFIX_LENGTH],
    trailing: Trailing<B>,
}

/// # Safety:
///
/// + `len` is always copied.
/// + The heap-allocated bytes are `Send`.
unsafe impl<B> Send for UmbraString<B> where B: ThinDrop + Send {}

/// # Safety:
///
/// + `len` is immutable.
/// + The heap-allocated bytes are `Sync`.
unsafe impl<B> Sync for UmbraString<B> where B: ThinDrop + Sync {}

impl<B> Drop for UmbraString<B>
where
    B: ThinDrop,
{
    fn drop(&mut self) {
        let len = self.len();
        if len > INLINED_LENGTH {
            // Safety:
            // + We know that the string is heap-allocated because len > INLINED_LENGTH.
            // + We never modify `len`, thus it always equals to the number of allocated bytes.
            unsafe {
                self.trailing.ptr.thin_drop(len);
            }
        }
    }
}

impl<B> Clone for UmbraString<B>
where
    B: ThinDrop + ThinClone,
{
    fn clone(&self) -> Self {
        let len = self.len();
        let trailing = if len <= INLINED_LENGTH {
            // Safety:
            // + We know that the string is inlined because len <= INLINED_LENGTH.
            unsafe {
                Trailing {
                    buf: self.trailing.buf,
                }
            }
        } else {
            // Safety:
            // + We know that the string is heap-allocated because len > INLINED_LENGTH.
            unsafe {
                Trailing {
                    ptr: ManuallyDrop::new(self.trailing.ptr.thin_clone(len)),
                }
            }
        };
        Self {
            len: self.len,
            prefix: self.prefix,
            trailing,
        }
    }
}

impl<B> TryFrom<&str> for UmbraString<B>
where
    B: ThinDrop + for<'a> From<&'a [u8]>,
{
    type Error = Error;

    #[inline]
    fn try_from(s: &str) -> Result<Self, Self::Error> {
        Self::new(s, |s| B::from(s.as_bytes()))
    }
}

impl<B> TryFrom<&String> for UmbraString<B>
where
    B: ThinDrop + for<'a> From<&'a [u8]>,
{
    type Error = Error;

    #[inline]
    fn try_from(s: &String) -> Result<Self, Self::Error> {
        Self::new(s, |s| B::from(s.as_bytes()))
    }
}

impl<B> TryFrom<String> for UmbraString<B>
where
    B: ThinDrop + From<Vec<u8>>,
{
    type Error = Error;

    #[inline]
    fn try_from(s: String) -> Result<Self, Self::Error> {
        Self::new(s, |s| B::from(s.into_bytes()))
    }
}

impl<B> std::ops::Deref for UmbraString<B>
where
    B: ThinDrop + ThinAsBytes,
{
    type Target = str;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_str()
    }
}

impl<B> AsRef<str> for UmbraString<B>
where
    B: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl<B> Borrow<str> for UmbraString<B>
where
    B: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

impl<B> std::hash::Hash for UmbraString<B>
where
    B: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn hash<H>(&self, hasher: &mut H)
    where
        H: std::hash::Hasher,
    {
        self.as_str().hash(hasher);
    }
}

impl<B> Eq for UmbraString<B> where B: ThinDrop + ThinAsBytes {}
impl<B1, B2> PartialEq<UmbraString<B2>> for UmbraString<B1>
where
    B1: ThinDrop + ThinAsBytes,
    B2: ThinDrop + ThinAsBytes,
{
    fn eq(&self, other: &UmbraString<B2>) -> bool {
        let lhs_first_qword = std::ptr::from_ref(self).cast::<u64>();
        let rhs_first_qword = std::ptr::from_ref(other).cast::<u64>();
        // Safety:
        // + The pointers are obtained from the given references and guaranteed to be non-null and
        // properly aligned.
        // + The first QWORD contains the string length and prefix based on the layout, guaranteed
        // by `#[repr(C)]`.
        // + The referenced objects are immutable and are not changed concurrently.
        if unsafe { *lhs_first_qword != *rhs_first_qword } {
            return false;
        }
        if self.len() <= INLINED_LENGTH {
            // Safety:
            // + We know that the string is inlined because len <= INLINED_LENGTH.
            return unsafe { self.trailing.buf == other.trailing.buf };
        }
        self.suffix() == other.suffix()
    }
}

impl<B> PartialEq<str> for UmbraString<B>
where
    B: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn eq(&self, other: &str) -> bool {
        self.as_bytes() == other.as_bytes()
    }
}

impl<B> PartialEq<UmbraString<B>> for str
where
    B: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn eq(&self, other: &UmbraString<B>) -> bool {
        self.as_bytes() == other.as_bytes()
    }
}

impl<B> PartialEq<String> for UmbraString<B>
where
    B: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn eq(&self, other: &String) -> bool {
        self.as_bytes() == other.as_bytes()
    }
}

impl<B> PartialEq<UmbraString<B>> for String
where
    B: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn eq(&self, other: &UmbraString<B>) -> bool {
        self.as_bytes() == other.as_bytes()
    }
}

impl<B> Ord for UmbraString<B>
where
    B: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        Self::cmp(self, other)
    }
}

impl<B1, B2> PartialOrd<UmbraString<B2>> for UmbraString<B1>
where
    B1: ThinDrop + ThinAsBytes,
    B2: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn partial_cmp(&self, other: &UmbraString<B2>) -> Option<cmp::Ordering> {
        Some(Self::cmp(self, other))
    }
}

impl<B> PartialOrd<str> for UmbraString<B>
where
    B: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn partial_cmp(&self, other: &str) -> Option<cmp::Ordering> {
        PartialOrd::partial_cmp(self.as_bytes(), other.as_bytes())
    }
}

impl<B> PartialOrd<UmbraString<B>> for str
where
    B: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn partial_cmp(&self, other: &UmbraString<B>) -> Option<cmp::Ordering> {
        PartialOrd::partial_cmp(self.as_bytes(), other.as_bytes())
    }
}

impl<B> PartialOrd<String> for UmbraString<B>
where
    B: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn partial_cmp(&self, other: &String) -> Option<cmp::Ordering> {
        PartialOrd::partial_cmp(self.as_bytes(), other.as_bytes())
    }
}

impl<B> PartialOrd<UmbraString<B>> for String
where
    B: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn partial_cmp(&self, other: &UmbraString<B>) -> Option<cmp::Ordering> {
        PartialOrd::partial_cmp(self.as_bytes(), other.as_bytes())
    }
}

impl<B> std::fmt::Display for UmbraString<B>
where
    B: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

impl<B> std::fmt::Debug for UmbraString<B>
where
    B: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.as_str())
    }
}

impl<B> UmbraString<B>
where
    B: ThinDrop,
{
    /// Returns the length of `self`.
    ///
    /// This length is in bytes, not [`char`]s or graphemes. In other words,
    /// it might not be what a human considers the length of the string.
    #[inline]
    pub const fn len(&self) -> usize {
        self.len as usize
    }

    /// Returns `true` if `self` has a length of zero bytes.
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    fn new<S, A>(s: S, alloc: A) -> Result<Self, Error>
    where
        S: AsRef<str>,
        A: FnOnce(S) -> B,
    {
        let bytes = s.as_ref().as_bytes();
        let len = bytes.len();
        if len > u32::MAX as usize {
            return Err(Error::TooLong);
        }
        let mut prefix = [0u8; PREFIX_LENGTH];
        let trailing = if len <= INLINED_LENGTH {
            let mut buf = [0u8; SUFFIX_LENGTH];
            if len <= PREFIX_LENGTH {
                prefix[..len].copy_from_slice(&bytes[..len]);
            } else {
                prefix.copy_from_slice(&bytes[..PREFIX_LENGTH]);
                buf[..len - PREFIX_LENGTH].copy_from_slice(&bytes[PREFIX_LENGTH..]);
            }
            Trailing { buf }
        } else {
            prefix.copy_from_slice(&bytes[..PREFIX_LENGTH]);
            Trailing {
                ptr: ManuallyDrop::new(alloc(s)),
            }
        };
        #[allow(clippy::cast_possible_truncation)]
        Ok(Self {
            len: len as u32,
            prefix,
            trailing,
        })
    }
}
impl<B> UmbraString<B>
where
    B: ThinDrop + ThinAsBytes,
{
    /// Converts `self` to a byte slice.
    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        let len = self.len();
        if len <= INLINED_LENGTH {
            // Note: If we cast from a reference to a pointer, we can only access memory that was
            // within the bounds of the reference. This is done to satisfied miri when we create a
            // slice starting from the pointer of self.prefix to access data beyond it.
            let ptr = std::ptr::from_ref(self);
            // Safety:
            // + We know that the string is inlined because len <= INLINED_LENGTH.
            // + We can create a slice starting from the pointer to self.prefix with a length of at
            // most PREFIX_LENGTH because we have an inlined suffix of 8 bytes after the prefix.
            unsafe { std::slice::from_raw_parts(std::ptr::addr_of!((*ptr).prefix).cast(), len) }
        } else {
            // Safety:
            // + We know that the string is heap-allocated because len > INLINED_LENGTH.
            // + We never modify `len`, thus it always equals to the number of allocated bytes.
            unsafe { self.trailing.ptr.thin_as_bytes(len) }
        }
    }

    /// Extracts a string slice containing the entire [`UmbraString`].
    #[inline]
    pub fn as_str(&self) -> &str {
        // Safety:
        // + We always construct the string using valid UTF-8 bytes.
        unsafe { std::str::from_utf8_unchecked(self.as_bytes()) }
    }

    #[inline]
    fn suffix(&self) -> &[u8] {
        let len = self.len();
        if len <= INLINED_LENGTH {
            // Safety:
            // + We know that the string is inlined because len <= INLINED_LENGTH.
            let suffix_len = len.saturating_sub(PREFIX_LENGTH);
            unsafe { self.trailing.buf.get_unchecked(..suffix_len) }
        } else {
            // Safety:
            // + We know that the string is heap-allocated because len > INLINED_LENGTH.
            // + We never modify `len`, thus it always equals to the number of allocated bytes.
            // + We can slice into the bytes without bound checks because len > PREFIX_LENGTH.
            unsafe {
                self.trailing
                    .ptr
                    .thin_as_bytes(len)
                    .get_unchecked(PREFIX_LENGTH..)
            }
        }
    }

    fn cmp<BB>(lhs: &Self, rhs: &UmbraString<BB>) -> cmp::Ordering
    where
        BB: ThinDrop + ThinAsBytes,
    {
        let prefix_ordering = Ord::cmp(&lhs.prefix, &rhs.prefix);
        if prefix_ordering != cmp::Ordering::Equal {
            return prefix_ordering;
        }
        let lhs_len = lhs.len();
        let rhs_len = rhs.len();
        if lhs_len <= PREFIX_LENGTH && rhs_len <= PREFIX_LENGTH {
            return Ord::cmp(&lhs.len, &rhs.len);
        }
        if lhs_len <= INLINED_LENGTH && rhs_len <= INLINED_LENGTH {
            // Safety:
            // + We know that the string is inlined because len <= INLINED_LENGTH.
            let suffix_ordering = unsafe { Ord::cmp(&lhs.trailing.buf, &rhs.trailing.buf) };
            if suffix_ordering != cmp::Ordering::Equal {
                return suffix_ordering;
            }
            return Ord::cmp(&lhs.len, &rhs.len);
        }
        Ord::cmp(lhs.suffix(), rhs.suffix())
    }
}

#[cfg(test)]
mod tests {
    use std::{cmp, thread};

    use super::{SharedString, UniqueString};
    use quickcheck_macros::quickcheck;

    #[test]
    fn test_size_of() {
        assert_eq!(16, std::mem::size_of::<UniqueString>());
        assert_eq!(16, std::mem::size_of::<SharedString>());
    }

    #[test]
    fn test_construct_inlined() {
        let unique = UniqueString::try_from("hello world").expect("A valid Umbra-style string");
        let shared = SharedString::try_from("hello world").expect("A valid Umbra-style string");
        assert_eq!("hello world", unique.as_ref());
        assert_eq!("hello world", shared.as_ref());
    }

    #[test]
    fn test_construct_allocated() {
        let unique =
            UniqueString::try_from("Good Morning, Vietnam").expect("A valid Umbra-style string");
        let shared =
            SharedString::try_from("Good Morning, Vietnam").expect("A valid Umbra-style string");
        assert_eq!("Good Morning, Vietnam", unique.as_ref());
        assert_eq!("Good Morning, Vietnam", shared.as_ref());
    }

    #[test]
    fn test_move_across_threads_inlined() {
        let unique = UniqueString::try_from("hello world").expect("A valid Umbra-style string");
        let shared = SharedString::try_from("hello world").expect("A valid Umbra-style string");

        let handles: Vec<_> = (0..8)
            .map(|_| {
                let cloned0 = unique.clone();
                let cloned1 = shared.clone();
                thread::spawn(move || assert_eq!(cloned0, cloned1))
            })
            .collect();

        for handle in handles {
            handle.join().expect("Thread finishes successfully");
        }
    }

    #[test]
    fn test_move_across_threads_allocated() {
        let unique =
            UniqueString::try_from("Good Morning, Vietnam").expect("A valid Umbra-style string");
        let shared =
            SharedString::try_from("Good Morning, Vietnam").expect("A valid Umbra-style string");

        let handles: Vec<_> = (0..8)
            .map(|_| {
                let cloned0 = unique.clone();
                let cloned1 = shared.clone();
                thread::spawn(move || assert_eq!(cloned0, cloned1))
            })
            .collect();

        for handle in handles {
            handle.join().expect("Thread finishes successfully");
        }
    }

    #[test]
    fn test_eq_string_different_length_with_null_byte() {
        let assert = |lhs: &str, rhs: &str| {
            let unique_lhs = UniqueString::try_from(lhs).expect("A valid Umbra-style string");
            let unique_rhs = UniqueString::try_from(rhs).expect("A valid Umbra-style string");
            let shared_lhs = SharedString::try_from(lhs).expect("A valid Umbra-style string");
            let shared_rhs = SharedString::try_from(rhs).expect("A valid Umbra-style string");
            assert_ne!(unique_lhs, unique_rhs);
            assert_ne!(unique_lhs, shared_rhs);
            assert_ne!(shared_lhs, shared_rhs);
            assert_ne!(shared_lhs, unique_rhs);
        };
        assert("abc", "abc\0");
        assert("abc\0", "abc");
        assert("abcdefghijk", "abcdefghijk\0");
        assert("abcdefghijk\0", "abcdefghijk");
    }

    #[test]
    fn test_cmp_string_different_length_with_null_byte() {
        let assert = |lhs: &str, rhs: &str| {
            let unique_lhs = UniqueString::try_from(lhs).expect("A valid Umbra-style string");
            let unique_rhs = UniqueString::try_from(rhs).expect("A valid Umbra-style string");
            let shared_lhs = SharedString::try_from(lhs).expect("A valid Umbra-style string");
            let shared_rhs = SharedString::try_from(rhs).expect("A valid Umbra-style string");
            assert_eq!(Ord::cmp(lhs, rhs), Ord::cmp(&unique_lhs, &unique_rhs));
            assert_eq!(
                PartialOrd::partial_cmp(lhs, rhs),
                PartialOrd::partial_cmp(&unique_lhs, &shared_rhs)
            );
            assert_eq!(Ord::cmp(lhs, rhs), Ord::cmp(&shared_lhs, &shared_rhs));
            assert_eq!(
                PartialOrd::partial_cmp(lhs, rhs),
                PartialOrd::partial_cmp(&shared_lhs, &unique_rhs)
            );
        };
        assert("abc", "abc\0");
        assert("abc\0", "abc");
        assert("abcdefghijk", "abcdefghijk\0");
        assert("abcdefghijk\0", "abcdefghijk");
    }

    #[quickcheck]
    #[cfg_attr(miri, ignore)]
    #[allow(clippy::needless_pass_by_value)]
    fn test_format_debug(s: String) {
        let expected = format!("{s:?}");
        let unique = UniqueString::try_from(s.as_str()).expect("A valid Umbra-style string");
        let shared = SharedString::try_from(s.as_str()).expect("A valid Umbra-style string");
        assert_eq!(expected, format!("{unique:?}"));
        assert_eq!(expected, format!("{shared:?}"));
    }

    #[quickcheck]
    #[cfg_attr(miri, ignore)]
    #[allow(clippy::needless_pass_by_value)]
    fn test_format_display(s: String) {
        let unique = UniqueString::try_from(s.as_str()).expect("A valid Umbra-style string");
        let shared = SharedString::try_from(s.as_str()).expect("A valid Umbra-style string");
        assert_eq!(s, format!("{unique}"));
        assert_eq!(s, format!("{shared}"));
    }

    #[quickcheck]
    #[cfg_attr(miri, ignore)]
    #[allow(clippy::needless_pass_by_value)]
    fn test_eq(s: String) {
        let unique = UniqueString::try_from(s.as_str()).expect("A valid Umbra-style string");
        let shared = SharedString::try_from(s.as_str()).expect("A valid Umbra-style string");
        assert_eq!(unique, unique);
        assert_eq!(unique, shared);
        assert_eq!(shared, unique);
        assert_eq!(shared, shared);
    }

    #[quickcheck]
    #[cfg_attr(miri, ignore)]
    #[allow(clippy::needless_pass_by_value)]
    fn test_eq_str(s: String) {
        let unique = UniqueString::try_from(s.as_str()).expect("A valid Umbra-style string");
        let shared = SharedString::try_from(s.as_str()).expect("A valid Umbra-style string");
        assert_eq!(s.as_str(), &unique);
        assert_eq!(s.as_str(), &shared);
    }

    #[quickcheck]
    #[cfg_attr(miri, ignore)]
    #[allow(clippy::needless_pass_by_value)]
    fn test_eq_string(s: String) {
        let unique = UniqueString::try_from(s.as_str()).expect("A valid Umbra-style string");
        let shared = SharedString::try_from(s.as_str()).expect("A valid Umbra-style string");
        assert_eq!(s, unique);
        assert_eq!(s, shared);
    }

    #[quickcheck]
    #[cfg_attr(miri, ignore)]
    #[allow(clippy::needless_pass_by_value)]
    fn test_ne(s1: String, s2: String) {
        let lhs_unique = UniqueString::try_from(s1.as_str()).expect("A valid Umbra-style string");
        let rhs_unique = UniqueString::try_from(s2.as_str()).expect("A valid Umbra-style string");
        let lhs_shared = SharedString::try_from(s1.as_str()).expect("A valid Umbra-style string");
        let rhs_shared = SharedString::try_from(s2.as_str()).expect("A valid Umbra-style string");
        assert_ne!(lhs_unique, rhs_unique);
        assert_ne!(lhs_unique, rhs_shared);
        assert_ne!(lhs_shared, rhs_unique);
        assert_ne!(lhs_shared, rhs_shared);
    }

    #[quickcheck]
    #[cfg_attr(miri, ignore)]
    #[allow(clippy::needless_pass_by_value)]
    fn test_ne_str(s1: String, s2: String) {
        let lhs_unique = UniqueString::try_from(s1.as_str()).expect("A valid Umbra-style string");
        let rhs_unique = UniqueString::try_from(s2.as_str()).expect("A valid Umbra-style string");
        let lhs_shared = SharedString::try_from(s1.as_str()).expect("A valid Umbra-style string");
        let rhs_shared = SharedString::try_from(s2.as_str()).expect("A valid Umbra-style string");
        assert_ne!(s1.as_str(), &rhs_unique);
        assert_ne!(s1.as_str(), &rhs_shared);
        assert_ne!(&lhs_unique, s2.as_str());
        assert_ne!(&lhs_shared, s2.as_str());
    }

    #[quickcheck]
    #[cfg_attr(miri, ignore)]
    #[allow(clippy::needless_pass_by_value)]
    fn test_ne_string(s1: String, s2: String) {
        let lhs_unique = UniqueString::try_from(s1.as_str()).expect("A valid Umbra-style string");
        let rhs_unique = UniqueString::try_from(s2.as_str()).expect("A valid Umbra-style string");
        let lhs_shared = SharedString::try_from(s1.as_str()).expect("A valid Umbra-style string");
        let rhs_shared = SharedString::try_from(s2.as_str()).expect("A valid Umbra-style string");
        assert_ne!(s1, rhs_unique);
        assert_ne!(s1, rhs_shared);
        assert_ne!(lhs_unique, s2);
        assert_ne!(lhs_shared, s2);
    }

    #[quickcheck]
    #[cfg_attr(miri, ignore)]
    #[allow(clippy::needless_pass_by_value)]
    fn test_cmp_same(s: String) {
        let unique = UniqueString::try_from(s.as_str()).expect("A valid Umbra-style string");
        let shared = SharedString::try_from(s.as_str()).expect("A valid Umbra-style string");
        assert_eq!(cmp::Ordering::Equal, unique.cmp(&unique));
        assert_eq!(cmp::Ordering::Equal, shared.cmp(&shared));
        assert_eq!(Some(cmp::Ordering::Equal), unique.partial_cmp(&shared));
        assert_eq!(Some(cmp::Ordering::Equal), shared.partial_cmp(&unique));
    }

    #[quickcheck]
    #[cfg_attr(miri, ignore)]
    #[allow(clippy::needless_pass_by_value)]
    fn test_cmp_same_str(s: String) {
        let unique = UniqueString::try_from(s.as_str()).expect("A valid Umbra-style string");
        let shared = SharedString::try_from(s.as_str()).expect("A valid Umbra-style string");
        assert_eq!(Some(cmp::Ordering::Equal), unique.partial_cmp(s.as_str()));
        assert_eq!(Some(cmp::Ordering::Equal), shared.partial_cmp(s.as_str()));
        assert_eq!(Some(cmp::Ordering::Equal), s.as_str().partial_cmp(&unique));
        assert_eq!(Some(cmp::Ordering::Equal), s.as_str().partial_cmp(&shared));
    }

    #[quickcheck]
    #[cfg_attr(miri, ignore)]
    #[allow(clippy::needless_pass_by_value)]
    fn test_cmp_same_string(s: String) {
        let unique = UniqueString::try_from(s.as_str()).expect("A valid Umbra-style string");
        let shared = SharedString::try_from(s.as_str()).expect("A valid Umbra-style string");
        assert_eq!(Some(cmp::Ordering::Equal), unique.partial_cmp(&s));
        assert_eq!(Some(cmp::Ordering::Equal), shared.partial_cmp(&s));
        assert_eq!(Some(cmp::Ordering::Equal), s.partial_cmp(&unique));
        assert_eq!(Some(cmp::Ordering::Equal), s.partial_cmp(&shared));
    }

    #[quickcheck]
    #[cfg_attr(miri, ignore)]
    #[allow(clippy::needless_pass_by_value)]
    fn test_cmp_diff(s1: String, s2: String) {
        let lhs_unique = UniqueString::try_from(s1.as_str()).expect("A valid Umbra-style string");
        let rhs_unique = UniqueString::try_from(s2.as_str()).expect("A valid Umbra-style string");
        let lhs_shared = SharedString::try_from(s1.as_str()).expect("A valid Umbra-style string");
        let rhs_shared = SharedString::try_from(s2.as_str()).expect("A valid Umbra-style string");
        assert_eq!(s1.cmp(&s2), lhs_unique.cmp(&rhs_unique));
        assert_eq!(s1.cmp(&s2), lhs_shared.cmp(&rhs_shared));
        assert_eq!(s1.partial_cmp(&s2), lhs_unique.partial_cmp(&rhs_shared));
        assert_eq!(s1.partial_cmp(&s2), lhs_shared.partial_cmp(&rhs_unique));
    }

    #[quickcheck]
    #[cfg_attr(miri, ignore)]
    #[allow(clippy::needless_pass_by_value)]
    fn test_cmp_diff_str(s1: String, s2: String) {
        let lhs_unique = UniqueString::try_from(s1.as_str()).expect("A valid Umbra-style string");
        let rhs_unique = UniqueString::try_from(s2.as_str()).expect("A valid Umbra-style string");
        let lhs_shared = SharedString::try_from(s1.as_str()).expect("A valid Umbra-style string");
        let rhs_shared = SharedString::try_from(s2.as_str()).expect("A valid Umbra-style string");
        assert_eq!(s1.partial_cmp(&s2), s1.as_str().partial_cmp(&rhs_unique));
        assert_eq!(s1.partial_cmp(&s2), s1.as_str().partial_cmp(&rhs_shared));
        assert_eq!(s1.partial_cmp(&s2), lhs_unique.partial_cmp(s2.as_str()));
        assert_eq!(s1.partial_cmp(&s2), lhs_shared.partial_cmp(s2.as_str()));
    }

    #[quickcheck]
    #[cfg_attr(miri, ignore)]
    #[allow(clippy::needless_pass_by_value)]
    fn test_cmp_diff_string(s1: String, s2: String) {
        let lhs_unique = UniqueString::try_from(s1.as_str()).expect("A valid Umbra-style string");
        let rhs_unique = UniqueString::try_from(s2.as_str()).expect("A valid Umbra-style string");
        let lhs_shared = SharedString::try_from(s1.as_str()).expect("A valid Umbra-style string");
        let rhs_shared = SharedString::try_from(s2.as_str()).expect("A valid Umbra-style string");
        assert_eq!(s1.partial_cmp(&s2), s1.partial_cmp(&rhs_unique));
        assert_eq!(s1.partial_cmp(&s2), s1.partial_cmp(&rhs_shared));
        assert_eq!(s1.partial_cmp(&s2), lhs_unique.partial_cmp(&s2));
        assert_eq!(s1.partial_cmp(&s2), lhs_shared.partial_cmp(&s2));
    }
}

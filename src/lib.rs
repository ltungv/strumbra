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

use heap::{ArcDynBytes, BoxDynBytes, RcDynBytes, ThinAsBytes, ThinClone, ThinDrop};

const SUFFIX_LENGTH: usize = std::mem::size_of::<usize>();

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

#[repr(C)]
union Trailing<B> {
    buf: [u8; SUFFIX_LENGTH],
    ptr: ManuallyDrop<B>,
}

/// # Safety:
///
/// + The inlined content is always copied.
/// + The heap-allocated content is `Send`.
unsafe impl<B> Send for Trailing<B> where B: Send + Sync {}

/// # Safety:
///
/// + The inlined content is immutable.
/// + The heap-allocated content is `Sync`.
unsafe impl<B> Sync for Trailing<B> where B: Send + Sync {}

/// An Umbra-style string that owns its underlying bytes and does not share the bytes among
/// different instances.
pub type BoxString<const PREFIX_LENGTH: usize> = UmbraString<BoxDynBytes, PREFIX_LENGTH>;

/// An Umbra-style string that shares its underlying bytes and keeps track of the number of
/// references using an atomic counter.
pub type ArcString<const PREFIX_LENGTH: usize> = UmbraString<ArcDynBytes, PREFIX_LENGTH>;

/// An Umbra-style string that shares its underlying bytes and keeps track of the number of
/// references using a counter.
pub type RcString<const PREFIX_LENGTH: usize> = UmbraString<RcDynBytes, PREFIX_LENGTH>;

/// An alias for [`BoxString<4>`].
pub type UniqueString = BoxString<4>;

/// An alias for [`ArcString<4>`].
pub type SharedString = ArcString<4>;

/// A string data structure optimized for analytical processing workload. Unlike [`String`], which
/// uses 24 bytes on the stack, this data structure uses only 16 bytes and is immutable.
#[repr(C)]
pub struct UmbraString<B: ThinDrop, const PREFIX_LENGTH: usize> {
    len: u32,
    prefix: [u8; PREFIX_LENGTH],
    trailing: Trailing<B>,
}

/// # Safety:
///
/// + `len` is always copied.
/// + The heap-allocated bytes are `Send`.
unsafe impl<B, const PREFIX_LENGTH: usize> Send for UmbraString<B, PREFIX_LENGTH> where
    B: ThinDrop + Send + Sync
{
}

/// # Safety:
///
/// + `len` is immutable.
/// + The heap-allocated bytes are `Sync`.
unsafe impl<B, const PREFIX_LENGTH: usize> Sync for UmbraString<B, PREFIX_LENGTH> where
    B: ThinDrop + Send + Sync
{
}

impl<B, const PREFIX_LENGTH: usize> Drop for UmbraString<B, PREFIX_LENGTH>
where
    B: ThinDrop,
{
    fn drop(&mut self) {
        if self.len() > Self::INLINED_LENGTH {
            // Safety:
            // + We know that the string is heap-allocated because len > INLINED_LENGTH.
            // + We never modify `len`, thus it always equals to the number of allocated bytes.
            unsafe {
                self.trailing.ptr.thin_drop(self.len());
            }
        }
    }
}

impl<B, const PREFIX_LENGTH: usize> Clone for UmbraString<B, PREFIX_LENGTH>
where
    B: ThinDrop + ThinClone,
{
    fn clone(&self) -> Self {
        let trailing = if self.len() <= Self::INLINED_LENGTH {
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
                    ptr: ManuallyDrop::new(self.trailing.ptr.thin_clone(self.len())),
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

impl<B, const PREFIX_LENGTH: usize> TryFrom<&str> for UmbraString<B, PREFIX_LENGTH>
where
    B: ThinDrop + for<'a> From<&'a [u8]>,
{
    type Error = Error;

    #[inline]
    fn try_from(s: &str) -> Result<Self, Self::Error> {
        Self::new(s, |s| B::from(s.as_bytes()))
    }
}

impl<B, const PREFIX_LENGTH: usize> TryFrom<&String> for UmbraString<B, PREFIX_LENGTH>
where
    B: ThinDrop + for<'a> From<&'a [u8]>,
{
    type Error = Error;

    #[inline]
    fn try_from(s: &String) -> Result<Self, Self::Error> {
        Self::new(s, |s| B::from(s.as_bytes()))
    }
}

impl<B, const PREFIX_LENGTH: usize> TryFrom<String> for UmbraString<B, PREFIX_LENGTH>
where
    B: ThinDrop + From<Vec<u8>>,
{
    type Error = Error;

    #[inline]
    fn try_from(s: String) -> Result<Self, Self::Error> {
        Self::new(s, |s| B::from(s.into_bytes()))
    }
}

impl<B, const PREFIX_LENGTH: usize> std::ops::Deref for UmbraString<B, PREFIX_LENGTH>
where
    B: ThinDrop + ThinAsBytes,
{
    type Target = str;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_str()
    }
}

impl<B, const PREFIX_LENGTH: usize> AsRef<str> for UmbraString<B, PREFIX_LENGTH>
where
    B: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl<B, const PREFIX_LENGTH: usize> Borrow<str> for UmbraString<B, PREFIX_LENGTH>
where
    B: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

impl<B, const PREFIX_LENGTH: usize> std::hash::Hash for UmbraString<B, PREFIX_LENGTH>
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

impl<B, const PREFIX_LENGTH: usize> Eq for UmbraString<B, PREFIX_LENGTH> where
    B: ThinDrop + ThinAsBytes
{
}

impl<B1, B2, const PREFIX_LENGTH: usize> PartialEq<UmbraString<B2, PREFIX_LENGTH>>
    for UmbraString<B1, PREFIX_LENGTH>
where
    B1: ThinDrop + ThinAsBytes,
    B2: ThinDrop + ThinAsBytes,
{
    fn eq(&self, other: &UmbraString<B2, PREFIX_LENGTH>) -> bool {
        // NOTES: These match branches should be eliminate by the compiler when optimization is enabled
        match PREFIX_LENGTH {
            // SAFETY: Calls to `first_qword` are safe because we alreay confirm that
            // `PREFIX_LENGTH` is 4
            4 => unsafe {
                if self.first_qword() != other.first_qword() {
                    return false;
                }
            },
            // SAFETY: Calls to `first_oword` are safe because we alreay confirm that
            // `PREFIX_LENGTH` is 12
            12 => unsafe {
                if self.first_oword() != other.first_oword() {
                    return false;
                }
            },
            _ => {
                if self.len() != other.len() || self.prefix != other.prefix {
                    return false;
                }
            }
        }
        if self.len() <= Self::INLINED_LENGTH {
            // Safety:
            // + We know that the string is inlined because len <= INLINED_LENGTH.
            return unsafe { self.trailing.buf == other.trailing.buf };
        }
        self.suffix() == other.suffix()
    }
}

impl<B, const PREFIX_LENGTH: usize> PartialEq<str> for UmbraString<B, PREFIX_LENGTH>
where
    B: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn eq(&self, other: &str) -> bool {
        self.as_bytes() == other.as_bytes()
    }
}

impl<B, const PREFIX_LENGTH: usize> PartialEq<UmbraString<B, PREFIX_LENGTH>> for str
where
    B: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn eq(&self, other: &UmbraString<B, PREFIX_LENGTH>) -> bool {
        self.as_bytes() == other.as_bytes()
    }
}

impl<B, const PREFIX_LENGTH: usize> PartialEq<String> for UmbraString<B, PREFIX_LENGTH>
where
    B: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn eq(&self, other: &String) -> bool {
        self.as_bytes() == other.as_bytes()
    }
}

impl<B, const PREFIX_LENGTH: usize> PartialEq<UmbraString<B, PREFIX_LENGTH>> for String
where
    B: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn eq(&self, other: &UmbraString<B, PREFIX_LENGTH>) -> bool {
        self.as_bytes() == other.as_bytes()
    }
}

impl<B, const PREFIX_LENGTH: usize> Ord for UmbraString<B, PREFIX_LENGTH>
where
    B: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        Self::cmp(self, other)
    }
}

impl<B1, B2, const PREFIX_LENGTH: usize> PartialOrd<UmbraString<B2, PREFIX_LENGTH>>
    for UmbraString<B1, PREFIX_LENGTH>
where
    B1: ThinDrop + ThinAsBytes,
    B2: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn partial_cmp(&self, other: &UmbraString<B2, PREFIX_LENGTH>) -> Option<cmp::Ordering> {
        Some(Self::cmp(self, other))
    }
}

impl<B, const PREFIX_LENGTH: usize> PartialOrd<str> for UmbraString<B, PREFIX_LENGTH>
where
    B: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn partial_cmp(&self, other: &str) -> Option<cmp::Ordering> {
        PartialOrd::partial_cmp(self.as_bytes(), other.as_bytes())
    }
}

impl<B, const PREFIX_LENGTH: usize> PartialOrd<UmbraString<B, PREFIX_LENGTH>> for str
where
    B: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn partial_cmp(&self, other: &UmbraString<B, PREFIX_LENGTH>) -> Option<cmp::Ordering> {
        PartialOrd::partial_cmp(self.as_bytes(), other.as_bytes())
    }
}

impl<B, const PREFIX_LENGTH: usize> PartialOrd<String> for UmbraString<B, PREFIX_LENGTH>
where
    B: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn partial_cmp(&self, other: &String) -> Option<cmp::Ordering> {
        PartialOrd::partial_cmp(self.as_bytes(), other.as_bytes())
    }
}

impl<B, const PREFIX_LENGTH: usize> PartialOrd<UmbraString<B, PREFIX_LENGTH>> for String
where
    B: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn partial_cmp(&self, other: &UmbraString<B, PREFIX_LENGTH>) -> Option<cmp::Ordering> {
        PartialOrd::partial_cmp(self.as_bytes(), other.as_bytes())
    }
}

impl<B, const PREFIX_LENGTH: usize> std::fmt::Display for UmbraString<B, PREFIX_LENGTH>
where
    B: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

impl<B, const PREFIX_LENGTH: usize> std::fmt::Debug for UmbraString<B, PREFIX_LENGTH>
where
    B: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.as_str())
    }
}

impl<B, const PREFIX_LENGTH: usize> UmbraString<B, PREFIX_LENGTH>
where
    B: ThinDrop,
{
    const INLINED_LENGTH: usize = PREFIX_LENGTH + SUFFIX_LENGTH;

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
        const {
            assert!(
                (4 + PREFIX_LENGTH) % SUFFIX_LENGTH == 0,
                "got padding between the prefix and suffix",
            );
        }
        let bytes = s.as_ref().as_bytes();
        let len = bytes.len();
        if len > u32::MAX as usize {
            return Err(Error::TooLong);
        }
        let mut prefix = [0u8; PREFIX_LENGTH];
        let trailing = if len <= Self::INLINED_LENGTH {
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

impl<B, const PREFIX_LENGTH: usize> UmbraString<B, PREFIX_LENGTH>
where
    B: ThinDrop + ThinAsBytes,
{
    /// Converts `self` to a byte slice.
    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        if self.len() <= Self::INLINED_LENGTH {
            // Note: If we cast from a reference to a pointer, we can only access memory that was
            // within the bounds of the reference. This is done to satisfied miri when we create a
            // slice starting from the pointer of self.prefix to access data beyond it.
            let ptr = std::ptr::from_ref(self);
            // Safety:
            // + We know that the string is inlined because len <= INLINED_LENGTH.
            // + We can create a slice starting from the pointer to self.prefix with a length of at
            // most PREFIX_LENGTH because we have an inlined suffix of 8 bytes after the prefix.
            unsafe {
                std::slice::from_raw_parts(std::ptr::addr_of!((*ptr).prefix).cast(), self.len())
            }
        } else {
            // Safety:
            // + We know that the string is heap-allocated because len > INLINED_LENGTH.
            // + We never modify `len`, thus it always equals to the number of allocated bytes.
            unsafe { self.trailing.ptr.thin_as_bytes(self.len()) }
        }
    }

    /// Extracts a string slice containing the entire [`UmbraString`].
    #[inline]
    pub fn as_str(&self) -> &str {
        // Safety:
        // + We always construct the string using valid UTF-8 bytes.
        unsafe { std::str::from_utf8_unchecked(self.as_bytes()) }
    }

    /// # Safety
    ///
    /// By calling this method, we must ensure that `PREFIX_LENGTH` equals to 4. Otherwise, we will
    /// access invalid data.
    #[inline]
    const unsafe fn first_qword(&self) -> u64 {
        debug_assert!(
            PREFIX_LENGTH == 4,
            "prefix must have a length of 4 in order to get the first qword"
        );
        if std::mem::align_of::<Self>() == std::mem::align_of::<u64>() {
            // Safety:
            // + The referenced objects are immutable and are not changed concurrently.
            // + The pointers are obtained from the given references and guaranteed to be non-null.
            // + The alignment was checked by the if statement.
            // + The first QWORD contains the string length and prefix based on the layout, guaranteed
            // by `#[repr(C)]` and the function's invariant.
            unsafe { std::ptr::from_ref(self).cast::<u64>().read() }
        } else {
            // Safety:
            // + The referenced objects are immutable and are not changed concurrently.
            // + The pointers are obtained from the given references and guaranteed to be non-null.
            // + The alignment is unimportant because we are using `read_unaligned`.
            // + The first QWORD contains the string length and prefix based on the layout, guaranteed
            // by `#[repr(C)]` and the function's invariant.
            unsafe { std::ptr::from_ref(self).cast::<u64>().read_unaligned() }
        }
    }

    /// # Safety
    ///
    /// By calling this method, we must ensure that `PREFIX_LENGTH` equals to 12. Otherwise, we
    /// will access invalid data.
    #[inline]
    const unsafe fn first_oword(&self) -> u128 {
        debug_assert!(
            PREFIX_LENGTH == 12,
            "prefix must have a length of 12 in order to get the first oword"
        );
        if std::mem::align_of::<Self>() == std::mem::align_of::<u128>() {
            // Safety:
            // + The referenced objects are immutable and are not changed concurrently.
            // + The pointers are obtained from the given references and guaranteed to be non-null.
            // + The alignment was checked by the if statement.
            // + The first OWORD contains the string length and prefix based on the layout, guaranteed
            // by `#[repr(C)]` and the function's invariant.
            unsafe { std::ptr::from_ref(self).cast::<u128>().read() }
        } else {
            // Safety:
            // + The referenced objects are immutable and are not changed concurrently.
            // + The pointers are obtained from the given references and guaranteed to be non-null.
            // + The alignment is unimportant because we are using `read_unaligned`.
            // + The first OWORD contains the string length and prefix based on the layout, guaranteed
            // by `#[repr(C)]` and the function's invariant.
            unsafe { std::ptr::from_ref(self).cast::<u128>().read_unaligned() }
        }
    }

    #[inline]
    fn suffix(&self) -> &[u8] {
        if self.len() <= Self::INLINED_LENGTH {
            // Safety:
            // + We know that the string is inlined because len <= INLINED_LENGTH.
            let suffix_len = self.len().saturating_sub(PREFIX_LENGTH);
            unsafe { self.trailing.buf.get_unchecked(..suffix_len) }
        } else {
            // Safety:
            // + We know that the string is heap-allocated because len > INLINED_LENGTH.
            // + We never modify `len`, thus it always equals to the number of allocated bytes.
            // + We can slice into the bytes without bound checks because len > PREFIX_LENGTH.
            unsafe {
                self.trailing
                    .ptr
                    .thin_as_bytes(self.len())
                    .get_unchecked(PREFIX_LENGTH..)
            }
        }
    }

    fn cmp<BB>(lhs: &Self, rhs: &UmbraString<BB, PREFIX_LENGTH>) -> cmp::Ordering
    where
        BB: ThinDrop + ThinAsBytes,
    {
        let prefix_ordering = Ord::cmp(&lhs.prefix, &rhs.prefix);
        if prefix_ordering != cmp::Ordering::Equal {
            return prefix_ordering;
        }
        if lhs.len() <= PREFIX_LENGTH && rhs.len() <= PREFIX_LENGTH {
            return Ord::cmp(&lhs.len, &rhs.len);
        }
        if lhs.len() <= Self::INLINED_LENGTH && rhs.len() <= Self::INLINED_LENGTH {
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

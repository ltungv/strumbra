//! A container of bytes in an [`UmbraString`].
//!
//! [`UmbraString`]: crate::UmbraString

use std::{borrow::Borrow, cmp, mem::ManuallyDrop};

use crate::{
    Error, UmbraString,
    heap::{ArcDynBytes, BoxDynBytes, RcDynBytes, ThinAsBytes, ThinClone, ThinDrop},
};

/// The number of trailing bytes in the inlined representation of an [`UmbraBytes`].
const SUFFIX_LENGTH: usize = std::mem::size_of::<usize>();

/// An [`UmbraString`] that owns its underlying bytes and does not share the bytes among
/// different instances.
pub type BoxBytes<const PREFIX_LENGTH: usize> = UmbraBytes<BoxDynBytes, PREFIX_LENGTH>;

/// An [`UmbraBytes`] that shares its underlying bytes and keeps track of the number of
/// references using an atomic counter.
pub type ArcBytes<const PREFIX_LENGTH: usize> = UmbraBytes<ArcDynBytes, PREFIX_LENGTH>;

/// An [`UmbraBytes`] that shares its underlying bytes and keeps track of the number of
/// references using a counter.
pub type RcBytes<const PREFIX_LENGTH: usize> = UmbraBytes<RcDynBytes, PREFIX_LENGTH>;

/// A byte sequence optimized for analytical processing workload.
#[repr(C)]
pub struct UmbraBytes<B: ThinDrop, const PREFIX_LENGTH: usize> {
    len: u32,
    prefix: [u8; PREFIX_LENGTH],
    trailing: Trailing<B>,
}

// SAFETY:
// + `len` and `prefix` are always copied.
// + The heap-allocated bytes are `Send`.
unsafe impl<B, const PREFIX_LENGTH: usize> Send for UmbraBytes<B, PREFIX_LENGTH> where
    B: ThinDrop + Send + Sync
{
}

// SAFETY:
// + `len` and `prefix` are immutable.
// + The heap-allocated bytes are `Sync`.
unsafe impl<B, const PREFIX_LENGTH: usize> Sync for UmbraBytes<B, PREFIX_LENGTH> where
    B: ThinDrop + Send + Sync
{
}

impl<B, const PREFIX_LENGTH: usize> Drop for UmbraBytes<B, PREFIX_LENGTH>
where
    B: ThinDrop,
{
    fn drop(&mut self) {
        if self.len() > Self::INLINED_LENGTH {
            // SAFETY:
            // + We know that the bytes are heap-allocated because len > INLINED_LENGTH.
            // + We never modify `len`, thus it always equals to the number of allocated bytes.
            unsafe {
                self.trailing.ptr.thin_drop(self.len());
            }
        }
    }
}

impl<B, const PREFIX_LENGTH: usize> Clone for UmbraBytes<B, PREFIX_LENGTH>
where
    B: ThinDrop + ThinClone,
{
    fn clone(&self) -> Self {
        let trailing = if self.len() <= Self::INLINED_LENGTH {
            // SAFETY: We know that the bytes are inlined because len <= INLINED_LENGTH.
            unsafe {
                Trailing {
                    buf: self.trailing.buf,
                }
            }
        } else {
            // SAFETY: We know that the bytes are heap-allocated because len > INLINED_LENGTH.
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

impl<B, const PREFIX_LENGTH: usize> From<UmbraString<B, PREFIX_LENGTH>>
    for UmbraBytes<B, PREFIX_LENGTH>
where
    B: ThinDrop,
{
    fn from(s: UmbraString<B, PREFIX_LENGTH>) -> Self {
        s.bytes
    }
}

impl<B, const PREFIX_LENGTH: usize> TryFrom<&[u8]> for UmbraBytes<B, PREFIX_LENGTH>
where
    B: ThinDrop + for<'a> From<&'a [u8]>,
{
    type Error = Error;

    #[inline]
    fn try_from(s: &[u8]) -> Result<Self, Self::Error> {
        Self::new(s, |s| B::from(s))
    }
}

impl<B, const PREFIX_LENGTH: usize> TryFrom<&Vec<u8>> for UmbraBytes<B, PREFIX_LENGTH>
where
    B: ThinDrop + for<'a> From<&'a [u8]>,
{
    type Error = Error;

    #[inline]
    fn try_from(s: &Vec<u8>) -> Result<Self, Self::Error> {
        Self::new(s, |s| B::from(s))
    }
}

impl<B, const PREFIX_LENGTH: usize> TryFrom<Vec<u8>> for UmbraBytes<B, PREFIX_LENGTH>
where
    B: ThinDrop + From<Vec<u8>>,
{
    type Error = Error;

    #[inline]
    fn try_from(s: Vec<u8>) -> Result<Self, Self::Error> {
        Self::new(s, |s| B::from(s))
    }
}

impl<B, const PREFIX_LENGTH: usize> std::ops::Deref for UmbraBytes<B, PREFIX_LENGTH>
where
    B: ThinDrop + ThinAsBytes,
{
    type Target = [u8];

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_bytes()
    }
}

impl<B, const PREFIX_LENGTH: usize> AsRef<[u8]> for UmbraBytes<B, PREFIX_LENGTH>
where
    B: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl<B, const PREFIX_LENGTH: usize> Borrow<[u8]> for UmbraBytes<B, PREFIX_LENGTH>
where
    B: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn borrow(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl<B, const PREFIX_LENGTH: usize> std::hash::Hash for UmbraBytes<B, PREFIX_LENGTH>
where
    B: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn hash<H>(&self, hasher: &mut H)
    where
        H: std::hash::Hasher,
    {
        self.as_bytes().hash(hasher);
    }
}

impl<B, const PREFIX_LENGTH: usize> Eq for UmbraBytes<B, PREFIX_LENGTH> where
    B: ThinDrop + ThinAsBytes
{
}

impl<B1, B2, const PREFIX_LENGTH: usize> PartialEq<UmbraBytes<B2, PREFIX_LENGTH>>
    for UmbraBytes<B1, PREFIX_LENGTH>
where
    B1: ThinDrop + ThinAsBytes,
    B2: ThinDrop + ThinAsBytes,
{
    fn eq(&self, other: &UmbraBytes<B2, PREFIX_LENGTH>) -> bool {
        // NOTES: These match branches should be eliminate by the compiler when optimization is enabled
        match PREFIX_LENGTH {
            // SAFETY: Calls to `first_qword` are safe because we already confirm that
            // `PREFIX_LENGTH` is 4
            4 => unsafe {
                if self.first_qword() != other.first_qword() {
                    return false;
                }
            },
            // SAFETY: Calls to `first_oword` are safe because we already confirm that
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
            // SAFETY: We know that the bytes are inlined because len <= INLINED_LENGTH.
            return unsafe { self.trailing.buf == other.trailing.buf };
        }
        self.suffix() == other.suffix()
    }
}

impl<B, const PREFIX_LENGTH: usize> PartialEq<[u8]> for UmbraBytes<B, PREFIX_LENGTH>
where
    B: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn eq(&self, other: &[u8]) -> bool {
        self.as_bytes() == other
    }
}

impl<B, const PREFIX_LENGTH: usize> PartialEq<UmbraBytes<B, PREFIX_LENGTH>> for [u8]
where
    B: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn eq(&self, other: &UmbraBytes<B, PREFIX_LENGTH>) -> bool {
        self == other.as_bytes()
    }
}

impl<B, const PREFIX_LENGTH: usize> PartialEq<Vec<u8>> for UmbraBytes<B, PREFIX_LENGTH>
where
    B: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn eq(&self, other: &Vec<u8>) -> bool {
        self.as_bytes() == other.as_slice()
    }
}

impl<B, const PREFIX_LENGTH: usize> PartialEq<UmbraBytes<B, PREFIX_LENGTH>> for Vec<u8>
where
    B: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn eq(&self, other: &UmbraBytes<B, PREFIX_LENGTH>) -> bool {
        self.as_slice() == other.as_bytes()
    }
}

impl<B, const PREFIX_LENGTH: usize> PartialEq<Box<[u8]>> for UmbraBytes<B, PREFIX_LENGTH>
where
    B: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn eq(&self, other: &Box<[u8]>) -> bool {
        self.as_bytes() == other.as_ref()
    }
}

impl<B, const PREFIX_LENGTH: usize> PartialEq<UmbraBytes<B, PREFIX_LENGTH>> for Box<[u8]>
where
    B: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn eq(&self, other: &UmbraBytes<B, PREFIX_LENGTH>) -> bool {
        self.as_ref() == other.as_bytes()
    }
}

impl<B, const PREFIX_LENGTH: usize> Ord for UmbraBytes<B, PREFIX_LENGTH>
where
    B: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        Self::cmp(self, other)
    }
}

impl<B1, B2, const PREFIX_LENGTH: usize> PartialOrd<UmbraBytes<B2, PREFIX_LENGTH>>
    for UmbraBytes<B1, PREFIX_LENGTH>
where
    B1: ThinDrop + ThinAsBytes,
    B2: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn partial_cmp(&self, other: &UmbraBytes<B2, PREFIX_LENGTH>) -> Option<cmp::Ordering> {
        Some(Self::cmp(self, other))
    }
}

impl<B, const PREFIX_LENGTH: usize> PartialOrd<[u8]> for UmbraBytes<B, PREFIX_LENGTH>
where
    B: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn partial_cmp(&self, other: &[u8]) -> Option<cmp::Ordering> {
        self.as_bytes().partial_cmp(other)
    }
}

impl<B, const PREFIX_LENGTH: usize> PartialOrd<UmbraBytes<B, PREFIX_LENGTH>> for [u8]
where
    B: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn partial_cmp(&self, other: &UmbraBytes<B, PREFIX_LENGTH>) -> Option<cmp::Ordering> {
        self.partial_cmp(other.as_bytes())
    }
}

impl<B, const PREFIX_LENGTH: usize> PartialOrd<Vec<u8>> for UmbraBytes<B, PREFIX_LENGTH>
where
    B: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn partial_cmp(&self, other: &Vec<u8>) -> Option<cmp::Ordering> {
        self.as_bytes().partial_cmp(other.as_slice())
    }
}

impl<B, const PREFIX_LENGTH: usize> PartialOrd<UmbraBytes<B, PREFIX_LENGTH>> for Vec<u8>
where
    B: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn partial_cmp(&self, other: &UmbraBytes<B, PREFIX_LENGTH>) -> Option<cmp::Ordering> {
        self.as_slice().partial_cmp(other.as_bytes())
    }
}

impl<B, const PREFIX_LENGTH: usize> std::fmt::Debug for UmbraBytes<B, PREFIX_LENGTH>
where
    B: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.as_bytes())
    }
}

impl<B, const PREFIX_LENGTH: usize> UmbraBytes<B, PREFIX_LENGTH>
where
    B: ThinDrop,
{
    const INLINED_LENGTH: usize = {
        assert!(
            (4 + PREFIX_LENGTH) % SUFFIX_LENGTH == 0,
            "invalid memory layout",
        );
        PREFIX_LENGTH + SUFFIX_LENGTH
    };

    /// Returns the number of bytes.
    #[inline]
    pub const fn len(&self) -> usize {
        self.len as usize
    }

    /// Returns whether there is no byte.
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    fn new<S, A>(s: S, alloc: A) -> Result<Self, Error>
    where
        S: AsRef<[u8]>,
        A: FnOnce(S) -> B,
    {
        let bytes = s.as_ref();
        let len = bytes.len();
        if len > u32::MAX as usize {
            return Err(Error::TooLong);
        }
        let mut prefix = [0u8; PREFIX_LENGTH];
        let trailing = if len <= Self::INLINED_LENGTH {
            // The content can be inlined.
            let mut buf = [0u8; SUFFIX_LENGTH];
            if len <= PREFIX_LENGTH {
                prefix[..len].copy_from_slice(&bytes[..len]);
            } else {
                prefix.copy_from_slice(&bytes[..PREFIX_LENGTH]);
                buf[..len - PREFIX_LENGTH].copy_from_slice(&bytes[PREFIX_LENGTH..]);
            }
            Trailing { buf }
        } else {
            // The content must be heap-allocated.
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

impl<B, const PREFIX_LENGTH: usize> UmbraBytes<B, PREFIX_LENGTH>
where
    B: ThinDrop + ThinAsBytes,
{
    /// Slices into the bytes.
    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        if self.len() <= Self::INLINED_LENGTH {
            // NOTES: If we cast from a reference to a pointer, we can only access the memory that
            // is within the bounds of the reference. What we're doing is creating a pointer from
            // `&self`, which enables us to access the memory of the entire struct through the
            // pointer. We then obtain the pointer to `prefix` by offsetting the pointer to `&self`.
            // This is done to satisfy MIRI when we creating a slice starting at `prefix` that is
            // longer than `PREFIX_LENGTH`.
            let ptr = std::ptr::from_ref(self);
            // SAFETY:
            // + We know that the bytes are inlined because len <= INLINED_LENGTH.
            // + We can create a slice starting from the pointer to `prefix` with a length of at
            // most `INLINED_LENGTH` because we have an inlined suffix containing valid bytes after
            // the inlined prefix.
            unsafe {
                std::slice::from_raw_parts(std::ptr::addr_of!((*ptr).prefix).cast(), self.len())
            }
        } else {
            // SAFETY:
            // + We know that the bytes are heap-allocated because len > INLINED_LENGTH.
            // + We never modify `len`, thus it always equals to the number of allocated bytes.
            unsafe { self.trailing.ptr.thin_as_bytes(self.len()) }
        }
    }

    /// # SAFETY
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
            // SAFETY:
            // + The referenced objects are immutable and are not changed concurrently.
            // + The pointers are obtained from the given references and guaranteed to be non-null.
            // + The alignment was checked by the if statement.
            // + The first QWORD contains the number of bytes and prefix based on the layout,
            // guaranteed by `#[repr(C)]` and the function's invariant.
            unsafe { std::ptr::from_ref(self).cast::<u64>().read() }
        } else {
            // SAFETY:
            // + The referenced objects are immutable and are not changed concurrently.
            // + The pointers are obtained from the given references and guaranteed to be non-null.
            // + The alignment is unimportant because we are using `read_unaligned`.
            // + The first QWORD contains the number of bytes and prefix based on the layout,
            // guaranteed by `#[repr(C)]` and the function's invariant.
            unsafe { std::ptr::from_ref(self).cast::<u64>().read_unaligned() }
        }
    }

    /// # SAFETY
    ///
    /// By calling this method, we must ensure that `PREFIX_LENGTH` equals to 12. Otherwise, we will
    /// access invalid data.
    #[inline]
    const unsafe fn first_oword(&self) -> u128 {
        debug_assert!(
            PREFIX_LENGTH == 12,
            "prefix must have a length of 12 in order to get the first oword"
        );
        if std::mem::align_of::<Self>() == std::mem::align_of::<u128>() {
            // SAFETY:
            // + The referenced objects are immutable and are not changed concurrently.
            // + The pointers are obtained from the given references and guaranteed to be non-null.
            // + The alignment was checked by the if statement.
            // + The first OWORD contains the number of bytes and prefix based on the layout,
            // guaranteed by `#[repr(C)]` and the function's invariant.
            unsafe { std::ptr::from_ref(self).cast::<u128>().read() }
        } else {
            // SAFETY:
            // + The referenced objects are immutable and are not changed concurrently.
            // + The pointers are obtained from the given references and guaranteed to be non-null.
            // + The alignment is unimportant because we are using `read_unaligned`.
            // + The first OWORD contains the number of bytes and prefix based on the layout,
            // guaranteed by `#[repr(C)]` and the function's invariant.
            unsafe { std::ptr::from_ref(self).cast::<u128>().read_unaligned() }
        }
    }

    #[inline]
    fn suffix(&self) -> &[u8] {
        if self.len() <= Self::INLINED_LENGTH {
            // SAFETY: We know that the bytes are inlined because len <= INLINED_LENGTH.
            let suffix_len = self.len().saturating_sub(PREFIX_LENGTH);
            unsafe { self.trailing.buf.get_unchecked(..suffix_len) }
        } else {
            // SAFETY:
            // + We know that the bytes are heap-allocated because len > INLINED_LENGTH.
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

    fn cmp<BB>(lhs: &Self, rhs: &UmbraBytes<BB, PREFIX_LENGTH>) -> cmp::Ordering
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
            // SAFETY: We know that the bytes are inlined because len <= INLINED_LENGTH.
            let suffix_ordering = unsafe { Ord::cmp(&lhs.trailing.buf, &rhs.trailing.buf) };
            if suffix_ordering != cmp::Ordering::Equal {
                return suffix_ordering;
            }
            return Ord::cmp(&lhs.len, &rhs.len);
        }
        Ord::cmp(lhs.suffix(), rhs.suffix())
    }
}

#[repr(C)]
union Trailing<B> {
    buf: [u8; SUFFIX_LENGTH],
    ptr: ManuallyDrop<B>,
}

// SAFETY:
// + The inlined content is always copied.
// + The heap-allocated content is `Send`.
unsafe impl<B> Send for Trailing<B> where B: Send + Sync {}

// SAFETY:
// + The inlined content is immutable.
// + The heap-allocated content is `Sync`.
unsafe impl<B> Sync for Trailing<B> where B: Send + Sync {}

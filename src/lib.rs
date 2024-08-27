//! An implementation for the string data structure described in [Umbra: A Disk-Based System with In-Memory Performance].
//!
//! [Umbra: A Disk-Based System with In-Memory Performance]: https://www.cidrdb.org/cidr2020/papers/p29-neumann-cidr20.pdf

#![warn(
    rustdoc::all,
    clippy::pedantic,
    clippy::nursery,
    missing_debug_implementations
)]
#![deny(clippy::all, missing_docs, rust_2018_idioms, rust_2021_compatibility)]

mod heap;

use std::{cmp, mem::ManuallyDrop};

use heap::{DynBytes, SharedDynBytes, UniqueDynBytes};

const INLINED_LENGTH: usize = 12;
const PREFIX_LENGTH: usize = 4;
const SUFFIX_LENGTH: usize = 8;

/// An Umbra-style string that owns its underlying bytes and does not share the bytes among
/// different instances.
pub type UniqueString = UmbraString<UniqueDynBytes>;

/// An Umbra-style string that shares its underlying bytes and keeps track of the number of
/// references using an atomic counter.
pub type SharedString = UmbraString<SharedDynBytes>;

/// An error type for all possible errors that can occur when using [`UmbraString`].
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

union Tail<B: DynBytes> {
    suffix: [u8; SUFFIX_LENGTH],
    bytes: ManuallyDrop<B>,
}

// Safety:
// + Inlined content is always copied.
// + If the heap-allocated content is `Send` then `Repr` is `Send`.
unsafe impl<B> Send for Tail<B> where B: DynBytes + Send {}

// Safety:
// + Inlined content is immutable.
// + If the heap-allocated content is `Sync` then `Repr` is `Sync`.
unsafe impl<B> Sync for Tail<B> where B: DynBytes + Sync {}

/// A string data structure optimized for analytical processing workload. Unlike [`String`], which
/// uses 24 bytes on the stack, this data structure uses only 16 bytes and is immutable.
#[repr(C)]
pub struct UmbraString<B: DynBytes> {
    len: u32,
    head: [u8; PREFIX_LENGTH],
    tail: Tail<B>,
}

// Safety:
// + `len` is always copied.
// + `UniqueDynBytes` is `Send`.
unsafe impl Send for UmbraString<UniqueDynBytes> {}

// Safety:
// + `len` is immutable.
// + `UniqueDynBytes` is `Sync`.
unsafe impl Sync for UmbraString<UniqueDynBytes> {}

// Safety:
// + `len` is always copied.
// + `SharedDynBytes` is `Send`.
unsafe impl Send for UmbraString<SharedDynBytes> {}

// Safety:
// + `len` is immutable.
// + `SharedDynBytes` is `Sync`.
unsafe impl Sync for UmbraString<SharedDynBytes> {}

impl<B> Drop for UmbraString<B>
where
    B: DynBytes,
{
    fn drop(&mut self) {
        let len = self.len as usize;
        if len > INLINED_LENGTH {
            // Safety:
            // + We know that the string is heap-allocated because len > INLINED_LENGTH.
            // + We never modify `len`, thus it always equals to the number of allocated bytes.
            unsafe {
                self.tail.bytes.dealloc_unchecked(len);
            }
        }
    }
}

impl Clone for UmbraString<UniqueDynBytes> {
    fn clone(&self) -> Self {
        let len = self.len as usize;
        let tail = if len <= INLINED_LENGTH {
            // Safety:
            // + We know that the string is inlined because len <= INLINED_LENGTH.
            unsafe {
                Tail {
                    suffix: self.tail.suffix,
                }
            }
        } else {
            // Safety:
            // + We know that the string is heap-allocated because len > INLINED_LENGTH.
            // + We never modify `len`, thus it always equals to the number of allocated bytes.
            unsafe {
                Tail {
                    bytes: ManuallyDrop::new(UniqueDynBytes::clone(&self.tail.bytes, len)),
                }
            }
        };
        Self {
            len: self.len,
            head: self.head,
            tail,
        }
    }
}

impl Clone for UmbraString<SharedDynBytes> {
    fn clone(&self) -> Self {
        let tail = if self.len as usize <= INLINED_LENGTH {
            // Safety:
            // + We know that the string is inlined because len <= INLINED_LENGTH.
            unsafe {
                Tail {
                    suffix: self.tail.suffix,
                }
            }
        } else {
            // Safety:
            // + We know that the string is heap-allocated because len > INLINED_LENGTH.
            unsafe {
                Tail {
                    bytes: ManuallyDrop::new(SharedDynBytes::clone(&self.tail.bytes)),
                }
            }
        };
        Self {
            len: self.len,
            head: self.head,
            tail,
        }
    }
}

impl TryFrom<&str> for UmbraString<UniqueDynBytes> {
    type Error = Error;

    fn try_from(s: &str) -> Result<Self, Self::Error> {
        Self::new(s)
    }
}

impl TryFrom<&str> for UmbraString<SharedDynBytes> {
    type Error = Error;

    fn try_from(s: &str) -> Result<Self, Self::Error> {
        Self::new(s)
    }
}

impl TryFrom<String> for UmbraString<UniqueDynBytes> {
    type Error = Error;

    fn try_from(s: String) -> Result<Self, Self::Error> {
        Self::new(s)
    }
}

impl TryFrom<String> for UmbraString<SharedDynBytes> {
    type Error = Error;

    fn try_from(s: String) -> Result<Self, Self::Error> {
        Self::new(s)
    }
}

impl<B> std::ops::Deref for UmbraString<B>
where
    B: DynBytes,
{
    type Target = str;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_str()
    }
}

impl<B> AsRef<str> for UmbraString<B>
where
    B: DynBytes,
{
    #[inline]
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl<B> Eq for UmbraString<B> where B: DynBytes {}
impl<B1, B2> PartialEq<UmbraString<B2>> for UmbraString<B1>
where
    B1: DynBytes,
    B2: DynBytes,
{
    fn eq(&self, other: &UmbraString<B2>) -> bool {
        if self.head != other.head {
            return false;
        }
        let lhs_len = self.len as usize;
        let rhs_len = other.len as usize;
        if lhs_len <= PREFIX_LENGTH && rhs_len <= PREFIX_LENGTH {
            return true;
        }
        if lhs_len <= INLINED_LENGTH && rhs_len <= INLINED_LENGTH {
            // Safety:
            // + We know that the string is inlined because len <= INLINED_LENGTH.
            unsafe {
                return self.tail.suffix == other.tail.suffix;
            }
        }
        self.suffix() == other.suffix()
    }
}

impl<B> Ord for UmbraString<B>
where
    B: DynBytes,
{
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        // Safety:
        // + It's always possible to compare strings according to our PartialOrd implementation.
        unsafe { PartialOrd::partial_cmp(self, other).unwrap_unchecked() }
    }
}

impl<B1, B2> PartialOrd<UmbraString<B2>> for UmbraString<B1>
where
    B1: DynBytes,
    B2: DynBytes,
{
    fn partial_cmp(&self, other: &UmbraString<B2>) -> Option<cmp::Ordering> {
        let ordering = Ord::cmp(&self.head, &other.head).then_with(|| {
            let lhs_len = self.len as usize;
            let rhs_len = other.len as usize;
            if lhs_len <= PREFIX_LENGTH && rhs_len <= PREFIX_LENGTH {
                return cmp::Ordering::Equal;
            }
            if lhs_len <= INLINED_LENGTH && rhs_len <= INLINED_LENGTH {
                // Safety:
                // + We know that the string is inlined because len <= INLINED_LENGTH.
                unsafe {
                    return Ord::cmp(&self.tail.suffix, &other.tail.suffix);
                }
            }
            Ord::cmp(self.suffix(), other.suffix())
        });
        Some(ordering)
    }
}

impl<B> std::fmt::Display for UmbraString<B>
where
    B: DynBytes,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

impl<B> std::fmt::Debug for UmbraString<B>
where
    B: DynBytes,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.as_str())
    }
}

impl<B> UmbraString<B>
where
    B: DynBytes,
{
    fn new<S: AsRef<str>>(s: S) -> Result<Self, Error> {
        let s = s.as_ref();
        let len = s.len();
        if len > u32::MAX as usize {
            return Err(Error::TooLong);
        }
        let bytes = s.as_bytes();
        let mut head = [0u8; PREFIX_LENGTH];
        let tail = if len <= INLINED_LENGTH {
            let mut suffix = [0u8; SUFFIX_LENGTH];
            if len <= PREFIX_LENGTH {
                head[..len].copy_from_slice(&bytes[..len]);
            } else {
                head.copy_from_slice(&bytes[..PREFIX_LENGTH]);
                suffix[..len - PREFIX_LENGTH].copy_from_slice(&bytes[PREFIX_LENGTH..]);
            }
            Tail { suffix }
        } else {
            head.copy_from_slice(&bytes[..PREFIX_LENGTH]);
            // Safety:
            // + We know that the string is heap-allocated because len > INLINED_LENGTH.
            let bytes = unsafe { B::alloc_unchecked(bytes) };
            Tail { bytes }
        };
        #[allow(clippy::cast_possible_truncation)]
        Ok(Self {
            len: len as u32,
            head,
            tail,
        })
    }

    #[inline]
    fn as_bytes(&self) -> &[u8] {
        let len = self.len as usize;
        if len <= INLINED_LENGTH {
            // TODO: This is currently marked as UB by miri, but it seems fine given our struct
            // layout. Check if it really is an UB, then provide a fix or a work-around.
            // Safety:
            // + We know that the string is inlined because len <= INLINED_LENGTH.
            // + We can create a slice starting from the pointer to self.head with a length of at
            // most PREFIX_LENGTH by having an inlined suffix of 8 bytes right after the prefix.
            unsafe { &*std::ptr::slice_from_raw_parts(std::ptr::addr_of!(self.head).cast(), len) }
        } else {
            // Safety:
            // + We know that the string is heap-allocated because len > INLINED_LENGTH.
            // + We never modify `len`, thus it always equals to the number of allocated bytes.
            unsafe { self.tail.bytes.as_bytes_unchecked(len) }
        }
    }

    #[inline]
    fn as_str(&self) -> &str {
        // Safety:
        // + We always construct the string using valid UTF-8 bytes.
        unsafe { std::str::from_utf8_unchecked(self.as_bytes()) }
    }

    #[inline]
    fn suffix(&self) -> &[u8] {
        let len = self.len as usize;
        if len <= INLINED_LENGTH {
            // Safety:
            // + We know that the string is inlined because len <= INLINED_LENGTH.
            unsafe { &self.tail.suffix }
        } else {
            // Safety:
            // + We know that the string is heap-allocated because len > INLINED_LENGTH.
            // + We never modify `len`, thus it always equals to the number of allocated bytes.
            // + We can slice into the bytes without bound checks because len > PREFIX_LENGTH.
            unsafe {
                self.tail
                    .bytes
                    .as_bytes_unchecked(len)
                    .get_unchecked(PREFIX_LENGTH..)
            }
        }
    }
}

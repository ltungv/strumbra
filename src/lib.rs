//! An implementation of the string data structure described in [Umbra: A Disk-Based System with In-Memory Performance].
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

pub mod bytes;
#[cfg(feature = "serde")]
pub mod serde;

mod heap;

use std::{borrow::Borrow, cmp};

use bytes::UmbraBytes;
use heap::{ArcDynBytes, BoxDynBytes, RcDynBytes, ThinAsBytes, ThinClone, ThinDrop};

/// An enumeration of all errors that can occur when using this crate.
#[derive(Debug)]
pub enum Error {
    /// An error from converting from an array whose length exceeds the maximum value of a 32-bit
    /// unsigned integer.
    TooLong,
}

impl std::error::Error for Error {}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TooLong => write!(f, "too long"),
        }
    }
}

/// An [`UmbraString`] that owns its underlying bytes and does not share the bytes among
/// different instances.
pub type BoxString<const PREFIX_LENGTH: usize> = UmbraString<BoxDynBytes, PREFIX_LENGTH>;

/// An [`UmbraString`] that shares its underlying bytes and keeps track of the number of
/// references using an atomic counter.
pub type ArcString<const PREFIX_LENGTH: usize> = UmbraString<ArcDynBytes, PREFIX_LENGTH>;

/// An [`UmbraString`] that shares its underlying bytes and keeps track of the number of
/// references using a counter.
pub type RcString<const PREFIX_LENGTH: usize> = UmbraString<RcDynBytes, PREFIX_LENGTH>;

/// An alias for [`BoxString<4>`].
pub type UniqueString = BoxString<4>;

/// An alias for [`ArcString<4>`].
pub type SharedString = ArcString<4>;

/// A string data structure optimized for analytical processing workload.
#[repr(C)]
pub struct UmbraString<B: ThinDrop, const PREFIX_LENGTH: usize> {
    bytes: UmbraBytes<B, PREFIX_LENGTH>,
}

// SAFETY:
// + `len` and `prefix` are always copied.
// + The heap-allocated bytes are `Send`.
unsafe impl<B, const PREFIX_LENGTH: usize> Send for UmbraString<B, PREFIX_LENGTH> where
    B: ThinDrop + Send + Sync
{
}

// SAFETY:
// + `len` and `prefix` are immutable.
// + The heap-allocated bytes are `Sync`.
unsafe impl<B, const PREFIX_LENGTH: usize> Sync for UmbraString<B, PREFIX_LENGTH> where
    B: ThinDrop + Send + Sync
{
}

impl<B, const PREFIX_LENGTH: usize> Clone for UmbraString<B, PREFIX_LENGTH>
where
    B: ThinDrop + ThinClone,
{
    fn clone(&self) -> Self {
        Self {
            bytes: self.bytes.clone(),
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
        UmbraBytes::try_from(s.as_bytes()).map(|bytes| Self { bytes })
    }
}

impl<B, const PREFIX_LENGTH: usize> TryFrom<&String> for UmbraString<B, PREFIX_LENGTH>
where
    B: ThinDrop + for<'a> From<&'a [u8]>,
{
    type Error = Error;

    #[inline]
    fn try_from(s: &String) -> Result<Self, Self::Error> {
        UmbraBytes::try_from(s.as_bytes()).map(|bytes| Self { bytes })
    }
}

impl<B, const PREFIX_LENGTH: usize> TryFrom<String> for UmbraString<B, PREFIX_LENGTH>
where
    B: ThinDrop + From<Vec<u8>>,
{
    type Error = Error;

    #[inline]
    fn try_from(s: String) -> Result<Self, Self::Error> {
        UmbraBytes::try_from(s.into_bytes()).map(|bytes| Self { bytes })
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
        self.bytes.eq(&other.bytes)
    }
}

impl<B, const PREFIX_LENGTH: usize> PartialEq<str> for UmbraString<B, PREFIX_LENGTH>
where
    B: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn eq(&self, other: &str) -> bool {
        &self.bytes == other.as_bytes()
    }
}

impl<B, const PREFIX_LENGTH: usize> PartialEq<UmbraString<B, PREFIX_LENGTH>> for str
where
    B: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn eq(&self, other: &UmbraString<B, PREFIX_LENGTH>) -> bool {
        self.as_bytes() == &other.bytes
    }
}

impl<B, const PREFIX_LENGTH: usize> PartialEq<String> for UmbraString<B, PREFIX_LENGTH>
where
    B: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn eq(&self, other: &String) -> bool {
        &self.bytes == other.as_bytes()
    }
}

impl<B, const PREFIX_LENGTH: usize> PartialEq<UmbraString<B, PREFIX_LENGTH>> for String
where
    B: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn eq(&self, other: &UmbraString<B, PREFIX_LENGTH>) -> bool {
        self.as_bytes() == &other.bytes
    }
}

impl<B, const PREFIX_LENGTH: usize> Ord for UmbraString<B, PREFIX_LENGTH>
where
    B: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.bytes.cmp(&other.bytes)
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
        self.bytes.partial_cmp(&other.bytes)
    }
}

impl<B, const PREFIX_LENGTH: usize> PartialOrd<str> for UmbraString<B, PREFIX_LENGTH>
where
    B: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn partial_cmp(&self, other: &str) -> Option<cmp::Ordering> {
        self.bytes.partial_cmp(other.as_bytes())
    }
}

impl<B, const PREFIX_LENGTH: usize> PartialOrd<UmbraString<B, PREFIX_LENGTH>> for str
where
    B: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn partial_cmp(&self, other: &UmbraString<B, PREFIX_LENGTH>) -> Option<cmp::Ordering> {
        self.as_bytes().partial_cmp(&other.bytes)
    }
}

impl<B, const PREFIX_LENGTH: usize> PartialOrd<String> for UmbraString<B, PREFIX_LENGTH>
where
    B: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn partial_cmp(&self, other: &String) -> Option<cmp::Ordering> {
        self.bytes.partial_cmp(other.as_bytes())
    }
}

impl<B, const PREFIX_LENGTH: usize> PartialOrd<UmbraString<B, PREFIX_LENGTH>> for String
where
    B: ThinDrop + ThinAsBytes,
{
    #[inline]
    fn partial_cmp(&self, other: &UmbraString<B, PREFIX_LENGTH>) -> Option<cmp::Ordering> {
        self.as_bytes().partial_cmp(&other.bytes)
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
    /// Returns the length of the string.
    ///
    /// This length is in bytes, not [`char`]s or graphemes. In other words,
    /// it might not be what a human considers the length of the string.
    #[inline]
    pub const fn len(&self) -> usize {
        self.bytes.len()
    }

    /// Returns whether the string has a length of zero.
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.bytes.is_empty()
    }
}

impl<B, const PREFIX_LENGTH: usize> UmbraString<B, PREFIX_LENGTH>
where
    B: ThinDrop + ThinAsBytes,
{
    /// Views the string as a slice of bytes.
    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes
    }

    /// Gets a reference to the underlying content.
    #[inline]
    pub fn as_str(&self) -> &str {
        // SAFETY: We always construct the string using valid UTF-8 bytes.
        unsafe { std::str::from_utf8_unchecked(&self.bytes) }
    }
}

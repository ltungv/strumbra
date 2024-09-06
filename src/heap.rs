use std::{
    alloc::Layout,
    marker::PhantomData,
    ptr::NonNull,
    sync::atomic::{self, AtomicUsize},
};

/// Trait for thin pointer to an array that can be dropped using a user-provided length.
///
/// # Safety
///
/// Types that implement this trait must correctly use the user-provided length.
pub unsafe trait ThinDrop {
    /// Drop the underlying buffer through a thin pointer.
    ///
    /// # Safety
    ///
    /// + The caller must ensure that `len` equals the number of allocated bytes.
    /// + The caller must ensure that the object will never be accessed once this method is called.
    ///   Accessing the object after calling this method may result in an undefined behavior.
    /// + The caller must ensure the this method is called exactly once through out the lifetime of
    ///   the program. Not calling this method will result in a memory leak. Calling this method
    ///   more than once may result in an undefined behavior.
    unsafe fn thin_drop(&self, len: usize);
}

/// Trait for thin pointer to an array that can be cloned using a user-provided length.
///
/// # Safety
///
/// Types that implement this trait must correctly use the user-provided length.
pub unsafe trait ThinClone {
    /// Clone the underlying buffer through a thin pointer.
    ///
    /// # Safety
    ///
    /// + The caller must ensure that `len` equals the number of allocated bytes.
    unsafe fn thin_clone(&self, len: usize) -> Self;
}

/// Trait for thin pointer to an array that can be referenced using a user-provided length.
///
/// # Safety
///
/// Types that implement this trait must correctly use the user-provided length.
pub unsafe trait ThinAsBytes {
    /// Slice into the underlying buffer through a thin pointer.
    ///
    /// # Safety
    ///
    /// + The caller must ensure that `len` equals the number of allocated bytes.
    unsafe fn thin_as_bytes(&self, len: usize) -> &[u8];
}

#[repr(C)]
#[allow(missing_debug_implementations)]
pub struct UniqueDynBytes {
    ptr: NonNull<u8>,
    phantom: PhantomData<u8>,
}

/// # Safety:
///
/// + `UniqueDynBytes` is the only owner of its data.
unsafe impl Send for UniqueDynBytes {}

/// # Safety:
///
/// + `UniqueDynBytes` is immutable.
unsafe impl Sync for UniqueDynBytes {}

impl From<&[u8]> for UniqueDynBytes {
    fn from(bytes: &[u8]) -> Self {
        let ptr = if bytes.is_empty() {
            NonNull::dangling()
        } else {
            let layout = array_layout::<u8>(bytes.len());
            // Safety:
            // + Our layout is always guaranteed to be of a non-zero sized type due to the if
            // statement that we have.
            let nullable = unsafe { std::alloc::alloc(layout) };
            let Some(ptr) = NonNull::new(nullable) else {
                std::alloc::handle_alloc_error(layout);
            };
            // Safety:
            // + We are copying `bytes.len()` bytes into a buffer of the same size that we just
            // allocated.
            unsafe {
                std::ptr::copy_nonoverlapping(bytes.as_ptr(), ptr.as_ptr(), bytes.len());
            }
            ptr
        };
        Self {
            ptr,
            phantom: PhantomData,
        }
    }
}

impl From<Vec<u8>> for UniqueDynBytes {
    fn from(bytes: Vec<u8>) -> Self {
        let ptr = if bytes.is_empty() {
            NonNull::dangling()
        } else {
            // Safety:
            // + We create a `NonNull` from the result of `Box::into_raw` which is guaranteed to be
            // non-null and aligned.
            unsafe { NonNull::new_unchecked(Box::into_raw(bytes.into_boxed_slice()).cast()) }
        };
        Self {
            ptr,
            phantom: PhantomData,
        }
    }
}

unsafe impl ThinDrop for UniqueDynBytes {
    unsafe fn thin_drop(&self, len: usize) {
        if len > 0 {
            // Safety:
            // + We only allocate using the default global allocator.
            // + We require that the caller passes in a `len` matching the number of allocated bytes.
            unsafe {
                std::alloc::dealloc(self.ptr.as_ptr(), array_layout::<u8>(len));
            }
        }
    }
}

unsafe impl ThinClone for UniqueDynBytes {
    unsafe fn thin_clone(&self, len: usize) -> Self {
        let ptr = if len == 0 {
            NonNull::dangling()
        } else {
            let layout = array_layout::<u8>(len);
            // Safety:
            // + Our layout is always guaranteed to be of a non-zero sized type due to the if
            // statement that we have.
            let nullable = unsafe { std::alloc::alloc(layout) };
            let Some(ptr) = NonNull::new(nullable) else {
                std::alloc::handle_alloc_error(layout);
            };
            // Safety:
            // + We require the caller to pass in a valid `len` corresponding to the number of
            // allocated bytes.
            // + We are copying `len` bytes into a buffer of the same size that we just
            // allocated.
            unsafe {
                std::ptr::copy_nonoverlapping(self.ptr.as_ptr(), ptr.as_ptr(), len);
            }
            ptr
        };
        Self {
            ptr,
            phantom: PhantomData,
        }
    }
}

unsafe impl ThinAsBytes for UniqueDynBytes {
    #[inline]
    unsafe fn thin_as_bytes(&self, len: usize) -> &[u8] {
        if len == 0 {
            Default::default()
        } else {
            // Safety:
            // + We ensure that the pointer is aligned and the data it points to is properly
            // initialized.
            // + We have access to `&self`, thus the bytes have not been deallocated.
            // + We return a slice having the same lifetime as `&self`.
            std::slice::from_raw_parts(self.ptr.as_ptr(), len)
        }
    }
}

#[repr(C)]
struct SharedDynBytesInner<T: ?Sized> {
    count: AtomicUsize,
    data: T,
}

impl<T> SharedDynBytesInner<[T]> {
    #[inline]
    fn cast(ptr: *mut T, len: usize) -> *mut Self {
        // Type-casting magic to create a fat pointer to a dynamically sized type.
        let fake_slice = std::ptr::slice_from_raw_parts_mut(ptr, len);
        fake_slice as *mut Self
    }
}

#[repr(C)]
#[allow(missing_debug_implementations)]
pub struct SharedDynBytes {
    ptr: NonNull<SharedDynBytesInner<[u8; 0]>>,
    phantom: PhantomData<SharedDynBytesInner<[u8]>>,
}

/// # Safety:
///
/// + `SharedDynBytes` keeps track of the number of references to its data using an atomic counter and
///   allows shared ownership across threads.
unsafe impl Send for SharedDynBytes {}

/// # Safety:
///
/// + `SharedDynBytes` is immutable.
unsafe impl Sync for SharedDynBytes {}

impl From<&[u8]> for SharedDynBytes {
    fn from(bytes: &[u8]) -> Self {
        let ptr = if bytes.is_empty() {
            NonNull::dangling()
        } else {
            let layout = shared_dyn_bytes_inner_layout(bytes.len());
            // Safety:
            // + Our layout is always guaranteed to be of a non-zero sized type due to the if
            // statement that we have.
            let nullable = unsafe { std::alloc::alloc(layout) };
            let nullable_fat_ptr = SharedDynBytesInner::<[u8]>::cast(nullable, bytes.len());
            let Some(fat_ptr) = NonNull::new(nullable_fat_ptr) else {
                std::alloc::handle_alloc_error(layout)
            };
            // Safety:
            // + We just allocated for a new `SharedDynBytesInner<[T]>` with enough space to
            // contain `len` bytes.
            // + We require the caller to pass in a valid `len` corresponding to the number of
            // allocated bytes.
            // + We are copying `len` bytes into a buffer of the same size.
            unsafe {
                let inner = &mut (*fat_ptr.as_ptr());
                std::ptr::write(&mut inner.count, AtomicUsize::new(1));
                std::ptr::copy_nonoverlapping(bytes.as_ptr(), inner.data.as_mut_ptr(), bytes.len());
            }
            fat_ptr.cast()
        };
        Self {
            ptr,
            phantom: PhantomData,
        }
    }
}

impl From<Vec<u8>> for SharedDynBytes {
    #[inline]
    fn from(bytes: Vec<u8>) -> Self {
        Self::from(&bytes[..])
    }
}

unsafe impl ThinDrop for SharedDynBytes {
    unsafe fn thin_drop(&self, len: usize) {
        if len > 0 {
            // Safety:
            // + We have access to `&self`, thus the pointer has not been deallocated.
            let inner = unsafe { &*self.ptr.as_ptr() };
            if inner.count.fetch_sub(1, atomic::Ordering::Release) == 1 {
                inner.count.load(atomic::Ordering::Acquire);
                // Safety:
                // + We require that the caller passes in a `len` matching the number of allocated bytes.
                unsafe {
                    std::alloc::dealloc(
                        self.ptr.as_ptr().cast::<u8>(),
                        shared_dyn_bytes_inner_layout(len),
                    );
                };
            }
        }
    }
}

unsafe impl ThinClone for SharedDynBytes {
    unsafe fn thin_clone(&self, len: usize) -> Self {
        let ptr = if len == 0 {
            NonNull::dangling()
        } else {
            // Safety:
            // + We never deallocate the pointer if the reference count is at least 1.
            // + We can deference the pointer because we are accessing it through a reference to
            // [`SharedDynBytes`] which means the reference count is at least 1.
            let inner = unsafe { &*self.ptr.as_ptr() };
            inner.count.fetch_add(1, atomic::Ordering::Relaxed);
            self.ptr
        };

        Self {
            ptr,
            phantom: PhantomData,
        }
    }
}

unsafe impl ThinAsBytes for SharedDynBytes {
    #[inline]
    unsafe fn thin_as_bytes(&self, len: usize) -> &[u8] {
        if len == 0 {
            Default::default()
        } else {
            let fat_ptr = SharedDynBytesInner::<[u8]>::cast(self.ptr.as_ptr().cast::<u8>(), len);
            // Safety:
            // + We have access to `&self`, thus the pointer has not been deallocated.
            let ptr = unsafe { (*fat_ptr).data.as_ptr() };
            // Safety:
            // + We have access to `&self`, thus the bytes have not been deallocated.
            // + We require that the caller passes a valid length for the slice.
            unsafe { std::slice::from_raw_parts(ptr, len) }
        }
    }
}

fn shared_dyn_bytes_inner_layout(len: usize) -> Layout {
    Layout::new::<SharedDynBytesInner<()>>()
        .extend(array_layout::<u8>(len))
        .expect("A valid layout for a SharedDynBytesInner")
        .0
        .pad_to_align()
}

fn array_layout<T>(len: usize) -> Layout {
    Layout::array::<T>(len).expect("A valid layout for a byte array")
}

#[cfg(test)]
mod tests {
    use super::{SharedDynBytes, ThinAsBytes, ThinClone, ThinDrop, UniqueDynBytes};

    #[test]
    fn create_unique_dyn_bytes_from_empty_slice() {
        let data = [];
        let unique = UniqueDynBytes::from(&data[..]);
        unsafe {
            assert_eq!(&data, unique.thin_as_bytes(data.len()));
            unique.thin_drop(data.len());
        }
    }

    #[test]
    fn create_unique_dyn_bytes_from_non_empty_slice() {
        let data = b"hello world";
        let unique = UniqueDynBytes::from(&data[..]);
        unsafe {
            assert_eq!(&data[..], unique.thin_as_bytes(data.len()));
            unique.thin_drop(data.len());
        }
    }

    #[test]
    fn create_unique_dyn_bytes_from_empty_vec() {
        let data = Vec::new();
        let unique = UniqueDynBytes::from(data.clone());
        unsafe {
            assert_eq!(&data, unique.thin_as_bytes(data.len()));
            unique.thin_drop(data.len());
        }
    }

    #[test]
    fn create_unique_dyn_bytes_from_non_empty_vec() {
        let data = Vec::from(b"hello world");
        let unique = UniqueDynBytes::from(data.clone());
        unsafe {
            assert_eq!(&data, unique.thin_as_bytes(data.len()));
            unique.thin_drop(data.len());
        }
    }

    #[test]
    fn create_shared_dyn_bytes_from_empty_slice() {
        let data = [];
        let shared = SharedDynBytes::from(&data[..]);
        unsafe {
            assert_eq!(&data, shared.thin_as_bytes(data.len()));
            shared.thin_drop(data.len());
        }
    }

    #[test]
    fn create_shared_dyn_bytes_from_non_empty_slice() {
        let data = b"hello world";
        let shared = SharedDynBytes::from(&data[..]);
        unsafe {
            assert_eq!(&data[..], shared.thin_as_bytes(data.len()));
            shared.thin_drop(data.len());
        }
    }

    #[test]
    fn create_shared_dyn_bytes_from_empty_vec() {
        let data = Vec::new();
        let shared = SharedDynBytes::from(data.clone());
        unsafe {
            assert_eq!(&data, shared.thin_as_bytes(data.len()));
            shared.thin_drop(data.len());
        }
    }

    #[test]
    fn create_shared_dyn_bytes_from_non_empty_vec() {
        let data = Vec::from(b"hello world");
        let shared = SharedDynBytes::from(data.clone());
        unsafe {
            assert_eq!(&data, shared.thin_as_bytes(data.len()));
            shared.thin_drop(data.len());
        }
    }

    #[test]
    fn clone_unique_dyn_bytes_empty() {
        let data = [];
        let unique0 = UniqueDynBytes::from(&data[..]);
        let unique1 = unsafe { unique0.thin_clone(data.len()) };
        unsafe {
            assert_eq!(&data, unique0.thin_as_bytes(data.len()));
            assert_eq!(&data, unique1.thin_as_bytes(data.len()));
            unique0.thin_drop(data.len());
            unique1.thin_drop(data.len());
        }
    }

    #[test]
    fn clone_unique_dyn_bytes_non_empty() {
        let data = b"hello world";
        let unique0 = UniqueDynBytes::from(&data[..]);
        let unique1 = unsafe { unique0.thin_clone(data.len()) };
        unsafe {
            assert_eq!(&data[..], unique0.thin_as_bytes(data.len()));
            assert_eq!(&data[..], unique1.thin_as_bytes(data.len()));
            unique0.thin_drop(data.len());
            unique1.thin_drop(data.len());
        }
    }

    #[test]
    fn clone_shared_dyn_bytes_empty() {
        let data = [];
        let shared0 = SharedDynBytes::from(&data[..]);
        let shared1 = unsafe { shared0.thin_clone(data.len()) };
        unsafe {
            assert_eq!(&data, shared0.thin_as_bytes(data.len()));
            assert_eq!(&data, shared1.thin_as_bytes(data.len()));
            shared0.thin_drop(data.len());
            shared1.thin_drop(data.len());
        }
    }

    #[test]
    fn clone_shared_dyn_bytes_non_empty() {
        let data = b"hello world";
        let shared0 = SharedDynBytes::from(&data[..]);
        let shared1 = unsafe { shared0.thin_clone(data.len()) };
        unsafe {
            assert_eq!(&data[..], shared0.thin_as_bytes(data.len()));
            assert_eq!(&data[..], shared1.thin_as_bytes(data.len()));
            shared0.thin_drop(data.len());
            shared1.thin_drop(data.len());
        }
    }
}

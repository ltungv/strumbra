use std::{
    alloc::Layout,
    marker::PhantomData,
    mem::ManuallyDrop,
    ptr::NonNull,
    sync::atomic::{self, AtomicUsize},
};

/// Trait for types that represent a heap-allocated byte array.
///
/// # Safety
///
/// + [`DynBytes`] are thin pointers to a heap-allocated byte array and do not support allocating
///   array of length zero.
/// + Because types don't have the information about the length of the heap-allocated byte
///   array, the user is responsible for providing a valid length when they access the array.
pub unsafe trait DynBytes {
    /// Allocate a new byte container.
    ///
    /// # Safety
    ///
    /// + The caller must make sure that `bytes.len() > 0`.
    unsafe fn alloc_unchecked(bytes: &[u8]) -> ManuallyDrop<Self>;

    /// Deallocate a byte container.
    ///
    /// # Safety
    ///
    /// + The caller must make sure that `len` equals to the number of bytes being allocated.
    unsafe fn dealloc_unchecked(&self, len: usize);

    /// Get a slice to the underlying bytes.
    ///
    /// # Safety
    ///
    /// + The caller must make sure that `len` equals to the number of bytes being allocated.
    unsafe fn as_bytes_unchecked(&self, len: usize) -> &[u8];
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

unsafe impl DynBytes for UniqueDynBytes {
    unsafe fn alloc_unchecked(bytes: &[u8]) -> ManuallyDrop<Self> {
        debug_assert!(!bytes.is_empty());
        let layout = array_layout::<u8>(bytes.len());
        // Safety:
        // + We require the caller to make sure that `bytes.len() > 0`.
        // + We are sure that a non-zero size type is being allocated when `bytes.len() > 0`.
        let nullable = unsafe { std::alloc::alloc(layout) };
        let ptr = NonNull::new(nullable).map_or_else(
            || std::alloc::handle_alloc_error(layout),
            |ptr| {
                // Safety:
                // + We are copying `bytes.len()` bytes into a buffer of the same size that we just
                // allocated.
                unsafe {
                    std::ptr::copy_nonoverlapping(bytes.as_ptr(), ptr.as_ptr(), bytes.len());
                }
                ptr
            },
        );
        ManuallyDrop::new(Self {
            ptr,
            phantom: PhantomData,
        })
    }

    unsafe fn dealloc_unchecked(&self, len: usize) {
        debug_assert!(len > 0);
        // Safety:
        // + We only allocate using the default global allocator.
        // + We require that the caller passes in a `len` matching the number of allocated bytes.
        unsafe {
            std::alloc::dealloc(self.ptr.as_ptr(), array_layout::<u8>(len));
        }
    }

    #[inline]
    unsafe fn as_bytes_unchecked(&self, len: usize) -> &[u8] {
        debug_assert!(len > 0);
        // Safety:
        // + We ensure that the pointer is aligned and the data it points to is properly
        // initialized.
        // + We have access to `&self`, thus the bytes have not been deallocated.
        // + We return a slice having the same lifetime as `&self`.
        std::slice::from_raw_parts(self.ptr.as_ptr(), len)
    }
}

impl UniqueDynBytes {
    pub unsafe fn clone(bytes: &Self, len: usize) -> Self {
        debug_assert!(len > 0);
        let layout = array_layout::<u8>(len);
        // Safety:
        // + We require the caller to make sure that `bytes.len() > 0`.
        // + We are sure that a non-zero size type is being allocated when `bytes.len() > 0`.
        let nullable = unsafe { std::alloc::alloc(layout) };
        let ptr = NonNull::new(nullable).map_or_else(
            || std::alloc::handle_alloc_error(layout),
            |ptr| {
                // Safety:
                // + We require the caller to pass in a valid `len` corresponding to the number of
                // allocated bytes.
                // + We are copying `len` bytes into a buffer of the same size that we just
                // allocated.
                unsafe {
                    std::ptr::copy_nonoverlapping(bytes.ptr.as_ptr(), ptr.as_ptr(), len);
                }
                ptr
            },
        );
        Self {
            ptr,
            phantom: PhantomData,
        }
    }
}

#[repr(C)]
struct SharedDynBytesInner<T: ?Sized> {
    count: AtomicUsize,
    data: T,
}

impl<T> SharedDynBytesInner<[T; 0]> {
    /// Allocate a new byte container.
    ///
    /// # Safety
    ///
    /// + The caller must make sure that `bytes.len() > 0`.
    unsafe fn alloc_unchecked(bytes: &[T]) -> NonNull<Self> {
        debug_assert!(!bytes.is_empty());
        let layout = Self::layout(bytes.len());
        // Safety:
        // + We require the caller to make sure that `bytes.len() > 0`.
        // + We are sure that a non-zero size type is being allocated when `bytes.len() > 0`.
        let ptr = unsafe { std::alloc::alloc(layout) };
        // Type-casting magic to create a fat pointer to a dynamically sized type.
        let fake_slice = std::ptr::slice_from_raw_parts_mut(ptr, bytes.len());
        let fat_ptr = fake_slice as *mut SharedDynBytesInner<[T]>;
        NonNull::new(fat_ptr).map_or_else(
            || std::alloc::handle_alloc_error(layout),
            |ptr| {
                // Safety:
                // + We just allocated for a new `SharedDynBytesInner<[T]>` with enough space to
                // contain `len` bytes.
                // + We require the caller to pass in a valid `len` corresponding to the number of
                // allocated bytes.
                // + We are copying `len` bytes into a buffer of the same size.
                unsafe {
                    let inner = &mut (*ptr.as_ptr());
                    std::ptr::write(&mut inner.count, AtomicUsize::new(1));
                    std::ptr::copy_nonoverlapping(
                        bytes.as_ptr(),
                        inner.data.as_mut_ptr(),
                        bytes.len(),
                    );
                }
                ptr.cast::<Self>()
            },
        )
    }

    /// Deallocate a byte container.
    ///
    /// # Safety
    ///
    /// + The caller must make sure that `len` equals to the number of bytes being allocated.
    unsafe fn dealloc_unchecked(ptr: *mut Self, len: usize) {
        debug_assert!(len > 0);
        // Safety:
        // + We only allocate using the default global allocator.
        // + We require that the caller passes in a `len` matching the number of allocated bytes.
        unsafe {
            std::alloc::dealloc(ptr.cast::<u8>(), Self::layout(len));
        }
    }

    fn thin_to_fat_ptr(ptr: *mut Self, len: usize) -> *mut SharedDynBytesInner<[T]> {
        let fake_slice = std::ptr::slice_from_raw_parts_mut(ptr.cast::<T>(), len);
        fake_slice as *mut SharedDynBytesInner<[T]>
    }

    fn layout(len: usize) -> Layout {
        Layout::new::<SharedDynBytesInner<()>>()
            .extend(array_layout::<T>(len))
            .expect("A valid layout for a SharedDynBytesInner")
            .0
            .pad_to_align()
    }
}

#[repr(C)]
#[allow(missing_debug_implementations)]
pub struct SharedDynBytes {
    ptr: NonNull<SharedDynBytesInner<[u8; 0]>>,
    phantom: PhantomData<SharedDynBytesInner<[u8; 0]>>,
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

unsafe impl DynBytes for SharedDynBytes {
    unsafe fn alloc_unchecked(bytes: &[u8]) -> ManuallyDrop<Self> {
        debug_assert!(!bytes.is_empty());
        // Safety:
        // + We require the caller to make sure that `bytes.len() > 0`.
        let ptr = unsafe { SharedDynBytesInner::<[u8; 0]>::alloc_unchecked(bytes) };
        ManuallyDrop::new(Self {
            ptr,
            phantom: PhantomData,
        })
    }

    unsafe fn dealloc_unchecked(&self, len: usize) {
        debug_assert!(len > 0);
        // Safety:
        // + We have access to `&self`, thus the pointer has not been deallocated.
        let inner = unsafe { &*self.ptr.as_ptr() };
        if inner.count.fetch_sub(1, atomic::Ordering::Release) == 1 {
            inner.count.load(atomic::Ordering::Acquire);
            // Safety:
            // + We require that the caller passes in a `len` matching the number of allocated bytes.
            unsafe { SharedDynBytesInner::<[u8; 0]>::dealloc_unchecked(self.ptr.as_ptr(), len) };
        }
    }

    #[inline]
    unsafe fn as_bytes_unchecked(&self, len: usize) -> &[u8] {
        debug_assert!(len > 0);
        let fat_ptr = SharedDynBytesInner::<[u8; 0]>::thin_to_fat_ptr(self.ptr.as_ptr(), len);
        // Safety:
        // + We have access to `&self`, thus the pointer has not been deallocated.
        let ptr = unsafe { (*fat_ptr).data.as_ptr() };
        // Safety:
        // + We have access to `&self`, thus the bytes have not been deallocated.
        // + We require that the caller passes a valid length for the slice.
        unsafe { std::slice::from_raw_parts(ptr, len) }
    }
}

impl SharedDynBytes {
    pub fn clone(bytes: &Self) -> Self {
        // Safety:
        // + We never deallocate the pointer if the reference count is at least 1.
        // + We can deference the pointer because we are accessing it through a reference to
        // [`SharedDynBytes`] which means the reference count is at least 1.
        let inner = unsafe { &*bytes.ptr.as_ptr() };
        inner.count.fetch_add(1, atomic::Ordering::Relaxed);

        Self {
            ptr: bytes.ptr,
            phantom: PhantomData,
        }
    }
}

fn array_layout<T>(len: usize) -> Layout {
    Layout::array::<T>(len).expect("A valid layout for a byte array")
}

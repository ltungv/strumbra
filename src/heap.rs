use std::{
    alloc::Layout,
    cell::Cell,
    marker::PhantomData,
    ptr::NonNull,
    sync::atomic::{self, AtomicUsize},
};

/// A type that owns a manually allocated array, whose length is externally known, implements this
/// trait to provide its user a method to drop itself.
///
/// # SAFETY
///
/// The type that implements this trait must have ownership to the allocated array. If it has
/// unique ownership, calling [`ThinDrop::thin_drop`] immediately deallocates the array. If it has
/// shared ownership, calling [`ThinDrop::thin_drop`] performs the neccessary bookkeeping to remove
/// its ownership.
///
/// It is the user's responsibility to provide a correct length. Thus, any implementation of this
/// trait must respect the user-provided length when [`ThinDrop::thin_drop`] is called.
pub unsafe trait ThinDrop {
    /// Drops the current object.
    ///
    /// # SAFETY
    ///
    /// The caller of this methods must ensure that the provided length matches the number of bytes
    /// occupied by the allocated array. Once this method is called, any further access to the data
    /// will result in undefined behaviours.
    ///
    /// This method must be called exactly once throughout the lifetime of an object. Calling this
    /// method more than once will result in undefined behaviors. Not calling this method will
    /// result in memory leaks.
    unsafe fn thin_drop(&self, len: usize);
}

/// A type that owns a manually allocated array, whose length is externally known, implements this
/// trait to provide its user a method to clone itself.
///
/// # SAFETY
///
/// The type that implements this trait must have ownership to the allocated array. If it has
/// unique ownership, calling [`ThinClone::thin_clone`] allocates a new array and copies the
/// elements over. If it has shared ownership, calling [`ThinClone::thin_clone`] performs the
/// neccessary bookkeeping to share the array.
///
/// It is the user's responsibility to provide a correct length. Thus, any implementation of this
/// trait must respect the user-provided length when [`ThinClone::thin_clone`] is called.
pub unsafe trait ThinClone {
    /// Clones the current object.
    ///
    /// # SAFETY
    ///
    /// The caller of this methods must ensure that the provided length matches the number of bytes
    /// occupied by the allocated array.
    unsafe fn thin_clone(&self, len: usize) -> Self;
}

/// A type that owns a manually allocated array, whose length is externally known, implements this
/// trait to provide its user a method to view its bytes.
///
/// # SAFETY
///
/// It is the user's responsibility to provide a correct length. Thus, any implementation of this
/// trait must respect the user-provided length when [`ThisAsBytes::thin_as_bytes`] is called.
pub unsafe trait ThinAsBytes {
    /// Returns a slice into the allocated array.
    ///
    /// # SAFETY
    ///
    /// The caller of this methods must ensure that the provided length matches the number of bytes
    /// occupied by the allocated array.
    unsafe fn thin_as_bytes(&self, len: usize) -> &[u8];
}

#[repr(C)]
#[allow(missing_debug_implementations)]
pub struct BoxDynBytes {
    ptr: NonNull<u8>,
    phantom: PhantomData<[u8]>,
}

// # SAFETY:
//
// [`BoxDynBytes`] is the only owner of its data.
unsafe impl Send for BoxDynBytes {}

// # SAFETY:
//
// [`BoxDynBytes`] is immutable.
unsafe impl Sync for BoxDynBytes {}

impl From<&[u8]> for BoxDynBytes {
    fn from(bytes: &[u8]) -> Self {
        let ptr = if bytes.is_empty() {
            NonNull::dangling()
        } else {
            let layout = array_layout::<u8>(bytes.len());
            // SAFETY: Our layout is always guaranteed to be of a non-zero sized type due to the if
            // statement that we had.
            let nullable = unsafe { std::alloc::alloc(layout) };
            let Some(ptr) = NonNull::new(nullable) else {
                std::alloc::handle_alloc_error(layout);
            };
            // SAFETY: We are copying `bytes.len()` bytes into a buffer of the same size that we just
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

impl From<Vec<u8>> for BoxDynBytes {
    fn from(bytes: Vec<u8>) -> Self {
        let ptr = if bytes.is_empty() {
            NonNull::dangling()
        } else {
            // SAFETY: We create a `NonNull` from the result of `Box::into_raw` which is guaranteed to be
            // non-null and aligned.
            unsafe { NonNull::new_unchecked(Box::into_raw(bytes.into_boxed_slice()).cast()) }
        };
        Self {
            ptr,
            phantom: PhantomData,
        }
    }
}

unsafe impl ThinDrop for BoxDynBytes {
    unsafe fn thin_drop(&self, len: usize) {
        if len > 0 {
            // SAFETY:
            // + We only allocate using the default global allocator.
            // + We require that the caller passes in a `len` matching the number of allocated bytes.
            unsafe {
                std::alloc::dealloc(self.ptr.as_ptr(), array_layout::<u8>(len));
            }
        }
    }
}

unsafe impl ThinClone for BoxDynBytes {
    unsafe fn thin_clone(&self, len: usize) -> Self {
        let ptr = if len == 0 {
            NonNull::dangling()
        } else {
            let layout = array_layout::<u8>(len);
            // SAFETY: Our layout is always guaranteed to be of a non-zero sized type due to the if
            // statement that we had.
            let nullable = unsafe { std::alloc::alloc(layout) };
            let Some(ptr) = NonNull::new(nullable) else {
                std::alloc::handle_alloc_error(layout);
            };
            // SAFETY:
            // + We require the caller to pass in a valid `len` corresponding to the number of
            // allocated bytes.
            // + We are copying `len` bytes into a buffer of the same size that we just allocated.
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

unsafe impl ThinAsBytes for BoxDynBytes {
    #[inline]
    unsafe fn thin_as_bytes(&self, len: usize) -> &[u8] {
        if len == 0 {
            Default::default()
        } else {
            // SAFETY:
            // + We ensure that the pointer is aligned and the data it points to is properly
            // initialized.
            // + We have access to `&self`, thus the bytes have not been deallocated.
            // + We return a slice having the same lifetime as `&self`.
            unsafe { std::slice::from_raw_parts(self.ptr.as_ptr(), len) }
        }
    }
}

#[repr(C)]
struct ArcDynBytesInner<T: ?Sized> {
    count: AtomicUsize,
    data: T,
}

impl<T> ArcDynBytesInner<[T]> {
    #[inline]
    const fn cast(ptr: *mut T, len: usize) -> *mut Self {
        // Type-casting magic to create a fat pointer to a dynamically sized type.
        let fake_slice = std::ptr::slice_from_raw_parts_mut(ptr, len);
        fake_slice as *mut Self
    }
}

#[repr(C)]
#[allow(missing_debug_implementations)]
pub struct ArcDynBytes {
    ptr: NonNull<ArcDynBytesInner<[u8; 0]>>,
    phantom: PhantomData<ArcDynBytesInner<[u8]>>,
}

/// # SAFETY:
///
/// [`ArcDynBytes`] keeps track of the number of references to its data using an atomic counter
/// allowing shared ownership across threads.
unsafe impl Send for ArcDynBytes {}

/// # SAFETY:
///
/// [`ArcDynBytes`] is immutable.
unsafe impl Sync for ArcDynBytes {}

impl From<&[u8]> for ArcDynBytes {
    fn from(bytes: &[u8]) -> Self {
        let ptr = if bytes.is_empty() {
            NonNull::dangling()
        } else {
            let layout = arc_dyn_bytes_inner_layout(bytes.len());
            // SAFETY: Our layout is always guaranteed to be of a non-zero sized type due to the if
            // statement that we had.
            let nullable = unsafe { std::alloc::alloc(layout) };
            let nullable_fat_ptr = ArcDynBytesInner::<[u8]>::cast(nullable, bytes.len());
            let Some(fat_ptr) = NonNull::new(nullable_fat_ptr) else {
                std::alloc::handle_alloc_error(layout)
            };
            // SAFETY:
            // + We just allocated for a new `ArcDynBytesInner<[T]>` with enough space to
            // contain `len` bytes.
            // + We require the caller to pass in a valid `len` corresponding to the number of
            // allocated bytes.
            // + We are copying `len` bytes into a buffer of the same size.
            unsafe {
                std::ptr::write(
                    std::ptr::addr_of_mut!((*fat_ptr.as_ptr()).count),
                    AtomicUsize::new(1),
                );
                std::ptr::copy_nonoverlapping(
                    bytes.as_ptr(),
                    std::ptr::addr_of_mut!((*fat_ptr.as_ptr()).data).cast(),
                    bytes.len(),
                );
            }
            fat_ptr.cast()
        };
        Self {
            ptr,
            phantom: PhantomData,
        }
    }
}

impl From<Vec<u8>> for ArcDynBytes {
    #[inline]
    fn from(bytes: Vec<u8>) -> Self {
        Self::from(&bytes[..])
    }
}

unsafe impl ThinDrop for ArcDynBytes {
    unsafe fn thin_drop(&self, len: usize) {
        if len > 0 {
            // SAFETY: We have access to `&self`, thus the pointer has not been deallocated.
            let inner = unsafe { &*self.ptr.as_ptr() };
            if inner.count.fetch_sub(1, atomic::Ordering::Release) == 1 {
                inner.count.load(atomic::Ordering::Acquire);
                // SAFETY: We require that the caller passes in a `len` matching the number of
                // allocated bytes.
                unsafe {
                    std::alloc::dealloc(
                        self.ptr.as_ptr().cast::<u8>(),
                        arc_dyn_bytes_inner_layout(len),
                    );
                };
            }
        }
    }
}

unsafe impl ThinClone for ArcDynBytes {
    unsafe fn thin_clone(&self, len: usize) -> Self {
        let ptr = if len == 0 {
            NonNull::dangling()
        } else {
            // SAFETY:
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

unsafe impl ThinAsBytes for ArcDynBytes {
    #[inline]
    unsafe fn thin_as_bytes(&self, len: usize) -> &[u8] {
        if len == 0 {
            Default::default()
        } else {
            let fat_ptr = ArcDynBytesInner::<[u8]>::cast(self.ptr.as_ptr().cast::<u8>(), len);
            // SAFETY: We have access to `&self`, thus the pointer has not been deallocated.
            let ptr = unsafe { (*fat_ptr).data.as_ptr() };
            // SAFETY:
            // + We have access to `&self`, thus the bytes have not been deallocated.
            // + We require that the caller passes a valid length for the slice.
            unsafe { std::slice::from_raw_parts(ptr, len) }
        }
    }
}

#[repr(C)]
struct RcDynBytesInner<T: ?Sized> {
    count: Cell<usize>,
    data: T,
}

impl<T> RcDynBytesInner<[T]> {
    #[inline]
    const fn cast(ptr: *mut T, len: usize) -> *mut Self {
        // Type-casting magic to create a fat pointer to a dynamically sized type.
        let fake_slice = std::ptr::slice_from_raw_parts_mut(ptr, len);
        fake_slice as *mut Self
    }
}

#[repr(C)]
#[allow(missing_debug_implementations)]
pub struct RcDynBytes {
    ptr: NonNull<RcDynBytesInner<[u8; 0]>>,
    phantom: PhantomData<RcDynBytesInner<[u8]>>,
}

impl From<&[u8]> for RcDynBytes {
    fn from(bytes: &[u8]) -> Self {
        let ptr = if bytes.is_empty() {
            NonNull::dangling()
        } else {
            let layout = rc_dyn_bytes_inner_layout(bytes.len());
            // SAFETY: Our layout is always guaranteed to be of a non-zero sized type due to the if
            // statement that we had.
            let nullable = unsafe { std::alloc::alloc(layout) };
            let nullable_fat_ptr = RcDynBytesInner::<[u8]>::cast(nullable, bytes.len());
            let Some(fat_ptr) = NonNull::new(nullable_fat_ptr) else {
                std::alloc::handle_alloc_error(layout)
            };
            // SAFETY:
            // + We just allocated for a new `RcDynBytesInner<[T]>` with enough space to
            // contain `len` bytes.
            // + We require the caller to pass in a valid `len` corresponding to the number of
            // allocated bytes.
            // + We are copying `len` bytes into a buffer of the same size.
            unsafe {
                std::ptr::write(
                    std::ptr::addr_of_mut!((*fat_ptr.as_ptr()).count),
                    Cell::new(1),
                );
                std::ptr::copy_nonoverlapping(
                    bytes.as_ptr(),
                    std::ptr::addr_of_mut!((*fat_ptr.as_ptr()).data).cast(),
                    bytes.len(),
                );
            }
            fat_ptr.cast()
        };
        Self {
            ptr,
            phantom: PhantomData,
        }
    }
}

impl From<Vec<u8>> for RcDynBytes {
    #[inline]
    fn from(bytes: Vec<u8>) -> Self {
        Self::from(&bytes[..])
    }
}

unsafe impl ThinDrop for RcDynBytes {
    unsafe fn thin_drop(&self, len: usize) {
        if len > 0 {
            // SAFETY: We have access to `&self`, thus the pointer has not been deallocated.
            let inner = unsafe { &*self.ptr.as_ptr() };
            let ref_count = inner.count.get();
            inner.count.set(ref_count - 1);
            if ref_count == 1 {
                // SAFETY: We require that the caller passes in a `len` matching the number of
                // allocated bytes.
                unsafe {
                    std::alloc::dealloc(
                        self.ptr.as_ptr().cast::<u8>(),
                        rc_dyn_bytes_inner_layout(len),
                    );
                };
            }
        }
    }
}

unsafe impl ThinClone for RcDynBytes {
    unsafe fn thin_clone(&self, len: usize) -> Self {
        let ptr = if len == 0 {
            NonNull::dangling()
        } else {
            // SAFETY:
            // + We never deallocate the pointer if the reference count is at least 1.
            // + We can deference the pointer because we are accessing it through a reference to
            // [`SharedDynBytes`] which means the reference count is at least 1.
            let inner = unsafe { &*self.ptr.as_ptr() };
            let ref_count = inner.count.get();
            inner.count.set(ref_count + 1);
            self.ptr
        };

        Self {
            ptr,
            phantom: PhantomData,
        }
    }
}

unsafe impl ThinAsBytes for RcDynBytes {
    #[inline]
    unsafe fn thin_as_bytes(&self, len: usize) -> &[u8] {
        if len == 0 {
            Default::default()
        } else {
            let fat_ptr = RcDynBytesInner::<[u8]>::cast(self.ptr.as_ptr().cast::<u8>(), len);
            // SAFETY: We have access to `&self`, thus the pointer has not been deallocated.
            let ptr = unsafe { (*fat_ptr).data.as_ptr() };
            // SAFETY:
            // + We have access to `&self`, thus the bytes have not been deallocated.
            // + We require that the caller passes a valid length for the slice.
            unsafe { std::slice::from_raw_parts(ptr, len) }
        }
    }
}

fn array_layout<T>(len: usize) -> Layout {
    Layout::array::<T>(len).expect("A valid layout for a byte array")
}

fn arc_dyn_bytes_inner_layout(len: usize) -> Layout {
    Layout::new::<ArcDynBytesInner<()>>()
        .extend(array_layout::<u8>(len))
        .expect("A valid layout for a ArcDynBytesInner")
        .0
        .pad_to_align()
}

fn rc_dyn_bytes_inner_layout(len: usize) -> Layout {
    Layout::new::<RcDynBytesInner<()>>()
        .extend(array_layout::<u8>(len))
        .expect("A valid layout for a RcDynBytesInner")
        .0
        .pad_to_align()
}

#[cfg(test)]
mod tests {
    use super::{ArcDynBytes, BoxDynBytes, RcDynBytes, ThinAsBytes, ThinClone, ThinDrop};

    #[test]
    fn create_box_dyn_bytes_from_empty_slice() {
        let data = [];
        let boxed = BoxDynBytes::from(&data[..]);
        unsafe {
            assert_eq!(&data, boxed.thin_as_bytes(data.len()));
            boxed.thin_drop(data.len());
        }
    }

    #[test]
    fn create_box_dyn_bytes_from_non_empty_slice() {
        let data = b"hello world";
        let boxed = BoxDynBytes::from(&data[..]);
        unsafe {
            assert_eq!(&data[..], boxed.thin_as_bytes(data.len()));
            boxed.thin_drop(data.len());
        }
    }

    #[test]
    fn create_box_dyn_bytes_from_empty_vec() {
        let data = Vec::new();
        let boxed = BoxDynBytes::from(data.clone());
        unsafe {
            assert_eq!(&data, boxed.thin_as_bytes(data.len()));
            boxed.thin_drop(data.len());
        }
    }

    #[test]
    fn create_box_dyn_bytes_from_non_empty_vec() {
        let data = Vec::from(b"hello world");
        let boxed = BoxDynBytes::from(data.clone());
        unsafe {
            assert_eq!(&data, boxed.thin_as_bytes(data.len()));
            boxed.thin_drop(data.len());
        }
    }

    #[test]
    fn create_arc_dyn_bytes_from_empty_slice() {
        let data = [];
        let arc = ArcDynBytes::from(&data[..]);
        unsafe {
            assert_eq!(&data, arc.thin_as_bytes(data.len()));
            arc.thin_drop(data.len());
        }
    }

    #[test]
    fn create_arc_dyn_bytes_from_non_empty_slice() {
        let data = b"hello world";
        let arc = ArcDynBytes::from(&data[..]);
        unsafe {
            assert_eq!(&data[..], arc.thin_as_bytes(data.len()));
            arc.thin_drop(data.len());
        }
    }

    #[test]
    fn create_arc_dyn_bytes_from_empty_vec() {
        let data = Vec::new();
        let arc = ArcDynBytes::from(data.clone());
        unsafe {
            assert_eq!(&data, arc.thin_as_bytes(data.len()));
            arc.thin_drop(data.len());
        }
    }

    #[test]
    fn create_arc_dyn_bytes_from_non_empty_vec() {
        let data = Vec::from(b"hello world");
        let arc = ArcDynBytes::from(data.clone());
        unsafe {
            assert_eq!(&data, arc.thin_as_bytes(data.len()));
            arc.thin_drop(data.len());
        }
    }

    #[test]
    fn create_rc_dyn_bytes_from_empty_slice() {
        let data = [];
        let rc = RcDynBytes::from(&data[..]);
        unsafe {
            assert_eq!(&data, rc.thin_as_bytes(data.len()));
            rc.thin_drop(data.len());
        }
    }

    #[test]
    fn create_rc_dyn_bytes_from_non_empty_slice() {
        let data = b"hello world";
        let rc = RcDynBytes::from(&data[..]);
        unsafe {
            assert_eq!(&data[..], rc.thin_as_bytes(data.len()));
            rc.thin_drop(data.len());
        }
    }

    #[test]
    fn create_rc_dyn_bytes_from_empty_vec() {
        let data = Vec::new();
        let rc = RcDynBytes::from(data.clone());
        unsafe {
            assert_eq!(&data, rc.thin_as_bytes(data.len()));
            rc.thin_drop(data.len());
        }
    }

    #[test]
    fn create_rc_dyn_bytes_from_non_empty_vec() {
        let data = Vec::from(b"hello world");
        let rc = RcDynBytes::from(data.clone());
        unsafe {
            assert_eq!(&data, rc.thin_as_bytes(data.len()));
            rc.thin_drop(data.len());
        }
    }

    #[test]
    fn clone_box_dyn_bytes_empty() {
        let data = [];
        let boxed0 = BoxDynBytes::from(&data[..]);
        let boxed1 = unsafe { boxed0.thin_clone(data.len()) };
        unsafe {
            assert_eq!(&data, boxed0.thin_as_bytes(data.len()));
            assert_eq!(&data, boxed1.thin_as_bytes(data.len()));
            boxed0.thin_drop(data.len());
            boxed1.thin_drop(data.len());
        }
    }

    #[test]
    fn clone_box_dyn_bytes_non_empty() {
        let data = b"hello world";
        let boxed0 = BoxDynBytes::from(&data[..]);
        let boxed1 = unsafe { boxed0.thin_clone(data.len()) };
        unsafe {
            assert_eq!(&data[..], boxed0.thin_as_bytes(data.len()));
            assert_eq!(&data[..], boxed1.thin_as_bytes(data.len()));
            boxed0.thin_drop(data.len());
            boxed1.thin_drop(data.len());
        }
    }

    #[test]
    fn clone_arc_dyn_bytes_empty() {
        let data = [];
        let arc0 = ArcDynBytes::from(&data[..]);
        let arc1 = unsafe { arc0.thin_clone(data.len()) };
        unsafe {
            assert_eq!(&data, arc0.thin_as_bytes(data.len()));
            assert_eq!(&data, arc1.thin_as_bytes(data.len()));
            arc0.thin_drop(data.len());
            arc1.thin_drop(data.len());
        }
    }

    #[test]
    fn clone_arc_dyn_bytes_non_empty() {
        let data = b"hello world";
        let arc0 = ArcDynBytes::from(&data[..]);
        let arc1 = unsafe { arc0.thin_clone(data.len()) };
        unsafe {
            assert_eq!(&data[..], arc0.thin_as_bytes(data.len()));
            assert_eq!(&data[..], arc1.thin_as_bytes(data.len()));
            arc0.thin_drop(data.len());
            arc1.thin_drop(data.len());
        }
    }

    #[test]
    fn clone_rc_dyn_bytes_empty() {
        let data = [];
        let rc0 = RcDynBytes::from(&data[..]);
        let rc1 = unsafe { rc0.thin_clone(data.len()) };
        unsafe {
            assert_eq!(&data, rc0.thin_as_bytes(data.len()));
            assert_eq!(&data, rc1.thin_as_bytes(data.len()));
            rc0.thin_drop(data.len());
            rc1.thin_drop(data.len());
        }
    }

    #[test]
    fn clone_rc_dyn_bytes_non_empty() {
        let data = b"hello world";
        let rc0 = RcDynBytes::from(&data[..]);
        let rc1 = unsafe { rc0.thin_clone(data.len()) };
        unsafe {
            assert_eq!(&data[..], rc0.thin_as_bytes(data.len()));
            assert_eq!(&data[..], rc1.thin_as_bytes(data.len()));
            rc0.thin_drop(data.len());
            rc1.thin_drop(data.len());
        }
    }
}

use alloc::vec::Vec;

/// This trait abstracts away a vector implementation.
///
/// It is useful for supporting other vectors as tree's backing storage, such as SmallVec and Bumpalo's Vec.
pub trait Vector<T> {
    fn clear(&mut self);
    fn len(&self) -> usize;
    fn push(&mut self, value: T);
    fn slice(&self) -> &[T];
    fn slice_mut(&mut self) -> &mut [T];
}

impl<T> Vector<T> for Vec<T> {
    fn clear(&mut self) {
        Vec::clear(self);
    }

    fn len(&self) -> usize {
        Vec::len(self)
    }

    fn push(&mut self, value: T) {
        Vec::push(self, value);
    }

    fn slice(&self) -> &[T] {
        self
    }

    fn slice_mut(&mut self) -> &mut [T] {
        self
    }
}

#[cfg(feature = "bumpalo")]
impl<T> Vector<T> for bumpalo::collections::Vec<'_, T> {
    fn clear(&mut self) {
        bumpalo::collections::Vec::clear(self);
    }

    fn len(&self) -> usize {
        bumpalo::collections::Vec::len(self)
    }

    fn push(&mut self, value: T) {
        bumpalo::collections::Vec::push(self, value);
    }

    fn slice(&self) -> &[T] {
        self
    }

    fn slice_mut(&mut self) -> &mut [T] {
        self
    }
}

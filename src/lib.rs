//! In memory of Anna Harren, who coined the term
//! [turbofish](https://turbo.fish/) - which you'll see a lot of
//! if you use this crate.
//!
//! The main purpose of this crate is the `HarrenVec` type -
//! a [`Vec`]-like data structure that can store items
//! of different types and sizes from each other.
//!
//! Values of any type can be stored, and they are
//! stored contiguous in memory like a normal [`Vec`] would.
//! It supports values with a [`Drop`] implementation, however
//! dropping the `HarrenVec` will _not_ call the destructors of
//! the contents. To avoid leaking memory, use the
//! [`HarrenVec::into_iter`] method and consume all of
//! the values to ensure they are dropped.
//!
//! The intended use case for efficiently packing structs with
//! large optional fields, while avoiding [`Box`]-ing those
//! values.
//!
//! # Examples
//! ```
//! use hvec::HarrenVec;
//!
//! struct SmallMessage {
//!     id: usize,
//!     has_extra: bool,
//! }
//!
//! struct LargeExtraField {
//!     data: [[f64; 4]; 4],
//! }
//!
//! let mut messages = HarrenVec::new();
//! messages.push(SmallMessage { id: 0, has_extra: false });
//! messages.push(SmallMessage { id: 1, has_extra: true });
//! messages.push(LargeExtraField { data: [[0.; 4]; 4] });
//! messages.push(SmallMessage { id: 2, has_extra: false });
//!
//! let mut iter = messages.into_iter();
//! while let Some(message) = iter.next::<SmallMessage>() {
//!     println!("id = {}", message.id);
//!     if message.has_extra {
//!         let extra = iter.next::<LargeExtraField>().unwrap();
//!         println!("extra data = {:?}", extra.data);
//!     }
//! }
//!
//! // Output:
//! // id = 0
//! // id = 1
//! // extra data = [[0., 0., 0., 0.], [0., 0., 0., 0.], [0., 0., 0., 0.], [0., 0., 0., 0.]]
//! // id = 2
//! ```

use std::any::TypeId;
use std::mem::MaybeUninit;

/// A [`Vec`]-like data structure that can store items
/// of different types and sizes from each other.
///
/// Values of any type can be stored, and they are
/// stored contiguous in memory like a normal [`Vec`] would.
/// It supports values with a [`Drop`] implementation, however
/// dropping the `HarrenVec` will _not_ call the destructors of
/// the contents. To avoid leaking memory, use the
/// [`HarrenVec::into_iter`] method and consume all of the
/// values to ensure they are dropped.
///
/// The intended use case for efficiently packing structs with
/// large optional fields, while avoiding [`Box`]-ing those
/// values.
///
/// # Examples
/// ```
/// use hvec::HarrenVec;
///
/// struct SmallMessage {
///     id: usize,
///     has_extra: bool,
/// }
///
/// struct LargeExtraField {
///     data: [[f64; 4]; 4],
/// }
///
/// let mut messages = HarrenVec::new();
/// messages.push(SmallMessage { id: 0, has_extra: false });
/// messages.push(SmallMessage { id: 1, has_extra: true });
/// messages.push(LargeExtraField { data: [[0.; 4]; 4] });
/// messages.push(SmallMessage { id: 2, has_extra: false });
///
/// let mut iter = messages.into_iter();
/// while let Some(message) = iter.next::<SmallMessage>() {
///     println!("id = {}", message.id);
///     if message.has_extra {
///         let extra = iter.next::<LargeExtraField>().unwrap();
///         println!("extra data = {:?}", extra.data);
///     }
/// }
///
/// // Output:
/// // id = 0
/// // id = 1
/// // extra data = [[0., 0., 0., 0.], [0., 0., 0., 0.], [0., 0., 0., 0.], [0., 0., 0., 0.]]
/// // id = 2
/// ```
#[derive(Debug, Default, Clone)]
pub struct HarrenVec {
    types: Vec<TypeId>,
    indices: Vec<usize>,
    backing: Vec<u8>,
}

/// Type alias for [`HarrenVec`].
pub type HVec = HarrenVec;

/// A very basic [`Iterator`]-like structure for accessing the elements
/// of a [`HarrenVec`].
#[derive(Debug)]
pub struct HarrenVecIter {
    cursor: usize,
    vec: HarrenVec,
}

impl HarrenVec {
    /// Constructs a new empty [`HarrenVec`].
    ///
    /// # Examples
    /// ```
    /// # use hvec::HarrenVec;
    /// let mut list = HarrenVec::new();
    /// ```
    pub fn new() -> Self {
        Self::default()
    }

    /// Constructs a new empty [`HarrenVec`] with at least the
    /// specified capacity in items and bytes.
    ///
    /// The `HarrenVec` stores the types of the data separately
    /// from the data. In practice, it will re-allocate if
    /// either of these capacities are exceeded.
    ///
    /// # Examples
    /// ```
    /// # use hvec::HarrenVec;
    /// let mut list = HarrenVec::with_capacity(4, 64);
    /// assert!(list.item_capacity() >= 4);
    /// assert!(list.byte_capacity() >= 64);
    /// ```
    pub fn with_capacity(items: usize, bytes: usize) -> Self {
        HarrenVec {
            types: Vec::with_capacity(items),
            indices: Vec::with_capacity(items),
            backing: Vec::with_capacity(bytes),
        }
    }

    /// Reserve capacity for at least `items` more items and
    /// `bytes` more bytes.
    pub fn reserve(&mut self, items: usize, bytes: usize) {
        self.types.reserve(items);
        self.indices.reserve(items);
        self.backing.reserve(bytes);
    }

    /// Reserve capacity for at least `items` more items and
    /// `bytes` more bytes. (Attempts to reserve the minimum
    /// possible, but this is not guaranteed.)
    pub fn reserve_exact(&mut self, items: usize, bytes: usize) {
        self.types.reserve_exact(items);
        self.indices.reserve_exact(items);
        self.backing.reserve_exact(bytes);
    }

    /// Reserve capacity for at least `items` more items and
    /// `bytes` more bytes.
    ///
    /// # Errors
    /// Returns an error if allocation fails.
    pub fn try_reserve(
        &mut self,
        items: usize,
        bytes: usize,
    ) -> Result<(), std::collections::TryReserveError> {
        self.types.try_reserve(items)?;
        self.indices.try_reserve(items)?;
        self.backing.try_reserve(bytes)?;
        Ok(())
    }

    /// Reserve capacity for at least `items` more items and
    /// `bytes` more bytes. (Attempts to reserve the minimum
    /// possible, but this is not guaranteed.)
    ///
    /// # Errors
    /// Returns an error if allocation fails.
    pub fn try_reserve_exact(
        &mut self,
        items: usize,
        bytes: usize,
    ) -> Result<(), std::collections::TryReserveError> {
        self.types.try_reserve_exact(items)?;
        self.indices.try_reserve_exact(items)?;
        self.backing.try_reserve_exact(bytes)?;
        Ok(())
    }

    /// Move all elements from another `HarrenVec` into
    /// this one, leaving the `other` empty.
    ///
    /// # Examples
    /// ```
    /// # use hvec::hvec;
    /// let mut a = hvec![1, 2, 3];
    /// let mut b = hvec![4, 5, 6];
    /// a.append(&mut b);
    /// assert_eq!(a.len(), 6);
    /// assert_eq!(b.len(), 0);
    /// ```
    pub fn append(&mut self, other: &mut HarrenVec) {
        let mut offset = 0;
        for i in 0..other.len() {
            let end = other
                .indices
                .get(i + 1)
                .copied()
                .unwrap_or(other.backing.len());

            self.indices.push(self.backing.len());
            self.backing.extend_from_slice(&other.backing[offset..end]);
            self.types.push(other.types[i]);

            offset = end;
        }
        unsafe { other.clear() }
    }

    /// Clears the contents of the `HarrenVec`.
    ///
    /// # Safety
    ///
    /// This method is unsafe because it will not call the
    /// destructors of any of its contents. If the contents
    /// do not have a [`Drop`] implementation, this method is
    /// safe.
    pub unsafe fn clear(&mut self) {
        self.types.clear();
        self.indices.clear();
        self.backing.clear();
    }

    /// Truncates the contents of the `HarrenVec` to a set
    /// number of items, clearing the rest.
    ///
    /// # Safety
    ///
    /// This method is unsafe because it will not call the
    /// destructors of any of its contents. If the contents
    /// do not have a [`Drop`] implementation, this method is
    /// safe.
    pub unsafe fn truncate(&mut self, items: usize) {
        if let Some(last_index) = self.indices.get(items).copied() {
            self.types.truncate(items);
            self.indices.truncate(items);
            self.backing.truncate(last_index);
        }
    }

    /// Returns the type of the last item in the `HarrenVec`.
    ///
    /// # Examples
    /// ```
    /// # use hvec::hvec;
    /// use std::any::TypeId;
    ///
    /// let list = hvec![1_u8, 2_i32, 3_u64];
    /// assert_eq!(list.peek_type(), Some(TypeId::of::<u64>()));
    /// ```
    pub fn peek_type(&self) -> Option<TypeId> {
        self.types.last().copied()
    }

    /// Returns the type of the last item in the `HarrenVec`,
    /// as well as a pointer to the first byte of it.
    ///
    /// # Safety
    ///
    /// The pointer returned points to memory owned by the
    /// `HarrenVec`, and so it is only valid as long as it that
    /// data is unchanged.
    ///
    /// # Examples
    /// ```
    /// # use hvec::hvec;
    /// use std::any::TypeId;
    ///
    /// let list = hvec![1_u8, 2_i32, 3_u64];
    /// let (type_id, ptr) = list.peek_ptr().unwrap();
    ///
    /// assert_eq!(type_id, TypeId::of::<u64>());
    ///
    /// unsafe {
    ///     let ptr = ptr as *const u64;
    ///     assert_eq!(*ptr, 3_u64);
    /// }
    /// ```
    pub fn peek_ptr(&self) -> Option<(TypeId, *const u8)> {
        self.types.last().map(|&type_id| {
            let index = self.indices.last().unwrap();
            (type_id, &self.backing[*index] as *const u8)
        })
    }

    /// Returns the number of items in the `HarrenVec`.
    pub fn len(&self) -> usize {
        self.indices.len()
    }

    /// Returns the total number of bytes occupied by the
    /// contents of the `HarrenVec`.
    pub fn bytes(&self) -> usize {
        self.backing.len()
    }

    /// Returns `true` if there are no contents.
    pub fn is_empty(&self) -> bool {
        self.indices.is_empty()
    }

    /// Returns an Iterator-like structure for stepping through
    /// the contents of the `HarrenVec`.
    ///
    /// Note that because the type of each item can be
    /// different, and may not be known, this "iterator" cannot
    /// be used in `for` loops.
    ///
    /// # Examples
    ///
    /// The recommended way to use this method depends on how
    /// much you know about the contents. If there is a main
    /// type and you know in advance when that type will
    /// deviate, you can use a `while-let` loop:
    ///
    /// ```
    /// # use hvec::hvec;
    /// let list = hvec![1_usize, 2_usize, 999_usize, "Wow, big number!".to_string(), 3_usize];
    /// let mut iter = list.into_iter();
    ///
    /// let mut total = 0;
    /// while let Some(number) = iter.next::<usize>() {
    ///     if number > 100 {
    ///         let comment = iter.next::<String>().unwrap();
    ///         assert_eq!(comment, "Wow, big number!");
    ///     }
    ///     total += number;
    /// }
    /// assert_eq!(total, 1005);
    /// ```
    ///
    /// If you don't have a structure that allows you to know
    /// what type the next element is in advance, you can check
    /// the type of each item as you read it:
    ///
    /// ```
    /// # use hvec::hvec;
    /// use std::any::TypeId;
    ///
    /// let list = hvec![1_u8, 500_u16, 99999_u32];
    /// let mut iter = list.into_iter();
    ///
    /// let mut total: usize = 0;
    /// while let Some(type_id) = iter.peek_type() {
    ///     if type_id == TypeId::of::<u8>() {
    ///         total += iter.next::<u8>().unwrap() as usize;
    ///     } else if type_id == TypeId::of::<u16>() {
    ///         total += iter.next::<u16>().unwrap() as usize;
    ///     } else if type_id == TypeId::of::<u32>() {
    ///         total += iter.next::<u32>().unwrap() as usize;
    ///     }
    /// }
    /// assert_eq!(total, 100500);
    /// ```
    #[allow(clippy::should_implement_trait)]
    pub fn into_iter(self) -> HarrenVecIter {
        HarrenVecIter {
            cursor: 0,
            vec: self,
        }
    }

    /// Add an element of any type to the `HarrenVec`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hvec::HarrenVec;
    /// let mut list = HarrenVec::new();
    /// list.push(1_u8);
    /// list.push("Hello, world!".to_string());
    /// assert_eq!(list.len(), 2);
    /// ```
    pub fn push<T: 'static>(&mut self, t: T) {
        let type_id = TypeId::of::<T>();
        let ptr = &t as *const T as *const u8;
        let size = std::mem::size_of::<T>();
        let bytes = unsafe { std::slice::from_raw_parts(ptr, size) };
        self.indices.push(self.backing.len());
        self.backing.extend_from_slice(bytes);
        self.types.push(type_id);
        std::mem::forget(t);
    }

    /// Pop the last element from the `HarrenVec`.
    ///
    /// # Panics
    ///
    /// This method panics if the actual element is not an
    /// element of the specified type `T`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hvec::hvec;
    /// let mut list = hvec!["Hello".to_string()];
    /// assert_eq!(list.pop::<String>().unwrap(), "Hello".to_string());
    /// ```
    pub fn pop<T: 'static>(&mut self) -> Option<T> {
        self.types.pop().map(|type_id| {
            let index = self.indices.pop().unwrap();
            assert_eq!(TypeId::of::<T>(), type_id);

            let result = unsafe { self.take_at::<T>(index) };
            self.backing.truncate(index);
            result
        })
    }

    unsafe fn ref_at<T>(&self, offset: usize) -> &T {
        std::mem::transmute(&self.backing[offset])
    }

    unsafe fn mut_ref_at<T>(&mut self, offset: usize) -> &mut T {
        std::mem::transmute(&mut self.backing[offset])
    }

    unsafe fn take_at<T>(&self, offset: usize) -> T {
        let mut result: MaybeUninit<T> = MaybeUninit::uninit();

        let ptr = &self.backing[offset] as *const u8 as *const T;
        let dest = result.as_mut_ptr();
        dest.copy_from(ptr, 1);
        result.assume_init()
    }

    /// Returns true if this `HarrenVec` contains the element.
    ///
    /// # Examples
    /// ```
    /// # use hvec::hvec;
    /// let list = hvec![1_usize, "Hello".to_string()];
    /// assert!(list.contains::<usize>(&1));
    /// assert!(list.contains::<String>(&"Hello".to_string()));
    /// assert!(!list.contains::<isize>(&1));
    /// assert!(!list.contains::<String>(&"???".to_string()));
    /// ```
    pub fn contains<T: PartialEq<T> + 'static>(&self, x: &T) -> bool {
        for (item_index, type_id) in self.types.iter().enumerate() {
            if *type_id == TypeId::of::<T>()
                && unsafe { self.ref_at::<T>(self.indices[item_index]) == x }
            {
                return true;
            }
        }
        false
    }

    /// Return a reference to the first item of the `HarrenVec`.
    ///
    /// # Panics
    ///
    /// This method panics if the item is not of the specified
    /// type `T`.
    pub fn first<T: 'static>(&self) -> Option<&T> {
        assert_eq!(Some(&TypeId::of::<T>()), self.types.first());
        self.indices
            .first()
            .copied()
            .map(|i| unsafe { self.ref_at::<T>(i) })
    }

    /// Return a mutable reference to the first item of
    /// the `HarrenVec`.
    ///
    /// # Panics
    ///
    /// This method panics if the item is not of the specified
    /// type `T`.
    pub fn first_mut<T: 'static>(&mut self) -> Option<&mut T> {
        assert_eq!(Some(&TypeId::of::<T>()), self.types.first());
        self.indices
            .first()
            .copied()
            .map(|i| unsafe { self.mut_ref_at::<T>(i) })
    }

    /// Return a reference to the last item of the `HarrenVec`.
    ///
    /// # Panics
    ///
    /// This method panics if the item is not of the specified
    /// type `T`.
    pub fn last<T: 'static>(&self) -> Option<&T> {
        assert_eq!(Some(&TypeId::of::<T>()), self.types.last());
        self.indices
            .last()
            .copied()
            .map(|i| unsafe { self.ref_at::<T>(i) })
    }

    /// Return a mutable reference to the last item of
    /// the `HarrenVec`.
    ///
    /// # Panics
    ///
    /// This method panics if the item is not of the specified
    /// type `T`.
    pub fn last_mut<T: 'static>(&mut self) -> Option<&mut T> {
        assert_eq!(Some(&TypeId::of::<T>()), self.types.last());
        self.indices
            .last()
            .copied()
            .map(|i| unsafe { self.mut_ref_at::<T>(i) })
    }

    /// Alias of the `HarrenVec::last` method.
    pub fn peek<T: 'static>(&self) -> Option<&T> {
        self.last()
    }

    /// Alias of the `HarrenVec::last_mut` method.
    pub fn peek_mut<T: 'static>(&mut self) -> Option<&mut T> {
        self.last_mut()
    }

    /// Return a reference to the item of the `HarrenVec` at
    /// the given index.
    ///
    /// # Panics
    ///
    /// This method panics if the item is not of the specified
    /// type `T`.
    pub fn get<T: 'static>(&self, index: usize) -> Option<&T> {
        assert_eq!(Some(&TypeId::of::<T>()), self.types.get(index));
        self.indices
            .get(index)
            .copied()
            .map(|i| unsafe { self.ref_at::<T>(i) })
    }

    /// Return a mutable reference to the item of
    /// the `HarrenVec` at the given index.
    ///
    /// # Panics
    ///
    /// This method panics if the item is not of the specified
    /// type `T`.
    pub fn get_mut<T: 'static>(&mut self, index: usize) -> Option<&mut T> {
        assert_eq!(Some(&TypeId::of::<T>()), self.types.get(index));
        self.indices
            .get(index)
            .copied()
            .map(|i| unsafe { self.mut_ref_at::<T>(i) })
    }

    /// Returns the total number of elements this `HarrenVec`
    /// can store without reallocating.
    ///
    /// Note that this is separate from its capacity in bytes.
    /// Allocation will occur if either capacity is exceeded.
    pub fn item_capacity(&self) -> usize {
        std::cmp::min(self.types.capacity(), self.indices.capacity())
    }

    /// Returns the total number of bytes this `HarrenVec`
    /// can store without reallocating.
    ///
    /// Note that this is separate from its capacity in items.
    /// Allocation will occur if either capacity is exceeded.
    pub fn byte_capacity(&self) -> usize {
        self.backing.capacity()
    }

    /// Returns true if `other` contains the exact same types
    /// and bytes as this `HarrenVec`. Not that this does _not_
    /// call the actual [`PartialEq`] implementation for the
    /// stored values, so the result may not be intuitive for
    /// more complex or heap-allocated types.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hvec::hvec;
    /// let list_a = hvec![1_u8, 2_isize];
    /// let list_b = hvec![1_u8, 2_isize];
    ///
    /// let list_c = hvec![1_u8, "Hello".to_string()];
    /// let list_d = hvec![1_u8, "Hello".to_string()];
    ///
    /// // Numbers can be correctly compared as bytes
    /// assert!(list_a.bytes_eq(&list_b));
    ///
    /// // Strings contain pointers so identical strings may differ in bytes
    /// assert!(!list_c.bytes_eq(&list_d));
    /// ```
    pub fn bytes_eq(&self, other: &HarrenVec) -> bool {
        self.types == other.types && self.indices == other.indices && self.backing == other.backing
    }
}

impl HarrenVecIter {
    /// Checks the type of the next item in the iterator
    /// without actually advancing it.
    ///
    /// # Examples
    /// ```
    /// use std::any::TypeId;
    /// use hvec::hvec;
    ///
    /// let list = hvec![1_u64, 2_i32];
    /// let mut iter = list.into_iter();
    /// assert_eq!(iter.peek_type(), Some(TypeId::of::<u64>()));
    /// ```
    pub fn peek_type(&self) -> Option<TypeId> {
        self.vec.types.get(self.cursor).copied()
    }

    /// Advances the iterator and returns the next item if
    /// one exists - or else None.
    ///
    /// # Panics
    ///
    /// This method will panic if the actual type of the item
    /// differs from the `T` that this method was called with.
    ///
    /// # Examples
    /// ```
    /// use hvec::hvec;
    ///
    /// let list = hvec![1_u64, 2_i32];
    /// let mut iter = list.into_iter();
    /// assert_eq!(iter.next::<u64>(), Some(1_u64));
    /// assert_eq!(iter.next::<i32>(), Some(2_i32));
    /// assert_eq!(iter.next::<()>(), None);
    /// ```
    #[allow(clippy::should_implement_trait)]
    pub fn next<T: 'static>(&mut self) -> Option<T> {
        if self.is_empty() {
            return None;
        }

        let type_id = self.vec.types[self.cursor];
        assert_eq!(type_id, TypeId::of::<T>());

        let index = self.vec.indices[self.cursor];
        let result = unsafe { self.vec.take_at::<T>(index) };
        self.cursor += 1;
        Some(result)
    }

    /// Returns true if there are no more elements in the
    /// iterator.
    pub fn is_empty(&self) -> bool {
        self.cursor >= self.vec.len()
    }
}

/// Creates a [`HarrenVec`] containing the arguments.
///
/// # Examples
/// ```
/// use hvec::hvec;
///
/// let list_a = hvec![];
/// let list_b = hvec![1_u64; 2];
/// let list_c = hvec![1_u64, 2_i64, 3_u8];
///
/// assert!(list_a.len() == 0);
/// assert!(list_b.len() == 2);
/// assert!(list_c.len() == 3);
/// ```
#[macro_export]
macro_rules! hvec {
    () => { $crate::HarrenVec::new() };
    ($elem : expr ; $n : expr) => {{
        let mut vec = $crate::HarrenVec::new();
        for _ in 0..($n) {
            vec.push(($elem).clone());
        }
        vec
    }};
    ($($x : expr), + $(,) ?) => {{
        let mut vec = $crate::HarrenVec::new();
        $(vec.push($x);)*
        vec
    }};
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn construction_and_equality() {
        let macro_created = hvec![1_usize, 2_u8, [100_u32; 5]];
        let mut default = HVec::default();
        let mut with_cap = HVec::with_capacity(5, 64);

        {
            default.push(1_usize);
            default.push(2_u8);
            default.push([100_u32; 5]);
            with_cap.push(1_usize);
            with_cap.push(2_u8);
            with_cap.push([100_u32; 5]);
        }

        assert!(macro_created.bytes_eq(&default));
        assert!(default.bytes_eq(&with_cap));
        assert!(with_cap.bytes_eq(&macro_created));
    }

    #[test]
    fn macro_forms() {
        assert!(hvec![].bytes_eq(&HVec::default()));
        assert!(hvec![1_u8, 1_u8].bytes_eq(&hvec![1_u8; 2]));
    }

    #[test]
    fn bytes_eq_fails_for_strings() {
        let a = hvec!["Hello".to_string()];
        let b = hvec!["Hello".to_string()];
        assert!(!a.bytes_eq(&b));
    }

    #[test]
    fn capacity() {
        let mut list = HVec::with_capacity(2, 16);
        assert!(list.item_capacity() >= 2);
        assert!(list.byte_capacity() >= 16);

        list.push(1_u64);
        list.push(2_i64);
        list.push(3_u128);

        assert!(list.item_capacity() >= 3);
        assert!(list.byte_capacity() >= 32);
    }

    #[test]
    fn new_reserve() {
        let mut list = HVec::new();
        assert!(list.item_capacity() == 0);
        assert!(list.byte_capacity() == 0);

        list.reserve(4, 64);
        assert!(list.item_capacity() >= 4);
        assert!(list.byte_capacity() >= 64);
    }

    #[test]
    fn clear_truncate() {
        let mut list = hvec![1_u8, 2_i16, 3_u32, 4_i64];
        assert!(!list.is_empty());
        assert_eq!(list.len(), 4);

        unsafe {
            list.truncate(2);
            assert_eq!(list.len(), 2);
            list.clear();
            assert_eq!(list.len(), 0);
        }

        assert!(list.is_empty());
    }

    #[test]
    fn peek() {
        let list_a = hvec![11_u8, 22_i16, 33_u32];
        let list_b = hvec![11_u8, 22_i16];
        let list_c = hvec![11_u8];
        let list_d = hvec![];

        assert_eq!(list_a.peek_type(), Some(TypeId::of::<u32>()));
        assert_eq!(list_b.peek_type(), Some(TypeId::of::<i16>()));
        assert_eq!(list_c.peek_type(), Some(TypeId::of::<u8>()));
        assert_eq!(list_d.peek_type(), None);

        let (_, p_a) = list_a.peek_ptr().unwrap();
        let (_, p_b) = list_b.peek_ptr().unwrap();
        let (_, p_c) = list_c.peek_ptr().unwrap();

        unsafe {
            assert_eq!(*(p_a as *const u32), 33);
            assert_eq!(*(p_b as *const i16), 22);
            assert_eq!(*(p_c as *const u8), 11);
        }
    }

    #[test]
    fn append() {
        let mut a = hvec![1_u32, 2_u64, 3_u128];
        let mut b = hvec![4_i32, 5_i64, 6_i128];
        a.append(&mut b);

        assert!(a.len() == 6);
        assert!(b.is_empty());

        let mut iter = a.into_iter();
        assert_eq!(iter.next::<u32>(), Some(1_u32));
        assert_eq!(iter.next::<u64>(), Some(2_u64));
        assert_eq!(iter.next::<u128>(), Some(3_u128));
        assert_eq!(iter.next::<i32>(), Some(4_i32));
        assert_eq!(iter.next::<i64>(), Some(5_i64));
        assert_eq!(iter.next::<i128>(), Some(6_i128));
        assert_eq!(iter.next::<()>(), None);
    }

    #[test]
    fn push_peek_pop() {
        let mut list = hvec![];
        list.push(1_usize);
        list.push(2_u8);
        list.push("Hello".to_string());

        assert_eq!(list.peek::<String>().unwrap(), "Hello");
        assert_eq!(list.pop::<String>().unwrap(), "Hello");
        assert_eq!(list.peek::<u8>(), Some(&2));
        assert_eq!(list.pop::<u8>(), Some(2));
        assert_eq!(list.peek::<usize>(), Some(&1));
        assert_eq!(list.pop::<usize>(), Some(1));
    }

    #[test]
    fn first_last_get() {
        let a = hvec![1_u8, 2_isize, "3".to_string()];
        assert_eq!(a.first::<u8>(), Some(&1));
        assert_eq!(a.get::<isize>(1), Some(&2));
        assert_eq!(a.last::<String>(), Some(&"3".to_string()));
    }

    #[test]
    fn first_last_get_mut() {
        let mut a = hvec![1_u8, 2_isize, "3".to_string()];

        let target = a.first_mut::<u8>().unwrap();
        *target = 10;

        let target = a.get_mut::<isize>(1).unwrap();
        *target = 20;

        let target = a.last_mut::<String>().unwrap();
        *target = "30".to_string();

        assert_eq!(a.first::<u8>(), Some(&10));
        assert_eq!(a.get::<isize>(1), Some(&20));
        assert_eq!(a.last::<String>(), Some(&"30".to_string()));
    }

    #[test]
    fn contains() {
        let a = hvec![1_u8, 2_isize, "3".to_string()];
        assert!(a.contains::<u8>(&1));
        assert!(a.contains::<isize>(&2));
        assert!(a.contains::<String>(&"3".to_string()));
    }

    #[test]
    #[should_panic]
    fn wrong_first_panics() {
        let a = hvec![1_usize];
        a.first::<u8>();
    }

    #[test]
    #[should_panic]
    fn wrong_last_panics() {
        let a = hvec![1_usize];
        a.last::<u8>();
    }

    #[test]
    #[should_panic]
    fn wrong_get_panics() {
        let a = hvec![1_usize];
        a.get::<u8>(0);
    }

    #[test]
    #[should_panic]
    fn wrong_pop_panics() {
        let mut a = hvec![1_usize];
        a.pop::<u8>();
    }

    #[test]
    fn iter() {
        let mut list = HarrenVec::new();
        list.push(1_usize);
        list.push(2_u8);
        list.push("Hello".to_string());

        let mut items = list.into_iter();
        assert_eq!(items.peek_type(), Some(TypeId::of::<usize>()));
        assert_eq!(items.next::<usize>(), Some(1));
        assert_eq!(items.next::<u8>(), Some(2));
        assert_eq!(items.next::<String>(), Some("Hello".to_string()));
    }

    #[test]
    fn extra_props() {
        struct Entry {
            id: usize,
            extra: bool,
        }

        struct Extra {
            info: String,
        }

        let mut log = String::new();

        let mut list = HarrenVec::new();
        list.push(Entry {
            id: 0,
            extra: false,
        });
        list.push(Entry { id: 1, extra: true });
        list.push(Extra {
            info: "Hello".into(),
        });
        list.push(Entry {
            id: 2,
            extra: false,
        });

        let mut items = list.into_iter();
        while let Some(entry) = items.next::<Entry>() {
            log.push_str(&entry.id.to_string());
            if entry.extra {
                let extra = items.next::<Extra>().unwrap();
                log.push_str(&extra.info);
            }
        }

        assert_eq!(log, "01Hello2");
    }
}

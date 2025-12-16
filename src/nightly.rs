extern crate alloc as alloc_crate;

use alloc_crate::alloc::Allocator;
use alloc_crate::collections::{TryReserveError, TryReserveErrorKind};
use alloc_crate::vec::{self, Vec};
use composable_allocators::Global as Global;
use const_default::ConstDefault;
use core::fmt::Debug;
use core::hint::unreachable_unchecked;
use core::iter::{self, FusedIterator};
use core::mem::{align_of, replace, size_of};
use core::ops::{Index, IndexMut};
use core::slice::{self};
use either::{Either, Left, Right};

pub use crate::index::*;

type ArenaItem<I, T> = Either<<I as ArenaIndex>::Optional, T>;

/// A (mostly read-only) inner container holding [`Arena`] items.
/// While [`Arena`] itself is unique (i.e. non-clonable) object,
/// arena ['items'](Arena::items) could be cloned.
#[derive(Debug, Clone)]
pub struct ArenaItems<I: ArenaIndex, T, A: Allocator = Global> {
    vec: Vec<ArenaItem<I, T>, A>,
    vacancy: I::Optional,
}

impl<I: ArenaIndex, T, A: Allocator> ArenaItems<I, T, A> {
    /// An amount of memory required to hold one component.
    ///
    /// This information can be useful for memory management fine-tuning.
    pub const fn item_size() -> usize {
        size_of::<ArenaItem<I, T>>()
    }

    /// An alignment of a cell, holding a component with all required metadata.
    ///
    /// This information can be useful for memory management fine-tuning.
    pub const fn item_align() -> usize {
        align_of::<ArenaItem<I, T>>()
    }

    const fn new_in(alloc: A) -> Self {
        ArenaItems {
            vec: Vec::new_in(alloc),
            vacancy: I::NONE
        }
    }

    fn with_capacity_in(capacity: usize, alloc: A) -> Self {
        ArenaItems {
            vec: Vec::with_capacity_in(capacity, alloc),
            vacancy: I::NONE
        }
    }

    /// Returns a reference to the underlying allocator.
    pub fn allocator(&self) -> &A { self.vec.allocator() }

    /// Returns the number of elements the arena can hold without reallocating.
    pub fn capacity(&self) -> usize { self.vec.capacity() }

    /// Returns the number of elements in the arena.
    ///
    /// This function has linear worst-case complexity.
    pub fn len(&self) -> usize {
        let mut vacancies = 0;
        let mut vacancy = self.vacancy;
        while let Some(i) = I::to_option(vacancy) {
            vacancies += 1;
            vacancy = *self.vec[I::try_to_usize(i).unwrap()].as_ref().left().unwrap();
        }
        self.vec.len() - vacancies
    }

    /// Returns true iff the number of elements in the arena equals the maximum number of elements ever in the arena.
    ///
    /// Because the arena capacity cannot be less than `min_capacity`, the returned false means
    /// there is space for at least one more item.
    ///
    /// The returned value equals to `self.len() == self.min_capacity()`, but unlike [`len`](ArenaItems::len)
    /// this function has constant complexity.
    pub fn len_equals_to_min_capacity(&self) -> bool {
        I::to_option(self.vacancy).is_none()
    }

    /// Returns `true` if the arena contains no elements.
    ///
    /// This function has linear worst-case complexity.
    pub fn is_empty(&self) -> bool { self.vec.iter().all(|x| x.is_left()) }

    /// Returns the maximum number of elements ever in the arena.
    /// The arena capacity cannot be less than `min_capacity`.
    ///
    /// Arena `min_capacity` never decreases.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use arena_container::Arena;
    /// #
    /// # struct Data { /* ... */ }
    /// #
    /// # fn main() {
    /// let mut arena: Arena<usize, Data> = Arena::new();
    /// assert_eq!(arena.items().min_capacity(), 0);
    /// let index_1 = arena.insert(|index| (Data { /* ... */ }, index));
    /// assert_eq!(arena.items().min_capacity(), 1);
    /// let index_2 = arena.insert(|index| (Data { /* ... */ }, index));
    /// assert_eq!(arena.items().min_capacity(), 2);
    /// arena.remove(index_1);
    /// assert_eq!(arena.items().min_capacity(), 2);
    /// let index_3 = arena.insert(|index| (Data { /* ... */ }, index));
    /// assert_eq!(arena.items().min_capacity(), 2);
    /// let index_4 = arena.insert(|index| (Data { /* ... */ }, index));
    /// assert_eq!(arena.items().min_capacity(), 3);
    /// # }
    /// ```
    pub fn min_capacity(&self) -> usize { self.vec.len() }

    /// Reserves capacity for at least `additional` more elements.
    /// The collection may reserve more space to avoid frequent reallocations.
    /// After calling `reserve`, capacity will be greater than or equal to
    /// `self.min_capacity() + additional`. Does nothing if capacity is already sufficient.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows usize.
    pub fn reserve(&mut self, additional: usize) { self.vec.reserve(additional) }

    /// Reserves the minimum capacity for exactly `additional` more elements.
    /// After calling `reserve_exact`, capacity will be greater than or equal to
    /// `self.min_capacity() + additional`. Does nothing if the capacity is already sufficient.
    ///
    /// Note that the allocator may give the collection more space than it requests.
    /// Therefore, capacity can not be relied upon to be precisely minimal.
    /// Prefer [`reserve`](ArenaItems::reserve) if future insertions are expected.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows usize.
    pub fn reserve_exact(&mut self, additional: usize) { self.vec.reserve_exact(additional) }

    /// Shrinks the capacity of the arena with a lower bound.
    ///
    /// The capacity will remain at least as large as both the [`min_capacity`](ArenaItems::min_capacity)
    /// and the supplied value.
    pub fn shrink_to(&mut self, min_capacity: usize) { self.vec.shrink_to(min_capacity) }

    /// Shrinks the capacity of the vector as much as possible.
    ///
    /// It will drop down as close as possible to the [`min_capacity`](ArenaItems::min_capacity)
    /// but the allocator may still inform the arena that there is space for a few more elements.
    pub fn shrink_to_fit(&mut self) { self.vec.shrink_to_fit() }

    /// Tries to reserve capacity for at least additional more elements.
    /// The collection may reserve more space to avoid frequent reallocations.
    /// After calling `try_reserve`, capacity will be greater than or equal
    /// to `self.min_capacity() + additional`. Does nothing if capacity is already sufficient.
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an error is returned.
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.vec.try_reserve(additional)
    }

    /// Tries to reserve capacity for exactly `additional` more elements.
    /// The collection may reserve more space to avoid frequent reallocations.
    /// After calling `try_reserve_exact`, capacity will be greater than or equal
    /// to `self.min_capacity() + additional`. Does nothing if capacity is already sufficient.
    ///
    /// Note that the allocator may give the collection more space than it requests.
    /// Therefore, capacity can not be relied upon to be precisely minimal.
    /// Prefer [`try_reserve`](ArenaItems::try_reserve) if future insertions are expected.
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an error is returned.
    pub fn try_reserve_exact(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.vec.try_reserve_exact(additional)
    }

    /// Returns reference to the item occupying `index` place, or `None` if there is no such.
    ///
    /// # Panics
    ///
    /// Panics if `index` is greater than or equal to [`min_capacity()`](ArenaItems::min_capacity).
    pub fn get_value(&self, index: usize) -> Option<&T> {
        self.vec[index].as_ref().right()
    }

    /// Returns mutable reference to the item occupying `index` place, or `None` if there is no such.
    ///
    /// # Panics
    ///
    /// Panics if `index` is greater than or equal to [`min_capacity()`](ArenaItems::min_capacity).
    pub fn get_value_mut(&mut self, index: usize) -> Option<&mut T> {
        self.vec[index].as_mut().right()
    }

    /// Returns an iterator over all occupied indices.
    pub fn indices(&self) -> ArenaItemsIndices<'_, I, T> {
        ArenaItemsIndices(self.vec.iter().enumerate())
    }

    /// Returns an iterator over all items.
    pub fn values(&self) -> ArenaItemsValues<'_, I, T> {
        ArenaItemsValues(self.vec.iter())
    }

    /// Returns a mutable iterator over all items.
    pub fn values_mut(&mut self) -> ArenaItemsValuesMut<'_, I, T> {
        ArenaItemsValuesMut(self.vec.iter_mut())
    }

    /// Returns an iterator over all items combined with their indices.
    pub fn iter(&self) -> ArenaItemsIter<'_, I, T> {
        ArenaItemsIter(self.vec.iter().enumerate())
    }

    /// Returns a mutable iterator over all items combined with their indices.
    pub fn iter_mut(&mut self) -> ArenaItemsIterMut<'_, I, T> {
        ArenaItemsIterMut(self.vec.iter_mut().enumerate())
    }

    /// Transforms the container into an iterator over all occupied indices.
    pub fn into_indices(self) -> ArenaItemsIntoIndices<I, T, A> {
        ArenaItemsIntoIndices(self.vec.into_iter().enumerate())
    }

    /// Transforms the container into an iterator over all items.
    pub fn into_values(self) -> ArenaItemsIntoValues<I, T, A> {
        ArenaItemsIntoValues(self.vec.into_iter())
    }
}

/// An iterator over all items combined with their ids.
///
/// Usually created by the [`ArenaItems::iter`](ArenaItems::iter) method.
#[derive(Debug, Clone)]
pub struct ArenaItemsIter<'a, I: ArenaIndex, T>(
    iter::Enumerate<slice::Iter<'a, Either<I::Optional, T>>>
);

impl<'a, I: ArenaIndex, T> Iterator for ArenaItemsIter<'a, I, T> {
    type Item = (I, &'a T);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.0.next() {
                None => return None,
                Some((_, Left(_))) => { },
                Some((index, Right(item))) =>
                    return Some((I::try_from_usize(index).unwrap(), item)),
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, self.0.size_hint().1)
    }
}

impl<'a, I: ArenaIndex, T> DoubleEndedIterator for ArenaItemsIter<'a, I, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        loop {
            match self.0.next_back() {
                None => return None,
                Some((_, Left(_))) => { },
                Some((index, Right(item))) =>
                    return Some((I::try_from_usize(index).unwrap(), item)),
            }
        }
    }
}

impl<'a, I: ArenaIndex, T> FusedIterator for ArenaItemsIter<'a, I, T> { }

/// A mutable iterator over all items combined with their ids.
///
/// Usually created by the [`ArenaItems::iter_mut`](ArenaItems::iter_mut) method.
#[derive(Debug)]
pub struct ArenaItemsIterMut<'a, I: ArenaIndex, T>(
    iter::Enumerate<slice::IterMut<'a, Either<I::Optional, T>>>
);

impl<'a, I: ArenaIndex, T> Iterator for ArenaItemsIterMut<'a, I, T> {
    type Item = (I, &'a mut T);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.0.next() {
                None => return None,
                Some((_, Left(_))) => { },
                Some((index, Right(item))) =>
                    return Some((I::try_from_usize(index).unwrap(), item)),
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, self.0.size_hint().1)
    }
}

impl<'a, I: ArenaIndex, T> DoubleEndedIterator for ArenaItemsIterMut<'a, I, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        loop {
            match self.0.next_back() {
                None => return None,
                Some((_, Left(_))) => { },
                Some((index, Right(item))) =>
                    return Some((I::try_from_usize(index).unwrap(), item)),
            }
        }
    }
}

impl<'a, I: ArenaIndex, T> FusedIterator for ArenaItemsIterMut<'a, I, T> { }

/// An iterator over all items ids.
///
/// Usually created by the [`ArenaItems::indices`](ArenaItems::indices) method.
#[derive(Debug, Clone)]
pub struct ArenaItemsIndices<'a, I: ArenaIndex, T>(
    iter::Enumerate<slice::Iter<'a, Either<I::Optional, T>>>
);

impl<'a, I: ArenaIndex, T> Iterator for ArenaItemsIndices<'a, I, T> {
    type Item = I;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.0.next() {
                None => return None,
                Some((_, Left(_))) => { },
                Some((index, Right(_))) => return Some(I::try_from_usize(index).unwrap()),
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, self.0.size_hint().1)
    }
}

impl<'a, I: ArenaIndex, T> DoubleEndedIterator for ArenaItemsIndices<'a, I, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        loop {
            match self.0.next_back() {
                None => return None,
                Some((_, Left(_))) => { },
                Some((index, Right(_))) => return Some(I::try_from_usize(index).unwrap()),
            }
        }
    }
}

impl<'a, I: ArenaIndex, T> FusedIterator for ArenaItemsIndices<'a, I, T> { }

/// An iterator over all items.
///
/// Usually created by the [`ArenaItems::values`](ArenaItems::values) method.
#[derive(Debug, Clone)]
pub struct ArenaItemsValues<'a, I: ArenaIndex, T>(
    slice::Iter<'a, Either<I::Optional, T>>
);

impl<'a, I: ArenaIndex, T> Iterator for ArenaItemsValues<'a, I, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.0.next() {
                None => return None,
                Some(Left(_)) => { },
                Some(Right(item)) => return Some(item),
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, self.0.size_hint().1)
    }
}

impl<'a, I: ArenaIndex, T> DoubleEndedIterator for ArenaItemsValues<'a, I, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        loop {
            match self.0.next_back() {
                None => return None,
                Some(Left(_)) => { },
                Some(Right(item)) => return Some(item),
            }
        }
    }
}

impl<'a, I: ArenaIndex, T> FusedIterator for ArenaItemsValues<'a, I, T> { }

/// A mutable iterator over all items.
///
/// Usually created by the [`ArenaItems::values_mut`](ArenaItems::values_mut) method.
#[derive(Debug)]
pub struct ArenaItemsValuesMut<'a, I: ArenaIndex, T>(
    slice::IterMut<'a, Either<I::Optional, T>>
);

impl<'a, I: ArenaIndex, T> Iterator for ArenaItemsValuesMut<'a, I, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.0.next() {
                None => return None,
                Some(Left(_)) => { },
                Some(Right(item)) => return Some(item),
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, self.0.size_hint().1)
    }
}

impl<'a, I: ArenaIndex, T> DoubleEndedIterator for ArenaItemsValuesMut<'a, I, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        loop {
            match self.0.next_back() {
                None => return None,
                Some(Left(_)) => { },
                Some(Right(item)) => return Some(item),
            }
        }
    }
}

impl<'a, I: ArenaIndex, T> FusedIterator for ArenaItemsValuesMut<'a, I, T> { }

/// An iterator over all occupied indices.
///
/// Usually created by the [`ArenaItems::into_indices`](ArenaItems::into_indices) method.
#[derive(Debug)]
pub struct ArenaItemsIntoIndices<I: ArenaIndex, T, A: Allocator = Global>(
    iter::Enumerate<vec::IntoIter<Either<I::Optional, T>, A>>,
);

impl<I: ArenaIndex, T, A: Allocator> Iterator for ArenaItemsIntoIndices<I, T, A> {
    type Item = I;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.0.next() {
                None => return None,
                Some((_, Left(_))) => { },
                Some((index, Right(_))) => return Some(I::try_from_usize(index).unwrap()),
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, self.0.size_hint().1)
    }
}

impl<I: ArenaIndex, T, A: Allocator> DoubleEndedIterator for ArenaItemsIntoIndices<I, T, A> {
    fn next_back(&mut self) -> Option<Self::Item> {
        loop {
            match self.0.next_back() {
                None => return None,
                Some((_, Left(_))) => { },
                Some((index, Right(_))) => return Some(I::try_from_usize(index).unwrap()),
            }
        }
    }
}

impl<I: ArenaIndex, T, A: Allocator> FusedIterator for ArenaItemsIntoIndices<I, T, A> { }

/// An iterator over all items.
///
/// Usually created by the [`ArenaItems::into_values`](ArenaItems::into_values) method.
#[derive(Debug)]
pub struct ArenaItemsIntoValues<I: ArenaIndex, T, A: Allocator = Global>(
    vec::IntoIter<Either<I::Optional, T>, A>,
);

impl<I: ArenaIndex, T, A: Allocator> Iterator for ArenaItemsIntoValues<I, T, A> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.0.next() {
                None => return None,
                Some(Left(_)) => { },
                Some(Right(item)) => return Some(item),
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, self.0.size_hint().1)
    }
}

impl<I: ArenaIndex, T, A: Allocator> DoubleEndedIterator for ArenaItemsIntoValues<I, T, A> {
    fn next_back(&mut self) -> Option<Self::Item> {
        loop {
            match self.0.next_back() {
                None => return None,
                Some(Left(_)) => { },
                Some(Right(item)) => return Some(item),
            }
        }
    }
}

impl<I: ArenaIndex, T, A: Allocator> FusedIterator for ArenaItemsIntoValues<I, T, A> { }

/// An iterator over all items combined with their ids.
///
/// Usually created by the [`ArenaItems::into_iter`](ArenaItems::into_iter) method.
#[derive(Debug, Clone)]
pub struct ArenaItemsIntoIter<I: ArenaIndex, T, A: Allocator = Global>(
    iter::Enumerate<vec::IntoIter<Either<I::Optional, T>, A>>,
);

impl<I: ArenaIndex, T, A: Allocator> Iterator for ArenaItemsIntoIter<I, T, A> {
    type Item = (I, T);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.0.next() {
                None => return None,
                Some((_, Left(_))) => { },
                Some((index, Right(item))) =>
                    return Some((I::try_from_usize(index).unwrap(), item)),
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, self.0.size_hint().1)
    }
}

impl<I: ArenaIndex, T, A: Allocator> DoubleEndedIterator for ArenaItemsIntoIter<I, T, A> {
    fn next_back(&mut self) -> Option<Self::Item> {
        loop {
            match self.0.next_back() {
                None => return None,
                Some((_, Left(_))) => { },
                Some((index, Right(item))) =>
                    return Some((I::try_from_usize(index).unwrap(), item)),
            }
        }
    }
}

impl<I: ArenaIndex, T, A: Allocator> FusedIterator for ArenaItemsIntoIter<I, T, A> { }

impl<I: ArenaIndex, T, A: Allocator> IntoIterator for ArenaItems<I, T, A> {
    type Item = (I, T);
    type IntoIter = ArenaItemsIntoIter<I, T, A>;

    fn into_iter(self) -> Self::IntoIter {
        ArenaItemsIntoIter(self.vec.into_iter().enumerate())
    }
}

impl<'a, I: ArenaIndex, T, A: Allocator> IntoIterator for &'a ArenaItems<I, T, A> {
    type Item = (I, &'a T);
    type IntoIter = ArenaItemsIter<'a, I, T>;

    fn into_iter(self) -> Self::IntoIter { self.iter() }
}

mod forgettable_field {
    use core::fmt::{self, Debug, Formatter};
    use core::mem::{MaybeUninit, forget, replace};
    use core::ops::{Deref, DerefMut};

    pub struct ForgettableField<T>(MaybeUninit<T>);

    impl<T> ForgettableField<T> {
        pub const fn new(value: T) -> Self { ForgettableField(MaybeUninit::new(value)) }

        pub fn into_inner(mut this: Self) -> T {
            let inner = replace(&mut this.0, MaybeUninit::uninit());
            forget(this);
            unsafe { inner.assume_init() }
        }

        pub fn take_and_forget<Owner>(mut owner: Owner, f: impl FnOnce(&mut Owner) -> &mut Self) -> T {
            let this = replace(f(&mut owner), ForgettableField(MaybeUninit::uninit()));
            forget(owner);
            Self::into_inner(this)
        }
    }

    impl<T> Drop for ForgettableField<T> {
        fn drop(&mut self) {
            unsafe { self.0.assume_init_drop() }
        }
    }

    impl<T> Deref for ForgettableField<T> {
        type Target = T;

        fn deref(&self) -> &T { unsafe { self.0.assume_init_ref() } }
    }

    impl<T> DerefMut for ForgettableField<T> {
        fn deref_mut(&mut self) -> &mut T { unsafe { self.0.assume_init_mut() } }
    }

    impl<T: Default> Default for ForgettableField<T> {
        fn default() -> Self { ForgettableField::new(T::default()) }
    }

    impl<T: Debug> Debug for ForgettableField<T> {
        fn fmt(&self, f: &mut Formatter) -> fmt::Result {
            self.deref().fmt(f)
        }
    }
}

use forgettable_field::*;

/// Unordered container with random access.
#[derive(Debug)]
pub struct Arena<I: ArenaIndex, T: 'static, A: Allocator = Global> {
    items: ForgettableField<ArenaItems<I, T, A>>,
}

impl<I: ArenaIndex, T, A: Allocator> Arena<I, T, A> {
    /// Creates an arena instance.
    pub const fn new() -> Self where A: ConstDefault {
        Self::new_in(ConstDefault::DEFAULT)
    }

    /// Creates an arena instance with the specified initial capacity.
    pub fn with_capacity(capacity: usize) -> Self where A: ConstDefault {
        Self::with_capacity_in(capacity, ConstDefault::DEFAULT)
    }

    /// Creates an arena instance.
    pub const fn new_in(alloc: A) -> Self {
        Arena {
            items: ForgettableField::new(ArenaItems::new_in(alloc))
        }
    }

    /// Creates an arena instance with the specified initial capacity.
    pub fn with_capacity_in(capacity: usize, alloc: A) -> Self {
        Arena {
            items: ForgettableField::new(ArenaItems::with_capacity_in(capacity, alloc))
        }
    }

    /// Returns contained items packed in a special container.
    /// While arena itself is unique (i.e. non-clonable) object,
    /// this special container could be cloned.
    pub fn into_items(#[allow(unused_mut)] mut self) -> ArenaItems<I, T, A> {
        ForgettableField::take_and_forget(self, |x| &mut x.items)
    }

    /// Returns reference to contained items packed in a special container.
    /// While arena itself is unique (i.e. non-clonable) object,
    /// this special container could be cloned.
    pub fn items(&self) -> &ArenaItems<I, T, A> { &self.items }

    /// Returns mutable reference to contained items packed in
    /// a (mostly read-only) special container.
    /// While arena itself is unique (i.e. non-clonable) object,
    /// this special container could be cloned.
    pub fn items_mut(&mut self) -> &mut ArenaItems<I, T, A> { &mut self.items }

    /// Reserves capacity for at least one more element.
    /// The collection may reserve more space to avoid frequent reallocations.
    /// After calling `reserve`, capacity will be greater than or equal to
    /// `self.items().len() + 1`. Does nothing if capacity is already sufficient.
    ///
    /// # Panics
    ///
    /// Panics if the required capacity overflows maximum index value + 1.
    pub fn reserve(&mut self) {
        if self.items().len_equals_to_min_capacity() {
            self.items_mut().reserve(1);
            assert!(I::try_from_usize(self.items().min_capacity()).is_some());
        }
    }

    /// Reserves the minimum capacity for exactly one more element.
    /// After calling `reserve_exact`, capacity will be greater than or equal to
    /// `self.items().len() + 1`. Does nothing if the capacity is already sufficient.
    ///
    /// Note that the allocator may give the collection more space than it requests.
    /// Therefore, capacity can not be relied upon to be precisely minimal.
    /// Prefer [`reserve`](Arena::reserve) if future insertions are expected.
    ///
    /// # Panics
    ///
    /// Panics if the required capacity overflows maximum index value + 1.
    pub fn reserve_exact(&mut self) {
        if self.items().len_equals_to_min_capacity() {
            self.items_mut().reserve_exact(1);
            assert!(I::try_from_usize(self.items().min_capacity()).is_some());
        }
    }

    /// Tries to reserve capacity for at least one more element.
    /// The collection may reserve more space to avoid frequent reallocations.
    /// After calling `try_reserve`, capacity will be greater than or equal
    /// to `self.items().len() + 1`. Does nothing if capacity is already sufficient.
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an error is returned.
    pub fn try_reserve(&mut self) -> Result<(), TryReserveError> {
        if self.items().len_equals_to_min_capacity() {
            self.items_mut().try_reserve(1)?;
            I::try_from_usize(self.items().min_capacity())
                .ok_or(TryReserveError::from(TryReserveErrorKind::CapacityOverflow)).map(|_| ())
        } else {
            Ok(())
        }
    }

    /// Tries to reserve capacity for exactly one more element.
    /// The collection may reserve more space to avoid frequent reallocations.
    /// After calling `try_reserve_exact`, capacity will be greater than or equal
    /// to `self.items().len() + 1`. Does nothing if capacity is already sufficient.
    ///
    /// Note that the allocator may give the collection more space than it requests.
    /// Therefore, capacity can not be relied upon to be precisely minimal.
    /// Prefer [`try_reserve`](Arena::try_reserve) if future insertions are expected.
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an error is returned.
    pub fn try_reserve_exact(&mut self) -> Result<(), TryReserveError> {
        if self.items().len_equals_to_min_capacity() {
            self.items_mut().try_reserve_exact(1)?;
            I::try_from_usize(self.items().min_capacity())
                .ok_or(TryReserveError::from(TryReserveErrorKind::CapacityOverflow)).map(|_| ())
        } else {
            Ok(())
        }
    }

    /// Place new component into the arena.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use arena_container::Arena;
    /// #
    /// # struct Data { /* ... */ }
    /// #
    /// # fn main() {
    /// let mut arena: Arena<usize, Data> = Arena::new();
    /// let new_item_index = arena.insert(|index| (Data { /* ... */ }, index));
    /// # }
    /// ```
    pub fn insert<R>(&mut self, item: impl FnOnce(I) -> (T, R)) -> R {
        if let Some(index) = I::to_option(self.items.vacancy) {
            let (item, result) = item(index);
            self.items.vacancy = replace(&mut self.items.vec[I::try_to_usize(index).unwrap()], Right(item)).left()
                .unwrap_or_else(|| unsafe { unreachable_unchecked() });
            result
        } else {
            let index = I::try_from_usize(self.items.len()).expect("out of indices");
            let (item, result) = item(index);
            self.items.vec.push(Right(item));
            result
        }
    }

    /// Removes component with provided index.
    ///
    /// Panics if index is not occupied.
    pub fn remove(&mut self, index: I) -> T {
        let vacancy = self.items.vacancy;
        match replace(&mut self.items.vec[I::try_to_usize(index).expect("invalid index")], Left(vacancy)) {
            Left(vacancy) => {
                self.items.vec[I::try_to_usize(index).unwrap()] = Left(vacancy);
                panic!("invalid index");
            },
            Right(item) => {
                self.items.vacancy = I::some(index);
                item
            }
        }
    }
}

impl<I: ArenaIndex, T, A: Allocator> Default for Arena<I, T, A> where A: ConstDefault {
    fn default() -> Self { Arena::new() }
}

impl<I: ArenaIndex, T, A: Allocator> Index<I> for Arena<I, T, A> {
    type Output = T;

    fn index(&self, index: I) -> &T {
        self.items.vec[I::try_to_usize(index).expect("invalid index")].as_ref().right().expect("invalid index")
    }
}

impl<I: ArenaIndex, T, A: Allocator> IndexMut<I> for Arena<I, T, A> {
    fn index_mut(&mut self, index: I) -> &mut T {
        self.items.vec[I::try_to_usize(index).expect("invalid index")].as_mut().right().expect("invalid index")
    }
}

#[cfg(test)]
mod test {
    use quickcheck_macros::quickcheck;

    use core::num::NonZeroU32;
    use core::sync::atomic::{AtomicI8, Ordering};
    use crate::*;

    struct Test {
        this: NonZeroU32,
        value: i8
    }

    const fn _new_test_arena() -> Arena<NonZeroU32, Test> {
        Arena::new()
    }

    struct TestWithDrop {
        value: i8
    }

    static TEST_DROP: AtomicI8 = AtomicI8::new(-1);

    const fn _new_test_with_drop_arena() -> Arena<NonZeroU32, TestWithDrop> {
        Arena::new()
    }

    impl Drop for TestWithDrop {
        fn drop(&mut self) {
            TEST_DROP.store(self.value, Ordering::SeqCst);
        }
    }

    #[quickcheck]
    fn new_arena_min_capacity_is_zero(capacity: Option<u8>) -> bool {
        let capacity = capacity.map(|capacity| capacity as usize);
        capacity.map_or_else(
            || <Arena::<NonZeroU32, Test>>::new(),
            |capacity| <Arena::<NonZeroU32, Test>>::with_capacity(capacity)
        ).items().min_capacity() == 0
    }

    #[quickcheck]
    fn arena_contains_inserted_item(capacity: Option<u8>, value: i8) -> bool {
        let capacity = capacity.map(|capacity| capacity as usize);
        let mut arena = capacity.map_or_else(
            || <Arena::<NonZeroU32, Test>>::new(),
            |capacity| <Arena::<NonZeroU32, Test>>::with_capacity(capacity)
        );
        let index = arena.insert(|this| (Test { this, value }, this));
        arena[index].this == index && arena[index].value == value
    }

    #[test]
    fn drop_components() {
        {
            let mut arena: Arena<NonZeroU32, TestWithDrop> = Arena::new();
            arena.insert(|this: NonZeroU32| (TestWithDrop { value: 7 }, this));
            TEST_DROP.store(-1, Ordering::SeqCst);
        }
        assert_eq!(TEST_DROP.load(Ordering::SeqCst), 7);
    }

    #[test]
    fn try_reserve() {
        let mut arena: Arena<i8, ()> = Arena::new();
        while arena.try_reserve().is_ok() {
            arena.insert(|_| ((), ()));
        }
    }
}

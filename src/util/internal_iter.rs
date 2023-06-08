use std::collections::VecDeque;
use std::iter;
use std::iter::Sum;
use std::ops::ControlFlow;

use crate::util::{Never, NeverExt};

/// Alternative to `std::ops::Try` (which is not yet stable).
pub trait Try {
    type B;
    fn to_control_flow(self) -> ControlFlow<Self::B>;
    fn from_control_flow(control: ControlFlow<Self::B>) -> Self;
}

/// Alternative to the `internal_iterator` crate, but we support all `Try` types instead of only `ControlFlow`.
pub trait InternalIterator: Sized {
    type Item;

    // We use ControlFlow for the implementation so it can use the `?` operator.
    fn try_for_each_impl<B>(self, f: impl FnMut(Self::Item) -> ControlFlow<B>) -> ControlFlow<B>;

    fn try_for_each<T: Try>(self, mut f: impl FnMut(Self::Item) -> T) -> T {
        T::from_control_flow(self.try_for_each_impl(|item| f(item).to_control_flow()))
    }

    fn for_each(self, f: impl FnMut(Self::Item)) {
        self.try_for_each(f)
    }

    fn map<T, F: FnMut(Self::Item) -> T>(self, f: F) -> Map<Self, F> {
        Map(self, f)
    }

    fn filter_map<T, F: FnMut(Self::Item) -> Option<T>>(self, f: F) -> FilterMap<Self, F> {
        FilterMap(self, f)
    }

    fn filter<F: FnMut(&Self::Item) -> bool>(self, f: F) -> Filter<Self, F> {
        Filter(self, f)
    }

    fn find_map<T, F: FnMut(Self::Item) -> Option<T>>(self, mut f: F) -> Option<T> {
        let result = self.try_for_each_impl(|item| match f(item) {
            Some(value) => ControlFlow::Break(value),
            None => ControlFlow::Continue(()),
        });

        match result {
            ControlFlow::Continue(()) => None,
            ControlFlow::Break(value) => Some(value),
        }
    }

    // TODO refactor this to be more similar to vec.extend
    fn sink_to<R: FromInternalIterator<Self::Item>>(self, result: &mut R) {
        self.for_each(|item| result.push(item));
    }

    fn collect<R: Default + FromInternalIterator<Self::Item>>(self) -> R {
        let mut result = R::default();
        self.sink_to(&mut result);
        result
    }

    fn collect_vec(self) -> Vec<Self::Item> {
        self.collect()
    }

    fn try_all<E>(self, mut f: impl FnMut(Self::Item) -> Result<bool, E>) -> Result<bool, E> {
        enum AllBreak<E> {
            FoundFalse,
            Err(E),
        }

        let result = self.try_for_each_impl(|item| match f(item) {
            Ok(true) => ControlFlow::Continue(()),
            Ok(false) => ControlFlow::Break(AllBreak::FoundFalse),
            Err(e) => ControlFlow::Break(AllBreak::Err(e)),
        });

        match result {
            ControlFlow::Continue(()) => Ok(true),
            ControlFlow::Break(AllBreak::FoundFalse) => Ok(false),
            ControlFlow::Break(AllBreak::Err(e)) => Err(e),
        }
    }

    fn all(self, mut f: impl FnMut(Self::Item) -> bool) -> bool {
        self.try_all(|item| Ok(f(item))).no_err()
    }

    fn sum(self) -> Self::Item where Self::Item: Copy + Sum<Self::Item> {
        // we abuse the way std::iter::Sum works a lot, but it should be fine
        let mut curr = iter::empty().sum();
        self.for_each(|item| {
            curr = iter::once(curr).chain(iter::once(item)).sum();
        });
        curr
    }

    fn count(self) -> usize {
        let mut result = 0;
        self.for_each(|_| result += 1);
        result
    }

    fn single(self) -> Option<Self::Item> {
        let mut first = None;
        let result = self.try_for_each_impl(|curr| {
            match first {
                None => {
                    first = Some(curr);
                    ControlFlow::Continue(())
                }
                Some(_) => {
                    ControlFlow::Break(())
                }
            }
        });
        match result {
            ControlFlow::Continue(_) => first,
            ControlFlow::Break(_) => None,
        }
    }

    fn single_unique(self) -> Option<Self::Item> where Self::Item: PartialEq {
        let mut first = None;
        let _ = self.try_for_each_impl(|curr| {
            match &first {
                None => {
                    first = Some(curr);
                    ControlFlow::Continue(())
                },
                Some(curr_first) => {
                    if curr_first == &curr {
                        ControlFlow::Continue(())
                    } else {
                        first = None;
                        ControlFlow::Break(())
                    }
                }
            }
        });
        first
    }
}

/// Types that can be used in [InternalIterator::collect] or [InternalIterator::sink].
pub trait FromInternalIterator<T> {
    fn push(&mut self, value: T);
}

// boring wrapper types
#[derive(Debug, Clone)]
pub struct Map<I, F>(I, F);

impl<T, I: InternalIterator, F: FnMut(I::Item) -> T> InternalIterator for Map<I, F> {
    type Item = T;
    fn try_for_each_impl<B>(self, mut f: impl FnMut(Self::Item) -> ControlFlow<B>) -> ControlFlow<B> {
        let Map(inner, mut map) = self;
        inner.try_for_each_impl(|item| {
            f(map(item))
        })
    }
}

#[derive(Debug, Clone)]
pub struct FilterMap<I, F>(I, F);

impl<T, I: InternalIterator, F: FnMut(I::Item) -> Option<T>> InternalIterator for FilterMap<I, F> {
    type Item = T;
    fn try_for_each_impl<B>(self, mut f: impl FnMut(Self::Item) -> ControlFlow<B>) -> ControlFlow<B> {
        let FilterMap(inner, mut filter_map) = self;
        inner.try_for_each_impl(|item| {
            match filter_map(item) {
                Some(mapped) => f(mapped)?,
                None => {}
            }
            ControlFlow::Continue(())
        })
    }
}

#[derive(Debug, Clone)]
pub struct Filter<I, F>(I, F);

impl<I: InternalIterator, F: FnMut(&I::Item) -> bool> InternalIterator for Filter<I, F> {
    type Item = I::Item;
    fn try_for_each_impl<B>(self, mut f: impl FnMut(Self::Item) -> ControlFlow<B>) -> ControlFlow<B> {
        let Filter(inner, mut filter) = self;
        inner.try_for_each_impl(|item| {
            match filter(&item) {
                true => f(item)?,
                false => {}
            }
            ControlFlow::Continue(())
        })
    }
}

// boring implementations
impl<E> Try for Result<(), E> {
    type B = E;
    fn to_control_flow(self) -> ControlFlow<Self::B> {
        match self {
            Ok(()) => ControlFlow::Continue(()),
            Err(e) => ControlFlow::Break(e),
        }
    }
    fn from_control_flow(control: ControlFlow<Self::B>) -> Self {
        match control {
            ControlFlow::Continue(()) => Ok(()),
            ControlFlow::Break(e) => Err(e),
        }
    }
}

impl Try for () {
    type B = Never;
    fn to_control_flow(self) -> ControlFlow<Self::B> {
        ControlFlow::Continue(())
    }
    fn from_control_flow(control: ControlFlow<Self::B>) -> Self {
        match control {
            ControlFlow::Continue(()) => (),
            ControlFlow::Break(_) => unreachable!(),
        }
    }
}

impl<B> Try for ControlFlow<B, ()> {
    type B = B;

    fn to_control_flow(self) -> ControlFlow<Self::B> {
        self
    }

    fn from_control_flow(control: ControlFlow<Self::B>) -> Self {
        control
    }
}

impl<T> FromInternalIterator<T> for Vec<T> {
    fn push(&mut self, value: T) {
        self.push(value)
    }
}

impl<T> FromInternalIterator<T> for VecDeque<T> {
    fn push(&mut self, value: T) {
        self.push_back(value)
    }
}

#[derive(Debug, Clone)]
pub struct WrapIterator<I>(I);

pub trait IterExt: Iterator + Sized {
    fn into_internal(self) -> WrapIterator<Self>;
    fn single(self) -> Option<Self::Item>;
    fn single_unique(self) -> Option<Self::Item> where Self::Item : PartialEq;
}

impl<I: Iterator> IterExt for I {
    fn into_internal(self) -> WrapIterator<Self> {
        WrapIterator(self)
    }

    fn single(self) -> Option<Self::Item> {
        self.into_internal().single()
    }

    fn single_unique(self) -> Option<Self::Item> where Self::Item: PartialEq {
        self.into_internal().single_unique()
    }
}

impl<I: Iterator> InternalIterator for WrapIterator<I> {
    type Item = I::Item;

    fn try_for_each_impl<B>(self, mut f: impl FnMut(Self::Item) -> ControlFlow<B>) -> ControlFlow<B> {
        for x in self.0 {
            f(x)?;
        }
        ControlFlow::Continue(())
    }
}

#[cfg(test)]
mod test {
    use crate::util::internal_iter::IterExt;

    #[test]
    fn single() {
        let none: Option<&i32> = None;
        assert_eq!([].iter().single(), none);
        assert_eq!([1].iter().single(), Some(&1));
        assert_eq!([1, 2].iter().single(), none);
        assert_eq!([1, 2, 3].iter().single(), none);
    }
}
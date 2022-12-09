#[macro_use]
pub mod arena;

pub trait IndexMutTwice<T> {
    fn index_mut_twice(&mut self, a: usize, b: usize) -> Option<(&mut T, &mut T)>;
}

impl<T> IndexMutTwice<T> for [T] {
    fn index_mut_twice(&mut self, a: usize, b: usize) -> Option<(&mut T, &mut T)> {
        if a != b {
            unsafe {
                Some((
                    &mut *(&mut self[a] as *mut _),
                    &mut *(&mut self[b] as *mut _),
                ))
            }
        } else {
            None
        }
    }
}

pub fn zip_eq<L: ExactSizeIterator, R: ExactSizeIterator>(
    left: impl IntoIterator<IntoIter=L>,
    right: impl IntoIterator<IntoIter=R>,
) -> std::iter::Zip<L, R> {
    let left = left.into_iter();
    let right = right.into_iter();

    assert_eq!(left.len(), right.len(), "iterators are not the same length");
    left.zip(right)
}

#[allow(unused_macros)]
macro_rules! assert_match {
    ($value: expr, $($pattern: pat)|+) => {
        match $value {
            $($pattern)|+ => (),
            ref value =>
                panic!("assert_match failed: `{:?}` does not match `{}`", value, stringify!($($pattern)|+)),
        }
    };
}

#[allow(unused_macros)]
macro_rules! unwrap_match {
    ($value: expr, $($pattern: pat)|+ => $result: expr) => {
        match $value {
            $($pattern)|+ =>
                $result,
            ref value =>
                panic!("unwrap_match failed: `{:?}` does not match `{}`", value, stringify!($($pattern)|+)),
        }
    };
}

pub trait VecExt {
    type T;
    fn index_of(&self, value: &Self::T) -> Option<usize>;
}

impl<T: Eq> VecExt for &[T] {
    type T = T;
    fn index_of(&self, value: &Self::T) -> Option<usize> {
        self.iter().position(|cand| cand == value)
    }
}

impl<T: Eq> VecExt for Vec<T> {
    type T = T;
    fn index_of(&self, value: &Self::T) -> Option<usize> {
        self.iter().position(|cand| cand == value)
    }
}

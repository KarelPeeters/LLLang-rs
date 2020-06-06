use std::collections::HashMap;
use std::fmt::{Debug, Formatter};
use std::marker::PhantomData;
use std::ops::{Index, IndexMut};

//TODO make some macro for newtypes once that comes up
//  also change the debug print to include that newtype name
#[derive(Eq, PartialEq, Hash)]
pub struct Idx<T> {
    i: usize,
    ph: PhantomData<T>,
}

impl<T> Debug for Idx<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("<{}>", self.i))
    }
}

//Clone and Copy implemented manually because #[derive(Copy, Clone)] places bounds on T
impl<T> Clone for Idx<T> {
    fn clone(&self) -> Self {
        Self { i: self.i, ph: PhantomData }
    }
}

impl<T> Copy for Idx<T> {}

pub struct Arena<T> {
    //TODO for now this is implemented as a map, but this can be improved
    //  to just be a vec using generational indices
    map: HashMap<usize, T>,
    next_i: usize,
}

#[allow(dead_code)]
impl<T> Arena<T> {
    pub fn push(&mut self, value: T) -> Idx<T> {
        let i = self.next_i;
        self.next_i += 1;
        assert!(self.map.insert(i, value).is_none());
        Idx { i, ph: PhantomData }
    }

    pub fn pop(&mut self, index: Idx<T>) -> T {
        self.map.remove(&index.i)
            .unwrap_or_else(|| panic!("Value at {:?} not found", index.i))
    }
}

impl<T> Index<Idx<T>> for Arena<T> {
    type Output = T;
    fn index(&self, index: Idx<T>) -> &Self::Output {
        &self.map[&index.i]
    }
}

impl<T> IndexMut<Idx<T>> for Arena<T> {
    fn index_mut(&mut self, index: Idx<T>) -> &mut Self::Output {
        self.map.get_mut(&index.i)
            .unwrap_or_else(|| panic!("Value at {:?} not found", index.i))
    }
}

impl<T> Default for Arena<T> {
    fn default() -> Self {
        Self { map: Default::default(), next_i: 0 }
    }
}

impl<T: Debug> Debug for Arena<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.map.fmt(f)
    }
}

#[cfg(test)]
mod test {
    use crate::util::arena::Arena;

    struct MyIndex(usize);

    #[test]
    fn basic() {
        let mut arena: Arena<char> = Default::default();
        let ai = arena.push('a');
        let bi = arena.push('b');
        assert_eq!(arena[ai], 'a');
        assert_eq!(arena[bi], 'b');
    }

    #[test]
    fn pop() {
        let mut arena: Arena<char> = Default::default();
        let ai = arena.push('a');
        let bi = arena.push('b');
        arena.pop(ai);
        assert_eq!(arena[bi], 'b');
    }

    #[test]
    #[should_panic]
    fn pop_twice() {
        let mut arena: Arena<char> = Default::default();
        let ai = arena.push('a');
        let bi = arena.push('b');
        arena.pop(ai);
        arena.pop(ai);
    }
}
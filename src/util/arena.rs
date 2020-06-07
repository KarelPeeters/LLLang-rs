use std::collections::HashMap;
use std::fmt::{Debug, Formatter};
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;
use std::ops::{Index, IndexMut};

use bimap::BiHashMap;

#[derive(Eq)]
pub struct Idx<T> {
    i: usize,
    ph: PhantomData<T>,
}

impl<T> Idx<T> {
    // a fake index that will never be part of an actual arena
    pub fn sentinel() -> Idx<T> {
        Idx { i: usize::MAX, ph: PhantomData }
    }
}

impl<T> Debug for Idx<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("<{}>", self.i))
    }
}

//Traits implemented manually because #[derive(...)] places bounds on T
impl<T> Clone for Idx<T> {
    fn clone(&self) -> Self {
        Self { i: self.i, ph: PhantomData }
    }
}

impl<T> Copy for Idx<T> {}

impl<T> PartialEq for Idx<T> {
    fn eq(&self, other: &Self) -> bool {
        self.i == other.i
    }
}

impl<T> Hash for Idx<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.i.hash(state)
    }
}

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

pub struct ArenaSet<T: Eq + Hash> {
    //TODO this implementation could also be optimized similar to Arena
    map: BiHashMap<usize, T>,
    next_i: usize,
}

impl<T: Eq + Hash> ArenaSet<T> {
    pub fn push(&mut self, value: T) -> Idx<T> {
        if let Some(&i) = self.map.get_by_right(&value) {
            Idx { i, ph: PhantomData }
        } else {
            let i = self.next_i;
            self.next_i += 1;
            self.map.insert(i, value);
            Idx { i, ph: PhantomData }
        }
    }

    pub fn pop(&mut self, index: Idx<T>) -> T {
        self.map.remove_by_left(&index.i)
            .unwrap_or_else(|| panic!("Value at {:?} not found", index.i)).1
    }
}

impl<T: Eq + Hash> Index<Idx<T>> for ArenaSet<T> {
    type Output = T;
    fn index(&self, index: Idx<T>) -> &Self::Output {
        self.map.get_by_left(&index.i)
            .unwrap_or_else(|| panic!("Value at {:?} not found", index.i))
    }
}

impl<T: Eq + Hash> Default for ArenaSet<T> {
    fn default() -> Self {
        Self { map: Default::default(), next_i: 0 }
    }
}

impl<T: Debug + Eq + Hash> Debug for ArenaSet<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.map.fmt(f)
    }
}

#[cfg(test)]
mod test {
    use crate::util::arena::{Arena, ArenaSet};

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

    #[test]
    fn basic_set() {
        let mut arena: ArenaSet<char> = Default::default();
        let ai = arena.push('a');
        let bi = arena.push('b');
        assert_eq!(arena[ai], 'a');
        assert_eq!(arena[bi], 'b');
    }

    #[test]
    fn duplicate_set() {
        let mut arena: ArenaSet<char> = Default::default();
        let ai0 = arena.push('a');
        let ai1 = arena.push('a');
        assert_eq!(arena[ai0], 'a');
        assert_eq!(ai0, ai1)
    }

    #[test]
    fn pop_set() {
        let mut arena: Arena<char> = Default::default();
        let ai = arena.push('a');
        let bi = arena.push('b');
        arena.pop(ai);
        assert_eq!(arena[bi], 'b');
    }

    #[test]
    #[should_panic]
    fn pop_twice_set() {
        let mut arena: Arena<char> = Default::default();
        let ai = arena.push('a');
        let bi = arena.push('b');
        arena.pop(ai);
        arena.pop(ai);
    }
}
use std::fmt::{Debug, Formatter};
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;
use std::ops::{Index, IndexMut};

use indexmap::map::IndexMap;

#[derive(Eq)]
pub struct Idx<T> {
    i: usize,
    ph: PhantomData<T>,
}

impl<T> Idx<T> {
    fn new(i: usize) -> Self {
        Self { i, ph: PhantomData }
    }

    // a fake index that will never be part of an actual arena
    pub fn sentinel() -> Idx<T> {
        Self::new(usize::MAX)
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
        Self::new(self.i)
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
    map: IndexMap<usize, T>,
    next_i: usize,
}

#[allow(dead_code)]
impl<T> Arena<T> {
    pub fn push(&mut self, value: T) -> Idx<T> {
        let i = self.next_i;
        self.next_i += 1;
        assert!(self.map.insert(i, value).is_none());
        Idx::new(i)
    }

    pub fn pop(&mut self, index: Idx<T>) -> T {
        self.map.remove(&index.i)
            .unwrap_or_else(|| panic!("Value at {:?} not found", index.i))
    }

    pub fn iter(&self) -> impl Iterator<Item=(Idx<T>, &T)> {
        self.into_iter()
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

pub struct ArenaIterator<'s, T> {
    inner: indexmap::map::Iter<'s, usize, T>,
}

impl<'s, T> IntoIterator for &'s Arena<T> {
    type Item = (Idx<T>, &'s T);
    type IntoIter = ArenaIterator<'s, T>;

    fn into_iter(self) -> Self::IntoIter {
        ArenaIterator { inner: self.map.iter() }
    }
}

impl<'s, T: 's> Iterator for ArenaIterator<'s, T> {
    type Item = (Idx<T>, &'s T);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
            .map(|(&i, v)| (Idx::new(i), v))
    }
}

pub struct ArenaSet<T: Eq + Hash + Copy> {
    //TODO this implementation should also be optimized
    //TODO this copy bound could theoretically be removed
    map_fwd: IndexMap<usize, T>,
    map_back: IndexMap<T, usize>,
    next_i: usize,
}

impl<T: Eq + Hash + Copy> ArenaSet<T> {
    pub fn push(&mut self, value: T) -> Idx<T> {
        if let Some(&i) = self.map_back.get(&value) {
            Idx::new(i)
        } else {
            let i = self.next_i;
            self.next_i += 1;
            self.map_fwd.insert(i, value);
            self.map_back.insert(value, i);
            Idx::new(i)
        }
    }

    pub fn pop(&mut self, index: Idx<T>) -> T {
        let value = self.map_fwd.remove(&index.i)
            .unwrap_or_else(|| panic!("Value at {:?} not found", index.i));
        self.map_back.remove(&value);
        value
    }

    pub fn iter(&self) -> impl Iterator<Item=(Idx<T>, &T)> {
        self.into_iter()
    }
}

impl<T: Eq + Hash + Copy> Index<Idx<T>> for ArenaSet<T> {
    type Output = T;
    fn index(&self, index: Idx<T>) -> &Self::Output {
        self.map_fwd.get(&index.i)
            .unwrap_or_else(|| panic!("Value at {:?} not found", index.i))
    }
}

impl<T: Eq + Hash + Copy> Default for ArenaSet<T> {
    fn default() -> Self {
        Self {
            map_fwd: Default::default(),
            map_back: Default::default(),
            next_i: 0,
        }
    }
}

impl<T: Debug + Eq + Hash + Copy> Debug for ArenaSet<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.map_fwd.fmt(f)
    }
}

pub struct ArenaSetIterator<'s, T> {
    inner: indexmap::map::Iter<'s, usize, T>,
}

impl<'s, T: Eq + Hash + Copy> IntoIterator for &'s ArenaSet<T> {
    type Item = (Idx<T>, &'s T);
    type IntoIter = ArenaSetIterator<'s, T>;

    fn into_iter(self) -> Self::IntoIter {
        ArenaSetIterator { inner: self.map_fwd.iter() }
    }
}

impl<'s, T: 's> Iterator for ArenaSetIterator<'s, T> {
    type Item = (Idx<T>, &'s T);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
            .map(|(&i, v)| (Idx::new(i), v))
    }
}

#[cfg(test)]
mod test {
    use crate::util::arena::{Arena, ArenaSet, Idx};

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
        arena.push('b');
        arena.pop(ai);
        arena.pop(ai);
    }

    #[test]
    fn duplicate() {
        let mut arena: Arena<char> = Default::default();
        let ai0 = arena.push('a');
        let ai1 = arena.push('a');
        assert_eq!(arena[ai0], 'a');
        assert_eq!(arena[ai1], 'a');
        assert_ne!(ai0, ai1)
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
        let mut arena: ArenaSet<char> = Default::default();
        let ai = arena.push('a');
        let bi = arena.push('b');
        arena.pop(ai);
        assert_eq!(arena[bi], 'b');
    }

    #[test]
    #[should_panic]
    fn pop_twice_set() {
        let mut arena: ArenaSet<char> = Default::default();
        let ai = arena.push('a');
        arena.push('b');
        assert_eq!(arena.pop(ai), 'a');
        arena.pop(ai); //panics
    }

    #[test]
    fn iter() {
        let mut arena: Arena<char> = Default::default();
        let ai = arena.push('a');
        let bi = arena.push('b');

        let expected = vec![
            (ai, &'a'),
            (bi, &'b'),
        ];
        let mut actual: Vec<(Idx<char>, &char)> = arena.iter().collect();
        actual.sort_by_key(|x| x.0.i);

        assert_eq!(actual, expected);
    }

    #[test]
    fn iter_set() {
        let mut arena: ArenaSet<char> = Default::default();
        let ai = arena.push('a');
        let bi = arena.push('b');

        let expected = vec![
            (ai, &'a'),
            (bi, &'b'),
        ];
        let mut actual: Vec<(Idx<char>, &char)> = arena.iter().collect();
        actual.sort_by_key(|x| x.0.i);

        assert_eq!(actual, expected);
    }
}
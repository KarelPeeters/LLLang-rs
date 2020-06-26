use std::fmt::Formatter;
use std::fmt::Debug;
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;
use std::ops::{Index, IndexMut};

use indexmap::map::IndexMap;

pub trait IndexType: Sized + Debug {
    type T;
    fn idx(&self) -> Idx<Self::T>;
    fn new(idx: Idx<Self::T>) -> Self;

    fn sentinel() -> Self {
        Self::new(Idx::sentinel())
    }
}

pub struct Idx<T> {
    i: usize,
    ph: PhantomData<T>,
}

impl<T> IndexType for Idx<T> {
    type T = T;
    fn idx(&self) -> Idx<T> {
        *self
    }
    fn new(idx: Idx<T>) -> Self {
        idx
    }
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
        write!(f, "<{}>", self.i)
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

impl<T> Eq for Idx<T> {}

impl<T> Hash for Idx<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.i.hash(state)
    }
}

pub struct Arena<K: IndexType, T> {
    //TODO for now this is implemented as a map, but this can be improved
    //  to just be a vec using generational indices
    map: IndexMap<usize, T>,
    next_i: usize,
    ph: PhantomData<K>,
}

#[allow(dead_code)]
impl<K: IndexType, T> Arena<K, T> {
    pub fn push(&mut self, value: T) -> K {
        let i = self.next_i;
        self.next_i += 1;
        assert!(self.map.insert(i, value).is_none());
        K::new(Idx::new(i))
    }

    pub fn pop(&mut self, index: K) -> T {
        self.map.remove(&index.idx().i)
            .unwrap_or_else(|| panic!("Value {:?} not found", index))
    }

    pub fn len(&self) -> usize {
        self.map.len()
    }

    pub fn iter(&self) -> impl Iterator<Item=(K, &T)> {
        self.into_iter()
    }
}

impl<K: IndexType, T> Index<K> for Arena<K, T> {
    type Output = T;
    fn index(&self, index: K) -> &Self::Output {
        &self.map.get(&index.idx().i)
            .unwrap_or_else(|| panic!("Value {:?} not found", index))
    }
}

impl<K: IndexType, T> IndexMut<K> for Arena<K, T> {
    fn index_mut(&mut self, index: K) -> &mut Self::Output {
        self.map.get_mut(&index.idx().i)
            .unwrap_or_else(|| panic!("Value {:?} not found", index))
    }
}

impl<K: IndexType, T> Default for Arena<K, T> {
    fn default() -> Self {
        Self { map: Default::default(), next_i: 0, ph: PhantomData }
    }
}

impl<K: IndexType, T: Debug> Debug for Arena<K, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.map.fmt(f)
    }
}

pub struct ArenaIterator<'s, K, T> {
    inner: indexmap::map::Iter<'s, usize, T>,
    ph: PhantomData<K>,
}

impl<'s, K: IndexType, T> IntoIterator for &'s Arena<K, T> {
    type Item = (K, &'s T);
    type IntoIter = ArenaIterator<'s, K, T>;

    fn into_iter(self) -> Self::IntoIter {
        ArenaIterator { inner: self.map.iter(), ph: PhantomData }
    }
}

impl<'s, K: IndexType, T: 's> Iterator for ArenaIterator<'s, K, T> {
    type Item = (K, &'s T);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
            .map(|(&i, v)| (K::new(Idx::new(i)), v))
    }
}

pub struct ArenaSet<K: IndexType, T: Eq + Hash + Clone> {
    //TODO this implementation should also be optimized
    //TODO this clone bound should be removed
    map_fwd: IndexMap<usize, T>,
    map_back: IndexMap<T, usize>,
    next_i: usize,
    ph: PhantomData<K>,
}

impl<K: IndexType, T: Eq + Hash + Clone> ArenaSet<K, T> {
    pub fn push(&mut self, value: T) -> K {
        if let Some(&i) = self.map_back.get(&value) {
            K::new(Idx::new(i))
        } else {
            let i = self.next_i;
            self.next_i += 1;
            self.map_fwd.insert(i, value.clone());
            self.map_back.insert(value, i);
            K::new(Idx::new(i))
        }
    }

    pub fn pop(&mut self, index: Idx<T>) -> T {
        let value = self.map_fwd.remove(&index.i)
            .unwrap_or_else(|| panic!("Value {:?} not found", index));
        self.map_back.remove(&value);
        value
    }

    pub fn iter(&self) -> impl Iterator<Item=(K, &T)> {
        self.into_iter()
    }
}

impl<K: IndexType, T: Eq + Hash + Clone> Index<K> for ArenaSet<K, T> {
    type Output = T;
    fn index(&self, index: K) -> &Self::Output {
        self.map_fwd.get(&index.idx().i)
            .unwrap_or_else(|| panic!("Value {:?} not found", index))
    }
}

impl<K: IndexType, T: Eq + Hash + Clone> Default for ArenaSet<K, T> {
    fn default() -> Self {
        Self {
            map_fwd: Default::default(),
            map_back: Default::default(),
            next_i: 0,
            ph: PhantomData,
        }
    }
}

impl<K: IndexType, T: Debug + Eq + Hash + Clone> Debug for ArenaSet<K, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.map_fwd.fmt(f)
    }
}

pub struct ArenaSetIterator<'s, K, T> {
    inner: indexmap::map::Iter<'s, usize, T>,
    ph: PhantomData<K>,
}

impl<'s, K: IndexType, T: Eq + Hash + Clone> IntoIterator for &'s ArenaSet<K, T> {
    type Item = (K, &'s T);
    type IntoIter = ArenaSetIterator<'s, K, T>;

    fn into_iter(self) -> Self::IntoIter {
        ArenaSetIterator { inner: self.map_fwd.iter(), ph: PhantomData }
    }
}

impl<'s, K: IndexType, T: 's> Iterator for ArenaSetIterator<'s, K, T> {
    type Item = (K, &'s T);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
            .map(|(&i, v)| (K::new(Idx::new(i)), v))
    }
}

#[cfg(test)]
mod test {
    use crate::util::arena::{Arena, ArenaSet, Idx};

    struct MyIndex(usize);

    #[test]
    fn basic() {
        let mut arena: Arena<Idx<char>, char> = Default::default();
        let ai = arena.push('a');
        let bi = arena.push('b');
        assert_eq!(arena[ai], 'a');
        assert_eq!(arena[bi], 'b');
    }

    #[test]
    fn pop() {
        let mut arena: Arena<Idx<char>, char> = Default::default();
        let ai = arena.push('a');
        let bi = arena.push('b');
        arena.pop(ai);
        assert_eq!(arena[bi], 'b');
    }

    #[test]
    #[should_panic]
    fn pop_twice() {
        let mut arena: Arena<Idx<char>, char> = Default::default();
        let ai = arena.push('a');
        arena.push('b');
        arena.pop(ai);
        arena.pop(ai);
    }

    #[test]
    fn duplicate() {
        let mut arena: Arena<Idx<char>, char> = Default::default();
        let ai0 = arena.push('a');
        let ai1 = arena.push('a');
        assert_eq!(arena[ai0], 'a');
        assert_eq!(arena[ai1], 'a');
        assert_ne!(ai0, ai1)
    }

    #[test]
    fn basic_set() {
        let mut arena: ArenaSet<Idx<char>, char> = Default::default();
        let ai = arena.push('a');
        let bi = arena.push('b');
        assert_eq!(arena[ai], 'a');
        assert_eq!(arena[bi], 'b');
    }

    #[test]
    fn duplicate_set() {
        let mut arena: ArenaSet<Idx<char>, char> = Default::default();
        let ai0 = arena.push('a');
        let ai1 = arena.push('a');
        assert_eq!(arena[ai0], 'a');
        assert_eq!(ai0, ai1)
    }

    #[test]
    fn pop_set() {
        let mut arena: ArenaSet<Idx<char>, char> = Default::default();
        let ai = arena.push('a');
        let bi = arena.push('b');
        arena.pop(ai);
        assert_eq!(arena[bi], 'b');
    }

    #[test]
    #[should_panic]
    fn pop_twice_set() {
        let mut arena: ArenaSet<Idx<char>, char> = Default::default();
        let ai = arena.push('a');
        arena.push('b');
        assert_eq!(arena.pop(ai), 'a');
        arena.pop(ai); //panics
    }

    #[test]
    fn iter() {
        let mut arena: Arena<Idx<char>, char> = Default::default();
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
        let mut arena: ArenaSet<Idx<char>, char> = Default::default();
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
use crate::ast::{Binder, BindingList, Rc, Sort, Term};
use indexmap::{IndexMap, IndexSet};
use rug::Integer;
use std::{
    borrow::Borrow,
    fmt,
    hash::{Hash, Hasher},
    ops,
};

/// Returns `true` if the character is a valid symbol character in the SMT-LIB and Alethe formats.
pub fn is_symbol_character(ch: char) -> bool {
    match ch {
        ch if ch.is_ascii_alphanumeric() => true,
        '+' | '-' | '/' | '*' | '=' | '%' | '?' | '!' | '.' | '$' | '_' | '~' | '&' | '^' | '<'
        | '>' | '@' => true,

        // While `'` is not a valid symbol character according to the SMT-LIB and Alethe specs, it
        // is used by Carcara to differentiate variables renamed by capture-avoidance in
        // substitutions. To accommodate for that, we consider it a valid character when parsing.
        '\'' => true,
        _ => false,
    }
}

/// An iterator that removes duplicate elements from `iter`. This will yield the elements in
/// `iter` in order, skipping elements that have already been seen before.
pub struct Dedup<T, I> {
    seen: IndexSet<T>,
    iter: I,
}

impl<T, I> Iterator for Dedup<T, I>
where
    T: Clone + Hash + Eq,
    I: Iterator<Item = T>,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let got = self.iter.next()?;
            let is_new = self.seen.insert(got.clone());
            if is_new {
                return Some(got);
            }
        }
    }
}

pub trait DedupIterator<T> {
    /// Creates an iterator that skips duplicate elements.
    fn dedup(self) -> Dedup<T, Self>
    where
        Self: Sized;
}

impl<T, I: Iterator<Item = T>> DedupIterator<T> for I {
    fn dedup(self) -> Dedup<T, Self>
    where
        Self: Sized,
    {
        Dedup { seen: IndexSet::new(), iter: self }
    }
}

pub struct HashCache<T> {
    hash: u64,
    value: T,
}

impl<T: PartialEq> PartialEq for HashCache<T> {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}

impl<T: Eq> Eq for HashCache<T> {}

impl<T: Hash> Hash for HashCache<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u64(self.hash);
    }
}

impl<T: Eq + Hash> HashCache<T> {
    pub fn new(value: T) -> Self {
        let mut hasher = std::collections::hash_map::DefaultHasher::default();
        value.hash(&mut hasher);
        Self { hash: hasher.finish(), value }
    }

    pub fn unwrap(self) -> T {
        self.value
    }
}

impl<T> AsRef<T> for HashCache<T> {
    fn as_ref(&self) -> &T {
        &self.value
    }
}

#[derive(Debug)]
pub struct HashMapStack<K, V> {
    scopes: Vec<IndexMap<K, V>>,
    // Added in Clean: see `generation`. `numbered` counts the numbers given out, and `pushed_at`
    // holds, for each scope but the outermost, the generation before it was pushed.
    id: u64,
    generation: u64,
    numbered: u64,
    pushed_at: Vec<u64>,
    // Added in Clean: the entries of every scope but the outermost (see `inner_len`).
    inner: usize,
}

/// Added in Clean: the ids of `HashMapStack`s, each taken once in a process.
static STACK_IDS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

impl<K, V> HashMapStack<K, V> {
    pub fn new() -> Self {
        Self {
            scopes: vec![IndexMap::new()],
            id: STACK_IDS.fetch_add(1, std::sync::atomic::Ordering::Relaxed),
            generation: 0,
            numbered: 0,
            pushed_at: Vec::new(),
            inner: 0,
        }
    }

    /// Added in Clean: the stack's id, which no other stack in the process has, and a number for its
    /// contents. Inserting an entry or pushing a scope gives the stack a number it has never had;
    /// popping a scope gives it back the number it had before that scope was pushed, and it then
    /// holds what it held then, since every change in between was to the popped scope. So two
    /// reads that return the same generation read one stack with the same contents, and a cache of
    /// answers computed from the stack is valid whenever it is at the generation they were computed
    /// at, after a scope entered and left too (see `Parser::locally_bound_free_vars`).
    pub fn generation(&self) -> (u64, u64) {
        (self.id, self.generation)
    }

    /// Added in Clean: the generation of the stack's scopes up to `depth` (the outermost is depth
    /// 0): the stack's generation for its innermost scope, and for any other the generation the
    /// stack had when the scope inside it was pushed, which it keeps while that scope is on the
    /// stack (every change in between is to scopes inside it). Two reads that return the same
    /// generation for a depth read the same scopes up to that depth, and the same generations for
    /// every depth below it (see `Parser::locally_bound_free_vars`).
    pub fn generation_at(&self, depth: usize) -> (u64, u64) {
        match self.pushed_at.get(depth) {
            Some(&generation) => (self.id, generation),
            None => self.generation(),
        }
    }

    /// Added in Clean: how many entries the scope at `depth` holds.
    pub fn scope_len(&self, depth: usize) -> usize {
        self.scopes[depth].len()
    }

    /// Added in Clean: the keys of the scope at `depth`.
    pub fn scope_keys(&self, depth: usize) -> impl Iterator<Item = &K> {
        self.scopes[depth].keys()
    }

    /// Added in Clean: a number the stack has never had (see `generation`).
    fn renumber(&mut self) {
        self.numbered += 1;
        self.generation = self.numbered;
    }

    pub fn height(&self) -> usize {
        self.scopes.len()
    }

    /// Modified in Clean: only the comparator kept as a test oracle (`ast/polyeq_oracle.rs`) asks
    /// this; `Polyeq`'s De Bruijn map no longer holds `HashMapStack`s.
    #[cfg(test)]
    pub fn is_empty(&self) -> bool {
        self.scopes.iter().all(IndexMap::is_empty)
    }

    pub fn push_scope(&mut self) {
        self.scopes.push(IndexMap::new());
        self.pushed_at.push(self.generation);
        self.renumber();
    }

    /// Added in Clean: the keys of every scope but the outermost.
    pub fn inner_keys(&self) -> impl Iterator<Item = &K> {
        self.scopes[1..].iter().flat_map(IndexMap::keys)
    }

    /// Added in Clean: how many entries every scope but the outermost holds, kept as the scopes
    /// change.
    pub fn inner_len(&self) -> usize {
        self.inner
    }

    pub fn pop_scope(&mut self) {
        match self.scopes.len() {
            0 => unreachable!(),
            1 => panic!("trying to pop last scope in `HashMapStack`"),
            _ => {
                let popped = self.scopes.pop().unwrap();
                self.inner -= popped.len();
                self.generation = self.pushed_at.pop().unwrap();
            }
        }
    }
}

impl<K: Eq + Hash, V> HashMapStack<K, V> {
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        // Note: If there are a lot of scopes in the symbol table, this can be a big performance
        // bottleneck. As currently implemented, this function needs to hash the key once for every
        // scope. The ideal way of solving this would be to hash the key once, and reuse that hash
        // to access the entry in each scope. To do that, we could use the `HashMap::raw_entry`
        // method, but it is currently nightly-only. Another way to mitigate this issue is to use
        // the `HashCache<T>` struct to wrap the key values in the symbol table. This allows the key
        // to only be hashed once, and that value is stored and reused in the struct.
        self.scopes.iter().rev().find_map(|scope| scope.get(key))
    }

    pub fn get_with_depth<Q>(&self, key: &Q) -> Option<(usize, &V)>
    where
        K: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.scopes
            .iter()
            .enumerate()
            .rev()
            .find_map(|(depth, scope)| scope.get(key).map(|v| (depth, v)))
    }

    pub fn insert(&mut self, key: K, value: V) {
        let inner = self.scopes.len() > 1;
        let new = self.scopes.last_mut().unwrap().insert(key, value).is_none();
        if inner && new {
            self.inner += 1;
        }
        self.renumber();
    }

    /// Added in Clean: the entries of every scope, for the test oracle `ast/polyeq_oracle.rs`.
    #[cfg(test)]
    pub fn len(&self) -> usize {
        self.scopes.iter().map(IndexMap::len).sum()
    }
}

impl<K, V> Default for HashMapStack<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, Clone)]
pub struct MultiSet<T>(pub IndexMap<T, usize>);

impl<T> Default for MultiSet<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> MultiSet<T> {
    pub fn new() -> Self {
        MultiSet(IndexMap::new())
    }
}

pub enum MultiSetDifference<'a, T> {
    None,
    Missing(&'a T),
    Extra(&'a T),
}

impl<T: Hash + Eq> MultiSet<T> {
    pub fn get(&self, value: &T) -> usize {
        self.0.get(value).copied().unwrap_or_default()
    }

    pub fn get_mut(&mut self, value: T) -> &mut usize {
        self.0.entry(value).or_default()
    }

    pub fn insert(&mut self, value: T) -> usize {
        self.insert_n(value, 1)
    }

    pub fn insert_n(&mut self, value: T, n: usize) -> usize {
        if n == 0 {
            return self.get(&value);
        }
        let v = self.get_mut(value);
        *v += n;
        *v
    }

    pub fn remove(&mut self, value: T) -> usize {
        self.remove_n(value, 1)
    }

    pub fn remove_n(&mut self, value: T, n: usize) -> usize {
        if self.get(&value) <= n {
            self.0.swap_remove(&value);
            0
        } else {
            let v = self.get_mut(value);
            *v -= n;
            *v
        }
    }

    pub fn symmetric_difference<'a>(&'a self, other: &'a Self) -> MultiSetDifference<'a, T> {
        for (item, &count) in &self.0 {
            let other_count = other.get(item);
            if count > other_count {
                return MultiSetDifference::Extra(item);
            } else if count < other_count {
                return MultiSetDifference::Missing(item);
            }
        }

        for (item, &count) in &other.0 {
            let self_count = self.get(item);
            if self_count > count {
                return MultiSetDifference::Extra(item);
            } else if self_count < count {
                return MultiSetDifference::Missing(item);
            }
        }

        MultiSetDifference::None
    }
}

impl<T: Hash + Eq> PartialEq for MultiSet<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<T: Hash + Eq> FromIterator<T> for MultiSet<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut mset = MultiSet::new();
        for i in iter {
            mset.insert(i);
        }
        mset
    }
}

impl<T: Clone> MultiSet<T> {
    pub fn into_iter(self) -> impl Iterator<Item = T> {
        // I use a custom `into_iter` method instead of implementing `IntoIterator` because the
        // actual iterator type I use can't be named (because of the closure), which `IntoIterator`
        // requires.
        self.0
            .into_iter()
            .flat_map(|(item, count)| std::iter::repeat_n(item, count))
    }
}

/// A range type with a nice `Display` implementation, to be used in error messages.
#[derive(Debug)]
pub struct Range(Option<usize>, Option<usize>);

impl Range {
    pub fn contains(&self, n: usize) -> bool {
        self.0.as_ref().is_none_or(|bound| n >= *bound)
            && self.1.as_ref().is_none_or(|bound| n <= *bound)
    }
}

impl fmt::Display for Range {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Range(Some(a), Some(b)) if a == b => write!(f, "{}", a),
            Range(Some(a), Some(b)) => write!(f, "between {} and {}", a, b),
            Range(Some(a), None) => write!(f, "at least {}", a),
            Range(None, Some(b)) => write!(f, "up to {}", b),
            Range(None, None) => write!(f, "any number of"),
        }
    }
}

impl From<usize> for Range {
    fn from(n: usize) -> Self {
        Self(Some(n), Some(n))
    }
}

impl From<ops::Range<usize>> for Range {
    fn from(r: ops::Range<usize>) -> Self {
        Self(Some(r.start), Some(r.end - 1))
    }
}

impl From<ops::RangeFrom<usize>> for Range {
    fn from(r: ops::RangeFrom<usize>) -> Self {
        Self(Some(r.start), None)
    }
}

impl From<ops::RangeFull> for Range {
    fn from(_: ops::RangeFull) -> Self {
        Self(None, None)
    }
}

impl From<ops::RangeTo<usize>> for Range {
    fn from(r: ops::RangeTo<usize>) -> Self {
        Self(None, Some(r.end - 1))
    }
}

/// Provides a pretty displayable name for a type. For example, the type name for `Rc<Term>` is
/// "term".
pub trait TypeName {
    const NAME: &'static str;
}

impl TypeName for Rc<Term> {
    const NAME: &'static str = "term";
}

impl TypeName for Rc<Sort> {
    const NAME: &'static str = "sort";
}

impl TypeName for Binder {
    const NAME: &'static str = "binder";
}

impl<T> TypeName for BindingList<T> {
    const NAME: &'static str = "binding list";
}

impl TypeName for Integer {
    const NAME: &'static str = "integer";
}

/// Added in Clean.
#[cfg(test)]
mod tests {
    use super::HashMapStack;
    use rand::{rngs::StdRng, Rng, SeedableRng};
    use std::collections::HashMap;

    /// `HashMapStack::generation` names the stack's contents: over random pushes, pops and
    /// insertions (a key inserted again in its scope included), every generation read twice reads
    /// the same scopes, and each insertion or push gives a generation never read before. And
    /// `generation_at` names the scopes up to a depth: a generation read at a depth twice reads
    /// the same scopes up to that depth, and the same generations at every depth below; and
    /// `inner_len` counts the entries of every scope but the outermost.
    #[test]
    fn a_generation_names_the_stacks_contents() {
        type Scopes = Vec<Vec<(u8, u32)>>;
        // For each generation a depth was read at, the scopes up to it and the generations below.
        type Prefix = (Scopes, Vec<(u64, u64)>);
        let mut rng = StdRng::seed_from_u64(5);
        let mut stack: HashMapStack<u8, u32> = HashMapStack::new();
        let mut model: Scopes = vec![Vec::new()];
        let mut seen: HashMap<(u64, u64), Scopes> = HashMap::new();
        seen.insert(stack.generation(), model.clone());
        let mut seen_at: HashMap<(u64, u64), Prefix> = HashMap::new();
        for step in 0..20_000u32 {
            let fresh = match rng.gen_range(0..3) {
                0 => {
                    stack.push_scope();
                    model.push(Vec::new());
                    true
                }
                1 if model.len() > 1 => {
                    stack.pop_scope();
                    model.pop();
                    false
                }
                _ => {
                    let key = rng.gen_range(0..8);
                    stack.insert(key, step);
                    let scope = model.last_mut().unwrap();
                    scope.retain(|(k, _)| *k != key);
                    scope.push((key, step));
                    true
                }
            };
            for scope in &mut model {
                scope.sort_unstable();
            }
            let generation = stack.generation();
            match seen.get(&generation) {
                Some(contents) => {
                    assert!(
                        !fresh,
                        "step {step}: a change kept the generation {generation:?}"
                    );
                    assert_eq!(contents, &model, "step {step}: generation {generation:?}");
                }
                None => {
                    seen.insert(generation, model.clone());
                }
            }
            let below: Vec<(u64, u64)> = (0..model.len()).map(|d| stack.generation_at(d)).collect();
            assert_eq!(below.last(), Some(&generation));
            for depth in 0..model.len() {
                let prefix = (model[..=depth].to_vec(), below[..depth].to_vec());
                match seen_at.get(&below[depth]) {
                    Some(seen) => assert_eq!(seen, &prefix, "step {step}: depth {depth}"),
                    None => {
                        seen_at.insert(below[depth], prefix);
                    }
                }
                assert_eq!(stack.scope_len(depth), model[depth].len());
            }
            let inner: usize = model[1..].iter().map(Vec::len).sum();
            assert_eq!(stack.inner_len(), inner);
            for (depth, scope) in model.iter().enumerate() {
                for (key, value) in scope {
                    let found = stack.get_with_depth(key);
                    assert!(found.is_some_and(|(d, v)| d >= depth && (d > depth || v == value)));
                }
            }
        }
        assert_ne!(
            HashMapStack::<u8, u32>::new().generation().0,
            stack.generation().0
        );
    }
}

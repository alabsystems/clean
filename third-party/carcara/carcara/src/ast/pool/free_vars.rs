// Modified in Clean: typed array-lambda dialect and explicit lambda export refusal.
//! Added in Clean (not part of upstream Carcara): free-variable sets that share structure.
//!
//! Upstream's pool cached, for every term it was asked about, an `IndexSet` of the term's free
//! variables, built by copying the sets of its subterms. A chain of terms over distinct constants,
//! `e_j = (bvadd c_j e_(j-1))`, made those sets hold `n^2 / 2` entries in all: 10,000 links (an
//! 885 KB problem) took 1.75 GB. Here a set is a persistent big-endian Patricia trie (Okasaki and
//! Gill, "Fast Mergeable Integer Maps", 1998): a term's set is its subterms' sets merged, and the
//! merge copies only the paths where they differ, so the chain's sets share all but one path each.
//!
//! A variable's key is the hash of its name in the high 64 bits and the address of its term in the
//! low 64 bits, and the trie's leaf holds the term, which keeps the address from being reused while
//! the set exists. Two variables have the same key only if they are the same allocation, which is
//! the identity the pool's terms compare by (`ast::Rc`), so membership answers exactly what the
//! `IndexSet` of `Rc<Term>`s answered; and the variables of one name are the keys under one prefix.
//! Addresses differ from run to run, so the order in which a set lists its variables does too:
//! nothing may depend on it (see `first_free_var` for a deterministic choice among variables).
//! See third-party/carcara/DOWNSTREAM.md, "Free-variable sets share structure".
//!
//! A merge copies the paths where its operands differ, so two sets that share no structure cost
//! a merge linear in their size: two chains merged at every link, `r_j = (bvor p_j q_j)` with
//! `p_j = (bvadd c_j p_(j-1))` and `q_j = (bvmul d_j q_(j-1))`, cost quadratic time and memory,
//! and equal sets built apart (`q_j = (bvmul c_j q_(j-1))`) quadratic time. So each thread
//! remembers the merges of branches it computed, by their operands, while the operands and the
//! result live (`Merges`): `r_j`'s merge meets, off the paths `c_j` and `d_j` changed, the pairs of
//! subtrees `r_(j-1)`'s merge met, and takes their results, so each link costs a few paths. The
//! table remembers at most one merge for every `LIVE_NODES_PER_ENTRY` trie nodes that live on its
//! thread (`live_nodes`), and is emptied past that, so it stays a fraction of the tries it serves
//! whatever pairs of sets are merged.

use super::TermPool;
use crate::ast::{Rc, Term};
use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::hash::{BuildHasherDefault, Hash, Hasher};
use std::sync::{Arc, Weak};
use std::thread::LocalKey;

type Key = u128;

#[derive(Debug)]
enum Node<V> {
    Leaf(Key, V),
    /// The keys below share the bits above `bit`, which are `prefix`'s (the bits at and below
    /// `bit` are zero in `prefix`); `left` holds those whose bit `bit` is clear, `right` the
    /// others. Both are nonempty, and `len` counts the keys of both.
    Branch {
        prefix: Key,
        bit: u8,
        len: usize,
        left: Arc<Node<V>>,
        right: Arc<Node<V>>,
    },
}

/// Added in Clean: a node counts itself out of `live_nodes` when it is dropped.
impl<V> Drop for Node<V> {
    fn drop(&mut self) {
        let _ = LIVE_NODES.try_with(|live| live.set(live.get().saturating_sub(1)));
    }
}

// The trie nodes that live on this thread (see `live_nodes`).
thread_local! {
    static LIVE_NODES: Cell<usize> = const { Cell::new(0) };
}

/// The trie nodes that live on this thread: a node counts itself in when it is allocated
/// (`allocated`) and out when it is dropped, on the thread that drops it, where the count stops at
/// zero. Where a trie is dropped on the thread that made it (Clean's adapter parses and checks each
/// certificate on a thread of its own) the count is exact; a node dropped on another thread leaves
/// its own thread's count over and the other's under, which only bounds the table of merges
/// (`Merges`) more loosely on the first and more tightly on the second.
fn live_nodes() -> usize {
    LIVE_NODES.try_with(Cell::get).unwrap_or(0)
}

/// A persistent map from 128-bit keys to values, as a big-endian Patricia trie. Cloning it, and
/// every operation, leaves the original as it was; the result shares every subtree it does not
/// change. Each operation is at most 128 levels deep.
#[derive(Debug)]
pub struct Trie<V>(Option<Arc<Node<V>>>);

impl<V> Clone for Trie<V> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<V> Default for Trie<V> {
    fn default() -> Self {
        Self(None)
    }
}

fn mask(bit: u8) -> Key {
    1 << bit
}

/// `key` with the bits at and below `bit` cleared: the prefix `key` has above `bit`.
fn prefix_of(key: Key, bit: u8) -> Key {
    let m = mask(bit);
    key & !(m | (m - 1))
}

fn matches(key: Key, prefix: Key, bit: u8) -> bool {
    prefix_of(key, bit) == prefix
}

/// The highest bit in which two different keys differ.
fn branching_bit(a: Key, b: Key) -> u8 {
    debug_assert_ne!(a, b);
    (127 - (a ^ b).leading_zeros()) as u8
}

fn len<V>(node: &Node<V>) -> usize {
    match node {
        Node::Leaf(..) => 1,
        Node::Branch { len, .. } => *len,
    }
}

/// The key of a leaf, or the prefix of a branch: what a branch above it is built on.
fn key_of<V>(node: &Node<V>) -> Key {
    match node {
        Node::Leaf(key, _) => *key,
        Node::Branch { prefix, .. } => *prefix,
    }
}

/// The values a trie may hold. A type with a table of merges (`merges`) has its tries' merges of
/// branches remembered on each thread (see `Merges`); a type without computes each merge.
pub trait Value: Clone + 'static {
    fn merges() -> Option<&'static LocalKey<RefCell<Merges<Self>>>>;
}

/// The free-variable sets' values: variables.
impl Value for Rc<Term> {
    fn merges() -> Option<&'static LocalKey<RefCell<Merges<Self>>>> {
        thread_local! {
            static MERGES: RefCell<Merges<Rc<Term>>> = RefCell::new(Merges::default());
        }
        Some(&MERGES)
    }
}

/// The name sets of `bfun_elim` (`checker/rules/clausification.rs`), which live for one step and
/// bound their cost with fuel: each merge is computed.
impl Value for () {
    fn merges() -> Option<&'static LocalKey<RefCell<Merges<Self>>>> {
        None
    }
}

/// The merges of two branches a thread computed, each by the addresses of its operands (the lower
/// first) with the operands and the result, while they live.
///
/// Each entry holds its nodes weakly, so it keeps none of them alive, and an entry whose node died
/// is dropped by a later sweep (`remember`). A weak reference keeps its allocation's memory from
/// being freed (only its contents are dropped), so an address an entry holds is not reused while
/// the entry exists: an entry found by the addresses of two live nodes was made for those nodes.
/// A trie never changes, so the result of merging the same two nodes again is the result kept, and
/// what a merge returns does not depend on whether it was found here.
///
/// The table holds at most one entry for every `LIVE_NODES_PER_ENTRY` trie nodes that live on its
/// thread (`live_nodes`), or `SWEEP_MIN` entries if that is more: past that it is emptied, and the
/// merges it held are computed again where they recur. An entry lives as long as the tries it was
/// made from, which a pool caches, so without the bound sets merged in many pairs that recur little
/// made the table most of the memory: two chains over the same constants merged in a random pairing
/// with the superset first and folded (the review's `twinsup` shape) gave it nearly seven entries
/// for each live trie node at 20,000 links and more at 40,000, and merged in an unordered random
/// pairing (`twinperm`), where it saves no time, it took two thirds more memory than no table.
pub struct Merges<V> {
    entries: HashMap<(usize, usize), [Weak<Node<V>>; 3], BuildHasherDefault<AddressHasher>>,
    /// The entries at which the next sweep runs.
    sweep_at: usize,
}

impl<V> Default for Merges<V> {
    fn default() -> Self {
        Self {
            entries: HashMap::default(),
            sweep_at: SWEEP_MIN,
        }
    }
}

/// The hasher of `Merges`' keys, two addresses. No input chooses an address, so a multiplicative
/// mix, finished as `MurmurHash3`'s is (an address is a multiple of 16, and the table indexes by
/// the hash's low bits), spreads them well enough, at a fraction of `SipHash`'s cost.
#[derive(Default)]
pub struct AddressHasher(u64);

impl Hasher for AddressHasher {
    fn finish(&self) -> u64 {
        let mut h = self.0;
        h ^= h >> 33;
        h = h.wrapping_mul(0xff51_afd7_ed55_8ccd);
        h ^= h >> 33;
        h
    }

    fn write(&mut self, bytes: &[u8]) {
        for chunk in bytes.chunks(8) {
            let mut word = [0u8; 8];
            word[..chunk.len()].copy_from_slice(chunk);
            self.write_u64(u64::from_le_bytes(word));
        }
    }

    fn write_u64(&mut self, n: u64) {
        self.0 = (self.0 ^ n)
            .wrapping_mul(0x9e37_79b9_7f4a_7c15)
            .rotate_left(29);
    }

    fn write_usize(&mut self, n: usize) {
        self.write_u64(n as u64);
    }
}

/// The fewest entries at which `Merges` is swept.
const SWEEP_MIN: usize = 1 << 12;

/// The trie nodes that live on a thread (`live_nodes`) for each entry its `Merges` may hold. An
/// entry takes about as much memory as a node, so the table takes about an eighth of what its tries
/// take. Two chains merged at every link reuse mostly the entries of the last few links, so they pay
/// little for the bound: a merge the emptied table no longer holds is computed once more, at a cost
/// linear in its operands, and the table is emptied a few times as the tries grow. Read by one
/// `qnt_rm_unused` step at 40,000 links, they kept without a bound 0.37 entries a live node over
/// distinct constants and 0.71 over the same ones, and took the same time at one entry for every
/// 8, 16 or 32 nodes as with none. A larger divisor saves more memory where entries serve little
/// and costs more time where they serve much (third-party/carcara/DOWNSTREAM.md, "Free-variable sets
/// share structure", the table's bound).
const LIVE_NODES_PER_ENTRY: usize = 8;

/// The fewest keys two branches hold together for their merge to be remembered. A merge that is
/// not remembered is computed each time, at a cost linear in its operands, so two chains merged at
/// every link cost about this many keys' worth of merging per link on each path a link changed.
/// And each entry costs the merges that no remembered result serves (sets merged once each): two
/// chains over distinct constants whose links are merged in a random pairing took, before the
/// table had a bound (`LIVE_NODES_PER_ENTRY`), half again the time and a fifth more memory than
/// with no table when every merge of 8 keys or more was remembered, and at 32 about a tenth more
/// time and no more memory; over the same constants, at 32, two thirds more memory than with no
/// table, which the bound brings to a tenth (third-party/carcara/DOWNSTREAM.md, "Free-variable
/// sets share structure").
const REMEMBERED_MERGE_MIN: usize = 32;

impl<V> Merges<V> {
    fn key(a: &Arc<Node<V>>, b: &Arc<Node<V>>) -> (usize, usize) {
        let (a, b) = (Arc::as_ptr(a) as usize, Arc::as_ptr(b) as usize);
        (a.min(b), a.max(b))
    }

    /// The remembered merge of `a` and `b`, if its result lives.
    fn find(&self, a: &Arc<Node<V>>, b: &Arc<Node<V>>) -> Option<Arc<Node<V>>> {
        self.entries.get(&Self::key(a, b))?[2].upgrade()
    }

    /// Remembers `result` as the merge of `a` and `b`. Once the table holds twice the entries the
    /// last sweep left (and at least `SWEEP_MIN`), it drops those whose nodes died: it then holds at
    /// most about twice the entries whose nodes live, at a cost spread over the insertions between
    /// two sweeps. Once it holds more than its bound (`Merges`), it is emptied, at a cost spread
    /// over the insertions since it was last emptied.
    fn remember(&mut self, a: &Arc<Node<V>>, b: &Arc<Node<V>>, result: &Arc<Node<V>>) {
        let nodes = [a, b, result].map(Arc::downgrade);
        self.entries.insert(Self::key(a, b), nodes);
        let bound = (live_nodes() / LIVE_NODES_PER_ENTRY).max(SWEEP_MIN);
        if self.entries.len() > bound {
            // A new table, so that the old one's memory goes too.
            *self = Self::default();
            return;
        }
        if self.entries.len() >= self.sweep_at {
            self.entries
                .retain(|_, nodes| nodes.iter().all(|node| node.strong_count() > 0));
            self.sweep_at = (2 * self.entries.len()).max(SWEEP_MIN);
        }
    }
}

/// Runs `f` on this thread's `Merges` for `V`, if `V` has them and they can be borrowed (not while
/// the thread's locals are being destroyed); otherwise `None`.
fn with_merges<V: Value, R>(f: impl FnOnce(&mut Merges<V>) -> R) -> Option<R> {
    let merges = V::merges()?;
    let mut f = Some(f);
    let result = merges.try_with(|cell| {
        let mut merges = cell.try_borrow_mut().ok()?;
        f.take().map(|f| f(&mut merges))
    });
    result.ok().flatten()
}

// The merges this thread found remembered, for the tests that check the table serves them.
#[cfg(test)]
thread_local! {
    static FOUND: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// How many merges this thread has found remembered so far.
#[cfg(test)]
fn merges_found() -> usize {
    FOUND.with(std::cell::Cell::get)
}

/// Every node of every trie is allocated here, and counts itself in `live_nodes`.
fn allocated<V>(node: Node<V>) -> Arc<Node<V>> {
    #[cfg(test)]
    ALLOCATED.with(|count| count.set(count.get() + 1));
    let _ = LIVE_NODES.try_with(|live| live.set(live.get() + 1));
    Arc::new(node)
}

// The nodes this thread has allocated, for the tests that bound what a computation allocates as it
// goes (they then fail at the first link over the bound, rather than run out of memory).
#[cfg(test)]
thread_local! {
    static ALLOCATED: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// How many trie nodes this thread has allocated so far.
#[cfg(test)]
pub fn nodes_allocated() -> usize {
    ALLOCATED.with(std::cell::Cell::get)
}

fn branch<V: Value>(prefix: Key, bit: u8, left: Arc<Node<V>>, right: Arc<Node<V>>) -> Arc<Node<V>> {
    allocated(Node::Branch {
        prefix,
        bit,
        len: len(&left) + len(&right),
        left,
        right,
    })
}

/// What a merge or an insertion may still spend: `VISIT` for each node it visits and `ALLOCATION`
/// for each node it allocates. An operation that would spend more than is left stops, returns
/// `None`, and leaves its operands as they were. The unmetered operations start with `Fuel::MAX`,
/// more than any operation can spend.
pub type Fuel = u64;

const VISIT: Fuel = 1;

pub const ALLOCATION: Fuel = 16;

fn spend(fuel: &mut Fuel, units: Fuel) -> Option<()> {
    *fuel = fuel.checked_sub(units)?;
    Some(())
}

/// A branch over `left` and `right`, either of which may be empty.
fn branch_or_child<V: Value>(
    prefix: Key,
    bit: u8,
    left: Option<Arc<Node<V>>>,
    right: Option<Arc<Node<V>>>,
) -> Option<Arc<Node<V>>> {
    match (left, right) {
        (None, other) | (other, None) => other,
        (Some(left), Some(right)) => Some(branch(prefix, bit, left, right)),
    }
}

/// The trie holding both `a` and `b`, whose keys differ above both of their branching bits.
fn join<V: Value>(a: Arc<Node<V>>, b: Arc<Node<V>>, fuel: &mut Fuel) -> Option<Arc<Node<V>>> {
    spend(fuel, ALLOCATION)?;
    let (ka, kb) = (key_of(&a), key_of(&b));
    let bit = branching_bit(ka, kb);
    Some(if ka & mask(bit) == 0 {
        branch(prefix_of(ka, bit), bit, a, b)
    } else {
        branch(prefix_of(ka, bit), bit, b, a)
    })
}

/// `node` with the key of `leaf`, a leaf, which is shared rather than copied.
fn insert<V: Value>(
    node: &Arc<Node<V>>,
    leaf: &Arc<Node<V>>,
    fuel: &mut Fuel,
) -> Option<Arc<Node<V>>> {
    spend(fuel, VISIT)?;
    let key = key_of(leaf);
    match node.as_ref() {
        // A key is a variable's identity, so a key already present keeps its value.
        Node::Leaf(k, _) if *k == key => Some(node.clone()),
        Node::Leaf(..) => join(leaf.clone(), node.clone(), fuel),
        Node::Branch { prefix, bit, left, right, .. } => {
            if !matches(key, *prefix, *bit) {
                return join(leaf.clone(), node.clone(), fuel);
            }
            let (left, right) = if key & mask(*bit) == 0 {
                let new = insert(left, leaf, fuel)?;
                if Arc::ptr_eq(&new, left) {
                    return Some(node.clone());
                }
                (new, right.clone())
            } else {
                let new = insert(right, leaf, fuel)?;
                if Arc::ptr_eq(&new, right) {
                    return Some(node.clone());
                }
                (left.clone(), new)
            };
            spend(fuel, ALLOCATION)?;
            Some(branch(*prefix, *bit, left, right))
        }
    }
}

fn remove<V: Value>(node: &Arc<Node<V>>, key: Key) -> Option<Arc<Node<V>>> {
    match node.as_ref() {
        Node::Leaf(k, _) if *k == key => None,
        Node::Leaf(..) => Some(node.clone()),
        Node::Branch { prefix, bit, left, right, .. } => {
            if !matches(key, *prefix, *bit) {
                return Some(node.clone());
            }
            if key & mask(*bit) == 0 {
                match remove(left, key) {
                    Some(new) if Arc::ptr_eq(&new, left) => Some(node.clone()),
                    new => branch_or_child(*prefix, *bit, new, Some(right.clone())),
                }
            } else {
                match remove(right, key) {
                    Some(new) if Arc::ptr_eq(&new, right) => Some(node.clone()),
                    new => branch_or_child(*prefix, *bit, Some(left.clone()), new),
                }
            }
        }
    }
}

/// A branch with the children `left` and `right`, reusing `a` or `b` when they are its children.
fn rebuilt<V: Value>(
    prefix: Key,
    bit: u8,
    left: Arc<Node<V>>,
    right: Arc<Node<V>>,
    candidates: [&Arc<Node<V>>; 2],
    fuel: &mut Fuel,
) -> Option<Arc<Node<V>>> {
    for candidate in candidates {
        if let Node::Branch { left: l, right: r, .. } = candidate.as_ref() {
            if Arc::ptr_eq(l, &left) && Arc::ptr_eq(r, &right) {
                return Some(candidate.clone());
            }
        }
    }
    spend(fuel, ALLOCATION)?;
    Some(branch(prefix, bit, left, right))
}

fn union<V: Value>(a: &Arc<Node<V>>, b: &Arc<Node<V>>, fuel: &mut Fuel) -> Option<Arc<Node<V>>> {
    if Arc::ptr_eq(a, b) {
        return Some(a.clone());
    }
    spend(fuel, VISIT)?;
    // Added in Clean: a merge of two branches is looked up among those this thread remembers, and
    // remembered once computed (see `Merges`). A merge the fuel stopped is not.
    let remembered = matches!(
        (a.as_ref(), b.as_ref()),
        (Node::Branch { .. }, Node::Branch { .. })
    ) && len(a) + len(b) >= REMEMBERED_MERGE_MIN;
    if remembered {
        if let Some(result) = with_merges(|merges| merges.find(a, b)).flatten() {
            #[cfg(test)]
            FOUND.with(|found| found.set(found.get() + 1));
            return Some(result);
        }
    }
    let result = merged(a, b, fuel)?;
    if remembered {
        with_merges(|merges| merges.remember(a, b, &result));
    }
    Some(result)
}

/// `union` of two different nodes, computed.
fn merged<V: Value>(a: &Arc<Node<V>>, b: &Arc<Node<V>>, fuel: &mut Fuel) -> Option<Arc<Node<V>>> {
    match (a.as_ref(), b.as_ref()) {
        (Node::Leaf(..), _) => insert(b, a, fuel),
        (_, Node::Leaf(..)) => insert(a, b, fuel),
        (
            Node::Branch {
                prefix: p,
                bit: m,
                left: a0,
                right: a1,
                ..
            },
            Node::Branch {
                prefix: q,
                bit: n,
                left: b0,
                right: b1,
                ..
            },
        ) => {
            if m == n && p == q {
                let left = union(a0, b0, fuel)?;
                let right = union(a1, b1, fuel)?;
                rebuilt(*p, *m, left, right, [a, b], fuel)
            } else if m > n && matches(*q, *p, *m) {
                // `a` branches higher, and `b`'s keys fall into one of its halves.
                if q & mask(*m) == 0 {
                    rebuilt(*p, *m, union(a0, b, fuel)?, a1.clone(), [a, a], fuel)
                } else {
                    rebuilt(*p, *m, a0.clone(), union(a1, b, fuel)?, [a, a], fuel)
                }
            } else if n > m && matches(*p, *q, *n) {
                if p & mask(*n) == 0 {
                    rebuilt(*q, *n, union(a, b0, fuel)?, b1.clone(), [b, b], fuel)
                } else {
                    rebuilt(*q, *n, b0.clone(), union(a, b1, fuel)?, [b, b], fuel)
                }
            } else {
                join(a.clone(), b.clone(), fuel)
            }
        }
    }
}

fn get<V>(mut node: &Arc<Node<V>>, key: Key) -> Option<&V> {
    loop {
        match node.as_ref() {
            Node::Leaf(k, value) => return (*k == key).then_some(value),
            Node::Branch { prefix, bit, left, right, .. } => {
                if !matches(key, *prefix, *bit) {
                    return None;
                }
                node = if key & mask(*bit) == 0 { left } else { right };
            }
        }
    }
}

fn intersects<V>(a: &Arc<Node<V>>, b: &Arc<Node<V>>) -> bool {
    if Arc::ptr_eq(a, b) {
        return true;
    }
    match (a.as_ref(), b.as_ref()) {
        (Node::Leaf(key, _), _) => get(b, *key).is_some(),
        (_, Node::Leaf(key, _)) => get(a, *key).is_some(),
        (
            Node::Branch {
                prefix: p,
                bit: m,
                left: a0,
                right: a1,
                ..
            },
            Node::Branch {
                prefix: q,
                bit: n,
                left: b0,
                right: b1,
                ..
            },
        ) => {
            if m == n && p == q {
                intersects(a0, b0) || intersects(a1, b1)
            } else if m > n && matches(*q, *p, *m) {
                intersects(if q & mask(*m) == 0 { a0 } else { a1 }, b)
            } else if n > m && matches(*p, *q, *n) {
                intersects(a, if p & mask(*n) == 0 { b0 } else { b1 })
            } else {
                false
            }
        }
    }
}

/// The subtree holding exactly the keys whose high 64 bits are `high`, if any.
fn high_range<V>(mut node: &Arc<Node<V>>, high: u64) -> Option<&Arc<Node<V>>> {
    let key = (high as Key) << 64;
    loop {
        match node.as_ref() {
            Node::Leaf(k, _) => return ((*k >> 64) as u64 == high).then_some(node),
            Node::Branch { prefix, bit, left, right, .. } => {
                if *bit < 64 {
                    // Every key below shares its high 64 bits with `prefix`.
                    return ((*prefix >> 64) as u64 == high).then_some(node);
                }
                if !matches(key, *prefix, *bit) {
                    return None;
                }
                node = if key & mask(*bit) == 0 { left } else { right };
            }
        }
    }
}

/// The values of a subtree, in the order of their keys.
pub struct Values<'a, V> {
    stack: Vec<&'a Arc<Node<V>>>,
}

impl<'a, V> Iterator for Values<'a, V> {
    type Item = &'a V;

    fn next(&mut self) -> Option<&'a V> {
        loop {
            match self.stack.pop()?.as_ref() {
                Node::Leaf(_, value) => return Some(value),
                Node::Branch { left, right, .. } => {
                    self.stack.push(right);
                    self.stack.push(left);
                }
            }
        }
    }
}

impl<V: Value> Trie<V> {
    pub(crate) fn singleton(key: Key, value: V) -> Self {
        Self(Some(allocated(Node::Leaf(key, value))))
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.0.is_none()
    }

    pub(crate) fn len(&self) -> usize {
        self.0.as_deref().map_or(0, len)
    }

    pub(crate) fn get(&self, key: Key) -> Option<&V> {
        self.0.as_ref().and_then(|node| get(node, key))
    }

    pub(crate) fn insert(&self, key: Key, value: V) -> Self {
        let mut fuel = Fuel::MAX;
        let inserted = self.insert_within(key, value, &mut fuel);
        inserted.unwrap_or_else(|| unreachable!("an insertion spends less than `Fuel::MAX`"))
    }

    /// `insert`, spending at most `fuel` (see `Fuel`); `None` where it would spend more.
    pub(crate) fn insert_within(&self, key: Key, value: V, fuel: &mut Fuel) -> Option<Self> {
        match &self.0 {
            None => {
                spend(fuel, ALLOCATION)?;
                Some(Self(Some(allocated(Node::Leaf(key, value)))))
            }
            Some(node) => {
                spend(fuel, ALLOCATION)?;
                let leaf = allocated(Node::Leaf(key, value));
                insert(node, &leaf, fuel).map(|node| Self(Some(node)))
            }
        }
    }

    pub(crate) fn remove(&self, key: Key) -> Self {
        Self(self.0.as_ref().and_then(|node| remove(node, key)))
    }

    pub(crate) fn union(&self, other: &Self) -> Self {
        let mut fuel = Fuel::MAX;
        let merged = self.union_within(other, &mut fuel);
        merged.unwrap_or_else(|| unreachable!("a merge spends less than `Fuel::MAX`"))
    }

    /// `union`, spending at most `fuel` (see `Fuel`); `None` where it would spend more.
    pub(crate) fn union_within(&self, other: &Self, fuel: &mut Fuel) -> Option<Self> {
        match (&self.0, &other.0) {
            (None, _) => Some(other.clone()),
            (_, None) => Some(self.clone()),
            (Some(a), Some(b)) => union(a, b, fuel).map(|node| Self(Some(node))),
        }
    }

    pub(crate) fn intersects(&self, other: &Self) -> bool {
        match (&self.0, &other.0) {
            (Some(a), Some(b)) => intersects(a, b),
            _ => false,
        }
    }

    pub(crate) fn values(&self) -> Values<'_, V> {
        Values { stack: self.0.iter().collect() }
    }

    /// The values of the keys whose high 64 bits are `high`.
    pub(crate) fn values_in(&self, high: u64) -> Values<'_, V> {
        let root = self.0.as_ref().and_then(|node| high_range(node, high));
        Values { stack: root.into_iter().collect() }
    }

    /// Whether `self` and `other` are the same allocation (or both empty).
    #[cfg(test)]
    pub(crate) fn ptr_eq(&self, other: &Self) -> bool {
        match (&self.0, &other.0) {
            (None, None) => true,
            (Some(a), Some(b)) => Arc::ptr_eq(a, b),
            _ => false,
        }
    }

    /// The nodes of the trie, leaves and branches, counted once per allocation.
    #[cfg(test)]
    pub(crate) fn count_nodes(tries: &[&Self]) -> usize {
        let mut seen = std::collections::HashSet::new();
        let mut stack: Vec<&Arc<Node<V>>> = tries.iter().filter_map(|t| t.0.as_ref()).collect();
        while let Some(node) = stack.pop() {
            if !seen.insert(Arc::as_ptr(node)) {
                continue;
            }
            if let Node::Branch { left, right, .. } = node.as_ref() {
                stack.push(left);
                stack.push(right);
            }
        }
        seen.len()
    }
}

/// The hash of a name: the high 64 bits of the keys of the variables of that name.
pub fn name_hash(name: &str) -> u64 {
    // `DefaultHasher::new` is SipHash with fixed keys: the same name hashes the same in every
    // pool, so the sets of different pools can be merged.
    let mut hasher = std::hash::DefaultHasher::new();
    name.hash(&mut hasher);
    hasher.finish()
}

fn var_key(name: &str, var: &Rc<Term>) -> Key {
    ((name_hash(name) as Key) << 64) | (Rc::as_ptr(var) as usize as Key)
}

/// The free variables of a term (see the module's documentation): a set of variables, compared by
/// allocation as the pool's terms are. Cloning it is cheap.
#[derive(Debug, Clone, Default)]
pub struct FreeVars(Trie<Rc<Term>>);

impl FreeVars {
    /// The set holding only `var`, which must be a variable.
    pub(crate) fn singleton(var: &Rc<Term>) -> Self {
        let name = var
            .as_var()
            .expect("invariant: a free variable is a variable");
        Self(Trie::singleton(var_key(name, var), var.clone()))
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// The number of variables in the set.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Whether the set holds `var` (this allocation of it): a term that is not a variable is in no
    /// set.
    pub fn contains(&self, var: &Rc<Term>) -> bool {
        match var.as_var() {
            Some(name) => self
                .0
                .get(var_key(name, var))
                .is_some_and(|held| held == var),
            None => false,
        }
    }

    /// Whether the set holds a variable named `name`, of any sort.
    pub fn contains_name(&self, name: &str) -> bool {
        self.named(name).next().is_some()
    }

    /// The variables of the set named `name`, in no particular order.
    pub fn named<'a>(&'a self, name: &'a str) -> impl Iterator<Item = &'a Rc<Term>> + 'a {
        self.0
            .values_in(name_hash(name))
            .filter(move |var| var.as_var() == Some(name))
    }

    /// The variables of the set, in an order that differs from run to run: use it only where the
    /// order cannot be observed.
    pub fn iter(&self) -> impl Iterator<Item = &Rc<Term>> {
        self.0.values()
    }

    pub fn union(&self, other: &Self) -> Self {
        Self(self.0.union(&other.0))
    }

    /// Whether the two sets have a variable in common.
    pub fn intersects(&self, other: &Self) -> bool {
        self.0.intersects(&other.0)
    }

    /// The set without `var` (which need not be in it).
    pub fn without(&self, var: &Rc<Term>) -> Self {
        match var.as_var() {
            Some(name) => Self(self.0.remove(var_key(name, var))),
            None => self.clone(),
        }
    }

    /// The variables of the set satisfying `keep` (which sees every variable of the set).
    pub fn filter(&self, mut keep: impl FnMut(&Rc<Term>) -> bool) -> Self {
        let mut result = Trie::default();
        for var in self.iter() {
            if keep(var) {
                let name = var
                    .as_var()
                    .expect("invariant: a free variable is a variable");
                result = result.insert(var_key(name, var), var.clone());
            }
        }
        Self(result)
    }

    #[cfg(test)]
    pub(crate) fn trie(&self) -> &Trie<Rc<Term>> {
        &self.0
    }
}

/// The variables of `candidates` that a term's subterm mentions free, reached in a walk of the term
/// that reads, as upstream's sets listed their variables, a function before its arguments, the
/// arguments in order, a `let`'s body before its values, and a `match`'s scrutinee before its
/// cases; and of those, the first the walk reaches.
///
/// Upstream's checks that refuse a step because some variable of a set occurs free in a term named,
/// in their message, the first such variable in the order of the term's cached `IndexSet`. That
/// order was the order of first occurrence in this walk, except where removing a binder's variable
/// (`swap_remove`) moved the set's last variable into its place. The order of a `FreeVars` is not
/// deterministic, so those messages name this function's choice instead: when one variable of
/// `candidates` occurs free in `term` it is that one, as upstream's was, and otherwise the first
/// the walk reaches. Only messages depend on the choice, never a verdict.
///
/// The walk descends one path, into the first child whose free variables meet the candidates (with
/// those a binder on the way binds removed), so it visits at most the children of the terms on one
/// path. It reads the sets of subterms, which `pool.free_vars(term)` has computed and cached. It
/// looks each candidate up in the term's set, and never lists that set.
pub fn first_free_var(
    pool: &mut dyn TermPool,
    term: &Rc<Term>,
    candidates: &FreeVars,
) -> Option<Rc<Term>> {
    let free = pool.free_vars(term);
    let mut candidates = candidates.filter(|var| free.contains(var));
    match candidates.len() {
        0 => return None,
        1 => return candidates.iter().next().cloned(),
        _ => {}
    }
    let mut term = term.clone();
    loop {
        // Invariant: `candidates` meets the free variables of `term`.
        let next = match term.as_ref() {
            Term::Var(..) => return Some(term),
            Term::Const(_) => unreachable!("a constant has no free variable"),
            Term::App(func, args) => {
                let children = std::iter::once(func).chain(args.iter());
                first_meeting(pool, children, &candidates)
            }
            Term::Op(_, args) | Term::ParamOp { args, .. } | Term::AsOp(_, _, args) => {
                first_meeting(pool, args.iter(), &candidates)
            }
            Term::Binder(_, bindings, inner) => {
                for var in bindings {
                    let var = pool.add(var.clone().into());
                    candidates = candidates.without(&var);
                }
                Some(inner.clone())
            }
            Term::Let(bindings, inner) => {
                let mut in_body = candidates.clone();
                for (name, value) in bindings {
                    let sort = pool.sort(value);
                    let var = pool.add(Term::new_var(name.clone(), sort));
                    in_body = in_body.without(&var);
                }
                if pool.free_vars(inner).intersects(&in_body) {
                    candidates = in_body;
                    Some(inner.clone())
                } else {
                    first_meeting(pool, bindings.iter().map(|(_, value)| value), &candidates)
                }
            }
            Term::Match(scrutinee, cases) => {
                if pool.free_vars(scrutinee).intersects(&candidates) {
                    Some(scrutinee.clone())
                } else {
                    let mut found = None;
                    for case in cases {
                        let mut in_case = candidates.clone();
                        for var in case.bindings() {
                            let var = pool.add(var.clone().into());
                            in_case = in_case.without(&var);
                        }
                        if pool.free_vars(&case.body).intersects(&in_case) {
                            candidates = in_case;
                            found = Some(case.body.clone());
                            break;
                        }
                    }
                    found
                }
            }
        };
        term = next.expect("invariant: some child holds a candidate its parent holds free");
    }
}

fn first_meeting<'a>(
    pool: &mut dyn TermPool,
    children: impl Iterator<Item = &'a Rc<Term>>,
    candidates: &FreeVars,
) -> Option<Rc<Term>> {
    for child in children {
        if pool.free_vars(child).intersects(candidates) {
            return Some(child.clone());
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{
        pool::{advanced::ContextPool, advanced::LocalPool, PrimitivePool},
        Binder, BindingList, MatchCase, MatchPattern, Operator, Sort, SortedVar,
    };
    use indexmap::{IndexMap, IndexSet};
    use rand::{rngs::StdRng, Rng, SeedableRng};
    use std::collections::{BTreeMap, HashSet};

    /// Upstream's `free_vars_with_priorities`, kept to hold the pool's sets to it (with Clean's
    /// fix 28: a `let`'s values are read). Its sets are `IndexSet`s, in upstream's order.
    fn upstream(
        pool: &mut dyn TermPool,
        term: &Rc<Term>,
        cache: &mut IndexMap<Rc<Term>, IndexSet<Rc<Term>>>,
    ) -> IndexSet<Rc<Term>> {
        if let Some(set) = cache.get(term) {
            return set.clone();
        }
        let set = match term.as_ref() {
            Term::App(f, args) => {
                let mut set = upstream(pool, f, cache);
                for a in args {
                    set.extend(upstream(pool, a, cache));
                }
                set
            }
            Term::Op(_, args) | Term::ParamOp { args, .. } | Term::AsOp(_, _, args) => {
                let mut set = IndexSet::new();
                for a in args {
                    set.extend(upstream(pool, a, cache));
                }
                set
            }
            Term::Binder(_, bindings, inner) => {
                let mut vars = upstream(pool, inner, cache);
                for bound_var in bindings {
                    let term = pool.add(bound_var.clone().into());
                    vars.swap_remove(&term);
                }
                vars
            }
            Term::Let(bindings, inner) => {
                let mut vars = upstream(pool, inner, cache);
                for (var, value) in bindings {
                    let sort = pool.sort(value);
                    let term = pool.add((var.clone(), sort).into());
                    vars.swap_remove(&term);
                }
                for (_, value) in bindings {
                    vars.extend(upstream(pool, value, cache));
                }
                vars
            }
            Term::Match(term, cases) => {
                let mut vars = upstream(pool, term, cache);
                for case in cases {
                    let mut res_vars = upstream(pool, &case.body, cache);
                    for bound_var in case.bindings() {
                        let term = pool.add(bound_var.clone().into());
                        res_vars.swap_remove(&term);
                    }
                    vars.extend(res_vars);
                }
                vars
            }
            Term::Var(..) => {
                let mut set = IndexSet::with_capacity(1);
                set.insert(term.clone());
                set
            }
            Term::Const(_) => IndexSet::new(),
        };
        cache.insert(term.clone(), set.clone());
        set
    }

    /// The first variable of `candidates` free in `term` in the walk `first_free_var` documents,
    /// read off the tree (every path) with the variables bound on the way excluded.
    fn walk_first(
        pool: &mut dyn TermPool,
        term: &Rc<Term>,
        candidates: &HashSet<Rc<Term>>,
        bound: &mut Vec<Rc<Term>>,
    ) -> Option<Rc<Term>> {
        let under = |pool: &mut dyn TermPool,
                     vars: Vec<Rc<Term>>,
                     body: &Rc<Term>,
                     bound: &mut Vec<Rc<Term>>| {
            let depth = bound.len();
            bound.extend(vars);
            let found = walk_first(pool, body, candidates, bound);
            bound.truncate(depth);
            found
        };
        match term.as_ref() {
            Term::Var(..) => {
                (candidates.contains(term) && !bound.contains(term)).then(|| term.clone())
            }
            Term::Const(_) => None,
            Term::App(f, args) => std::iter::once(f)
                .chain(args.iter())
                .find_map(|c| walk_first(pool, c, candidates, bound)),
            Term::Op(_, args) | Term::ParamOp { args, .. } | Term::AsOp(_, _, args) => args
                .iter()
                .find_map(|c| walk_first(pool, c, candidates, bound)),
            Term::Binder(_, bindings, inner) => {
                let vars = bindings
                    .iter()
                    .map(|v| pool.add(v.clone().into()))
                    .collect();
                under(pool, vars, inner, bound)
            }
            Term::Let(bindings, inner) => {
                let vars = bindings
                    .iter()
                    .map(|(name, value)| {
                        let sort = pool.sort(value);
                        pool.add(Term::new_var(name.clone(), sort))
                    })
                    .collect();
                under(pool, vars, inner, bound).or_else(|| {
                    bindings
                        .iter()
                        .find_map(|(_, value)| walk_first(pool, value, candidates, bound))
                })
            }
            Term::Match(scrutinee, cases) => walk_first(pool, scrutinee, candidates, bound)
                .or_else(|| {
                    cases.iter().find_map(|case| {
                        let vars: Vec<Rc<Term>> = case
                            .bindings()
                            .iter()
                            .map(|v| pool.add(v.clone().into()))
                            .collect();
                        under(pool, vars, &case.body, bound)
                    })
                }),
        }
    }

    /// Whether `term`, read as a tree (a subterm counted at each of its occurrences), has at most
    /// `limit` nodes.
    fn tree_is_at_most(term: &Rc<Term>, limit: usize) -> bool {
        let mut stack = vec![term];
        let mut count = 0;
        while let Some(t) = stack.pop() {
            count += 1;
            if count > limit {
                return false;
            }
            match t.as_ref() {
                Term::App(f, args) => stack.extend(std::iter::once(f).chain(args.iter())),
                Term::Op(_, args) | Term::ParamOp { args, .. } | Term::AsOp(_, _, args) => {
                    stack.extend(args.iter());
                }
                Term::Binder(_, _, inner) => stack.push(inner),
                Term::Let(bindings, inner) => {
                    stack.push(inner);
                    stack.extend(bindings.iter().map(|(_, value)| value));
                }
                Term::Match(scrutinee, cases) => {
                    stack.push(scrutinee);
                    stack.extend(cases.iter().map(|case| &case.body));
                }
                Term::Var(..) | Term::Const(_) => {}
            }
        }
        true
    }

    fn has_scoping_node(term: &Rc<Term>) -> bool {
        let mut stack = vec![term.clone()];
        let mut seen = HashSet::new();
        while let Some(t) = stack.pop() {
            if !seen.insert(t.clone()) {
                continue;
            }
            match t.as_ref() {
                Term::Binder(..) | Term::Let(..) | Term::Match(..) => return true,
                Term::App(f, args) => {
                    stack.push(f.clone());
                    stack.extend(args.iter().cloned());
                }
                Term::Op(_, args) | Term::ParamOp { args, .. } | Term::AsOp(_, _, args) => {
                    stack.extend(args.iter().cloned());
                }
                Term::Var(..) | Term::Const(_) => {}
            }
        }
        false
    }

    /// Random terms over a few names in several sorts (`Int`, `Bool` and a sort variable), with
    /// shared subterms, applications of free function symbols, binders of every kind that bind a
    /// name twice or shadow an outer one, `let`s whose values mention the names they bind, and
    /// `match`es with variable, wildcard and constructor patterns.
    struct Generator {
        rng: StdRng,
        sorts: Vec<Rc<Sort>>,
        names: Vec<String>,
        /// Terms made so far, by the index of their sort in `sorts`.
        made: Vec<Vec<Rc<Term>>>,
        functions: Vec<(Rc<Term>, Vec<usize>, usize)>,
    }

    impl Generator {
        fn new(pool: &mut PrimitivePool, seed: u64) -> Self {
            let names = ["x", "y", "z", "f"].map(str::to_owned).to_vec();
            Self::over(pool, seed, names)
        }

        /// A generator whose variables and bindings take their names from `names`.
        fn over(pool: &mut PrimitivePool, seed: u64, names: Vec<String>) -> Self {
            let sorts = vec![
                pool.add_sort(Sort::Int),
                pool.add_sort(Sort::Bool),
                pool.add_sort(Sort::Var("A".to_owned())),
            ];
            let mut made = vec![Vec::new(), Vec::new(), Vec::new()];
            for name in &names {
                for (i, sort) in sorts.iter().enumerate() {
                    made[i].push(pool.add(Term::new_var(name.clone(), sort.clone())));
                }
            }
            made[0].push(pool.add(Term::new_int(1)));
            made[1].push(pool.bool_true());
            let mut functions = Vec::new();
            for (name, args, result) in [("f", vec![0], 0), ("g", vec![1, 0], 1), ("h", vec![2], 1)]
            {
                let mut list: Vec<Rc<Sort>> = args.iter().map(|&i| sorts[i].clone()).collect();
                list.push(sorts[result].clone());
                let sort = pool.add_sort(Sort::Function(list));
                functions.push((pool.add(Term::new_var(name, sort)), args, result));
            }
            Self {
                rng: StdRng::seed_from_u64(seed),
                sorts,
                names,
                made,
                functions,
            }
        }

        fn pick(&mut self, sort: usize) -> Rc<Term> {
            let list = &self.made[sort];
            list[self.rng.gen_range(0..list.len())].clone()
        }

        fn bindings(&mut self, at_least: usize) -> Vec<SortedVar> {
            (0..at_least + self.rng.gen_range(0..3))
                .map(|_| {
                    let name = self.names[self.rng.gen_range(0..self.names.len())].clone();
                    let sort = self.sorts[self.rng.gen_range(0..self.sorts.len())].clone();
                    (name, sort)
                })
                .collect()
        }

        /// Makes one more term, of a random sort, from terms made before.
        fn step(&mut self, pool: &mut PrimitivePool) {
            let (sort, term) = match self.rng.gen_range(0..9) {
                0 => {
                    let args = (0..1 + self.rng.gen_range(0..3))
                        .map(|_| self.pick(1))
                        .collect();
                    (1, Term::Op(Operator::And, args))
                }
                1 => {
                    let (a, b) = (self.pick(0), self.pick(0));
                    (0, Term::Op(Operator::Add, vec![a, b]))
                }
                2 => {
                    let i = self.rng.gen_range(0..self.functions.len());
                    let (f, args, result) = self.functions[i].clone();
                    let args = args.iter().map(|&s| self.pick(s)).collect();
                    (result, Term::App(f, args))
                }
                3 | 4 => {
                    let binder = [
                        Binder::Forall,
                        Binder::Exists,
                        Binder::Lambda,
                        Binder::Choice,
                    ][self.rng.gen_range(0..4)];
                    let mut bindings = self.bindings(1);
                    let body = self.pick(1);
                    let sort = match binder {
                        Binder::Forall | Binder::Exists => 1,
                        Binder::Choice => {
                            bindings.truncate(1);
                            let s = self.sorts.iter().position(|s| *s == bindings[0].1).unwrap();
                            s
                        }
                        Binder::ArrayLambda => {
                            return;
                        }
                        Binder::Lambda => {
                            let lambda =
                                pool.add(Term::Binder(binder, BindingList(bindings), body));
                            let other = self.pick(1);
                            let eq = pool.add(Term::Op(Operator::Equals, vec![lambda, other]));
                            self.made[1].push(eq);
                            return;
                        }
                    };
                    (sort, Term::Binder(binder, BindingList(bindings), body))
                }
                5 | 6 => {
                    let names = self.bindings(1);
                    let bindings = names
                        .into_iter()
                        .map(|(name, sort)| {
                            let s = self.sorts.iter().position(|t| *t == sort).unwrap();
                            (name, self.pick(s))
                        })
                        .collect();
                    let s = self.rng.gen_range(0..self.sorts.len());
                    (s, Term::Let(BindingList(bindings), self.pick(s)))
                }
                7 => {
                    let of = self.rng.gen_range(0..self.sorts.len());
                    let scrutinee = self.pick(of);
                    let s = self.rng.gen_range(0..self.sorts.len());
                    let cases = (0..1 + self.rng.gen_range(0..3))
                        .map(|_| {
                            let pattern = match self.rng.gen_range(0..3) {
                                0 => MatchPattern::Wildcard,
                                1 => MatchPattern::Variable(self.bindings(1).remove(0)),
                                _ => MatchPattern::Cons("c".to_owned(), self.bindings(0)),
                            };
                            MatchCase { pattern, body: self.pick(s) }
                        })
                        .collect();
                    (s, Term::Match(scrutinee, cases))
                }
                _ => {
                    let s = self.rng.gen_range(0..self.sorts.len());
                    let (a, b) = (self.pick(s), self.pick(s));
                    (1, Term::Op(Operator::Equals, vec![a, b]))
                }
            };
            let term = pool.add(term);
            self.made[sort].push(term);
        }
    }

    fn pointers(set: impl IntoIterator<Item = Rc<Term>>) -> HashSet<*const Term> {
        set.into_iter().map(|t| Rc::as_ptr(&t)).collect()
    }

    /// Every set the pool computes holds upstream's variables, on 300 random batches of terms:
    /// membership of every variable of every name and sort (bound ones included), the variables
    /// of each name, and the size. `first_free_var` chooses a candidate free in the term, the
    /// first one the documented walk reaches, which is upstream's first candidate in its set's
    /// order whenever one candidate is free there, and whenever no binder, `let` or `match`
    /// occurs in the term.
    #[test]
    fn free_variable_sets_hold_upstreams_variables() {
        let (mut compared, mut chosen, mut as_upstream) = (0, 0, 0);
        for seed in 0..300 {
            let mut pool = PrimitivePool::new();
            let mut generator = Generator::new(&mut pool, seed);
            for _ in 0..60 + seed % 4 * 60 {
                generator.step(&mut pool);
            }
            let terms: Vec<Rc<Term>> = generator.made.iter().flatten().cloned().collect();
            let mut variables: Vec<Rc<Term>> = Vec::new();
            for name in ["x", "y", "z", "f", "g", "h", "w"] {
                for sort in &generator.sorts {
                    variables.push(pool.add(Term::new_var(name, sort.clone())));
                }
            }
            variables.extend(generator.functions.iter().map(|(f, _, _)| f.clone()));
            let mut cache = IndexMap::new();
            for term in &terms {
                let expected = upstream(&mut pool, term, &mut cache);
                let got = pool.free_vars(term);
                assert_eq!(
                    pointers(got.iter().cloned()),
                    pointers(expected.iter().cloned()),
                    "{term}"
                );
                assert_eq!(got.len(), expected.len(), "{term}");
                for var in &variables {
                    assert_eq!(got.contains(var), expected.contains(var), "{var} in {term}");
                }
                for name in ["x", "y", "z", "f", "g", "h", "w"] {
                    let named = pointers(got.named(name).cloned());
                    let want = pointers(
                        expected
                            .iter()
                            .filter(|v| v.as_var() == Some(name))
                            .cloned(),
                    );
                    assert_eq!(named, want, "{name} in {term}");
                    assert_eq!(got.contains_name(name), !want.is_empty());
                }
                compared += 1;

                let candidates: Vec<Rc<Term>> = variables
                    .iter()
                    .filter(|_| generator.rng.gen_bool(0.4))
                    .cloned()
                    .collect();
                let mut set = FreeVars::default();
                for var in &candidates {
                    set = set.union(&FreeVars::singleton(var));
                }
                let first = first_free_var(&mut pool, term, &set);
                let free_candidates: Vec<&Rc<Term>> =
                    expected.iter().filter(|v| candidates.contains(v)).collect();
                assert_eq!(first.is_some(), !free_candidates.is_empty(), "{term}");
                let candidates: HashSet<Rc<Term>> = candidates.into_iter().collect();
                let walked = walk_first(&mut pool, term, &candidates, &mut Vec::new());
                assert_eq!(first, walked, "{term}");
                if let Some(first) = first {
                    chosen += 1;
                    let upstreams = free_candidates[0];
                    if *upstreams == first {
                        as_upstream += 1;
                    } else {
                        assert!(
                            free_candidates.len() > 1 && has_scoping_node(term),
                            "{term}"
                        );
                    }
                }
            }
        }
        eprintln!("{compared} sets compared, {chosen} choices, {as_upstream} upstream's");
        assert!(compared > 10_000 && chosen > 1_000, "{compared} {chosen}");
        assert!(as_upstream * 10 > chosen * 9, "{as_upstream} of {chosen}");
    }

    /// A pool that reads the sets of the pools before it (the parallel checker's `LocalPool`)
    /// computes the same sets, for terms of those pools and for terms it adds itself.
    #[test]
    fn layered_pools_compute_upstreams_sets() {
        for seed in 0..40 {
            let mut global = PrimitivePool::new();
            let mut generator = Generator::new(&mut global, 1000 + seed);
            for _ in 0..40 {
                generator.step(&mut global);
            }
            let old: Vec<Rc<Term>> = generator.made.iter().flatten().cloned().collect();
            // Some of the global pool's sets are cached before it is shared.
            for term in old.iter().step_by(3) {
                global.free_vars(term);
            }
            let global = std::sync::Arc::new(global);
            let context = ContextPool::from_global(&global);
            let mut local = LocalPool::from_previous(&context);
            let mut cache = IndexMap::new();
            for (i, term) in old.iter().enumerate() {
                let bool_sort = local.add_sort(Sort::Bool);
                let b = local.add(Term::new_var(format!("local{}", i % 3), bool_sort.clone()));
                let body = local.add(Term::Op(
                    Operator::And,
                    vec![b, generator.made[1][i % 5].clone()],
                ));
                let new = local.add(Term::Binder(
                    Binder::Exists,
                    BindingList(vec![("x".to_owned(), generator.sorts[0].clone())]),
                    body,
                ));
                for t in [term, &new] {
                    let expected = upstream(&mut local, t, &mut cache);
                    let got = local.free_vars(t);
                    assert_eq!(
                        pointers(got.iter().cloned()),
                        pointers(expected.iter().cloned())
                    );
                }
            }
        }
    }

    /// Sets of many variables, which the merges a thread remembers serve (`Merges`): on 30 random
    /// batches, two chains of 150 links over distinct variables are merged at every link in order
    /// (`(- p_j q_j)`), with a chain over the same variables (`(- p_j t_j)`: equal sets built
    /// apart), and in a random pairing (`(- p_k q_(s(k)))`); random terms over 30 of the chains'
    /// names in three sorts are then built on them, with binders, `let`s and `match`es that bind
    /// those names. Every set the pool computes holds upstream's variables (membership of every
    /// variable, the variables of each name, the size), and `first_free_var` chooses as the
    /// documented walk does. The batches run one after another on one thread, each in a pool made
    /// after the last one was dropped, so the table holds merges of tries that died, at addresses
    /// later tries may have had (an entry keeps its nodes' addresses until it goes). The merges
    /// found remembered are counted: with none, the test would not have reached the table.
    #[test]
    fn wide_sets_hold_upstreams_variables_through_remembered_merges() {
        let found = merges_found();
        let (mut compared, mut chosen) = (0, 0);
        for seed in 0..30 {
            let n = 150;
            let mut pool = PrimitivePool::new();
            let names: Vec<String> = (0..30).map(|i| format!("c{i}")).collect();
            let mut generator = Generator::over(&mut pool, 7000 + seed, names);
            let int = generator.sorts[0].clone();
            let mut var = |name: String| pool.add(Term::new_var(name, int.clone()));
            let cs: Vec<Rc<Term>> = (0..=n).map(|j| var(format!("c{j}"))).collect();
            let ds: Vec<Rc<Term>> = (0..=n).map(|j| var(format!("d{j}"))).collect();
            let (mut ps, mut qs, mut ts) = (
                vec![cs[0].clone()],
                vec![ds[0].clone()],
                vec![cs[0].clone()],
            );
            let mut chain_terms = Vec::new();
            for j in 1..=n {
                let link = |pool: &mut PrimitivePool, op, v: &Rc<Term>, last: &Rc<Term>| {
                    pool.add(Term::Op(op, vec![v.clone(), last.clone()]))
                };
                ps.push(link(&mut pool, Operator::Add, &cs[j], &ps[j - 1]));
                qs.push(link(&mut pool, Operator::Mult, &ds[j], &qs[j - 1]));
                ts.push(link(&mut pool, Operator::Mult, &cs[j], &ts[j - 1]));
                for other in [&qs[j], &ts[j]] {
                    let merged = Term::Op(Operator::Sub, vec![ps[j].clone(), other.clone()]);
                    chain_terms.push(pool.add(merged));
                }
            }
            let mut pairing: Vec<usize> = (1..=n).collect();
            for k in (1..n).rev() {
                pairing.swap(k, generator.rng.gen_range(0..=k));
            }
            for (k, &other) in (1..=n).zip(&pairing) {
                let merged = Term::Op(Operator::Sub, vec![ps[k].clone(), qs[other].clone()]);
                chain_terms.push(pool.add(merged));
            }
            generator.made[0].extend(chain_terms.iter().cloned());
            for _ in 0..150 {
                generator.step(&mut pool);
            }
            let terms: Vec<Rc<Term>> = chain_terms
                .iter()
                .chain(generator.made.iter().flatten())
                .cloned()
                .collect();
            let variables: Vec<Rc<Term>> = generator
                .made
                .iter()
                .flatten()
                .filter(|t| t.is_var())
                .chain(&ds)
                .cloned()
                .collect();
            let mut cache = IndexMap::new();
            for term in &terms {
                let expected = upstream(&mut pool, term, &mut cache);
                let got = pool.free_vars(term);
                assert_eq!(
                    pointers(got.iter().cloned()),
                    pointers(expected.iter().cloned()),
                    "{term}"
                );
                assert_eq!(got.len(), expected.len(), "{term}");
                for var in &variables {
                    assert_eq!(got.contains(var), expected.contains(var), "{var} in {term}");
                }
                for name in ["c0", "c7", "c29", "c140", "d3"] {
                    let named = pointers(got.named(name).cloned());
                    let want = expected
                        .iter()
                        .filter(|v| v.as_var() == Some(name))
                        .cloned();
                    assert_eq!(named, pointers(want), "{name} in {term}");
                }
                compared += 1;
                // The walk reads the term as a tree, every path of it: only terms whose tree is
                // small are walked.
                if !tree_is_at_most(term, 20_000) {
                    continue;
                }
                let candidates: Vec<Rc<Term>> = variables
                    .iter()
                    .filter(|_| generator.rng.gen_bool(0.05))
                    .cloned()
                    .collect();
                let mut set = FreeVars::default();
                for var in &candidates {
                    set = set.union(&FreeVars::singleton(var));
                }
                let first = first_free_var(&mut pool, term, &set);
                let candidates: HashSet<Rc<Term>> = candidates.into_iter().collect();
                let walked = walk_first(&mut pool, term, &candidates, &mut Vec::new());
                assert_eq!(first, walked, "{term}");
                chosen += usize::from(first.is_some());
            }
        }
        let found = merges_found() - found;
        eprintln!("{compared} sets compared, {chosen} choices, {found} merges found remembered");
        assert!(compared > 20_000 && chosen > 5_000, "{compared} {chosen}");
        assert!(found > 10_000, "{found} merges found remembered");
    }

    /// The sets of a chain of terms over distinct constants, `e_j = (bvadd c_j e_(j-1))`, share
    /// all but a path each: 20,000 links take fewer than 40 trie nodes a link, where upstream's
    /// `IndexSet`s held 200 million entries. The nodes allocated are checked as the chain grows,
    /// every 100 links, so sets that copied their children's fail at the 100th link, having
    /// allocated some 25,000 nodes, rather than allocate billions. A link's set is a child's,
    /// extended; a term whose children add nothing has its child's set itself.
    #[test]
    fn a_chains_sets_share_structure() {
        let n = 20_000;
        let mut pool = PrimitivePool::new();
        let bv = pool.add_sort(Sort::BitVec(8));
        let start = nodes_allocated();
        let mut link = pool.add(Term::new_var("c0", bv.clone()));
        let mut links = Vec::new();
        for j in 1..=n {
            let c = pool.add(Term::new_var(format!("c{j}"), bv.clone()));
            link = pool.add(Term::Op(Operator::BvAdd, vec![c, link]));
            links.push(link.clone());
            if j % 100 == 0 {
                pool.free_vars(&link);
                let allocated = nodes_allocated() - start;
                assert!(
                    allocated < 40 * j,
                    "{allocated} nodes allocated for {j} links"
                );
            }
        }
        let end = pool.free_vars(&link);
        assert_eq!(end.len(), n + 1);
        assert!(end.contains_name("c0") && end.contains_name(&format!("c{n}")));
        assert!(!end.contains_name("c"));
        let sets: Vec<FreeVars> = pool.free_vars_cache.values().cloned().collect();
        let tries: Vec<&Trie<Rc<Term>>> = sets.iter().map(FreeVars::trie).collect();
        let nodes = Trie::count_nodes(&tries);
        assert!(nodes < 40 * n, "{nodes} nodes for {n} links");

        let neg = pool.add(Term::Op(Operator::BvNeg, vec![link.clone()]));
        assert!(pool.free_vars(&neg).trie().ptr_eq(end.trie()));
        let below = pool.free_vars(&links[n / 2]);
        assert!(end.union(&below).trie().ptr_eq(end.trie()));
        assert!(below.union(&end).trie().ptr_eq(end.trie()));
    }

    /// Two chains of sets merged at every link, as the pool merges `r_j = (bvor p_j q_j)` with
    /// `p_j = (bvadd c_j p_(j-1))` and `q_j = (bvmul d_j q_(j-1))` over distinct constants, or
    /// over the same ones (`twin`: equal sets built apart). The merges are kept, and with `kept`
    /// every link's `p_j` and `q_j` too, as a pool keeps the sets it caches, so that no entry of the
    /// table of merges dies and only its bound limits it. Returns the cost of each merge, the nodes
    /// it visits and allocates (`VISIT` and `ALLOCATION` fuel units), summed over the links so far,
    /// every 100 links, and stops at the first sum past `bound` per link.
    fn merging_two_chains<V: Value>(
        wrap: fn(u128) -> V,
        n: usize,
        (twin, kept): (bool, bool),
        bound: Fuel,
    ) -> Vec<Fuel> {
        let key = |name: String| (name_hash(&name) as u128) << 64 | 1;
        let (mut p, mut q) = (Trie::default(), Trie::default());
        let (mut merged, mut chains) = (Vec::new(), Vec::new());
        let (mut cost, mut sums) = (0, Vec::new());
        for j in 1..=n {
            let c = key(format!("c{j}"));
            let d = if twin { c } else { key(format!("d{j}")) };
            p = p.insert(c, wrap(c));
            q = q.insert(d, wrap(d));
            if kept {
                chains.push((p.clone(), q.clone()));
            }
            let mut fuel = Fuel::MAX;
            let start = nodes_allocated();
            let r = p.union_within(&q, &mut fuel).expect("unmetered");
            cost += (Fuel::MAX - fuel) + (nodes_allocated() - start) as Fuel * ALLOCATION;
            assert_eq!(r.len(), if twin { j } else { 2 * j });
            merged.push(r);
            if j % 100 == 0 {
                sums.push(cost);
                if cost > bound * j as Fuel {
                    break;
                }
            }
        }
        sums
    }

    /// Two chains merged at every link cost a few paths a link: over distinct keys about 2,000
    /// units a link (4,000 allowed), over the same keys (equal sets built apart) about 80 (200
    /// allowed), up to 20,000 links, also with every link's sets kept, where the table of merges is
    /// emptied at its bound (`LIVE_NODES_PER_ENTRY`) as the tries grow. The cost is checked every
    /// 100 links, so merges that are not remembered, linear in the size of their operands (about 24
    /// units a link per link merged over distinct keys, 1.5 over the same), fail within the first
    /// 1,000 links, as the same merges of tries whose value type remembers none (`Plain`) show
    /// here, rather than run out of memory.
    #[test]
    fn two_chains_merged_at_every_link_cost_a_few_paths_a_link() {
        let n = 20_000;
        for (twin, bound) in [(false, 4_000), (true, 200)] {
            for kept in [false, true] {
                with_merges(|merges: &mut Merges<u128>| *merges = Merges::default());
                let sums = merging_two_chains(|k| k, n, (twin, kept), bound);
                assert_eq!(
                    sums.len(),
                    n / 100,
                    "twin {twin}, kept {kept}: past {bound} a link at {}",
                    sums.len() * 100
                );
            }
            let without = merging_two_chains(Plain, n, (twin, false), bound);
            assert!(without.len() <= 10, "twin {twin}: {without:?}");
        }
    }

    /// The pool's sets of two chains over distinct constants merged at every link, `r_j = (bvor
    /// p_j q_j)` with `p_j = (bvadd c_j p_(j-1))` and `q_j = (bvmul d_j q_(j-1))`, each asked for:
    /// 20,000 links allocate about 110 trie nodes a link (200 allowed), checked every 100 links.
    /// Merges that are not remembered copy each `r_j`'s set whole, `2j` leaves' worth of branches,
    /// and fail by the 300th link; on base 10,000 such links read by one `qnt_rm_unused` step took
    /// 4.7 GB.
    #[test]
    fn a_pools_sets_of_two_chains_merged_at_every_link_share_structure() {
        let n = 20_000;
        let mut pool = PrimitivePool::new();
        let bv = pool.add_sort(Sort::BitVec(8));
        let start = nodes_allocated();
        let mut p = pool.add(Term::new_var("c0", bv.clone()));
        let mut q = pool.add(Term::new_var("d0", bv.clone()));
        for j in 1..=n {
            let c = pool.add(Term::new_var(format!("c{j}"), bv.clone()));
            let d = pool.add(Term::new_var(format!("d{j}"), bv.clone()));
            p = pool.add(Term::Op(Operator::BvAdd, vec![c, p]));
            q = pool.add(Term::Op(Operator::BvMul, vec![d, q]));
            let r = pool.add(Term::Op(Operator::BvOr, vec![p.clone(), q.clone()]));
            assert_eq!(pool.free_vars(&r).len(), 2 * j + 2);
            if j % 100 == 0 {
                let allocated = nodes_allocated() - start;
                assert!(
                    allocated < 200 * j,
                    "{allocated} nodes allocated for {j} links"
                );
            }
        }
        eprintln!("{} nodes for {n} links", nodes_allocated() - start);
    }

    /// The merges remembered keep no trie alive: a merge's result dies with the tries that hold
    /// it, and the table of merges, swept as it grows, holds at most about twice the merges whose
    /// operands and result live, however many died.
    #[test]
    fn remembered_merges_keep_no_trie_alive() {
        // The table starts empty, whatever ran on this thread before.
        with_merges(|merges: &mut Merges<u128>| *merges = Merges::default());
        let keys: Vec<u128> = (0..64u128).map(|i| (i << 64) | (i * 7 + 1)).collect();
        let build = |of: &[u128]| {
            let mut trie = Trie::default();
            for &k in of {
                trie = trie.insert(k, k);
            }
            trie
        };
        let (a, b) = (build(&keys[..40]), build(&keys[20..]));
        let merged = a.union(&b);
        let result = Arc::downgrade(merged.0.as_ref().expect("nonempty"));
        assert!(a.union(&b).ptr_eq(&merged), "the merge is remembered");
        drop((a, b, merged));
        assert!(
            result.upgrade().is_none(),
            "a remembered merge kept its result alive"
        );

        let entries = || with_merges(|merges: &mut Merges<u128>| merges.entries.len()).unwrap();
        for round in 0..2_000u128 {
            let shifted: Vec<u128> = keys.iter().map(|k| k + (round << 32)).collect();
            let (a, b) = (build(&shifted[..40]), build(&shifted[20..]));
            assert_eq!(a.union(&b).len(), 64);
        }
        assert!(entries() <= 2 * SWEEP_MIN, "{} entries", entries());
    }

    /// The table of merges holds at most one entry for every `LIVE_NODES_PER_ENTRY` nodes of the
    /// tries it serves (or `SWEEP_MIN` entries), on sets merged in many pairs that recur little:
    /// two chains of tries over the same 4,000 keys, `p_j` and `q_j` (equal sets built apart, which
    /// share each key's leaf, as the pool's sets share a variable's singleton), all kept, as a pool
    /// keeps the sets it caches, and 4,000 merges `p_k U q_m` of a random pair with `k >= m`, each
    /// folded into the merges before it, all kept too (the review's `twinsup` shape). Every merge's
    /// operands and result live, so no sweep drops an entry: without the bound the table held more
    /// entries than the tries held nodes by the 750th merge, a ratio that grows with the chains.
    /// The nodes are counted every 250 merges; the merges are checked against the keys they must
    /// hold, and some are found remembered.
    #[test]
    fn remembered_merges_stay_within_the_tries_they_serve() {
        with_merges(|merges: &mut Merges<u128>| *merges = Merges::default());
        let n = 4_000;
        let key = |j: usize| (name_hash(&format!("c{j}")) as u128) << 64 | 1;
        let (mut ps, mut qs) = (vec![Trie::default()], vec![Trie::default()]);
        for j in 0..=n {
            // One leaf for both chains, as the pool's sets share a variable's singleton.
            let leaf = Trie::singleton(key(j), key(j));
            let (p, q) = (leaf.union(&ps[j]), leaf.union(&qs[j]));
            ps.push(p);
            qs.push(q);
        }
        let entries = || with_merges(|merges: &mut Merges<u128>| merges.entries.len()).unwrap();
        let mut rng = StdRng::seed_from_u64(1);
        let (found, mut most) = (merges_found(), 0.0f64);
        let mut results = vec![Trie::default()];
        for i in 1..=n {
            let (a, b) = (rng.gen_range(1..=n + 1), rng.gen_range(1..=n + 1));
            let (k, m) = (a.max(b), a.min(b));
            let merged = ps[k].union(&qs[m]);
            assert_eq!(merged.len(), k);
            let last = results.last().expect("a set");
            let folded: Trie<u128> = last.union(&merged);
            assert_eq!(folded.len(), k.max(last.len()));
            results.push(merged);
            results.push(folded);
            if i % 250 == 0 {
                let tries: Vec<&Trie<u128>> = ps.iter().chain(&qs).chain(&results).collect();
                let nodes = Trie::count_nodes(&tries);
                most = most.max(entries() as f64 / nodes as f64);
                assert!(
                    entries() <= nodes / LIVE_NODES_PER_ENTRY + SWEEP_MIN,
                    "{} entries for {nodes} trie nodes after {i} merges",
                    entries()
                );
            }
        }
        let found = merges_found() - found;
        eprintln!("at most {most:.2} entries a node; {found} merges found remembered");
        assert!(found > 0, "no merge found remembered");
    }

    /// Keys as values, in tries whose merges this thread remembers.
    impl Value for u128 {
        fn merges() -> Option<&'static LocalKey<RefCell<Merges<Self>>>> {
            thread_local! {
                static MERGES: RefCell<Merges<u128>> = RefCell::new(Merges::default());
            }
            Some(&MERGES)
        }
    }

    /// Keys as values, in tries whose merges are each computed.
    #[derive(Debug, Clone, Copy, PartialEq)]
    struct Plain(u128);

    impl Value for Plain {
        fn merges() -> Option<&'static LocalKey<RefCell<Merges<Self>>>> {
            None
        }
    }

    /// The trie against a `BTreeMap`: every operation on keys that agree in their high or low 64
    /// bits, on random versions of both, and every version unchanged by the operations on it; for
    /// tries whose merges are remembered, and for tries without.
    #[test]
    fn the_trie_is_a_persistent_map() {
        persistent_map_against_a_btreemap(|k| k, |v| *v);
        persistent_map_against_a_btreemap(Plain, |v| v.0);
        assert_ne!(name_hash("x"), name_hash("y"));
    }

    fn persistent_map_against_a_btreemap<V: Value + std::fmt::Debug>(
        wrap: fn(u128) -> V,
        unwrap: fn(&V) -> u128,
    ) {
        let highs = [0u64, 1, 2, u64::MAX - 1, u64::MAX, 1 << 63];
        let lows = [0u64, 1, 3, 1 << 40, u64::MAX];
        let keys: Vec<u128> = highs
            .iter()
            .flat_map(|&h| lows.iter().map(move |&l| ((h as u128) << 64) | l as u128))
            .collect();
        let mut rng = StdRng::seed_from_u64(7);
        let mut versions: Vec<(Trie<V>, BTreeMap<u128, u128>)> =
            vec![(Trie::default(), BTreeMap::new())];
        for _ in 0..20_000 {
            let (trie, model) = versions[rng.gen_range(0..versions.len())].clone();
            let key = keys[rng.gen_range(0..keys.len())];
            let (trie, model) = match rng.gen_range(0..3) {
                0 => {
                    let mut model = model;
                    model.entry(key).or_insert(key);
                    (trie.insert(key, wrap(key)), model)
                }
                1 => {
                    let mut model = model;
                    model.remove(&key);
                    (trie.remove(key), model)
                }
                _ => {
                    let (other, other_model) = versions[rng.gen_range(0..versions.len())].clone();
                    assert_eq!(
                        trie.intersects(&other),
                        model.keys().any(|k| other_model.contains_key(k))
                    );
                    let mut union = model.clone();
                    for (k, v) in other_model {
                        union.entry(k).or_insert(v);
                    }
                    (trie.union(&other), union)
                }
            };
            assert_eq!(trie.len(), model.len());
            assert_eq!(trie.is_empty(), model.is_empty());
            let values: Vec<u128> = trie.values().map(unwrap).collect();
            assert_eq!(values, model.values().copied().collect::<Vec<_>>());
            for &k in &keys {
                assert_eq!(trie.get(k).map(unwrap), model.get(&k).copied());
            }
            for &h in &highs {
                let range: Vec<u128> = trie.values_in(h).map(unwrap).collect();
                let want: Vec<u128> = model
                    .keys()
                    .copied()
                    .filter(|k| (k >> 64) as u64 == h)
                    .collect();
                assert_eq!(range, want);
            }
            if versions.len() < 64 {
                versions.push((trie, model));
            } else {
                let i = rng.gen_range(0..versions.len());
                versions[i] = (trie, model);
            }
        }
        for (trie, model) in &versions {
            let values: Vec<u128> = trie.values().map(unwrap).collect();
            assert_eq!(values, model.values().copied().collect::<Vec<_>>());
        }
    }
}

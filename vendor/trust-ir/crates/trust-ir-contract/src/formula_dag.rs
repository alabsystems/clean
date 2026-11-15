// trust-ir-contract/formula_dag: a hash-consed DAG of `Formula` nodes and its
// sharing-preserving SMT-LIB printers
//
// A verification condition is a `Formula` TREE: every row carries its own copy
// of every subterm it mentions, so a function whose rows share a growing
// context costs Θ(rows × context) to build, hash, print and solve. This module
// is the representation that stores each distinct subterm ONCE:
//
//   * a node is keyed on (its own payload, its children's ids), compared by
//     EXACT equality — a hash only selects candidates, never decides identity;
//   * construction is bottom-up (`mk`), so a child id always precedes its
//     parent's and the store is acyclic by construction;
//   * a node id names the DAG that issued it, so an id can never stand for a
//     node of another DAG;
//   * `intern` (tree -> DAG) and `expand` (DAG -> tree) are iterative and are
//     built on the crate's own exhaustive `Formula::children` /
//     `Formula::map_children`, so no variant can be skipped or treated as an
//     opaque leaf;
//   * the printers use the same per-node spelling as `Formula::to_smtlib`
//     (`Formula::write_smtlib_node`), so the sharing text and the tree text
//     cannot spell anything differently.
//
// There is NO new `Formula` variant (a `Ref`/`Let` node would be an opaque
// leaf to every downstream walker's wildcard arm), no wire, Lean or olean
// change, and the `trust-types.Formula@1` schema tag is unchanged.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::Symbol;
use crate::formula::{Formula, escape_smtlib_symbol};
use crate::fx::{FxHashMap, FxHashSet};
use crate::sort::Sort;
use std::collections::hash_map::{Entry, RandomState};
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::hash::{BuildHasher, BuildHasherDefault, Hasher};
use std::iter::FusedIterator;
use std::sync::atomic::{AtomicU64, Ordering};

// ─────────────────────────────────────────────────────────────────────────────
// Identities and shells
// ─────────────────────────────────────────────────────────────────────────────

/// The identity of one node of one [`FormulaDag`].
///
/// An id carries the brand of the DAG that issued it, and every operation of
/// any other DAG refuses it ([`DagError::UnknownNode`], or a panic where a
/// method documents one): an id never silently stands for another DAG's node.
/// Within its DAG, ids are dense and assigned in creation order, so a node's
/// children always have smaller indexes than the node itself.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct NodeId {
    /// The brand of the issuing DAG.
    dag: u64,
    index: u32,
}

impl NodeId {
    /// The dense index of this node in its DAG (`0..dag.len()`).
    #[must_use]
    pub fn index(self) -> usize {
        // u32 -> usize is lossless on every target this crate supports
        // (16-bit targets are not among them).
        self.index as usize
    }
}

impl fmt::Display for NodeId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "n{}", self.index)
    }
}

/// The brand of the next [`FormulaDag`]: process-wide and never reused, so
/// two DAGs (a clone included) never share one.
static NEXT_BRAND: AtomicU64 = AtomicU64::new(0);

fn fresh_brand() -> u64 {
    NEXT_BRAND
        .try_update(Ordering::Relaxed, Ordering::Relaxed, |n| n.checked_add(1))
        .expect("a process creates at most 2^64 FormulaDags (the brand width)")
}

/// One node with its children stripped: the operator and every payload field
/// (widths, sorts, names, quantifier bindings), and the number of children.
///
/// A fixed-arity child slot holds the placeholder `Formula::Bool(true)`; the
/// child list of an n-ary node (`And`, `Or`, `Pred`, `Ctor`, `FnApp`) is
/// EMPTY, its length being [`Shell::arity`]. So a shell costs its payload,
/// whatever its arity.
///
/// Two nodes of a [`FormulaDag`] are the same node exactly when their shells
/// are equal and their child ids are equal, element by element.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Shell {
    node: Formula,
    arity: usize,
}

impl Shell {
    /// The shell of `node`, cloning its payload but none of its children.
    #[must_use]
    pub fn of(node: &Formula) -> Shell {
        Shell {
            node: node.shell_clone(),
            arity: node.children().len(),
        }
    }

    /// Split an owned node into its shell and its children (in
    /// [`Formula::children`] order). The children are moved, not cloned.
    #[must_use]
    pub fn split(node: Formula) -> (Shell, Vec<Formula>) {
        let (node, kids) = node.split_children();
        let arity = kids.len();
        (Shell { node, arity }, kids)
    }

    /// The number of child slots.
    #[must_use]
    pub fn arity(&self) -> usize {
        self.arity
    }

    /// The stripped node: every fixed-arity child slot holds the placeholder
    /// `Formula::Bool(true)`, and an n-ary node's child list is empty (its
    /// length is [`Shell::arity`], not the list's). Spell a shell with
    /// [`Shell::write_smtlib_node`], which supplies the arity.
    #[must_use]
    pub fn payload(&self) -> &Formula {
        &self.node
    }

    /// Whether the node binds variable names in its children (a quantifier).
    #[must_use]
    pub fn binds_variables(&self) -> bool {
        self.node.binds_variables()
    }

    /// The variables the node binds; see [`Formula::bound_variables`].
    #[must_use]
    pub fn bound_variables(&self) -> Option<&[(Symbol, Sort)]> {
        self.node.bound_variables()
    }

    /// [`Formula::write_smtlib_node`] of the node this shell strips: its
    /// spelling, calling `child(i, out)` where child `i` belongs.
    pub fn write_smtlib_node(&self, out: &mut String, child: &mut dyn FnMut(usize, &mut String)) {
        self.node.write_smtlib_shell(self.arity, out, child);
    }

    /// Rebuild a full node from this shell and `kids` (in
    /// [`Formula::children`] order).
    ///
    /// # Errors
    ///
    /// [`DagError::ArityMismatch`] if `kids.len()` is not the shell's arity.
    pub fn rebuild(&self, kids: Vec<Formula>) -> Result<Formula, DagError> {
        if kids.len() != self.arity {
            return Err(DagError::ArityMismatch {
                expected: self.arity,
                found: kids.len(),
            });
        }
        Ok(self.node.clone().fill_children(kids))
    }
}

/// Why a [`FormulaDag`] operation was refused.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum DagError {
    /// A shell was given a number of children different from its arity.
    ArityMismatch {
        /// The shell's arity.
        expected: usize,
        /// The number of children supplied.
        found: usize,
    },
    /// A node id is not a node of this DAG: another DAG issued it, or it is
    /// out of range.
    UnknownNode {
        /// The offending id.
        node: NodeId,
        /// The number of nodes the DAG holds.
        len: usize,
    },
    /// A node shared at the top level of several assertions has no sort this
    /// module can name, so it cannot be written as a `define-fun`: its
    /// operands' sorts are unknown, or two of them disagree (mixed `Int` /
    /// `Real` arithmetic, which one solver coerces and another refuses).
    UnsortedDefinition {
        /// The node that needed a sort.
        node: NodeId,
    },
}

impl fmt::Display for DagError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DagError::ArityMismatch { expected, found } => {
                write!(f, "shell of arity {expected} was given {found} children")
            }
            DagError::UnknownNode { node, len } => {
                write!(f, "{node} is not a node of this DAG (it holds {len} nodes)")
            }
            DagError::UnsortedDefinition { node } => write!(
                f,
                "{node} is shared across assertions but its sort cannot be inferred \
                 (unknown or disagreeing operand sorts), so it has no define-fun spelling"
            ),
        }
    }
}

impl std::error::Error for DagError {}

// ─────────────────────────────────────────────────────────────────────────────
// Exact interning
// ─────────────────────────────────────────────────────────────────────────────

/// A `u64` that is already a hash: the identity hasher for [`ExactIndex`].
#[derive(Default)]
struct PreHashed(u64);

impl Hasher for PreHashed {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, bytes: &[u8]) {
        // Only `write_u64` is used (the key type is `u64`); fold anything
        // else in so the hasher stays total.
        for b in bytes {
            self.0 = self.0.rotate_left(8) ^ u64::from(*b);
        }
    }
    fn write_u64(&mut self, n: u64) {
        self.0 = n;
    }
}

/// The candidates for one hash value: almost always one id (a second needs
/// a collision of a randomly keyed 64-bit hash), so the rare list is boxed
/// to keep the common entry small.
#[derive(Debug, Clone)]
enum Bucket {
    One(u32),
    Many(Box<[u32]>),
}

/// Hash -> ids of the entries with that hash. The entries themselves live in
/// the owner's vectors and are compared there by EXACT equality, so a hash
/// collision costs a comparison and can never merge two different entries.
#[derive(Debug, Clone, Default)]
struct ExactIndex {
    map: HashMap<u64, Bucket, BuildHasherDefault<PreHashed>>,
}

impl ExactIndex {
    fn find(&self, hash: u64, mut equal: impl FnMut(u32) -> bool) -> Option<u32> {
        match self.map.get(&hash)? {
            Bucket::One(id) => equal(*id).then_some(*id),
            Bucket::Many(ids) => ids.iter().copied().find(|&id| equal(id)),
        }
    }

    fn insert(&mut self, hash: u64, id: u32) {
        match self.map.entry(hash) {
            Entry::Vacant(slot) => {
                slot.insert(Bucket::One(id));
            }
            Entry::Occupied(mut slot) => {
                let bucket = slot.get_mut();
                match bucket {
                    Bucket::One(first) => *bucket = Bucket::Many(Box::new([*first, id])),
                    Bucket::Many(ids) => {
                        let mut grown = std::mem::take(ids).into_vec();
                        grown.push(id);
                        *ids = grown.into_boxed_slice();
                    }
                }
            }
        }
    }
}

/// One node: its shell (an index into the distinct shells) and its children
/// (a range of the shared child-index arena).
#[derive(Debug, Clone, Copy)]
struct NodeRec {
    shell: u32,
    /// `u32`, the `NodeId` width: a node with 2^32 or more children is
    /// refused (with a panic naming the width) rather than truncated.
    kids_len: u32,
    kids_start: usize,
}

/// A hash-consed store of [`Formula`] nodes.
///
/// Every distinct (shell, children) pair is stored once, so a formula with
/// shared subterms costs memory proportional to its number of DISTINCT
/// subterms plus their child lists, not to the size of its tree. Distinct
/// shells are stored once too (every `bvadd` of width 64 shares one shell,
/// every `And` of five children another), and a shell holds its payload
/// only, never a placeholder per child: a node costs one shell index, a
/// child range, and four bytes per child.
///
/// # Example
///
/// ```
/// use trust_ir_contract::formula_dag::FormulaDag;
/// use trust_ir_contract::{Formula, Sort};
///
/// let x = Formula::Var("x".into(), Sort::Int);
/// let big = Formula::Add(Box::new(x.clone()), Box::new(Formula::Int(1)));
/// // The same subterm twice: a tree of 7 nodes, a DAG of 4.
/// let f = Formula::Eq(Box::new(big.clone()), Box::new(big));
///
/// let mut dag = FormulaDag::new();
/// let root = dag.intern(&f);
/// assert_eq!(dag.len(), 4);
/// assert_eq!(dag.expand(root), f);
/// assert_eq!(dag.to_smtlib(root), "(let ((dag!0_0 (+ x 1))) (= dag!0_0 dag!0_0))");
/// assert_eq!(f.to_smtlib(), "(= (+ x 1) (+ x 1))");
///
/// // An id is the issuing DAG's alone.
/// let other = FormulaDag::new();
/// assert!(!other.contains(root));
/// ```
#[derive(Debug)]
pub struct FormulaDag {
    /// This DAG's brand, carried by every id it issues.
    brand: u64,
    /// Hashes keys for the two indexes. Randomly keyed (std's SipHash), so
    /// formula payloads chosen to collide cannot degrade interning; the
    /// indexes are never iterated, so ids and every output stay
    /// deterministic regardless of the key.
    hasher: RandomState,
    shells: Vec<Shell>,
    shell_index: ExactIndex,
    nodes: Vec<NodeRec>,
    /// The children of every node, as indexes into `nodes`.
    kids: Vec<u32>,
    node_index: ExactIndex,
    /// `mk`'s reusable buffer of child indexes.
    scratch: Vec<u32>,
    /// Test-only: every hash is 0, so every lookup scans every candidate and
    /// identity rests on the exact comparisons alone.
    #[cfg(test)]
    collide: bool,
}

impl Default for FormulaDag {
    fn default() -> FormulaDag {
        FormulaDag {
            brand: fresh_brand(),
            hasher: RandomState::new(),
            shells: Vec::new(),
            shell_index: ExactIndex::default(),
            nodes: Vec::new(),
            kids: Vec::new(),
            node_index: ExactIndex::default(),
            scratch: Vec::new(),
            #[cfg(test)]
            collide: false,
        }
    }
}

impl Clone for FormulaDag {
    /// A copy under a NEW brand: it holds the same nodes at the same
    /// indexes, but an id of the original is not an id of the copy (the two
    /// may diverge afterwards, and an id must never name another DAG's node).
    /// Translate an id deliberately with [`FormulaDag::id_at`] and
    /// [`NodeId::index`].
    fn clone(&self) -> FormulaDag {
        FormulaDag {
            brand: fresh_brand(),
            hasher: self.hasher.clone(),
            shells: self.shells.clone(),
            shell_index: self.shell_index.clone(),
            nodes: self.nodes.clone(),
            kids: self.kids.clone(),
            node_index: self.node_index.clone(),
            scratch: Vec::new(),
            #[cfg(test)]
            collide: self.collide,
        }
    }
}

/// The children of one node, as ids of its DAG (see [`FormulaDag::kids`]).
#[derive(Debug, Clone)]
pub struct Kids<'a> {
    dag: u64,
    ids: std::slice::Iter<'a, u32>,
}

impl Iterator for Kids<'_> {
    type Item = NodeId;

    fn next(&mut self) -> Option<NodeId> {
        let index = *self.ids.next()?;
        Some(NodeId {
            dag: self.dag,
            index,
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.ids.size_hint()
    }
}

impl DoubleEndedIterator for Kids<'_> {
    fn next_back(&mut self) -> Option<NodeId> {
        let index = *self.ids.next_back()?;
        Some(NodeId {
            dag: self.dag,
            index,
        })
    }
}

impl ExactSizeIterator for Kids<'_> {}

impl FusedIterator for Kids<'_> {}

impl FormulaDag {
    /// An empty DAG, with a brand no other DAG of this process has.
    #[must_use]
    pub fn new() -> FormulaDag {
        FormulaDag::default()
    }

    /// The number of distinct nodes.
    #[must_use]
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Whether the DAG holds no node.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// The number of child edges over all distinct nodes.
    #[must_use]
    pub fn edge_count(&self) -> usize {
        self.kids.len()
    }

    /// The number of distinct shells.
    #[must_use]
    pub fn shell_count(&self) -> usize {
        self.shells.len()
    }

    /// Whether `id` is a node of this DAG: issued by it (not by another DAG,
    /// a clone included) and in range.
    #[must_use]
    pub fn contains(&self, id: NodeId) -> bool {
        id.dag == self.brand && id.index() < self.nodes.len()
    }

    /// The id of this DAG's node at dense index `index`, if there is one.
    /// The way to enumerate the nodes, or to carry an index across a
    /// [`Clone`] deliberately.
    #[must_use]
    pub fn id_at(&self, index: usize) -> Option<NodeId> {
        if index >= self.nodes.len() {
            return None;
        }
        u32::try_from(index).ok().map(|index| self.id(index))
    }

    fn id(&self, index: u32) -> NodeId {
        NodeId {
            dag: self.brand,
            index,
        }
    }

    /// The index of `id`, or the refusal.
    fn check(&self, id: NodeId) -> Result<u32, DagError> {
        if self.contains(id) {
            Ok(id.index)
        } else {
            Err(DagError::UnknownNode {
                node: id,
                len: self.nodes.len(),
            })
        }
    }

    /// The index of `id`.
    ///
    /// # Panics
    ///
    /// If `id` is not a node of this DAG.
    fn ix(&self, id: NodeId) -> u32 {
        match self.check(id) {
            Ok(ix) => ix,
            Err(refused) => panic!("{refused}"),
        }
    }

    fn shell_of(&self, ix: u32) -> &Shell {
        &self.shells[self.nodes[ix as usize].shell as usize]
    }

    fn kids_of(&self, ix: u32) -> &[u32] {
        let rec = self.nodes[ix as usize];
        &self.kids[rec.kids_start..rec.kids_start + rec.kids_len as usize]
    }

    /// The shell of node `id`.
    ///
    /// # Panics
    ///
    /// If `id` is not a node of this DAG.
    #[must_use]
    pub fn shell(&self, id: NodeId) -> &Shell {
        self.shell_of(self.ix(id))
    }

    /// The children of node `id`, in [`Formula::children`] order.
    ///
    /// # Panics
    ///
    /// If `id` is not a node of this DAG.
    #[must_use]
    pub fn kids(&self, id: NodeId) -> Kids<'_> {
        Kids {
            dag: self.brand,
            ids: self.kids_of(self.ix(id)).iter(),
        }
    }

    fn shell_hash(&self, shell: &Shell) -> u64 {
        #[cfg(test)]
        if self.collide {
            return 0;
        }
        self.hasher.hash_one(shell)
    }

    fn node_hash(&self, sid: u32, kids: &[u32]) -> u64 {
        #[cfg(test)]
        if self.collide {
            return 0;
        }
        self.hasher.hash_one((sid, kids))
    }

    fn find_shell(&self, shell: &Shell) -> Option<u32> {
        let hash = self.shell_hash(shell);
        self.shell_index
            .find(hash, |s| self.shells[s as usize] == *shell)
    }

    fn find_node(&self, hash: u64, sid: u32, kids: &[u32]) -> Option<u32> {
        self.node_index.find(hash, |n| {
            self.nodes[n as usize].shell == sid && self.kids_of(n) == kids
        })
    }

    /// The node with this shell and these children, if the DAG holds it
    /// (`None` for a child that is not a node of this DAG, too).
    #[must_use]
    pub fn get(&self, shell: &Shell, kids: &[NodeId]) -> Option<NodeId> {
        if kids.len() != shell.arity || !kids.iter().all(|&kid| self.contains(kid)) {
            return None;
        }
        let sid = self.find_shell(shell)?;
        let ixs: Vec<u32> = kids.iter().map(|kid| kid.index).collect();
        let hash = self.node_hash(sid, &ixs);
        self.find_node(hash, sid, &ixs).map(|ix| self.id(ix))
    }

    /// Build a node bottom-up: the node with `shell` and children `kids`,
    /// created if the DAG does not hold it yet.
    ///
    /// # Errors
    ///
    /// [`DagError::ArityMismatch`] if `kids.len()` is not the shell's arity;
    /// [`DagError::UnknownNode`] if a child is not a node of this DAG.
    pub fn mk(&mut self, shell: Shell, kids: &[NodeId]) -> Result<NodeId, DagError> {
        if kids.len() != shell.arity {
            return Err(DagError::ArityMismatch {
                expected: shell.arity,
                found: kids.len(),
            });
        }
        let mut ixs = std::mem::take(&mut self.scratch);
        ixs.clear();
        for &kid in kids {
            match self.check(kid) {
                Ok(ix) => ixs.push(ix),
                Err(refused) => {
                    self.scratch = ixs;
                    return Err(refused);
                }
            }
        }
        let ix = self.insert(shell, &ixs);
        self.scratch = ixs;
        Ok(self.id(ix))
    }

    /// [`FormulaDag::mk`] with the shell of `template` (whose own children
    /// are ignored; only their number matters).
    ///
    /// # Errors
    ///
    /// As [`FormulaDag::mk`].
    pub fn mk_like(&mut self, template: &Formula, kids: &[NodeId]) -> Result<NodeId, DagError> {
        self.mk(Shell::of(template), kids)
    }

    /// Insert without validation: `kids` are nodes of this DAG and their
    /// number is the shell's arity.
    fn insert(&mut self, shell: Shell, kids: &[u32]) -> u32 {
        let sid = self.intern_shell(shell);
        self.insert_with_shell(sid, kids)
    }

    /// [`FormulaDag::insert`] for an already-interned shell.
    fn insert_with_shell(&mut self, sid: u32, kids: &[u32]) -> u32 {
        let hash = self.node_hash(sid, kids);
        if let Some(ix) = self.find_node(hash, sid, kids) {
            return ix;
        }
        let ix = u32::try_from(self.nodes.len())
            .expect("a FormulaDag holds at most 2^32 nodes (the NodeId width)");
        let kids_start = self.kids.len();
        self.kids.extend_from_slice(kids);
        let kids_len =
            u32::try_from(kids.len()).expect("a node has at most 2^32 children (the NodeId width)");
        self.nodes.push(NodeRec {
            shell: sid,
            kids_len,
            kids_start,
        });
        self.node_index.insert(hash, ix);
        ix
    }

    fn intern_shell(&mut self, shell: Shell) -> u32 {
        let hash = self.shell_hash(&shell);
        if let Some(sid) = self
            .shell_index
            .find(hash, |s| self.shells[s as usize] == shell)
        {
            return sid;
        }
        let sid = u32::try_from(self.shells.len())
            .expect("a FormulaDag holds at most 2^32 shells (the NodeId width)");
        self.shells.push(shell);
        self.shell_index.insert(hash, sid);
        sid
    }

    /// Intern a formula tree, returning the id of its root. Equal subtrees
    /// (here or in anything interned before) become one node.
    ///
    /// Iterative: the depth of `f` is bounded by memory, not by the stack.
    /// The work is proportional to the size of the tree `f`; the working
    /// memory is a few words per level of the walk plus one reference per
    /// sibling still to visit.
    pub fn intern(&mut self, f: &Formula) -> NodeId {
        // `pending` holds the children not yet visited, of every frame,
        // last child first: a frame's unvisited children are always on top
        // of it, because a deeper frame's children are pushed later and
        // consumed first.
        struct Frame<'a> {
            node: &'a Formula,
            remaining: usize,
            arity: usize,
        }
        fn open<'a>(node: &'a Formula, pending: &mut Vec<&'a Formula>) -> Frame<'a> {
            let kids = node.children();
            let arity = kids.len();
            pending.extend(kids.into_iter().rev());
            Frame {
                node,
                remaining: arity,
                arity,
            }
        }
        let mut pending: Vec<&Formula> = Vec::new();
        let mut frames: Vec<Frame<'_>> = Vec::new();
        let mut done: Vec<u32> = Vec::new();
        frames.push(open(f, &mut pending));
        while let Some(top) = frames.last_mut() {
            if top.remaining > 0 {
                top.remaining -= 1;
                if let Some(kid) = pending.pop() {
                    let frame = open(kid, &mut pending);
                    frames.push(frame);
                }
                continue;
            }
            let start = done.len() - top.arity;
            let shell = Shell::of(top.node);
            frames.pop();
            let ix = self.insert(shell, &done[start..]);
            done.truncate(start);
            done.push(ix);
        }
        // The root's frame popped last and pushed exactly one index.
        let root = done
            .pop()
            .expect("interning a formula yields its root's id");
        self.id(root)
    }

    /// [`FormulaDag::intern`] for an owned tree: the payloads are moved into
    /// the shells instead of cloned, and each node's shell is interned as
    /// soon as the node is split, so a level of the walk holds a shell index
    /// rather than a shell. Iterative, linear in the size of `f`.
    pub fn intern_owned(&mut self, f: Formula) -> NodeId {
        struct Frame {
            shell: u32,
            remaining: usize,
            arity: usize,
        }
        let mut pending: Vec<Formula> = Vec::new();
        let mut frames: Vec<Frame> = Vec::new();
        let mut done: Vec<u32> = Vec::new();
        let open = |dag: &mut FormulaDag, node: Formula, pending: &mut Vec<Formula>| {
            let (shell, mut kids) = Shell::split(node);
            let arity = kids.len();
            kids.reverse();
            pending.append(&mut kids);
            Frame {
                shell: dag.intern_shell(shell),
                remaining: arity,
                arity,
            }
        };
        let root = open(self, f, &mut pending);
        frames.push(root);
        while let Some(top) = frames.last_mut() {
            if top.remaining > 0 {
                top.remaining -= 1;
                if let Some(kid) = pending.pop() {
                    let frame = open(self, kid, &mut pending);
                    frames.push(frame);
                }
                continue;
            }
            let (sid, arity) = (top.shell, top.arity);
            frames.pop();
            let start = done.len() - arity;
            let ix = self.insert_with_shell(sid, &done[start..]);
            done.truncate(start);
            done.push(ix);
        }
        let root = done
            .pop()
            .expect("interning a formula yields its root's id");
        self.id(root)
    }

    /// The formula tree node `id` stands for: the exact tree whose
    /// [`FormulaDag::intern`] is `id`.
    ///
    /// This is the cold path. Its cost is the size of the TREE it returns,
    /// which for a node with shared subterms can be far larger than the DAG
    /// (a chain of `n` nodes that each use their child twice expands to
    /// `2^n` leaves). It is iterative; a very deep result should be released
    /// with [`Formula::drop_iterative`].
    ///
    /// # Panics
    ///
    /// If `id` is not a node of this DAG.
    #[must_use]
    pub fn expand(&self, id: NodeId) -> Formula {
        let mut stack: Vec<(u32, usize)> = vec![(self.ix(id), 0)];
        let mut built: Vec<Formula> = Vec::new();
        while let Some(top) = stack.last_mut() {
            let (node, next) = *top;
            let kids = self.kids_of(node);
            if let Some(&kid) = kids.get(next) {
                top.1 += 1;
                stack.push((kid, 0));
                continue;
            }
            stack.pop();
            let args = built.split_off(built.len() - kids.len());
            // `args.len()` is the shell's arity by construction;
            // `fill_children` panics rather than build anything else.
            built.push(self.shell_of(node).node.clone().fill_children(args));
        }
        built.pop().expect("expanding a node yields its tree")
    }

    // ── SMT-LIB printers ────────────────────────────────────────────────────

    /// The SMT-LIB text of node `root` with every shared compound subterm
    /// written once, bound by `let`. Logically identical to
    /// `self.expand(root).to_smtlib()`.
    ///
    /// * Spelling: every node is spelled by [`Formula::write_smtlib_node`],
    ///   the function the tree printer uses.
    /// * Sharing: a compound node referenced more than once — counting the
    ///   repeated operand slots of the truncating `Div`/`Rem`, signed
    ///   `BvToInt` and saturating `FpToSbv`/`FpToUbv` spellings — is bound
    ///   once. A leaf is bound only when its text is longer than any name the
    ///   printer can produce. Bindings of one dependency level share one
    ///   parallel `let`, so the `let` nesting of a region is the longest
    ///   chain of its bindings, not their number.
    /// * Binders: under a quantifier, a symbol spelled like a name it binds
    ///   denotes the bound variable, so one DAG node can mean different
    ///   things on the two sides of a binder. A node is bound in the
    ///   outermost `let` region where it means what it means at every one of
    ///   its uses: the top level when it mentions no name that any binder of
    ///   the printed DAG binds; the body of the innermost enclosing binder of
    ///   `k` when the one such name it mentions is `k` (the top level when no
    ///   enclosing binder binds `k`); the region of each use otherwise (two
    ///   or more such names). So a subterm closed under the binders it sits
    ///   in is written once however many binder bodies use it, and a binding
    ///   is never captured.
    /// * Names: `dag!<j>_<k>`, where `j` is the smallest number such that
    ///   `dag!<j>_` occurs nowhere in the formula's own text, so a name can
    ///   neither capture nor be captured, and its length is logarithmic in
    ///   the text, whatever the formula's symbols are.
    ///
    /// Size and work: every (node, region) spelling is written once, so the
    /// output is linear in the reachable DAG for a quantifier-free term and
    /// for one whose shared subterms mean the same in every binder body that
    /// uses them; the work (see [`PrintStats`]) is linear in the reachable
    /// DAG plus the output. A subterm that mentions a variable of a binder
    /// is written once in each printed body of that binder, and no `let`
    /// text can do better (a `let` binding cannot denote the variables of a
    /// binder it is outside of), so a DAG that nests such binders inside
    /// one another can print larger than linear — never larger than its
    /// tree text. `LIMITATIONS.md` records the bound. The walk is iterative.
    ///
    /// # Panics
    ///
    /// If `root` is not a node of this DAG.
    #[must_use]
    pub fn to_smtlib(&self, root: NodeId) -> String {
        let mut out = String::new();
        self.write_smtlib(root, &mut out);
        out
    }

    /// Append [`FormulaDag::to_smtlib`]'s text to `out`, returning the
    /// print's work counters.
    ///
    /// # Panics
    ///
    /// If `root` is not a node of this DAG.
    pub fn write_smtlib(&self, root: NodeId, out: &mut String) -> PrintStats {
        let roots = [self.ix(root)];
        let mut stats = PrintStats::default();
        let reach = reach(self, &roots, &mut stats);
        let plan = Planner::run(self, &reach, &roots, &mut stats);
        let level = levels(self, &plan);
        let before = out.len();
        let mut emitter = Emitter::new(self, &plan, &level, &reach.prefix);
        let task = emitter.region_task(0);
        emitter.run(vec![Task::Region(Box::new(task))], out);
        stats.rendered_bytes += emitter.rendered;
        stats.output_bytes = out.len() - before;
        stats
    }

    /// SMT-LIB text for several assertions at once, sharing across them.
    ///
    /// A compound node that is bound at the top level (by the rules of
    /// [`FormulaDag::to_smtlib`], counting references from every assertion,
    /// binder bodies included) becomes one `(define-fun NAME () SORT TERM)`;
    /// a node bound inside a binder body stays a `let` there. The
    /// definitions are in dependency order. `terms[i]` is the text of
    /// `roots[i]` in terms of those names; the definitions must precede any
    /// assertion of a term. The names are fresh with respect to the text of
    /// `roots`; a caller that also declares other symbols named `dag!…`
    /// gets a redefinition error from the solver, never a silent capture.
    ///
    /// Not for the strict-certification lane: in the shared-VC design
    /// measurement (ay 0.27, 2026-09-30) ay's strict UNSAT certification
    /// rejected refutations over `define-fun` definitions (an uncertified
    /// "hole" step) and accepted the same rows written with `let` — use
    /// [`FormulaDag::to_smtlib`] per assertion there.
    ///
    /// # Errors
    ///
    /// [`DagError::UnknownNode`] for a root that is not a node of this DAG;
    /// [`DagError::UnsortedDefinition`] for a shared node whose sort cannot
    /// be inferred: an ill-sorted formula, or one whose operands mix sorts a
    /// solver may coerce (`Int` and `Real`), which this printer refuses to
    /// guess.
    pub fn to_smtlib_script(&self, roots: &[NodeId]) -> Result<SmtlibScript, DagError> {
        let mut ixs = Vec::with_capacity(roots.len());
        for &root in roots {
            ixs.push(self.check(root)?);
        }
        let mut stats = PrintStats::default();
        let reach = reach(self, &ixs, &mut stats);
        let plan = Planner::run(self, &reach, &ixs, &mut stats);
        let level = levels(self, &plan);
        let sorts = infer_sorts(self, &reach.order);
        let mut emitter = Emitter::new(self, &plan, &level, &reach.prefix);
        let top = &plan.regions[0];
        let top_bindings = &plan.bound[top.bind_start..top.bind_end];
        let mut definitions = Vec::with_capacity(top_bindings.len());
        for &b in top_bindings {
            let node = plan.spellings[b].node;
            let sort = sorts.get(node).ok_or(DagError::UnsortedDefinition {
                node: self.id(node),
            })?;
            let mut text = String::from("(define-fun ");
            emitter.bind_name(b, &mut text);
            text.push_str(" () ");
            text.push_str(&sort.to_smtlib());
            text.push(' ');
            // The definition's body is the node's own spelling; its children
            // resolve through the names defined so far, which (post-order)
            // include every top-level binding it uses.
            let frame = emitter.node_task(b);
            emitter.run(vec![frame], &mut text);
            text.push(')');
            stats.output_bytes += text.len();
            definitions.push(text);
        }
        let mut terms = Vec::with_capacity(roots.len());
        for &root in &plan.roots {
            let mut text = String::new();
            if plan.is_bound(root) {
                emitter.write_name(root, &mut text);
            } else {
                let frame = emitter.node_task(root);
                emitter.run(vec![frame], &mut text);
            }
            stats.output_bytes += text.len();
            terms.push(text);
        }
        stats.rendered_bytes += emitter.rendered;
        Ok(SmtlibScript {
            definitions,
            terms,
            stats,
        })
    }
}

/// The output of [`FormulaDag::to_smtlib_script`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SmtlibScript {
    /// `(define-fun NAME () SORT TERM)` commands, in dependency order.
    pub definitions: Vec<String>,
    /// One term per root, in the order the roots were given.
    pub terms: Vec<String>,
    /// The print's work counters.
    pub stats: PrintStats,
}

impl SmtlibScript {
    /// Append the definitions and then `(assert TERM)` for every term, one
    /// command per line.
    pub fn write_assertions(&self, out: &mut String) {
        for definition in &self.definitions {
            out.push_str(definition);
            out.push('\n');
        }
        for term in &self.terms {
            out.push_str("(assert ");
            out.push_str(term);
            out.push_str(")\n");
        }
    }
}

/// The work counters of one sharing print: deterministic measures of what
/// the printer did, so a test can hold its work linear (a super-linear
/// regression shows as a counter that more than doubles when the input
/// doubles, not as a hung run).
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct PrintStats {
    /// Distinct nodes reachable from the printed roots.
    pub nodes: usize,
    /// Spellings: the distinct (node, `let` region) pairs. Each is written
    /// once (a short leaf may be repeated inline where it is used).
    pub spellings: usize,
    /// Child references the analysis resolved: one per printed child slot of
    /// each spelling.
    pub references: usize,
    /// `let` regions: the top level and one per printed binder.
    pub regions: usize,
    /// Spellings bound by a `let` or a `define-fun`.
    pub bindings: usize,
    /// Bytes of node spellings rendered by the analysis and the printing,
    /// the printers' dominant work.
    pub rendered_bytes: usize,
    /// Bytes of text produced.
    pub output_bytes: usize,
}

// ─────────────────────────────────────────────────────────────────────────────
// The sharing printer: what is reachable, and what each node mentions
// ─────────────────────────────────────────────────────────────────────────────

/// The longest decimal spelling of a `u64` name number.
const U64_DECIMAL_DIGITS: usize = 20;

/// The free-name summary of a node: which names that some binder of the
/// printed DAG binds occur free in the node's text.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Free {
    /// None: the node means the same thing under every binder.
    Closed,
    /// Exactly one, `names[id]`.
    One(u32),
    /// Two or more (or text this printer does not resolve): the node is
    /// bound only where it is used, never moved across any binder.
    Many,
}

impl Free {
    fn join(self, other: Free) -> Free {
        match (self, other) {
            (Free::Closed, f) | (f, Free::Closed) => f,
            (Free::One(a), Free::One(b)) if a == b => Free::One(a),
            _ => Free::Many,
        }
    }

    /// The summary seen from outside a binder of `bound`.
    fn without(self, bound: &[u32]) -> Free {
        match self {
            Free::One(name) if bound.contains(&name) => Free::Closed,
            f => f,
        }
    }
}

/// How the summaries of the reachable nodes are known.
enum FreeMode {
    /// No binder is reachable: every node is `Closed`.
    AllClosed,
    /// Per node.
    Analysed(FxHashMap<u32, Free>),
    /// A binder binds a name this printer does not resolve (its spelling
    /// holds a backslash): every node is `Many`, so nothing is moved across
    /// any binder.
    AllMany,
}

/// What the printer knows about the nodes reachable from its roots.
struct Reach {
    /// The reachable nodes, children before parents, binder bodies included.
    order: Vec<u32>,
    free: FreeMode,
    /// The names each reachable binder binds (ids of the name table).
    binds: FxHashMap<u32, Vec<u32>>,
    /// The number of distinct bound names.
    names: usize,
    /// `dag!<j>_`, fresh for the text being printed.
    prefix: String,
}

impl Reach {
    fn free(&self, node: u32) -> Free {
        match &self.free {
            FreeMode::AllClosed => Free::Closed,
            FreeMode::AllMany => Free::Many,
            FreeMode::Analysed(free) => free.get(&node).copied().unwrap_or(Free::Many),
        }
    }
}

/// The symbol an SMT-LIB token denotes: `|s|` denotes `s`. `None` for a
/// quoted symbol holding a backslash, which readers resolve differently.
fn plain_symbol(token: &str) -> Option<&str> {
    match token.strip_prefix('|').and_then(|t| t.strip_suffix('|')) {
        Some(inner) if inner.contains('\\') => None,
        Some(inner) => Some(inner),
        None => Some(token),
    }
}

/// Which of `names` the SMT-LIB `text` mentions: `Closed` (none), `One` or
/// `Many`. Every symbol token counts, wherever it stands (an operator or a
/// sort spelled like a bound name counts too: over-counting only keeps a
/// node where it is). A quoted symbol holding a backslash, or an
/// unterminated one, is not resolved, and the text counts as `Many`.
fn mentions(text: &str, names: &HashMap<String, u32>) -> Free {
    let bytes = text.as_bytes();
    let delimiter = |b: u8| b.is_ascii_whitespace() || b == b'(' || b == b')';
    let mut free = Free::Closed;
    let mut i = 0;
    while i < bytes.len() {
        if delimiter(bytes[i]) {
            i += 1;
            continue;
        }
        let token = if bytes[i] == b'|' {
            let Some(len) = text[i + 1..].find('|') else {
                return Free::Many;
            };
            let token = &text[i..i + len + 2];
            i += len + 2;
            token
        } else {
            let start = i;
            while i < bytes.len() && !delimiter(bytes[i]) && bytes[i] != b'|' {
                i += 1;
            }
            &text[start..i]
        };
        let Some(symbol) = plain_symbol(token) else {
            return Free::Many;
        };
        if let Some(&id) = names.get(symbol) {
            free = free.join(Free::One(id));
            if free == Free::Many {
                return free;
            }
        }
    }
    free
}

/// Record every `j` such that `dag!<j>_` (decimal `j`, no leading zero)
/// occurs in `text`.
fn block_prefixes(text: &str, blocked: &mut HashSet<u64>) {
    const MARK: &str = "dag!";
    for (at, _) in text.match_indices(MARK) {
        let digits_at = at + MARK.len();
        let run = text[digits_at..]
            .bytes()
            .take_while(u8::is_ascii_digit)
            .count();
        if run == 0 || text.as_bytes().get(digits_at + run) != Some(&b'_') {
            continue;
        }
        let digits = &text[digits_at..digits_at + run];
        if run > 1 && digits.starts_with('0') {
            // Not a canonical decimal: it equals no prefix this printer
            // spells.
            continue;
        }
        // A run too long for a u64 equals no prefix this printer can choose
        // either (it chooses at most the number of blocked values).
        if let Ok(j) = digits.parse::<u64>() {
            blocked.insert(j);
        }
    }
}

/// Collect the nodes reachable from `roots`, their free-name summaries, the
/// names each binder binds, and a fresh name prefix. Work: one rendering of
/// each reachable node's own text (two when a binder is reachable).
fn reach(dag: &FormulaDag, roots: &[u32], stats: &mut PrintStats) -> Reach {
    let mut order: Vec<u32> = Vec::new();
    let mut seen: FxHashSet<u32> = FxHashSet::default();
    let mut stack: Vec<(u32, usize)> = Vec::new();
    let mut own = String::new();
    // Payload-derived keys: randomly keyed, so chosen symbols cannot make
    // the lookups collide.
    let mut blocked: HashSet<u64> = HashSet::new();
    let mut name_ids: HashMap<String, u32> = HashMap::new();
    let mut binds: FxHashMap<u32, Vec<u32>> = FxHashMap::default();
    let mut resolvable = true;
    for &root in roots {
        if !seen.insert(root) {
            continue;
        }
        stack.push((root, 0));
        while let Some(top) = stack.last_mut() {
            let (node, next) = *top;
            if let Some(&kid) = dag.kids_of(node).get(next) {
                top.1 += 1;
                if seen.insert(kid) {
                    stack.push((kid, 0));
                }
                continue;
            }
            stack.pop();
            order.push(node);
            let shell = dag.shell_of(node);
            own.clear();
            // A child slot is a delimiter here, so no token spans one.
            shell.write_smtlib_node(&mut own, &mut |_, out| out.push(' '));
            stats.rendered_bytes += own.len();
            block_prefixes(&own, &mut blocked);
            if let Some(vars) = shell.bound_variables() {
                let mut ids = Vec::with_capacity(vars.len());
                for (symbol, _) in vars {
                    let spelled = escape_smtlib_symbol(symbol.as_str());
                    match plain_symbol(&spelled) {
                        Some(name) => {
                            let fresh = u32::try_from(name_ids.len())
                                .expect("at most 2^32 distinct bound names (the name-id width)");
                            ids.push(*name_ids.entry(name.to_owned()).or_insert(fresh));
                        }
                        None => resolvable = false,
                    }
                }
                binds.insert(node, ids);
            }
        }
    }
    stats.nodes = order.len();
    let mut j = 0u64;
    while blocked.contains(&j) {
        j += 1;
    }
    let prefix = format!("dag!{j}_");

    let free = if binds.is_empty() {
        FreeMode::AllClosed
    } else if !resolvable {
        FreeMode::AllMany
    } else {
        let mut free: FxHashMap<u32, Free> = FxHashMap::default();
        for &node in &order {
            let kids = dag.kids_of(node);
            let summary = if let Some(bound) = binds.get(&node) {
                // A binder: what its body mentions, less the names it binds.
                // Its own text is declarations and sorts, which mention no
                // term.
                kids.iter()
                    .fold(Free::Closed, |f, kid| f.join(free[kid]))
                    .without(bound)
            } else {
                own.clear();
                dag.shell_of(node)
                    .write_smtlib_node(&mut own, &mut |_, out| out.push(' '));
                stats.rendered_bytes += own.len();
                kids.iter()
                    .fold(mentions(&own, &name_ids), |f, kid| f.join(free[kid]))
            };
            free.insert(node, summary);
        }
        FreeMode::Analysed(free)
    };
    Reach {
        order,
        free,
        binds,
        names: name_ids.len(),
        prefix,
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The sharing printer: where each node is spelled
// ─────────────────────────────────────────────────────────────────────────────

/// "No spelling / no region".
const NO: usize = usize::MAX;

/// One node as written in one `let` region.
#[derive(Debug, Clone, Copy)]
struct Spelling {
    node: u32,
    region: usize,
    /// References to it, saturating at 2 (only "two or more" matters).
    refs: u8,
    /// Whether a binding can shorten the text: a compound node, or a leaf
    /// longer than any name.
    bindable: bool,
    /// Its child references: `kid_refs[kids..kids + arity]`, a spelling per
    /// child slot (`NO` for a slot the spelling never prints).
    kids: usize,
    /// The region of its body, for a binder; `NO` otherwise.
    body: usize,
}

/// A `let` region: the top level, or the body of one printed binder.
#[derive(Debug, Clone, Copy)]
struct Region {
    /// The body's root spelling (unused for the top level, whose roots are
    /// `Plan::roots`).
    root: usize,
    /// Its bindings: `Plan::bound[bind_start..bind_end]`, children first.
    bind_start: usize,
    bind_end: usize,
}

/// Where everything is spelled.
struct Plan {
    spellings: Vec<Spelling>,
    kid_refs: Vec<usize>,
    regions: Vec<Region>,
    /// The bound spellings of every region, grouped by region, each group in
    /// post-order (a binding after every binding of its region it uses).
    bound: Vec<usize>,
    /// The spellings of the printed roots (top level).
    roots: Vec<usize>,
}

impl Plan {
    fn is_bound(&self, s: usize) -> bool {
        let spelling = &self.spellings[s];
        spelling.refs >= 2 && spelling.bindable
    }
}

/// The walk that decides every spelling's region and counts its references.
///
/// The DFS carries the binder environment: for each bound name, the stack
/// of open regions that bind it, and the stack of open regions itself. A
/// node's region is decided from its summary at each reference: `Closed`,
/// the top level; `One(k)`, the innermost open region binding `k` (the top
/// level if none); `Many`, the innermost open region. A spelling is
/// expanded once, at its first reference; every later reference only counts.
///
/// Why expanding at the FIRST reference is sound: a spelling's descendants
/// are decided in the environment of that reference, which may hold regions
/// opened below the spelling's own region. Those regions bind no name the
/// spelling mentions (else its region would be one of them), and a
/// descendant outside a nested binder mentions only names the spelling
/// does, so every descendant is decided exactly as in the spelling's own
/// region; a `Many` spelling's region is the innermost one, so nothing lies
/// between.
struct Planner<'a> {
    dag: &'a FormulaDag,
    reach: &'a Reach,
    name_len: usize,
    plan: Plan,
    memo: FxHashMap<(u32, usize), usize>,
    /// Per bound name, the open regions that bind it (innermost last).
    binding: Vec<Vec<usize>>,
    /// The open regions (innermost last); the top level is always open.
    open: Vec<usize>,
    frames: Vec<PlanFrame>,
    /// Per open frame, how many times its spelling prints each child slot.
    mults: Vec<u32>,
    /// Spellings in DFS finish order.
    finish: Vec<usize>,
    own: String,
    stats: PrintStats,
}

#[derive(Debug, Clone, Copy)]
struct PlanFrame {
    spelling: usize,
    next: usize,
    mult_start: usize,
    /// For a binder: whether its body's region is open (and so is popped
    /// when the frame finishes).
    opened: bool,
}

impl<'a> Planner<'a> {
    fn run(dag: &'a FormulaDag, reach: &'a Reach, roots: &[u32], stats: &mut PrintStats) -> Plan {
        let mut planner = Planner {
            dag,
            reach,
            name_len: reach.prefix.len() + U64_DECIMAL_DIGITS,
            plan: Plan {
                spellings: Vec::new(),
                kid_refs: Vec::new(),
                regions: vec![Region {
                    root: NO,
                    bind_start: 0,
                    bind_end: 0,
                }],
                bound: Vec::new(),
                roots: Vec::with_capacity(roots.len()),
            },
            memo: FxHashMap::default(),
            binding: vec![Vec::new(); reach.names],
            open: vec![0],
            frames: Vec::new(),
            mults: Vec::new(),
            finish: Vec::new(),
            own: String::new(),
            stats: PrintStats::default(),
        };
        for &root in roots {
            let s = planner.visit(root, 1);
            planner.plan.roots.push(s);
            planner.drain();
        }
        planner.group_bindings();
        let mut plan = planner.plan;
        stats.spellings = plan.spellings.len();
        stats.regions = plan.regions.len();
        stats.bindings = plan.bound.len();
        stats.references += planner.stats.references;
        stats.rendered_bytes += planner.stats.rendered_bytes;
        plan.kid_refs.shrink_to_fit();
        plan
    }

    fn region_of(&self, node: u32) -> usize {
        match self.reach.free(node) {
            Free::Closed => 0,
            Free::One(name) => self.binding[name as usize].last().copied().unwrap_or(0),
            Free::Many => *self.open.last().expect("the top level is always open"),
        }
    }

    /// One reference (printed `mult` times) to `node` from where the walk
    /// stands: count it, and open its spelling if this is the first.
    fn visit(&mut self, node: u32, mult: u32) -> usize {
        let region = self.region_of(node);
        let add = u8::try_from(mult).unwrap_or(u8::MAX);
        match self.memo.entry((node, region)) {
            Entry::Occupied(seen) => {
                let s = *seen.get();
                let spelling = &mut self.plan.spellings[s];
                spelling.refs = spelling.refs.saturating_add(add).min(2);
                s
            }
            Entry::Vacant(slot) => {
                let s = self.plan.spellings.len();
                slot.insert(s);
                let shell = self.dag.shell_of(node);
                let arity = shell.arity();
                let mult_start = self.mults.len();
                self.mults.resize(mult_start + arity, 0);
                self.own.clear();
                let mults = &mut self.mults;
                shell.write_smtlib_node(&mut self.own, &mut |i, out| {
                    mults[mult_start + i] += 1;
                    out.push(' ');
                });
                self.stats.rendered_bytes += self.own.len();
                let kids = self.plan.kid_refs.len();
                self.plan.kid_refs.resize(kids + arity, NO);
                self.plan.spellings.push(Spelling {
                    node,
                    region,
                    refs: add.min(2),
                    bindable: arity > 0 || self.own.len() > self.name_len,
                    kids,
                    body: NO,
                });
                self.frames.push(PlanFrame {
                    spelling: s,
                    next: 0,
                    mult_start,
                    opened: false,
                });
                s
            }
        }
    }

    /// Run the DFS until every opened spelling has finished.
    fn drain(&mut self) {
        while let Some(&frame) = self.frames.last() {
            let spelling = self.plan.spellings[frame.spelling];
            let kids = self.dag.kids_of(spelling.node);
            if frame.next >= kids.len() {
                self.frames.pop();
                if frame.opened {
                    if let Some(bound) = self.reach.binds.get(&spelling.node) {
                        for &name in bound {
                            self.binding[name as usize].pop();
                        }
                    }
                    self.open.pop();
                }
                self.mults.truncate(frame.mult_start);
                self.finish.push(frame.spelling);
                continue;
            }
            let slot = frame.next;
            let mult = self.mults[frame.mult_start + slot];
            let kid = kids[slot];
            if let Some(top) = self.frames.last_mut() {
                top.next += 1;
            }
            if mult == 0 {
                continue;
            }
            self.stats.references += 1;
            if let Some(bound) = self.reach.binds.get(&spelling.node) {
                assert!(
                    kids.len() == 1,
                    "a binder has exactly one child, its body (the sharing printer \
                     opens one region per binder)"
                );
                // Open the body's region: its names now denote its variables.
                let region = self.plan.regions.len();
                self.plan.regions.push(Region {
                    root: NO,
                    bind_start: 0,
                    bind_end: 0,
                });
                self.plan.spellings[frame.spelling].body = region;
                for &name in bound {
                    self.binding[name as usize].push(region);
                }
                self.open.push(region);
                if let Some(top) = self.frames.last_mut() {
                    top.opened = true;
                }
                let s = self.visit(kid, mult);
                self.plan.regions[region].root = s;
                self.plan.kid_refs[spelling.kids + slot] = s;
            } else {
                let s = self.visit(kid, mult);
                self.plan.kid_refs[spelling.kids + slot] = s;
            }
        }
    }

    /// Group the bound spellings by region (a counting sort that keeps the
    /// finish order within a region).
    fn group_bindings(&mut self) {
        let plan = &mut self.plan;
        let mut count = vec![0usize; plan.regions.len()];
        for &s in &self.finish {
            if plan.is_bound(s) {
                count[plan.spellings[s].region] += 1;
            }
        }
        let mut next = Vec::with_capacity(count.len());
        let mut total = 0;
        for (region, n) in plan.regions.iter_mut().zip(&count) {
            region.bind_start = total;
            next.push(total);
            total += n;
            region.bind_end = total;
        }
        plan.bound = vec![NO; total];
        for &s in &self.finish {
            if plan.is_bound(s) {
                let region = plan.spellings[s].region;
                plan.bound[next[region]] = s;
                next[region] += 1;
            }
        }
    }
}

/// The `let` level of every bound spelling (1 = it uses no binding of its
/// own region; otherwise one more than the deepest binding of its own region
/// its text uses, binder bodies inside it included). 0 for the rest.
///
/// A walk of the text structure without the text: while a binding's text is
/// walked it is its region's ACTIVE binding (a region has at most one, as
/// its bindings are written one after another), and every reference to a
/// bound spelling raises the active binding of that spelling's region.
fn levels(dag: &FormulaDag, plan: &Plan) -> Vec<u32> {
    enum Step {
        Region {
            region: usize,
            next_binding: usize,
            next_root: usize,
        },
        EndBinding {
            binding: usize,
            region: usize,
        },
        Spell {
            spelling: usize,
            next: usize,
        },
    }
    let mut level = vec![0u32; plan.spellings.len()];
    let mut active = vec![NO; plan.regions.len()];
    let mut stack = vec![Step::Region {
        region: 0,
        next_binding: 0,
        next_root: 0,
    }];
    // A reference: raise the active binding of a bound spelling's region,
    // or walk an unbound spelling's text.
    let reference = |s: usize, level: &mut [u32], active: &[usize], stack: &mut Vec<Step>| {
        if plan.is_bound(s) {
            let user = active[plan.spellings[s].region];
            if user != NO {
                level[user] = level[user].max(level[s]);
            }
        } else {
            stack.push(Step::Spell {
                spelling: s,
                next: 0,
            });
        }
    };
    while let Some(step) = stack.last_mut() {
        match step {
            Step::Region {
                region,
                next_binding,
                next_root,
            } => {
                let r = *region;
                let reg = plan.regions[r];
                if reg.bind_start + *next_binding < reg.bind_end {
                    let b = plan.bound[reg.bind_start + *next_binding];
                    *next_binding += 1;
                    active[r] = b;
                    stack.push(Step::EndBinding {
                        binding: b,
                        region: r,
                    });
                    stack.push(Step::Spell {
                        spelling: b,
                        next: 0,
                    });
                } else {
                    let roots: &[usize] = if r == 0 {
                        &plan.roots
                    } else {
                        std::slice::from_ref(&plan.regions[r].root)
                    };
                    if let Some(&s) = roots.get(*next_root) {
                        *next_root += 1;
                        reference(s, &mut level, &active, &mut stack);
                    } else {
                        stack.pop();
                    }
                }
            }
            Step::EndBinding { binding, region } => {
                let (b, r) = (*binding, *region);
                level[b] += 1;
                active[r] = NO;
                stack.pop();
            }
            Step::Spell { spelling, next } => {
                let s = *spelling;
                let sp = plan.spellings[s];
                let arity = dag.shell_of(sp.node).arity();
                if *next >= arity {
                    stack.pop();
                    continue;
                }
                let slot = *next;
                *next += 1;
                let kid = plan.kid_refs[sp.kids + slot];
                if kid == NO {
                    continue;
                }
                if sp.body == NO {
                    reference(kid, &mut level, &active, &mut stack);
                } else {
                    stack.push(Step::Region {
                        region: sp.body,
                        next_binding: 0,
                        next_root: 0,
                    });
                }
            }
        }
    }
    level
}

// ─────────────────────────────────────────────────────────────────────────────
// The sharing printer: the text
// ─────────────────────────────────────────────────────────────────────────────

/// How one child slot of a rendered spelling is filled.
#[derive(Debug, Clone, Copy)]
enum Slot {
    /// Print the child spelling's own text here.
    Inline(usize),
    /// Print a region here: the body of a binder.
    Enter(usize),
}

/// A spelling being printed: its own text in the text arena, and the child
/// slots in the slot arena still to be filled.
#[derive(Debug, Clone, Copy)]
struct NodeFrame {
    text_start: usize,
    text_end: usize,
    emitted: usize,
    slot_start: usize,
    slot_next: usize,
    slot_end: usize,
}

/// Where a region's printing stands.
#[derive(Debug, Clone, Copy)]
enum Phase {
    /// About to open `let` group `group` (or, past the last group, the body).
    Open { group: usize },
    /// About to print binding `at` of group `group` (or close the group).
    Member { group: usize, at: usize },
    /// Binding `at`'s defining term has been printed; close its pair.
    AfterMember { group: usize, at: usize },
    /// About to print the region's root.
    Body,
    /// About to close every group.
    Close,
}

/// A `let` region being printed: its bindings grouped by level (group `g` is
/// `order[group_end[g-1]..group_end[g]]`), then its root, then one `)` per
/// group.
#[derive(Debug)]
struct RegionTask {
    region: usize,
    order: Vec<usize>,
    group_end: Vec<usize>,
    phase: Phase,
}

#[derive(Debug)]
enum Task {
    Node(NodeFrame),
    /// Boxed: a region is opened once per binder, a node frame once per
    /// spelling, so the common frame stays small.
    Region(Box<RegionTask>),
}

struct Emitter<'p> {
    dag: &'p FormulaDag,
    plan: &'p Plan,
    level: &'p [u32],
    prefix: &'p str,
    /// The name number of each bound spelling, once its binding is written.
    names: Vec<u64>,
    next_name: u64,
    /// Own texts of the node frames on the stack.
    text: String,
    /// Child slots of the node frames on the stack: (position in `text`,
    /// how to fill it).
    slots: Vec<(usize, Slot)>,
    rendered: usize,
}

impl<'p> Emitter<'p> {
    fn new(dag: &'p FormulaDag, plan: &'p Plan, level: &'p [u32], prefix: &'p str) -> Emitter<'p> {
        Emitter {
            dag,
            plan,
            level,
            prefix,
            names: vec![u64::MAX; plan.spellings.len()],
            next_name: 0,
            text: String::new(),
            slots: Vec::new(),
            rendered: 0,
        }
    }

    /// Give bound spelling `s` the next name and write it.
    fn bind_name(&mut self, s: usize, out: &mut String) {
        self.names[s] = self.next_name;
        self.next_name += 1;
        self.write_name(s, out);
    }

    fn write_name(&self, s: usize, out: &mut String) {
        write_name(out, self.prefix, self.names[s]);
    }

    /// The task that prints region `r`: its bindings grouped by level with a
    /// counting sort (post-order kept within a level), so the cost is linear
    /// in the bindings plus the number of levels.
    fn region_task(&self, r: usize) -> RegionTask {
        let reg = self.plan.regions[r];
        let bindings = &self.plan.bound[reg.bind_start..reg.bind_end];
        let depth = bindings
            .iter()
            .map(|&b| self.level[b] as usize)
            .max()
            .unwrap_or(0);
        let mut group_end = vec![0usize; depth];
        for &b in bindings {
            group_end[self.level[b] as usize - 1] += 1;
        }
        let mut next_at = Vec::with_capacity(depth);
        let mut total = 0;
        for end in &mut group_end {
            next_at.push(total);
            total += *end;
            *end = total;
        }
        let mut order = vec![NO; total];
        for &b in bindings {
            let g = self.level[b] as usize - 1;
            order[next_at[g]] = b;
            next_at[g] += 1;
        }
        RegionTask {
            region: r,
            order,
            group_end,
            phase: Phase::Open { group: 0 },
        }
    }

    /// Render spelling `s`'s own text into the text arena, resolving each
    /// child slot, and return its frame.
    fn node_task(&mut self, s: usize) -> Task {
        let plan = self.plan;
        let spelling = plan.spellings[s];
        let shell = self.dag.shell_of(spelling.node);
        let kid_refs = &plan.kid_refs[spelling.kids..spelling.kids + shell.arity()];
        let text_start = self.text.len();
        let slot_start = self.slots.len();
        let (names, prefix, slots) = (&self.names, self.prefix, &mut self.slots);
        shell.write_smtlib_node(&mut self.text, &mut |i, out| {
            let kid = kid_refs[i];
            if spelling.body != NO {
                slots.push((out.len(), Slot::Enter(spelling.body)));
            } else if plan.is_bound(kid) {
                assert!(
                    names[kid] != u64::MAX,
                    "a binding is written before every use of its name"
                );
                write_name(out, prefix, names[kid]);
            } else {
                slots.push((out.len(), Slot::Inline(kid)));
            }
        });
        self.rendered += self.text.len() - text_start;
        Task::Node(NodeFrame {
            text_start,
            text_end: self.text.len(),
            emitted: text_start,
            slot_start,
            slot_next: slot_start,
            slot_end: self.slots.len(),
        })
    }

    /// Run the task stack to completion, appending the text to `out`.
    fn run(&mut self, mut stack: Vec<Task>, out: &mut String) {
        while let Some(task) = stack.last_mut() {
            match task {
                Task::Node(frame) => {
                    if frame.slot_next < frame.slot_end {
                        let (pos, slot) = self.slots[frame.slot_next];
                        frame.slot_next += 1;
                        out.push_str(&self.text[frame.emitted..pos]);
                        frame.emitted = pos;
                        let next = match slot {
                            Slot::Inline(kid) => self.node_task(kid),
                            Slot::Enter(region) => Task::Region(Box::new(self.region_task(region))),
                        };
                        stack.push(next);
                    } else {
                        out.push_str(&self.text[frame.emitted..frame.text_end]);
                        let (text_start, slot_start) = (frame.text_start, frame.slot_start);
                        stack.pop();
                        self.text.truncate(text_start);
                        self.slots.truncate(slot_start);
                    }
                }
                Task::Region(task) => match task.phase {
                    Phase::Open { group } => {
                        if group < task.group_end.len() {
                            out.push_str("(let (");
                            let at = if group == 0 {
                                0
                            } else {
                                task.group_end[group - 1]
                            };
                            task.phase = Phase::Member { group, at };
                        } else {
                            task.phase = Phase::Body;
                        }
                    }
                    Phase::Member { group, at } => {
                        if at < task.group_end[group] {
                            let group_start = if group == 0 {
                                0
                            } else {
                                task.group_end[group - 1]
                            };
                            if at > group_start {
                                out.push(' ');
                            }
                            let b = task.order[at];
                            out.push('(');
                            self.bind_name(b, out);
                            out.push(' ');
                            task.phase = Phase::AfterMember { group, at };
                            // The defining term: the spelling's own text.
                            let next = self.node_task(b);
                            stack.push(next);
                        } else {
                            out.push_str(") ");
                            task.phase = Phase::Open { group: group + 1 };
                        }
                    }
                    Phase::AfterMember { group, at } => {
                        out.push(')');
                        task.phase = Phase::Member { group, at: at + 1 };
                    }
                    Phase::Body => {
                        task.phase = Phase::Close;
                        let root = if task.region == 0 {
                            self.plan.roots[0]
                        } else {
                            self.plan.regions[task.region].root
                        };
                        if self.plan.is_bound(root) {
                            self.write_name(root, out);
                        } else {
                            let next = self.node_task(root);
                            stack.push(next);
                        }
                    }
                    Phase::Close => {
                        for _ in 0..task.group_end.len() {
                            out.push(')');
                        }
                        stack.pop();
                    }
                },
            }
        }
    }
}

fn write_name(out: &mut String, prefix: &str, name: u64) {
    out.push_str(prefix);
    out.push_str(&name.to_string());
}

// ─────────────────────────────────────────────────────────────────────────────
// Sorts, for `define-fun` headers
// ─────────────────────────────────────────────────────────────────────────────

/// Where a node's sort comes from.
enum SortOf<'s> {
    Unknown,
    /// A sort the node's own payload carries.
    Payload(&'s Sort),
    /// A sort built from the node's payload.
    Fresh(Sort),
    /// The sort of child `i`.
    Kid(usize),
    /// The element sort of child `i`'s array sort.
    ElemOfKid(usize),
}

/// The sorts of the reachable nodes, interned: a node's sort is an index
/// into `sorts`, so a sort that propagates through many nodes is stored once.
struct Sorts {
    sorts: Vec<Sort>,
    index: FxHashMap<Sort, usize>,
    of_node: FxHashMap<u32, usize>,
    elem_of: FxHashMap<usize, Option<usize>>,
}

impl Sorts {
    fn intern(&mut self, sort: &Sort) -> usize {
        if let Some(&id) = self.index.get(sort) {
            return id;
        }
        let id = self.sorts.len();
        self.sorts.push(sort.clone());
        self.index.insert(sort.clone(), id);
        id
    }

    fn elem(&mut self, array: usize) -> Option<usize> {
        if let Some(&elem) = self.elem_of.get(&array) {
            return elem;
        }
        let elem = match &self.sorts[array] {
            Sort::Array(_, elem) => {
                let elem = (**elem).clone();
                Some(self.intern(&elem))
            }
            _ => None,
        };
        self.elem_of.insert(array, elem);
        elem
    }

    fn get(&self, node: u32) -> Option<&Sort> {
        self.of_node.get(&node).map(|&id| &self.sorts[id])
    }
}

/// Infer the sort of every node of `order` (post-order, so children first).
fn infer_sorts(dag: &FormulaDag, order: &[u32]) -> Sorts {
    let mut table = Sorts {
        sorts: Vec::new(),
        index: FxHashMap::default(),
        of_node: FxHashMap::default(),
        elem_of: FxHashMap::default(),
    };
    for &node in order {
        let kids = dag.kids_of(node);
        let shell = &dag.shell_of(node).node;
        let of = {
            let kid_sort = |i: usize| -> Option<&Sort> { kids.get(i).and_then(|k| table.get(*k)) };
            sort_of(shell, &kid_sort)
        };
        let id = match of {
            SortOf::Unknown => None,
            SortOf::Payload(sort) => Some(table.intern(sort)),
            SortOf::Fresh(sort) => Some(table.intern(&sort)),
            SortOf::Kid(i) => kids.get(i).and_then(|k| table.of_node.get(k).copied()),
            SortOf::ElemOfKid(i) => kids
                .get(i)
                .and_then(|k| table.of_node.get(k).copied())
                .and_then(|array| table.elem(array)),
        };
        if let Some(id) = id {
            table.of_node.insert(node, id);
        }
    }
    table
}

/// The result sort of a node from its shell and its children's sorts.
///
/// Not trusted, and conservative: a sort-generic operator (`+ - *`, the FP
/// arithmetic, `ite`) takes its operands' sort only when every operand
/// whose sort is known has the SAME sort; operands of two different sorts
/// (`Int` and `Real`) give `Unknown`, so the `define-fun` is refused
/// (`DagError::UnsortedDefinition`) rather than declared with a sort one
/// solver coerces to and another refuses. Exhaustive (no wildcard), so a
/// new variant cannot compile until it states its sort.
#[allow(clippy::too_many_lines)] // one arm per variant, by design
fn sort_of<'s, 'k>(shell: &'s Formula, kid: &dyn Fn(usize) -> Option<&'k Sort>) -> SortOf<'s> {
    // The sort of `slots`, when every known one agrees.
    let agreed = |slots: &[usize]| -> SortOf<'s> {
        let mut found: Option<(usize, &Sort)> = None;
        for &i in slots {
            if let Some(sort) = kid(i) {
                match found {
                    None => found = Some((i, sort)),
                    Some((_, first)) if first != sort => return SortOf::Unknown,
                    Some(_) => {}
                }
            }
        }
        found.map_or(SortOf::Unknown, |(i, _)| SortOf::Kid(i))
    };
    let bv_width = |i: usize| -> Option<u32> {
        match kid(i) {
            Some(Sort::BitVec(w)) => Some(*w),
            _ => None,
        }
    };
    let fresh_bv = |w: Option<u32>| w.map_or(SortOf::Unknown, |w| SortOf::Fresh(Sort::BitVec(w)));
    match shell {
        Formula::Bool(_) => SortOf::Fresh(Sort::Bool),
        Formula::Int(_) | Formula::UInt(_) => SortOf::Fresh(Sort::Int),
        Formula::BitVec { width, .. } => SortOf::Fresh(Sort::BitVec(*width)),
        Formula::Var(_, sort) | Formula::SymVar(_, sort) => SortOf::Payload(sort),
        Formula::Rat(_) => SortOf::Fresh(Sort::Real),

        Formula::Not(_)
        | Formula::And(_)
        | Formula::Or(_)
        | Formula::Implies(..)
        | Formula::Eq(..)
        | Formula::Lt(..)
        | Formula::Le(..)
        | Formula::Gt(..)
        | Formula::Ge(..)
        | Formula::BvULt(..)
        | Formula::BvULe(..)
        | Formula::BvSLt(..)
        | Formula::BvSLe(..)
        | Formula::FpEq(..)
        | Formula::FpLt(..)
        | Formula::FpLe(..)
        | Formula::FpGt(..)
        | Formula::FpGe(..)
        | Formula::FpIsNaN(_)
        | Formula::FpIsInfinite(_)
        | Formula::FpIsZero(_)
        | Formula::FpIsNormal(_)
        | Formula::FpIsSubnormal(_)
        | Formula::FpIsNegative(_)
        | Formula::FpIsPositive(_)
        | Formula::Forall(..)
        | Formula::Exists(..)
        | Formula::Pred(..)
        | Formula::IsCtor { .. } => SortOf::Fresh(Sort::Bool),

        // `+ - *` are sort-generic over Int and Real; `div`/`mod` (the
        // truncating spellings) are Int.
        Formula::Add(..) | Formula::Sub(..) | Formula::Mul(..) => agreed(&[0, 1]),
        Formula::Neg(_) => SortOf::Kid(0),
        Formula::Div(..) | Formula::Rem(..) | Formula::BvToInt(..) => SortOf::Fresh(Sort::Int),

        Formula::BvAdd(_, _, w)
        | Formula::BvSub(_, _, w)
        | Formula::BvMul(_, _, w)
        | Formula::BvUDiv(_, _, w)
        | Formula::BvSDiv(_, _, w)
        | Formula::BvURem(_, _, w)
        | Formula::BvSRem(_, _, w)
        | Formula::BvAnd(_, _, w)
        | Formula::BvOr(_, _, w)
        | Formula::BvXor(_, _, w)
        | Formula::BvNot(_, w)
        | Formula::BvShl(_, _, w)
        | Formula::BvLShr(_, _, w)
        | Formula::BvAShr(_, _, w)
        | Formula::IntToBv(_, w) => SortOf::Fresh(Sort::BitVec(*w)),
        Formula::BvExtract { high, low, .. } => {
            fresh_bv(high.checked_sub(*low).and_then(|span| span.checked_add(1)))
        }
        Formula::BvConcat(..) => fresh_bv(
            bv_width(0)
                .zip(bv_width(1))
                .and_then(|(a, b)| a.checked_add(b)),
        ),
        Formula::BvZeroExt(_, bits) | Formula::BvSignExt(_, bits) => {
            fresh_bv(bv_width(0).and_then(|w| w.checked_add(*bits)))
        }

        Formula::FpConst { eb, sb, .. }
        | Formula::FpNaN { eb, sb }
        | Formula::FpInf { eb, sb, .. }
        | Formula::FpZero { eb, sb, .. }
        | Formula::FpFromBits { eb, sb, .. }
        | Formula::FpFromSbv { eb, sb, .. }
        | Formula::FpFromUbv { eb, sb, .. }
        | Formula::FpConvert { eb, sb, .. } => SortOf::Fresh(Sort::Float { eb: *eb, sb: *sb }),
        Formula::FpRoundingMode(_) => SortOf::Fresh(Sort::RoundingMode),
        // Child 0 is the rounding mode.
        Formula::FpAdd(..) | Formula::FpSub(..) | Formula::FpMul(..) | Formula::FpDiv(..) => {
            agreed(&[1, 2])
        }
        Formula::FpFma(..) => agreed(&[1, 2, 3]),
        Formula::FpSqrt(..) => SortOf::Kid(1),
        Formula::FpRem(..) | Formula::FpMin(..) | Formula::FpMax(..) => agreed(&[0, 1]),
        Formula::FpNeg(_) | Formula::FpAbs(_) => SortOf::Kid(0),
        Formula::FpToSbv { width, .. } | Formula::FpToUbv { width, .. } => {
            SortOf::Fresh(Sort::BitVec(*width))
        }
        Formula::FpToIeeeBv(_) => match kid(0) {
            Some(Sort::Float { eb, sb }) => fresh_bv(eb.checked_add(*sb)),
            _ => SortOf::Unknown,
        },

        Formula::Ite(..) => agreed(&[1, 2]),
        Formula::Select(..) => SortOf::ElemOfKid(0),
        Formula::Store(..) => SortOf::Kid(0),

        Formula::Ctor { sort, .. } | Formula::FnApp { sort, .. } => SortOf::Payload(sort),
        Formula::Sel { field_sort, .. } => SortOf::Payload(field_sort),
        Formula::ConstArray {
            index_sort,
            elem_sort,
            ..
        } => SortOf::Fresh(Sort::Array(
            Box::new(index_sort.clone()),
            Box::new(elem_sort.clone()),
        )),
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Unit tests: what only the crate can reach
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::formula_census::witnesses;

    fn bx(f: Formula) -> Box<Formula> {
        Box::new(f)
    }

    fn bvar(name: &str) -> Formula {
        Formula::Var(name.into(), Sort::Bool)
    }

    /// A DAG whose every hash is 0: each lookup scans every candidate, so
    /// identity rests on the exact comparisons alone.
    fn colliding() -> FormulaDag {
        let mut dag = FormulaDag::new();
        dag.collide = true;
        dag
    }

    /// Formulas that differ only in a child, only in the payload, only in
    /// the order or number of children, plus every variant's witness and
    /// each witness used in a compound.
    fn identity_corpus() -> Vec<Formula> {
        let (p, q) = (bvar("p"), bvar("q"));
        let mut corpus = vec![
            Formula::Not(bx(p.clone())),
            Formula::Not(bx(q.clone())),
            Formula::And(vec![p.clone(), q.clone()]),
            Formula::And(vec![q.clone(), p.clone()]),
            Formula::And(vec![p.clone()]),
            Formula::And(vec![p.clone(), p.clone()]),
            Formula::And(vec![]),
            Formula::Or(vec![p.clone(), q.clone()]),
            Formula::Or(vec![]),
            Formula::Implies(bx(p.clone()), bx(q.clone())),
            Formula::Implies(bx(q.clone()), bx(p.clone())),
            Formula::BvAdd(
                bx(Formula::Var("a".into(), Sort::BitVec(8))),
                bx(Formula::Var("a".into(), Sort::BitVec(8))),
                8,
            ),
            Formula::BvAdd(
                bx(Formula::Var("a".into(), Sort::BitVec(8))),
                bx(Formula::Var("a".into(), Sort::BitVec(8))),
                16,
            ),
        ];
        for w in witnesses() {
            corpus.push(Formula::Eq(bx(w.clone()), bx(w.clone())));
            corpus.push(Formula::Ite(bx(p.clone()), bx(w.clone()), bx(w.clone())));
            corpus.push(w);
        }
        corpus
    }

    /// With every hash colliding, tree -> DAG -> tree is still the identity,
    /// two formulas share an id exactly when they are equal, and the node and
    /// shell counts are those of a DAG with a working hash. A refactor that
    /// let the hash decide identity (dropping the child or the shell
    /// comparison) fails here.
    #[test]
    fn identity_is_exact_when_every_hash_collides() {
        let corpus = identity_corpus();
        let mut dag = colliding();
        let ids: Vec<NodeId> = corpus.iter().map(|f| dag.intern(f)).collect();
        for (f, &id) in corpus.iter().zip(&ids) {
            assert_eq!(dag.expand(id), *f, "round trip under collisions");
            assert_eq!(dag.intern_owned(f.clone()), id, "owned interning");
        }
        for i in 0..corpus.len() {
            for j in 0..corpus.len() {
                assert_eq!(
                    ids[i] == ids[j],
                    corpus[i] == corpus[j],
                    "identity of {:?} and {:?}",
                    corpus[i],
                    corpus[j]
                );
            }
        }
        let mut plain = FormulaDag::new();
        for f in &corpus {
            plain.intern(f);
        }
        assert_eq!(dag.len(), plain.len());
        assert_eq!(dag.shell_count(), plain.shell_count());
        assert_eq!(dag.edge_count(), plain.edge_count());

        // `get` and `mk` under collisions.
        let p = dag.intern(&bvar("p"));
        let q = dag.intern(&bvar("q"));
        let not = Shell::of(&Formula::Not(bx(Formula::Bool(true))));
        let not_p = dag.get(&not, &[p]).expect("Not(p) is held");
        let not_q = dag.get(&not, &[q]).expect("Not(q) is held");
        assert_ne!(not_p, not_q);
        assert_eq!(dag.mk(not.clone(), &[q]), Ok(not_q));
        assert_eq!(dag.expand(not_q), Formula::Not(bx(bvar("q"))));
    }

    /// A forged candidate: the bucket for the hash of Not(q) already holds
    /// Not(p) (and, so the `Many` bucket path runs, p). Exact comparison
    /// rejects both.
    #[test]
    fn forged_node_collision_is_rejected_by_exact_equality() {
        let mut dag = FormulaDag::new();
        let p = dag.intern(&bvar("p"));
        let q = dag.intern(&bvar("q"));
        let not_p = dag.intern(&Formula::Not(bx(bvar("p"))));
        let sid = dag.nodes[not_p.index()].shell;
        let forged = dag.node_hash(sid, &[q.index]);
        dag.node_index.insert(forged, not_p.index);
        dag.node_index.insert(forged, p.index);
        let not_q = dag.intern(&Formula::Not(bx(bvar("q"))));
        assert_ne!(
            not_q, not_p,
            "a hash collision conflated Not(q) with Not(p)"
        );
        assert_eq!(dag.expand(not_q), Formula::Not(bx(bvar("q"))));
        assert_eq!(dag.intern(&Formula::Not(bx(bvar("q")))), not_q);
    }

    /// A forged shell candidate: the bucket for the hash of q's shell holds
    /// p's shell. Exact comparison rejects it.
    #[test]
    fn forged_shell_collision_is_rejected_by_exact_equality() {
        let mut dag = FormulaDag::new();
        let p = dag.intern(&bvar("p"));
        let sid_p = dag.nodes[p.index()].shell;
        let forged = dag.shell_hash(&Shell::of(&bvar("q")));
        dag.shell_index.insert(forged, sid_p);
        let q = dag.intern(&bvar("q"));
        assert_ne!(q, p, "a shell hash collision conflated q with p");
        assert_eq!(dag.expand(q), bvar("q"));
    }

    /// A shell is filled with exactly its arity of children: a missing one
    /// never becomes the placeholder, a surplus one is never dropped.
    #[test]
    #[should_panic(expected = "fewer children than the shell's arity")]
    fn fill_children_refuses_a_missing_child() {
        let shell = Shell::of(&Formula::Implies(bx(bvar("p")), bx(bvar("q"))));
        let _ = shell.node.clone().fill_children(vec![bvar("p")]);
    }

    #[test]
    #[should_panic(expected = "3 children for a shell of arity 2")]
    fn fill_children_refuses_a_surplus_child() {
        let shell = Shell::of(&Formula::Implies(bx(bvar("p")), bx(bvar("q"))));
        let _ = shell
            .node
            .clone()
            .fill_children(vec![bvar("p"), bvar("q"), bvar("r")]);
    }

    #[test]
    #[should_panic(expected = "an n-ary shell holds no child list")]
    fn fill_children_refuses_a_node_that_is_not_a_shell() {
        let full = Formula::And(vec![bvar("p")]);
        let _ = full.fill_children(vec![bvar("q")]);
    }

    /// An n-ary shell holds its payload only: no placeholder per child.
    #[test]
    fn nary_shells_hold_no_placeholders() {
        for n in [0usize, 1, 7, 1000] {
            let wide = Formula::And(vec![bvar("p"); n]);
            let shell = Shell::of(&wide);
            assert_eq!(shell.arity(), n);
            assert_eq!(shell.node, Formula::And(Vec::new()));
            assert_eq!(Shell::split(wide.clone()).0, shell);
            assert_eq!(shell.rebuild(vec![bvar("p"); n]), Ok(wide));
        }
    }

    /// The fresh prefix ignores digit runs that no canonical `dag!<j>_` can
    /// equal, and takes the smallest free `j`.
    #[test]
    fn block_prefixes_reads_canonical_runs() {
        let mut blocked = HashSet::new();
        block_prefixes(
            "dag!0_1 |dag!1_x| dag!007_ dag!3 dag!4x dag!99999999999999999999999_ dag!_",
            &mut blocked,
        );
        let mut got: Vec<u64> = blocked.into_iter().collect();
        got.sort_unstable();
        assert_eq!(got, [0, 1]);
    }

    /// The lexer resolves quoted symbols and refuses to guess at escapes.
    #[test]
    fn mentions_resolves_tokens() {
        let names: HashMap<String, u32> = [("k".to_owned(), 0), ("a b".to_owned(), 1)]
            .into_iter()
            .collect();
        assert_eq!(mentions("(+ x 1)", &names), Free::Closed);
        assert_eq!(mentions("(+ k 1)", &names), Free::One(0));
        assert_eq!(mentions("(+ |k| k)", &names), Free::One(0));
        assert_eq!(mentions("(+ |a b| 1)", &names), Free::One(1));
        assert_eq!(mentions("(+ |a b| k)", &names), Free::Many);
        assert_eq!(mentions("(+ kk k1 xk)", &names), Free::Closed);
        assert_eq!(mentions("(f |a\\|b|)", &names), Free::Many);
        assert_eq!(mentions("(f |unterminated", &names), Free::Many);
    }
}

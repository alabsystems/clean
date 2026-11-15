// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The reference interpreter's array, vector, sequence and set VALUE: a
//! persistent rope ([`super::rope`]) of element values, so a collection costs
//! space proportional to how it was BUILT, never to its length.
//!
//! * `ArraySplat` / `Constant::Splat` of any length is one uniform node.
//! * A load of memory holding a stored splat, or a copy of one, is decoded
//!   STRUCTURALLY ([`super::rope::Rope::chunk_map`]): a repeating run of
//!   memory becomes a repeating run of values, whatever the element type it
//!   is read at.
//! * `ExtractElement` walks one root-to-leaf path: O(height).
//! * `InsertElement` copies that one path and shares every other node with
//!   the input (which SSA keeps alive): it never clones the array.
//! * A dense array (`MakeAggregate`, `Constant::Array`, a literal load) is
//!   built in O(n), its elements MOVED into literal leaves of at most 16.
//!
//! Equality is SEMANTIC (element-wise), decided structurally wherever the
//! two ropes' shapes agree, so two spellings of one array compare equal
//! whatever their shapes.

use super::rope::{Rope, RopeElem};
use super::{InterpretValue, InterpretValueKind};

/// A persistent 16-element literal leaf: a `set` copies at most this many.
const LEAF: usize = 16;

impl RopeElem for InterpretValue {
    const FRESH_LEAF: usize = LEAF;

    /// Certainly-equal, cheaply: scalars by value, arrays and vectors by node
    /// identity, tensors by extents and element-node identity, aggregates
    /// field by field. Never a deep array comparison.
    fn same(&self, other: &Self) -> bool {
        use InterpretValueKind as K;
        if self.ty != other.ty {
            return false;
        }
        match (&self.kind, &other.kind) {
            (K::Int(a), K::Int(b)) => a == b,
            (K::FloatBits(a), K::FloatBits(b)) => a == b,
            (K::Bool(a), K::Bool(b)) => a == b,
            (K::Ptr(a), K::Ptr(b)) => a == b,
            (K::DanglingPtr(a), K::DanglingPtr(b)) => a == b,
            (K::FnDef(a), K::FnDef(b)) => a == b,
            (K::NullPtr, K::NullPtr) | (K::Unit, K::Unit) | (K::PhantomData, K::PhantomData) => {
                true
            }
            (K::Array(a), K::Array(b))
            | (K::Vector(a), K::Vector(b))
            | (K::Sequence(a), K::Sequence(b))
            | (K::Set(a), K::Set(b)) => a.ptr_eq(b),
            (K::Tensor { dims: a, elems: x }, K::Tensor { dims: b, elems: y }) => {
                a == b && x.ptr_eq(y)
            }
            (K::Aggregate(a), K::Aggregate(b)) => {
                a.len() == b.len() && a.iter().zip(b).all(|(x, y)| x.same(y))
            }
            (
                K::FatPtr {
                    data: a,
                    metadata: m,
                },
                K::FatPtr {
                    data: b,
                    metadata: n,
                },
            ) => a.same(b) && m.same(n),
            _ => false,
        }
    }
}

/// A borrowed compact observation of an array's stored graph. Nodes are
/// topologically ordered and sharing is explicit; there is no per-element walk.
#[derive(Debug)]
pub struct ArrayStructure<'a> {
    pub nodes: Vec<ArrayStructureNode<'a>>,
    pub root: Option<usize>,
    /// One identity per node, aligned with `nodes`. Shared nodes keep their
    /// identity across snapshots of different arrays that borrow the same DAG.
    pub identities: Vec<ArrayStructureId<'a>>,
}

/// Opaque identity of a stored array node, tied to the source borrow. Equality
/// means sharing, not element-wise equivalence. This is not a portable or
/// serialized identifier. It cannot outlive its source array; keep it inside
/// one observation batch.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ArrayStructureId<'a> {
    address: usize,
    borrow: core::marker::PhantomData<&'a InterpretValue>,
}

impl ArrayStructureId<'_> {
    fn new(address: usize) -> Self {
        Self {
            address,
            borrow: core::marker::PhantomData,
        }
    }
}
pub type ArrayStructureNode<'a> = super::rope::StructureNode<'a, InterpretValue>;

/// A lazy, read-only borrow of one stored array node. Identity, length and
/// kind access are O(1), allocate no snapshot and clone neither values nor
/// reference counts. Every child view and payload retains the source borrow.
#[derive(Clone, Copy)]
pub struct ArrayNode<'a> {
    node: super::rope::NodeRef<'a, InterpretValue>,
}

/// The immediate contents of one stored node. Counts describe logical
/// elements; neither periodic units nor child subtrees are expanded.
#[derive(Debug)]
pub enum ArrayNodeKind<'a> {
    Dense(&'a [InterpretValue]),
    Uniform(&'a InterpretValue),
    Repeat {
        unit: ArrayNode<'a>,
        count: u64,
    },
    Concat {
        left: ArrayNode<'a>,
        right: ArrayNode<'a>,
    },
}

impl<'a> ArrayNode<'a> {
    /// Sharing identity, comparable with the identities in `structure()`.
    pub fn id(&self) -> ArrayStructureId<'a> {
        ArrayStructureId::new(self.node.key())
    }

    /// The logical element count below this stored node.
    pub fn len(&self) -> u64 {
        self.node.len()
    }

    /// Stored nodes are nonempty; empty arrays have no root node.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Borrow the immediate node contents without visiting any child.
    pub fn kind(&self) -> ArrayNodeKind<'a> {
        use super::rope::NodeView;
        match self.node.view() {
            NodeView::Dense(values) => ArrayNodeKind::Dense(values),
            NodeView::Uniform(value) => ArrayNodeKind::Uniform(value),
            NodeView::Repeat { unit, count } => ArrayNodeKind::Repeat {
                unit: Self { node: unit },
                count,
            },
            NodeView::Concat { left, right } => ArrayNodeKind::Concat {
                left: Self { node: left },
                right: Self { node: right },
            },
        }
    }
}

impl core::fmt::Debug for ArrayNode<'_> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        // Printing a view must not traverse its children.
        f.debug_struct("ArrayNode")
            .field("id", &self.id())
            .field("len", &self.len())
            .finish_non_exhaustive()
    }
}

/// An array, vector, sequence or set value of the reference interpreter. See
/// the module docs.
#[derive(Clone)]
pub struct ArrayValue {
    rope: Rope<InterpretValue>,
}

impl ArrayValue {
    pub(crate) fn into_rope_observed(self) -> Rope<InterpretValue> {
        self.rope
    }

    pub(crate) fn from_rope(rope: Rope<InterpretValue>) -> Self {
        Self { rope }
    }

    pub(crate) fn rope(&self) -> &Rope<InterpretValue> {
        &self.rope
    }

    /// `len` copies of `value`: one node, O(1) in `len`.
    pub fn splat(value: InterpretValue, len: u64) -> Self {
        Self {
            rope: Rope::uniform(value, len),
        }
    }

    /// A dense array of the given elements, MOVED into 16-element leaves:
    /// O(n), with a `Vec`'s per-element footprint plus one node per leaf.
    pub fn from_vec(values: Vec<InterpretValue>) -> Self {
        Self::try_from_elements(values.into_iter().map(Ok::<_, core::convert::Infallible>))
            .unwrap_or_else(|never| match never {})
    }

    /// A dense array built straight from a fallible element stream — each
    /// element lands in its leaf as it is produced, so no intermediate list
    /// of all the elements ever exists.
    pub fn try_from_elements<E>(
        elements: impl IntoIterator<Item = Result<InterpretValue, E>>,
    ) -> Result<Self, E> {
        Ok(Self {
            rope: Rope::from_elements(elements)?,
        })
    }

    /// The array made of consecutive RUNS — `count` copies of each value, in
    /// order. Zero-count runs are ignored. O(runs), whatever the counts.
    pub fn from_runs(runs: Vec<(InterpretValue, u64)>) -> Self {
        Self {
            rope: Rope::concat(
                runs.into_iter()
                    .map(|(value, count)| Rope::uniform(value, count)),
            ),
        }
    }

    /// `count` copies of this whole array, back to back: one node.
    pub fn repeat(&self, count: u64) -> Self {
        Self {
            rope: self.rope.repeat(count),
        }
    }

    /// The number of elements.
    pub fn len(&self) -> u64 {
        self.rope.len()
    }

    /// Whether the array has no elements.
    pub fn is_empty(&self) -> bool {
        self.rope.is_empty()
    }

    /// The element at `index`, or `None` out of bounds. O(height).
    pub fn get(&self, index: u64) -> Option<&InterpretValue> {
        self.rope.get(index)
    }

    /// A copy of this array with `index` set to `value` (`None` out of
    /// bounds). Persistent: `self` is unchanged, and the result shares every
    /// node off the one changed path. O(height).
    pub fn set(&self, index: u64, value: InterpretValue) -> Option<Self> {
        Some(Self {
            rope: self.rope.set(index, value)?,
        })
    }

    /// The value of every element, if the array is ONE uniform node — the
    /// shape `splat` builds. (A uniform array built another way may answer
    /// `None`; this is a fast path, not a decision procedure.)
    pub fn as_splat(&self) -> Option<&InterpretValue> {
        self.rope.as_uniform()
    }

    /// Every element, in order. O(len): for callers that need the dense
    /// list (short arrays, bounded vectors, tests, diagnostics).
    pub fn to_vec(&self) -> Vec<InterpretValue> {
        self.rope.to_vec()
    }

    /// Every element, in order, by reference. O(len) to exhaust.
    pub fn iter(&self) -> impl Iterator<Item = &InterpretValue> + '_ {
        self.rope.iter()
    }

    /// Map every stored value (each distinct stored value once, the shape
    /// kept). O(stored values), never O(len).
    pub fn try_map<E>(
        &self,
        map: impl FnMut(&InterpretValue) -> Result<InterpretValue, E>,
    ) -> Result<Self, E> {
        Ok(Self {
            rope: self.rope.try_map(map)?,
        })
    }

    /// Element-wise combination under a stable ordered-pair callback, computed
    /// on borrowed shared windows. Callback results must depend only on the
    /// fixed pair; successes keep their full extent and errors are left-to-right.
    /// Two splats combine once, including when both arrays physically alias.
    pub fn try_zip_with<E>(
        &self,
        other: &Self,
        zip: impl FnMut(&InterpretValue, &InterpretValue) -> Result<InterpretValue, E>,
    ) -> Result<Self, E> {
        Ok(Self {
            rope: self.rope.try_zip_with(&other.rope, zip)?,
        })
    }

    /// Visit each STORED value once (a splat's value once, whatever the
    /// length), until `visit` breaks.
    pub fn try_for_each_stored<'a, B>(
        &'a self,
        visit: impl FnMut(&'a InterpretValue) -> core::ops::ControlFlow<B>,
    ) -> core::ops::ControlFlow<B> {
        self.rope.try_for_each_stored(visit)
    }

    /// Snapshot the stored graph for diagnostics and semantic observations.
    /// Uniform counts, periodic blocks and shared subtrees stay compact. The
    /// returned snapshot borrows payloads and does not clone interpreter values.
    /// This ordinary observation allocates metadata proportional to distinct
    /// stored nodes; it is separate from observed execution admission.
    /// For batches with overlapping roots, use [`Self::root_node`] and memoize
    /// node identities before following children to avoid repeated snapshots.
    pub fn structure(&self) -> ArrayStructure<'_> {
        let snapshot = self.rope.structure();
        ArrayStructure {
            nodes: snapshot.nodes,
            root: snapshot.root,
            identities: snapshot
                .keys
                .into_iter()
                .map(ArrayStructureId::new)
                .collect(),
        }
    }

    /// Borrow the stored root without allocating, cloning or visiting children.
    /// Empty arrays return `None`. A batch collector can memoize each node's
    /// identity before calling `kind()` and following its child views.
    /// This observation API does not grant observed-execution admission.
    ///
    /// ```
    /// use trust_ir::{Ty, interpret::{ArrayValue, ArrayNodeKind, InterpretValue}};
    /// let array = ArrayValue::splat(InterpretValue::int(Ty::U32, 7).unwrap(), u64::MAX);
    /// let root = array.root_node().unwrap();
    /// assert_eq!(root.len(), u64::MAX);
    /// assert_eq!(Some(root.id()), array.structure_id());
    /// assert!(matches!(root.kind(), ArrayNodeKind::Uniform(_)));
    /// let periodic = ArrayValue::from_vec(vec![
    ///     InterpretValue::int(Ty::U32, 7).unwrap(),
    ///     InterpretValue::int(Ty::U32, 8).unwrap(),
    /// ]).repeat(10);
    /// let child = match periodic.root_node().unwrap().kind() {
    ///     ArrayNodeKind::Repeat { unit, .. } => unit,
    ///     _ => panic!("expected periodic node"),
    /// };
    /// assert_eq!(child.len(), 2);
    /// ```
    ///
    /// A child view cannot outlive the source array:
    ///
    /// ```compile_fail,E0597
    /// use trust_ir::{Ty, interpret::{ArrayValue, ArrayNodeKind, InterpretValue}};
    /// let child = {
    ///     let array = ArrayValue::from_vec(vec![
    ///         InterpretValue::int(Ty::U32, 7).unwrap(),
    ///         InterpretValue::int(Ty::U32, 8).unwrap(),
    ///     ]).repeat(10);
    ///     match array.root_node().unwrap().kind() {
    ///         ArrayNodeKind::Repeat { unit, .. } => unit,
    ///         _ => panic!("expected periodic node"),
    ///     }
    /// };
    /// assert_eq!(child.len(), 2);
    /// ```
    pub fn root_node(&self) -> Option<ArrayNode<'_>> {
        self.rope.root_node().map(|node| ArrayNode { node })
    }

    /// The root identity without walking or allocating a snapshot. A collector
    /// can reuse a previously seen array before traversing shared nested data.
    /// Empty arrays have no stored root.
    ///
    /// ```
    /// use trust_ir::{Ty, interpret::{ArrayValue, InterpretValue}};
    /// let array = ArrayValue::splat(InterpretValue::int(Ty::U32, 7).unwrap(), 3);
    /// assert!(array.structure_id().is_some());
    /// ```
    ///
    /// A cache key cannot escape the array it borrows:
    ///
    /// ```compile_fail,E0597
    /// use trust_ir::{Ty, interpret::{ArrayValue, InterpretValue}};
    /// let identity = {
    ///     let array = ArrayValue::splat(InterpretValue::int(Ty::U32, 7).unwrap(), 3);
    ///     array.structure_id()
    /// };
    /// assert!(identity.is_some());
    /// ```
    pub fn structure_id(&self) -> Option<ArrayStructureId<'_>> {
        self.rope.root_key().map(ArrayStructureId::new)
    }

    /// Whether the two arrays are the same stored node (O(1)).
    pub(crate) fn ptr_eq(&self, other: &Self) -> bool {
        self.rope.ptr_eq(&other.rope)
    }
}

impl PartialEq for ArrayValue {
    /// Element-wise equality, decided on the ropes' structure.
    fn eq(&self, other: &Self) -> bool {
        self.ptr_eq(other) || self.rope.eq_by(&other.rope, |a, b| a == b)
    }
}

impl Eq for ArrayValue {}

impl core::fmt::Debug for ArrayValue {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        // Structure, not elements: a debug print must not cost the length.
        self.rope
            .fmt_structure(f, &|value, f| core::fmt::Debug::fmt(value, f))
    }
}

impl From<Vec<InterpretValue>> for ArrayValue {
    fn from(values: Vec<InterpretValue>) -> Self {
        Self::from_vec(values)
    }
}

impl FromIterator<InterpretValue> for ArrayValue {
    /// A dense collection, each element moved into its leaf as it arrives.
    fn from_iter<I: IntoIterator<Item = InterpretValue>>(values: I) -> Self {
        Self::try_from_elements(values.into_iter().map(Ok::<_, core::convert::Infallible>))
            .unwrap_or_else(|never| match never {})
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ty::Ty;

    fn int(v: i128) -> InterpretValue {
        InterpretValue::int(Ty::I32, v).expect("i32")
    }

    #[test]
    fn splat_of_a_u64_scale_length_is_constant_size() {
        let array = ArrayValue::splat(int(7), 1 << 40);
        assert_eq!(array.len(), 1 << 40);
        assert_eq!(array.get(0), Some(&int(7)));
        assert_eq!(array.get((1 << 40) - 1), Some(&int(7)));
        assert_eq!(array.get(1 << 40), None);
        assert_eq!(array.rope.node_count(), 1);
        let max = ArrayValue::splat(int(1), u64::MAX);
        assert_eq!(max.get(u64::MAX - 1), Some(&int(1)));
    }

    #[test]
    fn set_is_persistent_and_touches_one_path() {
        let base = ArrayValue::splat(int(0), 1 << 40);
        let written = base.set(123_456_789, int(9)).expect("in bounds");
        assert_eq!(
            base.get(123_456_789),
            Some(&int(0)),
            "the input is unchanged"
        );
        assert_eq!(written.get(123_456_789), Some(&int(9)));
        assert_eq!(written.get(123_456_788), Some(&int(0)));
        assert_eq!(written.get(123_456_790), Some(&int(0)));
        assert!(written.rope.node_count() <= 5, "{written:?}");
        assert!(base.set(1 << 40, int(1)).is_none());
        // Writing the value already there shares the whole tree.
        assert!(base.set(5, int(0)).expect("in bounds").ptr_eq(&base));
    }

    #[test]
    fn equality_is_element_wise_across_shapes() {
        let dense = ArrayValue::from_vec(vec![int(3); 40]);
        let splat = ArrayValue::splat(int(3), 40);
        assert_eq!(dense, splat);
        let mut mixed = ArrayValue::splat(int(3), 40);
        for index in 0..40 {
            mixed = mixed.set(index, int(3)).unwrap();
        }
        assert_eq!(mixed, splat);
        assert_ne!(splat.set(39, int(4)).unwrap(), splat);
        assert_ne!(ArrayValue::splat(int(3), 41), splat);
        assert_eq!(
            ArrayValue::from_vec(Vec::new()),
            ArrayValue::splat(int(3), 0)
        );
        // Two periodic spellings of one array: [1, 2] x 6 against
        // [1, 2, 1, 2, 1, 2] x 2, and a different period that disagrees.
        let pair = ArrayValue::from_vec(vec![int(1), int(2)]);
        let six = ArrayValue::from_vec((0..6).map(|i| int(1 + i % 2)).collect());
        assert_eq!(pair.repeat(6), six.repeat(2));
        let triple = ArrayValue::from_vec(vec![int(1), int(2), int(1)]);
        assert_ne!(pair.repeat(6), triple.repeat(4));
    }

    #[test]
    fn dense_arrays_read_back_in_order() {
        let values: Vec<_> = (0..1000).map(int).collect();
        let array = ArrayValue::from_vec(values.clone());
        assert_eq!(array.to_vec(), values);
        for (index, value) in values.iter().enumerate() {
            assert_eq!(array.get(index as u64), Some(value));
        }
        let updated = array.set(999, int(-1)).unwrap();
        assert_eq!(updated.get(999), Some(&int(-1)));
        assert_eq!(array.get(999), Some(&int(999)));
    }

    #[test]
    fn short_and_leaf_sized_arrays() {
        assert_eq!(ArrayValue::from_vec(vec![int(9)]).get(0), Some(&int(9)));
        assert!(ArrayValue::from_vec(Vec::new()).is_empty());
        for len in [2u64, 15, 16, 17, 255, 256, 257] {
            let values: Vec<_> = (0..len as i128).map(int).collect();
            let array = ArrayValue::from_vec(values.clone());
            assert_eq!(array.len(), len);
            assert_eq!(array.to_vec(), values, "len {len}");
            let written = array.set(len - 1, int(-9)).unwrap();
            assert_eq!(written.get(len - 1), Some(&int(-9)));
            assert_eq!(written.get(0), Some(&int(0)));
            assert_eq!(
                ArrayValue::from_runs(values.into_iter().map(|v| (v, 1)).collect()),
                array
            );
        }
    }

    #[test]
    fn runs_build_and_read_back() {
        let array = ArrayValue::from_runs(vec![(int(1), 5), (int(2), 1 << 33), (int(3), 7)]);
        assert_eq!(array.len(), 5 + (1 << 33) + 7);
        assert_eq!(array.get(4), Some(&int(1)));
        assert_eq!(array.get(5), Some(&int(2)));
        assert_eq!(array.get(4 + (1 << 33)), Some(&int(2)));
        assert_eq!(array.get(5 + (1 << 33)), Some(&int(3)));
        assert!(array.rope.node_count() <= 5);
        let mut stored = Vec::new();
        let _ = array.try_for_each_stored(|value| {
            stored.push(value.clone());
            core::ops::ControlFlow::<()>::Continue(())
        });
        assert_eq!(stored, vec![int(1), int(2), int(3)]);
    }

    /// An `InsertElement` chain over a fresh array keeps O(height) new nodes
    /// per insert: filling `n` elements one by one leaves O(n) nodes, never
    /// O(n^2) (the pre-v50 interpreter cloned the array on every insert).
    #[test]
    fn an_insert_chain_is_linear_in_its_inserts() {
        let n = 4096u64;
        let mut array = ArrayValue::splat(int(0), n);
        for index in 0..n {
            array = array.set(index, int(index as i128 + 1)).unwrap();
        }
        assert_eq!(array.get(n - 1), Some(&int(n as i128)));
        assert!(
            array.rope.node_count() <= 4 * n as usize,
            "{} nodes for {n} inserts",
            array.rope.node_count()
        );
        assert!(
            array.rope.height() <= 2 * 13,
            "height {}",
            array.rope.height()
        );
    }
}

#[cfg(test)]
#[path = "array_structure_tests.rs"]
mod structure_tests;

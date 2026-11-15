// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Persistent, height-balanced ropes with SHARED structure: the one
//! representation behind the reference interpreter's byte images
//! ([`super::byte_image::Image`]) and its array and vector values
//! ([`super::ArrayValue`]).
//!
//! A rope costs what BUILT it, never its length:
//!
//! * a `Uniform` node is `len` copies of one element;
//! * a `Repeat` node is `count` back-to-back copies of a sub-rope, which it
//!   shares;
//! * a `Dense` node is a window of a literal buffer. Its elements were paid
//!   for by whoever wrote them, and slicing it copies nothing;
//! * a `Concat` node joins two ropes and shares both.
//!
//! Nodes are immutable and reference-counted, so a copy of a rope, a slice
//! of it, or a rope assembled from pieces of others SHARES their nodes: a
//! rope is a DAG. A copy of memory onto its own neighbourhood (the doubling
//! copy of `<[T]>::repeat`) therefore adds one node, not the bytes it copies.
//! Single-input structural walks memoize original node identity. Paired walks
//! memoize original windows, including phase and extent where required, so a
//! shared input does not acquire a fresh memo identity merely by being sliced.
//!
//! **Balance.** `Concat` nodes are AVL-balanced: sibling heights differ by at
//! most one ([`join`] is the AVL join, splitting a `Repeat` into halves when
//! it has to descend into one). For balancing, a `Repeat` of `count` copies
//! counts as the perfectly balanced tree of its copies (height `unit +
//! ceil(log2 count)`). A rope's height is therefore O(log) of the number of
//! leaves it would have with every `Repeat` written out, which is at most its
//! length: every root-to-leaf path is short for any `u64` length, whatever
//! sequence of joins and slices built the rope, so no recursion here is deep.
//!
//! **What stays proportional to a length.** Only the operations documented
//! as such: [`Rope::to_vec`] / [`Rope::iter`] (for callers that asked for
//! every element), a `Dense` window (literal elements already paid for), and
//! the realignment of two structures whose periods disagree
//! ([`Rope::chunk_map`], [`Rope::try_zip_with`], equality). Paired walks
//! depend on distinct original windows, phases and extents, and on the
//! represented result. Node count alone is not a universal bound for arbitrary
//! misaligned inputs; literal pair periods can have `lcm(p, q)` alignments.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

#[path = "rope_observed.rs"]
mod observed_impl;

/// Two literal leaves whose total is at most this many elements are merged
/// (by copying at most this many elements) when a join makes them neighbours.
/// A node-size constant, like a B-tree's order: it bounds the copy, not any
/// input.
const SMALL_LEAF: usize = 16;

/// The element type of a [`Rope`].
pub(crate) trait RopeElem: Clone {
    /// The longest literal leaf [`Rope::concat`] and [`Rope::from_elements`]
    /// assemble from FRESH (uniquely owned) literal parts. Bytes use no bound
    /// (a written literal is one buffer); array values use a small node size
    /// so a persistent `set` copies a bounded leaf.
    const FRESH_LEAF: usize;

    /// A CHEAP, conservative identity test: `true` only when the two elements
    /// are certainly equal (it may answer `false` for equal elements). Used
    /// to merge neighbouring runs and to recognize uniform structure; never a
    /// semantic comparison.
    fn same(&self, other: &Self) -> bool;
}

/// A persistent rope: see the module docs.
pub(crate) struct Rope<T> {
    root: Option<Link<T>>,
}

/// A borrowed, bottom-up snapshot of a rope's distinct stored nodes.
/// Child indices always precede their parents. Logical repetitions and shared
/// subtrees remain compact; literal windows borrow their actual stored lanes.
#[derive(Debug)]
pub(crate) struct Structure<'a, T> {
    pub keys: Vec<usize>,
    pub nodes: Vec<StructureNode<'a, T>>,
    pub root: Option<usize>,
}

/// One node in a [`Structure`]. Counts describe logical elements, never the
/// amount of host storage allocated by a snapshot.
#[derive(Debug)]
pub enum StructureNode<'a, T> {
    Dense(&'a [T]),
    Uniform { len: u64, value: &'a T },
    Repeat { unit: usize, count: u64 },
    Concat { left: usize, right: usize },
}

/// One borrowed stored node. Copying a view neither clones an Arc nor walks
/// its children. This is internal machinery for the concrete array view API.
pub(crate) struct NodeRef<'a, T>(&'a Node<T>);

impl<T> Copy for NodeRef<'_, T> {}
impl<T> Clone for NodeRef<'_, T> {
    fn clone(&self) -> Self {
        *self
    }
}

pub(crate) enum NodeView<'a, T> {
    Dense(&'a [T]),
    Uniform(&'a T),
    Repeat {
        unit: NodeRef<'a, T>,
        count: u64,
    },
    Concat {
        left: NodeRef<'a, T>,
        right: NodeRef<'a, T>,
    },
}

impl<'a, T> NodeRef<'a, T> {
    pub(crate) fn key(self) -> usize {
        self.0 as *const Node<T> as usize
    }
    pub(crate) fn len(self) -> u64 {
        self.0.len
    }
    pub(crate) fn view(self) -> NodeView<'a, T> {
        match &self.0.kind {
            Kind::Dense { data, start } => {
                NodeView::Dense(&data[*start..*start + self.0.len as usize])
            }
            Kind::Uniform(value) => NodeView::Uniform(value),
            Kind::Repeat { unit, count } => NodeView::Repeat {
                unit: NodeRef(unit),
                count: *count,
            },
            Kind::Concat { left, right } => NodeView::Concat {
                left: NodeRef(left),
                right: NodeRef(right),
            },
        }
    }
}

type Link<T> = Arc<Node<T>>;

pub(crate) struct Node<T> {
    len: u64,
    height: u32,
    kind: Kind<T>,
}

enum Kind<T> {
    /// `data[start .. start + len]`.
    Dense { data: Arc<Vec<T>>, start: usize },
    /// `len` copies of one element.
    Uniform(T),
    /// `count >= 2` copies of `unit`, which is never itself a `Uniform`, a
    /// `Repeat` or a one-element `Dense` (those normalize away).
    Repeat { unit: Link<T>, count: u64 },
    /// `left` then `right`, both nonempty.
    Concat { left: Link<T>, right: Link<T> },
}

impl<T> Clone for Rope<T> {
    fn clone(&self) -> Self {
        Rope {
            root: self.root.clone(),
        }
    }
}

fn ceil_log2(count: u64) -> u32 {
    if count <= 1 {
        0
    } else {
        u64::BITS - (count - 1).leading_zeros()
    }
}

fn sum_len(a: u64, b: u64) -> u64 {
    a.checked_add(b)
        .expect("a rope length fits u64 (a type or allocation size bounds it)")
}

fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

/// `lcm(p, q)` when it is below `len`; the logical window may have a tail.
fn lcm_below(p: u64, q: u64, len: u64) -> Option<u64> {
    (p / gcd(p, q)).checked_mul(q).filter(|lcm| *lcm < len)
}

fn key<T>(node: &Link<T>) -> usize {
    Arc::as_ptr(node) as usize
}

fn dense_node<T>(data: Arc<Vec<T>>, start: usize, len: usize) -> Link<T> {
    debug_assert!(len > 0 && start + len <= data.len());
    Arc::new(Node {
        len: len as u64,
        height: 0,
        kind: Kind::Dense { data, start },
    })
}

fn uniform_node<T>(value: T, len: u64) -> Link<T> {
    debug_assert!(len > 0);
    Arc::new(Node {
        len,
        height: 0,
        kind: Kind::Uniform(value),
    })
}

/// A `Concat` node with no balancing (callers keep the AVL invariant).
fn concat_node<T>(left: Link<T>, right: Link<T>) -> Link<T> {
    Arc::new(Node {
        len: sum_len(left.len, right.len),
        height: left.height.max(right.height) + 1,
        kind: Kind::Concat { left, right },
    })
}

/// `count` copies of `unit`, normalized (no element test: callers pass a unit
/// that is already normalized, or accept a `Repeat` of a uniform unit).
fn repeat_node<T: Clone>(unit: Link<T>, count: u64) -> Option<Link<T>> {
    match count {
        0 => return None,
        1 => return Some(unit),
        _ => {}
    }
    let len = unit
        .len
        .checked_mul(count)
        .expect("a rope length fits u64 (a type or allocation size bounds it)");
    match &unit.kind {
        Kind::Uniform(value) => return Some(uniform_node(value.clone(), len)),
        Kind::Dense { data, start } if unit.len == 1 => {
            return Some(uniform_node(data[*start].clone(), len));
        }
        Kind::Repeat {
            unit: inner,
            count: inner_count,
        } => {
            let count = inner_count
                .checked_mul(count)
                .expect("a rope length fits u64 (a type or allocation size bounds it)");
            return Some(Arc::new(Node {
                len,
                height: inner.height + ceil_log2(count),
                kind: Kind::Repeat {
                    unit: Arc::clone(inner),
                    count,
                },
            }));
        }
        Kind::Dense { .. } | Kind::Concat { .. } => {}
    }
    let height = unit.height + ceil_log2(count);
    Some(Arc::new(Node {
        len,
        height,
        kind: Kind::Repeat { unit, count },
    }))
}

/// An internal node's two halves: a `Concat`'s children, or a `Repeat` split
/// into two `Repeat`s of the unit (the perfectly balanced tree of its copies).
fn expose<T: Clone>(node: &Link<T>) -> Option<(Link<T>, Link<T>)> {
    match &node.kind {
        Kind::Concat { left, right } => Some((Arc::clone(left), Arc::clone(right))),
        Kind::Repeat { unit, count } => {
            let first = count.div_ceil(2);
            Some((
                repeat_node(Arc::clone(unit), first)?,
                repeat_node(Arc::clone(unit), count - first)?,
            ))
        }
        Kind::Dense { .. } | Kind::Uniform(_) => None,
    }
}

fn rotate_left<T: Clone>(node: Link<T>) -> Link<T> {
    let (left, right) = expose(&node).expect("rotating an internal node");
    let (right_left, right_right) =
        expose(&right).expect("a left rotation's right child is internal");
    concat_node(concat_node(left, right_left), right_right)
}

fn rotate_right<T: Clone>(node: Link<T>) -> Link<T> {
    let (left, right) = expose(&node).expect("rotating an internal node");
    let (left_left, left_right) = expose(&left).expect("a right rotation's left child is internal");
    concat_node(left_left, concat_node(left_right, right))
}

/// Whether two nodes are the same stored content by IDENTITY (never by
/// comparing elements): one node, one window of one buffer, one uniform run,
/// or the same copies of the same unit.
fn same_node<T: RopeElem>(a: &Link<T>, b: &Link<T>) -> bool {
    if Arc::ptr_eq(a, b) {
        return true;
    }
    if a.len != b.len {
        return false;
    }
    match (&a.kind, &b.kind) {
        (Kind::Dense { data: x, start: i }, Kind::Dense { data: y, start: j }) => {
            Arc::ptr_eq(x, y) && i == j
        }
        (Kind::Uniform(x), Kind::Uniform(y)) => x.same(y),
        (Kind::Repeat { unit: u, count: c }, Kind::Repeat { unit: v, count: d }) => {
            c == d && same_node(u, v)
        }
        (
            Kind::Concat {
                left: al,
                right: ar,
            },
            Kind::Concat {
                left: bl,
                right: br,
            },
        ) => Arc::ptr_eq(al, bl) && Arc::ptr_eq(ar, br),
        _ => false,
    }
}

fn unit_and_count<T>(node: &Link<T>) -> (&Link<T>, u64) {
    match &node.kind {
        Kind::Repeat { unit, count } => (unit, *count),
        _ => (node, 1),
    }
}

/// The one node two neighbours become, when they are copies of one unit, two
/// runs of one element, or two small literal windows.
fn merge_neighbours<T: RopeElem>(a: &Link<T>, b: &Link<T>) -> Option<Link<T>> {
    let (unit_a, count_a) = unit_and_count(a);
    let (unit_b, count_b) = unit_and_count(b);
    if same_node(unit_a, unit_b) {
        let count = count_a
            .checked_add(count_b)
            .expect("a rope length fits u64 (a type or allocation size bounds it)");
        return repeat_node(Arc::clone(unit_a), count);
    }
    match (&a.kind, &b.kind) {
        (Kind::Uniform(x), Kind::Uniform(y)) if x.same(y) => {
            Some(uniform_node(x.clone(), sum_len(a.len, b.len)))
        }
        (Kind::Dense { data: x, start: i }, Kind::Dense { data: y, start: j })
            if a.len + b.len <= SMALL_LEAF as u64 =>
        {
            let mut elems = Vec::with_capacity((a.len + b.len) as usize);
            elems.extend_from_slice(&x[*i..*i + a.len as usize]);
            elems.extend_from_slice(&y[*j..*j + b.len as usize]);
            let len = elems.len();
            Some(dense_node(Arc::new(elems), 0, len))
        }
        _ => None,
    }
}

/// `a` then `b`: the AVL join, after merging neighbours that are one node.
fn join<T: RopeElem>(a: Link<T>, b: Link<T>) -> Link<T> {
    if let Some(merged) = merge_neighbours(&a, &b) {
        return merged;
    }
    if a.height > b.height + 1 {
        join_right(a, b)
    } else if b.height > a.height + 1 {
        join_left(a, b)
    } else {
        concat_node(a, b)
    }
}

/// `a` then `b` where `a` is at least two levels taller: descend `a`'s right
/// spine (Blelloch, Ferizovic and Sun's `joinRight`).
fn join_right<T: Clone>(a: Link<T>, b: Link<T>) -> Link<T> {
    let (left, right) =
        expose(&a).expect("a node two levels taller than its neighbour is internal");
    let left_height = left.height;
    if right.height <= b.height + 1 {
        let joined = concat_node(right, b);
        if joined.height <= left_height + 1 {
            concat_node(left, joined)
        } else {
            rotate_left(concat_node(left, rotate_right(joined)))
        }
    } else {
        let joined = join_right(right, b);
        let joined_height = joined.height;
        let node = concat_node(left, joined);
        if joined_height <= left_height + 1 {
            node
        } else {
            rotate_left(node)
        }
    }
}

/// The mirror of [`join_right`].
fn join_left<T: Clone>(a: Link<T>, b: Link<T>) -> Link<T> {
    let (left, right) =
        expose(&b).expect("a node two levels taller than its neighbour is internal");
    let right_height = right.height;
    if left.height <= a.height + 1 {
        let joined = concat_node(a, left);
        if joined.height <= right_height + 1 {
            concat_node(joined, right)
        } else {
            rotate_right(concat_node(rotate_left(joined), right))
        }
    } else {
        let joined = join_left(a, left);
        let joined_height = joined.height;
        let node = concat_node(joined, right);
        if joined_height <= right_height + 1 {
            node
        } else {
            rotate_right(node)
        }
    }
}

fn join_opt<T: RopeElem>(a: Option<Link<T>>, b: Option<Link<T>>) -> Option<Link<T>> {
    match (a, b) {
        (Some(a), Some(b)) => Some(join(a, b)),
        (a, None) => a,
        (None, b) => b,
    }
}

fn join_all<T: RopeElem>(parts: impl IntoIterator<Item = Option<Link<T>>>) -> Option<Link<T>> {
    parts.into_iter().fold(None, join_opt)
}

/// The sub-rope `[start, start + len)` of `node` (in bounds), sharing its
/// storage: O(height) new nodes, never O(len).
fn slice_node<T: RopeElem>(node: &Link<T>, start: u64, len: u64) -> Option<Link<T>> {
    if len == 0 {
        return None;
    }
    if start == 0 && len == node.len {
        return Some(Arc::clone(node));
    }
    debug_assert!(start + len <= node.len, "slice within the rope");
    match &node.kind {
        Kind::Dense { data, start: base } => Some(dense_node(
            Arc::clone(data),
            base + start as usize,
            len as usize,
        )),
        Kind::Uniform(value) => Some(uniform_node(value.clone(), len)),
        Kind::Repeat { unit, .. } => {
            let unit_len = unit.len;
            let phase = start % unit_len;
            let mut remaining = len;
            let mut head = None;
            if phase != 0 {
                let take = (unit_len - phase).min(remaining);
                head = slice_node(unit, phase, take);
                remaining -= take;
            }
            let whole = remaining / unit_len;
            let middle = repeat_node(Arc::clone(unit), whole);
            remaining -= whole * unit_len;
            let tail = slice_node(unit, 0, remaining);
            join_all([head, middle, tail])
        }
        Kind::Concat { left, right } => {
            let left_len = left.len;
            if start + len <= left_len {
                slice_node(left, start, len)
            } else if start >= left_len {
                slice_node(right, start - left_len, len)
            } else {
                join_opt(
                    slice_node(left, start, left_len - start),
                    slice_node(right, 0, start + len - left_len),
                )
            }
        }
    }
}

/// `node` with element `index` replaced: the path to it is copied, every
/// other node is shared.
fn set_node<T: RopeElem>(node: &Link<T>, index: u64, value: T) -> Link<T> {
    match &node.kind {
        Kind::Dense { data, start } => {
            let mut elems = data[*start..*start + node.len as usize].to_vec();
            elems[index as usize] = value;
            let len = elems.len();
            dense_node(Arc::new(elems), 0, len)
        }
        Kind::Uniform(current) => {
            if current.same(&value) {
                return Arc::clone(node);
            }
            let after = node.len - index - 1;
            join_all([
                (index > 0).then(|| uniform_node(current.clone(), index)),
                Some(dense_node(Arc::new(vec![value]), 0, 1)),
                (after > 0).then(|| uniform_node(current.clone(), after)),
            ])
            .expect("a nonempty rope")
        }
        Kind::Repeat { unit, count } => {
            let copy = index / unit.len;
            join_all([
                repeat_node(Arc::clone(unit), copy),
                Some(set_node(unit, index % unit.len, value)),
                repeat_node(Arc::clone(unit), count - copy - 1),
            ])
            .expect("a nonempty rope")
        }
        Kind::Concat { left, right } => {
            if index < left.len {
                join(set_node(left, index, value), Arc::clone(right))
            } else {
                join(Arc::clone(left), set_node(right, index - left.len, value))
            }
        }
    }
}

/// Move a fresh literal buffer into a leaf and join it onto `acc`.
fn flush<T: RopeElem>(acc: &mut Option<Link<T>>, pending: &mut Vec<T>) {
    if pending.is_empty() {
        return;
    }
    let elems = std::mem::take(pending);
    let len = elems.len();
    let leaf = dense_node(Arc::new(elems), 0, len);
    *acc = join_opt(acc.take(), Some(leaf));
}

/// One piece of a [`Rope::chunk_map`] walk: what a node contributes to the
/// sequence of `stride`-element chunks, given how far into a chunk it starts.
enum Piece<T, R> {
    /// The node lies strictly inside one chunk (it does not complete it).
    Within(Option<Link<T>>),
    /// `pre` completes the chunk pending at the node's start (empty when the
    /// node starts on a chunk boundary), `mid` are the node's whole chunks,
    /// mapped, and `suf` begins the chunk pending at its end (shorter than a
    /// chunk).
    Spans {
        pre: Option<Link<T>>,
        mid: Option<Link<R>>,
        suf: Option<Link<T>>,
    },
}

impl<T, R> Clone for Piece<T, R> {
    fn clone(&self) -> Self {
        match self {
            Piece::Within(node) => Piece::Within(node.clone()),
            Piece::Spans { pre, mid, suf } => Piece::Spans {
                pre: pre.clone(),
                mid: mid.clone(),
                suf: suf.clone(),
            },
        }
    }
}

/// The state of one [`Rope::chunk_map`] walk.
struct ChunkWalk<'f, T, R, E> {
    stride: u64,
    decode: &'f mut dyn FnMut(&Rope<T>) -> Result<R, E>,
    memo: HashMap<(usize, u64), Piece<T, R>>,
}

impl<T: RopeElem, R: RopeElem, E> ChunkWalk<'_, T, R, E> {
    fn decode_chunk(&mut self, chunk: Option<Link<T>>) -> Result<Link<R>, E> {
        let value = (self.decode)(&Rope { root: chunk })?;
        Ok(dense_node(Arc::new(vec![value]), 0, 1))
    }

    /// `a` then `b`, where `b` starts where `a` ends.
    fn combine(&mut self, a: Piece<T, R>, b: Piece<T, R>) -> Result<Piece<T, R>, E> {
        Ok(match (a, b) {
            (Piece::Within(x), Piece::Within(y)) => Piece::Within(join_opt(x, y)),
            (Piece::Within(x), Piece::Spans { pre, mid, suf }) => Piece::Spans {
                pre: join_opt(x, pre),
                mid,
                suf,
            },
            (Piece::Spans { pre, mid, suf }, Piece::Within(y)) => Piece::Spans {
                pre,
                mid,
                suf: join_opt(suf, y),
            },
            (
                Piece::Spans {
                    pre: pre_a,
                    mid: mid_a,
                    suf: suf_a,
                },
                Piece::Spans {
                    pre: pre_b,
                    mid: mid_b,
                    suf: suf_b,
                },
            ) => {
                // The chunk `a` leaves pending is completed by `b`'s prefix:
                // exactly one chunk, or nothing on a chunk boundary.
                let junction = join_opt(suf_a, pre_b);
                let junction = match junction {
                    Some(chunk) => Some(self.decode_chunk(Some(chunk))?),
                    None => None,
                };
                Piece::Spans {
                    pre: pre_a,
                    mid: join_all([mid_a, junction, mid_b]),
                    suf: suf_b,
                }
            }
        })
    }

    /// The whole chunks of `node[offset .. offset + count * stride)`, one
    /// decode each: `period` distinct chunks then repeated.
    fn chunks_by_window(
        &mut self,
        node: &Link<T>,
        offset: u64,
        count: u64,
        period: u64,
    ) -> Result<Option<Link<R>>, E> {
        let distinct = count.min(period);
        let mut acc: Option<Link<R>> = None;
        let mut pending: Vec<R> = Vec::new();
        for index in 0..distinct {
            let chunk = slice_node(node, offset + index * self.stride, self.stride);
            pending.push((self.decode)(&Rope { root: chunk })?);
            if pending.len() == R::FRESH_LEAF {
                flush(&mut acc, &mut pending);
            }
        }
        flush(&mut acc, &mut pending);
        let Some(one_period) = acc else {
            return Ok(None);
        };
        if count <= period {
            return Ok(Some(one_period));
        }
        let rest = slice_node(&one_period, 0, count % period);
        Ok(join_opt(repeat_node(one_period, count / period), rest))
    }

    /// What `node` contributes when it starts `phase` elements into a chunk.
    fn walk(&mut self, node: &Link<T>, phase: u64) -> Result<Piece<T, R>, E> {
        let stride = self.stride;
        let need = (stride - phase) % stride;
        if need > 0 && node.len < need {
            return Ok(Piece::Within(Some(Arc::clone(node))));
        }
        let memo_key = (key(node), phase);
        if let Some(piece) = self.memo.get(&memo_key) {
            return Ok(piece.clone());
        }
        let whole = (node.len - need) / stride;
        let tail = need + whole * stride;
        let piece = match &node.kind {
            // Literal elements: one decode per chunk (the elements are paid
            // for already).
            Kind::Dense { .. } => Piece::Spans {
                pre: slice_node(node, 0, need),
                mid: self.chunks_by_window(node, need, whole, whole.max(1))?,
                suf: slice_node(node, tail, node.len - tail),
            },
            // Every whole chunk of a uniform run is the same chunk.
            Kind::Uniform(_) => Piece::Spans {
                pre: slice_node(node, 0, need),
                mid: self.chunks_by_window(node, need, whole, 1)?,
                suf: slice_node(node, tail, node.len - tail),
            },
            Kind::Repeat { unit, count } => self.walk_repeat(node, unit, *count, phase)?,
            Kind::Concat { left, right } => {
                let left_piece = self.walk(left, phase)?;
                let right_piece = self.walk(right, (phase + left.len) % stride)?;
                self.combine(left_piece, right_piece)?
            }
        };
        self.memo.insert(memo_key, piece.clone());
        Ok(piece)
    }

    /// `count` copies of `unit` (the node `node`) starting `phase` elements
    /// into a chunk. With unit length `u` and stride `s`, the chunks repeat
    /// every `lcm(u, s)` elements: `u / gcd` chunks, or `s / gcd` copies of
    /// the unit. Whichever is fewer is walked once and the rest repeated.
    fn walk_repeat(
        &mut self,
        node: &Link<T>,
        unit: &Link<T>,
        count: u64,
        phase: u64,
    ) -> Result<Piece<T, R>, E> {
        let stride = self.stride;
        let unit_len = unit.len;
        let divisor = gcd(unit_len, stride);
        let need = (stride - phase) % stride;
        if unit_len <= stride {
            // Chunk windows: at most `unit / gcd` distinct ones.
            let whole = (node.len - need) / stride;
            let tail = need + whole * stride;
            return Ok(Piece::Spans {
                pre: slice_node(node, 0, need),
                mid: self.chunks_by_window(node, need, whole, unit_len / divisor)?,
                suf: slice_node(node, tail, node.len - tail),
            });
        }
        // The unit is longer than a chunk: walk the unit's own structure at
        // each of the `stride / gcd` phases a copy can start at. After that
        // many copies the phase is back where it began.
        let copies_per_period = stride / divisor;
        let walked = count.min(copies_per_period);
        let remainder = count % copies_per_period;
        let mut acc: Option<Piece<T, R>> = None;
        let mut first_remainder: Option<Piece<T, R>> = None;
        for copy in 0..walked {
            if copy == remainder && remainder > 0 {
                first_remainder = acc.clone();
            }
            // `(phase + copy * unit_len) mod stride`, without overflow.
            let copy_phase = ((u128::from(phase)
                + u128::from(copy) * u128::from(unit_len % stride))
                % u128::from(stride)) as u64;
            let piece = self.walk(unit, copy_phase)?;
            acc = Some(match acc {
                Some(acc) => self.combine(acc, piece)?,
                None => piece,
            });
        }
        let period = acc.expect("a repeat has at least two copies");
        if count <= copies_per_period {
            return Ok(period);
        }
        // `count / copies_per_period` periods back to back, each starting and
        // ending at `phase`: pre, mid, (junction, mid)*, suf.
        let Piece::Spans { pre, mid, suf } = period else {
            unreachable!("a period of a unit longer than a chunk spans chunks")
        };
        let periods = count / copies_per_period;
        let junction = match join_opt(suf.clone(), pre.clone()) {
            Some(chunk) => Some(self.decode_chunk(Some(chunk))?),
            None => None,
        };
        let body = join_opt(junction, mid.clone());
        let repeated = Piece::Spans {
            pre,
            mid: join_opt(mid, body.and_then(|body| repeat_node(body, periods - 1))),
            suf,
        };
        match first_remainder {
            Some(rest) => self.combine(repeated, rest),
            None if remainder > 0 => {
                unreachable!("the remainder prefix was recorded while walking")
            }
            None => Ok(repeated),
        }
    }
}

impl<T: RopeElem> Rope<T> {
    /// The empty rope.
    pub(crate) fn empty() -> Self {
        Rope { root: None }
    }

    /// One literal leaf holding `elems` (no copy).
    pub(crate) fn dense(elems: Vec<T>) -> Self {
        let len = elems.len();
        Rope {
            root: (len > 0).then(|| dense_node(Arc::new(elems), 0, len)),
        }
    }

    /// A literal rope built from a fallible element stream, in leaves of at
    /// most [`RopeElem::FRESH_LEAF`] elements: O(n), and no intermediate list
    /// of all the elements ever exists.
    pub(crate) fn from_elements<E>(
        elems: impl IntoIterator<Item = Result<T, E>>,
    ) -> Result<Self, E> {
        let mut acc = None;
        let mut pending = Vec::new();
        for elem in elems {
            pending.push(elem?);
            if pending.len() == T::FRESH_LEAF {
                flush(&mut acc, &mut pending);
            }
        }
        flush(&mut acc, &mut pending);
        Ok(Rope { root: acc })
    }

    /// `len` copies of `value`: one node.
    pub(crate) fn uniform(value: T, len: u64) -> Self {
        Rope {
            root: (len > 0).then(|| uniform_node(value, len)),
        }
    }

    /// The ropes back to back. Structure is SHARED, never copied, with one
    /// exception: literal parts that are FRESH (their node and buffer have
    /// no other owner, so their elements were just paid for) are moved into
    /// one leaf. Neighbouring copies of one unit become one `Repeat`.
    pub(crate) fn concat(parts: impl IntoIterator<Item = Rope<T>>) -> Self {
        let mut acc: Option<Link<T>> = None;
        let mut pending: Vec<T> = Vec::new();
        for part in parts {
            let Some(root) = part.root else { continue };
            let shared = match Arc::try_unwrap(root) {
                Ok(Node {
                    len,
                    kind: Kind::Dense { data, start },
                    ..
                }) => match Arc::try_unwrap(data) {
                    Ok(mut elems) => {
                        let len = len as usize;
                        if pending.len() + len > T::FRESH_LEAF {
                            flush(&mut acc, &mut pending);
                        }
                        if pending.is_empty() && start == 0 && elems.len() == len {
                            pending = elems;
                        } else {
                            pending.extend(elems.drain(start..start + len));
                        }
                        continue;
                    }
                    Err(data) => dense_node(data, start, len as usize),
                },
                Ok(node) => Arc::new(node),
                Err(root) => root,
            };
            flush(&mut acc, &mut pending);
            acc = join_opt(acc, Some(shared));
        }
        flush(&mut acc, &mut pending);
        Rope { root: acc }
    }

    /// `self` then `other`, sharing both.
    pub(crate) fn append(&self, other: &Self) -> Self {
        Rope {
            root: join_opt(self.root.clone(), other.root.clone()),
        }
    }

    pub(crate) fn len(&self) -> u64 {
        self.root.as_ref().map_or(0, |root| root.len)
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.root.is_none()
    }

    /// `count` copies of this rope: one node (a uniform rope stays uniform).
    pub(crate) fn repeat(&self, count: u64) -> Self {
        let Some(root) = &self.root else {
            return Rope::empty();
        };
        if count == 0 {
            return Rope::empty();
        }
        if count > 1
            && let Some(value) = self.all_same()
        {
            let len = root
                .len
                .checked_mul(count)
                .expect("a rope length fits u64 (a type or allocation size bounds it)");
            return Rope::uniform(value.clone(), len);
        }
        Rope {
            root: repeat_node(Arc::clone(root), count),
        }
    }

    /// The sub-rope `[start, start + len)` (in bounds), sharing storage:
    /// O(height) new nodes, never O(len).
    pub(crate) fn slice(&self, start: u64, len: u64) -> Self {
        debug_assert!(start + len <= self.len(), "slice within the rope");
        Rope {
            root: self
                .root
                .as_ref()
                .and_then(|root| slice_node(root, start, len)),
        }
    }

    /// Element `index`, or `None` out of bounds. O(height), no recursion.
    pub(crate) fn get(&self, mut index: u64) -> Option<&T> {
        let mut node = self.root.as_deref()?;
        if index >= node.len {
            return None;
        }
        loop {
            match &node.kind {
                Kind::Dense { data, start } => return data.get(start + index as usize),
                Kind::Uniform(value) => return Some(value),
                Kind::Repeat { unit, .. } => {
                    index %= unit.len;
                    node = unit;
                }
                Kind::Concat { left, right } => {
                    if index < left.len {
                        node = left;
                    } else {
                        index -= left.len;
                        node = right;
                    }
                }
            }
        }
    }

    /// A copy with element `index` set to `value` (`None` out of bounds).
    /// Persistent: `self` is unchanged and shares every node off the one
    /// changed path. O(height) new nodes.
    pub(crate) fn set(&self, index: u64, value: T) -> Option<Self> {
        let root = self.root.as_ref()?;
        (index < root.len).then(|| Rope {
            root: Some(set_node(root, index, value)),
        })
    }

    /// The element of a rope that is ONE uniform node.
    pub(crate) fn as_uniform(&self) -> Option<&T> {
        match &self.root.as_deref()?.kind {
            Kind::Uniform(value) => Some(value),
            _ => None,
        }
    }

    /// The literal elements of a rope that is ONE dense leaf.
    pub(crate) fn as_dense(&self) -> Option<&[T]> {
        let root = self.root.as_deref()?;
        match &root.kind {
            Kind::Dense { data, start } => Some(&data[*start..*start + root.len as usize]),
            _ => None,
        }
    }

    /// Whether the rope is a single leaf (a literal window or a uniform run).
    pub(crate) fn is_leaf(&self) -> bool {
        self.root
            .as_ref()
            .is_some_and(|root| matches!(root.kind, Kind::Dense { .. } | Kind::Uniform(_)))
    }

    /// Whether the two ropes are the same stored node (an O(1) identity test).
    pub(crate) fn ptr_eq(&self, other: &Self) -> bool {
        match (&self.root, &other.root) {
            (Some(a), Some(b)) => Arc::ptr_eq(a, b),
            (None, None) => true,
            _ => false,
        }
    }

    /// The literal window of a rope that is ONE dense leaf, made uniquely
    /// owned so it can be written in place: copy-on-write of the WINDOW when
    /// its buffer is shared (the window's elements were paid for when they
    /// were written). `None` for any other shape.
    pub(crate) fn dense_mut(&mut self) -> Option<&mut [T]> {
        let root = self.root.as_mut()?;
        if !matches!(root.kind, Kind::Dense { .. }) {
            return None;
        }
        if Arc::get_mut(root).is_none() {
            let Kind::Dense { data, start } = &root.kind else {
                unreachable!("checked above")
            };
            *root = dense_node(Arc::clone(data), *start, root.len as usize);
        }
        let node = Arc::get_mut(root).expect("uniquely owned above");
        let len = node.len as usize;
        let Kind::Dense { data, start } = &mut node.kind else {
            unreachable!("checked above")
        };
        if Arc::get_mut(data).is_none() {
            *data = Arc::new(data[*start..*start + len].to_vec());
            *start = 0;
        }
        let buffer = Arc::get_mut(data).expect("uniquely owned above");
        Some(&mut buffer[*start..*start + len])
    }

    /// Append `elems` in place to a rope that is ONE uniquely owned dense
    /// leaf whose window ends at its buffer's end; `false` (and nothing
    /// changed) for any other shape.
    pub(crate) fn try_append_in_place(&mut self, elems: &[T]) -> bool {
        let Some(root) = self.root.as_mut() else {
            return false;
        };
        let Some(node) = Arc::get_mut(root) else {
            return false;
        };
        let Kind::Dense { data, start } = &mut node.kind else {
            return false;
        };
        if *start + node.len as usize != data.len() {
            return false;
        }
        let Some(buffer) = Arc::get_mut(data) else {
            return false;
        };
        buffer.extend_from_slice(elems);
        node.len += elems.len() as u64;
        true
    }

    /// The element, when every element of the rope is certainly the same one
    /// ([`RopeElem::same`]). Decided structurally, each node once; a literal
    /// leaf is scanned (its elements are paid for already).
    pub(crate) fn all_same(&self) -> Option<&T> {
        fn go<'a, T: RopeElem>(
            node: &'a Link<T>,
            memo: &mut HashMap<usize, Option<&'a T>>,
        ) -> Option<&'a T> {
            match &node.kind {
                Kind::Uniform(value) => return Some(value),
                Kind::Dense { data, start } => {
                    let window = &data[*start..*start + node.len as usize];
                    let first = window.first()?;
                    return window.iter().all(|elem| elem.same(first)).then_some(first);
                }
                Kind::Repeat { .. } | Kind::Concat { .. } => {}
            }
            if let Some(done) = memo.get(&key(node)) {
                return *done;
            }
            let answer = match &node.kind {
                Kind::Repeat { unit, .. } => go(unit, memo),
                Kind::Concat { left, right } => match (go(left, memo), go(right, memo)) {
                    (Some(a), Some(b)) if a.same(b) => Some(a),
                    _ => None,
                },
                Kind::Dense { .. } | Kind::Uniform(_) => unreachable!("answered above"),
            };
            memo.insert(key(node), answer);
            answer
        }
        go(self.root.as_ref()?, &mut HashMap::new())
    }

    /// The first element satisfying `pred`, with its index. Structural: a
    /// uniform run is asked once, a repeat's first copy answers for all, and
    /// each shared node is searched once.
    pub(crate) fn find_first(&self, mut pred: impl FnMut(&T) -> bool) -> Option<(u64, &T)> {
        fn go<'a, T>(
            node: &'a Link<T>,
            pred: &mut impl FnMut(&T) -> bool,
            memo: &mut HashMap<usize, Option<(u64, &'a T)>>,
        ) -> Option<(u64, &'a T)> {
            match &node.kind {
                Kind::Uniform(value) => return pred(value).then_some((0, value)),
                Kind::Dense { data, start } => {
                    return data[*start..*start + node.len as usize]
                        .iter()
                        .enumerate()
                        .find(|(_, elem)| pred(elem))
                        .map(|(index, elem)| (index as u64, elem));
                }
                Kind::Repeat { .. } | Kind::Concat { .. } => {}
            }
            if let Some(done) = memo.get(&key(node)) {
                return *done;
            }
            let answer = match &node.kind {
                Kind::Repeat { unit, .. } => go(unit, pred, memo),
                Kind::Concat { left, right } => go(left, pred, memo).or_else(|| {
                    go(right, pred, memo).map(|(index, elem)| (index + left.len, elem))
                }),
                Kind::Dense { .. } | Kind::Uniform(_) => unreachable!("answered above"),
            };
            memo.insert(key(node), answer);
            answer
        }
        go(self.root.as_ref()?, &mut pred, &mut HashMap::new())
    }

    /// Visit every STORED element once per node that stores it (a uniform
    /// run's element once, a repeat's unit once, a shared node once), until
    /// `visit` breaks. O(nodes + literal elements), never O(len).
    pub(crate) fn try_for_each_stored<'a, B>(
        &'a self,
        mut visit: impl FnMut(&'a T) -> core::ops::ControlFlow<B>,
    ) -> core::ops::ControlFlow<B> {
        let mut seen: HashSet<usize> = HashSet::new();
        let mut stack: Vec<&'a Link<T>> = self.root.iter().collect();
        while let Some(node) = stack.pop() {
            if !seen.insert(key(node)) {
                continue;
            }
            match &node.kind {
                Kind::Dense { data, start } => {
                    for elem in &data[*start..*start + node.len as usize] {
                        visit(elem)?;
                    }
                }
                Kind::Uniform(value) => visit(value)?,
                Kind::Repeat { unit, .. } => stack.push(unit),
                Kind::Concat { left, right } => {
                    stack.push(right);
                    stack.push(left);
                }
            }
        }
        core::ops::ControlFlow::Continue(())
    }

    /// Map every stored element (each stored element once; the shape is
    /// kept). O(nodes + literal elements).
    pub(crate) fn try_map<U: RopeElem, E>(
        &self,
        mut map: impl FnMut(&T) -> Result<U, E>,
    ) -> Result<Rope<U>, E> {
        let mut memo = HashMap::new();
        Ok(Rope {
            root: match &self.root {
                Some(root) => Some(map_node(root, &mut map, &mut memo)?),
                None => None,
            },
        })
    }

    /// Map every element to a rope and concatenate the results, structurally:
    /// a uniform run maps its element once and repeats the result, a repeat
    /// maps its unit once, a shared node is mapped once.
    pub(crate) fn try_flat_map<U: RopeElem, E>(
        &self,
        mut map: impl FnMut(&T) -> Result<Rope<U>, E>,
    ) -> Result<Rope<U>, E> {
        fn go<T: RopeElem, U: RopeElem, E>(
            node: &Link<T>,
            map: &mut impl FnMut(&T) -> Result<Rope<U>, E>,
            memo: &mut HashMap<usize, Rope<U>>,
        ) -> Result<Rope<U>, E> {
            if let Some(done) = memo.get(&key(node)) {
                return Ok(done.clone());
            }
            let mapped = match &node.kind {
                Kind::Dense { data, start } => Rope::concat(
                    data[*start..*start + node.len as usize]
                        .iter()
                        .map(&mut *map)
                        .collect::<Result<Vec<_>, E>>()?,
                ),
                Kind::Uniform(value) => map(value)?.repeat(node.len),
                Kind::Repeat { unit, count } => go(unit, map, memo)?.repeat(*count),
                Kind::Concat { left, right } => {
                    let left = go(left, map, memo)?;
                    let right = go(right, map, memo)?;
                    left.append(&right)
                }
            };
            memo.insert(key(node), mapped.clone());
            Ok(mapped)
        }
        match &self.root {
            Some(root) => go(root, &mut map, &mut HashMap::new()),
            None => Ok(Rope::empty()),
        }
    }

    /// Element-wise combination under one stable ordered-pair callback.
    /// Original borrowed windows preserve memo identity across differing shapes
    /// and cyclic phases. Successful results retain their exact logical extent;
    /// aliasing never substitutes for calling `zip`. Errors are left-to-right.
    /// Joint periods realign every `lcm(p, q)` elements, with a clipped tail.
    /// Callbacks may count work but must return the same result for a fixed pair.
    pub(crate) fn try_zip_with<U: RopeElem, V: RopeElem, E>(
        &self,
        other: &Rope<U>,
        mut zip: impl FnMut(&T, &U) -> Result<V, E>,
    ) -> Result<Rope<V>, E> {
        assert_eq!(self.len(), other.len(), "zipped ropes have one length");
        let (Some(a), Some(b)) = (&self.root, &other.root) else {
            return Ok(Rope::empty());
        };
        Ok(Rope {
            root: Some(zip_window(
                RopeWindow::whole(a),
                RopeWindow::whole(b),
                &mut zip,
                &mut HashMap::new(),
            )?),
        })
    }

    /// Element-wise equality under a stable pair predicate. Borrowed windows
    /// retain original node identity across splits and periodic phases; no
    /// temporary sliced rope supplies a memo key. Literal periods compare all
    /// distinct ordered alignments, without assuming predicate transitivity.
    pub(crate) fn eq_by<U: RopeElem>(
        &self,
        other: &Rope<U>,
        mut eq: impl FnMut(&T, &U) -> bool,
    ) -> bool {
        if self.len() != other.len() {
            return false;
        }
        match (&self.root, &other.root) {
            (Some(a), Some(b)) => eq_window(
                RopeWindow::whole(a),
                RopeWindow::whole(b),
                &mut eq,
                &mut HashMap::new(),
            ),
            _ => true,
        }
    }

    /// The rope of `self.len() / stride` values whose `j`-th is
    /// `decode(self[j * stride .. (j + 1) * stride])`. `self.len()` must be a
    /// multiple of `stride > 0`.
    ///
    /// STRUCTURAL: each node is walked once per distinct phase (offset modulo
    /// `stride`) it starts at; a uniform run decodes its chunk once; a repeat
    /// whose period divides or is divided by the stride decodes one period;
    /// in general a repeat of a `u`-element unit decodes `min(u, stride) /
    /// gcd(u, stride)` pieces and repeats them, because the chunks repeat
    /// every `lcm(u, stride)` elements. Only literal elements are decoded one
    /// chunk at a time.
    pub(crate) fn chunk_map<R: RopeElem, E>(
        &self,
        stride: u64,
        decode: &mut dyn FnMut(&Rope<T>) -> Result<R, E>,
    ) -> Result<Rope<R>, E> {
        assert!(stride > 0, "chunks have a positive width");
        assert_eq!(self.len() % stride, 0, "the rope is whole chunks");
        let Some(root) = &self.root else {
            return Ok(Rope::empty());
        };
        let mut walk = ChunkWalk {
            stride,
            decode,
            memo: HashMap::new(),
        };
        match walk.walk(root, 0)? {
            Piece::Spans {
                pre: None,
                mid,
                suf: None,
            } => Ok(Rope { root: mid }),
            _ => unreachable!("a rope of whole chunks starts and ends on a boundary"),
        }
    }

    /// Every element, in order. O(len): for callers that asked for all of
    /// them (a scalar's bytes, a bounded vector, tests).
    pub(crate) fn to_vec(&self) -> Vec<T> {
        self.iter().cloned().collect()
    }

    /// Every element, in order, by reference. O(len) to exhaust.
    pub(crate) fn iter(&self) -> impl Iterator<Item = &T> + '_ {
        // A stack of (node, copies of it still to emit).
        let mut stack: Vec<(&Node<T>, u64)> = self.root.iter().map(|root| (&**root, 1)).collect();
        let mut window: core::slice::Iter<'_, T> = [].iter();
        let mut uniform: Option<(&T, u64)> = None;
        core::iter::from_fn(move || {
            loop {
                if let Some(elem) = window.next() {
                    return Some(elem);
                }
                if let Some((value, left)) = &mut uniform
                    && *left > 0
                {
                    *left -= 1;
                    return Some(*value);
                }
                let (node, copies) = stack.pop()?;
                if copies > 1 {
                    stack.push((node, copies - 1));
                }
                match &node.kind {
                    Kind::Dense { data, start } => {
                        window = data[*start..*start + node.len as usize].iter();
                    }
                    Kind::Uniform(value) => uniform = Some((value, node.len)),
                    Kind::Repeat { unit, count } => stack.push((&**unit, *count)),
                    Kind::Concat { left, right } => {
                        stack.push((&**right, 1));
                        stack.push((&**left, 1));
                    }
                }
            }
        })
    }

    /// The number of distinct stored nodes (for structural-size assertions).
    #[cfg(test)]
    pub(crate) fn node_count(&self) -> usize {
        let mut seen = HashSet::new();
        let mut stack: Vec<&Link<T>> = self.root.iter().collect();
        while let Some(node) = stack.pop() {
            if !seen.insert(key(node)) {
                continue;
            }
            match &node.kind {
                Kind::Repeat { unit, .. } => stack.push(unit),
                Kind::Concat { left, right } => {
                    stack.push(left);
                    stack.push(right);
                }
                Kind::Dense { .. } | Kind::Uniform(_) => {}
            }
        }
        seen.len()
    }

    #[cfg(test)]
    pub(crate) fn height(&self) -> u32 {
        self.root.as_ref().map_or(0, |root| root.height)
    }

    pub(crate) fn root_node(&self) -> Option<NodeRef<'_, T>> {
        self.root.as_deref().map(NodeRef)
    }

    pub(crate) fn root_key(&self) -> Option<usize> {
        self.root_node().map(NodeRef::key)
    }

    /// Borrow each distinct stored node once, preserving periodic units and
    /// shared edges. No element or node is cloned and no repetition is expanded.
    pub(crate) fn structure(&self) -> Structure<'_, T> {
        fn visit<'a, T>(
            node: &'a Link<T>,
            nodes: &mut Vec<StructureNode<'a, T>>,
            keys: &mut Vec<usize>,
            seen: &mut HashMap<usize, usize>,
        ) -> usize {
            if let Some(&index) = seen.get(&key(node)) {
                return index;
            }
            let observed = match &node.kind {
                Kind::Dense { data, start } => {
                    StructureNode::Dense(&data[*start..*start + node.len as usize])
                }
                Kind::Uniform(value) => StructureNode::Uniform {
                    len: node.len,
                    value,
                },
                Kind::Repeat { unit, count } => StructureNode::Repeat {
                    unit: visit(unit, nodes, keys, seen),
                    count: *count,
                },
                Kind::Concat { left, right } => StructureNode::Concat {
                    left: visit(left, nodes, keys, seen),
                    right: visit(right, nodes, keys, seen),
                },
            };
            let index = nodes.len();
            nodes.push(observed);
            keys.push(key(node));
            seen.insert(key(node), index);
            index
        }
        let mut nodes = Vec::new();
        let mut keys = Vec::new();
        let root = self
            .root
            .as_ref()
            .map(|node| visit(node, &mut nodes, &mut keys, &mut HashMap::new()));
        Structure { nodes, keys, root }
    }

    /// The rope's STRUCTURE, never its elements one by one: a uniform run as
    /// `value x len`, a repeat as `(unit) x count`, and a node already
    /// printed as `<shared, len>` (so a DAG prints in O(distinct nodes)).
    pub(crate) fn fmt_structure(
        &self,
        f: &mut core::fmt::Formatter<'_>,
        elem: &dyn Fn(&T, &mut core::fmt::Formatter<'_>) -> core::fmt::Result,
    ) -> core::fmt::Result {
        fn go<T>(
            node: &Link<T>,
            f: &mut core::fmt::Formatter<'_>,
            elem: &dyn Fn(&T, &mut core::fmt::Formatter<'_>) -> core::fmt::Result,
            first: &mut bool,
            seen: &mut HashSet<usize>,
        ) -> core::fmt::Result {
            let mut sep = |f: &mut core::fmt::Formatter<'_>| {
                if !core::mem::replace(first, false) {
                    f.write_str(", ")?;
                }
                Ok::<(), core::fmt::Error>(())
            };
            match &node.kind {
                Kind::Dense { data, start } => {
                    for value in &data[*start..*start + node.len as usize] {
                        sep(f)?;
                        elem(value, f)?;
                    }
                    Ok(())
                }
                Kind::Uniform(value) => {
                    sep(f)?;
                    elem(value, f)?;
                    if node.len > 1 {
                        write!(f, " x {}", node.len)?;
                    }
                    Ok(())
                }
                Kind::Repeat { .. } | Kind::Concat { .. } if !seen.insert(key(node)) => {
                    sep(f)?;
                    write!(f, "<shared, {} elements>", node.len)
                }
                Kind::Repeat { unit, count } => {
                    sep(f)?;
                    f.write_str("(")?;
                    let mut inner_first = true;
                    go(unit, f, elem, &mut inner_first, seen)?;
                    write!(f, ") x {count}")
                }
                Kind::Concat { left, right } => {
                    go(left, f, elem, first, seen)?;
                    go(right, f, elem, first, seen)
                }
            }
        }
        f.write_str("[")?;
        if let Some(root) = &self.root {
            go(root, f, elem, &mut true, &mut HashSet::new())?;
        }
        f.write_str("]")
    }
}

fn map_node<T: RopeElem, U: RopeElem, E>(
    node: &Link<T>,
    map: &mut impl FnMut(&T) -> Result<U, E>,
    memo: &mut HashMap<usize, Link<U>>,
) -> Result<Link<U>, E> {
    if let Some(done) = memo.get(&key(node)) {
        return Ok(Arc::clone(done));
    }
    let mapped = match &node.kind {
        Kind::Dense { data, start } => {
            let elems = data[*start..*start + node.len as usize]
                .iter()
                .map(&mut *map)
                .collect::<Result<Vec<U>, E>>()?;
            let len = elems.len();
            dense_node(Arc::new(elems), 0, len)
        }
        Kind::Uniform(value) => uniform_node(map(value)?, node.len),
        Kind::Repeat { unit, count } => {
            repeat_node(map_node(unit, map, memo)?, *count).expect("a repeat has copies")
        }
        Kind::Concat { left, right } => {
            let left = map_node(left, map, memo)?;
            let right = map_node(right, map, memo)?;
            join(left, right)
        }
    };
    memo.insert(key(node), Arc::clone(&mapped));
    Ok(mapped)
}

/// Results retain their full extent. Both input roots stay borrowed for the
/// operation, so these original-node addresses cannot be retired or reused.
type ZipMemo<V> = HashMap<(WindowKey, WindowKey), Link<V>>;

fn zip_window<T: RopeElem, U: RopeElem, V: RopeElem, E>(
    a: RopeWindow<'_, T>,
    b: RopeWindow<'_, U>,
    zip: &mut impl FnMut(&T, &U) -> Result<V, E>,
    memo: &mut ZipMemo<V>,
) -> Result<Link<V>, E> {
    debug_assert_eq!(a.len, b.len);
    let a = a.normalize();
    let b = b.normalize();
    let identity = (a.exact_key(), b.exact_key());
    if let Some(done) = memo.get(&identity) {
        return Ok(Arc::clone(done));
    }
    let zipped = if let (Kind::Uniform(x), Kind::Uniform(y)) = (&a.node.kind, &b.node.kind) {
        uniform_node(zip(x, y)?, a.len)
    } else if let Some(period) = lcm_below(a.period(), b.period(), a.len) {
        // The normalized inputs realign after this period, including windows
        // with a phase and a final incomplete copy. Only OUTPUT is sliced;
        // memo keys always refer to the original borrowed inputs.
        let one = zip_window(a.slice(0, period), b.slice(0, period), zip, memo)?;
        let copies = repeat_node(Arc::clone(&one), a.len / period).expect("nonempty copies");
        match slice_node(&one, 0, a.len % period) {
            Some(tail) => join(copies, tail),
            None => copies,
        }
    } else if a.literal_run().is_some_and(|run| a.len <= run)
        && b.literal_run().is_some_and(|run| b.len <= run)
    {
        // At least one side is a paid-for dense literal (uniform/uniform was
        // handled above). Never allocate a dense buffer for a logical repeat.
        let elems = (0..a.len)
            .map(|i| zip(a.leaf_at(i), b.leaf_at(i)))
            .collect::<Result<Vec<V>, E>>()?;
        let len = elems.len();
        dense_node(Arc::new(elems), 0, len)
    } else {
        // Halve cyclic and mismatched structured windows rather than peeling
        // one small period at a time. The left half completes first, preserving
        // the first error of the fixed ordered-pair callback.
        let cut = a.len / 2;
        debug_assert!(cut > 0);
        let left = zip_window(a.slice(0, cut), b.slice(0, cut), zip, memo)?;
        let right = zip_window(
            a.slice(cut, a.len - cut),
            b.slice(cut, b.len - cut),
            zip,
            memo,
        )?;
        join(left, right)
    };
    memo.insert(identity, Arc::clone(&zipped));
    Ok(zipped)
}

/// A cyclic window of an ORIGINAL borrowed node. Repeat nodes expose their
/// real unit plus phase; concatenations expose children only when the complete
/// window lies in one child. Both original roots stay borrowed for the entire
/// operation, so memo addresses cannot be retired or reused. Input slice nodes
/// are never allocated; output construction may slice a completed result. No
/// pointer equality substitutes for the real callback.
struct RopeWindow<'a, T> {
    node: &'a Node<T>,
    start: u64,
    len: u64,
}
impl<T> Copy for RopeWindow<'_, T> {}
impl<T> Clone for RopeWindow<'_, T> {
    fn clone(&self) -> Self {
        *self
    }
}

type WindowKey = (usize, u64, u64);
type EqualityMemo = HashMap<(WindowKey, WindowKey), bool>;

impl<'a, T> RopeWindow<'a, T> {
    fn whole(node: &'a Node<T>) -> Self {
        Self {
            node,
            start: 0,
            len: node.len,
        }
    }

    fn normalize(mut self) -> Self {
        loop {
            let node = self.node;
            debug_assert!(self.len > 0 && self.start < node.len);
            match &node.kind {
                Kind::Uniform(_) => {
                    self.start = 0;
                    return self;
                }
                Kind::Repeat { unit, .. } => {
                    self.start %= unit.len;
                    self.node = unit;
                }
                Kind::Concat { left, right } if self.len <= node.len - self.start => {
                    if self.start < left.len && self.len <= left.len - self.start {
                        self.node = left;
                    } else if self.start >= left.len {
                        self.start -= left.len;
                        self.node = right;
                    } else {
                        return self;
                    }
                }
                Kind::Dense { .. } | Kind::Concat { .. } => return self,
            }
        }
    }

    fn exact_key(self) -> WindowKey {
        (self.node as *const Node<T> as usize, self.start, self.len)
    }

    fn period(self) -> u64 {
        if matches!(self.node.kind, Kind::Uniform(_)) {
            1
        } else {
            self.node.len
        }
    }

    fn literal_run(self) -> Option<u64> {
        match self.node.kind {
            Kind::Uniform(_) => Some(u64::MAX),
            Kind::Dense { .. } => Some(self.node.len - self.start),
            Kind::Repeat { .. } | Kind::Concat { .. } => None,
        }
    }

    fn key(self) -> WindowKey {
        // A nonempty constant window has the same boolean comparison at
        // every extent. Other nodes retain the full dependent window length.
        let len = if matches!(self.node.kind, Kind::Uniform(_)) {
            1
        } else {
            self.len
        };
        (self.node as *const Node<T> as usize, self.start, len)
    }

    fn slice(self, offset: u64, len: u64) -> Self {
        debug_assert!(len > 0 && offset <= self.len && len <= self.len - offset);
        Self {
            node: self.node,
            start: ((u128::from(self.start) + u128::from(offset)) % u128::from(self.node.len))
                as u64,
            len,
        }
    }

    fn leaf_period(self) -> Option<u64> {
        match self.node.kind {
            Kind::Uniform(_) => Some(1),
            Kind::Dense { .. } => Some(self.node.len),
            Kind::Repeat { .. } | Kind::Concat { .. } => None,
        }
    }

    fn leaf_at(self, index: u64) -> &'a T {
        match &self.node.kind {
            Kind::Uniform(value) => value,
            Kind::Dense { data, start } => {
                let index =
                    (u128::from(self.start) + u128::from(index)) % u128::from(self.node.len);
                &data[*start + index as usize]
            }
            Kind::Repeat { .. } | Kind::Concat { .. } => unreachable!("normalized literal window"),
        }
    }
}

fn eq_window<T, U>(
    a: RopeWindow<'_, T>,
    b: RopeWindow<'_, U>,
    eq: &mut impl FnMut(&T, &U) -> bool,
    memo: &mut EqualityMemo,
) -> bool {
    debug_assert_eq!(a.len, b.len);
    let a = a.normalize();
    let b = b.normalize();
    let identity = (a.key(), b.key());
    if let Some(done) = memo.get(&identity) {
        return *done;
    }
    let answer = if let (Some(p), Some(q)) = (a.leaf_period(), b.leaf_period()) {
        // lcm fits u128 even if it exceeds the u64 logical length. A stable
        // ordered pair repeats after lcm; unlike Fine-Wilf this needs no
        // transitivity, reflexivity or symmetry assumption about the callback.
        let period = u128::from(p / gcd(p, q)) * u128::from(q);
        let count = u128::from(a.len).min(period) as u64;
        (0..count).all(|i| eq(a.leaf_at(i), b.leaf_at(i)))
    } else {
        // Halving the logical window bounds recursion by the u64 width even
        // when both original nodes are cyclic. Cutting one small unit at a
        // time would instead create a chain proportional to its repeat count.
        let cut = a.len / 2;
        debug_assert!(cut > 0);
        eq_window(a.slice(0, cut), b.slice(0, cut), eq, memo)
            && eq_window(
                a.slice(cut, a.len - cut),
                b.slice(cut, b.len - cut),
                eq,
                memo,
            )
    };
    memo.insert(identity, answer);
    answer
}

impl RopeElem for Option<u64> {
    const FRESH_LEAF: usize = SMALL_LEAF;
    fn same(&self, other: &Self) -> bool {
        self == other
    }
}

impl<A: RopeElem, B: RopeElem> RopeElem for (A, B) {
    const FRESH_LEAF: usize = SMALL_LEAF;
    fn same(&self, other: &Self) -> bool {
        self.0.same(&other.0) && self.1.same(&other.1)
    }
}

#[cfg(test)]
impl<T: RopeElem> Rope<T> {
    /// Every structural invariant: lengths and heights add up, every
    /// `Concat` is AVL-balanced, every `Repeat` has a normalized unit and at
    /// least two copies, and no node is empty.
    pub(crate) fn check_invariants(&self) {
        fn go<T>(node: &Link<T>) {
            assert!(node.len > 0, "no empty node");
            match &node.kind {
                Kind::Dense { data, start } => {
                    assert_eq!(node.height, 0);
                    assert!(start + node.len as usize <= data.len());
                }
                Kind::Uniform(_) => assert_eq!(node.height, 0),
                Kind::Repeat { unit, count } => {
                    assert!(*count >= 2, "a repeat has two or more copies");
                    assert!(
                        !matches!(unit.kind, Kind::Uniform(_) | Kind::Repeat { .. }),
                        "a repeat's unit is normalized"
                    );
                    assert!(
                        !matches!(unit.kind, Kind::Dense { .. }) || unit.len > 1,
                        "a one-element unit is a uniform run"
                    );
                    assert_eq!(node.len, unit.len * count);
                    assert_eq!(node.height, unit.height + ceil_log2(*count));
                    go(unit);
                }
                Kind::Concat { left, right } => {
                    assert_eq!(node.len, left.len + right.len);
                    assert_eq!(node.height, left.height.max(right.height) + 1);
                    assert!(
                        left.height.abs_diff(right.height) <= 1,
                        "AVL balance: {} vs {}",
                        left.height,
                        right.height
                    );
                    go(left);
                    go(right);
                }
            }
        }
        if let Some(root) = &self.root {
            go(root);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn phased_zip_input(
        phase: u64,
        len: u64,
        memo: &mut HashMap<(u64, u64), Rope<Option<u64>>>,
    ) -> Rope<Option<u64>> {
        if let Some(word) = memo.get(&(phase, len)) {
            return word.clone();
        }
        let word = if len <= 16 {
            Rope::dense((0..len).map(|i| Some((phase + i) % 3 + 1)).collect())
        } else {
            let cut = len / 2;
            Rope::concat([
                phased_zip_input(phase, cut, memo),
                phased_zip_input((phase + cut) % 3, len - cut, memo),
            ])
        };
        memo.insert((phase, len), word.clone());
        word
    }

    #[test]
    fn zip_reuses_original_shared_windows_against_periods() {
        for depth in [10, 40] {
            let count = (1 << depth) + 37;
            let shared = phased_zip_input(0, 3 * count, &mut HashMap::new());
            let topology = shared.structure();
            let mut incoming = vec![0; topology.nodes.len()];
            for node in &topology.nodes {
                match node {
                    StructureNode::Concat { left, right } => {
                        incoming[*left] += 1;
                        incoming[*right] += 1;
                    }
                    StructureNode::Repeat { unit, .. } => incoming[*unit] += 1,
                    StructureNode::Dense(_) | StructureNode::Uniform { .. } => {}
                }
            }
            assert!(
                topology.nodes.iter().enumerate().any(|(i, node)| {
                    matches!(node, StructureNode::Concat { .. }) && incoming[i] > 1
                }),
                "fixture must retain shared concat nodes"
            );
            let periodic = Rope::dense(vec![Some(4), Some(5), Some(6)]).repeat(count);
            let mut calls = 0;
            let zipped = shared
                .try_zip_with(&periodic, |a, b| {
                    calls += 1;
                    Ok::<_, ()>(Some(a.unwrap() + b.unwrap()))
                })
                .unwrap();
            let bound = if depth == 10 { 1024 } else { 8192 };
            assert!(calls < bound, "zip must reuse original windows: {calls}");
            assert_eq!(zipped.len(), 3 * count);
            assert!(zipped.node_count() < 8192, "result must remain shared");
            let expected = Rope::dense(vec![Some(5), Some(7), Some(9)]).repeat(count);
            assert!(zipped.eq_by(&expected, |a, b| a == b));
            let late = zipped.set(zipped.len() - 1, Some(99)).unwrap();
            assert!(!late.eq_by(&expected, |a, b| a == b));
        }
    }

    #[test]
    fn zip_cyclic_phases_tails_and_first_errors_match_dense_models() {
        let left = [Some(1_u64), Some(2)];
        let right = [Some(4_u64), Some(5), Some(6)];
        for len in 0_u64..100 {
            for phase_a in 0_u64..2 {
                for phase_b in 0_u64..3 {
                    let a = Rope::dense(left.to_vec())
                        .repeat((len + phase_a).div_ceil(2))
                        .slice(phase_a, len);
                    let b = Rope::dense(right.to_vec())
                        .repeat((len + phase_b).div_ceil(3))
                        .slice(phase_b, len);
                    let model: Vec<_> = (0..len)
                        .map(|i| {
                            (
                                left[((i + phase_a) % 2) as usize],
                                right[((i + phase_b) % 3) as usize],
                            )
                        })
                        .collect();
                    let zipped = a
                        .try_zip_with(&b, |x, y| Ok::<_, ()>(Some(x.unwrap() * 10 + y.unwrap())))
                        .unwrap();
                    zipped.check_invariants();
                    assert_eq!(
                        zipped.to_vec(),
                        model
                            .iter()
                            .map(|(x, y)| { Some(x.unwrap() * 10 + y.unwrap()) })
                            .collect::<Vec<_>>()
                    );
                    let fail = |x: &Option<u64>, y: &Option<u64>| {
                        if *x == Some(2) {
                            Err("left-two")
                        } else if *y == Some(6) {
                            Err("right-six")
                        } else {
                            Ok(Some(x.unwrap() + y.unwrap()))
                        }
                    };
                    let expected = model.iter().find_map(|(x, y)| fail(x, y).err());
                    assert_eq!(a.try_zip_with(&b, fail).err(), expected);
                }
            }
        }
    }

    #[test]
    fn zip_aliases_run_the_callback_and_keep_full_extents() {
        let value = Rope::uniform(Some(7_u64), u64::MAX);
        let mut calls = 0;
        let changed = value
            .try_zip_with(&value, |x, y| {
                calls += 1;
                Ok::<_, ()>(Some(x.unwrap() + y.unwrap()))
            })
            .unwrap();
        assert_eq!(calls, 1);
        assert_eq!(changed.len(), u64::MAX);
        assert_eq!(changed.as_uniform(), Some(&Some(14)));
        assert_eq!(
            value
                .try_zip_with(&value, |_, _| Err::<Option<u64>, _>("alias error"))
                .err(),
            Some("alias error")
        );
        let unit = Rope::concat([Rope::uniform(Some(1_u64), 23), Rope::uniform(Some(2), 31)]);
        let a = unit.repeat(19).slice(7, 1001);
        let b = Rope::uniform(Some(3_u64), 1001);
        let zipped = a
            .try_zip_with(&b, |x, y| Ok::<_, ()>(Some(x.unwrap() + y.unwrap())))
            .unwrap();
        assert_eq!(zipped.len(), 1001);
        assert_eq!(
            zipped.to_vec(),
            a.iter().map(|v| Some(v.unwrap() + 3)).collect::<Vec<_>>()
        );
    }

    /// A deterministic xorshift generator (the crate has no test-only
    /// randomness dependency).
    struct Rng(u64);

    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0
        }
        fn below(&mut self, bound: u64) -> u64 {
            self.next() % bound.max(1)
        }
        /// A byte state from a small alphabet, so uniform runs occur.
        fn byte(&mut self) -> Option<u8> {
            match self.below(4) {
                0 => None,
                n => Some(n as u8),
            }
        }
    }

    type Model = Vec<Option<u8>>;

    /// A random rope built by a random sequence of the constructors, with
    /// its dense model.
    fn gen_rope(rng: &mut Rng, depth: u32) -> (Rope<Option<u8>>, Model) {
        let choice = if depth == 0 {
            rng.below(2)
        } else {
            rng.below(7)
        };
        match choice {
            0 => {
                let len = rng.below(8) as usize;
                let model: Model = (0..len).map(|_| rng.byte()).collect();
                (Rope::dense(model.clone()), model)
            }
            1 => {
                let len = rng.below(20);
                let byte = rng.byte();
                (Rope::uniform(byte, len), vec![byte; len as usize])
            }
            2 => {
                let (rope, model) = gen_rope(rng, depth - 1);
                let count = rng.below(5);
                let repeated = model.repeat(count as usize);
                (rope.repeat(count), repeated)
            }
            3 => {
                let parts: Vec<_> = (0..2 + rng.below(3))
                    .map(|_| gen_rope(rng, depth - 1))
                    .collect();
                let model = parts.iter().flat_map(|(_, m)| m.clone()).collect();
                (Rope::concat(parts.into_iter().map(|(r, _)| r)), model)
            }
            4 => {
                let (rope, model) = gen_rope(rng, depth - 1);
                let start = rng.below(model.len() as u64 + 1);
                let len = rng.below(model.len() as u64 - start + 1);
                (
                    rope.slice(start, len),
                    model[start as usize..(start + len) as usize].to_vec(),
                )
            }
            5 => {
                let (rope, mut model) = gen_rope(rng, depth - 1);
                if model.is_empty() {
                    return (rope, model);
                }
                let index = rng.below(model.len() as u64);
                let byte = rng.byte();
                model[index as usize] = byte;
                (rope.set(index, byte).expect("in bounds"), model)
            }
            _ => {
                // A rope and a copy of itself, joined: the shape a doubling
                // memory copy builds.
                let (rope, model) = gen_rope(rng, depth - 1);
                let doubled = Rope::concat([rope.clone(), rope]);
                (doubled, model.repeat(2))
            }
        }
    }

    #[derive(Clone, Debug, PartialEq)]
    struct Chunk(Model);

    impl RopeElem for Chunk {
        const FRESH_LEAF: usize = SMALL_LEAF;
        fn same(&self, other: &Self) -> bool {
            self == other
        }
    }

    fn check_against_model(rope: &Rope<Option<u8>>, model: &Model, rng: &mut Rng) {
        rope.check_invariants();
        assert_eq!(rope.len(), model.len() as u64);
        assert_eq!(&rope.to_vec(), model);
        assert!(rope.iter().eq(model.iter()));
        for (index, byte) in model.iter().enumerate() {
            assert_eq!(rope.get(index as u64), Some(byte));
        }
        assert_eq!(rope.get(model.len() as u64), None);
        let uniform = model
            .first()
            .filter(|first| model.iter().all(|byte| byte == *first));
        assert_eq!(rope.all_same(), uniform);
        let target = rng.byte();
        assert_eq!(
            rope.find_first(|byte| *byte == target)
                .map(|(index, byte)| (index, *byte)),
            model
                .iter()
                .position(|byte| *byte == target)
                .map(|index| (index as u64, target))
        );
        // A dense spelling of the same bytes is equal; one changed byte is not.
        let dense = Rope::dense(model.clone());
        assert!(rope.eq_by(&dense, |a, b| a == b));
        assert!(dense.eq_by(rope, |a, b| a == b));
        if !model.is_empty() {
            let index = rng.below(model.len() as u64);
            let other = if model[index as usize] == Some(9) {
                None
            } else {
                Some(9)
            };
            let changed = rope.set(index, other).expect("in bounds");
            assert!(!rope.eq_by(&changed, |a, b| a == b));
        }
        // Chunks of every stride that divides the length.
        for stride in 1..=model.len().min(24) as u64 {
            if !(model.len() as u64).is_multiple_of(stride) {
                continue;
            }
            let mut decodes = 0usize;
            let chunks = rope
                .chunk_map(stride, &mut |chunk: &Rope<Option<u8>>| {
                    decodes += 1;
                    chunk.check_invariants();
                    Ok::<_, ()>(Chunk(chunk.to_vec()))
                })
                .expect("infallible");
            chunks.check_invariants();
            let expected: Vec<Chunk> = model
                .chunks(stride as usize)
                .map(|chunk| Chunk(chunk.to_vec()))
                .collect();
            assert_eq!(chunks.to_vec(), expected, "stride {stride}");
            assert!(decodes <= expected.len() + 2 * rope.node_count_for_tests());
        }
        // Zip with a reversed-structure rope of the same length.
        let reversed: Model = model.iter().rev().copied().collect();
        let other = Rope::concat(reversed.chunks(3).map(|chunk| Rope::dense(chunk.to_vec())));
        let zipped = rope
            .try_zip_with(&other, |a, b| Ok::<_, ()>((*a, *b)))
            .expect("infallible");
        zipped.check_invariants();
        let pairs: Vec<(Option<u8>, Option<u8>)> = model
            .iter()
            .copied()
            .zip(reversed.iter().copied())
            .collect();
        assert_eq!(zipped.to_vec(), pairs);
        // Flat-map every byte to a two-byte rope.
        let flat = rope
            .try_flat_map(|byte| Ok::<_, ()>(Rope::dense(vec![*byte, None])))
            .expect("infallible");
        flat.check_invariants();
        let expected: Model = model.iter().flat_map(|byte| [*byte, None]).collect();
        assert_eq!(flat.to_vec(), expected);
    }

    impl<T: RopeElem> Rope<T> {
        fn node_count_for_tests(&self) -> usize {
            self.node_count()
        }
    }

    #[test]
    fn random_ropes_agree_with_a_dense_model() {
        let mut rng = Rng(0x9E37_79B9_7F4A_7C15);
        for _ in 0..3000 {
            let (rope, model) = gen_rope(&mut rng, 5);
            check_against_model(&rope, &model, &mut rng);
        }
    }

    #[test]
    fn random_rope_pairs_compare_like_their_models() {
        let mut rng = Rng(0xD1B5_4A32_D192_ED03);
        for _ in 0..3000 {
            let (a, model_a) = gen_rope(&mut rng, 4);
            let (b, model_b) = gen_rope(&mut rng, 4);
            assert_eq!(a.eq_by(&b, |x, y| x == y), model_a == model_b);
            if model_a.len() == model_b.len() {
                let zipped = a
                    .try_zip_with(&b, |x, y| Ok::<_, ()>((*x, *y)))
                    .expect("infallible");
                let expected: Vec<_> = model_a
                    .iter()
                    .copied()
                    .zip(model_b.iter().copied())
                    .collect();
                assert_eq!(zipped.to_vec(), expected);
            }
        }
        // Two periodic spellings of one sequence, at u64 lengths: compare
        // all distinct literal-period alignments, without expanding repeats.
        let pair = Rope::dense(vec![Some(1u8), Some(2)]);
        let six = Rope::dense([Some(1u8), Some(2)].repeat(3));
        let n = 1u64 << 40;
        assert!(pair.repeat(3 * n).eq_by(&six.repeat(n), |a, b| a == b));
        let triple = Rope::dense(vec![Some(1u8), Some(2), Some(1)]);
        assert!(
            !pair
                .repeat(3 * n)
                .eq_by(&triple.repeat(2 * n), |a, b| a == b)
        );
    }

    /// Chunking a periodic rope at a stride its period does not divide
    /// decodes one period of chunks, never one per chunk (reviewer finding,
    /// 2026-09-23: a stored `[u16; N]` read back as `[u8; 2N]`, or
    /// `[[u8; 3]; N]` as `[u8; 3N]`).
    #[test]
    fn chunking_a_repeat_decodes_one_period() {
        let n = 1u64 << 40;
        for (unit, stride, period) in [
            (vec![Some(1u8), Some(2)], 1u64, 2usize),
            (vec![Some(1), Some(2), Some(3)], 1, 3),
            (vec![Some(1), Some(2), Some(3)], 2, 3),
            (vec![Some(1), Some(2), Some(3), Some(4)], 6, 2),
            (vec![Some(1), Some(2)], 4, 1),
        ] {
            let unit_len = unit.len() as u64;
            let rope = Rope::dense(unit.clone()).repeat(n * stride);
            let mut decodes = 0usize;
            let chunks = rope
                .chunk_map(stride, &mut |chunk: &Rope<Option<u8>>| {
                    decodes += 1;
                    Ok::<_, ()>(Chunk(chunk.to_vec()))
                })
                .expect("infallible");
            assert_eq!(chunks.len(), n * unit_len);
            assert!(
                decodes <= 2 * period + 2,
                "{decodes} decodes, unit {unit:?} stride {stride}"
            );
            assert!(
                chunks.node_count() <= 4 * 64,
                "{} nodes",
                chunks.node_count()
            );
            let last = chunks.get(n * unit_len - 1).expect("in bounds").0.clone();
            let expected: Model = (0..stride)
                .map(|k| unit[((n * unit_len * stride - stride + k) % unit_len) as usize])
                .collect();
            assert_eq!(last, expected);
        }
    }

    /// A unit LONGER than the stride with structure inside it (a long
    /// uniform run and one marker byte) is walked on its own structure at
    /// each phase: O(unit structure), not O(unit length).
    #[test]
    fn chunking_a_long_structured_unit_walks_its_structure() {
        let marker = Rope::dense(vec![Some(2)]);
        let unit = Rope::concat([Rope::uniform(Some(1), 1 << 20), marker]);
        let rope = unit.repeat(1 << 30);
        let mut decodes = 0usize;
        let chunks = rope
            .chunk_map(2, &mut |chunk: &Rope<Option<u8>>| {
                decodes += 1;
                Ok::<_, ()>(Chunk(chunk.to_vec()))
            })
            .expect("infallible");
        assert_eq!(chunks.len(), ((1u64 << 20) + 1) * (1 << 29));
        assert!(decodes <= 16, "{decodes} decodes");
        assert_eq!(chunks.get(0).unwrap().0, vec![Some(1), Some(1)]);
        // Element (2^20)/2 straddles the first marker: [2, 1].
        assert_eq!(chunks.get(1 << 19).unwrap().0, vec![Some(2), Some(1)]);
    }
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The module layout table: every nominal layout laid out once.
//!
//! [`Module::ty_layout_shape`] used to recurse through every field layout
//! with no memo. A type that shares a sub-type (`P{k+1} = {Pk, Pk}`) was laid
//! out once per PATH, `2^k` times (161 ms at depth 20 in a release build,
//! doubling per level), and a chain paid a linear struct-table scan and a
//! linear cycle-guard scan per level, on a native stack frame per level (a
//! 4096-deep chain overflowed a 2 MiB stack).
//!
//! A [`LayoutTable`] lays out each NOMINAL node at most once:
//!
//! * a struct (the first [`crate::ty::StructDef`] with its id),
//! * an enum (the first [`crate::ty::EnumDef`] with its id),
//! * a type-table entry reached by value (an `Array` element or a `Refine`
//!   base), and
//! * a declared tuple layout ([`crate::TupleLayoutDescriptor`]), and
//! * a declared closure layout ([`crate::ClosureLayoutDescriptor`], wire v58).
//!
//! Nodes are laid out bottom-up on an explicit stack (no recursion, so no
//! depth limit) and the id lookups are hash maps, so a query costs O(the part
//! of the type graph it reaches that the table has not laid out yet), and a
//! table that answers every query of a module does O(total fields) work over
//! its lifetime (the per-definition overlap test sorts, O(f log f) for `f`
//! fields; the first-definition index reads each struct and enum row at most
//! once, the tuple and closure indexes each declared row once, and the
//! inhabitedness memo
//! each definition once). [`LayoutTableStats`] counts all of it.
//!
//! # Identical results, cycles included
//!
//! The table returns exactly what the unmemoized recursion returned, for
//! every query, in any order (the conformance test `layout_table_differential`
//! keeps the recursion as its oracle), with one deliberate exception: the
//! niche rule's inhabitedness question on a cyclic reach (see Inhabitedness).
//! Memoizing that walk is exact even though its cycle refusals depend on
//! where the walk entered:
//!
//! 1. Every arm passes a field's error up unchanged, so a query's answer is
//!    the first failure in walk order, or the layout.
//! 2. A node that lays out reaches no by-value cycle, hence no node of the
//!    path that entered it, so its layout is the same from every path.
//! 3. A failure met without re-entering an open node — a node's own check,
//!    or the recorded answer of a node laid out earlier — is what every node
//!    on the current path answers from any path: what they reached before it
//!    laid out, and what it consulted is all laid out already.
//!
//! A re-entry is the one failure that depends on the path. When the walk
//! re-enters an OPEN node `g` (one on the current path), the path from `g` to
//! the top is a cycle: each node on it reached the next through its first
//! field that did not lay out, and which field that is does not depend on the
//! path (2). So `g` and every node BELOW it on the path fail with `g`'s
//! re-entry error, while each node ABOVE `g` fails with ITS OWN re-entry
//! error: entered first, it walks the same cycle back to itself. `unwind`
//! records exactly that, so no node is ever laid out twice and every later
//! query reads the answer the recursion would have computed. The colouring
//! is the slot state: absent (white), `Slot::Open` (grey), laid out
//! (black).
//!
//! # Inhabitedness
//!
//! A `Niche` descriptor must encode every INHABITED variant, so laying out a
//! niche enum asks which variants are uninhabited. The table keeps those
//! verdicts too (the least solution of the inhabitedness equations, see
//! [`Module::ty_is_uninhabited`]), each node decided once over the table's
//! lifetime on a heap stack, so the question costs O(what it reaches that no
//! earlier question decided) and never recurses. The same memo answers
//! [`LayoutTable::ty_is_uninhabited`] and
//! [`LayoutTable::variant_is_uninhabited`]. Where the question's reach has no
//! cycle this is exactly the verdict of the recursion it replaced. A niche
//! enum's fields all laid out, so its question can meet a cycle only through
//! a later definition of a duplicate id, which the walk never lays out; there
//! that recursion's verdict depended on the order it met the cycle, and the
//! least solution is never below it and the same in every order.
//!
//! # Reachability
//!
//! The layout-sensitive cast rule asks, before any layout, whether a side
//! reaches a handle, holds a closure by value or stores a bool lane,
//! following table references. Those are reachability questions, decided by
//! the table's reachability memo (the private `reach` module) once per node
//! and predicate over the table's lifetime
//! ([`LayoutTable::type_reaches_handle`],
//! [`LayoutTable::type_holds_closure_by_value`],
//! [`LayoutTable::type_stores_bool_lane`]), so a pass judging every cast of a
//! module through one table does O(total fields) work for them too.
//!
//! # Sharing
//!
//! The memo sits behind a [`Mutex`], so one table can serve a parallel pass
//! (the validator's per-function section asks one table from every worker),
//! and it holds no borrow of the module ([`LayoutMemo`]), so a caller that
//! holds the module mutably — a function builder sizing each `Alloca` — can
//! keep it between questions and lend it back.

use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::hash::Hash;
use std::sync::{Arc, Mutex, MutexGuard};

use crate::inhabit::InhabitMemo;
use crate::reach::{Reach, ReachMemo};
use crate::shape::{
    EnumLayoutShape, FieldOffsetShape, LayoutError, TyLayoutKind, TyLayoutShape, TyShape,
    align_up_bits, any_byte_ranges_overlap, byte_ranges_overlap, leaf_layout,
    ty_uses_scalar_layout_table,
};
use crate::ty::{
    EnumDef, EnumTagEncoding, EnumTagRepr, EnumVariant, FieldDef, StructDef, StructRepr, Ty,
};
use crate::value::{ClosureTyId, EnumId, StructId, TyId};
use crate::{ClosureLayoutDescriptor, Module, TupleLayoutDescriptor};

mod observed;

/// A failure, shared: a node that fails because a field failed records the
/// field's failure, not a copy of it.
type Failure = Arc<LayoutError>;

/// A layout or a failure, both shared.
type Laid = Result<Arc<TyLayoutShape>, Failure>;

/// The layouts of one module's types, each nominal node laid out at most once.
///
/// [`Module::ty_layout_shape`] and [`Module::enum_layout_shape`] build a table
/// per call, which costs one query's reach. A caller that asks many layout
/// questions of one module (a validator pass, a translation that sizes every
/// access) builds one table with [`Module::layout_table`] and asks it, so the
/// whole module costs O(total fields). The answers are exactly the
/// [`Module`] methods' answers (see the module docs).
///
/// The table borrows the module, so it cannot outlive an edit of it. It is
/// `Sync`: its memo sits behind a [`Mutex`], so threads can share one table.
pub struct LayoutTable<'m> {
    module: &'m Module,
    pointer_bits: u32,
    canonical_scalars: bool,
    // Observed queries own independent memo-free Work. None keeps even cold
    // randomized hash-map/TLS entropy setup outside the observed constructor;
    // the exact old ordinary memo is initialized only by ordinary queries.
    memo: Mutex<Option<Memo>>,
}

impl core::fmt::Debug for LayoutTable<'_> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("LayoutTable")
            .field("module", &self.module.name)
            .field("pointer_bits", &self.pointer_bits)
            .field("canonical_scalars", &self.canonical_scalars)
            .field("stats", &self.stats())
            .finish()
    }
}

#[derive(Default)]
struct Memo {
    structs: FirstDef<StructId>,
    enums: FirstDef<EnumId>,
    tuples: Option<TupleIndex>,
    closures: Option<ClosureIndex>,
    nodes: HashMap<Node, Slot>,
    /// The off-table-target refusal, built once and shared by every scalar.
    scalar_refusal: Option<Failure>,
    /// Walk steps taken, for [`LayoutTable::stats`].
    steps: u64,
    /// The inhabitedness verdicts (the niche rule, and the table's own
    /// inhabitedness questions).
    inhabit: InhabitMemo,
    /// The cast rule's reachability verdicts (handle, closure by value, bool
    /// lane).
    reach: ReachMemo,
}

/// The work a [`LayoutTable`] has done. Every count is O(the module) however
/// many questions the table answered, so a test can hold the bound without a
/// clock:
///
/// * `nodes`: the nominal nodes laid out (each at most once);
/// * `steps`: the layout walk's steps — one per type entered, per layout
///   handed to a frame, and per failure;
/// * `definitions_indexed`: the struct and enum rows the first-definition
///   index has read (each at most once);
/// * `tuple_rows_indexed`: the declared tuple rows the tuple index has read
///   (each at most once);
/// * `closure_rows_indexed`: the declared closure rows the closure index has
///   read (each at most once);
/// * `inhabitedness_nodes`: the nodes whose inhabitedness is decided (each
///   once);
/// * `inhabitedness_steps`: the inhabitedness memo's nodes expanded, clauses
///   written, literals read and propagations made;
/// * `inhabitedness_rows_indexed`: the struct, record and enum rows its
///   all-definitions index has read (each at most once);
/// * `reach_nodes`: the reachability verdicts decided for the cast rule's
///   three predicates (each node once per predicate);
/// * `reach_steps`: the reachability memo's inline types scanned, nodes
///   expanded, member edges written and propagations made;
/// * `reach_rows_indexed`: the struct, record and enum rows the reachability
///   memo's all-definitions index has read (each at most once).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub struct LayoutTableStats {
    pub nodes: usize,
    pub steps: u64,
    pub definitions_indexed: usize,
    pub tuple_rows_indexed: usize,
    pub closure_rows_indexed: usize,
    pub inhabitedness_nodes: usize,
    pub inhabitedness_steps: u64,
    pub inhabitedness_rows_indexed: usize,
    pub reach_nodes: usize,
    pub reach_steps: u64,
    pub reach_rows_indexed: usize,
}

impl LayoutTableStats {
    const EMPTY: Self = Self {
        nodes: 0,
        steps: 0,
        definitions_indexed: 0,
        tuple_rows_indexed: 0,
        closure_rows_indexed: 0,
        inhabitedness_nodes: 0,
        inhabitedness_steps: 0,
        inhabitedness_rows_indexed: 0,
        reach_nodes: 0,
        reach_steps: 0,
        reach_rows_indexed: 0,
    };
}

/// A [`LayoutTable`]'s memo without its borrow of the module: what a caller
/// that holds the module MUTABLY (and so cannot keep a table borrowing it)
/// keeps between questions, lending it back with [`LayoutTable::with_memo`].
///
/// The memo's answers are about the module it was built over. Lend it only
/// to that module, with its type tables (`types`, `structs`, `enums`,
/// `records`, `tuple_layouts`, `closure_types`, `closure_layouts`, and for
/// the handle verdicts `func_types`) and target unchanged; a function
/// builder, which holds the module exclusively and edits only its own
/// function, is the case this is for. [`LayoutTable::with_memo`] starts
/// afresh when a table's length or the target's layout differs from the one
/// the memo was built over (an edit it can see), except that a longer or
/// shorter signature table drops only the reachability verdicts (no layout
/// reads a signature); it cannot see an edit in place.
pub struct LayoutMemo {
    memo: Memo,
    tables: Tables,
}

impl LayoutMemo {
    /// The work its tables have done so far (see [`LayoutTableStats`]).
    pub fn stats(&self) -> LayoutTableStats {
        self.memo.stats()
    }
}

impl Memo {
    fn stats(&self) -> LayoutTableStats {
        LayoutTableStats {
            nodes: self.nodes.len(),
            steps: self.steps,
            definitions_indexed: self.structs.scanned + self.enums.scanned,
            tuple_rows_indexed: self.tuples.as_ref().map_or(0, |tuples| tuples.read),
            closure_rows_indexed: self.closures.as_ref().map_or(0, |closures| closures.read),
            inhabitedness_nodes: self.inhabit.decided(),
            inhabitedness_steps: self.inhabit.steps,
            inhabitedness_rows_indexed: self.inhabit.rows_indexed,
            reach_nodes: self.reach.decided(),
            reach_steps: self.reach.steps,
            reach_rows_indexed: self.reach.defs.rows_indexed,
        }
    }
}

impl core::fmt::Debug for LayoutMemo {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("LayoutMemo")
            .field("stats", &self.memo.stats())
            .field("tables", &self.tables)
            .finish()
    }
}

/// The table lengths and target layout a memo was built over.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Tables {
    types: usize,
    structs: usize,
    enums: usize,
    records: usize,
    tuple_layouts: usize,
    closure_types: usize,
    closure_layouts: usize,
    /// Read by the handle reachability verdicts only.
    func_types: usize,
    pointer_bits: u32,
    canonical_scalars: bool,
}

impl Tables {
    fn of(module: &Module) -> Self {
        Tables {
            types: module.types.len(),
            structs: module.structs.len(),
            enums: module.enums.len(),
            records: module.records.len(),
            tuple_layouts: module.tuple_layouts.len(),
            closure_types: module.closure_types.len(),
            closure_layouts: module.closure_layouts.len(),
            func_types: module.func_types.len(),
            pointer_bits: module.pointer_bits(),
            canonical_scalars: module.target_has_canonical_scalar_layout(),
        }
    }
}

/// A node the walk guards against re-entry, with the guard's key: the first
/// definition's index for a struct or an enum (the walk resolves an id to its
/// first definition), the `TyId` for a type-table entry, and the descriptor's
/// index for a declared tuple layout (a tuple that resolves names exactly one
/// descriptor), and likewise for a declared closure layout.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Node {
    Struct(usize),
    Enum(usize),
    Entry(usize),
    Tuple(usize),
    Closure(usize),
}

enum Slot {
    /// On the current path (grey): re-entering it is a by-value cycle.
    Open,
    /// Laid out (black).
    Laid(Laid),
    /// An enum laid out (black), with its [`EnumLayoutShape`].
    Enum(Result<(Arc<EnumLayoutShape>, Arc<TyLayoutShape>), Failure>),
}

/// Resolves an id to its FIRST definition's index, scanning the definition
/// list at most once per table and no further than the furthest id asked
/// for, so one query never scans more than the recursion's `find` did.
struct FirstDef<K> {
    scanned: usize,
    first: HashMap<K, usize>,
}

impl<K> Default for FirstDef<K> {
    fn default() -> Self {
        FirstDef {
            scanned: 0,
            first: HashMap::new(),
        }
    }
}

impl<K: Copy + Eq + Hash> FirstDef<K> {
    fn find(&mut self, key: K, len: usize, id_at: impl Fn(usize) -> K) -> Option<usize> {
        if let Some(&index) = self.first.get(&key) {
            return Some(index);
        }
        while self.scanned < len {
            let index = self.scanned;
            self.scanned += 1;
            let id = id_at(index);
            if let Entry::Vacant(slot) = self.first.entry(id) {
                slot.insert(index);
                if id == key {
                    return Some(index);
                }
            }
        }
        None
    }
}

/// [`Module::tuple_layout_descriptor`] for every tuple at once.
///
/// That function scans every row: a row naming a missing type or a non-tuple
/// refuses the scan when reached, and so does a SECOND row declaring the
/// queried tuple. So only the rows before the first refusing row matter; this
/// keeps, per declared tuple among them, its first two rows. The keys are
/// copies of the declared tuple types (O(their size), once), so the index
/// holds no borrow of the module.
struct TupleIndex {
    rows: HashMap<Ty, (usize, Option<usize>)>,
    refusal: Option<Failure>,
    /// Rows read.
    read: usize,
}

impl TupleIndex {
    fn build(module: &Module) -> Self {
        let mut rows: HashMap<Ty, (usize, Option<usize>)> = HashMap::new();
        let mut refusal = None;
        let mut read = 0;
        for (index, desc) in module.tuple_layouts.iter().enumerate() {
            read += 1;
            let Some(declared) = module.types.get(desc.tuple_type.as_usize()) else {
                refusal = Some(Arc::new(LayoutError::MissingType(desc.tuple_type)));
                break;
            };
            if !matches!(declared, Ty::Tuple(_)) {
                refusal = Some(Arc::new(LayoutError::TupleLayoutIncoherent(
                    desc.tuple_type,
                )));
                break;
            }
            match rows.get_mut(declared) {
                Some((_, second)) => {
                    second.get_or_insert(index);
                }
                None => {
                    rows.insert(declared.clone(), (index, None));
                }
            }
        }
        TupleIndex {
            rows,
            refusal,
            read,
        }
    }

    fn lookup(&self, module: &Module, ty: &Ty) -> Result<Option<usize>, Failure> {
        match self.rows.get(ty) {
            // The second row comes before any refusing row (the index holds
            // no row after one).
            Some((_, Some(second))) => Err(Arc::new(LayoutError::TupleLayoutIncoherent(
                module.tuple_layouts[*second].tuple_type,
            ))),
            Some((first, None)) => match &self.refusal {
                Some(refusal) => Err(refusal.clone()),
                None => Ok(Some(*first)),
            },
            None => match &self.refusal {
                Some(refusal) => Err(refusal.clone()),
                None => Ok(None),
            },
        }
    }
}

/// [`Module::closure_layout_descriptor`] for every closure type at once.
///
/// That function scans every row: a row naming a closure type the module does
/// not define refuses the scan when reached, and so does a SECOND row for the
/// queried closure type. So only the rows before the first refusing row
/// matter; this keeps, per closure type among them, its first two rows — the
/// tuple index's rule, keyed by the closure type's id.
struct ClosureIndex {
    rows: HashMap<ClosureTyId, (usize, Option<usize>)>,
    refusal: Option<Failure>,
    /// Rows read.
    read: usize,
}

impl ClosureIndex {
    fn build(module: &Module) -> Self {
        let mut rows: HashMap<ClosureTyId, (usize, Option<usize>)> = HashMap::new();
        let mut refusal = None;
        let mut read = 0;
        for (index, desc) in module.closure_layouts.iter().enumerate() {
            read += 1;
            if module.closure_type(desc.closure).is_none() {
                refusal = Some(Arc::new(LayoutError::ClosureLayoutIncoherent(desc.closure)));
                break;
            }
            match rows.get_mut(&desc.closure) {
                Some((_, second)) => {
                    second.get_or_insert(index);
                }
                None => {
                    rows.insert(desc.closure, (index, None));
                }
            }
        }
        ClosureIndex {
            rows,
            refusal,
            read,
        }
    }

    fn lookup(&self, module: &Module, id: ClosureTyId) -> Result<Option<usize>, Failure> {
        match self.rows.get(&id) {
            // The second row comes before any refusing row (the index holds
            // no row after one).
            Some((_, Some(second))) => Err(Arc::new(LayoutError::ClosureLayoutIncoherent(
                module.closure_layouts[*second].closure,
            ))),
            Some((first, None)) => match &self.refusal {
                Some(refusal) => Err(refusal.clone()),
                None => Ok(Some(*first)),
            },
            None => match &self.refusal {
                Some(refusal) => Err(refusal.clone()),
                None => Ok(None),
            },
        }
    }
}

/// What the walk does next.
enum Step<'q> {
    /// Lay out this type as part of the body of the frame on top.
    Enter(&'q Ty),
    /// Hand this layout to the frame on top, or answer the query with it.
    Give(Arc<TyLayoutShape>),
    /// Answer the query with this failure, closing every open frame. The node
    /// is the re-entered open node when the failure is a re-entry.
    Fail(Failure, Option<Node>),
}

/// A frame of the explicit stack.
enum Frame<'q> {
    /// `<lanes x elem>`, waiting for the element's layout.
    Vector { elem: &'q Ty, lanes: u32 },
    /// `[ty.elem; len]`, waiting for the element entry's layout.
    Array { elem: TyId, len: u64 },
    /// A type-table entry reached by value; its layout is its type's.
    Entry(usize),
    /// A definition laying out its fields.
    Def(Def<'q>),
}

impl Frame<'_> {
    fn node(&self) -> Option<Node> {
        match self {
            Frame::Vector { .. } | Frame::Array { .. } => None,
            Frame::Entry(index) => Some(Node::Entry(*index)),
            Frame::Def(def) => Some(def.node()),
        }
    }
}

/// A definition being laid out field by field.
enum Def<'q> {
    Struct(Box<StructFrame<'q>>),
    Tuple(Box<TupleFrame<'q>>),
    Closure(Box<ClosureFrame<'q>>),
    Enum(Box<EnumFrame<'q>>),
}

/// What a definition does after its checks or after taking a field.
enum Progress<'q> {
    /// Lay out this field next.
    Field(&'q Ty),
    /// Every field is laid out and the definition is: its slot and layout.
    Done(Slot, Arc<TyLayoutShape>),
}

impl<'q> Def<'q> {
    fn node(&self) -> Node {
        match self {
            Def::Struct(frame) => Node::Struct(frame.index),
            Def::Tuple(frame) => Node::Tuple(frame.index),
            Def::Closure(frame) => Node::Closure(frame.index),
            Def::Enum(frame) => Node::Enum(frame.index),
        }
    }

    fn take(&mut self, layout: &TyLayoutShape) -> Result<(), Failure> {
        match self {
            Def::Struct(frame) => frame.take(layout),
            Def::Tuple(frame) => frame.take(layout),
            Def::Closure(frame) => frame.take(layout),
            Def::Enum(frame) => frame.take(layout),
        }
    }

    /// The next field, or the finished definition (an enum's niche rule asks
    /// `inhabit`).
    fn progress(
        &mut self,
        module: &Module,
        inhabit: &mut InhabitMemo,
    ) -> Result<Progress<'q>, Failure> {
        let field = match self {
            Def::Struct(frame) => frame.next_field(),
            Def::Tuple(frame) => frame.next_field(),
            Def::Closure(frame) => frame.next_field(),
            Def::Enum(frame) => frame.next_field()?,
        };
        if let Some(field) = field {
            return Ok(Progress::Field(field));
        }
        Ok(match self {
            Def::Struct(frame) => {
                let layout = Arc::new(frame.finish()?);
                Progress::Done(Slot::Laid(Ok(layout.clone())), layout)
            }
            Def::Tuple(frame) => {
                let layout = Arc::new(frame.finish()?);
                Progress::Done(Slot::Laid(Ok(layout.clone())), layout)
            }
            Def::Closure(frame) => {
                let layout = Arc::new(frame.finish()?);
                Progress::Done(Slot::Laid(Ok(layout.clone())), layout)
            }
            Def::Enum(frame) => {
                let shape = frame.finish(module, inhabit)?;
                let layout = Arc::new(TyLayoutShape {
                    size_bits: shape.size_bits,
                    align_bits: Some(shape.align_bits),
                    kind: TyLayoutKind::Enum {
                        id: shape.id,
                        variants: shape.discriminants.len(),
                    },
                });
                Progress::Done(Slot::Enum(Ok((Arc::new(shape), layout.clone()))), layout)
            }
        })
    }
}

impl Module {
    /// An empty [`LayoutTable`] over this module, for a caller that asks many
    /// layout questions of it: each nominal node is laid out once, by the
    /// first question that reaches it.
    pub fn layout_table(&self) -> LayoutTable<'_> {
        LayoutTable::new(self)
    }
}

impl<'m> LayoutTable<'m> {
    /// An empty table over `module` ([`Module::layout_table`]); nothing is
    /// laid out until a question reaches it.
    pub fn new(module: &'m Module) -> Self {
        LayoutTable {
            module,
            pointer_bits: module.pointer_bits(),
            canonical_scalars: module.target_has_canonical_scalar_layout(),
            memo: Mutex::new(Some(Memo::default())),
        }
    }

    /// A table over `module` that starts from `memo`, the memo of an earlier
    /// table over the same module (see [`LayoutMemo`] for when that is
    /// sound). A memo built over tables of other lengths or another target
    /// layout is dropped and the table starts empty; one built over a
    /// signature table of another length keeps all but its reachability
    /// verdicts.
    pub fn with_memo(module: &'m Module, memo: LayoutMemo) -> Self {
        let table = LayoutTable::new(module);
        let now = Tables::of(module);
        let LayoutMemo { mut memo, tables } = memo;
        let layouts_unchanged = Tables {
            func_types: now.func_types,
            ..tables
        } == now;
        if layouts_unchanged {
            if tables.func_types != now.func_types {
                memo.reach = ReachMemo::default();
            }
            *table.lock() = Some(memo);
        }
        table
    }

    /// This table's memo, without its borrow of the module (see
    /// [`LayoutMemo`]).
    pub fn into_memo(self) -> LayoutMemo {
        let tables = Tables::of(self.module);
        let memo = self
            .memo
            .into_inner()
            // A walk that panicked may have left nodes open: start afresh.
            .unwrap_or(None)
            .unwrap_or_default();
        LayoutMemo { memo, tables }
    }

    /// The memo, locked. A walk that panicked while holding it may have left
    /// nodes open, so a poisoned memo is replaced by an empty one (its
    /// answers are recomputed, never read from a half-closed walk).
    fn lock(&self) -> MutexGuard<'_, Option<Memo>> {
        match self.memo.lock() {
            Ok(memo) => memo,
            Err(poisoned) => {
                let mut memo = poisoned.into_inner();
                *memo = None;
                self.memo.clear_poison();
                memo
            }
        }
    }

    /// Enter the unchanged ordinary memo only for an actual ordinary query.
    /// Observed query methods never call this helper or ordinary query APIs.
    fn query_memo<T>(&self, query: impl FnOnce(&mut Memo) -> T) -> T {
        let mut guard = self.lock();
        query(guard.get_or_insert_with(Memo::default))
    }

    /// The module this table lays out.
    pub fn module(&self) -> &'m Module {
        self.module
    }

    /// The struct definition this table lays out for `id`: the FIRST with
    /// that id (a duplicate id is a validation error; the walk has always
    /// resolved an id to its first definition). O(1) amortized: each table
    /// scans the definition list at most once.
    pub fn struct_def(&self, id: StructId) -> Option<&'m StructDef> {
        let module = self.module;
        self.query_memo(|memo| {
            memo.structs
                .find(id, module.structs.len(), |index| module.structs[index].id)
                .map(|index| &module.structs[index])
        })
    }

    /// [`LayoutTable::struct_def`] for an enum.
    pub fn enum_def(&self, id: EnumId) -> Option<&'m EnumDef> {
        let module = self.module;
        self.query_memo(|memo| {
            memo.enums
                .find(id, module.enums.len(), |index| module.enums[index].id)
                .map(|index| &module.enums[index])
        })
    }

    /// The work done so far (see [`LayoutTableStats`]).
    pub fn stats(&self) -> LayoutTableStats {
        self.lock()
            .as_ref()
            .map_or(LayoutTableStats::EMPTY, Memo::stats)
    }

    /// [`Module::ty_layout_shape`], answered from (and into) this table.
    pub fn ty_layout_shape(&self, ty: &Ty) -> Result<TyLayoutShape, LayoutError> {
        self.ty_layout(ty).map(Arc::unwrap_or_clone)
    }

    /// [`LayoutTable::ty_layout_shape`] without copying the layout out: a
    /// struct's layout carries its field list, which a caller that reads only
    /// the size or alignment need not copy.
    pub fn ty_layout(&self, ty: &Ty) -> Result<Arc<TyLayoutShape>, LayoutError> {
        self.query_memo(|memo| self.lay_out(memo, ty).map_err(|failure| (*failure).clone()))
    }

    /// [`Module::enum_layout_shape`], answered from (and into) this table.
    pub fn enum_layout_shape(&self, id: EnumId) -> Result<EnumLayoutShape, LayoutError> {
        self.enum_layout(id).map(Arc::unwrap_or_clone)
    }

    /// [`LayoutTable::enum_layout_shape`] without copying the layout out.
    pub fn enum_layout(&self, id: EnumId) -> Result<Arc<EnumLayoutShape>, LayoutError> {
        self.query_memo(|memo| {
            let root = Ty::Enum(id);
            self.lay_out(memo, &root)
                .map_err(|failure| (*failure).clone())?;
            let module = self.module;
            let index = memo
                .enums
                .find(id, module.enums.len(), |index| module.enums[index].id);
            match index.and_then(|index| memo.nodes.get(&Node::Enum(index))) {
                Some(Slot::Enum(Ok((shape, _)))) => Ok(shape.clone()),
                Some(Slot::Enum(Err(failure))) => Err((**failure).clone()),
                _ => Err(LayoutError::EnumLayoutUnavailable(id)),
            }
        })
    }

    /// [`Module::struct_field_offset_bits`], answered from (and into) this
    /// table.
    pub fn struct_field_offset_bits(
        &self,
        struct_id: StructId,
        field: u32,
    ) -> Result<u64, LayoutError> {
        let layout = self.ty_layout(&Ty::Struct(struct_id))?;
        let TyLayoutKind::Struct { fields, .. } = &layout.kind else {
            return Err(LayoutError::StructLayoutIncoherent(struct_id));
        };
        fields
            .get(field as usize)
            .and_then(|field| field.offset_bits)
            .ok_or(LayoutError::MissingFieldOffset { struct_id, field })
    }

    /// [`Module::validate_tuple_layouts`], answered from (and into) this
    /// table: every declaration row is checked, each tuple laid out once.
    pub fn validate_tuple_layouts(&self) -> Result<(), LayoutError> {
        let module = self.module;
        for desc in &module.tuple_layouts {
            let ty = module
                .types
                .get(desc.tuple_type.as_usize())
                .ok_or(LayoutError::MissingType(desc.tuple_type))?;
            if !matches!(ty, Ty::Tuple(_)) {
                return Err(LayoutError::TupleLayoutIncoherent(desc.tuple_type));
            }
            self.ty_layout(ty)?;
        }
        Ok(())
    }

    /// [`Module::validate_closure_layouts`], answered from (and into) this
    /// table: every declaration row is checked, each closure laid out once.
    pub fn validate_closure_layouts(&self) -> Result<(), LayoutError> {
        let module = self.module;
        for desc in &module.closure_layouts {
            if module.closure_type(desc.closure).is_none() {
                return Err(LayoutError::ClosureLayoutIncoherent(desc.closure));
            }
            self.ty_layout(&Ty::Closure(desc.closure))?;
        }
        Ok(())
    }

    /// [`Module::ty_is_uninhabited`], answered from (and into) this table's
    /// inhabitedness memo.
    pub fn ty_is_uninhabited(&self, ty: &Ty) -> bool {
        self.query_memo(|memo| memo.inhabit.ty_is_uninhabited(self.module, ty))
    }

    /// [`Module::variant_is_uninhabited`], answered from (and into) this
    /// table's inhabitedness memo.
    pub fn variant_is_uninhabited(&self, variant: &EnumVariant) -> bool {
        self.query_memo(|memo| memo.inhabit.variant_is_uninhabited(self.module, variant))
    }

    /// [`Module::type_reaches_handle`], answered from (and into) this table's
    /// reachability memo: each node is decided once per table, so a pass
    /// asking it of every cast of a module does O(total fields) work.
    pub fn type_reaches_handle(&self, ty: &Ty) -> bool {
        self.query_memo(|memo| memo.reach.reaches(self.module, Reach::Handle, ty))
    }

    /// [`Module::type_holds_closure_by_value`], answered from (and into) this
    /// table's reachability memo.
    pub fn type_holds_closure_by_value(&self, ty: &Ty) -> bool {
        self.query_memo(|memo| memo.reach.reaches(self.module, Reach::ClosureByValue, ty))
    }

    /// Whether this type carries a `Char` by value. Pointer boundaries stop
    /// the walk; missing declarations and by-value cycles fail closed. This
    /// is the same memoized predicate used by the Char-origin subset rule.
    pub fn type_contains_char_by_value(&self, ty: &Ty) -> bool {
        self.query_memo(|memo| memo.reach.reaches(self.module, Reach::CharValue, ty))
    }

    /// Storage-only geometry can never be transported as a typed SSA value.
    /// The graph walk stops at reference/raw-pointer boundaries and reuses this
    /// exact immutable module's reach memo for aggregate/collection definitions.
    pub fn type_contains_storage_by_value(&self, ty: &Ty) -> bool {
        self.query_memo(|memo| memo.reach.reaches(self.module, Reach::StorageValue, ty))
    }

    /// [`Module::type_stores_bool_lane`], answered from (and into) this
    /// table's reachability memo.
    pub fn type_stores_bool_lane(&self, ty: &Ty) -> bool {
        self.query_memo(|memo| memo.reach.reaches(self.module, Reach::BoolLane, ty))
    }

    /// [`Module::niche_unencoded_inhabited_variant`], answered from (and
    /// into) this table's inhabitedness memo.
    pub fn niche_unencoded_inhabited_variant(
        &self,
        def: &EnumDef,
        untagged_variant: u32,
        niche_variants_start: u32,
        niche_variants_end: u32,
    ) -> Option<usize> {
        self.query_memo(|memo| {
            memo.inhabit.niche_unencoded_inhabited_variant(
                self.module,
                def,
                untagged_variant,
                niche_variants_start,
                niche_variants_end,
            )
        })
    }

    /// The walk: lays out `root` and every node it reaches that the table has
    /// not laid out, on an explicit stack.
    fn lay_out<'q>(&'q self, memo: &mut Memo, root: &'q Ty) -> Laid {
        let mut stack: Vec<Frame<'q>> = Vec::new();
        let mut step = Step::Enter(root);
        loop {
            memo.steps += 1;
            step = match step {
                Step::Enter(ty) => self.enter(memo, &mut stack, ty),
                Step::Give(layout) => {
                    if stack.is_empty() {
                        return Ok(layout);
                    }
                    self.resume(memo, &mut stack, layout)
                }
                Step::Fail(failure, reentered) => {
                    self.unwind(memo, &mut stack, &failure, reentered);
                    return Err(failure);
                }
            };
        }
    }

    /// Start laying out `ty`.
    fn enter<'q>(&'q self, memo: &mut Memo, stack: &mut Vec<Frame<'q>>, ty: &'q Ty) -> Step<'q> {
        if let Some(laid) = self.leaf(memo, ty) {
            return give(laid);
        }
        let module = self.module;
        match ty {
            Ty::Vector(elem, lanes) => {
                stack.push(Frame::Vector {
                    elem,
                    lanes: *lanes,
                });
                Step::Enter(elem)
            }
            Ty::Array(elem, len) => {
                // The recursion asked the re-entry guard before the table, but
                // an open entry exists, so asking the table first is the same.
                if module.types.get(elem.as_usize()).is_none() {
                    return fail(LayoutError::MissingType(*elem));
                }
                stack.push(Frame::Array {
                    elem: *elem,
                    len: *len,
                });
                self.open(memo, stack, Node::Entry(elem.as_usize()))
            }
            // REPRESENTATION PRESERVATION: a `Refine(b, p)` lays out exactly as
            // `b` does, so the entry's answer is the refinement's.
            Ty::Refine(base, _) => {
                if module.types.get(base.as_usize()).is_none() {
                    return fail(LayoutError::UnsupportedTyShape(TyShape::Refine));
                }
                self.open(memo, stack, Node::Entry(base.as_usize()))
            }
            Ty::Struct(id) => {
                match memo
                    .structs
                    .find(*id, module.structs.len(), |index| module.structs[index].id)
                {
                    Some(index) => self.open(memo, stack, Node::Struct(index)),
                    None => fail(LayoutError::MissingStruct(*id)),
                }
            }
            // trust-ir's CANONICAL tagged-union layout (see
            // `Module::enum_layout_shape`). Deliberately NOT a claim of rustc
            // layout parity: no niche optimization, no variant reordering.
            Ty::Enum(id) => {
                match memo
                    .enums
                    .find(*id, module.enums.len(), |index| module.enums[index].id)
                {
                    Some(index) => self.open(memo, stack, Node::Enum(index)),
                    None => fail(LayoutError::EnumLayoutUnavailable(*id)),
                }
            }
            Ty::Tuple(elems) => {
                let rows = memo.tuples.get_or_insert_with(|| TupleIndex::build(module));
                match rows.lookup(module, ty) {
                    Err(failure) => Step::Fail(failure, None),
                    Ok(None) if elems.is_empty() => give(Ok(Arc::new(TyLayoutShape {
                        size_bits: 0,
                        align_bits: Some(8),
                        kind: TyLayoutKind::Unit,
                    }))),
                    Ok(None) => fail(LayoutError::UnsupportedTyShape(ty.shape())),
                    Ok(Some(_)) if module.target_info.is_none() => {
                        fail(LayoutError::TupleLayoutTargetMissing)
                    }
                    Ok(Some(index)) => self.open(memo, stack, Node::Tuple(index)),
                }
            }
            // v58: a closure type has a byte image exactly when the producer
            // DECLARED one. Absence is the pre-v58 state and stays
            // `UnsupportedTyShape` — never a guessed declaration-order frame.
            Ty::Closure(id) => {
                let rows = memo
                    .closures
                    .get_or_insert_with(|| ClosureIndex::build(module));
                match rows.lookup(module, *id) {
                    Err(failure) => Step::Fail(failure, None),
                    Ok(None) => fail(LayoutError::UnsupportedTyShape(ty.shape())),
                    Ok(Some(_)) if module.target_info.is_none() => {
                        fail(LayoutError::ClosureLayoutTargetMissing)
                    }
                    Ok(Some(index)) => self.open(memo, stack, Node::Closure(index)),
                }
            }
            // Every other type is a leaf.
            _ => fail(LayoutError::UnsupportedTyShape(ty.shape())),
        }
    }

    /// Enter a nominal node: a re-entry if it is open, its answer if it is
    /// laid out, else its own checks and a frame for its fields.
    fn open<'q>(&'q self, memo: &mut Memo, stack: &mut Vec<Frame<'q>>, node: Node) -> Step<'q> {
        match memo.nodes.get(&node) {
            Some(Slot::Open) => {
                return Step::Fail(Arc::new(self.reentry_error(node)), Some(node));
            }
            Some(Slot::Laid(laid)) => return give(laid.clone()),
            Some(Slot::Enum(laid)) => {
                return give(
                    laid.as_ref()
                        .map(|(_, layout)| layout.clone())
                        .map_err(Arc::clone),
                );
            }
            None => {}
        }
        let module = self.module;
        let def = match node {
            Node::Entry(index) => {
                memo.nodes.insert(node, Slot::Open);
                stack.push(Frame::Entry(index));
                return Step::Enter(&module.types[index]);
            }
            Node::Struct(index) => StructFrame::begin(index, &module.structs[index])
                .map(|frame| Def::Struct(Box::new(frame))),
            Node::Tuple(index) => {
                TupleFrame::begin(module, index).map(|frame| Def::Tuple(Box::new(frame)))
            }
            Node::Closure(index) => {
                ClosureFrame::begin(module, index).map(|frame| Def::Closure(Box::new(frame)))
            }
            Node::Enum(index) => self
                .enum_frame(memo, index)
                .map(|frame| Def::Enum(Box::new(frame))),
        };
        // A failure before the node's first field is its own (its checks, or
        // a variant closing with no field): the same from every path.
        let mut def = match def {
            Ok(def) => def,
            Err(failure) => {
                memo.nodes.insert(node, failed(node, failure.clone()));
                return Step::Fail(failure, None);
            }
        };
        match def.progress(module, &mut memo.inhabit) {
            Err(failure) => {
                memo.nodes.insert(node, failed(node, failure.clone()));
                Step::Fail(failure, None)
            }
            Ok(Progress::Field(field)) => {
                memo.nodes.insert(node, Slot::Open);
                stack.push(Frame::Def(def));
                Step::Enter(field)
            }
            Ok(Progress::Done(slot, layout)) => {
                memo.nodes.insert(node, slot);
                Step::Give(layout)
            }
        }
    }

    /// Hand a field's layout to the frame on top.
    fn resume<'q>(
        &'q self,
        memo: &mut Memo,
        stack: &mut Vec<Frame<'q>>,
        layout: Arc<TyLayoutShape>,
    ) -> Step<'q> {
        let Some(top) = stack.last_mut() else {
            return Step::Give(layout);
        };
        match top {
            Frame::Vector { elem, lanes } => {
                let laid = vector_layout(elem, *lanes, &layout);
                stack.pop();
                give(laid)
            }
            Frame::Array { elem, len } => {
                let laid = array_layout(*elem, *len, &layout);
                stack.pop();
                give(laid)
            }
            Frame::Entry(index) => {
                let node = Node::Entry(*index);
                stack.pop();
                memo.nodes.insert(node, Slot::Laid(Ok(layout.clone())));
                Step::Give(layout)
            }
            Frame::Def(def) => match def
                .take(&layout)
                .and_then(|()| def.progress(self.module, &mut memo.inhabit))
            {
                // The frame stays on the stack, so `unwind` records the failure.
                Err(failure) => Step::Fail(failure, None),
                Ok(Progress::Field(field)) => Step::Enter(field),
                Ok(Progress::Done(slot, layout)) => {
                    let node = def.node();
                    stack.pop();
                    memo.nodes.insert(node, slot);
                    Step::Give(layout)
                }
            },
        }
    }

    /// Close every open frame with `failure` (see the module docs): a node
    /// above the re-entered node `reentered` failed by its own re-entry; the
    /// re-entered node and every node below it, and every node of a path that
    /// failed by anything but a re-entry, failed with `failure`.
    fn unwind(
        &self,
        memo: &mut Memo,
        stack: &mut Vec<Frame<'_>>,
        failure: &Failure,
        mut reentered: Option<Node>,
    ) {
        while let Some(frame) = stack.pop() {
            let Some(node) = frame.node() else {
                continue;
            };
            let closed = match reentered {
                Some(open) if open != node => Arc::new(self.reentry_error(node)),
                Some(_) => {
                    reentered = None;
                    failure.clone()
                }
                None => failure.clone(),
            };
            memo.nodes.insert(node, failed(node, closed));
        }
    }

    /// The error the recursion's guard returned on re-entering `node`.
    fn reentry_error(&self, node: Node) -> LayoutError {
        match node {
            Node::Struct(index) => {
                LayoutError::StructLayoutIncoherent(self.module.structs[index].id)
            }
            Node::Enum(index) => LayoutError::EnumLayoutUnavailable(self.module.enums[index].id),
            Node::Entry(index) => LayoutError::TyLayoutCycle(TyId::new(index as u32)),
            Node::Tuple(index) => {
                LayoutError::TupleLayoutIncoherent(self.module.tuple_layouts[index].tuple_type)
            }
            // A closure that captures a value of its own type (directly, or
            // through an aggregate no pointer breaks) has no finite frame.
            Node::Closure(index) => {
                LayoutError::ClosureLayoutIncoherent(self.module.closure_layouts[index].closure)
            }
        }
    }

    /// The layout of a type that names no other type by value, or `None`.
    fn leaf(&self, memo: &mut Memo, ty: &Ty) -> Option<Laid> {
        if ty_uses_scalar_layout_table(ty) && !self.canonical_scalars {
            let module = self.module;
            let refusal = memo.scalar_refusal.get_or_insert_with(|| {
                Arc::new(LayoutError::TargetScalarLayoutUnavailable {
                    triple: module
                        .target_info
                        .as_ref()
                        .map_or_else(String::new, |target| target.triple.clone()),
                })
            });
            return Some(Err(refusal.clone()));
        }
        leaf_layout(ty, self.pointer_bits).map(|laid| laid.map(Arc::new).map_err(Arc::new))
    }

    /// [`Module::enum_tag_repr_align`] in bits, through the table's leaf.
    fn tag_align_bits(&self, memo: &mut Memo, repr: EnumTagRepr) -> Result<u64, Failure> {
        let ty = repr.ty();
        let layout = match self.leaf(memo, &ty) {
            Some(laid) => laid?,
            None => return Err(Arc::new(LayoutError::UnsupportedTyShape(ty.shape()))),
        };
        let align_bits = layout
            .align_bits
            .filter(|bits| *bits != 0 && bits.is_multiple_of(8))
            .ok_or_else(|| Arc::new(LayoutError::UnsupportedTyShape(ty.shape())))?;
        // A multiple of 8, so this is `enum_tag_repr_align(repr) * 8`.
        Ok(align_bits)
    }

    /// An enum's own checks, before any field is laid out.
    fn enum_frame(&self, memo: &mut Memo, index: usize) -> Result<EnumFrame<'m>, Failure> {
        let def = &self.module.enums[index];
        let unavailable = || Arc::new(LayoutError::EnumLayoutUnavailable(def.id));
        let discriminants = def.effective_discriminants().ok_or_else(unavailable)?;
        let tag = def.canonical_tag_repr().ok_or_else(unavailable)?;
        // WS2.22 (review): a lane's ALIGNMENT is the target's for the lane
        // type — asked of the layout authority, as the reference interpreter
        // asks `byte_align_in` for the same number — never the byte count. The
        // ask is made for exactly the lane that EXISTS, the same `lane_repr`
        // the validator computes: the canonical tag when no descriptor is
        // declared (the canonical layout stores it, and its alignment enters
        // `max(tag alignment, payload alignment)` — a fieldless enum has no
        // field to draw the scalar-table refusal, and its tag is a scalar of
        // exactly the kind the table is about), the placed tag under `Direct`,
        // the niche type under `Niche`, and nothing under `Untagged`, which
        // stores no lane. On a target with no scalar table the ask propagates
        // `TargetScalarLayoutUnavailable`: the layout is unjudgeable, not
        // admissible.
        let lane_align_bits = match def.layout.as_ref().map(|desc| &desc.encoding) {
            None | Some(EnumTagEncoding::Direct { .. }) => Some(self.tag_align_bits(memo, tag)?),
            Some(EnumTagEncoding::Niche { niche_ty, .. }) => {
                Some(self.tag_align_bits(memo, *niche_ty)?)
            }
            Some(EnumTagEncoding::Untagged | EnumTagEncoding::SingleInhabited { .. }) => None,
        };
        Ok(EnumFrame {
            index,
            def,
            discriminants,
            tag,
            tag_size_bits: tag.size_bytes() * 8,
            lane_align_bits,
            variant: 0,
            field: 0,
            offset_bits: 0,
            variant_align_bits: 8,
            field_sizes: Vec::new(),
            field_aligns: Vec::new(),
            payload_size_bits: 0,
            payload_align_bits: 8,
            variant_field_sizes: Vec::with_capacity(def.variants.len()),
            variant_field_aligns: Vec::with_capacity(def.variants.len()),
            never_field: false,
        })
    }
}

fn give<'q>(laid: Laid) -> Step<'q> {
    match laid {
        Ok(layout) => Step::Give(layout),
        Err(failure) => Step::Fail(failure, None),
    }
}

fn fail<'q>(error: LayoutError) -> Step<'q> {
    Step::Fail(Arc::new(error), None)
}

fn failed(node: Node, failure: Failure) -> Slot {
    match node {
        Node::Enum(_) => Slot::Enum(Err(failure)),
        Node::Struct(_) | Node::Entry(_) | Node::Tuple(_) | Node::Closure(_) => {
            Slot::Laid(Err(failure))
        }
    }
}

fn vector_layout(elem: &Ty, lanes: u32, elem_layout: &TyLayoutShape) -> Laid {
    Ok(Arc::new(TyLayoutShape {
        size_bits: elem_layout
            .size_bits
            .checked_mul(u64::from(lanes))
            .ok_or(LayoutError::SizeOverflow)?,
        align_bits: elem_layout.align_bits,
        kind: TyLayoutKind::Vector {
            elem_shape: elem.shape(),
            lanes,
            lane_bits: elem_layout.size_bits,
        },
    }))
}

fn array_layout(elem: TyId, len: u64, elem_layout: &TyLayoutShape) -> Laid {
    Ok(Arc::new(TyLayoutShape {
        size_bits: elem_layout
            .size_bits
            .checked_mul(len)
            .ok_or(LayoutError::SizeOverflow)?,
        align_bits: elem_layout.align_bits,
        kind: TyLayoutKind::Array {
            elem,
            len,
            stride_bits: elem_layout.size_bits,
        },
    }))
}

/// A struct being laid out: its declared layout, checked field by field.
struct StructFrame<'q> {
    index: usize,
    def: &'q StructDef,
    size: u64,
    align: u64,
    clamp: u64,
    ranges: Vec<(u64, u64)>,
    fields: Vec<FieldOffsetShape>,
    transparent_carrier: Option<(u64, u64, u64)>,
    transparent_nontrivial: usize,
}

impl<'q> StructFrame<'q> {
    fn begin(index: usize, def: &'q StructDef) -> Result<Self, Failure> {
        let id = def.id;
        let size = def.size.ok_or(LayoutError::MissingStructSize(id))?;
        let align = def.align.ok_or(LayoutError::MissingStructAlign(id))?;
        if align == 0 || !align.is_power_of_two() || !size.is_multiple_of(align) {
            return Err(Arc::new(LayoutError::StructLayoutIncoherent(id)));
        }
        let clamp = match def.repr {
            StructRepr::Packed(packed) if packed != 0 && packed.is_power_of_two() => {
                u64::from(packed)
            }
            StructRepr::Packed(_) => {
                return Err(Arc::new(LayoutError::StructLayoutIncoherent(id)));
            }
            _ => u64::MAX,
        };
        if align > clamp {
            return Err(Arc::new(LayoutError::StructLayoutIncoherent(id)));
        }
        Ok(StructFrame {
            index,
            def,
            size,
            align,
            clamp,
            ranges: Vec::with_capacity(def.fields.len()),
            fields: Vec::with_capacity(def.fields.len()),
            transparent_carrier: None,
            transparent_nontrivial: 0,
        })
    }

    fn next_field(&self) -> Option<&'q Ty> {
        self.def.fields.get(self.fields.len()).map(|def| &def.ty)
    }

    fn take(&mut self, field_layout: &TyLayoutShape) -> Result<(), Failure> {
        let id = self.def.id;
        let field = self.fields.len();
        let def: &FieldDef = &self.def.fields[field];
        let field_size = field_layout
            .size_bytes()
            .ok_or(LayoutError::StructLayoutIncoherent(id))?;
        let field_align = field_layout
            .align_bits
            .filter(|bits| *bits != 0 && bits.is_multiple_of(8))
            .map(|bits| bits / 8)
            .ok_or(LayoutError::StructLayoutIncoherent(id))?
            .max(1)
            .min(self.clamp);
        let offset = match def.offset {
            Some(offset) => offset,
            None if field_size == 0 => 0,
            None => {
                return Err(Arc::new(LayoutError::MissingFieldOffset {
                    struct_id: id,
                    field: field as u32,
                }));
            }
        };
        if !offset.is_multiple_of(field_align)
            || field_align > self.align
            || offset
                .checked_add(field_size)
                .is_none_or(|end| end > self.size)
        {
            return Err(Arc::new(LayoutError::StructLayoutIncoherent(id)));
        }
        if self.def.repr == StructRepr::Transparent && (field_size != 0 || field_align != 1) {
            self.transparent_nontrivial += 1;
            self.transparent_carrier = Some((field_size, field_align, offset));
        }
        self.ranges.push((offset, field_size));
        self.fields.push(FieldOffsetShape {
            field: field as u32,
            name: def.name.clone(),
            ty_shape: def.ty.shape(),
            // A missing offset is information-free only for a ZST;
            // canonicalize that placement to byte zero for consumers.
            offset_bits: Some(offset.checked_mul(8).ok_or(LayoutError::SizeOverflow)?),
        });
        Ok(())
    }

    fn finish(&mut self) -> Result<TyLayoutShape, Failure> {
        let id = self.def.id;
        if any_byte_ranges_overlap(&self.ranges) {
            return Err(Arc::new(LayoutError::StructLayoutIncoherent(id)));
        }
        if self.def.repr == StructRepr::Transparent {
            // rustc's transparent rule is about 1-ZSTs, not size alone. A
            // zero-sized field with alignment > 1 is the representation-bearing
            // field. The wrapper must match that sole carrier exactly
            // (including offset zero); if every field is a 1-ZST, the wrapper
            // itself is a 1-ZST.
            let (carrier_size, carrier_align, carrier_offset) =
                self.transparent_carrier.unwrap_or((0, 1, 0));
            if self.transparent_nontrivial > 1
                || self.size != carrier_size
                || self.align != carrier_align
                || carrier_offset != 0
            {
                return Err(Arc::new(LayoutError::StructLayoutIncoherent(id)));
            }
        }
        Ok(TyLayoutShape {
            size_bits: self.size.checked_mul(8).ok_or(LayoutError::SizeOverflow)?,
            align_bits: Some(self.align.checked_mul(8).ok_or(LayoutError::SizeOverflow)?),
            kind: TyLayoutKind::Struct {
                id,
                fields: std::mem::take(&mut self.fields),
            },
        })
    }
}

/// A declared tuple layout being checked element by element.
struct TupleFrame<'q> {
    index: usize,
    desc: &'q TupleLayoutDescriptor,
    elems: &'q [Ty],
    ranges: Vec<(u64, u64)>,
    fields: Vec<FieldOffsetShape>,
}

impl<'q> TupleFrame<'q> {
    fn begin(module: &'q Module, index: usize) -> Result<Self, Failure> {
        let desc = &module.tuple_layouts[index];
        let bad = || Arc::new(LayoutError::TupleLayoutIncoherent(desc.tuple_type));
        // The index admitted the row only over a declared tuple, which is the
        // queried tuple (the row matched it by equality).
        let Some(Ty::Tuple(elems)) = module.types.get(desc.tuple_type.as_usize()) else {
            return Err(bad());
        };
        if desc.align == 0
            || !desc.align.is_power_of_two()
            || !desc.size.is_multiple_of(desc.align)
            || desc.field_offsets.len() != elems.len()
        {
            return Err(bad());
        }
        Ok(TupleFrame {
            index,
            desc,
            elems,
            ranges: Vec::with_capacity(elems.len()),
            fields: Vec::with_capacity(elems.len()),
        })
    }

    fn next_field(&self) -> Option<&'q Ty> {
        self.elems.get(self.fields.len())
    }

    fn take(&mut self, layout: &TyLayoutShape) -> Result<(), Failure> {
        let desc = self.desc;
        let bad = || Arc::new(LayoutError::TupleLayoutIncoherent(desc.tuple_type));
        let index = self.fields.len();
        let elem = &self.elems[index];
        let offset = desc.field_offsets[index];
        let size = layout.size_bytes().ok_or_else(bad)?;
        let align = layout
            .align_bits
            .filter(|bits| *bits != 0 && bits.is_multiple_of(8))
            .map(|bits| bits / 8)
            .ok_or_else(bad)?;
        if align > desc.align
            || !offset.is_multiple_of(align)
            || offset.checked_add(size).is_none_or(|end| end > desc.size)
        {
            return Err(bad());
        }
        self.ranges.push((offset, size));
        self.fields.push(FieldOffsetShape {
            field: u32::try_from(index).map_err(|_| bad())?,
            name: index.to_string(),
            ty_shape: elem.shape(),
            offset_bits: Some(offset.checked_mul(8).ok_or(LayoutError::SizeOverflow)?),
        });
        Ok(())
    }

    fn finish(&mut self) -> Result<TyLayoutShape, Failure> {
        let desc = self.desc;
        if any_byte_ranges_overlap(&self.ranges) {
            return Err(Arc::new(LayoutError::TupleLayoutIncoherent(
                desc.tuple_type,
            )));
        }
        Ok(TyLayoutShape {
            size_bits: desc.size.checked_mul(8).ok_or(LayoutError::SizeOverflow)?,
            align_bits: Some(desc.align.checked_mul(8).ok_or(LayoutError::SizeOverflow)?),
            kind: TyLayoutKind::Tuple {
                fields: std::mem::take(&mut self.fields),
            },
        })
    }
}

/// A declared closure layout (wire v58) being checked capture by capture:
/// exactly the declared tuple layout's rules, over the closure type's
/// captures in CAPTURE order (the producer's declared image, which
/// `repr(Rust)` may have reordered physically).
struct ClosureFrame<'q> {
    index: usize,
    desc: &'q ClosureLayoutDescriptor,
    captures: &'q [Ty],
    ranges: Vec<(u64, u64)>,
    fields: Vec<FieldOffsetShape>,
}

impl<'q> ClosureFrame<'q> {
    fn begin(module: &'q Module, index: usize) -> Result<Self, Failure> {
        let desc = &module.closure_layouts[index];
        let bad = || Arc::new(LayoutError::ClosureLayoutIncoherent(desc.closure));
        // The index admitted the row only over a closure type the module
        // defines, which is the queried one (the row matched it by id).
        let captures = module
            .closure_type(desc.closure)
            .ok_or_else(bad)?
            .captures
            .as_slice();
        if desc.align == 0
            || !desc.align.is_power_of_two()
            || !desc.size.is_multiple_of(desc.align)
            || desc.capture_offsets.len() != captures.len()
        {
            return Err(bad());
        }
        Ok(ClosureFrame {
            index,
            desc,
            captures,
            ranges: Vec::with_capacity(captures.len()),
            fields: Vec::with_capacity(captures.len()),
        })
    }

    fn next_field(&self) -> Option<&'q Ty> {
        self.captures.get(self.fields.len())
    }

    fn take(&mut self, layout: &TyLayoutShape) -> Result<(), Failure> {
        let desc = self.desc;
        let bad = || Arc::new(LayoutError::ClosureLayoutIncoherent(desc.closure));
        let index = self.fields.len();
        let capture = &self.captures[index];
        let offset = desc.capture_offsets[index];
        let size = layout.size_bytes().ok_or_else(bad)?;
        let align = layout
            .align_bits
            .filter(|bits| *bits != 0 && bits.is_multiple_of(8))
            .map(|bits| bits / 8)
            .ok_or_else(bad)?;
        if align > desc.align
            || !offset.is_multiple_of(align)
            || offset.checked_add(size).is_none_or(|end| end > desc.size)
        {
            return Err(bad());
        }
        self.ranges.push((offset, size));
        self.fields.push(FieldOffsetShape {
            field: u32::try_from(index).map_err(|_| bad())?,
            name: index.to_string(),
            ty_shape: capture.shape(),
            offset_bits: Some(offset.checked_mul(8).ok_or(LayoutError::SizeOverflow)?),
        });
        Ok(())
    }

    fn finish(&mut self) -> Result<TyLayoutShape, Failure> {
        let desc = self.desc;
        if any_byte_ranges_overlap(&self.ranges) {
            return Err(Arc::new(LayoutError::ClosureLayoutIncoherent(desc.closure)));
        }
        Ok(TyLayoutShape {
            size_bits: desc.size.checked_mul(8).ok_or(LayoutError::SizeOverflow)?,
            align_bits: Some(desc.align.checked_mul(8).ok_or(LayoutError::SizeOverflow)?),
            kind: TyLayoutKind::Closure {
                id: desc.closure,
                captures: std::mem::take(&mut self.fields),
            },
        })
    }
}

/// An enum being laid out: each variant's payload C-style, then the canonical
/// image or the declared descriptor's checks.
struct EnumFrame<'q> {
    index: usize,
    def: &'q EnumDef,
    discriminants: Vec<i128>,
    tag: EnumTagRepr,
    tag_size_bits: u64,
    lane_align_bits: Option<u64>,
    /// The variant and field the walk is at.
    variant: usize,
    field: usize,
    /// The open variant's running offset and alignment.
    offset_bits: u64,
    variant_align_bits: u64,
    field_sizes: Vec<u64>,
    field_aligns: Vec<u64>,
    /// The payload region: the max variant size and alignment (min 1 byte).
    payload_size_bits: u64,
    payload_align_bits: u64,
    variant_field_sizes: Vec<Vec<u64>>,
    variant_field_aligns: Vec<Vec<u64>>,
    never_field: bool,
}

impl<'q> EnumFrame<'q> {
    /// The next field to lay out, closing every variant whose fields are all
    /// laid out on the way.
    fn next_field(&mut self) -> Result<Option<&'q Ty>, Failure> {
        let def = self.def;
        while let Some(variant) = def.variants.get(self.variant) {
            let inactive = matches!(&def.layout, Some(layout) if matches!(layout.encoding,
                EnumTagEncoding::SingleInhabited { variant } if usize::try_from(variant).ok() != Some(self.variant)));
            if !inactive && let Some(field) = variant.fields.get(self.field) {
                return Ok(Some(field));
            }
            let variant_size_bits = align_up_bits(self.offset_bits, self.variant_align_bits)?;
            self.payload_size_bits = self.payload_size_bits.max(variant_size_bits);
            self.payload_align_bits = self.payload_align_bits.max(self.variant_align_bits);
            self.variant_field_sizes
                .push(std::mem::take(&mut self.field_sizes));
            self.variant_field_aligns
                .push(std::mem::take(&mut self.field_aligns));
            self.offset_bits = 0;
            self.variant_align_bits = 8;
            self.variant += 1;
            self.field = 0;
        }
        Ok(None)
    }

    fn take(&mut self, field_layout: &TyLayoutShape) -> Result<(), Failure> {
        let id = self.def.id;
        let field_ty = &self.def.variants[self.variant].fields[self.field];
        let field_size = field_layout
            .size_bytes()
            .ok_or(LayoutError::EnumLayoutUnavailable(id))?;
        // WS3.14: a `!` payload field (rustc's `B(!)`) occupies no bytes and —
        // as in rustc, where `!` is size 0 / align 1 — constrains no offset.
        // `Ty::Never` has no alignment of its own, so it is admitted here ONLY
        // under a producer descriptor (checked in `finish`); the canonical
        // layout keeps refusing an enum that spells one.
        let field_align_bits = if matches!(field_ty, Ty::Never) {
            self.never_field = true;
            8
        } else {
            field_layout
                .align_bits
                .ok_or(LayoutError::EnumLayoutUnavailable(id))?
                .max(8)
        };
        self.offset_bits = align_up_bits(self.offset_bits, field_align_bits)?;
        self.offset_bits = self
            .offset_bits
            .checked_add(field_layout.size_bits)
            .ok_or(LayoutError::SizeOverflow)?;
        self.variant_align_bits = self.variant_align_bits.max(field_align_bits);
        self.field_sizes.push(field_size);
        self.field_aligns.push(field_align_bits / 8);
        self.field += 1;
        Ok(())
    }

    fn finish(
        &mut self,
        module: &Module,
        inhabit: &mut InhabitMemo,
    ) -> Result<EnumLayoutShape, Failure> {
        let ed = self.def;
        let id = ed.id;
        let unavailable = || Arc::new(LayoutError::EnumLayoutUnavailable(id));
        if self.never_field && ed.layout.is_none() {
            return Err(unavailable());
        }
        let tag_size_bits = self.tag_size_bits;
        let payload_offset_bits = align_up_bits(tag_size_bits, self.payload_align_bits)?;
        let variant_field_sizes = &self.variant_field_sizes;
        let variant_field_aligns = &self.variant_field_aligns;
        // The canonical image — tag lane at 0, payload after it, alignment the
        // max of the two — is formed only when no descriptor replaces it: a
        // declared descriptor's size and align are normative, and under
        // `Niche` / `Untagged` there is no canonical tag lane whose alignment
        // could have been asked for.
        let (size_bits, align_bits) = if let Some(desc) = &ed.layout {
            if desc.align == 0
                || !desc.align.is_power_of_two()
                || !desc.size.is_multiple_of(desc.align)
                || desc.variant_field_offsets.len() != ed.variants.len()
            {
                return Err(unavailable());
            }
            for ((offsets, sizes), aligns) in desc
                .variant_field_offsets
                .iter()
                .zip(variant_field_sizes)
                .zip(variant_field_aligns)
            {
                if offsets.len() != sizes.len() || offsets.len() != aligns.len() {
                    return Err(unavailable());
                }
                for ((offset, field_size), field_align) in offsets.iter().zip(sizes).zip(aligns) {
                    if !offset.is_multiple_of(*field_align)
                        || *field_align > desc.align
                        || offset
                            .checked_add(*field_size)
                            .is_none_or(|end| end > desc.size)
                    {
                        return Err(unavailable());
                    }
                }
                let ranges: Vec<(u64, u64)> =
                    offsets.iter().copied().zip(sizes.iter().copied()).collect();
                if any_byte_ranges_overlap(&ranges) {
                    return Err(unavailable());
                }
            }
            match &desc.encoding {
                // v37: no tag lane exists, so every tag-PLACEMENT check is
                // vacuous — there is no offset to align, nothing to fit inside
                // `desc.size`, and nothing that could overlap a payload field.
                // The per-field bound above still ran and is what makes this
                // encoding safe: the fields must lie inside the declared size
                // exactly as for the tagged encodings.
                //
                // The one check with content is that a variant is RECOVERABLE
                // without reading anything, which holds exactly when there is
                // one. This mirrors the interpreter and the validator: all
                // three must agree, or a shape query would report a size for an
                // enum the interpreter refuses to load.
                EnumTagEncoding::Untagged => {
                    if ed.variants.len() != 1 {
                        return Err(unavailable());
                    }
                }
                EnumTagEncoding::SingleInhabited { variant } => {
                    let active = usize::try_from(*variant).map_err(|_| unavailable())?;
                    let selected = ed.variants.get(active).ok_or_else(unavailable)?;
                    if inhabit.variant_is_uninhabited(module, selected)
                        || ed.variants.iter().enumerate().any(|(index, item)| {
                            index != active && !inhabit.variant_is_uninhabited(module, item)
                        })
                    {
                        return Err(unavailable());
                    }
                }
                EnumTagEncoding::Direct { tag_offset } => {
                    let tag_size = tag_size_bits / 8;
                    // WS2.22: the tag's PLACEMENT is judged against the
                    // target's alignment for the tag type (asked of the layout
                    // authority before any field, never reused from the byte
                    // count). On a target with no scalar table that ask
                    // already propagated `TargetScalarLayoutUnavailable` — the
                    // descriptor is unjudgeable, not admissible.
                    let tag_align = self.lane_align_bits.ok_or_else(unavailable)? / 8;
                    if tag_align > desc.align
                        || !tag_offset.is_multiple_of(tag_align)
                        || tag_offset
                            .checked_add(tag_size)
                            .is_none_or(|end| end > desc.size)
                    {
                        return Err(unavailable());
                    }
                    for (offsets, sizes) in
                        desc.variant_field_offsets.iter().zip(variant_field_sizes)
                    {
                        if offsets.iter().zip(sizes).any(|(offset, field_size)| {
                            byte_ranges_overlap(*tag_offset, tag_size, *offset, *field_size)
                        }) {
                            return Err(unavailable());
                        }
                    }
                }
                EnumTagEncoding::Niche {
                    untagged_variant,
                    niche_variants_start,
                    niche_variants_end,
                    niche_start,
                    niche_offset,
                    niche_ty,
                } => {
                    let variant_count =
                        u32::try_from(ed.variants.len()).map_err(|_| unavailable())?;
                    let niche_size = niche_ty.size_bytes();
                    // WS2.22: as for the direct tag, the niche lane's alignment
                    // is the target's for the lane type (asked before any
                    // field).
                    let niche_align = self.lane_align_bits.ok_or_else(unavailable)? / 8;
                    let niche_bits = u32::try_from(niche_size * 8).map_err(|_| unavailable())?;
                    let niche_mask = match niche_bits {
                        0 => return Err(unavailable()),
                        128 => u128::MAX,
                        bits if bits < 128 => (1u128 << bits) - 1,
                        _ => return Err(unavailable()),
                    };
                    let niche_span = niche_variants_end
                        .checked_sub(*niche_variants_start)
                        .map(u128::from)
                        .ok_or_else(unavailable)?;
                    // WS3.14: every INHABITED variant is the untagged one or
                    // lies in the niche interval; an uninhabited variant
                    // (rustc's `B(!)`) needs no encoding and may lie in either
                    // place or in neither. The same rule, through the same
                    // memo rule, as the validator and the interpreter.
                    if *untagged_variant >= variant_count
                        || *niche_variants_end >= variant_count
                        || inhabit
                            .niche_unencoded_inhabited_variant(
                                module,
                                ed,
                                *untagged_variant,
                                *niche_variants_start,
                                *niche_variants_end,
                            )
                            .is_some()
                        || niche_span > niche_mask
                        || *niche_start > niche_mask
                        || niche_align > desc.align
                        || !niche_offset.is_multiple_of(niche_align)
                        || niche_offset
                            .checked_add(niche_size)
                            .is_none_or(|end| end > desc.size)
                    {
                        return Err(unavailable());
                    }
                    let untagged = *untagged_variant as usize;
                    let lane_end = niche_offset
                        .checked_add(niche_size)
                        .ok_or_else(unavailable)?;
                    let lane_is_covered = desc.variant_field_offsets[untagged]
                        .iter()
                        .zip(&variant_field_sizes[untagged])
                        .any(|(field_offset, field_size)| {
                            *field_size > 0
                                && *field_offset <= *niche_offset
                                && field_offset
                                    .checked_add(*field_size)
                                    .is_some_and(|field_end| field_end >= lane_end)
                        });
                    if !lane_is_covered {
                        return Err(unavailable());
                    }
                    for variant in *niche_variants_start..=*niche_variants_end {
                        if variant == *untagged_variant {
                            continue;
                        }
                        let variant = variant as usize;
                        if desc.variant_field_offsets[variant]
                            .iter()
                            .zip(&variant_field_sizes[variant])
                            .any(|(field_offset, field_size)| {
                                byte_ranges_overlap(
                                    *niche_offset,
                                    niche_size,
                                    *field_offset,
                                    *field_size,
                                )
                            })
                        {
                            return Err(unavailable());
                        }
                    }
                }
            }
            (
                desc.size.checked_mul(8).ok_or(LayoutError::SizeOverflow)?,
                desc.align.checked_mul(8).ok_or(LayoutError::SizeOverflow)?,
            )
        } else {
            // WS2.22 (review): the canonical alignment is
            // `max(tag alignment, payload alignment)` — the tag's the target's,
            // asked before any field — as the reference interpreter forms it,
            // never `max(tag SIZE, payload alignment)`.
            let tag_align_bits = self.lane_align_bits.ok_or_else(unavailable)?;
            let align_bits = tag_align_bits.max(self.payload_align_bits);
            let size_bits = align_up_bits(
                payload_offset_bits
                    .checked_add(self.payload_size_bits)
                    .ok_or(LayoutError::SizeOverflow)?,
                align_bits,
            )?;
            (size_bits, align_bits)
        };
        Ok(EnumLayoutShape {
            id,
            tag: self.tag,
            tag_size_bits,
            payload_offset_bits,
            payload_size_bits: self.payload_size_bits,
            size_bits,
            align_bits,
            discriminants: std::mem::take(&mut self.discriminants),
            descriptor: ed.layout.clone(),
        })
    }
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! By-value and nominal reachability, decided once per nominal node.
//!
//! The layout-sensitive cast rule
//! ([`crate::LayoutTable::layout_sensitive_cast_evidence`]) refuses a cast one
//! of whose sides, FOLLOWING named table references,
//!
//! * reaches a v43 opaque runtime handle ([`Module::type_reaches_handle`]),
//! * holds a closure by value ([`Module::type_holds_closure_by_value`]), or
//! * stores a bool lane by value ([`Module::type_stores_bool_lane`]).
//!
//! Each of the three used to be a fresh walk per question that scanned the
//! whole struct, enum or record list at every nominal node it entered, and
//! the by-value two recursed on the native stack behind a `Vec` guard. So
//! one question about a 16 000-deep struct chain took 190 ms (quadratic), a
//! validator pass judging one cast per level of a 4000-deep chain took 77 s on
//! one shared [`crate::LayoutTable`] (whose layouts were memoized but whose
//! cast predicates were not), and a 100 000-deep chain overflowed an 8 MiB
//! stack while the table laid it out on the heap.
//!
//! # Reachability
//!
//! Each predicate asks whether a SEED occurrence is reachable from the type,
//! over a graph whose vertices are the module's nominal nodes (a type-table
//! entry, a struct, enum or record id, a signature, a closure type):
//!
//! | predicate        | seed         | inline children it follows    | a node's members |
//! |------------------|--------------|-------------------------------|------------------|
//! | closure by value | `Closure`    | tuple elements, vector and tensor element | `Array` / `Refine` entry; every struct, enum and record definition of the id |
//! | bool lane        | `Bool`       | tuple elements, vector and tensor element | `Array` / `Refine` entry; every struct and enum definition of the id (not records) |
//! | handle           | `Handle`     | every inline child ([`Ty::visit_types`]) | every table reference ([`table_referent`]): an entry, a signature's parameters and returns, every struct, enum and record definition, a closure's captures and its signature |
//!
//! A missing entry, id or signature has no members. The walks these replace
//! answered exactly this: each marked a node before expanding it and answered
//! "no" on meeting a marked node again, and a marked node is either fully
//! expanded already (having found no seed, or the walk would have stopped)
//! or open on the current path (its remaining members are expanded by the
//! frame that opened it). So the walk said "yes" exactly when some seed was
//! reachable, whatever the order — unlike the inhabitedness walk
//! ([`crate::inhabit`]), whose rules mix "every" with "some", these are pure
//! disjunctions, whose least solution IS reachability and is reached by any
//! complete walk.
//!
//! A node's verdict therefore depends on the node alone, so [`ReachMemo`]
//! keeps it: a query scans the type inline, collects the nodes it reaches
//! that no earlier query decided (an explicit stack, no recursion), records
//! each member edge backwards, and propagates "yes" from the nodes that hold
//! a seed (or name a node decided "yes") back along those edges; every node
//! the propagation does not reach is "no". That is linear in the members
//! written, each node is expanded at most once per memo and predicate, and the
//! all-definitions index ([`DefIndex`]) is built once per kind on first use.
//! A [`crate::LayoutTable`] keeps one memo for its lifetime, so a pass that
//! judges every cast of a module through one table does O(total fields) work
//! for the three predicates together; a one-shot `Module` call costs O(its
//! reach) plus one pass over each definition table it meets (comparisons
//! only, when the table's ids are their positions; a hash index otherwise).
//!
//! # A `Char` carried by value (subset condition 6)
//!
//! The lowering-target subset refuses a `Load` / `AtomicLoad` / `LoadSlot` at
//! a type that carries a `Char` BY VALUE ([`crate::ConformanceSubset`]'s
//! condition 6: a load does not re-establish the Unicode-scalar invariant).
//! That is a fourth predicate here, [`Reach::CharValue`], with its own rules:
//!
//! | seed | inline children it follows | a node's members |
//! |------|----------------------------|------------------|
//! | `Char`; a MISSING entry, id or closure type; a node on a by-value CYCLE | tuple elements, vector element, tensor element | `Array` / `Sequence` / `Set` / `Refine` entry; the ONE struct, enum or record definition [`Module::struct_def`] (and its twins) resolves an id to; a closure type's captures |
//!
//! A dangling reference is a seed so that a malformed module fails closed,
//! and so is a node on a by-value cycle: it is an infinitely large type
//! (`validate_module` refuses it on its own), and the walk this replaces
//! failed closed on it. That walk was a native recursion with a 24-level
//! depth budget that answered "carries a `Char`" when the budget ran out, so
//! it also refused every char-free type 24 levels deep, and walked a shared
//! sub-type once per path (2^d paths through `P{k+1} = {Pk, Pk}`). What it
//! answered as its budget grows is exactly this predicate: a `Char`, a
//! dangling reference or a cycle reachable. A solve finds the cycles among
//! the nodes it collected (Tarjan's strongly connected components, on an
//! explicit stack, over the member edges it wrote: a node on a cycle with a
//! node decided earlier would have been decided with it) and marks them as
//! seeds before it propagates, so the predicate keeps the memo's linear
//! cost.

use std::collections::HashMap;

use crate::Module;
use crate::inhabit::{AllDefs, END};
use crate::ty::{ClosureTy, EnumDef, FuncTy, RecordDef, StructDef, Ty};
use crate::type_reachability::{TableReferent, table_referent};
use crate::value::{EnumId, RecordId, StructId};

/// The exact immutable definition slices consumed by the existing graph.
pub(crate) trait DefinitionSource {
    fn types(&self) -> &[Ty];
    fn structs(&self) -> &[StructDef];
    fn enums(&self) -> &[EnumDef];
    fn records(&self) -> &[RecordDef];
    fn closure_types(&self) -> &[ClosureTy];
    fn func_types(&self) -> &[FuncTy];
}
impl DefinitionSource for Module {
    fn types(&self) -> &[Ty] {
        &self.types
    }
    fn structs(&self) -> &[StructDef] {
        &self.structs
    }
    fn enums(&self) -> &[EnumDef] {
        &self.enums
    }
    fn records(&self) -> &[RecordDef] {
        &self.records
    }
    fn closure_types(&self) -> &[ClosureTy] {
        &self.closure_types
    }
    fn func_types(&self) -> &[FuncTy] {
        &self.func_types
    }
}

struct ByValueDefinitions<'a> {
    types: &'a [Ty],
    structs: &'a [StructDef],
    enums: &'a [EnumDef],
    records: &'a [RecordDef],
    closure_types: &'a [ClosureTy],
}
impl DefinitionSource for ByValueDefinitions<'_> {
    fn types(&self) -> &[Ty] {
        self.types
    }
    fn structs(&self) -> &[StructDef] {
        self.structs
    }
    fn enums(&self) -> &[EnumDef] {
        self.enums
    }
    fn records(&self) -> &[RecordDef] {
        self.records
    }
    fn closure_types(&self) -> &[ClosureTy] {
        self.closure_types
    }
    // This private view is queried ONLY with StorageClosed. Code pointers
    // stop that predicate; a signature is never a by-value child.
    fn func_types(&self) -> &[FuncTy] {
        &[]
    }
}

/// A conservative storage-free query over one immutable set of borrowed tables.
///
/// Uses the existing by-value reachability graph and definition index, without
/// cloning a module. Unlike a predicate over an already validated module, this
/// raw-table boundary also refuses dangling references, by-value cycles and
/// duplicate nominal definitions. Every declared variant is inspected,
/// including an inactive structurally uninhabited variant. Pointers, references
/// and code signatures stop the walk; closure captures remain by-value children.
/// A true answer grants no initialization, layout, ABI, source or proof license.
/// The private memo cannot be exported or reused with different table slices.
pub struct ByValueStorageQuery<'a> {
    definitions: ByValueDefinitions<'a>,
    memo: ReachMemo,
}
impl<'a> ByValueStorageQuery<'a> {
    /// Bind the exact by-value definition slices. Code signatures are not
    /// inputs: a function pointer is an address boundary, not its arguments.
    pub fn new(
        types: &'a [Ty],
        structs: &'a [StructDef],
        records: &'a [RecordDef],
        enums: &'a [EnumDef],
        closure_types: &'a [ClosureTy],
    ) -> Self {
        Self {
            definitions: ByValueDefinitions {
                types,
                structs,
                enums,
                records,
                closure_types,
            },
            memo: ReachMemo::default(),
        }
    }
    /// Borrow a module's definition slices without cloning or validating it.
    pub fn for_module(module: &'a Module) -> Self {
        Self::new(
            &module.types,
            &module.structs,
            &module.records,
            &module.enums,
            &module.closure_types,
        )
    }
    /// True only after a complete, unambiguous, acyclic by-value graph has
    /// established the absence of Storage. False also covers invalid schemas.
    pub fn is_storage_free(&mut self, ty: &Ty) -> bool {
        !self
            .memo
            .reaches(&self.definitions, Reach::StorageClosed, ty)
    }
}

/// Every definition of each struct, enum and record id, in table order; each
/// kind is indexed on first use (O(that table) once), so a walk that follows
/// every definition of an id costs O(its definitions), not a scan of the
/// table per id.
#[derive(Default)]
pub(crate) struct DefIndex {
    structs: Option<AllDefs>,
    enums: Option<AllDefs>,
    records: Option<AllDefs>,
    /// Definition rows indexed (each at most once).
    pub(crate) rows_indexed: usize,
}

impl DefIndex {
    /// Call `each` on every struct definition with `id`, in table order;
    /// `false` when there is none.
    pub(crate) fn each_struct<'m>(
        &mut self,
        module: &'m impl DefinitionSource,
        id: StructId,
        mut each: impl FnMut(&'m StructDef),
    ) -> bool {
        let rows = &mut self.rows_indexed;
        let defs = self.structs.get_or_insert_with(|| {
            *rows += module.structs().len();
            AllDefs::build(module.structs().len(), |at| module.structs()[at].id.index())
        });
        let mut at = defs.first(id.index());
        let found = at != END;
        while at != END {
            each(&module.structs()[at]);
            at = defs.next(at);
        }
        found
    }

    /// [`DefIndex::each_struct`] for an enum.
    pub(crate) fn each_enum<'m>(
        &mut self,
        module: &'m impl DefinitionSource,
        id: EnumId,
        mut each: impl FnMut(&'m EnumDef),
    ) -> bool {
        let rows = &mut self.rows_indexed;
        let defs = self.enums.get_or_insert_with(|| {
            *rows += module.enums().len();
            AllDefs::build(module.enums().len(), |at| module.enums()[at].id.index())
        });
        let mut at = defs.first(id.index());
        let found = at != END;
        while at != END {
            each(&module.enums()[at]);
            at = defs.next(at);
        }
        found
    }

    /// [`DefIndex::each_struct`] for a record.
    pub(crate) fn each_record<'m>(
        &mut self,
        module: &'m impl DefinitionSource,
        id: RecordId,
        mut each: impl FnMut(&'m RecordDef),
    ) -> bool {
        let rows = &mut self.rows_indexed;
        let defs = self.records.get_or_insert_with(|| {
            *rows += module.records().len();
            AllDefs::build(module.records().len(), |at| module.records()[at].id.index())
        });
        let mut at = defs.first(id.index());
        let found = at != END;
        while at != END {
            each(&module.records()[at]);
            at = defs.next(at);
        }
        found
    }

    /// The struct definition [`Module::struct_def`] resolves `id` to (the
    /// row at the id's position if it has that id, else the first with it),
    /// from the index rather than a scan.
    pub(crate) fn struct_def<'m>(
        &mut self,
        module: &'m impl DefinitionSource,
        id: StructId,
    ) -> Option<&'m StructDef> {
        if let Some(def) = module
            .structs()
            .get(id.as_usize())
            .filter(|def| def.id == id)
        {
            return Some(def);
        }
        let mut first = None;
        self.each_struct(module, id, |def| {
            first.get_or_insert(def);
        });
        first
    }

    /// [`DefIndex::struct_def`] for [`Module::enum_def`].
    pub(crate) fn enum_def<'m>(
        &mut self,
        module: &'m impl DefinitionSource,
        id: EnumId,
    ) -> Option<&'m EnumDef> {
        if let Some(def) = module.enums().get(id.as_usize()).filter(|def| def.id == id) {
            return Some(def);
        }
        let mut first = None;
        self.each_enum(module, id, |def| {
            first.get_or_insert(def);
        });
        first
    }

    /// [`DefIndex::struct_def`] for [`Module::record_def`].
    pub(crate) fn record_def<'m>(
        &mut self,
        module: &'m impl DefinitionSource,
        id: RecordId,
    ) -> Option<&'m RecordDef> {
        if let Some(def) = module
            .records()
            .get(id.as_usize())
            .filter(|def| def.id == id)
        {
            return Some(def);
        }
        let mut first = None;
        self.each_record(module, id, |def| {
            first.get_or_insert(def);
        });
        first
    }
}

/// Which reachability question (see the module docs).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Reach {
    /// [`Module::type_holds_closure_by_value`].
    ClosureByValue = 0,
    /// [`Module::type_stores_bool_lane`].
    BoolLane = 1,
    /// [`Module::type_reaches_handle`].
    Handle = 2,
    /// Subset condition 6: a `Char` carried by value, a dangling reference
    /// or a by-value cycle (see the module docs).
    CharValue = 3,
    /// Storage-only declarations carried by value, stopping at pointer boundaries.
    StorageValue = 4,
    /// Raw-table storage query: invalid/incomplete by-value graphs also block.
    StorageClosed = 5,
}

const PREDICATES: usize = 6;

/// The reachability verdicts decided so far over one module, per predicate.
///
/// The memo holds no borrow of the module; every query passes it, and a memo
/// must only ever be asked about the module (unchanged) it was first asked
/// about.
#[derive(Default)]
pub(crate) struct ReachMemo {
    /// The all-definitions index; its `rows_indexed` counts the rows it has
    /// read (each at most once per memo).
    pub(crate) defs: DefIndex,
    /// Indexed by [`Reach`].
    decided: [HashMap<TableReferent, bool>; PREDICATES],
    /// Inline types scanned, nodes expanded, member edges written and
    /// propagations made: O(the members of the decided nodes) over the
    /// memo's lifetime.
    pub(crate) steps: u64,
}

impl core::fmt::Debug for ReachMemo {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("ReachMemo")
            .field("decided", &self.decided())
            .field("rows_indexed", &self.defs.rows_indexed)
            .field("steps", &self.steps)
            .finish()
    }
}

/// Reverse member edges as intrusive lists in one vector.
const NO_EDGE: usize = usize::MAX;

/// The state of one solve: the nodes a query reached that were not decided.
#[derive(Default)]
struct Solve {
    local: HashMap<TableReferent, usize>,
    nodes: Vec<TableReferent>,
    /// Per node: does it reach a seed (so far)?
    verdict: Vec<bool>,
    /// Per node: its first reverse edge (an edge to a node that has it as a
    /// member).
    head: Vec<usize>,
    /// Per edge: the node that has the edge's node as a member, and the next
    /// edge of the same member.
    edges: Vec<(usize, usize)>,
    /// Nodes whose members are not read yet.
    unexpanded: Vec<usize>,
    /// Nodes found to reach a seed whose dependents are not told yet.
    reached: Vec<usize>,
    /// Per node: does it have itself as a member?
    self_member: Vec<bool>,
}

impl Solve {
    fn intern(&mut self, node: TableReferent) -> usize {
        *self.local.entry(node).or_insert_with(|| {
            let index = self.nodes.len();
            self.nodes.push(node);
            self.verdict.push(false);
            self.head.push(NO_EDGE);
            self.self_member.push(false);
            self.unexpanded.push(index);
            index
        })
    }

    /// `dependent` has `member` as a member.
    fn edge(&mut self, member: usize, dependent: usize) {
        self.edges.push((dependent, self.head[member]));
        self.head[member] = self.edges.len() - 1;
        self.self_member[member] |= member == dependent;
    }

    /// Mark every node on a cycle of the member edges written: the members
    /// of each strongly connected component with two nodes or more, or with
    /// one that is its own member. Tarjan's algorithm on an explicit stack,
    /// over the reverse edges (a graph and its reverse have the same
    /// components); each node and edge is visited once.
    fn mark_cycles(&mut self, steps: &mut u64) {
        const UNVISITED: usize = usize::MAX;
        let count = self.nodes.len();
        let mut order = vec![UNVISITED; count];
        let mut low = vec![0usize; count];
        let mut on_stack = vec![false; count];
        let mut stack: Vec<usize> = Vec::new();
        // (node, its next edge to visit)
        let mut frames: Vec<(usize, usize)> = Vec::new();
        let mut next_order = 0usize;
        let mut component: Vec<usize> = Vec::new();
        for root in 0..count {
            if order[root] != UNVISITED {
                continue;
            }
            order[root] = next_order;
            low[root] = next_order;
            next_order += 1;
            stack.push(root);
            on_stack[root] = true;
            frames.push((root, self.head[root]));
            while let Some(frame) = frames.last_mut() {
                *steps += 1;
                let node = frame.0;
                if frame.1 != NO_EDGE {
                    let (next, rest) = self.edges[frame.1];
                    frame.1 = rest;
                    if order[next] == UNVISITED {
                        order[next] = next_order;
                        low[next] = next_order;
                        next_order += 1;
                        stack.push(next);
                        on_stack[next] = true;
                        frames.push((next, self.head[next]));
                    } else if on_stack[next] {
                        low[node] = low[node].min(order[next]);
                    }
                    continue;
                }
                frames.pop();
                if let Some(parent) = frames.last() {
                    low[parent.0] = low[parent.0].min(low[node]);
                }
                if low[node] != order[node] {
                    continue;
                }
                component.clear();
                while let Some(member) = stack.pop() {
                    on_stack[member] = false;
                    component.push(member);
                    if member == node {
                        break;
                    }
                }
                if component.len() > 1 || self.self_member[node] {
                    for &member in &component {
                        self.mark(member);
                    }
                }
            }
        }
    }

    fn mark(&mut self, index: usize) {
        if !self.verdict[index] {
            self.verdict[index] = true;
            self.reached.push(index);
        }
    }
}

impl ReachMemo {
    /// Number of verdicts decided, over all predicates.
    pub(crate) fn decided(&self) -> usize {
        self.decided.iter().map(HashMap::len).sum()
    }

    /// Does `ty` reach a seed of `reach` (see the module docs)?
    pub(crate) fn reaches(
        &mut self,
        module: &impl DefinitionSource,
        reach: Reach,
        ty: &Ty,
    ) -> bool {
        let mut roots = Vec::new();
        if scan(reach, ty, &mut roots, &mut self.steps) {
            return true;
        }
        let decided = &self.decided[reach as usize];
        let mut undecided = Vec::new();
        for root in roots {
            match decided.get(&root) {
                Some(true) => return true,
                Some(false) => {}
                None => undecided.push(root),
            }
        }
        if undecided.is_empty() {
            return false;
        }
        self.solve(module, reach, &undecided);
        let decided = &self.decided[reach as usize];
        undecided.iter().any(|root| decided[root])
    }

    /// Decide every node `roots` reach that is not decided: read their
    /// members once, then propagate "reaches a seed" back along the member
    /// edges (see the module docs).
    fn solve(&mut self, module: &impl DefinitionSource, reach: Reach, roots: &[TableReferent]) {
        let mut solve = Solve::default();
        for &root in roots {
            solve.intern(root);
        }
        let mut members: Vec<TableReferent> = Vec::new();
        while let Some(index) = solve.unexpanded.pop() {
            self.steps += 1;
            members.clear();
            if self.expand(module, reach, solve.nodes[index], &mut members) {
                // A seed of its own: what else it reaches cannot change it.
                solve.mark(index);
                continue;
            }
            let decided = &self.decided[reach as usize];
            if members
                .iter()
                .any(|member| decided.get(member) == Some(&true))
            {
                solve.mark(index);
                continue;
            }
            for &member in &members {
                self.steps += 1;
                if decided.contains_key(&member) {
                    // Decided "no" by an earlier query.
                    continue;
                }
                let at = solve.intern(member);
                solve.edge(at, index);
            }
        }
        if matches!(reach, Reach::CharValue | Reach::StorageClosed) {
            // A by-value cycle is an infinitely large type: a seed.
            solve.mark_cycles(&mut self.steps);
        }
        while let Some(index) = solve.reached.pop() {
            let mut edge = solve.head[index];
            while edge != NO_EDGE {
                self.steps += 1;
                let (dependent, next) = solve.edges[edge];
                solve.mark(dependent);
                edge = next;
            }
        }
        let decided = &mut self.decided[reach as usize];
        for (node, verdict) in solve.nodes.into_iter().zip(solve.verdict) {
            decided.insert(node, verdict);
        }
    }

    /// Scan the member types of `node` for `reach`, pushing the nodes they
    /// name into `members`; `true` when one of them holds a seed inline.
    fn expand(
        &mut self,
        module: &impl DefinitionSource,
        reach: Reach,
        node: TableReferent,
        members: &mut Vec<TableReferent>,
    ) -> bool {
        let ReachMemo { defs, steps, .. } = self;
        if reach == Reach::CharValue {
            return expand_char_value(module, defs, steps, node, members);
        }
        let mut seeded = false;
        let strict = reach == Reach::StorageClosed;
        match node {
            TableReferent::Ty(index) => {
                if let Some(ty) = module.types().get(index) {
                    seeded |= scan(reach, ty, members, steps);
                } else {
                    seeded |= strict;
                }
            }
            TableReferent::FuncTy(index) => {
                seeded |= strict;
                // Only the handle walk names a signature.
                if let Some(signature) = module.func_types().get(index) {
                    for ty in signature.params.iter().chain(&signature.returns) {
                        seeded |= scan(reach, ty, members, steps);
                    }
                }
            }
            TableReferent::Struct(id) => {
                let mut count = 0usize;
                defs.each_struct(module, StructId::new(id), |def| {
                    count += 1;
                    for field in &def.fields {
                        seeded |= scan(reach, &field.ty, members, steps);
                    }
                });
                seeded |= strict && count != 1;
            }
            TableReferent::Enum(id) => {
                let mut count = 0usize;
                defs.each_enum(module, EnumId::new(id), |def| {
                    count += 1;
                    for ty in def.variants.iter().flat_map(|variant| &variant.fields) {
                        seeded |= scan(reach, ty, members, steps);
                    }
                });
                seeded |= strict && count != 1;
            }
            TableReferent::Record(id) => {
                let mut count = 0usize;
                defs.each_record(module, RecordId::new(id), |def| {
                    count += 1;
                    for field in &def.fields {
                        seeded |= scan(reach, &field.ty, members, steps);
                    }
                });
                seeded |= strict && count != 1;
            }
            TableReferent::ClosureTy(index) => {
                // Handle reachability and storage policy follow captures.
                // The bool walk stops here; closure-by-value uses the type
                // itself as its seed. Only handle reachability follows the
                // code signature, which is not stored in the capture frame.
                if let Some(closure) = module.closure_types().get(index) {
                    for capture in &closure.captures {
                        seeded |= scan(reach, capture, members, steps);
                    }
                    // The signature is a bare `FuncTyId` field, not a
                    // spelling, so no scan names it: it is a member of its
                    // own, as the whole-module summary records it.
                    if reach == Reach::Handle {
                        members.push(TableReferent::FuncTy(closure.func.as_usize()));
                    }
                } else {
                    seeded |= strict;
                }
            }
        }
        seeded
    }
}

/// Scan one inline spelling for `reach`: `true` when it holds a seed itself;
/// every table node it names, through the inline children `reach` follows,
/// is pushed into `out`. Iterative: inline nesting costs heap, not stack.
fn scan(reach: Reach, ty: &Ty, out: &mut Vec<TableReferent>, steps: &mut u64) -> bool {
    match reach {
        Reach::CharValue => scan_char_value(ty, out, steps),
        Reach::Handle => {
            let mut found = false;
            ty.visit_types(|child| {
                *steps += 1;
                found |= matches!(child, Ty::Handle(_));
                if let Some(referent) = table_referent(child) {
                    out.push(referent);
                }
            });
            found
        }
        Reach::ClosureByValue | Reach::BoolLane | Reach::StorageValue | Reach::StorageClosed => {
            let storage = matches!(reach, Reach::StorageValue | Reach::StorageClosed);
            let closure = reach == Reach::ClosureByValue;
            let mut pending: Vec<&Ty> = vec![ty];
            while let Some(ty) = pending.pop() {
                *steps += 1;
                match ty {
                    Ty::Error | Ty::Dialect(_) if reach == Reach::StorageClosed => return true,
                    Ty::Storage(_) if storage => return true,
                    Ty::Storage(_) => {}
                    Ty::Set(id, _) | Ty::Sequence(id) if storage => {
                        out.push(TableReferent::Ty(id.as_usize()))
                    }
                    Ty::Closure(id) if storage => out.push(TableReferent::ClosureTy(id.as_usize())),
                    Ty::Closure(_) if closure => return true,
                    Ty::Bool if reach == Reach::BoolLane => return true,
                    Ty::Tuple(elems) => pending.extend(elems.iter()),
                    // A tensor's element is an inline child, as a vector's
                    // is: following it can only find a seed, which refuses.
                    Ty::Vector(elem, _) | Ty::Tensor(elem, _) => pending.push(elem),
                    Ty::Array(id, _) | Ty::Refine(id, _) => {
                        out.push(TableReferent::Ty(id.as_usize()));
                    }
                    Ty::Struct(id) => out.push(TableReferent::Struct(id.index())),
                    Ty::Enum(id) => out.push(TableReferent::Enum(id.index())),
                    // The bool walk never followed a record.
                    Ty::Record(id) if closure || storage => {
                        out.push(TableReferent::Record(id.index()))
                    }
                    // An address's bytes are an address whatever it points
                    // at; a code address, a scalar, an opaque nominal type
                    // and a logical collection hold neither seed by value.
                    Ty::Closure(_)
                    | Ty::Bool
                    | Ty::Record(_)
                    | Ty::Ref(_)
                    | Ty::RefMut(_)
                    | Ty::PtrConst(_)
                    | Ty::PtrMut(_)
                    | Ty::Rc(_)
                    | Ty::Ptr
                    | Ty::FatPtr(_)
                    | Ty::Func(_)
                    | Ty::Handle(_)
                    | Ty::Dialect(_)
                    | Ty::Set(_, _)
                    | Ty::Sequence(_)
                    | Ty::I8
                    | Ty::I16
                    | Ty::I32
                    | Ty::I64
                    | Ty::I128
                    | Ty::U8
                    | Ty::U16
                    | Ty::U32
                    | Ty::U64
                    | Ty::U128
                    | Ty::Isize
                    | Ty::Usize
                    | Ty::F16
                    | Ty::F32
                    | Ty::F64
                    | Ty::Char
                    | Ty::Unit
                    | Ty::Never
                    | Ty::Error => {}
                    Ty::Ext(e) => e.unreachable(),
                }
            }
            false
        }
    }
}

/// [`ReachMemo::expand`] for [`Reach::CharValue`]: the one definition an id
/// resolves to, and a missing one is a seed (see the module docs).
fn expand_char_value(
    module: &impl DefinitionSource,
    defs: &mut DefIndex,
    steps: &mut u64,
    node: TableReferent,
    members: &mut Vec<TableReferent>,
) -> bool {
    let mut seeded = false;
    let mut each = |ty: &Ty, members: &mut Vec<TableReferent>| {
        seeded |= scan_char_value(ty, members, steps);
    };
    let found = match node {
        TableReferent::Ty(index) => module.types().get(index).map(|ty| each(ty, members)),
        TableReferent::Struct(id) => defs
            .struct_def(module, StructId::new(id))
            .map(|def| def.fields.iter().for_each(|field| each(&field.ty, members))),
        TableReferent::Enum(id) => defs.enum_def(module, EnumId::new(id)).map(|def| {
            def.variants
                .iter()
                .flat_map(|variant| &variant.fields)
                .for_each(|ty| each(ty, members));
        }),
        TableReferent::Record(id) => defs
            .record_def(module, RecordId::new(id))
            .map(|def| def.fields.iter().for_each(|field| each(&field.ty, members))),
        // A closure VALUE is its code pointer and its captured frame: the
        // frame is carried by value, the signature is not.
        TableReferent::ClosureTy(index) => module
            .closure_types()
            .get(index)
            .map(|closure| closure.captures.iter().for_each(|ty| each(ty, members))),
        // No `Char` scan names a signature.
        TableReferent::FuncTy(_) => Some(()),
    };
    // A dangling reference fails closed.
    seeded || found.is_none()
}

/// [`scan`] for [`Reach::CharValue`]: `true` on an inline `Char`; pushes the
/// table node of every `Array` / `Sequence` / `Set` / `Refine` entry, struct,
/// enum, record and closure type it holds by value. A pointer arm stops it
/// (loading a `&char` loads an address), and so does every scalar, a code
/// address, an opaque nominal type and a fat pointer.
fn scan_char_value(ty: &Ty, out: &mut Vec<TableReferent>, steps: &mut u64) -> bool {
    let mut pending: Vec<&Ty> = vec![ty];
    while let Some(ty) = pending.pop() {
        *steps += 1;
        match ty {
            Ty::Storage(_) => {}
            Ty::Char => return true,
            Ty::Tuple(elems) => pending.extend(elems.iter()),
            Ty::Vector(elem, _) | Ty::Tensor(elem, _) => pending.push(elem),
            Ty::Array(id, _) | Ty::Sequence(id) | Ty::Set(id, _) | Ty::Refine(id, _) => {
                out.push(TableReferent::Ty(id.as_usize()));
            }
            Ty::Struct(id) => out.push(TableReferent::Struct(id.index())),
            Ty::Enum(id) => out.push(TableReferent::Enum(id.index())),
            Ty::Record(id) => out.push(TableReferent::Record(id.index())),
            Ty::Closure(id) => out.push(TableReferent::ClosureTy(id.as_usize())),
            Ty::Ref(_)
            | Ty::RefMut(_)
            | Ty::PtrConst(_)
            | Ty::PtrMut(_)
            | Ty::Rc(_)
            | Ty::Ptr
            | Ty::FatPtr(_)
            | Ty::Func(_)
            | Ty::Handle(_)
            | Ty::Dialect(_)
            | Ty::Bool
            | Ty::I8
            | Ty::I16
            | Ty::I32
            | Ty::I64
            | Ty::I128
            | Ty::U8
            | Ty::U16
            | Ty::U32
            | Ty::U64
            | Ty::U128
            | Ty::Isize
            | Ty::Usize
            | Ty::F16
            | Ty::F32
            | Ty::F64
            | Ty::Unit
            | Ty::Never
            | Ty::Error => {}
            Ty::Ext(e) => e.unreachable(),
        }
    }
    false
}

#[cfg(test)]
mod char_value_tests {
    use super::*;
    use crate::ty::{ClosureTy, EnumVariant, FieldDef, RecordDef, StructRepr};
    use crate::value::{ClosureTyId, FuncTyId, TyId};

    fn strukt(id: u32, fields: Vec<Ty>) -> StructDef {
        StructDef {
            id: StructId::new(id),
            name: format!("S{id}"),
            fields: fields
                .into_iter()
                .map(|ty| FieldDef {
                    name: "f".into(),
                    ty,
                    offset: None,
                })
                .collect(),
            size: None,
            align: None,
            repr: StructRepr::C,
            origin: None,
        }
    }

    fn s(id: u32) -> Ty {
        Ty::Struct(StructId::new(id))
    }

    fn char_value(memo: &mut ReachMemo, module: &Module, ty: &Ty) -> bool {
        memo.reaches(module, Reach::CharValue, ty)
    }

    /// `S0 = { bottom }`, `S{k} = { S{k-1} }`.
    fn chain(depth: u32, bottom: Ty) -> Module {
        let mut module = Module::new("chain");
        module.structs.push(strukt(0, vec![bottom]));
        for k in 1..depth {
            module.structs.push(strukt(k, vec![s(k - 1)]));
        }
        module
    }

    /// `P0 = { bottom }`, `P{k+1} = { Pk, Pk }`: 2^depth paths.
    fn tower(depth: u32, bottom: Ty) -> Module {
        let mut module = Module::new("tower");
        module.structs.push(strukt(0, vec![bottom]));
        for k in 1..=depth {
            module.structs.push(strukt(k, vec![s(k - 1), s(k - 1)]));
        }
        module
    }

    /// Every shape at `depth`: the verdicts, and linear work for one memo
    /// asked about every level.
    fn shapes(depth: u32) {
        let bound = |memo: &ReachMemo| {
            assert!(
                memo.steps <= 12 * u64::from(depth) + 64,
                "{depth}: {} steps",
                memo.steps
            );
        };
        // A char-free chain carries no `Char`, however deep; one at the
        // bottom is carried from every level.
        for (bottom, want) in [(Ty::U32, false), (Ty::Char, true)] {
            let module = chain(depth, bottom);
            let mut memo = ReachMemo::default();
            assert_eq!(char_value(&mut memo, &module, &s(depth - 1)), want);
            for k in (0..depth).rev() {
                assert_eq!(char_value(&mut memo, &module, &s(k)), want, "{k}");
            }
            bound(&memo);
        }
        // A ring (S0 names the top) is an infinitely large type: carried,
        // entered anywhere.
        let mut ring = chain(depth, Ty::U32);
        ring.structs[0] = strukt(0, vec![Ty::U32, s(depth - 1)]);
        let mut memo = ReachMemo::default();
        for k in [depth / 2, 0, depth - 1] {
            assert!(char_value(&mut memo, &ring, &s(k)), "{k}");
        }
        bound(&memo);
        // A dangling reference at the bottom fails closed.
        let dangling = chain(depth, s(depth + 7));
        let mut memo = ReachMemo::default();
        assert!(char_value(&mut memo, &dangling, &s(depth - 1)));
        bound(&memo);
        // 2^depth paths, each node decided once.
        for (bottom, want) in [(Ty::U32, false), (Ty::Char, true)] {
            let module = tower(depth, bottom);
            let mut memo = ReachMemo::default();
            assert_eq!(char_value(&mut memo, &module, &s(depth)), want);
            bound(&memo);
        }
    }

    #[test]
    fn deep_chains_rings_and_towers_are_decided_in_linear_work_on_a_small_stack() {
        // The work bound FIRST, at a size where a walk per path would not
        // end but a walk per level would.
        shapes(2000);
        let worker = std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| shapes(100_000))
            .expect("spawn");
        worker.join().expect("no stack overflow, linear work");
    }

    #[test]
    fn only_the_char_question_takes_a_cycle_or_a_dangling_reference_as_a_seed() {
        let mut ring = Module::new("ring");
        ring.structs.push(strukt(0, vec![s(1)]));
        ring.structs.push(strukt(1, vec![s(0), Ty::U8]));
        // Its own member, through an enum, a record, a closure capture and
        // type-table entries.
        let mut selfish = Module::new("self");
        let entry = TyId::new(0);
        selfish.types.push(Ty::Sequence(entry));
        selfish.enums.push(EnumDef::new(
            EnumId::new(0),
            "E",
            vec![EnumVariant {
                name: "V".into(),
                fields: vec![Ty::Enum(EnumId::new(0))],
                field_names: Vec::new(),
            }],
        ));
        selfish.records.push(RecordDef {
            id: RecordId::new(0),
            name: "R".into(),
            fields: vec![FieldDef {
                name: "r".into(),
                ty: Ty::Tuple(vec![Ty::U8, Ty::Record(RecordId::new(0))]),
                offset: None,
            }],
        });
        selfish.closure_types.push(ClosureTy {
            func: FuncTyId::new(0),
            captures: vec![Ty::Vector(Box::new(Ty::Closure(ClosureTyId::new(0))), 2)],
        });
        for (module, ty) in [
            (&ring, s(0)),
            (&ring, Ty::Tuple(vec![Ty::U8, s(1)])),
            (&selfish, Ty::Array(entry, 1)),
            (&selfish, Ty::Set(entry, crate::ty::SetRepr::Bitset)),
            (&selfish, Ty::Enum(EnumId::new(0))),
            (&selfish, Ty::Record(RecordId::new(0))),
            (&selfish, Ty::Closure(ClosureTyId::new(0))),
            (&ring, s(9)),
            (&ring, Ty::Array(TyId::new(3), 1)),
            (&ring, Ty::Closure(ClosureTyId::new(4))),
        ] {
            let mut memo = ReachMemo::default();
            assert!(char_value(&mut memo, module, &ty), "{ty:?}");
            for reach in [Reach::ClosureByValue, Reach::BoolLane, Reach::Handle] {
                // (A closure is the closure question's own seed.)
                if reach == Reach::ClosureByValue && matches!(ty, Ty::Closure(_)) {
                    continue;
                }
                assert!(!memo.reaches(module, reach, &ty), "{reach:?} {ty:?}");
            }
        }
        // A pointer arm stops the char question: a `&S` is an address.
        let mut memo = ReachMemo::default();
        assert!(!char_value(&mut memo, &ring, &Ty::Ref(Box::new(s(0)))));
        assert!(!char_value(&mut memo, &ring, &Ty::PtrMut(Box::new(s(9)))));
    }

    #[test]
    fn an_id_resolves_to_the_definition_module_struct_def_names() {
        // The row at the id's position when it has the id, else the first
        // row with it: `Module::struct_def`, and the walk this replaces.
        let cases: [(Vec<StructDef>, bool); 4] = [
            (
                vec![strukt(1, vec![Ty::U8]), strukt(1, vec![Ty::Char])],
                true,
            ),
            (
                vec![strukt(1, vec![Ty::Char]), strukt(1, vec![Ty::U8])],
                false,
            ),
            (
                vec![strukt(5, vec![Ty::U8]), strukt(5, vec![Ty::Char])],
                false,
            ),
            (
                vec![strukt(5, vec![Ty::Char]), strukt(5, vec![Ty::U8])],
                true,
            ),
        ];
        for (structs, want) in cases {
            let mut module = Module::new("resolve");
            module.structs = structs;
            let id = module.structs[0].id;
            assert_eq!(
                module
                    .struct_def(id)
                    .is_some_and(|def| def.fields[0].ty == Ty::Char),
                want
            );
            let mut memo = ReachMemo::default();
            assert_eq!(char_value(&mut memo, &module, &Ty::Struct(id)), want);
        }
    }

    #[test]
    fn borrowed_storage_query_matches_module_and_preserves_all_pointer_boundaries() {
        let mut module = Module::new("borrowed storage policy");
        let storage = module
            .add_type(Ty::Storage(crate::StorageLayout::new(8, 8)))
            .unwrap();
        module.structs = vec![
            strukt(0, vec![Ty::U64]),
            strukt(1, vec![Ty::Array(storage, 1)]),
        ];
        let roots = [
            Ty::U64,
            s(0),
            s(1),
            Ty::Array(storage, 0),
            Ty::Tuple(vec![
                Ty::Never,
                Ty::Storage(crate::StorageLayout::new(8, 8)),
            ]),
            Ty::Ref(Box::new(Ty::Storage(crate::StorageLayout::new(8, 8)))),
            Ty::RefMut(Box::new(Ty::Storage(crate::StorageLayout::new(8, 8)))),
            Ty::PtrConst(Box::new(Ty::Storage(crate::StorageLayout::new(8, 8)))),
            Ty::PtrMut(Box::new(Ty::Storage(crate::StorageLayout::new(8, 8)))),
            Ty::Rc(Box::new(Ty::Storage(crate::StorageLayout::new(8, 8)))),
        ];
        let mut query = ByValueStorageQuery::for_module(&module);
        let layouts = module.layout_table();
        for root in &roots {
            assert_eq!(
                query.is_storage_free(root),
                !layouts.type_contains_storage_by_value(root),
                "{root:?}"
            );
        }
        // A code pointer's signature is not a by-value child.
        assert!(query.is_storage_free(&Ty::Func(crate::FuncTyId::new(99))));
    }

    #[test]
    fn inactive_never_storage_is_not_hidden_by_uninhabitedness() {
        let mut module = Module::new("inactive storage");
        module.enums.push(EnumDef::new(
            crate::EnumId::new(0),
            "Selected",
            vec![
                crate::EnumVariant {
                    name: "Value".into(),
                    fields: vec![Ty::U64],
                    field_names: vec![],
                },
                crate::EnumVariant {
                    name: "Absent".into(),
                    fields: vec![Ty::Never, Ty::Storage(crate::StorageLayout::new(8, 8))],
                    field_names: vec![],
                },
            ],
        ));
        assert!(
            crate::Inhabitedness::for_module(&module)
                .variant_is_uninhabited(&module.enums[0].variants[1])
        );
        let mut query = ByValueStorageQuery::for_module(&module);
        assert!(!query.is_storage_free(&Ty::Enum(crate::EnumId::new(0))));
    }

    #[test]
    fn borrowed_storage_raw_schema_refuses_missing_cycles_and_duplicate_definitions() {
        let mut module = Module::new("raw schema");
        module.structs = vec![
            strukt(0, vec![s(0)]),
            strukt(1, vec![Ty::U64]),
            strukt(1, vec![Ty::U64]),
        ];
        let mut query = ByValueStorageQuery::for_module(&module);
        for root in [
            s(0),
            s(1),
            s(99),
            Ty::Enum(crate::EnumId::new(99)),
            Ty::Record(crate::RecordId::new(99)),
            Ty::Array(crate::TyId::new(99), 0),
            Ty::Closure(crate::ClosureTyId::new(99)),
            Ty::Error,
        ] {
            assert!(
                !query.is_storage_free(&root),
                "raw incomplete schema {root:?}"
            );
        }
        // Legacy Module/LayoutTable predicates retain their historical answers
        // on malformed input; only the new raw-data boundary is conservative.
        assert!(!module.layout_table().type_contains_storage_by_value(&s(0)));
        assert!(!module.layout_table().type_contains_storage_by_value(&s(1)));
    }

    #[test]
    fn borrowed_storage_context_and_shared_deep_graph_memos_are_separate() {
        let plain = chain(4096, Ty::U64);
        let blocked = chain(4096, Ty::Storage(crate::StorageLayout::new(8, 8)));
        let mut plain_query = ByValueStorageQuery::for_module(&plain);
        let mut blocked_query = ByValueStorageQuery::for_module(&blocked);
        assert!(plain_query.is_storage_free(&s(4095)));
        assert!(!blocked_query.is_storage_free(&s(4095)));
        let before = plain_query.memo.steps;
        for _ in 0..100 {
            assert!(plain_query.is_storage_free(&s(4095)));
        }
        assert!(plain_query.memo.steps - before <= 100);
        assert!(plain_query.memo.steps < 100_000);
    }

    #[test]
    fn borrowed_storage_records_enums_and_closure_captures_share_module_meaning() {
        let mut module = Module::new("all by-value tables");
        module.records.push(RecordDef {
            id: crate::RecordId::new(0),
            name: "record".into(),
            fields: vec![FieldDef {
                name: "bytes".into(),
                ty: Ty::Storage(crate::StorageLayout::new(8, 8)),
                offset: None,
            }],
        });
        module.enums.push(EnumDef::new(
            crate::EnumId::new(0),
            "enum",
            vec![EnumVariant {
                name: "Value".into(),
                fields: vec![Ty::Record(crate::RecordId::new(0))],
                field_names: vec![],
            }],
        ));
        module.closure_types.push(ClosureTy {
            func: FuncTyId::new(0),
            captures: vec![Ty::Enum(crate::EnumId::new(0))],
        });
        let roots = [
            Ty::Record(crate::RecordId::new(0)),
            Ty::Enum(crate::EnumId::new(0)),
            Ty::Closure(ClosureTyId::new(0)),
        ];
        let mut query = ByValueStorageQuery::for_module(&module);
        for root in roots {
            assert!(!query.is_storage_free(&root));
            assert!(module.layout_table().type_contains_storage_by_value(&root));
        }
    }

    #[test]
    fn borrowed_storage_duplicate_enum_and_record_ids_do_not_become_closed_answers() {
        let mut module = Module::new("duplicate nominal tables");
        let row = RecordDef {
            id: crate::RecordId::new(0),
            name: "record".into(),
            fields: vec![],
        };
        module.records.extend([row.clone(), row]);
        let row = EnumDef::new(
            crate::EnumId::new(0),
            "enum",
            vec![EnumVariant {
                name: "Value".into(),
                fields: vec![Ty::U64],
                field_names: vec![],
            }],
        );
        module.enums.extend([row.clone(), row]);
        let mut query = ByValueStorageQuery::for_module(&module);
        assert!(!query.is_storage_free(&Ty::Record(crate::RecordId::new(0))));
        assert!(!query.is_storage_free(&Ty::Enum(crate::EnumId::new(0))));
    }
}

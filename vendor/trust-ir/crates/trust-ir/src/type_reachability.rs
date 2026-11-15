// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Bounded reachability over inline types and the module's named type tables.

use std::collections::{BTreeSet, HashMap, HashSet};
use std::ops::Range;

use crate::value::{ClosureTyId, FuncTyId};
use crate::{FatPtrKind, Inst, Module, Ty};
mod observed;
pub use observed::ObservedNominalTypeReachability;

/// Which nominal axis a reachability query asks about. The axes are tracked
/// independently because their rules differ: a dialect value may flow through
/// a `DialectOp`, or as an ARGUMENT of an indirect call over a pointer-like
/// callee (never as its result — WS2.20), a v43 handle may not; and a
/// CALLABLE (a function pointer, a closure, or a `dyn` value's vtable) is what
/// the spawn census's indirect-call pools are keyed by (design 2026-09-29
/// §5.4: LAUNDER and the rule H operand walk).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NominalAxis {
    Dialect = 0,
    Handle = 1,
    Callable = 2,
}

const AXES: [NominalAxis; 3] = [
    NominalAxis::Dialect,
    NominalAxis::Handle,
    NominalAxis::Callable,
];

/// Whether types transitively contain a nominal type — a [`Ty::Dialect`], a
/// v43 [`Ty::Handle`], or a callable ([`Ty::Func`], [`Ty::Closure`], or a
/// trait-object vtable word) — in one exact module.
///
/// Build with [`Module::nominal_type_reachability`]. ONE builder pass over the
/// module's named type tables yields every axis's bitset. The summary borrows
/// that module, preventing mutation while its indexed results are in use. It
/// answers only type reachability; it establishes no representation or proof
/// authority. Missing table entries contribute no edge and remain a validation
/// error. Duplicate named IDs conservatively combine all matching definitions.
#[derive(Debug)]
pub struct NominalTypeReachability<'module> {
    _module: &'module Module,
    tables: TypeTableVertices,
    /// Indexed by [`NominalAxis`].
    reachable: [Vec<bool>; 3],
}

impl NominalTypeReachability<'_> {
    /// Whether this type contains a dialect type, including through named
    /// tables, function signatures, closure captures, and slice elements.
    ///
    /// This visits the inline spelling once and reads indexed table results;
    /// it never traverses the table graph. Expected time is linear in the
    /// inline occurrences, with iterative scratch bounded by inline depth.
    pub fn contains_dialect(&self, ty: &Ty) -> bool {
        self.contains(NominalAxis::Dialect, ty)
    }

    /// Whether this type contains a v43 opaque runtime handle, including
    /// through named tables, function signatures, closure captures, and slice
    /// elements. Same cost profile as [`Self::contains_dialect`].
    pub fn contains_handle(&self, ty: &Ty) -> bool {
        self.contains(NominalAxis::Handle, ty)
    }

    /// Whether any type spelled by an instruction transitively contains a
    /// dialect type. Includes type-valued dialect attributes, but not the
    /// separately declared types of SSA operands.
    ///
    /// Each inline occurrence is visited once, with indexed table lookups.
    pub fn contains_dialect_instruction_types(&self, inst: &Inst) -> bool {
        self.contains_instruction_types(NominalAxis::Dialect, inst)
    }

    /// Whether any type spelled by an instruction transitively contains a
    /// v43 opaque runtime handle. Includes type-valued dialect attributes, but
    /// not the separately declared types of SSA operands.
    pub fn contains_handle_instruction_types(&self, inst: &Inst) -> bool {
        self.contains_instruction_types(NominalAxis::Handle, inst)
    }

    /// Whether a value of this type may carry a callable spelled in its type:
    /// a function pointer ([`Ty::Func`]), a closure ([`Ty::Closure`]), or a
    /// `dyn` vtable word ([`FatPtrKind::TraitObject`] or
    /// [`FatPtrKind::ContainerVtable`]), including through named tables and
    /// closure captures. Same cost profile as [`Self::contains_dialect`].
    ///
    /// An untyped [`Ty::Ptr`] is NOT counted: it names no callable, and
    /// counting it would make every pointer cast a LAUNDER. What an untyped
    /// pointer may lead to is the rule H question, answered by
    /// [`Module::callable_carriers`] (which reports it as opaque).
    pub fn contains_callable(&self, ty: &Ty) -> bool {
        self.contains(NominalAxis::Callable, ty)
    }

    fn contains(&self, axis: NominalAxis, ty: &Ty) -> bool {
        let mut found = false;
        ty.visit_types(|child| found |= self.contains_occurrence(axis, child));
        found
    }

    fn contains_instruction_types(&self, axis: NominalAxis, inst: &Inst) -> bool {
        let mut found = false;
        inst.visit_types(|ty| found |= self.contains_occurrence(axis, ty));
        found
    }

    fn contains_occurrence(&self, axis: NominalAxis, ty: &Ty) -> bool {
        seeds(axis, ty)
            || self
                .tables
                .referenced_vertex(ty)
                .is_some_and(|vertex| self.reachable[axis as usize][vertex])
    }
}

/// Whether an inline occurrence seeds `axis` directly. A callable seed may
/// also reference a table (a `Ty::Func` names its signature), so seeding and
/// table edges are independent.
fn seeds(axis: NominalAxis, ty: &Ty) -> bool {
    match axis {
        NominalAxis::Dialect => matches!(ty, Ty::Dialect(_)),
        NominalAxis::Handle => matches!(ty, Ty::Handle(_)),
        NominalAxis::Callable => matches!(
            ty,
            Ty::Func(_)
                | Ty::Closure(_)
                | Ty::FatPtr(FatPtrKind::TraitObject { .. } | FatPtrKind::ContainerVtable)
        ),
    }
}

/// The callables a value of one type may carry, for the spawn census's rule H
/// operand walk (design 2026-09-29 §5.4). Built by
/// [`Module::callable_carriers`].
///
/// Signature types are not carried values: a `Ty::Func` contributes its own
/// signature, never the types of its parameters, and a closure contributes
/// its signature and its CAPTURES (which are part of the value).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct CallableCarriers {
    /// Function-pointer signatures the value may hold.
    pub fn_types: BTreeSet<FuncTyId>,
    /// Closure types the value may hold.
    pub closures: BTreeSet<ClosureTyId>,
    /// Trait-object principals ([`FatPtrKind::TraitObject`] ids).
    pub principals: BTreeSet<u32>,
    /// A vtable word whose principal the type does not state
    /// ([`FatPtrKind::ContainerVtable`]).
    pub erased_dyn: bool,
    /// The value may lead to ANY callable: it holds an untyped pointer
    /// ([`Ty::Ptr`], whose pointee and code-pointer status are unstated), an
    /// opaque [`Ty::Dialect`] or [`Ty::Error`], or a table reference this
    /// module does not define. Fail closed: absent is never "carries nothing".
    pub opaque: bool,
}

impl CallableCarriers {
    /// Whether a callable is spelled in the type. Agrees with
    /// [`NominalTypeReachability::contains_callable`].
    #[must_use]
    pub fn carries_typed_callable(&self) -> bool {
        !self.fn_types.is_empty()
            || !self.closures.is_empty()
            || !self.principals.is_empty()
            || self.erased_dyn
    }

    /// Whether the value can carry no callable at all.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        !self.carries_typed_callable() && !self.opaque
    }
}

/// Whether types transitively contain a [`Ty::Dialect`] in one exact module.
///
/// Build with [`Module::dialect_type_reachability`]. A dialect-only view of
/// [`NominalTypeReachability`]; the signatures predate v43 and are kept for
/// the callers that ask only the dialect question.
#[derive(Debug)]
pub struct DialectTypeReachability<'module> {
    nominal: NominalTypeReachability<'module>,
}

impl DialectTypeReachability<'_> {
    /// Whether this type contains a dialect type, including through named
    /// tables, function signatures, closure captures, and slice elements.
    ///
    /// This visits the inline spelling once and reads indexed table results;
    /// it never traverses the table graph. Expected time is linear in the
    /// inline occurrences, with iterative scratch bounded by inline depth.
    pub fn contains(&self, ty: &Ty) -> bool {
        self.nominal.contains_dialect(ty)
    }

    /// Whether any type spelled by an instruction transitively contains a
    /// dialect type. Includes type-valued dialect attributes, but not the
    /// separately declared types of SSA operands.
    ///
    /// Each inline occurrence is visited once, with indexed table lookups.
    pub fn contains_instruction_types(&self, inst: &Inst) -> bool {
        self.nominal.contains_dialect_instruction_types(inst)
    }
}

impl Module {
    /// Build exact transitive dialect-type reachability, including cyclic
    /// references between any of the module's named type tables.
    ///
    /// The dialect-only view of [`Module::nominal_type_reachability`]; same
    /// cost, same one builder pass.
    pub fn dialect_type_reachability(&self) -> DialectTypeReachability<'_> {
        DialectTypeReachability {
            nominal: self.nominal_type_reachability(),
        }
    }

    /// Build exact transitive nominal-type reachability — dialect types AND
    /// v43 opaque runtime handles, as two independent bitsets — including
    /// cyclic references between any of the module's named type tables.
    ///
    /// Construction takes expected `O(V + T + E)` time and `O(V + E + D)` scratch for
    /// `V` table entries, `T` inline type occurrences in those entries, `E`
    /// reference edges, and maximum inline depth `D`. Each entry and inline
    /// occurrence is scanned once; a reverse-edge worklist per axis propagates
    /// direct nominal occurrences without recursion or a depth cutoff. The
    /// retained summary takes `O(V)` space. Callers needing only a census can
    /// first use [`Module::visit_types`] and skip construction when no nominal
    /// type occurs.
    pub fn nominal_type_reachability(&self) -> NominalTypeReachability<'_> {
        let mut builder = ReachabilityBuilder::new(self);
        for (index, ty) in self.types.iter().enumerate() {
            builder.record_type(builder.tables.types.start + index, ty);
        }
        for (index, signature) in self.func_types.iter().enumerate() {
            let owner = builder.tables.func_types.start + index;
            for ty in signature.params.iter().chain(&signature.returns) {
                builder.record_type(owner, ty);
            }
        }
        for definition in &self.structs {
            let owner = builder.tables.structs[&definition.id.index()];
            for field in &definition.fields {
                builder.record_type(owner, &field.ty);
            }
        }
        for definition in &self.enums {
            let owner = builder.tables.enums[&definition.id.index()];
            for variant in &definition.variants {
                for ty in &variant.fields {
                    builder.record_type(owner, ty);
                }
            }
        }
        for definition in &self.records {
            let owner = builder.tables.records[&definition.id.index()];
            for field in &definition.fields {
                builder.record_type(owner, &field.ty);
            }
        }
        for (index, closure) in self.closure_types.iter().enumerate() {
            let owner = builder.tables.closure_types.start + index;
            if let Some(target) = table_vertex(&builder.tables.func_types, closure.func.as_usize())
            {
                builder.record_dependency(owner, target);
            }
            for ty in &closure.captures {
                builder.record_type(owner, ty);
            }
        }
        builder.finish(self)
    }

    /// Whether `ty` reaches a v43 opaque runtime handle in THIS module,
    /// FOLLOWING named table references.
    ///
    /// The targeted, single-type form of
    /// [`NominalTypeReachability::contains_handle`], and the one to reach for
    /// when a caller asks the handle question about a handful of types. It
    /// answers exactly the same question — same edges, same seeds, via the
    /// same [`table_referent`] classifier — but costs only the type's own
    /// reachable closure plus one pass over each definition table it meets
    /// (comparisons only, when the table's ids are their positions; a hash
    /// index otherwise) instead of a whole-module builder pass. Building
    /// the summary per node is `O(module)` each time: measured on a
    /// 4000-entry type graph, 5000 queries took 453ms via the summary and
    /// 0.5ms via this walk. Prefer the summary when the same module is asked
    /// about every type (the validator's transport rule does); a caller that
    /// asks this question inside a per-node loop asks one
    /// [`crate::LayoutTable`] ([`crate::LayoutTable::type_reaches_handle`]),
    /// whose reachability memo decides each node once over the table's life.
    ///
    /// **This is not [`Ty::contains_handle`].** That method inspects the
    /// INLINE spelling only and is documented as such, so it answers `false`
    /// for `Refine(ty.0, _)`, `Array(ty.0, _)`, `Struct(s0)` and every other
    /// reference whose referent is the handle. A guard that must fail closed
    /// on a handle cannot use it unless something else independently refuses
    /// the table-backed spelling.
    ///
    /// Duplicate named ids contribute ALL matching definitions, matching the
    /// whole-module summary's conservatism (a duplicate id is itself a
    /// `validate_module` error, so this only widens a refusal on a module that
    /// is already rejected).
    pub fn type_reaches_handle(&self, ty: &Ty) -> bool {
        crate::reach::ReachMemo::default().reaches(self, crate::reach::Reach::Handle, ty)
    }

    /// The callables a value of type `ty` may carry in THIS module, following
    /// named table references and closure captures: the rule H operand walk
    /// of the spawn census (design 2026-09-29 §5.4).
    ///
    /// Costs the type's own reachable closure plus one pass over each
    /// definition table (struct, enum, record) it meets, like
    /// [`Self::type_reaches_handle`]; a pass asking it of many types shares
    /// that index (the spawn census does, and asks it once per signature). A
    /// missing table entry, an untyped pointer and an opaque type set
    /// [`CallableCarriers::opaque`] rather than contributing nothing.
    /// Duplicate named ids contribute ALL matching definitions.
    pub fn callable_carriers(&self, ty: &Ty) -> CallableCarriers {
        self.callable_carriers_in(&mut crate::reach::DefIndex::default(), ty)
    }

    /// [`Self::callable_carriers`] reading `defs`, an all-definitions index
    /// over THIS module that a pass shares across its questions, so each call
    /// costs only the type's reach.
    pub(crate) fn callable_carriers_in(
        &self,
        defs: &mut crate::reach::DefIndex,
        ty: &Ty,
    ) -> CallableCarriers {
        let mut carriers = CallableCarriers::default();
        let mut seen: HashSet<TableReferent> = HashSet::new();
        let mut frontier: Vec<TableReferent> = Vec::new();
        let mut members: Vec<&Ty> = vec![ty];
        loop {
            for member in members.drain(..) {
                member.visit_types(|child| {
                    record_carrier(&mut carriers, child);
                    if let Some(referent) = table_referent(child)
                        && seen.insert(referent)
                    {
                        frontier.push(referent);
                    }
                });
            }
            let Some(referent) = frontier.pop() else {
                return carriers;
            };
            carriers.opaque |= !self.referent_members(referent, defs, &mut members);
        }
    }

    /// Push the member types of one table referent that a value CARRIES;
    /// `false` when this module does not define it. Duplicate named ids
    /// contribute ALL matching definitions (through `defs`, so each costs
    /// O(its definitions)). A signature is not a carried value: a function
    /// pointer does not carry its parameters, and a closure carries its
    /// captures, not its signature's types.
    fn referent_members<'module>(
        &'module self,
        referent: TableReferent,
        defs: &mut crate::reach::DefIndex,
        members: &mut Vec<&'module Ty>,
    ) -> bool {
        match referent {
            TableReferent::Ty(index) => self.types.get(index).map(|ty| members.push(ty)).is_some(),
            TableReferent::FuncTy(index) => self.func_types.get(index).is_some(),
            TableReferent::Struct(id) => {
                defs.each_struct(self, crate::value::StructId::new(id), |def| {
                    members.extend(def.fields.iter().map(|field| &field.ty));
                })
            }
            TableReferent::Enum(id) => defs.each_enum(self, crate::value::EnumId::new(id), |def| {
                members.extend(
                    def.variants
                        .iter()
                        .flat_map(|variant| variant.fields.iter()),
                );
            }),
            TableReferent::Record(id) => {
                defs.each_record(self, crate::value::RecordId::new(id), |def| {
                    members.extend(def.fields.iter().map(|field| &field.ty));
                })
            }
            TableReferent::ClosureTy(index) => {
                let Some(closure) = self.closure_types.get(index) else {
                    return false;
                };
                members.extend(&closure.captures);
                true
            }
        }
    }
}

/// Record one inline occurrence's own contribution to a carrier census.
/// Exhaustive so a new `Ty` variant forces a decision here.
fn record_carrier(carriers: &mut CallableCarriers, ty: &Ty) {
    match ty {
        Ty::Storage(_) => {}
        Ty::Func(signature) => {
            carriers.fn_types.insert(*signature);
        }
        Ty::Closure(closure) => {
            carriers.closures.insert(*closure);
        }
        Ty::FatPtr(FatPtrKind::TraitObject { trait_id }) => {
            carriers.principals.insert(*trait_id);
        }
        Ty::FatPtr(FatPtrKind::ContainerVtable) => carriers.erased_dyn = true,
        Ty::Ptr | Ty::Dialect(_) | Ty::Error => carriers.opaque = true,
        Ty::I8
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
        | Ty::Char
        | Ty::F16
        | Ty::F32
        | Ty::F64
        | Ty::Bool
        | Ty::Unit
        | Ty::Never
        | Ty::Handle(_)
        | Ty::Vector(..)
        | Ty::Tensor(..)
        | Ty::Tuple(_)
        | Ty::Array(..)
        | Ty::Set(..)
        | Ty::Sequence(_)
        | Ty::Refine(..)
        | Ty::Struct(_)
        | Ty::Enum(_)
        | Ty::Record(_)
        | Ty::Ref(_)
        | Ty::RefMut(_)
        | Ty::PtrConst(_)
        | Ty::PtrMut(_)
        | Ty::Rc(_)
        | Ty::FatPtr(FatPtrKind::Slice(_) | FatPtrKind::Str | FatPtrKind::ContainerLen) => {}
        Ty::Ext(e) => e.unreachable(),
    }
}

/// Dense ranges and sparse named-ID indexes keep the namespaces disjoint.
#[derive(Debug)]
struct TypeTableVertices {
    types: Range<usize>,
    func_types: Range<usize>,
    structs: HashMap<u32, usize>,
    enums: HashMap<u32, usize>,
    records: HashMap<u32, usize>,
    closure_types: Range<usize>,
}

impl TypeTableVertices {
    fn new(module: &Module) -> Self {
        fn range(next: &mut usize, len: usize) -> Range<usize> {
            let start = *next;
            *next += len;
            start..*next
        }
        let mut next = 0;
        let types = range(&mut next, module.types.len());
        let func_types = range(&mut next, module.func_types.len());
        let structs = range(&mut next, module.structs.len());
        let enums = range(&mut next, module.enums.len());
        let records = range(&mut next, module.records.len());
        Self {
            types,
            func_types,
            structs: named_vertices(module.structs.iter().map(|def| def.id.index()).zip(structs)),
            enums: named_vertices(module.enums.iter().map(|def| def.id.index()).zip(enums)),
            records: named_vertices(module.records.iter().map(|def| def.id.index()).zip(records)),
            closure_types: range(&mut next, module.closure_types.len()),
        }
    }

    fn referenced_vertex(&self, ty: &Ty) -> Option<usize> {
        let (table, index) = match table_referent(ty)? {
            TableReferent::Ty(index) => (&self.types, index),
            TableReferent::FuncTy(index) => (&self.func_types, index),
            TableReferent::Struct(id) => return self.structs.get(&id).copied(),
            TableReferent::Enum(id) => return self.enums.get(&id).copied(),
            TableReferent::Record(id) => return self.records.get(&id).copied(),
            TableReferent::ClosureTy(index) => (&self.closure_types, index),
        };
        table_vertex(table, index)
    }
}

/// One entry of one of the module's named type tables, as the key that
/// identifies it for cycle breaking. The single place the `Ty` variants that
/// REFERENCE a table are enumerated, so a new variant forces one decision
/// rather than drifting between the whole-module builder below and
/// [`Module::type_reaches_handle`]'s targeted walk.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum TableReferent {
    Ty(usize),
    FuncTy(usize),
    Struct(u32),
    Enum(u32),
    Record(u32),
    ClosureTy(usize),
}

pub(crate) fn table_referent(ty: &Ty) -> Option<TableReferent> {
    Some(match ty {
        Ty::Storage(_) => return None,
        Ty::Array(id, _)
        | Ty::Set(id, _)
        | Ty::Sequence(id)
        | Ty::Refine(id, _)
        | Ty::FatPtr(FatPtrKind::Slice(id)) => TableReferent::Ty(id.as_usize()),
        Ty::Func(id) => TableReferent::FuncTy(id.as_usize()),
        Ty::Struct(id) => TableReferent::Struct(id.index()),
        Ty::Enum(id) => TableReferent::Enum(id.index()),
        Ty::Record(id) => TableReferent::Record(id.index()),
        Ty::Closure(id) => TableReferent::ClosureTy(id.as_usize()),
        Ty::I8
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
        | Ty::Char
        | Ty::Error
        | Ty::F16
        | Ty::F32
        | Ty::F64
        | Ty::Bool
        | Ty::Vector(_, _)
        | Ty::Tensor(_, _)
        | Ty::Ptr
        | Ty::FatPtr(
            FatPtrKind::Str
            | FatPtrKind::TraitObject { .. }
            | FatPtrKind::ContainerLen
            | FatPtrKind::ContainerVtable,
        )
        | Ty::Unit
        | Ty::Never
        | Ty::Tuple(_)
        | Ty::Ref(_)
        | Ty::RefMut(_)
        | Ty::PtrConst(_)
        | Ty::PtrMut(_)
        | Ty::Rc(_)
        | Ty::Dialect(_)
        | Ty::Handle(_) => return None,
        Ty::Ext(e) => e.unreachable(),
    })
}

fn table_vertex(table: &Range<usize>, index: usize) -> Option<usize> {
    (index < table.len()).then(|| table.start + index)
}

fn named_vertices(entries: impl Iterator<Item = (u32, usize)>) -> HashMap<u32, usize> {
    let mut vertices = HashMap::new();
    for (id, vertex) in entries {
        // Duplicate definitions share the first vertex and contribute all
        // their dependencies/seeds when the module tables are scanned.
        vertices.entry(id).or_insert(vertex);
    }
    vertices
}

// Intrusive lists in one edge vector avoid a separate allocation per vertex.
const NO_EDGE: usize = usize::MAX;

struct ReverseEdge {
    dependent: usize,
    next: usize,
}

struct ReachabilityBuilder {
    tables: TypeTableVertices,
    /// Indexed by [`NominalAxis`].
    reachable: [Vec<bool>; 3],
    heads: Vec<usize>,
    edges: Vec<ReverseEdge>,
    /// Indexed by [`NominalAxis`].
    pending: [Vec<usize>; 3],
}

impl ReachabilityBuilder {
    fn new(module: &Module) -> Self {
        let tables = TypeTableVertices::new(module);
        let count = tables.closure_types.end;
        Self {
            tables,
            reachable: [vec![false; count], vec![false; count], vec![false; count]],
            heads: vec![NO_EDGE; count],
            edges: Vec::new(),
            pending: [Vec::new(), Vec::new(), Vec::new()],
        }
    }

    fn record_type(&mut self, owner: usize, ty: &Ty) {
        ty.visit_types(|child| {
            for axis in AXES {
                if seeds(axis, child) {
                    self.mark(axis, owner);
                }
            }
            if let Some(target) = self.tables.referenced_vertex(child) {
                self.record_dependency(owner, target);
            }
        });
    }

    fn record_dependency(&mut self, owner: usize, target: usize) {
        self.edges.push(ReverseEdge {
            dependent: owner,
            next: self.heads[target],
        });
        self.heads[target] = self.edges.len() - 1;
    }

    fn mark(&mut self, axis: NominalAxis, vertex: usize) {
        if !self.reachable[axis as usize][vertex] {
            self.reachable[axis as usize][vertex] = true;
            self.pending[axis as usize].push(vertex);
        }
    }

    fn finish(mut self, module: &Module) -> NominalTypeReachability<'_> {
        // The reverse-edge graph is shared; each axis propagates its own seeds
        // over it, so a handle behind a struct never marks that struct as
        // dialect-reaching and vice versa.
        for axis in AXES {
            while let Some(target) = self.pending[axis as usize].pop() {
                let mut edge = self.heads[target];
                while edge != NO_EDGE {
                    self.mark(axis, self.edges[edge].dependent);
                    edge = self.edges[edge].next;
                }
            }
        }
        NominalTypeReachability {
            _module: module,
            tables: self.tables,
            reachable: self.reachable,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        ClosureTy, ClosureTyId, DialectTy, EnumDef, EnumId, EnumVariant, FieldDef, FuncTy,
        FuncTyId, PredId, RecordDef, RecordId, SetRepr, StructDef, StructId, StructRepr, TyId,
    };

    fn nominal() -> Ty {
        Ty::Dialect(Box::new(DialectTy::new("example", "value", 1)))
    }

    fn array(index: u32) -> Ty {
        Ty::Array(TyId::new(index), 1)
    }

    fn field(ty: Ty) -> FieldDef {
        FieldDef {
            name: "value".into(),
            ty,
            offset: None,
        }
    }

    fn structure(id: u32, ty: Ty) -> StructDef {
        StructDef {
            id: StructId::new(id),
            name: "structure".into(),
            fields: vec![field(ty)],
            size: None,
            align: None,
            repr: StructRepr::Rust,
            origin: None,
        }
    }

    fn enumeration(id: u32, ty: Ty) -> EnumDef {
        EnumDef::new(
            EnumId::new(id),
            "enumeration",
            vec![EnumVariant {
                name: "variant".into(),
                fields: vec![ty],
                field_names: Vec::new(),
            }],
        )
    }

    fn record(id: u32, ty: Ty) -> RecordDef {
        RecordDef {
            id: RecordId::new(id),
            name: "record".into(),
            fields: vec![field(ty)],
        }
    }

    #[test]
    fn cycle_branch_reaches_every_dependent_without_tainting_unrelated_cycles() {
        let mut module = Module::new("cycles");
        // 0 <-> 1 has a nominal sibling branch; 2 references its back edge.
        // 3 <-> 4 is an independent, nominal-free component.
        module.types = vec![
            Ty::Tuple(vec![array(1), nominal()]),
            array(0),
            array(1),
            array(4),
            array(3),
        ];
        let summary = module.dialect_type_reachability();
        for index in 0..3 {
            assert!(summary.contains(&array(index)));
        }
        for index in 3..5 {
            assert!(!summary.contains(&array(index)));
        }
    }

    #[test]
    fn cycles_without_any_nominal_type_reach_nothing() {
        let mut module = Module::new("empty cycles");
        module.types = vec![array(1), array(0), array(2)];
        let summary = module.dialect_type_reachability();
        for ty in &module.types {
            assert!(!summary.contains(ty));
        }
    }

    #[test]
    fn long_named_chain_uses_no_rust_call_stack_or_depth_cutoff() {
        let mut module = Module::new("long chain");
        for index in 0..100_000 {
            module.types.push(array(index + 1));
        }
        module.types.push(nominal());
        let summary = module.dialect_type_reachability();
        assert!(summary.contains(&array(0)));
        assert!(summary.contains(&array(50_000)));
        assert!(!summary.contains(&Ty::Bool));
    }

    #[test]
    fn every_named_and_inline_edge_class_reaches_nominal_types() {
        let mut module = Module::new("all edges");
        module.types.push(nominal());
        module.func_types = vec![
            FuncTy {
                params: vec![array(0)],
                returns: vec![Ty::Bool],
                abi: None,
                is_vararg: false,
            },
            FuncTy {
                params: vec![Ty::Bool],
                returns: vec![array(0)],
                abi: None,
                is_vararg: false,
            },
            FuncTy {
                params: Vec::new(),
                returns: Vec::new(),
                abi: None,
                is_vararg: false,
            },
        ];
        module.structs.push(structure(70, array(0)));
        module.enums.push(enumeration(90, array(0)));
        module.records.push(record(100, array(0)));
        module.closure_types = vec![
            ClosureTy::bare(FuncTyId::new(0)),
            ClosureTy {
                func: FuncTyId::new(2),
                captures: vec![array(0)],
            },
        ];
        let roots = vec![
            array(0),
            Ty::Set(TyId::new(0), SetRepr::Boxed),
            Ty::Sequence(TyId::new(0)),
            Ty::Refine(TyId::new(0), PredId::new(0)),
            Ty::FatPtr(FatPtrKind::Slice(TyId::new(0))),
            Ty::Func(FuncTyId::new(0)),
            Ty::Func(FuncTyId::new(1)),
            Ty::Struct(StructId::new(70)),
            Ty::Enum(EnumId::new(90)),
            Ty::Record(RecordId::new(100)),
            Ty::Closure(ClosureTyId::new(0)),
            Ty::Closure(ClosureTyId::new(1)),
            Ty::Vector(Box::new(array(0)), 4),
            Ty::Tuple(vec![Ty::Bool, array(0)]),
            Ty::Ref(Box::new(array(0))),
            Ty::RefMut(Box::new(array(0))),
            Ty::PtrConst(Box::new(array(0))),
            Ty::PtrMut(Box::new(array(0))),
            Ty::Rc(Box::new(array(0))),
        ];
        module.types.extend(roots.iter().cloned());
        let summary = module.dialect_type_reachability();
        for (index, root) in roots.iter().enumerate() {
            assert!(summary.contains(root), "direct root {root:?}");
            assert!(
                summary.contains(&array(index as u32 + 1)),
                "stored root {root:?}"
            );
        }
        assert!(!summary.contains(&Ty::Func(FuncTyId::new(2))));
    }

    #[test]
    fn sparse_out_of_order_ids_and_duplicate_definitions_do_not_hide_nominal_types() {
        let mut module = Module::new("sparse IDs");
        module.structs = vec![structure(u32::MAX, nominal()), structure(0, Ty::Bool)];
        module.enums = vec![enumeration(u32::MAX, nominal()), enumeration(0, Ty::Bool)];
        module.records = vec![record(u32::MAX, nominal()), record(0, Ty::Bool)];
        {
            let summary = module.dialect_type_reachability();
            for ty in [
                Ty::Struct(StructId::new(u32::MAX)),
                Ty::Enum(EnumId::new(u32::MAX)),
                Ty::Record(RecordId::new(u32::MAX)),
            ] {
                assert!(summary.contains(&ty));
            }
            for ty in [
                Ty::Struct(StructId::new(0)),
                Ty::Enum(EnumId::new(0)),
                Ty::Record(RecordId::new(0)),
            ] {
                assert!(!summary.contains(&ty));
            }
        }
        // A duplicate that appears later must still contribute its branch.
        module
            .structs
            .push(structure(0, Ty::Struct(StructId::new(u32::MAX))));
        module
            .enums
            .push(enumeration(0, Ty::Enum(EnumId::new(u32::MAX))));
        module
            .records
            .push(record(0, Ty::Record(RecordId::new(u32::MAX))));
        let summary = module.dialect_type_reachability();
        for ty in [
            Ty::Struct(StructId::new(0)),
            Ty::Enum(EnumId::new(0)),
            Ty::Record(RecordId::new(0)),
        ] {
            assert!(summary.contains(&ty));
        }
    }

    #[test]
    fn missing_ids_do_not_alias_another_table_or_claim_a_nominal_type() {
        let mut module = Module::new("missing IDs");
        module.func_types.push(FuncTy {
            params: vec![nominal()],
            returns: Vec::new(),
            abi: None,
            is_vararg: false,
        });
        let summary = module.dialect_type_reachability();
        for ty in [
            array(0),
            Ty::Func(FuncTyId::new(1)),
            Ty::Struct(StructId::new(0)),
            Ty::Enum(EnumId::new(0)),
            Ty::Record(RecordId::new(0)),
            Ty::Closure(ClosureTyId::new(0)),
            Ty::FatPtr(FatPtrKind::Str),
            Ty::FatPtr(FatPtrKind::ContainerLen),
            Ty::FatPtr(FatPtrKind::TraitObject { trait_id: 0 }),
            Ty::FatPtr(FatPtrKind::ContainerVtable),
        ] {
            assert!(!summary.contains(&ty), "{ty:?}");
        }
        assert!(summary.contains(&nominal()));
    }

    fn handle() -> Ty {
        Ty::handle("Nat", "trust_bignum::Nat")
    }

    #[test]
    fn the_two_nominal_axes_are_tracked_independently_through_tables_and_cycles() {
        let mut module = Module::new("two axes");
        // 0 <-> 1 reaches a HANDLE; 2 <-> 3 reaches a DIALECT; 4 reaches both
        // through the two back edges; 5 is nominal-free.
        module.types = vec![
            Ty::Tuple(vec![array(1), handle()]),
            array(0),
            Ty::Tuple(vec![array(3), nominal()]),
            array(2),
            Ty::Tuple(vec![array(0), array(2)]),
            Ty::Bool,
        ];
        let summary = module.nominal_type_reachability();
        for index in 0..2 {
            assert!(summary.contains_handle(&array(index)), "{index}");
            assert!(!summary.contains_dialect(&array(index)), "{index}");
        }
        for index in 2..4 {
            assert!(summary.contains_dialect(&array(index)), "{index}");
            assert!(!summary.contains_handle(&array(index)), "{index}");
        }
        assert!(summary.contains_handle(&array(4)));
        assert!(summary.contains_dialect(&array(4)));
        assert!(!summary.contains_handle(&array(5)));
        assert!(!summary.contains_dialect(&array(5)));
        assert!(summary.contains_handle(&handle()));
        assert!(!summary.contains_dialect(&handle()));
        // The dialect-only view answers only its own axis.
        let dialect_view = module.dialect_type_reachability();
        assert!(!dialect_view.contains(&array(0)));
        assert!(dialect_view.contains(&array(2)));
        // Instruction types: a handle-typed `Undef` is a handle occurrence.
        let inst = Inst::Undef { ty: array(0) };
        assert!(summary.contains_handle_instruction_types(&inst));
        assert!(!summary.contains_dialect_instruction_types(&inst));
    }

    #[test]
    fn handles_reach_through_every_named_edge_class() {
        let mut module = Module::new("handle edges");
        module.types.push(handle());
        module.func_types.push(FuncTy {
            params: vec![array(0)],
            returns: vec![Ty::Bool],
            abi: None,
            is_vararg: false,
        });
        module.structs.push(structure(1, array(0)));
        module.enums.push(enumeration(2, array(0)));
        module.records.push(record(3, array(0)));
        module.closure_types.push(ClosureTy::bare(FuncTyId::new(0)));
        let summary = module.nominal_type_reachability();
        for ty in [
            Ty::Func(FuncTyId::new(0)),
            Ty::Struct(StructId::new(1)),
            Ty::Enum(EnumId::new(2)),
            Ty::Record(RecordId::new(3)),
            Ty::Closure(ClosureTyId::new(0)),
            Ty::Ref(Box::new(array(0))),
            Ty::FatPtr(FatPtrKind::Slice(TyId::new(0))),
        ] {
            assert!(summary.contains_handle(&ty), "{ty:?}");
            assert!(!summary.contains_dialect(&ty), "{ty:?}");
        }
    }

    /// The targeted walk and the whole-module summary must answer the SAME
    /// question. They are two implementations of one predicate — the summary
    /// for callers that ask a module about many types, the walk for callers
    /// that ask about a few inside a per-node loop — and a divergence is a
    /// live fail-open, because `shape::layout_sensitive_cast_evidence` refuses
    /// a handle cast on the walk while `validate_module`'s transport rule
    /// refuses it on the summary.
    #[test]
    fn the_targeted_handle_walk_agrees_with_the_whole_module_summary() {
        let mut module = Module::new("walk vs summary");
        // Handle behind `ty.0`; dialect behind `ty.1`; `ty.2` is a cycle with
        // no nominal type at all; `ty.3` reaches the handle one hop further.
        module.types = vec![handle(), nominal(), array(2), array(0)];
        module.func_types.push(FuncTy {
            params: vec![array(0)],
            returns: vec![Ty::Bool],
            abi: None,
            is_vararg: false,
        });
        module.func_types.push(FuncTy {
            params: vec![Ty::Bool],
            returns: vec![array(1)],
            abi: None,
            is_vararg: false,
        });
        module.structs.push(structure(1, array(3)));
        module
            .enums
            .push(enumeration(2, Ty::Struct(StructId::new(1))));
        module.records.push(record(3, array(1)));
        // Captures reach the handle; the SIGNATURE reaches only the dialect.
        module.closure_types.push(ClosureTy {
            func: FuncTyId::new(1),
            captures: vec![array(0)],
        });
        // Nothing but the signature reaches anything: the closure's handle
        // answer must come through its `FuncTyId` edge alone.
        module.closure_types.push(ClosureTy::bare(FuncTyId::new(0)));

        let roots = [
            handle(),
            nominal(),
            Ty::Bool,
            array(0),
            array(1),
            array(2),
            array(3),
            Ty::Set(TyId::new(0), SetRepr::Boxed),
            Ty::Sequence(TyId::new(3)),
            Ty::Refine(TyId::new(0), PredId::new(0)),
            Ty::FatPtr(FatPtrKind::Slice(TyId::new(3))),
            Ty::FatPtr(FatPtrKind::Str),
            Ty::Func(FuncTyId::new(0)),
            Ty::Func(FuncTyId::new(1)),
            Ty::Func(FuncTyId::new(9)),
            Ty::Struct(StructId::new(1)),
            Ty::Struct(StructId::new(9)),
            Ty::Enum(EnumId::new(2)),
            Ty::Record(RecordId::new(3)),
            Ty::Closure(ClosureTyId::new(0)),
            Ty::Closure(ClosureTyId::new(1)),
            Ty::Closure(ClosureTyId::new(9)),
            Ty::Vector(Box::new(array(0)), 4),
            Ty::Tuple(vec![Ty::Bool, array(3)]),
            Ty::Tuple(vec![Ty::Bool, array(1)]),
            Ty::Ref(Box::new(Ty::Struct(StructId::new(1)))),
            Ty::Rc(Box::new(array(2))),
            Ty::Ptr,
        ];
        let summary = module.nominal_type_reachability();
        let mut reaching = 0;
        for root in &roots {
            let expected = summary.contains_handle(root);
            assert_eq!(
                module.type_reaches_handle(root),
                expected,
                "walk and summary disagree on {root:?}"
            );
            reaching += usize::from(expected);
        }
        // The test is only meaningful if both answers actually vary.
        assert!(reaching > 0 && reaching < roots.len(), "{reaching}");
        // Spelled out, because each is a distinct edge the walk resolves by
        // hand: closure 1 reaches the handle ONLY through its `FuncTyId`
        // signature, closure 0 only through its captures, and `ty.2` is a pure
        // cycle that must terminate answering `false`.
        assert!(module.type_reaches_handle(&Ty::Closure(ClosureTyId::new(1))));
        assert!(module.type_reaches_handle(&Ty::Closure(ClosureTyId::new(0))));
        assert!(!module.type_reaches_handle(&array(2)));

        // Duplicate named ids contribute ALL matching definitions, as the
        // summary does: a second `struct 1` appended after the handle-free
        // first one must not hide its branch.
        let mut duplicated = Module::new("duplicate ids");
        duplicated.types.push(handle());
        duplicated.structs.push(structure(1, Ty::Bool));
        duplicated.structs.push(structure(1, array(0)));
        let root = Ty::Struct(StructId::new(1));
        assert!(
            duplicated
                .nominal_type_reachability()
                .contains_handle(&root)
        );
        assert!(duplicated.type_reaches_handle(&root));
    }

    fn trait_object(id: u32) -> Ty {
        Ty::FatPtr(FatPtrKind::TraitObject { trait_id: id })
    }

    fn signature(params: Vec<Ty>) -> FuncTy {
        FuncTy {
            abi: None,
            params,
            returns: Vec::new(),
            is_vararg: false,
        }
    }

    /// The callable axis is a third independent bitset: a function pointer,
    /// closure or vtable word behind any named table reaches it, and neither
    /// it nor an untyped pointer marks the dialect or handle axes.
    #[test]
    fn the_callable_axis_reaches_through_tables_independently_of_the_other_axes() {
        let mut module = Module::new("callable axis");
        module.func_types = vec![signature(vec![handle()]), signature(Vec::new())];
        module.types = vec![
            Ty::Func(FuncTyId::new(1)),
            Ty::Tuple(vec![Ty::U8, Ty::Ptr]),
            trait_object(7),
            Ty::FatPtr(FatPtrKind::ContainerVtable),
        ];
        module.structs.push(structure(1, array(0)));
        module.enums.push(enumeration(2, array(2)));
        module.records.push(record(3, array(3)));
        module.closure_types.push(ClosureTy::bare(FuncTyId::new(1)));
        module.closure_types.push(ClosureTy {
            func: FuncTyId::new(1),
            captures: vec![Ty::Struct(StructId::new(1))],
        });
        let summary = module.nominal_type_reachability();
        for ty in [
            Ty::Func(FuncTyId::new(0)),
            Ty::Struct(StructId::new(1)),
            Ty::Enum(EnumId::new(2)),
            Ty::Record(RecordId::new(3)),
            Ty::Closure(ClosureTyId::new(0)),
            Ty::Ref(Box::new(array(0))),
            trait_object(9),
        ] {
            assert!(summary.contains_callable(&ty), "{ty:?}");
            assert!(!summary.contains_dialect(&ty), "{ty:?}");
        }
        // An untyped pointer names no callable: counting it would make every
        // pointer cast a LAUNDER.
        assert!(!summary.contains_callable(&array(1)));
        assert!(!summary.contains_callable(&Ty::Ptr));
        // The FIRST signature mentions a handle, so a pointer of it reaches
        // the handle axis through its table edge as before.
        assert!(summary.contains_handle(&Ty::Func(FuncTyId::new(0))));
        assert!(!summary.contains_handle(&Ty::Func(FuncTyId::new(1))));
    }

    /// The rule H operand walk agrees with the summary on typed callables,
    /// reports what the bitset cannot (untyped pointers, missing entries and
    /// opaque types fail closed as `opaque`), carries closure captures, and
    /// does not mistake a signature's parameter types for carried values.
    #[test]
    fn the_carrier_walk_agrees_with_the_summary_and_fails_closed_on_opaque_types() {
        let mut module = Module::new("carriers");
        module.func_types = vec![signature(vec![Ty::Ptr]), signature(Vec::new())];
        module.types = vec![
            Ty::Tuple(vec![Ty::Func(FuncTyId::new(0)), trait_object(4)]),
            Ty::Ptr,
            array(0),
        ];
        module.structs.push(structure(1, array(2)));
        module.closure_types.push(ClosureTy {
            func: FuncTyId::new(1),
            captures: vec![trait_object(5), Ty::Ptr],
        });
        let summary = module.nominal_type_reachability();
        let roots = [
            Ty::Bool,
            Ty::Ptr,
            array(0),
            array(1),
            array(2),
            Ty::Struct(StructId::new(1)),
            Ty::Struct(StructId::new(99)),
            Ty::Func(FuncTyId::new(0)),
            Ty::Closure(ClosureTyId::new(0)),
            Ty::FatPtr(FatPtrKind::ContainerVtable),
            Ty::FatPtr(FatPtrKind::Str),
            nominal(),
            handle(),
            Ty::Error,
        ];
        for root in &roots {
            assert_eq!(
                module.callable_carriers(root).carries_typed_callable(),
                summary.contains_callable(root),
                "walk and summary disagree on {root:?}"
            );
        }
        let through_struct = module.callable_carriers(&Ty::Struct(StructId::new(1)));
        assert_eq!(
            through_struct.fn_types,
            std::collections::BTreeSet::from([FuncTyId::new(0)])
        );
        assert_eq!(
            through_struct.principals,
            std::collections::BTreeSet::from([4])
        );
        // `fn(*const u8)`'s parameter is a signature type, not a carried value.
        assert!(!through_struct.opaque);
        let closure = module.callable_carriers(&Ty::Closure(ClosureTyId::new(0)));
        assert_eq!(
            closure.closures,
            std::collections::BTreeSet::from([ClosureTyId::new(0)])
        );
        assert_eq!(closure.principals, std::collections::BTreeSet::from([5]));
        assert!(
            closure.opaque,
            "a captured untyped pointer may lead anywhere"
        );
        for opaque in [
            Ty::Ptr,
            array(1),
            Ty::Struct(StructId::new(99)),
            nominal(),
            Ty::Error,
        ] {
            assert!(module.callable_carriers(&opaque).opaque, "{opaque:?}");
        }
        assert!(
            module
                .callable_carriers(&Ty::FatPtr(FatPtrKind::ContainerVtable))
                .erased_dyn
        );
        assert!(module.callable_carriers(&Ty::Bool).is_empty());
        assert!(module.callable_carriers(&handle()).is_empty());
    }

    #[test]
    fn deeply_nested_instruction_types_visit_inline_spelling_once() {
        let mut module = Module::new("inline depth");
        module.types.push(nominal());
        let summary = module.dialect_type_reachability();
        let mut ty = array(0);
        for _ in 0..100_000 {
            ty = Ty::Ref(Box::new(ty));
        }
        assert!(summary.contains(&ty));
        let inst = Inst::Undef { ty };
        assert!(summary.contains_instruction_types(&inst));
        assert!(!summary.contains_instruction_types(&Inst::Undef { ty: Ty::Bool }));
        // Avoid the unrelated recursive derived destructor on this input.
        if let Inst::Undef { mut ty } = inst {
            while let Ty::Ref(inner) = ty {
                ty = *inner;
            }
        }
    }
}

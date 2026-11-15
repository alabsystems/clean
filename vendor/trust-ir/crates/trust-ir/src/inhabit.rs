// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Inhabitedness as a least fixpoint, decided once per nominal node.
//!
//! [`crate::Module::ty_is_uninhabited`] is a SOUND claim: `true` grants an
//! exemption (an uninhabited enum variant needs no niche encoding), so it is
//! `true` only when a finite derivation says the type has no value:
//!
//! * `Ty::Never` is uninhabited;
//! * a tuple, a struct DEFINITION or a record DEFINITION is uninhabited when
//!   one of its fields is;
//! * an enum DEFINITION is uninhabited when every variant is, and a variant
//!   is when one of its fields is (so a zero-variant enum is);
//! * a nominal id is uninhabited when it has a definition and EVERY
//!   definition with the id is (a duplicate id is a validation error, but an
//!   unvalidated module can carry one);
//! * `[T; n]` with `n > 0`, and `Refine(T, p)`, are uninhabited when the
//!   type-table entry `T` is (a missing entry is not);
//! * nothing else is: pointers and references to `!` included, a closure, an
//!   unresolvable id.
//!
//! Read as equations over the nominal nodes (a type-table entry, a struct id,
//! a record id, an enum id), these are monotone and-or equations, and the
//! predicate is their LEAST solution: a node is uninhabited exactly when the
//! rules derive it from `Never` in finitely many steps. A by-value cycle
//! derives nothing by itself, so `struct S { s: S }` is inhabited (the
//! conservative answer; the validator refuses the cycle separately).
//!
//! # How it is computed
//!
//! A query collects the nodes its type reaches that no earlier query decided
//! (an explicit stack, no recursion), writes each node's equation as a
//! conjunction of clauses — one per definition, or per variant of each enum
//! definition — each clause a disjunction of nodes, and solves them by
//! propagation: a node with no unsatisfied clause is uninhabited, and that
//! satisfies every clause that names it. Every node the propagation does not
//! reach is inhabited. That is the least solution, in time linear in the
//! clauses written, and the verdicts are kept: a node's least solution
//! depends only on what it reaches, so it is the same for every later query.
//! A [`InhabitMemo`] therefore decides each node once over its lifetime, and
//! the all-definitions index it needs is built once per kind, on first use.
//!
//! # Against the recursion it replaced
//!
//! The predicate used to be a depth-first recursion that answered
//! "inhabited" on re-entering a node of its own path and memoized every
//! verdict for the rest of the query. Where the reach of a question has no
//! cycle, that recursion computed this least solution exactly (its walk never
//! re-entered a node, and an acyclic system has one solution). Where the
//! reach has a cycle, its verdicts depended on the order it met the cycle: a
//! node first decided while its own derivation was on the path was memoized
//! "inhabited" although it is not, so `enum E { A(G), B(Y) }` could be
//! inhabited while both of its variants, asked one at a time, were not. The
//! least solution is never below that recursion's answer and is
//! order-independent. The validator refuses every by-value cycle
//! (`InlineAggregateCycle`) and every duplicate struct and enum id, so on the
//! modules it admits the reach of every question is acyclic, except through
//! a duplicate RECORD id (which it does not refuse) — and there the new
//! verdict is the derivable one.

use std::collections::HashMap;

use crate::Module;
use crate::ty::{EnumDef, EnumVariant, RecordDef, StructDef, Ty};
use crate::value::{EnumId, RecordId, StructId};

/// Cached structural inhabitedness over one immutable set of borrowed tables.
///
/// This uses the same least-fixpoint rules as [`Module::ty_is_uninhabited`].
/// A `true` result is a finite structural derivation of uninhabitedness;
/// unresolved types and cycles without such a derivation answer `false`.
/// It does not validate the tables or establish a physical layout.
///
/// Consumers that already borrow definition tables can query them without
/// cloning a module. The table borrows are fixed for the lifetime of this
/// query, so cached verdicts cannot be reused with different definitions.
/// This is an ordinary query; observed operations use their observed solver.
pub struct Inhabitedness<'a> {
    definitions: DefinitionTables<'a>,
    memo: InhabitMemo,
}

impl<'a> Inhabitedness<'a> {
    /// Bind a query to the exact type, struct, record and enum tables.
    pub fn new(
        types: &'a [Ty],
        structs: &'a [StructDef],
        records: &'a [RecordDef],
        enums: &'a [EnumDef],
    ) -> Self {
        Self {
            definitions: DefinitionTables {
                types,
                structs,
                records,
                enums,
            },
            memo: InhabitMemo::default(),
        }
    }

    /// Bind a query to a module's immutable definition tables.
    pub fn for_module(module: &'a Module) -> Self {
        Self {
            definitions: DefinitionTables::from(module),
            memo: InhabitMemo::default(),
        }
    }

    /// Is this type structurally uninhabited? Each reached node is decided once.
    pub fn ty_is_uninhabited(&mut self, ty: &Ty) -> bool {
        self.memo
            .some_uninhabited(self.definitions, std::slice::from_ref(ty))
    }

    /// Is at least one field of this variant structurally uninhabited?
    pub fn variant_is_uninhabited(&mut self, variant: &EnumVariant) -> bool {
        self.memo
            .some_uninhabited(self.definitions, &variant.fields)
    }
}

#[derive(Clone, Copy)]
struct DefinitionTables<'a> {
    types: &'a [Ty],
    structs: &'a [StructDef],
    records: &'a [RecordDef],
    enums: &'a [EnumDef],
}

impl<'a> From<&'a Module> for DefinitionTables<'a> {
    fn from(module: &'a Module) -> Self {
        Self {
            types: &module.types,
            structs: &module.structs,
            records: &module.records,
            enums: &module.enums,
        }
    }
}

/// A node of the inhabitedness equations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Node {
    /// A type-table entry, reached by value through `Array` or `Refine`.
    Entry(usize),
    Struct(StructId),
    Record(RecordId),
    Enum(EnumId),
}

/// Every definition of each id, in table order. Also the index of the
/// by-value and nominal reachability memo (`crate::reach`) and of the rule H
/// carrier walk, whose walks follow every definition of an id too.
///
/// Built in one pass over the table. When every row's id is its position
/// (the form a builder writes), row `i` is the one definition of id `i`, so
/// that pass of comparisons IS the index: no hash index is built, and a
/// one-shot question costs what the per-id list scan it replaced cost for one
/// id. Any other table (an id out of place, a duplicate, an id past the
/// table) gets chains: each id's first row, and per row the next row with the
/// same id.
pub(crate) struct AllDefs {
    /// `None` for a positional table.
    chains: Option<Chains>,
    len: usize,
}

struct Chains {
    head: HashMap<u32, usize>,
    next: Vec<usize>,
}

/// The end of an [`AllDefs`] chain.
pub(crate) const END: usize = usize::MAX;

impl AllDefs {
    /// The index of a table of `len` rows whose row `at` has id `id_at(at)`.
    pub(crate) fn build(len: usize, id_at: impl Fn(usize) -> u32) -> Self {
        let positional = (0..len).all(|at| usize::try_from(id_at(at)).is_ok_and(|id| id == at));
        if positional {
            return AllDefs { chains: None, len };
        }
        let mut head = HashMap::with_capacity(len);
        let mut next = vec![END; len];
        // Backwards, so each id's chain runs in table order from its head.
        for at in (0..len).rev() {
            if let Some(later) = head.insert(id_at(at), at) {
                next[at] = later;
            }
        }
        AllDefs {
            chains: Some(Chains { head, next }),
            len,
        }
    }

    /// The first row with `id`, or [`END`].
    pub(crate) fn first(&self, id: u32) -> usize {
        match &self.chains {
            None => usize::try_from(id)
                .ok()
                .filter(|&at| at < self.len)
                .unwrap_or(END),
            Some(chains) => chains.head.get(&id).copied().unwrap_or(END),
        }
    }

    /// The next row after `at` with row `at`'s id, or [`END`].
    pub(crate) fn next(&self, at: usize) -> usize {
        match &self.chains {
            None => END,
            Some(chains) => chains.next[at],
        }
    }

    /// Whether the table is positional (no hash index was built).
    #[cfg(test)]
    pub(crate) fn is_positional(&self) -> bool {
        self.chains.is_none()
    }
}

/// The inhabitedness verdicts decided so far over one module.
///
/// The memo holds no borrow of the module; every query passes it, and a memo
/// must only ever be asked about the module (unchanged) it was first asked
/// about.
#[derive(Default)]
pub(crate) struct InhabitMemo {
    structs: Option<AllDefs>,
    records: Option<AllDefs>,
    enums: Option<AllDefs>,
    decided: HashMap<Node, bool>,
    /// Definition rows the all-definitions indexes have read (each at most
    /// once per memo).
    pub(crate) rows_indexed: usize,
    /// Nodes expanded, clauses written, literals read and propagations
    /// made: O(the clauses of the decided nodes) over the memo's lifetime.
    pub(crate) steps: u64,
}

impl core::fmt::Debug for InhabitMemo {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("InhabitMemo")
            .field("decided", &self.decided.len())
            .field("rows_indexed", &self.rows_indexed)
            .field("steps", &self.steps)
            .finish()
    }
}

/// The clause-and-propagation state of one solve: the nodes a query reached
/// that were not decided yet.
#[derive(Default)]
struct Solve {
    local: HashMap<Node, usize>,
    nodes: Vec<Node>,
    /// Per node: its clauses not yet satisfied.
    open_clauses: Vec<usize>,
    /// Per node: the clauses that name it.
    watchers: Vec<Vec<usize>>,
    /// Per clause: its node, and whether it is satisfied.
    owner: Vec<usize>,
    satisfied: Vec<bool>,
    /// Nodes whose clauses are not written yet.
    unexpanded: Vec<usize>,
}

impl Solve {
    fn intern(&mut self, node: Node) -> usize {
        *self.local.entry(node).or_insert_with(|| {
            let index = self.nodes.len();
            self.nodes.push(node);
            self.open_clauses.push(0);
            self.watchers.push(Vec::new());
            self.unexpanded.push(index);
            index
        })
    }
}

impl InhabitMemo {
    /// Number of nodes decided.
    pub(crate) fn decided(&self) -> usize {
        self.decided.len()
    }

    /// Is `ty` uninhabited (see the module docs)?
    pub(crate) fn ty_is_uninhabited(&mut self, module: &Module, ty: &Ty) -> bool {
        self.some_uninhabited(module.into(), std::slice::from_ref(ty))
    }

    /// Is `variant` uninhabited: is one of its fields?
    pub(crate) fn variant_is_uninhabited(
        &mut self,
        module: &Module,
        variant: &EnumVariant,
    ) -> bool {
        self.some_uninhabited(module.into(), &variant.fields)
    }

    /// The first INHABITED variant of `def` that a niche encoding leaves
    /// without an encoding — neither `untagged_variant` nor inside
    /// `niche_variants_start..=niche_variants_end` — or `None`.
    pub(crate) fn niche_unencoded_inhabited_variant(
        &mut self,
        module: &Module,
        def: &EnumDef,
        untagged_variant: u32,
        niche_variants_start: u32,
        niche_variants_end: u32,
    ) -> Option<usize> {
        def.variants
            .iter()
            .enumerate()
            .find(|(index, variant)| {
                let encoded = u32::try_from(*index).is_ok_and(|index| {
                    index == untagged_variant
                        || (niche_variants_start..=niche_variants_end).contains(&index)
                });
                !encoded && !self.variant_is_uninhabited(module, variant)
            })
            .map(|(index, _)| index)
    }

    /// Is one of `tys` uninhabited? Decides every node they reach first.
    fn some_uninhabited(&mut self, module: DefinitionTables<'_>, tys: &[Ty]) -> bool {
        let mut literals = Vec::new();
        if self.literals(module, tys.iter(), &mut literals) {
            return true;
        }
        let mut undecided = Vec::new();
        for node in literals {
            match self.decided.get(&node) {
                Some(true) => return true,
                Some(false) => {}
                None => undecided.push(node),
            }
        }
        if undecided.is_empty() {
            return false;
        }
        self.solve(module, &undecided);
        undecided.iter().any(|node| self.decided[node])
    }

    /// The nodes of the disjunction "one of `tys` is uninhabited", into
    /// `out`; `true` when the disjunction holds outright (a `Never`).
    fn literals<'t>(
        &mut self,
        module: DefinitionTables<'_>,
        tys: impl Iterator<Item = &'t Ty>,
        out: &mut Vec<Node>,
    ) -> bool {
        let mut pending: Vec<&Ty> = tys.collect();
        // Inline types nest without identity: walk them on a heap stack.
        while let Some(ty) = pending.pop() {
            self.steps += 1;
            match ty {
                Ty::Never => return true,
                Ty::Tuple(elems) => pending.extend(elems.iter()),
                Ty::Array(elem, len) => {
                    if *len > 0 && module.types.get(elem.as_usize()).is_some() {
                        out.push(Node::Entry(elem.as_usize()));
                    }
                }
                Ty::Refine(base, _) => {
                    if module.types.get(base.as_usize()).is_some() {
                        out.push(Node::Entry(base.as_usize()));
                    }
                }
                Ty::Struct(id) => out.push(Node::Struct(*id)),
                Ty::Record(id) => out.push(Node::Record(*id)),
                Ty::Enum(id) => out.push(Node::Enum(*id)),
                _ => {}
            }
        }
        false
    }

    /// Decide every node `roots` reach that is not decided: write their
    /// clauses, then propagate (see the module docs).
    fn solve(&mut self, module: DefinitionTables<'_>, roots: &[Node]) {
        let mut solve = Solve::default();
        for &root in roots {
            solve.intern(root);
        }
        let mut uninhabited: Vec<usize> = Vec::new();
        let mut literals: Vec<Node> = Vec::new();
        while let Some(index) = solve.unexpanded.pop() {
            self.steps += 1;
            let node = solve.nodes[index];
            match node {
                Node::Entry(entry) => {
                    let ty = &module.types[entry];
                    self.clause(
                        module,
                        &mut solve,
                        index,
                        std::iter::once(ty),
                        &mut literals,
                    );
                }
                Node::Struct(id) => {
                    let defs = self.structs.get_or_insert_with(|| {
                        self.rows_indexed += module.structs.len();
                        AllDefs::build(module.structs.len(), |at| module.structs[at].id.index())
                    });
                    let mut at = defs.first(id.index());
                    if at == END {
                        self.clause(module, &mut solve, index, std::iter::empty(), &mut literals);
                    }
                    while at != END {
                        let fields = module.structs[at].fields.iter().map(|field| &field.ty);
                        self.clause(module, &mut solve, index, fields, &mut literals);
                        at = self.structs.as_ref().map_or(END, |defs| defs.next(at));
                    }
                }
                Node::Record(id) => {
                    let defs = self.records.get_or_insert_with(|| {
                        self.rows_indexed += module.records.len();
                        AllDefs::build(module.records.len(), |at| module.records[at].id.index())
                    });
                    let mut at = defs.first(id.index());
                    if at == END {
                        self.clause(module, &mut solve, index, std::iter::empty(), &mut literals);
                    }
                    while at != END {
                        let fields = module.records[at].fields.iter().map(|field| &field.ty);
                        self.clause(module, &mut solve, index, fields, &mut literals);
                        at = self.records.as_ref().map_or(END, |defs| defs.next(at));
                    }
                }
                Node::Enum(id) => {
                    let defs = self.enums.get_or_insert_with(|| {
                        self.rows_indexed += module.enums.len();
                        AllDefs::build(module.enums.len(), |at| module.enums[at].id.index())
                    });
                    let mut at = defs.first(id.index());
                    if at == END {
                        self.clause(module, &mut solve, index, std::iter::empty(), &mut literals);
                    }
                    while at != END {
                        for variant in &module.enums[at].variants {
                            self.clause(
                                module,
                                &mut solve,
                                index,
                                variant.fields.iter(),
                                &mut literals,
                            );
                        }
                        at = self.enums.as_ref().map_or(END, |defs| defs.next(at));
                    }
                }
            }
            if solve.open_clauses[index] == 0 {
                uninhabited.push(index);
            }
        }
        let mut verdict = vec![false; solve.nodes.len()];
        for &index in &uninhabited {
            verdict[index] = true;
        }
        while let Some(index) = uninhabited.pop() {
            for &clause in &solve.watchers[index] {
                self.steps += 1;
                if solve.satisfied[clause] {
                    continue;
                }
                solve.satisfied[clause] = true;
                let owner = solve.owner[clause];
                solve.open_clauses[owner] -= 1;
                if solve.open_clauses[owner] == 0 {
                    verdict[owner] = true;
                    uninhabited.push(owner);
                }
            }
        }
        for (node, verdict) in solve.nodes.into_iter().zip(verdict) {
            self.decided.insert(node, verdict);
        }
    }

    /// Write the clause "one of `tys` is uninhabited" of node `owner`: drop
    /// it if it already holds, else count it open and watch its undecided
    /// nodes (a clause with none stays open: the node is inhabited).
    fn clause<'t>(
        &mut self,
        module: DefinitionTables<'_>,
        solve: &mut Solve,
        owner: usize,
        tys: impl Iterator<Item = &'t Ty>,
        literals: &mut Vec<Node>,
    ) {
        self.steps += 1;
        literals.clear();
        if self.literals(module, tys, literals) {
            return;
        }
        if literals
            .iter()
            .any(|node| self.decided.get(node) == Some(&true))
        {
            return;
        }
        let clause = solve.owner.len();
        solve.owner.push(owner);
        solve.satisfied.push(false);
        solve.open_clauses[owner] += 1;
        for &node in literals.iter() {
            if self.decided.contains_key(&node) {
                continue;
            }
            let watched = solve.intern(node);
            solve.watchers[watched].push(clause);
        }
    }
}

#[cfg(test)]
mod borrowed_tests {
    use super::*;
    use crate::{FieldDef, PredId, StructRepr, TyId};

    fn field(ty: Ty) -> FieldDef {
        FieldDef {
            name: "field".into(),
            ty,
            offset: None,
        }
    }

    fn structure(id: u32, fields: Vec<Ty>) -> StructDef {
        StructDef {
            id: StructId::new(id),
            name: format!("S{id}"),
            fields: fields.into_iter().map(field).collect(),
            size: None,
            align: None,
            repr: StructRepr::Rust,
            origin: None,
        }
    }

    fn variant(fields: Vec<Ty>) -> EnumVariant {
        EnumVariant {
            name: "variant".into(),
            fields,
            field_names: vec![],
        }
    }

    #[test]
    fn borrowed_tables_follow_all_definition_kinds_without_copying_or_recomputing() {
        let types = [Ty::Record(RecordId::new(6))];
        let structs = [structure(5, vec![Ty::Enum(EnumId::new(4))])];
        let records = [RecordDef {
            id: RecordId::new(6),
            name: "R".into(),
            fields: vec![field(Ty::Struct(StructId::new(5)))],
        }];
        let enums = [EnumDef::new(EnumId::new(4), "Empty", vec![])];
        let mut query = Inhabitedness::new(&types, &structs, &records, &enums);
        assert!(core::ptr::eq(query.definitions.types, types.as_slice()));
        assert!(core::ptr::eq(query.definitions.structs, structs.as_slice()));
        assert!(core::ptr::eq(query.definitions.records, records.as_slice()));
        assert!(core::ptr::eq(query.definitions.enums, enums.as_slice()));
        let array = Ty::Array(TyId::new(0), 1);
        assert!(query.ty_is_uninhabited(&array));
        let work = (
            query.memo.decided(),
            query.memo.rows_indexed,
            query.memo.steps,
        );
        for _ in 0..100 {
            assert!(query.variant_is_uninhabited(&variant(vec![array.clone()])));
        }
        assert_eq!(query.memo.decided(), work.0);
        assert_eq!(query.memo.rows_indexed, work.1);
        // One root literal per repeat; the reached graph is never expanded again.
        assert_eq!(query.memo.steps, work.2 + 100);
        assert!(query.ty_is_uninhabited(&Ty::Refine(TyId::new(0), PredId::new(0))));
        assert!(!query.ty_is_uninhabited(&Ty::Array(TyId::new(0), 0)));
        assert!(!query.ty_is_uninhabited(&Ty::Array(TyId::new(99), 1)));
        assert!(!query.ty_is_uninhabited(&Ty::Ref(Box::new(Ty::Never))));
    }

    #[test]
    fn borrowed_cycles_need_a_finite_derivation_and_query_order_does_not_change_answers() {
        let structs = [
            structure(0, vec![Ty::Struct(StructId::new(0))]),
            structure(1, vec![Ty::Struct(StructId::new(1)), Ty::Never]),
        ];
        for order in [[0, 1], [1, 0]] {
            let mut query = Inhabitedness::new(&[], &structs, &[], &[]);
            for id in order {
                assert_eq!(
                    query.ty_is_uninhabited(&Ty::Struct(StructId::new(id))),
                    id == 1
                );
            }
            assert!(!query.ty_is_uninhabited(&Ty::Struct(StructId::new(2))));
        }
    }

    #[test]
    fn borrowed_duplicate_ids_require_every_definition_to_be_uninhabited() {
        for fields in [vec![Ty::Unit], vec![Ty::Never]] {
            let expected = fields == [Ty::Never];
            let mut enums = [
                EnumDef::new(EnumId::new(3), "Empty", vec![]),
                EnumDef::new(EnumId::new(3), "Other", vec![variant(fields)]),
            ];
            for _ in 0..2 {
                let mut query = Inhabitedness::new(&[], &[], &[], &enums);
                assert_eq!(query.ty_is_uninhabited(&Ty::Enum(EnumId::new(3))), expected);
                enums.reverse();
            }
        }
    }

    #[test]
    fn separate_queries_keep_conflicting_tables_and_module_queries_independent() {
        let empty = [EnumDef::new(EnumId::new(0), "Empty", vec![])];
        let inhabited = [EnumDef::new(EnumId::new(0), "Unit", vec![variant(vec![])])];
        let mut a = Inhabitedness::new(&[], &[], &[], &empty);
        let mut b = Inhabitedness::new(&[], &[], &[], &inhabited);
        let ty = Ty::Enum(EnumId::new(0));
        assert!(a.ty_is_uninhabited(&ty));
        assert!(!b.ty_is_uninhabited(&ty));
        assert!(a.ty_is_uninhabited(&ty));
        let mut module = Module::new("borrowed_inhabitedness");
        module.enums.extend(inhabited);
        assert!(!Inhabitedness::for_module(&module).ty_is_uninhabited(&ty));
        assert!(!module.ty_is_uninhabited(&ty));
    }
}

#[cfg(test)]
mod all_defs_tests {
    use super::{AllDefs, END};

    /// Every row of `ids` with `id`, in table order, by brute force.
    fn rows_with(ids: &[u32], id: u32) -> Vec<usize> {
        (0..ids.len()).filter(|&at| ids[at] == id).collect()
    }

    fn chain(defs: &AllDefs, id: u32) -> Vec<usize> {
        let mut rows = Vec::new();
        let mut at = defs.first(id);
        while at != END {
            rows.push(at);
            at = defs.next(at);
        }
        rows
    }

    fn check(ids: &[u32]) -> AllDefs {
        let defs = AllDefs::build(ids.len(), |at| ids[at]);
        let mut asked: Vec<u32> = ids.to_vec();
        asked.extend([ids.len() as u32, ids.len() as u32 + 1, u32::MAX, 0]);
        for id in asked {
            assert_eq!(chain(&defs, id), rows_with(ids, id), "{ids:?}: {id}");
        }
        defs
    }

    #[test]
    fn a_table_whose_ids_are_their_positions_builds_no_hash_index() {
        for len in [0, 1, 2, 1000] {
            let ids: Vec<u32> = (0..len).collect();
            assert!(check(&ids).is_positional(), "{len}");
        }
    }

    #[test]
    fn any_other_table_chains_every_definition_of_an_id_in_table_order() {
        let tables: [&[u32]; 7] = [
            &[1, 0],
            &[0, 0],
            &[0, 1, 1, 3],
            &[5],
            &[u32::MAX],
            &[0, 1, 2, 0, 1, 2, 0],
            &[2, 2, 2],
        ];
        for ids in tables {
            assert!(!check(ids).is_positional(), "{ids:?}");
        }
        // Random tables, most of them one swap or duplicate off positional.
        let mut state = 0x9e37_79b9_7f4a_7c15u64;
        let mut below = |n: u64| {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state % n.max(1)
        };
        for _ in 0..2000 {
            let len = below(12) as u32;
            let mut ids: Vec<u32> = (0..len).collect();
            for _ in 0..below(3) {
                if len > 0 {
                    let at = below(u64::from(len)) as usize;
                    ids[at] = below(u64::from(len) + 2) as u32;
                }
            }
            let positional = ids.iter().enumerate().all(|(at, id)| *id as usize == at);
            assert_eq!(check(&ids).is_positional(), positional, "{ids:?}");
        }
    }
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! [`MinimalEnv`] — the in-memory [`Env`] used by tests and as the M0–M2
//! placeholder host environment. Extracted from `validate.rs` to keep both
//! files under the 500-line convention. It implements both [`Env`] (read) and
//! [`crate::inductive::MutableEnv`] (the single admission write path); there is
//! no `_unchecked` admission method (design §4.3).

use crate::name::Name;
use crate::term::Term;
use crate::validate::{
    ConstDef, ConstructorArity, Env, QuotKind, RecursorShape, StructureInfo, Transparency,
};

/// A minimal in-memory [`Env`] for tests and the M0/M1 placeholder. Maps a name
/// to its level-param count, declared type, optional definition, and (for
/// inductives) the large-elim flag; recognizes the four `Quot` built-ins and
/// recursor names.
#[derive(Debug, Default, Clone)]
pub struct MinimalEnv {
    consts: std::collections::HashMap<Name, u32>,
    types: std::collections::HashMap<Name, Term>,
    defs: std::collections::HashMap<Name, ConstDef>,
    inductives: std::collections::HashMap<Name, bool>,
    quots: std::collections::HashMap<Name, QuotKind>,
    recursors: std::collections::HashSet<Name>,
    ctors: std::collections::HashMap<Name, ConstructorArity>,
    structs: std::collections::HashMap<Name, StructureInfo>,
    /// M2: full admitted-inductive records (decl + large_elim + derived rec),
    /// keyed by inductive name. Backs the structural-identity idempotency check
    /// and the recursor-type / ι-rule lookups.
    admitted_inductives: std::collections::HashMap<Name, crate::inductive::AdmittedInductive>,
    /// M2: maps `I.rec` (and recursor names) back to their inductive `I`, so
    /// `recursor_type`/`recursor_rules` can be looked up by either the inductive
    /// or the recursor name.
    rec_name_to_ind: std::collections::HashMap<Name, Name>,
    /// M3: maps an inductive name to its leading-parameter count (for the
    /// nested→mutual auxiliary construction's container peeling).
    ind_num_params: std::collections::HashMap<Name, u32>,
    /// M3: maps an inductive name to its constructors `(name, type)` in order
    /// (for the nested→mutual auxiliary construction's container unfolding).
    ind_ctors: std::collections::HashMap<Name, Vec<(Name, Term)>>,
    /// M3: full admitted-mutual records, keyed by EACH block type name (so a
    /// member name resolves the whole block for the idempotency check).
    admitted_mutuals: std::collections::HashMap<Name, crate::mutual::AdmittedMutual>,
}

impl MinimalEnv {
    /// An empty env.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a constant with `num_level_params`.
    #[must_use]
    pub fn with_const(mut self, name: Name, num_level_params: u32) -> Self {
        self.consts.insert(name, num_level_params);
        self
    }

    /// Register a constant with `num_level_params` and a declared type (for
    /// `infer`). The type is a closed [`Term`] over the constant's level params.
    #[must_use]
    pub fn with_const_typed(mut self, name: Name, num_level_params: u32, ty: Term) -> Self {
        self.consts.insert(name.clone(), num_level_params);
        self.types.insert(name, ty);
        self
    }

    /// Register a definition: `num_level_params`, declared type, body, and
    /// transparency. The body becomes δ-unfoldable iff `transparency` is
    /// [`Transparency::Transparent`].
    #[must_use]
    pub fn with_def(
        mut self,
        name: Name,
        num_level_params: u32,
        ty: Term,
        body: Term,
        transparency: Transparency,
    ) -> Self {
        self.consts.insert(name.clone(), num_level_params);
        self.types.insert(name.clone(), ty);
        self.defs.insert(name, ConstDef { body, transparency });
        self
    }

    /// Register an inductive with its declared `num_level_params` and its
    /// large-elim flag. An inductive is also a declaration, so it must carry a
    /// level-param count: this is what [`crate::ElimRef::mk`] checks the supplied
    /// `ind_levels` length against (design §4.2). The count is recorded in the
    /// same `consts` table that backs [`Env::num_level_params`], so the env's
    /// declaration table and inductive registry stay consistent.
    #[must_use]
    pub fn with_inductive(mut self, name: Name, num_level_params: u32, large_elim: bool) -> Self {
        self.consts.insert(name.clone(), num_level_params);
        self.inductives.insert(name, large_elim);
        self
    }

    /// Register an inductive container with its parameter count and constructors
    /// `(name, type)`, so the nested→mutual auxiliary construction (M3) can peel
    /// its parameters and unfold its constructors. Also registers the inductive
    /// type former (if `ty` is given), each constructor's type + arity, and the
    /// large-elim flag.
    #[must_use]
    pub fn with_container_inductive(
        mut self,
        name: Name,
        num_level_params: u32,
        num_params: u32,
        ty: Term,
        large_elim: bool,
        ctors: Vec<(Name, Term)>,
    ) -> Self {
        self.consts.insert(name.clone(), num_level_params);
        self.types.insert(name.clone(), ty);
        self.inductives.insert(name.clone(), large_elim);
        self.ind_num_params.insert(name.clone(), num_params);
        for (cn, ct) in &ctors {
            let arity = crate::inductive::count_pi(ct);
            let num_fields = arity.saturating_sub(num_params);
            self.consts.insert(cn.clone(), num_level_params);
            self.types.insert(cn.clone(), ct.clone());
            self.ctors.insert(
                cn.clone(),
                ConstructorArity {
                    num_params,
                    num_fields,
                },
            );
        }
        self.ind_ctors.insert(name, ctors);
        self
    }

    /// Register one of the four `Quot` built-ins under its pinned name.
    #[must_use]
    pub fn with_quot(mut self, name: Name, num_level_params: u32, kind: QuotKind) -> Self {
        self.consts.insert(name.clone(), num_level_params);
        self.quots.insert(name, kind);
        self
    }

    /// Mark `name` as a recursor (so `whnf` leaves its application stuck; ι is
    /// M2).
    #[must_use]
    pub fn with_recursor(mut self, name: Name) -> Self {
        self.recursors.insert(name);
        self
    }

    /// Register a constructor with a declared type and its param/field split.
    #[must_use]
    pub fn with_constructor(
        mut self,
        name: Name,
        num_level_params: u32,
        ty: Term,
        num_params: u32,
        num_fields: u32,
    ) -> Self {
        self.consts.insert(name.clone(), num_level_params);
        self.types.insert(name.clone(), ty);
        self.ctors.insert(
            name,
            ConstructorArity {
                num_params,
                num_fields,
            },
        );
        self
    }

    /// Register structure-η info for a single-constructor inductive.
    #[must_use]
    pub fn with_structure(
        mut self,
        struct_name: Name,
        ctor: Name,
        num_params: u32,
        num_fields: u32,
    ) -> Self {
        self.structs.insert(
            struct_name,
            StructureInfo {
                ctor,
                num_params,
                num_fields,
            },
        );
        self
    }
}

impl Env for MinimalEnv {
    fn num_level_params(&self, name: &Name) -> Option<u32> {
        self.consts.get(name).copied()
    }
    fn inductive_large_elim(&self, name: &Name) -> Option<bool> {
        self.inductives.get(name).copied()
    }
    fn const_def(&self, name: &Name) -> Option<ConstDef> {
        self.defs.get(name).cloned()
    }
    fn const_type(&self, name: &Name) -> Option<Term> {
        self.types.get(name).cloned()
    }
    fn quot_kind(&self, name: &Name) -> Option<QuotKind> {
        self.quots.get(name).copied()
    }
    fn is_recursor(&self, name: &Name) -> bool {
        self.recursors.contains(name)
    }
    fn recursor_inductive(&self, name: &Name) -> Option<Name> {
        if !self.recursors.contains(name) {
            return None;
        }
        self.rec_name_to_ind.get(name).cloned()
    }
    fn constructor_arity(&self, name: &Name) -> Option<ConstructorArity> {
        self.ctors.get(name).copied()
    }
    fn structure_info(&self, struct_name: &Name) -> Option<StructureInfo> {
        self.structs.get(struct_name).cloned()
    }
    fn recursor_type(&self, name: &Name) -> Option<Term> {
        let ind = self.rec_name_to_ind.get(name).unwrap_or(name);
        if let Some(a) = self.admitted_inductives.get(ind) {
            return Some(a.recursor.type_.clone());
        }
        let m = self.admitted_mutuals.get(ind)?;
        m.recursors
            .iter()
            .find(|r| r.inductive == *ind)
            .map(|r| r.type_.clone())
    }
    fn recursor_rules(&self, name: &Name) -> Option<Vec<crate::recursor::IotaRule>> {
        let ind = self.rec_name_to_ind.get(name).unwrap_or(name);
        if let Some(a) = self.admitted_inductives.get(ind) {
            return Some(a.recursor.rules.clone());
        }
        let m = self.admitted_mutuals.get(ind)?;
        m.recursors
            .iter()
            .find(|r| r.inductive == *ind)
            .map(|r| r.rules.clone())
    }
    fn recursor_shape(&self, name: &Name) -> Option<RecursorShape> {
        let ind = self.rec_name_to_ind.get(name).unwrap_or(name);
        if let Some(a) = self.admitted_inductives.get(ind) {
            return Some(RecursorShape {
                num_params: a.recursor.num_params,
                num_indices: a.recursor.num_indices,
                num_minors: a.recursor.num_minors_total,
                num_motives: a.recursor.num_motives,
                large_elim: a.large_elim,
            });
        }
        // Mutual-block recursor shape: find the recursor among the block whose
        // `inductive` is `ind`.
        let m = self.admitted_mutuals.get(ind)?;
        let rec = m.recursors.iter().find(|r| r.inductive == *ind)?;
        Some(RecursorShape {
            num_params: rec.num_params,
            num_indices: rec.num_indices,
            num_minors: rec.num_minors_total,
            num_motives: rec.num_motives,
            large_elim: m.large_elim,
        })
    }

    fn inductive_num_params(&self, name: &Name) -> Option<u32> {
        self.ind_num_params.get(name).copied()
    }

    fn inductive_constructors(&self, name: &Name) -> Option<Vec<(Name, Term)>> {
        self.ind_ctors.get(name).cloned()
    }
}

impl crate::inductive::MutableEnv for MinimalEnv {
    fn has_inductive(&self, name: &Name) -> bool {
        self.admitted_inductives.contains_key(name) || self.admitted_mutuals.contains_key(name)
    }

    fn admitted(&self, name: &Name) -> Option<crate::inductive::AdmittedInductive> {
        self.admitted_inductives.get(name).cloned()
    }

    fn admitted_mutual_decl(&self, name: &Name) -> Option<crate::inductive::InductiveDecl> {
        if let Some(a) = self.admitted_inductives.get(name) {
            return Some(a.decl.clone());
        }
        let m = self.admitted_mutuals.get(name)?;
        m.block.decls.iter().find(|d| d.name == *name).cloned()
    }

    fn commit_inductive(&mut self, admitted: crate::inductive::AdmittedInductive) {
        let decl = &admitted.decl;
        // Register the inductive type former.
        self.consts.insert(decl.name.clone(), decl.num_level_params);
        self.types.insert(decl.name.clone(), decl.type_.clone());
        self.inductives
            .insert(decl.name.clone(), admitted.large_elim);
        // M3: container metadata so a singly-admitted inductive can later be a
        // nesting container (e.g. List nested inside RoseTree).
        self.ind_num_params
            .insert(decl.name.clone(), decl.num_params);
        self.ind_ctors.insert(
            decl.name.clone(),
            decl.constructors
                .iter()
                .map(|c| (c.name.clone(), c.type_.clone()))
                .collect(),
        );
        // Register constructors (type + param/field arity).
        for ctor in &decl.constructors {
            let arity = crate::inductive::count_pi(&ctor.type_);
            let num_fields = arity.saturating_sub(decl.num_params);
            self.consts.insert(ctor.name.clone(), decl.num_level_params);
            self.types.insert(ctor.name.clone(), ctor.type_.clone());
            self.ctors.insert(
                ctor.name.clone(),
                ConstructorArity {
                    num_params: decl.num_params,
                    num_fields,
                },
            );
        }
        // Single-constructor inductive → also a structure (for proj/structure-η)
        // ONLY when it is a genuine η-structure: 1 ctor, NO indices, NON-recursive
        // (so `mk (proj t) ≡ t`). An indexed or recursive single-ctor inductive
        // (e.g. `Eq`, or a recursive record) is NOT η-eligible — registering it
        // would make structure-η a false-accept. Fail-closed: gate before insert.
        if decl.constructors.len() == 1 {
            let ctor = &decl.constructors[0];
            let arity = crate::inductive::count_pi(&ctor.type_);
            let num_fields = arity.saturating_sub(decl.num_params);
            if crate::inductive::is_eta_structure(
                &ctor.type_,
                decl.num_params,
                admitted.recursor.num_indices,
                decl.constructors.len(),
                std::slice::from_ref(&decl.name),
            ) {
                self.structs.insert(
                    decl.name.clone(),
                    StructureInfo {
                        ctor: ctor.name.clone(),
                        num_params: decl.num_params,
                        num_fields,
                    },
                );
            }
        }
        // Register the recursor: name → inductive map, level-param count, and
        // mark it as a recursor.
        let rec = &admitted.recursor;
        self.consts.insert(rec.name.clone(), rec.num_level_params);
        self.recursors.insert(rec.name.clone());
        self.rec_name_to_ind
            .insert(rec.name.clone(), decl.name.clone());
        self.admitted_inductives.insert(decl.name.clone(), admitted);
    }
}

impl crate::mutual::MutableMutualEnv for MinimalEnv {
    fn commit_mutual(&mut self, admitted: crate::mutual::AdmittedMutual) {
        let np = admitted.block.num_params();
        let nlp = admitted.block.num_level_params();
        // The whole block is the recursion "family": a single-ctor member is an
        // η-structure only if NONE of its fields mention ANY block member (a
        // cross-member recursive field is just as non-projectable as a self-
        // recursive one).
        let family: Vec<Name> = admitted
            .block
            .decls
            .iter()
            .map(|d| d.name.clone())
            .collect();
        // Register every block type former + constructors + container metadata.
        for d in &admitted.block.decls {
            self.consts.insert(d.name.clone(), nlp);
            self.types.insert(d.name.clone(), d.type_.clone());
            self.inductives.insert(d.name.clone(), admitted.large_elim);
            self.ind_num_params.insert(d.name.clone(), np);
            self.ind_ctors.insert(
                d.name.clone(),
                d.constructors
                    .iter()
                    .map(|c| (c.name.clone(), c.type_.clone()))
                    .collect(),
            );
            for ctor in &d.constructors {
                let arity = crate::inductive::count_pi(&ctor.type_);
                let num_fields = arity.saturating_sub(np);
                self.consts.insert(ctor.name.clone(), nlp);
                self.types.insert(ctor.name.clone(), ctor.type_.clone());
                self.ctors.insert(
                    ctor.name.clone(),
                    ConstructorArity {
                        num_params: np,
                        num_fields,
                    },
                );
            }
            // η-structure gate (mutual): 1 ctor, NO indices, NON-recursive across
            // the whole block. `num_indices` comes from this member's derived
            // recursor; a missing recursor (should not happen) fails the gate.
            if d.constructors.len() == 1 {
                let ctor = &d.constructors[0];
                let arity = crate::inductive::count_pi(&ctor.type_);
                let num_fields = arity.saturating_sub(np);
                let num_indices = admitted
                    .recursors
                    .iter()
                    .find(|r| r.inductive == d.name)
                    .map_or(u32::MAX, |r| r.num_indices);
                if crate::inductive::is_eta_structure(
                    &ctor.type_,
                    np,
                    num_indices,
                    d.constructors.len(),
                    &family,
                ) {
                    self.structs.insert(
                        d.name.clone(),
                        StructureInfo {
                            ctor: ctor.name.clone(),
                            num_params: np,
                            num_fields,
                        },
                    );
                }
            }
        }
        // Register each derived recursor: name → inductive map, level count.
        for rec in &admitted.recursors {
            self.consts.insert(rec.name.clone(), rec.num_level_params);
            self.recursors.insert(rec.name.clone());
            self.rec_name_to_ind
                .insert(rec.name.clone(), rec.inductive.clone());
        }
        // Key the block record by EACH member name.
        for d in &admitted.block.decls {
            self.admitted_mutuals
                .insert(d.name.clone(), admitted.clone());
        }
    }
}

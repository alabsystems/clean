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
    /// Read-only base of a temporary export admission overlay; never nested.
    admission_base: Option<std::sync::Arc<MinimalEnv>>,
    consts: std::collections::HashMap<Name, u32>,
    /// Private lowering symbols are never names the wire input may reference.
    #[cfg(feature = "export")]
    export_hidden: std::collections::HashSet<Name>,
    /// None preserves the host API; Some explicitly licenses individual folds.
    native_nat_folds: Option<std::collections::HashSet<Name>>,
    types: std::collections::HashMap<Name, Term>,
    string_literal_view: bool,
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
    admitted_mutuals:
        std::collections::HashMap<Name, std::sync::Arc<crate::mutual::AdmittedMutual>>,
}

impl MinimalEnv {
    /// An empty env.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    #[cfg(feature = "export")]
    pub(crate) fn restrict_native_nat_folds(&mut self) {
        self.native_nat_folds = Some(std::collections::HashSet::new());
    }

    #[cfg(feature = "export")]
    pub(crate) fn license_native_nat(&mut self, name: Name) {
        if let Some(allowed) = &mut self.native_nat_folds {
            allowed.insert(name);
        }
    }

    #[cfg(feature = "export")]
    pub(crate) fn license_string_literal_view(&mut self) {
        self.string_literal_view = true;
    }

    #[cfg(feature = "export")]
    pub(crate) fn hide_from_export(&mut self, name: Name) {
        self.export_hidden.insert(name);
    }

    #[cfg(feature = "export")]
    pub(crate) fn hidden_from_export(&self, name: &Name) -> bool {
        self.export_hidden.contains(name)
            || self
                .admission_base
                .as_deref()
                .is_some_and(|base| base.hidden_from_export(name))
    }

    #[cfg(feature = "export")]
    pub(crate) fn recursor_export_alias(&mut self, alias: Name, owner: &Name) -> Option<()> {
        if self.consts.contains_key(&alias) {
            return None;
        }
        let levels = self.consts.get(&owner.str("rec")).copied()?;
        self.consts.insert(alias.clone(), levels);
        self.recursors.insert(alias.clone());
        self.rec_name_to_ind.insert(alias, owner.clone());
        Some(())
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
    fn string_literal_view(&self) -> bool {
        self.string_literal_view
    }

    fn native_nat_allowed(&self, name: &Name) -> bool {
        match &self.native_nat_folds {
            None => true,
            Some(allowed) => allowed.contains(name),
        }
    }

    fn num_level_params(&self, name: &Name) -> Option<u32> {
        self.consts
            .get(name)
            .copied()
            .or_else(|| self.admission_base.as_deref()?.num_level_params(name))
    }
    fn inductive_large_elim(&self, name: &Name) -> Option<bool> {
        self.inductives
            .get(name)
            .copied()
            .or_else(|| self.admission_base.as_deref()?.inductive_large_elim(name))
    }
    fn const_def(&self, name: &Name) -> Option<ConstDef> {
        self.defs
            .get(name)
            .cloned()
            .or_else(|| self.admission_base.as_deref()?.const_def(name))
    }
    fn const_type(&self, name: &Name) -> Option<Term> {
        self.types
            .get(name)
            .cloned()
            .or_else(|| self.admission_base.as_deref()?.const_type(name))
    }
    fn quot_kind(&self, name: &Name) -> Option<QuotKind> {
        self.quots
            .get(name)
            .copied()
            .or_else(|| self.admission_base.as_deref()?.quot_kind(name))
    }
    fn is_recursor(&self, name: &Name) -> bool {
        self.recursors.contains(name)
            || self
                .admission_base
                .as_deref()
                .is_some_and(|base| base.is_recursor(name))
    }
    fn recursor_inductive(&self, name: &Name) -> Option<Name> {
        self.rec_name_to_ind
            .get(name)
            .cloned()
            .or_else(|| self.admission_base.as_deref()?.recursor_inductive(name))
    }
    fn constructor_arity(&self, name: &Name) -> Option<ConstructorArity> {
        self.ctors
            .get(name)
            .copied()
            .or_else(|| self.admission_base.as_deref()?.constructor_arity(name))
    }
    fn structure_info(&self, struct_name: &Name) -> Option<StructureInfo> {
        self.structs
            .get(struct_name)
            .cloned()
            .or_else(|| self.admission_base.as_deref()?.structure_info(struct_name))
    }
    fn recursor_type(&self, name: &Name) -> Option<Term> {
        let ind = self.rec_name_to_ind.get(name).unwrap_or(name);
        if let Some(a) = self.admitted_inductives.get(ind) {
            return Some(a.recursor.type_.clone());
        }
        let Some(m) = self.admitted_mutuals.get(ind) else {
            return self.admission_base.as_deref()?.recursor_type(ind);
        };
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
        let Some(m) = self.admitted_mutuals.get(ind) else {
            return self.admission_base.as_deref()?.recursor_rules(ind);
        };
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
        let Some(m) = self.admitted_mutuals.get(ind) else {
            return self.admission_base.as_deref()?.recursor_shape(ind);
        };
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
        self.ind_num_params
            .get(name)
            .copied()
            .or_else(|| self.admission_base.as_deref()?.inductive_num_params(name))
    }

    fn inductive_family(&self, name: &Name) -> Option<Vec<Name>> {
        if let Some(block) = self.admitted_mutuals.get(name) {
            let members = block.block.decls.iter().map(|d| d.name.clone());
            #[cfg(feature = "export")]
            let members = members.filter(|n| !self.hidden_from_export(n));
            return Some(members.collect());
        }
        if let Some(base) = self.admission_base.as_deref() {
            if let Some(family) = base.inductive_family(name) {
                return Some(family);
            }
        }
        self.inductive_num_params(name).map(|_| vec![name.clone()])
    }

    fn inductive_constructors(&self, name: &Name) -> Option<Vec<(Name, Term)>> {
        self.ind_ctors
            .get(name)
            .cloned()
            .or_else(|| self.admission_base.as_deref()?.inductive_constructors(name))
    }
}

mod admission;

#[cfg(feature = "export")]
mod overlay;

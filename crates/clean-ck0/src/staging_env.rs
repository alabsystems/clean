// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The read-only [`Env`] overlay used during inductive admission (design §5.2).
//! Extracted from `inductive.rs` to keep both files under the 500-line
//! convention. See [`StagingEnv`] for the rationale.

use crate::inductive::{count_pi, InductiveDecl};
use crate::name::Name;
use crate::term::Term;
use crate::validate::Env;

/// A read-only [`Env`] overlay used during admission: the underlying env plus
/// the inductive type former and its constructors (which are not yet committed),
/// so positivity-free checks — field-sort inference and the recursor kernel-check
/// — can resolve `I` and `I`'s constructors before the recursor exists.
pub(crate) struct StagingEnv<'a> {
    base: &'a dyn Env,
    ind_name: Name,
    ind_type: Term,
    num_level_params: u32,
    num_params: u32,
    ctor_types: std::collections::HashMap<Name, Term>,
    ctor_arity: std::collections::HashMap<Name, crate::validate::ConstructorArity>,
    structure: Option<(Name, crate::validate::StructureInfo)>,
}

impl<'a> StagingEnv<'a> {
    pub(crate) fn new(base: &'a dyn Env, decl: &InductiveDecl) -> Self {
        let mut ctor_types = std::collections::HashMap::new();
        let mut ctor_arity = std::collections::HashMap::new();
        for ctor in &decl.constructors {
            let arity = count_pi(&ctor.type_);
            let num_fields = arity.saturating_sub(decl.num_params);
            ctor_types.insert(ctor.name.clone(), ctor.type_.clone());
            ctor_arity.insert(
                ctor.name.clone(),
                crate::validate::ConstructorArity {
                    num_params: decl.num_params,
                    num_fields,
                },
            );
        }
        // η-structure gate, same soundness side-condition as the committed env:
        // 1 ctor, NO indices, NON-recursive. `num_indices` of the type former is
        // `arity(I) - num_params` (the type former's trailing Pi binders past the
        // parameters). Gating here keeps structure-η from firing UNSOUNDLY on an
        // indexed/recursive single-ctor inductive while it is still being admitted
        // (the staging env is what `infer`/`is_def_eq` consult during the recursor
        // kernel-check).
        let num_indices = count_pi(&decl.type_).saturating_sub(decl.num_params);
        let structure = if decl.constructors.len() == 1 {
            let ctor = &decl.constructors[0];
            let arity = count_pi(&ctor.type_);
            let num_fields = arity.saturating_sub(decl.num_params);
            if crate::inductive::is_eta_structure(
                &ctor.type_,
                decl.num_params,
                num_indices,
                decl.constructors.len(),
                std::slice::from_ref(&decl.name),
            ) {
                Some((
                    decl.name.clone(),
                    crate::validate::StructureInfo {
                        ctor: ctor.name.clone(),
                        num_params: decl.num_params,
                        num_fields,
                    },
                ))
            } else {
                None
            }
        } else {
            None
        };
        StagingEnv {
            base,
            ind_name: decl.name.clone(),
            ind_type: decl.type_.clone(),
            num_level_params: decl.num_level_params,
            num_params: decl.num_params,
            ctor_types,
            ctor_arity,
            structure,
        }
    }
}

/// The mutual-block analogue of [`StagingEnv`]: a read-only [`Env`] overlay that
/// knows *every* block type former and *every* constructor of the block (none
/// committed yet), so field-sort inference, the gate, and the per-type recursor
/// kernel-check can resolve cross-type references before any recursor exists.
pub(crate) struct MutualStagingEnv<'a> {
    base: &'a dyn Env,
    num_level_params: u32,
    /// type-former name -> its declared type.
    ind_types: std::collections::HashMap<Name, Term>,
    ctor_types: std::collections::HashMap<Name, Term>,
    ctor_arity: std::collections::HashMap<Name, crate::validate::ConstructorArity>,
    /// single-constructor block types are also structures (proj/structure-η).
    structures: std::collections::HashMap<Name, crate::validate::StructureInfo>,
}

impl<'a> MutualStagingEnv<'a> {
    pub(crate) fn new(base: &'a dyn Env, block: &crate::mutual::MutualBlock) -> Self {
        let num_params = block.num_params();
        let num_level_params = block.num_level_params();
        let mut ind_types = std::collections::HashMap::new();
        let mut ctor_types = std::collections::HashMap::new();
        let mut ctor_arity = std::collections::HashMap::new();
        let mut structures = std::collections::HashMap::new();
        // Family = every block member; a single-ctor member is an η-structure only
        // if NONE of its fields mention ANY block member (no cross-member or self
        // recursion) AND it has no indices.
        let family: Vec<Name> = block.decls.iter().map(|d| d.name.clone()).collect();
        for d in &block.decls {
            ind_types.insert(d.name.clone(), d.type_.clone());
            for ctor in &d.constructors {
                let arity = count_pi(&ctor.type_);
                let num_fields = arity.saturating_sub(num_params);
                ctor_types.insert(ctor.name.clone(), ctor.type_.clone());
                ctor_arity.insert(
                    ctor.name.clone(),
                    crate::validate::ConstructorArity {
                        num_params,
                        num_fields,
                    },
                );
            }
            // η-structure gate (mutual staging): 1 ctor, NO indices, NON-recursive
            // across the whole block. `num_indices` of member `d` is its type
            // former's trailing Pi binders past the params.
            let num_indices = count_pi(&d.type_).saturating_sub(num_params);
            if d.constructors.len() == 1 {
                let ctor = &d.constructors[0];
                let arity = count_pi(&ctor.type_);
                let num_fields = arity.saturating_sub(num_params);
                if crate::inductive::is_eta_structure(
                    &ctor.type_,
                    num_params,
                    num_indices,
                    d.constructors.len(),
                    &family,
                ) {
                    structures.insert(
                        d.name.clone(),
                        crate::validate::StructureInfo {
                            ctor: ctor.name.clone(),
                            num_params,
                            num_fields,
                        },
                    );
                }
            }
        }
        MutualStagingEnv {
            base,
            num_level_params,
            ind_types,
            ctor_types,
            ctor_arity,
            structures,
        }
    }
}

impl Env for MutualStagingEnv<'_> {
    fn num_level_params(&self, name: &Name) -> Option<u32> {
        if self.ind_types.contains_key(name) || self.ctor_types.contains_key(name) {
            return Some(self.num_level_params);
        }
        self.base.num_level_params(name)
    }
    fn inductive_large_elim(&self, name: &Name) -> Option<bool> {
        if self.ind_types.contains_key(name) {
            return Some(false); // placeholder; never consulted on the staging path
        }
        self.base.inductive_large_elim(name)
    }
    fn const_def(&self, name: &Name) -> Option<crate::validate::ConstDef> {
        self.base.const_def(name)
    }
    fn const_type(&self, name: &Name) -> Option<Term> {
        if let Some(t) = self.ind_types.get(name) {
            return Some(t.clone());
        }
        if let Some(t) = self.ctor_types.get(name) {
            return Some(t.clone());
        }
        self.base.const_type(name)
    }
    fn quot_kind(&self, name: &Name) -> Option<crate::validate::QuotKind> {
        self.base.quot_kind(name)
    }
    fn is_recursor(&self, name: &Name) -> bool {
        self.base.is_recursor(name)
    }
    fn recursor_inductive(&self, name: &Name) -> Option<Name> {
        self.base.recursor_inductive(name)
    }
    fn constructor_arity(&self, name: &Name) -> Option<crate::validate::ConstructorArity> {
        if let Some(a) = self.ctor_arity.get(name) {
            return Some(*a);
        }
        self.base.constructor_arity(name)
    }
    fn structure_info(&self, struct_name: &Name) -> Option<crate::validate::StructureInfo> {
        if let Some(info) = self.structures.get(struct_name) {
            return Some(info.clone());
        }
        self.base.structure_info(struct_name)
    }
    fn recursor_type(&self, name: &Name) -> Option<Term> {
        self.base.recursor_type(name)
    }
    fn recursor_rules(&self, name: &Name) -> Option<Vec<crate::recursor::IotaRule>> {
        self.base.recursor_rules(name)
    }
    fn recursor_shape(&self, name: &Name) -> Option<crate::validate::RecursorShape> {
        self.base.recursor_shape(name)
    }
}

impl Env for StagingEnv<'_> {
    fn num_level_params(&self, name: &Name) -> Option<u32> {
        if *name == self.ind_name || self.ctor_types.contains_key(name) {
            return Some(self.num_level_params);
        }
        self.base.num_level_params(name)
    }
    fn inductive_large_elim(&self, name: &Name) -> Option<bool> {
        if *name == self.ind_name {
            // large-elim flag not yet computed; report small as a placeholder —
            // never consulted on the staging path (we don't build ElimRefs here).
            return Some(false);
        }
        self.base.inductive_large_elim(name)
    }
    fn const_def(&self, name: &Name) -> Option<crate::validate::ConstDef> {
        self.base.const_def(name)
    }
    fn const_type(&self, name: &Name) -> Option<Term> {
        if *name == self.ind_name {
            return Some(self.ind_type.clone());
        }
        if let Some(t) = self.ctor_types.get(name) {
            return Some(t.clone());
        }
        self.base.const_type(name)
    }
    fn quot_kind(&self, name: &Name) -> Option<crate::validate::QuotKind> {
        self.base.quot_kind(name)
    }
    fn is_recursor(&self, name: &Name) -> bool {
        self.base.is_recursor(name)
    }
    fn recursor_inductive(&self, name: &Name) -> Option<Name> {
        self.base.recursor_inductive(name)
    }
    fn constructor_arity(&self, name: &Name) -> Option<crate::validate::ConstructorArity> {
        if let Some(a) = self.ctor_arity.get(name) {
            return Some(*a);
        }
        self.base.constructor_arity(name)
    }
    fn structure_info(&self, struct_name: &Name) -> Option<crate::validate::StructureInfo> {
        if let Some((n, info)) = &self.structure {
            if n == struct_name {
                return Some(info.clone());
            }
        }
        self.base.structure_info(struct_name)
    }
    fn recursor_type(&self, name: &Name) -> Option<Term> {
        self.base.recursor_type(name)
    }
    fn recursor_rules(&self, name: &Name) -> Option<Vec<crate::recursor::IotaRule>> {
        self.base.recursor_rules(name)
    }
    fn recursor_shape(&self, name: &Name) -> Option<crate::validate::RecursorShape> {
        self.base.recursor_shape(name)
    }
}

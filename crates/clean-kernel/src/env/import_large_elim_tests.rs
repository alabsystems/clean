// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The in-place large-elimination recompute must reach the verdict the
//! per-module staging clone reached, for both answers, and must leave a
//! kernel-checked inductive alone.

use super::super::{DeclarationVerification, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::inductive::{allows_large_elim, Constructor, ConstructorVal, InductiveVal};
use crate::name::Name;

fn n(s: &str) -> Name {
    Name::from_string(s)
}

/// `inductive <name> (p : Prop) : Prop | intro (h : p)` when `prop_field`,
/// else `inductive <name> (α : Type) : Prop | intro (val : α)` — the
/// `Nonempty` shape, whose recursor may only eliminate into `Prop`.
fn family(name: &str, prop_field: bool) -> (InductiveVal, ConstructorVal) {
    let param_ty = if prop_field {
        Expr::prop()
    } else {
        Expr::sort(crate::level::Level::succ(crate::level::Level::Zero))
    };
    let ind_ty = Expr::pi(BinderInfo::Default, param_ty.clone(), Expr::prop());
    // (p : P) → (h : p) → name p
    let ctor_ty = Expr::pi(
        BinderInfo::Default,
        param_ty,
        Expr::pi(
            BinderInfo::Default,
            Expr::bvar(0),
            Expr::app(Expr::const_(n(name), vec![]), Expr::bvar(1)),
        ),
    );
    let ctor_name = n(&format!("{name}.intro"));
    (
        InductiveVal {
            name: n(name),
            level_params: vec![],
            type_: ind_ty,
            num_params: 1,
            num_indices: 0,
            all_names: vec![n(name)],
            constructor_names: vec![ctor_name.clone()],
            is_recursive: false,
            is_reflexive: false,
            // The converter's placeholder, as `convert_direct` sets it.
            is_large_elim: true,
            is_nested: false,
        },
        ConstructorVal {
            name: ctor_name,
            inductive_name: n(name),
            level_params: vec![],
            type_: ctor_ty,
            num_params: 1,
            num_fields: 1,
            constructor_idx: 0,
        },
    )
}

fn ctor_list(ctor: &ConstructorVal) -> Vec<Constructor> {
    vec![Constructor {
        name: ctor.name.clone(),
        type_: ctor.type_.clone(),
    }]
}

/// The pre-2026-09-26 staging: clone, insert the family, decide.
fn staged_verdict(base: &Environment, ind: &InductiveVal, ctor: &ConstructorVal) -> bool {
    let mut staging = base.clone();
    let _ = staging.extend_inductives_structural(std::iter::once(ind.clone()));
    let _ = staging.extend_constructors_structural(std::iter::once(ctor.clone()));
    allows_large_elim(
        &staging,
        &ind.type_,
        &ctor_list(ctor),
        ind.num_params,
        ind.all_names.len(),
    )
}

#[test]
fn test_recompute_imported_large_elim_matches_staging_clone_for_both_verdicts() {
    for (name, prop_field, expected) in [("PropBox", true, true), ("TypeBox", false, false)] {
        let base = Environment::new();
        let (ind, ctor) = family(name, prop_field);
        let staged = staged_verdict(&base, &ind, &ctor);
        assert_eq!(staged, expected, "{name}: staging-clone verdict");

        let mut env = base.clone();
        assert!(env
            .extend_inductives_structural(std::iter::once(ind.clone()))
            .is_empty());
        assert!(env
            .extend_constructors_structural(std::iter::once(ctor.clone()))
            .is_empty());
        let gen_before = env.generation();
        let changed = env.recompute_imported_large_elim([(n(name), ctor_list(&ctor))]);
        let now = env.get_inductive(&n(name)).expect("resident").is_large_elim;
        assert_eq!(
            now, staged,
            "{name}: in-place verdict must equal the staged one"
        );
        assert_eq!(
            changed,
            usize::from(!expected),
            "{name}: placeholder was `true`"
        );
        assert_eq!(
            env.generation() > gen_before,
            !expected,
            "{name}: bump iff changed"
        );
    }
}

#[test]
fn test_recompute_imported_large_elim_leaves_kernel_checked_inductive_alone() {
    let mut env = Environment::new();
    let (ind, ctor) = family("CheckedBox", false);
    assert!(env
        .extend_inductives_structural(std::iter::once(ind))
        .is_empty());
    assert!(env
        .extend_constructors_structural(std::iter::once(ctor.clone()))
        .is_empty());
    env.declaration_verification
        .insert(n("CheckedBox"), DeclarationVerification::FullKernelCheck);
    let changed = env.recompute_imported_large_elim([(n("CheckedBox"), ctor_list(&ctor))]);
    assert_eq!(changed, 0);
    assert!(
        env.get_inductive(&n("CheckedBox"))
            .expect("resident")
            .is_large_elim,
        "a kernel-checked flag is never revisited"
    );
}

#[test]
fn test_recompute_imported_large_elim_ignores_absent_names() {
    let mut env = Environment::new();
    assert_eq!(
        env.recompute_imported_large_elim([(n("Nowhere"), Vec::new())]),
        0
    );
}

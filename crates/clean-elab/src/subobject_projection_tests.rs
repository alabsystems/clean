// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! ON-THE-FLY inherited-field projection — Lean 4's `mkBaseProjections`.
//!
//! For `structure C extends P`, Lean 4 declares NO constant for an inherited
//! field: `c.f` is composed at the use site as `P.f (C.toP c)`. Clean
//! additionally MATERIALIZES that composition as a constant `C.f`
//! (`infer::elab_structure::build_inherited_projections`), which is a
//! Clean-only environment entry.
//!
//! MEASURED, against real Lean 4 v4.30.0-rc2. `import Lean` (197,256
//! constants): 160 structures carry inherited fields, giving 1,235
//! (structure, inherited field) pairs, and Lean declares a constant for
//! **0** of them. `import Mathlib` (754,026 constants): 1,098 structures,
//! **9,185** pairs, again **0** declared — and **0** of those 9,185 names is
//! declared by anything else either, so the collision search is closed.
//! Clean's own `.olean` IMPORT path also declares 0 — it
//! recovers only OWN field names from real Lean projection bodies
//! (`clean_olean::import::load_register::register_structure_fields_from_projections`)
//! and never calls `register_structure_parents`. So the divergence is created
//! by Clean's `structure` elaborator alone, and Clean's two paths to the "same"
//! environment disagree with each other.
//!
//! These tests pin the composer that closes it:
//! [`crate::name_resolution::compose_subobject_projection`] builds the kernel
//! `Proj` spine directly, with no constant, no name lookup and no universe
//! parameters to mint. The companion fixture
//! `tests/fixtures/namespace_shadowing/inherited_projection_composed.lean`
//! carries the KERNEL-CHECKED half: `x.toMyBase.widget = MyDer.widget Nat x`
//! by `rfl`, i.e. the composed chain is definitionally equal to the generated
//! constant's application.
//!
//! See `designs/2026-08-24-inherited-projection-parity.md`.

use crate::name_resolution::{compose_subobject_projection, inherited_field_subobject_hop};
use crate::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_kernel::env::Environment;
use clean_kernel::{Expr, ExprKind, Name};
use clean_parser::parse_file;

/// Two-level `extends` chain: `MyDer extends MyBase`, `MyTop extends MyDer`.
const SOURCE: &str = "\
universe u
structure MyBase (a : Type u) where
  widget : a
structure MyDer (a : Type u) extends MyBase a where
  tag : Nat
structure MyTop (a : Type u) extends MyDer a where
  extra : Nat
";

fn env_with_chain() -> Environment {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(SOURCE).expect("fixture source must parse");
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        elaborate_decl_and_register(&mut env, &processed).expect("declaration must elaborate");
    }
    env
}

/// Peel a `Proj` spine into `[(struct, idx), …]` outermost-first, returning the
/// innermost non-`Proj` expression alongside it.
fn peel(mut e: &Expr) -> (Vec<(String, u32)>, &Expr) {
    let mut hops = Vec::new();
    while let ExprKind::Proj(name, idx, inner) = e.kind() {
        hops.push((name.to_string(), *idx));
        e = inner.as_ref();
    }
    (hops, e)
}

/// An OWN field composes to a single `Proj` — the composer must not invent a
/// parent hop for a field the structure already carries.
#[test]
fn own_field_composes_to_a_single_projection() {
    let env = env_with_chain();
    let recv = Expr::fvar(clean_kernel::FVarId::new(0));
    let composed = compose_subobject_projection(
        &env,
        &Name::from_string("MyDer"),
        &Name::from_string("tag"),
        recv.clone(),
        0,
    )
    .expect("`tag` is an own field of `MyDer`");
    let (hops, base) = peel(&composed);
    assert_eq!(
        hops.len(),
        1,
        "own field must be ONE projection: {composed:?}"
    );
    assert_eq!(hops[0].0, "MyDer");
    assert_eq!(base, &recv, "the receiver must be preserved verbatim");
}

/// One level of `extends`: `widget` is inherited from `MyBase`, so the chain is
/// `Proj(MyBase, widget, Proj(MyDer, toMyBase, x))` — exactly the shape the
/// generated constant `MyDer.widget` unfolds to.
#[test]
fn inherited_field_composes_through_the_parent_subobject() {
    let env = env_with_chain();
    let recv = Expr::fvar(clean_kernel::FVarId::new(0));
    let composed = compose_subobject_projection(
        &env,
        &Name::from_string("MyDer"),
        &Name::from_string("widget"),
        recv.clone(),
        0,
    )
    .expect("`widget` is reachable on `MyDer` through `toMyBase`");
    let (hops, base) = peel(&composed);
    assert_eq!(
        hops.iter().map(|(n, _)| n.as_str()).collect::<Vec<_>>(),
        vec!["MyBase", "MyDer"],
        "outermost hop reads the parent field, innermost reads the subobject slot: {composed:?}"
    );
    assert_eq!(base, &recv);
}

/// TWO levels: `MyTop`'s `widget` is its grandparent's field, so the walk
/// recurses and produces a three-deep spine. This is the case a
/// non-recursive composer would silently miss.
#[test]
fn grandparent_field_composes_through_two_subobject_hops() {
    let env = env_with_chain();
    let recv = Expr::fvar(clean_kernel::FVarId::new(0));
    let composed = compose_subobject_projection(
        &env,
        &Name::from_string("MyTop"),
        &Name::from_string("widget"),
        recv.clone(),
        0,
    )
    .expect("`widget` is reachable on `MyTop` through `toMyDer.toMyBase`");
    let (hops, base) = peel(&composed);
    assert_eq!(
        hops.iter().map(|(n, _)| n.as_str()).collect::<Vec<_>>(),
        vec!["MyBase", "MyDer", "MyTop"],
        "grandparent field needs TWO subobject hops: {composed:?}"
    );
    assert_eq!(base, &recv);
}

/// A field that exists nowhere in the chain must decline, not fabricate an
/// index. (A fabricated index would be caught by the kernel, but declining is
/// what lets the caller report the precise unknown-field diagnostic.)
#[test]
fn unknown_field_declines() {
    let env = env_with_chain();
    assert!(
        compose_subobject_projection(
            &env,
            &Name::from_string("MyTop"),
            &Name::from_string("noSuchField"),
            Expr::fvar(clean_kernel::FVarId::new(0)),
            0,
        )
        .is_none(),
        "an unknown field must not compose to anything"
    );
}

/// The first-hop query used by the structure-UPDATE rewrite: `None` for an own
/// field, the `toParent` slot for an inherited one, at any depth.
#[test]
fn subobject_hop_names_the_first_parent_only() {
    let env = env_with_chain();
    assert_eq!(
        inherited_field_subobject_hop(&env, &Name::from_string("MyDer"), &Name::from_string("tag")),
        None,
        "an own field has no subobject hop"
    );
    assert_eq!(
        inherited_field_subobject_hop(
            &env,
            &Name::from_string("MyDer"),
            &Name::from_string("widget")
        )
        .map(|n| n.to_string()),
        Some("toMyBase".to_string())
    );
    assert_eq!(
        inherited_field_subobject_hop(
            &env,
            &Name::from_string("MyTop"),
            &Name::from_string("widget")
        )
        .map(|n| n.to_string()),
        Some("toMyDer".to_string()),
        "the FIRST hop, not the terminal one"
    );
}

/// The parity switch is OFF unless the operator sets it, so every gate in this
/// repo measures the shipped behaviour. If this ever fails, a default flipped
/// without the dependency census that must precede it.
#[test]
fn lean4_struct_parity_is_off_by_default() {
    assert!(
        std::env::var("CLEAN_LEAN4_STRUCT_PARITY").is_err(),
        "the suite must not be run with the parity instrument set; \
         it changes the environment's constant set"
    );
    assert!(!crate::name_resolution::lean4_struct_parity_enabled());
}

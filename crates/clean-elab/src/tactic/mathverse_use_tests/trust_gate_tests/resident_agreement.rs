// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Test code by its own head: the source gates read a file-level #![cfg(test)]
// as proof (headed_cfg_test in scripts/check_add_decl_ratchet.py).
#![cfg(test)]

use super::*;

/// Shard `Victim.def : Prop`; resident `Victim.def : Prop → Prop`.
/// Same name, same kind, DIFFERENT type — and the gate must now say no.
#[test]
fn test_resident_definition_with_different_type_is_rejected() {
    let shard = build_guard_shard(&[
        (
            "Good.thm",
            ImportConfidence::KernelVerified,
            DeclKind::Theorem,
            true,
        ),
        // `build_guard_shard` gives every row the type `Sort 0` (Prop).
        (
            "Victim.def",
            ImportConfidence::KernelVerified,
            DeclKind::Definition,
            /* has_value */ true,
        ),
    ]);
    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    lib.load_shard(&shard).unwrap();
    lib.add_dependency(0, 1);

    let mut env = Environment::new();
    let prop = Expr::sort(Level::zero());
    // Resident type is `Prop → Prop`, NOT the shard's `Prop`. Not even
    // definitionally equal — there is no reduction from one to the other.
    env.add_decl(clean_kernel::Declaration::Definition {
        name: clean_kernel::Name::from_string("Victim.def"),
        level_params: vec![],
        type_: Expr::pi(
            clean_kernel::BinderInfo::Default,
            prop.clone(),
            prop.clone(),
        ),
        value: Expr::lam(clean_kernel::BinderInfo::Default, prop, Expr::bvar(0)),
        is_reducible: false,
    })
    .expect("the resident definition is well-typed and must register");
    assert_eq!(
        env.declaration_verification(&clean_kernel::Name::from_string("Victim.def")),
        Some(clean_kernel::DeclarationVerification::FullKernelCheck),
        "precondition: the resident IS fully kernel-checked — that is what \
             makes this hole invisible to the verdict test and to the kind test"
    );

    let candidate = premise_candidate(&lib, 0);
    for gate in [TrustGate::Strict, TrustGate::RelaxedFoundational] {
        let detail = detail_from_result(validate_dependency_loader_trust(
            &env, &candidate, &lib, gate,
        ));
        assert!(
            detail.contains("Victim.def") && detail.contains("type substitution"),
            "{gate:?} must reject the type-substituted resident by name: {detail}"
        );
    }
    // …and `Relaxed`, the explicitly weaker bang-variant gate, is untouched.
    assert!(
        validate_dependency_loader_trust(&env, &candidate, &lib, TrustGate::Relaxed).is_ok(),
        "the type-agreement check is scoped to the gates that demand KernelVerified"
    );
}

/// The other half of the measurement: a resident that genuinely IS the shard
/// row must still be admitted. Same shape as the test above — a `Definition`
/// row against a `Definition` resident — with the type made to agree.
#[test]
fn test_resident_definition_with_matching_type_is_admitted() {
    // Shard `Victim.def : Type`; resident `Victim.def : Type := Prop`.
    let shard = build_resident_probe_shard(
        "Victim.def",
        DeclKind::Definition,
        &[],
        |w| {
            let l0 = w.add_level(FlatLevel::zero());
            let l1 = w.add_level(FlatLevel::succ(l0));
            w.add_expr(FlatExpr::sort(l1))
        },
        |_| {},
    );
    let lib = probe_library(&shard);

    let mut env = Environment::new();
    env.add_decl(clean_kernel::Declaration::Definition {
        name: clean_kernel::Name::from_string("Victim.def"),
        level_params: vec![],
        type_: Expr::sort(Level::succ(Level::zero())),
        value: Expr::sort(Level::zero()),
        is_reducible: false,
    })
    .expect("resident registers");

    let candidate = premise_candidate(&lib, 0);
    for gate in [TrustGate::Strict, TrustGate::RelaxedFoundational] {
        assert!(
            validate_dependency_loader_trust(&env, &candidate, &lib, gate).is_ok(),
            "a resident whose type agrees with the shard row must still be admitted under \
                 {gate:?} — over-rejection here collapses citability"
        );
    }
}

/// The canonicalization cannot be turned into a false MATCH by pre-spelling
/// its reserved names. Shard `Dep.{u} : Sort _mathverse_lp_0` (`u` declared
/// but unused) against resident `Dep.{u} : Sort u`: without the guard the
/// resident's `u` renames to `_mathverse_lp_0` and the two become
/// structurally identical.
#[test]
fn test_reserved_level_namespace_cannot_forge_a_match() {
    let shard = build_resident_probe_shard(
        "Dep",
        DeclKind::Axiom,
        &["u"],
        |w| {
            let forged = w.add_string("_mathverse_lp_0");
            let level = w.add_level(FlatLevel::param(forged));
            w.add_expr(FlatExpr::sort(level))
        },
        |_| {},
    );
    let lib = probe_library(&shard);

    let mut env = Environment::new();
    env.add_decl(clean_kernel::Declaration::Axiom {
        name: clean_kernel::Name::from_string("Dep"),
        level_params: vec![clean_kernel::Name::from_string("u")],
        type_: Expr::sort(Level::param(clean_kernel::Name::from_string("u"))),
    })
    .expect("resident registers");

    let candidate = premise_candidate(&lib, 0);
    let detail = detail_from_result(validate_dependency_loader_trust(
        &env,
        &candidate,
        &lib,
        TrustGate::Strict,
    ));
    assert!(
        detail.contains("reserved"),
        "the refusal must name the reserved-namespace guard: {detail}"
    );
}

/// Universe-parameter ARITY is decided from the header alone, before any
/// reconstruction, and a mismatch is never benign. (`List.zip` is the
/// measured real instance: 2 shard params against the prelude's 1.)
#[test]
fn test_resident_with_different_universe_arity_is_rejected() {
    // The shard row declares 0 universe parameters; the resident declares 1.
    let shard = build_resident_probe_shard(
        "Poly.def",
        DeclKind::Axiom,
        &[],
        |w| {
            let l0 = w.add_level(FlatLevel::zero());
            w.add_expr(FlatExpr::sort(l0))
        },
        |_| {},
    );
    let lib = probe_library(&shard);

    let mut env = Environment::new();
    env.add_decl(clean_kernel::Declaration::Axiom {
        name: clean_kernel::Name::from_string("Poly.def"),
        level_params: vec![clean_kernel::Name::from_string("u")],
        type_: Expr::sort(Level::zero()),
    })
    .expect("resident registers");

    let candidate = premise_candidate(&lib, 0);
    let detail = detail_from_result(validate_dependency_loader_trust(
        &env,
        &candidate,
        &lib,
        TrustGate::Strict,
    ));
    assert!(
        detail.contains("universe parameter"),
        "the refusal must name the universe-arity difference: {detail}"
    );
}

/// PERMISSIVENESS 1 — universe parameter NAMES and ORDER are irrelevant.
/// Shard `Dep.{a, b} : Sort a → Sort b`, resident `Dep.{v, u} : Sort v → Sort u`.
/// This is the real `Eq.ndrec` shape (shard `[u1, u2]`, prelude `[v, u]`);
/// comparing under the declared names would reject it.
#[test]
fn test_resident_with_renamed_universe_params_is_admitted() {
    let shard = build_resident_probe_shard(
        "Dep",
        DeclKind::Axiom,
        &["a", "b"],
        |w| {
            let na = w.add_string("a");
            let nb = w.add_string("b");
            let la = w.add_level(FlatLevel::param(na));
            let lb = w.add_level(FlatLevel::param(nb));
            let sa = w.add_expr(FlatExpr::sort(la));
            let sb = w.add_expr(FlatExpr::sort(lb));
            w.add_expr(FlatExpr::pi(0, sa, sb))
        },
        |_| {},
    );
    let lib = probe_library(&shard);

    let mut env = Environment::new();
    env.add_decl(clean_kernel::Declaration::Axiom {
        name: clean_kernel::Name::from_string("Dep"),
        level_params: vec![
            clean_kernel::Name::from_string("v"),
            clean_kernel::Name::from_string("u"),
        ],
        type_: Expr::pi(
            clean_kernel::BinderInfo::Default,
            Expr::sort(Level::param(clean_kernel::Name::from_string("v"))),
            Expr::sort(Level::param(clean_kernel::Name::from_string("u"))),
        ),
    })
    .expect("resident registers");

    let candidate = premise_candidate(&lib, 0);
    assert!(
        validate_dependency_loader_trust(&env, &candidate, &lib, TrustGate::Strict).is_ok(),
        "a universe-parameter RENAMING must not be read as a different declaration"
    );
}

/// PERMISSIVENESS 2 — the comparison is DEFINITIONAL, not syntactic.
/// Shard `Dep : Prop`, resident `Dep : Alias` where `Alias : Type := Prop`.
/// Structurally `Const Alias` and `Sort 0` are unrelated; one delta step
/// identifies them. This miniature stands in for the measured real case —
/// shard `Not p` against the prelude's `p → False` — which is worth 158/308
/// probes on the Mathlib population.
#[test]
fn test_resident_definitionally_equal_type_is_admitted() {
    let shard = build_resident_probe_shard(
        "Dep",
        DeclKind::Axiom,
        &[],
        |w| {
            let l0 = w.add_level(FlatLevel::zero());
            w.add_expr(FlatExpr::sort(l0))
        },
        |_| {},
    );
    let lib = probe_library(&shard);

    let mut env = Environment::new();
    env.add_decl(clean_kernel::Declaration::Definition {
        name: clean_kernel::Name::from_string("Alias"),
        level_params: vec![],
        type_: Expr::sort(Level::succ(Level::zero())),
        value: Expr::sort(Level::zero()),
        is_reducible: false,
    })
    .expect("`Alias : Type := Prop` registers");
    env.add_decl(clean_kernel::Declaration::Axiom {
        name: clean_kernel::Name::from_string("Dep"),
        level_params: vec![],
        type_: Expr::const_str("Alias"),
    })
    .expect("resident registers");

    assert_ne!(
        Expr::const_str("Alias"),
        Expr::sort(Level::zero()),
        "precondition: the two types are NOT structurally equal, so this test \
             genuinely exercises the definitional rung"
    );
    let candidate = premise_candidate(&lib, 0);
    assert!(
        validate_dependency_loader_trust(&env, &candidate, &lib, TrustGate::Strict).is_ok(),
        "a definitionally equal resident type must be admitted"
    );
}

/// Shard `Dep : outParam Prop` against resident `Dep : Prop`. `outParam` is
/// absent from the environment, so `is_def_eq` cannot delta it; the erasure
/// rung must — but ONLY because the shard's own `outParam` value is proved
/// here to be `fun α => α`. This is the measured `Membership` /
/// `Membership.mem` case, worth 7/308 probes.
#[test]
fn test_resident_under_verified_identity_gadget_is_admitted() {
    let shard = build_resident_probe_shard(
        "Dep",
        DeclKind::Axiom,
        &[],
        |w| {
            let l0 = w.add_level(FlatLevel::zero());
            let sort0 = w.add_expr(FlatExpr::sort(l0));
            let out = w.add_string("outParam");
            let out_ref = w.add_expr(FlatExpr::const_ref(out, u32::MAX));
            w.add_expr(FlatExpr::app(out_ref, sort0))
        },
        |w| add_gadget_row(w, "outParam", 1, 1),
    );
    let lib = probe_library(&shard);

    let mut env = Environment::new();
    env.add_decl(clean_kernel::Declaration::Axiom {
        name: clean_kernel::Name::from_string("Dep"),
        level_params: vec![],
        type_: Expr::sort(Level::zero()),
    })
    .expect("resident registers");
    assert!(
        env.get_const(&clean_kernel::Name::from_string("outParam"))
            .is_none(),
        "precondition: the gadget is NOT resident, which is what makes is_def_eq \
             unable to decide this on its own"
    );

    let candidate = premise_candidate(&lib, 0);
    assert!(
        validate_dependency_loader_trust(&env, &candidate, &lib, TrustGate::Strict).is_ok(),
        "an `outParam`-wrapped shard type must not be read as a different declaration"
    );
}

/// The erasure is EARNED, not assumed. Same shape as above, but the shard's
/// `outParam` is `fun a b => b` — not the identity on its first argument — so
/// nothing is erased and the dependency is rejected.
#[test]
fn test_gadget_erasure_requires_a_verified_identity_value() {
    let shard = build_resident_probe_shard(
        "Dep",
        DeclKind::Axiom,
        &[],
        |w| {
            let l0 = w.add_level(FlatLevel::zero());
            let sort0 = w.add_expr(FlatExpr::sort(l0));
            let out = w.add_string("outParam");
            let out_ref = w.add_expr(FlatExpr::const_ref(out, u32::MAX));
            w.add_expr(FlatExpr::app(out_ref, sort0))
        },
        // Two binders, returns the SECOND — the shard's `outParam` is not the
        // identity on its first argument.
        |w| add_gadget_row(w, "outParam", 2, 2),
    );
    let lib = probe_library(&shard);

    let mut env = Environment::new();
    env.add_decl(clean_kernel::Declaration::Axiom {
        name: clean_kernel::Name::from_string("Dep"),
        level_params: vec![],
        type_: Expr::sort(Level::zero()),
    })
    .expect("resident registers");

    let candidate = premise_candidate(&lib, 0);
    let detail = detail_from_result(validate_dependency_loader_trust(
        &env,
        &candidate,
        &lib,
        TrustGate::Strict,
    ));
    assert!(
        detail.contains("type substitution"),
        "a gadget whose shard value is not the identity must not be erased: {detail}"
    );
}

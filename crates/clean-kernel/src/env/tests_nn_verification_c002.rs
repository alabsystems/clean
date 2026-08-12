// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for C002: LayerNorm correlation firewall kernel theorem.
//!
//! Verifies that the C002 theorem (Declaration::Theorem) type-checks
//! through the kernel, confirming the proof term is valid.

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verification_c002()
        .expect("init_nn_verification_c002");
    env
}

fn count_pi_binders(mut expr: Expr) -> usize {
    let mut count = 0;
    while let ExprKind::Pi(_, _, body) = expr.kind() {
        count += 1;
        expr = body.as_ref().clone();
    }
    count
}

fn innermost_lam_body(mut expr: Expr) -> Expr {
    while let ExprKind::Lam(_, _, body) = expr.kind() {
        expr = body.as_ref().clone();
    }
    expr
}

fn expr_mentions_const(expr: &Expr, target: &str) -> bool {
    match expr.kind() {
        ExprKind::Const(name, _) => name.to_string() == target,
        ExprKind::App(f, a) => expr_mentions_const(f, target) || expr_mentions_const(a, target),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            expr_mentions_const(ty, target) || expr_mentions_const(body, target)
        }
        ExprKind::Let(_, ty, value, body, _) => {
            expr_mentions_const(ty, target)
                || expr_mentions_const(value, target)
                || expr_mentions_const(body, target)
        }
        ExprKind::Proj(_, _, e) | ExprKind::MData(_, e) => expr_mentions_const(e, target),
        ExprKind::Squash(e) => expr_mentions_const(e, target),
        _ => false,
    }
}

// =============================================================================
// Registration tests
// =============================================================================

#[test]
fn test_c002_layernorm_zonotope_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.C002.layernorm_zonotope"))
            .is_some(),
        "NNVerify.C002.layernorm_zonotope should be registered",
    );
}

#[test]
fn test_c002_layernorm_effective_jacobian_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string(
            "NNVerify.C002.layernorm_effective_jacobian"
        ))
        .is_some(),
        "NNVerify.C002.layernorm_effective_jacobian should be registered",
    );
}

#[test]
fn test_c002_layernorm_jacobian_rank_deficient_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string(
            "NNVerify.C002.layernorm_jacobian_rank_deficient"
        ))
        .is_some(),
        "NNVerify.C002.layernorm_jacobian_rank_deficient should be registered",
    );
}

#[test]
fn test_c002_correlation_firewall_core_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string(
            "NNVerify.C002.correlation_firewall_core"
        ))
        .is_some(),
        "NNVerify.C002.correlation_firewall_core should be registered",
    );
}

#[test]
fn test_c002_correlation_firewall_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.C002.correlation_firewall"))
            .is_some(),
        "NNVerify.C002.correlation_firewall should be registered",
    );
}

// =============================================================================
// Type-checking tests
// =============================================================================

#[test]
fn test_c002_layernorm_zonotope_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("NNVerify.C002.layernorm_zonotope"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&e)
        .expect("infer NNVerify.C002.layernorm_zonotope type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "layernorm_zonotope should have Pi type, got {:?}",
        ty.kind(),
    );
}

#[test]
fn test_c002_effective_jacobian_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("NNVerify.C002.layernorm_effective_jacobian"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&e)
        .expect("infer NNVerify.C002.layernorm_effective_jacobian type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "effective_jacobian should have Pi type",
    );
}

#[test]
fn test_c002_jacobian_rank_deficient_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("NNVerify.C002.layernorm_jacobian_rank_deficient"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&e)
        .expect("infer NNVerify.C002.layernorm_jacobian_rank_deficient type");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "rank_deficient should have Pi type",
    );
}

/// Pins that the `NNVerify.C002.correlation_firewall` theorem type still
/// type-checks to a Pi after the 2026-04-27 hypothesis wrapping.
///
/// The statement is now explicitly conditional on a local firewall equality
/// witness; the hypothesis-free equality remains represented by the
/// `layernorm_ibp_bridge` / retired `correlation_firewall_core` declarations.
#[test]
fn test_c002_correlation_firewall_theorem_type_checks() {
    let env = make_env();
    let thm = Expr::const_(
        Name::from_string("NNVerify.C002.correlation_firewall"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&thm)
        .expect("C002 correlation_firewall theorem type must infer");
    // The type should be universally quantified (starts with Pi)
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "C002 correlation_firewall theorem type should be Pi (universally \
         quantified), got {:?}",
        ty.kind(),
    );
}

/// `NNVerify.C002.correlation_firewall` is retired from the C002 domain
/// axiom row as a hypothesis-wrapped theorem. The proof consumes a local
/// firewall equality witness instead of wrapping `correlation_firewall_core`
/// or `layernorm_ibp_bridge`.
#[test]
fn test_c002_correlation_firewall_is_hypothesis_wrapped_theorem() {
    let env = make_env();
    let name = Name::from_string("NNVerify.C002.correlation_firewall");
    let ci = env
        .get_const(&name)
        .expect("C002 correlation_firewall should be registered");
    assert_eq!(
        ci.kind,
        ConstantKind::Theorem,
        "correlation_firewall should be the hypothesis-wrapped C002 headline \
         theorem, got {:?}",
        ci.kind,
    );
    assert!(
        ci.value.is_some(),
        "correlation_firewall theorem must carry the local-hypothesis proof value",
    );
}

#[test]
fn test_c002_correlation_firewall_type_has_local_hypothesis() {
    let env = make_env();
    let ci = env
        .get_const(&Name::from_string("NNVerify.C002.correlation_firewall"))
        .expect("C002 correlation_firewall should be registered");
    assert_eq!(
        count_pi_binders(ci.type_.clone()),
        7,
        "headline theorem should bind n, k, gamma, beta, eps, Z plus one \
         local firewall equality hypothesis",
    );
    assert!(
        expr_mentions_const(&ci.type_, "NNVerify.fresh_zonotope_from_hull"),
        "headline theorem type must still expose the firewall equality target",
    );
}

#[test]
fn test_c002_correlation_firewall_proof_uses_local_hypothesis_only() {
    let env = make_env();
    let ci = env
        .get_const(&Name::from_string("NNVerify.C002.correlation_firewall"))
        .expect("C002 correlation_firewall should be registered");
    let value = ci
        .value
        .clone()
        .expect("hypothesis-wrapped theorem should carry a proof value");
    assert!(
        !expr_mentions_const(&value, "NNVerify.C002.correlation_firewall_core"),
        "headline proof must not wrap the global C002 core axiom",
    );
    assert!(
        !expr_mentions_const(&value, "NNVerify.layernorm_ibp_bridge"),
        "headline proof must not wrap the global bridge axiom",
    );
    assert!(
        matches!(innermost_lam_body(value).kind(), ExprKind::BVar(0)),
        "headline proof should return its innermost local hypothesis",
    );
}

/// Guards the 2026-04-27 source retirement:
/// `NNVerify.C002.correlation_firewall_core` is a hypothesis-wrapped
/// `Declaration::Theorem`, not a live C002 Axiom.
///
/// Replaces the #3307/#3371 `test_c002_core_theorem_has_proof` test, which
/// pinned the opposite property. The former Theorem delegated to
/// `layernorm_ibp_bridge` which closed via `Eq.refl` over the reducible
/// `fresh_zonotope_from_hull` identity carrier; with the carrier flipped
/// to `Opaque` in #3639, the wrapper no longer type-checks under the honest
/// carrier. The 2026-04-27 version keeps that safeguard and returns local
/// firewall evidence instead.
#[test]
fn test_c002_correlation_firewall_core_is_hypothesis_wrapped_theorem() {
    let env = make_env();
    let core = Name::from_string("NNVerify.C002.correlation_firewall_core");
    let ci = env.get_const(&core).expect("core axiom should exist");
    assert_eq!(
        ci.kind,
        ConstantKind::Theorem,
        "correlation_firewall_core must be retired as a hypothesis-wrapped \
         Theorem, got {:?}",
        ci.kind,
    );
    let value = ci.value.clone().expect("hypothesis-wrapped core proof");
    assert!(
        !expr_mentions_const(&value, "NNVerify.layernorm_ibp_bridge"),
        "core proof must not wrap the global bridge axiom",
    );
    assert!(
        matches!(innermost_lam_body(value).kind(), ExprKind::BVar(0)),
        "core proof should return its innermost local hypothesis",
    );
}

/// Guards the 2026-04-27 source retirement: `NNVerify.C002.jac_rankdef_core`
/// is a hypothesis-wrapped `Declaration::Theorem`, not a live C002 Axiom.
///
/// Replaces the #3307 `test_c002_jac_rankdef_core_is_theorem` test, which
/// pinned a 5-step proof composition that only type-checked because
/// `mean_projection n` δ-reduced to `ones_matrix n` (placeholder-body
/// MASQUERADE per `designs/2026-04-19-demasquerade-cxxx-pattern.md` Rule
/// M2). #3587 closed that path by flipping `NNVerify.mean_projection`
/// from reducible `Definition` (#3458) to `Declaration::Opaque`; the old
/// proof no longer type-checks under the honest carrier. The 2026-04-27
/// version keeps that safeguard and returns local rank-deficiency evidence.
#[test]
fn test_c002_jac_rankdef_core_is_hypothesis_wrapped_theorem() {
    let env = make_env();
    let jrc = Name::from_string("NNVerify.C002.jac_rankdef_core");
    let ci = env.get_const(&jrc).expect("jac_rankdef_core should exist");
    assert_eq!(
        ci.kind,
        ConstantKind::Theorem,
        "jac_rankdef_core must be retired as a hypothesis-wrapped Theorem, \
         got {:?}",
        ci.kind,
    );
    let value = ci.value.clone().expect("hypothesis-wrapped rank proof");
    assert!(
        !expr_mentions_const(&value, "NNVerify.C002.jac_rankdef_core"),
        "rank proof must not recursively wrap the old global core claim",
    );
    assert!(
        matches!(innermost_lam_body(value).kind(), ExprKind::BVar(0)),
        "rank proof should return its innermost local hypothesis",
    );
}

/// Verify firewall_algebraic has been eliminated (#3307).
/// The former axiom is replaced by a constructive proof in
/// the retired correlation_firewall_core path via layernorm_ibp_bridge.
#[test]
fn test_c002_firewall_algebraic_eliminated() {
    let env = make_env();
    let fa = Name::from_string("NNVerify.C002.firewall_algebraic");
    assert!(
        env.get_const(&fa).is_none(),
        "firewall_algebraic should no longer exist — eliminated by #3307",
    );
}

/// Verify that definitions (layernorm_zonotope, eff_jacobian) have values.
#[test]
fn test_c002_definitions_have_values() {
    let env = make_env();
    let lz = Name::from_string("NNVerify.C002.layernorm_zonotope");
    let ci = env.get_const(&lz).expect("layernorm_zonotope should exist");
    assert!(
        ci.value.is_some(),
        "layernorm_zonotope should be a Definition with a value",
    );
    let ej = Name::from_string("NNVerify.C002.layernorm_effective_jacobian");
    let ci = env.get_const(&ej).expect("eff_jacobian should exist");
    assert!(
        ci.value.is_some(),
        "layernorm_effective_jacobian should be a Definition with a value",
    );
}

/// Guards the 2026-04-27 source retirement:
/// `NNVerify.C002.layernorm_jacobian_rank_deficient` is a
/// hypothesis-wrapped `Declaration::Theorem`, not a live C002 Axiom.
///
/// Replaces the `test_c002_jac_rankdef_theorem_has_proof` test. The
/// former proof term was a lambda that delegated to `jac_rankdef_core`;
/// once the core lost its constructive proof (same #3587 demasquerade),
/// this downstream theorem lost its carrier. The 2026-04-27 version keeps
/// the claim explicit as local rank-deficiency evidence.
#[test]
fn test_c002_layernorm_jac_rankdef_is_hypothesis_wrapped_theorem() {
    let env = make_env();
    let name = Name::from_string("NNVerify.C002.layernorm_jacobian_rank_deficient");
    let ci = env
        .get_const(&name)
        .expect("jac_rankdef theorem should exist");
    assert_eq!(
        ci.kind,
        ConstantKind::Theorem,
        "layernorm_jacobian_rank_deficient must be retired as a \
         hypothesis-wrapped Theorem, got {:?}",
        ci.kind,
    );
    let value = ci.value.clone().expect("hypothesis-wrapped rank proof");
    assert!(
        !expr_mentions_const(&value, "NNVerify.C002.jac_rankdef_core"),
        "rank proof must not wrap the global jac_rankdef_core claim",
    );
    assert!(
        matches!(innermost_lam_body(value).kind(), ExprKind::BVar(0)),
        "rank proof should return its innermost local hypothesis",
    );
}

/// Verify supporting axioms are registered.
#[test]
fn test_c002_supporting_axioms_registered() {
    let env = make_env();
    let names = [
        "NNVerify.scalar_mat_mul",
        "NNVerify.Zonotope.sigma",
        "NNVerify.Zonotope.center",
        "NNVerify.Zonotope.generators",
    ];
    for name in &names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{} should be registered as supporting axiom",
            name,
        );
    }
}

// =============================================================================
// Idempotency
// =============================================================================

#[test]
fn test_c002_idempotent() {
    let mut env = Environment::new();
    env.init_nn_verification_c002().expect("first init");
    env.init_nn_verification_c002()
        .expect("second init should be idempotent");
}

// =============================================================================
// Naming convention
// =============================================================================

#[test]
fn test_c002_naming_convention() {
    let env = make_env();
    let names = [
        "NNVerify.C002.layernorm_zonotope",
        "NNVerify.C002.layernorm_effective_jacobian",
        "NNVerify.C002.layernorm_jacobian_rank_deficient",
        "NNVerify.C002.correlation_firewall_core",
        "NNVerify.C002.correlation_firewall",
        "NNVerify.C002.jac_rankdef_core",
    ];
    for name in &names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{} should be registered",
            name,
        );
        assert!(
            name.starts_with("NNVerify.C002."),
            "all C002 names must use NNVerify.C002. prefix: {}",
            name,
        );
    }
}

// =============================================================================
// Dependency chain verification
// =============================================================================

/// Verify that C002 correctly depends on zonotope infrastructure.
#[test]
fn test_c002_has_zonotope_deps() {
    let env = make_env();
    // These should exist from init_nn_verify_zonotope
    assert!(
        env.get_const(&Name::from_string("NNVerify.Zonotope"))
            .is_some(),
        "Zonotope type should exist from dependencies",
    );
    assert!(
        env.get_const(&Name::from_string("NNVerify.Zonotope.to_ibp"))
            .is_some(),
        "Zonotope.to_ibp should exist from dependencies",
    );
}

/// Verify that C002 correctly depends on LayerNorm infrastructure.
#[test]
fn test_c002_has_layernorm_deps() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.LayerNorm.forward"))
            .is_some(),
        "LayerNorm.forward should exist from crown_layernorm dependency",
    );
}

/// Verify that C002 correctly depends on matrix rank infrastructure.
#[test]
fn test_c002_has_matrix_rank_deps() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("NNVerify.interval_hull_width"))
            .is_some(),
        "interval_hull_width should exist from matrix_rank dependency",
    );
    assert!(
        env.get_const(&Name::from_string("NNVerify.fresh_zonotope_from_hull"))
            .is_some(),
        "fresh_zonotope_from_hull should exist from matrix_rank dependency",
    );
    assert!(
        env.get_const(&Name::from_string("NNVerify.matrix_rank"))
            .is_some(),
        "matrix_rank should exist from matrix_rank dependency",
    );
}

// =============================================================================
// Proof quality / axiom dependency tests (#3372)
// =============================================================================

/// Verify scalar_mat_mul is now a Definition (not an Axiom).
///
/// Part of #3372: scalar_mat_mul was upgraded from Axiom to Definition
/// with constructive value `fun m n s A i j => Rat.mul s (A i j)`.
#[test]
fn test_c002_scalar_mat_mul_is_definition() {
    let env = make_env();
    let name = Name::from_string("NNVerify.scalar_mat_mul");
    let ci = env.get_const(&name).expect("scalar_mat_mul should exist");
    assert!(
        ci.value.is_some(),
        "scalar_mat_mul should be a Definition with a value (not an Axiom). \
         Part of #3372.",
    );
}

/// Verify nn_vec_variance is now a Definition (not an Axiom).
///
/// Part of #3372: nn_vec_variance was upgraded from Axiom to Definition
/// with constructive value computing variance via Fin.sum and Rat ops.
#[test]
fn test_c002_nn_vec_variance_is_definition() {
    let env = make_env();
    let name = Name::from_string("NNVerify.nn_vec_variance");
    let ci = env.get_const(&name).expect("nn_vec_variance should exist");
    assert!(
        ci.value.is_some(),
        "nn_vec_variance should be a Definition with a value (not an Axiom). \
         Part of #3372.",
    );
}

/// Verify scalar_mat_mul and nn_vec_variance are NOT in the C002 axiom deps.
///
/// After #3372, these are Definitions and should not appear as domain-specific
/// axioms in the transitive dependency chain of the C002 firewall theorem.
#[test]
fn test_c002_axiom_deps_exclude_eliminated_axioms() {
    let env = make_env();
    let name = Name::from_string("NNVerify.C002.correlation_firewall");
    let deps = env.axiom_deps(&name).expect("axiom_deps should work");
    let dep_strings: Vec<String> = deps.iter().map(|n| n.to_string()).collect();

    assert!(
        !dep_strings.contains(&"NNVerify.scalar_mat_mul".to_string()),
        "scalar_mat_mul should NOT be in C002 axiom deps after #3372. \
         Current deps: {:?}",
        dep_strings,
    );
    assert!(
        !dep_strings.contains(&"NNVerify.nn_vec_variance".to_string()),
        "nn_vec_variance should NOT be in C002 axiom deps after #3372. \
         Current deps: {:?}",
        dep_strings,
    );
}

/// Guards the #3639 Branch A demasquerade: `NNVerify.layernorm_ibp_bridge`
/// is a `Declaration::Axiom`.
///
/// Replaces the #3371 `test_c002_layernorm_ibp_bridge_is_theorem` test
/// (which pinned the opposite property: a Theorem with proof value, not a
/// dep of the firewall). The former Theorem's `Eq.refl`-over-identity-carrier
/// proof only type-checked because `NNVerify.fresh_zonotope_from_hull` was
/// a reducible `Declaration::Definition` whose body was the identity
/// `fun (n : Nat) (B : IntervalBounds n) => B`; the kernel δ-unfolded
/// `fresh_zonotope_from_hull n B → B` during `def_eq`, making the bridge
/// type collapse to the reflexive `ihw n B = ihw n B`. #3639 closed that
/// path by flipping `fresh_zonotope_from_hull` to `Declaration::Opaque`;
/// the proof no longer type-checks, so the bridge demoted to `Axiom`.
///
/// `correlation_firewall` itself was later retired from the direct C002
/// axiom row as a hypothesis-wrapped theorem. The bridge remains unwrapped
/// and hypothesis-free, so it stays an honest Axiom.
#[test]
fn test_c002_layernorm_ibp_bridge_is_axiom_honest_demotion() {
    let env = make_env();
    let bridge_name = Name::from_string("NNVerify.layernorm_ibp_bridge");
    let ci = env
        .get_const(&bridge_name)
        .expect("layernorm_ibp_bridge should exist");
    assert_eq!(
        ci.kind,
        ConstantKind::Axiom,
        "#3639 Branch A: layernorm_ibp_bridge must be Axiom (honest \
         MASQUERADE demotion — δ-reduction path `fresh_zonotope_from_hull n B \
         → B` closed), got {:?}",
        ci.kind,
    );
    assert!(
        ci.value.is_none(),
        "#3639 Branch A: layernorm_ibp_bridge Axiom must not carry a proof \
         value",
    );
}

/// Guards the #3639 Branch A carrier co-demotion:
/// `NNVerify.fresh_zonotope_from_hull` is a `Declaration::Opaque`, not a
/// reducible `Declaration::Definition`.
///
/// Replaces the #3371 `test_c002_fresh_zonotope_from_hull_is_definition`
/// test (which pinned the opposite property). The stored body
/// (`fun (n : Nat) (B : IntervalBounds n) => B`) is unchanged; only the
/// declaration kind flipped from `Definition { is_reducible: true }` to
/// `Declaration::Opaque` per `designs/2026-04-19-demasquerade-cxxx-pattern.md`
/// Rule M2 (identity-on-argument carrier) + Rule M1 (alias-collapse via
/// reducible Definition). Opaques are NOT δ-unfolded during `def_eq`, so
/// the alias-collapse path that let `layernorm_ibp_bridge` close via
/// `Eq.refl` is closed. Mirrors the #3587 `mean_projection` co-demotion
/// pattern.
#[test]
fn test_c002_fresh_zonotope_from_hull_is_opaque_not_reducible_definition() {
    let env = make_env();
    let name = Name::from_string("NNVerify.fresh_zonotope_from_hull");
    let ci = env
        .get_const(&name)
        .expect("fresh_zonotope_from_hull should exist");
    assert_eq!(
        ci.kind,
        ConstantKind::Opaque,
        "#3639 Branch A: fresh_zonotope_from_hull must be Opaque (closes \
         the δ-reduction path `fresh_zonotope_from_hull n B → B` that let \
         `layernorm_ibp_bridge` masquerade as proven via Eq.refl), got {:?}",
        ci.kind,
    );
    assert!(
        !ci.is_reducible,
        "#3639 Branch A: fresh_zonotope_from_hull Opaque must NOT be \
         reducible; reducibility would re-open the δ-reduction MASQUERADE \
         path",
    );
    // Opaques carry a body (unlike Axioms); body must still be present and
    // unchanged from #3371 (`fun n B => B`).
    assert!(
        ci.value.is_some(),
        "#3639 fresh_zonotope_from_hull Opaque should still carry its \
         identity body `fun n B => B` (#3371 body preserved; only the \
         declaration kind flipped)",
    );
}

/// Pin the `fresh_zonotope_from_hull` Opaque-set membership after #3639.
///
/// Guards against silent regressions that re-promote it to a reducible
/// `Definition` and re-open the δ-reduction MASQUERADE path.
#[test]
fn test_c002_fresh_zonotope_from_hull_in_opaque_set() {
    let env = make_env();
    let opaque_names: Vec<String> = env
        .constants()
        .filter(|c| c.kind == ConstantKind::Opaque)
        .map(|c| c.name.to_string())
        .collect();
    assert!(
        opaque_names.contains(&"NNVerify.fresh_zonotope_from_hull".to_string()),
        "#3639 Branch A: NNVerify.fresh_zonotope_from_hull MUST be an \
         Opaque (co-demoted from reducible Definition per #3371). \
         Current Opaque set: {:?}",
        opaque_names,
    );
}

/// Gate that the non-C002 bridge Axiom and retired C002 core theorem types
/// still infer to Pi under the honest (Opaque) carrier.
#[test]
fn test_c002_firewall_bridge_and_core_types_still_type_check() {
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    for name in [
        "NNVerify.layernorm_ibp_bridge",
        "NNVerify.C002.correlation_firewall_core",
    ] {
        let e = Expr::const_(Name::from_string(name), vec![]);
        let ty = tc
            .infer_type(&e)
            .unwrap_or_else(|_| panic!("{} type must infer", name));
        assert!(
            matches!(ty.kind(), ExprKind::Pi(..)),
            "{} type should be Pi, got {:?}",
            name,
            ty.kind(),
        );
    }
}

/// Verify identity_matrix is now a Definition (not an Axiom).
///
/// Part of #3372: identity_matrix was upgraded from Axiom to Definition
/// with constructive value using Kronecker delta:
/// `fun n i j => @ite Rat (i = j) (instDecidableEqFin n i j) 1 0`
#[test]
fn test_c002_identity_matrix_is_definition() {
    let env = make_env();
    let name = Name::from_string("NNVerify.identity_matrix");
    let ci = env.get_const(&name).expect("identity_matrix should exist");
    assert!(
        ci.value.is_some(),
        "identity_matrix should be a Definition with a value (not an Axiom). \
         Part of #3372.",
    );
    // Verify it is classified as a Definition, not an Axiom
    assert_eq!(
        ci.kind,
        ConstantKind::Definition,
        "identity_matrix should be ConstantKind::Definition. Part of #3372.",
    );
}

/// Verify matrix_sub is now a Definition (not an Axiom).
///
/// Part of #3372: matrix_sub was upgraded from Axiom to Definition
/// with constructive value: `fun m n A B i j => Rat.sub (A i j) (B i j)`
#[test]
fn test_c002_matrix_sub_is_definition() {
    let env = make_env();
    let name = Name::from_string("NNVerify.matrix_sub");
    let ci = env.get_const(&name).expect("matrix_sub should exist");
    assert!(
        ci.value.is_some(),
        "matrix_sub should be a Definition with a value (not an Axiom). \
         Part of #3372.",
    );
    assert_eq!(
        ci.kind,
        ConstantKind::Definition,
        "matrix_sub should be ConstantKind::Definition. Part of #3372.",
    );
}

/// Guards the #3587 Branch A demasquerade: `NNVerify.mean_projection` is
/// an `Opaque` declaration, NOT a reducible `Definition`.
///
/// Replaces the #3458 `test_c002_mean_projection_is_reducible_definition`
/// test (which pinned the opposite property). The stored body
/// (`fun n => ones_matrix n`) is unchanged; only the declaration kind
/// flipped back from `Definition { is_reducible: true }` to
/// `Declaration::Opaque`.
///
/// This is the load-bearing half of Branch A. If `mean_projection` stays
/// reducible, the 5-step proof of `jac_rankdef_core` could once again
/// type-check because the kernel would δ-unfold
/// `mean_projection n → ones_matrix n`, making the axiom
/// `identity_minus_projection_rank` discharge the goal on the wrong
/// matrix (`J_n` instead of the true centering matrix `(1/n) * J_n`).
/// Opaques are not δ-unfolded during `def_eq`, so this test pins the
/// kernel property that keeps the demasquerade intact. See
/// `designs/2026-04-19-demasquerade-cxxx-pattern.md` Rule M2
/// (placeholder-body carrier), and precedents #3579 C012 `single_lp_form`
/// and #3578 C006 `ln_variance_lower_bound`.
#[test]
fn test_c002_mean_projection_is_opaque_not_reducible_definition() {
    let env = make_env();
    let name = Name::from_string("NNVerify.mean_projection");
    let ci = env.get_const(&name).expect("mean_projection should exist");
    assert_eq!(
        ci.kind,
        ConstantKind::Opaque,
        "#3587 Branch A: mean_projection must be Opaque (closes the \
         δ-reduction path `mean_projection n → ones_matrix n` that let \
         `jac_rankdef_core` masquerade as proven), got {:?}",
        ci.kind,
    );
    assert!(
        !ci.is_reducible,
        "#3587 Branch A: mean_projection Opaque must NOT be reducible; \
         reducibility would re-open the δ-reduction MASQUERADE path",
    );
    // The stored body is unchanged from #3458 (`fun n => ones_matrix n`).
    // Opaques carry bodies (unlike Axioms); confirm it is still present.
    assert!(
        ci.value.is_some(),
        "#3587 mean_projection Opaque should still carry its placeholder \
         `fun n => ones_matrix n` body (#3458 body preserved; only the \
         declaration kind flipped)",
    );
}

/// Pin the `mean_projection` Opaque-set membership in the C002 environment
/// post-#3587.
///
/// After #3587, `NNVerify.mean_projection` MUST appear among
/// `ConstantKind::Opaque` declarations in a freshly initialized C002
/// environment. Guards against silent regressions that re-promote it to
/// a reducible `Definition` and re-open the δ-reduction MASQUERADE path.
#[test]
fn test_c002_mean_projection_in_opaque_set() {
    let env = make_env();
    let opaque_names: Vec<String> = env
        .constants()
        .filter(|c| c.kind == ConstantKind::Opaque)
        .map(|c| c.name.to_string())
        .collect();
    assert!(
        opaque_names.contains(&"NNVerify.mean_projection".to_string()),
        "#3587 Branch A: NNVerify.mean_projection MUST be an Opaque \
         (re-demoted from reducible Definition per #3458). \
         Current Opaque set: {:?}",
        opaque_names,
    );
}

/// Kernel-validation gate for the `mean_projection` Opaque (#3587).
///
/// Runs `TypeChecker::infer_type` on the stored value and asserts `is_def_eq`
/// with the declared type. This exercises the same check that `add_decl`
/// runs internally during `init_nn_verification_c002`; if it did not hold,
/// the `make_env()` helper would have panicked. Opaques carry a body
/// (unlike Axioms), and that body must still type-check at its declared
/// type — only δ-reduction is blocked. The explicit assertion pins the
/// post-re-demotion shape so future refactors of
/// `nn_verify_matrix_rank_defs::build_mean_projection_value` / `_type`
/// cannot silently diverge.
#[test]
fn test_c002_mean_projection_kernel_validates_via_add_decl() {
    let env = make_env();
    let name = Name::from_string("NNVerify.mean_projection");
    let ci = env.get_const(&name).expect("mean_projection should exist");
    let value = ci
        .value
        .clone()
        .expect("mean_projection Opaque carries its placeholder body");
    let declared_type = ci.type_.clone();

    let tc = TypeChecker::new(&env);
    let inferred = tc
        .infer_type(&value)
        .expect("kernel should infer type of mean_projection Opaque body");
    assert!(
        tc.is_def_eq(&inferred, &declared_type),
        "kernel def_eq gate: inferred type of mean_projection Opaque body \
         must match declared type. Part of #3587.",
    );
}

/// Type-checks guard: the retired `jac_rankdef_core` and
/// `layernorm_jacobian_rank_deficient` theorems still carry Pi types so
/// downstream callers that `infer_type` through the declaration continue
/// to type-check.
#[test]
fn test_c002_jac_rankdef_theorems_still_type_check() {
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    for theorem_name in &[
        "NNVerify.C002.jac_rankdef_core",
        "NNVerify.C002.layernorm_jacobian_rank_deficient",
    ] {
        let e = Expr::const_(Name::from_string(theorem_name), vec![]);
        let ty = tc
            .infer_type(&e)
            .unwrap_or_else(|_| panic!("{} theorem should infer a type", theorem_name));
        assert!(
            matches!(ty.kind(), ExprKind::Pi(..)),
            "{} theorem type should be Pi (universally quantified), got {:?}",
            theorem_name,
            ty.kind(),
        );
    }
}

#[test]
fn test_c002_has_no_live_domain_axioms_after_retirement() {
    let env = make_env();
    let live_c002_axioms: Vec<String> = env
        .constants()
        .filter(|c| c.kind == ConstantKind::Axiom)
        .map(|c| c.name.to_string())
        .filter(|name| name.starts_with("NNVerify.C002."))
        .collect();
    assert!(
        live_c002_axioms.is_empty(),
        "C002 should have no live domain axioms after hypothesis wrapping; \
         got {live_c002_axioms:?}",
    );
}

/// Verify that identity_matrix, matrix_sub, and mean_projection are NOT in C002 axiom deps.
///
/// After #3372, these are Definitions/Opaques (not Axioms) and should NOT appear
/// as domain-specific axioms in the transitive dependency chain.
#[test]
fn test_c002_axiom_deps_exclude_infrastructure_conversions() {
    let env = make_env();
    let name = Name::from_string("NNVerify.C002.correlation_firewall");
    let deps = env.axiom_deps(&name).expect("axiom_deps should work");
    let dep_strings: Vec<String> = deps.iter().map(|n| n.to_string()).collect();

    assert!(
        !dep_strings.contains(&"NNVerify.identity_matrix".to_string()),
        "identity_matrix should NOT be in C002 axiom deps after #3372. \
         Current deps: {:?}",
        dep_strings,
    );
    assert!(
        !dep_strings.contains(&"NNVerify.matrix_sub".to_string()),
        "matrix_sub should NOT be in C002 axiom deps after #3372. \
         Current deps: {:?}",
        dep_strings,
    );
    assert!(
        !dep_strings.contains(&"NNVerify.mean_projection".to_string()),
        "mean_projection should NOT be in C002 axiom deps after #3372. \
         Current deps: {:?}",
        dep_strings,
    );
}

/// Report the proof-quality classification of
/// `NNVerify.C002.correlation_firewall` after the 2026-04-27
/// hypothesis-wrapped retirement.
///
/// The theorem returns a local hypothesis and does not reference the old
/// C002 global axioms. `proof_quality` still reports shared non-C002 type
/// dependencies (`interval_hull_width`, `matrix_mul`), which is expected:
/// this retirement removes one C002-prefix domain axiom, not every shared
/// NNVerify infrastructure axiom in the statement surface.
#[test]
fn test_c002_proof_quality_report() {
    let env = make_env();
    let name = Name::from_string("NNVerify.C002.correlation_firewall");
    let quality = env.proof_quality(&name).expect("proof_quality should work");
    let quality_axioms: Vec<String> = match &quality {
        crate::env::axiom_audit::ProofQuality::AxiomDependent { axioms, .. } => {
            axioms.iter().map(|n| n.to_string()).collect()
        }
        other => panic!(
            "hypothesis-wrapped correlation_firewall should be axiom-dependent \
             only through shared non-C002 type dependencies; got {other:?}",
        ),
    };
    assert!(
        quality_axioms
            .iter()
            .all(|n| !n.starts_with("NNVerify.C002.")),
        "headline theorem must not depend on C002-prefix axioms; got {quality_axioms:?}",
    );
    assert!(
        !quality_axioms.contains(&"NNVerify.layernorm_ibp_bridge".to_string()),
        "headline theorem must not depend on the global bridge axiom; got {quality_axioms:?}",
    );

    // Sanity: the prior-wave eliminated C002 axioms (#3371/#3372) must still
    // be absent from the type-signature axiom-dependency set of the retired
    // theorem. This guards against a Definition/Opaque/regression reintroducing
    // an axiom dependency.
    let deps = env.axiom_deps(&name).expect("axiom_deps should work");
    let dep_strings: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
    for eliminated in [
        "NNVerify.scalar_mat_mul",
        "NNVerify.nn_vec_variance",
        "NNVerify.fresh_zonotope_from_hull",
        "NNVerify.layernorm_ibp_bridge",
        "NNVerify.C002.correlation_firewall_core",
    ] {
        assert!(
            !dep_strings.contains(&eliminated.to_string()),
            "{} should remain outside C002 axiom deps (prior-wave \
             Definition/Opaque status must not regress). Current deps: {:?}",
            eliminated,
            dep_strings,
        );
    }
    eprintln!(
        "C002 correlation_firewall (hypothesis-wrapped theorem) axiom deps \
         ({}): {:?}",
        dep_strings.len(),
        dep_strings,
    );
}

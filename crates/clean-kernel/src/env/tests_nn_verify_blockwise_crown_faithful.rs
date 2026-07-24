// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Discriminator tests for the faithful `Block.monolithic_crown_faithful`
//! carrier (#3494).
//!
//! These tests assert that the faithful carrier is **semantically live**:
//! its output depends on both `k` and `B`, so theorems stated over it
//! cannot close by `Eq.refl` between alias-collapsed constants. The
//! pattern mirrors the design in
//! `designs/2026-04-19-demasquerade-cxxx-pattern.md` → "Template:
//! faithful abstract-domain carrier" → "Discriminator property".
//!
//! See `nn_verify_blockwise_crown_ext_carriers.rs` for the faithful
//! carrier registration.

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_blockwise_crown_ext()
        .expect("init_nn_verify_blockwise_crown_ext");
    env
}

/// Returns true iff `expr` (or any of its subexpressions) references
/// `target_const` as a `Const` head. Conservative walk over the core
/// expression shapes; matches the helper used in the T22 tests.
fn expr_references_const(expr: &Expr, target_const: &str) -> bool {
    match expr.kind() {
        ExprKind::Const(name, _) => name.to_string() == target_const,
        ExprKind::App(f, a) => {
            expr_references_const(f, target_const) || expr_references_const(a, target_const)
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            expr_references_const(ty, target_const) || expr_references_const(body, target_const)
        }
        ExprKind::Let(_, ty, val, body, _nondep) => {
            expr_references_const(ty, target_const)
                || expr_references_const(val, target_const)
                || expr_references_const(body, target_const)
        }
        ExprKind::Proj(_, _, inner) => expr_references_const(inner, target_const),
        ExprKind::MData(_, inner) => expr_references_const(inner, target_const),
        _ => false,
    }
}

// =============================================================================
// Registration + shape
// =============================================================================

#[test]
fn test_monolithic_crown_faithful_registered() {
    let env = make_env();
    let ci = env
        .get_const(&Name::from_string(
            "NNVerify.Block.monolithic_crown_faithful",
        ))
        .expect("monolithic_crown_faithful should be registered");
    assert_eq!(
        ci.kind,
        ConstantKind::Definition,
        "faithful carrier must be a Declaration::Definition (reducible)"
    );
    assert!(
        ci.value.is_some(),
        "faithful carrier must carry a body (reducible Definition)"
    );
}

#[test]
fn test_monolithic_crown_faithful_body_uses_nat_rec() {
    // #3494: the body must reference Nat.rec (structural recursion on k).
    // A body like `fun d k B => B` or `fun d k B => zero_ib d` would
    // trivially collapse.
    let env = make_env();
    let ci = env
        .get_const(&Name::from_string(
            "NNVerify.Block.monolithic_crown_faithful",
        ))
        .expect("monolithic_crown_faithful should exist");
    let value = ci
        .value
        .as_ref()
        .expect("monolithic_crown_faithful should be a Definition with a value");
    assert!(
        expr_references_const(value, "Nat.rec"),
        "faithful carrier body must reference Nat.rec — the body is \
         supposed to pattern-match on k via structural recursion",
    );
    // And must reference IntervalBounds.mk via the step-case zero_ib builder.
    assert!(
        expr_references_const(value, "NNVerify.IntervalBounds.mk"),
        "faithful carrier body must construct zero_ib via IntervalBounds.mk \
         in the step case",
    );
}

#[test]
fn test_blockwise_crown_equiv_faithful_registered() {
    let env = make_env();
    let ci = env
        .get_const(&Name::from_string(
            "NNVerify.Block.blockwise_crown_equiv_faithful",
        ))
        .expect("blockwise_crown_equiv_faithful should be registered");
    assert_eq!(
        ci.kind,
        ConstantKind::Theorem,
        "blockwise_crown_equiv_faithful must be Declaration::Theorem"
    );
    assert!(
        ci.value.is_some(),
        "blockwise_crown_equiv_faithful must have a proof value"
    );
}

// =============================================================================
// Discriminator: the faithful carrier is NOT identity-on-argument and NOT
// constant. Its WHNF at different inputs yields different normal forms.
// =============================================================================

/// Construct `@Block.monolithic_crown_faithful d k B` as a kernel Expr.
fn mcf_app(d: Expr, k: Expr, b: Expr) -> Expr {
    let mcf = Expr::const_(
        Name::from_string("NNVerify.Block.monolithic_crown_faithful"),
        vec![],
    );
    Expr::apps(mcf, [d, k, b])
}

/// A symbolic `IntervalBounds` constructor application — distinct from
/// `zero_ib d` because the lower/upper vectors differ.
fn sym_bounds_one() -> Expr {
    // @IntervalBounds.mk 1 (fun _ => Rat.one) (fun _ => Rat.one) valid
    // We only need the head constant and dim for WHNF comparison; the
    // validity proof shape doesn't matter for the discriminator test
    // because WHNF will keep it under the `mk` head as-is.
    let ib_mk = Expr::const_(Name::from_string("NNVerify.IntervalBounds.mk"), vec![]);
    let nat_one = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
    );
    let rat_one = Expr::const_(Name::from_string("Rat.one"), vec![]);
    let rat_le_refl = Expr::const_(Name::from_string("Rat.le_refl"), vec![]);
    let fin_1 = Expr::app(
        Expr::const_(Name::from_string("Fin"), vec![]),
        nat_one.clone(),
    );
    // fun _ : Fin 1 => Rat.one
    let const_one_vec = Expr::lam(
        crate::expr::BinderInfo::Default,
        fin_1.clone(),
        rat_one.clone(),
    );
    // fun _ : Fin 1 => Rat.le_refl Rat.one
    // (Note: not a real proof of lower ≤ upper under the IB invariant,
    //  but for WHNF shape comparison it's only the constructor head that
    //  matters. The env's `add_decl` never re-checks this body during
    //  WHNF — WHNF is applied to pre-built terms.)
    let valid_proof = Expr::lam(
        crate::expr::BinderInfo::Default,
        fin_1,
        Expr::app(rat_le_refl, rat_one),
    );
    Expr::apps(
        ib_mk,
        [nat_one, const_one_vec.clone(), const_one_vec, valid_proof],
    )
}

/// The zero `IntervalBounds 1` value — two `fun _ => Rat.zero` vectors.
fn zero_bounds_one() -> Expr {
    let ib_mk = Expr::const_(Name::from_string("NNVerify.IntervalBounds.mk"), vec![]);
    let nat_one = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
    );
    let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
    let rat_le_refl = Expr::const_(Name::from_string("Rat.le_refl"), vec![]);
    let fin_1 = Expr::app(
        Expr::const_(Name::from_string("Fin"), vec![]),
        nat_one.clone(),
    );
    let const_zero_vec = Expr::lam(
        crate::expr::BinderInfo::Default,
        fin_1.clone(),
        rat_zero.clone(),
    );
    let valid_proof = Expr::lam(
        crate::expr::BinderInfo::Default,
        fin_1,
        Expr::app(rat_le_refl, rat_zero),
    );
    Expr::apps(
        ib_mk,
        [nat_one, const_zero_vec.clone(), const_zero_vec, valid_proof],
    )
}

#[test]
fn test_discriminator_k_zero_returns_input() {
    // At k=0, the carrier must iota-reduce to its input B (not to zero).
    // So `mcf 1 0 sym_B` and `sym_B` should have the same WHNF.
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let nat_one = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
    );
    let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let b_sym = sym_bounds_one();
    let applied = mcf_app(nat_one, nat_zero, b_sym.clone());
    let whnf_applied = tc.whnf(&applied);
    let whnf_input = tc.whnf(&b_sym);
    assert_eq!(
        whnf_applied, whnf_input,
        "at k=0 the faithful carrier must WHNF-reduce to its input B \
         (was: {:?}, expected: {:?})",
        whnf_applied, whnf_input,
    );
}

#[test]
fn test_discriminator_k_zero_discriminates_on_input() {
    // At k=0, two distinct inputs must give two distinct outputs.
    // `mcf 1 0 sym_B` != `mcf 1 0 zero_B` after WHNF.
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let nat_one = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
    );
    let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let b_sym = sym_bounds_one();
    let b_zero = zero_bounds_one();
    let whnf_sym = tc.whnf(&mcf_app(nat_one.clone(), nat_zero.clone(), b_sym));
    let whnf_zero = tc.whnf(&mcf_app(nat_one, nat_zero, b_zero));
    assert_ne!(
        whnf_sym, whnf_zero,
        "MASQUERADE NOT CLOSED: at k=0 the carrier returns the same \
         output for distinct inputs — it is still identity-on-carrier \
         or zero-constant. WHNF(mcf 1 0 sym)={:?}, WHNF(mcf 1 0 zero)={:?}",
        whnf_sym, whnf_zero,
    );
}

#[test]
fn test_discriminator_k_positive_discriminates_on_k() {
    // The outputs at k=0 and k=1 must differ: at k=0 we get B, at k=1
    // we get zero_ib — two syntactically different normal forms for a
    // symbolic input B (assuming B != zero_ib).
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let nat_one_dim = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
    );
    let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    let k_one = Expr::app(nat_succ, nat_zero.clone());
    let b_sym = sym_bounds_one();
    let whnf_k0 = tc.whnf(&mcf_app(nat_one_dim.clone(), nat_zero, b_sym.clone()));
    let whnf_k1 = tc.whnf(&mcf_app(nat_one_dim, k_one, b_sym));
    assert_ne!(
        whnf_k0, whnf_k1,
        "MASQUERADE NOT CLOSED: the faithful carrier produces the same \
         output at k=0 and k=1 — it is constant in k. WHNF(k=0)={:?}, \
         WHNF(k=1)={:?}",
        whnf_k0, whnf_k1,
    );
}

// =============================================================================
// Faithful theorem: proof term is Eq.refl on a free variable B, NOT on a
// collapsed constant. Verifies the statement type and that the proof term's
// tail literally names the bound `B` variable (structural, not alias).
// =============================================================================

#[test]
fn test_blockwise_crown_equiv_faithful_kernel_accepts() {
    // The kernel's add_decl must accept the proof. Re-run the full init on
    // a fresh env so the Declaration::Theorem registration exercises
    // add_decl (type-checks the proof term against the type).
    let mut env = Environment::new();
    env.init_nn_verify_blockwise_crown_ext()
        .expect("kernel must accept blockwise_crown_equiv_faithful proof term");
    let ci = env
        .get_const(&Name::from_string(
            "NNVerify.Block.blockwise_crown_equiv_faithful",
        ))
        .expect("blockwise_crown_equiv_faithful should be registered");
    assert_eq!(ci.kind, ConstantKind::Theorem);
    assert!(ci.value.is_some());
}

#[test]
fn test_blockwise_crown_equiv_faithful_type_has_two_binders() {
    // Statement: forall (d : Nat) (B : IntervalBounds d), ... = B
    // — two outer Pi binders.
    let env = make_env();
    let ci = env
        .get_const(&Name::from_string(
            "NNVerify.Block.blockwise_crown_equiv_faithful",
        ))
        .expect("blockwise_crown_equiv_faithful should exist");
    let mut cursor = ci.type_.clone();
    let mut binders = 0;
    while let ExprKind::Pi(_, _, body) = cursor.kind() {
        binders += 1;
        cursor = (**body).clone();
    }
    assert_eq!(
        binders, 2,
        "blockwise_crown_equiv_faithful should have 2 Pi binders (d, B), \
         got {}",
        binders,
    );
}

#[test]
fn test_blockwise_crown_equiv_faithful_not_refl_between_aliases() {
    // Rule M4 detection: the proof term must be Eq.refl on a BOUND VARIABLE
    // (BVar, introduced by the outer Pi binder for B), NOT Eq.refl on a
    // fully-applied constant like `zero_ib 1`. In the latter case, the
    // theorem would hold vacuously via alias collapse.
    let env = make_env();
    let ci = env
        .get_const(&Name::from_string(
            "NNVerify.Block.blockwise_crown_equiv_faithful",
        ))
        .expect("blockwise_crown_equiv_faithful should exist");
    let value = ci.value.as_ref().expect("proof value missing");

    // Walk through outer lambdas; the innermost body should be an
    // application of Eq.refl whose last argument is a BVar (referring to
    // the bound B).
    let mut cursor = value.clone();
    let mut lam_depth = 0;
    while let ExprKind::Lam(_, _, body) = cursor.kind() {
        lam_depth += 1;
        cursor = (**body).clone();
    }
    assert_eq!(
        lam_depth, 2,
        "proof should have 2 outer lambdas (d, B), got {}",
        lam_depth,
    );
    // Peel Eq.refl applications: @Eq.refl.{_} T arg
    let (_head, args) = app_spine(&cursor);
    // After peeling, the spine should be Eq.refl applied to the type and
    // the witness. The witness (last arg) should be a BVar 0 — the
    // innermost bound variable `B`.
    assert!(
        args.len() >= 2,
        "proof spine should be `Eq.refl T B` — got {} args",
        args.len(),
    );
    let witness = &args[args.len() - 1];
    match witness.kind() {
        ExprKind::BVar(idx) => {
            assert_eq!(
                *idx, 0,
                "witness arg of Eq.refl should be BVar 0 (bound B), got BVar {}",
                idx,
            );
        }
        other => panic!(
            "MASQUERADE NOT CLOSED: Eq.refl witness should be a BVar (bound \
             B), got {:?}. This suggests the proof closes over a collapsed \
             constant (e.g., zero_ib 1) instead of the symbolic input.",
            other,
        ),
    }
}

fn app_spine(expr: &Expr) -> (Expr, Vec<Expr>) {
    let mut args = Vec::new();
    let mut cursor = expr.clone();
    while let ExprKind::App(f, a) = cursor.kind() {
        args.push((**a).clone());
        cursor = (**f).clone();
    }
    args.reverse();
    (cursor, args)
}

#[test]
fn test_blockwise_crown_equiv_faithful_proof_references_eq_refl() {
    // Sanity: the proof term must actually reference Eq.refl.
    let env = make_env();
    let ci = env
        .get_const(&Name::from_string(
            "NNVerify.Block.blockwise_crown_equiv_faithful",
        ))
        .expect("blockwise_crown_equiv_faithful should exist");
    let value = ci.value.as_ref().expect("proof value missing");
    assert!(
        expr_references_const(value, "Eq.refl"),
        "proof term must reference Eq.refl",
    );
}

#[test]
fn test_blockwise_crown_equiv_faithful_infer_type_matches() {
    // Kernel infer_type on the theorem must succeed and yield the Pi type.
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let thm = Expr::const_(
        Name::from_string("NNVerify.Block.blockwise_crown_equiv_faithful"),
        vec![],
    );
    let ty = tc
        .infer_type(&thm)
        .expect("infer_type must succeed on faithful theorem");
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "inferred type must be a Pi (universally quantified)",
    );
    // Suppress Level-unused warning in case the import is dead after edits.
    let _ = Level::zero();
}

// =============================================================================
// #3491 Phase 2 — Block.compose_faithful discriminators
// =============================================================================
//
// The faithful `Block.compose_faithful` carrier lives in
// `nn_verify_blockwise_crown_ext_compose.rs`. Its body is
// `fun d k cb B => Nat.rec (fun _ => IB d) B (fun m ih => cb m ih) k`,
// so:
//   - at k = 0:       reduces to B (the input)
//   - at k = succ m:  reduces to cb m (compose_faithful d m cb B) — USES ih
//
// These tests assert the carrier is semantically live (Rule M2 inverted)
// and structurally distinct from `monolithic_crown_faithful` whose step
// case ignores IH and returns `zero_ib d` (Rule M3 inverted comparison).

/// Construct `@Block.compose_faithful d k cb B` as a kernel Expr.
fn cf_app(d: Expr, k: Expr, cb: Expr, b: Expr) -> Expr {
    let cf = Expr::const_(Name::from_string("NNVerify.Block.compose_faithful"), vec![]);
    Expr::apps(cf, [d, k, cb, b])
}

/// Build `cb := fun (_m : Nat) (b : IB 1) => zero_bounds_one` — constant
/// zero step. With `compose_faithful d k cb B`:
///   - at k=0 returns B
///   - at k=succ m returns `cb m ih = zero_ib 1` (ignoring ih)
///
/// At k=1 this produces `zero_ib 1`, matching what `monolithic_crown_faithful`
/// produces at k=1. For a cb that DOES use ih, results differ.
fn cb_zero_step() -> Expr {
    // fun (_ : Nat) (_ : IB 1) => zero_bounds_one
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let ib1 = Expr::app(
        Expr::const_(Name::from_string("NNVerify.IntervalBounds"), vec![]),
        Expr::app(
            Expr::const_(Name::from_string("Nat.succ"), vec![]),
            Expr::const_(Name::from_string("Nat.zero"), vec![]),
        ),
    );
    let inner = Expr::lam(crate::expr::BinderInfo::Default, ib1, zero_bounds_one());
    Expr::lam(crate::expr::BinderInfo::Default, nat_ty, inner)
}

/// `cb := fun (_m : Nat) (b : IB 1) => b` — identity step. With
/// `compose_faithful d k cb B`:
///   - at k=0 returns B
///   - at k=succ m returns `cb m ih = ih = compose_faithful d m cb B`
///     which unfolds iteratively back to B. So the whole expression
///     reduces to B at any k. This is the "cb uses ih" case.
fn cb_identity_step() -> Expr {
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let ib1 = Expr::app(
        Expr::const_(Name::from_string("NNVerify.IntervalBounds"), vec![]),
        Expr::app(
            Expr::const_(Name::from_string("Nat.succ"), vec![]),
            Expr::const_(Name::from_string("Nat.zero"), vec![]),
        ),
    );
    // The inner lambda binds b : IB 1, body is BVar 0 (which is b).
    let b_bvar = Expr::bvar(0);
    let inner = Expr::lam(crate::expr::BinderInfo::Default, ib1, b_bvar);
    Expr::lam(crate::expr::BinderInfo::Default, nat_ty, inner)
}

#[test]
fn test_compose_faithful_registered() {
    let env = make_env();
    let ci = env
        .get_const(&Name::from_string("NNVerify.Block.compose_faithful"))
        .expect("compose_faithful should be registered");
    assert_eq!(
        ci.kind,
        ConstantKind::Definition,
        "faithful Block.compose carrier must be a Declaration::Definition"
    );
    assert!(
        ci.value.is_some(),
        "compose_faithful must carry a body (reducible Definition)"
    );
}

#[test]
fn test_compose_faithful_body_uses_nat_rec() {
    // Body must reference Nat.rec (structural recursion on k).
    let env = make_env();
    let ci = env
        .get_const(&Name::from_string("NNVerify.Block.compose_faithful"))
        .expect("compose_faithful should exist");
    let value = ci
        .value
        .as_ref()
        .expect("compose_faithful should have a value");
    assert!(
        expr_references_const(value, "Nat.rec"),
        "compose_faithful body must reference Nat.rec — it is supposed to \
         pattern-match on k via structural recursion",
    );
}

#[test]
fn test_compose_faithful_structurally_distinct_from_monolithic() {
    // Rule M1 inverse: compose_faithful and monolithic_crown_faithful
    // must produce DIFFERENT WHNF outputs for the same (d, k, B) when cb
    // is NOT the constant-zero step. At k=1 with the identity cb,
    // compose_faithful returns B; monolithic_crown_faithful returns
    // zero_ib 1. These must differ.
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let nat_one_dim = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
    );
    let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    let k_one = Expr::app(nat_succ, nat_zero);
    let b_sym = sym_bounds_one();
    let cb = cb_identity_step();

    // compose_faithful 1 1 (fun _m b => b) sym_B  →*  sym_B
    let cf_whnf = tc.whnf(&cf_app(
        nat_one_dim.clone(),
        k_one.clone(),
        cb,
        b_sym.clone(),
    ));
    // monolithic_crown_faithful 1 1 sym_B  →*  zero_ib 1 (which ≠ sym_B)
    let mcf_whnf = tc.whnf(&mcf_app(nat_one_dim, k_one, b_sym));
    assert_ne!(
        cf_whnf, mcf_whnf,
        "MASQUERADE NOT BROKEN: compose_faithful (identity cb) and \
         monolithic_crown_faithful both reduce to the same WHNF at k=1 — \
         the two carriers are alias-equivalent and the Phase 2 refactor \
         did not actually break the collapse. \
         WHNF(compose_faithful)={:?}, WHNF(monolithic_crown_faithful)={:?}",
        cf_whnf, mcf_whnf,
    );
}

#[test]
fn test_compose_faithful_k_zero_returns_input() {
    // At k=0 the carrier must reduce to its input B, NOT to a collapsed
    // constant. Pass any cb — shape of cb must be irrelevant at k=0.
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let nat_one_dim = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
    );
    let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let b_sym = sym_bounds_one();
    let cb = cb_zero_step();
    let applied = cf_app(nat_one_dim, nat_zero, cb, b_sym.clone());
    let whnf_applied = tc.whnf(&applied);
    let whnf_input = tc.whnf(&b_sym);
    assert_eq!(
        whnf_applied, whnf_input,
        "at k=0 compose_faithful must WHNF-reduce to its input B \
         (was: {:?}, expected: {:?})",
        whnf_applied, whnf_input,
    );
}

#[test]
fn test_compose_faithful_uses_ih_in_step() {
    // Rule M3 inverse: with a cb that applies its IH argument, the
    // successor case must produce a normal form that depends on B.
    // compose_faithful 1 (succ 0) (fun _m ih => ih) sym_B  →*  sym_B
    // compose_faithful 1 (succ 0) (fun _m ih => ih) zero_B →*  zero_B
    // — two distinct inputs produce two distinct outputs via `cb`, proving
    // the step case actually consumes the IH.
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let nat_one_dim = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
    );
    let k_one = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
    );
    let cb = cb_identity_step();
    let b_sym = sym_bounds_one();
    let b_zero = zero_bounds_one();
    let whnf_sym = tc.whnf(&cf_app(
        nat_one_dim.clone(),
        k_one.clone(),
        cb.clone(),
        b_sym,
    ));
    let whnf_zero = tc.whnf(&cf_app(nat_one_dim, k_one, cb, b_zero));
    assert_ne!(
        whnf_sym, whnf_zero,
        "MASQUERADE NOT CLOSED: compose_faithful at k=succ 0 with an \
         identity cb returned the same output for two distinct inputs — \
         the step case is NOT actually using its IH. \
         WHNF(sym)={:?}, WHNF(zero)={:?}",
        whnf_sym, whnf_zero,
    );
}

#[test]
fn test_compose_faithful_discriminates_on_cb() {
    // With different `cb` functions, compose_faithful at k=succ 0 must
    // produce different outputs. cb_identity applied to B yields B; cb_zero
    // applied to B yields zero_ib. These must differ for a symbolic B.
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let nat_one_dim = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
    );
    let k_one = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
    );
    let b_sym = sym_bounds_one();
    let whnf_id = tc.whnf(&cf_app(
        nat_one_dim.clone(),
        k_one.clone(),
        cb_identity_step(),
        b_sym.clone(),
    ));
    let whnf_zero = tc.whnf(&cf_app(nat_one_dim, k_one, cb_zero_step(), b_sym));
    assert_ne!(
        whnf_id, whnf_zero,
        "MASQUERADE NOT CLOSED: compose_faithful at k=succ 0 gave the \
         same output for two distinct cb functions. Rule M2 still fires: \
         the carrier is ignoring its cb argument. \
         WHNF(cb=id)={:?}, WHNF(cb=zero)={:?}",
        whnf_id, whnf_zero,
    );
}

#[test]
fn test_compose_faithful_zero_eq_input_registered() {
    let env = make_env();
    let ci = env
        .get_const(&Name::from_string(
            "NNVerify.Block.compose_faithful_zero_eq_input",
        ))
        .expect("compose_faithful_zero_eq_input should be registered");
    assert_eq!(
        ci.kind,
        ConstantKind::Theorem,
        "compose_faithful_zero_eq_input must be Declaration::Theorem",
    );
    assert!(ci.value.is_some(), "theorem must carry a proof value");
}

#[test]
fn test_compose_faithful_zero_eq_input_kernel_accepts() {
    // Fresh environment re-runs `add_decl`, which type-checks the proof
    // term against the type. If the faithful carrier's iota-reduction at
    // k=0 did not actually return B, this would fail here.
    let mut env = Environment::new();
    env.init_nn_verify_blockwise_crown_ext()
        .expect("kernel must accept compose_faithful_zero_eq_input proof term");
    let ci = env
        .get_const(&Name::from_string(
            "NNVerify.Block.compose_faithful_zero_eq_input",
        ))
        .expect("compose_faithful_zero_eq_input should be registered");
    assert_eq!(ci.kind, ConstantKind::Theorem);
}

#[test]
fn test_compose_faithful_zero_eq_input_proof_refl_on_bvar() {
    // Rule M4 inverse: the proof must be Eq.refl on a BVar (bound B),
    // NOT on a collapsed constant. Walk through outer lambdas and check
    // the innermost Eq.refl witness.
    let env = make_env();
    let ci = env
        .get_const(&Name::from_string(
            "NNVerify.Block.compose_faithful_zero_eq_input",
        ))
        .expect("compose_faithful_zero_eq_input should exist");
    let value = ci.value.as_ref().expect("proof value missing");

    let mut cursor = value.clone();
    let mut lam_depth = 0;
    while let ExprKind::Lam(_, _, body) = cursor.kind() {
        lam_depth += 1;
        cursor = (**body).clone();
    }
    assert_eq!(
        lam_depth, 3,
        "proof should have 3 outer lambdas (d, cb, B), got {}",
        lam_depth,
    );
    // Collect application spine.
    let mut args = Vec::new();
    let mut head = cursor.clone();
    while let ExprKind::App(f, a) = head.kind() {
        args.push((**a).clone());
        head = (**f).clone();
    }
    args.reverse();
    assert!(
        args.len() >= 2,
        "proof spine should be `Eq.refl T B` — got {} args",
        args.len(),
    );
    let witness = &args[args.len() - 1];
    match witness.kind() {
        ExprKind::BVar(idx) => {
            assert_eq!(
                *idx, 0,
                "witness of Eq.refl should be BVar 0 (bound B), got BVar {}. \
                 A collapsed-constant witness would indicate the LHS is still \
                 alias-collapsing to zero_ib instead of iota-reducing to B.",
                idx,
            );
        }
        other => panic!(
            "MASQUERADE NOT CLOSED: Eq.refl witness must be a BVar (bound \
             B), got {:?}. This means the proof closes over a collapsed \
             constant rather than the symbolic input.",
            other,
        ),
    }
}

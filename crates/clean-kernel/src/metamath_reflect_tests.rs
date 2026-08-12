// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the computational Metamath checker (proof by reflection).
//!
//! The decisive tests are [`test_subst_step_kernel_verified_via_add_decl`]
//! (the kernel ACCEPTS a correct Metamath substitution certificate, via full
//! `add_decl` type-checking) and [`test_tampered_subst_target_rejected`] (the
//! kernel REJECTS a tampered one). Together they show the kernel genuinely
//! re-runs the substitution — this is not a String reflection or a vacuous
//! defeq collapse.

use super::*;
use crate::tc::TypeChecker;
use crate::ConstantKind;

/// Symbol codes used by the tests (arbitrary interned `Nat`s):
/// `(`=1, `→`=2, `)`=3, variable `ph`=10, wff `A`=20, wff `B`=21.
const OPEN: u64 = 1;
const ARROW: u64 = 2;
const CLOSE: u64 = 3;
const PH: u64 = 10;
const PS: u64 = 11;
const A: u64 = 20;
const B: u64 = 21;

fn env() -> Environment {
    let mut env = Environment::new();
    env.init_metamath_reflect()
        .expect("init_metamath_reflect must succeed");
    env
}

fn bool_ty_t() -> Expr {
    Expr::const_str("Bool")
}
/// `@Eq.{1} Bool x y`.
fn eq_bool(x: Expr, y: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [bool_ty_t(), x, y],
    )
}
/// `@Eq.refl.{1} Bool v`.
fn eq_refl_bool(v: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [bool_ty_t(), v],
    )
}

#[test]
fn test_metamath_ops_are_reducible_definitions() {
    let env = env();
    for op in [
        names::APPEND,
        names::ITE_LIST,
        names::SUBST1,
        names::LIST_BEQ,
    ] {
        let info = env
            .get_const(&Name::from_string(op))
            .unwrap_or_else(|| panic!("{op} should be registered"));
        assert!(
            matches!(info.kind, ConstantKind::Definition),
            "{op} must be a Definition, not an axiom"
        );
    }
}

/// SOUNDNESS PRIMITIVE for the O(1) range-coded fast path: `isVar K n` must be
/// def-eq to `memNat n [1..K-1]` for ALL sampled n — including n=0 (a wrong
/// `isVar` missing the lower bound would mis-equate here), the in-range vars, the
/// boundary K-1/K, and far out-of-range constants. The kernel reduces both and
/// `Eq.refl` only type-checks when they agree, so this is a genuine check.
#[test]
fn test_isvar_equiv_memnat_on_contiguous_range() {
    let env = env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    const K: u64 = 6;
    let vu = nat_list_lit(&(1..K).collect::<Vec<u64>>()); // var_universe = [1,2,3,4,5]
    for n in [0u64, 1, 2, 5, 6, 7, 100] {
        let lhs = is_var_app(Expr::nat_lit(K), Expr::nat_lit(n));
        let rhs = mem_nat_app(Expr::nat_lit(n), vu.clone());
        // isVar K n  ≡  memNat n [1..K-1]
        tc.check_type(&eq_refl_bool_t(lhs.clone()), &eq_bool_t(lhs.clone(), rhs))
            .unwrap_or_else(|e| {
                panic!("isVar {K} {n} must def-eq memNat {n} [1..{}]: {e:?}", K - 1)
            });
        // and reduces to the expected Bool literal (positive litmus)
        let expected = if (1..K).contains(&n) {
            btrue()
        } else {
            bfalse()
        };
        tc.check_type(
            &eq_refl_bool_t(expected.clone()),
            &eq_bool_t(lhs.clone(), expected),
        )
        .unwrap_or_else(|e| panic!("isVar {K} {n} expected {}: {e:?}", (1..K).contains(&n)));
    }
}

/// The native `memNat` reducer must return EXACTLY list membership on ground
/// args, and `None` (definitional fallback) on non-ground args — pinning the
/// trusted fast path against the definition it replaces in computation.
#[test]
fn test_memnat_native_reducer_matches_definition() {
    let xs = nat_list_lit(&[1, 3, 5, 7]);
    for (n, want) in [
        (0u64, false),
        (1, true),
        (2, false),
        (5, true),
        (7, true),
        (8, false),
        (9999, false),
    ] {
        let got = reduce_mm_memnat(&[&Expr::nat_lit(n), &xs]);
        let expected = Some(if want { btrue() } else { bfalse() });
        assert!(
            got == expected,
            "memNat {n} [1,3,5,7] native gave wrong result"
        );
    }
    // non-literal n, and non-ground list, must fall back (None).
    assert!(reduce_mm_memnat(&[&Expr::const_str("v"), &xs]).is_none());
    assert!(reduce_mm_memnat(&[&Expr::nat_lit(1), &Expr::const_str("xs")]).is_none());
}

/// The MILESTONE-1 result: a genuine Metamath substitution step
/// `subst ph := A in ( ph → ph )  ≡  ( A → A )` is certified by an `Eq.refl`
/// term that the Clean kernel accepts via full `add_decl` type-checking. The
/// kernel reduces `subst1` over the data; this is real kernel verification.
#[test]
fn test_subst_step_kernel_verified_via_add_decl() {
    let mut env = env();
    // template  ( ph → ph )   = [ ( ph → ph ) ]
    let template = [OPEN, PH, ARROW, PH, CLOSE];
    // expected  ( A → A )
    let target = nat_list_lit(&[OPEN, A, ARROW, A, CLOSE]);

    let lhs = subst1_app(PH, &[A], &template);
    let goal = eq_list_nat(lhs, target.clone());
    let proof = eq_refl_list_nat(target);

    env.add_decl(Declaration::Theorem {
        name: Name::from_string("Clean.MM.test.idSubstStep"),
        level_params: vec![],
        type_: goal,
        value: proof,
    })
    .expect("kernel must accept the correct substitution certificate");

    assert!(env
        .get_const(&Name::from_string("Clean.MM.test.idSubstStep"))
        .is_some());
}

/// LITMUS: a tampered conclusion (claiming the substitution yields `( A → B )`)
/// must be REJECTED by the kernel — proving the check is genuine, not vacuous.
#[test]
fn test_tampered_subst_target_rejected() {
    let env = env();
    let template = [OPEN, PH, ARROW, PH, CLOSE];
    let wrong = nat_list_lit(&[OPEN, A, ARROW, B, CLOSE]); // second slot B, not A

    let lhs = subst1_app(PH, &[A], &template);
    let goal = eq_list_nat(lhs, wrong.clone());
    let proof = eq_refl_list_nat(wrong);

    let tc = TypeChecker::with_mode(&env, env.mode());
    let res = tc.check_type(&proof, &goal);
    assert!(
        res.is_err(),
        "kernel MUST reject a tampered substitution target (got Ok)"
    );
}

/// The substitution reduces to exactly the expected expression (positive
/// direction, checked through `check_type` of the reflection certificate).
#[test]
fn test_subst1_reduces_to_expected() {
    let env = env();
    let template = [OPEN, PH, ARROW, PH, CLOSE];
    let target = nat_list_lit(&[OPEN, A, ARROW, A, CLOSE]);
    let lhs = subst1_app(PH, &[A], &template);
    let goal = eq_list_nat(lhs, target.clone());
    let proof = eq_refl_list_nat(target);
    let tc = TypeChecker::with_mode(&env, env.mode());
    tc.check_type(&proof, &goal)
        .expect("subst1 must reduce to ( A → A )");
}

/// A multi-symbol replacement (`ph := ( A → B )`) substitutes the whole
/// expression for each occurrence — the genuine Metamath substitution shape.
#[test]
fn test_subst1_multi_symbol_replacement() {
    let env = env();
    // ph := ( A → B ); template ( ph → ph ) ⇒ ( ( A → B ) → ( A → B ) )
    let repl = [OPEN, A, ARROW, B, CLOSE];
    let template = [OPEN, PH, ARROW, PH, CLOSE];
    let expected = [
        OPEN, OPEN, A, ARROW, B, CLOSE, ARROW, OPEN, A, ARROW, B, CLOSE, CLOSE,
    ];
    let lhs = subst1_app(PH, &repl, &template);
    let goal = eq_list_nat(lhs, nat_list_lit(&expected));
    let proof = eq_refl_list_nat(nat_list_lit(&expected));
    let tc = TypeChecker::with_mode(&env, env.mode());
    tc.check_type(&proof, &goal)
        .expect("multi-symbol substitution must reduce correctly");
}

/// `listBeq` reflects to `true` on equal lists and `false` on unequal lists —
/// the final-stack comparison the multi-step checker will use.
#[test]
fn test_list_beq_reflects_true_and_false() {
    let env = env();
    let tc = TypeChecker::with_mode(&env, env.mode());

    let equal = eq_bool(
        list_beq_app(&[OPEN, A, ARROW, A, CLOSE], &[OPEN, A, ARROW, A, CLOSE]),
        btrue(),
    );
    tc.check_type(&eq_refl_bool(btrue()), &equal)
        .expect("equal lists must reflect to Bool.true");

    let unequal = eq_bool(
        list_beq_app(&[OPEN, A, ARROW, A, CLOSE], &[OPEN, A, ARROW, B, CLOSE]),
        bfalse(),
    );
    tc.check_type(&eq_refl_bool(bfalse()), &unequal)
        .expect("unequal lists must reflect to Bool.false");

    // Different lengths also compare false.
    let shorter = eq_bool(list_beq_app(&[OPEN, A], &[OPEN, A, CLOSE]), bfalse());
    tc.check_type(&eq_refl_bool(bfalse()), &shorter)
        .expect("different-length lists must reflect to Bool.false");
}

/// M2: a genuine simultaneous multi-variable substitution
/// `subst {ph:=A, ps:=B} in ( ph → ps ) ≡ ( A → B )` is kernel-accepted via
/// full `add_decl`.
#[test]
fn test_apply_subst_multivar_kernel_verified() {
    let mut env = env();
    let template = [OPEN, PH, ARROW, PS, CLOSE];
    let a = [A];
    let b = [B];
    let bindings: [(u64, &[u64]); 2] = [(PH, &a), (PS, &b)];
    let target = nat_list_lit(&[OPEN, A, ARROW, B, CLOSE]);

    let lhs = apply_subst_app(&bindings, &template);
    let goal = eq_list_nat(lhs, target.clone());
    let proof = eq_refl_list_nat(target);

    env.add_decl(Declaration::Theorem {
        name: Name::from_string("Clean.MM.test.multivarSubst"),
        level_params: vec![],
        type_: goal,
        value: proof,
    })
    .expect("kernel must accept the multi-variable substitution certificate");
}

/// The DECISIVE simultaneity test: `subst {ph:=ps, ps:=A} in ( ph → ps )`.
/// Simultaneous substitution gives `( ps → A )`. A *sequential* substitution
/// (`ph:=ps` then `ps:=A`) would wrongly give `( A → A )`. We verify the kernel
/// reduces to `( ps → A )` AND rejects `( A → A )` — proving genuine
/// simultaneity (a soundness requirement of Metamath substitution).
#[test]
fn test_apply_subst_is_simultaneous_not_sequential() {
    let env = env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let template = [OPEN, PH, ARROW, PS, CLOSE];
    let ps = [PS];
    let a = [A];
    let bindings: [(u64, &[u64]); 2] = [(PH, &ps), (PS, &a)];

    // Correct simultaneous result: ( ps → A )
    let simultaneous = nat_list_lit(&[OPEN, PS, ARROW, A, CLOSE]);
    let lhs = apply_subst_app(&bindings, &template);
    tc.check_type(
        &eq_refl_list_nat(simultaneous.clone()),
        &eq_list_nat(lhs.clone(), simultaneous),
    )
    .expect("simultaneous substitution must yield ( ps → A )");

    // Sequential (wrong) result ( A → A ) must be REJECTED.
    let sequential_wrong = nat_list_lit(&[OPEN, A, ARROW, A, CLOSE]);
    let res = tc.check_type(
        &eq_refl_list_nat(sequential_wrong.clone()),
        &eq_list_nat(lhs, sequential_wrong),
    );
    assert!(
        res.is_err(),
        "the sequential (non-simultaneous) result ( A → A ) must be rejected"
    );
}

/// LITMUS for `applySubst`: a tampered conclusion is rejected.
#[test]
fn test_apply_subst_tampered_rejected() {
    let env = env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let template = [OPEN, PH, ARROW, PS, CLOSE];
    let a = [A];
    let b = [B];
    let bindings: [(u64, &[u64]); 2] = [(PH, &a), (PS, &b)];
    // claim ( B → A ) instead of the correct ( A → B )
    let wrong = nat_list_lit(&[OPEN, B, ARROW, A, CLOSE]);
    let lhs = apply_subst_app(&bindings, &template);
    let res = tc.check_type(&eq_refl_list_nat(wrong.clone()), &eq_list_nat(lhs, wrong));
    assert!(res.is_err(), "tampered applySubst target must be rejected");
}

// ════════════════════════════════════════════════════════════════════════════
// M3: a COMPLETE propositional Metamath theorem, kernel-verified (derivation
// terms). `Provable`, ax-1 and ax-mp are postulated as SCHEMATIC axioms
// (`Π (σ : Nat → List Nat), Provable (applySubst σ …)`) — a faithful
// transcription of the `.mm` `$a` statements. A `$p` theorem is then PROVED by
// a derivation term that applies them; the kernel checks the term, reducing
// `applySubst` at each step to confirm the (substituted) types line up. The
// theorem's axiom closure is exactly {Provable, ax-1, ax-mp} — i.e. Metamath's
// own postulates, the honest trust basis for a Metamath import.
// ════════════════════════════════════════════════════════════════════════════

const TURN: u64 = 4; // |-

/// `( x → y )` as a symbol list.
fn imp_form(x: &[u64], y: &[u64]) -> Vec<u64> {
    let mut v = vec![OPEN];
    v.extend_from_slice(x);
    v.push(ARROW);
    v.extend_from_slice(y);
    v.push(CLOSE);
    v
}
/// `|- x` as a symbol list.
fn turn(x: &[u64]) -> Vec<u64> {
    let mut v = vec![TURN];
    v.extend_from_slice(x);
    v
}
/// `Clean.MM.Provable form : Prop`.
fn prov(form: Expr) -> Expr {
    Expr::app(Expr::const_str("Clean.MM.Provable"), form)
}
/// `Clean.MM.applySubst σ form` for a σ expression and a literal `form`.
fn apply_subst_var(sigma: Expr, form: &[u64]) -> Expr {
    Expr::apps(
        Expr::const_str(names::APPLY_SUBST),
        [sigma, nat_list_lit(form)],
    )
}

/// An env with `Provable` plus the propositional assertion axioms ax-1, ax-mp.
fn prop_env() -> Environment {
    let mut env = env();
    let subst_fn_ty = Expr::arrow(Expr::const_str("Nat"), list_nat());

    // Provable : List Nat → Prop
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Clean.MM.Provable"),
        level_params: vec![],
        type_: Expr::arrow(list_nat(), Expr::prop()),
    })
    .expect("register Provable");

    // ax-1 : Π σ, Provable (applySubst σ |- ( ph → ( ps → ph ) ))
    let ax1_concl = turn(&imp_form(&[PH], &imp_form(&[PS], &[PH])));
    {
        let mut b = EnvDeclBuilder::new();
        let (s_id, s) = b.fresh_local(subst_fn_ty.clone());
        let body = prov(apply_subst_var(s, &ax1_concl));
        let ty = b.finish(b.mk_pi(s_id, BinderInfo::Default, subst_fn_ty.clone(), body));
        env.add_decl(Declaration::Axiom {
            name: Name::from_string("Clean.MM.prop.ax1"),
            level_params: vec![],
            type_: ty,
        })
        .expect("register ax-1");
    }

    // ax-mp : Π σ, Provable (applySubst σ |- ph)
    //              → Provable (applySubst σ |- ( ph → ps ))
    //              → Provable (applySubst σ |- ps)
    {
        let mp_h1 = turn(&[PH]);
        let mp_h2 = turn(&imp_form(&[PH], &[PS]));
        let mp_concl = turn(&[PS]);
        let mut b = EnvDeclBuilder::new();
        let (s_id, s) = b.fresh_local(subst_fn_ty.clone());
        let concl = prov(apply_subst_var(s.clone(), &mp_concl));
        let arrow2 = Expr::arrow(prov(apply_subst_var(s.clone(), &mp_h2)), concl);
        let arrow1 = Expr::arrow(prov(apply_subst_var(s, &mp_h1)), arrow2);
        let ty = b.finish(b.mk_pi(s_id, BinderInfo::Default, subst_fn_ty.clone(), arrow1));
        env.add_decl(Declaration::Axiom {
            name: Name::from_string("Clean.MM.prop.axmp"),
            level_params: vec![],
            type_: ty,
        })
        .expect("register ax-mp");
    }
    env
}

/// MILESTONE 3: a COMPLETE Metamath theorem — a ground instance of `a1i`
/// (from `|- A` infer `|- ( B → A )`) — is kernel-verified by a derivation term
/// applying ax-1 and ax-mp. The kernel reduces `applySubst` to confirm the
/// substituted hypotheses match; this is a genuine kernel proof of a Metamath
/// theorem relative to Metamath's postulates.
#[test]
fn test_a1i_complete_theorem_kernel_verified() {
    let mut env = prop_env();

    let hyp_ty = prov(nat_list_lit(&turn(&[A]))); // Provable (|- A)
    let goal_ty = prov(nat_list_lit(&turn(&imp_form(&[B], &[A])))); // Provable (|- ( B → A ))
    let thm_ty = Expr::arrow(hyp_ty.clone(), goal_ty);

    // proof: fun (h : Provable (|- A)) => axmp σ_mp h (ax1 σ_ax1)
    //   σ_ax1 = {ph:=A, ps:=B}        ⇒ ax1 σ_ax1 : Provable (|- ( A → ( B → A ) ))
    //   σ_mp  = {ph:=A, ps:=( B → A )} ⇒ axmp expects (|- A) then (|- ( A → ( B → A ) ))
    let a_arr = [A];
    let b_arr = [B];
    let ba = imp_form(&[B], &[A]);
    let sigma_ax1 = subst_fn(&[(PH, &a_arr), (PS, &b_arr)]);
    let sigma_mp = subst_fn(&[(PH, &a_arr), (PS, &ba)]);

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (h_id, h) = b.fresh_local(hyp_ty.clone());
        let ax1_app = Expr::app(Expr::const_str("Clean.MM.prop.ax1"), sigma_ax1);
        let mp_app = Expr::apps(
            Expr::const_str("Clean.MM.prop.axmp"),
            [sigma_mp, h, ax1_app],
        );
        b.finish(b.mk_lam(h_id, BinderInfo::Default, hyp_ty.clone(), mp_app))
    };

    env.add_decl(Declaration::Theorem {
        name: Name::from_string("Clean.MM.test.a1i_AB"),
        level_params: vec![],
        type_: thm_ty,
        value,
    })
    .expect("kernel must accept the a1i derivation term");

    assert!(env
        .get_const(&Name::from_string("Clean.MM.test.a1i_AB"))
        .is_some());
}

/// LITMUS for the complete theorem: a derivation that swaps the two ax-mp
/// premises (an invalid proof) must be REJECTED by the kernel.
#[test]
fn test_a1i_tampered_proof_rejected() {
    let env = prop_env();
    let tc = TypeChecker::with_mode(&env, env.mode());

    let hyp_ty = prov(nat_list_lit(&turn(&[A])));
    let goal_ty = prov(nat_list_lit(&turn(&imp_form(&[B], &[A]))));
    let thm_ty = Expr::arrow(hyp_ty.clone(), goal_ty);

    let a_arr = [A];
    let b_arr = [B];
    let ba = imp_form(&[B], &[A]);
    let sigma_ax1 = subst_fn(&[(PH, &a_arr), (PS, &b_arr)]);
    let sigma_mp = subst_fn(&[(PH, &a_arr), (PS, &ba)]);

    // TAMPER: pass (ax1, h) instead of (h, ax1) — premises in the wrong order.
    let bad_value = {
        let mut b = EnvDeclBuilder::new();
        let (h_id, h) = b.fresh_local(hyp_ty.clone());
        let ax1_app = Expr::app(Expr::const_str("Clean.MM.prop.ax1"), sigma_ax1);
        let mp_app = Expr::apps(
            Expr::const_str("Clean.MM.prop.axmp"),
            [sigma_mp, ax1_app, h],
        );
        b.finish(b.mk_lam(h_id, BinderInfo::Default, hyp_ty.clone(), mp_app))
    };

    let res = tc.check_type(&bad_value, &thm_ty);
    assert!(
        res.is_err(),
        "an invalid (swapped-premise) derivation must be rejected by the kernel"
    );
}

// ════════════════════════════════════════════════════════════════════════════
// M4: the TYPECODE-FAITHFUL encoding the importer will target. One predicate
// `MMThm : List Nat → Prop` over `[typecode, …]` symbol lists; each assertion
// takes its mandatory FLOATING and ESSENTIAL hypotheses as `Π` arguments — so
// the kernel also checks well-formedness (`wff`) construction, exactly as a real
// Metamath verifier does. We verify the real set.mm theorem `a1i` end to end,
// including building `wff ( B → A )` via `wi`.
// ════════════════════════════════════════════════════════════════════════════

const WFF: u64 = 5; // wff typecode

/// `Clean.MM.MMThm form : Prop` (form's first symbol is its typecode).
fn mmthm(form: Expr) -> Expr {
    Expr::app(Expr::const_str("Clean.MM.MMThm"), form)
}

/// An env with `MMThm`, the wff-builder `wi`, and ax-1 / ax-mp carrying their
/// floating + essential hypotheses as Π arguments, plus ground wff floats for
/// `A` and `B`.
fn prop_env_typed() -> Environment {
    let mut env = env();
    let subst_fn_ty = Expr::arrow(Expr::const_str("Nat"), list_nat());

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Clean.MM.MMThm"),
        level_params: vec![],
        type_: Expr::arrow(list_nat(), Expr::prop()),
    })
    .expect("register MMThm");

    // Register `name : Π σ, MMThm(σ h_0) → … → MMThm(σ h_{n-1}) → MMThm(σ concl)`.
    let add_assertion = |env: &mut Environment, name: &str, hyps: &[Vec<u64>], concl: &[u64]| {
        let mut b = EnvDeclBuilder::new();
        let (s_id, s) = b.fresh_local(subst_fn_ty.clone());
        let mut ty = mmthm(apply_subst_var(s.clone(), concl));
        for h in hyps.iter().rev() {
            ty = Expr::arrow(mmthm(apply_subst_var(s.clone(), h)), ty);
        }
        let ty = b.finish(b.mk_pi(s_id, BinderInfo::Default, subst_fn_ty.clone(), ty));
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
        })
        .unwrap_or_else(|e| panic!("register {name}: {e}"));
    };

    // wi : wff ph → wff ps → wff ( ph → ps )
    add_assertion(
        &mut env,
        "Clean.MM.t.wi",
        &[vec![WFF, PH], vec![WFF, PS]],
        &[WFF, OPEN, PH, ARROW, PS, CLOSE],
    );
    // ax-1 : wff ph → wff ps → |- ( ph → ( ps → ph ) )
    add_assertion(
        &mut env,
        "Clean.MM.t.ax1",
        &[vec![WFF, PH], vec![WFF, PS]],
        &turn(&imp_form(&[PH], &imp_form(&[PS], &[PH]))),
    );
    // ax-mp : wff ph → wff ps → |- ph → |- ( ph → ps ) → |- ps
    add_assertion(
        &mut env,
        "Clean.MM.t.axmp",
        &[
            vec![WFF, PH],
            vec![WFF, PS],
            turn(&[PH]),
            turn(&imp_form(&[PH], &[PS])),
        ],
        &turn(&[PS]),
    );

    // Ground wff floats: A and B are wffs.
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Clean.MM.t.wA"),
        level_params: vec![],
        type_: mmthm(nat_list_lit(&[WFF, A])),
    })
    .expect("register wA");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Clean.MM.t.wB"),
        level_params: vec![],
        type_: mmthm(nat_list_lit(&[WFF, B])),
    })
    .expect("register wB");
    env
}

/// MILESTONE 4: the real set.mm theorem `a1i` (given `|- A` infer `|- ( B → A )`)
/// kernel-verified in the TYPECODE-FAITHFUL encoding — the derivation also
/// constructs `wff ( B → A )` via `wi`, and the kernel checks every wff and
/// substitution. This is exactly the certificate shape the importer emits.
#[test]
fn test_a1i_typed_encoding_kernel_verified() {
    let mut env = prop_env_typed();

    // a1i_AB : MMThm (|- A) → MMThm (|- ( B → A ))
    let hyp_ty = mmthm(nat_list_lit(&turn(&[A])));
    let goal_ty = mmthm(nat_list_lit(&turn(&imp_form(&[B], &[A]))));
    let thm_ty = Expr::arrow(hyp_ty.clone(), goal_ty);

    let a_arr = [A];
    let b_arr = [B];
    let ba = imp_form(&[B], &[A]);
    let wa = Expr::const_str("Clean.MM.t.wA");
    let wb = Expr::const_str("Clean.MM.t.wB");

    // w_ba : wff ( B → A ) = wi {ph:=B, ps:=A} wB wA
    let w_ba = Expr::apps(
        Expr::const_str("Clean.MM.t.wi"),
        [
            subst_fn(&[(PH, &b_arr), (PS, &a_arr)]),
            wb.clone(),
            wa.clone(),
        ],
    );
    // ax1_app : |- ( A → ( B → A ) ) = ax1 {ph:=A, ps:=B} wA wB
    let ax1_app = Expr::apps(
        Expr::const_str("Clean.MM.t.ax1"),
        [
            subst_fn(&[(PH, &a_arr), (PS, &b_arr)]),
            wa.clone(),
            wb.clone(),
        ],
    );

    // proof: fun h => axmp {ph:=A, ps:=( B → A )} wA w_ba h ax1_app
    let value = {
        let mut b = EnvDeclBuilder::new();
        let (h_id, h) = b.fresh_local(hyp_ty.clone());
        let mp_app = Expr::apps(
            Expr::const_str("Clean.MM.t.axmp"),
            [
                subst_fn(&[(PH, &a_arr), (PS, &ba)]),
                wa.clone(),
                w_ba,
                h,
                ax1_app,
            ],
        );
        b.finish(b.mk_lam(h_id, BinderInfo::Default, hyp_ty.clone(), mp_app))
    };

    env.add_decl(Declaration::Theorem {
        name: Name::from_string("Clean.MM.test.a1i_typed"),
        level_params: vec![],
        type_: thm_ty,
        value,
    })
    .expect("kernel must accept the typecode-faithful a1i derivation");

    assert!(env
        .get_const(&Name::from_string("Clean.MM.test.a1i_typed"))
        .is_some());
}

/// LITMUS for the typed encoding: supplying the WRONG wff witness for `ps`
/// (claiming `wff A` where `wff ( B → A )` is required) must be rejected.
#[test]
fn test_a1i_typed_wrong_wff_rejected() {
    let env = prop_env_typed();
    let tc = TypeChecker::with_mode(&env, env.mode());

    let hyp_ty = mmthm(nat_list_lit(&turn(&[A])));
    let goal_ty = mmthm(nat_list_lit(&turn(&imp_form(&[B], &[A]))));
    let thm_ty = Expr::arrow(hyp_ty.clone(), goal_ty);

    let a_arr = [A];
    let b_arr = [B];
    let ba = imp_form(&[B], &[A]);
    let wa = Expr::const_str("Clean.MM.t.wA");
    let wb = Expr::const_str("Clean.MM.t.wB");
    let ax1_app = Expr::apps(
        Expr::const_str("Clean.MM.t.ax1"),
        [
            subst_fn(&[(PH, &a_arr), (PS, &b_arr)]),
            wa.clone(),
            wb.clone(),
        ],
    );

    // TAMPER: pass `wA` (wff A) as the `wff ps` witness, but ps = ( B → A ).
    let bad_value = {
        let mut b = EnvDeclBuilder::new();
        let (h_id, h) = b.fresh_local(hyp_ty.clone());
        let mp_app = Expr::apps(
            Expr::const_str("Clean.MM.t.axmp"),
            [
                subst_fn(&[(PH, &a_arr), (PS, &ba)]),
                wa.clone(),
                wa.clone(), // WRONG: should be wff ( B → A )
                h,
                ax1_app,
            ],
        );
        b.finish(b.mk_lam(h_id, BinderInfo::Default, hyp_ty.clone(), mp_app))
    };

    let res = tc.check_type(&bad_value, &thm_ty);
    assert!(
        res.is_err(),
        "a wrong wff witness must be rejected by the kernel"
    );
}

// ════════════════════════════════════════════════════════════════════════════
// M5: in-kernel inductive lemmas (the substitution-composition chain). These
// are registered — and therefore kernel-type-checked — by
// `init_metamath_reflect` itself, so if any `List.rec` induction proof were
// wrong, `env()` would panic. The chain (append_assoc → applySubst_append →
// applySubst_compose) justifies substitution composition, the key lemma that
// unblocks schematic lemma reuse for the importer.
// ════════════════════════════════════════════════════════════════════════════

/// The three composition-chain lemmas are present (and were proved at init).
#[test]
fn test_subst_lemmas_registered() {
    let env = env();
    for lemma in [
        names::APPEND_ASSOC,
        names::APPLYSUBST_APPEND,
        names::APPLYSUBST_COMPOSE,
    ] {
        assert!(
            env.get_const(&Name::from_string(lemma)).is_some(),
            "{lemma} should be registered (proved) by init_metamath_reflect"
        );
    }
}

// ════════════════════════════════════════════════════════════════════════════
// M6: the IMPORTER CORE. `register_metamath_assertions` + `verify_metamath_theorem`
// build and kernel-check a certificate AUTOMATICALLY from structured data
// (assertions + a proof tree) — the bridge a real `.mm` importer drives. Here we
// auto-verify `a1i` from its proof tree (vs. the hand-built terms of M3/M4).
// ════════════════════════════════════════════════════════════════════════════

/// The propositional assertions wi, ax-1, ax-mp as importer `MMAssertion`s.
fn prop_assertions() -> Vec<MMAssertion> {
    vec![
        // wi : wff ph → wff ps → wff ( ph → ps )
        MMAssertion {
            name: "mm.wi".to_string(),
            float_hyps: vec![(WFF, PH), (WFF, PS)],
            essential_hyps: vec![],
            conclusion: vec![WFF, OPEN, PH, ARROW, PS, CLOSE],
            disjoints: vec![],
            var_universe: vec![PH, PS, A, B],
        },
        // ax-1 : wff ph → wff ps → |- ( ph → ( ps → ph ) )
        MMAssertion {
            name: "mm.ax-1".to_string(),
            float_hyps: vec![(WFF, PH), (WFF, PS)],
            essential_hyps: vec![],
            conclusion: turn(&imp_form(&[PH], &imp_form(&[PS], &[PH]))),
            disjoints: vec![],
            var_universe: vec![PH, PS, A, B],
        },
        // ax-mp : wff ph → wff ps → |- ph → |- ( ph → ps ) → |- ps
        MMAssertion {
            name: "mm.ax-mp".to_string(),
            float_hyps: vec![(WFF, PH), (WFF, PS)],
            essential_hyps: vec![turn(&[PH]), turn(&imp_form(&[PH], &[PS]))],
            conclusion: turn(&[PS]),
            disjoints: vec![],
            var_universe: vec![PH, PS, A, B],
        },
    ]
}

/// The `a1i` ground proof tree (floats wff A, wff B at indices 0,1; essential
/// |- A at index 2).
fn a1i_proof_tree() -> MMProofTree {
    let ba = imp_form(&[B], &[A]);
    let wi_app = MMProofTree::Apply {
        assertion: "mm.wi".to_string(),
        subst: vec![(PH, vec![B]), (PS, vec![A])],
        args: vec![MMProofTree::Hyp(1), MMProofTree::Hyp(0)],
    };
    let ax1_app = MMProofTree::Apply {
        assertion: "mm.ax-1".to_string(),
        subst: vec![(PH, vec![A]), (PS, vec![B])],
        args: vec![MMProofTree::Hyp(0), MMProofTree::Hyp(1)],
    };
    MMProofTree::Apply {
        assertion: "mm.ax-mp".to_string(),
        subst: vec![(PH, vec![A]), (PS, ba)],
        args: vec![MMProofTree::Hyp(0), wi_app, MMProofTree::Hyp(2), ax1_app],
    }
}

/// M11 — SCHEMATIC reuse. Register a theorem as `Π σ, MMThm(applySubst σ H)→…`
/// and REUSE it by APPLICATION at the call-site σ (no proof-tree inlining). The
/// decisive case is reuse at a MERGING substitution (`ps := ph`) — the same shape
/// that broke under inlining (`simprim`), here verified with a small term.
#[test]
fn test_schematic_reuse_at_merging_subst() {
    let mut env = env();
    register_metamath_assertions(&mut env, &prop_assertions()).expect("register assertions");

    let ax1_concl = turn(&imp_form(&[PH], &imp_form(&[PS], &[PH])));
    let ax1_sig = (vec![vec![WFF, PH], vec![WFF, PS]], ax1_concl.clone());

    let mut sigs: hashbrown::HashMap<String, (Vec<Vec<u64>>, Vec<u64>)> = hashbrown::HashMap::new();
    sigs.insert("mm.ax-1".to_string(), ax1_sig.clone());

    // mm.a1restate : Π σ, … ⊢ applySubst σ ( ph → ( ps → ph ) ) — restate ax-1
    // by APPLYING the schematic axiom at the identity substitution.
    let restate_proof = MMProofTree::Apply {
        assertion: "mm.ax-1".to_string(),
        subst: vec![(PH, vec![PH]), (PS, vec![PS])],
        args: vec![MMProofTree::Hyp(0), MMProofTree::Hyp(1)],
    };
    verify_metamath_theorem_schematic(
        &mut env,
        "mm.a1restate",
        &[(WFF, PH), (WFF, PS)],
        &[],
        &ax1_concl,
        &restate_proof,
        &sigs,
        &[PH, PS, A, B],
    )
    .expect("schematic restatement of ax-1 must kernel-verify");

    // a1restate has the same schematic signature as ax-1.
    sigs.insert("mm.a1restate".to_string(), ax1_sig);

    // mm.reuse : REUSE a1restate at σ = (ps := ph) ⇒ ⊢ ( ph → ( ph → ph ) ).
    // Both float-witness args collapse to `Hyp(0)` (the single wff ph witness).
    let reuse_concl = turn(&imp_form(&[PH], &imp_form(&[PH], &[PH])));
    let reuse_proof = MMProofTree::Apply {
        assertion: "mm.a1restate".to_string(),
        subst: vec![(PH, vec![PH]), (PS, vec![PH])],
        args: vec![MMProofTree::Hyp(0), MMProofTree::Hyp(0)],
    };
    verify_metamath_theorem_schematic(
        &mut env,
        "mm.reuse",
        &[(WFF, PH)],
        &[],
        &reuse_concl,
        &reuse_proof,
        &sigs,
        &[PH, PS, A, B],
    )
    .expect("schematic reuse at a MERGING substitution must kernel-verify");
    assert!(env.get_const(&Name::from_string("mm.reuse")).is_some());
}

/// MILESTONE 6: the importer auto-builds and the kernel accepts the `a1i`
/// certificate directly from a structured proof tree.
#[test]
fn test_importer_verifies_a1i_from_proof_tree() {
    let mut env = env();
    register_metamath_assertions(&mut env, &prop_assertions()).expect("register assertions");
    verify_metamath_theorem(
        &mut env,
        "mm.a1i_AB",
        &[(WFF, A), (WFF, B)],
        &[turn(&[A])],
        &turn(&imp_form(&[B], &[A])),
        &a1i_proof_tree(),
    )
    .expect("importer must kernel-verify a1i from its proof tree");
    assert!(env.get_const(&Name::from_string("mm.a1i_AB")).is_some());
}

/// LITMUS: an invalid proof tree (ax-mp's essential premises swapped) is
/// rejected by the importer's kernel check.
#[test]
fn test_importer_rejects_invalid_proof_tree() {
    let mut env = env();
    register_metamath_assertions(&mut env, &prop_assertions()).expect("register assertions");

    let ba = imp_form(&[B], &[A]);
    let wi_app = MMProofTree::Apply {
        assertion: "mm.wi".to_string(),
        subst: vec![(PH, vec![B]), (PS, vec![A])],
        args: vec![MMProofTree::Hyp(1), MMProofTree::Hyp(0)],
    };
    let ax1_app = MMProofTree::Apply {
        assertion: "mm.ax-1".to_string(),
        subst: vec![(PH, vec![A]), (PS, vec![B])],
        args: vec![MMProofTree::Hyp(0), MMProofTree::Hyp(1)],
    };
    // TAMPER: swap the two essential premises (|- A and |- (A → (B → A))).
    let bad = MMProofTree::Apply {
        assertion: "mm.ax-mp".to_string(),
        subst: vec![(PH, vec![A]), (PS, ba)],
        args: vec![
            MMProofTree::Hyp(0),
            wi_app,
            ax1_app,             // wrong slot (should be |- A)
            MMProofTree::Hyp(2), // wrong slot (should be |- (A → (B → A)))
        ],
    };
    let res = verify_metamath_theorem(
        &mut env,
        "mm.a1i_bad",
        &[(WFF, A), (WFF, B)],
        &[turn(&[A])],
        &turn(&imp_form(&[B], &[A])),
        &bad,
    );
    assert!(
        res.is_err(),
        "importer must reject an invalid proof tree (got Ok)"
    );
}

/// Two `applySubst` terms with DIFFERENT substitutions and DIFFERENT base forms
/// that reduce to the SAME form must be definitionally equal. This is the exact
/// shape the kernel sees when checking a Metamath proof step that reuses a lemma:
/// the argument's inferred type `applySubst σ_arg concl_arg` vs the expected
/// `applySubst σ_top hyp_top`. (Pins the set.mm reuse false-negative.)
#[test]
fn test_defeq_distinct_subst_same_form_small() {
    let env = env();
    let tc = TypeChecker::new(&env);
    // applySubst {PH:[A,B]} [PH] ⇒ [A,B];  applySubst {PS:[A,B]} [PS] ⇒ [A,B]
    let a = apply_subst_app(&[(PH, &[A, B])], &[PH]);
    let b = apply_subst_app(&[(PS, &[A, B])], &[PS]);
    assert!(
        tc.is_def_eq(&a, &b),
        "distinct-subst same-form (small) must be def-eq"
    );
}

/// Same shape but with a LARGER reduced form (many symbols) and a multi-binding
/// substitution — closer to the deep set.mm reuse terms.
#[test]
fn test_defeq_distinct_subst_same_form_large() {
    let env = env();
    let tc = TypeChecker::new(&env);
    // Build a FLAT ~240-symbol base form (linear, like a real set.mm formula),
    // then substitute it under two different variable names.
    let mut big: Vec<u64> = Vec::new();
    for _ in 0..60 {
        big.extend_from_slice(&[OPEN, PH, ARROW, CLOSE]);
    }
    // a = applySubst {PH := big} [PH]  ⇒ big
    let a = apply_subst_app(&[(PH, &big)], &[PH]);
    // b = applySubst {PS := big} [PS]  ⇒ big  (different var, same value)
    let b = apply_subst_app(&[(PS, &big)], &[PS]);
    assert!(
        tc.is_def_eq(&a, &b),
        "distinct-subst same-form (large) must be def-eq"
    );
}

/// Mirrors the simprim trigger: a MERGE substitution (two distinct vars mapped to
/// the same value) against a different base/subst that reduces to the SAME form.
/// `applySubst {PH:[A], PS:[B], CH:[B]} [( PH -> CH )]` vs
/// `applySubst {PH:[A], PS:[B]}        [( PH -> PS )]` both ⇒ `( A -> B )`.
const CH: u64 = 12;
#[test]
fn test_defeq_merge_subst_same_form() {
    let env = env();
    let tc = TypeChecker::new(&env);
    // grow to a realistic size: repeat the ( PH -> CH ) / ( PH -> PS ) block.
    let mut base1: Vec<u64> = Vec::new();
    let mut base2: Vec<u64> = Vec::new();
    for _ in 0..30 {
        base1.extend_from_slice(&[OPEN, PH, ARROW, CH, CLOSE]);
        base2.extend_from_slice(&[OPEN, PH, ARROW, PS, CLOSE]);
    }
    // σ1 merges CH and PS onto the same value B.
    let a = apply_subst_app(&[(PH, &[A]), (PS, &[B]), (CH, &[B])], &base1);
    let b = apply_subst_app(&[(PH, &[A]), (PS, &[B])], &base2);
    assert!(tc.is_def_eq(&a, &b), "merge-subst same-form must be def-eq");
}

/// M12 — DISJOINT-VARIABLE ($d) SOUNDNESS PRIMITIVE. `disjPair vars σ x y`
/// reducibly recomputes "the variables of σ(x) and σ(y) are disjoint" on ground
/// data: it reduces to `Bool.true` when σ keeps them apart and `Bool.false` when
/// σ collapses them onto a shared variable. The decisive soundness check is that
/// a $d-VIOLATING instance cannot be certified `= Bool.true` — so a guard arrow
/// `Eq Bool (disjPair …) Bool.true` makes the kernel itself enforce $d.
#[test]
fn test_dv_disjpair_reduces_and_rejects_violation() {
    let env = env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    const X: u64 = 10; // $d variable x
    const Y: u64 = 11; // $d variable ph/y
    const V: u64 = 20; // a concrete variable code
    const W: u64 = 21; // another concrete variable code
    let vars = nat_list_lit(&[V, W]); // the variable universe
    let dp = |s: Expr| {
        Expr::apps(
            Expr::const_str(names::DISJ_PAIR),
            [vars.clone(), s, Expr::nat_lit(X), Expr::nat_lit(Y)],
        )
    };

    // σ1 keeps x,ph disjoint: x := [V], ph := [W]  → disjPair = Bool.true.
    let s1 = subst_fn(&[(X, &[V][..]), (Y, &[W][..])]);
    tc.check_type(&eq_refl_bool(btrue()), &eq_bool(dp(s1), btrue()))
        .expect("disjoint substitution must reduce disjPair to Bool.true");

    // σ2 COLLAPSES them: x := [V], ph := [V]  → disjPair = Bool.false.
    let s2 = subst_fn(&[(X, &[V][..]), (Y, &[V][..])]);
    tc.check_type(&eq_refl_bool(bfalse()), &eq_bool(dp(s2.clone()), bfalse()))
        .expect("collapsing substitution must reduce disjPair to Bool.false");

    // SOUNDNESS LITMUS: the $d-violating instance must NOT be certifiable `= true`.
    let res = tc.check_type(&eq_refl_bool(btrue()), &eq_bool(dp(s2), btrue()));
    assert!(
        res.is_err(),
        "a $d-VIOLATING disjPair must not typecheck as Bool.true (kernel enforces $d)"
    );
}

/// M12 — the GUARD ARROW end to end. A $d-bearing assertion is encoded as
/// `Π σ, Eq Bool (disjPair vars σ x ph) Bool.true → MMThm(applySubst σ concl)`:
/// the conclusion sits BEHIND a guard that the kernel can only let through when
/// the $d holds. Applying it at a DISJOINT ground substitution (guard discharged
/// by `Eq.refl Bool.true`) kernel-verifies; applying it at a COLLAPSING one makes
/// `disjPair` reduce to `Bool.false`, so the guard domain is `Eq Bool false true`,
/// the `Eq.refl true` witness is ill-typed, and `add_decl` REJECTS. This is the
/// kernel-level analogue of soundly verifying ax-5 (`|- (ph -> A. x ph)`, $d x ph).
#[test]
fn test_dv_guard_arrow_accepts_disjoint_rejects_violation() {
    let mut env = env();
    // MMThm is registered by the assertion registrar, not init_metamath_reflect.
    register_metamath_assertions(&mut env, &[]).expect("register MMThm");
    const X: u64 = 10;
    const PH: u64 = 11;
    const V: u64 = 20;
    const W: u64 = 21;
    const IMP: u64 = 30;
    const FA: u64 = 31;
    let vars = nat_list_lit(&[V, W]);
    let concl = [IMP, PH, FA, X, PH]; // an ax-5-shaped form mentioning x and ph

    let disjpair = |s: &Expr| {
        Expr::apps(
            Expr::const_str(names::DISJ_PAIR),
            [vars.clone(), s.clone(), Expr::nat_lit(X), Expr::nat_lit(PH)],
        )
    };
    // mm.ax5demo : Π σ, Eq Bool (disjPair vars σ X PH) true → MMThm(applySubst σ concl)
    let ax_ty = {
        let mut b = EnvDeclBuilder::new();
        let (s_id, s) = b.fresh_local(subst_ty());
        let guard = eq_bool(disjpair(&s), btrue());
        let conc = mmthm_of(applysubst2(s.clone(), nat_list_lit(&concl)));
        let arrow = Expr::arrow(guard, conc);
        b.finish(b.mk_pi(s_id, BinderInfo::Default, subst_ty(), arrow))
    };
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("mm.ax5demo"),
        level_params: vec![],
        type_: ax_ty,
    })
    .expect("register synthetic guarded axiom");
    let ax = Expr::const_str("mm.ax5demo");

    // ACCEPT: σ1 disjoint (x:=[V], ph:=[W]); guard discharged by Eq.refl true.
    let s1 = subst_fn(&[(X, &[V][..]), (PH, &[W][..])]);
    let value1 = Expr::apps(ax.clone(), [s1.clone(), eq_refl_bool(btrue())]);
    let ty1 = mmthm_of(applysubst2(s1, nat_list_lit(&concl)));
    env.add_decl(Declaration::Theorem {
        name: Name::from_string("mm.ax5demo_ok"),
        level_params: vec![],
        type_: ty1,
        value: value1,
    })
    .expect("guarded axiom at a DISJOINT substitution must kernel-verify");

    // REJECT: σ2 collapses x,ph (x:=[V], ph:=[V]) → disjPair reduces to Bool.false.
    let s2 = subst_fn(&[(X, &[V][..]), (PH, &[V][..])]);
    let value2 = Expr::apps(ax, [s2.clone(), eq_refl_bool(btrue())]);
    let ty2 = mmthm_of(applysubst2(s2, nat_list_lit(&concl)));
    let res = env.add_decl(Declaration::Theorem {
        name: Name::from_string("mm.ax5demo_bad"),
        level_params: vec![],
        type_: ty2,
        value: value2,
    });
    assert!(
        res.is_err(),
        "guarded axiom at a $d-VIOLATING substitution must be REJECTED by add_decl"
    );
}

/// M12 — full GUARDED IMPORT PATH. `register_metamath_assertions` adds a `disjPair`
/// guard arrow for a `$d`-bearing assertion, and `verify_metamath_theorem_guarded`
/// discharges it with a ground `Eq.refl Bool.true`. A DISJOINT instance verifies;
/// a COLLAPSING one (the substituted variables overlap) makes `disjPair` reduce to
/// `Bool.false`, the guard is unsatisfiable, and `add_decl` REJECTS — end to end.
#[test]
fn test_dv_register_and_verify_guarded() {
    const TURN: u64 = 4;
    const WFF: u64 = 5;
    const SETVAR: u64 = 6;
    const FA: u64 = 7; // A. (forall)
    const X: u64 = 10;
    const PH: u64 = 11;
    const V: u64 = 20;
    const W: u64 = 21;

    // A synthetic $d-bearing axiom  mm.dvax : (… $d x ph) ⊢ ( A. x ph ).
    let dvax = MMAssertion {
        name: "mm.dvax".to_string(),
        float_hyps: vec![(SETVAR, X), (WFF, PH)],
        essential_hyps: vec![],
        conclusion: vec![TURN, FA, X, PH],
        disjoints: vec![(X, PH)],
        // The universe must contain BOTH the assertion variables (X, PH — so
        // `applySubstV` substitutes them) and the image variables (V, W — so
        // `disjPair` classifies them and detects a collapse).
        var_universe: vec![X, PH, V, W],
    };
    let guards: std::collections::HashMap<String, usize> =
        [("mm.dvax".to_string(), 1usize)].into_iter().collect();

    // ACCEPT: instantiate at a DISJOINT ground substitution (x:=v, ph:=w, v≠w).
    {
        let mut env = env();
        register_metamath_assertions(&mut env, std::slice::from_ref(&dvax)).expect("register dvax");
        let proof = MMProofTree::Apply {
            assertion: "mm.dvax".to_string(),
            subst: vec![(X, vec![V]), (PH, vec![W])],
            args: vec![MMProofTree::Hyp(0), MMProofTree::Hyp(1)],
        };
        verify_metamath_theorem_guarded(
            &mut env,
            "mm.dvax_ok",
            &[(SETVAR, V), (WFF, W)],
            &[],
            &[TURN, FA, V, W],
            &proof,
            &guards,
        )
        .expect("$d-bearing axiom at a DISJOINT substitution must kernel-verify");
    }

    // REJECT: instantiate at a COLLAPSING substitution (x:=v, ph:=v) → $d violated.
    {
        let mut env = env();
        register_metamath_assertions(&mut env, std::slice::from_ref(&dvax)).expect("register dvax");
        let proof = MMProofTree::Apply {
            assertion: "mm.dvax".to_string(),
            subst: vec![(X, vec![V]), (PH, vec![V])],
            args: vec![MMProofTree::Hyp(0), MMProofTree::Hyp(1)],
        };
        let res = verify_metamath_theorem_guarded(
            &mut env,
            "mm.dvax_bad",
            &[(SETVAR, V), (WFF, V)],
            &[],
            &[TURN, FA, V, V],
            &proof,
            &guards,
        );
        assert!(
            res.is_err(),
            "$d-bearing axiom at a COLLAPSING substitution must be REJECTED"
        );
    }
}

/// SOUNDNESS — a `$f` float-axiom is the GROUND typing of its variable, NOT the
/// all-σ claim. `register_float_axiom` registers `mm.<v> : Π σ, MMThm([tc, var])`
/// whose body IGNORES σ, so applying it at ANY σ yields exactly `MMThm([tc, var])`
/// — it can never be coerced into `MMThm([tc, σ(var)])` (which for a type-incorrect
/// σ, e.g. `[wff, <a setvar>]`, would be false and would pollute the MMThm base).
#[test]
fn test_float_axiom_is_ground_typing_not_sigma() {
    let mut env = env();
    register_metamath_assertions(&mut env, &[]).expect("register MMThm");
    const WFF: u64 = 5;
    const PH: u64 = 11;
    const X: u64 = 20;
    register_float_axiom(&mut env, "mm.wph", WFF, PH).expect("register float axiom");
    let tc = TypeChecker::with_mode(&env, env.mode());

    // Applied at σ mapping ph := x, the body still ignores σ: type is MMThm([wff, ph]).
    let app = Expr::app(Expr::const_str("mm.wph"), subst_fn(&[(PH, &[X][..])]));
    tc.check_type(&app, &mmthm_of(nat_list_lit(&[WFF, PH])))
        .expect("float-axiom yields the GROUND typing MMThm([wff, ph])");

    // SOUNDNESS LITMUS: it must NOT prove the σ-image typing MMThm([wff, x]).
    assert!(
        tc.check_type(&app, &mmthm_of(nat_list_lit(&[WFF, X])))
            .is_err(),
        "float-axiom must NOT claim MMThm([wff, σ(ph)]) — that would pollute the MMThm base"
    );
}

/// M13 — `applySubstV` (constant-fixing substitution) substitutes VARIABLES and
/// leaves CONSTANTS fixed by construction, regardless of σ. This is what makes
/// `varsOf`/distribution lemmas true for any σ (the keystone for schematic
/// `$d`/dummy reuse). Proved out by a worktree swarm; ported + re-verified here.
#[test]
fn test_apply_subst_v_fixes_constants_substitutes_vars() {
    let env = env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let vars = nat_list_lit(&[PH, PS]); // PH,PS are variables; OPEN/ARROW/CLOSE are not

    // Substitutes the variables: ( ph -> ps )[ph:=A, ps:=B] = ( A -> B ).
    let s = subst_fn(&[(PH, &[A][..]), (PS, &[B][..])]);
    let lhs = apply_subst_v_app(vars.clone(), s, nat_list_lit(&[OPEN, PH, ARROW, PS, CLOSE]));
    let expected = nat_list_lit(&[OPEN, A, ARROW, B, CLOSE]);
    tc.check_type(
        &eq_refl_list_nat(expected.clone()),
        &eq_list_nat(lhs, expected),
    )
    .expect("applySubstV substitutes variables, fixes constants");

    // LITMUS: a σ aimed at the CONSTANT `OPEN` is IGNORED (OPEN ∉ vars).
    let s2 = subst_fn(&[(OPEN, &[A][..])]);
    let lhs2 = apply_subst_v_app(vars, s2, nat_list_lit(&[OPEN, PH, CLOSE]));
    let exp2 = nat_list_lit(&[OPEN, PH, CLOSE]);
    tc.check_type(&eq_refl_list_nat(exp2.clone()), &eq_list_nat(lhs2, exp2))
        .expect("applySubstV must IGNORE a substitution aimed at a constant");
}

/// M13 — the append-distribution lemmas (`varsOf_append`, `applySubstV_append`)
/// are registered as kernel `Theorem`s and apply at concrete instances. (Their
/// proofs already full-kernel-typecheck at `init_metamath_reflect`; this confirms
/// the registered constants have the expected types.)
#[test]
fn test_vars_subst_lemmas_registered_and_instantiable() {
    let env = env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let vars = nat_list_lit(&[PH, PS]);
    let xs = nat_list_lit(&[OPEN, PH]);
    let ys = nat_list_lit(&[PS, CLOSE]);
    let inst = Expr::apps(
        Expr::const_str(names::VARSOF_APPEND),
        [vars.clone(), xs.clone(), ys.clone()],
    );
    let expected = eq_list_nat(
        vars_of_app(vars.clone(), append2(xs.clone(), ys.clone())),
        append2(vars_of_app(vars.clone(), xs), vars_of_app(vars, ys)),
    );
    tc.check_type(&inst, &expected)
        .expect("varsOf_append applies at a concrete instance with the expected type");
}

/// M13 — `append_nil_right` and the `varsOf`/`applySubstV` SINGLETON lemmas apply
/// at concrete instances (they already full-kernel-typecheck at init; this confirms
/// the registered constants' types). These close the head-case of the full
/// `varsOf`-distribution lemma (the remaining step is the `Bool.rec` convoy on
/// `memNat h vars`).
#[test]
fn test_append_nil_right_and_singletons_instantiable() {
    let env = env();
    let tc = TypeChecker::with_mode(&env, env.mode());

    // append_nil_right [A,B] : append [A,B] [] = [A,B]
    let xs = nat_list_lit(&[A, B]);
    let anr = Expr::app(Expr::const_str(names::APPEND_NIL_RIGHT), xs.clone());
    tc.check_type(
        &anr,
        &eq_list_nat(append2(xs.clone(), nat_list_lit(&[])), xs),
    )
    .expect("append_nil_right instance has the expected type");

    // varsOf_singleton [PH] PH : varsOf [PH] [PH] = iteList (memNat PH [PH]) [PH] []
    let vars = nat_list_lit(&[PH]);
    let vs = Expr::apps(
        Expr::const_str(names::VARSOF_SINGLETON),
        [vars.clone(), Expr::nat_lit(PH)],
    );
    let single = nat_list_lit(&[PH]);
    let rhs = ite_list_app(
        mem_nat_app(Expr::nat_lit(PH), vars.clone()),
        single.clone(),
        nat_list_lit(&[]),
    );
    tc.check_type(&vs, &eq_list_nat(vars_of_app(vars, single), rhs))
        .expect("varsOf_singleton instance has the expected type");
}

/// M13 KEYSTONE — the full `varsOf`-distribution lemma is kernel-verified:
/// `varsOf vars (applySubstV vars σ e) = applySubstV vars (λv. varsOf vars (σ v))
/// (varsOf vars e)`. (Proved by `List.rec` induction + the convoy head identity at
/// `init`; this confirms it instantiates with the expected type — the unlock for
/// schematic `$d`/dummy theorem reuse.)
#[test]
fn test_varsof_applysubstv_keystone_instantiable() {
    let env = env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let vars = nat_list_lit(&[PH, PS]);
    let sigma = subst_fn(&[(PH, &[A, B][..])]);
    let e = nat_list_lit(&[OPEN, PH, CLOSE]);
    let inst = Expr::apps(
        Expr::const_str(names::VARSOF_APPLYSUBSTV),
        [vars.clone(), sigma.clone(), e.clone()],
    );
    // φ = λ v, varsOf vars (σ v)
    let phi = Expr::lam(
        BinderInfo::Default,
        Expr::const_str("Nat"),
        vars_of_app(vars.clone(), Expr::app(sigma.clone(), Expr::bvar(0))),
    );
    let expected = eq_list_nat(
        vars_of_app(
            vars.clone(),
            apply_subst_v_app(vars.clone(), sigma, e.clone()),
        ),
        apply_subst_v_app(vars.clone(), phi, vars_of_app(vars, e)),
    );
    tc.check_type(&inst, &expected)
        .expect("varsOf_applySubstV keystone instantiates with the expected type");
}

/// M13 — SINGLE-VAR SCHEMATIC $d DISCHARGE. The decisive capability for schematic
/// reuse of (single-variable) $d theorems: a step's obligation
/// `disjPair vu (comp σ σn) A B = true` is discharged from the THEOREM's guard
/// hypothesis `disjPair vu σ X Y = true` (σn maps A:=[X], B:=[Y]) — NO encoding
/// switch needed, because `applySubst σ [X] = append (σ X) []` and
/// `varsOf vu (append (σ X) []) = varsOf vu (σ X)` via the proven `varsOf_append`
/// + `append_nil_right`. If this Theorem registers, the discharge typechecks.
#[test]
fn test_schematic_dv_discharge_single_var() {
    let mut env = env();
    const A: u64 = 10;
    const B: u64 = 11;
    const X: u64 = 20;
    const Y: u64 = 21;
    let vu = nat_list_lit(&[X, Y]);
    let nil = || list_nil(Expr::const_str("Nat"));
    let sn = subst_fn(&[(A, &[X][..]), (B, &[Y][..])]);

    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (sig_id, sig) = b.fresh_local(subst_ty());
        let guard = eq_bool(disjpair_app(vu.clone(), sig.clone(), X, Y), btrue());
        let comp = comp_subst(&sig, &sn);
        let obligation = eq_bool(disjpair_app(vu.clone(), comp, A, B), btrue());
        let arrow = Expr::arrow(guard, obligation);
        b.finish(b.mk_pi(sig_id, BinderInfo::Default, subst_ty(), arrow))
    };
    let val = {
        let mut b = EnvDeclBuilder::new();
        let (sig_id, sig) = b.fresh_local(subst_ty());
        let guard_ty = eq_bool(disjpair_app(vu.clone(), sig.clone(), X, Y), btrue());
        let (hd_id, hd) = b.fresh_local(guard_ty.clone());
        let comp = comp_subst(&sig, &sn);
        let sigx = Expr::app(sig.clone(), Expr::nat_lit(X));
        let sigy = Expr::app(sig.clone(), Expr::nat_lit(Y));
        let lx = vars_of_app(vu.clone(), append2(sigx.clone(), nil()));
        let rx = vars_of_app(vu.clone(), sigx.clone());
        let ly = vars_of_app(vu.clone(), append2(sigy.clone(), nil()));
        let ry = vars_of_app(vu.clone(), sigy.clone());
        let mid = |r: &Expr| append2(r.clone(), vars_of_app(vu.clone(), nil()));
        let cast_x = eq_trans_list(
            lx.clone(),
            mid(&rx),
            rx.clone(),
            Expr::apps(
                Expr::const_str(names::VARSOF_APPEND),
                [vu.clone(), sigx.clone(), nil()],
            ),
            Expr::app(Expr::const_str(names::APPEND_NIL_RIGHT), rx.clone()),
        );
        let cast_y = eq_trans_list(
            ly.clone(),
            mid(&ry),
            ry.clone(),
            Expr::apps(
                Expr::const_str(names::VARSOF_APPEND),
                [vu.clone(), sigy.clone(), nil()],
            ),
            Expr::app(Expr::const_str(names::APPEND_NIL_RIGHT), ry.clone()),
        );
        let f_left = Expr::lam(
            BinderInfo::Default,
            list_nat(),
            list_disjoint_app(Expr::bvar(0), ly.clone()),
        );
        let step_a = congr_arg_list_bool(lx.clone(), rx.clone(), f_left, cast_x);
        let f_right = Expr::lam(
            BinderInfo::Default,
            list_nat(),
            list_disjoint_app(rx.clone(), Expr::bvar(0)),
        );
        let step_b = congr_arg_list_bool(ly.clone(), ry.clone(), f_right, cast_y);
        let bridge = eq_trans_bool(
            list_disjoint_app(lx.clone(), ly.clone()),
            list_disjoint_app(rx.clone(), ly.clone()),
            list_disjoint_app(rx.clone(), ry.clone()),
            step_a,
            step_b,
        );
        let dp_comp = disjpair_app(vu.clone(), comp, A, B);
        let dp_sig = disjpair_app(vu.clone(), sig.clone(), X, Y);
        let discharge = eq_trans_bool(dp_comp, dp_sig, btrue(), bridge, hd);
        let r = b.mk_lam(hd_id, BinderInfo::Default, guard_ty, discharge);
        b.finish(b.mk_lam(sig_id, BinderInfo::Default, subst_ty(), r))
    };
    env.add_decl(Declaration::Theorem {
        name: Name::from_string("test.dvDischargeSingleVar"),
        level_params: vec![],
        type_: ty,
        value: val,
    })
    .expect("single-var $d discharge from the guard hypothesis must typecheck");
}

/// M13 — schematic `$d` THEOREM end to end. Register a `$d`-bearing axiom (guarded,
/// via `register_metamath_assertions`), then verify a SCHEMATIC `$d`-theorem that
/// applies it at a single-variable substitution — its step `$d` obligation is
/// discharged from the theorem's own guard hypothesis. The theorem registers as
/// `mm.T : Π σ, (disjPair vu σ X Y = true …) → … → MMThm(applySubst σ C)`, hence is
/// SCHEMATICALLY REUSABLE. This is the capability that lifts (single-variable)
/// `$d` theorems off the ground-only path.
#[test]
fn test_schematic_dv_theorem_registers() {
    let mut env = env();
    const TURN: u64 = 4;
    const SETVAR: u64 = 6;
    const A: u64 = 10;
    const B: u64 = 11;
    const X: u64 = 20;
    const Y: u64 = 21;
    let vu_codes = [X, Y, A, B];

    // $d-bearing axiom mm.dax : (… $d A B) ⊢ ( A B ), with float hyps for A, B.
    let dax = MMAssertion {
        name: "mm.dax".to_string(),
        float_hyps: vec![(SETVAR, A), (SETVAR, B)],
        essential_hyps: vec![],
        conclusion: vec![TURN, A, B],
        disjoints: vec![(A, B)],
        var_universe: vu_codes.to_vec(),
    };
    register_metamath_assertions(&mut env, std::slice::from_ref(&dax)).expect("register dax");

    // sigs: mm.dax's (hyp forms, conclusion).
    let sigs: hashbrown::HashMap<String, AssertionSig> = [(
        "mm.dax".to_string(),
        (vec![vec![SETVAR, A], vec![SETVAR, B]], vec![TURN, A, B]),
    )]
    .into_iter()
    .collect();
    let guards: hashbrown::HashMap<String, Vec<(u64, u64)>> =
        [("mm.dax".to_string(), vec![(A, B)])].into_iter().collect();

    // mm.T : (… $d X Y) ⊢ ( X Y ), proved by applying mm.dax at {A:=X, B:=Y}.
    let proof = MMProofTree::Apply {
        assertion: "mm.dax".to_string(),
        subst: vec![(A, vec![X]), (B, vec![Y])],
        args: vec![MMProofTree::Hyp(0), MMProofTree::Hyp(1)],
    };
    verify_metamath_theorem_schematic_dv(
        &mut env,
        "mm.dthm",
        &[(SETVAR, X), (SETVAR, Y)],
        &[],
        &[TURN, X, Y],
        &proof,
        &sigs,
        &[(X, Y)],
        &vu_codes,
        &guards,
        &[],
        &hashbrown::HashSet::new(),
        &hashbrown::HashMap::new(),
    )
    .expect("schematic $d theorem (single-var discharge from its guard) must register");

    // It is registered as a schematic constant — i.e. reusable.
    assert!(env.get_const(&Name::from_string("mm.dthm")).is_some());
}

/// M13 — COMPOUND `$d` discharge via the KEYSTONE. The capability that reaches the
/// bulk of predicate logic (ax-5: `$d x ph` with `ph` substituted to a wff). With
/// the constant-fixing `comp_v`, a step obligation `disjPair vu (comp_v σ σn) A B`
/// where `σn B` is a COMPOUND form `[WFF, v]` discharges from the theorem's guard
/// `disjPair vu σ X v`: `varsOf vu (applySubstV vu σ [WFF,v])` distributes (keystone
/// `varsOf_applySubstV`) to `varsOf vu (σ v)` (the constant WFF is dropped), so the
/// obligation casts to the single guard. If the Theorem registers, this works.
#[test]
fn test_compound_dv_discharge_via_keystone() {
    let mut env = env();
    const WFF: u64 = 5; // a constant typecode (NOT in the variable universe)
    const A: u64 = 10;
    const B: u64 = 11;
    const X: u64 = 20;
    const V: u64 = 21;
    let vu = nat_list_lit(&[X, V]); // variables; WFF is a constant
    let nil = || list_nil(Expr::const_str("Nat"));
    // σn: A := [X] (single var), B := [WFF, V] (a compound wff form).
    let sn = subst_fn(&[(A, &[X][..]), (B, &[WFF, V][..])]);
    let w = nat_list_lit(&[WFF, V]);

    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (sig_id, sig) = b.fresh_local(subst_ty());
        let guard = eq_bool(disjpair_app(vu.clone(), sig.clone(), X, V), btrue());
        let comp = comp_subst_v(&vu, &sig, &sn);
        let obligation = eq_bool(disjpair_app(vu.clone(), comp, A, B), btrue());
        b.finish(b.mk_pi(
            sig_id,
            BinderInfo::Default,
            subst_ty(),
            Expr::arrow(guard, obligation),
        ))
    };
    let val = {
        let mut b = EnvDeclBuilder::new();
        let (sig_id, sig) = b.fresh_local(subst_ty());
        let guard_ty = eq_bool(disjpair_app(vu.clone(), sig.clone(), X, V), btrue());
        let (hd_id, hd) = b.fresh_local(guard_ty.clone());
        let comp = comp_subst_v(&vu, &sig, &sn);
        let sigx = Expr::app(sig.clone(), Expr::nat_lit(X));
        let sigv = Expr::app(sig.clone(), Expr::nat_lit(V));
        let rx = vars_of_app(vu.clone(), sigx.clone()); // varsOf vu (σ X)
        let rv = vars_of_app(vu.clone(), sigv.clone()); // varsOf vu (σ V)
                                                        // cast_a : varsOf vu (comp_v A) = varsOf vu (σ X)   [comp_v A ≡ append (σX) []]
        let la = vars_of_app(vu.clone(), append2(sigx.clone(), nil()));
        let cast_a = eq_trans_list(
            la.clone(),
            append2(rx.clone(), vars_of_app(vu.clone(), nil())),
            rx.clone(),
            Expr::apps(
                Expr::const_str(names::VARSOF_APPEND),
                [vu.clone(), sigx.clone(), nil()],
            ),
            Expr::app(Expr::const_str(names::APPEND_NIL_RIGHT), rx.clone()),
        );
        // cast_b : varsOf vu (applySubstV vu σ W) = varsOf vu (σ V)  [keystone + append_nil_right]
        let phi = Expr::lam(
            BinderInfo::Default,
            Expr::const_str("Nat"),
            vars_of_app(vu.clone(), Expr::app(sig.clone(), Expr::bvar(0))),
        );
        let lb = vars_of_app(
            vu.clone(),
            apply_subst_v_app(vu.clone(), sig.clone(), w.clone()),
        );
        let keystone_rhs = apply_subst_v_app(vu.clone(), phi, vars_of_app(vu.clone(), w.clone()));
        let cast_b = eq_trans_list(
            lb.clone(),
            keystone_rhs,
            rv.clone(),
            Expr::apps(
                Expr::const_str(names::VARSOF_APPLYSUBSTV),
                [vu.clone(), sig.clone(), w.clone()],
            ),
            Expr::app(Expr::const_str(names::APPEND_NIL_RIGHT), rv.clone()),
        );
        // bridge : listDisjoint la lb = listDisjoint rx rv
        let f_left = Expr::lam(
            BinderInfo::Default,
            list_nat(),
            list_disjoint_app(Expr::bvar(0), lb.clone()),
        );
        let step_a = congr_arg_list_bool(la.clone(), rx.clone(), f_left, cast_a);
        let f_right = Expr::lam(
            BinderInfo::Default,
            list_nat(),
            list_disjoint_app(rx.clone(), Expr::bvar(0)),
        );
        let step_b = congr_arg_list_bool(lb.clone(), rv.clone(), f_right, cast_b);
        let bridge = eq_trans_bool(
            list_disjoint_app(la.clone(), lb.clone()),
            list_disjoint_app(rx.clone(), lb),
            list_disjoint_app(rx.clone(), rv),
            step_a,
            step_b,
        );
        let discharge = eq_trans_bool(
            disjpair_app(vu.clone(), comp, A, B),
            disjpair_app(vu.clone(), sig.clone(), X, V),
            btrue(),
            bridge,
            hd,
        );
        let r = b.mk_lam(hd_id, BinderInfo::Default, guard_ty, discharge);
        b.finish(b.mk_lam(sig_id, BinderInfo::Default, subst_ty(), r))
    };
    env.add_decl(Declaration::Theorem {
        name: Name::from_string("test.compoundDvDischarge"),
        level_params: vec![],
        type_: ty,
        value: val,
    })
    .expect("compound $d discharge via the keystone must typecheck");
}

/// DUMMY-REUSE CORE: the float-cast via a σ-fixes-d guard. A dummy d's float
/// is registered σ-IGNORED (`Π σ, MMThm([tc,d])`), but the schematic path needs
/// `MMThm(applySubstV vu σ [tc,d])`. Given the guard `hd : applySubstV vu σ [d] =
/// [d]`, the two are equal: `applySubstV vu σ [tc,d] ≡ append [tc] (applySubstV vu
/// σ [d])` and `[tc,d] ≡ append [tc] [d]`, so `congrArg (append [tc]) hd` bridges
/// them. This is the cast that lets a σ-ignored float slot into the schematic
/// `Π σ` form (the keystone of sound dummy reuse). If the Theorem registers, the
/// cast is kernel-validated.
#[test]
fn test_dummy_float_cast_via_sigma_fixes_d_guard() {
    let mut env = env();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Clean.MM.MMThm"),
        level_params: vec![],
        type_: Expr::arrow(list_nat(), Expr::prop()),
    })
    .expect("register MMThm");
    const TC: u64 = 5; // a constant typecode (NOT in the variable universe)
    const D: u64 = 30; // the dummy variable
    let vu = nat_list_lit(&[D]);
    let tcd = nat_list_lit(&[TC, D]);
    let d1 = nat_list_lit(&[D]);
    let tc1 = nat_list_lit(&[TC]);

    // f = λ e:List Nat, append [TC] e   (List Nat → List Nat)
    let cast_f = || {
        Expr::lam(
            BinderInfo::Default,
            list_nat(),
            append2(tc1.clone(), Expr::bvar(0)),
        )
    };
    // @congrArg.{1,1} (List Nat) (List Nat) a1 a2 f h
    let congr_list_list = |a1: Expr, a2: Expr, f: Expr, h: Expr| {
        let l1 = Level::succ(Level::zero());
        Expr::apps(
            Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
            [list_nat(), list_nat(), a1, a2, f, h],
        )
    };
    // @Eq.{1} (List Nat) x y
    let eq_list = |x: Expr, y: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [list_nat(), x, y],
        )
    };

    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (sig_id, sig) = b.fresh_local(subst_ty());
        let guard = eq_list(
            apply_subst_v_app(vu.clone(), sig.clone(), d1.clone()),
            d1.clone(),
        );
        let float_ty = mmthm(tcd.clone());
        let goal = mmthm(apply_subst_v_app(vu.clone(), sig.clone(), tcd.clone()));
        b.finish(b.mk_pi(
            sig_id,
            BinderInfo::Default,
            subst_ty(),
            Expr::arrow(guard, Expr::arrow(float_ty, goal)),
        ))
    };
    let val = {
        let mut b = EnvDeclBuilder::new();
        let (sig_id, sig) = b.fresh_local(subst_ty());
        let guard_ty = eq_list(
            apply_subst_v_app(vu.clone(), sig.clone(), d1.clone()),
            d1.clone(),
        );
        let (hd_id, hd) = b.fresh_local(guard_ty.clone());
        let float_ty = mmthm(tcd.clone());
        let (f_id, fterm) = b.fresh_local(float_ty.clone());
        // hform : applySubstV vu σ [TC,D] = [TC,D]   (via congrArg (append [TC]) hd)
        let lhs = apply_subst_v_app(vu.clone(), sig.clone(), tcd.clone());
        let hform = congr_list_list(
            apply_subst_v_app(vu.clone(), sig.clone(), d1.clone()),
            d1.clone(),
            cast_f(),
            hd,
        );
        let h_mmthm = congr_arg_mmthm(lhs.clone(), tcd.clone(), hform);
        let cast = eq_mpr_mmthm(lhs, tcd.clone(), h_mmthm, fterm);
        let inner = b.mk_lam(f_id, BinderInfo::Default, float_ty, cast);
        let inner = b.mk_lam(hd_id, BinderInfo::Default, guard_ty, inner);
        b.finish(b.mk_lam(sig_id, BinderInfo::Default, subst_ty(), inner))
    };
    env.add_decl(Declaration::Theorem {
        name: Name::from_string("test.dummyFloatCast"),
        level_params: vec![],
        type_: ty,
        value: val,
    })
    .expect("float cast via σ-fixes-d guard must typecheck");
}

/// M13 — TRANSITIVE dummy reuse discharge. When theorem S reuses dummy-theorem T,
/// it instantiates T's `Π σ` at `comp_v(vu, σ_S, σn_S)`, so T's σ-fixes-d obligation
/// becomes `applySubstV vu comp_v [d] = [d]` — with σ_S an OPAQUE schematic var. This
/// validates that S discharges it from ITS OWN propagated guard
/// `fix_d_S : applySubstV vu σ_S [d] = [d]`: `applySubstV vu comp_v [d]` reduces to
/// `append (applySubstV vu σ_S [d]) []` (since σn_S(d)=[d]), so `append_nil_right`
/// then `fix_d_S` bridge it. This is the keystone that makes transitive propagation
/// (not per-theorem-local guards) sound — the gap impl-fork-#1 found.
#[test]
fn test_dummy_transitive_fix_discharge() {
    let mut env = env();
    const D: u64 = 30; // dummy
    const V: u64 = 21; // a real var of the reusing theorem S
    const A: u64 = 40; // a real var of T, mapped to V on reuse
    let vu = nat_list_lit(&[D, V]);
    let d1 = nat_list_lit(&[D]);
    let eq_list = |x: Expr, y: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [list_nat(), x, y],
        )
    };
    // σn_S binds T's real var A := [V]; d is NOT bound (⇒ σn_S(d) = [d]).
    let sn = subst_fn(&[(A, &[V][..])]);

    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (sig_id, sig) = b.fresh_local(subst_ty()); // σ_S
        let comp = comp_subst_v(&vu, &sig, &sn);
        let obligation = eq_list(apply_subst_v_app(vu.clone(), comp, d1.clone()), d1.clone());
        let fix_hyp = eq_list(
            apply_subst_v_app(vu.clone(), sig.clone(), d1.clone()),
            d1.clone(),
        );
        b.finish(b.mk_pi(
            sig_id,
            BinderInfo::Default,
            subst_ty(),
            Expr::arrow(fix_hyp, obligation),
        ))
    };
    let val = {
        let mut b = EnvDeclBuilder::new();
        let (sig_id, sig) = b.fresh_local(subst_ty());
        let fix_ty = eq_list(
            apply_subst_v_app(vu.clone(), sig.clone(), d1.clone()),
            d1.clone(),
        );
        let (hd_id, hd) = b.fresh_local(fix_ty.clone());
        let comp = comp_subst_v(&vu, &sig, &sn);
        let mid = apply_subst_v_app(vu.clone(), sig.clone(), d1.clone()); // ≡ append (σ_S d) []
        let lhs = apply_subst_v_app(vu.clone(), comp, d1.clone()); // ≡ append mid []
        let anr = Expr::app(Expr::const_str(names::APPEND_NIL_RIGHT), mid.clone());
        let disch = eq_trans_list(lhs, mid, d1.clone(), anr, hd);
        let inner = b.mk_lam(hd_id, BinderInfo::Default, fix_ty, disch);
        b.finish(b.mk_lam(sig_id, BinderInfo::Default, subst_ty(), inner))
    };
    env.add_decl(Declaration::Theorem {
        name: Name::from_string("test.dummyTransitiveFixDischarge"),
        level_params: vec![],
        type_: ty,
        value: val,
    })
    .expect("transitive σ-fixes-d discharge at a reuse site must typecheck");
}

/// M13-dummy LITMUS (soundness). A dummy/work-variable theorem registers
/// SCHEMATICALLY through the real verify path (its `$f` float leaf cast up via the
/// σ-fixes-d guard), AND a reuse that does NOT carry the dummy's σ-fixes-d guarantee
/// is REJECTED (fail-closed) — so a context that cannot keep `d` fresh under σ can
/// never reuse it. This is the propagation discipline that blocks σ from corrupting
/// a locally-fresh dummy: no carried guard ⇒ no discharge ⇒ no acceptance.
#[test]
fn test_dummy_schematic_reuse_requires_carried_fix_guard() {
    const SETVAR: u64 = 6;
    const D: u64 = 30; // the dummy / work variable
    const V: u64 = 20; // a real variable (in the universe, not equal to d)
    let vu = vec![D, V];
    let mut env = env();
    register_float_axiom(&mut env, "mm.fD", SETVAR, D).expect("register float-axiom for D");

    let mut sigs: hashbrown::HashMap<String, AssertionSig> = hashbrown::HashMap::new();
    sigs.insert("mm.fD".to_string(), (vec![], vec![SETVAR, D]));
    let float_names: hashbrown::HashSet<String> = ["mm.fD".to_string()].into_iter().collect();
    let no_guards: hashbrown::HashMap<String, Vec<(u64, u64)>> = hashbrown::HashMap::new();
    let no_fix: hashbrown::HashMap<String, Vec<u64>> = hashbrown::HashMap::new();

    // T's proof is the dummy float leaf; T carries D as a fix-d dummy. It must
    // register SCHEMATICALLY (the float cast `MMThm([setvar,d]) → MMThm(applySubstV
    // vu σ [setvar,d])` discharges from T's own σ-fixes-d guard).
    let proof = MMProofTree::Apply {
        assertion: "mm.fD".to_string(),
        subst: vec![],
        args: vec![],
    };
    verify_metamath_theorem_schematic_dv(
        &mut env,
        "mm.dumT",
        &[],
        &[],
        &[SETVAR, D],
        &proof,
        &sigs,
        &[],
        &vu,
        &no_guards,
        &[D],
        &float_names,
        &no_fix,
    )
    .expect("dummy float-leaf theorem must register schematically via the σ-fixes-d cast");
    assert!(env.get_const(&Name::from_string("mm.dumT")).is_some());

    // Reuse setup: mm.dumT carries D as a fix-d guard.
    sigs.insert("mm.dumT".to_string(), (vec![], vec![SETVAR, D]));
    let fix_guards: hashbrown::HashMap<String, Vec<u64>> =
        [("mm.dumT".to_string(), vec![D])].into_iter().collect();
    let reuse = MMProofTree::Apply {
        assertion: "mm.dumT".to_string(),
        subst: vec![],
        args: vec![],
    };

    // REJECT: a reuser that does NOT carry D's σ-fixes-d guard (empty fix_dummies)
    // cannot discharge mm.dumT's requirement → fail-closed.
    let bad = verify_metamath_theorem_schematic_dv(
        &mut env,
        "mm.badReuse",
        &[],
        &[],
        &[SETVAR, D],
        &reuse,
        &sigs,
        &[],
        &vu,
        &no_guards,
        &[],
        &float_names,
        &fix_guards,
    );
    assert!(
        bad.is_err(),
        "reusing a dummy theorem WITHOUT carrying its σ-fixes-d guarantee must be REJECTED"
    );

    // ACCEPT: a reuser that DOES carry D transitively discharges it and verifies.
    let good = verify_metamath_theorem_schematic_dv(
        &mut env,
        "mm.goodReuse",
        &[],
        &[],
        &[SETVAR, D],
        &reuse,
        &sigs,
        &[],
        &vu,
        &no_guards,
        &[D],
        &float_names,
        &fix_guards,
    );
    good.expect("a reuser that carries the dummy's σ-fixes-d guard transitively must verify");
}

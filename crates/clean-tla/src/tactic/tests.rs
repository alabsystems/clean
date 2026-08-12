// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for TLA+ tactic engine

use super::*;
use crate::encoding::TlaFormula;

#[test]
fn test_tactic_engine_creation() {
    let engine = TlaTacticEngine::new();
    assert!(!engine.trace);
    assert_eq!(engine.timeout_ms, 10_000);
}

#[test]
fn test_prove_trivial() {
    let obligation = TlaObligation::new(TlaFormula::True);
    let result = prove_tla_obligation(&obligation);
    // TlaFormula::True should be provable via trivial or simp tactics
    assert!(!result.tactics_tried.is_empty());
    assert!(
        result.proved,
        "TlaFormula::True should be provable. Tried: {:?}, error: {:?}",
        result.tactics_tried, result.error
    );
}

#[test]
fn test_reused_engine_isolates_obligation_bindings() {
    use crate::encoding::TlaExpr;
    use crate::obligation::TlaDeclare;

    let mut engine = TlaTacticEngine::new();
    let substituted = TlaObligation::new(TlaFormula::True).with_declare(TlaDeclare::Instance {
        module: "Parameterized".to_string(),
        substitutions: vec![("p".to_string(), TlaExpr::Var("replacement".to_string()))],
    });
    assert!(engine.prove(&substituted).proved);
    assert!(
        engine.ctx.vars.contains_key("p"),
        "the first obligation should install its INSTANCE substitution"
    );

    assert!(engine.prove(&TlaObligation::new(TlaFormula::True)).proved);
    assert!(
        !engine.ctx.vars.contains_key("p"),
        "a reused engine must clear substitutions from the previous obligation"
    );
}

#[test]
fn test_tactic_selection() {
    // Temporal obligation should use temporal tactic
    let temporal = TlaObligation::new(TlaFormula::Always(Box::new(TlaFormula::True)));
    let result = prove_tla_obligation(&temporal);
    assert!(result
        .tactics_tried
        .contains(&"unfold_temporal".to_string()));

    // Induction obligation should use induction
    let induction = TlaObligation::new(TlaFormula::ForallIn(
        "n".to_string(),
        Box::new(crate::encoding::TlaExpr::Nat),
        Box::new(TlaFormula::True),
    ));
    let result = prove_tla_obligation(&induction);
    assert!(result.tactics_tried.contains(&"nat_induction".to_string()));
}

#[test]
fn test_tactic_hint_respected() {
    let obligation = TlaObligation::new(TlaFormula::True).with_tactic("blast");
    let result = prove_tla_obligation(&obligation);
    assert!(result.tactics_tried.contains(&"tableau".to_string()));
}

#[test]
fn test_temporal_unfold_always_true() {
    // □True should be provable via temporal tactics
    let obligation = TlaObligation::new(TlaFormula::Always(Box::new(TlaFormula::True)));
    let result = prove_tla_obligation(&obligation);
    assert!(result.proved, "□True should be provable, got: {result:?}");
    // Should try temporal tactics
    assert!(result
        .tactics_tried
        .contains(&"unfold_temporal".to_string()));
}

#[test]
fn test_temporal_unfold_always_true_with_hypothesis() {
    let obligation = TlaObligation::new(TlaFormula::Always(Box::new(TlaFormula::True)))
        .with_hypothesis("h1", TlaFormula::True);
    let result = prove_tla_obligation(&obligation);
    assert!(
        result.proved,
        "□True should stay provable under sequent hypotheses, got: {result:?}"
    );
    assert!(result
        .tactics_tried
        .contains(&"unfold_temporal".to_string()));
}

#[test]
fn test_temporal_unfold_eventually_true() {
    // ◇True should be provable
    let obligation = TlaObligation::new(TlaFormula::Eventually(Box::new(TlaFormula::True)));
    let result = prove_tla_obligation(&obligation);
    assert!(result
        .tactics_tried
        .contains(&"unfold_temporal".to_string()));
}

#[test]
fn test_temporal_leads_to() {
    // True ~> True should be provable
    let obligation = TlaObligation::new(TlaFormula::LeadsTo(
        Box::new(TlaFormula::True),
        Box::new(TlaFormula::True),
    ));
    let result = prove_tla_obligation(&obligation);
    assert!(result
        .tactics_tried
        .contains(&"unfold_temporal".to_string()));
}

#[test]
fn test_extract_always() {
    use clean_kernel::expr::Expr;
    use clean_kernel::name::Name;

    let engine = TlaTacticEngine::new();

    // Build: FixedPoint.TLA_always P
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let always = Expr::app(
        Expr::const_(Name::from_string("FixedPoint.TLA_always"), vec![]),
        p.clone(),
    );

    let extracted = engine.extract_always(&always);
    let extracted = extracted.expect("extract_always should extract from TLA_always P");
    assert_eq!(extracted, p);
}

#[test]
fn test_extract_eventually() {
    use clean_kernel::expr::Expr;
    use clean_kernel::name::Name;

    let engine = TlaTacticEngine::new();

    // Build: FixedPoint.TLA_eventually P
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let eventually = Expr::app(
        Expr::const_(Name::from_string("FixedPoint.TLA_eventually"), vec![]),
        p.clone(),
    );

    let extracted = engine.extract_eventually(&eventually);
    let extracted = extracted.expect("extract_eventually should extract from TLA_eventually P");
    assert_eq!(extracted, p);
}

#[test]
fn test_extract_leads_to() {
    use clean_kernel::expr::Expr;
    use clean_kernel::name::Name;

    let engine = TlaTacticEngine::new();

    // Build: FixedPoint.TLA_leads_to P Q
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);
    let leads_to = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("FixedPoint.TLA_leads_to"), vec![]),
            p.clone(),
        ),
        q.clone(),
    );

    let extracted = engine.extract_leads_to(&leads_to);
    let (ep, eq) = extracted.expect("extract_leads_to should extract from TLA_leads_to P Q");
    assert_eq!(ep, p);
    assert_eq!(eq, q);
}

#[test]
fn test_is_trivially_true() {
    use clean_kernel::expr::Expr;
    use clean_kernel::name::Name;

    let engine = TlaTacticEngine::new();

    let true_expr = Expr::const_(Name::from_string("Bool.true"), vec![]);
    assert!(engine.is_trivially_true(&true_expr));

    let false_expr = Expr::const_(Name::from_string("Bool.false"), vec![]);
    assert!(!engine.is_trivially_true(&false_expr));

    let p = Expr::const_(Name::from_string("P"), vec![]);
    assert!(!engine.is_trivially_true(&p));
}

#[test]
fn test_lfp_induction_trivial() {
    use clean_kernel::expr::Expr;
    use clean_kernel::name::Name;

    let engine = TlaTacticEngine::new();

    // Build: ◇True = FixedPoint.TLA_eventually Bool.true
    let true_expr = Expr::const_(Name::from_string("Bool.true"), vec![]);
    let eventually_true = Expr::app(
        Expr::const_(Name::from_string("FixedPoint.TLA_eventually"), vec![]),
        true_expr,
    );

    let result = engine.try_lfp_induction(&eventually_true);
    let result = result.expect("try_lfp_induction on ◇True should not error");
    // Should succeed with lfp_induction_trivial since inner is Bool.true
    if let Some(cert) = result {
        assert!(cert.contains("lfp_induction"));
    }
}

#[test]
fn test_gfp_coinduction_trivial() {
    use clean_kernel::expr::Expr;
    use clean_kernel::name::Name;

    let engine = TlaTacticEngine::new();

    // Build: □True = FixedPoint.TLA_always Bool.true
    let true_expr = Expr::const_(Name::from_string("Bool.true"), vec![]);
    let always_true = Expr::app(
        Expr::const_(Name::from_string("FixedPoint.TLA_always"), vec![]),
        true_expr,
    );

    let result = engine.try_gfp_coinduction(&always_true);
    let result = result.expect("try_gfp_coinduction on □True should not error");
    // Should succeed with gfp_coinduction_trivial since inner is Bool.true
    if let Some(cert) = result {
        assert!(cert.contains("gfp_coinduction"));
    }
}

#[test]
fn test_make_next() {
    use clean_kernel::expr::Expr;
    use clean_kernel::name::Name;

    let engine = TlaTacticEngine::new();

    let p = Expr::const_(Name::from_string("P"), vec![]);
    let next_p = engine.make_next(p.clone());

    // Verify structure: make_next(P) should be App(Const("FixedPoint.TLA_next"), P)
    let expected = Expr::app(
        Expr::const_(Name::from_string("FixedPoint.TLA_next"), vec![]),
        p,
    );
    assert_eq!(next_p, expected);
}

#[test]
fn test_unfold_always() {
    use clean_kernel::expr::Expr;
    use clean_kernel::name::Name;

    let engine = TlaTacticEngine::new();

    // Build: □P
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let always_p = engine.make_always(p.clone());

    // Unfold: □P → P ∧ ○(□P)
    let result = engine.unfold_always(always_p);

    // The result should be And(P, Next(Always(P)))
    // Result is App(App(And, P), Next(Always(P)))
    assert!(
        matches!(result.kind(), ExprKind::App(_, _)),
        "expected App node from unfold_always, got: {:?}",
        result
    );
}

#[test]
fn test_unfold_eventually() {
    use clean_kernel::expr::Expr;
    use clean_kernel::name::Name;

    let engine = TlaTacticEngine::new();

    // Build: ◇P
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let eventually_p = engine.make_eventually(p.clone());

    // Unfold: ◇P → P ∨ ○(◇P)
    let result = engine.unfold_eventually(eventually_p);

    // The result should be Or(P, Next(Eventually(P)))
    assert!(
        matches!(result.kind(), ExprKind::App(_, _)),
        "expected App node from unfold_eventually, got: {:?}",
        result
    );
}

#[test]
fn test_make_and_or() {
    use clean_kernel::expr::Expr;
    use clean_kernel::name::Name;

    let engine = TlaTacticEngine::new();

    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);

    // Test make_and
    let and_pq = engine.make_and(p.clone(), q.clone());
    if let ExprKind::App(f, arg2) = and_pq.kind() {
        assert_eq!(**arg2, q);
        if let ExprKind::App(_, arg1) = f.kind() {
            assert_eq!(**arg1, p);
        } else {
            panic!("make_and structure incorrect");
        }
    } else {
        panic!("make_and should produce App");
    }

    // Test make_or
    let or_pq = engine.make_or(p.clone(), q.clone());
    if let ExprKind::App(f, arg2) = or_pq.kind() {
        assert_eq!(**arg2, q);
        if let ExprKind::App(_, arg1) = f.kind() {
            assert_eq!(**arg1, p);
        } else {
            panic!("make_or structure incorrect");
        }
    } else {
        panic!("make_or should produce App");
    }
}

#[test]
fn test_is_trivially_false() {
    use clean_kernel::expr::Expr;
    use clean_kernel::name::Name;

    let engine = TlaTacticEngine::new();

    let false_expr = Expr::const_(Name::from_string("Bool.false"), vec![]);
    assert!(engine.is_trivially_false(&false_expr));

    let false_prop = Expr::const_(Name::from_string("False"), vec![]);
    assert!(engine.is_trivially_false(&false_prop));

    let true_expr = Expr::const_(Name::from_string("Bool.true"), vec![]);
    assert!(!engine.is_trivially_false(&true_expr));

    let p = Expr::const_(Name::from_string("P"), vec![]);
    assert!(!engine.is_trivially_false(&p));
}

#[test]
fn test_exprs_equal() {
    use clean_kernel::expr::Expr;
    use clean_kernel::name::Name;

    let engine = TlaTacticEngine::new();

    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);
    let p2 = Expr::const_(Name::from_string("P"), vec![]);

    assert!(engine.exprs_equal(&p, &p2));
    assert!(!engine.exprs_equal(&p, &q));
}

#[test]
fn test_peel_pis_to_innermost() {
    use clean_kernel::expr::{BinderInfo, Expr};
    use clean_kernel::name::Name;

    let engine = TlaTacticEngine::new();

    // No Pi - returns None (no peeling happened)
    let simple = Expr::const_(Name::from_string("True"), vec![]);
    assert!(
        engine.peel_pis_to_innermost(&simple).is_none(),
        "non-Pi expression should return None from peel_pis_to_innermost"
    );

    // Pi(_, A, True) - non-dependent, should peel to True
    let with_pi = Expr::pi(
        BinderInfo::Default,
        Expr::const_(Name::from_string("A"), vec![]),
        Expr::const_(Name::from_string("True"), vec![]),
    );
    let peeled = engine
        .peel_pis_to_innermost(&with_pi)
        .expect("Pi(_, A, True) should peel to innermost body");
    assert!(
        engine.is_trivially_true(&peeled),
        "peeled body should be trivially true, got: {:?}",
        peeled
    );

    // Nested Pis: A → B → True
    let nested = Expr::pi(
        BinderInfo::Default,
        Expr::const_(Name::from_string("A"), vec![]),
        Expr::pi(
            BinderInfo::Default,
            Expr::const_(Name::from_string("B"), vec![]),
            Expr::const_(Name::from_string("True"), vec![]),
        ),
    );
    let peeled_nested = engine
        .peel_pis_to_innermost(&nested)
        .expect("nested Pi(A, Pi(B, True)) should peel to innermost body");
    assert!(
        engine.is_trivially_true(&peeled_nested),
        "nested peeled body should be trivially true, got: {:?}",
        peeled_nested
    );
}

#[test]
fn test_try_trivial_on_true() {
    use clean_kernel::expr::Expr;
    use clean_kernel::name::Name;

    let engine = TlaTacticEngine::new();

    // True should be trivially provable
    let true_goal = Expr::const_(Name::from_string("True"), vec![]);
    let cert = engine
        .try_trivial(&true_goal)
        .expect("try_trivial should not error on True")
        .expect("True should be trivially provable and produce a certificate");
    // Proof certificate should be valid JSON containing the tactic name and status
    assert!(
        cert.contains("proved"),
        "proof certificate should indicate 'proved', got: {cert}"
    );
    assert!(!cert.is_empty(), "proof certificate should not be empty");
}

#[test]
fn test_try_trivial_on_non_trivial() {
    use clean_kernel::expr::Expr;
    use clean_kernel::name::Name;

    let engine = TlaTacticEngine::new();

    // P is not trivially provable
    let p_goal = Expr::const_(Name::from_string("P"), vec![]);
    let inner = engine
        .try_trivial(&p_goal)
        .expect("try_trivial should not error on P");
    assert!(
        inner.is_none(),
        "P should not be trivially provable, but got certificate: {:?}",
        inner
    );
}

#[test]
fn test_leads_to_true_true() {
    // True ~> True should be provable
    let obligation = TlaObligation::new(TlaFormula::LeadsTo(
        Box::new(TlaFormula::True),
        Box::new(TlaFormula::True),
    ));
    let result = prove_tla_obligation(&obligation);
    assert!(
        result.proved,
        "True ~> True should be provable, got: {result:?}"
    );
    let cert = result.certificate.as_deref().unwrap_or_default();
    assert!(
        cert.contains("leads_to") || cert.contains("lattice_rule"),
        "expected leads_to or lattice_rule in certificate, got: {result:?}"
    );
}

#[test]
fn test_leads_to_false_q() {
    // False ~> Q is vacuously true
    let obligation = TlaObligation::new(TlaFormula::LeadsTo(
        Box::new(TlaFormula::False),
        Box::new(TlaFormula::Expr(crate::encoding::TlaExpr::Const(
            "Q".to_string(),
        ))),
    ));
    let result = prove_tla_obligation(&obligation);
    assert!(
        result.proved,
        "False ~> Q should be provable (vacuously true), got: {result:?}"
    );
}

#[test]
fn test_leads_to_p_true() {
    // P ~> True is always provable
    let obligation = TlaObligation::new(TlaFormula::LeadsTo(
        Box::new(TlaFormula::Expr(crate::encoding::TlaExpr::Const(
            "P".to_string(),
        ))),
        Box::new(TlaFormula::True),
    ));
    let result = prove_tla_obligation(&obligation);
    assert!(
        result.proved,
        "P ~> True should be provable, got: {result:?}"
    );
}

// ================================================================
// Natural Number Induction Tests
// ================================================================

#[test]
fn test_extract_forall_nat_basic() {
    use clean_kernel::expr::{BinderInfo, Expr, ExprKind};
    use clean_kernel::name::Name;

    let engine = TlaTacticEngine::new();

    // Build: ∀n : Nat, P(n)
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let p_n = Expr::app(
        Expr::const_(Name::from_string("P"), vec![]),
        Expr::from_kind(ExprKind::BVar(0)),
    );
    let forall_nat = Expr::pi(BinderInfo::Default, nat, p_n.clone());

    let result = engine.extract_forall_nat(&forall_nat);
    assert!(result.is_some(), "Should extract body from ∀n : Nat, P(n)");

    let body = result.unwrap();
    // Body should contain BVar(0)
    assert!(body.has_loose_bvars(), "Body should have loose bound vars");
}

#[test]
fn test_extract_forall_nat_not_nat() {
    use clean_kernel::expr::{BinderInfo, Expr, ExprKind};
    use clean_kernel::name::Name;

    let engine = TlaTacticEngine::new();

    // Build: ∀x : Int, P(x) - should NOT match
    let int = Expr::const_(Name::from_string("Int"), vec![]);
    let p_x = Expr::app(
        Expr::const_(Name::from_string("P"), vec![]),
        Expr::from_kind(ExprKind::BVar(0)),
    );
    let forall_int = Expr::pi(BinderInfo::Default, int, p_x);

    let result = engine.extract_forall_nat(&forall_int);
    assert!(result.is_none(), "Should not extract from ∀x : Int");
}

#[test]
fn test_nat_induction_tried() {
    // Test that nat_induction is attempted for ForallIn over Nat
    let obligation = TlaObligation::new(TlaFormula::ForallIn(
        "n".to_string(),
        Box::new(crate::encoding::TlaExpr::Nat),
        Box::new(TlaFormula::True),
    ));
    let result = prove_tla_obligation(&obligation);

    // nat_induction should be in the tactics tried
    assert!(
        result.tactics_tried.contains(&"nat_induction".to_string()),
        "nat_induction should be tried, got: {:?}",
        result.tactics_tried
    );
}

#[test]
fn test_nat_induction_trivial_property() {
    // ∀n : Nat, True should be provable
    let obligation = TlaObligation::new(TlaFormula::ForallIn(
        "n".to_string(),
        Box::new(crate::encoding::TlaExpr::Nat),
        Box::new(TlaFormula::True),
    ));
    let result = prove_tla_obligation(&obligation);

    // This should be provable since P(0) = True and P(n) → P(succ n) = True → True
    // Both are trivially true
    assert!(
        result.tactics_tried.contains(&"nat_induction".to_string()),
        "nat_induction should be tried for forall over Nat"
    );
}

#[test]
fn test_nat_induction_builds_correct_subgoals() {
    use clean_kernel::expr::{BinderInfo, Expr, ExprKind};
    use clean_kernel::name::Name;

    // Manually test the subgoal construction
    // For ∀n : Nat, P(n):
    //   Base case: P(0)
    //   Step case: ∀n : Nat, P(n) → P(succ n)

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let succ_n = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::from_kind(ExprKind::BVar(0)),
    );

    // Body: P(#0) where #0 is BVar(0)
    let body = Expr::app(
        Expr::const_(Name::from_string("P"), vec![]),
        Expr::from_kind(ExprKind::BVar(0)),
    );

    // Base case: P(0)
    let base_case = body.instantiate(&zero);
    // Should be P(Nat.zero)
    if let ExprKind::App(f, arg) = base_case.kind() {
        if let ExprKind::Const(name, _) = f.kind() {
            assert_eq!(name.to_string(), "P");
        }
        if let ExprKind::Const(arg_name, _) = arg.kind() {
            assert_eq!(arg_name.to_string(), "Nat.zero");
        }
    }

    // Step case hypothesis: P(#0) (same as body)
    let p_n = body.clone();

    // Step case conclusion: P(succ #0)
    let p_succ_n = body.instantiate(&succ_n);

    // P(n) → P(succ n)
    let step_body = Expr::arrow(p_n, p_succ_n);

    // ∀n : Nat, P(n) → P(succ n)
    let step_case = Expr::pi(BinderInfo::Default, nat, step_body);

    // Verify step_case has expected structure
    if let ExprKind::Pi(_, ty, _body) = step_case.kind() {
        if let ExprKind::Const(ty_name, _) = ty.kind() {
            assert_eq!(ty_name.to_string(), "Nat");
        }
    } else {
        panic!("Step case should be a Pi");
    }
}

// ================================================================
// Well-Founded Induction Tests
// ================================================================

#[test]
fn test_extract_tla_forall_in() {
    use clean_kernel::expr::{BinderInfo, Expr, ExprKind};
    use clean_kernel::name::Name;

    let engine = TlaTacticEngine::new();

    // Build: TLA.forallIn S (λx. P(x))
    let s = Expr::const_(Name::from_string("S"), vec![]);
    let tla_value = Expr::const_(Name::from_string("TLA.Value"), vec![]);
    let body = Expr::app(
        Expr::const_(Name::from_string("P"), vec![]),
        Expr::from_kind(ExprKind::BVar(0)),
    );
    let lam = Expr::lam(BinderInfo::Default, tla_value, body);
    let forall_in = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("TLA.forallIn"), vec![]),
            s.clone(),
        ),
        lam,
    );

    let result = engine.extract_tla_forall_in(&forall_in);
    assert!(result.is_some(), "Should extract TLA.forallIn pattern");

    let (set, _var, body) = result.unwrap();
    assert_eq!(set, s);
    assert!(body.has_loose_bvars(), "Body should have bound vars");
}

#[test]
fn test_is_nat_set() {
    use clean_kernel::expr::Expr;
    use clean_kernel::name::Name;

    let engine = TlaTacticEngine::new();

    let nat_tla = Expr::const_(Name::from_string("TLA.Nat"), vec![]);
    assert!(engine.is_nat_set(&nat_tla), "TLA.Nat should be recognized");

    let nat_plain = Expr::const_(Name::from_string("Nat"), vec![]);
    assert!(engine.is_nat_set(&nat_plain), "Nat should be recognized");

    let other = Expr::const_(Name::from_string("S"), vec![]);
    assert!(!engine.is_nat_set(&other), "S should not be Nat");
}

#[test]
fn test_wf_induction_on_nat_trivial() {
    // ∀n ∈ Nat. True should be provable via WF induction
    let obligation = TlaObligation::new(TlaFormula::ForallIn(
        "n".to_string(),
        Box::new(crate::encoding::TlaExpr::Nat),
        Box::new(TlaFormula::True),
    ));
    let result = prove_tla_obligation(&obligation);

    // wf_induction should be tried (after nat_induction)
    assert!(
        result.tactics_tried.contains(&"wf_induction".to_string())
            || result.tactics_tried.contains(&"nat_induction".to_string()),
        "wf_induction or nat_induction should be tried, got: {:?}",
        result.tactics_tried
    );
}

#[test]
fn test_wf_induction_on_generic_set_trivial() {
    use clean_kernel::expr::{BinderInfo, Expr};
    use clean_kernel::name::Name;

    let engine = TlaTacticEngine::new();

    // Build: TLA.forallIn S (λx. True)
    let s = Expr::const_(Name::from_string("S"), vec![]);
    let tla_value = Expr::const_(Name::from_string("TLA.Value"), vec![]);
    let body = Expr::const_(Name::from_string("True"), vec![]);
    let lam = Expr::lam(BinderInfo::Default, tla_value, body);
    let goal = Expr::app(
        Expr::app(Expr::const_(Name::from_string("TLA.forallIn"), vec![]), s),
        lam,
    );

    // Should extract the pattern
    let extract = engine.extract_tla_forall_in(&goal);
    assert!(extract.is_some(), "Should extract ForallIn pattern");

    let (_, _, inner_body) = extract.unwrap();
    assert!(engine.is_trivially_true(&inner_body), "Body should be True");
}

#[test]
fn test_wf_induction_certificate_format() {
    use clean_kernel::expr::{BinderInfo, Expr};
    use clean_kernel::name::Name;

    let mut engine = TlaTacticEngine::new();
    engine.trace = false;

    // Build a trivial goal: TLA.forallIn TLA.Nat (λx. True)
    let nat = Expr::const_(Name::from_string("TLA.Nat"), vec![]);
    let tla_value = Expr::const_(Name::from_string("TLA.Value"), vec![]);
    let body = Expr::const_(Name::from_string("True"), vec![]);
    let lam = Expr::lam(BinderInfo::Default, tla_value, body);
    let goal = Expr::app(
        Expr::app(Expr::const_(Name::from_string("TLA.forallIn"), vec![]), nat),
        lam,
    );

    let cert = engine
        .try_wf_induction(&goal)
        .expect("WF induction should not error")
        .expect("WF induction should produce a certificate for trivial Nat goal");
    assert!(
        cert.contains("wf_induction"),
        "Certificate should mention wf_induction, got: {}",
        cert
    );
}

#[test]
fn test_wf_induction_relation_selection() {
    use clean_kernel::expr::Expr;
    use clean_kernel::name::Name;

    let engine = TlaTacticEngine::new();

    // Nat should use Nat.lt
    let nat = Expr::const_(Name::from_string("TLA.Nat"), vec![]);
    assert!(engine.is_nat_set(&nat));

    // Generic set should use TLA.wf_rel
    let generic = Expr::const_(Name::from_string("MySet"), vec![]);
    assert!(!engine.is_nat_set(&generic));
}

// ================================================================
// Arithmetic Simplification Tests
// ================================================================

#[test]
fn test_normalize_int_ofnat_in_function_arg() {
    // Verify that sum(Int.ofNat 0) normalizes to sum(Nat.zero)
    use clean_kernel::expr::Expr;
    use clean_kernel::name::Name;

    let engine = TlaTacticEngine::new();

    // Build: Int.ofNat 0
    let int_ofnat_0 = Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(0),
    );
    eprintln!("Int.ofNat 0: {:?}", int_ofnat_0);

    // Build: sum(Int.ofNat 0)
    let sum_int_ofnat_0 = Expr::app(
        Expr::const_(Name::from_string("sum"), vec![]),
        int_ofnat_0.clone(),
    );
    eprintln!("sum(Int.ofNat 0): {:?}", sum_int_ofnat_0);

    // Expected: sum(Nat.zero)
    let sum_nat_zero = Expr::app(
        Expr::const_(Name::from_string("sum"), vec![]),
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
    );
    eprintln!("Expected sum(Nat.zero): {:?}", sum_nat_zero);

    // Normalize
    let normalized = engine.normalize_arith(&sum_int_ofnat_0);
    eprintln!("Normalized: {:?}", normalized);

    // Check equality
    assert!(
        engine.exprs_equal(&normalized, &sum_nat_zero),
        "sum(Int.ofNat 0) should normalize to sum(Nat.zero), got {:?}",
        normalized
    );
}

#[test]
fn test_is_zero_variants() {
    use clean_kernel::expr::Expr;
    use clean_kernel::name::Name;

    let engine = TlaTacticEngine::new();

    // Named constants
    let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    assert!(engine.is_zero(&nat_zero), "Nat.zero should be zero");

    let tla_zero = Expr::const_(Name::from_string("TLA.zero"), vec![]);
    assert!(engine.is_zero(&tla_zero), "TLA.zero should be zero");

    // Literal 0
    let lit_zero = Expr::nat_lit(0);
    assert!(engine.is_zero(&lit_zero), "Lit(0) should be zero");

    // Int.ofNat 0
    let int_zero = Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(0),
    );
    assert!(engine.is_zero(&int_zero), "Int.ofNat 0 should be zero");

    // Non-zero
    let one = Expr::nat_lit(1);
    assert!(!engine.is_zero(&one), "Lit(1) should not be zero");
}

#[test]
fn test_is_one_variants() {
    use clean_kernel::expr::Expr;
    use clean_kernel::name::Name;

    let engine = TlaTacticEngine::new();

    // Nat.succ Nat.zero
    let succ_zero = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
    );
    assert!(engine.is_one(&succ_zero), "Nat.succ Nat.zero should be one");

    // Literal 1
    let lit_one = Expr::nat_lit(1);
    assert!(engine.is_one(&lit_one), "Lit(1) should be one");

    // Int.ofNat 1
    let int_one = Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(1),
    );
    assert!(engine.is_one(&int_one), "Int.ofNat 1 should be one");

    // Non-one values
    let zero = Expr::nat_lit(0);
    assert!(!engine.is_one(&zero), "Lit(0) should not be one");
}

#[test]
fn test_normalize_arith_add_zero() {
    use clean_kernel::expr::Expr;
    use clean_kernel::name::Name;

    let engine = TlaTacticEngine::new();

    // n + 0 should normalize to n
    let n = Expr::const_(Name::from_string("n"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let n_plus_zero = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("TLA.add"), vec![]),
            n.clone(),
        ),
        zero,
    );

    let normalized = engine.normalize_arith(&n_plus_zero);
    assert_eq!(normalized, n, "n + 0 should normalize to n");

    // 0 + n should normalize to n
    let zero2 = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let zero_plus_n = Expr::app(
        Expr::app(Expr::const_(Name::from_string("TLA.add"), vec![]), zero2),
        n.clone(),
    );

    let normalized2 = engine.normalize_arith(&zero_plus_n);
    assert_eq!(normalized2, n, "0 + n should normalize to n");
}

#[test]
fn test_normalize_arith_mul_zero() {
    use clean_kernel::expr::Expr;
    use clean_kernel::name::Name;

    let engine = TlaTacticEngine::new();

    // n * 0 should normalize to 0
    let n = Expr::const_(Name::from_string("n"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let n_times_zero = Expr::app(
        Expr::app(Expr::const_(Name::from_string("TLA.mul"), vec![]), n),
        zero,
    );

    let normalized = engine.normalize_arith(&n_times_zero);
    assert!(
        engine.is_zero(&normalized),
        "n * 0 should normalize to zero"
    );
}

#[test]
fn test_normalize_arith_mul_one() {
    use clean_kernel::expr::Expr;
    use clean_kernel::name::Name;

    let engine = TlaTacticEngine::new();

    // n * 1 should normalize to n
    let n = Expr::const_(Name::from_string("n"), vec![]);
    let one = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
    );
    let n_times_one = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("TLA.mul"), vec![]),
            n.clone(),
        ),
        one,
    );

    let normalized = engine.normalize_arith(&n_times_one);
    assert_eq!(normalized, n, "n * 1 should normalize to n");
}

#[test]
fn test_check_arith_identity_add_zero() {
    use clean_kernel::expr::Expr;
    use clean_kernel::name::Name;

    let engine = TlaTacticEngine::new();

    // n + 0 = n should be recognized as add_zero_right
    let n = Expr::const_(Name::from_string("n"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let n_plus_zero = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("TLA.add"), vec![]),
            n.clone(),
        ),
        zero,
    );

    let rule = engine.check_arith_identity(&n_plus_zero, &n);
    assert_eq!(rule, Some("add_zero_right"), "Should recognize n + 0 = n");

    // 0 + n = n should be recognized as add_zero_left
    let zero2 = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let zero_plus_n = Expr::app(
        Expr::app(Expr::const_(Name::from_string("TLA.add"), vec![]), zero2),
        n.clone(),
    );

    let rule2 = engine.check_arith_identity(&zero_plus_n, &n);
    assert_eq!(rule2, Some("add_zero_left"), "Should recognize 0 + n = n");
}

#[test]
fn test_try_arith_simplify() {
    use clean_kernel::expr::Expr;
    use clean_kernel::name::Name;

    let engine = TlaTacticEngine::new();

    // Build: TLA.eq (n + 0) n
    let n = Expr::const_(Name::from_string("n"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let n_plus_zero = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("TLA.add"), vec![]),
            n.clone(),
        ),
        zero,
    );
    let eq_goal = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("TLA.eq"), vec![]),
            n_plus_zero,
        ),
        n,
    );

    let result = engine.try_arith_simplify(&eq_goal);
    assert!(
        result.is_some(),
        "Should prove n + 0 = n via arith_simplify"
    );
    let cert = result.unwrap();
    assert!(
        cert.contains("add_zero") || cert.contains("normalize"),
        "Certificate should mention add_zero or normalize, got: {}",
        cert
    );
}

#[test]
fn test_try_arith_simplify_with_hypotheses() {
    use clean_kernel::expr::Expr;
    use clean_kernel::name::Name;

    let engine = TlaTacticEngine::new();

    // First verify the basic normalization: 0 * x / 2 should normalize to 0
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let one = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        zero.clone(),
    );
    let two = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        one.clone(),
    );
    let zero_plus_one = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("TLA.add"), vec![]),
            zero.clone(),
        ),
        one.clone(),
    );
    let zero_mul_expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("TLA.mul"), vec![]),
            zero.clone(),
        ),
        zero_plus_one.clone(),
    );
    let div_expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("TLA.div"), vec![]),
            zero_mul_expr,
        ),
        two,
    );
    let normalized_rhs = engine.normalize_arith(&div_expr);
    assert!(
        engine.is_zero(&normalized_rhs),
        "0 * (0 + 1) / 2 should normalize to 0, got {:?}",
        normalized_rhs
    );

    // Now test the hypothesis matching with this simplified RHS
    // sum(0) - a function application
    let sum_zero = Expr::app(Expr::const_(Name::from_string("sum"), vec![]), zero.clone());

    // Hypothesis: sum(0) = 0
    let hyp_sum_def_0 = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("TLA.eq"), vec![]),
            sum_zero.clone(),
        ),
        zero.clone(),
    );

    // Goal: sum(0) = 0 * (0 + 1) / 2
    // After normalization, 0 * (0 + 1) / 2 → 0 (via 0 * x = 0)
    let zero_mul_expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("TLA.mul"), vec![]),
            zero.clone(),
        ),
        zero_plus_one,
    );
    let two = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::app(
            Expr::const_(Name::from_string("Nat.succ"), vec![]),
            zero.clone(),
        ),
    );
    let rhs = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("TLA.div"), vec![]),
            zero_mul_expr,
        ),
        two,
    );

    let goal = Expr::app(
        Expr::app(Expr::const_(Name::from_string("TLA.eq"), vec![]), sum_zero),
        rhs,
    );

    let hypotheses = vec![hyp_sum_def_0];
    let result = engine.try_arith_simplify_with_hypotheses(&goal, &hypotheses);

    assert!(
        result.is_some(),
        "Should prove sum(0) = 0 * (0+1) / 2 using hypothesis sum(0) = 0"
    );
    let cert = result.unwrap();
    assert!(
        cert.contains("arith_simplify_hyp"),
        "Certificate should mention arith_simplify_hyp, got: {}",
        cert
    );
}

// ================================================================
// Lexicographic Ordering Tests
// ================================================================

#[test]
fn test_extract_product_type() {
    use clean_kernel::expr::Expr;
    use clean_kernel::name::Name;

    let engine = TlaTacticEngine::new();

    // Build: Prod Nat Nat (Nat × Nat)
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let prod_nat_nat = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Prod"), vec![]), nat.clone()),
        nat.clone(),
    );

    let result = engine.extract_product_type(&prod_nat_nat);
    assert!(result.is_some(), "Should extract product type");
    let (a, b) = result.unwrap();
    assert_eq!(a, nat);
    assert_eq!(b, nat);

    // Build: TLA.cross Nat Nat (TLA style)
    let tla_cross = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("TLA.cross"), vec![]),
            nat.clone(),
        ),
        nat.clone(),
    );

    let (a2, b2) = engine
        .extract_product_type(&tla_cross)
        .expect("Should extract TLA.cross product type");
    assert_eq!(a2, nat, "TLA.cross first component should be Nat");
    assert_eq!(b2, nat, "TLA.cross second component should be Nat");

    // Non-product types
    let single = Expr::const_(Name::from_string("Nat"), vec![]);
    assert!(
        engine.extract_product_type(&single).is_none(),
        "Single type should not be product"
    );
}

#[test]
fn test_build_lex_ordering() {
    use clean_kernel::expr::Expr;
    use clean_kernel::name::Name;

    let engine = TlaTacticEngine::new();

    // Nat × Nat should use Nat.lt for both components
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let tla_nat = Expr::const_(Name::from_string("TLA.Nat"), vec![]);

    let lex_rel = engine.build_lex_ordering(&nat, &tla_nat);

    // Should produce: TLA.lex_lt Nat.lt Nat.lt
    if let ExprKind::App(f, _b) = lex_rel.kind() {
        if let ExprKind::App(lex_lt, _a) = f.kind() {
            if let ExprKind::Const(name, _) = lex_lt.kind() {
                assert_eq!(name.to_string(), "TLA.lex_lt", "Should use TLA.lex_lt");
            } else {
                panic!("Expected TLA.lex_lt constant");
            }
        } else {
            panic!("Expected nested application");
        }
    } else {
        panic!("Expected application");
    }
}

#[test]
fn test_get_wf_relation_nat() {
    use clean_kernel::expr::Expr;
    use clean_kernel::name::Name;

    let engine = TlaTacticEngine::new();

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let (_rel, desc) = engine.get_wf_relation(&nat);
    assert_eq!(desc, "Nat.lt", "Nat should use Nat.lt");

    let tla_nat = Expr::const_(Name::from_string("TLA.Nat"), vec![]);
    let (_rel2, desc2) = engine.get_wf_relation(&tla_nat);
    assert_eq!(desc2, "Nat.lt", "TLA.Nat should use Nat.lt");
}

#[test]
fn test_get_wf_relation_product() {
    use clean_kernel::expr::Expr;
    use clean_kernel::name::Name;

    let engine = TlaTacticEngine::new();

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let prod = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Prod"), vec![]), nat.clone()),
        nat.clone(),
    );

    let (_rel, desc) = engine.get_wf_relation(&prod);
    assert_eq!(desc, "lex_lt", "Product should use lex_lt");
}

#[test]
fn test_get_wf_relation_generic() {
    use clean_kernel::expr::Expr;
    use clean_kernel::name::Name;

    let engine = TlaTacticEngine::new();

    let generic = Expr::const_(Name::from_string("SomeSet"), vec![]);
    let (_rel, desc) = engine.get_wf_relation(&generic);
    assert_eq!(desc, "TLA.wf_rel", "Generic set should use TLA.wf_rel");
}

#[test]
fn test_try_lex_induction_nat_nat_trivial() {
    use clean_kernel::expr::{BinderInfo, Expr};
    use clean_kernel::name::Name;

    let engine = TlaTacticEngine::new();

    // Build: TLA.forallIn (Nat × Nat) (λp. True)
    let nat = Expr::const_(Name::from_string("TLA.Nat"), vec![]);
    let prod = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Prod"), vec![]), nat.clone()),
        nat.clone(),
    );
    let tla_value = Expr::const_(Name::from_string("TLA.Value"), vec![]);
    let body = Expr::const_(Name::from_string("True"), vec![]);
    let lam = Expr::lam(BinderInfo::Default, tla_value, body);
    let goal = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("TLA.forallIn"), vec![]),
            prod,
        ),
        lam,
    );

    let cert = engine
        .try_lex_induction(&goal)
        .expect("lex_induction should not error")
        .expect("lex_induction should produce a certificate for trivial Nat×Nat goal");
    assert!(
        cert.contains("lex_induction"),
        "Certificate should mention lex_induction, got: {}",
        cert
    );
}

// ================================================================
// Progress Measure Tests
// ================================================================

#[test]
fn test_extract_variant_pattern_countdown() {
    use clean_kernel::expr::Expr;
    use clean_kernel::name::Name;

    let engine = TlaTacticEngine::new();

    // Build: TLA.gt n 0 (countdown pattern)
    let n = Expr::const_(Name::from_string("n"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let gt_n_0 = Expr::app(
        Expr::app(Expr::const_(Name::from_string("TLA.gt"), vec![]), n.clone()),
        zero,
    );

    let q = Expr::const_(Name::from_string("done"), vec![]);

    let result = engine.extract_variant_pattern(&gt_n_0, &q);
    assert!(result.is_some(), "Should extract countdown variant pattern");

    let (variant, domain) = result.unwrap();
    assert_eq!(domain, "Nat", "Domain should be Nat");
    assert!(
        variant.contains("n"),
        "Variant should reference n, got: {}",
        variant
    );
}

#[test]
fn test_extract_variant_pattern_distance() {
    use clean_kernel::expr::Expr;
    use clean_kernel::name::Name;

    let engine = TlaTacticEngine::new();

    // Build: TLA.ne state goal (distance pattern)
    let state = Expr::const_(Name::from_string("state"), vec![]);
    let goal_state = Expr::const_(Name::from_string("goal"), vec![]);
    let ne_state_goal = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("TLA.ne"), vec![]),
            state.clone(),
        ),
        goal_state.clone(),
    );

    let q = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Eq"), vec![]), state),
        goal_state,
    );

    let result = engine.extract_variant_pattern(&ne_state_goal, &q);
    assert!(result.is_some(), "Should extract distance variant pattern");

    let (variant, domain) = result.unwrap();
    assert_eq!(domain, "Nat", "Domain should be Nat");
    assert_eq!(variant, "dist", "Variant should be distance");
}

#[test]
fn test_try_progress_measure_countdown_is_not_proved() {
    // SOUNDNESS: a countdown *pattern* in P is only a candidate measure, not a
    // proof of `P ~> Q`. Without the spec's next-state action, a fairness
    // assumption, and a well-founded domain, `try_progress_measure` cannot
    // discharge the progress obligation and must fail-closed (return None).
    // The pattern is still detectable (see `extract_variant_pattern`), but
    // detection ≠ proof.
    use clean_kernel::expr::Expr;
    use clean_kernel::name::Name;

    let engine = TlaTacticEngine::new();

    // P: n > 0, Q: done (simple countdown)
    let n = Expr::const_(Name::from_string("n"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let p = Expr::app(
        Expr::app(Expr::const_(Name::from_string("TLA.gt"), vec![]), n),
        zero,
    );
    let q = Expr::const_(Name::from_string("done"), vec![]);

    // The pattern is detectable...
    assert!(
        engine.extract_variant_pattern(&p, &q).is_some(),
        "countdown pattern should still be *detected*"
    );

    // ...but the progress-measure tactic must NOT certify it as proved.
    let result = engine
        .try_progress_measure(&p, &q)
        .expect("progress_measure should not error");
    assert!(
        result.is_none(),
        "SOUNDNESS: progress_measure must not prove liveness from a bare P/Q \
         countdown pattern, got: {result:?}"
    );
}

#[test]
fn test_leads_to_false_p_proves_ex_falso_end_to_end() {
    // `False ~> Q` is genuinely true (ex falso) and must still be proved
    // through the PUBLIC entry via the sound leads-to triviality (Rule 0b),
    // not the fail-closed progress-measure heuristic. This is the end-to-end
    // guard for the trivial-P case.
    let obligation = TlaObligation::new(TlaFormula::LeadsTo(
        Box::new(TlaFormula::False),
        Box::new(TlaFormula::Expr(crate::encoding::TlaExpr::Const(
            "anything".to_string(),
        ))),
    ));
    let result = prove_tla_obligation(&obligation);
    assert!(
        result.proved,
        "False ~> Q should still be provable ex falso, got: {result:?}"
    );

    // And the progress-measure heuristic on its own must NOT be what proves it:
    // for a bare (non-false) P/Q it is fail-closed.
    use clean_kernel::expr::Expr;
    use clean_kernel::name::Name;
    let engine = TlaTacticEngine::new();
    let p = Expr::const_(Name::from_string("some_state"), vec![]);
    let q = Expr::const_(Name::from_string("anything"), vec![]);
    assert!(
        engine
            .try_progress_measure(&p, &q)
            .expect("progress_measure should not error")
            .is_none(),
        "progress_measure must be fail-closed for a bare P/Q"
    );
}

#[test]
fn test_peel_hypotheses_with_declarations() {
    // Test that peel_hypotheses_with_context correctly skips implicit declarations
    // and extracts non-dependent hypotheses.
    //
    // Structure we're testing:
    // Pi(Implicit, TLA.Value,          -- declaration: constant sum
    //    Pi(Default, sum(0) = 0,       -- hypothesis: sum_def_0
    //       Pi(Default, forall k...,   -- hypothesis: sum_def_succ
    //          goal)))                 -- inner goal

    use clean_kernel::expr::{BinderInfo, Expr};
    use clean_kernel::name::Name;

    let engine = TlaTacticEngine::new();

    // Build the goal expression (e.g., forall n. P(n))
    let goal = Expr::const_(Name::from_string("goal"), vec![]);

    // Build hypothesis 2: forall k. sum(k+1) = sum(k) + (k+1)
    // (simplified as a constant for this test)
    let hyp2 = Expr::const_(Name::from_string("sum_def_succ"), vec![]);

    // Build hypothesis 1: sum(0) = 0
    let hyp1 = Expr::const_(Name::from_string("sum_def_0_eq"), vec![]);

    // Build declaration type: TLA.Value
    let tla_value = Expr::const_(Name::from_string("TLA.Value"), vec![]);

    // Construct the full expression:
    // Pi(Implicit, TLA.Value,      -- declaration
    //    Pi(Default, hyp1,         -- hypothesis 1 (non-dependent)
    //       Pi(Default, hyp2,      -- hypothesis 2 (non-dependent)
    //          goal)))
    let with_hyp2 = Expr::pi(BinderInfo::Default, hyp2.clone(), goal.clone());
    let with_hyp1 = Expr::pi(BinderInfo::Default, hyp1.clone(), with_hyp2);
    let with_decl = Expr::pi(BinderInfo::Implicit, tla_value, with_hyp1);

    // Call peel_hypotheses_with_context
    let (hypotheses, inner_goal) = engine.peel_hypotheses_with_context(&with_decl);

    // Verify: should extract 2 hypotheses (hyp1, hyp2) and skip the declaration
    assert_eq!(
        hypotheses.len(),
        2,
        "Should extract 2 hypotheses, got {}",
        hypotheses.len()
    );

    // Verify hypothesis types are correct
    assert_eq!(
        hypotheses[0], hyp1,
        "First hypothesis should be sum_def_0_eq"
    );
    assert_eq!(
        hypotheses[1], hyp2,
        "Second hypothesis should be sum_def_succ"
    );

    // Verify inner goal is correct
    assert_eq!(inner_goal, goal, "Inner goal should be the original goal");
}

#[test]
fn test_peel_hypotheses_no_declarations() {
    // Test that peel_hypotheses_with_context works when there are no declarations
    use clean_kernel::expr::{BinderInfo, Expr};
    use clean_kernel::name::Name;

    let engine = TlaTacticEngine::new();

    let goal = Expr::const_(Name::from_string("goal"), vec![]);
    let hyp = Expr::const_(Name::from_string("hypothesis"), vec![]);

    // Pi(Default, hyp, goal) - just a hypothesis, no declaration
    let with_hyp = Expr::pi(BinderInfo::Default, hyp.clone(), goal.clone());

    let (hypotheses, inner_goal) = engine.peel_hypotheses_with_context(&with_hyp);

    assert_eq!(hypotheses.len(), 1, "Should extract 1 hypothesis");
    assert_eq!(hypotheses[0], hyp);
    assert_eq!(inner_goal, goal);
}

#[test]
fn test_peel_hypotheses_multiple_declarations() {
    // Test with multiple declarations followed by hypotheses
    use clean_kernel::expr::{BinderInfo, Expr};
    use clean_kernel::name::Name;

    let engine = TlaTacticEngine::new();

    let goal = Expr::const_(Name::from_string("goal"), vec![]);
    let hyp = Expr::const_(Name::from_string("hypothesis"), vec![]);
    let tla_value = Expr::const_(Name::from_string("TLA.Value"), vec![]);

    // Build: Pi(Implicit, TLA.Value,
    //           Pi(Implicit, TLA.Value,
    //              Pi(Default, hyp, goal)))
    let with_hyp = Expr::pi(BinderInfo::Default, hyp.clone(), goal.clone());
    let with_decl1 = Expr::pi(BinderInfo::Implicit, tla_value.clone(), with_hyp);
    let with_decl2 = Expr::pi(BinderInfo::Implicit, tla_value, with_decl1);

    let (hypotheses, inner_goal) = engine.peel_hypotheses_with_context(&with_decl2);

    assert_eq!(
        hypotheses.len(),
        1,
        "Should extract 1 hypothesis after 2 declarations"
    );
    assert_eq!(hypotheses[0], hyp);
    assert_eq!(inner_goal, goal);
}

// ============================================================
// Ring tactic tests
// ============================================================

#[test]
fn test_expr_to_polynomial_constant() {
    use clean_kernel::expr::Expr;
    use clean_kernel::Literal;

    let engine = TlaTacticEngine::new();

    // Test literal 5
    let five = Expr::from_kind(ExprKind::Lit(Literal::Nat(clean_kernel::BigNat::Small(5))));
    let poly = engine
        .expr_to_polynomial(&five)
        .expect("literal is decidable");
    assert_eq!(poly, vec![(5, vec![])]);

    // Test Nat.zero
    let zero = Expr::const_(clean_kernel::name::Name::from_string("Nat.zero"), vec![]);
    let poly = engine.expr_to_polynomial(&zero).expect("zero is decidable");
    assert!(poly.is_empty()); // Zero term removed
}

#[test]
fn test_expr_to_polynomial_variable() {
    use clean_kernel::expr::Expr;

    let engine = TlaTacticEngine::new();

    // Test BVar(0) representing n
    let n = Expr::from_kind(ExprKind::BVar(0));
    let poly = engine
        .expr_to_polynomial(&n)
        .expect("variable is decidable");
    assert_eq!(poly, vec![(1, vec!["#BVar0".to_string()])]);
}

#[test]
fn test_expr_to_polynomial_addition() {
    use clean_kernel::expr::Expr;
    use clean_kernel::name::Name;
    use clean_kernel::Literal;

    let engine = TlaTacticEngine::new();

    // Test n + 1 = BVar(0) + 1
    let n = Expr::from_kind(ExprKind::BVar(0));
    let one = Expr::from_kind(ExprKind::Lit(Literal::Nat(clean_kernel::BigNat::Small(1))));
    let n_plus_1 = Expr::app(
        Expr::app(Expr::const_(Name::from_string("TLA.add"), vec![]), n),
        one,
    );
    let poly = engine
        .expr_to_polynomial(&n_plus_1)
        .expect("addition is decidable");

    // Should be [(1, []), (1, ["#BVar0"])] = 1 + n
    assert_eq!(poly.len(), 2);
    assert!(poly.contains(&(1, vec![])));
    assert!(poly.contains(&(1, vec!["#BVar0".to_string()])));
}

#[test]
fn test_expr_to_polynomial_multiplication() {
    use clean_kernel::expr::Expr;
    use clean_kernel::name::Name;
    use clean_kernel::Literal;

    let engine = TlaTacticEngine::new();

    // Test 2 * n = 2 * BVar(0)
    let n = Expr::from_kind(ExprKind::BVar(0));
    let two = Expr::from_kind(ExprKind::Lit(Literal::Nat(clean_kernel::BigNat::Small(2))));
    let two_times_n = Expr::app(
        Expr::app(Expr::const_(Name::from_string("TLA.mul"), vec![]), two),
        n,
    );
    let poly = engine
        .expr_to_polynomial(&two_times_n)
        .expect("multiplication is decidable");

    // Should be [(2, ["#BVar0"])]
    assert_eq!(poly, vec![(2, vec!["#BVar0".to_string()])]);
}

#[test]
fn test_expr_to_polynomial_distribution() {
    use clean_kernel::expr::Expr;
    use clean_kernel::name::Name;
    use clean_kernel::Literal;

    let engine = TlaTacticEngine::new();

    // Test n * (n + 1)
    // = n*n + n*1 = n² + n
    let n = Expr::from_kind(ExprKind::BVar(0));
    let one = Expr::from_kind(ExprKind::Lit(Literal::Nat(clean_kernel::BigNat::Small(1))));
    let n_plus_1 = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("TLA.add"), vec![]),
            n.clone(),
        ),
        one,
    );
    let n_times_n_plus_1 = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("TLA.mul"), vec![]),
            n.clone(),
        ),
        n_plus_1,
    );
    let poly = engine
        .expr_to_polynomial(&n_times_n_plus_1)
        .expect("distribution is decidable");

    // Should be [(1, ["#BVar0"]), (1, ["#BVar0", "#BVar0"])] = n + n²
    assert_eq!(poly.len(), 2);
    assert!(poly.contains(&(1, vec!["#BVar0".to_string()])));
    assert!(poly.contains(&(1, vec!["#BVar0".to_string(), "#BVar0".to_string()])));
}

#[test]
fn test_expr_to_polynomial_succ() {
    use clean_kernel::expr::Expr;
    use clean_kernel::name::Name;

    let engine = TlaTacticEngine::new();

    // Test Nat.succ(n) where n = BVar(0)
    // succ(n) = n + 1
    let n = Expr::from_kind(ExprKind::BVar(0));
    let succ_n = Expr::app(Expr::const_(Name::from_string("Nat.succ"), vec![]), n);
    let poly = engine
        .expr_to_polynomial(&succ_n)
        .expect("succ is decidable");

    // Should be [(1, []), (1, ["#BVar0"])] = 1 + n
    assert_eq!(poly.len(), 2);
    assert!(poly.contains(&(1, vec![])));
    assert!(poly.contains(&(1, vec!["#BVar0".to_string()])));
}

#[test]
fn test_polynomial_equality() {
    use clean_kernel::expr::Expr;
    use clean_kernel::name::Name;
    use clean_kernel::Literal;

    let engine = TlaTacticEngine::new();

    // Test that (n+1) and (1+n) produce the same polynomial
    let n = Expr::from_kind(ExprKind::BVar(0));
    let one = Expr::from_kind(ExprKind::Lit(Literal::Nat(clean_kernel::BigNat::Small(1))));

    let n_plus_1 = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("TLA.add"), vec![]),
            n.clone(),
        ),
        one.clone(),
    );
    let one_plus_n = Expr::app(
        Expr::app(Expr::const_(Name::from_string("TLA.add"), vec![]), one),
        n,
    );

    let poly1 = engine
        .expr_to_polynomial(&n_plus_1)
        .expect("n+1 is decidable");
    let poly2 = engine
        .expr_to_polynomial(&one_plus_n)
        .expect("1+n is decidable");

    // Both should be 1 + n
    assert_eq!(poly1, poly2);
}

// ================================================================
// Fairness (WF_vars(A) / SF_vars(A)) Tests
// ================================================================

/// Walk an application spine and collect every constant name that appears in
/// head position, so tests can assert structural features of a reduced form.
fn collect_const_names(expr: &Expr, out: &mut Vec<String>) {
    match expr.kind() {
        ExprKind::Const(name, _) => out.push(name.to_string()),
        ExprKind::App(f, a) => {
            collect_const_names(f, out);
            collect_const_names(a, out);
        }
        ExprKind::Pi(_, ty, body) => {
            collect_const_names(ty, out);
            collect_const_names(body, out);
        }
        _ => {}
    }
}

fn build_weak_fairness(vars: Expr, action: Expr) -> Expr {
    use clean_kernel::expr::Expr;
    use clean_kernel::name::Name;
    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("FixedPoint.TLA_weak_fairness"), vec![]),
            vars,
        ),
        action,
    )
}

fn build_strong_fairness(vars: Expr, action: Expr) -> Expr {
    use clean_kernel::expr::Expr;
    use clean_kernel::name::Name;
    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("FixedPoint.TLA_strong_fairness"), vec![]),
            vars,
        ),
        action,
    )
}

#[test]
fn test_extract_weak_fairness_roundtrip() {
    use clean_kernel::expr::Expr;
    use clean_kernel::name::Name;

    let engine = TlaTacticEngine::new();

    let vars = Expr::const_(Name::from_string("vars"), vec![]);
    let action = Expr::const_(Name::from_string("A"), vec![]);
    let wf = build_weak_fairness(vars.clone(), action.clone());

    let (ev, ea) = engine
        .extract_weak_fairness(&wf)
        .expect("extract_weak_fairness should match TLA_weak_fairness vars action");
    assert_eq!(ev, vars, "extracted vars should round-trip");
    assert_eq!(ea, action, "extracted action should round-trip");
}

#[test]
fn test_extract_strong_fairness_roundtrip() {
    use clean_kernel::expr::Expr;
    use clean_kernel::name::Name;

    let engine = TlaTacticEngine::new();

    let vars = Expr::const_(Name::from_string("vars"), vec![]);
    let action = Expr::const_(Name::from_string("A"), vec![]);
    let sf = build_strong_fairness(vars.clone(), action.clone());

    let (ev, ea) = engine
        .extract_strong_fairness(&sf)
        .expect("extract_strong_fairness should match TLA_strong_fairness vars action");
    assert_eq!(ev, vars, "extracted vars should round-trip");
    assert_eq!(ea, action, "extracted action should round-trip");
}

#[test]
fn test_extract_fairness_rejects_non_fairness() {
    use clean_kernel::expr::Expr;
    use clean_kernel::name::Name;

    let engine = TlaTacticEngine::new();

    // □P is a temporal formula but NOT a fairness application: both extractors
    // must cleanly decline rather than mis-parse it.
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let always_p = Expr::app(
        Expr::const_(Name::from_string("FixedPoint.TLA_always"), vec![]),
        p.clone(),
    );
    assert!(
        engine.extract_weak_fairness(&always_p).is_none(),
        "extract_weak_fairness should reject □P"
    );
    assert!(
        engine.extract_strong_fairness(&always_p).is_none(),
        "extract_strong_fairness should reject □P"
    );

    // A bare constant is also not a fairness goal.
    assert!(
        engine.extract_weak_fairness(&p).is_none(),
        "extract_weak_fairness should reject a bare constant"
    );

    // Strong fairness must not match a weak-fairness head and vice versa.
    let vars = Expr::const_(Name::from_string("vars"), vec![]);
    let action = Expr::const_(Name::from_string("A"), vec![]);
    let wf = build_weak_fairness(vars.clone(), action.clone());
    let sf = build_strong_fairness(vars, action);
    assert!(
        engine.extract_strong_fairness(&wf).is_none(),
        "extract_strong_fairness should not match a WF head"
    );
    assert!(
        engine.extract_weak_fairness(&sf).is_none(),
        "extract_weak_fairness should not match an SF head"
    );
}

#[test]
fn test_weak_fairness_unfolded_definitional_form() {
    use clean_kernel::expr::Expr;
    use clean_kernel::name::Name;

    let engine = TlaTacticEngine::new();

    let vars = Expr::const_(Name::from_string("vars"), vec![]);
    let action = Expr::const_(Name::from_string("A"), vec![]);

    let unfolded = engine.weak_fairness_unfolded(&vars, &action);

    // Outermost operator must be □ (TLA_always): WF_vars(A) = □( … ).
    let head = engine
        .extract_always(&unfolded)
        .expect("WF unfolding should be headed by □");

    // The body must be an implication □ENABLED⟨A⟩ ⇒ ◇⟨A⟩.
    let (antecedent, consequent) = engine
        .extract_implication(&head)
        .expect("WF body should be an implication");

    // Antecedent is □ of an ENABLED application.
    let enabled_inner = engine
        .extract_always(&antecedent)
        .expect("WF antecedent should be □(…)");
    let mut ant_consts = Vec::new();
    collect_const_names(&enabled_inner, &mut ant_consts);
    assert!(
        ant_consts.iter().any(|c| c == "FixedPoint.TLA_enabled"),
        "WF antecedent should mention ENABLED, got {ant_consts:?}"
    );

    // Consequent is ◇ of the angle action.
    let angle = engine
        .extract_eventually(&consequent)
        .expect("WF consequent should be ◇(…)");
    let mut cons_consts = Vec::new();
    collect_const_names(&angle, &mut cons_consts);
    // Angle action ⟨A⟩_vars = A ∧ vars' ≠ vars carries A, the prime, and Not.
    assert!(
        cons_consts.iter().any(|c| c == "A"),
        "angle action should retain the original action A, got {cons_consts:?}"
    );
    assert!(
        cons_consts.iter().any(|c| c == "TLA.prime"),
        "angle action should reference the primed vars, got {cons_consts:?}"
    );
    assert!(
        cons_consts.iter().any(|c| c == "Not"),
        "angle action should negate UNCHANGED (vars' ≠ vars), got {cons_consts:?}"
    );
}

#[test]
fn test_strong_fairness_unfolded_definitional_form() {
    use clean_kernel::expr::Expr;
    use clean_kernel::name::Name;

    let engine = TlaTacticEngine::new();

    let vars = Expr::const_(Name::from_string("vars"), vec![]);
    let action = Expr::const_(Name::from_string("A"), vec![]);

    let unfolded = engine.strong_fairness_unfolded(&vars, &action);

    // Outermost operator must be □: SF_vars(A) = □( … ).
    let head = engine
        .extract_always(&unfolded)
        .expect("SF unfolding should be headed by □");

    let (antecedent, consequent) = engine
        .extract_implication(&head)
        .expect("SF body should be an implication");

    // Antecedent is □◇ENABLED⟨A⟩: □ then ◇ then ENABLED.
    let ant_box_inner = engine
        .extract_always(&antecedent)
        .expect("SF antecedent should be □(…)");
    let ant_diamond_inner = engine
        .extract_eventually(&ant_box_inner)
        .expect("SF antecedent should be □◇(…)");
    let mut ant_consts = Vec::new();
    collect_const_names(&ant_diamond_inner, &mut ant_consts);
    assert!(
        ant_consts.iter().any(|c| c == "FixedPoint.TLA_enabled"),
        "SF antecedent should mention ENABLED, got {ant_consts:?}"
    );

    // Consequent is □◇⟨A⟩: □ then ◇ then the angle action.
    let cons_box_inner = engine
        .extract_always(&consequent)
        .expect("SF consequent should be □(…)");
    let angle = engine
        .extract_eventually(&cons_box_inner)
        .expect("SF consequent should be □◇(…)");
    let mut cons_consts = Vec::new();
    collect_const_names(&angle, &mut cons_consts);
    assert!(
        cons_consts.iter().any(|c| c == "A"),
        "SF angle action should retain action A, got {cons_consts:?}"
    );
}

#[test]
fn test_weak_fairness_obligation_dispatches_to_temporal() {
    // A WF_vars(A) goal must reach the temporal dispatcher (which now contains
    // the fairness reduction) instead of silently failing tactic selection.
    let obligation = TlaObligation::new(TlaFormula::WeakFairness(
        Box::new(crate::encoding::TlaExpr::Var("vars".to_string())),
        Box::new(TlaFormula::Expr(crate::encoding::TlaExpr::Const(
            "A".to_string(),
        ))),
    ));
    let result = prove_tla_obligation(&obligation);
    assert!(
        result
            .tactics_tried
            .contains(&"unfold_temporal".to_string()),
        "WF_vars(A) should be routed through the temporal unfolder, got: {:?}",
        result.tactics_tried
    );
}

#[test]
fn test_strong_fairness_obligation_dispatches_to_temporal() {
    let obligation = TlaObligation::new(TlaFormula::StrongFairness(
        Box::new(crate::encoding::TlaExpr::Var("vars".to_string())),
        Box::new(TlaFormula::Expr(crate::encoding::TlaExpr::Const(
            "A".to_string(),
        ))),
    ));
    let result = prove_tla_obligation(&obligation);
    assert!(
        result
            .tactics_tried
            .contains(&"unfold_temporal".to_string()),
        "SF_vars(A) should be routed through the temporal unfolder, got: {:?}",
        result.tactics_tried
    );
}

#[test]
fn test_weak_fairness_of_genuine_action_not_falsely_proved() {
    // Soundness guard: WF of a genuine (non-trivial) action is NOT a
    // tautology, so the engine must not claim it proved. It should reach the
    // temporal machinery and then honestly report failure.
    let obligation = TlaObligation::new(TlaFormula::WeakFairness(
        Box::new(crate::encoding::TlaExpr::Var("vars".to_string())),
        Box::new(TlaFormula::Expr(crate::encoding::TlaExpr::Const(
            "A".to_string(),
        ))),
    ));
    let result = prove_tla_obligation(&obligation);
    assert!(
        result
            .tactics_tried
            .contains(&"unfold_temporal".to_string()),
        "WF goal should still be dispatched, got: {:?}",
        result.tactics_tried
    );
    assert!(
        !result.proved,
        "WF of a genuine action must not be reported as proved, got: {result:?}"
    );
}

#[test]
fn test_ring_for_associativity() {
    use clean_kernel::expr::Expr;
    use clean_kernel::name::Name;

    let engine = TlaTacticEngine::new();

    // Test that (a + b) + c and a + (b + c) produce the same polynomial
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);

    // (a + b) + c
    let a_plus_b = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("TLA.add"), vec![]),
            a.clone(),
        ),
        b.clone(),
    );
    let lhs = Expr::app(
        Expr::app(Expr::const_(Name::from_string("TLA.add"), vec![]), a_plus_b),
        c.clone(),
    );

    // a + (b + c)
    let b_plus_c = Expr::app(
        Expr::app(Expr::const_(Name::from_string("TLA.add"), vec![]), b),
        c,
    );
    let rhs = Expr::app(
        Expr::app(Expr::const_(Name::from_string("TLA.add"), vec![]), a),
        b_plus_c,
    );

    let poly_lhs = engine.expr_to_polynomial(&lhs);
    let poly_rhs = engine.expr_to_polynomial(&rhs);

    // Both should be a + b + c
    assert_eq!(poly_lhs, poly_rhs, "Associativity: (a+b)+c == a+(b+c)");

    // Now test try_arith_simplify with this equality
    let eq_goal = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("TLA.eq"), vec![]),
            lhs.clone(),
        ),
        rhs.clone(),
    );

    let result = engine.try_arith_simplify(&eq_goal);
    assert!(
        result.is_some(),
        "try_arith_simplify should prove (a+b)+c = a+(b+c) via ring"
    );
    let cert = result.unwrap();
    assert!(
        cert.contains("ring"),
        "Certificate should mention ring, got: {}",
        cert
    );
}

// ====================================================================
// Multi-hop leads-to chain transitivity (P ~> A, A ~> B, B ~> R ⊢ P ~> R)
// ====================================================================

/// Build a distinct atomic state predicate named `name`.
fn lt_atom(name: &str) -> Expr {
    use clean_kernel::expr::Expr;
    use clean_kernel::name::Name;
    Expr::const_(Name::from_string(name), vec![])
}

/// Build the leads-to hypothesis `FixedPoint.TLA_leads_to a b`.
fn lt_edge(a: &Expr, b: &Expr) -> Expr {
    use clean_kernel::expr::Expr;
    use clean_kernel::name::Name;
    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("FixedPoint.TLA_leads_to"), vec![]),
            a.clone(),
        ),
        b.clone(),
    )
}

#[test]
fn test_leads_to_transitivity_three_step_chain_returns_none() {
    // Gap confirmation: the binary transitivity rule cannot close a 3-step
    // chain P ~> A, A ~> B, B ~> R for the goal P ~> R, because there is no
    // single intermediate Q with both P ~> Q and Q ~> R as hypotheses.
    let engine = TlaTacticEngine::new();
    let p = lt_atom("P");
    let a = lt_atom("A");
    let b = lt_atom("B");
    let r = lt_atom("R");

    let hyps = vec![lt_edge(&p, &a), lt_edge(&a, &b), lt_edge(&b, &r)];

    let result = engine.try_leads_to_transitivity(&p, &r, &hyps);
    assert!(
        result.is_none(),
        "binary transitivity must NOT close a genuine 3-step chain (the gap), got: {result:?}"
    );
}

#[test]
fn test_leads_to_chain_three_step_proves_goal() {
    // P ~> A, A ~> B, B ~> R ⊢ P ~> R via iterated transitivity.
    let engine = TlaTacticEngine::new();
    let p = lt_atom("P");
    let a = lt_atom("A");
    let b = lt_atom("B");
    let r = lt_atom("R");

    // Deliberately out of order to exercise the graph search.
    let hyps = vec![lt_edge(&b, &r), lt_edge(&p, &a), lt_edge(&a, &b)];

    let result = engine.try_leads_to_chain_transitivity(&p, &r, &hyps);
    let cert = result.expect("3-step chain P~>A~>B~>R should prove P~>R");
    assert!(
        cert.contains("leads_to_chain"),
        "certificate should name the chain tactic, got: {cert}"
    );
    // Chain order is P->A (hyp 1), A->B (hyp 2), B->R (hyp 0).
    assert!(
        cert.contains("\"chain\":[1,2,0]"),
        "certificate should record the ordered hypothesis indices, got: {cert}"
    );
}

#[test]
fn test_leads_to_chain_four_step_linear_path_proves_goal() {
    // A linear path of four hops: P ~> A, A ~> B, B ~> C, C ~> R ⊢ P ~> R.
    let engine = TlaTacticEngine::new();
    let p = lt_atom("P");
    let a = lt_atom("A");
    let b = lt_atom("B");
    let c = lt_atom("C");
    let r = lt_atom("R");

    let hyps = vec![
        lt_edge(&p, &a),
        lt_edge(&a, &b),
        lt_edge(&b, &c),
        lt_edge(&c, &r),
    ];

    let result = engine.try_leads_to_chain_transitivity(&p, &r, &hyps);
    let cert = result.expect("4-hop linear path P~>A~>B~>C~>R should prove P~>R");
    assert!(
        cert.contains("\"chain\":[0,1,2,3]"),
        "certificate should record all four hops in order, got: {cert}"
    );
}

#[test]
fn test_leads_to_chain_no_path_fails_cleanly() {
    // Edges exist but none connect P to R: P ~> A, B ~> R (the chain is
    // broken at A -- there is no A ~> B). The search must terminate and
    // report failure rather than fabricate a proof.
    let engine = TlaTacticEngine::new();
    let p = lt_atom("P");
    let a = lt_atom("A");
    let b = lt_atom("B");
    let r = lt_atom("R");

    let hyps = vec![lt_edge(&p, &a), lt_edge(&b, &r)];

    let result = engine.try_leads_to_chain_transitivity(&p, &r, &hyps);
    assert!(
        result.is_none(),
        "a broken chain (no path P->...->R) must fail cleanly, got: {result:?}"
    );
}

#[test]
fn test_leads_to_chain_cycle_does_not_loop_and_fails() {
    // A cycle that never reaches R: P ~> A, A ~> P. BFS must terminate via the
    // visited-set guard and report failure (R is unreachable).
    let engine = TlaTacticEngine::new();
    let p = lt_atom("P");
    let a = lt_atom("A");
    let r = lt_atom("R");

    let hyps = vec![lt_edge(&p, &a), lt_edge(&a, &p)];

    let result = engine.try_leads_to_chain_transitivity(&p, &r, &hyps);
    assert!(
        result.is_none(),
        "a cycle not reaching R must terminate and fail, got: {result:?}"
    );
}

#[test]
fn test_leads_to_chain_two_step_binary_case_still_handled() {
    // The chain method subsumes the binary case: P ~> Q, Q ~> R ⊢ P ~> R.
    let engine = TlaTacticEngine::new();
    let p = lt_atom("P");
    let q = lt_atom("Q");
    let r = lt_atom("R");

    let hyps = vec![lt_edge(&p, &q), lt_edge(&q, &r)];

    let result = engine.try_leads_to_chain_transitivity(&p, &r, &hyps);
    let cert = result.expect("chain method should also close the binary 2-hop case");
    assert!(
        cert.contains("\"chain\":[0,1]"),
        "binary chain should record both hops in order, got: {cert}"
    );
}

#[test]
fn test_leads_to_binary_transitivity_unaffected_by_chain_addition() {
    // Regression guard: the binary rule itself still fires (and is tried first)
    // on the classic 2-hop case, emitting the leads_to_trans certificate.
    let engine = TlaTacticEngine::new();
    let p = lt_atom("P");
    let q = lt_atom("Q");
    let r = lt_atom("R");

    let hyps = vec![lt_edge(&p, &q), lt_edge(&q, &r)];

    let result = engine.try_leads_to_transitivity(&p, &r, &hyps);
    let cert = result.expect("binary transitivity must still close P~>Q, Q~>R ⊢ P~>R");
    assert!(
        cert.contains("leads_to_trans"),
        "binary case must still emit leads_to_trans, got: {cert}"
    );
}

// ============================================================================
// Existential instantiation tests
// ============================================================================

/// Translate a standalone obligation's goal/hypotheses into a clean goal Expr,
/// exactly as the tactic engine sees it.
fn exists_test_goal(obligation: &TlaObligation) -> Expr {
    let mut ctx = TlaContext::new();
    obligation
        .to_clean_goal(&mut ctx)
        .expect("test obligation should translate to a clean goal")
}

#[test]
fn test_exists_instantiation_equality_lhs_var_closes_with_witness() {
    use crate::encoding::TlaExpr;
    // ∃ x : x = c  — witness is c, residual obligation c = c is reflexive.
    let goal = TlaFormula::Exists(
        "x".to_string(),
        Box::new(TlaFormula::Eq(
            Box::new(TlaExpr::Var("x".to_string())),
            Box::new(TlaExpr::Const("c".to_string())),
        )),
    );
    let obligation = TlaObligation::new(goal).with_tactic("force");
    let result = prove_tla_obligation(&obligation);
    assert!(
        result.proved,
        "∃ x : x = c should close by equality witness. tried={:?} err={:?}",
        result.tactics_tried, result.error
    );
    assert!(
        result.tactics_tried.contains(&"existsi".to_string()),
        "force should route through the existsi tactic, got: {:?}",
        result.tactics_tried
    );
}

#[test]
fn test_exists_instantiation_equality_rhs_var_closes_with_witness() {
    use crate::encoding::TlaExpr;
    // ∃ x : c = x  — symmetric equality-witness case.
    let goal = TlaFormula::Exists(
        "x".to_string(),
        Box::new(TlaFormula::Eq(
            Box::new(TlaExpr::Const("c".to_string())),
            Box::new(TlaExpr::Var("x".to_string())),
        )),
    );
    let obligation = TlaObligation::new(goal).with_tactic("force");
    let result = prove_tla_obligation(&obligation);
    assert!(
        result.proved,
        "∃ x : c = x should close by equality witness. tried={:?} err={:?}",
        result.tactics_tried, result.error
    );
}

#[test]
fn test_exists_instantiation_equality_certificate_records_witness() {
    use crate::encoding::TlaExpr;
    let goal = TlaFormula::Exists(
        "x".to_string(),
        Box::new(TlaFormula::Eq(
            Box::new(TlaExpr::Var("x".to_string())),
            Box::new(TlaExpr::Const("c".to_string())),
        )),
    );
    let engine = TlaTacticEngine::new();
    let clean_goal = exists_test_goal(&TlaObligation::new(goal));
    let cert = engine
        .try_exists_instantiation(&clean_goal)
        .expect("instantiation should not error")
        .expect("∃ x : x = c should yield a witness certificate");
    assert!(
        cert.contains("exists_instantiation") && cert.contains("\"witness\":\"c\""),
        "certificate should name the exists rule and witness c, got: {cert}"
    );
    assert!(
        cert.contains("reflexivity"),
        "equality witness should be justified by reflexivity, got: {cert}"
    );
}

#[test]
fn test_exists_instantiation_hypothesis_witness_closes() {
    use crate::encoding::TlaExpr;
    // Goal: ∃ x : x ∈ S, with hypothesis h : c ∈ S.
    // Witness c is drawn from the hypothesis; the discharged obligation c ∈ S
    // is literally the assumption.
    let goal = TlaFormula::Exists(
        "x".to_string(),
        Box::new(TlaFormula::Mem(
            Box::new(TlaExpr::Var("x".to_string())),
            Box::new(TlaExpr::Const("S".to_string())),
        )),
    );
    let hyp = TlaFormula::Mem(
        Box::new(TlaExpr::Const("c".to_string())),
        Box::new(TlaExpr::Const("S".to_string())),
    );
    let obligation = TlaObligation::new(goal)
        .with_hypothesis("h", hyp)
        .with_tactic("force");

    let engine = TlaTacticEngine::new();
    let clean_goal = exists_test_goal(&obligation);
    let cert = engine
        .try_exists_instantiation(&clean_goal)
        .expect("instantiation should not error")
        .expect("∃ x : x ∈ S should close using witness from hypothesis c ∈ S");
    assert!(
        cert.contains("hypothesis") && cert.contains("\"witness\":\"c\""),
        "certificate should record the hypothesis witness c, got: {cert}"
    );
}

#[test]
fn test_exists_instantiation_no_witness_does_not_falsely_close() {
    use crate::encoding::TlaExpr;
    // ∃ x : IsPrime(x) with no supporting hypothesis. There is no equality to
    // read a witness from and nothing in the (empty) context discharges the
    // body, so the dedicated rule must abstain rather than invent a witness.
    let goal = TlaFormula::Exists(
        "x".to_string(),
        Box::new(TlaFormula::Expr(TlaExpr::OpApply(
            "IsPrime".to_string(),
            vec![TlaExpr::Var("x".to_string())],
        ))),
    );
    let engine = TlaTacticEngine::new();
    let clean_goal = exists_test_goal(&TlaObligation::new(goal));
    let result = engine
        .try_exists_instantiation(&clean_goal)
        .expect("instantiation should not error");
    assert!(
        result.is_none(),
        "∃ x : IsPrime(x) has no sound witness; the rule must not close it, got: {result:?}"
    );
}

#[test]
fn test_exists_instantiation_wrong_hypothesis_witness_abstains() {
    use crate::encoding::TlaExpr;
    // Goal: ∃ x : x ∈ S, hypothesis mentions d but in an unrelated predicate
    // (d ∈ T, not d ∈ S). No candidate witness discharges x ∈ S, so the rule
    // must abstain — instantiating d would yield d ∈ S, which is NOT assumed.
    let goal = TlaFormula::Exists(
        "x".to_string(),
        Box::new(TlaFormula::Mem(
            Box::new(TlaExpr::Var("x".to_string())),
            Box::new(TlaExpr::Const("S".to_string())),
        )),
    );
    let hyp = TlaFormula::Mem(
        Box::new(TlaExpr::Const("d".to_string())),
        Box::new(TlaExpr::Const("T".to_string())),
    );
    let obligation = TlaObligation::new(goal).with_hypothesis("h", hyp);

    let engine = TlaTacticEngine::new();
    let clean_goal = exists_test_goal(&obligation);
    let result = engine
        .try_exists_instantiation(&clean_goal)
        .expect("instantiation should not error");
    assert!(
        result.is_none(),
        "no hypothesis discharges x ∈ S; the rule must abstain, got: {result:?}"
    );
}

#[test]
fn test_extract_exists_body_unwraps_predicate() {
    use clean_kernel::expr::{BinderInfo, Expr};
    use clean_kernel::name::Name;
    // Build: Exists (λ _ : TLA.Value. Eq (BVar 0) c)
    let body = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Eq"), vec![]), Expr::bvar(0)),
        Expr::const_(Name::from_string("c"), vec![]),
    );
    let pred = Expr::lam(
        BinderInfo::Default,
        Expr::const_(Name::from_string("TLA.Value"), vec![]),
        body.clone(),
    );
    let exists = Expr::app(Expr::const_(Name::from_string("Exists"), vec![]), pred);

    let engine = TlaTacticEngine::new();
    let extracted = engine
        .extract_exists_body(&exists)
        .expect("extract_exists_body should unwrap the predicate body");
    assert_eq!(
        extracted, body,
        "extracted body should equal the lambda body"
    );

    // A non-existential expression yields None.
    assert!(
        engine
            .extract_exists_body(&Expr::const_(Name::from_string("c"), vec![]))
            .is_none(),
        "extract_exists_body should reject non-existentials"
    );
}

/// Regression: `combine_like_terms` must not overflow-panic when two
/// attacker-controlled integer literals with the same (empty) variable key are
/// summed. `TLA.add (Int 5e18) (Int 5e18)` becomes the monomial list
/// `[(5e18, []), (5e18, [])]`; combining them computes `5e18 + 5e18 = 1e19`,
/// which exceeds `i64::MAX`. Under `overflow-checks = true` (enabled for both
/// dev and release profiles in the workspace Cargo.toml) a plain `+=` aborts
/// the whole verifier on this fully public input. The obligation below is the
/// exact adversarial trigger routed through the public `prove_tla_obligation`
/// entry with `tactic_hint = "induction"`: `do_nat_induction` instantiates the
/// bound variable with 0, producing the base case
/// `TLA.add (Int 5e18) (Int 5e18) = 0`, which `try_arith_simplify` feeds to
/// `expr_to_polynomial -> combine_like_terms`.
///
/// Before the fix this panicked (overflow) / aborted. After switching to
/// `checked_add` (which returns `None` = undecided on overflow) the call
/// returns normally; the goal is false, so the expected outcome is simply
/// "not proved" — never a false claim of success, and never a saturated
/// coefficient that could alias a distinct value.
#[test]
fn test_combine_like_terms_literal_sum_overflow_no_panic() {
    use crate::encoding::{TlaArithOp, TlaExpr};

    // ∀ n ∈ Nat, (5e18 + 5e18) = n
    let obligation = TlaObligation::new(TlaFormula::ForallIn(
        "n".to_string(),
        Box::new(TlaExpr::Nat),
        Box::new(TlaFormula::Eq(
            Box::new(TlaExpr::Arith(
                TlaArithOp::Add,
                Box::new(TlaExpr::Int(5_000_000_000_000_000_000)),
                Box::new(TlaExpr::Int(5_000_000_000_000_000_000)),
            )),
            Box::new(TlaExpr::Var("n".to_string())),
        )),
    ))
    .with_tactic("induction");

    // The sole requirement is that proof search terminates without an
    // arithmetic-overflow abort. A false goal like this must not be reported as
    // proved (soundness of the saturating path).
    let result = prove_tla_obligation(&obligation);
    assert!(
        !result.proved,
        "false overflow-literal goal must not be reported as proved"
    );
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end regression lock for **`rw` with an elaborated proof term** and
//! **`simpa using <term>`** (Track Z — tactic mode for the trust-ir bitwise
//! commutativity proofs).
//!
//! ## The gaps this guards
//!
//! trust-ir's `Nat.land`/`Nat.lxor` commutativity proofs are tactic-mode and use
//! rewrite/simp shapes that previously failed in Clean:
//!
//! ```text
//! rw [show Nat.land m n = m &&& n from rfl, …]   -- non-identifier rw rule term
//! rw [Nat.testBit_and, …]                         -- (env-const path, already worked)
//! simpa using Bool.xor_comm (m.testBit i) (n.testBit i)
//! ```
//!
//! Before Track Z, a `rw` rule whose term was *not a bare identifier* (an
//! application like `lem x y h`, or a `show A = B from …` ascription) was reduced
//! to a `format!`-derived name string by `surface_expr_to_name` and looked up as
//! a hypothesis/constant — always failing with `HypothesisNotFound("App(…)")`.
//! And `simpa using <term>` dropped the `using` term entirely at parse time, so
//! the proof term never reached the goal.
//!
//! Track Z makes `rw` *elaborate* a non-identifier rule term to a proof `Expr`
//! and rewrite by its inferred equality type (`rewrite_with_proof`), and threads
//! the `using` term through `simpa` to close the (optionally simplified) goal via
//! a kernel-checked `exact`.
//!
//! ## Why these are genuine proofs (not `sorry` / axioms)
//!
//! Each theorem below carries a real tactic proof; the test drives the SAME
//! pipeline as `clean check` (`parse_file → preprocess_decl_with_context →
//! elaborate_decl_and_register`) and additionally asserts, for every gate:
//!   * the theorem registers (the kernel re-checks the produced proof term),
//!   * `infer_type` of the proof term is def-eq to the stated proposition, and
//!   * the transitive `axiom_deps` closure is **empty** — no `sorry`/`sorryAx`/
//!     fabricated axiom anywhere underneath the generated `Eq.subst`/`exact` term.
//!
//! A pass here matches an observable `clean check` pass on surface syntax.

use clean_kernel::env::Environment;
use clean_kernel::{Name, TypeChecker};

use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_parser::parse_file;

/// Drive the real file pipeline for a (possibly multi-declaration) source.
fn try_elaborate_into(env: &mut Environment, source: &str) -> Result<(), String> {
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        elaborate_decl_and_register(env, &processed).map_err(|e| e.to_string())?;
    }
    Ok(())
}

/// Elaborate `source` (which must define `name` last as a tactic-proved theorem)
/// and assert:
///   * it elaborates + kernel-checks through the real file pipeline,
///   * `name`'s proof term `infer_type`s to a type def-eq to its proposition,
///   * `name` has an EMPTY `axiom_deps` closure (sorry-free, axiom-free).
fn assert_tactic_theorem(name: &str, source: &str) {
    let mut env = Environment::with_prelude();
    try_elaborate_into(&mut env, source)
        .unwrap_or_else(|e| panic!("`{name}` must elaborate and kernel-check: {e}"));

    let info = env
        .get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("`{name}` must be registered after elaboration"));
    let proof = info
        .value
        .as_ref()
        .unwrap_or_else(|| panic!("`{name}` theorem must carry a proof value"));

    // SOUNDNESS 1 — infer_type: the kernel re-derives the proof's type and it is
    // def-eq to the stated proposition. This is the kernel re-check of the
    // tactic-produced term (the `Eq.subst` of `rw`, or the `exact` of `simpa`).
    let tc = TypeChecker::new(&env);
    let inferred = tc
        .infer_type(proof)
        .unwrap_or_else(|e| panic!("`{name}` proof must infer a type: {e}"));
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "`{name}` proof type must be def-eq to its stated proposition:\n  got {inferred:?}\n  exp {:?}",
        info.type_
    );

    // SOUNDNESS 2 — empty axiom_deps closure: no `sorry`/`sorryAx`/fabricated
    // axiom anywhere underneath the tactic-built proof term.
    let deps = env
        .axiom_deps(&Name::from_string(name))
        .unwrap_or_else(|| panic!("`{name}` must have an axiom_deps closure"));
    assert!(
        deps.is_empty(),
        "`{name}` must be axiom-free (genuine tactic proof, no sorry/axiom); got {deps:?}"
    );
}

// ---------------------------------------------------------------------------
// GATE rw1 — `rw [<applied lemma term>]`: the rule term is an application
// `g_lem x y hh`, not a bare identifier. Previously stringified to a bogus
// `HypothesisNotFound("App(…)")`; now elaborated and rewritten by its type.
// ---------------------------------------------------------------------------

#[test]
fn rw_with_applied_lemma_term_elaborates_and_rewrites() {
    assert_tactic_theorem(
        "rw_applied",
        "theorem g_lem (a b : Nat) (h : a = b) : a = b := h\n\
         theorem rw_applied (x y : Nat) (hh : x = y) : x = y := by rw [g_lem x y hh]",
    );
}

// ---------------------------------------------------------------------------
// GATE rw2 — `rw [<applied unfold lemma>]` rewrites a *use of a reducible
// defined constant* (`dbl n`) to its body (`n + n`). This is the
// `Nat.land m n = m &&& n` rewrite shape: the rule type is genuinely `A = B`
// with A a def-use, and the `from` side must be matched syntactically (not
// WHNF-unfolded) in the goal.
// ---------------------------------------------------------------------------

#[test]
fn rw_with_applied_unfold_lemma_rewrites_def_use_to_body() {
    assert_tactic_theorem(
        "rw_unfold",
        "def dbl (n : Nat) : Nat := n + n\n\
         theorem dbl_unfold (n : Nat) : dbl n = n + n := rfl\n\
         theorem rw_unfold (n : Nat) : dbl n = n + n := by rw [dbl_unfold n]",
    );
}

// ---------------------------------------------------------------------------
// GATE rw3 — `rw [show a = a from rfl]`: a `show … from …` ascription rule term
// (non-identifier) is elaborated and rewritten.
// ---------------------------------------------------------------------------

#[test]
fn rw_with_show_from_rfl_term_elaborates_and_rewrites() {
    assert_tactic_theorem(
        "rw_show",
        "theorem rw_show (a : Nat) : a = a := by rw [show a = a from rfl]",
    );
}

// ---------------------------------------------------------------------------
// GATE rw3b (Track JJ) — `rw [show <def-use> = <body> from rfl]` where the two
// written sides differ and the LHS is a *use of a reducible defined constant*
// (`D x`). This is the trust-ir `nat_land_comm` shape:
//
//     rw [show Nat.land m n = m &&& n from rfl]
//
// where `Nat.land` is a real `def` (= `Nat.bitwise and`). The `from rfl` proof
// type-checks because the two sides are def-eq, but a `rfl : @Eq T a a` carries
// only ONE side; inferring it re-derives both sides from that one expression,
// δ-unfolding the def-use `D x` to its `Nat.rec` body. The rewrite then searches
// the goal for the *unfolded* form, which does not occur (the goal still holds
// the folded `D x`), and fails `RewriteNoMatch`.
//
// The ascription elaborator now preserves the WRITTEN sides (`D x` and the body
// notation) so the folded `from` side matches the goal. SOUNDNESS is unchanged:
// the proof is the applied-identity beta-redex `(fun h : (D x = body) => h) rfl`,
// which the kernel re-checks (it still requires `rfl : D x = body` by def-eq).
// ---------------------------------------------------------------------------

#[test]
fn rw_with_show_from_rfl_unfolds_reducible_def_use_track_jj() {
    assert_tactic_theorem(
        "rw_show_unfold",
        "def D (n : Nat) : Nat := n + n\n\
         theorem rw_show_unfold (x : Nat) : D x = x + x := by \
            rw [show D x = x + x from rfl]",
    );
}

// ---------------------------------------------------------------------------
// GATE simpa1 — `simpa using <hyp>`: the `using` term is parsed, elaborated,
// and closes the goal. Previously the `using` clause was dropped at parse time.
// ---------------------------------------------------------------------------

#[test]
fn simpa_using_hypothesis_closes_goal() {
    assert_tactic_theorem(
        "simpa_using_hyp",
        "theorem simpa_using_hyp (p : Prop) (h : p) : p := by simpa using h",
    );
}

// ---------------------------------------------------------------------------
// GATE simpa2 — `simpa using <applied Bool-comm lemma>`: the trust-ir XOR shape,
// `simpa using Bool.xor_comm …`, modelled with a locally-proved (axiom-free,
// `cases … rfl`) Bool commutativity lemma applied to the goal's arguments.
// ---------------------------------------------------------------------------

#[test]
fn simpa_using_applied_bool_comm_lemma_closes_xor_goal() {
    assert_tactic_theorem(
        "xor_via_simpa",
        "theorem g_bxor_comm (a b : Bool) : Bool.xor a b = Bool.xor b a := by \
            cases a <;> cases b <;> rfl\n\
         theorem xor_via_simpa (x y : Bool) : Bool.xor x y = Bool.xor y x := by \
            simpa using g_bxor_comm x y",
    );
}

// ---------------------------------------------------------------------------
// GATE shape — the combined `Nat.eq_of_testBit_eq` proof shape:
// `apply <lemma with ∀i premise>; intro i; <close>`. Exercises apply + intro
// + a term close in one tactic block (the bitwise-commutativity skeleton).
// ---------------------------------------------------------------------------

#[test]
fn apply_intro_testbit_proof_shape_closes() {
    assert_tactic_theorem(
        "testbit_shape",
        "theorem g_all_imp {m n : Nat} (h : forall (i : Nat), m = n) : m = n := h 0\n\
         theorem testbit_shape (a b : Nat) (hh : forall (i : Nat), a = b) : a = b := by\n\
           apply g_all_imp\n\
           intro i\n\
           exact hh i",
    );
}

#[test]
fn generated_receiver_prefix_is_consumed_before_generic_rewrite_matching() {
    use clean_elab::module_driver::{
        elaborate_decls, module_elaboration_lock, DriverOptions, VerdictKind,
    };

    let _lock = module_elaboration_lock();
    let source = include_str!("../../../reports/self-proof-w1-map-levels-respect/Nested.lean");
    let mut env = Environment::with_prelude();
    let cases = parse_file(source).expect("parse measured fixture");
    let report = elaborate_decls(
        &mut env,
        &cases,
        source,
        &mut FileContext::new(),
        DriverOptions {
            lean_front_door: true,
            ..Default::default()
        },
        &mut (),
    );
    let refused: Vec<_> = report
        .verdicts
        .iter()
        .filter(|v| v.kind != VerdictKind::Passed)
        .map(|v| v.name.as_str())
        .collect();
    assert_eq!(report.verdicts.len(), 9);
    assert_eq!(refused, ["RespectProbe.falseIndex"], "{report:?}");
}

#[test]
fn generated_receiver_prefix_keeps_remaining_binders_and_authored_lambdas() {
    let code = r#"
structure RwCell where
  n : Nat
def RwCell.fold (x y : Nat) (s : RwCell) : Nat := s.n + x + y
def rwFull (s : RwCell) (x y : Nat) := s.fold x y
def rwGrouped (s : RwCell) (x y : Nat) := (s.fold) x y
def rwGroupedPrefix (s : RwCell) (x y : Nat) := (fun a b => RwCell.fold a b s) x y
def rwPrefix (s : RwCell) (x y : Nat) := RwCell.fold x y s
def rwPartial (s : RwCell) (x : Nat) := s.fold x
def rwPartialPrefix (s : RwCell) (x : Nat) := fun y => RwCell.fold x y s
def rwAuthored (s : RwCell) (x y : Nat) := (fun z => RwCell.fold z y s) x
"#;
    let mut env = Environment::with_prelude();
    try_elaborate_into(&mut env, code).expect("well-typed field applications");
    let value = |name: &str| {
        env.get_const(&Name::from_string(name))
            .unwrap()
            .value
            .as_ref()
            .unwrap()
    };
    assert_eq!(value("rwFull"), value("rwPrefix"));
    assert_eq!(value("rwGrouped"), value("rwGroupedPrefix"));
    assert_ne!(value("rwGrouped"), value("rwPrefix"));
    assert_eq!(value("rwPartial"), value("rwPartialPrefix"));
    assert_ne!(value("rwAuthored"), value("rwPrefix"));
}

#[test]
fn rw_keeps_lambda_applications_as_distinct_occurrences() {
    let rules = r#"
theorem groupedRule (n : Nat) : (fun x : Nat => Nat.succ x) n = Nat.succ n := rfl
theorem directRule (n : Nat) : Nat.succ n = (fun x : Nat => Nat.succ x) n := rfl
"#;
    let subject = "g ((fun x : Nat => Nat.succ x) n) = g (Nat.succ n)";
    let plain = "g (Nat.succ n) = g (Nat.succ n)";
    for rule in [
        "groupedRule",
        "groupedRule n",
        "← directRule",
        "← directRule n",
    ] {
        let source = |target: &str| {
            format!(
                "{rules}\ntheorem nested (g : Nat → Nat) (n : Nat) : {target} := by rw [{rule}]"
            )
        };
        assert_tactic_theorem("nested", &source(subject));
        let refusal = try_elaborate_into(&mut Environment::with_prelude(), &source(plain))
            .expect_err("rw must retain the lambda application key");
        assert!(refusal.contains("did not match"), "{rule}: {refusal}");
    }
}

#[test]
fn rw_skips_open_occurrences_under_binders_and_visits_closed_children() {
    let source = |target: &str, rule: &str| {
        format!("theorem succ_eq (n : Nat) : Nat.succ n = n + 1 := rfl\ntheorem nested : {target} := by rw [{rule}]")
    };
    let closed = "(fun (_ : Nat) => Nat.succ 1) = (fun (_ : Nat) => 1 + 1)";
    let mixed = "(fun x : Nat => (Nat.succ x, Nat.succ 1)) = (fun x : Nat => (Nat.succ x, 1 + 1))";
    for (target, rule) in [
        (closed, "succ_eq"),
        (closed, "succ_eq 1"),
        (mixed, "succ_eq"),
    ] {
        assert_tactic_theorem("nested", &source(target, rule));
    }
    let open = "(fun x : Nat => Nat.succ x) = (fun x : Nat => x + 1)";
    let false_result = "(fun (_ : Nat) => Nat.succ 1) = (fun (_ : Nat) => (3 : Nat))";
    for (target, rule, expected) in [
        (open, "succ_eq", "did not match"),
        (open, "succ_eq 1", "did not match"),
        (false_result, "succ_eq 1", "unsolved goal"),
    ] {
        let error = try_elaborate_into(&mut Environment::with_prelude(), &source(target, rule))
            .expect_err("invalid occurrence or false rewrite conclusion");
        assert!(error.contains(expected), "{rule}: {error}");
    }
}

#[test]
fn tactic_entry_exposes_a_dependent_goal_and_retains_an_intro_let_binder() {
    let positives = [
        (
            "correctLetIntro",
            "(let A := True; A → A) := by intro A x; exact x",
        ),
        (
            "nestedOmega",
            "(fun n : Nat => (fun k : Nat => k > 0) n) 1 := by omega",
        ),
        ("simpleOmega", "(fun n : Nat => n > 0) 1 := by omega"),
        ("letOmega", "(let n : Nat := 1; n > 0) := by omega"),
        (
            "betaConstructor",
            "∃ n : Nat, (fun k : Nat => k > 0) n := ⟨1, by omega⟩",
        ),
    ];
    for (name, declaration) in positives {
        assert_tactic_theorem(name, &format!("theorem {name} : {declaration}"));
    }
    let source = "theorem oldLetIntro : (let A := True; A → A) := by intro x; exact x";
    let error = try_elaborate_into(&mut Environment::with_prelude(), source)
        .expect_err("intro binds the let entry before the implication premise");
    assert!(error.contains("type mismatch"), "{error}");
}

#[test]
fn applied_rewrite_selects_a_registered_operator_result_field() {
    let declarations = r#"
structure RwPoint where
  x : Int
  y : Int
instance : Add RwPoint where
  add a b := ⟨a.x + b.x, a.y * b.y⟩
def RwPoint.readX (p : RwPoint) : Int := p.x
"#;
    let source = |field: &str, rule: &str| {
        format!(
            "{declarations}\ntheorem pointField (u v : RwPoint) : \
             (u + v).{field} = (v + u).{field} := by rw [{rule}]"
        )
    };
    assert_tactic_theorem("pointField", &source("x", "Int.add_comm u.x v.x"));
    for (field, rule) in [
        ("y", "Int.add_comm"),
        ("y", "Int.add_comm u.y v.y"),
        ("readX", "Int.add_comm"),
        ("readX", "Int.add_comm u.x v.x"),
    ] {
        let err = try_elaborate_into(&mut Environment::with_prelude(), &source(field, rule))
            .expect_err("only a registered field with the matching operation can be selected");
        assert!(err.contains("did not match"), "{field} / {rule}: {err}");
    }
}

#[test]
fn visible_rewrite_occurrences_take_priority_over_operator_result_fields() {
    let first = "(v.x + u.x) (u.x + v.x)";
    let second = "(u + v).x (v.x + u.x)";
    let both = "(v.x + u.x) (v.x + u.x)";
    for rule in ["Int.add_comm", "Int.add_comm u.x v.x"] {
        let source = |hyp: &str| {
            format!(
                "structure S where\n  x : Int\ninstance : Add S where\n  add u v := ⟨u.x + v.x⟩\n\
             theorem checkMixed (P : Int → Int → Prop) (u v : S) (h : P {hyp}) : \
             P (u + v).x (u.x + v.x) := by\n  rw [{rule}]\n  exact h"
            )
        };
        assert_tactic_theorem("checkMixed", &source(second));
        for crossed in [first, both] {
            let err = try_elaborate_into(&mut Environment::with_prelude(), &source(crossed))
                .expect_err("rw must leave the earlier hidden occurrence untouched");
            assert!(err.contains("type mismatch"), "{crossed} / {rule}: {err}");
        }
    }
}

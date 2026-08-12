// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Audit rows d01 / e08 / e09 — `match h :` discriminant hypothesis, Sigma
//! application, PSigma arity (docs/plans/ELAB_ARMS_AUDIT_2026-07-08.md §1).
//!
//! End-to-end (parse → elaborate → kernel re-check) coverage:
//!
//! 1. d01 `match h : e with` (Lean `Lean/Parser/Term.lean:275 matchDiscr`,
//!    `Lean/Elab/Match.lean:67 Discr`): the annotated discriminant binds a
//!    per-branch equality hypothesis `h : e = <branch pattern>`. POSITIVE
//!    shapes pin the hypothesis TYPE per branch (a checker function whose
//!    signature demands exactly `e = <pattern>`) and pin VALUES with `rfl`
//!    (the casesOn lowering + trailing `Eq.refl` application must compute).
//!    Descoped sub-shapes fail LOUD with `MatchDiscrHypUnsupported` — never
//!    silently dropped, never sorry.
//! 2. e08 Sigma — `Sigma.mk`/`Sigma.fst`/`Sigma.snd` carry Lean-exact binder
//!    info (`{β}` implicit, `Init/Core.lean:266`, oracle `#check @Sigma.mk`),
//!    so plain (non-`@`) applications elaborate. The audit's original probe
//!    `(x : Nat) × (x = x)` is pinned as MUST-REJECT — Lean rejects it too
//!    (`x = x : Prop` where `Type u` is required), so Clean's loud
//!    TypeMismatch is parity, not a gap.
//! 3. e09 PSigma — registered in the kernel prelude via the fully-checked
//!    `add_inductive`/`add_decl(Definition)` path (`Init/Core.lean:301`),
//!    with Lean-exact `{β}` on `PSigma.mk`. `Σ' x : T, b` / `(x : T) ×' b` /
//!    bare `PSigma (fun …)` all elaborate; anonymous constructors and
//!    projections compute by `rfl`.
//!
//! Axiom hygiene: every positive definition below has an EMPTY transitive
//! axiom closure (no new axioms, no sorry — `rfl` pins would fail otherwise).

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::Name;
use clean_parser::parse_file;

/// Parse + elaborate + kernel-check + register every decl in `source` on top
/// of the default prelude. Err carries the first failure.
fn elaborate_module(source: &str) -> Result<Environment, String> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let result = elaborate_decl_and_register(&mut env, &processed)
            .map_err(|e| format!("elaborate/kernel-check error: {e}"))?;
        let mut failures = Vec::new();
        collect_failures(&result, &mut failures);
        if !failures.is_empty() {
            return Err(format!(
                "inner declaration(s) failed:\n{}",
                failures.join("\n")
            ));
        }
    }
    Ok(env)
}

fn collect_failures(result: &ElabResult, out: &mut Vec<String>) {
    match result {
        ElabResult::Multiple(results) => {
            for r in results {
                collect_failures(r, out);
            }
        }
        ElabResult::Failed { name, error, .. } => out.push(format!("{name}: {error}")),
        _ => {}
    }
}

/// Assert `source` fails somewhere in parse/elab/kernel (fail-closed), and
/// return the failure text for shape assertions.
fn expect_rejected(source: &str, what: &str) -> String {
    match elaborate_module(source) {
        Ok(_) => {
            panic!("{what} must be rejected (fail-closed), but it elaborated and kernel-checked")
        }
        Err(e) => e,
    }
}

fn axiom_closure(env: &Environment, name: &str) -> Vec<String> {
    env.axiom_deps(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{name} should be registered"))
        .iter()
        .map(ToString::to_string)
        .collect()
}

fn assert_axiom_free(env: &Environment, names: &[&str]) {
    for name in names {
        assert!(
            axiom_closure(env, name).is_empty(),
            "{name} must have an EMPTY transitive axiom closure (no sorry, no new axioms)"
        );
    }
}

// =========================================================================
// d01 — `match h : e with` (annotated discriminant)
// =========================================================================

#[test]
fn test_match_hyp_audit_probe_elaborates_and_computes() {
    // The exact audit d01 probe shape, plus rfl value pins through both
    // branches (the casesOn lowering, the equation-wrapped motive, and the
    // trailing `Eq.refl` application must all COMPUTE, not just typecheck).
    let env = elaborate_module(
        r"
def f (n : Nat) : Nat := match h : n with
  | 0 => 0
  | k+1 => k
theorem f_zero : f 0 = 0 := rfl
theorem f_three : f 3 = 2 := rfl
",
    )
    .expect("audit d01 probe `match h : n with` must elaborate and kernel-check");
    assert_axiom_free(&env, &["f", "f_zero", "f_three"]);
}

#[test]
fn test_match_hyp_binds_per_branch_pattern_equation() {
    // The load-bearing semantics: in the branch for pattern `pᵢ` the
    // hypothesis has EXACTLY the type `n = pᵢ` (per-branch pattern instance,
    // Lean/Elab/Match.lean:67). The checker functions demand those types, so
    // any drift (wrong side, wrong instance, dropped hypothesis) fails
    // elaboration or the kernel re-check.
    let env = elaborate_module(
        r"
def wantEq0 (n : Nat) (p : n = 0) : Nat := 7
def wantEqSucc (n k : Nat) (p : n = k + 1) : Nat := k
def usesH (n : Nat) : Nat := match h : n with
  | 0 => wantEq0 n h
  | k+1 => wantEqSucc n k h
theorem usesH_zero : usesH 0 = 7 := rfl
theorem usesH_three : usesH 3 = 2 := rfl
",
    )
    .expect("per-branch `h : n = <pattern>` must typecheck against the exact equation type");
    assert_axiom_free(&env, &["usesH", "usesH_zero", "usesH_three"]);
}

#[test]
fn test_match_hyp_option_payload_equation() {
    // Constructor with a field: in the `some k` branch, `h : o = some k`.
    let env = elaborate_module(
        r"
def wantEqSome (o : Option Nat) (k : Nat) (p : o = some k) : Nat := k
def optCase (o : Option Nat) : Nat := match h : o with
  | none => 0
  | some k => wantEqSome o k h
theorem optCase_none : optCase none = 0 := rfl
theorem optCase_some : optCase (some 5) = 5 := rfl
",
    )
    .expect("`match h : o with | some k =>` must bind `h : o = some k`");
    assert_axiom_free(&env, &["optCase", "optCase_none", "optCase_some"]);
}

#[test]
fn test_match_hyp_bool_and_unused_hypothesis() {
    // Bool scrutinee; the hypothesis may go unused — the lowering must not
    // depend on the arm body mentioning `h`.
    let env = elaborate_module(
        r"
def bnot (b : Bool) : Bool := match h : b with
  | true => false
  | false => true
theorem bnot_true : bnot true = false := rfl
theorem bnot_false : bnot false = true := rfl
",
    )
    .expect("`match h : b with` over Bool must elaborate with `h` unused");
    assert_axiom_free(&env, &["bnot", "bnot_true", "bnot_false"]);
}

#[test]
fn test_match_hyp_catchall_var_binds_pattern_variable_equation() {
    // Single catch-all variable pattern: Lean binds `h : n = m` where `m` is
    // the pattern variable (the let-encoded lowering; `Eq.refl` checks
    // against `n = m` through the zeta-transparent `m := n`).
    let env = elaborate_module(
        r"
def wantEqVar (n m : Nat) (p : n = m) : Nat := m
def catchAll (n : Nat) : Nat := match h : n with
  | m => wantEqVar n m h
theorem catchAll_five : catchAll 5 = 5 := rfl
",
    )
    .expect("single catch-all `match h : n with | m =>` must bind `h : n = m`");
    assert_axiom_free(&env, &["catchAll", "catchAll_five"]);
}

#[test]
fn test_match_hyp_wildcard_arms() {
    // A trailing wildcard arm under a hypothesis match: the wildcard expands
    // per remaining constructor and each expansion carries its own equation.
    // Also the single-wildcard-arm form.
    let env = elaborate_module(
        r"
def wexp (n : Nat) : Nat := match h : n with
  | 0 => 0
  | _ => 1
theorem wexp_zero : wexp 0 = 0 := rfl
theorem wexp_two : wexp 2 = 1 := rfl
def wonly (n : Nat) : Nat := match h : n with
  | _ => 3
theorem wonly_val : wonly 9 = 3 := rfl
",
    )
    .expect("wildcard arms under `match h :` must elaborate");
    assert_axiom_free(
        &env,
        &["wexp", "wexp_zero", "wexp_two", "wonly", "wonly_val"],
    );
}

#[test]
fn test_match_hyp_compound_scrutinee() {
    // Non-fvar scrutinee: the equation mentions the full expression
    // (`h : n + 1 = <pattern>`), exactly as in Lean.
    let env = elaborate_module(
        r"
def addCase (n : Nat) : Nat := match h : n + 1 with
  | 0 => 0
  | k+1 => k
theorem addCase_val : addCase 4 = 4 := rfl
",
    )
    .expect("`match h : n + 1 with` (compound scrutinee) must elaborate");
    assert_axiom_free(&env, &["addCase", "addCase_val"]);
}

// ---- d01 loud negatives (descoped sub-shapes; typed, never silent) ------

#[test]
fn test_match_hyp_multi_discriminant_rejected_loud() {
    // Clean packs multiple discriminants into one `Prod.mk` scrutinee, which
    // cannot carry a per-discriminant equation — the parser refuses.
    let err = expect_rejected(
        "def bad (a b : Nat) : Nat := match h : a, b with | _, _ => 0\n",
        "`match h : a, b with` (hypothesis + multiple discriminants)",
    );
    // At file level the typed `UnexpectedToken("... multiple discriminants
    // ...")` is surfaced through decl-level error recovery (a loud RawDecl
    // rejection); the precise message is asserted at `parse_expr` level in
    // `clean-parser/src/grammar/tests.rs`.
    assert!(
        err.contains("multiple discriminants")
            || err.contains("parser recovery produced raw declaration"),
        "must fail loud at parse; got: {err}"
    );
}

#[test]
fn test_match_hyp_string_literal_match_rejected_loud() {
    let err = expect_rejected(
        "def bads (s : String) : Nat := match h : s with | \"a\" => 0 | _ => 1\n",
        "`match h : s with` over String literal patterns",
    );
    assert!(
        err.contains("unsupported `match h : "),
        "must fail with the typed MatchDiscrHypUnsupported error; got: {err}"
    );
}

#[test]
fn test_match_hyp_on_decreasing_arg_rejected_loud() {
    // `T.rec` lowering (match on the decreasing argument of a recursive def)
    // is descoped for the hypothesis form.
    let err = expect_rejected(
        "def r (n : Nat) : Nat := match h : n with | 0 => 0 | k+1 => r k\n",
        "`match h :` on the decreasing argument of a recursive definition",
    );
    assert!(
        err.contains("unsupported `match h : "),
        "must fail with the typed MatchDiscrHypUnsupported error; got: {err}"
    );
}

// =========================================================================
// e08 — Sigma application
// =========================================================================

#[test]
fn test_sigma_type_formations_elaborate() {
    let env = elaborate_module(
        r"
def sigAnon : Type := (x : Nat) × Fin x
def sigBinder : Type := Σ x : Nat, Fin x
",
    )
    .expect("`(x : Nat) × Fin x` and `Σ x : Nat, Fin x` type formations must elaborate");
    assert_axiom_free(&env, &["sigAnon", "sigBinder", "Sigma", "Sigma.mk"]);
}

#[test]
fn test_sigma_mk_plain_application_elaborates_and_computes() {
    // The genuine e08 defect: `Sigma.mk 1 2` (no `@`) mis-slotted `1` into
    // the previously-EXPLICIT `β` parameter. With Lean-exact binder info
    // (`{β}` implicit) the plain application elaborates and computes.
    let env = elaborate_module(
        r"
def p2 : (x : Nat) × Nat := Sigma.mk 1 2
theorem p2_fst : p2.fst = 1 := rfl
theorem p2_snd : p2.snd = 2 := rfl
def getFst (p : (x : Nat) × Nat) : Nat := Sigma.fst p
def getSnd (p : (x : Nat) × Nat) : Nat := Sigma.snd p
theorem getFst_val : getFst (Sigma.mk 4 5) = 4 := rfl
theorem getSnd_val : getSnd (Sigma.mk 4 5) = 5 := rfl
",
    )
    .expect("plain `Sigma.mk`/`Sigma.fst`/`Sigma.snd` applications must elaborate (audit e08)");
    assert_axiom_free(
        &env,
        &[
            "p2",
            "p2_fst",
            "p2_snd",
            "getFst",
            "getSnd",
            "Sigma.fst",
            "Sigma.snd",
        ],
    );
}

#[test]
fn test_sigma_anonymous_constructor_elaborates_and_computes() {
    let env = elaborate_module(
        r"
def p1 : (x : Nat) × Nat := ⟨1, 2⟩
theorem p1_fst : p1.fst = 1 := rfl
theorem p1_snd : p1.snd = 2 := rfl
",
    )
    .expect("anonymous constructor `⟨1, 2⟩ : (x : Nat) × Nat` must elaborate");
    assert_axiom_free(&env, &["p1", "p1_fst", "p1_snd"]);
}

#[test]
fn test_sigma_dependent_second_component() {
    // Genuinely dependent snd: `β = fun n => List (Fin n)`; the second
    // component's type is forced by the first (oracle-checked on
    // v4.30.0-rc2).
    let env = elaborate_module(
        r"
def pd : (n : Nat) × List (Fin n) := Sigma.mk 1 []
theorem pd_fst : pd.fst = 1 := rfl
",
    )
    .expect("dependent `Sigma.mk 1 [] : (n : Nat) × List (Fin n)` must elaborate");
    assert_axiom_free(&env, &["pd", "pd_fst"]);
}

#[test]
fn test_sigma_prop_component_rejected_like_lean() {
    // The audit's ORIGINAL e08 probe. Lean v4.30.0-rc2 rejects it (`x = x :
    // Prop` of sort `Type`, expected `Type u` — Sigma is Type-only); Clean's
    // loud TypeMismatch is PARITY, and must never flip to acceptance.
    expect_rejected(
        "def m : Type := (x : Nat) × (x = x)\n",
        "`(x : Nat) × (x = x)` (Prop second component; Lean rejects too)",
    );
}

// =========================================================================
// e09 — PSigma arity
// =========================================================================

#[test]
fn test_psigma_audit_probes_elaborate() {
    // The exact audit e09 probe plus the `×'` anonymous-binder form and the
    // bare head application (the old `TooManyArguments Sort(u)` shape came
    // from `PSigma` being ABSENT from the prelude and auto-bound as an
    // implicit `Sort`-typed binder).
    let env = elaborate_module(
        r"
def m : Type := Σ' _ : Nat, Nat
def t4 : Type := (x : Nat) ×' Nat
def m2 := PSigma (fun _ : Nat => Nat)
",
    )
    .expect("`Σ' _ : Nat, Nat` / `(x : Nat) ×' Nat` / bare `PSigma` must elaborate (audit e09)");
    assert_axiom_free(&env, &["m", "t4", "m2", "PSigma", "PSigma.mk"]);
}

#[test]
fn test_psigma_values_elaborate_and_compute() {
    let env = elaborate_module(
        r"
def p : Σ' _ : Nat, Nat := ⟨1, 2⟩
theorem p_fst : p.fst = 1 := rfl
theorem p_snd : p.snd = 2 := rfl
def pm : Σ' _ : Nat, Nat := PSigma.mk 1 2
theorem pm_fst : PSigma.fst pm = 1 := rfl
",
    )
    .expect("PSigma anonymous constructor / plain `PSigma.mk` must elaborate and compute");
    assert_axiom_free(
        &env,
        &[
            "p",
            "p_fst",
            "p_snd",
            "pm",
            "pm_fst",
            "PSigma.fst",
            "PSigma.snd",
        ],
    );
}

#[test]
fn test_psigma_sort_polymorphic_prop_component() {
    // What PSigma exists FOR (vs Sigma): `Sort`-polymorphic components. A
    // Prop-valued second component is accepted (`Σ' n : Nat, n = n : Type`).
    let env = elaborate_module(
        r"
def psp : Σ' n : Nat, n = n := ⟨0, rfl⟩
theorem psp_fst : psp.fst = 0 := rfl
",
    )
    .expect("`Σ' n : Nat, n = n := ⟨0, rfl⟩` (Prop second component) must elaborate");
    assert_axiom_free(&env, &["psp", "psp_fst"]);
}

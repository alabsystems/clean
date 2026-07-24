// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Sweep brick B09 — dependent motive specialization: proof-by-match + `dite`
//! hypothesis (docs/plans/GAP_SWEEP_2026-07-09.md §3 Tier-1).
//!
//! End-to-end (parse → elaborate → kernel re-check) coverage of the two
//! functional gaps the sweep flagged as "the single highest-impact functional
//! gap for idiomatic Lean proofs":
//!
//! 1. **Proof-by-match** (`match_variants/p16`). A `theorem` proved by matching
//!    the scrutinee and discharging each arm with a per-constructor proof
//!    (`fun n => match n with | 0 => Or.inl rfl | m+1 => Or.inr ⟨m, rfl⟩`).
//!    Pre-fix, arm 0's expected type kept the scrutinee fvar (`n = 0` instead of
//!    `0 = 0`), so `rfl` was checked against the wrong equation and elaboration
//!    failed. The fix: for a NON-indexed scrutinee whose expected type depends
//!    on the scrutinee VALUE, the `branch_ty` used for the eliminator levels is
//!    the raw expected type (the motive at the scrutinee) — never re-inferred by
//!    elaborating arm 0's body against the UNspecialized expected type — and each
//!    arm is checked against `motive[scrutinee := ctorᵢ …]` (`arm_branch_ty`).
//!
//! 2. **`dite` hypothesis** (`term_sugar/p22`). `if h : c then … else …` where
//!    `h` is consumed in a branch. The branch lambdas bind `h : c` / `h : ¬c`,
//!    and the surrounding expected type flows into BOTH branches (`dite`'s result
//!    type is fixed), with the else branch checked against the then-branch's type
//!    so cross-branch metavariables (`Or.inl h`'s right disjunct pinned by
//!    `Or.inr h`'s) resolve — a `dite` in inference position no longer leaks an
//!    unresolved metavariable to the kernel.
//!
//! Every positive theorem/def below is pinned axiom-free (an empty transitive
//! axiom closure — a stray `sorry`/motive-fudge would show up here) and the
//! computable ones carry `rfl` value pins. Loud negatives (a WRONG arm proof, a
//! WRONG `dite` branch) must FAIL closed — never silently certify.

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::Name;
use clean_parser::parse_file;

/// Parse + elaborate + kernel-check + register every decl in `source` on top of
/// the default prelude. Err carries the first failure.
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

/// Assert `source` fails somewhere in parse/elab/kernel (fail-closed).
fn expect_rejected(source: &str, what: &str) -> String {
    match elaborate_module(source) {
        Ok(_) => {
            panic!("{what} must be rejected (fail-closed), but it elaborated and kernel-checked")
        }
        Err(e) => e,
    }
}

fn assert_axiom_free(env: &Environment, names: &[&str]) {
    for name in names {
        let deps = env
            .axiom_deps(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert!(
            deps.is_empty(),
            "{name} must have an EMPTY transitive axiom closure (no sorry, no motive fudge); got {deps:?}"
        );
    }
}

// =========================================================================
// 1. Proof-by-match (match_variants/p16)
// =========================================================================

#[test]
fn test_proof_by_match_p16_zero_or_succ() {
    // The EXACT p16 probe: a theorem proved by matching `n` and giving each arm
    // its own per-constructor proof. Arm 0 needs `0 = 0` (not `n = 0`); arm
    // `m+1` needs `∃ m, (m+1) = m + 1`. Pre-fix this failed with
    // `TypeMismatch { expected: Eq Nat (FVar n) 0 }`.
    let env = elaborate_module(
        r"
theorem zero_or_succ : ∀ n : Nat, n = 0 ∨ ∃ m, n = m + 1 :=
  fun n => match n with
  | 0 => Or.inl rfl
  | m + 1 => Or.inr ⟨m, rfl⟩
",
    )
    .expect("p16 proof-by-match must elaborate and kernel-check");
    assert_axiom_free(&env, &["zero_or_succ"]);
}

#[test]
fn test_proof_by_match_equation_form() {
    // Same content in the equation (no leading `fun n =>`) form — the scrutinee
    // is still a bare fvar the expected type depends on.
    let env = elaborate_module(
        r"
theorem zos (n : Nat) : n = 0 ∨ ∃ m, n = m + 1 :=
  match n with
  | 0 => Or.inl rfl
  | m + 1 => Or.inr ⟨m, rfl⟩
",
    )
    .expect("equation-form proof-by-match must elaborate and kernel-check");
    assert_axiom_free(&env, &["zos"]);
}

#[test]
fn test_proof_by_match_minimal_n_eq_n() {
    // The sweep's minimal reduction `∀ n, n = 0 ∨ n = n` — arm 0 proves
    // `0 = 0 ∨ 0 = 0` (`Or.inl rfl`), arm `m+1` proves `… ∨ (m+1) = (m+1)`.
    let env = elaborate_module(
        r"
theorem zero_or_self (n : Nat) : n = 0 ∨ n = n :=
  match n with
  | 0 => Or.inl rfl
  | _ + 1 => Or.inr rfl
",
    )
    .expect("minimal proof-by-match must elaborate and kernel-check");
    assert_axiom_free(&env, &["zero_or_self"]);
}

#[test]
fn test_proof_by_match_option() {
    // Proof-by-match on `Option` (a genuine 2-constructor inductive, not Nat's
    // literal/succ special-casing): `o = none ∨ ∃ x, o = some x`.
    let env = elaborate_module(
        r"
theorem opt_cases (o : Option Nat) : o = none ∨ ∃ x, o = some x :=
  match o with
  | none => Or.inl rfl
  | some x => Or.inr ⟨x, rfl⟩
",
    )
    .expect("Option proof-by-match must elaborate and kernel-check");
    assert_axiom_free(&env, &["opt_cases"]);
}

#[test]
fn test_proof_by_match_nested() {
    // Nested proof-by-match: the outer match on `p` is a dependent-motive proof,
    // and the `q+1` arm's body is ITSELF a dependent-motive proof-by-match on
    // `q`. Both levels must specialize per arm.
    let env = elaborate_module(
        r"
theorem nested_pbm (p : Nat) : p = 0 ∨ ∃ m, p = m + 1 :=
  match p with
  | 0 => Or.inl rfl
  | q + 1 =>
    match q with
    | 0 => Or.inr ⟨0, rfl⟩
    | r + 1 => Or.inr ⟨r + 1, rfl⟩
",
    )
    .expect("nested proof-by-match must elaborate and kernel-check");
    assert_axiom_free(&env, &["nested_pbm"]);
}

#[test]
fn test_value_dependent_motive_type_family() {
    // A VALUE-dependent motive (the `match_variants/p15` shape, minus the
    // type-level `ite` that p15 additionally trips over — that residual is
    // B18's `sorryAx`-in-signature synthesis, not the motive specialization):
    // the return type `Choose b` reduces to `Nat` at `true` and `String` at
    // `false`, so the two arms have genuinely different types. The dependent
    // motive must be `fun x => Choose x`, and each arm checked against
    // `Choose ctorᵢ`. `rfl` pins force the per-arm reductions to compute.
    let env = elaborate_module(
        r#"
def Choose : Bool → Type
  | true => Nat
  | false => String
def choose (b : Bool) : Choose b :=
  match b with
  | true => (3 : Nat)
  | false => "s"
theorem choose_true : choose true = 3 := rfl
theorem choose_false : choose false = "s" := rfl
"#,
    )
    .expect("value-dependent motive over a type family must elaborate and kernel-check");
    assert_axiom_free(&env, &["choose", "choose_true", "choose_false"]);
}

#[test]
fn test_proof_by_match_wrong_arm_rejected() {
    // LOUD NEGATIVE: arm 0 claims the SUCCESSOR disjunct (`∃ m, 0 = m + 1`),
    // which is false — `rfl : 0 = 0 + 1` cannot check. Must fail closed, never
    // certify a false proof.
    let err = expect_rejected(
        r"
theorem bad_pbm (n : Nat) : n = 0 ∨ ∃ m, n = m + 1 :=
  match n with
  | 0 => Or.inr ⟨0, rfl⟩
  | m + 1 => Or.inr ⟨m, rfl⟩
",
        "proof-by-match with a false arm-0 proof",
    );
    assert!(
        !err.to_lowercase().contains("panic"),
        "must be a typed rejection, not a panic: {err}"
    );
}

// =========================================================================
// 2. `dite` hypothesis (term_sugar/p22)
// =========================================================================

#[test]
fn test_dite_p22_hyp_used_both_branches() {
    // The EXACT p22 probe: `if h : n = 0 then Or.inl h else Or.inr h`. `h` is
    // consumed in BOTH branches (as the proof witness), and the result type
    // `n = 0 ∨ ¬ n = 0` flows into both. Exercises the `¬ n = 0` precedence
    // (`¬ (n = 0)`, not `(¬ n) = 0`) AND the dite hypothesis binding together.
    let env = elaborate_module(
        r"
theorem em_nat (n : Nat) : n = 0 ∨ ¬ n = 0 :=
  if h : n = 0 then Or.inl h else Or.inr h
",
    )
    .expect("p22 dite-with-used-hypothesis must elaborate and kernel-check");
    assert_axiom_free(&env, &["em_nat"]);
}

#[test]
fn test_dite_hyp_parenthesized_negation() {
    // The same proof with an explicitly parenthesized negation — isolates the
    // dite hypothesis binding from the `¬`-precedence parser fix (so a parser
    // regression cannot mask a dite-elaboration regression, and vice versa).
    let env = elaborate_module(
        r"
def em_nat_def (n : Nat) : (n = 0) ∨ (¬ (n = 0)) :=
  if h : n = 0 then Or.inl h else Or.inr h
",
    )
    .expect("parenthesized dite-with-used-hypothesis must elaborate and kernel-check");
    assert_axiom_free(&env, &["em_nat_def"]);
}

#[test]
fn test_dite_value_position_computes() {
    // `dite` in VALUE position (result is data, not a proof): the branches
    // compute, `h` is bound (unused here), and the two `rfl` pins force the
    // whole `dite` to REDUCE per decision — `instDecidableEqNat` must compute.
    let env = elaborate_module(
        r"
def classify (n : Nat) : Nat := if h : n = 0 then 100 else 200
theorem classify_zero : classify 0 = 100 := rfl
theorem classify_succ : classify 5 = 200 := rfl
",
    )
    .expect("value-position dite must elaborate, kernel-check, and reduce");
    assert_axiom_free(&env, &["classify", "classify_zero", "classify_succ"]);
}

#[test]
fn test_dite_wrong_branch_rejected() {
    // LOUD NEGATIVE: the then branch is handed `Or.inr h`, but `h : n = 0` and
    // `Or.inr` demands the SECOND disjunct `¬ n = 0`. Must fail closed.
    let err = expect_rejected(
        r"
theorem bad_em (n : Nat) : n = 0 ∨ ¬ n = 0 :=
  if h : n = 0 then Or.inr h else Or.inl h
",
        "dite with swapped branch witnesses",
    );
    assert!(
        !err.to_lowercase().contains("panic"),
        "must be a typed rejection, not a panic: {err}"
    );
}

// =========================================================================
// 3. `¬` precedence (unblocks p22; regression guard)
// =========================================================================

#[test]
fn test_not_binds_looser_than_eq() {
    // `¬ n = 0` must parse as `¬ (n = 0) : Prop` (Lean `prefix:40 "¬"` vs
    // `infixl:50 " = "`), so it is a valid hypothesis type. Pre-fix it parsed as
    // the ill-typed `(¬ n) = 0` and failed with `expected Sort(Zero)`.
    let env = elaborate_module(r"theorem not_prec (n : Nat) (h : ¬ n = 0) : ¬ n = 0 := h")
        .expect("`¬ n = 0` must parse as `¬ (n = 0)`");
    assert_axiom_free(&env, &["not_prec"]);
}

#[test]
fn test_not_binds_tighter_than_and() {
    // `¬` (prec 40) binds TIGHTER than `∧` (prec 35): `¬ a = b ∧ c` is
    // `(¬ (a = b)) ∧ c`. This regression guard proves the precedence widening
    // did not swallow the connectives.
    let env = elaborate_module(
        r"theorem not_and (a b : Nat) (h1 : ¬ a = b) (h2 : a = a) : (¬ a = b) ∧ a = a :=
  And.intro h1 h2",
    )
    .expect("`¬ a = b ∧ c` must parse as `(¬ (a = b)) ∧ c`");
    assert_axiom_free(&env, &["not_and"]);
}

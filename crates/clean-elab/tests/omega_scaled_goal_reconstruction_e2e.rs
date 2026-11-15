// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! End-to-end regression lock: `omega` must reconstruct a goal that needs a
//! DERIVED linear combination of its hypotheses, not only one that is
//! syntactically near a hypothesis — and it must do so **constructively**.
//!
//! ## The defect this guards (measured 2026-09-20, `integrate/2026-09-20`)
//!
//! `omega` decided these goals correctly and then handed the kernel the
//! HYPOTHESIS instead of a proof of the goal:
//!
//! ```text
//! theorem h3 (n : Nat) (h : Nat.lt n 21) : Nat.le n 20 := by omega
//! -- Tactic failed: mathverse: certified arithmetic contradiction has no
//! -- kernel proof (close_goal rejected arithmetic proof: type mismatch:
//! --   expected Nat.le fvar#0 20, got Nat.le (Nat.succ fvar#0) 21)
//! ```
//!
//! The general builder that WOULD have produced the goal term
//! (`arith_linarith_farkas_goal`) was already wired in and already reached. It
//! failed one step from the end, inside the linear-equality synthesizer that
//! proves the Farkas obligation `L = R + k`:
//!
//! * A surface numeral elaborates to `@OfNat.ofNat Nat k (instOfNatNat k)`, an
//!   `App` node; a constant a tactic mints is `Expr::nat_lit(k)`, a `Lit` node.
//! * `arith_linarith_nat_eq::normalize_to_canonical` orders leaves by their
//!   `{:?}` debug string, where `App(` sorts before `FVar(` before `Lit(`.
//! * So the source numeral lands at the HEAD of the canonical sum and the
//!   minted one in the TAIL, breaking the "evaluable leaves are a contiguous
//!   tail" invariant `fold_canonical_literal_tail` folds on. It sees a
//!   symbolic `FVar` inside the run, returns the sum unfolded, and the two
//!   sides' canonical forms differ — so the TRUE equality `(n + 1) + 21 =
//!   (21 + n) + 1` is refused.
//!
//! Every Farkas obligation has that shape (one constant from the hypothesis,
//! one minted by the tactic), so every goal needing a derived combination
//! failed and every goal that only weakens a hypothesis's right-hand constant
//! passed — which is exactly the reported symptom. The fix collapses ground
//! leaves to their value before canonicalization (a definitional rewrite
//! carried by the re-typed `Eq.refl` the pass already uses).
//!
//! ## The second half: it must not go classical
//!
//! The Farkas builder sealed its result under `Classical.byContradiction`,
//! which in this kernel is a Diaconescu-derived theorem
//! (`env/classical_em_proof.rs`) whose closure reaches `Classical.choice`,
//! `propext` and `funext`. `Environment::axiom_deps` FILTERS the foundational
//! axioms out, so that dependency is invisible there — a row would keep
//! reporting an empty axiom closure while silently becoming classical. Over
//! `Nat` the split is decidable and already proved by double induction
//! (`Nat.le_or_lt`), so omega now takes an `Or.rec` on it FIRST and the
//! classical seal is never reached. Every PASS gate below therefore asserts
//! both halves of the closure: `axiom_deps` empty AND `foundational_axiom_deps`
//! free of `Classical.choice`.

use clean_kernel::env::Environment;
use clean_kernel::{Name, TypeChecker};

use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_parser::parse_file;

fn try_elaborate_into(env: &mut Environment, source: &str) -> Result<(), String> {
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        elaborate_decl_and_register(env, &processed).map_err(|e| e.to_string())?;
    }
    Ok(())
}

/// Sorted `to_string` of a name set. Generic because `axiom_deps` and
/// `foundational_axiom_deps` are reached through two different re-exports of
/// `Name` and the compiler treats them as distinct types.
fn names<'a, I, N>(set: I) -> Vec<String>
where
    I: IntoIterator<Item = &'a N>,
    N: std::fmt::Display + 'a,
{
    let mut v: Vec<String> = set.into_iter().map(ToString::to_string).collect();
    v.sort();
    v
}

/// Elaborate `source` (whose LAST declaration is the tactic-proved theorem
/// `name`) and assert the full chain: it elaborates, the kernel re-checks the
/// assembled proof, the proof `infer_type`s def-eq to its stated proposition,
/// its non-foundational axiom closure is EMPTY, and its foundational closure
/// does not reach `Classical.choice`.
fn assert_omega_theorem_constructive(name: &str, source: &str) {
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

    let tc = TypeChecker::new(&env);
    let inferred = tc
        .infer_type(proof)
        .unwrap_or_else(|e| panic!("`{name}` proof must infer a type: {e}"));
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "`{name}` proof type must be def-eq to its stated proposition:\n  got {inferred:?}\n  exp {:?}",
        info.type_
    );

    let deps = env
        .axiom_deps(&Name::from_string(name))
        .unwrap_or_else(|| panic!("`{name}` must have an axiom_deps closure"));
    assert!(
        deps.is_empty(),
        "`{name}` must carry an EMPTY non-foundational axiom closure, found {:?}",
        names(&deps)
    );

    // The half `axiom_deps` cannot see. `Classical.byContradiction` is a
    // Theorem here, so it never appears in a closure by name — its cost shows
    // up as `Classical.choice` (via Diaconescu) and nowhere else.
    let foundational = env
        .foundational_axiom_deps(&Name::from_string(name))
        .unwrap_or_else(|| panic!("`{name}` must have a foundational closure"));
    let classical: Vec<String> = names(&foundational)
        .into_iter()
        .filter(|n| n.starts_with("Classical."))
        .collect();
    assert!(
        classical.is_empty(),
        "`{name}` must be reconstructed CONSTRUCTIVELY, but its closure reaches {classical:?} \
         (the `Classical.byContradiction` Farkas seal); the `Nat.le_or_lt` split must run first"
    );
}

/// Assert that `source` is REFUSED: elaboration fails, the failure is an honest
/// tactic verdict (never an internal kernel error), and no proof of `name` is
/// registered.
fn assert_refused_honestly(name: &str, source: &str) {
    let mut env = Environment::with_prelude();
    let err = match try_elaborate_into(&mut env, source) {
        Err(e) => e,
        Ok(()) => panic!("`{name}` is FALSE and must be refused, but elaboration succeeded"),
    };
    for internal in ["Unbound variable", "type check failed", "UnknownFVar"] {
        assert!(
            !err.contains(internal),
            "`{name}` must be refused with an honest tactic error, not an internal one: {err}"
        );
    }
    assert!(
        env.get_const(&Name::from_string(name))
            .and_then(|info| info.value.clone())
            .is_none(),
        "`{name}` must not have a registered proof after a refusal"
    );
}

// ---------------------------------------------------------------------------
// INSTRUMENT CALIBRATION
//
// Every PASS gate below asserts that the closure does NOT reach
// `Classical.*`. That assertion is worthless unless `foundational_axiom_deps`
// actually REPORTS a classical dependency when one is there — and it is easy
// to believe it does not, because `axiom_deps` (the usual instrument) filters
// exactly these names out. This row pins that the instrument has teeth: a term
// that genuinely uses `Classical.em` must show `Classical.choice`, and must
// show it ONLY in the foundational half.
// ---------------------------------------------------------------------------

#[test]
fn foundational_closure_actually_reports_classical_choice() {
    let mut env = Environment::with_prelude();
    try_elaborate_into(
        &mut env,
        "theorem classical_control (p : Prop) : Or p (Not p) := Classical.em p\n",
    )
    .expect("the classical control must elaborate");

    let name = Name::from_string("classical_control");
    let deps = env.axiom_deps(&name).expect("axiom_deps");
    let foundational = env
        .foundational_axiom_deps(&name)
        .expect("foundational_axiom_deps");

    assert!(
        foundational
            .iter()
            .any(|n| n.to_string() == "Classical.choice"),
        "`foundational_axiom_deps` must report `Classical.choice` for a term built on \
         `Classical.em`, else every `no Classical.*` assertion in this file is vacuous; got {:?}",
        names(&foundational)
    );
    assert!(
        deps.is_empty(),
        "and `axiom_deps` must stay EMPTY for that same term — this is precisely why it cannot \
         be the instrument for this question; got {:?}",
        names(&deps)
    );
}

// ---------------------------------------------------------------------------
// CONTROLS — these three passed BEFORE the fix.
//
// They take the shape the old reconstruction could already reach: the goal
// keeps the hypothesis's left-hand side and relation and only weakens the
// right-hand constant. A "fix" that repairs the derived-combination family by
// breaking this one must not go unnoticed.
// ---------------------------------------------------------------------------

#[test]
fn control_weakened_right_constant() {
    assert_omega_theorem_constructive(
        "a",
        "theorem a (n : Nat) (h : Nat.lt n 21) : Nat.lt n 22 := by omega\n",
    );
}

#[test]
fn control_offset_left_and_right() {
    assert_omega_theorem_constructive(
        "c",
        "theorem c (n : Nat) (h : Nat.lt n 21) : Nat.lt (n + 1) 22 := by omega\n",
    );
}

#[test]
fn control_symbolic_right_core() {
    assert_omega_theorem_constructive(
        "h2",
        "theorem h2 (n m : Nat) (h : Nat.lt n m) : Nat.lt n (m + 1) := by omega\n",
    );
}

// ---------------------------------------------------------------------------
// The defect: goals needing a DERIVED linear combination.
// ---------------------------------------------------------------------------

/// Scale the atom AND the offset — the a3d `depth < 21` ⟺ `3*(depth+1) < 64`
/// step, in the small.
#[test]
fn scaled_atom_with_offset() {
    assert_omega_theorem_constructive(
        "b",
        "theorem b (n : Nat) (h : Nat.lt n 21) : Nat.lt (3 * (n + 1)) 64 := by omega\n",
    );
}

/// Scale the atom by 3.
#[test]
fn scaled_atom_times_three() {
    assert_omega_theorem_constructive(
        "d",
        "theorem d (n : Nat) (h : Nat.lt n 21) : Nat.lt (3 * n) 63 := by omega\n",
    );
}

/// Scale the atom by 2.
#[test]
fn scaled_atom_times_two() {
    assert_omega_theorem_constructive(
        "e",
        "theorem e (n : Nat) (h : Nat.lt n 21) : Nat.lt (2 * n) 42 := by omega\n",
    );
}

/// `n + n` — the SAME derived combination with no multiplication anywhere, so a
/// diagnosis of "omega cannot multiply" is refuted by this row alone.
#[test]
fn scaled_atom_written_as_repeated_addition() {
    assert_omega_theorem_constructive(
        "f",
        "theorem f (n : Nat) (h : Nat.lt n 21) : Nat.lt (n + n) 42 := by omega\n",
    );
}

/// Divide the coefficient OUT — the multiplier lives on the refuted goal, not
/// on the hypothesis, so no assignment that fixes the goal at 1 can express it.
#[test]
fn divides_the_coefficient_out() {
    assert_omega_theorem_constructive(
        "h1",
        "theorem h1 (n : Nat) (h : Nat.lt (2 * n) 42) : Nat.lt n 21 := by omega\n",
    );
}

/// The cheapest reproduction: one relation step, no arithmetic. `n < 21` and
/// `n ≤ 20` are the same fact.
#[test]
fn relation_step_lt_to_le() {
    assert_omega_theorem_constructive(
        "h3",
        "theorem h3 (n : Nat) (h : Nat.lt n 21) : Nat.le n 20 := by omega\n",
    );
}

/// Literal on the RIGHT of the multiplication (`n * 3`, not `3 * n`).
#[test]
fn scaled_atom_literal_on_the_right() {
    assert_omega_theorem_constructive(
        "h4",
        "theorem h4 (n : Nat) (h : Nat.lt n 21) : Nat.lt (n * 3) 63 := by omega\n",
    );
}

// ---------------------------------------------------------------------------
// NEGATIVE GATES — fail closed. Each is the true theorem above with the
// constant moved one step past what the hypothesis supports.
// ---------------------------------------------------------------------------

/// FALSE at `n = 20`: `3 * 20 = 60`, and `60 < 60` does not hold.
#[test]
fn rejects_false_scaled_bound() {
    assert_refused_honestly(
        "d_false",
        "theorem d_false (n : Nat) (h : Nat.lt n 21) : Nat.lt (3 * n) 60 := by omega\n",
    );
}

/// FALSE at `n = 20`.
#[test]
fn rejects_false_relation_step() {
    assert_refused_honestly(
        "h3_false",
        "theorem h3_false (n : Nat) (h : Nat.lt n 21) : Nat.le n 19 := by omega\n",
    );
}

/// FALSE at `n = 20`: `2 * 20 = 40 < 42`, but `20 < 20` does not hold.
#[test]
fn rejects_false_division() {
    assert_refused_honestly(
        "h1_false",
        "theorem h1_false (n : Nat) (h : Nat.lt (2 * n) 42) : Nat.lt n 20 := by omega\n",
    );
}

// ---------------------------------------------------------------------------
// The a3d shape: the SAME derived combination over an OPAQUE Nat atom.
//
// `UInt32.toNat d` has an application head, and the mathverse linear parser
// names atoms by `FVarId` — so these never reached the certified block at all
// and omega reported "could not extract linear constraints". The Farkas
// builder's linear forms are keyed by `Expr`, so it decides and reconstructs
// them without the certificate.
// ---------------------------------------------------------------------------

#[test]
fn opaque_nat_atom_scaled_forward() {
    assert_omega_theorem_constructive(
        "fwd",
        "theorem fwd (d : UInt32) (h : Nat.lt (UInt32.toNat d) 21) : \
         Nat.lt (3 * (UInt32.toNat d + 1)) 64 := by omega\n",
    );
}

#[test]
fn opaque_nat_atom_divides_backward() {
    assert_omega_theorem_constructive(
        "bwd",
        "theorem bwd (d : UInt32) (h : Nat.lt (3 * (UInt32.toNat d + 1)) 64) : \
         Nat.lt (UInt32.toNat d) 21 := by omega\n",
    );
}

/// FALSE at `UInt32.toNat d = 20`: `3 * 21 = 63`, and `63 < 63` does not hold.
/// Pins that the opaque-atom lane fails closed rather than atomizing its way
/// into proving anything.
#[test]
fn rejects_false_opaque_nat_atom_bound() {
    assert_refused_honestly(
        "fwd_false",
        "theorem fwd_false (d : UInt32) (h : Nat.lt (UInt32.toNat d) 21) : \
         Nat.lt (3 * (UInt32.toNat d + 1)) 63 := by omega\n",
    );
}

// ---------------------------------------------------------------------------
// The acceptance test: a3d's open item, end to end.
// ---------------------------------------------------------------------------

/// The guard `depth < 21` and the arithmetic `3 * (depth + 1) < 64` are the
/// same decision — the theorem that makes 21 the right constant. Both `omega`s
/// are the derived-combination family (forward is `b`; backward divides the 3
/// out), over the opaque `UInt32.toNat` atom. `BitVec.toNat`'s width is
/// implicit (`{w : Nat} → BitVec w → Nat`) and `Decidable.decide`'s instance
/// is inst-implicit (`(p : Prop) → [Decidable p] → Bool`), so the source names
/// them positionally only under `@`; Lean v4.30.0-rc2 and v4.36.0-rc2 refuse
/// both spellings without it ("function expected").
#[test]
fn depth_fits_eq_span_fits_closes_end_to_end() {
    assert_omega_theorem_constructive(
        "depth_fits_eq_span_fits",
        concat!(
            "theorem u32_toNat_def (d : UInt32) :\n",
            "    Eq (UInt32.toNat d) (@BitVec.toNat 32 (UInt32.toBitVec d)) := rfl\n",
            "theorem u32_ofNat21_toNat :\n",
            "    Eq (@BitVec.toNat 32 (UInt32.toBitVec (UInt32.ofNat 21))) 21 := rfl\n",
            "\n",
            "def depth_fits_isl (d : UInt32) : Bool :=\n",
            "  @Decidable.decide (LT.lt d (UInt32.ofNat 21))\n",
            "                    (instDecidableUInt32Lt d (UInt32.ofNat 21))\n",
            "def span_fits_isl (d : UInt32) : Bool :=\n",
            "  @Decidable.decide (Nat.lt (3 * (UInt32.toNat d + 1)) 64)\n",
            "                    (Nat.decLt (3 * (UInt32.toNat d + 1)) 64)\n",
            "\n",
            "theorem depth_fits_eq_span_fits (d : UInt32) :\n",
            "    Eq (depth_fits_isl d) (span_fits_isl d) := by\n",
            "  unfold depth_fits_isl\n",
            "  unfold span_fits_isl\n",
            "  rw [decide_eq_decide]\n",
            "  rw [u32_toNat_def]\n",
            "  rw [u32_ofNat21_toNat]\n",
            "  exact Iff.intro (fun h => by omega) (fun h => by omega)\n",
        ),
    );
}

/// Negative control for the `@BitVec.toNat 32` spelling above: the width is
/// implicit, so `BitVec.toNat 32 x` applies a `Nat` to `x`. Lean v4.30.0-rc2
/// and v4.36.0-rc2 refuse it ("function expected"), so Clean must too.
#[test]
fn bitvec_to_nat_positional_width_without_at_is_refused() {
    let mut env = Environment::with_prelude();
    let err = try_elaborate_into(
        &mut env,
        "theorem u32_toNat_def_bad (d : UInt32) :\n    \
         Eq (UInt32.toNat d) (BitVec.toNat 32 (UInt32.toBitVec d)) := rfl\n",
    )
    .expect_err("an explicit width must not fill `BitVec.toNat`'s implicit `w`");
    assert!(
        env.get_const(&Name::from_string("u32_toNat_def_bad"))
            .is_none(),
        "a refused theorem must not be registered: {err}"
    );
}

/// Negative control for the `@Decidable.decide p inst` spelling above: the
/// instance binder is inst-implicit, so `Decidable.decide p inst` applies a
/// `Bool` to `inst`. Lean v4.30.0-rc2 and v4.36.0-rc2 refuse it ("function
/// expected at decide (d < UInt32.ofNat 21)"), so Clean must too.
#[test]
fn decide_positional_instance_without_at_is_refused() {
    let mut env = Environment::with_prelude();
    let err = try_elaborate_into(
        &mut env,
        "def depth_fits_bad (d : UInt32) : Bool :=\n  \
         Decidable.decide (LT.lt d (UInt32.ofNat 21))\n    \
         (instDecidableUInt32Lt d (UInt32.ofNat 21))\n",
    )
    .expect_err("an explicit instance must not fill `Decidable.decide`'s `[Decidable p]`");
    assert!(
        err.contains("Too many arguments") && err.contains("Bool"),
        "the refusal must be Lean's function-expected one, got: {err}"
    );
}

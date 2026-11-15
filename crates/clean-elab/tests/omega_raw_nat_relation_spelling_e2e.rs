// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! End-to-end regression lock: `omega` must not depend on which of the two
//! definitionally-equal SPELLINGS a `Nat` comparison is written in.
//!
//! ## The defect this guards (measured 2026-09-20, trustc `379912412`)
//!
//! `a ≤ b` elaborates to the typeclass spine `@LE.le Nat instLENat a b`; a
//! hand-written Lean island may instead name the kernel constant directly and
//! write `Nat.le a b`. `instLENat` / `instLTNat` are reducible wrappers, so the
//! two are definitionally equal and the kernel accepts a proof of either
//! against the other. `omega` did not: its negated-relation normalization
//! (`omega_tactic::is_negated_relation` → `push_neg_at`) matched only the
//! typeclass spine, so a NEGATED raw-spelled hypothesis was never flipped.
//!
//! ```text
//! theorem t (x y : Nat) (h : ¬ (x < y))          : y ≤ x       := by omega  -- PASSED
//! theorem t (x y : Nat) (h : Not (Nat.lt x y))   : Nat.le y x  := by omega  -- FAILED
//! ```
//!
//! with `mathverse: certified arithmetic contradiction has no kernel proof
//! (close_goal rejected arithmetic proof: type mismatch: expected
//! Nat.le fvar#1 fvar#0, got Nat.lt fvar#0 fvar#1 -> False)` — the built term
//! was the hypothesis itself, never converted to the goal.
//!
//! The same one defect is what blocked the a3d two-language conversion's
//! signed-order-key bound theorems (`a3d-kernel/CONVERSION.md` §4.3/§4.4).
//! There the decision is `if Nat.lt (key64 a) (key64 b) then a else b`, so
//! `split` introduces `h : Not (Nat.lt …)` in the raw spelling and
//! `unfold; split <;> omega` failed — while the byte-identical model written
//! `if key64 a < key64 b then …` goes through. It is NOT, as that file
//! records, that omega "cannot see through" the `Nat.xor`-based order key:
//! omega atomizes the key fine (see `key_atom_is_not_the_blocker`).
//!
//! Every PASS gate drives the same pipeline as `clean check`: the theorem must
//! register (the kernel re-checks the assembled proof), the proof must
//! `infer_type` def-eq to the stated proposition, and the axiom closure must be
//! free of `sorryAx`. The negative gates pin that a FALSE twin is REFUSED with
//! an honest tactic verdict and nothing registered.

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

/// Elaborate `source` (which must define `name` last as a tactic-proved
/// theorem) and assert it elaborates + kernel-checks, that the proof
/// `infer_type`s def-eq to its proposition, and that no `sorryAx` is in its
/// axiom closure.
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
        !deps.iter().any(|d| d.to_string().contains("sorry")),
        "`{name}` axiom closure must not contain sorry, found {deps:?}"
    );
}

/// Assert that `source` is REFUSED: elaboration fails, the failure is an
/// honest tactic verdict (never an internal kernel type-check error), and no
/// proof of `name` is registered.
fn assert_refused_honestly(name: &str, source: &str) -> String {
    let mut env = Environment::with_prelude();
    let err = match try_elaborate_into(&mut env, source) {
        Err(e) => e,
        Ok(()) => {
            let registered = env
                .get_const(&Name::from_string(name))
                .and_then(|info| info.value.clone());
            panic!(
                "`{name}` must be refused, but elaboration succeeded (proof registered: {})",
                registered.is_some()
            );
        }
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
    err
}

// ---------------------------------------------------------------------------
// The bare defect: a negated RAW-spelled hypothesis
// ---------------------------------------------------------------------------

/// The exact failing statement from `a3d-kernel/kernel_model.lean`, which that
/// model had to prove by hand from `Nat.le_or_lt` instead.
#[test]
fn raw_not_lt_hypothesis_closes_raw_le_goal() {
    assert_tactic_theorem(
        "nat_le_of_not_lt",
        "theorem nat_le_of_not_lt (x : Nat) (y : Nat) (h : Not (Nat.lt x y)) : Nat.le y x := by\n  omega\n",
    );
}

/// The `≤` half of the same gap: `¬(x ≤ y) → y < x`, raw on both sides.
#[test]
fn raw_not_le_hypothesis_closes_raw_lt_goal() {
    assert_tactic_theorem(
        "nat_lt_of_not_le",
        "theorem nat_lt_of_not_le (x : Nat) (y : Nat) (h : Not (Nat.le x y)) : Nat.lt y x := by\n  omega\n",
    );
}

/// CONTROL — the typeclass spelling of the same proposition. This one already
/// passed before the fix; it is here so a regression that "fixes" the raw
/// spelling by breaking the sugar one cannot go unnoticed.
#[test]
fn typeclass_not_lt_hypothesis_still_closes_le_goal() {
    assert_tactic_theorem(
        "nat_le_of_not_lt_tc",
        "theorem nat_le_of_not_lt_tc (x y : Nat) (h : ¬ (x < y)) : y ≤ x := by\n  omega\n",
    );
}

/// MIXED spellings across hypothesis and goal must also close: the hypothesis
/// is raw, the goal is sugar. (The reverse — sugar hypothesis, raw goal —
/// already worked, and is the control above's cousin.)
#[test]
fn raw_hypothesis_closes_typeclass_goal() {
    assert_tactic_theorem(
        "nat_le_of_not_lt_mixed",
        "theorem nat_le_of_not_lt_mixed (x y : Nat) (h : Not (Nat.lt x y)) : y ≤ x := by\n  omega\n",
    );
}

// ---------------------------------------------------------------------------
// The a3d shape: an opaque order key, a raw-spelled `if`, `unfold; split`
// ---------------------------------------------------------------------------

/// `key` is `Nat.xor v 8`: an atom omega cannot compute with, standing for
/// a3d's `key64 v = Nat.xor (BitVec.toNat v) 2^63`. `min2` decides on it in the
/// RAW spelling, exactly as a3d's model does.
const MIN2_KEY_RAW: &str = concat!(
    "def key (v : Nat) : Nat := Nat.xor v 8\n",
    "def min2 (a : Nat) (b : Nat) : Nat := if Nat.lt (key a) (key b) then a else b\n",
);

/// The same pair written with the `<` sugar. It passed BEFORE the fix — the
/// spelling was the whole difference — and must keep passing after it.
const MIN2_KEY_TC: &str = concat!(
    "def key (v : Nat) : Nat := Nat.xor v 8\n",
    "def min2 (a : Nat) (b : Nat) : Nat := if key a < key b then a else b\n",
);

/// `min2 a b ≤ a` at the key. This is a3d's `min2_le_a_isl`, which had to be
/// written as an explicit `Decidable.casesOn` term proof.
#[test]
fn raw_key_decision_min2_le_left() {
    assert_tactic_theorem(
        "min2_key_le_left",
        &format!(
            "{MIN2_KEY_RAW}theorem min2_key_le_left (a b : Nat) : Nat.le (key (min2 a b)) (key a) := by\n  unfold min2\n  split <;> omega\n"
        ),
    );
}

/// The other true bound, `min2 a b ≤ b` — a3d's `min2_le_b_isl`.
#[test]
fn raw_key_decision_min2_le_right() {
    assert_tactic_theorem(
        "min2_key_le_right",
        &format!(
            "{MIN2_KEY_RAW}theorem min2_key_le_right (a b : Nat) : Nat.le (key (min2 a b)) (key b) := by\n  unfold min2\n  split <;> omega\n"
        ),
    );
}

/// CONTROL — the sugar spelling of the identical fixture, which passed before
/// the fix. Pins that the order key itself was never the blocker.
#[test]
fn key_atom_is_not_the_blocker() {
    assert_tactic_theorem(
        "min2_key_le_left_tc",
        &format!(
            "{MIN2_KEY_TC}theorem min2_key_le_left_tc (a b : Nat) : Nat.le (key (min2 a b)) (key a) := by\n  unfold min2\n  split <;> omega\n"
        ),
    );
}

// ---------------------------------------------------------------------------
// FAIL gates — the fix must not prove anything false
// ---------------------------------------------------------------------------

/// CLOSE NEGATIVE TWIN of `raw_not_lt_hypothesis_closes_raw_le_goal`: one
/// argument swapped in the CONCLUSION, so the statement is `¬(x < y) → x ≤ y`,
/// which is false at `x = 1, y = 0`. Must be refused honestly.
#[test]
fn false_twin_of_not_lt_is_refused_honestly() {
    let err = assert_refused_honestly(
        "nat_le_of_not_lt_false",
        "theorem nat_le_of_not_lt_false (x : Nat) (y : Nat) (h : Not (Nat.lt x y)) : Nat.le x y := by\n  omega\n",
    );
    assert!(
        err.contains("omega") || err.contains("mathverse"),
        "the false twin must be refused by the arithmetic tactic, got: {err}"
    );
}

/// CLOSE NEGATIVE TWIN of the key fixture: the bound pointed the other way,
/// `key a ≤ key (min2 a b)`, which fails on the branch where `min2` returns
/// `b`. Must be refused honestly and register nothing.
#[test]
fn false_key_bound_is_refused_honestly() {
    let err = assert_refused_honestly(
        "min2_key_ge_left_false",
        &format!(
            "{MIN2_KEY_RAW}theorem min2_key_ge_left_false (a b : Nat) : Nat.le (key a) (key (min2 a b)) := by\n  unfold min2\n  split <;> omega\n"
        ),
    );
    assert!(
        err.contains("omega") || err.contains("mathverse"),
        "the false key bound must be refused by the arithmetic tactic, got: {err}"
    );
}

/// MUTATION CONTROL: one token changed in the MODEL — `min2`'s arms swapped,
/// so the definition is the maximum — and the true-for-`min2` bound
/// `min2 a b ≤ a` becomes false. The damage must be attributable: this one
/// theorem is refused while `raw_key_decision_min2_le_left` (identical but for
/// the swapped arms) passes.
#[test]
fn swapped_arms_mutation_is_refused_honestly() {
    let mutated = concat!(
        "def key (v : Nat) : Nat := Nat.xor v 8\n",
        "def min2 (a : Nat) (b : Nat) : Nat := if Nat.lt (key a) (key b) then b else a\n",
    );
    let err = assert_refused_honestly(
        "min2_key_le_left",
        &format!(
            "{mutated}theorem min2_key_le_left (a b : Nat) : Nat.le (key (min2 a b)) (key a) := by\n  unfold min2\n  split <;> omega\n"
        ),
    );
    assert!(
        err.contains("omega") || err.contains("mathverse"),
        "the mutated model must be refused by the arithmetic tactic, got: {err}"
    );
}

/// SCOPE GUARD: the widening is to the raw `Nat.le` / `Nat.lt` spellings of a
/// RELATION, not to negations in general. `¬(P ∧ Q)` is not a negated linear
/// relation; the normalization must not manufacture one, and the goal is then
/// genuinely out of omega's reach. The gate is that this is refused honestly
/// rather than "proved" by an over-eager rewrite.
///
/// (The unit-level version of this guard — that `Nat.ble` / `Nat.blt` /
/// `Nat.beq` / `Int.le` / `Int.lt` are not admitted as Nat order relations —
/// is in `tactic::tests::nat_rel_spelling_matchers`.)
#[test]
fn negated_conjunction_is_not_treated_as_a_relation() {
    let err = assert_refused_honestly(
        "and_not_a_relation",
        "theorem and_not_a_relation (x : Nat) (y : Nat) (h : Not (And (Nat.le x y) (Nat.le y x))) : Nat.lt y x := by\n  omega\n",
    );
    assert!(
        err.contains("omega") || err.contains("mathverse"),
        "the negated conjunction must reach omega and be refused by it, got: {err}"
    );
}

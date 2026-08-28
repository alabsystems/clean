// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **R3 PROBES — what actually stopped `gcd` from elaborating, measured
//! before the change, and re-pinned after it.**
//!
//! The Trust superproject's `crates/trust-clean-origin/tests/
//! recursion_boundary_probes.rs` records `def gcd (a b : Nat) : Nat :=
//! if b == 0 then a else gcd b (a % b)` as REJECTED at every spelling, and
//! names TWO blockers: (1) multi-parameter well-founded recursion, (2) the
//! `a % b < b` decrease. This file measured both HERE, in the elaborator's own
//! test lane, BEFORE any code moved — so the extension was designed against
//! measurements rather than against the summary.
//!
//! # What the pre-change run said (2026-08-22, at pin `f391bd466`)
//!
//! | # | question | verdict THEN | verdict NOW |
//! |---|---|---|---|
//! | p0 | does `Nat.mod_lt` exist? | **YES** — `with_prelude` carries it as an axiom-free `Theorem`, `∀ (a n : Nat), Nat.lt 0 n → Nat.lt (Nat.mod a n) n`. **Blocker 2 needed no new kernel or prelude work at all** | unchanged |
//! | p1 | can the cascade discharge a `%` decrease at ONE parameter? | **YES, already** — `modDown (7 % b)` under `h : 0 < b` elaborated and kernel-verified before the change. So blocker 2 was not a blocker; it was a consequence of blocker 1 | unchanged (now via the named `Nat.mod_lt` tier rather than a tactic) |
//! | p2 | is the parameter count a HARD gate, or does it fail later? | **HARD GATE** — a two-parameter definition whose call passes no bare identifier DID reach the well-founded lowering, and was refused verbatim: *"only single-parameter definitions are supported by the well-founded lowering so far"* | ADMITTED |
//! | p3 | what stops `gcd` itself? | **ROUTING, one layer earlier** — `gcd` never reached that gate. `find_decreasing_arg` reads `gcd b (a % b)`'s first argument (`b`, a bare identifier spelled differently from parameter `a`) as "parameter 0 decreases", so `setup_recursion` sent it down the STRUCTURAL path and the self-call died `RecursionOutsideFragment`. The explicit `termination_by b` was never consulted | ADMITTED (dite spelling) |
//!
//! **So the measured blocker list was wrong in both directions**: blocker 2
//! did not exist, and blocker 1 was two blockers stacked — a routing decision
//! that hid an arity gate. Fixing only the arity gate would have changed
//! nothing observable about `gcd`.
//!
//! # R4 amendment (2026-08-22)
//!
//! Two rows below were RE-PINNED when R4 landed the Bool-test spelling, because
//! a measurement file that keeps asserting a superseded verdict is worse than
//! one that moves: p0's control (`Nat.pos_of_ne_zero` ABSENT → PRESENT, proved)
//! and p3's Bool row (REFUSED → ADMITTED with `termination_by b`). Each carries
//! its R3 verdict inline. R4's own measurements — including that R3's named
//! prerequisite was mis-specified, since `b == 0` elaborates through
//! `BEq.beq`/`decide` and never through `Nat.beq` — are in
//! `r4_bool_test_bridge_probes.rs`, and its e2e gate is
//! `r4_gcd_bool_spelling_e2e.rs`.
//!
//! Every probe asserts its verdict. No probe passes vacuously.

use clean_elab::{
    elaborate_decl, elaborate_decl_and_register, preprocess_decl_with_context, ElabError,
    ElabResult, FileContext,
};
use clean_kernel::name::Name;
use clean_kernel::{ConstantKind, Environment};
use clean_parser::parse_file;

fn elab_one(env: &Environment, source: &str) -> Result<ElabResult, ElabError> {
    let decls = parse_file(source).expect("source should parse");
    assert_eq!(decls.len(), 1, "fixture must be exactly one declaration");
    let mut file_ctx = FileContext::new();
    let processed = preprocess_decl_with_context(&decls[0], &mut file_ctx);
    elaborate_decl(env, &processed)
}

fn register_one(env: &mut Environment, source: &str) -> Result<ElabResult, ElabError> {
    let decls = parse_file(source).expect("source should parse");
    assert_eq!(decls.len(), 1, "fixture must be exactly one declaration");
    let mut file_ctx = FileContext::new();
    let processed = preprocess_decl_with_context(&decls[0], &mut file_ctx);
    elaborate_decl_and_register(env, &processed)
}

// ═════════ (p0) BLOCKER 2's prerequisite: does `Nat.mod_lt` exist? ═════════

/// The decrease `gcd` needs is `a % b < b` given `0 < b` — i.e. exactly
/// `Nat.mod_lt`. MEASURED: it IS in the production prelude, as an axiom-free
/// `Theorem` (`clean-kernel/src/env/data_types_nat_div_mod_lemmas.rs`), with
/// BOTH value arguments explicit and the positivity side condition last.
#[test]
fn probe_p0_nat_mod_lt_is_present_and_axiom_free() {
    let env = Environment::with_prelude();
    let c = env
        .get_const(&Name::from_string("Nat.mod_lt"))
        .expect("MEASURED: `Nat.mod_lt` IS in with_prelude — blocker 2 needs no new prelude axiom");
    assert_eq!(
        c.kind,
        ConstantKind::Theorem,
        "`Nat.mod_lt` must be a proof-carrying Theorem, not an axiom"
    );
    assert!(c.value.is_some(), "and it must carry its proof term");
    let closure = env
        .axiom_deps(&Name::from_string("Nat.mod_lt"))
        .expect("Nat.mod_lt must have an axiom closure");
    let foundational = ["propext", "Quot.sound", "Classical.choice"];
    let offending: Vec<String> = closure
        .iter()
        .map(ToString::to_string)
        .filter(|ax| !foundational.contains(&ax.as_str()))
        .collect();
    assert!(
        offending.is_empty(),
        "`Nat.mod_lt` must be foundational-only, got {offending:?}"
    );
    eprintln!("PROBE-ROW | p0 Nat.mod_lt | PRESENT, Theorem, foundational-only closure");
    eprintln!("          | type: {:?}", c.type_);

    // CONTROL, RE-PINNED BY R4. At R3 (pin `f391bd466`) both of the constants
    // the Bool-test spelling was thought to need were ABSENT, which is how R3
    // established that a Bool-test `gcd` was a DIFFERENT problem from the
    // `dite` spelling. R4 then added `Nat.pos_of_ne_zero` (proved, axiom-free)
    // and closed that problem — so the row moves rather than lying.
    //
    // `Nat.ne_of_beq_eq_false` is STILL absent and was never needed: R4's
    // probes measured that `b == 0` elaborates through `BEq.beq` /
    // `instBEqOfDecidableEq` to `decide (b = 0)`, NOT through `Nat.beq`, so a
    // `Nat.beq`-shaped bridge would not have matched the condition at all.
    // See `r4_bool_test_bridge_probes::probe_q1_*` / `probe_q2b_*`.
    assert!(
        env.get_const(&Name::from_string("Nat.pos_of_ne_zero"))
            .is_some(),
        "R4 added the positivity bridge; at R3 this was ABSENT"
    );
    assert!(
        env.get_const(&Name::from_string("Nat.ne_of_beq_eq_false"))
            .is_none(),
        "measured: `Nat.ne_of_beq_eq_false` is absent, and R4 did not need it"
    );
}

// ═══════ (p1) the single-parameter lane: can the cascade do `_ % b < b`? ═══════

/// Isolates BLOCKER 2 from BLOCKER 1 by asking the decrease question at ONE
/// parameter, where the parameter-count gate cannot fire. `modDown` recurses on
/// `7 % b` under `h : 0 < b`; the obligation is `Nat.lt (7 % b) b`, which is
/// `Nat.mod_lt 7 b h` and nothing else.
#[test]
fn probe_p1_single_param_mod_decrease() {
    const MOD_DOWN: &str = "def modDown (b : Nat) : Nat := \
         if h : 0 < b then modDown (7 % b) else 0\n\
         termination_by b";
    let mut env = Environment::with_prelude();
    let result = register_one(&mut env, MOD_DOWN);
    eprintln!(
        "PROBE-ROW | p1 single-param `7 % b < b` | {}",
        match &result {
            Ok(_) => "ADMITTED".to_owned(),
            Err(e) => format!("REFUSED: {e}"),
        }
    );
    result.expect(
        "the `%` decrease must discharge at ONE parameter — this is blocker 2 \
         in isolation, and `Nat.mod_lt` is in the prelude (p0)",
    );
}

// ═══════ (p2) the parameter-count gate, reached in isolation ═══════

/// A two-parameter WF definition whose recursive call passes NO bare
/// identifier — so the structural auto-detector finds no decreasing argument
/// and routing DOES reach the well-founded lowering. This is the probe that
/// isolated the ARITY gate from the ROUTING decision: before the change it was
/// refused with *"only single-parameter definitions are supported by the
/// well-founded lowering so far"*, which is the gate `gcd` was assumed to be
/// dying on and in fact never reached.
#[test]
fn probe_p2_two_param_reaches_wf_and_the_arity_gate_is_gone() {
    const TWO_P: &str = "def twoP (a b : Nat) : Nat := \
         if h : 0 < b then twoP (a + 0) (b - 1) else a\n\
         termination_by b";
    let env = Environment::with_prelude();
    let result = elab_one(&env, TWO_P);
    match &result {
        Ok(_) => eprintln!("PROBE-ROW | p2 two-param, no-ident args | ADMITTED"),
        Err(e) => eprintln!("PROBE-ROW | p2 two-param, no-ident args | REFUSED: {e}"),
    }
    // BEFORE: `Unsupported { feature: "well-founded recursion for 'twoP' … only
    // single-parameter definitions are supported by the well-founded lowering
    // so far …" }`.
    result.expect(
        "a two-parameter WF definition with a single-parameter measure must \
         elaborate: the measure and the decrease stay one-parameter; only the \
         SIGNATURE is wider",
    );
}

// ═══════ (p3) gcd itself, at all three spellings ═══════

/// `gcd` in the `dite` spelling — the spelling whose decrease is discharged by
/// a hypothesis in scope. This is the R3 target.
const GCD_DITE: &str = "def gcd (a b : Nat) : Nat := \
     if h : 0 < b then gcd b (a % b) else a\n\
     termination_by b";

/// The §1 demo's verbatim Bool-test spelling. At R3 its `else` branch bound NO
/// hypothesis at all (a non-dependent `ite`), so nothing in scope bounded `b`;
/// R4 normalizes the `ite` to a `dite` inside the well-founded lowering, which
/// is what puts `¬((b == 0) = true)` in scope at the call site.
const GCD_BOOL: &str = "def gcdBool (a b : Nat) : Nat := \
     if b == 0 then a else gcdBool b (a % b)\n\
     termination_by b";

/// The same Bool-test shape with no `termination_by` at all.
const GCD_BARE: &str = "def gcdBare (a b : Nat) : Nat := \
     if b == 0 then a else gcdBare b (a % b)";

#[test]
fn probe_p3_gcd_dite_spelling() {
    let mut env = Environment::with_prelude();
    let result = register_one(&mut env, GCD_DITE);
    match &result {
        Ok(_) => eprintln!("PROBE-ROW | p3 gcd (dite spelling)    | ADMITTED"),
        Err(e) => eprintln!("PROBE-ROW | p3 gcd (dite spelling)    | REFUSED: {e}"),
    }
    // BEFORE: `RecursionOutsideFragment { name: "gcd", decl: "gcd", params: 2 }`
    // — raised at unknown-identifier resolution, i.e. one layer EARLIER than
    // the well-founded lowering, because routing never sent it there.
    result.expect("R3's target: `gcd` in the hypothesis-bearing spelling must elaborate");
}

#[test]
fn probe_p3_gcd_bool_spelling_measured() {
    let env = Environment::with_prelude();
    let by_measure = elab_one(&env, GCD_BOOL);
    let bare = elab_one(&env, GCD_BARE);
    eprintln!(
        "PROBE-ROW | p3 gcd (b == 0, termination_by b) | {}",
        match &by_measure {
            Ok(_) => "ADMITTED".to_owned(),
            Err(e) => format!("REFUSED: {e}"),
        }
    );
    eprintln!(
        "PROBE-ROW | p3 gcd (b == 0, no termination_by) | {}",
        match &bare {
            Ok(_) => "ADMITTED".to_owned(),
            Err(e) => format!("REFUSED: {e}"),
        }
    );
    // RE-PINNED BY R4.
    //
    // AT R3 (pin `f391bd466`): both rows REFUSED. The `termination_by b` row
    // reached the well-founded lowering and died at the DECREASE — its `else`
    // branch bound no hypothesis, so no positivity fact about `b` was in scope
    // and `a % b < b` was genuinely underivable. R3 recorded this as a separate
    // prelude-side increment and did not claim it.
    //
    // AT R4: the `termination_by b` row is ADMITTED. Two things had to land,
    // and R3's note named neither correctly — see
    // `r4_bool_test_bridge_probes` for the measurements:
    //   1. an `ite`→`dite` normalization inside the well-founded lowering, so
    //      the negative branch BINDS `¬((b == 0) = true)` at the call site
    //      (definitional: `ite c t e ≡ dite c (fun _ => t) (fun _ => e)`);
    //   2. `Nat.pos_of_ne_zero` + `of_not_decide_eq_true`, proved and
    //      axiom-free, to turn that hypothesis into `Nat.mod_lt`'s `0 < b`.
    //
    // The BARE row — no `termination_by` at all — is STILL refused, and that is
    // correct and unchanged: without a declared measure the structural
    // auto-detector claims `gcdBare b (a % b)`'s first argument and routing
    // never reaches the well-founded lowering. R4 extends what a DECLARED
    // measure can discharge; it does not add measure inference.
    by_measure.expect(
        "R4: the Bool-test spelling with `termination_by b` now elaborates — \
         ite→dite binds the negative hypothesis and the positivity bridge \
         converts it",
    );
    bare.expect_err("with no termination_by at all it is still refused");
}

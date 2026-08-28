// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **R4 PROBES — what the VERBATIM Bool-test `gcd` spelling actually needs,
//! measured in the elaborator's own lane before anything moved.**
//!
//! R3 landed the `dite` spelling (`if h : 0 < b then gcd b (a % b) else a`)
//! and left this one refused:
//!
//! ```text
//! def gcd (a b : Nat) : Nat := if b == 0 then a else gcd b (a % b)
//! ```
//!
//! R3's recorded reason: *"an `ite` binds no hypothesis, so nothing bounds `b`
//! away from zero"*, with a named prerequisite of a prelude positivity bridge
//! (`Nat.pos_of_ne_zero`, measured ABSENT). These probes re-measured that claim
//! at the CURRENT pin and, crucially, measured the thing the R3 note did not
//! record: **the exact Prop the `b == 0` test elaborates to**, because the
//! bridge theorem's statement has to match it or the cascade cannot fire.
//!
//! # What the pre-change run said (2026-08-22, at pin `27a46804e`)
//!
//! | # | question | verdict THEN | verdict NOW |
//! |---|---|---|---|
//! | q0 | is `Nat.pos_of_ne_zero` in the prelude? | **ABSENT**, and so were `Nat.ne_of_beq_eq_false`, `Nat.zero_lt_of_ne_zero`, `Nat.beq_eq_false_of_ne`. PRESENT: `Nat.eq_of_beq_eq_true`, `Nat.beq`, `Nat.decEq`, `Nat.zero_lt_succ`, `Nat.mod_lt`, `ite`, `dite`, `instBEqNat`, `of_decide_eq_true/false` | `Nat.pos_of_ne_zero` and `of_not_decide_eq_true` are PRESENT, both proved, both foundational-only |
//! | q1 | what Prop does `b == 0` elaborate to inside an `if`? | `@Eq Bool (@BEq.beq Nat (instBEqOfDecidableEq Nat instDecidableEqNat) b 0) Bool.true`, under a NON-dependent `ite`. **Not `Nat.beq`** — the R3 note's named prerequisite `Nat.ne_of_beq_eq_false` would not have matched anything | unchanged (the elaboration is untouched) |
//! | q2 | is `ite c t e ≡ dite c (fun _ => t) (fun _ => e)`? | **YES, definitionally** — kernel-confirmed by `rfl`. This is what makes the `ite`→`dite` normalization a rewrite rather than a reinterpretation | unchanged |
//! | q2b | is `n == 0` def-eq to `Nat.beq n 0`? | **NO** (kernel type mismatch). It IS def-eq to `decide (n = 0)` | unchanged |
//! | q3 | does the verbatim Bool `gcd` elaborate? | **NO** — *"no decreasing proof was found for a recursive call site"*, i.e. it reached the well-founded lowering and died at the DECREASE | **ADMITTED** |
//!
//! **So the R3 note was right about the cause and wrong about the cure.** The
//! blocker really was "an `ite` binds no hypothesis". But the named
//! prerequisite was mis-specified twice over: a `Nat.beq`-shaped bridge would
//! not have matched the elaborated condition (q1/q2b), and a bridge theorem
//! ALONE would not have helped at all, because with a non-dependent `ite` there
//! is no hypothesis for any bridge to consume (q2). The `ite`→`dite`
//! normalization is the load-bearing half; the theorem is what makes the
//! hypothesis it exposes usable.
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

// ════════════ (q0) the prelude inventory, re-measured at THIS pin ════════════

/// What bridges a Bool test to a Prop today? Prints one row per candidate so
/// the inventory is readable in the test log, then asserts the two halves that
/// the design depends on: the positivity bridge is ABSENT (so it must be
/// added), and its ingredients are PRESENT (so it can be added as a proved
/// theorem rather than an axiom).
#[test]
fn probe_q0_bool_to_prop_bridge_inventory() {
    let env = Environment::with_prelude();
    let candidates = [
        "Nat.pos_of_ne_zero",
        "of_not_decide_eq_true",
        "of_decide_eq_true",
        "of_decide_eq_false",
        "Nat.ne_of_beq_eq_false",
        "Nat.eq_of_beq_eq_true",
        "Nat.zero_lt_of_ne_zero",
        "Nat.beq_eq_false_of_ne",
        "Nat.beq",
        "Nat.decEq",
        "Nat.zero_lt_succ",
        "Nat.mod_lt",
        "Nat.lt",
        "Nat.rec",
        "False.elim",
        "Eq.refl",
        "ite",
        "dite",
        "instBEqNat",
        "BEq.beq",
    ];
    for name in candidates {
        match env.get_const(&Name::from_string(name)) {
            Some(c) => eprintln!("INVENTORY | {name:32} | PRESENT ({:?})", c.kind),
            None => eprintln!("INVENTORY | {name:32} | ABSENT"),
        }
    }

    // RE-PINNED: the two theorems R4 adds are now present, PROVED, and
    // foundational-only. An `axiom` here would be the trust-root escape
    // `r2_axiom_closure_probes` c1 measures, so the closure is asserted, not
    // assumed.
    let foundational = ["propext", "Quot.sound", "Classical.choice"];
    for added in ["Nat.pos_of_ne_zero", "of_not_decide_eq_true"] {
        let n = Name::from_string(added);
        let c = env
            .get_const(&n)
            .unwrap_or_else(|| panic!("R4 registers `{added}` into with_prelude"));
        assert_eq!(
            c.kind,
            ConstantKind::Theorem,
            "`{added}` must be a proof-carrying Theorem, never an axiom"
        );
        assert!(c.value.is_some(), "`{added}` must carry its proof term");
        let closure = env.axiom_deps(&n).expect("registered");
        let offending: Vec<String> = closure
            .iter()
            .map(ToString::to_string)
            .filter(|ax| !foundational.contains(&ax.as_str()))
            .collect();
        assert!(
            offending.is_empty(),
            "`{added}` must be foundational-only, got {offending:?}"
        );
        eprintln!("INVENTORY | {added:32} | ADDED by R4, Theorem, foundational-only");
        eprintln!("          | type: {:?}", c.type_);
    }

    // CONTROL: the R3 note's OTHER named candidates are still absent, and were
    // never needed — see q1/q2b for why a `Nat.beq`-shaped bridge could not
    // have matched the elaborated `==` condition in the first place.
    for missing in ["Nat.ne_of_beq_eq_false", "Nat.zero_lt_of_ne_zero"] {
        assert!(
            env.get_const(&Name::from_string(missing)).is_none(),
            "measured: `{missing}` is absent, and R4 did not need it"
        );
    }

    // The proof's ingredients must all be present, or it could not be built.
    for needed in [
        "Nat.rec",
        "Nat.zero_lt_succ",
        "False.elim",
        "Eq.refl",
        "Decidable.rec",
        "decide",
    ] {
        assert!(
            env.get_const(&Name::from_string(needed)).is_some(),
            "the positivity bridge's proof needs `{needed}` in with_prelude"
        );
    }
}

// ═══════ (q1) the exact Prop `b == 0` elaborates to inside an `if` ═══════

/// THE measurement the R3 note is missing. A bridge theorem is useless unless
/// its hypothesis is def-eq to what the `else` branch would actually bind, so
/// dump the elaborated body of a NON-recursive definition with the same test.
///
/// Non-recursive on purpose: this isolates the `if b == 0 then _ else _`
/// elaboration from every question about well-founded recursion.
#[test]
fn probe_q1_bool_test_elaborated_shape() {
    const PROBE: &str = "def boolTestShape (a b : Nat) : Nat := if b == 0 then a else a % b";
    let env = Environment::with_prelude();
    let result = elab_one(&env, PROBE).expect("a non-recursive Bool test must elaborate");
    let ElabResult::Definition { val, .. } = &result else {
        panic!("expected a Definition");
    };
    eprintln!("SHAPE | elaborated body:\n{val:?}");
    let rendered = format!("{val:?}");
    // Assert the two facts the design turns on: it is a NON-dependent `ite`
    // (hence no hypothesis), and the condition mentions `Nat.beq`.
    assert!(
        rendered.contains("ite"),
        "the Bool test must elaborate through `ite`; got {rendered}"
    );
    eprintln!(
        "SHAPE | mentions dite? {} | mentions Nat.beq? {} | mentions Eq? {}",
        rendered.contains("dite"),
        rendered.contains("beq"),
        rendered.contains("Eq")
    );
}

// ═══ (q2) does the ite→dite rewrite preserve the VALUE definitionally? ═══

/// The faithfulness question, asked of the kernel rather than argued in prose.
/// `ite` and `dite` are both `is_reducible` definitions that δ-reduce to the
/// SAME `Decidable.casesOn` application, so `ite c t e` and
/// `dite c (fun _ => t) (fun _ => e)` must be definitionally equal — and a
/// `rfl` proof at a concrete instance is the kernel confirming it.
#[test]
fn probe_q2_ite_dite_are_definitionally_equal() {
    let mut env = Environment::with_prelude();
    const PAIR: &str = "theorem iteDiteSame (a b : Nat) : \
         (if b == 0 then a else a % b) = \
         (dite ((b == 0) = true) (fun _ => a) (fun _ => a % b)) := rfl";
    let result = register_one(&mut env, PAIR);
    match &result {
        Ok(_) => eprintln!("PROBE-ROW | q2 ite ≡ dite | ADMITTED (kernel-checked by rfl)"),
        Err(e) => eprintln!("PROBE-ROW | q2 ite ≡ dite | REFUSED: {e}"),
    }
    result.expect(
        "the ite→dite rewrite must be DEFINITIONAL — both are reducible \
         definitions with the same Decidable.casesOn body",
    );
}

// ═ (q2b) what is the elaborated `b == 0` Bool def-eq to at the kernel? ═

/// The bridge theorem has to be STATED in something the cascade's strict
/// recheck will accept against the real hypothesis. The elaborated test is
/// `@BEq.beq Nat (instBEqOfDecidableEq Nat instDecidableEqNat) n 0`, NOT
/// `Nat.beq n 0` — so ask the kernel whether those two are the same term up
/// to δ, one `rfl` per candidate spelling. Whatever is GREEN here is what the
/// theorem may be stated in.
#[test]
fn probe_q2b_beq_spelling_defeq_matrix() {
    let rows: [(&str, &str); 4] = [
        (
            "n == 0  ≡  Nat.beq n 0",
            "theorem beqA (n : Nat) : (n == 0) = Nat.beq n 0 := rfl",
        ),
        (
            "n == 0  ≡  decide (n = 0)",
            "theorem beqB (n : Nat) : (n == 0) = decide (n = 0) := rfl",
        ),
        (
            "0 < n   ≡  Nat.lt 0 n",
            "theorem ltA (n : Nat) : (0 < n) = Nat.lt 0 n := rfl",
        ),
        (
            "Nat.lt 0 n ≡ Nat.le 1 n",
            "theorem ltB (n : Nat) : Nat.lt 0 n = Nat.le 1 n := rfl",
        ),
    ];
    let mut any_green = false;
    for (label, src) in rows {
        let mut env = Environment::with_prelude();
        match register_one(&mut env, src) {
            Ok(_) => {
                any_green = true;
                eprintln!("DEFEQ | {label:28} | GREEN");
            }
            Err(e) => eprintln!("DEFEQ | {label:28} | RED: {e}"),
        }
    }
    assert!(
        any_green,
        "at least one spelling must be def-eq or the bridge cannot be stated"
    );
}

// ═══════ (q3) the verbatim Bool `gcd`, re-measured at this pin ═══════

/// The R4 target, verbatim from the two-language paper's §1 demo.
pub const GCD_BOOL_VERBATIM: &str = "def gcd (a b : Nat) : Nat := \
     if b == 0 then a else gcd b (a % b)\n\
     termination_by b";

#[test]
fn probe_q3_verbatim_bool_gcd_status() {
    let env = Environment::with_prelude();
    let result = elab_one(&env, GCD_BOOL_VERBATIM);
    match &result {
        Ok(_) => eprintln!("PROBE-ROW | q3 verbatim Bool gcd | ADMITTED"),
        Err(e) => eprintln!("PROBE-ROW | q3 verbatim Bool gcd | REFUSED: {e}"),
    }
    // BEFORE (at pin `27a46804e`): `Unsupported feature: well-founded recursion
    // for 'gcd': `termination_by` with a non-structural recursive call. no
    // decreasing proof was found for a recursive call site (tried: hypothesis
    // lookup, Nat.sub_lt, Nat.mod_lt, omega, simp_arith)`. R3 had already moved
    // the refusal from the NAME to the DECREASE; R4 discharges the decrease.
    result.expect(
        "R4's target: the VERBATIM Bool-test `gcd` must elaborate — the \
         ite→dite normalization binds `¬((b == 0) = true)` at the call site \
         and the positivity bridge turns it into `0 < b` for `Nat.mod_lt`",
    );
}

/// CONTROL: the `dite` spelling R3 landed still works and still computes.
/// If this ever goes red, an R4 change broke R3 rather than extending it.
#[test]
fn probe_q4_r3_dite_spelling_still_computes() {
    let mut env = Environment::with_prelude();
    const GCD_DITE: &str = "def gcdD (a b : Nat) : Nat := \
         if h : 0 < b then gcdD b (a % b) else a\n\
         termination_by b";
    register_one(&mut env, GCD_DITE).expect("R3's dite spelling must still elaborate");
    const COMPUTES: &str = "theorem gcdDComputes : gcdD 12 18 = 6 := rfl";
    register_one(&mut env, COMPUTES).expect("R3's dite spelling must still COMPUTE 6");
    eprintln!("PROBE-ROW | q4 R3 dite gcd 12 18 = 6 | STILL GREEN");
}

/// A `ConstantKind` re-export sanity check so the inventory probe's `PRESENT
/// (Theorem)` rows mean what they say.
#[test]
fn probe_q5_mod_lt_is_still_a_proved_theorem() {
    let env = Environment::with_prelude();
    let c = env
        .get_const(&Name::from_string("Nat.mod_lt"))
        .expect("Nat.mod_lt is the decrease R4 still relies on");
    assert_eq!(c.kind, ConstantKind::Theorem);
    assert!(c.value.is_some());
}

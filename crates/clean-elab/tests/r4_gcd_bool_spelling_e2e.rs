// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **R4 E2E — the VERBATIM Bool-test `gcd` elaborates, kernel-verifies, and
//! COMPUTES.**
//!
//! ```text
//! def gcd (a b : Nat) : Nat := if b == 0 then a else gcd b (a % b)
//! termination_by b
//! ```
//!
//! This is the §1 demo spelling from the two-language paper, character for
//! character. R3 landed the `dite` spelling (`if h : 0 < b then …`) and
//! recorded this one as out of fragment. R4 closes it with two pieces, both
//! asserted here:
//!
//! 1. **A prelude positivity bridge, proved.** `Nat.pos_of_ne_zero` and
//!    `of_not_decide_eq_true` are axiom-free `Declaration::Theorem`s. This is
//!    the trust root, so an `axiom` here would be exactly the escape hatch the
//!    closure audits look for — asserted, not assumed.
//! 2. **An `ite`→`dite` normalization inside the well-founded lowering.** A
//!    non-dependent `ite` binds NO hypothesis, so a bridge theorem alone would
//!    have had nothing to consume. `ite c t e` and
//!    `dite c (fun _ => t) (fun _ => e)` are DEFINITIONALLY equal (both are
//!    reducible definitions unfolding to the same `Decidable.casesOn`), so the
//!    rewrite preserves the value — which is why `gcd 12 18` still computes.
//!
//! Fail-closed is unchanged: every candidate decreasing proof is strictly
//! re-inferred and def-eq checked before use, and the refusal tests at the tail
//! pin that undischargeable decreases are still REJECTED, not admitted.

use clean_elab::{
    elaborate_decl, elaborate_decl_and_register, preprocess_decl_with_context, ElabError,
    ElabResult, FileContext,
};
use clean_kernel::name::Name;
use clean_kernel::{ConstantKind, Environment};
use clean_parser::parse_file;

fn register_one(env: &mut Environment, source: &str) -> Result<ElabResult, ElabError> {
    let decls = parse_file(source).expect("source should parse");
    assert_eq!(decls.len(), 1, "fixture must be exactly one declaration");
    let mut file_ctx = FileContext::new();
    let processed = preprocess_decl_with_context(&decls[0], &mut file_ctx);
    elaborate_decl_and_register(env, &processed)
}

fn elab_one(env: &Environment, source: &str) -> Result<ElabResult, ElabError> {
    let decls = parse_file(source).expect("source should parse");
    assert_eq!(decls.len(), 1, "fixture must be exactly one declaration");
    let mut file_ctx = FileContext::new();
    let processed = preprocess_decl_with_context(&decls[0], &mut file_ctx);
    elaborate_decl(env, &processed)
}

/// The R4 target, verbatim.
const GCD_BOOL: &str = "def gcd (a b : Nat) : Nat := \
     if b == 0 then a else gcd b (a % b)\n\
     termination_by b";

const FOUNDATIONAL: [&str; 3] = ["propext", "Quot.sound", "Classical.choice"];

fn assert_foundational_only(env: &Environment, name: &str) {
    let n = Name::from_string(name);
    let closure = env
        .axiom_deps(&n)
        .unwrap_or_else(|| panic!("`{name}` must be registered"));
    let offending: Vec<String> = closure
        .iter()
        .map(ToString::to_string)
        .filter(|ax| !FOUNDATIONAL.contains(&ax.as_str()))
        .collect();
    assert!(
        offending.is_empty(),
        "`{name}` must have a foundational-only axiom closure, got {offending:?}"
    );
}

// ═══════════════ §1 the prelude bridge, as a PROVED theorem ═══════════════

/// `Nat.pos_of_ne_zero : ∀ n, ¬(n = 0) → 0 < n` — present, a `Theorem` with a
/// proof term, foundational-only closure. The kernel-side twin of this test is
/// `clean-kernel/src/env/nat_pos_of_ne_zero_proof.rs::tests`; this one asserts
/// it from the ELABORATOR's environment, i.e. that `with_prelude` actually
/// wires it rather than it merely being registrable on request.
#[test]
fn nat_pos_of_ne_zero_is_in_the_prelude_and_proved() {
    let env = Environment::with_prelude();
    let c = env
        .get_const(&Name::from_string("Nat.pos_of_ne_zero"))
        .expect("R4 wires `Nat.pos_of_ne_zero` into with_prelude");
    assert_eq!(
        c.kind,
        ConstantKind::Theorem,
        "the positivity bridge is kernel-adjacent: an axiom here is a trust-root escape"
    );
    assert!(c.value.is_some(), "must carry its proof term");
    assert_foundational_only(&env, "Nat.pos_of_ne_zero");
    eprintln!("R4 | Nat.pos_of_ne_zero  | Theorem, proof-carrying, foundational-only");
}

/// `of_not_decide_eq_true : ¬(decide p = true) → ¬p` — the generic Bool→Prop
/// step. Same standard.
#[test]
fn of_not_decide_eq_true_is_in_the_prelude_and_proved() {
    let env = Environment::with_prelude();
    let c = env
        .get_const(&Name::from_string("of_not_decide_eq_true"))
        .expect("R4 wires `of_not_decide_eq_true` into with_prelude");
    assert_eq!(c.kind, ConstantKind::Theorem);
    assert!(c.value.is_some(), "must carry its proof term");
    assert_foundational_only(&env, "of_not_decide_eq_true");
    eprintln!("R4 | of_not_decide_eq_true | Theorem, proof-carrying, foundational-only");
}

/// The bridge is USABLE from source, not merely present: this proves
/// `0 < 7` through it, so the theorem's argument order and implicit/explicit
/// binder structure are pinned by something that would break if they moved.
#[test]
fn the_bridge_is_usable_from_source() {
    let mut env = Environment::with_prelude();
    const USE: &str = "theorem sevenPos : Nat.lt 0 7 := \
         Nat.pos_of_ne_zero 7 (fun h => Nat.noConfusion h)";
    let result = register_one(&mut env, USE);
    match &result {
        Ok(_) => eprintln!("R4 | Nat.pos_of_ne_zero applied from source | ADMITTED"),
        Err(e) => eprintln!("R4 | Nat.pos_of_ne_zero applied from source | REFUSED: {e}"),
    }
    result.expect("the positivity bridge must be applicable from Clean source");
}

// ═══════════════ §2 the target: elaborates AND computes ═══════════════

/// THE R4 GATE. The verbatim Bool-test `gcd` elaborates, registers (so the
/// kernel re-checked the whole definition at `add_decl`), and **computes**:
/// `gcd 12 18 = 6` by `rfl`, which only holds if the emitted term reduces.
///
/// `gcd 12 18` is the interesting direction — the first recursive step swaps
/// the arguments (`gcd 18 (12 % 18)` = `gcd 18 12`), so this exercises the
/// widened motive as well as the decrease.
#[test]
fn verbatim_bool_gcd_elaborates_and_computes_six() {
    let mut env = Environment::with_prelude();
    register_one(&mut env, GCD_BOOL).expect(
        "R4's target: `def gcd (a b : Nat) : Nat := if b == 0 then a else gcd b (a % b)` \
         must elaborate and kernel-verify",
    );

    let gcd = env
        .get_const(&Name::from_string("gcd"))
        .expect("gcd must be registered after a successful elaboration");
    assert!(
        gcd.value.is_some(),
        "gcd must be a value-carrying definition, not an opaque or an axiom"
    );

    const COMPUTES: &str = "theorem gcdComputes : gcd 12 18 = 6 := rfl";
    register_one(&mut env, COMPUTES).expect(
        "the ite→dite normalization is DEFINITIONAL, so the emitted gcd must \
         still reduce: gcd 12 18 = 6 by rfl",
    );
    eprintln!("R4 | verbatim Bool gcd | ADMITTED and COMPUTES gcd 12 18 = 6");
}

/// The other argument order, and the two base-ish cases — so "it computes" is
/// not one lucky reduction.
#[test]
fn verbatim_bool_gcd_computes_several_values() {
    let mut env = Environment::with_prelude();
    register_one(&mut env, GCD_BOOL).expect("gcd must elaborate");
    for (src, what) in [
        ("theorem g1 : gcd 18 12 = 6 := rfl", "gcd 18 12 = 6"),
        ("theorem g2 : gcd 7 0 = 7 := rfl", "immediate base case"),
        ("theorem g3 : gcd 0 5 = 5 := rfl", "zero numerator"),
        ("theorem g4 : gcd 17 5 = 1 := rfl", "coprime"),
        ("theorem g5 : gcd 48 18 = 6 := rfl", "longer chain"),
    ] {
        register_one(&mut env, src).unwrap_or_else(|e| panic!("{what} must compute: {e}"));
        eprintln!("R4 | compute | {what} | GREEN");
    }
}

/// The emitted definition's own axiom closure is foundational-only — nothing
/// was smuggled in through the decreasing proof.
#[test]
fn verbatim_bool_gcd_has_a_foundational_only_closure() {
    let mut env = Environment::with_prelude();
    register_one(&mut env, GCD_BOOL).expect("gcd must elaborate");
    assert_foundational_only(&env, "gcd");
    eprintln!("R4 | gcd axiom closure | foundational-only");
}

// ═══════════════ §3 the normalization is value-preserving ═══════════════

/// The faithfulness claim, asked of the kernel: `ite` and `dite` at the same
/// condition are definitionally equal, so rewriting one to the other inside the
/// well-founded lowering cannot change what the definition means.
#[test]
fn ite_and_dite_are_definitionally_equal() {
    let mut env = Environment::with_prelude();
    const PAIR: &str = "theorem iteDiteSame (a b : Nat) : \
         (if b == 0 then a else a % b) = \
         (dite ((b == 0) = true) (fun _ => a) (fun _ => a % b)) := rfl";
    register_one(&mut env, PAIR).expect(
        "ite ≡ dite must hold DEFINITIONALLY — both are reducible definitions \
         with the same Decidable.casesOn body",
    );
    eprintln!("R4 | ite ≡ dite | kernel-confirmed by rfl");
}

/// The `dite` spelling R3 landed is untouched and still computes. If this goes
/// red, R4 broke R3 rather than extending it.
#[test]
fn r3_dite_spelling_is_unaffected() {
    let mut env = Environment::with_prelude();
    const GCD_DITE: &str = "def gcdD (a b : Nat) : Nat := \
         if h : 0 < b then gcdD b (a % b) else a\n\
         termination_by b";
    register_one(&mut env, GCD_DITE).expect("R3's dite spelling must still elaborate");
    register_one(&mut env, "theorem gcdDC : gcdD 12 18 = 6 := rfl")
        .expect("R3's dite spelling must still compute 6");
    assert_foundational_only(&env, "gcdD");
    eprintln!("R4 | R3 dite gcd | STILL GREEN, foundational-only");
}

// ═════════ §4 the same lane generalizes past gcd (the `-` decrease) ═════════

/// The positivity route is wired into the `Nat.sub_lt` tier as well as
/// `Nat.mod_lt`, so a Bool-tested countdown works for the same reason `gcd`
/// does. This is what makes R4 a cascade extension rather than a `gcd` special
/// case.
#[test]
fn bool_tested_countdown_also_elaborates_and_computes() {
    let mut env = Environment::with_prelude();
    const COUNTDOWN: &str = "def cdown (b : Nat) : Nat := \
         if b == 0 then 0 else cdown (b - 1)\n\
         termination_by b";
    let result = register_one(&mut env, COUNTDOWN);
    match &result {
        Ok(_) => eprintln!("R4 | Bool-tested `b - 1` countdown | ADMITTED"),
        Err(e) => eprintln!("R4 | Bool-tested `b - 1` countdown | REFUSED: {e}"),
    }
    result.expect("the Nat.sub_lt tier must see the same derived positivity");
    register_one(&mut env, "theorem cd : cdown 5 = 0 := rfl").expect("and it must compute");
    assert_foundational_only(&env, "cdown");
}

// ═══════════════ §5 fail-closed is UNCHANGED ═══════════════

/// A recursion with no decrease is still REJECTED, and rejected AT THE
/// DECREASE. The `ite`→`dite` normalization exposes a hypothesis; it does not
/// manufacture a proof, and a hypothesis that does not bound the measured
/// argument still discharges nothing.
///
/// The shape reaches the well-founded lowering on purpose: the call's
/// parameter-0 argument is the bare `b`, which the structural auto-detector
/// claims, while `termination_by b` names parameter 1 — so the declaration
/// wins (R3's routing rule), the lowering runs, and `Nat.lt (a + 1) b` is what
/// fails. Pinning the LAYER, not just the fact of refusal, is what makes this a
/// real control: it proves the Bool-test lane still evaluates the obligation
/// rather than having stopped asking.
#[test]
fn a_bool_test_that_proves_nothing_is_still_refused_at_the_decrease() {
    let env = Environment::with_prelude();
    const NO_DECREASE: &str = "def spin (a b : Nat) : Nat := \
         if b == 0 then a else spin b (a + 1)\n\
         termination_by b";
    let result = elab_one(&env, NO_DECREASE);
    match &result {
        Ok(_) => eprintln!("R4 | non-decreasing Bool recursion | ADMITTED (BAD)"),
        Err(e) => eprintln!("R4 | non-decreasing Bool recursion | REFUSED: {e}"),
    }
    let err = result.expect_err(
        "FAIL-CLOSED: a recursive call that does not decrease the measure must \
         be rejected, Bool test or not — nothing may be registered",
    );
    let msg = err.to_string();
    assert!(
        msg.contains("no decreasing proof was found"),
        "it must be refused at the DECREASE, not at routing: {msg}"
    );
}

/// And nothing is left registered behind a refusal.
#[test]
fn a_refused_definition_registers_nothing() {
    let mut env = Environment::with_prelude();
    const NO_DECREASE: &str = "def spin2 (a b : Nat) : Nat := \
         if b == 0 then a else spin2 b (a + 1)\n\
         termination_by b";
    let _ = register_one(&mut env, NO_DECREASE);
    assert!(
        env.get_const(&Name::from_string("spin2")).is_none(),
        "a refused well-founded definition must not leave a constant behind"
    );
}

/// The measure must still be a parameter the lowering supports: a genuinely
/// two-parameter (lexicographic) measure is still refused, and R4 does not
/// widen that. Pins that the new cascade tier did not accidentally make an
/// unsupported TERMINATION shape look supported.
#[test]
fn multi_parameter_measures_are_still_refused() {
    let env = Environment::with_prelude();
    const LEX: &str = "def lex (a b : Nat) : Nat := \
         if b == 0 then a else lex (a % b) (b - 1)\n\
         termination_by a + b";
    let result = elab_one(&env, LEX);
    match &result {
        Ok(_) => eprintln!("R4 | two-parameter measure | ADMITTED"),
        Err(e) => eprintln!("R4 | two-parameter measure | REFUSED: {e}"),
    }
    result.expect_err("a measure mentioning two parameters is still outside the fragment");
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The COMBINATION fixture for the two lanes landed together on 2026-09-18:
//! a table keyed on nested `Nat` literals whose arm bodies are machine-word bit
//! operations. Neither lane alone can compile a single declaration in this
//! file, and current `main` (24e25d10a) can compile none of them either:
//!
//! * `agents/prelude-bits-20260916` supplies `<<<` / `>>>` / `^^^` and
//!   `toUInt{M}` at the machine carriers, and the rule that types a bare
//!   numeral shift amount at the carrier. Without it every arm body here is
//!   `failed to synthesize instance HShiftLeft UInt64 UInt64 UInt64`.
//! * `agents/natmatch-blowup-20260916` makes an arm bind the caller's fallback
//!   ONCE instead of inlining a copy into every nested `Nat.casesOn` minor.
//!   Without it the `mask` table below — literals 6, 7 and 8 in a NESTED
//!   position — repeats its alternative `7 · 8 · 9 = 504` times; MEASURED by
//!   reverting only the sharing predicate, 11,239 nodes against 384. The
//!   magnitude of the same defect is measured where it belongs, on the owner's
//!   22-arm table, in `nat_literal_table_match_e2e.rs`, which is killed at a
//!   3 GB watchdog cap in about a second without this fix.
//! * `main`'s own 569076d4f makes a nested literal MEAN that literal. It is on
//!   main, and it is what makes the blow-up above reachable at all: before it,
//!   `some 6` planned as `Nat.zero`, one level deep and one node wide. The two
//!   fixes are therefore not independent — closing the meaning defect makes the
//!   machine-safety defect strictly WORSE on exactly these shapes, which is why
//!   they must travel together.
//!
//! ## What is asserted
//!
//! 1. The table elaborates and kernel-checks, and each arm computes ITS value
//!    by axiom-free `rfl` — the bit result, not merely some `UInt64`.
//! 2. The lowered term is LINEAR in `Σ (kᵢ+1)`, with the zeta-inlined size (the
//!    term the pre-fix elaborator emitted) measured beside it so the bound is
//!    shown to be discriminating rather than merely satisfied.
//! 3. The close negative twins stay REFUSED and register nothing: the
//!    shift-past-the-width-is-zero reading, the `|||`-for-`^^^` reading, and
//!    the wrong-arm reading that the pre-fix nested planner PROVED.
//!
//! Predicted-output note: this file asserts on values and on the environment,
//! never on rendered diagnostic text, so it carries no golden output.
//!
//! ## KEEP EVERY COMPARED VALUE SMALL — measured, not stylistic
//!
//! Deciding `u = <Nat literal>` by `rfl`, where `u : UInt{N}` is given by an
//! ARITHMETIC EXPRESSION, costs memory proportional to the numeric VALUE:
//! about 50 KB of RSS per unit
//! (`docs/issues/2026-09-17-uint32-literal-defeq-cost-scales-with-value.md`,
//! and the same paragraph in `CLAUDE.md`). That is a pre-existing property of
//! the kernel's defeq on this shape, owned by neither lane merged here, and it
//! is why no arm below states a bit at position 30 or above: the first draft of
//! this file did (`mask (some 30) = 1073741824`) and was measured at **24 GB of
//! RSS against an 8 GB gate reservation** before it was killed, on this host,
//! 2026-09-18. Every value asserted here is under 300, and the whole file is
//! measured below. If a later arm needs a wide bit, state it as `.toNat` — the
//! document records that spelling as free at any value.

use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_kernel::env::Environment;
use clean_kernel::{Expr, ExprKind, Name, TypeChecker};
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

fn elaborate_all(env: &mut Environment, source: &str) {
    try_elaborate_into(env, source)
        .unwrap_or_else(|e| panic!("source must elaborate and kernel-check: {e}\n{source}"));
}

/// A registered `rfl` theorem: present, re-inferable to its own statement, and
/// with an EMPTY axiom closure — pure reduction, no `sorry`, no fabricated
/// axiom. This is the only reading of "the arm computes its value" that a
/// native reducer cannot fake, because the kernel re-checks the term.
fn assert_rfl_theorem(env: &Environment, name: &str) {
    let info = env
        .get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("`{name}` must be registered"));
    let proof = info
        .value
        .as_ref()
        .unwrap_or_else(|| panic!("`{name}` must carry a proof value"));
    let tc = TypeChecker::new(env);
    let inferred = tc
        .infer_type(proof)
        .unwrap_or_else(|e| panic!("`{name}` proof must infer a type: {e}"));
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "`{name}` proof type must be def-eq to its statement"
    );
    let deps = env
        .axiom_deps(&Name::from_string(name))
        .unwrap_or_else(|| panic!("`{name}` must have an axiom_deps closure"));
    assert!(deps.is_empty(), "`{name}` must be axiom-free; got {deps:?}");
}

fn assert_all_rfl(env: &Environment, names: &[&str]) {
    for name in names {
        assert_rfl_theorem(env, name);
    }
}

/// A false claim must be REFUSED and must leave nothing registered. The second
/// half matters as much as the first: a refusal that still registers the
/// constant would let a later `rfl` cite it.
fn assert_rejected(env: &mut Environment, name: &str, source: &str) {
    let result = try_elaborate_into(env, source);
    assert!(result.is_err(), "false claim must be rejected: {source}");
    assert!(
        env.get_const(&Name::from_string(name)).is_none(),
        "rejected `{name}` must not be registered"
    );
}

const SIZE_CAP: usize = 2_000_000;
/// Per-level node budget of the lowered chain: one `Nat.casesOn` application
/// with its motive, major, matching minor and fallback minor. Deliberately
/// generous, and larger than the 64 `nat_literal_table_match_e2e.rs` uses,
/// because these arm bodies are machine-word expressions rather than a bare
/// numeral — a per-level budget must not be a disguised assertion about how
/// big an arm body may be. MEASURED on this table: 384 nodes shared against a
/// bound of 2,304 (6x inside it) and 11,239 duplicated (4.9x outside it), so
/// the constant separates the two cases by a wide margin in both directions.
const NODES_PER_LEVEL: usize = 96;

fn tree_size_capped(expr: &Expr, zeta: bool, cap: usize) -> usize {
    fn go(expr: &Expr, zeta: bool, cap: usize, seen: &mut usize) {
        if *seen >= cap {
            return;
        }
        *seen += 1;
        match expr.kind() {
            ExprKind::App(f, a) => {
                go(f, zeta, cap, seen);
                go(a, zeta, cap, seen);
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                go(ty, zeta, cap, seen);
                go(body, zeta, cap, seen);
            }
            ExprKind::Let(_, ty, val, body, _) => {
                if zeta {
                    go(&body.instantiate(val), zeta, cap, seen);
                } else {
                    go(ty, zeta, cap, seen);
                    go(val, zeta, cap, seen);
                    go(body, zeta, cap, seen);
                }
            }
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => go(inner, zeta, cap, seen),
            _ => {}
        }
    }
    let mut seen = 0;
    go(expr, zeta, cap, &mut seen);
    seen
}

fn def_value(env: &Environment, name: &str) -> Expr {
    env.get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("`{name}` must be registered"))
        .value
        .clone()
        .unwrap_or_else(|| panic!("`{name}` must have a defining value"))
}

/// Pattern literals of the `mask` table. The KEYS may be as large as memory
/// allows (they cost `Σ (kᵢ+1)` casesOn levels with the fix and `∏ (kᵢ+1)`
/// tree nodes without it); it is the compared VALUES that must stay small, per
/// the module header. These three make the duplicated term
/// `7 · 8 · 9 = 504` copies of the alternative it repeats: measured, 11,239
/// nodes against a bound of 2,304, where the shared form is 384. A factor of
/// five on each side of the bound is all this fixture needs — the MAGNITUDE of
/// defect A is measured where it belongs, on the owner's 22-arm table, in
/// `nat_literal_table_match_e2e.rs`.
const MASK_LITERALS: [usize; 3] = [6, 7, 8];

const MASK_TABLE: &str = "\
def mask : Option Nat → UInt64
  | some 6 => (1 : UInt64) <<< 3
  | some 7 => (1 : UInt64) <<< 4
  | some 8 => (255 : UInt8).toUInt64 ^^^ 240
  | _      => 0
theorem mask_6 : mask (some 6) = 8 := rfl
theorem mask_7 : mask (some 7) = 16 := rfl
theorem mask_8 : mask (some 8) = 15 := rfl
theorem mask_default_below : mask (some 5) = 0 := rfl
theorem mask_default_between : mask (some 0) = 0 := rfl
theorem mask_default_none : mask none = 0 := rfl
";

#[test]
fn nested_literal_table_of_shifts_computes_and_stays_linear() {
    let mut env = Environment::with_prelude();
    elaborate_all(&mut env, MASK_TABLE);
    assert_all_rfl(
        &env,
        &[
            "mask_6",
            "mask_7",
            "mask_8",
            "mask_default_below",
            "mask_default_between",
            "mask_default_none",
        ],
    );

    let value = def_value(&env, "mask");
    let levels: usize = MASK_LITERALS.iter().map(|k| k + 1).sum();
    let bound = NODES_PER_LEVEL * levels;
    let shared = tree_size_capped(&value, false, SIZE_CAP);
    assert!(
        shared <= bound,
        "mask: tree size {shared} exceeds the linear bound {bound} (= {NODES_PER_LEVEL} × \
         Σ(kᵢ+1) = {levels}); the fallback is being duplicated per nested casesOn level again"
    );

    // The adversarial control: zeta-inlining every `let` reconstructs the term
    // the pre-fix elaborator emitted. If THAT also fits the bound, the bound is
    // not discriminating and the test above proves nothing.
    let inlined = tree_size_capped(&value, true, SIZE_CAP);
    assert!(
        inlined > bound,
        "the zeta-inlined term is {inlined} nodes, within the bound {bound}: this fixture no \
         longer separates the shared form from the duplicated one, so it is not evidence"
    );
    // Printed, not only asserted: a bound that is satisfied says nothing on its
    // own, and the ratio is the figure a future reader needs in order to tell a
    // regression from a re-tuned constant. Visible under `--nocapture`.
    println!(
        "mask: levels={levels} bound={bound} shared={shared} zeta_inlined={inlined} \
         ratio={:.1}x",
        inlined as f64 / shared as f64
    );
}

#[test]
fn the_tables_close_negative_twins_stay_refused() {
    let mut env = Environment::with_prelude();
    elaborate_all(&mut env, MASK_TABLE);

    // (a) The wrong-arm reading — what the pre-`569076d4f` nested planner
    // PROVED, since every nested literal was `Nat.zero`: the first literal arm
    // firing on `some 0`.
    assert_rejected(
        &mut env,
        "mask_wrong_zero",
        "theorem mask_wrong_zero : mask (some 0) = 8 := rfl",
    );
    // (b) The adjacent-arm reading: source order is what selects.
    assert_rejected(
        &mut env,
        "mask_wrong_adjacent",
        "theorem mask_wrong_adjacent : mask (some 7) = 8 := rfl",
    );
    // (c) The default is not a catch-all for a listed key.
    assert_rejected(
        &mut env,
        "mask_wrong_default",
        "theorem mask_wrong_default : mask (some 8) = 0 := rfl",
    );
    // (d) The shift amount is not the key: `some 6` shifts by 3, not by 6.
    assert_rejected(
        &mut env,
        "mask_amount_is_not_the_key",
        "theorem mask_amount_is_not_the_key : mask (some 6) = 64 := rfl",
    );
}

#[test]
fn a_shift_amount_at_or_past_the_width_is_taken_mod_the_width() {
    // The half of the prelude lane that a plausible-looking wrong body gets
    // wrong, exercised from inside a nested-literal table so that the two lanes
    // are on the same term. Lean reduces a machine shift amount MODULO the
    // width, so `1 <<< 64` at `UInt64` is `1`, not `0` and not a trap.
    let mut env = Environment::with_prelude();
    elaborate_all(
        &mut env,
        "\
def wrapShift : Option Nat → UInt64
  | some 64 => (1 : UInt64) <<< 64
  | some 65 => (1 : UInt64) <<< 65
  | _       => 7
theorem wrap_64 : wrapShift (some 64) = 1 := rfl
theorem wrap_65 : wrapShift (some 65) = 2 := rfl
theorem wrap_default : wrapShift (some 63) = 7 := rfl
",
    );
    assert_all_rfl(&env, &["wrap_64", "wrap_65", "wrap_default"]);

    // The negative twins are the answers the three wrong semantics give:
    // `checked_shl(..).unwrap_or(0)` and `if b >= bits { 0 }` (the two readings
    // three clean-compiler sites carried), and Rust's own unmasked shift.
    assert_rejected(
        &mut env,
        "wrap_64_is_zero",
        "theorem wrap_64_is_zero : wrapShift (some 64) = 0 := rfl",
    );
    assert_rejected(
        &mut env,
        "wrap_65_is_zero",
        "theorem wrap_65_is_zero : wrapShift (some 65) = 0 := rfl",
    );
}

#[test]
fn xor_and_widening_conversions_compose_inside_a_literal_table() {
    // `^^^` and a cross-width `toUInt64` in the arm bodies of a nested-literal
    // table: the mixed-width helper shape the prelude lane exists for, on the
    // pattern shape the natmatch lane exists for.
    let mut env = Environment::with_prelude();
    elaborate_all(
        &mut env,
        "\
def fold : Option Nat → UInt64
  | some 12 => (255 : UInt8).toUInt64 ^^^ 15
  | some 13 => ((1 : UInt64) <<< 8) ^^^ 1
  | _       => 0
theorem fold_12 : fold (some 12) = 240 := rfl
theorem fold_13 : fold (some 13) = 257 := rfl
theorem fold_default : fold (some 11) = 0 := rfl
",
    );
    assert_all_rfl(&env, &["fold_12", "fold_13", "fold_default"]);

    // `|||` in place of `^^^` is the plausible wrong reducer: it agrees with
    // `^^^` on disjoint bits and differs here (255 ||| 15 = 255, not 240).
    assert_rejected(
        &mut env,
        "fold_12_is_or",
        "theorem fold_12_is_or : fold (some 12) = 255 := rfl",
    );
    // A sign-extending / saturating narrow would not give 240 either; pin the
    // widening direction explicitly.
    assert_rejected(
        &mut env,
        "fold_12_wrong",
        "theorem fold_12_wrong : fold (some 12) = 15 := rfl",
    );
}

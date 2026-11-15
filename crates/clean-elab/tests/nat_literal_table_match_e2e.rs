// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end regression lock for **table-driven matches on `Nat` literals**
//! (key maps, opcode tables, byte classifiers).
//!
//! ## The defect this guards (machine-safety, 2026-09-17)
//!
//! ```text
//! def T : Nat → Nat
//!   | 49 => 1000 | 50 => 1001 | 51 => 1002 | … | c => c
//! ```
//!
//! A literal pattern `k` is the constructor pattern `Nat.succ^k Nat.zero`, so
//! its arm lowers to a chain of `k + 1` nested `Nat.casesOn`, and EVERY level's
//! non-matching minor is the fallback — the next arm's whole alternative. The
//! match compiler inlined that fallback at every level, so arm `i` held
//! `kᵢ + 1` copies of arm `i+1`, which held `kᵢ₊₁ + 1` copies of arm `i+2`, …:
//! linear as an `Arc` DAG, but a TREE of size `∏ (kᵢ + 1)`. Each copy sits
//! under a different minor binder, and the kernel's inference memo is keyed on
//! the node address plus the last active `FVarId`, so `add_decl`'s `check_type`
//! re-inferred the next alternative once per level, recursively. Measured at
//! `origin/main` (release build, peak RSS under a 3 GB watchdog): 2 arms at
//! 49..50 = 71 MB, 3 arms = 546 MB, 4 arms and up killed at 3 GB within 1.1 s,
//! including the owner's 22-arm `keyboard_shift.lean` (which the uncapped
//! read-only measurement had taken to 27.9 GB).
//!
//! The fix binds the fallback ONCE per arm
//! (`let fb := <next alternative> in <casesOn chain mentioning fb>`,
//! `ElabCtx::apply_nested_plans_with_fallback`), which is definitionally the
//! inlined form (zeta) and makes the term linear as a tree.
//!
//! ## What is asserted
//!
//! * **Structure** — the registered definition's TREE size is linear in
//!   `Σ (kᵢ + 1)`, with an adversarial control: the same term with every `let`
//!   zeta-inlined (i.e. the pre-fix term) blows through that bound. The sizes
//!   are counted with a hard cap, and the shapes are small enough that a
//!   regression fails this test instead of eating the machine.
//! * **Meaning** — literal patterns keep Lean's first-match semantics: every
//!   arm, the default below/between/above the literals, and source order are
//!   pinned by `rfl`, axiom-free.
//! * **Negative twins** — a WRONG `rfl` about the same table is still rejected
//!   and not registered: the sharing `let` must not make the match vacuous.
//! * **The real table** — the 22-arm shift map elaborates and kernel-checks in
//!   a child process under a memory watchdog (so a regression is a bounded
//!   test failure, not a 28 GB allocation).
//!
//! The tests drive the SAME pipeline as `clean check`
//! (`parse_file → preprocess_decl_with_context → elaborate_decl_and_register`).

use clean_kernel::env::Environment;
use clean_kernel::{Expr, ExprKind, Name, TypeChecker};

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

fn elaborate_all(env: &mut Environment, source: &str) {
    try_elaborate_into(env, source)
        .unwrap_or_else(|e| panic!("source must elaborate and kernel-check: {e}\n{source}"));
}

/// A registered `rfl` theorem: present, re-inferable to its statement, and with
/// an EMPTY axiom closure (pure reduction — no `sorry`, no fabricated axiom).
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

/// A false claim must be rejected AND leave nothing registered.
fn assert_rejected(env: &mut Environment, name: &str, source: &str) {
    let result = try_elaborate_into(env, source);
    assert!(result.is_err(), "false claim must be rejected: {source}");
    assert!(
        env.get_const(&Name::from_string(name)).is_none(),
        "rejected `{name}` must not be registered"
    );
}

/// TREE size of `expr` (shared `Arc` nodes counted once per occurrence),
/// giving up at `cap`. With `zeta`, every `let` is first inlined into its body
/// — the term the match compiler emitted before the arm-scope sharing. The cap
/// bounds the walk, so measuring the blown-up form costs `O(cap)`, not `O(∏)`.
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

const SIZE_CAP: usize = 2_000_000;

/// Per-level node budget of the lowered chain: one `Nat.casesOn` application
/// with its motive, major, matching minor lambda and fallback minor lambda.
/// Generous (the measured figure is recorded by the assertion message); what
/// matters is that the bound is LINEAR in the summed depths, where the
/// regressed term is their PRODUCT.
const NODES_PER_LEVEL: usize = 64;

fn assert_linear_with_inlined_control(env: &Environment, name: &str, literals: &[usize]) {
    let value = def_value(env, name);
    let levels: usize = literals.iter().map(|k| k + 1).sum();
    let bound = NODES_PER_LEVEL * levels;
    let shared = tree_size_capped(&value, false, SIZE_CAP);
    assert!(
        shared <= bound,
        "`{name}`: tree size {shared} exceeds the linear bound {bound} \
         (= {NODES_PER_LEVEL} × Σ(kᵢ+1) = {levels}); the fallback is being duplicated per \
         nested casesOn level again"
    );
    // Adversarial control: the zeta-inlined (pre-fix) term is NOT within the
    // bound, so the assertion above is discriminating and it is the sharing
    // `let` that holds the size down.
    let inlined = tree_size_capped(&value, true, SIZE_CAP);
    assert!(
        inlined > bound,
        "`{name}`: control failed — the let-inlined term has tree size {inlined} <= bound \
         {bound}, so this shape no longer distinguishes shared from duplicated fallbacks"
    );
}

// ---------------------------------------------------------------------------
// Equation-compiler table: `def T : Nat → Nat | 12 => … | 13 => … | c => c`.
// Small literals on purpose: regressed, this shape is ∏ = 13·14·15·16 ≈ 44k
// copies (a bounded failure), not the 50⁶ of the measured repro.
// ---------------------------------------------------------------------------

const TABLE: &str = "\
def T : Nat → Nat
  | 12 => 1000
  | 13 => 1001
  | 15 => 1003
  | 14 => 1002
  | c  => c
theorem t12 : T 12 = 1000 := rfl
theorem t13 : T 13 = 1001 := rfl
theorem t14 : T 14 = 1002 := rfl
theorem t15 : T 15 = 1003 := rfl
theorem t_below : T 3 = 3 := rfl
theorem t_zero : T 0 = 0 := rfl
theorem t_above : T 16 = 16 := rfl
theorem t_far : T 200 = 200 := rfl
";

#[test]
fn nat_literal_table_is_linear_and_computes_every_arm() {
    let mut env = Environment::with_prelude();
    elaborate_all(&mut env, TABLE);
    for name in [
        "t12", "t13", "t14", "t15", "t_below", "t_zero", "t_above", "t_far",
    ] {
        assert_rfl_theorem(&env, name);
    }
    assert_linear_with_inlined_control(&env, "T", &[12, 13, 15, 14]);
}

#[test]
fn nat_literal_table_wrong_rfl_is_rejected() {
    let mut env = Environment::with_prelude();
    elaborate_all(&mut env, TABLE);
    // Close negative twins of the passing theorems above: a neighbouring arm's
    // value, the default's value for a listed literal, and an arm's value for
    // an unlisted scrutinee.
    assert_rejected(
        &mut env,
        "bad_neighbour",
        "theorem bad_neighbour : T 13 = 1000 := rfl",
    );
    assert_rejected(
        &mut env,
        "bad_default",
        "theorem bad_default : T 14 = 14 := rfl",
    );
    assert_rejected(
        &mut env,
        "bad_unlisted",
        "theorem bad_unlisted : T 16 = 1003 := rfl",
    );
    assert_rejected(
        &mut env,
        "bad_last",
        "theorem bad_last : T 14 = 1003 := rfl",
    );
}

// ---------------------------------------------------------------------------
// Term-level `match` (not the equation compiler), arms out of numeric order:
// the sharing `let` must not change which arm fires.
// ---------------------------------------------------------------------------

#[test]
fn term_match_on_nat_literals_is_linear_and_source_ordered() {
    let mut env = Environment::with_prelude();
    elaborate_all(
        &mut env,
        "\
def U (n : Nat) : Nat :=
  match n with
  | 9 => 1
  | 11 => 2
  | 10 => 3
  | _ => 4
theorem u9 : U 9 = 1 := rfl
theorem u10 : U 10 = 3 := rfl
theorem u11 : U 11 = 2 := rfl
theorem u12 : U 12 = 4 := rfl
theorem u0 : U 0 = 4 := rfl
",
    );
    for name in ["u9", "u10", "u11", "u12", "u0"] {
        assert_rfl_theorem(&env, name);
    }
    assert_linear_with_inlined_control(&env, "U", &[9, 11, 10]);
    assert_rejected(&mut env, "u_bad", "theorem u_bad : U 10 = 2 := rfl");
    assert_rejected(
        &mut env,
        "u_bad_default",
        "theorem u_bad_default : U 11 = 4 := rfl",
    );
}

// ---------------------------------------------------------------------------
// The same table inside a `do` block: `elab_do_match.rs` has its own arm
// compiler and its own fallback threading. Measured at `origin/main`, this
// four-arm shape was killed at the 3 GB watchdog cap after 6.6 s; here it is a
// bounded structural assertion.
// ---------------------------------------------------------------------------

#[test]
fn do_match_nat_literal_table_is_linear_and_computes() {
    let mut env = Environment::with_prelude();
    elaborate_all(
        &mut env,
        "\
def H (n : Nat) : Option Nat := do
  match n with
  | 30 => pure 1000
  | 31 => pure 1001
  | 32 => pure 1002
  | 33 => pure 1003
  | c => pure c
theorem h30 : H 30 = some 1000 := rfl
theorem h32 : H 32 = some 1002 := rfl
theorem h33 : H 33 = some 1003 := rfl
theorem h34 : H 34 = some 34 := rfl
theorem h0 : H 0 = some 0 := rfl
",
    );
    for name in ["h30", "h32", "h33", "h34", "h0"] {
        assert_rfl_theorem(&env, name);
    }
    assert_linear_with_inlined_control(&env, "H", &[30, 31, 32, 33]);
    assert_rejected(&mut env, "h_bad", "theorem h_bad : H 32 = some 1001 := rfl");
    assert_rejected(
        &mut env,
        "h_bad_default",
        "theorem h_bad_default : H 33 = some 33 := rfl",
    );
}

// ---------------------------------------------------------------------------
// `if let <literal>` chains: the else branch is the fallback of every nested
// level, and an `else if let` chain multiplies exactly like match arms did.
// ---------------------------------------------------------------------------

#[test]
fn if_let_nat_literal_chain_is_linear_and_computes() {
    let mut env = Environment::with_prelude();
    elaborate_all(
        &mut env,
        "\
def G (n : Nat) : Nat :=
  if let 12 := n then 1000 else if let 13 := n then 1001 else if let 14 := n then 1002 else n
theorem g12 : G 12 = 1000 := rfl
theorem g13 : G 13 = 1001 := rfl
theorem g14 : G 14 = 1002 := rfl
theorem g3 : G 3 = 3 := rfl
theorem g15 : G 15 = 15 := rfl
",
    );
    for name in ["g12", "g13", "g14", "g3", "g15"] {
        assert_rfl_theorem(&env, name);
    }
    assert_linear_with_inlined_control(&env, "G", &[12, 13, 14]);
    assert_rejected(&mut env, "g_bad", "theorem g_bad : G 13 = 1002 := rfl");
    assert_rejected(
        &mut env,
        "g_bad_else",
        "theorem g_bad_else : G 14 = 14 := rfl",
    );
}

// ---------------------------------------------------------------------------
// A tactic arm body must NOT see the arm-scope fallback placeholder: if it
// were in scope while the body is elaborated, `assumption` would close the
// goal with the NEXT arm's value and silently change the table. The result
// type is `Bool` so that no pattern local (all `Nat`) can satisfy the goal —
// the placeholder (typed at the branch type) is the only candidate.
// ---------------------------------------------------------------------------

#[test]
fn fallback_placeholder_is_not_a_hypothesis_of_the_arm_body() {
    let mut env = Environment::with_prelude();
    let result = try_elaborate_into(
        &mut env,
        "\
def V : Nat → Bool
  | 6 => by assumption
  | 7 => true
  | c => false
",
    );
    let error = result.expect_err(
        "`by assumption` has no `Bool` hypothesis in a literal arm; it must not be closed by \
         the shared-fallback placeholder",
    );
    assert!(
        error.contains("assumption"),
        "the refusal must come from `assumption` finding no hypothesis, got: {error}"
    );
    assert!(env.get_const(&Name::from_string("V")).is_none());
}

// ---------------------------------------------------------------------------
// The real table (aterm `keyboard_shift.lean`, 22 arms, literals 39..=96), in
// a child process under a memory watchdog. Pre-fix this shape is
// ∏ (kᵢ + 1) ≈ 10³⁷ copies: the watchdog is what makes a regression a test
// failure instead of a machine hazard.
// ---------------------------------------------------------------------------

const SHIFT_TABLE: &str = "\
def ShiftSpecSym : Nat → Nat
  | 49 => 33
  | 50 => 64
  | 51 => 35
  | 52 => 36
  | 53 => 37
  | 54 => 94
  | 55 => 38
  | 56 => 42
  | 57 => 40
  | 48 => 41
  | 96 => 126
  | 45 => 95
  | 61 => 43
  | 91 => 123
  | 93 => 125
  | 92 => 124
  | 59 => 58
  | 39 => 34
  | 44 => 60
  | 46 => 62
  | 47 => 63
  | c  => c
theorem shift_1 : ShiftSpecSym 49 = 33 := rfl
theorem shift_0 : ShiftSpecSym 48 = 41 := rfl
theorem shift_backtick : ShiftSpecSym 96 = 126 := rfl
theorem shift_quote : ShiftSpecSym 39 = 34 := rfl
theorem shift_slash : ShiftSpecSym 47 = 63 := rfl
theorem shift_letter_fixed : ShiftSpecSym 97 = 97 := rfl
theorem shift_low_fixed : ShiftSpecSym 7 = 7 := rfl
";

const SHIFT_LITERALS: [usize; 21] = [
    49, 50, 51, 52, 53, 54, 55, 56, 57, 48, 96, 45, 61, 91, 93, 92, 59, 39, 44, 46, 47,
];

const CHILD_ENV: &str = "CLEAN_NAT_LITERAL_TABLE_CHILD";
/// Post-fix the child stays far under this (a release `clean check` of the same
/// table peaks at 69 MB). Pre-fix, measured by reverting the fix in a debug
/// build, the child climbs past the cap in about five minutes and this test
/// fails with the peak in its message rather than taking the machine down.
const CHILD_RSS_CAP_KB: u64 = 3 * 1024 * 1024;
const CHILD_DEADLINE: std::time::Duration = std::time::Duration::from_secs(900);

fn shift_table_child() {
    let mut env = Environment::with_prelude();
    elaborate_all(&mut env, SHIFT_TABLE);
    for name in [
        "shift_1",
        "shift_0",
        "shift_backtick",
        "shift_quote",
        "shift_slash",
        "shift_letter_fixed",
        "shift_low_fixed",
    ] {
        assert_rfl_theorem(&env, name);
    }
    let value = def_value(&env, "ShiftSpecSym");
    let levels: usize = SHIFT_LITERALS.iter().map(|k| k + 1).sum();
    let bound = NODES_PER_LEVEL * levels;
    let shared = tree_size_capped(&value, false, SIZE_CAP);
    assert!(
        shared <= bound,
        "ShiftSpecSym: tree size {shared} exceeds the linear bound {bound}"
    );
    assert_rejected(
        &mut env,
        "shift_bad",
        "theorem shift_bad : ShiftSpecSym 50 = 33 := rfl",
    );
    assert_rejected(
        &mut env,
        "shift_bad_default",
        "theorem shift_bad_default : ShiftSpecSym 47 = 47 := rfl",
    );
}

#[cfg(unix)]
fn child_rss_kb(pid: u32) -> Option<u64> {
    let out = std::process::Command::new("ps")
        .args(["-o", "rss=", "-p", &pid.to_string()])
        .output()
        .ok()?;
    String::from_utf8_lossy(&out.stdout).trim().parse().ok()
}

/// The parent half: spawn this same test as a child with `CHILD_ENV` set and
/// hold it under an RSS + wall-clock watchdog, so a regression to the
/// duplicated fallback is a bounded test FAILURE and not a 28 GB allocation.
///
/// Split out of the `#[test]` so that the child re-entry can be a two-armed
/// `if`/`else` rather than an early `return`. That shape is what
/// `scripts/check_self_skipping_tests.py` measures (EARLY_RETURN: a `return`
/// with assertions after it), and its ratchet counts a hit whether or not it is
/// allowlisted -- correctly, since a reader cannot see from the `return` that
/// the branch taking it runs every assertion inside `shift_table_child`.
/// Neither arm can pass without asserting.
fn watchdogged_shift_table_parent() {
    #[cfg(not(unix))]
    {
        // No portable RSS probe: run in-process. The structural tests above
        // still catch the regression on a bounded shape first.
        shift_table_child();
    }
    #[cfg(unix)]
    {
        use std::process::{Command, Stdio};
        use std::time::Instant;

        let exe = std::env::current_exe().expect("test binary path");
        let mut child = Command::new(exe)
            .args([
                "--exact",
                "keyboard_shift_table_checks_within_memory_bound",
                "--test-threads=1",
            ])
            .env(CHILD_ENV, "1")
            .stdout(Stdio::null())
            .stderr(Stdio::inherit())
            .spawn()
            .expect("spawn watchdogged child test");
        let started = Instant::now();
        let mut peak_kb = 0_u64;
        let status = loop {
            if let Some(status) = child.try_wait().expect("poll child") {
                break status;
            }
            if let Some(rss) = child_rss_kb(child.id()) {
                peak_kb = peak_kb.max(rss);
            }
            if peak_kb > CHILD_RSS_CAP_KB || started.elapsed() > CHILD_DEADLINE {
                let _ = child.kill();
                let _ = child.wait();
                panic!(
                    "22-arm Nat-literal table blew its budget: peak RSS {peak_kb} KiB (cap \
                     {CHILD_RSS_CAP_KB} KiB) after {:?} (deadline {CHILD_DEADLINE:?}); the \
                     fallback is being duplicated per nested casesOn level again",
                    started.elapsed()
                );
            }
            std::thread::sleep(std::time::Duration::from_millis(100));
        };
        assert!(
            status.success(),
            "watchdogged child failed ({status}); peak RSS {peak_kb} KiB"
        );
    }
}

#[test]
fn keyboard_shift_table_checks_within_memory_bound() {
    if std::env::var_os(CHILD_ENV).is_some() {
        // The child re-entry. Every assertion of this test lives in
        // `shift_table_child`, which this arm runs in THIS process, under the
        // parent's watchdog.
        shift_table_child();
    } else {
        watchdogged_shift_table_parent();
    }
}

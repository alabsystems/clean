// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression pin — `%`, `/`, `&&&` and `|||` at the machine carriers.
//!
//! ## The gap (measured 2026-08-22)
//!
//! ```text
//! def v (a b : UInt64) : UInt64 := a % b      -- FAILED
//! def v (a b : Nat)    : Nat    := a % b      -- worked
//! def v (a b : UInt64) : UInt64 := a + b      -- worked
//! ```
//!
//! Not the operand-ordering bug `binop_carrier_first_numeral.rs` pins: this
//! failed between two VARIABLES, at every width, with no numeral anywhere. It
//! was a pure declaration gap at TWO layers — neither the backing operations
//! `UInt{N}.div/.mod/.land/.lor` nor the `HDiv`/`HMod`/`HAnd`/`HOr` instances
//! existed, while the `H*` classes and the native reducers for those very
//! operation names had been in place the whole time.
//!
//! ## The zero divisor is the whole risk
//!
//! `/` and `%` at a machine width are TOTAL in Lean 4 — `n / 0 = 0`
//! (`Nat.div_zero`), `n % 0 = n` (`Nat.mod_zero`) — and Clean's own `Nat.div` /
//! `Nat.mod` bodies say the same thing (`Nat.div`'s `n = 0` branch is literally
//! `Nat.zero`; `Nat.mod`'s fuel recursion at `n = 0` walks `a - 0 = a` down to
//! `a`). A declared `W.div a b := W.ofNat (Nat.div a.toNat b.toNat)` that
//! disagreed with that would be a false-computation vector — strictly worse
//! than the honest refusal it replaced — so the values are checked here, by the
//! KERNEL (`TypeChecker::is_def_eq`) rather than by asking the elaborator.
//!
//! See `data_types_uint.rs::init_one_uint_arith` for which reducer actually
//! fires on a ground term (the `Nat`-level one; the per-width UInt arithmetic
//! reducers decline on well-typed operands) and why the dormant ones were
//! checked for agreement anyway.

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::{Expr, TypeChecker};
use clean_parser::parse_file;

const WIDTHS: [&str; 4] = ["UInt8", "UInt16", "UInt32", "UInt64"];

/// `(surface operator, the `H*` class it desugars to, the backing operation)`.
const OPS: [(&str, &str, &str); 4] = [
    ("%", "HMod", "mod"),
    ("/", "HDiv", "div"),
    ("&&&", "HAnd", "land"),
    ("|||", "HOr", "lor"),
];

/// Drive the real file pipeline, and KERNEL-CHECK every definition it produces
/// (`TypeChecker::check_type` against the declared type) before registering it.
/// A pass here is therefore not an elaborator self-report.
fn elaborate_file(source: &str) -> Result<(Environment, Vec<(String, Expr)>), String> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    let mut values = Vec::new();
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let result =
            elaborate_decl_and_register(&mut env, &processed).map_err(|e| e.to_string())?;
        if let ElabResult::Definition { name, ty, val, .. } = &result {
            let tc = TypeChecker::new(&env);
            tc.check_type(val, ty)
                .map_err(|e| format!("kernel rejected {name}: {e}"))?;
            values.push((name.to_string(), val.clone()));
        }
    }
    Ok((env, values))
}

/// Elaborate + kernel-check, returning the last definition's value.
fn expect_value(source: &str) -> Expr {
    let (_, values) = elaborate_file(source)
        .unwrap_or_else(|e| panic!("must elaborate and kernel-check, got: {e}\n{source}"));
    values
        .last()
        .unwrap_or_else(|| panic!("no definition produced\n{source}"))
        .1
        .clone()
}

fn expect_refusal(source: &str) -> String {
    match elaborate_file(source) {
        Ok(_) => panic!("must be REFUSED, but elaborated:\n{source}"),
        Err(e) => e,
    }
}

/// Elaborate a two-definition file `lhs`/`rhs` and ask the KERNEL whether the
/// two values are definitionally equal. The elaborator does not get a vote on
/// the answer.
fn assert_reduces_to(carrier: &str, expr: &str, expected: &str) {
    let source = format!("def lhs : {carrier} := {expr}\n\ndef rhs : {carrier} := {expected}\n");
    let (env, values) = elaborate_file(&source)
        .unwrap_or_else(|e| panic!("must elaborate and kernel-check, got: {e}\n{source}"));
    let tc = TypeChecker::with_mode(&env, env.mode());
    assert!(
        tc.is_def_eq(&values[0].1, &values[1].1),
        "{carrier}: `{expr}` must reduce to `{expected}`"
    );
}

// ── The gap: two VARIABLES, every width, every operator ────────────────────

#[test]
fn div_mod_and_or_elaborate_between_two_variables_at_every_uint_width() {
    for carrier in WIDTHS {
        for (op, _, _) in OPS {
            let _ = expect_value(&format!(
                "def probe (a b : {carrier}) : {carrier} := a {op} b"
            ));
        }
    }
}

/// The carrier-first pass means a bare numeral takes its type from the sibling
/// operand on EITHER side, so both directions must work at the new operators
/// too — the two fixes are independent and this is where they meet.
#[test]
fn div_mod_and_or_elaborate_with_a_numeral_on_either_side() {
    for carrier in WIDTHS {
        for (op, _, _) in OPS {
            let _ = expect_value(&format!(
                "def probe_right (a : {carrier}) : {carrier} := a {op} 3"
            ));
            let _ = expect_value(&format!(
                "def probe_left (a : {carrier}) : {carrier} := 12 {op} a"
            ));
        }
    }
}

/// The instance that resolves is the one for the CARRIER, not the `Nat` one —
/// a fix that silently computed at `Nat` and coerced would be worse than the
/// refusal it replaced.
#[test]
fn the_carrier_instance_resolves_not_the_nat_one() {
    for carrier in WIDTHS {
        for (op, class, _) in OPS {
            let val = expect_value(&format!(
                "def probe (a b : {carrier}) : {carrier} := a {op} b"
            ));
            let printed = format!("{val:?}");
            assert!(
                printed.contains(&format!("\"inst{class}{carrier}\"")),
                "`{op}` at {carrier} must resolve inst{class}{carrier}, got:\n{printed}"
            );
            assert!(
                !printed.contains(&format!("\"inst{class}Nat\"")),
                "`{op}` at {carrier} must not fall back to the Nat instance:\n{printed}"
            );
        }
    }
}

/// The backing operation CONSTANT exists, so a downstream consumer has a callee
/// to recognise. Trust's Clean-origin CALL lane carries a standing "miss" entry
/// for `{C}.div` / `{C}.mod`; it was assumed to be a Trust recogniser gap, and
/// it was not — the constants did not exist in Clean's prelude at all.
///
/// Note the elaborated TERM is `@HMod.hMod C C C instHModC a b`: the operation
/// constant is reached by unfolding the (reducible) instance, not by appearing
/// in the term. So this is asserted against the ENVIRONMENT, which is where the
/// recogniser looks.
#[test]
fn the_backing_operation_constant_is_registered() {
    let (env, _) = elaborate_file("def probe (a b : UInt64) : UInt64 := a % b")
        .expect("must elaborate and kernel-check");
    for carrier in WIDTHS {
        for (_, _, backing) in OPS {
            let cname = format!("{carrier}.{backing}");
            let info = env
                .get_const(&clean_kernel::Name::from_string(&cname))
                .unwrap_or_else(|| panic!("{cname} must be a constant in the prelude"));
            assert_eq!(
                info.kind,
                clean_kernel::ConstantKind::Definition,
                "{cname} must be a Definition, never an Axiom"
            );
        }
    }
}

// ── The VALUES ─────────────────────────────────────────────────────────────

#[test]
fn division_and_modulus_compute_at_every_uint_width() {
    for carrier in WIDTHS {
        assert_reduces_to(carrier, &format!("(7 : {carrier}) / 2"), "3");
        assert_reduces_to(carrier, &format!("(7 : {carrier}) % 3"), "1");
        assert_reduces_to(carrier, &format!("(255 : {carrier}) / 16"), "15");
        assert_reduces_to(carrier, &format!("(255 : {carrier}) % 16"), "15");
    }
}

#[test]
fn bitwise_and_or_compute_at_every_uint_width() {
    for carrier in WIDTHS {
        assert_reduces_to(carrier, &format!("(12 : {carrier}) &&& 10"), "8");
        assert_reduces_to(carrier, &format!("(12 : {carrier}) ||| 10"), "14");
        assert_reduces_to(carrier, &format!("(240 : {carrier}) &&& 60"), "48");
        assert_reduces_to(carrier, &format!("(240 : {carrier}) ||| 12"), "252");
    }
}

/// THE LOAD-BEARING VALUE TEST. `/` and `%` are total at a machine width, and
/// the value at the zero divisor is the one place the declared body and the
/// pre-registered native reducer could have disagreed. Lean 4: `n / 0 = 0`,
/// `n % 0 = n`.
#[test]
fn the_zero_divisor_is_total_and_matches_lean() {
    for carrier in WIDTHS {
        assert_reduces_to(carrier, &format!("(7 : {carrier}) / 0"), "0");
        assert_reduces_to(carrier, &format!("(7 : {carrier}) % 0"), "7");
        assert_reduces_to(carrier, &format!("(0 : {carrier}) / 0"), "0");
        assert_reduces_to(carrier, &format!("(0 : {carrier}) % 0"), "0");
    }
}

/// `Nat`, which already worked, must keep working — and keep its own answers.
#[test]
fn nat_keeps_working() {
    for (op, _, _) in OPS {
        let _ = expect_value(&format!("def probe (a b : Nat) : Nat := a {op} b"));
        let _ = expect_value(&format!("def probe (a : Nat) : Nat := a {op} 3"));
        let _ = expect_value(&format!("def probe (a : Nat) : Nat := 12 {op} a"));
    }
    assert_reduces_to("Nat", "(7 : Nat) / 2", "3");
    assert_reduces_to("Nat", "(7 : Nat) % 3", "1");
    assert_reduces_to("Nat", "(7 : Nat) / 0", "0");
    assert_reduces_to("Nat", "(7 : Nat) % 0", "7");
    assert_reduces_to("Nat", "(12 : Nat) &&& 10", "8");
    assert_reduces_to("Nat", "(12 : Nat) ||| 10", "14");
}

/// `+ - *` are the template these were copied from; they must be untouched.
#[test]
fn addition_subtraction_multiplication_control() {
    for carrier in WIDTHS {
        for op in ["+", "-", "*"] {
            let _ = expect_value(&format!(
                "def probe (a b : {carrier}) : {carrier} := a {op} b"
            ));
        }
    }
    assert_reduces_to("UInt8", "(255 : UInt8) + 1", "0");
    assert_reduces_to("UInt8", "(0 : UInt8) - 1", "255");
    assert_reduces_to("UInt8", "(16 : UInt8) * 16", "0");
}

// ── What was deliberately NOT fixed here, and where it went ────────────────
//
// `xor_and_shifts_are_still_out_of_scope_at_uint_carriers` stood here, pinning
// `^^^`/`<<<`/`>>>` as REFUSED, with the instruction to delete it in the commit
// that closed the boundary. That commit is the one that added
// `uint_xor_shift_conv.rs`, which answers both reasons the old pin gave:
// `UInt{N}.shiftRight` is built on `Nat.div`/`Nat.pow`, not on the admitted
// `Nat.shiftRight`, so the overlay stays axiom-free; and a numeral shift amount
// is measured to resolve at the carrier. The boundary that STILL stands —
// nothing at `USize` — is pinned there
// (`usize_is_still_refused_for_xor_shifts_and_conversions`).

// ── A genuinely missing instance still REFUSES — now readably ──────────────

/// The message must NAME THE GOAL. Before this change the identical failure
/// read `elaboration left unresolved variables (unsolved metavariables ?[7])`;
/// `?7` is an allocation counter that names nothing, and the same `?[7]` was
/// measured for two unrelated programs.
#[test]
fn a_missing_instance_names_the_goal_and_carries_options() {
    let err = expect_refusal(
        "structure Widget where\n  w : Nat\n\ndef bad (a b : Widget) : Widget := a % b\n",
    );
    assert!(
        err.contains("failed to synthesize instance `HMod Widget Widget Widget`"),
        "the refusal must name the goal, got:\n{err}"
    );
    assert!(
        !err.contains("unsolved metavariables"),
        "the refusal must not fall back to naming a metavariable id, got:\n{err}"
    );
    // It must show what the search HAD — the candidate list is the evidence
    // for the claim, and it is read out of the live instance table.
    assert!(
        err.contains("instHModNat"),
        "the refusal must list the candidates the search had, got:\n{err}"
    );
    assert!(
        err.contains("Options:"),
        "the refusal must carry the fix, with options (v7/D3), got:\n{err}"
    );
    assert!(
        err.contains("instance : HMod Widget Widget Widget"),
        "option 2 must spell the instance the reader would write, got:\n{err}"
    );
    // HONESTY: it reports non-DISCOVERY, never non-EXISTENCE. The resolution
    // reason (`NoInstance` vs `MaxDepthExceeded`) is discarded upstream, so a
    // no-such-instance-exists claim would be false in the cap cases.
    assert!(
        err.contains("it is not a proof that no such instance can exist"),
        "the refusal must not overstate what it knows, got:\n{err}"
    );
}

/// The same refusal for an UNASCRIBED def, where the goal's result slot is
/// never pinned. The message must say the goal is not fully determined rather
/// than pretend it was a complete goal with no instance.
#[test]
fn an_undetermined_instance_goal_says_so() {
    let err =
        expect_refusal("structure Widget where\n  w : Nat\n\ndef bad (a b : Widget) := a % b\n");
    assert!(
        err.contains("failed to synthesize instance `HMod Widget Widget ?"),
        "the refusal must name the goal INCLUDING its open slot, got:\n{err}"
    );
    assert!(
        err.contains("NOT fully determined"),
        "an undetermined goal must be reported as undetermined, got:\n{err}"
    );
}

/// Every operator in the family reports its own class, so the message is not a
/// hard-coded string about `%`.
#[test]
fn each_operator_reports_its_own_class() {
    for (op, class, _) in OPS {
        let err = expect_refusal(&format!(
            "structure Widget where\n  w : Nat\n\ndef bad (a b : Widget) : Widget := a {op} b\n"
        ));
        assert!(
            err.contains(&format!(
                "failed to synthesize instance `{class} Widget Widget Widget`"
            )),
            "`{op}` must report a {class} goal, got:\n{err}"
        );
    }
}

/// The explanation must reach the path the failures actually take.
///
/// There are two: `ensure_no_residual_fvars` builds a full explanation — what
/// was left unfilled, which candidates exist, what the reader can do — at
/// declaration CLOSE, and the argument loop raises a bare
/// `FailedToSynthesizeInstance` the moment a GROUND instance goal cannot be
/// resolved. The second aborts the body long before the first runs, so on real
/// input the good message never fired: measured over the pinned Mathlib slice
/// in `reports/source-elab/`, 0 rich against 497 bare. Replacing every proof
/// body with `sorry`, so the argument loop never runs, took the rich count to 3
/// — which is what showed this was a race and not dead code.
///
/// `Widget` has no `HMod` instance and the goal is fully ground, so this is the
/// eager path exactly.
#[test]
fn the_eager_path_carries_the_same_explanation_as_the_close_path() {
    let err = expect_refusal(
        "structure Widget where\n  w : Nat\n\ndef bad (a b : Widget) : Widget := a % b\n",
    );
    assert!(
        err.contains("failed to synthesize instance `HMod Widget Widget Widget`"),
        "the goal line must be unchanged, got:\n{err}"
    );
    assert!(
        err.contains("An instance-implicit argument was left unfilled"),
        "the eager path must carry the explanation, not just the goal, got:\n{err}"
    );
}

/// The diagnostic must not list a candidate and then say there is none.
///
/// `registered_carriers` read the HEAD of each instance type, and a derived
/// instance is Pi-headed — `∀ {α} [Sho α], Sho (Option α)` — so
/// `extract_class_app` returned `None` for it and it contributed no carrier.
/// With every candidate Pi-headed the carrier list came back empty and the
/// Options block took its no-instance branch, so one message listed an instance
/// under "Instance synthesis had these candidates" and, a few lines later, told
/// the reader to "Register an instance of `Sho` — there is currently none."
/// A diagnostic that contradicts itself inside one screen teaches nothing.
#[test]
fn the_failure_help_never_lists_a_candidate_and_then_denies_it() {
    let err = expect_refusal(
        "structure Widget where\n  w : Nat\n\n\
         class Sho (a : Type) where\n  sho : a -> Nat\n\n\
         instance [Sho a] : Sho (Option a) := ⟨fun _ => 0⟩\n\n\
         def bad (x : Widget) : Nat := Sho.sho x\n",
    );
    assert!(
        err.contains("failed to synthesize instance"),
        "the fixture must fail synthesis, or this test proves nothing:\n{err}"
    );
    if err.contains("had these candidates") {
        assert!(
            !err.contains("there is currently none"),
            "the message lists a candidate AND denies one:\n{err}"
        );
    }
}

/// A genuinely MIXED-carrier `%` — `Nat % UInt64` — is still refused, and the
/// refusal now names the heterogeneous goal it could not synthesize instead of
/// a metavariable id. This is the shape real Lean reports for the same source
/// (`failed to synthesize HMod Nat UInt64 ?m`), so naming it is parity, not
/// permissiveness. THE LOAD-BEARING HALF IS THAT IT STILL FAILS: a "fix" that
/// inserted coercions until mixed carriers elaborated would turn this green.
#[test]
fn a_mixed_carrier_modulus_is_still_refused_and_names_both_carriers() {
    let err = expect_refusal("def bad (a : Nat) (b : UInt64) : Nat := a % b");
    assert!(
        err.contains("failed to synthesize instance `HMod Nat UInt64 Nat`"),
        "the refusal must name the heterogeneous goal, got:\n{err}"
    );
    assert!(
        !err.contains("unsolved metavariables"),
        "the refusal must not fall back to naming a metavariable id, got:\n{err}"
    );
}

/// The new rendering is SCOPED to instance goals: a refusal whose residuals are
/// not instance goals keeps the original classified-id wording. What is pinned
/// here is that a plain type error is NOT relabelled as synthesis.
///
/// This comment used to add that the eager ground-goal path "keeps its own
/// shorter message". It no longer does — see
/// `the_eager_path_carries_the_same_explanation_as_the_close_path` above.
#[test]
fn a_plain_type_mismatch_is_not_relabelled_as_instance_synthesis() {
    let err = expect_refusal("def bad (a : Nat) (b : UInt64) : UInt64 := if a < b then b else b");
    assert!(
        err.contains("Type mismatch"),
        "a heterogeneous comparison must stay a type mismatch, got:\n{err}"
    );
}

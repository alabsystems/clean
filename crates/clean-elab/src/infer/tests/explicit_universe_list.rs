// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! U2 rung-4 explicitness channel — what a WRITTEN `.{...}` universe list
//! does at declaration close (`docs/analysis/u2-implementation-plan-2026-08-24.md`
//! §3 stage-3 delta 3c, lane U2, 2026-08-25; corrected to Lean's rule
//! 2026-10-19, `docs/FRONTEND_CLASS_LEDGER.md` class (164)).
//!
//! # Lean's rule
//!
//! A written list is not exhaustive. `levelMVarToParamTypesPreDecls`
//! (`Lean/Elab/MutualDef.lean:1406`) turns a universe metavariable left in a
//! declaration's TYPE into a fresh parameter, and `sortDeclLevelParams`
//! (`Lean/Elab/DeclUtil.lean:79-88`) appends every used parameter the list
//! does not name after the written ones; its only error is a written name the
//! declaration never uses. A metavariable left ONLY in the value is refused
//! ("declaration … contains universe level metavariables … in the
//! declaration body"). Measured on the pinned v4.30.0-rc2:
//!
//! ```text
//! def leak.{u} (A : Type u) (a : A) := fun (B : Type _) (b : B) => b
//! #print leak  -- def leak.{u, u_1} : (A : Type u) → A → (B : Type u_1) → B → B
//! ```
//!
//! # What went wrong here, 2026-08-25 to 2026-10-19
//!
//! The channel was built on the reading that `sortDeclLevelParams` errors on
//! a used level outside a non-empty list, so `leak` (p21) was flipped from a
//! PASS pin to a refusal, and so was every declaration whose type left a
//! level to generalize. The corpus line `def noAns.{u} : noEv → Type u` met
//! it once an unannotated `fun _` binder was typed `?T : Sort ?u`. Only the
//! value-only case is Lean's refusal; p21 is a PASS pin again and p54 pins
//! the refusal that remains.
//!
//! # Why the channel is still needed
//!
//! `preprocess_decl_with_context` merges the file's `universe` names into
//! the SAME `universe_params` vector as the written list, ahead of it, so at
//! declaration close `universe u` and `def f.{u}` are one indistinguishable
//! vector (`test_issue168_param_to_param_canonical` is the merged case).
//! `ElabCtx::file_universe_params` carries the file half — injected from
//! `FileContext` at the one point both halves are still separable — and
//! `set_decl_universe_params` subtracts it. The value-only refusal applies
//! only to a declaration that wrote a list: one that wrote none still
//! generalizes every leftover, where Lean refuses a value-only one too (the
//! OPEN half of class (164)).
//!
//! # What these tests pin
//!
//! The generalization (p21), the refusal (p54) and, in equal weight, the
//! refusal's BOUNDARY (p46 plus the merged-file tests below). A MUST_FAIL
//! probe alone cannot distinguish a precise refusal from an over-broad one:
//! both satisfy it.

use crate::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::Environment;
use clean_parser::parse_file;

const FIXTURE_DIR: &str = "../../tests/fixtures/universes";

fn read_fixture(file: &str) -> String {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join(FIXTURE_DIR)
        .join(file);
    std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("fixture must exist at {}: {e}", path.display()))
}

/// Elaborate every declaration of `src` against the kernel prelude, through
/// the same `preprocess` → `elaborate_with_context` pair `clean check` uses
/// (the file context is what carries `universe` commands, so a helper that
/// skipped it could not exercise this channel at all). Returns
/// `(declaration name, verdict)` per leaf in source order; a verdict is
/// `Ok(())` only when the declaration registered.
fn elab_source(label: &str, src: &str) -> Vec<(String, Result<(), String>)> {
    let decls = parse_file(src).unwrap_or_else(|e| panic!("{label} must parse: {e}"));
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let mut verdicts = Vec::new();
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        match elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx) {
            Ok(result) => {
                let mut leaves = Vec::new();
                result.leaf_decls(&mut leaves);
                for leaf in leaves {
                    match leaf {
                        ElabResult::Failed { name, error, .. } => {
                            verdicts.push((name.to_string(), Err(format!("{error:?}"))));
                        }
                        ElabResult::Theorem { name, .. } | ElabResult::Definition { name, .. } => {
                            verdicts.push((name.to_string(), Ok(())));
                        }
                        ElabResult::Skipped => {}
                        other => panic!("{label}: unexpected leaf {other:?}"),
                    }
                }
            }
            Err(error) => {
                let name = crate::preprocess_ext::decl_name(decl)
                    .map_or_else(|| format!("<decl {}>", verdicts.len()), ToString::to_string);
                verdicts.push((name, Err(format!("{error:?}"))));
            }
        }
    }
    verdicts
}

fn elab_fixture(file: &str) -> Vec<(String, Result<(), String>)> {
    elab_source(file, &read_fixture(file))
}

/// The exact fragment `scripts/u2_battery.sh` pins for p54. Deliberately
/// free of the minted `?u_N` name: which id a leaked level carries is an
/// allocation detail that has already moved once (U2 stage 3 re-based the
/// counter), and a gate that pins it would refuse a change that fixed
/// nothing.
const PINNED_FRAGMENT: &str =
    "that its type does not mention and the explicit universe list `.{u}` does not name";

/// p21: a written `.{u}` whose TYPE leaves a second level registers with TWO
/// parameters, as Lean registers it (`leak.{u, u_1}`, `noAns.{u, u_1}`); the
/// use sites force that arity. This was a refusal from 2026-08-25 to
/// 2026-10-19.
#[test]
fn test_explicit_list_generalizes_a_level_its_type_leaves_as_lean_does() {
    let verdicts = elab_fixture("p21_explicit_list_autoextends.lean");
    let names: Vec<&str> = verdicts.iter().map(|(n, _)| n.as_str()).collect();
    assert_eq!(
        names,
        ["leak", "useLeak", "noEv", "noAns", "useNoAns"],
        "p21: declaration set moved — update the expected list deliberately"
    );
    let failures: Vec<String> = verdicts
        .iter()
        .filter_map(|(name, v)| v.as_ref().err().map(|e| format!("  {name}: {e}")))
        .collect();
    assert!(
        failures.is_empty(),
        "p21: Lean accepts every declaration here at the arity the use sites \
         write; refused:\n{}",
        failures.join("\n")
    );
}

/// p54: a level left only in the VALUE of a declaration that wrote `.{u}` is
/// REFUSED, at the declaration, as Lean refuses it ("contains universe level
/// metavariables … in the declaration body").
#[test]
fn test_explicit_list_refuses_a_level_only_its_value_leaves() {
    let verdicts = elab_fixture("p54_explicit_list_value_only_level_MUST_FAIL.lean");
    let names: Vec<&str> = verdicts.iter().map(|(n, _)| n.as_str()).collect();
    assert_eq!(
        names,
        ["z", "useZ"],
        "p54: declaration set moved — update the expected list deliberately"
    );
    assert!(
        verdicts[0].1.is_ok(),
        "p54: the control `z` must pass: {:?}",
        verdicts[0].1
    );
    let err = verdicts[1]
        .1
        .as_ref()
        .expect_err("p54: `useZ` must be REFUSED — its value leaves a level its type never names");
    assert!(
        err.contains(PINNED_FRAGMENT),
        "p54: refusal lost its pinned fragment `{PINNED_FRAGMENT}`; got: {err}"
    );
}

/// The refusal names the LEAKED level, not just the fact of a leak: a message
/// that only said "some level leaked" would leave the reader to guess which
/// `Sort _` is the culprit in a large declaration.
///
/// AMENDED 2026-08-26b (mint-namespace reservation). This used to assert
/// `err.contains("(u_")`. Universe metavariables are now spelled `?u_N`
/// (`crate::level_mint::MINT_PREFIX`), so the assertion is on the reserved
/// prefix — and that is a claim about CONTENT, not a rename: the leaked level
/// IS a metavariable, and quoting it as `u_0` invited the reader to add `u_0`
/// to the list, which never absorbed it. AMENDED 2026-10-19: the refusal is
/// p54's (value-only) now, and the message states Lean's rule instead of
/// claiming Lean treats the list as exhaustive.
#[test]
fn test_explicit_list_refusal_names_the_leaked_level_and_the_count() {
    let verdicts = elab_fixture("p54_explicit_list_value_only_level_MUST_FAIL.lean");
    let err = verdicts[1]
        .1
        .as_ref()
        .expect_err("p54: `useZ` must be refused");
    assert!(
        err.contains("leaves 1 undetermined universe level"),
        "p54: refusal must state HOW MANY levels leaked; got: {err}"
    );
    let prefix = crate::level_mint::MINT_PREFIX;
    assert!(
        err.contains(&format!("({prefix}")),
        "p54: refusal must NAME the leaked level, in the reserved metavariable \
         spelling `{prefix}N` — a bare `u_N` here would claim the leak is a \
         parameter the author could have declared. Got: {err}"
    );
    assert!(
        err.contains("only when the declaration's type mentions it") && !err.contains("exhaustive"),
        "p54: refusal must state Lean's rule, never that Lean's list is \
         exhaustive. Got: {err}"
    );
}

/// p46, the companion: every neighbouring legitimate shape still elaborates
/// AND registers at the arity its use site demands.
///
/// This is the over-refusal guard. `test_explicit_list_refuses_a_level_only_its_value_leaves`
/// is satisfied by an elaborator that refuses every declaration; this one
/// (with p21's) is not.
#[test]
fn test_neighbouring_legitimate_shapes_still_elaborate() {
    let verdicts = elab_fixture("p46_explicit_list_complete.lean");
    let names: Vec<&str> = verdicts.iter().map(|(n, _)| n.as_str()).collect();
    assert_eq!(
        names,
        [
            "noLeak",
            "useNoLeak",
            "holeDetermined",
            "useDetermined",
            "leakOpen",
            "useOpen",
            "leakScoped",
            "useScoped",
        ],
        "p46: declaration set moved — update the expected list deliberately"
    );
    let failures: Vec<String> = verdicts
        .iter()
        .filter_map(|(name, v)| v.as_ref().err().map(|e| format!("  {name}: {e}")))
        .collect();
    assert!(
        failures.is_empty(),
        "p46: {} of {} declarations rejected — the closure over-refuses:\n{}",
        failures.len(),
        verdicts.len(),
        failures.join("\n")
    );
}

/// The subtraction itself, which is the whole brick: in a file that HAS a
/// `universe` command, a declaration that writes `.{u}` is refused over `u`
/// ALONE when its value leaves a level — the merged-in `w` is not part of its
/// written list and must not appear in the refusal — while its neighbour that
/// writes no list is never refused AS a written list.
///
/// Both directions in one file on purpose. Splitting them would let a channel
/// that simply ignores `FileContext` pass the first half, and one that treats
/// any non-empty vector as written pass the second. `mergedOpen` is accepted
/// today because a declaration with no written list generalizes every
/// leftover; Lean refuses that body too (the OPEN half of
/// `docs/FRONTEND_CLASS_LEDGER.md` class (164)), so the assertion is only
/// that it is not refused as a written list.
#[test]
fn test_file_scope_universe_is_subtracted_not_treated_as_written() {
    let src = "\
universe w

def zz.{v} (x : Sort v) : Nat := 0

def mergedOpen (A : Type w) : Nat := zz (Sort _)

def mergedClosed.{u} (A : Type u) : Nat := zz (Sort _)
";
    let verdicts = elab_source("merged-universe file", src);
    let names: Vec<&str> = verdicts.iter().map(|(n, _)| n.as_str()).collect();
    assert_eq!(names, ["zz", "mergedOpen", "mergedClosed"]);

    assert!(
        verdicts[1]
            .1
            .as_ref()
            .err()
            .is_none_or(|e| !e.contains("explicit universe list")),
        "a file-scope `universe` must NOT read as a written list on a \
         declaration that wrote none — this is the merged case the rung-4 \
         scope cut existed for: {:?}",
        verdicts[1].1
    );

    let err = verdicts[2]
        .1
        .as_ref()
        .expect_err("a written `.{u}` list still refuses a value-only level when a `universe` command merged in");
    assert!(
        err.contains(PINNED_FRAGMENT),
        "the refusal must report the WRITTEN list `.{{u}}`, with the merged \
         `w` subtracted out; got: {err}"
    );
    assert!(
        !err.contains("`.{w"),
        "the merged file-scope name leaked into the reported written list: {err}"
    );
}

/// The SECOND context-construction site, pinned separately because it does
/// not share the first one's code path.
///
/// `module_batch` builds its `ElabCtx` from a FROZEN `LexicalSnapshot`
/// (`module_batch::exec::elab_ctx_for`), not from the live `FileContext` the
/// ordinary entry point reads. An explicitness channel wired at only one of
/// the two would be silently over-refusing on the other — every declaration
/// in a `universe`-bearing file would read as having written a list there —
/// while every test above still passed. Same two shapes as
/// `test_file_scope_universe_is_subtracted_not_treated_as_written`, driven
/// through the planner instead, one per batch so each verdict is its own.
#[test]
fn test_module_batch_context_also_subtracts_file_scope_universes() {
    use crate::module_batch::{elaborate_module, BatchOptions, SourceUnit, UnitId};

    fn batch(src: &str) -> (bool, String) {
        let decls = parse_file(src).expect("batch fixture must parse");
        let mut env = Environment::with_prelude();
        let mut file_ctx = FileContext::new();
        let units = [SourceUnit {
            id: UnitId(0),
            decls: &decls,
        }];
        let outcome = elaborate_module(&mut env, &mut file_ctx, &units, BatchOptions::islands());
        (outcome.committed, outcome.render_rejections())
    }

    let (committed, report) = batch(
        "\
universe w

def zz.{v} (x : Sort v) : Nat := 0

def mergedOpen (A : Type w) : Nat := zz (Sort _)
",
    );
    assert!(
        committed || !report.contains("explicit universe list"),
        "the batch planner read a file-scope `universe` name as a written \
         `.{{...}}` list: {report}"
    );

    let (committed, report) = batch(
        "\
universe w

def zz.{v} (x : Sort v) : Nat := 0

def mergedClosed.{u} (A : Type u) : Nat := zz (Sort _)
",
    );
    assert!(
        !committed,
        "the batch planner accepted a value-only level under a written `.{{u}}` list"
    );
    assert!(
        report.contains(PINNED_FRAGMENT),
        "the batch planner's refusal must report the WRITTEN list, with the \
         merged `w` subtracted out; got: {report}"
    );
}

/// A declaration with a written list and NO leftover level is not touched:
/// the written-list branch is reached only past the `fresh.is_empty()` early
/// return, so the ordinary polymorphic declaration pays nothing and cannot be
/// refused.
#[test]
fn test_written_list_with_no_leftover_is_untouched() {
    let src = "\
def idu.{u} (A : Sort u) (a : A) : A := a

def useIdu : Nat := @idu.{1} Nat Nat.zero
";
    let verdicts = elab_source("no-leftover file", src);
    let failures: Vec<String> = verdicts
        .iter()
        .filter_map(|(name, v)| v.as_ref().err().map(|e| format!("  {name}: {e}")))
        .collect();
    assert!(
        failures.is_empty(),
        "a complete written list must be unaffected:\n{}",
        failures.join("\n")
    );
}

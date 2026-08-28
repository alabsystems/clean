// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! U2 rung-4 explicitness channel — an explicit `.{...}` universe list is
//! CLOSED (`docs/analysis/u2-implementation-plan-2026-08-24.md` §3 stage-3
//! delta 3c, re-scoped as its own brick; lane U2, 2026-08-25).
//!
//! # What was silently accepted
//!
//! `finalize_level_params` (U2 rung 4, `25bdb96a1`) has always split the
//! surviving universe parameters into the declared head and the fresh tail,
//! and has always APPENDED the tail. For a declaration that wrote no list
//! that is Lean's auto-generalization. For one that wrote `.{u}` it is not:
//! Lean's `sortDeclLevelParams` treats a non-empty user level list as
//! exhaustive and errors on a used level outside it.
//!
//! Measured on the release binary at `d549a50bf`, builtin prelude:
//!
//! ```text
//! def leak.{u} (A : Type u) (a : A) := fun (B : Type _) (b : B) => b
//! def useLeak : Nat := @leak.{0, 0} Nat Nat.zero Nat Nat.zero
//! → 2 passed, 0 failed
//!
//! def useLeak1 : Nat := @leak.{0} Nat Nat.zero Nat Nat.zero
//! → UniverseLevelMismatch { name: "leak", expected: 2, actual: 1 }
//! ```
//!
//! `leak` declares one universe parameter and registers with two. Nothing
//! unsound follows — the kernel re-check is untouched and the arity-2 term is
//! well-typed — but the registered interface is not the declared one, and the
//! only report is at a use site that wrote the arity the source says.
//!
//! # Why it was not enforced until now
//!
//! Not the rule; the channel. `preprocess_decl_with_context` merges the
//! file's `universe` names into the SAME `universe_params` vector as the
//! written list, ahead of it, so at declaration close `universe u` and
//! `def f.{u}` are one indistinguishable vector
//! (`test_issue168_param_to_param_canonical` is the merged case). Enforcing
//! closure on that vector would have closed every declaration in any file
//! that ever said `universe`. `ElabCtx::file_universe_params` now carries the
//! file half — injected from `FileContext` at the one point both halves are
//! still separable — and `set_decl_universe_params` subtracts it.
//!
//! # What these tests pin
//!
//! The refusal (p21) and, in equal weight, its BOUNDARY (p46 plus the
//! merged-file test below). A MUST_FAIL probe alone cannot distinguish a
//! precise refusal from an over-broad one: both satisfy it.

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
                    .map_or_else(|| format!("<decl {}>", verdicts.len()), str::to_string);
                verdicts.push((name, Err(format!("{error:?}"))));
            }
        }
    }
    verdicts
}

fn elab_fixture(file: &str) -> Vec<(String, Result<(), String>)> {
    elab_source(file, &read_fixture(file))
}

/// The exact fragment `scripts/u2_battery.sh` pins for p21. Deliberately free
/// of the minted `u_N` name: which id a leaked level carries is an allocation
/// detail that has already moved once (U2 stage 3 re-based the counter), and
/// a gate that pins it would refuse a change that fixed nothing.
const PINNED_FRAGMENT: &str = "the explicit universe list `.{u}` is closed";

/// p21: the declaration that wrote `.{u}` and leaked a second level is
/// REFUSED, at the declaration, on its own line.
#[test]
fn test_explicit_list_closed_refuses_leaked_level() {
    let verdicts = elab_fixture("p21_explicit_list_closed_MUST_FAIL.lean");
    let names: Vec<&str> = verdicts.iter().map(|(n, _)| n.as_str()).collect();
    assert_eq!(
        names,
        ["leak", "useLeak"],
        "p21: declaration set moved — update the expected list deliberately"
    );
    let err = verdicts[0]
        .1
        .as_ref()
        .expect_err("p21: `leak` must be REFUSED — it declares .{u} and needs two levels");
    assert!(
        err.contains(PINNED_FRAGMENT),
        "p21: refusal lost its pinned fragment `{PINNED_FRAGMENT}`; got: {err}"
    );
    assert!(
        verdicts[1].1.is_err(),
        "p21: `useLeak` must fail as a consequence of `leak` never registering"
    );
}

/// The refusal names the LEAKED level, not just the fact of a leak: a message
/// that only said "some level leaked" would leave the reader to guess which
/// `Type _` is the culprit in a large declaration.
///
/// AMENDED 2026-08-26b (mint-namespace reservation). This used to assert
/// `err.contains("(u_")`. Universe metavariables are now spelled `?u_N`
/// (`crate::level_mint::MINT_PREFIX`), so the assertion is on the reserved
/// prefix — and that is a claim about CONTENT, not a rename: the leaked level
/// IS a metavariable, and quoting it as `u_0` invited the reader to add `u_0`
/// to the list, which never absorbed it. The advice clause was corrected in
/// the same change and is asserted below, so the message cannot drift back to
/// telling the reader to name a level that naming cannot fix.
#[test]
fn test_explicit_list_refusal_names_the_leaked_level_and_the_count() {
    let verdicts = elab_fixture("p21_explicit_list_closed_MUST_FAIL.lean");
    let err = verdicts[0]
        .1
        .as_ref()
        .expect_err("p21: `leak` must be refused");
    assert!(
        err.contains("left 1 undetermined universe level"),
        "p21: refusal must state HOW MANY levels leaked; got: {err}"
    );
    let prefix = crate::level_mint::MINT_PREFIX;
    assert!(
        err.contains(&format!("({prefix}")),
        "p21: refusal must NAME the leaked level, in the reserved metavariable \
         spelling `{prefix}N` — a bare `u_N` here would claim the leak is a \
         parameter the author could have declared. Got: {err}"
    );
    assert!(
        err.contains("universe METAVARIABLE, so adding a name to the list will not absorb"),
        "p21: refusal must say why naming it in the list does not work; without \
         that the message quotes a name the user cannot even write. Got: {err}"
    );
}

/// p46, the companion: every neighbouring legitimate shape still elaborates
/// AND registers at the arity its use site demands.
///
/// This is the over-refusal guard. `test_explicit_list_closed_refuses_leaked_level`
/// is satisfied by an elaborator that refuses every declaration; this one is
/// not.
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
/// `universe` command, a declaration that writes `.{u}` is still closed over
/// `u` ALONE — the merged-in `w` is not part of its written list and must not
/// appear in the refusal — while its neighbour that writes no list keeps
/// auto-generalizing.
///
/// Both directions in one file on purpose. Splitting them would let a channel
/// that simply ignores `FileContext` pass the first half, and one that closes
/// on any non-empty vector pass the second.
#[test]
fn test_file_scope_universe_is_subtracted_not_treated_as_written() {
    let src = "\
universe w

def mergedOpen (A : Type w) (a : A) := fun (B : Type _) (b : B) => b

def mergedClosed.{u} (A : Type u) (a : A) := fun (B : Type _) (b : B) => b
";
    let verdicts = elab_source("merged-universe file", src);
    let names: Vec<&str> = verdicts.iter().map(|(n, _)| n.as_str()).collect();
    assert_eq!(names, ["mergedOpen", "mergedClosed"]);

    assert!(
        verdicts[0].1.is_ok(),
        "a file-scope `universe` must NOT close a declaration that wrote no \
         list — this is the merged case the rung-4 scope cut existed for: {:?}",
        verdicts[0].1
    );

    let err = verdicts[1]
        .1
        .as_ref()
        .expect_err("a written `.{u}` list stays closed even when a `universe` command merged in");
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
/// in a `universe`-bearing file would read as closed there — while every test
/// above still passed. Same two shapes as
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

def mergedOpen (A : Type w) (a : A) := fun (B : Type _) (b : B) => b
",
    );
    assert!(
        committed,
        "the batch planner over-refused the merged case — its context reads a \
         file-scope `universe` name as a written `.{{...}}` list: {report}"
    );

    let (committed, report) = batch(
        "\
universe w

def mergedClosed.{u} (A : Type u) (a : A) := fun (B : Type _) (b : B) => b
",
    );
    assert!(
        !committed,
        "the batch planner accepted a leak out of a written `.{{u}}` list"
    );
    assert!(
        report.contains(PINNED_FRAGMENT),
        "the batch planner's refusal must report the WRITTEN list, with the \
         merged `w` subtracted out; got: {report}"
    );
}

/// A declaration with a written list and NO leftover level is not touched:
/// the refusal is reached only past the `fresh.is_empty()` early return, so
/// the ordinary polymorphic declaration pays nothing and cannot be refused.
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

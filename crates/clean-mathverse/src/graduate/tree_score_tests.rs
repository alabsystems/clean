// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the kernel-confirmed tree-score / uniqueness probe.
//!
//! Hosted in a sibling file (pulled in via `#[path]`) so the owning module
//! stays well under the 500-line cap. Coverage: a defeq-but-structurally-distinct
//! pair is bucketed by the kernel-confirmed tree-signature AND confirmed by the
//! kernel `is_def_eq` arbiter; a genuinely distinct pair is never confirmed; a
//! non-`KernelVerified` floor scopes which constants participate.

use clean_kernel::{BinderInfo, Declaration, Expr, Name};

use super::{tree_score_verified_corpus, CollisionForm, TreeScoreOptions};
use crate::export::kernel_export::KernelShardBuilder;
use crate::types::ImportConfidence;

fn bd() -> BinderInfo {
    BinderInfo::Default
}

/// `∀ (p : Prop), p → p` with proof `fun p h => h`.
fn imp_self() -> (Expr, Expr) {
    (
        Expr::pi(
            bd(),
            Expr::prop(),
            Expr::pi(bd(), Expr::bvar(0), Expr::bvar(1)),
        ),
        Expr::lam(
            bd(),
            Expr::prop(),
            Expr::lam(bd(), Expr::bvar(0), Expr::bvar(0)),
        ),
    )
}

/// `∀ (p : Prop), (fun x => x → x) p` — a β-redex statement that is DEFEQ to
/// [`imp_self`]'s type but STRUCTURALLY distinct (the redex is un-reduced).
/// The same proof `fun p h => h` checks against it (the kernel reduces the redex).
fn imp_self_beta_redex() -> (Expr, Expr) {
    // (fun x : Prop => x → x)  applied to the bound `p` (bvar 0 under the ∀).
    let redex_fn = Expr::lam(
        bd(),
        Expr::prop(),
        Expr::pi(bd(), Expr::bvar(0), Expr::bvar(1)),
    );
    (
        Expr::pi(bd(), Expr::prop(), Expr::app(redex_fn, Expr::bvar(0))),
        Expr::lam(
            bd(),
            Expr::prop(),
            Expr::lam(bd(), Expr::bvar(0), Expr::bvar(0)),
        ),
    )
}

/// `∀ (p q : Prop), p → q → p` / `fun p q hp hq => hp` — genuinely distinct,
/// never defeq to the `imp_self` pair.
fn const_left() -> (Expr, Expr) {
    (
        Expr::pi(
            bd(),
            Expr::prop(),
            Expr::pi(
                bd(),
                Expr::prop(),
                Expr::pi(
                    bd(),
                    Expr::bvar(1),
                    Expr::pi(bd(), Expr::bvar(1), Expr::bvar(3)),
                ),
            ),
        ),
        Expr::lam(
            bd(),
            Expr::prop(),
            Expr::lam(
                bd(),
                Expr::prop(),
                Expr::lam(
                    bd(),
                    Expr::bvar(1),
                    Expr::lam(bd(), Expr::bvar(1), Expr::bvar(1)),
                ),
            ),
        ),
    )
}

fn theorem(name: &str, type_: Expr, value: Expr) -> Declaration {
    Declaration::Theorem {
        name: Name::from_string(name),
        level_params: vec![],
        type_,
        value,
    }
}

/// Write one shard with: a base lemma, its β-redex twin (defeq, different form),
/// and a genuinely distinct lemma. All three are stamped `KernelVerified` by the
/// kernel exporter (theorems with a checked value).
fn write_fixture_shard(path: &std::path::Path) {
    let (is_ty, is_val) = imp_self();
    let (rd_ty, rd_val) = imp_self_beta_redex();
    let (cl_ty, cl_val) = const_left();
    let mut builder = KernelShardBuilder::new();
    builder
        .add_declaration(&theorem("Tree.imp_self", is_ty, is_val), &[])
        .expect("export imp_self");
    builder
        .add_declaration(&theorem("Tree.imp_self_redex", rd_ty, rd_val), &[])
        .expect("export imp_self_redex");
    builder
        .add_declaration(&theorem("Tree.const_left", cl_ty, cl_val), &[])
        .expect("export const_left");
    builder.write_to_file(path).expect("write shard");
}

#[test]
fn test_tree_score_confirms_defeq_different_form_with_kernel() {
    let tmp = tempfile::tempdir().expect("tempdir");
    write_fixture_shard(&tmp.path().join("fixture.mathverse"));

    let stats = tree_score_verified_corpus(tmp.path(), &TreeScoreOptions::default())
        .expect("tree-score should succeed over verified shards");

    // All three theorems are KernelVerified and scored.
    assert_eq!(stats.shards, 1);
    assert_eq!(stats.constants, 3);
    assert_eq!(stats.scored, 3, "all three KernelVerified theorems scored");

    // The β-redex twin and the base lemma share the kernel-confirmed
    // tree-signature (whnf collapses the redex) but differ structurally.
    assert_eq!(
        stats.different_form_pairs, 1,
        "exactly the imp_self / imp_self_redex pair is a different-form candidate"
    );
    assert_eq!(
        stats.literal_duplicate_pairs, 0,
        "no two fixtures share an identical structural digest"
    );
    assert_eq!(
        stats.confirmed_same_object, 1,
        "the kernel is_def_eq arbiter must confirm the defeq pair"
    );
    assert_eq!(
        stats.confirmed_different_form, 1,
        "the confirmed hit is a 'same object, different form' pair"
    );
    assert_eq!(stats.hits.len(), 1);
    let hit = &stats.hits[0];
    assert!(hit.same_object, "reported hits are kernel-confirmed");
    assert_eq!(hit.form, CollisionForm::DifferentForm);
    assert_eq!(hit.name_a, "Tree.imp_self");
    assert_eq!(hit.name_b, "Tree.imp_self_redex");
    // The genuinely distinct lemma never collides.
    assert!(
        stats.distinct_tree_signatures >= 2,
        "const_left occupies its own tree-signature bucket"
    );

    // Corpus pin is a well-formed blake3 digest.
    assert!(stats.corpus_digest.starts_with("blake3:"));
}

#[test]
fn test_tree_score_unverified_floor_scopes_scoring() {
    // With a confidence floor of `Unverified` (the weakest), KernelVerified
    // theorems still qualify (they are at least as trusted), so scoring is
    // unchanged — this asserts the floor is "at least as trusted as", not "exactly".
    let tmp = tempfile::tempdir().expect("tempdir");
    write_fixture_shard(&tmp.path().join("fixture.mathverse"));

    let opts = TreeScoreOptions {
        min_confidence: ImportConfidence::Unverified,
        ..TreeScoreOptions::default()
    };
    let stats =
        tree_score_verified_corpus(tmp.path(), &opts).expect("tree-score with weaker floor");
    assert_eq!(
        stats.scored, 3,
        "KernelVerified theorems clear the Unverified floor"
    );
}

#[test]
fn test_tree_score_classifies_literal_duplicate() {
    // Two theorems with byte-identical statements under distinct names: a literal
    // (alpha-equal) duplicate, NOT a re-encoding. The tree-score must classify it
    // as `LiteralDuplicate` and still confirm it via the kernel arbiter.
    let tmp = tempfile::tempdir().expect("tempdir");
    let (ty, val) = imp_self();
    let mut builder = KernelShardBuilder::new();
    builder
        .add_declaration(&theorem("Dup.a", ty.clone(), val.clone()), &[])
        .expect("export a");
    builder
        .add_declaration(&theorem("Dup.b", ty, val), &[])
        .expect("export b");
    builder
        .write_to_file(tmp.path().join("dup.mathverse"))
        .expect("write shard");

    let stats = tree_score_verified_corpus(tmp.path(), &TreeScoreOptions::default())
        .expect("tree-score over duplicate shard");
    assert_eq!(stats.scored, 2);
    assert_eq!(stats.different_form_pairs, 0);
    assert_eq!(stats.literal_duplicate_pairs, 1);
    assert_eq!(stats.confirmed_same_object, 1);
    assert_eq!(stats.confirmed_different_form, 0);
    assert_eq!(stats.hits.len(), 1);
    assert_eq!(stats.hits[0].form, CollisionForm::LiteralDuplicate);
}

#[test]
fn test_tree_score_empty_dir_is_clean() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let stats = tree_score_verified_corpus(tmp.path(), &TreeScoreOptions::default())
        .expect("empty dir scores cleanly");
    assert_eq!(stats.shards, 0);
    assert_eq!(stats.scored, 0);
    assert_eq!(stats.confirmed_same_object, 0);
    assert!(stats.hits.is_empty());
}

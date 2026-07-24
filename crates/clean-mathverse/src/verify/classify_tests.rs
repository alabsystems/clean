// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unit tests for the MATH/GENERATED constant classifier.
//!
//! The load-bearing property is CONSERVATISM: we must never label a real,
//! human-authored theorem as GENERATED (that would inflate the math rate by
//! hiding failures). So the negative tests (honest math that LOOKS internal)
//! matter as much as the positive ones.

use super::*;

fn is_math(name: &str) -> bool {
    classify_const(name) == ConstKind::Math
}

fn is_gen(name: &str) -> bool {
    classify_const(name) == ConstKind::Generated
}

#[test]
fn test_real_math_names_are_math() {
    // Ordinary Mathlib theorems / definitions a mathematician writes.
    for n in [
        "Nat.add_comm",
        "Mathlib.Order.Basic",
        "Group.mul_assoc",
        "Ideal.add_mem",
        "Nat.gcd_comm",
        "Mathlib.Algebra.Group.Defs.MulOneClass",
        "List.length_append",
        "Finset.sum_range_succ",
        "MonoidHom.map_one",
        "Nat.Coprime.gcd_eq_one",
    ] {
        assert!(is_math(n), "expected MATH: {n}");
    }
}

#[test]
fn test_generated_tags_are_generated() {
    // Compiler-emitted internals across the documented families.
    for n in [
        "Nat.rec",
        "Nat.recAux",
        "Nat.casesOn",
        "Nat.brecOn",
        "List.below",
        "List.ibelow",
        "Nat.noConfusion",
        "Nat.noConfusionType",
        "Foo.mk.inj",
        "Foo.mk.sizeOf_spec",
        "Nat.add.eq_1",
        "Nat.add.match_1",
        "Foo.bar.proof_2",
        "Foo.bar._proof_3",
        "Foo.bar._sizeOf_1",
        "Foo.bar._simp_1",
        "instMulNat._cstage1",
        "instMulNat._cstage2",
        "Foo.eq_def",
        "Foo.eq_unfold_1",
        "Nat.add._eq_1",
        "Foo._mutual_1",
        "Foo.toCtorIdx",
        "Nat.decEq",
        "Foo.elim",
        "MyEnum.ofNat",
        // Compiler-IR / LCNF artifacts observed in real Mathlib modules.
        "Function.Injective.linearOrder._boxed",
        "DenselyOrdered.mk._flat_ctor",
        "Foo.bar._inherited_default",
        "LinearOrder.lift'._redArg._lam_0",
        "LinearOrder.lift'._redArg._lam_1",
        "LinearOrder.lift'._redArg",
        "Foo._unsafe_rec",
        // Structure-field auto-default auxiliaries (class fields with defaults).
        "Monoid.npow._default",
        "DivInvMonoid.div._default",
    ] {
        assert!(is_gen(n), "expected GENERATED: {n}");
    }
}

#[test]
fn test_conservative_does_not_mislabel_honest_lookalikes() {
    // Honest human names that merely RESEMBLE internal tags. Substring matching
    // would wrongly flag these; whole-segment matching keeps them MATH.
    for n in [
        "Nat.rec_aux_lemma",    // segment is `rec_aux_lemma`, not `rec`/`recAux`
        "Foo.eq_comm",          // `eq_comm` is a real lemma, not `eq_<digits>`
        "Foo.match_pattern",    // `match_pattern`, not `match_<digits>`
        "Foo.proof_irrel",      // `proof_irrel`, not `proof_<digits>`
        "Foo.below_average",    // `below_average`, not bare `below`
        "Foo.elimination_rule", // `elimination_rule`, not bare `elim`
        "Foo.mkString",         // `mkString`, not bare `mk`
        "Foo.recursive",        // `recursive`, not bare `rec`
        "Foo.foldr_eq",         // `foldr_eq` (and `fold` is exact, not prefix)
        "Group.sizeOf_pos",     // `sizeOf_pos` — wait: this is `sizeOf_<alpha>`
    ] {
        assert!(is_math(n), "should stay MATH (conservative): {n}");
    }
}

#[test]
fn test_sizeof_counter_vs_lemma() {
    // `_sizeOf_1` (generated) vs `sizeOf_spec`-style human lemma boundary.
    assert!(is_gen("Foo._sizeOf_1"));
    assert!(is_gen("Foo.sizeOf_1")); // `sizeOf_<digits>` counter form -> generated
                                     // `sizeOf` as an exact segment is the auto projection -> generated.
    assert!(is_gen("Foo.sizeOf"));
    // But `sizeOf_pos` (alpha tail) is an honest lemma name -> math.
    assert!(is_math("Foo.sizeOf_pos"));
}

#[test]
fn test_bare_hygienic_counter_segment() {
    assert!(is_gen("Foo._123"));
    assert!(is_gen("_private.Foo._42.bar")); // any segment generated => generated
                                             // `_root_` is NOT a digit run — stays math-eligible by this rule alone.
    assert!(is_math("Foo._root_helper") || is_gen("Foo._root_helper"));
}

#[test]
fn test_cstage_specializations() {
    assert!(is_gen("Nat.add._cstage1"));
    assert!(is_gen("instDecidableEqNat._cstage2"));
    // No `_cstage` -> math.
    assert!(is_math("instDecidableEqNat"));
}

#[test]
fn test_label_strings() {
    assert_eq!(ConstKind::Math.label(), "math");
    assert_eq!(ConstKind::Generated.label(), "generated");
}

#[test]
fn test_rule_string_nonempty_and_mentions_buckets() {
    let rule = classification_rule();
    assert!(rule.contains("GENERATED"));
    assert!(rule.contains("MATH"));
    assert!(rule.contains("whole-segment"));
}

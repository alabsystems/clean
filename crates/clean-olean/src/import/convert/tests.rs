// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::infer_recursor_arg_order;
use super::is_inductive_family_kind;
use crate::module::ConstantKind;
use clean_kernel::inductive::RecursorArgOrder;

/// Lock the HYBRID lazy-skip invariant: `is_inductive_family_kind` must be
/// TRUE for exactly the kinds `convert_parsed_constant`/`convert_load_constant`
/// route to a non-`Other` `ConvertedConstant` variant (Inductive/Constructor/
/// Recursor) and FALSE for every definitional kind the lazy source serves
/// (Axiom/Definition/Theorem/Opaque/Quot). If a kind moves buckets, the
/// conversion-skip filter in `load_register.rs` must move with it — this test
/// fails loudly if they ever drift.
#[test]
fn test_inductive_family_kind_matches_variant() {
    assert!(is_inductive_family_kind(&ConstantKind::Inductive));
    assert!(is_inductive_family_kind(&ConstantKind::Constructor));
    assert!(is_inductive_family_kind(&ConstantKind::Recursor));
    assert!(!is_inductive_family_kind(&ConstantKind::Axiom));
    assert!(!is_inductive_family_kind(&ConstantKind::Definition));
    assert!(!is_inductive_family_kind(&ConstantKind::Theorem));
    assert!(!is_inductive_family_kind(&ConstantKind::Opaque));
    assert!(!is_inductive_family_kind(&ConstantKind::Quot));
}

#[test]
fn test_infer_recursor_arg_order_rec_is_major_after_minors() {
    assert_eq!(
        infer_recursor_arg_order("Nat.rec"),
        RecursorArgOrder::MajorAfterMinors
    );
}

#[test]
fn test_infer_recursor_arg_order_rec_on_is_major_after_motive() {
    assert_eq!(
        infer_recursor_arg_order("Nat.recOn"),
        RecursorArgOrder::MajorAfterMotive
    );
}

#[test]
fn test_infer_recursor_arg_order_nested_rec_on_is_major_after_motive() {
    // Nested-inductive eliminators are named `T.recOn_2`, `T.recOn_3`, ...
    // and must also be recognized as the recOn layout.
    assert_eq!(
        infer_recursor_arg_order("Tree.recOn_2"),
        RecursorArgOrder::MajorAfterMotive
    );
    assert_eq!(
        infer_recursor_arg_order("Tree.recOn_3"),
        RecursorArgOrder::MajorAfterMotive
    );
}

#[test]
fn test_infer_recursor_arg_order_cases_on_is_major_after_motive() {
    // Lean-faithful casesOn layout: major premise right after the motive,
    // before the minors — same as recOn.
    assert_eq!(
        infer_recursor_arg_order("List.casesOn"),
        RecursorArgOrder::MajorAfterMotive
    );
    assert_eq!(
        infer_recursor_arg_order("Tree.casesOn_2"),
        RecursorArgOrder::MajorAfterMotive
    );
}

#[test]
fn test_infer_recursor_arg_order_brec_on_is_major_after_minors() {
    assert_eq!(
        infer_recursor_arg_order("Nat.brecOn"),
        RecursorArgOrder::MajorAfterMinors
    );
}

#[test]
fn test_infer_recursor_arg_order_below_is_major_after_minors() {
    assert_eq!(
        infer_recursor_arg_order("Nat.below"),
        RecursorArgOrder::MajorAfterMinors
    );
}

#[test]
fn test_infer_recursor_arg_order_custom_name_defaults_to_major_after_minors() {
    // A recursor whose name does not match the recOn convention defaults to
    // the standard layout. This is the documented limitation of name-based
    // inference: a custom-named recursor with MajorAfterMotive can only be
    // preserved losslessly through the CleanPayload, not the bare Lean-4
    // `.olean` body (which has no arg_order slot).
    assert_eq!(
        infer_recursor_arg_order("Foo.myEliminator"),
        RecursorArgOrder::MajorAfterMinors
    );
}

#[test]
fn test_infer_recursor_arg_order_does_not_match_recon_substring_outside_suffix() {
    // "recOnly" embeds "recOn" but is neither a `.recOn` suffix nor a
    // `.recOn_` nested variant, so it must not be misclassified.
    assert_eq!(
        infer_recursor_arg_order("Bar.recOnly"),
        RecursorArgOrder::MajorAfterMinors
    );
}

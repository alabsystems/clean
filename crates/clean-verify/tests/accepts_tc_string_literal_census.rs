// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Crystal E4's String-literal census** -- the inventory rows
//! `conv-string-literal-expansion`, `conv-iota-major-string-literal` and
//! `conv-proj-iota-string-literal` (`data/crystal_e4_conversion_inventory.json`).
//!
//! The deployed `string_lit_to_constructor` is ONE rule of both typed families,
//! `lit_string_expand`, keyed on the literal's decoded payload
//! (`src/spec/core_spec/literal_string_codec.rs`: the payload IS the character
//! list, through a bijection proved both ways) and on the admission fact
//! `StringLitAdmitIn` (the deployed default prelude's canonical records); the
//! three deployed branches that expand are DERIVED from it
//! (`src/spec/core_spec/acceptance_cdp_in/string_literal.rs`). "Proved" means
//! what the E4 census means: kernel-checked on registration, re-checked by
//! `verify_definition`, domain AND foundational axiom closure EMPTY. Near misses
//! -- a wrong character, a wrong length, a wrong constructor, a surrogate, an
//! environment without the canonical records -- are REFUSED by the kernel.

use clean_kernel::name::Name;
use clean_verify::test_utils::build_spec_with_stack;

use crate::acceptance_cdp_in_census::{assert_kernel_checked_axiom_free, type_src};

/// The codec proofs (the payload's decoding). Quote it.
const STRING_LIT_CODEC_PROOFS: usize = 8;
/// The rule's derived branches and witnesses. Quote it.
const STRING_LITERAL_PROOFS: usize = 15;

const ENV: &str = "accepts_tc_string_env";

fn list(cs: &[u32]) -> String {
    cs.iter()
        .rev()
        .fold("(@ListType.nil Nat)".to_string(), |acc, c| {
            format!("(@ListType.cons Nat {c} {acc})")
        })
}

#[test]
fn string_literal_rules_register_axiom_free_and_say_what_they_claim() {
    let spec = build_spec_with_stack();
    let codec = clean_verify::spec::STRING_LIT_CODEC_PROOF_NAMES;
    let rules = clean_verify::spec::STRING_LITERAL_PROOF_NAMES;
    assert_eq!(codec.len(), STRING_LIT_CODEC_PROOFS);
    assert_eq!(rules.len(), STRING_LITERAL_PROOFS);
    for name in codec.iter().chain(rules) {
        assert_kernel_checked_axiom_free(&spec, name);
    }
    // The decoding is a bijection, both round trips stated exactly.
    assert_eq!(
        type_src(&spec, "string_lit_code_chars"),
        "forall (n : Nat), @Eq Nat (string_lit_code (string_lit_chars n)) n"
    );
    assert_eq!(
        type_src(&spec, "string_lit_chars_code"),
        "forall (cs : ListType Nat), @Eq (ListType Nat) (string_lit_chars (string_lit_code cs)) cs"
    );
    assert_eq!(
        type_src(&spec, "string_lit_code_injective"),
        "forall (a : ListType Nat) (b : ListType Nat), @Eq Nat (string_lit_code a) (string_lit_code b) -> @Eq (ListType Nat) a b"
    );
    // Every derived branch holds at every environment carrying the admission
    // fact; the every-payload lemma covers ANY literal leaf, not only codes.
    for lemma in [
        "accepts_tc_lit_string_every_payload",
        "accepts_tc_string_lit_expansion",
        "accepts_tc_iota_major_string_literal",
        "accepts_tc_proj_string_literal",
    ] {
        let src = type_src(&spec, lemma);
        assert!(
            src.starts_with("forall (R : RedEnv) (tenv : KDeclEnv) (G : ListType CtxEntryIn)"),
            "{lemma} must hold at every environment: {src}"
        );
        assert!(
            src.contains("StringLitAdmitIn R ->"),
            "{lemma} must key on the admission fact: {src}"
        );
    }
    assert!(type_src(&spec, "accepts_tc_lit_string_every_payload")
        .contains("(literal_string n) (string_lit_expansion (string_lit_chars n))"));
    // The witnesses run at the canonical-closure fixture, never the seed, and
    // each relates two DIFFERENT terms.
    let ab = list(&[97, 98]);
    for (witness, tail) in [
        (
            "kernel_accepts_tc_in_lit_string_expand",
            format!("(literal_string (string_lit_code {ab})) (string_lit_expansion {ab})"),
        ),
        (
            "kernel_accepts_tc_in_string_lit_constructor",
            format!("(literal_string (string_lit_code {ab})) (KExpr.app (KExpr.const accepts_tc_string_mk_name (@ListType.nil Level)) (string_lit_char_list {ab}))"),
        ),
        (
            "kernel_accepts_tc_in_string_lit_proj",
            format!("(KExpr.proj literal_builtin_string_name Nat.zero (literal_string (string_lit_code {ab}))) (string_lit_char_list {ab})"),
        ),
        (
            "kernel_accepts_tc_in_lit_string_empty",
            "(literal_string Nat.zero) (string_lit_expansion (@ListType.nil Nat))".to_string(),
        ),
    ] {
        let src = type_src(&spec, witness);
        assert!(
            src.starts_with(&format!(
                "forall (tenv : KDeclEnv) (G : ListType CtxEntryIn), KernelAcceptsTcIn {ENV} tenv Bool.false G "
            )),
            "{witness} must run at {ENV}: {src}"
        );
        assert!(src.ends_with(&tail), "{witness} must state {tail}: {src}");
        assert!(!src.contains("the_red_env"), "{witness} must not be seed-pinned");
    }
    assert!(type_src(&spec, "kernel_accepts_tc_in_string_lit_iota")
        .contains("(literal_string (string_lit_code (@ListType.cons Nat 97"));
    assert_eq!(
        type_src(&spec, "accepts_tc_string_admit"),
        format!("StringLitAdmitIn {ENV}")
    );
    // The rule keys on REFLECTED names: each alias is the validated table's atom.
    for (alias, real) in clean_verify::spec::ACCEPTS_TC_STRING_NAME_ALIASES {
        let atom = clean_verify::red_env_reflect::committed_name_atom(real)
            .unwrap_or_else(|e| panic!("{real} must be interned: {e}"));
        let value = spec
            .definitions()
            .get(*alias)
            .and_then(|d| d.value_src.clone())
            .unwrap_or_else(|| panic!("{alias} must be registered with a value"));
        assert_eq!(
            value.trim(),
            format!("def {alias} : Name := {atom}"),
            "{alias} must be the reflected {real}"
        );
    }
    // The admission fact pins the canonical records REFLECTED from the deployed
    // default prelude: String.ofList's body applies the String.mk atom.
    let mk_atom = clean_verify::red_env_reflect::committed_name_atom("String.mk")
        .expect("String.mk is interned");
    let of_list_body = spec
        .definitions()
        .get("accepts_tc_string_of_list_body")
        .and_then(|d| d.value_src.clone())
        .expect("the canonical String.ofList body is registered");
    assert!(
        of_list_body.contains(&format!("(KExpr.const {mk_atom} (@ListType.nil Level))")),
        "the canonical String.ofList body must build String.mk: {of_list_body}"
    );
    for inductive in ["StringLitAdmitIn", "KernelAcceptsTcIn", "TypingTcIn"] {
        assert!(
            spec.env()
                .get_const(&Name::from_string(inductive))
                .is_some(),
            "{inductive} must be registered"
        );
    }
}

/// Near misses the kernel must refuse: each by a type mismatch, leaving no
/// trace.
#[test]
fn string_literal_witnesses_refuse_near_misses() {
    let mut spec = build_spec_with_stack();
    for (name, source) in forged() {
        let kernel_name = Name::from_string(&name);
        assert!(spec.env().get_const(&kernel_name).is_none(), "{name}");
        let error = spec
            .add_recursive_def(&source, "Forged String-literal caller: must not register.")
            .expect_err("a forged caller must be refused");
        assert!(
            format!("{error:?}").contains("mismatch"),
            "{name} must be refused by a type mismatch, got {error:?}"
        );
        assert!(spec.env().get_const(&kernel_name).is_none(), "{name}");
        assert!(!spec.definitions().contains_key(&name), "{name}");
    }
}

fn forged() -> Vec<(String, String)> {
    let ab = list(&[97, 98]);
    let lit = format!("(literal_string (string_lit_code {ab}))");
    let fa = "forall (tenv : KDeclEnv) (G : ListType CtxEntryIn)";
    let fun = "fun (tenv : KDeclEnv) (G : ListType CtxEntryIn)";
    let arm = |cs: &str| {
        format!(
            "(@KernelAcceptsTcIn.lit_string_expand {ENV} tenv G {cs} accepts_tc_string_admit (@Eq.refl Bool Bool.true))"
        )
    };
    let mk = "(KExpr.const accepts_tc_string_mk_name (@ListType.nil Level))";
    let proj =
        |subject: &str| format!("(KExpr.proj literal_builtin_string_name Nat.zero {subject})");
    let motive = "(KExpr.lam (KExpr.const literal_builtin_string_name (@ListType.nil Level)) (KExpr.app (KExpr.const accepts_tc_list_name (@ListType.cons Level Level.zero (@ListType.nil Level))) (KExpr.const accepts_tc_char_name (@ListType.nil Level))))";
    let minor = "(KExpr.lam accepts_tc_string_of_list_dom (KExpr.bvar Nat.zero))";
    let us = "(@ListType.cons Level (Level.succ Level.zero) (@ListType.nil Level))";
    let rec_f = format!(
        "(KExpr.app (KExpr.app (KExpr.const accepts_tc_string_rec_name {us}) {motive}) {minor})"
    );
    let contractum = |cs: &str| {
        format!("(KExpr.app (KExpr.app (KExpr.app (recursor_rhs_instance (recmeta_signature accepts_tc_string_rec_meta) (recrule_rhs accepts_tc_string_rec_mk_rule) {us}) {motive}) {minor}) (string_lit_char_list {cs}))")
    };
    let admit_premises = "(@Eq.refl (OptionType KDefSig) (@OptionType.some KDefSig accepts_tc_string_of_list_def)) (@Eq.refl (OptionType KDefSig) (@OptionType.some KDefSig accepts_tc_char_of_nat_def)) (@Eq.refl (OptionType KCtorMeta) (@OptionType.some KCtorMeta accepts_tc_string_mk_meta))";
    let identity_env = format!(
        "(RedEnv.mk (red_rec {ENV}) (DefEnv.addDef (red_def {ENV}) accepts_tc_string_of_list_name (KDefSig.mk (kdef_signature accepts_tc_string_of_list_def) (KExpr.lam accepts_tc_string_of_list_dom (KExpr.bvar Nat.zero)))) (red_ind_ctor {ENV}))"
    );
    let rows = [
        // The rule: a wrong character, a wrong length, a wrong constructor.
        (
            "accepts_tc_forged_string_wrong_char",
            format!("{fa}, KernelAcceptsTcIn {ENV} tenv Bool.false G {lit} (string_lit_expansion {})", list(&[97, 99])),
            format!("{fun} => {}", arm(&ab)),
        ),
        (
            "accepts_tc_forged_string_wrong_length",
            format!("{fa}, KernelAcceptsTcIn {ENV} tenv Bool.false G {lit} (string_lit_expansion {})", list(&[97])),
            format!("{fun} => {}", arm(&ab)),
        ),
        (
            "accepts_tc_forged_string_wrong_constructor",
            format!("{fa}, KernelAcceptsTcIn {ENV} tenv Bool.false G {lit} (KExpr.app {mk} (string_lit_char_list {ab}))"),
            format!("{fun} => {}", arm(&ab)),
        ),
        // The rule's range premise: a surrogate is not a scalar value.
        (
            "accepts_tc_forged_string_surrogate",
            format!(
                "{fa}, KernelAcceptsTcIn {ENV} tenv Bool.false G (literal_string (string_lit_code {s})) (string_lit_expansion {s})",
                s = list(&[55296])
            ),
            format!("{fun} => {}", arm(&list(&[55296]))),
        ),
        // The admission fact: the reflected seed has no canonical String.ofList,
        // and an identity String.ofList is not the canonical record.
        (
            "accepts_tc_forged_string_admit_seed",
            "StringLitAdmitIn kernel_core_red_env".to_string(),
            format!("@StringLitAdmitIn.mk kernel_core_red_env {admit_premises}"),
        ),
        (
            "accepts_tc_forged_string_admit_identity_of_list",
            format!("StringLitAdmitIn {identity_env}"),
            format!("@StringLitAdmitIn.mk {identity_env} {admit_premises}"),
        ),
        // The decoding: two lists never share a payload.
        (
            "accepts_tc_forged_string_code_collision",
            format!("@Eq Nat (string_lit_code {}) (string_lit_code {})", list(&[1]), list(&[0, 0])),
            format!("@Eq.refl Nat (string_lit_code {})", list(&[1])),
        ),
        // The derived branches, each at its witness: a constructor form with the
        // characters swapped, a projection with a character dropped.
        (
            "accepts_tc_forged_string_constructor_order",
            format!("{fa}, KernelAcceptsTcIn {ENV} tenv Bool.false G {lit} (KExpr.app {mk} (string_lit_char_list {}))", list(&[98, 97])),
            format!("{fun} => kernel_accepts_tc_in_string_lit_constructor tenv G"),
        ),
        (
            "accepts_tc_forged_string_proj_length",
            format!("{fa}, KernelAcceptsTcIn {ENV} tenv Bool.false G {} (string_lit_char_list {})", proj(&lit), list(&[97])),
            format!("{fun} => kernel_accepts_tc_in_string_lit_proj tenv G"),
        ),
        // The recursor major: the minor fed a wrong character.
        (
            "accepts_tc_forged_string_iota_char",
            format!("{fa}, KernelAcceptsTcIn {ENV} tenv Bool.false G (KExpr.app {rec_f} {lit}) {}", contractum(&list(&[97, 99]))),
            format!("{fun} => kernel_accepts_tc_in_string_lit_iota tenv G"),
        ),
        // Every payload: payload 0 is the EMPTY string, not "\0".
        (
            "accepts_tc_forged_string_empty_payload",
            format!("{fa}, KernelAcceptsTcIn {ENV} tenv Bool.false G (literal_string Nat.zero) (string_lit_expansion {})", list(&[0])),
            format!("{fun} => kernel_accepts_tc_in_lit_string_empty tenv G"),
        ),
    ];
    rows.into_iter()
        .map(|(name, ty, value)| (name.to_string(), format!("def {name} : {ty} := {value}")))
        .collect()
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Crystal E4d's census** -- the inventory rows `conv-native-nat`,
//! `conv-native-int` and `conv-iota-k-like`
//! (`data/crystal_e4_conversion_inventory.json`).
//!
//! The native Nat / Int folds are DERIVED `KernelAcceptsTcIn` conversions, one
//! lemma per fold key, over any environment holding the key's canonical closure
//! (`src/spec/core_spec/acceptance_cdp_in/native_nat.rs`); K-like reduction is
//! the `k_like` rule of both typed families, keyed on the admission fact
//! `RecKAdmitIn`. "Proved" means what the E4 census means: kernel-checked on
//! registration, re-checked by `verify_definition`, domain AND foundational
//! axiom closure EMPTY. Forged K admissions are REFUSED by the kernel.

use clean_kernel::name::Name;
use clean_verify::test_utils::build_spec_with_stack;

use crate::acceptance_cdp_in_census::{assert_kernel_checked_axiom_free, type_src};

/// The native Nat / Int fold proofs this census mints (E4d). Quote it.
const NATIVE_NAT_PROOFS: usize = 102;

/// Each deployed `reduce_nat` fold key the specification's world admits, with
/// the lemma that derives its fold.
const NATIVE_NAT_FOLD_LEMMAS: &[(&str, &str)] = &[
    ("Nat.succ", "kernel_accepts_tc_in_nat_succ_fold"),
    ("Nat.pred", "kernel_accepts_tc_in_nat_pred_fold"),
    ("Nat.add", "kernel_accepts_tc_in_nat_add_fold"),
    ("Nat.sub", "kernel_accepts_tc_in_nat_sub_fold"),
    ("Nat.mul", "kernel_accepts_tc_in_nat_mul_fold"),
    ("Nat.pow", "kernel_accepts_tc_in_nat_pow_fold"),
    ("Nat.shiftLeft", "kernel_accepts_tc_in_nat_shiftleft_fold"),
    ("Nat.beq", "kernel_accepts_tc_in_nat_beq_fold"),
    ("Nat.ble", "kernel_accepts_tc_in_nat_ble_fold"),
    ("Nat.blt", "kernel_accepts_tc_in_nat_blt_fold"),
    ("Nat.div", "kernel_accepts_tc_in_nat_div_fold"),
    ("Nat.mod", "kernel_accepts_tc_in_nat_mod_fold"),
    ("Nat.land", "kernel_accepts_tc_in_nat_land_fold"),
    ("Nat.lor", "kernel_accepts_tc_in_nat_lor_fold"),
    ("Nat.xor", "kernel_accepts_tc_in_nat_xor_fold"),
    ("Nat.shiftRight", "kernel_accepts_tc_in_nat_shiftright_fold"),
];

/// Each deployed `reduce_int` fold key, with the lemma that derives its fold
/// over constructor-applied literals (and `Int.neg`, the closure member the
/// subtraction reaches).
const NATIVE_INT_FOLD_LEMMAS: &[(&str, &str)] = &[
    ("Int.add", "kernel_accepts_tc_in_int_add_fold"),
    ("Int.sub", "kernel_accepts_tc_in_int_sub_fold"),
    ("Int.mul", "kernel_accepts_tc_in_int_mul_fold"),
    ("Int.neg", "kernel_accepts_tc_in_int_neg_fold"),
    ("Int.toNat", "kernel_accepts_tc_in_int_tonat_fold"),
];

/// Every native-fold proof is kernel-checked with an empty closure, each fold
/// key's lemma folds the reflected head over R's definition of it, and the K
/// witnesses say what the inventory cites.
#[test]
fn native_folds_and_k_like_register_axiom_free_and_say_what_they_claim() {
    let spec = build_spec_with_stack();
    let native = clean_verify::spec::NATIVE_NAT_PROOF_NAMES;
    assert_eq!(native.len(), NATIVE_NAT_PROOFS);
    for name in native {
        assert_kernel_checked_axiom_free(&spec, name);
    }
    for (op, lemma) in NATIVE_NAT_FOLD_LEMMAS.iter().chain(NATIVE_INT_FOLD_LEMMAS) {
        let src = type_src(&spec, lemma);
        assert!(
            src.starts_with("forall (R : RedEnv) (tenv : KDeclEnv) (G : ListType CtxEntryIn)"),
            "{lemma} must hold at every environment carrying the canonical closure: {src}"
        );
        let atom = clean_verify::red_env_reflect::committed_name_atom(op)
            .unwrap_or_else(|e| panic!("{op} must be interned: {e}"));
        assert!(
            src.contains(&format!("(KExpr.const {atom} (ListType.nil Level))")),
            "{lemma} must fold the reflected {op}: {src}"
        );
        // `Nat.succ` is a constructor: its fold IS the literal rule, keyed on
        // no definition. Every other head keys on R's definition of it.
        assert_eq!(
            src.contains("(kdef_value_at (red_def R) "),
            *op != "Nat.succ",
            "{lemma} must key on R's definition of the head exactly when it has one: {src}"
        );
    }
    // The Int folds read Int.rec's rules off R, and the predecessor fold keys on
    // Nat.rec and Int.rec together (the deployed reduce_int_pred_fold pins both).
    let int_rec = clean_verify::red_env_reflect::committed_name_atom("Int.rec")
        .unwrap_or_else(|e| panic!("Int.rec must be interned: {e}"));
    for lemma in NATIVE_INT_FOLD_LEMMAS
        .iter()
        .map(|(_, lemma)| *lemma)
        .chain(["kernel_accepts_tc_in_int_pred_fold"])
    {
        let src = type_src(&spec, lemma);
        assert!(
            src.contains(&format!("(recmeta_for (red_rec R) {int_rec})")),
            "{lemma} must read Int.rec's metadata off R: {src}"
        );
    }
    // K-like reduction: the admission fact is a fact about the reflected seed's
    // own K recursor too (Eq.rec), not only about the fixture.
    assert_eq!(
        type_src(&spec, "typing_tc_in_k_like_is_proof_irrel"),
        "forall (R : RedEnv) (tenv : KDeclEnv) (G : ListType CtxEntryIn) (major : KExpr) (W : KExpr) (ctor : KExpr) (S : KExpr), \
         TypingTcIn R tenv Bool.true G major W -> TypingTcIn R tenv Bool.true G ctor W -> \
         TypingTcIn R tenv Bool.true G W S -> TypingTcIn R tenv Bool.false G S (KExpr.sort Level.zero) -> \
         TypingTcIn R tenv Bool.false G major ctor"
    );
    for witness in ["kernel_accepts_tc_in_k_like", "accepts_k_iota_witness"] {
        let src = type_src(&spec, witness);
        assert!(
            src.contains("accepts_k_env"),
            "{witness} must run at accepts_k_env: {src}"
        );
        assert!(
            src.contains("(KExpr.bvar Nat.zero)"),
            "{witness} must start from the hypothesis #0"
        );
    }
}

/// The admission fact claimed at a recursor whose K flag is 0, at an inductive
/// living in `Type`, and at a constructor with a field: each is refused by a
/// type mismatch at exactly that guard and leaves no trace.
#[test]
fn k_admission_refuses_forged_callers() {
    let mut spec = build_spec_with_stack();
    for &(name, source) in FORGED_K {
        let kernel_name = Name::from_string(name);
        assert!(spec.env().get_const(&kernel_name).is_none(), "{name}");
        let error = spec
            .add_recursive_def(source, "Forged RecKAdmitIn caller: must not register.")
            .expect_err("a forged caller must be refused");
        assert!(
            format!("{error:?}").contains("mismatch"),
            "{name} must be refused by a type mismatch, got {error:?}"
        );
        assert!(spec.env().get_const(&kernel_name).is_none(), "{name}");
        assert!(!spec.definitions().contains_key(name), "{name}");
    }
}

/// E4n near misses: each registered-reducer fold lemma restated with a WRONG
/// right side (the value the reducer does not compute) keeps its checked proof
/// and must be refused by the kernel, so the agreement the lemma states is not
/// vacuous. `Nat.blt a b` is not `Nat.ble a b`, and `Int.toNat i` is not its
/// successor.
#[test]
fn registered_reducer_folds_refuse_a_wrong_result() {
    let mut spec = build_spec_with_stack();
    for (lemma, right, wrong) in [
        (
            "kernel_accepts_tc_in_nat_blt_fold",
            "(accepts_tc_bool_lit (Nat.blt a b))",
            "(accepts_tc_bool_lit (Nat.ble a b))",
        ),
        (
            "kernel_accepts_tc_in_int_tonat_fold",
            "(literal_nat (Int.toNat i))",
            "(literal_nat (Nat.succ (Int.toNat i)))",
        ),
    ] {
        let def = spec
            .definitions()
            .get(lemma)
            .unwrap_or_else(|| panic!("{lemma} must be registered"))
            .clone();
        assert_eq!(
            def.type_src.matches(right).count(),
            1,
            "{lemma} must state its result once as {right}: {}",
            def.type_src
        );
        let forged = format!("{lemma}_near_miss");
        let error = spec
            .add_definition(clean_verify::spec::SpecDefinition {
                name: forged.clone(),
                type_src: def.type_src.replace(right, wrong),
                value_src: def.value_src.clone(),
                is_axiom: false,
                description: "E4n near miss: must not register.".to_string(),
                category: clean_verify::spec::AxiomCategory::DerivedLemma,
                proof_status: clean_verify::spec::ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: None,
                axiom_deps: std::collections::HashSet::new(),
            })
            .expect_err("a fold lemma restated at the wrong result must be refused");
        assert!(
            format!("{error:?}").contains("mismatch"),
            "{forged} must be refused by a type mismatch, got {error:?}"
        );
        assert!(
            spec.env().get_const(&Name::from_string(&forged)).is_none(),
            "{forged}"
        );
    }
}

/// Kernel-refused K admissions (one guard each).
const FORGED_K: &[(&str, &str)] = &[
    (
        "accepts_tc_forged_k_unflagged",
        r"def accepts_tc_forged_k_unflagged : RecKAdmitIn (RedEnv.mk (RecEnv.addRec RecEnv.empty accepts_k_rn (RecMeta.mk Nat.zero (Nat.succ Nat.zero) (Nat.succ Nat.zero) Nat.zero Bool.true accepts_k_rec_sig Nat.zero) (RecRules.cons (RecRule.mk accepts_k_cn Nat.zero accepts_k_rhs) RecRules.nil)) DefEnv.empty (IndCtorEnv.addCtor (IndCtorEnv.addInd IndCtorEnv.empty Name.anonymous accepts_k_ind_meta) accepts_k_cn accepts_k_ctor_meta)) accepts_k_rn Name.anonymous (RecMeta.mk Nat.zero (Nat.succ Nat.zero) (Nat.succ Nat.zero) Nat.zero Bool.true accepts_k_rec_sig Nat.zero) accepts_k_cn :=
RecKAdmitIn.mk (RedEnv.mk (RecEnv.addRec RecEnv.empty accepts_k_rn (RecMeta.mk Nat.zero (Nat.succ Nat.zero) (Nat.succ Nat.zero) Nat.zero Bool.true accepts_k_rec_sig Nat.zero) (RecRules.cons (RecRule.mk accepts_k_cn Nat.zero accepts_k_rhs) RecRules.nil)) DefEnv.empty (IndCtorEnv.addCtor (IndCtorEnv.addInd IndCtorEnv.empty Name.anonymous accepts_k_ind_meta) accepts_k_cn accepts_k_ctor_meta)) accepts_k_rn Name.anonymous (RecMeta.mk Nat.zero (Nat.succ Nat.zero) (Nat.succ Nat.zero) Nat.zero Bool.true accepts_k_rec_sig Nat.zero) accepts_k_cn accepts_k_rhs accepts_k_ctor_meta accepts_k_ind_meta
  (Eq.refl (OptionType RecMeta) (OptionType.some RecMeta (RecMeta.mk Nat.zero (Nat.succ Nat.zero) (Nat.succ Nat.zero) Nat.zero Bool.true accepts_k_rec_sig Nat.zero)))
  (Eq.refl Nat (Nat.succ Nat.zero))
  (Eq.refl (OptionType RecRules) (OptionType.some RecRules (RecRules.cons (RecRule.mk accepts_k_cn Nat.zero accepts_k_rhs) RecRules.nil)))
  (Eq.refl (OptionType KCtorMeta) (OptionType.some KCtorMeta accepts_k_ctor_meta))
  (Eq.refl Name Name.anonymous)
  (Eq.refl Nat Nat.zero)
  (Eq.refl (OptionType KIndMeta) (OptionType.some KIndMeta accepts_k_ind_meta))
  (Eq.refl (ListType Name) (ListType.cons Name accepts_k_cn (ListType.nil Name)))
  (Eq.refl (ListType Name) (ListType.cons Name Name.anonymous (ListType.nil Name)))
  (Eq.refl Bool Bool.true)",
    ),
    (
        "accepts_tc_forged_k_type_valued",
        r"def accepts_tc_forged_k_type_valued : RecKAdmitIn (RedEnv.mk (RecEnv.addRec RecEnv.empty accepts_k_rn accepts_k_rec_meta (RecRules.cons (RecRule.mk accepts_k_cn Nat.zero accepts_k_rhs) RecRules.nil)) DefEnv.empty (IndCtorEnv.addCtor (IndCtorEnv.addInd IndCtorEnv.empty Name.anonymous (KIndMeta.mk (KConstSig.mk (ListType.nil Name) (KExpr.sort (Level.succ Level.zero))) Nat.zero Nat.zero (ListType.cons Name accepts_k_cn (ListType.nil Name)) (ListType.cons Name Name.anonymous (ListType.nil Name)))) accepts_k_cn accepts_k_ctor_meta)) accepts_k_rn Name.anonymous accepts_k_rec_meta accepts_k_cn :=
RecKAdmitIn.mk (RedEnv.mk (RecEnv.addRec RecEnv.empty accepts_k_rn accepts_k_rec_meta (RecRules.cons (RecRule.mk accepts_k_cn Nat.zero accepts_k_rhs) RecRules.nil)) DefEnv.empty (IndCtorEnv.addCtor (IndCtorEnv.addInd IndCtorEnv.empty Name.anonymous (KIndMeta.mk (KConstSig.mk (ListType.nil Name) (KExpr.sort (Level.succ Level.zero))) Nat.zero Nat.zero (ListType.cons Name accepts_k_cn (ListType.nil Name)) (ListType.cons Name Name.anonymous (ListType.nil Name)))) accepts_k_cn accepts_k_ctor_meta)) accepts_k_rn Name.anonymous accepts_k_rec_meta accepts_k_cn accepts_k_rhs accepts_k_ctor_meta (KIndMeta.mk (KConstSig.mk (ListType.nil Name) (KExpr.sort (Level.succ Level.zero))) Nat.zero Nat.zero (ListType.cons Name accepts_k_cn (ListType.nil Name)) (ListType.cons Name Name.anonymous (ListType.nil Name)))
  (Eq.refl (OptionType RecMeta) (OptionType.some RecMeta accepts_k_rec_meta))
  (Eq.refl Nat (Nat.succ Nat.zero))
  (Eq.refl (OptionType RecRules) (OptionType.some RecRules (RecRules.cons (RecRule.mk accepts_k_cn Nat.zero accepts_k_rhs) RecRules.nil)))
  (Eq.refl (OptionType KCtorMeta) (OptionType.some KCtorMeta accepts_k_ctor_meta))
  (Eq.refl Name Name.anonymous)
  (Eq.refl Nat Nat.zero)
  (Eq.refl (OptionType KIndMeta) (OptionType.some KIndMeta (KIndMeta.mk (KConstSig.mk (ListType.nil Name) (KExpr.sort (Level.succ Level.zero))) Nat.zero Nat.zero (ListType.cons Name accepts_k_cn (ListType.nil Name)) (ListType.cons Name Name.anonymous (ListType.nil Name)))))
  (Eq.refl (ListType Name) (ListType.cons Name accepts_k_cn (ListType.nil Name)))
  (Eq.refl (ListType Name) (ListType.cons Name Name.anonymous (ListType.nil Name)))
  (Eq.refl Bool Bool.true)",
    ),
    (
        "accepts_tc_forged_k_ctor_field",
        r"def accepts_tc_forged_k_ctor_field : RecKAdmitIn (RedEnv.mk (RecEnv.addRec RecEnv.empty accepts_k_rn accepts_k_rec_meta (RecRules.cons (RecRule.mk accepts_k_cn Nat.zero accepts_k_rhs) RecRules.nil)) DefEnv.empty (IndCtorEnv.addCtor (IndCtorEnv.addInd IndCtorEnv.empty Name.anonymous accepts_k_ind_meta) accepts_k_cn (KCtorMeta.mk (KConstSig.mk (ListType.nil Name) accepts_k_type) Name.anonymous Nat.zero (Nat.succ Nat.zero) Nat.zero))) accepts_k_rn Name.anonymous accepts_k_rec_meta accepts_k_cn :=
RecKAdmitIn.mk (RedEnv.mk (RecEnv.addRec RecEnv.empty accepts_k_rn accepts_k_rec_meta (RecRules.cons (RecRule.mk accepts_k_cn Nat.zero accepts_k_rhs) RecRules.nil)) DefEnv.empty (IndCtorEnv.addCtor (IndCtorEnv.addInd IndCtorEnv.empty Name.anonymous accepts_k_ind_meta) accepts_k_cn (KCtorMeta.mk (KConstSig.mk (ListType.nil Name) accepts_k_type) Name.anonymous Nat.zero (Nat.succ Nat.zero) Nat.zero))) accepts_k_rn Name.anonymous accepts_k_rec_meta accepts_k_cn accepts_k_rhs (KCtorMeta.mk (KConstSig.mk (ListType.nil Name) accepts_k_type) Name.anonymous Nat.zero (Nat.succ Nat.zero) Nat.zero) accepts_k_ind_meta
  (Eq.refl (OptionType RecMeta) (OptionType.some RecMeta accepts_k_rec_meta))
  (Eq.refl Nat (Nat.succ Nat.zero))
  (Eq.refl (OptionType RecRules) (OptionType.some RecRules (RecRules.cons (RecRule.mk accepts_k_cn Nat.zero accepts_k_rhs) RecRules.nil)))
  (Eq.refl (OptionType KCtorMeta) (OptionType.some KCtorMeta (KCtorMeta.mk (KConstSig.mk (ListType.nil Name) accepts_k_type) Name.anonymous Nat.zero (Nat.succ Nat.zero) Nat.zero)))
  (Eq.refl Name Name.anonymous)
  (Eq.refl Nat Nat.zero)
  (Eq.refl (OptionType KIndMeta) (OptionType.some KIndMeta accepts_k_ind_meta))
  (Eq.refl (ListType Name) (ListType.cons Name accepts_k_cn (ListType.nil Name)))
  (Eq.refl (ListType Name) (ListType.cons Name Name.anonymous (ListType.nil Name)))
  (Eq.refl Bool Bool.true)",
    ),
];

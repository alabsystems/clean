// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::DeclarationInput;

pub(super) const DECLARATIONS: &[DeclarationInput] = &[
    DeclarationInput::Data(
        "ict_append",
        r"forall (base updates : IndCtorEnv), IndCtorEnv",
        r"fun (base updates : IndCtorEnv) => IndCtorEnv.rec
 (fun (_s : IndCtorEnv) => IndCtorEnv) base
 (fun (_tail : IndCtorEnv) (n : Name) (im : KIndMeta) (ih : IndCtorEnv) => IndCtorEnv.addInd ih n im)
 (fun (_tail : IndCtorEnv) (n : Name) (cm : KCtorMeta) (ih : IndCtorEnv) => IndCtorEnv.addCtor ih n cm) updates",
    ),
    DeclarationInput::Data(
        "ict_has_name_b",
        r"forall (updates : IndCtorEnv) (q : Name), Bool",
        r"fun (updates : IndCtorEnv) => IndCtorEnv.rec
 (fun (_s : IndCtorEnv) => Name -> Bool)
 (fun (_q : Name) => Bool.false)
 (fun (_tail : IndCtorEnv) (n : Name) (_im : KIndMeta) (ih : Name -> Bool) (q : Name) => Bool.rec (fun (_b : Bool) => Bool) (ih q) Bool.true (name_eqb n q))
 (fun (_tail : IndCtorEnv) (n : Name) (_cm : KCtorMeta) (ih : Name -> Bool) (q : Name) => Bool.rec (fun (_b : Bool) => Bool) (ih q) Bool.true (name_eqb n q)) updates",
    ),
    DeclarationInput::Proof(
        "ict_kind_append",
        r"forall (updates base : IndCtorEnv) (q : Name), Eq (OptionType KIndMeta) (kind_for (ict_append base updates) q) (Bool.rec (fun (_b : Bool) => (OptionType KIndMeta)) (kind_for base q) (kind_for updates q) (ict_has_name_b updates q))",
        r"fun (updates : IndCtorEnv) => IndCtorEnv.rec
 (fun (s : IndCtorEnv) => forall (base : IndCtorEnv) (q : Name), Eq (OptionType KIndMeta) (kind_for (ict_append base s) q) (Bool.rec (fun (_b : Bool) => (OptionType KIndMeta)) (kind_for base q) (kind_for s q) (ict_has_name_b s q)))
 (fun (base : IndCtorEnv) (q : Name) => Eq.refl (OptionType KIndMeta) (kind_for base q))
 (fun (tail : IndCtorEnv) (n : Name) (im : KIndMeta)
 (ih : forall (base : IndCtorEnv) (q : Name), Eq (OptionType KIndMeta) (kind_for (ict_append base tail) q) (Bool.rec (fun (_b : Bool) => (OptionType KIndMeta)) (kind_for base q) (kind_for tail q) (ict_has_name_b tail q)))
 (base : IndCtorEnv) (q : Name) => Bool.rec
  (fun (b : Bool) => Eq (OptionType KIndMeta) (Bool.rec (fun (_b : Bool) => (OptionType KIndMeta)) (kind_for (ict_append base tail) q) (OptionType.some KIndMeta im) b) (Bool.rec (fun (_b : Bool) => (OptionType KIndMeta)) (kind_for base q) (Bool.rec (fun (_b : Bool) => (OptionType KIndMeta)) (kind_for tail q) (OptionType.some KIndMeta im) b) (Bool.rec (fun (_b : Bool) => Bool) (ict_has_name_b tail q) Bool.true b)))
  (ih base q) (Eq.refl (OptionType KIndMeta) (OptionType.some KIndMeta im)) (name_eqb n q))
 (fun (tail : IndCtorEnv) (n : Name) (cm : KCtorMeta)
 (ih : forall (base : IndCtorEnv) (q : Name), Eq (OptionType KIndMeta) (kind_for (ict_append base tail) q) (Bool.rec (fun (_b : Bool) => (OptionType KIndMeta)) (kind_for base q) (kind_for tail q) (ict_has_name_b tail q)))
 (base : IndCtorEnv) (q : Name) => Bool.rec
  (fun (b : Bool) => Eq (OptionType KIndMeta) (Bool.rec (fun (_b : Bool) => (OptionType KIndMeta)) (kind_for (ict_append base tail) q) (OptionType.none KIndMeta) b) (Bool.rec (fun (_b : Bool) => (OptionType KIndMeta)) (kind_for base q) (Bool.rec (fun (_b : Bool) => (OptionType KIndMeta)) (kind_for tail q) (OptionType.none KIndMeta) b) (Bool.rec (fun (_b : Bool) => Bool) (ict_has_name_b tail q) Bool.true b)))
  (ih base q) (Eq.refl (OptionType KIndMeta) (OptionType.none KIndMeta)) (name_eqb n q)) updates",
    ),
    DeclarationInput::Proof(
        "ict_kind_append_fresh",
        r"forall (updates base : IndCtorEnv) (q : Name), Eq Bool (ict_has_name_b updates q) Bool.false -> Eq (OptionType KIndMeta) (kind_for (ict_append base updates) q) (kind_for base q)",
        r"fun (updates base : IndCtorEnv) (q : Name) (branch : Eq Bool (ict_has_name_b updates q) Bool.false) =>
 Eq.trans (OptionType KIndMeta) (kind_for (ict_append base updates) q) (Bool.rec (fun (_b : Bool) => (OptionType KIndMeta)) (kind_for base q) (kind_for updates q) (ict_has_name_b updates q)) (kind_for base q)
  (ict_kind_append updates base q)
  (Eq.cong Bool (OptionType KIndMeta) (fun (b : Bool) => (Bool.rec (fun (_b : Bool) => (OptionType KIndMeta)) (kind_for base q) (kind_for updates q) b)) (ict_has_name_b updates q) Bool.false branch)",
    ),
    DeclarationInput::Proof(
        "ict_kind_append_seen",
        r"forall (updates base : IndCtorEnv) (q : Name), Eq Bool (ict_has_name_b updates q) Bool.true -> Eq (OptionType KIndMeta) (kind_for (ict_append base updates) q) (kind_for updates q)",
        r"fun (updates base : IndCtorEnv) (q : Name) (branch : Eq Bool (ict_has_name_b updates q) Bool.true) =>
 Eq.trans (OptionType KIndMeta) (kind_for (ict_append base updates) q) (Bool.rec (fun (_b : Bool) => (OptionType KIndMeta)) (kind_for base q) (kind_for updates q) (ict_has_name_b updates q)) (kind_for updates q)
  (ict_kind_append updates base q)
  (Eq.cong Bool (OptionType KIndMeta) (fun (b : Bool) => (Bool.rec (fun (_b : Bool) => (OptionType KIndMeta)) (kind_for base q) (kind_for updates q) b)) (ict_has_name_b updates q) Bool.true branch)",
    ),
    DeclarationInput::Proof(
        "ict_kind_add_ind_same",
        r"forall (base : IndCtorEnv) (n : Name) (im : KIndMeta), Eq (OptionType KIndMeta) (kind_for (IndCtorEnv.addInd base n im) n) (OptionType.some KIndMeta im)",
        r"fun (base : IndCtorEnv) (n : Name) (im : KIndMeta) =>
 Eq.cong Bool (OptionType KIndMeta) (fun (b : Bool) => (Bool.rec (fun (_b : Bool) => (OptionType KIndMeta)) (kind_for base n) (OptionType.some KIndMeta im) b))
  (name_eqb n n) Bool.true (name_eqb_refl n)",
    ),
    DeclarationInput::Proof(
        "ict_kind_add_ind_other",
        r"forall (base : IndCtorEnv) (n q : Name) (im : KIndMeta), Eq Bool (name_eqb n q) Bool.false -> Eq (OptionType KIndMeta) (kind_for (IndCtorEnv.addInd base n im) q) (kind_for base q)",
        r"fun (base : IndCtorEnv) (n q : Name) (im : KIndMeta) (different : Eq Bool (name_eqb n q) Bool.false) =>
 Eq.cong Bool (OptionType KIndMeta) (fun (b : Bool) => (Bool.rec (fun (_b : Bool) => (OptionType KIndMeta)) (kind_for base q) (OptionType.some KIndMeta im) b))
  (name_eqb n q) Bool.false different",
    ),
    DeclarationInput::Proof(
        "ict_kind_add_ctor_same",
        r"forall (base : IndCtorEnv) (n : Name) (cm : KCtorMeta), Eq (OptionType KIndMeta) (kind_for (IndCtorEnv.addCtor base n cm) n) (OptionType.none KIndMeta)",
        r"fun (base : IndCtorEnv) (n : Name) (cm : KCtorMeta) =>
 Eq.cong Bool (OptionType KIndMeta) (fun (b : Bool) => (Bool.rec (fun (_b : Bool) => (OptionType KIndMeta)) (kind_for base n) (OptionType.none KIndMeta) b))
  (name_eqb n n) Bool.true (name_eqb_refl n)",
    ),
    DeclarationInput::Proof(
        "ict_kind_add_ctor_other",
        r"forall (base : IndCtorEnv) (n q : Name) (cm : KCtorMeta), Eq Bool (name_eqb n q) Bool.false -> Eq (OptionType KIndMeta) (kind_for (IndCtorEnv.addCtor base n cm) q) (kind_for base q)",
        r"fun (base : IndCtorEnv) (n q : Name) (cm : KCtorMeta) (different : Eq Bool (name_eqb n q) Bool.false) =>
 Eq.cong Bool (OptionType KIndMeta) (fun (b : Bool) => (Bool.rec (fun (_b : Bool) => (OptionType KIndMeta)) (kind_for base q) (OptionType.none KIndMeta) b))
  (name_eqb n q) Bool.false different",
    ),
    DeclarationInput::Proof(
        "ict_ctor_append",
        r"forall (updates base : IndCtorEnv) (q : Name), Eq (OptionType KCtorMeta) (kctor_for (ict_append base updates) q) (Bool.rec (fun (_b : Bool) => (OptionType KCtorMeta)) (kctor_for base q) (kctor_for updates q) (ict_has_name_b updates q))",
        r"fun (updates : IndCtorEnv) => IndCtorEnv.rec
 (fun (s : IndCtorEnv) => forall (base : IndCtorEnv) (q : Name), Eq (OptionType KCtorMeta) (kctor_for (ict_append base s) q) (Bool.rec (fun (_b : Bool) => (OptionType KCtorMeta)) (kctor_for base q) (kctor_for s q) (ict_has_name_b s q)))
 (fun (base : IndCtorEnv) (q : Name) => Eq.refl (OptionType KCtorMeta) (kctor_for base q))
 (fun (tail : IndCtorEnv) (n : Name) (im : KIndMeta)
 (ih : forall (base : IndCtorEnv) (q : Name), Eq (OptionType KCtorMeta) (kctor_for (ict_append base tail) q) (Bool.rec (fun (_b : Bool) => (OptionType KCtorMeta)) (kctor_for base q) (kctor_for tail q) (ict_has_name_b tail q)))
 (base : IndCtorEnv) (q : Name) => Bool.rec
  (fun (b : Bool) => Eq (OptionType KCtorMeta) (Bool.rec (fun (_b : Bool) => (OptionType KCtorMeta)) (kctor_for (ict_append base tail) q) (OptionType.none KCtorMeta) b) (Bool.rec (fun (_b : Bool) => (OptionType KCtorMeta)) (kctor_for base q) (Bool.rec (fun (_b : Bool) => (OptionType KCtorMeta)) (kctor_for tail q) (OptionType.none KCtorMeta) b) (Bool.rec (fun (_b : Bool) => Bool) (ict_has_name_b tail q) Bool.true b)))
  (ih base q) (Eq.refl (OptionType KCtorMeta) (OptionType.none KCtorMeta)) (name_eqb n q))
 (fun (tail : IndCtorEnv) (n : Name) (cm : KCtorMeta)
 (ih : forall (base : IndCtorEnv) (q : Name), Eq (OptionType KCtorMeta) (kctor_for (ict_append base tail) q) (Bool.rec (fun (_b : Bool) => (OptionType KCtorMeta)) (kctor_for base q) (kctor_for tail q) (ict_has_name_b tail q)))
 (base : IndCtorEnv) (q : Name) => Bool.rec
  (fun (b : Bool) => Eq (OptionType KCtorMeta) (Bool.rec (fun (_b : Bool) => (OptionType KCtorMeta)) (kctor_for (ict_append base tail) q) (OptionType.some KCtorMeta cm) b) (Bool.rec (fun (_b : Bool) => (OptionType KCtorMeta)) (kctor_for base q) (Bool.rec (fun (_b : Bool) => (OptionType KCtorMeta)) (kctor_for tail q) (OptionType.some KCtorMeta cm) b) (Bool.rec (fun (_b : Bool) => Bool) (ict_has_name_b tail q) Bool.true b)))
  (ih base q) (Eq.refl (OptionType KCtorMeta) (OptionType.some KCtorMeta cm)) (name_eqb n q)) updates",
    ),
    DeclarationInput::Proof(
        "ict_ctor_append_fresh",
        r"forall (updates base : IndCtorEnv) (q : Name), Eq Bool (ict_has_name_b updates q) Bool.false -> Eq (OptionType KCtorMeta) (kctor_for (ict_append base updates) q) (kctor_for base q)",
        r"fun (updates base : IndCtorEnv) (q : Name) (branch : Eq Bool (ict_has_name_b updates q) Bool.false) =>
 Eq.trans (OptionType KCtorMeta) (kctor_for (ict_append base updates) q) (Bool.rec (fun (_b : Bool) => (OptionType KCtorMeta)) (kctor_for base q) (kctor_for updates q) (ict_has_name_b updates q)) (kctor_for base q)
  (ict_ctor_append updates base q)
  (Eq.cong Bool (OptionType KCtorMeta) (fun (b : Bool) => (Bool.rec (fun (_b : Bool) => (OptionType KCtorMeta)) (kctor_for base q) (kctor_for updates q) b)) (ict_has_name_b updates q) Bool.false branch)",
    ),
    DeclarationInput::Proof(
        "ict_ctor_append_seen",
        r"forall (updates base : IndCtorEnv) (q : Name), Eq Bool (ict_has_name_b updates q) Bool.true -> Eq (OptionType KCtorMeta) (kctor_for (ict_append base updates) q) (kctor_for updates q)",
        r"fun (updates base : IndCtorEnv) (q : Name) (branch : Eq Bool (ict_has_name_b updates q) Bool.true) =>
 Eq.trans (OptionType KCtorMeta) (kctor_for (ict_append base updates) q) (Bool.rec (fun (_b : Bool) => (OptionType KCtorMeta)) (kctor_for base q) (kctor_for updates q) (ict_has_name_b updates q)) (kctor_for updates q)
  (ict_ctor_append updates base q)
  (Eq.cong Bool (OptionType KCtorMeta) (fun (b : Bool) => (Bool.rec (fun (_b : Bool) => (OptionType KCtorMeta)) (kctor_for base q) (kctor_for updates q) b)) (ict_has_name_b updates q) Bool.true branch)",
    ),
    DeclarationInput::Proof(
        "ict_ctor_add_ind_same",
        r"forall (base : IndCtorEnv) (n : Name) (im : KIndMeta), Eq (OptionType KCtorMeta) (kctor_for (IndCtorEnv.addInd base n im) n) (OptionType.none KCtorMeta)",
        r"fun (base : IndCtorEnv) (n : Name) (im : KIndMeta) =>
 Eq.cong Bool (OptionType KCtorMeta) (fun (b : Bool) => (Bool.rec (fun (_b : Bool) => (OptionType KCtorMeta)) (kctor_for base n) (OptionType.none KCtorMeta) b))
  (name_eqb n n) Bool.true (name_eqb_refl n)",
    ),
    DeclarationInput::Proof(
        "ict_ctor_add_ind_other",
        r"forall (base : IndCtorEnv) (n q : Name) (im : KIndMeta), Eq Bool (name_eqb n q) Bool.false -> Eq (OptionType KCtorMeta) (kctor_for (IndCtorEnv.addInd base n im) q) (kctor_for base q)",
        r"fun (base : IndCtorEnv) (n q : Name) (im : KIndMeta) (different : Eq Bool (name_eqb n q) Bool.false) =>
 Eq.cong Bool (OptionType KCtorMeta) (fun (b : Bool) => (Bool.rec (fun (_b : Bool) => (OptionType KCtorMeta)) (kctor_for base q) (OptionType.none KCtorMeta) b))
  (name_eqb n q) Bool.false different",
    ),
    DeclarationInput::Proof(
        "ict_ctor_add_ctor_same",
        r"forall (base : IndCtorEnv) (n : Name) (cm : KCtorMeta), Eq (OptionType KCtorMeta) (kctor_for (IndCtorEnv.addCtor base n cm) n) (OptionType.some KCtorMeta cm)",
        r"fun (base : IndCtorEnv) (n : Name) (cm : KCtorMeta) =>
 Eq.cong Bool (OptionType KCtorMeta) (fun (b : Bool) => (Bool.rec (fun (_b : Bool) => (OptionType KCtorMeta)) (kctor_for base n) (OptionType.some KCtorMeta cm) b))
  (name_eqb n n) Bool.true (name_eqb_refl n)",
    ),
    DeclarationInput::Proof(
        "ict_ctor_add_ctor_other",
        r"forall (base : IndCtorEnv) (n q : Name) (cm : KCtorMeta), Eq Bool (name_eqb n q) Bool.false -> Eq (OptionType KCtorMeta) (kctor_for (IndCtorEnv.addCtor base n cm) q) (kctor_for base q)",
        r"fun (base : IndCtorEnv) (n q : Name) (cm : KCtorMeta) (different : Eq Bool (name_eqb n q) Bool.false) =>
 Eq.cong Bool (OptionType KCtorMeta) (fun (b : Bool) => (Bool.rec (fun (_b : Bool) => (OptionType KCtorMeta)) (kctor_for base q) (OptionType.some KCtorMeta cm) b))
  (name_eqb n q) Bool.false different",
    ),
    DeclarationInput::Data(
        "ict_eq_updates",
        r"IndCtorEnv",
        r"IndCtorEnv.addCtor (IndCtorEnv.addInd IndCtorEnv.empty kcre_eq_type_name kcre_eq_ind_meta) kcre_eq_refl_name kcre_eq_refl_meta",
    ),
    DeclarationInput::Proof(
        "ict_eq_kind",
        r"forall (base : IndCtorEnv), Eq (OptionType KIndMeta) (kind_for (ict_append base ict_eq_updates) kcre_eq_type_name) (OptionType.some KIndMeta kcre_eq_ind_meta)",
        r"fun (base : IndCtorEnv) => ict_kind_append_seen ict_eq_updates base kcre_eq_type_name (Eq.refl Bool Bool.true)",
    ),
    DeclarationInput::Proof(
        "ict_eq_ctor",
        r"forall (base : IndCtorEnv), Eq (OptionType KCtorMeta) (kctor_for (ict_append base ict_eq_updates) kcre_eq_refl_name) (OptionType.some KCtorMeta kcre_eq_refl_meta)",
        r"fun (base : IndCtorEnv) => ict_ctor_append_seen ict_eq_updates base kcre_eq_refl_name (Eq.refl Bool Bool.true)",
    ),
    DeclarationInput::Proof(
        "ict_eq_unrelated_kind",
        r"forall (base : IndCtorEnv), Eq (OptionType KIndMeta) (kind_for (ict_append base ict_eq_updates) Name.anonymous) (kind_for base Name.anonymous)",
        r"fun (base : IndCtorEnv) => ict_kind_append_fresh ict_eq_updates base Name.anonymous (Eq.refl Bool Bool.false)",
    ),
    DeclarationInput::Proof(
        "ict_eq_ctor_shadows_ind",
        r"forall (base : IndCtorEnv), Eq (OptionType KIndMeta) (kind_for (ict_append base (IndCtorEnv.addCtor ict_eq_updates kcre_eq_type_name kcre_eq_refl_meta)) kcre_eq_type_name) (OptionType.none KIndMeta)",
        r"fun (base : IndCtorEnv) => ict_kind_append_seen (IndCtorEnv.addCtor ict_eq_updates kcre_eq_type_name kcre_eq_refl_meta) base kcre_eq_type_name (Eq.refl Bool Bool.true)",
    ),
    DeclarationInput::Proof(
        "ict_eq_ind_shadows_ctor",
        r"forall (base : IndCtorEnv), Eq (OptionType KCtorMeta) (kctor_for (ict_append base (IndCtorEnv.addInd ict_eq_updates kcre_eq_refl_name kcre_eq_ind_meta)) kcre_eq_refl_name) (OptionType.none KCtorMeta)",
        r"fun (base : IndCtorEnv) => ict_ctor_append_seen (IndCtorEnv.addInd ict_eq_updates kcre_eq_refl_name kcre_eq_ind_meta) base kcre_eq_refl_name (Eq.refl Bool Bool.true)",
    ),
];

#[cfg(test)]
pub(super) const PROOF_ROOTS: &[&str] = &[
    "ict_kind_append",
    "ict_kind_append_fresh",
    "ict_kind_append_seen",
    "ict_kind_add_ind_same",
    "ict_kind_add_ind_other",
    "ict_kind_add_ctor_same",
    "ict_kind_add_ctor_other",
    "ict_ctor_append",
    "ict_ctor_append_fresh",
    "ict_ctor_append_seen",
    "ict_ctor_add_ind_same",
    "ict_ctor_add_ind_other",
    "ict_ctor_add_ctor_same",
    "ict_ctor_add_ctor_other",
    "ict_eq_kind",
    "ict_eq_ctor",
    "ict_eq_unrelated_kind",
    "ict_eq_ctor_shadows_ind",
    "ict_eq_ind_shadows_ctor",
];

#[cfg(test)]
pub(super) const DATA_NAMES: &[&str] = &["ict_append", "ict_has_name_b", "ict_eq_updates"];

#[cfg(test)]
pub(super) const INDUCTIVE_NAMES: &[&str] = &[];

#[cfg(test)]
pub(super) const PROP_PROOF_ROOTS: &[&str] = &[
    "ict_kind_append",
    "ict_kind_append_fresh",
    "ict_kind_append_seen",
    "ict_kind_add_ind_same",
    "ict_kind_add_ind_other",
    "ict_kind_add_ctor_same",
    "ict_kind_add_ctor_other",
    "ict_ctor_append",
    "ict_ctor_append_fresh",
    "ict_ctor_append_seen",
    "ict_ctor_add_ind_same",
    "ict_ctor_add_ind_other",
    "ict_ctor_add_ctor_same",
    "ict_ctor_add_ctor_other",
    "ict_eq_kind",
    "ict_eq_ctor",
    "ict_eq_unrelated_kind",
    "ict_eq_ctor_shadows_ind",
    "ict_eq_ind_shadows_ctor",
];

#[cfg(test)]
pub(super) const TYPE_PROOF_ROOTS: &[&str] = &[];

#[cfg(test)]
pub(super) const NEGATIVE_CONTROLS: &[(&str, &str, &str)] = &[
    (
        "ict_false_cross_kind_survives",
        r"forall (base : IndCtorEnv), Eq (OptionType KIndMeta) (kind_for (ict_append base (IndCtorEnv.addCtor ict_eq_updates kcre_eq_type_name kcre_eq_refl_meta)) kcre_eq_type_name) (OptionType.some KIndMeta kcre_eq_ind_meta)",
        r"fun (base : IndCtorEnv) => ict_eq_ctor_shadows_ind base",
    ),
    (
        "ict_false_other_without_inequality",
        r"forall (base : IndCtorEnv) (n : Name) (im : KIndMeta), Eq (OptionType KIndMeta) (kind_for (IndCtorEnv.addInd base n im) n) (kind_for base n)",
        r"fun (base : IndCtorEnv) (n : Name) (im : KIndMeta) => ict_kind_add_ind_other base n n im (Eq.refl Bool Bool.false)",
    ),
    (
        "ict_false_append_order",
        r"Eq (OptionType KCtorMeta) (kctor_for (ict_append (IndCtorEnv.addCtor IndCtorEnv.empty kcre_eq_refl_name kcre_eq_refl_meta) (IndCtorEnv.addInd IndCtorEnv.empty kcre_eq_refl_name kcre_eq_ind_meta)) kcre_eq_refl_name) (OptionType.some KCtorMeta kcre_eq_refl_meta)",
        r"Eq.refl (OptionType KCtorMeta) (OptionType.some KCtorMeta kcre_eq_refl_meta)",
    ),
    (
        "ict_false_cross_kind_is_fresh",
        r"Eq Bool (ict_has_name_b (IndCtorEnv.addCtor IndCtorEnv.empty kcre_eq_type_name kcre_eq_refl_meta) kcre_eq_type_name) Bool.false",
        r"Eq.refl Bool Bool.false",
    ),
];

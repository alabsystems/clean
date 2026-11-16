// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::DeclarationInput;

pub(super) const DECLARATIONS: &[DeclarationInput] = &[
    DeclarationInput::Proof(
        "nsi_ctor_install_kind_absent",
        r"forall (us : ListType Name) (p : Nat) (parent : Name) (cs : ListType NamedCtorSource), forall (i : Nat) (base : IndCtorEnv) (q : Name), @Eq (Bool) (name_list_mem (nsi_names (NamedCtorSource) (nsi_ctor_name) (cs)) (q)) (Bool.false) -> @Eq (OptionType KIndMeta) (kind_for (nsi_install_ctors (us) (p) (parent) (cs) (i) (base)) (q)) (kind_for (base) (q))",
        r"fun (us : ListType Name) (p : Nat) (parent : Name) (cs : ListType NamedCtorSource) => @ListType.rec NamedCtorSource
 (fun (xs : ListType NamedCtorSource) => forall (i : Nat) (base : IndCtorEnv) (q : Name), @Eq (Bool) (name_list_mem (nsi_names (NamedCtorSource) (nsi_ctor_name) (xs)) (q)) (Bool.false) -> @Eq (OptionType KIndMeta) (kind_for (nsi_install_ctors (us) (p) (parent) (xs) (i) (base)) (q)) (kind_for (base) (q)))
 (fun (i : Nat) (base : IndCtorEnv) (q : Name) (_absent : @Eq (Bool) (name_list_mem (@ListType.nil (Name)) (q)) (Bool.false)) => @Eq.refl (OptionType KIndMeta) (kind_for (base) (q)))
 (fun (c : NamedCtorSource) (tail : ListType NamedCtorSource) (ih : forall (i : Nat) (base : IndCtorEnv) (q : Name), @Eq (Bool) (name_list_mem (nsi_names (NamedCtorSource) (nsi_ctor_name) (tail)) (q)) (Bool.false) -> @Eq (OptionType KIndMeta) (kind_for (nsi_install_ctors (us) (p) (parent) (tail) (i) (base)) (q)) (kind_for (base) (q))) (i : Nat) (base : IndCtorEnv) (q : Name) (no_name : @Eq (Bool) (name_list_mem (nsi_names (NamedCtorSource) (nsi_ctor_name) (@ListType.cons (NamedCtorSource) (c) (tail))) (q)) (Bool.false)) =>
  Eq.trans (OptionType KIndMeta) (kind_for (nsi_install_ctors (us) (p) (parent) (tail) (Nat.succ i) (IndCtorEnv.addCtor (base) (nsi_ctor_name (c)) (nsi_ctor_meta (us) (p) (parent) (i) (c)))) (q)) (kind_for (IndCtorEnv.addCtor (base) (nsi_ctor_name (c)) (nsi_ctor_meta (us) (p) (parent) (i) (c))) (q)) (kind_for (base) (q)) (ih (Nat.succ i) (IndCtorEnv.addCtor (base) (nsi_ctor_name (c)) (nsi_ctor_meta (us) (p) (parent) (i) (c))) (q) (nsi_mem_cons_false_tail (nsi_ctor_name (c)) (nsi_names (NamedCtorSource) (nsi_ctor_name) (tail)) (q) (no_name))) (ict_kind_add_ctor_other (base) (nsi_ctor_name (c)) (q) (nsi_ctor_meta (us) (p) (parent) (i) (c)) (nsi_mem_cons_false_head (nsi_ctor_name (c)) (nsi_names (NamedCtorSource) (nsi_ctor_name) (tail)) (q) (no_name)))) cs",
    ),
    DeclarationInput::Proof(
        "nsi_member_install_kind_absent",
        r"forall (us : ListType Name) (p : Nat) (block : ListType Name) (ms : ListType NamedMemberSource), forall (base : IndCtorEnv) (q : Name), @Eq (Bool) (name_list_mem (nsi_all_names (ms)) (q)) (Bool.false) -> @Eq (OptionType KIndMeta) (kind_for (nsi_install_members (us) (p) (block) (ms) (base)) (q)) (kind_for (base) (q))",
        r"fun (us : ListType Name) (p : Nat) (block : ListType Name) (ms : ListType NamedMemberSource) => @ListType.rec NamedMemberSource
 (fun (xs : ListType NamedMemberSource) => forall (base : IndCtorEnv) (q : Name), @Eq (Bool) (name_list_mem (nsi_all_names (xs)) (q)) (Bool.false) -> @Eq (OptionType KIndMeta) (kind_for (nsi_install_members (us) (p) (block) (xs) (base)) (q)) (kind_for (base) (q)))
 (fun (base : IndCtorEnv) (q : Name) (_no_name : @Eq (Bool) (Bool.false) (Bool.false)) => @Eq.refl (OptionType KIndMeta) (kind_for (base) (q)))
 (fun (m : NamedMemberSource) (tail : ListType NamedMemberSource) (ih : forall (base : IndCtorEnv) (q : Name), @Eq (Bool) (name_list_mem (nsi_all_names (tail)) (q)) (Bool.false) -> @Eq (OptionType KIndMeta) (kind_for (nsi_install_members (us) (p) (block) (tail) (base)) (q)) (kind_for (base) (q))) (base : IndCtorEnv) (q : Name) (no_name : @Eq (Bool) (name_list_mem (nsi_all_names (@ListType.cons (NamedMemberSource) (m) (tail))) (q)) (Bool.false)) =>
  Eq.trans (OptionType KIndMeta) (kind_for (nsi_install_members (us) (p) (block) (tail) (IndCtorEnv.addInd (nsi_install_ctors (us) (p) (nsi_member_name (m)) (nsi_member_ctors (m)) (Nat.zero) (base)) (nsi_member_name (m)) (nsi_member_meta (us) (p) (block) (m)))) (q)) (kind_for (IndCtorEnv.addInd (nsi_install_ctors (us) (p) (nsi_member_name (m)) (nsi_member_ctors (m)) (Nat.zero) (base)) (nsi_member_name (m)) (nsi_member_meta (us) (p) (block) (m))) (q)) (kind_for (base) (q)) (ih (IndCtorEnv.addInd (nsi_install_ctors (us) (p) (nsi_member_name (m)) (nsi_member_ctors (m)) (Nat.zero) (base)) (nsi_member_name (m)) (nsi_member_meta (us) (p) (block) (m))) (q) (nsi_mem_append_false_intro (nsi_names (NamedMemberSource) (nsi_member_name) (tail)) (nsi_all_ctor_names (tail)) (q) (nsi_mem_cons_false_tail (nsi_member_name (m)) (nsi_names (NamedMemberSource) (nsi_member_name) (tail)) (q) (nsi_mem_append_false_left (nsi_names (NamedMemberSource) (nsi_member_name) (@ListType.cons (NamedMemberSource) (m) (tail))) (nsi_all_ctor_names (@ListType.cons (NamedMemberSource) (m) (tail))) (q) (no_name))) (nsi_mem_append_false_right (nsi_names (NamedCtorSource) (nsi_ctor_name) (nsi_member_ctors (m))) (nsi_all_ctor_names (tail)) (q) (nsi_mem_append_false_right (nsi_names (NamedMemberSource) (nsi_member_name) (@ListType.cons (NamedMemberSource) (m) (tail))) (nsi_all_ctor_names (@ListType.cons (NamedMemberSource) (m) (tail))) (q) (no_name))))) (Eq.trans (OptionType KIndMeta) (kind_for (IndCtorEnv.addInd (nsi_install_ctors (us) (p) (nsi_member_name (m)) (nsi_member_ctors (m)) (Nat.zero) (base)) (nsi_member_name (m)) (nsi_member_meta (us) (p) (block) (m))) (q)) (kind_for (nsi_install_ctors (us) (p) (nsi_member_name (m)) (nsi_member_ctors (m)) (Nat.zero) (base)) (q)) (kind_for (base) (q)) (ict_kind_add_ind_other (nsi_install_ctors (us) (p) (nsi_member_name (m)) (nsi_member_ctors (m)) (Nat.zero) (base)) (nsi_member_name (m)) (q) (nsi_member_meta (us) (p) (block) (m)) (nsi_mem_cons_false_head (nsi_member_name (m)) (nsi_names (NamedMemberSource) (nsi_member_name) (tail)) (q) (nsi_mem_append_false_left (nsi_names (NamedMemberSource) (nsi_member_name) (@ListType.cons (NamedMemberSource) (m) (tail))) (nsi_all_ctor_names (@ListType.cons (NamedMemberSource) (m) (tail))) (q) (no_name)))) (nsi_ctor_install_kind_absent (us) (p) (nsi_member_name (m)) (nsi_member_ctors (m)) (Nat.zero) (base) (q) (nsi_mem_append_false_left (nsi_names (NamedCtorSource) (nsi_ctor_name) (nsi_member_ctors (m))) (nsi_all_ctor_names (tail)) (q) (nsi_mem_append_false_right (nsi_names (NamedMemberSource) (nsi_member_name) (@ListType.cons (NamedMemberSource) (m) (tail))) (nsi_all_ctor_names (@ListType.cons (NamedMemberSource) (m) (tail))) (q) (no_name)))))) ms",
    ),
    DeclarationInput::Proof(
        "nsi_source_head_family_tail_absent",
        r"forall (m : NamedMemberSource) (tail : ListType NamedMemberSource) (unique : @Eq (Bool) (nrb_names_unique_b (nsi_all_names (@ListType.cons (NamedMemberSource) (m) (tail)))) (Bool.true)), @Eq (Bool) (name_list_mem (nsi_all_names (tail)) (nsi_member_name (m))) (Bool.false)",
        r"fun (m : NamedMemberSource) (tail : ListType NamedMemberSource) (unique : @Eq (Bool) (nrb_names_unique_b (nsi_all_names (@ListType.cons (NamedMemberSource) (m) (tail)))) (Bool.true)) =>
 nsi_mem_append_false_intro (nsi_names (NamedMemberSource) (nsi_member_name) (tail)) (nsi_all_ctor_names (tail)) (nsi_member_name (m)) (nsi_mem_append_false_left (nsi_names (NamedMemberSource) (nsi_member_name) (tail)) (nsi_name_append (nsi_names (NamedCtorSource) (nsi_ctor_name) (nsi_member_ctors (m))) (nsi_all_ctor_names (tail))) (nsi_member_name (m)) (nsi_unique_cons_head (nsi_member_name (m)) (nsi_name_append (nsi_names (NamedMemberSource) (nsi_member_name) (tail)) (nsi_name_append (nsi_names (NamedCtorSource) (nsi_ctor_name) (nsi_member_ctors (m))) (nsi_all_ctor_names (tail)))) (unique))) (nsi_mem_append_false_right (nsi_names (NamedCtorSource) (nsi_ctor_name) (nsi_member_ctors (m))) (nsi_all_ctor_names (tail)) (nsi_member_name (m)) (nsi_mem_append_false_right (nsi_names (NamedMemberSource) (nsi_member_name) (tail)) (nsi_name_append (nsi_names (NamedCtorSource) (nsi_ctor_name) (nsi_member_ctors (m))) (nsi_all_ctor_names (tail))) (nsi_member_name (m)) (nsi_unique_cons_head (nsi_member_name (m)) (nsi_name_append (nsi_names (NamedMemberSource) (nsi_member_name) (tail)) (nsi_name_append (nsi_names (NamedCtorSource) (nsi_ctor_name) (nsi_member_ctors (m))) (nsi_all_ctor_names (tail)))) (unique))))",
    ),
    DeclarationInput::Proof(
        "nsi_member_head_kind_selected",
        r"forall (us : ListType Name) (p : Nat) (block : ListType Name) (m : NamedMemberSource) (tail : ListType NamedMemberSource) (base : IndCtorEnv) (unique : @Eq (Bool) (nrb_names_unique_b (nsi_all_names (@ListType.cons (NamedMemberSource) (m) (tail)))) (Bool.true)), @Eq (OptionType KIndMeta) (kind_for (nsi_install_members (us) (p) (block) (@ListType.cons (NamedMemberSource) (m) (tail)) (base)) (nsi_member_name (m))) (@OptionType.some (KIndMeta) (nsi_member_meta (us) (p) (block) (m)))",
        r"fun (us : ListType Name) (p : Nat) (block : ListType Name) (m : NamedMemberSource) (tail : ListType NamedMemberSource) (base : IndCtorEnv) (unique : @Eq (Bool) (nrb_names_unique_b (nsi_all_names (@ListType.cons (NamedMemberSource) (m) (tail)))) (Bool.true)) =>
 Eq.trans (OptionType KIndMeta) (kind_for (nsi_install_members (us) (p) (block) (@ListType.cons (NamedMemberSource) (m) (tail)) (base)) (nsi_member_name (m))) (kind_for (IndCtorEnv.addInd (nsi_install_ctors (us) (p) (nsi_member_name (m)) (nsi_member_ctors (m)) (Nat.zero) (base)) (nsi_member_name (m)) (nsi_member_meta (us) (p) (block) (m))) (nsi_member_name (m))) (@OptionType.some (KIndMeta) (nsi_member_meta (us) (p) (block) (m))) (nsi_member_install_kind_absent (us) (p) (block) (tail) (IndCtorEnv.addInd (nsi_install_ctors (us) (p) (nsi_member_name (m)) (nsi_member_ctors (m)) (Nat.zero) (base)) (nsi_member_name (m)) (nsi_member_meta (us) (p) (block) (m))) (nsi_member_name (m)) (nsi_source_head_family_tail_absent (m) (tail) (unique))) (ict_kind_add_ind_same (nsi_install_ctors (us) (p) (nsi_member_name (m)) (nsi_member_ctors (m)) (Nat.zero) (base)) (nsi_member_name (m)) (nsi_member_meta (us) (p) (block) (m)))",
    ),
    DeclarationInput::Proof(
        "nsi_member_install_kind_selected",
        r"forall (us : ListType Name) (p : Nat) (block : ListType Name) (ms : ListType NamedMemberSource), forall (base : IndCtorEnv) (mi : Nat) (m : NamedMemberSource), @Eq (Bool) (nrb_names_unique_b (nsi_all_names (ms))) (Bool.true) -> @Eq (OptionType NamedMemberSource) (nsi_at (NamedMemberSource) (ms) (mi)) (@OptionType.some (NamedMemberSource) (m)) -> @Eq (OptionType KIndMeta) (kind_for (nsi_install_members (us) (p) (block) (ms) (base)) (nsi_member_name (m))) (@OptionType.some (KIndMeta) (nsi_member_meta (us) (p) (block) (m)))",
        r"fun (us : ListType Name) (p : Nat) (block : ListType Name) (ms : ListType NamedMemberSource) => @ListType.rec NamedMemberSource
 (fun (xs : ListType NamedMemberSource) => forall (base : IndCtorEnv) (mi : Nat) (m : NamedMemberSource), @Eq (Bool) (nrb_names_unique_b (nsi_all_names (xs))) (Bool.true) -> @Eq (OptionType NamedMemberSource) (nsi_at (NamedMemberSource) (xs) (mi)) (@OptionType.some (NamedMemberSource) (m)) -> @Eq (OptionType KIndMeta) (kind_for (nsi_install_members (us) (p) (block) (xs) (base)) (nsi_member_name (m))) (@OptionType.some (KIndMeta) (nsi_member_meta (us) (p) (block) (m))))
 (fun (base : IndCtorEnv) (mi : Nat) (m : NamedMemberSource) (_unique : @Eq (Bool) (nrb_names_unique_b (nsi_all_names (@ListType.nil (NamedMemberSource)))) (Bool.true)) (bad : @Eq (OptionType NamedMemberSource) (nsi_at (NamedMemberSource) (@ListType.nil (NamedMemberSource)) (mi)) (@OptionType.some (NamedMemberSource) (m))) => option_none_ne_some (NamedMemberSource) (m) (@Eq (OptionType KIndMeta) (kind_for (nsi_install_members (us) (p) (block) (@ListType.nil (NamedMemberSource)) (base)) (nsi_member_name (m))) (@OptionType.some (KIndMeta) (nsi_member_meta (us) (p) (block) (m)))) (bad))
 (fun (m0 : NamedMemberSource) (tail : ListType NamedMemberSource) (ih : forall (base : IndCtorEnv) (mi : Nat) (m : NamedMemberSource), @Eq (Bool) (nrb_names_unique_b (nsi_all_names (tail))) (Bool.true) -> @Eq (OptionType NamedMemberSource) (nsi_at (NamedMemberSource) (tail) (mi)) (@OptionType.some (NamedMemberSource) (m)) -> @Eq (OptionType KIndMeta) (kind_for (nsi_install_members (us) (p) (block) (tail) (base)) (nsi_member_name (m))) (@OptionType.some (KIndMeta) (nsi_member_meta (us) (p) (block) (m)))) (base : IndCtorEnv) (mi : Nat) => @Nat.rec
  (fun (j : Nat) => forall (m : NamedMemberSource), @Eq (Bool) (nrb_names_unique_b (nsi_all_names (@ListType.cons (NamedMemberSource) (m0) (tail)))) (Bool.true) -> @Eq (OptionType NamedMemberSource) (nsi_at (NamedMemberSource) (@ListType.cons (NamedMemberSource) (m0) (tail)) (j)) (@OptionType.some (NamedMemberSource) (m)) -> @Eq (OptionType KIndMeta) (kind_for (nsi_install_members (us) (p) (block) (@ListType.cons (NamedMemberSource) (m0) (tail)) (base)) (nsi_member_name (m))) (@OptionType.some (KIndMeta) (nsi_member_meta (us) (p) (block) (m))))
  (fun (m : NamedMemberSource) (unique : @Eq (Bool) (nrb_names_unique_b (nsi_all_names (@ListType.cons (NamedMemberSource) (m0) (tail)))) (Bool.true)) (found : @Eq (OptionType NamedMemberSource) (@OptionType.some (NamedMemberSource) (m0)) (@OptionType.some (NamedMemberSource) (m))) =>
   Eq.subst (NamedMemberSource) (fun (z : NamedMemberSource) => @Eq (OptionType KIndMeta) (kind_for (nsi_install_members (us) (p) (block) (@ListType.cons (NamedMemberSource) (m0) (tail)) (base)) (nsi_member_name (z))) (@OptionType.some (KIndMeta) (nsi_member_meta (us) (p) (block) (z)))) (m0) (m) (option_some_inj (NamedMemberSource) (m0) (m) (found)) (nsi_member_head_kind_selected (us) (p) (block) (m0) (tail) (base) (unique)))
  (fun (j : Nat) (_unused : forall (m : NamedMemberSource), @Eq (Bool) (nrb_names_unique_b (nsi_all_names (@ListType.cons (NamedMemberSource) (m0) (tail)))) (Bool.true) -> @Eq (OptionType NamedMemberSource) (nsi_at (NamedMemberSource) (@ListType.cons (NamedMemberSource) (m0) (tail)) (j)) (@OptionType.some (NamedMemberSource) (m)) -> @Eq (OptionType KIndMeta) (kind_for (nsi_install_members (us) (p) (block) (@ListType.cons (NamedMemberSource) (m0) (tail)) (base)) (nsi_member_name (m))) (@OptionType.some (KIndMeta) (nsi_member_meta (us) (p) (block) (m)))) (m : NamedMemberSource) (unique : @Eq (Bool) (nrb_names_unique_b (nsi_all_names (@ListType.cons (NamedMemberSource) (m0) (tail)))) (Bool.true)) (found : @Eq (OptionType NamedMemberSource) (nsi_at (NamedMemberSource) (tail) (j)) (@OptionType.some (NamedMemberSource) (m))) => ih (IndCtorEnv.addInd (nsi_install_ctors (us) (p) (nsi_member_name (m0)) (nsi_member_ctors (m0)) (Nat.zero) (base)) (nsi_member_name (m0)) (nsi_member_meta (us) (p) (block) (m0))) (j) (m) (nsi_source_unique_tail (m0) (tail) (unique)) (found)) mi) ms",
    ),
    DeclarationInput::Proof(
        "nsi_raw_kind_lookup_installed",
        r"forall (us : ListType Name) (p : Nat) (ms : ListType NamedMemberSource) (base : IndCtorEnv) (mi : Nat) (m : NamedMemberSource) (unique : @Eq (Bool) (nrb_names_unique_b (nsi_all_names (ms))) (Bool.true)) (member_at : @Eq (OptionType NamedMemberSource) (nsi_at (NamedMemberSource) (ms) (mi)) (@OptionType.some (NamedMemberSource) (m))), @Eq (OptionType KIndMeta) (kind_for (nsi_raw_install (us) (p) (ms) (base)) (nsi_member_name (m))) (@OptionType.some (KIndMeta) (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m)))",
        r"fun (us : ListType Name) (p : Nat) (ms : ListType NamedMemberSource) (base : IndCtorEnv) (mi : Nat) (m : NamedMemberSource) (unique : @Eq (Bool) (nrb_names_unique_b (nsi_all_names (ms))) (Bool.true)) (member_at : @Eq (OptionType NamedMemberSource) (nsi_at (NamedMemberSource) (ms) (mi)) (@OptionType.some (NamedMemberSource) (m))) =>
 nsi_member_install_kind_selected (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (ms) (base) (mi) (m) (unique) (member_at)",
    ),
    DeclarationInput::Proof(
        "nsi_raw_selected_lookups",
        r"forall (us : ListType Name) (p : Nat) (ms : ListType NamedMemberSource) (base : IndCtorEnv) (mi : Nat) (m : NamedMemberSource) (j : Nat) (c : NamedCtorSource) (unique : @Eq (Bool) (nrb_names_unique_b (nsi_all_names (ms))) (Bool.true)) (member_at : @Eq (OptionType NamedMemberSource) (nsi_at (NamedMemberSource) (ms) (mi)) (@OptionType.some (NamedMemberSource) (m))) (ctor_at : @Eq (OptionType NamedCtorSource) (nsi_at (NamedCtorSource) (nsi_member_ctors (m)) (j)) (@OptionType.some (NamedCtorSource) (c))) (C : Type) (k : forall (first : NamedMemberSource), @Eq (OptionType Name) (nrb_name_at (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (Nat.zero)) (@OptionType.some (Name) (nsi_member_name (first))) -> @Eq (OptionType KIndMeta) (kind_for (nsi_raw_install (us) (p) (ms) (base)) (nsi_member_name (first))) (@OptionType.some (KIndMeta) (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first))) -> @Eq (OptionType Name) (nrb_name_at (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (mi)) (@OptionType.some (Name) (nsi_member_name (m))) -> @Eq (OptionType KIndMeta) (kind_for (nsi_raw_install (us) (p) (ms) (base)) (nsi_member_name (m))) (@OptionType.some (KIndMeta) (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m))) -> @Eq (OptionType Name) (nrb_name_at (kind_ctor_names (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m))) (j)) (@OptionType.some (Name) (nsi_ctor_name (c))) -> @Eq (OptionType KCtorMeta) (kctor_for (nsi_raw_install (us) (p) (ms) (base)) (nsi_ctor_name (c))) (@OptionType.some (KCtorMeta) (nsi_ctor_meta (us) (p) (nsi_member_name (m)) (j) (c))) -> C), C",
        r"fun (us : ListType Name) (p : Nat) (ms : ListType NamedMemberSource) (base : IndCtorEnv) (mi : Nat) (m : NamedMemberSource) (j : Nat) (c : NamedCtorSource) (unique : @Eq (Bool) (nrb_names_unique_b (nsi_all_names (ms))) (Bool.true)) (member_at : @Eq (OptionType NamedMemberSource) (nsi_at (NamedMemberSource) (ms) (mi)) (@OptionType.some (NamedMemberSource) (m))) (ctor_at : @Eq (OptionType NamedCtorSource) (nsi_at (NamedCtorSource) (nsi_member_ctors (m)) (j)) (@OptionType.some (NamedCtorSource) (c))) (C : Type) (k : forall (first : NamedMemberSource), @Eq (OptionType Name) (nrb_name_at (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (Nat.zero)) (@OptionType.some (Name) (nsi_member_name (first))) -> @Eq (OptionType KIndMeta) (kind_for (nsi_raw_install (us) (p) (ms) (base)) (nsi_member_name (first))) (@OptionType.some (KIndMeta) (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first))) -> @Eq (OptionType Name) (nrb_name_at (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (mi)) (@OptionType.some (Name) (nsi_member_name (m))) -> @Eq (OptionType KIndMeta) (kind_for (nsi_raw_install (us) (p) (ms) (base)) (nsi_member_name (m))) (@OptionType.some (KIndMeta) (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m))) -> @Eq (OptionType Name) (nrb_name_at (kind_ctor_names (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m))) (j)) (@OptionType.some (Name) (nsi_ctor_name (c))) -> @Eq (OptionType KCtorMeta) (kctor_for (nsi_raw_install (us) (p) (ms) (base)) (nsi_ctor_name (c))) (@OptionType.some (KCtorMeta) (nsi_ctor_meta (us) (p) (nsi_member_name (m)) (j) (c))) -> C) =>
 @ListType.rec (NamedMemberSource) (fun (xs : ListType NamedMemberSource) => forall (base : IndCtorEnv) (mi : Nat) (m : NamedMemberSource) (j : Nat) (c : NamedCtorSource), @Eq (Bool) (nrb_names_unique_b (nsi_all_names (xs))) (Bool.true) -> @Eq (OptionType NamedMemberSource) (nsi_at (NamedMemberSource) (xs) (mi)) (@OptionType.some (NamedMemberSource) (m)) -> @Eq (OptionType NamedCtorSource) (nsi_at (NamedCtorSource) (nsi_member_ctors (m)) (j)) (@OptionType.some (NamedCtorSource) (c)) -> (forall (first : NamedMemberSource), @Eq (OptionType Name) (nrb_name_at (nsi_names (NamedMemberSource) (nsi_member_name) (xs)) (Nat.zero)) (@OptionType.some (Name) (nsi_member_name (first))) -> @Eq (OptionType KIndMeta) (kind_for (nsi_raw_install (us) (p) (xs) (base)) (nsi_member_name (first))) (@OptionType.some (KIndMeta) (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (xs)) (first))) -> @Eq (OptionType Name) (nrb_name_at (nsi_names (NamedMemberSource) (nsi_member_name) (xs)) (mi)) (@OptionType.some (Name) (nsi_member_name (m))) -> @Eq (OptionType KIndMeta) (kind_for (nsi_raw_install (us) (p) (xs) (base)) (nsi_member_name (m))) (@OptionType.some (KIndMeta) (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (xs)) (m))) -> @Eq (OptionType Name) (nrb_name_at (kind_ctor_names (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (xs)) (m))) (j)) (@OptionType.some (Name) (nsi_ctor_name (c))) -> @Eq (OptionType KCtorMeta) (kctor_for (nsi_raw_install (us) (p) (xs) (base)) (nsi_ctor_name (c))) (@OptionType.some (KCtorMeta) (nsi_ctor_meta (us) (p) (nsi_member_name (m)) (j) (c))) -> C) -> C) (fun (base : IndCtorEnv) (mi : Nat) (m : NamedMemberSource) (j : Nat) (c : NamedCtorSource) (_unique : @Eq (Bool) (nrb_names_unique_b (nsi_all_names (@ListType.nil (NamedMemberSource)))) (Bool.true)) (bad : @Eq (OptionType NamedMemberSource) (nsi_at (NamedMemberSource) (@ListType.nil (NamedMemberSource)) (mi)) (@OptionType.some (NamedMemberSource) (m))) (_ctor_at : @Eq (OptionType NamedCtorSource) (nsi_at (NamedCtorSource) (nsi_member_ctors (m)) (j)) (@OptionType.some (NamedCtorSource) (c))) (_k : forall (first : NamedMemberSource), @Eq (OptionType Name) (nrb_name_at (nsi_names (NamedMemberSource) (nsi_member_name) (@ListType.nil (NamedMemberSource))) (Nat.zero)) (@OptionType.some (Name) (nsi_member_name (first))) -> @Eq (OptionType KIndMeta) (kind_for (nsi_raw_install (us) (p) (@ListType.nil (NamedMemberSource)) (base)) (nsi_member_name (first))) (@OptionType.some (KIndMeta) (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (@ListType.nil (NamedMemberSource))) (first))) -> @Eq (OptionType Name) (nrb_name_at (nsi_names (NamedMemberSource) (nsi_member_name) (@ListType.nil (NamedMemberSource))) (mi)) (@OptionType.some (Name) (nsi_member_name (m))) -> @Eq (OptionType KIndMeta) (kind_for (nsi_raw_install (us) (p) (@ListType.nil (NamedMemberSource)) (base)) (nsi_member_name (m))) (@OptionType.some (KIndMeta) (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (@ListType.nil (NamedMemberSource))) (m))) -> @Eq (OptionType Name) (nrb_name_at (kind_ctor_names (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (@ListType.nil (NamedMemberSource))) (m))) (j)) (@OptionType.some (Name) (nsi_ctor_name (c))) -> @Eq (OptionType KCtorMeta) (kctor_for (nsi_raw_install (us) (p) (@ListType.nil (NamedMemberSource)) (base)) (nsi_ctor_name (c))) (@OptionType.some (KCtorMeta) (nsi_ctor_meta (us) (p) (nsi_member_name (m)) (j) (c))) -> C) => opt_none_ne_some_t (NamedMemberSource) (m) (C) (bad)) (fun (head : NamedMemberSource) (tail : ListType NamedMemberSource) (_unused : forall (base : IndCtorEnv) (mi : Nat) (m : NamedMemberSource) (j : Nat) (c : NamedCtorSource), @Eq (Bool) (nrb_names_unique_b (nsi_all_names (tail))) (Bool.true) -> @Eq (OptionType NamedMemberSource) (nsi_at (NamedMemberSource) (tail) (mi)) (@OptionType.some (NamedMemberSource) (m)) -> @Eq (OptionType NamedCtorSource) (nsi_at (NamedCtorSource) (nsi_member_ctors (m)) (j)) (@OptionType.some (NamedCtorSource) (c)) -> (forall (first : NamedMemberSource), @Eq (OptionType Name) (nrb_name_at (nsi_names (NamedMemberSource) (nsi_member_name) (tail)) (Nat.zero)) (@OptionType.some (Name) (nsi_member_name (first))) -> @Eq (OptionType KIndMeta) (kind_for (nsi_raw_install (us) (p) (tail) (base)) (nsi_member_name (first))) (@OptionType.some (KIndMeta) (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (tail)) (first))) -> @Eq (OptionType Name) (nrb_name_at (nsi_names (NamedMemberSource) (nsi_member_name) (tail)) (mi)) (@OptionType.some (Name) (nsi_member_name (m))) -> @Eq (OptionType KIndMeta) (kind_for (nsi_raw_install (us) (p) (tail) (base)) (nsi_member_name (m))) (@OptionType.some (KIndMeta) (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (tail)) (m))) -> @Eq (OptionType Name) (nrb_name_at (kind_ctor_names (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (tail)) (m))) (j)) (@OptionType.some (Name) (nsi_ctor_name (c))) -> @Eq (OptionType KCtorMeta) (kctor_for (nsi_raw_install (us) (p) (tail) (base)) (nsi_ctor_name (c))) (@OptionType.some (KCtorMeta) (nsi_ctor_meta (us) (p) (nsi_member_name (m)) (j) (c))) -> C) -> C) (base : IndCtorEnv) (mi : Nat) (m : NamedMemberSource) (j : Nat) (c : NamedCtorSource) (unique : @Eq (Bool) (nrb_names_unique_b (nsi_all_names (@ListType.cons (NamedMemberSource) (head) (tail)))) (Bool.true)) (member_at : @Eq (OptionType NamedMemberSource) (nsi_at (NamedMemberSource) (@ListType.cons (NamedMemberSource) (head) (tail)) (mi)) (@OptionType.some (NamedMemberSource) (m))) (ctor_at : @Eq (OptionType NamedCtorSource) (nsi_at (NamedCtorSource) (nsi_member_ctors (m)) (j)) (@OptionType.some (NamedCtorSource) (c))) (k : forall (first : NamedMemberSource), @Eq (OptionType Name) (nrb_name_at (nsi_names (NamedMemberSource) (nsi_member_name) (@ListType.cons (NamedMemberSource) (head) (tail))) (Nat.zero)) (@OptionType.some (Name) (nsi_member_name (first))) -> @Eq (OptionType KIndMeta) (kind_for (nsi_raw_install (us) (p) (@ListType.cons (NamedMemberSource) (head) (tail)) (base)) (nsi_member_name (first))) (@OptionType.some (KIndMeta) (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (@ListType.cons (NamedMemberSource) (head) (tail))) (first))) -> @Eq (OptionType Name) (nrb_name_at (nsi_names (NamedMemberSource) (nsi_member_name) (@ListType.cons (NamedMemberSource) (head) (tail))) (mi)) (@OptionType.some (Name) (nsi_member_name (m))) -> @Eq (OptionType KIndMeta) (kind_for (nsi_raw_install (us) (p) (@ListType.cons (NamedMemberSource) (head) (tail)) (base)) (nsi_member_name (m))) (@OptionType.some (KIndMeta) (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (@ListType.cons (NamedMemberSource) (head) (tail))) (m))) -> @Eq (OptionType Name) (nrb_name_at (kind_ctor_names (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (@ListType.cons (NamedMemberSource) (head) (tail))) (m))) (j)) (@OptionType.some (Name) (nsi_ctor_name (c))) -> @Eq (OptionType KCtorMeta) (kctor_for (nsi_raw_install (us) (p) (@ListType.cons (NamedMemberSource) (head) (tail)) (base)) (nsi_ctor_name (c))) (@OptionType.some (KCtorMeta) (nsi_ctor_meta (us) (p) (nsi_member_name (m)) (j) (c))) -> C) => k (head) (@Eq.refl (OptionType Name) (@OptionType.some (Name) (nsi_member_name (head)))) (nsi_raw_kind_lookup_installed (us) (p) (@ListType.cons (NamedMemberSource) (head) (tail)) (base) (Nat.zero) (head) (unique) (@Eq.refl (OptionType NamedMemberSource) (@OptionType.some (NamedMemberSource) (head)))) (nsi_at_name_at (NamedMemberSource) (nsi_member_name) (@ListType.cons (NamedMemberSource) (head) (tail)) (mi) (m) (member_at)) (nsi_raw_kind_lookup_installed (us) (p) (@ListType.cons (NamedMemberSource) (head) (tail)) (base) (mi) (m) (unique) (member_at)) (nsi_at_name_at (NamedCtorSource) (nsi_ctor_name) (nsi_member_ctors (m)) (j) (c) (ctor_at)) (nsi_raw_ctor_lookup_installed (us) (p) (@ListType.cons (NamedMemberSource) (head) (tail)) (base) (mi) (m) (j) (c) (unique) (member_at) (ctor_at))) (ms) (base) (mi) (m) (j) (c) (unique) (member_at) (ctor_at) (k)",
    ),
    DeclarationInput::Proof(
        "nfi_demo_second_family",
        r"forall (base : IndCtorEnv), @Eq (OptionType KIndMeta) (kind_for (nsi_raw_install (nrb_demo_levels) (Nat.succ Nat.zero) (nsi_demo_sources) (base)) (nrb_demo_g)) (@OptionType.some (KIndMeta) (nsi_member_meta (nrb_demo_levels) (Nat.succ Nat.zero) (nsi_names (NamedMemberSource) (nsi_member_name) (nsi_demo_sources)) (nsi_demo_g)))",
        r"fun (base : IndCtorEnv) =>
 nsi_raw_kind_lookup_installed (nrb_demo_levels) (Nat.succ Nat.zero) (nsi_demo_sources) (base) (Nat.succ Nat.zero) (nsi_demo_g) (nsi_demo_unique) (@Eq.refl (OptionType NamedMemberSource) (@OptionType.some (NamedMemberSource) (nsi_demo_g)))",
    ),
    DeclarationInput::Proof(
        "nfi_demo_unrelated_old_kind",
        r"forall (base : IndCtorEnv), @Eq (OptionType KIndMeta) (kind_for (nsi_raw_install (nrb_demo_levels) (Nat.succ Nat.zero) (nsi_demo_sources) (base)) (nrb_demo_u)) (kind_for (base) (nrb_demo_u))",
        r"fun (base : IndCtorEnv) =>
 nsi_member_install_kind_absent (nrb_demo_levels) (Nat.succ Nat.zero) (nsi_names (NamedMemberSource) (nsi_member_name) (nsi_demo_sources)) (nsi_demo_sources) (base) (nrb_demo_u) (@Eq.refl (Bool) (Bool.false))",
    ),
    DeclarationInput::Proof(
        "nfi_demo_preserves_captured_eq",
        r"@Eq (OptionType KIndMeta) (kind_for (nsi_raw_install (nrb_demo_levels) (Nat.succ Nat.zero) (nsi_demo_sources) (ict_eq_updates)) (kcre_eq_type_name)) (@OptionType.some (KIndMeta) (kcre_eq_ind_meta))",
        r"Eq.trans (OptionType KIndMeta) (kind_for (nsi_raw_install (nrb_demo_levels) (Nat.succ Nat.zero) (nsi_demo_sources) (ict_eq_updates)) (kcre_eq_type_name)) (kind_for (ict_eq_updates) (kcre_eq_type_name)) (@OptionType.some (KIndMeta) (kcre_eq_ind_meta)) (nsi_member_install_kind_absent (nrb_demo_levels) (Nat.succ Nat.zero) (nsi_names (NamedMemberSource) (nsi_member_name) (nsi_demo_sources)) (nsi_demo_sources) (ict_eq_updates) (kcre_eq_type_name) (@Eq.refl (Bool) (Bool.false))) (@Eq.refl (OptionType KIndMeta) (@OptionType.some (KIndMeta) (kcre_eq_ind_meta)))",
    ),
    DeclarationInput::Proof(
        "nfi_demo_six_equation_consumer",
        r"forall (base : IndCtorEnv) (C : Type) (k : forall (first : NamedMemberSource), @Eq (OptionType Name) (nrb_name_at (nsi_names (NamedMemberSource) (nsi_member_name) (nsi_demo_sources)) (Nat.zero)) (@OptionType.some (Name) (nsi_member_name (first))) -> @Eq (OptionType KIndMeta) (kind_for (nsi_raw_install (nrb_demo_levels) (Nat.succ Nat.zero) (nsi_demo_sources) (base)) (nsi_member_name (first))) (@OptionType.some (KIndMeta) (nsi_member_meta (nrb_demo_levels) (Nat.succ Nat.zero) (nsi_names (NamedMemberSource) (nsi_member_name) (nsi_demo_sources)) (first))) -> @Eq (OptionType Name) (nrb_name_at (nsi_names (NamedMemberSource) (nsi_member_name) (nsi_demo_sources)) (Nat.succ Nat.zero)) (@OptionType.some (Name) (nsi_member_name (nsi_demo_g))) -> @Eq (OptionType KIndMeta) (kind_for (nsi_raw_install (nrb_demo_levels) (Nat.succ Nat.zero) (nsi_demo_sources) (base)) (nsi_member_name (nsi_demo_g))) (@OptionType.some (KIndMeta) (nsi_member_meta (nrb_demo_levels) (Nat.succ Nat.zero) (nsi_names (NamedMemberSource) (nsi_member_name) (nsi_demo_sources)) (nsi_demo_g))) -> @Eq (OptionType Name) (nrb_name_at (kind_ctor_names (nsi_member_meta (nrb_demo_levels) (Nat.succ Nat.zero) (nsi_names (NamedMemberSource) (nsi_member_name) (nsi_demo_sources)) (nsi_demo_g))) (Nat.succ Nat.zero)) (@OptionType.some (Name) (nsi_ctor_name (nsi_demo_cg2))) -> @Eq (OptionType KCtorMeta) (kctor_for (nsi_raw_install (nrb_demo_levels) (Nat.succ Nat.zero) (nsi_demo_sources) (base)) (nsi_ctor_name (nsi_demo_cg2))) (@OptionType.some (KCtorMeta) (nsi_ctor_meta (nrb_demo_levels) (Nat.succ Nat.zero) (nsi_member_name (nsi_demo_g)) (Nat.succ Nat.zero) (nsi_demo_cg2))) -> C), C",
        r"fun (base : IndCtorEnv) (C : Type) (k : forall (first : NamedMemberSource), @Eq (OptionType Name) (nrb_name_at (nsi_names (NamedMemberSource) (nsi_member_name) (nsi_demo_sources)) (Nat.zero)) (@OptionType.some (Name) (nsi_member_name (first))) -> @Eq (OptionType KIndMeta) (kind_for (nsi_raw_install (nrb_demo_levels) (Nat.succ Nat.zero) (nsi_demo_sources) (base)) (nsi_member_name (first))) (@OptionType.some (KIndMeta) (nsi_member_meta (nrb_demo_levels) (Nat.succ Nat.zero) (nsi_names (NamedMemberSource) (nsi_member_name) (nsi_demo_sources)) (first))) -> @Eq (OptionType Name) (nrb_name_at (nsi_names (NamedMemberSource) (nsi_member_name) (nsi_demo_sources)) (Nat.succ Nat.zero)) (@OptionType.some (Name) (nsi_member_name (nsi_demo_g))) -> @Eq (OptionType KIndMeta) (kind_for (nsi_raw_install (nrb_demo_levels) (Nat.succ Nat.zero) (nsi_demo_sources) (base)) (nsi_member_name (nsi_demo_g))) (@OptionType.some (KIndMeta) (nsi_member_meta (nrb_demo_levels) (Nat.succ Nat.zero) (nsi_names (NamedMemberSource) (nsi_member_name) (nsi_demo_sources)) (nsi_demo_g))) -> @Eq (OptionType Name) (nrb_name_at (kind_ctor_names (nsi_member_meta (nrb_demo_levels) (Nat.succ Nat.zero) (nsi_names (NamedMemberSource) (nsi_member_name) (nsi_demo_sources)) (nsi_demo_g))) (Nat.succ Nat.zero)) (@OptionType.some (Name) (nsi_ctor_name (nsi_demo_cg2))) -> @Eq (OptionType KCtorMeta) (kctor_for (nsi_raw_install (nrb_demo_levels) (Nat.succ Nat.zero) (nsi_demo_sources) (base)) (nsi_ctor_name (nsi_demo_cg2))) (@OptionType.some (KCtorMeta) (nsi_ctor_meta (nrb_demo_levels) (Nat.succ Nat.zero) (nsi_member_name (nsi_demo_g)) (Nat.succ Nat.zero) (nsi_demo_cg2))) -> C) =>
 nsi_raw_selected_lookups (nrb_demo_levels) (Nat.succ Nat.zero) (nsi_demo_sources) (base) (Nat.succ Nat.zero) (nsi_demo_g) (Nat.succ Nat.zero) (nsi_demo_cg2) (nsi_demo_unique) (@Eq.refl (OptionType NamedMemberSource) (@OptionType.some (NamedMemberSource) (nsi_demo_g))) (@Eq.refl (OptionType NamedCtorSource) (@OptionType.some (NamedCtorSource) (nsi_demo_cg2))) (C) (k)",
    ),
    DeclarationInput::Proof(
        "nsi_raw_member_name_at",
        r"forall (ms : ListType NamedMemberSource) (mi : Nat) (m : NamedMemberSource),
 @Eq (OptionType NamedMemberSource) (nsi_at NamedMemberSource ms mi) (@OptionType.some NamedMemberSource m) ->
 @Eq (OptionType Name) (nrb_name_at (nsi_names NamedMemberSource nsi_member_name ms) mi) (@OptionType.some Name (nsi_member_name m))",
        r"fun (ms : ListType NamedMemberSource) (mi : Nat) (m : NamedMemberSource)
 (member_at : @Eq (OptionType NamedMemberSource) (nsi_at NamedMemberSource ms mi) (@OptionType.some NamedMemberSource m)) =>
 nsi_at_name_at NamedMemberSource nsi_member_name ms mi m member_at",
    ),
    DeclarationInput::Proof(
        "nsi_member_ctor_name_at",
        r"forall (us : ListType Name) (p : Nat) (block : ListType Name) (m : NamedMemberSource) (ci : Nat) (c : NamedCtorSource),
 @Eq (OptionType NamedCtorSource) (nsi_at NamedCtorSource (nsi_member_ctors m) ci) (@OptionType.some NamedCtorSource c) ->
 @Eq (OptionType Name) (nrb_name_at (kind_ctor_names (nsi_member_meta us p block m)) ci) (@OptionType.some Name (nsi_ctor_name c))",
        r"fun (us : ListType Name) (p : Nat) (block : ListType Name) (m : NamedMemberSource) (ci : Nat) (c : NamedCtorSource)
 (ctor_at : @Eq (OptionType NamedCtorSource) (nsi_at NamedCtorSource (nsi_member_ctors m) ci) (@OptionType.some NamedCtorSource c)) =>
 nsi_at_name_at NamedCtorSource nsi_ctor_name (nsi_member_ctors m) ci c ctor_at",
    ),
    DeclarationInput::Proof(
        "nsi_raw_first_name_at",
        r"forall (first : NamedMemberSource) (tail : ListType NamedMemberSource),
 @Eq (OptionType Name)
  (nrb_name_at (nsi_names NamedMemberSource nsi_member_name (@ListType.cons NamedMemberSource first tail)) Nat.zero)
  (@OptionType.some Name (nsi_member_name first))",
        r"fun (first : NamedMemberSource) (tail : ListType NamedMemberSource) =>
 nsi_raw_member_name_at (@ListType.cons NamedMemberSource first tail) Nat.zero first
  (@Eq.refl (OptionType NamedMemberSource) (@OptionType.some NamedMemberSource first))",
    ),
    DeclarationInput::Proof(
        "nsi_demo_g_member_position",
        r"@Eq (OptionType Name)
 (nrb_name_at (nsi_names NamedMemberSource nsi_member_name nsi_demo_sources) (Nat.succ Nat.zero))
 (@OptionType.some Name nrb_demo_g)",
        r"nsi_raw_member_name_at nsi_demo_sources (Nat.succ Nat.zero) nsi_demo_g
 (@Eq.refl (OptionType NamedMemberSource) (@OptionType.some NamedMemberSource nsi_demo_g))",
    ),
    DeclarationInput::Proof(
        "nsi_demo_cg2_constructor_position",
        r"@Eq (OptionType Name)
 (nrb_name_at
  (kind_ctor_names (nsi_member_meta nrb_demo_levels (Nat.succ Nat.zero)
   (nsi_names NamedMemberSource nsi_member_name nsi_demo_sources) nsi_demo_g))
  (Nat.succ Nat.zero))
 (@OptionType.some Name (Name.str nrb_demo_g (Nat.succ Nat.zero)))",
        r"nsi_member_ctor_name_at nrb_demo_levels (Nat.succ Nat.zero)
 (nsi_names NamedMemberSource nsi_member_name nsi_demo_sources)
 nsi_demo_g (Nat.succ Nat.zero) nsi_demo_cg2
 (@Eq.refl (OptionType NamedCtorSource) (@OptionType.some NamedCtorSource nsi_demo_cg2))",
    ),
];

#[cfg(test)]
pub(super) const PROOF_ROOTS: &[&str] = &[
    "nsi_ctor_install_kind_absent",
    "nsi_member_install_kind_absent",
    "nsi_source_head_family_tail_absent",
    "nsi_member_head_kind_selected",
    "nsi_member_install_kind_selected",
    "nsi_raw_kind_lookup_installed",
    "nsi_raw_selected_lookups",
    "nfi_demo_second_family",
    "nfi_demo_unrelated_old_kind",
    "nfi_demo_preserves_captured_eq",
    "nfi_demo_six_equation_consumer",
    "nsi_raw_member_name_at",
    "nsi_member_ctor_name_at",
    "nsi_raw_first_name_at",
    "nsi_demo_g_member_position",
    "nsi_demo_cg2_constructor_position",
];

#[cfg(test)]
pub(super) const PROP_PROOF_ROOTS: &[&str] = &[
    "nsi_ctor_install_kind_absent",
    "nsi_member_install_kind_absent",
    "nsi_source_head_family_tail_absent",
    "nsi_member_head_kind_selected",
    "nsi_member_install_kind_selected",
    "nsi_raw_kind_lookup_installed",
    "nfi_demo_second_family",
    "nfi_demo_unrelated_old_kind",
    "nfi_demo_preserves_captured_eq",
    "nsi_raw_member_name_at",
    "nsi_member_ctor_name_at",
    "nsi_raw_first_name_at",
    "nsi_demo_g_member_position",
    "nsi_demo_cg2_constructor_position",
];

#[cfg(test)]
pub(super) const TYPE_PROOF_ROOTS: &[&str] =
    &["nsi_raw_selected_lookups", "nfi_demo_six_equation_consumer"];

#[cfg(test)]
pub(super) const DATA_NAMES: &[&str] = &[];

#[cfg(test)]
pub(super) const INDUCTIVE_NAMES: &[&str] = &[];

#[cfg(test)]
pub(super) const NEGATIVE_CONTROLS: &[(&str, &str, &str)] = &[
    (
        "nfi_false_member_index_count",
        r"@Eq (OptionType KIndMeta) (kind_for (nsi_demo_installed) (nrb_demo_g)) (@OptionType.some (KIndMeta) (KIndMeta.mk (kind_sig (nsi_member_meta (nrb_demo_levels) (Nat.succ Nat.zero) (nsi_names (NamedMemberSource) (nsi_member_name) (nsi_demo_sources)) (nsi_demo_g))) (kind_num_params (nsi_member_meta (nrb_demo_levels) (Nat.succ Nat.zero) (nsi_names (NamedMemberSource) (nsi_member_name) (nsi_demo_sources)) (nsi_demo_g))) (Nat.zero) (kind_ctor_names (nsi_member_meta (nrb_demo_levels) (Nat.succ Nat.zero) (nsi_names (NamedMemberSource) (nsi_member_name) (nsi_demo_sources)) (nsi_demo_g))) (kind_all_names (nsi_member_meta (nrb_demo_levels) (Nat.succ Nat.zero) (nsi_names (NamedMemberSource) (nsi_member_name) (nsi_demo_sources)) (nsi_demo_g)))))",
        r"nfi_demo_second_family (IndCtorEnv.empty)",
    ),
    (
        "nfi_false_member_block_order",
        r"@Eq (OptionType KIndMeta) (kind_for (nsi_demo_installed) (nrb_demo_g)) (@OptionType.some (KIndMeta) (nsi_member_meta (nrb_demo_levels) (Nat.succ Nat.zero) (@ListType.cons (Name) (nrb_demo_g) (@ListType.cons (Name) (nrb_demo_f) (@ListType.nil (Name)))) (nsi_demo_g)))",
        r"nfi_demo_second_family (IndCtorEnv.empty)",
    ),
    (
        "nsi_false_member_position_name",
        r"@Eq (OptionType Name)
 (nrb_name_at (nsi_names NamedMemberSource nsi_member_name nsi_demo_sources) (Nat.succ Nat.zero))
 (@OptionType.some Name nrb_demo_f)",
        r"nsi_demo_g_member_position",
    ),
    (
        "nsi_false_constructor_position_name",
        r"@Eq (OptionType Name)
 (nrb_name_at
  (kind_ctor_names (nsi_member_meta nrb_demo_levels (Nat.succ Nat.zero)
   (nsi_names NamedMemberSource nsi_member_name nsi_demo_sources) nsi_demo_g))
  (Nat.succ Nat.zero))
 (@OptionType.some Name nrb_demo_cg)",
        r"nsi_demo_cg2_constructor_position",
    ),
];

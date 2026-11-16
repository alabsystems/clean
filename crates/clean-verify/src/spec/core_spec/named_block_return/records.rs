// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::DeclarationInput;

pub(super) const DECLARATIONS: &[DeclarationInput] = &[
    DeclarationInput::Data(
        "nrb_option_b",
        r"forall (A : Type) (f : A -> Bool) (o : OptionType A), Bool",
        r"fun (A : Type) (f : A -> Bool) (o : OptionType A) => @OptionType.rec A (fun (_q : OptionType A) => Bool) Bool.false f o",
    ),
    DeclarationInput::Proof(
        "nrb_option_selected",
        r"forall (A : Type) (f : A -> Bool) (o : OptionType A) (x : A), @Eq Bool (nrb_option_b A f o) Bool.true -> @Eq (OptionType A) o (@OptionType.some A x) -> @Eq Bool (f x) Bool.true",
        r"fun (A : Type) (f : A -> Bool) (o : OptionType A) (x : A) (run : @Eq Bool (nrb_option_b A f o) Bool.true) (found : @Eq (OptionType A) o (@OptionType.some A x)) => Eq.subst (OptionType A) (fun (q : OptionType A) => @Eq Bool (nrb_option_b A f q) Bool.true) o (@OptionType.some A x) found run",
    ),
    DeclarationInput::Proof(
        "nrb_option_resolve",
        r"forall (A : Type) (f : A -> Bool) (o : OptionType A) (C : Type), @Eq Bool (nrb_option_b A f o) Bool.true -> (forall (x : A), @Eq (OptionType A) o (@OptionType.some A x) -> @Eq Bool (f x) Bool.true -> C) -> C",
        r"fun (A : Type) (f : A -> Bool) (o : OptionType A) (C : Type) =>
 @OptionType.rec A
  (fun (q : OptionType A) => @Eq Bool (nrb_option_b A f q) Bool.true -> (forall (x : A), @Eq (OptionType A) q (@OptionType.some A x) -> @Eq Bool (f x) Bool.true -> C) -> C)
  (fun (bad : @Eq Bool Bool.false Bool.true) (_k : forall (x : A), @Eq (OptionType A) (@OptionType.none A) (@OptionType.some A x) -> @Eq Bool (f x) Bool.true -> C) => bool_false_ne_true_t C bad)
  (fun (x : A) (run : @Eq Bool (f x) Bool.true) (k : forall (y : A), @Eq (OptionType A) (@OptionType.some A x) (@OptionType.some A y) -> @Eq Bool (f y) Bool.true -> C) => k x (@Eq.refl (OptionType A) (@OptionType.some A x)) run) o",
    ),
    DeclarationInput::Data(
        "nrb_name_at",
        r"forall (xs : ListType Name) (j : Nat), OptionType Name",
        r"fun (xs : ListType Name) => @ListType.rec Name
 (fun (_ns : ListType Name) => Nat -> OptionType Name)
 (fun (_j : Nat) => @OptionType.none Name)
 (fun (n : Name) (_ns : ListType Name) (ih : Nat -> OptionType Name) (j : Nat) =>
  @Nat.rec (fun (_j : Nat) => OptionType Name) (@OptionType.some Name n)
   (fun (k : Nat) (_unused : OptionType Name) => ih k) j) xs",
    ),
    DeclarationInput::Data(
        "nrb_all_index_b",
        r"forall (f : Nat -> Name -> Bool) (xs : ListType Name), Bool",
        r"fun (f : Nat -> Name -> Bool) (xs : ListType Name) => @ListType.rec Name
 (fun (_ns : ListType Name) => (Nat -> Name -> Bool) -> Bool)
 (fun (_f : Nat -> Name -> Bool) => Bool.true)
 (fun (n : Name) (_ns : ListType Name) (ih : (Nat -> Name -> Bool) -> Bool) (g : Nat -> Name -> Bool) =>
  Bool.and (g Nat.zero n) (ih (fun (j : Nat) (m : Name) => g (Nat.succ j) m))) xs f",
    ),
    DeclarationInput::Proof(
        "nrb_all_index_at",
        r"forall (xs : ListType Name) (f : Nat -> Name -> Bool) (j : Nat) (n : Name), @Eq Bool (nrb_all_index_b f xs) Bool.true -> @Eq (OptionType Name) (nrb_name_at xs j) (@OptionType.some Name n) -> @Eq Bool (f j n) Bool.true",
        r"fun (xs : ListType Name) => @ListType.rec Name
 (fun (ns : ListType Name) => forall (f : Nat -> Name -> Bool) (j : Nat) (n : Name), @Eq Bool (nrb_all_index_b f ns) Bool.true -> @Eq (OptionType Name) (nrb_name_at ns j) (@OptionType.some Name n) -> @Eq Bool (f j n) Bool.true)
 (fun (f : Nat -> Name -> Bool) (j : Nat) (n : Name) (_run : @Eq Bool Bool.true Bool.true) (bad : @Eq (OptionType Name) (@OptionType.none Name) (@OptionType.some Name n)) => option_none_ne_some Name n (@Eq Bool (f j n) Bool.true) bad)
 (fun (a : Name) (tail : ListType Name)
  (ih : forall (f : Nat -> Name -> Bool) (j : Nat) (n : Name), @Eq Bool (nrb_all_index_b f tail) Bool.true -> @Eq (OptionType Name) (nrb_name_at tail j) (@OptionType.some Name n) -> @Eq Bool (f j n) Bool.true)
  (f : Nat -> Name -> Bool) (j : Nat) => @Nat.rec
   (fun (k : Nat) => forall (n : Name), @Eq Bool (nrb_all_index_b f (@ListType.cons Name a tail)) Bool.true -> @Eq (OptionType Name) (nrb_name_at (@ListType.cons Name a tail) k) (@OptionType.some Name n) -> @Eq Bool (f k n) Bool.true)
   (fun (n : Name) (run : @Eq Bool (nrb_all_index_b f (@ListType.cons Name a tail)) Bool.true) (found : @Eq (OptionType Name) (@OptionType.some Name a) (@OptionType.some Name n)) =>
    Eq.subst Name (fun (m : Name) => @Eq Bool (f Nat.zero m) Bool.true) a n (option_some_inj Name a n found)
     (band_eq_true_left (f Nat.zero a) (nrb_all_index_b (fun (k : Nat) (m : Name) => f (Nat.succ k) m) tail) run))
   (fun (k : Nat) (_unused : forall (n : Name), @Eq Bool (nrb_all_index_b f (@ListType.cons Name a tail)) Bool.true -> @Eq (OptionType Name) (nrb_name_at (@ListType.cons Name a tail) k) (@OptionType.some Name n) -> @Eq Bool (f k n) Bool.true)
    (n : Name) (run : @Eq Bool (nrb_all_index_b f (@ListType.cons Name a tail)) Bool.true) (found : @Eq (OptionType Name) (nrb_name_at tail k) (@OptionType.some Name n)) =>
     ih (fun (i : Nat) (m : Name) => f (Nat.succ i) m) k n
      (band_eq_true_right (f Nat.zero a) (nrb_all_index_b (fun (i : Nat) (m : Name) => f (Nat.succ i) m) tail) run) found) j) xs",
    ),
    DeclarationInput::Data(
        "nrb_names_eq_b",
        r"forall (xs ys : ListType Name), Bool",
        r"fun (xs : ListType Name) => @ListType.rec Name
 (fun (_ns : ListType Name) => ListType Name -> Bool)
 (fun (ys : ListType Name) => @ListType.rec Name (fun (_ms : ListType Name) => Bool) Bool.true (fun (_m : Name) (_ms : ListType Name) (_ih : Bool) => Bool.false) ys)
 (fun (n : Name) (_ns : ListType Name) (ih : ListType Name -> Bool) (ys : ListType Name) =>
  @ListType.rec Name (fun (_ms : ListType Name) => Bool) Bool.false
   (fun (m : Name) (ms : ListType Name) (_unused : Bool) => Bool.and (name_eqb n m) (ih ms)) ys) xs",
    ),
    DeclarationInput::Proof(
        "nrb_names_eq_sound",
        r"forall (xs ys : ListType Name), @Eq Bool (nrb_names_eq_b xs ys) Bool.true -> @Eq (ListType Name) xs ys",
        r"fun (xs : ListType Name) => @ListType.rec Name
 (fun (ns : ListType Name) => forall (ys : ListType Name), @Eq Bool (nrb_names_eq_b ns ys) Bool.true -> @Eq (ListType Name) ns ys)
 (fun (ys : ListType Name) => @ListType.rec Name
  (fun (ms : ListType Name) => @Eq Bool (nrb_names_eq_b (@ListType.nil Name) ms) Bool.true -> @Eq (ListType Name) (@ListType.nil Name) ms)
  (fun (_run : @Eq Bool Bool.true Bool.true) => @Eq.refl (ListType Name) (@ListType.nil Name))
  (fun (m : Name) (ms : ListType Name) (_ih : @Eq Bool (nrb_names_eq_b (@ListType.nil Name) ms) Bool.true -> @Eq (ListType Name) (@ListType.nil Name) ms) (bad : @Eq Bool Bool.false Bool.true) => bool_false_ne_true (@Eq (ListType Name) (@ListType.nil Name) (@ListType.cons Name m ms)) bad) ys)
 (fun (n : Name) (ns : ListType Name) (ih : forall (ys : ListType Name), @Eq Bool (nrb_names_eq_b ns ys) Bool.true -> @Eq (ListType Name) ns ys) (ys : ListType Name) => @ListType.rec Name
  (fun (ms : ListType Name) => @Eq Bool (nrb_names_eq_b (@ListType.cons Name n ns) ms) Bool.true -> @Eq (ListType Name) (@ListType.cons Name n ns) ms)
  (fun (bad : @Eq Bool Bool.false Bool.true) => bool_false_ne_true (@Eq (ListType Name) (@ListType.cons Name n ns) (@ListType.nil Name)) bad)
  (fun (m : Name) (ms : ListType Name) (_unused : @Eq Bool (nrb_names_eq_b (@ListType.cons Name n ns) ms) Bool.true -> @Eq (ListType Name) (@ListType.cons Name n ns) ms)
   (run : @Eq Bool (Bool.and (name_eqb n m) (nrb_names_eq_b ns ms)) Bool.true) =>
   universe_bridge_congr2 Name (ListType Name) (ListType Name) (fun (n0 : Name) (ns0 : ListType Name) => @ListType.cons Name n0 ns0) n m ns ms
    (name_eqb_eq n m (band_eq_true_left (name_eqb n m) (nrb_names_eq_b ns ms) run))
    (ih ms (band_eq_true_right (name_eqb n m) (nrb_names_eq_b ns ms) run))) ys) xs",
    ),
    DeclarationInput::Data(
        "nrb_names_unique_b",
        r"forall (xs : ListType Name), Bool",
        r"fun (xs : ListType Name) => @ListType.rec Name (fun (_ns : ListType Name) => Bool) Bool.true (fun (n : Name) (ns : ListType Name) (ih : Bool) => Bool.and (Bool.not (name_list_mem ns n)) ih) xs",
    ),
    DeclarationInput::Data(
        "nrb_nat_some_b",
        r"forall (n : Nat) (o : OptionType Nat), Bool",
        r"fun (n : Nat) (o : OptionType Nat) => nrb_option_b Nat (fun (m : Nat) => nat_eqb m n) o",
    ),
    DeclarationInput::Proof(
        "nrb_nat_some_sound",
        r"forall (n : Nat) (o : OptionType Nat), @Eq Bool (nrb_nat_some_b n o) Bool.true -> @Eq (OptionType Nat) o (@OptionType.some Nat n)",
        r"fun (n : Nat) (o : OptionType Nat) =>
 @OptionType.rec Nat
  (fun (q : OptionType Nat) => @Eq Bool (nrb_nat_some_b n q) Bool.true -> @Eq (OptionType Nat) q (@OptionType.some Nat n))
  (fun (bad : @Eq Bool Bool.false Bool.true) => bool_false_ne_true (@Eq (OptionType Nat) (@OptionType.none Nat) (@OptionType.some Nat n)) bad)
  (fun (m : Nat) (same : @Eq Bool (nat_eqb m n) Bool.true) =>
   Eq.cong Nat (OptionType Nat) (fun (j : Nat) => @OptionType.some Nat j) m n (nat_eqb_eq m n same)) o",
    ),
    DeclarationInput::Data(
        "nrb_reference",
        r"forall (first : KIndMeta), ListType KExpr",
        r"fun (first : KIndMeta) => list_take (kind_num_params first) (nig_pi_domains (kconst_type (kind_sig first)))",
    ),
    DeclarationInput::Data(
        "nrb_member_fields_b",
        r"forall (block : ListType Name) (first im : KIndMeta), Bool",
        r"fun (block : ListType Name) (first im : KIndMeta) =>
 Bool.and (nrb_names_eq_b (kind_all_names im) block) (Bool.and (nat_eqb (kind_num_params im) (kind_num_params first)) (Bool.and (nrb_names_eq_b (kconst_params (kind_sig im)) (kconst_params (kind_sig first))) (Bool.and (nig_pi_prefix_b (nrb_reference first) (kconst_type (kind_sig im))) (Bool.and (nrb_nat_some_b (kind_num_indices im) (nig_checked_indices (kind_num_params first) (kconst_type (kind_sig im)))) (Bool.true)))))",
    ),
    DeclarationInput::Data(
        "nrb_ctor_fields_b",
        r"forall (block : ListType Name) (first : KIndMeta) (family : Name) (im : KIndMeta) (ci : Nat) (cm : KCtorMeta), Bool",
        r"fun (block : ListType Name) (first : KIndMeta) (family : Name) (im : KIndMeta) (ci : Nat) (cm : KCtorMeta) =>
 Bool.and (name_eqb (kctor_parent cm) family) (Bool.and (nat_eqb (kctor_num_params cm) (kind_num_params first)) (Bool.and (nrb_names_eq_b (kconst_params (kctor_sig cm)) (kconst_params (kind_sig first))) (Bool.and (nat_eqb (kctor_index cm) ci) (Bool.and (nat_eqb (count_pi (kconst_type (kctor_sig cm))) (Nat.add (kind_num_params first) (kctor_num_fields cm))) (Bool.and (nig_pi_prefix_b (nrb_reference first) (kconst_type (kctor_sig cm))) (Bool.and (nig_strict_app_b block (nig_param_levels (kconst_params (kind_sig first))) family (count_pi (kconst_type (kctor_sig cm))) (kind_num_params first) (kind_num_indices im) (return_type (kconst_type (kctor_sig cm)))) (Bool.true)))))))",
    ),
    DeclarationInput::Data(
        "nrb_ctor_at_b",
        r"forall (env : IndCtorEnv) (block : ListType Name) (first : KIndMeta) (family : Name) (im : KIndMeta) (ci : Nat) (cn : Name), Bool",
        r"fun (env : IndCtorEnv) (block : ListType Name) (first : KIndMeta) (family : Name) (im : KIndMeta) (ci : Nat) (cn : Name) =>
 nrb_option_b KCtorMeta (fun (cm : KCtorMeta) => nrb_ctor_fields_b block first family im ci cm) (kctor_for env cn)",
    ),
    DeclarationInput::Data(
        "nrb_member_at_b",
        r"forall (env : IndCtorEnv) (block : ListType Name) (first : KIndMeta) (mi : Nat) (family : Name), Bool",
        r"fun (env : IndCtorEnv) (block : ListType Name) (first : KIndMeta) (_mi : Nat) (family : Name) =>
 nrb_option_b KIndMeta (fun (im : KIndMeta) => Bool.and (nrb_member_fields_b block first im) (nrb_all_index_b (nrb_ctor_at_b env block first family im) (kind_ctor_names im))) (kind_for env family)",
    ),
    DeclarationInput::Data(
        "nrb_block_fields_b",
        r"forall (env : IndCtorEnv) (block : ListType Name) (first : KIndMeta), Bool",
        r"fun (env : IndCtorEnv) (block : ListType Name) (first : KIndMeta) =>
 Bool.and (nat_eqb (list_length (nrb_reference first)) (kind_num_params first)) (Bool.and (nrb_names_unique_b block) (Bool.and (nrb_all_index_b (nrb_member_at_b env block first) block) (Bool.true)))",
    ),
    DeclarationInput::Data(
        "nrb_block_return_b",
        r"forall (env : IndCtorEnv) (block : ListType Name), Bool",
        r"fun (env : IndCtorEnv) (block : ListType Name) =>
 nrb_option_b Name (fun (first_name : Name) => nrb_option_b KIndMeta (fun (first : KIndMeta) => nrb_block_fields_b env block first) (kind_for env first_name)) (nrb_name_at block Nat.zero)",
    ),
    DeclarationInput::Proof(
        "nrb_block_walk_select",
        r"forall (env : IndCtorEnv) (block : ListType Name) (first_name : Name) (first : KIndMeta) (mi : Nat) (family : Name) (im : KIndMeta) (ci : Nat) (cn : Name) (cm : KCtorMeta), @Eq Bool (nrb_block_return_b env block) (Bool.true) -> @Eq (OptionType Name) (nrb_name_at block Nat.zero) (@OptionType.some Name (first_name)) -> @Eq (OptionType KIndMeta) (kind_for env first_name) (@OptionType.some KIndMeta (first)) -> @Eq (OptionType Name) (nrb_name_at block mi) (@OptionType.some Name (family)) -> @Eq (OptionType KIndMeta) (kind_for env family) (@OptionType.some KIndMeta (im)) -> @Eq (OptionType Name) (nrb_name_at (kind_ctor_names im) ci) (@OptionType.some Name (cn)) -> @Eq (OptionType KCtorMeta) (kctor_for env cn) (@OptionType.some KCtorMeta (cm)) -> forall (C : Type), (@Eq Bool (nrb_block_fields_b env block first) (Bool.true) -> @Eq Bool (nrb_member_fields_b block first im) (Bool.true) -> @Eq Bool (nrb_ctor_fields_b block first family im ci cm) (Bool.true) -> C) -> C",
        r"fun (env : IndCtorEnv) (block : ListType Name) (first_name : Name) (first : KIndMeta) (mi : Nat) (family : Name) (im : KIndMeta) (ci : Nat) (cn : Name) (cm : KCtorMeta) (run : @Eq Bool (nrb_block_return_b env block) (Bool.true)) (first_at : @Eq (OptionType Name) (nrb_name_at block Nat.zero) (@OptionType.some Name (first_name))) (first_lookup : @Eq (OptionType KIndMeta) (kind_for env first_name) (@OptionType.some KIndMeta (first))) (member_at : @Eq (OptionType Name) (nrb_name_at block mi) (@OptionType.some Name (family))) (member_lookup : @Eq (OptionType KIndMeta) (kind_for env family) (@OptionType.some KIndMeta (im))) (ctor_at : @Eq (OptionType Name) (nrb_name_at (kind_ctor_names im) ci) (@OptionType.some Name (cn))) (ctor_lookup : @Eq (OptionType KCtorMeta) (kctor_for env cn) (@OptionType.some KCtorMeta (cm))) (C : Type) (k : @Eq Bool (nrb_block_fields_b env block first) (Bool.true) -> @Eq Bool (nrb_member_fields_b block first im) (Bool.true) -> @Eq Bool (nrb_ctor_fields_b block first family im ci cm) (Bool.true) -> C) =>
 (fun (block_run : @Eq Bool (nrb_block_fields_b env block first) (Bool.true)) =>
  (fun (member_run : @Eq Bool (Bool.and (nrb_member_fields_b block first im) (nrb_all_index_b (nrb_ctor_at_b env block first family im) (kind_ctor_names im))) (Bool.true)) =>
   k block_run (band_eq_true_left (nrb_member_fields_b block first im) (nrb_all_index_b (nrb_ctor_at_b env block first family im) (kind_ctor_names im)) member_run) (nrb_option_selected KCtorMeta (fun (cm : KCtorMeta) => nrb_ctor_fields_b block first family im ci cm) (kctor_for env cn) (cm) (nrb_all_index_at (kind_ctor_names im) (nrb_ctor_at_b env block first family im) ci cn (band_eq_true_right (nrb_member_fields_b block first im) (nrb_all_index_b (nrb_ctor_at_b env block first family im) (kind_ctor_names im)) member_run) ctor_at) (ctor_lookup))) (nrb_option_selected KIndMeta (fun (im : KIndMeta) => Bool.and (nrb_member_fields_b block first im) (nrb_all_index_b (nrb_ctor_at_b env block first family im) (kind_ctor_names im))) (kind_for env family) (im) (nrb_all_index_at block (nrb_member_at_b env block first) mi family (band_eq_true_left (nrb_all_index_b (nrb_member_at_b env block first) block) (Bool.true) (band_eq_true_right (nrb_names_unique_b block) (Bool.and (nrb_all_index_b (nrb_member_at_b env block first) block) (Bool.true)) (band_eq_true_right (nat_eqb (list_length (nrb_reference first)) (kind_num_params first)) (Bool.and (nrb_names_unique_b block) (Bool.and (nrb_all_index_b (nrb_member_at_b env block first) block) (Bool.true))) (block_run)))) member_at) (member_lookup))) (nrb_option_selected KIndMeta (fun (first : KIndMeta) => nrb_block_fields_b env block first) (kind_for env first_name) (first) (nrb_option_selected Name (fun (first_name : Name) => nrb_option_b KIndMeta (fun (first : KIndMeta) => nrb_block_fields_b env block first) (kind_for env first_name)) (nrb_name_at block Nat.zero) (first_name) (run) (first_at)) (first_lookup))",
    ),
    DeclarationInput::Proof(
        "nrb_selected_constructor",
        r"forall (env : IndCtorEnv) (block : ListType Name) (first_name : Name) (first : KIndMeta) (mi : Nat) (family : Name) (im : KIndMeta) (ci : Nat) (cn : Name) (cm : KCtorMeta), @Eq Bool (nrb_block_return_b env block) (Bool.true) -> @Eq (OptionType Name) (nrb_name_at block Nat.zero) (@OptionType.some Name (first_name)) -> @Eq (OptionType KIndMeta) (kind_for env first_name) (@OptionType.some KIndMeta (first)) -> @Eq (OptionType Name) (nrb_name_at block mi) (@OptionType.some Name (family)) -> @Eq (OptionType KIndMeta) (kind_for env family) (@OptionType.some KIndMeta (im)) -> @Eq (OptionType Name) (nrb_name_at (kind_ctor_names im) ci) (@OptionType.some Name (cn)) -> @Eq (OptionType KCtorMeta) (kctor_for env cn) (@OptionType.some KCtorMeta (cm)) -> forall (C : Type), (@Eq Nat (list_length (nrb_reference first)) (kind_num_params first) -> @Eq Bool (nrb_names_unique_b block) (Bool.true) -> @Eq (ListType Name) (kind_all_names im) (block) -> @Eq Nat (kind_num_params im) (kind_num_params first) -> @Eq (ListType Name) (kconst_params (kind_sig im)) (kconst_params (kind_sig first)) -> @Eq Bool (nig_pi_prefix_b (nrb_reference first) (kconst_type (kind_sig im))) (Bool.true) -> @Eq (OptionType Nat) (nig_checked_indices (kind_num_params first) (kconst_type (kind_sig im))) (@OptionType.some Nat (kind_num_indices im)) -> @Eq Nat (count_pi (kconst_type (kind_sig im))) (Nat.add (kind_num_params first) (kind_num_indices im)) -> @Eq Name (kctor_parent cm) (family) -> @Eq Nat (kctor_num_params cm) (kind_num_params first) -> @Eq (ListType Name) (kconst_params (kctor_sig cm)) (kconst_params (kind_sig first)) -> @Eq Nat (kctor_index cm) (ci) -> @Eq Nat (count_pi (kconst_type (kctor_sig cm))) (Nat.add (kind_num_params first) (kctor_num_fields cm)) -> @Eq Bool (nig_pi_prefix_b (nrb_reference first) (kconst_type (kctor_sig cm))) (Bool.true) -> Le (kind_num_params first) (count_pi (kconst_type (kctor_sig cm))) -> NamedStrictAppFacts block (nig_param_levels (kconst_params (kind_sig first))) family (count_pi (kconst_type (kctor_sig cm))) (kind_num_params first) (kind_num_indices im) (return_type (kconst_type (kctor_sig cm))) -> C) -> C",
        r"fun (env : IndCtorEnv) (block : ListType Name) (first_name : Name) (first : KIndMeta) (mi : Nat) (family : Name) (im : KIndMeta) (ci : Nat) (cn : Name) (cm : KCtorMeta) (run : @Eq Bool (nrb_block_return_b env block) (Bool.true)) (first_at : @Eq (OptionType Name) (nrb_name_at block Nat.zero) (@OptionType.some Name (first_name))) (first_lookup : @Eq (OptionType KIndMeta) (kind_for env first_name) (@OptionType.some KIndMeta (first))) (member_at : @Eq (OptionType Name) (nrb_name_at block mi) (@OptionType.some Name (family))) (member_lookup : @Eq (OptionType KIndMeta) (kind_for env family) (@OptionType.some KIndMeta (im))) (ctor_at : @Eq (OptionType Name) (nrb_name_at (kind_ctor_names im) ci) (@OptionType.some Name (cn))) (ctor_lookup : @Eq (OptionType KCtorMeta) (kctor_for env cn) (@OptionType.some KCtorMeta (cm))) (C : Type) (k : @Eq Nat (list_length (nrb_reference first)) (kind_num_params first) -> @Eq Bool (nrb_names_unique_b block) (Bool.true) -> @Eq (ListType Name) (kind_all_names im) (block) -> @Eq Nat (kind_num_params im) (kind_num_params first) -> @Eq (ListType Name) (kconst_params (kind_sig im)) (kconst_params (kind_sig first)) -> @Eq Bool (nig_pi_prefix_b (nrb_reference first) (kconst_type (kind_sig im))) (Bool.true) -> @Eq (OptionType Nat) (nig_checked_indices (kind_num_params first) (kconst_type (kind_sig im))) (@OptionType.some Nat (kind_num_indices im)) -> @Eq Nat (count_pi (kconst_type (kind_sig im))) (Nat.add (kind_num_params first) (kind_num_indices im)) -> @Eq Name (kctor_parent cm) (family) -> @Eq Nat (kctor_num_params cm) (kind_num_params first) -> @Eq (ListType Name) (kconst_params (kctor_sig cm)) (kconst_params (kind_sig first)) -> @Eq Nat (kctor_index cm) (ci) -> @Eq Nat (count_pi (kconst_type (kctor_sig cm))) (Nat.add (kind_num_params first) (kctor_num_fields cm)) -> @Eq Bool (nig_pi_prefix_b (nrb_reference first) (kconst_type (kctor_sig cm))) (Bool.true) -> Le (kind_num_params first) (count_pi (kconst_type (kctor_sig cm))) -> NamedStrictAppFacts block (nig_param_levels (kconst_params (kind_sig first))) family (count_pi (kconst_type (kctor_sig cm))) (kind_num_params first) (kind_num_indices im) (return_type (kconst_type (kctor_sig cm))) -> C) =>
 nrb_block_walk_select env block first_name first mi family im ci cn cm run first_at first_lookup member_at member_lookup ctor_at ctor_lookup C
 (fun (hb : @Eq Bool (nrb_block_fields_b env block first) (Bool.true)) (hm : @Eq Bool (nrb_member_fields_b block first im) (Bool.true)) (hc : @Eq Bool (nrb_ctor_fields_b block first family im ci cm) (Bool.true)) =>
 k
  (nat_eqb_eq (list_length (nrb_reference first)) (kind_num_params first) (band_eq_true_left (nat_eqb (list_length (nrb_reference first)) (kind_num_params first)) (Bool.and (nrb_names_unique_b block) (Bool.and (nrb_all_index_b (nrb_member_at_b env block first) block) (Bool.true))) (hb)))
  (band_eq_true_left (nrb_names_unique_b block) (Bool.and (nrb_all_index_b (nrb_member_at_b env block first) block) (Bool.true)) (band_eq_true_right (nat_eqb (list_length (nrb_reference first)) (kind_num_params first)) (Bool.and (nrb_names_unique_b block) (Bool.and (nrb_all_index_b (nrb_member_at_b env block first) block) (Bool.true))) (hb)))
  (nrb_names_eq_sound (kind_all_names im) block (band_eq_true_left (nrb_names_eq_b (kind_all_names im) block) (Bool.and (nat_eqb (kind_num_params im) (kind_num_params first)) (Bool.and (nrb_names_eq_b (kconst_params (kind_sig im)) (kconst_params (kind_sig first))) (Bool.and (nig_pi_prefix_b (nrb_reference first) (kconst_type (kind_sig im))) (Bool.and (nrb_nat_some_b (kind_num_indices im) (nig_checked_indices (kind_num_params first) (kconst_type (kind_sig im)))) (Bool.true))))) (hm)))
  (nat_eqb_eq (kind_num_params im) (kind_num_params first) (band_eq_true_left (nat_eqb (kind_num_params im) (kind_num_params first)) (Bool.and (nrb_names_eq_b (kconst_params (kind_sig im)) (kconst_params (kind_sig first))) (Bool.and (nig_pi_prefix_b (nrb_reference first) (kconst_type (kind_sig im))) (Bool.and (nrb_nat_some_b (kind_num_indices im) (nig_checked_indices (kind_num_params first) (kconst_type (kind_sig im)))) (Bool.true)))) (band_eq_true_right (nrb_names_eq_b (kind_all_names im) block) (Bool.and (nat_eqb (kind_num_params im) (kind_num_params first)) (Bool.and (nrb_names_eq_b (kconst_params (kind_sig im)) (kconst_params (kind_sig first))) (Bool.and (nig_pi_prefix_b (nrb_reference first) (kconst_type (kind_sig im))) (Bool.and (nrb_nat_some_b (kind_num_indices im) (nig_checked_indices (kind_num_params first) (kconst_type (kind_sig im)))) (Bool.true))))) (hm))))
  (nrb_names_eq_sound (kconst_params (kind_sig im)) (kconst_params (kind_sig first)) (band_eq_true_left (nrb_names_eq_b (kconst_params (kind_sig im)) (kconst_params (kind_sig first))) (Bool.and (nig_pi_prefix_b (nrb_reference first) (kconst_type (kind_sig im))) (Bool.and (nrb_nat_some_b (kind_num_indices im) (nig_checked_indices (kind_num_params first) (kconst_type (kind_sig im)))) (Bool.true))) (band_eq_true_right (nat_eqb (kind_num_params im) (kind_num_params first)) (Bool.and (nrb_names_eq_b (kconst_params (kind_sig im)) (kconst_params (kind_sig first))) (Bool.and (nig_pi_prefix_b (nrb_reference first) (kconst_type (kind_sig im))) (Bool.and (nrb_nat_some_b (kind_num_indices im) (nig_checked_indices (kind_num_params first) (kconst_type (kind_sig im)))) (Bool.true)))) (band_eq_true_right (nrb_names_eq_b (kind_all_names im) block) (Bool.and (nat_eqb (kind_num_params im) (kind_num_params first)) (Bool.and (nrb_names_eq_b (kconst_params (kind_sig im)) (kconst_params (kind_sig first))) (Bool.and (nig_pi_prefix_b (nrb_reference first) (kconst_type (kind_sig im))) (Bool.and (nrb_nat_some_b (kind_num_indices im) (nig_checked_indices (kind_num_params first) (kconst_type (kind_sig im)))) (Bool.true))))) (hm)))))
  (band_eq_true_left (nig_pi_prefix_b (nrb_reference first) (kconst_type (kind_sig im))) (Bool.and (nrb_nat_some_b (kind_num_indices im) (nig_checked_indices (kind_num_params first) (kconst_type (kind_sig im)))) (Bool.true)) (band_eq_true_right (nrb_names_eq_b (kconst_params (kind_sig im)) (kconst_params (kind_sig first))) (Bool.and (nig_pi_prefix_b (nrb_reference first) (kconst_type (kind_sig im))) (Bool.and (nrb_nat_some_b (kind_num_indices im) (nig_checked_indices (kind_num_params first) (kconst_type (kind_sig im)))) (Bool.true))) (band_eq_true_right (nat_eqb (kind_num_params im) (kind_num_params first)) (Bool.and (nrb_names_eq_b (kconst_params (kind_sig im)) (kconst_params (kind_sig first))) (Bool.and (nig_pi_prefix_b (nrb_reference first) (kconst_type (kind_sig im))) (Bool.and (nrb_nat_some_b (kind_num_indices im) (nig_checked_indices (kind_num_params first) (kconst_type (kind_sig im)))) (Bool.true)))) (band_eq_true_right (nrb_names_eq_b (kind_all_names im) block) (Bool.and (nat_eqb (kind_num_params im) (kind_num_params first)) (Bool.and (nrb_names_eq_b (kconst_params (kind_sig im)) (kconst_params (kind_sig first))) (Bool.and (nig_pi_prefix_b (nrb_reference first) (kconst_type (kind_sig im))) (Bool.and (nrb_nat_some_b (kind_num_indices im) (nig_checked_indices (kind_num_params first) (kconst_type (kind_sig im)))) (Bool.true))))) (hm)))))
  (nrb_nat_some_sound (kind_num_indices im) (nig_checked_indices (kind_num_params first) (kconst_type (kind_sig im))) (band_eq_true_left (nrb_nat_some_b (kind_num_indices im) (nig_checked_indices (kind_num_params first) (kconst_type (kind_sig im)))) (Bool.true) (band_eq_true_right (nig_pi_prefix_b (nrb_reference first) (kconst_type (kind_sig im))) (Bool.and (nrb_nat_some_b (kind_num_indices im) (nig_checked_indices (kind_num_params first) (kconst_type (kind_sig im)))) (Bool.true)) (band_eq_true_right (nrb_names_eq_b (kconst_params (kind_sig im)) (kconst_params (kind_sig first))) (Bool.and (nig_pi_prefix_b (nrb_reference first) (kconst_type (kind_sig im))) (Bool.and (nrb_nat_some_b (kind_num_indices im) (nig_checked_indices (kind_num_params first) (kconst_type (kind_sig im)))) (Bool.true))) (band_eq_true_right (nat_eqb (kind_num_params im) (kind_num_params first)) (Bool.and (nrb_names_eq_b (kconst_params (kind_sig im)) (kconst_params (kind_sig first))) (Bool.and (nig_pi_prefix_b (nrb_reference first) (kconst_type (kind_sig im))) (Bool.and (nrb_nat_some_b (kind_num_indices im) (nig_checked_indices (kind_num_params first) (kconst_type (kind_sig im)))) (Bool.true)))) (band_eq_true_right (nrb_names_eq_b (kind_all_names im) block) (Bool.and (nat_eqb (kind_num_params im) (kind_num_params first)) (Bool.and (nrb_names_eq_b (kconst_params (kind_sig im)) (kconst_params (kind_sig first))) (Bool.and (nig_pi_prefix_b (nrb_reference first) (kconst_type (kind_sig im))) (Bool.and (nrb_nat_some_b (kind_num_indices im) (nig_checked_indices (kind_num_params first) (kconst_type (kind_sig im)))) (Bool.true))))) (hm)))))))
  (nig_checked_indices_sound (kind_num_params first) (kind_num_indices im) (kconst_type (kind_sig im)) (nrb_nat_some_sound (kind_num_indices im) (nig_checked_indices (kind_num_params first) (kconst_type (kind_sig im))) (band_eq_true_left (nrb_nat_some_b (kind_num_indices im) (nig_checked_indices (kind_num_params first) (kconst_type (kind_sig im)))) (Bool.true) (band_eq_true_right (nig_pi_prefix_b (nrb_reference first) (kconst_type (kind_sig im))) (Bool.and (nrb_nat_some_b (kind_num_indices im) (nig_checked_indices (kind_num_params first) (kconst_type (kind_sig im)))) (Bool.true)) (band_eq_true_right (nrb_names_eq_b (kconst_params (kind_sig im)) (kconst_params (kind_sig first))) (Bool.and (nig_pi_prefix_b (nrb_reference first) (kconst_type (kind_sig im))) (Bool.and (nrb_nat_some_b (kind_num_indices im) (nig_checked_indices (kind_num_params first) (kconst_type (kind_sig im)))) (Bool.true))) (band_eq_true_right (nat_eqb (kind_num_params im) (kind_num_params first)) (Bool.and (nrb_names_eq_b (kconst_params (kind_sig im)) (kconst_params (kind_sig first))) (Bool.and (nig_pi_prefix_b (nrb_reference first) (kconst_type (kind_sig im))) (Bool.and (nrb_nat_some_b (kind_num_indices im) (nig_checked_indices (kind_num_params first) (kconst_type (kind_sig im)))) (Bool.true)))) (band_eq_true_right (nrb_names_eq_b (kind_all_names im) block) (Bool.and (nat_eqb (kind_num_params im) (kind_num_params first)) (Bool.and (nrb_names_eq_b (kconst_params (kind_sig im)) (kconst_params (kind_sig first))) (Bool.and (nig_pi_prefix_b (nrb_reference first) (kconst_type (kind_sig im))) (Bool.and (nrb_nat_some_b (kind_num_indices im) (nig_checked_indices (kind_num_params first) (kconst_type (kind_sig im)))) (Bool.true))))) (hm))))))))
  (name_eqb_eq (kctor_parent cm) family (band_eq_true_left (name_eqb (kctor_parent cm) family) (Bool.and (nat_eqb (kctor_num_params cm) (kind_num_params first)) (Bool.and (nrb_names_eq_b (kconst_params (kctor_sig cm)) (kconst_params (kind_sig first))) (Bool.and (nat_eqb (kctor_index cm) ci) (Bool.and (nat_eqb (count_pi (kconst_type (kctor_sig cm))) (Nat.add (kind_num_params first) (kctor_num_fields cm))) (Bool.and (nig_pi_prefix_b (nrb_reference first) (kconst_type (kctor_sig cm))) (Bool.and (nig_strict_app_b block (nig_param_levels (kconst_params (kind_sig first))) family (count_pi (kconst_type (kctor_sig cm))) (kind_num_params first) (kind_num_indices im) (return_type (kconst_type (kctor_sig cm)))) (Bool.true))))))) (hc)))
  (nat_eqb_eq (kctor_num_params cm) (kind_num_params first) (band_eq_true_left (nat_eqb (kctor_num_params cm) (kind_num_params first)) (Bool.and (nrb_names_eq_b (kconst_params (kctor_sig cm)) (kconst_params (kind_sig first))) (Bool.and (nat_eqb (kctor_index cm) ci) (Bool.and (nat_eqb (count_pi (kconst_type (kctor_sig cm))) (Nat.add (kind_num_params first) (kctor_num_fields cm))) (Bool.and (nig_pi_prefix_b (nrb_reference first) (kconst_type (kctor_sig cm))) (Bool.and (nig_strict_app_b block (nig_param_levels (kconst_params (kind_sig first))) family (count_pi (kconst_type (kctor_sig cm))) (kind_num_params first) (kind_num_indices im) (return_type (kconst_type (kctor_sig cm)))) (Bool.true)))))) (band_eq_true_right (name_eqb (kctor_parent cm) family) (Bool.and (nat_eqb (kctor_num_params cm) (kind_num_params first)) (Bool.and (nrb_names_eq_b (kconst_params (kctor_sig cm)) (kconst_params (kind_sig first))) (Bool.and (nat_eqb (kctor_index cm) ci) (Bool.and (nat_eqb (count_pi (kconst_type (kctor_sig cm))) (Nat.add (kind_num_params first) (kctor_num_fields cm))) (Bool.and (nig_pi_prefix_b (nrb_reference first) (kconst_type (kctor_sig cm))) (Bool.and (nig_strict_app_b block (nig_param_levels (kconst_params (kind_sig first))) family (count_pi (kconst_type (kctor_sig cm))) (kind_num_params first) (kind_num_indices im) (return_type (kconst_type (kctor_sig cm)))) (Bool.true))))))) (hc))))
  (nrb_names_eq_sound (kconst_params (kctor_sig cm)) (kconst_params (kind_sig first)) (band_eq_true_left (nrb_names_eq_b (kconst_params (kctor_sig cm)) (kconst_params (kind_sig first))) (Bool.and (nat_eqb (kctor_index cm) ci) (Bool.and (nat_eqb (count_pi (kconst_type (kctor_sig cm))) (Nat.add (kind_num_params first) (kctor_num_fields cm))) (Bool.and (nig_pi_prefix_b (nrb_reference first) (kconst_type (kctor_sig cm))) (Bool.and (nig_strict_app_b block (nig_param_levels (kconst_params (kind_sig first))) family (count_pi (kconst_type (kctor_sig cm))) (kind_num_params first) (kind_num_indices im) (return_type (kconst_type (kctor_sig cm)))) (Bool.true))))) (band_eq_true_right (nat_eqb (kctor_num_params cm) (kind_num_params first)) (Bool.and (nrb_names_eq_b (kconst_params (kctor_sig cm)) (kconst_params (kind_sig first))) (Bool.and (nat_eqb (kctor_index cm) ci) (Bool.and (nat_eqb (count_pi (kconst_type (kctor_sig cm))) (Nat.add (kind_num_params first) (kctor_num_fields cm))) (Bool.and (nig_pi_prefix_b (nrb_reference first) (kconst_type (kctor_sig cm))) (Bool.and (nig_strict_app_b block (nig_param_levels (kconst_params (kind_sig first))) family (count_pi (kconst_type (kctor_sig cm))) (kind_num_params first) (kind_num_indices im) (return_type (kconst_type (kctor_sig cm)))) (Bool.true)))))) (band_eq_true_right (name_eqb (kctor_parent cm) family) (Bool.and (nat_eqb (kctor_num_params cm) (kind_num_params first)) (Bool.and (nrb_names_eq_b (kconst_params (kctor_sig cm)) (kconst_params (kind_sig first))) (Bool.and (nat_eqb (kctor_index cm) ci) (Bool.and (nat_eqb (count_pi (kconst_type (kctor_sig cm))) (Nat.add (kind_num_params first) (kctor_num_fields cm))) (Bool.and (nig_pi_prefix_b (nrb_reference first) (kconst_type (kctor_sig cm))) (Bool.and (nig_strict_app_b block (nig_param_levels (kconst_params (kind_sig first))) family (count_pi (kconst_type (kctor_sig cm))) (kind_num_params first) (kind_num_indices im) (return_type (kconst_type (kctor_sig cm)))) (Bool.true))))))) (hc)))))
  (nat_eqb_eq (kctor_index cm) ci (band_eq_true_left (nat_eqb (kctor_index cm) ci) (Bool.and (nat_eqb (count_pi (kconst_type (kctor_sig cm))) (Nat.add (kind_num_params first) (kctor_num_fields cm))) (Bool.and (nig_pi_prefix_b (nrb_reference first) (kconst_type (kctor_sig cm))) (Bool.and (nig_strict_app_b block (nig_param_levels (kconst_params (kind_sig first))) family (count_pi (kconst_type (kctor_sig cm))) (kind_num_params first) (kind_num_indices im) (return_type (kconst_type (kctor_sig cm)))) (Bool.true)))) (band_eq_true_right (nrb_names_eq_b (kconst_params (kctor_sig cm)) (kconst_params (kind_sig first))) (Bool.and (nat_eqb (kctor_index cm) ci) (Bool.and (nat_eqb (count_pi (kconst_type (kctor_sig cm))) (Nat.add (kind_num_params first) (kctor_num_fields cm))) (Bool.and (nig_pi_prefix_b (nrb_reference first) (kconst_type (kctor_sig cm))) (Bool.and (nig_strict_app_b block (nig_param_levels (kconst_params (kind_sig first))) family (count_pi (kconst_type (kctor_sig cm))) (kind_num_params first) (kind_num_indices im) (return_type (kconst_type (kctor_sig cm)))) (Bool.true))))) (band_eq_true_right (nat_eqb (kctor_num_params cm) (kind_num_params first)) (Bool.and (nrb_names_eq_b (kconst_params (kctor_sig cm)) (kconst_params (kind_sig first))) (Bool.and (nat_eqb (kctor_index cm) ci) (Bool.and (nat_eqb (count_pi (kconst_type (kctor_sig cm))) (Nat.add (kind_num_params first) (kctor_num_fields cm))) (Bool.and (nig_pi_prefix_b (nrb_reference first) (kconst_type (kctor_sig cm))) (Bool.and (nig_strict_app_b block (nig_param_levels (kconst_params (kind_sig first))) family (count_pi (kconst_type (kctor_sig cm))) (kind_num_params first) (kind_num_indices im) (return_type (kconst_type (kctor_sig cm)))) (Bool.true)))))) (band_eq_true_right (name_eqb (kctor_parent cm) family) (Bool.and (nat_eqb (kctor_num_params cm) (kind_num_params first)) (Bool.and (nrb_names_eq_b (kconst_params (kctor_sig cm)) (kconst_params (kind_sig first))) (Bool.and (nat_eqb (kctor_index cm) ci) (Bool.and (nat_eqb (count_pi (kconst_type (kctor_sig cm))) (Nat.add (kind_num_params first) (kctor_num_fields cm))) (Bool.and (nig_pi_prefix_b (nrb_reference first) (kconst_type (kctor_sig cm))) (Bool.and (nig_strict_app_b block (nig_param_levels (kconst_params (kind_sig first))) family (count_pi (kconst_type (kctor_sig cm))) (kind_num_params first) (kind_num_indices im) (return_type (kconst_type (kctor_sig cm)))) (Bool.true))))))) (hc))))))
  (nat_eqb_eq (count_pi (kconst_type (kctor_sig cm))) (Nat.add (kind_num_params first) (kctor_num_fields cm)) (band_eq_true_left (nat_eqb (count_pi (kconst_type (kctor_sig cm))) (Nat.add (kind_num_params first) (kctor_num_fields cm))) (Bool.and (nig_pi_prefix_b (nrb_reference first) (kconst_type (kctor_sig cm))) (Bool.and (nig_strict_app_b block (nig_param_levels (kconst_params (kind_sig first))) family (count_pi (kconst_type (kctor_sig cm))) (kind_num_params first) (kind_num_indices im) (return_type (kconst_type (kctor_sig cm)))) (Bool.true))) (band_eq_true_right (nat_eqb (kctor_index cm) ci) (Bool.and (nat_eqb (count_pi (kconst_type (kctor_sig cm))) (Nat.add (kind_num_params first) (kctor_num_fields cm))) (Bool.and (nig_pi_prefix_b (nrb_reference first) (kconst_type (kctor_sig cm))) (Bool.and (nig_strict_app_b block (nig_param_levels (kconst_params (kind_sig first))) family (count_pi (kconst_type (kctor_sig cm))) (kind_num_params first) (kind_num_indices im) (return_type (kconst_type (kctor_sig cm)))) (Bool.true)))) (band_eq_true_right (nrb_names_eq_b (kconst_params (kctor_sig cm)) (kconst_params (kind_sig first))) (Bool.and (nat_eqb (kctor_index cm) ci) (Bool.and (nat_eqb (count_pi (kconst_type (kctor_sig cm))) (Nat.add (kind_num_params first) (kctor_num_fields cm))) (Bool.and (nig_pi_prefix_b (nrb_reference first) (kconst_type (kctor_sig cm))) (Bool.and (nig_strict_app_b block (nig_param_levels (kconst_params (kind_sig first))) family (count_pi (kconst_type (kctor_sig cm))) (kind_num_params first) (kind_num_indices im) (return_type (kconst_type (kctor_sig cm)))) (Bool.true))))) (band_eq_true_right (nat_eqb (kctor_num_params cm) (kind_num_params first)) (Bool.and (nrb_names_eq_b (kconst_params (kctor_sig cm)) (kconst_params (kind_sig first))) (Bool.and (nat_eqb (kctor_index cm) ci) (Bool.and (nat_eqb (count_pi (kconst_type (kctor_sig cm))) (Nat.add (kind_num_params first) (kctor_num_fields cm))) (Bool.and (nig_pi_prefix_b (nrb_reference first) (kconst_type (kctor_sig cm))) (Bool.and (nig_strict_app_b block (nig_param_levels (kconst_params (kind_sig first))) family (count_pi (kconst_type (kctor_sig cm))) (kind_num_params first) (kind_num_indices im) (return_type (kconst_type (kctor_sig cm)))) (Bool.true)))))) (band_eq_true_right (name_eqb (kctor_parent cm) family) (Bool.and (nat_eqb (kctor_num_params cm) (kind_num_params first)) (Bool.and (nrb_names_eq_b (kconst_params (kctor_sig cm)) (kconst_params (kind_sig first))) (Bool.and (nat_eqb (kctor_index cm) ci) (Bool.and (nat_eqb (count_pi (kconst_type (kctor_sig cm))) (Nat.add (kind_num_params first) (kctor_num_fields cm))) (Bool.and (nig_pi_prefix_b (nrb_reference first) (kconst_type (kctor_sig cm))) (Bool.and (nig_strict_app_b block (nig_param_levels (kconst_params (kind_sig first))) family (count_pi (kconst_type (kctor_sig cm))) (kind_num_params first) (kind_num_indices im) (return_type (kconst_type (kctor_sig cm)))) (Bool.true))))))) (hc)))))))
  (band_eq_true_left (nig_pi_prefix_b (nrb_reference first) (kconst_type (kctor_sig cm))) (Bool.and (nig_strict_app_b block (nig_param_levels (kconst_params (kind_sig first))) family (count_pi (kconst_type (kctor_sig cm))) (kind_num_params first) (kind_num_indices im) (return_type (kconst_type (kctor_sig cm)))) (Bool.true)) (band_eq_true_right (nat_eqb (count_pi (kconst_type (kctor_sig cm))) (Nat.add (kind_num_params first) (kctor_num_fields cm))) (Bool.and (nig_pi_prefix_b (nrb_reference first) (kconst_type (kctor_sig cm))) (Bool.and (nig_strict_app_b block (nig_param_levels (kconst_params (kind_sig first))) family (count_pi (kconst_type (kctor_sig cm))) (kind_num_params first) (kind_num_indices im) (return_type (kconst_type (kctor_sig cm)))) (Bool.true))) (band_eq_true_right (nat_eqb (kctor_index cm) ci) (Bool.and (nat_eqb (count_pi (kconst_type (kctor_sig cm))) (Nat.add (kind_num_params first) (kctor_num_fields cm))) (Bool.and (nig_pi_prefix_b (nrb_reference first) (kconst_type (kctor_sig cm))) (Bool.and (nig_strict_app_b block (nig_param_levels (kconst_params (kind_sig first))) family (count_pi (kconst_type (kctor_sig cm))) (kind_num_params first) (kind_num_indices im) (return_type (kconst_type (kctor_sig cm)))) (Bool.true)))) (band_eq_true_right (nrb_names_eq_b (kconst_params (kctor_sig cm)) (kconst_params (kind_sig first))) (Bool.and (nat_eqb (kctor_index cm) ci) (Bool.and (nat_eqb (count_pi (kconst_type (kctor_sig cm))) (Nat.add (kind_num_params first) (kctor_num_fields cm))) (Bool.and (nig_pi_prefix_b (nrb_reference first) (kconst_type (kctor_sig cm))) (Bool.and (nig_strict_app_b block (nig_param_levels (kconst_params (kind_sig first))) family (count_pi (kconst_type (kctor_sig cm))) (kind_num_params first) (kind_num_indices im) (return_type (kconst_type (kctor_sig cm)))) (Bool.true))))) (band_eq_true_right (nat_eqb (kctor_num_params cm) (kind_num_params first)) (Bool.and (nrb_names_eq_b (kconst_params (kctor_sig cm)) (kconst_params (kind_sig first))) (Bool.and (nat_eqb (kctor_index cm) ci) (Bool.and (nat_eqb (count_pi (kconst_type (kctor_sig cm))) (Nat.add (kind_num_params first) (kctor_num_fields cm))) (Bool.and (nig_pi_prefix_b (nrb_reference first) (kconst_type (kctor_sig cm))) (Bool.and (nig_strict_app_b block (nig_param_levels (kconst_params (kind_sig first))) family (count_pi (kconst_type (kctor_sig cm))) (kind_num_params first) (kind_num_indices im) (return_type (kconst_type (kctor_sig cm)))) (Bool.true)))))) (band_eq_true_right (name_eqb (kctor_parent cm) family) (Bool.and (nat_eqb (kctor_num_params cm) (kind_num_params first)) (Bool.and (nrb_names_eq_b (kconst_params (kctor_sig cm)) (kconst_params (kind_sig first))) (Bool.and (nat_eqb (kctor_index cm) ci) (Bool.and (nat_eqb (count_pi (kconst_type (kctor_sig cm))) (Nat.add (kind_num_params first) (kctor_num_fields cm))) (Bool.and (nig_pi_prefix_b (nrb_reference first) (kconst_type (kctor_sig cm))) (Bool.and (nig_strict_app_b block (nig_param_levels (kconst_params (kind_sig first))) family (count_pi (kconst_type (kctor_sig cm))) (kind_num_params first) (kind_num_indices im) (return_type (kconst_type (kctor_sig cm)))) (Bool.true))))))) (hc)))))))
  (Eq.subst Nat (fun (p0 : Nat) => Le p0 (count_pi (kconst_type (kctor_sig cm)))) (list_length (nrb_reference first)) (kind_num_params first) (nat_eqb_eq (list_length (nrb_reference first)) (kind_num_params first) (band_eq_true_left (nat_eqb (list_length (nrb_reference first)) (kind_num_params first)) (Bool.and (nrb_names_unique_b block) (Bool.and (nrb_all_index_b (nrb_member_at_b env block first) block) (Bool.true))) (hb))) (nig_prefix_bound (nrb_reference first) (kconst_type (kctor_sig cm)) (band_eq_true_left (nig_pi_prefix_b (nrb_reference first) (kconst_type (kctor_sig cm))) (Bool.and (nig_strict_app_b block (nig_param_levels (kconst_params (kind_sig first))) family (count_pi (kconst_type (kctor_sig cm))) (kind_num_params first) (kind_num_indices im) (return_type (kconst_type (kctor_sig cm)))) (Bool.true)) (band_eq_true_right (nat_eqb (count_pi (kconst_type (kctor_sig cm))) (Nat.add (kind_num_params first) (kctor_num_fields cm))) (Bool.and (nig_pi_prefix_b (nrb_reference first) (kconst_type (kctor_sig cm))) (Bool.and (nig_strict_app_b block (nig_param_levels (kconst_params (kind_sig first))) family (count_pi (kconst_type (kctor_sig cm))) (kind_num_params first) (kind_num_indices im) (return_type (kconst_type (kctor_sig cm)))) (Bool.true))) (band_eq_true_right (nat_eqb (kctor_index cm) ci) (Bool.and (nat_eqb (count_pi (kconst_type (kctor_sig cm))) (Nat.add (kind_num_params first) (kctor_num_fields cm))) (Bool.and (nig_pi_prefix_b (nrb_reference first) (kconst_type (kctor_sig cm))) (Bool.and (nig_strict_app_b block (nig_param_levels (kconst_params (kind_sig first))) family (count_pi (kconst_type (kctor_sig cm))) (kind_num_params first) (kind_num_indices im) (return_type (kconst_type (kctor_sig cm)))) (Bool.true)))) (band_eq_true_right (nrb_names_eq_b (kconst_params (kctor_sig cm)) (kconst_params (kind_sig first))) (Bool.and (nat_eqb (kctor_index cm) ci) (Bool.and (nat_eqb (count_pi (kconst_type (kctor_sig cm))) (Nat.add (kind_num_params first) (kctor_num_fields cm))) (Bool.and (nig_pi_prefix_b (nrb_reference first) (kconst_type (kctor_sig cm))) (Bool.and (nig_strict_app_b block (nig_param_levels (kconst_params (kind_sig first))) family (count_pi (kconst_type (kctor_sig cm))) (kind_num_params first) (kind_num_indices im) (return_type (kconst_type (kctor_sig cm)))) (Bool.true))))) (band_eq_true_right (nat_eqb (kctor_num_params cm) (kind_num_params first)) (Bool.and (nrb_names_eq_b (kconst_params (kctor_sig cm)) (kconst_params (kind_sig first))) (Bool.and (nat_eqb (kctor_index cm) ci) (Bool.and (nat_eqb (count_pi (kconst_type (kctor_sig cm))) (Nat.add (kind_num_params first) (kctor_num_fields cm))) (Bool.and (nig_pi_prefix_b (nrb_reference first) (kconst_type (kctor_sig cm))) (Bool.and (nig_strict_app_b block (nig_param_levels (kconst_params (kind_sig first))) family (count_pi (kconst_type (kctor_sig cm))) (kind_num_params first) (kind_num_indices im) (return_type (kconst_type (kctor_sig cm)))) (Bool.true)))))) (band_eq_true_right (name_eqb (kctor_parent cm) family) (Bool.and (nat_eqb (kctor_num_params cm) (kind_num_params first)) (Bool.and (nrb_names_eq_b (kconst_params (kctor_sig cm)) (kconst_params (kind_sig first))) (Bool.and (nat_eqb (kctor_index cm) ci) (Bool.and (nat_eqb (count_pi (kconst_type (kctor_sig cm))) (Nat.add (kind_num_params first) (kctor_num_fields cm))) (Bool.and (nig_pi_prefix_b (nrb_reference first) (kconst_type (kctor_sig cm))) (Bool.and (nig_strict_app_b block (nig_param_levels (kconst_params (kind_sig first))) family (count_pi (kconst_type (kctor_sig cm))) (kind_num_params first) (kind_num_indices im) (return_type (kconst_type (kctor_sig cm)))) (Bool.true))))))) (hc)))))))))
  (nig_strict_sound block (nig_param_levels (kconst_params (kind_sig first))) family (count_pi (kconst_type (kctor_sig cm))) (kind_num_params first) (kind_num_indices im) (return_type (kconst_type (kctor_sig cm))) (band_eq_true_left (nig_strict_app_b block (nig_param_levels (kconst_params (kind_sig first))) family (count_pi (kconst_type (kctor_sig cm))) (kind_num_params first) (kind_num_indices im) (return_type (kconst_type (kctor_sig cm)))) (Bool.true) (band_eq_true_right (nig_pi_prefix_b (nrb_reference first) (kconst_type (kctor_sig cm))) (Bool.and (nig_strict_app_b block (nig_param_levels (kconst_params (kind_sig first))) family (count_pi (kconst_type (kctor_sig cm))) (kind_num_params first) (kind_num_indices im) (return_type (kconst_type (kctor_sig cm)))) (Bool.true)) (band_eq_true_right (nat_eqb (count_pi (kconst_type (kctor_sig cm))) (Nat.add (kind_num_params first) (kctor_num_fields cm))) (Bool.and (nig_pi_prefix_b (nrb_reference first) (kconst_type (kctor_sig cm))) (Bool.and (nig_strict_app_b block (nig_param_levels (kconst_params (kind_sig first))) family (count_pi (kconst_type (kctor_sig cm))) (kind_num_params first) (kind_num_indices im) (return_type (kconst_type (kctor_sig cm)))) (Bool.true))) (band_eq_true_right (nat_eqb (kctor_index cm) ci) (Bool.and (nat_eqb (count_pi (kconst_type (kctor_sig cm))) (Nat.add (kind_num_params first) (kctor_num_fields cm))) (Bool.and (nig_pi_prefix_b (nrb_reference first) (kconst_type (kctor_sig cm))) (Bool.and (nig_strict_app_b block (nig_param_levels (kconst_params (kind_sig first))) family (count_pi (kconst_type (kctor_sig cm))) (kind_num_params first) (kind_num_indices im) (return_type (kconst_type (kctor_sig cm)))) (Bool.true)))) (band_eq_true_right (nrb_names_eq_b (kconst_params (kctor_sig cm)) (kconst_params (kind_sig first))) (Bool.and (nat_eqb (kctor_index cm) ci) (Bool.and (nat_eqb (count_pi (kconst_type (kctor_sig cm))) (Nat.add (kind_num_params first) (kctor_num_fields cm))) (Bool.and (nig_pi_prefix_b (nrb_reference first) (kconst_type (kctor_sig cm))) (Bool.and (nig_strict_app_b block (nig_param_levels (kconst_params (kind_sig first))) family (count_pi (kconst_type (kctor_sig cm))) (kind_num_params first) (kind_num_indices im) (return_type (kconst_type (kctor_sig cm)))) (Bool.true))))) (band_eq_true_right (nat_eqb (kctor_num_params cm) (kind_num_params first)) (Bool.and (nrb_names_eq_b (kconst_params (kctor_sig cm)) (kconst_params (kind_sig first))) (Bool.and (nat_eqb (kctor_index cm) ci) (Bool.and (nat_eqb (count_pi (kconst_type (kctor_sig cm))) (Nat.add (kind_num_params first) (kctor_num_fields cm))) (Bool.and (nig_pi_prefix_b (nrb_reference first) (kconst_type (kctor_sig cm))) (Bool.and (nig_strict_app_b block (nig_param_levels (kconst_params (kind_sig first))) family (count_pi (kconst_type (kctor_sig cm))) (kind_num_params first) (kind_num_indices im) (return_type (kconst_type (kctor_sig cm)))) (Bool.true)))))) (band_eq_true_right (name_eqb (kctor_parent cm) family) (Bool.and (nat_eqb (kctor_num_params cm) (kind_num_params first)) (Bool.and (nrb_names_eq_b (kconst_params (kctor_sig cm)) (kconst_params (kind_sig first))) (Bool.and (nat_eqb (kctor_index cm) ci) (Bool.and (nat_eqb (count_pi (kconst_type (kctor_sig cm))) (Nat.add (kind_num_params first) (kctor_num_fields cm))) (Bool.and (nig_pi_prefix_b (nrb_reference first) (kconst_type (kctor_sig cm))) (Bool.and (nig_strict_app_b block (nig_param_levels (kconst_params (kind_sig first))) family (count_pi (kconst_type (kctor_sig cm))) (kind_num_params first) (kind_num_indices im) (return_type (kconst_type (kctor_sig cm)))) (Bool.true))))))) (hc))))))))))",
    ),
    DeclarationInput::Data("nrb_demo_f", r"Name", r"Name.anonymous"),
    DeclarationInput::Data("nrb_demo_g", r"Name", r"Name.str Name.anonymous Nat.zero"),
    DeclarationInput::Data(
        "nrb_demo_cf",
        r"Name",
        r"Name.str Name.anonymous (Nat.succ Nat.zero)",
    ),
    DeclarationInput::Data(
        "nrb_demo_cg",
        r"Name",
        r"Name.str Name.anonymous (Nat.succ (Nat.succ Nat.zero))",
    ),
    DeclarationInput::Data(
        "nrb_demo_u",
        r"Name",
        r"Name.str (Name.str Name.anonymous Nat.zero) Nat.zero",
    ),
    DeclarationInput::Data(
        "nrb_demo_levels",
        r"ListType Name",
        r"@ListType.cons Name (nrb_demo_u) (@ListType.nil Name)",
    ),
    DeclarationInput::Data(
        "nrb_demo_block",
        r"ListType Name",
        r"@ListType.cons Name (nrb_demo_f) (@ListType.cons Name (nrb_demo_g) (@ListType.nil Name))",
    ),
    DeclarationInput::Data(
        "nrb_demo_domain",
        r"KExpr",
        r"KExpr.sort (Level.param nrb_demo_u)",
    ),
    DeclarationInput::Data(
        "nrb_demo_f_type",
        r"KExpr",
        r"KExpr.pi nrb_demo_domain nrb_demo_domain",
    ),
    DeclarationInput::Data(
        "nrb_demo_g_type",
        r"KExpr",
        r"KExpr.pi nrb_demo_domain (KExpr.pi (KExpr.bvar Nat.zero) nrb_demo_domain)",
    ),
    DeclarationInput::Data(
        "nrb_demo_cf_type",
        r"KExpr",
        r"KExpr.pi nrb_demo_domain (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.app (KExpr.const nrb_demo_f (nig_param_levels nrb_demo_levels)) (KExpr.bvar (Nat.succ Nat.zero))))",
    ),
    DeclarationInput::Data(
        "nrb_demo_cg_type",
        r"KExpr",
        r"KExpr.pi nrb_demo_domain (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.app (KExpr.app (KExpr.const nrb_demo_g (nig_param_levels nrb_demo_levels)) (KExpr.bvar (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)))",
    ),
    DeclarationInput::Data(
        "nrb_demo_f_meta",
        r"KIndMeta",
        r"KIndMeta.mk (KConstSig.mk nrb_demo_levels nrb_demo_f_type) (Nat.succ Nat.zero) Nat.zero (@ListType.cons Name (nrb_demo_cf) (@ListType.nil Name)) nrb_demo_block",
    ),
    DeclarationInput::Data(
        "nrb_demo_g_meta",
        r"KIndMeta",
        r"KIndMeta.mk (KConstSig.mk nrb_demo_levels nrb_demo_g_type) (Nat.succ Nat.zero) (Nat.succ Nat.zero) (@ListType.cons Name (nrb_demo_cg) (@ListType.nil Name)) nrb_demo_block",
    ),
    DeclarationInput::Data(
        "nrb_demo_cf_meta",
        r"KCtorMeta",
        r"KCtorMeta.mk (KConstSig.mk nrb_demo_levels nrb_demo_cf_type) nrb_demo_f (Nat.succ Nat.zero) (Nat.succ Nat.zero) Nat.zero",
    ),
    DeclarationInput::Data(
        "nrb_demo_cg_meta",
        r"KCtorMeta",
        r"KCtorMeta.mk (KConstSig.mk nrb_demo_levels nrb_demo_cg_type) nrb_demo_g (Nat.succ Nat.zero) (Nat.succ Nat.zero) Nat.zero",
    ),
    DeclarationInput::Data(
        "nrb_demo_env",
        r"IndCtorEnv",
        r"IndCtorEnv.addCtor (IndCtorEnv.addCtor (IndCtorEnv.addInd (IndCtorEnv.addInd IndCtorEnv.empty nrb_demo_f nrb_demo_f_meta) nrb_demo_g nrb_demo_g_meta) nrb_demo_cf nrb_demo_cf_meta) nrb_demo_cg nrb_demo_cg_meta",
    ),
    DeclarationInput::Proof(
        "nrb_demo_whole",
        r"@Eq Bool (nrb_block_return_b nrb_demo_env nrb_demo_block) (Bool.true)",
        r"@Eq.refl Bool Bool.true",
    ),
    DeclarationInput::Proof(
        "nrb_demo_selected_g",
        r"NamedStrictAppFacts (nrb_demo_block) (nig_param_levels (kconst_params (kind_sig (nrb_demo_f_meta)))) (nrb_demo_g) (count_pi (kconst_type (kctor_sig (nrb_demo_cg_meta)))) (kind_num_params (nrb_demo_f_meta)) (kind_num_indices (nrb_demo_g_meta)) (return_type (kconst_type (kctor_sig (nrb_demo_cg_meta))))",
        r"nrb_selected_constructor nrb_demo_env nrb_demo_block nrb_demo_f nrb_demo_f_meta (Nat.succ Nat.zero) nrb_demo_g nrb_demo_g_meta Nat.zero nrb_demo_cg nrb_demo_cg_meta nrb_demo_whole
 (@Eq.refl (OptionType Name) (@OptionType.some Name ((nrb_demo_f))))
 (@Eq.refl (OptionType KIndMeta) (@OptionType.some KIndMeta ((nrb_demo_f_meta))))
 (@Eq.refl (OptionType Name) (@OptionType.some Name ((nrb_demo_g))))
 (@Eq.refl (OptionType KIndMeta) (@OptionType.some KIndMeta ((nrb_demo_g_meta))))
 (@Eq.refl (OptionType Name) (@OptionType.some Name ((nrb_demo_cg))))
 (@Eq.refl (OptionType KCtorMeta) (@OptionType.some KCtorMeta ((nrb_demo_cg_meta))))
 (NamedStrictAppFacts (nrb_demo_block) (nig_param_levels (kconst_params (kind_sig (nrb_demo_f_meta)))) (nrb_demo_g) (count_pi (kconst_type (kctor_sig (nrb_demo_cg_meta)))) (kind_num_params (nrb_demo_f_meta)) (kind_num_indices (nrb_demo_g_meta)) (return_type (kconst_type (kctor_sig (nrb_demo_cg_meta))))) (fun (h0 : @Eq Nat (list_length (nrb_reference (nrb_demo_f_meta))) (kind_num_params (nrb_demo_f_meta))) (h1 : @Eq Bool (nrb_names_unique_b (nrb_demo_block)) (Bool.true)) (h2 : @Eq (ListType Name) (kind_all_names (nrb_demo_g_meta)) ((nrb_demo_block))) (h3 : @Eq Nat (kind_num_params (nrb_demo_g_meta)) (kind_num_params (nrb_demo_f_meta))) (h4 : @Eq (ListType Name) (kconst_params (kind_sig (nrb_demo_g_meta))) (kconst_params (kind_sig (nrb_demo_f_meta)))) (h5 : @Eq Bool (nig_pi_prefix_b (nrb_reference (nrb_demo_f_meta)) (kconst_type (kind_sig (nrb_demo_g_meta)))) (Bool.true)) (h6 : @Eq (OptionType Nat) (nig_checked_indices (kind_num_params (nrb_demo_f_meta)) (kconst_type (kind_sig (nrb_demo_g_meta)))) (@OptionType.some Nat (kind_num_indices (nrb_demo_g_meta)))) (h7 : @Eq Nat (count_pi (kconst_type (kind_sig (nrb_demo_g_meta)))) (Nat.add (kind_num_params (nrb_demo_f_meta)) (kind_num_indices (nrb_demo_g_meta)))) (h8 : @Eq Name (kctor_parent (nrb_demo_cg_meta)) ((nrb_demo_g))) (h9 : @Eq Nat (kctor_num_params (nrb_demo_cg_meta)) (kind_num_params (nrb_demo_f_meta))) (h10 : @Eq (ListType Name) (kconst_params (kctor_sig (nrb_demo_cg_meta))) (kconst_params (kind_sig (nrb_demo_f_meta)))) (h11 : @Eq Nat (kctor_index (nrb_demo_cg_meta)) ((Nat.zero))) (h12 : @Eq Nat (count_pi (kconst_type (kctor_sig (nrb_demo_cg_meta)))) (Nat.add (kind_num_params (nrb_demo_f_meta)) (kctor_num_fields (nrb_demo_cg_meta)))) (h13 : @Eq Bool (nig_pi_prefix_b (nrb_reference (nrb_demo_f_meta)) (kconst_type (kctor_sig (nrb_demo_cg_meta)))) (Bool.true)) (h14 : Le (kind_num_params (nrb_demo_f_meta)) (count_pi (kconst_type (kctor_sig (nrb_demo_cg_meta))))) (h15 : NamedStrictAppFacts (nrb_demo_block) (nig_param_levels (kconst_params (kind_sig (nrb_demo_f_meta)))) (nrb_demo_g) (count_pi (kconst_type (kctor_sig (nrb_demo_cg_meta)))) (kind_num_params (nrb_demo_f_meta)) (kind_num_indices (nrb_demo_g_meta)) (return_type (kconst_type (kctor_sig (nrb_demo_cg_meta))))) => h15)",
    ),
    DeclarationInput::Data(
        "nrb_demo_bad_other_parent",
        r"IndCtorEnv",
        r"IndCtorEnv.addCtor nrb_demo_env nrb_demo_cf (KCtorMeta.mk (KConstSig.mk nrb_demo_levels nrb_demo_cf_type) nrb_demo_g (Nat.succ Nat.zero) (Nat.succ Nat.zero) Nat.zero)",
    ),
    DeclarationInput::Proof(
        "nrb_demo_other_parent_refuses",
        r"@Eq Bool (nrb_block_return_b nrb_demo_bad_other_parent nrb_demo_block) (Bool.false)",
        r"@Eq.refl Bool Bool.false",
    ),
    DeclarationInput::Data(
        "nrb_demo_bad_other_index",
        r"IndCtorEnv",
        r"IndCtorEnv.addCtor nrb_demo_env nrb_demo_cf (KCtorMeta.mk (KConstSig.mk nrb_demo_levels nrb_demo_cf_type) nrb_demo_f (Nat.succ Nat.zero) (Nat.succ Nat.zero) (Nat.succ Nat.zero))",
    ),
    DeclarationInput::Proof(
        "nrb_demo_other_index_refuses",
        r"@Eq Bool (nrb_block_return_b nrb_demo_bad_other_index nrb_demo_block) (Bool.false)",
        r"@Eq.refl Bool Bool.false",
    ),
    DeclarationInput::Data(
        "nrb_demo_bad_g_arity",
        r"IndCtorEnv",
        r"IndCtorEnv.addInd nrb_demo_env nrb_demo_g (KIndMeta.mk (KConstSig.mk nrb_demo_levels nrb_demo_g_type) (Nat.succ Nat.zero) Nat.zero (@ListType.cons Name (nrb_demo_cg) (@ListType.nil Name)) nrb_demo_block)",
    ),
    DeclarationInput::Proof(
        "nrb_demo_member_arity_refuses",
        r"@Eq Bool (nrb_block_return_b nrb_demo_bad_g_arity nrb_demo_block) (Bool.false)",
        r"@Eq.refl Bool Bool.false",
    ),
    DeclarationInput::Proof(
        "nrb_demo_swapped_block_refuses",
        r"@Eq Bool (nrb_block_return_b nrb_demo_env (@ListType.cons Name (nrb_demo_g) (@ListType.cons Name (nrb_demo_f) (@ListType.nil Name)))) (Bool.false)",
        r"@Eq.refl Bool Bool.false",
    ),
    DeclarationInput::Proof(
        "nrb_demo_missing_refuses",
        r"@Eq Bool (nrb_block_return_b IndCtorEnv.empty nrb_demo_block) (Bool.false)",
        r"@Eq.refl Bool Bool.false",
    ),
    DeclarationInput::Proof(
        "nrb_demo_wrong_kind_refuses",
        r"@Eq Bool (nrb_block_return_b (IndCtorEnv.addCtor nrb_demo_env nrb_demo_f nrb_demo_cf_meta) nrb_demo_block) (Bool.false)",
        r"@Eq.refl Bool Bool.false",
    ),
];

#[cfg(test)]
pub(super) const PROOF_ROOTS: &[&str] = &[
    "nrb_option_selected",
    "nrb_option_resolve",
    "nrb_all_index_at",
    "nrb_names_eq_sound",
    "nrb_nat_some_sound",
    "nrb_block_walk_select",
    "nrb_selected_constructor",
    "nrb_demo_whole",
    "nrb_demo_selected_g",
    "nrb_demo_other_parent_refuses",
    "nrb_demo_other_index_refuses",
    "nrb_demo_member_arity_refuses",
    "nrb_demo_swapped_block_refuses",
    "nrb_demo_missing_refuses",
    "nrb_demo_wrong_kind_refuses",
];

#[cfg(test)]
pub(super) const DATA_NAMES: &[&str] = &[
    "nrb_option_b",
    "nrb_name_at",
    "nrb_all_index_b",
    "nrb_names_eq_b",
    "nrb_names_unique_b",
    "nrb_nat_some_b",
    "nrb_reference",
    "nrb_member_fields_b",
    "nrb_ctor_fields_b",
    "nrb_ctor_at_b",
    "nrb_member_at_b",
    "nrb_block_fields_b",
    "nrb_block_return_b",
    "nrb_demo_f",
    "nrb_demo_g",
    "nrb_demo_cf",
    "nrb_demo_cg",
    "nrb_demo_u",
    "nrb_demo_levels",
    "nrb_demo_block",
    "nrb_demo_domain",
    "nrb_demo_f_type",
    "nrb_demo_g_type",
    "nrb_demo_cf_type",
    "nrb_demo_cg_type",
    "nrb_demo_f_meta",
    "nrb_demo_g_meta",
    "nrb_demo_cf_meta",
    "nrb_demo_cg_meta",
    "nrb_demo_env",
    "nrb_demo_bad_other_parent",
    "nrb_demo_bad_other_index",
    "nrb_demo_bad_g_arity",
];

#[cfg(test)]
pub(super) const INDUCTIVE_NAMES: &[&str] = &[];

#[cfg(test)]
pub(super) const PROP_PROOF_ROOTS: &[&str] = &[
    "nrb_option_selected",
    "nrb_all_index_at",
    "nrb_names_eq_sound",
    "nrb_nat_some_sound",
    "nrb_demo_whole",
    "nrb_demo_other_parent_refuses",
    "nrb_demo_other_index_refuses",
    "nrb_demo_member_arity_refuses",
    "nrb_demo_swapped_block_refuses",
    "nrb_demo_missing_refuses",
    "nrb_demo_wrong_kind_refuses",
];

#[cfg(test)]
pub(super) const TYPE_PROOF_ROOTS: &[&str] = &[
    "nrb_option_resolve",
    "nrb_block_walk_select",
    "nrb_selected_constructor",
    "nrb_demo_selected_g",
];

#[cfg(test)]
pub(super) const NEGATIVE_CONTROLS: &[(&str, &str, &str)] = &[
    (
        "nrb_false_other_parent_accepts",
        r"@Eq Bool (nrb_block_return_b nrb_demo_bad_other_parent nrb_demo_block) (Bool.true)",
        r"nrb_demo_whole",
    ),
    (
        "nrb_false_other_index_accepts",
        r"@Eq Bool (nrb_block_return_b nrb_demo_bad_other_index nrb_demo_block) (Bool.true)",
        r"nrb_demo_whole",
    ),
    (
        "nrb_false_g_index_count_zero",
        r"@Eq Nat (count_pi nrb_demo_g_type) (kind_num_params nrb_demo_g_meta)",
        r"@Eq.refl Nat (count_pi nrb_demo_g_type)",
    ),
    (
        "nrb_false_selected_family",
        r"NamedStrictAppFacts (nrb_demo_block) (nig_param_levels (kconst_params (kind_sig (nrb_demo_f_meta)))) (nrb_demo_f) (count_pi (kconst_type (kctor_sig (nrb_demo_cg_meta)))) (kind_num_params (nrb_demo_f_meta)) (kind_num_indices (nrb_demo_g_meta)) (return_type (kconst_type (kctor_sig (nrb_demo_cg_meta))))",
        r"nrb_demo_selected_g",
    ),
];

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::DeclarationInput;

pub(super) const DECLARATIONS: &[DeclarationInput] = &[
    DeclarationInput::Data(
        "nwr_all_index_b",
        r"forall (A : Type) (f : Nat -> A -> Bool) (xs : ListType A), Bool",
        r"fun (A : Type) (f : Nat -> A -> Bool) (xs : ListType A) => ListType.rec A
 (fun (_ns : ListType A) => (Nat -> A -> Bool) -> Bool)
 (fun (_f : Nat -> A -> Bool) => Bool.true)
 (fun (x : A) (_ns : ListType A) (ih : (Nat -> A -> Bool) -> Bool) (g : Nat -> A -> Bool) =>
  Bool.and (g Nat.zero x) (ih (fun (j : Nat) (y : A) => g (Nat.succ j) y))) xs f",
    ),
    DeclarationInput::Proof(
        "nwr_all_index_names_eq",
        r"forall (A : Type) (name_of : A -> Name) (xs : ListType A)
 (P : Nat -> A -> Bool) (Q : Nat -> Name -> Bool),
 (forall (j : Nat) (x : A),
  Eq (OptionType A) (nsi_at A xs j) (OptionType.some A x) ->
  Eq Bool (P j x) (Q j (name_of x))) ->
 Eq Bool (nwr_all_index_b A P xs) (nrb_all_index_b Q (nsi_names A name_of xs))",
        r"fun (A : Type) (name_of : A -> Name) (xs : ListType A) => ListType.rec A
 (fun (ns : ListType A) => forall (P : Nat -> A -> Bool) (Q : Nat -> Name -> Bool),
  (forall (j : Nat) (x : A),
   Eq (OptionType A) (nsi_at A ns j) (OptionType.some A x) ->
   Eq Bool (P j x) (Q j (name_of x))) ->
  Eq Bool (nwr_all_index_b A P ns) (nrb_all_index_b Q (nsi_names A name_of ns)))
 (fun (P : Nat -> A -> Bool) (Q : Nat -> Name -> Bool)
  (_agree : forall (j : Nat) (x : A),
   Eq (OptionType A) (nsi_at A (ListType.nil A) j) (OptionType.some A x) ->
   Eq Bool (P j x) (Q j (name_of x))) => Eq.refl Bool Bool.true)
 (fun (head : A) (tail : ListType A)
  (ih : forall (P : Nat -> A -> Bool) (Q : Nat -> Name -> Bool),
   (forall (j : Nat) (x : A),
    Eq (OptionType A) (nsi_at A tail j) (OptionType.some A x) ->
    Eq Bool (P j x) (Q j (name_of x))) ->
   Eq Bool (nwr_all_index_b A P tail) (nrb_all_index_b Q (nsi_names A name_of tail)))
  (P : Nat -> A -> Bool) (Q : Nat -> Name -> Bool)
  (agree : forall (j : Nat) (x : A),
   Eq (OptionType A) (nsi_at A (ListType.cons A head tail) j) (OptionType.some A x) ->
   Eq Bool (P j x) (Q j (name_of x))) =>
  universe_bridge_congr2 Bool Bool Bool (fun (a : Bool) (b : Bool) => Bool.and a b)
   (P Nat.zero head) (Q Nat.zero (name_of head))
   (nwr_all_index_b A (fun (j : Nat) (x : A) => P (Nat.succ j) x) tail)
   (nrb_all_index_b (fun (j : Nat) (n : Name) => Q (Nat.succ j) n) (nsi_names A name_of tail))
   (agree Nat.zero head (Eq.refl (OptionType A) (OptionType.some A head)))
   (ih (fun (j : Nat) (x : A) => P (Nat.succ j) x)
    (fun (j : Nat) (n : Name) => Q (Nat.succ j) n)
    (fun (j : Nat) (x : A)
     (found : Eq (OptionType A) (nsi_at A tail j) (OptionType.some A x)) =>
     agree (Nat.succ j) x found))) xs",
    ),
    DeclarationInput::Proof(
        "nwr_all_index_at",
        r"forall (A : Type) (xs : ListType A) (f : Nat -> A -> Bool) (j : Nat) (x : A),
 Eq Bool (nwr_all_index_b A f xs) Bool.true ->
 Eq (OptionType A) (nsi_at A xs j) (OptionType.some A x) ->
 Eq Bool (f j x) Bool.true",
        r"fun (A : Type) (xs : ListType A) => ListType.rec A
 (fun (ns : ListType A) => forall (f : Nat -> A -> Bool) (j : Nat) (x : A),
  Eq Bool (nwr_all_index_b A f ns) Bool.true ->
  Eq (OptionType A) (nsi_at A ns j) (OptionType.some A x) ->
  Eq Bool (f j x) Bool.true)
 (fun (f : Nat -> A -> Bool) (j : Nat) (x : A)
  (_run : Eq Bool Bool.true Bool.true)
  (bad : Eq (OptionType A) (OptionType.none A) (OptionType.some A x)) =>
  option_none_ne_some A x (Eq Bool (f j x) Bool.true) bad)
 (fun (head : A) (tail : ListType A)
  (ih : forall (f : Nat -> A -> Bool) (j : Nat) (x : A),
   Eq Bool (nwr_all_index_b A f tail) Bool.true ->
   Eq (OptionType A) (nsi_at A tail j) (OptionType.some A x) ->
   Eq Bool (f j x) Bool.true)
  (f : Nat -> A -> Bool) (j : Nat) => Nat.rec
   (fun (k : Nat) => forall (x : A),
    Eq Bool (nwr_all_index_b A f (ListType.cons A head tail)) Bool.true ->
    Eq (OptionType A) (nsi_at A (ListType.cons A head tail) k) (OptionType.some A x) ->
    Eq Bool (f k x) Bool.true)
   (fun (x : A)
    (run : Eq Bool (nwr_all_index_b A f (ListType.cons A head tail)) Bool.true)
    (found : Eq (OptionType A) (OptionType.some A head) (OptionType.some A x)) =>
    Eq.subst A (fun (y : A) => Eq Bool (f Nat.zero y) Bool.true) head x
     (option_some_inj A head x found)
     (band_eq_true_left (f Nat.zero head)
      (nwr_all_index_b A (fun (k : Nat) (y : A) => f (Nat.succ k) y) tail) run))
   (fun (k : Nat)
    (_unused : forall (x : A),
     Eq Bool (nwr_all_index_b A f (ListType.cons A head tail)) Bool.true ->
     Eq (OptionType A) (nsi_at A (ListType.cons A head tail) k) (OptionType.some A x) ->
     Eq Bool (f k x) Bool.true)
    (x : A)
    (run : Eq Bool (nwr_all_index_b A f (ListType.cons A head tail)) Bool.true)
    (found : Eq (OptionType A) (nsi_at A tail k) (OptionType.some A x)) =>
    ih (fun (i : Nat) (y : A) => f (Nat.succ i) y) k x
     (band_eq_true_right (f Nat.zero head)
      (nwr_all_index_b A (fun (i : Nat) (y : A) => f (Nat.succ i) y) tail) run) found) j) xs",
    ),
    DeclarationInput::Data(
        "nwr_ctor_fields_b",
        r"forall (us : ListType Name) (p : Nat) (block : ListType Name) (first : KIndMeta) (m : NamedMemberSource) (j : Nat) (c : NamedCtorSource), Bool",
        r"fun (us : ListType Name) (p : Nat) (block : ListType Name) (first : KIndMeta) (m : NamedMemberSource) (j : Nat) (c : NamedCtorSource) => nrb_ctor_fields_b block first (nsi_member_name m) (nsi_member_meta us p block m) j (nsi_ctor_meta us p (nsi_member_name m) j c)",
    ),
    DeclarationInput::Data(
        "nwr_member_fields_b",
        r"forall (us : ListType Name) (p : Nat) (block : ListType Name) (first : KIndMeta) (mi : Nat) (m : NamedMemberSource), Bool",
        r"fun (us : ListType Name) (p : Nat) (block : ListType Name) (first : KIndMeta) (_mi : Nat) (m : NamedMemberSource) => Bool.and (nrb_member_fields_b block first (nsi_member_meta us p block m)) (nwr_all_index_b NamedCtorSource (fun (j : Nat) (c : NamedCtorSource) => nwr_ctor_fields_b us p block first m j c) (nsi_member_ctors m))",
    ),
    DeclarationInput::Data(
        "nwr_first_fields_b",
        r"forall (us : ListType Name) (p : Nat) (whole : ListType NamedMemberSource) (first_source : NamedMemberSource), Bool",
        r"fun (us : ListType Name) (p : Nat) (whole : ListType NamedMemberSource) (first_source : NamedMemberSource) => Bool.and (nat_eqb (list_length (nrb_reference (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (whole)) (first_source)))) (p)) (nwr_all_index_b (NamedMemberSource) (fun (j0 : Nat) (m0 : NamedMemberSource) => nwr_member_fields_b (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (whole)) (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (whole)) (first_source)) (j0) (m0)) (whole))",
    ),
    DeclarationInput::Data(
        "nwr_nonempty_b",
        r"forall (us : ListType Name) (p : Nat) (whole : ListType NamedMemberSource), Bool",
        r"fun (us : ListType Name) (p : Nat) (whole : ListType NamedMemberSource) => ListType.rec NamedMemberSource (fun (_xs : ListType NamedMemberSource) => Bool) Bool.false (fun (first_source : NamedMemberSource) (_tail : ListType NamedMemberSource) (_unused : Bool) => nwr_first_fields_b us p whole first_source) whole",
    ),
    DeclarationInput::Data(
        "nwr_raw_return_b",
        r"forall (us : ListType Name) (p : Nat) (whole : ListType NamedMemberSource), Bool",
        r"fun (us : ListType Name) (p : Nat) (whole : ListType NamedMemberSource) => Bool.and (nrb_names_unique_b (nsi_all_names whole)) (nwr_nonempty_b us p whole)",
    ),
    DeclarationInput::Proof(
        "nwr_raw_success_unique",
        r"forall (us : ListType Name) (p : Nat) (ms : ListType NamedMemberSource) (run : Eq (Bool) (nwr_raw_return_b (us) (p) (ms)) (Bool.true)), Eq (Bool) (nrb_names_unique_b (nsi_all_names (ms))) (Bool.true)",
        r"fun (us : ListType Name) (p : Nat) (ms : ListType NamedMemberSource) (run : Eq (Bool) (nwr_raw_return_b (us) (p) (ms)) (Bool.true)) =>
 band_eq_true_left (nrb_names_unique_b (nsi_all_names (ms))) (nwr_nonempty_b (us) (p) (ms)) (run)",
    ),
    DeclarationInput::Proof(
        "nwr_ctor_leaf_agree",
        r"forall (us : ListType Name) (p : Nat) (ms : ListType NamedMemberSource) (base : IndCtorEnv) (first : KIndMeta) (mi : Nat) (m : NamedMemberSource) (unique : Eq (Bool) (nrb_names_unique_b (nsi_all_names (ms))) (Bool.true)) (member_at : Eq (OptionType NamedMemberSource) (nsi_at (NamedMemberSource) (ms) (mi)) (OptionType.some (NamedMemberSource) (m))) (j : Nat) (c : NamedCtorSource) (ctor_at : Eq (OptionType NamedCtorSource) (nsi_at (NamedCtorSource) (nsi_member_ctors (m)) (j)) (OptionType.some (NamedCtorSource) (c))), Eq (Bool) (nwr_ctor_fields_b (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first) (m) (j) (c)) (nrb_ctor_at_b (nsi_raw_install (us) (p) (ms) (base)) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first) (nsi_member_name (m)) (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m)) (j) (nsi_ctor_name (c)))",
        r"fun (us : ListType Name) (p : Nat) (ms : ListType NamedMemberSource) (base : IndCtorEnv) (first : KIndMeta) (mi : Nat) (m : NamedMemberSource) (unique : Eq (Bool) (nrb_names_unique_b (nsi_all_names (ms))) (Bool.true)) (member_at : Eq (OptionType NamedMemberSource) (nsi_at (NamedMemberSource) (ms) (mi)) (OptionType.some (NamedMemberSource) (m))) (j : Nat) (c : NamedCtorSource) (ctor_at : Eq (OptionType NamedCtorSource) (nsi_at (NamedCtorSource) (nsi_member_ctors (m)) (j)) (OptionType.some (NamedCtorSource) (c))) =>
 Eq.symm (Bool) (nrb_ctor_at_b (nsi_raw_install (us) (p) (ms) (base)) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first) (nsi_member_name (m)) (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m)) (j) (nsi_ctor_name (c))) (nwr_ctor_fields_b (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first) (m) (j) (c)) (Eq.cong (OptionType KCtorMeta) (Bool) (fun (o : OptionType KCtorMeta) => nrb_option_b (KCtorMeta) (fun (record : KCtorMeta) => nrb_ctor_fields_b (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first) (nsi_member_name (m)) (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m)) (j) (record)) (o)) (kctor_for (nsi_raw_install (us) (p) (ms) (base)) (nsi_ctor_name (c))) (OptionType.some (KCtorMeta) (nsi_ctor_meta (us) (p) (nsi_member_name (m)) (j) (c))) (nsi_raw_ctor_lookup_installed (us) (p) (ms) (base) (mi) (m) (j) (c) (unique) (member_at) (ctor_at)))",
    ),
    DeclarationInput::Proof(
        "nwr_ctor_walk_agree",
        r"forall (us : ListType Name) (p : Nat) (ms : ListType NamedMemberSource) (base : IndCtorEnv) (first : KIndMeta) (mi : Nat) (m : NamedMemberSource) (unique : Eq (Bool) (nrb_names_unique_b (nsi_all_names (ms))) (Bool.true)) (member_at : Eq (OptionType NamedMemberSource) (nsi_at (NamedMemberSource) (ms) (mi)) (OptionType.some (NamedMemberSource) (m))), Eq (Bool) (nwr_all_index_b (NamedCtorSource) (fun (j0 : Nat) (c0 : NamedCtorSource) => nwr_ctor_fields_b (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first) (m) (j0) (c0)) (nsi_member_ctors (m))) (nrb_all_index_b (fun (j0 : Nat) (n0 : Name) => nrb_ctor_at_b (nsi_raw_install (us) (p) (ms) (base)) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first) (nsi_member_name (m)) (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m)) (j0) (n0)) (kind_ctor_names (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m))))",
        r"fun (us : ListType Name) (p : Nat) (ms : ListType NamedMemberSource) (base : IndCtorEnv) (first : KIndMeta) (mi : Nat) (m : NamedMemberSource) (unique : Eq (Bool) (nrb_names_unique_b (nsi_all_names (ms))) (Bool.true)) (member_at : Eq (OptionType NamedMemberSource) (nsi_at (NamedMemberSource) (ms) (mi)) (OptionType.some (NamedMemberSource) (m))) =>
 nwr_all_index_names_eq (NamedCtorSource) (nsi_ctor_name) (nsi_member_ctors (m)) (fun (j0 : Nat) (c0 : NamedCtorSource) => nwr_ctor_fields_b (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first) (m) (j0) (c0)) (fun (j0 : Nat) (n0 : Name) => nrb_ctor_at_b (nsi_raw_install (us) (p) (ms) (base)) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first) (nsi_member_name (m)) (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m)) (j0) (n0)) (fun (j : Nat) (c : NamedCtorSource) (ctor_at : Eq (OptionType NamedCtorSource) (nsi_at (NamedCtorSource) (nsi_member_ctors (m)) (j)) (OptionType.some (NamedCtorSource) (c))) => nwr_ctor_leaf_agree (us) (p) (ms) (base) (first) (mi) (m) (unique) (member_at) (j) (c) (ctor_at))",
    ),
    DeclarationInput::Proof(
        "nwr_member_leaf_agree",
        r"forall (us : ListType Name) (p : Nat) (ms : ListType NamedMemberSource) (base : IndCtorEnv) (first : KIndMeta) (mi : Nat) (m : NamedMemberSource) (unique : Eq (Bool) (nrb_names_unique_b (nsi_all_names (ms))) (Bool.true)) (member_at : Eq (OptionType NamedMemberSource) (nsi_at (NamedMemberSource) (ms) (mi)) (OptionType.some (NamedMemberSource) (m))), Eq (Bool) (nwr_member_fields_b (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first) (mi) (m)) (nrb_member_at_b (nsi_raw_install (us) (p) (ms) (base)) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first) (mi) (nsi_member_name (m)))",
        r"fun (us : ListType Name) (p : Nat) (ms : ListType NamedMemberSource) (base : IndCtorEnv) (first : KIndMeta) (mi : Nat) (m : NamedMemberSource) (unique : Eq (Bool) (nrb_names_unique_b (nsi_all_names (ms))) (Bool.true)) (member_at : Eq (OptionType NamedMemberSource) (nsi_at (NamedMemberSource) (ms) (mi)) (OptionType.some (NamedMemberSource) (m))) =>
 Eq.trans (Bool) (nwr_member_fields_b (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first) (mi) (m)) (Bool.and (nrb_member_fields_b (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first) (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m))) (nrb_all_index_b (fun (j0 : Nat) (n0 : Name) => nrb_ctor_at_b (nsi_raw_install (us) (p) (ms) (base)) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first) (nsi_member_name (m)) (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m)) (j0) (n0)) (kind_ctor_names (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m))))) (nrb_member_at_b (nsi_raw_install (us) (p) (ms) (base)) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first) (mi) (nsi_member_name (m))) (Eq.cong (Bool) (Bool) (fun (b : Bool) => Bool.and (nrb_member_fields_b (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first) (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m))) (b)) (nwr_all_index_b (NamedCtorSource) (fun (j0 : Nat) (c0 : NamedCtorSource) => nwr_ctor_fields_b (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first) (m) (j0) (c0)) (nsi_member_ctors (m))) (nrb_all_index_b (fun (j0 : Nat) (n0 : Name) => nrb_ctor_at_b (nsi_raw_install (us) (p) (ms) (base)) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first) (nsi_member_name (m)) (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m)) (j0) (n0)) (kind_ctor_names (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m)))) (nwr_ctor_walk_agree (us) (p) (ms) (base) (first) (mi) (m) (unique) (member_at))) (Eq.symm (Bool) (nrb_member_at_b (nsi_raw_install (us) (p) (ms) (base)) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first) (mi) (nsi_member_name (m))) (Bool.and (nrb_member_fields_b (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first) (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m))) (nrb_all_index_b (fun (j0 : Nat) (n0 : Name) => nrb_ctor_at_b (nsi_raw_install (us) (p) (ms) (base)) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first) (nsi_member_name (m)) (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m)) (j0) (n0)) (kind_ctor_names (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m))))) (Eq.cong (OptionType KIndMeta) (Bool) (fun (o : OptionType KIndMeta) => nrb_option_b (KIndMeta) (fun (record : KIndMeta) => Bool.and (nrb_member_fields_b (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first) (record)) (nrb_all_index_b (fun (j0 : Nat) (cn0 : Name) => nrb_ctor_at_b (nsi_raw_install (us) (p) (ms) (base)) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first) (nsi_member_name (m)) (record) (j0) (cn0)) (kind_ctor_names (record)))) (o)) (kind_for (nsi_raw_install (us) (p) (ms) (base)) (nsi_member_name (m))) (OptionType.some (KIndMeta) (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m))) (nsi_raw_kind_lookup_installed (us) (p) (ms) (base) (mi) (m) (unique) (member_at))))",
    ),
    DeclarationInput::Proof(
        "nwr_member_walk_agree",
        r"forall (us : ListType Name) (p : Nat) (ms : ListType NamedMemberSource) (base : IndCtorEnv) (first : KIndMeta) (unique : Eq (Bool) (nrb_names_unique_b (nsi_all_names (ms))) (Bool.true)), Eq (Bool) (nwr_all_index_b (NamedMemberSource) (fun (j0 : Nat) (m0 : NamedMemberSource) => nwr_member_fields_b (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first) (j0) (m0)) (ms)) (nrb_all_index_b (fun (j0 : Nat) (n0 : Name) => nrb_member_at_b (nsi_raw_install (us) (p) (ms) (base)) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first) (j0) (n0)) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)))",
        r"fun (us : ListType Name) (p : Nat) (ms : ListType NamedMemberSource) (base : IndCtorEnv) (first : KIndMeta) (unique : Eq (Bool) (nrb_names_unique_b (nsi_all_names (ms))) (Bool.true)) =>
 nwr_all_index_names_eq (NamedMemberSource) (nsi_member_name) (ms) (fun (j0 : Nat) (m0 : NamedMemberSource) => nwr_member_fields_b (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first) (j0) (m0)) (fun (j0 : Nat) (n0 : Name) => nrb_member_at_b (nsi_raw_install (us) (p) (ms) (base)) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first) (j0) (n0)) (fun (mi : Nat) (m : NamedMemberSource) (member_at : Eq (OptionType NamedMemberSource) (nsi_at (NamedMemberSource) (ms) (mi)) (OptionType.some (NamedMemberSource) (m))) => nwr_member_leaf_agree (us) (p) (ms) (base) (first) (mi) (m) (unique) (member_at))",
    ),
    DeclarationInput::Proof(
        "nwr_installed_block_fields",
        r"forall (us : ListType Name) (p : Nat) (head : NamedMemberSource) (tail : ListType NamedMemberSource) (base : IndCtorEnv) (run : Eq (Bool) (nwr_raw_return_b (us) (p) (ListType.cons (NamedMemberSource) (head) (tail))) (Bool.true)), Eq (Bool) (nrb_block_fields_b (nsi_raw_install (us) (p) (ListType.cons (NamedMemberSource) (head) (tail)) (base)) (nsi_names (NamedMemberSource) (nsi_member_name) (ListType.cons (NamedMemberSource) (head) (tail))) (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ListType.cons (NamedMemberSource) (head) (tail))) (head))) (Bool.true)",
        r"fun (us : ListType Name) (p : Nat) (head : NamedMemberSource) (tail : ListType NamedMemberSource) (base : IndCtorEnv) (run : Eq (Bool) (nwr_raw_return_b (us) (p) (ListType.cons (NamedMemberSource) (head) (tail))) (Bool.true)) =>
 nig_and_intro (nat_eqb (list_length (nrb_reference (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ListType.cons (NamedMemberSource) (head) (tail))) (head)))) (p)) (Bool.and (nrb_names_unique_b (nsi_names (NamedMemberSource) (nsi_member_name) (ListType.cons (NamedMemberSource) (head) (tail)))) (Bool.and (nrb_all_index_b (fun (j0 : Nat) (n0 : Name) => nrb_member_at_b (nsi_raw_install (us) (p) (ListType.cons (NamedMemberSource) (head) (tail)) (base)) (nsi_names (NamedMemberSource) (nsi_member_name) (ListType.cons (NamedMemberSource) (head) (tail))) (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ListType.cons (NamedMemberSource) (head) (tail))) (head)) (j0) (n0)) (nsi_names (NamedMemberSource) (nsi_member_name) (ListType.cons (NamedMemberSource) (head) (tail)))) (Bool.true))) (band_eq_true_left (nat_eqb (list_length (nrb_reference (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ListType.cons (NamedMemberSource) (head) (tail))) (head)))) (p)) (nwr_all_index_b (NamedMemberSource) (fun (j0 : Nat) (m0 : NamedMemberSource) => nwr_member_fields_b (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ListType.cons (NamedMemberSource) (head) (tail))) (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ListType.cons (NamedMemberSource) (head) (tail))) (head)) (j0) (m0)) (ListType.cons (NamedMemberSource) (head) (tail))) (band_eq_true_right (nrb_names_unique_b (nsi_all_names (ListType.cons (NamedMemberSource) (head) (tail)))) (nwr_first_fields_b (us) (p) (ListType.cons (NamedMemberSource) (head) (tail)) (head)) (run))) (nig_and_intro (nrb_names_unique_b (nsi_names (NamedMemberSource) (nsi_member_name) (ListType.cons (NamedMemberSource) (head) (tail)))) (Bool.and (nrb_all_index_b (fun (j0 : Nat) (n0 : Name) => nrb_member_at_b (nsi_raw_install (us) (p) (ListType.cons (NamedMemberSource) (head) (tail)) (base)) (nsi_names (NamedMemberSource) (nsi_member_name) (ListType.cons (NamedMemberSource) (head) (tail))) (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ListType.cons (NamedMemberSource) (head) (tail))) (head)) (j0) (n0)) (nsi_names (NamedMemberSource) (nsi_member_name) (ListType.cons (NamedMemberSource) (head) (tail)))) (Bool.true)) (nsi_unique_append_left (nsi_names (NamedMemberSource) (nsi_member_name) (ListType.cons (NamedMemberSource) (head) (tail))) (nsi_all_ctor_names (ListType.cons (NamedMemberSource) (head) (tail))) (nwr_raw_success_unique (us) (p) (ListType.cons (NamedMemberSource) (head) (tail)) (run))) (nig_and_intro (nrb_all_index_b (fun (j0 : Nat) (n0 : Name) => nrb_member_at_b (nsi_raw_install (us) (p) (ListType.cons (NamedMemberSource) (head) (tail)) (base)) (nsi_names (NamedMemberSource) (nsi_member_name) (ListType.cons (NamedMemberSource) (head) (tail))) (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ListType.cons (NamedMemberSource) (head) (tail))) (head)) (j0) (n0)) (nsi_names (NamedMemberSource) (nsi_member_name) (ListType.cons (NamedMemberSource) (head) (tail)))) (Bool.true) (Eq.subst (Bool) (fun (b : Bool) => Eq Bool b Bool.true) (nwr_all_index_b (NamedMemberSource) (fun (j0 : Nat) (m0 : NamedMemberSource) => nwr_member_fields_b (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ListType.cons (NamedMemberSource) (head) (tail))) (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ListType.cons (NamedMemberSource) (head) (tail))) (head)) (j0) (m0)) (ListType.cons (NamedMemberSource) (head) (tail))) (nrb_all_index_b (fun (j0 : Nat) (n0 : Name) => nrb_member_at_b (nsi_raw_install (us) (p) (ListType.cons (NamedMemberSource) (head) (tail)) (base)) (nsi_names (NamedMemberSource) (nsi_member_name) (ListType.cons (NamedMemberSource) (head) (tail))) (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ListType.cons (NamedMemberSource) (head) (tail))) (head)) (j0) (n0)) (nsi_names (NamedMemberSource) (nsi_member_name) (ListType.cons (NamedMemberSource) (head) (tail)))) (nwr_member_walk_agree (us) (p) (ListType.cons (NamedMemberSource) (head) (tail)) (base) (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ListType.cons (NamedMemberSource) (head) (tail))) (head)) (nwr_raw_success_unique (us) (p) (ListType.cons (NamedMemberSource) (head) (tail)) (run))) (band_eq_true_right (nat_eqb (list_length (nrb_reference (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ListType.cons (NamedMemberSource) (head) (tail))) (head)))) (p)) (nwr_all_index_b (NamedMemberSource) (fun (j0 : Nat) (m0 : NamedMemberSource) => nwr_member_fields_b (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ListType.cons (NamedMemberSource) (head) (tail))) (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ListType.cons (NamedMemberSource) (head) (tail))) (head)) (j0) (m0)) (ListType.cons (NamedMemberSource) (head) (tail))) (band_eq_true_right (nrb_names_unique_b (nsi_all_names (ListType.cons (NamedMemberSource) (head) (tail)))) (nwr_first_fields_b (us) (p) (ListType.cons (NamedMemberSource) (head) (tail)) (head)) (run)))) (Eq.refl (Bool) (Bool.true))))",
    ),
    DeclarationInput::Proof(
        "nwr_installed_return_of_raw",
        r"forall (us : ListType Name) (p : Nat) (ms : ListType NamedMemberSource), forall (base : IndCtorEnv), Eq (Bool) (nwr_raw_return_b (us) (p) (ms)) (Bool.true) -> Eq (Bool) (nrb_block_return_b (nsi_raw_install (us) (p) (ms) (base)) (nsi_names (NamedMemberSource) (nsi_member_name) (ms))) (Bool.true)",
        r"fun (us : ListType Name) (p : Nat) (ms : ListType NamedMemberSource) => ListType.rec NamedMemberSource
 (fun (xs : ListType NamedMemberSource) => forall (base : IndCtorEnv), Eq (Bool) (nwr_raw_return_b (us) (p) (xs)) (Bool.true) -> Eq (Bool) (nrb_block_return_b (nsi_raw_install (us) (p) (xs) (base)) (nsi_names (NamedMemberSource) (nsi_member_name) (xs))) (Bool.true))
 (fun (base : IndCtorEnv) (bad : Eq Bool Bool.false Bool.true) => bool_false_ne_true (Eq (Bool) (nrb_block_return_b (nsi_raw_install (us) (p) (ListType.nil (NamedMemberSource)) (base)) (nsi_names (NamedMemberSource) (nsi_member_name) (ListType.nil (NamedMemberSource)))) (Bool.true)) (bad))
 (fun (head : NamedMemberSource) (tail : ListType NamedMemberSource) (_unused : forall (base : IndCtorEnv), Eq (Bool) (nwr_raw_return_b (us) (p) (tail)) (Bool.true) -> Eq (Bool) (nrb_block_return_b (nsi_raw_install (us) (p) (tail) (base)) (nsi_names (NamedMemberSource) (nsi_member_name) (tail))) (Bool.true)) (base : IndCtorEnv) (run : Eq (Bool) (nwr_raw_return_b (us) (p) (ListType.cons (NamedMemberSource) (head) (tail))) (Bool.true)) =>
  Eq.trans (Bool) (nrb_block_return_b (nsi_raw_install (us) (p) (ListType.cons (NamedMemberSource) (head) (tail)) (base)) (nsi_names (NamedMemberSource) (nsi_member_name) (ListType.cons (NamedMemberSource) (head) (tail)))) (nrb_block_fields_b (nsi_raw_install (us) (p) (ListType.cons (NamedMemberSource) (head) (tail)) (base)) (nsi_names (NamedMemberSource) (nsi_member_name) (ListType.cons (NamedMemberSource) (head) (tail))) (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ListType.cons (NamedMemberSource) (head) (tail))) (head))) (Bool.true) (Eq.cong (OptionType KIndMeta) (Bool) (fun (o : OptionType KIndMeta) => nrb_option_b (KIndMeta) (fun (record : KIndMeta) => nrb_block_fields_b (nsi_raw_install (us) (p) (ListType.cons (NamedMemberSource) (head) (tail)) (base)) (nsi_names (NamedMemberSource) (nsi_member_name) (ListType.cons (NamedMemberSource) (head) (tail))) (record)) (o)) (kind_for (nsi_raw_install (us) (p) (ListType.cons (NamedMemberSource) (head) (tail)) (base)) (nsi_member_name (head))) (OptionType.some (KIndMeta) (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ListType.cons (NamedMemberSource) (head) (tail))) (head))) (nsi_raw_kind_lookup_installed (us) (p) (ListType.cons (NamedMemberSource) (head) (tail)) (base) (Nat.zero) (head) (nwr_raw_success_unique (us) (p) (ListType.cons (NamedMemberSource) (head) (tail)) (run)) (Eq.refl (OptionType NamedMemberSource) (OptionType.some (NamedMemberSource) (head))))) (nwr_installed_block_fields (us) (p) (head) (tail) (base) (run))) ms",
    ),
    DeclarationInput::Proof(
        "nwr_selected_constructor_from_raw",
        r"forall (us : ListType Name) (p : Nat) (ms : ListType NamedMemberSource) (base : IndCtorEnv) (mi : Nat) (m : NamedMemberSource) (j : Nat) (c : NamedCtorSource) (run : Eq (Bool) (nwr_raw_return_b (us) (p) (ms)) (Bool.true)) (member_at : Eq (OptionType NamedMemberSource) (nsi_at (NamedMemberSource) (ms) (mi)) (OptionType.some (NamedMemberSource) (m))) (ctor_at : Eq (OptionType NamedCtorSource) (nsi_at (NamedCtorSource) (nsi_member_ctors (m)) (j)) (OptionType.some (NamedCtorSource) (c))) (C : Type) (k : forall (first_source : NamedMemberSource), Eq Nat (list_length (nrb_reference ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first_source) ))) (kind_num_params ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first_source) )) -> Eq Bool (nrb_names_unique_b ( nsi_names (NamedMemberSource) (nsi_member_name) (ms) )) (Bool.true) -> Eq (ListType Name) (kind_all_names ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m) )) (( nsi_names (NamedMemberSource) (nsi_member_name) (ms) )) -> Eq Nat (kind_num_params ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m) )) (kind_num_params ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first_source) )) -> Eq (ListType Name) (kconst_params (kind_sig ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m) ))) (kconst_params (kind_sig ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first_source) ))) -> Eq Bool (nig_pi_prefix_b (nrb_reference ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first_source) )) (kconst_type (kind_sig ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m) )))) (Bool.true) -> Eq (OptionType Nat) (nig_checked_indices (kind_num_params ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first_source) )) (kconst_type (kind_sig ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m) )))) (OptionType.some Nat (kind_num_indices ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m) ))) -> Eq Nat (count_pi (kconst_type (kind_sig ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m) )))) (Nat.add (kind_num_params ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first_source) )) (kind_num_indices ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m) ))) -> Eq Name (kctor_parent ( nsi_ctor_meta (us) (p) (nsi_member_name (m)) (j) (c) )) (( nsi_member_name (m) )) -> Eq Nat (kctor_num_params ( nsi_ctor_meta (us) (p) (nsi_member_name (m)) (j) (c) )) (kind_num_params ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first_source) )) -> Eq (ListType Name) (kconst_params (kctor_sig ( nsi_ctor_meta (us) (p) (nsi_member_name (m)) (j) (c) ))) (kconst_params (kind_sig ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first_source) ))) -> Eq Nat (kctor_index ( nsi_ctor_meta (us) (p) (nsi_member_name (m)) (j) (c) )) (( j )) -> Eq Nat (count_pi (kconst_type (kctor_sig ( nsi_ctor_meta (us) (p) (nsi_member_name (m)) (j) (c) )))) (Nat.add (kind_num_params ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first_source) )) (kctor_num_fields ( nsi_ctor_meta (us) (p) (nsi_member_name (m)) (j) (c) ))) -> Eq Bool (nig_pi_prefix_b (nrb_reference ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first_source) )) (kconst_type (kctor_sig ( nsi_ctor_meta (us) (p) (nsi_member_name (m)) (j) (c) )))) (Bool.true) -> Le (kind_num_params ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first_source) )) (count_pi (kconst_type (kctor_sig ( nsi_ctor_meta (us) (p) (nsi_member_name (m)) (j) (c) )))) -> NamedStrictAppFacts ( nsi_names (NamedMemberSource) (nsi_member_name) (ms) ) (nig_param_levels (kconst_params (kind_sig ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first_source) )))) ( nsi_member_name (m) ) (count_pi (kconst_type (kctor_sig ( nsi_ctor_meta (us) (p) (nsi_member_name (m)) (j) (c) )))) (kind_num_params ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first_source) )) (kind_num_indices ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m) )) (return_type (kconst_type (kctor_sig ( nsi_ctor_meta (us) (p) (nsi_member_name (m)) (j) (c) )))) -> C), C",
        r"fun (us : ListType Name) (p : Nat) (ms : ListType NamedMemberSource) (base : IndCtorEnv) (mi : Nat) (m : NamedMemberSource) (j : Nat) (c : NamedCtorSource) (run : Eq (Bool) (nwr_raw_return_b (us) (p) (ms)) (Bool.true)) (member_at : Eq (OptionType NamedMemberSource) (nsi_at (NamedMemberSource) (ms) (mi)) (OptionType.some (NamedMemberSource) (m))) (ctor_at : Eq (OptionType NamedCtorSource) (nsi_at (NamedCtorSource) (nsi_member_ctors (m)) (j)) (OptionType.some (NamedCtorSource) (c))) (C : Type) (k : forall (first_source : NamedMemberSource), Eq Nat (list_length (nrb_reference ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first_source) ))) (kind_num_params ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first_source) )) -> Eq Bool (nrb_names_unique_b ( nsi_names (NamedMemberSource) (nsi_member_name) (ms) )) (Bool.true) -> Eq (ListType Name) (kind_all_names ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m) )) (( nsi_names (NamedMemberSource) (nsi_member_name) (ms) )) -> Eq Nat (kind_num_params ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m) )) (kind_num_params ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first_source) )) -> Eq (ListType Name) (kconst_params (kind_sig ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m) ))) (kconst_params (kind_sig ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first_source) ))) -> Eq Bool (nig_pi_prefix_b (nrb_reference ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first_source) )) (kconst_type (kind_sig ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m) )))) (Bool.true) -> Eq (OptionType Nat) (nig_checked_indices (kind_num_params ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first_source) )) (kconst_type (kind_sig ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m) )))) (OptionType.some Nat (kind_num_indices ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m) ))) -> Eq Nat (count_pi (kconst_type (kind_sig ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m) )))) (Nat.add (kind_num_params ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first_source) )) (kind_num_indices ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m) ))) -> Eq Name (kctor_parent ( nsi_ctor_meta (us) (p) (nsi_member_name (m)) (j) (c) )) (( nsi_member_name (m) )) -> Eq Nat (kctor_num_params ( nsi_ctor_meta (us) (p) (nsi_member_name (m)) (j) (c) )) (kind_num_params ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first_source) )) -> Eq (ListType Name) (kconst_params (kctor_sig ( nsi_ctor_meta (us) (p) (nsi_member_name (m)) (j) (c) ))) (kconst_params (kind_sig ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first_source) ))) -> Eq Nat (kctor_index ( nsi_ctor_meta (us) (p) (nsi_member_name (m)) (j) (c) )) (( j )) -> Eq Nat (count_pi (kconst_type (kctor_sig ( nsi_ctor_meta (us) (p) (nsi_member_name (m)) (j) (c) )))) (Nat.add (kind_num_params ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first_source) )) (kctor_num_fields ( nsi_ctor_meta (us) (p) (nsi_member_name (m)) (j) (c) ))) -> Eq Bool (nig_pi_prefix_b (nrb_reference ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first_source) )) (kconst_type (kctor_sig ( nsi_ctor_meta (us) (p) (nsi_member_name (m)) (j) (c) )))) (Bool.true) -> Le (kind_num_params ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first_source) )) (count_pi (kconst_type (kctor_sig ( nsi_ctor_meta (us) (p) (nsi_member_name (m)) (j) (c) )))) -> NamedStrictAppFacts ( nsi_names (NamedMemberSource) (nsi_member_name) (ms) ) (nig_param_levels (kconst_params (kind_sig ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first_source) )))) ( nsi_member_name (m) ) (count_pi (kconst_type (kctor_sig ( nsi_ctor_meta (us) (p) (nsi_member_name (m)) (j) (c) )))) (kind_num_params ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first_source) )) (kind_num_indices ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m) )) (return_type (kconst_type (kctor_sig ( nsi_ctor_meta (us) (p) (nsi_member_name (m)) (j) (c) )))) -> C) =>
 nsi_raw_selected_lookups (us) (p) (ms) (base) (mi) (m) (j) (c) (nwr_raw_success_unique (us) (p) (ms) (run)) (member_at) (ctor_at) (C) (fun (first_source : NamedMemberSource) (h0 : Eq (OptionType Name) (nrb_name_at (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (Nat.zero)) (OptionType.some (Name) (nsi_member_name (first_source)))) (h1 : Eq (OptionType KIndMeta) (kind_for (nsi_raw_install (us) (p) (ms) (base)) (nsi_member_name (first_source))) (OptionType.some (KIndMeta) (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first_source)))) (h2 : Eq (OptionType Name) (nrb_name_at (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (mi)) (OptionType.some (Name) (nsi_member_name (m)))) (h3 : Eq (OptionType KIndMeta) (kind_for (nsi_raw_install (us) (p) (ms) (base)) (nsi_member_name (m))) (OptionType.some (KIndMeta) (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m)))) (h4 : Eq (OptionType Name) (nrb_name_at (kind_ctor_names (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m))) (j)) (OptionType.some (Name) (nsi_ctor_name (c)))) (h5 : Eq (OptionType KCtorMeta) (kctor_for (nsi_raw_install (us) (p) (ms) (base)) (nsi_ctor_name (c))) (OptionType.some (KCtorMeta) (nsi_ctor_meta (us) (p) (nsi_member_name (m)) (j) (c)))) => nrb_selected_constructor (nsi_raw_install (us) (p) (ms) (base)) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (nsi_member_name (first_source)) (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first_source)) (mi) (nsi_member_name (m)) (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m)) (j) (nsi_ctor_name (c)) (nsi_ctor_meta (us) (p) (nsi_member_name (m)) (j) (c)) (nwr_installed_return_of_raw (us) (p) (ms) (base) (run)) (h0) (h1) (h2) (h3) (h4) (h5) (C) (k (first_source)))",
    ),
    DeclarationInput::Proof(
        "nwr_selected_strict_facts",
        r"forall (us : ListType Name) (p : Nat) (ms : ListType NamedMemberSource) (base : IndCtorEnv) (mi : Nat) (m : NamedMemberSource) (j : Nat) (c : NamedCtorSource) (run : Eq (Bool) (nwr_raw_return_b (us) (p) (ms)) (Bool.true)) (member_at : Eq (OptionType NamedMemberSource) (nsi_at (NamedMemberSource) (ms) (mi)) (OptionType.some (NamedMemberSource) (m))) (ctor_at : Eq (OptionType NamedCtorSource) (nsi_at (NamedCtorSource) (nsi_member_ctors (m)) (j)) (OptionType.some (NamedCtorSource) (c))), NamedStrictAppFacts (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (nig_param_levels (us)) (nsi_member_name (m)) (count_pi (nsi_ctor_type (c))) (p) (kind_num_indices (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m))) (return_type (nsi_ctor_type (c)))",
        r"fun (us : ListType Name) (p : Nat) (ms : ListType NamedMemberSource) (base : IndCtorEnv) (mi : Nat) (m : NamedMemberSource) (j : Nat) (c : NamedCtorSource) (run : Eq (Bool) (nwr_raw_return_b (us) (p) (ms)) (Bool.true)) (member_at : Eq (OptionType NamedMemberSource) (nsi_at (NamedMemberSource) (ms) (mi)) (OptionType.some (NamedMemberSource) (m))) (ctor_at : Eq (OptionType NamedCtorSource) (nsi_at (NamedCtorSource) (nsi_member_ctors (m)) (j)) (OptionType.some (NamedCtorSource) (c))) =>
 nwr_selected_constructor_from_raw (us) (p) (ms) (base) (mi) (m) (j) (c) (run) (member_at) (ctor_at) (NamedStrictAppFacts (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (nig_param_levels (us)) (nsi_member_name (m)) (count_pi (nsi_ctor_type (c))) (p) (kind_num_indices (nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m))) (return_type (nsi_ctor_type (c)))) (fun (first_source : NamedMemberSource) (h0 : Eq Nat (list_length (nrb_reference ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first_source) ))) (kind_num_params ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first_source) ))) (h1 : Eq Bool (nrb_names_unique_b ( nsi_names (NamedMemberSource) (nsi_member_name) (ms) )) (Bool.true)) (h2 : Eq (ListType Name) (kind_all_names ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m) )) (( nsi_names (NamedMemberSource) (nsi_member_name) (ms) ))) (h3 : Eq Nat (kind_num_params ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m) )) (kind_num_params ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first_source) ))) (h4 : Eq (ListType Name) (kconst_params (kind_sig ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m) ))) (kconst_params (kind_sig ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first_source) )))) (h5 : Eq Bool (nig_pi_prefix_b (nrb_reference ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first_source) )) (kconst_type (kind_sig ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m) )))) (Bool.true)) (h6 : Eq (OptionType Nat) (nig_checked_indices (kind_num_params ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first_source) )) (kconst_type (kind_sig ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m) )))) (OptionType.some Nat (kind_num_indices ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m) )))) (h7 : Eq Nat (count_pi (kconst_type (kind_sig ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m) )))) (Nat.add (kind_num_params ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first_source) )) (kind_num_indices ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m) )))) (h8 : Eq Name (kctor_parent ( nsi_ctor_meta (us) (p) (nsi_member_name (m)) (j) (c) )) (( nsi_member_name (m) ))) (h9 : Eq Nat (kctor_num_params ( nsi_ctor_meta (us) (p) (nsi_member_name (m)) (j) (c) )) (kind_num_params ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first_source) ))) (h10 : Eq (ListType Name) (kconst_params (kctor_sig ( nsi_ctor_meta (us) (p) (nsi_member_name (m)) (j) (c) ))) (kconst_params (kind_sig ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first_source) )))) (h11 : Eq Nat (kctor_index ( nsi_ctor_meta (us) (p) (nsi_member_name (m)) (j) (c) )) (( j ))) (h12 : Eq Nat (count_pi (kconst_type (kctor_sig ( nsi_ctor_meta (us) (p) (nsi_member_name (m)) (j) (c) )))) (Nat.add (kind_num_params ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first_source) )) (kctor_num_fields ( nsi_ctor_meta (us) (p) (nsi_member_name (m)) (j) (c) )))) (h13 : Eq Bool (nig_pi_prefix_b (nrb_reference ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first_source) )) (kconst_type (kctor_sig ( nsi_ctor_meta (us) (p) (nsi_member_name (m)) (j) (c) )))) (Bool.true)) (h14 : Le (kind_num_params ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first_source) )) (count_pi (kconst_type (kctor_sig ( nsi_ctor_meta (us) (p) (nsi_member_name (m)) (j) (c) ))))) (h15 : NamedStrictAppFacts ( nsi_names (NamedMemberSource) (nsi_member_name) (ms) ) (nig_param_levels (kconst_params (kind_sig ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first_source) )))) ( nsi_member_name (m) ) (count_pi (kconst_type (kctor_sig ( nsi_ctor_meta (us) (p) (nsi_member_name (m)) (j) (c) )))) (kind_num_params ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (first_source) )) (kind_num_indices ( nsi_member_meta (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (m) )) (return_type (kconst_type (kctor_sig ( nsi_ctor_meta (us) (p) (nsi_member_name (m)) (j) (c) ))))) => h15)",
    ),
    DeclarationInput::Proof(
        "nwr_demo_raw_success",
        r"Eq (Bool) (nwr_raw_return_b (nrb_demo_levels) (Nat.succ Nat.zero) (nsi_demo_sources)) (Bool.true)",
        r"Eq.refl (Bool) (Bool.true)",
    ),
    DeclarationInput::Proof(
        "nwr_demo_installed_success",
        r"forall (base : IndCtorEnv), Eq (Bool) (nrb_block_return_b (nsi_raw_install ((nrb_demo_levels)) ((Nat.succ Nat.zero)) ((nsi_demo_sources)) (base)) (nsi_names (NamedMemberSource) (nsi_member_name) ((nsi_demo_sources)))) (Bool.true)",
        r"fun (base : IndCtorEnv) =>
 nwr_installed_return_of_raw (nrb_demo_levels) (Nat.succ Nat.zero) (nsi_demo_sources) (base) (nwr_demo_raw_success)",
    ),
    DeclarationInput::Proof(
        "nwr_demo_selected_second_ctor",
        r"forall (base : IndCtorEnv), NamedStrictAppFacts (nsi_names (NamedMemberSource) (nsi_member_name) ((nsi_demo_sources))) (nig_param_levels ((nrb_demo_levels))) (nsi_member_name ((nsi_demo_g))) (count_pi (nsi_ctor_type ((nsi_demo_cg2)))) ((Nat.succ Nat.zero)) (kind_num_indices (nsi_member_meta ((nrb_demo_levels)) ((Nat.succ Nat.zero)) (nsi_names (NamedMemberSource) (nsi_member_name) ((nsi_demo_sources))) ((nsi_demo_g)))) (return_type (nsi_ctor_type ((nsi_demo_cg2))))",
        r"fun (base : IndCtorEnv) =>
 nwr_selected_strict_facts (nrb_demo_levels) (Nat.succ Nat.zero) (nsi_demo_sources) (base) (Nat.succ Nat.zero) (nsi_demo_g) (Nat.succ Nat.zero) (nsi_demo_cg2) (nwr_demo_raw_success) (Eq.refl (OptionType NamedMemberSource) (OptionType.some (NamedMemberSource) (nsi_demo_g))) (Eq.refl (OptionType NamedCtorSource) (OptionType.some (NamedCtorSource) (nsi_demo_cg2)))",
    ),
    DeclarationInput::Proof(
        "nwr_empty_outer_refuses",
        r"Eq (Bool) (Bool.not (nwr_raw_return_b (nrb_demo_levels) (Nat.succ Nat.zero) (ListType.nil (NamedMemberSource)))) (Bool.true)",
        r"Eq.refl (Bool) (Bool.true)",
    ),
    DeclarationInput::Proof(
        "nwr_empty_raw_fold_true",
        r"Eq (Bool) (nwr_all_index_b (NamedCtorSource) (fun (_j : Nat) (_c : NamedCtorSource) => Bool.false) (ListType.nil (NamedCtorSource))) (Bool.true)",
        r"Eq.refl (Bool) (Bool.true)",
    ),
    DeclarationInput::Data(
        "nwr_empty_ctor_sources",
        r"ListType NamedMemberSource",
        r"ListType.cons (NamedMemberSource) (NamedMemberSource.mk (nrb_demo_f) (nrb_demo_f_type) (ListType.nil (NamedCtorSource))) (ListType.nil (NamedMemberSource))",
    ),
    DeclarationInput::Proof(
        "nwr_empty_ctor_member_accepts",
        r"Eq (Bool) (nwr_raw_return_b (nrb_demo_levels) (Nat.succ Nat.zero) (nwr_empty_ctor_sources)) (Bool.true)",
        r"Eq.refl (Bool) (Bool.true)",
    ),
    DeclarationInput::Proof(
        "nwr_empty_ctor_installed_success",
        r"forall (base : IndCtorEnv), Eq (Bool) (nrb_block_return_b (nsi_raw_install (nrb_demo_levels) (Nat.succ Nat.zero) (nwr_empty_ctor_sources) (base)) (nsi_names (NamedMemberSource) (nsi_member_name) (nwr_empty_ctor_sources))) (Bool.true)",
        r"fun (base : IndCtorEnv) =>
 nwr_installed_return_of_raw (nrb_demo_levels) (Nat.succ Nat.zero) (nwr_empty_ctor_sources) (base) (nwr_empty_ctor_member_accepts)",
    ),
    DeclarationInput::Proof(
        "nwr_cross_kind_raw_refuses",
        r"Eq (Bool) (nwr_raw_return_b (nrb_demo_levels) (Nat.succ Nat.zero) (nsi_demo_collision_sources)) (Bool.false)",
        r"Eq.refl (Bool) (Bool.false)",
    ),
    DeclarationInput::Data(
        "nwr_bad_other_member",
        r"NamedMemberSource",
        r"NamedMemberSource.mk (nrb_demo_f) (nrb_demo_f_type) (ListType.cons (NamedCtorSource) (NamedCtorSource.mk (nrb_demo_cf) (nrb_demo_cg_type)) (ListType.nil (NamedCtorSource)))",
    ),
    DeclarationInput::Data(
        "nwr_bad_other_sources",
        r"ListType NamedMemberSource",
        r"ListType.cons (NamedMemberSource) (nwr_bad_other_member) (ListType.cons (NamedMemberSource) (nsi_demo_g) (ListType.nil (NamedMemberSource)))",
    ),
    DeclarationInput::Proof(
        "nwr_bad_other_member_refuses",
        r"Eq (Bool) (nwr_raw_return_b (nrb_demo_levels) (Nat.succ Nat.zero) (nwr_bad_other_sources)) (Bool.false)",
        r"Eq.refl (Bool) (Bool.false)",
    ),
    DeclarationInput::Proof(
        "nwr_selected_local_still_accepts",
        r"Eq (Bool) (nwr_member_fields_b (nrb_demo_levels) (Nat.succ Nat.zero) (nsi_names (NamedMemberSource) (nsi_member_name) (nwr_bad_other_sources)) (nsi_member_meta (nrb_demo_levels) (Nat.succ Nat.zero) (nsi_names (NamedMemberSource) (nsi_member_name) (nwr_bad_other_sources)) (nwr_bad_other_member)) (Nat.succ Nat.zero) (nsi_demo_g)) (Bool.true)",
        r"Eq.refl (Bool) (Bool.true)",
    ),
    DeclarationInput::Data(
        "nwr_short_former_sources",
        r"ListType NamedMemberSource",
        r"ListType.cons (NamedMemberSource) (NamedMemberSource.mk (nrb_demo_f) (nrb_demo_domain) (ListType.nil (NamedCtorSource))) (ListType.nil (NamedMemberSource))",
    ),
    DeclarationInput::Proof(
        "nwr_short_former_refuses",
        r"Eq (Bool) (nwr_raw_return_b (nrb_demo_levels) (Nat.succ Nat.zero) (nwr_short_former_sources)) (Bool.false)",
        r"Eq.refl (Bool) (Bool.false)",
    ),
    DeclarationInput::Data(
        "nwr_wrong_level_sources",
        r"ListType NamedMemberSource",
        r"ListType.cons (NamedMemberSource) (NamedMemberSource.mk (nrb_demo_f) (nrb_demo_f_type) (ListType.cons (NamedCtorSource) (NamedCtorSource.mk (nrb_demo_cf) (KExpr.pi nrb_demo_domain (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.app (KExpr.const nrb_demo_f (ListType.nil Level)) (KExpr.bvar (Nat.succ Nat.zero)))))) (ListType.nil (NamedCtorSource)))) (ListType.nil (NamedMemberSource))",
    ),
    DeclarationInput::Proof(
        "nwr_wrong_level_refuses",
        r"Eq (Bool) (nwr_raw_return_b (nrb_demo_levels) (Nat.succ Nat.zero) (nwr_wrong_level_sources)) (Bool.false)",
        r"Eq.refl (Bool) (Bool.false)",
    ),
];

#[cfg(test)]
pub(super) const PROOF_ROOTS: &[&str] = &[
    "nwr_all_index_names_eq",
    "nwr_all_index_at",
    "nwr_raw_success_unique",
    "nwr_ctor_leaf_agree",
    "nwr_ctor_walk_agree",
    "nwr_member_leaf_agree",
    "nwr_member_walk_agree",
    "nwr_installed_block_fields",
    "nwr_installed_return_of_raw",
    "nwr_selected_constructor_from_raw",
    "nwr_selected_strict_facts",
    "nwr_demo_raw_success",
    "nwr_demo_installed_success",
    "nwr_demo_selected_second_ctor",
    "nwr_empty_outer_refuses",
    "nwr_empty_raw_fold_true",
    "nwr_empty_ctor_member_accepts",
    "nwr_empty_ctor_installed_success",
    "nwr_cross_kind_raw_refuses",
    "nwr_bad_other_member_refuses",
    "nwr_selected_local_still_accepts",
    "nwr_short_former_refuses",
    "nwr_wrong_level_refuses",
];

#[cfg(test)]
pub(super) const PROP_PROOF_ROOTS: &[&str] = &[
    "nwr_all_index_names_eq",
    "nwr_all_index_at",
    "nwr_raw_success_unique",
    "nwr_ctor_leaf_agree",
    "nwr_ctor_walk_agree",
    "nwr_member_leaf_agree",
    "nwr_member_walk_agree",
    "nwr_installed_block_fields",
    "nwr_installed_return_of_raw",
    "nwr_demo_raw_success",
    "nwr_demo_installed_success",
    "nwr_empty_outer_refuses",
    "nwr_empty_raw_fold_true",
    "nwr_empty_ctor_member_accepts",
    "nwr_empty_ctor_installed_success",
    "nwr_cross_kind_raw_refuses",
    "nwr_bad_other_member_refuses",
    "nwr_selected_local_still_accepts",
    "nwr_short_former_refuses",
    "nwr_wrong_level_refuses",
];

#[cfg(test)]
pub(super) const TYPE_PROOF_ROOTS: &[&str] = &[
    "nwr_selected_constructor_from_raw",
    "nwr_selected_strict_facts",
    "nwr_demo_selected_second_ctor",
];

#[cfg(test)]
pub(super) const DATA_NAMES: &[&str] = &[
    "nwr_all_index_b",
    "nwr_ctor_fields_b",
    "nwr_member_fields_b",
    "nwr_first_fields_b",
    "nwr_nonempty_b",
    "nwr_raw_return_b",
    "nwr_empty_ctor_sources",
    "nwr_bad_other_member",
    "nwr_bad_other_sources",
    "nwr_short_former_sources",
    "nwr_wrong_level_sources",
];

#[cfg(test)]
pub(super) const INDUCTIVE_NAMES: &[&str] = &[];

#[cfg(test)]
pub(super) const NEGATIVE_CONTROLS: &[(&str, &str, &str)] = &[
    (
        "nwr_false_empty_accepts",
        r"Eq (Bool) (nwr_raw_return_b (nrb_demo_levels) (Nat.succ Nat.zero) (ListType.nil (NamedMemberSource))) (Bool.true)",
        r"Eq.refl (Bool) (Bool.true)",
    ),
    (
        "nwr_false_other_member_accepts",
        r"Eq (Bool) (nwr_raw_return_b (nrb_demo_levels) (Nat.succ Nat.zero) (nwr_bad_other_sources)) (Bool.true)",
        r"Eq.refl (Bool) (Bool.true)",
    ),
    (
        "nwr_false_installed_outcome",
        r"Eq (Bool) (nrb_block_return_b (nsi_raw_install ((nrb_demo_levels)) ((Nat.succ Nat.zero)) ((nsi_demo_sources)) (IndCtorEnv.empty)) (nsi_names (NamedMemberSource) (nsi_member_name) ((nsi_demo_sources)))) (Bool.false)",
        r"nwr_demo_installed_success (IndCtorEnv.empty)",
    ),
    (
        "nwr_false_selected_family",
        r"NamedStrictAppFacts (nsi_names (NamedMemberSource) (nsi_member_name) ((nsi_demo_sources))) (nig_param_levels ((nrb_demo_levels))) nrb_demo_f (count_pi (nsi_ctor_type ((nsi_demo_cg2)))) ((Nat.succ Nat.zero)) (kind_num_indices (nsi_member_meta ((nrb_demo_levels)) ((Nat.succ Nat.zero)) (nsi_names (NamedMemberSource) (nsi_member_name) ((nsi_demo_sources))) ((nsi_demo_g)))) (return_type (nsi_ctor_type ((nsi_demo_cg2))))",
        r"nwr_demo_selected_second_ctor (IndCtorEnv.empty)",
    ),
];

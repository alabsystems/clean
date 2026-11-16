// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::DeclarationInput;

pub(super) const DECLARATIONS: &[DeclarationInput] = &[
    DeclarationInput::Data(
        "nsi_name_append",
        r"forall (xs ys : ListType Name), ListType Name",
        r"fun (xs ys : ListType Name) => @ListType.rec Name
 (fun (_ns : ListType Name) => ListType Name) ys
 (fun (n : Name) (_ns : ListType Name) (ih : ListType Name) => @ListType.cons Name n ih) xs",
    ),
    DeclarationInput::Proof(
        "nsi_mem_cons_false_head",
        r"forall (n : Name) (xs : ListType Name) (q : Name), @Eq Bool (name_list_mem (@ListType.cons Name n xs) q) Bool.false -> @Eq Bool (name_eqb n q) Bool.false",
        r"fun (n : Name) (xs : ListType Name) (q : Name)
 (absent : @Eq Bool (name_list_mem (@ListType.cons Name n xs) q) Bool.false) =>
 projection_absent_or_left (name_eqb n q) (name_list_mem xs q) absent",
    ),
    DeclarationInput::Proof(
        "nsi_mem_cons_false_tail",
        r"forall (n : Name) (xs : ListType Name) (q : Name), @Eq Bool (name_list_mem (@ListType.cons Name n xs) q) Bool.false -> @Eq Bool (name_list_mem xs q) Bool.false",
        r"fun (n : Name) (xs : ListType Name) (q : Name)
 (absent : @Eq Bool (name_list_mem (@ListType.cons Name n xs) q) Bool.false) =>
 projection_absent_or_right (name_eqb n q) (name_list_mem xs q) absent",
    ),
    DeclarationInput::Proof(
        "nsi_mem_cons_false_intro",
        r"forall (n : Name) (xs : ListType Name) (q : Name), @Eq Bool (name_eqb n q) Bool.false -> @Eq Bool (name_list_mem xs q) Bool.false -> @Eq Bool (name_list_mem (@ListType.cons Name n xs) q) Bool.false",
        r"fun (n : Name) (xs : ListType Name) (q : Name)
 (different : @Eq Bool (name_eqb n q) Bool.false)
 (absent : @Eq Bool (name_list_mem xs q) Bool.false) =>
 Eq.trans Bool (Bool.or (name_eqb n q) (name_list_mem xs q))
  (Bool.or Bool.false (name_list_mem xs q)) Bool.false
  (Eq.cong Bool Bool (fun (b : Bool) => Bool.or b (name_list_mem xs q))
   (name_eqb n q) Bool.false different) absent",
    ),
    DeclarationInput::Proof(
        "nsi_mem_cons_true_head",
        r"forall (n : Name) (xs : ListType Name), @Eq Bool (name_list_mem (@ListType.cons Name n xs) n) Bool.true",
        r"fun (n : Name) (xs : ListType Name) =>
 Eq.cong Bool Bool (fun (b : Bool) => Bool.or b (name_list_mem xs n))
  (name_eqb n n) Bool.true (name_eqb_refl n)",
    ),
    DeclarationInput::Proof(
        "nsi_mem_cons_true_tail",
        r"forall (n : Name) (xs : ListType Name) (q : Name), @Eq Bool (name_list_mem xs q) Bool.true -> @Eq Bool (name_list_mem (@ListType.cons Name n xs) q) Bool.true",
        r"fun (n : Name) (xs : ListType Name) (q : Name)
 (member : @Eq Bool (name_list_mem xs q) Bool.true) => @Bool.rec
 (fun (b : Bool) => @Eq Bool (Bool.or b (name_list_mem xs q)) Bool.true)
 member (@Eq.refl Bool Bool.true) (name_eqb n q)",
    ),
    DeclarationInput::Proof(
        "nsi_unique_cons_head",
        r"forall (n : Name) (xs : ListType Name), @Eq Bool (nrb_names_unique_b (@ListType.cons Name n xs)) Bool.true -> @Eq Bool (name_list_mem xs n) Bool.false",
        r"fun (n : Name) (xs : ListType Name)
 (unique : @Eq Bool (nrb_names_unique_b (@ListType.cons Name n xs)) Bool.true) =>
 nig_not_true_false (name_list_mem xs n)
  (band_eq_true_left (Bool.not (name_list_mem xs n)) (nrb_names_unique_b xs) unique)",
    ),
    DeclarationInput::Proof(
        "nsi_unique_cons_tail",
        r"forall (n : Name) (xs : ListType Name), @Eq Bool (nrb_names_unique_b (@ListType.cons Name n xs)) Bool.true -> @Eq Bool (nrb_names_unique_b xs) Bool.true",
        r"fun (n : Name) (xs : ListType Name)
 (unique : @Eq Bool (nrb_names_unique_b (@ListType.cons Name n xs)) Bool.true) =>
 band_eq_true_right (Bool.not (name_list_mem xs n)) (nrb_names_unique_b xs) unique",
    ),
    DeclarationInput::Proof(
        "nsi_unique_cons_intro",
        r"forall (n : Name) (xs : ListType Name), @Eq Bool (name_list_mem xs n) Bool.false -> @Eq Bool (nrb_names_unique_b xs) Bool.true -> @Eq Bool (nrb_names_unique_b (@ListType.cons Name n xs)) Bool.true",
        r"fun (n : Name) (xs : ListType Name)
 (absent : @Eq Bool (name_list_mem xs n) Bool.false)
 (unique : @Eq Bool (nrb_names_unique_b xs) Bool.true) =>
 nig_and_intro (Bool.not (name_list_mem xs n)) (nrb_names_unique_b xs)
  (Eq.cong Bool Bool (fun (b : Bool) => Bool.not b) (name_list_mem xs n) Bool.false absent)
  unique",
    ),
    DeclarationInput::Proof(
        "nsi_mem_append_false_left",
        r"forall (xs ys : ListType Name) (q : Name), @Eq Bool (name_list_mem (nsi_name_append xs ys) q) Bool.false -> @Eq Bool (name_list_mem xs q) Bool.false",
        r"fun (xs : ListType Name) => @ListType.rec Name
 (fun (ns : ListType Name) => forall (ys : ListType Name) (q : Name), @Eq Bool (name_list_mem (nsi_name_append ns ys) q) Bool.false -> @Eq Bool (name_list_mem ns q) Bool.false)
 (fun (ys : ListType Name) (q : Name) (_absent : @Eq Bool (name_list_mem ys q) Bool.false) => @Eq.refl Bool Bool.false)
 (fun (n : Name) (ns : ListType Name)
  (ih : forall (ys : ListType Name) (q : Name), @Eq Bool (name_list_mem (nsi_name_append ns ys) q) Bool.false -> @Eq Bool (name_list_mem ns q) Bool.false)
  (ys : ListType Name) (q : Name)
  (absent : @Eq Bool (name_list_mem (@ListType.cons Name n (nsi_name_append ns ys)) q) Bool.false) =>
  nsi_mem_cons_false_intro n ns q
   (nsi_mem_cons_false_head n (nsi_name_append ns ys) q absent)
   (ih ys q (nsi_mem_cons_false_tail n (nsi_name_append ns ys) q absent))) xs",
    ),
    DeclarationInput::Proof(
        "nsi_mem_append_false_right",
        r"forall (xs ys : ListType Name) (q : Name), @Eq Bool (name_list_mem (nsi_name_append xs ys) q) Bool.false -> @Eq Bool (name_list_mem ys q) Bool.false",
        r"fun (xs : ListType Name) => @ListType.rec Name
 (fun (ns : ListType Name) => forall (ys : ListType Name) (q : Name), @Eq Bool (name_list_mem (nsi_name_append ns ys) q) Bool.false -> @Eq Bool (name_list_mem ys q) Bool.false)
 (fun (ys : ListType Name) (q : Name) (absent : @Eq Bool (name_list_mem ys q) Bool.false) => absent)
 (fun (n : Name) (ns : ListType Name)
  (ih : forall (ys : ListType Name) (q : Name), @Eq Bool (name_list_mem (nsi_name_append ns ys) q) Bool.false -> @Eq Bool (name_list_mem ys q) Bool.false)
  (ys : ListType Name) (q : Name)
  (absent : @Eq Bool (name_list_mem (@ListType.cons Name n (nsi_name_append ns ys)) q) Bool.false) =>
  ih ys q (nsi_mem_cons_false_tail n (nsi_name_append ns ys) q absent)) xs",
    ),
    DeclarationInput::Proof(
        "nsi_unique_append_left",
        r"forall (xs ys : ListType Name), @Eq Bool (nrb_names_unique_b (nsi_name_append xs ys)) Bool.true -> @Eq Bool (nrb_names_unique_b xs) Bool.true",
        r"fun (xs : ListType Name) => @ListType.rec Name
 (fun (ns : ListType Name) => forall (ys : ListType Name), @Eq Bool (nrb_names_unique_b (nsi_name_append ns ys)) Bool.true -> @Eq Bool (nrb_names_unique_b ns) Bool.true)
 (fun (ys : ListType Name) (_unique : @Eq Bool (nrb_names_unique_b ys) Bool.true) => @Eq.refl Bool Bool.true)
 (fun (n : Name) (ns : ListType Name)
  (ih : forall (ys : ListType Name), @Eq Bool (nrb_names_unique_b (nsi_name_append ns ys)) Bool.true -> @Eq Bool (nrb_names_unique_b ns) Bool.true)
  (ys : ListType Name)
  (unique : @Eq Bool (nrb_names_unique_b (@ListType.cons Name n (nsi_name_append ns ys))) Bool.true) =>
  nsi_unique_cons_intro n ns
   (nsi_mem_append_false_left ns ys n (nsi_unique_cons_head n (nsi_name_append ns ys) unique))
   (ih ys (nsi_unique_cons_tail n (nsi_name_append ns ys) unique))) xs",
    ),
    DeclarationInput::Proof(
        "nsi_unique_append_right",
        r"forall (xs ys : ListType Name), @Eq Bool (nrb_names_unique_b (nsi_name_append xs ys)) Bool.true -> @Eq Bool (nrb_names_unique_b ys) Bool.true",
        r"fun (xs : ListType Name) => @ListType.rec Name
 (fun (ns : ListType Name) => forall (ys : ListType Name), @Eq Bool (nrb_names_unique_b (nsi_name_append ns ys)) Bool.true -> @Eq Bool (nrb_names_unique_b ys) Bool.true)
 (fun (ys : ListType Name) (unique : @Eq Bool (nrb_names_unique_b ys) Bool.true) => unique)
 (fun (n : Name) (ns : ListType Name)
  (ih : forall (ys : ListType Name), @Eq Bool (nrb_names_unique_b (nsi_name_append ns ys)) Bool.true -> @Eq Bool (nrb_names_unique_b ys) Bool.true)
  (ys : ListType Name)
  (unique : @Eq Bool (nrb_names_unique_b (@ListType.cons Name n (nsi_name_append ns ys))) Bool.true) =>
  ih ys (nsi_unique_cons_tail n (nsi_name_append ns ys) unique)) xs",
    ),
    DeclarationInput::Proof(
        "nsi_unique_append_cross",
        r"forall (xs ys : ListType Name) (q : Name), @Eq Bool (nrb_names_unique_b (nsi_name_append xs ys)) Bool.true -> @Eq Bool (name_list_mem xs q) Bool.true -> @Eq Bool (name_list_mem ys q) Bool.false",
        r"fun (xs : ListType Name) => @ListType.rec Name
 (fun (ns : ListType Name) => forall (ys : ListType Name) (q : Name), @Eq Bool (nrb_names_unique_b (nsi_name_append ns ys)) Bool.true -> @Eq Bool (name_list_mem ns q) Bool.true -> @Eq Bool (name_list_mem ys q) Bool.false)
 (fun (ys : ListType Name) (q : Name)
  (_unique : @Eq Bool (nrb_names_unique_b ys) Bool.true)
  (bad : @Eq Bool Bool.false Bool.true) =>
  bool_false_ne_true (@Eq Bool (name_list_mem ys q) Bool.false) bad)
 (fun (n : Name) (ns : ListType Name)
  (ih : forall (ys : ListType Name) (q : Name), @Eq Bool (nrb_names_unique_b (nsi_name_append ns ys)) Bool.true -> @Eq Bool (name_list_mem ns q) Bool.true -> @Eq Bool (name_list_mem ys q) Bool.false)
  (ys : ListType Name) (q : Name)
  (unique : @Eq Bool (nrb_names_unique_b (@ListType.cons Name n (nsi_name_append ns ys))) Bool.true)
  (member : @Eq Bool (Bool.or (name_eqb n q) (name_list_mem ns q)) Bool.true) =>
  nig_or_elim_prop (name_eqb n q) (name_list_mem ns q) (@Eq Bool (name_list_mem ys q) Bool.false) member
   (fun (same : @Eq Bool (name_eqb n q) Bool.true) =>
    Eq.subst Name (fun (z : Name) => @Eq Bool (name_list_mem ys z) Bool.false) n q (name_eqb_eq n q same)
     (nsi_mem_append_false_right ns ys n (nsi_unique_cons_head n (nsi_name_append ns ys) unique)))
   (fun (tail : @Eq Bool (name_list_mem ns q) Bool.true) =>
    ih ys q (nsi_unique_cons_tail n (nsi_name_append ns ys) unique) tail)) xs",
    ),
    DeclarationInput::Proof(
        "nsi_unique_append_cross_right",
        r"forall (xs ys : ListType Name) (q : Name), @Eq Bool (nrb_names_unique_b (nsi_name_append xs ys)) Bool.true -> @Eq Bool (name_list_mem ys q) Bool.true -> @Eq Bool (name_list_mem xs q) Bool.false",
        r"fun (xs ys : ListType Name) (q : Name)
 (unique : @Eq Bool (nrb_names_unique_b (nsi_name_append xs ys)) Bool.true)
 (member : @Eq Bool (name_list_mem ys q) Bool.true) => @Bool.rec
 (fun (b : Bool) => @Eq Bool (name_list_mem xs q) b -> @Eq Bool (name_list_mem xs q) Bool.false)
 (fun (absent : @Eq Bool (name_list_mem xs q) Bool.false) => absent)
 (fun (present : @Eq Bool (name_list_mem xs q) Bool.true) =>
  bool_false_ne_true (@Eq Bool (name_list_mem xs q) Bool.false)
   (Eq.trans Bool Bool.false (name_list_mem ys q) Bool.true
    (Eq.symm Bool (name_list_mem ys q) Bool.false (nsi_unique_append_cross xs ys q unique present)) member))
 (name_list_mem xs q) (@Eq.refl Bool (name_list_mem xs q))",
    ),
    DeclarationInput::Proof(
        "nsi_mem_append_false_intro",
        r"forall (xs ys : ListType Name) (q : Name), @Eq Bool (name_list_mem xs q) Bool.false -> @Eq Bool (name_list_mem ys q) Bool.false -> @Eq Bool (name_list_mem (nsi_name_append xs ys) q) Bool.false",
        r"fun (xs : ListType Name) => @ListType.rec Name
 (fun (ns : ListType Name) => forall (ys : ListType Name) (q : Name), @Eq Bool (name_list_mem ns q) Bool.false -> @Eq Bool (name_list_mem ys q) Bool.false -> @Eq Bool (name_list_mem (nsi_name_append ns ys) q) Bool.false)
 (fun (ys : ListType Name) (q : Name) (_left : @Eq Bool Bool.false Bool.false)
  (right : @Eq Bool (name_list_mem ys q) Bool.false) => right)
 (fun (n : Name) (ns : ListType Name)
  (ih : forall (ys : ListType Name) (q : Name), @Eq Bool (name_list_mem ns q) Bool.false -> @Eq Bool (name_list_mem ys q) Bool.false -> @Eq Bool (name_list_mem (nsi_name_append ns ys) q) Bool.false)
  (ys : ListType Name) (q : Name)
  (left : @Eq Bool (name_list_mem (@ListType.cons Name n ns) q) Bool.false)
  (right : @Eq Bool (name_list_mem ys q) Bool.false) =>
  nsi_mem_cons_false_intro n (nsi_name_append ns ys) q
   (nsi_mem_cons_false_head n ns q left)
   (ih ys q (nsi_mem_cons_false_tail n ns q left) right)) xs",
    ),
    DeclarationInput::Proof(
        "nsi_unique_append_remove_middle",
        r"forall (xs ys zs : ListType Name), @Eq Bool (nrb_names_unique_b (nsi_name_append xs (nsi_name_append ys zs))) Bool.true -> @Eq Bool (nrb_names_unique_b (nsi_name_append xs zs)) Bool.true",
        r"fun (xs : ListType Name) => @ListType.rec Name
 (fun (ns : ListType Name) => forall (ys zs : ListType Name), @Eq Bool (nrb_names_unique_b (nsi_name_append ns (nsi_name_append ys zs))) Bool.true -> @Eq Bool (nrb_names_unique_b (nsi_name_append ns zs)) Bool.true)
 (fun (ys zs : ListType Name)
  (unique : @Eq Bool (nrb_names_unique_b (nsi_name_append ys zs)) Bool.true) =>
  nsi_unique_append_right ys zs unique)
 (fun (n : Name) (ns : ListType Name)
  (ih : forall (ys zs : ListType Name), @Eq Bool (nrb_names_unique_b (nsi_name_append ns (nsi_name_append ys zs))) Bool.true -> @Eq Bool (nrb_names_unique_b (nsi_name_append ns zs)) Bool.true)
  (ys zs : ListType Name)
  (unique : @Eq Bool (nrb_names_unique_b (@ListType.cons Name n (nsi_name_append ns (nsi_name_append ys zs)))) Bool.true) =>
  nsi_unique_cons_intro n (nsi_name_append ns zs)
   (nsi_mem_append_false_intro ns zs n
    (nsi_mem_append_false_left ns (nsi_name_append ys zs) n
     (nsi_unique_cons_head n (nsi_name_append ns (nsi_name_append ys zs)) unique))
    (nsi_mem_append_false_right ys zs n
     (nsi_mem_append_false_right ns (nsi_name_append ys zs) n
      (nsi_unique_cons_head n (nsi_name_append ns (nsi_name_append ys zs)) unique))))
   (ih ys zs (nsi_unique_cons_tail n (nsi_name_append ns (nsi_name_append ys zs)) unique))) xs",
    ),
    DeclarationInput::Inductive(
        r"inductive NamedCtorSource : Type
| mk : Name -> KExpr -> NamedCtorSource",
    ),
    DeclarationInput::Inductive(
        r"inductive NamedMemberSource : Type
| mk : Name -> KExpr -> ListType NamedCtorSource -> NamedMemberSource",
    ),
    DeclarationInput::Data(
        "nsi_ctor_name",
        r"NamedCtorSource -> Name",
        r"fun (c : NamedCtorSource) => @NamedCtorSource.rec (fun (_c : NamedCtorSource) => Name) (fun (n : Name) (_t : KExpr) => n) c",
    ),
    DeclarationInput::Data(
        "nsi_ctor_type",
        r"NamedCtorSource -> KExpr",
        r"fun (c : NamedCtorSource) => @NamedCtorSource.rec (fun (_c : NamedCtorSource) => KExpr) (fun (_n : Name) (t : KExpr) => t) c",
    ),
    DeclarationInput::Data(
        "nsi_member_name",
        r"NamedMemberSource -> Name",
        r"fun (m : NamedMemberSource) => @NamedMemberSource.rec (fun (_m : NamedMemberSource) => Name) (fun (n : Name) (_t : KExpr) (_cs : ListType NamedCtorSource) => n) m",
    ),
    DeclarationInput::Data(
        "nsi_member_type",
        r"NamedMemberSource -> KExpr",
        r"fun (m : NamedMemberSource) => @NamedMemberSource.rec (fun (_m : NamedMemberSource) => KExpr) (fun (_n : Name) (t : KExpr) (_cs : ListType NamedCtorSource) => t) m",
    ),
    DeclarationInput::Data(
        "nsi_member_ctors",
        r"NamedMemberSource -> ListType NamedCtorSource",
        r"fun (m : NamedMemberSource) => @NamedMemberSource.rec (fun (_m : NamedMemberSource) => ListType NamedCtorSource) (fun (_n : Name) (_t : KExpr) (cs : ListType NamedCtorSource) => cs) m",
    ),
    DeclarationInput::Data(
        "nsi_names",
        r"forall (A : Type) (f : A -> Name) (xs : ListType A), ListType Name",
        r"fun (A : Type) (f : A -> Name) (xs : ListType A) => @ListType.rec A (fun (_xs : ListType A) => ListType Name) (@ListType.nil Name) (fun (x : A) (_xs : ListType A) (ih : ListType Name) => @ListType.cons Name (f x) ih) xs",
    ),
    DeclarationInput::Data(
        "nsi_at",
        r"forall (A : Type) (xs : ListType A) (j : Nat), OptionType A",
        r"fun (A : Type) (xs : ListType A) => @ListType.rec A (fun (_xs : ListType A) => Nat -> OptionType A) (fun (_j : Nat) => @OptionType.none A) (fun (x : A) (_xs : ListType A) (ih : Nat -> OptionType A) (j : Nat) => @Nat.rec (fun (_j : Nat) => OptionType A) (@OptionType.some A x) (fun (k : Nat) (_unused : OptionType A) => ih k) j) xs",
    ),
    DeclarationInput::Data(
        "nsi_all_ctor_names",
        r"ListType NamedMemberSource -> ListType Name",
        r"fun (ms : ListType NamedMemberSource) => @ListType.rec NamedMemberSource (fun (_ms : ListType NamedMemberSource) => ListType Name) (@ListType.nil Name) (fun (m : NamedMemberSource) (_ms : ListType NamedMemberSource) (ih : ListType Name) => nsi_name_append (nsi_names (NamedCtorSource) (nsi_ctor_name) (nsi_member_ctors (m))) (ih)) ms",
    ),
    DeclarationInput::Data(
        "nsi_all_names",
        r"ListType NamedMemberSource -> ListType Name",
        r"fun (ms : ListType NamedMemberSource) => nsi_name_append (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (nsi_all_ctor_names (ms))",
    ),
    DeclarationInput::Data(
        "nsi_ctor_meta",
        r"forall (us : ListType Name) (p : Nat) (parent : Name) (i : Nat) (c : NamedCtorSource), KCtorMeta",
        r"fun (us : ListType Name) (p : Nat) (parent : Name) (i : Nat) (c : NamedCtorSource) => KCtorMeta.mk (KConstSig.mk us (nsi_ctor_type (c))) parent p (Nat.sub (count_pi (nsi_ctor_type (c))) p) i",
    ),
    DeclarationInput::Data(
        "nsi_member_meta",
        r"forall (us : ListType Name) (p : Nat) (block : ListType Name) (m : NamedMemberSource), KIndMeta",
        r"fun (us : ListType Name) (p : Nat) (block : ListType Name) (m : NamedMemberSource) => KIndMeta.mk (KConstSig.mk us (nsi_member_type (m))) p (Nat.sub (count_pi (nsi_member_type (m))) p) (nsi_names (NamedCtorSource) (nsi_ctor_name) (nsi_member_ctors (m))) block",
    ),
    DeclarationInput::Data(
        "nsi_install_ctors",
        r"forall (us : ListType Name) (p : Nat) (parent : Name) (cs : ListType NamedCtorSource) (i : Nat) (base : IndCtorEnv), IndCtorEnv",
        r"fun (us : ListType Name) (p : Nat) (parent : Name) (cs : ListType NamedCtorSource) => @ListType.rec NamedCtorSource
 (fun (_cs : ListType NamedCtorSource) => Nat -> IndCtorEnv -> IndCtorEnv)
 (fun (_i : Nat) (base : IndCtorEnv) => base)
 (fun (c : NamedCtorSource) (_cs : ListType NamedCtorSource) (ih : Nat -> IndCtorEnv -> IndCtorEnv) (i : Nat) (base : IndCtorEnv) => ih (Nat.succ i) (IndCtorEnv.addCtor base (nsi_ctor_name (c)) (nsi_ctor_meta (us) (p) (parent) (i) (c)))) cs",
    ),
    DeclarationInput::Data(
        "nsi_install_members",
        r"forall (us : ListType Name) (p : Nat) (block : ListType Name) (ms : ListType NamedMemberSource) (base : IndCtorEnv), IndCtorEnv",
        r"fun (us : ListType Name) (p : Nat) (block : ListType Name) (ms : ListType NamedMemberSource) => @ListType.rec NamedMemberSource
 (fun (_ms : ListType NamedMemberSource) => IndCtorEnv -> IndCtorEnv)
 (fun (base : IndCtorEnv) => base)
 (fun (m : NamedMemberSource) (_ms : ListType NamedMemberSource) (ih : IndCtorEnv -> IndCtorEnv) (base : IndCtorEnv) => ih (IndCtorEnv.addInd (nsi_install_ctors (us) (p) (nsi_member_name (m)) (nsi_member_ctors (m)) (Nat.zero) (base)) (nsi_member_name (m)) (nsi_member_meta (us) (p) (block) (m)))) ms",
    ),
    DeclarationInput::Data(
        "nsi_raw_install",
        r"forall (us : ListType Name) (p : Nat) (ms : ListType NamedMemberSource) (base : IndCtorEnv), IndCtorEnv",
        r"fun (us : ListType Name) (p : Nat) (ms : ListType NamedMemberSource) (base : IndCtorEnv) => nsi_install_members (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (ms) (base)",
    ),
    DeclarationInput::Proof(
        "nsi_at_mem",
        r"forall (A : Type) (f : A -> Name) (xs : ListType A), forall (j : Nat) (x : A), @Eq (OptionType A) (nsi_at (A) (xs) (j)) (@OptionType.some (A) (x)) -> @Eq (Bool) (name_list_mem (nsi_names (A) (f) (xs)) (f (x))) (Bool.true)",
        r"fun (A : Type) (f : A -> Name) (xs : ListType A) => @ListType.rec A
 (fun (ns : ListType A) => forall (j : Nat) (x : A), @Eq (OptionType A) (nsi_at (A) (ns) (j)) (@OptionType.some (A) (x)) -> @Eq (Bool) (name_list_mem (nsi_names (A) (f) (ns)) (f (x))) (Bool.true))
 (fun (j : Nat) (x : A) (bad : @Eq (OptionType A) (nsi_at (A) (@ListType.nil (A)) (j)) (@OptionType.some (A) (x))) => option_none_ne_some (A) (x) (@Eq (Bool) (name_list_mem (nsi_names (A) (f) (@ListType.nil (A))) (f (x))) (Bool.true)) (bad))
 (fun (x0 : A) (tail : ListType A) (ih : forall (j : Nat) (x : A), @Eq (OptionType A) (nsi_at (A) (tail) (j)) (@OptionType.some (A) (x)) -> @Eq (Bool) (name_list_mem (nsi_names (A) (f) (tail)) (f (x))) (Bool.true)) (j : Nat) => @Nat.rec
  (fun (k : Nat) => forall (x : A), @Eq (OptionType A) (nsi_at (A) (@ListType.cons (A) (x0) (tail)) (k)) (@OptionType.some (A) (x)) -> @Eq (Bool) (name_list_mem (nsi_names (A) (f) (@ListType.cons (A) (x0) (tail))) (f (x))) (Bool.true))
  (fun (x : A) (found : @Eq (OptionType A) (@OptionType.some (A) (x0)) (@OptionType.some (A) (x))) => Eq.subst (A) (fun (y : A) => @Eq (Bool) (name_list_mem (nsi_names (A) (f) (@ListType.cons (A) (x0) (tail))) (f (y))) (Bool.true)) (x0) (x) (option_some_inj (A) (x0) (x) (found)) (nsi_mem_cons_true_head (f (x0)) (nsi_names (A) (f) (tail))))
  (fun (k : Nat) (_unused : forall (x : A), @Eq (OptionType A) (nsi_at (A) (@ListType.cons (A) (x0) (tail)) (k)) (@OptionType.some (A) (x)) -> @Eq (Bool) (name_list_mem (nsi_names (A) (f) (@ListType.cons (A) (x0) (tail))) (f (x))) (Bool.true)) (x : A) (found : @Eq (OptionType A) (nsi_at (A) (tail) (k)) (@OptionType.some (A) (x))) => nsi_mem_cons_true_tail (f (x0)) (nsi_names (A) (f) (tail)) (f (x)) (ih (k) (x) (found))) j) xs",
    ),
    DeclarationInput::Proof(
        "nsi_at_name_at",
        r"forall (A : Type) (f : A -> Name) (xs : ListType A), forall (j : Nat) (x : A), @Eq (OptionType A) (nsi_at (A) (xs) (j)) (@OptionType.some (A) (x)) -> @Eq (OptionType Name) (nrb_name_at (nsi_names (A) (f) (xs)) (j)) (@OptionType.some (Name) (f (x)))",
        r"fun (A : Type) (f : A -> Name) (xs : ListType A) => @ListType.rec A
 (fun (ns : ListType A) => forall (j : Nat) (x : A), @Eq (OptionType A) (nsi_at (A) (ns) (j)) (@OptionType.some (A) (x)) -> @Eq (OptionType Name) (nrb_name_at (nsi_names (A) (f) (ns)) (j)) (@OptionType.some (Name) (f (x))))
 (fun (j : Nat) (x : A) (bad : @Eq (OptionType A) (nsi_at (A) (@ListType.nil (A)) (j)) (@OptionType.some (A) (x))) => option_none_ne_some (A) (x) (@Eq (OptionType Name) (nrb_name_at (nsi_names (A) (f) (@ListType.nil (A))) (j)) (@OptionType.some (Name) (f (x)))) (bad))
 (fun (x0 : A) (tail : ListType A) (ih : forall (j : Nat) (x : A), @Eq (OptionType A) (nsi_at (A) (tail) (j)) (@OptionType.some (A) (x)) -> @Eq (OptionType Name) (nrb_name_at (nsi_names (A) (f) (tail)) (j)) (@OptionType.some (Name) (f (x)))) (j : Nat) => @Nat.rec
  (fun (k : Nat) => forall (x : A), @Eq (OptionType A) (nsi_at (A) (@ListType.cons (A) (x0) (tail)) (k)) (@OptionType.some (A) (x)) -> @Eq (OptionType Name) (nrb_name_at (nsi_names (A) (f) (@ListType.cons (A) (x0) (tail))) (k)) (@OptionType.some (Name) (f (x))))
  (fun (x : A) (found : @Eq (OptionType A) (@OptionType.some (A) (x0)) (@OptionType.some (A) (x))) => Eq.subst (A) (fun (y : A) => @Eq (OptionType Name) (nrb_name_at (nsi_names (A) (f) (@ListType.cons (A) (x0) (tail))) (Nat.zero)) (@OptionType.some (Name) (f (y)))) (x0) (x) (option_some_inj (A) (x0) (x) (found)) (@Eq.refl (OptionType Name) (@OptionType.some (Name) (f (x0)))))
  (fun (k : Nat) (_unused : forall (x : A), @Eq (OptionType A) (nsi_at (A) (@ListType.cons (A) (x0) (tail)) (k)) (@OptionType.some (A) (x)) -> @Eq (OptionType Name) (nrb_name_at (nsi_names (A) (f) (@ListType.cons (A) (x0) (tail))) (k)) (@OptionType.some (Name) (f (x)))) (x : A) (found : @Eq (OptionType A) (nsi_at (A) (tail) (k)) (@OptionType.some (A) (x))) => ih (k) (x) (found)) j) xs",
    ),
    DeclarationInput::Proof(
        "nsi_ctor_install_absent",
        r"forall (us : ListType Name) (p : Nat) (parent : Name) (cs : ListType NamedCtorSource), forall (i : Nat) (base : IndCtorEnv) (q : Name), @Eq (Bool) (name_list_mem (nsi_names (NamedCtorSource) (nsi_ctor_name) (cs)) (q)) (Bool.false) -> @Eq (OptionType KCtorMeta) (kctor_for (nsi_install_ctors (us) (p) (parent) (cs) (i) (base)) (q)) (kctor_for (base) (q))",
        r"fun (us : ListType Name) (p : Nat) (parent : Name) (cs : ListType NamedCtorSource) => @ListType.rec NamedCtorSource
 (fun (xs : ListType NamedCtorSource) => forall (i : Nat) (base : IndCtorEnv) (q : Name), @Eq (Bool) (name_list_mem (nsi_names (NamedCtorSource) (nsi_ctor_name) (xs)) (q)) (Bool.false) -> @Eq (OptionType KCtorMeta) (kctor_for (nsi_install_ctors (us) (p) (parent) (xs) (i) (base)) (q)) (kctor_for (base) (q)))
 (fun (i : Nat) (base : IndCtorEnv) (q : Name) (_absent : @Eq (Bool) (name_list_mem (@ListType.nil (Name)) (q)) (Bool.false)) => @Eq.refl (OptionType KCtorMeta) (kctor_for (base) (q)))
 (fun (c : NamedCtorSource) (tail : ListType NamedCtorSource) (ih : forall (i : Nat) (base : IndCtorEnv) (q : Name), @Eq (Bool) (name_list_mem (nsi_names (NamedCtorSource) (nsi_ctor_name) (tail)) (q)) (Bool.false) -> @Eq (OptionType KCtorMeta) (kctor_for (nsi_install_ctors (us) (p) (parent) (tail) (i) (base)) (q)) (kctor_for (base) (q))) (i : Nat) (base : IndCtorEnv) (q : Name) (no_name : @Eq (Bool) (name_list_mem (nsi_names (NamedCtorSource) (nsi_ctor_name) (@ListType.cons (NamedCtorSource) (c) (tail))) (q)) (Bool.false)) =>
  Eq.trans (OptionType KCtorMeta) (kctor_for (nsi_install_ctors (us) (p) (parent) (tail) (Nat.succ i) (IndCtorEnv.addCtor (base) (nsi_ctor_name (c)) (nsi_ctor_meta (us) (p) (parent) (i) (c)))) (q)) (kctor_for (IndCtorEnv.addCtor (base) (nsi_ctor_name (c)) (nsi_ctor_meta (us) (p) (parent) (i) (c))) (q)) (kctor_for (base) (q)) (ih (Nat.succ i) (IndCtorEnv.addCtor (base) (nsi_ctor_name (c)) (nsi_ctor_meta (us) (p) (parent) (i) (c))) (q) (nsi_mem_cons_false_tail (nsi_ctor_name (c)) (nsi_names (NamedCtorSource) (nsi_ctor_name) (tail)) (q) (no_name))) (ict_ctor_add_ctor_other (base) (nsi_ctor_name (c)) (q) (nsi_ctor_meta (us) (p) (parent) (i) (c)) (nsi_mem_cons_false_head (nsi_ctor_name (c)) (nsi_names (NamedCtorSource) (nsi_ctor_name) (tail)) (q) (no_name)))) cs",
    ),
    DeclarationInput::Proof(
        "nsi_ctor_install_selected",
        r"forall (us : ListType Name) (p : Nat) (parent : Name) (cs : ListType NamedCtorSource), forall (i : Nat) (base : IndCtorEnv) (j : Nat) (c : NamedCtorSource), @Eq (Bool) (nrb_names_unique_b (nsi_names (NamedCtorSource) (nsi_ctor_name) (cs))) (Bool.true) -> @Eq (OptionType NamedCtorSource) (nsi_at (NamedCtorSource) (cs) (j)) (@OptionType.some (NamedCtorSource) (c)) -> @Eq (OptionType KCtorMeta) (kctor_for (nsi_install_ctors (us) (p) (parent) (cs) (i) (base)) (nsi_ctor_name (c))) (@OptionType.some (KCtorMeta) (nsi_ctor_meta (us) (p) (parent) (Nat.add (i) (j)) (c)))",
        r"fun (us : ListType Name) (p : Nat) (parent : Name) (cs : ListType NamedCtorSource) => @ListType.rec NamedCtorSource
 (fun (xs : ListType NamedCtorSource) => forall (i : Nat) (base : IndCtorEnv) (j : Nat) (c : NamedCtorSource), @Eq (Bool) (nrb_names_unique_b (nsi_names (NamedCtorSource) (nsi_ctor_name) (xs))) (Bool.true) -> @Eq (OptionType NamedCtorSource) (nsi_at (NamedCtorSource) (xs) (j)) (@OptionType.some (NamedCtorSource) (c)) -> @Eq (OptionType KCtorMeta) (kctor_for (nsi_install_ctors (us) (p) (parent) (xs) (i) (base)) (nsi_ctor_name (c))) (@OptionType.some (KCtorMeta) (nsi_ctor_meta (us) (p) (parent) (Nat.add (i) (j)) (c))))
 (fun (i : Nat) (base : IndCtorEnv) (j : Nat) (c : NamedCtorSource) (_unique : @Eq (Bool) (nrb_names_unique_b (@ListType.nil (Name))) (Bool.true)) (bad : @Eq (OptionType NamedCtorSource) (nsi_at (NamedCtorSource) (@ListType.nil (NamedCtorSource)) (j)) (@OptionType.some (NamedCtorSource) (c))) => option_none_ne_some (NamedCtorSource) (c) (@Eq (OptionType KCtorMeta) (kctor_for (nsi_install_ctors (us) (p) (parent) (@ListType.nil (NamedCtorSource)) (i) (base)) (nsi_ctor_name (c))) (@OptionType.some (KCtorMeta) (nsi_ctor_meta (us) (p) (parent) (Nat.add (i) (j)) (c)))) (bad))
 (fun (c0 : NamedCtorSource) (tail : ListType NamedCtorSource) (ih : forall (i : Nat) (base : IndCtorEnv) (j : Nat) (c : NamedCtorSource), @Eq (Bool) (nrb_names_unique_b (nsi_names (NamedCtorSource) (nsi_ctor_name) (tail))) (Bool.true) -> @Eq (OptionType NamedCtorSource) (nsi_at (NamedCtorSource) (tail) (j)) (@OptionType.some (NamedCtorSource) (c)) -> @Eq (OptionType KCtorMeta) (kctor_for (nsi_install_ctors (us) (p) (parent) (tail) (i) (base)) (nsi_ctor_name (c))) (@OptionType.some (KCtorMeta) (nsi_ctor_meta (us) (p) (parent) (Nat.add (i) (j)) (c)))) (i : Nat) (base : IndCtorEnv) (j : Nat) => @Nat.rec
  (fun (k : Nat) => forall (c : NamedCtorSource), @Eq (Bool) (nrb_names_unique_b (nsi_names (NamedCtorSource) (nsi_ctor_name) (@ListType.cons (NamedCtorSource) (c0) (tail)))) (Bool.true) -> @Eq (OptionType NamedCtorSource) (nsi_at (NamedCtorSource) (@ListType.cons (NamedCtorSource) (c0) (tail)) (k)) (@OptionType.some (NamedCtorSource) (c)) -> @Eq (OptionType KCtorMeta) (kctor_for (nsi_install_ctors (us) (p) (parent) (@ListType.cons (NamedCtorSource) (c0) (tail)) (i) (base)) (nsi_ctor_name (c))) (@OptionType.some (KCtorMeta) (nsi_ctor_meta (us) (p) (parent) (Nat.add (i) (k)) (c))))
  (fun (c : NamedCtorSource) (unique : @Eq (Bool) (nrb_names_unique_b (nsi_names (NamedCtorSource) (nsi_ctor_name) (@ListType.cons (NamedCtorSource) (c0) (tail)))) (Bool.true)) (found : @Eq (OptionType NamedCtorSource) (@OptionType.some (NamedCtorSource) (c0)) (@OptionType.some (NamedCtorSource) (c))) =>
   Eq.subst (NamedCtorSource) (fun (z : NamedCtorSource) => @Eq (OptionType KCtorMeta) (kctor_for (nsi_install_ctors (us) (p) (parent) (@ListType.cons (NamedCtorSource) (c0) (tail)) (i) (base)) (nsi_ctor_name (z))) (@OptionType.some (KCtorMeta) (nsi_ctor_meta (us) (p) (parent) (Nat.add (i) (Nat.zero)) (z)))) (c0) (c) (option_some_inj (NamedCtorSource) (c0) (c) (found)) (Eq.trans (OptionType KCtorMeta) (kctor_for (nsi_install_ctors (us) (p) (parent) (tail) (Nat.succ i) (IndCtorEnv.addCtor (base) (nsi_ctor_name (c0)) (nsi_ctor_meta (us) (p) (parent) (i) (c0)))) (nsi_ctor_name (c0))) (kctor_for (IndCtorEnv.addCtor (base) (nsi_ctor_name (c0)) (nsi_ctor_meta (us) (p) (parent) (i) (c0))) (nsi_ctor_name (c0))) (@OptionType.some (KCtorMeta) (nsi_ctor_meta (us) (p) (parent) (i) (c0))) (nsi_ctor_install_absent (us) (p) (parent) (tail) (Nat.succ i) (IndCtorEnv.addCtor (base) (nsi_ctor_name (c0)) (nsi_ctor_meta (us) (p) (parent) (i) (c0))) (nsi_ctor_name (c0)) (nsi_unique_cons_head (nsi_ctor_name (c0)) (nsi_names (NamedCtorSource) (nsi_ctor_name) (tail)) (unique))) (ict_ctor_add_ctor_same (base) (nsi_ctor_name (c0)) (nsi_ctor_meta (us) (p) (parent) (i) (c0)))))
  (fun (k : Nat) (_unused : forall (c : NamedCtorSource), @Eq (Bool) (nrb_names_unique_b (nsi_names (NamedCtorSource) (nsi_ctor_name) (@ListType.cons (NamedCtorSource) (c0) (tail)))) (Bool.true) -> @Eq (OptionType NamedCtorSource) (nsi_at (NamedCtorSource) (@ListType.cons (NamedCtorSource) (c0) (tail)) (k)) (@OptionType.some (NamedCtorSource) (c)) -> @Eq (OptionType KCtorMeta) (kctor_for (nsi_install_ctors (us) (p) (parent) (@ListType.cons (NamedCtorSource) (c0) (tail)) (i) (base)) (nsi_ctor_name (c))) (@OptionType.some (KCtorMeta) (nsi_ctor_meta (us) (p) (parent) (Nat.add (i) (k)) (c)))) (c : NamedCtorSource) (unique : @Eq (Bool) (nrb_names_unique_b (nsi_names (NamedCtorSource) (nsi_ctor_name) (@ListType.cons (NamedCtorSource) (c0) (tail)))) (Bool.true)) (found : @Eq (OptionType NamedCtorSource) (nsi_at (NamedCtorSource) (tail) (k)) (@OptionType.some (NamedCtorSource) (c))) => Eq.subst (Nat) (fun (idx : Nat) => @Eq (OptionType KCtorMeta) (kctor_for (nsi_install_ctors (us) (p) (parent) (tail) (Nat.succ i) (IndCtorEnv.addCtor (base) (nsi_ctor_name (c0)) (nsi_ctor_meta (us) (p) (parent) (i) (c0)))) (nsi_ctor_name (c))) (@OptionType.some (KCtorMeta) (nsi_ctor_meta (us) (p) (parent) (idx) (c)))) (Nat.add (Nat.succ i) (k)) (Nat.add (i) (Nat.succ k)) (nat_succ_add (i) (k)) (ih (Nat.succ i) (IndCtorEnv.addCtor (base) (nsi_ctor_name (c0)) (nsi_ctor_meta (us) (p) (parent) (i) (c0))) (k) (c) (nsi_unique_cons_tail (nsi_ctor_name (c0)) (nsi_names (NamedCtorSource) (nsi_ctor_name) (tail)) (unique)) (found))) j) cs",
    ),
    DeclarationInput::Proof(
        "nsi_ctor_install_selected_zero",
        r"forall (us : ListType Name) (p : Nat) (parent : Name) (cs : ListType NamedCtorSource) (base : IndCtorEnv) (j : Nat) (c : NamedCtorSource) (unique : @Eq (Bool) (nrb_names_unique_b (nsi_names (NamedCtorSource) (nsi_ctor_name) (cs))) (Bool.true)) (found : @Eq (OptionType NamedCtorSource) (nsi_at (NamedCtorSource) (cs) (j)) (@OptionType.some (NamedCtorSource) (c))), @Eq (OptionType KCtorMeta) (kctor_for (nsi_install_ctors (us) (p) (parent) (cs) (Nat.zero) (base)) (nsi_ctor_name (c))) (@OptionType.some (KCtorMeta) (nsi_ctor_meta (us) (p) (parent) (j) (c)))",
        r"fun (us : ListType Name) (p : Nat) (parent : Name) (cs : ListType NamedCtorSource) (base : IndCtorEnv) (j : Nat) (c : NamedCtorSource) (unique : @Eq (Bool) (nrb_names_unique_b (nsi_names (NamedCtorSource) (nsi_ctor_name) (cs))) (Bool.true)) (found : @Eq (OptionType NamedCtorSource) (nsi_at (NamedCtorSource) (cs) (j)) (@OptionType.some (NamedCtorSource) (c))) =>
 Eq.subst (Nat) (fun (idx : Nat) => @Eq (OptionType KCtorMeta) (kctor_for (nsi_install_ctors (us) (p) (parent) (cs) (Nat.zero) (base)) (nsi_ctor_name (c))) (@OptionType.some (KCtorMeta) (nsi_ctor_meta (us) (p) (parent) (idx) (c)))) (Nat.add (Nat.zero) (j)) (j) (nat_zero_add (j)) (nsi_ctor_install_selected (us) (p) (parent) (cs) (Nat.zero) (base) (j) (c) (unique) (found))",
    ),
    DeclarationInput::Proof(
        "nsi_mem_append_true_left",
        r"forall (xs : ListType Name), forall (ys : ListType Name) (q : Name), @Eq (Bool) (name_list_mem (xs) (q)) (Bool.true) -> @Eq (Bool) (name_list_mem (nsi_name_append (xs) (ys)) (q)) (Bool.true)",
        r"fun (xs : ListType Name) => @ListType.rec Name
 (fun (ns : ListType Name) => forall (ys : ListType Name) (q : Name), @Eq (Bool) (name_list_mem (ns) (q)) (Bool.true) -> @Eq (Bool) (name_list_mem (nsi_name_append (ns) (ys)) (q)) (Bool.true))
 (fun (ys : ListType Name) (q : Name) (bad : @Eq (Bool) (Bool.false) (Bool.true)) => bool_false_ne_true (@Eq (Bool) (name_list_mem (ys) (q)) (Bool.true)) (bad))
 (fun (n : Name) (ns : ListType Name) (ih : forall (ys : ListType Name) (q : Name), @Eq (Bool) (name_list_mem (ns) (q)) (Bool.true) -> @Eq (Bool) (name_list_mem (nsi_name_append (ns) (ys)) (q)) (Bool.true)) (ys : ListType Name) (q : Name) (member : @Eq (Bool) (name_list_mem (@ListType.cons (Name) (n) (ns)) (q)) (Bool.true)) =>
  nig_or_elim_prop (name_eqb (n) (q)) (name_list_mem (ns) (q)) (@Eq (Bool) (name_list_mem (nsi_name_append (@ListType.cons (Name) (n) (ns)) (ys)) (q)) (Bool.true)) (member) (fun (same : @Eq (Bool) (name_eqb (n) (q)) (Bool.true)) => Eq.cong (Bool) (Bool) (fun (b : Bool) => Bool.or b (name_list_mem (nsi_name_append (ns) (ys)) (q))) (name_eqb (n) (q)) (Bool.true) (same)) (fun (tail : @Eq (Bool) (name_list_mem (ns) (q)) (Bool.true)) => nsi_mem_cons_true_tail (n) (nsi_name_append (ns) (ys)) (q) (ih (ys) (q) (tail)))) xs",
    ),
    DeclarationInput::Proof(
        "nsi_source_unique_tail",
        r"forall (m : NamedMemberSource) (tail : ListType NamedMemberSource) (unique : @Eq (Bool) (nrb_names_unique_b (nsi_all_names (@ListType.cons (NamedMemberSource) (m) (tail)))) (Bool.true)), @Eq (Bool) (nrb_names_unique_b (nsi_all_names (tail))) (Bool.true)",
        r"fun (m : NamedMemberSource) (tail : ListType NamedMemberSource) (unique : @Eq (Bool) (nrb_names_unique_b (nsi_all_names (@ListType.cons (NamedMemberSource) (m) (tail)))) (Bool.true)) =>
 nsi_unique_append_remove_middle (nsi_names (NamedMemberSource) (nsi_member_name) (tail)) (nsi_names (NamedCtorSource) (nsi_ctor_name) (nsi_member_ctors (m))) (nsi_all_ctor_names (tail)) (nsi_unique_cons_tail (nsi_member_name (m)) (nsi_name_append (nsi_names (NamedMemberSource) (nsi_member_name) (tail)) (nsi_name_append (nsi_names (NamedCtorSource) (nsi_ctor_name) (nsi_member_ctors (m))) (nsi_all_ctor_names (tail)))) (unique))",
    ),
    DeclarationInput::Proof(
        "nsi_source_head_ctors_unique",
        r"forall (m : NamedMemberSource) (tail : ListType NamedMemberSource) (unique : @Eq (Bool) (nrb_names_unique_b (nsi_all_names (@ListType.cons (NamedMemberSource) (m) (tail)))) (Bool.true)), @Eq (Bool) (nrb_names_unique_b (nsi_names (NamedCtorSource) (nsi_ctor_name) (nsi_member_ctors (m)))) (Bool.true)",
        r"fun (m : NamedMemberSource) (tail : ListType NamedMemberSource) (unique : @Eq (Bool) (nrb_names_unique_b (nsi_all_names (@ListType.cons (NamedMemberSource) (m) (tail)))) (Bool.true)) =>
 nsi_unique_append_left (nsi_names (NamedCtorSource) (nsi_ctor_name) (nsi_member_ctors (m))) (nsi_all_ctor_names (tail)) (nsi_unique_append_right (nsi_names (NamedMemberSource) (nsi_member_name) (@ListType.cons (NamedMemberSource) (m) (tail))) (nsi_all_ctor_names (@ListType.cons (NamedMemberSource) (m) (tail))) (unique))",
    ),
    DeclarationInput::Proof(
        "nsi_member_install_absent",
        r"forall (us : ListType Name) (p : Nat) (block : ListType Name) (ms : ListType NamedMemberSource), forall (base : IndCtorEnv) (q : Name), @Eq (Bool) (name_list_mem (nsi_all_names (ms)) (q)) (Bool.false) -> @Eq (OptionType KCtorMeta) (kctor_for (nsi_install_members (us) (p) (block) (ms) (base)) (q)) (kctor_for (base) (q))",
        r"fun (us : ListType Name) (p : Nat) (block : ListType Name) (ms : ListType NamedMemberSource) => @ListType.rec NamedMemberSource
 (fun (xs : ListType NamedMemberSource) => forall (base : IndCtorEnv) (q : Name), @Eq (Bool) (name_list_mem (nsi_all_names (xs)) (q)) (Bool.false) -> @Eq (OptionType KCtorMeta) (kctor_for (nsi_install_members (us) (p) (block) (xs) (base)) (q)) (kctor_for (base) (q)))
 (fun (base : IndCtorEnv) (q : Name) (_no_name : @Eq (Bool) (Bool.false) (Bool.false)) => @Eq.refl (OptionType KCtorMeta) (kctor_for (base) (q)))
 (fun (m : NamedMemberSource) (tail : ListType NamedMemberSource) (ih : forall (base : IndCtorEnv) (q : Name), @Eq (Bool) (name_list_mem (nsi_all_names (tail)) (q)) (Bool.false) -> @Eq (OptionType KCtorMeta) (kctor_for (nsi_install_members (us) (p) (block) (tail) (base)) (q)) (kctor_for (base) (q))) (base : IndCtorEnv) (q : Name) (no_name : @Eq (Bool) (name_list_mem (nsi_all_names (@ListType.cons (NamedMemberSource) (m) (tail))) (q)) (Bool.false)) =>
  Eq.trans (OptionType KCtorMeta) (kctor_for (nsi_install_members (us) (p) (block) (tail) (IndCtorEnv.addInd (nsi_install_ctors (us) (p) (nsi_member_name (m)) (nsi_member_ctors (m)) (Nat.zero) (base)) (nsi_member_name (m)) (nsi_member_meta (us) (p) (block) (m)))) (q)) (kctor_for (IndCtorEnv.addInd (nsi_install_ctors (us) (p) (nsi_member_name (m)) (nsi_member_ctors (m)) (Nat.zero) (base)) (nsi_member_name (m)) (nsi_member_meta (us) (p) (block) (m))) (q)) (kctor_for (base) (q)) (ih (IndCtorEnv.addInd (nsi_install_ctors (us) (p) (nsi_member_name (m)) (nsi_member_ctors (m)) (Nat.zero) (base)) (nsi_member_name (m)) (nsi_member_meta (us) (p) (block) (m))) (q) (nsi_mem_append_false_intro (nsi_names (NamedMemberSource) (nsi_member_name) (tail)) (nsi_all_ctor_names (tail)) (q) (nsi_mem_cons_false_tail (nsi_member_name (m)) (nsi_names (NamedMemberSource) (nsi_member_name) (tail)) (q) (nsi_mem_append_false_left (nsi_names (NamedMemberSource) (nsi_member_name) (@ListType.cons (NamedMemberSource) (m) (tail))) (nsi_all_ctor_names (@ListType.cons (NamedMemberSource) (m) (tail))) (q) (no_name))) (nsi_mem_append_false_right (nsi_names (NamedCtorSource) (nsi_ctor_name) (nsi_member_ctors (m))) (nsi_all_ctor_names (tail)) (q) (nsi_mem_append_false_right (nsi_names (NamedMemberSource) (nsi_member_name) (@ListType.cons (NamedMemberSource) (m) (tail))) (nsi_all_ctor_names (@ListType.cons (NamedMemberSource) (m) (tail))) (q) (no_name))))) (Eq.trans (OptionType KCtorMeta) (kctor_for (IndCtorEnv.addInd (nsi_install_ctors (us) (p) (nsi_member_name (m)) (nsi_member_ctors (m)) (Nat.zero) (base)) (nsi_member_name (m)) (nsi_member_meta (us) (p) (block) (m))) (q)) (kctor_for (nsi_install_ctors (us) (p) (nsi_member_name (m)) (nsi_member_ctors (m)) (Nat.zero) (base)) (q)) (kctor_for (base) (q)) (ict_ctor_add_ind_other (nsi_install_ctors (us) (p) (nsi_member_name (m)) (nsi_member_ctors (m)) (Nat.zero) (base)) (nsi_member_name (m)) (q) (nsi_member_meta (us) (p) (block) (m)) (nsi_mem_cons_false_head (nsi_member_name (m)) (nsi_names (NamedMemberSource) (nsi_member_name) (tail)) (q) (nsi_mem_append_false_left (nsi_names (NamedMemberSource) (nsi_member_name) (@ListType.cons (NamedMemberSource) (m) (tail))) (nsi_all_ctor_names (@ListType.cons (NamedMemberSource) (m) (tail))) (q) (no_name)))) (nsi_ctor_install_absent (us) (p) (nsi_member_name (m)) (nsi_member_ctors (m)) (Nat.zero) (base) (q) (nsi_mem_append_false_left (nsi_names (NamedCtorSource) (nsi_ctor_name) (nsi_member_ctors (m))) (nsi_all_ctor_names (tail)) (q) (nsi_mem_append_false_right (nsi_names (NamedMemberSource) (nsi_member_name) (@ListType.cons (NamedMemberSource) (m) (tail))) (nsi_all_ctor_names (@ListType.cons (NamedMemberSource) (m) (tail))) (q) (no_name)))))) ms",
    ),
    DeclarationInput::Proof(
        "nsi_source_head_ctor_other",
        r"forall (m : NamedMemberSource) (tail : ListType NamedMemberSource) (q : Name) (unique : @Eq (Bool) (nrb_names_unique_b (nsi_all_names (@ListType.cons (NamedMemberSource) (m) (tail)))) (Bool.true)) (member : @Eq (Bool) (name_list_mem (nsi_names (NamedCtorSource) (nsi_ctor_name) (nsi_member_ctors (m))) (q)) (Bool.true)), @Eq (Bool) (name_eqb (nsi_member_name (m)) (q)) (Bool.false)",
        r"fun (m : NamedMemberSource) (tail : ListType NamedMemberSource) (q : Name) (unique : @Eq (Bool) (nrb_names_unique_b (nsi_all_names (@ListType.cons (NamedMemberSource) (m) (tail)))) (Bool.true)) (member : @Eq (Bool) (name_list_mem (nsi_names (NamedCtorSource) (nsi_ctor_name) (nsi_member_ctors (m))) (q)) (Bool.true)) =>
 nsi_mem_cons_false_head (nsi_member_name (m)) (nsi_names (NamedMemberSource) (nsi_member_name) (tail)) (q) (nsi_unique_append_cross_right (nsi_names (NamedMemberSource) (nsi_member_name) (@ListType.cons (NamedMemberSource) (m) (tail))) (nsi_all_ctor_names (@ListType.cons (NamedMemberSource) (m) (tail))) (q) (unique) (nsi_mem_append_true_left (nsi_names (NamedCtorSource) (nsi_ctor_name) (nsi_member_ctors (m))) (nsi_all_ctor_names (tail)) (q) (member)))",
    ),
    DeclarationInput::Proof(
        "nsi_source_head_ctor_tail_absent",
        r"forall (m : NamedMemberSource) (tail : ListType NamedMemberSource) (q : Name) (unique : @Eq (Bool) (nrb_names_unique_b (nsi_all_names (@ListType.cons (NamedMemberSource) (m) (tail)))) (Bool.true)) (member : @Eq (Bool) (name_list_mem (nsi_names (NamedCtorSource) (nsi_ctor_name) (nsi_member_ctors (m))) (q)) (Bool.true)), @Eq (Bool) (name_list_mem (nsi_all_names (tail)) (q)) (Bool.false)",
        r"fun (m : NamedMemberSource) (tail : ListType NamedMemberSource) (q : Name) (unique : @Eq (Bool) (nrb_names_unique_b (nsi_all_names (@ListType.cons (NamedMemberSource) (m) (tail)))) (Bool.true)) (member : @Eq (Bool) (name_list_mem (nsi_names (NamedCtorSource) (nsi_ctor_name) (nsi_member_ctors (m))) (q)) (Bool.true)) =>
 nsi_mem_append_false_intro (nsi_names (NamedMemberSource) (nsi_member_name) (tail)) (nsi_all_ctor_names (tail)) (q) (nsi_mem_cons_false_tail (nsi_member_name (m)) (nsi_names (NamedMemberSource) (nsi_member_name) (tail)) (q) (nsi_unique_append_cross_right (nsi_names (NamedMemberSource) (nsi_member_name) (@ListType.cons (NamedMemberSource) (m) (tail))) (nsi_all_ctor_names (@ListType.cons (NamedMemberSource) (m) (tail))) (q) (unique) (nsi_mem_append_true_left (nsi_names (NamedCtorSource) (nsi_ctor_name) (nsi_member_ctors (m))) (nsi_all_ctor_names (tail)) (q) (member)))) (nsi_unique_append_cross (nsi_names (NamedCtorSource) (nsi_ctor_name) (nsi_member_ctors (m))) (nsi_all_ctor_names (tail)) (q) (nsi_unique_append_right (nsi_names (NamedMemberSource) (nsi_member_name) (@ListType.cons (NamedMemberSource) (m) (tail))) (nsi_all_ctor_names (@ListType.cons (NamedMemberSource) (m) (tail))) (unique)) (member))",
    ),
    DeclarationInput::Proof(
        "nsi_member_head_ctor_selected",
        r"forall (us : ListType Name) (p : Nat) (block : ListType Name) (m : NamedMemberSource) (tail : ListType NamedMemberSource) (base : IndCtorEnv) (j : Nat) (c : NamedCtorSource) (unique : @Eq (Bool) (nrb_names_unique_b (nsi_all_names (@ListType.cons (NamedMemberSource) (m) (tail)))) (Bool.true)) (found : @Eq (OptionType NamedCtorSource) (nsi_at (NamedCtorSource) (nsi_member_ctors (m)) (j)) (@OptionType.some (NamedCtorSource) (c))), @Eq (OptionType KCtorMeta) (kctor_for (nsi_install_members (us) (p) (block) (@ListType.cons (NamedMemberSource) (m) (tail)) (base)) (nsi_ctor_name (c))) (@OptionType.some (KCtorMeta) (nsi_ctor_meta (us) (p) (nsi_member_name (m)) (j) (c)))",
        r"fun (us : ListType Name) (p : Nat) (block : ListType Name) (m : NamedMemberSource) (tail : ListType NamedMemberSource) (base : IndCtorEnv) (j : Nat) (c : NamedCtorSource) (unique : @Eq (Bool) (nrb_names_unique_b (nsi_all_names (@ListType.cons (NamedMemberSource) (m) (tail)))) (Bool.true)) (found : @Eq (OptionType NamedCtorSource) (nsi_at (NamedCtorSource) (nsi_member_ctors (m)) (j)) (@OptionType.some (NamedCtorSource) (c))) =>
 Eq.trans (OptionType KCtorMeta) (kctor_for (nsi_install_members (us) (p) (block) (@ListType.cons (NamedMemberSource) (m) (tail)) (base)) (nsi_ctor_name (c))) (kctor_for (IndCtorEnv.addInd (nsi_install_ctors (us) (p) (nsi_member_name (m)) (nsi_member_ctors (m)) (Nat.zero) (base)) (nsi_member_name (m)) (nsi_member_meta (us) (p) (block) (m))) (nsi_ctor_name (c))) (@OptionType.some (KCtorMeta) (nsi_ctor_meta (us) (p) (nsi_member_name (m)) (j) (c))) (nsi_member_install_absent (us) (p) (block) (tail) (IndCtorEnv.addInd (nsi_install_ctors (us) (p) (nsi_member_name (m)) (nsi_member_ctors (m)) (Nat.zero) (base)) (nsi_member_name (m)) (nsi_member_meta (us) (p) (block) (m))) (nsi_ctor_name (c)) (nsi_source_head_ctor_tail_absent (m) (tail) (nsi_ctor_name (c)) (unique) (nsi_at_mem (NamedCtorSource) (nsi_ctor_name) (nsi_member_ctors (m)) (j) (c) (found)))) (Eq.trans (OptionType KCtorMeta) (kctor_for (IndCtorEnv.addInd (nsi_install_ctors (us) (p) (nsi_member_name (m)) (nsi_member_ctors (m)) (Nat.zero) (base)) (nsi_member_name (m)) (nsi_member_meta (us) (p) (block) (m))) (nsi_ctor_name (c))) (kctor_for (nsi_install_ctors (us) (p) (nsi_member_name (m)) (nsi_member_ctors (m)) (Nat.zero) (base)) (nsi_ctor_name (c))) (@OptionType.some (KCtorMeta) (nsi_ctor_meta (us) (p) (nsi_member_name (m)) (j) (c))) (ict_ctor_add_ind_other (nsi_install_ctors (us) (p) (nsi_member_name (m)) (nsi_member_ctors (m)) (Nat.zero) (base)) (nsi_member_name (m)) (nsi_ctor_name (c)) (nsi_member_meta (us) (p) (block) (m)) (nsi_source_head_ctor_other (m) (tail) (nsi_ctor_name (c)) (unique) (nsi_at_mem (NamedCtorSource) (nsi_ctor_name) (nsi_member_ctors (m)) (j) (c) (found)))) (nsi_ctor_install_selected_zero (us) (p) (nsi_member_name (m)) (nsi_member_ctors (m)) (base) (j) (c) (nsi_source_head_ctors_unique (m) (tail) (unique)) (found)))",
    ),
    DeclarationInput::Proof(
        "nsi_member_install_ctor_selected",
        r"forall (us : ListType Name) (p : Nat) (block : ListType Name) (ms : ListType NamedMemberSource), forall (base : IndCtorEnv) (mi : Nat) (m : NamedMemberSource) (j : Nat) (c : NamedCtorSource), @Eq (Bool) (nrb_names_unique_b (nsi_all_names (ms))) (Bool.true) -> @Eq (OptionType NamedMemberSource) (nsi_at (NamedMemberSource) (ms) (mi)) (@OptionType.some (NamedMemberSource) (m)) -> @Eq (OptionType NamedCtorSource) (nsi_at (NamedCtorSource) (nsi_member_ctors (m)) (j)) (@OptionType.some (NamedCtorSource) (c)) -> @Eq (OptionType KCtorMeta) (kctor_for (nsi_install_members (us) (p) (block) (ms) (base)) (nsi_ctor_name (c))) (@OptionType.some (KCtorMeta) (nsi_ctor_meta (us) (p) (nsi_member_name (m)) (j) (c)))",
        r"fun (us : ListType Name) (p : Nat) (block : ListType Name) (ms : ListType NamedMemberSource) => @ListType.rec NamedMemberSource
 (fun (xs : ListType NamedMemberSource) => forall (base : IndCtorEnv) (mi : Nat) (m : NamedMemberSource) (j : Nat) (c : NamedCtorSource), @Eq (Bool) (nrb_names_unique_b (nsi_all_names (xs))) (Bool.true) -> @Eq (OptionType NamedMemberSource) (nsi_at (NamedMemberSource) (xs) (mi)) (@OptionType.some (NamedMemberSource) (m)) -> @Eq (OptionType NamedCtorSource) (nsi_at (NamedCtorSource) (nsi_member_ctors (m)) (j)) (@OptionType.some (NamedCtorSource) (c)) -> @Eq (OptionType KCtorMeta) (kctor_for (nsi_install_members (us) (p) (block) (xs) (base)) (nsi_ctor_name (c))) (@OptionType.some (KCtorMeta) (nsi_ctor_meta (us) (p) (nsi_member_name (m)) (j) (c))))
 (fun (base : IndCtorEnv) (mi : Nat) (m : NamedMemberSource) (j : Nat) (c : NamedCtorSource) (_unique : @Eq (Bool) (nrb_names_unique_b (nsi_all_names (@ListType.nil (NamedMemberSource)))) (Bool.true)) (bad : @Eq (OptionType NamedMemberSource) (nsi_at (NamedMemberSource) (@ListType.nil (NamedMemberSource)) (mi)) (@OptionType.some (NamedMemberSource) (m))) (_ctor_at : @Eq (OptionType NamedCtorSource) (nsi_at (NamedCtorSource) (nsi_member_ctors (m)) (j)) (@OptionType.some (NamedCtorSource) (c))) => option_none_ne_some (NamedMemberSource) (m) (@Eq (OptionType KCtorMeta) (kctor_for (nsi_install_members (us) (p) (block) (@ListType.nil (NamedMemberSource)) (base)) (nsi_ctor_name (c))) (@OptionType.some (KCtorMeta) (nsi_ctor_meta (us) (p) (nsi_member_name (m)) (j) (c)))) (bad))
 (fun (m0 : NamedMemberSource) (tail : ListType NamedMemberSource) (ih : forall (base : IndCtorEnv) (mi : Nat) (m : NamedMemberSource) (j : Nat) (c : NamedCtorSource), @Eq (Bool) (nrb_names_unique_b (nsi_all_names (tail))) (Bool.true) -> @Eq (OptionType NamedMemberSource) (nsi_at (NamedMemberSource) (tail) (mi)) (@OptionType.some (NamedMemberSource) (m)) -> @Eq (OptionType NamedCtorSource) (nsi_at (NamedCtorSource) (nsi_member_ctors (m)) (j)) (@OptionType.some (NamedCtorSource) (c)) -> @Eq (OptionType KCtorMeta) (kctor_for (nsi_install_members (us) (p) (block) (tail) (base)) (nsi_ctor_name (c))) (@OptionType.some (KCtorMeta) (nsi_ctor_meta (us) (p) (nsi_member_name (m)) (j) (c)))) (base : IndCtorEnv) (mi : Nat) => @Nat.rec
  (fun (k : Nat) => forall (m : NamedMemberSource) (j : Nat) (c : NamedCtorSource), @Eq (Bool) (nrb_names_unique_b (nsi_all_names (@ListType.cons (NamedMemberSource) (m0) (tail)))) (Bool.true) -> @Eq (OptionType NamedMemberSource) (nsi_at (NamedMemberSource) (@ListType.cons (NamedMemberSource) (m0) (tail)) (k)) (@OptionType.some (NamedMemberSource) (m)) -> @Eq (OptionType NamedCtorSource) (nsi_at (NamedCtorSource) (nsi_member_ctors (m)) (j)) (@OptionType.some (NamedCtorSource) (c)) -> @Eq (OptionType KCtorMeta) (kctor_for (nsi_install_members (us) (p) (block) (@ListType.cons (NamedMemberSource) (m0) (tail)) (base)) (nsi_ctor_name (c))) (@OptionType.some (KCtorMeta) (nsi_ctor_meta (us) (p) (nsi_member_name (m)) (j) (c))))
  (fun (m : NamedMemberSource) (j : Nat) (c : NamedCtorSource) (unique : @Eq (Bool) (nrb_names_unique_b (nsi_all_names (@ListType.cons (NamedMemberSource) (m0) (tail)))) (Bool.true)) (member_at : @Eq (OptionType NamedMemberSource) (@OptionType.some (NamedMemberSource) (m0)) (@OptionType.some (NamedMemberSource) (m))) =>
   Eq.subst (NamedMemberSource) (fun (z : NamedMemberSource) => @Eq (OptionType NamedCtorSource) (nsi_at (NamedCtorSource) (nsi_member_ctors (z)) (j)) (@OptionType.some (NamedCtorSource) (c)) -> @Eq (OptionType KCtorMeta) (kctor_for (nsi_install_members (us) (p) (block) (@ListType.cons (NamedMemberSource) (m0) (tail)) (base)) (nsi_ctor_name (c))) (@OptionType.some (KCtorMeta) (nsi_ctor_meta (us) (p) (nsi_member_name (z)) (j) (c)))) (m0) (m) (option_some_inj (NamedMemberSource) (m0) (m) (member_at)) (fun (ctor_at : @Eq (OptionType NamedCtorSource) (nsi_at (NamedCtorSource) (nsi_member_ctors (m0)) (j)) (@OptionType.some (NamedCtorSource) (c))) => nsi_member_head_ctor_selected (us) (p) (block) (m0) (tail) (base) (j) (c) (unique) (ctor_at)))
  (fun (k : Nat) (_unused : forall (m : NamedMemberSource) (j : Nat) (c : NamedCtorSource), @Eq (Bool) (nrb_names_unique_b (nsi_all_names (@ListType.cons (NamedMemberSource) (m0) (tail)))) (Bool.true) -> @Eq (OptionType NamedMemberSource) (nsi_at (NamedMemberSource) (@ListType.cons (NamedMemberSource) (m0) (tail)) (k)) (@OptionType.some (NamedMemberSource) (m)) -> @Eq (OptionType NamedCtorSource) (nsi_at (NamedCtorSource) (nsi_member_ctors (m)) (j)) (@OptionType.some (NamedCtorSource) (c)) -> @Eq (OptionType KCtorMeta) (kctor_for (nsi_install_members (us) (p) (block) (@ListType.cons (NamedMemberSource) (m0) (tail)) (base)) (nsi_ctor_name (c))) (@OptionType.some (KCtorMeta) (nsi_ctor_meta (us) (p) (nsi_member_name (m)) (j) (c)))) (m : NamedMemberSource) (j : Nat) (c : NamedCtorSource) (unique : @Eq (Bool) (nrb_names_unique_b (nsi_all_names (@ListType.cons (NamedMemberSource) (m0) (tail)))) (Bool.true)) (member_at : @Eq (OptionType NamedMemberSource) (nsi_at (NamedMemberSource) (tail) (k)) (@OptionType.some (NamedMemberSource) (m))) (ctor_at : @Eq (OptionType NamedCtorSource) (nsi_at (NamedCtorSource) (nsi_member_ctors (m)) (j)) (@OptionType.some (NamedCtorSource) (c))) =>
   ih (IndCtorEnv.addInd (nsi_install_ctors (us) (p) (nsi_member_name (m0)) (nsi_member_ctors (m0)) (Nat.zero) (base)) (nsi_member_name (m0)) (nsi_member_meta (us) (p) (block) (m0))) (k) (m) (j) (c) (nsi_source_unique_tail (m0) (tail) (unique)) (member_at) (ctor_at)) mi) ms",
    ),
    DeclarationInput::Proof(
        "nsi_raw_ctor_lookup_installed",
        r"forall (us : ListType Name) (p : Nat) (ms : ListType NamedMemberSource) (base : IndCtorEnv) (mi : Nat) (m : NamedMemberSource) (j : Nat) (c : NamedCtorSource) (unique : @Eq (Bool) (nrb_names_unique_b (nsi_all_names (ms))) (Bool.true)) (member_at : @Eq (OptionType NamedMemberSource) (nsi_at (NamedMemberSource) (ms) (mi)) (@OptionType.some (NamedMemberSource) (m))) (ctor_at : @Eq (OptionType NamedCtorSource) (nsi_at (NamedCtorSource) (nsi_member_ctors (m)) (j)) (@OptionType.some (NamedCtorSource) (c))), @Eq (OptionType KCtorMeta) (kctor_for (nsi_raw_install (us) (p) (ms) (base)) (nsi_ctor_name (c))) (@OptionType.some (KCtorMeta) (nsi_ctor_meta (us) (p) (nsi_member_name (m)) (j) (c)))",
        r"fun (us : ListType Name) (p : Nat) (ms : ListType NamedMemberSource) (base : IndCtorEnv) (mi : Nat) (m : NamedMemberSource) (j : Nat) (c : NamedCtorSource) (unique : @Eq (Bool) (nrb_names_unique_b (nsi_all_names (ms))) (Bool.true)) (member_at : @Eq (OptionType NamedMemberSource) (nsi_at (NamedMemberSource) (ms) (mi)) (@OptionType.some (NamedMemberSource) (m))) (ctor_at : @Eq (OptionType NamedCtorSource) (nsi_at (NamedCtorSource) (nsi_member_ctors (m)) (j)) (@OptionType.some (NamedCtorSource) (c))) =>
 nsi_member_install_ctor_selected (us) (p) (nsi_names (NamedMemberSource) (nsi_member_name) (ms)) (ms) (base) (mi) (m) (j) (c) (unique) (member_at) (ctor_at)",
    ),
    DeclarationInput::Data(
        "nsi_demo_cf",
        r"NamedCtorSource",
        r"NamedCtorSource.mk nrb_demo_cf nrb_demo_cf_type",
    ),
    DeclarationInput::Data(
        "nsi_demo_cg",
        r"NamedCtorSource",
        r"NamedCtorSource.mk nrb_demo_cg nrb_demo_cg_type",
    ),
    DeclarationInput::Data(
        "nsi_demo_cg2",
        r"NamedCtorSource",
        r"NamedCtorSource.mk (Name.str nrb_demo_g (Nat.succ Nat.zero)) nrb_demo_cg_type",
    ),
    DeclarationInput::Data(
        "nsi_demo_f",
        r"NamedMemberSource",
        r"NamedMemberSource.mk nrb_demo_f nrb_demo_f_type (@ListType.cons NamedCtorSource nsi_demo_cf (@ListType.nil NamedCtorSource))",
    ),
    DeclarationInput::Data(
        "nsi_demo_g",
        r"NamedMemberSource",
        r"NamedMemberSource.mk nrb_demo_g nrb_demo_g_type (@ListType.cons NamedCtorSource nsi_demo_cg (@ListType.cons NamedCtorSource nsi_demo_cg2 (@ListType.nil NamedCtorSource)))",
    ),
    DeclarationInput::Data(
        "nsi_demo_sources",
        r"ListType NamedMemberSource",
        r"@ListType.cons (NamedMemberSource) (nsi_demo_f) (@ListType.cons (NamedMemberSource) (nsi_demo_g) (@ListType.nil (NamedMemberSource)))",
    ),
    DeclarationInput::Data(
        "nsi_demo_installed",
        r"IndCtorEnv",
        r"nsi_raw_install (nrb_demo_levels) (Nat.succ Nat.zero) (nsi_demo_sources) (IndCtorEnv.empty)",
    ),
    DeclarationInput::Proof(
        "nsi_demo_unique",
        r"@Eq (Bool) (nrb_names_unique_b (nsi_all_names (nsi_demo_sources))) (Bool.true)",
        r"@Eq.refl (Bool) (Bool.true)",
    ),
    DeclarationInput::Proof(
        "nsi_demo_second_ctor",
        r"forall (base : IndCtorEnv), @Eq (OptionType KCtorMeta) (kctor_for (nsi_raw_install (nrb_demo_levels) (Nat.succ Nat.zero) (nsi_demo_sources) (base)) (nsi_ctor_name (nsi_demo_cg2))) (@OptionType.some (KCtorMeta) (nsi_ctor_meta (nrb_demo_levels) (Nat.succ Nat.zero) (nrb_demo_g) (Nat.succ Nat.zero) (nsi_demo_cg2)))",
        r"fun (base : IndCtorEnv) =>
 nsi_raw_ctor_lookup_installed (nrb_demo_levels) (Nat.succ Nat.zero) (nsi_demo_sources) (base) (Nat.succ Nat.zero) (nsi_demo_g) (Nat.succ Nat.zero) (nsi_demo_cg2) (nsi_demo_unique) (@Eq.refl (OptionType NamedMemberSource) (@OptionType.some (NamedMemberSource) (nsi_demo_g))) (@Eq.refl (OptionType NamedCtorSource) (@OptionType.some (NamedCtorSource) (nsi_demo_cg2)))",
    ),
    DeclarationInput::Proof(
        "nsi_demo_f_indices",
        r"@Eq (Nat) (kind_num_indices (nsi_member_meta (nrb_demo_levels) (Nat.succ Nat.zero) (nsi_names (NamedMemberSource) (nsi_member_name) (nsi_demo_sources)) (nsi_demo_f))) (Nat.zero)",
        r"@Eq.refl (Nat) (Nat.zero)",
    ),
    DeclarationInput::Proof(
        "nsi_demo_g_indices",
        r"@Eq (Nat) (kind_num_indices (nsi_member_meta (nrb_demo_levels) (Nat.succ Nat.zero) (nsi_names (NamedMemberSource) (nsi_member_name) (nsi_demo_sources)) (nsi_demo_g))) (Nat.succ Nat.zero)",
        r"@Eq.refl (Nat) (Nat.succ Nat.zero)",
    ),
    DeclarationInput::Proof(
        "nsi_demo_unrelated_old_lookup",
        r"forall (base : IndCtorEnv), @Eq (OptionType KCtorMeta) (kctor_for (nsi_raw_install (nrb_demo_levels) (Nat.succ Nat.zero) (nsi_demo_sources) (base)) (nrb_demo_u)) (kctor_for (base) (nrb_demo_u))",
        r"fun (base : IndCtorEnv) =>
 nsi_member_install_absent (nrb_demo_levels) (Nat.succ Nat.zero) (nsi_names (NamedMemberSource) (nsi_member_name) (nsi_demo_sources)) (nsi_demo_sources) (base) (nrb_demo_u) (@Eq.refl (Bool) (Bool.false))",
    ),
    DeclarationInput::Data(
        "nsi_demo_collision_sources",
        r"ListType NamedMemberSource",
        r"@ListType.cons (NamedMemberSource) (nsi_demo_f) (@ListType.cons (NamedMemberSource) (NamedMemberSource.mk (nrb_demo_cf) (nrb_demo_g_type) (@ListType.nil (NamedCtorSource))) (@ListType.nil (NamedMemberSource)))",
    ),
    DeclarationInput::Proof(
        "nsi_demo_cross_kind_collision",
        r"@Eq (Bool) (nrb_names_unique_b (nsi_all_names (nsi_demo_collision_sources))) (Bool.false)",
        r"@Eq.refl (Bool) (Bool.false)",
    ),
    DeclarationInput::Proof(
        "nsi_demo_later_family_shadows_ctor",
        r"@Eq (OptionType KCtorMeta) (kctor_for (nsi_raw_install (nrb_demo_levels) (Nat.succ Nat.zero) (nsi_demo_collision_sources) (IndCtorEnv.empty)) (nrb_demo_cf)) (@OptionType.none (KCtorMeta))",
        r"@Eq.refl (OptionType KCtorMeta) (@OptionType.none (KCtorMeta))",
    ),
];

#[cfg(test)]
pub(super) const PROOF_ROOTS: &[&str] = &[
    "nsi_mem_cons_false_head",
    "nsi_mem_cons_false_tail",
    "nsi_mem_cons_false_intro",
    "nsi_mem_cons_true_head",
    "nsi_mem_cons_true_tail",
    "nsi_unique_cons_head",
    "nsi_unique_cons_tail",
    "nsi_unique_cons_intro",
    "nsi_mem_append_false_left",
    "nsi_mem_append_false_right",
    "nsi_unique_append_left",
    "nsi_unique_append_right",
    "nsi_unique_append_cross",
    "nsi_unique_append_cross_right",
    "nsi_mem_append_false_intro",
    "nsi_unique_append_remove_middle",
    "nsi_at_mem",
    "nsi_at_name_at",
    "nsi_ctor_install_absent",
    "nsi_ctor_install_selected",
    "nsi_ctor_install_selected_zero",
    "nsi_mem_append_true_left",
    "nsi_source_unique_tail",
    "nsi_source_head_ctors_unique",
    "nsi_member_install_absent",
    "nsi_source_head_ctor_other",
    "nsi_source_head_ctor_tail_absent",
    "nsi_member_head_ctor_selected",
    "nsi_member_install_ctor_selected",
    "nsi_raw_ctor_lookup_installed",
    "nsi_demo_unique",
    "nsi_demo_second_ctor",
    "nsi_demo_f_indices",
    "nsi_demo_g_indices",
    "nsi_demo_unrelated_old_lookup",
    "nsi_demo_cross_kind_collision",
    "nsi_demo_later_family_shadows_ctor",
];

#[cfg(test)]
pub(super) const PROP_PROOF_ROOTS: &[&str] = &[
    "nsi_mem_cons_false_head",
    "nsi_mem_cons_false_tail",
    "nsi_mem_cons_false_intro",
    "nsi_mem_cons_true_head",
    "nsi_mem_cons_true_tail",
    "nsi_unique_cons_head",
    "nsi_unique_cons_tail",
    "nsi_unique_cons_intro",
    "nsi_mem_append_false_left",
    "nsi_mem_append_false_right",
    "nsi_unique_append_left",
    "nsi_unique_append_right",
    "nsi_unique_append_cross",
    "nsi_unique_append_cross_right",
    "nsi_mem_append_false_intro",
    "nsi_unique_append_remove_middle",
    "nsi_at_mem",
    "nsi_at_name_at",
    "nsi_ctor_install_absent",
    "nsi_ctor_install_selected",
    "nsi_ctor_install_selected_zero",
    "nsi_mem_append_true_left",
    "nsi_source_unique_tail",
    "nsi_source_head_ctors_unique",
    "nsi_member_install_absent",
    "nsi_source_head_ctor_other",
    "nsi_source_head_ctor_tail_absent",
    "nsi_member_head_ctor_selected",
    "nsi_member_install_ctor_selected",
    "nsi_raw_ctor_lookup_installed",
    "nsi_demo_unique",
    "nsi_demo_second_ctor",
    "nsi_demo_f_indices",
    "nsi_demo_g_indices",
    "nsi_demo_unrelated_old_lookup",
    "nsi_demo_cross_kind_collision",
    "nsi_demo_later_family_shadows_ctor",
];

#[cfg(test)]
pub(super) const TYPE_PROOF_ROOTS: &[&str] = &[];

#[cfg(test)]
pub(super) const DATA_NAMES: &[&str] = &[
    "nsi_name_append",
    "nsi_ctor_name",
    "nsi_ctor_type",
    "nsi_member_name",
    "nsi_member_type",
    "nsi_member_ctors",
    "nsi_names",
    "nsi_at",
    "nsi_all_ctor_names",
    "nsi_all_names",
    "nsi_ctor_meta",
    "nsi_member_meta",
    "nsi_install_ctors",
    "nsi_install_members",
    "nsi_raw_install",
    "nsi_demo_cf",
    "nsi_demo_cg",
    "nsi_demo_cg2",
    "nsi_demo_f",
    "nsi_demo_g",
    "nsi_demo_sources",
    "nsi_demo_installed",
    "nsi_demo_collision_sources",
];

#[cfg(test)]
pub(super) const INDUCTIVE_NAMES: &[&str] = &["NamedCtorSource", "NamedMemberSource"];

#[cfg(test)]
pub(super) const NEGATIVE_CONTROLS: &[(&str, &str, &str)] = &[
    (
        "nsi_false_selected_parent",
        r"@Eq (OptionType KCtorMeta) (kctor_for (nsi_demo_installed) (nsi_ctor_name (nsi_demo_cg2))) (@OptionType.some (KCtorMeta) (nsi_ctor_meta (nrb_demo_levels) (Nat.succ Nat.zero) (nrb_demo_f) (Nat.succ Nat.zero) (nsi_demo_cg2)))",
        r"nsi_demo_second_ctor (IndCtorEnv.empty)",
    ),
    (
        "nsi_false_selected_index",
        r"@Eq (OptionType KCtorMeta) (kctor_for (nsi_demo_installed) (nsi_ctor_name (nsi_demo_cg2))) (@OptionType.some (KCtorMeta) (nsi_ctor_meta (nrb_demo_levels) (Nat.succ Nat.zero) (nrb_demo_g) (Nat.zero) (nsi_demo_cg2)))",
        r"nsi_demo_second_ctor (IndCtorEnv.empty)",
    ),
    (
        "nsi_false_cross_kind_survives",
        r"@Eq (OptionType KCtorMeta) (kctor_for (nsi_raw_install (nrb_demo_levels) (Nat.succ Nat.zero) (nsi_demo_collision_sources) (IndCtorEnv.empty)) (nrb_demo_cf)) (@OptionType.some (KCtorMeta) (nsi_ctor_meta (nrb_demo_levels) (Nat.succ Nat.zero) (nrb_demo_f) (Nat.zero) (nsi_demo_cf)))",
        r"@Eq.refl (OptionType KCtorMeta) (@OptionType.some (KCtorMeta) (nsi_ctor_meta (nrb_demo_levels) (Nat.succ Nat.zero) (nrb_demo_f) (Nat.zero) (nsi_demo_cf)))",
    ),
    (
        "nsi_false_input_slot",
        r"@Eq (OptionType NamedCtorSource) (nsi_at (NamedCtorSource) (nsi_member_ctors (nsi_demo_g)) (Nat.zero)) (@OptionType.some (NamedCtorSource) (nsi_demo_cg2))",
        r"@Eq.refl (OptionType NamedCtorSource) (@OptionType.some (NamedCtorSource) (nsi_demo_cg2))",
    ),
];

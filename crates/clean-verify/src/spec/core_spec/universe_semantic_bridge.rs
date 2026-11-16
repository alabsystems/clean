// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Additive structural semantic-universe relation for the acceptance model.
//!
//! The four arithmetic/evaluation adapters are copied exactly from the checked
//! ec03fa833 scratch guide. The relations and proof terms are checked against
//! the exact 31fa57c00 export (Wgxf0r, SHA256
//! 941dcfb5f386a75f80afef5afc35dfc733e1fde210abea22bbf8ae3333478957).
//! This module does not change legacy DefEq, raw reduction, or syntactic sort
//! injectivity. KExprUniverseEq changes only semantic universes: constructor
//! shape, names, indices, and tagged literal payloads remain exact.
//!
//! This is a model-level relation, not semantic confluence, production smart
//! constructor correctness, an environment representation, or Rust refinement.
//! Registration and whole-corpus replay are separate integration obligations.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// Requires expr_model, evalL/levelEqSem, kexpr_beq_sound, the existing
    /// arithmetic transport lemmas, and universe_bridge_congr2. No fixed
    /// reduction environment or typing/confluence theorem is used.
    pub(super) fn add_universe_semantic_bridge(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            r"def nat_max_eq_natMax (a : Nat) : forall (b : Nat), @Eq Nat (nat_max a b) (natMax a b) := @Nat.rec (fun (a0 : Nat) => forall (b : Nat), @Eq Nat (nat_max a0 b) (natMax a0 b)) (fun (b : Nat) => nat_zero_add b) (fun (a0 : Nat) (ih : forall (b : Nat), @Eq Nat (nat_max a0 b) (natMax a0 b)) => fun (b : Nat) => @Nat.rec (fun (b0 : Nat) => @Eq Nat (nat_max (Nat.succ a0) b0) (natMax (Nat.succ a0) b0)) (Eq.cong Nat Nat (fun (z : Nat) => Nat.add (Nat.succ a0) z) (Nat.sub Nat.zero (Nat.succ a0)) Nat.zero (nat_sub_zero_left (Nat.succ a0))) (fun (b0 : Nat) (_ : @Eq Nat (nat_max (Nat.succ a0) b0) (natMax (Nat.succ a0) b0)) => Eq.trans Nat (nat_max (Nat.succ a0) (Nat.succ b0)) (Nat.add (Nat.succ a0) (Nat.sub b0 a0)) (Nat.succ (natMax a0 b0)) (Eq.cong Nat Nat (fun (z : Nat) => Nat.add (Nat.succ a0) z) (Nat.sub (Nat.succ b0) (Nat.succ a0)) (Nat.sub b0 a0) (nat_sub_succ_succ b0 a0)) (Eq.trans Nat (Nat.add (Nat.succ a0) (Nat.sub b0 a0)) (Nat.succ (Nat.add a0 (Nat.sub b0 a0))) (Nat.succ (natMax a0 b0)) (nat_succ_add a0 (Nat.sub b0 a0)) (Eq.cong Nat Nat (fun (x : Nat) => Nat.succ x) (nat_max a0 b0) (natMax a0 b0) (ih b0)))) b) a",
            "Exact ec03fa833 semantic adapter; model-level only.",
        )?;

        self.add_recursive_def(
            r"def imax_nat_eq_imaxNat (a : Nat) (b : Nat) : @Eq Nat (imax_nat a b) (imaxNat a b) := @Nat.rec (fun (b0 : Nat) => @Eq Nat (imax_nat a b0) (imaxNat a b0)) (@Eq.refl Nat Nat.zero) (fun (b0 : Nat) (_ : @Eq Nat (imax_nat a b0) (imaxNat a b0)) => nat_max_eq_natMax a (Nat.succ b0)) b",
            "Exact ec03fa833 semantic adapter; model-level only.",
        )?;

        self.add_recursive_def(
            r"def level_eval_eq_evalL (v : Name -> Nat) (l : Level) : @Eq Nat (level_eval v l) (evalL v l) := @Level.rec (fun (l0 : Level) => @Eq Nat (level_eval v l0) (evalL v l0)) (@Eq.refl Nat Nat.zero) (fun (a : Level) (ih : @Eq Nat (level_eval v a) (evalL v a)) => Eq.cong Nat Nat (fun (n : Nat) => Nat.succ n) (level_eval v a) (evalL v a) ih) (fun (a : Level) (b : Level) (iha : @Eq Nat (level_eval v a) (evalL v a)) (ihb : @Eq Nat (level_eval v b) (evalL v b)) => Eq.trans Nat (nat_max (level_eval v a) (level_eval v b)) (nat_max (evalL v a) (evalL v b)) (natMax (evalL v a) (evalL v b)) (universe_bridge_congr2 Nat Nat Nat nat_max (level_eval v a) (evalL v a) (level_eval v b) (evalL v b) iha ihb) (nat_max_eq_natMax (evalL v a) (evalL v b))) (fun (a : Level) (b : Level) (iha : @Eq Nat (level_eval v a) (evalL v a)) (ihb : @Eq Nat (level_eval v b) (evalL v b)) => Eq.trans Nat (imax_nat (level_eval v a) (level_eval v b)) (imax_nat (evalL v a) (evalL v b)) (imaxNat (evalL v a) (evalL v b)) (universe_bridge_congr2 Nat Nat Nat imax_nat (level_eval v a) (evalL v a) (level_eval v b) (evalL v b) iha ihb) (imax_nat_eq_imaxNat (evalL v a) (evalL v b))) (fun (n : Name) => @Eq.refl Nat (v n)) l",
            "Exact ec03fa833 semantic adapter; model-level only.",
        )?;

        self.add_recursive_def(
            r"def level_is_nonzero_evalL_sound (l : Level) (h : @Eq Bool (level_is_nonzero l) Bool.true) (v : Name -> Nat) : @Eq Bool (nat_is_zero (evalL v l)) Bool.false := Eq.trans Bool (nat_is_zero (evalL v l)) (nat_is_zero (level_eval v l)) Bool.false (Eq.cong Nat Bool nat_is_zero (evalL v l) (level_eval v l) (Eq.symm Nat (level_eval v l) (evalL v l) (level_eval_eq_evalL v l))) (level_is_nonzero_sound l h v)",
            "Exact ec03fa833 semantic adapter; model-level only.",
        )?;

        self.add_inductive(
            r"inductive LevelListEqSem : ListType Level -> ListType Level -> Type
| nil : LevelListEqSem (@ListType.nil Level) (@ListType.nil Level)
| cons : forall (u : Level) (v : Level) (us : ListType Level) (vs : ListType Level),
    levelEqSem u v -> LevelListEqSem us vs ->
    LevelListEqSem (@ListType.cons Level u us) (@ListType.cons Level v vs)",
            "LevelListEqSem: Type-valued structural relation; only universe levels may vary semantically.",
        )?;

        self.add_inductive(
            r"inductive KExprUniverseEq : KExpr -> KExpr -> Type
| sort : forall (u : Level) (v : Level), levelEqSem u v -> KExprUniverseEq (KExpr.sort u) (KExpr.sort v)
| bvar : forall (i : Nat), KExprUniverseEq (KExpr.bvar i) (KExpr.bvar i)
| app : forall (f : KExpr) (f2 : KExpr) (a : KExpr) (a2 : KExpr), KExprUniverseEq f f2 -> KExprUniverseEq a a2 -> KExprUniverseEq (KExpr.app f a) (KExpr.app f2 a2)
| lam : forall (A : KExpr) (A2 : KExpr) (b : KExpr) (b2 : KExpr), KExprUniverseEq A A2 -> KExprUniverseEq b b2 -> KExprUniverseEq (KExpr.lam A b) (KExpr.lam A2 b2)
| pi : forall (A : KExpr) (A2 : KExpr) (b : KExpr) (b2 : KExpr), KExprUniverseEq A A2 -> KExprUniverseEq b b2 -> KExprUniverseEq (KExpr.pi A b) (KExpr.pi A2 b2)
| const : forall (n : Name) (us : ListType Level) (vs : ListType Level), LevelListEqSem us vs -> KExprUniverseEq (KExpr.const n us) (KExpr.const n vs)
| let_ : forall (A : KExpr) (A2 : KExpr) (v : KExpr) (v2 : KExpr) (b : KExpr) (b2 : KExpr), KExprUniverseEq A A2 -> KExprUniverseEq v v2 -> KExprUniverseEq b b2 -> KExprUniverseEq (KExpr.let_ A v b) (KExpr.let_ A2 v2 b2)
| proj : forall (sn : Name) (i : Nat) (sub : KExpr) (sub2 : KExpr), KExprUniverseEq sub sub2 -> KExprUniverseEq (KExpr.proj sn i sub) (KExpr.proj sn i sub2)
| lit : forall (n : Nat), KExprUniverseEq (KExpr.lit n) (KExpr.lit n)",
            "KExprUniverseEq: Type-valued structural relation; only universe levels may vary semantically.",
        )?;

        self.add_recursive_def(
            r"def levelEqSem_refl (u : Level) : levelEqSem u u := fun (v : Name -> Nat) => @Eq.refl Nat (evalL v u)",
            "Every raw level is semantically equal to itself.",
        )?;

        self.add_recursive_def(
            r"def levelEqSem_symm (u : Level) (v : Level) (h : levelEqSem u v) : levelEqSem v u := fun (r : Name -> Nat) => Eq.symm Nat (evalL r u) (evalL r v) (h r)",
            "Semantic equality is symmetric.",
        )?;

        self.add_recursive_def(
            r"def levelEqSem_trans (u : Level) (v : Level) (w : Level) (h : levelEqSem u v) (k : levelEqSem v w) : levelEqSem u w := fun (r : Name -> Nat) => Eq.trans Nat (evalL r u) (evalL r v) (evalL r w) (h r) (k r)",
            "Semantic equality is transitive.",
        )?;

        self.add_recursive_def(
            r"def levelListEqSem_refl (us : ListType Level) : LevelListEqSem us us :=
 @ListType.rec Level (fun (xs : ListType Level) => LevelListEqSem xs xs)
 LevelListEqSem.nil
 (fun (u : Level) (xs : ListType Level) (ih : LevelListEqSem xs xs) =>
   LevelListEqSem.cons u u xs xs (levelEqSem_refl u) ih) us",
            "Pointwise semantic universe-list equality is reflexive.",
        )?;

        self.add_recursive_def(
            r"def levelListEqSem_symm (us : ListType Level) (vs : ListType Level) (h : LevelListEqSem us vs) : LevelListEqSem vs us :=
 @LevelListEqSem.rec
 (fun (xs : ListType Level) (ys : ListType Level) (_ : LevelListEqSem xs ys) => LevelListEqSem ys xs)
 LevelListEqSem.nil
 (fun (u : Level) (v : Level) (xs : ListType Level) (ys : ListType Level)
   (hu : levelEqSem u v) (_hs : LevelListEqSem xs ys) (ih : LevelListEqSem ys xs) =>
   LevelListEqSem.cons v u ys xs (levelEqSem_symm u v hu) ih) us vs h",
            "Pointwise semantic universe-list equality is symmetric.",
        )?;

        self.add_recursive_def(
            r"def levelListEqSem_view_type (us : ListType Level) (vs : ListType Level) (C : Type) : Type :=
 @ListType.rec Level (fun (_ : ListType Level) => Type)
   ((@Eq (ListType Level) vs (@ListType.nil Level) -> C) -> C)
   (fun (u : Level) (xs : ListType Level) (_ : Type) =>
     (forall (v : Level) (ys : ListType Level), levelEqSem u v -> LevelListEqSem xs ys ->
       @Eq (ListType Level) vs (@ListType.cons Level v ys) -> C) -> C) us",
            "Continuation view keeps the exact target list and all related elements; no axiom or result assumption.",
        )?;

        self.add_recursive_def(
            r"def levelListEqSem_view (us : ListType Level) (vs : ListType Level) (h : LevelListEqSem us vs)
 (C : Type) : levelListEqSem_view_type us vs C :=
 @LevelListEqSem.rec
 (fun (xs : ListType Level) (ys : ListType Level) (_ : LevelListEqSem xs ys) => levelListEqSem_view_type xs ys C)
 (fun (k : @Eq (ListType Level) (@ListType.nil Level) (@ListType.nil Level) -> C) =>
   k (@Eq.refl (ListType Level) (@ListType.nil Level)))
 (fun (u : Level) (v : Level) (xs : ListType Level) (ys : ListType Level)
   (hu : levelEqSem u v) (hs : LevelListEqSem xs ys) (_ih : levelListEqSem_view_type xs ys C) =>
   fun (k : forall (v2 : Level) (ys2 : ListType Level), levelEqSem u v2 -> LevelListEqSem xs ys2 ->
     @Eq (ListType Level) (@ListType.cons Level v ys) (@ListType.cons Level v2 ys2) -> C) =>
   k v ys hu hs (@Eq.refl (ListType Level) (@ListType.cons Level v ys))) us vs h",
            "Proved target-list view, by induction on the actual pointwise relation.",
        )?;

        self.add_recursive_def(
            r"def levelListEqSem_trans (us : ListType Level) (vs : ListType Level) (h : LevelListEqSem us vs) :
 forall (ws : ListType Level), LevelListEqSem vs ws -> LevelListEqSem us ws :=
 @LevelListEqSem.rec
 (fun (xs : ListType Level) (ys : ListType Level) (_ : LevelListEqSem xs ys) =>
   forall (zs : ListType Level), LevelListEqSem ys zs -> LevelListEqSem xs zs)
 (fun (zs : ListType Level) (h2 : LevelListEqSem (@ListType.nil Level) zs) => h2)
 (fun (u : Level) (v : Level) (xs : ListType Level) (ys : ListType Level)
   (hu : levelEqSem u v) (_hs : LevelListEqSem xs ys)
   (ih : forall (zs : ListType Level), LevelListEqSem ys zs -> LevelListEqSem xs zs)
   (zs : ListType Level) (h2 : LevelListEqSem (@ListType.cons Level v ys) zs) =>
   levelListEqSem_view (@ListType.cons Level v ys) zs h2 (LevelListEqSem (@ListType.cons Level u xs) zs)
   (fun (w : Level) (tail : ListType Level) (hw : levelEqSem v w) (ht : LevelListEqSem ys tail)
     (hz : @Eq (ListType Level) zs (@ListType.cons Level w tail)) =>
     Eq.substType (ListType Level) (fun (out : ListType Level) => LevelListEqSem (@ListType.cons Level u xs) out)
       (@ListType.cons Level w tail) zs
       (Eq.symm (ListType Level) zs (@ListType.cons Level w tail) hz)
       (LevelListEqSem.cons u w xs tail (levelEqSem_trans u v w hu hw) (ih tail ht)))) us vs h",
            "Pointwise semantic universe-list equality is transitive, with target shape derived from its constructor proof.",
        )?;

        self.add_recursive_def(
            r"def kexprUniverseEq_refl (e : KExpr) : KExprUniverseEq e e :=
 @KExpr.rec (fun (e0 : KExpr) => KExprUniverseEq e0 e0)
 (fun (u : Level) => KExprUniverseEq.sort u u (levelEqSem_refl u))
 (fun (i : Nat) => KExprUniverseEq.bvar i)
 (fun (f : KExpr) (a : KExpr) (ihf : KExprUniverseEq f f) (iha : KExprUniverseEq a a) => KExprUniverseEq.app f f a a ihf iha)
 (fun (A : KExpr) (b : KExpr) (ihA : KExprUniverseEq A A) (ihb : KExprUniverseEq b b) => KExprUniverseEq.lam A A b b ihA ihb)
 (fun (A : KExpr) (b : KExpr) (ihA : KExprUniverseEq A A) (ihb : KExprUniverseEq b b) => KExprUniverseEq.pi A A b b ihA ihb)
 (fun (n : Name) (us : ListType Level) => KExprUniverseEq.const n us us (levelListEqSem_refl us))
 (fun (A : KExpr) (v : KExpr) (b : KExpr) (ihA : KExprUniverseEq A A) (ihv : KExprUniverseEq v v) (ihb : KExprUniverseEq b b) => KExprUniverseEq.let_ A A v v b b ihA ihv ihb)
 (fun (sn : Name) (i : Nat) (sub : KExpr) (ihsub : KExprUniverseEq sub sub) => KExprUniverseEq.proj sn i sub sub ihsub)
 (fun (n : Nat) => KExprUniverseEq.lit n) e",
            "All nine KExpr constructors are reflexive, including every tagged literal and projection.",
        )?;

        self.add_recursive_def(
            r"def kexprUniverseEq_symm (e : KExpr) (e2 : KExpr) (h : KExprUniverseEq e e2) : KExprUniverseEq e2 e :=
 @KExprUniverseEq.rec
 (fun (a : KExpr) (b : KExpr) (_ : KExprUniverseEq a b) => KExprUniverseEq b a)
 (fun (u : Level) (v : Level) (h : levelEqSem u v) => KExprUniverseEq.sort v u (levelEqSem_symm u v h))
 (fun (i : Nat) => KExprUniverseEq.bvar i)
 (fun (f : KExpr) (f2 : KExpr) (a : KExpr) (a2 : KExpr) (hf : KExprUniverseEq f f2) (ha : KExprUniverseEq a a2) (ihf : KExprUniverseEq f2 f) (iha : KExprUniverseEq a2 a) => KExprUniverseEq.app f2 f a2 a ihf iha)
 (fun (A : KExpr) (A2 : KExpr) (b : KExpr) (b2 : KExpr) (hA : KExprUniverseEq A A2) (hb : KExprUniverseEq b b2) (ihA : KExprUniverseEq A2 A) (ihb : KExprUniverseEq b2 b) => KExprUniverseEq.lam A2 A b2 b ihA ihb)
 (fun (A : KExpr) (A2 : KExpr) (b : KExpr) (b2 : KExpr) (hA : KExprUniverseEq A A2) (hb : KExprUniverseEq b b2) (ihA : KExprUniverseEq A2 A) (ihb : KExprUniverseEq b2 b) => KExprUniverseEq.pi A2 A b2 b ihA ihb)
 (fun (n : Name) (us : ListType Level) (vs : ListType Level) (h : LevelListEqSem us vs) => KExprUniverseEq.const n vs us (levelListEqSem_symm us vs h))
 (fun (A : KExpr) (A2 : KExpr) (v : KExpr) (v2 : KExpr) (b : KExpr) (b2 : KExpr) (hA : KExprUniverseEq A A2) (hv : KExprUniverseEq v v2) (hb : KExprUniverseEq b b2) (ihA : KExprUniverseEq A2 A) (ihv : KExprUniverseEq v2 v) (ihb : KExprUniverseEq b2 b) => KExprUniverseEq.let_ A2 A v2 v b2 b ihA ihv ihb)
 (fun (sn : Name) (i : Nat) (sub : KExpr) (sub2 : KExpr) (hsub : KExprUniverseEq sub sub2) (ihsub : KExprUniverseEq sub2 sub) => KExprUniverseEq.proj sn i sub2 sub ihsub)
 (fun (n : Nat) => KExprUniverseEq.lit n) e e2 h",
            "Structural semantic universe equivalence is symmetric; syntax and literal payloads remain exact.",
        )?;

        self.add_recursive_def(
            r"def kexprUniverseEq_view_type (e : KExpr) (target : KExpr) (C : Type) : Type :=
 @KExpr.rec (fun (_ : KExpr) => Type)
 (fun (u : Level) => (forall (v : Level), levelEqSem u v -> @Eq KExpr target (KExpr.sort v) -> C) -> C)
 (fun (i : Nat) => (@Eq KExpr target (KExpr.bvar i) -> C) -> C)
 (fun (f : KExpr) (a : KExpr) (ihf : Type) (iha : Type) => (forall (f2 : KExpr) (a2 : KExpr), KExprUniverseEq f f2 -> KExprUniverseEq a a2 -> @Eq KExpr target (KExpr.app f2 a2) -> C) -> C)
 (fun (A : KExpr) (b : KExpr) (ihA : Type) (ihb : Type) => (forall (A2 : KExpr) (b2 : KExpr), KExprUniverseEq A A2 -> KExprUniverseEq b b2 -> @Eq KExpr target (KExpr.lam A2 b2) -> C) -> C)
 (fun (A : KExpr) (b : KExpr) (ihA : Type) (ihb : Type) => (forall (A2 : KExpr) (b2 : KExpr), KExprUniverseEq A A2 -> KExprUniverseEq b b2 -> @Eq KExpr target (KExpr.pi A2 b2) -> C) -> C)
 (fun (n : Name) (us : ListType Level) => (forall (vs : ListType Level), LevelListEqSem us vs -> @Eq KExpr target (KExpr.const n vs) -> C) -> C)
 (fun (A : KExpr) (v : KExpr) (b : KExpr) (ihA : Type) (ihv : Type) (ihb : Type) => (forall (A2 : KExpr) (v2 : KExpr) (b2 : KExpr), KExprUniverseEq A A2 -> KExprUniverseEq v v2 -> KExprUniverseEq b b2 -> @Eq KExpr target (KExpr.let_ A2 v2 b2) -> C) -> C)
 (fun (sn : Name) (i : Nat) (sub : KExpr) (ihsub : Type) => (forall (sub2 : KExpr), KExprUniverseEq sub sub2 -> @Eq KExpr target (KExpr.proj sn i sub2) -> C) -> C)
 (fun (n : Nat) => (@Eq KExpr target (KExpr.lit n) -> C) -> C) e",
            "A constructor-specific continuation view retains the exact target expression; it is not an assumed decomposition.",
        )?;

        self.add_recursive_def(
            r"def kexprUniverseEq_view (e : KExpr) (e2 : KExpr) (h : KExprUniverseEq e e2)
 (C : Type) : kexprUniverseEq_view_type e e2 C :=
 @KExprUniverseEq.rec
 (fun (a : KExpr) (b : KExpr) (_ : KExprUniverseEq a b) => kexprUniverseEq_view_type a b C)
 (fun (u : Level) (v : Level) (h : levelEqSem u v) => fun (k : forall (v3 : Level), levelEqSem u v3 -> @Eq KExpr (KExpr.sort v) (KExpr.sort v3) -> C) =>
   k v h (@Eq.refl KExpr (KExpr.sort v)))
 (fun (i : Nat) => fun (k : @Eq KExpr (KExpr.bvar i) (KExpr.bvar i) -> C) =>
   k (@Eq.refl KExpr (KExpr.bvar i)))
 (fun (f : KExpr) (f2 : KExpr) (a : KExpr) (a2 : KExpr) (hf : KExprUniverseEq f f2) (ha : KExprUniverseEq a a2) (ihf : kexprUniverseEq_view_type f f2 C) (iha : kexprUniverseEq_view_type a a2 C) => fun (k : forall (f23 : KExpr) (a23 : KExpr), KExprUniverseEq f f23 -> KExprUniverseEq a a23 -> @Eq KExpr (KExpr.app f2 a2) (KExpr.app f23 a23) -> C) =>
   k f2 a2 hf ha (@Eq.refl KExpr (KExpr.app f2 a2)))
 (fun (A : KExpr) (A2 : KExpr) (b : KExpr) (b2 : KExpr) (hA : KExprUniverseEq A A2) (hb : KExprUniverseEq b b2) (ihA : kexprUniverseEq_view_type A A2 C) (ihb : kexprUniverseEq_view_type b b2 C) => fun (k : forall (A23 : KExpr) (b23 : KExpr), KExprUniverseEq A A23 -> KExprUniverseEq b b23 -> @Eq KExpr (KExpr.lam A2 b2) (KExpr.lam A23 b23) -> C) =>
   k A2 b2 hA hb (@Eq.refl KExpr (KExpr.lam A2 b2)))
 (fun (A : KExpr) (A2 : KExpr) (b : KExpr) (b2 : KExpr) (hA : KExprUniverseEq A A2) (hb : KExprUniverseEq b b2) (ihA : kexprUniverseEq_view_type A A2 C) (ihb : kexprUniverseEq_view_type b b2 C) => fun (k : forall (A23 : KExpr) (b23 : KExpr), KExprUniverseEq A A23 -> KExprUniverseEq b b23 -> @Eq KExpr (KExpr.pi A2 b2) (KExpr.pi A23 b23) -> C) =>
   k A2 b2 hA hb (@Eq.refl KExpr (KExpr.pi A2 b2)))
 (fun (n : Name) (us : ListType Level) (vs : ListType Level) (h : LevelListEqSem us vs) => fun (k : forall (vs3 : ListType Level), LevelListEqSem us vs3 -> @Eq KExpr (KExpr.const n vs) (KExpr.const n vs3) -> C) =>
   k vs h (@Eq.refl KExpr (KExpr.const n vs)))
 (fun (A : KExpr) (A2 : KExpr) (v : KExpr) (v2 : KExpr) (b : KExpr) (b2 : KExpr) (hA : KExprUniverseEq A A2) (hv : KExprUniverseEq v v2) (hb : KExprUniverseEq b b2) (ihA : kexprUniverseEq_view_type A A2 C) (ihv : kexprUniverseEq_view_type v v2 C) (ihb : kexprUniverseEq_view_type b b2 C) => fun (k : forall (A23 : KExpr) (v23 : KExpr) (b23 : KExpr), KExprUniverseEq A A23 -> KExprUniverseEq v v23 -> KExprUniverseEq b b23 -> @Eq KExpr (KExpr.let_ A2 v2 b2) (KExpr.let_ A23 v23 b23) -> C) =>
   k A2 v2 b2 hA hv hb (@Eq.refl KExpr (KExpr.let_ A2 v2 b2)))
 (fun (sn : Name) (i : Nat) (sub : KExpr) (sub2 : KExpr) (hsub : KExprUniverseEq sub sub2) (ihsub : kexprUniverseEq_view_type sub sub2 C) => fun (k : forall (sub23 : KExpr), KExprUniverseEq sub sub23 -> @Eq KExpr (KExpr.proj sn i sub2) (KExpr.proj sn i sub23) -> C) =>
   k sub2 hsub (@Eq.refl KExpr (KExpr.proj sn i sub2)))
 (fun (n : Nat) => fun (k : @Eq KExpr (KExpr.lit n) (KExpr.lit n) -> C) =>
   k (@Eq.refl KExpr (KExpr.lit n))) e e2 h",
            "Proved inversion view by induction on the nine constructors; no equality of returned outputs is assumed.",
        )?;

        self.add_recursive_def(
            r"def kexprUniverseEq_trans (e : KExpr) (e2 : KExpr) (h : KExprUniverseEq e e2) :
 forall (e3 : KExpr), KExprUniverseEq e2 e3 -> KExprUniverseEq e e3 :=
 @KExprUniverseEq.rec
 (fun (a : KExpr) (b : KExpr) (_ : KExprUniverseEq a b) => forall (z : KExpr), KExprUniverseEq b z -> KExprUniverseEq a z)
 (fun (u : Level) (v : Level) (h : levelEqSem u v) => fun (z : KExpr) (h2 : KExprUniverseEq (KExpr.sort v) z) =>
   kexprUniverseEq_view (KExpr.sort v) z h2 (KExprUniverseEq (KExpr.sort u) z)
     (fun (v3 : Level) (h3 : levelEqSem v v3) (heq : @Eq KExpr z (KExpr.sort v3)) =>
       Eq.substType KExpr (fun (out : KExpr) => KExprUniverseEq (KExpr.sort u) out)
         (KExpr.sort v3) z (Eq.symm KExpr z (KExpr.sort v3) heq)
         (KExprUniverseEq.sort u v3 (levelEqSem_trans u v v3 h h3))))
 (fun (i : Nat) => fun (z : KExpr) (h2 : KExprUniverseEq (KExpr.bvar i) z) =>
   kexprUniverseEq_view (KExpr.bvar i) z h2 (KExprUniverseEq (KExpr.bvar i) z)
     (fun (heq : @Eq KExpr z (KExpr.bvar i)) =>
       Eq.substType KExpr (fun (out : KExpr) => KExprUniverseEq (KExpr.bvar i) out)
         (KExpr.bvar i) z (Eq.symm KExpr z (KExpr.bvar i) heq)
         (KExprUniverseEq.bvar i)))
 (fun (f : KExpr) (f2 : KExpr) (a : KExpr) (a2 : KExpr) (hf : KExprUniverseEq f f2) (ha : KExprUniverseEq a a2) (ihf : forall (z : KExpr), KExprUniverseEq f2 z -> KExprUniverseEq f z) (iha : forall (z : KExpr), KExprUniverseEq a2 z -> KExprUniverseEq a z) => fun (z : KExpr) (h2 : KExprUniverseEq (KExpr.app f2 a2) z) =>
   kexprUniverseEq_view (KExpr.app f2 a2) z h2 (KExprUniverseEq (KExpr.app f a) z)
     (fun (f23 : KExpr) (a23 : KExpr) (hf3 : KExprUniverseEq f2 f23) (ha3 : KExprUniverseEq a2 a23) (heq : @Eq KExpr z (KExpr.app f23 a23)) =>
       Eq.substType KExpr (fun (out : KExpr) => KExprUniverseEq (KExpr.app f a) out)
         (KExpr.app f23 a23) z (Eq.symm KExpr z (KExpr.app f23 a23) heq)
         (KExprUniverseEq.app f f23 a a23 (ihf f23 hf3) (iha a23 ha3))))
 (fun (A : KExpr) (A2 : KExpr) (b : KExpr) (b2 : KExpr) (hA : KExprUniverseEq A A2) (hb : KExprUniverseEq b b2) (ihA : forall (z : KExpr), KExprUniverseEq A2 z -> KExprUniverseEq A z) (ihb : forall (z : KExpr), KExprUniverseEq b2 z -> KExprUniverseEq b z) => fun (z : KExpr) (h2 : KExprUniverseEq (KExpr.lam A2 b2) z) =>
   kexprUniverseEq_view (KExpr.lam A2 b2) z h2 (KExprUniverseEq (KExpr.lam A b) z)
     (fun (A23 : KExpr) (b23 : KExpr) (hA3 : KExprUniverseEq A2 A23) (hb3 : KExprUniverseEq b2 b23) (heq : @Eq KExpr z (KExpr.lam A23 b23)) =>
       Eq.substType KExpr (fun (out : KExpr) => KExprUniverseEq (KExpr.lam A b) out)
         (KExpr.lam A23 b23) z (Eq.symm KExpr z (KExpr.lam A23 b23) heq)
         (KExprUniverseEq.lam A A23 b b23 (ihA A23 hA3) (ihb b23 hb3))))
 (fun (A : KExpr) (A2 : KExpr) (b : KExpr) (b2 : KExpr) (hA : KExprUniverseEq A A2) (hb : KExprUniverseEq b b2) (ihA : forall (z : KExpr), KExprUniverseEq A2 z -> KExprUniverseEq A z) (ihb : forall (z : KExpr), KExprUniverseEq b2 z -> KExprUniverseEq b z) => fun (z : KExpr) (h2 : KExprUniverseEq (KExpr.pi A2 b2) z) =>
   kexprUniverseEq_view (KExpr.pi A2 b2) z h2 (KExprUniverseEq (KExpr.pi A b) z)
     (fun (A23 : KExpr) (b23 : KExpr) (hA3 : KExprUniverseEq A2 A23) (hb3 : KExprUniverseEq b2 b23) (heq : @Eq KExpr z (KExpr.pi A23 b23)) =>
       Eq.substType KExpr (fun (out : KExpr) => KExprUniverseEq (KExpr.pi A b) out)
         (KExpr.pi A23 b23) z (Eq.symm KExpr z (KExpr.pi A23 b23) heq)
         (KExprUniverseEq.pi A A23 b b23 (ihA A23 hA3) (ihb b23 hb3))))
 (fun (n : Name) (us : ListType Level) (vs : ListType Level) (h : LevelListEqSem us vs) => fun (z : KExpr) (h2 : KExprUniverseEq (KExpr.const n vs) z) =>
   kexprUniverseEq_view (KExpr.const n vs) z h2 (KExprUniverseEq (KExpr.const n us) z)
     (fun (vs3 : ListType Level) (h3 : LevelListEqSem vs vs3) (heq : @Eq KExpr z (KExpr.const n vs3)) =>
       Eq.substType KExpr (fun (out : KExpr) => KExprUniverseEq (KExpr.const n us) out)
         (KExpr.const n vs3) z (Eq.symm KExpr z (KExpr.const n vs3) heq)
         (KExprUniverseEq.const n us vs3 (levelListEqSem_trans us vs h vs3 h3))))
 (fun (A : KExpr) (A2 : KExpr) (v : KExpr) (v2 : KExpr) (b : KExpr) (b2 : KExpr) (hA : KExprUniverseEq A A2) (hv : KExprUniverseEq v v2) (hb : KExprUniverseEq b b2) (ihA : forall (z : KExpr), KExprUniverseEq A2 z -> KExprUniverseEq A z) (ihv : forall (z : KExpr), KExprUniverseEq v2 z -> KExprUniverseEq v z) (ihb : forall (z : KExpr), KExprUniverseEq b2 z -> KExprUniverseEq b z) => fun (z : KExpr) (h2 : KExprUniverseEq (KExpr.let_ A2 v2 b2) z) =>
   kexprUniverseEq_view (KExpr.let_ A2 v2 b2) z h2 (KExprUniverseEq (KExpr.let_ A v b) z)
     (fun (A23 : KExpr) (v23 : KExpr) (b23 : KExpr) (hA3 : KExprUniverseEq A2 A23) (hv3 : KExprUniverseEq v2 v23) (hb3 : KExprUniverseEq b2 b23) (heq : @Eq KExpr z (KExpr.let_ A23 v23 b23)) =>
       Eq.substType KExpr (fun (out : KExpr) => KExprUniverseEq (KExpr.let_ A v b) out)
         (KExpr.let_ A23 v23 b23) z (Eq.symm KExpr z (KExpr.let_ A23 v23 b23) heq)
         (KExprUniverseEq.let_ A A23 v v23 b b23 (ihA A23 hA3) (ihv v23 hv3) (ihb b23 hb3))))
 (fun (sn : Name) (i : Nat) (sub : KExpr) (sub2 : KExpr) (hsub : KExprUniverseEq sub sub2) (ihsub : forall (z : KExpr), KExprUniverseEq sub2 z -> KExprUniverseEq sub z) => fun (z : KExpr) (h2 : KExprUniverseEq (KExpr.proj sn i sub2) z) =>
   kexprUniverseEq_view (KExpr.proj sn i sub2) z h2 (KExprUniverseEq (KExpr.proj sn i sub) z)
     (fun (sub23 : KExpr) (hsub3 : KExprUniverseEq sub2 sub23) (heq : @Eq KExpr z (KExpr.proj sn i sub23)) =>
       Eq.substType KExpr (fun (out : KExpr) => KExprUniverseEq (KExpr.proj sn i sub) out)
         (KExpr.proj sn i sub23) z (Eq.symm KExpr z (KExpr.proj sn i sub23) heq)
         (KExprUniverseEq.proj sn i sub sub23 (ihsub sub23 hsub3))))
 (fun (n : Nat) => fun (z : KExpr) (h2 : KExprUniverseEq (KExpr.lit n) z) =>
   kexprUniverseEq_view (KExpr.lit n) z h2 (KExprUniverseEq (KExpr.lit n) z)
     (fun (heq : @Eq KExpr z (KExpr.lit n)) =>
       Eq.substType KExpr (fun (out : KExpr) => KExprUniverseEq (KExpr.lit n) out)
         (KExpr.lit n) z (Eq.symm KExpr z (KExpr.lit n) heq)
         (KExprUniverseEq.lit n))) e e2 h",
            "Structural semantic universe equivalence is transitive. Exact constructor shape is derived through the proved view.",
        )?;

        self.add_recursive_def(
            r"def kexprUniverseEq_lift_at (e : KExpr) (e2 : KExpr) (h : KExprUniverseEq e e2) :
 forall (cutoff : Nat) (amount : Nat), KExprUniverseEq (lift_at e cutoff amount) (lift_at e2 cutoff amount) :=
 @KExprUniverseEq.rec
 (fun (a : KExpr) (b : KExpr) (_ : KExprUniverseEq a b) =>
   forall (cutoff : Nat) (amount : Nat), KExprUniverseEq (lift_at a cutoff amount) (lift_at b cutoff amount))
 (fun (u : Level) (v : Level) (h : levelEqSem u v) => fun (cutoff : Nat) (amount : Nat) => KExprUniverseEq.sort u v h)
 (fun (i : Nat) => fun (cutoff : Nat) (amount : Nat) => kexprUniverseEq_refl (lift_bvar_at i cutoff amount))
 (fun (f : KExpr) (f2 : KExpr) (a : KExpr) (a2 : KExpr) (hf : KExprUniverseEq f f2) (ha : KExprUniverseEq a a2) (ihf : forall (cutoff : Nat) (amount : Nat), KExprUniverseEq (lift_at f cutoff amount) (lift_at f2 cutoff amount)) (iha : forall (cutoff : Nat) (amount : Nat), KExprUniverseEq (lift_at a cutoff amount) (lift_at a2 cutoff amount)) => fun (cutoff : Nat) (amount : Nat) => KExprUniverseEq.app (lift_at f cutoff amount) (lift_at f2 cutoff amount) (lift_at a cutoff amount) (lift_at a2 cutoff amount) (ihf cutoff amount) (iha cutoff amount))
 (fun (A : KExpr) (A2 : KExpr) (b : KExpr) (b2 : KExpr) (hA : KExprUniverseEq A A2) (hb : KExprUniverseEq b b2) (ihA : forall (cutoff : Nat) (amount : Nat), KExprUniverseEq (lift_at A cutoff amount) (lift_at A2 cutoff amount)) (ihb : forall (cutoff : Nat) (amount : Nat), KExprUniverseEq (lift_at b cutoff amount) (lift_at b2 cutoff amount)) => fun (cutoff : Nat) (amount : Nat) => KExprUniverseEq.lam (lift_at A cutoff amount) (lift_at A2 cutoff amount) (lift_at b (Nat.succ cutoff) amount) (lift_at b2 (Nat.succ cutoff) amount) (ihA cutoff amount) (ihb (Nat.succ cutoff) amount))
 (fun (A : KExpr) (A2 : KExpr) (b : KExpr) (b2 : KExpr) (hA : KExprUniverseEq A A2) (hb : KExprUniverseEq b b2) (ihA : forall (cutoff : Nat) (amount : Nat), KExprUniverseEq (lift_at A cutoff amount) (lift_at A2 cutoff amount)) (ihb : forall (cutoff : Nat) (amount : Nat), KExprUniverseEq (lift_at b cutoff amount) (lift_at b2 cutoff amount)) => fun (cutoff : Nat) (amount : Nat) => KExprUniverseEq.pi (lift_at A cutoff amount) (lift_at A2 cutoff amount) (lift_at b (Nat.succ cutoff) amount) (lift_at b2 (Nat.succ cutoff) amount) (ihA cutoff amount) (ihb (Nat.succ cutoff) amount))
 (fun (n : Name) (us : ListType Level) (vs : ListType Level) (h : LevelListEqSem us vs) => fun (cutoff : Nat) (amount : Nat) => KExprUniverseEq.const n us vs h)
 (fun (A : KExpr) (A2 : KExpr) (v : KExpr) (v2 : KExpr) (b : KExpr) (b2 : KExpr) (hA : KExprUniverseEq A A2) (hv : KExprUniverseEq v v2) (hb : KExprUniverseEq b b2) (ihA : forall (cutoff : Nat) (amount : Nat), KExprUniverseEq (lift_at A cutoff amount) (lift_at A2 cutoff amount)) (ihv : forall (cutoff : Nat) (amount : Nat), KExprUniverseEq (lift_at v cutoff amount) (lift_at v2 cutoff amount)) (ihb : forall (cutoff : Nat) (amount : Nat), KExprUniverseEq (lift_at b cutoff amount) (lift_at b2 cutoff amount)) => fun (cutoff : Nat) (amount : Nat) => KExprUniverseEq.let_ (lift_at A cutoff amount) (lift_at A2 cutoff amount) (lift_at v cutoff amount) (lift_at v2 cutoff amount) (lift_at b (Nat.succ cutoff) amount) (lift_at b2 (Nat.succ cutoff) amount) (ihA cutoff amount) (ihv cutoff amount) (ihb (Nat.succ cutoff) amount))
 (fun (sn : Name) (i : Nat) (sub : KExpr) (sub2 : KExpr) (hsub : KExprUniverseEq sub sub2) (ihsub : forall (cutoff : Nat) (amount : Nat), KExprUniverseEq (lift_at sub cutoff amount) (lift_at sub2 cutoff amount)) => fun (cutoff : Nat) (amount : Nat) => KExprUniverseEq.proj sn i (lift_at sub cutoff amount) (lift_at sub2 cutoff amount) (ihsub cutoff amount))
 (fun (n : Nat) => fun (cutoff : Nat) (amount : Nat) => KExprUniverseEq.lit n) e e2 h",
            "Semantic universe equivalence commutes with the actual raw de Bruijn lift, including binder cutoffs.",
        )?;

        self.add_recursive_def(
            r"def kexprUniverseEq_instantiate_bvar_geq (idx : Nat) (depth : Nat) (v : KExpr) (v2 : KExpr)
 (hv : KExprUniverseEq v v2) :
 KExprUniverseEq (instantiate_bvar_geq idx depth v) (instantiate_bvar_geq idx depth v2) :=
 @Nat.rec (fun (j : Nat) => KExprUniverseEq
   (@Nat.rec (fun (_ : Nat) => KExpr) (lift_at v Nat.zero depth)
     (fun (_ : Nat) (_ : KExpr) => KExpr.bvar (Nat.sub idx (Nat.succ Nat.zero))) j)
   (@Nat.rec (fun (_ : Nat) => KExpr) (lift_at v2 Nat.zero depth)
     (fun (_ : Nat) (_ : KExpr) => KExpr.bvar (Nat.sub idx (Nat.succ Nat.zero))) j))
   (kexprUniverseEq_lift_at v v2 hv Nat.zero depth)
   (fun (j : Nat) (_ih : KExprUniverseEq
     (@Nat.rec (fun (_ : Nat) => KExpr) (lift_at v Nat.zero depth)
       (fun (_ : Nat) (_ : KExpr) => KExpr.bvar (Nat.sub idx (Nat.succ Nat.zero))) j)
     (@Nat.rec (fun (_ : Nat) => KExpr) (lift_at v2 Nat.zero depth)
       (fun (_ : Nat) (_ : KExpr) => KExpr.bvar (Nat.sub idx (Nat.succ Nat.zero))) j)) =>
     KExprUniverseEq.bvar (Nat.sub idx (Nat.succ Nat.zero))) (Nat.sub idx depth)",
            "The equal-or-greater de Bruijn substitution helper preserves related replacement values.",
        )?;

        self.add_recursive_def(
            r"def kexprUniverseEq_instantiate_bvar_at (idx : Nat) (depth : Nat) (v : KExpr) (v2 : KExpr)
 (hv : KExprUniverseEq v v2) :
 KExprUniverseEq (instantiate_bvar_at idx depth v) (instantiate_bvar_at idx depth v2) :=
 @Nat.rec (fun (j : Nat) => KExprUniverseEq
   (@Nat.rec (fun (_ : Nat) => KExpr) (instantiate_bvar_geq idx depth v)
     (fun (_ : Nat) (_ : KExpr) => KExpr.bvar idx) j)
   (@Nat.rec (fun (_ : Nat) => KExpr) (instantiate_bvar_geq idx depth v2)
     (fun (_ : Nat) (_ : KExpr) => KExpr.bvar idx) j))
   (kexprUniverseEq_instantiate_bvar_geq idx depth v v2 hv)
   (fun (j : Nat) (_ih : KExprUniverseEq
     (@Nat.rec (fun (_ : Nat) => KExpr) (instantiate_bvar_geq idx depth v)
       (fun (_ : Nat) (_ : KExpr) => KExpr.bvar idx) j)
     (@Nat.rec (fun (_ : Nat) => KExpr) (instantiate_bvar_geq idx depth v2)
       (fun (_ : Nat) (_ : KExpr) => KExpr.bvar idx) j)) =>
     KExprUniverseEq.bvar idx) (Nat.sub depth idx)",
            "All three de Bruijn substitution cases preserve related replacement values.",
        )?;

        self.add_recursive_def(
            r"def kexprUniverseEq_instantiate_at (e : KExpr) (e2 : KExpr) (h : KExprUniverseEq e e2)
 (value : KExpr) (value2 : KExpr) (hvalue : KExprUniverseEq value value2) :
 forall (depth : Nat), KExprUniverseEq (instantiate_at e value depth) (instantiate_at e2 value2 depth) :=
 @KExprUniverseEq.rec
 (fun (a : KExpr) (b : KExpr) (_ : KExprUniverseEq a b) =>
   forall (depth : Nat), KExprUniverseEq (instantiate_at a value depth) (instantiate_at b value2 depth))
 (fun (u : Level) (v : Level) (h : levelEqSem u v) => fun (depth : Nat) => KExprUniverseEq.sort u v h)
 (fun (i : Nat) => fun (depth : Nat) => kexprUniverseEq_instantiate_bvar_at i depth value value2 hvalue)
 (fun (f : KExpr) (f2 : KExpr) (a : KExpr) (a2 : KExpr) (hf : KExprUniverseEq f f2) (ha : KExprUniverseEq a a2) (ihf : forall (depth : Nat), KExprUniverseEq (instantiate_at f value depth) (instantiate_at f2 value2 depth)) (iha : forall (depth : Nat), KExprUniverseEq (instantiate_at a value depth) (instantiate_at a2 value2 depth)) => fun (depth : Nat) => KExprUniverseEq.app (instantiate_at f value depth) (instantiate_at f2 value2 depth) (instantiate_at a value depth) (instantiate_at a2 value2 depth) (ihf depth) (iha depth))
 (fun (A : KExpr) (A2 : KExpr) (b : KExpr) (b2 : KExpr) (hA : KExprUniverseEq A A2) (hb : KExprUniverseEq b b2) (ihA : forall (depth : Nat), KExprUniverseEq (instantiate_at A value depth) (instantiate_at A2 value2 depth)) (ihb : forall (depth : Nat), KExprUniverseEq (instantiate_at b value depth) (instantiate_at b2 value2 depth)) => fun (depth : Nat) => KExprUniverseEq.lam (instantiate_at A value depth) (instantiate_at A2 value2 depth) (instantiate_at b value (Nat.succ depth)) (instantiate_at b2 value2 (Nat.succ depth)) (ihA depth) (ihb (Nat.succ depth)))
 (fun (A : KExpr) (A2 : KExpr) (b : KExpr) (b2 : KExpr) (hA : KExprUniverseEq A A2) (hb : KExprUniverseEq b b2) (ihA : forall (depth : Nat), KExprUniverseEq (instantiate_at A value depth) (instantiate_at A2 value2 depth)) (ihb : forall (depth : Nat), KExprUniverseEq (instantiate_at b value depth) (instantiate_at b2 value2 depth)) => fun (depth : Nat) => KExprUniverseEq.pi (instantiate_at A value depth) (instantiate_at A2 value2 depth) (instantiate_at b value (Nat.succ depth)) (instantiate_at b2 value2 (Nat.succ depth)) (ihA depth) (ihb (Nat.succ depth)))
 (fun (n : Name) (us : ListType Level) (vs : ListType Level) (h : LevelListEqSem us vs) => fun (depth : Nat) => KExprUniverseEq.const n us vs h)
 (fun (A : KExpr) (A2 : KExpr) (v : KExpr) (v2 : KExpr) (b : KExpr) (b2 : KExpr) (hA : KExprUniverseEq A A2) (hv : KExprUniverseEq v v2) (hb : KExprUniverseEq b b2) (ihA : forall (depth : Nat), KExprUniverseEq (instantiate_at A value depth) (instantiate_at A2 value2 depth)) (ihv : forall (depth : Nat), KExprUniverseEq (instantiate_at v value depth) (instantiate_at v2 value2 depth)) (ihb : forall (depth : Nat), KExprUniverseEq (instantiate_at b value depth) (instantiate_at b2 value2 depth)) => fun (depth : Nat) => KExprUniverseEq.let_ (instantiate_at A value depth) (instantiate_at A2 value2 depth) (instantiate_at v value depth) (instantiate_at v2 value2 depth) (instantiate_at b value (Nat.succ depth)) (instantiate_at b2 value2 (Nat.succ depth)) (ihA depth) (ihv depth) (ihb (Nat.succ depth)))
 (fun (sn : Name) (i : Nat) (sub : KExpr) (sub2 : KExpr) (hsub : KExprUniverseEq sub sub2) (ihsub : forall (depth : Nat), KExprUniverseEq (instantiate_at sub value depth) (instantiate_at sub2 value2 depth)) => fun (depth : Nat) => KExprUniverseEq.proj sn i (instantiate_at sub value depth) (instantiate_at sub2 value2 depth) (ihsub depth))
 (fun (n : Nat) => fun (depth : Nat) => KExprUniverseEq.lit n) e e2 h",
            "Simultaneously replacing related bodies and values preserves semantic universe equivalence, at every binder depth.",
        )?;

        self.add_recursive_def(
            r"def kexprUniverseEq_instantiate (e : KExpr) (e2 : KExpr) (h : KExprUniverseEq e e2)
 (value : KExpr) (value2 : KExpr) (hvalue : KExprUniverseEq value value2) :
 KExprUniverseEq (instantiate e value) (instantiate e2 value2) :=
 kexprUniverseEq_instantiate_at e e2 h value value2 hvalue Nat.zero",
            "Top-level term instantiation is compatible in both the body and substituted value.",
        )?;

        self.add_recursive_def(
            r"def kexprUniverseEq_imax_zero (u : Level) :
 KExprUniverseEq (KExpr.sort (Level.imax u Level.zero)) (KExpr.sort Level.zero) :=
 KExprUniverseEq.sort (Level.imax u Level.zero) Level.zero
   (fun (v : Name -> Nat) => @Eq.refl Nat Nat.zero)",
            "Nontrivial semantic equality: raw imax(u,0) and zero are different syntax but agree under every valuation.",
        )?;

        self.add_recursive_def(
            r"def kexprUniverseEq_binder_instantiation_witness :
 KExprUniverseEq
   (KExpr.lam (KExpr.sort Level.zero) (KExpr.sort (Level.imax (Level.succ Level.zero) Level.zero)))
   (KExpr.lam (KExpr.sort Level.zero) (KExpr.sort Level.zero)) :=
 kexprUniverseEq_instantiate
   (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar (Nat.succ Nat.zero)))
   (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar (Nat.succ Nat.zero)))
   (kexprUniverseEq_refl (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar (Nat.succ Nat.zero))))
   (KExpr.sort (Level.imax (Level.succ Level.zero) Level.zero)) (KExpr.sort Level.zero)
   (kexprUniverseEq_imax_zero (Level.succ Level.zero))",
            "The actual compatibility theorem is applied across a lambda binder, including its nonzero de Bruijn substitution depth.",
        )?;

        self.add_recursive_def(
            r"def level_imax_eq_sem (u : Level) (v : Level) :
 levelEqSem (level_imax u v) (Level.imax u v) :=
 fun (r : Name -> Nat) =>
 Eq.trans Nat (evalL r (level_imax u v)) (level_eval r (level_imax u v))
   (evalL r (Level.imax u v))
   (Eq.symm Nat (level_eval r (level_imax u v)) (evalL r (level_imax u v))
     (level_eval_eq_evalL r (level_imax u v)))
   (Eq.trans Nat (level_eval r (level_imax u v)) (level_eval r (Level.imax u v))
     (evalL r (Level.imax u v))
     (level_imax_eval u v r) (level_eval_eq_evalL r (Level.imax u v)))",
            "The existing computational-model level_imax preserves semantic universes. This is not Rust smart-constructor refinement: model level_max omits the source is_geq subsumption branch.",
        )?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::test_utils::{build_spec_with_stack, run_with_stack};

    #[test]
    fn semantic_universe_relation_has_checked_equivalence_and_substitution_proofs() {
        run_with_stack(|| {
            let spec = build_spec_with_stack();
            for name in [
                "nat_max_eq_natMax",
                "imax_nat_eq_imaxNat",
                "level_eval_eq_evalL",
                "level_is_nonzero_evalL_sound",
                "levelEqSem_refl",
                "levelEqSem_symm",
                "levelEqSem_trans",
                "levelListEqSem_refl",
                "levelListEqSem_symm",
                "levelListEqSem_view_type",
                "levelListEqSem_view",
                "levelListEqSem_trans",
                "kexprUniverseEq_refl",
                "kexprUniverseEq_symm",
                "kexprUniverseEq_view_type",
                "kexprUniverseEq_view",
                "kexprUniverseEq_trans",
                "kexprUniverseEq_lift_at",
                "kexprUniverseEq_instantiate_bvar_geq",
                "kexprUniverseEq_instantiate_bvar_at",
                "kexprUniverseEq_instantiate_at",
                "kexprUniverseEq_instantiate",
                "kexprUniverseEq_imax_zero",
                "kexprUniverseEq_binder_instantiation_witness",
                "level_imax_eq_sem",
            ] {
                let declaration = spec
                    .definitions()
                    .get(name)
                    .expect("registered semantic proof");
                assert!(!declaration.is_axiom, "{name} must not be an axiom");
                assert!(
                    declaration.elaborated_value.is_some(),
                    "{name} needs an actual value"
                );
                assert!(
                    crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty(),
                    "{name} must have an empty transitive axiom closure"
                );
            }
        });
    }

    #[test]
    fn semantic_universe_relation_rejects_changed_syntax_and_false_level_equality() {
        run_with_stack(|| {
            let mut spec = build_spec_with_stack();
            for source in [
                "def semantic_false_sort_must_fail : KExprUniverseEq (KExpr.sort Level.zero) (KExpr.sort (Level.succ Level.zero)) := KExprUniverseEq.sort Level.zero (Level.succ Level.zero) (fun (v : Name -> Nat) => @Eq.refl Nat Nat.zero)",
                "def semantic_changed_literal_must_fail : KExprUniverseEq (KExpr.lit Nat.zero) (KExpr.lit (Nat.succ Nat.zero)) := KExprUniverseEq.lit Nat.zero",
                "def semantic_changed_bvar_must_fail : KExprUniverseEq (KExpr.bvar Nat.zero) (KExpr.bvar (Nat.succ Nat.zero)) := KExprUniverseEq.bvar Nat.zero",
                "def semantic_changed_name_must_fail : KExprUniverseEq (KExpr.const Name.anonymous (@ListType.nil Level)) (KExpr.const (Name.str Name.anonymous Nat.zero) (@ListType.nil Level)) := KExprUniverseEq.const Name.anonymous (@ListType.nil Level) (@ListType.nil Level) LevelListEqSem.nil",
                "def semantic_changed_arity_must_fail : LevelListEqSem (@ListType.nil Level) (@ListType.cons Level Level.zero (@ListType.nil Level)) := LevelListEqSem.nil",
            ] {
                assert!(spec.add_recursive_def(source, "Negative semantic-universe control.").is_err(),
                    "universe-only equivalence must reject changed syntax or false semantic equality");
            }
        });
    }
}

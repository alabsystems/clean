// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Exact universe instantiation for the existing generic recursor RHS builder.
//!
//! Registered before the actual iota_fires_gen migration. It changes no rule
//! storage, reduction operator or typing claim by itself.
//! Generic signatures contain only Nat arities; no indexed payload invariance
//! premise is introduced or inferred from parameter support.

use crate::spec::error::SpecError;
use crate::spec::Specification;

const PROOFS: &[(&str, &str)] = &[
    (r"def gen_rhs_instL_piN (s : Name -> Level) (dom : KExpr) (n : Nat) (body : KExpr) :
 @Eq KExpr (instL s (piN dom n body)) (piN (instL s dom) n (instL s body)) :=
 @Nat.rec (fun (k : Nat) => @Eq KExpr (instL s (piN dom k body)) (piN (instL s dom) k (instL s body)))
  (@Eq.refl KExpr (instL s body))
  (fun (k : Nat) (ih : @Eq KExpr (instL s (piN dom k body)) (piN (instL s dom) k (instL s body))) =>
   @Eq.cong KExpr KExpr (fun (b : KExpr) => KExpr.pi (instL s dom) b)
    (instL s (piN dom k body)) (piN (instL s dom) k (instL s body)) ih) n", "Universe substitution traverses the actual piN telescope by Nat induction; no domain invariance is assumed."),
    (r"def gen_rhs_instL_lamN (s : Name -> Level) (dom : KExpr) (n : Nat) (body : KExpr) :
 @Eq KExpr (instL s (lamN dom n body)) (lamN (instL s dom) n (instL s body)) :=
 @Nat.rec (fun (k : Nat) => @Eq KExpr (instL s (lamN dom k body)) (lamN (instL s dom) k (instL s body)))
  (@Eq.refl KExpr (instL s body))
  (fun (k : Nat) (ih : @Eq KExpr (instL s (lamN dom k body)) (lamN (instL s dom) k (instL s body))) =>
   @Eq.cong KExpr KExpr (fun (b : KExpr) => KExpr.lam (instL s dom) b)
    (instL s (lamN dom k body)) (lamN (instL s dom) k (instL s body)) ih) n", "Universe substitution traverses the actual lamN telescope by Nat induction; no domain invariance is assumed."),
    (r"def gen_rhs_instL_ihTel (s : Name -> Level) (r : Nat) (c : Nat) (q : Nat) (body : KExpr) :
 @Eq KExpr (instL s (ihTel r c q body)) (ihTel r c q (instL s body)) :=
 @Nat.rec (fun (k : Nat) => forall (c0 : Nat),
   @Eq KExpr (instL s (ihTel r c0 k body)) (ihTel r c0 k (instL s body)))
  (fun (c0 : Nat) => @Eq.refl KExpr (instL s body))
  (fun (k : Nat) (ih : forall (c0 : Nat), @Eq KExpr (instL s (ihTel r c0 k body)) (ihTel r c0 k (instL s body))) =>
   fun (c0 : Nat) => @Eq.cong KExpr KExpr
    (fun (b : KExpr) => KExpr.pi (KExpr.app (KExpr.bvar c0) (KExpr.bvar (Nat.sub r (Nat.succ Nat.zero)))) b)
    (instL s (ihTel r (Nat.add c0 (Nat.succ Nat.zero)) k body))
    (ihTel r (Nat.add c0 (Nat.succ Nat.zero)) k (instL s body))
    (ih (Nat.add c0 (Nat.succ Nat.zero)))) q c", "Actual ihTel domain expressions contain only bound variables; the proof follows its varying motive-index accumulator."),
    (r"def gen_rhs_instL_bvarSeq (s : Name -> Level) (top : Nat) (n : Nat) :
 @Eq (ListType KExpr) (mapLT (instL s) (bvarSeq top n)) (bvarSeq top n) :=
 @Nat.rec (fun (k : Nat) => forall (t : Nat),
   @Eq (ListType KExpr) (mapLT (instL s) (bvarSeq t k)) (bvarSeq t k))
  (fun (t : Nat) => @Eq.refl (ListType KExpr) (@ListType.nil KExpr))
  (fun (k : Nat) (ih : forall (t : Nat), @Eq (ListType KExpr) (mapLT (instL s) (bvarSeq t k)) (bvarSeq t k)) =>
   fun (t : Nat) => @Eq.cong (ListType KExpr) (ListType KExpr)
    (fun (xs : ListType KExpr) => @ListType.cons KExpr (KExpr.bvar t) xs)
    (mapLT (instL s) (bvarSeq (Nat.sub t (Nat.succ Nat.zero)) k))
    (bvarSeq (Nat.sub t (Nat.succ Nat.zero)) k)
    (ih (Nat.sub t (Nat.succ Nat.zero)))) n top", "Actual descending bvarSeq is pointwise unchanged, by Nat induction with its decreasing top index."),
    (r"def gen_rhs_instL_bvar_spine (s : Name -> Level) (top : Nat) (n : Nat) (head : KExpr) :
 @Eq KExpr (instL s (apply_spine (bvarSeq top n) head)) (apply_spine (bvarSeq top n) (instL s head)) :=
 (@Eq.trans KExpr (instL s (apply_spine (bvarSeq top n) head)) (apply_spine (mapLT (instL s) (bvarSeq top n)) (instL s head)) ((fun (xs : ListType KExpr) => apply_spine xs (instL s head)) (bvarSeq top n))
 (instL_apply_spine s (bvarSeq top n) head)
 (@Eq.cong (ListType KExpr) KExpr (fun (xs : ListType KExpr) => apply_spine xs (instL s head)) (mapLT (instL s) (bvarSeq top n)) (bvarSeq top n) (gen_rhs_instL_bvarSeq s top n)))", "Reuse the actual apply_spine substitution theorem and the derived unchanged bound-variable argument list."),
    (r"def gen_rhs_instL_minorTy (s : Name -> Level) (fam : Name) (j : Nat) (r : Nat) :
 @Eq KExpr (instL s (minorTy fam j r)) (minorTy fam j r) :=
 (@Eq.trans KExpr (instL s (minorTy fam j r)) (piN (famTypeC fam) r (instL s (ihTel r (Nat.add j r) r (KExpr.app (KExpr.bvar (Nat.add j (Nat.add r r))) (ctorApp fam j (bvarSeq (Nat.sub (Nat.add r r) (Nat.succ Nat.zero)) r)))))) ((fun (x : KExpr) => piN (famTypeC fam) r x) (ihTel r (Nat.add j r) r (KExpr.app (KExpr.bvar (Nat.add j (Nat.add r r))) (ctorApp fam j (bvarSeq (Nat.sub (Nat.add r r) (Nat.succ Nat.zero)) r)))))
 (gen_rhs_instL_piN s (famTypeC fam) r (ihTel r (Nat.add j r) r (KExpr.app (KExpr.bvar (Nat.add j (Nat.add r r))) (ctorApp fam j (bvarSeq (Nat.sub (Nat.add r r) (Nat.succ Nat.zero)) r)))))
 (@Eq.cong KExpr KExpr (fun (x : KExpr) => piN (famTypeC fam) r x) (instL s (ihTel r (Nat.add j r) r (KExpr.app (KExpr.bvar (Nat.add j (Nat.add r r))) (ctorApp fam j (bvarSeq (Nat.sub (Nat.add r r) (Nat.succ Nat.zero)) r))))) (ihTel r (Nat.add j r) r (KExpr.app (KExpr.bvar (Nat.add j (Nat.add r r))) (ctorApp fam j (bvarSeq (Nat.sub (Nat.add r r) (Nat.succ Nat.zero)) r)))) (@Eq.trans KExpr (instL s (ihTel r (Nat.add j r) r (KExpr.app (KExpr.bvar (Nat.add j (Nat.add r r))) (ctorApp fam j (bvarSeq (Nat.sub (Nat.add r r) (Nat.succ Nat.zero)) r))))) (ihTel r (Nat.add j r) r (instL s (KExpr.app (KExpr.bvar (Nat.add j (Nat.add r r))) (ctorApp fam j (bvarSeq (Nat.sub (Nat.add r r) (Nat.succ Nat.zero)) r))))) ((fun (x : KExpr) => ihTel r (Nat.add j r) r x) (KExpr.app (KExpr.bvar (Nat.add j (Nat.add r r))) (ctorApp fam j (bvarSeq (Nat.sub (Nat.add r r) (Nat.succ Nat.zero)) r))))
 (gen_rhs_instL_ihTel s r (Nat.add j r) r (KExpr.app (KExpr.bvar (Nat.add j (Nat.add r r))) (ctorApp fam j (bvarSeq (Nat.sub (Nat.add r r) (Nat.succ Nat.zero)) r))))
 (@Eq.cong KExpr KExpr (fun (x : KExpr) => ihTel r (Nat.add j r) r x) (instL s (KExpr.app (KExpr.bvar (Nat.add j (Nat.add r r))) (ctorApp fam j (bvarSeq (Nat.sub (Nat.add r r) (Nat.succ Nat.zero)) r)))) (KExpr.app (KExpr.bvar (Nat.add j (Nat.add r r))) (ctorApp fam j (bvarSeq (Nat.sub (Nat.add r r) (Nat.succ Nat.zero)) r))) (@Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.app (KExpr.bvar (Nat.add j (Nat.add r r))) x) (instL s (ctorApp fam j (bvarSeq (Nat.sub (Nat.add r r) (Nat.succ Nat.zero)) r))) (ctorApp fam j (bvarSeq (Nat.sub (Nat.add r r) (Nat.succ Nat.zero)) r)) (gen_rhs_instL_bvar_spine s (Nat.sub (Nat.add r r) (Nat.succ Nat.zero)) r (ctorC fam j)))))))", "Derived invariance of the actual generic minor type through piN, ihTel and its constructor/bvar spine. No supported-implies-invariant inference."),
    (r"def gen_rhs_instL_minorsLam (s : Name -> Level) (fam : Name) (j : Nat) (sig : ListType Nat) (body : KExpr) :
 @Eq KExpr (instL s (minorsLam fam j sig body)) (minorsLam fam j sig (instL s body)) :=
 @ListType.rec Nat
  (fun (xs : ListType Nat) => forall (j0 : Nat), @Eq KExpr (instL s (minorsLam fam j0 xs body)) (minorsLam fam j0 xs (instL s body)))
  (fun (j0 : Nat) => @Eq.refl KExpr (instL s body))
  (fun (r : Nat) (rest : ListType Nat)
    (ih : forall (j0 : Nat), @Eq KExpr (instL s (minorsLam fam j0 rest body)) (minorsLam fam j0 rest (instL s body))) =>
   fun (j0 : Nat) => (universe_bridge_congr2 KExpr KExpr KExpr KExpr.lam (instL s (minorTy fam j0 r)) (minorTy fam j0 r) (instL s (minorsLam fam (Nat.add j0 (Nat.succ Nat.zero)) rest body)) (minorsLam fam (Nat.add j0 (Nat.succ Nat.zero)) rest (instL s body)) (gen_rhs_instL_minorTy s fam j0 r) (ih (Nat.add j0 (Nat.succ Nat.zero))))) sig j", "List induction follows the actual minor-index threading. Domain invariance is the preceding proved minorTy result."),
    (r"def gen_rhs_mapLT_natural (s : Name -> Level) (f : KExpr -> KExpr) (g : KExpr -> KExpr)
 (h : forall (x : KExpr), @Eq KExpr (instL s (f x)) (g (instL s x))) (xs : ListType KExpr) :
 @Eq (ListType KExpr) (mapLT (instL s) (mapLT f xs)) (mapLT g (mapLT (instL s) xs)) :=
 @ListType.rec KExpr
  (fun (ys : ListType KExpr) => @Eq (ListType KExpr) (mapLT (instL s) (mapLT f ys)) (mapLT g (mapLT (instL s) ys)))
  (@Eq.refl (ListType KExpr) (@ListType.nil KExpr))
  (fun (x : KExpr) (rest : ListType KExpr)
    (ih : @Eq (ListType KExpr) (mapLT (instL s) (mapLT f rest)) (mapLT g (mapLT (instL s) rest))) =>
   universe_bridge_congr2 KExpr (ListType KExpr) (ListType KExpr)
    (fun (head : KExpr) (tail : ListType KExpr) => @ListType.cons KExpr head tail)
    (instL s (f x)) (g (instL s x))
    (mapLT (instL s) (mapLT f rest)) (mapLT g (mapLT (instL s) rest)) (h x) ih) xs", "Pointwise transport through the existing mapLT; the caller must prove its actual element equation."),
    (r"def gen_rhs_instL_rec_call (s : Name -> Level) (fam : Name) (sig : ListType Nat) (u : Level) (top : Nat) (n : Nat) (x : KExpr) :
 @Eq KExpr (instL s (apply_spine (list_append (bvarSeq top n) (@ListType.cons KExpr x (@ListType.nil KExpr))) (genRecC fam sig u)))
  (apply_spine (list_append (bvarSeq top n) (@ListType.cons KExpr (instL s x) (@ListType.nil KExpr))) (genRecC fam sig (substL s u))) :=
 (@Eq.trans KExpr (instL s (apply_spine (list_append (bvarSeq top n) (@ListType.cons KExpr x (@ListType.nil KExpr))) (genRecC fam sig u))) (apply_spine (mapLT (instL s) (list_append (bvarSeq top n) (@ListType.cons KExpr x (@ListType.nil KExpr)))) (genRecC fam sig (substL s u))) ((fun (xs : ListType KExpr) => apply_spine xs (genRecC fam sig (substL s u))) (list_append (bvarSeq top n) (@ListType.cons KExpr (instL s x) (@ListType.nil KExpr))))
 (instL_apply_spine s (list_append (bvarSeq top n) (@ListType.cons KExpr x (@ListType.nil KExpr))) (genRecC fam sig u))
 (@Eq.cong (ListType KExpr) KExpr (fun (xs : ListType KExpr) => apply_spine xs (genRecC fam sig (substL s u))) (mapLT (instL s) (list_append (bvarSeq top n) (@ListType.cons KExpr x (@ListType.nil KExpr)))) (list_append (bvarSeq top n) (@ListType.cons KExpr (instL s x) (@ListType.nil KExpr))) (@Eq.trans (ListType KExpr) (mapLT (instL s) (list_append (bvarSeq top n) (@ListType.cons KExpr x (@ListType.nil KExpr)))) (list_append (mapLT (instL s) (bvarSeq top n)) (@ListType.cons KExpr (instL s x) (@ListType.nil KExpr))) ((fun (xs : ListType KExpr) => list_append xs (@ListType.cons KExpr (instL s x) (@ListType.nil KExpr))) (bvarSeq top n))
 (delta_instL_map_append s (bvarSeq top n) (@ListType.cons KExpr x (@ListType.nil KExpr)))
 (@Eq.cong (ListType KExpr) (ListType KExpr) (fun (xs : ListType KExpr) => list_append xs (@ListType.cons KExpr (instL s x) (@ListType.nil KExpr))) (mapLT (instL s) (bvarSeq top n)) (bvarSeq top n) (gen_rhs_instL_bvarSeq s top n)))))", "Universe substitution acts on the actual recursive-call constant and argument x; the bound-variable prefix is proved unchanged."),
    (r"def gen_rhs_instL_recursive_spine (s : Name -> Level) (fam : Name) (sig : ListType Nat) (u : Level)
 (prefixTop : Nat) (prefixN : Nat) (top : Nat) (n : Nat) :
 @Eq (ListType KExpr) (mapLT (instL s) (mapLT (fun (x : KExpr) => apply_spine (list_append (bvarSeq prefixTop prefixN) (@ListType.cons KExpr x (@ListType.nil KExpr))) (genRecC fam sig u)) (bvarSeq top n))) (mapLT (fun (x : KExpr) => apply_spine (list_append (bvarSeq prefixTop prefixN) (@ListType.cons KExpr x (@ListType.nil KExpr))) (genRecC fam sig (substL s u))) (bvarSeq top n)) :=
 (@Eq.trans (ListType KExpr) (mapLT (instL s) (mapLT (fun (x : KExpr) => apply_spine (list_append (bvarSeq prefixTop prefixN) (@ListType.cons KExpr x (@ListType.nil KExpr))) (genRecC fam sig u)) (bvarSeq top n))) (mapLT (fun (x : KExpr) => apply_spine (list_append (bvarSeq prefixTop prefixN) (@ListType.cons KExpr x (@ListType.nil KExpr))) (genRecC fam sig (substL s u))) (mapLT (instL s) (bvarSeq top n))) ((fun (xs : ListType KExpr) => mapLT (fun (x : KExpr) => apply_spine (list_append (bvarSeq prefixTop prefixN) (@ListType.cons KExpr x (@ListType.nil KExpr))) (genRecC fam sig (substL s u))) xs) (bvarSeq top n))
 (gen_rhs_mapLT_natural s (fun (x : KExpr) => apply_spine (list_append (bvarSeq prefixTop prefixN) (@ListType.cons KExpr x (@ListType.nil KExpr))) (genRecC fam sig u)) (fun (x : KExpr) => apply_spine (list_append (bvarSeq prefixTop prefixN) (@ListType.cons KExpr x (@ListType.nil KExpr))) (genRecC fam sig (substL s u))) (fun (x : KExpr) => gen_rhs_instL_rec_call s fam sig u prefixTop prefixN x) (bvarSeq top n))
 (@Eq.cong (ListType KExpr) (ListType KExpr) (fun (xs : ListType KExpr) => mapLT (fun (x : KExpr) => apply_spine (list_append (bvarSeq prefixTop prefixN) (@ListType.cons KExpr x (@ListType.nil KExpr))) (genRecC fam sig (substL s u))) xs) (mapLT (instL s) (bvarSeq top n)) (bvarSeq top n) (gen_rhs_instL_bvarSeq s top n)))", "Actual mapped recursive-call spine transport; combines mapLT induction, the real call equation and bvarSeq invariance."),
    (r"def genRecRhsBody_instL (s : Name -> Level) (fam : Name) (sig : ListType Nat) (u : Level) (j : Nat) (r : Nat) :
 @Eq KExpr (instL s (genRecRhsBody fam sig u j r)) (genRecRhsBody fam sig (substL s u) j r) :=
 (@Eq.trans KExpr (instL s (genRecRhsBody fam sig u j r)) (apply_spine (mapLT (instL s) (list_append (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r) (mapLT (fun (x : KExpr) => apply_spine (list_append (bvarSeq (Nat.add r (sigLength sig)) (Nat.add (sigLength sig) (Nat.succ Nat.zero))) (@ListType.cons KExpr x (@ListType.nil KExpr))) (genRecC fam sig u)) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r)))) (KExpr.bvar (Nat.add r (Nat.sub (Nat.sub (sigLength sig) (Nat.succ Nat.zero)) j)))) ((fun (xs : ListType KExpr) => apply_spine xs (KExpr.bvar (Nat.add r (Nat.sub (Nat.sub (sigLength sig) (Nat.succ Nat.zero)) j)))) (list_append (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r) (mapLT (fun (x : KExpr) => apply_spine (list_append (bvarSeq (Nat.add r (sigLength sig)) (Nat.add (sigLength sig) (Nat.succ Nat.zero))) (@ListType.cons KExpr x (@ListType.nil KExpr))) (genRecC fam sig (substL s u))) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r))))
 (instL_apply_spine s (list_append (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r) (mapLT (fun (x : KExpr) => apply_spine (list_append (bvarSeq (Nat.add r (sigLength sig)) (Nat.add (sigLength sig) (Nat.succ Nat.zero))) (@ListType.cons KExpr x (@ListType.nil KExpr))) (genRecC fam sig u)) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r))) (KExpr.bvar (Nat.add r (Nat.sub (Nat.sub (sigLength sig) (Nat.succ Nat.zero)) j))))
 (@Eq.cong (ListType KExpr) KExpr (fun (xs : ListType KExpr) => apply_spine xs (KExpr.bvar (Nat.add r (Nat.sub (Nat.sub (sigLength sig) (Nat.succ Nat.zero)) j)))) (mapLT (instL s) (list_append (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r) (mapLT (fun (x : KExpr) => apply_spine (list_append (bvarSeq (Nat.add r (sigLength sig)) (Nat.add (sigLength sig) (Nat.succ Nat.zero))) (@ListType.cons KExpr x (@ListType.nil KExpr))) (genRecC fam sig u)) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r)))) (list_append (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r) (mapLT (fun (x : KExpr) => apply_spine (list_append (bvarSeq (Nat.add r (sigLength sig)) (Nat.add (sigLength sig) (Nat.succ Nat.zero))) (@ListType.cons KExpr x (@ListType.nil KExpr))) (genRecC fam sig (substL s u))) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r))) (@Eq.trans (ListType KExpr) (mapLT (instL s) (list_append (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r) (mapLT (fun (x : KExpr) => apply_spine (list_append (bvarSeq (Nat.add r (sigLength sig)) (Nat.add (sigLength sig) (Nat.succ Nat.zero))) (@ListType.cons KExpr x (@ListType.nil KExpr))) (genRecC fam sig u)) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r)))) (list_append (mapLT (instL s) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r)) (mapLT (instL s) (mapLT (fun (x : KExpr) => apply_spine (list_append (bvarSeq (Nat.add r (sigLength sig)) (Nat.add (sigLength sig) (Nat.succ Nat.zero))) (@ListType.cons KExpr x (@ListType.nil KExpr))) (genRecC fam sig u)) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r)))) ((fun (xs : ListType KExpr) (ys : ListType KExpr) => list_append xs ys) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r) (mapLT (fun (x : KExpr) => apply_spine (list_append (bvarSeq (Nat.add r (sigLength sig)) (Nat.add (sigLength sig) (Nat.succ Nat.zero))) (@ListType.cons KExpr x (@ListType.nil KExpr))) (genRecC fam sig (substL s u))) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r)))
 (delta_instL_map_append s (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r) (mapLT (fun (x : KExpr) => apply_spine (list_append (bvarSeq (Nat.add r (sigLength sig)) (Nat.add (sigLength sig) (Nat.succ Nat.zero))) (@ListType.cons KExpr x (@ListType.nil KExpr))) (genRecC fam sig u)) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r)))
 (universe_bridge_congr2 (ListType KExpr) (ListType KExpr) (ListType KExpr) (fun (xs : ListType KExpr) (ys : ListType KExpr) => list_append xs ys) (mapLT (instL s) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r)) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r) (mapLT (instL s) (mapLT (fun (x : KExpr) => apply_spine (list_append (bvarSeq (Nat.add r (sigLength sig)) (Nat.add (sigLength sig) (Nat.succ Nat.zero))) (@ListType.cons KExpr x (@ListType.nil KExpr))) (genRecC fam sig u)) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r))) (mapLT (fun (x : KExpr) => apply_spine (list_append (bvarSeq (Nat.add r (sigLength sig)) (Nat.add (sigLength sig) (Nat.succ Nat.zero))) (@ListType.cons KExpr x (@ListType.nil KExpr))) (genRecC fam sig (substL s u))) (bvarSeq (Nat.sub r (Nat.succ Nat.zero)) r)) (gen_rhs_instL_bvarSeq s (Nat.sub r (Nat.succ Nat.zero)) r) (gen_rhs_instL_recursive_spine s fam sig u (Nat.add r (sigLength sig)) (Nat.add (sigLength sig) (Nat.succ Nat.zero)) (Nat.sub r (Nat.succ Nat.zero)) r)))))", "The actual generic RHS body commutes with universe substitution, including every recursive-call head, field and prefix. Arbitrary sig/j/r; no well-formedness or output oracle."),
    (r"def genRecRhs_instL (s : Name -> Level) (fam : Name) (sig : ListType Nat) (u : Level) (j : Nat) (r : Nat) :
 @Eq KExpr (instL s (genRecRhs fam sig u j r)) (genRecRhs fam sig (substL s u) j r) :=
 (@Eq.cong KExpr KExpr (fun (b : KExpr) => KExpr.lam (genMotiveTy fam (substL s u)) b) (instL s (minorsLam fam Nat.zero sig (lamN (famTypeC fam) r (genRecRhsBody fam sig u j r)))) (minorsLam fam Nat.zero sig (lamN (famTypeC fam) r (genRecRhsBody fam sig (substL s u) j r))) (@Eq.trans KExpr (instL s (minorsLam fam Nat.zero sig (lamN (famTypeC fam) r (genRecRhsBody fam sig u j r)))) (minorsLam fam Nat.zero sig (instL s (lamN (famTypeC fam) r (genRecRhsBody fam sig u j r)))) ((fun (b : KExpr) => minorsLam fam Nat.zero sig b) (lamN (famTypeC fam) r (genRecRhsBody fam sig (substL s u) j r)))
 (gen_rhs_instL_minorsLam s fam Nat.zero sig (lamN (famTypeC fam) r (genRecRhsBody fam sig u j r)))
 (@Eq.cong KExpr KExpr (fun (b : KExpr) => minorsLam fam Nat.zero sig b) (instL s (lamN (famTypeC fam) r (genRecRhsBody fam sig u j r))) (lamN (famTypeC fam) r (genRecRhsBody fam sig (substL s u) j r)) (@Eq.trans KExpr (instL s (lamN (famTypeC fam) r (genRecRhsBody fam sig u j r))) (lamN (famTypeC fam) r (instL s (genRecRhsBody fam sig u j r))) ((fun (b : KExpr) => lamN (famTypeC fam) r b) (genRecRhsBody fam sig (substL s u) j r))
 (gen_rhs_instL_lamN s (famTypeC fam) r (genRecRhsBody fam sig u j r))
 (@Eq.cong KExpr KExpr (fun (b : KExpr) => lamN (famTypeC fam) r b) (instL s (genRecRhsBody fam sig u j r)) (genRecRhsBody fam sig (substL s u) j r) (genRecRhsBody_instL s fam sig u j r))))))", "Exact full generic RHS transport through motive, minors and field lambdas, proved from actual construction equations."),
    (r"def genRecRhs_schematic_instance (fam : Name) (sig : ListType Nat) (u : Level) (j : Nat) (r : Nat) :
 @Eq KExpr (instLevels (@ListType.cons Name Name.anonymous (@ListType.nil Name)) (genRecRhs fam sig (Level.param Name.anonymous) j r) (@ListType.cons Level u (@ListType.nil Level))) (genRecRhs fam sig u j r) :=
 genRecRhs_instL (paramSubstN (@ListType.cons Name Name.anonymous (@ListType.nil Name)) (@ListType.cons Level u (@ListType.nil Level))) fam sig (Level.param Name.anonymous) j r", "Instantiate the once-stored schematic generic RHS at the actual singleton head universe; unconditional in all generic builder parameters."),
    (r"def genRecRhs_schematic_guarded (fam : Name) (sig : ListType Nat) (u : Level) (j : Nat) (r : Nat) :
 @Eq (OptionType KExpr)
  (recursor_rhs_at (KConstSig.mk (@ListType.cons Name Name.anonymous (@ListType.nil Name)) (genRecTy fam sig (Level.param Name.anonymous))) (genRecRhs fam sig (Level.param Name.anonymous) j r) (@ListType.cons Level u (@ListType.nil Level)))
  (@OptionType.some KExpr (genRecRhs fam sig u j r)) :=
 @Eq.cong KExpr (OptionType KExpr) (fun (e : KExpr) => @OptionType.some KExpr e)
  (instLevels (@ListType.cons Name Name.anonymous (@ListType.nil Name)) (genRecRhs fam sig (Level.param Name.anonymous) j r) (@ListType.cons Level u (@ListType.nil Level))) (genRecRhs fam sig u j r)
  (genRecRhs_schematic_instance fam sig u j r)", "Direct caller of the actual guarded RHS operator: its real singleton arity guard computes; no later arithmetic reflection or assumed output equality."),
    (r"def genRecRhs_schematic_nat_zero (u : Level) :
 @Eq KExpr (instLevels (@ListType.cons Name Name.anonymous (@ListType.nil Name)) (genRecRhs natName sigNat (Level.param Name.anonymous) Nat.zero Nat.zero) (@ListType.cons Level u (@ListType.nil Level))) (natRecRhsZero u) :=
 @Eq.trans KExpr (instLevels (@ListType.cons Name Name.anonymous (@ListType.nil Name)) (genRecRhs natName sigNat (Level.param Name.anonymous) Nat.zero Nat.zero) (@ListType.cons Level u (@ListType.nil Level)))
  (genRecRhs natName sigNat u Nat.zero Nat.zero) (natRecRhsZero u)
  (genRecRhs_schematic_instance natName sigNat u Nat.zero Nat.zero) (genRecRhs_nat_zero u)", "Actual Nat degeneration caller derives the concrete RHS result from the unrestricted generic instance theorem."),
    (r"def genRecRhs_schematic_nat_succ (u : Level) :
 @Eq KExpr (instLevels (@ListType.cons Name Name.anonymous (@ListType.nil Name)) (genRecRhs natName sigNat (Level.param Name.anonymous) (Nat.succ Nat.zero) (Nat.succ Nat.zero)) (@ListType.cons Level u (@ListType.nil Level))) (natRecRhsSucc u) :=
 @Eq.trans KExpr (instLevels (@ListType.cons Name Name.anonymous (@ListType.nil Name)) (genRecRhs natName sigNat (Level.param Name.anonymous) (Nat.succ Nat.zero) (Nat.succ Nat.zero)) (@ListType.cons Level u (@ListType.nil Level)))
  (genRecRhs natName sigNat u (Nat.succ Nat.zero) (Nat.succ Nat.zero)) (natRecRhsSucc u)
  (genRecRhs_schematic_instance natName sigNat u (Nat.succ Nat.zero) (Nat.succ Nat.zero)) (genRecRhs_nat_succ u)", "Actual Nat degeneration caller derives the concrete RHS result from the unrestricted generic instance theorem."),
    (r"def genRecRhs_schematic_self_parameter (fam : Name) (sig : ListType Nat) (j : Nat) (r : Nat) :
 @Eq (OptionType KExpr)
  (recursor_rhs_at (KConstSig.mk (@ListType.cons Name Name.anonymous (@ListType.nil Name)) (genRecTy fam sig (Level.param Name.anonymous)))
   (genRecRhs fam sig (Level.param Name.anonymous) j r) (@ListType.cons Level (Level.succ (Level.param Name.anonymous)) (@ListType.nil Level)))
  (@OptionType.some KExpr (genRecRhs fam sig (Level.succ (Level.param Name.anonymous)) j r)) :=
 genRecRhs_schematic_guarded fam sig (Level.succ (Level.param Name.anonymous)) j r", "Arbitrary-family/signature guarded caller with a genuinely nonzero argument still containing the schematic parameter. No accidental second substitution."),
];

impl Specification {
    /// After generic object definitions and early delta/instL structural helpers;
    /// deliberately before add_snschema, where the actual iota_fires_gen lives.
    pub(super) fn add_recursor_generic_rhs_instances(&mut self) -> Result<(), SpecError> {
        for (source, description) in PROOFS {
            self.add_recursive_def(source, description)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::test_utils::{build_spec_with_stack, run_with_stack};

    #[test]
    fn generic_rhs_instances_have_empty_actual_axiom_closures() {
        let spec = build_spec_with_stack();
        for name in [
            "gen_rhs_instL_piN",
            "gen_rhs_instL_lamN",
            "gen_rhs_instL_ihTel",
            "gen_rhs_instL_bvarSeq",
            "gen_rhs_instL_bvar_spine",
            "gen_rhs_instL_minorTy",
            "gen_rhs_instL_minorsLam",
            "gen_rhs_mapLT_natural",
            "gen_rhs_instL_rec_call",
            "gen_rhs_instL_recursive_spine",
            "genRecRhsBody_instL",
            "genRecRhs_instL",
            "genRecRhs_schematic_instance",
            "genRecRhs_schematic_guarded",
            "genRecRhs_schematic_nat_zero",
            "genRecRhs_schematic_nat_succ",
            "genRecRhs_schematic_self_parameter",
        ] {
            let definition = spec
                .definitions()
                .get(name)
                .expect("registered generic RHS proof");
            assert!(!definition.is_axiom, "{name}");
            assert!(definition.elaborated_value.is_some(), "{name}");
            assert!(
                crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty(),
                "{name}"
            );
        }
    }

    #[test]
    fn generic_rhs_instances_reject_erasure_missing_argument_and_double_substitution() {
        run_with_stack(|| {
            let mut spec = build_spec_with_stack();
            for source in [
                "def gen_rhs_forged_erased_universe : @Eq KExpr (instLevels (@ListType.cons Name Name.anonymous (@ListType.nil Name)) (genRecRhs natName sigNat (Level.param Name.anonymous) (Nat.succ Nat.zero) (Nat.succ Nat.zero)) (@ListType.cons Level (Level.succ (Level.param Name.anonymous)) (@ListType.nil Level))) (genRecRhs natName sigNat Level.zero (Nat.succ Nat.zero) (Nat.succ Nat.zero)) := @Eq.refl KExpr (genRecRhs natName sigNat Level.zero (Nat.succ Nat.zero) (Nat.succ Nat.zero))",
                "def gen_rhs_forged_missing_argument : @Eq (OptionType KExpr) (recursor_rhs_at (KConstSig.mk (@ListType.cons Name Name.anonymous (@ListType.nil Name)) (genRecTy natName sigNat (Level.param Name.anonymous))) (genRecRhs natName sigNat (Level.param Name.anonymous) (Nat.succ Nat.zero) (Nat.succ Nat.zero)) (@ListType.nil Level)) (@OptionType.some KExpr (genRecRhs natName sigNat Level.zero (Nat.succ Nat.zero) (Nat.succ Nat.zero))) := @Eq.refl (OptionType KExpr) (@OptionType.some KExpr (genRecRhs natName sigNat Level.zero (Nat.succ Nat.zero) (Nat.succ Nat.zero)))",
                "def gen_rhs_forged_old_storage : @Eq KExpr (instLevels (@ListType.cons Name Name.anonymous (@ListType.nil Name)) (genRecRhs natName sigNat (Level.succ (Level.param Name.anonymous)) Nat.zero Nat.zero) (@ListType.cons Level (Level.succ (Level.param Name.anonymous)) (@ListType.nil Level))) (genRecRhs natName sigNat (Level.succ (Level.param Name.anonymous)) Nat.zero Nat.zero) := @Eq.refl KExpr (genRecRhs natName sigNat (Level.succ (Level.param Name.anonymous)) Nat.zero Nat.zero)",
            ] {
                assert!(spec.add_recursive_def(source, "Planted generic RHS result must be rejected").is_err());
            }
        });
    }
}

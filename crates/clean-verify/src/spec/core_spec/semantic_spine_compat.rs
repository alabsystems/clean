// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Semantic-universe compatibility of the existing list/spine operators.
//!
//! This is the pointwise companion of KExprUniverseEq, not another reduction
//! relation. Existing FVRelL/par_reduces_c_list/delta_cong_star_list fix other
//! element relations, so cannot directly express this semantic relation.
//! No generic list framework or replacement operator is introduced.
//!
//! Exact proof terms are independently checked against the 31fa57c00 export
//! (Wgxf0r, SHA256 941dcfb5f386a75f80afef5afc35dfc733e1fde210abea22bbf8ae3333478957)
//! plus the actual new universe_semantic_bridge declarations. This module is
//! unregistered pending integration. It supplies prerequisites for the current
//! model iota_reduct simulation, not that simulation itself, semantic
//! confluence, production-faithful iota (whose current model erases universes),
//! environment validity, or Rust refinement.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// Requires universe_semantic_bridge and the existing expr_model/iota_step
    /// syntax operators. No reduction environment, typing, or confluence stage.
    pub(super) fn add_semantic_spine_compat(&mut self) -> Result<(), SpecError> {
        self.add_inductive(
            r"inductive KExprListUniverseEq : ListType KExpr -> ListType KExpr -> Type
| nil : KExprListUniverseEq (@ListType.nil KExpr) (@ListType.nil KExpr)
| cons : forall (x : KExpr) (x2 : KExpr) (xs : ListType KExpr) (xs2 : ListType KExpr),
    KExprUniverseEq x x2 -> KExprListUniverseEq xs xs2 ->
    KExprListUniverseEq (@ListType.cons KExpr x xs) (@ListType.cons KExpr x2 xs2)",
            "KExprListUniverseEq: exact list shape and order, with pointwise KExprUniverseEq elements.",
        )?;

        self.add_recursive_def(
            r"def kexprListUniverseEq_refl (xs : ListType KExpr) : KExprListUniverseEq xs xs :=
 @ListType.rec KExpr (fun (ys : ListType KExpr) => KExprListUniverseEq ys ys)
   KExprListUniverseEq.nil
   (fun (x : KExpr) (ys : ListType KExpr) (ih : KExprListUniverseEq ys ys) =>
     KExprListUniverseEq.cons x x ys ys (kexprUniverseEq_refl x) ih) xs",
            "Reflexivity for the semantic relation on actual expression lists.",
        )?;

        self.add_recursive_def(
            r"def kexprListUniverseEq_length (xs : ListType KExpr) (xs2 : ListType KExpr)
 (h : KExprListUniverseEq xs xs2) : @Eq Nat (list_length xs) (list_length xs2) :=
 @KExprListUniverseEq.rec
   (fun (ys : ListType KExpr) (ys2 : ListType KExpr) (_ : KExprListUniverseEq ys ys2) =>
     @Eq Nat (list_length ys) (list_length ys2))
   (@Eq.refl Nat Nat.zero)
   (fun (x : KExpr) (x2 : KExpr) (ys : ListType KExpr) (ys2 : ListType KExpr)
     (_hx : KExprUniverseEq x x2) (_hy : KExprListUniverseEq ys ys2)
     (ih : @Eq Nat (list_length ys) (list_length ys2)) =>
     Eq.cong Nat Nat Nat.succ (list_length ys) (list_length ys2) ih) xs xs2 h",
            "Pointwise semantic relation preserves the actual list_length, without a separate arity assumption.",
        )?;

        self.add_recursive_def(
            r"def kexprListUniverseEq_append (xs : ListType KExpr) (xs2 : ListType KExpr)
 (hxs : KExprListUniverseEq xs xs2) (ys : ListType KExpr) (ys2 : ListType KExpr)
 (hys : KExprListUniverseEq ys ys2) :
 KExprListUniverseEq (list_append xs ys) (list_append xs2 ys2) :=
 @KExprListUniverseEq.rec
   (fun (zs : ListType KExpr) (zs2 : ListType KExpr) (_ : KExprListUniverseEq zs zs2) =>
     KExprListUniverseEq (list_append zs ys) (list_append zs2 ys2))
   hys
   (fun (x : KExpr) (x2 : KExpr) (zs : ListType KExpr) (zs2 : ListType KExpr)
     (hx : KExprUniverseEq x x2) (_hz : KExprListUniverseEq zs zs2)
     (ih : KExprListUniverseEq (list_append zs ys) (list_append zs2 ys2)) =>
     KExprListUniverseEq.cons x x2 (list_append zs ys) (list_append zs2 ys2) hx ih) xs xs2 hxs",
            "The existing list_append preserves pointwise semantic universes in both arguments.",
        )?;

        self.add_recursive_def(
            r"def kexprListUniverseEq_tail (xs : ListType KExpr) (xs2 : ListType KExpr)
 (h : KExprListUniverseEq xs xs2) :
 KExprListUniverseEq (list_tail xs) (list_tail xs2) :=
 @KExprListUniverseEq.rec
   (fun (ys : ListType KExpr) (ys2 : ListType KExpr) (_ : KExprListUniverseEq ys ys2) =>
     KExprListUniverseEq (list_tail ys) (list_tail ys2))
   KExprListUniverseEq.nil
   (fun (x : KExpr) (x2 : KExpr) (ys : ListType KExpr) (ys2 : ListType KExpr)
     (_hx : KExprUniverseEq x x2) (hy : KExprListUniverseEq ys ys2)
     (_ih : KExprListUniverseEq (list_tail ys) (list_tail ys2)) => hy) xs xs2 h",
            "The actual total list_tail preserves pointwise semantic universes, including nil.",
        )?;

        self.add_recursive_def(
            r"def kexprListUniverseEq_drop (n : Nat) :
 forall (xs : ListType KExpr) (xs2 : ListType KExpr), KExprListUniverseEq xs xs2 ->
 KExprListUniverseEq (list_drop n xs) (list_drop n xs2) :=
 @Nat.rec
   (fun (m : Nat) => forall (xs : ListType KExpr) (xs2 : ListType KExpr),
     KExprListUniverseEq xs xs2 -> KExprListUniverseEq (list_drop m xs) (list_drop m xs2))
   (fun (xs : ListType KExpr) (xs2 : ListType KExpr) (h : KExprListUniverseEq xs xs2) => h)
   (fun (m : Nat)
     (ih : forall (xs : ListType KExpr) (xs2 : ListType KExpr), KExprListUniverseEq xs xs2 ->
       KExprListUniverseEq (list_drop m xs) (list_drop m xs2))
     (xs : ListType KExpr) (xs2 : ListType KExpr) (h : KExprListUniverseEq xs xs2) =>
       ih (list_tail xs) (list_tail xs2) (kexprListUniverseEq_tail xs xs2 h)) n",
            "Dropping the same count preserves semantic universes using the actual Nat.rec/list_tail implementation, even beyond either list.",
        )?;

        self.add_recursive_def(
            r"def kexprListUniverseEq_take (n : Nat) :
 forall (xs : ListType KExpr) (xs2 : ListType KExpr), KExprListUniverseEq xs xs2 ->
 KExprListUniverseEq (list_take n xs) (list_take n xs2) :=
 @Nat.rec
   (fun (m : Nat) => forall (xs : ListType KExpr) (xs2 : ListType KExpr),
     KExprListUniverseEq xs xs2 -> KExprListUniverseEq (list_take m xs) (list_take m xs2))
   (fun (xs : ListType KExpr) (xs2 : ListType KExpr) (_h : KExprListUniverseEq xs xs2) =>
     KExprListUniverseEq.nil)
   (fun (m : Nat)
     (ih : forall (xs : ListType KExpr) (xs2 : ListType KExpr), KExprListUniverseEq xs xs2 ->
       KExprListUniverseEq (list_take m xs) (list_take m xs2))
     (xs : ListType KExpr) (xs2 : ListType KExpr) (h : KExprListUniverseEq xs xs2) =>
     @KExprListUniverseEq.rec
       (fun (ys : ListType KExpr) (ys2 : ListType KExpr) (_ : KExprListUniverseEq ys ys2) =>
         KExprListUniverseEq (list_take (Nat.succ m) ys) (list_take (Nat.succ m) ys2))
       KExprListUniverseEq.nil
       (fun (x : KExpr) (x2 : KExpr) (ys : ListType KExpr) (ys2 : ListType KExpr)
         (hx : KExprUniverseEq x x2) (hy : KExprListUniverseEq ys ys2)
         (_ihy : KExprListUniverseEq (list_take (Nat.succ m) ys) (list_take (Nat.succ m) ys2)) =>
         KExprListUniverseEq.cons x x2 (list_take m ys) (list_take m ys2) hx (ih ys ys2 hy)) xs xs2 h) n",
            "Taking the same count preserves semantic universes using the actual nested Nat/List recursors, including truncation at nil.",
        )?;

        self.add_recursive_def(
            r"def kexprUniverseEq_apply_spine (args : ListType KExpr) (args2 : ListType KExpr)
 (hargs : KExprListUniverseEq args args2) :
 forall (head : KExpr) (head2 : KExpr), KExprUniverseEq head head2 ->
 KExprUniverseEq (apply_spine args head) (apply_spine args2 head2) :=
 @KExprListUniverseEq.rec
   (fun (xs : ListType KExpr) (xs2 : ListType KExpr) (_ : KExprListUniverseEq xs xs2) =>
     forall (head : KExpr) (head2 : KExpr), KExprUniverseEq head head2 ->
       KExprUniverseEq (apply_spine xs head) (apply_spine xs2 head2))
   (fun (head : KExpr) (head2 : KExpr) (hh : KExprUniverseEq head head2) => hh)
   (fun (x : KExpr) (x2 : KExpr) (xs : ListType KExpr) (xs2 : ListType KExpr)
     (hx : KExprUniverseEq x x2) (_hxs : KExprListUniverseEq xs xs2)
     (ih : forall (head : KExpr) (head2 : KExpr), KExprUniverseEq head head2 ->
       KExprUniverseEq (apply_spine xs head) (apply_spine xs2 head2))
     (head : KExpr) (head2 : KExpr) (hh : KExprUniverseEq head head2) =>
     ih (KExpr.app head x) (KExpr.app head2 x2)
       (KExprUniverseEq.app head head2 x x2 hh hx)) args args2 hargs",
            "The actual left-nested application fold preserves related argument lists and heads; it does not assert any reduction.",
        )?;

        self.add_recursive_def(
            r"def kexprUniverseEq_kapp_fn (e : KExpr) (e2 : KExpr) (h : KExprUniverseEq e e2) :
 KExprUniverseEq (kapp_fn e) (kapp_fn e2) :=
 @KExprUniverseEq.rec
 (fun (a : KExpr) (b : KExpr) (_ : KExprUniverseEq a b) =>
   KExprUniverseEq (kapp_fn a) (kapp_fn b))
 (fun (u : Level) (v : Level) (h : levelEqSem u v) => KExprUniverseEq.sort u v h)
 (fun (i : Nat) => KExprUniverseEq.bvar i)
 (fun (f : KExpr) (f2 : KExpr) (a : KExpr) (a2 : KExpr) (hf : KExprUniverseEq f f2) (ha : KExprUniverseEq a a2) (ihf : KExprUniverseEq (kapp_fn f) (kapp_fn f2)) (iha : KExprUniverseEq (kapp_fn a) (kapp_fn a2)) => ihf)
 (fun (A : KExpr) (A2 : KExpr) (b : KExpr) (b2 : KExpr) (hA : KExprUniverseEq A A2) (hb : KExprUniverseEq b b2) (ihA : KExprUniverseEq (kapp_fn A) (kapp_fn A2)) (ihb : KExprUniverseEq (kapp_fn b) (kapp_fn b2)) => KExprUniverseEq.lam A A2 b b2 hA hb)
 (fun (A : KExpr) (A2 : KExpr) (b : KExpr) (b2 : KExpr) (hA : KExprUniverseEq A A2) (hb : KExprUniverseEq b b2) (ihA : KExprUniverseEq (kapp_fn A) (kapp_fn A2)) (ihb : KExprUniverseEq (kapp_fn b) (kapp_fn b2)) => KExprUniverseEq.pi A A2 b b2 hA hb)
 (fun (n : Name) (us : ListType Level) (vs : ListType Level) (h : LevelListEqSem us vs) => KExprUniverseEq.const n us vs h)
 (fun (A : KExpr) (A2 : KExpr) (v : KExpr) (v2 : KExpr) (b : KExpr) (b2 : KExpr) (hA : KExprUniverseEq A A2) (hv : KExprUniverseEq v v2) (hb : KExprUniverseEq b b2) (ihA : KExprUniverseEq (kapp_fn A) (kapp_fn A2)) (ihv : KExprUniverseEq (kapp_fn v) (kapp_fn v2)) (ihb : KExprUniverseEq (kapp_fn b) (kapp_fn b2)) => KExprUniverseEq.let_ A A2 v v2 b b2 hA hv hb)
 (fun (sn : Name) (i : Nat) (sub : KExpr) (sub2 : KExpr) (hsub : KExprUniverseEq sub sub2) (ihsub : KExprUniverseEq (kapp_fn sub) (kapp_fn sub2)) => KExprUniverseEq.proj sn i sub sub2 hsub)
 (fun (n : Nat) => KExprUniverseEq.lit n) e e2 h",
            "Head extraction preserves semantic universe equivalence. Only application strips a node; projection and binder heads retain their entire related syntax.",
        )?;

        self.add_recursive_def(
            r"def kexprUniverseEq_kapp_args (e : KExpr) (e2 : KExpr) (h : KExprUniverseEq e e2) :
 KExprListUniverseEq (kapp_args e) (kapp_args e2) :=
 @KExprUniverseEq.rec
 (fun (a : KExpr) (b : KExpr) (_ : KExprUniverseEq a b) =>
   KExprListUniverseEq (kapp_args a) (kapp_args b))
 (fun (u : Level) (v : Level) (h : levelEqSem u v) => KExprListUniverseEq.nil)
 (fun (i : Nat) => KExprListUniverseEq.nil)
 (fun (f : KExpr) (f2 : KExpr) (a : KExpr) (a2 : KExpr) (hf : KExprUniverseEq f f2) (ha : KExprUniverseEq a a2) (ihf : KExprListUniverseEq (kapp_args f) (kapp_args f2)) (iha : KExprListUniverseEq (kapp_args a) (kapp_args a2)) => kexprListUniverseEq_append (kapp_args f) (kapp_args f2) ihf
   (@ListType.cons KExpr a (@ListType.nil KExpr)) (@ListType.cons KExpr a2 (@ListType.nil KExpr))
   (KExprListUniverseEq.cons a a2 (@ListType.nil KExpr) (@ListType.nil KExpr) ha KExprListUniverseEq.nil))
 (fun (A : KExpr) (A2 : KExpr) (b : KExpr) (b2 : KExpr) (hA : KExprUniverseEq A A2) (hb : KExprUniverseEq b b2) (ihA : KExprListUniverseEq (kapp_args A) (kapp_args A2)) (ihb : KExprListUniverseEq (kapp_args b) (kapp_args b2)) => KExprListUniverseEq.nil)
 (fun (A : KExpr) (A2 : KExpr) (b : KExpr) (b2 : KExpr) (hA : KExprUniverseEq A A2) (hb : KExprUniverseEq b b2) (ihA : KExprListUniverseEq (kapp_args A) (kapp_args A2)) (ihb : KExprListUniverseEq (kapp_args b) (kapp_args b2)) => KExprListUniverseEq.nil)
 (fun (n : Name) (us : ListType Level) (vs : ListType Level) (h : LevelListEqSem us vs) => KExprListUniverseEq.nil)
 (fun (A : KExpr) (A2 : KExpr) (v : KExpr) (v2 : KExpr) (b : KExpr) (b2 : KExpr) (hA : KExprUniverseEq A A2) (hv : KExprUniverseEq v v2) (hb : KExprUniverseEq b b2) (ihA : KExprListUniverseEq (kapp_args A) (kapp_args A2)) (ihv : KExprListUniverseEq (kapp_args v) (kapp_args v2)) (ihb : KExprListUniverseEq (kapp_args b) (kapp_args b2)) => KExprListUniverseEq.nil)
 (fun (sn : Name) (i : Nat) (sub : KExpr) (sub2 : KExpr) (hsub : KExprUniverseEq sub sub2) (ihsub : KExprListUniverseEq (kapp_args sub) (kapp_args sub2)) => KExprListUniverseEq.nil)
 (fun (n : Nat) => KExprListUniverseEq.nil) e e2 h",
            "Argument extraction preserves exact spine length and order with pointwise universe equivalence, using actual append/singleton computation at app.",
        )?;

        self.add_recursive_def(
            r"def semantic_spine_reassemble_compat (e : KExpr) (e2 : KExpr) (h : KExprUniverseEq e e2) :
 KExprUniverseEq (apply_spine (kapp_args e) (kapp_fn e))
   (apply_spine (kapp_args e2) (kapp_fn e2)) :=
 kexprUniverseEq_apply_spine (kapp_args e) (kapp_args e2)
   (kexprUniverseEq_kapp_args e e2 h) (kapp_fn e) (kapp_fn e2)
   (kexprUniverseEq_kapp_fn e e2 h)",
            "The actual extraction and reassembly operators compose through the proved relation; no output or reduct correspondence is assumed.",
        )?;

        self.add_recursive_def(
            r"def semantic_spine_partition_compat (n : Nat) (args : ListType KExpr) (args2 : ListType KExpr)
 (hargs : KExprListUniverseEq args args2) (head : KExpr) (head2 : KExpr)
 (hhead : KExprUniverseEq head head2) :
 KExprUniverseEq (apply_spine (list_append (list_take n args) (list_drop n args)) head)
   (apply_spine (list_append (list_take n args2) (list_drop n args2)) head2) :=
 kexprUniverseEq_apply_spine
   (list_append (list_take n args) (list_drop n args))
   (list_append (list_take n args2) (list_drop n args2))
   (kexprListUniverseEq_append (list_take n args) (list_take n args2)
     (kexprListUniverseEq_take n args args2 hargs) (list_drop n args) (list_drop n args2)
     (kexprListUniverseEq_drop n args args2 hargs)) head head2 hhead",
            "The actual take/drop/append/application composition preserves semantics; this is an operator caller, not an iota-reduction or typing theorem.",
        )?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::test_utils::{build_spec_with_stack, run_with_stack};

    #[test]
    fn semantic_spine_operators_have_checked_axiom_free_proofs() {
        run_with_stack(|| {
            let spec = build_spec_with_stack();
            for name in [
                "kexprListUniverseEq_refl",
                "kexprListUniverseEq_length",
                "kexprListUniverseEq_append",
                "kexprListUniverseEq_tail",
                "kexprListUniverseEq_drop",
                "kexprListUniverseEq_take",
                "kexprUniverseEq_apply_spine",
                "kexprUniverseEq_kapp_fn",
                "kexprUniverseEq_kapp_args",
                "semantic_spine_reassemble_compat",
                "semantic_spine_partition_compat",
            ] {
                let declaration = spec
                    .definitions()
                    .get(name)
                    .expect("registered spine proof");
                assert!(!declaration.is_axiom, "{name}");
                assert!(declaration.elaborated_value.is_some(), "{name}");
                assert!(
                    crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty(),
                    "{name}"
                );
            }
        });
    }

    #[test]
    fn semantic_spine_relation_cannot_change_length_or_literal_payload() {
        run_with_stack(|| {
            let mut spec = build_spec_with_stack();
            for source in [
                "def semantic_spine_forged_length : KExprListUniverseEq (@ListType.nil KExpr) (@ListType.cons KExpr (KExpr.lit Nat.zero) (@ListType.nil KExpr)) := KExprListUniverseEq.nil",
                "def semantic_spine_forged_payload : KExprListUniverseEq (@ListType.cons KExpr (KExpr.lit Nat.zero) (@ListType.nil KExpr)) (@ListType.cons KExpr (KExpr.lit (Nat.succ Nat.zero)) (@ListType.nil KExpr)) := KExprListUniverseEq.cons (KExpr.lit Nat.zero) (KExpr.lit (Nat.succ Nat.zero)) (@ListType.nil KExpr) (@ListType.nil KExpr) (KExprUniverseEq.lit Nat.zero) KExprListUniverseEq.nil",
                "def semantic_spine_forged_drop : KExprListUniverseEq (list_drop (Nat.succ Nat.zero) (@ListType.cons KExpr (KExpr.lit Nat.zero) (@ListType.nil KExpr))) (@ListType.cons KExpr (KExpr.lit Nat.zero) (@ListType.nil KExpr)) := kexprListUniverseEq_refl (@ListType.cons KExpr (KExpr.lit Nat.zero) (@ListType.nil KExpr))",
            ] {
                assert!(spec.add_recursive_def(source, "Negative semantic spine control.").is_err(),
                    "pointwise universe equivalence preserves actual list shape and literal payloads");
            }
        });
    }
}

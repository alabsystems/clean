// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! General source-derived Nat.zero typing from actual typed arguments.
//!
//! Thirty-two checked declarations (8 data/24 proofs)
//! preserve the exact terms in scratch/reflected-nat-zero-general-typed-spine.rs.
//! Proof registration only desugars original binders into explicit forall/fun;
//! no status changes, self-constant proofs, or result-typing axioms are used.
//!
//! Generic input/output typing takes the actual three argument typings at any
//! raw universe in the empty context, using kcre_nat_tenv. It consumes the
//! checked actual stored-RHS instance and forward typed-spine theorem. The
//! actual guarded step is proved independently with both real guards.
//! Concrete universe-one source-environment callers exercise the generic path.
//!
//! This is the actual Nat.zero branch only: no successor/extra-argument theorem,
//! source-admission theorem, or Rust execution refinement is claimed. In
//! particular, raw-RHS telescope typing must not be imposed on every recursor:
//! source validation may check a post-beta payload (including repaired Eq rules).
//! Open-motive substitutions preserve the actual lift/cancellation semantics.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

const DECLARATIONS: &[(&str, &str)] = &[
    (r"def rfnzg_succ_case (m : KExpr) : KExpr := KExpr.pi rfnz_nat (KExpr.pi (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (KExpr.app rfnz_succ (KExpr.bvar (Nat.succ Nat.zero)))))", "Actual-name telescope/spine model data used by the source-derived Nat.zero general caller."),
    (r"def rfnzg_zero_args (m : KExpr) (z : KExpr) (s : KExpr) : ListType KExpr :=
 (@ListType.cons KExpr m (@ListType.cons KExpr z (@ListType.cons KExpr s (@ListType.nil KExpr))))", "Actual-name telescope/spine model data used by the source-derived Nat.zero general caller."),
    (r"def rfnzg_zero_rule_tail : KExpr :=
 (KExpr.pi (KExpr.app (KExpr.bvar Nat.zero) rfnz_zero) (KExpr.pi rfnz_sarm (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) rfnz_zero)))", "Actual-name telescope/spine model data used by the source-derived Nat.zero general caller."),
    (r"def rfnzg_zero_sarm_after_m (m : KExpr) : KExpr :=
 (KExpr.pi rfnz_nat (KExpr.pi (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.app rfnz_succ (KExpr.bvar (Nat.succ Nat.zero))))))", "Actual-name telescope/spine model data used by the source-derived Nat.zero general caller."),
    (r"def rfnzg_zero_tail_after_m (m : KExpr) : KExpr :=
 (KExpr.pi (KExpr.app m rfnz_zero) (KExpr.pi (rfnzg_zero_sarm_after_m m) (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) rfnz_zero)))", "Actual-name telescope/spine model data used by the source-derived Nat.zero general caller."),
    (r"def rfnzg_zero_after_m_eq (m : KExpr) : @Eq KExpr (instantiate rfnzg_zero_rule_tail m) (rfnzg_zero_tail_after_m m) :=
 (Eq.cong KExpr KExpr (fun (x : KExpr) => (KExpr.pi (KExpr.app x rfnz_zero) (KExpr.pi (rfnzg_zero_sarm_after_m m) (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) rfnz_zero)))) (lift_at m Nat.zero Nat.zero) m (lift_zero_identity m))", "Constructive source-derived Nat.zero general-caller prerequisite or closed caller; no assumption of output typing or general recursor admission."),
    (r"def rfnzg_zero_sarm_after_z_eq (m : KExpr) (z : KExpr) : @Eq KExpr (instantiate (rfnzg_zero_sarm_after_m m) z) (rfnzg_succ_case m) :=
 (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.pi rfnz_nat x) (KExpr.pi (KExpr.app (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) z (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) (KExpr.app (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) z (Nat.succ (Nat.succ Nat.zero))) (KExpr.app rfnz_succ (KExpr.bvar (Nat.succ Nat.zero))))) (KExpr.pi (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (KExpr.app rfnz_succ (KExpr.bvar (Nat.succ Nat.zero))))) (universe_bridge_congr2 KExpr KExpr KExpr (fun (A : KExpr) (B : KExpr) => KExpr.pi A B) (KExpr.app (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) z (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) (KExpr.app (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) z (Nat.succ (Nat.succ Nat.zero))) (KExpr.app rfnz_succ (KExpr.bvar (Nat.succ Nat.zero)))) (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (KExpr.app rfnz_succ (KExpr.bvar (Nat.succ Nat.zero)))) (Eq.cong KExpr KExpr (fun (x : KExpr) => (KExpr.app x (KExpr.bvar Nat.zero))) (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) z (Nat.succ Nat.zero)) (lift_at m Nat.zero (Nat.succ Nat.zero)) (inst_at1_lift2 m z)) (Eq.cong KExpr KExpr (fun (x : KExpr) => (KExpr.app x (KExpr.app rfnz_succ (KExpr.bvar (Nat.succ Nat.zero))))) (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) z (Nat.succ (Nat.succ Nat.zero))) (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (instantiate_lift_cancel_general m z Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero))) (Nat.succ (Nat.succ Nat.zero)) (@Eq.refl Nat (Nat.succ Nat.zero))))))", "Constructive source-derived Nat.zero general-caller prerequisite or closed caller; no assumption of output typing or general recursor admission."),
    (r"def rfnzg_zero_after_z_eq (m : KExpr) (z : KExpr) : @Eq KExpr (instantiate (KExpr.pi (rfnzg_zero_sarm_after_m m) (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) rfnz_zero)) z) (KExpr.pi (rfnzg_succ_case m) (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) rfnz_zero)) :=
 (universe_bridge_congr2 KExpr KExpr KExpr (fun (A : KExpr) (B : KExpr) => KExpr.pi A B) (instantiate (rfnzg_zero_sarm_after_m m) z) (rfnzg_succ_case m) (KExpr.app (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) z (Nat.succ Nat.zero)) rfnz_zero) (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) rfnz_zero) (rfnzg_zero_sarm_after_z_eq m z) (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.app x rfnz_zero) (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) z (Nat.succ Nat.zero)) (lift_at m Nat.zero (Nat.succ Nat.zero)) (inst_at1_lift2 m z)))", "Constructive source-derived Nat.zero general-caller prerequisite or closed caller; no assumption of output typing or general recursor admission."),
    (r"def rfnzg_zero_after_s_eq (m : KExpr) (s : KExpr) : @Eq KExpr (instantiate (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) rfnz_zero) s) (KExpr.app m rfnz_zero) :=
 (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.app x rfnz_zero) (instantiate (lift_at m Nat.zero (Nat.succ Nat.zero)) s) m (inst_lift1 m s))", "Constructive source-derived Nat.zero general-caller prerequisite or closed caller; no assumption of output typing or general recursor admission."),
    (r"def rfnzg_zero_typed_spine (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr) (u : Level) (m : KExpr) (z : KExpr) (s : KExpr)
 (hm : TypingCtxConvIn R tenv G m (rfnz_motive_type u))
 (hz : TypingCtxConvIn R tenv G z (KExpr.app m rfnz_zero))
 (hs : TypingCtxConvIn R tenv G s (rfnzg_succ_case m)) : TypedRawPiSpine R tenv G (rfnz_rule_type u) (rfnzg_zero_args m z s) (KExpr.app m rfnz_zero) :=
 @TypedRawPiSpine.cons R tenv G (rfnz_motive_type u) rfnzg_zero_rule_tail m (@ListType.cons KExpr z (@ListType.cons KExpr s (@ListType.nil KExpr))) (KExpr.app m rfnz_zero) hm (Eq.substType KExpr (fun (F : KExpr) => TypedRawPiSpine R tenv G F (@ListType.cons KExpr z (@ListType.cons KExpr s (@ListType.nil KExpr))) (KExpr.app m rfnz_zero)) (rfnzg_zero_tail_after_m m) (instantiate rfnzg_zero_rule_tail m) (Eq.symm KExpr (instantiate rfnzg_zero_rule_tail m) (rfnzg_zero_tail_after_m m) (rfnzg_zero_after_m_eq m)) (@TypedRawPiSpine.cons R tenv G (KExpr.app m rfnz_zero) (KExpr.pi (rfnzg_zero_sarm_after_m m) (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) rfnz_zero)) z (@ListType.cons KExpr s (@ListType.nil KExpr)) (KExpr.app m rfnz_zero) hz (Eq.substType KExpr (fun (F : KExpr) => TypedRawPiSpine R tenv G F (@ListType.cons KExpr s (@ListType.nil KExpr)) (KExpr.app m rfnz_zero)) (KExpr.pi (rfnzg_succ_case m) (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) rfnz_zero)) (instantiate (KExpr.pi (rfnzg_zero_sarm_after_m m) (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) rfnz_zero)) z) (Eq.symm KExpr (instantiate (KExpr.pi (rfnzg_zero_sarm_after_m m) (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) rfnz_zero)) z) (KExpr.pi (rfnzg_succ_case m) (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) rfnz_zero)) (rfnzg_zero_after_z_eq m z)) (@TypedRawPiSpine.cons R tenv G (rfnzg_succ_case m) (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) rfnz_zero) s (@ListType.nil KExpr) (KExpr.app m rfnz_zero) hs (Eq.substType KExpr (fun (F : KExpr) => TypedRawPiSpine R tenv G F (@ListType.nil KExpr) (KExpr.app m rfnz_zero)) (KExpr.app m rfnz_zero) (instantiate (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) rfnz_zero) s) (Eq.symm KExpr (instantiate (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) rfnz_zero) s) (KExpr.app m rfnz_zero) (rfnzg_zero_after_s_eq m s)) (@TypedRawPiSpine.nil R tenv G (KExpr.app m rfnz_zero)))))))", "Constructive source-derived Nat.zero general-caller prerequisite or closed caller; no assumption of output typing or general recursor admission."),
    (r"def rfnzg_zero_spine_open_motive_control :
 @Eq KExpr (instantiate (rfnzg_zero_sarm_after_m (KExpr.bvar Nat.zero))
   (KExpr.bvar (Nat.succ Nat.zero))) (rfnzg_succ_case (KExpr.bvar Nat.zero)) :=
 rfnzg_zero_sarm_after_z_eq (KExpr.bvar Nat.zero) (KExpr.bvar (Nat.succ Nat.zero))", "Constructive source-derived Nat.zero general-caller prerequisite or closed caller; no assumption of output typing or general recursor admission."),
    (r"def rfnzg_zero_input_args (m : KExpr) (z : KExpr) (s : KExpr) : ListType KExpr :=
 (@ListType.cons KExpr m (@ListType.cons KExpr z (@ListType.cons KExpr s (@ListType.cons KExpr rfnz_zero (@ListType.nil KExpr)))))", "Actual-name telescope/spine model data used by the source-derived Nat.zero general caller."),
    (r"def rfnzg_zero_input_tail : KExpr :=
 (KExpr.pi (KExpr.app (KExpr.bvar Nat.zero) rfnz_zero) (KExpr.pi rfnz_sarm (KExpr.pi rfnz_nat (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar Nat.zero)))))", "Actual-name telescope/spine model data used by the source-derived Nat.zero general caller."),
    (r"def rfnzg_zero_input_after_m (m : KExpr) : KExpr :=
 (KExpr.pi (KExpr.app m rfnz_zero) (KExpr.pi (rfnzg_zero_sarm_after_m m) (KExpr.pi rfnz_nat (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar Nat.zero)))))", "Actual-name telescope/spine model data used by the source-derived Nat.zero general caller."),
    (r"def rfnzg_zero_input_after_m_eq (m : KExpr) : @Eq KExpr (instantiate rfnzg_zero_input_tail m) (rfnzg_zero_input_after_m m) :=
 (Eq.cong KExpr KExpr (fun (x : KExpr) => (KExpr.pi (KExpr.app x rfnz_zero) (KExpr.pi (rfnzg_zero_sarm_after_m m) (KExpr.pi rfnz_nat (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar Nat.zero)))))) (lift_at m Nat.zero Nat.zero) m (lift_zero_identity m))", "Constructive source-derived Nat.zero general-caller prerequisite or closed caller; no assumption of output typing or general recursor admission."),
    (r"def rfnzg_zero_input_after_z_eq (m : KExpr) (z : KExpr) : @Eq KExpr (instantiate (KExpr.pi (rfnzg_zero_sarm_after_m m) (KExpr.pi rfnz_nat (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar Nat.zero)))) z) (KExpr.pi (rfnzg_succ_case m) (KExpr.pi rfnz_nat (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)))) :=
 (universe_bridge_congr2 KExpr KExpr KExpr (fun (A : KExpr) (B : KExpr) => KExpr.pi A B) (instantiate (rfnzg_zero_sarm_after_m m) z) (rfnzg_succ_case m) (KExpr.pi rfnz_nat (KExpr.app (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) z (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero))) (KExpr.pi rfnz_nat (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero))) (rfnzg_zero_sarm_after_z_eq m z) (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.pi rfnz_nat x) (KExpr.app (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) z (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (Eq.cong KExpr KExpr (fun (x : KExpr) => (KExpr.app x (KExpr.bvar Nat.zero))) (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) z (Nat.succ (Nat.succ Nat.zero))) (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (instantiate_lift_cancel_general m z Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero))) (Nat.succ (Nat.succ Nat.zero)) (@Eq.refl Nat (Nat.succ Nat.zero))))))", "Constructive source-derived Nat.zero general-caller prerequisite or closed caller; no assumption of output typing or general recursor admission."),
    (r"def rfnzg_zero_input_after_s_eq (m : KExpr) (s : KExpr) : @Eq KExpr (instantiate (KExpr.pi rfnz_nat (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero))) s) (KExpr.pi rfnz_nat (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero))) :=
 (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.pi rfnz_nat x) (KExpr.app (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) s (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) (Eq.cong KExpr KExpr (fun (x : KExpr) => (KExpr.app x (KExpr.bvar Nat.zero))) (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) s (Nat.succ Nat.zero)) (lift_at m Nat.zero (Nat.succ Nat.zero)) (inst_at1_lift2 m s)))", "Constructive source-derived Nat.zero general-caller prerequisite or closed caller; no assumption of output typing or general recursor admission."),
    (r"def rfnzg_zero_input_after_major_eq (m : KExpr) : @Eq KExpr (instantiate (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) rfnz_zero) (KExpr.app m rfnz_zero) :=
 (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.app x rfnz_zero) (instantiate (lift_at m Nat.zero (Nat.succ Nat.zero)) rfnz_zero) m (inst_lift1 m rfnz_zero))", "Constructive source-derived Nat.zero general-caller prerequisite or closed caller; no assumption of output typing or general recursor admission."),
    (r"def rfnzg_zero_input_typed_spine (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr) (u : Level) (m : KExpr) (z : KExpr) (s : KExpr)
 (hm : TypingCtxConvIn R tenv G m (rfnz_motive_type u))
 (hz : TypingCtxConvIn R tenv G z (KExpr.app m rfnz_zero))
 (hs : TypingCtxConvIn R tenv G s (rfnzg_succ_case m))
 (hzero : TypingCtxConvIn R tenv G rfnz_zero rfnz_nat) : TypedRawPiSpine R tenv G (rfnz_rec_type u) (rfnzg_zero_input_args m z s) (KExpr.app m rfnz_zero) :=
 @TypedRawPiSpine.cons R tenv G (rfnz_motive_type u) rfnzg_zero_input_tail m (@ListType.cons KExpr z (@ListType.cons KExpr s (@ListType.cons KExpr rfnz_zero (@ListType.nil KExpr)))) (KExpr.app m rfnz_zero) hm (Eq.substType KExpr (fun (F : KExpr) => TypedRawPiSpine R tenv G F (@ListType.cons KExpr z (@ListType.cons KExpr s (@ListType.cons KExpr rfnz_zero (@ListType.nil KExpr)))) (KExpr.app m rfnz_zero)) (rfnzg_zero_input_after_m m) (instantiate rfnzg_zero_input_tail m) (Eq.symm KExpr (instantiate rfnzg_zero_input_tail m) (rfnzg_zero_input_after_m m) (rfnzg_zero_input_after_m_eq m)) (@TypedRawPiSpine.cons R tenv G (KExpr.app m rfnz_zero) (KExpr.pi (rfnzg_zero_sarm_after_m m) (KExpr.pi rfnz_nat (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar Nat.zero)))) z (@ListType.cons KExpr s (@ListType.cons KExpr rfnz_zero (@ListType.nil KExpr))) (KExpr.app m rfnz_zero) hz (Eq.substType KExpr (fun (F : KExpr) => TypedRawPiSpine R tenv G F (@ListType.cons KExpr s (@ListType.cons KExpr rfnz_zero (@ListType.nil KExpr))) (KExpr.app m rfnz_zero)) (KExpr.pi (rfnzg_succ_case m) (KExpr.pi rfnz_nat (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)))) (instantiate (KExpr.pi (rfnzg_zero_sarm_after_m m) (KExpr.pi rfnz_nat (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar Nat.zero)))) z) (Eq.symm KExpr (instantiate (KExpr.pi (rfnzg_zero_sarm_after_m m) (KExpr.pi rfnz_nat (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar Nat.zero)))) z) (KExpr.pi (rfnzg_succ_case m) (KExpr.pi rfnz_nat (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)))) (rfnzg_zero_input_after_z_eq m z)) (@TypedRawPiSpine.cons R tenv G (rfnzg_succ_case m) (KExpr.pi rfnz_nat (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero))) s (@ListType.cons KExpr rfnz_zero (@ListType.nil KExpr)) (KExpr.app m rfnz_zero) hs (Eq.substType KExpr (fun (F : KExpr) => TypedRawPiSpine R tenv G F (@ListType.cons KExpr rfnz_zero (@ListType.nil KExpr)) (KExpr.app m rfnz_zero)) (KExpr.pi rfnz_nat (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero))) (instantiate (KExpr.pi rfnz_nat (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero))) s) (Eq.symm KExpr (instantiate (KExpr.pi rfnz_nat (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero))) s) (KExpr.pi rfnz_nat (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero))) (rfnzg_zero_input_after_s_eq m s)) (@TypedRawPiSpine.cons R tenv G rfnz_nat (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) rfnz_zero (@ListType.nil KExpr) (KExpr.app m rfnz_zero) hzero (Eq.substType KExpr (fun (F : KExpr) => TypedRawPiSpine R tenv G F (@ListType.nil KExpr) (KExpr.app m rfnz_zero)) (KExpr.app m rfnz_zero) (instantiate (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) rfnz_zero) (Eq.symm KExpr (instantiate (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) rfnz_zero) (KExpr.app m rfnz_zero) (rfnzg_zero_input_after_major_eq m)) (@TypedRawPiSpine.nil R tenv G (KExpr.app m rfnz_zero)))))))))", "Constructive source-derived Nat.zero general-caller prerequisite or closed caller; no assumption of output typing or general recursor admission."),
    (r"def rfnzg_source_rec_lookup (u : Level) : @Eq (OptionType KExpr)
 (kdecl_type_at kcre_nat_tenv fixture_nat_rec_name (@ListType.cons Level u (@ListType.nil Level)))
 (@OptionType.some KExpr (rfnz_rec_type u)) :=
 Eq.subst KDeclEnv (fun (tenv : KDeclEnv) => @Eq (OptionType KExpr)
  (kdecl_type_at tenv fixture_nat_rec_name (@ListType.cons Level u (@ListType.nil Level))) (@OptionType.some KExpr (rfnz_rec_type u)))
  rfnz_tenv kcre_nat_tenv rfnz_source_tenv_eq (rfnz_rec_lookup u)", "Constructive source-derived Nat.zero general-caller prerequisite or closed caller; no assumption of output typing or general recursor admission."),
    (r"def rfnzg_source_zero_typed : TypingCtxConvIn kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) rfnz_zero rfnz_nat :=
 Eq.substType KDeclEnv (fun (tenv : KDeclEnv) => TypingCtxConvIn kernel_core_red_env tenv (@ListType.nil KExpr) rfnz_zero rfnz_nat)
  rfnz_tenv kcre_nat_tenv rfnz_source_tenv_eq
  (nz_typing_to_semantic kernel_core_red_env rfnz_tenv (@ListType.nil KExpr) rfnz_zero rfnz_nat (rfnz_zero_typed (@ListType.nil KExpr)))", "Constructive source-derived Nat.zero general-caller prerequisite or closed caller; no assumption of output typing or general recursor admission."),
    (r"def rfnzg_source_general_raw_result_typed (u : Level) (m : KExpr) (z : KExpr) (s : KExpr)
 (hm : TypingCtxConvIn kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) m (rfnz_motive_type u))
 (hz : TypingCtxConvIn kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) z (KExpr.app m rfnz_zero))
 (hs : TypingCtxConvIn kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) s (rfnzg_succ_case m)) :
 TypingCtxConvIn kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) (apply_spine (rfnzg_zero_args m z s) (recursor_rhs_instance kcre_nat_rec_signature kcre_witness_nat_zero_rhs (@ListType.cons Level u (@ListType.nil Level)))) (KExpr.app m rfnz_zero) :=
 typed_raw_pi_spine_apply kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) (rfnz_rule_type u)
  (rfnzg_zero_args m z s) (KExpr.app m rfnz_zero)
  (rfnzg_zero_typed_spine kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) u m z s hm hz hs) (recursor_rhs_instance kcre_nat_rec_signature kcre_witness_nat_zero_rhs (@ListType.cons Level u (@ListType.nil Level)))
  (nz_typing_to_semantic kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) (recursor_rhs_instance kcre_nat_rec_signature kcre_witness_nat_zero_rhs (@ListType.cons Level u (@ListType.nil Level))) (rfnz_rule_type u)
   (rfnz_source_actual_instance_typed u))", "Derive actual once-instantiated Nat.zero raw-output typing from the checked source RHS instance and actual argument typings via the forward spine theorem. No output oracle."),
    (r"def rfnzg_source_general_input_typed (u : Level) (m : KExpr) (z : KExpr) (s : KExpr)
 (hm : TypingCtxConvIn kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) m (rfnz_motive_type u))
 (hz : TypingCtxConvIn kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) z (KExpr.app m rfnz_zero))
 (hs : TypingCtxConvIn kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) s (rfnzg_succ_case m)) :
 TypingCtxConvIn kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) (rfnz_rec_app u m z s rfnz_zero) (KExpr.app m rfnz_zero) :=
 typed_raw_pi_spine_const_apply kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) fixture_nat_rec_name (@ListType.cons Level u (@ListType.nil Level))
  (rfnz_rec_type u) (rfnzg_zero_input_args m z s) (KExpr.app m rfnz_zero)
  (rfnzg_source_rec_lookup u)
  (rfnzg_zero_input_typed_spine kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) u m z s hm hz hs rfnzg_source_zero_typed)", "Derive actual source-environment Nat.zero input typing from guarded recursor lookup and the actual typed argument spine."),
    (r"def rfnzg_source_general_guarded_step (u : Level) (m : KExpr) (z : KExpr) (s : KExpr) :
 iota_step (red_rec kernel_core_red_env) (rfnz_rec_app u m z s rfnz_zero)
  (apply_spine (rfnzg_zero_args m z s) (recursor_rhs_instance kcre_nat_rec_signature kcre_witness_nat_zero_rhs (@ListType.cons Level u (@ListType.nil Level)))) :=
 iota_reduct_full_recon (red_rec kernel_core_red_env) (rfnz_rec_app u m z s rfnz_zero)
  (apply_spine (rfnzg_zero_args m z s) (recursor_rhs_instance kcre_nat_rec_signature kcre_witness_nat_zero_rhs (@ListType.cons Level u (@ListType.nil Level))))
  fixture_nat_rec_name fixture_nat_rec_meta rfnz_zero fixture_nat_zero_name
  (RecRule.mk fixture_nat_zero_name Nat.zero kcre_witness_nat_zero_rhs)
  (@Eq.refl (OptionType Name) (@OptionType.some Name fixture_nat_rec_name))
  rfnz_actual_metadata
  (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr rfnz_zero))
  (@Eq.refl (OptionType Name) (@OptionType.some Name fixture_nat_zero_name))
  rfnz_actual_zero_rule (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)
  (@Eq.refl KExpr (apply_spine (rfnzg_zero_args m z s) (recursor_rhs_instance kcre_nat_rec_signature kcre_witness_nat_zero_rhs (@ListType.cons Level u (@ListType.nil Level)))))", "The actual reflected guarded zero step for arbitrary raw universe and arguments, preserving both real guards and once-instantiated RHS."),
    (r"def rfnzg_source_motive_argument_typed : TypingCtxConvIn kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) rfnz_motive (rfnz_motive_type (Level.succ Level.zero)) :=
 Eq.substType KDeclEnv (fun (tenv : KDeclEnv) => TypingCtxConvIn kernel_core_red_env tenv (@ListType.nil KExpr) rfnz_motive (rfnz_motive_type (Level.succ Level.zero)))
  rfnz_tenv kcre_nat_tenv rfnz_source_tenv_eq rfnz_motive_argument_typed", "Constructive source-derived Nat.zero general-caller prerequisite or closed caller; no assumption of output typing or general recursor admission."),
    (r"def rfnzg_source_zero_argument_typed : TypingCtxConvIn kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) rfnz_zero (KExpr.app rfnz_motive rfnz_zero) :=
 Eq.substType KDeclEnv (fun (tenv : KDeclEnv) => TypingCtxConvIn kernel_core_red_env tenv (@ListType.nil KExpr) rfnz_zero (KExpr.app rfnz_motive rfnz_zero))
  rfnz_tenv kcre_nat_tenv rfnz_source_tenv_eq rfnz_zero_argument_typed", "Constructive source-derived Nat.zero general-caller prerequisite or closed caller; no assumption of output typing or general recursor admission."),
    (r"def rfnzg_source_minor_argument_typed : TypingCtxConvIn kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) rfnz_minor (rfnzg_succ_case rfnz_motive) :=
 Eq.substType KDeclEnv (fun (tenv : KDeclEnv) => TypingCtxConvIn kernel_core_red_env tenv (@ListType.nil KExpr) rfnz_minor (rfnzg_succ_case rfnz_motive))
  rfnz_tenv kcre_nat_tenv rfnz_source_tenv_eq rfnz_minor_argument_typed", "Constructive source-derived Nat.zero general-caller prerequisite or closed caller; no assumption of output typing or general recursor admission."),
    (r"def rfnzg_source_nonzero_input : TypingCtxConvIn kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) rfnz_input (KExpr.app rfnz_motive rfnz_zero) :=
 rfnzg_source_general_input_typed (Level.succ Level.zero) rfnz_motive rfnz_zero rfnz_minor
  rfnzg_source_motive_argument_typed rfnzg_source_zero_argument_typed rfnzg_source_minor_argument_typed", "Constructive source-derived Nat.zero general-caller prerequisite or closed caller; no assumption of output typing or general recursor admission."),
    (r"def rfnzg_source_nonzero_input_nat : TypingCtxConvIn kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) rfnz_input rfnz_nat :=
 @TypingCtxConvIn.conv kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) rfnz_input (KExpr.app rfnz_motive rfnz_zero) rfnz_nat
  rfnzg_source_nonzero_input (rfnz_motive_beta rfnz_zero)", "Constructive source-derived Nat.zero general-caller prerequisite or closed caller; no assumption of output typing or general recursor admission."),
    (r"def rfnzg_source_nonzero_raw_result : TypingCtxConvIn kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) rfnz_raw_result (KExpr.app rfnz_motive rfnz_zero) :=
 rfnzg_source_general_raw_result_typed (Level.succ Level.zero) rfnz_motive rfnz_zero rfnz_minor
  rfnzg_source_motive_argument_typed rfnzg_source_zero_argument_typed rfnzg_source_minor_argument_typed", "Constructive source-derived Nat.zero general-caller prerequisite or closed caller; no assumption of output typing or general recursor admission."),
    (r"def rfnzg_source_nonzero_raw_result_nat : TypingCtxConvIn kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) rfnz_raw_result rfnz_nat :=
 @TypingCtxConvIn.conv kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) rfnz_raw_result (KExpr.app rfnz_motive rfnz_zero) rfnz_nat
  rfnzg_source_nonzero_raw_result (rfnz_motive_beta rfnz_zero)", "Constructive source-derived Nat.zero general-caller prerequisite or closed caller; no assumption of output typing or general recursor admission."),
    (r"def rfnzg_source_nonzero_step : iota_step (red_rec kernel_core_red_env) rfnz_input rfnz_raw_result :=
 rfnzg_source_general_guarded_step (Level.succ Level.zero) rfnz_motive rfnz_zero rfnz_minor", "Constructive source-derived Nat.zero general-caller prerequisite or closed caller; no assumption of output typing or general recursor admission."),
];

enum Registration {
    Data {
        declaration_index: usize,
        name: &'static str,
    },
    Proof {
        declaration_index: usize,
        name: &'static str,
        type_src: &'static str,
        value_src: &'static str,
    },
}

const REGISTRATIONS: &[Registration] = &[
    Registration::Data {
        declaration_index: 0,
        name: "rfnzg_succ_case",
    },
    Registration::Data {
        declaration_index: 1,
        name: "rfnzg_zero_args",
    },
    Registration::Data {
        declaration_index: 2,
        name: "rfnzg_zero_rule_tail",
    },
    Registration::Data {
        declaration_index: 3,
        name: "rfnzg_zero_sarm_after_m",
    },
    Registration::Data {
        declaration_index: 4,
        name: "rfnzg_zero_tail_after_m",
    },
    Registration::Proof {
        declaration_index: 5,
        name: "rfnzg_zero_after_m_eq",
        type_src: r"forall (m : KExpr),
 @Eq KExpr (instantiate rfnzg_zero_rule_tail m) (rfnzg_zero_tail_after_m m)",
        value_src: r"fun (m : KExpr) =>
 (Eq.cong KExpr KExpr (fun (x : KExpr) => (KExpr.pi (KExpr.app x rfnz_zero) (KExpr.pi (rfnzg_zero_sarm_after_m m) (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) rfnz_zero)))) (lift_at m Nat.zero Nat.zero) m (lift_zero_identity m))",
    },
    Registration::Proof {
        declaration_index: 6,
        name: "rfnzg_zero_sarm_after_z_eq",
        type_src: r"forall (m : KExpr) (z : KExpr),
 @Eq KExpr (instantiate (rfnzg_zero_sarm_after_m m) z) (rfnzg_succ_case m)",
        value_src: r"fun (m : KExpr) (z : KExpr) =>
 (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.pi rfnz_nat x) (KExpr.pi (KExpr.app (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) z (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) (KExpr.app (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) z (Nat.succ (Nat.succ Nat.zero))) (KExpr.app rfnz_succ (KExpr.bvar (Nat.succ Nat.zero))))) (KExpr.pi (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (KExpr.app rfnz_succ (KExpr.bvar (Nat.succ Nat.zero))))) (universe_bridge_congr2 KExpr KExpr KExpr (fun (A : KExpr) (B : KExpr) => KExpr.pi A B) (KExpr.app (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) z (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) (KExpr.app (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) z (Nat.succ (Nat.succ Nat.zero))) (KExpr.app rfnz_succ (KExpr.bvar (Nat.succ Nat.zero)))) (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (KExpr.app rfnz_succ (KExpr.bvar (Nat.succ Nat.zero)))) (Eq.cong KExpr KExpr (fun (x : KExpr) => (KExpr.app x (KExpr.bvar Nat.zero))) (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) z (Nat.succ Nat.zero)) (lift_at m Nat.zero (Nat.succ Nat.zero)) (inst_at1_lift2 m z)) (Eq.cong KExpr KExpr (fun (x : KExpr) => (KExpr.app x (KExpr.app rfnz_succ (KExpr.bvar (Nat.succ Nat.zero))))) (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) z (Nat.succ (Nat.succ Nat.zero))) (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (instantiate_lift_cancel_general m z Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero))) (Nat.succ (Nat.succ Nat.zero)) (@Eq.refl Nat (Nat.succ Nat.zero))))))",
    },
    Registration::Proof {
        declaration_index: 7,
        name: "rfnzg_zero_after_z_eq",
        type_src: r"forall (m : KExpr) (z : KExpr),
 @Eq KExpr (instantiate (KExpr.pi (rfnzg_zero_sarm_after_m m) (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) rfnz_zero)) z) (KExpr.pi (rfnzg_succ_case m) (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) rfnz_zero))",
        value_src: r"fun (m : KExpr) (z : KExpr) =>
 (universe_bridge_congr2 KExpr KExpr KExpr (fun (A : KExpr) (B : KExpr) => KExpr.pi A B) (instantiate (rfnzg_zero_sarm_after_m m) z) (rfnzg_succ_case m) (KExpr.app (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) z (Nat.succ Nat.zero)) rfnz_zero) (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) rfnz_zero) (rfnzg_zero_sarm_after_z_eq m z) (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.app x rfnz_zero) (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) z (Nat.succ Nat.zero)) (lift_at m Nat.zero (Nat.succ Nat.zero)) (inst_at1_lift2 m z)))",
    },
    Registration::Proof {
        declaration_index: 8,
        name: "rfnzg_zero_after_s_eq",
        type_src: r"forall (m : KExpr) (s : KExpr),
 @Eq KExpr (instantiate (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) rfnz_zero) s) (KExpr.app m rfnz_zero)",
        value_src: r"fun (m : KExpr) (s : KExpr) =>
 (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.app x rfnz_zero) (instantiate (lift_at m Nat.zero (Nat.succ Nat.zero)) s) m (inst_lift1 m s))",
    },
    Registration::Proof {
        declaration_index: 9,
        name: "rfnzg_zero_typed_spine",
        type_src: r"forall (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr) (u : Level) (m : KExpr) (z : KExpr) (s : KExpr)
 (hm : TypingCtxConvIn R tenv G m (rfnz_motive_type u))
 (hz : TypingCtxConvIn R tenv G z (KExpr.app m rfnz_zero))
 (hs : TypingCtxConvIn R tenv G s (rfnzg_succ_case m)),
 TypedRawPiSpine R tenv G (rfnz_rule_type u) (rfnzg_zero_args m z s) (KExpr.app m rfnz_zero)",
        value_src: r"fun (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr) (u : Level) (m : KExpr) (z : KExpr) (s : KExpr)
 (hm : TypingCtxConvIn R tenv G m (rfnz_motive_type u))
 (hz : TypingCtxConvIn R tenv G z (KExpr.app m rfnz_zero))
 (hs : TypingCtxConvIn R tenv G s (rfnzg_succ_case m)) =>
 @TypedRawPiSpine.cons R tenv G (rfnz_motive_type u) rfnzg_zero_rule_tail m (@ListType.cons KExpr z (@ListType.cons KExpr s (@ListType.nil KExpr))) (KExpr.app m rfnz_zero) hm (Eq.substType KExpr (fun (F : KExpr) => TypedRawPiSpine R tenv G F (@ListType.cons KExpr z (@ListType.cons KExpr s (@ListType.nil KExpr))) (KExpr.app m rfnz_zero)) (rfnzg_zero_tail_after_m m) (instantiate rfnzg_zero_rule_tail m) (Eq.symm KExpr (instantiate rfnzg_zero_rule_tail m) (rfnzg_zero_tail_after_m m) (rfnzg_zero_after_m_eq m)) (@TypedRawPiSpine.cons R tenv G (KExpr.app m rfnz_zero) (KExpr.pi (rfnzg_zero_sarm_after_m m) (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) rfnz_zero)) z (@ListType.cons KExpr s (@ListType.nil KExpr)) (KExpr.app m rfnz_zero) hz (Eq.substType KExpr (fun (F : KExpr) => TypedRawPiSpine R tenv G F (@ListType.cons KExpr s (@ListType.nil KExpr)) (KExpr.app m rfnz_zero)) (KExpr.pi (rfnzg_succ_case m) (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) rfnz_zero)) (instantiate (KExpr.pi (rfnzg_zero_sarm_after_m m) (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) rfnz_zero)) z) (Eq.symm KExpr (instantiate (KExpr.pi (rfnzg_zero_sarm_after_m m) (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) rfnz_zero)) z) (KExpr.pi (rfnzg_succ_case m) (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) rfnz_zero)) (rfnzg_zero_after_z_eq m z)) (@TypedRawPiSpine.cons R tenv G (rfnzg_succ_case m) (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) rfnz_zero) s (@ListType.nil KExpr) (KExpr.app m rfnz_zero) hs (Eq.substType KExpr (fun (F : KExpr) => TypedRawPiSpine R tenv G F (@ListType.nil KExpr) (KExpr.app m rfnz_zero)) (KExpr.app m rfnz_zero) (instantiate (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) rfnz_zero) s) (Eq.symm KExpr (instantiate (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) rfnz_zero) s) (KExpr.app m rfnz_zero) (rfnzg_zero_after_s_eq m s)) (@TypedRawPiSpine.nil R tenv G (KExpr.app m rfnz_zero)))))))",
    },
    Registration::Proof {
        declaration_index: 10,
        name: "rfnzg_zero_spine_open_motive_control",
        type_src: r"@Eq KExpr (instantiate (rfnzg_zero_sarm_after_m (KExpr.bvar Nat.zero))
   (KExpr.bvar (Nat.succ Nat.zero))) (rfnzg_succ_case (KExpr.bvar Nat.zero))",
        value_src: r"rfnzg_zero_sarm_after_z_eq (KExpr.bvar Nat.zero) (KExpr.bvar (Nat.succ Nat.zero))",
    },
    Registration::Data {
        declaration_index: 11,
        name: "rfnzg_zero_input_args",
    },
    Registration::Data {
        declaration_index: 12,
        name: "rfnzg_zero_input_tail",
    },
    Registration::Data {
        declaration_index: 13,
        name: "rfnzg_zero_input_after_m",
    },
    Registration::Proof {
        declaration_index: 14,
        name: "rfnzg_zero_input_after_m_eq",
        type_src: r"forall (m : KExpr),
 @Eq KExpr (instantiate rfnzg_zero_input_tail m) (rfnzg_zero_input_after_m m)",
        value_src: r"fun (m : KExpr) =>
 (Eq.cong KExpr KExpr (fun (x : KExpr) => (KExpr.pi (KExpr.app x rfnz_zero) (KExpr.pi (rfnzg_zero_sarm_after_m m) (KExpr.pi rfnz_nat (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar Nat.zero)))))) (lift_at m Nat.zero Nat.zero) m (lift_zero_identity m))",
    },
    Registration::Proof {
        declaration_index: 15,
        name: "rfnzg_zero_input_after_z_eq",
        type_src: r"forall (m : KExpr) (z : KExpr),
 @Eq KExpr (instantiate (KExpr.pi (rfnzg_zero_sarm_after_m m) (KExpr.pi rfnz_nat (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar Nat.zero)))) z) (KExpr.pi (rfnzg_succ_case m) (KExpr.pi rfnz_nat (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero))))",
        value_src: r"fun (m : KExpr) (z : KExpr) =>
 (universe_bridge_congr2 KExpr KExpr KExpr (fun (A : KExpr) (B : KExpr) => KExpr.pi A B) (instantiate (rfnzg_zero_sarm_after_m m) z) (rfnzg_succ_case m) (KExpr.pi rfnz_nat (KExpr.app (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) z (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero))) (KExpr.pi rfnz_nat (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero))) (rfnzg_zero_sarm_after_z_eq m z) (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.pi rfnz_nat x) (KExpr.app (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) z (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (Eq.cong KExpr KExpr (fun (x : KExpr) => (KExpr.app x (KExpr.bvar Nat.zero))) (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) z (Nat.succ (Nat.succ Nat.zero))) (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (instantiate_lift_cancel_general m z Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero))) (Nat.succ (Nat.succ Nat.zero)) (@Eq.refl Nat (Nat.succ Nat.zero))))))",
    },
    Registration::Proof {
        declaration_index: 16,
        name: "rfnzg_zero_input_after_s_eq",
        type_src: r"forall (m : KExpr) (s : KExpr),
 @Eq KExpr (instantiate (KExpr.pi rfnz_nat (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero))) s) (KExpr.pi rfnz_nat (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)))",
        value_src: r"fun (m : KExpr) (s : KExpr) =>
 (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.pi rfnz_nat x) (KExpr.app (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) s (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) (Eq.cong KExpr KExpr (fun (x : KExpr) => (KExpr.app x (KExpr.bvar Nat.zero))) (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) s (Nat.succ Nat.zero)) (lift_at m Nat.zero (Nat.succ Nat.zero)) (inst_at1_lift2 m s)))",
    },
    Registration::Proof {
        declaration_index: 17,
        name: "rfnzg_zero_input_after_major_eq",
        type_src: r"forall (m : KExpr),
 @Eq KExpr (instantiate (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) rfnz_zero) (KExpr.app m rfnz_zero)",
        value_src: r"fun (m : KExpr) =>
 (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.app x rfnz_zero) (instantiate (lift_at m Nat.zero (Nat.succ Nat.zero)) rfnz_zero) m (inst_lift1 m rfnz_zero))",
    },
    Registration::Proof {
        declaration_index: 18,
        name: "rfnzg_zero_input_typed_spine",
        type_src: r"forall (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr) (u : Level) (m : KExpr) (z : KExpr) (s : KExpr)
 (hm : TypingCtxConvIn R tenv G m (rfnz_motive_type u))
 (hz : TypingCtxConvIn R tenv G z (KExpr.app m rfnz_zero))
 (hs : TypingCtxConvIn R tenv G s (rfnzg_succ_case m))
 (hzero : TypingCtxConvIn R tenv G rfnz_zero rfnz_nat),
 TypedRawPiSpine R tenv G (rfnz_rec_type u) (rfnzg_zero_input_args m z s) (KExpr.app m rfnz_zero)",
        value_src: r"fun (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr) (u : Level) (m : KExpr) (z : KExpr) (s : KExpr)
 (hm : TypingCtxConvIn R tenv G m (rfnz_motive_type u))
 (hz : TypingCtxConvIn R tenv G z (KExpr.app m rfnz_zero))
 (hs : TypingCtxConvIn R tenv G s (rfnzg_succ_case m))
 (hzero : TypingCtxConvIn R tenv G rfnz_zero rfnz_nat) =>
 @TypedRawPiSpine.cons R tenv G (rfnz_motive_type u) rfnzg_zero_input_tail m (@ListType.cons KExpr z (@ListType.cons KExpr s (@ListType.cons KExpr rfnz_zero (@ListType.nil KExpr)))) (KExpr.app m rfnz_zero) hm (Eq.substType KExpr (fun (F : KExpr) => TypedRawPiSpine R tenv G F (@ListType.cons KExpr z (@ListType.cons KExpr s (@ListType.cons KExpr rfnz_zero (@ListType.nil KExpr)))) (KExpr.app m rfnz_zero)) (rfnzg_zero_input_after_m m) (instantiate rfnzg_zero_input_tail m) (Eq.symm KExpr (instantiate rfnzg_zero_input_tail m) (rfnzg_zero_input_after_m m) (rfnzg_zero_input_after_m_eq m)) (@TypedRawPiSpine.cons R tenv G (KExpr.app m rfnz_zero) (KExpr.pi (rfnzg_zero_sarm_after_m m) (KExpr.pi rfnz_nat (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar Nat.zero)))) z (@ListType.cons KExpr s (@ListType.cons KExpr rfnz_zero (@ListType.nil KExpr))) (KExpr.app m rfnz_zero) hz (Eq.substType KExpr (fun (F : KExpr) => TypedRawPiSpine R tenv G F (@ListType.cons KExpr s (@ListType.cons KExpr rfnz_zero (@ListType.nil KExpr))) (KExpr.app m rfnz_zero)) (KExpr.pi (rfnzg_succ_case m) (KExpr.pi rfnz_nat (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)))) (instantiate (KExpr.pi (rfnzg_zero_sarm_after_m m) (KExpr.pi rfnz_nat (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar Nat.zero)))) z) (Eq.symm KExpr (instantiate (KExpr.pi (rfnzg_zero_sarm_after_m m) (KExpr.pi rfnz_nat (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar Nat.zero)))) z) (KExpr.pi (rfnzg_succ_case m) (KExpr.pi rfnz_nat (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)))) (rfnzg_zero_input_after_z_eq m z)) (@TypedRawPiSpine.cons R tenv G (rfnzg_succ_case m) (KExpr.pi rfnz_nat (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero))) s (@ListType.cons KExpr rfnz_zero (@ListType.nil KExpr)) (KExpr.app m rfnz_zero) hs (Eq.substType KExpr (fun (F : KExpr) => TypedRawPiSpine R tenv G F (@ListType.cons KExpr rfnz_zero (@ListType.nil KExpr)) (KExpr.app m rfnz_zero)) (KExpr.pi rfnz_nat (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero))) (instantiate (KExpr.pi rfnz_nat (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero))) s) (Eq.symm KExpr (instantiate (KExpr.pi rfnz_nat (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero))) s) (KExpr.pi rfnz_nat (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero))) (rfnzg_zero_input_after_s_eq m s)) (@TypedRawPiSpine.cons R tenv G rfnz_nat (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) rfnz_zero (@ListType.nil KExpr) (KExpr.app m rfnz_zero) hzero (Eq.substType KExpr (fun (F : KExpr) => TypedRawPiSpine R tenv G F (@ListType.nil KExpr) (KExpr.app m rfnz_zero)) (KExpr.app m rfnz_zero) (instantiate (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) rfnz_zero) (Eq.symm KExpr (instantiate (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) rfnz_zero) (KExpr.app m rfnz_zero) (rfnzg_zero_input_after_major_eq m)) (@TypedRawPiSpine.nil R tenv G (KExpr.app m rfnz_zero)))))))))",
    },
    Registration::Proof {
        declaration_index: 19,
        name: "rfnzg_source_rec_lookup",
        type_src: r"forall (u : Level),
 @Eq (OptionType KExpr)
 (kdecl_type_at kcre_nat_tenv fixture_nat_rec_name (@ListType.cons Level u (@ListType.nil Level)))
 (@OptionType.some KExpr (rfnz_rec_type u))",
        value_src: r"fun (u : Level) =>
 Eq.subst KDeclEnv (fun (tenv : KDeclEnv) => @Eq (OptionType KExpr)
  (kdecl_type_at tenv fixture_nat_rec_name (@ListType.cons Level u (@ListType.nil Level))) (@OptionType.some KExpr (rfnz_rec_type u)))
  rfnz_tenv kcre_nat_tenv rfnz_source_tenv_eq (rfnz_rec_lookup u)",
    },
    Registration::Proof {
        declaration_index: 20,
        name: "rfnzg_source_zero_typed",
        type_src: r"TypingCtxConvIn kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) rfnz_zero rfnz_nat",
        value_src: r"Eq.substType KDeclEnv (fun (tenv : KDeclEnv) => TypingCtxConvIn kernel_core_red_env tenv (@ListType.nil KExpr) rfnz_zero rfnz_nat)
  rfnz_tenv kcre_nat_tenv rfnz_source_tenv_eq
  (nz_typing_to_semantic kernel_core_red_env rfnz_tenv (@ListType.nil KExpr) rfnz_zero rfnz_nat (rfnz_zero_typed (@ListType.nil KExpr)))",
    },
    Registration::Proof {
        declaration_index: 21,
        name: "rfnzg_source_general_raw_result_typed",
        type_src: r"forall (u : Level) (m : KExpr) (z : KExpr) (s : KExpr)
 (hm : TypingCtxConvIn kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) m (rfnz_motive_type u))
 (hz : TypingCtxConvIn kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) z (KExpr.app m rfnz_zero))
 (hs : TypingCtxConvIn kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) s (rfnzg_succ_case m)),
 TypingCtxConvIn kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) (apply_spine (rfnzg_zero_args m z s) (recursor_rhs_instance kcre_nat_rec_signature kcre_witness_nat_zero_rhs (@ListType.cons Level u (@ListType.nil Level)))) (KExpr.app m rfnz_zero)",
        value_src: r"fun (u : Level) (m : KExpr) (z : KExpr) (s : KExpr)
 (hm : TypingCtxConvIn kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) m (rfnz_motive_type u))
 (hz : TypingCtxConvIn kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) z (KExpr.app m rfnz_zero))
 (hs : TypingCtxConvIn kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) s (rfnzg_succ_case m)) =>
 typed_raw_pi_spine_apply kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) (rfnz_rule_type u)
  (rfnzg_zero_args m z s) (KExpr.app m rfnz_zero)
  (rfnzg_zero_typed_spine kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) u m z s hm hz hs) (recursor_rhs_instance kcre_nat_rec_signature kcre_witness_nat_zero_rhs (@ListType.cons Level u (@ListType.nil Level)))
  (nz_typing_to_semantic kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) (recursor_rhs_instance kcre_nat_rec_signature kcre_witness_nat_zero_rhs (@ListType.cons Level u (@ListType.nil Level))) (rfnz_rule_type u)
   (rfnz_source_actual_instance_typed u))",
    },
    Registration::Proof {
        declaration_index: 22,
        name: "rfnzg_source_general_input_typed",
        type_src: r"forall (u : Level) (m : KExpr) (z : KExpr) (s : KExpr)
 (hm : TypingCtxConvIn kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) m (rfnz_motive_type u))
 (hz : TypingCtxConvIn kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) z (KExpr.app m rfnz_zero))
 (hs : TypingCtxConvIn kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) s (rfnzg_succ_case m)),
 TypingCtxConvIn kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) (rfnz_rec_app u m z s rfnz_zero) (KExpr.app m rfnz_zero)",
        value_src: r"fun (u : Level) (m : KExpr) (z : KExpr) (s : KExpr)
 (hm : TypingCtxConvIn kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) m (rfnz_motive_type u))
 (hz : TypingCtxConvIn kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) z (KExpr.app m rfnz_zero))
 (hs : TypingCtxConvIn kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) s (rfnzg_succ_case m)) =>
 typed_raw_pi_spine_const_apply kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) fixture_nat_rec_name (@ListType.cons Level u (@ListType.nil Level))
  (rfnz_rec_type u) (rfnzg_zero_input_args m z s) (KExpr.app m rfnz_zero)
  (rfnzg_source_rec_lookup u)
  (rfnzg_zero_input_typed_spine kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) u m z s hm hz hs rfnzg_source_zero_typed)",
    },
    Registration::Proof {
        declaration_index: 23,
        name: "rfnzg_source_general_guarded_step",
        type_src: r"forall (u : Level) (m : KExpr) (z : KExpr) (s : KExpr),
 iota_step (red_rec kernel_core_red_env) (rfnz_rec_app u m z s rfnz_zero)
  (apply_spine (rfnzg_zero_args m z s) (recursor_rhs_instance kcre_nat_rec_signature kcre_witness_nat_zero_rhs (@ListType.cons Level u (@ListType.nil Level))))",
        value_src: r"fun (u : Level) (m : KExpr) (z : KExpr) (s : KExpr) =>
 iota_reduct_full_recon (red_rec kernel_core_red_env) (rfnz_rec_app u m z s rfnz_zero)
  (apply_spine (rfnzg_zero_args m z s) (recursor_rhs_instance kcre_nat_rec_signature kcre_witness_nat_zero_rhs (@ListType.cons Level u (@ListType.nil Level))))
  fixture_nat_rec_name fixture_nat_rec_meta rfnz_zero fixture_nat_zero_name
  (RecRule.mk fixture_nat_zero_name Nat.zero kcre_witness_nat_zero_rhs)
  (@Eq.refl (OptionType Name) (@OptionType.some Name fixture_nat_rec_name))
  rfnz_actual_metadata
  (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr rfnz_zero))
  (@Eq.refl (OptionType Name) (@OptionType.some Name fixture_nat_zero_name))
  rfnz_actual_zero_rule (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)
  (@Eq.refl KExpr (apply_spine (rfnzg_zero_args m z s) (recursor_rhs_instance kcre_nat_rec_signature kcre_witness_nat_zero_rhs (@ListType.cons Level u (@ListType.nil Level)))))",
    },
    Registration::Proof {
        declaration_index: 24,
        name: "rfnzg_source_motive_argument_typed",
        type_src: r"TypingCtxConvIn kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) rfnz_motive (rfnz_motive_type (Level.succ Level.zero))",
        value_src: r"Eq.substType KDeclEnv (fun (tenv : KDeclEnv) => TypingCtxConvIn kernel_core_red_env tenv (@ListType.nil KExpr) rfnz_motive (rfnz_motive_type (Level.succ Level.zero)))
  rfnz_tenv kcre_nat_tenv rfnz_source_tenv_eq rfnz_motive_argument_typed",
    },
    Registration::Proof {
        declaration_index: 25,
        name: "rfnzg_source_zero_argument_typed",
        type_src: r"TypingCtxConvIn kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) rfnz_zero (KExpr.app rfnz_motive rfnz_zero)",
        value_src: r"Eq.substType KDeclEnv (fun (tenv : KDeclEnv) => TypingCtxConvIn kernel_core_red_env tenv (@ListType.nil KExpr) rfnz_zero (KExpr.app rfnz_motive rfnz_zero))
  rfnz_tenv kcre_nat_tenv rfnz_source_tenv_eq rfnz_zero_argument_typed",
    },
    Registration::Proof {
        declaration_index: 26,
        name: "rfnzg_source_minor_argument_typed",
        type_src: r"TypingCtxConvIn kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) rfnz_minor (rfnzg_succ_case rfnz_motive)",
        value_src: r"Eq.substType KDeclEnv (fun (tenv : KDeclEnv) => TypingCtxConvIn kernel_core_red_env tenv (@ListType.nil KExpr) rfnz_minor (rfnzg_succ_case rfnz_motive))
  rfnz_tenv kcre_nat_tenv rfnz_source_tenv_eq rfnz_minor_argument_typed",
    },
    Registration::Proof {
        declaration_index: 27,
        name: "rfnzg_source_nonzero_input",
        type_src: r"TypingCtxConvIn kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) rfnz_input (KExpr.app rfnz_motive rfnz_zero)",
        value_src: r"rfnzg_source_general_input_typed (Level.succ Level.zero) rfnz_motive rfnz_zero rfnz_minor
  rfnzg_source_motive_argument_typed rfnzg_source_zero_argument_typed rfnzg_source_minor_argument_typed",
    },
    Registration::Proof {
        declaration_index: 28,
        name: "rfnzg_source_nonzero_input_nat",
        type_src: r"TypingCtxConvIn kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) rfnz_input rfnz_nat",
        value_src: r"@TypingCtxConvIn.conv kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) rfnz_input (KExpr.app rfnz_motive rfnz_zero) rfnz_nat
  rfnzg_source_nonzero_input (rfnz_motive_beta rfnz_zero)",
    },
    Registration::Proof {
        declaration_index: 29,
        name: "rfnzg_source_nonzero_raw_result",
        type_src: r"TypingCtxConvIn kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) rfnz_raw_result (KExpr.app rfnz_motive rfnz_zero)",
        value_src: r"rfnzg_source_general_raw_result_typed (Level.succ Level.zero) rfnz_motive rfnz_zero rfnz_minor
  rfnzg_source_motive_argument_typed rfnzg_source_zero_argument_typed rfnzg_source_minor_argument_typed",
    },
    Registration::Proof {
        declaration_index: 30,
        name: "rfnzg_source_nonzero_raw_result_nat",
        type_src: r"TypingCtxConvIn kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) rfnz_raw_result rfnz_nat",
        value_src: r"@TypingCtxConvIn.conv kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) rfnz_raw_result (KExpr.app rfnz_motive rfnz_zero) rfnz_nat
  rfnzg_source_nonzero_raw_result (rfnz_motive_beta rfnz_zero)",
    },
    Registration::Proof {
        declaration_index: 31,
        name: "rfnzg_source_nonzero_step",
        type_src: r"iota_step (red_rec kernel_core_red_env) rfnz_input rfnz_raw_result",
        value_src: r"rfnzg_source_general_guarded_step (Level.succ Level.zero) rfnz_motive rfnz_zero rfnz_minor",
    },
];

fn checked_definition(
    name: &str,
    type_src: &str,
    value_src: &str,
    description: &str,
) -> SpecDefinition {
    SpecDefinition {
        name: name.to_string(),
        type_src: type_src.to_string(),
        value_src: Some(value_src.to_string()),
        is_axiom: false,
        description: description.to_string(),
        category: AxiomCategory::DerivedLemma,
        proof_status: ProofStatus::DerivedProved,
        elaborated_type: None,
        elaborated_value: None,
        dependencies: None,
        axiom_deps: HashSet::new(),
    }
}

impl Specification {
    /// Requires add_reflected_nat_zero_source_bridge, the existing typed-spine
    /// forward wrappers, and the existing raw substitution/lift cancellation lemmas.
    pub(super) fn add_reflected_nat_zero_general(&mut self) -> Result<(), SpecError> {
        for registration in REGISTRATIONS {
            match registration {
                Registration::Data {
                    declaration_index,
                    name,
                } => {
                    let (source, description) = DECLARATIONS[*declaration_index];
                    self.add_recursive_def(source, description)?;
                    debug_assert!(self.definitions().contains_key(*name));
                }
                Registration::Proof {
                    declaration_index,
                    name,
                    type_src,
                    value_src,
                } => {
                    self.add_definition(checked_definition(
                        name,
                        type_src,
                        value_src,
                        DECLARATIONS[*declaration_index].1,
                    ))?;
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::{checked_definition, Registration, DECLARATIONS, REGISTRATIONS};
    use crate::spec::types::{AxiomCategory, ProofStatus};
    use crate::test_utils::{build_spec_with_stack, parse_check, run_with_stack};
    use clean_kernel::{ConstantKind, ExprKind, Name, TypeChecker};

    const PROOF_ROOTS: &[&str] = &[
        "rfnzg_zero_after_m_eq",
        "rfnzg_zero_sarm_after_z_eq",
        "rfnzg_zero_after_z_eq",
        "rfnzg_zero_after_s_eq",
        "rfnzg_zero_typed_spine",
        "rfnzg_zero_spine_open_motive_control",
        "rfnzg_zero_input_after_m_eq",
        "rfnzg_zero_input_after_z_eq",
        "rfnzg_zero_input_after_s_eq",
        "rfnzg_zero_input_after_major_eq",
        "rfnzg_zero_input_typed_spine",
        "rfnzg_source_rec_lookup",
        "rfnzg_source_zero_typed",
        "rfnzg_source_general_raw_result_typed",
        "rfnzg_source_general_input_typed",
        "rfnzg_source_general_guarded_step",
        "rfnzg_source_motive_argument_typed",
        "rfnzg_source_zero_argument_typed",
        "rfnzg_source_minor_argument_typed",
        "rfnzg_source_nonzero_input",
        "rfnzg_source_nonzero_input_nat",
        "rfnzg_source_nonzero_raw_result",
        "rfnzg_source_nonzero_raw_result_nat",
        "rfnzg_source_nonzero_step",
    ];
    const REUSED_PROOFS: &[&str] = &[
        "typed_raw_pi_spine_apply",
        "typed_raw_pi_spine_const_apply",
        "rfnz_source_actual_instance_typed",
    ];

    struct Refusal {
        name: &'static str,
        type_src: &'static str,
        value_src: &'static str,
    }

    // All six exact independently rejected general-caller proof terms.
    const REFUSALS: &[Refusal] = &[
        Refusal {
            name: "rfnzg_forged_raw_type",
            type_src: r"TypingCtxConvIn kernel_core_red_env kcre_nat_tenv
 (@ListType.nil KExpr) rfnz_raw_result (KExpr.sort Level.zero)",
            value_src: r"rfnzg_source_nonzero_raw_result_nat",
        },
        Refusal {
            name: "rfnzg_forged_minor",
            type_src: r"TypingCtxConvIn kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr)
 rfnz_raw_result (KExpr.app rfnz_motive rfnz_zero)",
            value_src: r"rfnzg_source_general_raw_result_typed (Level.succ Level.zero) rfnz_motive rfnz_zero rfnz_minor
  rfnzg_source_motive_argument_typed rfnzg_source_zero_argument_typed rfnzg_source_zero_argument_typed",
        },
        Refusal {
            name: "rfnzg_forged_universe",
            type_src: r"iota_step (red_rec kernel_core_red_env) rfnz_input
 (KExpr.app (KExpr.app (KExpr.app
  (recursor_rhs_instance kcre_nat_rec_signature kcre_witness_nat_zero_rhs (@ListType.cons Level Level.zero (@ListType.nil Level)))
  rfnz_motive) rfnz_zero) rfnz_minor)",
            value_src: r"rfnzg_source_nonzero_step",
        },
        Refusal {
            name: "rfnzg_forged_open_motive_erasure",
            type_src: r"@Eq KExpr (instantiate (rfnzg_zero_sarm_after_m (KExpr.bvar Nat.zero))
  (KExpr.bvar (Nat.succ Nat.zero))) (rfnzg_succ_case (KExpr.sort Level.zero))",
            value_src: r"rfnzg_zero_spine_open_motive_control",
        },
        Refusal {
            name: "rfnzg_forged_input_type",
            type_src: r"TypingCtxConvIn kernel_core_red_env kcre_nat_tenv
 (@ListType.nil KExpr) rfnz_input (KExpr.sort Level.zero)",
            value_src: r"rfnzg_source_nonzero_input",
        },
        Refusal {
            name: "rfnzg_forged_input_missing_universe",
            type_src: r"TypingCtxConvIn kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr)
  (apply_spine (rfnzg_zero_input_args rfnz_motive rfnz_zero rfnz_minor)
   (KExpr.const fixture_nat_rec_name (@ListType.nil Level))) (KExpr.app rfnz_motive rfnz_zero)",
            value_src: r"rfnzg_source_nonzero_input",
        },
    ];

    #[test]
    fn reflected_nat_general_sources_parse_and_preserve_checked_terms() {
        use clean_parser::{parse_decl, parse_expr, Span, SurfaceDecl, SurfaceExpr};
        fn fragment(source: &str, span: Span) -> Vec<&str> {
            source[span.start..span.end].split_whitespace().collect()
        }
        assert_eq!(DECLARATIONS.len(), 32);
        assert_eq!(REGISTRATIONS.len(), DECLARATIONS.len());
        assert_eq!(PROOF_ROOTS.len(), 24);
        let mut data = 0;
        let mut proofs = 0;
        let mut seen = std::collections::HashSet::new();
        for (index, registration) in REGISTRATIONS.iter().enumerate() {
            let (source, _) = DECLARATIONS[index];
            parse_check(source).expect("original checked declaration parses");
            let SurfaceDecl::Def {
                name,
                binders,
                ty: Some(result),
                val,
                ..
            } = parse_decl(source).expect("original declaration AST")
            else {
                panic!("expected explicit checked definition")
            };
            assert!(seen.insert(name.clone()), "duplicate registration");
            assert!(
                !REUSED_PROOFS
                    .iter()
                    .any(|candidate| clean_parser::parse_name(candidate)
                        .expect("explicit source name")
                        == name),
                "existing helpers are reused, not re-registered"
            );
            match registration {
                Registration::Data {
                    declaration_index,
                    name: registered,
                } => {
                    data += 1;
                    assert_eq!(*declaration_index, index);
                    assert_eq!(
                        clean_parser::parse_name(registered).expect("explicit source name"),
                        name
                    );
                    assert!(!PROOF_ROOTS.contains(registered));
                }
                Registration::Proof {
                    declaration_index,
                    name: registered,
                    type_src,
                    value_src,
                } => {
                    proofs += 1;
                    assert_eq!(*declaration_index, index);
                    assert_eq!(
                        clean_parser::parse_name(registered).expect("explicit source name"),
                        name
                    );
                    assert!(PROOF_ROOTS.contains(registered));
                    assert_ne!(value_src.trim(), *registered, "no self-constant proof");
                    parse_check(&format!("def {registered} : {type_src} := {value_src}"))
                        .expect("explicit proof record parses");
                    let parsed_type = parse_expr(type_src).expect("explicit theorem type");
                    let parsed_value = parse_expr(value_src).expect("explicit theorem body");
                    if binders.is_empty() {
                        assert_eq!(
                            fragment(source, result.span()),
                            fragment(type_src, parsed_type.span()),
                            "{name}: result"
                        );
                        assert_eq!(
                            fragment(source, val.span()),
                            fragment(value_src, parsed_value.span()),
                            "{name}: body"
                        );
                    } else {
                        let SurfaceExpr::Pi(_, type_binders, explicit_result) = parsed_type else {
                            panic!("{name}: expected forall")
                        };
                        let SurfaceExpr::Lambda(_, value_binders, explicit_body) = parsed_value
                        else {
                            panic!("{name}: expected fun")
                        };
                        assert_eq!(type_binders.len(), binders.len(), "{name}: type binders");
                        assert_eq!(value_binders.len(), binders.len(), "{name}: value binders");
                        for ((original, type_binder), value_binder) in
                            binders.iter().zip(&type_binders).zip(&value_binders)
                        {
                            assert_eq!(
                                fragment(source, original.span),
                                fragment(type_src, type_binder.span),
                                "{name}: forall binder"
                            );
                            assert_eq!(
                                fragment(source, original.span),
                                fragment(value_src, value_binder.span),
                                "{name}: fun binder"
                            );
                        }
                        assert_eq!(
                            fragment(source, result.span()),
                            fragment(type_src, explicit_result.span()),
                            "{name}: result"
                        );
                        assert_eq!(
                            fragment(source, val.span()),
                            fragment(value_src, explicit_body.span()),
                            "{name}: body"
                        );
                    }
                }
            }
        }
        assert_eq!((data, proofs), (8, 24));
        assert_eq!(REFUSALS.len(), 6);
        for refusal in REFUSALS {
            parse_check(&format!(
                "def {} : {} := {}",
                refusal.name, refusal.type_src, refusal.value_src
            ))
            .expect("forged statement and proof parse before refusal is tested");
        }
    }

    #[test]
    fn reflected_nat_general_actual_roots_values_types_and_closures_recheck() {
        run_with_stack(|| {
            let spec = build_spec_with_stack();
            let names = REGISTRATIONS
                .iter()
                .map(|registration| match registration {
                    Registration::Data { name, .. } | Registration::Proof { name, .. } => *name,
                })
                .chain(REUSED_PROOFS.iter().copied());
            for root in names {
                let definition = spec
                    .definitions()
                    .get(root)
                    .expect("registered declaration root");
                let name = Name::from_string(root);
                let constant = spec
                    .env()
                    .get_const(&name)
                    .expect("actual kernel environment root");
                let ty = definition
                    .elaborated_type
                    .as_ref()
                    .expect("actual elaborated type");
                let value = definition
                    .elaborated_value
                    .as_ref()
                    .expect("actual elaborated value");
                assert!(!definition.is_axiom, "{root}");
                assert_ne!(constant.kind, ConstantKind::Axiom, "{root}");
                assert_eq!(
                    &constant.type_, ty,
                    "{root}: kernel/metadata type agreement"
                );
                assert_eq!(
                    constant.value.as_ref(),
                    Some(value),
                    "{root}: kernel/metadata value agreement"
                );
                assert!(
                    !matches!(value.kind(), ExprKind::Const(found, _) if found == &name),
                    "{root}: not a self-constant proof"
                );
                spec.verify_definition(root)
                    .expect("actual body checks against actual stored type");
                assert!(
                    spec.env()
                        .axiom_deps(&name)
                        .expect("actual domain-closure root exists")
                        .is_empty(),
                    "{root}: domain axioms"
                );
                assert!(
                    spec.env()
                        .foundational_axiom_deps(&name)
                        .expect("actual foundational-closure root exists")
                        .is_empty(),
                    "{root}: foundational axioms"
                );
                assert!(
                    crate::spec_axiom_closure::computed_axiom_closure(&spec, root).is_empty(),
                    "{root}"
                );
            }
            for registration in REGISTRATIONS {
                if let Registration::Proof {
                    name,
                    type_src,
                    value_src,
                    ..
                } = registration
                {
                    let definition = spec.definitions().get(*name).expect("actual proof record");
                    assert_eq!(definition.category, AxiomCategory::DerivedLemma, "{name}");
                    assert_eq!(
                        definition.proof_status,
                        ProofStatus::DerivedProved,
                        "{name}"
                    );
                    assert_eq!(
                        definition.type_src, *type_src,
                        "{name}: exact registered type source"
                    );
                    assert_eq!(
                        definition.value_src.as_deref(),
                        Some(*value_src),
                        "{name}: exact registered body source"
                    );
                }
            }
            for root in REUSED_PROOFS {
                let helper = spec
                    .definitions()
                    .get(*root)
                    .expect("existing checked helper");
                assert_eq!(helper.category, AxiomCategory::DerivedLemma);
                assert_eq!(helper.proof_status, ProofStatus::DerivedProved);
            }
        });
    }

    #[test]
    fn reflected_nat_general_real_generic_and_nonzero_callers_check() {
        run_with_stack(|| {
            let spec = build_spec_with_stack();
            for (value_src, type_src) in [
                ("rfnzg_source_general_input_typed (Level.succ Level.zero) rfnz_motive rfnz_zero rfnz_minor rfnzg_source_motive_argument_typed rfnzg_source_zero_argument_typed rfnzg_source_minor_argument_typed",
                 "TypingCtxConvIn kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) rfnz_input (KExpr.app rfnz_motive rfnz_zero)"),
                ("rfnzg_source_general_raw_result_typed (Level.succ Level.zero) rfnz_motive rfnz_zero rfnz_minor rfnzg_source_motive_argument_typed rfnzg_source_zero_argument_typed rfnzg_source_minor_argument_typed",
                 "TypingCtxConvIn kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) rfnz_raw_result (KExpr.app rfnz_motive rfnz_zero)"),
                ("rfnzg_source_general_guarded_step (Level.succ Level.zero) rfnz_motive rfnz_zero rfnz_minor",
                 "iota_step (red_rec kernel_core_red_env) rfnz_input rfnz_raw_result"),
                ("rfnzg_source_nonzero_raw_result_nat",
                 "TypingCtxConvIn kernel_core_red_env kcre_nat_tenv (@ListType.nil KExpr) rfnz_raw_result rfnz_nat"),
            ] {
                let value = spec.elaborate_source(value_src, "actual general zero caller").expect("caller elaborates");
                let expected = spec.elaborate_source(type_src, "actual general zero caller type").expect("caller type elaborates");
                let checker = TypeChecker::with_mode(spec.env(), spec.env().mode());
                let inferred = checker.infer_type(&value).expect("actual generic caller checks");
                assert!(checker.is_def_eq(&inferred, &expected), "{value_src}");
            }
        });
    }

    #[test]
    fn reflected_nat_general_rejects_forged_parameter_input_guarded_and_output_claims() {
        run_with_stack(|| {
            let mut spec = build_spec_with_stack();
            for refusal in REFUSALS {
                parse_check(&format!(
                    "def {} : {} := {}",
                    refusal.name, refusal.type_src, refusal.value_src
                ))
                .expect("forged theorem is well parsed");
                let error = spec
                    .add_definition(checked_definition(
                        refusal.name,
                        refusal.type_src,
                        refusal.value_src,
                        "Deliberately invalid reflected Nat.zero proof; must be rejected.",
                    ))
                    .expect_err(
                        "forged type, universe, arity, or immediate raw result must be refused",
                    );
                let message = match &error {
                    crate::spec::error::SpecError::ElabError(message)
                    | crate::spec::error::SpecError::TypeError(message) => message,
                    other => panic!("expected a type refusal, not {other:?}"),
                };
                let diagnostic = message.to_ascii_lowercase();
                assert!(diagnostic.contains("type mismatch"), "{error:?}");
                assert!(
                    !diagnostic.contains("unknown identifier")
                        && !diagnostic.contains("unknown constant")
                        && !diagnostic.contains("unknown name"),
                    "missing names do not count as a type refusal: {error:?}"
                );
                assert!(
                    !spec.definitions().contains_key(refusal.name),
                    "{}: rejected proof record absent",
                    refusal.name
                );
                assert!(
                    spec.env()
                        .get_const(&Name::from_string(refusal.name))
                        .is_none(),
                    "{}: rejected kernel root absent",
                    refusal.name
                );
            }
        });
    }
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! General typed-argument composition for the synthetic Nat.zero branch.
//!
//! The actual three-argument RHS and four-argument input telescopes are built
//! from real motive/minor typings. Lift/substitution cancellation needs no
//! closedness assumption, even for loose-BVar motives. The final fixed-Nat,
//! empty-context results independently prove input typing, the guarded raw
//! iota step, and raw-output typing at arbitrary supplied universes.
//!
//! No coherence, candidate model, output-typing oracle, or subject-reduction
//! premise is used. This is not reflected-source admission, general iota
//! preservation, another recursor branch, extra-argument preservation, or Rust
//! refinement. Exact independent source evidence is recorded in
//! scratch/self-verification-nat-zero-general-spine-2026-09-09.md.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

// Byte-identical logical prototypes from the independently checked scratch unit.
// Proof records below make the same binders explicit; data stays unfoldable.
const DECLARATIONS: &[(&str, &str)] = &[
    (r"def nz_zero_args (m : KExpr) (z : KExpr) (s : KExpr) : ListType KExpr :=
 (ListType.cons KExpr m (ListType.cons KExpr z (ListType.cons KExpr s (ListType.nil KExpr))))", "Actual raw telescope or argument-list data for the synthetic Nat.zero composition."),

    (r"def nz_zero_rule_tail : KExpr :=
 (KExpr.pi (KExpr.app (KExpr.bvar Nat.zero) natZeroC) (KExpr.pi natRecSArm (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) natZeroC)))", "Actual raw telescope or argument-list data for the synthetic Nat.zero composition."),

    (r"def nz_zero_sarm_after_m (m : KExpr) : KExpr :=
 (KExpr.pi natTypeC (KExpr.pi (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.app natSuccC (KExpr.bvar (Nat.succ Nat.zero))))))", "Actual raw telescope or argument-list data for the synthetic Nat.zero composition."),

    (r"def nz_zero_tail_after_m (m : KExpr) : KExpr :=
 (KExpr.pi (KExpr.app m natZeroC) (KExpr.pi (nz_zero_sarm_after_m m) (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) natZeroC)))", "Actual raw telescope or argument-list data for the synthetic Nat.zero composition."),

    (r"def nz_zero_after_m_eq (m : KExpr) : Eq KExpr (instantiate nz_zero_rule_tail m) (nz_zero_tail_after_m m) :=
 (Eq.cong KExpr KExpr (fun (x : KExpr) => (KExpr.pi (KExpr.app x natZeroC) (KExpr.pi (nz_zero_sarm_after_m m) (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) natZeroC)))) (lift_at m Nat.zero Nat.zero) m (lift_zero_identity m))", "Checked telescope equality or concrete nonzero-universe caller of the generic Nat.zero composition."),

    (r"def nz_zero_sarm_after_z_eq (m : KExpr) (z : KExpr) : Eq KExpr (instantiate (nz_zero_sarm_after_m m) z) (natSuccCaseSem m) :=
 (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.pi natTypeC x) (KExpr.pi (KExpr.app (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) z (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) (KExpr.app (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) z (Nat.succ (Nat.succ Nat.zero))) (KExpr.app natSuccC (KExpr.bvar (Nat.succ Nat.zero))))) (KExpr.pi (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (KExpr.app natSuccC (KExpr.bvar (Nat.succ Nat.zero))))) (universe_bridge_congr2 KExpr KExpr KExpr (fun (A : KExpr) (B : KExpr) => KExpr.pi A B) (KExpr.app (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) z (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) (KExpr.app (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) z (Nat.succ (Nat.succ Nat.zero))) (KExpr.app natSuccC (KExpr.bvar (Nat.succ Nat.zero)))) (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (KExpr.app natSuccC (KExpr.bvar (Nat.succ Nat.zero)))) (Eq.cong KExpr KExpr (fun (x : KExpr) => (KExpr.app x (KExpr.bvar Nat.zero))) (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) z (Nat.succ Nat.zero)) (lift_at m Nat.zero (Nat.succ Nat.zero)) (inst_at1_lift2 m z)) (Eq.cong KExpr KExpr (fun (x : KExpr) => (KExpr.app x (KExpr.app natSuccC (KExpr.bvar (Nat.succ Nat.zero))))) (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) z (Nat.succ (Nat.succ Nat.zero))) (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (instantiate_lift_cancel_general m z Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero))) (Nat.succ (Nat.succ Nat.zero)) (Eq.refl Nat (Nat.succ Nat.zero))))))", "Checked telescope equality or concrete nonzero-universe caller of the generic Nat.zero composition."),

    (r"def nz_zero_after_z_eq (m : KExpr) (z : KExpr) : Eq KExpr (instantiate (KExpr.pi (nz_zero_sarm_after_m m) (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) natZeroC)) z) (KExpr.pi (natSuccCaseSem m) (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) natZeroC)) :=
 (universe_bridge_congr2 KExpr KExpr KExpr (fun (A : KExpr) (B : KExpr) => KExpr.pi A B) (instantiate (nz_zero_sarm_after_m m) z) (natSuccCaseSem m) (KExpr.app (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) z (Nat.succ Nat.zero)) natZeroC) (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) natZeroC) (nz_zero_sarm_after_z_eq m z) (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.app x natZeroC) (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) z (Nat.succ Nat.zero)) (lift_at m Nat.zero (Nat.succ Nat.zero)) (inst_at1_lift2 m z)))", "Checked telescope equality or concrete nonzero-universe caller of the generic Nat.zero composition."),

    (r"def nz_zero_after_s_eq (m : KExpr) (s : KExpr) : Eq KExpr (instantiate (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) natZeroC) s) (KExpr.app m natZeroC) :=
 (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.app x natZeroC) (instantiate (lift_at m Nat.zero (Nat.succ Nat.zero)) s) m (inst_lift1 m s))", "Checked telescope equality or concrete nonzero-universe caller of the generic Nat.zero composition."),

    (r"def nz_zero_typed_spine (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr) (u : Level) (m : KExpr) (z : KExpr) (s : KExpr)
 (hm : TypingCtxConvIn R tenv G m (natMotiveTy u))
 (hz : TypingCtxConvIn R tenv G z (KExpr.app m natZeroC))
 (hs : TypingCtxConvIn R tenv G s (natSuccCaseSem m)) : TypedRawPiSpine R tenv G (nz_rule_type u) (nz_zero_args m z s) (KExpr.app m natZeroC) :=
 TypedRawPiSpine.cons R tenv G (natMotiveTy u) nz_zero_rule_tail m (ListType.cons KExpr z (ListType.cons KExpr s (ListType.nil KExpr))) (KExpr.app m natZeroC) hm (Eq.substType KExpr (fun (F : KExpr) => TypedRawPiSpine R tenv G F (ListType.cons KExpr z (ListType.cons KExpr s (ListType.nil KExpr))) (KExpr.app m natZeroC)) (nz_zero_tail_after_m m) (instantiate nz_zero_rule_tail m) (Eq.symm KExpr (instantiate nz_zero_rule_tail m) (nz_zero_tail_after_m m) (nz_zero_after_m_eq m)) (TypedRawPiSpine.cons R tenv G (KExpr.app m natZeroC) (KExpr.pi (nz_zero_sarm_after_m m) (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) natZeroC)) z (ListType.cons KExpr s (ListType.nil KExpr)) (KExpr.app m natZeroC) hz (Eq.substType KExpr (fun (F : KExpr) => TypedRawPiSpine R tenv G F (ListType.cons KExpr s (ListType.nil KExpr)) (KExpr.app m natZeroC)) (KExpr.pi (natSuccCaseSem m) (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) natZeroC)) (instantiate (KExpr.pi (nz_zero_sarm_after_m m) (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) natZeroC)) z) (Eq.symm KExpr (instantiate (KExpr.pi (nz_zero_sarm_after_m m) (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) natZeroC)) z) (KExpr.pi (natSuccCaseSem m) (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) natZeroC)) (nz_zero_after_z_eq m z)) (TypedRawPiSpine.cons R tenv G (natSuccCaseSem m) (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) natZeroC) s (ListType.nil KExpr) (KExpr.app m natZeroC) hs (Eq.substType KExpr (fun (F : KExpr) => TypedRawPiSpine R tenv G F (ListType.nil KExpr) (KExpr.app m natZeroC)) (KExpr.app m natZeroC) (instantiate (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) natZeroC) s) (Eq.symm KExpr (instantiate (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) natZeroC) s) (KExpr.app m natZeroC) (nz_zero_after_s_eq m s)) (TypedRawPiSpine.nil R tenv G (KExpr.app m natZeroC)))))))", "Actual three-binder RHS telescope from the motive and two minor typings, without closedness premises."),

    (r"def nz_general_raw_result_typed (R : RedEnv) (u : Level) (m : KExpr) (z : KExpr) (s : KExpr)
 (hm : TypingCtxConvIn R (natTEnv Level.zero) (ListType.nil KExpr) m (natMotiveTy u))
 (hz : TypingCtxConvIn R (natTEnv Level.zero) (ListType.nil KExpr) z (KExpr.app m natZeroC))
 (hs : TypingCtxConvIn R (natTEnv Level.zero) (ListType.nil KExpr) s (natSuccCaseSem m)) : TypingCtxConvIn R (natTEnv Level.zero) (ListType.nil KExpr) (KExpr.app (KExpr.app (KExpr.app (natRecRhsZero u) m) z) s) (KExpr.app m natZeroC) :=
 typed_raw_pi_spine_apply R (natTEnv Level.zero) (ListType.nil KExpr) (nz_rule_type u) (nz_zero_args m z s) (KExpr.app m natZeroC)
  (nz_zero_typed_spine R (natTEnv Level.zero) (ListType.nil KExpr) u m z s hm hz hs) (natRecRhsZero u)
  (nz_typing_to_semantic R (natTEnv Level.zero) (ListType.nil KExpr) (natRecRhsZero u) (nz_rule_type u) (nz_rhs_typed u))", "Raw Nat.zero RHS application typing from the proved schematic RHS and actual typed spine; no output oracle."),

    (r"def nz_general_guarded_step (u : Level) (m : KExpr) (z : KExpr) (s : KExpr) : iota_step (red_rec nz_env) (natRecApp u m z s natZeroC) (KExpr.app (KExpr.app (KExpr.app (natRecRhsZero u) m) z) s) :=
 natREnv_iota_zero u m z s", "Actual guarded synthetic Nat.zero iota step at arbitrary supplied universe and raw arguments."),

    (r"def nz_general_guarded_result_typed (u : Level) (m : KExpr) (z : KExpr) (s : KExpr)
 (hm : TypingCtxConvIn nz_env (natTEnv Level.zero) (ListType.nil KExpr) m (natMotiveTy u))
 (hz : TypingCtxConvIn nz_env (natTEnv Level.zero) (ListType.nil KExpr) z (KExpr.app m natZeroC))
 (hs : TypingCtxConvIn nz_env (natTEnv Level.zero) (ListType.nil KExpr) s (natSuccCaseSem m)) : TypingCtxConvIn nz_env (natTEnv Level.zero) (ListType.nil KExpr) (KExpr.app (KExpr.app (KExpr.app (natRecRhsZero u) m) z) s) (KExpr.app m natZeroC) :=
 nz_general_raw_result_typed nz_env u m z s hm hz hs", "Raw result typing for the actual synthetic Nat.zero guarded environment."),

    (r"def nz_general_nonzero_caller :
 TypingCtxConvIn nz_env (natTEnv Level.zero) (ListType.nil KExpr)
 nz_raw_result (KExpr.app nz_motive natZeroC) :=
 nz_general_guarded_result_typed (Level.succ Level.zero) nz_motive natZeroC nz_minor
 nz_motive_argument_typed nz_zero_argument_typed nz_minor_argument_typed", "Checked telescope equality or concrete nonzero-universe caller of the generic Nat.zero composition."),

    (r"def nz_general_nonzero_caller_nat :
 TypingCtxConvIn nz_env (natTEnv Level.zero) (ListType.nil KExpr) nz_raw_result natTypeC :=
 TypingCtxConvIn.conv nz_env (natTEnv Level.zero) (ListType.nil KExpr)
 nz_raw_result (KExpr.app nz_motive natZeroC) natTypeC
 nz_general_nonzero_caller (nz_motive_beta natZeroC)", "Checked telescope equality or concrete nonzero-universe caller of the generic Nat.zero composition."),

    (r"def nz_general_nonzero_step : iota_step (red_rec nz_env) nz_input nz_raw_result :=
 nz_general_guarded_step (Level.succ Level.zero) nz_motive natZeroC nz_minor", "Checked telescope equality or concrete nonzero-universe caller of the generic Nat.zero composition."),

    (r"def nz_zero_spine_open_motive_control :
 Eq KExpr (instantiate (nz_zero_sarm_after_m (KExpr.bvar Nat.zero))
   (KExpr.bvar (Nat.succ Nat.zero))) (natSuccCaseSem (KExpr.bvar Nat.zero)) :=
 nz_zero_sarm_after_z_eq (KExpr.bvar Nat.zero) (KExpr.bvar (Nat.succ Nat.zero))", "Actual loose-BVar motive cancellation control; no assertion that this motive is typed in the empty context."),

    (r"def nz_zero_input_args (m : KExpr) (z : KExpr) (s : KExpr) : ListType KExpr :=
 (ListType.cons KExpr m (ListType.cons KExpr z (ListType.cons KExpr s (ListType.cons KExpr natZeroC (ListType.nil KExpr)))))", "Actual raw telescope or argument-list data for the synthetic Nat.zero composition."),

    (r"def nz_zero_input_tail : KExpr :=
 (KExpr.pi (KExpr.app (KExpr.bvar Nat.zero) natZeroC) (KExpr.pi natRecSArm (KExpr.pi natTypeC (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar Nat.zero)))))", "Actual raw telescope or argument-list data for the synthetic Nat.zero composition."),

    (r"def nz_zero_input_after_m (m : KExpr) : KExpr :=
 (KExpr.pi (KExpr.app m natZeroC) (KExpr.pi (nz_zero_sarm_after_m m) (KExpr.pi natTypeC (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar Nat.zero)))))", "Actual raw telescope or argument-list data for the synthetic Nat.zero composition."),

    (r"def nz_zero_input_after_m_eq (m : KExpr) : Eq KExpr (instantiate nz_zero_input_tail m) (nz_zero_input_after_m m) :=
 (Eq.cong KExpr KExpr (fun (x : KExpr) => (KExpr.pi (KExpr.app x natZeroC) (KExpr.pi (nz_zero_sarm_after_m m) (KExpr.pi natTypeC (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar Nat.zero)))))) (lift_at m Nat.zero Nat.zero) m (lift_zero_identity m))", "Checked telescope equality or concrete nonzero-universe caller of the generic Nat.zero composition."),

    (r"def nz_zero_input_after_z_eq (m : KExpr) (z : KExpr) : Eq KExpr (instantiate (KExpr.pi (nz_zero_sarm_after_m m) (KExpr.pi natTypeC (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar Nat.zero)))) z) (KExpr.pi (natSuccCaseSem m) (KExpr.pi natTypeC (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)))) :=
 (universe_bridge_congr2 KExpr KExpr KExpr (fun (A : KExpr) (B : KExpr) => KExpr.pi A B) (instantiate (nz_zero_sarm_after_m m) z) (natSuccCaseSem m) (KExpr.pi natTypeC (KExpr.app (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) z (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero))) (KExpr.pi natTypeC (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero))) (nz_zero_sarm_after_z_eq m z) (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.pi natTypeC x) (KExpr.app (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) z (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (Eq.cong KExpr KExpr (fun (x : KExpr) => (KExpr.app x (KExpr.bvar Nat.zero))) (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) z (Nat.succ (Nat.succ Nat.zero))) (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (instantiate_lift_cancel_general m z Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero))) (Nat.succ (Nat.succ Nat.zero)) (Eq.refl Nat (Nat.succ Nat.zero))))))", "Checked telescope equality or concrete nonzero-universe caller of the generic Nat.zero composition."),

    (r"def nz_zero_input_after_s_eq (m : KExpr) (s : KExpr) : Eq KExpr (instantiate (KExpr.pi natTypeC (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero))) s) (KExpr.pi natTypeC (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero))) :=
 (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.pi natTypeC x) (KExpr.app (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) s (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) (Eq.cong KExpr KExpr (fun (x : KExpr) => (KExpr.app x (KExpr.bvar Nat.zero))) (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) s (Nat.succ Nat.zero)) (lift_at m Nat.zero (Nat.succ Nat.zero)) (inst_at1_lift2 m s)))", "Checked telescope equality or concrete nonzero-universe caller of the generic Nat.zero composition."),

    (r"def nz_zero_input_after_major_eq (m : KExpr) : Eq KExpr (instantiate (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) natZeroC) (KExpr.app m natZeroC) :=
 (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.app x natZeroC) (instantiate (lift_at m Nat.zero (Nat.succ Nat.zero)) natZeroC) m (inst_lift1 m natZeroC))", "Checked telescope equality or concrete nonzero-universe caller of the generic Nat.zero composition."),

    (r"def nz_zero_input_typed_spine (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr) (u : Level) (m : KExpr) (z : KExpr) (s : KExpr)
 (hm : TypingCtxConvIn R tenv G m (natMotiveTy u))
 (hz : TypingCtxConvIn R tenv G z (KExpr.app m natZeroC))
 (hs : TypingCtxConvIn R tenv G s (natSuccCaseSem m))
 (hzero : TypingCtxConvIn R tenv G natZeroC natTypeC) : TypedRawPiSpine R tenv G (natRecTy u) (nz_zero_input_args m z s) (KExpr.app m natZeroC) :=
 TypedRawPiSpine.cons R tenv G (natMotiveTy u) nz_zero_input_tail m (ListType.cons KExpr z (ListType.cons KExpr s (ListType.cons KExpr natZeroC (ListType.nil KExpr)))) (KExpr.app m natZeroC) hm (Eq.substType KExpr (fun (F : KExpr) => TypedRawPiSpine R tenv G F (ListType.cons KExpr z (ListType.cons KExpr s (ListType.cons KExpr natZeroC (ListType.nil KExpr)))) (KExpr.app m natZeroC)) (nz_zero_input_after_m m) (instantiate nz_zero_input_tail m) (Eq.symm KExpr (instantiate nz_zero_input_tail m) (nz_zero_input_after_m m) (nz_zero_input_after_m_eq m)) (TypedRawPiSpine.cons R tenv G (KExpr.app m natZeroC) (KExpr.pi (nz_zero_sarm_after_m m) (KExpr.pi natTypeC (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar Nat.zero)))) z (ListType.cons KExpr s (ListType.cons KExpr natZeroC (ListType.nil KExpr))) (KExpr.app m natZeroC) hz (Eq.substType KExpr (fun (F : KExpr) => TypedRawPiSpine R tenv G F (ListType.cons KExpr s (ListType.cons KExpr natZeroC (ListType.nil KExpr))) (KExpr.app m natZeroC)) (KExpr.pi (natSuccCaseSem m) (KExpr.pi natTypeC (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)))) (instantiate (KExpr.pi (nz_zero_sarm_after_m m) (KExpr.pi natTypeC (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar Nat.zero)))) z) (Eq.symm KExpr (instantiate (KExpr.pi (nz_zero_sarm_after_m m) (KExpr.pi natTypeC (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar Nat.zero)))) z) (KExpr.pi (natSuccCaseSem m) (KExpr.pi natTypeC (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)))) (nz_zero_input_after_z_eq m z)) (TypedRawPiSpine.cons R tenv G (natSuccCaseSem m) (KExpr.pi natTypeC (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero))) s (ListType.cons KExpr natZeroC (ListType.nil KExpr)) (KExpr.app m natZeroC) hs (Eq.substType KExpr (fun (F : KExpr) => TypedRawPiSpine R tenv G F (ListType.cons KExpr natZeroC (ListType.nil KExpr)) (KExpr.app m natZeroC)) (KExpr.pi natTypeC (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero))) (instantiate (KExpr.pi natTypeC (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero))) s) (Eq.symm KExpr (instantiate (KExpr.pi natTypeC (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero))) s) (KExpr.pi natTypeC (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero))) (nz_zero_input_after_s_eq m s)) (TypedRawPiSpine.cons R tenv G natTypeC (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) natZeroC (ListType.nil KExpr) (KExpr.app m natZeroC) hzero (Eq.substType KExpr (fun (F : KExpr) => TypedRawPiSpine R tenv G F (ListType.nil KExpr) (KExpr.app m natZeroC)) (KExpr.app m natZeroC) (instantiate (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) natZeroC) (Eq.symm KExpr (instantiate (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) natZeroC) (KExpr.app m natZeroC) (nz_zero_input_after_major_eq m)) (TypedRawPiSpine.nil R tenv G (KExpr.app m natZeroC)))))))))", "Actual four-argument Nat recursor telescope, including genuine zero-major typing."),

    (r"def nz_general_input_typed (R : RedEnv) (u : Level) (m : KExpr) (z : KExpr) (s : KExpr)
 (hm : TypingCtxConvIn R (natTEnv Level.zero) (ListType.nil KExpr) m (natMotiveTy u))
 (hz : TypingCtxConvIn R (natTEnv Level.zero) (ListType.nil KExpr) z (KExpr.app m natZeroC))
 (hs : TypingCtxConvIn R (natTEnv Level.zero) (ListType.nil KExpr) s (natSuccCaseSem m)) : TypingCtxConvIn R (natTEnv Level.zero) (ListType.nil KExpr) (natRecApp u m z s natZeroC) (KExpr.app m natZeroC) :=
 typed_raw_pi_spine_const_apply R (natTEnv Level.zero) (ListType.nil KExpr) recName
 (ListType.cons Level u (ListType.nil Level)) (natRecTy u)
 (nz_zero_input_args m z s) (KExpr.app m natZeroC) (natTEnv_rec_lookup u)
 (nz_zero_input_typed_spine R (natTEnv Level.zero) (ListType.nil KExpr) u m z s hm hz hs
  (nz_typing_to_semantic R (natTEnv Level.zero) (ListType.nil KExpr) natZeroC natTypeC (nz_zero_typed (ListType.nil KExpr))))", "Whole synthetic Nat.zero input typing from actual three argument typings and guarded recursor lookup."),

    (r"def nz_general_nonzero_input : TypingCtxConvIn nz_env (natTEnv Level.zero) (ListType.nil KExpr) nz_input (KExpr.app nz_motive natZeroC) :=
 nz_general_input_typed nz_env (Level.succ Level.zero) nz_motive natZeroC nz_minor nz_motive_argument_typed nz_zero_argument_typed nz_minor_argument_typed", "Checked telescope equality or concrete nonzero-universe caller of the generic Nat.zero composition."),
];

// These are static registrations, not a runtime parser or post-hoc status edit.
// The ordinary checked add_definition path checks each real proof body/type.
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
        name: "nz_zero_args",
    },
    Registration::Data {
        declaration_index: 1,
        name: "nz_zero_rule_tail",
    },
    Registration::Data {
        declaration_index: 2,
        name: "nz_zero_sarm_after_m",
    },
    Registration::Data {
        declaration_index: 3,
        name: "nz_zero_tail_after_m",
    },
    Registration::Proof {
        declaration_index: 4,
        name: "nz_zero_after_m_eq",
        type_src: r"forall (m : KExpr),
 Eq KExpr (instantiate nz_zero_rule_tail m) (nz_zero_tail_after_m m)",
        value_src: r"fun (m : KExpr) =>
 (Eq.cong KExpr KExpr (fun (x : KExpr) => (KExpr.pi (KExpr.app x natZeroC) (KExpr.pi (nz_zero_sarm_after_m m) (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) natZeroC)))) (lift_at m Nat.zero Nat.zero) m (lift_zero_identity m))",
    },
    Registration::Proof {
        declaration_index: 5,
        name: "nz_zero_sarm_after_z_eq",
        type_src: r"forall (m : KExpr) (z : KExpr),
 Eq KExpr (instantiate (nz_zero_sarm_after_m m) z) (natSuccCaseSem m)",
        value_src: r"fun (m : KExpr) (z : KExpr) =>
 (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.pi natTypeC x) (KExpr.pi (KExpr.app (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) z (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) (KExpr.app (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) z (Nat.succ (Nat.succ Nat.zero))) (KExpr.app natSuccC (KExpr.bvar (Nat.succ Nat.zero))))) (KExpr.pi (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (KExpr.app natSuccC (KExpr.bvar (Nat.succ Nat.zero))))) (universe_bridge_congr2 KExpr KExpr KExpr (fun (A : KExpr) (B : KExpr) => KExpr.pi A B) (KExpr.app (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) z (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) (KExpr.app (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) z (Nat.succ (Nat.succ Nat.zero))) (KExpr.app natSuccC (KExpr.bvar (Nat.succ Nat.zero)))) (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (KExpr.app natSuccC (KExpr.bvar (Nat.succ Nat.zero)))) (Eq.cong KExpr KExpr (fun (x : KExpr) => (KExpr.app x (KExpr.bvar Nat.zero))) (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) z (Nat.succ Nat.zero)) (lift_at m Nat.zero (Nat.succ Nat.zero)) (inst_at1_lift2 m z)) (Eq.cong KExpr KExpr (fun (x : KExpr) => (KExpr.app x (KExpr.app natSuccC (KExpr.bvar (Nat.succ Nat.zero))))) (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) z (Nat.succ (Nat.succ Nat.zero))) (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (instantiate_lift_cancel_general m z Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero))) (Nat.succ (Nat.succ Nat.zero)) (Eq.refl Nat (Nat.succ Nat.zero))))))",
    },
    Registration::Proof {
        declaration_index: 6,
        name: "nz_zero_after_z_eq",
        type_src: r"forall (m : KExpr) (z : KExpr),
 Eq KExpr (instantiate (KExpr.pi (nz_zero_sarm_after_m m) (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) natZeroC)) z) (KExpr.pi (natSuccCaseSem m) (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) natZeroC))",
        value_src: r"fun (m : KExpr) (z : KExpr) =>
 (universe_bridge_congr2 KExpr KExpr KExpr (fun (A : KExpr) (B : KExpr) => KExpr.pi A B) (instantiate (nz_zero_sarm_after_m m) z) (natSuccCaseSem m) (KExpr.app (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) z (Nat.succ Nat.zero)) natZeroC) (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) natZeroC) (nz_zero_sarm_after_z_eq m z) (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.app x natZeroC) (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) z (Nat.succ Nat.zero)) (lift_at m Nat.zero (Nat.succ Nat.zero)) (inst_at1_lift2 m z)))",
    },
    Registration::Proof {
        declaration_index: 7,
        name: "nz_zero_after_s_eq",
        type_src: r"forall (m : KExpr) (s : KExpr),
 Eq KExpr (instantiate (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) natZeroC) s) (KExpr.app m natZeroC)",
        value_src: r"fun (m : KExpr) (s : KExpr) =>
 (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.app x natZeroC) (instantiate (lift_at m Nat.zero (Nat.succ Nat.zero)) s) m (inst_lift1 m s))",
    },
    Registration::Proof {
        declaration_index: 8,
        name: "nz_zero_typed_spine",
        type_src: r"forall (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr) (u : Level) (m : KExpr) (z : KExpr) (s : KExpr)
 (hm : TypingCtxConvIn R tenv G m (natMotiveTy u))
 (hz : TypingCtxConvIn R tenv G z (KExpr.app m natZeroC))
 (hs : TypingCtxConvIn R tenv G s (natSuccCaseSem m)),
 TypedRawPiSpine R tenv G (nz_rule_type u) (nz_zero_args m z s) (KExpr.app m natZeroC)",
        value_src: r"fun (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr) (u : Level) (m : KExpr) (z : KExpr) (s : KExpr)
 (hm : TypingCtxConvIn R tenv G m (natMotiveTy u))
 (hz : TypingCtxConvIn R tenv G z (KExpr.app m natZeroC))
 (hs : TypingCtxConvIn R tenv G s (natSuccCaseSem m)) =>
 TypedRawPiSpine.cons R tenv G (natMotiveTy u) nz_zero_rule_tail m (ListType.cons KExpr z (ListType.cons KExpr s (ListType.nil KExpr))) (KExpr.app m natZeroC) hm (Eq.substType KExpr (fun (F : KExpr) => TypedRawPiSpine R tenv G F (ListType.cons KExpr z (ListType.cons KExpr s (ListType.nil KExpr))) (KExpr.app m natZeroC)) (nz_zero_tail_after_m m) (instantiate nz_zero_rule_tail m) (Eq.symm KExpr (instantiate nz_zero_rule_tail m) (nz_zero_tail_after_m m) (nz_zero_after_m_eq m)) (TypedRawPiSpine.cons R tenv G (KExpr.app m natZeroC) (KExpr.pi (nz_zero_sarm_after_m m) (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) natZeroC)) z (ListType.cons KExpr s (ListType.nil KExpr)) (KExpr.app m natZeroC) hz (Eq.substType KExpr (fun (F : KExpr) => TypedRawPiSpine R tenv G F (ListType.cons KExpr s (ListType.nil KExpr)) (KExpr.app m natZeroC)) (KExpr.pi (natSuccCaseSem m) (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) natZeroC)) (instantiate (KExpr.pi (nz_zero_sarm_after_m m) (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) natZeroC)) z) (Eq.symm KExpr (instantiate (KExpr.pi (nz_zero_sarm_after_m m) (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) natZeroC)) z) (KExpr.pi (natSuccCaseSem m) (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) natZeroC)) (nz_zero_after_z_eq m z)) (TypedRawPiSpine.cons R tenv G (natSuccCaseSem m) (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) natZeroC) s (ListType.nil KExpr) (KExpr.app m natZeroC) hs (Eq.substType KExpr (fun (F : KExpr) => TypedRawPiSpine R tenv G F (ListType.nil KExpr) (KExpr.app m natZeroC)) (KExpr.app m natZeroC) (instantiate (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) natZeroC) s) (Eq.symm KExpr (instantiate (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) natZeroC) s) (KExpr.app m natZeroC) (nz_zero_after_s_eq m s)) (TypedRawPiSpine.nil R tenv G (KExpr.app m natZeroC)))))))",
    },
    Registration::Proof {
        declaration_index: 9,
        name: "nz_general_raw_result_typed",
        type_src: r"forall (R : RedEnv) (u : Level) (m : KExpr) (z : KExpr) (s : KExpr)
 (hm : TypingCtxConvIn R (natTEnv Level.zero) (ListType.nil KExpr) m (natMotiveTy u))
 (hz : TypingCtxConvIn R (natTEnv Level.zero) (ListType.nil KExpr) z (KExpr.app m natZeroC))
 (hs : TypingCtxConvIn R (natTEnv Level.zero) (ListType.nil KExpr) s (natSuccCaseSem m)),
 TypingCtxConvIn R (natTEnv Level.zero) (ListType.nil KExpr) (KExpr.app (KExpr.app (KExpr.app (natRecRhsZero u) m) z) s) (KExpr.app m natZeroC)",
        value_src: r"fun (R : RedEnv) (u : Level) (m : KExpr) (z : KExpr) (s : KExpr)
 (hm : TypingCtxConvIn R (natTEnv Level.zero) (ListType.nil KExpr) m (natMotiveTy u))
 (hz : TypingCtxConvIn R (natTEnv Level.zero) (ListType.nil KExpr) z (KExpr.app m natZeroC))
 (hs : TypingCtxConvIn R (natTEnv Level.zero) (ListType.nil KExpr) s (natSuccCaseSem m)) =>
 typed_raw_pi_spine_apply R (natTEnv Level.zero) (ListType.nil KExpr) (nz_rule_type u) (nz_zero_args m z s) (KExpr.app m natZeroC)
  (nz_zero_typed_spine R (natTEnv Level.zero) (ListType.nil KExpr) u m z s hm hz hs) (natRecRhsZero u)
  (nz_typing_to_semantic R (natTEnv Level.zero) (ListType.nil KExpr) (natRecRhsZero u) (nz_rule_type u) (nz_rhs_typed u))",
    },
    Registration::Proof {
        declaration_index: 10,
        name: "nz_general_guarded_step",
        type_src: r"forall (u : Level) (m : KExpr) (z : KExpr) (s : KExpr),
 iota_step (red_rec nz_env) (natRecApp u m z s natZeroC) (KExpr.app (KExpr.app (KExpr.app (natRecRhsZero u) m) z) s)",
        value_src: r"fun (u : Level) (m : KExpr) (z : KExpr) (s : KExpr) =>
 natREnv_iota_zero u m z s",
    },
    Registration::Proof {
        declaration_index: 11,
        name: "nz_general_guarded_result_typed",
        type_src: r"forall (u : Level) (m : KExpr) (z : KExpr) (s : KExpr)
 (hm : TypingCtxConvIn nz_env (natTEnv Level.zero) (ListType.nil KExpr) m (natMotiveTy u))
 (hz : TypingCtxConvIn nz_env (natTEnv Level.zero) (ListType.nil KExpr) z (KExpr.app m natZeroC))
 (hs : TypingCtxConvIn nz_env (natTEnv Level.zero) (ListType.nil KExpr) s (natSuccCaseSem m)),
 TypingCtxConvIn nz_env (natTEnv Level.zero) (ListType.nil KExpr) (KExpr.app (KExpr.app (KExpr.app (natRecRhsZero u) m) z) s) (KExpr.app m natZeroC)",
        value_src: r"fun (u : Level) (m : KExpr) (z : KExpr) (s : KExpr)
 (hm : TypingCtxConvIn nz_env (natTEnv Level.zero) (ListType.nil KExpr) m (natMotiveTy u))
 (hz : TypingCtxConvIn nz_env (natTEnv Level.zero) (ListType.nil KExpr) z (KExpr.app m natZeroC))
 (hs : TypingCtxConvIn nz_env (natTEnv Level.zero) (ListType.nil KExpr) s (natSuccCaseSem m)) =>
 nz_general_raw_result_typed nz_env u m z s hm hz hs",
    },
    Registration::Proof {
        declaration_index: 12,
        name: "nz_general_nonzero_caller",
        type_src: r"TypingCtxConvIn nz_env (natTEnv Level.zero) (ListType.nil KExpr)
 nz_raw_result (KExpr.app nz_motive natZeroC)",
        value_src: r"nz_general_guarded_result_typed (Level.succ Level.zero) nz_motive natZeroC nz_minor
 nz_motive_argument_typed nz_zero_argument_typed nz_minor_argument_typed",
    },
    Registration::Proof {
        declaration_index: 13,
        name: "nz_general_nonzero_caller_nat",
        type_src: r"TypingCtxConvIn nz_env (natTEnv Level.zero) (ListType.nil KExpr) nz_raw_result natTypeC",
        value_src: r"TypingCtxConvIn.conv nz_env (natTEnv Level.zero) (ListType.nil KExpr)
 nz_raw_result (KExpr.app nz_motive natZeroC) natTypeC
 nz_general_nonzero_caller (nz_motive_beta natZeroC)",
    },
    Registration::Proof {
        declaration_index: 14,
        name: "nz_general_nonzero_step",
        type_src: r"iota_step (red_rec nz_env) nz_input nz_raw_result",
        value_src: r"nz_general_guarded_step (Level.succ Level.zero) nz_motive natZeroC nz_minor",
    },
    Registration::Proof {
        declaration_index: 15,
        name: "nz_zero_spine_open_motive_control",
        type_src: r"Eq KExpr (instantiate (nz_zero_sarm_after_m (KExpr.bvar Nat.zero))
   (KExpr.bvar (Nat.succ Nat.zero))) (natSuccCaseSem (KExpr.bvar Nat.zero))",
        value_src: r"nz_zero_sarm_after_z_eq (KExpr.bvar Nat.zero) (KExpr.bvar (Nat.succ Nat.zero))",
    },
    Registration::Data {
        declaration_index: 16,
        name: "nz_zero_input_args",
    },
    Registration::Data {
        declaration_index: 17,
        name: "nz_zero_input_tail",
    },
    Registration::Data {
        declaration_index: 18,
        name: "nz_zero_input_after_m",
    },
    Registration::Proof {
        declaration_index: 19,
        name: "nz_zero_input_after_m_eq",
        type_src: r"forall (m : KExpr),
 Eq KExpr (instantiate nz_zero_input_tail m) (nz_zero_input_after_m m)",
        value_src: r"fun (m : KExpr) =>
 (Eq.cong KExpr KExpr (fun (x : KExpr) => (KExpr.pi (KExpr.app x natZeroC) (KExpr.pi (nz_zero_sarm_after_m m) (KExpr.pi natTypeC (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar Nat.zero)))))) (lift_at m Nat.zero Nat.zero) m (lift_zero_identity m))",
    },
    Registration::Proof {
        declaration_index: 20,
        name: "nz_zero_input_after_z_eq",
        type_src: r"forall (m : KExpr) (z : KExpr),
 Eq KExpr (instantiate (KExpr.pi (nz_zero_sarm_after_m m) (KExpr.pi natTypeC (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar Nat.zero)))) z) (KExpr.pi (natSuccCaseSem m) (KExpr.pi natTypeC (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero))))",
        value_src: r"fun (m : KExpr) (z : KExpr) =>
 (universe_bridge_congr2 KExpr KExpr KExpr (fun (A : KExpr) (B : KExpr) => KExpr.pi A B) (instantiate (nz_zero_sarm_after_m m) z) (natSuccCaseSem m) (KExpr.pi natTypeC (KExpr.app (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) z (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero))) (KExpr.pi natTypeC (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero))) (nz_zero_sarm_after_z_eq m z) (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.pi natTypeC x) (KExpr.app (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) z (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (Eq.cong KExpr KExpr (fun (x : KExpr) => (KExpr.app x (KExpr.bvar Nat.zero))) (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) z (Nat.succ (Nat.succ Nat.zero))) (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (instantiate_lift_cancel_general m z Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero))) (Nat.succ (Nat.succ Nat.zero)) (Eq.refl Nat (Nat.succ Nat.zero))))))",
    },
    Registration::Proof {
        declaration_index: 21,
        name: "nz_zero_input_after_s_eq",
        type_src: r"forall (m : KExpr) (s : KExpr),
 Eq KExpr (instantiate (KExpr.pi natTypeC (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero))) s) (KExpr.pi natTypeC (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)))",
        value_src: r"fun (m : KExpr) (s : KExpr) =>
 (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.pi natTypeC x) (KExpr.app (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) s (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) (Eq.cong KExpr KExpr (fun (x : KExpr) => (KExpr.app x (KExpr.bvar Nat.zero))) (instantiate_at (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) s (Nat.succ Nat.zero)) (lift_at m Nat.zero (Nat.succ Nat.zero)) (inst_at1_lift2 m s)))",
    },
    Registration::Proof {
        declaration_index: 22,
        name: "nz_zero_input_after_major_eq",
        type_src: r"forall (m : KExpr),
 Eq KExpr (instantiate (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) natZeroC) (KExpr.app m natZeroC)",
        value_src: r"fun (m : KExpr) =>
 (Eq.cong KExpr KExpr (fun (x : KExpr) => KExpr.app x natZeroC) (instantiate (lift_at m Nat.zero (Nat.succ Nat.zero)) natZeroC) m (inst_lift1 m natZeroC))",
    },
    Registration::Proof {
        declaration_index: 23,
        name: "nz_zero_input_typed_spine",
        type_src: r"forall (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr) (u : Level) (m : KExpr) (z : KExpr) (s : KExpr)
 (hm : TypingCtxConvIn R tenv G m (natMotiveTy u))
 (hz : TypingCtxConvIn R tenv G z (KExpr.app m natZeroC))
 (hs : TypingCtxConvIn R tenv G s (natSuccCaseSem m))
 (hzero : TypingCtxConvIn R tenv G natZeroC natTypeC),
 TypedRawPiSpine R tenv G (natRecTy u) (nz_zero_input_args m z s) (KExpr.app m natZeroC)",
        value_src: r"fun (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr) (u : Level) (m : KExpr) (z : KExpr) (s : KExpr)
 (hm : TypingCtxConvIn R tenv G m (natMotiveTy u))
 (hz : TypingCtxConvIn R tenv G z (KExpr.app m natZeroC))
 (hs : TypingCtxConvIn R tenv G s (natSuccCaseSem m))
 (hzero : TypingCtxConvIn R tenv G natZeroC natTypeC) =>
 TypedRawPiSpine.cons R tenv G (natMotiveTy u) nz_zero_input_tail m (ListType.cons KExpr z (ListType.cons KExpr s (ListType.cons KExpr natZeroC (ListType.nil KExpr)))) (KExpr.app m natZeroC) hm (Eq.substType KExpr (fun (F : KExpr) => TypedRawPiSpine R tenv G F (ListType.cons KExpr z (ListType.cons KExpr s (ListType.cons KExpr natZeroC (ListType.nil KExpr)))) (KExpr.app m natZeroC)) (nz_zero_input_after_m m) (instantiate nz_zero_input_tail m) (Eq.symm KExpr (instantiate nz_zero_input_tail m) (nz_zero_input_after_m m) (nz_zero_input_after_m_eq m)) (TypedRawPiSpine.cons R tenv G (KExpr.app m natZeroC) (KExpr.pi (nz_zero_sarm_after_m m) (KExpr.pi natTypeC (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar Nat.zero)))) z (ListType.cons KExpr s (ListType.cons KExpr natZeroC (ListType.nil KExpr))) (KExpr.app m natZeroC) hz (Eq.substType KExpr (fun (F : KExpr) => TypedRawPiSpine R tenv G F (ListType.cons KExpr s (ListType.cons KExpr natZeroC (ListType.nil KExpr))) (KExpr.app m natZeroC)) (KExpr.pi (natSuccCaseSem m) (KExpr.pi natTypeC (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)))) (instantiate (KExpr.pi (nz_zero_sarm_after_m m) (KExpr.pi natTypeC (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar Nat.zero)))) z) (Eq.symm KExpr (instantiate (KExpr.pi (nz_zero_sarm_after_m m) (KExpr.pi natTypeC (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar Nat.zero)))) z) (KExpr.pi (natSuccCaseSem m) (KExpr.pi natTypeC (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)))) (nz_zero_input_after_z_eq m z)) (TypedRawPiSpine.cons R tenv G (natSuccCaseSem m) (KExpr.pi natTypeC (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero))) s (ListType.cons KExpr natZeroC (ListType.nil KExpr)) (KExpr.app m natZeroC) hs (Eq.substType KExpr (fun (F : KExpr) => TypedRawPiSpine R tenv G F (ListType.cons KExpr natZeroC (ListType.nil KExpr)) (KExpr.app m natZeroC)) (KExpr.pi natTypeC (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero))) (instantiate (KExpr.pi natTypeC (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero))) s) (Eq.symm KExpr (instantiate (KExpr.pi natTypeC (KExpr.app (lift_at m Nat.zero (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero))) s) (KExpr.pi natTypeC (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero))) (nz_zero_input_after_s_eq m s)) (TypedRawPiSpine.cons R tenv G natTypeC (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) natZeroC (ListType.nil KExpr) (KExpr.app m natZeroC) hzero (Eq.substType KExpr (fun (F : KExpr) => TypedRawPiSpine R tenv G F (ListType.nil KExpr) (KExpr.app m natZeroC)) (KExpr.app m natZeroC) (instantiate (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) natZeroC) (Eq.symm KExpr (instantiate (KExpr.app (lift_at m Nat.zero (Nat.succ Nat.zero)) (KExpr.bvar Nat.zero)) natZeroC) (KExpr.app m natZeroC) (nz_zero_input_after_major_eq m)) (TypedRawPiSpine.nil R tenv G (KExpr.app m natZeroC)))))))))",
    },
    Registration::Proof {
        declaration_index: 24,
        name: "nz_general_input_typed",
        type_src: r"forall (R : RedEnv) (u : Level) (m : KExpr) (z : KExpr) (s : KExpr)
 (hm : TypingCtxConvIn R (natTEnv Level.zero) (ListType.nil KExpr) m (natMotiveTy u))
 (hz : TypingCtxConvIn R (natTEnv Level.zero) (ListType.nil KExpr) z (KExpr.app m natZeroC))
 (hs : TypingCtxConvIn R (natTEnv Level.zero) (ListType.nil KExpr) s (natSuccCaseSem m)),
 TypingCtxConvIn R (natTEnv Level.zero) (ListType.nil KExpr) (natRecApp u m z s natZeroC) (KExpr.app m natZeroC)",
        value_src: r"fun (R : RedEnv) (u : Level) (m : KExpr) (z : KExpr) (s : KExpr)
 (hm : TypingCtxConvIn R (natTEnv Level.zero) (ListType.nil KExpr) m (natMotiveTy u))
 (hz : TypingCtxConvIn R (natTEnv Level.zero) (ListType.nil KExpr) z (KExpr.app m natZeroC))
 (hs : TypingCtxConvIn R (natTEnv Level.zero) (ListType.nil KExpr) s (natSuccCaseSem m)) =>
 typed_raw_pi_spine_const_apply R (natTEnv Level.zero) (ListType.nil KExpr) recName
 (ListType.cons Level u (ListType.nil Level)) (natRecTy u)
 (nz_zero_input_args m z s) (KExpr.app m natZeroC) (natTEnv_rec_lookup u)
 (nz_zero_input_typed_spine R (natTEnv Level.zero) (ListType.nil KExpr) u m z s hm hz hs
  (nz_typing_to_semantic R (natTEnv Level.zero) (ListType.nil KExpr) natZeroC natTypeC (nz_zero_typed (ListType.nil KExpr))))",
    },
    Registration::Proof {
        declaration_index: 25,
        name: "nz_general_nonzero_input",
        type_src: r"TypingCtxConvIn nz_env (natTEnv Level.zero) (ListType.nil KExpr) nz_input (KExpr.app nz_motive natZeroC)",
        value_src: r"nz_general_input_typed nz_env (Level.succ Level.zero) nz_motive natZeroC nz_minor nz_motive_argument_typed nz_zero_argument_typed nz_minor_argument_typed",
    },
];

impl Specification {
    /// After add_nat_zero_rhs_typing and add_semantic_typed_spine_forward.
    /// Uses the existing late full-model Nat and substitution dependencies.
    pub(super) fn add_nat_zero_rhs_general(&mut self) -> Result<(), SpecError> {
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
                    self.add_definition(SpecDefinition {
                        name: (*name).to_string(),
                        type_src: (*type_src).to_string(),
                        value_src: Some((*value_src).to_string()),
                        is_axiom: false,
                        description: DECLARATIONS[*declaration_index].1.to_string(),
                        category: AxiomCategory::DerivedLemma,
                        proof_status: ProofStatus::DerivedProved,
                        elaborated_type: None,
                        elaborated_value: None,
                        dependencies: None,
                        axiom_deps: HashSet::new(),
                    })?;
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::{Registration, DECLARATIONS, REGISTRATIONS};
    use crate::spec::types::{AxiomCategory, ProofStatus};
    use crate::test_utils::{build_spec_with_stack, parse_check, run_with_stack};
    use clean_kernel::{ConstantKind, ExprKind, Name, TypeChecker};

    const PROOF_ROOTS: &[&str] = &[
        "nz_zero_after_m_eq",
        "nz_zero_sarm_after_z_eq",
        "nz_zero_after_z_eq",
        "nz_zero_after_s_eq",
        "nz_zero_typed_spine",
        "nz_general_raw_result_typed",
        "nz_general_guarded_step",
        "nz_general_guarded_result_typed",
        "nz_general_nonzero_caller",
        "nz_general_nonzero_caller_nat",
        "nz_general_nonzero_step",
        "nz_zero_spine_open_motive_control",
        "nz_zero_input_after_m_eq",
        "nz_zero_input_after_z_eq",
        "nz_zero_input_after_s_eq",
        "nz_zero_input_after_major_eq",
        "nz_zero_input_typed_spine",
        "nz_general_input_typed",
        "nz_general_nonzero_input",
    ];

    // Well-parsed false terms: refusal is not a universal untypability claim.
    const NEGATIVE_CONTROLS: &[&str] = &[
        r"def nz_general_forged_raw_type : TypingCtxConvIn nz_env (natTEnv Level.zero)
 (ListType.nil KExpr) nz_raw_result (KExpr.sort Level.zero) := nz_general_nonzero_caller_nat",
        r"def nz_general_forged_minor : TypingCtxConvIn nz_env (natTEnv Level.zero) (ListType.nil KExpr)
 nz_raw_result (KExpr.app nz_motive natZeroC) :=
 nz_general_guarded_result_typed (Level.succ Level.zero) nz_motive natZeroC nz_minor
 nz_motive_argument_typed nz_zero_argument_typed nz_zero_argument_typed",
        r"def nz_general_forged_universe : iota_step (red_rec nz_env) nz_input
 (KExpr.app (KExpr.app (KExpr.app (natRecRhsZero Level.zero) nz_motive) natZeroC) nz_minor) :=
 nz_general_nonzero_step",
        r"def nz_general_forged_input_missing_universe :
 TypingCtxConvIn nz_env (natTEnv Level.zero) (ListType.nil KExpr)
 (apply_spine (nz_zero_input_args nz_motive natZeroC nz_minor)
   (KExpr.const recName (ListType.nil Level))) (KExpr.app nz_motive natZeroC) :=
 nz_general_nonzero_input",
    ];

    #[test]
    fn nat_zero_rhs_general_explicit_records_preserve_checked_terms() {
        use clean_parser::{parse_decl, parse_expr, Span, SurfaceDecl, SurfaceExpr};

        fn fragment(source: &str, span: Span) -> Vec<&str> {
            source[span.start..span.end].split_whitespace().collect()
        }

        assert_eq!(DECLARATIONS.len(), 26);
        assert_eq!(REGISTRATIONS.len(), DECLARATIONS.len());
        let mut proofs = 0;
        let mut data = 0;
        for (index, registration) in REGISTRATIONS.iter().enumerate() {
            let (source, _) = DECLARATIONS[index];
            let SurfaceDecl::Def {
                name,
                binders,
                ty: Some(ty),
                val,
                ..
            } = parse_decl(source).expect("prototype declaration parses")
            else {
                panic!("expected explicit prototype definition");
            };
            match registration {
                Registration::Data {
                    declaration_index,
                    name: registered_name,
                } => {
                    data += 1;
                    assert_eq!(*declaration_index, index);
                    assert_eq!(
                        clean_parser::parse_name(registered_name).expect("explicit source name"),
                        name
                    );
                    assert!(!PROOF_ROOTS.contains(registered_name));
                }
                Registration::Proof {
                    declaration_index,
                    name: registered_name,
                    type_src,
                    value_src,
                } => {
                    proofs += 1;
                    assert_eq!(*declaration_index, index);
                    assert_eq!(
                        clean_parser::parse_name(registered_name).expect("explicit source name"),
                        name
                    );
                    assert!(PROOF_ROOTS.contains(registered_name));
                    assert_ne!(value_src.trim(), *registered_name, "no self-constant proof");
                    let parsed_type = parse_expr(type_src).expect("explicit proof type parses");
                    let parsed_value = parse_expr(value_src).expect("explicit proof value parses");
                    if binders.is_empty() {
                        assert_eq!(
                            fragment(source, ty.span()),
                            fragment(type_src, parsed_type.span()),
                            "{name}: result type"
                        );
                        assert_eq!(
                            fragment(source, val.span()),
                            fragment(value_src, parsed_value.span()),
                            "{name}: proof body"
                        );
                    } else {
                        let SurfaceExpr::Pi(_, type_binders, result) = parsed_type else {
                            panic!("{name}: expected explicit forall");
                        };
                        let SurfaceExpr::Lambda(_, value_binders, body) = parsed_value else {
                            panic!("{name}: expected explicit fun");
                        };
                        assert_eq!(type_binders.len(), binders.len(), "{name}: forall binders");
                        assert_eq!(value_binders.len(), binders.len(), "{name}: fun binders");
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
                            fragment(source, ty.span()),
                            fragment(type_src, result.span()),
                            "{name}: result type"
                        );
                        assert_eq!(
                            fragment(source, val.span()),
                            fragment(value_src, body.span()),
                            "{name}: proof body"
                        );
                    }
                }
            }
        }
        assert_eq!(proofs, 19);
        assert_eq!(data, 7);
    }

    #[test]
    fn nat_zero_rhs_general_actual_roots_values_types_and_closures_recheck() {
        run_with_stack(|| {
            let spec = build_spec_with_stack();
            for registration in REGISTRATIONS {
                let (name, proof_record) = match registration {
                    Registration::Data { name, .. } => (*name, None),
                    Registration::Proof {
                        name,
                        type_src,
                        value_src,
                        ..
                    } => (*name, Some((*type_src, *value_src))),
                };
                let definition = spec
                    .definitions()
                    .get(name)
                    .expect("registered declaration");
                let kernel_name = Name::from_string(name);
                let constant = spec
                    .env()
                    .get_const(&kernel_name)
                    .expect("actual kernel root");
                let ty = definition
                    .elaborated_type
                    .as_ref()
                    .expect("actual elaborated type");
                let value = definition
                    .elaborated_value
                    .as_ref()
                    .expect("actual elaborated body");
                assert!(!definition.is_axiom, "{name}");
                assert_ne!(constant.kind, ConstantKind::Axiom, "{name}");
                assert_eq!(&constant.type_, ty, "{name}: kernel type agreement");
                assert_eq!(
                    constant.value.as_ref(),
                    Some(value),
                    "{name}: kernel value agreement"
                );
                assert!(
                    !matches!(value.kind(), ExprKind::Const(found, _) if found == &kernel_name),
                    "{name}: not a self-constant proof"
                );
                let domains = spec
                    .env()
                    .axiom_deps(&kernel_name)
                    .expect("actual root domain closure");
                let foundations = spec
                    .env()
                    .foundational_axiom_deps(&kernel_name)
                    .expect("actual root foundational closure");
                assert!(domains.is_empty(), "{name}: domain axioms {domains:?}");
                assert!(
                    foundations.is_empty(),
                    "{name}: foundational axioms {foundations:?}"
                );
                if let Some((type_src, value_src)) = proof_record {
                    assert!(PROOF_ROOTS.contains(&name));
                    assert_eq!(definition.category, AxiomCategory::DerivedLemma, "{name}");
                    assert_eq!(
                        definition.proof_status,
                        ProofStatus::DerivedProved,
                        "{name}"
                    );
                    assert_eq!(definition.type_src, type_src, "{name}");
                    assert_eq!(definition.value_src.as_deref(), Some(value_src), "{name}");
                    spec.verify_definition(name)
                        .expect("actual proof body rechecks");
                } else {
                    assert_eq!(
                        definition.proof_status,
                        ProofStatus::DerivedPending,
                        "{name}: data is not counted as a theorem"
                    );
                    assert_eq!(
                        constant.kind,
                        ConstantKind::Definition,
                        "{name}: computational data remains unfoldable"
                    );
                }
            }
        });
    }

    #[test]
    fn nat_zero_rhs_general_actual_nonzero_input_step_and_raw_result_check() {
        run_with_stack(|| {
            let spec = build_spec_with_stack();
            for (value_src, type_src) in [
                ("nz_general_nonzero_input",
                 "TypingCtxConvIn nz_env (natTEnv Level.zero) (ListType.nil KExpr) nz_input (KExpr.app nz_motive natZeroC)"),
                ("nz_general_nonzero_step",
                 "iota_step (red_rec nz_env) nz_input nz_raw_result"),
                ("nz_general_nonzero_caller",
                 "TypingCtxConvIn nz_env (natTEnv Level.zero) (ListType.nil KExpr) nz_raw_result (KExpr.app nz_motive natZeroC)"),
                ("nz_general_nonzero_caller_nat",
                 "TypingCtxConvIn nz_env (natTEnv Level.zero) (ListType.nil KExpr) nz_raw_result natTypeC"),
                ("nz_zero_spine_open_motive_control",
                 "Eq KExpr (instantiate (nz_zero_sarm_after_m (KExpr.bvar Nat.zero)) (KExpr.bvar (Nat.succ Nat.zero))) (natSuccCaseSem (KExpr.bvar Nat.zero))"),
            ] {
                let value = spec.elaborate_source(value_src, "actual generic Nat.zero caller")
                    .expect("actual caller elaborates");
                let expected = spec.elaborate_source(type_src, "actual caller result type")
                    .expect("actual caller result type elaborates");
                let checker = TypeChecker::with_mode(spec.env(), spec.env().mode());
                let inferred = checker.infer_type(&value).expect("actual caller typechecks");
                assert!(checker.is_def_eq(&inferred, &expected), "{value_src}");
            }
        });
    }

    #[test]
    fn nat_zero_rhs_general_rejects_wrong_result_minor_and_universes() {
        run_with_stack(|| {
            let mut spec = build_spec_with_stack();
            assert_eq!(NEGATIVE_CONTROLS.len(), 4);
            for source in NEGATIVE_CONTROLS {
                parse_check(source).expect("negative proof is well parsed");
                let name = source
                    .split_whitespace()
                    .nth(1)
                    .expect("negative proof name");
                let error = spec.add_recursive_def(source, "Deliberately forged generic Nat.zero proof.")
                    .expect_err("wrong result, minor, output universe or missing input universe must be refused");
                assert!(format!("{error:?}").contains("Type mismatch"), "{error:?}");
                assert!(
                    !spec.definitions().contains_key(name),
                    "{name}: no rejected metadata"
                );
                assert!(
                    spec.env().get_const(&Name::from_string(name)).is_none(),
                    "{name}: no rejected kernel root"
                );
            }
        });
    }
}

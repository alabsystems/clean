// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Typed schematic Nat.zero RHS and a genuinely typed guarded caller.
//!
//! These are the existing synthetic Nat objects, not reflected source admission.
//! The generic RHS proof uses direct TypingCtx constructors; the closed caller
//! supplies real universe-one motive/minor terms. Input typing, the actual raw
//! iota step, and raw-result typing are proved independently, without CandModel,
//! TypingEnvCoherent, a subject-reduction oracle, or assumed RHS/output typing.
//! This does not discharge general iota preservation, legacy tec_iota_typed,
//! successor/other recursor branches, extra arguments, or Rust refinement.
//!
//! Exact 26-declaration prototype and independent positive/negative evidence:
//! scratch/self-verification-nat-zero-rhs-typing-2026-09-08.md.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

const DECLARATIONS: &[(&str, &str)] = &[
    (r"def nz_rule_type (u : Level) : KExpr := (KExpr.pi (natMotiveTy u) (KExpr.pi (KExpr.app (KExpr.bvar Nat.zero) natZeroC) (KExpr.pi natRecSArm (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) natZeroC))))", "The actual three-binder type telescope of the synthetic Nat.zero rule."),

    (r"def nz_nat_typed (G : ListType KExpr) : TypingCtx (natTEnv Level.zero) G natTypeC (KExpr.sort (Level.succ Level.zero)) := TypingCtx.const (natTEnv Level.zero) G natName (ListType.nil Level) (KExpr.sort (Level.succ Level.zero)) (Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.sort (Level.succ Level.zero))))", "Constructive typing or conversion prerequisite for the actual synthetic Nat.zero guarded caller."),

    (r"def nz_zero_typed (G : ListType KExpr) : TypingCtx (natTEnv Level.zero) G natZeroC natTypeC := TypingCtx.const (natTEnv Level.zero) G zeroName (ListType.nil Level) natTypeC (Eq.refl (OptionType KExpr) (OptionType.some KExpr natTypeC))", "Constructive typing or conversion prerequisite for the actual synthetic Nat.zero guarded caller."),

    (r"def nz_succ_typed (G : ListType KExpr) : TypingCtx (natTEnv Level.zero) G natSuccC (KExpr.pi natTypeC natTypeC) := TypingCtx.const (natTEnv Level.zero) G succName (ListType.nil Level) (KExpr.pi natTypeC natTypeC) (Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.pi natTypeC natTypeC)))", "Constructive typing or conversion prerequisite for the actual synthetic Nat.zero guarded caller."),

    (r"def nz_motive_typed (u : Level) (G : ListType KExpr) : TypingCtx (natTEnv Level.zero) G (natMotiveTy u) (KExpr.sort (Level.imax (Level.succ Level.zero) (Level.succ u))) := TypingCtx.pi (natTEnv Level.zero) G natTypeC (KExpr.sort u) (Level.succ Level.zero) (Level.succ u) (nz_nat_typed G) (TypingCtx.sort (natTEnv Level.zero) (ListType.cons KExpr natTypeC G) u)", "Constructive typing or conversion prerequisite for the actual synthetic Nat.zero guarded caller."),

    (r"def nz_zero_domain_typed (u : Level) : TypingCtx (natTEnv Level.zero) (ListType.cons KExpr (natMotiveTy u) (ListType.nil KExpr)) (KExpr.app (KExpr.bvar Nat.zero) natZeroC) (KExpr.sort u) := (TypingCtx.app (natTEnv Level.zero) (ListType.cons KExpr (natMotiveTy u) (ListType.nil KExpr)) (KExpr.bvar Nat.zero) natZeroC natTypeC (KExpr.sort u) (TypingCtx.var (natTEnv Level.zero) (ListType.cons KExpr (natMotiveTy u) (ListType.nil KExpr)) Nat.zero (natMotiveTy u) (Eq.refl (OptionType KExpr) (OptionType.some KExpr (natMotiveTy u)))) (nz_zero_typed (ListType.cons KExpr (natMotiveTy u) (ListType.nil KExpr))))", "Constructive typing or conversion prerequisite for the actual synthetic Nat.zero guarded caller."),

    (r"def nz_sarm_typed (u : Level) : TypingCtx (natTEnv Level.zero) (ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) natZeroC) (ListType.cons KExpr (natMotiveTy u) (ListType.nil KExpr))) natRecSArm (KExpr.sort (Level.imax (Level.succ Level.zero) (Level.imax u u))) := TypingCtx.pi (natTEnv Level.zero) (ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) natZeroC) (ListType.cons KExpr (natMotiveTy u) (ListType.nil KExpr))) natTypeC (KExpr.pi (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.app natSuccC (KExpr.bvar (Nat.succ Nat.zero))))) (Level.succ Level.zero) (Level.imax u u) (nz_nat_typed (ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) natZeroC) (ListType.cons KExpr (natMotiveTy u) (ListType.nil KExpr)))) (TypingCtx.pi (natTEnv Level.zero) (ListType.cons KExpr natTypeC (ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) natZeroC) (ListType.cons KExpr (natMotiveTy u) (ListType.nil KExpr)))) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.app natSuccC (KExpr.bvar (Nat.succ Nat.zero)))) u u (TypingCtx.app (natTEnv Level.zero) (ListType.cons KExpr natTypeC (ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) natZeroC) (ListType.cons KExpr (natMotiveTy u) (ListType.nil KExpr)))) (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero) natTypeC (KExpr.sort u) (TypingCtx.var (natTEnv Level.zero) (ListType.cons KExpr natTypeC (ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) natZeroC) (ListType.cons KExpr (natMotiveTy u) (ListType.nil KExpr)))) (Nat.succ (Nat.succ Nat.zero)) (natMotiveTy u) (Eq.refl (OptionType KExpr) (OptionType.some KExpr (natMotiveTy u)))) (TypingCtx.var (natTEnv Level.zero) (ListType.cons KExpr natTypeC (ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) natZeroC) (ListType.cons KExpr (natMotiveTy u) (ListType.nil KExpr)))) Nat.zero natTypeC (Eq.refl (OptionType KExpr) (OptionType.some KExpr natTypeC)))) (TypingCtx.app (natTEnv Level.zero) (ListType.cons KExpr (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (ListType.cons KExpr natTypeC (ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) natZeroC) (ListType.cons KExpr (natMotiveTy u) (ListType.nil KExpr))))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.app natSuccC (KExpr.bvar (Nat.succ Nat.zero))) natTypeC (KExpr.sort u) (TypingCtx.var (natTEnv Level.zero) (ListType.cons KExpr (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (ListType.cons KExpr natTypeC (ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) natZeroC) (ListType.cons KExpr (natMotiveTy u) (ListType.nil KExpr))))) (Nat.succ (Nat.succ (Nat.succ Nat.zero))) (natMotiveTy u) (Eq.refl (OptionType KExpr) (OptionType.some KExpr (natMotiveTy u)))) (TypingCtx.app (natTEnv Level.zero) (ListType.cons KExpr (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (ListType.cons KExpr natTypeC (ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) natZeroC) (ListType.cons KExpr (natMotiveTy u) (ListType.nil KExpr))))) natSuccC (KExpr.bvar (Nat.succ Nat.zero)) natTypeC natTypeC (nz_succ_typed (ListType.cons KExpr (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (ListType.cons KExpr natTypeC (ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) natZeroC) (ListType.cons KExpr (natMotiveTy u) (ListType.nil KExpr)))))) (TypingCtx.var (natTEnv Level.zero) (ListType.cons KExpr (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (ListType.cons KExpr natTypeC (ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) natZeroC) (ListType.cons KExpr (natMotiveTy u) (ListType.nil KExpr))))) (Nat.succ Nat.zero) natTypeC (Eq.refl (OptionType KExpr) (OptionType.some KExpr natTypeC))))))", "Constructive typing or conversion prerequisite for the actual synthetic Nat.zero guarded caller."),

    (r"def nz_rhs_typed (u : Level) : TypingCtx (natTEnv Level.zero) (ListType.nil KExpr) (natRecRhsZero u) (nz_rule_type u) := (TypingCtx.lam (natTEnv Level.zero) (ListType.nil KExpr) (natMotiveTy u) (KExpr.lam (KExpr.app (KExpr.bvar Nat.zero) natZeroC) (KExpr.lam natRecSArm (KExpr.bvar (Nat.succ Nat.zero)))) (KExpr.pi (KExpr.app (KExpr.bvar Nat.zero) natZeroC) (KExpr.pi natRecSArm (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) natZeroC))) (Level.imax (Level.succ Level.zero) (Level.succ u)) (nz_motive_typed u (ListType.nil KExpr)) (TypingCtx.lam (natTEnv Level.zero) (ListType.cons KExpr (natMotiveTy u) (ListType.nil KExpr)) (KExpr.app (KExpr.bvar Nat.zero) natZeroC) (KExpr.lam natRecSArm (KExpr.bvar (Nat.succ Nat.zero))) (KExpr.pi natRecSArm (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) natZeroC)) u (nz_zero_domain_typed u) (TypingCtx.lam (natTEnv Level.zero) (ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) natZeroC) (ListType.cons KExpr (natMotiveTy u) (ListType.nil KExpr))) natRecSArm (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) natZeroC) (Level.imax (Level.succ Level.zero) (Level.imax u u)) (nz_sarm_typed u) (TypingCtx.var (natTEnv Level.zero) (ListType.cons KExpr natRecSArm (ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) natZeroC) (ListType.cons KExpr (natMotiveTy u) (ListType.nil KExpr)))) (Nat.succ Nat.zero) (KExpr.app (KExpr.bvar Nat.zero) natZeroC) (Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.app (KExpr.bvar Nat.zero) natZeroC)))))))", "The actual Nat.zero RHS is typed at every raw universe by direct TypingCtx constructors; no coherence, substitution, weakening or RHS-typing premise."),

    (r"def nz_stored_rhs_typed : TypingCtx (natTEnv Level.zero) (ListType.nil KExpr) (natRecRhsZero (Level.param Name.anonymous)) (nz_rule_type (Level.param Name.anonymous)) := nz_rhs_typed (Level.param Name.anonymous)", "Typing of the actual stored schematic Nat.zero RHS at its declared anonymous universe parameter."),

    (r"def nz_typing_to_semantic (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr) (e : KExpr) (T : KExpr) (h : TypingCtx tenv G e T) :
 TypingCtxConvIn R tenv G e T :=
 TypingCtx.rec tenv
  (fun (G0 : ListType KExpr) (e0 : KExpr) (T0 : KExpr) (_h : TypingCtx tenv G0 e0 T0) =>
   TypingCtxConvIn R tenv G0 e0 T0)
  (fun (G0 : ListType KExpr) (i : Nat) (A : KExpr)
   (lookup : Eq (OptionType KExpr) (ctx_lookup G0 i) (OptionType.some KExpr A)) =>
    TypingCtxConvIn.var R tenv G0 i A lookup)
  (fun (G0 : ListType KExpr) (u : Level) => TypingCtxConvIn.sort R tenv G0 u)
  (fun (G0 : ListType KExpr) (A : KExpr) (B : KExpr) (u : Level) (v : Level)
   (_hA : TypingCtx tenv G0 A (KExpr.sort u))
   (_hB : TypingCtx tenv (ListType.cons KExpr A G0) B (KExpr.sort v))
   (ihA : TypingCtxConvIn R tenv G0 A (KExpr.sort u))
   (ihB : TypingCtxConvIn R tenv (ListType.cons KExpr A G0) B (KExpr.sort v)) =>
   TypingCtxConvIn.pi R tenv G0 A B u v ihA ihB)
  (fun (G0 : ListType KExpr) (A : KExpr) (b : KExpr) (B : KExpr) (u : Level)
   (_hA : TypingCtx tenv G0 A (KExpr.sort u))
   (_hb : TypingCtx tenv (ListType.cons KExpr A G0) b B)
   (ihA : TypingCtxConvIn R tenv G0 A (KExpr.sort u))
   (ihb : TypingCtxConvIn R tenv (ListType.cons KExpr A G0) b B) =>
   TypingCtxConvIn.lam R tenv G0 A b B u ihA ihb)
  (fun (G0 : ListType KExpr) (f : KExpr) (a : KExpr) (A : KExpr) (B : KExpr)
   (_hf : TypingCtx tenv G0 f (KExpr.pi A B)) (_ha : TypingCtx tenv G0 a A)
   (ihf : TypingCtxConvIn R tenv G0 f (KExpr.pi A B))
   (iha : TypingCtxConvIn R tenv G0 a A) =>
   TypingCtxConvIn.app R tenv G0 f a A B ihf iha)
  (fun (G0 : ListType KExpr) (n : Name) (us : ListType Level) (A : KExpr)
   (lookup : Eq (OptionType KExpr) (kdecl_type_at tenv n us) (OptionType.some KExpr A)) =>
   TypingCtxConvIn.const R tenv G0 n us A lookup)
  (fun (G0 : ListType KExpr) (A : KExpr) (v : KExpr) (b : KExpr) (B : KExpr) (u : Level)
   (_hA : TypingCtx tenv G0 A (KExpr.sort u)) (_hv : TypingCtx tenv G0 v A)
   (_hb : TypingCtx tenv (ListType.cons KExpr A G0) b B)
   (ihA : TypingCtxConvIn R tenv G0 A (KExpr.sort u))
   (ihv : TypingCtxConvIn R tenv G0 v A)
   (ihb : TypingCtxConvIn R tenv (ListType.cons KExpr A G0) b B) =>
   TypingCtxConvIn.let_ R tenv G0 A v b B u ihA ihv ihb)
  G e T h", "The seven real TypingCtx constructors embed into TypingCtxConvIn for an arbitrary reduction environment, without a reverse-conversion claim."),

    (r"def nz_env : RedEnv := RedEnv.mk (natREnv Level.zero) DefEnv.empty IndCtorEnv.empty", "The existing synthetic schematic Nat recursor environment, with no delta definitions; not source-reflected admission."),

    (r"def nz_motive : KExpr := (KExpr.lam natTypeC natTypeC)", "A genuinely typed constant-Nat motive at nonzero universe one."),

    (r"def nz_minor : KExpr := (KExpr.lam natTypeC (KExpr.lam natTypeC (KExpr.app natSuccC (KExpr.bvar Nat.zero))))", "A genuinely typed successor minor, applying succ to the inductive hypothesis."),

    (r"def nz_minor_type : KExpr := (KExpr.pi natTypeC (KExpr.pi (KExpr.app nz_motive (KExpr.bvar Nat.zero)) (KExpr.app nz_motive (KExpr.app natSuccC (KExpr.bvar (Nat.succ Nat.zero))))))", "Constructive typing or conversion prerequisite for the actual synthetic Nat.zero guarded caller."),

    (r"def nz_motive_core_typed : TypingCtx (natTEnv Level.zero) (ListType.nil KExpr) nz_motive (natMotiveTy (Level.succ Level.zero)) :=
 TypingCtx.lam (natTEnv Level.zero) (ListType.nil KExpr) natTypeC natTypeC (KExpr.sort (Level.succ Level.zero)) (Level.succ Level.zero)
 (nz_nat_typed (ListType.nil KExpr)) (nz_nat_typed (ListType.cons KExpr natTypeC (ListType.nil KExpr)))", "Constructive typing or conversion prerequisite for the actual synthetic Nat.zero guarded caller."),

    (r"def nz_minor_core_typed : TypingCtx (natTEnv Level.zero) (ListType.nil KExpr) nz_minor (KExpr.pi natTypeC (KExpr.pi natTypeC natTypeC)) :=
 TypingCtx.lam (natTEnv Level.zero) (ListType.nil KExpr) natTypeC (KExpr.lam natTypeC (KExpr.app natSuccC (KExpr.bvar Nat.zero))) (KExpr.pi natTypeC natTypeC) (Level.succ Level.zero)
 (nz_nat_typed (ListType.nil KExpr))
 (TypingCtx.lam (natTEnv Level.zero) (ListType.cons KExpr natTypeC (ListType.nil KExpr)) natTypeC (KExpr.app natSuccC (KExpr.bvar Nat.zero)) natTypeC (Level.succ Level.zero)
  (nz_nat_typed (ListType.cons KExpr natTypeC (ListType.nil KExpr)))
  (TypingCtx.app (natTEnv Level.zero) (ListType.cons KExpr natTypeC (ListType.cons KExpr natTypeC (ListType.nil KExpr))) natSuccC (KExpr.bvar Nat.zero) natTypeC natTypeC
   (nz_succ_typed (ListType.cons KExpr natTypeC (ListType.cons KExpr natTypeC (ListType.nil KExpr))))
   (TypingCtx.var (natTEnv Level.zero) (ListType.cons KExpr natTypeC (ListType.cons KExpr natTypeC (ListType.nil KExpr))) Nat.zero natTypeC (Eq.refl (OptionType KExpr) (OptionType.some KExpr natTypeC)))))", "Constructive typing or conversion prerequisite for the actual synthetic Nat.zero guarded caller."),

    (r"def nz_motive_beta (x : KExpr) : DefEqIn nz_env (KExpr.app nz_motive x) natTypeC :=
 def_eq_in_beta nz_env natTypeC natTypeC x", "Constructive typing or conversion prerequisite for the actual synthetic Nat.zero guarded caller."),

    (r"def nz_minor_type_conversion : DefEqIn nz_env (KExpr.pi natTypeC (KExpr.pi natTypeC natTypeC)) nz_minor_type :=
 DefEqIn.pi nz_env natTypeC natTypeC (KExpr.pi natTypeC natTypeC) (KExpr.pi (KExpr.app nz_motive (KExpr.bvar Nat.zero)) (KExpr.app nz_motive (KExpr.app natSuccC (KExpr.bvar (Nat.succ Nat.zero)))))
  (DefEqIn.refl nz_env natTypeC)
  (DefEqIn.pi nz_env natTypeC (KExpr.app nz_motive (KExpr.bvar Nat.zero)) natTypeC (KExpr.app nz_motive (KExpr.app natSuccC (KExpr.bvar (Nat.succ Nat.zero))))
   (DefEqIn.symm nz_env (KExpr.app nz_motive (KExpr.bvar Nat.zero)) natTypeC (nz_motive_beta (KExpr.bvar Nat.zero)))
   (DefEqIn.symm nz_env (KExpr.app nz_motive (KExpr.app natSuccC (KExpr.bvar (Nat.succ Nat.zero)))) natTypeC (nz_motive_beta (KExpr.app natSuccC (KExpr.bvar (Nat.succ Nat.zero))))))", "Constructive typing or conversion prerequisite for the actual synthetic Nat.zero guarded caller."),

    (r"def nz_motive_argument_typed : TypingCtxConvIn nz_env (natTEnv Level.zero) (ListType.nil KExpr) nz_motive (natMotiveTy (Level.succ Level.zero)) := (nz_typing_to_semantic nz_env (natTEnv Level.zero) (ListType.nil KExpr) nz_motive (natMotiveTy (Level.succ Level.zero)) nz_motive_core_typed)", "Constructive typing or conversion prerequisite for the actual synthetic Nat.zero guarded caller."),

    (r"def nz_zero_argument_typed : TypingCtxConvIn nz_env (natTEnv Level.zero) (ListType.nil KExpr) natZeroC (KExpr.app nz_motive natZeroC) :=
 TypingCtxConvIn.conv nz_env (natTEnv Level.zero) (ListType.nil KExpr) natZeroC natTypeC (KExpr.app nz_motive natZeroC)
  (nz_typing_to_semantic nz_env (natTEnv Level.zero) (ListType.nil KExpr) natZeroC natTypeC (nz_zero_typed (ListType.nil KExpr)))
  (DefEqIn.symm nz_env (KExpr.app nz_motive natZeroC) natTypeC (nz_motive_beta natZeroC))", "Constructive typing or conversion prerequisite for the actual synthetic Nat.zero guarded caller."),

    (r"def nz_minor_argument_typed : TypingCtxConvIn nz_env (natTEnv Level.zero) (ListType.nil KExpr) nz_minor nz_minor_type :=
 TypingCtxConvIn.conv nz_env (natTEnv Level.zero) (ListType.nil KExpr) nz_minor (KExpr.pi natTypeC (KExpr.pi natTypeC natTypeC)) nz_minor_type
  (nz_typing_to_semantic nz_env (natTEnv Level.zero) (ListType.nil KExpr) nz_minor (KExpr.pi natTypeC (KExpr.pi natTypeC natTypeC)) nz_minor_core_typed) nz_minor_type_conversion", "Constructive typing or conversion prerequisite for the actual synthetic Nat.zero guarded caller."),

    (r"def nz_input : KExpr := natRecApp (Level.succ Level.zero) nz_motive natZeroC nz_minor natZeroC", "Constructive typing or conversion prerequisite for the actual synthetic Nat.zero guarded caller."),

    (r"def nz_input_typed : TypingCtxConvIn nz_env (natTEnv Level.zero) (ListType.nil KExpr) nz_input natTypeC :=
 TypingCtxConvIn.conv nz_env (natTEnv Level.zero) (ListType.nil KExpr) nz_input (KExpr.app nz_motive natZeroC) natTypeC (TypingCtxConvIn.app nz_env (natTEnv Level.zero) (ListType.nil KExpr) (KExpr.app (KExpr.app (KExpr.app (natRecC (Level.succ Level.zero)) nz_motive) natZeroC) nz_minor) natZeroC natTypeC (KExpr.app nz_motive (KExpr.bvar Nat.zero)) (TypingCtxConvIn.app nz_env (natTEnv Level.zero) (ListType.nil KExpr) (KExpr.app (KExpr.app (natRecC (Level.succ Level.zero)) nz_motive) natZeroC) nz_minor nz_minor_type (KExpr.pi natTypeC (KExpr.app nz_motive (KExpr.bvar Nat.zero))) (TypingCtxConvIn.app nz_env (natTEnv Level.zero) (ListType.nil KExpr) (KExpr.app (natRecC (Level.succ Level.zero)) nz_motive) natZeroC (KExpr.app nz_motive natZeroC) (KExpr.pi nz_minor_type (KExpr.pi natTypeC (KExpr.app nz_motive (KExpr.bvar Nat.zero)))) (TypingCtxConvIn.app nz_env (natTEnv Level.zero) (ListType.nil KExpr) (natRecC (Level.succ Level.zero)) nz_motive (natMotiveTy (Level.succ Level.zero)) (KExpr.pi (KExpr.app (KExpr.bvar Nat.zero) natZeroC) (KExpr.pi natRecSArm (KExpr.pi natTypeC (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar Nat.zero))))) (nz_typing_to_semantic nz_env (natTEnv Level.zero) (ListType.nil KExpr) (natRecC (Level.succ Level.zero)) (natRecTy (Level.succ Level.zero)) (natTEnv_rec_typed (Level.succ Level.zero))) nz_motive_argument_typed) nz_zero_argument_typed) nz_minor_argument_typed) (nz_typing_to_semantic nz_env (natTEnv Level.zero) (ListType.nil KExpr) natZeroC natTypeC (nz_zero_typed (ListType.nil KExpr)))) (nz_motive_beta natZeroC)", "The actual universe-one recursor caller has type Nat, from its real motive and minor typings."),

    (r"def nz_raw_result : KExpr := (KExpr.app (KExpr.app (KExpr.app (natRecRhsZero (Level.succ Level.zero)) nz_motive) natZeroC) nz_minor)", "Constructive typing or conversion prerequisite for the actual synthetic Nat.zero guarded caller."),

    (r"def nz_guarded_step : iota_step (red_rec nz_env) nz_input nz_raw_result :=
 natREnv_iota_zero (Level.succ Level.zero) nz_motive natZeroC nz_minor", "The actual guarded iota operator steps the typed caller to its raw triple application; no beta steps are conflated with iota."),

    (r"def nz_raw_result_typed : TypingCtxConvIn nz_env (natTEnv Level.zero) (ListType.nil KExpr) nz_raw_result natTypeC :=
 TypingCtxConvIn.conv nz_env (natTEnv Level.zero) (ListType.nil KExpr) nz_raw_result (KExpr.app nz_motive natZeroC) natTypeC (TypingCtxConvIn.app nz_env (natTEnv Level.zero) (ListType.nil KExpr) (KExpr.app (KExpr.app (natRecRhsZero (Level.succ Level.zero)) nz_motive) natZeroC) nz_minor nz_minor_type (KExpr.app nz_motive natZeroC) (TypingCtxConvIn.app nz_env (natTEnv Level.zero) (ListType.nil KExpr) (KExpr.app (natRecRhsZero (Level.succ Level.zero)) nz_motive) natZeroC (KExpr.app nz_motive natZeroC) (KExpr.pi nz_minor_type (KExpr.app nz_motive natZeroC)) (TypingCtxConvIn.app nz_env (natTEnv Level.zero) (ListType.nil KExpr) (natRecRhsZero (Level.succ Level.zero)) nz_motive (natMotiveTy (Level.succ Level.zero)) (KExpr.pi (KExpr.app (KExpr.bvar Nat.zero) natZeroC) (KExpr.pi natRecSArm (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) natZeroC))) (nz_typing_to_semantic nz_env (natTEnv Level.zero) (ListType.nil KExpr) (natRecRhsZero (Level.succ Level.zero)) (nz_rule_type (Level.succ Level.zero)) (nz_rhs_typed (Level.succ Level.zero))) nz_motive_argument_typed) nz_zero_argument_typed) nz_minor_argument_typed) (nz_motive_beta natZeroC)", "The raw guarded contractum is independently typed from the RHS and argument typings, not by assuming subject reduction."),
];

// Static classification preserves the original declaration order. The proof
// entries explicitly desugar declaration binders into forall/fun; registration
// neither parses prototype text nor mutates status after inserting a declaration.
// Seven computational data definitions retain the ordinary declaration path.
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
        name: "nz_rule_type",
    },
    Registration::Proof {
        declaration_index: 1,
        name: "nz_nat_typed",
        type_src: r"forall (G : ListType KExpr),
 TypingCtx (natTEnv Level.zero) G natTypeC (KExpr.sort (Level.succ Level.zero))",
        value_src: r"fun (G : ListType KExpr) =>
 TypingCtx.const (natTEnv Level.zero) G natName (ListType.nil Level) (KExpr.sort (Level.succ Level.zero)) (Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.sort (Level.succ Level.zero))))",
    },
    Registration::Proof {
        declaration_index: 2,
        name: "nz_zero_typed",
        type_src: r"forall (G : ListType KExpr),
 TypingCtx (natTEnv Level.zero) G natZeroC natTypeC",
        value_src: r"fun (G : ListType KExpr) =>
 TypingCtx.const (natTEnv Level.zero) G zeroName (ListType.nil Level) natTypeC (Eq.refl (OptionType KExpr) (OptionType.some KExpr natTypeC))",
    },
    Registration::Proof {
        declaration_index: 3,
        name: "nz_succ_typed",
        type_src: r"forall (G : ListType KExpr),
 TypingCtx (natTEnv Level.zero) G natSuccC (KExpr.pi natTypeC natTypeC)",
        value_src: r"fun (G : ListType KExpr) =>
 TypingCtx.const (natTEnv Level.zero) G succName (ListType.nil Level) (KExpr.pi natTypeC natTypeC) (Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.pi natTypeC natTypeC)))",
    },
    Registration::Proof {
        declaration_index: 4,
        name: "nz_motive_typed",
        type_src: r"forall (u : Level) (G : ListType KExpr),
 TypingCtx (natTEnv Level.zero) G (natMotiveTy u) (KExpr.sort (Level.imax (Level.succ Level.zero) (Level.succ u)))",
        value_src: r"fun (u : Level) (G : ListType KExpr) =>
 TypingCtx.pi (natTEnv Level.zero) G natTypeC (KExpr.sort u) (Level.succ Level.zero) (Level.succ u) (nz_nat_typed G) (TypingCtx.sort (natTEnv Level.zero) (ListType.cons KExpr natTypeC G) u)",
    },
    Registration::Proof {
        declaration_index: 5,
        name: "nz_zero_domain_typed",
        type_src: r"forall (u : Level),
 TypingCtx (natTEnv Level.zero) (ListType.cons KExpr (natMotiveTy u) (ListType.nil KExpr)) (KExpr.app (KExpr.bvar Nat.zero) natZeroC) (KExpr.sort u)",
        value_src: r"fun (u : Level) =>
 (TypingCtx.app (natTEnv Level.zero) (ListType.cons KExpr (natMotiveTy u) (ListType.nil KExpr)) (KExpr.bvar Nat.zero) natZeroC natTypeC (KExpr.sort u) (TypingCtx.var (natTEnv Level.zero) (ListType.cons KExpr (natMotiveTy u) (ListType.nil KExpr)) Nat.zero (natMotiveTy u) (Eq.refl (OptionType KExpr) (OptionType.some KExpr (natMotiveTy u)))) (nz_zero_typed (ListType.cons KExpr (natMotiveTy u) (ListType.nil KExpr))))",
    },
    Registration::Proof {
        declaration_index: 6,
        name: "nz_sarm_typed",
        type_src: r"forall (u : Level),
 TypingCtx (natTEnv Level.zero) (ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) natZeroC) (ListType.cons KExpr (natMotiveTy u) (ListType.nil KExpr))) natRecSArm (KExpr.sort (Level.imax (Level.succ Level.zero) (Level.imax u u)))",
        value_src: r"fun (u : Level) =>
 TypingCtx.pi (natTEnv Level.zero) (ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) natZeroC) (ListType.cons KExpr (natMotiveTy u) (ListType.nil KExpr))) natTypeC (KExpr.pi (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.app natSuccC (KExpr.bvar (Nat.succ Nat.zero))))) (Level.succ Level.zero) (Level.imax u u) (nz_nat_typed (ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) natZeroC) (ListType.cons KExpr (natMotiveTy u) (ListType.nil KExpr)))) (TypingCtx.pi (natTEnv Level.zero) (ListType.cons KExpr natTypeC (ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) natZeroC) (ListType.cons KExpr (natMotiveTy u) (ListType.nil KExpr)))) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.app natSuccC (KExpr.bvar (Nat.succ Nat.zero)))) u u (TypingCtx.app (natTEnv Level.zero) (ListType.cons KExpr natTypeC (ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) natZeroC) (ListType.cons KExpr (natMotiveTy u) (ListType.nil KExpr)))) (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero) natTypeC (KExpr.sort u) (TypingCtx.var (natTEnv Level.zero) (ListType.cons KExpr natTypeC (ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) natZeroC) (ListType.cons KExpr (natMotiveTy u) (ListType.nil KExpr)))) (Nat.succ (Nat.succ Nat.zero)) (natMotiveTy u) (Eq.refl (OptionType KExpr) (OptionType.some KExpr (natMotiveTy u)))) (TypingCtx.var (natTEnv Level.zero) (ListType.cons KExpr natTypeC (ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) natZeroC) (ListType.cons KExpr (natMotiveTy u) (ListType.nil KExpr)))) Nat.zero natTypeC (Eq.refl (OptionType KExpr) (OptionType.some KExpr natTypeC)))) (TypingCtx.app (natTEnv Level.zero) (ListType.cons KExpr (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (ListType.cons KExpr natTypeC (ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) natZeroC) (ListType.cons KExpr (natMotiveTy u) (ListType.nil KExpr))))) (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.app natSuccC (KExpr.bvar (Nat.succ Nat.zero))) natTypeC (KExpr.sort u) (TypingCtx.var (natTEnv Level.zero) (ListType.cons KExpr (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (ListType.cons KExpr natTypeC (ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) natZeroC) (ListType.cons KExpr (natMotiveTy u) (ListType.nil KExpr))))) (Nat.succ (Nat.succ (Nat.succ Nat.zero))) (natMotiveTy u) (Eq.refl (OptionType KExpr) (OptionType.some KExpr (natMotiveTy u)))) (TypingCtx.app (natTEnv Level.zero) (ListType.cons KExpr (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (ListType.cons KExpr natTypeC (ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) natZeroC) (ListType.cons KExpr (natMotiveTy u) (ListType.nil KExpr))))) natSuccC (KExpr.bvar (Nat.succ Nat.zero)) natTypeC natTypeC (nz_succ_typed (ListType.cons KExpr (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (ListType.cons KExpr natTypeC (ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) natZeroC) (ListType.cons KExpr (natMotiveTy u) (ListType.nil KExpr)))))) (TypingCtx.var (natTEnv Level.zero) (ListType.cons KExpr (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) (KExpr.bvar Nat.zero)) (ListType.cons KExpr natTypeC (ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) natZeroC) (ListType.cons KExpr (natMotiveTy u) (ListType.nil KExpr))))) (Nat.succ Nat.zero) natTypeC (Eq.refl (OptionType KExpr) (OptionType.some KExpr natTypeC))))))",
    },
    Registration::Proof {
        declaration_index: 7,
        name: "nz_rhs_typed",
        type_src: r"forall (u : Level),
 TypingCtx (natTEnv Level.zero) (ListType.nil KExpr) (natRecRhsZero u) (nz_rule_type u)",
        value_src: r"fun (u : Level) =>
 (TypingCtx.lam (natTEnv Level.zero) (ListType.nil KExpr) (natMotiveTy u) (KExpr.lam (KExpr.app (KExpr.bvar Nat.zero) natZeroC) (KExpr.lam natRecSArm (KExpr.bvar (Nat.succ Nat.zero)))) (KExpr.pi (KExpr.app (KExpr.bvar Nat.zero) natZeroC) (KExpr.pi natRecSArm (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) natZeroC))) (Level.imax (Level.succ Level.zero) (Level.succ u)) (nz_motive_typed u (ListType.nil KExpr)) (TypingCtx.lam (natTEnv Level.zero) (ListType.cons KExpr (natMotiveTy u) (ListType.nil KExpr)) (KExpr.app (KExpr.bvar Nat.zero) natZeroC) (KExpr.lam natRecSArm (KExpr.bvar (Nat.succ Nat.zero))) (KExpr.pi natRecSArm (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) natZeroC)) u (nz_zero_domain_typed u) (TypingCtx.lam (natTEnv Level.zero) (ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) natZeroC) (ListType.cons KExpr (natMotiveTy u) (ListType.nil KExpr))) natRecSArm (KExpr.bvar (Nat.succ Nat.zero)) (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) natZeroC) (Level.imax (Level.succ Level.zero) (Level.imax u u)) (nz_sarm_typed u) (TypingCtx.var (natTEnv Level.zero) (ListType.cons KExpr natRecSArm (ListType.cons KExpr (KExpr.app (KExpr.bvar Nat.zero) natZeroC) (ListType.cons KExpr (natMotiveTy u) (ListType.nil KExpr)))) (Nat.succ Nat.zero) (KExpr.app (KExpr.bvar Nat.zero) natZeroC) (Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.app (KExpr.bvar Nat.zero) natZeroC)))))))",
    },
    Registration::Proof {
        declaration_index: 8,
        name: "nz_stored_rhs_typed",
        type_src: r"TypingCtx (natTEnv Level.zero) (ListType.nil KExpr) (natRecRhsZero (Level.param Name.anonymous)) (nz_rule_type (Level.param Name.anonymous))",
        value_src: r"nz_rhs_typed (Level.param Name.anonymous)",
    },
    Registration::Proof {
        declaration_index: 9,
        name: "nz_typing_to_semantic",
        type_src: r"forall (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr) (e : KExpr) (T : KExpr) (h : TypingCtx tenv G e T),
 TypingCtxConvIn R tenv G e T",
        value_src: r"fun (R : RedEnv) (tenv : KDeclEnv)
 (G : ListType KExpr) (e : KExpr) (T : KExpr) (h : TypingCtx tenv G e T) =>
 TypingCtx.rec tenv
  (fun (G0 : ListType KExpr) (e0 : KExpr) (T0 : KExpr) (_h : TypingCtx tenv G0 e0 T0) =>
   TypingCtxConvIn R tenv G0 e0 T0)
  (fun (G0 : ListType KExpr) (i : Nat) (A : KExpr)
   (lookup : Eq (OptionType KExpr) (ctx_lookup G0 i) (OptionType.some KExpr A)) =>
    TypingCtxConvIn.var R tenv G0 i A lookup)
  (fun (G0 : ListType KExpr) (u : Level) => TypingCtxConvIn.sort R tenv G0 u)
  (fun (G0 : ListType KExpr) (A : KExpr) (B : KExpr) (u : Level) (v : Level)
   (_hA : TypingCtx tenv G0 A (KExpr.sort u))
   (_hB : TypingCtx tenv (ListType.cons KExpr A G0) B (KExpr.sort v))
   (ihA : TypingCtxConvIn R tenv G0 A (KExpr.sort u))
   (ihB : TypingCtxConvIn R tenv (ListType.cons KExpr A G0) B (KExpr.sort v)) =>
   TypingCtxConvIn.pi R tenv G0 A B u v ihA ihB)
  (fun (G0 : ListType KExpr) (A : KExpr) (b : KExpr) (B : KExpr) (u : Level)
   (_hA : TypingCtx tenv G0 A (KExpr.sort u))
   (_hb : TypingCtx tenv (ListType.cons KExpr A G0) b B)
   (ihA : TypingCtxConvIn R tenv G0 A (KExpr.sort u))
   (ihb : TypingCtxConvIn R tenv (ListType.cons KExpr A G0) b B) =>
   TypingCtxConvIn.lam R tenv G0 A b B u ihA ihb)
  (fun (G0 : ListType KExpr) (f : KExpr) (a : KExpr) (A : KExpr) (B : KExpr)
   (_hf : TypingCtx tenv G0 f (KExpr.pi A B)) (_ha : TypingCtx tenv G0 a A)
   (ihf : TypingCtxConvIn R tenv G0 f (KExpr.pi A B))
   (iha : TypingCtxConvIn R tenv G0 a A) =>
   TypingCtxConvIn.app R tenv G0 f a A B ihf iha)
  (fun (G0 : ListType KExpr) (n : Name) (us : ListType Level) (A : KExpr)
   (lookup : Eq (OptionType KExpr) (kdecl_type_at tenv n us) (OptionType.some KExpr A)) =>
   TypingCtxConvIn.const R tenv G0 n us A lookup)
  (fun (G0 : ListType KExpr) (A : KExpr) (v : KExpr) (b : KExpr) (B : KExpr) (u : Level)
   (_hA : TypingCtx tenv G0 A (KExpr.sort u)) (_hv : TypingCtx tenv G0 v A)
   (_hb : TypingCtx tenv (ListType.cons KExpr A G0) b B)
   (ihA : TypingCtxConvIn R tenv G0 A (KExpr.sort u))
   (ihv : TypingCtxConvIn R tenv G0 v A)
   (ihb : TypingCtxConvIn R tenv (ListType.cons KExpr A G0) b B) =>
   TypingCtxConvIn.let_ R tenv G0 A v b B u ihA ihv ihb)
  G e T h",
    },
    Registration::Data {
        declaration_index: 10,
        name: "nz_env",
    },
    Registration::Data {
        declaration_index: 11,
        name: "nz_motive",
    },
    Registration::Data {
        declaration_index: 12,
        name: "nz_minor",
    },
    Registration::Data {
        declaration_index: 13,
        name: "nz_minor_type",
    },
    Registration::Proof {
        declaration_index: 14,
        name: "nz_motive_core_typed",
        type_src: r"TypingCtx (natTEnv Level.zero) (ListType.nil KExpr) nz_motive (natMotiveTy (Level.succ Level.zero))",
        value_src: r"TypingCtx.lam (natTEnv Level.zero) (ListType.nil KExpr) natTypeC natTypeC (KExpr.sort (Level.succ Level.zero)) (Level.succ Level.zero)
 (nz_nat_typed (ListType.nil KExpr)) (nz_nat_typed (ListType.cons KExpr natTypeC (ListType.nil KExpr)))",
    },
    Registration::Proof {
        declaration_index: 15,
        name: "nz_minor_core_typed",
        type_src: r"TypingCtx (natTEnv Level.zero) (ListType.nil KExpr) nz_minor (KExpr.pi natTypeC (KExpr.pi natTypeC natTypeC))",
        value_src: r"TypingCtx.lam (natTEnv Level.zero) (ListType.nil KExpr) natTypeC (KExpr.lam natTypeC (KExpr.app natSuccC (KExpr.bvar Nat.zero))) (KExpr.pi natTypeC natTypeC) (Level.succ Level.zero)
 (nz_nat_typed (ListType.nil KExpr))
 (TypingCtx.lam (natTEnv Level.zero) (ListType.cons KExpr natTypeC (ListType.nil KExpr)) natTypeC (KExpr.app natSuccC (KExpr.bvar Nat.zero)) natTypeC (Level.succ Level.zero)
  (nz_nat_typed (ListType.cons KExpr natTypeC (ListType.nil KExpr)))
  (TypingCtx.app (natTEnv Level.zero) (ListType.cons KExpr natTypeC (ListType.cons KExpr natTypeC (ListType.nil KExpr))) natSuccC (KExpr.bvar Nat.zero) natTypeC natTypeC
   (nz_succ_typed (ListType.cons KExpr natTypeC (ListType.cons KExpr natTypeC (ListType.nil KExpr))))
   (TypingCtx.var (natTEnv Level.zero) (ListType.cons KExpr natTypeC (ListType.cons KExpr natTypeC (ListType.nil KExpr))) Nat.zero natTypeC (Eq.refl (OptionType KExpr) (OptionType.some KExpr natTypeC)))))",
    },
    Registration::Proof {
        declaration_index: 16,
        name: "nz_motive_beta",
        type_src: r"forall (x : KExpr),
 DefEqIn nz_env (KExpr.app nz_motive x) natTypeC",
        value_src: r"fun (x : KExpr) =>
 def_eq_in_beta nz_env natTypeC natTypeC x",
    },
    Registration::Proof {
        declaration_index: 17,
        name: "nz_minor_type_conversion",
        type_src: r"DefEqIn nz_env (KExpr.pi natTypeC (KExpr.pi natTypeC natTypeC)) nz_minor_type",
        value_src: r"DefEqIn.pi nz_env natTypeC natTypeC (KExpr.pi natTypeC natTypeC) (KExpr.pi (KExpr.app nz_motive (KExpr.bvar Nat.zero)) (KExpr.app nz_motive (KExpr.app natSuccC (KExpr.bvar (Nat.succ Nat.zero)))))
  (DefEqIn.refl nz_env natTypeC)
  (DefEqIn.pi nz_env natTypeC (KExpr.app nz_motive (KExpr.bvar Nat.zero)) natTypeC (KExpr.app nz_motive (KExpr.app natSuccC (KExpr.bvar (Nat.succ Nat.zero))))
   (DefEqIn.symm nz_env (KExpr.app nz_motive (KExpr.bvar Nat.zero)) natTypeC (nz_motive_beta (KExpr.bvar Nat.zero)))
   (DefEqIn.symm nz_env (KExpr.app nz_motive (KExpr.app natSuccC (KExpr.bvar (Nat.succ Nat.zero)))) natTypeC (nz_motive_beta (KExpr.app natSuccC (KExpr.bvar (Nat.succ Nat.zero))))))",
    },
    Registration::Proof {
        declaration_index: 18,
        name: "nz_motive_argument_typed",
        type_src: r"TypingCtxConvIn nz_env (natTEnv Level.zero) (ListType.nil KExpr) nz_motive (natMotiveTy (Level.succ Level.zero))",
        value_src: r"(nz_typing_to_semantic nz_env (natTEnv Level.zero) (ListType.nil KExpr) nz_motive (natMotiveTy (Level.succ Level.zero)) nz_motive_core_typed)",
    },
    Registration::Proof {
        declaration_index: 19,
        name: "nz_zero_argument_typed",
        type_src: r"TypingCtxConvIn nz_env (natTEnv Level.zero) (ListType.nil KExpr) natZeroC (KExpr.app nz_motive natZeroC)",
        value_src: r"TypingCtxConvIn.conv nz_env (natTEnv Level.zero) (ListType.nil KExpr) natZeroC natTypeC (KExpr.app nz_motive natZeroC)
  (nz_typing_to_semantic nz_env (natTEnv Level.zero) (ListType.nil KExpr) natZeroC natTypeC (nz_zero_typed (ListType.nil KExpr)))
  (DefEqIn.symm nz_env (KExpr.app nz_motive natZeroC) natTypeC (nz_motive_beta natZeroC))",
    },
    Registration::Proof {
        declaration_index: 20,
        name: "nz_minor_argument_typed",
        type_src: r"TypingCtxConvIn nz_env (natTEnv Level.zero) (ListType.nil KExpr) nz_minor nz_minor_type",
        value_src: r"TypingCtxConvIn.conv nz_env (natTEnv Level.zero) (ListType.nil KExpr) nz_minor (KExpr.pi natTypeC (KExpr.pi natTypeC natTypeC)) nz_minor_type
  (nz_typing_to_semantic nz_env (natTEnv Level.zero) (ListType.nil KExpr) nz_minor (KExpr.pi natTypeC (KExpr.pi natTypeC natTypeC)) nz_minor_core_typed) nz_minor_type_conversion",
    },
    Registration::Data {
        declaration_index: 21,
        name: "nz_input",
    },
    Registration::Proof {
        declaration_index: 22,
        name: "nz_input_typed",
        type_src: r"TypingCtxConvIn nz_env (natTEnv Level.zero) (ListType.nil KExpr) nz_input natTypeC",
        value_src: r"TypingCtxConvIn.conv nz_env (natTEnv Level.zero) (ListType.nil KExpr) nz_input (KExpr.app nz_motive natZeroC) natTypeC (TypingCtxConvIn.app nz_env (natTEnv Level.zero) (ListType.nil KExpr) (KExpr.app (KExpr.app (KExpr.app (natRecC (Level.succ Level.zero)) nz_motive) natZeroC) nz_minor) natZeroC natTypeC (KExpr.app nz_motive (KExpr.bvar Nat.zero)) (TypingCtxConvIn.app nz_env (natTEnv Level.zero) (ListType.nil KExpr) (KExpr.app (KExpr.app (natRecC (Level.succ Level.zero)) nz_motive) natZeroC) nz_minor nz_minor_type (KExpr.pi natTypeC (KExpr.app nz_motive (KExpr.bvar Nat.zero))) (TypingCtxConvIn.app nz_env (natTEnv Level.zero) (ListType.nil KExpr) (KExpr.app (natRecC (Level.succ Level.zero)) nz_motive) natZeroC (KExpr.app nz_motive natZeroC) (KExpr.pi nz_minor_type (KExpr.pi natTypeC (KExpr.app nz_motive (KExpr.bvar Nat.zero)))) (TypingCtxConvIn.app nz_env (natTEnv Level.zero) (ListType.nil KExpr) (natRecC (Level.succ Level.zero)) nz_motive (natMotiveTy (Level.succ Level.zero)) (KExpr.pi (KExpr.app (KExpr.bvar Nat.zero) natZeroC) (KExpr.pi natRecSArm (KExpr.pi natTypeC (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) (KExpr.bvar Nat.zero))))) (nz_typing_to_semantic nz_env (natTEnv Level.zero) (ListType.nil KExpr) (natRecC (Level.succ Level.zero)) (natRecTy (Level.succ Level.zero)) (natTEnv_rec_typed (Level.succ Level.zero))) nz_motive_argument_typed) nz_zero_argument_typed) nz_minor_argument_typed) (nz_typing_to_semantic nz_env (natTEnv Level.zero) (ListType.nil KExpr) natZeroC natTypeC (nz_zero_typed (ListType.nil KExpr)))) (nz_motive_beta natZeroC)",
    },
    Registration::Data {
        declaration_index: 23,
        name: "nz_raw_result",
    },
    Registration::Proof {
        declaration_index: 24,
        name: "nz_guarded_step",
        type_src: r"iota_step (red_rec nz_env) nz_input nz_raw_result",
        value_src: r"natREnv_iota_zero (Level.succ Level.zero) nz_motive natZeroC nz_minor",
    },
    Registration::Proof {
        declaration_index: 25,
        name: "nz_raw_result_typed",
        type_src: r"TypingCtxConvIn nz_env (natTEnv Level.zero) (ListType.nil KExpr) nz_raw_result natTypeC",
        value_src: r"TypingCtxConvIn.conv nz_env (natTEnv Level.zero) (ListType.nil KExpr) nz_raw_result (KExpr.app nz_motive natZeroC) natTypeC (TypingCtxConvIn.app nz_env (natTEnv Level.zero) (ListType.nil KExpr) (KExpr.app (KExpr.app (natRecRhsZero (Level.succ Level.zero)) nz_motive) natZeroC) nz_minor nz_minor_type (KExpr.app nz_motive natZeroC) (TypingCtxConvIn.app nz_env (natTEnv Level.zero) (ListType.nil KExpr) (KExpr.app (natRecRhsZero (Level.succ Level.zero)) nz_motive) natZeroC (KExpr.app nz_motive natZeroC) (KExpr.pi nz_minor_type (KExpr.app nz_motive natZeroC)) (TypingCtxConvIn.app nz_env (natTEnv Level.zero) (ListType.nil KExpr) (natRecRhsZero (Level.succ Level.zero)) nz_motive (natMotiveTy (Level.succ Level.zero)) (KExpr.pi (KExpr.app (KExpr.bvar Nat.zero) natZeroC) (KExpr.pi natRecSArm (KExpr.app (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))) natZeroC))) (nz_typing_to_semantic nz_env (natTEnv Level.zero) (ListType.nil KExpr) (natRecRhsZero (Level.succ Level.zero)) (nz_rule_type (Level.succ Level.zero)) (nz_rhs_typed (Level.succ Level.zero))) nz_motive_argument_typed) nz_zero_argument_typed) nz_minor_argument_typed) (nz_motive_beta natZeroC)",
    },
];

impl Specification {
    /// After actual Nat objects/typing/guarded rules and semantic acceptance.
    /// The late full-model stage supplies these dependencies without broadening
    /// either reduced bundle or introducing any new environment hypothesis.
    pub(super) fn add_nat_zero_rhs_typing(&mut self) -> Result<(), SpecError> {
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

    const PROOF_ROOTS: &[&str] = &[
        "nz_nat_typed",
        "nz_zero_typed",
        "nz_succ_typed",
        "nz_motive_typed",
        "nz_zero_domain_typed",
        "nz_sarm_typed",
        "nz_rhs_typed",
        "nz_stored_rhs_typed",
        "nz_typing_to_semantic",
        "nz_motive_core_typed",
        "nz_minor_core_typed",
        "nz_motive_beta",
        "nz_minor_type_conversion",
        "nz_motive_argument_typed",
        "nz_zero_argument_typed",
        "nz_minor_argument_typed",
        "nz_input_typed",
        "nz_guarded_step",
        "nz_raw_result_typed",
    ];

    const NEGATIVE_CONTROLS: &[&str] = &[
        "def nz_forged_raw_type : TypingCtxConvIn nz_env (natTEnv Level.zero) (ListType.nil KExpr) nz_raw_result (KExpr.sort Level.zero) := nz_raw_result_typed",
        "def nz_forged_beta_as_iota : iota_step (red_rec nz_env) nz_input natZeroC := nz_guarded_step",
        "def nz_forged_erased_universe : iota_step (red_rec nz_env) nz_input (KExpr.app (KExpr.app (KExpr.app (natRecRhsZero Level.zero) nz_motive) natZeroC) nz_minor) := nz_guarded_step",
    ];

    #[test]
    fn nat_zero_rhs_typing_sources_parse() {
        for (source, _) in DECLARATIONS {
            parse_check(source).expect("actual typed-rule declaration parses");
        }
        for registration in REGISTRATIONS {
            if let Registration::Proof {
                name,
                type_src,
                value_src,
                ..
            } = registration
            {
                parse_check(&format!("def {name} : {type_src} := {value_src}"))
                    .expect("explicit checked proof record parses");
            }
        }
        for source in NEGATIVE_CONTROLS {
            parse_check(source).expect("forged proof is syntactically well formed");
        }
    }

    /// Use the real parser's source spans, not a registration-time text parser,
    /// to check that only the declaration-binder sugar changed. The result type,
    /// proof body and every binder are the original prototype text.
    #[test]
    fn nat_zero_rhs_typing_explicit_records_preserve_prototype_bodies() {
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
    fn nat_zero_rhs_typing_is_checked_without_coherence_or_output_oracles() {
        run_with_stack(|| {
            let spec = build_spec_with_stack();
            for (source, _) in DECLARATIONS {
                let name = source.split_whitespace().nth(1).expect("definition name");
                let definition = spec
                    .definitions()
                    .get(name)
                    .expect("registered declaration");
                assert!(!definition.is_axiom, "{name}");
                assert!(definition.elaborated_value.is_some(), "{name}");
                let kernel_name = clean_kernel::Name::from_string(name);
                let constant = spec
                    .env()
                    .get_const(&kernel_name)
                    .expect("every registered declaration exists in the kernel environment");
                assert_ne!(constant.kind, clean_kernel::ConstantKind::Axiom, "{name}");
                assert!(constant.value.is_some(), "{name}: kernel value exists");
                assert_eq!(
                    Some(&constant.type_),
                    definition.elaborated_type.as_ref(),
                    "{name}: kernel and metadata types agree"
                );
                assert_eq!(
                    constant.value.as_ref(),
                    definition.elaborated_value.as_ref(),
                    "{name}: kernel and metadata values agree"
                );
                assert!(
                    spec.env()
                        .foundational_axiom_deps(&kernel_name)
                        .expect("actual kernel root has an axiom closure")
                        .is_empty(),
                    "{name}: no foundational axioms either"
                );
                assert!(
                    crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty(),
                    "{name}"
                );
            }
            for name in PROOF_ROOTS {
                let definition = spec.definitions().get(*name).expect("actual proof root");
                assert_eq!(definition.category, AxiomCategory::DerivedLemma, "{name}");
                assert_eq!(
                    definition.proof_status,
                    ProofStatus::DerivedProved,
                    "{name}"
                );
                spec.verify_definition(name)
                    .expect("actual typed-rule proof rechecks");
            }
            for registration in REGISTRATIONS {
                if let Registration::Data { name, .. } = registration {
                    let definition = spec
                        .definitions()
                        .get(*name)
                        .expect("actual data definition");
                    assert_eq!(
                        definition.proof_status,
                        ProofStatus::DerivedPending,
                        "{name}: data is not a proved theorem"
                    );
                    let constant = spec
                        .env()
                        .get_const(&clean_kernel::Name::from_string(name))
                        .expect("registered data constant");
                    assert_eq!(
                        constant.kind,
                        clean_kernel::ConstantKind::Definition,
                        "{name}: computational data remains unfoldable"
                    );
                }
            }
            for name in ["nz_rhs_typed", "nz_input_typed", "nz_raw_result_typed"] {
                let definition = spec.definitions().get(name).expect("actual terminal proof");
                let ty = &definition.type_src;
                let value = definition.value_src.as_deref().expect("actual proof body");
                for forbidden in [
                    "TypingEnvCoherent",
                    "CandModel",
                    "tec_iota_typed",
                    "substitution_general",
                ] {
                    assert!(
                        !ty.contains(forbidden) && !value.contains(forbidden),
                        "{name}: {forbidden}"
                    );
                }
            }
        });
    }

    #[test]
    fn nat_zero_rhs_typing_rejects_wrong_type_beta_shortcut_and_erased_universe() {
        run_with_stack(|| {
            let mut spec = build_spec_with_stack();
            for source in NEGATIVE_CONTROLS {
                let error = spec
                    .add_recursive_def(source, "Deliberately forged typed iota claim.")
                    .expect_err("actual wrong type, raw step, or universe must be rejected");
                assert!(format!("{error:?}").contains("Type mismatch"), "{error:?}");
            }
        });
    }
}

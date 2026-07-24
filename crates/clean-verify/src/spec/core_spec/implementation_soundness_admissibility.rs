// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Admissibility inversion lemmas for implementation-soundness case proofs (#461).
//!
//! The production kernel's recursive infer/check steps reuse immediate
//! subexpressions such as `App` function/argument terms and lambda/Pi parameter
//! types. The specification-level `KernelInputAdmissible` predicate is reducible
//! to `is_closed`, so recursive case proofs need constructive inversion lemmas
//! that recover those closed subexpressions from a closed composite term.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::Specification;

/// Inline KExpr.rec discriminator: non-App -> Nat, App -> Empty.
/// (let_ minor returns Nat — a let is not an App.)
const KEXPR_NOT_APP_INLINE: &str = concat!(
    "(KExpr.rec (fun (_ : KExpr) => Type) ",
    "(fun (_ : Level) => Nat) ",
    "(fun (_ : Nat) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Empty) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : Name) (_ : ListType Level) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Type) => Nat) ",
    "(fun (_ : Nat) => Nat))"
);

/// Inline KExpr.rec discriminator: non-Lam -> Nat, Lam -> Empty.
/// (let_ minor returns Nat — a let is not a Lam.)
const KEXPR_NOT_LAM_INLINE: &str = concat!(
    "(KExpr.rec (fun (_ : KExpr) => Type) ",
    "(fun (_ : Level) => Nat) ",
    "(fun (_ : Nat) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Empty) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : Name) (_ : ListType Level) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Type) => Nat) ",
    "(fun (_ : Nat) => Nat))"
);

/// Inline KExpr.rec discriminator: non-Pi -> Nat, Pi -> Empty.
/// (let_ minor returns Nat — a let is not a Pi.)
const KEXPR_NOT_PI_INLINE: &str = concat!(
    "(KExpr.rec (fun (_ : KExpr) => Type) ",
    "(fun (_ : Level) => Nat) ",
    "(fun (_ : Nat) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Empty) ",
    "(fun (_ : Name) (_ : ListType Level) => Nat) ",
    "(fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) (_ : Type) => Nat) ",
    "(fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Type) => Nat) ",
    "(fun (_ : Nat) => Nat))"
);

impl Specification {
    pub(super) fn add_implementation_soundness_admissibility(&mut self) -> Result<(), SpecError> {
        self.add_is_closed_at_app_inversions()?;
        self.add_is_closed_at_lam_inversions()?;
        self.add_is_closed_at_pi_inversions()?;
        self.add_kernel_input_admissibility_wrappers()?;
        Ok(())
    }

    fn add_is_closed_at_app_inversions(&mut self) -> Result<(), SpecError> {
        self.add_is_closed_at_app_fun()?;
        self.add_is_closed_at_app_arg()?;
        Ok(())
    }

    fn add_is_closed_at_app_fun(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "is_closed_at_app_fun".to_string(),
            type_src: "forall (f : KExpr) (a : KExpr) (d : Nat), is_closed_at (KExpr.app f a) d -> is_closed_at f d".to_string(),
            value_src: Some(format!(concat!(
                "fun (f : KExpr) (a : KExpr) (d : Nat) ",
                "(h : is_closed_at (KExpr.app f a) d) => ",
                "is_closed_at.rec ",
                "(fun (e : KExpr) (depth : Nat) (_hc : is_closed_at e depth) => ",
                "Eq KExpr e (KExpr.app f a) -> is_closed_at f depth) ",
                "(fun (n : Level) (depth : Nat) ",
                "(eq : Eq KExpr (KExpr.sort n) (KExpr.app f a)) => ",
                "Empty.rec (fun (_ : Empty) => is_closed_at f depth) ",
                "(Eq.substType KExpr {discr} ",
                "(KExpr.sort n) (KExpr.app f a) eq Nat.zero)) ",
                "(fun (i : Nat) (depth : Nat) (_hlt : Lt i depth) ",
                "(eq : Eq KExpr (KExpr.bvar i) (KExpr.app f a)) => ",
                "Empty.rec (fun (_ : Empty) => is_closed_at f depth) ",
                "(Eq.substType KExpr {discr} ",
                "(KExpr.bvar i) (KExpr.app f a) eq Nat.zero)) ",
                "(fun (f0 : KExpr) (a0 : KExpr) (depth : Nat) ",
                "(hf0 : is_closed_at f0 depth) (_ha0 : is_closed_at a0 depth) ",
                "(_ihf : Eq KExpr f0 (KExpr.app f a) -> is_closed_at f depth) ",
                "(_iha : Eq KExpr a0 (KExpr.app f a) -> is_closed_at f depth) ",
                "(eq : Eq KExpr (KExpr.app f0 a0) (KExpr.app f a)) => ",
                "Eq.substType KExpr (fun (x : KExpr) => is_closed_at x depth) ",
                "f0 f (app_inj_fst f0 a0 f a eq) hf0) ",
                "(fun (A : KExpr) (body : KExpr) (depth : Nat) ",
                "(_hA : is_closed_at A depth) (_hbody : is_closed_at body (Nat.succ depth)) ",
                "(_ihA : Eq KExpr A (KExpr.app f a) -> is_closed_at f depth) ",
                "(_ihbody : Eq KExpr body (KExpr.app f a) -> is_closed_at f (Nat.succ depth)) ",
                "(eq : Eq KExpr (KExpr.lam A body) (KExpr.app f a)) => ",
                "Empty.rec (fun (_ : Empty) => is_closed_at f depth) ",
                "(Eq.substType KExpr {discr} ",
                "(KExpr.lam A body) (KExpr.app f a) eq Nat.zero)) ",
                "(fun (A : KExpr) (body : KExpr) (depth : Nat) ",
                "(_hA : is_closed_at A depth) (_hbody : is_closed_at body (Nat.succ depth)) ",
                "(_ihA : Eq KExpr A (KExpr.app f a) -> is_closed_at f depth) ",
                "(_ihbody : Eq KExpr body (KExpr.app f a) -> is_closed_at f (Nat.succ depth)) ",
                "(eq : Eq KExpr (KExpr.pi A body) (KExpr.app f a)) => ",
                "Empty.rec (fun (_ : Empty) => is_closed_at f depth) ",
                "(Eq.substType KExpr {discr} ",
                "(KExpr.pi A body) (KExpr.app f a) eq Nat.zero)) ",
                "(fun (n : Name) (us : ListType Level) (depth : Nat) ",
                "(eq : Eq KExpr (KExpr.const n us) (KExpr.app f a)) => ",
                "Empty.rec (fun (_ : Empty) => is_closed_at f depth) ",
                "(Eq.substType KExpr {discr} ",
                "(KExpr.const n us) (KExpr.app f a) eq Nat.zero)) ",
                "(fun (ty : KExpr) (val : KExpr) (body : KExpr) (depth : Nat) ",
                "(_hty : is_closed_at ty depth) (_hval : is_closed_at val depth) ",
                "(_hbody : is_closed_at body (Nat.succ depth)) ",
                "(_ihty : Eq KExpr ty (KExpr.app f a) -> is_closed_at f depth) ",
                "(_ihval : Eq KExpr val (KExpr.app f a) -> is_closed_at f depth) ",
                "(_ihbody : Eq KExpr body (KExpr.app f a) -> is_closed_at f (Nat.succ depth)) ",
                "(eq : Eq KExpr (KExpr.let_ ty val body) (KExpr.app f a)) => ",
                "Empty.rec (fun (_ : Empty) => is_closed_at f depth) ",
                "(Eq.substType KExpr {discr} ",
                "(KExpr.let_ ty val body) (KExpr.app f a) eq Nat.zero)) ",
                "(fun (s : Name) (i : Nat) (sub : KExpr) (depth : Nat) ",
                "(_hsub : is_closed_at sub depth) ",
                "(_ihsub : Eq KExpr sub (KExpr.app f a) -> is_closed_at f depth) ",
                "(eq : Eq KExpr (KExpr.proj s i sub) (KExpr.app f a)) => ",
                "Empty.rec (fun (_ : Empty) => is_closed_at f depth) ",
                "(Eq.substType KExpr {discr} ",
                "(KExpr.proj s i sub) (KExpr.app f a) eq Nat.zero)) ",
                "(fun (v : Nat) (depth : Nat) ",
                "(eq : Eq KExpr (KExpr.lit v) (KExpr.app f a)) => ",
                "Empty.rec (fun (_ : Empty) => is_closed_at f depth) ",
                "(Eq.substType KExpr {discr} ",
                "(KExpr.lit v) (KExpr.app f a) eq Nat.zero)) ",
                "(KExpr.app f a) d h (Eq.refl KExpr (KExpr.app f a))"
            ), discr = KEXPR_NOT_APP_INLINE)),
            is_axiom: false,
            description: "Closed app terms have closed function subexpressions: invert is_closed_at.app constructively via is_closed_at.rec and App injectivity. Part of #461.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "is_closed_at.rec".to_string(),
                "app_inj_fst".to_string(),
                "Eq.substType".to_string(),
                "Eq.refl".to_string(),
                "KExpr.rec".to_string(),
                "Empty.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        Ok(())
    }

    fn add_is_closed_at_app_arg(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "is_closed_at_app_arg".to_string(),
            type_src: "forall (f : KExpr) (a : KExpr) (d : Nat), is_closed_at (KExpr.app f a) d -> is_closed_at a d".to_string(),
            value_src: Some(format!(concat!(
                "fun (f : KExpr) (a : KExpr) (d : Nat) ",
                "(h : is_closed_at (KExpr.app f a) d) => ",
                "is_closed_at.rec ",
                "(fun (e : KExpr) (depth : Nat) (_hc : is_closed_at e depth) => ",
                "Eq KExpr e (KExpr.app f a) -> is_closed_at a depth) ",
                "(fun (n : Level) (depth : Nat) ",
                "(eq : Eq KExpr (KExpr.sort n) (KExpr.app f a)) => ",
                "Empty.rec (fun (_ : Empty) => is_closed_at a depth) ",
                "(Eq.substType KExpr {discr} ",
                "(KExpr.sort n) (KExpr.app f a) eq Nat.zero)) ",
                "(fun (i : Nat) (depth : Nat) (_hlt : Lt i depth) ",
                "(eq : Eq KExpr (KExpr.bvar i) (KExpr.app f a)) => ",
                "Empty.rec (fun (_ : Empty) => is_closed_at a depth) ",
                "(Eq.substType KExpr {discr} ",
                "(KExpr.bvar i) (KExpr.app f a) eq Nat.zero)) ",
                "(fun (f0 : KExpr) (a0 : KExpr) (depth : Nat) ",
                "(_hf0 : is_closed_at f0 depth) (ha0 : is_closed_at a0 depth) ",
                "(_ihf : Eq KExpr f0 (KExpr.app f a) -> is_closed_at a depth) ",
                "(_iha : Eq KExpr a0 (KExpr.app f a) -> is_closed_at a depth) ",
                "(eq : Eq KExpr (KExpr.app f0 a0) (KExpr.app f a)) => ",
                "Eq.substType KExpr (fun (x : KExpr) => is_closed_at x depth) ",
                "a0 a (app_inj_snd f0 a0 f a eq) ha0) ",
                "(fun (A : KExpr) (body : KExpr) (depth : Nat) ",
                "(_hA : is_closed_at A depth) (_hbody : is_closed_at body (Nat.succ depth)) ",
                "(_ihA : Eq KExpr A (KExpr.app f a) -> is_closed_at a depth) ",
                "(_ihbody : Eq KExpr body (KExpr.app f a) -> is_closed_at a (Nat.succ depth)) ",
                "(eq : Eq KExpr (KExpr.lam A body) (KExpr.app f a)) => ",
                "Empty.rec (fun (_ : Empty) => is_closed_at a depth) ",
                "(Eq.substType KExpr {discr} ",
                "(KExpr.lam A body) (KExpr.app f a) eq Nat.zero)) ",
                "(fun (A : KExpr) (body : KExpr) (depth : Nat) ",
                "(_hA : is_closed_at A depth) (_hbody : is_closed_at body (Nat.succ depth)) ",
                "(_ihA : Eq KExpr A (KExpr.app f a) -> is_closed_at a depth) ",
                "(_ihbody : Eq KExpr body (KExpr.app f a) -> is_closed_at a (Nat.succ depth)) ",
                "(eq : Eq KExpr (KExpr.pi A body) (KExpr.app f a)) => ",
                "Empty.rec (fun (_ : Empty) => is_closed_at a depth) ",
                "(Eq.substType KExpr {discr} ",
                "(KExpr.pi A body) (KExpr.app f a) eq Nat.zero)) ",
                "(fun (n : Name) (us : ListType Level) (depth : Nat) ",
                "(eq : Eq KExpr (KExpr.const n us) (KExpr.app f a)) => ",
                "Empty.rec (fun (_ : Empty) => is_closed_at a depth) ",
                "(Eq.substType KExpr {discr} ",
                "(KExpr.const n us) (KExpr.app f a) eq Nat.zero)) ",
                "(fun (ty : KExpr) (val : KExpr) (body : KExpr) (depth : Nat) ",
                "(_hty : is_closed_at ty depth) (_hval : is_closed_at val depth) ",
                "(_hbody : is_closed_at body (Nat.succ depth)) ",
                "(_ihty : Eq KExpr ty (KExpr.app f a) -> is_closed_at a depth) ",
                "(_ihval : Eq KExpr val (KExpr.app f a) -> is_closed_at a depth) ",
                "(_ihbody : Eq KExpr body (KExpr.app f a) -> is_closed_at a (Nat.succ depth)) ",
                "(eq : Eq KExpr (KExpr.let_ ty val body) (KExpr.app f a)) => ",
                "Empty.rec (fun (_ : Empty) => is_closed_at a depth) ",
                "(Eq.substType KExpr {discr} ",
                "(KExpr.let_ ty val body) (KExpr.app f a) eq Nat.zero)) ",
                "(fun (s : Name) (i : Nat) (sub : KExpr) (depth : Nat) ",
                "(_hsub : is_closed_at sub depth) ",
                "(_ihsub : Eq KExpr sub (KExpr.app f a) -> is_closed_at a depth) ",
                "(eq : Eq KExpr (KExpr.proj s i sub) (KExpr.app f a)) => ",
                "Empty.rec (fun (_ : Empty) => is_closed_at a depth) ",
                "(Eq.substType KExpr {discr} ",
                "(KExpr.proj s i sub) (KExpr.app f a) eq Nat.zero)) ",
                "(fun (v : Nat) (depth : Nat) ",
                "(eq : Eq KExpr (KExpr.lit v) (KExpr.app f a)) => ",
                "Empty.rec (fun (_ : Empty) => is_closed_at a depth) ",
                "(Eq.substType KExpr {discr} ",
                "(KExpr.lit v) (KExpr.app f a) eq Nat.zero)) ",
                "(KExpr.app f a) d h (Eq.refl KExpr (KExpr.app f a))"
            ), discr = KEXPR_NOT_APP_INLINE)),
            is_axiom: false,
            description: "Closed app terms have closed argument subexpressions: invert is_closed_at.app constructively via is_closed_at.rec and App injectivity. Part of #461.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "is_closed_at.rec".to_string(),
                "app_inj_snd".to_string(),
                "Eq.substType".to_string(),
                "Eq.refl".to_string(),
                "KExpr.rec".to_string(),
                "Empty.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    fn add_is_closed_at_lam_inversions(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "is_closed_at_lam_type".to_string(),
            type_src: "forall (A : KExpr) (body : KExpr) (d : Nat), is_closed_at (KExpr.lam A body) d -> is_closed_at A d".to_string(),
            value_src: Some(format!(concat!(
                "fun (A : KExpr) (body : KExpr) (d : Nat) ",
                "(h : is_closed_at (KExpr.lam A body) d) => ",
                "is_closed_at.rec ",
                "(fun (e : KExpr) (depth : Nat) (_hc : is_closed_at e depth) => ",
                "Eq KExpr e (KExpr.lam A body) -> is_closed_at A depth) ",
                "(fun (n : Level) (depth : Nat) ",
                "(eq : Eq KExpr (KExpr.sort n) (KExpr.lam A body)) => ",
                "Empty.rec (fun (_ : Empty) => is_closed_at A depth) ",
                "(Eq.substType KExpr {discr} ",
                "(KExpr.sort n) (KExpr.lam A body) eq Nat.zero)) ",
                "(fun (i : Nat) (depth : Nat) (_hlt : Lt i depth) ",
                "(eq : Eq KExpr (KExpr.bvar i) (KExpr.lam A body)) => ",
                "Empty.rec (fun (_ : Empty) => is_closed_at A depth) ",
                "(Eq.substType KExpr {discr} ",
                "(KExpr.bvar i) (KExpr.lam A body) eq Nat.zero)) ",
                "(fun (f : KExpr) (a : KExpr) (depth : Nat) ",
                "(_hf : is_closed_at f depth) (_ha : is_closed_at a depth) ",
                "(_ihf : Eq KExpr f (KExpr.lam A body) -> is_closed_at A depth) ",
                "(_iha : Eq KExpr a (KExpr.lam A body) -> is_closed_at A depth) ",
                "(eq : Eq KExpr (KExpr.app f a) (KExpr.lam A body)) => ",
                "Empty.rec (fun (_ : Empty) => is_closed_at A depth) ",
                "(Eq.substType KExpr {discr} ",
                "(KExpr.app f a) (KExpr.lam A body) eq Nat.zero)) ",
                "(fun (A0 : KExpr) (body0 : KExpr) (depth : Nat) ",
                "(hA0 : is_closed_at A0 depth) (_hbody0 : is_closed_at body0 (Nat.succ depth)) ",
                "(_ihA0 : Eq KExpr A0 (KExpr.lam A body) -> is_closed_at A depth) ",
                "(_ihbody0 : Eq KExpr body0 (KExpr.lam A body) -> is_closed_at A (Nat.succ depth)) ",
                "(eq : Eq KExpr (KExpr.lam A0 body0) (KExpr.lam A body)) => ",
                "Eq.substType KExpr (fun (x : KExpr) => is_closed_at x depth) ",
                "A0 A (lam_inj_fst A0 body0 A body eq) hA0) ",
                "(fun (A0 : KExpr) (body0 : KExpr) (depth : Nat) ",
                "(_hA0 : is_closed_at A0 depth) (_hbody0 : is_closed_at body0 (Nat.succ depth)) ",
                "(_ihA0 : Eq KExpr A0 (KExpr.lam A body) -> is_closed_at A depth) ",
                "(_ihbody0 : Eq KExpr body0 (KExpr.lam A body) -> is_closed_at A (Nat.succ depth)) ",
                "(eq : Eq KExpr (KExpr.pi A0 body0) (KExpr.lam A body)) => ",
                "Empty.rec (fun (_ : Empty) => is_closed_at A depth) ",
                "(Eq.substType KExpr {discr} ",
                "(KExpr.pi A0 body0) (KExpr.lam A body) eq Nat.zero)) ",
                "(fun (n : Name) (us : ListType Level) (depth : Nat) ",
                "(eq : Eq KExpr (KExpr.const n us) (KExpr.lam A body)) => ",
                "Empty.rec (fun (_ : Empty) => is_closed_at A depth) ",
                "(Eq.substType KExpr {discr} ",
                "(KExpr.const n us) (KExpr.lam A body) eq Nat.zero)) ",
                "(fun (ty0 : KExpr) (val0 : KExpr) (body0 : KExpr) (depth : Nat) ",
                "(_hty0 : is_closed_at ty0 depth) (_hval0 : is_closed_at val0 depth) ",
                "(_hbody0 : is_closed_at body0 (Nat.succ depth)) ",
                "(_ihty0 : Eq KExpr ty0 (KExpr.lam A body) -> is_closed_at A depth) ",
                "(_ihval0 : Eq KExpr val0 (KExpr.lam A body) -> is_closed_at A depth) ",
                "(_ihbody0 : Eq KExpr body0 (KExpr.lam A body) -> is_closed_at A (Nat.succ depth)) ",
                "(eq : Eq KExpr (KExpr.let_ ty0 val0 body0) (KExpr.lam A body)) => ",
                "Empty.rec (fun (_ : Empty) => is_closed_at A depth) ",
                "(Eq.substType KExpr {discr} ",
                "(KExpr.let_ ty0 val0 body0) (KExpr.lam A body) eq Nat.zero)) ",
                "(fun (s : Name) (i : Nat) (sub : KExpr) (depth : Nat) ",
                "(_hsub : is_closed_at sub depth) ",
                "(_ihsub : Eq KExpr sub (KExpr.lam A body) -> is_closed_at A depth) ",
                "(eq : Eq KExpr (KExpr.proj s i sub) (KExpr.lam A body)) => ",
                "Empty.rec (fun (_ : Empty) => is_closed_at A depth) ",
                "(Eq.substType KExpr {discr} ",
                "(KExpr.proj s i sub) (KExpr.lam A body) eq Nat.zero)) ",
                "(fun (v : Nat) (depth : Nat) ",
                "(eq : Eq KExpr (KExpr.lit v) (KExpr.lam A body)) => ",
                "Empty.rec (fun (_ : Empty) => is_closed_at A depth) ",
                "(Eq.substType KExpr {discr} ",
                "(KExpr.lit v) (KExpr.lam A body) eq Nat.zero)) ",
                "(KExpr.lam A body) d h (Eq.refl KExpr (KExpr.lam A body))"
            ), discr = KEXPR_NOT_LAM_INLINE)),
            is_axiom: false,
            description: "Closed lambda terms have closed parameter types: invert is_closed_at.lam constructively via is_closed_at.rec and Lam injectivity. Part of #461.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "is_closed_at.rec".to_string(),
                "lam_inj_fst".to_string(),
                "Eq.substType".to_string(),
                "Eq.refl".to_string(),
                "KExpr.rec".to_string(),
                "Empty.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    fn add_is_closed_at_pi_inversions(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "is_closed_at_pi_type".to_string(),
            type_src: "forall (A : KExpr) (body : KExpr) (d : Nat), is_closed_at (KExpr.pi A body) d -> is_closed_at A d".to_string(),
            value_src: Some(format!(concat!(
                "fun (A : KExpr) (body : KExpr) (d : Nat) ",
                "(h : is_closed_at (KExpr.pi A body) d) => ",
                "is_closed_at.rec ",
                "(fun (e : KExpr) (depth : Nat) (_hc : is_closed_at e depth) => ",
                "Eq KExpr e (KExpr.pi A body) -> is_closed_at A depth) ",
                "(fun (n : Level) (depth : Nat) ",
                "(eq : Eq KExpr (KExpr.sort n) (KExpr.pi A body)) => ",
                "Empty.rec (fun (_ : Empty) => is_closed_at A depth) ",
                "(Eq.substType KExpr {discr} ",
                "(KExpr.sort n) (KExpr.pi A body) eq Nat.zero)) ",
                "(fun (i : Nat) (depth : Nat) (_hlt : Lt i depth) ",
                "(eq : Eq KExpr (KExpr.bvar i) (KExpr.pi A body)) => ",
                "Empty.rec (fun (_ : Empty) => is_closed_at A depth) ",
                "(Eq.substType KExpr {discr} ",
                "(KExpr.bvar i) (KExpr.pi A body) eq Nat.zero)) ",
                "(fun (f : KExpr) (a : KExpr) (depth : Nat) ",
                "(_hf : is_closed_at f depth) (_ha : is_closed_at a depth) ",
                "(_ihf : Eq KExpr f (KExpr.pi A body) -> is_closed_at A depth) ",
                "(_iha : Eq KExpr a (KExpr.pi A body) -> is_closed_at A depth) ",
                "(eq : Eq KExpr (KExpr.app f a) (KExpr.pi A body)) => ",
                "Empty.rec (fun (_ : Empty) => is_closed_at A depth) ",
                "(Eq.substType KExpr {discr} ",
                "(KExpr.app f a) (KExpr.pi A body) eq Nat.zero)) ",
                "(fun (A0 : KExpr) (body0 : KExpr) (depth : Nat) ",
                "(_hA0 : is_closed_at A0 depth) (_hbody0 : is_closed_at body0 (Nat.succ depth)) ",
                "(_ihA0 : Eq KExpr A0 (KExpr.pi A body) -> is_closed_at A depth) ",
                "(_ihbody0 : Eq KExpr body0 (KExpr.pi A body) -> is_closed_at A (Nat.succ depth)) ",
                "(eq : Eq KExpr (KExpr.lam A0 body0) (KExpr.pi A body)) => ",
                "Empty.rec (fun (_ : Empty) => is_closed_at A depth) ",
                "(Eq.substType KExpr {discr} ",
                "(KExpr.lam A0 body0) (KExpr.pi A body) eq Nat.zero)) ",
                "(fun (A0 : KExpr) (body0 : KExpr) (depth : Nat) ",
                "(hA0 : is_closed_at A0 depth) (_hbody0 : is_closed_at body0 (Nat.succ depth)) ",
                "(_ihA0 : Eq KExpr A0 (KExpr.pi A body) -> is_closed_at A depth) ",
                "(_ihbody0 : Eq KExpr body0 (KExpr.pi A body) -> is_closed_at A (Nat.succ depth)) ",
                "(eq : Eq KExpr (KExpr.pi A0 body0) (KExpr.pi A body)) => ",
                "Eq.substType KExpr (fun (x : KExpr) => is_closed_at x depth) ",
                "A0 A (pi_inj_fst A0 body0 A body eq) hA0) ",
                "(fun (n : Name) (us : ListType Level) (depth : Nat) ",
                "(eq : Eq KExpr (KExpr.const n us) (KExpr.pi A body)) => ",
                "Empty.rec (fun (_ : Empty) => is_closed_at A depth) ",
                "(Eq.substType KExpr {discr} ",
                "(KExpr.const n us) (KExpr.pi A body) eq Nat.zero)) ",
                "(fun (ty0 : KExpr) (val0 : KExpr) (body0 : KExpr) (depth : Nat) ",
                "(_hty0 : is_closed_at ty0 depth) (_hval0 : is_closed_at val0 depth) ",
                "(_hbody0 : is_closed_at body0 (Nat.succ depth)) ",
                "(_ihty0 : Eq KExpr ty0 (KExpr.pi A body) -> is_closed_at A depth) ",
                "(_ihval0 : Eq KExpr val0 (KExpr.pi A body) -> is_closed_at A depth) ",
                "(_ihbody0 : Eq KExpr body0 (KExpr.pi A body) -> is_closed_at A (Nat.succ depth)) ",
                "(eq : Eq KExpr (KExpr.let_ ty0 val0 body0) (KExpr.pi A body)) => ",
                "Empty.rec (fun (_ : Empty) => is_closed_at A depth) ",
                "(Eq.substType KExpr {discr} ",
                "(KExpr.let_ ty0 val0 body0) (KExpr.pi A body) eq Nat.zero)) ",
                "(fun (s : Name) (i : Nat) (sub : KExpr) (depth : Nat) ",
                "(_hsub : is_closed_at sub depth) ",
                "(_ihsub : Eq KExpr sub (KExpr.pi A body) -> is_closed_at A depth) ",
                "(eq : Eq KExpr (KExpr.proj s i sub) (KExpr.pi A body)) => ",
                "Empty.rec (fun (_ : Empty) => is_closed_at A depth) ",
                "(Eq.substType KExpr {discr} ",
                "(KExpr.proj s i sub) (KExpr.pi A body) eq Nat.zero)) ",
                "(fun (v : Nat) (depth : Nat) ",
                "(eq : Eq KExpr (KExpr.lit v) (KExpr.pi A body)) => ",
                "Empty.rec (fun (_ : Empty) => is_closed_at A depth) ",
                "(Eq.substType KExpr {discr} ",
                "(KExpr.lit v) (KExpr.pi A body) eq Nat.zero)) ",
                "(KExpr.pi A body) d h (Eq.refl KExpr (KExpr.pi A body))"
            ), discr = KEXPR_NOT_PI_INLINE)),
            is_axiom: false,
            description: "Closed Pi terms have closed domain types: invert is_closed_at.pi constructively via is_closed_at.rec and Pi injectivity. Part of #461.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "is_closed_at.rec".to_string(),
                "pi_inj_fst".to_string(),
                "Eq.substType".to_string(),
                "Eq.refl".to_string(),
                "KExpr.rec".to_string(),
                "Empty.rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

#[cfg(test)]
#[path = "implementation_soundness_admissibility_tests.rs"]
mod implementation_soundness_admissibility_tests;

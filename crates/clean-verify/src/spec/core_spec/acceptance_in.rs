// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! An additive, environment-indexed semantic acceptance target.
//!
//! These are model judgments, not extracted Rust execution. The explicit R is
//! shared by finite reduction traces, conversion, inference, and typing. The
//! older fixed-environment DefEq and its syntactic confluence results remain
//! unchanged. Production environment validity and the still-missing kernel
//! operations are separate obligations.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

const CONVERSION: &str = r"inductive DefEqIn (R : RedEnv) : KExpr -> KExpr -> Type
| refl : forall (e : KExpr), DefEqIn R e e
| symm : forall (e : KExpr) (e' : KExpr), DefEqIn R e e' -> DefEqIn R e' e
| trans : forall (e : KExpr) (m : KExpr) (e' : KExpr), DefEqIn R e m -> DefEqIn R m e' -> DefEqIn R e e'
| raw : forall (e : KExpr) (e' : KExpr), par_reduces_cd R e e' -> DefEqIn R e e'
| levels : forall (e : KExpr) (e' : KExpr), KExprUniverseEq e e' -> DefEqIn R e e'
| app : forall (f : KExpr) (f' : KExpr) (a : KExpr) (a' : KExpr), DefEqIn R f f' -> DefEqIn R a a' -> DefEqIn R (KExpr.app f a) (KExpr.app f' a')
| lam : forall (A : KExpr) (A' : KExpr) (b : KExpr) (b' : KExpr), DefEqIn R A A' -> DefEqIn R b b' -> DefEqIn R (KExpr.lam A b) (KExpr.lam A' b')
| pi : forall (A : KExpr) (A' : KExpr) (B : KExpr) (B' : KExpr), DefEqIn R A A' -> DefEqIn R B B' -> DefEqIn R (KExpr.pi A B) (KExpr.pi A' B')
| let_ : forall (A : KExpr) (A' : KExpr) (v : KExpr) (v' : KExpr) (b : KExpr) (b' : KExpr), DefEqIn R A A' -> DefEqIn R v v' -> DefEqIn R b b' -> DefEqIn R (KExpr.let_ A v b) (KExpr.let_ A' v' b')
| proj : forall (n : Name) (i : Nat) (e : KExpr) (e' : KExpr), DefEqIn R e e' -> DefEqIn R (KExpr.proj n i e) (KExpr.proj n i e')";

const TYPING: &str = r"inductive TypingCtxConvIn (R : RedEnv) (tenv : KDeclEnv) : ListType KExpr -> KExpr -> KExpr -> Type
| var : forall (G : ListType KExpr) (i : Nat) (A : KExpr), @Eq (OptionType KExpr) (ctx_lookup G i) (@OptionType.some KExpr A) -> TypingCtxConvIn R tenv G (KExpr.bvar i) (lift_at A Nat.zero (Nat.succ i))
| sort : forall (G : ListType KExpr) (u : Level), TypingCtxConvIn R tenv G (KExpr.sort u) (KExpr.sort (Level.succ u))
| pi : forall (G : ListType KExpr) (A : KExpr) (B : KExpr) (u : Level) (v : Level), TypingCtxConvIn R tenv G A (KExpr.sort u) -> TypingCtxConvIn R tenv (@ListType.cons KExpr A G) B (KExpr.sort v) -> TypingCtxConvIn R tenv G (KExpr.pi A B) (KExpr.sort (Level.imax u v))
| lam : forall (G : ListType KExpr) (A : KExpr) (b : KExpr) (B : KExpr) (u : Level), TypingCtxConvIn R tenv G A (KExpr.sort u) -> TypingCtxConvIn R tenv (@ListType.cons KExpr A G) b B -> TypingCtxConvIn R tenv G (KExpr.lam A b) (KExpr.pi A B)
| app : forall (G : ListType KExpr) (f : KExpr) (a : KExpr) (A : KExpr) (B : KExpr), TypingCtxConvIn R tenv G f (KExpr.pi A B) -> TypingCtxConvIn R tenv G a A -> TypingCtxConvIn R tenv G (KExpr.app f a) (instantiate B a)
| const : forall (G : ListType KExpr) (n : Name) (us : ListType Level) (A : KExpr), @Eq (OptionType KExpr) (kdecl_type_at tenv n us) (@OptionType.some KExpr A) -> TypingCtxConvIn R tenv G (KExpr.const n us) A
| conv : forall (G : ListType KExpr) (e : KExpr) (A : KExpr) (B : KExpr), TypingCtxConvIn R tenv G e A -> DefEqIn R A B -> TypingCtxConvIn R tenv G e B
| let_ : forall (G : ListType KExpr) (A : KExpr) (v : KExpr) (b : KExpr) (B : KExpr) (u : Level), TypingCtxConvIn R tenv G A (KExpr.sort u) -> TypingCtxConvIn R tenv G v A -> TypingCtxConvIn R tenv (@ListType.cons KExpr A G) b B -> TypingCtxConvIn R tenv G (KExpr.let_ A v b) (instantiate B v)
| lit_nat : forall (G : ListType KExpr) (n : Nat), TypingCtxConvIn R tenv G (literal_nat n) literal_nat_type
| lit_string : forall (G : ListType KExpr) (n : Nat), TypingCtxConvIn R tenv G (literal_string n) literal_string_type";

const INFERENCE: &str = r"inductive KernelInfersIn (R : RedEnv) (tenv : KDeclEnv) : ListType KExpr -> KExpr -> KExpr -> Type
| sort : forall (G : ListType KExpr) (u : Level), KernelInfersIn R tenv G (KExpr.sort u) (KExpr.sort (Level.succ u))
| bvar : forall (G : ListType KExpr) (i : Nat) (A : KExpr), @Eq (OptionType KExpr) (ctx_lookup G i) (@OptionType.some KExpr A) -> KernelInfersIn R tenv G (KExpr.bvar i) (lift_at A Nat.zero (Nat.succ i))
| pi : forall (G : ListType KExpr) (A : KExpr) (B : KExpr) (SA : KExpr) (u : Level) (SB : KExpr) (v : Level) (r : Level), KernelInfersIn R tenv G A SA -> whnf_red_step_star R SA (KExpr.sort u) -> KernelInfersIn R tenv (@ListType.cons KExpr A G) B SB -> whnf_red_step_star R SB (KExpr.sort v) -> levelEqSem (Level.imax u v) r -> KernelInfersIn R tenv G (KExpr.pi A B) (KExpr.sort r)
| lam : forall (G : ListType KExpr) (A : KExpr) (b : KExpr) (B : KExpr) (SA : KExpr) (u : Level), KernelInfersIn R tenv G A SA -> whnf_red_step_star R SA (KExpr.sort u) -> KernelInfersIn R tenv (@ListType.cons KExpr A G) b B -> KernelInfersIn R tenv G (KExpr.lam A b) (KExpr.pi A B)
| const : forall (G : ListType KExpr) (n : Name) (us : ListType Level) (A : KExpr) (T : KExpr), @Eq (OptionType KExpr) (kdecl_type_at tenv n us) (@OptionType.some KExpr A) -> KExprUniverseEq A T -> KernelInfersIn R tenv G (KExpr.const n us) T
| app : forall (G : ListType KExpr) (f : KExpr) (a : KExpr) (F : KExpr) (A : KExpr) (B : KExpr) (A' : KExpr), KernelInfersIn R tenv G f F -> whnf_red_step_star R F (KExpr.pi A B) -> KernelInfersIn R tenv G a A' -> DefEqIn R A' A -> KernelInfersIn R tenv G (KExpr.app f a) (instantiate B a)
| let_ : forall (G : ListType KExpr) (A : KExpr) (v : KExpr) (b : KExpr) (Ty : KExpr) (u : Level) (Tv : KExpr) (B : KExpr), KernelInfersIn R tenv G A Ty -> whnf_red_step_star R Ty (KExpr.sort u) -> KernelInfersIn R tenv G v Tv -> DefEqIn R Tv A -> KernelInfersIn R tenv (@ListType.cons KExpr A G) b B -> KernelInfersIn R tenv G (KExpr.let_ A v b) (instantiate B v)
| lit_nat : forall (G : ListType KExpr) (n : Nat), KernelInfersIn R tenv G (literal_nat n) literal_nat_type
| lit_string : forall (G : ListType KExpr) (n : Nat), KernelInfersIn R tenv G (literal_string n) literal_string_type";

pub(super) fn theorem(
    spec: &mut Specification,
    name: &str,
    type_src: &str,
    value_src: &str,
    description: &str,
) -> Result<(), SpecError> {
    spec.add_definition(SpecDefinition {
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
    })
}

impl Specification {
    pub(super) fn add_acceptance_in(&mut self) -> Result<(), SpecError> {
        self.add_inductive(CONVERSION, "Conversion over an explicit reduction environment: equivalence and congruence closure of raw computational parallel reduction and structural semantic-universe equivalence. No syntactic sort injectivity or common raw reduct is asserted.")?;
        self.add_inductive(TYPING, "Declarative model typing with the same explicit reduction environment in conversion. Arbitrary type environments and contexts are parameters, not established production-valid environments. Projection typing and other missing production rules remain open.")?;
        self.add_inductive(INFERENCE, "Environment-parametric algorithmic model using finite successful reduction traces. Pi accepts a semantically justified smart universe result, and constants require exact guarded signature lookup plus universe-only result correspondence, not an assumed typing derivation. This relation is not extracted Rust execution.")?;
        theorem(
            self,
            "whnf_red_step_star_to_def_eq_in",
            "forall (R : RedEnv) (e : KExpr) (e' : KExpr), whnf_red_step_star R e e' -> DefEqIn R e e'",
            r"fun (R : RedEnv) (e : KExpr) (e' : KExpr) (h : whnf_red_step_star R e e') =>
@whnf_red_step_star.rec R
  (fun (x : KExpr) (y : KExpr) (_h : whnf_red_step_star R x y) => DefEqIn R x y)
  (fun (x : KExpr) => @DefEqIn.refl R x)
  (fun (x : KExpr) (y : KExpr) (z : KExpr) (step : whnf_red_step R x y)
    (_tail : whnf_red_step_star R y z) (ih : DefEqIn R y z) =>
      @DefEqIn.trans R x y z (@DefEqIn.raw R x y (whnf_red_step_to_par_cd R x y step)) ih)
  e e' h",
            "Every finite modeled weak-head trace gives conversion under the same arbitrary R, using the existing generic one-step bridge. No termination, CandModel, environment coherence, or fixed-seed assumption is needed for this inclusion.",
        )?;
        self.add_acceptance_in_sound()?;
        theorem(
            self,
            "kernel_infers_in_pi_smart",
            r"forall (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr)
(A : KExpr) (B : KExpr) (SA : KExpr) (u : Level) (SB : KExpr) (v : Level),
KernelInfersIn R tenv G A SA -> whnf_red_step_star R SA (KExpr.sort u) ->
KernelInfersIn R tenv (@ListType.cons KExpr A G) B SB -> whnf_red_step_star R SB (KExpr.sort v) ->
KernelInfersIn R tenv G (KExpr.pi A B) (KExpr.sort (level_imax u v))",
            r"fun (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr)
(A : KExpr) (B : KExpr) (SA : KExpr) (u : Level) (SB : KExpr) (v : Level)
(ha : KernelInfersIn R tenv G A SA) (hwa : whnf_red_step_star R SA (KExpr.sort u))
(hb : KernelInfersIn R tenv (@ListType.cons KExpr A G) B SB) (hwb : whnf_red_step_star R SB (KExpr.sort v)) =>
@KernelInfersIn.pi R tenv G A B SA u SB v (level_imax u v) ha hwa hb hwb
  (levelEqSem_symm (level_imax u v) (Level.imax u v) (level_imax_eq_sem u v))",
            "The actual modeled smart imax function supplies the Pi result; its semantic correctness premise is derived, not carried. This function is not yet a source-refinement model of every Rust max/is_geq branch.",
        )?;
        self.add_acceptance_in_witnesses()
    }

    fn add_acceptance_in_sound(&mut self) -> Result<(), SpecError> {
        theorem(
            self,
            "kernel_infers_in_sound",
            "forall (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr) (e : KExpr) (T : KExpr), KernelInfersIn R tenv G e T -> TypingCtxConvIn R tenv G e T",
            r"fun (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr) (e : KExpr) (T : KExpr)
(h : KernelInfersIn R tenv G e T) =>
@KernelInfersIn.rec R tenv
  (fun (G0 : ListType KExpr) (e0 : KExpr) (T0 : KExpr)
    (_h : KernelInfersIn R tenv G0 e0 T0) => TypingCtxConvIn R tenv G0 e0 T0)
  (fun (G0 : ListType KExpr) (u : Level) => @TypingCtxConvIn.sort R tenv G0 u)
  (fun (G0 : ListType KExpr) (i : Nat) (A : KExpr)
    (get : @Eq (OptionType KExpr) (ctx_lookup G0 i) (@OptionType.some KExpr A)) =>
      @TypingCtxConvIn.var R tenv G0 i A get)
  (fun (G0 : ListType KExpr) (A : KExpr) (B : KExpr) (SA : KExpr) (u : Level)
    (SB : KExpr) (v : Level) (r : Level)
    (_ha : KernelInfersIn R tenv G0 A SA) (hwa : whnf_red_step_star R SA (KExpr.sort u))
    (_hb : KernelInfersIn R tenv (@ListType.cons KExpr A G0) B SB)
    (hwb : whnf_red_step_star R SB (KExpr.sort v)) (hr : levelEqSem (Level.imax u v) r)
    (iha : TypingCtxConvIn R tenv G0 A SA)
    (ihb : TypingCtxConvIn R tenv (@ListType.cons KExpr A G0) B SB) =>
      @TypingCtxConvIn.conv R tenv G0 (KExpr.pi A B) (KExpr.sort (Level.imax u v)) (KExpr.sort r)
        (@TypingCtxConvIn.pi R tenv G0 A B u v
          (@TypingCtxConvIn.conv R tenv G0 A SA (KExpr.sort u) iha (whnf_red_step_star_to_def_eq_in R SA (KExpr.sort u) hwa))
          (@TypingCtxConvIn.conv R tenv (@ListType.cons KExpr A G0) B SB (KExpr.sort v) ihb (whnf_red_step_star_to_def_eq_in R SB (KExpr.sort v) hwb)))
        (@DefEqIn.levels R (KExpr.sort (Level.imax u v)) (KExpr.sort r) (KExprUniverseEq.sort (Level.imax u v) r hr)))
  (fun (G0 : ListType KExpr) (A : KExpr) (b : KExpr) (B : KExpr) (SA : KExpr) (u : Level)
    (_ha : KernelInfersIn R tenv G0 A SA) (hwa : whnf_red_step_star R SA (KExpr.sort u))
    (_hb : KernelInfersIn R tenv (@ListType.cons KExpr A G0) b B)
    (iha : TypingCtxConvIn R tenv G0 A SA)
    (ihb : TypingCtxConvIn R tenv (@ListType.cons KExpr A G0) b B) =>
      @TypingCtxConvIn.lam R tenv G0 A b B u
        (@TypingCtxConvIn.conv R tenv G0 A SA (KExpr.sort u) iha (whnf_red_step_star_to_def_eq_in R SA (KExpr.sort u) hwa)) ihb)
  (fun (G0 : ListType KExpr) (n : Name) (us : ListType Level) (A : KExpr) (T0 : KExpr)
    (get : @Eq (OptionType KExpr) (kdecl_type_at tenv n us) (@OptionType.some KExpr A))
    (result : KExprUniverseEq A T0) =>
      @TypingCtxConvIn.conv R tenv G0 (KExpr.const n us) A T0
        (@TypingCtxConvIn.const R tenv G0 n us A get) (@DefEqIn.levels R A T0 result))
  (fun (G0 : ListType KExpr) (f : KExpr) (a : KExpr) (F : KExpr) (A : KExpr) (B : KExpr) (A' : KExpr)
    (_hf : KernelInfersIn R tenv G0 f F) (hw : whnf_red_step_star R F (KExpr.pi A B))
    (_ha : KernelInfersIn R tenv G0 a A') (heq : DefEqIn R A' A)
    (ihf : TypingCtxConvIn R tenv G0 f F) (iha : TypingCtxConvIn R tenv G0 a A') =>
      @TypingCtxConvIn.app R tenv G0 f a A B
        (@TypingCtxConvIn.conv R tenv G0 f F (KExpr.pi A B) ihf (whnf_red_step_star_to_def_eq_in R F (KExpr.pi A B) hw))
        (@TypingCtxConvIn.conv R tenv G0 a A' A iha heq))
  (fun (G0 : ListType KExpr) (A : KExpr) (v : KExpr) (b : KExpr) (Ty : KExpr) (u : Level) (Tv : KExpr) (B : KExpr)
    (_ht : KernelInfersIn R tenv G0 A Ty) (hw : whnf_red_step_star R Ty (KExpr.sort u))
    (_hv : KernelInfersIn R tenv G0 v Tv) (heq : DefEqIn R Tv A)
    (_hb : KernelInfersIn R tenv (@ListType.cons KExpr A G0) b B)
    (iht : TypingCtxConvIn R tenv G0 A Ty) (ihv : TypingCtxConvIn R tenv G0 v Tv)
    (ihb : TypingCtxConvIn R tenv (@ListType.cons KExpr A G0) b B) =>
      @TypingCtxConvIn.let_ R tenv G0 A v b B u
        (@TypingCtxConvIn.conv R tenv G0 A Ty (KExpr.sort u) iht (whnf_red_step_star_to_def_eq_in R Ty (KExpr.sort u) hw))
        (@TypingCtxConvIn.conv R tenv G0 v Tv A ihv heq) ihb)
  (fun (G0 : ListType KExpr) (n : Nat) => @TypingCtxConvIn.lit_nat R tenv G0 n)
  (fun (G0 : ListType KExpr) (n : Nat) => @TypingCtxConvIn.lit_string R tenv G0 n)
  G e T h",
            "Soundness of the environment-indexed inference model by induction on its actual nine constructors. Finite traces justify conversions at the same R; Pi and constant result correspondence use only universe equivalence. This is not production source correspondence or proof that arbitrary supplied environments are valid.",
        )
    }

    fn add_acceptance_in_witnesses(&mut self) -> Result<(), SpecError> {
        theorem(
            self,
            "acceptance_imax_one_one",
            "levelEqSem (Level.imax (Level.succ Level.zero) (Level.succ Level.zero)) (Level.succ Level.zero)",
            "fun (v : Name -> Nat) => @Eq.refl Nat (Nat.succ Nat.zero)",
            "Concrete semantic equality for the smart Pi result: imax(1,1) and 1 are not the same raw Level constructor tree.",
        )?;
        theorem(
            self,
            "kernel_infers_in_pi_one",
            "forall (R : RedEnv) (tenv : KDeclEnv), KernelInfersIn R tenv (@ListType.nil KExpr) (KExpr.pi (KExpr.sort Level.zero) (KExpr.sort Level.zero)) (KExpr.sort (Level.succ Level.zero))",
            r"fun (R : RedEnv) (tenv : KDeclEnv) =>
kernel_infers_in_pi_smart R tenv (@ListType.nil KExpr) (KExpr.sort Level.zero) (KExpr.sort Level.zero)
  (KExpr.sort (Level.succ Level.zero)) (Level.succ Level.zero)
  (KExpr.sort (Level.succ Level.zero)) (Level.succ Level.zero)
  (@KernelInfersIn.sort R tenv (@ListType.nil KExpr) Level.zero)
  (@whnf_red_step_star.refl R (KExpr.sort (Level.succ Level.zero)))
  (@KernelInfersIn.sort R tenv (@ListType.cons KExpr (KExpr.sort Level.zero) (@ListType.nil KExpr)) Level.zero)
  (@whnf_red_step_star.refl R (KExpr.sort (Level.succ Level.zero)))",
            "An inhabited inference derivation returning the actual smart result Sort 1 for Pi(Sort 0,Sort 0), under every supplied reduction environment. No impossible case guard is carried.",
        )?;
        theorem(
            self,
            "acceptance_pi_one_sound",
            "forall (R : RedEnv) (tenv : KDeclEnv), TypingCtxConvIn R tenv (@ListType.nil KExpr) (KExpr.pi (KExpr.sort Level.zero) (KExpr.sort Level.zero)) (KExpr.sort (Level.succ Level.zero))",
            "fun (R : RedEnv) (tenv : KDeclEnv) => kernel_infers_in_sound R tenv (@ListType.nil KExpr) (KExpr.pi (KExpr.sort Level.zero) (KExpr.sort Level.zero)) (KExpr.sort (Level.succ Level.zero)) (kernel_infers_in_pi_one R tenv)",
            "The actual new soundness theorem is applied to the smart-universe Pi derivation, not replaced by a separate declarative fixture.",
        )?;
        self.add_acceptance_in_delta_witnesses()
    }

    fn add_acceptance_in_delta_witnesses(&mut self) -> Result<(), SpecError> {
        for (source, description) in [
            (
                "def acceptance_example_sig : KConstSig := KConstSig.mk (@ListType.cons Name Name.anonymous (@ListType.nil Name)) (KExpr.sort (Level.succ (Level.param Name.anonymous)))",
                "One universe parameter and the schematic type of a body Sort u. The signature and body below agree; this fixture is not a production environment representation.",
            ),
            (
                "def acceptance_example_env : RedEnv := RedEnv.mk RecEnv.empty (DefEnv.addDef DefEnv.empty Name.anonymous (KDefSig.mk acceptance_example_sig (KExpr.sort (Level.param Name.anonymous)))) IndCtorEnv.empty",
                "A supplied singleton reduction environment, not the reflected seed, with a genuine universe-dependent definition body.",
            ),
            (
                "def acceptance_example_tenv : KDeclEnv := fun (n : Name) => opt_pick KConstSig (name_eqb n Name.anonymous) acceptance_example_sig (@OptionType.none KConstSig)",
                "A singleton type environment sharing the exact stored signature with the reduction fixture; no unrelated names are declared.",
            ),
            (
                "def acceptance_example_alias : KExpr := KExpr.const Name.anonymous (@ListType.cons Level (Level.succ Level.zero) (@ListType.nil Level))",
                "The fixture definition applied to one nonzero universe, whose body instance is Sort 1.",
            ),
            (
                "def acceptance_example_context : ListType KExpr := @ListType.cons KExpr acceptance_example_alias (@ListType.nil KExpr)",
                "One binder of the fixture's universe-instantiated alias type.",
            ),
        ] {
            self.add_recursive_def(source, description)?;
        }
        theorem(
            self,
            "acceptance_example_delta_trace",
            "whnf_red_step_star acceptance_example_env acceptance_example_alias (KExpr.sort (Level.succ Level.zero))",
            r"@whnf_red_step_star.step acceptance_example_env acceptance_example_alias
  (KExpr.sort (Level.succ Level.zero)) (KExpr.sort (Level.succ Level.zero))
  (@whnf_red_step.delta acceptance_example_env acceptance_example_alias
    (KExpr.sort (Level.succ Level.zero))
    (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (KExpr.sort (Level.succ Level.zero)))))
  (@whnf_red_step_star.refl acceptance_example_env (KExpr.sort (Level.succ Level.zero)))",
            "Actual finite nonzero-universe delta trace under the supplied environment, using the computed arity-guarded delta result, not an assumed reduction relation.",
        )?;
        theorem(
            self,
            "acceptance_example_alias_typed",
            "TypingCtxConvIn acceptance_example_env acceptance_example_tenv (@ListType.nil KExpr) acceptance_example_alias (KExpr.sort (Level.succ (Level.succ Level.zero)))",
            r"@TypingCtxConvIn.const acceptance_example_env acceptance_example_tenv (@ListType.nil KExpr)
  Name.anonymous (@ListType.cons Level (Level.succ Level.zero) (@ListType.nil Level))
  (KExpr.sort (Level.succ (Level.succ Level.zero)))
  (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (KExpr.sort (Level.succ (Level.succ Level.zero)))))",
            "The fixture context's stored alias type has a sort by actual guarded signature lookup in the matching type environment. This concrete type-validity witness is not a general environment-preservation theorem.",
        )?;
        theorem(
            self,
            "kernel_infers_in_delta_pi",
            "KernelInfersIn acceptance_example_env acceptance_example_tenv acceptance_example_context (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.sort Level.zero)) (KExpr.sort (Level.succ Level.zero))",
            r"kernel_infers_in_pi_smart acceptance_example_env acceptance_example_tenv acceptance_example_context
  (KExpr.bvar Nat.zero) (KExpr.sort Level.zero) acceptance_example_alias (Level.succ Level.zero)
  (KExpr.sort (Level.succ Level.zero)) (Level.succ Level.zero)
  (@KernelInfersIn.bvar acceptance_example_env acceptance_example_tenv acceptance_example_context
    Nat.zero acceptance_example_alias (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr acceptance_example_alias)))
  acceptance_example_delta_trace
  (@KernelInfersIn.sort acceptance_example_env acceptance_example_tenv
    (@ListType.cons KExpr (KExpr.bvar Nat.zero) acceptance_example_context) Level.zero)
  (@whnf_red_step_star.refl acceptance_example_env (KExpr.sort (Level.succ Level.zero)))",
            "An inference derivation whose Pi-domain sort check actually uses universe-aware delta in a supplied environment, then returns the semantically simplified Sort 1 result. All relation premises are constructed.",
        )?;
        theorem(
            self,
            "acceptance_delta_pi_sound",
            "TypingCtxConvIn acceptance_example_env acceptance_example_tenv acceptance_example_context (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.sort Level.zero)) (KExpr.sort (Level.succ Level.zero))",
            r"kernel_infers_in_sound acceptance_example_env acceptance_example_tenv acceptance_example_context
  (KExpr.pi (KExpr.bvar Nat.zero) (KExpr.sort Level.zero)) (KExpr.sort (Level.succ Level.zero))
  kernel_infers_in_delta_pi",
            "The actual new acceptance theorem consumes the constructed non-seed delta/Pi derivation. Finite trace soundness, conversion, and typing use the identical supplied environment.",
        )?;
        theorem(
            self,
            "acceptance_example_wrong_arity_none",
            "@Eq (OptionType KExpr) (delta_reduct (red_def acceptance_example_env) (KExpr.const Name.anonymous (@ListType.nil Level))) (@OptionType.none KExpr)",
            "@Eq.refl (OptionType KExpr) (@OptionType.none KExpr)",
            "The same supplied definition refuses a missing universe argument rather than using default substitution.",
        )?;
        theorem(
            self,
            "acceptance_example_missing_type_argument",
            "@Eq (OptionType KExpr) (kdecl_type_at acceptance_example_tenv Name.anonymous (@ListType.nil Level)) (@OptionType.none KExpr)",
            "@Eq.refl (OptionType KExpr) (@OptionType.none KExpr)",
            "The matching type environment also refuses missing universe arity; the positive trace is not obtained by weakening type lookup.",
        )?;
        theorem(
            self,
            "acceptance_seed_has_no_example_alias",
            "@Eq (OptionType KExpr) (delta_reduct (red_def the_red_env) acceptance_example_alias) (@OptionType.none KExpr)",
            "@Eq.refl (OptionType KExpr) (@OptionType.none KExpr)",
            "The reflected seed has no anonymous fixture definition. This actual lookup control distinguishes the arbitrary-environment caller from a renamed fixed-seed result.",
        )?;
        theorem(
            self,
            "acceptance_example_env_not_seed",
            "@Eq RedEnv acceptance_example_env the_red_env -> Empty",
            r"fun (same : @Eq RedEnv acceptance_example_env the_red_env) =>
option_none_ne_some_type KExpr (KExpr.sort (Level.succ Level.zero)) Empty
  (Eq.trans (OptionType KExpr) (@OptionType.none KExpr)
    (delta_reduct (red_def the_red_env) acceptance_example_alias)
    (@OptionType.some KExpr (KExpr.sort (Level.succ Level.zero)))
    (Eq.symm (OptionType KExpr)
      (delta_reduct (red_def the_red_env) acceptance_example_alias) (@OptionType.none KExpr)
      acceptance_seed_has_no_example_alias)
    (Eq.symm (OptionType KExpr) (@OptionType.some KExpr (KExpr.sort (Level.succ Level.zero)))
      (delta_reduct (red_def the_red_env) acceptance_example_alias)
      (Eq.cong RedEnv (OptionType KExpr)
        (fun (R : RedEnv) => delta_reduct (red_def R) acceptance_example_alias)
        acceptance_example_env the_red_env same)))",
            "A constructive inequality between the supplied environment and the reflected seed, witnessed by their different actual delta results on the same expression.",
        )
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn semantic_acceptance_judgments_parse() {
        for source in [super::CONVERSION, super::TYPING, super::INFERENCE] {
            crate::test_utils::parse_check(source).expect("semantic acceptance judgment parses");
        }
    }

    #[test]
    fn semantic_acceptance_is_checked_and_has_an_executed_pi_caller() {
        let spec = crate::test_utils::build_spec_with_stack();
        for name in [
            "whnf_red_step_star_to_def_eq_in",
            "kernel_infers_in_sound",
            "kernel_infers_in_pi_smart",
            "acceptance_imax_one_one",
            "kernel_infers_in_pi_one",
            "acceptance_pi_one_sound",
            "acceptance_example_delta_trace",
            "acceptance_example_alias_typed",
            "kernel_infers_in_delta_pi",
            "acceptance_delta_pi_sound",
            "acceptance_example_wrong_arity_none",
            "acceptance_example_missing_type_argument",
            "acceptance_seed_has_no_example_alias",
            "acceptance_example_env_not_seed",
        ] {
            let definition = spec.definitions().get(name).expect("registered proof");
            assert!(!definition.is_axiom);
            assert!(definition.elaborated_value.is_some());
            assert!(crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty());
        }
    }
}

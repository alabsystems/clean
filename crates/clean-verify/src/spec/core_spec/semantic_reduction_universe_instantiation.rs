// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Actual raw reduction and additive semantic conversion under instL.
//!
//! Support premises describe selected schematic definition bodies and selected
//! iota RHSs under their stored signature parameters. They do not assume resulting
//! steps or conversion/typing judgments. No confluence premise is needed.
//! This uses the guarded, once-instantiated iota model; production recursor
//! layouts, prepasses and admission remain separate refinement obligations.
//! No Rust execution or admission refinement is claimed; legacy DefEq is intact.
//!
//! Historical universe-blind version check: 165 exact dependency blocks from checkpoint
//! 9f368f80a/hvs0z0, export SHA256
//! b5ff6fa3fc255b6dd1bcce19223911ee2babde3374e91508243ccad7773f861f,
//! plus actual semantic_universe_substitution and current-iota instantiation
//! source declarations. Pinned Lean 4.30.0-rc2 checked all 10 new declarations
//! axiom-free on 2026-09-08 (0.62 seconds, 499,187,712-byte max RSS; 1 GB reserved).
//! Exact scratch SHA256:
//! de1225cde6c523a5f4253ec1e2392b6d622f65c162fbe818cd26caeacacc94bd.
//! Reproduce using scratch/clean_model_slice.rb with the exact export and those
//! two source files, followed by this file. Registered Clean checking and
//! whole-corpus replay remain separate integration obligations.

use crate::spec::error::SpecError;
use crate::spec::Specification;

const PROOFS: &[(&str, &str)] = &[
    (
        r"def DefEnvBodyParamSupported (env : DefEnv) : Prop :=
 forall (n : Name) (defn : KDefSig),
 Eq (OptionType KDefSig) (kdef_for env n) (OptionType.some KDefSig defn) ->
 KExprParamSupport (kconst_params (kdef_signature defn)) (kdef_value defn)",
        "Structural support of each actually selected schematic definition body under its own ordered signature parameters. This is not an output-step or typing contract, NoDup, or production admission evidence.",
    ),
    (
        r"def par_reduces_cd_instL_supported (R : RedEnv)
 (hd : DefEnvBodyParamSupported (red_def R)) (hi : RecEnvRhsParamSupported (red_rec R))
 (s : Name -> Level) (e : KExpr) (r : KExpr) (h : par_reduces_cd R e r) :
 par_reduces_cd R (instL s e) (instL s r) :=
 par_reduces_cd.rec R
  (fun (x : KExpr) (y : KExpr) (_h : par_reduces_cd R x y) => par_reduces_cd R (instL s x) (instL s y))
 (fun (x : KExpr) => par_reduces_cd.refl R (instL s x))
 (fun (A : KExpr) (A2 : KExpr) (b : KExpr) (b2 : KExpr) (a : KExpr) (a2 : KExpr)
 (_hA : par_reduces_cd R A A2) (_hb : par_reduces_cd R b b2) (_ha : par_reduces_cd R a a2)
 (ihA : par_reduces_cd R (instL s A) (instL s A2)) (ihb : par_reduces_cd R (instL s b) (instL s b2)) (iha : par_reduces_cd R (instL s a) (instL s a2)) =>
 Eq.substType KExpr
  (fun (out : KExpr) => par_reduces_cd R (KExpr.app (KExpr.lam (instL s A) (instL s b)) (instL s a)) out)
  (instantiate (instL s b2) (instL s a2)) (instL s (instantiate b2 a2))
  (Eq.symm KExpr (instL s (instantiate b2 a2)) (instantiate (instL s b2) (instL s a2))
    (instL_instantiate s b2 a2))
  (par_reduces_cd.beta R (instL s A) (instL s A2) (instL s b) (instL s b2)
    (instL s a) (instL s a2) ihA ihb iha))
 (fun (a : KExpr) (a2 : KExpr) (b : KExpr) (b2 : KExpr)
 (_ha : par_reduces_cd R a a2) (_hb : par_reduces_cd R b b2)
 (iha : par_reduces_cd R (instL s a) (instL s a2)) (ihb : par_reduces_cd R (instL s b) (instL s b2)) =>
 par_reduces_cd.app R (instL s a) (instL s a2) (instL s b) (instL s b2) iha ihb)
 (fun (a : KExpr) (a2 : KExpr) (b : KExpr) (b2 : KExpr)
 (_ha : par_reduces_cd R a a2) (_hb : par_reduces_cd R b b2)
 (iha : par_reduces_cd R (instL s a) (instL s a2)) (ihb : par_reduces_cd R (instL s b) (instL s b2)) =>
 par_reduces_cd.lam R (instL s a) (instL s a2) (instL s b) (instL s b2) iha ihb)
 (fun (a : KExpr) (a2 : KExpr) (b : KExpr) (b2 : KExpr)
 (_ha : par_reduces_cd R a a2) (_hb : par_reduces_cd R b b2)
 (iha : par_reduces_cd R (instL s a) (instL s a2)) (ihb : par_reduces_cd R (instL s b) (instL s b2)) =>
 par_reduces_cd.pi R (instL s a) (instL s a2) (instL s b) (instL s b2) iha ihb)
 (fun (a : KExpr) (a2 : KExpr) (b : KExpr) (b2 : KExpr)
 (_ha : par_reduces_cd R a a2) (_hb : par_reduces_cd R b b2)
 (iha : par_reduces_cd R (instL s a) (instL s a2)) (ihb : par_reduces_cd R (instL s b) (instL s b2)) =>
 par_reduces_cd.forall_ R (instL s a) (instL s a2) (instL s b) (instL s b2) iha ihb)
 (fun (A : KExpr) (A2 : KExpr) (v : KExpr) (v2 : KExpr) (b : KExpr) (b2 : KExpr)
 (_hA : par_reduces_cd R A A2) (_hv : par_reduces_cd R v v2) (_hb : par_reduces_cd R b b2)
 (ihA : par_reduces_cd R (instL s A) (instL s A2)) (ihv : par_reduces_cd R (instL s v) (instL s v2)) (ihb : par_reduces_cd R (instL s b) (instL s b2)) =>
 Eq.substType KExpr
  (fun (out : KExpr) => par_reduces_cd R (KExpr.let_ (instL s A) (instL s v) (instL s b)) out)
  (instantiate (instL s b2) (instL s v2)) (instL s (instantiate b2 v2))
  (Eq.symm KExpr (instL s (instantiate b2 v2)) (instantiate (instL s b2) (instL s v2))
    (instL_instantiate s b2 v2))
  (par_reduces_cd.let_ R (instL s A) (instL s A2) (instL s v) (instL s v2)
    (instL s b) (instL s b2) ihA ihv ihb))
 (fun (x : KExpr) (y : KExpr) (step : iota_step (red_rec R) x y) =>
 par_reduces_cd.iota R (instL s x) (instL s y)
  (iota_step_instL_supported (red_rec R) hi s x y step))
 (fun (x : KExpr) (y : KExpr) (step : delta_step (red_def R) x y) =>
 par_reduces_cd.delta R (instL s x) (instL s y)
  (delta_step_instL_supported (red_def R) hd s x y step))
 (fun (A : KExpr) (A2 : KExpr) (v : KExpr) (v2 : KExpr) (b : KExpr) (b2 : KExpr)
 (_hA : par_reduces_cd R A A2) (_hv : par_reduces_cd R v v2) (_hb : par_reduces_cd R b b2)
 (ihA : par_reduces_cd R (instL s A) (instL s A2)) (ihv : par_reduces_cd R (instL s v) (instL s v2)) (ihb : par_reduces_cd R (instL s b) (instL s b2)) =>
 par_reduces_cd.let_cong R (instL s A) (instL s A2) (instL s v) (instL s v2)
  (instL s b) (instL s b2) ihA ihv ihb)
 (fun (n : Name) (i : Nat) (b : KExpr) (b2 : KExpr) (_hb : par_reduces_cd R b b2)
 (ihb : par_reduces_cd R (instL s b) (instL s b2)) => par_reduces_cd.proj R n i (instL s b) (instL s b2) ihb) e r h",
        "All eleven actual raw parallel constructors commute with instL under schematic definition-body and signature-relative stored iota RHS support. Beta/zeta use proved instL/instantiate commutation; delta/iota invoke actual supported evaluator proofs. No resulting-step premise, environment faithfulness, or output typing is assumed.",
    ),
    (
        r"def def_eq_in_instL_supported (R : RedEnv)
 (hd : DefEnvBodyParamSupported (red_def R)) (hi : RecEnvRhsParamSupported (red_rec R))
 (s : Name -> Level) (a : KExpr) (b : KExpr) (h : DefEqIn R a b) :
 DefEqIn R (instL s a) (instL s b) :=
 DefEqIn.rec R
  (fun (x : KExpr) (y : KExpr) (_h : DefEqIn R x y) => DefEqIn R (instL s x) (instL s y))
 (fun (x : KExpr) => DefEqIn.refl R (instL s x))
 (fun (x : KExpr) (y : KExpr) (_h : DefEqIn R x y) (ih : DefEqIn R (instL s x) (instL s y)) =>
 DefEqIn.symm R (instL s x) (instL s y) ih)
 (fun (x : KExpr) (m : KExpr) (y : KExpr) (_hx : DefEqIn R x m) (_hy : DefEqIn R m y)
 (ihx : DefEqIn R (instL s x) (instL s m)) (ihy : DefEqIn R (instL s m) (instL s y)) =>
 DefEqIn.trans R (instL s x) (instL s m) (instL s y) ihx ihy)
 (fun (x : KExpr) (y : KExpr) (raw : par_reduces_cd R x y) =>
 DefEqIn.raw R (instL s x) (instL s y) (par_reduces_cd_instL_supported R hd hi s x y raw))
 (fun (x : KExpr) (y : KExpr) (levels : KExprUniverseEq x y) =>
 DefEqIn.levels R (instL s x) (instL s y) (kexprUniverseEq_instL s x y levels))
 (fun (a : KExpr) (a2 : KExpr) (b : KExpr) (b2 : KExpr)
 (_ha : DefEqIn R a a2) (_hb : DefEqIn R b b2)
 (iha : DefEqIn R (instL s a) (instL s a2)) (ihb : DefEqIn R (instL s b) (instL s b2)) =>
 DefEqIn.app R (instL s a) (instL s a2) (instL s b) (instL s b2) iha ihb)
 (fun (a : KExpr) (a2 : KExpr) (b : KExpr) (b2 : KExpr)
 (_ha : DefEqIn R a a2) (_hb : DefEqIn R b b2)
 (iha : DefEqIn R (instL s a) (instL s a2)) (ihb : DefEqIn R (instL s b) (instL s b2)) =>
 DefEqIn.lam R (instL s a) (instL s a2) (instL s b) (instL s b2) iha ihb)
 (fun (a : KExpr) (a2 : KExpr) (b : KExpr) (b2 : KExpr)
 (_ha : DefEqIn R a a2) (_hb : DefEqIn R b b2)
 (iha : DefEqIn R (instL s a) (instL s a2)) (ihb : DefEqIn R (instL s b) (instL s b2)) =>
 DefEqIn.pi R (instL s a) (instL s a2) (instL s b) (instL s b2) iha ihb)
 (fun (A : KExpr) (A2 : KExpr) (v : KExpr) (v2 : KExpr) (b : KExpr) (b2 : KExpr)
 (_hA : DefEqIn R A A2) (_hv : DefEqIn R v v2) (_hb : DefEqIn R b b2)
 (ihA : DefEqIn R (instL s A) (instL s A2)) (ihv : DefEqIn R (instL s v) (instL s v2)) (ihb : DefEqIn R (instL s b) (instL s b2)) =>
 DefEqIn.let_ R (instL s A) (instL s A2) (instL s v) (instL s v2) (instL s b) (instL s b2) ihA ihv ihb)
 (fun (n : Name) (i : Nat) (b : KExpr) (b2 : KExpr) (_h : DefEqIn R b b2)
 (ih : DefEqIn R (instL s b) (instL s b2)) => DefEqIn.proj R n i (instL s b) (instL s b2) ih) a b h",
        "All ten additive semantic conversion constructors preserve actual same-universe substitution. The raw arm uses the proved eleven-case supported reduction theorem and levels uses semantic same-substitution preservation; no pre-assumed substituted conversion or legacy DefEq transport is used.",
    ),
];

const CONTROLS: &[(&str, &str)] = &[
    (
        r"def def_env_body_param_supported_empty : DefEnvBodyParamSupported DefEnv.empty :=
 fun (n : Name) (defn : KDefSig)
   (found : Eq (OptionType KDefSig) (kdef_for DefEnv.empty n) (OptionType.some KDefSig defn)) =>
 option_none_ne_some KDefSig defn
   (KExprParamSupport (kconst_params (kdef_signature defn)) (kdef_value defn)) found",
        "Actual empty definition environment discharges schematic body support because every successful lookup is impossible, by the computed lookup graph.",
    ),
    (
        r"def semantic_reduction_fixture_env : RedEnv :=
 RedEnv.mk iota_inst_supported_env DefEnv.empty IndCtorEnv.empty",
        "Actual supported current-iota environment combined with an empty definition environment; support is discharged by existing concrete proofs.",
    ),
    (
        r"def semantic_reduction_mixed_source : KExpr :=
 iota_inst_supported_input (Level.imax (Level.param Name.anonymous) Level.zero)",
        "Actual iota redex with field and extra argument, carrying an open universe parameter under imax.",
    ),
    (
        r"def semantic_reduction_mixed_target : KExpr := (KExpr.app (KExpr.sort Level.zero) (KExpr.lit Nat.zero))",
        "Result after actual iota, beta-under-application and semantic imax-zero simplification.",
    ),
    (
        r"def semantic_reduction_mixed_conversion :
 DefEqIn semantic_reduction_fixture_env semantic_reduction_mixed_source semantic_reduction_mixed_target :=
 DefEqIn.trans semantic_reduction_fixture_env semantic_reduction_mixed_source
  (iota_inst_supported_output (Level.imax (Level.param Name.anonymous) Level.zero)) semantic_reduction_mixed_target
  (DefEqIn.raw semantic_reduction_fixture_env semantic_reduction_mixed_source
    (iota_inst_supported_output (Level.imax (Level.param Name.anonymous) Level.zero))
    (par_reduces_cd.iota semantic_reduction_fixture_env semantic_reduction_mixed_source
      (iota_inst_supported_output (Level.imax (Level.param Name.anonymous) Level.zero)) (iota_inst_supported_initial_step (Level.imax (Level.param Name.anonymous) Level.zero))))
  (DefEqIn.trans semantic_reduction_fixture_env (iota_inst_supported_output (Level.imax (Level.param Name.anonymous) Level.zero)) (KExpr.app (KExpr.sort (Level.imax (Level.param Name.anonymous) Level.zero)) (KExpr.lit Nat.zero))
    semantic_reduction_mixed_target
    (DefEqIn.raw semantic_reduction_fixture_env (iota_inst_supported_output (Level.imax (Level.param Name.anonymous) Level.zero)) (KExpr.app (KExpr.sort (Level.imax (Level.param Name.anonymous) Level.zero)) (KExpr.lit Nat.zero))
      (par_reduces_cd.app semantic_reduction_fixture_env (KExpr.app iota_inst_supported_rhs (KExpr.sort (Level.imax (Level.param Name.anonymous) Level.zero))) (KExpr.sort (Level.imax (Level.param Name.anonymous) Level.zero)) (KExpr.lit Nat.zero) (KExpr.lit Nat.zero)
  (par_reduces_cd.beta semantic_reduction_fixture_env (KExpr.sort Level.zero) (KExpr.sort Level.zero)
    (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero) (KExpr.sort (Level.imax (Level.param Name.anonymous) Level.zero)) (KExpr.sort (Level.imax (Level.param Name.anonymous) Level.zero))
    (par_reduces_cd.refl semantic_reduction_fixture_env (KExpr.sort Level.zero))
    (par_reduces_cd.refl semantic_reduction_fixture_env (KExpr.bvar Nat.zero))
    (par_reduces_cd.refl semantic_reduction_fixture_env (KExpr.sort (Level.imax (Level.param Name.anonymous) Level.zero))))
  (par_reduces_cd.refl semantic_reduction_fixture_env (KExpr.lit Nat.zero))))
    (DefEqIn.levels semantic_reduction_fixture_env (KExpr.app (KExpr.sort (Level.imax (Level.param Name.anonymous) Level.zero)) (KExpr.lit Nat.zero)) semantic_reduction_mixed_target
      (KExprUniverseEq.app (KExpr.sort (Level.imax (Level.param Name.anonymous) Level.zero)) (KExpr.sort Level.zero) (KExpr.lit Nat.zero) (KExpr.lit Nat.zero)
        (kexprUniverseEq_imax_zero (Level.param Name.anonymous)) (KExprUniverseEq.lit Nat.zero))))",
        "An inhabited conversion chain with an actual iota step, actual beta under the outer application, then semantic universe normalization. No assumed conversion or support capability.",
    ),
    (
        r"def semantic_reduction_mixed_instantiation :
 DefEqIn semantic_reduction_fixture_env
  (instL (fun (_n : Name) => Level.succ Level.zero) semantic_reduction_mixed_source)
  semantic_reduction_mixed_target :=
 def_eq_in_instL_supported semantic_reduction_fixture_env
  def_env_body_param_supported_empty (rec_env_rhs_paramfree_supported iota_inst_supported_env iota_inst_supported_env_support)
  (fun (_n : Name) => Level.succ Level.zero)
  semantic_reduction_mixed_source semantic_reduction_mixed_target semantic_reduction_mixed_conversion",
        "Closed actual caller of supported DefEqIn instantiation under a nonidentity substitution, exercising raw iota/beta and the levels/trans conversion constructors with proved environment support.",
    ),
    (
        r"def semantic_reduction_iota_nonzero :
 par_reduces_cd semantic_reduction_fixture_env
  (iota_inst_supported_input (Level.succ Level.zero)) (iota_inst_supported_output (Level.succ Level.zero)) :=
 par_reduces_cd_instL_supported semantic_reduction_fixture_env
  def_env_body_param_supported_empty (rec_env_rhs_paramfree_supported iota_inst_supported_env iota_inst_supported_env_support)
  (fun (_n : Name) => Level.succ Level.zero)
  (iota_inst_supported_input (Level.param Name.anonymous)) (iota_inst_supported_output (Level.param Name.anonymous))
  (par_reduces_cd.iota semantic_reduction_fixture_env
    (iota_inst_supported_input (Level.param Name.anonymous)) (iota_inst_supported_output (Level.param Name.anonymous))
    (iota_inst_supported_initial_step (Level.param Name.anonymous)))",
        "Actual raw-parallel caller with nonzero instantiated field universe, using the generic eleven-constructor theorem and a concrete successful original iota step.",
    ),
];

impl Specification {
    /// Requires actual delta/iota supported instantiation, semantic same-
    /// substitution preservation, instL/instantiate commutation and DefEqIn.
    pub(super) fn add_semantic_reduction_universe_instantiation(
        &mut self,
    ) -> Result<(), SpecError> {
        for (source, description) in PROOFS.iter().chain(CONTROLS) {
            self.add_recursive_def(source, description)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn supported_raw_and_conversion_instantiation_have_checked_actual_callers() {
        let spec = crate::test_utils::build_spec_with_stack();
        for name in [
            "par_reduces_cd_instL_supported",
            "def_eq_in_instL_supported",
            "def_env_body_param_supported_empty",
            "semantic_reduction_mixed_conversion",
            "semantic_reduction_mixed_instantiation",
            "semantic_reduction_iota_nonzero",
        ] {
            let definition = spec
                .definitions()
                .get(name)
                .expect("registered checked supported instantiation declaration");
            assert!(!definition.is_axiom, "{name}");
            assert!(definition.elaborated_value.is_some(), "{name}");
            assert!(
                crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty(),
                "{name}"
            );
        }
    }
}

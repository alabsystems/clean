// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Exact guarded constant results for the semantic acceptance model.
//!
//! The stored lookup result need not be syntactically equal to the returned
//! type: the model's constant rule separately requires universe equivalence.
//! This module inverts that actual rule, keeps both pieces of evidence, and
//! applies the assembled soundness theorem to a genuinely simplified result.
//! It neither assumes output typing nor claims production Rust refinement or
//! validity of an arbitrary supplied declaration environment.

use crate::spec::error::SpecError;
use crate::spec::Specification;

use super::acceptance_in::theorem;

const RETURN: &str = r"inductive AcceptanceConstantReturn (tenv : KDeclEnv)
(n : Name) (us : ListType Level) (T : KExpr) : Type
| intro : forall (A : KExpr),
  Eq (OptionType KExpr) (kdecl_type_at tenv n us) (OptionType.some KExpr A) ->
  KExprUniverseEq A T -> AcceptanceConstantReturn tenv n us T";

const RESULT: &str = r"def acceptance_constant_result (tenv : KDeclEnv)
(e : KExpr) (T : KExpr) : Type := match e with
| KExpr.sort u => Nat
| KExpr.bvar i => Nat
| KExpr.app f a => Nat
| KExpr.lam A b => Nat
| KExpr.pi A B => Nat
| KExpr.const n us => AcceptanceConstantReturn tenv n us T
| KExpr.let_ A v b => Nat
| KExpr.proj sn i sub => Nat
| KExpr.lit n => Nat";

const RESULT_TYPE: &str = r"forall (R : RedEnv) (tenv : KDeclEnv)
(G : ListType KExpr) (e : KExpr) (T : KExpr),
KernelInfersIn R tenv G e T -> acceptance_constant_result tenv e T";

const RESULT_VALUE: &str = r"fun (R : RedEnv) (tenv : KDeclEnv)
(G : ListType KExpr) (e : KExpr) (T : KExpr) (h : KernelInfersIn R tenv G e T) =>
KernelInfersIn.rec R tenv
  (fun (G0 : ListType KExpr) (e0 : KExpr) (T0 : KExpr)
    (_h : KernelInfersIn R tenv G0 e0 T0) => acceptance_constant_result tenv e0 T0)
  (fun (_G0 : ListType KExpr) (_u : Level) => Nat.zero)
  (fun (G0 : ListType KExpr) (i : Nat) (A : KExpr)
    (_get : Eq (OptionType KExpr) (ctx_lookup G0 i) (OptionType.some KExpr A)) => Nat.zero)
  (fun (G0 : ListType KExpr) (A : KExpr) (B : KExpr) (SA : KExpr) (u : Level)
    (SB : KExpr) (v : Level) (r : Level)
    (_ha : KernelInfersIn R tenv G0 A SA) (_hwa : whnf_red_step_star R SA (KExpr.sort u))
    (_hb : KernelInfersIn R tenv (ListType.cons KExpr A G0) B SB)
    (_hwb : whnf_red_step_star R SB (KExpr.sort v)) (_hr : levelEqSem (Level.imax u v) r)
    (_iha : acceptance_constant_result tenv A SA)
    (_ihb : acceptance_constant_result tenv B SB) => Nat.zero)
  (fun (G0 : ListType KExpr) (A : KExpr) (b : KExpr) (B : KExpr) (SA : KExpr) (u : Level)
    (_ha : KernelInfersIn R tenv G0 A SA) (_hwa : whnf_red_step_star R SA (KExpr.sort u))
    (_hb : KernelInfersIn R tenv (ListType.cons KExpr A G0) b B)
    (_iha : acceptance_constant_result tenv A SA)
    (_ihb : acceptance_constant_result tenv b B) => Nat.zero)
  (fun (_G0 : ListType KExpr) (n : Name) (us : ListType Level) (A : KExpr) (T0 : KExpr)
    (get : Eq (OptionType KExpr) (kdecl_type_at tenv n us) (OptionType.some KExpr A))
    (result : KExprUniverseEq A T0) => AcceptanceConstantReturn.intro tenv n us T0 A get result)
  (fun (G0 : ListType KExpr) (f : KExpr) (a : KExpr) (F : KExpr) (A : KExpr) (B : KExpr) (A2 : KExpr)
    (_hf : KernelInfersIn R tenv G0 f F) (_hw : whnf_red_step_star R F (KExpr.pi A B))
    (_ha : KernelInfersIn R tenv G0 a A2) (_heq : DefEqIn R A2 A)
    (_ihf : acceptance_constant_result tenv f F)
    (_iha : acceptance_constant_result tenv a A2) => Nat.zero)
  (fun (G0 : ListType KExpr) (A : KExpr) (v : KExpr) (b : KExpr) (Ty : KExpr) (u : Level) (Tv : KExpr) (B : KExpr)
    (_ht : KernelInfersIn R tenv G0 A Ty) (_hw : whnf_red_step_star R Ty (KExpr.sort u))
    (_hv : KernelInfersIn R tenv G0 v Tv) (_heq : DefEqIn R Tv A)
    (_hb : KernelInfersIn R tenv (ListType.cons KExpr A G0) b B)
    (_iht : acceptance_constant_result tenv A Ty)
    (_ihv : acceptance_constant_result tenv v Tv)
    (_ihb : acceptance_constant_result tenv b B) => Nat.zero)
  (fun (_G0 : ListType KExpr) (_n : Nat) => Nat.zero)
  (fun (_G0 : ListType KExpr) (_n : Nat) => Nat.zero) G e T h";

impl Specification {
    pub(super) fn add_acceptance_constants(&mut self) -> Result<(), SpecError> {
        self.add_inductive(
            RETURN,
            "A successful semantic constant result packages the raw instantiated type, exact guarded lookup equation, and universe-only correspondence to the returned type. It does not replace either evidence field by output typing.",
        )?;
        self.add_recursive_def(
            RESULT,
            "Constant-specific return assertion; nonconstant expression constructors deliberately impose no constant-lookup obligation.",
        )?;
        theorem(
            self,
            "kernel_infers_in_constant_result",
            RESULT_TYPE,
            RESULT_VALUE,
            "Invert all nine actual KernelInfersIn constructors. A constant subject retains both its computed guarded type and semantic universe result correspondence, under arbitrary R, declaration environment, and context.",
        )?;
        theorem(
            self,
            "kernel_infers_in_constant_inv",
            r"forall (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr)
(n : Name) (us : ListType Level) (T : KExpr), KernelInfersIn R tenv G (KExpr.const n us) T ->
forall (C : Type), (forall (A : KExpr),
  Eq (OptionType KExpr) (kdecl_type_at tenv n us) (OptionType.some KExpr A) ->
  KExprUniverseEq A T -> C) -> C",
            r"fun (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr)
(n : Name) (us : ListType Level) (T : KExpr) (h : KernelInfersIn R tenv G (KExpr.const n us) T)
(C : Type) (consume : forall (A : KExpr),
  Eq (OptionType KExpr) (kdecl_type_at tenv n us) (OptionType.some KExpr A) ->
  KExprUniverseEq A T -> C) =>
AcceptanceConstantReturn.rec tenv n us T
  (fun (_r : AcceptanceConstantReturn tenv n us T) => C) consume
  (kernel_infers_in_constant_result R tenv G (KExpr.const n us) T h)",
            "Type-valued elimination of the derived constant result package. The existential raw type A is not identified syntactically with the returned type T.",
        )?;
        theorem(
            self,
            "kernel_infers_in_constant_lookup_failure",
            r"forall (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr)
(n : Name) (us : ListType Level) (T : KExpr),
Eq (OptionType KExpr) (kdecl_type_at tenv n us) (OptionType.none KExpr) ->
KernelInfersIn R tenv G (KExpr.const n us) T -> Empty",
            r"fun (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr)
(n : Name) (us : ListType Level) (T : KExpr)
(missing : Eq (OptionType KExpr) (kdecl_type_at tenv n us) (OptionType.none KExpr))
(h : KernelInfersIn R tenv G (KExpr.const n us) T) =>
kernel_infers_in_constant_inv R tenv G n us T h Empty
  (fun (A : KExpr)
    (get : Eq (OptionType KExpr) (kdecl_type_at tenv n us) (OptionType.some KExpr A))
    (_result : KExprUniverseEq A T) => option_none_ne_some_type KExpr A Empty
      (Eq.trans (OptionType KExpr) (OptionType.none KExpr) (kdecl_type_at tenv n us)
        (OptionType.some KExpr A)
        (Eq.symm (OptionType KExpr) (kdecl_type_at tenv n us) (OptionType.none KExpr) missing) get))",
            "Every claimed return type is impossible after actual guarded lookup fails. Semantic universe correspondence cannot bypass a missing name or wrong arity.",
        )?;
        theorem(
            self,
            "kernel_infers_in_constant_wrong_arity",
            r"forall (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr)
(n : Name) (us : ListType Level) (sig : KConstSig) (T : KExpr),
Eq (OptionType KConstSig) (tenv n) (OptionType.some KConstSig sig) ->
(kconst_arity sig us -> Empty) -> KernelInfersIn R tenv G (KExpr.const n us) T -> Empty",
            r"fun (R : RedEnv) (tenv : KDeclEnv) (G : ListType KExpr)
(n : Name) (us : ListType Level) (sig : KConstSig) (T : KExpr)
(get : Eq (OptionType KConstSig) (tenv n) (OptionType.some KConstSig sig))
(bad : kconst_arity sig us -> Empty) =>
kernel_infers_in_constant_lookup_failure R tenv G n us T
  (kdecl_type_at_wrong_arity tenv n us sig get bad)",
            "Universal wrong-universe-arity impossibility for the actual semantic inference relation, derived from computed lookup failure rather than a branch-exclusion hypothesis.",
        )?;
        self.add_acceptance_constant_witnesses()
    }

    fn add_acceptance_constant_witnesses(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            "def acceptance_constant_imax_sig : KConstSig := KConstSig.mk (ListType.cons Name Name.anonymous (ListType.nil Name)) (KExpr.sort (Level.imax (Level.param Name.anonymous) Level.zero))",
            "One stored universe parameter with a raw imax type; its constructor tree is deliberately not the simplified semantic result Sort 0.",
        )?;
        self.add_recursive_def(
            "def acceptance_constant_imax_tenv : KDeclEnv := fun (n : Name) => opt_pick KConstSig (name_eqb n Name.anonymous) acceptance_constant_imax_sig (OptionType.none KConstSig)",
            "A singleton schematic declaration environment shared by the positive smart-result caller and the missing-argument rejection. This fixture is not a proved admitted production environment.",
        )?;
        theorem(
            self,
            "acceptance_constant_imax_lookup",
            "forall (u : Level), Eq (OptionType KExpr) (kdecl_type_at acceptance_constant_imax_tenv Name.anonymous (ListType.cons Level u (ListType.nil Level))) (OptionType.some KExpr (KExpr.sort (Level.imax u Level.zero)))",
            "fun (u : Level) => Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.sort (Level.imax u Level.zero)))",
            "Actual guarded lookup retains the raw instantiated imax syntax for every supplied level; the declaration is not silently changed to a fixed Sort 0 signature.",
        )?;
        theorem(
            self,
            "kernel_infers_in_constant_imax_zero",
            "forall (R : RedEnv) (G : ListType KExpr) (u : Level), KernelInfersIn R acceptance_constant_imax_tenv G (KExpr.const Name.anonymous (ListType.cons Level u (ListType.nil Level))) (KExpr.sort Level.zero)",
            r"fun (R : RedEnv) (G : ListType KExpr) (u : Level) =>
KernelInfersIn.const R acceptance_constant_imax_tenv G Name.anonymous
  (ListType.cons Level u (ListType.nil Level))
  (KExpr.sort (Level.imax u Level.zero)) (KExpr.sort Level.zero)
  (acceptance_constant_imax_lookup u) (kexprUniverseEq_imax_zero u)",
            "An inhabited constant inference whose raw type is Sort(imax u 0) and returned type is Sort 0. Both the lookup and universe-equivalence premises are constructed; no assumed result typing is supplied.",
        )?;
        theorem(
            self,
            "acceptance_constant_imax_zero_sound",
            "forall (R : RedEnv) (G : ListType KExpr) (u : Level), TypingCtxConvIn R acceptance_constant_imax_tenv G (KExpr.const Name.anonymous (ListType.cons Level u (ListType.nil Level))) (KExpr.sort Level.zero)",
            r"fun (R : RedEnv) (G : ListType KExpr) (u : Level) =>
kernel_infers_in_sound R acceptance_constant_imax_tenv G
  (KExpr.const Name.anonymous (ListType.cons Level u (ListType.nil Level))) (KExpr.sort Level.zero)
  (kernel_infers_in_constant_imax_zero R G u)",
            "The actual assembled kernel_infers_in_sound theorem consumes the successful semantic constant result at arbitrary R and context. This is a model caller, not production source refinement.",
        )?;
        theorem(
            self,
            "acceptance_constant_imax_one_sound",
            "forall (R : RedEnv), TypingCtxConvIn R acceptance_constant_imax_tenv (ListType.nil KExpr) (KExpr.const Name.anonymous (ListType.cons Level (Level.succ Level.zero) (ListType.nil Level))) (KExpr.sort Level.zero)",
            "fun (R : RedEnv) => acceptance_constant_imax_zero_sound R (ListType.nil KExpr) (Level.succ Level.zero)",
            "Concrete nonzero universe instance of the same stored signature and assembled soundness caller, with every inference premise discharged.",
        )?;
        theorem(
            self,
            "acceptance_constant_imax_missing_arity",
            "kconst_arity acceptance_constant_imax_sig (ListType.nil Level) -> Empty",
            r"fun (h : kconst_arity acceptance_constant_imax_sig (ListType.nil Level)) =>
Eq.substType Nat
  (fun (n : Nat) => Nat.rec (fun (_ : Nat) => Type) Empty (fun (_ : Nat) (_ : Type) => Nat) n)
  (Nat.succ Nat.zero) Nat.zero h Nat.zero",
            "The same stored one-parameter signature cannot have zero supplied universe arguments.",
        )?;
        theorem(
            self,
            "acceptance_constant_imax_missing_lookup",
            "Eq (OptionType KExpr) (kdecl_type_at acceptance_constant_imax_tenv Name.anonymous (ListType.nil Level)) (OptionType.none KExpr)",
            "Eq.refl (OptionType KExpr) (OptionType.none KExpr)",
            "Actual guarded lookup rejects the missing argument in the positive caller's exact stored environment.",
        )?;
        theorem(
            self,
            "acceptance_constant_imax_missing_argument",
            "forall (R : RedEnv) (G : ListType KExpr) (T : KExpr), KernelInfersIn R acceptance_constant_imax_tenv G (KExpr.const Name.anonymous (ListType.nil Level)) T -> Empty",
            r"fun (R : RedEnv) (G : ListType KExpr) (T : KExpr) =>
kernel_infers_in_constant_wrong_arity R acceptance_constant_imax_tenv G Name.anonymous
  (ListType.nil Level) acceptance_constant_imax_sig T
  (Eq.refl (OptionType KConstSig) (OptionType.some KConstSig acceptance_constant_imax_sig))
  acceptance_constant_imax_missing_arity",
            "The universal wrong-arity theorem is applied to the same environment as the inhabited successful inference: no output type can rescue its missing universe argument.",
        )
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn semantic_constant_result_package_and_recursor_parse() {
        for source in [
            super::RETURN.to_string(),
            super::RESULT.to_string(),
            format!(
                "def acceptance_constant_result_parse_probe : {} := {}",
                super::RESULT_TYPE,
                super::RESULT_VALUE
            ),
        ] {
            crate::test_utils::parse_check(&source).expect("constant result source parses");
        }
        assert!(super::RETURN.contains("KExprUniverseEq A T"));
        assert!(super::RETURN.contains("OptionType.some KExpr A"));
        assert!(!super::RETURN.contains("TypingCtxConvIn"));
        assert!(super::RESULT_VALUE.contains("KernelInfersIn.rec R tenv"));
    }

    #[test]
    fn semantic_constant_results_and_imax_soundness_caller_are_checked() {
        let spec = crate::test_utils::build_spec_with_stack();
        for name in [
            "kernel_infers_in_constant_result",
            "kernel_infers_in_constant_inv",
            "kernel_infers_in_constant_lookup_failure",
            "kernel_infers_in_constant_wrong_arity",
            "acceptance_constant_imax_lookup",
            "kernel_infers_in_constant_imax_zero",
            "acceptance_constant_imax_zero_sound",
            "acceptance_constant_imax_one_sound",
            "acceptance_constant_imax_missing_arity",
            "acceptance_constant_imax_missing_lookup",
            "acceptance_constant_imax_missing_argument",
        ] {
            let def = spec
                .definitions()
                .get(name)
                .expect("registered constant proof");
            assert!(!def.is_axiom, "{name}");
            assert!(def.elaborated_value.is_some(), "{name}");
            assert!(
                crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty(),
                "{name}"
            );
        }
        let sound = spec
            .definitions()
            .get("acceptance_constant_imax_zero_sound")
            .expect("sound caller");
        assert!(sound
            .value_src
            .as_deref()
            .is_some_and(|source| source.contains("kernel_infers_in_sound")));
    }

    #[test]
    fn semantic_constant_cannot_forge_guard_or_syntactic_result_equality() {
        let mut spec = crate::test_utils::build_spec_with_stack();
        for source in [
            "def acceptance_constant_forged_raw_simplification : Eq (OptionType KExpr) (kdecl_type_at acceptance_constant_imax_tenv Name.anonymous (ListType.cons Level (Level.succ Level.zero) (ListType.nil Level))) (OptionType.some KExpr (KExpr.sort Level.zero)) := Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.sort Level.zero))",
            "def acceptance_constant_forged_missing_argument : KernelInfersIn the_red_env acceptance_constant_imax_tenv (ListType.nil KExpr) (KExpr.const Name.anonymous (ListType.nil Level)) (KExpr.sort Level.zero) := KernelInfersIn.const the_red_env acceptance_constant_imax_tenv (ListType.nil KExpr) Name.anonymous (ListType.nil Level) (KExpr.sort (Level.imax Level.zero Level.zero)) (KExpr.sort Level.zero) (Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.sort (Level.imax Level.zero Level.zero)))) (kexprUniverseEq_imax_zero Level.zero)",
            "def acceptance_constant_forged_semantic_result : KernelInfersIn the_red_env acceptance_constant_imax_tenv (ListType.nil KExpr) (KExpr.const Name.anonymous (ListType.cons Level Level.zero (ListType.nil Level))) (KExpr.sort (Level.succ Level.zero)) := KernelInfersIn.const the_red_env acceptance_constant_imax_tenv (ListType.nil KExpr) Name.anonymous (ListType.cons Level Level.zero (ListType.nil Level)) (KExpr.sort (Level.imax Level.zero Level.zero)) (KExpr.sort (Level.succ Level.zero)) (acceptance_constant_imax_lookup Level.zero) (kexprUniverseEq_imax_zero Level.zero)",
        ] {
            assert!(spec.add_recursive_def(source, "Negative semantic constant-inference control.").is_err(), "forged guard or result must be rejected");
        }
    }
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Universe substitution of the explicit-environment semantic typing judgment.
//!
//! All ten typing constructors are handled. Constant lookup uses stored type
//! support; conversion uses the proved actual supported delta/iota operations.
//! No instantiated-body typing or output-step premise is assumed. The iota
//! support interface refers to each selected stored metadata signature; it is
//! a structural model invariant, not production admission or Rust refinement.
//!
//! Historical parameter-free version check: all sixteen declarations, including the
//! inhabited callers, have empty axiom closures under pinned Lean 4.30.0-rc2.
//! The 343 exact dependency blocks came from bc0ae2504/PJrAsR (export SHA256
//! 4a64c4995ca70fae3c7399eabeaa8e618eeba3cc0f7f65105856ec18086a9571).
//! Measured 2026-09-08: 0.74s, 529,137,664-byte max RSS under 1 GB. Reproduce
//! with scratch/clean_model_slice.rb and the iota/reduction substitution files
//! before this file. Registered Clean checking and whole replay are separate.

use crate::spec::error::SpecError;
use crate::spec::Specification;

const PROOFS: &[(&str, &str)] = &[
    (
        r"def KDeclEnvTypeParamSupported (tenv : KDeclEnv) : Prop :=
 forall (n : Name) (sig : KConstSig),
 Eq (OptionType KConstSig) (tenv n) (OptionType.some KConstSig sig) ->
 KExprParamSupport (kconst_params sig) (kconst_type sig)",
        "Every actually stored signature type uses only its declared universe parameters. This is a schematic syntax invariant, not per-instance typing or a production admission proof.",
    ),
    (
        r"def typingctxconv_in_instL_supported (R : RedEnv)
 (hd : DefEnvBodyParamSupported (red_def R)) (hi : RecEnvRhsParamSupported (red_rec R))
 (tenv : KDeclEnv) (supported : KDeclEnvTypeParamSupported tenv) (s : Name -> Level)
 (G : ListType KExpr) (e : KExpr) (T : KExpr)
 (typed : TypingCtxConvIn R tenv G e T) :
 TypingCtxConvIn R tenv (mapLT (instL s) G) (instL s e) (instL s T) :=
 TypingCtxConvIn.rec R tenv
   (fun (G0 : ListType KExpr) (e0 : KExpr) (T0 : KExpr)
     (_h : TypingCtxConvIn R tenv G0 e0 T0) =>
     TypingCtxConvIn R tenv (mapLT (instL s) G0) (instL s e0) (instL s T0))
   (fun (G0 : ListType KExpr) (i : Nat) (A : KExpr)
     (found : Eq (OptionType KExpr) (ctx_lookup G0 i) (OptionType.some KExpr A)) =>
     Eq.substType KExpr
       (fun (T0 : KExpr) => TypingCtxConvIn R tenv (mapLT (instL s) G0) (KExpr.bvar i) T0)
       (lift_at (instL s A) Nat.zero (Nat.succ i))
       (instL s (lift_at A Nat.zero (Nat.succ i)))
       (Eq.symm KExpr (instL s (lift_at A Nat.zero (Nat.succ i)))
         (lift_at (instL s A) Nat.zero (Nat.succ i))
         (instL_lift_at s A Nat.zero (Nat.succ i)))
       (TypingCtxConvIn.var R tenv (mapLT (instL s) G0) i (instL s A)
         (ctx_lookup_mapLT_some (instL s) G0 i A found)))
   (fun (G0 : ListType KExpr) (u : Level) =>
     TypingCtxConvIn.sort R tenv (mapLT (instL s) G0) (substL s u))
   (fun (G0 : ListType KExpr) (A : KExpr) (B : KExpr) (u : Level) (v : Level)
     (_hA : TypingCtxConvIn R tenv G0 A (KExpr.sort u))
     (_hB : TypingCtxConvIn R tenv (ListType.cons KExpr A G0) B (KExpr.sort v))
     (ihA : TypingCtxConvIn R tenv (mapLT (instL s) G0) (instL s A) (instL s (KExpr.sort u)))
     (ihB : TypingCtxConvIn R tenv (mapLT (instL s) (ListType.cons KExpr A G0)) (instL s B) (instL s (KExpr.sort v))) =>
     TypingCtxConvIn.pi R tenv (mapLT (instL s) G0) (instL s A) (instL s B)
       (substL s u) (substL s v) ihA ihB)
   (fun (G0 : ListType KExpr) (A : KExpr) (b : KExpr) (B : KExpr) (u : Level)
     (_hA : TypingCtxConvIn R tenv G0 A (KExpr.sort u))
     (_hb : TypingCtxConvIn R tenv (ListType.cons KExpr A G0) b B)
     (ihA : TypingCtxConvIn R tenv (mapLT (instL s) G0) (instL s A) (instL s (KExpr.sort u)))
     (ihb : TypingCtxConvIn R tenv (mapLT (instL s) (ListType.cons KExpr A G0)) (instL s b) (instL s B)) =>
     TypingCtxConvIn.lam R tenv (mapLT (instL s) G0) (instL s A) (instL s b) (instL s B)
       (substL s u) ihA ihb)
   (fun (G0 : ListType KExpr) (f : KExpr) (a : KExpr) (A : KExpr) (B : KExpr)
     (_hf : TypingCtxConvIn R tenv G0 f (KExpr.pi A B))
     (_ha : TypingCtxConvIn R tenv G0 a A)
     (ihf : TypingCtxConvIn R tenv (mapLT (instL s) G0) (instL s f) (instL s (KExpr.pi A B)))
     (iha : TypingCtxConvIn R tenv (mapLT (instL s) G0) (instL s a) (instL s A)) =>
     Eq.substType KExpr
       (fun (T0 : KExpr) => TypingCtxConvIn R tenv (mapLT (instL s) G0)
         (KExpr.app (instL s f) (instL s a)) T0)
       (instantiate (instL s B) (instL s a)) (instL s (instantiate B a))
       (Eq.symm KExpr (instL s (instantiate B a))
         (instantiate (instL s B) (instL s a)) (instL_instantiate s B a))
       (TypingCtxConvIn.app R tenv (mapLT (instL s) G0)
         (instL s f) (instL s a) (instL s A) (instL s B) ihf iha))
   (fun (G0 : ListType KExpr) (n : Name) (us : ListType Level) (A : KExpr)
     (found : Eq (OptionType KExpr) (kdecl_type_at tenv n us) (OptionType.some KExpr A)) =>
     TypingCtxConvIn.const R tenv (mapLT (instL s) G0) n (mapLL (substL s) us) (instL s A)
       (kdecl_type_at_instL_supported tenv supported n us A found s))
   (fun (G0 : ListType KExpr) (e0 : KExpr) (A : KExpr) (B : KExpr)
     (_typed : TypingCtxConvIn R tenv G0 e0 A) (equivalent : DefEqIn R A B)
     (ih : TypingCtxConvIn R tenv (mapLT (instL s) G0) (instL s e0) (instL s A)) =>
     TypingCtxConvIn.conv R tenv (mapLT (instL s) G0) (instL s e0) (instL s A) (instL s B)
       ih (def_eq_in_instL_supported R hd hi s A B equivalent))
   (fun (G0 : ListType KExpr) (ty : KExpr) (v : KExpr) (b : KExpr) (B : KExpr) (u : Level)
     (_hty : TypingCtxConvIn R tenv G0 ty (KExpr.sort u))
     (_hv : TypingCtxConvIn R tenv G0 v ty)
     (_hb : TypingCtxConvIn R tenv (ListType.cons KExpr ty G0) b B)
     (ihty : TypingCtxConvIn R tenv (mapLT (instL s) G0) (instL s ty) (instL s (KExpr.sort u)))
     (ihv : TypingCtxConvIn R tenv (mapLT (instL s) G0) (instL s v) (instL s ty))
     (ihb : TypingCtxConvIn R tenv (mapLT (instL s) (ListType.cons KExpr ty G0)) (instL s b) (instL s B)) =>
     Eq.substType KExpr
       (fun (T0 : KExpr) => TypingCtxConvIn R tenv (mapLT (instL s) G0)
         (KExpr.let_ (instL s ty) (instL s v) (instL s b)) T0)
       (instantiate (instL s B) (instL s v)) (instL s (instantiate B v))
       (Eq.symm KExpr (instL s (instantiate B v))
         (instantiate (instL s B) (instL s v)) (instL_instantiate s B v))
       (TypingCtxConvIn.let_ R tenv (mapLT (instL s) G0)
         (instL s ty) (instL s v) (instL s b) (instL s B) (substL s u)
         ihty ihv ihb))
   (fun (G0 : ListType KExpr) (n : Nat) =>
     TypingCtxConvIn.lit_nat R tenv (mapLT (instL s) G0) n)
   (fun (G0 : ListType KExpr) (n : Nat) =>
     TypingCtxConvIn.lit_string R tenv (mapLT (instL s) G0) n)
   G e T typed",
        "Actual ten-constructor semantic typing induction at the same explicit environment. Constant cases derive guarded lookup transport from stored schematic support; conversion uses the proved generic supported operational substitution theorem. No output typing or step closure is a premise.",
    ),
    (
        r"def typingctxconv_in_instLevels_supported (R : RedEnv)
 (hd : DefEnvBodyParamSupported (red_def R)) (hi : RecEnvRhsParamSupported (red_rec R))
 (tenv : KDeclEnv) (supported : KDeclEnvTypeParamSupported tenv)
 (ps : ListType Name) (us : ListType Level)
 (G : ListType KExpr) (e : KExpr) (T : KExpr)
 (typed : TypingCtxConvIn R tenv G e T) :
 TypingCtxConvIn R tenv (mapLT (instL (paramSubstN ps us)) G)
 (instLevels ps e us) (instLevels ps T us) :=
 typingctxconv_in_instL_supported R hd hi tenv supported (paramSubstN ps us) G e T typed",
        "Specialize the proved semantic typing transport to the actual ordered parameter substitution, retaining the same explicit reduction and type environments.",
    ),
    (
        r"def typingctxconv_in_kdef_instantiated (R : RedEnv)
 (hd : DefEnvBodyParamSupported (red_def R)) (hi : RecEnvRhsParamSupported (red_rec R))
 (tenv : KDeclEnv) (supported : KDeclEnvTypeParamSupported tenv)
 (defn : KDefSig) (us : ListType Level)
 (schematic : TypingCtxConvIn R tenv (ListType.nil KExpr)
 (kdef_value defn) (kconst_type (kdef_signature defn))) :
 TypingCtxConvIn R tenv (ListType.nil KExpr) (kdef_inst_value defn us)
 (kconst_inst_type (kdef_signature defn) us) :=
 typingctxconv_in_instLevels_supported R hd hi tenv supported
 (kconst_params (kdef_signature defn)) us (ListType.nil KExpr)
 (kdef_value defn) (kconst_type (kdef_signature defn)) schematic",
        "Derive instantiated definition body typing from one schematic empty-context derivation, the shared stored signature, and syntax support of actual environments. No per-instance typing contract is carried.",
    ),
];

const CONTROLS: &[(&str, &str)] = &[
    (
        r"def def_env_body_param_supported_add (env : DefEnv)
 (old : DefEnvBodyParamSupported env) (n : Name) (defn : KDefSig)
 (supported : KExprParamSupport (kconst_params (kdef_signature defn)) (kdef_value defn)) :
 DefEnvBodyParamSupported (DefEnv.addDef env n defn) :=
 fun (query : Name) (selected : KDefSig)
 (found : Eq (OptionType KDefSig) (kdef_for (DefEnv.addDef env n defn) query) (OptionType.some KDefSig selected)) =>
 opt_pick_some_inv KDefSig (name_eqb n query) defn (kdef_for env query) selected
 (KExprParamSupport (kconst_params (kdef_signature selected)) (kdef_value selected)) found
 (fun (_same_name : Eq Bool (name_eqb n query) Bool.true) (same_record : Eq KDefSig defn selected) =>
 Eq.subst KDefSig (fun (d : KDefSig) => KExprParamSupport (kconst_params (kdef_signature d)) (kdef_value d))
 defn selected same_record supported)
 (fun (_different_name : Eq Bool (name_eqb n query) Bool.false)
 (old_lookup : Eq (OptionType KDefSig) (kdef_for env query) (OptionType.some KDefSig selected)) =>
 old query selected old_lookup)",
        "The actual stored-body support invariant is preserved by addDef, including shadowing, by inverting its real name-selection helper. This is only syntax support preservation, not valid declaration admission.",
    ),
    (
        r"def rec_env_rhs_paramfree_empty : RecEnvRhsParamFree RecEnv.empty :=
 fun (rn : Name) (cn : Name) (rule : RecRule)
 (found : Eq (OptionType RecRule) (recrule_for RecEnv.empty rn cn) (OptionType.some RecRule rule)) =>
 option_none_ne_some RecRule rule (KExprParamSupport (ListType.nil Name) (recrule_rhs rule)) found",
        "The actual empty recursor table discharges RHS syntax support by computed failed lookup. This supplies a concrete environment invariant, not an impossible inference premise.",
    ),
    (
        r"def rec_env_rhs_supported_empty : RecEnvRhsParamSupported RecEnv.empty :=
 rec_env_rhs_paramfree_supported RecEnv.empty rec_env_rhs_paramfree_empty",
        "The actual empty recursor environment satisfies the new signature-relative support invariant through the proved parameter-free compatibility implication.",
    ),
    (
        r"def kdecl_env_type_param_supported_singleton (n0 : Name) (sig0 : KConstSig)
 (supported : KExprParamSupport (kconst_params sig0) (kconst_type sig0)) :
 KDeclEnvTypeParamSupported (fun (n : Name) => opt_pick KConstSig (name_eqb n n0) sig0 (OptionType.none KConstSig)) :=
 fun (query : Name) (selected : KConstSig)
 (found : Eq (OptionType KConstSig) (opt_pick KConstSig (name_eqb query n0) sig0 (OptionType.none KConstSig)) (OptionType.some KConstSig selected)) =>
 opt_pick_some_inv KConstSig (name_eqb query n0) sig0 (OptionType.none KConstSig) selected
 (KExprParamSupport (kconst_params selected) (kconst_type selected)) found
 (fun (_same_name : Eq Bool (name_eqb query n0) Bool.true) (same_record : Eq KConstSig sig0 selected) =>
 Eq.subst KConstSig (fun (sig : KConstSig) => KExprParamSupport (kconst_params sig) (kconst_type sig))
 sig0 selected same_record supported)
 (fun (_different_name : Eq Bool (name_eqb query n0) Bool.false)
 (missing : Eq (OptionType KConstSig) (OptionType.none KConstSig) (OptionType.some KConstSig selected)) =>
 option_none_ne_some KConstSig selected (KExprParamSupport (kconst_params selected) (kconst_type selected)) missing)",
        "Actual singleton signature lookup discharges stored-type support, with record identity derived in the successful branch and absent names refused.",
    ),
    (
        r"def acceptance_example_parameter_support :
 LevelParamSupport (kconst_params acceptance_example_sig) (Level.param Name.anonymous) :=
 LevelParamSupport.param (ListType.cons Name Name.anonymous (ListType.nil Name)) Name.anonymous Nat.zero
 (Eq.refl (OptionType Nat) (OptionType.some Nat Nat.zero))",
        "The concrete schematic parameter actually appears at index zero in the existing acceptance example signature.",
    ),
    (
        r"def acceptance_example_def_body_supported : DefEnvBodyParamSupported (red_def acceptance_example_env) :=
 def_env_body_param_supported_add DefEnv.empty def_env_body_param_supported_empty Name.anonymous
 (KDefSig.mk acceptance_example_sig (KExpr.sort (Level.param Name.anonymous)))
 (KExprParamSupport.sort (kconst_params acceptance_example_sig) (Level.param Name.anonymous)
 acceptance_example_parameter_support)",
        "Discharge actual stored-body support of the existing nonempty polymorphic definition environment, using its declared parameter rather than a per-instance body theorem.",
    ),
    (
        r"def acceptance_example_types_supported : KDeclEnvTypeParamSupported acceptance_example_tenv :=
 kdecl_env_type_param_supported_singleton Name.anonymous acceptance_example_sig
 (KExprParamSupport.sort (kconst_params acceptance_example_sig) (Level.succ (Level.param Name.anonymous))
 (LevelParamSupport.succ (kconst_params acceptance_example_sig) (Level.param Name.anonymous)
 acceptance_example_parameter_support))",
        "Discharge actual schematic signature-type support of the matching nonempty type environment, including the successor around its parameter.",
    ),
    (
        r"def acceptance_example_schematic_body_typed :
 TypingCtxConvIn acceptance_example_env acceptance_example_tenv (ListType.nil KExpr)
 (KExpr.sort (Level.param Name.anonymous)) (kconst_type acceptance_example_sig) :=
 TypingCtxConvIn.sort acceptance_example_env acceptance_example_tenv (ListType.nil KExpr)
 (Level.param Name.anonymous)",
        "One actual schematic body derivation under the same matched type/reduction environment; this is the input to the generic instantiation theorem.",
    ),
    (
        r"def acceptance_example_instantiated_body_typed (u : Level) :
 TypingCtxConvIn acceptance_example_env acceptance_example_tenv (ListType.nil KExpr)
 (KExpr.sort u) (KExpr.sort (Level.succ u)) :=
 typingctxconv_in_kdef_instantiated acceptance_example_env acceptance_example_def_body_supported
 rec_env_rhs_supported_empty acceptance_example_tenv acceptance_example_types_supported
 (KDefSig.mk acceptance_example_sig (KExpr.sort (Level.param Name.anonymous)))
 (ListType.cons Level u (ListType.nil Level)) acceptance_example_schematic_body_typed",
        "Apply the generic schematic-body theorem to the actual nonempty matched environment at every universe, with every syntax and typing premise discharged.",
    ),
    (
        r"def acceptance_example_instantiated_body_nonzero :
 TypingCtxConvIn acceptance_example_env acceptance_example_tenv (ListType.nil KExpr)
 (KExpr.sort (Level.succ Level.zero)) (KExpr.sort (Level.succ (Level.succ Level.zero))) :=
 acceptance_example_instantiated_body_typed (Level.succ Level.zero)",
        "Nonzero universe instance actually reaches the composed body theorem and changes the schematic parameter into Sort 1 with type Sort 2.",
    ),
    (
        r"def acceptance_example_constant_instantiation_caller (u : Level) :
 TypingCtxConvIn acceptance_example_env acceptance_example_tenv (ListType.nil KExpr)
 (KExpr.const Name.anonymous (ListType.cons Level u (ListType.nil Level)))
 (KExpr.sort (Level.succ u)) :=
 typingctxconv_in_instL_supported acceptance_example_env acceptance_example_def_body_supported
 rec_env_rhs_supported_empty acceptance_example_tenv acceptance_example_types_supported
 (fun (_n : Name) => u) (ListType.nil KExpr)
 (KExpr.const Name.anonymous (ListType.cons Level (Level.param Name.anonymous) (ListType.nil Level)))
 (KExpr.sort (Level.succ (Level.param Name.anonymous)))
 (TypingCtxConvIn.const acceptance_example_env acceptance_example_tenv (ListType.nil KExpr)
 Name.anonymous (ListType.cons Level (Level.param Name.anonymous) (ListType.nil Level))
 (KExpr.sort (Level.succ (Level.param Name.anonymous)))
 (Eq.refl (OptionType KExpr) (OptionType.some KExpr (KExpr.sort (Level.succ (Level.param Name.anonymous))))))",
        "The actual constant constructor with computed guarded lookup reaches the generic typing substitution theorem; its result instantiates both constant universe arguments and the retained type.",
    ),
    (
        r"def acceptance_example_semantic_conversion_typed :
 TypingCtxConvIn acceptance_example_env acceptance_example_tenv (ListType.nil KExpr)
 (KExpr.sort (Level.imax (Level.param Name.anonymous) Level.zero)) (KExpr.sort (Level.succ Level.zero)) :=
 TypingCtxConvIn.conv acceptance_example_env acceptance_example_tenv (ListType.nil KExpr)
 (KExpr.sort (Level.imax (Level.param Name.anonymous) Level.zero))
 (KExpr.sort (Level.succ (Level.imax (Level.param Name.anonymous) Level.zero)))
 (KExpr.sort (Level.succ Level.zero))
 (TypingCtxConvIn.sort acceptance_example_env acceptance_example_tenv (ListType.nil KExpr)
 (Level.imax (Level.param Name.anonymous) Level.zero))
 (DefEqIn.levels acceptance_example_env
 (KExpr.sort (Level.succ (Level.imax (Level.param Name.anonymous) Level.zero)))
 (KExpr.sort (Level.succ Level.zero))
 (KExprUniverseEq.sort (Level.succ (Level.imax (Level.param Name.anonymous) Level.zero))
 (Level.succ Level.zero) (fun (_v : Name -> Nat) => Eq.refl Nat (Nat.succ Nat.zero))))",
        "An actual typing derivation uses semantic imax conversion rather than raw syntactic equality; this exercises the new conversion arm's premises.",
    ),
    (
        r"def acceptance_example_semantic_typing_instantiation_caller :
 TypingCtxConvIn acceptance_example_env acceptance_example_tenv (ListType.nil KExpr)
 (KExpr.sort (Level.imax (Level.succ Level.zero) Level.zero)) (KExpr.sort (Level.succ Level.zero)) :=
 typingctxconv_in_instL_supported acceptance_example_env acceptance_example_def_body_supported
 rec_env_rhs_supported_empty acceptance_example_tenv acceptance_example_types_supported
 (fun (_n : Name) => Level.succ Level.zero) (ListType.nil KExpr)
 (KExpr.sort (Level.imax (Level.param Name.anonymous) Level.zero)) (KExpr.sort (Level.succ Level.zero))
 acceptance_example_semantic_conversion_typed",
        "A nonidentity universe substitution consumes actual semantic-conversion typing in the inhabited matched environment, so the checked preservation result is not only a sort-constructor fixture.",
    ),
];

impl Specification {
    pub(super) fn add_semantic_typing_universe_instantiation(&mut self) -> Result<(), SpecError> {
        for (source, description) in PROOFS.iter().chain(CONTROLS) {
            self.add_recursive_def(source, description)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn supported_semantic_typing_substitution_and_actual_callers_are_checked() {
        let spec = crate::test_utils::build_spec_with_stack();
        for name in [
            "KDeclEnvTypeParamSupported",
            "typingctxconv_in_instL_supported",
            "typingctxconv_in_instLevels_supported",
            "typingctxconv_in_kdef_instantiated",
            "def_env_body_param_supported_add",
            "rec_env_rhs_paramfree_empty",
            "rec_env_rhs_supported_empty",
            "kdecl_env_type_param_supported_singleton",
            "acceptance_example_parameter_support",
            "acceptance_example_def_body_supported",
            "acceptance_example_types_supported",
            "acceptance_example_schematic_body_typed",
            "acceptance_example_instantiated_body_typed",
            "acceptance_example_instantiated_body_nonzero",
            "acceptance_example_constant_instantiation_caller",
            "acceptance_example_semantic_conversion_typed",
            "acceptance_example_semantic_typing_instantiation_caller",
        ] {
            let definition = spec.definitions().get(name).expect("registered proof");
            assert!(!definition.is_axiom, "{name}");
            assert!(definition.elaborated_value.is_some(), "{name}");
            assert!(
                crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty(),
                "{name}"
            );
        }
    }

    #[test]
    fn semantic_typing_substitution_cannot_reuse_an_unsubstituted_derivation_or_wrong_type() {
        crate::test_utils::run_with_stack(|| {
            let mut spec = crate::test_utils::build_spec_with_stack();
            for (name, ty, value) in [
                (
                    "fake_semantic_typing_substitution_identity",
                    "forall (R : RedEnv) (tenv : KDeclEnv) (s : Name -> Level) (G : ListType KExpr) (e : KExpr) (T : KExpr), TypingCtxConvIn R tenv G e T -> TypingCtxConvIn R tenv (mapLT (instL s) G) (instL s e) (instL s T)",
                    "fun (R : RedEnv) (tenv : KDeclEnv) (s : Name -> Level) (G : ListType KExpr) (e : KExpr) (T : KExpr) (h : TypingCtxConvIn R tenv G e T) => h",
                ),
                (
                    "fake_semantic_instantiated_body_wrong_sort",
                    "forall (u : Level), TypingCtxConvIn acceptance_example_env acceptance_example_tenv (ListType.nil KExpr) (KExpr.sort u) (KExpr.sort u)",
                    "fun (u : Level) => acceptance_example_instantiated_body_typed u",
                ),
            ] {
                assert!(
                    crate::spec::core_spec::acceptance_in::theorem(
                        &mut spec,
                        name,
                        ty,
                        value,
                        "Negative control: neither the old derivation nor a correctly typed universe instance establishes the fabricated conclusion.",
                    )
                    .is_err(),
                    "{name}"
                );
            }
        });
    }
}

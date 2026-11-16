// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Raw universe substitution preserves the seven-constructor TypingCtx judgment.
//!
//! Ports the exact-source, two-edit prototype checked in
//! scratch/self-verification-typingctx-instantiation-2026-09-08.lean.
//! The live judgment must use KDeclEnv and computed kdecl_type_at at constants.
//! This is not TypingCtxConv preservation or production checker refinement.
//! Stored schematic-type support is the only environment premise; actual
//! lookup inversion supplies constant arity, and no per-output typing is assumed.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

fn instantiation_theorem(
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
    /// Requires signature-aware TypingCtx, declaration_lookup_instantiation,
    /// mapLT, and univ_poly's instL_lift_at / instL_instantiate commutations.
    pub(super) fn add_typingctx_universe_instantiation(&mut self) -> Result<(), SpecError> {
        instantiation_theorem(
            self,
            "ctx_lookup_mapLT",
            r"forall (f : KExpr -> KExpr) (G : ListType KExpr) (i : Nat),
 @Eq (OptionType KExpr) (ctx_lookup (mapLT f G) i) (@OptionType.rec KExpr (fun (_ : OptionType KExpr) => OptionType KExpr) (@OptionType.none KExpr) (fun (A0 : KExpr) => @OptionType.some KExpr (f A0)) (ctx_lookup G i))",
            r"fun (f : KExpr -> KExpr) (G : ListType KExpr) (i : Nat) =>
 @ListType.rec KExpr
   (fun (G0 : ListType KExpr) => forall (i0 : Nat),
     @Eq (OptionType KExpr) (ctx_lookup (mapLT f G0) i0) (@OptionType.rec KExpr (fun (_ : OptionType KExpr) => OptionType KExpr) (@OptionType.none KExpr) (fun (A0 : KExpr) => @OptionType.some KExpr (f A0)) (ctx_lookup G0 i0)))
   (fun (i0 : Nat) => @Eq.refl (OptionType KExpr) (@OptionType.none KExpr))
   (fun (A : KExpr) (rest : ListType KExpr)
     (ih : forall (i0 : Nat), @Eq (OptionType KExpr)
       (ctx_lookup (mapLT f rest) i0) (@OptionType.rec KExpr (fun (_ : OptionType KExpr) => OptionType KExpr) (@OptionType.none KExpr) (fun (A0 : KExpr) => @OptionType.some KExpr (f A0)) (ctx_lookup rest i0)))
     (i0 : Nat) =>
     @Nat.rec
       (fun (j : Nat) => @Eq (OptionType KExpr)
         (ctx_lookup (mapLT f (@ListType.cons KExpr A rest)) j)
         (@OptionType.rec KExpr (fun (_ : OptionType KExpr) => OptionType KExpr) (@OptionType.none KExpr) (fun (A0 : KExpr) => @OptionType.some KExpr (f A0)) (ctx_lookup (@ListType.cons KExpr A rest) j)))
       (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (f A)))
       (fun (j : Nat)
         (_ihj : @Eq (OptionType KExpr)
           (ctx_lookup (mapLT f (@ListType.cons KExpr A rest)) j)
           (@OptionType.rec KExpr (fun (_ : OptionType KExpr) => OptionType KExpr) (@OptionType.none KExpr) (fun (A0 : KExpr) => @OptionType.some KExpr (f A0)) (ctx_lookup (@ListType.cons KExpr A rest) j))) => ih j)
       i0)
   G i",
            "Mapping any function over the stored context commutes with actual ctx_lookup, including unsuccessful/out-of-range lookup.",
        )?;

        instantiation_theorem(
            self,
            "ctx_lookup_mapLT_some",
            r"forall (f : KExpr -> KExpr) (G : ListType KExpr) (i : Nat) (A : KExpr),
 @Eq (OptionType KExpr) (ctx_lookup G i) (@OptionType.some KExpr A) ->
 @Eq (OptionType KExpr) (ctx_lookup (mapLT f G) i) (@OptionType.some KExpr (f A))",
            r"fun (f : KExpr -> KExpr) (G : ListType KExpr) (i : Nat) (A : KExpr)
 (found : @Eq (OptionType KExpr) (ctx_lookup G i) (@OptionType.some KExpr A)) =>
 @Eq.trans (OptionType KExpr)
   (ctx_lookup (mapLT f G) i) (@OptionType.rec KExpr (fun (_ : OptionType KExpr) => OptionType KExpr) (@OptionType.none KExpr) (fun (A0 : KExpr) => @OptionType.some KExpr (f A0)) (ctx_lookup G i))
   (@OptionType.some KExpr (f A))
   (ctx_lookup_mapLT f G i)
   (@Eq.cong (OptionType KExpr) (OptionType KExpr)
     (fun (r : OptionType KExpr) => (@OptionType.rec KExpr (fun (_ : OptionType KExpr) => OptionType KExpr) (@OptionType.none KExpr) (fun (A0 : KExpr) => @OptionType.some KExpr (f A0)) r))
     (ctx_lookup G i) (@OptionType.some KExpr A) found)",
            "A successful ctx_lookup transports through a mapped context with its stored type mapped by the same function.",
        )?;

        instantiation_theorem(
            self,
            "typingctx_instL",
            r"forall (tenv : KDeclEnv),
 (forall (n : Name) (sig : KConstSig),
   @Eq (OptionType KConstSig) (tenv n) (@OptionType.some KConstSig sig) ->
   KExprParamSupport (kconst_params sig) (kconst_type sig)) ->
 forall (s : Name -> Level) (G : ListType KExpr) (e : KExpr) (T : KExpr),
 TypingCtx tenv G e T ->
 TypingCtx tenv (mapLT (instL s) G) (instL s e) (instL s T)",
            r"fun (tenv : KDeclEnv)
 (supported : forall (n : Name) (sig : KConstSig),
   @Eq (OptionType KConstSig) (tenv n) (@OptionType.some KConstSig sig) ->
   KExprParamSupport (kconst_params sig) (kconst_type sig))
 (s : Name -> Level) (G : ListType KExpr) (e : KExpr) (T : KExpr)
 (typed : TypingCtx tenv G e T) =>
 @TypingCtx.rec tenv
   (fun (G0 : ListType KExpr) (e0 : KExpr) (T0 : KExpr)
     (_h : TypingCtx tenv G0 e0 T0) =>
     TypingCtx tenv (mapLT (instL s) G0) (instL s e0) (instL s T0))
   (fun (G0 : ListType KExpr) (i : Nat) (A : KExpr)
     (found : @Eq (OptionType KExpr) (ctx_lookup G0 i) (@OptionType.some KExpr A)) =>
     @Eq.substType KExpr
       (fun (T0 : KExpr) => TypingCtx tenv (mapLT (instL s) G0) (KExpr.bvar i) T0)
       (lift_at (instL s A) Nat.zero (Nat.succ i))
       (instL s (lift_at A Nat.zero (Nat.succ i)))
       (@Eq.symm KExpr (instL s (lift_at A Nat.zero (Nat.succ i)))
         (lift_at (instL s A) Nat.zero (Nat.succ i))
         (instL_lift_at s A Nat.zero (Nat.succ i)))
       (@TypingCtx.var tenv (mapLT (instL s) G0) i (instL s A)
         (ctx_lookup_mapLT_some (instL s) G0 i A found)))
   (fun (G0 : ListType KExpr) (u : Level) =>
     @TypingCtx.sort tenv (mapLT (instL s) G0) (substL s u))
   (fun (G0 : ListType KExpr) (A : KExpr) (B : KExpr) (u : Level) (v : Level)
     (_hA : TypingCtx tenv G0 A (KExpr.sort u))
     (_hB : TypingCtx tenv (@ListType.cons KExpr A G0) B (KExpr.sort v))
     (ihA : TypingCtx tenv (mapLT (instL s) G0) (instL s A) (instL s (KExpr.sort u)))
     (ihB : TypingCtx tenv (mapLT (instL s) (@ListType.cons KExpr A G0)) (instL s B) (instL s (KExpr.sort v))) =>
     @TypingCtx.pi tenv (mapLT (instL s) G0) (instL s A) (instL s B)
       (substL s u) (substL s v) ihA ihB)
   (fun (G0 : ListType KExpr) (A : KExpr) (b : KExpr) (B : KExpr) (u : Level)
     (_hA : TypingCtx tenv G0 A (KExpr.sort u))
     (_hb : TypingCtx tenv (@ListType.cons KExpr A G0) b B)
     (ihA : TypingCtx tenv (mapLT (instL s) G0) (instL s A) (instL s (KExpr.sort u)))
     (ihb : TypingCtx tenv (mapLT (instL s) (@ListType.cons KExpr A G0)) (instL s b) (instL s B)) =>
     @TypingCtx.lam tenv (mapLT (instL s) G0) (instL s A) (instL s b) (instL s B)
       (substL s u) ihA ihb)
   (fun (G0 : ListType KExpr) (f : KExpr) (a : KExpr) (A : KExpr) (B : KExpr)
     (_hf : TypingCtx tenv G0 f (KExpr.pi A B))
     (_ha : TypingCtx tenv G0 a A)
     (ihf : TypingCtx tenv (mapLT (instL s) G0) (instL s f) (instL s (KExpr.pi A B)))
     (iha : TypingCtx tenv (mapLT (instL s) G0) (instL s a) (instL s A)) =>
     @Eq.substType KExpr
       (fun (T0 : KExpr) => TypingCtx tenv (mapLT (instL s) G0)
         (KExpr.app (instL s f) (instL s a)) T0)
       (instantiate (instL s B) (instL s a)) (instL s (instantiate B a))
       (@Eq.symm KExpr (instL s (instantiate B a))
         (instantiate (instL s B) (instL s a)) (instL_instantiate s B a))
       (@TypingCtx.app tenv (mapLT (instL s) G0)
         (instL s f) (instL s a) (instL s A) (instL s B) ihf iha))
   (fun (G0 : ListType KExpr) (n : Name) (us : ListType Level) (A : KExpr)
     (found : @Eq (OptionType KExpr) (kdecl_type_at tenv n us) (@OptionType.some KExpr A)) =>
     @TypingCtx.const tenv (mapLT (instL s) G0) n (mapLL (substL s) us) (instL s A)
       (kdecl_type_at_instL_supported tenv supported n us A found s))
   (fun (G0 : ListType KExpr) (ty : KExpr) (v : KExpr) (b : KExpr) (B : KExpr) (u : Level)
     (_hty : TypingCtx tenv G0 ty (KExpr.sort u))
     (_hv : TypingCtx tenv G0 v ty)
     (_hb : TypingCtx tenv (@ListType.cons KExpr ty G0) b B)
     (ihty : TypingCtx tenv (mapLT (instL s) G0) (instL s ty) (instL s (KExpr.sort u)))
     (ihv : TypingCtx tenv (mapLT (instL s) G0) (instL s v) (instL s ty))
     (ihb : TypingCtx tenv (mapLT (instL s) (@ListType.cons KExpr ty G0)) (instL s b) (instL s B)) =>
     @Eq.substType KExpr
       (fun (T0 : KExpr) => TypingCtx tenv (mapLT (instL s) G0)
         (KExpr.let_ (instL s ty) (instL s v) (instL s b)) T0)
       (instantiate (instL s B) (instL s v)) (instL s (instantiate B v))
       (@Eq.symm KExpr (instL s (instantiate B v))
         (instantiate (instL s B) (instL s v)) (instL_instantiate s B v))
       (@TypingCtx.let_ tenv (mapLT (instL s) G0)
         (instL s ty) (instL s v) (instL s b) (instL s B) (substL s u)
         ihty ihv ihb))
   G e T typed",
            "Universe-substitution preservation for all seven TypingCtx constructors under support of stored schematic signature types. Constant arity is derived from successful computed lookup; no per-output typing law is assumed.",
        )?;

        instantiation_theorem(
            self,
            "typingctx_instLevels",
            r"forall (tenv : KDeclEnv),
 (forall (n : Name) (sig : KConstSig),
   @Eq (OptionType KConstSig) (tenv n) (@OptionType.some KConstSig sig) ->
   KExprParamSupport (kconst_params sig) (kconst_type sig)) ->
 forall (ps : ListType Name) (us : ListType Level)
   (G : ListType KExpr) (e : KExpr) (T : KExpr),
 TypingCtx tenv G e T ->
 TypingCtx tenv (mapLT (instL (paramSubstN ps us)) G)
   (instLevels ps e us) (instLevels ps T us)",
            r"fun (tenv : KDeclEnv)
 (supported : forall (n : Name) (sig : KConstSig),
   @Eq (OptionType KConstSig) (tenv n) (@OptionType.some KConstSig sig) ->
   KExprParamSupport (kconst_params sig) (kconst_type sig))
 (ps : ListType Name) (us : ListType Level)
 (G : ListType KExpr) (e : KExpr) (T : KExpr) (typed : TypingCtx tenv G e T) =>
 typingctx_instL tenv supported (paramSubstN ps us) G e T typed",
            "Specialization of TypingCtx universe-substitution preservation to paramSubstN/instLevels. No outer arity premise is needed for this total raw syntax statement.",
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::instantiation_theorem;
    use crate::spec::types::ProofStatus;
    use crate::test_utils::{build_spec_with_stack, run_with_stack};

    fn assert_body_type_mismatch(name: &str, error: &crate::spec::SpecError) {
        let crate::spec::SpecError::TypeError(detail) = error else {
            panic!("{name}: expected kernel body type mismatch, got {error:?}");
        };
        assert!(detail.starts_with(&format!("add_decl {name}:")), "{detail}");
        assert!(detail.contains("Type mismatch"), "{detail}");
    }

    #[test]
    fn typingctx_universe_instantiation_has_checked_values_and_empty_axiom_closures() {
        let spec = build_spec_with_stack();
        for name in [
            "ctx_lookup_mapLT",
            "ctx_lookup_mapLT_some",
            "typingctx_instL",
            "typingctx_instLevels",
        ] {
            let definition = spec
                .definitions()
                .get(name)
                .expect("registered context instantiation theorem");
            assert!(!definition.is_axiom);
            assert_eq!(definition.proof_status, ProofStatus::DerivedProved);
            assert!(definition.elaborated_value.is_some());
            assert!(
                crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty(),
                "{name} must have empty actual axiom closure"
            );
        }
    }

    #[test]
    fn mapped_context_transports_lookup_and_rejects_the_old_stored_type() {
        run_with_stack(|| {
            let mut spec = build_spec_with_stack();
            let context = "(@ListType.cons KExpr (KExpr.sort (Level.param Name.anonymous)) (@ListType.nil KExpr))";
            let function = "(instL (fun (_ : Name) => Level.zero))";
            instantiation_theorem(
                &mut spec,
                "typingctx_mapped_lookup_witness",
                &format!("Eq (OptionType KExpr) (ctx_lookup (mapLT {function} {context}) Nat.zero) (@OptionType.some KExpr (KExpr.sort Level.zero))"),
                &format!("ctx_lookup_mapLT_some {function} {context} Nat.zero (KExpr.sort (Level.param Name.anonymous)) (@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (KExpr.sort (Level.param Name.anonymous))))"),
                "Regression: successful lookup maps the stored universe-bearing type.",
            ).expect("mapped context lookup");
            assert!(crate::spec_axiom_closure::computed_axiom_closure(
                &spec,
                "typingctx_mapped_lookup_witness"
            )
            .is_empty());
            assert!(instantiation_theorem(
                &mut spec,
                "typingctx_unmapped_lookup_must_fail",
                &format!("Eq (OptionType KExpr) (ctx_lookup (mapLT {function} {context}) Nat.zero) (@OptionType.some KExpr (KExpr.sort (Level.param Name.anonymous)))"),
                "@Eq.refl (OptionType KExpr) (@OptionType.some KExpr (KExpr.sort (Level.param Name.anonymous)))",
                "Negative control: retaining the old stored type is not the mapped lookup result.",
            ).inspect_err(|error| assert_body_type_mismatch("typingctx_unmapped_lookup_must_fail", error))
            .is_err());
        });
    }
}

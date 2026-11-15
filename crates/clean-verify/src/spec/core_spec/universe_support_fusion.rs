// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Support-sensitive fusion for the existing raw universe-substitution model.
//!
//! Ports scratch/self-verification-universe-support-2026-09-08.lean, checked
//! against exact exported dependencies at fb013b509. Actual support predicates
//! and general proofs register before subject reduction. Only the control
//! method waits for the later implementation-model lookup counterexample.
//! Raw fusion needs support, not arity or NoDup: substL fixes the positional
//! lookup's zero default. Unknown names invalidate fusion, as a checked
//! exclusion witnesses. Arity and source HashMap uniqueness remain separate.
//!
//! This is not admitted-input support, smart-level semantics, Rust refinement,
//! or typing/conversion preservation. No such result is assumed as a field.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

fn support_theorem(
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
    /// General proofs require early support, univ_poly_structural (including
    /// the pure congr2 helper), and universe_closedness congr3. No C4 or
    /// implementation-model lookup dependency remains in this method.
    pub(super) fn add_universe_support_fusion(&mut self) -> Result<(), SpecError> {
        support_theorem(
            self,
            "list_getD_mapLL_substL",
            r"forall (s : Name -> Level) (us : ListType Level) (i : Nat),
 Eq Level (list_getD (mapLL (substL s) us) i) (substL s (list_getD us i))",
            r"fun (s : Name -> Level) (us : ListType Level) (i : Nat) =>
 ListType.rec Level (fun (us0 : ListType Level) => forall (i0 : Nat),
   Eq Level (list_getD (mapLL (substL s) us0) i0) (substL s (list_getD us0 i0)))
   (fun (i0 : Nat) => Eq.refl Level Level.zero)
   (fun (u : Level) (rest : ListType Level)
     (ih : forall (i0 : Nat), Eq Level (list_getD (mapLL (substL s) rest) i0) (substL s (list_getD rest i0)))
     (i0 : Nat) =>
     Nat.rec (fun (j : Nat) => Eq Level
       (list_getD (mapLL (substL s) (ListType.cons Level u rest)) j)
       (substL s (list_getD (ListType.cons Level u rest) j)))
       (Eq.refl Level (substL s u))
       (fun (j : Nat) (_ih : Eq Level
         (list_getD (mapLL (substL s) (ListType.cons Level u rest)) j)
         (substL s (list_getD (ListType.cons Level u rest) j))) => ih j) i0)
   us i",
            "Positional lookup commutes with mapped raw universe substitution even out of range: the existing zero default is fixed by substL.",
        )?;

        support_theorem(
            self,
            "level_list_len_mapLL",
            r"forall (f : Level -> Level) (us : ListType Level),
 Eq Nat (level_list_len (mapLL f us)) (level_list_len us)",
            r"fun (f : Level -> Level) (us : ListType Level) =>
 ListType.rec Level (fun (us0 : ListType Level) => Eq Nat (level_list_len (mapLL f us0)) (level_list_len us0))
   (Eq.refl Nat Nat.zero)
   (fun (u : Level) (rest : ListType Level)
     (ih : Eq Nat (level_list_len (mapLL f rest)) (level_list_len rest)) =>
     Eq.cong Nat Nat Nat.succ (level_list_len (mapLL f rest)) (level_list_len rest) ih) us",
            "Mapping any function over a level list preserves its actual recursively computed length.",
        )?;

        support_theorem(
            self,
            "paramSubstN_mapLL_supported",
            r"forall (ps : ListType Name) (us : ListType Level) (n : Name) (i : Nat),
 Eq (OptionType Nat) (nameIdx ps n) (OptionType.some Nat i) ->
 forall (s : Name -> Level),
 Eq Level (paramSubstN ps (mapLL (substL s) us) n) (substL s (paramSubstN ps us n))",
            r"fun (ps : ListType Name) (us : ListType Level) (n : Name) (i : Nat)
 (member : Eq (OptionType Nat) (nameIdx ps n) (OptionType.some Nat i))
 (s : Name -> Level) =>
 Eq.rec (OptionType Nat) (OptionType.some Nat i)
   (fun (r : OptionType Nat) (_h : Eq (OptionType Nat) (OptionType.some Nat i) r) => Eq Level
     (OptionType.rec Nat (fun (_ : OptionType Nat) => Level) (Level.param n)
       (fun (j : Nat) => list_getD (mapLL (substL s) us) j) r)
     (substL s (OptionType.rec Nat (fun (_ : OptionType Nat) => Level) (Level.param n)
       (fun (j : Nat) => list_getD us j) r)))
   (list_getD_mapLL_substL s us i) (nameIdx ps n)
   (Eq.symm (OptionType Nat) (nameIdx ps n) (OptionType.some Nat i) member)",
            "Parameter-substitution fusion at an actual supported name; requires only successful nameIdx membership, not arity or NoDup.",
        )?;

        support_theorem(
            self,
            "substL_congr_on_support",
            r"forall (ps : ListType Name) (l : Level), LevelParamSupport ps l ->
 forall (s : Name -> Level) (t : Name -> Level),
 (forall (n : Name) (i : Nat), Eq (OptionType Nat) (nameIdx ps n) (OptionType.some Nat i) -> Eq Level (s n) (t n)) ->
 Eq Level (substL s l) (substL t l)",
            r"fun (ps : ListType Name) (l : Level) (support : LevelParamSupport ps l)
 (s : Name -> Level) (t : Name -> Level)
 (agree : forall (n : Name) (i : Nat),
   Eq (OptionType Nat) (nameIdx ps n) (OptionType.some Nat i) -> Eq Level (s n) (t n)) =>
 LevelParamSupport.rec ps
   (fun (l0 : Level) (_h : LevelParamSupport ps l0) => Eq Level (substL s l0) (substL t l0))
   (Eq.refl Level Level.zero)
   (fun (u : Level) (_hu : LevelParamSupport ps u)
     (ihu : Eq Level (substL s u) (substL t u)) =>
     Eq.cong Level Level Level.succ (substL s u) (substL t u) ihu)
   (fun (u : Level) (v : Level) (_hu : LevelParamSupport ps u) (_hv : LevelParamSupport ps v)
     (ihu : Eq Level (substL s u) (substL t u)) (ihv : Eq Level (substL s v) (substL t v)) =>
     universe_bridge_congr2 Level Level Level Level.max
       (substL s u) (substL t u) (substL s v) (substL t v) ihu ihv)
   (fun (u : Level) (v : Level) (_hu : LevelParamSupport ps u) (_hv : LevelParamSupport ps v)
     (ihu : Eq Level (substL s u) (substL t u)) (ihv : Eq Level (substL s v) (substL t v)) =>
     universe_bridge_congr2 Level Level Level Level.imax
       (substL s u) (substL t u) (substL s v) (substL t v) ihu ihv)
   (fun (n : Name) (i : Nat)
     (member : Eq (OptionType Nat) (nameIdx ps n) (OptionType.some Nat i)) => agree n i member)
   l support",
            "Raw level substitution depends only on the values of names supported by this level. All five Level constructors are handled.",
        )?;

        support_theorem(
            self,
            "substL_param_instantiation_fusion",
            r"forall (ps : ListType Name) (us : ListType Level) (l : Level),
 LevelParamSupport ps l -> forall (s : Name -> Level),
 Eq Level (substL s (substL (paramSubstN ps us) l))
   (substL (paramSubstN ps (mapLL (substL s) us)) l)",
            r"fun (ps : ListType Name) (us : ListType Level) (l : Level)
 (support : LevelParamSupport ps l) (s : Name -> Level) =>
 Eq.trans Level
   (substL s (substL (paramSubstN ps us) l))
   (substL (fun (n : Name) => substL s (paramSubstN ps us n)) l)
   (substL (paramSubstN ps (mapLL (substL s) us)) l)
   (substL_substL s (paramSubstN ps us) l)
   (substL_congr_on_support ps l support
     (fun (n : Name) => substL s (paramSubstN ps us n))
     (paramSubstN ps (mapLL (substL s) us))
     (fun (n : Name) (i : Nat)
       (member : Eq (OptionType Nat) (nameIdx ps n) (OptionType.some Nat i)) =>
       Eq.symm Level (paramSubstN ps (mapLL (substL s) us) n)
         (substL s (paramSubstN ps us n)) (paramSubstN_mapLL_supported ps us n i member s)))",
            "Substitution through an instantiated supported Level equals instantiation with substituted arguments; proved from existing raw fusion and support, with no arity or uniqueness premise.",
        )?;

        support_theorem(
            self,
            "mapLL_congr_on_support",
            r"forall (ps : ListType Name) (us : ListType Level), LevelListParamSupport ps us ->
 forall (s : Name -> Level) (t : Name -> Level),
 (forall (n : Name) (i : Nat), Eq (OptionType Nat) (nameIdx ps n) (OptionType.some Nat i) -> Eq Level (s n) (t n)) ->
 Eq (ListType Level) (mapLL (substL s) us) (mapLL (substL t) us)",
            r"fun (ps : ListType Name) (us : ListType Level) (support : LevelListParamSupport ps us)
 (s : Name -> Level) (t : Name -> Level)
 (agree : forall (n : Name) (i : Nat),
   Eq (OptionType Nat) (nameIdx ps n) (OptionType.some Nat i) -> Eq Level (s n) (t n)) =>
 LevelListParamSupport.rec ps
   (fun (us0 : ListType Level) (_h : LevelListParamSupport ps us0) =>
     Eq (ListType Level) (mapLL (substL s) us0) (mapLL (substL t) us0))
   (Eq.refl (ListType Level) (ListType.nil Level))
   (fun (u : Level) (rest : ListType Level) (hu : LevelParamSupport ps u)
     (_hrest : LevelListParamSupport ps rest)
     (ih : Eq (ListType Level) (mapLL (substL s) rest) (mapLL (substL t) rest)) =>
     universe_bridge_congr2 Level (ListType Level) (ListType Level)
       (fun (head : Level) (tail : ListType Level) => ListType.cons Level head tail)
       (substL s u) (substL t u) (mapLL (substL s) rest) (mapLL (substL t) rest)
       (substL_congr_on_support ps u hu s t agree) ih)
   us support",
            "Agreement on supported names extends to every level in the whole argument list; no constant-level arguments are omitted.",
        )?;

        support_theorem(
            self,
            "instL_congr_on_support",
            r"forall (ps : ListType Name) (e : KExpr), KExprParamSupport ps e ->
 forall (s : Name -> Level) (t : Name -> Level),
 (forall (n : Name) (i : Nat), Eq (OptionType Nat) (nameIdx ps n) (OptionType.some Nat i) -> Eq Level (s n) (t n)) ->
 Eq KExpr (instL s e) (instL t e)",
            r"fun (ps : ListType Name) (e : KExpr) (support : KExprParamSupport ps e)
 (s : Name -> Level) (t : Name -> Level)
 (agree : forall (n : Name) (i : Nat),
   Eq (OptionType Nat) (nameIdx ps n) (OptionType.some Nat i) -> Eq Level (s n) (t n)) =>
 KExprParamSupport.rec ps
   (fun (e0 : KExpr) (_h : KExprParamSupport ps e0) => Eq KExpr (instL s e0) (instL t e0))
   (fun (u : Level) (hu : LevelParamSupport ps u) =>
     Eq.cong Level KExpr KExpr.sort (substL s u) (substL t u)
       (substL_congr_on_support ps u hu s t agree))
   (fun (i : Nat) => Eq.refl KExpr (KExpr.bvar i))
   (fun (f : KExpr) (a : KExpr) (_hf : KExprParamSupport ps f) (_ha : KExprParamSupport ps a)
     (ihf : Eq KExpr (instL s f) (instL t f)) (iha : Eq KExpr (instL s a) (instL t a)) =>
     universe_bridge_congr2 KExpr KExpr KExpr KExpr.app
       (instL s f) (instL t f) (instL s a) (instL t a) ihf iha)
   (fun (A : KExpr) (b : KExpr) (_hA : KExprParamSupport ps A) (_hb : KExprParamSupport ps b)
     (ihA : Eq KExpr (instL s A) (instL t A)) (ihb : Eq KExpr (instL s b) (instL t b)) =>
     universe_bridge_congr2 KExpr KExpr KExpr KExpr.lam
       (instL s A) (instL t A) (instL s b) (instL t b) ihA ihb)
   (fun (A : KExpr) (B : KExpr) (_hA : KExprParamSupport ps A) (_hB : KExprParamSupport ps B)
     (ihA : Eq KExpr (instL s A) (instL t A)) (ihB : Eq KExpr (instL s B) (instL t B)) =>
     universe_bridge_congr2 KExpr KExpr KExpr KExpr.pi
       (instL s A) (instL t A) (instL s B) (instL t B) ihA ihB)
   (fun (n : Name) (us : ListType Level) (hu : LevelListParamSupport ps us) =>
     Eq.cong (ListType Level) KExpr (fun (vs : ListType Level) => KExpr.const n vs)
       (mapLL (substL s) us) (mapLL (substL t) us)
       (mapLL_congr_on_support ps us hu s t agree))
   (fun (A : KExpr) (v : KExpr) (b : KExpr)
     (_hA : KExprParamSupport ps A) (_hv : KExprParamSupport ps v) (_hb : KExprParamSupport ps b)
     (ihA : Eq KExpr (instL s A) (instL t A))
     (ihv : Eq KExpr (instL s v) (instL t v))
     (ihb : Eq KExpr (instL s b) (instL t b)) =>
     psubst_closed_cong3 KExpr.let_
       (instL s A) (instL t A) (instL s v) (instL t v) (instL s b) (instL t b)
       ihA ihv ihb)
   (fun (sn : Name) (i : Nat) (sub : KExpr) (_hsub : KExprParamSupport ps sub)
     (ihsub : Eq KExpr (instL s sub) (instL t sub)) =>
     Eq.cong KExpr KExpr (fun (child : KExpr) => KExpr.proj sn i child)
       (instL s sub) (instL t sub) ihsub)
   (fun (n : Nat) => Eq.refl KExpr (KExpr.lit n))
   e support",
            "Raw instantiation depends only on supported parameter names over every existing KExpr constructor. The proof traverses sorts, full constant-level lists, binders, lets and projections, and preserves every tagged literal payload.",
        )?;

        support_theorem(
            self,
            "instL_instLevels_supported",
            r"forall (ps : ListType Name) (T : KExpr) (us : ListType Level),
 KExprParamSupport ps T -> forall (s : Name -> Level),
 Eq KExpr (instL s (instLevels ps T us)) (instLevels ps T (mapLL (substL s) us))",
            r"fun (ps : ListType Name) (T : KExpr) (us : ListType Level)
 (support : KExprParamSupport ps T) (s : Name -> Level) =>
 Eq.trans KExpr
   (instL s (instLevels ps T us))
   (instL (fun (n : Name) => substL s (paramSubstN ps us n)) T)
   (instLevels ps T (mapLL (substL s) us))
   (instL_instL s (paramSubstN ps us) T)
   (instL_congr_on_support ps T support
     (fun (n : Name) => substL s (paramSubstN ps us n))
     (paramSubstN ps (mapLL (substL s) us))
     (fun (n : Name) (i : Nat)
       (member : Eq (OptionType Nat) (nameIdx ps n) (OptionType.some Nat i)) =>
       Eq.symm Level (paramSubstN ps (mapLL (substL s) us) n)
         (substL s (paramSubstN ps us n)) (paramSubstN_mapLL_supported ps us n i member s)))",
            "The exact raw type equation needed in the future constant case: the referenced declaration's schematic type is supported by its own parameter list. This proves substitution fusion, not typing/conversion preservation or Rust refinement; no arity or NoDup premise is needed for this raw equality.",
        )?;

        support_theorem(
            self,
            "arity_mapLL",
            r"forall (ps : ListType Name) (us : ListType Level),
 Eq Nat (name_list_len ps) (level_list_len us) -> forall (f : Level -> Level),
 Eq Nat (name_list_len ps) (level_list_len (mapLL f us))",
            r"fun (ps : ListType Name) (us : ListType Level)
 (arity : Eq Nat (name_list_len ps) (level_list_len us)) (f : Level -> Level) =>
 Eq.trans Nat (name_list_len ps) (level_list_len us) (level_list_len (mapLL f us))
   arity (Eq.symm Nat (level_list_len (mapLL f us)) (level_list_len us)
     (level_list_len_mapLL f us))",
            "Mapping universe arguments preserves a separately supplied exact-arity premise. Unlike raw fusion, successful constant typing/source-model lookup still requires this premise.",
        )?;

        Ok(())
    }

    /// Late controls: the unsupported-name exclusion reuses the checked source-shaped lookup/default counterexample.
    pub(super) fn add_universe_support_fusion_controls(&mut self) -> Result<(), SpecError> {
        support_theorem(
            self,
            "supported_nonzero_fusion_witness",
            r"Eq Level
 (substL (fun (_ : Name) => Level.succ Level.zero)
   (substL (paramSubstN (ListType.cons Name Name.anonymous (ListType.nil Name))
     (ListType.cons Level (Level.param Name.anonymous) (ListType.nil Level)))
     (Level.param Name.anonymous)))
 (Level.succ Level.zero)",
            r"substL_param_instantiation_fusion
 (ListType.cons Name Name.anonymous (ListType.nil Name))
 (ListType.cons Level (Level.param Name.anonymous) (ListType.nil Level))
 (Level.param Name.anonymous)
 (LevelParamSupport.param (ListType.cons Name Name.anonymous (ListType.nil Name))
   Name.anonymous Nat.zero (Eq.refl (OptionType Nat) (OptionType.some Nat Nat.zero)))
 (fun (_ : Name) => Level.succ Level.zero)",
            "Positive control: supported nested instantiation actually substitutes a nonzero universe, rather than silently leaving the schematic parameter unchanged.",
        )?;

        support_theorem(
            self,
            "unsupported_fusion_fails",
            r"Eq Level
 (substL (fun (_ : Name) => Level.zero)
   (substL (paramSubstN (ListType.nil Name) (ListType.nil Level)) (Level.param Name.anonymous)))
 (substL (paramSubstN (ListType.nil Name)
   (mapLL (substL (fun (_ : Name) => Level.zero)) (ListType.nil Level)))
   (Level.param Name.anonymous)) -> Empty",
            r"param_lookup_short_lists_differ",
            "Constructive negative control: removing the support premise permits an unknown parameter, and the claimed fusion equality then implies Empty. Reuses the already checked zero-versus-parameter discrimination.",
        )?;

        support_theorem(
            self,
            "supported_projection_fusion_witness",
            r"Eq KExpr
 (instL (fun (_ : Name) => Level.succ Level.zero)
   (instLevels (ListType.cons Name Name.anonymous (ListType.nil Name))
     (KExpr.proj Name.anonymous Nat.zero
       (KExpr.const Name.anonymous (ListType.cons Level (Level.param Name.anonymous) (ListType.nil Level))))
     (ListType.cons Level (Level.param Name.anonymous) (ListType.nil Level))))
 (KExpr.proj Name.anonymous Nat.zero
   (KExpr.const Name.anonymous (ListType.cons Level (Level.succ Level.zero) (ListType.nil Level))))",
            r"instL_instLevels_supported
 (ListType.cons Name Name.anonymous (ListType.nil Name))
 (KExpr.proj Name.anonymous Nat.zero
   (KExpr.const Name.anonymous (ListType.cons Level (Level.param Name.anonymous) (ListType.nil Level))))
 (ListType.cons Level (Level.param Name.anonymous) (ListType.nil Level))
 (KExprParamSupport.proj
   (ListType.cons Name Name.anonymous (ListType.nil Name)) Name.anonymous Nat.zero
   (KExpr.const Name.anonymous (ListType.cons Level (Level.param Name.anonymous) (ListType.nil Level)))
   (KExprParamSupport.const
     (ListType.cons Name Name.anonymous (ListType.nil Name)) Name.anonymous
     (ListType.cons Level (Level.param Name.anonymous) (ListType.nil Level))
     (LevelListParamSupport.cons
       (ListType.cons Name Name.anonymous (ListType.nil Name))
       (Level.param Name.anonymous) (ListType.nil Level)
       (LevelParamSupport.param
         (ListType.cons Name Name.anonymous (ListType.nil Name)) Name.anonymous Nat.zero
         (Eq.refl (OptionType Nat) (OptionType.some Nat Nat.zero)))
       (LevelListParamSupport.nil (ListType.cons Name Name.anonymous (ListType.nil Name))))))
 (fun (_ : Name) => Level.succ Level.zero)",
            "Nonzero positive control for a projection containing a parameterized constant. Checks whole level-list traversal and projection support, without asserting projection typing.",
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::support_theorem;
    use crate::spec::types::ProofStatus;
    use crate::test_utils::{build_spec_with_stack, run_with_stack};

    #[test]
    fn support_fusion_terms_have_checked_values_and_empty_axiom_closures() {
        let spec = build_spec_with_stack();
        for name in [
            "list_getD_mapLL_substL",
            "level_list_len_mapLL",
            "paramSubstN_mapLL_supported",
            "substL_congr_on_support",
            "substL_param_instantiation_fusion",
            "supported_nonzero_fusion_witness",
            "unsupported_fusion_fails",
            "mapLL_congr_on_support",
            "instL_congr_on_support",
            "instL_instLevels_supported",
            "arity_mapLL",
            "supported_projection_fusion_witness",
        ] {
            let definition = spec
                .definitions()
                .get(name)
                .expect("registered support theorem");
            assert!(!definition.is_axiom, "{name} must carry a checked value");
            assert_eq!(definition.proof_status, ProofStatus::DerivedProved);
            assert!(
                definition.elaborated_value.is_some(),
                "{name} must be elaborated"
            );
            assert!(
                crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty(),
                "{name} must have empty actual transitive axiom closure"
            );
        }
    }

    #[test]
    fn support_fusion_keeps_minimal_premises_and_rejects_missing_support() {
        run_with_stack(|| {
            let mut spec = build_spec_with_stack();
            // Duplicate declared names and a short argument list are deliberate:
            // raw first-match fusion remains valid without either premise.
            // This does not establish production HashMap behavior or arity.
            support_theorem(
                &mut spec,
                "support_duplicate_short_raw_fusion_witness",
                r"Eq KExpr
 (instL (fun (_ : Name) => Level.succ Level.zero)
   (instLevels
     (ListType.cons Name Name.anonymous (ListType.cons Name Name.anonymous (ListType.nil Name)))
     (KExpr.sort (Level.param Name.anonymous)) (ListType.nil Level)))
 (KExpr.sort Level.zero)",
                r"instL_instLevels_supported
 (ListType.cons Name Name.anonymous (ListType.cons Name Name.anonymous (ListType.nil Name)))
 (KExpr.sort (Level.param Name.anonymous)) (ListType.nil Level)
 (KExprParamSupport.sort
   (ListType.cons Name Name.anonymous (ListType.cons Name Name.anonymous (ListType.nil Name)))
   (Level.param Name.anonymous)
   (LevelParamSupport.param
     (ListType.cons Name Name.anonymous (ListType.cons Name Name.anonymous (ListType.nil Name)))
     Name.anonymous Nat.zero (Eq.refl (OptionType Nat) (OptionType.some Nat Nat.zero))))
 (fun (_ : Name) => Level.succ Level.zero)",
                "Minimal-premise regression: duplicate parameters and missing arguments do not break the raw supported fusion equation.",
            ).expect("raw fusion must not accidentally acquire arity or uniqueness premises");
            support_theorem(
                &mut spec,
                "support_every_literal_payload_fusion_witness",
                r"forall (ps : ListType Name) (us : ListType Level) (s : Name -> Level) (n : Nat),
 Eq KExpr (instL s (instLevels ps (KExpr.lit n) us)) (KExpr.lit n)",
                r"fun (ps : ListType Name) (us : ListType Level) (s : Name -> Level) (n : Nat) =>
 instL_instLevels_supported ps (KExpr.lit n) us (KExprParamSupport.lit ps n) s",
                "Generic regression: every existing encoded literal payload, not only one chosen literal kind, survives supported fusion unchanged.",
            ).expect("both literal kinds and all payloads are retained");
            for name in [
                "support_duplicate_short_raw_fusion_witness",
                "support_every_literal_payload_fusion_witness",
            ] {
                assert!(crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty());
            }
            assert!(support_theorem(
                &mut spec,
                "support_unknown_parameter_equality_must_fail",
                r"Eq Level
 (substL (fun (_ : Name) => Level.zero)
   (substL (paramSubstN (ListType.nil Name) (ListType.nil Level)) (Level.param Name.anonymous)))
 (substL (paramSubstN (ListType.nil Name)
   (mapLL (substL (fun (_ : Name) => Level.zero)) (ListType.nil Level)))
   (Level.param Name.anonymous))",
                "Eq.refl Level Level.zero",
                "Negative control: unsupported fusion is not a definitional equality.",
            )
            .is_err());
            assert!(support_theorem(
                &mut spec,
                "support_false_membership_must_fail",
                "Eq (OptionType Nat) (nameIdx (ListType.nil Name) Name.anonymous) (OptionType.some Nat Nat.zero)",
                "Eq.refl (OptionType Nat) (OptionType.some Nat Nat.zero)",
                "Negative control: unknown parameter support cannot be supplied by a fabricated successful lookup.",
            ).is_err());
        });
    }
}

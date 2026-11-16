// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Universe substitution commutes with the current implementation-model translation.
//!
//! These are proof terms about the two existing raw models, not extracted Rust.
//! In particular, checked arity relates their positional and zipped first-match
//! lookups; it does not prove Rust's hash-map or smart-constructor behavior.
//! The independent exact-export guide is
//! `scratch/self-verification-instantiation-2026-09-08.lean`.

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
    /// Pure Eq congruence only; invoked by add_univ_poly_structural before
    /// typing/metatheory. The implementation-model bridge stays at its old slot.
    pub(super) fn add_universe_congruence(&mut self) -> Result<(), SpecError> {
        instantiation_theorem(
            self,
            "universe_bridge_congr2",
            r"forall (A : Type) (B : Type) (C : Type) (f : A -> B -> C)
    (a : A) (a2 : A) (b : B) (b2 : B)
    (ha : @Eq A a a2) (hb : @Eq B b b2), @Eq C (f a b) (f a2 b2)",
            r"fun (A : Type) (B : Type) (C : Type) (f : A -> B -> C)
    (a : A) (a2 : A) (b : B) (b2 : B)
    (ha : @Eq A a a2) (hb : @Eq B b b2) =>
  @Eq.trans C (f a b) (f a2 b) (f a2 b2)
    (@Eq.cong A C (fun (x : A) => f x b) a a2 ha)
    (@Eq.cong B C (fun (y : B) => f a2 y) b b2 hb)",
            "Two-argument congruence for the level, list and expression constructors in the raw instantiation bridge.",
        )?;
        Ok(())
    }

    /// Requires the universe substrate, lookup agreement, and C4 translation.
    pub(super) fn add_universe_instantiation_bridge(&mut self) -> Result<(), SpecError> {
        instantiation_theorem(
            self,
            "level_subst_eq_substL",
            r"forall (ps : ListType Name) (us : ListType Level)
    (arity : @Eq Nat (name_list_len ps) (level_list_len us)) (l : Level),
    @Eq Level (level_subst ps us l) (substL (paramSubstN ps us) l)",
            r"fun (ps : ListType Name) (us : ListType Level)
    (arity : @Eq Nat (name_list_len ps) (level_list_len us)) (l : Level) =>
  @Level.rec (fun (l0 : Level) =>
    @Eq Level (level_subst ps us l0) (substL (paramSubstN ps us) l0))
    (@Eq.refl Level Level.zero)
    (fun (u : Level)
      (ih : @Eq Level (level_subst ps us u) (substL (paramSubstN ps us) u)) =>
        Eq.cong Level Level Level.succ
          (level_subst ps us u) (substL (paramSubstN ps us) u) ih)
    (fun (u : Level) (v : Level)
      (ihu : @Eq Level (level_subst ps us u) (substL (paramSubstN ps us) u))
      (ihv : @Eq Level (level_subst ps us v) (substL (paramSubstN ps us) v)) =>
        universe_bridge_congr2 Level Level Level Level.max
          (level_subst ps us u) (substL (paramSubstN ps us) u)
          (level_subst ps us v) (substL (paramSubstN ps us) v) ihu ihv)
    (fun (u : Level) (v : Level)
      (ihu : @Eq Level (level_subst ps us u) (substL (paramSubstN ps us) u))
      (ihv : @Eq Level (level_subst ps us v) (substL (paramSubstN ps us) v)) =>
        universe_bridge_congr2 Level Level Level Level.imax
          (level_subst ps us u) (substL (paramSubstN ps us) u)
          (level_subst ps us v) (substL (paramSubstN ps us) v) ihu ihv)
    (fun (n : Name) => Eq.symm Level (paramSubstN ps us n)
      (level_subst ps us (Level.param n))
      (paramSubstN_eq_level_lookup ps us n arity)) l",
            "Arity-checked agreement of the two raw level substitutions. Structural induction discharges every Level constructor; parameter lookup uses a proved equation, not an assumed result equality.",
        )?;

        instantiation_theorem(
            self,
            "impl_inst_levels_list_eq_mapLL",
            r"forall (ps : ListType Name) (us : ListType Level)
    (arity : @Eq Nat (name_list_len ps) (level_list_len us)) (vs : ListType Level),
    @Eq (ListType Level) (impl_inst_levels_list ps us vs)
      (mapLL (substL (paramSubstN ps us)) vs)",
            r"fun (ps : ListType Name) (us : ListType Level)
    (arity : @Eq Nat (name_list_len ps) (level_list_len us)) (vs : ListType Level) =>
  @ListType.rec Level (fun (vs0 : ListType Level) =>
      @Eq (ListType Level) (impl_inst_levels_list ps us vs0)
        (mapLL (substL (paramSubstN ps us)) vs0))
    (@Eq.refl (ListType Level) (@ListType.nil Level))
    (fun (v : Level) (rest : ListType Level)
      (ih : @Eq (ListType Level) (impl_inst_levels_list ps us rest)
        (mapLL (substL (paramSubstN ps us)) rest)) =>
      universe_bridge_congr2 Level (ListType Level) (ListType Level)
        (fun (head : Level) (tail : ListType Level) => @ListType.cons Level head tail)
        (level_subst ps us v) (substL (paramSubstN ps us) v)
        (impl_inst_levels_list ps us rest) (mapLL (substL (paramSubstN ps us)) rest)
        (level_subst_eq_substL ps us arity v) ih) vs",
            "Raw substitution agreement lifts to every constant node's universe list by list induction.",
        )?;

        instantiation_theorem(
            self,
            "instL_preserves_impl_literal",
            r"forall (s : Name -> Level) (lt : ImplLit),
    @Eq KExpr (impl_lit_to_kexpr lt) (instL s (impl_lit_to_kexpr lt))",
            r"fun (s : Name -> Level) (lt : ImplLit) =>
  @ImplLit.rec (fun (lt0 : ImplLit) =>
      @Eq KExpr (impl_lit_to_kexpr lt0) (instL s (impl_lit_to_kexpr lt0)))
    (fun (n : Nat) => @Eq.refl KExpr (literal_nat n))
    (fun (n : Nat) => @Eq.refl KExpr (literal_string n)) lt",
            "Raw universe substitution leaves both tagged model literal kinds unchanged, for every payload.",
        )?;

        // Generate only repetitive, fully explicit equality telescopes. No
        // proof hole, trusted equation, source-code claim or omitted arm is
        // introduced by this Rust formatting helper.
        let lhs = |e: &str, d: &str| format!("(to_kexpr_at (impl_inst_levels ps us {e}) rho {d})");
        let rhs = |e: &str, d: &str| format!("(instLevels ps (to_kexpr_at {e} rho {d}) us)");
        let ih = |e: &str| {
            format!(
                "forall (rho : ListType Nat) (d : Nat), @Eq KExpr {} {}",
                lhs(e, "d"),
                rhs(e, "d")
            )
        };
        let binary_minor = |constructor: &str, binder: bool| {
            let annotation = if binder { "(_bd : BinderData) " } else { "" };
            let body_depth = if binder { "(Nat.succ d)" } else { "d" };
            format!(
                "(fun {annotation}(a : ImplExpr) (b : ImplExpr) \
                 (iha : {}) (ihb : {}) (rho : ListType Nat) (d : Nat) => \
                 universe_bridge_congr2 KExpr KExpr KExpr KExpr.{constructor} \
                 {} {} {} {} (iha rho d) (ihb rho {body_depth}))",
                ih("a"),
                ih("b"),
                lhs("a", "d"),
                rhs("a", "d"),
                lhs("b", body_depth),
                rhs("b", body_depth),
            )
        };
        let value = format!(
            r"fun (ps : ListType Name) (us : ListType Level)
    (arity : @Eq Nat (name_list_len ps) (level_list_len us)) (e : ImplExpr)
    (rho : ListType Nat) (d : Nat) =>
  @ImplExpr.rec (fun (e0 : ImplExpr) => {motive})
    (fun (i : Nat) (_rho : ListType Nat) (_d : Nat) => @Eq.refl KExpr (KExpr.bvar i))
    (fun (y : Nat) (rho : ListType Nat) (d : Nat) =>
      @Eq.refl KExpr (KExpr.bvar (Nat.add (rho_index rho y) d)))
    (fun (l : Level) (_rho : ListType Nat) (_d : Nat) =>
      Eq.cong Level KExpr KExpr.sort (level_subst ps us l) (substL (paramSubstN ps us) l)
        (level_subst_eq_substL ps us arity l))
    (fun (nm : Name) (vs : ListType Level) (_rho : ListType Nat) (_d : Nat) =>
      Eq.cong (ListType Level) KExpr (KExpr.const nm)
        (impl_inst_levels_list ps us vs) (mapLL (substL (paramSubstN ps us)) vs)
        (impl_inst_levels_list_eq_mapLL ps us arity vs))
    {app}
    {lam}
    {pi}
    (fun (_nm : Name) (ty : ImplExpr) (v : ImplExpr) (b : ImplExpr)
      (ihty : {ihty}) (ihv : {ihv}) (ihb : {ihb})
      (rho : ListType Nat) (d : Nat) =>
      psubst_closed_cong3 KExpr.let_ {ty_lhs} {ty_rhs} {v_lhs} {v_rhs} {b_lhs} {b_rhs}
        (ihty rho d) (ihv rho d) (ihb rho (Nat.succ d)))
    (fun (lt : ImplLit) (_rho : ListType Nat) (_d : Nat) =>
      instL_preserves_impl_literal (paramSubstN ps us) lt)
    (fun (inner : ImplExpr) (ihinner : {ihinner}) (rho : ListType Nat) (d : Nat) =>
      ihinner rho d) e rho d",
            motive = ih("e0"),
            app = binary_minor("app", false),
            lam = binary_minor("lam", true),
            pi = binary_minor("pi", true),
            ihty = ih("ty"),
            ihv = ih("v"),
            ihb = ih("b"),
            ihinner = ih("inner"),
            ty_lhs = lhs("ty", "d"),
            ty_rhs = rhs("ty", "d"),
            v_lhs = lhs("v", "d"),
            v_rhs = rhs("v", "d"),
            b_lhs = lhs("b", "(Nat.succ d)"),
            b_rhs = rhs("b", "(Nat.succ d)"),
        );
        instantiation_theorem(
            self,
            "to_kexpr_at_impl_inst_levels",
            r"forall (ps : ListType Name) (us : ListType Level)
    (arity : @Eq Nat (name_list_len ps) (level_list_len us)) (e : ImplExpr)
    (rho : ListType Nat) (d : Nat),
    @Eq KExpr (to_kexpr_at (impl_inst_levels ps us e) rho d)
      (instLevels ps (to_kexpr_at e rho d) us)",
            &value,
            "Translation commutes with raw model universe instantiation, at every renaming and binder depth, under checked arity. All ten current ImplExpr constructors are covered. This does not connect the actual Rust substitution implementation.",
        )?;

        instantiation_theorem(
            self,
            "to_kexpr_impl_inst_levels",
            r"forall (ps : ListType Name) (us : ListType Level)
    (arity : @Eq Nat (name_list_len ps) (level_list_len us)) (e : ImplExpr)
    (rho : ListType Nat),
    @Eq KExpr (to_kexpr (impl_inst_levels ps us e) rho)
      (instLevels ps (to_kexpr e rho) us)",
            r"fun (ps : ListType Name) (us : ListType Level)
    (arity : @Eq Nat (name_list_len ps) (level_list_len us)) (e : ImplExpr)
    (rho : ListType Nat) =>
  to_kexpr_at_impl_inst_levels ps us arity e rho Nat.zero",
            "Depth-zero raw instantiation/translation equation for the constant-inference bridge; universe arity is a required premise.",
        )?;

        instantiation_theorem(
            self,
            "to_kexpr_instantiated_binder_witness",
            r"@Eq KExpr
    (to_kexpr
      (impl_inst_levels (@ListType.cons Name Name.anonymous (@ListType.nil Name))
        (@ListType.cons Level (Level.succ Level.zero) (@ListType.nil Level))
        (ImplExpr.lam (BinderData.mk BinderInfo.default Multiplicity.many)
          (ImplExpr.sort (Level.param Name.anonymous))
          (ImplExpr.mdata (ImplExpr.bvar Nat.zero)))) (@ListType.nil Nat))
    (KExpr.lam (KExpr.sort (Level.succ Level.zero)) (KExpr.bvar Nat.zero))",
            r"to_kexpr_impl_inst_levels
    (@ListType.cons Name Name.anonymous (@ListType.nil Name))
    (@ListType.cons Level (Level.succ Level.zero) (@ListType.nil Level))
    (@Eq.refl Nat (Nat.succ Nat.zero))
    (ImplExpr.lam (BinderData.mk BinderInfo.default Multiplicity.many)
      (ImplExpr.sort (Level.param Name.anonymous))
      (ImplExpr.mdata (ImplExpr.bvar Nat.zero))) (@ListType.nil Nat)",
            "Nonempty universe-argument witness using the assembled commuting theorem: the lambda domain is instantiated, its bound variable survives, and metadata is erased.",
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::instantiation_theorem;
    use crate::spec::types::ProofStatus;
    use crate::test_utils::{build_spec_with_stack, run_with_stack};

    #[test]
    fn registered_universe_instantiation_bridge_has_real_proofs_and_nontrivial_witness() {
        run_with_stack(|| {
            let spec = build_spec_with_stack();
            for name in [
                "universe_bridge_congr2",
                "level_subst_eq_substL",
                "impl_inst_levels_list_eq_mapLL",
                "instL_preserves_impl_literal",
                "to_kexpr_at_impl_inst_levels",
                "to_kexpr_impl_inst_levels",
                "to_kexpr_instantiated_binder_witness",
            ] {
                let def = spec.definitions().get(name).expect("registered proof");
                assert!(!def.is_axiom, "{name} must have a value");
                assert_eq!(def.proof_status, ProofStatus::DerivedProved);
                assert!(def.elaborated_value.is_some(), "{name} must be checked");
                assert!(
                    crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty(),
                    "{name} must have no transitive axiom dependency"
                );
            }
        });
    }

    #[test]
    fn universe_instantiation_does_not_accept_false_arity_or_unchanged_universe() {
        run_with_stack(|| {
            let mut spec = build_spec_with_stack();
            assert!(
                instantiation_theorem(
                    &mut spec,
                    "univ_inst_false_arity_must_fail",
                    "@Eq Nat (name_list_len (@ListType.cons Name Name.anonymous (@ListType.nil Name))) (level_list_len (@ListType.nil Level))",
                    "@Eq.refl Nat Nat.zero",
                    "Negative control: a missing universe argument does not satisfy the bridge's arity premise.",
                )
                .is_err(),
                "checked arity cannot be supplied for an unequal pair of lists"
            );
            assert!(
                instantiation_theorem(
                    &mut spec,
                    "univ_inst_unchanged_sort_must_fail",
                    "@Eq KExpr (instLevels (@ListType.cons Name Name.anonymous (@ListType.nil Name)) (KExpr.sort (Level.param Name.anonymous)) (@ListType.cons Level (Level.succ Level.zero) (@ListType.nil Level))) (KExpr.sort (Level.param Name.anonymous))",
                    "@Eq.refl KExpr (KExpr.sort (Level.param Name.anonymous))",
                    "Negative control: the nonempty polymorphic type is not universe-independent.",
                )
                .is_err(),
                "instantiation really changes the schematic universe"
            );
        });
    }
}

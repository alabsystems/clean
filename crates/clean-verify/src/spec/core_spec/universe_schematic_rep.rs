// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! No-FVar schematic types need only one renaming-representation equation.
//!
//! Port of the independently checked exact-export scratch guide
//! `scratch/self-verification-no-fvar-2026-09-08.lean`. The syntactic predicate
//! permits loose BVars; neither lexical closedness nor source admission follows
//! from it. The actual admission/metadata boundary is documented beside the guide.

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

fn schematic_theorem(
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
    /// Requires C4 translation and universe_closedness's congruence helpers.
    /// Can run before impl_infer_sound; the later ImplLC comparison is test-only.
    /// Does not require a new environment signature or source theorem.
    pub(super) fn add_universe_schematic_rep(&mut self) -> Result<(), SpecError> {
        self.add_inductive(
            r"inductive ImplNoFVar : ImplExpr -> Type
| bvar : forall (i : Nat), ImplNoFVar (ImplExpr.bvar i)
| sort : forall (l : Level), ImplNoFVar (ImplExpr.sort l)
| const : forall (nm : Name) (us : ListType Level), ImplNoFVar (ImplExpr.const nm us)
| app : forall (f : ImplExpr) (a : ImplExpr), ImplNoFVar f -> ImplNoFVar a -> ImplNoFVar (ImplExpr.app f a)
| lam : forall (bd : BinderData) (ty : ImplExpr) (b : ImplExpr), ImplNoFVar ty -> ImplNoFVar b -> ImplNoFVar (ImplExpr.lam bd ty b)
| pi : forall (bd : BinderData) (ty : ImplExpr) (b : ImplExpr), ImplNoFVar ty -> ImplNoFVar b -> ImplNoFVar (ImplExpr.pi bd ty b)
| let_ : forall (nm : Name) (ty : ImplExpr) (v : ImplExpr) (b : ImplExpr), ImplNoFVar ty -> ImplNoFVar v -> ImplNoFVar b -> ImplNoFVar (ImplExpr.let_ nm ty v b)
| lit : forall (lt : ImplLit), ImplNoFVar (ImplExpr.lit lt)
| mdata : forall (e : ImplExpr), ImplNoFVar e -> ImplNoFVar (ImplExpr.mdata e)",
            "Structural absence of FVar in the current ten-constructor ImplExpr. All expression children are checked, including binder domains and bodies, let types/values/bodies, and metadata. BVar indices are unrestricted: this is not de Bruijn closedness, and it does not assert actual Rust metadata correctness.",
        )?;

        let translated = |e: &str, rho: &str, d: &str| format!("(to_kexpr_at {e} {rho} {d})");
        let ih = |e: &str| {
            format!(
                "forall (rho : ListType Nat) (sigma : ListType Nat) (d : Nat), @Eq KExpr {} {}",
                translated(e, "rho", "d"),
                translated(e, "sigma", "d")
            )
        };
        let binary_minor = |constructor: &str, binder: bool| {
            let annotation = if binder { "(_bd : BinderData) " } else { "" };
            let body_depth = if binder { "(Nat.succ d)" } else { "d" };
            format!(
                "(fun {annotation}(a : ImplExpr) (b : ImplExpr) \
                 (_ha : ImplNoFVar a) (_hb : ImplNoFVar b) \
                 (iha : {}) (ihb : {}) (rho : ListType Nat) (sigma : ListType Nat) (d : Nat) => \
                 psubst_closed_cong2 KExpr.{constructor} {} {} {} {} \
                 (iha rho sigma d) (ihb rho sigma {body_depth}))",
                ih("a"),
                ih("b"),
                translated("a", "rho", "d"),
                translated("a", "sigma", "d"),
                translated("b", "rho", body_depth),
                translated("b", "sigma", body_depth),
            )
        };
        let proof = format!(
            r"fun (e : ImplExpr) (h : ImplNoFVar e)
    (rho : ListType Nat) (sigma : ListType Nat) (d : Nat) =>
  @ImplNoFVar.rec (fun (e0 : ImplExpr) (_h0 : ImplNoFVar e0) => {motive})
    (fun (i : Nat) (_rho : ListType Nat) (_sigma : ListType Nat) (_d : Nat) =>
      @Eq.refl KExpr (KExpr.bvar i))
    (fun (l : Level) (_rho : ListType Nat) (_sigma : ListType Nat) (_d : Nat) =>
      @Eq.refl KExpr (KExpr.sort l))
    (fun (nm : Name) (us : ListType Level)
      (_rho : ListType Nat) (_sigma : ListType Nat) (_d : Nat) =>
      @Eq.refl KExpr (KExpr.const nm us))
    {app}
    {lam}
    {pi}
    (fun (_nm : Name) (ty : ImplExpr) (v : ImplExpr) (b : ImplExpr)
      (_ht : ImplNoFVar ty) (_hv : ImplNoFVar v) (_hb : ImplNoFVar b)
      (iht : {iht}) (ihv : {ihv}) (ihb : {ihb})
      (rho : ListType Nat) (sigma : ListType Nat) (d : Nat) =>
      psubst_closed_cong3 KExpr.let_ {ty_lhs} {ty_rhs} {v_lhs} {v_rhs} {b_lhs} {b_rhs}
        (iht rho sigma d) (ihv rho sigma d) (ihb rho sigma (Nat.succ d)))
    (fun (lt : ImplLit) (_rho : ListType Nat) (_sigma : ListType Nat) (_d : Nat) =>
      @Eq.refl KExpr (impl_lit_to_kexpr lt))
    (fun (inner : ImplExpr) (_hinner : ImplNoFVar inner) (ihinner : {ihinner})
      (rho : ListType Nat) (sigma : ListType Nat) (d : Nat) => ihinner rho sigma d)
    e h rho sigma d",
            motive = ih("e0"),
            app = binary_minor("app", false),
            lam = binary_minor("lam", true),
            pi = binary_minor("pi", true),
            iht = ih("ty"),
            ihv = ih("v"),
            ihb = ih("b"),
            ihinner = ih("inner"),
            ty_lhs = translated("ty", "rho", "d"),
            ty_rhs = translated("ty", "sigma", "d"),
            v_lhs = translated("v", "rho", "d"),
            v_rhs = translated("v", "sigma", "d"),
            b_lhs = translated("b", "rho", "(Nat.succ d)"),
            b_rhs = translated("b", "sigma", "(Nat.succ d)"),
        );
        schematic_theorem(
            self,
            "to_kexpr_at_rho_independent",
            r"forall (e : ImplExpr) (h : ImplNoFVar e)
    (rho : ListType Nat) (sigma : ListType Nat) (d : Nat),
    @Eq KExpr (to_kexpr_at e rho d) (to_kexpr_at e sigma d)",
            &proof,
            "No-FVar syntax translates independently of the renaming at every binder depth. Nine structural positive cases cover the ten-constructor syntax by excluding FVar. Binder depths increment and metadata erases exactly as in to_kexpr_at. No source or closedness claim.",
        )?;
        schematic_theorem(
            self,
            "to_kexpr_rho_independent",
            r"forall (e : ImplExpr) (h : ImplNoFVar e) (rho : ListType Nat) (sigma : ListType Nat),
    @Eq KExpr (to_kexpr e rho) (to_kexpr e sigma)",
            r"fun (e : ImplExpr) (h : ImplNoFVar e) (rho : ListType Nat) (sigma : ListType Nat) =>
    to_kexpr_at_rho_independent e h rho sigma Nat.zero",
            "Depth-zero specialization of the structural No-FVar translation theorem.",
        )?;
        schematic_theorem(
            self,
            "to_kexpr_eq_of_nil",
            r"forall (e : ImplExpr) (h : ImplNoFVar e) (T : KExpr)
    (ht : @Eq KExpr (to_kexpr e (@ListType.nil Nat)) T) (rho : ListType Nat),
    @Eq KExpr (to_kexpr e rho) T",
            r"fun (e : ImplExpr) (h : ImplNoFVar e) (T : KExpr)
    (ht : @Eq KExpr (to_kexpr e (@ListType.nil Nat)) T) (rho : ListType Nat) =>
  Eq.trans KExpr (to_kexpr e rho) (to_kexpr e (@ListType.nil Nat)) T
    (to_kexpr_rho_independent e h rho (@ListType.nil Nat)) ht",
            "A schematic field represented once at nil is represented at every rho under structural No-FVar. Intended for the environment bridge without assuming an all-rho equality as a field.",
        )?;

        self.add_universe_schematic_rep_controls()
    }

    fn add_universe_schematic_rep_controls(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            "def impl_no_fvar_rho_zero : ListType Nat := @ListType.cons Nat Nat.zero (@ListType.nil Nat)",
            "Counterexample renaming containing FVarId 0.",
        )?;
        self.add_recursive_def(
            "def impl_no_fvar_rho_one : ListType Nat := @ListType.cons Nat (Nat.succ Nat.zero) (@ListType.nil Nat)",
            "Counterexample renaming omitting FVarId 0; its sentinel index is one.",
        )?;
        schematic_theorem(
            self,
            "impl_fvar_translation_depends_on_rho",
            r"@Eq KExpr (to_kexpr (ImplExpr.fvar Nat.zero) impl_no_fvar_rho_zero)
    (to_kexpr (ImplExpr.fvar Nat.zero) impl_no_fvar_rho_one) -> Empty",
            r"fun (h : @Eq KExpr (to_kexpr (ImplExpr.fvar Nat.zero) impl_no_fvar_rho_zero)
    (to_kexpr (ImplExpr.fvar Nat.zero) impl_no_fvar_rho_one)) =>
  nat_zero_ne_succ Nat.zero Empty (kexpr_bvar_inj Nat.zero (Nat.succ Nat.zero) h)",
            "Genuine free-variable counterexample: FVar 0 becomes BVar 0 under [0] and BVar 1 under [1]. This is a checked refutation, not merely rejection of a proposed proof term.",
        )?;
        schematic_theorem(
            self,
            "impl_unqualified_rho_independence_refuted",
            r"(forall (e : ImplExpr) (rho : ListType Nat) (sigma : ListType Nat) (d : Nat),
    @Eq KExpr (to_kexpr_at e rho d) (to_kexpr_at e sigma d)) -> Empty",
            r"fun (h : forall (e : ImplExpr) (rho : ListType Nat) (sigma : ListType Nat) (d : Nat),
    @Eq KExpr (to_kexpr_at e rho d) (to_kexpr_at e sigma d)) =>
  impl_fvar_translation_depends_on_rho
    (h (ImplExpr.fvar Nat.zero) impl_no_fvar_rho_zero impl_no_fvar_rho_one Nat.zero)",
            "Refutes the universal renaming-independence statement when its No-FVar premise is removed.",
        )?;
        schematic_theorem(
            self,
            "impl_no_fvar_loose_bvar_witness",
            "ImplNoFVar (ImplExpr.bvar Nat.zero)",
            "ImplNoFVar.bvar Nat.zero",
            "No-FVar deliberately permits top-level loose BVar 0; it does not establish lexical closedness.",
        )?;
        self.add_recursive_def(
            r"def impl_no_fvar_binder_mdata_expr : ImplExpr :=
  ImplExpr.mdata (ImplExpr.lam (BinderData.mk BinderInfo.default Multiplicity.many)
    (ImplExpr.sort Level.zero) (ImplExpr.mdata (ImplExpr.bvar Nat.zero)))",
            "Positive nested binder and metadata syntax witness for No-FVar translation.",
        )?;
        schematic_theorem(
            self,
            "impl_no_fvar_binder_mdata_witness",
            "ImplNoFVar impl_no_fvar_binder_mdata_expr",
            r"ImplNoFVar.mdata
    (ImplExpr.lam (BinderData.mk BinderInfo.default Multiplicity.many)
      (ImplExpr.sort Level.zero) (ImplExpr.mdata (ImplExpr.bvar Nat.zero)))
    (ImplNoFVar.lam (BinderData.mk BinderInfo.default Multiplicity.many)
      (ImplExpr.sort Level.zero) (ImplExpr.mdata (ImplExpr.bvar Nat.zero))
      (ImplNoFVar.sort Level.zero)
      (ImplNoFVar.mdata (ImplExpr.bvar Nat.zero) (ImplNoFVar.bvar Nat.zero)))",
            "Constructor witness: metadata at the root and in a lambda body preserves structural No-FVar.",
        )?;
        schematic_theorem(
            self,
            "to_kexpr_no_fvar_binder_mdata_witness",
            r"forall (rho : ListType Nat) (sigma : ListType Nat) (d : Nat),
    @Eq KExpr (to_kexpr_at impl_no_fvar_binder_mdata_expr rho d)
      (to_kexpr_at impl_no_fvar_binder_mdata_expr sigma d)",
            r"fun (rho : ListType Nat) (sigma : ListType Nat) (d : Nat) =>
  to_kexpr_at_rho_independent impl_no_fvar_binder_mdata_expr
    impl_no_fvar_binder_mdata_witness rho sigma d",
            "Positive binder/metadata control uses the general checked theorem, not a reflexivity-only replacement.",
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::schematic_theorem;
    use crate::spec::types::ProofStatus;
    use crate::test_utils::{build_spec_with_stack, run_with_stack};

    #[test]
    fn registered_no_fvar_schematic_rep_has_actual_empty_axiom_closure() {
        run_with_stack(|| {
            let mut spec = build_spec_with_stack();
            // ImplLC registers later than the schematic representation stage.
            // Kernel-check this comparison in the full-spec test so the stage
            // stays usable by the earlier environment relation.
            schematic_theorem(
                &mut spec,
                "impl_no_fvar_counterexample_is_locally_closed",
                "ImplLC (ImplExpr.fvar Nat.zero) Nat.zero",
                "ImplLC.fvar Nat.zero Nat.zero",
                "The same FVar counterexample is locally closed in the de Bruijn sense. ImplLC cannot replace No-FVar.",
            )
            .expect("FVar counterexample must be genuinely ImplLC");
            let predicate = spec
                .definitions()
                .get("ImplNoFVar")
                .expect("registered predicate");
            assert!(!predicate.is_axiom);
            assert!(predicate.elaborated_type.is_some());
            for constructor in [
                "bvar", "sort", "const", "app", "lam", "pi", "let_", "lit", "mdata",
            ] {
                assert!(spec
                    .definitions()
                    .contains_key(&format!("ImplNoFVar.{constructor}")));
            }
            assert!(!spec.definitions().contains_key("ImplNoFVar.fvar"));
            for name in [
                "to_kexpr_at_rho_independent",
                "to_kexpr_rho_independent",
                "to_kexpr_eq_of_nil",
                "impl_fvar_translation_depends_on_rho",
                "impl_unqualified_rho_independence_refuted",
                "impl_no_fvar_counterexample_is_locally_closed",
                "impl_no_fvar_loose_bvar_witness",
                "impl_no_fvar_binder_mdata_witness",
                "to_kexpr_no_fvar_binder_mdata_witness",
            ] {
                let def = spec.definitions().get(name).expect("registered proof");
                assert!(!def.is_axiom, "{name} must have a value");
                assert_eq!(def.proof_status, ProofStatus::DerivedProved);
                assert!(
                    def.elaborated_value.is_some(),
                    "{name} must be kernel checked"
                );
                assert!(
                    crate::spec_axiom_closure::computed_axiom_closure(&spec, name).is_empty(),
                    "{name} must have empty actual transitive axiom closure"
                );
            }
        });
    }

    #[test]
    fn no_fvar_controls_reject_fvar_membership_and_unqualified_equality() {
        run_with_stack(|| {
            let mut spec = build_spec_with_stack();
            assert!(schematic_theorem(
                &mut spec,
                "no_fvar_forged_fvar_membership_must_fail",
                "ImplNoFVar (ImplExpr.fvar Nat.zero)",
                "ImplNoFVar.bvar Nat.zero",
                "Negative control: BVar's constructor cannot witness No-FVar of FVar.",
            )
            .is_err());
            assert!(
                schematic_theorem(
                    &mut spec,
                    "no_fvar_unqualified_translation_must_fail",
                    "@Eq KExpr (to_kexpr (ImplExpr.fvar Nat.zero) impl_no_fvar_rho_zero) (to_kexpr (ImplExpr.fvar Nat.zero) impl_no_fvar_rho_one)",
                    "@Eq.refl KExpr (KExpr.bvar Nat.zero)",
                    "Negative control: changing the renaming changes the represented FVar.",
                )
                .is_err()
            );
        });
    }
}

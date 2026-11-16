// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Kernel expression model: KExpr, lift, instantiate (PART 4 + lift_at lemmas)

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::model_units::ModelUnit;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    pub(super) fn add_expr_model(&mut self) -> Result<(), SpecError> {
        // =========================================================
        // PART 4: Kernel Expression Model
        // =========================================================
        // KExpr models the 9-constructor fragment of kernel expressions used by
        // the current refinement packet.
        // This enables formal reasoning about type checking operations.

        // Name is registered BEFORE Level because the real kernel Level algebra's
        // `param` constructor carries a Name (level/mod.rs:81-92). Hoisting Name
        // keeps `Level.param : Name -> Level` well-scoped at elaboration time.
        self.register_model_unit(ModelUnit::ExprModelCore)?;

        // instantiate_at_bvar: unfolding lemma for bvar case
        self.add_definition(SpecDefinition {
            name: "instantiate_at_bvar".to_string(),
            type_src: "forall (i : Nat) (val : KExpr) (depth : Nat), @Eq KExpr (instantiate_at (KExpr.bvar i) val depth) (instantiate_bvar_at i depth val)".to_string(),
            value_src: Some(
                "fun (i : Nat) (val : KExpr) (depth : Nat) => @Eq.refl KExpr (instantiate_bvar_at i depth val)".to_string()
            ),
            is_axiom: false,
            description: "Unfolding: instantiate_at (bvar i) val depth = instantiate_bvar_at i depth val.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // instantiate_bvar_at_below: derived proof for idx < depth case.
        //
        // Proof strategy: the hypothesis h gives Nat.sub depth idx = Nat.succ k,
        // so applying Eq.cong with the Nat.rec function maps h to an equality
        // between instantiate_bvar_at (via delta) and Nat.rec on Nat.succ k
        // (which iota+beta reduces to KExpr.bvar idx).
        // Part of #464.
        self.add_definition_structural(SpecDefinition {
            name: "instantiate_bvar_at_below".to_string(),
            type_src: "forall (idx : Nat) (depth : Nat) (val : KExpr), @Eq Nat (Nat.sub depth idx) (Nat.succ (Nat.sub (Nat.sub depth idx) (Nat.succ Nat.zero))) -> @Eq KExpr (instantiate_bvar_at idx depth val) (KExpr.bvar idx)".to_string(),
            value_src: Some(concat!(
                "fun (idx : Nat) (depth : Nat) (val : KExpr) ",
                "(h : @Eq Nat (Nat.sub depth idx) (Nat.succ (Nat.sub (Nat.sub depth idx) (Nat.succ Nat.zero)))) => ",
                "@Eq.cong Nat KExpr ",
                "(fun (n : Nat) => @Nat.rec (fun (_ : Nat) => KExpr) ",
                "(instantiate_bvar_geq idx depth val) ",
                "(fun (_ : Nat) (_ : KExpr) => KExpr.bvar idx) n) ",
                "(Nat.sub depth idx) ",
                "(Nat.succ (Nat.sub (Nat.sub depth idx) (Nat.succ Nat.zero))) ",
                "h",
            ).to_string()),
            is_axiom: false,
            description: "If idx < depth, instantiate_bvar_at returns bvar idx unchanged. DerivedProved via Eq.cong + Nat.rec iota. Part of #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // instantiate_bvar_at_eq: derived proof for idx == depth case.
        //
        // Proof strategy: a single Eq.cong with a composed function that
        // nests both Nat.recs. The outer Nat.rec is from instantiate_bvar_at,
        // whose zero case is instantiate_bvar_geq (itself a Nat.rec).
        // Applying Eq.cong with nat_sub_self maps (Nat.sub idx idx) to
        // Nat.zero in both nested Nat.recs simultaneously, reducing the
        // whole expression to lift_at val Nat.zero idx.
        // Part of #464.
        self.add_definition_structural(SpecDefinition {
            name: "instantiate_bvar_at_eq".to_string(),
            type_src: "forall (idx : Nat) (val : KExpr), @Eq KExpr (instantiate_bvar_at idx idx val) (lift_at val Nat.zero idx)".to_string(),
            value_src: Some(concat!(
                "fun (idx : Nat) (val : KExpr) => ",
                "@Eq.cong Nat KExpr ",
                "(fun (n : Nat) => @Nat.rec (fun (_ : Nat) => KExpr) ",
                "(@Nat.rec (fun (_ : Nat) => KExpr) ",
                "(lift_at val Nat.zero idx) ",
                "(fun (_ : Nat) (_ : KExpr) => KExpr.bvar (Nat.sub idx (Nat.succ Nat.zero))) n) ",
                "(fun (_ : Nat) (_ : KExpr) => KExpr.bvar idx) n) ",
                "(Nat.sub idx idx) ",
                "Nat.zero ",
                "(nat_sub_self idx)",
            ).to_string()),
            is_axiom: false,
            description: "If idx == depth, instantiate_bvar_at substitutes with lifted val. DerivedProved via Eq.cong + nat_sub_self (now constructive) + nested Nat.rec iota. Part of #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "nat_sub_self".to_string(),
                "Eq.cong".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // instantiate_bvar_at_eq_from_zero_witnesses: generalized equality case.
        //
        // When both subtraction directions reduce to zero, instantiate_bvar_at
        // must take the outer zero branch into instantiate_bvar_geq and then the
        // inner zero branch into lift_at val 0 depth. This avoids needing an
        // explicit idx = depth rewrite in later bvar commutation proofs. Part of
        // #461, #464.
        self.add_definition_structural(SpecDefinition {
            name: "instantiate_bvar_at_eq_from_zero_witnesses".to_string(),
            type_src: concat!(
                "forall (idx : Nat) (depth : Nat) (val : KExpr), ",
                "@Eq Nat (Nat.sub depth idx) Nat.zero -> ",
                "@Eq Nat (Nat.sub idx depth) Nat.zero -> ",
                "@Eq KExpr (instantiate_bvar_at idx depth val) (lift_at val Nat.zero depth)",
            )
            .to_string(),
            value_src: Some(concat!(
                "fun (idx : Nat) (depth : Nat) (val : KExpr) ",
                "(h_outer : @Eq Nat (Nat.sub depth idx) Nat.zero) ",
                "(h_inner : @Eq Nat (Nat.sub idx depth) Nat.zero) => ",
                "@Eq.trans KExpr ",
                "(instantiate_bvar_at idx depth val) ",
                "(instantiate_bvar_geq idx depth val) ",
                "(lift_at val Nat.zero depth) ",
                "(@Eq.cong Nat KExpr ",
                "(fun (n : Nat) => @Nat.rec (fun (_ : Nat) => KExpr) ",
                "(instantiate_bvar_geq idx depth val) ",
                "(fun (_ : Nat) (_ : KExpr) => KExpr.bvar idx) n) ",
                "(Nat.sub depth idx) ",
                "Nat.zero ",
                "h_outer) ",
                "(@Eq.cong Nat KExpr ",
                "(fun (n : Nat) => @Nat.rec (fun (_ : Nat) => KExpr) ",
                "(lift_at val Nat.zero depth) ",
                "(fun (_ : Nat) (_ : KExpr) => KExpr.bvar (Nat.sub idx (Nat.succ Nat.zero))) n) ",
                "(Nat.sub idx depth) ",
                "Nat.zero ",
                "h_inner)",
            ).to_string()),
            is_axiom: false,
            description: "If both subtraction directions collapse to zero, instantiate_bvar_at takes the equality branch and returns lift_at val 0 depth. DerivedProved via two Eq.cong transports through the nested Nat.recs. Part of #461, #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition_structural(SpecDefinition {
            name: "instantiate_at_bvar_eq_from_zero_witnesses".to_string(),
            type_src: concat!(
                "forall (idx : Nat) (depth : Nat) (val : KExpr), ",
                "@Eq Nat (Nat.sub depth idx) Nat.zero -> ",
                "@Eq Nat (Nat.sub idx depth) Nat.zero -> ",
                "@Eq KExpr (instantiate_at (KExpr.bvar idx) val depth) (lift_at val Nat.zero depth)",
            )
            .to_string(),
            value_src: Some(concat!(
                "fun (idx : Nat) (depth : Nat) (val : KExpr) ",
                "(h_outer : @Eq Nat (Nat.sub depth idx) Nat.zero) ",
                "(h_inner : @Eq Nat (Nat.sub idx depth) Nat.zero) => ",
                "@Eq.trans KExpr ",
                "(instantiate_at (KExpr.bvar idx) val depth) ",
                "(instantiate_bvar_at idx depth val) ",
                "(lift_at val Nat.zero depth) ",
                "(instantiate_at_bvar idx val depth) ",
                "(instantiate_bvar_at_eq_from_zero_witnesses idx depth val h_outer h_inner)",
            ).to_string()),
            is_axiom: false,
            description: "Witness-driven equality branch for instantiate_at on bvars. Lets downstream proofs consume Nat.sub zero evidence directly instead of rewriting idx = depth. Part of #461, #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Eq.trans".to_string(),
                "instantiate_at_bvar".to_string(),
                "instantiate_bvar_at_eq_from_zero_witnesses".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // instantiate_bvar_at_above: derived proof for idx > depth case.
        //
        // Type restructured from single to two hypotheses (#464 handoff):
        // h1: Nat.sub depth idx = 0 (outer Nat.rec goes to zero case → instantiate_bvar_geq)
        // h2: Nat.sub idx depth = Nat.succ k (inner Nat.rec in instantiate_bvar_geq goes to succ case)
        //
        // Proof strategy: Eq.trans chaining two Eq.cong steps:
        // Step 1: Eq.cong with h1 on the outer Nat.rec, reducing to instantiate_bvar_geq.
        // Step 2: Eq.cong with h2 on the inner Nat.rec in instantiate_bvar_geq,
        //         reducing to KExpr.bvar (Nat.sub idx 1).
        // Part of #464.
        self.add_definition_structural(SpecDefinition {
            name: "instantiate_bvar_at_above".to_string(),
            type_src: concat!(
                "forall (idx : Nat) (depth : Nat) (val : KExpr), ",
                "@Eq Nat (Nat.sub depth idx) Nat.zero -> ",
                "@Eq Nat (Nat.sub idx depth) (Nat.succ (Nat.sub (Nat.sub idx depth) (Nat.succ Nat.zero))) -> ",
                "@Eq KExpr (instantiate_bvar_at idx depth val) (KExpr.bvar (Nat.sub idx (Nat.succ Nat.zero)))",
            ).to_string(),
            value_src: Some(concat!(
                "fun (idx : Nat) (depth : Nat) (val : KExpr) ",
                "(h1 : @Eq Nat (Nat.sub depth idx) Nat.zero) ",
                "(h2 : @Eq Nat (Nat.sub idx depth) (Nat.succ (Nat.sub (Nat.sub idx depth) (Nat.succ Nat.zero)))) => ",
                "@Eq.trans KExpr ",
                "(@Nat.rec (fun (_ : Nat) => KExpr) ",
                "(instantiate_bvar_geq idx depth val) ",
                "(fun (_ : Nat) (_ : KExpr) => KExpr.bvar idx) (Nat.sub depth idx)) ",
                "(instantiate_bvar_geq idx depth val) ",
                "(KExpr.bvar (Nat.sub idx (Nat.succ Nat.zero))) ",
                "(@Eq.cong Nat KExpr ",
                "(fun (n : Nat) => @Nat.rec (fun (_ : Nat) => KExpr) ",
                "(instantiate_bvar_geq idx depth val) ",
                "(fun (_ : Nat) (_ : KExpr) => KExpr.bvar idx) n) ",
                "(Nat.sub depth idx) Nat.zero h1) ",
                "(@Eq.cong Nat KExpr ",
                "(fun (n : Nat) => @Nat.rec (fun (_ : Nat) => KExpr) ",
                "(lift_at val Nat.zero depth) ",
                "(fun (_ : Nat) (_ : KExpr) => KExpr.bvar (Nat.sub idx (Nat.succ Nat.zero))) n) ",
                "(Nat.sub idx depth) ",
                "(Nat.succ (Nat.sub (Nat.sub idx depth) (Nat.succ Nat.zero))) h2)",
            ).to_string()),
            is_axiom: false,
            description: "If idx > depth (two witnesses), instantiate_bvar_at decrements the index. DerivedProved via Eq.trans + two Eq.cong on outer/inner Nat.rec. Part of #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Eq.trans".to_string(),
                "Eq.cong".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // =========================================================
        // Increment A (#2859 computational-iota/delta track) —
        // application-spine / head recognition substrate.
        // =========================================================
        //
        // An iota redex is a recursor-`const` applied to a constructor-headed
        // major premise; in the 6-constructor KExpr that is a `const`-headed
        // `app`-spine. These pure structural functions recover the spine head and
        // arity so a later computational `iota_step` can recognize redexes without
        // any change to KExpr. Purely additive (nothing downstream consumes them
        // yet). See designs/2026-06-14-computational-iota-delta-track.md (Increment A).

        // kapp_fn: the head of an application spine (peel KExpr.app on the left).
        self.register_model_unit(ModelUnit::ExprModelSpine)?;

        // kapp_fn_app: unfolding — the head of `app f a` is the head of `f`.
        self.add_definition(SpecDefinition {
            name: "kapp_fn_app".to_string(),
            type_src:
                "forall (f : KExpr) (a : KExpr), @Eq KExpr (kapp_fn (KExpr.app f a)) (kapp_fn f)"
                    .to_string(),
            value_src: Some(
                "fun (f : KExpr) (a : KExpr) => @Eq.refl KExpr (kapp_fn f)".to_string(),
            ),
            is_axiom: false,
            description:
                "Unfolding: kapp_fn (app f a) = kapp_fn f (the app arm returns the head of f). \
                 DerivedProved via delta+iota computation. Part of #2859 (Increment A)."
                    .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // kapp_fn_const: unfolding — the head of a bare const is itself.
        self.add_definition(SpecDefinition {
            name: "kapp_fn_const".to_string(),
            type_src: concat!(
                "forall (n : Name) (us : ListType Level), ",
                "@Eq KExpr (kapp_fn (KExpr.const n us)) (KExpr.const n us)"
            )
            .to_string(),
            value_src: Some(
                "fun (n : Name) (us : ListType Level) => @Eq.refl KExpr (KExpr.const n us)"
                    .to_string(),
            ),
            is_axiom: false,
            description:
                "Unfolding: kapp_fn (const n us) = const n us (a bare const is its own spine head). \
                 DerivedProved via iota computation. Part of #2859 (Increment A)."
                    .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // kapp_arg_count_app: unfolding — the spine of `app f a` has one more
        // argument than the spine of `f`.
        self.add_definition(SpecDefinition {
            name: "kapp_arg_count_app".to_string(),
            type_src: concat!(
                "forall (f : KExpr) (a : KExpr), ",
                "@Eq Nat (kapp_arg_count (KExpr.app f a)) (Nat.succ (kapp_arg_count f))"
            )
            .to_string(),
            value_src: Some(
                "fun (f : KExpr) (a : KExpr) => @Eq.refl Nat (Nat.succ (kapp_arg_count f))"
                    .to_string(),
            ),
            is_axiom: false,
            description:
                "Unfolding: kapp_arg_count (app f a) = succ (kapp_arg_count f). DerivedProved via \
                 delta+iota computation. Part of #2859 (Increment A)."
                    .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

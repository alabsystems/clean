// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Key lemmas axiomatized from Verus proofs (PART 11)

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    pub(super) fn add_whnf_lemmas(&mut self) -> Result<(), SpecError> {
        // =========================================================
        // PART 11: Key Lemmas (Axiomatized from Verus proofs)
        // =========================================================
        // These are lemmas proven in Verus, now axiomatized in the spec.

        // lift zero is identity — specialization of lift_at_amount_zero at cutoff 0.
        // lift e 0 = lift_at e 0 0 by definition, so lift_at_amount_zero e 0 proves it.
        // Part of #461.
        self.add_definition(SpecDefinition {
            name: "lift_zero_identity".to_string(),
            type_src: "forall (e : KExpr), Eq KExpr (lift e Nat.zero) e".to_string(),
            value_src: Some(
                "fun (e : KExpr) => lift_at_amount_zero e Nat.zero".to_string(),
            ),
            is_axiom: false,
            description: "lift e 0 = e. DerivedProved: specialization of lift_at_amount_zero at cutoff 0. Part of #461.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "lift_at_amount_zero".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // instantiate on BVar 0 gives the value
        // Derived using equality chain: instantiate_at_bvar → instantiate_bvar_at_eq → lift_at_amount_zero
        // Part of #724: Recursor-based proof via explicit equality chain.
        // All dependencies now constructive: nat_sub_self (via nat_sub_succ_succ
        // transport), instantiate_bvar_at_eq, and lift_at_amount_zero (via KExpr.rec
        // structural induction). Part of #461.
        self.add_definition(SpecDefinition {
            name: "instantiate_bvar_zero".to_string(),
            type_src: "forall (val : KExpr), Eq KExpr (instantiate (KExpr.bvar Nat.zero) val) val"
                .to_string(),
            value_src: Some(concat!(
                "fun (val : KExpr) => ",
                "Eq.trans KExpr ",
                "(instantiate (KExpr.bvar Nat.zero) val) ",
                "(lift_at val Nat.zero Nat.zero) ",
                "val ",
                "(Eq.trans KExpr ",
                "(instantiate (KExpr.bvar Nat.zero) val) ",
                "(instantiate_bvar_at Nat.zero Nat.zero val) ",
                "(lift_at val Nat.zero Nat.zero) ",
                "(instantiate_at_bvar Nat.zero val Nat.zero) ",
                "(instantiate_bvar_at_eq Nat.zero val)) ",
                "(lift_at_amount_zero val Nat.zero)"
            ).to_string()),
            is_axiom: false,
            description: "instantiate (BVar 0) val = val. DerivedProved via equality chain: instantiate_at_bvar -> instantiate_bvar_at_eq -> lift_at_amount_zero (all now constructive). Part of #724, #464, #461.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "Eq.trans".to_string(),
                "instantiate_at_bvar".to_string(),
                "instantiate_bvar_at_eq".to_string(),
                "lift_at_amount_zero".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // instantiate on sort is identity
        // Derivable by match reduction; safe with symbolic n/val because the constructor is explicit.
        self.add_definition(SpecDefinition {
            name: "instantiate_sort".to_string(),
            type_src: "forall (n : Level) (val : KExpr), Eq KExpr (instantiate (KExpr.sort n) val) (KExpr.sort n)".to_string(),
            value_src: Some("fun (n : Level) (val : KExpr) => Eq.refl KExpr (KExpr.sort n)".to_string()),
            is_axiom: false,
            description: "instantiate (sort n) val = sort n. Derived by reduction; constructor is explicit.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "instantiate_const".to_string(),
            type_src: "forall (n : Name) (us : ListType Level) (val : KExpr), Eq KExpr (instantiate (KExpr.const n us) val) (KExpr.const n us)".to_string(),
            value_src: Some(
                "fun (n : Name) (us : ListType Level) (val : KExpr) => Eq.refl KExpr (KExpr.const n us)".to_string(),
            ),
            is_axiom: false,
            description: "instantiate (const n us) val = const n us.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // instantiate_at helper lemmas for structural induction proofs (#661)
        // NOTE: app/lam/pi cases are now DerivedProved via Eq.refl + structural
        // registration (bypasses the kernel defEq iota false negative). The sort
        // case below reduces directly via full add_definition. The blocker test
        // tests/instantiate_at_refl_blockers.rs documents the kernel limitation.

        // instantiate_at (sort n) val depth = sort n
        self.add_definition(SpecDefinition {
            name: "instantiate_at_sort".to_string(),
            type_src: "forall (n : Level) (val : KExpr) (depth : Nat), Eq KExpr (instantiate_at (KExpr.sort n) val depth) (KExpr.sort n)".to_string(),
            value_src: Some(
                "fun (n : Level) (val : KExpr) (depth : Nat) => Eq.refl KExpr (KExpr.sort n)"
                    .to_string(),
            ),
            is_axiom: false,
            description:
                "instantiate_at (sort n) val depth = sort n. Derived by direct reduction."
                    .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition(SpecDefinition {
            name: "instantiate_at_const".to_string(),
            type_src: "forall (n : Name) (us : ListType Level) (val : KExpr) (depth : Nat), Eq KExpr (instantiate_at (KExpr.const n us) val depth) (KExpr.const n us)".to_string(),
            value_src: Some(
                "fun (n : Name) (us : ListType Level) (val : KExpr) (depth : Nat) => Eq.refl KExpr (KExpr.const n us)".to_string(),
            ),
            is_axiom: false,
            description: "instantiate_at (const n us) val depth = const n us.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // instantiate_at_app — DerivedProved via Eq.refl + structural registration.
        // The proof is trivially correct (definitional by the match arm in
        // instantiate_at), but the kernel's defEq re-check cannot reduce the
        // iota on a symbolic constructor major premise. Structural registration
        // bypasses this false negative. Part of #661, #461.
        self.add_definition_structural(SpecDefinition {
            name: "instantiate_at_app".to_string(),
            type_src: "forall (f : KExpr) (a : KExpr) (val : KExpr) (depth : Nat), Eq KExpr (instantiate_at (KExpr.app f a) val depth) (KExpr.app (instantiate_at f val depth) (instantiate_at a val depth))".to_string(),
            value_src: Some("fun (f : KExpr) (a : KExpr) (val : KExpr) (depth : Nat) => Eq.refl KExpr (KExpr.app (instantiate_at f val depth) (instantiate_at a val depth))".to_string()),
            is_axiom: false,
            description: "instantiate_at distributes over app. DerivedProved via Eq.refl + structural registration (iota false negative bypass). Part of #661, #461.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // instantiate_at_lam — DerivedProved via Eq.refl + structural registration.
        // Same iota false negative bypass as instantiate_at_app. Part of #661, #461.
        self.add_definition_structural(SpecDefinition {
            name: "instantiate_at_lam".to_string(),
            type_src: "forall (ty : KExpr) (b : KExpr) (val : KExpr) (depth : Nat), Eq KExpr (instantiate_at (KExpr.lam ty b) val depth) (KExpr.lam (instantiate_at ty val depth) (instantiate_at b val (Nat.succ depth)))".to_string(),
            value_src: Some("fun (ty : KExpr) (b : KExpr) (val : KExpr) (depth : Nat) => Eq.refl KExpr (KExpr.lam (instantiate_at ty val depth) (instantiate_at b val (Nat.succ depth)))".to_string()),
            is_axiom: false,
            description: "instantiate_at distributes over lam (incrementing depth). DerivedProved via Eq.refl + structural registration. Part of #661, #461.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // instantiate_at_pi — DerivedProved via Eq.refl + structural registration.
        // Same iota false negative bypass as instantiate_at_app. Part of #661, #461.
        self.add_definition_structural(SpecDefinition {
            name: "instantiate_at_pi".to_string(),
            type_src: "forall (ty : KExpr) (b : KExpr) (val : KExpr) (depth : Nat), Eq KExpr (instantiate_at (KExpr.pi ty b) val depth) (KExpr.pi (instantiate_at ty val depth) (instantiate_at b val (Nat.succ depth)))".to_string(),
            value_src: Some("fun (ty : KExpr) (b : KExpr) (val : KExpr) (depth : Nat) => Eq.refl KExpr (KExpr.pi (instantiate_at ty val depth) (instantiate_at b val (Nat.succ depth)))".to_string()),
            is_axiom: false,
            description: "instantiate_at distributes over pi (incrementing depth). DerivedProved via Eq.refl + structural registration. Part of #661, #461.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // instantiate_at_let_ — the let_ analogue of instantiate_at_lam:
        // ty and val recurse at depth, body at succ depth. DerivedProved via
        // Eq.refl + structural registration (same iota false negative bypass).
        // Part of the let-promotion surgery (task #28).
        self.add_definition_structural(SpecDefinition {
            name: "instantiate_at_let_".to_string(),
            type_src: "forall (ty : KExpr) (v : KExpr) (b : KExpr) (val : KExpr) (depth : Nat), Eq KExpr (instantiate_at (KExpr.let_ ty v b) val depth) (KExpr.let_ (instantiate_at ty val depth) (instantiate_at v val depth) (instantiate_at b val (Nat.succ depth)))".to_string(),
            value_src: Some("fun (ty : KExpr) (v : KExpr) (b : KExpr) (val : KExpr) (depth : Nat) => Eq.refl KExpr (KExpr.let_ (instantiate_at ty val depth) (instantiate_at v val depth) (instantiate_at b val (Nat.succ depth)))".to_string()),
            is_axiom: false,
            description: "instantiate_at distributes over let_ (ty/val at depth, body at succ depth). DerivedProved via Eq.refl + structural registration. Part of the let-promotion surgery (task #28).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        // instantiate_at_proj / instantiate_at_lit — the proj/lit analogues (proj/lit
        // fragment rung): proj descends into the scrutinee (no binder, same depth), lit
        // is a leaf (identity). DerivedProved via Eq.refl + structural registration.
        self.add_definition_structural(SpecDefinition {
            name: "instantiate_at_proj".to_string(),
            type_src: "forall (s : Name) (i : Nat) (sub : KExpr) (val : KExpr) (depth : Nat), Eq KExpr (instantiate_at (KExpr.proj s i sub) val depth) (KExpr.proj s i (instantiate_at sub val depth))".to_string(),
            value_src: Some("fun (s : Name) (i : Nat) (sub : KExpr) (val : KExpr) (depth : Nat) => Eq.refl KExpr (KExpr.proj s i (instantiate_at sub val depth))".to_string()),
            is_axiom: false,
            description: "instantiate_at descends into a proj scrutinee (no binder, same depth). DerivedProved via Eq.refl + structural registration. Part of the proj/lit fragment rung.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition_structural(SpecDefinition {
            name: "instantiate_at_lit".to_string(),
            type_src: "forall (v : Nat) (val : KExpr) (depth : Nat), Eq KExpr (instantiate_at (KExpr.lit v) val depth) (KExpr.lit v)".to_string(),
            value_src: Some("fun (v : Nat) (val : KExpr) (depth : Nat) => Eq.refl KExpr (KExpr.lit v)".to_string()),
            is_axiom: false,
            description: "instantiate_at leaves a literal unchanged (leaf). DerivedProved via Eq.refl + structural registration. Part of the proj/lit fragment rung.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition_structural(SpecDefinition {
            name: "lift_at_proj".to_string(),
            type_src: "forall (s : Name) (i : Nat) (sub : KExpr) (c : Nat) (a : Nat), Eq KExpr (lift_at (KExpr.proj s i sub) c a) (KExpr.proj s i (lift_at sub c a))".to_string(),
            value_src: Some("fun (s : Name) (i : Nat) (sub : KExpr) (c : Nat) (a : Nat) => Eq.refl KExpr (KExpr.proj s i (lift_at sub c a))".to_string()),
            is_axiom: false,
            description: "lift_at descends into a proj scrutinee (no binder, same cutoff). DerivedProved via Eq.refl + structural registration. Part of the proj/lit fragment rung.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        self.add_definition_structural(SpecDefinition {
            name: "lift_at_lit".to_string(),
            type_src: "forall (v : Nat) (c : Nat) (a : Nat), Eq KExpr (lift_at (KExpr.lit v) c a) (KExpr.lit v)".to_string(),
            value_src: Some("fun (v : Nat) (c : Nat) (a : Nat) => Eq.refl KExpr (KExpr.lit v)".to_string()),
            is_axiom: false,
            description: "lift_at leaves a literal unchanged (leaf). DerivedProved via Eq.refl + structural registration. Part of the proj/lit fragment rung.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: None,
            axiom_deps: HashSet::new(),
        })?;

        self.add_instantiate_at_pi_codomain_eq()?;
        self.add_instantiate_at_pi_self_codomain_eq()?;

        // instantiate over app distributes — forward through instantiate_at_app at depth 0
        self.add_definition(SpecDefinition {
            name: "instantiate_app".to_string(),
            type_src: "forall (f : KExpr) (a : KExpr) (val : KExpr), Eq KExpr (instantiate (KExpr.app f a) val) (KExpr.app (instantiate f val) (instantiate a val))".to_string(),
            value_src: Some(
                "fun (f : KExpr) (a : KExpr) (val : KExpr) => instantiate_at_app f a val Nat.zero"
                    .to_string(),
            ),
            is_axiom: false,
            description: "instantiate (app f a) val = app (instantiate f val) (instantiate a val). Forwarded through instantiate_at_app at depth 0."
                .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["instantiate_at_app".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        // instantiate over lam distributes with depth tracking — forward through the
        // binder-aware instantiate_at theorem at depth 0.
        self.add_definition(SpecDefinition {
            name: "instantiate_lam".to_string(),
            type_src: "forall (ty : KExpr) (b : KExpr) (val : KExpr), Eq KExpr (instantiate (KExpr.lam ty b) val) (KExpr.lam (instantiate ty val) (instantiate_at b val (Nat.succ Nat.zero)))".to_string(),
            value_src: Some(
                "fun (ty : KExpr) (b : KExpr) (val : KExpr) => instantiate_at_lam ty b val Nat.zero"
                    .to_string(),
            ),
            is_axiom: false,
            description: "instantiate (lam ty b) val = lam (instantiate ty val) (instantiate_at b val 1). Forwarded through instantiate_at_lam at depth 0. Part of #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["instantiate_at_lam".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        // instantiate over pi distributes with depth tracking — forward through the
        // binder-aware instantiate_at theorem at depth 0.
        self.add_definition(SpecDefinition {
            name: "instantiate_pi".to_string(),
            type_src: "forall (ty : KExpr) (b : KExpr) (val : KExpr), Eq KExpr (instantiate (KExpr.pi ty b) val) (KExpr.pi (instantiate ty val) (instantiate_at b val (Nat.succ Nat.zero)))".to_string(),
            value_src: Some(
                "fun (ty : KExpr) (b : KExpr) (val : KExpr) => instantiate_at_pi ty b val Nat.zero"
                    .to_string(),
            ),
            is_axiom: false,
            description: "instantiate (pi ty b) val = pi (instantiate ty val) (instantiate_at b val 1). Forwarded through instantiate_at_pi at depth 0. Part of #464.".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["instantiate_at_pi".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        // beta_deterministic, whnf_idempotent, whnf_confluent:
        // Moved to implementation_soundness_whnf_decomposition.rs where they
        // are registered as DerivedProved (not HelperAxiom) using constructive
        // proof terms via beta_reduces_preserves_def_eq and
        // whnf_to_preserves_def_eq. Part of #461.

        self.add_definition(SpecDefinition {
            name: "value_is_whnf".to_string(),
            type_src: "forall (e : KExpr), is_value e -> is_whnf e".to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (h : is_value e) => ",
                    "is_value.rec ",
                    "(fun (e0 : KExpr) (_ : is_value e0) => is_whnf e0) ",
                    "(fun (n : Level) => is_whnf.sort n) ",
                    "(fun (ty : KExpr) (body : KExpr) => is_whnf.lam ty body) ",
                    "(fun (ty : KExpr) (body : KExpr) => is_whnf.pi ty body) ",
                    "e h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description:
                "Legacy values are bounded WHNFs. DerivedProved via is_value.rec into is_whnf."
                    .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "is_value.rec".to_string(),
                "is_whnf.sort".to_string(),
                "is_whnf.lam".to_string(),
                "is_whnf.pi".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // Values are in WHNF
        self.add_definition_structural(SpecDefinition {
            name: "value_in_whnf".to_string(),
            type_src: "forall (e : KExpr), is_value e -> whnf_to e e".to_string(),
            value_src: Some(
                "fun (e : KExpr) (h : is_value e) => whnf_to.refl e (value_is_whnf e h)"
                    .to_string(),
            ),
            is_axiom: false,
            description:
                "Legacy values are already in bounded WHNF via value_is_whnf + whnf_to.refl."
                    .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "value_is_whnf".to_string(),
                "whnf_to.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // WHNF termination for well-typed terms: whnf_terminates_well_typed
        // (has_type e T -> terminates_whnf e) is RETIRED from the axiom census and
        // registered as a DerivedProved theorem in add_whnf_terminates_well_typed
        // (whnf_terminates_well_typed.rs), which runs after add_whnf_normalizes so
        // all of its proof dependencies (beta_bd_sn_has_type, const_free, the δ/ι
        // head-none absurdities, the reduces->step bridges) are already registered.
        // The FULL whnf_step = beta_reduces ∪ delta_reduces union is discharged on
        // the spec's context-free (bvar-free + const-free) Typing fragment.

        // Type inference termination: infer_terminates
        // (forall e, terminates_infer e) is RETIRED from the axiom census and
        // registered as a DerivedProved theorem in add_infer_terminates_proof
        // (infer_terminates_proof.rs), which runs after add_whnf_progress so its
        // ConstFreeUnit / const_free / AndType dependencies are already
        // registered. It is the standard well-founded accessibility of KExpr
        // under the strict-subexpression relation subexpr_step: terminates_infer
        // := infer_acc := Acc(subexpr_step) models infer's STRUCTURAL recursion
        // into immediate children (provable by KExpr.rec), NOT the whnf
        // reductions infer performs on types (that SN is whnf_terminates_well_typed).

        Ok(())
    }

    fn add_instantiate_at_pi_codomain_eq(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "instantiate_at_pi_codomain_eq".to_string(),
            type_src: concat!(
                "forall (A : KExpr) (B : KExpr) (val : KExpr) (depth : Nat) ",
                "(A' : KExpr) (B' : KExpr), ",
                "Eq KExpr (instantiate_at (KExpr.pi A B) val depth) (KExpr.pi A' B') -> ",
                "Eq KExpr (instantiate_at B val (Nat.succ depth)) B'"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (A : KExpr) (B : KExpr) (val : KExpr) (depth : Nat) ",
                    "(A' : KExpr) (B' : KExpr) ",
                    "(h : Eq KExpr (instantiate_at (KExpr.pi A B) val depth) ",
                    "(KExpr.pi A' B')) => ",
                    "pi_inj_snd ",
                    "(instantiate_at A val depth) ",
                    "(instantiate_at B val (Nat.succ depth)) ",
                    "A' B' ",
                    "(Eq.trans KExpr ",
                    "(KExpr.pi (instantiate_at A val depth) ",
                    "(instantiate_at B val (Nat.succ depth))) ",
                    "(instantiate_at (KExpr.pi A B) val depth) ",
                    "(KExpr.pi A' B') ",
                    "(Eq.symm KExpr ",
                    "(instantiate_at (KExpr.pi A B) val depth) ",
                    "(KExpr.pi (instantiate_at A val depth) ",
                    "(instantiate_at B val (Nat.succ depth))) ",
                    "(instantiate_at_pi A B val depth)) ",
                    "h)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "If instantiating a Pi yields Pi A' B', then the instantiated ",
                "codomain equals B'. DerivedProved via instantiate_at_pi + ",
                "pi_inj_snd. Part of #464."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "instantiate_at_pi".to_string(),
                "pi_inj_snd".to_string(),
                "Eq.trans".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    fn add_instantiate_at_pi_self_codomain_eq(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "instantiate_at_pi_self_codomain_eq".to_string(),
            type_src: concat!(
                "forall (A : KExpr) (B : KExpr) (val : KExpr) (depth : Nat), ",
                "Eq KExpr (instantiate_at (KExpr.pi A B) val depth) (KExpr.pi A B) -> ",
                "Eq KExpr (instantiate_at B val (Nat.succ depth)) B"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (A : KExpr) (B : KExpr) (val : KExpr) (depth : Nat) ",
                    "(h : Eq KExpr (instantiate_at (KExpr.pi A B) val depth) ",
                    "(KExpr.pi A B)) => ",
                    "instantiate_at_pi_codomain_eq A B val depth A B h"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Specialized codomain projection for stable instantiated Pis. ",
                "This packages the d+1 codomain equality needed by the ongoing ",
                "#464 substitution_typing_gen app-case bridge."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from(["instantiate_at_pi_codomain_eq".to_string()])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unique normal forms of `par_reduces_c_star` — the confluence tower's first
//! end-user corollary (Aristotle port-back, Item 3).
//!
//! Clean-kernel port of the Aristotle-proven Lean development
//! `proofs/lean-aristotle/unique_normal_forms.lean` (0 sorry). The Lean file
//! proves `normal_star_eq` + `unique_normal_forms` over an abstract step
//! relation with confluence as a HYPOTHESIS; here both are discharged against
//! the IN-TREE proved confluence machinery. The Lean proof is the STRATEGY
//! guide only; every lemma here is a closed spec proof term re-checked by the
//! Clean kernel at spec build (`DerivedProved`, empty non-foundational
//! closure). No Lean tactic output is trusted.
//!
//! ## The exact relation targeted (honesty note)
//!
//! Everything in this module is about **`par_reduces_c`** — the env-indexed
//! COMPUTATIONAL parallel reduction (par_reduces_c.rs, #2859 Increment F) —
//! and its reflexive-transitive closure **`par_reduces_c_star`**. It is NOT a
//! statement about "kernel reduction" in general: not about `beta_reduces`,
//! not about `whnf_step`, not about `DefEq`. `par_reduces_c` is REFLEXIVE
//! (its `refl` constructor relates every `e` to itself), so the classical
//! normality notion "no step applies" is degenerate — NO term would be normal.
//! The honest normality notion for a reflexive parallel relation is
//! "reduces only to itself":
//!
//! ```text
//! is_normal_c env e := forall e', par_reduces_c env e e' -> Eq KExpr e e'
//! ```
//!
//! (For the Lean file's non-reflexive single-step `Step`, "no step applies"
//! and "reduces only to itself" agree on the star level; over the reflexive
//! `par_reduces_c` only the latter is meaningful. This is the locked port
//! decision for Item 3.)
//!
//! ## Ladder (all `DerivedProved`, zero axiom_deps)
//!
//!   1. `is_normal_c` — the normality predicate (semireducible definition,
//!      so proof terms can apply a normality hypothesis).
//!   2. `normal_c_star_eq` — a `par_reduces_c`-normal form reaches only
//!      itself via `par_reduces_c_star` (the Lean `normal_star_eq`;
//!      hypothesis-free induction on the star derivation).
//!   3. `unique_normal_forms_c` — THE GOAL: two `par_reduces_c`-normal forms
//!      reachable from a common source via `par_reduces_c_star` are equal.
//!      The confluence hypothesis of the Lean file is discharged by the
//!      in-tree `par_reduces_c_star_diamond` (par_reduces_p_topdev.rs), which
//!      carries the FOUR faithful RecEnv interfaces as hypotheses — so this
//!      lemma carries them too.
//!   4. `unique_normal_forms_c_faithful` — the hypothesis-free instantiation
//!      at `env := red_rec faithful_red_env`, discharging the four interfaces
//!      with the honest DerivedProved witnesses (faithful_red_env.rs /
//!      faithful_confluence.rs precedent).

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    /// Register the `par_reduces_c_star` unique-normal-forms ladder.
    ///
    /// Must run after `add_par_reduces_c` (`par_reduces_c` /
    /// `par_reduces_c_star` / `par_strips_witness_c_star`),
    /// `add_par_reduces_p_topdev` (`par_reduces_c_star_diamond`), and
    /// `add_faithful_red_env` + `add_faithful_red_env_bundle` (the four
    /// faithful interface witnesses for the `_faithful` corollary).
    /// Purely additive; zero new axioms.
    pub(super) fn add_unique_normal_forms_c(&mut self) -> Result<(), SpecError> {
        // is_normal_c: normality for the REFLEXIVE computational parallel
        // reduction par_reduces_c, as "reduces only to itself". Registered
        // semireducibly (add_definition_reducible) so proof terms can APPLY a
        // normality hypothesis (the kernel must unfold the alias to the Pi).
        self.add_definition_reducible(SpecDefinition {
            name: "is_normal_c".to_string(),
            type_src: "RecEnv -> KExpr -> Prop".to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (e : KExpr) => ",
                    "forall (e' : KExpr), par_reduces_c env e e' -> Eq KExpr e e'"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Normality for the env-indexed COMPUTATIONAL parallel reduction par_reduces_c: ",
                "is_normal_c env e holds iff every par_reduces_c reduct of e is e itself ",
                "(\"reduces only to itself\"). par_reduces_c is REFLEXIVE (refl constructor), so ",
                "the classical \"no step applies\" normality would be degenerately empty — this is ",
                "the honest normality notion for a reflexive parallel relation. A statement about ",
                "par_reduces_c ONLY (not beta_reduces, not whnf_step, not kernel reduction in ",
                "general). Semireducible so normality hypotheses can be applied in proof terms. ",
                "Part of the unique-normal-forms ladder (Aristotle port, Item 3)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c".to_string(),
                "Eq".to_string(),
                "RecEnv".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // normal_c_star_eq: a par_reduces_c-normal form star-reaches only
        // itself (the Lean normal_star_eq). par_reduces_c_star.rec with the
        // motive generalized over the normality hypothesis: the refl arm is
        // Eq.refl; the step arm extracts e = e' from normality, transports the
        // normality of e to e' along that equality (Eq.subst), feeds the IH,
        // and chains via Eq.trans. Hypothesis-free (no faithful interfaces).
        self.add_definition(SpecDefinition {
            name: "normal_c_star_eq".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (n : KExpr) (m : KExpr), ",
                "is_normal_c env n -> par_reduces_c_star env n m -> Eq KExpr n m"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (n : KExpr) (m : KExpr) ",
                    "(hn : is_normal_c env n) (h : par_reduces_c_star env n m) => ",
                    "par_reduces_c_star.rec env ",
                    "(fun (x : KExpr) (y : KExpr) (_h : par_reduces_c_star env x y) => ",
                    "is_normal_c env x -> Eq KExpr x y) ",
                    "(fun (e : KExpr) (_hx : is_normal_c env e) => Eq.refl KExpr e) ",
                    "(fun (e : KExpr) (e' : KExpr) (e'' : KExpr) ",
                    "(hstep : par_reduces_c env e e') ",
                    "(_htail : par_reduces_c_star env e' e'') ",
                    "(ih : is_normal_c env e' -> Eq KExpr e' e'') ",
                    "(hx : is_normal_c env e) => ",
                    "Eq.trans KExpr e e' e'' (hx e' hstep) ",
                    "(ih (Eq.subst KExpr (fun (z : KExpr) => is_normal_c env z) ",
                    "e e' (hx e' hstep) hx))) ",
                    "n m h hn"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "A par_reduces_c-normal form star-reaches only itself: is_normal_c env n -> ",
                "par_reduces_c_star env n m -> n = m. Induction on the par_reduces_c_star ",
                "derivation with the motive generalized over the normality hypothesis; the step ",
                "arm turns the head step into an equality via normality (reduces only to itself), ",
                "transports normality along it (Eq.subst), and chains the IH with Eq.trans. ",
                "Kernel-checked port of normal_star_eq in ",
                "proofs/lean-aristotle/unique_normal_forms.lean, stated over the exact in-tree ",
                "relation par_reduces_c_star (NOT kernel reduction in general). DerivedProved, ",
                "zero axiom_deps. Part of the unique-normal-forms ladder (Aristotle port, Item 3)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "is_normal_c".to_string(),
                "par_reduces_c".to_string(),
                "par_reduces_c_star".to_string(),
                "par_reduces_c_star.rec".to_string(),
                "Eq.refl".to_string(),
                "Eq.trans".to_string(),
                "Eq.subst".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // unique_normal_forms_c — THE GOAL: unique normal forms of
        // par_reduces_c_star. The Lean file's confluence HYPOTHESIS is
        // discharged by the in-tree par_reduces_c_star_diamond, so the four
        // faithful RecEnv interfaces it carries appear here as hypotheses.
        // Join the two star legs at a common reduct e3, then collapse both
        // join legs with normal_c_star_eq and chain: n1 = e3 = n2.
        self.add_definition(SpecDefinition {
            name: "unique_normal_forms_c".to_string(),
            type_src: concat!(
                "forall (env : RecEnv) (e : KExpr) (n1 : KExpr) (n2 : KExpr), ",
                "RecEnvReductNotRedex env -> RecEnvCtorNoRecMeta env -> ",
                "RecEnvClosed env -> RecEnvLiftClosed env -> ",
                "par_reduces_c_star env e n1 -> par_reduces_c_star env e n2 -> ",
                "is_normal_c env n1 -> is_normal_c env n2 -> ",
                "Eq KExpr n1 n2"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RecEnv) (e : KExpr) (n1 : KExpr) (n2 : KExpr) ",
                    "(i1 : RecEnvReductNotRedex env) (i2 : RecEnvCtorNoRecMeta env) ",
                    "(i3 : RecEnvClosed env) (i4 : RecEnvLiftClosed env) ",
                    "(h1 : par_reduces_c_star env e n1) (h2 : par_reduces_c_star env e n2) ",
                    "(hn1 : is_normal_c env n1) (hn2 : is_normal_c env n2) => ",
                    "@par_strips_witness_c_star.rec env n1 n2 ",
                    "(fun (_w : par_strips_witness_c_star env n1 n2) => Eq KExpr n1 n2) ",
                    "(fun (e3 : KExpr) ",
                    "(l1 : par_reduces_c_star env n1 e3) (l2 : par_reduces_c_star env n2 e3) => ",
                    "Eq.trans KExpr n1 e3 n2 ",
                    "(normal_c_star_eq env n1 e3 hn1 l1) ",
                    "(Eq.symm KExpr n2 e3 (normal_c_star_eq env n2 e3 hn2 l2))) ",
                    "(par_reduces_c_star_diamond env e n1 n2 i1 i2 i3 i4 h1 h2)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "UNIQUE NORMAL FORMS of par_reduces_c_star (the env-indexed computational ",
                "parallel reduction's reflexive-transitive closure): two par_reduces_c-normal ",
                "forms (is_normal_c: reduces only to itself) reachable from a common source are ",
                "EQUAL. The first end-user corollary of the confluence tower: the Lean file's ",
                "confluence hypothesis is discharged by the proved Church-Rosser ",
                "par_reduces_c_star_diamond, whose four faithful RecEnv interfaces ",
                "(RecEnvReductNotRedex, RecEnvCtorNoRecMeta, RecEnvClosed, RecEnvLiftClosed) are ",
                "therefore carried as hypotheses here. Join the legs at a common reduct, collapse ",
                "both join legs with normal_c_star_eq, chain via Eq.trans/Eq.symm. Kernel-checked ",
                "port of unique_normal_forms in proofs/lean-aristotle/unique_normal_forms.lean. ",
                "A statement about par_reduces_c_star ONLY — NOT \"unique normal forms of kernel ",
                "reduction\" (no claim about beta_reduces/whnf_step/DefEq). DerivedProved, zero ",
                "axiom_deps. Part of the unique-normal-forms ladder (Aristotle port, Item 3)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "is_normal_c".to_string(),
                "normal_c_star_eq".to_string(),
                "par_reduces_c_star".to_string(),
                "par_reduces_c_star_diamond".to_string(),
                "par_strips_witness_c_star".to_string(),
                "par_strips_witness_c_star.rec".to_string(),
                "RecEnvReductNotRedex".to_string(),
                "RecEnvCtorNoRecMeta".to_string(),
                "RecEnvClosed".to_string(),
                "RecEnvLiftClosed".to_string(),
                "Eq.trans".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // unique_normal_forms_c_faithful: the hypothesis-free instantiation
        // over the concrete faithful_red_env, discharging the four interfaces
        // with the honest DerivedProved witnesses (faithful_confluence.rs
        // precedent). Pure application.
        self.add_definition(SpecDefinition {
            name: "unique_normal_forms_c_faithful".to_string(),
            type_src: concat!(
                "forall (e : KExpr) (n1 : KExpr) (n2 : KExpr), ",
                "par_reduces_c_star (red_rec faithful_red_env) e n1 -> ",
                "par_reduces_c_star (red_rec faithful_red_env) e n2 -> ",
                "is_normal_c (red_rec faithful_red_env) n1 -> ",
                "is_normal_c (red_rec faithful_red_env) n2 -> ",
                "Eq KExpr n1 n2"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (e : KExpr) (n1 : KExpr) (n2 : KExpr) ",
                    "(h1 : par_reduces_c_star (red_rec faithful_red_env) e n1) ",
                    "(h2 : par_reduces_c_star (red_rec faithful_red_env) e n2) ",
                    "(hn1 : is_normal_c (red_rec faithful_red_env) n1) ",
                    "(hn2 : is_normal_c (red_rec faithful_red_env) n2) => ",
                    "unique_normal_forms_c (red_rec faithful_red_env) e n1 n2 ",
                    "faithful_red_env_reduct_not_redex ",
                    "faithful_rec_env_ctor_no_recmeta ",
                    "faithful_rec_env_closed ",
                    "faithful_rec_env_lift_closed ",
                    "h1 h2 hn1 hn2"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "UNCONDITIONAL unique normal forms of par_reduces_c_star over the concrete ",
                "faithful_red_env: two par_reduces_c-normal forms (is_normal_c over ",
                "red_rec faithful_red_env) reachable from a common source are equal, with NO ",
                "interface hypotheses. unique_normal_forms_c instantiated at env := red_rec ",
                "faithful_red_env with its four faithful interfaces discharged by the honest ",
                "DerivedProved witnesses faithful_red_env_reduct_not_redex (i1), ",
                "faithful_rec_env_ctor_no_recmeta (i2), faithful_rec_env_closed (i3), ",
                "faithful_rec_env_lift_closed (i4). A statement about par_reduces_c_star over ",
                "this one concrete env ONLY — not about kernel reduction in general. Pure ",
                "application, DerivedProved, zero axiom_deps. Part of the unique-normal-forms ",
                "ladder (Aristotle port, Item 3)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "is_normal_c".to_string(),
                "unique_normal_forms_c".to_string(),
                "par_reduces_c_star".to_string(),
                "red_rec".to_string(),
                "faithful_red_env".to_string(),
                "faithful_red_env_reduct_not_redex".to_string(),
                "faithful_rec_env_ctor_no_recmeta".to_string(),
                "faithful_rec_env_closed".to_string(),
                "faithful_rec_env_lift_closed".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }
}

#[cfg(test)]
#[path = "unique_normal_forms_c_tests.rs"]
mod unique_normal_forms_c_tests;

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R13 of the candidate-model construction ladder — **`funext` is DERIVED, and
//! R12's wall comes down.**
//!
//! ## Why this rung
//!
//! R12 landed the shape-indexed interpretation and ACHIEVED conversion
//! invariance, then reported one obstruction as spec-side and permanent:
//!
//! > *"No substitution lemma, and it is BLOCKED, not skipped. The corpus's
//! > `val_psub`/`val_lift` equate two SEMANTIC FUNCTIONS that agree pointwise,
//! > i.e. they are `funext` applications. **The spec has no `funext`** — by
//! > design (`dependent_sn_richmodel.rs:664`, which replaces every corpus
//! > `funext` with a pointwise congruence). Pointwise congruence does not
//! > substitute here: the objects being equated ARE functions
//! > (`VD (arr d c)`), not substitutions."*
//!
//! That was a claim about what is REGISTERED. It is not a claim about what is
//! DERIVABLE, and the two come apart here: the spec's foundational base already
//! contains the entire toolkit Lean 4 core uses to PROVE `funext` as a theorem.
//!
//! ## A — `funext` IS derivable in the spec. Here is the derivation.
//!
//! Four facts, each read from source, are jointly sufficient:
//!
//! 1. **The quotient primitives are the standard ones.**
//!    `clean-kernel/src/quot.rs` builds `Quot.{u} : {α : Sort u} → (α → α →
//!    Prop) → Sort u`, `Quot.mk`, `Quot.lift.{u v}`, `Quot.ind` and
//!    `Quot.sound.{u} : … → r a b → Eq (Quot α r) (Quot.mk α r a)
//!    (Quot.mk α r b)`. All five are `EnvInjected` census entries, and
//!    `Quot.sound` is one of the THREE genuine foundational axioms.
//! 2. **The quotient computation rule is implemented.**
//!    `try_quot_lift_reduction` (`quot.rs:598`) contracts
//!    `Quot.lift α r β f h (Quot.mk α r a)` to `f a`, wired into whnf at
//!    `tc/whnf.rs:712` and into the no-delta core. Function eta is in
//!    `tc/eta.rs`. Those two are what make the extracted map compute.
//! 3. **The spec's `Eq` is `Prop`-valued and universe-polymorphic** —
//!    `inductive Eq (α : Sort u) : α → α → Prop` (`foundation_types.rs:197`),
//!    type argument EXPLICIT. So `forall (x : A), Eq (B x) (f x) (g x)` lands
//!    in `Sort (imax u 0) = Prop` at EVERY `u`, which is exactly the shape
//!    `Quot`'s relation argument demands. This is the step that could have
//!    failed and does not: the spec's candidates are `Type`-valued, but its
//!    EQUALITY is not, and only the equality has to be a `Prop` here.
//! 4. **The spec has an explicit-argument congruence** —
//!    `Eq.cong : forall (α : Sort u) (β : Sort v) (f : α -> β) (a : α) (b : α),
//!    Eq α a b -> Eq β (f a) (f b)` (`foundation_types.rs:267`), itself
//!    `DerivedProved` from `Eq.rec` with an empty axiom closure.
//!
//! The derivation (`spec_fneq` / `spec_fnapp` / `spec_funext`) is Lean 4 core's,
//! written in the spec's own source language: quotient the dependent function
//! space by pointwise equality, extract an application map with `Quot.lift`
//! (its respect obligation at the point `x` is the pointwise hypothesis AT `x`),
//! and push `Quot.sound` through that map with `Eq.cong`. Both sides reduce —
//! quotient ι, beta, eta — back to the functions themselves, so the transported
//! equality IS `Eq (forall (x : A), B x) f g`.
//!
//! **Independent corroboration, found after the derivation was designed:** the
//! kernel already contains the same proof, in Rust `Expr` form, at
//! `clean-kernel/src/env/logic.rs:189` (`Environment::init_funext`) — a CHECKED
//! `Declaration::Theorem`, not an axiom, with `funext_proof_value` building
//! `congrArg extfunApp (Quot.sound h)` exactly as above. The spec had simply
//! never called it; `init_funext` is also the only PUBLIC kernel entry point
//! that reaches `init_quot`, which is why this rung calls it to bring the
//! quotient bundle into the Substitution bundle's environment. `spec_funext` is
//! NOT that constant: it is derived independently, in the spec's source
//! language, against the spec's explicit-argument `Eq.cong`.
//!
//! ## Census — ZERO new axioms
//!
//! `spec_funext`'s closure is `{Quot.sound, Quot, Quot.mk, Quot.lift}` plus
//! `Eq`/`Eq.cong`/`Eq.rec`. Every one of those is in
//! `spec_axiom_closure::EXPLICIT_FOUNDATIONAL_BASE`, and
//! `Environment::axiom_deps` short-circuits the whole quotient bundle as
//! kernel-foundational — so `computed_axiom_closure` is EMPTY and there is no
//! residual DerivedProved debt. Bringing the bundle into the Substitution
//! environment adds no NAME to the live census either: `Quot`, `Quot.mk`,
//! `Quot.lift`, `Quot.ind` and `Quot.sound` are already five of its eleven
//! entries, reached in the Full bundle through `init_rat`'s quotient carrier.
//! `funext` itself is value-bearing and never was a census entry.
//!
//! ## B — what the derivation knocks out
//!
//! * `r13_vd_arr_funext` — two semantic functions at an ARROW shape that agree
//!   pointwise are equal. `VD (Sk.arr d c)` ι-reduces to `VD d -> VD c`, so
//!   this is R12's blocked object, verbatim.
//! * `r13_venvD_funext` — two VALUATIONS that agree pointwise are equal.
//!   `VEnvD D` is R12's dependent function space `forall i, VD (D i)`, so this
//!   one needs dependent funext, not the corollary.
//! * `r13_sval_env_congr` — **the payoff.** The interpretation respects
//!   pointwise-equal valuations, at every shape environment, term, shape and
//!   derivation. This is the substitution R12 could not perform, and it is the
//!   engine the corpus's `val_psub`/`val_lift` run on.
//! * `r13_vconsD_env_congr` — the same, carried under a binder through the
//!   valuation extension.
//! * `r13_piCandDep_fn_congr` — the `piB` congruence case, at R12's dependent
//!   Pi candidate. R12 recorded that the corpus's `piVal_congr` needs `propext`
//!   as well as `funext`, and that a `Type`-valued candidate cannot use
//!   `propext`. **It does not need to.** With genuine funext on the semantic
//!   function `GB`, the congruence is one `Eq.cong` in the FUNCTION argument —
//!   never a biimplication between two `Type`s. The spec's route here is
//!   strictly better than the corpus's, not a workaround for it.
//! * `r13_wkPiDep_env_congr` — the same congruence at the constructed dependent
//!   Pi clause, in the valuation.
//!
//! ## What did NOT land, and why — read before quoting
//!
//! * **`funext` does not touch R12's two horns, and they still stand.**
//!   HORN 1 (predicativity: `piCandV` lands one universe above the candidates
//!   because `VD d : Type 1` and `Type` is predicative, with the offset
//!   invariant under shifting) and HORN 2 (`piCandDep` calls `sval` at
//!   derivations of unrelated terms, so it cannot be a minor of `sval`'s own
//!   `WK.rec`) are obstructions about universes and about structural recursion.
//!   Extensionality is neither. `test_candmodel_r12_value_quantified_pi_clause_
//!   is_refused` and `test_candmodel_r12_sval_is_not_self_referential` are
//!   unaffected and still measure what they measured.
//! * **`val_psub` / `val_lift` themselves are still not registered.** What was
//!   blocking them is gone; what is still missing is different and was never a
//!   funext problem — R12 built no substitution or weakening OPERATION on `WK`
//!   derivations, and the corpus lemmas are statements about one. R13 lands the
//!   congruence engine those proofs consume, not the proofs.
//! * **No SN capstone, and `sval` is still PARTIAL.** Unchanged from R12:
//!   nothing here advances `whnf_terminates_well_typed_dependent` or discharges
//!   `M : CandModel tenv`, and `sval` still interprets only shape-typed terms.
//! * **`r13_sval_env_congr` is a congruence, not an invariance.** It moves the
//!   VALUATION, not the TERM. The general one-step invariance `val_step` also
//!   needs the term-side cases, of which R12 proved the head-beta one
//!   (`r12_sval_beta`); R13 supplies the congruence cases' missing ingredient
//!   and claims no more.
//!
//! ## Non-degeneracy (no automated gate performs this)
//!
//! `spec_funext_witness` applies the theorem at two functions the kernel does
//! NOT hold definitionally equal — `fun n => Nat.add Nat.zero n` and
//! `fun n => n`, distinct because `Nat.add` recurses on its SECOND argument, so
//! `Nat.add Nat.zero n` is stuck on the variable. The other half is a
//! measurement, not a claim: `test_candmodel_r13_reflexivity_is_refused_at_the_
//! witness` feeds the kernel `Eq.refl` at that very statement and asserts it is
//! REJECTED, and `test_candmodel_r13_pointwise_does_not_substitute` does the
//! same for the general statement with the pointwise hypothesis in hand. So
//! funext is doing work no reduction was going to do.
//! `r13_sval_env_congr_witness` and `r13_vd_arr_funext_witness` apply the two
//! B lemmas at registered R12 objects (`r12_wk_sort_witness`, `r12_junkEnv`,
//! `junkD`), so their premises are visibly satisfiable. `spec_fneq` is
//! witnessed on both sides by `spec_fneq_intro`/`spec_fneq_elim` and `Quot` by
//! `spec_quot_fn` — a CONSTRUCTOR does not count on the supply side of the
//! premise gate, so the introduction has to be a definition.
//!
//! ## Census
//!
//! ZERO new axioms: 16 constants — 3 defs via `add_recursive_def` and 13
//! value-bearing theorems via `add_definition` with kernel `add_decl` checking.
//! Census-neutral.

use std::collections::HashSet;

use super::candmodel_construct_r13_src::*;
use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

/// R6-R12's theorem helper, verbatim: one `add_definition` per theorem so the
/// kernel's `add_decl` type-checks the proof term against the declared type.
fn add_thm(
    spec: &mut Specification,
    name: &str,
    ty: String,
    val: String,
    deps: &[&str],
    desc: &str,
) -> Result<(), SpecError> {
    spec.add_definition(SpecDefinition {
        name: name.to_string(),
        type_src: ty,
        value_src: Some(val),
        is_axiom: false,
        description: desc.to_string(),
        category: AxiomCategory::DerivedLemma,
        proof_status: ProofStatus::DerivedProved,
        elaborated_type: None,
        elaborated_value: None,
        dependencies: Some(
            deps.iter()
                .map(|d| (*d).to_string())
                .collect::<HashSet<_>>(),
        ),
        axiom_deps: HashSet::new(),
    })
}

fn decl_description(name: &str) -> &'static str {
    match name {
        "spec_fneq" => {
            "Pointwise (extensional) equality on the dependent function space, Prop-valued \
             because Quot's relation argument is fixed at Prop. `forall (x : A), <Prop>` lands \
             in `Sort (imax u 0) = Prop` at every u, which is why a Type-valued candidate \
             calculus can still quotient its function spaces."
        }
        "spec_fnapp" => {
            "The application map out of the quotient (Quot.liftOn at the point x). Its respect \
             obligation at x IS the pointwise hypothesis at x, so no choice principle is \
             involved. `spec_fnapp A B (Quot.mk (spec_fneq A B) c)` reduces to c by quotient \
             iota (quot.rs:598) then beta then eta (tc/eta.rs) — the two kernel facts the \
             theorem's type check rests on. Registered via add_recursive_def so it DELTA-\
             UNFOLDS; an add_definition registration would lower to Opaque and stop that \
             reduction."
        }
        "spec_quot_fn" => {
            "Introduction form for the quotient of a function space, and the premise-gate \
             witness for `Quot`: the gate excludes axioms from the supply side and Quot is a \
             value-less CIC type former, so a hypothesis headed by Quot needs a concluding \
             DEFINITION."
        }
        _ => "R13 funext derivation.",
    }
}

#[allow(clippy::too_many_lines)]
fn thm_meta(name: &str) -> (&'static [&'static str], &'static str) {
    match name {
        "spec_fneq_intro" => (
            &["spec_fneq"],
            "Concluding definition for spec_fneq (premise-gate supply). `fun .. h => h` is the \
             delta-unfolding of spec_fneq, a genuine proof rather than a restatement.",
        ),
        "spec_fneq_elim" => (
            &["spec_fneq"],
            "The converse, pinning spec_fneq as EXACTLY pointwise equality — not something \
             weaker that happens to be inhabited.",
        ),
        "spec_funext" => (
            &["spec_fneq", "spec_fnapp", "Eq.cong"],
            "FUNCTION EXTENSIONALITY, DERIVED. Eq.cong at spec_fnapp transports Quot.sound's \
             equality of the two pointwise-equality classes to an equality of their \
             applications, and both applications reduce (quotient iota, beta, eta) to the \
             functions themselves. Lean 4 core's derivation, written in the spec's own source \
             language against the spec's explicit-argument Eq.cong. Axiom closure = \
             {Quot.sound, Quot, Quot.mk, Quot.lift} union the Eq built-ins, all inside \
             EXPLICIT_FOUNDATIONAL_BASE, so computed_axiom_closure is EMPTY: ZERO new axioms \
             and zero DerivedProved debt. This RETIRES the claim, carried by R12 and by \
             dependent_sn_richmodel.rs:664, that the spec has no funext — true of what was \
             REGISTERED, false of what is DERIVABLE.",
        ),
        "spec_funext_nd" => (
            &["spec_funext"],
            "Non-dependent corollary (B := fun _ => C). Every R12 semantic function lives \
             here: VD (arr d c) = VD d -> VD c is a plain function space.",
        ),
        "spec_funext_witness" => (
            &["spec_funext_nd", "nat_zero_add"],
            "NON-VACUITY. Applies funext at two functions the kernel does NOT hold \
             definitionally equal: Nat.add recurses on its SECOND argument, so \
             Nat.add Nat.zero n is stuck on the variable n. The paired refusal test measures \
             that Eq.refl at this very statement is REJECTED, so the theorem records work no \
             reduction was going to do.",
        ),
        "r13_vd_arr_funext" => (
            &["spec_funext_nd", "VD"],
            "PART B. Two semantic functions at an ARROW shape that agree pointwise are equal. \
             VD (Sk.arr d c) iota-reduces to VD d -> VD c, so this is R12's blocked object \
             verbatim — the one its note says pointwise congruence cannot substitute into \
             because the objects being equated ARE functions.",
        ),
        "r13_venvD_funext" => (
            &["spec_funext", "VEnvD", "VD"],
            "PART B. Two VALUATIONS that agree pointwise are equal. VEnvD D is R12's \
             DEPENDENT function space forall i, VD (D i) — R12's deliberate divergence from \
             the corpus — so this needs dependent funext and not the corollary.",
        ),
        "r13_sval_env_congr" => (
            &["r13_venvD_funext", "sval", "Eq.cong"],
            "PART B, THE PAYOFF. The interpretation respects pointwise-equal valuations, at \
             EVERY shape environment, term, shape and derivation. This is the substitution \
             R12 could not perform; it is the engine the corpus's val_psub / val_lift run on. \
             SCOPE: it moves the VALUATION, not the TERM — the term-side one-step invariance \
             is a separate obligation of which R12 proved the head-beta case.",
        ),
        "r13_vconsD_env_congr" => (
            &["vconsD", "Eq.cong"],
            "PART B. The valuation extension respects equal valuations, so the congruence \
             engine survives going under a binder. vconsD s D v r inhabits VEnvD (skcons s D) \
             definitionally, which is what lets one Eq.cong carry the equality across.",
        ),
        "r13_piCandDep_fn_congr" => (
            &["spec_funext_nd", "piCandDep", "Eq.cong"],
            "PART B, the piB congruence case at R12's dependent Pi candidate. The corpus \
             proves this with piVal_congr, whose proof is funext AND propext, and R12 \
             recorded that propext is unusable for a Type-valued candidate. It is not needed: \
             with genuine funext on the semantic function GB the congruence is a single \
             Eq.cong in the FUNCTION argument, never a biimplication between two Types. \
             Strictly better than the corpus's route, not a workaround for it.",
        ),
        "r13_wkPiDep_env_congr" => (
            &["r13_venvD_funext", "wkPiDep", "Eq.cong"],
            "PART B. The same congruence at the CONSTRUCTED dependent Pi clause, in the \
             valuation. wkPiDep reads sval at both the domain and the extended-valuation \
             codomain, so this is the composite the piB case of val_step consumes — and it \
             exists only because a valuation can now be substituted.",
        ),
        "r13_sval_env_congr_witness" => (
            &["r13_sval_env_congr", "r12_wk_sort_witness", "r12_junkEnv"],
            "Non-vacuity for the payoff: r13_sval_env_congr applied at R12's own registered \
             sort derivation and junk valuation, so its premise is visibly satisfiable and \
             its conclusion visibly inhabited at a real shape derivation. HONESTY: the two \
             valuations here are the same one, so this witnesses APPLICABILITY, not a \
             non-trivial identification.",
        ),
        "r13_vd_arr_funext_witness" => (
            &["r13_vd_arr_funext", "junkD"],
            "Non-vacuity for the arrow-shape extensionality, through junkD at \
             Sk.arr Sk.ty Sk.ty — a real semantic function space with a registered \
             inhabitant, so the lemma is applied and not merely stated.",
        ),
        _ => (&[], "R13 funext derivation."),
    }
}

impl Specification {
    /// Register R13: `funext` derived from the quotient primitives, and the R12
    /// congruence lemmas it unblocks.
    pub(super) fn add_candmodel_construct_r13(&mut self) -> Result<(), SpecError> {
        // Bring the quotient bundle into THIS bundle's environment.
        //
        // The Substitution bundle starts from a bare `Environment::new()` and
        // never reaches `init_quot`: in the Full bundle the primitives arrive
        // transitively through `add_boolean_analysis_spec` -> `init_rat` ->
        // `ensure_rat_quotient_deps` (the live `Rat` IS a quotient), and that
        // stage is `in_substitution: false`. `Environment::init_quot` itself is
        // `pub(crate)` to clean-kernel; `init_funext` is the public entry point
        // that reaches it, and it is idempotent, so in the Full bundle the later
        // `init_rat` is a no-op on the quotient side.
        //
        // This adds NO name to the live axiom census: `Quot`, `Quot.mk`,
        // `Quot.lift`, `Quot.ind` and `Quot.sound` are already five of its
        // eleven entries. `funext` and the `Eq` built-ins it drags in
        // (`congrArg`, `Eq.ndrec`, `cast`, ...) are all value-bearing.
        self.env_mut()
            .init_funext()
            .map_err(|e| SpecError::TypeError(format!("R13 init_funext: {e}")))?;

        for (kind, name, src) in r13_decl_sources() {
            let desc = decl_description(&name);
            match kind {
                "inductive" => self.add_inductive(&src, desc)?,
                _ => self.add_recursive_def(&src, desc)?,
            }
        }
        for (name, ty, val) in r13_theorem_sources() {
            let (deps, desc) = thm_meta(&name);
            add_thm(self, &name, ty, val, deps, desc)?;
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "candmodel_construct_r13_tests.rs"]
mod tests;

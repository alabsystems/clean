// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Increment H++ (#2859 computational-iota/delta track, DELTA INCREMENT Stage 4,
//! the HINDLEY-ROSEN assembly): the β+ι/δ COMMUTATION star-tiling, parameterized on
//! the single-step strong commutation `SC` as a BOUND HYPOTHESIS.
//!
//! ## The commutation (verified blueprint §(a)/(c): `SC` ⟹ `commute_one` ⟹ `commute`)
//!
//! `HindleyRosen_delta_VERIFIED.lean` reduces the β+ι/δ commutation to the single
//! load-bearing lemma
//!
//!   `SC : Par e a → DeltaStep e b → ∃ d, DeltaStar a d ∧ Par b d`
//!
//! (a single β+ι parallel step and a single δ step from `e` join: δ catches `a` up —
//! possibly DUPLICATED, hence a `DeltaStar` — and a single β+ι step catches `b` up).
//! From `SC` the two-level tiling is mechanical:
//!   - `commute_one : Par e a → DeltaStar e b → ∃ d, DeltaStar a d ∧ ParStar b d`
//!     (one β+ι step vs a whole δ-chain — induction on the δ-chain, `SC` at the head);
//!   - `commute : ParStar e a → DeltaStar e b → ∃ c, DeltaStar a c ∧ ParStar b c`
//!     (a β+ι-chain vs a δ-chain — induction on the β+ι-chain, `commute_one` at the head).
//!
//! This module ports `commute_one` / `commute` ABSTRACTLY: the single-step
//! commutation `SC` is carried as a BOUND HYPOTHESIS (not a registered axiom),
//! exactly as `delta_cong_star_diamond_of_strong` carries its `SC`. So
//! `par_delta_commute_of_sc` is genuinely 0-axiom — it ISOLATES the β+ι/δ commutation
//! (and hence, through the Hindley-Rosen composition, the 3-way β+ι+δ Church-Rosser)
//! to exactly the single-step strong commutation `par_delta_sc`.
//!
//! In the in-tree encoding `Par` ↔ `par_reduces_c (red_rec env)`, `DeltaStep` ↔
//! `delta_cong env`, `DeltaStar` ↔ `delta_cong_star env`, `ParStar` ↔
//! `par_reduces_c_star (red_rec env)`; the `SC` output `∃ d, DeltaStar a d ∧ Par b d`
//! is the witness `par_delta_sc_witness`, and `commute`'s output `∃ c, DeltaStar a c ∧
//! ParStar b c` is `par_delta_commute_witness` (from `par_reduces_cd_hr`).
//!
//! Runs AFTER `add_par_reduces_cd_hr` (so `par_delta_commute_witness` is in scope).
//! Part of #2859 (Increment H++, delta increment Stage 4 — Hindley-Rosen assembly).

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

/// The single-step strong-commutation hypothesis type (`SC`): a single β+ι step and
/// a single δ step from a common source join, the δ side bounded to a `delta_cong_star`
/// (it may duplicate the δ-redex) and the β+ι side to ONE `par_reduces_c` step.
const SC_TYPE: &str = concat!(
    "(forall (s : KExpr) (u : KExpr) (v : KExpr), ",
    "par_reduces_c (red_rec env) s u -> delta_cong env s v -> par_delta_sc_witness env u v)"
);

impl Specification {
    pub(super) fn add_par_reduces_cd_commute(&mut self) -> Result<(), SpecError> {
        self.add_par_delta_sc_witness()?;
        self.add_par_delta_commute_one_of_sc()?;
        self.add_par_delta_commute_of_sc()?;
        Ok(())
    }

    /// Brick B0: the single-step strong-commutation witness `par_delta_sc_witness` —
    /// the output of `SC`: a common reduct `d` with `delta_cong_star env a d` (the
    /// β+ι-reduct `a` catches up on δ, possibly duplicated) and `par_reduces_c
    /// (red_rec env) b d` (the δ-reduct `b` catches up in ONE β+ι step). Mirror of the
    /// blueprint's `∃ d, DeltaStar a d ∧ Par b d`.
    fn add_par_delta_sc_witness(&mut self) -> Result<(), SpecError> {
        self.add_inductive(
            r"inductive par_delta_sc_witness (env : RedEnv) : KExpr → KExpr → Type
| intro : forall (a : KExpr) (b : KExpr) (d : KExpr), delta_cong_star env a d → par_reduces_c (red_rec env) b d → par_delta_sc_witness env a b",
            "par_delta_sc_witness env a b packages a common reduct d with delta_cong_star env a d (the \
             β+ι-reduct a catches up on δ, possibly duplicated) and par_reduces_c (red_rec env) b d (the \
             δ-reduct b catches up in ONE β+ι step) — the single-step strong-commutation (SC) output. Mirror \
             of the blueprint's ∃ d, DeltaStar a d ∧ Par b d. Part of #2859 (Increment H++, delta increment \
             Stage 4 — Hindley-Rosen assembly).",
        )?;
        Ok(())
    }

    /// Brick B1: `par_delta_commute_one_of_sc` — one β+ι step commuted past a whole
    /// δ-chain (blueprint `commute_one`), parameterized on `SC`. Induction on the
    /// δ-chain `delta_cong_star env e b` (motive generalized over the β+ι reduct):
    /// the refl arm embeds the single β+ι step into the closure; the step arm fires
    /// `SC` at the head δ-step, feeds the bounded β+ι residual into the IH, and
    /// re-closes the δ side via `delta_cong_star_trans`.
    fn add_par_delta_commute_one_of_sc(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "par_delta_commute_one_of_sc".to_string(),
            type_src: format!(
                "forall (env : RedEnv) (SC : {SC_TYPE}) (e : KExpr) (a : KExpr) (b : KExpr), \
                 par_reduces_c (red_rec env) e a -> delta_cong_star env e b -> \
                 par_delta_commute_witness env a b"
            ),
            value_src: Some(par_delta_commute_one_of_sc_proof()),
            is_axiom: false,
            description: concat!(
                "par_delta_commute_one_of_sc — one β+ι step commuted past a whole δ-chain (blueprint ",
                "commute_one), parameterized on the single-step strong commutation SC (a bound hypothesis, NOT ",
                "a registered axiom). Induction on the δ-chain delta_cong_star env e b (motive generalized over ",
                "the β+ι reduct): refl embeds the single β+ι step (par_subsumes_par_c_star); step fires SC at the ",
                "head δ-step, feeds the bounded β+ι residual into the IH, and re-closes the δ side via ",
                "delta_cong_star_trans. DerivedProved, zero axiom_deps. Part of #2859 (Increment H++, delta ",
                "increment Stage 4 — Hindley-Rosen assembly)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c".to_string(),
                "par_reduces_c_star".to_string(),
                "par_subsumes_par_c_star".to_string(),
                "delta_cong".to_string(),
                "delta_cong_star".to_string(),
                "delta_cong_star.rec".to_string(),
                "delta_cong_star.refl".to_string(),
                "delta_cong_star_trans".to_string(),
                "par_delta_sc_witness".to_string(),
                "par_delta_sc_witness.rec".to_string(),
                "par_delta_commute_witness".to_string(),
                "par_delta_commute_witness.intro".to_string(),
                "par_delta_commute_witness.rec".to_string(),
                "red_rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        Ok(())
    }

    /// Brick B2: `par_delta_commute_of_sc` — a whole β+ι-chain commuted past a whole
    /// δ-chain (blueprint `commute`), parameterized on `SC`. Induction on the β+ι-chain
    /// `par_reduces_c_star env e a` (motive generalized over the δ reduct): the refl
    /// arm meets at `b`; the step arm runs `par_delta_commute_one_of_sc` at the head
    /// β+ι step, feeds the δ residual into the IH, and re-closes the β+ι side via
    /// `par_reduces_c_star_trans`. THE β+ι/δ commutation, isolated to exactly `SC`.
    fn add_par_delta_commute_of_sc(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "par_delta_commute_of_sc".to_string(),
            type_src: format!(
                "forall (env : RedEnv) (SC : {SC_TYPE}) (e : KExpr) (a : KExpr) (b : KExpr), \
                 par_reduces_c_star (red_rec env) e a -> delta_cong_star env e b -> \
                 par_delta_commute_witness env a b"
            ),
            value_src: Some(par_delta_commute_of_sc_proof()),
            is_axiom: false,
            description: concat!(
                "par_delta_commute_of_sc — a whole β+ι-chain commuted past a whole δ-chain (blueprint commute), ",
                "parameterized on the single-step strong commutation SC (a bound hypothesis). Induction on the ",
                "β+ι-chain par_reduces_c_star env e a (motive generalized over the δ reduct): refl meets at b; ",
                "step runs par_delta_commute_one_of_sc at the head β+ι step, feeds the δ residual into the IH, ",
                "and re-closes the β+ι side via par_reduces_c_star_trans. THE β+ι/δ commutation (the COMM corner ",
                "of the Hindley-Rosen tiling), ISOLATED to exactly the single-step strong commutation SC. ",
                "DerivedProved, zero axiom_deps. Part of #2859 (Increment H++, delta increment Stage 4 — ",
                "Hindley-Rosen assembly)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "par_reduces_c".to_string(),
                "par_reduces_c_star".to_string(),
                "par_reduces_c_star.rec".to_string(),
                "par_reduces_c_star.refl".to_string(),
                "par_reduces_c_star_trans".to_string(),
                "delta_cong_star".to_string(),
                "par_delta_commute_one_of_sc".to_string(),
                "par_delta_commute_witness".to_string(),
                "par_delta_commute_witness.intro".to_string(),
                "par_delta_commute_witness.rec".to_string(),
                "red_rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        Ok(())
    }
}

/// Proof term for `par_delta_commute_one_of_sc`. `delta_cong_star.rec` on the δ-chain
/// `e ⇒* b`, motive `fun e b _ => forall a, par_reduces_c (red_rec env) e a ->
/// par_delta_commute_witness env a b`.
fn par_delta_commute_one_of_sc_proof() -> String {
    let motive = concat!(
        "(fun (x : KExpr) (y : KExpr) (_ : delta_cong_star env x y) => ",
        "forall (a : KExpr), par_reduces_c (red_rec env) x a -> par_delta_commute_witness env a y)"
    );
    // refl arm (x = y = s): meet at a (the β+ι reduct). δ* a a refl, β+ι* s a subsumes.
    let refl_arm = concat!(
        "(fun (s : KExpr) => ",
        "fun (a : KExpr) (hpar : par_reduces_c (red_rec env) s a) => ",
        "par_delta_commute_witness.intro env a s a (delta_cong_star.refl env a) ",
        "(par_subsumes_par_c_star (red_rec env) s a hpar))"
    );
    // step arm: x ⇒ x1 (δ-step h1), x1 ⇒* y (tail), ih. Given a, hpar : β+ι x => a.
    // SC s u v = SC x a x1 hpar h1 : par_delta_sc_witness env a x1 = ∃d, δ* a d ∧ β+ι x1 d.
    // ih d (β+ι x1 d) : par_delta_commute_witness env d y = ∃c, δ* d c ∧ β+ι* y c.
    let step_arm = concat!(
        "(fun (x : KExpr) (x1 : KExpr) (y : KExpr) ",
        "(h1 : delta_cong env x x1) (_htail : delta_cong_star env x1 y) ",
        "(ih : forall (a : KExpr), par_reduces_c (red_rec env) x1 a -> par_delta_commute_witness env a y) => ",
        "fun (a : KExpr) (hpar : par_reduces_c (red_rec env) x a) => ",
        "@par_delta_sc_witness.rec env a x1 ",
        "(fun (_w : par_delta_sc_witness env a x1) => par_delta_commute_witness env a y) ",
        "(fun (d : KExpr) (hd1 : delta_cong_star env a d) (hd2 : par_reduces_c (red_rec env) x1 d) => ",
        "@par_delta_commute_witness.rec env d y ",
        "(fun (_w : par_delta_commute_witness env d y) => par_delta_commute_witness env a y) ",
        "(fun (c : KExpr) (hc1 : delta_cong_star env d c) (hc2 : par_reduces_c_star (red_rec env) y c) => ",
        "par_delta_commute_witness.intro env a y c ",
        "(delta_cong_star_trans env a d c hd1 hc1) hc2) ",
        "(ih d hd2)) ",
        "(SC x a x1 hpar h1))"
    );
    format!(
        concat!(
            "fun (env : RedEnv) (SC : {sc}) (e : KExpr) (a : KExpr) (b : KExpr) ",
            "(hpar : par_reduces_c (red_rec env) e a) (hb : delta_cong_star env e b) => ",
            "delta_cong_star.rec env {motive} {refl_arm} {step_arm} e b hb a hpar"
        ),
        sc = SC_TYPE,
        motive = motive,
        refl_arm = refl_arm,
        step_arm = step_arm,
    )
}

/// Proof term for `par_delta_commute_of_sc`. `par_reduces_c_star.rec` on the β+ι-chain
/// `e ⇒* a`, motive `fun e a _ => forall b, delta_cong_star env e b ->
/// par_delta_commute_witness env a b`.
fn par_delta_commute_of_sc_proof() -> String {
    let motive = concat!(
        "(fun (x : KExpr) (y : KExpr) (_ : par_reduces_c_star (red_rec env) x y) => ",
        "forall (b : KExpr), delta_cong_star env x b -> par_delta_commute_witness env y b)"
    );
    // refl arm (x = y = s): meet at b. δ* s b (hb), β+ι* b b refl.
    let refl_arm = concat!(
        "(fun (s : KExpr) => ",
        "fun (b : KExpr) (hb : delta_cong_star env s b) => ",
        "par_delta_commute_witness.intro env s b b hb (par_reduces_c_star.refl (red_rec env) b))"
    );
    // step arm: x ⇒ x1 (β+ι step hstep), x1 ⇒* y (tail), ih. Given b, hb : δ* x b.
    // commute_one hstep hb : par_delta_commute_witness env x1 b = ∃d1, δ* x1 d1 ∧ β+ι* b d1.
    // ih d1 (δ* x1 d1) : par_delta_commute_witness env y d1 = ∃c, δ* y c ∧ β+ι* d1 c.
    let step_arm = concat!(
        "(fun (x : KExpr) (x1 : KExpr) (y : KExpr) ",
        "(hstep : par_reduces_c (red_rec env) x x1) (_htail : par_reduces_c_star (red_rec env) x1 y) ",
        "(ih : forall (b : KExpr), delta_cong_star env x1 b -> par_delta_commute_witness env y b) => ",
        "fun (b : KExpr) (hb : delta_cong_star env x b) => ",
        "@par_delta_commute_witness.rec env x1 b ",
        "(fun (_w : par_delta_commute_witness env x1 b) => par_delta_commute_witness env y b) ",
        "(fun (d1 : KExpr) (he1d1 : delta_cong_star env x1 d1) (hbd1 : par_reduces_c_star (red_rec env) b d1) => ",
        "@par_delta_commute_witness.rec env y d1 ",
        "(fun (_w : par_delta_commute_witness env y d1) => par_delta_commute_witness env y b) ",
        "(fun (c : KExpr) (hac : delta_cong_star env y c) (hd1c : par_reduces_c_star (red_rec env) d1 c) => ",
        "par_delta_commute_witness.intro env y b c hac ",
        "(par_reduces_c_star_trans (red_rec env) b d1 c hbd1 hd1c)) ",
        "(ih d1 he1d1)) ",
        "(par_delta_commute_one_of_sc env SC x x1 b hstep hb))"
    );
    format!(
        concat!(
            "fun (env : RedEnv) (SC : {sc}) (e : KExpr) (a : KExpr) (b : KExpr) ",
            "(hpar : par_reduces_c_star (red_rec env) e a) (hb : delta_cong_star env e b) => ",
            "par_reduces_c_star.rec (red_rec env) {motive} {refl_arm} {step_arm} e a hpar b hb"
        ),
        sc = SC_TYPE,
        motive = motive,
        refl_arm = refl_arm,
        step_arm = step_arm,
    )
}

#[cfg(test)]
#[path = "par_reduces_cd_commute_tests.rs"]
mod par_reduces_cd_commute_tests;

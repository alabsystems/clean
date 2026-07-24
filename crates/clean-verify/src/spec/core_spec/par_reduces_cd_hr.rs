// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Increment H++ (#2859 computational-iota/delta track, DELTA INCREMENT Stage 4,
//! the HINDLEY-ROSEN assembly): the abstract Hindley-Rosen tiling that composes
//! β+ι Church-Rosser (`par_reduces_c_star_diamond`), δ Church-Rosser
//! (`delta_cong_star_diamond`) and the β+ι/δ commutation into the 3-way
//! (β+ι+δ) Church-Rosser of `par_reduces_cd_star`.
//!
//! ## The macro-step tiling (verbatim port of the verified blueprint §(b))
//!
//! `HindleyRosen_delta_VERIFIED.lean` proves union confluence by a MACRO STEP
//!
//!   `MStep a b := ParStar a b ∨ DeltaStar a b`   (a whole β+ι block OR a whole δ block)
//!
//! whose reflexive-transitive closure `MStar` is inter-derivable with the union
//! closure `StepStar`. The key is that `MStep` has a GENUINE single-macro-step
//! diamond (`M_diamond`), obtained by a 2×2 split on the two disjuncts:
//!   - (β+ι, β+ι) → `par_reduces_c_star_diamond` (β+ι CR);
//!   - (β+ι, δ) / (δ, β+ι) → the commutation;
//!   - (δ, δ) → `delta_cong_star_diamond` (δ CR).
//! From the single-step diamond, `M_strip` and `MStar_confluent` give confluence
//! of `MStar` by the standard two inductions.
//!
//! This module ports that tiling ABSTRACTLY: the three corner join-lemmas are
//! carried as BOUND HYPOTHESES (`PCR` / `DCR` / `COMM`), NOT registered axioms, so
//! the closure is genuinely zero-axiom — exactly the way
//! `delta_cong_star_diamond_of_strong` carries its `SC` hypothesis. The composition
//! module discharges the three corners with the landed β+ι CR, the landed δ CR and
//! the commutation, and bridges `MStar` confluence to the named target
//! `par_reduces_cd_star_diamond` via the closure-coincidence sandwich.
//!
//! In the in-tree encoding the macro step is
//!
//!   `m_step env a b := par_reduces_c_star (red_rec env) a b  ∨  delta_cong_star env a b`
//!
//! (an inductive with two ctors `par` / `delta`), `m_star` its RT-closure, and the
//! three join shapes (`m_step_join` / `m_strip_witness` / `m_star_join`) plus the
//! commutation witness `par_delta_commute_witness` are explicit Type-valued
//! inductives (the in-tree analogue of the blueprint's `∃ … ∧ …`).
//!
//! Runs AFTER `add_par_reduces_d_diamond` (so `par_reduces_c_star`,
//! `delta_cong_star`, `par_strips_witness_c_star`, `par_strips_witness_d_star`,
//! `par_reduces_c_star_diamond` and `delta_cong_star_diamond` are all in scope).
//! Part of #2859 (Increment H++, delta increment Stage 4 — Hindley-Rosen assembly).

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

impl Specification {
    pub(super) fn add_par_reduces_cd_hr(&mut self) -> Result<(), SpecError> {
        self.add_hr_macro_relations()?;
        self.add_hr_macro_combinators()?;
        self.add_hr_macro_diamond_of()?;
        self.add_hr_macro_strip_of()?;
        self.add_hr_mstar_confluent_of()?;
        Ok(())
    }

    /// Brick C0: the macro-step relation `m_step` (a whole β+ι block OR a whole δ
    /// block), its RT-closure `m_star`, the three join shapes (`m_step_join` /
    /// `m_strip_witness` / `m_star_join`) and the commutation witness
    /// `par_delta_commute_witness`. The in-tree analogue of the blueprint's
    /// `MStep`/`MStar` and the `∃ … ∧ …` join packages.
    fn add_hr_macro_relations(&mut self) -> Result<(), SpecError> {
        // m_step env a b: one macro step — a β+ι block (par_reduces_c_star over
        // red_rec env) OR a δ block (delta_cong_star env). Both disjuncts are
        // reflexive, so m_step is reflexive (via either ctor with a refl leg).
        self.add_inductive(
            r"inductive m_step (env : RedEnv) : KExpr → KExpr → Type
| par : forall (a : KExpr) (b : KExpr), par_reduces_c_star (red_rec env) a b → m_step env a b
| delta : forall (a : KExpr) (b : KExpr), delta_cong_star env a b → m_step env a b",
            "m_step env a b — one Hindley-Rosen MACRO STEP: a whole β+ι block (par_reduces_c_star over \
             red_rec env, ctor par) OR a whole δ block (delta_cong_star env, ctor delta). The in-tree \
             analogue of the blueprint's MStep = ParStar ∪ DeltaStar. Part of #2859 (Increment H++, \
             delta increment Stage 4 — Hindley-Rosen assembly).",
        )?;

        // m_star env a b: the reflexive-transitive closure of m_step. Mirror of the
        // blueprint's MStar.
        self.add_inductive(
            r"inductive m_star (env : RedEnv) : KExpr → KExpr → Type
| refl : forall (e : KExpr), m_star env e e
| step : forall (a : KExpr) (b : KExpr) (c : KExpr), m_step env a b → m_star env b c → m_star env a c",
            "m_star env a c — the reflexive-transitive closure of the macro step m_step. Mirror of the \
             blueprint's MStar; inter-derivable with the union closure par_reduces_cd_star. Part of #2859 \
             (Increment H++, delta increment Stage 4 — Hindley-Rosen assembly).",
        )?;

        // m_step_join env a b: the single-macro-step diamond output — a common reduct
        // c with m_step a c and m_step b c. Mirror of the blueprint's
        // `∃ c, MStep a c ∧ MStep b c`.
        self.add_inductive(
            r"inductive m_step_join (env : RedEnv) : KExpr → KExpr → Type
| intro : forall (a : KExpr) (b : KExpr) (c : KExpr), m_step env a c → m_step env b c → m_step_join env a b",
            "m_step_join env a b packages a common reduct c with m_step env a c and m_step env b c — the \
             genuine single-macro-step diamond output (each side joins in ONE macro step). Mirror of the \
             blueprint's M_diamond conclusion ∃ c, MStep a c ∧ MStep b c. Part of #2859 (Increment H++, \
             delta increment Stage 4 — Hindley-Rosen assembly).",
        )?;

        // m_strip_witness env b a: the strip-lemma output — a common reduct c with
        // m_star b c (the long side) and m_step a c (the bounded single side). Mirror
        // of the blueprint's M_strip conclusion `∃ c, MStar b c ∧ MStep a c`.
        self.add_inductive(
            r"inductive m_strip_witness (env : RedEnv) : KExpr → KExpr → Type
| intro : forall (b : KExpr) (a : KExpr) (c : KExpr), m_star env b c → m_step env a c → m_strip_witness env b a",
            "m_strip_witness env b a packages a common reduct c with m_star env b c and m_step env a c — \
             the strip-lemma output (one leg a whole MStar block, the other a single bounded macro step). \
             Mirror of the blueprint's M_strip conclusion ∃ c, MStar b c ∧ MStep a c. Part of #2859 \
             (Increment H++, delta increment Stage 4 — Hindley-Rosen assembly).",
        )?;

        // m_star_join env a b: the macro-closure confluence output — a common reduct c
        // with m_star a c and m_star b c. Mirror of the blueprint's MStar_confluent
        // conclusion `∃ c, MStar a c ∧ MStar b c`.
        self.add_inductive(
            r"inductive m_star_join (env : RedEnv) : KExpr → KExpr → Type
| intro : forall (a : KExpr) (b : KExpr) (c : KExpr), m_star env a c → m_star env b c → m_star_join env a b",
            "m_star_join env a b packages a common reduct c with m_star env a c and m_star env b c — the \
             confluence output for the macro closure MStar. Mirror of the blueprint's MStar_confluent \
             conclusion ∃ c, MStar a c ∧ MStar b c. Part of #2859 (Increment H++, delta increment Stage 4 \
             — Hindley-Rosen assembly).",
        )?;

        // par_delta_commute_witness env a b: the β+ι/δ commutation output — a common
        // reduct c with delta_cong_star a c (a catches up on δ) and par_reduces_c_star
        // (red_rec env) b c (b catches up on β+ι). Mirror of the blueprint's `commute`
        // conclusion `∃ c, DeltaStar a c ∧ ParStar b c`.
        self.add_inductive(
            r"inductive par_delta_commute_witness (env : RedEnv) : KExpr → KExpr → Type
| intro : forall (a : KExpr) (b : KExpr) (c : KExpr), delta_cong_star env a c → par_reduces_c_star (red_rec env) b c → par_delta_commute_witness env a b",
            "par_delta_commute_witness env a b packages a common reduct c with delta_cong_star env a c (the \
             β+ι-reduct a catches up on δ) and par_reduces_c_star (red_rec env) b c (the δ-reduct b catches \
             up on β+ι) — the β+ι/δ commutation output. Mirror of the blueprint's commute conclusion \
             ∃ c, DeltaStar a c ∧ ParStar b c. Part of #2859 (Increment H++, delta increment Stage 4 — \
             Hindley-Rosen assembly).",
        )?;

        Ok(())
    }

    /// Brick C1: the two basic `m_star` combinators — `m_step_to_mstar` (a single
    /// macro step embeds into the closure) and `m_star_trans` (transitivity).
    /// Verbatim mirrors of `delta_cong_subsumes_star` / `delta_cong_star_trans`.
    fn add_hr_macro_combinators(&mut self) -> Result<(), SpecError> {
        // m_step_to_mstar: a single macro step embeds into m_star (step with refl tail).
        self.add_definition(SpecDefinition {
            name: "m_step_to_mstar".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (a : KExpr) (b : KExpr), ",
                "m_step env a b -> m_star env a b"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (a : KExpr) (b : KExpr) (h : m_step env a b) => ",
                    "m_star.step env a b b h (m_star.refl env b)"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Single macro step embeds into m_star (m_star.step with a refl tail). DerivedProved, zero axiom_deps. Part of #2859 (Increment H++, delta increment Stage 4 — Hindley-Rosen assembly).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "m_step".to_string(),
                "m_star".to_string(),
                "m_star.refl".to_string(),
                "m_star.step".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // m_star_trans: transitivity of m_star (m_star.rec on the first chain,
        // prefixing each step onto the extended tail). Mirror of delta_cong_star_trans.
        self.add_definition(SpecDefinition {
            name: "m_star_trans".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (e1 : KExpr) (e2 : KExpr) (e3 : KExpr), ",
                "m_star env e1 e2 -> m_star env e2 e3 -> m_star env e1 e3"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (e1 : KExpr) (e2 : KExpr) (e3 : KExpr) ",
                    "(h1 : m_star env e1 e2) (h2 : m_star env e2 e3) => ",
                    "m_star.rec env ",
                    "(fun (a : KExpr) (b : KExpr) (_ : m_star env a b) => ",
                    "m_star env b e3 -> m_star env a e3) ",
                    "(fun (e : KExpr) (k : m_star env e e3) => k) ",
                    "(fun (a : KExpr) (b : KExpr) (c : KExpr) ",
                    "(hstep : m_step env a b) (_htail : m_star env b c) ",
                    "(ih : m_star env c e3 -> m_star env b e3) ",
                    "(k : m_star env c e3) => ",
                    "m_star.step env a b e3 hstep (ih k)) ",
                    "e1 e2 h1 h2"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: "Transitivity of m_star (m_star.rec on the first chain, prefixing each macro step onto the extended tail). Mirror of delta_cong_star_trans. DerivedProved, zero axiom_deps. Part of #2859 (Increment H++, delta increment Stage 4 — Hindley-Rosen assembly).".to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "m_step".to_string(),
                "m_star".to_string(),
                "m_star.rec".to_string(),
                "m_star.step".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// Brick C2: `m_diamond_of` — the GENUINE single-macro-step diamond, parameterized
    /// on the three corner join-lemmas (`PCR` β+ι CR, `DCR` δ CR, `COMM` the β+ι/δ
    /// commutation) as BOUND HYPOTHESES (not axioms). A 2×2 case split on the two
    /// `m_step` derivations (`m_step.rec` twice, threading the second derivation
    /// through the first's motive to relink the shared source) dispatches each corner
    /// and packages the result as `m_step_join`. Mirror of the blueprint's `M_diamond`.
    fn add_hr_macro_diamond_of(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "m_diamond_of".to_string(),
            type_src: hr_corner_binders_type(concat!(
                "(x : KExpr) (a : KExpr) (b : KExpr), ",
                "m_step env x a -> m_step env x b -> m_step_join env a b"
            )),
            value_src: Some(m_diamond_of_proof()),
            is_axiom: false,
            description: concat!(
                "m_diamond_of — the genuine single-macro-step diamond, parameterized on the three corner ",
                "join-lemmas PCR (β+ι Church-Rosser), DCR (δ Church-Rosser) and COMM (the β+ι/δ commutation) ",
                "as BOUND HYPOTHESES (not registered axioms). A 2×2 case split on the two m_step derivations ",
                "(m_step.rec twice, the second threaded through the first's motive to relink the shared ",
                "source) dispatches each corner: (par,par) via PCR, (par,delta)/(delta,par) via COMM, ",
                "(delta,delta) via DCR, packaging m_step_join. Mirror of the blueprint's M_diamond. The ",
                "corner hypotheses keep the closure genuinely zero-axiom (the composition module discharges ",
                "them with the landed CRs + the commutation). DerivedProved, zero axiom_deps. Part of #2859 ",
                "(Increment H++, delta increment Stage 4 — Hindley-Rosen assembly)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "m_step".to_string(),
                "m_step.rec".to_string(),
                "m_step.par".to_string(),
                "m_step.delta".to_string(),
                "m_step_join".to_string(),
                "m_step_join.intro".to_string(),
                "par_reduces_c_star".to_string(),
                "delta_cong_star".to_string(),
                "par_strips_witness_c_star".to_string(),
                "par_strips_witness_c_star.rec".to_string(),
                "par_strips_witness_d_star".to_string(),
                "par_strips_witness_d_star.rec".to_string(),
                "par_delta_commute_witness".to_string(),
                "par_delta_commute_witness.rec".to_string(),
                "red_rec".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        Ok(())
    }

    /// Brick C3: `m_strip_of` — the strip lemma. Induction on the `m_star x a` leg
    /// (`m_star.rec`, motive generalized over `b`): the refl arm meets at `b`; the step
    /// arm runs `m_diamond_of` against the head macro step, then the IH against the
    /// bounded residual, re-closing with `m_star.step`. Carries the three corners.
    /// Mirror of the blueprint's `M_strip`.
    fn add_hr_macro_strip_of(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "m_strip_of".to_string(),
            type_src: hr_corner_binders_type(concat!(
                "(x : KExpr) (a : KExpr) (b : KExpr), ",
                "m_step env x b -> m_star env x a -> m_strip_witness env b a"
            )),
            value_src: Some(m_strip_of_proof()),
            is_axiom: false,
            description: concat!(
                "m_strip_of — the macro strip lemma (parameterized on the three corners PCR/DCR/COMM). ",
                "Induction on the m_star x a leg (m_star.rec, motive generalized over b): the refl arm meets ",
                "at b (m_star.refl + the bounded step); the step arm runs m_diamond_of against the head macro ",
                "step, feeds the bounded residual into the IH, and re-closes via m_star.step. Mirror of the ",
                "blueprint's M_strip. DerivedProved, zero axiom_deps. Part of #2859 (Increment H++, delta ",
                "increment Stage 4 — Hindley-Rosen assembly)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "m_step".to_string(),
                "m_star".to_string(),
                "m_star.rec".to_string(),
                "m_star.refl".to_string(),
                "m_star.step".to_string(),
                "m_step_join".to_string(),
                "m_step_join.rec".to_string(),
                "m_strip_witness".to_string(),
                "m_strip_witness.intro".to_string(),
                "m_strip_witness.rec".to_string(),
                "m_diamond_of".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        Ok(())
    }

    /// Brick C4: `mstar_confluent_of` — confluence of the macro closure `m_star`.
    /// Induction on the first `m_star x a` leg (`m_star.rec`, motive generalized over
    /// `b`): refl meets at `b`; the step arm strips the head macro step against the
    /// `b`-leg via `m_strip_of`, recurses with the IH, and re-closes with `m_star_trans`.
    /// Carries the three corners. Mirror of the blueprint's `MStar_confluent`.
    fn add_hr_mstar_confluent_of(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "mstar_confluent_of".to_string(),
            type_src: hr_corner_binders_type(concat!(
                "(x : KExpr) (a : KExpr) (b : KExpr), ",
                "m_star env x a -> m_star env x b -> m_star_join env a b"
            )),
            value_src: Some(mstar_confluent_of_proof()),
            is_axiom: false,
            description: concat!(
                "mstar_confluent_of — confluence of the macro closure m_star (parameterized on the three ",
                "corners PCR/DCR/COMM). Induction on the first m_star x a leg (m_star.rec, motive generalized ",
                "over b): refl meets at b; the step arm strips the head macro step against the b-leg via ",
                "m_strip_of, feeds the residual into the IH, and re-closes via m_star_trans. THE Hindley-Rosen ",
                "macro-confluence theorem; the composition module bridges it to par_reduces_cd_star_diamond. ",
                "Mirror of the blueprint's MStar_confluent. DerivedProved, zero axiom_deps. Part of #2859 ",
                "(Increment H++, delta increment Stage 4 — Hindley-Rosen assembly)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "m_step".to_string(),
                "m_star".to_string(),
                "m_star.rec".to_string(),
                "m_star.refl".to_string(),
                "m_star.step".to_string(),
                "m_star_join".to_string(),
                "m_star_join.intro".to_string(),
                "m_strip_witness".to_string(),
                "m_strip_witness.rec".to_string(),
                "m_strip_of".to_string(),
                "m_step_to_mstar".to_string(),
                "m_star_trans".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        Ok(())
    }
}

/// The shared `(env, PCR, DCR, COMM)` binder prefix carried by every abstract
/// Hindley-Rosen combinator. `PCR` is β+ι Church-Rosser (the
/// `par_reduces_c_star_diamond` shape over `red_rec env`), `DCR` is δ Church-Rosser
/// (the `delta_cong_star_diamond` shape), `COMM` is the β+ι/δ commutation (the
/// `par_delta_commute_star` shape). All three are BOUND HYPOTHESES, not axioms.
fn hr_corner_binders_type(tail: &str) -> String {
    format!(
        concat!(
            "forall (env : RedEnv) ",
            "(PCR : forall (s : KExpr) (u : KExpr) (v : KExpr), ",
            "par_reduces_c_star (red_rec env) s u -> par_reduces_c_star (red_rec env) s v -> ",
            "par_strips_witness_c_star (red_rec env) u v) ",
            "(DCR : forall (s : KExpr) (u : KExpr) (v : KExpr), ",
            "delta_cong_star env s u -> delta_cong_star env s v -> ",
            "par_strips_witness_d_star env u v) ",
            "(COMM : forall (s : KExpr) (u : KExpr) (v : KExpr), ",
            "par_reduces_c_star (red_rec env) s u -> delta_cong_star env s v -> ",
            "par_delta_commute_witness env u v) ",
            "{tail}"
        ),
        tail = tail,
    )
}

/// The shared `(env, PCR, DCR, COMM)` lambda prefix matching `hr_corner_binders_type`.
fn hr_corner_binders_lam() -> &'static str {
    concat!(
        "fun (env : RedEnv) ",
        "(PCR : forall (s : KExpr) (u : KExpr) (v : KExpr), ",
        "par_reduces_c_star (red_rec env) s u -> par_reduces_c_star (red_rec env) s v -> ",
        "par_strips_witness_c_star (red_rec env) u v) ",
        "(DCR : forall (s : KExpr) (u : KExpr) (v : KExpr), ",
        "delta_cong_star env s u -> delta_cong_star env s v -> ",
        "par_strips_witness_d_star env u v) ",
        "(COMM : forall (s : KExpr) (u : KExpr) (v : KExpr), ",
        "par_reduces_c_star (red_rec env) s u -> delta_cong_star env s v -> ",
        "par_delta_commute_witness env u v) "
    )
}

/// Proof term for `m_diamond_of`. `@m_step.rec` with CONCRETE indices (`x a` / `x b`)
/// — the proven witness-recursor convention: the indices are fixed by the major, so
/// each arm binds ONLY the underlying `par_reduces_c_star` / `delta_cong_star`
/// derivation (the ctor's non-index field). A 2×2 nest dispatches the four corners,
/// each landing `m_step_join env a b`.
fn m_diamond_of_proof() -> String {
    // (par,par): hpar : β+ι* x a, hbpar : β+ι* x b. PCR x a b -> par_strips_witness_c_star a b.
    let pp = concat!(
        "(@par_strips_witness_c_star.rec (red_rec env) a b ",
        "(fun (_w : par_strips_witness_c_star (red_rec env) a b) => m_step_join env a b) ",
        "(fun (c : KExpr) (la : par_reduces_c_star (red_rec env) a c) (lb : par_reduces_c_star (red_rec env) b c) => ",
        "m_step_join.intro env a b c (m_step.par env a c la) (m_step.par env b c lb)) ",
        "(PCR x a b hpar hbpar))"
    );
    // (par,delta): hpar : β+ι* x a, hbdelta : δ* x b. COMM x a b -> par_delta_commute_witness a b
    // = ∃c, δ* a c ∧ β+ι* b c. Map: delta a c, par b c.
    let pd = concat!(
        "(@par_delta_commute_witness.rec env a b ",
        "(fun (_w : par_delta_commute_witness env a b) => m_step_join env a b) ",
        "(fun (c : KExpr) (la : delta_cong_star env a c) (lb : par_reduces_c_star (red_rec env) b c) => ",
        "m_step_join.intro env a b c (m_step.delta env a c la) (m_step.par env b c lb)) ",
        "(COMM x a b hpar hbdelta))"
    );
    // par arm of ha (hpar : β+ι* x a): eliminate hb2 : m_step env x b.
    let par_arm_a = format!(
        concat!(
            "(fun (hpar : par_reduces_c_star (red_rec env) x a) => ",
            "fun (hb2 : m_step env x b) => ",
            "@m_step.rec env x b ",
            "(fun (_ : m_step env x b) => m_step_join env a b) ",
            "(fun (hbpar : par_reduces_c_star (red_rec env) x b) => {pp}) ",
            "(fun (hbdelta : delta_cong_star env x b) => {pd}) ",
            "hb2)"
        ),
        pp = pp,
        pd = pd,
    );
    // (delta,par): hbpar : β+ι* x b, hdelta : δ* x a. COMM x b a -> par_delta_commute_witness b a
    // = ∃c, δ* b c ∧ β+ι* a c. Map: par a c, delta b c.
    let dp = concat!(
        "(@par_delta_commute_witness.rec env b a ",
        "(fun (_w : par_delta_commute_witness env b a) => m_step_join env a b) ",
        "(fun (c : KExpr) (lb : delta_cong_star env b c) (la : par_reduces_c_star (red_rec env) a c) => ",
        "m_step_join.intro env a b c (m_step.par env a c la) (m_step.delta env b c lb)) ",
        "(COMM x b a hbpar hdelta))"
    );
    // (delta,delta): hdelta : δ* x a, hbdelta : δ* x b. DCR x a b -> par_strips_witness_d_star a b
    // = ∃c, δ* a c ∧ δ* b c. Map: delta a c, delta b c.
    let dd = concat!(
        "(@par_strips_witness_d_star.rec env a b ",
        "(fun (_w : par_strips_witness_d_star env a b) => m_step_join env a b) ",
        "(fun (c : KExpr) (la : delta_cong_star env a c) (lb : delta_cong_star env b c) => ",
        "m_step_join.intro env a b c (m_step.delta env a c la) (m_step.delta env b c lb)) ",
        "(DCR x a b hdelta hbdelta))"
    );
    // delta arm of ha (hdelta : δ* x a): eliminate hb2 : m_step env x b.
    let delta_arm_a = format!(
        concat!(
            "(fun (hdelta : delta_cong_star env x a) => ",
            "fun (hb2 : m_step env x b) => ",
            "@m_step.rec env x b ",
            "(fun (_ : m_step env x b) => m_step_join env a b) ",
            "(fun (hbpar : par_reduces_c_star (red_rec env) x b) => {dp}) ",
            "(fun (hbdelta : delta_cong_star env x b) => {dd}) ",
            "hb2)"
        ),
        dp = dp,
        dd = dd,
    );
    format!(
        concat!(
            "{prefix}",
            "(x : KExpr) (a : KExpr) (b : KExpr) ",
            "(ha : m_step env x a) (hb : m_step env x b) => ",
            "@m_step.rec env x a ",
            "(fun (_ : m_step env x a) => m_step env x b -> m_step_join env a b) ",
            "{par_arm_a} {delta_arm_a} ",
            "ha hb"
        ),
        prefix = hr_corner_binders_lam(),
        par_arm_a = par_arm_a,
        delta_arm_a = delta_arm_a,
    )
}

/// Proof term for `m_strip_of`. `m_star.rec` on the `x ⇒* a` leg, motive
/// `fun x a _ => forall b, m_step env x b -> m_strip_witness env b a`.
fn m_strip_of_proof() -> String {
    let motive = concat!(
        "(fun (x : KExpr) (a : KExpr) (_ : m_star env x a) => ",
        "forall (b : KExpr), m_step env x b -> m_strip_witness env b a)"
    );
    // refl arm (x = a = e): given b, hb : m_step env e b. Meet at b.
    let refl_arm = concat!(
        "(fun (e : KExpr) => ",
        "fun (b : KExpr) (hb : m_step env e b) => ",
        "m_strip_witness.intro env b e b (m_star.refl env b) hb)"
    );
    // step arm: x ⇒ x1 (hstep), x1 ⇒* a (htail), ih. Given b, hb : m_step env x b.
    // m_diamond_of hb hstep : m_step_join env b x1 = ∃d, m_step b d ∧ m_step x1 d.
    // ih d (m_step x1 d) : m_strip_witness env d a = ∃e2, m_star d e2 ∧ m_step a e2.
    let step_arm = concat!(
        "(fun (x : KExpr) (x1 : KExpr) (a : KExpr) ",
        "(hstep : m_step env x x1) (_htail : m_star env x1 a) ",
        "(ih : forall (b : KExpr), m_step env x1 b -> m_strip_witness env b a) => ",
        "fun (b : KExpr) (hb : m_step env x b) => ",
        "@m_step_join.rec env b x1 ",
        "(fun (_w : m_step_join env b x1) => m_strip_witness env b a) ",
        "(fun (d : KExpr) (l1 : m_step env b d) (l2 : m_step env x1 d) => ",
        "@m_strip_witness.rec env d a ",
        "(fun (_w : m_strip_witness env d a) => m_strip_witness env b a) ",
        "(fun (e2 : KExpr) (m1 : m_star env d e2) (m2 : m_step env a e2) => ",
        "m_strip_witness.intro env b a e2 (m_star.step env b d e2 l1 m1) m2) ",
        "(ih d l2)) ",
        "(m_diamond_of env PCR DCR COMM x b x1 hb hstep))"
    );
    format!(
        concat!(
            "{prefix}",
            "(x : KExpr) (a : KExpr) (b : KExpr) ",
            "(hb : m_step env x b) (ha : m_star env x a) => ",
            "m_star.rec env {motive} {refl_arm} {step_arm} x a ha b hb"
        ),
        prefix = hr_corner_binders_lam(),
        motive = motive,
        refl_arm = refl_arm,
        step_arm = step_arm,
    )
}

/// Proof term for `mstar_confluent_of`. `m_star.rec` on the first `x ⇒* a` leg,
/// motive `fun x a _ => forall b, m_star env x b -> m_star_join env a b`.
fn mstar_confluent_of_proof() -> String {
    let motive = concat!(
        "(fun (x : KExpr) (a : KExpr) (_ : m_star env x a) => ",
        "forall (b : KExpr), m_star env x b -> m_star_join env a b)"
    );
    // refl arm (x = a = e): given b, hb : m_star env e b. Meet at b.
    let refl_arm = concat!(
        "(fun (e : KExpr) => ",
        "fun (b : KExpr) (hb : m_star env e b) => ",
        "m_star_join.intro env e b b hb (m_star.refl env b))"
    );
    // step arm: x ⇒ x1 (hstep), x1 ⇒* a (htail), ih. Given b, hb : m_star env x b.
    // m_strip_of hstep hb : m_strip_witness env x1 b = ∃c, m_star x1 c ∧ m_step b c.
    // ih c (m_star x1 c) : m_star_join env a c = ∃d, m_star a d ∧ m_star c d.
    let step_arm = concat!(
        "(fun (x : KExpr) (x1 : KExpr) (a : KExpr) ",
        "(hstep : m_step env x x1) (_htail : m_star env x1 a) ",
        "(ih : forall (b : KExpr), m_star env x1 b -> m_star_join env a b) => ",
        "fun (b : KExpr) (hb : m_star env x b) => ",
        "@m_strip_witness.rec env x1 b ",
        "(fun (_w : m_strip_witness env x1 b) => m_star_join env a b) ",
        "(fun (c : KExpr) (s1 : m_star env x1 c) (s2 : m_step env b c) => ",
        "@m_star_join.rec env a c ",
        "(fun (_w : m_star_join env a c) => m_star_join env a b) ",
        "(fun (d : KExpr) (j1 : m_star env a d) (j2 : m_star env c d) => ",
        "m_star_join.intro env a b d j1 ",
        "(m_star_trans env b c d (m_step_to_mstar env b c s2) j2)) ",
        "(ih c s1)) ",
        "(m_strip_of env PCR DCR COMM x b x1 hstep hb))"
    );
    format!(
        concat!(
            "{prefix}",
            "(x : KExpr) (a : KExpr) (b : KExpr) ",
            "(ha : m_star env x a) (hb : m_star env x b) => ",
            "m_star.rec env {motive} {refl_arm} {step_arm} x a ha b hb"
        ),
        prefix = hr_corner_binders_lam(),
        motive = motive,
        refl_arm = refl_arm,
        step_arm = step_arm,
    )
}

#[cfg(test)]
#[path = "par_reduces_cd_hr_tests.rs"]
mod par_reduces_cd_hr_tests;

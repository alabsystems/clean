// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Increment H++ (#2859 computational-iota/delta track, DELTA INCREMENT Stage 4,
//! the HINDLEY-ROSEN redirect): `delta_cong_diamond` — the δ single-step STRONG
//! diamond — and the UNCONDITIONAL δ Church-Rosser `delta_cong_star_diamond` it
//! unlocks.
//!
//! ## What this discharges
//!
//! `par_reduces_d_conf.rs` reduced δ Church-Rosser to exactly the single honest
//! obligation `SC` (a BOUND hypothesis there): the single-step strong diamond
//!
//!   `delta_cong env a b -> delta_cong env a c -> par_strong_join_d env b c`.
//!
//! This module PROVES `SC` (as `delta_cong_diamond`, zero-axiom) and feeds it into
//! `delta_cong_star_diamond_of_strong` to land the unconditional δ CR
//! (`delta_cong_star_diamond`).
//!
//! ## Why it closes cleanly (δ orthogonality)
//!
//! δ-redexes are distinct const leaves, never root-overlapping, so the diamond is
//! by STRUCTURAL induction on the term `a` (`KExpr.rec`): the IH covers the two
//! KExpr subterms. A head-δ on an app-spine `app f x` FACTORS (via
//! `delta_step_app_inv_type`) into a head-δ on `f` — a structural subterm — so every
//! `delta_cong` step on `app f x` normalises to a step on `f` (the head-δ and the
//! `app_f` congruence) or on `x` (the `app_a` congruence). The app overlap then
//! collapses to a clean 4-case grid (f-side / x-side, joined by the
//! `par_strong_join_d` congruence lifts or a one-step `one` join). Binder nodes
//! (`lam`/`pi`) mirror it; the genuine `let_` node mirrors it with THREE slots
//! (annotation/value/body via `delta_cong.let_{t,v,b}` — a let is never itself a
//! δ-redex, so its head-δ arm is vacuous and the 3×3 grid is same-slot IH or
//! orthogonal one-step joins); const is the determinism base case
//! (`delta_step_deterministic`); sort/bvar are vacuous (a head-δ on a non-const head
//! is impossible via `delta_step_head_none_absurd_type`).
//!
//! Runs AFTER `add_par_reduces_d_conf` (so `par_strong_join_d`, its six congruence
//! lifts, `delta_step_app_inv`, and `delta_cong_star_diamond_of_strong` are all in
//! scope). Part of #2859 (Increment H++, delta increment Stage 4 — Hindley-Rosen
//! route).

use std::collections::HashSet;

use crate::spec::definition::SpecDefinition;
use crate::spec::error::SpecError;
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;

/// Inline `KExpr.rec` discriminator (large elim into Type): the named constructor
/// (one of app/lam/pi) maps to `Empty`, every other constructor to `Nat`. Constructor
/// order is sort, bvar, app, lam, pi, const, let_ — the trailing let_ minor (three
/// KExpr fields, three motive IHs) is never a discrimination target here, so it always
/// maps to `Nat`.
fn kexpr_not_inline(target_app: bool, target_lam: bool, target_pi: bool) -> String {
    let arm = |is_target: bool| if is_target { "Empty" } else { "Nat" };
    format!(
        "(KExpr.rec (fun (_ : KExpr) => Type) \
         (fun (_ : Level) => Nat) \
         (fun (_ : Nat) => Nat) \
         (fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => {app}) \
         (fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => {lam}) \
         (fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => {pi}) \
         (fun (_ : Name) (_ : ListType Level) => Nat) \
         (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) (_ : Type) => Nat) \
         (fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Type) => Nat) \
         (fun (_ : Nat) => Nat))",
        app = arm(target_app),
        lam = arm(target_lam),
        pi = arm(target_pi),
    )
}

impl Specification {
    pub(super) fn add_par_reduces_d_diamond(&mut self) -> Result<(), SpecError> {
        self.add_delta_inv_type_substrate()?;
        self.add_kexpr_bvar_const_discriminators()?;
        self.add_delta_cong_inversions()?;
        self.add_delta_cong_diamond()?;
        self.add_delta_cong_star_diamond()?;
        Ok(())
    }

    /// Brick D4: `delta_cong_star_diamond` — the UNCONDITIONAL δ Church-Rosser.
    /// Feeds the single-step strong diamond `delta_cong_diamond` (the `SC` witness)
    /// into the landed tiling brick `delta_cong_star_diamond_of_strong`: any two
    /// multi-step δ reductions `e =>* e1`, `e =>* e2` join via
    /// `par_strips_witness_d_star`. This discharges the last bound hypothesis — δ CR
    /// now holds with NO parameter, zero-axiom. The Hindley-Rosen payoff: with β+ι CR
    /// (`par_reduces_c_star_diamond`) already landed, only the β+ι/δ commutation and
    /// the Hindley-Rosen combinator remain for the 3-way β+ι+δ Church-Rosser.
    fn add_delta_cong_star_diamond(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "delta_cong_star_diamond".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (e : KExpr) (e1 : KExpr) (e2 : KExpr), ",
                "delta_cong_star env e e1 -> delta_cong_star env e e2 -> ",
                "par_strips_witness_d_star env e1 e2"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : RedEnv) (e : KExpr) (e1 : KExpr) (e2 : KExpr) ",
                    "(h1 : delta_cong_star env e e1) (h2 : delta_cong_star env e e2) => ",
                    "delta_cong_star_diamond_of_strong env (delta_cong_diamond env) e e1 e2 h1 h2"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "The UNCONDITIONAL δ Church-Rosser: delta_cong_star is confluent (any two multi-step δ reductions ",
                "join via par_strips_witness_d_star). Feeds the single-step strong diamond delta_cong_diamond (SC) ",
                "into the landed tiling delta_cong_star_diamond_of_strong, discharging the last bound hypothesis — ",
                "δ CR now holds with no parameter. The Hindley-Rosen payoff: with β+ι CR already landed, only the ",
                "β+ι/δ commutation + the Hindley-Rosen combinator remain for the 3-way β+ι+δ CR. DerivedProved, ",
                "zero axiom_deps. Part of #2859 (Increment H++, delta increment Stage 4)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "delta_cong_star".to_string(),
                "delta_cong_star_diamond_of_strong".to_string(),
                "delta_cong_diamond".to_string(),
                "par_strips_witness_d_star".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        Ok(())
    }

    /// Brick D3: `delta_cong_diamond` — THE δ single-step STRONG diamond
    /// (`SC`): `delta_cong env a b -> delta_cong env a c -> par_strong_join_d env b c`.
    /// Structural induction on the term `a` (`KExpr.rec`, motive
    /// `fun a0 => forall b0 c0, delta_cong env a0 b0 -> delta_cong env a0 c0 ->
    /// par_strong_join_d env b0 c0`):
    ///   - sort/bvar: vacuous (no live congruence arm, not const-headed).
    ///   - const: both steps are the head-δ; determinism (`delta_step_deterministic`)
    ///     gives `b0 = c0`, join `zero`.
    ///   - app/lam/pi: invert both steps (`delta_cong_<head>_inv`) into a first-slot /
    ///     second-slot reduction (the head-δ folds into the first-slot leg via the
    ///     factoring); the 4-case grid joins via the `par_strong_join_d` congruence
    ///     lifts (same-slot, using the subterm IH) or a one-step `one` join
    ///     (orthogonal slots).
    ///   - let_ (genuine 7th ctor): invert both steps (`delta_cong_let_inv`) into one
    ///     of THREE slots — a let is never itself a δ-redex, so the head-δ arm is
    ///     vacuous — and join the 3×3 grid the same way (same slot: the slot IH lifted
    ///     by `par_strong_join_d_let_{t,v,b}`; cross slots: orthogonal one-step joins).
    ///     This is the precise residual `par_reduces_d_conf.rs`
    ///     left as the bound `SC` hypothesis. δ orthogonality is what makes it close
    ///     with no developer / no termination argument.
    fn add_delta_cong_diamond(&mut self) -> Result<(), SpecError> {
        self.add_definition(SpecDefinition {
            name: "delta_cong_diamond".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (a : KExpr) (b : KExpr) (c : KExpr), ",
                "delta_cong env a b -> delta_cong env a c -> par_strong_join_d env b c"
            )
            .to_string(),
            value_src: Some(delta_cong_diamond_proof()),
            is_axiom: false,
            description: concat!(
                "The δ single-step STRONG diamond (Huet SC): delta_cong env a b and delta_cong env a c join via ",
                "par_strong_join_d (b-leg star, c-leg <= 1 step). Structural KExpr.rec on a: sort/bvar vacuous, ",
                "const is determinism (delta_step_deterministic, join zero), app/lam/pi invert both steps into a ",
                "first-/second-slot reduction (head-δ folds into the first slot via delta_step_app_inv_type) and ",
                "join the 4-case grid via the par_strong_join_d congruence lifts (same slot, subterm IH) or a ",
                "one-step `one` join (orthogonal slots); the genuine let_ node inverts both steps into one of ",
                "THREE slots (delta_cong_let_inv — a let is never itself a δ-redex) and joins the 3x3 grid the ",
                "same way (par_strong_join_d_let_{t,v,b} on the same-slot IH, orthogonal one-step joins across ",
                "slots). Discharges the SC obligation par_reduces_d_conf.rs left as ",
                "a bound hypothesis; δ orthogonality closes it with no developer/termination argument. DerivedProved, ",
                "zero axiom_deps. Part of #2859 (Increment H++, delta increment Stage 4)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "delta_cong".to_string(),
                "delta_cong.here".to_string(),
                "delta_cong.app_f".to_string(),
                "delta_cong.app_a".to_string(),
                "delta_cong.lam_t".to_string(),
                "delta_cong.lam_b".to_string(),
                "delta_cong.pi_d".to_string(),
                "delta_cong.pi_b".to_string(),
                "delta_cong_star".to_string(),
                "delta_cong_star.refl".to_string(),
                "delta_cong_subsumes_star".to_string(),
                "delta_cong.let_t".to_string(),
                "delta_cong.let_v".to_string(),
                "delta_cong.let_b".to_string(),
                "delta_cong_app_inv".to_string(),
                "delta_cong_lam_inv".to_string(),
                "delta_cong_pi_inv".to_string(),
                "delta_cong_let_inv".to_string(),
                "delta_cong_proj_inv".to_string(),
                "delta_cong_sort_absurd".to_string(),
                "delta_cong_bvar_absurd".to_string(),
                "delta_cong_lit_absurd".to_string(),
                "delta_cong_const_inv".to_string(),
                "delta_step_deterministic".to_string(),
                "red_def".to_string(),
                "par_strong_join_d".to_string(),
                "par_strong_join_d.zero".to_string(),
                "par_strong_join_d.one".to_string(),
                "par_strong_join_d_app_f".to_string(),
                "par_strong_join_d_app_a".to_string(),
                "par_strong_join_d_lam_t".to_string(),
                "par_strong_join_d_lam_b".to_string(),
                "par_strong_join_d_pi_d".to_string(),
                "par_strong_join_d_pi_b".to_string(),
                "par_strong_join_d_let_t".to_string(),
                "par_strong_join_d_let_v".to_string(),
                "par_strong_join_d_let_b".to_string(),
                "par_strong_join_d_proj".to_string(),
                "KExpr.rec".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;
        Ok(())
    }

    /// Brick D2: the per-shape `delta_cong` inversions (Type-valued, `C : Type`).
    /// Each eliminates `delta_cong env (SHAPE ..) r` via `delta_cong.rec` with a
    /// source-equation motive (`Eq lhs (SHAPE ..)`), discharging the off-shape
    /// congruence arms by KExpr no-confusion and the `here` arm either by FACTORING
    /// the head-δ (app, via `delta_step_app_inv_type`) or as VACUOUS (binder/leaf,
    /// via `delta_step_head_none_absurd_type`); `const` extracts the head-δ step.
    ///
    ///  - `delta_cong_{app,lam,pi}_inv` — two-sided CPS: a step on a compound node
    ///    reduces the first slot (left continuation) or the second (right), with the
    ///    head-δ on an app folded into the left (f-side) leg via the factoring.
    ///  - `delta_cong_let_inv` — three-sided CPS over the genuine let_ ctor: a step
    ///    on `let_ s0 s1 s2` reduces the annotation, value or body (a let is never
    ///    itself a δ-redex, so the `here` arm is vacuous); slot alignment recovered
    ///    via `let_inj_{fst,snd,thd}`, off-shape arms via `{app,lam,pi}_ne_let`.
    ///  - `delta_cong_{sort,bvar}_absurd` — a leaf has no live congruence arm and is
    ///    not const-headed, so any `delta_cong` out of it is impossible.
    ///  - `delta_cong_const_inv` — a const node reduces only by the head-δ (`here`).
    fn add_delta_cong_inversions(&mut self) -> Result<(), SpecError> {
        for target in ["app", "lam", "pi"] {
            let (name, head) = match target {
                "app" => ("delta_cong_app_inv", "KExpr.app"),
                "lam" => ("delta_cong_lam_inv", "KExpr.lam"),
                _ => ("delta_cong_pi_inv", "KExpr.pi"),
            };
            let type_src = format!(
                "forall (env : RedEnv) (s0 : KExpr) (s1 : KExpr) (r : KExpr) (C : Type), \
                 delta_cong env ({head} s0 s1) r -> \
                 (forall (b0 : KExpr), delta_cong env s0 b0 -> Eq KExpr r ({head} b0 s1) -> C) -> \
                 (forall (b1 : KExpr), delta_cong env s1 b1 -> Eq KExpr r ({head} s0 b1) -> C) -> \
                 C"
            );
            self.add_definition(SpecDefinition {
                name: name.to_string(),
                type_src,
                value_src: Some(compound_inv_proof(target)),
                is_axiom: false,
                description: format!(
                    "Two-sided CPS inversion of delta_cong at a {target} node: a single-position δ step on \
                     ({head} s0 s1) reduces the first slot (left continuation) or the second (right). \
                     delta_cong.rec with a source-equation motive; off-shape congruence arms discharged by \
                     KExpr no-confusion, the here arm {here}. The substantive case-splitter the single-step \
                     strong diamond uses on each compound node. DerivedProved, zero axiom_deps. Part of #2859 \
                     (Increment H++, delta increment Stage 4).",
                    here = if target == "app" {
                        "folded into the left (f-side) leg via delta_step_app_inv_type"
                    } else {
                        "vacuous via delta_step_head_none_absurd_type (a binder is not const-headed)"
                    },
                ),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(compound_inv_deps(target)),
                axiom_deps: HashSet::new(),
            })?;
        }

        for leaf in ["sort", "bvar"] {
            let (name, binders, term, ctor_arg) = match leaf {
                "sort" => (
                    "delta_cong_sort_absurd",
                    "(n : Level)",
                    "(KExpr.sort n)",
                    "n",
                ),
                _ => ("delta_cong_bvar_absurd", "(i : Nat)", "(KExpr.bvar i)", "i"),
            };
            let type_src = format!(
                "forall (env : RedEnv) {binders} (r : KExpr) (C : Type), \
                 delta_cong env {term} r -> C"
            );
            self.add_definition(SpecDefinition {
                name: name.to_string(),
                type_src,
                value_src: Some(leaf_absurd_proof(leaf, binders, term, ctor_arg)),
                is_axiom: false,
                description: format!(
                    "Vacuity of delta_cong at a {leaf} node: a {leaf} has no live congruence arm and is not \
                     const-headed, so delta_cong env {term} r is impossible (delivers any C). delta_cong.rec \
                     with a source-equation motive; congruence arms by KExpr no-confusion (sort/bvar_ne_*), here \
                     by delta_step_head_none_absurd_type. DerivedProved, zero axiom_deps. Part of #2859 \
                     (Increment H++, delta increment Stage 4)."
                ),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(leaf_absurd_deps(leaf)),
                axiom_deps: HashSet::new(),
            })?;
        }

        // delta_cong_let_inv: three-sided CPS inversion at a genuine let_ node. With
        // the trailing let_t/let_v/let_b congruence ctors live, a delta_cong step out
        // of (let_ s0 s1 s2) reduces EXACTLY ONE of the three slots (a let is never
        // const-headed — kapp_fn of a let is itself and kexpr_const_name is none — so
        // the head-δ `here` arm is vacuous via delta_step_head_none_absurd_type). The
        // app/lam/pi congruence arms are off-shape ({app,lam,pi}_ne_let); the three
        // live let arms recover the slot step via let_inj_{fst,snd,thd} and rebuild
        // the target equation componentwise.
        self.add_definition(SpecDefinition {
            name: "delta_cong_let_inv".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (s0 : KExpr) (s1 : KExpr) (s2 : KExpr) (r : KExpr) (C : Type), ",
                "delta_cong env (KExpr.let_ s0 s1 s2) r -> ",
                "(forall (b0 : KExpr), delta_cong env s0 b0 -> Eq KExpr r (KExpr.let_ b0 s1 s2) -> C) -> ",
                "(forall (b1 : KExpr), delta_cong env s1 b1 -> Eq KExpr r (KExpr.let_ s0 b1 s2) -> C) -> ",
                "(forall (b2 : KExpr), delta_cong env s2 b2 -> Eq KExpr r (KExpr.let_ s0 s1 b2) -> C) -> ",
                "C"
            )
            .to_string(),
            value_src: Some(let_inv_proof()),
            is_axiom: false,
            description: concat!(
                "Three-sided CPS inversion of delta_cong at a genuine let_ node: a single-position δ step on ",
                "(let_ s0 s1 s2) reduces the annotation (first continuation), the value (second) or the body ",
                "(third). delta_cong.rec with a source-equation motive; the here arm is vacuous via ",
                "delta_step_head_none_absurd_type (a let is its own spine head, kexpr_const_name none — never a ",
                "δ-redex), the app/lam/pi congruence arms are off-shape ({app,lam,pi}_ne_let), and the three live ",
                "let arms transport the slot step via let_inj_{fst,snd,thd} and rebuild the target equation by ",
                "Eq.cong/Eq.trans on the other two slots. The let-node case-splitter of the single-step strong ",
                "diamond (the let analogue of delta_cong_app_inv). DerivedProved, zero axiom_deps. Part of #2859 ",
                "(Increment H++, delta increment Stage 4)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "delta_cong".to_string(),
                "delta_cong.rec".to_string(),
                "delta_step".to_string(),
                "red_def".to_string(),
                "delta_step_head_none_absurd_type".to_string(),
                "app_ne_let".to_string(),
                "lam_ne_let".to_string(),
                "pi_ne_let".to_string(),
                "let_inj_fst".to_string(),
                "let_inj_snd".to_string(),
                "let_inj_thd".to_string(),
                "Eq.refl".to_string(),
                "Eq.subst".to_string(),
                "Eq.substType".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // delta_cong_const_inv: a const node reduces only by the head-δ (here).
        self.add_definition(SpecDefinition {
            name: "delta_cong_const_inv".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (nm : Name) (us : ListType Level) (r : KExpr) (C : Type), ",
                "delta_cong env (KExpr.const nm us) r -> ",
                "(delta_step (red_def env) (KExpr.const nm us) r -> C) -> C"
            )
            .to_string(),
            value_src: Some(delta_cong_const_inv_proof()),
            is_axiom: false,
            description: concat!(
                "Inversion of delta_cong at a const node: the only live constructor is `here`, so delta_cong env ",
                "(const nm us) r yields the head-δ step delta_step (red_def env) (const nm us) r, delivered to a ",
                "continuation. delta_cong.rec with a source-equation motive; congruence arms by KExpr no-confusion ",
                "(const_ne_*), here transports the head-δ. The determinism-case extractor for the single-step ",
                "strong diamond. DerivedProved, zero axiom_deps. Part of #2859 (Increment H++, delta increment Stage 4)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "delta_cong".to_string(),
                "delta_cong.rec".to_string(),
                "delta_step".to_string(),
                "red_def".to_string(),
                "const_ne_app".to_string(),
                "const_ne_lam".to_string(),
                "const_ne_pi".to_string(),
                // the trailing let-congruence arms are refuted by the inline let
                // discriminator (KExpr.rec + Eq.substType + Empty.rec).
                "KExpr.rec".to_string(),
                "Empty.rec".to_string(),
                "Eq.substType".to_string(),
                "Eq.symm".to_string(),
                "Eq.subst".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // delta_cong_proj_inv: single-continuation CPS inversion at a genuine proj
        // node. A delta_cong step out of (proj s i sub) reduces the (single) scrutinee
        // — a proj is never itself a δ-redex (not const-headed), so the head-δ `here`
        // arm is vacuous; the app/lam/pi/let congruence arms are off-shape
        // ({app,lam,pi,let}_ne_proj); the live proj_s arm recovers s/i/sub via
        // proj_inj_{name,idx,sub} and feeds the continuation. Part of the proj/lit rung.
        self.add_definition(SpecDefinition {
            name: "delta_cong_proj_inv".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (s : Name) (i : Nat) (sub : KExpr) (r : KExpr) (C : Type), ",
                "delta_cong env (KExpr.proj s i sub) r -> ",
                "(forall (sub' : KExpr), delta_cong env sub sub' -> Eq KExpr r (KExpr.proj s i sub') -> C) -> ",
                "C"
            )
            .to_string(),
            value_src: Some(delta_cong_proj_inv_proof()),
            is_axiom: false,
            description: concat!(
                "Single-continuation CPS inversion of delta_cong at a proj node: a single-position δ step on ",
                "(proj s i sub) reduces the scrutinee. delta_cong.rec with a source-equation motive; the here arm ",
                "is vacuous via delta_step_head_none_absurd_type (a proj is not const-headed), the app/lam/pi ",
                "congruence arms off-shape ({app,lam,pi}_ne_proj), the three let arms off-shape (let_ne_proj), and ",
                "the live proj_s arm recovers the components via proj_inj_{name,idx,sub} and rebuilds the target ",
                "equation by Eq.cong/Eq.trans. The proj-node case-splitter of the single-step strong diamond. ",
                "DerivedProved, zero axiom_deps. Part of the proj/lit fragment rung."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "delta_cong".to_string(),
                "delta_cong.rec".to_string(),
                "delta_step".to_string(),
                "red_def".to_string(),
                "delta_step_head_none_absurd_type".to_string(),
                "app_ne_proj".to_string(),
                "lam_ne_proj".to_string(),
                "pi_ne_proj".to_string(),
                "let_ne_proj".to_string(),
                "proj_inj_name".to_string(),
                "proj_inj_idx".to_string(),
                "proj_inj_sub".to_string(),
                "Eq.refl".to_string(),
                "Eq.subst".to_string(),
                "Eq.substType".to_string(),
                "Eq.cong".to_string(),
                "Eq.trans".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // delta_cong_lit_absurd: a lit node has no live congruence arm and is not
        // const-headed, so any delta_cong out of it is impossible (delivers any C).
        // Every arm is off-shape; the here arm is vacuous via
        // delta_step_head_none_absurd_type and each congruence arm is refuted by an
        // inline (lit -> Empty) discriminator. Part of the proj/lit fragment rung.
        self.add_definition(SpecDefinition {
            name: "delta_cong_lit_absurd".to_string(),
            type_src: concat!(
                "forall (env : RedEnv) (litv : Nat) (r : KExpr) (C : Type), ",
                "delta_cong env (KExpr.lit litv) r -> C"
            )
            .to_string(),
            value_src: Some(delta_cong_lit_absurd_proof()),
            is_axiom: false,
            description: concat!(
                "Vacuity of delta_cong at a lit node: a lit is a leaf with no delta_cong producer and a non-const ",
                "head, so delta_cong env (lit litv) r is impossible (delivers any C). delta_cong.rec with a ",
                "source-equation motive; the here arm is vacuous via delta_step_head_none_absurd_type and every ",
                "congruence arm is refuted by an inline (lit -> Empty) discriminator transported along the source ",
                "equation. DerivedProved, zero axiom_deps. Part of the proj/lit fragment rung."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "delta_cong".to_string(),
                "delta_cong.rec".to_string(),
                "delta_step".to_string(),
                "red_def".to_string(),
                "delta_step_head_none_absurd_type".to_string(),
                "KExpr.rec".to_string(),
                "Empty.rec".to_string(),
                "Eq.substType".to_string(),
                "Eq.subst".to_string(),
                "Eq.refl".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        Ok(())
    }

    /// Brick D1: the six missing KExpr constructor discriminators
    /// `{bvar,const}_ne_{app,lam,pi}` (Type-valued, `R : Type`). The #464
    /// discrimination work built only the sort/app/lam/pi pairs; inverting
    /// `delta_cong` at a `bvar`/`const` node needs to refute the app/lam/pi
    /// congruence arms (whose LHS shapes differ), so we add the analogous
    /// large-elimination discriminators (named constructor -> Empty, else Nat;
    /// transport `Nat.zero` along the false equation; `Empty.rec` into any sort).
    fn add_kexpr_bvar_const_discriminators(&mut self) -> Result<(), SpecError> {
        // (lhs-ctor name, lhs param binders, lhs term, head label, head term builder)
        for (lhs_name, lhs_binders, lhs_term) in [
            ("bvar", "(i : Nat)", "(KExpr.bvar i)"),
            (
                "const",
                "(nm : Name) (us : ListType Level)",
                "(KExpr.const nm us)",
            ),
        ] {
            for (head_label, head_binders, head_term, is_app, is_lam, is_pi) in [
                (
                    "app",
                    "(f : KExpr) (a : KExpr)",
                    "(KExpr.app f a)",
                    true,
                    false,
                    false,
                ),
                (
                    "lam",
                    "(A : KExpr) (b : KExpr)",
                    "(KExpr.lam A b)",
                    false,
                    true,
                    false,
                ),
                (
                    "pi",
                    "(A : KExpr) (B : KExpr)",
                    "(KExpr.pi A B)",
                    false,
                    false,
                    true,
                ),
            ] {
                let discr = kexpr_not_inline(is_app, is_lam, is_pi);
                let name = format!("{lhs_name}_ne_{head_label}");
                let type_src = format!(
                    "forall {lhs_binders} {head_binders} (R : Type), \
                     Eq KExpr {lhs_term} {head_term} -> R"
                );
                let value_src = format!(
                    "fun {lhs_binders} {head_binders} (R : Type) \
                     (h : Eq KExpr {lhs_term} {head_term}) => \
                     Empty.rec (fun (_ : Empty) => R) \
                     (Eq.substType KExpr {discr} {lhs_term} {head_term} h Nat.zero)"
                );
                self.add_definition(SpecDefinition {
                    name,
                    type_src,
                    value_src: Some(value_src),
                    is_axiom: false,
                    description: format!(
                        "{lhs_name} != {head_label} discrimination (Type-valued): large-elimination discriminator \
                         ({head_label} -> Empty, else Nat) transported along the false equation via Eq.substType + \
                         Empty.rec. The {lhs_name}-node analogue of sort_ne_{head_label}, needed to refute the \
                         {head_label} congruence arms when inverting delta_cong at a {lhs_name} node. DerivedProved, \
                         zero axiom_deps. Part of #2859 (Increment H++, delta increment Stage 4)."
                    ),
                    category: AxiomCategory::DerivedLemma,
                    proof_status: ProofStatus::DerivedProved,
                    elaborated_type: None,
                    elaborated_value: None,
                    dependencies: Some(HashSet::from([
                        "KExpr.rec".to_string(),
                        "Eq.substType".to_string(),
                        "Empty.rec".to_string(),
                    ])),
                    axiom_deps: HashSet::new(),
                })?;
            }
        }
        Ok(())
    }

    /// Brick D0: the TYPE-VALUED δ inversion substrate. `delta_reduct_some_inv` /
    /// `delta_step_app_inv` / `delta_step_head_none_absurd` are all Prop-targeted
    /// (`C : Prop`), but the single-step strong diamond builds a `par_strong_join_d`
    /// (in `Type`) from the recovered witnesses, so it needs the Type-valued
    /// siblings. Verbatim mirrors of the Prop versions, swapping
    /// `opt_bind_some_inv -> opt_bind_some_inv_type`,
    /// `delta_reduct_some_inv -> delta_reduct_some_inv_type`,
    /// `option_none_ne_some -> option_none_ne_some_type`, and `C : Prop -> C : Type`.
    fn add_delta_inv_type_substrate(&mut self) -> Result<(), SpecError> {
        // delta_reduct_some_inv_type: Type-valued sibling of delta_reduct_some_inv.
        {
            let reduct = "(apply_spine (kapp_args e) val)";
            let l3 = format!("(fun (val : KExpr) => OptionType.some KExpr {reduct})");
            let l2 =
                format!("(fun (dname : Name) => opt_bind KExpr KExpr (defval_for env dname) {l3})");
            let kont = format!(
                "(forall (dname : Name) (val : KExpr), \
                 Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name dname) -> \
                 Eq (OptionType KExpr) (defval_for env dname) (OptionType.some KExpr val) -> \
                 Eq (OptionType KExpr) (OptionType.some KExpr {reduct}) (OptionType.some KExpr e') -> \
                 C)"
            );
            let value = format!(
                "fun (env : DefEnv) (e : KExpr) (e' : KExpr) (C : Type) \
                 (h : Eq (OptionType KExpr) (delta_reduct env e) (OptionType.some KExpr e')) \
                 (k : {kont}) => \
                 opt_bind_some_inv_type Name KExpr (kexpr_const_name (kapp_fn e)) {l2} e' C h \
                 (fun (dname : Name) \
                 (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name dname)) \
                 (h1r : Eq (OptionType KExpr) ({l2} dname) (OptionType.some KExpr e')) => \
                 opt_bind_some_inv_type KExpr KExpr (defval_for env dname) {l3} e' C h1r \
                 (fun (val : KExpr) \
                 (h2 : Eq (OptionType KExpr) (defval_for env dname) (OptionType.some KExpr val)) \
                 (h2r : Eq (OptionType KExpr) ({l3} val) (OptionType.some KExpr e')) => \
                 k dname val h1 h2 h2r))"
            );
            self.add_definition(SpecDefinition {
                name: "delta_reduct_some_inv_type".to_string(),
                type_src: format!(
                    "forall (env : DefEnv) (e : KExpr) (e' : KExpr) (C : Type), \
                     Eq (OptionType KExpr) (delta_reduct env e) (OptionType.some KExpr e') -> {kont} -> C"
                ),
                value_src: Some(value),
                is_axiom: false,
                description: concat!(
                    "Type-valued sibling of delta_reduct_some_inv: CPS inversion of delta_reduct's 2-level ",
                    "opt_bind chain into a Type-valued continuation. Same proof, opt_bind_some_inv -> ",
                    "opt_bind_some_inv_type, C : Prop -> C : Type. Needed because the single-step strong diamond ",
                    "recovers the head-δ witness to build a par_strong_join_d (in Type). DerivedProved, zero ",
                    "axiom_deps. Part of #2859 (Increment H++, delta increment Stage 4)."
                )
                .to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "delta_reduct".to_string(),
                    "opt_bind_some_inv_type".to_string(),
                    "kexpr_const_name".to_string(),
                    "defval_for".to_string(),
                    "apply_spine".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        // delta_step_head_none_absurd_type: Type-valued sibling of
        // delta_step_head_none_absurd.
        self.add_definition(SpecDefinition {
            name: "delta_step_head_none_absurd_type".to_string(),
            type_src: concat!(
                "forall (env : DefEnv) (e : KExpr) (e' : KExpr) (C : Type), ",
                "Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.none Name) -> ",
                "delta_step env e e' -> C"
            )
            .to_string(),
            value_src: Some(
                concat!(
                    "fun (env : DefEnv) (e : KExpr) (e' : KExpr) (C : Type) ",
                    "(hnone : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.none Name)) ",
                    "(h : Eq (OptionType KExpr) (delta_reduct env e) (OptionType.some KExpr e')) => ",
                    "delta_reduct_some_inv_type env e e' C h ",
                    "(fun (dname : Name) (val : KExpr) ",
                    "(h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name dname)) ",
                    "(h2 : Eq (OptionType KExpr) (defval_for env dname) (OptionType.some KExpr val)) ",
                    "(h2r : Eq (OptionType KExpr) (OptionType.some KExpr (apply_spine (kapp_args e) val)) (OptionType.some KExpr e')) => ",
                    "option_none_ne_some_type Name dname C ",
                    "(Eq.trans (OptionType Name) (OptionType.none Name) (kexpr_const_name (kapp_fn e)) (OptionType.some Name dname) ",
                    "(Eq.symm (OptionType Name) (kexpr_const_name (kapp_fn e)) (OptionType.none Name) hnone) h1))"
                )
                .to_string(),
            ),
            is_axiom: false,
            description: concat!(
                "Type-valued sibling of delta_step_head_none_absurd: a head-δ on a non-const-headed term is ",
                "impossible, discharging a Type-valued goal. Inverts via delta_reduct_some_inv_type and ",
                "contradicts via option_none_ne_some_type. The vacuous-arm discharger for the binder/leaf cases ",
                "of the single-step strong diamond. DerivedProved, zero axiom_deps. Part of #2859 (Increment H++)."
            )
            .to_string(),
            category: AxiomCategory::DerivedLemma,
            proof_status: ProofStatus::DerivedProved,
            elaborated_type: None,
            elaborated_value: None,
            dependencies: Some(HashSet::from([
                "delta_reduct_some_inv_type".to_string(),
                "option_none_ne_some_type".to_string(),
                "kexpr_const_name".to_string(),
                "kapp_fn".to_string(),
                "delta_step".to_string(),
                "Eq.trans".to_string(),
                "Eq.symm".to_string(),
            ])),
            axiom_deps: HashSet::new(),
        })?;

        // delta_step_app_inv_type: Type-valued sibling of delta_step_app_inv. From
        // delta_step env (app f arg) b, recover f0 = apply_spine (kapp_args f) val
        // with delta_step env f f0 and b = app f0 arg, delivered to a Type continuation.
        {
            let afa = "(KExpr.app f arg)";
            let f0v = "(apply_spine (kapp_args f) val)";
            let f2f =
                "(fun (val : KExpr) => OptionType.some KExpr (apply_spine (kapp_args f) val))"
                    .to_string();
            let f1f = format!(
                "(fun (dname : Name) => opt_bind KExpr KExpr (defval_for env dname) {f2f})"
            );
            let h1f = format!(
                "(Eq.trans (OptionType Name) (kexpr_const_name (kapp_fn f)) (kexpr_const_name (kapp_fn {afa})) (OptionType.some Name dname) \
                 (Eq.cong KExpr (OptionType Name) (fun (H : KExpr) => kexpr_const_name H) (kapp_fn f) (kapp_fn {afa}) \
                 (Eq.symm KExpr (kapp_fn {afa}) (kapp_fn f) (kapp_fn_app f arg))) \
                 h1)"
            );
            let hf2f = format!("(Eq.refl (OptionType KExpr) (OptionType.some KExpr {f0v}))");
            let reduct_f = format!(
                "opt_bind_some_intro Name KExpr (kexpr_const_name (kapp_fn f)) {f1f} dname {f0v} {h1f} \
                 (opt_bind_some_intro KExpr KExpr (defval_for env dname) {f2f} val {f0v} h2 {hf2f})"
            );
            let beq = format!(
                "(Eq.trans KExpr b (apply_spine (kapp_args {afa}) val) (KExpr.app {f0v} arg) \
                 (Eq.symm KExpr (apply_spine (kapp_args {afa}) val) b \
                 (option_some_inj KExpr (apply_spine (kapp_args {afa}) val) b h2r)) \
                 (delta_reduct_app_eq f arg val))"
            );
            let kont = format!(
                "(fun (dname : Name) (val : KExpr) \
                 (h1 : Eq (OptionType Name) (kexpr_const_name (kapp_fn {afa})) (OptionType.some Name dname)) \
                 (h2 : Eq (OptionType KExpr) (defval_for env dname) (OptionType.some KExpr val)) \
                 (h2r : Eq (OptionType KExpr) (OptionType.some KExpr (apply_spine (kapp_args {afa}) val)) (OptionType.some KExpr b)) => \
                 k {f0v} ({reduct_f}) ({beq}))"
            );
            let value = format!(
                "fun (env : DefEnv) (f : KExpr) (arg : KExpr) (b : KExpr) (C : Type) \
                 (h : Eq (OptionType KExpr) (delta_reduct env {afa}) (OptionType.some KExpr b)) \
                 (k : forall (f0 : KExpr), delta_step env f f0 -> Eq KExpr b (KExpr.app f0 arg) -> C) => \
                 delta_reduct_some_inv_type env {afa} b C h {kont}"
            );
            self.add_definition(SpecDefinition {
                name: "delta_step_app_inv_type".to_string(),
                type_src: concat!(
                    "forall (env : DefEnv) (f : KExpr) (arg : KExpr) (b : KExpr) (C : Type), ",
                    "delta_step env (KExpr.app f arg) b -> ",
                    "(forall (f0 : KExpr), delta_step env f f0 -> Eq KExpr b (KExpr.app f0 arg) -> C) -> C"
                )
                .to_string(),
                value_src: Some(value),
                is_axiom: false,
                description: concat!(
                    "Type-valued sibling of delta_step_app_inv: a head-δ on `app f arg` factors through a head-δ ",
                    "on `f`, delivered to a Type continuation. Same proof, delta_reduct_some_inv -> ",
                    "delta_reduct_some_inv_type, C : Prop -> C : Type. The (here, app) overlap discharger for the ",
                    "single-step strong diamond (which builds a par_strong_join_d in Type). DerivedProved, zero ",
                    "axiom_deps. Part of #2859 (Increment H++, delta increment Stage 4)."
                )
                .to_string(),
                category: AxiomCategory::DerivedLemma,
                proof_status: ProofStatus::DerivedProved,
                elaborated_type: None,
                elaborated_value: None,
                dependencies: Some(HashSet::from([
                    "delta_step".to_string(),
                    "delta_reduct".to_string(),
                    "delta_reduct_some_inv_type".to_string(),
                    "delta_reduct_app_eq".to_string(),
                    "opt_bind_some_intro".to_string(),
                    "kapp_fn_app".to_string(),
                    "kexpr_const_name".to_string(),
                    "option_some_inj".to_string(),
                    "Eq.refl".to_string(),
                    "Eq.cong".to_string(),
                    "Eq.trans".to_string(),
                    "Eq.symm".to_string(),
                ])),
                axiom_deps: HashSet::new(),
            })?;
        }

        Ok(())
    }
}

/// The six two-slot `delta_cong` congruence-constructor arm specs, in
/// `delta_cong.rec` order (AFTER `here`, BEFORE the three trailing let arms of
/// `DELTA_CONG_LET_ARMS`): `(ctor_head, b0, b1, b2, premise_lhs, premise_rhs,
/// slot_a, slot_b, reduces_first_slot)`. `b0 b1 b2` are the ctor's three KExpr
/// binders; the ctor LHS is `head slot_a slot_b`; `premise_lhs/rhs` are the
/// indices of its single recursive `delta_cong` premise.
const DELTA_CONG_CONG_ARMS: [(&str, &str, &str, &str, &str, &str, &str, &str, bool); 6] = [
    ("app", "f", "f'", "a", "f", "f'", "f", "a", true),
    ("app", "f", "a", "a'", "a", "a'", "f", "a", false),
    ("lam", "t", "t'", "b", "t", "t'", "t", "b", true),
    ("lam", "t", "b", "b'", "b", "b'", "t", "b", false),
    ("pi", "d", "d'", "b", "d", "d'", "d", "b", true),
    ("pi", "d", "b", "b'", "b", "b'", "d", "b", false),
];

/// The three TRAILING `delta_cong` let-congruence arm specs (let_t/let_v/let_b,
/// appended after the six two-slot arms in `delta_cong.rec` order):
/// `(binders, premise_lhs, premise_rhs, rhs_term)`. The ctor LHS is always
/// `(KExpr.let_ t v b)`; the premise reduces exactly one of the three slots.
const DELTA_CONG_LET_ARMS: [(&str, &str, &str, &str); 3] = [
    (
        "(t : KExpr) (t' : KExpr) (v : KExpr) (b : KExpr)",
        "t",
        "t'",
        "(KExpr.let_ t' v b)",
    ),
    (
        "(t : KExpr) (v : KExpr) (v' : KExpr) (b : KExpr)",
        "v",
        "v'",
        "(KExpr.let_ t v' b)",
    ),
    (
        "(t : KExpr) (v : KExpr) (b : KExpr) (b' : KExpr)",
        "b",
        "b'",
        "(KExpr.let_ t v b')",
    ),
];

/// Inline `KExpr.rec` discriminator: `let_` maps to `Empty`, every other
/// constructor to `Nat`. Used to refute the trailing let-congruence arms when
/// inverting `delta_cong` at a sort/bvar/const node (no `sort_ne_let` /
/// `bvar_ne_let` / `const_ne_let` globals exist; the inline form keeps the
/// refutation self-contained).
fn kexpr_not_let_inline() -> String {
    "(KExpr.rec (fun (_ : KExpr) => Type) \
     (fun (_ : Level) => Nat) \
     (fun (_ : Nat) => Nat) \
     (fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) \
     (fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) \
     (fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) \
     (fun (_ : Name) (_ : ListType Level) => Nat) \
     (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) (_ : Type) => Empty) \
     (fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Type) => Nat) \
     (fun (_ : Nat) => Nat))"
        .to_string()
}

/// Inline KExpr.rec discriminator: proj -> Empty, every other ctor -> Nat.
/// Used to refute a proj-vs-leaf equation in the delta_cong leaf-absurd proof
/// (proj/lit fragment rung), mirroring kexpr_not_let_inline for the let arm.
fn kexpr_not_proj_inline() -> String {
    "(KExpr.rec (fun (_ : KExpr) => Type) \
     (fun (_ : Level) => Nat) \
     (fun (_ : Nat) => Nat) \
     (fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) \
     (fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) \
     (fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) \
     (fun (_ : Name) (_ : ListType Level) => Nat) \
     (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) (_ : Type) => Nat) \
     (fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Type) => Empty) \
     (fun (_ : Nat) => Nat))"
        .to_string()
}

fn kexpr_head(ctor_head: &str) -> String {
    format!("KExpr.{ctor_head}")
}

fn compound_inv_deps(target: &str) -> HashSet<String> {
    let mut deps = HashSet::from([
        "delta_cong".to_string(),
        "delta_cong.rec".to_string(),
        "delta_cong.here".to_string(),
        "delta_step".to_string(),
        "red_def".to_string(),
        "Eq.refl".to_string(),
        "Eq.subst".to_string(),
        "Eq.substType".to_string(),
        "Eq.cong".to_string(),
    ]);
    match target {
        "app" => {
            for d in [
                "delta_step_app_inv_type",
                "app_inj_fst",
                "app_inj_snd",
                "lam_ne_app",
                "pi_ne_app",
                "let_ne_app",
            ] {
                deps.insert(d.to_string());
            }
        }
        "lam" => {
            for d in [
                "delta_step_head_none_absurd_type",
                "lam_inj_fst",
                "lam_inj_snd",
                "app_ne_lam",
                "pi_ne_lam",
                "let_ne_lam",
            ] {
                deps.insert(d.to_string());
            }
        }
        _ => {
            for d in [
                "delta_step_head_none_absurd_type",
                "pi_inj_fst",
                "pi_inj_snd",
                "app_ne_pi",
                "lam_ne_pi",
                "let_ne_pi",
            ] {
                deps.insert(d.to_string());
            }
        }
    }
    deps
}

fn leaf_absurd_deps(leaf: &str) -> HashSet<String> {
    HashSet::from([
        "delta_cong".to_string(),
        "delta_cong.rec".to_string(),
        "delta_step".to_string(),
        "red_def".to_string(),
        "delta_step_head_none_absurd_type".to_string(),
        format!("{leaf}_ne_app"),
        format!("{leaf}_ne_lam"),
        format!("{leaf}_ne_pi"),
        // the trailing let-congruence arms are refuted by the inline let
        // discriminator (KExpr.rec + Eq.substType + Empty.rec).
        "KExpr.rec".to_string(),
        "Empty.rec".to_string(),
        "Eq.substType".to_string(),
        "Eq.refl".to_string(),
        "Eq.subst".to_string(),
        "Eq.symm".to_string(),
    ])
}

/// Proof term for `delta_cong_{app,lam,pi}_inv`. `delta_cong.rec` with a
/// source-equation motive `Eq lhs (HEAD s0 s1)`, two continuation parameters
/// threaded into the motive (so the arms see them at the case's rhs). The off-shape
/// congruence arms are discharged by KExpr no-confusion; the `here` arm factors the
/// head-δ (app) or is vacuous (binder).
fn compound_inv_proof(target: &str) -> String {
    let head = kexpr_head(target);
    let (inj_fst, inj_snd) = match target {
        "app" => ("app_inj_fst", "app_inj_snd"),
        "lam" => ("lam_inj_fst", "lam_inj_snd"),
        _ => ("pi_inj_fst", "pi_inj_snd"),
    };
    // Continuation type strings at a given rhs term.
    let contl = |rhs: &str| {
        format!("(forall (b0 : KExpr), delta_cong env s0 b0 -> Eq KExpr {rhs} ({head} b0 s1) -> C)")
    };
    let contr = |rhs: &str| {
        format!("(forall (b1 : KExpr), delta_cong env s1 b1 -> Eq KExpr {rhs} ({head} s0 b1) -> C)")
    };

    let motive = format!(
        "(fun (lhs : KExpr) (rhs : KExpr) (_d : delta_cong env lhs rhs) => \
         Eq KExpr lhs ({head} s0 s1) -> {cl} -> {cr} -> C)",
        cl = contl("rhs"),
        cr = contr("rhs"),
    );

    // here arm: factor (app) or absurd (binder). Binders e0 e1 (the here ctor's two
    // KExpr args) and the head-δ premise hstep, then (heq, kl, kr).
    let here_arm = if target == "app" {
        format!(
            "(fun (e0 : KExpr) (e1 : KExpr) (hstep : delta_step (red_def env) e0 e1) \
             (heq : Eq KExpr e0 ({head} s0 s1)) (kl : {cl}) (kr : {cr}) => \
             delta_step_app_inv_type (red_def env) s0 s1 e1 C \
             (Eq.subst KExpr (fun (z : KExpr) => delta_step (red_def env) z e1) e0 ({head} s0 s1) heq hstep) \
             (fun (f0 : KExpr) (hf0 : delta_step (red_def env) s0 f0) (heqr : Eq KExpr e1 ({head} f0 s1)) => \
             kl f0 (delta_cong.here env s0 f0 hf0) heqr))",
            cl = contl("e1"),
            cr = contr("e1"),
        )
    } else {
        format!(
            "(fun (e0 : KExpr) (e1 : KExpr) (hstep : delta_step (red_def env) e0 e1) \
             (heq : Eq KExpr e0 ({head} s0 s1)) (kl : {cl}) (kr : {cr}) => \
             delta_step_head_none_absurd_type (red_def env) ({head} s0 s1) e1 C \
             (Eq.refl (OptionType Name) (OptionType.none Name)) \
             (Eq.subst KExpr (fun (z : KExpr) => delta_step (red_def env) z e1) e0 ({head} s0 s1) heq hstep))",
            cl = contl("e1"),
            cr = contr("e1"),
        )
    };

    // The six congruence arms.
    let mut cong_arms = String::new();
    for (ctor_head, b0, b1, b2, plhs, prhs, slot_a, slot_b, reduces_first) in DELTA_CONG_CONG_ARMS {
        let cur_head = kexpr_head(ctor_head);
        let lhs_term = format!("({cur_head} {slot_a} {slot_b})");
        let rhs_term = if reduces_first {
            format!("({cur_head} {prhs} {slot_b})")
        } else {
            format!("({cur_head} {slot_a} {prhs})")
        };
        let ih_ty = format!(
            "Eq KExpr {plhs} ({head} s0 s1) -> {cl} -> {cr} -> C",
            cl = contl(prhs),
            cr = contr(prhs),
        );
        let body = if ctor_head == target {
            // Live arm: reduce the first (kl) or second (kr) slot.
            if reduces_first {
                format!(
                    "kl {prhs} \
                     (Eq.substType KExpr (fun (z : KExpr) => delta_cong env z {prhs}) {plhs} s0 \
                     ({inj_fst} {slot_a} {slot_b} s0 s1 heq) hsub) \
                     (Eq.cong KExpr KExpr (fun (z : KExpr) => {head} {prhs} z) {slot_b} s1 \
                     ({inj_snd} {slot_a} {slot_b} s0 s1 heq))"
                )
            } else {
                format!(
                    "kr {prhs} \
                     (Eq.substType KExpr (fun (z : KExpr) => delta_cong env z {prhs}) {plhs} s1 \
                     ({inj_snd} {slot_a} {slot_b} s0 s1 heq) hsub) \
                     (Eq.cong KExpr KExpr (fun (z : KExpr) => {head} z {prhs}) {slot_a} s0 \
                     ({inj_fst} {slot_a} {slot_b} s0 s1 heq))"
                )
            }
        } else {
            // Vacuous arm: {ctor_head}_ne_{target} refutes Eq (ctor_head ..) (target ..).
            format!("{ctor_head}_ne_{target} {slot_a} {slot_b} s0 s1 C heq")
        };
        cong_arms.push_str(&format!(
            "(fun ({b0} : KExpr) ({b1} : KExpr) ({b2} : KExpr) \
             (hsub : delta_cong env {plhs} {prhs}) (_ih : {ih_ty}) \
             (heq : Eq KExpr {lhs_term} ({head} s0 s1)) (kl : {cl}) (kr : {cr}) => {body}) ",
            cl = contl(&rhs_term),
            cr = contr(&rhs_term),
        ));
    }

    // The three trailing let-congruence arms: always off-shape here (a let_ never
    // equals an app/lam/pi node), refuted by let_ne_{target} directly on heq.
    for (binders, plhs, prhs, rhs_term) in DELTA_CONG_LET_ARMS {
        let ih_ty = format!(
            "Eq KExpr {plhs} ({head} s0 s1) -> {cl} -> {cr} -> C",
            cl = contl(prhs),
            cr = contr(prhs),
        );
        cong_arms.push_str(&format!(
            "(fun {binders} \
             (hsub : delta_cong env {plhs} {prhs}) (_ih : {ih_ty}) \
             (heq : Eq KExpr (KExpr.let_ t v b) ({head} s0 s1)) (kl : {cl}) (kr : {cr}) => \
             let_ne_{target} t v b s0 s1 C heq) ",
            cl = contl(rhs_term),
            cr = contr(rhs_term),
        ));
    }

    // The trailing proj_s congruence arm: always off-shape here (a proj never equals
    // an app/lam/pi node), refuted by proj_ne_{target} directly on heq.
    {
        let proj_lhs = "(KExpr.proj ps pidx psub)";
        let proj_rhs = "(KExpr.proj ps pidx psub')";
        // IH is the motive at the SCRUTINEE (psub, psub'), not at the proj node.
        let ih_ty = format!(
            "Eq KExpr psub ({head} s0 s1) -> {cl} -> {cr} -> C",
            cl = contl("psub'"),
            cr = contr("psub'"),
        );
        cong_arms.push_str(&format!(
            "(fun (ps : Name) (pidx : Nat) (psub : KExpr) (psub' : KExpr) \
             (hsub : delta_cong env psub psub') (_ih : {ih_ty}) \
             (heq : Eq KExpr {proj_lhs} ({head} s0 s1)) (kl : {cl}) (kr : {cr}) => \
             proj_ne_{target} ps pidx psub s0 s1 C heq) ",
            cl = contl(proj_rhs),
            cr = contr(proj_rhs),
        ));
    }

    format!(
        "fun (env : RedEnv) (s0 : KExpr) (s1 : KExpr) (r : KExpr) (C : Type) \
         (h : delta_cong env ({head} s0 s1) r) (kl : {cl}) (kr : {cr}) => \
         delta_cong.rec env {motive} {here_arm} {cong_arms} ({head} s0 s1) r h \
         (Eq.refl KExpr ({head} s0 s1)) kl kr",
        cl = contl("r"),
        cr = contr("r"),
    )
}

/// Proof term for `delta_cong_{sort,bvar}_absurd`. `delta_cong.rec` with a
/// source-equation motive `Eq lhs LEAF` (no continuations); every congruence arm is
/// off-shape (KExpr no-confusion via `{leaf}_ne_*`), `here` is a head-δ on a
/// non-const head (`delta_step_head_none_absurd_type`).
fn leaf_absurd_proof(leaf: &str, binders: &str, term: &str, ctor_arg: &str) -> String {
    let motive = format!(
        "(fun (lhs : KExpr) (rhs : KExpr) (_d : delta_cong env lhs rhs) => Eq KExpr lhs {term} -> C)"
    );
    let here_arm = format!(
        "(fun (e0 : KExpr) (e1 : KExpr) (hstep : delta_step (red_def env) e0 e1) \
         (heq : Eq KExpr e0 {term}) => \
         delta_step_head_none_absurd_type (red_def env) {term} e1 C \
         (Eq.refl (OptionType Name) (OptionType.none Name)) \
         (Eq.subst KExpr (fun (z : KExpr) => delta_step (red_def env) z e1) e0 {term} heq hstep))"
    );
    let mut cong_arms = String::new();
    for (ctor_head, b0, b1, b2, plhs, prhs, slot_a, slot_b, _reduces_first) in DELTA_CONG_CONG_ARMS
    {
        let cur_head = kexpr_head(ctor_head);
        let lhs_term = format!("({cur_head} {slot_a} {slot_b})");
        cong_arms.push_str(&format!(
            "(fun ({b0} : KExpr) ({b1} : KExpr) ({b2} : KExpr) \
             (hsub : delta_cong env {plhs} {prhs}) (_ih : Eq KExpr {plhs} {term} -> C) \
             (heq : Eq KExpr {lhs_term} {term}) => \
             {leaf}_ne_{ctor_head} {ctor_arg} {slot_a} {slot_b} C \
             (Eq.symm KExpr {lhs_term} {term} heq)) "
        ));
    }
    // The three trailing let-congruence arms: off-shape (a let_ never equals a
    // leaf), refuted by the inline let discriminator transported along the
    // symmetrised source equation (no sort_ne_let/bvar_ne_let global exists).
    let let_discr = kexpr_not_let_inline();
    for (lbinders, plhs, prhs, _rhs_term) in DELTA_CONG_LET_ARMS {
        cong_arms.push_str(&format!(
            "(fun {lbinders} \
             (hsub : delta_cong env {plhs} {prhs}) (_ih : Eq KExpr {plhs} {term} -> C) \
             (heq : Eq KExpr (KExpr.let_ t v b) {term}) => \
             Empty.rec (fun (_ : Empty) => C) \
             (Eq.substType KExpr {let_discr} {term} (KExpr.let_ t v b) \
             (Eq.symm KExpr (KExpr.let_ t v b) {term} heq) Nat.zero)) "
        ));
    }
    // The trailing proj_s congruence arm: off-shape (a proj never equals a leaf),
    // refuted by the inline proj discriminator transported along the symmetrised eq.
    {
        let proj_discr = kexpr_not_proj_inline();
        cong_arms.push_str(&format!(
            "(fun (ps : Name) (pidx : Nat) (psub : KExpr) (psub' : KExpr) \
             (hsub : delta_cong env psub psub') (_ih : Eq KExpr psub {term} -> C) \
             (heq : Eq KExpr (KExpr.proj ps pidx psub) {term}) => \
             Empty.rec (fun (_ : Empty) => C) \
             (Eq.substType KExpr {proj_discr} {term} (KExpr.proj ps pidx psub) \
             (Eq.symm KExpr (KExpr.proj ps pidx psub) {term} heq) Nat.zero)) "
        ));
    }
    format!(
        "fun (env : RedEnv) {binders} (r : KExpr) (C : Type) (h : delta_cong env {term} r) => \
         delta_cong.rec env {motive} {here_arm} {cong_arms} {term} r h (Eq.refl KExpr {term})"
    )
}

/// Proof term for `delta_cong_let_inv`. `delta_cong.rec` with a source-equation
/// motive `Eq lhs (let_ s0 s1 s2)` threading THREE continuation parameters (one per
/// slot). The `here` arm is a head-δ on a non-const head (a let is its own spine
/// head), vacuous via `delta_step_head_none_absurd_type`; the six app/lam/pi
/// congruence arms are off-shape (`{app,lam,pi}_ne_let`, source-args-first); the
/// three live let arms transport the slot step along `let_inj_{fst,snd,thd}` and
/// rebuild the target equation on the other two slots by `Eq.cong`/`Eq.trans`.
fn let_inv_proof() -> String {
    let src = "(KExpr.let_ s0 s1 s2)";
    // Continuation type strings at a given rhs term.
    let contt = |rhs: &str| {
        format!(
            "(forall (b0 : KExpr), delta_cong env s0 b0 -> Eq KExpr {rhs} (KExpr.let_ b0 s1 s2) -> C)"
        )
    };
    let contv = |rhs: &str| {
        format!(
            "(forall (b1 : KExpr), delta_cong env s1 b1 -> Eq KExpr {rhs} (KExpr.let_ s0 b1 s2) -> C)"
        )
    };
    let contb = |rhs: &str| {
        format!(
            "(forall (b2 : KExpr), delta_cong env s2 b2 -> Eq KExpr {rhs} (KExpr.let_ s0 s1 b2) -> C)"
        )
    };

    let motive = format!(
        "(fun (lhs : KExpr) (rhs : KExpr) (_d : delta_cong env lhs rhs) => \
         Eq KExpr lhs {src} -> {ct} -> {cv} -> {cb} -> C)",
        ct = contt("rhs"),
        cv = contv("rhs"),
        cb = contb("rhs"),
    );

    // here arm: a let_ is never a δ-redex (own spine head, kexpr_const_name none).
    let here_arm = format!(
        "(fun (e0 : KExpr) (e1 : KExpr) (hstep : delta_step (red_def env) e0 e1) \
         (heq : Eq KExpr e0 {src}) (kt : {ct}) (kv : {cv}) (kb : {cb}) => \
         delta_step_head_none_absurd_type (red_def env) {src} e1 C \
         (Eq.refl (OptionType Name) (OptionType.none Name)) \
         (Eq.subst KExpr (fun (z : KExpr) => delta_step (red_def env) z e1) e0 {src} heq hstep))",
        ct = contt("e1"),
        cv = contv("e1"),
        cb = contb("e1"),
    );

    // The six app/lam/pi congruence arms: off-shape ({ctor}_ne_let on heq directly).
    let mut cong_arms = String::new();
    for (ctor_head, b0, b1, b2, plhs, prhs, slot_a, slot_b, reduces_first) in DELTA_CONG_CONG_ARMS {
        let cur_head = kexpr_head(ctor_head);
        let lhs_term = format!("({cur_head} {slot_a} {slot_b})");
        let rhs_term = if reduces_first {
            format!("({cur_head} {prhs} {slot_b})")
        } else {
            format!("({cur_head} {slot_a} {prhs})")
        };
        let ih_ty = format!(
            "Eq KExpr {plhs} {src} -> {ct} -> {cv} -> {cb} -> C",
            ct = contt(prhs),
            cv = contv(prhs),
            cb = contb(prhs),
        );
        cong_arms.push_str(&format!(
            "(fun ({b0} : KExpr) ({b1} : KExpr) ({b2} : KExpr) \
             (hsub : delta_cong env {plhs} {prhs}) (_ih : {ih_ty}) \
             (heq : Eq KExpr {lhs_term} {src}) (kt : {ct}) (kv : {cv}) (kb : {cb}) => \
             {ctor_head}_ne_let {slot_a} {slot_b} s0 s1 s2 C heq) ",
            ct = contt(&rhs_term),
            cv = contv(&rhs_term),
            cb = contb(&rhs_term),
        ));
    }

    // The three live let arms. Each recovers the slot alignment from heq via
    // let_inj_{fst,snd,thd}, transports the slot step, and rebuilds the target
    // equation on the two untouched slots (Eq.trans of two Eq.cong steps).
    let inj = |which: &str| format!("(let_inj_{which} t v b s0 s1 s2 heq)");
    let let_arm_bodies = [
        // let_t (binders t t' v b; rhs (let_ t' v b)): slot 0 varies.
        format!(
            "kt t' \
             (Eq.substType KExpr (fun (z : KExpr) => delta_cong env z t') t s0 {ifst} hsub) \
             (Eq.trans KExpr (KExpr.let_ t' v b) (KExpr.let_ t' s1 b) (KExpr.let_ t' s1 s2) \
             (Eq.cong KExpr KExpr (fun (z : KExpr) => KExpr.let_ t' z b) v s1 {isnd}) \
             (Eq.cong KExpr KExpr (fun (z : KExpr) => KExpr.let_ t' s1 z) b s2 {ithd}))",
            ifst = inj("fst"),
            isnd = inj("snd"),
            ithd = inj("thd"),
        ),
        // let_v (binders t v v' b; rhs (let_ t v' b)): slot 1 varies.
        format!(
            "kv v' \
             (Eq.substType KExpr (fun (z : KExpr) => delta_cong env z v') v s1 {isnd} hsub) \
             (Eq.trans KExpr (KExpr.let_ t v' b) (KExpr.let_ s0 v' b) (KExpr.let_ s0 v' s2) \
             (Eq.cong KExpr KExpr (fun (z : KExpr) => KExpr.let_ z v' b) t s0 {ifst}) \
             (Eq.cong KExpr KExpr (fun (z : KExpr) => KExpr.let_ s0 v' z) b s2 {ithd}))",
            ifst = inj("fst"),
            isnd = inj("snd"),
            ithd = inj("thd"),
        ),
        // let_b (binders t v b b'; rhs (let_ t v b')): slot 2 varies.
        format!(
            "kb b' \
             (Eq.substType KExpr (fun (z : KExpr) => delta_cong env z b') b s2 {ithd} hsub) \
             (Eq.trans KExpr (KExpr.let_ t v b') (KExpr.let_ s0 v b') (KExpr.let_ s0 s1 b') \
             (Eq.cong KExpr KExpr (fun (z : KExpr) => KExpr.let_ z v b') t s0 {ifst}) \
             (Eq.cong KExpr KExpr (fun (z : KExpr) => KExpr.let_ s0 z b') v s1 {isnd}))",
            ifst = inj("fst"),
            isnd = inj("snd"),
            ithd = inj("thd"),
        ),
    ];
    for ((lbinders, plhs, prhs, rhs_term), body) in
        DELTA_CONG_LET_ARMS.iter().zip(let_arm_bodies.iter())
    {
        let ih_ty = format!(
            "Eq KExpr {plhs} {src} -> {ct} -> {cv} -> {cb} -> C",
            ct = contt(prhs),
            cv = contv(prhs),
            cb = contb(prhs),
        );
        cong_arms.push_str(&format!(
            "(fun {lbinders} \
             (hsub : delta_cong env {plhs} {prhs}) (_ih : {ih_ty}) \
             (heq : Eq KExpr (KExpr.let_ t v b) {src}) (kt : {ct}) (kv : {cv}) (kb : {cb}) => \
             {body}) ",
            ct = contt(rhs_term),
            cv = contv(rhs_term),
            cb = contb(rhs_term),
        ));
    }

    // The trailing proj_s congruence arm: off-shape (a proj never equals a let_),
    // refuted by proj_ne_let directly on heq.
    {
        let proj_rhs = "(KExpr.proj ps pidx psub')";
        let ih_ty = format!(
            "Eq KExpr psub {src} -> {ct} -> {cv} -> {cb} -> C",
            ct = contt("psub'"),
            cv = contv("psub'"),
            cb = contb("psub'"),
        );
        cong_arms.push_str(&format!(
            "(fun (ps : Name) (pidx : Nat) (psub : KExpr) (psub' : KExpr) \
             (hsub : delta_cong env psub psub') (_ih : {ih_ty}) \
             (heq : Eq KExpr (KExpr.proj ps pidx psub) {src}) (kt : {ct}) (kv : {cv}) (kb : {cb}) => \
             proj_ne_let ps pidx psub s0 s1 s2 C heq) ",
            ct = contt(proj_rhs),
            cv = contv(proj_rhs),
            cb = contb(proj_rhs),
        ));
    }

    format!(
        "fun (env : RedEnv) (s0 : KExpr) (s1 : KExpr) (s2 : KExpr) (r : KExpr) (C : Type) \
         (h : delta_cong env {src} r) (kt : {ct}) (kv : {cv}) (kb : {cb}) => \
         delta_cong.rec env {motive} {here_arm} {cong_arms} {src} r h \
         (Eq.refl KExpr {src}) kt kv kb",
        ct = contt("r"),
        cv = contv("r"),
        cb = contb("r"),
    )
}

/// Proof term for `delta_cong_const_inv`. `delta_cong.rec` with a source-equation
/// motive `Eq lhs (const nm us)` threading a `delta_step ... -> C` continuation; the
/// congruence arms are off-shape (`const_ne_*`), `here` transports the head-δ.
fn delta_cong_const_inv_proof() -> String {
    let cst = "(KExpr.const nm us)";
    let kty = |rhs: &str| format!("(delta_step (red_def env) {cst} {rhs} -> C)");
    let motive = format!(
        "(fun (lhs : KExpr) (rhs : KExpr) (_d : delta_cong env lhs rhs) => \
         Eq KExpr lhs {cst} -> {k} -> C)",
        k = kty("rhs"),
    );
    let here_arm = format!(
        "(fun (e0 : KExpr) (e1 : KExpr) (hstep : delta_step (red_def env) e0 e1) \
         (heq : Eq KExpr e0 {cst}) (k : {k}) => \
         k (Eq.subst KExpr (fun (z : KExpr) => delta_step (red_def env) z e1) e0 {cst} heq hstep))",
        k = kty("e1"),
    );
    let mut cong_arms = String::new();
    for (ctor_head, b0, b1, b2, plhs, prhs, slot_a, slot_b, reduces_first) in DELTA_CONG_CONG_ARMS {
        let cur_head = kexpr_head(ctor_head);
        let lhs_term = format!("({cur_head} {slot_a} {slot_b})");
        let rhs_term = if reduces_first {
            format!("({cur_head} {prhs} {slot_b})")
        } else {
            format!("({cur_head} {slot_a} {prhs})")
        };
        cong_arms.push_str(&format!(
            "(fun ({b0} : KExpr) ({b1} : KExpr) ({b2} : KExpr) \
             (hsub : delta_cong env {plhs} {prhs}) \
             (_ih : Eq KExpr {plhs} {cst} -> {ihk} -> C) \
             (heq : Eq KExpr {lhs_term} {cst}) (k : {curk}) => \
             const_ne_{ctor_head} nm us {slot_a} {slot_b} C (Eq.symm KExpr {lhs_term} {cst} heq)) ",
            ihk = kty(prhs),
            curk = kty(&rhs_term),
        ));
    }
    // The three trailing let-congruence arms: off-shape (a let_ never equals a
    // const), refuted by the inline let discriminator (no const_ne_let global).
    let let_discr = kexpr_not_let_inline();
    for (lbinders, plhs, prhs, rhs_term) in DELTA_CONG_LET_ARMS {
        cong_arms.push_str(&format!(
            "(fun {lbinders} \
             (hsub : delta_cong env {plhs} {prhs}) \
             (_ih : Eq KExpr {plhs} {cst} -> {ihk} -> C) \
             (heq : Eq KExpr (KExpr.let_ t v b) {cst}) (k : {curk}) => \
             Empty.rec (fun (_ : Empty) => C) \
             (Eq.substType KExpr {let_discr} {cst} (KExpr.let_ t v b) \
             (Eq.symm KExpr (KExpr.let_ t v b) {cst} heq) Nat.zero)) ",
            ihk = kty(prhs),
            curk = kty(rhs_term),
        ));
    }
    // The trailing proj_s congruence arm: off-shape (a proj never equals a const),
    // refuted by the inline proj discriminator on the symmetrised eq.
    {
        let proj_discr = kexpr_not_proj_inline();
        cong_arms.push_str(&format!(
            "(fun (ps : Name) (pidx : Nat) (psub : KExpr) (psub' : KExpr) \
             (hsub : delta_cong env psub psub') \
             (_ih : Eq KExpr psub {cst} -> {ihk} -> C) \
             (heq : Eq KExpr (KExpr.proj ps pidx psub) {cst}) (k : {curk}) => \
             Empty.rec (fun (_ : Empty) => C) \
             (Eq.substType KExpr {proj_discr} {cst} (KExpr.proj ps pidx psub) \
             (Eq.symm KExpr (KExpr.proj ps pidx psub) {cst} heq) Nat.zero)) ",
            ihk = kty("psub'"),
            curk = kty("(KExpr.proj ps pidx psub')"),
        ));
    }
    format!(
        "fun (env : RedEnv) (nm : Name) (us : ListType Level) (r : KExpr) (C : Type) \
         (h : delta_cong env {cst} r) (k : {k}) => \
         delta_cong.rec env {motive} {here_arm} {cong_arms} {cst} r h (Eq.refl KExpr {cst}) k",
        k = kty("r"),
    )
}

/// Inline `KExpr.rec` discriminator: `lit` maps to `Empty`, every other
/// constructor to `Nat`. Refutes the off-shape arms in `delta_cong_lit_absurd`
/// (a lit is never the source of any delta_cong constructor). Part of the
/// proj/lit fragment rung; mirrors `kexpr_not_proj_inline` for the lit slot.
fn kexpr_not_lit_inline() -> String {
    "(KExpr.rec (fun (_ : KExpr) => Type) \
     (fun (_ : Level) => Nat) \
     (fun (_ : Nat) => Nat) \
     (fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) \
     (fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) \
     (fun (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) => Nat) \
     (fun (_ : Name) (_ : ListType Level) => Nat) \
     (fun (_ : KExpr) (_ : KExpr) (_ : KExpr) (_ : Type) (_ : Type) (_ : Type) => Nat) \
     (fun (_ : Name) (_ : Nat) (_ : KExpr) (_ : Type) => Nat) \
     (fun (_ : Nat) => Empty))"
        .to_string()
}

/// Proof term for `delta_cong_proj_inv`: single-continuation inversion of a
/// `delta_cong` step out of a `proj s i sub` node. `delta_cong.rec` with a
/// source-equation motive; the `here` arm is vacuous (proj is not const-headed),
/// the six app/lam/pi and three let congruence arms are off-shape
/// (`{app,lam,pi,let}_ne_proj`), and the live `proj_s` arm recovers the components
/// via `proj_inj_{name,idx,sub}` and feeds the single continuation.
fn delta_cong_proj_inv_proof() -> String {
    let src = "(KExpr.proj s i sub)";
    let cont = |rhs: &str| {
        format!(
            "(forall (sub' : KExpr), delta_cong env sub sub' -> Eq KExpr {rhs} (KExpr.proj s i sub') -> C)"
        )
    };
    let motive = format!(
        "(fun (lhs : KExpr) (rhs : KExpr) (_d : delta_cong env lhs rhs) => \
         Eq KExpr lhs {src} -> {k} -> C)",
        k = cont("rhs"),
    );
    let here_arm = format!(
        "(fun (e0 : KExpr) (e1 : KExpr) (hstep : delta_step (red_def env) e0 e1) \
         (heq : Eq KExpr e0 {src}) (k : {k}) => \
         delta_step_head_none_absurd_type (red_def env) {src} e1 C \
         (Eq.refl (OptionType Name) (OptionType.none Name)) \
         (Eq.subst KExpr (fun (z : KExpr) => delta_step (red_def env) z e1) e0 {src} heq hstep))",
        k = cont("e1"),
    );
    let mut cong_arms = String::new();
    // The six app/lam/pi congruence arms: off-shape ({app,lam,pi}_ne_proj on heq).
    for (ctor_head, b0, b1, b2, plhs, prhs, slot_a, slot_b, reduces_first) in DELTA_CONG_CONG_ARMS {
        let cur_head = kexpr_head(ctor_head);
        let lhs_term = format!("({cur_head} {slot_a} {slot_b})");
        let rhs_term = if reduces_first {
            format!("({cur_head} {prhs} {slot_b})")
        } else {
            format!("({cur_head} {slot_a} {prhs})")
        };
        let ih_ty = format!("Eq KExpr {plhs} {src} -> {ihk} -> C", ihk = cont(prhs));
        cong_arms.push_str(&format!(
            "(fun ({b0} : KExpr) ({b1} : KExpr) ({b2} : KExpr) \
             (hsub : delta_cong env {plhs} {prhs}) (_ih : {ih_ty}) \
             (heq : Eq KExpr {lhs_term} {src}) (k : {curk}) => \
             {ctor_head}_ne_proj {slot_a} {slot_b} s i sub C heq) ",
            curk = cont(&rhs_term),
        ));
    }
    // The three trailing let-congruence arms: off-shape (let_ne_proj on heq).
    for (binders, plhs, prhs, rhs_term) in DELTA_CONG_LET_ARMS {
        let ih_ty = format!("Eq KExpr {plhs} {src} -> {ihk} -> C", ihk = cont(prhs));
        cong_arms.push_str(&format!(
            "(fun {binders} \
             (hsub : delta_cong env {plhs} {prhs}) (_ih : {ih_ty}) \
             (heq : Eq KExpr (KExpr.let_ t v b) {src}) (k : {curk}) => \
             let_ne_proj t v b s i sub C heq) ",
            curk = cont(rhs_term),
        ));
    }
    // The live proj_s arm: recover s/i/sub via proj_inj_{name,idx,sub}, feed k.
    {
        let ih_ty = format!("Eq KExpr psub {src} -> {ihk} -> C", ihk = cont("psub'"));
        cong_arms.push_str(&format!(
            "(fun (ps : Name) (pidx : Nat) (psub : KExpr) (psub' : KExpr) \
             (hsub : delta_cong env psub psub') (_ih : {ih_ty}) \
             (heq : Eq KExpr (KExpr.proj ps pidx psub) {src}) (k : {curk}) => \
             k psub' \
             (Eq.substType KExpr (fun (z : KExpr) => delta_cong env z psub') psub sub \
             (proj_inj_sub ps pidx psub s i sub heq) hsub) \
             (Eq.trans KExpr (KExpr.proj ps pidx psub') (KExpr.proj s pidx psub') (KExpr.proj s i psub') \
             (Eq.cong Name KExpr (fun (z : Name) => KExpr.proj z pidx psub') ps s \
             (proj_inj_name ps pidx psub s i sub heq)) \
             (Eq.cong Nat KExpr (fun (z : Nat) => KExpr.proj s z psub') pidx i \
             (proj_inj_idx ps pidx psub s i sub heq)))) ",
            curk = cont("(KExpr.proj ps pidx psub')"),
        ));
    }
    format!(
        "fun (env : RedEnv) (s : Name) (i : Nat) (sub : KExpr) (r : KExpr) (C : Type) \
         (h : delta_cong env {src} r) (k : {k}) => \
         delta_cong.rec env {motive} {here_arm} {cong_arms} {src} r h \
         (Eq.refl KExpr {src}) k",
        k = cont("r"),
    )
}

/// Proof term for `delta_cong_lit_absurd`. `delta_cong.rec` with a source-equation
/// motive `Eq lhs (lit litv)` (no continuations); the `here` arm is a head-δ on a
/// non-const head (vacuous via `delta_step_head_none_absurd_type`); every
/// congruence arm is off-shape, refuted by the inline `lit -> Empty` discriminator
/// (`kexpr_not_lit_inline`) transported along the source equation.
fn delta_cong_lit_absurd_proof() -> String {
    let term = "(KExpr.lit litv)";
    let lit_discr = kexpr_not_lit_inline();
    let motive = format!(
        "(fun (lhs : KExpr) (rhs : KExpr) (_d : delta_cong env lhs rhs) => Eq KExpr lhs {term} -> C)"
    );
    let here_arm = format!(
        "(fun (e0 : KExpr) (e1 : KExpr) (hstep : delta_step (red_def env) e0 e1) \
         (heq : Eq KExpr e0 {term}) => \
         delta_step_head_none_absurd_type (red_def env) {term} e1 C \
         (Eq.refl (OptionType Name) (OptionType.none Name)) \
         (Eq.subst KExpr (fun (z : KExpr) => delta_step (red_def env) z e1) e0 {term} heq hstep))"
    );
    let mut cong_arms = String::new();
    // The six app/lam/pi congruence arms: off-shape (source is not a lit), refuted by
    // the inline lit discriminator applied to the source (D(source)=Nat -> Nat.zero,
    // D(lit litv)=Empty; heq : Eq source (lit litv), no symm needed).
    for (ctor_head, b0, b1, b2, plhs, prhs, slot_a, slot_b, _reduces_first) in DELTA_CONG_CONG_ARMS
    {
        let cur_head = kexpr_head(ctor_head);
        let lhs_term = format!("({cur_head} {slot_a} {slot_b})");
        cong_arms.push_str(&format!(
            "(fun ({b0} : KExpr) ({b1} : KExpr) ({b2} : KExpr) \
             (hsub : delta_cong env {plhs} {prhs}) (_ih : Eq KExpr {plhs} {term} -> C) \
             (heq : Eq KExpr {lhs_term} {term}) => \
             Empty.rec (fun (_ : Empty) => C) \
             (Eq.substType KExpr {lit_discr} {lhs_term} {term} heq Nat.zero)) "
        ));
    }
    // The three trailing let-congruence arms: off-shape, same inline refutation.
    for (lbinders, plhs, prhs, _rhs_term) in DELTA_CONG_LET_ARMS {
        cong_arms.push_str(&format!(
            "(fun {lbinders} \
             (hsub : delta_cong env {plhs} {prhs}) (_ih : Eq KExpr {plhs} {term} -> C) \
             (heq : Eq KExpr (KExpr.let_ t v b) {term}) => \
             Empty.rec (fun (_ : Empty) => C) \
             (Eq.substType KExpr {lit_discr} (KExpr.let_ t v b) {term} heq Nat.zero)) "
        ));
    }
    // The trailing proj_s congruence arm: off-shape, same inline refutation.
    cong_arms.push_str(&format!(
        "(fun (ps : Name) (pidx : Nat) (psub : KExpr) (psub' : KExpr) \
         (hsub : delta_cong env psub psub') (_ih : Eq KExpr psub {term} -> C) \
         (heq : Eq KExpr (KExpr.proj ps pidx psub) {term}) => \
         Empty.rec (fun (_ : Empty) => C) \
         (Eq.substType KExpr {lit_discr} (KExpr.proj ps pidx psub) {term} heq Nat.zero)) "
    ));
    format!(
        "fun (env : RedEnv) (litv : Nat) (r : KExpr) (C : Type) (h : delta_cong env {term} r) => \
         delta_cong.rec env {motive} {here_arm} {cong_arms} {term} r h (Eq.refl KExpr {term})"
    )
}

/// The compound (app/lam/pi) case of `delta_cong_diamond`: invert both steps into a
/// first-slot / second-slot reduction and join the 4-case grid. `s0`/`s1` are the
/// two subterms (in scope from the `KExpr.rec` arm), `ih0`/`ih1` their IHs, `b0`/`c0`
/// the two reducts of `HEAD s0 s1`.
fn compound_diamond_case(target: &str) -> String {
    let head = kexpr_head(target);
    let inv = format!("delta_cong_{target}_inv");
    let (lift_l, lift_r, cong_l, cong_r) = match target {
        "app" => (
            "par_strong_join_d_app_f",
            "par_strong_join_d_app_a",
            "delta_cong.app_f",
            "delta_cong.app_a",
        ),
        "lam" => (
            "par_strong_join_d_lam_t",
            "par_strong_join_d_lam_b",
            "delta_cong.lam_t",
            "delta_cong.lam_b",
        ),
        _ => (
            "par_strong_join_d_pi_d",
            "par_strong_join_d_pi_b",
            "delta_cong.pi_d",
            "delta_cong.pi_b",
        ),
    };
    let p_of = |a0: &str| {
        format!(
            "(forall (bi : KExpr) (ci : KExpr), delta_cong env {a0} bi -> delta_cong env {a0} ci -> par_strong_join_d env bi ci)"
        )
    };
    // transport PSJ env bcanon ccanon to PSJ env b0 c0 (eb : Eq b0 bcanon, ec : Eq c0 ccanon).
    let transport = |bcanon: &str, ccanon: &str, eb: &str, ec: &str, join: &str| {
        format!(
            "(Eq.substType KExpr (fun (z : KExpr) => par_strong_join_d env z c0) {bcanon} b0 \
             (Eq.symm KExpr b0 {bcanon} {eb}) \
             (Eq.substType KExpr (fun (z : KExpr) => par_strong_join_d env {bcanon} z) {ccanon} c0 \
             (Eq.symm KExpr c0 {ccanon} {ec}) {join}))"
        )
    };

    // (L,L): both reduced first slot; join via lift_l on ih0.
    let ll = transport(
        &format!("({head} bL s1)"),
        &format!("({head} cL s1)"),
        "ebL",
        "ecL",
        &format!("({lift_l} env bL cL s1 (ih0 bL cL hbL hcL))"),
    );
    // (L,R): b reduced first slot, c reduced second; orthogonal one-join at HEAD bL cR.
    let lr_join = format!(
        "(par_strong_join_d.one env ({head} bL s1) ({head} s0 cR) ({head} bL cR) \
         (delta_cong_subsumes_star env ({head} bL s1) ({head} bL cR) ({cong_r} env bL s1 cR hcR)) \
         ({cong_l} env s0 bL cR hbL))"
    );
    let lr = transport(
        &format!("({head} bL s1)"),
        &format!("({head} s0 cR)"),
        "ebL",
        "ecR",
        &lr_join,
    );
    // (R,L): b reduced second slot, c reduced first; orthogonal one-join at HEAD cL bR.
    let rl_join = format!(
        "(par_strong_join_d.one env ({head} s0 bR) ({head} cL s1) ({head} cL bR) \
         (delta_cong_subsumes_star env ({head} s0 bR) ({head} cL bR) ({cong_l} env s0 cL bR hcL)) \
         ({cong_r} env cL s1 bR hbR))"
    );
    let rl = transport(
        &format!("({head} s0 bR)"),
        &format!("({head} cL s1)"),
        "ebR",
        "ecL",
        &rl_join,
    );
    // (R,R): both reduced second slot; join via lift_r on ih1.
    let rr = transport(
        &format!("({head} s0 bR)"),
        &format!("({head} s0 cR)"),
        "ebR",
        "ecR",
        &format!("({lift_r} env bR cR s0 (ih1 bR cR hbR hcR))"),
    );

    let psj_bc = "(par_strong_join_d env b0 c0)";
    format!(
        "(fun (s0 : KExpr) (s1 : KExpr) (ih0 : {p0}) (ih1 : {p1}) => \
         fun (b0 : KExpr) (c0 : KExpr) \
         (hb : delta_cong env ({head} s0 s1) b0) (hc : delta_cong env ({head} s0 s1) c0) => \
         {inv} env s0 s1 b0 {psj_bc} hb \
         (fun (bL : KExpr) (hbL : delta_cong env s0 bL) (ebL : Eq KExpr b0 ({head} bL s1)) => \
         {inv} env s0 s1 c0 {psj_bc} hc \
         (fun (cL : KExpr) (hcL : delta_cong env s0 cL) (ecL : Eq KExpr c0 ({head} cL s1)) => {ll}) \
         (fun (cR : KExpr) (hcR : delta_cong env s1 cR) (ecR : Eq KExpr c0 ({head} s0 cR)) => {lr})) \
         (fun (bR : KExpr) (hbR : delta_cong env s1 bR) (ebR : Eq KExpr b0 ({head} s0 bR)) => \
         {inv} env s0 s1 c0 {psj_bc} hc \
         (fun (cL : KExpr) (hcL : delta_cong env s0 cL) (ecL : Eq KExpr c0 ({head} cL s1)) => {rl}) \
         (fun (cR : KExpr) (hcR : delta_cong env s1 cR) (ecR : Eq KExpr c0 ({head} s0 cR)) => {rr})))",
        p0 = p_of("s0"),
        p1 = p_of("s1"),
    )
}

/// The let_ case of `delta_cong_diamond`: invert both steps into one of the THREE
/// slots (annotation/value/body) via `delta_cong_let_inv` and join the 3×3 grid.
/// `s0`/`s1`/`s2` are the three subterms (in scope from the `KExpr.rec` let_ arm),
/// `ih0`/`ih1`/`ih2` their IHs, `b0`/`c0` the two reducts of `let_ s0 s1 s2`.
/// Same-slot cells recurse through the slot IH lifted by the matching
/// `par_strong_join_d_let_{t,v,b}` congruence; cross-slot cells are orthogonal —
/// a one-step `one` join at the term with BOTH slots reduced, each leg firing the
/// other side's step through the matching `delta_cong.let_{t,v,b}` congruence
/// (exactly the app/lam/pi (L,R)/(R,L) mechanism, now over a 3-slot node).
fn let_diamond_case() -> String {
    let p_of = |a0: &str| {
        format!(
            "(forall (bi : KExpr) (ci : KExpr), delta_cong env {a0} bi -> delta_cong env {a0} ci -> par_strong_join_d env bi ci)"
        )
    };
    // transport PSJ env bcanon ccanon to PSJ env b0 c0 (eb : Eq b0 bcanon, ec : Eq c0 ccanon).
    let transport = |bcanon: &str, ccanon: &str, eb: &str, ec: &str, join: &str| {
        format!(
            "(Eq.substType KExpr (fun (z : KExpr) => par_strong_join_d env z c0) {bcanon} b0 \
             (Eq.symm KExpr b0 {bcanon} {eb}) \
             (Eq.substType KExpr (fun (z : KExpr) => par_strong_join_d env {bcanon} z) {ccanon} c0 \
             (Eq.symm KExpr c0 {ccanon} {ec}) {join}))"
        )
    };
    // Orthogonal one-step join: b-leg B ⇒ M (subsumed to star), c-leg C ⇒ M (single).
    let one_join = |bterm: &str, cterm: &str, mterm: &str, bstep: &str, cstep: &str| {
        format!(
            "(par_strong_join_d.one env {bterm} {cterm} {mterm} \
             (delta_cong_subsumes_star env {bterm} {mterm} {bstep}) \
             {cstep})"
        )
    };

    // Same-slot cells: lift the slot IH through the matching let congruence.
    let tt = transport(
        "(KExpr.let_ bT s1 s2)",
        "(KExpr.let_ cT s1 s2)",
        "ebT",
        "ecT",
        "(par_strong_join_d_let_t env bT cT s1 s2 (ih0 bT cT hbT hcT))",
    );
    let vv = transport(
        "(KExpr.let_ s0 bV s2)",
        "(KExpr.let_ s0 cV s2)",
        "ebV",
        "ecV",
        "(par_strong_join_d_let_v env bV cV s0 s2 (ih1 bV cV hbV hcV))",
    );
    let bb = transport(
        "(KExpr.let_ s0 s1 bB)",
        "(KExpr.let_ s0 s1 cB)",
        "ebB",
        "ecB",
        "(par_strong_join_d_let_b env bB cB s0 s1 (ih2 bB cB hbB hcB))",
    );

    // Cross-slot cells: orthogonal — meet at the let with BOTH slots reduced.
    let tv = transport(
        "(KExpr.let_ bT s1 s2)",
        "(KExpr.let_ s0 cV s2)",
        "ebT",
        "ecV",
        &one_join(
            "(KExpr.let_ bT s1 s2)",
            "(KExpr.let_ s0 cV s2)",
            "(KExpr.let_ bT cV s2)",
            "(delta_cong.let_v env bT s1 cV s2 hcV)",
            "(delta_cong.let_t env s0 bT cV s2 hbT)",
        ),
    );
    let tb = transport(
        "(KExpr.let_ bT s1 s2)",
        "(KExpr.let_ s0 s1 cB)",
        "ebT",
        "ecB",
        &one_join(
            "(KExpr.let_ bT s1 s2)",
            "(KExpr.let_ s0 s1 cB)",
            "(KExpr.let_ bT s1 cB)",
            "(delta_cong.let_b env bT s1 s2 cB hcB)",
            "(delta_cong.let_t env s0 bT s1 cB hbT)",
        ),
    );
    let vt = transport(
        "(KExpr.let_ s0 bV s2)",
        "(KExpr.let_ cT s1 s2)",
        "ebV",
        "ecT",
        &one_join(
            "(KExpr.let_ s0 bV s2)",
            "(KExpr.let_ cT s1 s2)",
            "(KExpr.let_ cT bV s2)",
            "(delta_cong.let_t env s0 cT bV s2 hcT)",
            "(delta_cong.let_v env cT s1 bV s2 hbV)",
        ),
    );
    let vb = transport(
        "(KExpr.let_ s0 bV s2)",
        "(KExpr.let_ s0 s1 cB)",
        "ebV",
        "ecB",
        &one_join(
            "(KExpr.let_ s0 bV s2)",
            "(KExpr.let_ s0 s1 cB)",
            "(KExpr.let_ s0 bV cB)",
            "(delta_cong.let_b env s0 bV s2 cB hcB)",
            "(delta_cong.let_v env s0 s1 bV cB hbV)",
        ),
    );
    let bt = transport(
        "(KExpr.let_ s0 s1 bB)",
        "(KExpr.let_ cT s1 s2)",
        "ebB",
        "ecT",
        &one_join(
            "(KExpr.let_ s0 s1 bB)",
            "(KExpr.let_ cT s1 s2)",
            "(KExpr.let_ cT s1 bB)",
            "(delta_cong.let_t env s0 cT s1 bB hcT)",
            "(delta_cong.let_b env cT s1 s2 bB hbB)",
        ),
    );
    let bv = transport(
        "(KExpr.let_ s0 s1 bB)",
        "(KExpr.let_ s0 cV s2)",
        "ebB",
        "ecV",
        &one_join(
            "(KExpr.let_ s0 s1 bB)",
            "(KExpr.let_ s0 cV s2)",
            "(KExpr.let_ s0 cV bB)",
            "(delta_cong.let_v env s0 s1 cV bB hcV)",
            "(delta_cong.let_b env s0 cV s2 bB hbB)",
        ),
    );

    let psj_bc = "(par_strong_join_d env b0 c0)";
    format!(
        "(fun (s0 : KExpr) (s1 : KExpr) (s2 : KExpr) (ih0 : {p0}) (ih1 : {p1}) (ih2 : {p2}) => \
         fun (b0 : KExpr) (c0 : KExpr) \
         (hb : delta_cong env (KExpr.let_ s0 s1 s2) b0) (hc : delta_cong env (KExpr.let_ s0 s1 s2) c0) => \
         delta_cong_let_inv env s0 s1 s2 b0 {psj_bc} hb \
         (fun (bT : KExpr) (hbT : delta_cong env s0 bT) (ebT : Eq KExpr b0 (KExpr.let_ bT s1 s2)) => \
         delta_cong_let_inv env s0 s1 s2 c0 {psj_bc} hc \
         (fun (cT : KExpr) (hcT : delta_cong env s0 cT) (ecT : Eq KExpr c0 (KExpr.let_ cT s1 s2)) => {tt}) \
         (fun (cV : KExpr) (hcV : delta_cong env s1 cV) (ecV : Eq KExpr c0 (KExpr.let_ s0 cV s2)) => {tv}) \
         (fun (cB : KExpr) (hcB : delta_cong env s2 cB) (ecB : Eq KExpr c0 (KExpr.let_ s0 s1 cB)) => {tb})) \
         (fun (bV : KExpr) (hbV : delta_cong env s1 bV) (ebV : Eq KExpr b0 (KExpr.let_ s0 bV s2)) => \
         delta_cong_let_inv env s0 s1 s2 c0 {psj_bc} hc \
         (fun (cT : KExpr) (hcT : delta_cong env s0 cT) (ecT : Eq KExpr c0 (KExpr.let_ cT s1 s2)) => {vt}) \
         (fun (cV : KExpr) (hcV : delta_cong env s1 cV) (ecV : Eq KExpr c0 (KExpr.let_ s0 cV s2)) => {vv}) \
         (fun (cB : KExpr) (hcB : delta_cong env s2 cB) (ecB : Eq KExpr c0 (KExpr.let_ s0 s1 cB)) => {vb})) \
         (fun (bB : KExpr) (hbB : delta_cong env s2 bB) (ebB : Eq KExpr b0 (KExpr.let_ s0 s1 bB)) => \
         delta_cong_let_inv env s0 s1 s2 c0 {psj_bc} hc \
         (fun (cT : KExpr) (hcT : delta_cong env s0 cT) (ecT : Eq KExpr c0 (KExpr.let_ cT s1 s2)) => {bt}) \
         (fun (cV : KExpr) (hcV : delta_cong env s1 cV) (ecV : Eq KExpr c0 (KExpr.let_ s0 cV s2)) => {bv}) \
         (fun (cB : KExpr) (hcB : delta_cong env s2 cB) (ecB : Eq KExpr c0 (KExpr.let_ s0 s1 cB)) => {bb})))",
        p0 = p_of("s0"),
        p1 = p_of("s1"),
        p2 = p_of("s2"),
    )
}

/// Proof term for `delta_cong_diamond` — structural `KExpr.rec` on the term.
fn delta_cong_diamond_proof() -> String {
    let motive = concat!(
        "(fun (a0 : KExpr) => forall (b0 : KExpr) (c0 : KExpr), ",
        "delta_cong env a0 b0 -> delta_cong env a0 c0 -> par_strong_join_d env b0 c0)"
    );
    let sort_case = "(fun (n : Level) => fun (b0 : KExpr) (c0 : KExpr) \
         (hb : delta_cong env (KExpr.sort n) b0) (hc : delta_cong env (KExpr.sort n) c0) => \
         delta_cong_sort_absurd env n b0 (par_strong_join_d env b0 c0) hb)";
    let bvar_case = "(fun (i : Nat) => fun (b0 : KExpr) (c0 : KExpr) \
         (hb : delta_cong env (KExpr.bvar i) b0) (hc : delta_cong env (KExpr.bvar i) c0) => \
         delta_cong_bvar_absurd env i b0 (par_strong_join_d env b0 c0) hb)";
    let const_case = "(fun (nm : Name) (us : ListType Level) => fun (b0 : KExpr) (c0 : KExpr) \
         (hb : delta_cong env (KExpr.const nm us) b0) (hc : delta_cong env (KExpr.const nm us) c0) => \
         delta_cong_const_inv env nm us b0 (par_strong_join_d env b0 c0) hb \
         (fun (sb : delta_step (red_def env) (KExpr.const nm us) b0) => \
         delta_cong_const_inv env nm us c0 (par_strong_join_d env b0 c0) hc \
         (fun (sc : delta_step (red_def env) (KExpr.const nm us) c0) => \
         par_strong_join_d.zero env b0 c0 \
         (Eq.substType KExpr (fun (z : KExpr) => delta_cong_star env b0 z) b0 c0 \
         (delta_step_deterministic (red_def env) (KExpr.const nm us) b0 c0 sb sc) \
         (delta_cong_star.refl env b0)))))";
    let app_case = compound_diamond_case("app");
    let lam_case = compound_diamond_case("lam");
    let pi_case = compound_diamond_case("pi");
    // let_ case: the genuine three-slot overlap grid — invert both steps into one
    // of the three slots via delta_cong_let_inv, then join the 3×3 grid (same slot:
    // the slot IH lifted by par_strong_join_d_let_{t,v,b}; cross slots: orthogonal
    // one-step joins at the doubly-reduced let). Trailing minor of the 7-ctor KExpr.rec.
    let let_case = let_diamond_case();
    // proj_ (genuine 8th ctor): a SINGLE-hole diamond. Invert both steps into the
    // scrutinee via delta_cong_proj_inv, join via the scrutinee IH lifted by
    // par_strong_join_d_proj, transport back along the two reduct equations.
    let proj_case = "(fun (s : Name) (i : Nat) (sub : KExpr) (ihsub : forall (bi : KExpr) (ci : KExpr), delta_cong env sub bi -> delta_cong env sub ci -> par_strong_join_d env bi ci) => fun (b0 : KExpr) (c0 : KExpr) (hb : delta_cong env (KExpr.proj s i sub) b0) (hc : delta_cong env (KExpr.proj s i sub) c0) => delta_cong_proj_inv env s i sub b0 (par_strong_join_d env b0 c0) hb (fun (bS : KExpr) (hbS : delta_cong env sub bS) (ebS : Eq KExpr b0 (KExpr.proj s i bS)) => delta_cong_proj_inv env s i sub c0 (par_strong_join_d env b0 c0) hc (fun (cS : KExpr) (hcS : delta_cong env sub cS) (ecS : Eq KExpr c0 (KExpr.proj s i cS)) => Eq.substType KExpr (fun (z : KExpr) => par_strong_join_d env z c0) (KExpr.proj s i bS) b0 (Eq.symm KExpr b0 (KExpr.proj s i bS) ebS) (Eq.substType KExpr (fun (z : KExpr) => par_strong_join_d env (KExpr.proj s i bS) z) (KExpr.proj s i cS) c0 (Eq.symm KExpr c0 (KExpr.proj s i cS) ecS) (par_strong_join_d_proj env s i bS cS (ihsub bS cS hbS hcS))))))";
    // lit (genuine 9th ctor): a leaf — no live congruence arm, not const-headed, so
    // both delta_cong steps are impossible (delta_cong_lit_absurd delivers the join).
    let lit_case = "(fun (v : Nat) => fun (b0 : KExpr) (c0 : KExpr) \
         (hb : delta_cong env (KExpr.lit v) b0) (hc : delta_cong env (KExpr.lit v) c0) => \
         delta_cong_lit_absurd env v b0 (par_strong_join_d env b0 c0) hb)";
    format!(
        "fun (env : RedEnv) (a : KExpr) (b : KExpr) (c : KExpr) \
         (hab : delta_cong env a b) (hac : delta_cong env a c) => \
         KExpr.rec {motive} {sort_case} {bvar_case} {app_case} {lam_case} {pi_case} {const_case} {let_case} \
         {proj_case} {lit_case} \
         a b c hab hac"
    )
}

#[cfg(test)]
#[path = "par_reduces_d_diamond_tests.rs"]
mod par_reduces_d_diamond_tests;

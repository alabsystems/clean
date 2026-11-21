// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **`redTypeStep` AT THE WHNF-INDEXED CANDIDATE — the starvation question.**
//!
//! `candmodel_whnf_probe.rs` measures thirteen `RedW` results and its header
//! records that no refutation stands against this family. This module asks the
//! one question that could produce one, because it is the law that killed the
//! PREVIOUS family:
//!
//! ```text
//! redTypeStep : forall (T T2 e : KExpr), whnf_step T T2 ->
//!               AndType (Red T e -> Red T2 e) (Red T2 e -> Red T e)
//! ```
//!
//! **Why the step-indexed refutation cannot simply be replayed.**
//! `redstep_redTypeStep_refuted` works by moving the type's HEAD across the
//! `pi` boundary with one beta step — `app (lam _ (pi _ _)) _` is `app`-headed,
//! its contractum is `pi`-headed, and `RedN` reads the head constructor. `RedW`
//! reads `whnf_fuel_red_wh3`, which REDUCES first, so both sides of that step
//! present the same `pi` and the route closes. That is what this family was
//! built for.
//!
//! **The residual vulnerability is FUEL, not the head.** `RedW (succ n)` reads
//! the whnf at fuel `succ n` exactly. A redex needs strictly more fuel than its
//! contractum, so at the fuel where the redex STARVES and the contractum does
//! not, the two clauses are not merely different — they are different in KIND:
//!
//! * starved (`none`) selects `whnf_acc e0`, the blind clause;
//! * reduced to a `pi` selects `AndType (whnf_acc e0) (pointwise)`.
//!
//! `redTypeStep`'s forward direction then carries an INHABITED thing to an
//! EMPTY one at `e := OMEGA_LAM`, exactly as in the step-indexed case and for a
//! completely different reason.
//!
//! **This module does not assume that fuel accounting.** Nothing in the tree
//! bridges `whnf_step` to the wh3 loop — a scan for a definition whose head
//! mentions both returns zero — so the fuel at which a redex starves is
//! measured here rather than predicted. The census arms state BOTH readings of
//! each term (`_blind` and `_pi`) and exactly one of each pair can elaborate;
//! the refutation arms are written for all three candidate pairs and are
//! SELF-SELECTING, since each one typechecks only if its redex starves at fuel
//! one AND its contractum reduces to the `pi` there.
//!
//! So a mixed pass/fail report is the intended output, not a broken run.
//!
//! **MEASURED 2026-09-19, and the fuel is harsher than predicted.** Every redex
//! starves at fuel one — not merely the long chains, but `R1`, a SINGLE beta
//! step (`redw_tsc_r1_blind` elaborates and `redw_tsc_r1_pi` does not, for all
//! three of `R1`/`R2`/`R3`), while the already-whnf `pi` computes there (the
//! control). So the starvation boundary sits between a redex and its contractum
//! at the very first index, and exactly ONE refutation arm can land: `r1`,
//! whose contractum IS the `pi`. It does
//! (`redw_typestep_refuted_at_index_one_r1`). `r2`/`r3` fail on a rigid-head
//! mismatch because their contracta are themselves blind — they are the
//! controls that make `r1` mean something, and all three outcomes are pinned.
//!
//! **Scope, and it is now MEASURED rather than hedged.** The refutation is at a
//! FIXED INDEX, i.e. at the family `RedW n`. It does NOT lift to `RedWStep`,
//! which quantifies the index — and that is not a hope but a result:
//! `candmodel_whnf_typestep_quantified_sources` proves BOTH directions of the
//! law at `RedWStep` for the SAME pair of types that refutes it at index one.
//! So the law fails at every fixed index and holds at the quantified family,
//! for identical terms. `RedWStep`'s index is load-bearing, the same reading
//! `redw_pi_elim`'s deliberate index BUMP (`hf (Nat.succ n)`) already forces.
//! **Never cite the refutation against this candidate.**
//!
//! Everything here is SCRATCH and unwired.

use crate::spec::Specification;

impl Specification {
    /// The starvation census and the three self-selecting refutation arms.
    ///
    /// `R1`, `R2`, `R3` are beta chains of length one, two and three onto the
    /// same `pi (sort 0) (sort 0)`. Each is CLOSED, so `instantiate` is the
    /// identity on it and the contractum of `app (lam s0 X) s0` is `X` on the
    /// nose — which is what lets `beta_reduces.beta` be written without a
    /// transport, the same spelling `redstep_redTypeStep_refuted` uses.
    #[cfg(test)]
    pub(super) fn candmodel_whnf_typestep_census_sources() -> Vec<(String, String)> {
        let s0 = "(KExpr.sort Level.zero)";
        let pi = format!("(KExpr.pi {s0} {s0})");
        let r1 = format!("(KExpr.app (KExpr.lam {s0} {pi}) {s0})");
        let r2 = format!("(KExpr.app (KExpr.lam {s0} {r1}) {s0})");
        let r3 = format!("(KExpr.app (KExpr.lam {s0} {r2}) {s0})");
        let one = "(Nat.succ Nat.zero)";
        let om = "(KExpr.lam (KExpr.bvar Nat.zero) \
                  (KExpr.app (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero)))";

        // The `pi` clause at index one, with `ih = RedW Nat.zero`.
        let pi_clause = |e: &str| {
            format!(
                "(AndType (whnf_acc {e}) \
                 (forall (x : KExpr), RedW Nat.zero {s0} x -> \
                 RedW Nat.zero {s0} (KExpr.app {e} x)))"
            )
        };
        // One census pair: the term read as blind, and as the `pi` clause.
        let census = |tag: &str, term: &str| {
            vec![
                (
                    format!("redw_tsc_{tag}_blind"),
                    format!(
                        "def redw_tsc_{tag}_blind (e : KExpr) : \
                         @Eq Type (RedW {one} {term} e) (whnf_acc e) := \
                         @Eq.refl Type (whnf_acc e)"
                    ),
                ),
                (
                    format!("redw_tsc_{tag}_pi"),
                    format!(
                        "def redw_tsc_{tag}_pi (e : KExpr) : \
                         @Eq Type (RedW {one} {term} e) {clause} := \
                         @Eq.refl Type {clause}",
                        clause = pi_clause("e"),
                    ),
                ),
            ]
        };
        // One refutation arm: `whnf_step redex contractum`, where the redex is
        // `app (lam s0 contractum) s0`. Elaborates only if the redex starves at
        // fuel one (so `whnf_acc_omega_lam_uncond` is accepted at
        // `RedW 1 redex OMEGA`) and the contractum does not (so the result is
        // the `AndType` that `AndType.right` projects).
        let refute = |tag: &str, redex: &str, contractum: &str| {
            (
                format!("redw_typestep_refuted_at_index_one_{tag}"),
                format!(
                    "def redw_typestep_refuted_at_index_one_{tag} (C : Type) \
                     (law : forall (T : KExpr) (T2 : KExpr) (e : KExpr), \
                     whnf_step T T2 -> \
                     AndType (RedW {one} T e -> RedW {one} T2 e) \
                     (RedW {one} T2 e -> RedW {one} T e)) : C := \
                     self_app_loop_not_whnf_acc {om} omega_self_step C \
                     (AndType.right (whnf_acc {om}) {pw} \
                     (AndType.left (RedW {one} {redex} {om} -> RedW {one} {contractum} {om}) \
                     (RedW {one} {contractum} {om} -> RedW {one} {redex} {om}) \
                     (law {redex} {contractum} {om} \
                     (whnf_step.beta {redex} {contractum} \
                     (beta_reduces.beta {s0} {contractum} {s0}))) \
                     whnf_acc_omega_lam_uncond) \
                     {om} whnf_acc_omega_lam_uncond)",
                    pw = format_args!(
                        "(forall (x : KExpr), RedW Nat.zero {s0} x -> \
                         RedW Nat.zero {s0} (KExpr.app {om} x))"
                    ),
                ),
            )
        };

        let mut out: Vec<(String, String)> = Vec::new();
        // CONTROL. `redw_pi_clause_reached` already proves this shape; if it
        // fails here the census machinery is broken and nothing else is a
        // statement about fuel.
        out.push((
            "redw_tsc_control_pi_at_index_one".to_string(),
            format!(
                "def redw_tsc_control_pi_at_index_one (e : KExpr) : \
                 @Eq Type (RedW {one} {pi} e) {clause} := @Eq.refl Type {clause}",
                clause = pi_clause("e"),
            ),
        ));
        out.extend(census("r1", &r1));
        out.extend(census("r2", &r2));
        out.extend(census("r3", &r3));
        out.push(refute("r1", &r1, &pi));
        out.push(refute("r2", &r2, &r1));
        out.push(refute("r3", &r3, &r2));
        out
    }

    /// **The same pair at the INDEX-QUANTIFIED family.** The refutation above is
    /// at `RedW n`; every `CandModel` law is actually stated at `RedWStep`, and
    /// the two need not agree. This asks whether the starvation disagreement is
    /// ABSORBED by `forall n`.
    ///
    /// The route needs no general fuel lemma, which is why it is attemptable at
    /// all. Two computations carry it, and both are stated as their own arms so
    /// a failure says which:
    ///
    /// * **`sort 0` is INDEX-FREE.** `wh3` of a sort returns it at any fuel and
    ///   `RedWInner`'s `sort` arm is bare `whnf_acc`, so `RedW k (sort 0) y` is
    ///   `whnf_acc y` at every `k` — including a VARIABLE `k`, via `Nat.rec`.
    ///   That is what dissolves the index mismatch: the clause's `ih` appears
    ///   only at the domain and the codomain, and here both are `sort 0`.
    /// * **`R1` reaches the `pi` at `succ (succ m)` for VARIABLE `m`.** The loop
    ///   is a `Nat.rec` on fuel, so two `succ`s unfold two layers — one beta
    ///   step to the `pi`, then the already-whnf answer — without knowing `m`.
    ///
    /// Given those, `RedWStep R1 e` and `RedWStep PI e` are both equivalent to
    /// `whnf_acc e` AND `forall x, whnf_acc x -> whnf_acc (app e x)`: the first
    /// two conjuncts of `R1` are blind and the rest agree with `PI`'s. The
    /// backward direction needs a two-level `Nat.rec` because `RedW (succ m) R1`
    /// is NOT uniform in `m` — blind at `m = 0`, the `pi` clause after.
    #[cfg(test)]
    pub(super) fn candmodel_whnf_typestep_quantified_sources() -> Vec<(String, String)> {
        let s0 = "(KExpr.sort Level.zero)";
        let pi = format!("(KExpr.pi {s0} {s0})");
        let r1 = format!("(KExpr.app (KExpr.lam {s0} {pi}) {s0})");
        let one = "(Nat.succ Nat.zero)";
        let two = "(Nat.succ (Nat.succ Nat.zero))";
        // The `pi` clause at a VARIABLE index `j`, as `RedWInner` states it.
        let clause_at = |j: &str, e: &str| {
            format!(
                "(AndType (whnf_acc {e}) \
                 (forall (x : KExpr), RedW {j} {s0} x -> \
                 RedW {j} {s0} (KExpr.app {e} x)))"
            )
        };
        // `h 2`'s pointwise half, the concrete rung the transports route through.
        let pw1 =
            format!("(forall (y : KExpr), RedW {one} {s0} y -> RedW {one} {s0} (KExpr.app e y))");
        // `whnf_acc (app e x)` out of `h`, via the index-one rung.
        let acc_app = format!(
            "(redw_sort_to_acc {one} (KExpr.app e x) \
             (AndType.right (whnf_acc e) {pw1} (h {two}) x \
             (redw_acc_to_sort {one} x (redw_sort_to_acc j x hx))))"
        );
        // The `pi` clause built at index `j`, from `h`.
        let build = format!(
            "(@AndType.intro (whnf_acc e) \
             (forall (x : KExpr), RedW j {s0} x -> RedW j {s0} (KExpr.app e x)) \
             (h Nat.zero) \
             (fun (x : KExpr) (hx : RedW j {s0} x) => \
             redw_acc_to_sort j (KExpr.app e x) {acc_app}))"
        );
        // Same, with `j` instantiated to a concrete spelling.
        let build_at = |j: &str| {
            build
                .replace(" j ", &format!(" {j} "))
                .replace("RedW j", &format!("RedW {j}"))
        };
        vec![
            (
                "redw_sort_to_acc".to_string(),
                format!(
                    "def redw_sort_to_acc : forall (k : Nat) (y : KExpr), \
                     RedW k {s0} y -> whnf_acc y := \
                     @Nat.rec (fun (kk : Nat) => forall (y : KExpr), \
                     RedW kk {s0} y -> whnf_acc y) \
                     (fun (y : KExpr) (h0 : RedW Nat.zero {s0} y) => h0) \
                     (fun (n : Nat) (_ih : forall (y : KExpr), \
                     RedW n {s0} y -> whnf_acc y) => \
                     fun (y : KExpr) (hs : RedW (Nat.succ n) {s0} y) => hs)"
                ),
            ),
            (
                "redw_acc_to_sort".to_string(),
                format!(
                    "def redw_acc_to_sort : forall (k : Nat) (y : KExpr), \
                     whnf_acc y -> RedW k {s0} y := \
                     @Nat.rec (fun (kk : Nat) => forall (y : KExpr), \
                     whnf_acc y -> RedW kk {s0} y) \
                     (fun (y : KExpr) (h0 : whnf_acc y) => h0) \
                     (fun (n : Nat) (_ih : forall (y : KExpr), \
                     whnf_acc y -> RedW n {s0} y) => \
                     fun (y : KExpr) (ha : whnf_acc y) => ha)"
                ),
            ),
            (
                // The decisive computation: two `succ`s unfold the fuel loop
                // twice at a VARIABLE index, so R1 reaches the `pi` there.
                "redw_r1_reaches_pi_at_succ_succ".to_string(),
                format!(
                    "def redw_r1_reaches_pi_at_succ_succ (m : Nat) (e : KExpr) : \
                     @Eq Type (RedW (Nat.succ (Nat.succ m)) {r1} e) {cl} := \
                     @Eq.refl Type {cl}",
                    cl = clause_at("(Nat.succ m)", "e"),
                ),
            ),
            (
                "redw_typestep_fwd_at_redwstep_for_the_refuting_pair".to_string(),
                format!(
                    "def redw_typestep_fwd_at_redwstep_for_the_refuting_pair \
                     (e : KExpr) (h : RedWStep {r1} e) : RedWStep {pi} e := \
                     fun (n : Nat) => \
                     @Nat.rec (fun (k : Nat) => RedW k {pi} e) (h Nat.zero) \
                     (fun (j : Nat) (_ih : RedW j {pi} e) => {b}) n",
                    b = build,
                ),
            ),
            (
                "redw_typestep_bwd_at_redwstep_for_the_refuting_pair".to_string(),
                format!(
                    "def redw_typestep_bwd_at_redwstep_for_the_refuting_pair \
                     (e : KExpr) (h : RedWStep {pi} e) : RedWStep {r1} e := \
                     fun (n : Nat) => \
                     @Nat.rec (fun (k : Nat) => RedW k {r1} e) (h Nat.zero) \
                     (fun (m : Nat) (_ih : RedW m {r1} e) => \
                     @Nat.rec (fun (j : Nat) => RedW (Nat.succ j) {r1} e) \
                     (h Nat.zero) \
                     (fun (m2 : Nat) (_ih2 : RedW (Nat.succ m2) {r1} e) => {b2}) m) n",
                    b2 = build_at("(Nat.succ m2)"),
                ),
            ),
        ]
    }
}

#[cfg(test)]
#[path = "candmodel_whnf_typestep_tests.rs"]
mod tests;

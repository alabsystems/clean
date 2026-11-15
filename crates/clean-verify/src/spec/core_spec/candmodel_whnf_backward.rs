// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The six remaining BACKWARD laws at the whnf-indexed candidate, at a
//! non-`pi` type.** `redLet` and the four `redRec*` were the last block of
//! `CandModel` fields never measured at `RedW`.
//!
//! **Why this is one line per law and not six proofs.** The previous increment
//! proved `redw_acc_to_sort : forall k y, whnf_acc y -> RedW k (sort 0) y` —
//! `sort 0` is index-free at `RedW`, because `RedWInner`'s `sort` arm is bare
//! `whnf_acc` and `wh3` returns a sort at any fuel. So ANY type-blind result
//! `whnf_acc <redex>` lifts to `RedWStep (sort 0) <redex>` by
//! `fun n => redw_acc_to_sort n <redex> <blind proof>`, with nothing to prove in
//! between. All five type-blind lemmas already exist and are reused verbatim:
//! `redlet_blind_exact` (`beta_subst_congr.rs`) and the four `*_blind_inert`
//! (`redrecgen_probe.rs`).
//!
//! **This is the cheap half, and saying so is the point.** §3l measures that
//! the seven backward laws do NOT share a propagation lemma — `redAbstraction`
//! and `redLet` have no `T` binder at all, and even among the five that share
//! the shape the `pi`-arm proof does not factor. None of that difficulty lives
//! HERE, because at `sort 0` the `pi` arm is never reached. What these five buy
//! is the same row `redw_redAbstraction_at_a_non_pi_type` already occupies: the
//! law holds at the candidate away from the one arm that is hard. The hard part
//! stays open and is per-law.
//!
//! Everything here is SCRATCH and unwired. Every arm depends on its type-blind
//! source vec being registered first — `redrecgen_probe_sources` and
//! `redlet_blind_probe_sources` are both `#[cfg(test)]`, so the spec a probe is
//! handed does NOT carry them.

use crate::spec::Specification;

impl Specification {
    /// `redLet` and the four `redRec*` at `RedWStep (sort 0)`.
    #[cfg(test)]
    pub(super) fn candmodel_whnf_backward_sources() -> Vec<(String, String)> {
        let s0 = "(KExpr.sort Level.zero)";
        // The inert-constant side conditions the four `*_blind_inert` lemmas
        // take: the recursor name is neither δ-unfoldable nor ι-reducible in
        // the fixed `the_red_env`.
        let inert = |nm: &str| {
            format!(
                "(hdef : Eq (OptionType KExpr) \
                 (defval_for (red_def the_red_env) {nm}) (OptionType.none KExpr)) \
                 (hrec : Eq (OptionType RecMeta) \
                 (recmeta_for (red_rec the_red_env) {nm}) (OptionType.none RecMeta))"
            )
        };
        // `fun n => redw_acc_to_sort n <redex> <blind>` — the whole transfer.
        let lift = |redex: &str, blind: &str| {
            format!("fun (n : Nat) => redw_acc_to_sort n {redex} ({blind})")
        };

        let mut out: Vec<(String, String)> = Vec::new();

        let let_redex = "(KExpr.let_ A aa bb)";
        out.push((
            "redw_redLet_at_a_non_pi_type".to_string(),
            format!(
                "def redw_redLet_at_a_non_pi_type \
                 (hiota : forall (p : KExpr) (q : KExpr) (t : Nat -> KExpr), \
                 iota_reduces p q -> beta_reduces (psubst t p) (psubst t q)) \
                 (hdelta : forall (p : KExpr) (q : KExpr) (t : Nat -> KExpr), \
                 delta_reduces p q -> whnf_step (psubst t p) (psubst t q)) \
                 (kio : forall (p : KExpr) (q : KExpr) (r : KExpr) (z : KExpr), \
                 iota_reduces (KExpr.let_ p q r) z -> whnf_acc z) \
                 (kde : forall (p : KExpr) (q : KExpr) (r : KExpr) (z : KExpr), \
                 delta_reduces (KExpr.let_ p q r) z -> whnf_acc z) \
                 (A : KExpr) (bb : KExpr) (hA : whnf_acc A) \
                 (hpt : forall (x : KExpr), whnf_acc x -> whnf_acc (instantiate bb x)) \
                 (aa : KExpr) (haa : whnf_acc aa) : \
                 RedWStep {s0} {let_redex} := {body}",
                body = lift(
                    let_redex,
                    "redlet_blind_exact hiota hdelta kio kde A bb hA hpt aa haa",
                ),
            ),
        ));

        let gen_redex = "(genRecApp fam sig u m ms t)";
        out.push((
            "redw_redRecGen_at_a_non_pi_type".to_string(),
            format!(
                "def redw_redRecGen_at_a_non_pi_type \
                 (fam : Name) (sig : ListType Nat) (u : Level) {inert} \
                 (m : KExpr) (ms : ListType KExpr) (t : KExpr) \
                 (hm : whnf_acc m) (hms : WhnfAccAll ms) (ht : whnf_acc t) : \
                 RedWStep {s0} {gen_redex} := {body}",
                inert = inert("(genRecName fam sig)"),
                body = lift(
                    gen_redex,
                    "redrecgen_blind_inert fam sig u hdef hrec m ms t hm hms ht",
                ),
            ),
        ));

        let w_redex = "(wRecApp u m mn t)";
        out.push((
            "redw_redRecW_at_a_non_pi_type".to_string(),
            format!(
                "def redw_redRecW_at_a_non_pi_type (u : Level) {inert} \
                 (m : KExpr) (mn : KExpr) (t : KExpr) \
                 (hm : whnf_acc m) (hmn : whnf_acc mn) (ht : whnf_acc t) : \
                 RedWStep {s0} {w_redex} := {body}",
                inert = inert("wRecName"),
                body = lift(w_redex, "redrecw_blind_inert u hdef hrec m mn t hm hmn ht",),
            ),
        ));

        let mut_redex = "(mutRecApp msig u i cs ms t)";
        out.push((
            "redw_redRecMut_at_a_non_pi_type".to_string(),
            format!(
                "def redw_redRecMut_at_a_non_pi_type \
                 (msig : ListType FamSpec) (u : Level) (i : Nat) {inert} \
                 (cs : ListType KExpr) (ms : ListType KExpr) (t : KExpr) \
                 (hcs : WhnfAccAll cs) (hms : WhnfAccAll ms) (ht : whnf_acc t) : \
                 RedWStep {s0} {mut_redex} := {body}",
                inert = inert("(mutRecName msig i)"),
                body = lift(
                    mut_redex,
                    "redrecmut_blind_inert msig u i hdef hrec cs ms t hcs hms ht",
                ),
            ),
        ));

        let idx_redex = "(iRecApp fam isig u m ms ix t)";
        out.push((
            "redw_redRecIdx_at_a_non_pi_type".to_string(),
            format!(
                "def redw_redRecIdx_at_a_non_pi_type \
                 (fam : Name) (isig : ListType ICtor) (u : Level) {inert} \
                 (m : KExpr) (ms : ListType KExpr) (ix : ListType KExpr) (t : KExpr) \
                 (hm : whnf_acc m) (hms : WhnfAccAll ms) (hix : WhnfAccAll ix) \
                 (ht : whnf_acc t) : RedWStep {s0} {idx_redex} := {body}",
                inert = inert("(iRecName fam isig)"),
                body = lift(
                    idx_redex,
                    "redrecidx_blind_inert fam isig u hdef hrec m ms ix t hm hms hix ht",
                ),
            ),
        ));

        out
    }
}

#[cfg(test)]
#[path = "candmodel_whnf_backward_tests.rs"]
mod tests;

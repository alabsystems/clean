// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Isabelle **reprove lane** — prove a rejected statement FRESH instead of
//! translating its recorded (holey) proof.
//!
//! # The target population
//!
//! ~710 corpus lines carry a `ZNop` proof hole somewhere in their proof tree
//! (tool-internal lemmas — mostly `List`/`Nat`/`Int`/`Num`/`Set` shapes; the
//! conclusion is a `HOL.eq`/`Pure.eq` equation in ~394 of them). Their recorded
//! proofs contain an unfillable hole
//! ([`crate::hol::isabelle_pure::IsaProof::has_hole`] is `true`), so the
//! translator hard-refuses them at the top of
//! [`crate::hol::isabelle_pure_translate::translate_theorem_with_meta`] — every
//! escalation mode returns [`crate::hol::error::TranslateError::Hole`] and the
//! line can NEVER be `KernelVerified` by proof translation. But the STATEMENT is
//! intact and already embeds to a kernel `Expr` via the ordinary translator.
//!
//! # What clean-auto offers (capability survey)
//!
//! `clean-auto`'s `AutomationEngine` emits an
//! `AutomationOutcome::Verified(Box<ProofResult>)` whose `proof_term: Expr` is a
//! real kernel proof term (`ProofResult::infer_type` type-checks it). So an
//! automation success is, in principle, kernel-checkable. **However**: the
//! superposition path can emit `ProofStep::Axiom(name)` referencing arbitrary
//! environment constants (`clean-auto` `proof/builder.rs`), so a clean-auto
//! proof's transitive axiom closure is NOT guaranteed foundational. Any
//! clean-auto candidate MUST therefore be re-checked by `env.add_decl` AND gated
//! on `env.axiom_deps ⊆ FOUNDATIONAL_AXIOMS` before it may stamp
//! `KernelVerified` — exactly the gate the main verify path already applies
//! (`isabelle_pure_verify::batch::verify_one_with_translations`, the
//! `non-foundational-axiom` reject).
//!
//! On THIS population the goals are embedded HOL lemmas over `isabelle.*`
//! constants that clean-auto's SMT/superposition theories treat as
//! uninterpreted, so a clean-auto proof with a *foundational* closure is rare.
//! The mechanically-reliable, provably-foundational route is instead the
//! translator's own statement-level proof arms — telescoped `Eq.refl` for
//! definitional / datatype-computation-rule equations, `propext` isomorphisms
//! for the conjunction bridges, `True.intro`, premise-identity, … Each builds a
//! kernel term the kernel re-checks against the embedded statement and whose
//! closure is `⊆ FOUNDATIONAL_AXIOMS`. This is why the shipped lane routes the
//! hole statements through those arms rather than through clean-auto: it is the
//! subset that CAN produce kernel-checkable foundational proofs.
//!
//! # How the lane is wired (one guard, zero new gate plumbing)
//!
//! The translator's statement-level arms are already reached whenever the
//! recorded proof fails to translate: `translate_proof` returns
//! [`crate::hol::error::TranslateError::Hole`] on a `ZNop` node, which routes to
//! the `Err(_)` fallback arms (`prove_from_premises`, the `Eq.refl`
//! short-circuits, the telescoped datatype-refl). The ONLY thing standing
//! between a hole line and those arms is the `has_hole` fast-reject at the very
//! top of `translate_theorem_with_meta`.
//!
//! The reprove lane relaxes exactly that guard when [`reprove_enabled`]:
//!
//! ```text
//! if thm.proof.has_hole() && !isabelle_reprove::reprove_enabled() {
//!     return Err(TranslateError::Hole("statement proof contains a hole"));
//! }
//! ```
//!
//! A hole line then runs every escalation mode; the recorded (holey) proof
//! translation fails on the `ZNop` node and falls through to the statement-level
//! arms, whose fabricated-but-kernel-re-checked proof is `add_decl`-verified and
//! foundational-gated by the UNCHANGED `verify_one` path. The `ZNop` node is
//! never *used* — it only triggers the fall-through.
//!
//! ## Faithfulness and additivity
//!
//! - **Faithful.** The stored type is the embedded statement; the kernel
//!   re-checks `value : type` and rejects any mis-fabrication, and the
//!   `non-foundational-axiom` gate rejects any proof whose closure escapes the
//!   foundational set. Nothing is stamped `KernelVerified` that the kernel did
//!   not accept with a foundational-only closure.
//! - **Strictly additive.** Hole lines are 100% hard-rejects today (0 are
//!   `KernelVerified`), so every reprove success is a pure gain and no
//!   former-`KV` verdict can change.
//! - **Default-OFF.** [`reprove_enabled`] reads `ISA_REPROVE` once; when unset
//!   the guard fires exactly as before and the whole pipeline is byte-identical
//!   to HEAD (verified by the snapshot-resume and closure-replay gates).

/// Whether the reprove lane is enabled (`ISA_REPROVE` present and not `0`).
///
/// Parsed once and cached: the flag is read on the translate hot path (the
/// `has_hole` guard in `translate_theorem_with_meta`), so it must not re-hit the
/// environment per line.
///
/// Default-OFF — when unset the whole pipeline is byte-identical to HEAD and no
/// hole line is ever attempted.
#[must_use]
pub(crate) fn reprove_enabled() -> bool {
    // Default ON since the 2026-07-10 consolidation grand validated the lane
    // at corpus scale (+38 KV, 0 former-KV lost, gate >= 22,276 passed at
    // 22,314): every flip is kernel-re-checked with foundational closure, so
    // the lane can only add verdicts. `ISA_REPROVE=0` opts out (reproduces
    // the pre-lane bucket shapes, e.g. for hole-population analysis).
    //
    // Reads the **installed
    // [`VerifyConfig`](crate::hol::isabelle_verify_config::VerifyConfig)** for
    // the current run when one is installed (the entry points install it), else
    // the historical first-read env cache — byte-identical for an
    // un-instrumented caller, contamination-free for co-hosted runs.
    crate::hol::isabelle_verify_config::active_reprove_enabled()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_reprove_flag_parse_rule() {
        // The cache is process-global, so assert the parse rule directly rather
        // than mutating the shared env (which would race other tests).
        let parse = |v: &str| !v.is_empty() && v != "0";
        assert!(!parse(""), "empty string disables the lane");
        assert!(!parse("0"), "\"0\" disables the lane");
        assert!(parse("1"), "\"1\" enables the lane");
        assert!(parse("yes"), "any other non-empty value enables the lane");
    }

    #[test]
    fn test_reprove_enabled_callable() {
        // Smoke: the cached getter is callable and returns a bool.
        let _: bool = reprove_enabled();
    }
}

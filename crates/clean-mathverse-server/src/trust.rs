//! The honest trust statement served at `/v1/trust` and `/v1/foundational-axioms`.
//!
//! This is the public-facing TCB disclosure the design (Phase 0, §5.5) requires:
//! say plainly what "verified" means here, what is trusted-not-checked, and what
//! sits in the attacker-reachable surface.

use serde::Serialize;

/// The foundational axiom set — the only axioms a `KernelVerified` declaration's
/// transitive closure may use (Lean parity target: 3 + the `Eq` built-ins).
///
/// NOTE: this is a human-facing DISCLOSURE list (it includes prose entries for
/// the `Eq` built-ins), not a membership-check list — programmatic checks must
/// delegate to `clean_kernel::is_foundational_axiom`. Deliberately NOT named
/// after the canonical kernel const: the repo-wide anti-drift gate (#3561,
/// `clean-mathverse::shard_verify::tests::test_no_drifted_foundational_axioms_const_array`)
/// forbids re-declaring a const with that name outside the canonical
/// `crates/clean-kernel/src/env/axiom_audit.rs` (the scan matches the literal
/// `const <NAME>:` token sequence, including in comments — do not spell it out
/// here).
pub const FOUNDATIONAL_AXIOM_DISCLOSURE: &[&str] = &[
    "propext",
    "Quot.sound",
    "Classical.choice",
    "Eq.refl (built-in)",
    "Eq.ndrec / eliminators (built-in)",
];

#[derive(Debug, Clone, Serialize)]
pub struct TrustStatement {
    pub summary: &'static str,
    pub what_verified_means: &'static str,
    pub trust_levels: &'static [TrustLevelDoc],
    pub trusted_not_checked: &'static [&'static str],
    pub tcb_surface: &'static [&'static str],
    pub foundational_axioms: &'static [&'static str],
}

#[derive(Debug, Clone, Serialize)]
pub struct TrustLevelDoc {
    pub level: &'static str,
    pub meaning: &'static str,
}

const TRUST_LEVELS: &[TrustLevelDoc] = &[
    TrustLevelDoc {
        level: "KernelVerified",
        meaning: "Re-checked by the Clean kernel from the shard's proof term; \
                  transitive axiom closure ⊆ the foundational set.",
    },
    TrustLevelDoc {
        level: "SourceVerified",
        meaning: "The source system verified this constant, but the Mathverse \
                  reconstruction has not been independently Clean-kernel-checked \
                  (representation may be lossy).",
    },
    TrustLevelDoc {
        level: "Translated",
        meaning: "Translated from another system with a type-preservation claim; \
                  not Clean-kernel re-checked.",
    },
    TrustLevelDoc {
        level: "Axiomatized",
        meaning: "Statement imported but the proof is axiomatized (a skeleton may exist).",
    },
    TrustLevelDoc {
        level: "Unverified",
        meaning: "Statement only — no proof attempted. The bulk of the shipped corpus.",
    },
];

const TRUSTED_NOT_CHECKED: &[&str] = &[
    "Stored `KernelVerified` count in the shipped mathverse-v1.x corpus is 0: \
     trust is import/source confidence, NOT Clean-kernel re-verification.",
    "Metamath theorems are RPN-verified by Metamath's own checker; Lean 4 .olean \
     constants are type-reconstructed/axiomatized — neither is re-earned here.",
    "Abstract-carrier axioms (BoolAnalysis: Parseval/KKL/Friedgut/hypercontractivity) \
     are trusted-not-checked; the C4 refutation is vacuous on them.",
];

const TCB_SURFACE: &[&str] = &[
    "The Clean kernel (#![forbid(unsafe_code)]) — the only thing that re-earns a green badge.",
    "For the .olean lane: clean-olean's binary parser + shard-reconstruction path \
     are attacker-fed and inside the TCB.",
    "This hosting service displays stored trust labels; it does NOT itself re-verify \
     proofs (re-verification is the publisher/re-auditor pipeline, Phase 2).",
];

impl TrustStatement {
    pub fn current() -> Self {
        TrustStatement {
            summary: "Mathverse is today a broad-but-shallow catalog plus a tiny verified seed. \
                      This MVP serves the catalog honestly: it shows stored trust labels and \
                      does not paint unverified content green.",
            what_verified_means: "A declaration is `KernelVerified` only if the Clean kernel \
                                  re-checked its proof term and the transitive axiom closure is a \
                                  subset of the foundational axioms. Everything else is reported \
                                  at its real, lower trust level.",
            trust_levels: TRUST_LEVELS,
            trusted_not_checked: TRUSTED_NOT_CHECKED,
            tcb_surface: TCB_SURFACE,
            foundational_axioms: FOUNDATIONAL_AXIOM_DISCLOSURE,
        }
    }
}

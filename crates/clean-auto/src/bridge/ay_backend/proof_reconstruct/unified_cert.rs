// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The SHARED fail-closed certifying-verification bridge skeleton (design doc
//! §4, the "build once, reuse everywhere" scaffold).
//!
//! ════════════════════════════════════════════════════════════════════════════
//! HONEST STATUS (read before trusting anything here)
//!
//!   * This module is a **SCAFFOLD**, not a proof. It implements the *plumbing*
//!     every play (D·XLATE / D·SAFE / D·PINV / T·*) reuses: envelope ingest,
//!     structural validation, the two *acceptance gates* (`axiom_deps ⊆
//!     FOUNDATIONAL` and non-vacuity), and a TYPED placeholder for the per-play
//!     meta-theorem application.
//!   * The meta-theorem application itself ([`MetaTheorem::discharge`]) is a
//!     `TODO` trait method. A play (e.g. the BV lowering bridge in
//!     `bv_lowering_bridge.rs`) supplies the *real* kernel-term assembly. A
//!     `MetaTheorem` impl that returns `Ok` without a kernel-checked term is a
//!     stub, and is LABELLED so ([`UnimplementedMeta`]).
//!   * Per `AGENTS.md`: "prove" means `axiom_deps ⊆ FOUNDATIONAL_AXIOMS`. The
//!     [`axiom_deps_subset_foundational`] gate below is exactly that check, run
//!     over a theorem already registered in a kernel [`Environment`]. It is
//!     REAL: it calls the kernel's [`Environment::axiom_deps`]. It does **not**
//!     by itself make anything a theorem — it *refuses* a cert whose registered
//!     term carries a domain axiom.
//!
//! ## Why a shared skeleton at all
//!
//! Every play factors a TY answer into `(verdict, witness)` and proves a checker
//! `accept(witness) ⇒ verdict-true` (the soundness leg). The *shape* of that
//! acceptance is identical across plays:
//!
//!   1. **ingest** — parse the untrusted witness bytes; malformed ⇒ refuse.
//!   2. **hash-pin** — the envelope names content hashes of the parsed *source*
//!      objects (design doc §3, "wrong artifact" trap); a mismatch ⇒ refuse.
//!   3. **meta-theorem** — reduce the play's `check…` function to `Bool.true` by
//!      computation and apply the play's soundness theorem (per-play; the TODO).
//!   4. **axiom-subset gate** — the assembled theorem's transitive axiom closure
//!      must be `⊆ FOUNDATIONAL`; else refuse (design doc §4, soundness trap #5).
//!   5. **non-vacuity gate** — a checker that proves everything proves nothing:
//!      dropping a clause from a refuted obligation must make it SAT, so a real
//!      refutation is being checked, not a vacuous tautology (trap #7).
//!
//! These five steps are the "5-gate fail-closed pipeline" of §4. This module
//! provides 1, 2, 4, 5 as REAL compiling Rust with unit tests; 3 is the typed
//! `TODO` hook each play fills.

use std::collections::BTreeSet;

use clean_kernel::name::Name;
use clean_kernel::Environment;

// ── 0. domain vocabulary ────────────────────────────────────────────────────

/// Which leg(s) of the soundness/totality discipline (design doc §2) a cert
/// claims. The meter is mechanical: a frontier play ships `SoundnessOnly` and
/// says so; a decidable play may additionally carry `WithTotality`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Leg {
    /// `accept(witness) ⇒ verdict-true` for *this* verdict. Never claims a total
    /// procedure. The universal leg (achievable for every class, incl. liveness).
    SoundnessOnly,
    /// Soundness PLUS a decidability-bounded "always computes" guarantee on the
    /// play's fragment (e.g. D·SAFE finite-state, D·XLATE finite op-checklist).
    WithTotality,
}

/// The verdict an untrusted producer (TY/ay) claims, carried in the envelope so
/// the gate knows what theorem the witness is supposed to certify.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ClaimedVerdict {
    /// A safety/refinement/UNSAT-style "the bad thing cannot happen" verdict.
    Holds,
    /// A liveness `P ⇝ Q` verdict (soundness-leg only, per §8).
    LeadsTo,
    /// A lowering-refines verdict `evalNetlist N ≡ evalNetlist I` (D·XLATE).
    LoweringRefines,
}

/// A content hash of a parsed *source* object (design doc §3: certs name hashes
/// of `spec_src`, not TY's lowered relation). Opaque 32-byte digest.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct SourceHash(pub [u8; 32]);

impl SourceHash {
    /// The all-zero digest — used to detect an *unset* (forged/empty) hash slot.
    /// A real producer never emits the zero digest for a present source object;
    /// the ingester treats it as "missing" and fails closed.
    const ZERO: SourceHash = SourceHash([0u8; 32]);

    /// `true` iff this is the sentinel zero digest (i.e. an absent source hash).
    #[must_use]
    pub fn is_zero(&self) -> bool {
        *self == SourceHash::ZERO
    }
}

// ── 1. the envelope (the content-addressed package, design doc §3(b)) ────────

/// The logic-level, content-addressed certificate package the shared checker
/// ingests. Independent of TY/Trust/filesystem layout — the "one artifact, one
/// checker, two hosts" object of §3(b).
///
/// The `witness` bytes are UNTRUSTED producer output. The checker never trusts
/// them; it parses them, hash-pins the source objects, reduces the play's
/// `check…` to `Bool.true`, and applies the meta-theorem. Everything that can be
/// wrong with the bytes must be caught here and turned into a refusal.
#[derive(Clone, Debug)]
pub struct CertEnvelope {
    /// The raw, untrusted witness (e.g. a serialized refutation / ranking / step
    /// list). Opaque to the skeleton; the play's [`MetaTheorem`] parses it.
    pub witness: Vec<u8>,
    /// What the producer claims the witness certifies.
    pub claimed_verdict: ClaimedVerdict,
    /// Content hashes of the parsed source objects (module, Init, Next, Inv/P/Q,
    /// mapping, …). MUST be non-empty and contain no zero (absent) digest.
    pub source_hashes: Vec<SourceHash>,
    /// The mandatory residual-TCB line (design doc §9 / CLAUDE.md): names the
    /// unverified encoder this cert still trusts (e.g. "netlist→CNF Tseitin
    /// encoder unverified"). MUST be non-empty — an empty residual-TCB string is
    /// proof-inflation and is refused.
    pub residual_tcb: String,
    /// The soundness/totality leg the cert claims (the §2 meter).
    pub leg: Leg,
}

/// A structurally-validated envelope: ingest succeeded, so the invariants the
/// later gates rely on (non-empty hashes, no zero digest, non-empty residual
/// TCB) hold. Constructed ONLY by [`ingest`]; the private field makes that the
/// single entry point (no bypassing the structural checks).
#[derive(Clone, Debug)]
pub struct IngestedCert {
    env: CertEnvelope,
    /// De-duplicated, sorted source hashes (so the hash-pin compare is canonical).
    pinned: BTreeSet<SourceHash>,
}

impl IngestedCert {
    /// The validated underlying envelope.
    #[must_use]
    pub fn envelope(&self) -> &CertEnvelope {
        &self.env
    }
    /// The canonical (sorted, de-duplicated) pinned source hashes.
    #[must_use]
    pub fn pinned_hashes(&self) -> &BTreeSet<SourceHash> {
        &self.pinned
    }
}

// ── 2. errors — every failure mode is a REFUSAL, never a silent accept ───────

/// Why the shared bridge refused a cert. Fail-closed: any of these is a hard
/// `Err`; the bridge never downgrades a refusal to a warning.
#[derive(Debug, thiserror::Error, PartialEq, Eq)]
pub enum BridgeError {
    /// The witness byte vector was empty — nothing to certify.
    #[error("ingest: empty witness (no bytes to check)")]
    EmptyWitness,
    /// No source hashes were supplied — cannot pin the cert to a source object,
    /// so the "wrong artifact" trap (§3) is wide open. Refuse.
    #[error("ingest: no source hashes (cannot pin to source — §3 wrong-artifact trap)")]
    NoSourceHashes,
    /// A source-hash slot was the zero (absent) digest — a forged/incomplete
    /// envelope. Refuse.
    #[error("ingest: a source-hash slot is the zero digest (forged/absent)")]
    ZeroSourceHash,
    /// The residual-TCB line was empty — proof-inflation (§9). Refuse.
    #[error("ingest: empty residual-TCB line (§9 anti-inflation requires naming the encoder)")]
    EmptyResidualTcb,
    /// The expected source hashes (recomputed by the checker from `spec_src`) do
    /// not match the hashes the producer pinned. Wrong artifact. Refuse.
    #[error("hash-pin: producer hashes do not match re-encoded source ({0})")]
    HashMismatch(String),
    /// The acceptance theorem is not registered in the kernel environment — the
    /// meta-theorem step did not run / produced no `Theorem`. Refuse.
    #[error("axiom-subset gate: theorem '{0}' is not registered in the kernel env")]
    TheoremNotRegistered(String),
    /// The registered theorem's transitive axiom closure contains a
    /// non-foundational (domain / trust-marker) axiom. Not zero-trust. Refuse.
    #[error("axiom-subset gate: theorem '{theorem}' carries non-foundational axioms: {axioms:?}")]
    NonFoundationalAxioms {
        /// The theorem whose closure was audited.
        theorem: String,
        /// The offending non-foundational axiom names.
        axioms: Vec<String>,
    },
    /// The non-vacuity probe found that dropping a clause did NOT make the
    /// obligation satisfiable — so the "refutation" refutes a tautology, i.e.
    /// the checker would accept everything. Refuse (soundness trap #7).
    #[error(
        "non-vacuity gate: dropping clause {clause} left the obligation UNSAT — vacuous checker"
    )]
    Vacuous {
        /// Index of the clause whose removal failed to restore satisfiability.
        clause: usize,
    },
    /// The non-vacuity probe could not run (e.g. the witness exposes no clause
    /// set to drop from). We FAIL CLOSED: an un-probeable cert is refused, never
    /// waved through.
    #[error("non-vacuity gate: cert is not probeable ({0}) — refusing fail-closed")]
    NotProbeable(String),
    /// The per-play meta-theorem step is a stub / not implemented for this play.
    /// Surfaced as a refusal so a scaffold can never masquerade as a proof.
    #[error("meta-theorem: not implemented for this play ({0}) — scaffold, not a proof")]
    MetaUnimplemented(String),
}

// ── 3. GATE 1 — ingest (parse + structural validation, fail-closed) ──────────

/// **Gate 1 (ingest).** Parse + structurally validate an untrusted envelope.
///
/// Fail-closed: a malformed / empty / forged envelope yields `Err`, never a
/// half-trusted `IngestedCert`. Specifically refuses:
///   * an empty witness,
///   * an empty source-hash list (cannot pin to source — §3),
///   * any zero (absent) source-hash digest,
///   * an empty residual-TCB line (§9 anti-inflation).
///
/// # Errors
/// [`BridgeError::EmptyWitness`] / [`BridgeError::NoSourceHashes`] /
/// [`BridgeError::ZeroSourceHash`] / [`BridgeError::EmptyResidualTcb`].
pub fn ingest(env: CertEnvelope) -> Result<IngestedCert, BridgeError> {
    if env.witness.is_empty() {
        return Err(BridgeError::EmptyWitness);
    }
    if env.source_hashes.is_empty() {
        return Err(BridgeError::NoSourceHashes);
    }
    if env.source_hashes.iter().any(SourceHash::is_zero) {
        return Err(BridgeError::ZeroSourceHash);
    }
    if env.residual_tcb.trim().is_empty() {
        return Err(BridgeError::EmptyResidualTcb);
    }
    let pinned: BTreeSet<SourceHash> = env.source_hashes.iter().copied().collect();
    Ok(IngestedCert { env, pinned })
}

// ── 4. GATE 2 — hash-pin (re-encode from source, §3 wrong-artifact trap) ─────

/// **Gate 2 (hash-pin).** Confirm the producer-pinned source hashes match the
/// hashes the checker *re-derived* from `spec_src` (passed in as `expected`).
///
/// Per design doc §3, the checker must re-encode from the source objects and
/// never trust TY's lowered relation; this gate is where that comparison lands.
/// The set comparison is canonical (sorted/de-duplicated via [`BTreeSet`]).
///
/// # Errors
/// [`BridgeError::HashMismatch`] if the sets differ.
pub fn hash_pin(cert: &IngestedCert, expected: &[SourceHash]) -> Result<(), BridgeError> {
    let expected_set: BTreeSet<SourceHash> = expected.iter().copied().collect();
    if expected_set != cert.pinned {
        return Err(BridgeError::HashMismatch(format!(
            "producer pinned {} hash(es), checker re-derived {}",
            cert.pinned.len(),
            expected_set.len()
        )));
    }
    Ok(())
}

// ── 5. GATE 4 — axiom_deps ⊆ FOUNDATIONAL (the zero-trust gate) ──────────────

/// **Gate 4 (axiom-subset).** The registered acceptance theorem's transitive
/// axiom closure must be `⊆ FOUNDATIONAL_AXIOMS`. This is the literal meaning of
/// "prove" per `AGENTS.md` — the kernel's [`Environment::axiom_deps`] returns
/// exactly the *non-foundational* (domain + trust-marker) axioms, so the gate
/// passes iff that set is empty.
///
/// `theorem` must already be registered as a kernel `Theorem` by the play's
/// meta-theorem step (gate 3). If it is absent, the meta-theorem did not run and
/// we refuse. Parameters that are legitimate quantified variables (e.g. the
/// symbolic BV operands `a`/`b`) are passed via `allowed_params` and excluded —
/// they are not soundness axioms (mirrors the BV bridge's own audit).
///
/// # Errors
/// [`BridgeError::TheoremNotRegistered`] if `theorem` is absent;
/// [`BridgeError::NonFoundationalAxioms`] if its closure carries a domain axiom.
pub fn axiom_deps_subset_foundational(
    env: &Environment,
    theorem: &str,
    allowed_params: &[&str],
) -> Result<(), BridgeError> {
    let name = Name::from_string(theorem);
    let domain = env
        .axiom_deps(&name)
        .ok_or_else(|| BridgeError::TheoremNotRegistered(theorem.to_string()))?;
    let allowed: BTreeSet<&str> = allowed_params.iter().copied().collect();
    let mut offending: Vec<String> = domain
        .iter()
        .map(ToString::to_string)
        .filter(|n| !allowed.contains(n.as_str()))
        .collect();
    if offending.is_empty() {
        Ok(())
    } else {
        offending.sort();
        Err(BridgeError::NonFoundationalAxioms {
            theorem: theorem.to_string(),
            axioms: offending,
        })
    }
}

// ── 6. GATE 5 — non-vacuity ("drop a clause ⇒ must go SAT ⇒ refuse") ─────────

/// A minimal CNF view a cert exposes so the non-vacuity gate can probe it.
///
/// Literals are the `l = 2·var + polarity` Nat encoding the kernel uses
/// (`resolution_check.rs`); negation flips the LOW bit (`litNeg`). A clause is a
/// disjunction of literals; the formula is their conjunction.
///
/// The probe is INTENTIONALLY a tiny, self-contained DPLL over `Vec<Vec<u32>>`
/// — it is NOT the kernel checker and proves nothing on its own. Its only job is
/// to witness that the *refuted* obligation is genuinely UNSAT while every
/// single-clause-dropped obligation is SAT, i.e. the refutation is non-vacuous.
#[derive(Clone, Debug)]
pub struct CnfView {
    /// Clauses, each a list of `2·var+pol` literals.
    pub clauses: Vec<Vec<u32>>,
    /// Number of distinct variables (bounds the search).
    pub num_vars: u32,
}

/// **Gate 5 (non-vacuity).** A checker that proves everything proves nothing:
/// the obligation as a whole must be UNSAT, and dropping ANY ONE clause must
/// make it SAT. If some clause's removal leaves it UNSAT, that clause was
/// redundant and the "refutation" is (partly) vacuous — refuse.
///
/// This is the design-doc §4 / trap-#7 gate, made concrete over a CNF view. It
/// is deliberately a fast, exhaustive truth-table / DPLL check on the small
/// blasted obligations the D-tier produces (a few dozen vars). For larger
/// formulas a play supplies its own SAT-backed probe; the *contract* (drop ⇒
/// SAT) is the shared part.
///
/// # Errors
/// [`BridgeError::NotProbeable`] if the obligation is itself SAT (no refutation
/// to be non-vacuous about) or empty; [`BridgeError::Vacuous`] if some
/// clause-drop left it UNSAT.
pub fn non_vacuity_check(cnf: &CnfView) -> Result<(), BridgeError> {
    if cnf.clauses.is_empty() {
        return Err(BridgeError::NotProbeable("no clauses".to_string()));
    }
    // The full obligation must be UNSAT — otherwise there is no refutation and
    // "non-vacuity" is meaningless; fail closed.
    if sat(&cnf.clauses, cnf.num_vars) {
        return Err(BridgeError::NotProbeable(
            "obligation is SAT — no refutation to check".to_string(),
        ));
    }
    // Drop each clause in turn; a genuinely-needed clause leaves a SAT residue.
    for drop in 0..cnf.clauses.len() {
        let reduced: Vec<Vec<u32>> = cnf
            .clauses
            .iter()
            .enumerate()
            .filter(|&(i, _)| i != drop)
            .map(|(_, c)| c.clone())
            .collect();
        if !sat(&reduced, cnf.num_vars) {
            // Removing this clause did NOT restore satisfiability ⇒ it was
            // redundant ⇒ the refutation does not depend on it ⇒ vacuous.
            return Err(BridgeError::Vacuous { clause: drop });
        }
    }
    Ok(())
}

/// Exhaustive satisfiability over `num_vars` Boolean variables for the CNF
/// `clauses` (literals `2·var+pol`; pol bit 0 = positive). Returns `true` iff
/// some assignment satisfies every clause. O(2^num_vars · |clauses|) — fine for
/// the small blasted obligations this gate probes; not a production SAT engine.
fn sat(clauses: &[Vec<u32>], num_vars: u32) -> bool {
    debug_assert!(num_vars <= 24, "exhaustive probe is for small obligations");
    let total: u64 = 1u64 << num_vars.min(24);
    for assignment in 0..total {
        if clauses.iter().all(|clause| {
            clause.iter().any(|&lit| {
                let var = lit >> 1;
                let positive = (lit & 1) == 0;
                let bit = (assignment >> u64::from(var)) & 1 == 1;
                bit == positive
            })
        }) {
            return true;
        }
    }
    false
}

// ── 7. GATE 3 — the per-play meta-theorem (typed TODO hook) ──────────────────

/// **Gate 3 (meta-theorem).** The per-play step: reduce the play's `check…`
/// function to `Bool.true` by computation and apply the play's soundness theorem
/// (`checkRefutes3_sound` for the resolution leaves, `LOWERING_REFINES` for
/// D·XLATE, `LatticeRankSound` for T·LIVE, …), registering the result as a
/// kernel `Theorem` whose name the [`axiom_deps_subset_foundational`] gate then
/// audits.
///
/// This is the ONLY gate the skeleton does not implement: it is play-specific.
/// A play implements it by assembling a real kernel term (as
/// `bv_lowering_bridge::certify_lowering_by_reflection` already does) and
/// registering it. The trait makes that a typed obligation, not free text.
pub trait MetaTheorem {
    /// The kernel `Theorem` name this play registers (and the axiom-subset gate
    /// will audit).
    fn theorem_name(&self) -> String;

    /// Run the play's reflection + meta-theorem application against `env`,
    /// registering the acceptance theorem named [`Self::theorem_name`].
    ///
    /// # Errors
    /// A play returns its own [`BridgeError`] (typically wrapping a kernel
    /// rejection) on any failure; the default [`UnimplementedMeta`] returns
    /// [`BridgeError::MetaUnimplemented`] so a scaffold cannot pass as a proof.
    fn discharge(&self, env: &mut Environment, cert: &IngestedCert) -> Result<(), BridgeError>;
}

/// A typed `TODO`: the meta-theorem step for a play not yet wired in. Returns a
/// REFUSAL (never `Ok`) so the pipeline fails closed on an unimplemented play.
/// This is the honest placeholder the design doc's "5 gates compile, gate 3 is a
/// typed TODO" calls for.
pub struct UnimplementedMeta {
    /// Human-readable play tag, surfaced in the refusal.
    pub play: String,
}

impl MetaTheorem for UnimplementedMeta {
    fn theorem_name(&self) -> String {
        format!("<unimplemented::{}>", self.play)
    }
    fn discharge(&self, _env: &mut Environment, _cert: &IngestedCert) -> Result<(), BridgeError> {
        Err(BridgeError::MetaUnimplemented(self.play.clone()))
    }
}

// ── 8. the 5-gate pipeline (the shared fail-closed driver) ───────────────────

/// Inputs the shared pipeline needs from a play beyond the envelope itself.
pub struct PlayInputs<'a, M: MetaTheorem> {
    /// Source hashes the checker re-derived from `spec_src` (gate 2).
    pub expected_hashes: &'a [SourceHash],
    /// The play's meta-theorem implementation (gate 3).
    pub meta: &'a M,
    /// Quantified parameters excluded from the axiom audit (gate 4), e.g. the
    /// symbolic operands `a`/`b`.
    pub allowed_params: &'a [&'a str],
    /// The blasted-obligation CNF view for the non-vacuity probe (gate 5).
    pub cnf: &'a CnfView,
}

/// Run all five fail-closed gates in order. ANY gate's refusal aborts the
/// pipeline with that gate's [`BridgeError`]; only an all-green run returns the
/// validated [`IngestedCert`] (whose registered theorem the caller may then
/// trust *given* the named residual TCB).
///
/// Gate order: ingest → hash-pin → meta-theorem → axiom-subset → non-vacuity.
/// (Meta-theorem precedes the axiom audit because the audit needs the registered
/// theorem; non-vacuity is last because it is independent of the kernel term and
/// guards against a checker that would have accepted a tautology.)
///
/// # Errors
/// The first failing gate's [`BridgeError`].
pub fn run_pipeline<M: MetaTheorem>(
    env: &mut Environment,
    envelope: CertEnvelope,
    inputs: &PlayInputs<'_, M>,
) -> Result<IngestedCert, BridgeError> {
    // Gate 1.
    let cert = ingest(envelope)?;
    // Gate 2.
    hash_pin(&cert, inputs.expected_hashes)?;
    // Gate 3 (per-play; registers the acceptance theorem).
    inputs.meta.discharge(env, &cert)?;
    // Gate 4.
    axiom_deps_subset_foundational(env, &inputs.meta.theorem_name(), inputs.allowed_params)?;
    // Gate 5.
    non_vacuity_check(inputs.cnf)?;
    Ok(cert)
}

#[cfg(test)]
#[path = "tests_unified_cert.rs"]
mod tests;

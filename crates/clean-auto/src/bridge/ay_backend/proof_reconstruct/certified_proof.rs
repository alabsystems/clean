// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Sound public wrapper turning a reconstructed ay proof into a
//! kernel-CHECKED, serializable `CleanCic` payload.
//!
//! [`certify_reconstruction`] is the entry point. It takes a
//! [`ReconstructionResult`] (already closed by the caller: any sentinel
//! negated-goal / compound-witness FVars substituted for normal FVarIds and
//! pushed into the supplied [`LocalContext`]) plus the kernel
//! [`Environment`], and returns a [`CertifiedPayload`] only when the proof is
//! *fully* kernel-certified.
//!
//! # Soundness contract
//!
//! The whole point of this module is that a [`CertifiedPayload`] is a proof
//! that the SMT obligation is discharged *without* trusting ay. To that end
//! the certification is FAIL-CLOSED: every one of the following must hold, or
//! the function returns [`NotCertified`] (the caller then records the result
//! as `Trusted`, never `Certified`):
//!
//! 1. `proof_term` is `Some` — a proof term was actually built.
//! 2. `derives_empty_clause == true` — the proof reaches the empty clause.
//! 3. `compound_witness_fvars` is empty — no unbound witness FVars leak into
//!    the term (an open term is not a closed proof).
//! 4. NO residual-trust axiom (`trustedAy` / `trustedArith`) sub-term is
//!    present. This gate does NOT trust the caller-supplied
//!    `trust_subterm_count`: it INDEPENDENTLY re-scans the final certified term
//!    (see [`rescan_residual_trust`]) and rejects on the re-scanned count, so a
//!    reconstructor that reports `0` while emitting a `trustedAy` application
//!    cannot bypass it (gate (e) `check_type(_, False)` does not catch trust
//!    axioms — they type-check fine). If any un-reconstructed theory lemma was
//!    leaned on, the proof is only partially kernel-verified and MUST degrade
//!    to `Trusted`.
//! 5. `check_type(proof_term, False)` returns `Ok` — the FULL recursive kernel
//!    re-validation (`infer_only = false`), not the shallow `infer_type`,
//!    confirms the closed term has type `False` in the given context.
//! 6. The judgment is closed over the supplied context and
//!    [`Environment::audit_certification`] accepts the resulting `(goal, term)`
//!    pair. This is the authority gate: it follows the complete type/value
//!    dependency closure, validates foundational axioms by exact declaration,
//!    rejects unchecked/structural/unsafe/partial state, and rejects every
//!    non-foundational axiom.
//!
//! Only when (1)-(6) all hold is the proof term serialized and returned.

use clean_kernel::name::Name;
use clean_kernel::{
    BinderData, BinderInfo, CertificationIssue, Environment, Expr, ExprVisitor, FVarId, LevelVec,
    LocalContext,
};
use serde::{Deserialize, Serialize};
use std::collections::HashSet;
use thiserror::Error;

use super::ReconstructionResult;

/// A kernel-CHECKED, serializable proof payload.
///
/// A `CertifiedPayload` is only ever produced by [`certify_reconstruction`] or
/// [`certify_kernel_term`] after the proof term passed full kernel
/// re-validation, the rooted certification-authority audit, and every other
/// fail-closed soundness gate. It carries no trust in ay or in unchecked
/// environment state.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct CertifiedPayload {
    /// `bincode`-serialized kernel proof term ([`Expr`]).
    ///
    /// Re-deserializing this (see [`deserialize_term`]) and re-running
    /// `check_type(_, False)` against the matching context reproduces the
    /// certification — the payload is self-contained evidence.
    pub term_bytes: Vec<u8>,

    /// `bincode`-serialized reduced local context (its [`LocalDecl`]s only),
    /// see [`ReducedContext`].
    ///
    /// [`LocalDecl`]: clean_kernel::LocalDecl
    pub context_bytes: Vec<u8>,

    /// Number of `trustedAy` sub-terms in the certified term.
    ///
    /// Always `0` for a `CertifiedPayload` — gate (d) rejects any non-zero
    /// count. Retained as an explicit, auditable witness of that invariant.
    pub trust_count: usize,
}

/// Reason a reconstruction could not be certified.
///
/// Every variant maps a fail-closed soundness gate to a typed failure so the
/// caller can record *why* the proof degraded to `Trusted`.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
#[non_exhaustive]
pub enum NotCertified {
    /// Gate (a): reconstruction produced no proof term.
    #[error("no proof term: reconstruction did not produce a kernel term")]
    NoProofTerm,

    /// Gate (b): the proof does not derive the empty clause.
    #[error("proof does not derive the empty clause")]
    NoEmptyClause,

    /// Gate (c): the proof term contains unbound compound-witness FVars.
    #[error("proof term has {count} unbound compound-witness FVar(s)")]
    UnboundWitnesses { count: usize },

    /// Gate (d): the proof leaned on `trustedAy` (un-reconstructed lemma).
    #[error("proof uses {count} trustedAy sub-term(s); not fully kernel-certified")]
    TrustedSubterms { count: usize },

    /// Gate (e): the kernel rejected `proof_term` at the requested goal.
    #[error("kernel check_type(proof_term, goal) failed: {message}")]
    KernelRejected { message: String },

    /// Gate (f): the expression-rooted certification authority rejected the
    /// closed judgment or some declaration in its complete dependency closure.
    #[error("rooted certification authority rejected proof: {issues:?}")]
    AuthorityRejected { issues: Vec<CertificationIssue> },

    /// Encoding or exact, whole-slice decoding of a proof carrier failed.
    ///
    /// Encoding failure is internal; decoding failure means the presented
    /// carrier is malformed or non-canonical and is rejected fail-closed.
    #[error("serialization failed: {message}")]
    SerializationFailed { message: String },
}

/// A serde-serializable reduced form of [`LocalContext`].
///
/// [`LocalContext`] is not directly serializable (it carries `HashMap`s keyed
/// by `FVarId`). The kernel re-check only needs the ordered list of
/// declarations, so we serialize exactly the [`LocalDecl`] fields that
/// [`ReducedContext::into_context`] needs to rebuild an equivalent context.
///
/// [`LocalDecl`]: clean_kernel::LocalDecl
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReducedContext {
    /// One entry per declaration, in context (binding) order.
    pub decls: Vec<ReducedLocalDecl>,
}

/// Serializable projection of a kernel `LocalDecl` (decls only).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReducedLocalDecl {
    /// Free-variable id (raw `u64`).
    pub id: u64,
    /// User-facing binder name.
    pub name: Name,
    /// Declared type.
    pub type_: Expr,
    /// Definitional value for a local let-binding. `None` means an ordinary
    /// assumption. Preserving this is required for replay to reconstruct the
    /// same typing context that was certified.
    pub value: Option<Expr>,
    /// Binder annotation (info + multiplicity).
    pub bi: BinderData,
}

impl ReducedContext {
    /// Project a [`LocalContext`] to its serializable declaration list.
    fn from_context(ctx: &LocalContext) -> Self {
        let decls = ctx
            .iter()
            .map(|d| ReducedLocalDecl {
                id: d.id.as_u64(),
                name: d.name.clone(),
                type_: d.type_.clone(),
                value: d.value.clone(),
                bi: d.bi,
            })
            .collect();
        Self { decls }
    }

    /// Rebuild a [`LocalContext`] from this reduced form.
    ///
    /// Used by the round-trip soundness test (and any consumer) to re-run the
    /// kernel check against the deserialized term.
    pub fn into_context(&self) -> LocalContext {
        let mut ctx = LocalContext::new();
        for d in &self.decls {
            let id = FVarId::new(d.id);
            if let Some(value) = d.value.as_ref() {
                ctx.push_let_with_id(id, d.name.clone(), d.type_.clone(), value.clone());
            } else {
                ctx.push_with_id(id, d.name.clone(), d.type_.clone(), d.bi);
            }
        }
        ctx
    }
}

/// The kernel `False` constant, matched exactly as the e2e helper does:
/// `Const(Name "False")` with no level arguments.
pub fn false_expr() -> Expr {
    Expr::const_(Name::from_string("False"), Vec::new())
}

/// Close a judgment over an ordered local context.
///
/// Ordinary assumptions become matching `Pi`/`Lam` binders. Local definitions
/// become matching `Let` expressions so certification does not silently turn a
/// definition into an axiom. Iterating from newest to oldest lets each later
/// declaration depend on earlier locals; subsequent abstraction closes those
/// dependencies inside binder types and let values as well as bodies.
fn close_judgment(ctx: &LocalContext, goal: &Expr, term: &Expr) -> (Expr, Expr) {
    let mut closed_goal = goal.clone();
    let mut closed_term = term.clone();

    for decl in ctx.iter().rev() {
        let goal_body = closed_goal.abstract_fvar(decl.id);
        let term_body = closed_term.abstract_fvar(decl.id);
        if let Some(value) = decl.value.as_ref() {
            closed_goal = Expr::let_named(
                decl.name.clone(),
                decl.type_.clone(),
                value.clone(),
                goal_body,
                false,
            );
            closed_term = Expr::let_named(
                decl.name.clone(),
                decl.type_.clone(),
                value.clone(),
                term_body,
                false,
            );
        } else {
            closed_goal = Expr::pi(decl.bi, decl.type_.clone(), goal_body);
            closed_term = Expr::lam(decl.bi, decl.type_.clone(), term_body);
        }
    }

    (closed_goal, closed_term)
}

/// Apply the kernel's single expression-rooted certification authority to a
/// possibly open judgment by first binding every declared local.
fn audit_rooted_authority(
    env: &Environment,
    ctx: &LocalContext,
    goal: &Expr,
    term: &Expr,
) -> Result<(), NotCertified> {
    let (closed_goal, closed_term) = close_judgment(ctx, goal, term);
    let audit = env.audit_certification(&closed_goal, &closed_term);
    if audit.is_certified() {
        Ok(())
    } else if audit.issues.iter().any(|issue| {
        matches!(
            issue,
            CertificationIssue::GoalNotProposition { .. } | CertificationIssue::TermRejected { .. }
        )
    }) {
        // Preserve the public distinction between an invalid judgment and a
        // well-typed judgment whose dependency authority is insufficient. The
        // rooted audit performs the one full kernel check; do not run a second
        // TypeChecker pass here (large reflected certificates make that
        // duplication materially expensive).
        Err(NotCertified::KernelRejected {
            message: format!("{:?}", audit.issues),
        })
    } else {
        Err(NotCertified::AuthorityRejected {
            issues: audit.issues,
        })
    }
}

/// Residual-trust constant names that gate (d) re-scans for, independently of
/// the caller-supplied `trust_subterm_count`.
///
/// This is exactly the set the kernel's own `Expr::trust_scan` recognizes as
/// residual trust: the cross-theory `trustedAy` axiom (the canonical
/// reconstruction fallback, counted by
/// [`crate::bridge::proof_trust::count_embedded_trusted_ay_terms`]) and its
/// sibling `trustedArith` domain axiom (emitted by the arithmetic
/// reconstruction path when a Farkas/LRA closing step is not fully
/// kernel-reconstructed). Either constant appearing anywhere in the certified
/// term's transitive structure means the proof is only partially
/// kernel-verified and MUST NOT certify.
const RESIDUAL_TRUST_CONSTS: [&str; 2] = ["trustedAy", "trustedArith"];

/// Counts residual-trust constant sub-terms ([`RESIDUAL_TRUST_CONSTS`]) anywhere
/// in an [`Expr`]'s transitive structure.
///
/// Defense-in-depth re-scanner for gate (d): unlike the caller-supplied
/// `trust_subterm_count` field (which a buggy/malicious reconstructor could lie
/// about), this independently walks the FINAL certified term so the gate cannot
/// be bypassed by an under-reported count. It deliberately recognizes the same
/// constant set as the kernel's `Expr::trust_scan` so a term that survives this
/// gate carries no residual trust the kernel would flag.
struct ResidualTrustCounter;

impl ExprVisitor for ResidualTrustCounter {
    type Result = usize;

    fn combine(&self, a: Self::Result, b: Self::Result) -> Self::Result {
        a + b
    }

    fn visit_const(&mut self, name: &Name, _levels: &LevelVec) -> Self::Result {
        let s = name.to_string();
        usize::from(RESIDUAL_TRUST_CONSTS.contains(&s.as_str()))
    }
}

/// Independently re-scan a term for residual-trust sub-terms (gate (d)).
///
/// Never trusts the reconstructor's reported count: walks `term` directly.
fn rescan_residual_trust(term: &Expr) -> usize {
    let mut counter = ResidualTrustCounter;
    counter.visit_expr(term)
}

/// Certify a reconstructed ay proof into a kernel-CHECKED [`CertifiedPayload`].
///
/// `result` must already be *closed* by the caller: any sentinel
/// negated-goal / compound-witness FVar in `result.proof_term` substituted for
/// a normal `FVarId` that is also pushed into `ctx`. (This mirrors the e2e
/// reconstruction setup.)
///
/// Returns `Ok(CertifiedPayload)` iff all six fail-closed gates hold;
/// otherwise `Err(NotCertified)` identifying the first gate that failed. Never
/// returns a payload for a partial or trust-bearing proof.
pub(crate) fn certify_reconstruction(
    result: &ReconstructionResult,
    env: &Environment,
    ctx: &LocalContext,
) -> Result<CertifiedPayload, NotCertified> {
    // Gate (a): a proof term was produced.
    let proof_term = result
        .proof_term
        .as_ref()
        .ok_or(NotCertified::NoProofTerm)?;

    // Gate (b): the proof derives the empty clause (full contradiction).
    if !result.derives_empty_clause {
        return Err(NotCertified::NoEmptyClause);
    }

    // Gate (c): no unbound compound-witness FVars leak into the term.
    if !result.compound_witness_fvars.is_empty() {
        return Err(NotCertified::UnboundWitnesses {
            count: result.compound_witness_fvars.len(),
        });
    }

    // Gate (d): NO residual-trust axiom (`trustedAy` / `trustedArith`) is
    // present — a non-zero count means the proof is only partially
    // kernel-verified and must degrade to Trusted.
    //
    // Defense-in-depth: this gate INDEPENDENTLY re-scans the FINAL `proof_term`
    // rather than trusting `result.trust_subterm_count`. A buggy/malicious
    // reconstructor could report `trust_subterm_count == 0` while emitting a
    // term that actually applies `trustedAy`; gate (e) `check_type(_, False)`
    // would NOT catch it (axioms type-check fine), so this re-scan is the only
    // soundness barrier. The reported field is treated as advisory only: we
    // reject on `max(rescanned, reported)` so an over-reporting (honest-but-
    // conservative) field still degrades, while an under-reporting (lying)
    // field can never sneak a residual-trust term past certification.
    let rescanned_trust_count = rescan_residual_trust(proof_term);
    let effective_trust_count = rescanned_trust_count.max(result.trust_subterm_count);
    if effective_trust_count != 0 {
        return Err(NotCertified::TrustedSubterms {
            count: effective_trust_count,
        });
    }

    // Gates (e)+(f), in one traversal: close the judgment over the context,
    // then require the kernel's complete expression-rooted authority audit.
    // The audit performs full check_type (infer_only=false) and rejects all
    // unchecked, structural, unsafe, partial, trust-marked, missing, cyclic,
    // or non-foundational dependency state. Keeping this as a single pass is
    // important for large reflected certificates.
    audit_rooted_authority(env, ctx, &false_expr(), proof_term)?;

    // All gates passed — serialize the kernel-valid term and reduced context.
    let term_bytes = serialize_term(proof_term)?;
    let reduced = ReducedContext::from_context(ctx);
    let context_bytes = serialize_context(&reduced)?;

    Ok(CertifiedPayload {
        term_bytes,
        context_bytes,
        // Derived from the independent re-scan (guaranteed 0 here), NOT the
        // caller-supplied field — the payload's auditable witness must not
        // depend on the reconstructor being honest.
        trust_count: effective_trust_count,
    })
}

/// The FVarId a closed refutation binds its negated-goal hypothesis to when
/// [`reconstruct_and_certify_ay_proof`] substitutes out the reconstructor's
/// sentinel FVar. Chosen well above any hypothesis id a caller registers for
/// the small LIA fragment; kept in one place so the pushed context declaration
/// and the substitution agree.
const NEGATED_GOAL_BINDING_FVAR: u64 = 1_000_000;

/// NATIVE end-to-end: reconstruct an ay UNSAT proof into a kernel term and
/// certify it against the Clean kernel, in one call — the composer Trust's
/// router consumes to promote a `SmtBacked` verdict to `Certified`.
///
/// This is the proof-carrying-ay milestone-1 seam. It runs, in order:
/// 1. [`attempt_reconstruction`] — the NATIVE reconstruction of ay's structured
///    `ay_core::Proof` into a `clean_kernel::Expr`. This reads ay's own proof
///    data structures; it does NOT parse Alethe text and it NEVER calls Carcara.
/// 2. Sentinel closing — substitutes the reconstructor's negated-goal sentinel
///    FVar with a normal [`FVarId`] and pushes its `¬goal` declaration into a
///    clone of `ctx`, exactly as the e2e reconstruction tests do, so the term
///    becomes closed.
/// 3. [`certify_reconstruction`] — the six FAIL-CLOSED gates, including the
///    real kernel `check_type(proof_term, False)` (`infer_only = false`) and the
///    expression-rooted certification-authority audit.
///
/// The returned [`CertifiedPayload`] therefore carries NO trust in ay and NO
/// trust in Carcara: soundness reduces to the Clean kernel alone. Any failure
/// (reconstruction gap, residual trust, kernel rejection) returns
/// [`NotCertified`] — the caller keeps the honest pre-certification verdict.
///
/// [`attempt_reconstruction`]: super::attempt_reconstruction
pub fn reconstruct_and_certify_ay_proof(
    proof: &ay_core::Proof,
    terms: &ay_core::TermStore,
    var_map: &super::VariableMapping,
    negated_goal: &Expr,
    env: &Environment,
    ctx: &LocalContext,
) -> Result<CertifiedPayload, NotCertified> {
    // (1) NATIVE reconstruction from ay's structured proof — no Alethe parse,
    //     no Carcara. The Clean kernel is the only trust root downstream.
    let mut result = super::attempt_reconstruction(proof, terms, var_map, negated_goal);

    // (2) Close the negated-goal sentinel so the term has no open sentinel FVar.
    let mut closed_ctx = ctx.clone();
    if let Some(sentinel_id) = result.negated_goal_fvar {
        let bind_id = FVarId::new(NEGATED_GOAL_BINDING_FVAR);
        if let Some(term) = result.proof_term.as_ref() {
            let closed = term.subst_fvar(sentinel_id, &Expr::fvar(bind_id));
            result.proof_term = Some(closed);
        }
        closed_ctx.push_with_id(
            bind_id,
            Name::from_string("h_neg_goal"),
            negated_goal.clone(),
            BinderInfo::Default,
        );
    }

    // (3) FAIL-CLOSED kernel certification: strict check_type(_, False), exact
    //     rooted dependency authority, and independent trust re-scan.
    certify_reconstruction(&result, env, &closed_ctx)
}

/// Certify an already-assembled kernel term `proof_term` against an explicit
/// `goal` type, in the given `ctx` — the general-goal analogue of
/// [`certify_reconstruction`] (whose goal is fixed to `False`).
///
/// Proof-carrying ay, MILESTONE 2 (BV multiplication). The BV bit-blast
/// reflection lane produces a `checkRefutes_sound … : Unsat <clauses>` term
/// (NOT a `False`-typed refutation), so the milestone-1 `certify_reconstruction`
/// (which hard-codes the `False` goal) cannot certify it. This helper applies the
/// SAME fail-closed discipline to any goal:
///
/// * gate (d) — the independent `trustedAy`/`trustedArith` re-scan
///   ([`rescan_residual_trust`]), rejecting on a non-zero count so a
///   trust-bearing term can never certify; and
/// * gate (e) — the FULL kernel `check_type(proof_term, goal)`
///   (`infer_only = false`), confirming the term genuinely inhabits `goal`.
/// * gate (f) — close `goal` and `proof_term` over `ctx`, then require
///   [`Environment::audit_certification`] to accept the complete rooted
///   dependency closure and exact foundational declarations.
///
/// On success it serializes the kernel-valid term + reduced context into a
/// [`CertifiedPayload`] with `trust_count == 0`. No caller-side name whitelist
/// or residue scan is trusted for authority.
///
/// # Errors
/// [`NotCertified::TrustedSubterms`] if the term carries residual trust;
/// [`NotCertified::KernelRejected`] if `check_type(proof_term, goal)` fails;
/// [`NotCertified::AuthorityRejected`] if the rooted authority audit fails;
/// [`NotCertified::SerializationFailed`] on an encoding error.
pub fn certify_kernel_term(
    proof_term: &Expr,
    goal: &Expr,
    env: &Environment,
    ctx: &LocalContext,
) -> Result<CertifiedPayload, NotCertified> {
    // Gate (d): independent residual-trust re-scan (never trusts a caller count).
    let rescanned_trust_count = rescan_residual_trust(proof_term);
    if rescanned_trust_count != 0 {
        return Err(NotCertified::TrustedSubterms {
            count: rescanned_trust_count,
        });
    }

    // Gates (e)+(f), in one traversal: the exact rooted audit performs the full
    // kernel check over the context-closed judgment and validates its complete
    // authority closure. This is the final authorization step shared by every
    // CertifiedPayload constructor.
    audit_rooted_authority(env, ctx, goal, proof_term)?;

    let term_bytes = serialize_term(proof_term)?;
    let reduced = ReducedContext::from_context(ctx);
    let context_bytes = serialize_context(&reduced)?;

    Ok(CertifiedPayload {
        term_bytes,
        context_bytes,
        trust_count: rescanned_trust_count,
    })
}

/// Re-deserialize a certified proof term from [`CertifiedPayload::term_bytes`].
///
/// The encoding must consume the complete byte slice and equal the canonical
/// re-encoding of the decoded term. Exact consumption alone is insufficient:
/// bincode accepts some non-minimal varints, which would let two distinct
/// authenticated payloads decode to the same kernel term.
pub fn deserialize_term(term_bytes: &[u8]) -> Result<Expr, NotCertified> {
    crate::proof_codec::decode_term(term_bytes).map_err(serialization_failed)
}

/// Re-deserialize the reduced context from [`CertifiedPayload::context_bytes`].
///
/// As with [`deserialize_term`], the encoding must consume the complete slice
/// and be byte-for-byte canonical; trailing bytes and non-minimal encodings are
/// malformed, not ignorable envelope data.
pub fn deserialize_context(context_bytes: &[u8]) -> Result<ReducedContext, NotCertified> {
    crate::proof_codec::decode_context(context_bytes, validate_reduced_context)
        .map_err(serialization_failed)
}

fn serialization_failed(message: String) -> NotCertified {
    NotCertified::SerializationFailed { message }
}

/// Validate invariants needed to replay an untrusted reduced context without
/// panicking or admitting two wire values for the same rebuilt context.
fn validate_reduced_context(context: &ReducedContext) -> Result<(), String> {
    let mut budget =
        crate::proof_codec::StructuralBudget::new(crate::proof_codec::CONTEXT_STRUCTURE_LIMITS);
    budget.enter(1, 1, "reduced context")?;

    // Do not reserve from an untrusted decoded length before the structural
    // declaration budget has been applied incrementally.
    let mut ids = HashSet::new();
    for decl in &context.decls {
        budget.enter(2, 1, "local declaration")?;
        if FVarId::new(decl.id).is_sentinel() {
            return Err(format!(
                "local declaration id {} is in the reserved reconstruction-sentinel range",
                decl.id
            ));
        }
        if !ids.insert(decl.id) {
            return Err(format!("duplicate local declaration id {}", decl.id));
        }
        if decl.value.is_some() && decl.bi != BinderData::from(BinderInfo::Default) {
            return Err(format!(
                "local let declaration {} has non-default binder data that replay would discard",
                decl.id
            ));
        }
        budget.validate_name(&decl.name, 3)?;
        budget.validate_expr(&decl.type_)?;
        if let Some(value) = decl.value.as_ref() {
            budget.validate_expr(value)?;
        }
    }
    Ok(())
}

/// Serialize a kernel term into [`CertifiedPayload::term_bytes`] form — the
/// encoder half of [`deserialize_term`]. Consumers building a `CleanCic`
/// payload (e.g. the finite-DFA lane) MUST use this rather than a raw
/// `bincode::serialize`: this codec is bincode 2.x `config::standard()`
/// (varint), and a bincode 1.x fixint encoding round-trips to a corrupted term.
pub fn serialize_term(term: &Expr) -> Result<Vec<u8>, NotCertified> {
    crate::proof_codec::encode_term(term).map_err(serialization_failed)
}

/// Serialize a reduced context into [`CertifiedPayload::context_bytes`] form —
/// the encoder half of [`deserialize_context`]. Same bincode 2.x codec as
/// [`serialize_term`].
pub fn serialize_context(context: &ReducedContext) -> Result<Vec<u8>, NotCertified> {
    crate::proof_codec::encode_context(context, validate_reduced_context)
        .map_err(serialization_failed)
}

#[cfg(test)]
#[path = "tests_certified_proof.rs"]
mod tests_certified_proof;

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! VC → clean-auto Bridge for Automated Proof Discharge
//!
//! This module provides integration between the C verification condition
//! generator and the clean-auto SMT solver for automated proof discharge.
//!
//! ## Architecture
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────────────┐
//! │                    VC to SMT Bridge                                  │
//! ├─────────────────────────────────────────────────────────────────────┤
//! │                                                                      │
//! │  C VCs (Spec) ───────► clean Expr ───────► SMT Solver               │
//! │  (requires/ensures)    translate     prove_or_disprove               │
//! │                                                                      │
//! │  Proof Status ◄─────── ProofResult ◄─────── Sat/Unsat               │
//! │  (kernel/structural/   (witness/proof)                               │
//! │   unverified/failed)                                                │
//! │                                                                      │
//! └─────────────────────────────────────────────────────────────────────┘
//! ```
//!
//! ## Supported VC Types
//!
//! - Arithmetic comparisons: `x >= 0`, `a + b < n`
//! - Pointer validity: `valid(p)`, `valid_range(p, 0, n)`
//! - Boolean combinations: `P && Q`, `P || Q`, `!P`
//! - Quantified: `forall i. P(i)`, `exists x. Q(x)`
//!
//! ## Example
//!
//! ```
//! use clean_c_sem::auto::{ProofStatus, VCProver};
//! use clean_c_sem::spec::Spec;
//! use clean_c_sem::vcgen::{VC, VCKind};
//!
//! // Create a simple VC: prove 0 >= 0
//! let vc = VC {
//!     description: "trivial".to_string(),
//!     obligation: Spec::ge(Spec::int(0), Spec::int(0)),
//!     location: None,
//!     kind: VCKind::Postcondition,
//! };
//!
//! // Try to prove it
//! let mut prover = VCProver::new();
//! let status = prover.prove_vc(&vc);
//! assert!(status.is_established());
//! ```

use crate::expr::BinOp;
use crate::spec::Spec;
use crate::vcgen::{VCKind, VC};
use clean_auto::bridge::proof_trust::count_embedded_trusted_ay_terms;
use clean_kernel::{AppArgs, Environment, Expr, ExprKind};
use std::borrow::Cow;

/// Kernel-backed evidence returned by the SMT bridge.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KernelProofEvidence {
    /// Kernel proof term returned by clean-auto reconstruction.
    pub proof: Expr,
    /// Count of embedded `trustedAy` constants inside `proof`.
    pub trusted_ay_subterms: usize,
}

/// Result of attempting to prove a verification condition
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProofStatus {
    /// VC was proved with a kernel term returned by clean-auto.
    KernelVerified(KernelProofEvidence),
    /// VC was discharged by a local structural shortcut without a kernel proof term.
    StructuralProved,
    /// SMT proved UNSAT but no kernel proof term is available.
    Unverified(String),
    /// VC could not be proved
    /// Contains reason/counterexample if available
    Failed(String),
    /// Prover could not determine provability (timeout, unsupported, etc.)
    Unknown,
}

impl ProofStatus {
    /// Returns true for any success class accepted by the loose convenience APIs.
    pub fn is_established(&self) -> bool {
        matches!(self, Self::KernelVerified(_) | Self::StructuralProved)
    }

    /// Returns true when the VC has a kernel-backed proof term.
    pub fn is_kernel_verified(&self) -> bool {
        matches!(self, Self::KernelVerified(_))
    }

    /// Returns true when the VC has a kernel proof term with no embedded trust debt.
    pub fn is_fully_verified(&self) -> bool {
        matches!(
            self,
            Self::KernelVerified(KernelProofEvidence {
                trusted_ay_subterms: 0,
                ..
            })
        )
    }

    /// Compact marker for human-readable reports.
    pub fn display_marker(&self) -> &'static str {
        match self {
            Self::KernelVerified(evidence) if evidence.trusted_ay_subterms == 0 => "K",
            Self::KernelVerified(_) => "K!",
            Self::StructuralProved => "S",
            Self::Unverified(_) => "U",
            Self::Failed(_) => "X",
            Self::Unknown => "?",
        }
    }

    /// Human-readable status text for report output.
    pub fn display_text(&self) -> Cow<'static, str> {
        match self {
            Self::KernelVerified(evidence) if evidence.trusted_ay_subterms == 0 => {
                Cow::Borrowed("kernel verified")
            }
            Self::KernelVerified(evidence) => Cow::Owned(format!(
                "kernel verified with {} embedded trustedAy subterms",
                evidence.trusted_ay_subterms
            )),
            Self::StructuralProved => Cow::Borrowed("structural proof without kernel term"),
            Self::Unverified(reason) => Cow::Owned(format!("unverified UNSAT: {reason}")),
            Self::Failed(reason) => Cow::Owned(format!("failed: {reason}")),
            Self::Unknown => Cow::Borrowed("unknown"),
        }
    }
}

/// Summary of verification results for multiple VCs
#[derive(Debug, Clone, Default)]
pub struct VerificationSummary {
    /// Total number of VCs
    pub total: usize,
    /// Number of proved VCs
    pub proved: usize,
    /// Number of kernel-backed VCs
    pub kernel_verified: usize,
    /// Number of structurally discharged VCs
    pub structural_proved: usize,
    /// Number of VCs with UNSAT but no kernel proof term
    pub unverified: usize,
    /// Number of failed VCs
    pub failed: usize,
    /// Number of unknown VCs
    pub unknown: usize,
    /// Details for each VC
    pub details: Vec<(String, ProofStatus)>,
}

impl VerificationSummary {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add(&mut self, description: String, status: ProofStatus) {
        self.total += 1;
        match &status {
            ProofStatus::KernelVerified(_) => {
                self.proved += 1;
                self.kernel_verified += 1;
            }
            ProofStatus::StructuralProved => {
                self.proved += 1;
                self.structural_proved += 1;
            }
            ProofStatus::Unverified(_) => self.unverified += 1,
            ProofStatus::Failed(_) => self.failed += 1,
            ProofStatus::Unknown => self.unknown += 1,
        }
        self.details.push((description, status));
    }

    /// Check if all VCs were established by either a kernel proof or a structural shortcut.
    pub fn all_established(&self) -> bool {
        self.proved == self.total
    }

    /// Check if all VCs were kernel-verified without embedded trust debt.
    pub fn all_fully_verified(&self) -> bool {
        self.total
            == self
                .details
                .iter()
                .filter(|(_, status)| status.is_fully_verified())
                .count()
    }

    /// Backward-compatible alias for `all_established`.
    pub fn all_proved(&self) -> bool {
        self.all_established()
    }

    /// Check if any VCs failed
    pub fn has_failures(&self) -> bool {
        self.failed > 0
    }

    /// Human-readable summary line for report output.
    pub fn overview(&self) -> String {
        format!(
            "{} total, {} established ({} kernel, {} structural), {} unverified, {} failed, {} unknown",
            self.total,
            self.proved,
            self.kernel_verified,
            self.structural_proved,
            self.unverified,
            self.failed,
            self.unknown
        )
    }
}

/// Verification condition prover using clean-auto
pub struct VCProver {
    /// Kernel environment for type checking proofs
    env: Environment,
    /// Timeout for SMT solver (milliseconds)
    timeout_ms: u64,
    /// Whether to use arithmetic theory
    use_arithmetic: bool,
    /// Whether to use array theory
    use_arrays: bool,
}

impl Default for VCProver {
    fn default() -> Self {
        Self::new()
    }
}

impl VCProver {
    pub fn new() -> Self {
        Self {
            env: Environment::new(),
            timeout_ms: 5000, // 5 second default
            use_arithmetic: true,
            use_arrays: true,
        }
    }

    /// Set timeout in milliseconds
    #[must_use]
    pub fn with_timeout(mut self, ms: u64) -> Self {
        self.timeout_ms = ms;
        self
    }

    /// Enable/disable arithmetic theory
    #[must_use]
    pub fn with_arithmetic(mut self, enable: bool) -> Self {
        self.use_arithmetic = enable;
        self
    }

    /// Enable/disable array theory
    #[must_use]
    pub fn with_arrays(mut self, enable: bool) -> Self {
        self.use_arrays = enable;
        self
    }

    /// Try to prove a single verification condition
    pub fn prove_vc(&mut self, vc: &VC) -> ProofStatus {
        // SOUNDNESS (holes 2,4): an `Unsupported` obligation marks a construct
        // the verifier cannot reason about soundly. It is never established —
        // report `Unknown` unconditionally so `proved < total` and the function
        // is reported NOT verified (fail-closed). Do not attempt to prove its
        // placeholder obligation, which could be trivially discharged.
        if vc.kind == VCKind::Unsupported {
            return ProofStatus::Unknown;
        }

        // Translate Spec to clean Expr
        let Some(lean_expr) = self.spec_to_expr(&vc.obligation) else {
            return ProofStatus::Unknown;
        };

        // Try to prove using SMT bridge
        self.prove_expr(&lean_expr, &vc.kind)
    }

    /// Try to prove a Spec directly
    pub fn prove_spec(&mut self, spec: &Spec) -> ProofStatus {
        let Some(lean_expr) = self.spec_to_expr(spec) else {
            return ProofStatus::Unknown;
        };
        self.prove_expr(&lean_expr, &VCKind::Assertion)
    }

    /// Prove all VCs and return summary
    pub fn prove_all(&mut self, vcs: &[VC]) -> VerificationSummary {
        let mut summary = VerificationSummary::new();
        for vc in vcs {
            let status = self.prove_vc(vc);
            summary.add(vc.description.clone(), status);
        }
        summary
    }

    /// Check if a Spec is trivially true
    pub fn is_trivially_true(&self, spec: &Spec) -> bool {
        match spec {
            Spec::True => true,
            Spec::And(specs) => specs.iter().all(|s| self.is_trivially_true(s)),
            Spec::Implies(p, q) => self.is_trivially_false(p) || self.is_trivially_true(q),
            Spec::BinOp { op, left, right }
                // Check for reflexive comparisons
                if left == right => {
                    matches!(op, BinOp::Eq | BinOp::Le | BinOp::Ge)
                }
            _ => false,
        }
    }

    /// Check if a Spec is trivially false
    pub fn is_trivially_false(&self, spec: &Spec) -> bool {
        match spec {
            Spec::False => true,
            Spec::Or(specs) => specs.iter().all(|s| self.is_trivially_false(s)),
            Spec::BinOp { op, left, right }
                // Check for obviously false comparisons
                if left == right => {
                    matches!(op, BinOp::Ne | BinOp::Lt | BinOp::Gt)
                }
            _ => false,
        }
    }

    /// Translate Spec to clean kernel expression
    fn spec_to_expr(&self, spec: &Spec) -> Option<Expr> {
        let mut ctx = crate::translate::TranslationContext::new();
        Some(ctx.translate_spec(spec))
    }

    /// Core proving logic using clean-auto.
    ///
    /// SOUNDNESS (hole 9): a `Refuted` verdict is a GENUINE counterexample
    /// (¬goal is SAT, so the goal is FALSE) and is DISPOSITIVE. It is reported
    /// as `Failed` and is NOT overridden by the loose structural fallback that
    /// previously ran on `Refuted` (that fallback could certify a false
    /// obligation via a collapsed-head "equality").
    ///
    /// The sole exception is when the SOUND structural check *independently
    /// proves the goal true* (`StructuralProved`) — that can only happen for a
    /// genuinely-valid goal (`True`, a reflexive/constant comparison, or a
    /// composition of proved sub-goals; the translation is now injective, so
    /// distinct operands never collapse into a false equality). A
    /// genuinely-valid goal is never refuted by a *sound* SMT, so a
    /// disagreement means the SMT refutation is a translation artifact and the
    /// sound structural proof is authoritative. We deliberately do NOT accept a
    /// structural *`Failed`* as an override, nor any non-established structural
    /// result — a real counterexample stands.
    /// See docs/SOUNDNESS_FINDINGS_CLEAN_C_SEM_2026-07.md hole 9.
    fn prove_expr(&self, expr: &Expr, kind: &VCKind) -> ProofStatus {
        use clean_auto::bridge::SmtVerificationResult as SVR;
        let mut bridge = clean_auto::bridge::SmtBridge::new(&self.env);
        match bridge.prove(expr) {
            Ok(SVR::Verified(result)) => {
                let proof = result.proof_term().clone();
                let trusted_ay_subterms = count_embedded_trusted_ay_terms(&proof);
                ProofStatus::KernelVerified(KernelProofEvidence {
                    proof,
                    trusted_ay_subterms,
                })
            }
            Ok(SVR::Refuted(_)) => {
                // Only a sound, independent structural PROOF of validity may
                // override a refutation (translation artifact). Anything else —
                // including a structural `Failed` or inconclusive result —
                // leaves the genuine counterexample dispositive.
                match self.try_structural_proof(expr) {
                    Some(status @ ProofStatus::StructuralProved) => status,
                    _ => ProofStatus::Failed("SMT found counterexample".into()),
                }
            }
            // Non-committal SMT verdicts (could-not-decide / no reconstructed
            // proof term) may be translation artifacts — fall through to the
            // sound structural prover before giving up.
            Ok(SVR::Unverified { reason, .. }) => self.fallback_to_structural_or(
                expr,
                kind,
                ProofStatus::Unverified(reason.to_string()),
            ),
            Ok(SVR::Unknown(_)) => self.fallback_to_structural_or(expr, kind, ProofStatus::Unknown),
            Ok(_) | Err(_) => self.fallback_to_structural_or(expr, kind, ProofStatus::Unknown),
        }
    }

    fn fallback_to_structural_or(
        &self,
        expr: &Expr,
        kind: &VCKind,
        fallback: ProofStatus,
    ) -> ProofStatus {
        self.try_simple_proof(expr, kind).unwrap_or(fallback)
    }

    /// Try simple proof strategies for common VC patterns
    fn try_simple_proof(&self, expr: &Expr, _kind: &VCKind) -> Option<ProofStatus> {
        // First, try structural analysis of the expression
        if let Some(status) = self.try_structural_proof(expr) {
            return Some(status);
        }

        None
    }

    /// Try proving based on the structure of the expression
    fn try_structural_proof(&self, expr: &Expr) -> Option<ProofStatus> {
        let head = expr.get_app_fn();
        let args = expr.get_app_args();

        match head.kind() {
            ExprKind::Const(name, _) => self.try_structural_const_proof(&name.to_string(), &args),
            ExprKind::Pi(_, domain, codomain) => self.try_structural_pi_proof(domain, codomain),
            ExprKind::App(func, _) => self.try_structural_exists_proof(func),
            _ => None,
        }
    }

    fn try_structural_const_proof(
        &self,
        name_str: &str,
        args: &AppArgs<'_>,
    ) -> Option<ProofStatus> {
        // SOUNDNESS (holes 5,6,8): `exprs_structurally_equal` on the two
        // operands only discharges `Eq`/`le`/`ge` reflexively when the
        // Spec→Expr lowering is INJECTIVE on operator and variant identity —
        // otherwise distinct operations that collapse to the same head would be
        // "proved" equal. The lowering in `translate.rs` now embeds
        // operator/variant identity in every head (`Spec.binop.<Op>`,
        // `Spec.unsupported.<Variant>`, `CExpr.sizeofExpr`, ...), so structural
        // equality of the translated operands implies the source operands were
        // themselves structurally identical, and reflexive equality holds.
        // See docs/SOUNDNESS_FINDINGS_CLEAN_C_SEM_2026-07.md holes 5,6,8.
        match name_str {
            "True" => Some(ProofStatus::StructuralProved),
            "False" => Some(ProofStatus::Failed("Cannot prove False".to_string())),
            "Eq" if args.len() >= 2 => {
                let len = args.len();
                let lhs = args[len - 2];
                let rhs = args[len - 1];
                if self.exprs_structurally_equal(lhs, rhs) {
                    Some(ProofStatus::StructuralProved)
                } else {
                    None
                }
            }
            "LE.le" | "Int.le" | "Nat.le" if args.len() >= 2 => {
                let len = args.len();
                let lhs = args[len - 2];
                let rhs = args[len - 1];
                if self.exprs_structurally_equal(lhs, rhs) {
                    return Some(ProofStatus::StructuralProved);
                }
                if let (Some(a), Some(b)) = (self.try_extract_int(lhs), self.try_extract_int(rhs)) {
                    if a <= b {
                        return Some(ProofStatus::StructuralProved);
                    }
                    return Some(ProofStatus::Failed(format!("{a} > {b}")));
                }
                None
            }
            "GE.ge" if args.len() >= 2 => {
                let len = args.len();
                let lhs = args[len - 2];
                let rhs = args[len - 1];
                if self.exprs_structurally_equal(lhs, rhs) {
                    return Some(ProofStatus::StructuralProved);
                }
                if let (Some(a), Some(b)) = (self.try_extract_int(lhs), self.try_extract_int(rhs)) {
                    if a >= b {
                        return Some(ProofStatus::StructuralProved);
                    }
                    return Some(ProofStatus::Failed(format!("{a} < {b}")));
                }
                None
            }
            "LT.lt" | "Int.lt" | "Nat.lt" if args.len() >= 2 => {
                let len = args.len();
                let lhs = args[len - 2];
                let rhs = args[len - 1];
                if self.exprs_structurally_equal(lhs, rhs) {
                    return Some(ProofStatus::Failed("x < x is false".to_string()));
                }
                if let (Some(a), Some(b)) = (self.try_extract_int(lhs), self.try_extract_int(rhs)) {
                    if a < b {
                        return Some(ProofStatus::StructuralProved);
                    }
                    return Some(ProofStatus::Failed(format!("{a} >= {b}")));
                }
                None
            }
            "GT.gt" if args.len() >= 2 => {
                let len = args.len();
                let lhs = args[len - 2];
                let rhs = args[len - 1];
                if self.exprs_structurally_equal(lhs, rhs) {
                    return Some(ProofStatus::Failed("x > x is false".to_string()));
                }
                if let (Some(a), Some(b)) = (self.try_extract_int(lhs), self.try_extract_int(rhs)) {
                    if a > b {
                        return Some(ProofStatus::StructuralProved);
                    }
                    return Some(ProofStatus::Failed(format!("{a} <= {b}")));
                }
                None
            }
            "And" if args.len() == 2 => {
                let p_status = self.try_structural_proof(args[0]);
                let q_status = self.try_structural_proof(args[1]);
                match (p_status, q_status) {
                    (Some(left), Some(right))
                        if left.is_established() && right.is_established() =>
                    {
                        Some(ProofStatus::StructuralProved)
                    }
                    (Some(ProofStatus::Failed(reason)), _) => {
                        Some(ProofStatus::Failed(format!("Left conjunct: {reason}")))
                    }
                    (_, Some(ProofStatus::Failed(reason))) => {
                        Some(ProofStatus::Failed(format!("Right conjunct: {reason}")))
                    }
                    _ => None,
                }
            }
            "Or" if args.len() == 2 => {
                if self
                    .try_structural_proof(args[0])
                    .as_ref()
                    .is_some_and(ProofStatus::is_established)
                    || self
                        .try_structural_proof(args[1])
                        .as_ref()
                        .is_some_and(ProofStatus::is_established)
                {
                    Some(ProofStatus::StructuralProved)
                } else {
                    None
                }
            }
            "Not" if args.len() == 1 => match self.try_structural_proof(args[0]) {
                Some(ProofStatus::Failed(_)) => Some(ProofStatus::StructuralProved),
                Some(status) if status.is_established() => {
                    Some(ProofStatus::Failed("Cannot prove Not(True)".to_string()))
                }
                _ => None,
            },
            _ => None,
        }
    }

    fn try_structural_pi_proof(&self, domain: &Expr, codomain: &Expr) -> Option<ProofStatus> {
        if !codomain.has_loose_bvars() {
            if self
                .try_structural_proof(codomain)
                .as_ref()
                .is_some_and(ProofStatus::is_established)
            {
                return Some(ProofStatus::StructuralProved);
            }
            if let Some(ProofStatus::Failed(_)) = self.try_structural_proof(domain) {
                return Some(ProofStatus::StructuralProved);
            }
        }

        if self
            .try_structural_proof(codomain)
            .as_ref()
            .is_some_and(ProofStatus::is_established)
        {
            return Some(ProofStatus::StructuralProved);
        }

        None
    }

    fn try_structural_exists_proof(&self, func: &Expr) -> Option<ProofStatus> {
        let head = func.get_app_fn();
        if let ExprKind::Const(name, _) = head.kind() {
            if name.to_string() == "Exists" {
                return None;
            }
        }
        None
    }

    /// Check if two expressions are structurally equal
    fn exprs_structurally_equal(&self, a: &Expr, b: &Expr) -> bool {
        match (a.kind(), b.kind()) {
            (ExprKind::BVar(i), ExprKind::BVar(j)) => i == j,
            (ExprKind::FVar(i), ExprKind::FVar(j)) => i == j,
            (ExprKind::Const(n1, _), ExprKind::Const(n2, _)) => n1 == n2,
            (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => {
                self.exprs_structurally_equal(f1, f2) && self.exprs_structurally_equal(a1, a2)
            }
            (ExprKind::Lit(l1), ExprKind::Lit(l2)) => l1 == l2,
            _ => false,
        }
    }

    /// Try to extract an integer constant from an expression
    fn try_extract_int(&self, expr: &Expr) -> Option<i64> {
        match expr.kind() {
            ExprKind::Lit(clean_kernel::Literal::Nat(n)) => {
                n.to_u64().and_then(|v| i64::try_from(v).ok())
            }
            ExprKind::App(f, arg) => {
                let head = f.get_app_fn();
                if let ExprKind::Const(name, _) = head.kind() {
                    let name_str = name.to_string();
                    match name_str.as_str() {
                        "Int.ofNat" => self.try_extract_nat(arg),
                        "Int.negOfNat" => {
                            // Handle negation carefully to avoid overflow.
                            // For magnitude m, the result is -m unless m > i64::MAX,
                            // in which case it's only representable if m == i64::MAX + 1 (i.e., i64::MIN's magnitude).
                            let m = self.try_extract_nat(arg)?;
                            if m >= 0 {
                                m.checked_neg()
                            } else {
                                // m is already negative from try_extract_nat, shouldn't happen
                                // but handle defensively
                                None
                            }
                        }
                        "Nat.succ" => self.try_extract_nat(expr),
                        _ => None,
                    }
                } else {
                    None
                }
            }
            ExprKind::Const(name, _) => {
                if name.to_string() == "Nat.zero" {
                    Some(0)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Try to extract a natural number from an expression (Nat.zero / Nat.succ chain)
    /// Returns the value as i64; returns None if the value exceeds i64::MAX
    fn try_extract_nat(&self, expr: &Expr) -> Option<i64> {
        match expr.kind() {
            ExprKind::Lit(clean_kernel::Literal::Nat(n)) => {
                n.to_u64().and_then(|v| i64::try_from(v).ok())
            }
            ExprKind::Const(name, _) if name.to_string() == "Nat.zero" => Some(0),
            ExprKind::App(f, arg) => {
                if let ExprKind::Const(name, _) = f.kind() {
                    if name.to_string() == "Nat.succ" {
                        return self.try_extract_nat(arg).and_then(|n| n.checked_add(1));
                    }
                }
                None
            }
            _ => None,
        }
    }
}

/// Quick verification of a specification
/// Returns true if provable, false otherwise
pub fn quick_check(spec: &Spec) -> bool {
    let mut prover = VCProver::new().with_timeout(1000);
    prover.prove_spec(spec).is_established()
}

/// Strict verification of a specification.
/// Returns true only for kernel-backed proofs with zero embedded trust debt.
pub fn quick_check_fully_verified(spec: &Spec) -> bool {
    let mut prover = VCProver::new().with_timeout(1000);
    prover.prove_spec(spec).is_fully_verified()
}

/// Verify a set of VCs and print results
pub fn verify_and_report(vcs: &[VC]) -> VerificationSummary {
    let mut prover = VCProver::new();
    let summary = prover.prove_all(vcs);

    // Print summary
    tracing::info!("Verification: {}", summary.overview());

    for (desc, status) in &summary.details {
        tracing::info!(
            "  {} {desc} - {}",
            status.display_marker(),
            status.display_text()
        );
    }

    summary
}

pub use crate::simplify::simplify_spec;

#[cfg(test)]
#[path = "auto_tests.rs"]
mod auto_tests;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::CExpr;
    use crate::spec::FuncSpec;
    use crate::stmt::{CStmt, FuncDef, FuncParam, StorageClass};
    use crate::types::CType;
    use crate::vcgen::VCGen;

    #[test]
    fn test_abs_function_vcs() {
        // Generate VCs for abs function
        let mut vcgen = VCGen::new();

        let func = FuncDef {
            is_noreturn: false,
            name: "abs".into(),
            return_type: CType::int(),
            params: vec![FuncParam {
                name: "n".into(),
                ty: CType::int(),
            }],
            body: Box::new(CStmt::if_else(
                CExpr::binop(BinOp::Lt, CExpr::var("n"), CExpr::int(0)),
                CStmt::return_stmt(Some(CExpr::unary(
                    crate::expr::UnaryOp::Neg,
                    CExpr::var("n"),
                ))),
                CStmt::return_stmt(Some(CExpr::var("n"))),
            )),
            variadic: false,
            storage: StorageClass::Auto,
        };

        let spec = FuncSpec {
            requires: vec![Spec::True],
            ensures: vec![Spec::ge(Spec::result(), Spec::int(0))],
            ..Default::default()
        };

        let vcs = vcgen.gen_function(&func, &spec);
        assert!(!vcs.is_empty());

        // Verify the VCs
        let mut prover = VCProver::new();
        let summary = prover.prove_all(&vcs);

        // At minimum, we should get results for all VCs
        assert_eq!(summary.total, vcs.len());
    }

    #[test]
    fn test_prover_creation() {
        let prover = VCProver::new()
            .with_timeout(2000)
            .with_arithmetic(true)
            .with_arrays(false);

        assert_eq!(prover.timeout_ms, 2000);
        assert!(prover.use_arithmetic);
        assert!(!prover.use_arrays);
    }

    #[test]
    fn test_swap_function_vcs() {
        // Generate VCs for swap function:
        // void swap(int *x, int *y) {
        //     int tmp = *x;
        //     *x = *y;
        //     *y = tmp;
        // }
        //
        // Separation logic spec:
        // PRE:  x ↦ a * y ↦ b
        // POST: x ↦ b * y ↦ a
        use crate::sep::{SepAssertion, SepFuncSpec, Share};

        let mut vcgen = VCGen::new();

        // Build the swap function
        let func = FuncDef {
            is_noreturn: false,
            name: "swap".into(),
            return_type: CType::Void,
            params: vec![
                FuncParam {
                    name: "x".into(),
                    ty: CType::Pointer(Box::new(CType::int())),
                },
                FuncParam {
                    name: "y".into(),
                    ty: CType::Pointer(Box::new(CType::int())),
                },
            ],
            body: Box::new(CStmt::block(vec![
                // int tmp = *x;
                CStmt::decl_init("tmp", CType::int(), CExpr::deref(CExpr::var("x"))),
                // *x = *y;
                CStmt::Expr(CExpr::assign(
                    CExpr::deref(CExpr::var("x")),
                    CExpr::deref(CExpr::var("y")),
                )),
                // *y = tmp;
                CStmt::Expr(CExpr::assign(
                    CExpr::deref(CExpr::var("y")),
                    CExpr::var("tmp"),
                )),
            ])),
            variadic: false,
            storage: StorageClass::Auto,
        };

        // ACSL-style spec
        let spec = FuncSpec {
            requires: vec![
                Spec::valid(Spec::var("x")),
                Spec::valid(Spec::var("y")),
                Spec::Separated(vec![Spec::var("x"), Spec::var("y")]),
            ],
            ensures: vec![
                Spec::eq(
                    Spec::Expr(CExpr::deref(CExpr::var("x"))),
                    Spec::old(Spec::Expr(CExpr::deref(CExpr::var("y")))),
                ),
                Spec::eq(
                    Spec::Expr(CExpr::deref(CExpr::var("y"))),
                    Spec::old(Spec::Expr(CExpr::deref(CExpr::var("x")))),
                ),
            ],
            ..Default::default()
        };

        // Generate VCs
        let vcs = vcgen.gen_function(&func, &spec);
        assert!(!vcs.is_empty(), "Should generate VCs for swap");

        // Build separation logic spec for additional checking
        let sep_spec = SepFuncSpec::new(
            SepAssertion::sep_conj(
                SepAssertion::data_at(CExpr::var("x"), CType::int(), Spec::var("a"), Share::Full),
                SepAssertion::data_at(CExpr::var("y"), CType::int(), Spec::var("b"), Share::Full),
            ),
            SepAssertion::sep_conj(
                SepAssertion::data_at(CExpr::var("x"), CType::int(), Spec::var("b"), Share::Full),
                SepAssertion::data_at(CExpr::var("y"), CType::int(), Spec::var("a"), Share::Full),
            ),
        );

        // Check that pre and post are different (values swapped)
        assert_ne!(sep_spec.pre, sep_spec.post);

        // Check pointers mentioned
        let pre_ptrs = sep_spec.pre.mentioned_pointers();
        let post_ptrs = sep_spec.post.mentioned_pointers();
        assert_eq!(pre_ptrs.len(), 2);
        assert_eq!(post_ptrs.len(), 2);

        // Verify the VCs
        let mut prover = VCProver::new();
        let summary = prover.prove_all(&vcs);
        assert_eq!(summary.total, vcs.len());
    }

    #[test]
    fn test_increment_function_vcs() {
        // Simple function: increment a pointer value
        // void incr(int *p) { *p = *p + 1; }
        // PRE:  valid(p) && *p == n
        // POST: *p == n + 1

        let mut vcgen = VCGen::new();

        let func = FuncDef {
            is_noreturn: false,
            name: "incr".into(),
            return_type: CType::Void,
            params: vec![FuncParam {
                name: "p".into(),
                ty: CType::Pointer(Box::new(CType::int())),
            }],
            body: Box::new(CStmt::Expr(CExpr::assign(
                CExpr::deref(CExpr::var("p")),
                CExpr::add(CExpr::deref(CExpr::var("p")), CExpr::int(1)),
            ))),
            variadic: false,
            storage: StorageClass::Auto,
        };

        let spec = FuncSpec {
            requires: vec![Spec::valid(Spec::var("p"))],
            ensures: vec![Spec::eq(
                Spec::Expr(CExpr::deref(CExpr::var("p"))),
                Spec::binop(
                    BinOp::Add,
                    Spec::old(Spec::Expr(CExpr::deref(CExpr::var("p")))),
                    Spec::int(1),
                ),
            )],
            ..Default::default()
        };

        let vcs = vcgen.gen_function(&func, &spec);
        assert!(!vcs.is_empty(), "Should generate VCs for incr function");

        // Verify the VCs (postcondition VCs should be present)
        let has_postcondition = vcs
            .iter()
            .any(|vc| vc.kind == crate::vcgen::VCKind::Postcondition);
        assert!(has_postcondition, "Should have postcondition VC");
    }

    #[test]
    fn test_structural_proof_true() {
        let mut prover = VCProver::new();
        let status = prover.prove_spec(&Spec::True);
        assert!(
            status.is_established(),
            "True should be established, got {status:?}"
        );
    }

    #[test]
    fn test_structural_proof_false() {
        let mut prover = VCProver::new();
        let status = prover.prove_spec(&Spec::False);
        assert!(matches!(status, ProofStatus::Failed(_)));
    }

    #[test]
    fn test_structural_proof_reflexive_eq() {
        let mut prover = VCProver::new();
        // x = x should be proved
        let spec = Spec::eq(Spec::var("x"), Spec::var("x"));
        let status = prover.prove_spec(&spec);
        assert!(
            status.is_established(),
            "Reflexive equality should be proved, got {status:?}"
        );
    }

    #[test]
    fn test_structural_proof_reflexive_le() {
        let mut prover = VCProver::new();
        // x ≤ x should be proved
        let spec = Spec::le(Spec::var("x"), Spec::var("x"));
        let status = prover.prove_spec(&spec);
        assert!(
            status.is_established(),
            "Reflexive ≤ should be proved, got {status:?}"
        );
    }

    #[test]
    fn test_structural_proof_constant_comparison() {
        let mut prover = VCProver::new();

        // 1 < 2 should be proved
        let spec = Spec::lt(Spec::int(1), Spec::int(2));
        let status = prover.prove_spec(&spec);
        assert!(
            status.is_established(),
            "1 < 2 should be proved, got {status:?}"
        );

        // 0 ≤ 5 should be proved
        let spec = Spec::le(Spec::int(0), Spec::int(5));
        let status = prover.prove_spec(&spec);
        assert!(
            status.is_established(),
            "0 ≤ 5 should be proved, got {status:?}"
        );

        // 10 ≥ 3 should be proved
        let spec = Spec::ge(Spec::int(10), Spec::int(3));
        let status = prover.prove_spec(&spec);
        assert!(
            status.is_established(),
            "10 ≥ 3 should be proved, got {status:?}"
        );
    }

    #[test]
    fn test_structural_proof_conjunction() {
        let mut prover = VCProver::new();

        // True ∧ True should be proved
        let spec = Spec::and(vec![Spec::True, Spec::True]);
        let status = prover.prove_spec(&spec);
        assert!(
            status.is_established(),
            "True ∧ True should be proved, got {status:?}"
        );

        // 1 < 2 ∧ 3 < 4 should be proved
        let spec = Spec::and(vec![
            Spec::lt(Spec::int(1), Spec::int(2)),
            Spec::lt(Spec::int(3), Spec::int(4)),
        ]);
        let status = prover.prove_spec(&spec);
        assert!(
            status.is_established(),
            "1 < 2 ∧ 3 < 4 should be proved, got {status:?}"
        );
    }

    #[test]
    fn test_structural_proof_disjunction() {
        let mut prover = VCProver::new();

        // True ∨ False should be proved
        let spec = Spec::or(vec![Spec::True, Spec::False]);
        let status = prover.prove_spec(&spec);
        assert!(
            status.is_established(),
            "True ∨ False should be proved, got {status:?}"
        );

        // False ∨ True should be proved
        let spec = Spec::or(vec![Spec::False, Spec::True]);
        let status = prover.prove_spec(&spec);
        assert!(
            status.is_established(),
            "False ∨ True should be proved, got {status:?}"
        );
    }

    #[test]
    fn test_structural_proof_implication() {
        let mut prover = VCProver::new();

        // P → True should be proved
        let spec = Spec::implies(Spec::var("P"), Spec::True);
        let status = prover.prove_spec(&spec);
        assert!(
            status.is_established(),
            "P → True should be proved, got {status:?}"
        );

        // False → P should be proved
        let spec = Spec::implies(Spec::False, Spec::var("P"));
        let status = prover.prove_spec(&spec);
        assert!(
            status.is_established(),
            "False → P should be proved, got {status:?}"
        );
    }

    #[test]
    fn test_structural_proof_negation() {
        let mut prover = VCProver::new();

        // ¬False should be proved
        let spec = Spec::not(Spec::False);
        let status = prover.prove_spec(&spec);
        assert!(
            status.is_established(),
            "¬False should be proved, got {status:?}"
        );
    }

    #[test]
    fn test_try_extract_nat_overflow() {
        use clean_kernel::{BigNat, ExprKind, Literal};

        let prover = VCProver::new();

        // Values exceeding i64::MAX should return None
        let large_nat = Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(u64::MAX))));
        assert_eq!(prover.try_extract_nat(&large_nat), None);

        // i64::MAX should be extractable
        let max_i64 = Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(i64::MAX as u64))));
        assert_eq!(prover.try_extract_nat(&max_i64), Some(i64::MAX));

        // i64::MAX + 1 should NOT be extractable (exceeds i64)
        let overflow = Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(
            (i64::MAX as u64) + 1,
        ))));
        assert_eq!(prover.try_extract_nat(&overflow), None);
    }

    #[test]
    fn test_try_extract_int_from_nat_literal() {
        use clean_kernel::{BigNat, ExprKind, Literal};

        let prover = VCProver::new();

        // Small values should work
        let small = Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(42))));
        assert_eq!(prover.try_extract_int(&small), Some(42));

        // i64::MAX should work
        let max = Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(i64::MAX as u64))));
        assert_eq!(prover.try_extract_int(&max), Some(i64::MAX));

        // Values > i64::MAX should return None
        let overflow = Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(
            (i64::MAX as u64) + 1,
        ))));
        assert_eq!(prover.try_extract_int(&overflow), None);
    }

    #[test]
    fn test_try_extract_nat_succ_overflow() {
        use clean_kernel::{BigNat, ExprKind, Literal, Name};
        use std::str::FromStr;

        let prover = VCProver::new();

        // Nat.succ(i64::MAX) should overflow and return None
        let succ_name = Name::from_str("Nat.succ").unwrap();
        let max_nat = Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(i64::MAX as u64))));
        let succ_max = Expr::app(Expr::const_(succ_name, vec![]), max_nat);
        assert_eq!(
            prover.try_extract_nat(&succ_max),
            None,
            "Nat.succ(i64::MAX) should return None due to overflow"
        );
    }
}

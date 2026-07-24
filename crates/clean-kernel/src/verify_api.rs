// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Self-verification API — Wave 1 (#1891)
//!
//! Chains cert generation → replay → micro-check into a single reusable
//! primitive. Provides both single-expression and batch verification.
//!
//! # Three-Stage Pipeline
//!
//! 1. `TypeChecker::infer_type_with_cert(expr)` → `(type, ProofCert)`
//! 2. `CertVerifier::replay_and_verify(cert)` → `(reconstructed_expr, verified_type)`
//! 3. `cross_validate_with_micro(expr, type, cert)` → `Ok(true)` / `Ok(false)` / `Err`
//!
//! Stage 2 confirms that the certificate can independently reconstruct and
//! re-derive the typing judgment. Stage 3 runs a minimal independent checker
//! on the subset of expressions it supports (returns `Ok(false)` for
//! unsupported constructs like Const, FVar, mode-specific forms).

use crate::cert::{CertError, CertVerifier, ProofCert};
use crate::env::Environment;
use crate::expr::Expr;
use crate::micro::{cross_validate_with_micro, CrossValidationError};
use crate::tc::TypeChecker;
use crate::TypeError;

/// Structured evidence from a successful `verify_expr` call.
///
/// Contains the original expression, inferred type, proof certificate,
/// and results from each verification stage.
///
/// External crates must obtain this from [`verify_expr`] rather than fabricate
/// it with a struct literal.
///
/// ```compile_fail
/// use clean_kernel::cert::ProofCert;
/// use clean_kernel::expr::Expr;
/// use clean_kernel::verify_api::VerificationEvidence;
///
/// fn bogus_expr() -> Expr { loop {} }
/// fn bogus_cert() -> ProofCert { loop {} }
///
/// let _ = VerificationEvidence {
///     expr: bogus_expr(),
///     inferred_type: bogus_expr(),
///     cert: bogus_cert(),
///     replay_match: true,
///     micro_match: true,
/// };
/// ```
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct VerificationEvidence {
    /// The expression that was verified.
    pub expr: Expr,
    /// The type inferred by the kernel's type checker.
    pub inferred_type: Expr,
    /// The proof certificate emitted during type inference.
    pub cert: ProofCert,
    /// Whether certificate replay matched (stage 2 passed).
    pub replay_match: bool,
    /// Whether the micro-checker confirmed the typing (stage 3).
    /// `true` = micro-checker agreed, `false` = expression uses
    /// unsupported constructs (graceful skip, not a failure).
    pub micro_match: bool,
}

impl VerificationEvidence {
    pub fn expr(&self) -> &Expr {
        &self.expr
    }

    pub fn inferred_type(&self) -> &Expr {
        &self.inferred_type
    }

    pub fn cert(&self) -> &ProofCert {
        &self.cert
    }

    pub fn replay_match(&self) -> bool {
        self.replay_match
    }

    pub fn micro_match(&self) -> bool {
        self.micro_match
    }
}

/// Error from the `verify_expr` pipeline.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum VerifyError {
    /// Type inference failed (stage 1).
    #[error("type inference failed: {0}")]
    InferFailed(#[from] TypeError),
    /// Certificate replay/verification failed (stage 2).
    #[error("certificate replay failed: {0}")]
    ReplayFailed(#[from] CertError),
    /// Replay produced a type that doesn't match the inferred type (stage 2).
    #[error("replay type mismatch: inferred={inferred:?}, replayed={replayed:?}")]
    ReplayTypeMismatch {
        inferred: Box<Expr>,
        replayed: Box<Expr>,
    },
    /// Micro-checker disagreed with the main kernel (stage 3).
    #[error("micro-checker disagreement: {0}")]
    MicroDisagreement(#[source] CrossValidationError),
}

/// Verify a single expression through the three-stage pipeline.
///
/// 1. Infer type with certificate generation
/// 2. Replay certificate and verify independently
/// 3. Cross-validate with micro-checker (best-effort)
///
/// Returns `VerificationEvidence` on success, `VerifyError` on failure.
///
/// # Contract
///
/// REQUIRES: `expr` contains no unbound `BVar`
/// REQUIRES: All `Const` in `expr` are declared in `env`
/// ENSURES: On success, `evidence.replay_match() == true`
/// ENSURES: On success, `evidence.micro_match()` reflects micro-checker coverage
/// ENSURES: On error, identifies which stage failed
pub fn verify_expr(env: &Environment, expr: &Expr) -> Result<VerificationEvidence, VerifyError> {
    // Stage 1: Infer type with certificate
    let tc = TypeChecker::with_mode(env, env.mode());
    let (inferred_type, cert) = tc.infer_type_with_cert(expr)?;

    // Stage 2: Replay certificate through an independent verifier in the
    // same mode that produced the certificate.
    let mut verifier = CertVerifier::with_mode(env, env.mode());
    let (_reconstructed_expr, replayed_type) = verifier.replay_and_verify(&cert)?;

    // Confirm replay type matches inferred type
    if inferred_type != replayed_type {
        return Err(VerifyError::ReplayTypeMismatch {
            inferred: Box::new(inferred_type),
            replayed: Box::new(replayed_type),
        });
    }

    // Stage 3: Cross-validate with micro-checker (best-effort)
    let micro_match = match cross_validate_with_micro(expr, &inferred_type, &cert) {
        Ok(confirmed) => confirmed,
        Err(e) => return Err(VerifyError::MicroDisagreement(e)),
    };

    Ok(VerificationEvidence {
        expr: expr.clone(),
        inferred_type,
        cert,
        replay_match: true,
        micro_match,
    })
}

/// Statistics from batch verification.
///
/// External crates must obtain this from [`verify_batch`] rather than
/// fabricate a summary with a struct literal.
///
/// ```compile_fail
/// use clean_kernel::verify_api::BatchVerificationStats;
///
/// let _ = BatchVerificationStats {
///     total: 1,
///     passed: 1,
///     failed: 0,
///     micro_confirmed: 1,
///     micro_skipped: 0,
///     errors: vec![],
/// };
/// ```
///
/// ```compile_fail
/// use clean_kernel::verify_api::BatchVerificationStats;
///
/// let _ = BatchVerificationStats::default();
/// ```
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct BatchVerificationStats {
    /// Total expressions submitted.
    pub total: usize,
    /// Expressions that passed all stages.
    pub passed: usize,
    /// Expressions where verification returned an error.
    pub failed: usize,
    /// Expressions where micro-checker confirmed (subset of passed).
    pub micro_confirmed: usize,
    /// Expressions where micro-checker skipped (unsupported constructs).
    pub micro_skipped: usize,
    /// Per-expression errors (index, error message).
    pub errors: Vec<(usize, String)>,
}

impl BatchVerificationStats {
    fn new(total: usize) -> Self {
        Self {
            total,
            passed: 0,
            failed: 0,
            micro_confirmed: 0,
            micro_skipped: 0,
            errors: Vec::new(),
        }
    }

    pub fn total(&self) -> usize {
        self.total
    }

    pub fn passed(&self) -> usize {
        self.passed
    }

    pub fn failed(&self) -> usize {
        self.failed
    }

    pub fn micro_confirmed(&self) -> usize {
        self.micro_confirmed
    }

    pub fn micro_skipped(&self) -> usize {
        self.micro_skipped
    }

    pub fn errors(&self) -> &[(usize, String)] {
        &self.errors
    }

    /// Fraction of expressions that passed verification (0.0 to 1.0).
    pub fn pass_rate(&self) -> f64 {
        if self.total == 0 {
            return 0.0;
        }
        self.passed as f64 / self.total as f64
    }

    /// Fraction of passed expressions that micro-checker confirmed.
    pub fn micro_coverage(&self) -> f64 {
        if self.passed == 0 {
            return 0.0;
        }
        self.micro_confirmed as f64 / self.passed as f64
    }
}

/// Verify a batch of expressions and collect statistics.
///
/// Runs `verify_expr` on each expression. Does not short-circuit on failure;
/// collects all results for comprehensive reporting.
pub fn verify_batch(env: &Environment, exprs: &[Expr]) -> BatchVerificationStats {
    let mut stats = BatchVerificationStats::new(exprs.len());

    for (i, expr) in exprs.iter().enumerate() {
        match verify_expr(env, expr) {
            Ok(evidence) => {
                stats.passed += 1;
                if evidence.micro_match() {
                    stats.micro_confirmed += 1;
                } else {
                    stats.micro_skipped += 1;
                }
            }
            Err(e) => {
                stats.failed += 1;
                stats.errors.push((i, e.to_string()));
            }
        }
    }

    stats
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::BinderInfo;
    use crate::level::Level;
    use crate::mode::CleanMode;
    use crate::name::Name;

    fn test_env() -> Environment {
        Environment::new()
    }

    // --- verify_expr tests ---

    #[test]
    fn test_verify_sort_prop() {
        let env = test_env();
        let prop = Expr::sort(Level::zero());
        let evidence = verify_expr(&env, &prop).expect("Sort Prop should verify");
        assert!(evidence.replay_match());
        assert_eq!(
            evidence.inferred_type(),
            &Expr::sort(Level::succ(Level::zero()))
        );
    }

    #[test]
    fn test_verify_sort_type() {
        let env = test_env();
        let type0 = Expr::sort(Level::succ(Level::zero()));
        let evidence = verify_expr(&env, &type0).expect("Sort Type should verify");
        assert!(evidence.replay_match());
        assert_eq!(
            evidence.inferred_type(),
            &Expr::sort(Level::succ(Level::succ(Level::zero())))
        );
    }

    #[test]
    fn test_verify_lambda_identity() {
        let env = test_env();
        // λ (x : Prop) => x
        let prop = Expr::sort(Level::zero());
        let identity = Expr::lam(BinderInfo::Default, prop.clone(), Expr::bvar(0));
        let evidence = verify_expr(&env, &identity).expect("identity λ should verify");
        assert!(evidence.replay_match());
    }

    #[test]
    fn test_verify_pi_type() {
        let env = test_env();
        // ∀ (x : Prop), Prop
        let prop = Expr::sort(Level::zero());
        let pi = Expr::pi(BinderInfo::Default, prop.clone(), prop.clone());
        let evidence = verify_expr(&env, &pi).expect("Pi type should verify");
        assert!(evidence.replay_match());
    }

    #[test]
    fn test_verify_let_binding() {
        let env = test_env();
        // let _ : Type := Prop in #0
        // Prop : Type (Sort(0) : Sort(1)), so Type annotation matches.
        let prop = Expr::sort(Level::zero());
        let type0 = Expr::sort(Level::succ(Level::zero()));
        let let_expr = Expr::let_named(Name::anon(), type0, prop, Expr::bvar(0), false);
        let evidence = verify_expr(&env, &let_expr).expect("let binding should verify");
        assert!(evidence.replay_match());
    }

    #[test]
    fn test_verify_unbound_const_fails() {
        let env = test_env();
        // Const "Foo" not declared in empty env → should fail
        let bad_const = Expr::const_(Name::from_string("Foo"), vec![]);
        let err =
            verify_expr(&env, &bad_const).expect_err("unbound const Foo should fail verification");
        assert!(
            matches!(err, VerifyError::InferFailed(_)),
            "expected InferFailed for unbound const, got {err:?}"
        );
    }

    #[test]
    fn test_verify_nested_lambda() {
        let env = test_env();
        // λ (A : Type) (x : A) => x
        let type0 = Expr::sort(Level::succ(Level::zero()));
        let outer = Expr::lam(
            BinderInfo::Default,
            type0,
            Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
        );
        let evidence = verify_expr(&env, &outer).expect("nested λ should verify");
        assert!(evidence.replay_match());
    }

    #[test]
    fn test_verify_app() {
        let env = test_env();
        // (λ (A : Type) => A) Prop — identity on types applied to Prop
        let type0 = Expr::sort(Level::succ(Level::zero()));
        let prop = Expr::sort(Level::zero());
        let id_fn = Expr::lam(BinderInfo::Default, type0, Expr::bvar(0));
        let app = Expr::app(id_fn, prop);
        let evidence = verify_expr(&env, &app).expect("application should verify");
        assert!(evidence.replay_match());
    }

    #[test]
    fn test_verify_cubical_interval_uses_environment_mode() {
        let env = Environment::with_mode(CleanMode::Cubical);
        let interval = Expr::from_kind(crate::expr::ExprKind::CubicalInterval);

        let evidence =
            verify_expr(&env, &interval).expect("verify_expr should preserve cubical mode");

        assert!(evidence.replay_match());
        assert_eq!(
            evidence.inferred_type(),
            &Expr::sort(Level::succ(Level::zero()))
        );
    }

    // --- verify_batch tests ---

    #[test]
    fn test_verify_batch_all_pass() {
        let env = test_env();
        let exprs = vec![
            Expr::sort(Level::zero()),
            Expr::sort(Level::succ(Level::zero())),
        ];
        let stats = verify_batch(&env, &exprs);
        assert_eq!(stats.total(), 2);
        assert_eq!(stats.passed(), 2);
        assert_eq!(stats.failed(), 0);
        assert!((stats.pass_rate() - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_verify_batch_mixed() {
        let env = test_env();
        let exprs = vec![
            Expr::sort(Level::zero()),                        // pass
            Expr::const_(Name::from_string("Bogus"), vec![]), // fail: undeclared
        ];
        let stats = verify_batch(&env, &exprs);
        assert_eq!(stats.total(), 2);
        assert_eq!(stats.passed(), 1);
        assert_eq!(stats.failed(), 1);
        assert_eq!(stats.errors().len(), 1);
        assert_eq!(stats.errors()[0].0, 1);
    }

    #[test]
    fn test_verify_batch_empty() {
        let env = test_env();
        let stats = verify_batch(&env, &[]);
        assert_eq!(stats.total(), 0);
        assert_eq!(stats.passed(), 0);
        assert!((stats.pass_rate() - 0.0).abs() < f64::EPSILON);
        assert!((stats.micro_coverage() - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_batch_stats_micro_coverage() {
        let env = test_env();
        let exprs = vec![
            Expr::sort(Level::zero()),
            Expr::sort(Level::succ(Level::zero())),
            Expr::sort(Level::succ(Level::succ(Level::zero()))),
        ];
        let stats = verify_batch(&env, &exprs);
        assert_eq!(stats.passed(), 3);
        assert!(stats.micro_confirmed() + stats.micro_skipped() == stats.passed());
    }

    #[test]
    fn test_batch_pass_rate() {
        let stats = BatchVerificationStats {
            total: 10,
            passed: 7,
            failed: 3,
            micro_confirmed: 5,
            micro_skipped: 2,
            errors: vec![],
        };
        assert!((stats.pass_rate() - 0.7).abs() < f64::EPSILON);
        assert!((stats.micro_coverage() - 5.0 / 7.0).abs() < f64::EPSILON);
    }
}

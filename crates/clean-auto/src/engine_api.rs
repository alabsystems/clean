// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Detailed request/result surface for [`crate::AutomationEngine`].

use crate::bridge::QuantifierOrigin;
use crate::oracle::{OracleCandidateRunner, ProofOracle};
use crate::premise::PremiseDatabase;
use crate::ProofResult;
use clean_kernel::{Expr, LocalContext};
use std::time::Duration;

/// Which automation strategy produced the current outcome.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[must_use]
pub enum AutomationSource {
    /// SMT bridge / DPLL(T) solving.
    Smt,
    /// Saturation-based first-order proving.
    Superposition,
    /// Oracle-generated tactic scripts verified by the runner.
    Oracle,
}

/// Detailed result from automatic proof search.
#[derive(Debug)]
#[must_use]
#[non_exhaustive]
pub enum AutomationOutcome {
    /// A kernel-verifiable proof was found.
    Verified(Box<ProofResult>),
    /// A strategy established useful information but not a verified proof.
    Unverified {
        /// Human-readable explanation for the non-proof result.
        reason: String,
        /// Strategy that produced the outcome.
        source: AutomationSource,
        /// End-to-end time spent before returning.
        time_ms: u64,
    },
    /// A solver found a counterexample / refutation.
    Refuted {
        /// Strategy that produced the outcome.
        source: AutomationSource,
        /// End-to-end time spent before returning.
        time_ms: u64,
    },
    /// Automation exhausted the requested strategies without a proof.
    Unknown {
        /// Human-readable explanation for the non-proof result.
        reason: String,
        /// Strategy that produced the outcome.
        source: AutomationSource,
        /// End-to-end time spent before returning.
        time_ms: u64,
    },
}

impl AutomationOutcome {
    /// Extract the verified proof, if any.
    ///
    /// This helper exists for compatibility wrappers. New call sites should
    /// match on [`AutomationOutcome`] directly so non-proof states stay visible.
    pub fn verified(self) -> Option<ProofResult> {
        match self {
            Self::Verified(result) => Some(*result),
            Self::Unverified { .. } | Self::Refuted { .. } | Self::Unknown { .. } => None,
        }
    }
}

/// Structured automation request with public fields (semver-frozen).
///
/// New call sites should prefer [`AutomationQuery`], which has private fields
/// and can accept future options without semver breakage. This type remains
/// for backward compatibility and converts via `From<AutomationRequest>`.
#[must_use]
pub struct AutomationRequest<'a> {
    /// Goal to prove.
    pub goal: &'a Expr,
    /// Global budget for the search.
    pub timeout: Duration,
    /// Optional caller-owned local context for hypothesis names/FVarIds.
    pub local_ctx: Option<&'a LocalContext>,
    /// Hypotheses available to automation strategies.
    pub hypotheses: &'a [(Expr, Option<QuantifierOrigin>)],
    /// Optional MePo premise database for SMT scoring.
    pub premise_db: Option<&'a PremiseDatabase>,
    /// Optional proof oracle.
    pub oracle: Option<&'a dyn ProofOracle>,
    /// Candidate executor for oracle tactic scripts.
    pub oracle_runner: Option<&'a dyn OracleCandidateRunner>,
}

/// Forward-compatible automation query with private fields and builder pattern.
///
/// Unlike [`AutomationRequest`], this type's fields are private, so adding new
/// options in future versions is not a semver-breaking change. New call sites
/// should prefer this type; existing [`AutomationRequest`] callers continue to
/// work via [`From`] conversion.
///
/// # Example
///
/// ```text
/// use clean_auto::{AutomationEngine, AutomationOutcome, AutomationQuery};
///
/// let engine = AutomationEngine::new();
/// let query = AutomationQuery::new(&goal, timeout)
///     .with_hypotheses(&hypotheses)
///     .with_local_ctx(&local_ctx);
/// match engine.auto_prove_with_query(&env, query) {
///     AutomationOutcome::Verified(proof) => { /* ... */ }
///     _ => {}
/// }
/// ```
#[must_use]
pub struct AutomationQuery<'a> {
    pub(crate) goal: &'a Expr,
    pub(crate) timeout: Duration,
    pub(crate) local_ctx: Option<&'a LocalContext>,
    pub(crate) hypotheses: &'a [(Expr, Option<QuantifierOrigin>)],
    pub(crate) premise_db: Option<&'a PremiseDatabase>,
    pub(crate) oracle: Option<&'a dyn ProofOracle>,
    pub(crate) oracle_runner: Option<&'a dyn OracleCandidateRunner>,
}

impl<'a> AutomationQuery<'a> {
    /// Create a minimal query for a single goal.
    pub fn new(goal: &'a Expr, timeout: Duration) -> Self {
        Self {
            goal,
            timeout,
            local_ctx: None,
            hypotheses: &[],
            premise_db: None,
            oracle: None,
            oracle_runner: None,
        }
    }

    /// Supply the local context that owns hypothesis names and FVarIds.
    pub fn with_local_ctx(mut self, local_ctx: &'a LocalContext) -> Self {
        self.local_ctx = Some(local_ctx);
        self
    }

    /// Supply explicit hypotheses for SMT/superposition scoring.
    pub fn with_hypotheses(mut self, hypotheses: &'a [(Expr, Option<QuantifierOrigin>)]) -> Self {
        self.hypotheses = hypotheses;
        self
    }

    /// Supply a premise database for MePo scoring.
    pub fn with_premise_db(mut self, premise_db: &'a PremiseDatabase) -> Self {
        self.premise_db = Some(premise_db);
        self
    }

    /// Supply an oracle and the runner used to verify returned candidates.
    pub fn with_oracle(
        mut self,
        oracle: &'a dyn ProofOracle,
        oracle_runner: &'a dyn OracleCandidateRunner,
    ) -> Self {
        self.oracle = Some(oracle);
        self.oracle_runner = Some(oracle_runner);
        self
    }

    /// Supply an oracle that produces proof terms directly.
    ///
    /// Unlike [`Self::with_oracle`], this does not require an
    /// [`OracleCandidateRunner`]. The engine validates returned proof terms
    /// through the kernel type checker. Tactic candidates from
    /// [`ProofOracle::suggest_proof`] are ignored when no runner is provided.
    pub fn with_proof_term_oracle(mut self, oracle: &'a dyn ProofOracle) -> Self {
        self.oracle = Some(oracle);
        self
    }

    /// The goal expression to prove.
    pub fn goal(&self) -> &Expr {
        self.goal
    }

    /// The global budget for the search.
    pub fn timeout(&self) -> Duration {
        self.timeout
    }

    /// The caller-owned local context, if any.
    pub fn local_ctx(&self) -> Option<&LocalContext> {
        self.local_ctx
    }

    /// The hypotheses available to automation strategies.
    pub fn hypotheses(&self) -> &[(Expr, Option<QuantifierOrigin>)] {
        self.hypotheses
    }

    /// The premise database for MePo scoring, if any.
    pub fn premise_db(&self) -> Option<&PremiseDatabase> {
        self.premise_db
    }
}

impl<'a> From<AutomationRequest<'a>> for AutomationQuery<'a> {
    fn from(request: AutomationRequest<'a>) -> Self {
        Self {
            goal: request.goal,
            timeout: request.timeout,
            local_ctx: request.local_ctx,
            hypotheses: request.hypotheses,
            premise_db: request.premise_db,
            oracle: request.oracle,
            oracle_runner: request.oracle_runner,
        }
    }
}

impl<'a> AutomationRequest<'a> {
    /// Create a minimal request for a single goal.
    pub fn new(goal: &'a Expr, timeout: Duration) -> Self {
        Self {
            goal,
            timeout,
            local_ctx: None,
            hypotheses: &[],
            premise_db: None,
            oracle: None,
            oracle_runner: None,
        }
    }

    /// Supply the local context that owns hypothesis names and FVarIds.
    pub fn with_local_ctx(mut self, local_ctx: &'a LocalContext) -> Self {
        self.local_ctx = Some(local_ctx);
        self
    }

    /// Supply explicit hypotheses for SMT/superposition scoring.
    pub fn with_hypotheses(mut self, hypotheses: &'a [(Expr, Option<QuantifierOrigin>)]) -> Self {
        self.hypotheses = hypotheses;
        self
    }

    /// Supply a premise database for MePo scoring.
    pub fn with_premise_db(mut self, premise_db: &'a PremiseDatabase) -> Self {
        self.premise_db = Some(premise_db);
        self
    }

    /// Supply an oracle and the runner used to verify returned candidates.
    pub fn with_oracle(
        mut self,
        oracle: &'a dyn ProofOracle,
        oracle_runner: &'a dyn OracleCandidateRunner,
    ) -> Self {
        self.oracle = Some(oracle);
        self.oracle_runner = Some(oracle_runner);
        self
    }

    /// Supply an oracle that produces proof terms directly.
    ///
    /// Unlike [`Self::with_oracle`], this does not require an
    /// [`OracleCandidateRunner`]. The engine validates returned proof terms
    /// through the kernel type checker. Tactic candidates from
    /// [`ProofOracle::suggest_proof`] are ignored when no runner is provided.
    pub fn with_proof_term_oracle(mut self, oracle: &'a dyn ProofOracle) -> Self {
        self.oracle = Some(oracle);
        self
    }
}

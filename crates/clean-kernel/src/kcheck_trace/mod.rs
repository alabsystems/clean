// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! C4 experimental building blocks, excluded from normal builds.
//!
//! This module does NOT emit declaration advice or establish R2/R3. In
//! particular, its token journal is not an advice certificate. Neither ordinary
//! checking nor `ReferenceKernel` calls this module. See the C4 report for the
//! remaining inference/reduction work; do not derive R2/R3 from this API.
pub mod core;
pub mod term;
use term::{Label, Node, Term};

/// The tags named in design section 3.2. Operands/encoding are still owed by C4.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Token {
    /// Declaration's supplied depth bound (Revision 1).
    Depth(u64),
    /// Iota step with recursor/constructor spine certificates.
    Iota,
    /// K step with a spine and index comparison.
    K,
    /// All labels match syntactically; arity is diagnostic metadata, not an operand.
    SpineRefl(u64),
    /// One conversion certificate for each argument in a telescope.
    SpineCerts(u64),
    /// Erasure equality.
    Refl,
    /// Universe-sort equality.
    Sort,
    /// Constant equality.
    Const,
    /// Application congruence.
    App,
    /// Lambda congruence.
    Lam,
    /// Pi congruence.
    Pi,
    /// Non-delta head steps on the left.
    CoreL(u64),
    /// Non-delta head steps on the right.
    CoreR(u64),
    /// Beta domain comparison.
    Dom,
    /// Left delta step.
    DeltaL,
    /// Right delta step.
    DeltaR,
    /// Paired delta step.
    DeltaBoth,
    /// Left eta.
    EtaL,
    /// Right eta.
    EtaR,
    /// Proof irrelevance.
    Irrel,
    /// Declaration-local equation reference.
    Memo(u64),
    /// End of WHNF.
    Stop,
}

/// Declaration-owned journal. Failed speculative work is rolled back even when
/// it contains nested successful branches. Dropping the journal ends its scope.
#[derive(Default, Debug)]
pub struct Journal {
    tokens: Vec<Token>,
}
impl Journal {
    /// Append a successful rule.
    pub fn push(&mut self, token: Token) {
        self.tokens.push(token);
    }
    /// Inspect successful-path tokens.
    pub fn tokens(&self) -> &[Token] {
        &self.tokens
    }
    /// Retain a branch only if it succeeds. The caller's error is preserved.
    pub fn attempt<T, E>(
        &mut self,
        branch: impl FnOnce(&mut Self) -> Result<T, E>,
    ) -> Result<T, E> {
        let mark = self.tokens.len();
        let result = branch(self);
        if result.is_err() {
            self.tokens.truncate(mark);
        }
        result
    }
}

/// Result of the local DOM test. A failed comparison prevents contraction.
/// Level-only provenance compares diagnostic pre-instantiation syntax carried
/// through the same term substitutions as the actual labelled domains.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub enum DomainClass {
    /// Identical after erasure, at the current universe instantiation.
    Identical,
    /// The domains agree only after the recorded universe instantiations.
    LevelInstantiated,
    /// Conversion succeeded; count is supplied by the conversion journal.
    Convertible { steps: u64 },
    /// Conversion refused, with its reason.
    Failed(String),
    /// The application was not annotated, with its construction's name.
    Missing(String),
}

/// Inspect one exposed beta redex and contract only after DOM succeeds. The
/// conversion callback must compare the ACTUAL stored label and binder domain;
/// re-inferring the argument here would measure a different design.
///
/// `None` means the input is not an exposed beta redex. A `Missing` or `Failed`
/// result has no reduct. Labels in the returned body move through substitution.
pub fn beta(
    redex: &Term,
    journal: &mut Journal,
    mut conv: impl FnMut(&Term, &Term, &mut Journal) -> Result<u64, String>,
) -> Option<(DomainClass, Option<Term>)> {
    let Node::App(function, argument, label) = redex.0.as_ref() else {
        return None;
    };
    let Node::Lam(_, domain, body) = function.0.as_ref() else {
        return None;
    };
    let label = match label {
        Label::Checked(d) => d,
        Label::Missing(source) => return Some((DomainClass::Missing(source.clone()), None)),
    };
    let result = journal.attempt(|journal| {
        journal.push(Token::Dom);
        if label.erased_eq(domain) {
            journal.push(Token::Refl);
            Ok(if label.before_levels() == domain.before_levels() {
                DomainClass::Identical
            } else {
                DomainClass::LevelInstantiated
            })
        } else {
            conv(label, domain, journal).map(|steps| DomainClass::Convertible { steps })
        }
    });
    Some(match result {
        Ok(class) => (class, Some(body.instantiate(argument))),
        Err(reason) => (DomainClass::Failed(reason), None),
    })
}

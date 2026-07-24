// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof term closing: FVar → BVar conversion.
//!
//! When tactics like `intro` run, they introduce free variables (FVars) to
//! represent bound variables. After metavariable instantiation, the proof term
//! still contains these FVars. This module converts them back to bound variables
//! (BVars) so the result is a proper closed term suitable for type checking.

use crate::stack_safe;
use crate::unify::{MetaId, MetaState};
use clean_kernel::{Expr, ExprFolder, ExprKind, FVarId};
use std::collections::HashSet;

/// Validate the local-scope authority of a raw metavariable assignment.
///
/// Ordinary FVars may come only from the destination metavariable's immutable
/// creation scope, unless they are structurally bound by a lambda/Pi/let that
/// occurs in the assigned term itself.  An unassigned nested metavariable is
/// subject to the same rule: every local it captured must be available at the
/// point where the nested metavariable occurs.  This closes the delayed-escape
/// seam where `?outer := ?inner` looked locally closed but `?inner` could later
/// reveal a local that was never in `?outer`'s creation scope.
///
/// `proof` must already have assigned metavariables instantiated.  This keeps
/// the check precise: a solved wider metavariable is judged by its actual
/// assignment, while an open one is conservatively judged by its captured
/// scope.
pub(super) fn assignment_scope_violation(
    proof: &Expr,
    allowed: &HashSet<FVarId>,
    metas: &MetaState,
    binder_base: u64,
    limit: u64,
) -> Option<String> {
    struct ScopeFinder<'a> {
        allowed: &'a HashSet<FVarId>,
        metas: &'a MetaState,
        binder_base: u64,
        limit: u64,
        depth: u64,
        inspected_metas: HashSet<(MetaId, u64)>,
        violation: Option<String>,
    }

    impl ScopeFinder<'_> {
        fn structurally_bound(&self, id: FVarId) -> bool {
            let n = id.as_u64();
            n >= self.binder_base
                && n < self.limit
                && n.saturating_sub(self.binder_base) < self.depth
        }

        fn permitted(&self, id: FVarId) -> bool {
            self.allowed.contains(&id) || self.structurally_bound(id)
        }
    }

    impl ExprFolder for ScopeFinder<'_> {
        fn fold_binder_body(&mut self, expr: &Expr) -> Expr {
            self.depth += 1;
            let result = self.fold_expr(expr);
            self.depth -= 1;
            result
        }

        fn fold_fvar(&mut self, id: FVarId) -> Expr {
            if self.violation.is_some() {
                return Expr::fvar(id);
            }

            if let Some(meta_id) = MetaState::from_fvar(id) {
                // The same open meta can occur at different binder depths; its
                // captured scope must be legal at every occurrence.
                if self.inspected_metas.insert((meta_id, self.depth)) {
                    if let Some(meta) = self.metas.get(meta_id) {
                        if meta.assignment.is_none() {
                            if let Some((_, escaped, _)) = meta
                                .locals
                                .iter()
                                .find(|(_, local, _)| !self.permitted(*local))
                            {
                                self.violation = Some(format!(
                                    "nested metavariable {meta_id:?} captures out-of-scope local {escaped:?} at binder depth {}",
                                    self.depth
                                ));
                            }
                        }
                    }
                }
                return Expr::fvar(id);
            }

            if !self.permitted(id) {
                self.violation = Some(format!(
                    "proof captures out-of-scope local {id:?} at binder depth {}",
                    self.depth
                ));
            }
            Expr::fvar(id)
        }
    }

    let mut finder = ScopeFinder {
        allowed,
        metas,
        binder_base,
        limit,
        depth: 0,
        inspected_metas: HashSet::new(),
        violation: None,
    };
    let _ = finder.fold_expr(proof);
    finder.violation
}

/// ExprFolder that converts FVars to BVars based on binder depth.
///
/// FVar IDs correspond to binder depth: FVar(0) is the outermost, FVar(1) next, etc.
/// The `fold_binder_body` override tracks depth through binders (Lam, Pi, Let,
/// CubicalPathLam, ZFCComprehension/Separation/Replacement predicates).
///
/// # Invariant (#2204)
///
/// The FVar-to-BVar mapping assumes tactic FVar IDs are sequential from `base`
/// and each corresponds to exactly one binder in the proof term. If a
/// tactic-scope FVar (id >= base) is encountered at a depth where it cannot be
/// converted, it indicates a gap in the ID-to-binder correspondence — the FVar
/// was allocated but has no matching binder above it.
struct CloseFvarsFolder {
    depth: u64,
    /// Base FVar ID: only FVars with id >= base are considered tactic-created
    /// and eligible for closing. FVars below base are elaborator-scope (#2212).
    base: u64,
    /// Upper bound (exclusive) of tactic-created FVar IDs (#2204).
    /// When set, enables gap detection for FVars in [base, limit) that
    /// fall outside the convertible range.
    limit: u64,
    /// Set to `true` when a tactic-scope FVar (id in `[base, limit)`) is
    /// encountered at a depth where it cannot be converted to a BVar — i.e.
    /// the FVar was allocated but has no matching binder above it in the
    /// assembled proof term (an ID-to-binder gap, #2204). When this is set the
    /// closed term is NOT sound: the caller MUST reject the proof (fail closed)
    /// rather than hand a term with residual free variables to the kernel.
    ///
    /// Historically this condition tripped a `debug_assert!` that aborted the
    /// worker thread. A checker that panics on a genuinely-malformed proof term
    /// is a robustness failure; the diagnostic is preserved via
    /// [`CloseFvarsFolder::gap_diagnostic`] and surfaced as a normal
    /// elaboration `Err` instead. The proof is still refused — never accepted.
    gap_detected: bool,
    /// Diagnostic for the first gap encountered (the `{n}`, depth, base, limit
    /// that previously appeared in the `debug_assert!` message), for logging.
    gap_diagnostic: Option<String>,
}

impl ExprFolder for CloseFvarsFolder {
    fn fold_binder_body(&mut self, expr: &Expr) -> Expr {
        self.depth += 1;
        let result = self.fold_expr(expr);
        self.depth -= 1;
        result
    }

    fn fold_fvar(&mut self, id: FVarId) -> Expr {
        let n = id.as_u64();
        if n >= self.base && (n - self.base) < self.depth {
            #[allow(clippy::cast_possible_truncation)]
            let idx = (self.depth - 1 - (n - self.base)) as u32;
            Expr::bvar(idx)
        } else {
            // #2204: detect tactic-scope FVars that weren't converted.
            // A tactic FVar (base <= id < limit) that exceeds the current
            // binder depth has no matching binder — this is a mapping gap.
            // FAIL CLOSED: record the gap so the caller returns an Err/None
            // instead of panicking or accepting a term with a residual FVar.
            let is_tactic_gap = n >= self.base && n < self.limit && self.limit != 0;
            if is_tactic_gap {
                self.gap_detected = true;
                if self.gap_diagnostic.is_none() {
                    self.gap_diagnostic = Some(format!(
                        "close_fvars: tactic FVar({n}) not converted at depth {} \
                         (base={}, limit={}). This FVar has no matching binder — \
                         possible ID-to-binder gap.",
                        self.depth, self.base, self.limit,
                    ));
                }
            }
            Expr::fvar(id)
        }
    }
}

/// Outcome of a validated close: the closed term plus whether any tactic-scope
/// FVar was left unconverted (an ID-to-binder gap). When `gap` is `Some`, the
/// term is unsound (contains a residual free variable) and the caller MUST
/// reject the proof.
pub(crate) struct CloseOutcome {
    pub(crate) closed: Expr,
    /// `Some(diagnostic)` if a tactic-scope FVar had no matching binder.
    pub(crate) gap: Option<String>,
}

/// Close a proof term by converting FVars to BVars.
///
/// The conversion assumes FVar IDs correspond to binder depth in the order they
/// were introduced: FVar(base) is bound by the outermost binder, FVar(base+1) by
/// the next, etc. FVars with IDs below `base` are elaborator-scope and preserved.
///
/// # Arguments
/// * `expr` - The expression to close
/// * `depth` - Current binder depth (number of enclosing binders), starts at 0
///
/// # Contract
///
/// REQUIRES: `depth` matches the number of enclosing binders above `expr`
/// ENSURES: All FVars with id in `[0, depth)` are converted to BVar indices
/// ENSURES: FVars outside `[0, depth)` are preserved unchanged
/// ENSURES: Result contains no tactic-scope FVars that had matching binders
#[cfg(test)]
pub(crate) fn close_fvars(expr: &Expr, depth: u64) -> Expr {
    CloseFvarsFolder {
        depth,
        base: 0,
        limit: 0,
        gap_detected: false,
        gap_diagnostic: None,
    }
    .fold_expr(expr)
}

/// Close a proof term converting FVars in `[base, limit)` with validation (#2204).
///
/// Like `close_fvars` but additionally records the upper bound of
/// tactic-created FVar IDs. If any tactic-scope FVar in `[base, limit)` is left
/// unconverted (no matching binder — an ID-to-binder gap), the returned
/// [`CloseOutcome::gap`] is `Some(diagnostic)` and the caller MUST reject the
/// proof (fail closed). Never panics on such a term — a malformed proof is
/// refused via `Err`/`None`, not by aborting the worker thread.
///
/// # Contract
///
/// REQUIRES: `base` <= `limit`
/// REQUIRES: `depth` matches the number of enclosing binders above `expr`
/// ENSURES: FVars in `[base, base+depth)` are converted to BVar indices
/// ENSURES: `gap` is `Some` iff a tactic-scope FVar in `[base, limit)` had no
///          matching binder (in which case `closed` still contains that FVar)
pub(crate) fn close_fvars_validated(
    expr: &Expr,
    depth: u64,
    base: u64,
    limit: u64,
) -> CloseOutcome {
    let mut folder = CloseFvarsFolder {
        depth,
        base,
        limit,
        gap_detected: false,
        gap_diagnostic: None,
    };
    let closed = folder.fold_expr(expr);
    CloseOutcome {
        closed,
        gap: if folder.gap_detected {
            folder.gap_diagnostic
        } else {
            None
        },
    }
}

/// Check whether `expr` contains any FVar with id in `[base, limit)` (#2204).
///
/// Returns `true` if a tactic-scope FVar is found — meaning `close_fvars`
/// failed to convert it. Caller should use `has_fvar_quick()` as a fast
/// guard before calling this.
///
/// # Contract
///
/// REQUIRES: `base` <= `limit`
/// ENSURES: Returns true iff `expr` contains any FVar with id in `[base, limit)`
/// ENSURES: Recursively traverses App, Lam, Pi, Let, Proj, MData, Squash nodes
pub(super) fn contains_tactic_fvar(expr: &Expr, base: u64, limit: u64) -> bool {
    stack_safe(|| match expr.kind() {
        ExprKind::FVar(id) => {
            let n = id.as_u64();
            n >= base && n < limit
        }
        ExprKind::App(f, a) => {
            contains_tactic_fvar(f, base, limit) || contains_tactic_fvar(a, base, limit)
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            contains_tactic_fvar(ty, base, limit) || contains_tactic_fvar(body, base, limit)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            contains_tactic_fvar(ty, base, limit)
                || contains_tactic_fvar(val, base, limit)
                || contains_tactic_fvar(body, base, limit)
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
            contains_tactic_fvar(inner, base, limit)
        }
        ExprKind::Sort(_) | ExprKind::BVar(_) | ExprKind::Const(_, _) | ExprKind::Lit(_) => false,
        _ => {
            // ZFC, Cubical, etc. don't appear in tactic proof terms.
            // Option A (fold_fvar debug_assert) catches any FVars in these
            // variants during the close pass; this is a redundant check.
            false
        }
    })
}

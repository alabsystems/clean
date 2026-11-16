// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Temporal operator construction/extraction and fixed-point induction/coinduction.

use super::TlaTacticEngine;
use crate::TlaError;
use clean_elab::tactic::{simp, SimpConfig};
use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind};

impl TlaTacticEngine {
    /// Try least fixed point induction (for Eventually)
    ///
    /// To prove ∀x ∈ lfp(D,f). P(x), show:
    /// 1. Base: ∀x ∈ ∅. P(x) (trivially true)
    /// 2. Step: ∀S. (∀x ∈ S. P(x)) → (∀x ∈ f(S). P(x))
    pub(crate) fn try_lfp_induction(&self, goal: &Expr) -> Result<Option<String>, TlaError> {
        // Peel off non-dependent Π-bindings introduced by sequent encoding.
        if let ExprKind::Pi(_, _, body) = goal.kind() {
            if !body.has_loose_bvars() {
                return self.try_lfp_induction(body);
            }
        }

        // Check if goal is ◇P
        if let Some(inner) = self.extract_eventually(goal) {
            if self.trace {
                eprintln!("[TLA] lfp_induction: goal is Eventually, trying induction on lfp");
            }

            // For ◇P, we use lfp induction:
            // Base: P holds now (disjunct 1)
            // Step: ◇P holds in next state (disjunct 2)

            // Try to prove P directly (base case)
            let mut state = self.make_proof_state(&inner);
            match simp(&mut state, SimpConfig::new()) {
                Ok(()) if state.is_complete() => {
                    return Ok(Some(self.generate_certificate("lfp_induction_base")));
                }
                _ => {}
            }

            // Try superposition on inner
            if let Some(cert) = self.try_superposition(&inner)? {
                return Ok(Some(format!(
                    "{{\"tactic\":\"lfp_induction\",\"inner\":{},\"status\":\"proved\"}}",
                    cert
                )));
            }

            // If P is True, goal is trivially provable
            if self.is_trivially_true(&inner) {
                return Ok(Some(self.generate_certificate("lfp_induction_trivial")));
            }

            Ok(None)
        } else {
            // Not an Eventually goal, induction doesn't apply
            Ok(None)
        }
    }

    /// Try greatest fixed point coinduction (for Always)
    ///
    /// To prove x ∈ gfp(D,f):
    /// 1. Find/construct invariant S with x ∈ S
    /// 2. Show: S ⊆ f(S) (S is post-fixed point)
    ///
    /// For □P specifically, we need:
    /// 1. P holds at current state (base case)
    /// 2. P → ○P (P is inductive - holds at next state if it holds now)
    pub(crate) fn try_gfp_coinduction(&self, goal: &Expr) -> Result<Option<String>, TlaError> {
        // Peel off non-dependent Π-bindings introduced by sequent encoding.
        if let ExprKind::Pi(_, _, body) = goal.kind() {
            if !body.has_loose_bvars() {
                return self.try_gfp_coinduction(body);
            }
        }

        // Check if goal is □P
        if let Some(inner) = self.extract_always(goal) {
            if self.trace {
                eprintln!("[TLA] gfp_coinduction: goal is Always, trying coinduction on gfp");
            }

            // For □P, we need to prove BOTH:
            // 1. P holds at current state (base case)
            // 2. P → ○P (inductiveness - P is preserved by transitions)
            //
            // Previously this was UNSOUND: it only checked (1) and concluded □P

            // Step 1: Check if P holds at current state
            let mut base_state = self.make_proof_state(&inner);
            let base_holds = match simp(&mut base_state, SimpConfig::new()) {
                Ok(()) if base_state.is_complete() => true,
                _ => self.is_trivially_true(&inner),
            };

            if !base_holds {
                // Can't prove base case, try superposition
                if let Some(_cert) = self.try_superposition(&inner)? {
                    // Even if superposition proves P, we still need inductiveness
                    // For now, we're conservative and don't claim □P without inductiveness
                    if self.trace {
                        eprintln!(
                            "[TLA] gfp_coinduction: P proved by superposition, but inductiveness not verified"
                        );
                    }
                    // Note: We could return here if we also verified inductiveness via superposition
                }
                return Ok(None);
            }

            // Step 2: Check inductiveness (P → ○P)
            // Build the next-state version of P: ○P
            let next_p = self.build_next(inner.clone());

            // Build the implication P → ○P
            let inductiveness = Expr::arrow(inner.clone(), next_p);

            // Try to prove inductiveness
            let mut inductive_state = self.make_proof_state(&inductiveness);
            let inductive_holds = match simp(&mut inductive_state, SimpConfig::new()) {
                Ok(()) if inductive_state.is_complete() => true,
                _ => {
                    // Try superposition for inductiveness
                    self.try_superposition(&inductiveness)?.is_some()
                }
            };

            if !inductive_holds {
                if self.trace {
                    eprintln!(
                        "[TLA] gfp_coinduction: Base case proved but inductiveness check failed"
                    );
                }
                return Ok(None);
            }

            // Both base case and inductiveness proved - □P is valid
            Ok(Some(self.generate_certificate("gfp_coinduction")))
        } else {
            // Not an Always goal, coinduction doesn't apply
            Ok(None)
        }
    }

    /// Build ○P (next-state version of P)
    /// This applies TLA_next to the formula
    pub(crate) fn build_next(&self, p: Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("FixedPoint.TLA_next"), vec![]),
            p,
        )
    }

    // ================================================================
    // Temporal operator extraction helpers
    // ================================================================

    /// Extract inner formula from TLA_always application
    /// Returns Some(P) if goal is FixedPoint.TLA_always P
    pub(crate) fn extract_always(&self, expr: &Expr) -> Option<Expr> {
        if let ExprKind::App(f, arg) = expr.kind() {
            if let ExprKind::Const(name, _) = f.kind() {
                if name.to_string() == "FixedPoint.TLA_always" {
                    return Some(arg.as_ref().clone());
                }
            }
        }
        None
    }

    /// Extract inner formula from TLA_eventually application
    /// Returns Some(P) if goal is FixedPoint.TLA_eventually P
    pub(crate) fn extract_eventually(&self, expr: &Expr) -> Option<Expr> {
        if let ExprKind::App(f, arg) = expr.kind() {
            if let ExprKind::Const(name, _) = f.kind() {
                if name.to_string() == "FixedPoint.TLA_eventually" {
                    return Some(arg.as_ref().clone());
                }
            }
        }
        None
    }

    /// Extract P and Q from TLA_leads_to application
    /// Returns Some((P, Q)) if goal is FixedPoint.TLA_leads_to P Q
    pub(crate) fn extract_leads_to(&self, expr: &Expr) -> Option<(Expr, Expr)> {
        // leads_to is binary: TLA_leads_to P Q
        if let ExprKind::App(f, q) = expr.kind() {
            if let ExprKind::App(g, p) = f.kind() {
                if let ExprKind::Const(name, _) = g.kind() {
                    if name.to_string() == "FixedPoint.TLA_leads_to" {
                        return Some((p.as_ref().clone(), q.as_ref().clone()));
                    }
                }
            }
        }
        None
    }

    // ================================================================
    // Temporal operator construction helpers
    // ================================================================

    /// Construct TLA_next P (○P)
    pub(crate) fn make_next(&self, p: Expr) -> Expr {
        use clean_kernel::name::Name;
        Expr::app(
            Expr::const_(Name::from_string("FixedPoint.TLA_next"), vec![]),
            p,
        )
    }

    /// Construct TLA_always P (□P)
    pub(crate) fn make_always(&self, p: Expr) -> Expr {
        use clean_kernel::name::Name;
        Expr::app(
            Expr::const_(Name::from_string("FixedPoint.TLA_always"), vec![]),
            p,
        )
    }

    /// Construct TLA_eventually P (◇P)
    pub(crate) fn make_eventually(&self, p: Expr) -> Expr {
        use clean_kernel::name::Name;
        Expr::app(
            Expr::const_(Name::from_string("FixedPoint.TLA_eventually"), vec![]),
            p,
        )
    }

    /// Construct P ∧ Q (conjunction)
    pub(crate) fn make_and(&self, p: Expr, q: Expr) -> Expr {
        use clean_kernel::name::Name;
        Expr::app(
            Expr::app(Expr::const_(Name::from_string("And"), vec![]), p),
            q,
        )
    }

    /// Construct P ∨ Q (disjunction)
    pub(crate) fn make_or(&self, p: Expr, q: Expr) -> Expr {
        use clean_kernel::name::Name;
        Expr::app(
            Expr::app(Expr::const_(Name::from_string("Or"), vec![]), p),
            q,
        )
    }

    /// Unfold □P to P ∧ ○(□P)
    pub(crate) fn unfold_always(&self, always_expr: &Expr) -> Option<Expr> {
        self.extract_always(always_expr).map(|p| {
            // □P = P ∧ ○(□P)
            let next_always_p = self.make_next(self.make_always(p.clone()));
            self.make_and(p, next_always_p)
        })
    }

    /// Unfold ◇P to P ∨ ○(◇P)
    pub(crate) fn unfold_eventually(&self, eventually_expr: &Expr) -> Option<Expr> {
        self.extract_eventually(eventually_expr).map(|p| {
            // ◇P = P ∨ ○(◇P)
            let next_eventually_p = self.make_next(self.make_eventually(p.clone()));
            self.make_or(p, next_eventually_p)
        })
    }
}

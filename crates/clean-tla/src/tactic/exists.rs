// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Existential instantiation for TLA+ goals.
//!
//! To prove an existential goal `∃ x : P(x)` it suffices to exhibit a *witness*
//! `t` together with a proof of `P(t)`. This module implements a focused,
//! *sound* witness search for the cases that arise most often in TLA+
//! obligations:
//!
//! 1. **Equality witness.** For `∃ x : x = t` (or `∃ x : t = x`) where `t` does
//!    not mention the bound variable, the witness is `t` itself: substituting
//!    gives `t = t`, which is reflexively true. This is the canonical
//!    "choose the obvious value" instantiation.
//! 2. **Hypothesis witness.** For `∃ x : P(x)` where some hypothesis in the
//!    sequent already states `P(w)` for a concrete witness `w`, the witness is
//!    `w`: the discharged obligation `P(w)` is literally one of the
//!    assumptions.
//!
//! In both cases the witness is only emitted when the residual obligation
//! `P(witness)` is *genuinely* discharged (reflexivity or an exact hypothesis
//! match). A goal such as `∃ x : odd(x)` with no supporting hypothesis is left
//! unproved rather than closed with a bogus witness.

use super::TlaTacticEngine;
use clean_kernel::{Expr, ExprKind};

/// The outcome of a successful existential instantiation: the chosen witness
/// `t` and the residual obligation `P(t)` that was discharged.
pub(super) struct ExistsInstantiation {
    /// The witness term `t` substituted for the bound variable.
    pub(super) witness: Expr,
    /// The discharged predicate `P(t)` (the body with the witness substituted).
    pub(super) discharged: Expr,
    /// A short description of how the residual obligation was discharged.
    pub(super) justification: &'static str,
}

impl TlaTacticEngine {
    /// Extract the predicate lambda body of an unbounded existential goal.
    ///
    /// `∃ x : P(x)` is encoded as `App(Const("Exists"), Lam(_, ty, body))`
    /// where `body` references the bound variable through `BVar(0)`. Returns the
    /// raw `body` (still containing `BVar(0)`), or `None` if `expr` is not an
    /// unbounded existential.
    pub(super) fn extract_exists_body(&self, expr: &Expr) -> Option<Expr> {
        if let ExprKind::App(f, pred) = expr.kind() {
            if let ExprKind::Const(name, _) = f.kind() {
                let s = name.to_string();
                if s == "Exists" || s == "TLA.exists" {
                    if let ExprKind::Lam(_, _, body) = pred.kind() {
                        return Some(body.as_ref().clone());
                    }
                }
            }
        }
        None
    }

    /// Attempt to discharge an existential goal by exhibiting a witness.
    ///
    /// Returns the proof certificate string when a witness is found and its
    /// residual obligation `P(witness)` is soundly discharged; `None` otherwise.
    pub(super) fn try_exists_instantiation(
        &self,
        goal: &Expr,
    ) -> Result<Option<String>, TlaErrorAlias> {
        // The goal may be sequent-encoded as `h1 → … → hn → ∃ x : P(x)`.
        // Peel the hypotheses so witnesses present in them can be reused, and so
        // the existential body is exposed.
        let (hypotheses, inner) = self.peel_hypotheses_with_context(goal);

        let Some(body) = self.extract_exists_body(&inner) else {
            return Ok(None);
        };

        if let Some(inst) = self.find_exists_witness(&body, &hypotheses) {
            if self.trace {
                eprintln!(
                    "[TLA] existsi: witness {} discharges goal ({})",
                    self.expr_debug(&inst.witness),
                    inst.justification
                );
            }
            return Ok(Some(self.exists_certificate(&inst)));
        }

        Ok(None)
    }

    /// Search for a sound witness for an existential body `P` (which references
    /// the bound variable as `BVar(0)`), optionally drawing on `hypotheses`.
    fn find_exists_witness(&self, body: &Expr, hypotheses: &[Expr]) -> Option<ExistsInstantiation> {
        // Case 1: equality witness — `∃ x : x = t` or `∃ x : t = x`.
        if let Some(inst) = self.equality_witness(body) {
            return Some(inst);
        }

        // Case 2: hypothesis witness — some hypothesis is exactly `P(w)`.
        if let Some(inst) = self.hypothesis_witness(body, hypotheses) {
            return Some(inst);
        }

        None
    }

    /// Equality-witness rule.
    ///
    /// For a body of the form `BVar(0) = t` or `t = BVar(0)` where `t` does not
    /// mention the bound variable, the witness is `t` and the residual
    /// obligation `t = t` is closed by reflexivity.
    fn equality_witness(&self, body: &Expr) -> Option<ExistsInstantiation> {
        let (lhs, rhs) = self.extract_equality(body)?;

        let lhs_is_var = matches!(lhs.kind(), ExprKind::BVar(0));
        let rhs_is_var = matches!(rhs.kind(), ExprKind::BVar(0));

        // `BVar(0) = t`: witness is `t`, provided `t` does not itself mention
        // the bound variable (which would make the equality recursive, e.g.
        // `x = f(x)`, and the witness ill-formed).
        if lhs_is_var && !self.mentions_bvar0(&rhs) {
            let witness = self.lower_witness(&rhs);
            let discharged = self.make_eq(&witness, &witness);
            return Some(ExistsInstantiation {
                witness,
                discharged,
                justification: "reflexivity",
            });
        }

        // `t = BVar(0)`: symmetric.
        if rhs_is_var && !self.mentions_bvar0(&lhs) {
            let witness = self.lower_witness(&lhs);
            let discharged = self.make_eq(&witness, &witness);
            return Some(ExistsInstantiation {
                witness,
                discharged,
                justification: "reflexivity",
            });
        }

        None
    }

    /// Hypothesis-witness rule.
    ///
    /// For each candidate witness `w` drawn from the hypotheses, check whether
    /// substituting `w` for the bound variable in `P` yields an expression that
    /// matches one of the hypotheses exactly. If so, `∃ x : P(x)` holds because
    /// `P(w)` is an assumption.
    fn hypothesis_witness(&self, body: &Expr, hypotheses: &[Expr]) -> Option<ExistsInstantiation> {
        // The bound variable must actually appear in `P`; otherwise this is a
        // degenerate existential better handled by the propositional tactics
        // (and there is no meaningful witness to pin down).
        if !self.mentions_bvar0(body) {
            return None;
        }

        for candidate in self.candidate_witnesses(hypotheses) {
            // Substitute the candidate for BVar(0). `instantiate` lowers the
            // remaining loose BVars, yielding the residual obligation `P(w)`.
            let discharged = body.instantiate(&candidate);
            if discharged.has_loose_bvars() {
                // Substitution did not fully close the body (nested binder
                // mismatch); skip this candidate to stay sound.
                continue;
            }
            for hyp in hypotheses {
                if self.exprs_equal(hyp, &discharged) {
                    return Some(ExistsInstantiation {
                        witness: candidate,
                        discharged,
                        justification: "hypothesis",
                    });
                }
            }
        }

        None
    }

    /// Collect candidate witness terms from the hypotheses.
    ///
    /// Witnesses are concrete, closed sub-terms (constants, literals, and
    /// closed applications) appearing in the hypotheses. Restricting to closed
    /// terms keeps the substitution well-formed: a candidate must not capture or
    /// introduce loose bound variables.
    fn candidate_witnesses(&self, hypotheses: &[Expr]) -> Vec<Expr> {
        let mut out: Vec<Expr> = Vec::new();
        for hyp in hypotheses {
            self.collect_closed_atoms(hyp, &mut out);
        }
        out
    }

    /// Recursively gather closed atomic terms (constants, literals, free
    /// variables) usable as witnesses, deduplicating structurally-equal terms.
    fn collect_closed_atoms(&self, expr: &Expr, out: &mut Vec<Expr>) {
        match expr.kind() {
            ExprKind::Const(_, _) | ExprKind::Lit(_) | ExprKind::FVar(_) => {
                self.push_dedup(expr, out);
            }
            ExprKind::App(f, a) => {
                // A closed application (e.g. `Int.ofNat 3`, `f c`) is itself a
                // usable witness; record it before recursing into parts.
                if !expr.has_loose_bvars() {
                    self.push_dedup(expr, out);
                }
                self.collect_closed_atoms(f, out);
                self.collect_closed_atoms(a, out);
            }
            _ => {}
        }
    }

    /// Push `expr` onto `out` unless a structurally-equal term is already there.
    fn push_dedup(&self, expr: &Expr, out: &mut Vec<Expr>) {
        if !out.iter().any(|e| self.exprs_equal(e, expr)) {
            out.push(expr.clone());
        }
    }

    /// Lower a witness that was extracted from underneath the existential binder
    /// back into the ambient context.
    ///
    /// The body lives under one extra binder (the `∃`-bound variable), so a
    /// closed sub-term `t` that does not mention `BVar(0)` is encoded with its
    /// loose BVars shifted up by one relative to the surrounding goal. We lower
    /// it by one (instantiating the absent `BVar(0)` with a placeholder is not
    /// needed because, by construction, `t` does not reference `BVar(0)`).
    fn lower_witness(&self, t: &Expr) -> Expr {
        // `instantiate` substitutes BVar(0) and decrements the remaining loose
        // BVars by one. Since `t` does not mention BVar(0), the substituted
        // value is irrelevant; the net effect is the required downshift.
        let placeholder = Expr::const_(
            clean_kernel::name::Name::from_string("TLA.Value"),
            Vec::new(),
        );
        t.instantiate(&placeholder)
    }

    /// Build the equality `a = b` in the same encoding the translator emits
    /// (`App(App(Const("Eq"), a), b)`).
    fn make_eq(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::const_(clean_kernel::name::Name::from_string("Eq"), Vec::new()),
                a.clone(),
            ),
            b.clone(),
        )
    }

    /// Check whether an expression references the existential bound variable
    /// `BVar(0)` at the current binder depth.
    fn mentions_bvar0(&self, expr: &Expr) -> bool {
        self.bvar_at_depth(expr, 0)
    }

    /// Check whether `expr` references `BVar(depth)`, accounting for nested
    /// binders that shift the index.
    fn bvar_at_depth(&self, expr: &Expr, depth: u32) -> bool {
        match expr.kind() {
            ExprKind::BVar(i) => *i == depth,
            ExprKind::App(f, a) => self.bvar_at_depth(f, depth) || self.bvar_at_depth(a, depth),
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                self.bvar_at_depth(ty, depth) || self.bvar_at_depth(body, depth + 1)
            }
            _ => false,
        }
    }

    /// Produce the JSON instantiation certificate for a discharged existential.
    fn exists_certificate(&self, inst: &ExistsInstantiation) -> String {
        format!(
            "{{\"tactic\":\"exists_instantiation\",\"witness\":\"{}\",\"discharged\":\"{}\",\"justification\":\"{}\",\"status\":\"proved\"}}",
            self.escape_json(&self.expr_debug(&inst.witness)),
            self.escape_json(&self.expr_debug(&inst.discharged)),
            inst.justification,
        )
    }

    /// Minimal JSON string escaping for the certificate payload.
    fn escape_json(&self, s: &str) -> String {
        s.replace('\\', "\\\\").replace('"', "\\\"")
    }
}

/// Local alias so this module does not need to re-import the crate error path
/// under a different name than `mod.rs` uses.
pub(super) type TlaErrorAlias = crate::TlaError;

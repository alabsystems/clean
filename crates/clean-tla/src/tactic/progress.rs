// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Progress measure (variant function) proofs for TLA+ liveness.

use super::TlaTacticEngine;
use crate::TlaError;
use clean_kernel::{Expr, ExprKind};

impl TlaTacticEngine {
    /// Try to prove P ~> Q using a progress measure (variant function).
    ///
    /// A progress measure proof shows that Q is eventually reached by demonstrating:
    /// 1. There exists a variant function V : State → WellFoundedSet
    /// 2. While P ∧ ¬Q holds, either Q becomes true or V strictly decreases
    /// 3. Since V is bounded below, Q must eventually hold
    pub(super) fn try_progress_measure(
        &self,
        p: &Expr,
        q: &Expr,
    ) -> Result<Option<String>, TlaError> {
        if self.trace {
            eprintln!("[TLA] progress_measure: trying variant function proof for P ~> Q");
        }

        // SOUNDNESS: a variant/countdown *pattern* in P is only evidence of a
        // candidate measure — it is NOT a proof of the liveness `P ~> Q`. A
        // sound well-founded-progress proof (Lamport, *Specifying Systems*,
        // §11) must discharge:
        //   (a) the spec's next-state action A strictly decreases the variant
        //       while P ∧ ¬Q holds,
        //   (b) a fairness assumption (WF/SF on the decreasing action) is
        //       present so the decreasing step is actually taken, and
        //   (c) the variant's domain is well-founded.
        // This function receives only `(p, q)` — never the action or the
        // fairness hypotheses — so it has no basis to certify progress. The
        // former code returned `status:"proved"` from a syntactic P/Q pattern
        // alone (including a debug-string substring test on "count"/"fuel"/
        // "steps"), certifying genuinely-false liveness such as
        // `(counter=0) ~> (counter=5)` and `(n>0) ~> (n=0)` with no fairness.
        //
        // We keep `extract_variant_pattern` / `try_lattice_decomposition` as
        // pure detectors (they are exercised by unit tests and could feed a
        // future sound backend), but this dispatch never mints a "proved"
        // verdict from them. It returns `Ok(None)` so the caller reports the
        // obligation as not-proved. Genuinely-true liveness continues to be
        // discharged by the sound leads-to rules upstream (reflexivity,
        // □(P→Q), transitivity, chain transitivity, disjunction) in
        // `temporal.rs`, which run before this progress-measure fallback.
        if self.trace {
            if let Some((_variant, domain)) = self.extract_variant_pattern(p, q) {
                eprintln!(
                    "[TLA] progress_measure: variant pattern present (domain {domain}) but no \
                     action/fairness to discharge progress — not proved"
                );
            }
        }

        Ok(None)
    }

    /// Extract variant pattern from P ~> Q goal.
    ///
    /// Returns Some((variant_description, domain)) if a pattern is found.
    pub(super) fn extract_variant_pattern(&self, p: &Expr, q: &Expr) -> Option<(String, String)> {
        // Pattern 1: "distance to goal" variant
        if let Some((a, b)) = self.find_subexpr(p, &mut |e| self.extract_neq_pair(e)) {
            if self.contains_eq_pair(q, &a, &b) {
                return Some(("dist".to_string(), "Nat".to_string()));
            }
        }

        // Pattern 2: Countdown-style variant on Nat.
        let mut countdown_vars = Vec::new();
        self.collect_countdown_candidates(p, &mut countdown_vars);
        if countdown_vars.len() >= 2 {
            return Some((
                format!(
                    "({}, {})",
                    self.expr_debug(&countdown_vars[0]),
                    self.expr_debug(&countdown_vars[1])
                ),
                "Prod Nat Nat".to_string(),
            ));
        }
        if let Some(var) = countdown_vars.first() {
            return Some((self.expr_debug(var), "Nat".to_string()));
        }

        // Pattern 3: Simple bounded ascent: n < k and goal is n = k.
        if let Some((n, k)) = self.find_subexpr(p, &mut |e| self.extract_lt_pair(e)) {
            if self.contains_eq_pair(q, &n, &k) {
                return Some((
                    format!("({} - {})", self.expr_debug(&k), self.expr_debug(&n)),
                    "Nat".to_string(),
                ));
            }
        }

        // Pattern 4: Name-based fallback (heuristic).
        let p_str = self.expr_debug(p);
        if p_str.contains("count") || p_str.contains("fuel") || p_str.contains("steps") {
            return Some(("countdown".to_string(), "Nat".to_string()));
        }

        None
    }

    pub(super) fn extract_neq_pair(&self, expr: &Expr) -> Option<(Expr, Expr)> {
        // Not (Eq a b)
        if let ExprKind::App(f, inner) = expr.kind() {
            if let ExprKind::Const(name, _) = f.kind() {
                if name.to_string() == "Not" {
                    if let Some((lhs, rhs)) = self.extract_eq_pair(inner) {
                        return Some((lhs, rhs));
                    }
                }
            }
        }

        // Ne/TLA.ne a b
        if let Some((op, a, b)) = self.extract_binary_arith(expr) {
            if op == "Ne" || op == "TLA.ne" {
                return Some((a, b));
            }
        }

        None
    }

    pub(super) fn extract_eq_pair(&self, expr: &Expr) -> Option<(Expr, Expr)> {
        if let Some((op, a, b)) = self.extract_binary_arith(expr) {
            if op == "Eq" {
                return Some((a, b));
            }
        }
        None
    }

    pub(super) fn extract_lt_pair(&self, expr: &Expr) -> Option<(Expr, Expr)> {
        if let Some((op, a, b)) = self.extract_binary_arith(expr) {
            if op == "TLA.lt" || op == "Nat.lt" || op == "Lt.lt" {
                return Some((a, b));
            }
        }
        None
    }

    pub(super) fn contains_eq_pair(&self, expr: &Expr, a: &Expr, b: &Expr) -> bool {
        self.find_subexpr(expr, &mut |e| {
            let (lhs, rhs) = self.extract_eq_pair(e)?;
            if (self.exprs_equal(&lhs, a) && self.exprs_equal(&rhs, b))
                || (self.exprs_equal(&lhs, b) && self.exprs_equal(&rhs, a))
            {
                return Some(());
            }
            None
        })
        .is_some()
    }

    pub(super) fn extract_countdown_candidate(&self, expr: &Expr) -> Option<Expr> {
        let (op, a, b) = self.extract_binary_arith(expr)?;

        // n > 0
        if (op == "TLA.gt" || op == "Gt.gt") && self.is_zero(&b) {
            return Some(a);
        }

        // 0 < n
        if (op == "TLA.lt" || op == "Lt.lt" || op == "Nat.lt") && self.is_zero(&a) {
            return Some(b);
        }

        // n ≥ 1
        if (op == "TLA.ge" || op == "Ge.ge") && self.is_one(&b) {
            return Some(a);
        }

        // 1 ≤ n
        if (op == "TLA.le" || op == "Le.le") && self.is_one(&a) {
            return Some(b);
        }

        None
    }

    pub(super) fn collect_countdown_candidates(&self, expr: &Expr, out: &mut Vec<Expr>) {
        if let Some(candidate) = self.extract_countdown_candidate(expr) {
            if !out.iter().any(|e| self.exprs_equal(e, &candidate)) {
                out.push(candidate);
            }
        }

        match expr.kind() {
            ExprKind::App(f, a) => {
                self.collect_countdown_candidates(f, out);
                self.collect_countdown_candidates(a, out);
            }
            ExprKind::Lam(_, ty, body) => {
                self.collect_countdown_candidates(ty, out);
                self.collect_countdown_candidates(body, out);
            }
            ExprKind::Pi(_, ty, body) => {
                self.collect_countdown_candidates(ty, out);
                self.collect_countdown_candidates(body, out);
            }
            _ => {}
        }
    }

    /// Try lattice rule decomposition for P ~> Q.
    ///
    /// SOUNDNESS: the only accept here is ex-falso — `FALSE ~> Q` holds for any
    /// Q because P is never satisfied. Everything else is fail-closed.
    ///
    /// Two former accepts were unsound and are removed:
    /// * "bounded variant": finding a `<`-subterm anywhere in P is NOT a proof
    ///   of `P ~> Q`. Nothing checks that the term is a well-founded variant,
    ///   that it strictly decreases on the (absent) transition relation, or
    ///   that Q is reached. This certified false liveness like `(x<5) ~> FALSE`.
    /// * `is_trivially_true(Q) ⊢ P ~> Q`: a leads-to is `□(P ⇒ ◇Q)`, so even a
    ///   currently-true Q does not discharge it without the box; this is not a
    ///   sound leads-to rule and is dropped.
    pub(super) fn try_lattice_decomposition(
        &self,
        p: &Expr,
        q: &Expr,
    ) -> Result<Option<String>, TlaError> {
        // Ex falso: FALSE ~> Q is valid for any Q (P is unsatisfiable).
        if self.is_trivially_false(p) {
            if self.trace {
                eprintln!("[TLA] lattice: P is FALSE, P ~> Q holds ex falso");
            }
            return Ok(Some(
                "{\"tactic\":\"lattice_rule\",\"method\":\"ex_falso\",\"status\":\"proved\"}"
                    .to_string(),
            ));
        }

        // No sound structural discharge available: fail-closed. `q` is unused
        // for acceptance but kept in the signature for the detector API.
        let _ = q;
        Ok(None)
    }
}

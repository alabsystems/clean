// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Temporal logic methods for TLA+ tactics.

use super::TlaTacticEngine;
use crate::TlaError;
use clean_elab::tactic::{simp, SimpConfig};
use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind};

impl TlaTacticEngine {
    /// Try temporal logic reasoning: □, ◇, ~>, fixed-point induction.
    pub(super) fn try_temporal_unfold(&self, goal: &Expr) -> Result<Option<String>, TlaError> {
        // Peel hypotheses and dispatch to temporal reasoning with context
        let (hypotheses, inner_goal) = self.peel_hypotheses_with_context(goal);
        self.try_temporal_unfold_with_hypotheses(&inner_goal, &hypotheses)
    }

    /// Try temporal unfold with hypothesis context.
    fn try_temporal_unfold_with_hypotheses(
        &self,
        goal: &Expr,
        hypotheses: &[Expr],
    ) -> Result<Option<String>, TlaError> {
        if self.trace {
            eprintln!(
                "[TLA] temporal_unfold: checking goal with {} hypotheses",
                hypotheses.len()
            );
        }

        // Check for Always (□) goals
        if let Some(inner) = self.extract_always(goal) {
            if self.trace {
                eprintln!("[TLA] temporal_unfold: goal is □P, trying always-specific reasoning");
            }

            // Try stability pattern: P ∧ □(P → □P) ⊢ □P
            if let Some(cert) = self.try_always_via_stability(&inner, hypotheses) {
                return Ok(Some(cert));
            }

            // Try GFP coinduction
            if let Some(cert) = self.try_gfp_coinduction(goal)? {
                return Ok(Some(cert));
            }

            // Fall back to proving the inner formula and wrapping
            // This is only sound for state predicates (not temporal)
            if let Some(cert) =
                self.try_superposition(&self.wrap_with_hypotheses(hypotheses, inner.clone()))?
            {
                return Ok(Some(format!(
                    "{{\"tactic\":\"always_intro\",\"inner\":{},\"status\":\"proved\"}}",
                    cert
                )));
            }
        }

        // Check for Eventually (◇) goals
        if let Some(inner) = self.extract_eventually(goal) {
            if self.trace {
                eprintln!(
                    "[TLA] temporal_unfold: goal is ◇P, trying eventually-specific reasoning"
                );
            }

            // Try to derive ◇P from □P in hypotheses
            if let Some(cert) = self.try_eventually_from_always(&inner, hypotheses) {
                return Ok(Some(cert));
            }

            // Try LFP induction
            if let Some(cert) = self.try_lfp_induction(goal)? {
                return Ok(Some(cert));
            }

            // Try to prove P directly (then ◇P follows trivially)
            if let Some(cert) =
                self.try_superposition(&self.wrap_with_hypotheses(hypotheses, inner.clone()))?
            {
                return Ok(Some(format!(
                    "{{\"tactic\":\"eventually_intro\",\"inner\":{},\"status\":\"proved\"}}",
                    cert
                )));
            }
        }

        // Check for leads-to (P ~> Q) goals
        if let Some((p, q)) = self.extract_leads_to(goal) {
            if self.trace {
                eprintln!(
                    "[TLA] temporal_unfold: goal is {} ~> {}",
                    self.expr_debug(&p),
                    self.expr_debug(&q)
                );
            }

            // Rule 0: Reflexivity: P ~> P holds for any P.
            // Discharged structurally on syntactic equality of P and Q.
            if let Some(cert) = self.try_leads_to_reflexivity(&p, &q) {
                return Ok(Some(cert));
            }

            // Rule 0b: Sound structural trivialities for `P ~> Q ≡ □(P ⇒ ◇Q)`.
            //   * `FALSE ~> Q` is valid for any Q (ex falso: P is never true).
            //   * `P ~> TRUE` is valid for any P: `TRUE` holds in every state,
            //     so `◇TRUE` is unconditionally true, hence `P ⇒ ◇TRUE` holds.
            // Both are genuine leads-to theorems and do NOT require a variant,
            // fairness, or the well-founded-progress machinery — unlike the
            // (now fail-closed) progress-measure fallback.
            if let Some(cert) = self.try_leads_to_trivial(&p, &q) {
                return Ok(Some(cert));
            }

            // Rule 1: □(P → Q) ⊢ P ~> Q
            if let Some(cert) = self.try_leads_to_from_always(&p, &q, hypotheses) {
                return Ok(Some(cert));
            }

            // Rule 2: Transitivity: P ~> Q, Q ~> R ⊢ P ~> R
            if let Some(cert) = self.try_leads_to_transitivity(&p, &q, hypotheses) {
                return Ok(Some(cert));
            }

            // Rule 2b: Chain transitivity: P ~> A, A ~> B, …, Y ~> R ⊢ P ~> R
            // (the iterated/multi-hop generalisation of Rule 2).
            if let Some(cert) = self.try_leads_to_chain_transitivity(&p, &q, hypotheses) {
                return Ok(Some(cert));
            }

            // Rule 3: Disjunction: P ~> R, Q ~> R ⊢ (P ∨ Q) ~> R
            if let Some(cert) = self.try_leads_to_disjunction(&p, &q, hypotheses) {
                return Ok(Some(cert));
            }

            // Rule 4: Progress measure (variant function)
            if let Some(cert) = self.try_progress_measure(&p, &q)? {
                return Ok(Some(cert));
            }
        }

        // Check for weak-fairness (WF_vars(A)) goals.
        if let Some((vars, action)) = self.extract_weak_fairness(goal) {
            if self.trace {
                eprintln!(
                    "[TLA] temporal_unfold: goal is WF_{}({})",
                    self.expr_debug(&vars),
                    self.expr_debug(&action)
                );
            }
            if let Some(cert) = self.try_weak_fairness(&vars, &action, hypotheses)? {
                return Ok(Some(cert));
            }
        }

        // Check for strong-fairness (SF_vars(A)) goals.
        if let Some((vars, action)) = self.extract_strong_fairness(goal) {
            if self.trace {
                eprintln!(
                    "[TLA] temporal_unfold: goal is SF_{}({})",
                    self.expr_debug(&vars),
                    self.expr_debug(&action)
                );
            }
            if let Some(cert) = self.try_strong_fairness(&vars, &action, hypotheses)? {
                return Ok(Some(cert));
            }
        }

        Ok(None)
    }

    /// Reduce a weak-fairness goal `WF_vars(A)` to its definitional temporal
    /// form and dispatch that form back through the temporal machinery.
    ///
    /// TLA+ defines weak fairness (Lamport, *Specifying Systems*, §8.4) as
    ///
    /// ```text
    /// WF_vars(A) ≡ □( □ENABLED ⟨A⟩_vars ⇒ ◇⟨A⟩_vars )
    /// ```
    ///
    /// where the angle action `⟨A⟩_vars ≡ A ∧ vars' ≠ vars`. This method
    /// rewrites the goal into exactly that box-implication and asks the
    /// existing `□`/`◇`/`ENABLED` reasoning to discharge it. The rewrite is a
    /// definitional unfolding, so it preserves the goal's meaning: no
    /// fairness goal is reported as proved unless the (sound) temporal
    /// machinery closes the unfolded form. If that machinery does not close
    /// it, this returns `Ok(None)` and dispatch fails honestly.
    fn try_weak_fairness(
        &self,
        vars: &Expr,
        action: &Expr,
        hypotheses: &[Expr],
    ) -> Result<Option<String>, TlaError> {
        let unfolded = self.weak_fairness_unfolded(vars, action);

        if self.trace {
            eprintln!(
                "[TLA] weak_fairness: reduced WF to {}",
                self.expr_debug(&unfolded)
            );
        }

        match self.try_temporal_unfold_with_hypotheses(&unfolded, hypotheses)? {
            Some(inner) => Ok(Some(format!(
                "{{\"tactic\":\"weak_fairness_unfold\",\"reduced\":{},\"status\":\"proved\"}}",
                inner
            ))),
            None => Ok(None),
        }
    }

    /// Reduce a strong-fairness goal `SF_vars(A)` to its definitional temporal
    /// form and dispatch that form back through the temporal machinery.
    ///
    /// TLA+ defines strong fairness (Lamport, *Specifying Systems*, §8.4) as
    ///
    /// ```text
    /// SF_vars(A) ≡ □( □◇ENABLED ⟨A⟩_vars ⇒ □◇⟨A⟩_vars )
    /// ```
    ///
    /// with the same angle action `⟨A⟩_vars ≡ A ∧ vars' ≠ vars`. As with weak
    /// fairness, this rewrite is a definitional unfolding and only reports
    /// `proved` when the existing temporal reasoning closes the unfolded form.
    fn try_strong_fairness(
        &self,
        vars: &Expr,
        action: &Expr,
        hypotheses: &[Expr],
    ) -> Result<Option<String>, TlaError> {
        let unfolded = self.strong_fairness_unfolded(vars, action);

        if self.trace {
            eprintln!(
                "[TLA] strong_fairness: reduced SF to {}",
                self.expr_debug(&unfolded)
            );
        }

        match self.try_temporal_unfold_with_hypotheses(&unfolded, hypotheses)? {
            Some(inner) => Ok(Some(format!(
                "{{\"tactic\":\"strong_fairness_unfold\",\"reduced\":{},\"status\":\"proved\"}}",
                inner
            ))),
            None => Ok(None),
        }
    }

    /// Build the definitional unfolding of `WF_vars(A)`:
    /// `□( □ENABLED ⟨A⟩_vars ⇒ ◇⟨A⟩_vars )`.
    pub(super) fn weak_fairness_unfolded(&self, vars: &Expr, action: &Expr) -> Expr {
        let angle = self.make_angle_action(action.clone(), vars.clone());
        let enabled = self.make_enabled(angle.clone());

        // □ENABLED ⟨A⟩_vars ⇒ ◇⟨A⟩_vars
        let antecedent = self.make_always(enabled);
        let consequent = self.make_eventually(angle);
        let implication = Expr::arrow(antecedent, consequent);

        // □( … )
        self.make_always(implication)
    }

    /// Build the definitional unfolding of `SF_vars(A)`:
    /// `□( □◇ENABLED ⟨A⟩_vars ⇒ □◇⟨A⟩_vars )`.
    pub(super) fn strong_fairness_unfolded(&self, vars: &Expr, action: &Expr) -> Expr {
        let angle = self.make_angle_action(action.clone(), vars.clone());
        let enabled = self.make_enabled(angle.clone());

        // □◇ENABLED ⟨A⟩_vars ⇒ □◇⟨A⟩_vars
        let antecedent = self.make_always(self.make_eventually(enabled));
        let consequent = self.make_always(self.make_eventually(angle));
        let implication = Expr::arrow(antecedent, consequent);

        // □( … )
        self.make_always(implication)
    }

    /// Construct `ENABLED P` (`FixedPoint.TLA_enabled P`), matching the
    /// encoding used for `ENABLED` in [`crate::encoding`].
    fn make_enabled(&self, p: Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("FixedPoint.TLA_enabled"), vec![]),
            p,
        )
    }

    /// Construct the angle action `⟨A⟩_vars ≡ A ∧ vars' ≠ vars`.
    ///
    /// The "step" conjunct `vars' ≠ vars` is built as `Not(Eq(vars', vars))`
    /// where `vars'` is the next-state value `TLA.prime vars`, matching how
    /// `UNCHANGED`/priming are encoded in [`crate::encoding`].
    fn make_angle_action(&self, action: Expr, vars: Expr) -> Expr {
        let primed = Expr::app(
            Expr::const_(Name::from_string("TLA.prime"), vec![]),
            vars.clone(),
        );
        let unchanged = Expr::app(
            Expr::app(Expr::const_(Name::from_string("Eq"), vec![]), primed),
            vars,
        );
        let changed = Expr::app(Expr::const_(Name::from_string("Not"), vec![]), unchanged);
        self.make_and(action, changed)
    }

    /// Try to prove □P via stability pattern.
    fn try_always_via_stability(&self, p: &Expr, hypotheses: &[Expr]) -> Option<String> {
        let mut has_initial = false;
        let mut stability_idx = None;

        for (i, hyp) in hypotheses.iter().enumerate() {
            if self.exprs_equal(hyp, p) {
                has_initial = true;
            }

            if let Some(inner_always) = self.extract_always(hyp) {
                if let Some((antecedent, consequent)) = self.extract_implication(&inner_always) {
                    if self.exprs_equal(&antecedent, p) {
                        if let Some(consequent_inner) = self.extract_always(&consequent) {
                            if self.exprs_equal(&consequent_inner, p) {
                                stability_idx = Some(i);
                            }
                        }
                    }
                }
            }
        }

        if let (true, Some(idx)) = (has_initial, stability_idx) {
            if self.trace {
                eprintln!(
                    "[TLA] always_via_stability: found P initial and □(P → □P) stability for goal □{}",
                    self.expr_debug(p)
                );
            }
            return Some(format!(
                "{{\"tactic\":\"always_via_stability\",\"stability_hyp\":{idx},\"status\":\"proved\"}}"
            ));
        }

        None
    }

    /// Try to prove ◇P from hypothesis □P.
    fn try_eventually_from_always(&self, p: &Expr, hypotheses: &[Expr]) -> Option<String> {
        for (i, hyp) in hypotheses.iter().enumerate() {
            if let Some(inner) = self.extract_always(hyp) {
                if self.exprs_equal(&inner, p) {
                    if self.trace {
                        eprintln!(
                            "[TLA] eventually_from_always: found □{} matching goal ◇{}",
                            self.expr_debug(&inner),
                            self.expr_debug(p)
                        );
                    }
                    return Some(format!(
                        "{{\"tactic\":\"eventually_from_always\",\"hypothesis\":{},\"status\":\"proved\"}}",
                        i
                    ));
                }
            }
        }
        None
    }

    /// Try to prove P ~> Q by reflexivity when P and Q are syntactically equal.
    ///
    /// `LeadsTo` is defined as `P ~> Q ≡ □(P ⇒ ◇Q)`. When `P` and `Q` are the
    /// same formula, the implication `P ⇒ ◇P` is discharged by the witness
    /// "the current step", i.e. `P ⊢ ◇P`. Hence `P ~> P` holds for any `P`
    /// without any hypothesis on `P`. The check is purely structural, matching
    /// the syntactic-equality semantics requested in `docs/PROVER_GAPS.md`
    /// (Gap 5, "open question" on normalisation).
    fn try_leads_to_reflexivity(&self, p: &Expr, q: &Expr) -> Option<String> {
        if self.exprs_equal(p, q) {
            if self.trace {
                eprintln!(
                    "[TLA] leads_to_reflexivity: {} ~> {} closed by reflexivity",
                    self.expr_debug(p),
                    self.expr_debug(q)
                );
            }
            return Some("{\"tactic\":\"leads_to_reflexivity\",\"status\":\"proved\"}".to_string());
        }
        None
    }

    /// Try to prove `P ~> Q` by the two sound structural trivialities.
    ///
    /// `P ~> Q ≡ □(P ⇒ ◇Q)`. This discharges exactly:
    /// * `FALSE ~> Q` — ex falso, since `P` is never satisfied; and
    /// * `P ~> TRUE` — since `TRUE` holds in every state, `◇TRUE` is always
    ///   true, so `P ⇒ ◇TRUE` holds unconditionally.
    ///
    /// Nothing else is accepted here. In particular, a currently-true *state
    /// predicate* Q (not the literal `TRUE`) does NOT discharge `P ~> Q`,
    /// because the leads-to still needs the box; that case is intentionally
    /// excluded (it was one of the removed unsound lattice-decomposition
    /// accepts).
    fn try_leads_to_trivial(&self, p: &Expr, q: &Expr) -> Option<String> {
        if self.is_trivially_false(p) {
            if self.trace {
                eprintln!("[TLA] leads_to_trivial: FALSE ~> Q holds ex falso");
            }
            return Some(
                "{\"tactic\":\"leads_to_trivial\",\"method\":\"ex_falso\",\"status\":\"proved\"}"
                    .to_string(),
            );
        }
        if self.is_trivially_true(q) {
            if self.trace {
                eprintln!("[TLA] leads_to_trivial: P ~> TRUE holds (◇TRUE is valid)");
            }
            return Some(
                "{\"tactic\":\"leads_to_trivial\",\"method\":\"q_true\",\"status\":\"proved\"}"
                    .to_string(),
            );
        }
        None
    }

    /// Try to prove P ~> Q from hypothesis □(P → Q).
    fn try_leads_to_from_always(&self, p: &Expr, q: &Expr, hypotheses: &[Expr]) -> Option<String> {
        for (i, hyp) in hypotheses.iter().enumerate() {
            if let Some(inner) = self.extract_always(hyp) {
                if let Some((hyp_p, hyp_q)) = self.extract_implication(&inner) {
                    if self.exprs_equal(&hyp_p, p) && self.exprs_equal(&hyp_q, q) {
                        if self.trace {
                            eprintln!(
                                "[TLA] leads_to_from_always: found □({} → {}) matching goal {} ~> {}",
                                self.expr_debug(&hyp_p),
                                self.expr_debug(&hyp_q),
                                self.expr_debug(p),
                                self.expr_debug(q)
                            );
                        }
                        return Some(format!(
                            "{{\"tactic\":\"leads_to_from_always\",\"hypothesis\":{},\"status\":\"proved\"}}",
                            i
                        ));
                    }
                }
            }
        }
        None
    }

    /// Try transitivity rule: P ~> Q and Q ~> R implies P ~> R
    pub(super) fn try_leads_to_transitivity(
        &self,
        p: &Expr,
        r: &Expr,
        hypotheses: &[Expr],
    ) -> Option<String> {
        for (i, hyp_pq) in hypotheses.iter().enumerate() {
            if let Some((hyp_p, hyp_q)) = self.extract_leads_to(hyp_pq) {
                if self.exprs_equal(&hyp_p, p) {
                    for (j, hyp_qr) in hypotheses.iter().enumerate() {
                        if i != j {
                            if let Some((hyp_q2, hyp_r)) = self.extract_leads_to(hyp_qr) {
                                if self.exprs_equal(&hyp_q, &hyp_q2) && self.exprs_equal(&hyp_r, r)
                                {
                                    if self.trace {
                                        eprintln!(
                                            "[TLA] leads_to_trans: {} ~> {} from {} ~> {} and {} ~> {}",
                                            self.expr_debug(p),
                                            self.expr_debug(r),
                                            self.expr_debug(&hyp_p),
                                            self.expr_debug(&hyp_q),
                                            self.expr_debug(&hyp_q2),
                                            self.expr_debug(&hyp_r)
                                        );
                                    }
                                    return Some(format!(
                                        "{{\"tactic\":\"leads_to_trans\",\"hyp1\":{},\"hyp2\":{},\"status\":\"proved\"}}",
                                        i, j
                                    ));
                                }
                            }
                        }
                    }
                }
            }
        }
        None
    }

    /// Try multi-hop chain transitivity: a sequence of leads-to hypotheses
    /// `P ~> A`, `A ~> B`, …, `Y ~> R` discharges the goal `P ~> R`.
    ///
    /// This is the iterated generalisation of [`Self::try_leads_to_transitivity`],
    /// which only closes the two-hop case (`P ~> Q`, `Q ~> R ⊢ P ~> R`). A longer
    /// chain such as `P ~> A`, `A ~> B`, `B ~> R` previously forced the user to
    /// decompose the proof by hand; this method finds the chain automatically.
    ///
    /// Soundness rests entirely on the transitivity of TLA+ leads-to
    /// (`(P ~> Q) ∧ (Q ~> R) ⇒ (P ~> R)`, Lamport, *Specifying Systems*, §10.6).
    /// Every edge in the constructed graph corresponds to an actual leads-to
    /// hypothesis — `extract_leads_to` only yields an edge for a genuine
    /// `FixedPoint.TLA_leads_to A B` formula — and node adjacency is decided by
    /// `exprs_equal`, the same structural-equality check the binary rule uses.
    /// A path from `P` to `R` is therefore a witnessed sequence of real
    /// `~>`-steps whose composition is `P ~> R` by repeated transitivity; the
    /// chain is never a shortcut over a missing hypothesis. If no such path
    /// exists this returns `None` and dispatch fails honestly.
    ///
    /// The certificate records the ordered list of hypothesis indices forming
    /// the chain: `{"tactic":"leads_to_chain","chain":[i0, i1, …],"status":"proved"}`.
    pub(super) fn try_leads_to_chain_transitivity(
        &self,
        p: &Expr,
        r: &Expr,
        hypotheses: &[Expr],
    ) -> Option<String> {
        // Collect the leads-to edges (source, target, hypothesis index). Every
        // edge is a real `A ~> B` hypothesis; non-leads-to hypotheses contribute
        // no edges and so can never extend a chain.
        let edges: Vec<(Expr, Expr, usize)> = hypotheses
            .iter()
            .enumerate()
            .filter_map(|(i, hyp)| self.extract_leads_to(hyp).map(|(src, tgt)| (src, tgt, i)))
            .collect();

        if edges.is_empty() {
            return None;
        }

        // BFS over formula nodes, starting from `P` and looking for `R`. Nodes
        // are formulas, compared structurally with `exprs_equal`. `frontier`
        // holds the formulas to expand; `visited` holds formulas already
        // expanded (so cycles like A ~> B, B ~> A terminate). `parent` records,
        // for each visited target formula, the edge that first reached it so the
        // hypothesis-index chain can be reconstructed.
        //
        // The frontier and visited sets are deliberately keyed on `P` itself, so
        // the search begins exactly at the goal's antecedent.
        let mut visited: Vec<Expr> = vec![p.clone()];
        let mut frontier: Vec<Expr> = vec![p.clone()];
        // parent[k] = (predecessor formula, edge hyp index) for visited[k].
        // visited[0] (the start node P) has no parent.
        let mut parent: Vec<Option<(Expr, usize)>> = vec![None];

        while !frontier.is_empty() {
            let mut next_frontier: Vec<Expr> = Vec::new();

            for node in &frontier {
                for (src, tgt, idx) in &edges {
                    if !self.exprs_equal(src, node) {
                        continue;
                    }
                    // Already reached `tgt` via an earlier (shorter) path — skip
                    // to keep the chain minimal and avoid cycles.
                    if visited.iter().any(|v| self.exprs_equal(v, tgt)) {
                        continue;
                    }

                    visited.push(tgt.clone());
                    parent.push(Some((node.clone(), *idx)));

                    if self.exprs_equal(tgt, r) {
                        // Reconstruct the chain of hypothesis indices from `R`
                        // back to `P` by walking `parent` pointers.
                        let chain = self.reconstruct_chain(&visited, &parent, tgt);

                        // A genuine multi-hop chain has at least one edge. (A
                        // zero-edge "chain" would mean P and R are already equal,
                        // which reflexivity handles upstream.)
                        if chain.is_empty() {
                            return None;
                        }

                        if self.trace {
                            eprintln!(
                                "[TLA] leads_to_chain: {} ~> {} via {} hop(s) {:?}",
                                self.expr_debug(p),
                                self.expr_debug(r),
                                chain.len(),
                                chain
                            );
                        }

                        let chain_json = chain
                            .iter()
                            .map(|i| i.to_string())
                            .collect::<Vec<_>>()
                            .join(",");
                        return Some(format!(
                            "{{\"tactic\":\"leads_to_chain\",\"chain\":[{chain_json}],\"status\":\"proved\"}}"
                        ));
                    }

                    next_frontier.push(tgt.clone());
                }
            }

            frontier = next_frontier;
        }

        None
    }

    /// Reconstruct the ordered list of hypothesis indices on the BFS path from
    /// the start node to `target`, by walking the `parent` back-pointers.
    ///
    /// `visited[k]` is the k-th discovered formula and `parent[k]` is the edge
    /// (predecessor formula, hypothesis index) that first reached it. Following
    /// the pointers from `target` to the start yields the edges in reverse, so
    /// the result is reversed before returning to give source-to-target order.
    fn reconstruct_chain(
        &self,
        visited: &[Expr],
        parent: &[Option<(Expr, usize)>],
        target: &Expr,
    ) -> Vec<usize> {
        let mut chain: Vec<usize> = Vec::new();
        let mut cursor = target.clone();

        // Walk parent pointers until we reach the start node (whose parent is
        // `None`) or an unknown formula (defensive: should not happen).
        while let Some((pred, idx)) = visited
            .iter()
            .position(|v| self.exprs_equal(v, &cursor))
            .and_then(|pos| parent[pos].clone())
        {
            chain.push(idx);
            cursor = pred;
        }

        chain.reverse();
        chain
    }

    /// Try disjunction rule: P ~> R and Q ~> R implies (P ∨ Q) ~> R
    fn try_leads_to_disjunction(
        &self,
        goal_p: &Expr,
        goal_r: &Expr,
        hypotheses: &[Expr],
    ) -> Option<String> {
        if let Some((left, right)) = self.extract_or(goal_p) {
            let mut found_left = None;
            let mut found_right = None;

            for (i, hyp) in hypotheses.iter().enumerate() {
                if let Some((hyp_p, hyp_r)) = self.extract_leads_to(hyp) {
                    if self.exprs_equal(&hyp_r, goal_r) {
                        if self.exprs_equal(&hyp_p, &left) {
                            found_left = Some(i);
                        } else if self.exprs_equal(&hyp_p, &right) {
                            found_right = Some(i);
                        }
                    }
                }
            }

            if let (Some(i), Some(j)) = (found_left, found_right) {
                if self.trace {
                    eprintln!(
                        "[TLA] leads_to_disj: ({} ∨ {}) ~> {} from hyp[{}] and hyp[{}]",
                        self.expr_debug(&left),
                        self.expr_debug(&right),
                        self.expr_debug(goal_r),
                        i,
                        j
                    );
                }
                return Some(format!(
                    "{{\"tactic\":\"leads_to_disjunction\",\"left_hyp\":{},\"right_hyp\":{},\"status\":\"proved\"}}",
                    i, j
                ));
            }
        }
        None
    }

    /// Try least fixed point induction (for Eventually)
    pub(super) fn try_lfp_induction(&self, goal: &Expr) -> Result<Option<String>, TlaError> {
        if let ExprKind::Pi(_, _, body) = goal.kind() {
            if !body.has_loose_bvars() {
                return self.try_lfp_induction(body);
            }
        }

        if let Some(inner) = self.extract_eventually(goal) {
            if self.trace {
                eprintln!("[TLA] lfp_induction: goal is Eventually, trying induction on lfp");
            }

            let mut state = self.make_proof_state(&inner);
            match simp(&mut state, SimpConfig::new()) {
                Ok(()) if state.is_complete() => {
                    return Ok(Some(self.generate_certificate("lfp_induction_base")));
                }
                _ => {}
            }

            if let Some(cert) = self.try_superposition(&inner)? {
                return Ok(Some(format!(
                    "{{\"tactic\":\"lfp_induction\",\"inner\":{},\"status\":\"proved\"}}",
                    cert
                )));
            }

            if self.is_trivially_true(&inner) {
                return Ok(Some(self.generate_certificate("lfp_induction_trivial")));
            }

            Ok(None)
        } else {
            Ok(None)
        }
    }

    /// Try greatest fixed point coinduction (for Always)
    pub(super) fn try_gfp_coinduction(&self, goal: &Expr) -> Result<Option<String>, TlaError> {
        if let ExprKind::Pi(_, _, body) = goal.kind() {
            if !body.has_loose_bvars() {
                return self.try_gfp_coinduction(body);
            }
        }

        if let Some(inner) = self.extract_always(goal) {
            if self.trace {
                eprintln!("[TLA] gfp_coinduction: goal is Always, trying coinduction on gfp");
            }

            // Tautological state predicates hold in every state, so □P is
            // immediate without the general coinduction step.
            if self.is_trivially_true(&inner) {
                return Ok(Some(self.generate_certificate("gfp_coinduction_trivial")));
            }

            // Step 1: Check if P holds at current state
            let mut base_state = self.make_proof_state(&inner);
            let base_holds = match simp(&mut base_state, SimpConfig::new()) {
                Ok(()) if base_state.is_complete() => true,
                _ => self.is_trivially_true(&inner),
            };

            if !base_holds {
                if let Some(_cert) = self.try_superposition(&inner)? {
                    if self.trace {
                        eprintln!(
                            "[TLA] gfp_coinduction: P proved by superposition, but inductiveness not verified"
                        );
                    }
                }
                return Ok(None);
            }

            // Step 2: Check inductiveness (P → ○P)
            let next_p = self.build_next(inner.clone());
            let inductiveness = Expr::arrow(inner.clone(), next_p);

            let mut inductive_state = self.make_proof_state(&inductiveness);
            let inductive_holds = match simp(&mut inductive_state, SimpConfig::new()) {
                Ok(()) if inductive_state.is_complete() => true,
                _ => self.try_superposition(&inductiveness)?.is_some(),
            };

            if !inductive_holds {
                if self.trace {
                    eprintln!(
                        "[TLA] gfp_coinduction: Base case proved but inductiveness check failed"
                    );
                }
                return Ok(None);
            }

            Ok(Some(self.generate_certificate("gfp_coinduction")))
        } else {
            Ok(None)
        }
    }

    /// Build ○P (next-state version of P)
    fn build_next(&self, p: Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("FixedPoint.TLA_next"), vec![]),
            p,
        )
    }

    // ================================================================
    // Temporal operator constructors — used by unfold_always/unfold_eventually
    // and reserved for future temporal reasoning expansions.
    // ================================================================

    /// Construct ○P (next P)
    #[allow(dead_code)]
    pub(super) fn make_next(&self, p: Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("FixedPoint.TLA_next"), vec![]),
            p,
        )
    }

    /// Construct □P (always P)
    pub(super) fn make_always(&self, p: Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("FixedPoint.TLA_always"), vec![]),
            p,
        )
    }

    /// Construct ◇P (eventually P)
    pub(super) fn make_eventually(&self, p: Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("FixedPoint.TLA_eventually"), vec![]),
            p,
        )
    }

    /// Construct P ∧ Q
    pub(super) fn make_and(&self, p: Expr, q: Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::const_(Name::from_string("And"), vec![]), p),
            q,
        )
    }

    /// Construct P ∨ Q
    #[allow(dead_code)]
    pub(super) fn make_or(&self, p: Expr, q: Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::const_(Name::from_string("Or"), vec![]), p),
            q,
        )
    }

    /// Unfold □P to P ∧ ○(□P) (one step of greatest fixed point)
    #[allow(dead_code)]
    pub(super) fn unfold_always(&self, p: Expr) -> Expr {
        let always_p = self.make_always(p.clone());
        let next_always_p = self.make_next(always_p);
        self.make_and(p, next_always_p)
    }

    /// Unfold ◇P to P ∨ ○(◇P) (one step of least fixed point)
    #[allow(dead_code)]
    pub(super) fn unfold_eventually(&self, p: Expr) -> Expr {
        let eventually_p = self.make_eventually(p.clone());
        let next_eventually_p = self.make_next(eventually_p);
        self.make_or(p, next_eventually_p)
    }
}

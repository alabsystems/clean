// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Induction methods for TLA+ tactics — nat, well-founded, lexicographic.

use super::TlaTacticEngine;
use crate::TlaError;
use clean_kernel::expr::BinderInfo;
use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind};

impl TlaTacticEngine {
    /// Extract the body of a forall over Nat.
    pub(super) fn extract_forall_nat(&self, goal: &Expr) -> Option<Expr> {
        if let ExprKind::Pi(_, ty, body) = goal.kind() {
            if let ExprKind::Const(ty_name, _) = ty.kind() {
                if ty_name == &Name::from_string("Nat") {
                    return Some(body.as_ref().clone());
                }
            }
        }
        None
    }

    /// Try to prove goal by natural number induction.
    pub(super) fn try_nat_induction(&self, goal: &Expr) -> Result<Option<String>, TlaError> {
        // Peel hypotheses and check if inner goal is ∀n : Nat, P(n)
        let (hypotheses, inner) = self.peel_hypotheses_with_context(goal);

        if let Some(body) = self.extract_forall_nat(&inner) {
            if self.trace {
                eprintln!("[TLA] try_nat_induction: found ∀n : Nat, P(n)");
            }
            return self.do_nat_induction(&body, &hypotheses);
        }

        // Also try TLA-style ForallIn
        if let Some((set_expr, _var, body)) = self.extract_tla_forall_in(&inner) {
            if self.is_nat_set(&set_expr) {
                if self.trace {
                    eprintln!("[TLA] try_nat_induction: found ∀n ∈ Nat, P(n)");
                }
                return self.do_nat_induction(&body, &hypotheses);
            }
        }

        Ok(None)
    }

    /// Core nat induction: prove P(0) and P(n) → P(succ n).
    pub(super) fn do_nat_induction(
        &self,
        body: &Expr,
        hypotheses: &[Expr],
    ) -> Result<Option<String>, TlaError> {
        let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let base_case_core = body.instantiate(&zero);
        let base_case = self.wrap_with_hypotheses(hypotheses, base_case_core.clone());

        if self.trace {
            eprintln!(
                "[TLA] nat_induction: trying base case P(0) with {} hypotheses",
                hypotheses.len()
            );
        }

        let base_cert = if self.is_trivially_true(&base_case_core) {
            if self.trace {
                eprintln!("[TLA] nat_induction: base case is trivially true");
            }
            "{\"tactic\":\"trivial\",\"case\":\"base\",\"status\":\"proved\"}".to_string()
        } else if let Some(cert) = self.try_prove_nested_goal(&base_case_core, hypotheses) {
            if self.trace {
                eprintln!("[TLA] nat_induction: base case proved via nested goal handler");
            }
            cert
        } else {
            match self.try_arith_simplify(&base_case_core) {
                Some(cert) => {
                    if self.trace {
                        eprintln!("[TLA] nat_induction: base case proved via arith_simplify");
                    }
                    cert
                }
                None => {
                    match self.try_arith_simplify_with_hypotheses(&base_case_core, hypotheses) {
                        Some(cert) => {
                            if self.trace {
                                eprintln!(
                                    "[TLA] nat_induction: base case proved via hypothesis matching"
                                );
                            }
                            cert
                        }
                        None => {
                            match self.try_positivity_with_hypotheses(&base_case_core, hypotheses) {
                                Some(cert) => {
                                    if self.trace {
                                        eprintln!(
                                            "[TLA] nat_induction: base case proved via positivity"
                                        );
                                    }
                                    cert
                                }
                                None => match self.try_superposition(&base_case)? {
                                    Some(cert) => cert,
                                    None => {
                                        if self.trace {
                                            eprintln!("[TLA] nat_induction: base case failed");
                                        }
                                        return Ok(None);
                                    }
                                },
                            }
                        }
                    }
                }
            }
        };

        if self.trace {
            eprintln!("[TLA] nat_induction: base case proved, trying step case");
        }

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let succ_n = Expr::app(
            Expr::const_(Name::from_string("Nat.succ"), vec![]),
            Expr::from_kind(ExprKind::BVar(0)),
        );

        let p_n = body.clone();
        let p_succ_n = body.instantiate(&succ_n);
        let step_body = Expr::arrow(p_n, p_succ_n);
        let step_case_core = Expr::pi(BinderInfo::Default, nat, step_body.clone());
        let step_case = self.wrap_with_hypotheses(hypotheses, step_case_core.clone());

        if self.trace {
            eprintln!(
                "[TLA] nat_induction: trying step case ∀n, P(n) → P(succ n) with {} hypotheses",
                hypotheses.len()
            );
        }

        let step_cert = if let ExprKind::Pi(_, antecedent, consequent) = step_body.kind() {
            if self.is_implication_trivially_true(antecedent.as_ref(), consequent.as_ref()) {
                if self.trace {
                    eprintln!("[TLA] nat_induction: step case P(n) → P(succ n) is trivially true");
                }
                "{\"tactic\":\"trivial\",\"case\":\"step\",\"status\":\"proved\"}".to_string()
            } else {
                match self.try_prove_step_case(&step_body, &step_case, body, hypotheses)? {
                    Some(cert) => cert,
                    None => return Ok(None),
                }
            }
        } else {
            match self.try_prove_step_case(&step_body, &step_case, body, hypotheses)? {
                Some(cert) => cert,
                None => return Ok(None),
            }
        };

        if self.trace {
            eprintln!("[TLA] nat_induction: both cases proved!");
        }

        Ok(Some(format!(
            "{{\"tactic\":\"nat_induction\",\"base\":{},\"step\":{}}}",
            base_cert, step_cert
        )))
    }

    /// Helper to prove step case P(n) → P(succ n) using arith or SMT.
    fn try_prove_step_case(
        &self,
        step_body: &Expr,
        step_case: &Expr,
        body: &Expr,
        hypotheses: &[Expr],
    ) -> Result<Option<String>, TlaError> {
        if let Some(cert) = self.try_nested_forall_step_case(step_body, hypotheses)? {
            if self.trace {
                eprintln!("[TLA] nat_induction: step case proved via nested forall handling");
            }
            return Ok(Some(cert));
        }

        if let Some(cert) = self.try_arith_step_case(step_body) {
            if self.trace {
                eprintln!("[TLA] nat_induction: step case proved via arith_step");
            }
            return Ok(Some(cert));
        }

        if let Some(cert) = self.try_step_case_with_hypotheses(step_body, body, hypotheses) {
            if self.trace {
                eprintln!("[TLA] nat_induction: step case proved via hypothesis substitution");
            }
            return Ok(Some(cert));
        }

        if let Some(cert) = self.try_positivity_step_case(step_body, hypotheses) {
            if self.trace {
                eprintln!("[TLA] nat_induction: step case proved via positivity preservation");
            }
            return Ok(Some(cert));
        }

        if let Some(cert) = self.try_ring_step_case(step_body, hypotheses) {
            if self.trace {
                eprintln!("[TLA] nat_induction: step case proved via ring tactic");
            }
            return Ok(Some(cert));
        }

        match self.try_superposition(step_case)? {
            Some(cert) => Ok(Some(cert)),
            None => {
                if self.trace {
                    eprintln!("[TLA] nat_induction: step case failed");
                }
                Ok(None)
            }
        }
    }

    /// Try to prove a goal that may contain nested foralls.
    fn try_prove_nested_goal(&self, goal: &Expr, hypotheses: &[Expr]) -> Option<String> {
        if let Some((set_expr, _var, body)) = self.extract_tla_forall_in(goal) {
            if self.is_nat_set(&set_expr) {
                if self.trace {
                    eprintln!("[TLA] nested: found nested ∀m ∈ Nat, trying recursive induction");
                }
                if let Ok(Some(cert)) = self.do_nat_induction(&body, hypotheses) {
                    return Some(format!(
                        "{{\"tactic\":\"nested_induction\",\"inner\":{}}}",
                        cert
                    ));
                }
            }
        }

        if let Some(body) = self.extract_forall_nat(goal) {
            if self.trace {
                eprintln!("[TLA] nested: found nested ∀n : Nat, trying recursive induction");
            }
            if let Ok(Some(cert)) = self.do_nat_induction(&body, hypotheses) {
                return Some(format!(
                    "{{\"tactic\":\"nested_induction\",\"inner\":{}}}",
                    cert
                ));
            }
        }

        if let Some(cert) = self.try_arith_simplify(goal) {
            return Some(cert);
        }

        if let Some(cert) = self.try_arith_simplify_with_hypotheses(goal, hypotheses) {
            return Some(cert);
        }

        None
    }

    /// Try to prove step case for nested foralls.
    fn try_nested_forall_step_case(
        &self,
        step_body: &Expr,
        hypotheses: &[Expr],
    ) -> Result<Option<String>, TlaError> {
        let ExprKind::Pi(_, p_n, p_succ_n) = step_body.kind() else {
            return Ok(None);
        };

        let ih_forall = self.extract_tla_forall_in(p_n).or_else(|| {
            self.extract_forall_nat(p_n).map(|body| {
                let nat = Expr::const_(Name::from_string("TLA.Nat"), vec![]);
                (nat, "m".to_string(), body)
            })
        });

        let goal_forall = self.extract_tla_forall_in(p_succ_n).or_else(|| {
            self.extract_forall_nat(p_succ_n).map(|body| {
                let nat = Expr::const_(Name::from_string("TLA.Nat"), vec![]);
                (nat, "m".to_string(), body)
            })
        });

        let (Some((ih_set, _, ih_body)), Some((goal_set, _, goal_body))) = (ih_forall, goal_forall)
        else {
            return Ok(None);
        };

        if !self.exprs_equal(&ih_set, &goal_set) {
            return Ok(None);
        }

        if self.trace {
            eprintln!("[TLA] nested_step: found (∀m, P(n,m)) → (∀m, P(succ n,m))");
        }

        let inner_step = Expr::arrow(ih_body.clone(), goal_body.clone());

        if let Some(cert) = self.try_arith_step_case(&inner_step) {
            if self.trace {
                eprintln!("[TLA] nested_step: inner step proved via arith");
            }
            return Ok(Some(format!(
                "{{\"tactic\":\"nested_forall_step\",\"inner\":{}}}",
                cert
            )));
        }

        if self.extract_tla_forall_in(&ih_body).is_some()
            || self.extract_forall_nat(&ih_body).is_some()
        {
            if self.trace {
                eprintln!("[TLA] nested_step: ih_body is still a forall, recursing");
            }
            if let Ok(Some(cert)) = self.try_nested_forall_step_case(&inner_step, hypotheses) {
                return Ok(Some(format!(
                    "{{\"tactic\":\"nested_forall_step\",\"recursive\":{}}}",
                    cert
                )));
            }
        }

        if let (Some((ih_lhs, ih_rhs)), Some((goal_lhs, goal_rhs))) = (
            self.extract_equality(&ih_body),
            self.extract_equality(&goal_body),
        ) {
            if self.trace {
                eprintln!(
                    "[TLA] nested_step: IH = {} = {}",
                    self.expr_debug(&self.normalize_arith(&ih_lhs)),
                    self.expr_debug(&self.normalize_arith(&ih_rhs))
                );
                eprintln!(
                    "[TLA] nested_step: goal = {} = {}",
                    self.expr_debug(&self.normalize_arith(&goal_lhs)),
                    self.expr_debug(&self.normalize_arith(&goal_rhs))
                );
            }

            // SOUNDNESS: prove the inner step `ih_body → goal_body` by actually
            // *using* the induction hypothesis, not by any structural shift
            // heuristic. The previous `check_shifted_equality` branch accepted
            // the step whenever each side gained one `Nat.succ` node (a count
            // tally). That is unsound: the goal `P(succ n)` is ALWAYS the IH
            // `P(n)` with the induction variable shifted, by construction of the
            // step case, so a per-side shift/count match witnesses nothing — it
            // fired on genuinely-false goals like `∀n,m: (m+n)=(m+n*n)` and
            // `∀n,m: (n+m)=(n+m+m)`. The sound discharge is: rewrite the goal's
            // LHS with the IH equation (`ih_lhs ↦ ih_rhs`) and require the
            // result to normalize equal to the goal's RHS (and the symmetric
            // direction). This is a real congruence check, not a shift tally.
            if self.step_equality_follows_from_ih(&ih_lhs, &ih_rhs, &goal_lhs, &goal_rhs) {
                if self.trace {
                    eprintln!("[TLA] nested_step: goal equality discharged from IH by rewriting");
                }
                return Ok(Some("{\"tactic\":\"nested_forall_step\",\"method\":\"ih_rewrite\",\"status\":\"proved\"}".to_string()));
            }
        }

        // Try SMT on the inner step wrapped in a forall
        let inner_step_forall = if self.is_nat_set(&ih_set) {
            Expr::pi(
                BinderInfo::Default,
                Expr::const_(Name::from_string("Nat"), vec![]),
                inner_step,
            )
        } else {
            inner_step
        };

        match self.try_superposition(&self.wrap_with_hypotheses(hypotheses, inner_step_forall))? {
            Some(cert) => Ok(Some(format!(
                "{{\"tactic\":\"nested_forall_step\",\"inner\":{}}}",
                cert
            ))),
            None => Ok(None),
        }
    }

    /// Discharge the inner step equality `goal_lhs = goal_rhs` from the
    /// induction hypothesis `ih_lhs = ih_rhs`, soundly.
    ///
    /// SOUNDNESS: this replaces the former `check_shifted_equality` succ-count
    /// tally, which was unsound (see the call site in
    /// [`Self::try_nested_forall_step_case`]). The step is accepted ONLY when
    /// the goal equality genuinely follows from the IH equation used as a
    /// rewrite:
    ///
    /// 1. Rewrite the goal's LHS by substituting `ih_lhs ↦ ih_rhs` (and the
    ///    symmetric `ih_rhs ↦ ih_lhs`), normalize, and require it to equal the
    ///    normalized goal RHS. This is a real use of the hypothesis — a
    ///    congruence/rewrite check, not a structural shift.
    /// 2. As a strictly-weaker fallback, accept when the goal equality is a
    ///    standalone identity (both sides normalize equal) *independently* of
    ///    the IH — this is always sound (it does not depend on the IH at all).
    ///
    /// If neither holds, return `false` so the caller falls through to a sound
    /// prover (fail-closed). This rejects the false `∀n,m:(m+n)=(m+n*n)` family
    /// because rewriting `m+succ n` with `m+n ↦ m+n*n` does not yield the goal
    /// RHS `m + (succ n)*(succ n)`.
    fn step_equality_follows_from_ih(
        &self,
        ih_lhs: &Expr,
        ih_rhs: &Expr,
        goal_lhs: &Expr,
        goal_rhs: &Expr,
    ) -> bool {
        let ih_lhs_norm = self.normalize_arith(ih_lhs);
        let ih_rhs_norm = self.normalize_arith(ih_rhs);
        let goal_lhs_norm = self.normalize_arith(goal_lhs);
        let goal_rhs_norm = self.normalize_arith(goal_rhs);

        // (2) Standalone identity: goal holds without the IH. Always sound.
        if self.exprs_equal(&goal_lhs_norm, &goal_rhs_norm) {
            return true;
        }

        // (1) Rewrite the goal LHS using the IH equation in both directions,
        //     normalize, and require the two sides of the goal to coincide.
        let via_forward =
            self.normalize_arith(&self.substitute_ih(&goal_lhs_norm, &ih_lhs_norm, &ih_rhs_norm));
        if self.exprs_equal(&via_forward, &goal_rhs_norm) {
            return true;
        }
        let via_backward =
            self.normalize_arith(&self.substitute_ih(&goal_lhs_norm, &ih_rhs_norm, &ih_lhs_norm));
        if self.exprs_equal(&via_backward, &goal_rhs_norm) {
            return true;
        }

        // Symmetric: rewrite the goal RHS toward the goal LHS.
        let rhs_forward =
            self.normalize_arith(&self.substitute_ih(&goal_rhs_norm, &ih_lhs_norm, &ih_rhs_norm));
        if self.exprs_equal(&rhs_forward, &goal_lhs_norm) {
            return true;
        }
        let rhs_backward =
            self.normalize_arith(&self.substitute_ih(&goal_rhs_norm, &ih_rhs_norm, &ih_lhs_norm));
        if self.exprs_equal(&rhs_backward, &goal_lhs_norm) {
            return true;
        }

        false
    }

    /// Try well-founded induction
    pub(super) fn try_wf_induction(&self, goal: &Expr) -> Result<Option<String>, TlaError> {
        let Some((set_expr, var_name, body)) = self.extract_tla_forall_in(goal) else {
            if self.trace {
                eprintln!("[TLA] wf_induction: goal is not ForallIn pattern, falling back");
            }
            return self.try_superposition(goal);
        };

        if self.trace {
            eprintln!(
                "[TLA] wf_induction: found ∀{} ∈ S. P({})",
                var_name, var_name
            );
        }

        if self.extract_product_type(&set_expr).is_some() {
            if self.trace {
                eprintln!("[TLA] wf_induction: detected product type, delegating to lex_induction");
            }
            if let Some(cert) = self.try_lex_induction(goal)? {
                return Ok(Some(cert));
            }
        }

        let is_nat_set = self.is_nat_set(&set_expr);
        let (wf_rel, rel_desc) = self.get_wf_relation(&set_expr);

        let pred_rel = Expr::app(
            Expr::app(wf_rel.clone(), Expr::from_kind(ExprKind::BVar(0))),
            Expr::from_kind(ExprKind::BVar(1)),
        );

        let p_y = body.clone();
        let ih_inner = Expr::arrow(pred_rel, p_y);

        let tla_value = Expr::const_(Name::from_string("TLA.Value"), vec![]);
        let ih_body = Expr::pi(BinderInfo::Default, tla_value.clone(), ih_inner);

        let induction_hyp = Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("TLA.forallIn"), vec![]),
                set_expr.clone(),
            ),
            Expr::lam(BinderInfo::Default, tla_value.clone(), ih_body),
        );

        let step_case = Expr::arrow(induction_hyp, body.clone());

        if self.trace {
            eprintln!("[TLA] wf_induction: trying step case");
        }

        if let Some(step_cert) = self.try_superposition(&step_case)? {
            if self.trace {
                eprintln!("[TLA] wf_induction: step case proved!");
            }

            if self.is_trivially_true(&body) {
                return Ok(Some(format!(
                    "{{\"tactic\":\"wf_induction\",\"method\":\"trivial\",\"relation\":\"{}\",\"set\":\"S\",\"status\":\"proved\"}}",
                    rel_desc
                )));
            }

            return Ok(Some(format!(
                "{{\"tactic\":\"wf_induction\",\"method\":\"minimality\",\"relation\":\"{}\",\"step\":{},\"status\":\"proved\"}}",
                rel_desc,
                step_cert
            )));
        }

        if is_nat_set {
            let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
            let base_case = body.instantiate(&zero);

            if let Some(base_cert) = self.try_superposition(&base_case)? {
                if self.trace {
                    eprintln!("[TLA] wf_induction: Nat base case P(0) proved");
                }

                if let Some(full_cert) = self.try_superposition(goal)? {
                    return Ok(Some(format!(
                        "{{\"tactic\":\"wf_induction\",\"method\":\"nat_wf\",\"base\":{},\"full\":{},\"status\":\"proved\"}}",
                        base_cert,
                        full_cert
                    )));
                }
            }
        }

        if self.trace {
            eprintln!("[TLA] wf_induction: step case failed, trying direct SMT");
        }

        if let Some(cert) = self.try_superposition(goal)? {
            return Ok(Some(format!(
                "{{\"tactic\":\"wf_induction\",\"method\":\"smt_fallback\",\"inner\":{},\"status\":\"proved\"}}",
                cert
            )));
        }

        Ok(None)
    }

    /// Extract (set, var_name, body) from TLA.forallIn S (λx. P(x))
    pub(super) fn extract_tla_forall_in(&self, goal: &Expr) -> Option<(Expr, String, Expr)> {
        if let ExprKind::App(f, lam) = goal.kind() {
            if let ExprKind::App(forall_in, set) = f.kind() {
                if let ExprKind::Const(name, _) = forall_in.kind() {
                    if name.to_string() == "TLA.forallIn" {
                        if let ExprKind::Lam(_, _, body) = lam.kind() {
                            return Some((
                                set.as_ref().clone(),
                                "x".to_string(),
                                body.as_ref().clone(),
                            ));
                        }
                    }
                }
            }
        }

        if let ExprKind::Pi(binder_data, ty, body) = goal.kind() {
            if !matches!(binder_data.info, BinderInfo::Implicit) {
                if let ExprKind::Const(ty_name, _) = ty.kind() {
                    if ty_name.to_string() == "TLA.Value" {
                        let generic_set = Expr::const_(Name::from_string("TLA.Universe"), vec![]);
                        return Some((generic_set, "x".to_string(), body.as_ref().clone()));
                    }
                }
            }
        }

        None
    }

    /// Specialize hypotheses with ForallIn quantifiers based on target expression.
    pub(super) fn specialize_forall_hypotheses(
        &self,
        hypotheses: &[Expr],
        target: &Expr,
    ) -> Vec<Expr> {
        let mut specialized = Vec::new();

        for hyp in hypotheses {
            for spec in self.specialize_single_hypothesis(hyp, target) {
                specialized.push(spec);
            }
        }

        specialized
    }

    /// Specialize a single hypothesis based on target expression.
    fn specialize_single_hypothesis(&self, hyp: &Expr, target: &Expr) -> Vec<Expr> {
        let mut results = Vec::new();

        if let Some((set_expr, _var, body)) = self.extract_tla_forall_in(hyp) {
            if self.is_nat_set(&set_expr) {
                if let Some(value) = self.find_specialization_value(&body, target) {
                    let specialized_body = body.instantiate(&value);

                    if self.trace {
                        eprintln!(
                            "[TLA] specialize: ∀n ∈ Nat. {} => {}",
                            self.expr_debug(&body),
                            self.expr_debug(&specialized_body)
                        );
                    }

                    results.push(specialized_body.clone());

                    if self.extract_tla_forall_in(&specialized_body).is_some() {
                        for inner_spec in
                            self.specialize_single_hypothesis(&specialized_body, target)
                        {
                            results.push(inner_spec);
                        }
                    }
                }
            }
        }

        results
    }

    fn find_specialization_value(&self, body: &Expr, target: &Expr) -> Option<Expr> {
        self.find_specialization_value_at_depth(body, target, 0)
    }

    fn find_specialization_value_at_depth(
        &self,
        body: &Expr,
        target: &Expr,
        depth: u32,
    ) -> Option<Expr> {
        if let Some((body_lhs, _body_rhs)) = self.extract_equality(body) {
            return self.match_expr_for_bvar_at_depth(&body_lhs, target, depth);
        }

        if let Some((_op, body_lhs, _rhs)) = self.extract_comparison(body) {
            return self.match_expr_for_bvar_at_depth(&body_lhs, target, depth);
        }

        if let Some((_set, _var, inner_body)) = self.extract_tla_forall_in(body) {
            return self.find_specialization_value_at_depth(&inner_body, target, depth + 1);
        }

        None
    }

    fn match_expr_for_bvar_at_depth(
        &self,
        pattern: &Expr,
        concrete: &Expr,
        depth: u32,
    ) -> Option<Expr> {
        match (pattern.kind(), concrete.kind()) {
            (ExprKind::BVar(idx), _) if *idx == depth => Some(concrete.clone()),
            (ExprKind::App(pf, pa), ExprKind::App(cf, ca)) => {
                if let Some(val) = self.match_expr_for_bvar_at_depth(pf, cf, depth) {
                    return Some(val);
                }
                self.match_expr_for_bvar_at_depth(pa, ca, depth)
            }
            (ExprKind::Const(p_name, _), ExprKind::Const(c_name, _)) if p_name == c_name => None,
            (ExprKind::Lit(p), ExprKind::Lit(c)) if p == c => None,
            _ => None,
        }
    }

    /// Check if expression is a product type (A × B)
    pub(super) fn extract_product_type(&self, expr: &Expr) -> Option<(Expr, Expr)> {
        if let ExprKind::App(f, b) = expr.kind() {
            if let ExprKind::App(prod, a) = f.kind() {
                if let ExprKind::Const(name, _) = prod.kind() {
                    let s = name.to_string();
                    if s == "Prod" || s == "TLA.cross" || s == "×" {
                        return Some((a.as_ref().clone(), b.as_ref().clone()));
                    }
                }
            }
        }
        None
    }

    /// Build lexicographic ordering relation for a product type.
    pub(super) fn build_lex_ordering(&self, ty_a: &Expr, ty_b: &Expr) -> Expr {
        let rel_a = if self.is_nat_set(ty_a) {
            "Nat.lt"
        } else {
            "TLA.wf_rel"
        };

        let rel_b = if self.is_nat_set(ty_b) {
            "Nat.lt"
        } else {
            "TLA.wf_rel"
        };

        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("TLA.lex_lt"), vec![]),
                Expr::const_(Name::from_string(rel_a), vec![]),
            ),
            Expr::const_(Name::from_string(rel_b), vec![]),
        )
    }

    /// Get the appropriate well-founded relation for a set expression.
    pub(super) fn get_wf_relation(&self, set_expr: &Expr) -> (Expr, String) {
        if self.is_nat_set(set_expr) {
            return (
                Expr::const_(Name::from_string("Nat.lt"), vec![]),
                "Nat.lt".to_string(),
            );
        }

        if let Some((ty_a, ty_b)) = self.extract_product_type(set_expr) {
            let lex_rel = self.build_lex_ordering(&ty_a, &ty_b);
            return (lex_rel, "lex_lt".to_string());
        }

        (
            Expr::const_(Name::from_string("TLA.wf_rel"), vec![]),
            "TLA.wf_rel".to_string(),
        )
    }

    /// Try well-founded induction with lexicographic ordering on product types.
    pub(super) fn try_lex_induction(&self, goal: &Expr) -> Result<Option<String>, TlaError> {
        let Some((set_expr, _var_name, body)) = self.extract_tla_forall_in(goal) else {
            return Ok(None);
        };

        let Some((ty_a, ty_b)) = self.extract_product_type(&set_expr) else {
            return Ok(None);
        };

        if self.trace {
            eprintln!("[TLA] lex_induction: detected product type, using lexicographic ordering");
        }

        let rel_desc = format!(
            "lex({}×{})",
            if self.is_nat_set(&ty_a) { "Nat" } else { "?" },
            if self.is_nat_set(&ty_b) { "Nat" } else { "?" }
        );

        if self.is_trivially_true(&body) {
            return Ok(Some(format!(
                "{{\"tactic\":\"lex_induction\",\"method\":\"trivial\",\"relation\":\"{}\",\"status\":\"proved\"}}",
                rel_desc
            )));
        }

        if let Some(cert) = self.try_superposition(goal)? {
            return Ok(Some(format!(
                "{{\"tactic\":\"lex_induction\",\"relation\":\"{}\",\"inner\":{},\"status\":\"proved\"}}",
                rel_desc, cert
            )));
        }

        // SOUNDNESS: the Nat×Nat branch used to return `proved` unconditionally
        // on domain shape alone, discharging NEITHER a base case NOR the
        // lexicographic descent obligation. That certified genuinely-false
        // goals like `∀p ∈ Nat×Nat: 0 = 1`. Lexicographic well-founded
        // induction over Nat×Nat is valid only if the base case(s) and the
        // descent/step obligation are actually discharged — which is exactly
        // what the `try_superposition(goal)` attempt above tries. If that did
        // not close the goal, we have no discharge, so fall through to
        // not-proved (`Ok(None)`) rather than mint a certificate from the
        // domain shape. Over-conservatism here is sound; the structural accept
        // was not.
        if self.trace && self.is_nat_set(&ty_a) && self.is_nat_set(&ty_b) {
            eprintln!(
                "[TLA] lex_induction: Nat×Nat detected but no base/step discharged — not proved"
            );
        }

        Ok(None)
    }
}

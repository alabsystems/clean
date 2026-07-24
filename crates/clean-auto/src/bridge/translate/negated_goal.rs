// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::super::scoring::QuantifierPriorityScorer;
use super::super::{
    BridgeError, BridgeResult, LogicalForm, PendingForall, QuantifierOrigin, SmtBridge,
};
use crate::smt::{TermId, TheoryLiteral};
use clean_kernel::name::Name;
use clean_kernel::Expr;

impl<'env> SmtBridge<'env> {
    /// Translate a classified proposition and assert its negation.
    pub(crate) fn translate_negated_classified(&mut self, prop: &LogicalForm) -> BridgeResult<()> {
        match prop {
            LogicalForm::Eq { .. } | LogicalForm::Neq { .. } => {
                self.translate_negated_equality(prop)
            }
            LogicalForm::Lt { .. }
            | LogicalForm::Le { .. }
            | LogicalForm::Gt { .. }
            | LogicalForm::Ge { .. } => self.translate_negated_comparison(prop),
            LogicalForm::And(..)
            | LogicalForm::Or(..)
            | LogicalForm::Implies(..)
            | LogicalForm::Not(..)
            | LogicalForm::Atom(..) => self.translate_negated_connective(prop),
            LogicalForm::Forall {
                binder_type, body, ..
            } => self.translate_negated_forall(binder_type, body),
            LogicalForm::Exists {
                binder_type, body, ..
            } => self.translate_negated_exists(binder_type, body),
            LogicalForm::True => {
                // `¬True = False` -> empty clause -> UNSAT.
                self.smt.add_clause(vec![]);
                Ok(())
            }
            LogicalForm::False => {
                // `¬False = True` -> tautology -> no-op.
                Ok(())
            }
            // Iff and arithmetic are folded by classify_prop before reaching
            // translate_negated_classified. Fail closed so a future refactor
            // that stops folding a variant produces an error instead of
            // silently dropping a clause (which could cause false SAT/UNSAT).
            LogicalForm::Iff(..)
            | LogicalForm::Add { .. }
            | LogicalForm::Sub { .. }
            | LogicalForm::Mul { .. }
            | LogicalForm::Div { .. }
            | LogicalForm::Mod { .. }
            | LogicalForm::Neg { .. } => {
                debug_assert!(
                    false,
                    "LogicalForm variant should be folded by classify_prop before reaching translate_negated_classified"
                );
                Err(BridgeError::UnsupportedExpr {
                    context: "LogicalForm variant not folded by classify_prop".into(),
                })
            }
        }
    }

    fn translate_negated_equality(&mut self, prop: &LogicalForm) -> BridgeResult<()> {
        match prop {
            LogicalForm::Eq { lhs, rhs, .. } => {
                let t1 = self.translate_term(lhs)?;
                let t2 = self.translate_term(rhs)?;
                let _ = self.smt.assert_neq(t1, t2);
                Ok(())
            }
            LogicalForm::Neq { lhs, rhs, .. } => {
                let t1 = self.translate_term(lhs)?;
                let t2 = self.translate_term(rhs)?;
                let _ = self.smt.assert_eq(t1, t2);
                Ok(())
            }
            _ => unreachable!("non-equality form routed to translate_negated_equality"),
        }
    }

    fn translate_negated_comparison(&mut self, prop: &LogicalForm) -> BridgeResult<()> {
        match prop {
            // `¬(a < b) ≡ b <= a`
            LogicalForm::Lt { lhs, rhs, .. } => {
                let t1 = self.translate_term(lhs)?;
                let t2 = self.translate_term(rhs)?;
                self.smt.add_clause(vec![TheoryLiteral::Le(t2, t1)]);
                Ok(())
            }
            // `¬(a <= b) ≡ b < a`
            LogicalForm::Le { lhs, rhs, .. } => {
                let t1 = self.translate_term(lhs)?;
                let t2 = self.translate_term(rhs)?;
                self.smt.add_clause(vec![TheoryLiteral::Lt(t2, t1)]);
                Ok(())
            }
            // `¬(a > b) ≡ a <= b`
            LogicalForm::Gt { lhs, rhs, .. } => {
                let t1 = self.translate_term(lhs)?;
                let t2 = self.translate_term(rhs)?;
                self.smt.add_clause(vec![TheoryLiteral::Le(t1, t2)]);
                Ok(())
            }
            // `¬(a >= b) ≡ a < b`
            LogicalForm::Ge { lhs, rhs, .. } => {
                let t1 = self.translate_term(lhs)?;
                let t2 = self.translate_term(rhs)?;
                self.smt.add_clause(vec![TheoryLiteral::Lt(t1, t2)]);
                Ok(())
            }
            _ => unreachable!("non-comparison form routed to translate_negated_comparison"),
        }
    }

    fn translate_negated_connective(&mut self, prop: &LogicalForm) -> BridgeResult<()> {
        match prop {
            LogicalForm::And(p, q) => {
                let np = self.prop_to_literal(p, false)?;
                let nq = self.prop_to_literal(q, false)?;
                self.smt.add_clause(vec![np, nq]);
                Ok(())
            }
            LogicalForm::Or(p, q) => {
                let np = self.prop_to_literal(p, false)?;
                let nq = self.prop_to_literal(q, false)?;
                self.smt.add_clause(vec![np.clone()]);
                self.smt.add_clause(vec![nq.clone()]);
                Ok(())
            }
            LogicalForm::Implies(p, q) => {
                let pp = self.prop_to_literal(p, true)?;
                let nq = self.prop_to_literal(q, false)?;
                self.smt.add_clause(vec![pp.clone()]);
                self.smt.add_clause(vec![nq.clone()]);
                Ok(())
            }
            LogicalForm::Not(p) => {
                let pp = self.prop_to_literal(p, true)?;
                self.smt.add_clause(vec![pp]);
                Ok(())
            }
            LogicalForm::Atom(expr) => {
                let lit = self.prop_to_literal(expr, false)?;
                self.smt.add_clause(vec![lit]);
                Ok(())
            }
            _ => unreachable!("non-connective form routed to translate_negated_connective"),
        }
    }

    fn translate_negated_forall(&mut self, binder_type: &Expr, body: &Expr) -> BridgeResult<()> {
        // `¬(forall x : T, P(x)) ≡ exists x : T, ¬P(x)`.
        let (bound_types, flat_body) = self.flatten_forall(binder_type, body);
        let bound_count = u32::try_from(bound_types.len())
            .expect("invariant: forall bound-variable count fits in u32");
        let witness_bound_vars = Self::flattened_bvar_indices(bound_count);

        let witness_terms = self.create_named_witness_terms("sk", &bound_types);
        self.translate_instantiated_negated_body(&flat_body, &witness_bound_vars, &witness_terms)
    }

    fn translate_negated_exists(&mut self, binder_type: &Expr, body: &Expr) -> BridgeResult<()> {
        // `¬(exists x : T, P(x)) ≡ forall x : T, ¬P(x)`.
        // Add bounded concrete instances first: these are sound because they are
        // specific instances of the universal negation and let the solver close
        // easy existential goals using real in-scope witnesses instead of only
        // synthetic bridge locals.
        for witness in self.goal_scoped_witness_candidates(binder_type) {
            let inst = self.instantiate_bvars(body, &[(0, witness)]);
            self.translate_negated_classified(&self.classify_prop(&inst))?;
        }

        let (bound_types, flat_body) = self.flatten_exists(binder_type, body);
        let bound_count = u32::try_from(bound_types.len())
            .expect("invariant: exists bound-variable count fits in u32");
        let pending_bound_vars: Vec<u32> = (0..bound_count).collect();
        let witness_bound_vars = Self::flattened_bvar_indices(bound_count);

        self.queue_negated_exists_pending_forall(&bound_types, &flat_body, &pending_bound_vars);

        let witness_terms = self.create_named_witness_terms("neg_exists_witness", &bound_types);
        self.translate_instantiated_negated_body(&flat_body, &witness_bound_vars, &witness_terms)
    }

    fn translate_negated_lossy_clause(&mut self, expr: &Expr) -> BridgeResult<()> {
        self.record_lossy_expr(expr);
        let var_id = self.fresh_counter;
        self.fresh_counter += 1;
        self.smt.add_clause(vec![TheoryLiteral::Bool(var_id)]);
        Ok(())
    }

    fn queue_negated_exists_pending_forall(
        &mut self,
        bound_types: &[Expr],
        flat_body: &Expr,
        pending_bound_vars: &[u32],
    ) {
        let triggers = self.extract_ematch_triggers(flat_body, pending_bound_vars);
        if triggers.is_empty() {
            return;
        }

        let not_const = Expr::const_(Name::from_string("Not"), vec![]);
        let neg_body = Expr::app(not_const, flat_body.clone());

        let pending = PendingForall {
            _tys: bound_types.to_vec(),
            body: neg_body,
            triggers,
            bound_vars: pending_bound_vars.to_vec(),
            priority: 0,
            instantiation_count: 0,
            origin: Some(QuantifierOrigin::Synthesized),
        };
        let scorer = QuantifierPriorityScorer::new();
        let priority = scorer.score(&pending);
        self.pending_foralls.push(PendingForall {
            priority,
            ..pending
        });
    }

    fn create_named_witness_terms(&mut self, prefix: &str, bound_types: &[Expr]) -> Vec<TermId> {
        let mut witness_terms = Vec::with_capacity(bound_types.len());
        for (i, bound_ty) in bound_types.iter().enumerate() {
            let witness_name = format!("{prefix}_{}_{}", i, self.fresh_counter);
            self.fresh_counter += 1;
            witness_terms.push(self.create_witness_term(&witness_name, bound_ty));
        }
        witness_terms
    }

    fn translate_instantiated_negated_body(
        &mut self,
        flat_body: &Expr,
        witness_bound_vars: &[u32],
        witness_terms: &[TermId],
    ) -> BridgeResult<()> {
        let instantiated_body =
            self.instantiate_body_with_terms(flat_body, witness_bound_vars, witness_terms);
        if let Some(inst) = instantiated_body {
            return self.translate_negated_classified(&self.classify_prop(&inst));
        }

        self.translate_negated_lossy_clause(flat_body)
    }
}

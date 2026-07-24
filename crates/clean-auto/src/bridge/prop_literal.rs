// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proposition-to-literal translation with Tseitin encoding.
//!
//! Converts classified propositions (`LogicalForm`) into `TheoryLiteral` values
//! suitable for the SAT solver. Propositional connectives (And, Or, Implies,
//! Not, True, False) are encoded via standard Tseitin transformation: each
//! compound sub-formula gets a fresh boolean variable `p` with clauses
//! constraining `p <=> sub-formula`. This is linear in formula size.
//!
//! Quantifiers (Forall, Exists) remain lossy atoms tracked in
//! `SmtBridge::lossy_atoms` until Phase 3 (Skolemization).

use super::expr_classifier::LogicalForm;
use super::translate::ExprKey;
use super::{BridgeError, BridgeResult, SmtBridge};
use crate::smt::TheoryLiteral;
use clean_kernel::Expr;

impl<'env> SmtBridge<'env> {
    /// Translate a proposition to a theory literal (with polarity).
    ///
    /// For atomic propositions (equalities, comparisons, opaque atoms), returns
    /// the corresponding `TheoryLiteral` directly. For compound propositions,
    /// applies Tseitin encoding: introduces a fresh boolean variable `p` and
    /// adds clauses that constrain `p <=> sub-formula`, then returns `Bool(p)`
    /// or `NegBool(p)` depending on the requested polarity.
    pub(super) fn prop_to_literal(
        &mut self,
        prop: &Expr,
        positive: bool,
    ) -> BridgeResult<TheoryLiteral> {
        crate::bridge::stack_safe(|| match self.classify_prop(prop) {
            LogicalForm::Eq { ty: _, lhs, rhs } => {
                let t1 = self.translate_term(&lhs)?;
                let t2 = self.translate_term(&rhs)?;
                if positive {
                    Ok(TheoryLiteral::Eq(t1, t2))
                } else {
                    Ok(TheoryLiteral::Neq(t1, t2))
                }
            }
            LogicalForm::Neq { ty: _, lhs, rhs } => {
                let t1 = self.translate_term(&lhs)?;
                let t2 = self.translate_term(&rhs)?;
                if positive {
                    Ok(TheoryLiteral::Neq(t1, t2))
                } else {
                    Ok(TheoryLiteral::Eq(t1, t2))
                }
            }
            LogicalForm::Lt { ty: _, lhs, rhs } => {
                let t1 = self.translate_term(&lhs)?;
                let t2 = self.translate_term(&rhs)?;
                if positive {
                    Ok(TheoryLiteral::Lt(t1, t2))
                } else {
                    // ¬(a < b) ≡ b ≤ a
                    Ok(TheoryLiteral::Le(t2, t1))
                }
            }
            LogicalForm::Le { ty: _, lhs, rhs } => {
                let t1 = self.translate_term(&lhs)?;
                let t2 = self.translate_term(&rhs)?;
                if positive {
                    Ok(TheoryLiteral::Le(t1, t2))
                } else {
                    // ¬(a ≤ b) ≡ b < a
                    Ok(TheoryLiteral::Lt(t2, t1))
                }
            }
            LogicalForm::Gt { ty: _, lhs, rhs } => {
                let t1 = self.translate_term(&lhs)?;
                let t2 = self.translate_term(&rhs)?;
                // a > b ≡ b < a
                if positive {
                    Ok(TheoryLiteral::Lt(t2, t1))
                } else {
                    // ¬(a > b) ≡ a ≤ b
                    Ok(TheoryLiteral::Le(t1, t2))
                }
            }
            LogicalForm::Ge { ty: _, lhs, rhs } => {
                let t1 = self.translate_term(&lhs)?;
                let t2 = self.translate_term(&rhs)?;
                // a ≥ b ≡ b ≤ a
                if positive {
                    Ok(TheoryLiteral::Le(t2, t1))
                } else {
                    // ¬(a ≥ b) ≡ a < b
                    Ok(TheoryLiteral::Lt(t1, t2))
                }
            }
            LogicalForm::Atom(ref inner) => {
                if Self::requires_lossy_guard(inner) {
                    self.record_lossy_expr(inner);
                }
                // Use the classified inner (MData-stripped) for dedup, not
                // the original `prop` which may be MData-wrapped (#2279)
                let var_id = if let Some(key) = ExprKey::from_expr(inner) {
                    *self.atom_to_var.entry(key).or_insert_with(|| {
                        let id = self.fresh_counter;
                        self.fresh_counter += 1;
                        id
                    })
                } else {
                    // ExprKey::from_expr returns None for Sort, Let, Proj —
                    // fall back to fresh variable (no dedup possible)
                    let id = self.fresh_counter;
                    self.fresh_counter += 1;
                    id
                };
                if positive {
                    Ok(TheoryLiteral::Bool(var_id))
                } else {
                    Ok(TheoryLiteral::NegBool(var_id))
                }
            }
            LogicalForm::And(ref a, ref b) => {
                let lit_a = self.prop_to_literal(a, true)?;
                let lit_b = self.prop_to_literal(b, true)?;
                let p = self.fresh_counter;
                self.fresh_counter += 1;
                // Tseitin: p <=> (a ∧ b)
                self.smt
                    .add_clause(vec![TheoryLiteral::NegBool(p), lit_a.clone()]);
                self.smt
                    .add_clause(vec![TheoryLiteral::NegBool(p), lit_b.clone()]);
                self.smt
                    .add_clause(vec![TheoryLiteral::Bool(p), lit_a.negate(), lit_b.negate()]);
                if positive {
                    Ok(TheoryLiteral::Bool(p))
                } else {
                    Ok(TheoryLiteral::NegBool(p))
                }
            }
            LogicalForm::Or(ref a, ref b) => {
                let lit_a = self.prop_to_literal(a, true)?;
                let lit_b = self.prop_to_literal(b, true)?;
                let p = self.fresh_counter;
                self.fresh_counter += 1;
                // Tseitin: p <=> (a ∨ b)
                self.smt
                    .add_clause(vec![TheoryLiteral::Bool(p), lit_a.negate()]);
                self.smt
                    .add_clause(vec![TheoryLiteral::Bool(p), lit_b.negate()]);
                self.smt.add_clause(vec![
                    TheoryLiteral::NegBool(p),
                    lit_a.clone(),
                    lit_b.clone(),
                ]);
                if positive {
                    Ok(TheoryLiteral::Bool(p))
                } else {
                    Ok(TheoryLiteral::NegBool(p))
                }
            }
            LogicalForm::Implies(ref a, ref b) => {
                let lit_a = self.prop_to_literal(a, true)?;
                let lit_b = self.prop_to_literal(b, true)?;
                let p = self.fresh_counter;
                self.fresh_counter += 1;
                // Tseitin: p <=> (a → b) ≡ p <=> (¬a ∨ b)
                self.smt
                    .add_clause(vec![TheoryLiteral::Bool(p), lit_a.clone()]);
                self.smt
                    .add_clause(vec![TheoryLiteral::Bool(p), lit_b.negate()]);
                self.smt.add_clause(vec![
                    TheoryLiteral::NegBool(p),
                    lit_a.negate(),
                    lit_b.clone(),
                ]);
                if positive {
                    Ok(TheoryLiteral::Bool(p))
                } else {
                    Ok(TheoryLiteral::NegBool(p))
                }
            }
            LogicalForm::Not(ref a) => {
                // ¬a with polarity flip: no Tseitin variable needed
                self.prop_to_literal(a, !positive)
            }
            LogicalForm::True => {
                let p = self.fresh_counter;
                self.fresh_counter += 1;
                self.smt.add_clause(vec![TheoryLiteral::Bool(p)]);
                if positive {
                    Ok(TheoryLiteral::Bool(p))
                } else {
                    Ok(TheoryLiteral::NegBool(p))
                }
            }
            LogicalForm::False => {
                let p = self.fresh_counter;
                self.fresh_counter += 1;
                self.smt.add_clause(vec![TheoryLiteral::NegBool(p)]);
                if positive {
                    Ok(TheoryLiteral::Bool(p))
                } else {
                    Ok(TheoryLiteral::NegBool(p))
                }
            }
            // Quantifiers remain lossy atoms until Phase 3 (Skolemization)
            LogicalForm::Forall { .. } | LogicalForm::Exists { .. } => {
                let stripped = prop.strip_mdata();
                self.record_lossy_expr(stripped);
                let var_id = if let Some(key) = ExprKey::from_expr(stripped) {
                    *self.atom_to_var.entry(key).or_insert_with(|| {
                        let id = self.fresh_counter;
                        self.fresh_counter += 1;
                        id
                    })
                } else {
                    let id = self.fresh_counter;
                    self.fresh_counter += 1;
                    id
                };
                if positive {
                    Ok(TheoryLiteral::Bool(var_id))
                } else {
                    Ok(TheoryLiteral::NegBool(var_id))
                }
            }
            // Iff and arithmetic are folded by classify_prop — not reachable
            LogicalForm::Iff(..)
            | LogicalForm::Add { .. }
            | LogicalForm::Sub { .. }
            | LogicalForm::Mul { .. }
            | LogicalForm::Div { .. }
            | LogicalForm::Mod { .. }
            | LogicalForm::Neg { .. } => Err(BridgeError::UnsupportedExpr {
                context: "LogicalForm variant not folded by classify_prop".into(),
            }),
        })
    }
}

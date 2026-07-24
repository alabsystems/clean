// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proposition classification and reconstruction for the SMT bridge.
//!
//! Classification delegates to the shared `classify_expr` in `expr_classifier`,
//! which is the single source of truth for Lean expression → logical form mapping.
//! This module provides `classify_prop` (propositional classification with Iff
//! decomposition and arithmetic→Atom folding) and `logicalform_to_expr` for
//! reconstructing kernel expressions from classified forms.

use super::expr_classifier::{classify_expr, LogicalForm};
use super::{BridgeError, BridgeResult, SmtBridge};
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, Level};

impl<'env> SmtBridge<'env> {
    /// Classify a proposition into known logical forms.
    ///
    /// Delegates to the shared `classify_expr` and folds Iff and arithmetic
    /// variants for propositional contexts:
    /// - Iff(a, b) → And(a→b, b→a) (SmtBridge lacks native Iff handling)
    /// - Arithmetic → Atom (SmtBridge handles propositions, not arithmetic terms)
    ///
    /// This eliminates duplicated constant-name matching that was the root
    /// cause of bugs #2261, #2257, #2255, #2260, #2254.
    pub(super) fn classify_prop(&self, expr: &Expr) -> LogicalForm {
        let expr = expr.strip_mdata();
        let classified = match expr.kind() {
            ExprKind::Pi(_, domain, codomain) if self.pi_domain_is_proposition(domain) => {
                LogicalForm::Implies((**domain).clone(), (**codomain).clone())
            }
            _ => classify_expr(expr),
        };

        match classified {
            LogicalForm::Iff(a, b) => {
                // Iff(a, b) ≡ And(Implies(a, b), Implies(b, a))
                // Decompose since SmtBridge consumers don't handle Iff directly.
                let fwd = Expr::pi(BinderInfo::Default, a.clone(), b.clone());
                let bwd = Expr::pi(BinderInfo::Default, b, a);
                LogicalForm::And(fwd, bwd)
            }
            LogicalForm::Neq { ty, lhs, rhs } => {
                // Neq(a, b) ≡ Not(Eq a b) (#2442 Phase 2).
                // Fold so all Not/absurd logic automatically handles ≠ hypotheses and goals.
                let eq_form = LogicalForm::Eq {
                    ty: ty.clone(),
                    lhs: lhs.clone(),
                    rhs: rhs.clone(),
                };
                if let Ok(eq_expr) = self.logicalform_to_expr(&eq_form) {
                    LogicalForm::Not(eq_expr)
                } else {
                    // sort_level_of_type failed — keep as opaque atom
                    LogicalForm::Atom(expr.clone())
                }
            }
            // Arithmetic: fold to opaque atoms for propositional contexts.
            // SmtBridge handles propositions (Bool-sorted), not arithmetic expressions.
            // Use stripped expression so MData-wrapped arithmetic gets consistent
            // atom identity (#2279)
            LogicalForm::Add { .. }
            | LogicalForm::Sub { .. }
            | LogicalForm::Mul { .. }
            | LogicalForm::Div { .. }
            | LogicalForm::Mod { .. }
            | LogicalForm::Neg { .. } => LogicalForm::Atom(expr.clone()),
            other => other,
        }
    }

    fn pi_domain_is_proposition(&self, domain: &Expr) -> bool {
        if matches!(
            classify_expr(domain),
            LogicalForm::Eq { .. }
                | LogicalForm::Neq { .. }
                | LogicalForm::And(..)
                | LogicalForm::Or(..)
                | LogicalForm::Not(..)
                | LogicalForm::Iff(..)
                | LogicalForm::True
                | LogicalForm::False
                | LogicalForm::Lt { .. }
                | LogicalForm::Le { .. }
                | LogicalForm::Gt { .. }
                | LogicalForm::Ge { .. }
                | LogicalForm::Exists { .. }
        ) {
            return true;
        }

        self.make_tc()
            .infer_type(domain.strip_mdata())
            .map(|ty| ty.is_prop())
            .unwrap_or(false)
    }

    /// Convert a LogicalForm back to an Expr (for body extraction and proof reconstruction).
    ///
    /// Handles all propositional forms returned by `classify_prop`. Iff and
    /// arithmetic variants are included for exhaustiveness but are not
    /// reachable from `classify_prop` output (folded to And/Atom respectively).
    ///
    /// # Errors
    ///
    /// Returns `BridgeError::InferSortFailed` when sort inference fails for
    /// forms that require universe levels (Eq, Exists, Lt, Le, Gt, Ge).
    /// This replaces the silent default to `Level::succ(Level::zero())` which
    /// masked proof reconstruction failures (#2331).
    pub(super) fn logicalform_to_expr(&self, form: &LogicalForm) -> BridgeResult<Expr> {
        crate::bridge::stack_safe(|| match form {
            LogicalForm::Eq { ty, lhs, rhs } => {
                // @Eq.{u} α a b — use actual type and derive universe level
                let u = self.sort_level_of_type(ty)?;
                let eq_const = Expr::const_(Name::from_string("Eq"), vec![u]);
                Ok(Expr::app(
                    Expr::app(Expr::app(eq_const, ty.clone()), lhs.clone()),
                    rhs.clone(),
                ))
            }
            LogicalForm::Neq { ty, lhs, rhs } => {
                let eq = self.logicalform_to_expr(&LogicalForm::Eq {
                    ty: ty.clone(),
                    lhs: lhs.clone(),
                    rhs: rhs.clone(),
                })?;
                let not_const = Expr::const_(Name::from_string("Not"), vec![]);
                Ok(Expr::app(not_const, eq))
            }
            LogicalForm::And(p, q) => {
                let and_const = Expr::const_(Name::from_string("And"), vec![]);
                Ok(Expr::app(
                    Expr::app(and_const, self.logicalform_to_expr(&self.classify_prop(p))?),
                    self.logicalform_to_expr(&self.classify_prop(q))?,
                ))
            }
            LogicalForm::Or(p, q) => {
                let or_const = Expr::const_(Name::from_string("Or"), vec![]);
                Ok(Expr::app(
                    Expr::app(or_const, self.logicalform_to_expr(&self.classify_prop(p))?),
                    self.logicalform_to_expr(&self.classify_prop(q))?,
                ))
            }
            LogicalForm::Implies(p, q) => {
                // P → Q as Pi type
                Ok(Expr::pi(
                    BinderInfo::Default,
                    self.logicalform_to_expr(&self.classify_prop(p))?,
                    self.logicalform_to_expr(&self.classify_prop(q))?,
                ))
            }
            LogicalForm::Not(p) => {
                let not_const = Expr::const_(Name::from_string("Not"), vec![]);
                Ok(Expr::app(
                    not_const,
                    self.logicalform_to_expr(&self.classify_prop(p))?,
                ))
            }
            LogicalForm::Forall { binder_type, body } => Ok(Expr::pi(
                BinderInfo::Default,
                binder_type.clone(),
                body.clone(),
            )),
            LogicalForm::Exists { binder_type, body } => {
                // @Exists.{u} (α : Sort u) (p : α → Prop)
                let u = self.sort_level_of_type(binder_type)?;
                let exists_const = Expr::const_(Name::from_string("Exists"), vec![u]);
                let lam = Expr::lam(BinderInfo::Default, binder_type.clone(), body.clone());
                Ok(Expr::app(Expr::app(exists_const, binder_type.clone()), lam))
            }
            LogicalForm::True => Ok(Expr::const_(Name::from_string("True"), vec![])),
            LogicalForm::False => Ok(Expr::const_(Name::from_string("False"), vec![])),
            LogicalForm::Lt { ty, lhs, rhs } => {
                let u = Self::type_universe_level(self.sort_level_of_type(ty))?;
                let lt_const = Expr::const_(Name::from_string("LT.lt"), vec![u]);
                let inst = Self::mk_comparison_inst("LT", ty)?;
                Ok(Expr::app(
                    Expr::app(
                        Expr::app(Expr::app(lt_const, ty.clone()), inst),
                        lhs.clone(),
                    ),
                    rhs.clone(),
                ))
            }
            LogicalForm::Le { ty, lhs, rhs } => {
                let u = Self::type_universe_level(self.sort_level_of_type(ty))?;
                let le_const = Expr::const_(Name::from_string("LE.le"), vec![u]);
                let inst = Self::mk_comparison_inst("LE", ty)?;
                Ok(Expr::app(
                    Expr::app(
                        Expr::app(Expr::app(le_const, ty.clone()), inst),
                        lhs.clone(),
                    ),
                    rhs.clone(),
                ))
            }
            LogicalForm::Gt { ty, lhs, rhs } => {
                let u = Self::type_universe_level(self.sort_level_of_type(ty))?;
                let gt_const = Expr::const_(Name::from_string("GT.gt"), vec![u]);
                let inst = Self::mk_comparison_inst("GT", ty)?;
                Ok(Expr::app(
                    Expr::app(
                        Expr::app(Expr::app(gt_const, ty.clone()), inst),
                        lhs.clone(),
                    ),
                    rhs.clone(),
                ))
            }
            LogicalForm::Ge { ty, lhs, rhs } => {
                let u = Self::type_universe_level(self.sort_level_of_type(ty))?;
                let ge_const = Expr::const_(Name::from_string("GE.ge"), vec![u]);
                let inst = Self::mk_comparison_inst("GE", ty)?;
                Ok(Expr::app(
                    Expr::app(
                        Expr::app(Expr::app(ge_const, ty.clone()), inst),
                        lhs.clone(),
                    ),
                    rhs.clone(),
                ))
            }
            // Iff: decompose to And(→, ←) then reconstruct
            LogicalForm::Iff(a, b) => {
                let iff_const = Expr::const_(Name::from_string("Iff"), vec![]);
                Ok(Expr::app(Expr::app(iff_const, a.clone()), b.clone()))
            }
            // Arithmetic: classify_prop folds these to Atom. Return the original
            // expression for faithful round-trip reconstruction.
            LogicalForm::Add { original, .. }
            | LogicalForm::Sub { original, .. }
            | LogicalForm::Mul { original, .. }
            | LogicalForm::Div { original, .. }
            | LogicalForm::Mod { original, .. }
            | LogicalForm::Neg { original, .. } => Ok(original.clone()),
            LogicalForm::Atom(e) => Ok(e.clone()),
        })
    }

    /// Compute universe level for `Type u` from a sort level.
    ///
    /// Comparison operators (`LT.lt`, `LE.le`, `GT.gt`, `GE.ge`) take `{α : Type u}`
    /// where `Type u = Sort (u+1)`. So if `sort_level_of_type` returns `Succ(inner)`,
    /// the universe parameter is `inner`.
    ///
    /// # Errors
    ///
    /// Propagates `BridgeError::InferSortFailed` from the sort level result.
    /// Returns `BridgeError::InferSortFailed` if the sort level is not `Succ(_)`,
    /// which indicates the type does not live in `Type u` for any `u`.
    pub(super) fn type_universe_level(sort_level: BridgeResult<Level>) -> BridgeResult<Level> {
        match sort_level? {
            Level::Succ(inner) => Ok(inner.as_ref().clone()),
            other => Err(BridgeError::InferSortFailed {
                context: format!("expected Sort (succ u), got Sort {other}"),
            }),
        }
    }

    /// Construct a typeclass instance for a comparison operator and type.
    ///
    /// Lean 4 names instances as `inst{TC}{TypeName}`, e.g. `instLTNat`, `instLEInt`.
    /// GT uses LT instance (`instLTNat`), GE uses LE instance (`instLENat`).
    pub(super) fn mk_comparison_inst(tc_name: &str, ty: &Expr) -> BridgeResult<Expr> {
        let type_suffix = match ty.strip_mdata().get_app_fn().strip_mdata().kind() {
            ExprKind::Const(name, _) => name.to_string(),
            _ => {
                return Err(BridgeError::UnsupportedExpr {
                    context: format!("cannot resolve typeclass instance for type: {ty:?}"),
                });
            }
        };
        let inst_prefix = match tc_name {
            "LT" | "GT" => "instLT",
            "LE" | "GE" => "instLE",
            _ => "instLE",
        };
        Ok(Expr::const_(
            Name::from_string(&format!("{inst_prefix}{type_suffix}")),
            vec![],
        ))
    }
}

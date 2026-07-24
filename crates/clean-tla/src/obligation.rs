// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! TLA+ Proof Obligation Handling
//!
//! Copyright 2026 Andrew Yates
//! Licensed under Apache-2.0
//!
//! This module defines the structure of proof obligations from TLAPS
//! and how they are processed by clean.
//!
//! ## Obligation Format
//!
//! TLAPS generates sequent-style obligations:
//! ```text
//! h1: assumption1
//! h2: assumption2
//! ...
//! ├── goal
//! ```
//!
//! We translate these to clean goals with hypotheses in the local context.

use crate::encoding::{TlaContext, TlaExpr, TlaFormula};
use crate::tla_core;
use crate::TlaError;
use clean_kernel::expr::{BinderInfo, Expr};
use serde::{Deserialize, Serialize};

/// A hypothesis in a TLA+ proof obligation
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct TlaHypothesis {
    /// Hypothesis name (e.g., "h1", "h2")
    pub name: String,
    /// The formula this hypothesis asserts
    pub formula: TlaFormula,
}

/// A TLA+ proof obligation from TLAPS
///
/// Represents a sequent-style obligation:
/// ```text
/// [declares]
/// h1: assumption1, h2: assumption2, ...
/// ├── goal
/// ```
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct TlaObligation {
    /// Module name (for error reporting)
    pub module: String,

    /// Line number in source (for error reporting)
    pub line: Option<u32>,

    /// Constant/operator declarations in scope
    pub declares: Vec<TlaDeclare>,

    /// Hypotheses (assumptions)
    pub hypotheses: Vec<TlaHypothesis>,

    /// Goal to prove
    pub goal: TlaFormula,

    /// Suggested tactic (from TLAPS BY clause)
    pub tactic_hint: Option<String>,
}

/// A declaration in scope for the obligation
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum TlaDeclare {
    /// Constant with arity: CONSTANT Op(_,_)
    Constant { name: String, arity: u32 },

    /// Variable: VARIABLE x
    Variable { name: String },

    /// Operator definition: Op(a, b) == expr
    Operator {
        name: String,
        params: Vec<String>,
        body: TlaExpr,
    },

    /// Assumption: ASSUME P
    Assume { name: String, formula: TlaFormula },

    /// Propositional variable: typed as Prop instead of TLA.Value
    /// Used for pure propositional logic benchmarks where P, Q are
    /// Lean propositions rather than TLA+ set-theoretic values.
    Prop { name: String },

    /// Module instantiation: `INSTANCE M WITH p1 <- e1, p2 <- e2, ...`
    ///
    /// Brings the definitions of module `module` into scope, with each
    /// parameter of `M` (a CONSTANT or VARIABLE declared by `M`) replaced by
    /// the corresponding substitution expression. This is the basis of TLA+
    /// modular composition and refinement: `Impl => Spec` is established by an
    /// `INSTANCE Spec WITH ...` that maps `Spec`'s variables to expressions
    /// over `Impl`'s state (a *refinement mapping*).
    ///
    /// The `substitutions` field records each `from <- to` pair, where `from`
    /// is the name of a parameter of `M` and `to` is the substituting
    /// expression (translated faithfully, never dropped). During
    /// [`TlaObligation::to_clean_goal`] every reference to a substituted
    /// parameter resolves to its mapped expression, so the substitution is
    /// applied consistently to all references from the instantiated module.
    Instance {
        /// Name of the instantiated module (`M` in `INSTANCE M`).
        module: String,
        /// Parameter-to-expression substitution pairs (`p <- e`).
        substitutions: Vec<(String, TlaExpr)>,
    },
}

impl TlaObligation {
    /// Create a new obligation
    pub fn new(goal: TlaFormula) -> Self {
        Self {
            module: String::new(),
            line: None,
            declares: Vec::new(),
            hypotheses: Vec::new(),
            goal,
            tactic_hint: None,
        }
    }

    /// Create a new obligation from a canonical `tla-core` goal expression.
    pub fn from_tla_core_goal(
        goal: &tla_core::Spanned<tla_core::ast::Expr>,
    ) -> Result<Self, TlaError> {
        Ok(Self::new(TlaFormula::from_tla_core(goal)?))
    }

    /// Add a hypothesis
    pub fn with_hypothesis(mut self, name: &str, formula: TlaFormula) -> Self {
        self.hypotheses.push(TlaHypothesis {
            name: name.to_string(),
            formula,
        });
        self
    }

    /// Add a hypothesis expressed with the canonical `tla-core` AST.
    pub fn with_tla_core_hypothesis(
        mut self,
        name: &str,
        formula: &tla_core::Spanned<tla_core::ast::Expr>,
    ) -> Result<Self, TlaError> {
        self.hypotheses.push(TlaHypothesis {
            name: name.to_string(),
            formula: TlaFormula::from_tla_core(formula)?,
        });
        Ok(self)
    }

    /// Add a declaration
    pub fn with_declare(mut self, decl: TlaDeclare) -> Self {
        self.declares.push(decl);
        self
    }

    /// Add declarations converted from a canonical `tla-core` unit.
    pub fn with_tla_core_unit(mut self, unit: &tla_core::ast::Unit) -> Result<Self, TlaError> {
        self.declares.extend(TlaDeclare::from_tla_core_unit(unit)?);
        Ok(self)
    }

    /// Set module name
    pub fn in_module(mut self, module: &str) -> Self {
        self.module = module.to_string();
        self
    }

    /// Set line number
    pub fn at_line(mut self, line: u32) -> Self {
        self.line = Some(line);
        self
    }

    /// Set tactic hint
    pub fn with_tactic(mut self, tactic: &str) -> Self {
        self.tactic_hint = Some(tactic.to_string());
        self
    }

    /// Translate this obligation to a clean goal type
    ///
    /// The resulting expression is a Pi type encoding:
    /// ```text
    /// ∀ (decls...), h1 → h2 → ... → goal
    /// ```
    ///
    /// ## De Bruijn Index Computation
    ///
    /// For correct de Bruijn indices, we account for all binders in order:
    /// 1. Prop declarations (outermost)
    /// 2. Hypotheses (between props and goal body)
    /// 3. The goal body (innermost)
    ///
    /// Example: `∀ P Q : Prop, Q → P ∨ Q`
    /// - P is outermost (depth 2 from goal body)
    /// - Q is next (depth 1 from goal body)
    /// - h_q : Q is innermost binder (depth 0 from goal body)
    /// - Goal body: Or(BVar(2), BVar(1)) with h_q type BVar(0) when props in scope
    pub fn to_clean_goal(&self, ctx: &mut TlaContext) -> Result<Expr, TlaError> {
        // Phase 0: Apply INSTANCE substitutions.
        //
        // An `INSTANCE M WITH p <- e` instantiates module `M`, replacing each
        // parameter `p` of `M` with the expression `e`. Faithful TLA+ semantics
        // require the substitution to be applied consistently to *every*
        // reference to `p` coming from the instantiated module. We realise this
        // by binding `p` as a free variable in the translation context: any
        // later reference to `p` (in a hypothesis, the goal, or a substituted
        // expression that itself mentions `p`) then resolves to `e` rather than
        // to an opaque `TLA.var.p` constant.
        //
        // To avoid an instance's own substitution targets being rewritten by a
        // later (or the same) instance, each `to` expression is translated in
        // the context as it stood *before* this instance's bindings were added.
        for decl in &self.declares {
            if let TlaDeclare::Instance { substitutions, .. } = decl {
                let mut translated: Vec<(String, Expr)> = Vec::with_capacity(substitutions.len());
                for (from, to) in substitutions {
                    translated.push((from.clone(), ctx.translate_expr(to)?));
                }
                for (from, to_expr) in translated {
                    ctx.bind_var(&from, to_expr);
                }
            }
        }

        // Phase 1: Collect Prop declarations
        let mut prop_vars: Vec<String> = Vec::new();
        for decl in &self.declares {
            if let TlaDeclare::Prop { name } = decl {
                prop_vars.push(name.clone());
            }
        }

        // Phase 2: Enter binder scopes for prop vars (forward order)
        // bound_vars stack: [..., P, Q] - Q is innermost among props
        for name in &prop_vars {
            ctx.enter_prop_binder(name);
        }

        // Phase 3: Translate hypothesis types (props in scope, hypotheses NOT yet)
        // These types have BVars relative to just the prop binders
        let mut hyp_types: Vec<Expr> = Vec::new();
        for hyp in &self.hypotheses {
            hyp_types.push(ctx.translate_formula(&hyp.formula)?);
        }

        // Phase 4: Enter binder scopes for hypotheses (for goal translation)
        // bound_vars stack: [..., P, Q, h1, h2, ...] - h_n is innermost
        for hyp in &self.hypotheses {
            ctx.enter_prop_binder(&hyp.name);
        }

        // Phase 5: Translate goal (props AND hypotheses in scope)
        // Goal body has BVars relative to ALL binders including hypotheses
        let mut result = ctx.translate_formula(&self.goal)?;

        // Phase 6: Exit hypothesis binder scopes
        for _ in &self.hypotheses {
            ctx.exit_prop_binder();
        }

        // Phase 7: Wrap with hypothesis Pi types (in reverse order)
        // Each hypothesis type was computed at depth len(prop_vars).
        // But in the final expression, they appear at increasing depths.
        // The i-th hypothesis (in reverse order, 0 = innermost) is at depth:
        //   len(prop_vars) + (num_hyps - 1 - i)
        // So we lift by (num_hyps - 1 - i).
        let num_hyps = hyp_types.len();
        for (i, hyp_type) in hyp_types.into_iter().rev().enumerate() {
            let lift_amount = (num_hyps - 1 - i) as u32;
            let lifted_type = hyp_type.lift(lift_amount);
            result = Expr::pi(BinderInfo::Default, lifted_type, result);
        }

        // Phase 8: Exit Prop binder scopes
        for _ in &prop_vars {
            ctx.exit_prop_binder();
        }

        // Phase 9: Wrap with declaration Pi types
        for decl in self.declares.iter().rev() {
            match decl {
                TlaDeclare::Constant { .. } => {
                    let tla_value =
                        Expr::const_(clean_kernel::name::Name::from_string("TLA.Value"), vec![]);
                    result = Expr::pi(BinderInfo::Implicit, tla_value, result);
                }
                TlaDeclare::Variable { name: _ } => {
                    let tla_value =
                        Expr::const_(clean_kernel::name::Name::from_string("TLA.Value"), vec![]);
                    result = Expr::pi(BinderInfo::Default, tla_value, result);
                }
                TlaDeclare::Assume { name: _, formula } => {
                    let assume_type = ctx.translate_formula(formula)?;
                    result = Expr::pi(BinderInfo::Default, assume_type, result);
                }
                TlaDeclare::Operator { name, params, body } => {
                    let _ = (name, params, body);
                }
                TlaDeclare::Prop { name: _ } => {
                    result = Expr::pi(BinderInfo::Default, Expr::prop(), result);
                }
                TlaDeclare::Instance { .. } => {
                    // INSTANCE introduces no binder: its effect (substituting
                    // the instantiated module's parameters) was already applied
                    // by binding the substitution targets into the context in
                    // Phase 0, so there is nothing to wrap here.
                }
            }
        }

        Ok(result)
    }

    /// Check if this obligation uses temporal operators
    pub fn is_temporal(&self) -> bool {
        self.uses_temporal_formula(&self.goal)
            || self
                .hypotheses
                .iter()
                .any(|h| self.uses_temporal_formula(&h.formula))
    }

    fn uses_temporal_formula(&self, formula: &TlaFormula) -> bool {
        match formula {
            TlaFormula::Always(_)
            | TlaFormula::Eventually(_)
            | TlaFormula::LeadsTo(_, _)
            | TlaFormula::WeakFairness(_, _)
            | TlaFormula::StrongFairness(_, _) => true,

            TlaFormula::Not(p) => self.uses_temporal_formula(p),
            TlaFormula::And(p, q)
            | TlaFormula::Or(p, q)
            | TlaFormula::Implies(p, q)
            | TlaFormula::Iff(p, q) => {
                self.uses_temporal_formula(p) || self.uses_temporal_formula(q)
            }
            TlaFormula::Forall(_, p) | TlaFormula::Exists(_, p) => self.uses_temporal_formula(p),
            TlaFormula::ForallIn(_, _, p) | TlaFormula::ExistsIn(_, _, p) => {
                self.uses_temporal_formula(p)
            }
            _ => false,
        }
    }

    /// Check if this obligation requires induction
    pub fn likely_needs_induction(&self) -> bool {
        // Heuristic: bounded quantification over Nat usually needs induction
        self.mentions_nat(&self.goal)
    }

    fn mentions_nat(&self, formula: &TlaFormula) -> bool {
        match formula {
            TlaFormula::ForallIn(_, s, p) | TlaFormula::ExistsIn(_, s, p) => {
                self.expr_is_nat(s) || self.mentions_nat(p)
            }
            TlaFormula::Not(p) => self.mentions_nat(p),
            TlaFormula::And(p, q)
            | TlaFormula::Or(p, q)
            | TlaFormula::Implies(p, q)
            | TlaFormula::Iff(p, q) => self.mentions_nat(p) || self.mentions_nat(q),
            TlaFormula::Forall(_, p) | TlaFormula::Exists(_, p) => self.mentions_nat(p),
            _ => false,
        }
    }

    fn expr_is_nat(&self, expr: &TlaExpr) -> bool {
        matches!(expr, TlaExpr::Nat | TlaExpr::Integer)
    }
}

/// Result of processing an obligation
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ObligationResult {
    /// Whether the obligation was proved
    pub proved: bool,

    /// Proof certificate (if proved)
    pub certificate: Option<String>,

    /// Time taken in milliseconds
    pub time_ms: u64,

    /// Tactics tried
    pub tactics_tried: Vec<String>,

    /// Error message (if failed)
    pub error: Option<String>,
}

impl ObligationResult {
    /// Create a successful result
    pub fn success(certificate: String, time_ms: u64, tactics: Vec<String>) -> Self {
        Self {
            proved: true,
            certificate: Some(certificate),
            time_ms,
            tactics_tried: tactics,
            error: None,
        }
    }

    /// Create a failed result
    pub fn failure(error: String, time_ms: u64, tactics: Vec<String>) -> Self {
        Self {
            proved: false,
            certificate: None,
            time_ms,
            tactics_tried: tactics,
            error: Some(error),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_obligation_builder() {
        let obligation = TlaObligation::new(TlaFormula::True)
            .in_module("TestModule")
            .at_line(42)
            .with_hypothesis("h1", TlaFormula::True)
            .with_tactic("auto");

        assert_eq!(obligation.module, "TestModule");
        assert_eq!(obligation.line, Some(42));
        assert_eq!(obligation.hypotheses.len(), 1);
        assert_eq!(obligation.tactic_hint, Some("auto".to_string()));
    }

    #[test]
    fn test_obligation_to_clean() {
        let mut ctx = TlaContext::new();

        // Simple obligation: h1 → True
        let obligation =
            TlaObligation::new(TlaFormula::True).with_hypothesis("h1", TlaFormula::True);

        let result = obligation.to_clean_goal(&mut ctx);
        let _ = result.expect("simple obligation h1 → True should convert to clean goal");
    }

    #[test]
    fn test_temporal_detection() {
        // Non-temporal
        let ob1 = TlaObligation::new(TlaFormula::And(
            Box::new(TlaFormula::True),
            Box::new(TlaFormula::False),
        ));
        assert!(!ob1.is_temporal());

        // Temporal
        let ob2 = TlaObligation::new(TlaFormula::Always(Box::new(TlaFormula::True)));
        assert!(ob2.is_temporal());
    }

    #[test]
    fn test_induction_heuristic() {
        // Likely needs induction: ∀n ∈ Nat : P(n)
        let ob = TlaObligation::new(TlaFormula::ForallIn(
            "n".to_string(),
            Box::new(TlaExpr::Nat),
            Box::new(TlaFormula::True),
        ));
        assert!(ob.likely_needs_induction());
    }

    /// Whether the clean expression tree contains a `Const` whose name equals
    /// `target` anywhere within it. Used to assert that a substitution did (or
    /// did not) rewrite a particular variable reference.
    fn contains_const_named(expr: &Expr, target: &str) -> bool {
        use clean_kernel::expr::ExprKind;
        match expr.kind() {
            ExprKind::Const(name, _) => name.to_string() == target,
            ExprKind::App(f, a) => {
                contains_const_named(f, target) || contains_const_named(a, target)
            }
            ExprKind::Pi(_, ty, body) | ExprKind::Lam(_, ty, body) => {
                contains_const_named(ty, target) || contains_const_named(body, target)
            }
            _ => false,
        }
    }

    #[test]
    fn test_to_clean_goal_instance_substitutes_param_in_goal() {
        // INSTANCE M WITH x <- e, then a goal `x = x`.
        // The substitution must replace every reference to x with e, so the
        // resulting clean term mentions `TLA.var.e` and never `TLA.var.x`.
        let mut ctx = TlaContext::new();
        let obligation = TlaObligation::new(TlaFormula::Eq(
            Box::new(TlaExpr::Var("x".to_string())),
            Box::new(TlaExpr::Var("x".to_string())),
        ))
        .with_declare(TlaDeclare::Instance {
            module: "M".to_string(),
            substitutions: vec![("x".to_string(), TlaExpr::Var("e".to_string()))],
        });

        let goal = obligation
            .to_clean_goal(&mut ctx)
            .expect("instance obligation should convert");
        assert!(
            contains_const_named(&goal, "TLA.var.e"),
            "x should be substituted by e: {goal:?}"
        );
        assert!(
            !contains_const_named(&goal, "TLA.var.x"),
            "no reference to x should survive the substitution: {goal:?}"
        );
    }

    #[test]
    fn test_to_clean_goal_instance_substitutes_param_in_hypothesis() {
        // The substitution must reach hypotheses as well as the goal.
        let mut ctx = TlaContext::new();
        let obligation = TlaObligation::new(TlaFormula::True)
            .with_declare(TlaDeclare::Instance {
                module: "M".to_string(),
                substitutions: vec![("x".to_string(), TlaExpr::Var("e".to_string()))],
            })
            .with_hypothesis(
                "h1",
                TlaFormula::Eq(
                    Box::new(TlaExpr::Var("x".to_string())),
                    Box::new(TlaExpr::Int(0)),
                ),
            );

        let goal = obligation
            .to_clean_goal(&mut ctx)
            .expect("instance obligation with hypothesis should convert");
        assert!(
            contains_const_named(&goal, "TLA.var.e"),
            "x in the hypothesis should be substituted by e: {goal:?}"
        );
        assert!(
            !contains_const_named(&goal, "TLA.var.x"),
            "no reference to x should survive in the hypothesis: {goal:?}"
        );
    }

    #[test]
    fn test_to_clean_goal_refinement_mapping_instance_substitutes_all() {
        // Impl => Spec via INSTANCE Spec WITH s <- impl_state, c <- impl_count.
        // Both refinement-mapping substitutions must be applied.
        let mut ctx = TlaContext::new();
        let obligation = TlaObligation::new(TlaFormula::And(
            Box::new(TlaFormula::Eq(
                Box::new(TlaExpr::Var("s".to_string())),
                Box::new(TlaExpr::Var("s".to_string())),
            )),
            Box::new(TlaFormula::Eq(
                Box::new(TlaExpr::Var("c".to_string())),
                Box::new(TlaExpr::Int(0)),
            )),
        ))
        .with_declare(TlaDeclare::Instance {
            module: "Spec".to_string(),
            substitutions: vec![
                ("s".to_string(), TlaExpr::Var("impl_state".to_string())),
                ("c".to_string(), TlaExpr::Var("impl_count".to_string())),
            ],
        });

        let goal = obligation
            .to_clean_goal(&mut ctx)
            .expect("refinement obligation should convert");
        assert!(
            contains_const_named(&goal, "TLA.var.impl_state"),
            "s should map to impl_state: {goal:?}"
        );
        assert!(
            contains_const_named(&goal, "TLA.var.impl_count"),
            "c should map to impl_count: {goal:?}"
        );
        assert!(
            !contains_const_named(&goal, "TLA.var.s") && !contains_const_named(&goal, "TLA.var.c"),
            "neither s nor c should survive unsubstituted: {goal:?}"
        );
    }

    #[test]
    fn test_to_clean_goal_parameterless_instance_is_noop() {
        // INSTANCE M (no substitutions) must not perturb the rest of the goal:
        // a reference to an unrelated variable y stays as TLA.var.y.
        let mut ctx = TlaContext::new();
        let obligation = TlaObligation::new(TlaFormula::Eq(
            Box::new(TlaExpr::Var("y".to_string())),
            Box::new(TlaExpr::Var("y".to_string())),
        ))
        .with_declare(TlaDeclare::Instance {
            module: "M".to_string(),
            substitutions: vec![],
        });

        let goal = obligation
            .to_clean_goal(&mut ctx)
            .expect("parameterless instance obligation should convert");
        assert!(
            contains_const_named(&goal, "TLA.var.y"),
            "parameterless instance must leave y untouched: {goal:?}"
        );
    }

    #[test]
    fn test_to_clean_goal_without_instance_leaves_var_unsubstituted() {
        // Control: the SAME goal with NO instance declaration must keep x as the
        // opaque TLA.var.x constant (substitution only happens for INSTANCE).
        let mut ctx = TlaContext::new();
        let obligation = TlaObligation::new(TlaFormula::Eq(
            Box::new(TlaExpr::Var("x".to_string())),
            Box::new(TlaExpr::Var("x".to_string())),
        ));

        let goal = obligation
            .to_clean_goal(&mut ctx)
            .expect("plain obligation should convert");
        assert!(
            contains_const_named(&goal, "TLA.var.x"),
            "without INSTANCE, x must remain unsubstituted: {goal:?}"
        );
        assert!(
            !contains_const_named(&goal, "TLA.var.e"),
            "no spurious substitution should appear: {goal:?}"
        );
    }

    #[test]
    fn test_from_tla_core_goal_and_hypothesis() {
        let eq = tla_core::Spanned::dummy(tla_core::ast::Expr::Eq(
            Box::new(tla_core::Spanned::dummy(tla_core::ast::Expr::Int(1.into()))),
            Box::new(tla_core::Spanned::dummy(tla_core::ast::Expr::Int(1.into()))),
        ));
        let obligation = TlaObligation::from_tla_core_goal(&eq)
            .expect("goal conversion should succeed")
            .with_tla_core_hypothesis("h1", &eq)
            .expect("hypothesis conversion should succeed");

        assert!(matches!(obligation.goal, TlaFormula::Eq(_, _)));
        assert_eq!(obligation.hypotheses.len(), 1);
        assert!(matches!(
            obligation.hypotheses[0].formula,
            TlaFormula::Eq(_, _)
        ));
    }
}

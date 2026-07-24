// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Goal clausification for the superposition prover: Expr → negate → NNF → CNF.

use std::collections::HashMap;

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Environment, Expr, FVarId, TypeChecker};

use super::expr_classifier::{classify_expr, LogicalForm};
use super::superposition_reconstruction::{StoredType, SymbolMap};
use super::translate::ExprKey;
use crate::superposition::{Literal, Symbol, Term};

/// Clausifies kernel `Expr` goals into CNF and records reconstruction metadata.
pub struct GoalClausifier<'a> {
    /// Bidirectional mapping for proof reconstruction
    symbol_map: SymbolMap,
    /// Kernel Expr → superposition Symbol. Uses `ExprKey` for structural equality (#2252).
    expr_to_symbol: HashMap<ExprKey, Symbol>,
    /// Next fresh symbol ID
    next_symbol: Symbol,
    /// Next fresh variable index for universal quantifiers (#2256).
    next_var: u32,
    /// Synthetic Exprs mapping to Term::Var for universal quantifiers (#2256).
    universal_vars: HashMap<ExprKey, u32>,
    /// Optional kernel environment for type inference (#2277).
    env: Option<&'a Environment>,
    /// FVarId base for goal clause hypotheses. Part of #1164.
    goal_fvar_base: u64,
}

/// Internal NNF representation for CNF conversion (And/Or/Lit only).
#[derive(Clone, Debug)]
enum NnfFormula {
    Lit(Literal),
    And(Vec<NnfFormula>),
    Or(Vec<NnfFormula>),
}

impl Default for GoalClausifier<'_> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a> GoalClausifier<'a> {
    /// Create a new clausifier without environment-backed type inference.
    /// Type queries fail closed instead of fabricating placeholder metadata.
    pub fn new() -> Self {
        GoalClausifier {
            symbol_map: SymbolMap::new(),
            expr_to_symbol: HashMap::new(),
            next_symbol: 100,
            next_var: 0,
            universal_vars: HashMap::new(),
            env: None,
            goal_fvar_base: 0,
        }
    }

    /// Create a new clausifier with environment-backed type inference.
    /// Missing metadata still fails closed when `TypeChecker::infer_type` fails.
    pub fn new_with_env(env: &'a Environment) -> Self {
        GoalClausifier {
            symbol_map: SymbolMap::new(),
            expr_to_symbol: HashMap::new(),
            next_symbol: 100,
            next_var: 0,
            universal_vars: HashMap::new(),
            env: Some(env),
            goal_fvar_base: 0,
        }
    }

    /// Set the FVarId base for goal clause hypotheses.
    /// Avoids collisions with tactic-scope FVarIds. Part of #1164.
    pub fn set_goal_fvar_base(&mut self, base: u64) {
        self.goal_fvar_base = base;
    }

    /// Clausify a goal for refutation proving.
    ///
    /// Negates the goal, converts to CNF, and returns clause literal vectors
    /// and the symbol map for proof reconstruction.
    ///
    /// # Returns
    ///
    /// `(clauses, symbol_map)` where each inner `Vec<Literal>` is one clause
    /// (disjunction of literals), and the set of clauses is their conjunction.
    pub fn clausify_goal(&mut self, goal: &Expr) -> (Vec<Vec<Literal>>, &SymbolMap) {
        // Negate the goal for refutation: to prove P, show ¬P is unsatisfiable
        let nnf = self.expr_to_nnf(goal, true);
        let clauses = Self::nnf_to_cnf(&nnf);

        // Register each goal clause as an input clause for proof reconstruction.
        // Clause IDs start at 0, matching the prover's sequential assignment
        // (goal clauses are always added to the prover first).
        // The negated goal ¬P is the proposition backing each clause.
        let neg_goal = Expr::pi(
            BinderInfo::Default,
            goal.clone(),
            Expr::const_(Name::from_string("False"), vec![]),
        );
        for i in 0..clauses.len() {
            let clause_id = i as u64;
            let fvar = FVarId::new(self.goal_fvar_base + clause_id);
            self.symbol_map
                .add_input_clause(clause_id, fvar, neg_goal.clone());
        }
        self.symbol_map.set_goal_info_with_fvar_base(
            goal.clone(),
            clauses.len(),
            self.goal_fvar_base,
        );

        (clauses, &self.symbol_map)
    }

    /// Clausify a hypothesis (added as-is, not negated).
    #[cfg(test)]
    pub fn clausify_hypothesis(
        &mut self,
        hyp: &Expr,
        clause_id: u64,
        fvar: FVarId,
    ) -> Vec<Vec<Literal>> {
        // Register the hypothesis in the symbol map for proof reconstruction
        self.symbol_map
            .add_input_clause(clause_id, fvar, hyp.clone());
        let nnf = self.expr_to_nnf(hyp, false);
        Self::nnf_to_cnf(&nnf)
    }

    /// Clausify a hypothesis with sequential clause IDs for prover compatibility.
    ///
    /// Unlike `clausify_hypothesis`, this method registers each produced CNF
    /// clause with its own sequential ID starting at `starting_clause_id`.
    /// This ensures SymbolMap clause IDs match the prover's sequential ID
    /// assignment. Returns the number of clauses produced.
    ///
    /// Each clause is registered with the same `fvar` (all clauses originate
    /// from the same hypothesis).
    pub fn clausify_hypothesis_sequential(
        &mut self,
        hyp: &Expr,
        starting_clause_id: u64,
        fvar: FVarId,
    ) -> Vec<Vec<Literal>> {
        let nnf = self.expr_to_nnf(hyp, false);
        let clauses = Self::nnf_to_cnf(&nnf);
        for i in 0..clauses.len() {
            self.symbol_map
                .add_input_clause(starting_clause_id + i as u64, fvar, hyp.clone());
        }
        clauses
    }

    /// Consume the clausifier and return the symbol map.
    pub fn into_symbol_map(self) -> SymbolMap {
        self.symbol_map
    }

    /// Convert an expression to NNF, optionally negated.
    ///
    /// Uses `classify_expr` to dispatch on logical form, then pushes negation
    /// inward via De Morgan's laws. Handles MData transparently (via classifier),
    /// Iff (bidirectional implication), and Exists Skolemization.
    fn expr_to_nnf(&mut self, expr: &Expr, negated: bool) -> NnfFormula {
        crate::bridge::stack_safe(|| match classify_expr(expr) {
            LogicalForm::Eq { lhs, rhs, .. } => self.nnf_equation(&lhs, &rhs, !negated),
            LogicalForm::Neq { lhs, rhs, .. } => self.nnf_equation(&lhs, &rhs, negated),
            LogicalForm::Lt { .. }
            | LogicalForm::Le { .. }
            | LogicalForm::Gt { .. }
            | LogicalForm::Ge { .. }
            | LogicalForm::Add { .. }
            | LogicalForm::Sub { .. }
            | LogicalForm::Mul { .. }
            | LogicalForm::Div { .. }
            | LogicalForm::Mod { .. }
            | LogicalForm::Neg { .. } => {
                // Comparison and arithmetic operators are atomic from the clausifier's
                // perspective. The superposition calculus treats them as uninterpreted
                // predicates/terms; theory-specific semantics are handled by the SMT backend.
                self.atomic_to_nnf(expr, negated)
            }
            LogicalForm::And(a, b) => {
                let (l, r) = (self.expr_to_nnf(&a, negated), self.expr_to_nnf(&b, negated));
                if negated {
                    NnfFormula::Or(vec![l, r])
                } else {
                    NnfFormula::And(vec![l, r])
                }
            }
            LogicalForm::Or(a, b) => {
                let (l, r) = (self.expr_to_nnf(&a, negated), self.expr_to_nnf(&b, negated));
                if negated {
                    NnfFormula::And(vec![l, r])
                } else {
                    NnfFormula::Or(vec![l, r])
                }
            }
            LogicalForm::Not(a) => self.expr_to_nnf(&a, !negated),
            LogicalForm::Implies(domain, codomain) => {
                if negated {
                    // ¬(P → Q) = P ∧ ¬Q
                    let (l, r) = (
                        self.expr_to_nnf(&domain, false),
                        self.expr_to_nnf(&codomain, true),
                    );
                    NnfFormula::And(vec![l, r])
                } else {
                    // P → Q = ¬P ∨ Q
                    let (l, r) = (
                        self.expr_to_nnf(&domain, true),
                        self.expr_to_nnf(&codomain, false),
                    );
                    NnfFormula::Or(vec![l, r])
                }
            }
            LogicalForm::Iff(a, b) => self.nnf_iff(&a, &b, negated),
            LogicalForm::True if negated => NnfFormula::Or(vec![]),
            LogicalForm::True => NnfFormula::And(vec![]),
            LogicalForm::False if negated => NnfFormula::And(vec![]),
            LogicalForm::False => NnfFormula::Or(vec![]),
            LogicalForm::Forall { binder_type, body } => {
                if negated {
                    // ¬(∀x.P(x)) = ∃x.¬P(x) → Skolemize (existential)
                    self.nnf_skolemize(&body, &binder_type, negated)
                } else {
                    // ∀x.P(x) as hypothesis → universal variable (#2256)
                    self.nnf_universalize(&body, &binder_type, negated)
                }
            }
            LogicalForm::Exists { binder_type, body } => {
                if negated {
                    // ¬(∃x.P(x)) = ∀x.¬P(x) → universal variable (#2256)
                    self.nnf_universalize(&body, &binder_type, negated)
                } else {
                    // ∃x.P(x) → Skolemize (existential)
                    self.nnf_skolemize(&body, &binder_type, negated)
                }
            }
            LogicalForm::Atom(inner) => self.atomic_to_nnf(&inner, negated),
        })
    }

    /// Convert an equation to an NNF literal.
    fn nnf_equation(&mut self, lhs: &Expr, rhs: &Expr, positive: bool) -> NnfFormula {
        NnfFormula::Lit(Literal {
            lhs: self.expr_to_term(lhs),
            rhs: self.expr_to_term(rhs),
            positive,
        })
    }

    /// Convert `P ↔ Q` to NNF.
    fn nnf_iff(&mut self, a: &Expr, b: &Expr, negated: bool) -> NnfFormula {
        if negated {
            // ¬(P ↔ Q) = (P ∧ ¬Q) ∨ (¬P ∧ Q)
            let p_and_nq =
                NnfFormula::And(vec![self.expr_to_nnf(a, false), self.expr_to_nnf(b, true)]);
            let np_and_q =
                NnfFormula::And(vec![self.expr_to_nnf(a, true), self.expr_to_nnf(b, false)]);
            NnfFormula::Or(vec![p_and_nq, np_and_q])
        } else {
            // P ↔ Q = (¬P ∨ Q) ∧ (¬Q ∨ P)
            let fwd = NnfFormula::Or(vec![self.expr_to_nnf(a, true), self.expr_to_nnf(b, false)]);
            let bwd = NnfFormula::Or(vec![self.expr_to_nnf(b, true), self.expr_to_nnf(a, false)]);
            NnfFormula::And(vec![fwd, bwd])
        }
    }

    /// Skolemize a quantifier: introduce a fresh constant, substitute, recurse.
    ///
    /// Registers the Skolem constant in both `symbol_map.add_symbol` (for term
    /// conversion) and `symbol_map.register_skolem` (for kernel Environment
    /// declaration before type-checking reconstructed proofs).
    fn nnf_skolemize(&mut self, body: &Expr, binder_type: &Expr, negated: bool) -> NnfFormula {
        let fresh_sym = self.alloc_symbol();
        let skolem_name = Name::from_string(&format!("sk_{fresh_sym}"));
        let fresh_term = Expr::const_(skolem_name.clone(), vec![]);
        let instantiated = body.instantiate(&fresh_term);
        self.symbol_map
            .add_symbol(fresh_sym, fresh_term, binder_type.clone());
        self.symbol_map
            .register_skolem(skolem_name, binder_type.clone());
        self.expr_to_nnf(&instantiated, negated)
    }

    /// Universalize a quantifier: fresh `Term::Var` instead of Skolem constant (#2256).
    /// Creates synthetic `Expr::const_("uv_N")` tracked in `universal_vars`.
    fn nnf_universalize(&mut self, body: &Expr, binder_type: &Expr, negated: bool) -> NnfFormula {
        let var_id = self.next_var;
        self.next_var += 1;
        let var_name = Name::from_string(&format!("uv_{var_id}"));
        let var_expr = Expr::const_(var_name, vec![]);
        if let Some(key) = ExprKey::from_expr(&var_expr) {
            self.universal_vars.insert(key, var_id);
        }
        let instantiated = body.instantiate(&var_expr);
        // Register variable mapping for proof reconstruction (#2256).
        // Must use add_variable (not add_symbol) so term_to_expr can
        // resolve Term::Var(var_id) back to the kernel expression.
        self.symbol_map
            .add_variable(var_id, var_expr, binder_type.clone());
        self.expr_to_nnf(&instantiated, negated)
    }

    /// Convert an atomic (non-decomposable) proposition to NNF.
    ///
    /// Atomic propositions are encoded as `P = True` (standard equational encoding).
    fn atomic_to_nnf(&mut self, expr: &Expr, negated: bool) -> NnfFormula {
        let term = self.expr_to_term(expr);
        let true_sym = self.get_or_alloc_true_symbol();
        let true_term = Term::Const(true_sym);
        NnfFormula::Lit(Literal {
            lhs: term,
            rhs: true_term,
            positive: !negated,
        })
    }

    /// Get or allocate the symbol for the `True` constant.
    fn get_or_alloc_true_symbol(&mut self) -> Symbol {
        let true_key = ExprKey::Const(Name::from_string("True"), vec![]);
        if let Some(&sym) = self.expr_to_symbol.get(&true_key) {
            return sym;
        }
        let sym = self.alloc_symbol();
        self.expr_to_symbol.insert(true_key, sym);
        let true_expr = Expr::const_(Name::from_string("True"), vec![]);
        let prop_expr = Expr::prop();
        self.symbol_map.add_symbol(sym, true_expr, prop_expr);
        sym
    }

    /// Convert a kernel `Expr` to a superposition `Term`.
    ///
    /// Constants and free variables become `Term::Const`, function applications
    /// become `Term::App`. Registers each new symbol in the `SymbolMap`.
    ///
    /// Strips MData wrappers before decomposing, since `get_app_fn` does not
    /// traverse MData nodes. Without stripping, MData-wrapped expressions
    /// (common in .olean files with `@[simp]` annotations) become opaque atoms.
    pub(crate) fn expr_to_term(&mut self, expr: &Expr) -> Term {
        crate::bridge::stack_safe(|| {
            let expr = expr.strip_mdata();
            let head = expr.get_app_fn();
            let args = expr.get_app_args();

            if args.is_empty() {
                // Check if this expression is a universal variable placeholder (#2256).
                // Universal variables are synthetic constants (uv_N) registered in
                // nnf_universalize; they must become Term::Var for the prover to
                // instantiate them via unification.
                if let Some(key) = ExprKey::from_expr(head) {
                    if let Some(&var_id) = self.universal_vars.get(&key) {
                        return Term::Var(var_id);
                    }
                }
                let sym = self.get_or_alloc_expr_symbol(head);
                Term::Const(sym)
            } else {
                let func_sym = self.get_or_alloc_expr_symbol(head);
                let arg_terms: Vec<Term> = args.iter().map(|a| self.expr_to_term(a)).collect();
                Term::App(func_sym, arg_terms)
            }
        })
    }

    /// Get or allocate a symbol for a kernel expression (head position).
    ///
    /// Strips MData wrappers so that metadata-annotated heads (e.g., from
    /// `@[simp]` attributes) are correctly identified and deduplicated.
    ///
    /// Uses `ExprKey` for structural deduplication when available. For expressions
    /// where `ExprKey::from_expr` returns `None` (Sort, Let, Proj), allocates a
    /// fresh symbol unconditionally — accepting incompleteness over unsoundness (#2252).
    ///
    /// When `self.env` is set, infers the actual type of the expression via
    /// `TypeChecker::infer_type`. Records missing types explicitly instead of
    /// substituting fake `Type` (Part of #2345).
    fn get_or_alloc_expr_symbol(&mut self, expr: &Expr) -> Symbol {
        let expr = expr.strip_mdata();
        if let Some(key) = ExprKey::from_expr(expr) {
            if let Some(&sym) = self.expr_to_symbol.get(&key) {
                return sym;
            }
            let sym = self.alloc_symbol();
            self.expr_to_symbol.insert(key, sym);
            let ty = self.infer_symbol_type(expr);
            self.symbol_map.add_symbol(sym, expr.clone(), ty);
            sym
        } else {
            let sym = self.alloc_symbol();
            let ty = self.infer_symbol_type(expr);
            self.symbol_map.add_symbol(sym, expr.clone(), ty);
            sym
        }
    }

    /// Infer the type of an expression using the kernel environment.
    ///
    /// Returns `StoredType::Known` when the environment is available and type
    /// inference succeeds. Returns `StoredType::Missing` with a reason string
    /// otherwise — never substitutes a fake `Expr::type_()`. Part of #2345.
    fn infer_symbol_type(&self, expr: &Expr) -> StoredType {
        if let Some(env) = self.env {
            let tc = TypeChecker::new(env);
            if let Ok(ty) = tc.infer_type(expr) {
                return StoredType::Known(ty);
            }
            return StoredType::Missing(
                "infer_type failed for expression (env available but inference failed)".into(),
            );
        }
        StoredType::Missing("no environment available for type inference".into())
    }

    /// Allocate a fresh symbol ID.
    fn alloc_symbol(&mut self) -> Symbol {
        let sym = self.next_symbol;
        self.next_symbol += 1;
        sym
    }

    /// Budget: naive distributive CNF is O(2ⁿ). Truncation is sound (weakens conjunction).
    const MAX_CNF_CLAUSES: usize = 10_000;

    /// Convert NNF formula to CNF. Clause count bounded by `MAX_CNF_CLAUSES`.
    ///
    /// Protected by `stacker::maybe_grow` since NNF tree depth mirrors input
    /// Expr depth, which is unbounded for deeply nested Mathlib propositions.
    fn nnf_to_cnf(formula: &NnfFormula) -> Vec<Vec<Literal>> {
        crate::bridge::stack_safe(|| match formula {
            NnfFormula::Lit(lit) => vec![vec![lit.clone()]],
            NnfFormula::And(conjuncts) => {
                let mut clauses = Vec::new();
                for conjunct in conjuncts {
                    clauses.extend(Self::nnf_to_cnf(conjunct));
                    if clauses.len() >= Self::MAX_CNF_CLAUSES {
                        clauses.truncate(Self::MAX_CNF_CLAUSES);
                        break;
                    }
                }
                clauses
            }
            NnfFormula::Or(disjuncts) => {
                if disjuncts.is_empty() {
                    // Empty disjunction = False → one empty clause (unsatisfiable)
                    return vec![vec![]];
                }
                let mut result = Self::nnf_to_cnf(&disjuncts[0]);
                for disjunct in &disjuncts[1..] {
                    let other_clauses = Self::nnf_to_cnf(disjunct);
                    result = Self::distribute_or(&result, &other_clauses);
                }
                result
            }
        })
    }

    /// Distribute disjunction over two CNF clause sets. Bounded by `MAX_CNF_CLAUSES`.
    fn distribute_or(left: &[Vec<Literal>], right: &[Vec<Literal>]) -> Vec<Vec<Literal>> {
        let mut result = Vec::new();
        for l_clause in left {
            for r_clause in right {
                let mut combined = l_clause.clone();
                combined.extend(r_clause.iter().cloned());
                result.push(combined);
                if result.len() >= Self::MAX_CNF_CLAUSES {
                    return result;
                }
            }
        }
        result
    }
}

#[cfg(test)]
mod tests;

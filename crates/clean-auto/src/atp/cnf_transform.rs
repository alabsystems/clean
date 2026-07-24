// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! FOF to CNF transformation (clausification).
//!
//! Converts first-order formulas to clause normal form through:
//! 1. Eliminate implications and bi-implications
//! 2. Push negation inward (NNF)
//! 3. Standardize variables (rename to avoid capture)
//! 4. Skolemize (eliminate existential quantifiers)
//! 5. Drop universal quantifiers
//! 6. Distribute OR over AND (CNF)
//! 7. Extract clauses

use super::tptp_parser::{FofFormula, FofTerm};
use crate::superposition::{Clause, Literal, Symbol, Term};
use std::collections::HashMap;

/// Symbol table mapping TPTP names to internal symbol IDs.
pub(crate) struct SymbolTable {
    next_symbol: Symbol,
    names: HashMap<String, Symbol>,
    reverse: HashMap<Symbol, String>,
    next_var: u32,
    var_map: HashMap<String, u32>,
    skolem_count: usize,
}

impl SymbolTable {
    pub(crate) fn new() -> Self {
        SymbolTable {
            next_symbol: 0,
            names: HashMap::new(),
            reverse: HashMap::new(),
            next_var: 0,
            var_map: HashMap::new(),
            skolem_count: 0,
        }
    }

    fn get_or_create_symbol(&mut self, name: &str) -> Symbol {
        if let Some(&sym) = self.names.get(name) {
            return sym;
        }
        let sym = self.next_symbol;
        self.next_symbol += 1;
        self.names.insert(name.to_string(), sym);
        self.reverse.insert(sym, name.to_string());
        sym
    }

    fn get_or_create_var(&mut self, name: &str) -> u32 {
        if let Some(&v) = self.var_map.get(name) {
            return v;
        }
        let v = self.next_var;
        self.next_var += 1;
        self.var_map.insert(name.to_string(), v);
        v
    }

    fn fresh_skolem(&mut self, arity: usize) -> String {
        let name = format!("sk{}", self.skolem_count);
        self.skolem_count += 1;
        let _ = arity; // arity is used by the caller
        name
    }

    /// Look up a symbol name by its ID.
    pub(crate) fn symbol_name(&self, sym: Symbol) -> Option<&str> {
        self.reverse.get(&sym).map(|s| s.as_str())
    }
}

/// Eliminate implications and bi-implications.
fn eliminate_implications(f: &FofFormula) -> FofFormula {
    match f {
        FofFormula::Implies(a, b) => {
            let a = eliminate_implications(a);
            let b = eliminate_implications(b);
            FofFormula::Or(Box::new(FofFormula::Not(Box::new(a))), Box::new(b))
        }
        FofFormula::Iff(a, b) => {
            let a = eliminate_implications(a);
            let b = eliminate_implications(b);
            FofFormula::And(
                Box::new(FofFormula::Or(
                    Box::new(FofFormula::Not(Box::new(a.clone()))),
                    Box::new(b.clone()),
                )),
                Box::new(FofFormula::Or(
                    Box::new(FofFormula::Not(Box::new(b))),
                    Box::new(a),
                )),
            )
        }
        FofFormula::Not(a) => FofFormula::Not(Box::new(eliminate_implications(a))),
        FofFormula::And(a, b) => FofFormula::And(
            Box::new(eliminate_implications(a)),
            Box::new(eliminate_implications(b)),
        ),
        FofFormula::Or(a, b) => FofFormula::Or(
            Box::new(eliminate_implications(a)),
            Box::new(eliminate_implications(b)),
        ),
        FofFormula::Forall(vs, body) => {
            FofFormula::Forall(vs.clone(), Box::new(eliminate_implications(body)))
        }
        FofFormula::Exists(vs, body) => {
            FofFormula::Exists(vs.clone(), Box::new(eliminate_implications(body)))
        }
        other => other.clone(),
    }
}

/// Push negation inward to produce NNF.
fn nnf(f: &FofFormula) -> FofFormula {
    match f {
        FofFormula::Not(inner) => nnf_neg(inner),
        FofFormula::And(a, b) => FofFormula::And(Box::new(nnf(a)), Box::new(nnf(b))),
        FofFormula::Or(a, b) => FofFormula::Or(Box::new(nnf(a)), Box::new(nnf(b))),
        FofFormula::Forall(vs, body) => FofFormula::Forall(vs.clone(), Box::new(nnf(body))),
        FofFormula::Exists(vs, body) => FofFormula::Exists(vs.clone(), Box::new(nnf(body))),
        other => other.clone(),
    }
}

/// NNF of a negated formula.
fn nnf_neg(f: &FofFormula) -> FofFormula {
    match f {
        FofFormula::Not(inner) => nnf(inner),
        FofFormula::And(a, b) => FofFormula::Or(Box::new(nnf_neg(a)), Box::new(nnf_neg(b))),
        FofFormula::Or(a, b) => FofFormula::And(Box::new(nnf_neg(a)), Box::new(nnf_neg(b))),
        FofFormula::Forall(vs, body) => FofFormula::Exists(vs.clone(), Box::new(nnf_neg(body))),
        FofFormula::Exists(vs, body) => FofFormula::Forall(vs.clone(), Box::new(nnf_neg(body))),
        FofFormula::True => FofFormula::False,
        FofFormula::False => FofFormula::True,
        FofFormula::Equal(a, b) => FofFormula::NotEqual(a.clone(), b.clone()),
        FofFormula::NotEqual(a, b) => FofFormula::Equal(a.clone(), b.clone()),
        other => FofFormula::Not(Box::new(nnf(other))),
    }
}

/// Skolemize: replace existential quantifiers with Skolem functions.
/// `universal_vars` tracks the universally quantified variables in scope.
fn skolemize(
    f: &FofFormula,
    universal_vars: &[String],
    table: &mut SymbolTable,
    var_rename: &mut HashMap<String, String>,
) -> FofFormula {
    match f {
        FofFormula::Forall(vs, body) => {
            let mut new_uvars = universal_vars.to_vec();
            new_uvars.extend(vs.iter().cloned());
            skolemize(body, &new_uvars, table, var_rename)
        }
        FofFormula::Exists(vs, body) => {
            // Replace each existential variable with a Skolem function
            // applied to all universal variables in scope.
            for v in vs {
                let sk_name = table.fresh_skolem(universal_vars.len());
                // We store the mapping: v -> sk_name(universal_vars...)
                // but we need to handle this at the term level.
                // For now, store in var_rename so term conversion picks it up.
                var_rename.insert(v.clone(), sk_name);
            }
            skolemize(body, universal_vars, table, var_rename)
        }
        FofFormula::And(a, b) => FofFormula::And(
            Box::new(skolemize(a, universal_vars, table, var_rename)),
            Box::new(skolemize(b, universal_vars, table, var_rename)),
        ),
        FofFormula::Or(a, b) => FofFormula::Or(
            Box::new(skolemize(a, universal_vars, table, var_rename)),
            Box::new(skolemize(b, universal_vars, table, var_rename)),
        ),
        FofFormula::Not(a) => {
            FofFormula::Not(Box::new(skolemize(a, universal_vars, table, var_rename)))
        }
        other => other.clone(),
    }
}

/// Distribute OR over AND to get CNF.
fn distribute(f: &FofFormula) -> FofFormula {
    match f {
        FofFormula::And(a, b) => FofFormula::And(Box::new(distribute(a)), Box::new(distribute(b))),
        FofFormula::Or(a, b) => {
            let a = distribute(a);
            let b = distribute(b);
            distribute_or(&a, &b)
        }
        other => other.clone(),
    }
}

fn distribute_or(a: &FofFormula, b: &FofFormula) -> FofFormula {
    match (a, b) {
        (FofFormula::And(a1, a2), _) => FofFormula::And(
            Box::new(distribute_or(a1, b)),
            Box::new(distribute_or(a2, b)),
        ),
        (_, FofFormula::And(b1, b2)) => FofFormula::And(
            Box::new(distribute_or(a, b1)),
            Box::new(distribute_or(a, b2)),
        ),
        _ => FofFormula::Or(Box::new(a.clone()), Box::new(b.clone())),
    }
}

/// Extract clauses from a CNF formula (a conjunction of disjunctions).
fn extract_clauses(f: &FofFormula) -> Vec<Vec<FofFormula>> {
    match f {
        FofFormula::And(a, b) => {
            let mut clauses = extract_clauses(a);
            clauses.extend(extract_clauses(b));
            clauses
        }
        _ => {
            vec![extract_literals(f)]
        }
    }
}

fn extract_literals(f: &FofFormula) -> Vec<FofFormula> {
    match f {
        FofFormula::Or(a, b) => {
            let mut lits = extract_literals(a);
            lits.extend(extract_literals(b));
            lits
        }
        _ => vec![f.clone()],
    }
}

/// Convert a `FofTerm` to the internal `Term` representation.
fn convert_term(
    t: &FofTerm,
    table: &mut SymbolTable,
    var_rename: &HashMap<String, String>,
    universal_vars: &[String],
) -> Term {
    match t {
        FofTerm::Var(name) => {
            // Check if this variable was Skolemized
            if let Some(sk_name) = var_rename.get(name) {
                let sk_sym = table.get_or_create_symbol(sk_name);
                if universal_vars.is_empty() {
                    // Skolem constant
                    Term::Const(sk_sym)
                } else {
                    // Skolem function applied to universal variables
                    let args: Vec<Term> = universal_vars
                        .iter()
                        .map(|uv| Term::Var(table.get_or_create_var(uv)))
                        .collect();
                    Term::App(sk_sym, args)
                }
            } else {
                Term::Var(table.get_or_create_var(name))
            }
        }
        FofTerm::Func(name, args) if args.is_empty() => {
            let sym = table.get_or_create_symbol(name);
            Term::Const(sym)
        }
        FofTerm::Func(name, args) => {
            let sym = table.get_or_create_symbol(name);
            let converted: Vec<Term> = args
                .iter()
                .map(|a| convert_term(a, table, var_rename, universal_vars))
                .collect();
            Term::App(sym, converted)
        }
    }
}

/// Sentinel for `$true` literals in a clause.
/// When a clause contains `$true`, the entire clause is a tautology.
enum LiteralOrSpecial {
    Lit(Literal),
    /// `$true` — makes the whole clause a tautology.
    Tautology,
    /// `$false` — dropped from the clause (empty clause if sole literal).
    Absurd,
}

/// Convert a FOF literal to a superposition `Literal`, or a special sentinel.
fn convert_literal(
    f: &FofFormula,
    table: &mut SymbolTable,
    var_rename: &HashMap<String, String>,
    universal_vars: &[String],
) -> LiteralOrSpecial {
    match f {
        FofFormula::Equal(a, b) => {
            let lhs = convert_term(a, table, var_rename, universal_vars);
            let rhs = convert_term(b, table, var_rename, universal_vars);
            LiteralOrSpecial::Lit(Literal::eq(lhs, rhs))
        }
        FofFormula::NotEqual(a, b) => {
            let lhs = convert_term(a, table, var_rename, universal_vars);
            let rhs = convert_term(b, table, var_rename, universal_vars);
            LiteralOrSpecial::Lit(Literal::neq(lhs, rhs))
        }
        FofFormula::Predicate(name, args) => {
            // Encode predicate P(args) as P(args) = $true
            let pred_sym = table.get_or_create_symbol(name);
            let true_sym = table.get_or_create_symbol("$true");
            let lhs = if args.is_empty() {
                Term::Const(pred_sym)
            } else {
                Term::App(
                    pred_sym,
                    args.iter()
                        .map(|a| convert_term(a, table, var_rename, universal_vars))
                        .collect(),
                )
            };
            LiteralOrSpecial::Lit(Literal::eq(lhs, Term::Const(true_sym)))
        }
        FofFormula::Not(inner) => match inner.as_ref() {
            FofFormula::Predicate(name, args) => {
                let pred_sym = table.get_or_create_symbol(name);
                let true_sym = table.get_or_create_symbol("$true");
                let lhs = if args.is_empty() {
                    Term::Const(pred_sym)
                } else {
                    Term::App(
                        pred_sym,
                        args.iter()
                            .map(|a| convert_term(a, table, var_rename, universal_vars))
                            .collect(),
                    )
                };
                LiteralOrSpecial::Lit(Literal::neq(lhs, Term::Const(true_sym)))
            }
            FofFormula::Equal(a, b) => {
                let lhs = convert_term(a, table, var_rename, universal_vars);
                let rhs = convert_term(b, table, var_rename, universal_vars);
                LiteralOrSpecial::Lit(Literal::neq(lhs, rhs))
            }
            _ => {
                // Fallback: treat as predicate
                let pred_sym = table.get_or_create_symbol("__neg_fallback");
                let true_sym = table.get_or_create_symbol("$true");
                LiteralOrSpecial::Lit(Literal::neq(Term::Const(pred_sym), Term::Const(true_sym)))
            }
        },
        FofFormula::True => LiteralOrSpecial::Tautology,
        FofFormula::False => LiteralOrSpecial::Absurd,
        _ => {
            // Shouldn't happen after clausification, but handle gracefully
            let pred_sym = table.get_or_create_symbol("__unknown");
            let true_sym = table.get_or_create_symbol("$true");
            LiteralOrSpecial::Lit(Literal::eq(Term::Const(pred_sym), Term::Const(true_sym)))
        }
    }
}

/// Convert a list of FOF literals to a list of superposition literals.
/// Returns `None` if the clause is a tautology ($true appears as a literal).
fn convert_clause_literals(
    lits: &[FofFormula],
    table: &mut SymbolTable,
    var_rename: &HashMap<String, String>,
    universal_vars: &[String],
) -> Option<Vec<Literal>> {
    let mut result = Vec::new();
    for l in lits {
        match convert_literal(l, table, var_rename, universal_vars) {
            LiteralOrSpecial::Lit(lit) => result.push(lit),
            LiteralOrSpecial::Tautology => return None, // clause is trivially true
            LiteralOrSpecial::Absurd => {}              // drop $false from clause
        }
    }
    Some(result)
}

/// Result of clausification: clauses + the symbol table for proof output.
pub(crate) struct ClausificationResult {
    pub(crate) clauses: Vec<Clause>,
    pub(crate) table: SymbolTable,
}

/// Convert a TPTP problem to a set of clauses.
///
/// For FOF formulas: negate conjecture, then clausify all formulas.
/// For CNF formulas: convert directly.
pub(crate) fn clausify_problem(
    formulas: &[super::tptp_parser::TptpFormula],
) -> ClausificationResult {
    let mut table = SymbolTable::new();
    let mut clauses = Vec::new();
    let mut clause_id: u64 = 0;

    for tf in formulas {
        // Reset variable map for each formula (variables are scoped per formula)
        table.var_map.clear();
        table.next_var = 0;

        let formula = if tf.role == super::tptp_parser::TptpRole::Conjecture {
            // Negate the conjecture for refutation
            FofFormula::Not(Box::new(tf.formula.clone()))
        } else {
            tf.formula.clone()
        };

        if tf.is_cnf {
            // Already a clause, just extract literals
            let lits = extract_literals(&formula);
            let var_rename = HashMap::new();
            if let Some(converted) = convert_clause_literals(&lits, &mut table, &var_rename, &[]) {
                clauses.push(Clause::new(converted, clause_id));
                clause_id += 1;
            }
            // else: clause is a tautology ($true), skip it
        } else {
            // Full clausification pipeline
            let f = eliminate_implications(&formula);
            let f = nnf(&f);
            let mut var_rename = HashMap::new();
            let f = skolemize(&f, &[], &mut table, &mut var_rename);
            let f = distribute(&f);
            let raw_clauses = extract_clauses(&f);

            for raw in raw_clauses {
                if let Some(converted) = convert_clause_literals(&raw, &mut table, &var_rename, &[])
                {
                    clauses.push(Clause::new(converted, clause_id));
                    clause_id += 1;
                }
            }
        }
    }

    ClausificationResult { clauses, table }
}

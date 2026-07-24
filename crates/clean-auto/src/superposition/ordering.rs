// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Term orderings (KBO, LPO) and clause selection strategies.

use super::{Symbol, Term};
use std::cmp::Ordering;
use std::collections::HashMap;
use std::sync::Mutex;

/// Term ordering trait
pub trait TermOrdering: Send + Sync {
    /// Compare two terms
    fn compare(&self, t1: &Term, t2: &Term) -> Option<Ordering>;

    /// Check if t1 > t2
    fn greater(&self, t1: &Term, t2: &Term) -> bool {
        matches!(self.compare(t1, t2), Some(Ordering::Greater))
    }

    /// Check if t1 >= t2
    fn greater_equal(&self, t1: &Term, t2: &Term) -> bool {
        matches!(
            self.compare(t1, t2),
            Some(Ordering::Greater | Ordering::Equal)
        )
    }
}

/// Knuth-Bendix Ordering
pub struct KBO {
    /// Weight of each function symbol
    weights: HashMap<Symbol, u32>,
    /// Precedence of function symbols (higher = greater)
    precedence: HashMap<Symbol, u32>,
    /// Default weight for unknown symbols
    default_weight: u32,
    /// Weight of variables
    var_weight: u32,
    /// Scratch buffer for variable counts, reused across compare() calls (#1820).
    /// Mutex is uncontended (single-threaded prover) but needed for Sync trait bound.
    var_count_scratch: Mutex<HashMap<u32, i32>>,
}

impl Default for KBO {
    fn default() -> Self {
        Self::new()
    }
}

impl KBO {
    /// Create a new KBO with default settings
    pub fn new() -> Self {
        KBO {
            weights: HashMap::new(),
            precedence: HashMap::new(),
            default_weight: 1,
            var_weight: 1,
            var_count_scratch: Mutex::new(HashMap::new()),
        }
    }

    /// Set the weight of a symbol
    pub fn set_weight(&mut self, sym: Symbol, weight: u32) {
        self.weights.insert(sym, weight);
    }

    /// Set the precedence of a symbol
    pub fn set_precedence(&mut self, sym: Symbol, prec: u32) {
        self.precedence.insert(sym, prec);
    }

    fn weight(&self, term: &Term) -> u32 {
        match term {
            Term::Var(_) => self.var_weight,
            Term::Const(c) => *self.weights.get(c).unwrap_or(&self.default_weight),
            Term::App(f, args) => {
                let f_weight = *self.weights.get(f).unwrap_or(&self.default_weight);
                f_weight + args.iter().map(|a| self.weight(a)).sum::<u32>()
            }
        }
    }

    fn prec(&self, sym: Symbol) -> u32 {
        *self.precedence.get(&sym).unwrap_or(&sym)
    }

    fn collect_var_counts(term: &Term, counts: &mut HashMap<u32, i32>, sign: i32) {
        match term {
            Term::Var(v) => {
                *counts.entry(*v).or_insert(0) += sign;
            }
            Term::Const(_) => {}
            Term::App(_, args) => {
                for arg in args {
                    Self::collect_var_counts(arg, counts, sign);
                }
            }
        }
    }
}

impl TermOrdering for KBO {
    fn compare(&self, t1: &Term, t2: &Term) -> Option<Ordering> {
        if t1 == t2 {
            return Some(Ordering::Equal);
        }

        let w1 = self.weight(t1);
        let w2 = self.weight(t2);

        // Reuse scratch buffer for variable counts — avoids HashMap allocation per compare().
        // Lock is dropped before recursive compare calls in lexicographic comparison.
        let mut counts = self
            .var_count_scratch
            .lock()
            .expect("invariant: lock not poisoned");
        counts.clear();
        Self::collect_var_counts(t1, &mut counts, 1);
        Self::collect_var_counts(t2, &mut counts, -1);

        let all_non_negative = counts.values().all(|&c| c >= 0);
        let all_non_positive = counts.values().all(|&c| c <= 0);
        drop(counts);

        if w1 > w2 && all_non_negative {
            return Some(Ordering::Greater);
        }
        if w1 < w2 && all_non_positive {
            return Some(Ordering::Less);
        }

        // If weights are equal, compare by precedence
        if w1 == w2 {
            match (t1, t2) {
                (Term::App(f1, args1), Term::App(f2, args2)) => {
                    let p1 = self.prec(*f1);
                    let p2 = self.prec(*f2);
                    if p1 > p2 && all_non_negative {
                        return Some(Ordering::Greater);
                    }
                    if p1 < p2 && all_non_positive {
                        return Some(Ordering::Less);
                    }
                    if p1 == p2 && f1 == f2 {
                        // Lexicographic comparison of arguments
                        for (a1, a2) in args1.iter().zip(args2.iter()) {
                            match self.compare(a1, a2) {
                                Some(Ordering::Equal) => {}
                                Some(Ordering::Greater) if all_non_negative => {
                                    return Some(Ordering::Greater);
                                }
                                Some(Ordering::Less) if all_non_positive => {
                                    return Some(Ordering::Less);
                                }
                                _ => return None,
                            }
                        }
                    }
                }
                (Term::Const(c1), Term::Const(c2)) => {
                    let p1 = self.prec(*c1);
                    let p2 = self.prec(*c2);
                    if p1 > p2 {
                        return Some(Ordering::Greater);
                    }
                    if p1 < p2 {
                        return Some(Ordering::Less);
                    }
                }
                _ => {}
            }
        }

        None
    }
}

/// Lexicographic Path Ordering
pub struct LPO {
    /// Precedence of function symbols (higher = greater)
    precedence: HashMap<Symbol, u32>,
}

impl Default for LPO {
    fn default() -> Self {
        Self::new()
    }
}

impl LPO {
    /// Create a new LPO with default precedence
    pub fn new() -> Self {
        LPO {
            precedence: HashMap::new(),
        }
    }

    /// Set the precedence of a symbol
    pub fn set_precedence(&mut self, sym: Symbol, prec: u32) {
        self.precedence.insert(sym, prec);
    }

    fn prec(&self, sym: Symbol) -> u32 {
        *self.precedence.get(&sym).unwrap_or(&sym)
    }

    fn lpo_gt(&self, s: &Term, t: &Term) -> bool {
        match s {
            Term::Var(_) => false,
            Term::Const(f) => match t {
                Term::Var(x) => s.occurs(*x),
                Term::Const(g) => self.prec(*f) > self.prec(*g),
                Term::App(_, _) => false,
            },
            Term::App(f, ss) => {
                // s = f(s1,...,sm)
                // Case 1: some si >= t
                if ss.iter().any(|si| self.lpo_ge(si, t)) {
                    return true;
                }

                match t {
                    Term::Var(x) => s.occurs(*x),
                    Term::Const(g) => self.prec(*f) > self.prec(*g),
                    Term::App(g, ts) => {
                        // t = g(t1,...,tn)
                        // Case 2: f > g and s > ti for all i
                        if self.prec(*f) > self.prec(*g) {
                            return ts.iter().all(|ti| self.lpo_gt(s, ti));
                        }
                        // Case 3: f = g and lexicographic comparison
                        if f == g {
                            for (k, (si, ti)) in ss.iter().zip(ts.iter()).enumerate() {
                                if self.lpo_gt(si, ti) {
                                    return ts.iter().skip(k + 1).all(|tj| self.lpo_gt(s, tj));
                                }
                                if si != ti {
                                    return false;
                                }
                            }
                        }
                        false
                    }
                }
            }
        }
    }

    fn lpo_ge(&self, s: &Term, t: &Term) -> bool {
        s == t || self.lpo_gt(s, t)
    }
}

impl TermOrdering for LPO {
    fn compare(&self, t1: &Term, t2: &Term) -> Option<Ordering> {
        if t1 == t2 {
            Some(Ordering::Equal)
        } else if self.lpo_gt(t1, t2) {
            Some(Ordering::Greater)
        } else if self.lpo_gt(t2, t1) {
            Some(Ordering::Less)
        } else {
            None
        }
    }
}

/// Clause selection strategy
#[derive(Clone, Copy, Debug)]
pub enum SelectionStrategy {
    /// First-in-first-out
    FIFO,
    /// Prefer smaller clauses
    SizeFirst,
    /// Prefer clauses with fewer symbols
    SymbolCount,
}

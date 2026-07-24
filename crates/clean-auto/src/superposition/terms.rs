// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! First-order terms, substitutions, unification, and matching.

use std::collections::{HashMap, HashSet};
use std::fmt;
use std::ops::ControlFlow;

/// A term in first-order logic
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Term {
    /// Variable (identified by index)
    Var(u32),
    /// Constant symbol
    Const(Symbol),
    /// Function application: f(t1, ..., tn)
    App(Symbol, Vec<Term>),
}

/// Symbol identifier
pub type Symbol = u32;

impl Term {
    /// Check if this term is a variable
    pub fn is_var(&self) -> bool {
        matches!(self, Term::Var(_))
    }

    /// Get all variables in this term
    pub fn vars(&self) -> HashSet<u32> {
        let mut result = HashSet::new();
        self.collect_vars(&mut result);
        result
    }

    fn collect_vars(&self, vars: &mut HashSet<u32>) {
        match self {
            Term::Var(v) => {
                vars.insert(*v);
            }
            Term::Const(_) => {}
            Term::App(_, args) => {
                for arg in args {
                    arg.collect_vars(vars);
                }
            }
        }
    }

    /// Check if variable `var` occurs anywhere in this term.
    /// Avoids HashSet allocation — pure traversal with early exit.
    pub fn occurs(&self, var: u32) -> bool {
        match self {
            Term::Var(v) => *v == var,
            Term::Const(_) => false,
            Term::App(_, args) => args.iter().any(|a| a.occurs(var)),
        }
    }

    /// Apply a substitution to this term
    ///
    /// Recursively applies the substitution until a fixed point is reached.
    /// This handles chains like {X2 → X0, X0 → c0} correctly.
    #[must_use]
    pub fn apply_subst(&self, subst: &Substitution) -> Term {
        match self {
            Term::Var(v) => match subst.get(*v) {
                Some(t) => t.apply_subst(subst), // Recursively apply to handle chains
                None => self.clone(),
            },
            Term::Const(_) => self.clone(),
            Term::App(f, args) => {
                Term::App(*f, args.iter().map(|a| a.apply_subst(subst)).collect())
            }
        }
    }

    /// Size of the term (number of symbols)
    pub fn size(&self) -> usize {
        match self {
            Term::Var(_) | Term::Const(_) => 1,
            Term::App(_, args) => 1 + args.iter().map(Term::size).sum::<usize>(),
        }
    }

    /// Get all positions in this term (path from root).
    /// Uses top-down traversal with push/pop to avoid O(d^2) insert(0,...).
    pub fn positions(&self) -> Vec<Position> {
        let mut result = Vec::new();
        self.visit_positions(|path, _| result.push(Position(path.to_vec())));
        result
    }

    /// Visit each term position lazily in depth-first order.
    pub fn visit_positions<'a, F>(&'a self, mut visitor: F)
    where
        F: FnMut(&[usize], &'a Term),
    {
        let mut prefix = Vec::new();
        self.visit_positions_impl(&mut prefix, &mut visitor);
    }

    /// Visit positions until the callback requests an early stop.
    pub fn try_visit_positions<'a, B, F>(&'a self, mut visitor: F) -> ControlFlow<B>
    where
        F: FnMut(&[usize], &'a Term) -> ControlFlow<B>,
    {
        let mut prefix = Vec::new();
        self.try_visit_positions_impl(&mut prefix, &mut visitor)
    }

    fn visit_positions_impl<'a, F>(&'a self, prefix: &mut Vec<usize>, visitor: &mut F)
    where
        F: FnMut(&[usize], &'a Term),
    {
        visitor(prefix.as_slice(), self);
        if let Term::App(_, args) = self {
            for (i, arg) in args.iter().enumerate() {
                prefix.push(i);
                arg.visit_positions_impl(prefix, visitor);
                prefix.pop();
            }
        }
    }

    fn try_visit_positions_impl<'a, B, F>(
        &'a self,
        prefix: &mut Vec<usize>,
        visitor: &mut F,
    ) -> ControlFlow<B>
    where
        F: FnMut(&[usize], &'a Term) -> ControlFlow<B>,
    {
        visitor(prefix.as_slice(), self)?;
        if let Term::App(_, args) = self {
            for (i, arg) in args.iter().enumerate() {
                prefix.push(i);
                let visit_result = arg.try_visit_positions_impl(prefix, visitor);
                prefix.pop();
                visit_result?;
            }
        }
        ControlFlow::Continue(())
    }

    /// Get subterm at position
    pub fn at_position(&self, pos: &Position) -> Option<&Term> {
        self.at_path(&pos.0)
    }

    /// Get subterm at a raw path slice.
    pub fn at_path(&self, path: &[usize]) -> Option<&Term> {
        let mut current = self;
        for &i in path {
            match current {
                Term::App(_, args) if i < args.len() => {
                    current = &args[i];
                }
                _ => return None,
            }
        }
        Some(current)
    }

    /// Replace subterm at position
    pub fn replace_at(&self, pos: &Position, replacement: Term) -> Option<Term> {
        self.replace_at_path(&pos.0, replacement)
    }

    /// Replace subterm at a raw path slice.
    pub fn replace_at_path(&self, path: &[usize], replacement: Term) -> Option<Term> {
        if path.is_empty() {
            return Some(replacement);
        }
        match self {
            Term::App(f, args) => {
                let idx = path[0];
                if idx >= args.len() {
                    return None;
                }
                let new_arg = args[idx].replace_at_path(&path[1..], replacement)?;
                let mut new_args = args.clone();
                new_args[idx] = new_arg;
                Some(Term::App(*f, new_args))
            }
            _ => None,
        }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Var(v) => write!(f, "X{v}"),
            Term::Const(c) => write!(f, "c{c}"),
            Term::App(func, args) if args.is_empty() => write!(f, "f{func}"),
            Term::App(func, args) => {
                write!(f, "f{func}(")?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{arg}")?;
                }
                write!(f, ")")
            }
        }
    }
}

/// Position in a term (path from root)
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Position(pub Vec<usize>);

impl Position {
    /// Root position
    pub fn root() -> Self {
        Position(vec![])
    }

    /// Check if this is the root position
    pub fn is_root(&self) -> bool {
        self.0.is_empty()
    }
}

/// A substitution mapping variables to terms
#[derive(Clone, Debug, Default)]
pub struct Substitution {
    pub(super) map: HashMap<u32, Term>,
}

impl Substitution {
    /// Create an empty substitution
    pub fn new() -> Self {
        Substitution {
            map: HashMap::new(),
        }
    }

    /// Bind a variable to a term
    pub fn bind(&mut self, var: u32, term: Term) {
        self.map.insert(var, term);
    }

    /// Get the binding for a variable
    pub fn get(&self, var: u32) -> Option<&Term> {
        self.map.get(&var)
    }

    /// Check if this substitution is empty
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Compose two substitutions: (self ∘ other)
    #[must_use]
    pub fn compose(&self, other: &Substitution) -> Substitution {
        let mut result = Substitution::new();

        // Apply other to all terms in self
        for (var, term) in &self.map {
            result.bind(*var, term.apply_subst(other));
        }

        // Add bindings from other that aren't in self
        for (var, term) in &other.map {
            if !result.map.contains_key(var) {
                result.bind(*var, term.clone());
            }
        }

        result
    }
}

/// Attempt to unify two terms, returning a most general unifier (MGU).
///
/// # Contracts
///
/// **ENSURES:**
/// - `Some(σ)` implies `σ(t1) = σ(t2)` structurally
/// - `None` implies no substitution makes `t1` and `t2` equal
/// - When `Some(σ)`, `σ` is the most general unifier (any other unifier is an instance)
/// - Occurs check prevents infinite terms (e.g., `X = f(X)` returns `None`)
pub fn unify(t1: &Term, t2: &Term) -> Option<Substitution> {
    let mut subst = Substitution::new();
    if unify_rec(t1, t2, &mut subst) {
        Some(subst)
    } else {
        None
    }
}

fn unify_rec(t1: &Term, t2: &Term, subst: &mut Substitution) -> bool {
    let t1 = apply_subst_to_term(t1, subst);
    let t2 = apply_subst_to_term(t2, subst);

    match (&t1, &t2) {
        (Term::Var(v1), Term::Var(v2)) if v1 == v2 => true,
        (Term::Var(v), t) | (t, Term::Var(v)) => {
            // Occurs check — O(n) traversal, no HashSet allocation
            if t.occurs(*v) {
                return false;
            }
            subst.bind(*v, t.clone());
            true
        }
        (Term::Const(c1), Term::Const(c2)) => c1 == c2,
        (Term::App(f1, args1), Term::App(f2, args2)) => {
            if f1 != f2 || args1.len() != args2.len() {
                return false;
            }
            for (a1, a2) in args1.iter().zip(args2.iter()) {
                if !unify_rec(a1, a2, subst) {
                    return false;
                }
            }
            true
        }
        _ => false,
    }
}

fn apply_subst_to_term(term: &Term, subst: &Substitution) -> Term {
    match term {
        Term::Var(v) => match subst.get(*v) {
            Some(t) => apply_subst_to_term(t, subst),
            None => term.clone(),
        },
        Term::Const(_) => term.clone(),
        Term::App(f, args) => Term::App(
            *f,
            args.iter().map(|a| apply_subst_to_term(a, subst)).collect(),
        ),
    }
}

/// Attempt to match t1 against t2 (one-way unification)
/// Returns a substitution σ such that t1σ = t2
pub fn match_terms(pattern: &Term, target: &Term) -> Option<Substitution> {
    let mut subst = Substitution::new();
    if match_rec(pattern, target, &mut subst) {
        Some(subst)
    } else {
        None
    }
}

/// One-way matching that may bind ONLY pattern variables `>= bind_min`;
/// every variable below `bind_min` is FROZEN and matches only itself.
///
/// Callers rename the pattern's clause apart so its variables all sit at or
/// above `bind_min` while the target's variables all sit below it. The
/// resulting substitution is then bipartite — domain `>= bind_min`, range
/// containing only frozen variables — so it can never be self-referential and
/// [`Term::apply_subst`]'s chain-following application always terminates.
pub fn match_terms_frozen(pattern: &Term, target: &Term, bind_min: u32) -> Option<Substitution> {
    let mut subst = Substitution::new();
    if match_rec_frozen(pattern, target, bind_min, &mut subst) {
        Some(subst)
    } else {
        None
    }
}

fn match_rec_frozen(
    pattern: &Term,
    target: &Term,
    bind_min: u32,
    subst: &mut Substitution,
) -> bool {
    match (pattern, target) {
        // A frozen variable (below bind_min) is a rigid symbol: it matches
        // only the identical variable. This keeps the substitution's domain
        // disjoint from every variable that can appear in its range.
        (Term::Var(v), _) if *v < bind_min => pattern == target,
        (Term::Var(v), _) => {
            if let Some(bound) = subst.get(*v) {
                bound == target
            } else {
                subst.bind(*v, target.clone());
                true
            }
        }
        (Term::Const(c1), Term::Const(c2)) => c1 == c2,
        (Term::App(f1, args1), Term::App(f2, args2)) => {
            if f1 != f2 || args1.len() != args2.len() {
                return false;
            }
            args1
                .iter()
                .zip(args2.iter())
                .all(|(a1, a2)| match_rec_frozen(a1, a2, bind_min, subst))
        }
        _ => false,
    }
}

fn match_rec(pattern: &Term, target: &Term, subst: &mut Substitution) -> bool {
    match (pattern, target) {
        (Term::Var(v), _) => {
            if let Some(bound) = subst.get(*v) {
                bound == target
            } else {
                subst.bind(*v, target.clone());
                true
            }
        }
        (Term::Const(c1), Term::Const(c2)) => c1 == c2,
        (Term::App(f1, args1), Term::App(f2, args2)) => {
            if f1 != f2 || args1.len() != args2.len() {
                return false;
            }
            for (a1, a2) in args1.iter().zip(args2.iter()) {
                if !match_rec(a1, a2, subst) {
                    return false;
                }
            }
            true
        }
        _ => false,
    }
}

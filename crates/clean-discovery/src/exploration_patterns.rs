// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Pattern templates for algebraic identity exploration.
//!
//! Provides term enumeration up to a given depth and pattern instantiation
//! for common algebraic identities (commutativity, associativity,
//! distributivity, etc.).
//!
//! Part of #3194.

use clean_kernel::{BinderInfo, Expr};

/// A function signature available for exploration.
///
/// Describes a named function with its arity and the sort it operates on.
#[derive(Debug, Clone)]
pub struct FuncSig {
    /// Fully qualified name (e.g., "Nat.add").
    pub name: String,
    /// Number of arguments the function takes.
    pub arity: u32,
    /// The sort/type that the function operates on (e.g., Nat, Int).
    pub sort: Expr,
}

/// Algebraic pattern templates for candidate generation.
///
/// Each variant describes a structural equation template that can be
/// instantiated with concrete function signatures.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum TermPattern {
    /// `f(a, b) = f(b, a)` — commutativity of a binary operation.
    Commutativity,
    /// `f(f(a, b), c) = f(a, f(b, c))` — associativity of a binary operation.
    Associativity,
    /// `f(a, g(b, c)) = g(f(a, b), f(a, c))` — left distributivity of f over g.
    Distributivity,
    /// `f(a, e) = a` — right identity element.
    Identity,
    /// `f(a, a) = a` — idempotency.
    Idempotency,
    /// `f(a, g(a, b)) = a` — absorption.
    Absorption,
    /// `a <= b -> f(a) <= f(b)` — monotonicity.
    Monotonicity,
    /// `f(a, b) = f(a, b)` — trivial equality (baseline/sanity check).
    Equality,
    /// `f(a, b) <= f(a, c)` when `b <= c` — ordering preservation.
    Ordering,
}

impl std::fmt::Display for TermPattern {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Commutativity => write!(f, "commutativity"),
            Self::Associativity => write!(f, "associativity"),
            Self::Distributivity => write!(f, "distributivity"),
            Self::Identity => write!(f, "identity"),
            Self::Idempotency => write!(f, "idempotency"),
            Self::Absorption => write!(f, "absorption"),
            Self::Monotonicity => write!(f, "monotonicity"),
            Self::Equality => write!(f, "equality"),
            Self::Ordering => write!(f, "ordering"),
        }
    }
}

impl TermPattern {
    /// All known patterns.
    pub const ALL: &'static [Self] = &[
        Self::Commutativity,
        Self::Associativity,
        Self::Distributivity,
        Self::Identity,
        Self::Idempotency,
        Self::Absorption,
        Self::Monotonicity,
        Self::Equality,
        Self::Ordering,
    ];

    /// Minimum arity required for the primary function in this pattern.
    #[must_use]
    pub fn min_arity(&self) -> u32 {
        match self {
            Self::Monotonicity => 1,
            Self::Equality | Self::Ordering => 2,
            Self::Commutativity
            | Self::Associativity
            | Self::Distributivity
            | Self::Identity
            | Self::Idempotency
            | Self::Absorption => 2,
        }
    }

    /// Whether this pattern requires a second function (e.g., distributivity
    /// needs both f and g).
    #[must_use]
    pub fn needs_second_func(&self) -> bool {
        matches!(self, Self::Distributivity | Self::Absorption)
    }
}

/// A candidate equation generated from a pattern template.
#[derive(Debug, Clone)]
pub struct CandidateEquation {
    /// The pattern that generated this equation.
    pub pattern: TermPattern,
    /// The universally quantified statement as a kernel Expr.
    /// Structured as `forall (vars...), lhs = rhs` (or `lhs -> rhs` for implications).
    pub statement: Expr,
    /// Human-readable description for diagnostics.
    pub description: String,
    /// Names of functions involved.
    pub func_names: Vec<String>,
}

/// Generate candidate equations from a set of function signatures and patterns.
///
/// For each applicable `(pattern, func_sig)` combination, produces a
/// `CandidateEquation` with the universally quantified statement.
#[must_use]
pub fn generate_candidates(
    signatures: &[FuncSig],
    patterns: &[TermPattern],
    eq_const: &str,
) -> Vec<CandidateEquation> {
    let mut candidates = Vec::new();

    let binary_funcs: Vec<&FuncSig> = signatures.iter().filter(|s| s.arity == 2).collect();
    let unary_funcs: Vec<&FuncSig> = signatures.iter().filter(|s| s.arity == 1).collect();

    for &pattern in patterns {
        match pattern {
            // Single binary function patterns
            TermPattern::Commutativity
            | TermPattern::Associativity
            | TermPattern::Identity
            | TermPattern::Idempotency
            | TermPattern::Equality
            | TermPattern::Ordering => {
                candidates.extend(
                    binary_funcs
                        .iter()
                        .filter_map(|f| build_single_binary(pattern, f, eq_const)),
                );
            }
            // Paired binary function patterns
            TermPattern::Distributivity | TermPattern::Absorption => {
                for f in &binary_funcs {
                    for g in &binary_funcs {
                        if f.name != g.name {
                            let eq = match pattern {
                                TermPattern::Distributivity => build_distributivity(f, g, eq_const),
                                TermPattern::Absorption => build_absorption(f, g, eq_const),
                                _ => None,
                            };
                            candidates.extend(eq);
                        }
                    }
                }
            }
            // Unary function patterns
            TermPattern::Monotonicity => {
                candidates.extend(unary_funcs.iter().filter_map(|f| build_monotonicity(f)));
            }
        }
    }

    candidates
}

/// Enumerate all terms up to `max_depth` using the given function signatures
/// and `num_vars` free variables (represented as BVar(0)..BVar(num_vars-1)).
///
/// Returns a vector of `(term, depth)` pairs.
#[must_use]
pub fn enumerate_terms(signatures: &[FuncSig], num_vars: u32, max_depth: u32) -> Vec<(Expr, u32)> {
    let mut terms = Vec::new();

    // Depth 0: variables only
    for i in 0..num_vars {
        terms.push((Expr::bvar(i), 0));
    }

    // Depth 1..max_depth: apply functions to existing terms
    for depth in 1..=max_depth {
        let prev: Vec<(Expr, u32)> = terms.clone();
        for sig in signatures {
            match sig.arity {
                1 => {
                    let func = Expr::const_str(&sig.name);
                    for (arg, d) in &prev {
                        if *d < depth {
                            terms.push((Expr::app(func.clone(), arg.clone()), depth));
                        }
                    }
                }
                2 => {
                    let func = Expr::const_str(&sig.name);
                    for (arg1, d1) in &prev {
                        for (arg2, d2) in &prev {
                            let child_depth = (*d1).max(*d2);
                            if child_depth < depth {
                                terms.push((
                                    Expr::apps(func.clone(), [arg1.clone(), arg2.clone()]),
                                    depth,
                                ));
                            }
                        }
                    }
                }
                _ => {} // Skip higher arities for now
            }
        }
    }

    terms
}

// --- Pattern builders ---

/// Dispatch single-binary-function patterns.
fn build_single_binary(
    pattern: TermPattern,
    f: &FuncSig,
    eq_const: &str,
) -> Option<CandidateEquation> {
    match pattern {
        TermPattern::Commutativity => build_commutativity(f, eq_const),
        TermPattern::Associativity => build_associativity(f, eq_const),
        TermPattern::Identity => build_identity(f, eq_const),
        TermPattern::Idempotency => build_idempotency(f, eq_const),
        TermPattern::Equality => build_equality(f, eq_const),
        TermPattern::Ordering => build_ordering(f),
        _ => None,
    }
}

/// `forall (a b : S), f(a, b) = f(b, a)`
fn build_commutativity(f: &FuncSig, eq_const: &str) -> Option<CandidateEquation> {
    let sort = &f.sort;
    // Under 2 binders: a=BVar(1), b=BVar(0) (outer pi binds a, inner binds b).
    let func = Expr::const_str(&f.name);
    let lhs = Expr::apps(func.clone(), [Expr::bvar(1), Expr::bvar(0)]);
    let rhs = Expr::apps(func, [Expr::bvar(0), Expr::bvar(1)]);
    let eq_expr = mk_eq(eq_const, sort, &lhs, &rhs);
    let stmt = Expr::pi(
        BinderInfo::Default,
        sort.clone(),
        Expr::pi(BinderInfo::Default, sort.clone(), eq_expr),
    );

    Some(CandidateEquation {
        pattern: TermPattern::Commutativity,
        statement: stmt,
        description: format!("{} is commutative", f.name),
        func_names: vec![f.name.clone()],
    })
}

/// `forall (a b c : S), f(f(a, b), c) = f(a, f(b, c))`
fn build_associativity(f: &FuncSig, eq_const: &str) -> Option<CandidateEquation> {
    let sort = &f.sort;
    // Under 3 binders: a=BVar(2), b=BVar(1), c=BVar(0)
    let func = Expr::const_str(&f.name);
    let lhs = Expr::apps(
        func.clone(),
        [
            Expr::apps(func.clone(), [Expr::bvar(2), Expr::bvar(1)]),
            Expr::bvar(0),
        ],
    );
    let rhs = Expr::apps(
        func,
        [
            Expr::bvar(2),
            Expr::apps(Expr::const_str(&f.name), [Expr::bvar(1), Expr::bvar(0)]),
        ],
    );
    let eq_expr = mk_eq(eq_const, sort, &lhs, &rhs);
    let stmt = Expr::pi(
        BinderInfo::Default,
        sort.clone(),
        Expr::pi(
            BinderInfo::Default,
            sort.clone(),
            Expr::pi(BinderInfo::Default, sort.clone(), eq_expr),
        ),
    );

    Some(CandidateEquation {
        pattern: TermPattern::Associativity,
        statement: stmt,
        description: format!("{} is associative", f.name),
        func_names: vec![f.name.clone()],
    })
}

/// `forall (a b c : S), f(a, g(b, c)) = g(f(a, b), f(a, c))`
fn build_distributivity(f: &FuncSig, g: &FuncSig, eq_const: &str) -> Option<CandidateEquation> {
    let sort = &f.sort;
    let ff = Expr::const_str(&f.name);
    let gf = Expr::const_str(&g.name);
    // Under 3 binders: a=BVar(2), b=BVar(1), c=BVar(0)
    let lhs = Expr::apps(
        ff.clone(),
        [
            Expr::bvar(2),
            Expr::apps(gf.clone(), [Expr::bvar(1), Expr::bvar(0)]),
        ],
    );
    let rhs = Expr::apps(
        gf,
        [
            Expr::apps(ff.clone(), [Expr::bvar(2), Expr::bvar(1)]),
            Expr::apps(ff, [Expr::bvar(2), Expr::bvar(0)]),
        ],
    );
    let eq_expr = mk_eq(eq_const, sort, &lhs, &rhs);
    let stmt = Expr::pi(
        BinderInfo::Default,
        sort.clone(),
        Expr::pi(
            BinderInfo::Default,
            sort.clone(),
            Expr::pi(BinderInfo::Default, sort.clone(), eq_expr),
        ),
    );

    Some(CandidateEquation {
        pattern: TermPattern::Distributivity,
        statement: stmt,
        description: format!("{} distributes over {}", f.name, g.name),
        func_names: vec![f.name.clone(), g.name.clone()],
    })
}

/// `forall (a : S), f(a, e) = a`
///
/// Uses `Nat.zero` as the identity candidate for Nat operations.
fn build_identity(f: &FuncSig, eq_const: &str) -> Option<CandidateEquation> {
    let sort = &f.sort;
    // Under 1 binder: a=BVar(0)
    let func = Expr::const_str(&f.name);
    let zero = Expr::nat_lit(0);
    let lhs = Expr::apps(func, [Expr::bvar(0), zero]);
    let rhs = Expr::bvar(0);
    let eq_expr = mk_eq(eq_const, sort, &lhs, &rhs);
    let stmt = Expr::pi(BinderInfo::Default, sort.clone(), eq_expr);

    Some(CandidateEquation {
        pattern: TermPattern::Identity,
        statement: stmt,
        description: format!("{} has right identity 0", f.name),
        func_names: vec![f.name.clone()],
    })
}

/// `forall (a : S), f(a, a) = a`
fn build_idempotency(f: &FuncSig, eq_const: &str) -> Option<CandidateEquation> {
    let sort = &f.sort;
    let func = Expr::const_str(&f.name);
    let lhs = Expr::apps(func, [Expr::bvar(0), Expr::bvar(0)]);
    let rhs = Expr::bvar(0);
    let eq_expr = mk_eq(eq_const, sort, &lhs, &rhs);
    let stmt = Expr::pi(BinderInfo::Default, sort.clone(), eq_expr);

    Some(CandidateEquation {
        pattern: TermPattern::Idempotency,
        statement: stmt,
        description: format!("{} is idempotent", f.name),
        func_names: vec![f.name.clone()],
    })
}

/// `forall (a b : S), f(a, g(a, b)) = a`
fn build_absorption(f: &FuncSig, g: &FuncSig, eq_const: &str) -> Option<CandidateEquation> {
    let sort = &f.sort;
    let ff = Expr::const_str(&f.name);
    let gf = Expr::const_str(&g.name);
    // Under 2 binders: a=BVar(1), b=BVar(0)
    let lhs = Expr::apps(
        ff,
        [
            Expr::bvar(1),
            Expr::apps(gf, [Expr::bvar(1), Expr::bvar(0)]),
        ],
    );
    let rhs = Expr::bvar(1);
    let eq_expr = mk_eq(eq_const, sort, &lhs, &rhs);
    let stmt = Expr::pi(
        BinderInfo::Default,
        sort.clone(),
        Expr::pi(BinderInfo::Default, sort.clone(), eq_expr),
    );

    Some(CandidateEquation {
        pattern: TermPattern::Absorption,
        statement: stmt,
        description: format!("{} absorbs {}", f.name, g.name),
        func_names: vec![f.name.clone(), g.name.clone()],
    })
}

/// `forall (a b : S), a <= b -> f(a) <= f(b)`
fn build_monotonicity(f: &FuncSig) -> Option<CandidateEquation> {
    let sort = &f.sort;
    let func = Expr::const_str(&f.name);
    let le = Expr::const_str_levels("LE.le", vec![clean_kernel::Level::zero()]);
    let inst_le = Expr::const_str("instLENat");

    // Under 3 binders: a=BVar(2), b=BVar(1), _proof=BVar(0)
    let premise = Expr::apps(
        le.clone(),
        [sort.clone(), inst_le.clone(), Expr::bvar(1), Expr::bvar(0)],
    );
    let conclusion = Expr::apps(
        le,
        [
            sort.clone(),
            inst_le,
            Expr::app(func.clone(), Expr::bvar(2)),
            Expr::app(func, Expr::bvar(1)),
        ],
    );
    let stmt = Expr::pi(
        BinderInfo::Default,
        sort.clone(),
        Expr::pi(
            BinderInfo::Default,
            sort.clone(),
            Expr::pi(BinderInfo::Default, premise, conclusion),
        ),
    );

    Some(CandidateEquation {
        pattern: TermPattern::Monotonicity,
        statement: stmt,
        description: format!("{} is monotone", f.name),
        func_names: vec![f.name.clone()],
    })
}

/// `forall (a b : S), f(a, b) = f(a, b)` — trivially true, used as sanity check.
fn build_equality(f: &FuncSig, eq_const: &str) -> Option<CandidateEquation> {
    let sort = &f.sort;
    let func = Expr::const_str(&f.name);
    let term = Expr::apps(func, [Expr::bvar(1), Expr::bvar(0)]);
    let eq_expr = mk_eq(eq_const, sort, &term, &term);
    let stmt = Expr::pi(
        BinderInfo::Default,
        sort.clone(),
        Expr::pi(BinderInfo::Default, sort.clone(), eq_expr),
    );

    Some(CandidateEquation {
        pattern: TermPattern::Equality,
        statement: stmt,
        description: format!("{} equals itself", f.name),
        func_names: vec![f.name.clone()],
    })
}

/// `forall (a b c : S), b <= c -> f(a, b) <= f(a, c)`
fn build_ordering(f: &FuncSig) -> Option<CandidateEquation> {
    let sort = &f.sort;
    let func = Expr::const_str(&f.name);
    let le = Expr::const_str_levels("LE.le", vec![clean_kernel::Level::zero()]);
    let inst_le = Expr::const_str("instLENat");

    // Under 4 binders: a=BVar(3), b=BVar(2), c=BVar(1), _proof=BVar(0)
    let premise = Expr::apps(
        le.clone(),
        [sort.clone(), inst_le.clone(), Expr::bvar(1), Expr::bvar(0)],
    );
    let conclusion = Expr::apps(
        le,
        [
            sort.clone(),
            inst_le,
            Expr::apps(func.clone(), [Expr::bvar(3), Expr::bvar(2)]),
            Expr::apps(func, [Expr::bvar(3), Expr::bvar(1)]),
        ],
    );
    let stmt = Expr::pi(
        BinderInfo::Default,
        sort.clone(),
        Expr::pi(
            BinderInfo::Default,
            sort.clone(),
            Expr::pi(
                BinderInfo::Default,
                sort.clone(),
                Expr::pi(BinderInfo::Default, premise, conclusion),
            ),
        ),
    );

    Some(CandidateEquation {
        pattern: TermPattern::Ordering,
        statement: stmt,
        description: format!("{} preserves ordering in second arg", f.name),
        func_names: vec![f.name.clone()],
    })
}

/// Build `@Eq S lhs rhs`.
fn mk_eq(eq_const: &str, sort: &Expr, lhs: &Expr, rhs: &Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels(
            eq_const,
            vec![clean_kernel::Level::succ(clean_kernel::Level::zero())],
        ),
        [sort.clone(), lhs.clone(), rhs.clone()],
    )
}

#[cfg(test)]
#[path = "exploration_patterns_tests.rs"]
mod tests;

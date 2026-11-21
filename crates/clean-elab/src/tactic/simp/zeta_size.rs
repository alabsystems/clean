// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! How large a term's βζ-normal form is, measured without building it.
//!
//! [`super::reduce::beta_reduce`] substitutes each `let` value (except a match
//! join point's, which it keeps and this count keeps too), and each
//! β-redex argument, at every occurrence of its variable. A definition whose
//! `match` binds a large catch-all right-hand side once (`let alt := rhs`
//! named by several minors, G76, `infer/elab_match/shared_alt.rs`) is linear
//! as written and exponential once normalized, and an iota reduct
//! `succ n (T.rec motive zero succ n)` copies the whole minor into every
//! recursive call it contains: `simp [Pred.impliesFuel]` asked
//! `rec_equations::beta_normal` for that normal form and grew past an 8 GB
//! resident bound in five seconds (trust-ir `Proofs/PredLatticeProps.lean`,
//! 2026-10-16).
//!
//! The count here evaluates the term abstractly: a variable stands for the
//! SIZE of what it is bound to, or, when it is bound to a λ, for that λ
//! itself, so applying it counts its body with the arguments' sizes in place
//! — the normal form's size, step by step. Every step is charged, and the
//! walk stops at [`STEPS_PER_NODE`] steps per node of the limit, so its cost
//! is bounded whatever the term. Kernel-checked terms are strongly normalizing; the step bound makes
//! the count total on any input.

use std::rc::Rc;

use clean_kernel::{Expr, ExprKind};

/// Steps the count may take per node of its limit. Evaluating a node costs one
/// step and visiting its normal form about one more, so this leaves room for
/// work a reduction discards (`(fun _ => b) arg` evaluates `arg`).
const STEPS_PER_NODE: u64 = 4;

/// Whether the βζ-normal form of `expr` has at least `limit` nodes (as a
/// tree), or counting it took [`STEPS_PER_NODE`] steps per node of `limit`
/// (fail-closed: the caller declines).
pub(super) fn beta_zeta_size_reaches(expr: &Expr, limit: u64) -> bool {
    beta_zeta_limit(expr, limit).is_some()
}

#[derive(Debug, Clone, Copy)]
pub(super) enum BetaZetaLimit {
    Nodes(u64),
    Steps(u64),
}

/// Keep the same refusal predicate as the bounded count, with its actual cause.
pub(super) fn beta_zeta_limit(expr: &Expr, limit: u64) -> Option<BetaZetaLimit> {
    let mut eval = SizeEval {
        steps: 0,
        step_limit: limit.saturating_mul(STEPS_PER_NODE),
        limit,
    };
    let value = eval.eval(expr, &Env::Empty);
    if eval.size_of(&value) < limit {
        None
    } else if eval.spent() {
        Some(BetaZetaLimit::Steps(eval.step_limit))
    } else {
        Some(BetaZetaLimit::Nodes(limit))
    }
}

/// What a variable stands for.
#[derive(Clone)]
enum Val<'e> {
    /// A term of this many nodes.
    Size(u64),
    /// The λ `fun (_ : ty) => body`, closed over `env`.
    Lam {
        ty: &'e Expr,
        body: &'e Expr,
        env: Env<'e>,
    },
}

/// Bound variables, innermost first (`BVar 0` is the head).
#[derive(Clone)]
enum Env<'e> {
    Empty,
    Bind(Rc<(Val<'e>, Env<'e>)>),
}

impl<'e> Env<'e> {
    fn push(&self, val: Val<'e>) -> Self {
        Env::Bind(Rc::new((val, self.clone())))
    }

    fn get(&self, idx: u32) -> Option<&Val<'e>> {
        let mut env = self;
        let mut idx = idx;
        loop {
            match env {
                Env::Empty => return None,
                Env::Bind(node) if idx == 0 => return Some(&node.0),
                Env::Bind(node) => {
                    env = &node.1;
                    idx -= 1;
                }
            }
        }
    }
}

struct SizeEval {
    steps: u64,
    step_limit: u64,
    limit: u64,
}

impl SizeEval {
    fn spent(&self) -> bool {
        self.steps >= self.step_limit
    }

    fn eval<'e>(&mut self, expr: &'e Expr, env: &Env<'e>) -> Val<'e> {
        crate::stack_safe(|| self.eval_inner(expr, env))
    }

    fn eval_inner<'e>(&mut self, expr: &'e Expr, env: &Env<'e>) -> Val<'e> {
        self.steps += 1;
        if self.spent() {
            return Val::Size(self.limit);
        }
        match expr.kind() {
            ExprKind::BVar(idx) => env.get(*idx).cloned().unwrap_or(Val::Size(1)),
            ExprKind::Lam(_, ty, body) => Val::Lam {
                ty,
                body,
                env: env.clone(),
            },
            // A match join point stays a `let`, as `beta_reduce` keeps it
            // (`crate::infer::is_match_join_binder`): the `let` node, its
            // type, its value's normal form and its body's, where the
            // variable stands for itself. Counting it substituted measured a
            // normal form `beta_reduce` never builds, so `beta_normal` and
            // simp's β step refused a definition the join points keep linear.
            ExprKind::Let(name, ty, val, body, _) if crate::infer::is_match_join_binder(name) => {
                let ty = self.eval(ty, env);
                let ty = self.size_of(&ty);
                let val = self.eval(val, env);
                let val = self.size_of(&val);
                let body = self.eval(body, &env.push(Val::Size(1)));
                let body = self.size_of(&body);
                Val::Size(self.sum(&[1, ty, val, body]))
            }
            // ζ: the value stands at every occurrence of the variable.
            ExprKind::Let(_, _, val, body, _) => {
                let val = self.eval(val, env);
                self.eval(body, &env.push(val))
            }
            ExprKind::App(f, a) => {
                let f = self.eval(f, env);
                let a = self.eval(a, env);
                self.apply(f, a)
            }
            ExprKind::Pi(_, ty, body) => {
                let ty = self.eval(ty, env);
                let ty = self.size_of(&ty);
                let body = self.eval(body, &env.push(Val::Size(1)));
                let body = self.size_of(&body);
                Val::Size(self.sum(&[1, ty, body]))
            }
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => {
                let inner = self.eval(inner, env);
                let inner = self.size_of(&inner);
                Val::Size(self.sum(&[1, inner]))
            }
            _ => Val::Size(1),
        }
    }

    /// β: a λ applied to an argument is its body with the argument in place;
    /// anything else applied is one application node more.
    fn apply<'e>(&mut self, f: Val<'e>, a: Val<'e>) -> Val<'e> {
        match f {
            Val::Lam { body, env, .. } => self.eval(body, &env.push(a)),
            Val::Size(f) => {
                let a = self.size_of(&a);
                Val::Size(self.sum(&[1, f, a]))
            }
        }
    }

    fn size_of(&mut self, val: &Val<'_>) -> u64 {
        match val {
            Val::Size(size) => *size,
            Val::Lam { ty, body, env } => {
                if self.spent() {
                    return self.limit;
                }
                let ty = self.eval(ty, env);
                let ty = self.size_of(&ty);
                let body = self.eval(body, &env.push(Val::Size(1)));
                let body = self.size_of(&body);
                self.sum(&[1, ty, body])
            }
        }
    }

    fn sum(&self, parts: &[u64]) -> u64 {
        parts
            .iter()
            .fold(0u64, |acc, part| acc.saturating_add(*part))
            .min(self.limit)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{BinderInfo, Name};

    fn c(name: &str) -> Expr {
        Expr::const_(Name::from_string(name), vec![])
    }

    #[test]
    fn test_beta_zeta_size_counts_a_let_value_at_each_use() {
        // let x := f a; g x x x  →  g (f a) (f a) (f a).
        let value = Expr::app(c("f"), c("a"));
        let body = Expr::app(
            Expr::app(Expr::app(c("g"), Expr::bvar(0)), Expr::bvar(0)),
            Expr::bvar(0),
        );
        let e = Expr::let_named(Name::from_string("x"), c("T"), value, body, false);
        // g + 3 apps + 3 × (app f a = 3 nodes) = 1 + 3 + 9 = 13.
        assert!(beta_zeta_size_reaches(&e, 13));
        assert!(!beta_zeta_size_reaches(&e, 14));
    }

    #[test]
    fn test_beta_zeta_size_nested_lets_multiply_and_stop_at_the_limit() {
        // let x₀ := c; let x₁ := pair x₀ x₀; … sixty deep: about 2^62 nodes
        // normalized, about 300 as written; the count stops at the limit.
        let mut e = c("leaf");
        for _ in 0..60 {
            e = Expr::let_named(
                Name::from_string("x"),
                c("T"),
                e,
                Expr::app(Expr::app(c("pair"), Expr::bvar(0)), Expr::bvar(0)),
                false,
            );
        }
        assert!(beta_zeta_size_reaches(&e, 1 << 20));
        assert!(!beta_zeta_size_reaches(&Expr::app(c("leaf"), c("leaf")), 4));
    }

    /// A `let x := e; pair x x` tower sixty deep: about 2^62 nodes with each
    /// `let` substituted, about 420 with each kept.
    fn pair_tower(binder: &str) -> Expr {
        let mut e = c("leaf");
        for _ in 0..60 {
            e = Expr::let_named(
                Name::from_string(binder),
                c("T"),
                e,
                Expr::app(Expr::app(c("pair"), Expr::bvar(0)), Expr::bvar(0)),
                false,
            );
        }
        e
    }

    fn tree_nodes(e: &Expr) -> u64 {
        match e.kind() {
            ExprKind::App(f, a) => 1 + tree_nodes(f) + tree_nodes(a),
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                1 + tree_nodes(ty) + tree_nodes(body)
            }
            ExprKind::Let(_, ty, val, body, _) => {
                1 + tree_nodes(ty) + tree_nodes(val) + tree_nodes(body)
            }
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => 1 + tree_nodes(inner),
            _ => 1,
        }
    }

    #[test]
    fn test_beta_zeta_size_keeps_a_match_join_let_as_beta_reduce_does() {
        // `beta_reduce` keeps a match join point's `let` (RM1); the count is
        // the size of exactly the term it builds, not of the substituted one.
        let kept = pair_tower(crate::infer::MATCH_JOIN_BINDER);
        let reduct = super::super::reduce::beta_reduce(&kept);
        assert!(
            matches!(reduct.kind(), ExprKind::Let(..)),
            "beta_reduce keeps the join `let`"
        );
        let nodes = tree_nodes(&reduct);
        assert!(nodes < 1_000, "the kept tower is linear: {nodes} nodes");
        assert!(beta_zeta_size_reaches(&kept, nodes));
        assert!(!beta_zeta_size_reaches(&kept, nodes + 1));
        // Any other binder is still substituted at each use.
        assert!(beta_zeta_size_reaches(&pair_tower("x"), 1 << 20));
    }

    #[test]
    fn test_beta_zeta_size_follows_a_lambda_into_the_redex_it_makes() {
        // (fun f => g (f a) (f a)) (fun x => h x x): the argument is a λ, so
        // each `f a` is `h a a` once normalized: g + 2 apps + 2 × 5 = 13.
        let lam = |body: Expr| Expr::lam(BinderInfo::Default, c("T"), body);
        let inner = lam(Expr::app(Expr::app(c("h"), Expr::bvar(0)), Expr::bvar(0)));
        let f_a = Expr::app(Expr::bvar(0), c("a"));
        let outer = lam(Expr::app(Expr::app(c("g"), f_a.clone()), f_a));
        let e = Expr::app(outer, inner);
        assert!(beta_zeta_size_reaches(&e, 13));
        assert!(!beta_zeta_size_reaches(&e, 14));
    }
}

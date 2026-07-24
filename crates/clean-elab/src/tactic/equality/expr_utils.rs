// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Expression utility functions for equality manipulation.
//!
//! Pure expression helpers with no `ProofState` dependency. These are used
//! broadly across equality tactics and by other tactic modules (generalize,
//! calc, ring, etc.).

use std::sync::Arc;

use clean_kernel::{Expr, ExprKind, ExprVisitor, Level, Name};

use super::super::op_projection::is_hetero_op_projection;
use super::super::{RewriteCandidate, TacticError};
use crate::stack_safe;

/// Match an expression against the equality pattern `Eq α a b`
///
/// REQUIRES: `expr` is a fully instantiated expression (no unresolved metavariables).
/// ENSURES: On `Ok((α, a, b, levels))`, `expr` is `@Eq.{levels} α a b` with exactly 3 args.
/// ENSURES: On `Err`, `expr` is not an `Eq` application or has wrong arity.
pub(crate) fn match_equality(expr: &Expr) -> Result<(Expr, Expr, Expr, Vec<Level>), TacticError> {
    let head = expr.get_app_fn();
    let args = expr.get_app_args();

    match head.kind() {
        ExprKind::Const(name, levels) if name == &Name::from_string("Eq") => {
            if args.len() != 3 {
                return Err(TacticError::InvalidTarget {
                    tactic: "match_equality".into(),
                    detail: format!("malformed equality: expected 3 args, got {}", args.len()),
                });
            }
            Ok((
                args[0].clone(), // type α
                args[1].clone(), // lhs a
                args[2].clone(), // rhs b
                levels.to_vec(),
            ))
        }
        _ => Err(TacticError::GoalMismatch(
            "hypothesis is not an equality".into(),
        )),
    }
}

/// Match an expression against the propositional-equivalence pattern `Iff p q`.
///
/// REQUIRES: `expr` is a fully instantiated expression (no unresolved metavariables).
/// ENSURES: On `Some((p, q))`, `expr` is `@Iff p q` (head `Const("Iff")`, exactly 2 args).
/// ENSURES: On `None`, `expr` is not an `Iff` application of arity 2.
///
/// `Iff` is an inductive *structure* with `num_params == 2` and no level params,
/// so a head `Const("Iff")` applied to two `Prop` arguments is the canonical form;
/// WHNF does not reduce it to a `Pi`. This lets `rw` treat `h : p ↔ q` as a
/// rewrite source by adapting it to an `Eq` via `propext` (see `rewrite.rs`).
pub(crate) fn match_iff(expr: &Expr) -> Option<(Expr, Expr)> {
    let head = expr.get_app_fn();
    let args = expr.get_app_args();

    match head.kind() {
        ExprKind::Const(name, _levels) if name == &Name::from_string("Iff") && args.len() == 2 => {
            Some((args[0].clone(), args[1].clone()))
        }
        _ => None,
    }
}

/// Check if an expression contains a subexpression
///
/// REQUIRES: `haystack` and `needle` are well-formed expressions.
/// ENSURES: Returns `true` iff `needle` occurs as a structural subexpression of
///   `haystack` (equality by `Expr::eq`, not definitional equality).
/// ENSURES: Runs under `stack_safe` to prevent stack overflow on deep terms.
pub(crate) fn contains_expr(haystack: &Expr, needle: &Expr) -> bool {
    struct ContainsVisitor<'a> {
        needle: &'a Expr,
    }

    impl ExprVisitor for ContainsVisitor<'_> {
        type Result = bool;

        fn combine(&self, a: bool, b: bool) -> bool {
            a || b
        }

        fn visit_expr(&mut self, expr: &Expr) -> bool {
            if expr == self.needle {
                return true;
            }
            // Delegate to default structural recursion for child traversal.
            // We call each child explicitly to reuse our visit_expr override.
            match expr.kind() {
                ExprKind::App(f, a) => {
                    let rf = self.visit_expr(f);
                    let ra = self.visit_expr(a);
                    self.combine(rf, ra)
                }
                ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                    let rt = self.visit_expr(ty);
                    let rb = self.visit_expr(body);
                    self.combine(rt, rb)
                }
                ExprKind::Let(_, ty, val, body, _) => {
                    let rt = self.visit_expr(ty);
                    let rv = self.visit_expr(val);
                    let rb = self.visit_expr(body);
                    self.combine(rt, self.combine(rv, rb))
                }
                ExprKind::Proj(_, _, inner)
                | ExprKind::MData(_, inner)
                | ExprKind::Squash(inner) => self.visit_expr(inner),
                _ => false,
            }
        }
    }

    let mut visitor = ContainsVisitor { needle };
    visitor.visit_expr(haystack)
}

/// Return nearby subterms for a failed rewrite diagnostic.
pub(crate) fn rewrite_candidate_summaries(
    haystack: &Expr,
    needle: &Expr,
    limit: usize,
) -> Vec<RewriteCandidate> {
    fn collect(expr: &Expr, path: &mut Vec<String>, out: &mut Vec<(usize, String, String)>) {
        let rendered = expr.to_string();
        out.push((rendered.len(), path.join("."), rendered));
        match expr.kind() {
            ExprKind::App(f, a) => {
                path.push("app.fn".to_owned());
                collect(f, path, out);
                path.pop();
                path.push("app.arg".to_owned());
                collect(a, path, out);
                path.pop();
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                path.push("binder.type".to_owned());
                collect(ty, path, out);
                path.pop();
                path.push("binder.body".to_owned());
                collect(body, path, out);
                path.pop();
            }
            ExprKind::Let(_, ty, val, body, _) => {
                path.push("let.type".to_owned());
                collect(ty, path, out);
                path.pop();
                path.push("let.value".to_owned());
                collect(val, path, out);
                path.pop();
                path.push("let.body".to_owned());
                collect(body, path, out);
                path.pop();
            }
            ExprKind::Proj(_, _, inner) => {
                path.push("proj.target".to_owned());
                collect(inner, path, out);
                path.pop();
            }
            ExprKind::MData(_, inner) => {
                path.push("metadata".to_owned());
                collect(inner, path, out);
                path.pop();
            }
            ExprKind::Squash(inner) => {
                path.push("squash".to_owned());
                collect(inner, path, out);
                path.pop();
            }
            _ => {}
        }
    }

    let needle_text = needle.to_string();
    let mut candidates = Vec::new();
    stack_safe(|| collect(haystack, &mut Vec::new(), &mut candidates));
    candidates.sort_by(|a, b| {
        rewrite_candidate_score(&needle_text, &a.2)
            .cmp(&rewrite_candidate_score(&needle_text, &b.2))
            .then(a.0.cmp(&b.0))
            .then(a.1.cmp(&b.1))
    });
    candidates
        .into_iter()
        .filter(|(_, _, rendered)| rendered != &needle_text)
        .take(limit)
        .map(|(_, path, rendered)| RewriteCandidate::new(format_rewrite_path(&path), rendered))
        .collect()
}

fn format_rewrite_path(path: &str) -> String {
    if path.is_empty() {
        "root".to_owned()
    } else {
        format!("root.{path}")
    }
}

fn rewrite_candidate_score(needle: &str, candidate: &str) -> usize {
    if candidate.contains(needle) || needle.contains(candidate) {
        return 0;
    }
    levenshtein(needle, candidate)
}

fn levenshtein(a: &str, b: &str) -> usize {
    let a: Vec<char> = a.chars().collect();
    let b: Vec<char> = b.chars().collect();
    if a.is_empty() {
        return b.len();
    }
    if b.is_empty() {
        return a.len();
    }
    let mut prev: Vec<usize> = (0..=b.len()).collect();
    let mut curr = vec![0; b.len() + 1];
    for (i, ca) in a.iter().enumerate() {
        curr[0] = i + 1;
        for (j, cb) in b.iter().enumerate() {
            let substitution = prev[j] + usize::from(ca != cb);
            let insertion = curr[j] + 1;
            let deletion = prev[j + 1] + 1;
            curr[j + 1] = substitution.min(insertion).min(deletion);
        }
        std::mem::swap(&mut prev, &mut curr);
    }
    prev[b.len()]
}

/// Replace all occurrences of `from` with `to` in an expression
///
/// REQUIRES: `expr`, `from`, and `to` are well-formed expressions.
/// ENSURES: Every structural occurrence of `from` in `expr` is replaced by `to`.
/// ENSURES: Non-matching subexpressions are structurally preserved.
/// ENSURES: Runs under `stack_safe` to prevent stack overflow on deep terms.
pub(crate) fn replace_expr(expr: &Expr, from: &Expr, to: &Expr) -> Expr {
    stack_safe(|| {
        if expr == from {
            return to.clone();
        }
        match expr.kind() {
            ExprKind::App(f, a) => Expr::app(replace_expr(f, from, to), replace_expr(a, from, to)),
            ExprKind::Lam(bi, ty, body) => Expr::lam(
                *bi,
                replace_expr(ty, from, to),
                replace_expr(body, from, to),
            ),
            ExprKind::Pi(bi, ty, body) => Expr::pi(
                *bi,
                replace_expr(ty, from, to),
                replace_expr(body, from, to),
            ),
            ExprKind::Let(name, ty, val, body, non_dep) => Expr::let_named(
                name.clone(),
                replace_expr(ty, from, to),
                replace_expr(val, from, to),
                replace_expr(body, from, to),
                *non_dep,
            ),
            ExprKind::Proj(name, idx, inner) => {
                Expr::proj(name.clone(), *idx, replace_expr(inner, from, to))
            }
            ExprKind::MData(md, inner) => Expr::mdata(md.clone(), replace_expr(inner, from, to)),
            ExprKind::Squash(inner) => {
                Expr::from_kind(ExprKind::Squash(Arc::new(replace_expr(inner, from, to))))
            }
            _ => expr.clone(),
        }
    })
}

/// Abstract over occurrences of `term` in `expr`, creating a lambda abstraction
///
/// REQUIRES: `expr` and `term` are well-formed expressions.
/// ENSURES: Every structural occurrence of `term` in `expr` is replaced by
///   `BVar(depth)` at the appropriate de Bruijn depth.
/// ENSURES: Existing `BVar(i)` where `i >= depth` are shifted up by 1.
/// ENSURES: Binder depth increments correctly through Lam/Pi/Let bodies.
pub(crate) fn abstract_over(expr: &Expr, term: &Expr) -> Expr {
    super::super::bvar_ops::abstract_bvar(expr, term, 0)
}

/// Locate the first subterm of `haystack` that is definitionally equal to
/// `needle` but does **not** occur syntactically (so `contains_expr` already
/// failed). Returns the *surface* (un-reduced) subterm so a subsequent
/// `replace_expr` / `abstract_over` operates on the haystack's actual syntax.
///
/// This is the shared def-eq fallback behind both `rw`'s occurrence selection
/// (`rewrite.rs::find_defeq_subterm`, `ProofState`-backed def-eq) and the
/// term-level `▸` elaborator's `kabstract` approximation
/// (`infer/elab_subst.rs`, `ElabCtx`-backed def-eq). The definitional-equality
/// oracle is supplied by the caller so the walk itself stays a pure expression
/// helper.
///
/// # Soundness
/// Selecting a def-eq subterm only changes *which* occurrence is abstracted or
/// rewritten. Every caller's resulting proof/cast term is still kernel
/// re-checked (its type `motive needle` must be def-eq to the target, which is
/// `motive selected`).
///
/// # Performance
/// The expensive `is_def_eq` check is gated behind a cheap head-symbol
/// pre-filter: a candidate is only compared when its application head is the
/// *same* head constant as `needle` (so `Nat.testBit … = Nat.testBit …`) or
/// when either head is a hetero-op typeclass projection whose whnf could
/// expose the other (`@HAdd.hAdd … Nat.add n 0` vs `Nat.add n 0`, in both
/// directions). Bare atoms (fvars, sorts, literals) are never def-eq-probed.
/// Traversal is pre-order and stops at the first match.
pub(crate) fn find_defeq_subterm_with(
    haystack: &Expr,
    needle: &Expr,
    is_def_eq: &mut dyn FnMut(&Expr, &Expr) -> bool,
) -> Option<Expr> {
    // Only worth probing structured (application/projection-headed) needles —
    // a bare fvar/const/literal that is not syntactically present will not be
    // def-eq to a *distinct* surface subterm in any way a caller should
    // silently exploit, and probing every leaf would be both slow and
    // over-matching.
    if !matches!(needle.kind(), ExprKind::App(..) | ExprKind::Proj(..)) {
        return None;
    }
    let needle_head = needle.get_app_fn();
    let needle_head_is_const = matches!(needle_head.kind(), ExprKind::Const(..));

    fn candidate_worth_probing(
        candidate: &Expr,
        needle_head: &Expr,
        needle_head_is_const: bool,
    ) -> bool {
        // Same shape: both applications (the typical `f a … ≟ f a' …` case).
        if !matches!(candidate.kind(), ExprKind::App(..) | ExprKind::Proj(..)) {
            return false;
        }
        if !needle_head_is_const {
            // Without a const head to key on we cannot cheaply pre-filter; skip
            // to avoid indiscriminate whole-target def-eq probing.
            return false;
        }
        // Head-keyed gate: only spend a kernel `is_def_eq` on a candidate whose
        // application head is the *same* const as the needle's head. The cases
        // to recover share the outer head and differ only in a nested,
        // def-eq-but-not-syntactic argument:
        //   needle  = Nat.testBit (Nat.land m n) i
        //   surface = Nat.testBit (m &&& n) i   -- HAnd.hAnd … Nat.land m n
        //   surface = Nat.testBit (myAnd m n) i -- reducible `def myAnd … Nat.land`
        // Keying on the shared head keeps us from probing unrelated subterms
        // (e.g. the enclosing `@Eq Bool …`) and bounds the def-eq work.
        let (ExprKind::Const(cand_name, _), ExprKind::Const(needle_name, _)) =
            (candidate.get_app_fn().kind(), needle_head.kind())
        else {
            return false;
        };
        // Same head const: the common nested-arg case.
        if cand_name == needle_name {
            return true;
        }
        // Typeclass-projection bridge (target-side projection): a target
        // subterm headed by a hetero-op projection (`@HAdd.hAdd … Nat.add n 0`)
        // is def-eq to an op-headed needle (`Nat.add n 0`) coming from a
        // `Nat.*` lemma's LHS. Probe these so an env-lemma rw matches an
        // `n + 0`-style goal.
        if is_hetero_op_projection(cand_name) {
            return true;
        }
        // Mirror bridge (needle-side projection): the needle is the projection
        // (`@HAdd.hAdd … Nat.add 0 k`, e.g. a local hyp `ih` whose LHS is
        // written with `+`) while the target subterm is the concrete op
        // (`Nat.add 0 k`, left behind by an earlier `Nat.add_succ` rewrite).
        // Probe so the match works across the projection WHNF in either
        // direction. `is_def_eq(candidate, needle)` then bridges the
        // projection; `walk` returns the SURFACE candidate (the concrete
        // `Nat.add 0 k`), which the caller replaces syntactically. The result
        // stays kernel-checked, so an over-eager match is rejected downstream.
        is_hetero_op_projection(needle_name)
    }

    fn walk(
        expr: &Expr,
        needle: &Expr,
        needle_head: &Expr,
        needle_head_is_const: bool,
        is_def_eq: &mut dyn FnMut(&Expr, &Expr) -> bool,
    ) -> Option<Expr> {
        if candidate_worth_probing(expr, needle_head, needle_head_is_const)
            && is_def_eq(expr, needle)
        {
            return Some(expr.clone());
        }
        match expr.kind() {
            ExprKind::App(f, a) => walk(f, needle, needle_head, needle_head_is_const, is_def_eq)
                .or_else(|| walk(a, needle, needle_head, needle_head_is_const, is_def_eq)),
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                walk(ty, needle, needle_head, needle_head_is_const, is_def_eq)
                    .or_else(|| walk(body, needle, needle_head, needle_head_is_const, is_def_eq))
            }
            ExprKind::Let(_, ty, val, body, _) => {
                walk(ty, needle, needle_head, needle_head_is_const, is_def_eq)
                    .or_else(|| walk(val, needle, needle_head, needle_head_is_const, is_def_eq))
                    .or_else(|| walk(body, needle, needle_head, needle_head_is_const, is_def_eq))
            }
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
                walk(inner, needle, needle_head, needle_head_is_const, is_def_eq)
            }
            _ => None,
        }
    }

    walk(
        haystack,
        needle,
        needle_head,
        needle_head_is_const,
        is_def_eq,
    )
}

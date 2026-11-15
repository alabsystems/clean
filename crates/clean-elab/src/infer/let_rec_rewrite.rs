// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Reading lifted helpers back off a finished term (`super` module docs).

use std::collections::{HashMap, HashSet};

use clean_kernel::{BinderInfo, Expr, ExprKind, Level, Name};

/// `(fun (x : ty) => x) val` — the closed type and value of an auxiliary, in
/// a form every pass treats as an ordinary (well-typed) term.
pub(super) fn ascribe_closed(ty: Expr, val: Expr) -> Expr {
    Expr::app(Expr::lam(BinderInfo::Default, ty, Expr::bvar(0)), val)
}

/// Read back [`ascribe_closed`] applied to its captured arguments:
/// `Some((ty, val, args))`, borrowed from `value`.
pub(super) fn read_lifted_value(value: &Expr) -> Option<(&Expr, &Expr, Vec<&Expr>)> {
    let mut args: Vec<&Expr> = Vec::new();
    let mut head = value;
    loop {
        let ExprKind::App(f, a) = head.kind() else {
            return None;
        };
        if let ExprKind::Lam(_, ty, body) = f.kind() {
            if matches!(body.kind(), ExprKind::BVar(0)) {
                args.reverse();
                return Some((ty.as_ref(), a.as_ref(), args));
            }
        }
        args.push(a.as_ref());
        head = f.as_ref();
    }
}

/// Replaces each recognisable lifted-helper `let` by applications of the
/// helper's constant, collecting the helpers (dependencies first).
///
/// Rewriting a node does not depend on the binder depth it sits at (the
/// replacement's loose variables are the captured arguments, which
/// `instantiate` lifts correctly), so results are memoized by node address.
/// Every key is a node of the tree being rewritten, which outlives the walk,
/// so an address is never reused for a different node: shared subterms are
/// rewritten once, as a DAG, not once per path.
pub(super) struct LiftRewriter<'a> {
    /// The auxiliary names the declaration lifted.
    pub(super) names: &'a HashSet<Name>,
    /// The declaration's universe parameters, as levels.
    pub(super) us: &'a [Level],
    /// `(name, closed type, closed value)` in registration order.
    pub(super) found: Vec<(Name, Expr, Expr)>,
    /// The closed value registered under each name found so far.
    pub(super) seen: HashMap<Name, Expr>,
    pub(super) memo: HashMap<usize, Expr>,
    /// Names bound by two helpers with different values.
    pub(super) conflicts: Vec<Name>,
    /// Names whose binding stayed inline (not in recognisable lifted form).
    pub(super) inline: HashSet<Name>,
}

impl LiftRewriter<'_> {
    pub(super) fn rewrite(&mut self, e: &Expr) -> Expr {
        let key = e as *const Expr as usize;
        if let Some(done) = self.memo.get(&key) {
            return done.clone();
        }
        let out = crate::stack_safe(|| self.rewrite_node(e));
        self.memo.insert(key, out.clone());
        out
    }

    /// The marker `let` named `name` with `value` and `body`, rewritten — or
    /// `None` when it is not (or no longer) in recognisable lifted form.
    fn rewrite_marker(&mut self, name: &Name, value: &Expr, body: &Expr) -> Option<Expr> {
        if !self.names.contains(name) {
            return None;
        }
        let (closed_ty, closed_val, args) = read_lifted_value(value)?;
        // The helper's own value may use earlier helpers.
        let closed_val = self.rewrite(closed_val);
        match self.seen.get(name) {
            Some(prev) if prev != &closed_val => {
                // A second helper under the name: Lean refuses it.
                if !self.conflicts.contains(name) {
                    self.conflicts.push(name.clone());
                }
                return None;
            }
            Some(_) => {}
            None => {
                self.seen.insert(name.clone(), closed_val.clone());
                let closed_ty = self.rewrite(closed_ty);
                self.found.push((name.clone(), closed_ty, closed_val));
            }
        }
        let args: Vec<Expr> = args.into_iter().map(|a| self.rewrite(a)).collect();
        let use_term = Expr::apps(Expr::const_(name.clone(), self.us.to_vec()), args);
        Some(self.rewrite(body).instantiate(&use_term))
    }

    fn rewrite_node(&mut self, e: &Expr) -> Expr {
        match e.kind() {
            ExprKind::Let(name, ty, value, body, non_dep) => {
                if let Some(done) = self.rewrite_marker(name, value, body) {
                    return done;
                }
                if self.names.contains(name) {
                    self.inline.insert(name.clone());
                }
                Expr::let_named(
                    name.clone(),
                    self.rewrite(ty),
                    self.rewrite(value),
                    self.rewrite(body),
                    *non_dep,
                )
            }
            ExprKind::App(f, a) => Expr::app(self.rewrite(f), self.rewrite(a)),
            ExprKind::Lam(bd, ty, body) => Expr::lam(*bd, self.rewrite(ty), self.rewrite(body)),
            ExprKind::Pi(bd, ty, body) => Expr::pi(*bd, self.rewrite(ty), self.rewrite(body)),
            ExprKind::MData(m, inner) => Expr::mdata(m.clone(), self.rewrite(inner)),
            ExprKind::Proj(s, i, inner) => Expr::proj(s.clone(), *i, self.rewrite(inner)),
            // Leaves, and the extension forms no lifted helper is bound in.
            _ => e.clone(),
        }
    }
}

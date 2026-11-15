// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Demand-driven kernel `LocalContext` for `ElabCtx::make_tc`.
//!
//! MEASURED, NOT SPECULATIVE. With the full-context cache of
//! `local_ctx_cache.rs` in place, the `Mathlib/Logic/Basic.lean` profile
//! still put 75–99% of instance resolution in rebuilding the context: the
//! hot loop (`resolve_instance_with_depth` → `ElabCtx::whnf` on the goal)
//! runs once per candidate, and every candidate mints fresh universe
//! parameters / metavariables and unifies — so the generations move between
//! consecutive `whnf` calls and the O(|locals| + |metas|) rebuild is paid
//! on every one of them, while the kernel's own `whnf_impl` stayed at 0.0%.
//!
//! The kernel can only ever look up a free variable that occurs in the
//! expressions it is given, in the (instantiated) types and let-values of
//! the declarations it looks up, or in a closed constant it unfolds — the
//! cross-call `TcCaches` are keyed by expressions it is re-given, and the
//! binder locals it pushes itself never escape. So a context containing
//! exactly the free-variable CLOSURE of the call's input expressions is
//! observationally identical to the full one, and its cost is proportional
//! to what the call can touch instead of to everything the declaration has
//! ever created. A per-generation memo of instantiated declarations keeps
//! repeated calls on unchanged state from re-instantiating the same entries.
//!
//! Fail-closed: a free variable the builder cannot find (neither a local
//! nor a metavariable) is simply absent — exactly as it was absent from the
//! full context — and the kernel reports it as before. Debug builds audit
//! every context: each emitted declaration is re-instantiated from scratch
//! and compared (a stale memo entry = a missed generation bump), and the
//! emitted set is checked to be closed under the free variables of its own
//! types and values.

use super::ElabCtx;
use crate::unify::{push_expr_children, MetaState};
use clean_kernel::{BinderInfo, Expr, ExprKind, FVarId, LocalContext, LocalDecl, Name};
use std::collections::{HashMap, HashSet};

/// Instantiated declarations, valid for exactly one generation pair.
#[derive(Default)]
pub(crate) struct DeclMemo {
    metas_generation: u64,
    locals_generation: u64,
    /// `None` records "not a local and not a metavariable" so an unknown
    /// id is not re-searched on every call either.
    decls: HashMap<FVarId, Option<LocalDecl>>,
}

/// Push every free variable of `expr` not yet in `seen` onto `out`.
///
/// DAG-aware (pointer-visited) and pruned by the O(1) `has_fvar_quick`
/// flag, so a large shared proof term costs its distinct fvar-bearing
/// nodes, not its tree size.
fn collect_fvars(expr: &Expr, seen: &mut HashSet<FVarId>, out: &mut Vec<FVarId>) {
    let mut visited: HashSet<*const Expr> = HashSet::new();
    let mut stack: Vec<&Expr> = vec![expr];
    while let Some(e) = stack.pop() {
        if !e.has_fvar_quick() {
            continue;
        }
        if !visited.insert(e as *const Expr) {
            continue;
        }
        if let ExprKind::FVar(id) = e.kind() {
            if seen.insert(*id) {
                out.push(*id);
            }
        }
        push_expr_children(e, &mut stack);
    }
}

impl ElabCtx<'_> {
    /// Instantiate one declaration from scratch: a local (let-bound ones with
    /// their value) or a metavariable. `None` if `id` is neither.
    fn instantiate_decl(&self, id: FVarId) -> Option<LocalDecl> {
        if let Some(meta_id) = MetaState::from_fvar(id) {
            let meta = self.metas.get(meta_id)?;
            let ty = self.metas.instantiate(&meta.ty);
            let ty = self.metas.instantiate_levels(&ty);
            return Some(LocalDecl {
                id,
                name: Name::from_string(&format!("?m{}", meta_id.0)),
                type_: ty,
                value: None,
                bi: BinderInfo::Implicit.into(),
            });
        }
        let (name, _, ty) = self.locals.iter().rev().find(|(_, fvar, _)| *fvar == id)?;
        let ty = self.metas.instantiate(ty);
        let ty = self.metas.instantiate_levels(&ty);
        let value = self.locals.reduction_value(id).map(|value| {
            let value = self.metas.instantiate(value);
            self.metas.instantiate_levels(&value)
        });
        Some(LocalDecl {
            id,
            name: name.name().clone(),
            type_: ty,
            value,
            bi: self.locals.binder_info(id),
        })
    }

    /// The kernel context for a call whose inputs are `roots`: the
    /// free-variable closure of `roots` through instantiated types and
    /// let-values, locals before metavariables, each in id order.
    pub(crate) fn demand_local_ctx(&self, roots: &[&Expr]) -> LocalContext {
        let metas_generation = self.metas.generation();
        let locals_generation = self.locals.generation();
        let mut memo = self.decl_memo.borrow_mut();
        if memo.metas_generation != metas_generation || memo.locals_generation != locals_generation
        {
            memo.decls.clear();
            memo.metas_generation = metas_generation;
            memo.locals_generation = locals_generation;
        }

        let mut seen: HashSet<FVarId> = HashSet::new();
        let mut pending: Vec<FVarId> = Vec::new();
        for root in roots {
            collect_fvars(root, &mut seen, &mut pending);
        }
        let mut decls: Vec<LocalDecl> = Vec::new();
        while let Some(id) = pending.pop() {
            let decl = match memo.decls.get(&id) {
                Some(decl) => decl.clone(),
                None => {
                    let decl = self.instantiate_decl(id);
                    memo.decls.insert(id, decl.clone());
                    decl
                }
            };
            let Some(decl) = decl else {
                continue;
            };
            collect_fvars(&decl.type_, &mut seen, &mut pending);
            if let Some(value) = &decl.value {
                collect_fvars(value, &mut seen, &mut pending);
            }
            decls.push(decl);
        }
        drop(memo);

        // Locals first (they were pushed in id order), then metavariables.
        decls.sort_by_key(|decl| (MetaState::from_fvar(decl.id).is_some(), decl.id));
        #[cfg(debug_assertions)]
        self.audit_demand_local_ctx(&decls, &seen);

        let mut ctx = LocalContext::new();
        // Reserve the elaborator's own FVarId range BEFORE anything is pushed.
        // A full context registered every local, so the kernel's fresh-binder
        // paths (`push`'s `next_id`, `push_low_local`'s low cursor) could not
        // mint an id the elaborator had already bound; a demand-driven context
        // holds only a SUBSET, so without this floor a binder local opened
        // inside `whnf` / `infer_type` could alias a local that exists in the
        // elaborator but was not reachable from this call's roots.
        ctx.reserve_fvar_floor(self.next_fvar);
        for decl in decls {
            match decl.value {
                Some(value) => ctx.push_let_with_id(decl.id, decl.name, decl.type_, value),
                None => ctx.push_with_id(decl.id, decl.name, decl.type_, decl.bi),
            }
        }
        ctx
    }

    /// Debug-build audit of one demand-driven context (see the module doc).
    #[cfg(debug_assertions)]
    fn audit_demand_local_ctx(&self, decls: &[LocalDecl], seen: &HashSet<FVarId>) {
        let emitted: HashSet<FVarId> = decls.iter().map(|decl| decl.id).collect();
        for decl in decls {
            let Some(fresh) = self.instantiate_decl(decl.id) else {
                panic!(
                    "demand-driven local context is STALE: fvar {:?} ({}) no longer exists; a \
                     mutation site is missing its generation bump",
                    decl.id, decl.name
                );
            };
            assert!(
                fresh.name == decl.name
                    && fresh.type_ == decl.type_
                    && fresh.value == decl.value
                    && fresh.bi == decl.bi,
                "demand-driven local context is STALE for fvar {:?} ({}): memoised {:?} / {:?} vs \
                 fresh {:?} / {:?}; a mutation site is missing its generation bump (see \
                 crates/clean-elab/src/infer/demand_local_ctx.rs)",
                decl.id,
                decl.name,
                decl.type_,
                decl.value,
                fresh.type_,
                fresh.value
            );
            let mut inner_seen: HashSet<FVarId> = HashSet::new();
            let mut inner: Vec<FVarId> = Vec::new();
            collect_fvars(&decl.type_, &mut inner_seen, &mut inner);
            if let Some(value) = &decl.value {
                collect_fvars(value, &mut inner_seen, &mut inner);
            }
            for id in inner {
                assert!(
                    seen.contains(&id),
                    "demand-driven local context is NOT CLOSED: fvar {id:?} occurs in the \
                     declaration of {:?} ({}) but was never visited",
                    decl.id,
                    decl.name
                );
                assert!(
                    emitted.contains(&id) || self.instantiate_decl(id).is_none(),
                    "demand-driven local context is NOT CLOSED: fvar {id:?} occurs in the \
                     declaration of {:?} ({}) and is known but was not emitted",
                    decl.id,
                    decl.name
                );
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::infer::ElabCtx;
    use crate::unify::MetaState;
    use clean_kernel::{Environment, Expr};

    #[test]
    fn test_demand_local_ctx_is_the_fvar_closure_of_the_roots() {
        let env = Environment::new();
        let mut ctx = ElabCtx::new(&env);
        // a : Prop,  m : ?t  where ?t : Type,  b : m  (b's type mentions the meta)
        let a = ctx.push_local(clean_parser::SurfaceName::generated_path("a"), Expr::prop());
        let t = ctx.metas.fresh(Expr::type_());
        let t_fvar = MetaState::to_fvar(t);
        let m = ctx.push_local(
            clean_parser::SurfaceName::generated_path("m"),
            Expr::fvar(t_fvar),
        );
        let b = ctx.push_local(
            clean_parser::SurfaceName::generated_path("b"),
            Expr::fvar(m),
        );
        let unrelated =
            ctx.push_local(clean_parser::SurfaceName::generated_path("u"), Expr::prop());

        let only_b = ctx.demand_local_ctx(&[&Expr::fvar(b)]);
        assert!(only_b.get(b).is_some());
        assert!(only_b.get(m).is_some(), "b's type mentions m");
        assert!(only_b.get(t_fvar).is_some(), "m's type mentions ?t");
        assert!(only_b.get(a).is_none(), "a is unreachable from b");
        assert!(only_b.get(unrelated).is_none());
        assert_eq!(only_b.len(), 3);

        let closed = ctx.demand_local_ctx(&[&Expr::prop()]);
        assert!(closed.is_empty(), "a closed term needs no declarations");

        // Assigning ?t := Nat-ish (here: Prop) must show in m's emitted type.
        assert!(ctx.metas.assign(t, Expr::prop()));
        let after = ctx.demand_local_ctx(&[&Expr::fvar(m)]);
        assert_eq!(after.get(m).map(|d| d.type_.clone()), Some(Expr::prop()));
        assert!(
            after.get(t_fvar).is_none(),
            "an instantiated-away meta is not reachable"
        );
        let _ = a;
    }

    #[test]
    fn test_demand_local_ctx_reserves_the_elaborators_fvar_range() {
        // The partial context must not let the kernel's fresh-binder paths
        // mint an id the elaborator has already bound to an unreachable local.
        let env = Environment::new();
        let mut ctx = ElabCtx::new(&env);
        let reachable =
            ctx.push_local(clean_parser::SurfaceName::generated_path("r"), Expr::prop());
        let mut hidden = Vec::new();
        for i in 0..8 {
            hidden.push(ctx.push_local(
                clean_parser::SurfaceName::from_name(
                    clean_kernel::Name::anon().str(format!("h{i}")),
                ),
                Expr::prop(),
            ));
        }
        let mut demand = ctx.demand_local_ctx(&[&Expr::fvar(reachable)]);
        assert_eq!(demand.len(), 1, "only the reachable local is emitted");
        for _ in 0..4 {
            let fresh = demand.push(
                clean_kernel::Name::from_string("k"),
                Expr::prop(),
                clean_kernel::BinderInfo::Default,
            );
            assert!(
                !hidden.contains(&fresh) && fresh != reachable,
                "kernel binder {fresh:?} aliases an elaborator local"
            );
        }
        for _ in 0..4 {
            let fresh = demand.push_low_local(
                clean_kernel::Name::from_string("k"),
                Expr::prop(),
                clean_kernel::BinderInfo::Default,
            );
            assert!(
                !hidden.contains(&fresh) && fresh != reachable,
                "kernel low binder {fresh:?} aliases an elaborator local"
            );
        }
    }

    #[test]
    fn test_demand_local_ctx_emits_let_values_and_their_closure() {
        let env = Environment::new();
        let mut ctx = ElabCtx::new(&env);
        let a = ctx.push_local(clean_parser::SurfaceName::generated_path("a"), Expr::prop());
        let x = ctx.fresh_fvar();
        ctx.push_local_let_with_fvar(
            clean_parser::SurfaceName::generated_path("x"),
            x,
            Expr::prop(),
            Expr::fvar(a),
        );
        let c = ctx.demand_local_ctx(&[&Expr::fvar(x)]);
        let decl = c.get(x).expect("let-local x is emitted");
        assert_eq!(decl.value, Some(Expr::fvar(a)));
        assert!(c.get(a).is_some(), "the let value mentions a");
    }
}

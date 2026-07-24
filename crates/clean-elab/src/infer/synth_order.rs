// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Default synthesization-order computation for typeclass instances.
//!
//! Port of Lean 4's `computeSynthOrder`
//! (`Lean/Meta/Instances.lean:145-229`, v4.30.0-rc2): given an instance's
//! type, compute the order in which its `[inst]` binders should be
//! synthesized so that every sub-goal is attempted only after the
//! metavariables occurring in its non-(semi-)out-param arguments have been
//! determined — either by unification of the instance conclusion with the
//! goal, or by the solution of an earlier sub-goal.
//!
//! Lean's algorithm, restated over the instance type's Pi telescope:
//!
//! 1. Create a metavariable per telescope binder
//!    (`forallMetaTelescopeReducing`).
//! 2. Mark as *determined* every metavariable occurring in a
//!    non-(semi-)out-param argument of the conclusion (these are fixed by
//!    the goal before sub-goal synthesis starts), transitively including
//!    the metavariables in the *types* of the marked ones
//!    (`assignMVarsIn` recurses through `inferType`).
//! 3. Greedy loop over the not-yet-scheduled `instImplicit` binders: pick
//!    the first whose type — after stripping its own leading Pis — has all
//!    non-(semi-)out-param arguments free of undetermined metavariables
//!    ("ready"); when none is ready Lean errors at declaration time under
//!    `synthInstance.checkSynthOrder` and otherwise falls back to the first
//!    remaining one. Scheduling a sub-goal determines every metavariable it
//!    mentions (its synthesized solution pins them).
//!
//! This port is *syntactic*: binder references are de Bruijn occurrences in
//! the telescope (Lean's mvar-occurrence check on the meta-telescoped type),
//! and the `forallTelescopeReducing`/`whnf` reduction steps are approximated
//! by structural traversal (a `def`-alias conclusion that only whnf would
//! expose is not resolved here — acceptable for the hand-registered-instance
//! lane this default serves; imported instances carry Lean's own persisted
//! `synthOrder`, decoded from the `.olean`). Out-param positions come from
//! the elaborator's class table (Lean reads `getOutParamPositions?` plus
//! `semiOutParam` markers; Clean's `ClassInfo` carries both sets).
//!
//! Never panics; on any unrecognized shape the affected sub-goal simply
//! falls back to declaration order (Lean's `checkSynthOrder := false`
//! behavior).

use crate::instances::{extract_class_app, InstanceTable};
use clean_kernel::{BinderInfo, Expr, ExprKind};

/// Compute the default synthesization order for an instance type.
///
/// Returns the telescope binder indices of the instance-implicit binders in
/// the order their sub-goals should be synthesized. Mirrors
/// `computeSynthOrder` (`Lean/Meta/Instances.lean:145-229`); see the module
/// docs for the semantics and the documented syntactic approximations.
pub(super) fn default_synth_order(instances: &InstanceTable, inst_type: &Expr) -> Vec<usize> {
    // Walk the Pi telescope: binders[i] = (binder info, domain type).
    // The domain of binder i is expressed under i enclosing telescope
    // binders (BVar(k) at local depth d with k >= d refers to telescope
    // binder i - 1 - (k - d)).
    let mut binders: Vec<(BinderInfo, &Expr)> = Vec::new();
    let mut ty = inst_type;
    while let ExprKind::Pi(bi, dom, body) = ty.kind() {
        binders.push((bi.info, dom));
        ty = body;
    }
    let conclusion = ty;
    let n = binders.len();
    if n == 0 {
        return Vec::new();
    }

    // Transitively mark binder `b` (and the binders its TYPE references) as
    // determined — Lean's `assignMVarsIn` recursing through `inferType`.
    let determine = |determined: &mut Vec<bool>, seeds: Vec<usize>| {
        let mut work = seeds;
        while let Some(b) = work.pop() {
            if b >= n || determined[b] {
                continue;
            }
            determined[b] = true;
            work.extend(binder_refs(binders[b].1, b));
        }
    };

    // (Semi-)out-param positions of a class application, from the class
    // table. Lean: `getSemiOutParamPositionsOf` = outParams ∪ semiOutParams.
    let out_positions = |class_ty: &Expr| -> Vec<usize> {
        extract_class_app(class_ty)
            .and_then(|(name, _)| instances.get_class(&name))
            .map(|info| {
                let mut pos = info.out_params.clone();
                pos.extend(info.semi_out_params.iter().copied());
                pos
            })
            .unwrap_or_default()
    };

    // Step 2: metavariables in non-out-params of the conclusion are
    // determined by the goal before sub-goal synthesis starts.
    let mut determined = vec![false; n];
    if let Some((_, concl_args)) = extract_class_app(conclusion) {
        let concl_out = out_positions(conclusion);
        for (idx, arg) in concl_args.iter().enumerate() {
            if !concl_out.contains(&idx) {
                determine(&mut determined, binder_refs_at_depth(arg, n, 0));
            }
        }
    } else {
        // Non-class-app conclusion (defensive): treat every binder the
        // conclusion references as determined.
        determine(&mut determined, binder_refs_at_depth(conclusion, n, 0));
    }

    // Step 3: greedy scheduling of the instImplicit binders.
    let mut to_synth: Vec<usize> = (0..n)
        .filter(|&i| binders[i].0 == BinderInfo::InstImplicit)
        .collect();
    let mut synthed = Vec::with_capacity(to_synth.len());
    while !to_synth.is_empty() {
        let ready_pos = to_synth
            .iter()
            .position(|&i| subgoal_ready(binders[i].1, i, &determined, &out_positions))
            // No ready sub-goal: Lean errors at declaration time when
            // `synthInstance.checkSynthOrder` is set and otherwise picks the
            // first remaining one; the resolver must never fail here, so
            // take the fallback.
            .unwrap_or(0);
        let next = to_synth.remove(ready_pos);
        synthed.push(next);
        // The scheduled sub-goal's solution determines every binder its
        // type references, plus the binder itself.
        let mut seeds = binder_refs(binders[next].1, next);
        seeds.push(next);
        determine(&mut determined, seeds);
    }
    synthed
}

/// Whether sub-goal `binder_idx` (domain type `sub_ty`, expressed under
/// `binder_idx` telescope binders) is ready: after stripping its own leading
/// Pis, every non-(semi-)out-param argument of its class application
/// references only determined telescope binders.
fn subgoal_ready(
    sub_ty: &Expr,
    binder_idx: usize,
    determined: &[bool],
    out_positions: &impl Fn(&Expr) -> Vec<usize>,
) -> bool {
    // Strip the sub-goal's own leading Pis (Lean: `forallTelescopeReducing`);
    // each stripped binder increases the local depth, so its own bound
    // variables are never mistaken for telescope references.
    let mut local_depth = 0usize;
    let mut body = sub_ty;
    while let ExprKind::Pi(_, _, inner) = body.kind() {
        local_depth += 1;
        body = inner;
    }
    let Some((_, args)) = extract_class_app(body) else {
        // Not a class application (defensive): ready iff it references no
        // undetermined binder at all.
        return binder_refs_at_depth(body, binder_idx, local_depth)
            .iter()
            .all(|&b| determined[b]);
    };
    let out = out_positions(body);
    args.iter().enumerate().all(|(idx, arg)| {
        out.contains(&idx)
            || binder_refs_at_depth(arg, binder_idx, local_depth)
                .iter()
                .all(|&b| determined[b])
    })
}

/// Telescope binder indices referenced by the domain type of binder
/// `binder_idx` (an expression under `binder_idx` telescope binders, at
/// local depth 0).
fn binder_refs(e: &Expr, binder_idx: usize) -> Vec<usize> {
    binder_refs_at_depth(e, binder_idx, 0)
}

/// Telescope binder indices referenced by `e`, where `e` sits under
/// `n_binders` telescope binders plus `local_depth` local (non-telescope)
/// binders. A `BVar(k)` at inner traversal depth `d` refers to telescope
/// binder `n_binders - 1 - (k - d - local_depth)` when
/// `k >= d + local_depth`; smaller indices are local bound variables.
fn binder_refs_at_depth(e: &Expr, n_binders: usize, local_depth: usize) -> Vec<usize> {
    fn walk(e: &Expr, depth: usize, n_binders: usize, local_depth: usize, out: &mut Vec<usize>) {
        crate::stack_safe(|| match e.kind() {
            ExprKind::BVar(k) => {
                let k = *k as usize;
                if k >= depth + local_depth {
                    let up = k - depth - local_depth;
                    if up < n_binders {
                        let idx = n_binders - 1 - up;
                        if !out.contains(&idx) {
                            out.push(idx);
                        }
                    }
                }
            }
            ExprKind::App(f, a) => {
                walk(f, depth, n_binders, local_depth, out);
                walk(a, depth, n_binders, local_depth, out);
            }
            ExprKind::Lam(_, dom, body) | ExprKind::Pi(_, dom, body) => {
                walk(dom, depth, n_binders, local_depth, out);
                walk(body, depth + 1, n_binders, local_depth, out);
            }
            ExprKind::Let(_, ty, val, body, _) => {
                walk(ty, depth, n_binders, local_depth, out);
                walk(val, depth, n_binders, local_depth, out);
                walk(body, depth + 1, n_binders, local_depth, out);
            }
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
                walk(inner, depth, n_binders, local_depth, out);
            }
            // Leaves and mode-extension nodes: no BVar payload relevant to
            // instance types (which are plain Pi/App/Const/Sort terms).
            _ => {}
        });
    }
    let mut out = Vec::new();
    walk(e, 0, n_binders, local_depth, &mut out);
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::Name;

    fn n(s: &str) -> Name {
        Name::from_string(s)
    }
    fn c(s: &str) -> Expr {
        Expr::const_(n(s), vec![])
    }
    fn pi(info: BinderInfo, dom: Expr, body: Expr) -> Expr {
        Expr::pi(info, dom, body)
    }
    fn app1(f: &str, a: Expr) -> Expr {
        Expr::app(c(f), a)
    }
    fn app3(f: &str, a: Expr, b: Expr, d: Expr) -> Expr {
        Expr::apps(c(f), [a, b, d])
    }

    /// `[Add α] [Zero α] : Foo α` → `[1, 2]` (Lean docstring example one:
    /// declaration order, both ready once α is pinned by the conclusion).
    #[test]
    fn test_default_synth_order_left_to_right_when_all_ready() {
        let mut table = InstanceTable::new();
        table.register_class(n("Foo"), 1, vec![]);
        table.register_class(n("Add"), 1, vec![]);
        table.register_class(n("Zero"), 1, vec![]);

        // {α : Sort} → [Add α] → [Zero α] → Foo α
        let ty = pi(
            BinderInfo::Implicit,
            Expr::sort(clean_kernel::Level::zero()),
            pi(
                BinderInfo::InstImplicit,
                app1("Add", Expr::bvar(0)),
                pi(
                    BinderInfo::InstImplicit,
                    app1("Zero", Expr::bvar(1)),
                    app1("Foo", Expr::bvar(2)),
                ),
            ),
        );
        assert_eq!(default_synth_order(&table, &ty), vec![1, 2]);
    }

    /// `[Mul A] [Mul B] [MulHomClass F A B] : FunLike F A B` → `[2, 0, 1]`
    /// (Lean docstring example two, `Lean/Meta/Instances.lean:130-133`:
    /// A and B are out-params of both FunLike and MulHomClass, so only the
    /// MulHomClass sub-goal is ready first; solving it determines A and B).
    #[test]
    fn test_default_synth_order_outparam_driven_reorder() {
        let mut table = InstanceTable::new();
        table.register_class(n("FunLike"), 3, vec![1, 2]);
        table.register_class(n("MulHomClass"), 3, vec![1, 2]);
        table.register_class(n("Mul"), 1, vec![]);

        // {F A B : Sort} → [Mul A] → [Mul B] → [MulHomClass F A B]
        // → FunLike F A B (binders 0=F, 1=A, 2=B, 3..5 = the inst binders).
        let sort = Expr::sort(clean_kernel::Level::zero());
        let ty = pi(
            BinderInfo::Implicit,
            sort.clone(),
            pi(
                BinderInfo::Implicit,
                sort.clone(),
                pi(
                    BinderInfo::Implicit,
                    sort,
                    pi(
                        BinderInfo::InstImplicit,
                        app1("Mul", Expr::bvar(1)), // Mul A
                        pi(
                            BinderInfo::InstImplicit,
                            app1("Mul", Expr::bvar(1)), // Mul B
                            pi(
                                BinderInfo::InstImplicit,
                                // MulHomClass F A B
                                app3("MulHomClass", Expr::bvar(4), Expr::bvar(3), Expr::bvar(2)),
                                // FunLike F A B
                                app3("FunLike", Expr::bvar(5), Expr::bvar(4), Expr::bvar(3)),
                            ),
                        ),
                    ),
                ),
            ),
        );
        assert_eq!(default_synth_order(&table, &ty), vec![5, 3, 4]);
    }

    /// The transitivity shape (`instMonadLiftTOfMonadLift`,
    /// `Init/Prelude.lean:3917`): `(m n o) → [MonadLift n o] →
    /// [MonadLiftT m n] → MonadLiftT m o` with `MonadLift`'s first param a
    /// `semiOutParam`. The conclusion pins m and o; `MonadLift n o` is ready
    /// because its only undetermined binder (n) sits in the semi-out
    /// position; solving it determines n for `MonadLiftT m n`.
    /// Lean persists exactly `[3, 4]` for this instance (verified against
    /// the v4.30.0-rc2 Init.Prelude olean).
    #[test]
    fn test_default_synth_order_monad_lift_transitivity_shape() {
        let mut table = InstanceTable::new();
        table.register_class_full(n("MonadLift"), 2, vec![], vec![0]);
        table.register_class(n("MonadLiftT"), 2, vec![]);

        let sort = Expr::sort(clean_kernel::Level::zero());
        // (m n o : Sort) → [MonadLift n o] → [MonadLiftT m n] → MonadLiftT m o
        let ty = pi(
            BinderInfo::Default,
            sort.clone(),
            pi(
                BinderInfo::Default,
                sort.clone(),
                pi(
                    BinderInfo::Default,
                    sort,
                    pi(
                        BinderInfo::InstImplicit,
                        Expr::apps(c("MonadLift"), [Expr::bvar(1), Expr::bvar(0)]),
                        pi(
                            BinderInfo::InstImplicit,
                            Expr::apps(c("MonadLiftT"), [Expr::bvar(3), Expr::bvar(2)]),
                            Expr::apps(c("MonadLiftT"), [Expr::bvar(4), Expr::bvar(2)]),
                        ),
                    ),
                ),
            ),
        );
        assert_eq!(default_synth_order(&table, &ty), vec![3, 4]);
    }

    /// Without the semiOutParam on MonadLift, neither sub-goal is ready
    /// (n is undetermined in both); the fallback must still schedule every
    /// sub-goal exactly once, in declaration order, without panicking.
    #[test]
    fn test_default_synth_order_no_ready_subgoal_falls_back_in_order() {
        let mut table = InstanceTable::new();
        table.register_class(n("MonadLift"), 2, vec![]);
        table.register_class(n("MonadLiftT"), 2, vec![]);

        let sort = Expr::sort(clean_kernel::Level::zero());
        let ty = pi(
            BinderInfo::Default,
            sort.clone(),
            pi(
                BinderInfo::Default,
                sort.clone(),
                pi(
                    BinderInfo::Default,
                    sort,
                    pi(
                        BinderInfo::InstImplicit,
                        Expr::apps(c("MonadLift"), [Expr::bvar(1), Expr::bvar(0)]),
                        pi(
                            BinderInfo::InstImplicit,
                            Expr::apps(c("MonadLiftT"), [Expr::bvar(3), Expr::bvar(2)]),
                            Expr::apps(c("MonadLiftT"), [Expr::bvar(4), Expr::bvar(2)]),
                        ),
                    ),
                ),
            ),
        );
        assert_eq!(default_synth_order(&table, &ty), vec![3, 4]);
    }

    /// No inst-implicit binders → empty order (matches Lean persisting `[]`
    /// for e.g. `ReaderT.instMonadLift`).
    #[test]
    fn test_default_synth_order_no_inst_binders_empty() {
        let mut table = InstanceTable::new();
        table.register_class(n("MonadLift"), 2, vec![]);
        let sort = Expr::sort(clean_kernel::Level::zero());
        let ty = pi(
            BinderInfo::Implicit,
            sort,
            Expr::apps(c("MonadLift"), [Expr::bvar(0), Expr::bvar(0)]),
        );
        assert_eq!(default_synth_order(&table, &ty), Vec::<usize>::new());
    }
}

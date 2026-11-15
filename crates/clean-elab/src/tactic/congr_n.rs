// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The `congr` tactic — a port of Lean's `MVarId.congrN`
//! (`Lean/Meta/Tactic/Congr.lean`) over the congr-simp theorem shape of
//! `mkCongrSimp?` (`Lean/Meta/CongrTheorems.lean`).
//!
//! `congr` never fails: on each goal it first tries to close it (`Eq.refl`,
//! `HEq.refl`, an assumption, after turning a homogeneous `HEq` into `Eq`),
//! then splits `f a₁ … aₙ = f b₁ … bₙ` into `aᵢ = bᵢ` for the arguments that
//! may differ, recursing to the given depth; a goal nothing applies to is left
//! as it was. Which arguments may differ is Lean's `getCongrSimpKinds`: an
//! argument the result type depends on is FIXED (must already agree), a proof
//! is a CAST (proof irrelevance), a `Decidable` instance whose proposition may
//! change is a SUBSINGLETON (closed by `Subsingleton.elim`), and an argument a
//! later non-cast argument depends on is FIXED.
//!
//! Lean applies a generated lemma; here the proof is built directly: the goal
//! `lhs = rhs` is generalised over the changed arguments `z⃗` and the proof
//! arguments `q⃗` of the right side, `Q z⃗ := ∀ q⃗, lhs = f c⃗`, proved at
//! `z⃗ := a⃗` by `fun q⃗ => Eq.refl lhs` (the `q⃗` agree with `lhs`'s own proofs
//! by proof irrelevance) and transported along each `eᵢ : aᵢ = bᵢ` with
//! `Eq.ndrec`. Only proofs depend on a changed argument (anything else would
//! have fixed it), so every intermediate `Q` is well-typed.
//!
//! Measured 2026-09-12: the previous `congr` built `congrArg` with one
//! universe level (the constant has two), so it failed even on `f a = f b`,
//! and on several arguments it closed the goal with a copy of itself;
//! `Unique.subtypeEq` (`fun ⟨x, hx⟩ ↦ by congr` on `⟨x, hx⟩ = default`) and
//! `Function.extend_def` (two `dite`s that differ only in the `Decidable`
//! instance) were among the rows it failed.

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, FVarId, Level};

use super::core::{Goal, ProofState, TacticError, TacticResult};
use crate::unify::MetaState;

/// Lean's depth when `congr` is written without one (`evalCongr`'s
/// `hugeDepth`).
pub(crate) const CONGR_DEFAULT_DEPTH: usize = 1_000_000;

/// Lean's `CongrArgKind`, restricted to the kinds a congr-simp theorem uses.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ArgKind {
    Fixed,
    Eq,
    Cast,
    SubsingletonInst,
}

/// The transparency a closing attempt runs at: Lean's `congrPre` runs at
/// `reducible` before splitting and again at `default` on goals it could not
/// split (`post`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Transparency {
    Reducible,
    Default,
}

/// What `getFunInfo` records about one parameter.
struct ParamInfo {
    is_prop: bool,
    is_inst: bool,
    is_dec_inst: bool,
    back_deps: Vec<usize>,
}

/// Run `congr` with the given depth on the current goal; the goals it leaves
/// replace it, in order.
///
/// REQUIRES: `state.goals` is non-empty.
/// ENSURES: every goal it closes is closed by a kernel-checked proof
///   (`close_goal`), and a goal no step applies to is left unchanged.
pub(crate) fn congr_n(state: &mut ProofState, depth: usize) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }
    let mut open = Vec::new();
    go(state, depth, &mut open)?;
    for goal in open.into_iter().rev() {
        state.goals.push_front(goal);
    }
    Ok(())
}

/// Process the FRONT goal: close it, split it (recursing on each piece), or
/// move it to `open`. Removes exactly that goal from the queue.
fn go(state: &mut ProofState, n: usize, open: &mut Vec<Goal>) -> TacticResult {
    if congr_pre(state, Transparency::Reducible) {
        return Ok(());
    }
    if n == 0 {
        return post(state, open);
    }
    match congr_core(state)? {
        Some(pieces) => {
            for _ in 0..pieces {
                crate::stack_safe(|| go(state, n - 1, open))?;
            }
            Ok(())
        }
        None => post(state, open),
    }
}

fn post(state: &mut ProofState, open: &mut Vec<Goal>) -> TacticResult {
    if congr_pre(state, Transparency::Default) {
        return Ok(());
    }
    let goal = state.goals.pop_front().ok_or(TacticError::NoGoals)?;
    open.push(goal);
    Ok(())
}

fn defeq(state: &ProofState, goal: &Goal, a: &Expr, b: &Expr, mode: Transparency) -> bool {
    match mode {
        Transparency::Reducible => state.is_def_eq_reducible(goal, a, b),
        Transparency::Default => state.is_def_eq(goal, a, b),
    }
}

fn const_app_args(e: &Expr, name: &str, arity: usize) -> Option<(Vec<Level>, Vec<Expr>)> {
    let ExprKind::Const(head, levels) = e.get_app_fn().kind() else {
        return None;
    };
    if head.to_string() != name {
        return None;
    }
    let args: Vec<Expr> = e.get_app_args().into_iter().cloned().collect();
    (args.len() == arity).then(|| (levels.to_vec(), args))
}

/// Lean's `congrPre`: turn a homogeneous `HEq` goal into `Eq`, then try
/// `Eq.refl`, `HEq.refl` and an assumption. `true` when the goal was closed.
fn congr_pre(state: &mut ProofState, mode: Transparency) -> bool {
    heq_to_eq(state, mode);
    let Some(goal) = state.current_goal().cloned() else {
        return false;
    };
    let target = state.metas.instantiate(&goal.target);
    if let Some((levels, args)) = const_app_args(&target, "Eq", 3) {
        if defeq(state, &goal, &args[1], &args[2], mode) {
            let refl = Expr::apps(
                Expr::const_(Name::from_string("Eq.refl"), levels),
                [args[0].clone(), args[1].clone()],
            );
            if state.close_goal(&goal, refl).is_ok() {
                return true;
            }
        }
    }
    if let Some((levels, args)) = const_app_args(&target, "HEq", 4) {
        if defeq(state, &goal, &args[0], &args[2], mode)
            && defeq(state, &goal, &args[1], &args[3], mode)
        {
            let refl = Expr::apps(
                Expr::const_(Name::from_string("HEq.refl"), levels),
                [args[0].clone(), args[1].clone()],
            );
            if state.close_goal(&goal, refl).is_ok() {
                return true;
            }
        }
    }
    for decl in goal.local_ctx.iter().rev() {
        let ty = state.metas.instantiate(&decl.ty);
        if defeq(state, &goal, &ty, &target, mode)
            && state.close_goal(&goal, Expr::fvar(decl.fvar)).is_ok()
        {
            return true;
        }
    }
    false
}

/// Lean's `MVarId.heqOfEq`: `HEq a b` whose two types agree becomes `a = b`
/// (closed by `heq_of_eq`). Leaves the goal alone otherwise.
fn heq_to_eq(state: &mut ProofState, mode: Transparency) {
    let Some(goal) = state.current_goal().cloned() else {
        return;
    };
    let target = state.metas.instantiate(&goal.target);
    let Some((levels, args)) = const_app_args(&target, "HEq", 4) else {
        return;
    };
    let heq_of_eq = Name::from_string("heq_of_eq");
    if state.env.get_const(&heq_of_eq).is_none() || !defeq(state, &goal, &args[0], &args[2], mode) {
        return;
    }
    let eq_ty = Expr::apps(
        Expr::const_(Name::from_string("Eq"), levels.clone()),
        [args[0].clone(), args[1].clone(), args[3].clone()],
    );
    let meta = state.fresh_meta_in_context(eq_ty.clone(), &goal.local_ctx);
    let proof = Expr::apps(
        Expr::const_(heq_of_eq, levels),
        [
            args[0].clone(),
            args[1].clone(),
            args[3].clone(),
            Expr::fvar(MetaState::to_fvar(meta)),
        ],
    );
    if state.close_goal(&goal, proof).is_ok() {
        state.goals.push_front(Goal {
            meta_id: meta,
            target: eq_ty,
            local_ctx: goal.local_ctx.clone(),
            tag: goal.tag.clone(),
            case_binders: goal.case_binders.clone(),
        });
    }
}

/// Lean's `congrCore` on the front goal: the congr-simp split, then the
/// implication split. `Some(k)` when the goal was replaced by `k` new goals
/// at the front; `None` (state unchanged) when neither applies.
fn congr_core(state: &mut ProofState) -> Result<Option<usize>, TacticError> {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = state.whnf(&goal, &state.metas.instantiate(&goal.target));
    let Some((levels, args)) = const_app_args(&target, "Eq", 3) else {
        return Ok(None);
    };
    let (ty, lhs, rhs) = (&args[0], &args[1], &args[2]);
    let eq_level = levels.first().cloned().unwrap_or_else(Level::zero);
    if let Some(k) = congr_simp(state, &goal, &eq_level, ty, lhs, rhs)? {
        return Ok(Some(k));
    }
    congr_implies(state, &goal, &eq_level, ty, lhs, rhs)
}

fn sort_level(state: &ProofState, goal: &Goal, ty: &Expr) -> Option<Level> {
    let sort = state.whnf(goal, &state.infer_type(goal, ty).ok()?);
    match sort.kind() {
        ExprKind::Sort(l) => Some(l.clone()),
        _ => None,
    }
}

/// The parameter types of `f` applied to `args`, one per argument.
fn telescope_types(state: &ProofState, goal: &Goal, f: &Expr, args: &[Expr]) -> Option<Vec<Expr>> {
    let mut ty = state.whnf(goal, &state.infer_type(goal, f).ok()?);
    let mut out = Vec::with_capacity(args.len());
    for arg in args {
        if !matches!(ty.kind(), ExprKind::Pi(..)) {
            ty = state.whnf(goal, &ty);
        }
        let ExprKind::Pi(_, dom, body) = ty.kind() else {
            return None;
        };
        out.push(dom.as_ref().clone());
        ty = body.instantiate(arg);
    }
    Some(out)
}

/// Lean's `getFunInfoNArgs` for the head `f` of `f a⃗`: per parameter whether
/// it is a proof, an instance, a `Decidable` instance, and which earlier
/// parameters its type mentions; and which parameters the result type
/// mentions. `None` when the telescope hides behind a definition.
fn fun_info(
    state: &ProofState,
    goal: &Goal,
    f: &Expr,
    a: &[Expr],
) -> Option<(Vec<ParamInfo>, Vec<usize>)> {
    let f_ty = state.whnf(goal, &state.infer_type(goal, f).ok()?);
    let concrete = telescope_types(state, goal, f, a)?;
    let n = a.len();
    let mut generic = f_ty;
    let mut params = Vec::with_capacity(n);
    for (i, concrete_dom) in concrete.iter().enumerate() {
        let ExprKind::Pi(bd, dom, body) = generic.kind() else {
            return None;
        };
        let back_deps = (0..i)
            .filter(|&j| dom.has_loose_bvar(u32::try_from(i - 1 - j).unwrap_or(u32::MAX)))
            .collect();
        let is_prop = sort_level(state, goal, concrete_dom).is_some_and(|l| l.is_zero());
        let is_inst = bd.info == BinderInfo::InstImplicit;
        let is_dec_inst = is_inst
            && matches!(concrete_dom.get_app_fn().kind(),
                ExprKind::Const(h, _) if h.to_string() == "Decidable");
        params.push(ParamInfo {
            is_prop,
            is_inst,
            is_dec_inst,
            back_deps,
        });
        generic = body.as_ref().clone();
    }
    let result_deps = (0..n)
        .filter(|&j| generic.has_loose_bvar(u32::try_from(n - 1 - j).unwrap_or(u32::MAX)))
        .collect();
    Some((params, result_deps))
}

/// `Some(mask)` when `f` is a constructor of a CLASS: `mask[i]` says the
/// parameter is a field (Lean's `getClassSubobjectMask?` — an
/// instance-implicit field of a class constructor is a parent subobject and
/// may change like an ordinary argument).
fn class_field_mask(state: &ProofState, f: &Expr, n: usize) -> Option<Vec<bool>> {
    let ExprKind::Const(name, _) = f.kind() else {
        return None;
    };
    let ctor = state.env.get_constructor(name)?;
    if !state.env.is_class(&ctor.inductive_name) {
        return None;
    }
    let num_params = ctor.num_params as usize;
    Some((0..n).map(|i| i >= num_params).collect())
}

/// Lean's `getCongrSimpKinds` + `fixKindsForDependencies`.
fn congr_simp_kinds(
    params: &[ParamInfo],
    result_deps: &[usize],
    mask: Option<&[bool]>,
) -> Vec<ArgKind> {
    let mut kinds: Vec<ArgKind> = Vec::with_capacity(params.len());
    for (i, p) in params.iter().enumerate() {
        let kind = if result_deps.contains(&i) {
            ArgKind::Fixed
        } else if p.is_prop {
            ArgKind::Cast
        } else if p.is_inst {
            if mask.is_some_and(|m| m.get(i).copied().unwrap_or(false)) {
                ArgKind::Eq
            } else if p.is_dec_inst && p.back_deps.iter().any(|&j| kinds[j] == ArgKind::Eq) {
                ArgKind::SubsingletonInst
            } else {
                ArgKind::Fixed
            }
        } else {
            ArgKind::Eq
        };
        kinds.push(kind);
    }
    for i in 0..params.len() {
        let depended_on = ((i + 1)..params.len()).any(|j| {
            params[j].back_deps.contains(&i) && matches!(kinds[j], ArgKind::Eq | ArgKind::Fixed)
        });
        if depended_on {
            kinds[i] = ArgKind::Fixed;
        }
    }
    kinds
}

/// The arguments of `rhs` as an application of `f` with `n` arguments,
/// unfolding `rhs` once (Lean's `apply` unifies up to definitional
/// unfolding: `⟨x, hx⟩ = default` meets `default`'s value), and finally —
/// when `f` is a structure constructor — through structure eta.
fn rhs_args(
    state: &ProofState,
    goal: &Goal,
    f: &Expr,
    a: &[Expr],
    rhs: &Expr,
) -> Option<Vec<Expr>> {
    let n = a.len();
    let matches_head = |e: &Expr| {
        let args: Vec<Expr> = e.get_app_args().into_iter().cloned().collect();
        (args.len() == n && state.is_def_eq(goal, e.get_app_fn(), f)).then_some(args)
    };
    if let Some(args) = matches_head(rhs) {
        return Some(args);
    }
    if let Some(args) = matches_head(&state.whnf(goal, rhs)) {
        return Some(args);
    }
    struct_eta_rhs_args(state, goal, f, a, rhs)
}

/// STRUCTURE ETA for the right side of `S.mk a⃗ = e`.
///
/// Lean never requires the right side to be syntactically a constructor
/// application. `MVarId.congr?` (`Lean/Meta/Tactic/Congr.lean:42-51`) reads the
/// head off the LEFT side only — `let some (_, lhs, _) := target.eq? | return
/// none; unless lhs.isApp do return none; … mkCongrSimp? lhs.getAppFn` — and
/// `applyCongrThm?` (:33-38) then ASSERTS the congruence theorem and `apply`s
/// it, so the right side's arguments are solved by `isDefEq`, where
/// `isDefEqEtaStruct` (`Lean/Meta/ExprDefEq.lean:111`, called at :2176) assigns
/// `?bᵢ := e.projᵢ`. Clean decides by a syntactic head-plus-arity match, so a
/// bare local on the right made `congr` refuse a goal Lean splits: `beq_ext`
/// (`Mathlib/Logic/Basic.lean:999`), whose `have ⟨beq1⟩ := inst1` leaves
/// `BEq.mk beq1 = inst2` with `inst2` a rigid local.
///
/// This mints exactly what that unification would. The structure's PARAMETERS
/// are taken from the LEFT side — the `Eq`'s type fixes them on both sides, and
/// emitting a projection at a parameter position would mint a well-typed WRONG
/// congruence goal — and each FIELD becomes `Proj(S, i, rhs)`.
///
/// Fail-closed in four ways, in ascending order of strength:
/// * only a single-constructor, index-free inductive whose constructor has at
///   least one field (never a multi-constructor inductive);
/// * never a Prop-valued structure — proof irrelevance already settles those
///   and `congrPre` has run before this point;
/// * never a metavariable-headed right side — eta-expanding an unassigned
///   metavariable would commit the unifier to a constructor form it could
///   otherwise solve more generally;
/// * and finally the expansion is only accepted when it TYPE-CHECKS and is
///   definitionally equal to `rhs`, which is the same `isDefEq` question Lean
///   asks. Clean's def-eq already has structure eta (measured:
///   `theorem eta1 (i : MyBEq α) : i = MyBEq.mk i.beq := rfl` passes), so this
///   is a re-derivation of Lean's answer rather than a new acceptance rule.
fn struct_eta_rhs_args(
    state: &ProofState,
    goal: &Goal,
    f: &Expr,
    a: &[Expr],
    rhs: &Expr,
) -> Option<Vec<Expr>> {
    let ExprKind::Const(ctor_name, _) = f.kind() else {
        return None;
    };
    let ctor = state.env.get_constructor(ctor_name)?;
    let num_params = ctor.num_params as usize;
    let num_fields = ctor.num_fields as usize;
    let inductive_name = ctor.inductive_name.clone();
    if num_fields == 0 || a.len() != num_params + num_fields {
        return None;
    }
    let inductive = state.env.get_inductive(&inductive_name)?;
    if inductive.constructor_names.len() != 1 || inductive.num_indices != 0 {
        return None;
    }
    // A metavariable on the right is the unifier's business, not eta's.
    if matches!(rhs.get_app_fn().kind(),
        ExprKind::FVar(fvar) if MetaState::from_fvar(*fvar).is_some())
    {
        return None;
    }
    let rhs_ty = state.infer_type(goal, rhs).ok()?;
    if sort_level(state, goal, &rhs_ty).is_some_and(|level| level.is_zero()) {
        return None;
    }
    let mut args: Vec<Expr> = a[..num_params].to_vec();
    for field in 0..num_fields {
        let proj = Expr::proj(
            inductive_name.clone(),
            u32::try_from(field).ok()?,
            rhs.clone(),
        );
        // A `Proj` of something that is not a structure does not type-check;
        // refusing here leaves the goal untouched rather than handing the
        // kernel a term it will reject.
        let _: Expr = state.infer_type(goal, &proj).ok()?;
        args.push(proj);
    }
    state
        .is_def_eq(goal, &Expr::apps_ref(f.clone(), &args), rhs)
        .then_some(args)
}

/// Lean's `congr?`: split `f a⃗ = f b⃗` along `f`'s congr-simp kinds.
fn congr_simp(
    state: &mut ProofState,
    goal: &Goal,
    eq_level: &Level,
    ty: &Expr,
    lhs: &Expr,
    rhs: &Expr,
) -> Result<Option<usize>, TacticError> {
    let f = lhs.get_app_fn().clone();
    let a: Vec<Expr> = lhs.get_app_args().into_iter().cloned().collect();
    if a.is_empty() {
        return Ok(None);
    }
    let Some(b) = rhs_args(state, goal, &f, &a, rhs) else {
        return Ok(None);
    };
    let Some((params, result_deps)) = fun_info(state, goal, &f, &a) else {
        return Ok(None);
    };
    let mask = class_field_mask(state, &f, a.len());
    let kinds = congr_simp_kinds(&params, &result_deps, mask.as_deref());
    transport(state, goal, eq_level, ty, lhs, &f, &a, &b, &kinds)
}

/// Lean's `congrImplies?`: `(p → q) = (p' → q')` splits into `p = p'` and
/// `q = q'`, through the same transport over `fun a b => a → b`.
fn congr_implies(
    state: &mut ProofState,
    goal: &Goal,
    eq_level: &Level,
    ty: &Expr,
    lhs: &Expr,
    rhs: &Expr,
) -> Result<Option<usize>, TacticError> {
    let rhs = state.whnf(goal, rhs);
    let (ExprKind::Pi(_, p, q), ExprKind::Pi(_, p2, q2)) = (lhs.kind(), rhs.kind()) else {
        return Ok(None);
    };
    if q.has_loose_bvar(0) || q2.has_loose_bvar(0) {
        return Ok(None);
    }
    let (Some(u), Some(v)) = (sort_level(state, goal, p), sort_level(state, goal, q)) else {
        return Ok(None);
    };
    let arrow = Expr::lam(
        BinderInfo::Default,
        Expr::sort(u),
        Expr::lam(
            BinderInfo::Default,
            Expr::sort(v),
            Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::bvar(1)),
        ),
    );
    let a = [p.as_ref().clone(), q.as_ref().clone()];
    let b = [p2.as_ref().clone(), q2.as_ref().clone()];
    transport(
        state,
        goal,
        eq_level,
        ty,
        lhs,
        &arrow,
        &a,
        &b,
        &[ArgKind::Eq, ArgKind::Eq],
    )
}

/// `@Subsingleton.elim (Decidable p) (instSubsingletonDecidable p) a b` when
/// `tau` is `Decidable p` and both constants exist (they live in `Init`).
fn subsingleton_elim(
    state: &ProofState,
    tau: &Expr,
    level: &Level,
    a: &Expr,
    b: &Expr,
) -> Option<Expr> {
    let (_, args) = const_app_args(tau, "Decidable", 1)?;
    let elim = Name::from_string("Subsingleton.elim");
    let inst = Name::from_string("instSubsingletonDecidable");
    state.env.get_const(&elim)?;
    state.env.get_const(&inst)?;
    Some(Expr::apps(
        Expr::const_(elim, vec![level.clone()]),
        [
            tau.clone(),
            Expr::app(Expr::const_(inst, vec![]), args[0].clone()),
            a.clone(),
            b.clone(),
        ],
    ))
}

/// Build the congruence proof of `lhs = rhs` (`lhs = f a⃗`, `rhs ≡ f b⃗`)
/// along `kinds`, close the goal with it, and push one goal `aᵢ = bᵢ` per
/// changed argument that has no closed proof. `None` when a FIXED argument
/// disagrees or the proof does not check (state unchanged).
#[allow(clippy::too_many_arguments)]
fn transport(
    state: &mut ProofState,
    goal: &Goal,
    eq_level: &Level,
    ty: &Expr,
    lhs: &Expr,
    f: &Expr,
    a: &[Expr],
    b: &[Expr],
    kinds: &[ArgKind],
) -> Result<Option<usize>, TacticError> {
    let n = a.len();
    let mut changed: Vec<usize> = Vec::new();
    let mut casts: Vec<usize> = Vec::new();
    for i in 0..n {
        match kinds[i] {
            ArgKind::Fixed => {
                if !state.is_def_eq(goal, &a[i], &b[i]) {
                    return Ok(None);
                }
            }
            ArgKind::Cast => casts.push(i),
            ArgKind::Eq | ArgKind::SubsingletonInst => {
                if a[i] != b[i] {
                    changed.push(i);
                }
            }
        }
    }
    let Some(tys_a) = telescope_types(state, goal, f, a) else {
        return Ok(None);
    };

    let z: Vec<(usize, FVarId)> = changed.iter().map(|&i| (i, state.fresh_fvar())).collect();
    let q: Vec<(usize, FVarId)> = casts.iter().map(|&i| (i, state.fresh_fvar())).collect();
    let fvar_at = |i: usize| {
        z.iter()
            .chain(q.iter())
            .find(|(pos, _)| *pos == i)
            .map(|(_, id)| *id)
    };
    let c: Vec<Expr> = (0..n)
        .map(|i| fvar_at(i).map_or_else(|| a[i].clone(), Expr::fvar))
        .collect();
    let Some(tys_c) = telescope_types(state, goal, f, &c) else {
        return Ok(None);
    };

    // Q z⃗ := ∀ q⃗, lhs = f c⃗
    let eq_const = || Expr::const_(Name::from_string("Eq"), vec![eq_level.clone()]);
    let mut q_fun = Expr::apps(
        eq_const(),
        [
            ty.clone(),
            lhs.clone(),
            Expr::apps(f.clone(), c.iter().cloned()),
        ],
    );
    for &(pos, id) in q.iter().rev() {
        q_fun = Expr::pi(
            BinderInfo::Default,
            tys_c[pos].clone(),
            q_fun.abstract_fvar(id),
        );
    }
    let subst_z = |e: &Expr, upto: usize| {
        z.iter()
            .enumerate()
            .fold(e.clone(), |acc, (m, &(pos, id))| {
                let value = if m < upto { &b[pos] } else { &a[pos] };
                acc.subst_fvar(id, value)
            })
    };

    // Q a⃗ by `fun q⃗ => Eq.refl lhs`.
    let mut proof = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![eq_level.clone()]),
        [ty.clone(), lhs.clone()],
    );
    for &(pos, id) in q.iter().rev() {
        proof = Expr::lam(
            BinderInfo::Default,
            subst_z(&tys_c[pos], 0),
            proof.abstract_fvar(id),
        );
    }

    let mut new_goals = Vec::new();
    for (m, &(pos, id)) in z.iter().enumerate() {
        let tau = tys_a[pos].clone();
        let Some(tau_level) = sort_level(state, goal, &tau) else {
            return Ok(None);
        };
        let closed = if kinds[pos] == ArgKind::SubsingletonInst {
            subsingleton_elim(state, &tau, &tau_level, &a[pos], &b[pos])
        } else {
            None
        };
        let e_m = match closed {
            Some(term) => term,
            None => {
                let eq_ty = Expr::apps(
                    Expr::const_(Name::from_string("Eq"), vec![tau_level.clone()]),
                    [tau.clone(), a[pos].clone(), b[pos].clone()],
                );
                let meta = state.fresh_meta_in_context(eq_ty.clone(), &goal.local_ctx);
                new_goals.push(Goal {
                    meta_id: meta,
                    target: eq_ty,
                    local_ctx: goal.local_ctx.clone(),
                    tag: None,
                    case_binders: goal.case_binders.clone(),
                });
                Expr::fvar(MetaState::to_fvar(meta))
            }
        };
        // motive z := Q (b₁ … b_{m-1}, z, a_{m+1} …)
        let body = z
            .iter()
            .enumerate()
            .filter(|(m2, _)| *m2 != m)
            .fold(q_fun.clone(), |acc, (m2, &(p2, id2))| {
                acc.subst_fvar(id2, if m2 < m { &b[p2] } else { &a[p2] })
            });
        let motive = Expr::lam(BinderInfo::Default, tau.clone(), body.abstract_fvar(id));
        proof = Expr::apps(
            Expr::const_(
                Name::from_string("Eq.ndrec"),
                vec![Level::zero(), tau_level],
            ),
            [tau, a[pos].clone(), motive, proof, b[pos].clone(), e_m],
        );
    }
    for &(pos, _) in &q {
        proof = Expr::app(proof, b[pos].clone());
    }
    if state.close_goal(goal, proof).is_err() {
        return Ok(None);
    }
    let pieces = new_goals.len();
    for g in new_goals.into_iter().rev() {
        state.goals.push_front(g);
    }
    Ok(Some(pieces))
}

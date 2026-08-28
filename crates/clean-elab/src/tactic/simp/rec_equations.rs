// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Per-constructor equational lemmas for `simp [f]` where `f` is a definition
//! compiled to a `T.rec` value (the rec-iota simp class, B7).
//!
//! A structurally-recursive `def` elaborates to a value of the shape
//! `fun x₁ … xₙ => T.rec params motive minors major extras`, with the major
//! premise one of the def's own binders. Delta-unfolding such a definition
//! (the historical `unfold_defs` path) rewrites every `f`-application in the
//! goal into a raw recursor application which simp then cannot reduce — simp's
//! definitional normalization has no iota step, and, worse, induction
//! hypotheses in the local context still speak in `f`-form, so IH rewrites can
//! never match the rec-form goal (`mixed_tree_mirror_involutive`,
//! `mixed_mylist_append_assoc`).
//!
//! Lean 4's answer is per-definition *equational lemmas*: `simp [f]` rewrites
//! with `f.eq_N : f a… (c fields…) = <arm>` and the goal stays in surface
//! `f`-form. This module synthesizes exactly those equations at simp time,
//! straight from the compiled value plus the environment's recursor rules:
//! for each constructor `c` of the major's inductive
//!
//! ```text
//!   f prefix… (c params fields…) extras… = <iota-reduced arm with recursive
//!                                           `T.rec …` calls folded back to f>
//! ```
//!
//! Each equation is definitionally true (delta + beta + iota), so its proof
//! witness is a plain `Eq.refl` over the LHS. Soundness never rests on the
//! synthesis being right: `try_apply_simp_lemma_with_proof` re-checks the
//! instantiated proof against the claimed rewrite with kernel `is_def_eq`
//! (`proof_matches_rewrite`), and `close_goal`'s kernel re-check is the final
//! backstop — a bug here refuses a rewrite, it cannot mint a wrong one.
//!
//! # Fail-closed scope
//!
//! Synthesis returns `None` (and the caller falls back to the historical
//! delta-unfold) unless the whole shape is the plain structural class:
//! a level-monomorphic `Definition`, a non-mutual / non-nested / non-reflexive
//! inductive with no indices, `MajorAfterMinors` argument order, the major
//! premise and every extra argument being exactly the def's trailing binders,
//! and every recursive `T.rec` call in each reduced arm folding back to an
//! `f`-application over the same instantiated prefix. All-or-nothing per
//! definition: if any constructor's equation fails to synthesize, no equation
//! is emitted (a half-covered constructor set would leave some goals stuck in
//! a shape neither path can rewrite).

use clean_kernel::env::ConstantKind;
use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr, ExprKind, Level, RecursorArgOrder};

use super::reduce::beta_reduce;
use super::types::{SimpIndexMode, SimpLemma};
use crate::tactic::bvar_ops::lift_bvars;

/// Priority for synthesized equations: same tier as other `simp [name]`
/// extras (`collect_extra_lemmas` uses 50 for environment lemmas and local
/// hypothesis rewrites alike).
const EQUATION_PRIORITY: u32 = 50;

/// Synthesize per-constructor equational lemmas for `simp [name]` when `name`
/// is a definition compiled to a `T.rec` value.
///
/// # Contract
///
/// REQUIRES: `env` is the environment `name` will be rewritten against.
/// ENSURES: On `Some(eqs)`, `eqs` has exactly one lemma per constructor of the
///   recursor's inductive, each of the form `f … (c …) … = <arm>` with an
///   `Eq.refl`-over-LHS proof template; every lemma's LHS/RHS/eq_type use the
///   `extract_equality_full` pattern-BVar convention (loose BVars index the
///   equation's own binder telescope, innermost = 0).
/// ENSURES: On `Some(eqs)`, every equation RHS is the beta-reduced single-step
///   iota reduct of its LHS with recursive recursor calls folded back to `f` —
///   definitionally equal to the LHS by construction (delta+beta+iota), and
///   free of `T.rec` (surface form), so rewriting cannot leak rec-form terms.
/// ENSURES: `None` whenever any shape requirement fails (see module docs) —
///   the caller keeps the historical behavior.
pub(super) fn synthesize_rec_def_equations(
    env: &Environment,
    name: &Name,
) -> Option<Vec<SimpLemma>> {
    let decl = env.get_const(name)?;
    if !matches!(decl.kind, ConstantKind::Definition) {
        return None;
    }
    // Level-polymorphic defs are out of scope: the `Eq.refl` proof template is
    // assembled at synthesis time, where nothing can solve a level param, and
    // an unsolved level in a template is exactly the declaration-killing class
    // `template_has_unsolved_level` refuses.
    if !decl.level_params.is_empty() {
        return None;
    }
    let value = decl.value.as_ref()?;

    // 1. The value's lambda telescope: `fun x₁ … xₙ => body`.
    let mut n: usize = 0;
    let mut body: &Expr = value;
    while let ExprKind::Lam(_, _, b) = body.kind() {
        n += 1;
        body = b.as_ref();
    }
    if n == 0 {
        return None;
    }

    // 2. `body` must be a recursor application spine.
    let head = body.get_app_fn();
    let ExprKind::Const(rec_name, rec_levels) = head.kind() else {
        return None;
    };
    let rv = env.get_recursor(rec_name)?;
    if rv.num_motives != 1 || rv.num_indices != 0 {
        return None;
    }
    if !matches!(rv.arg_order, RecursorArgOrder::MajorAfterMinors) {
        return None;
    }
    if rec_levels.len() != rv.level_params.len() || rec_levels.iter().any(Level::has_params) {
        return None;
    }
    let iv = env.get_inductive(&rv.inductive_name)?;
    if iv.all_names.len() > 1 || iv.is_nested || iv.is_reflexive {
        return None;
    }
    if rv.rules.is_empty() || rv.rules.len() != iv.constructor_names.len() {
        return None;
    }

    let args: Vec<Expr> = body.get_app_args().iter().map(|a| (*a).clone()).collect();
    let num_params = rv.num_params as usize;
    // Spine layout (MajorAfterMinors, 0 indices): params, motive, minors,
    // major, then `m` extra arguments consumed by a function-typed motive.
    let p1 = num_params + 1 + rv.num_minors as usize;
    if args.len() < p1 + 1 {
        return None;
    }
    let m = args.len() - p1 - 1;
    if m + 1 > n {
        return None;
    }
    // 3. Major and extras must be exactly the def's trailing binders, in
    // order: `body = Rec prefix… x_{n-m} x_{n-m+1} … xₙ`.
    if args[p1] != Expr::bvar(m as u32) {
        return None;
    }
    for (i, extra) in args[p1 + 1..].iter().enumerate() {
        if *extra != Expr::bvar((m - 1 - i) as u32) {
            return None;
        }
    }
    // 4. The prefix spine (params/motive/minors) must not capture the major
    // or the extras — otherwise substituting the constructor for the major
    // would have to rewrite the prefix too and the fold-back spine below
    // would not be constant across recursive calls.
    for a in &args[..p1] {
        for v in 0..=(m as u32) {
            if a.has_loose_bvar(v) {
                return None;
            }
        }
    }

    // Constructor levels: a recursor prepends its motive-universe params, so
    // the inductive's own levels are the trailing entries of the rec levels.
    let ind_lp = iv.level_params.len();
    if rec_levels.len() < ind_lp {
        return None;
    }
    let ctor_levels: Vec<Level> = rec_levels[rec_levels.len() - ind_lp..].to_vec();

    // The equation sides' type: f's result type after its n binders (same
    // telescope indexing as the value's lambda telescope), and its sort for
    // the `Eq.refl` universe.
    let mut result_ty: &Expr = &decl.type_;
    for _ in 0..n {
        let ExprKind::Pi(_, _, b) = result_ty.kind() else {
            return None;
        };
        result_ty = b.as_ref();
    }
    let u = sort_level_of_result_type(env, result_ty)?;

    // `f x₁ … xₙ` over the original telescope; each equation σ-maps it.
    let mut f_app_old = Expr::const_(name.clone(), Vec::<Level>::new());
    for i in (0..n).rev() {
        f_app_old = Expr::app(f_app_old, Expr::bvar(i as u32));
    }

    let rec_levels_slice: Vec<Level> = rec_levels.iter().cloned().collect();
    let mut out = Vec::with_capacity(rv.rules.len());
    for rule in &rv.rules {
        let cv = env.get_constructor(&rule.constructor_name)?;
        if cv.inductive_name != rv.inductive_name || cv.num_fields != rule.num_fields {
            return None;
        }
        if !rule.rhs.is_lam() {
            return None;
        }
        let k = rule.num_fields as usize;

        // The constructor application replacing the major binder, built in the
        // NEW telescope `prefix-binders… fields… extras…` (innermost = last
        // extra). Its params are the rec spine's params, σ-shifted.
        let shift = ShiftSigma {
            m: m as u32,
            k: k as u32,
        };
        let mut ctor_app = Expr::const_(rule.constructor_name.clone(), ctor_levels.clone());
        for pa in &args[..num_params] {
            ctor_app = Expr::app(ctor_app, shift.apply(pa, 0)?);
        }
        for t in 0..k {
            ctor_app = Expr::app(ctor_app, Expr::bvar((m + k - 1 - t) as u32));
        }

        let sigma = Sigma {
            shift,
            ctor_app: &ctor_app,
        };
        let lhs = sigma.apply(&f_app_old, 0)?;
        let eq_ty = sigma.apply(result_ty, 0)?;

        // One manual iota step: the recursor rule's RHS lambda applied to the
        // σ-mapped prefix (params+motive+minors), then the constructor fields,
        // then the extras — exactly the kernel's `try_iota_reduction` recipe —
        // and beta-reduced. Bounded by construction: no whnf, no further
        // unfolding, so the arm keeps its surface operators.
        let sprefix: Vec<Expr> = args[..p1]
            .iter()
            .map(|a| sigma.apply(a, 0))
            .collect::<Option<Vec<_>>>()?;
        let mut red = rule
            .rhs
            .instantiate_level_params_direct(&rv.level_params, &rec_levels_slice);
        for pa in &sprefix {
            red = Expr::app(red, pa.clone());
        }
        for t in 0..k {
            red = Expr::app(red, Expr::bvar((m + k - 1 - t) as u32));
        }
        for i in 0..m {
            red = Expr::app(red, Expr::bvar((m - 1 - i) as u32));
        }
        let red = beta_reduce(&red);

        // Fold recursive `T.rec prefix… field extras…` calls back into
        // `f prefix-binders… field extras…` so the RHS (and thus the goal
        // after rewriting) stays in surface form the IHs can match.
        let f_prefix_args: Vec<Expr> = (0..(n - m - 1))
            .map(|i| Expr::bvar((n + k - 2 - i) as u32))
            .collect();
        let fold = RecFoldBack {
            rec_name,
            rec_levels: &rec_levels_slice,
            prefix: &sprefix,
            f_name: name,
            f_prefix_args: &f_prefix_args,
        };
        let rhs = fold.apply(&red, 0)?;

        // Proof witness: `@Eq.refl.{u} eq_ty lhs`. Definitional (delta+iota):
        // `proof_matches_rewrite` kernel-checks `rhs ≡ lhs` at match time.
        let proof = Expr::apps(
            Expr::const_str_levels("Eq.refl", vec![u.clone()]),
            [eq_ty.clone(), lhs.clone()],
        );
        out.push(SimpLemma {
            name: name.clone(),
            lhs,
            rhs,
            eq_type: Some(eq_ty),
            proof_expr: Some(proof),
            // The LHS head is the (semireducible, delta-unfoldable) `f`
            // itself, exactly the B102 class whose whnf'd discr-tree key rots
            // away from the goal's surface key — keep always-offered.
            index_mode: SimpIndexMode::Unindexed,
            priority: EQUATION_PRIORITY,
        });
    }
    Some(out)
}

/// Sort level of a definition's result type, resolved through its head
/// inductive: for `ty = T a…` with `T : Π …, Sort ℓ`, returns ℓ instantiated
/// at `T`'s level arguments. `None` for any other head (fail-closed).
fn sort_level_of_result_type(env: &Environment, ty: &Expr) -> Option<Level> {
    let head = ty.get_app_fn();
    let ExprKind::Const(tname, tlevels) = head.kind() else {
        return None;
    };
    let iv = env.get_inductive(tname)?;
    if iv.level_params.len() != tlevels.len() || tlevels.iter().any(Level::has_params) {
        return None;
    }
    let mut t: &Expr = &iv.type_;
    while let ExprKind::Pi(_, _, b) = t.kind() {
        t = b.as_ref();
    }
    let ExprKind::Sort(l) = t.kind() else {
        return None;
    };
    let subst: Vec<(Name, Level)> = iv
        .level_params
        .iter()
        .cloned()
        .zip(tlevels.iter().cloned())
        .collect();
    Some(l.substitute(&subst))
}

/// Index-only part of σ: maps an original-telescope BVar to the new telescope
/// where the major binder is replaced by `k` field binders. Used both bare
/// (for prefix expressions, which never reference major/extras — checked by
/// the caller) and inside [`Sigma`].
#[derive(Clone, Copy)]
struct ShiftSigma {
    /// Number of extra (post-major) binders.
    m: u32,
    /// Number of constructor fields replacing the major binder.
    k: u32,
}

impl ShiftSigma {
    /// REQUIRES: `e` has no loose BVar with telescope index `≤ m` (the caller
    /// checked the prefix spine); such a reference returns `None`.
    fn apply(&self, e: &Expr, depth: u32) -> Option<Expr> {
        map_bvars(e, depth, &|w, d| {
            let v = w - d; // telescope-level index
            if v > self.m {
                Some(Expr::bvar(w + self.k - 1))
            } else {
                None
            }
        })
    }
}

/// Full σ: extras keep their indices, the major becomes the constructor
/// application, prefix binders shift by `k - 1`.
struct Sigma<'a> {
    shift: ShiftSigma,
    /// Constructor application at new-telescope depth 0; lifted at use depth.
    ctor_app: &'a Expr,
}

impl Sigma<'_> {
    fn apply(&self, e: &Expr, depth: u32) -> Option<Expr> {
        map_bvars(e, depth, &|w, d| {
            let v = w - d;
            if v < self.shift.m {
                Some(Expr::bvar(w))
            } else if v == self.shift.m {
                Some(lift_bvars(self.ctor_app, d))
            } else {
                Some(Expr::bvar(w + self.shift.k - 1))
            }
        })
    }
}

/// Structural walk applying `f(bvar_index, binder_depth)` to every loose BVar
/// (`bvar_index ≥ binder_depth`); bound BVars pass through. Returns `None` on
/// expression kinds outside the plain lambda-calculus fragment a compiled
/// structural def can contain (fail-closed) or when `f` refuses a BVar.
fn map_bvars(e: &Expr, depth: u32, f: &dyn Fn(u32, u32) -> Option<Expr>) -> Option<Expr> {
    Some(match e.kind() {
        ExprKind::BVar(w) => {
            if *w < depth {
                e.clone()
            } else {
                f(*w, depth)?
            }
        }
        ExprKind::App(func, a) => Expr::app(map_bvars(func, depth, f)?, map_bvars(a, depth, f)?),
        ExprKind::Lam(bi, ty, b) => {
            Expr::lam(*bi, map_bvars(ty, depth, f)?, map_bvars(b, depth + 1, f)?)
        }
        ExprKind::Pi(bi, ty, b) => {
            Expr::pi(*bi, map_bvars(ty, depth, f)?, map_bvars(b, depth + 1, f)?)
        }
        ExprKind::Let(nm, ty, val, b, nd) => Expr::let_named(
            nm.clone(),
            map_bvars(ty, depth, f)?,
            map_bvars(val, depth, f)?,
            map_bvars(b, depth + 1, f)?,
            *nd,
        ),
        ExprKind::Proj(s, i, inner) => Expr::proj(s.clone(), *i, map_bvars(inner, depth, f)?),
        ExprKind::MData(md, inner) => Expr::mdata(md.clone(), map_bvars(inner, depth, f)?),
        ExprKind::Const(..) | ExprKind::Sort(_) | ExprKind::Lit(_) | ExprKind::FVar(_) => e.clone(),
        // Metavariables, cubical extensions, …: not part of the fragment.
        _ => return None,
    })
}

/// Folds recursive recursor calls back into `f`-applications.
struct RecFoldBack<'a> {
    rec_name: &'a Name,
    rec_levels: &'a [Level],
    /// σ-mapped params+motive+minors at new-telescope depth 0.
    prefix: &'a [Expr],
    f_name: &'a Name,
    /// `f`'s leading (pre-major) arguments — the new-telescope prefix-binder
    /// BVars — at depth 0.
    f_prefix_args: &'a [Expr],
}

impl RecFoldBack<'_> {
    /// Replace every `Rec prefix… major extras…` spine with
    /// `f prefix-binders… major extras…`. `None` when a `Rec` occurrence
    /// survives in any unfoldable position — the equation would leak a raw
    /// recursor into goals, so the whole synthesis is abandoned.
    fn apply(&self, e: &Expr, depth: u32) -> Option<Expr> {
        match e.kind() {
            ExprKind::App(func, a) => {
                if let ExprKind::Const(hn, hl) = e.get_app_fn().kind() {
                    if hn == self.rec_name {
                        if hl.as_slice() != self.rec_levels {
                            return None;
                        }
                        let eargs: Vec<Expr> =
                            e.get_app_args().iter().map(|x| (*x).clone()).collect();
                        if eargs.len() < self.prefix.len() + 1 {
                            return None;
                        }
                        for (pa, ea) in self.prefix.iter().zip(&eargs) {
                            if lift_bvars(pa, depth) != *ea {
                                return None;
                            }
                        }
                        let mut folded = Expr::const_(self.f_name.clone(), Vec::<Level>::new());
                        for fa in self.f_prefix_args {
                            folded = Expr::app(folded, lift_bvars(fa, depth));
                        }
                        for ea in &eargs[self.prefix.len()..] {
                            folded = Expr::app(folded, self.apply(ea, depth)?);
                        }
                        return Some(folded);
                    }
                }
                Some(Expr::app(self.apply(func, depth)?, self.apply(a, depth)?))
            }
            ExprKind::Const(nm, _) if nm == self.rec_name => None,
            ExprKind::Lam(bi, ty, b) => Some(Expr::lam(
                *bi,
                self.apply(ty, depth)?,
                self.apply(b, depth + 1)?,
            )),
            ExprKind::Pi(bi, ty, b) => Some(Expr::pi(
                *bi,
                self.apply(ty, depth)?,
                self.apply(b, depth + 1)?,
            )),
            ExprKind::Let(nm, ty, val, b, nd) => Some(Expr::let_named(
                nm.clone(),
                self.apply(ty, depth)?,
                self.apply(val, depth)?,
                self.apply(b, depth + 1)?,
                *nd,
            )),
            ExprKind::Proj(s, i, inner) => {
                Some(Expr::proj(s.clone(), *i, self.apply(inner, depth)?))
            }
            ExprKind::MData(md, inner) => Some(Expr::mdata(md.clone(), self.apply(inner, depth)?)),
            _ => Some(e.clone()),
        }
    }
}

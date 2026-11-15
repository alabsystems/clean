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
//!   f x₁ … (c params fields…) … xₙ = <iota-reduced arm with recursive
//!                                      `T.rec …` calls folded back to f>
//! ```
//!
//! (the constructor at the major's binder position, every other binder as
//! itself).
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
//! a `Definition` whose levels belong to its declared universe telescope,
//! a non-mutual / non-nested / non-reflexive
//! inductive with no indices, `MajorAfterMinors` argument order, the major
//! premise and every extra argument being distinct binders of the def with
//! every binder inside the major an extra (an extra may also sit OUTSIDE it: a
//! leading parameter the match lowering generalized into the motive), the
//! prefix spine mentioning neither, and every recursive `T.rec` call in each
//! reduced arm folding back to an `f`-application over the same instantiated
//! prefix. All-or-nothing per
//! definition: if any constructor's equation fails to synthesize, no equation
//! is emitted (a half-covered constructor set would leave some goals stuck in
//! a shape neither path can rewrite).

use clean_kernel::env::ConstantKind;
use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr, ExprKind, Level, RecursorArgOrder};

use super::reduce::beta_reduce;
use super::types::{SimpIndexMode, SimpLemma};
use crate::tactic::bvar_ops::lift_bvars;

#[path = "rec_equations_brec.rs"]
mod brec;

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
    synthesize_rec_def_equations_or_decline(env, name).ok()
}

/// [`synthesize_rec_def_equations`], naming the shape requirement that
/// declined when there are no equations (a diagnostic only: every decline
/// leaves the historical delta-unfold in place).
pub(super) fn synthesize_rec_def_equations_or_decline(
    env: &Environment,
    name: &Name,
) -> Result<Vec<SimpLemma>, &'static str> {
    synthesize_native_equations(env, name).or_else(|reason| {
        super::declared_equations::collect(env, name, EQUATION_PRIORITY)
            .or_else(|| brec::synthesize(env, name))
            .ok_or(reason)
    })
}

fn synthesize_native_equations(
    env: &Environment,
    name: &Name,
) -> Result<Vec<SimpLemma>, &'static str> {
    // A member of a lifted `mutual` block (gap G23) has its equations
    // recorded by the lift: its value applies a shared nested recursor that
    // the plain structural shape below declines.
    if let Some(lifted) = super::rec_equations_lifted::lifted_member_equations(env, name) {
        return lifted;
    }
    let decl = env.get_const(name).ok_or("no such constant")?;
    if !matches!(decl.kind, ConstantKind::Definition) {
        return Err("not a definition");
    }
    let value = decl.value.as_ref().ok_or("no value")?;
    // Keep declared parameters in the schema. LemmaLevels freshens them for
    // each match together with the LHS, RHS and Eq.refl template. Foreign
    // parameters remain a refusal, not implicit new schema variables.
    if crate::infer::collect_level_params(&[value, &decl.type_])
        .iter()
        .any(|parameter| !decl.level_params.contains(parameter))
    {
        return Err("undeclared universe parameter");
    }
    let definition_levels: Vec<Level> = decl
        .level_params
        .iter()
        .cloned()
        .map(Level::param)
        .collect();

    // 1. The value's lambda telescope: `fun x₁ … xₙ => body`.
    let mut n: usize = 0;
    let mut body: &Expr = value;
    while let ExprKind::Lam(_, _, b) = body.kind() {
        n += 1;
        body = b.as_ref();
    }
    if n == 0 {
        return Err("no lambda telescope");
    }

    // 2. `body` must be a recursor application spine.
    let head = body.get_app_fn();
    let ExprKind::Const(rec_name, rec_levels) = head.kind() else {
        return Err("body head is not a constant");
    };
    let rv = env.get_recursor(rec_name).ok_or("head is not a recursor")?;
    if rv.num_motives != 1 || rv.num_indices != 0 {
        return Err("not a single-motive index-free recursor");
    }
    if !matches!(rv.arg_order, RecursorArgOrder::MajorAfterMinors) {
        return Err("recursor is not MajorAfterMinors");
    }
    if rec_levels.len() != rv.level_params.len()
        || !levels_are_declared(rec_levels, &decl.level_params)
    {
        return Err("recursor levels are not declared");
    }
    let iv = env
        .get_inductive(&rv.inductive_name)
        .ok_or("recursor's inductive unknown")?;
    if iv.all_names.len() > 1 || iv.is_nested || iv.is_reflexive {
        return Err("mutual, nested or reflexive inductive");
    }
    if rv.rules.is_empty() || rv.rules.len() != iv.constructor_names.len() {
        return Err("recursor rules do not match the constructors");
    }

    let args: Vec<Expr> = body.get_app_args().iter().map(|a| (*a).clone()).collect();
    let num_params = rv.num_params as usize;
    // Spine layout (MajorAfterMinors, 0 indices): params, motive, minors,
    // major, then `m` extra arguments consumed by a function-typed motive.
    let p1 = num_params + 1 + rv.num_minors as usize;
    if args.len() < p1 + 1 {
        return Err("recursor spine has no major");
    }
    let num_extras = args.len() - p1 - 1;
    if num_extras + 1 > n {
        return Err("more extras than binders");
    }
    // 3. The major and the extras are distinct binders of the def, and every
    // other binder lies OUTSIDE the major (`f`'s fixed prefix). The extras
    // need not follow the major: the match lowering generalizes a parameter
    // written BEFORE the major into the motive too (`def f (k : Nat) : List α
    // → …` is `fun k x => T.rec … x k`), where Lean keeps it fixed — the same
    // function, so its equations are `f k (c fields…) = …` either way.
    let binder_bvar = |e: &Expr| match e.kind() {
        ExprKind::BVar(j) if (*j as usize) < n => Some(*j as usize),
        _ => None,
    };
    let major = binder_bvar(&args[p1]).ok_or("the major is not a binder of the def")?;
    let mut extras: Vec<usize> = Vec::with_capacity(num_extras);
    for extra in &args[p1 + 1..] {
        let j = binder_bvar(extra).ok_or("an extra is not a binder of the def")?;
        if j == major || extras.contains(&j) {
            return Err("an extra repeats the major or another extra");
        }
        extras.push(j);
    }
    // `m`: the binders inside the major. Each must be an extra — a binder
    // there that the recursor does not thread could have a type mentioning
    // the major, which no fold-back over the fields could re-type.
    let m = major;
    if (0..m).any(|j| !extras.contains(&j)) {
        return Err("a binder inside the major is not an extra");
    }
    // 4. The prefix spine (params/motive/minors) must not capture the major
    // or the extras — otherwise substituting the constructor for the major
    // would have to rewrite the prefix too and the fold-back spine below
    // would not be constant across recursive calls.
    for a in &args[..p1] {
        if std::iter::once(&major)
            .chain(&extras)
            .any(|&v| a.has_loose_bvar(v as u32))
        {
            return Err("the prefix spine mentions the major or an extra");
        }
    }
    // Where each of `f`'s arguments comes from in a recursive `T.rec` call:
    // a fixed binder is itself, the major and each extra are the call's
    // matching recursor argument (0 = major, 1 + i = extra i).
    let f_arg_sources: Vec<FArgSource> = (0..n)
        .map(|p| {
            let j = n - 1 - p;
            if j == major {
                FArgSource::RecArg(0)
            } else if let Some(i) = extras.iter().position(|&e| e == j) {
                FArgSource::RecArg(1 + i)
            } else {
                FArgSource::Fixed(j)
            }
        })
        .collect();

    // Constructor levels: a recursor prepends its motive-universe params, so
    // the inductive's own levels are the trailing entries of the rec levels.
    let ind_lp = iv.level_params.len();
    if rec_levels.len() < ind_lp {
        return Err("recursor levels shorter than the inductive's");
    }
    let ctor_levels: Vec<Level> = rec_levels[rec_levels.len() - ind_lp..].to_vec();

    // The equation sides' type: f's result type after its n binders (same
    // telescope indexing as the value's lambda telescope), and its sort for
    // the `Eq.refl` universe.
    let mut result_ty: &Expr = &decl.type_;
    for _ in 0..n {
        let ExprKind::Pi(_, _, b) = result_ty.kind() else {
            return Err("result type has fewer binders than the value");
        };
        result_ty = b.as_ref();
    }
    let u = sort_level_of_result_type(env, result_ty, &decl.level_params)
        .ok_or("result sort not resolvable")?;

    // `f x₁ … xₙ` over the original telescope; each equation σ-maps it.
    let mut f_app_old = Expr::const_(name.clone(), definition_levels.clone());
    for i in (0..n).rev() {
        f_app_old = Expr::app(f_app_old, Expr::bvar(i as u32));
    }

    let rec_levels_slice: Vec<Level> = rec_levels.iter().cloned().collect();
    let mut out = Vec::with_capacity(rv.rules.len());
    for rule in &rv.rules {
        let cv = env
            .get_constructor(&rule.constructor_name)
            .ok_or("rule constructor unknown")?;
        if cv.inductive_name != rv.inductive_name || cv.num_fields != rule.num_fields {
            return Err("rule and constructor disagree");
        }
        if !rule.rhs.is_lam() {
            return Err("rule RHS is not a lambda");
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
            ctor_app = Expr::app(
                ctor_app,
                shift
                    .apply(pa, 0)
                    .ok_or("a parameter mentions the major or an extra")?,
            );
        }
        for t in 0..k {
            ctor_app = Expr::app(ctor_app, Expr::bvar((m + k - 1 - t) as u32));
        }

        let sigma = Sigma {
            shift,
            ctor_app: &ctor_app,
        };
        let lhs = sigma.apply(&f_app_old, 0).ok_or("sigma on the LHS")?;
        let eq_ty = sigma
            .apply(result_ty, 0)
            .ok_or("sigma on the result type")?;

        // One manual iota step: the recursor rule's RHS lambda applied to the
        // σ-mapped prefix (params+motive+minors), then the constructor fields,
        // then the extras — exactly the kernel's `try_iota_reduction` recipe —
        // and brought to βζ-normal form (`beta_normal`). No whnf, no delta,
        // so the arm keeps its surface operators.
        let sprefix: Vec<Expr> = args[..p1]
            .iter()
            .map(|a| sigma.apply(a, 0))
            .collect::<Option<Vec<_>>>()
            .ok_or("sigma on the recursor prefix")?;
        let mut red = rule
            .rhs
            .instantiate_level_params_direct(&rv.level_params, &rec_levels_slice);
        for pa in &sprefix {
            red = Expr::app(red, pa.clone());
        }
        for t in 0..k {
            red = Expr::app(red, Expr::bvar((m + k - 1 - t) as u32));
        }
        for extra in &args[p1 + 1..] {
            red = Expr::app(red, sigma.apply(extra, 0).ok_or("sigma on an extra")?);
        }
        let red = beta_normal(&red).ok_or("the iota reduct has no beta normal form in bounds")?;

        // Fold recursive `T.rec prefix… field extras…` calls back into
        // `f prefix-binders… field extras…` so the RHS (and thus the goal
        // after rewriting) stays in surface form the IHs can match.
        //
        // The recursive call's prefix is the copy of the σ-mapped prefix that
        // the rule substituted into its `T.rec α motive minors… field`, now
        // in βζ-normal form with the rest of the reduct. Compare against the
        // normal form of the prefix, not the raw one: a minor carrying its
        // own redex or `let` (the nested-head fallback `(fun s x ih => …) s x
        // ih`, a pattern variable's `let` alias) is reduced in the copy. The
        // normal form is unique, so the two agree whatever order reduced them.
        let fold_prefix: Vec<Expr> = sprefix
            .iter()
            .map(beta_normal)
            .collect::<Option<Vec<_>>>()
            .ok_or("the recursor prefix has no beta normal form in bounds")?;
        // A fixed binder is outside the major (step 3), so σ only shifts it.
        let f_args: Vec<FArg> = f_arg_sources
            .iter()
            .map(|source| match *source {
                FArgSource::Fixed(j) => FArg::Fixed(Expr::bvar((j + k - 1) as u32)),
                FArgSource::RecArg(i) => FArg::RecArg(i),
            })
            .collect();
        let fold = RecFoldBack {
            rec_name,
            rec_levels: &rec_levels_slice,
            prefix: &fold_prefix,
            f_name: name,
            f_levels: &definition_levels,
            f_args: &f_args,
        };
        let rhs = fold
            .apply(&red, 0)
            .ok_or("a recursive call does not fold back to the definition")?;

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
    Ok(out)
}

/// Passes of [`beta_reduce`] that [`beta_normal`] makes before it gives up.
const BETA_NORMAL_ROUNDS: usize = 64;

/// The βζ-normal size (tree nodes) from which [`beta_normal`] declines
/// instead of building the normal form: a `match` that binds a large
/// right-hand side once by a `let` (G76) is linear as written and exponential
/// once normalized, and the iota reduct copies the whole minor into each
/// recursive call it contains (`zeta_size.rs`).
const BETA_NORMAL_MAX_NODES: u64 = 1 << 18;

/// The βζ-normal form of `e`. One [`beta_reduce`] pass contracts every redex
/// present in `e` but not the redexes its own substitutions create: the
/// iota reduct `rule_rhs prefix… fields… extras…` became `minor fields… ih
/// extras…`, a NEW redex, which a single pass left standing. With an extra
/// after the major (a parameter the lowering generalized into the motive) the
/// recursive call sat inside that redex as the bare induction hypothesis
/// `T.rec … tail`, not yet applied to its extra, and could not fold back to
/// `f k tail`: `def addKList (k : Nat) : List Nat → …` got no equations.
/// Repeats the pass to a fixpoint; `None` past [`BETA_NORMAL_ROUNDS`], or when
/// the normal form would reach [`BETA_NORMAL_MAX_NODES`] (fail-closed: the
/// caller declines and the delta-unfold stays, under simp's size budget).
fn beta_normal(e: &Expr) -> Option<Expr> {
    if super::zeta_size::beta_zeta_size_reaches(e, BETA_NORMAL_MAX_NODES) {
        return None;
    }
    let mut current = beta_reduce(e);
    for _ in 0..BETA_NORMAL_ROUNDS {
        let next = beta_reduce(&current);
        if next == current {
            return Some(current);
        }
        current = next;
    }
    None
}

/// Sort level of a definition's result type, resolved through its head
/// inductive: for `ty = T a…` with `T : Π …, Sort ℓ`, returns ℓ instantiated
/// at `T`'s level arguments. `None` for any other head (fail-closed).
fn sort_level_of_result_type(env: &Environment, ty: &Expr, declared: &[Name]) -> Option<Level> {
    let head = ty.get_app_fn();
    let ExprKind::Const(tname, tlevels) = head.kind() else {
        return None;
    };
    let iv = env.get_inductive(tname)?;
    if iv.level_params.len() != tlevels.len() || !levels_are_declared(tlevels, declared) {
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
    let result = l.substitute(&subst);
    levels_are_declared(std::slice::from_ref(&result), declared).then_some(result)
}

fn levels_are_declared(levels: &[Level], declared: &[Name]) -> bool {
    levels.iter().all(|level| {
        let mut parameters = Vec::new();
        level.collect_params(&mut parameters);
        parameters
            .iter()
            .all(|parameter| declared.contains(parameter))
    })
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

/// Where one of `f`'s arguments comes from in a recursive recursor call, by
/// the def's binder position (outermost first).
#[derive(Clone, Copy)]
enum FArgSource {
    /// A fixed binder (outside the major, threaded by no recursor argument):
    /// its original-telescope BVar index.
    Fixed(usize),
    /// The recursor argument after the prefix: 0 = major, `1 + i` = extra `i`.
    RecArg(usize),
}

/// One of `f`'s arguments in a fold-back, at new-telescope depth 0.
enum FArg {
    /// A fixed binder: the same variable at every recursive call.
    Fixed(Expr),
    /// The recursive call's own argument after the prefix (0 = major).
    RecArg(usize),
}

/// Folds recursive recursor calls back into `f`-applications.
struct RecFoldBack<'a> {
    rec_name: &'a Name,
    rec_levels: &'a [Level],
    /// σ-mapped params+motive+minors at new-telescope depth 0.
    prefix: &'a [Expr],
    f_name: &'a Name,
    f_levels: &'a [Level],
    /// `f`'s arguments in binder order.
    f_args: &'a [FArg],
}

impl RecFoldBack<'_> {
    /// `f`'s argument list for a recursive call whose arguments after the
    /// prefix are `rec_args` (major, then extras, then any over-application).
    /// A call that leaves an argument `f` needs unsupplied folds only when
    /// the missing ones are `f`'s trailing arguments (a partial application
    /// of `f`); otherwise it is `None`.
    fn f_application(&self, rec_args: &[Expr], depth: u32) -> Option<Expr> {
        let mut folded = Expr::const_(self.f_name.clone(), self.f_levels.to_vec());
        let mut used = 0usize;
        for (pos, fa) in self.f_args.iter().enumerate() {
            match fa {
                FArg::Fixed(v) => folded = Expr::app(folded, lift_bvars(v, depth)),
                FArg::RecArg(i) => match rec_args.get(*i) {
                    Some(ea) => {
                        folded = Expr::app(folded, self.apply(ea, depth)?);
                        used = used.max(i + 1);
                    }
                    // Partial: every remaining `f` argument must be a recursor
                    // argument the call also leaves out, in recursor order.
                    None => {
                        let rest = &self.f_args[pos..];
                        let in_order = rest.iter().enumerate().all(
                            |(o, r)| matches!(r, FArg::RecArg(ri) if *ri == rec_args.len() + o),
                        );
                        return in_order.then_some(folded);
                    }
                },
            }
        }
        for ea in rec_args.get(used..).unwrap_or_default() {
            folded = Expr::app(folded, self.apply(ea, depth)?);
        }
        Some(folded)
    }

    /// Replace every `Rec prefix… major extras…` spine with `f`'s
    /// application in binder order. `None` when a `Rec` occurrence survives
    /// in any unfoldable position — the equation would leak a raw recursor
    /// into goals, so the whole synthesis is abandoned.
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
                        return self.f_application(&eargs[self.prefix.len()..], depth);
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

#[cfg(test)]
#[path = "rec_equations_tests.rs"]
mod tests;

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Make the native path's EAGER IO model agree with Lean where it can, and
//! refuse to build where it cannot.
//!
//! The native runtime has no world token: an `IO α` value is represented by
//! the result of running it, so EVALUATING an `IO` expression performs its
//! effect (`native_build`'s module doc, and the `l_Bind_bind` shim that applies
//! the continuation to an already-executed action). Lean's `IO α` is an action:
//! evaluating it runs nothing, and `bind` runs it. The two models agree exactly
//! when every `IO` expression is evaluated at the moment Lean would run it — as
//! the action of the `bind` that sequences it, or as a function's result.
//! Measured 2026-09-24/25 through `clean run` (pinned Lean v4.30.0-rc2 in
//! brackets), each at exit status 0:
//!
//! * a non-final `if c then IO.println "big" else IO.println "small"` in a `do`
//!   block printed `big` AND `small` [`small`]: the `if` became the call
//!   `l_ite(c, IO.println "big", IO.println "small")`, whose arguments were
//!   both evaluated;
//! * `if false then IO.println "never" else pure ()` printed `never` [nothing];
//! * `let a := IO.println "A"; IO.println "B"; a; a` printed `A B` [`B A A`]:
//!   the action ran once, at its `let`;
//! * a non-final `match n with | 0 => IO.println "zero" | _ => …` ran its
//!   nullary arm for every `n`: the arm is an evaluated argument of
//!   `l_Nat_casesOn`.
//!
//! Two layers close it. This file is the first: [`rewrite_for_eager_io`]
//! rewrites the kernel value, before lowering, into a form whose eager
//! evaluation IS Lean's order. Both rewrites are equations of Lean's semantics
//! (β/ζ-conversions), never approximations:
//!
//! * **ζ for actions.** `let x : IO α := v; b` becomes `b[v/x]`, and so does
//!   the β-redex `(fun (x : IO α) => b) v`. Lean runs `v` at each use of `x`,
//!   so each use now evaluates it there — zero times, once, or twice.
//! * **Thunked branches.** A branch form whose result is an action —
//!   `ite`/`cond`, `<I>.casesOn`, and a single-motive `<I>.rec` — is rewritten
//!   so that every branch becomes a `Unit`-thunk and the selected thunk is
//!   forced once:
//!
//!   ```text
//!   ite (IO α) c h t e
//!     ~>  (fun (k : Unit → IO α) => k ()) (ite (Unit → IO α) c h (fun _ => t) (fun _ => e))
//!   ```
//!
//!   Evaluating the branch form now evaluates two closures and selects one;
//!   the only effect is the forced one, at the point the original expression
//!   was evaluated. This does not depend on whether the LCNF lowering happens
//!   to turn the branch form into a `Cases` (it does in return position and
//!   does not in argument position): either way the unselected arm is a
//!   closure nobody applies. For a recursor the induction hypotheses become
//!   thunks too, and each USE `ih` becomes `ih ()`, so the recursion's effects
//!   run where the arm uses them, never where the lowering computes the IH.
//!
//! The second layer, `native_eager_io_check`, audits the rewritten value and
//! refuses, with a named error, every shape the eager model still cannot run
//! in Lean's order.

use clean_kernel::{
    BinderInfo, ConstantInfo, ConstantKind, Environment, Expr, ExprKind, Name, RecursorArgOrder,
};

use crate::native_eager_io_check::{check_eager_io, mentions_actions, EagerIoRefusal};
use crate::native_rec_split_audit::{check_recursion_split, RecursionSplitRefusal};
use crate::native_string_carrier_audit::{check_string_carrier_in_env, StringCarrierRefusal};

/// Type constructors whose applications are actions the eager model runs on
/// evaluation, with the number of arguments that makes an ACTION type (not the
/// monad itself): `IO α`, `BaseIO α`, `EIO ε α`.
const ACTION_HEADS: &[(&str, usize)] = &[("IO", 1), ("BaseIO", 1), ("EIO", 2)];

/// Bound on the δ/β head-unfolding steps [`is_action_type`] takes. Every
/// realistic alias (`abbrev M := IO`, `Id (IO α)`) needs one or two.
const UNFOLD_FUEL: usize = 32;

/// Split an application into its head and arguments (in order), looking
/// through metadata on the spine.
pub(crate) fn spine(e: &Expr) -> (&Expr, Vec<&Expr>) {
    let mut args = Vec::new();
    let mut cur = e.strip_mdata();
    while let ExprKind::App(f, a) = cur.kind() {
        args.push(a.as_ref());
        cur = f.as_ref().strip_mdata();
    }
    args.reverse();
    (cur, args)
}

/// Contract head β-redexes: `(fun x => b) a rest..` to `b[a] rest..`.
fn head_beta(e: &Expr) -> Expr {
    let (head, args) = spine(e);
    let mut head = head.clone();
    let mut consumed = 0;
    for arg in &args {
        let ExprKind::Lam(_, _, body) = head.strip_mdata().kind() else {
            break;
        };
        head = body.instantiate(arg);
        consumed += 1;
    }
    Expr::apps(head, args[consumed..].iter().map(|a| (*a).clone()))
}

/// One δ step on the head of `e`: unfold a head constant that is a
/// `Definition` (never an opaque, theorem or axiom), then contract the β-redex
/// that exposes. `None` when the head does not unfold.
fn unfold_head(env: &Environment, e: &Expr) -> Option<Expr> {
    let (head, args) = spine(e);
    let ExprKind::Const(name, levels) = head.kind() else {
        return None;
    };
    let info = env.get_const(name)?;
    if info.kind != ConstantKind::Definition || info.level_params.len() != levels.len() {
        return None;
    }
    let value = info.value.as_ref()?;
    let levels: Vec<_> = levels.iter().cloned().collect();
    let value = value.instantiate_level_params_direct(&info.level_params, &levels);
    Some(head_beta(&Expr::apps(
        value,
        args.into_iter().cloned().collect::<Vec<_>>(),
    )))
}

/// Is `ty` an action type (`IO α`, `BaseIO α`, `EIO ε α`), after unfolding
/// definitions and β-redexes at its head?
///
/// Purely syntactic apart from δ: an action type can only be reached from a
/// definition that unfolds to one, because `IO` is an axiom and no inductive,
/// opaque or axiom is definitionally an `IO` application. Loose bound
/// variables are fine — only the head is inspected.
pub(crate) fn is_action_type(env: &Environment, ty: &Expr) -> bool {
    let mut cur = head_beta(ty);
    for _ in 0..UNFOLD_FUEL {
        let (head, args) = spine(&cur);
        if let ExprKind::Const(name, _) = head.kind() {
            let name = name.to_string();
            if let Some(&(_, arity)) = ACTION_HEADS.iter().find(|(h, _)| *h == name) {
                return args.len() >= arity;
            }
        }
        match unfold_head(env, &cur) {
            Some(next) => cur = next,
            None => return false,
        }
    }
    false
}

/// Strip leading `Pi` binders (unfolding a definition at the head when it
/// hides one) and return the codomain together with the binder count.
fn pi_codomain(env: &Environment, ty: &Expr) -> (Expr, usize) {
    let mut cur = ty.strip_mdata().clone();
    let mut binders = 0;
    for _ in 0..UNFOLD_FUEL * 4 {
        let next = match cur.kind() {
            ExprKind::Pi(_, _, body) => {
                binders += 1;
                body.as_ref().strip_mdata().clone()
            }
            ExprKind::MData(_, inner) => inner.as_ref().clone(),
            _ => match unfold_head(env, &cur) {
                Some(next) if matches!(next.strip_mdata().kind(), ExprKind::Pi(..)) => {
                    next.strip_mdata().clone()
                }
                _ => break,
            },
        };
        cur = next;
    }
    (cur, binders)
}

/// Is `ty` a function type whose final codomain is an action type
/// (`String → IO Unit`, `Unit → IO α`)?
pub(crate) fn is_action_returning(env: &Environment, ty: &Expr) -> bool {
    let (codomain, binders) = pi_codomain(env, ty);
    binders > 0 && is_action_type(env, &codomain)
}

/// Is `ty` a sort or a type family (`Sort u`, `α → Sort u`)? Arguments of
/// such a type are types, which carry no runtime effect.
pub(crate) fn is_type_like(env: &Environment, ty: &Expr) -> bool {
    let (codomain, _) = pi_codomain(env, ty);
    matches!(codomain.kind(), ExprKind::Sort(_))
}

/// Rewrite a declaration's value so eager evaluation runs its `IO` effects in
/// Lean's order (see the module doc). Terms with no action in them come back
/// structurally unchanged.
pub(crate) fn rewrite_for_eager_io(env: &Environment, value: &Expr) -> Expr {
    Rewriter::new(env).rw(value)
}

/// Why the native path refuses to compile a declaration's value.
#[derive(Debug, thiserror::Error)]
pub(crate) enum NativeBodyRefusal {
    #[error("native kernel-value Bool normalization for `{decl}` refused: {detail}")]
    KernelBool { decl: Name, detail: String },
    /// An action the eager IO model cannot run in Lean's order.
    #[error(transparent)]
    EagerIo(#[from] EagerIoRefusal),
    /// A recursion that reads the fields of an argument it generalized.
    #[error(transparent)]
    RecursionSplit(#[from] RecursionSplitRefusal),
    /// A body that builds or takes apart the runtime's byte-string `String`
    /// as the prelude's constructor cell.
    #[error(transparent)]
    StringCarrier(#[from] StringCarrierRefusal),
}

/// The value the native path compiles for `info`: audited for a `String`
/// used as a constructor cell (`native_string_carrier_audit`) and for the
/// generalized-split recursion shape (`native_rec_split_audit`), rewritten for
/// the eager IO model and audited, or refused with a named error. A value that
/// mentions no action and no monad axiom skips the IO rewrite — there is
/// nothing to rewrite and nothing to audit there.
///
/// `inline_env` is the environment the monad inlining reduces in
/// (`native_monad_inline::inlining_env`): `env` with every constant whose
/// compiled meaning is not its value hidden.
pub(crate) fn prepare_native_constant(
    env: &Environment,
    inline_env: &Environment,
    info: &ConstantInfo,
    meaning: clean_compiler::CodeMeaning,
) -> Result<ConstantInfo, NativeBodyRefusal> {
    // Monad operations over a closed instance are inlined to the instance's
    // field first (`native_monad_inline.rs`): the lowering must never build a
    // monad dictionary, and `IO`'s `bind` must reach the eager rewrite as
    // `IO.bind`. Definitional, so the value computed is unchanged.
    let mut info = info.clone();
    if info.kind != ConstantKind::Theorem {
        if let Some(value) = &info.value {
            info.value = Some(crate::native_monad_inline::inline_monad_instances(
                inline_env, value,
            ));
        }
        if let Some(value) =
            crate::native_kernel_bool::rewrite(env, &info, meaning).map_err(|detail| {
                NativeBodyRefusal::KernelBool {
                    decl: info.name.clone(),
                    detail,
                }
            })?
        {
            info.value = Some(value);
        }
    }
    let info = &info;
    if let Some(value) = &info.value {
        // A theorem's value is a proof, which `constant_to_decl` never lowers.
        if info.kind != ConstantKind::Theorem {
            check_string_carrier_in_env(env, &info.name, value)?;
        }
        check_recursion_split(env, &info.name, value)?;
    }
    let Some(value) = info.value.as_ref().filter(|v| mentions_actions(env, v)) else {
        return Ok(info.clone());
    };
    let rewritten = rewrite_for_eager_io(env, value);
    check_eager_io(env, &info.name, &rewritten)?;
    let mut prepared = info.clone();
    prepared.value = Some(rewritten);
    Ok(prepared)
}

/// Is `head args` a branch form whose result is an action — one the rewrite
/// thunks? After the rewrite, one that is still present is a shape the
/// rewrite declined, and its arms are evaluated arguments.
pub(crate) fn is_action_branch_form(env: &Environment, head: &Expr, args: &[Expr]) -> bool {
    let ExprKind::Const(name, _) = head.kind() else {
        return false;
    };
    match (name.to_string().as_str(), args.len()) {
        ("ite", 5) | ("cond", 4) => is_action_type(env, &args[0]),
        ("dite", _) => false,
        (_, nargs) => Rewriter::new(env)
            .eliminator_layout(name, nargs)
            .is_some_and(
                |layout| match peel_lams(&args[layout.motive], layout.motive_binders) {
                    Some((_, body)) => is_action_type(env, &body),
                    // A motive that is not a literal `fun`: the rewrite cannot see
                    // its result type, so treat the form as action-valued whenever
                    // the motive mentions an action at all.
                    None => mentions_actions(env, &args[layout.motive]),
                },
            ),
    }
}

struct Rewriter<'a> {
    env: &'a Environment,
    /// `Unit`, the thunk argument type.
    unit_ty: Expr,
    /// `Unit.unit`, the argument that forces a thunk.
    unit_val: Expr,
}

/// The branch forms [`Rewriter::thunk`] knows how to thunk, with where their
/// pieces sit in the argument list.
struct EliminatorLayout {
    /// Index of the motive argument.
    motive: usize,
    /// Number of `fun` binders the motive takes (indices + major).
    motive_binders: usize,
    /// For each minor: its argument index, its field count and its IH count.
    minors: Vec<(usize, usize, usize)>,
    /// Argument indices of the indices and then the major premise, in order.
    targets: Vec<usize>,
}

impl<'a> Rewriter<'a> {
    fn new(env: &'a Environment) -> Self {
        Self {
            env,
            unit_ty: Expr::const_(Name::from_string("Unit"), vec![]),
            unit_val: Expr::const_(Name::from_string("Unit.unit"), vec![]),
        }
    }

    fn rw(&self, e: &Expr) -> Expr {
        match e.kind() {
            ExprKind::Let(name, ty, val, body, non_dep) => {
                let val = self.rw(val);
                if is_action_type(self.env, ty) {
                    // ζ: Lean runs a named action at each USE, never at the
                    // binding, so each use evaluates the action itself.
                    return self.rw(&body.instantiate(&val));
                }
                Expr::let_named(
                    name.clone(),
                    ty.as_ref().clone(),
                    val,
                    self.rw(body),
                    *non_dep,
                )
            }
            ExprKind::Lam(bd, ty, body) => Expr::lam(*bd, ty.as_ref().clone(), self.rw(body)),
            ExprKind::MData(data, inner) => Expr::mdata(data.clone(), self.rw(inner)),
            ExprKind::Proj(s, idx, inner) => Expr::proj(s.clone(), *idx, self.rw(inner)),
            ExprKind::App(_, _) => self.rw_app(e),
            _ => e.clone(),
        }
    }

    fn rw_app(&self, e: &Expr) -> Expr {
        let (head, args) = spine(e);
        // ζ through a β-redex whose binder is an action: `have`-style bindings.
        if let ExprKind::Lam(_, ty, body) = head.kind() {
            if is_action_type(self.env, ty) {
                let reduct = body.instantiate(&self.rw(args[0]));
                return self.rw(&Expr::apps(reduct, args[1..].iter().map(|a| (*a).clone())));
            }
        }
        let head = self.rw(head);
        let args: Vec<Expr> = args.iter().map(|a| self.rw(a)).collect();
        self.thunk(&head, &args)
            .unwrap_or_else(|| Expr::apps(head, args))
    }

    /// `Unit → ty`, with `ty` moved under the new binder.
    fn thunk_type(&self, ty: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.unit_ty.clone(), ty.lift(1))
    }

    /// `fun (_ : Unit) => body`, with `body` moved under the new binder.
    fn thunk_of(&self, body: &Expr) -> Expr {
        Expr::lam(BinderInfo::Default, self.unit_ty.clone(), body.lift(1))
    }

    /// `(fun (k : thunk_ty) => k ()) thunk` — force the selected thunk once.
    fn force(&self, thunk_ty: Expr, thunk: Expr) -> Expr {
        let forcer = Expr::lam(
            BinderInfo::Default,
            thunk_ty,
            Expr::app(Expr::bvar(0), self.unit_val.clone()),
        );
        Expr::app(forcer, thunk)
    }

    /// Thunk an action-valued branch form, or `None` when `head args` is not
    /// one (or is one in a shape this rewrite does not handle — the checker
    /// then refuses whatever eager hazard remains).
    fn thunk(&self, head: &Expr, args: &[Expr]) -> Option<Expr> {
        let ExprKind::Const(name, _) = head.kind() else {
            return None;
        };
        match (name.to_string().as_str(), args.len()) {
            // ite.{u} {α : Sort u} (c : Prop) [Decidable c] (t e : α)
            ("ite", 5) => self.thunk_select(head, args, 0, &[3, 4]),
            // cond.{u} {α : Type u} (c : Bool) (x y : α)
            ("cond", 4) => self.thunk_select(head, args, 0, &[2, 3]),
            _ => {
                let layout = self.eliminator_layout(name, args.len())?;
                self.thunk_eliminator(head, args, &layout)
            }
        }
    }

    fn thunk_select(
        &self,
        head: &Expr,
        args: &[Expr],
        ty_idx: usize,
        branches: &[usize],
    ) -> Option<Expr> {
        let ty = &args[ty_idx];
        if !is_action_type(self.env, ty) {
            return None;
        }
        let thunk_ty = self.thunk_type(ty);
        let mut new_args = args.to_vec();
        new_args[ty_idx] = thunk_ty.clone();
        for &b in branches {
            new_args[b] = self.thunk_of(&args[b]);
        }
        Some(self.force(thunk_ty, Expr::apps(head.clone(), new_args)))
    }

    /// The layout of a saturated `<I>.casesOn` (params, motive, indices,
    /// major, minors) or single-motive `<I>.rec` (params, motive, minors,
    /// indices, major) application of exactly `nargs` arguments.
    fn eliminator_layout(&self, name: &Name, nargs: usize) -> Option<EliminatorLayout> {
        let full = name.to_string();
        if let Some(ind_name) = full.strip_suffix(".casesOn") {
            let ind = self.env.get_inductive(&Name::from_string(ind_name))?;
            let (np, ni) = (ind.num_params as usize, ind.num_indices as usize);
            let nc = ind.constructor_names.len();
            if nargs != np + 1 + ni + 1 + nc {
                return None;
            }
            let fields = ind
                .constructor_names
                .iter()
                .map(|c| self.env.get_constructor(c).map(|cv| cv.num_fields as usize))
                .collect::<Option<Vec<_>>>()?;
            let first_minor = np + 1 + ni + 1;
            return Some(EliminatorLayout {
                motive: np,
                motive_binders: ni + 1,
                minors: fields
                    .into_iter()
                    .enumerate()
                    .map(|(i, nf)| (first_minor + i, nf, 0))
                    .collect(),
                targets: (np + 1..=np + 1 + ni).collect(),
            });
        }
        let rec = self.env.get_recursor(name)?;
        if rec.num_motives != 1
            || rec.arg_order != RecursorArgOrder::MajorAfterMinors
            || rec.rules.len() != rec.num_minors as usize
        {
            return None;
        }
        let (np, ni, nm) = (
            rec.num_params as usize,
            rec.num_indices as usize,
            rec.num_minors as usize,
        );
        if nargs != np + 1 + nm + ni + 1 {
            return None;
        }
        Some(EliminatorLayout {
            motive: np,
            motive_binders: ni + 1,
            minors: rec
                .rules
                .iter()
                .enumerate()
                .map(|(i, rule)| {
                    let ihs = rule.recursive_fields.iter().filter(|r| **r).count();
                    (np + 1 + i, rule.num_fields as usize, ihs)
                })
                .collect(),
            targets: (np + 1 + nm..np + 1 + nm + ni + 1).collect(),
        })
    }

    fn thunk_eliminator(
        &self,
        head: &Expr,
        args: &[Expr],
        layout: &EliminatorLayout,
    ) -> Option<Expr> {
        // The motive must be a literal `fun idx.. x => T` with `T` an action.
        let (motive_binders, motive_body) = peel_lams(&args[layout.motive], layout.motive_binders)?;
        if !is_action_type(self.env, &motive_body) {
            return None;
        }
        let mut new_args = args.to_vec();
        new_args[layout.motive] = rebuild_lams(&motive_binders, self.thunk_type(&motive_body));
        for &(idx, fields, ihs) in &layout.minors {
            new_args[idx] = self.thunk_minor(&args[idx], fields, ihs)?;
        }
        // The application's own type: the motive body at the actual indices
        // and major premise (`instantiate_rev` wants the innermost first).
        let targets: Vec<Expr> = layout
            .targets
            .iter()
            .rev()
            .map(|&i| args[i].clone())
            .collect();
        let result_ty = motive_body.instantiate_rev(&targets);
        Some(self.force(
            self.thunk_type(&result_ty),
            Expr::apps(head.clone(), new_args),
        ))
    }

    /// `fun fields ihs => b`  ~>  `fun fields (ihs : Unit → _) => fun _ => b[ih := ih ()]`.
    fn thunk_minor(&self, minor: &Expr, fields: usize, ihs: usize) -> Option<Expr> {
        let (mut binders, body) = peel_lams(minor, fields + ihs)?;
        for binder in binders.iter_mut().skip(fields) {
            binder.1 = self.thunk_type(&binder.1);
        }
        let body = force_bvars(&body, ihs as u32, 0, &self.unit_val);
        Some(rebuild_lams(&binders, self.thunk_of(&body)))
    }
}

/// A peeled `fun` binder: its binder data and type.
type Binder = (clean_kernel::BinderData, Expr);

/// Peel exactly `n` leading lambdas (looking through metadata), or `None`.
fn peel_lams(e: &Expr, n: usize) -> Option<(Vec<Binder>, Expr)> {
    let mut binders = Vec::with_capacity(n);
    let mut cur = e.strip_mdata();
    for _ in 0..n {
        let ExprKind::Lam(bd, ty, body) = cur.kind() else {
            return None;
        };
        binders.push((*bd, ty.as_ref().clone()));
        cur = body.as_ref().strip_mdata();
    }
    Some((binders, cur.clone()))
}

/// Rebuild `fun binders => body`.
fn rebuild_lams(binders: &[Binder], body: Expr) -> Expr {
    binders
        .iter()
        .rev()
        .fold(body, |acc, (bd, ty)| Expr::lam(*bd, ty.clone(), acc))
}

/// Replace every occurrence of the loose bound variables `depth..depth+count`
/// in `e` with that variable applied to `unit` — the uses of thunked IHs.
fn force_bvars(e: &Expr, count: u32, depth: u32, unit: &Expr) -> Expr {
    if count == 0 || e.loose_bvar_range() <= depth {
        return e.clone();
    }
    match e.kind() {
        ExprKind::BVar(i) if *i >= depth && *i < depth + count => {
            Expr::app(e.clone(), unit.clone())
        }
        ExprKind::App(f, a) => Expr::app(
            force_bvars(f, count, depth, unit),
            force_bvars(a, count, depth, unit),
        ),
        ExprKind::Lam(bd, ty, body) => Expr::lam(
            *bd,
            force_bvars(ty, count, depth, unit),
            force_bvars(body, count, depth + 1, unit),
        ),
        ExprKind::Pi(bd, ty, body) => Expr::pi(
            *bd,
            force_bvars(ty, count, depth, unit),
            force_bvars(body, count, depth + 1, unit),
        ),
        ExprKind::Let(name, ty, val, body, non_dep) => Expr::let_named(
            name.clone(),
            force_bvars(ty, count, depth, unit),
            force_bvars(val, count, depth, unit),
            force_bvars(body, count, depth + 1, unit),
            *non_dep,
        ),
        ExprKind::MData(data, inner) => {
            Expr::mdata(data.clone(), force_bvars(inner, count, depth, unit))
        }
        ExprKind::Proj(s, idx, inner) => {
            Expr::proj(s.clone(), *idx, force_bvars(inner, count, depth, unit))
        }
        _ => e.clone(),
    }
}

#[cfg(test)]
#[path = "native_eager_io_tests.rs"]
mod tests;

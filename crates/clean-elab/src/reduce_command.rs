// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `#reduce (proofs := true)? (types := true)? e`.
//!
//! # What pinned Lean does
//!
//! Lean 4.30.0-rc2's `Lean.Elab.Command.elabReduce`
//! (`Lean/Elab/BuiltinCommand.lean`) elaborates `e`, runs `Meta.check e`,
//! and logs `Lean.Meta.reduce e (skipProofs) (skipTypes)`
//! (`Lean/Meta/Reduce.lean`) at transparency `.all` with `smartUnfolding`
//! off. It never compiles or runs `e`, and asks for no `Repr`. `reduce` is
//!
//! ```text
//! visit e := checkCache e fun _ => Core.withIncRecDepth do
//!   if skipTypes && (← isType e) then return e
//!   else if skipProofs && (← isProof e) then return e
//!   else match ← whnf e with …   -- reduce, then visit the pieces
//! ```
//!
//! and `isType e` (`Lean/Meta/InferType.lean`) first asks `isTypeQuick e`,
//! a purely syntactic test: `.sort` and `.forallE` are types, and so is
//! `c a₁ … aₙ` when the declared type of the constant `c` is, syntactically,
//! `n` binders followed by a `.sort` (`isTypeQuickApp` / `isArrowType`). When
//! that test says `true`, nothing is inferred, nothing is put in weak head
//! normal form, and `reduce` returns `e` itself.
//!
//! # What Clean does, and what it does NOT claim
//!
//! Clean does not implement `Meta.reduce`, Lean's `whnf`, its literal folds
//! (`reduceNat?` and its `exponentiation.threshold`) or its recursion-depth
//! and heartbeat accounting. The kernel's `whnf` is no stand-in for it: it
//! takes shortcuts `Meta.whnf` does not (GMP `Nat.pow` past Lean's threshold
//! of 256, native `String`/`Char`/`Int` reducers, `Nat` folds over terms with
//! free variables), so a kernel-normalized result says nothing about whether
//! Lean's reduction finishes inside `maxRecDepth`.
//!
//! Clean therefore accepts a `#reduce` only in the one case where `reduce`
//! does no reduction at all: no `(types := true)` flag, and Lean's
//! `isTypeQuick`, transcribed below over the elaborated term, says `true`.
//! `reduce` then returns the term unchanged after one `visit`, so Lean's work
//! is `Meta.check` (Clean's stand-in is the kernel check every `#check`
//! gets) and one syntactic test. The term's depth is also capped at
//! [`TERM_DEPTH_CAP`], and a `maxRecDepth` / `maxHeartbeats` set in scope is
//! refused, since Clean does not model what a lowered bound refuses. Every
//! other `#reduce` is the named refusal [`ElabError::ReduceUnmodeled`]: a
//! refusal where Lean accepts is a known gap (`#reduce 2 + 3`,
//! `#reduce "".data`, `#reduce (types := true) Nat`, `#reduce T 5000` for a
//! defined `T`), an acceptance where Lean
//! fails is the defect this module exists to prevent.
//!
//! Lean's elaborator and linters can still fail before or around `reduce`
//! where Clean's elaborator succeeds, so three more guards keep this command
//! from accepting such a term: a universe parameter is refused (Clean binds
//! an undeclared `u` where Lean says `unknown universe level`); so is a term
//! whose constants, or the constants of their types, transitively, include
//! anything but inductive types, constructors and axioms (`definition_free`:
//! Lean's `isDefEq` and its linters unfold definitions there, measured to
//! exhaust `maxRecDepth` where Clean's kernel finds it cheap); and so is a
//! term whose type-check needs any conversion (`conversion_free`). Beyond
//! those, the test runs on Clean's elaborated term, which is assumed to have
//! Lean's shape, as every `#check` assumes: this is an engineering argument
//! over measured cases, not a proof that Lean accepts. The logged message is
//! Clean's rendering of that term, NOT Lean's delaborated text, so a
//! `#guard_msgs` that would compare it is refused
//! (`crate::guard_msgs::conclude`), never judged.

use std::collections::HashMap;

use clean_kernel::expr::ExprKind;
use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr, TypeChecker};

use crate::error::ElabError;

/// Largest depth of the elaborated term an accepted `#reduce` may have.
pub(crate) const TERM_DEPTH_CAP: usize = 64;

/// The options in scope that change what Lean's `#reduce` would refuse.
pub(crate) const BOUND_OPTIONS: [&str; 2] = ["maxRecDepth", "maxHeartbeats"];

/// Options that change whether Lean's `#reduce` FAILS without changing the
/// reduction: `warningAsError` turns the linter and deprecation warnings Lean
/// emits while elaborating the term (`constructorNameAsVariable`, unused
/// variables, `@[deprecated]`) into errors, and Clean models none of those
/// warnings, so a `#reduce` in its scope is refused whatever its value.
pub(crate) const WARNING_OPTIONS: [&str; 1] = ["warningAsError"];

/// Which `(… := true)` groups the command wrote.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct ReduceFlags {
    /// `(types := true)`: Lean's `skipTypes := false`.
    pub(crate) reduce_types: bool,
    /// `(proofs := true)`: Lean's `skipProofs := false`.
    pub(crate) reduce_proofs: bool,
}

/// The output of an accepted `#reduce`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReduceResult {
    /// Clean's rendering of the term, which Lean's `reduce` returned
    /// unchanged (not Lean's text).
    pub value: String,
}

impl std::fmt::Display for ReduceResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

fn refuse(reason: impl Into<String>) -> ElabError {
    ElabError::ReduceUnmodeled {
        reason: reason.into(),
    }
}

/// `#reduce` of the already-elaborated `expr`. `bound_option_set` names an
/// option of [`BOUND_OPTIONS`] or [`WARNING_OPTIONS`] set in scope, if any.
///
/// # Errors
///
/// [`ElabError::KernelCheckFailed`] when `expr` does not kernel-check, and
/// [`ElabError::ReduceUnmodeled`] whenever `expr` is outside the class the
/// module documentation describes.
pub(crate) fn elab_reduce(
    env: &Environment,
    expr: &Expr,
    flags: ReduceFlags,
    bound_option_set: Option<&str>,
) -> Result<ReduceResult, ElabError> {
    if let Some(option) = bound_option_set {
        if WARNING_OPTIONS.contains(&option) {
            return Err(refuse(format!(
                "`{option}` is set, and Clean does not model the linter and deprecation \
                 warnings it turns into errors"
            )));
        }
        return Err(refuse(format!(
            "`{option}` is set, and Clean does not model what Lean's reduction refuses under \
             a changed bound"
        )));
    }
    if flags.reduce_types {
        return Err(refuse(
            "under `(types := true)` Lean's `Meta.reduce` reduces types too, and Clean does \
             not model that reduction",
        ));
    }
    if term_depth(expr, TERM_DEPTH_CAP).is_none() {
        return Err(refuse(format!(
            "the term is deeper than {TERM_DEPTH_CAP}, and Clean does not bound Lean's \
             recursion depth for it"
        )));
    }
    // Lean's `Meta.check e` before reducing; the type itself is not needed.
    let _checked_type =
        TypeChecker::new(env)
            .infer_type(expr)
            .map_err(|e| ElabError::KernelCheckFailed {
                name: Name::from_string("_reduce"),
                detail: e.to_string(),
            })?;
    if is_type_quick(env, expr) != LBool::True {
        return Err(refuse(
            "the term is not a type by Lean's syntactic `isTypeQuick`, so `Meta.reduce` \
             would reduce it, and Clean does not model Lean's reduction (its `whnf`, literal \
             folds and recursion-depth bound)",
        ));
    }
    // Clean's elaborator binds a universe name no `universe` command declared
    // (`#check Sort u`), where pinned Lean fails with `unknown universe level
    // `u``; Clean does not track which names are declared here, so any
    // written universe parameter is refused. Clean's universe metavariables
    // (`?u_N`, `crate::level_mint`) are what Lean's `levelMVarToParam` turns
    // into `u_1`, … and are accepted.
    if written_level_param(expr) {
        return Err(refuse(
            "the term mentions a universe parameter, and Clean does not check that it is \
             declared as Lean does (`unknown universe level`)",
        ));
    }
    definition_free(env, expr)?;
    conversion_free(&TypeChecker::new(env), expr)?;
    Ok(ReduceResult {
        value: format!("{expr}"),
    })
}

/// Whether `expr` mentions a universe parameter that is not one of Clean's
/// minted universe metavariables.
fn written_level_param(expr: &Expr) -> bool {
    if !expr.has_level_param_quick() {
        return false;
    }
    let mut params = Vec::new();
    let mut seen = std::collections::HashSet::new();
    let mut stack = vec![expr];
    while let Some(e) = stack.pop() {
        if !seen.insert(std::ptr::from_ref(e) as usize) || !e.has_level_param_quick() {
            continue;
        }
        match e.kind() {
            ExprKind::Sort(level) => level.collect_params(&mut params),
            ExprKind::Const(_, levels) => {
                for level in levels.iter() {
                    level.collect_params(&mut params);
                }
            }
            ExprKind::App(f, a) => stack.extend([f.as_ref(), a.as_ref()]),
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                stack.extend([ty.as_ref(), body.as_ref()]);
            }
            ExprKind::Let(_, ty, val, body, _) => {
                stack.extend([ty.as_ref(), val.as_ref(), body.as_ref()]);
            }
            ExprKind::Proj(_, _, s) | ExprKind::MData(_, s) => stack.push(s.as_ref()),
            // Any other node holding a level is refused below.
            _ => return true,
        }
    }
    params
        .iter()
        .any(|name| !crate::level_mint::is_reserved_level_name(&name.to_string()))
}

/// Most constants [`definition_free`] walks before refusing.
pub(crate) const CONSTANT_CLOSURE_CAP: usize = 4096;

/// Accept only a term whose constants, and the constants of their declared
/// types, transitively, are inductive types, constructors or axioms.
///
/// Pinned Lean's elaborator, `Meta.check` and its linters compare and
/// `whnf` the types of a term's pieces, and a definition there can make that
/// work arbitrarily deep where Clean's kernel finds it cheap: with `T : Nat →
/// Type` defined by recursion, `axiom n : T 5000`, `axiom f : T 5000 →
/// Type`, pinned Lean fails `#reduce f n` (even `example (n : T 5000) : T
/// 5000 := n`) with `maximum recursion depth has been reached`, and its
/// `constructorNameAsVariable` linter fails `#reduce (x : T 5000) → Nat` the
/// same way. With no definition anywhere in those types there is nothing to
/// unfold, so the comparisons are structural.
fn definition_free(env: &Environment, expr: &Expr) -> Result<(), ElabError> {
    use clean_kernel::env::ConstantKind;
    use clean_kernel::expr::UsedConstants;
    let mut seen = std::collections::HashSet::new();
    let mut pending = std::collections::HashSet::new();
    expr.used_constants_dag(UsedConstants::WithProjectionStructures, &mut pending);
    let mut stack: Vec<Name> = pending.into_iter().collect();
    while let Some(name) = stack.pop() {
        if !seen.insert(name.clone()) {
            continue;
        }
        if seen.len() > CONSTANT_CLOSURE_CAP {
            return Err(refuse(format!(
                "its constants' types reach more than {CONSTANT_CLOSURE_CAP} constants, and \
                 Clean does not walk further"
            )));
        }
        let Some(info) = env.get_const(&name) else {
            return Err(refuse(format!("`{name}` is no constant the kernel knows")));
        };
        let family = env.get_inductive(&name).is_some() || env.get_constructor(&name).is_some();
        if !family && info.kind != ConstantKind::Axiom {
            return Err(refuse(format!(
                "it mentions `{name}`, which is neither an inductive type, a constructor nor an \
                 axiom, and Clean does not model what Lean's elaborator, `Meta.check` and \
                 linters spend unfolding it"
            )));
        }
        let mut used = std::collections::HashSet::new();
        info.type_
            .used_constants_dag(UsedConstants::WithProjectionStructures, &mut used);
        stack.extend(used.into_iter().filter(|n| !seen.contains(n)));
    }
    Ok(())
}

fn not_conversion_free(what: &str) -> ElabError {
    refuse(format!(
        "{what}, and Clean does not model what Lean's elaborator and `Meta.check` spend on \
         a conversion (`maximum recursion depth` on a deep unfolding)"
    ))
}

/// Accept only a term that type-checks with no conversion at all: every
/// argument's inferred type is syntactically the domain its function's
/// (syntactic) `Pi` type expects, up to level normalization. Pinned Lean's
/// elaborator and `Meta.check` can fail on a conversion Clean's kernel
/// decides quickly (`axiom f : T 5000 → Type`, `#reduce f (n : Nat)` with
/// `T 5000` unfolding to `Nat`: Lean hits `maximum recursion depth`), so a
/// term that needs one is refused. Lambda and `Pi` binders are opened with
/// kernel locals; every other node but a sort, a constant, a literal and a
/// local is refused (fail closed).
fn conversion_free(tc: &TypeChecker<'_>, e: &Expr) -> Result<(), ElabError> {
    let infer = |e: &Expr| {
        tc.infer_type(e)
            .map_err(|error| refuse(format!("the kernel could not infer a subterm: {error}")))
    };
    match e.kind() {
        ExprKind::Sort(_) | ExprKind::Const(..) | ExprKind::Lit(_) | ExprKind::FVar(_) => Ok(()),
        ExprKind::App(..) => {
            let head = e.get_app_fn();
            conversion_free(tc, head)?;
            let mut fn_type = infer(head)?;
            for arg in e.get_app_args() {
                conversion_free(tc, arg)?;
                let ExprKind::Pi(_, domain, body) = fn_type.kind() else {
                    return Err(not_conversion_free(
                        "a function's type is not syntactically a `Pi`",
                    ));
                };
                if !syntactically_equal(&infer(arg)?, domain) {
                    return Err(not_conversion_free(
                        "an argument's type is not syntactically its function's domain",
                    ));
                }
                fn_type = body.instantiate(arg);
            }
            Ok(())
        }
        ExprKind::Lam(bd, ty, body) | ExprKind::Pi(bd, ty, body) => {
            conversion_free(tc, ty)?;
            let id = tc.push_binder_local(Name::anon(), ty.as_ref().clone(), *bd);
            let opened = body.instantiate(&Expr::fvar(id));
            let result = conversion_free(tc, &opened);
            tc.pop_binder_local();
            result
        }
        _ => Err(not_conversion_free(
            "the term holds a `let`, a projection or metadata",
        )),
    }
}

/// Structural equality, binder annotations ignored and universe levels
/// compared after normalization.
fn syntactically_equal(a: &Expr, b: &Expr) -> bool {
    match (a.kind(), b.kind()) {
        (ExprKind::Sort(l), ExprKind::Sort(m)) => l.normalize() == m.normalize(),
        (ExprKind::Const(n, ls), ExprKind::Const(m, ms)) => {
            n == m
                && ls.len() == ms.len()
                && ls
                    .iter()
                    .zip(ms.iter())
                    .all(|(l, m)| l.normalize() == m.normalize())
        }
        (ExprKind::App(f, x), ExprKind::App(g, y)) => {
            syntactically_equal(f, g) && syntactically_equal(x, y)
        }
        (ExprKind::Lam(_, t, s), ExprKind::Lam(_, u, v))
        | (ExprKind::Pi(_, t, s), ExprKind::Pi(_, u, v)) => {
            syntactically_equal(t, u) && syntactically_equal(s, v)
        }
        _ => a == b,
    }
}

/// Lean's three-valued answer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum LBool {
    True,
    False,
    Undef,
}

/// `Lean.Meta.isTypeQuick` (Lean 4.30.0-rc2 `Lean/Meta/InferType.lean`),
/// case for case. A closed term has no metavariables and no free variables,
/// so the `.mvar` and `.fvar` cases are `Undef` here (fail closed).
pub(crate) fn is_type_quick(env: &Environment, e: &Expr) -> LBool {
    match e.kind() {
        ExprKind::Sort(_) | ExprKind::Pi(..) => LBool::True,
        ExprKind::Lit(_) | ExprKind::Lam(..) => LBool::False,
        ExprKind::Let(_, _, _, body, _) => is_type_quick(env, body),
        ExprKind::MData(_, inner) => is_type_quick(env, inner),
        ExprKind::Const(name, _) => const_is_arrow_type(env, name, 0),
        ExprKind::App(f, _) => is_type_quick_app(env, f, 1),
        _ => LBool::Undef,
    }
}

/// `isTypeQuickApp f n`: whether `f` applied to `n` arguments is a type.
fn is_type_quick_app(env: &Environment, f: &Expr, arity: usize) -> LBool {
    match f.kind() {
        ExprKind::Const(name, _) => const_is_arrow_type(env, name, arity),
        ExprKind::App(g, _) => is_type_quick_app(env, g, arity + 1),
        ExprKind::MData(_, inner) => is_type_quick_app(env, inner, arity),
        ExprKind::Let(_, _, _, body, _) => is_type_quick_app(env, body, arity),
        ExprKind::Lam(..) if arity == 0 => LBool::False,
        ExprKind::Lam(_, _, body) => is_type_quick_app(env, body, arity - 1),
        _ => LBool::Undef,
    }
}

/// `isArrowType (inferConstType c) n`. Instantiating the universe parameters
/// does not change the syntactic shape the test reads.
fn const_is_arrow_type(env: &Environment, name: &Name, arity: usize) -> LBool {
    match env.get_const(name) {
        Some(info) => is_arrow_type(&info.type_, arity),
        None => LBool::Undef,
    }
}

/// `Lean.Meta.isArrowType`.
fn is_arrow_type(ty: &Expr, arity: usize) -> LBool {
    match (ty.kind(), arity) {
        (ExprKind::Sort(_), 0) => LBool::True,
        (ExprKind::Pi(..), 0) => LBool::False,
        (ExprKind::Pi(_, _, body), n) => is_arrow_type(body, n - 1),
        (ExprKind::Let(_, _, _, body, _), n) => is_arrow_type(body, n),
        (ExprKind::MData(_, inner), n) => is_arrow_type(inner, n),
        _ => LBool::Undef,
    }
}

/// `Some(depth)` of `e` when it is at most `cap`, `None` when it is deeper.
/// Shared subterms are measured once.
pub(crate) fn term_depth(e: &Expr, cap: usize) -> Option<usize> {
    fn go(e: &Expr, budget: usize, memo: &mut HashMap<usize, usize>) -> Option<usize> {
        let key = std::ptr::from_ref(e) as usize;
        if let Some(&depth) = memo.get(&key) {
            return (depth <= budget).then_some(depth);
        }
        let below = budget.checked_sub(1)?;
        let children: Vec<&Expr> = match e.kind() {
            ExprKind::App(f, a) => vec![f.as_ref(), a.as_ref()],
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                vec![ty.as_ref(), body.as_ref()]
            }
            ExprKind::Let(_, ty, val, body, _) => vec![ty.as_ref(), val.as_ref(), body.as_ref()],
            ExprKind::Proj(_, _, s) | ExprKind::MData(_, s) => vec![s.as_ref()],
            _ => Vec::new(),
        };
        let mut depth = 1;
        for child in children {
            depth = depth.max(go(child, below, memo)? + 1);
        }
        memo.insert(key, depth);
        Some(depth)
    }
    go(e, cap, &mut HashMap::new())
}

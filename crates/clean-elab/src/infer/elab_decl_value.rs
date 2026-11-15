// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Value-bearing declaration elaboration: Definition, Theorem, Axiom, Opaque
//!
//! Extracted from `elaborate_decl.rs` to keep files under 500 lines.
//! Each method is called from the corresponding match arm in
//! `ElabCtx::elab_decl_inner`.

use crate::ElabError;
use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprFolder, ExprVisitor, FVarId, Level, LevelVec};
use clean_parser::{
    Attribute, DeclModifiers, SurfaceBinder, SurfaceExpr, SurfaceName, SurfacePattern,
    TerminationHints, WhereLocalDef,
};
use std::collections::{HashMap, HashSet};

use super::elaborate_decl::PrivateNameKind;
use super::opaque_inhabitant::OpaqueInhabitant;
use super::{ElabCtx, ElabResult, RecursiveDefContext};

/// Normalize an equation-form declaration into the equivalent named-binder +
/// explicit-`match` shape, so the already-working structural-recursion lowering
/// (which resolves the decreasing argument against the declaration's *binders*)
/// fires for equation defs like:
///
/// ```text
/// def factorial : Nat → Nat
///   | 0 => 1
///   | Nat.succ n => (Nat.succ n) * factorial n
/// ```
///
/// The parser (`def_match_body`) desugars the equation arms into a value
/// `PatternMatchLambda([_x], Match(_x, arms))` with an **empty** declaration
/// `binders` list — the `Nat → Nat` lives in `ty`. Recursion *detection* still
/// works, but `setup_recursion` resolves the decreasing-arg position against
/// `binders`, which is empty, so no `RecursiveDefContext` is installed and the
/// self-name `factorial` is left as a placeholder typed `Nat`; `factorial n`
/// then over-applies and surfaces as `TooManyArguments`.
///
/// This helper lifts the synthetic `_x` lambda binder into a real declaration
/// binder by peeling one domain off the declaration arrow/Pi type, turning the
/// equation def into exactly the named-binder + `match` form that already
/// elaborates to a genuine `T.rec` application and kernel-checks.
///
/// Returns `Some((lifted_binders, new_return_ty, match_body))` when the
/// equation-form shape is recognized, or `None` to leave the declaration
/// untouched (the common, non-equation path).
///
/// SCOPE (slice 1): single decreasing argument. The parser always emits exactly
/// one synthetic `_x` binder, so multi-arg equation defs (parsed as a single
/// `_x` scrutinee matched against a `Prod.mk` tuple pattern) are intentionally
/// left alone: peeling a single domain off the type would not match the tuple
/// scrutinee, and tuple-`.rec` lowering is a separate follow-up. Multi-binder
/// pattern lambdas (which the def parser never produces) are likewise skipped.
///
/// Also reused by `try_elab_let_rec_lifted` (`infer/elab_core.rs`) to lift an
/// equation-form `where`/`let rec` helper's hidden `_x` scrutinee binder, so
/// such a helper routes through the identical structural-recursion lowering.
///
/// `Err` when the equations compile to a decision tree that never selects
/// some equation: Lean 4.8.0 refuses that definition ("redundant
/// alternative"), so no other lowering may be tried for it.
pub(in crate::infer) fn normalize_equation_def(
    env: &clean_kernel::Environment,
    idents: &PatternIdents<'_>,
    def_name: &SurfaceName,
    binders: &[SurfaceBinder],
    ty: Option<&SurfaceExpr>,
    val: &SurfaceExpr,
) -> Result<Option<(Vec<SurfaceBinder>, Option<SurfaceExpr>, SurfaceExpr)>, ElabError> {
    let mut redundant = None;
    let lifted = lift_equation_def(env, idents, def_name, binders, ty, val, &mut redundant);
    match redundant {
        Some(err) => Err(err),
        None => Ok(lifted),
    }
}

/// [`normalize_equation_def`]'s lifting; a redundant equation is reported
/// through `redundant` (and the lift is `None`).
fn lift_equation_def(
    env: &clean_kernel::Environment,
    idents: &PatternIdents<'_>,
    def_name: &SurfaceName,
    binders: &[SurfaceBinder],
    ty: Option<&SurfaceExpr>,
    val: &SurfaceExpr,
    redundant: &mut Option<ElabError>,
) -> Option<(Vec<SurfaceBinder>, Option<SurfaceExpr>, SurfaceExpr)> {
    // Trigger for the equation-def signature the parser emits: a
    // `PatternMatchLambda` value. Leading declaration binders (`def f (op : T)
    // (width : Nat) : A → B → C | …`) are allowed — they are kept in front of
    // the lifted equation-arg binders. This is exactly the `semVectorIntBinOp`
    // shape: explicit parameters before the multi-argument equation arrow.
    let SurfaceExpr::PatternMatchLambda(_span, lam_binders, lam_body) = val else {
        return None;
    };

    // Slice 1: arity-1 equation defs. The def parser always emits a single
    // synthetic `_x` binder regardless of arity (arity-N uses a tuple pattern
    // inside the single match), so gate on exactly one synthetic binder. This
    // keeps us conservative: it never fires for a user-written `fun | ...` with
    // its own binders, and defers multi-arg/tuple forms.
    let [lam_binder] = lam_binders.as_slice() else {
        return None;
    };
    if lam_binder.name != SurfaceName::pattern_lambda_binder() {
        return None;
    }

    // Multi-arg equation defs (`def f : A → B → C | a, b => ...`) are also
    // emitted by the parser as a single `_x` binder, but with arms whose
    // top-level pattern is a right-nested `Prod.mk` tuple over the multiple
    // arguments. Slices 2/3 lift that single `_x` into N named binders and
    // rewrite the tuple match into a single (or nested) single-scrutinee match,
    // so the *existing* sound single-arg `.rec` lowering fires.
    //
    // `normalize_equation_def_multiarg` recognizes the tuple shape and returns
    // the lifted form when it can do so soundly. When the shape is outside that
    // conservative envelope it returns `None`, and we fall back to the existing
    // (non-normalized) path — which still handles non-recursive multi-arg defs
    // like `addCases` via tuple `casesOn`. Any leading declaration binders are
    // prepended to the lifted equation-arg binders so they stay in scope (and so
    // the decreasing-arg position the recursion lowers on is offset past them).
    if let SurfaceExpr::Match(_, _, scrut, arms) = &**lam_body {
        if arms
            .iter()
            .any(|arm| matches!(&arm.pattern, SurfacePattern::Ctor(name, _) if name == &SurfaceName::generated_path("Prod.mk")))
        {
            let is_recursive =
                !def_name.is_anonymous() && super::structural::body_mentions_call(val, def_name);
            let calls = if is_recursive {
                super::structural::detect_recursion_with_params(def_name, val, &[]).calls
            } else {
                Vec::new()
            };
            let (lifted, ret_ty, body) = normalize_equation_def_multiarg(
                env,
                idents,
                def_name,
                binders,
                ty,
                scrut,
                arms,
                is_recursive,
                &calls,
                redundant,
            )?;
            let mut all_binders = binders.to_vec();
            all_binders.extend(lifted);
            return Some((all_binders, ret_ty, body));
        }
    }

    // Slice 1 (single-arg equation def): NON-recursive defs keep the historical
    // gate of *no* leading declaration binders — they already elaborate through
    // other paths, and routing them here risks regressing them. A RECURSIVE
    // single-arg equation def with leading binders, however, has no other
    // working path at all: without the lift no decreasing binder exists, no
    // `RecursiveDefContext` is installed, and the self-call dies
    // `RecursionOutsideFragment` (R100 `mixed_swap_pairs_nested`:
    // `def swapPairs {α β : Type} : List (α × β) → List (β × α) | …`).
    // Lift those exactly like the multiarg branch above: leading binders are
    // prepended and stay in scope; `setup_recursion` resolves the decreasing
    // position past them.
    let is_recursive =
        !def_name.is_anonymous() && super::structural::body_mentions_call(val, def_name);
    if !binders.is_empty() && !is_recursive {
        return None;
    }

    // Peel exactly one domain off the declaration type for the single binder.
    // The remaining tail becomes the new return type.
    //
    // - `Arrow(from, to)`: non-dependent (the `Nat → Nat` equation-def case).
    //   The binder gets type `from`; the return type becomes `to`.
    // - `Pi([p, ...], body)`: dependent. Peel the first Pi binder's type for
    //   `_x`; the remaining Pi binders (if any) re-wrap `body` as the return
    //   type, otherwise the return type is `body`.
    // `dep_name`: for a DEPENDENT `Pi` peel, the declared binder's name. The
    // residual return type may reference it (`def g : (b : Bool) → W b | …` —
    // the tail is `W b`). Lifting the value binder as the synthetic `_x` while
    // the return type still says `b` silently breaks the dependency: `b` no
    // longer resolves to the value binder, gets auto-bound as a FRESH fvar, and
    // every downstream consumer (the k=0 dependent-motive gate, the final
    // def-level check) sees two distinct fvars for the same parameter —
    // surfacing as MatchArmTypeMismatch on the second arm. Lift under the
    // DECLARED name instead (exactly Lean's equation-def semantics) and rename
    // the synthetic match scrutinee to match. Anonymous/`_` Pi binders keep
    // `_x` (nothing can reference them).
    let (binder_ty, new_return_ty, dep_name): (
        Option<SurfaceExpr>,
        Option<SurfaceExpr>,
        Option<SurfaceName>,
    ) = match ty {
        Some(SurfaceExpr::Arrow(_, from, to)) => {
            (Some((**from).clone()), Some((**to).clone()), None)
        }
        Some(SurfaceExpr::Pi(span, pi_binders, body)) => {
            let (first, rest) = pi_binders.split_first()?;
            let from = first.ty.as_ref().map(|t| (**t).clone());
            let tail = if rest.is_empty() {
                (**body).clone()
            } else {
                SurfaceExpr::Pi(*span, rest.to_vec(), body.clone())
            };
            let name = (!first.name.is_anonymous() && !first.name.is_unescaped_component("_"))
                .then(|| first.name.clone());
            (from, Some(tail), name)
        }
        // Unannotated (`None`) or a non-arrow type is not an equation def we can
        // soundly lift here — leave it for the existing paths.
        _ => return None,
    };

    let lifted_name = dep_name.unwrap_or_else(|| lam_binder.name.clone());
    let lifted_binder = SurfaceBinder::new_typed(lifted_name.clone(), binder_ty, lam_binder.info);

    // Rename the parser's synthetic scrutinee (`match _x with …`) to the lifted
    // binder name. `_x` is parser-generated and appears ONLY as the scrutinee
    // ident — user code cannot contain it — so a targeted scrutinee rebuild is
    // exact. Any other body shape is left untouched (then `lifted_name` must be
    // `_x`, since only the Match shape reaches the dependent peel).
    let new_body = match (&**lam_body, lifted_name != lam_binder.name) {
        (SurfaceExpr::Match(sp, h, scrut, arms), true) if matches!(scrut.as_ref(), SurfaceExpr::Ident(_, n) if n == &lam_binder.name) =>
        {
            let scrut_span = scrut.span();
            SurfaceExpr::Match(
                *sp,
                h.clone(),
                Box::new(SurfaceExpr::Ident(scrut_span, lifted_name.clone())),
                arms.clone(),
            )
        }
        _ => (**lam_body).clone(),
    };

    let mut all_binders = binders.to_vec();
    all_binders.push(lifted_binder);
    Some((all_binders, new_return_ty, new_body))
}

/// Peel exactly `n` domains off a declaration arrow/Pi type, returning the
/// `n` peeled domain types (in order) and the residual return type.
///
/// Mirrors the single-domain peel in `normalize_equation_def` but for the
/// multi-argument equation-def case. Returns `None` if the type does not have
/// at least `n` arrow/Pi domains, or is unannotated/non-arrow (which we never
/// lift — the binder types must be recoverable from the declaration type).
/// Each peeled domain also carries its declared `SurfaceBinderInfo`. Dropping
/// it and re-emitting every lifted binder as `Explicit` silently changes the
/// declaration's SIGNATURE: `def h : {b : β} → Imf f b → α` would register as
/// taking `b` explicitly, so the call Lean accepts is rejected and the call
/// Lean rejects is accepted — with exit 0 and nothing printed. Measured against
/// Lean v4.30.0-rc2, which prints
/// `def h : {α : Type u_1} → … → {b : β} → Imf f b → α`.
/// `Arrow` domains have no binder syntax and are `Explicit`.
pub(super) fn peel_n_domains(
    ty: &SurfaceExpr,
    n: usize,
) -> Option<(
    Vec<(
        SurfaceExpr,
        Option<SurfaceName>,
        clean_parser::SurfaceBinderInfo,
    )>,
    SurfaceExpr,
)> {
    // Each peeled domain carries the DECLARED Pi binder name (when named). A
    // dependent residual return type (`def f6 : (a : Nat) → (b : Bool) → W6 b
    // | …` — the tail is `W6 b`) references those names; lifting the equation
    // binders under synthetic `_x`/`_x_arg{pos}` names leaves them dangling,
    // to be auto-bound as FRESH fvars — the exact single-arg name-drop fixed
    // in `normalize_equation_def`, in its multiarg form. `Arrow` domains are
    // anonymous (nothing can reference them): `None`.
    let mut domains = Vec::with_capacity(n);
    let mut current = ty.clone();
    for _ in 0..n {
        match current {
            SurfaceExpr::Arrow(_, from, to) => {
                domains.push((*from, None, clean_parser::SurfaceBinderInfo::Explicit));
                current = *to;
            }
            SurfaceExpr::Pi(span, pi_binders, body) => {
                let (first, rest) = pi_binders.split_first()?;
                let declared = (!first.name.is_anonymous()
                    && !first.name.is_unescaped_component("_"))
                .then(|| first.name.clone());
                // A Pi binder without an explicit type cannot supply a binder
                // type; bail rather than fabricate one.
                domains.push(((**first.ty.as_ref()?).clone(), declared, first.info));
                current = if rest.is_empty() {
                    *body
                } else {
                    SurfaceExpr::Pi(span, rest.to_vec(), body)
                };
            }
            _ => return None,
        }
    }
    Some((domains, current))
}

/// Flatten a right-nested `Prod.mk(p0, Prod.mk(p1, ... p_{n-1}))` tuple pattern
/// into the flat leaf list `[p0, p1, ..., p_{n-1}]`.
///
/// The def-equation parser builds multi-argument arm patterns by right-folding
/// `Prod.mk` over the per-argument patterns (`def_match_body`), so a 2-arg arm
/// is `Prod.mk(p0, p1)` and a 3-arg arm is `Prod.mk(p0, Prod.mk(p1, p2))`. A
/// pattern that is not a `Prod.mk` is a single leaf.
fn flatten_prod_pattern(pat: &SurfacePattern) -> Vec<SurfacePattern> {
    let mut leaves = Vec::new();
    let mut current = pat.clone();
    loop {
        match current {
            SurfacePattern::Ctor(ref name, ref sub)
                if name == &SurfaceName::generated_path("Prod.mk") && sub.len() == 2 =>
            {
                leaves.push(sub[0].clone());
                current = sub[1].clone();
            }
            other => {
                leaves.push(other);
                break;
            }
        }
    }
    leaves
}

/// Whether a pattern leaf is a structural (constructor / literal / `n+k`)
/// matched position, as opposed to a pass-through variable or wildcard.
pub(super) fn is_structural_pattern(pat: &SurfacePattern) -> bool {
    matches!(
        pat,
        SurfacePattern::Ctor(..)
            | SurfacePattern::Lit(_)
            | SurfacePattern::NumeralAdd(..)
            | SurfacePattern::As(..)
            | SurfacePattern::Or(..)
    )
}

/// Could `name` occur in this surface expression?
///
/// Over-approximates on purpose: every form it cannot decompose answers
/// `true`, and it is not scope-aware. It is used only to decide whether
/// [`try_rename_free_ident`] has any work to do (and to let that function
/// short-circuit forms it could not traverse), so a spurious `true` costs at
/// most a refusal.
///
/// NOTE: this is deliberately NOT used as a safety guard on arm bodies. It runs
/// on UNEXPANDED surface syntax, so a body of `gee` where `notation "gee" => G`
/// does not mention `G` as far as this can tell. An earlier attempt guarded
/// binder-name adoption with exactly that test and silently miscompiled
/// (`reports/patches/README.md`). The design here never inspects a body at all.
pub(super) fn expr_may_mention_ident(e: &SurfaceExpr, name: &SurfaceName) -> bool {
    match e {
        SurfaceExpr::Ident(_, n) => n == name,
        SurfaceExpr::Lit(..)
        | SurfaceExpr::Hole(..)
        | SurfaceExpr::NamedHole(..)
        | SurfaceExpr::Universe(..)
        | SurfaceExpr::SyntheticSorry(..) => false,
        SurfaceExpr::App(_, f, args) => {
            expr_may_mention_ident(f, name)
                || args.iter().any(|a| expr_may_mention_ident(&a.expr, name))
        }
        SurfaceExpr::Arrow(_, l, r) | SurfaceExpr::Ascription(_, l, r) => {
            expr_may_mention_ident(l, name) || expr_may_mention_ident(r, name)
        }
        SurfaceExpr::Paren(_, i)
        | SurfaceExpr::Proj(_, i, _)
        | SurfaceExpr::Explicit(_, i)
        | SurfaceExpr::NamedArg(_, _, i)
        | SurfaceExpr::OutParam(_, i)
        | SurfaceExpr::SemiOutParam(_, i)
        | SurfaceExpr::UniverseInst(_, i, _) => expr_may_mention_ident(i, name),
        SurfaceExpr::Pi(_, binders, body) | SurfaceExpr::Lambda(_, binders, body) => {
            binders.iter().any(|b| {
                &b.name == name
                    || b.ty
                        .as_ref()
                        .is_some_and(|t| expr_may_mention_ident(t, name))
            }) || expr_may_mention_ident(body, name)
        }
        _ => true,
    }
}

/// Could `name` occur in this pattern — bound, as the matched constructor, or
/// inside an inaccessible/quoted subterm? Same conservative polarity as
/// [`expr_may_mention_ident`].
fn pattern_may_mention_ident(p: &SurfacePattern, name: &SurfaceName) -> bool {
    match p {
        SurfacePattern::Var(n) => n == name,
        SurfacePattern::Ctor(cname, args) => {
            cname == name
                || cname.last_component().name() == name.name()
                || args.iter().any(|a| pattern_may_mention_ident(a, name))
        }
        SurfacePattern::As(n, inner) => n == name || pattern_may_mention_ident(inner, name),
        SurfacePattern::Or(a, b) => {
            pattern_may_mention_ident(a, name) || pattern_may_mention_ident(b, name)
        }
        SurfacePattern::NumeralAdd(inner, _) => pattern_may_mention_ident(inner, name),
        SurfacePattern::Inaccessible(e) | SurfacePattern::QPattern(e) => {
            expr_may_mention_ident(e, name)
        }
        SurfacePattern::StructInst { fields, ty, .. } => {
            fields
                .iter()
                .any(|(_, pat)| pattern_may_mention_ident(pat, name))
                || ty
                    .as_ref()
                    .is_some_and(|ty| expr_may_mention_ident(ty, name))
        }
        SurfacePattern::Wildcard | SurfacePattern::Ellipsis | SurfacePattern::Lit(_) => false,
    }
}

/// Rename every FREE occurrence of `from` to `to` in a surface TYPE.
///
/// Returns `None` if the rewrite cannot be shown safe, in which case the caller
/// must leave the type alone. Refusing is always safe here: the type then keeps
/// the declared name, which is exactly the pre-existing behaviour (a dangling
/// name the kernel reports loudly).
///
/// Callers must only ever pass a `to` that cannot be spelled in user source
/// (the parser-generated `_x` / `_x_arg{n}` family). That is what makes this
/// capture-free in the target direction: no binder anywhere can already mean
/// `to`, so renaming into it cannot capture. The only remaining obligation is
/// not to rename an occurrence of `from` that an inner binder rebinds, which is
/// why this is scope-aware.
///
/// Any form this cannot traverse yields `None` rather than a guess — the
/// opposite of a silent pass-through.
fn try_rename_free_ident(
    e: &SurfaceExpr,
    from: &SurfaceName,
    to: &SurfaceName,
) -> Option<SurfaceExpr> {
    // Nothing to do — and this also short-circuits every unsupported form that
    // provably cannot contain the name.
    if !expr_may_mention_ident(e, from) {
        return Some(e.clone());
    }
    let r = |x: &SurfaceExpr| try_rename_free_ident(x, from, to);
    Some(match e {
        SurfaceExpr::Ident(sp, n) => {
            if n == from {
                SurfaceExpr::Ident(*sp, to.clone())
            } else {
                e.clone()
            }
        }
        SurfaceExpr::App(sp, f, args) => {
            let mut new_args = Vec::with_capacity(args.len());
            for a in args {
                let mut a2 = a.clone();
                a2.expr = r(&a.expr)?;
                new_args.push(a2);
            }
            SurfaceExpr::App(*sp, Box::new(r(f)?), new_args)
        }
        SurfaceExpr::Arrow(sp, l, rr) => SurfaceExpr::Arrow(*sp, Box::new(r(l)?), Box::new(r(rr)?)),
        SurfaceExpr::Ascription(sp, l, rr) => {
            SurfaceExpr::Ascription(*sp, Box::new(r(l)?), Box::new(r(rr)?))
        }
        SurfaceExpr::Paren(sp, i) => SurfaceExpr::Paren(*sp, Box::new(r(i)?)),
        SurfaceExpr::Explicit(sp, i) => SurfaceExpr::Explicit(*sp, Box::new(r(i)?)),
        SurfaceExpr::Proj(sp, i, p) => SurfaceExpr::Proj(*sp, Box::new(r(i)?), p.clone()),
        SurfaceExpr::NamedArg(sp, n, i) => SurfaceExpr::NamedArg(*sp, n.clone(), Box::new(r(i)?)),
        SurfaceExpr::OutParam(sp, i) => SurfaceExpr::OutParam(*sp, Box::new(r(i)?)),
        SurfaceExpr::SemiOutParam(sp, i) => SurfaceExpr::SemiOutParam(*sp, Box::new(r(i)?)),
        SurfaceExpr::UniverseInst(sp, i, ls) => {
            SurfaceExpr::UniverseInst(*sp, Box::new(r(i)?), ls.clone())
        }
        SurfaceExpr::Pi(sp, binders, body) => {
            let mut new_binders = Vec::with_capacity(binders.len());
            let mut shadowed = false;
            for b in binders {
                let mut b2 = b.clone();
                // A binder's own TYPE is still outside its scope.
                if !shadowed {
                    if let Some(t) = &b.ty {
                        b2.ty = Some(Box::new(r(t)?));
                    }
                } else if b
                    .ty
                    .as_ref()
                    .is_some_and(|t| expr_may_mention_ident(t, from))
                {
                    // Past the rebinding, occurrences belong to the inner
                    // binder; leaving them alone is correct.
                }
                if &b.name == from {
                    shadowed = true;
                }
                new_binders.push(b2);
            }
            let new_body = if shadowed { (**body).clone() } else { r(body)? };
            SurfaceExpr::Pi(*sp, new_binders, Box::new(new_body))
        }
        // Types are the only thing this is applied to, so a value-level form
        // reaching here is outside the envelope: refuse rather than guess.
        _ => return None,
    })
}

/// Lower a multi-argument equation def (parsed as a single `_x` binder matched
/// against a right-nested `Prod.mk` tuple) into the named-binder + single
/// scrutinee (or *nested* single-scrutinee) `match` shape that the existing
/// single-argument structural recursion path already lowers soundly through the
/// inductive's `.rec`.
///
/// SCOPE (conservative, sound envelope):
/// - The declaration type must expose `N` arrow/Pi domains (`N` = tuple arity).
/// - At least one position is structurally matched (constructor / literal /
///   `n+k` patterns) across the arms. The *first* structurally-matched position
///   becomes the decreasing argument the recursion lowers on.
/// - **Slice 2 (single structural position):** every other position is, in
///   every arm, the same variable name, or a wildcard in every arm. This lets us
///   name the lifted binder after that shared variable (no surface renaming
///   needed) so the arm bodies' references resolve unchanged. We emit a single
///   `match <dec_binder> with | <dec pattern> => <arm body> | …`.
/// - **Slice 3 (multiple structural positions — the `semVectorIntBinOp`
///   shape):** more than one position is structurally matched (e.g. a
///   simultaneous match on two `List`s). We compile the structural columns into
///   a *nested* single-scrutinee match decision tree (outer match on the
///   decreasing position, inner matches on the remaining structural positions),
///   which the kernel re-checks exactly like a hand-written nested `match`. The
///   nested form is the textbook ML pattern-matrix compilation; the recursion
///   still decreases on the outer (first) structural binder, so the existing
///   `.rec` lowering with trailing binders folded into the motive fires.
///
/// On success returns `(lifted_binders, Some(return_ty), match_body)`.
/// The non-decreasing binders surround it as ordinary declaration binders, so
/// they are in scope inside the arm bodies exactly as the surface program wrote
/// them, and `setup_recursion` resolves the decreasing-arg position against the
/// lifted binders — installing the genuine `.rec` lowering with the trailing
/// binders folded into the motive (the existing extra-param machinery).
fn normalize_equation_def_multiarg(
    env: &clean_kernel::Environment,
    idents: &PatternIdents<'_>,
    def_name: &SurfaceName,
    decl_binders: &[SurfaceBinder],
    ty: Option<&SurfaceExpr>,
    scrut: &SurfaceExpr,
    arms: &[clean_parser::SurfaceMatchArm],
    is_recursive: bool,
    calls: &[super::structural::RecursiveCall],
    redundant: &mut Option<ElabError>,
) -> Option<(Vec<SurfaceBinder>, Option<SurfaceExpr>, SurfaceExpr)> {
    // The synthetic scrutinee must be the parser's `_x` binder; anything else
    // is not the def-equation tuple shape we recognize.
    if !matches!(scrut, SurfaceExpr::Ident(_, name) if *name == SurfaceName::pattern_lambda_binder())
    {
        return None;
    }
    let ty = ty?;
    if arms.is_empty() {
        return None;
    }

    // Flatten every arm's tuple pattern into per-position leaves and require a
    // consistent arity across all arms.
    let mut arm_leaves: Vec<Vec<SurfacePattern>> = arms
        .iter()
        .map(|arm| flatten_prod_pattern(&arm.pattern))
        .collect();
    let mut arity = arm_leaves[0].len();
    if arity < 2 || arm_leaves.iter().any(|leaves| leaves.len() != arity) {
        return None;
    }

    // Peel the declaration domains up front (moved before classification): the
    // nullary-constructor rewrite below needs each column's domain type.
    let (mut domains, mut return_ty) = peel_n_domains(ty, arity)?;

    // Class (88), brick B4: trailing hypothesis columns typed by an earlier
    // matched column are generalized into the case split's result type and
    // bound per alternative, so each is about its alternative's constructor
    // (`super::equation_dep_columns`). The columns before them are lowered
    // below exactly as before.
    let generalized_arms;
    let mut arms = arms;
    let generalized = super::equation_dep_columns::generalize_dependent_columns(
        idents,
        &domains,
        &return_ty,
        &arm_leaves,
        arms,
    );
    let is_generalized = generalized.is_some();
    if let Some(generalized) = generalized {
        arity = generalized.keep;
        domains.truncate(arity);
        for leaves in &mut arm_leaves {
            leaves.truncate(arity);
        }
        return_ty = generalized.return_ty;
        generalized_arms = generalized.arms;
        arms = &generalized_arms;
    }

    // Bare-identifier resolution (see `PatternIdents` and
    // `rewrite_nullary_ctor_column`). A bare constructor ident pattern
    // (`true`, `none`, an opened constructor) parses as `SurfacePattern::Var`,
    // which would mis-classify its column as pass-through; every leaf that
    // ordinary name resolution makes a constructor — at any depth — is
    // rewritten to that constructor, exactly as Lean reads it. Anything else
    // stays a genuine binder, with two exceptions the surface cannot settle:
    //
    // * a leaf that names a nullary constructor of its column's own inductive
    //   only through that inductive's namespace is AMBIGUOUS — Lean binds it,
    //   the shorthand would test it — and the def is handed to the typed path,
    //   whose classifier refuses it (a recursive def then fails loudly);
    // * a leaf in a column whose inductive cannot be read off the surface
    //   (`abbrev`, type variable, dependent family) that could abbreviate a
    //   constructor is UNDETERMINED: only after the dependent-family lane
    //   below has had its chance (it refines such a column per row with a
    //   kernel whnf probe) is the def handed to the typed path.
    //
    // A NESTED leaf that could abbreviate a constructor of its (unknown) field
    // type sends a non-recursive def to the typed path too. A recursive def
    // keeps it as a variable: the matrix compiler re-emits every such leaf in
    // a pattern the typed classifier sees (`compile_pattern_matrix`), so it is
    // either bound exactly as Lean binds it or refused — never silently tested
    // or silently bound.
    let mut undetermined_ctor_columns: Vec<usize> = Vec::new();
    for (pos, (domain, _, _)) in domains.iter().enumerate() {
        match rewrite_nullary_ctor_column(idents, Some(domain), &mut arm_leaves, pos) {
            ColumnIdents::Settled => {}
            ColumnIdents::Undetermined => undetermined_ctor_columns.push(pos),
            ColumnIdents::Ambiguous => return None,
        }
    }
    for leaf in arm_leaves.iter_mut().flatten() {
        *leaf = idents.resolve_ctor_idents(leaf, false);
    }
    if !is_recursive
        && arm_leaves
            .iter()
            .flatten()
            .any(|leaf| idents.has_nested_suspect(leaf, false))
    {
        return None;
    }

    // Brick 88: dependent type-family second domain (`(n : Nat) → T9 n → R`).
    // The per-column rewrite above cannot see through `T9 n`, so `true`/
    // `false` leaves stay `Var`, the shared-name check below bails, and the
    // curried fallback descopes loudly. Refine the family PER ROW with a
    // kernel whnf probe and re-emit with the dependent domain kept in the
    // RETURN type (dependent-motive lane). All-or-nothing: on any gate
    // failure `arm_leaves` is untouched and everything below runs
    // byte-identically.
    if !is_generalized {
        if let Some(lifted) = super::equation_dep_family::try_emit_dependent_family(
            env,
            ty,
            &domains,
            &arm_leaves,
            arms,
            is_recursive,
        ) {
            return Some(lifted);
        }
    }
    if !undetermined_ctor_columns.is_empty() {
        return None;
    }

    // Identify the structurally-matched positions (those constructor/literal-
    // matched in some arm), in order. The first is the decreasing argument the
    // recursion lowers on; any additional ones drive the nested-match compile.
    let mut structural_positions: Vec<usize> = Vec::new();
    for pos in 0..arity {
        if arm_leaves
            .iter()
            .any(|leaves| is_structural_pattern(&leaves[pos]))
        {
            structural_positions.push(pos);
        }
    }
    // The decreasing column must be the OUTERMOST dispatch. `setup_recursion`
    // picks the decreasing argument from the self-calls (a position every
    // call passes a variable at) and preferring the whole-body match
    // scrutinee, and the `.rec` it lowers to re-runs only what sits below that
    // match. Leaving a different column outermost put the `.rec` inside a case
    // split on another argument, so the induction hypothesis reused that
    // split's pattern variables: `| 0, y => y | x+1, y+1 => f (x-2) y | x+1, 0
    // => 0` ignored the call's `x-2` and proved `f 1 2 = 0` (measured
    // 2026-09-25; Lean 4.8.0: `f 1 2 = 1`). Such a lowering is now refused by
    // `check_recursive_minors_closed`; this ordering lowers it correctly
    // instead. Reordering the columns of a pattern matrix does not change
    // which row matches — rows keep their order.
    if is_recursive && !calls.is_empty() {
        let explicit = |info: clean_parser::SurfaceBinderInfo| {
            matches!(info, clean_parser::SurfaceBinderInfo::Explicit)
        };
        let lead = decl_binders.iter().filter(|b| explicit(b.info)).count();
        let call_position = |pos: usize| -> Option<usize> {
            explicit(domains[pos].2)
                .then(|| lead + (0..pos).filter(|&q| explicit(domains[q].2)).count())
        };
        let current = structural_positions.iter().copied().find(|&pos| {
            call_position(pos).is_some_and(|at| {
                calls.iter().all(|call| {
                    matches!(
                        call.args.get(at),
                        Some(super::structural::RecursiveArg::Var(_))
                    )
                })
            })
        });
        // "Every call passes a variable here" does not say the variable is a
        // CHILD of this column's pattern: `| x, _ :: z => f x z | _, _ => 0`
        // passes the whole first column back unchanged, so recursion on it
        // cannot resolve the call, while `z` is the tail of the second. Replace
        // the column only when recursion on it certainly cannot resolve some
        // call, with the first column on which every call passes a recursive
        // field of its row's pattern (`structural::classify_descent`; Lean
        // 4.8.0 keeps the first parameter structural recursion succeeds on).
        let rows: Vec<super::structural::DescentRow<'_>> = arm_leaves
            .iter()
            .zip(arms.iter())
            .map(|(pats, arm)| super::structural::DescentRow {
                pats,
                body: &arm.body,
            })
            .collect();
        let decreasing =
            super::structural::choose_decreasing_position(current, &structural_positions, |pos| {
                let Some(at) = call_position(pos) else {
                    return super::structural::Descent::Unknown;
                };
                let column_inductive = surface_type_head(&domains[pos].0)
                    .and_then(|head| env.get_inductive(head.name()))
                    .map(|ind| ind.name.clone());
                super::structural::classify_descent(
                    env,
                    def_name,
                    &rows,
                    pos,
                    column_inductive.as_ref(),
                    at,
                )
            });
        if let Some(pos) = decreasing {
            structural_positions.retain(|&q| q != pos);
            structural_positions.insert(0, pos);
        }
    }
    let dec_pos = *structural_positions.first()?;
    let is_structural_col: Vec<bool> = (0..arity)
        .map(|pos| structural_positions.contains(&pos))
        .collect();

    // Resolve a binder name for each NON-structural (pass-through) position: all
    // *named* occurrences must agree on a single variable name; wildcard
    // occurrences impose no constraint (a `_` binds nothing, so the arm body
    // never references that position). A column that mixes a named var in one
    // arm and `_` in another therefore lifts soundly under the named var — the
    // wildcard arm simply ignores the extra binding. Only genuinely *different*
    // names across arms (which would require per-arm surface renaming) bail.
    //
    // The prior implementation treated `Wildcard` as a distinct `None` name and
    // bailed on any wildcard/named mix; that dropped the whole def back to the
    // non-normalized path, which does NOT lower multi-arg structural recursion
    // and so left the self-call as a placeholder constant typed at the return
    // type ("Too many arguments: function type … is not a function type" —
    // trust-ir `maskBitsAux`'s `| [], _, acc => …` base arm). (Track G)
    //
    // Named after the shared variable ONLY when every arm binds it there. A
    // lifted binder is in scope for every arm, so an arm with `_` in that
    // column would read the binder where its body meant something else of
    // that name: with `def y := 7`, `| 0, y => y | n+1, _ => y` made `k 1 5`
    // reduce to `5` (measured 2026-09-25; Lean 4.8.0: `7`). Otherwise the
    // binder keeps its synthetic name and each arm that names the column
    // binds its variable from it (`column_binds`).
    let mut binder_names: Vec<Option<SurfaceName>> = vec![None; arity];
    let mut column_binds: Vec<Vec<(SurfaceName, usize)>> = vec![Vec::new(); arm_leaves.len()];
    for pos in 0..arity {
        if is_structural_col[pos] {
            continue;
        }
        let mut shared_name: Option<SurfaceName> = None;
        let mut every_arm_names = true;
        for leaves in &arm_leaves {
            let this = match &leaves[pos] {
                SurfacePattern::Var(name) => Some(name.clone()),
                SurfacePattern::Wildcard => None,
                // A structural pattern in a non-structural column would
                // contradict the column classification; reject for safety.
                _ => return None,
            };
            match (&shared_name, this) {
                // Wildcard arm: no constraint, keep whatever name we have.
                (_, None) => every_arm_names = false,
                // First named occurrence sets the column's binder name.
                (None, Some(name)) => shared_name = Some(name),
                // Subsequent named occurrence must match the established name;
                // a different name would require per-arm renaming, so bail.
                (Some(prev), Some(name)) if *prev == name => {}
                (Some(_), Some(_)) => return None,
            }
        }
        if every_arm_names {
            binder_names[pos] = shared_name;
        } else if let Some(name) = shared_name {
            for (arm, leaves) in arm_leaves.iter().enumerate() {
                if matches!(&leaves[pos], SurfacePattern::Var(n) if *n == name) {
                    column_binds[arm].push((name.clone(), pos));
                }
            }
        }
    }

    // Build the lifted declaration binders. Each keeps the name the ARM BODIES
    // need (the pass-through pattern name, else the parser-generated synthetic)
    // and the declared binder's own `SurfaceBinderInfo`; the TYPE is rewritten
    // below to refer to whatever the binder ended up called.
    let declared_names: Vec<Option<SurfaceName>> =
        domains.iter().map(|(_, n, _)| n.clone()).collect();
    // UNSPELLABLE (`SurfaceName::unspellable`): a lifted binder under a
    // synthetic name is in scope for every arm body, so a spellable one
    // (`_x_arg1` used to be a plain string) captured an arm body's reference
    // to a global of that spelling — `def _x_arg1 := 77`, `| 0, y => y | n+1,
    // _ => _x_arg1` proved `e1 1 5 = 5` (measured 2026-09-25; Lean 4.8.0:
    // `77`) — and a pattern variable of that spelling captured the binder.
    let synthetic_name = |pos: usize| -> SurfaceName {
        if pos == dec_pos {
            SurfaceName::pattern_lambda_binder()
        } else {
            SurfaceName::unspellable("_x_arg", pos as u64)
        }
    };
    // NAME CHOICE — by renaming the TYPE, never by renaming the binder.
    //
    // Two consumers want this one name slot, and in Lean they are DIFFERENT
    // scopes: the TYPE references a position by its DECLARED Pi binder name,
    // while the ARM BODIES reference a pass-through position by its PATTERN
    // variable name. When those disagree no single name satisfies both.
    //
    // Four attempts tried to arbitrate — pick one side, guard the choice — and
    // each fixed its witness and silently miscompiled a shape one step wider.
    // The fourth established WHY the whole family fails: any guard of the form
    // "adopt the declared name if no arm body mentions it" reads UNEXPANDED
    // surface syntax, so with `notation "gee" => G` a body of `gee` does not
    // mention `G`, the binder takes `G`, and it shadows the global the body
    // meant. The arm body is not the program, so no syntactic test on it is
    // sound. See `reports/patches/README.md`.
    //
    // So this does not arbitrate and does not inspect bodies at all:
    //
    //   * The binder ALWAYS keeps the name the bodies need — the pass-through
    //     pattern name, or the parser-generated synthetic when there is none.
    //     A declared name is never adopted, so a binder can never shadow
    //     anything an arm body meant. That whole class is now unreachable
    //     rather than guarded.
    //   * The TYPE is instead rewritten to say what the binder is actually
    //     called. This is what makes the dependency resolve: `223.lean`'s
    //     `{b : β} → Imf f b → α` references `b` from the next DOMAIN, so the
    //     old return-type-only test left it dangling.
    //
    // Rewriting is only attempted when the target is the SYNTHETIC name, which
    // user source cannot spell (`_x` / `_x_arg{n}` are parser-generated), so
    // the rewrite cannot capture. Positions are processed RIGHT TO LEFT so a
    // name declared twice binds INNERMOST-first, as Lean does. A rewrite that
    // cannot be shown safe is skipped, leaving the pre-existing dangling-name
    // error — loud, not silent.
    let mut chosen_names: Vec<SurfaceName> = binder_names
        .iter()
        .enumerate()
        .map(|(pos, n)| n.clone().unwrap_or_else(|| synthetic_name(pos)))
        .collect();
    for pos in (0..arity).rev() {
        let Some(declared) = declared_names[pos].clone() else {
            continue;
        };
        let chosen = chosen_names[pos].clone();
        // Only rewrite toward the position's own synthetic name.
        if declared == chosen || chosen != synthetic_name(pos) {
            continue;
        }
        // The synthetic names are now unspellable, so no user binder or
        // global can already mean them. They were once ordinary identifiers
        // (`def _x_arg0 : Nat := 99`), and rewriting the type INTO a taken
        // name captured — measured producing a wrong dependent index. The
        // check stays as defense in depth: it only ever refuses, which leaves
        // the pre-existing dangling-name error.
        let target_is_taken = decl_binders.iter().any(|b| {
            b.name == chosen
                || b.ty
                    .as_ref()
                    .is_some_and(|t| expr_may_mention_ident(t, &chosen))
        }) || expr_may_mention_ident(ty, &chosen)
            || arms.iter().any(|a| {
                expr_may_mention_ident(&a.body, &chosen)
                    || pattern_may_mention_ident(&a.pattern, &chosen)
            });
        if target_is_taken {
            continue;
        }
        let mut rewritten: Vec<(
            SurfaceExpr,
            Option<SurfaceName>,
            clean_parser::SurfaceBinderInfo,
        )> = Vec::with_capacity(arity);
        let mut ok = true;
        for (idx, (dom, nm, info)) in domains.iter().enumerate() {
            if idx > pos {
                match try_rename_free_ident(dom, &declared, &chosen) {
                    Some(d) => rewritten.push((d, nm.clone(), *info)),
                    None => {
                        ok = false;
                        break;
                    }
                }
            } else {
                rewritten.push((dom.clone(), nm.clone(), *info));
            }
        }
        if !ok {
            continue;
        }
        let Some(new_return) = try_rename_free_ident(&return_ty, &declared, &chosen) else {
            continue;
        };
        domains = rewritten;
        return_ty = new_return;
    }
    // Resolve duplicates: keep the FIRST occurrence of a name, demote later
    // ones to their synthetic name (pass-through pattern names must win over a
    // structural declared name, and pattern names were already validated
    // unique per column).
    for pos in 0..arity {
        let dup = chosen_names[..pos].contains(&chosen_names[pos]);
        if dup {
            chosen_names[pos] = synthetic_name(pos);
        }
    }
    let scrut_binder_name = |pos: usize| -> SurfaceName { chosen_names[pos].clone() };
    let mut lifted_binders = Vec::with_capacity(arity);
    for (pos, (domain, _, info)) in domains.into_iter().enumerate() {
        lifted_binders.push(SurfaceBinder::new_typed(
            chosen_names[pos].clone(),
            Some(domain),
            info,
        ));
    }

    let dec_span = scrut.span();

    // The per-arm bindings of pass-through columns that kept a synthetic
    // binder name (see `column_binds`). A structural pattern that binds a
    // pass-through binder's name would capture that binder's value for every
    // arm binding read below it: refuse that. (The synthetic binder names are
    // unspellable, so only a user-named pass-through binder can meet this.)
    let arm_binds: Vec<Vec<RowBind>> = column_binds
        .iter()
        .map(|binds| {
            binds
                .iter()
                .map(|(var, pos)| RowBind {
                    var: var.clone(),
                    source: scrut_binder_name(*pos),
                    suspect: false,
                })
                .collect()
        })
        .collect();
    let passthrough_names: Vec<SurfaceName> = (0..arity)
        .filter(|&pos| !is_structural_col[pos])
        .map(scrut_binder_name)
        .collect();
    if column_binds.iter().any(|binds| !binds.is_empty())
        && arm_leaves.iter().any(|leaves| {
            structural_positions.iter().any(|&pos| {
                passthrough_names
                    .iter()
                    .any(|name| pattern_may_mention_ident(&leaves[pos], name))
            })
        })
    {
        return None;
    }

    if structural_positions.len() == 1 {
        // Slice 2: single structural position. Scrutinize only the decreasing
        // position. The arm body is unchanged — pass-through binders are already
        // in scope under their original surface names, and the decreasing
        // pattern's bound variables are re-bound by the single-scrutinee match.
        let new_arms: Vec<clean_parser::SurfaceMatchArm> = arms
            .iter()
            .zip(arm_leaves.iter())
            .zip(arm_binds.iter())
            .map(|((arm, leaves), binds)| clean_parser::SurfaceMatchArm {
                span: arm.span,
                pattern: leaves[dec_pos].clone(),
                body: bind_row_variables(binds, arm.body.clone(), arm.span),
            })
            .collect();
        let match_body = SurfaceExpr::Match(
            dec_span,
            None,
            Box::new(SurfaceExpr::Ident(dec_span, scrut_binder_name(dec_pos))),
            new_arms,
        );
        return Some((lifted_binders, Some(return_ty), match_body));
    }

    // Slice 3: multiple structural positions. Compile the structural columns
    // into a nested single-scrutinee match via textbook pattern-matrix
    // compilation. Each structural column's top-level leaf must be a constructor,
    // literal, or wildcard (variable / as / or / n+k patterns at a structural
    // top level are outside the envelope and bail) so the column always reduces
    // to "match this scrutinee against these head patterns".
    let scrut_names: Vec<SurfaceName> = structural_positions
        .iter()
        .map(|&pos| scrut_binder_name(pos))
        .collect();
    let rows: Vec<MatrixRow> = arm_leaves
        .iter()
        .zip(arms.iter())
        .zip(arm_binds)
        .enumerate()
        .map(|(origin, ((leaves, arm), binds))| MatrixRow {
            pats: structural_positions
                .iter()
                .map(|&pos| leaves[pos].clone())
                .collect(),
            body: arm.body.clone(),
            span: arm.span,
            binds,
            origin,
        })
        .collect();
    // Every lifted binder name is referenced below the emitted binders (the
    // structural ones by the inner matches, the pass-through ones by the arms'
    // bindings), so no constructor field may be bound under one of them.
    let reserved: Vec<SurfaceName> = scrut_names
        .iter()
        .chain(passthrough_names.iter())
        .cloned()
        .collect();
    // The `n + k` expansion's engagement gate admits defs the old envelope
    // could not lower at all: recursive ones, and (class (88)) ones whose
    // hypothesis columns were generalized above.
    let match_body = compile_pattern_matrix_checked(
        idents,
        def_name,
        &scrut_names,
        &rows,
        dec_span,
        is_recursive || is_generalized,
        &reserved,
        redundant,
    )?;
    Some((lifted_binders, Some(return_ty), match_body))
}

/// Unpack the parser's multi-discriminant scrutinee — a RIGHT-nested
/// `Prod.mk a (Prod.mk b c)` application spine (`match a, b, c with`,
/// `expr_match.rs::match_body`) — into its component expressions. Returns
/// `None` unless the top level is a positional two-argument application of the
/// bare ident `Prod.mk` (i.e. at least two packed discriminants).
fn unpack_prod_mk_scrutinee(scrut: &SurfaceExpr) -> Option<Vec<&SurfaceExpr>> {
    let mut components = Vec::new();
    let mut current = scrut;
    loop {
        match current {
            SurfaceExpr::App(_, f, args)
                if matches!(&**f, SurfaceExpr::Ident(_, n) if n == &SurfaceName::generated_path("Prod.mk"))
                    && args.len() == 2
                    && args.iter().all(|a| a.name.is_none()) =>
            {
                components.push(&args[0].expr);
                current = &args[1].expr;
            }
            other => {
                components.push(other);
                break;
            }
        }
    }
    (components.len() >= 2).then_some(components)
}

/// Brick 84: normalize a RECURSIVE def whose whole body is a multi-scrutinee
/// `match a, b with` over the def's own binders into the equivalent nested
/// single-scrutinee form, compiled through the same equation pattern matrix
/// as multi-argument equation defs (bricks B81/B83).
///
/// The parser packs `match a, b with` into ONE right-nested `Prod.mk`
/// scrutinee with `Prod.mk` tuple arm patterns. That tuple is never the bare
/// decreasing-arg ident, so `is_match_on_decreasing_arg` cannot fire, the
/// match lowers via `casesOn` with no induction hypothesis, and the self-call
/// dies `UnknownIdent` (the constant is not yet registered while its own body
/// elaborates). Rewriting to `match a with … match b with …` BEFORE
/// `setup_recursion` lets the existing `use_rec` + IH machinery work
/// unchanged.
///
/// ENGAGEMENT GATE (B81 lesson): only fires for defs whose body mentions a
/// self-call — the previously-FAILING class. Non-recursive multi-scrutinee
/// matches work today via the tuple-`casesOn` path and keep byte-identical
/// behavior. Every other shape check (`None` return) also falls back to that
/// pre-existing path, so nothing that elaborated before is rerouted.
///
/// `Err` when the rewritten match never selects some alternative (Lean 4.8.0:
/// "redundant alternative").
fn normalize_multi_scrutinee_match_body(
    idents: &PatternIdents<'_>,
    def_name: &SurfaceName,
    binders: &[SurfaceBinder],
    val: &SurfaceExpr,
    explicit_structural: Option<&SurfaceName>,
) -> Result<Option<SurfaceExpr>, ElabError> {
    let mut redundant = None;
    let body = nest_multi_scrutinee_match(
        idents,
        def_name,
        binders,
        val,
        explicit_structural,
        &mut redundant,
    );
    match redundant {
        Some(err) => Err(err),
        None => Ok(body),
    }
}

/// [`normalize_multi_scrutinee_match_body`]'s rewrite; a redundant
/// alternative is reported through `redundant` (and the rewrite is `None`).
fn nest_multi_scrutinee_match(
    idents: &PatternIdents<'_>,
    def_name: &SurfaceName,
    binders: &[SurfaceBinder],
    val: &SurfaceExpr,
    explicit_structural: Option<&SurfaceName>,
    redundant: &mut Option<ElabError>,
) -> Option<SurfaceExpr> {
    if def_name.is_anonymous() || binders.is_empty() {
        return None;
    }
    // The whole body must be a plain match (no `h :` discriminant hypothesis —
    // the parser rejects `h :` on multi-discriminant matches anyway).
    let SurfaceExpr::Match(span, None, scrut, arms) = val else {
        return None;
    };
    if arms.is_empty() {
        return None;
    }
    // The packed scrutinee must unpack to >= 2 BARE idents naming PAIRWISE
    // DISTINCT def binders (distinctness keeps the nested rebinding
    // shadow-free; a repeated component would re-match a name the outer match
    // may have re-bound).
    let components = unpack_prod_mk_scrutinee(scrut)?;
    let mut names: Vec<SurfaceName> = Vec::with_capacity(components.len());
    for component in components {
        let SurfaceExpr::Ident(_, n) = component else {
            return None;
        };
        if !binders.iter().any(|b| b.name == *n) || names.contains(n) {
            return None;
        }
        names.push(n.clone());
    }
    // ENGAGEMENT GATE: recursive defs only (see doc comment).
    if !super::structural::body_mentions_call(val, def_name) {
        return None;
    }
    // Every arm's tuple pattern must flatten to exactly one leaf per
    // scrutinee component.
    let mut arm_leaves: Vec<Vec<SurfacePattern>> = arms
        .iter()
        .map(|arm| flatten_prod_pattern(&arm.pattern))
        .collect();
    if arm_leaves.iter().any(|leaves| leaves.len() != names.len()) {
        return None;
    }
    // Bare-identifier resolution, keyed on the BINDER type (the multiarg path
    // keys on the peeled declaration domain) — see `PatternIdents` and the
    // same step in `normalize_equation_def_multiarg`. A bare `true`/`none`/…
    // pattern parses as `SurfacePattern::Var`, which the matrix compiler's
    // variable rule would silently treat as a catch-all. This lowering is
    // recursive-only, so an ambiguous or undetermined column refuses the
    // lowering (loudly, on the def's own name) rather than guess.
    for (pos, comp_name) in names.iter().enumerate() {
        let domain = binders
            .iter()
            .find(|b| b.name == *comp_name)
            .and_then(|b| b.ty.as_deref());
        match rewrite_nullary_ctor_column(idents, domain, &mut arm_leaves, pos) {
            ColumnIdents::Settled => {}
            ColumnIdents::Undetermined | ColumnIdents::Ambiguous => return None,
        }
    }
    for leaf in arm_leaves.iter_mut().flatten() {
        *leaf = idents.resolve_ctor_idents(leaf, false);
    }
    // Put the component `setup_recursion` will recurse on FIRST, so the `.rec`
    // is the outermost dispatch (see the same ordering in
    // `normalize_equation_def_multiarg`). `match x, y with | 0, y => … | x+1,
    // y+1 => b 0 y | …` recurses on `y`; compiled `x`-first, the induction
    // hypothesis ignored the call's `0` and `b 1 2 = 0` was provable (measured
    // 2026-09-25; Lean 4.8.0: `11`).
    let explicit_names: Vec<SurfaceName> = binders
        .iter()
        .filter(|b| matches!(b.info, clean_parser::SurfaceBinderInfo::Explicit))
        .map(|b| b.name.clone())
        .collect();
    let call_pos = |column: usize| explicit_names.iter().position(|n| *n == names[column]);
    let decreasing_column =
        match explicit_structural.and_then(|x| names.iter().position(|n| n == x)) {
            // `termination_by structural x` names the parameter `setup_recursion`
            // recurses on; it must be the outermost dispatch too. Before, the
            // rotation followed the name heuristic instead, left `x` inside a case
            // split on another column, and `match c, b with | none, z+1 => a + k3 z
            // z (some 2) | _, _ => 105` with `termination_by structural b` proved
            // `k3 1 4 none = 112` (measured 2026-09-26; the value is 106).
            Some(column) => Some(column),
            None => {
                let detected =
                    super::structural::detect_recursion_with_params(def_name, val, &explicit_names);
                // Where the recursion goes today: the detector's column, or — when
                // the detector names no column — the first column, which
                // `setup_recursion` prefers on the normalized body whenever every
                // call passes a variable there.
                let current = detected
                    .decreasing_arg
                    .and_then(|pos| explicit_names.get(pos))
                    .and_then(|name| names.iter().position(|n| n == name))
                    .or_else(|| {
                        let first = call_pos(0)?;
                        detected
                            .calls
                            .iter()
                            .all(|call| {
                                matches!(
                                    call.args.get(first),
                                    Some(super::structural::RecursiveArg::Var(_))
                                )
                            })
                            .then_some(0)
                    });
                // The detector reads spellings, not where a variable comes from:
                // `match c, b with | a+1, b+1 => f 4 c a | _, _ => 109` passes `c`
                // (spelled unlike `b`) at `b`'s position, so it chose `b`, although
                // no call passes a child of `b` and every call passes `a`, the
                // predecessor of `c`. Lean 4.8.0 recurses on `c`. Replace a column
                // only when recursion on it certainly cannot resolve some call
                // (`structural::classify_descent`).
                let rows: Vec<super::structural::DescentRow<'_>> = arm_leaves
                    .iter()
                    .zip(arms.iter())
                    .map(|(pats, arm)| super::structural::DescentRow {
                        pats,
                        body: &arm.body,
                    })
                    .collect();
                let column_inductive = |column: usize| -> Option<Name> {
                    let domain = binders
                        .iter()
                        .find(|b| b.name == names[column])
                        .and_then(|b| b.ty.as_deref())?;
                    let head = surface_type_head(domain)?;
                    idents
                        .env
                        .get_inductive(head.name())
                        .map(|ind| ind.name.clone())
                };
                let mut candidates: Vec<usize> = (0..names.len())
                    .filter(|&c| call_pos(c).is_some())
                    .collect();
                candidates.sort_by_key(|&c| call_pos(c));
                super::structural::choose_decreasing_position(current, &candidates, |column| {
                    match call_pos(column) {
                        Some(at) => super::structural::classify_descent(
                            idents.env,
                            def_name,
                            &rows,
                            column,
                            column_inductive(column).as_ref(),
                            at,
                        ),
                        None => super::structural::Descent::Unknown,
                    }
                })
            }
        };
    if let Some(column) = decreasing_column.filter(|&column| column > 0) {
        let name = names.remove(column);
        names.insert(0, name);
        for leaves in &mut arm_leaves {
            let leaf = leaves.remove(column);
            leaves.insert(0, leaf);
        }
    }
    let rows: Vec<MatrixRow> = arm_leaves
        .into_iter()
        .zip(arms.iter())
        .enumerate()
        .map(|(origin, (pats, arm))| MatrixRow {
            pats,
            body: arm.body.clone(),
            span: arm.span,
            binds: Vec::new(),
            origin,
        })
        .collect();
    // `extended: true` — the gate above already restricted us to the
    // recursive (previously-failing) class the B81 extensions target.
    compile_pattern_matrix_checked(
        idents, def_name, &names, &rows, *span, /*extended=*/ true, &names, redundant,
    )
}

/// The inductive a surface type names at its head: `T`, `T a b`, `(T a)`.
fn surface_type_head(ty: &SurfaceExpr) -> Option<&SurfaceName> {
    match ty {
        SurfaceExpr::Ident(_, name) => Some(name),
        SurfaceExpr::App(_, func, _) | SurfaceExpr::Paren(_, func) => surface_type_head(func),
        _ => None,
    }
}

/// How the equation normalizers read a bare pattern identifier: exactly as
/// Lean 4 does, with no type-directed shorthand.
///
/// A bare pattern identifier is a constructor iff ORDINARY name resolution —
/// locals, the current and opened namespaces, `export`s, the root — resolves
/// it to one; otherwise it is a pattern variable. `ctors` is that resolution,
/// computed by the elaborator (`ElabCtx::pattern_idents`) for every bare
/// identifier in the arms before the surface rewrite runs, because these
/// normalizers only see the environment.
///
/// The scrutinee type's own namespace is NOT consulted. Resolving `c` to `U.c`
/// because the column has type `U` (the shorthand the rewrite used to apply)
/// made `| some c => 0 | _ => 1` a constructor test where Lean 4.8.0 reads a
/// catch-all, and `rfl` proved the false `q (some U.a) = 1` (measured
/// 2026-09-24/25). An identifier that ONLY that shorthand would resolve is
/// ambiguous between the two readings; the normalizers then leave the
/// definition to the typed path, whose pattern classifier refuses it
/// (`classify_match_pattern_name`), or refuse it themselves.
///
/// A bare identifier that resolves to a `@[match_pattern]` global is neither
/// a constructor nor a binder (Lean's `processId` reads it like a constructor
/// and unfolds it); `match_patterns` holds those, and every normalizer treats
/// them as suspects the typed classifier must settle (G29: `| two => …` was
/// bound as a catch-all where Lean matches the literal `2`).
///
/// `ctor_heads` is the same ordinary resolution for every unqualified
/// constructor-APPLICATION head (`succ` in `| succ a, succ b => …`). The
/// matrix compiler consults it only for a column no head of which names a
/// constructor by itself (`canonicalize_column_heads`): inside `namespace Tm`
/// a `succ` head is `Tm.succ` to Lean although `Nat.succ` shares its short
/// name, and the environment alone cannot say which is meant.
pub(in crate::infer) struct PatternIdents<'e> {
    env: &'e clean_kernel::Environment,
    ctors: HashMap<SurfaceName, Name>,
    ctor_heads: HashMap<SurfaceName, Name>,
    match_patterns: HashSet<SurfaceName>,
}

impl<'e> PatternIdents<'e> {
    pub(in crate::infer) fn new(
        env: &'e clean_kernel::Environment,
        ctors: HashMap<SurfaceName, Name>,
        ctor_heads: HashMap<SurfaceName, Name>,
        match_patterns: HashSet<SurfaceName>,
    ) -> Self {
        Self {
            env,
            ctors,
            ctor_heads,
            match_patterns,
        }
    }

    /// The constructor ordinary resolution gives the unqualified
    /// constructor-application head `name`, if any.
    fn ctor_head(&self, name: &SurfaceName) -> Option<&Name> {
        self.ctor_heads.get(name)
    }

    /// `name` resolves to a `@[match_pattern]` global (see the type's doc).
    fn match_pattern(&self, name: &SurfaceName) -> bool {
        self.match_patterns.contains(name)
    }

    /// The constructor ordinary resolution gives `name`, if any.
    fn ctor(&self, name: &SurfaceName) -> Option<&Name> {
        self.ctors.get(name)
    }

    /// `name` is not a constructor by ordinary resolution, but SOME registered
    /// inductive has a nullary constructor it could abbreviate. Only a typed
    /// classification can tell whether the scrutinee type is that inductive.
    pub(super) fn shorthand_suspect(&self, name: &SurfaceName) -> bool {
        self.ctor(name).is_none()
            && (self.match_pattern(name) || name_could_be_nullary_ctor(self.env, name))
    }

    /// Rewrite every bare identifier that ordinary resolution makes a
    /// constructor into that constructor pattern (full name) — at the top
    /// when `top` holds, and in every nested position.
    pub(super) fn resolve_ctor_idents(&self, pat: &SurfacePattern, top: bool) -> SurfacePattern {
        let rec = |p: &SurfacePattern| self.resolve_ctor_idents(p, true);
        match pat {
            SurfacePattern::Var(name) if top => match self.ctor(name) {
                Some(ctor) => {
                    SurfacePattern::Ctor(SurfaceName::from_name(ctor.clone()), Vec::new())
                }
                None => pat.clone(),
            },
            SurfacePattern::Ctor(name, subs) => {
                SurfacePattern::Ctor(name.clone(), subs.iter().map(rec).collect())
            }
            SurfacePattern::As(name, inner) => {
                SurfacePattern::As(name.clone(), Box::new(rec(inner)))
            }
            SurfacePattern::NumeralAdd(inner, k) => {
                SurfacePattern::NumeralAdd(Box::new(rec(inner)), *k)
            }
            SurfacePattern::Or(a, b) => SurfacePattern::Or(Box::new(rec(a)), Box::new(rec(b))),
            other => other.clone(),
        }
    }

    /// Does a NESTED position (a sub-pattern of a constructor, `as`, `or` or
    /// `n + k`) hold a shorthand suspect? Run after `resolve_ctor_idents`.
    fn has_nested_suspect(&self, pat: &SurfacePattern, nested: bool) -> bool {
        match pat {
            SurfacePattern::Var(name) => nested && self.shorthand_suspect(name),
            SurfacePattern::Ctor(_, subs) => {
                subs.iter().any(|sub| self.has_nested_suspect(sub, true))
            }
            SurfacePattern::As(_, inner) | SurfacePattern::NumeralAdd(inner, _) => {
                self.has_nested_suspect(inner, true)
            }
            SurfacePattern::Or(a, b) => {
                self.has_nested_suspect(a, true) || self.has_nested_suspect(b, true)
            }
            SurfacePattern::StructInst { fields, .. } => fields
                .iter()
                .any(|(_, sub)| self.has_nested_suspect(sub, true)),
            SurfacePattern::Wildcard
            | SurfacePattern::Ellipsis
            | SurfacePattern::Inaccessible(_)
            | SurfacePattern::Lit(_)
            | SurfacePattern::QPattern(_) => false,
        }
    }
}

/// Every bare identifier (`Var`, `as` name excluded) in `pat`, in order.
pub(in crate::infer) fn collect_pattern_idents(pat: &SurfacePattern, out: &mut Vec<SurfaceName>) {
    match pat {
        SurfacePattern::Var(name) => {
            if !out.contains(name) {
                out.push(name.clone());
            }
        }
        SurfacePattern::Ctor(_, subs) => subs.iter().for_each(|p| collect_pattern_idents(p, out)),
        SurfacePattern::As(_, inner) | SurfacePattern::NumeralAdd(inner, _) => {
            collect_pattern_idents(inner, out)
        }
        SurfacePattern::Or(a, b) => {
            collect_pattern_idents(a, out);
            collect_pattern_idents(b, out);
        }
        _ => {}
    }
}

/// Every unqualified constructor-application head in `pat`, in order: the
/// names `PatternIdents::ctor_heads` resolves. A qualified head (`Nat.succ`)
/// and a relative one (`.succ`) are left out; neither is read through the
/// current namespace.
pub(in crate::infer) fn collect_pattern_ctor_heads(
    pat: &SurfacePattern,
    out: &mut Vec<SurfaceName>,
) {
    match pat {
        SurfacePattern::Ctor(name, subs) => {
            if !name.is_relative_constructor()
                && name.parent().is_anonymous()
                && !out.contains(name)
            {
                out.push(name.clone());
            }
            subs.iter().for_each(|p| collect_pattern_ctor_heads(p, out));
        }
        SurfacePattern::As(_, inner) | SurfacePattern::NumeralAdd(inner, _) => {
            collect_pattern_ctor_heads(inner, out)
        }
        SurfacePattern::Or(a, b) => {
            collect_pattern_ctor_heads(a, out);
            collect_pattern_ctor_heads(b, out);
        }
        _ => {}
    }
}

/// The arms of a declaration value's whole-body `match`, peeling the
/// equation-form `PatternMatchLambda` and plain lambdas.
pub(in crate::infer) fn whole_body_match_arms(
    val: &SurfaceExpr,
) -> &[clean_parser::SurfaceMatchArm] {
    let mut cur = val;
    loop {
        match cur {
            SurfaceExpr::Lambda(_, _, inner)
            | SurfaceExpr::PatternMatchLambda(_, _, inner)
            | SurfaceExpr::Ascription(_, inner, _) => cur = inner,
            SurfaceExpr::Match(_, _, _, arms) => return arms,
            _ => return &[],
        }
    }
}

/// Outcome of resolving one equation column's bare identifiers.
enum ColumnIdents {
    /// Every `Var` leaf left is a pattern variable.
    Settled,
    /// No inductive can be read off the column's surface domain, and a `Var`
    /// leaf could abbreviate a constructor of whatever it is.
    Undetermined,
    /// A `Var` leaf is not a constructor by ordinary resolution but names a
    /// nullary constructor of the column's own inductive: Lean binds it,
    /// the type-namespace shorthand would test it.
    Ambiguous,
}

/// Resolve the bare-identifier leaves of one equation column before the column
/// is classified as structural or pass-through.
///
/// A bare constructor ident (`none`, `true`, an opened or namespace-local
/// constructor) parses as `SurfacePattern::Var`. Left as a `Var`, the column
/// classifier calls it a pass-through binder, and the lowering then DROPS the
/// test: `| some _, none => 0 | _, _ => 1` compiled to a match on the first
/// column alone, so `f (some 5) (some 2)` reduced to `0` and `rfl` proved that
/// false equation (measured 2026-09-24; Lean 4.8.0 evaluates it to `1`).
///
/// Each `Var` leaf that ordinary resolution makes a constructor becomes that
/// constructor pattern (see `PatternIdents`); a leaf of another inductive is
/// then refused by the typed elaboration of the emitted match. The column's
/// inductive is the HEAD of its domain (`Option Nat` → `Option`); it is used
/// only to detect the ambiguous shorthand, never to resolve.
#[must_use]
fn rewrite_nullary_ctor_column(
    idents: &PatternIdents<'_>,
    domain: Option<&SurfaceExpr>,
    arm_leaves: &mut [Vec<SurfacePattern>],
    pos: usize,
) -> ColumnIdents {
    let env = idents.env;
    for leaves in arm_leaves.iter_mut() {
        leaves[pos] = idents.resolve_ctor_idents(&leaves[pos], true);
    }
    let head = domain.and_then(surface_type_head);
    let inductive = head.and_then(|type_name| {
        env.get_inductive(type_name.name())
            .map(|ind| (type_name, ind))
    });
    let Some((type_name, ind)) = inductive else {
        let undetermined = arm_leaves.iter().any(|leaves| {
            matches!(&leaves[pos], SurfacePattern::Var(name) if idents.shorthand_suspect(name))
        });
        return if undetermined {
            ColumnIdents::Undetermined
        } else {
            ColumnIdents::Settled
        };
    };
    let nullary: Vec<Name> = ind
        .constructor_names
        .iter()
        .filter(|c| env.get_constructor(c).is_some_and(|ci| ci.num_fields == 0))
        .cloned()
        .collect();
    let ambiguous = arm_leaves.iter().any(|leaves| {
        matches!(&leaves[pos], SurfacePattern::Var(name)
            if idents.match_pattern(name)
                || (name.parent().is_anonymous()
                    && nullary.contains(type_name.append(name).name())))
    });
    if ambiguous {
        ColumnIdents::Ambiguous
    } else {
        ColumnIdents::Settled
    }
}

/// Could this bare pattern identifier denote a nullary constructor of SOME
/// registered inductive — spelled as its full name, or (when unqualified) as
/// its last component, the way an opened namespace or the scrutinee type's own
/// namespace would resolve it? Over-approximates on purpose: it is only used to
/// REFUSE a lowering, never to build one.
fn name_could_be_nullary_ctor(env: &clean_kernel::Environment, name: &SurfaceName) -> bool {
    let last = name.name().last_component();
    let unqualified = name.parent().is_anonymous();
    env.constructors().any(|c| {
        c.num_fields == 0
            && (c.name == *name.name()
                || (unqualified && last.is_some() && c.name.last_component() == last))
    })
}

/// One row of the structural pattern matrix: the per-structural-column patterns
/// plus the arm body and source span.
///
/// `binds` are the row's pattern variables that the compiler has already
/// consumed from its columns, each with the scrutinee (or fresh field) name it
/// is bound from. They are emitted only at the LEAF, around the body of the
/// row that is selected there ([`bind_row_variables`]) — never while the
/// decision tree is still being built. A pattern binds all of its variables at
/// once, from the values being matched; an earlier column's binding wrapped in
/// place (`let a := b._f0` around `let x := a`) captured a later column's
/// reference to a scrutinee of the same name, and `match a, b with | x, a+1 =>
/// v2 x a + x | _, _ => 100` proved `v2 4 1 = 100` (Lean 4.8.0: `104`,
/// measured 2026-09-25).
#[derive(Clone)]
struct MatrixRow {
    pats: Vec<SurfacePattern>,
    body: SurfaceExpr,
    span: clean_parser::Span,
    binds: Vec<RowBind>,
    /// The alternative this row came from (0-based, source order). A leaf
    /// that selects the row records it (`RowReach`), so an alternative no
    /// leaf selects is refused as Lean refuses it.
    origin: usize,
}

/// A pattern variable of a matrix row and the name of the value it binds.
#[derive(Clone)]
struct RowBind {
    var: SurfaceName,
    source: SurfaceName,
    /// The variable might abbreviate a constructor of its scrutinee's type
    /// (`PatternIdents::shorthand_suspect`). It is bound by a one-arm `match`,
    /// whose pattern the typed classifier sees — it binds exactly when Lean
    /// binds and refuses the ambiguous shorthand. A `let` would bind it
    /// without asking.
    suspect: bool,
}

/// Open `body` with the row's pattern-variable bindings, all at once.
///
/// The sources are top-level scrutinee names and fresh field names, and every
/// source is read BEFORE any variable is bound: when some variable is spelled
/// like some source (`| b, a+1` over `match a, b` binds `b` from `a` and `a`
/// from `b`'s field), each source is first copied into an unspellable
/// temporary (a numeric name component, which no identifier token can
/// produce), so no binding can capture another's source.
fn bind_row_variables(
    binds: &[RowBind],
    body: SurfaceExpr,
    span: clean_parser::Span,
) -> SurfaceExpr {
    if binds.is_empty() {
        return body;
    }
    let collides = binds
        .iter()
        .any(|b| binds.iter().any(|other| other.source == b.var));
    let explicit = clean_parser::SurfaceBinderInfo::Explicit;
    let temp = |i: usize| SurfaceName::from_name(Name::anon().str("_pv").num(i as u64));
    let mut out = body;
    for (i, b) in binds.iter().enumerate().rev() {
        let source = if collides { temp(i) } else { b.source.clone() };
        out = if b.suspect {
            SurfaceExpr::Match(
                span,
                None,
                Box::new(SurfaceExpr::Ident(span, source)),
                vec![clean_parser::SurfaceMatchArm {
                    span,
                    pattern: SurfacePattern::Var(b.var.clone()),
                    body: out,
                }],
            )
        } else {
            SurfaceExpr::Let(
                span,
                SurfaceBinder::new_typed(b.var.clone(), None, explicit),
                Box::new(SurfaceExpr::Ident(span, source)),
                Box::new(out),
            )
        };
    }
    if collides {
        for (i, b) in binds.iter().enumerate().rev() {
            out = SurfaceExpr::Let(
                span,
                SurfaceBinder::new_typed(temp(i), None, explicit),
                Box::new(SurfaceExpr::Ident(span, b.source.clone())),
                Box::new(out),
            );
        }
    }
    out
}

/// The head shape a structural column's top-level pattern dispatches on. Two
/// patterns share a column "head" iff they would select the same `match` arm.
#[derive(Clone, PartialEq, Eq, Hash)]
enum ColHead {
    /// Constructor `name` applied to `arity` sub-patterns.
    Ctor(SurfaceName, usize),
    /// A literal pattern, keyed by its surface rendering.
    Lit(String),
}

/// Whether the explicit `heads` of a column name every constructor of one
/// inductive (`super::elab_match::complete_signature_inductive`). Heads are
/// canonical kernel names here (see `canonicalize_column_heads`); a literal
/// head, a relative head left as written, or a constructor the environment
/// does not know makes the answer `false`, which keeps the default arm — the
/// conservative direction.
fn column_signature_is_complete(env: &clean_kernel::Environment, heads: &[ColHead]) -> bool {
    let mut named: Vec<&Name> = Vec::with_capacity(heads.len());
    for head in heads {
        let ColHead::Ctor(name, _) = head else {
            return false;
        };
        named.push(name.name());
    }
    super::elab_match::complete_signature_inductive(env, named).is_some()
}

/// Whether a column pattern is a "pass-through" (binds the whole scrutinee or
/// ignores it) rather than dispatching on a constructor/literal head: a plain
/// variable, a wildcard, or the constructor-field ellipsis marker.
fn is_passthrough_pattern(pat: &SurfacePattern) -> bool {
    matches!(
        pat,
        SurfacePattern::Var(_) | SurfacePattern::Wildcard | SurfacePattern::Ellipsis
    )
}

/// Classify a structural column's top-level pattern's dispatch head. Returns
/// `Ok(None)` for a pass-through pattern (variable / wildcard / ellipsis — these
/// match every head and form the default rows) and bails the whole compile
/// (`Err(())`) for patterns outside the envelope (as / or / inaccessible / n+k /
/// q-pattern at a structural top level), which would need richer handling.
fn col_head(pat: &SurfacePattern) -> Result<Option<ColHead>, ()> {
    match pat {
        SurfacePattern::Var(_) | SurfacePattern::Wildcard | SurfacePattern::Ellipsis => Ok(None),
        SurfacePattern::Ctor(name, sub) => Ok(Some(ColHead::Ctor(name.clone(), sub.len()))),
        SurfacePattern::Lit(lit) => Ok(Some(ColHead::Lit(format!("{lit:?}")))),
        _ => Err(()),
    }
}

/// The kernel constructor a column-head constructor pattern names, resolved
/// without a type: an exact constructor name, else `I.name` for the column's
/// inductive `I` (when some other head already fixed it), else the UNIQUE
/// registered constructor whose last component is `name` (unqualified or
/// `.name` spellings only). `None` when no single constructor is named.
fn resolve_column_ctor(
    env: &clean_kernel::Environment,
    name: &SurfaceName,
    column_inductive: Option<&Name>,
) -> Option<Name> {
    let raw = name.name();
    if !name.is_relative_constructor() && env.get_constructor(raw).is_some() {
        return Some(raw.clone());
    }
    let unqualified = name.is_relative_constructor() || name.parent().is_anonymous();
    if !unqualified {
        return None;
    }
    let last = raw.last_component()?;
    if let Some(ind) = column_inductive {
        let qualified = ind.clone().str(&last);
        if env.get_constructor(&qualified).is_some() {
            return Some(qualified);
        }
    }
    let mut found = env
        .constructors()
        .filter(|c| c.name.last_component().as_deref() == Some(last.as_str()));
    let first = found.next()?;
    found.next().is_none().then(|| first.name.clone())
}

/// Canonicalize the FIRST column of a pattern matrix before its heads are
/// classified, or refuse (`None`).
///
/// `compile_pattern_matrix` treats two heads as the same arm iff they compare
/// equal, and treats distinct heads as DISJOINT. Two spellings broke that and
/// each let `rfl` prove a false equation (measured 2026-09-24, Lean 4.8.0
/// disagreeing):
///
/// * the same constructor spelled two ways — `| some 5, 0 => 0 | Option.some 6,
///   0 => 1 | _, _ => 2` made `Option.some` an unreachable second arm after
///   `some`, so `f (some 6) 0` reduced to `2`;
/// * a Nat literal beside `Nat.succ` — `| some (Nat.succ (Nat.succ _)), 0 => 0
///   | some 1, 0 => 1 | _, _ => 2` made the literal `1` an arm AFTER the
///   `Nat.succ` arm that already captures it, so `f (some 1) 0` reduced to `2`.
///   (`n + k` rows expand to exactly this shape on the recursive path.)
///
/// So: every constructor head is rewritten to its full kernel name (bail if it
/// names no single constructor, or the column's heads span several
/// inductives, or one constructor appears with different sub-pattern counts);
/// if the column is `Nat` and dispatches on a constructor, every literal head
/// `k` becomes `Nat.zero` / `Nat.succ (k-1)`; a literal beside a non-`Nat`
/// constructor bails. A column of literals and pass-throughs alone is left as
/// it is: distinct literals are disjoint heads.
///
/// The unfolding is ONE layer per call, and it recurs only while the column
/// still mixes literals with `Nat.zero`/`Nat.succ` heads. Those heads come from
/// the rows' own syntax, so the nesting it produces is bounded by the deepest
/// `Nat.succ`/`n + k` tower written in the column — not by the literal: `|
/// 1000 => … | Nat.succ 7 => …` peels once, after which `999` and `7` are both
/// literals again.
///
/// A column NO head of which names a constructor by itself — every head is a
/// short name several inductives own, such as a lone `succ` beside
/// `Nat.succ` and a user's `Tm.succ` — used to bail here, which dropped a
/// recursive definition onto the path that never installs its own name (the
/// refusal read "`same` is the name being defined …"; measured 2026-11-12 on
/// `| lit m, lit n => … | succ a, succ b => same a b | _, _ => …` inside
/// `namespace Tm`, whose second column under the `succ` arm holds `succ`
/// alone). Such a column's inductive is now the one ORDINARY name resolution
/// gives its heads (`PatternIdents::ctor_heads`), which is how Lean reads
/// them. The column's type is still not consulted, so a head that only the
/// type would resolve bails as before, and a column some head already fixes
/// is untouched. A head ordinary resolution sends to the wrong inductive
/// (`succ n` over `Nat` inside `namespace Tm`) is emitted under that name and
/// the typed elaboration of the emitted match refuses it, as Lean does.
fn canonicalize_column_heads(
    idents: &PatternIdents<'_>,
    mut rows: Vec<MatrixRow>,
) -> Option<Vec<MatrixRow>> {
    let env = idents.env;
    let nat = Name::from_string("Nat");
    // Pass 1: fix the column's inductive from the heads that name a
    // constructor exactly.
    let mut column_inductive: Option<Name> = None;
    for row in &rows {
        if let Some(SurfacePattern::Ctor(name, _)) = row.pats.first() {
            if let Some(ctor) = resolve_column_ctor(env, name, None) {
                let ind = env.get_constructor(&ctor)?.inductive_name.clone();
                match &column_inductive {
                    None => column_inductive = Some(ind),
                    Some(prev) if *prev == ind => {}
                    Some(_) => return None,
                }
            }
        }
    }
    // Pass 1b: no head fixed the inductive; let ordinary resolution of the
    // unqualified heads fix it (see the function's doc). Heads it sends to two
    // inductives name no single column type, so the lowering bails.
    if column_inductive.is_none() {
        for row in &rows {
            if let Some(SurfacePattern::Ctor(name, _)) = row.pats.first() {
                if let Some(ctor) = idents.ctor_head(name) {
                    let ind = env.get_constructor(ctor)?.inductive_name.clone();
                    match &column_inductive {
                        None => column_inductive = Some(ind),
                        Some(prev) if *prev == ind => {}
                        Some(_) => return None,
                    }
                }
            }
        }
    }
    // A column whose constructor heads are ALL relative (`.int`, `.bool`) and
    // fix no inductive by themselves — `.int` with both `Value.int` and
    // `Constant.int` in scope (trust-ir's `semVectorIntBinOp`) — has no
    // canonical spelling without the column's type, which this untyped pass
    // does not see. It needs none: inside one column every `.c` elaborates to
    // `T.c` for the column's single type `T`, and `c ↦ T.c` is injective, so
    // equal spellings are the same constructor and distinct spellings distinct
    // ones — the disjointness the dispatch below relies on. Such heads stay as
    // written and the emitted arm resolves them against the real column type.
    // A literal beside them still bails (below), as the column may not be
    // `Nat`. Bailing here used to drop the whole definition onto the tuple
    // lowering, which cannot compile a nested head under a recursive column.
    let relative_only = column_inductive.is_none()
        && rows.iter().all(|row| match row.pats.first() {
            Some(SurfacePattern::Ctor(name, _)) => name.is_relative_constructor(),
            _ => true,
        });
    // Pass 2: rewrite every constructor head to its canonical name.
    let mut arities: HashMap<Name, usize> = HashMap::new();
    let mut has_ctor = false;
    let mut has_lit = false;
    for row in &mut rows {
        match row.pats.first_mut() {
            Some(SurfacePattern::Ctor(name, subs)) if relative_only => {
                if *arities.entry(name.name().clone()).or_insert(subs.len()) != subs.len() {
                    return None;
                }
                has_ctor = true;
            }
            Some(SurfacePattern::Ctor(name, subs)) => {
                let ctor = resolve_column_ctor(env, name, column_inductive.as_ref())?;
                let ind = env.get_constructor(&ctor)?.inductive_name.clone();
                if column_inductive.get_or_insert_with(|| ind.clone()) != &ind {
                    return None;
                }
                if *arities.entry(ctor.clone()).or_insert(subs.len()) != subs.len() {
                    return None;
                }
                *name = SurfaceName::from_name(ctor);
                has_ctor = true;
            }
            Some(SurfacePattern::Lit(_)) => has_lit = true,
            _ => {}
        }
    }
    if !(has_ctor && has_lit) {
        return Some(rows);
    }
    if column_inductive.as_ref() != Some(&nat) {
        return None;
    }
    for row in &mut rows {
        if let Some(pat @ SurfacePattern::Lit(_)) = row.pats.first_mut() {
            let SurfacePattern::Lit(clean_parser::SurfaceLit::Nat(k)) = pat else {
                return None;
            };
            let k = *k;
            *pat = if k == 0 {
                SurfacePattern::Ctor(SurfaceName::generated_path("Nat.zero"), Vec::new())
            } else {
                SurfacePattern::Ctor(
                    SurfaceName::generated_path("Nat.succ"),
                    vec![SurfacePattern::Lit(clean_parser::SurfaceLit::Nat(k - 1))],
                )
            };
        }
    }
    Some(rows)
}

/// [`compile_pattern_matrix`] over a definition's whole equation list, with
/// Lean 4.8.0's redundancy check (`reportMatcherResultErrors`,
/// `src/Lean/Elab/Match.lean`): when the decision tree selects some equation
/// at no leaf, that equation is "redundant alternative" and the definition is
/// refused — reported through `redundant`, with `None` for the tree. The tree
/// splits each column exactly (see `elab_match::RowReach`), so an equation it
/// never selects is one every value of which an earlier equation matches.
/// `rows[i].origin` must be `i`.
fn compile_pattern_matrix_checked(
    idents: &PatternIdents<'_>,
    def_name: &SurfaceName,
    scruts: &[SurfaceName],
    rows: &[MatrixRow],
    span: clean_parser::Span,
    extended: bool,
    reserved: &[SurfaceName],
    redundant: &mut Option<ElabError>,
) -> Option<SurfaceExpr> {
    let mut reach = super::elab_match::RowReach::new(rows.len());
    let tree = compile_pattern_matrix(idents, scruts, rows, span, extended, reserved, &mut reach)?;
    if let Some(row) = reach.first_unreached() {
        *redundant = Some(super::elab_match::redundant_alternative(
            &format!("`{def_name}`"),
            row,
        ));
        return None;
    }
    Some(tree)
}

/// Textbook ML pattern-matrix compiler specialized for the structural columns
/// of a multi-argument equation def. Produces a nested single-scrutinee
/// `SurfaceExpr::Match` decision tree that is semantically equivalent to the
/// simultaneous match the surface program wrote, and that the kernel re-checks
/// like any hand-written nested match.
///
/// `scruts[i]` is the binder name scrutinized for matrix column `i`. Each row's
/// `pats[i]` is that row's pattern for column `i`. Rows are tried top-to-bottom
/// (first-match-wins), exactly as Lean's equation compiler orders arms.
///
/// Binding faithfulness: rather than alpha-renaming arm bodies (which would
/// require a full surface substitution pass), a column pattern's *variable*
/// bindings are recorded on the row (`MatrixRow::binds`) and emitted together
/// at the leaf, around the body (`bind_row_variables`). A constructor column
/// peels into fresh field-scrutinee columns bound by fresh names in the arm
/// pattern; each row's original sub-patterns then flow into those fresh columns,
/// so a sub-pattern like a list tail `xs` is bound from its field at the leaf.
/// No binder a row did not write is ever in scope for its body.
///
/// Returns `None` (bailing the whole lowering) when any column pattern is
/// outside `col_head`'s envelope, so we never emit a term that silently
/// reorders or drops a binding.
///
/// `reserved` are the TOP-LEVEL scrutinee names (and, for equation defs, the
/// lifted pass-through binder names). They are referenced by name below every
/// binder this compiler emits (the inner `match <name> with`, and the leaf
/// binding a whole-scrutinee variable row becomes), so no
/// emitted binder may be spelled like one: a constructor field bound under its
/// row's own name `y` inside `match y with | Nat.succ y => …` captured every
/// later `y`, and `match x, y with | 0, y => y + 10 | x+1, y+1 => b 0 y | x+1,
/// 0 => x` reduced `b 1 2` to `10` (measured 2026-09-25; Lean 4.8.0: `11`).
/// Such a field gets a fresh name and its row variable is re-bound from it.
fn compile_pattern_matrix(
    idents: &PatternIdents<'_>,
    scruts: &[SurfaceName],
    rows: &[MatrixRow],
    span: clean_parser::Span,
    extended: bool,
    reserved: &[SurfaceName],
    reach: &mut super::elab_match::RowReach,
) -> Option<SurfaceExpr> {
    // No columns left: every structural position matched. The first remaining
    // row wins (first-match-wins arm ordering).
    if scruts.is_empty() {
        return rows.first().map(|r| {
            reach.reach(r.origin);
            bind_row_variables(&r.binds, r.body.clone(), r.span)
        });
    }
    if rows.is_empty() {
        return None;
    }

    // Column-head normalization pass, run BEFORE head classification:
    //
    // (1) NumeralAdd expansion: an `inner + k` pattern is `k` nested
    //     `Nat.succ` constructor applications around `inner`. `col_head` has
    //     no numeral-add head (two different `+k`s OVERLAP, so they are not
    //     disjoint dispatch heads) — expanding to `Nat.succ` towers makes the
    //     column a uniform constructor dispatch, exactly how Lean's equation
    //     compiler treats `n+1` rows.
    // (2) Variable-row rewrite (the Maranget variable rule for a MIXED
    //     column): a row binding the WHOLE scrutinee to `x` alongside
    //     constructor heads matches every head. The scrutinee is a named
    //     lifted def binder that stays in scope inside the emitted match arms,
    //     so `x`'s binding is recorded on the row (bound from the scrutinee at
    //     the leaf) and the row's head is demoted to a wildcard
    //     pass-through — included in every constructor arm AND the default
    //     arm by the specialization below. (The prior mixed-column guard
    //     bailed the whole lowering here, dropping everyday defs like
    //     `| 0, m => m | n+1, m+1 => f n m + 1` back to the non-normalized
    //     path — where multi-arg structural recursion never installs the
    //     self-name and the recursive call fails UnknownIdent.)
    fn expand_numeral_add(pat: &SurfacePattern) -> SurfacePattern {
        match pat {
            SurfacePattern::NumeralAdd(inner, k) => {
                let mut expanded = (**inner).clone();
                for _ in 0..*k {
                    expanded = SurfacePattern::Ctor(
                        SurfaceName::generated_path("Nat.succ"),
                        vec![expanded],
                    );
                }
                expanded
            }
            other => other.clone(),
        }
    }
    // ENGAGEMENT GATE: the numeral-add expansion only fires for defs the OLD
    // envelope could not lower at all (recursive multiarg equation defs, which
    // previously died UnknownIdent on their own name).
    //
    // The variable-row rewrite fires on every path. The non-extended path used
    // to bail on ANY whole-scrutinee variable row (the guard below), which
    // handed the def to the tuple path; since the literal/`succ`
    // canonicalization (`canonicalize_column_heads`) turns `| 42, '0' | succ
    // x, '0'` into a column of a literal beside such a row, that path refused
    // the nested `Char` literal — a correct definition lost (measured
    // 2026-09-25). The rewrite is the same on both paths.
    let rewritten_rows: Vec<MatrixRow> = rows
        .iter()
        .map(|r| {
            let mut row = r.clone();
            if extended {
                row.pats[0] = expand_numeral_add(&row.pats[0]);
            }
            if let SurfacePattern::Var(x) = row.pats[0].clone() {
                // Recorded, not wrapped here: see `MatrixRow::binds`.
                row.pats[0] = SurfacePattern::Wildcard;
                row.binds.push(RowBind {
                    suspect: idents.shorthand_suspect(&x),
                    var: x,
                    source: scruts[0].clone(),
                });
            }
            row
        })
        .collect();
    // Head canonicalization (see `canonicalize_column_heads`): the dispatch
    // below compares heads by NAME, so every constructor head must be spelled
    // the one way the kernel names it, and a Nat literal must be the
    // constructor it denotes whenever the column also dispatches on
    // `Nat.zero`/`Nat.succ`. Outside that envelope the lowering bails.
    let rewritten_rows = canonicalize_column_heads(idents, rewritten_rows)?;
    let rows = &rewritten_rows[..];

    // The variable-row rewrite above removed every whole-scrutinee `Var` row.
    if rows
        .iter()
        .any(|r| matches!(&r.pats[0], SurfacePattern::Var(_)))
    {
        return None;
    }

    let heads: Vec<Option<ColHead>> = rows
        .iter()
        .map(|r| col_head(&r.pats[0]))
        .collect::<Result<_, _>>()
        .ok()?;

    // Variable rule: the first column dispatches on no constructor — every row
    // is a wildcard / ellipsis there (whole-scrutinee variables were recorded
    // as row bindings above, row by row, so no row's name is lost).
    // The column does not branch and is dropped.
    if heads.iter().all(Option::is_none) {
        let rest_scruts = &scruts[1..];
        let rest_rows: Vec<MatrixRow> = rows
            .iter()
            .map(|r| MatrixRow {
                pats: r.pats[1..].to_vec(),
                body: r.body.clone(),
                span: r.span,
                binds: r.binds.clone(),
                origin: r.origin,
            })
            .collect();
        return compile_pattern_matrix(
            idents,
            rest_scruts,
            &rest_rows,
            span,
            extended,
            reserved,
            reach,
        );
    }

    // Constructor rule: build a `match scruts[0] with` whose arms are the
    // distinct heads (in first-appearance order). For each head we *specialize*
    // the matrix: keep rows whose first pattern is that head (decomposing its
    // sub-patterns into fresh leading columns) or a pass-through (which
    // decomposes into wildcards for the head's fields). The remaining structural
    // columns follow. Fresh scrutinee names back the head's field columns.
    let mut head_order: Vec<ColHead> = Vec::new();
    for h in heads.iter().flatten() {
        if !head_order.contains(h) {
            head_order.push(h.clone());
        }
    }

    let mut match_arms: Vec<clean_parser::SurfaceMatchArm> = Vec::new();
    for head in &head_order {
        let (head_ctor_name, field_count) = match head {
            ColHead::Ctor(name, n) => (Some(name.clone()), *n),
            ColHead::Lit(_) => (None, 0),
        };

        // Per-field binding decision. For each of the head's fields we look at
        // how every row matching this head fills it. If every such row uses the
        // *same* variable name (wildcards are compatible — they bind nothing),
        // we bind the field directly to that surface name in the arm pattern and
        // do NOT spawn an inner column for it. This is what keeps a recursive
        // list-tail like `lhsRest` bound under its original name, so the IH
        // (keyed on the arm's pattern-variable name) matches the self-call's
        // decreasing argument. Otherwise we bind the field to a fresh name and
        // re-match the differing sub-patterns as a fresh inner column.
        let mut field_names: Vec<SurfaceName> = Vec::with_capacity(field_count);
        let mut field_is_inner: Vec<bool> = Vec::with_capacity(field_count);
        for fi in 0..field_count {
            // `chosen` is the single surface variable name every matching row
            // uses for this field (wildcards bind nothing, so they impose no
            // constraint and stay compatible with any chosen name). `decomposable`
            // stays true only while all matching rows are a `Var`/wildcard that
            // agree on at most one name.
            let mut chosen: Option<SurfaceName> = None;
            let mut decomposable = true;
            for r in rows {
                if let SurfacePattern::Ctor(name, sub) = &r.pats[0] {
                    if head_ctor_name.as_ref() == Some(name) && sub.len() == field_count {
                        match &sub[fi] {
                            SurfacePattern::Wildcard | SurfacePattern::Ellipsis => {
                                // No constraint.
                            }
                            SurfacePattern::Var(n) => match &chosen {
                                None => chosen = Some(n.clone()),
                                Some(prev) if prev == n => {}
                                Some(_) => {
                                    // Two different variable names for the same
                                    // field across arms: cannot bind one name.
                                    decomposable = false;
                                    break;
                                }
                            },
                            _ => {
                                // A non-variable sub-pattern (constructor/literal/…):
                                // this field must be re-matched as an inner column.
                                decomposable = false;
                                break;
                            }
                        }
                    }
                }
            }
            if decomposable && chosen.as_ref().is_some_and(|n| reserved.contains(n)) {
                decomposable = false;
            }
            // A field bound under a user name is in scope for EVERY row this
            // arm keeps: the rows with this head AND the pass-through rows.
            // A row that does not bind that name itself (a `_` there, or a
            // pass-through row) would see the field instead of whatever the
            // name meant in its body — a parameter outside the match, a
            // global, another column's binder: `match a, b with | c+1, 0 =>
            // g c 0 7 + 1 | _, _ => c` returned the field for `g 3 1 5`
            // (measured 2026-09-25: `2`; Lean 4.8.0: `5`). So a user name is
            // bound directly only when every kept row binds exactly it;
            // otherwise the field gets a fresh name and each row that names
            // it binds it at its leaf.
            if decomposable {
                if let Some(n) = &chosen {
                    let every_row_binds = rows.iter().all(|r| match &r.pats[0] {
                        SurfacePattern::Ctor(name, sub)
                            if head_ctor_name.as_ref() == Some(name)
                                && sub.len() == field_count =>
                        {
                            matches!(&sub[fi], SurfacePattern::Var(v) if v == n)
                        }
                        p => !is_passthrough_pattern(p),
                    });
                    if !every_row_binds {
                        decomposable = false;
                    }
                }
            }
            if decomposable {
                // All matching rows agree on a single variable (or only wildcards)
                // for this field: bind it directly, no inner column.
                // Fresh field names end in a numeric component, so no source
                // identifier (`a._f0` is field notation on `a`) can reach them.
                let name = chosen.unwrap_or_else(|| {
                    SurfaceName::from_name(scruts[0].name().clone().str("_f").num(fi as u64))
                });
                field_names.push(name);
                field_is_inner.push(false);
            } else {
                // Differing sub-patterns: bind a fresh name, re-match inner.
                field_names.push(SurfaceName::from_name(
                    scruts[0].name().clone().str("_f").num(fi as u64),
                ));
                field_is_inner.push(true);
            }
        }

        // Inner scrutinee columns are exactly the fields we did NOT bind by a
        // shared name, in order, followed by the remaining structural columns.
        let inner_field_scruts: Vec<SurfaceName> = (0..field_count)
            .filter(|&fi| field_is_inner[fi])
            .map(|fi| field_names[fi].clone())
            .collect();
        let mut sub_scruts: Vec<SurfaceName> = inner_field_scruts;
        sub_scruts.extend_from_slice(&scruts[1..]);

        // Specialize: rows whose first pattern is this head contribute their
        // re-match (inner-column) sub-patterns; pass-through rows contribute
        // wildcards for each inner column (they match every head).
        let inner_field_indices: Vec<usize> =
            (0..field_count).filter(|&fi| field_is_inner[fi]).collect();
        let mut sub_rows: Vec<MatrixRow> = Vec::new();
        for r in rows {
            match &r.pats[0] {
                SurfacePattern::Ctor(name, sub)
                    if head_ctor_name.as_ref() == Some(name) && sub.len() == field_count =>
                {
                    let mut new_pats: Vec<SurfacePattern> = inner_field_indices
                        .iter()
                        .map(|&fi| sub[fi].clone())
                        .collect();
                    new_pats.extend_from_slice(&r.pats[1..]);
                    sub_rows.push(MatrixRow {
                        pats: new_pats,
                        body: r.body.clone(),
                        span: r.span,
                        binds: r.binds.clone(),
                        origin: r.origin,
                    });
                }
                p @ SurfacePattern::Lit(_) if col_head(p).ok().flatten().as_ref() == Some(head) => {
                    sub_rows.push(MatrixRow {
                        pats: r.pats[1..].to_vec(),
                        body: r.body.clone(),
                        span: r.span,
                        binds: r.binds.clone(),
                        origin: r.origin,
                    });
                }
                p if is_passthrough_pattern(p) => {
                    let mut new_pats: Vec<SurfacePattern> =
                        vec![SurfacePattern::Wildcard; inner_field_indices.len()];
                    new_pats.extend_from_slice(&r.pats[1..]);
                    sub_rows.push(MatrixRow {
                        pats: new_pats,
                        body: r.body.clone(),
                        span: r.span,
                        binds: r.binds.clone(),
                        origin: r.origin,
                    });
                }
                _ => { /* row's head differs from this arm: skip */ }
            }
        }

        let body = compile_pattern_matrix(
            idents,
            &sub_scruts,
            &sub_rows,
            span,
            extended,
            reserved,
            reach,
        )?;
        // Arm pattern: reconstruct the head, binding fields either to their
        // shared surface name (so the body / IH refers to them unchanged) or to
        // the fresh re-match name. A literal head re-emits the literal verbatim.
        let arm_pattern = match head {
            ColHead::Ctor(name, _) => SurfacePattern::Ctor(
                name.clone(),
                field_names
                    .iter()
                    .map(|n| SurfacePattern::Var(n.clone()))
                    .collect(),
            ),
            ColHead::Lit(_) => rows.iter().find_map(|r| match &r.pats[0] {
                p @ SurfacePattern::Lit(_) if col_head(p).ok().flatten().as_ref() == Some(head) => {
                    Some(p.clone())
                }
                _ => None,
            })?,
        };
        match_arms.push(clean_parser::SurfaceMatchArm {
            span,
            pattern: arm_pattern,
            body,
        });
    }

    // Default arm: pass-through rows also apply when the scrutinee matches none
    // of the explicit heads. Emit a trailing arm dropping this column; a
    // pass-through row's variable is among its recorded bindings.
    //
    // Not when the heads already name EVERY constructor of the column's
    // inductive (Maranget's complete signature): no value reaches the default,
    // and every pass-through row is already inside each constructor arm above.
    // Lean's `processConstructor` (`Lean/Meta/Match/Match.lean`) likewise
    // splits on every constructor and emits no default. Emitting it anyway
    // compiled the rows that would reach it as a match of their own, which can
    // be partial: `| [], [], [] | a :: as, b :: bs, c :: cs | _ :: _, _, _ |
    // [], _ :: _, _ | [], _, _ :: _` left `match x₃ with | _ :: _ => …` (no
    // `[]`) under the unreachable default of the `[]`-column, and the whole
    // definition failed (trust-ir `semVectorSelectLanes`, gap G18).
    if heads.iter().any(Option::is_none) && !column_signature_is_complete(idents.env, &head_order) {
        let default_rows: Vec<MatrixRow> = rows
            .iter()
            .zip(heads.iter())
            .filter(|(_, h)| h.is_none())
            .map(|(r, _)| MatrixRow {
                pats: r.pats[1..].to_vec(),
                body: r.body.clone(),
                span: r.span,
                binds: r.binds.clone(),
                origin: r.origin,
            })
            .collect();
        // A default that cannot be compiled bails the whole lowering. Dropping
        // the arm instead left the emitted match without its catch-all, and
        // the constructors no explicit head names then had no minor at all.
        let default_body = compile_pattern_matrix(
            idents,
            &scruts[1..],
            &default_rows,
            span,
            extended,
            reserved,
            reach,
        )?;
        // Top-level `Var` rows were rewritten to wildcard rows that record the
        // variable as a row binding (variable-row rewrite above), so the only
        // pass-through heads here are wildcard / ellipsis — a wildcard arm is
        // faithful.
        match_arms.push(clean_parser::SurfaceMatchArm {
            span,
            pattern: SurfacePattern::Wildcard,
            body: default_body,
        });
    }

    Some(SurfaceExpr::Match(
        span,
        None,
        Box::new(SurfaceExpr::Ident(span, scruts[0].clone())),
        match_arms,
    ))
}

/// Collect all `Level::Param` names that appear in an expression's `Sort` and
/// `Const` nodes. Used to filter `universe_params` down to only those levels
/// that actually survive after `instantiate_levels` resolves concrete assignments.
///
/// Without this filtering, definitions like `abbrev MySem (a : Type) := StateT ...`
/// carry universe params (e.g., `u_0, u_1, u_2`) that were unified to concrete
/// levels during elaboration but still appear in `level_params`. This causes
/// level count mismatches when the definition is later unfolded, because the
/// definition's value has concrete levels but `unfold_definition` substitutes
/// the (now-unused) params with fresh levels that are never constrained.
/// Part of #3396.
struct DefLevelParamCollector<'a> {
    params: &'a mut Vec<Name>,
}

impl ExprVisitor for DefLevelParamCollector<'_> {
    type Result = ();

    fn combine(&self, _: Self::Result, _: Self::Result) -> Self::Result {}

    fn visit_sort(&mut self, level: &Level) -> Self::Result {
        level.collect_params(self.params);
    }

    fn visit_const(&mut self, _name: &Name, levels: &LevelVec) -> Self::Result {
        for level in levels {
            level.collect_params(self.params);
        }
    }
}

pub(super) fn collect_def_level_params(expr: &Expr, params: &mut Vec<Name>) {
    if !expr.has_level_param_quick() {
        return;
    }
    let mut collector = DefLevelParamCollector { params };
    collector.visit_expr(expr);
}

impl ElabCtx<'_> {
    /// Whether `meta`'s type is a TYPE-CLASS application, i.e. the metavariable
    /// is an unsolved instance goal rather than an ordinary type hole.
    ///
    /// Structural because `MetaVar` carries no instance marker: instantiate the
    /// recorded type, take the head of its application spine, and ask the
    /// instance registry whether that head is a registered class.
    fn meta_is_instance_goal(&self, meta: &crate::unify::MetaVar) -> bool {
        let ty = self.metas.instantiate(&meta.ty);
        crate::instances::extract_class_app(&ty)
            .is_some_and(|(name, _)| self.instances.is_class(&name))
    }

    /// Fail-closed residual guard for finalized declarations.
    ///
    /// This elaborator encodes unassigned metavariables as FVars with bit 63
    /// set (`MetaState` meta-tag), so the kernel's "contains free variables"
    /// rejection conflates two distinct completeness failures. Catch both
    /// here, classified: meta-tagged ids are implicit arguments nothing could
    /// ever constrain (phantom section binders, an untyped alias desugar, a
    /// failed instance-synthesis fallback); low ids are genuine locals that
    /// escaped abstraction (e.g. a dropped section variable). Zero soundness
    /// effect — every declaration this rejects, the kernel already rejects —
    /// but the error becomes typed, named, and actionable.
    pub(super) fn ensure_no_residual_fvars(
        &self,
        decl_kind: &str,
        name: &SurfaceName,
        ty: &Expr,
        val: Option<&Expr>,
    ) -> Result<(), ElabError> {
        const META_TAG: u64 = 1u64 << 63;
        let mut exprs: Vec<&Expr> = vec![ty];
        if let Some(v) = val {
            exprs.push(v);
        }
        let ids = clean_kernel::env::collect_fvar_ids_for_diagnostics(&exprs);
        if ids.is_empty() {
            return Ok(());
        }
        // User-written `_` holes are metas that carry a source span; they are
        // EXPECTED to survive finalization — the hole machinery reports their
        // goal as agent feedback and registration handles them downstream.
        // The guard is for metas nothing will ever report or resolve.
        let hole_ids: HashSet<u64> = self
            .metas
            .iter()
            .filter_map(|(id, meta)| meta.span.map(|_| id.as_u64()))
            .collect();
        let metas: Vec<u64> = ids
            .iter()
            .filter(|id| **id & META_TAG != 0)
            .map(|id| *id & !META_TAG)
            .filter(|raw| !hole_ids.contains(raw))
            .collect();
        let locals: Vec<u64> = ids
            .iter()
            .filter(|id| **id & META_TAG == 0)
            .copied()
            .collect();
        if metas.is_empty() && locals.is_empty() {
            return Ok(());
        }

        // NAME THE INSTANCE GOALS (v7/D3: a refusal must carry the fix, with
        // options). An unassigned instance metavariable is a synthesis
        // FAILURE, and the goal it failed on is still in hand — it is
        // `MetaVar.ty`, and `meta_is_instance_goal` already reads exactly that
        // field at exactly this boundary. Reporting `?[7]` instead discarded
        // the only actionable fact in the failure: the id is an allocation
        // counter that names nothing, and the same `?[7]` was measured for two
        // unrelated programs.
        let by_raw_id: HashMap<u64, &crate::unify::MetaVar> =
            self.metas.iter().map(|(id, m)| (id.as_u64(), m)).collect();
        let mut instance_goals: Vec<Expr> = Vec::new();
        let mut plain_metas: Vec<u64> = Vec::new();
        for raw in &metas {
            match by_raw_id.get(raw) {
                Some(meta) if self.meta_is_instance_goal(meta) => {
                    instance_goals.push(self.metas.instantiate(&meta.ty));
                }
                _ => plain_metas.push(*raw),
            }
        }

        if let Some(goal) = instance_goals.first() {
            let mut detail = self.instance_failure_help(goal);
            if instance_goals.len() > 1 {
                let rest: Vec<String> = instance_goals[1..]
                    .iter()
                    .map(|g| format!("`{}`", self.render_instance_goal(g)))
                    .collect();
                detail.push_str(&format!(
                    "\n  {} further instance goal(s) are also unsolved: {}\n",
                    rest.len(),
                    rest.join(", ")
                ));
            }
            if !plain_metas.is_empty() || !locals.is_empty() {
                detail.push_str(&format!(
                    "\n  Also unresolved in this declaration: unsolved metavariables \
                     ?{plain_metas:?}, escaped local fvars {locals:?}\n"
                ));
            }
            return Err(ElabError::UnsynthesizedInstanceGoal {
                decl_kind: decl_kind.to_owned(),
                name: name.to_string(),
                goal: self.render_instance_goal(goal),
                detail,
            });
        }

        let mut parts = Vec::new();
        if !plain_metas.is_empty() {
            parts.push(format!(
                "unsolved metavariables ?{}",
                crate::error_render::opaque(&plain_metas)
            ));
        }
        if !locals.is_empty() {
            parts.push(format!("escaped local fvars {locals:?}"));
        }
        Err(ElabError::ResidualFreeVariables {
            decl_kind: decl_kind.to_owned(),
            name: name.to_string(),
            detail: parts.join("; "),
        })
    }

    /// Render a class application as `Class Arg Arg …`, showing unassigned
    /// metavariables as `?N` rather than the `Display` impl's raw
    /// `fvar#FVarId(9223372036854775815)`.
    pub(super) fn render_instance_goal(&self, goal: &Expr) -> String {
        let Some((class, args)) = crate::instances::extract_class_app(goal) else {
            return format!("{goal}");
        };
        let mut out = class.to_string();
        for arg in &args {
            out.push(' ');
            out.push_str(&Self::render_goal_arg(arg));
        }
        out
    }

    fn render_goal_arg(arg: &Expr) -> String {
        use crate::unify::MetaState;
        use clean_kernel::ExprKind;
        if let ExprKind::FVar(id) = arg.kind() {
            if let Some(mid) = MetaState::from_fvar(*id) {
                return format!("?{}", mid.as_u64());
            }
        }
        let rendered = format!("{arg}");
        if rendered.contains(' ') {
            format!("({rendered})")
        } else {
            rendered
        }
    }

    /// The body of the refusal: what the search had, and what the reader can
    /// do about it.
    ///
    /// HONESTY BOUNDARY. Everything here is read out of state that is in hand
    /// at the reporting site — the goal (`MetaVar.ty`) and the candidate list
    /// (`InstanceTable::get_instances`). It therefore says "none of these
    /// inhabited the goal", NOT "no such instance can exist": the resolution
    /// REASON is discarded one call earlier (`ElabCtx::resolve_instance`
    /// narrows `Result<Expr, ResolutionError>` to `Option<Expr>` in
    /// `infer/instance.rs`), so a `MaxDepthExceeded` / `MaxHeartbeatsExceeded`
    /// outcome is indistinguishable here from a genuine absence, and a
    /// non-existence claim would be false in those cases. Widening that return
    /// type is the follow-on that would let this message distinguish them.
    /// [`Self::instance_failure_help`] as an error field: prefixed with its own
    /// newline, or empty.
    ///
    /// The variant's format string appends this directly after the goal, so a
    /// site that has nothing to add contributes nothing — no stray blank line,
    /// and the bare message stays byte-identical for the goals that are not
    /// class applications.
    pub(super) fn instance_failure_detail(&self, goal: &Expr) -> String {
        let help = self.instance_failure_help(goal);
        if help.is_empty() {
            help
        } else {
            format!("\n{help}")
        }
    }

    pub(super) fn instance_failure_help(&self, goal: &Expr) -> String {
        const MAX_LISTED: usize = 10;
        let mut out = String::new();
        let Some((class, args)) = crate::instances::extract_class_app(goal) else {
            return out;
        };
        let goal_str = self.render_instance_goal(goal);

        out.push_str(
            "  An instance-implicit argument was left unfilled, so the declaration is incomplete.\n",
        );

        // A goal that is not fully determined is a DIFFERENT failure from a
        // determined goal with no instance, and must not be reported as one.
        let open: Vec<String> = args
            .iter()
            .map(Self::render_goal_arg)
            .filter(|s| s.starts_with('?'))
            .collect();
        if !open.is_empty() {
            out.push_str(&format!(
                "  The goal is NOT fully determined: {} was never pinned by the enclosing\n  \
                 declaration, so synthesis could not state what it needed.\n",
                open.join(", ")
            ));
        }

        let registered = self.instances.get_instances(&class);
        if registered.is_empty() {
            out.push_str(&format!(
                "\n  `{class}` is a registered class, but NO instance of it is registered.\n"
            ));
        } else {
            out.push_str(&format!(
                "\n  `{class}` is a registered class. Instance synthesis had these candidates, and\n  none of them was found to inhabit the goal:\n"
            ));
            for inst in registered.iter().take(MAX_LISTED) {
                out.push_str(&format!(
                    "      {} : {}\n",
                    inst.name,
                    self.render_instance_goal(&inst.type_)
                ));
            }
            if registered.len() > MAX_LISTED {
                out.push_str(&format!(
                    "      … and {} more\n",
                    registered.len() - MAX_LISTED
                ));
            }
            // Kept on ONE line on purpose: this is the sentence that bounds the
            // claim, and a wrapped sentence is one a reader (or a test) can miss.
            out.push_str(
                "  That is what the search HAD available; it is not a proof that no such instance can exist.\n",
            );
        }

        out.push_str("\n  Options:\n");
        let carriers = Self::registered_carriers(registered);
        if carriers.is_empty() {
            out.push_str(&format!(
                "    1. Register an instance of `{class}` — there is currently none.\n"
            ));
        } else {
            out.push_str(&format!(
                "    1. Compute at a carrier `{class}` is registered at: {}.\n",
                carriers.join(", ")
            ));
            // Only offered when a machine carrier is actually involved — a
            // `UInt{N}.toNat` hint against a user structure would be noise.
            // Name the WIDTH the goal actually mentions. Hardcoding `UInt64`
            // here told a `UInt8`/`UInt16`/`UInt32` reader to convert through
            // the wrong type and quoted the wrong modulus — a hint that is
            // false of the program in front of it, which is exactly what this
            // whole diagnostic exists to stop being.
            if let Some(width) = args
                .iter()
                .map(Self::render_goal_arg)
                .find(|a| a.starts_with("UInt"))
            {
                let bits = match width.as_str() {
                    "UInt8" => "8",
                    "UInt16" => "16",
                    "UInt32" => "32",
                    _ => "64",
                };
                out.push_str(&format!(
                    "       Convert at the boundary — `{width}.toNat x : Nat`, and back with\n       \
                     `{width}.ofNat` (which wraps mod 2^{bits}).\n",
                ));
            }
        }
        out.push_str(&format!(
            "    2. Supply the instance yourself:\n         \
             instance : {goal_str} := \u{27e8}fun a b => \u{2026}\u{27e9}\n"
        ));
        out.push_str(
            "    3. If this is a prelude gap rather than a mistake in this program, the missing\n       \
             instance belongs beside the others in `Environment::with_prelude`\n       \
             (clean-kernel `src/env/`).\n",
        );
        out
    }

    /// The distinct FIRST arguments of a class's registered instances — the
    /// carriers the class is actually available at. Parametric instances (a Pi
    /// type, so no class application at the head) contribute nothing rather
    /// than a misleading name.
    fn registered_carriers(registered: &[crate::instances::InstanceInfo]) -> Vec<String> {
        let mut carriers: Vec<String> = Vec::new();
        for inst in registered {
            // The CONCLUSION of the instance's telescope, not its head. A derived
            // instance is Π-headed — `∀ {α} [Sho α], Sho (Option α)` — and
            // `extract_class_app` on the Π returns `None`, so such a candidate
            // contributed no carrier. When every candidate was Π-headed the
            // carrier list came back empty and the Options block took its
            // no-instance branch: the message LISTED a candidate and then said
            // "there is currently none", two screens apart, in one diagnostic.
            let mut concl = &inst.type_;
            while let clean_kernel::ExprKind::Pi(_, _, body) = concl.kind() {
                concl = body.as_ref();
            }
            if let Some((_, args)) = crate::instances::extract_class_app(concl) {
                if let Some(first) = args.first() {
                    let rendered = Self::render_goal_arg(first);
                    if !rendered.starts_with('?') && !carriers.contains(&rendered) {
                        carriers.push(rendered);
                    }
                }
            }
        }
        carriers.truncate(8);
        carriers
    }

    /// Lean's `solveSelfMax`: a postponed `?x =?= max ?x l` (satisfiable,
    /// `l ≤ ?x`) is closed by `?x := max ?x' l` with a FRESH universe `?x'`
    /// — the most general solution, and the only one that neither narrows
    /// the declaration's universes (`l := 0`) nor identifies two of them
    /// (`l := ?x`). Run before the drain, which would otherwise refuse the
    /// equation as circular. It is what the `Compl (α → Prop)` instance
    /// search leaves behind: `?ι := α` with `α : Type ?u` and `?u` already
    /// `max ?a ?b` from the class-level pre-check makes `?a =?= max ?a ?b`
    /// (measured 2026-09-11: `Std.Refl.compl`, `Ne.instIsEquiv_compl`, and
    /// every `example` over a `Type*` carrier that reached the kernel with
    /// `Sort (?u+1)` against `Sort (max ?u ?v + 1)`).
    pub(in crate::infer) fn resolve_self_max_level_equations(&mut self) {
        for _round in 0..8 {
            let mut progressed = false;
            for (l1, l2) in self.metas.postponed_level_equations() {
                let a = self.metas.instantiate_level(&l1);
                let b = self.metas.instantiate_level(&l2);
                for (x, rhs) in [(&a, &b), (&b, &a)] {
                    let Level::Param(name) = x else {
                        continue;
                    };
                    if self.metas.is_rigid_level_param(name)
                        || !matches!(rhs, Level::Max(..) | Level::IMax(..))
                        || !crate::unify::level_solve::level_param_occurs(name, rhs)
                    {
                        continue;
                    }
                    let fresh = self.fresh_universe_param();
                    let rest = rhs.substitute(&[(name.clone(), fresh.clone())]);
                    let solution = Level::max(fresh, rest);
                    if matches!(
                        crate::unify::level_solve::solve_level_eq_no_postpone(
                            &mut self.metas,
                            x,
                            &solution
                        ),
                        crate::unify::UnifyResult::Success
                    ) {
                        progressed = true;
                    }
                    break;
                }
            }
            if !progressed {
                return;
            }
        }
    }

    /// U2 rung 4 — the `levelMVarToParam` analog, run once at declaration
    /// close. Splits the surviving universe params into the DECLARED (rigid)
    /// head and the FRESH (auto-generalized) tail, orders the tail by first
    /// use (traversal order: type before value — Lean's ordering), renames it
    /// contiguously `u_1..u_k` (no gaps; mint-index gaps like `t5.{u_0,u_2}`
    /// were the measured naming divergence) and substitutes the renames into
    /// the declaration. Under a written `.{...}` list a fresh level the TYPE
    /// mentions is appended after the written names, as Lean's
    /// `sortDeclLevelParams` appends it, and one only the value mentions is
    /// refused (`docs/DECISIONS.md` R93, ledger class (164)); the list is not
    /// exhaustive in Lean. A written name the declaration never uses is
    /// dropped by the `used` filter below, where Lean refuses it ("unused
    /// universe parameter"): ledger class (165), OPEN.
    pub(super) fn finalize_level_params(
        &mut self,
        ty: Expr,
        val: Expr,
    ) -> Result<(Vec<Name>, Expr, Expr), ElabError> {
        self.retry_postponed_open_carrier_instances();
        // Canonicalize FIRST: the decl-close canonicalize pass
        // (`canonicalize_levels_in_elab_result`) resolves every level through
        // the union-find, so a rename applied to un-canonicalized exprs would
        // be clobbered when a resurrected mint-name flows back. After this,
        // whatever params remain are genuinely unsolved.
        // U2: DRAIN THE DEFERRED LEVEL QUEUE FIRST, and fail closed.
        //
        // The solver defers undetermined level equations (some side still
        // mentions a solvable parameter) instead of failing them, so a later
        // assignment can settle them. This is the boundary where "later" runs
        // out. Anything still unsolved here was ACCEPTED BY THE SOLVER AND
        // NEVER DISCHARGED, which is exactly the hole postponement would
        // otherwise open — so it is an error, not a warning.
        //
        // Drained BEFORE canonicalization on purpose: draining can assign
        // parameters, and canonicalize must see those assignments.
        self.resolve_self_max_level_equations();
        if let Err(msg) = self.metas.drain_postponed_levels() {
            return Err(ElabError::Unsupported { feature: msg });
        }
        self.retry_postponed_open_carrier_instances();
        let ty = self
            .metas
            .canonicalize_levels_in_expr(&self.metas.instantiate(&ty));
        let val = self
            .metas
            .canonicalize_levels_in_expr(&self.metas.instantiate(&val));
        let mut used = Vec::new();
        collect_def_level_params(&ty, &mut used);
        collect_def_level_params(&val, &mut used);
        let mut declared: Vec<Name> = Vec::new();
        let mut fresh: Vec<Name> = Vec::new();
        for s in &self.universe_params {
            let n = s.name().clone();
            if !used.contains(&n) {
                continue;
            }
            if self.metas.is_rigid_level_param(&n) {
                declared.push(n);
            } else {
                fresh.push(n);
            }
        }
        if fresh.is_empty() {
            return Ok((declared, ty, val));
        }
        fresh.sort_by_key(|n| used.iter().position(|u| u == n));
        // A WRITTEN `.{...}` list (U2 rung-4 explicitness channel,
        // 2026-08-25; corrected 2026-10-19). Lean does not treat the list as
        // exhaustive. `levelMVarToParamTypesPreDecls`
        // (`Lean/Elab/MutualDef.lean:1406`, `PreDefinition/Basic.lean:56`)
        // turns a universe metavariable left in the declaration's TYPE into a
        // fresh parameter, and `sortDeclLevelParams`
        // (`Lean/Elab/DeclUtil.lean:79-88`) APPENDS every used parameter the
        // list does not name after the written ones; its only error is a
        // written name the declaration never uses. Measured on the pinned
        // v4.30.0-rc2: `def leak.{u} (A : Type u) (a : A) := fun (B : Type _)
        // (b : B) => b` registers as `leak.{u, u_1}`, and `def noAns.{u} :
        // noEv → Type u := fun _ => PEmpty.{u+1}` as `noAns.{u, u_1}`. From
        // 2026-08-25 to 2026-10-19 Clean refused both, on a misreading of
        // that function (`docs/FRONTEND_CLASS_LEDGER.md` class (164)). A
        // metavariable left ONLY in the value is never generalized: Lean
        // refuses the declaration ("contains universe level metavariables
        // ... in the declaration body"), and so does this branch.
        //
        // `preprocess_decl_with_context` merges file-scope `universe` names
        // into the SAME `universe_params` vector as the written list;
        // `ElabCtx::file_universe_params` carries the file half,
        // `set_decl_universe_params` subtracts it, and `Some(..)` here means
        // the declaration genuinely wrote a list. A declaration with no
        // written list keeps generalizing every leftover, the value-only ones
        // included, where Lean refuses those too (the OPEN half of class
        // (164)).
        if let Some(explicit) = &self.decl_explicit_universes {
            let mut in_ty = Vec::new();
            collect_def_level_params(&ty, &mut in_ty);
            let value_only: Vec<String> = fresh
                .iter()
                .filter(|n| !in_ty.contains(n))
                .map(ToString::to_string)
                .collect();
            if !value_only.is_empty() {
                let list = explicit
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(", ");
                let n = value_only.len();
                let plural = if n == 1 { "level" } else { "levels" };
                return Err(ElabError::ExplicitUniverseListClosed {
                    detail: format!(
                        "the declaration's value leaves {n} undetermined universe {plural} \
                         ({}) that its type does not mention and the explicit universe list \
                         `.{{{list}}}` does not name. Lean generalizes a universe metavariable \
                         into an extra parameter only when the declaration's type mentions it, \
                         and refuses one left in the body (\"contains universe level \
                         metavariables\"). Write the level where it is used (`Sort v` rather \
                         than `Sort _`) and name `v` in the list, or constrain {} to a level the \
                         list already names.",
                        value_only.join(", "),
                        if n == 1 { "it" } else { "them" },
                    ),
                });
            }
        }
        // Rename targets come from `fresh_generalized_universe_param`: fresh
        // ids off the SAME monotone counter the metavariable mint draws from,
        // so they are guaranteed absent from the metas' union-find and the
        // decl-close canonicalize pass cannot rewrite them back into a solved
        // mint-name. The tail is a contiguous block in first-use order (the
        // measured divergence was mint-index GAPS like `t5.{u_0,u_2}`; 1-based
        // Lean-exact numbering is a cosmetic follow-up).
        //
        // THE SPELLING IS THE POINT (2026-08-26b). This is the levelMVarToParam
        // boundary: on the far side a level stops being a metavariable and
        // becomes part of the declaration's exported interface, so it must be
        // named in the WRITABLE space (`u_N`) even though every mint is now
        // named in the reserved one (`?u_N`). Because both minters share one
        // counter, the names this hands out did not move when the reservation
        // landed — `holeOnly` kept `u_1` at `2ce2cf2c1` and keeps `u_1` now.
        let mut subst: Vec<(Name, Level)> = Vec::new();
        let mut renamed: Vec<Name> = Vec::new();
        for f in &fresh {
            let tname = self.fresh_generalized_universe_param();
            subst.push((f.clone(), Level::param(tname.clone())));
            renamed.push(tname);
        }
        let (ty, val) = if subst.is_empty() {
            (ty, val)
        } else {
            (
                ty.instantiate_level_params(&subst),
                val.instantiate_level_params(&subst),
            )
        };
        declared.extend(renamed);
        Ok((declared, ty, val))
    }

    /// Type-only variant of [`Self::finalize_level_params`] (axioms/opaque
    /// declarations with no value expression).
    pub(super) fn finalize_level_params_ty(
        &mut self,
        ty: Expr,
    ) -> Result<(Vec<Name>, Expr), ElabError> {
        let (params, ty, _) = self.finalize_level_params(ty, Expr::sort(Level::zero()))?;
        Ok((params, ty))
    }
}

/// Replace every occurrence of the forward-declaration free variable `fvar`
/// with `Const(name)` (no universe args — the course-of-values auxiliary is
/// universe-monomorphic at `Nat → R × R`). Mirrors `replace_mutual_fvars` but
/// for the single auxiliary the pair-threading transform forward-declares.
fn replace_fvar_with_const(expr: Expr, fvar: FVarId, name: &Name) -> Expr {
    struct FvarToConst<'b> {
        fvar: FVarId,
        name: &'b Name,
    }
    impl ExprFolder for FvarToConst<'_> {
        fn fold_fvar(&mut self, id: FVarId) -> Expr {
            if id == self.fvar {
                Expr::const_(self.name.clone(), Vec::new())
            } else {
                Expr::fvar(id)
            }
        }
    }
    let mut folder = FvarToConst { fvar, name };
    folder.fold_expr(&expr)
}

impl<'a> ElabCtx<'a> {
    /// Course-of-values recursion via the pair-threading transform.
    ///
    /// Recognizes the two-prior `fib`-shape (`def f : Nat → R | 0 => .. | 1 =>
    /// .. | n + 2 => .. f (n+1) .. f n ..`) and lowers it to two ordinary
    /// declarations the existing single-step `Nat.rec` lowering already handles:
    ///
    /// - `f.cov : Nat → R × R` — the pair-threading auxiliary, single-step
    ///   structural recursion on the immediate predecessor.
    /// - `f (n : Nat) : R := Prod.fst (f.cov n)` — the projecting wrapper that
    ///   keeps the original surface name.
    ///
    /// Both are elaborated here and returned as an [`ElabResult::Multiple`] so
    /// the caller registers each into the kernel (which re-checks them — no
    /// `add_decl_unchecked`, no new axioms). Returns `Ok(None)` for every shape
    /// the transform does not recognize, leaving the standard path untouched.
    ///
    /// The wrapper references `f.cov`, which is not yet in the environment when
    /// its body elaborates (registration is deferred until this method returns).
    /// We bridge that exactly as the `mutual` path does: push `f.cov` as a
    /// forward local so the wrapper body resolves it, then rewrite that local
    /// fvar back to a `Const` in the final wrapper value.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn try_elab_course_of_values(
        &mut self,
        name: &SurfaceName,
        universe_params: &[SurfaceName],
        binders: &[SurfaceBinder],
        ty: Option<&SurfaceExpr>,
        val: &SurfaceExpr,
        attrs: &[Attribute],
        modifiers: &DeclModifiers,
    ) -> Result<Option<ElabResult>, ElabError> {
        let Some(plan) = super::course_of_values::try_pair_thread(name, binders, ty, val) else {
            return Ok(None);
        };

        // ---- Elaborate the auxiliary def `f.cov : Nat → R × R` ----
        // Route it through the ordinary definition path: `normalize_equation_def`
        // lifts its `_x` lambda to a binder, `setup_recursion` installs the
        // single-step IH, and `Nat.rec` lowering fires — the working k==1 path.
        self.set_decl_universe_params(universe_params);
        let aux_result = self.elab_definition_inner(
            &plan.aux_name,
            universe_params,
            &[],
            Some(&plan.aux_ty),
            &plan.aux_val,
            &[],
            &TerminationHints::default(),
            modifiers,
            &[],
        )?;

        // Recover the auxiliary's elaborated type so the forward local for the
        // wrapper carries the right signature.
        let aux_ty_expr = aux_result
            .declaration_type()
            .ok_or_else(|| ElabError::Unsupported {
                feature: "course-of-values: auxiliary def produced no type".to_string(),
            })?
            .clone();

        // ---- Elaborate the wrapper with `f.cov` pushed as a forward local ----
        self.set_decl_universe_params(universe_params);
        let aux_fvar: FVarId = self.push_local(plan.aux_name.clone(), aux_ty_expr);
        // The auxiliary registered above under its kernel name (`_private.M.0.
        // f.cov` for a private `f` — G21), so the wrapper names that constant.
        let aux_qualified =
            self.kernel_decl_name(&plan.aux_name, modifiers, PrivateNameKind::Definition);

        // The wrapper value is `fun (n : Nat) => Prod.fst (f.cov n)`; it already
        // carries its own binder, so elaborate it with an empty binder list and
        // the signature `Nat → R` reconstructed as an arrow.
        let wrapper_ty = SurfaceExpr::Arrow(
            clean_parser::Span::dummy(),
            Box::new(SurfaceExpr::Ident(
                clean_parser::Span::dummy(),
                SurfaceName::global_path("Nat"),
            )),
            Box::new(plan.wrapper_ret_ty.clone()),
        );
        let wrapper_outcome = self.elab_def_body(&[], Some(&wrapper_ty), &plan.wrapper_val);
        self.pop_local();
        let (wrapper_ty_expr, wrapper_val_expr) = wrapper_outcome?;

        let wrapper_ty_expr = self.metas.instantiate(&wrapper_ty_expr);
        let wrapper_val_expr = self.metas.instantiate(&wrapper_val_expr);
        let wrapper_ty_expr = self.metas.instantiate_levels(&wrapper_ty_expr);
        let wrapper_val_expr = self.metas.instantiate_levels(&wrapper_val_expr);

        // Rewrite the forward-local fvar `f.cov` back to a `Const` reference.
        let wrapper_val_expr = replace_fvar_with_const(wrapper_val_expr, aux_fvar, &aux_qualified);
        let wrapper_ty_expr = replace_fvar_with_const(wrapper_ty_expr, aux_fvar, &aux_qualified);

        let auto_implicits = self.take_auto_implicits();
        let (wrapper_ty_expr, wrapper_val_expr, _) = self.wrap_decl_auto_implicits(
            Self::section_binder_count(binders),
            wrapper_ty_expr,
            wrapper_val_expr,
            &auto_implicits,
            None,
        )?;

        let decl_name = self.kernel_decl_name(name, modifiers, PrivateNameKind::Definition);
        self.ensure_known_attributes(attrs)?;
        self.collect_attributes(&decl_name, attrs);

        let (surviving_universe_params, wrapper_ty_expr, wrapper_val_expr) =
            self.finalize_level_params(wrapper_ty_expr, wrapper_val_expr)?;

        let wrapper_result = ElabResult::Definition {
            name: decl_name,
            universe_params: surviving_universe_params,
            ty: wrapper_ty_expr,
            val: wrapper_val_expr,
            modifiers: *modifiers,
        };

        Ok(Some(ElabResult::Multiple(vec![aux_result, wrapper_result])))
    }

    /// Select indexed-child routing only from actual recursive-field metadata.
    fn applied_field_recursion_position(
        &self,
        name: &SurfaceName,
        binders: &[SurfaceBinder],
        body: &SurfaceExpr,
        parameters: &[SurfaceName],
        explicit_positions: &[usize],
        calls: &[super::structural::RecursiveCall],
    ) -> Option<usize> {
        let mut body = body;
        while let SurfaceExpr::Paren(_, inner)
        | SurfaceExpr::Lambda(_, _, inner)
        | SurfaceExpr::PatternMatchLambda(_, _, inner) = body
        {
            body = inner;
        }
        let SurfaceExpr::Match(_, _, scrutinee, arms) = body else {
            return None;
        };
        let SurfaceExpr::Ident(_, parameter) = scrutinee.as_ref() else {
            return None;
        };
        let position = parameters.iter().position(|name| name == parameter)?;
        if !calls.iter().any(|call| {
            matches!(
                call.args.get(position),
                Some(super::structural::RecursiveArg::AppliedField)
            )
        }) {
            return None;
        }
        let binder = binders.get(*explicit_positions.get(position)?)?;
        let mut domain = binder.ty.as_deref()?;
        while let SurfaceExpr::App(_, head, _)
        | SurfaceExpr::Paren(_, head)
        | SurfaceExpr::UniverseInst(_, head, _) = domain
        {
            domain = head;
        }
        let SurfaceExpr::Ident(_, head) = domain else {
            return None;
        };
        let super::elab_core::IdentTarget::Global(family) = self.resolve_global_ident_target(head)
        else {
            return None;
        };
        let family = self.env.get_inductive(&family)?;
        let rows: Vec<_> = arms
            .iter()
            .map(|arm| super::structural::DescentRow {
                pats: std::slice::from_ref(&arm.pattern),
                body: &arm.body,
            })
            .collect();
        (super::structural::classify_descent(
            self.env,
            name,
            &rows,
            0,
            Some(&family.name),
            position,
        ) == super::structural::Descent::Valid)
            .then_some(position)
    }

    /// Set up recursion handling shared by `def` and `theorem` elaboration (#1132).
    ///
    /// Detects whether the body recurses on `name`, applies any explicit
    /// `termination_by` hint, and then does one of two things:
    ///
    /// - **Well-founded recursion** (an explicit `termination_by <measure>` with
    ///   no resolvable structural decreasing argument): fully elaborates the
    ///   declaration through the WF lowering path and returns the resulting
    ///   `(type, value)` pair. The caller wraps this in the appropriate
    ///   `ElabResult` variant.
    /// - **Structural recursion**: installs `self.recursive_def_ctx` so the
    ///   subsequent `elab_def_body` call substitutes recursive calls with the
    ///   induction hypothesis, and returns `None`.
    ///
    /// Non-recursive declarations also return `None` without touching
    /// `recursive_def_ctx`, so the common (non-recursive) path is unchanged.
    pub(super) fn setup_recursion(
        &mut self,
        name: &SurfaceName,
        binders: &[SurfaceBinder],
        ty: Option<&SurfaceExpr>,
        val: &SurfaceExpr,
        termination: &TerminationHints,
    ) -> Result<Option<(Expr, Expr)>, ElabError> {
        // A reason recorded for an earlier declaration's self-call must not
        // name this one's refusal.
        self.recursive_call_miss = None;
        // Decreasing-argument positions live in CALL-ARGUMENT space: a surface
        // self-call passes only its OWN EXPLICIT binders, positionally. Section
        // parameters are captured by that recursive binding. (Implicit /
        // strict-implicit / instance binders are omitted at call sites), and
        // the one positional consumer of `decreasing_arg_pos` — `elab_app`'s
        // IH fast path — indexes surface call args too. Resolving detection
        // against the FULL binder list conflated the two spaces, so any def
        // with a leading implicit binder (`def lenM {α : Type} (xs : List α) …
        // lenM ys`) picked the type binder as "decreasing" and the self-call
        // died `RecursionOutsideFragment`. Detect against the explicit binders
        // and translate back to full binder indices where binders are sliced.
        // For all-explicit defs `explicit_positions` is the identity and
        // behavior is unchanged.
        let explicit_positions: Vec<usize> = binders
            .iter()
            .enumerate()
            .filter(|(_, b)| {
                !b.name.is_section_variable()
                    && matches!(b.info, clean_parser::SurfaceBinderInfo::Explicit)
            })
            .map(|(i, _)| i)
            .collect();
        let param_names: Vec<SurfaceName> = explicit_positions
            .iter()
            .map(|&i| binders[i].name.clone())
            .collect();
        let receiver_pos = self.method_dot_receiver_pos(name, binders);
        let mut recursion_info = super::structural::detect_recursion_with_receiver(
            name,
            val,
            &param_names,
            receiver_pos,
        );

        // Applied fields are NOT variables for the old spelling heuristic:
        // in particular `HSub.hSub n 1` must retain its well-founded route.
        // Only actual constructor metadata may select the indexed-child case.
        if let Some(position) = self.applied_field_recursion_position(
            name,
            binders,
            val,
            &param_names,
            &explicit_positions,
            &recursion_info.calls,
        ) {
            recursion_info.decreasing_arg = Some(position);
        }

        // Track AA: a fused nested-mutual fold's primary def (`Tree.size`) often
        // contains NO literal self-call — its only recursion is the SIBLING call
        // (`Tree.sizeList ts`), which the auto-detector does not see. But it IS
        // genuinely recursive: the sibling call becomes an induction hypothesis
        // of the fused `Tree.rec` application, so it must lower through `T.rec`
        // (not `T.casesOn`). When the aux-arm source is installed and a sibling
        // call appears in the body, force structural recursion on the sole/first
        // binder (the scrutinee). The kernel re-checks the recursor application,
        // so this never escapes soundness — it only routes to the right lowering.
        if !recursion_info.is_recursive {
            let forced = self.nested_mutual_aux_arms.as_ref().is_some_and(|aux| {
                !param_names.is_empty()
                    && aux
                        .sibling_signatures
                        .iter()
                        .any(|(sib, _)| super::structural::body_mentions_call(val, sib))
            });
            if forced {
                recursion_info.is_recursive = true;
                recursion_info.decreasing_arg = Some(0);
            }
        }

        if !recursion_info.is_recursive {
            return Ok(None);
        }

        // Check for explicit termination hints (#1132).
        // If `termination_by structural <param>` is specified, use that param
        // instead of the auto-detected decreasing argument.
        let explicit_dec_arg = termination
            .termination_by
            .as_ref()
            .map(|tb| match &tb.kind {
                clean_parser::TerminationKind::Structural(param_name) => {
                    if param_name.is_anonymous() {
                        Err(ElabError::Unsupported {
                            feature: "termination_by structural must select a parameter".into(),
                        })
                    } else if let Some(pos) = param_names.iter().position(|p| p == param_name) {
                        Ok(Some((pos, param_name.clone())))
                    } else {
                        Err(ElabError::Unsupported {
                            feature: format!(
                                "termination_by structural {} (unknown parameter)",
                                param_name
                            ),
                        })
                    }
                }
                // WellFounded and Query don't specify a structural param,
                // so fall back to auto-detection.
                clean_parser::TerminationKind::WellFounded
                | clean_parser::TerminationKind::Query => Ok(None),
            });

        // Use explicit hint if provided, otherwise use auto-detected position.
        // Both are call-argument-space positions; the binder is found through
        // `explicit_positions`.
        let dec_arg = explicit_dec_arg.transpose()?.flatten().or_else(|| {
            recursion_info.decreasing_arg.and_then(|pos| {
                explicit_positions
                    .get(pos)
                    .and_then(|&binder_pos| binders.get(binder_pos))
                    .map(|b| (pos, b.name.clone()))
            })
        });

        // ROUTING (R3): an explicit `termination_by <parameter>` is a
        // DECLARATION; `detect_recursion_with_params` is a HEURISTIC. When
        // they name different parameters, the declaration wins and the
        // definition is routed to the well-founded lowering.
        //
        // This is what `gcd` needs. `def gcd (a b : Nat) := … gcd b (a % b)`
        // has a self-call whose FIRST argument is a bare identifier (`b`)
        // spelled differently from the first parameter (`a`), which is
        // exactly the shape `find_decreasing_arg`'s name-inequality rule
        // reads as "position 0 decreases". Nothing about `b` is structurally
        // smaller than `a`, so the structural lowering could only fail — and
        // it failed as `UnknownIdent`/`RecursionOutsideFragment`, never
        // reaching the well-founded path the user asked for by writing
        // `termination_by b`.
        //
        // Deliberately narrow. It fires ONLY for the modern
        // `termination_by <measure>` form (`tb.params` empty — the
        // `termination_by x y => …` form REBINDS the parameters, so an
        // identifier there is not a parameter reference), and only when the
        // measure mentions EXACTLY ONE parameter. A measure that names the
        // position the detector already picked leaves routing untouched: a
        // structurally-recursive definition carrying `termination_by n` still
        // lowers structurally.
        //
        // R5 (2026-08-25) — the spelling hole. R3 matched a BARE
        // `SurfaceExpr::Ident` and nothing else, so the rule it established
        // ("the declaration beats the heuristic") silently stopped applying
        // the moment the measure was written any other way. Measured at pin
        // `99e2128ef`: `termination_by b + 0` and `termination_by b.toNat` on
        // an otherwise-identical `gcd` were both refused
        // `RecursionOutsideFragment` — R3's own bug, one spelling over —
        // while `termination_by b` elaborated. `sole_mentioned_param` closes
        // that by asking which parameters the measure MENTIONS, which is the
        // same "exactly one parameter" rule `elab_wf_recursion_core`'s phase
        // 2b applies to the elaborated measure, so routing and lowering now
        // agree instead of drifting.
        //
        // It answers `None` for any measure containing a binder, which is the
        // pre-existing behaviour — so this can only ADMIT shapes that were
        // previously refused, never redirect one that already worked. Nothing
        // about proof authority moves: the lowering re-derives the parameter
        // from real `FVar`s, requires a `Nat`-valued measure, and still
        // discharges or refuses every decreasing obligation itself.
        let wf_measure_param_pos = termination
            .termination_by
            .as_ref()
            .filter(|tb| {
                matches!(tb.kind, clean_parser::TerminationKind::WellFounded)
                    && tb.params.is_empty()
            })
            .and_then(|tb| tb.measure.as_deref())
            .and_then(|measure| {
                super::wf_recursion::measure_params::sole_mentioned_param(measure, &param_names)
            });
        // R6 (2026-08-25) — the same rule, at a measure over SEVERAL
        // parameters. A SUM measure (`termination_by a + b`) is now lowered by
        // `wf_recursion::sum_measure`, so the declaration must beat the
        // heuristic there too: no single structural position can be what the
        // user asked for, and the structural path could only fail. Before
        // this, `def gcdSub (a b : Nat) := … gcdSub (a-b) b … gcdSub a (b-a)`
        // with `termination_by a + b` died `RecursionOutsideFragment` — the
        // detector read the bare `a` at position 0 of the second self-call as
        // "position 0 decreases" — and never reached the lowering at all.
        //
        // Narrow, on purpose and for the same reason as R3/R5: it fires only
        // for the modern `termination_by <measure>` form, only when the
        // measure is `+`-headed at the surface, and only when it mentions at
        // least TWO parameters — i.e. exactly the class the lowering admits.
        // A non-sum multi-parameter measure keeps today's routing untouched,
        // so this can only ADMIT shapes that were previously refused.
        let wf_measure_is_sum = termination
            .termination_by
            .as_ref()
            .filter(|tb| {
                matches!(tb.kind, clean_parser::TerminationKind::WellFounded)
                    && tb.params.is_empty()
            })
            .and_then(|tb| tb.measure.as_deref())
            .is_some_and(|measure| {
                super::wf_recursion::measure_shape::is_surface_nat_sum(measure)
                    && super::wf_recursion::measure_params::mentioned_params(measure, &param_names)
                        .is_some_and(|mentioned| mentioned.len() >= 2)
            });
        let dec_arg = if wf_measure_is_sum {
            None
        } else {
            match (&dec_arg, wf_measure_param_pos) {
                (Some((pos, _)), Some(measure_pos)) if *pos != measure_pos => None,
                _ => dec_arg,
            }
        };

        if let Some((dec_pos, dec_name)) = dec_arg {
            // Extract well-founded measure if present (#1132).
            let wf_measure = termination
                .termination_by
                .as_ref()
                .and_then(|tb| match &tb.kind {
                    clean_parser::TerminationKind::WellFounded => tb.measure.clone(),
                    _ => None,
                });

            // Capture actual sibling annotations in declaration scope, before
            // pattern names could shadow constants used by those annotations.
            let mut sibling_types = Vec::new();
            if let Some(aux) = self.nested_mutual_aux_arms.clone() {
                for (member, source_type) in aux.sibling_signatures {
                    let member_type = self.elaborate(&source_type)?;
                    let _member_universe = self.infer_sort(&member_type)?;
                    sibling_types.push((self.qualify_name(&member), member_type));
                }
            }
            // Set up recursive definition context. Store the *qualified* name
            // (e.g. `TrustIr.Ty.bitWidth` inside `namespace TrustIr`) so the
            // call-site IH substitution can recognise namespace-qualified and
            // method-dot-notation self-references that resolve to the fully
            // qualified constant (Track R, Basic.lean `Ty.bitWidth`).
            self.recursive_def_ctx = Some(RecursiveDefContext {
                func_name: self.qualify_name(name),
                decreasing_arg_pos: dec_pos,
                decreasing_arg_name: dec_name,
                inductive_type_name: None, // Will be set during elaboration
                ih_fvar: None,
                ih_type: None,
                ih_map: HashMap::new(),
                // Track AA: a fused nested-mutual fold installs the sibling
                // function names on `nested_mutual_aux_arms`; copy them here so a
                // sibling self-call inside a minor body is recognized. Empty for
                // ordinary recursion (no aux-arm source installed).
                sibling_names: sibling_types.iter().map(|(name, _)| name.clone()).collect(),
                sibling_types,
                parameters: Vec::new(),
                generalized_params: Vec::new(),
                index_params: Vec::new(),
                wf_measure,
                outer_locals_floor: None,
            });
            Ok(None)
        } else if let Some(tb) = termination.termination_by.as_ref() {
            // The same predicate routes a `where` helper here
            // (`try_elab_let_rec_lifted`).
            if let Some(measure_expr) = tb.well_founded_measure() {
                // Well-founded recursion with explicit measure.
                // Use the WF elaboration path instead of structural recursion.
                let measure = super::wf_recursion::pre_definition::TerminationMeasure {
                    params: tb.params.clone(),
                    measure_expr: Box::new(measure_expr.clone()),
                    decreasing_by: termination
                        .decreasing_by
                        .as_ref()
                        .map(|db| db.tactic.clone()),
                };

                let (ty_expr, val_expr) =
                    self.elab_wf_recursion(name, binders, ty, val, &measure)?;

                // Substitute metavariables.
                let ty_expr = self.metas.instantiate(&ty_expr);
                let val_expr = self.metas.instantiate(&val_expr);
                let ty_expr = self.metas.instantiate_levels(&ty_expr);
                let val_expr = self.metas.instantiate_levels(&val_expr);

                return Ok(Some((ty_expr, val_expr)));
            }
            Ok(None)
        } else {
            Ok(None)
        }
    }

    /// Elaborate a `def` declaration.
    ///
    /// Handles recursive definition detection, termination hints,
    /// auto-implicits, and metavariable instantiation.
    pub(super) fn elab_definition_inner(
        &mut self,
        name: &SurfaceName,
        universe_params: &[SurfaceName],
        binders: &[SurfaceBinder],
        ty: Option<&SurfaceExpr>,
        val: &SurfaceExpr,
        attrs: &[Attribute],
        termination: &TerminationHints,
        modifiers: &DeclModifiers,
        where_decls: &[WhereLocalDef],
    ) -> Result<ElabResult, ElabError> {
        let attr_name = self.kernel_decl_name(name, modifiers, PrivateNameKind::Definition);
        self.collect_syntactic_defeq(&attr_name, val);

        // A SELF-RECURSIVE `partial def name : T := … name …`: Lean treats a
        // partial def as an opaque/unsafe constant — its body is NOT
        // termination-checked and the constant does not reduce in the kernel.
        // Register `name : T` as an OPAQUE declaration so the body's
        // self-reference — the whole reason such a partial def exists, and the
        // reason the ordinary recursion path can't elaborate it — resolves
        // against the signature, and discard the body. SOUNDNESS: an opaque
        // `name : T` is, kernel-wise, an axiom, so `T` MUST be inhabited —
        // otherwise `partial def f : False := f` would register an unsound
        // `f : False`. Lean requires `Inhabited T`; we FAIL LOUD otherwise.
        //
        // A NON-recursive partial def (`partial def p : Nat := 0`) has a valid
        // body and keeps the ordinary `Definition` path (carrying `is_partial`);
        // only the self-referencing case, which that path can't resolve, is
        // rerouted. Requires an explicit result type.
        if modifiers.is_partial {
            if let Some(ty) = ty {
                if super::course_of_values::body_calls(val, name) {
                    return self.elab_partial_def_opaque(
                        name,
                        universe_params,
                        binders,
                        ty,
                        attrs,
                        modifiers,
                    );
                }
            }
        }

        // Desugar where-clause local defs into let-rec wrapping the body.
        // Dependency-ordered (Lean's `where` decls form ONE mutually visible
        // `let rec` group — Lean/Elab/Binders.lean:472-476 expandWhereDecls,
        // Lean/Elab/LetRec.lean:87 withAuxLocalDecls — so acyclic forward
        // references must still resolve). Duplicate names and genuinely
        // mutual (cyclic) groups FAIL LOUD; they are never lowered to a
        // shape that would register with a placeholder.
        self.register_where_termination(where_decls);
        let val = if where_decls.is_empty() {
            val.clone()
        } else {
            crate::where_desugar_ext::desugar_where_from_parsed_ordered(val, where_decls).map_err(
                |e| ElabError::WhereLetRecUnsupported {
                    name: name.to_string(),
                    shape: format!("`where` block rejected: {e}"),
                },
            )?
        };
        let val = &val;

        // Course-of-values recursion (the `fib`-shape `n + 2 => f (n+1) + f n`).
        // Bare `Nat.rec` gives the succ minor exactly one immediate IH, so a
        // two-prior recurrence cannot lower directly. We rewrite it into the
        // fast-`fib` pair-threading form — a single-step auxiliary over `R × R`
        // plus a projecting wrapper — which reuses the existing `Nat.rec` (#20)
        // and `Prod` matcher (#21) lowering. Returns `None` for every other
        // shape, leaving the path below unchanged. This runs BEFORE
        // `normalize_equation_def` so the un-normalized `PatternMatchLambda`
        // shape (which the detector keys on) is still intact.
        if let Some(result) = self.try_elab_course_of_values(
            name,
            universe_params,
            binders,
            ty,
            val,
            attrs,
            modifiers,
        )? {
            return Ok(result);
        }

        // Normalize equation-form defs (`def f : A → B | pat => ...`) into the
        // named-binder + `match` shape so structural recursion lowers via the
        // inductive's `.rec` (Task 3, slice 1). Returns `None` for non-equation
        // declarations, leaving the common path unchanged.
        for arm in whole_body_match_arms(val) {
            self.check_pattern_linear(&arm.pattern)?;
        }
        let idents = self.pattern_idents(val);
        let normalized = normalize_equation_def(self.env, &idents, name, binders, ty, val)?;
        let written_binders = binders;
        let (binders, ty, val): (&[SurfaceBinder], Option<&SurfaceExpr>, &SurfaceExpr) =
            match &normalized {
                Some((lifted_binders, new_ty, match_body)) => {
                    (lifted_binders, new_ty.as_ref(), match_body)
                }
                None => (binders, ty, val),
            };

        let mut resolved_termination = termination.clone();
        if let Some(tb) = resolved_termination.termination_by.as_mut() {
            if let Some(index) = Self::structural_hint_index(tb, written_binders, binders.len())
                .map_err(|feature| ElabError::Unsupported { feature })?
            {
                tb.kind = clean_parser::TerminationKind::Structural(binders[index].name.clone());
                tb.params.clear();
                tb.measure = None;
            }
        }
        let termination = &resolved_termination;

        // A recursive def whose `match` on the decreasing parameter sits
        // inside a context (`1 + match n with …`, `if a = 0 then … else match
        // b with …`, an equation's case split on another column) has the
        // context moved into the match's arms, so the recursor computes the
        // whole definition, as Lean's `brecOn` does
        // (`structural::hoist_recursive_match`). What this declines is judged
        // by the recursion-site check after elaboration.
        let hoisted = super::structural::hoist_recursive_match(self.env, name, binders, val);
        let val: &SurfaceExpr = hoisted.as_ref().unwrap_or(val);

        // Brick 84: a RECURSIVE def whose body is a multi-scrutinee
        // `match a, b with` over its own binders. The parser packed the
        // scrutinees into ONE right-nested `Prod.mk` tuple, which never
        // matches the decreasing-arg ident, so `use_rec` cannot fire and the
        // self-call dies UnknownIdent. Rewrite to the nested single-scrutinee
        // form BEFORE `setup_recursion` so the existing IH machinery works
        // unchanged. Engagement-gated on recursion: non-recursive
        // multi-scrutinee matches keep the tuple-`casesOn` path untouched.
        let explicit_structural =
            termination
                .termination_by
                .as_ref()
                .and_then(|tb| match &tb.kind {
                    clean_parser::TerminationKind::Structural(param) if !param.is_anonymous() => {
                        Some(param)
                    }
                    _ => None,
                });
        let multi_scrut =
            normalize_multi_scrutinee_match_body(&idents, name, binders, val, explicit_structural)?;
        let val: &SurfaceExpr = multi_scrut.as_ref().unwrap_or(val);

        // The recursion-aware refusal quotes this declaration's parameter
        // count, and the count that means anything is the one the recursion
        // machinery works with — i.e. AFTER equation-form normalization has
        // lifted binders out of the arrow type. `def gcd3 : Nat → Nat → Nat |
        // a, 0 => a | a, b => gcd3 b (a % b)` writes no binders at all, so the
        // surface count seeded at `elab_decl` entry would report 0 parameters
        // for a two-parameter function. Diagnostic-only; nothing reads it
        // unless resolution has already failed.
        if let Some(subject) = self.self_reference.as_mut() {
            if &subject.written == name {
                subject.params = binders.len();
            }
        }

        // Set universe params
        self.set_decl_universe_params(universe_params);

        // Detect recursion and apply termination hints (#378, #1132).
        // Returns Some((ty, val)) only for the well-founded lowering early-return
        // path; otherwise installs the structural recursion context (if any) and
        // returns None so the standard body path runs below.
        if let Some((ty_expr, val_expr)) =
            self.setup_recursion(name, binders, ty, val, termination)?
        {
            // Wrap with auto-implicit binders.
            let auto_implicits = self.take_auto_implicits();
            let (ty_expr, val_expr, _) = self.wrap_decl_auto_implicits(
                Self::section_binder_count(binders),
                ty_expr,
                val_expr,
                &auto_implicits,
                None,
            )?;

            let decl_name = self.kernel_decl_name(name, modifiers, PrivateNameKind::Definition);
            self.ensure_known_attributes(attrs)?;
            self.collect_attributes(&decl_name, attrs);

            // Filter to surviving params only (#3396).
            let (surviving_universe_params, ty_expr, val_expr) =
                self.finalize_level_params(ty_expr, val_expr)?;

            return Ok(ElabResult::Definition {
                name: decl_name,
                universe_params: surviving_universe_params,
                ty: ty_expr,
                val: val_expr,
                modifiers: *modifiers,
            });
        }

        // Elaborate binders as pi types around the type, lambdas around the value
        // Use a closure to ensure recursive context is cleared even on error.
        // `where` / `let rec` helpers met on the way lift to `<decl>.<name>`
        // auxiliary declarations (`let_rec_lift`), finished below.
        // A private parent's helpers inherit its kernel name, so `where go`
        // of a private `f` is `_private.M.0.f.go`, as Lean names it (G21).
        let saved_lift = self.begin_let_rec_lift(
            self.kernel_decl_name(name, modifiers, PrivateNameKind::Definition),
            modifiers.is_partial,
        );
        let result = self.elab_decl_body(binders, ty, val);
        let lift_scope = self.end_let_rec_lift(saved_lift);

        // Clear recursive context after elaboration (must happen even on error)
        self.recursive_def_ctx = None;

        let (ty_expr, val_expr, section_fvars) = result?;

        // Substitute metavariables (#163: unsolved metavariables from typeclass
        // resolution would otherwise leak as FVars to the kernel type checker)
        let ty_expr = self.metas.instantiate(&ty_expr);
        let val_expr = self.metas.instantiate(&val_expr);

        // Substitute level constraints collected during unification
        let ty_expr = self.metas.instantiate_levels(&ty_expr);
        let val_expr = self.metas.instantiate_levels(&val_expr);

        // Wrap with auto-implicit binders (#164)
        // Auto-implicits are added in order of first occurrence (reversed for Pi/Lambda)
        let auto_implicits = self.take_auto_implicits();
        let (ty_expr, val_expr, section_auto_count) = self.wrap_decl_auto_implicits(
            Self::section_binder_count(binders),
            ty_expr,
            val_expr,
            &auto_implicits,
            Some(&section_fvars),
        )?;

        // Collect all attributes for later registration
        let decl_name = self.kernel_decl_name(name, modifiers, PrivateNameKind::Definition);

        // When `preprocess` could not scan this body (a `by` block, …) it
        // prepended EVERY section variable; keep the ones the elaborated
        // header and value use — Lean's `removeUnusedVars`
        // (`Lean/Elab/MutualDef.lean:593-609`). No-op unless armed.
        let (ty_expr, val_expr) = self.prune_armed_section_binders(
            &decl_name,
            binders.iter().map(|b| &b.name),
            section_auto_count,
            ty_expr,
            val_expr,
        );
        // B21: reject unknown attributes loudly before honoring the rest.
        self.ensure_known_attributes(attrs)?;
        self.collect_attributes(&decl_name, attrs);

        // Use self.universe_params which includes auto-bound params from
        // fresh_universe_param() during elaboration (e.g., auto-implicit
        // `def f (x : A) : A := x` auto-binds u_0 for A : Sort(u_0)).
        // Fix for #1324: previously used parser's explicit universe_params
        // which is empty when universe params are auto-bound.
        //
        // Fix for #3396: filter universe_params to only those that actually
        // appear in the final type/value expressions. When an abbrev like
        // `abbrev MySem (a : Type) := StateT MyState (Except MyError) a`
        // is applied to concrete types, `instantiate_levels` resolves the
        // auto-generated params (u_0, u_1, ...) to concrete levels (Zero),
        // but they remain in `universe_params`. This causes level count
        // mismatches when the definition is later unfolded.
        // Same pattern as #3390 fix for structures (see elab_structure.rs).
        // Ordinary definitions must solve expression metavariables. Aliases
        // preserve the target telescope directly in their own elaborator.
        let (surviving_universe_params, ty_expr, val_expr) =
            self.finalize_level_params(ty_expr, val_expr)?;

        let (auxiliaries, val_expr) =
            self.finish_let_rec_lifts(lift_scope, &surviving_universe_params, modifiers, val_expr)?;

        self.ensure_no_residual_fvars("def", name, &ty_expr, Some(&val_expr))?;

        let definition = ElabResult::Definition {
            name: decl_name,
            universe_params: surviving_universe_params,
            ty: ty_expr,
            val: val_expr,
            modifiers: *modifiers,
        };
        Ok(Self::with_let_rec_auxiliaries(auxiliaries, definition))
    }

    /// Elaborate a `theorem` declaration.
    ///
    /// Similar to `elab_definition_inner` but produces `ElabResult::Theorem`.
    pub(super) fn elab_theorem_inner(
        &mut self,
        name: &SurfaceName,
        universe_params: &[SurfaceName],
        binders: &[SurfaceBinder],
        ty: &SurfaceExpr,
        proof: &SurfaceExpr,
        attrs: &[Attribute],
        termination: &TerminationHints,
        modifiers: &DeclModifiers,
        where_decls: &[WhereLocalDef],
    ) -> Result<ElabResult, ElabError> {
        let attr_name = self.kernel_decl_name(name, modifiers, PrivateNameKind::Theorem);
        self.collect_syntactic_defeq(&attr_name, proof);

        // Lean refuses the modifier before it reads the theorem: pinned 4.8.0
        // and 4.30.0-rc2, "'unsafe' theorems are not allowed" (review r6, X10).
        if modifiers.is_unsafe {
            return Err(ElabError::CommandFailed {
                message: "'unsafe' theorems are not allowed".to_string(),
            });
        }
        // Desugar where-clause local defs for theorems. Same contract as the
        // `def` path above: dependency-ordered, duplicate/cyclic groups fail
        // loud, no placeholder registration.
        self.register_where_termination(where_decls);
        let proof = if where_decls.is_empty() {
            proof.clone()
        } else {
            crate::where_desugar_ext::desugar_where_from_parsed_ordered(proof, where_decls)
                .map_err(|e| ElabError::WhereLetRecUnsupported {
                    name: name.to_string(),
                    shape: format!("`where` block rejected: {e}"),
                })?
        };
        let proof = &proof;

        // Normalize equation-form theorems (`theorem t : A → B | pat => ...`)
        // into named-binder + `match` shape, mirroring the definition path so
        // structural recursion lowers via `.rec` (Task 3, slice 1).
        for arm in whole_body_match_arms(proof) {
            self.check_pattern_linear(&arm.pattern)?;
        }
        let idents = self.pattern_idents(proof);
        let normalized = normalize_equation_def(self.env, &idents, name, binders, Some(ty), proof)?;
        let written_binders = binders;
        let (binders, ty, proof): (&[SurfaceBinder], &SurfaceExpr, &SurfaceExpr) = match &normalized
        {
            // A normalized equation theorem must have a peeled return type;
            // if normalization somehow produced `None` for the type, fall
            // back to the original shape rather than fabricate one.
            Some((lifted_binders, Some(new_ty), match_body)) => {
                (lifted_binders, new_ty, match_body)
            }
            _ => (binders, ty, proof),
        };

        let mut resolved_termination = termination.clone();
        if let Some(tb) = resolved_termination.termination_by.as_mut() {
            if let Some(index) = Self::structural_hint_index(tb, written_binders, binders.len())
                .map_err(|feature| ElabError::Unsupported { feature })?
            {
                tb.kind = clean_parser::TerminationKind::Structural(binders[index].name.clone());
                tb.params.clear();
                tb.measure = None;
            }
        }
        let termination = &resolved_termination;

        self.set_decl_universe_params(universe_params);

        // Handle termination hints for recursive theorems (#1132).
        // Most theorems are not recursive, in which case `setup_recursion`
        // returns `None` without touching `recursive_def_ctx`, leaving the
        // common non-recursive path below unchanged. A recursive theorem with
        // an explicit `termination_by <measure>` is lowered through the
        // well-founded path; structural recursion installs the IH context for
        // the `elab_def_body` call.
        if let Some((ty_expr, proof_expr)) =
            self.setup_recursion(name, binders, Some(ty), proof, termination)?
        {
            // Well-founded lowering early-return path.
            let auto_implicits = self.take_auto_implicits();
            let (ty_expr, proof_expr, _) = self.wrap_decl_auto_implicits(
                Self::section_binder_count(binders),
                ty_expr,
                proof_expr,
                &auto_implicits,
                None,
            )?;

            let decl_name = self.kernel_decl_name(name, modifiers, PrivateNameKind::Theorem);
            self.ensure_known_attributes(attrs)?;
            self.collect_attributes(&decl_name, attrs);

            let (surviving_universe_params, ty_expr, proof_expr) =
                self.finalize_level_params(ty_expr, proof_expr)?;

            self.ensure_no_residual_fvars("theorem", name, &ty_expr, Some(&proof_expr))?;

            return Ok(ElabResult::Theorem {
                name: decl_name,
                universe_params: surviving_universe_params,
                ty: ty_expr,
                proof: proof_expr,
                modifiers: *modifiers,
            });
        }

        // Elaborate binders/body. The structural recursion context (if installed
        // by `setup_recursion`) is consumed here and must be cleared afterward,
        // even on error.
        let saved_lift = self.begin_let_rec_lift(
            self.kernel_decl_name(name, modifiers, PrivateNameKind::Theorem),
            modifiers.is_partial,
        );
        // A recursive self-call inside `by` becomes visible only after tactic
        // elaboration. When the surface structural path did not install an IH
        // context, let the pre-definition's real call graph choose its SCC.
        // Keep explicit termination hints on their existing validating path.
        let mut predef_auto_count = None;
        let result = if (normalized.is_some()
            || matches!(
                proof,
                SurfaceExpr::PatternMatchLambda(..)
                    | SurfaceExpr::ByTactic(..)
                    | SurfaceExpr::CalcBlock(..)
            ))
            && self.recursive_def_ctx.is_none()
            && termination.termination_by.is_none()
            && termination.decreasing_by.is_none()
        {
            self.elab_single_equation_theorem(name, binders, ty, proof, modifiers)
                .map(|(ty_expr, proof_expr, auto_count)| {
                    predef_auto_count = Some(auto_count);
                    (ty_expr, proof_expr, Vec::new())
                })
        } else {
            self.elab_decl_body(binders, Some(ty), proof)
        };
        let lift_scope = self.end_let_rec_lift(saved_lift);
        self.recursive_def_ctx = None;
        let (ty_expr, proof_expr, section_fvars) = result?;

        // Substitute metavariables (#163)
        let ty_expr = self.metas.instantiate(&ty_expr);
        let proof_expr = self.metas.instantiate(&proof_expr);

        // Substitute level constraints collected during unification
        let ty_expr = self.metas.instantiate_levels(&ty_expr);
        let proof_expr = self.metas.instantiate_levels(&proof_expr);

        // Wrap with auto-implicit binders (#164)
        let auto_implicits = self.take_auto_implicits();
        let (ty_expr, proof_expr, section_auto_count) = self.wrap_decl_auto_implicits(
            Self::section_binder_count(binders),
            ty_expr,
            proof_expr,
            &auto_implicits,
            Some(&section_fvars),
        )?;

        // Collect all attributes for later registration
        let decl_name = self.kernel_decl_name(name, modifiers, PrivateNameKind::Theorem);

        // When `preprocess` could not scan this theorem's HEADER it prepended
        // EVERY section variable; keep what Lean's `withHeaderSecVars`
        // (`Lean/Elab/MutualDef.lean:454-490`) keeps over the elaborated
        // statement. No-op unless armed.
        let (ty_expr, proof_expr) = self.prune_armed_section_binders(
            &decl_name,
            binders.iter().map(|b| &b.name),
            predef_auto_count.unwrap_or(section_auto_count),
            ty_expr,
            proof_expr,
        );
        // B21: reject unknown attributes loudly before honoring the rest.
        self.ensure_known_attributes(attrs)?;
        self.collect_attributes(&decl_name, attrs);

        // Use self.universe_params which includes auto-bound params
        // (same fix as Definition, see #1324)
        // Filter to surviving params only (#3396, same as Definition).
        let (surviving_universe_params, ty_expr, proof_expr) =
            self.finalize_level_params(ty_expr, proof_expr)?;

        let (auxiliaries, proof_expr) = self.finish_let_rec_lifts(
            lift_scope,
            &surviving_universe_params,
            modifiers,
            proof_expr,
        )?;

        self.ensure_no_residual_fvars("theorem", name, &ty_expr, Some(&proof_expr))?;

        let theorem = ElabResult::Theorem {
            name: decl_name,
            universe_params: surviving_universe_params,
            ty: ty_expr,
            proof: proof_expr,
            modifiers: *modifiers,
        };
        Ok(Self::with_let_rec_auxiliaries(auxiliaries, theorem))
    }

    /// Elaborate an `axiom` declaration.
    ///
    /// Axioms have a type but no value expression.
    pub(super) fn elab_axiom_inner(
        &mut self,
        name: &SurfaceName,
        universe_params: &[SurfaceName],
        binders: &[SurfaceBinder],
        ty: &SurfaceExpr,
        attrs: &[Attribute],
        modifiers: &DeclModifiers,
    ) -> Result<ElabResult, ElabError> {
        self.set_decl_universe_params(universe_params);
        let (ty_expr, section_fvars) = self.elab_decl_type(binders, ty)?;

        // Substitute metavariables (#163)
        let ty_expr = self.metas.instantiate(&ty_expr);

        // Substitute level constraints collected during unification
        let ty_expr = self.metas.instantiate_levels(&ty_expr);

        // Wrap with auto-implicit binders (#164)
        let auto_implicits = self.take_auto_implicits();
        let (ty_expr, section_auto_count) = self.wrap_decl_type_auto_implicits(
            Self::section_binder_count(binders),
            ty_expr,
            &auto_implicits,
            Some(&section_fvars),
        )?;

        // Collect all attributes for later registration
        let decl_name = self.kernel_decl_name(name, modifiers, PrivateNameKind::Axiom);
        let ty_expr = self.prune_armed_section_type(
            &decl_name,
            binders.iter().map(|binder| &binder.name),
            section_auto_count,
            ty_expr,
        );
        // B21: reject unknown attributes loudly before honoring the rest.
        self.ensure_known_attributes(attrs)?;
        self.collect_attributes(&decl_name, attrs);

        // Use self.universe_params which includes auto-bound params
        // (same fix as Definition, see #1324)
        // Filter to surviving params only (#3396, same as Definition).
        let (surviving_universe_params, ty_expr) = self.finalize_level_params_ty(ty_expr)?;

        Ok(ElabResult::Axiom {
            name: decl_name,
            universe_params: surviving_universe_params,
            ty: ty_expr,
            modifiers: *modifiers,
        })
    }

    /// Elaborate ONLY a declaration's SIGNATURE into a header: its
    /// namespace-qualified name, its surviving universe parameters, and its
    /// type. The body/proof is not elaborated and nothing is registered.
    ///
    /// This is the primitive that header-first, two-phase checking is built on
    /// (Trust I1): every declaration's header is elaborated before ANY body is,
    /// so name resolution sees the whole symbol table and stops depending on
    /// source order. It is deliberately the SAME computation `elab_axiom_inner`
    /// already performs for the signature of an `axiom` — an axiom *is* a
    /// header — minus attribute collection, which belongs to the authoritative
    /// pass that registers the real declaration.
    ///
    /// SOUNDNESS — a header is a TYPE, never a proof. Installing one as a
    /// constant is indistinguishable, to everything downstream, from asserting
    /// an axiom the user never wrote. A caller may therefore install headers
    /// ONLY in a non-authoritative staging environment, and owes two things
    /// this function cannot check for it:
    ///
    ///   1. elaborate a body only once every declaration it actually depends on
    ///      is a real, kernel-checked definition — never against the header of
    ///      something still unproved; and
    ///   2. verify, after registration, that the registered term mentions no
    ///      still-staged header.
    ///
    /// Without (2) a dependency scan that misses an edge silently upgrades a
    /// header into an assumption backing a kernel-certified proof. With it, a
    /// missed edge can only cause a spurious rejection.
    pub(crate) fn elab_decl_header_inner(
        &mut self,
        name: &SurfaceName,
        private_kind: Option<PrivateNameKind>,
        universe_params: &[SurfaceName],
        binders: &[SurfaceBinder],
        ty: &SurfaceExpr,
    ) -> Result<(Name, Vec<Name>, Expr), ElabError> {
        self.set_decl_universe_params(universe_params);
        let (ty_expr, section_fvars) = self.elab_decl_type(binders, ty)?;

        // Same normalization the axiom path applies: metavariables and level
        // constraints solved during signature unification must be substituted
        // before the type is used as a header, or the staged constant carries
        // unsolved holes the kernel would reject.
        let ty_expr = self.metas.instantiate(&ty_expr);
        let ty_expr = self.metas.instantiate_levels(&ty_expr);

        let auto_implicits = self.take_auto_implicits();
        let (ty_expr, _) = self.wrap_decl_type_auto_implicits(
            Self::section_binder_count(binders),
            ty_expr,
            &auto_implicits,
            Some(&section_fvars),
        )?;

        // The name the authoritative pass registers (a private theorem's
        // mangled name included — G21), so a header matches its declaration.
        let decl_name = self.kernel_decl_name_for(name, private_kind);

        // Filter to surviving params only (#3396, as Definition/Axiom do).
        let mut used_level_params = Vec::new();
        collect_def_level_params(&ty_expr, &mut used_level_params);
        let surviving_universe_params: Vec<Name> = self
            .universe_params
            .iter()
            .map(|s| s.name().clone())
            .filter(|name| used_level_params.contains(name))
            .collect();

        Ok((decl_name, surviving_universe_params, ty_expr))
    }

    /// Elaborate an `opaque` declaration.
    ///
    /// Opaque declarations may have an optional body:
    /// - `opaque name : ty := val` -- body-bearing: elaborate both type and value
    /// - `opaque name : ty` -- body-less: elaborate type only (sort-only lane)
    ///
    /// Fixes #2552: previously collapsed all opaque to ElabResult::Axiom.
    pub(super) fn elab_opaque_inner(
        &mut self,
        name: &SurfaceName,
        universe_params: &[SurfaceName],
        binders: &[SurfaceBinder],
        ty: &SurfaceExpr,
        val: Option<&SurfaceExpr>,
        attrs: &[Attribute],
        modifiers: &DeclModifiers,
    ) -> Result<ElabResult, ElabError> {
        if let Some(value) = val {
            let attr_name = self.kernel_decl_name(name, modifiers, PrivateNameKind::Definition);
            self.collect_syntactic_defeq(&attr_name, value);
        }

        self.set_decl_universe_params(universe_params);

        let decl_name = self.kernel_decl_name(name, modifiers, PrivateNameKind::Definition);
        // `implemented_by` names its target as written; a private opaque's
        // own name is its user-facing one, not the kernel's (G21).
        let user_name = self.qualify_name(name).into_name();
        if attrs.iter().any(|attr| {
            matches!(attr, Attribute::ImplementedBy(impl_name) if impl_name == name
                || impl_name.name() == &decl_name
                || impl_name.name() == &user_name)
        }) {
            return Err(ElabError::Unsupported {
                feature: format!(
                    "invalid implemented_by argument {name}: definition cannot be implemented by itself"
                ),
            });
        }
        self.ensure_known_attributes(attrs)?;
        self.collect_attributes(&decl_name, attrs);

        if let Some(val_expr) = val {
            // Body-bearing opaque: elaborate like a definition
            let (ty_expr, val_expr, section_fvars) =
                self.elab_decl_body(binders, Some(ty), val_expr)?;

            let ty_expr = self.metas.instantiate(&ty_expr);
            let val_expr = self.metas.instantiate(&val_expr);

            let ty_expr = self.metas.instantiate_levels(&ty_expr);
            let val_expr = self.metas.instantiate_levels(&val_expr);

            let auto_implicits = self.take_auto_implicits();
            let (ty_expr, val_expr, _) = self.wrap_decl_auto_implicits(
                Self::section_binder_count(binders),
                ty_expr,
                val_expr,
                &auto_implicits,
                Some(&section_fvars),
            )?;

            // Filter to surviving params only (#3396, same as Definition).
            let (surviving_universe_params, ty_expr, val_expr) =
                self.finalize_level_params(ty_expr, val_expr)?;

            Ok(ElabResult::Opaque {
                name: decl_name,
                universe_params: surviving_universe_params,
                ty: ty_expr,
                val: Some(val_expr),
                modifiers: *modifiers,
            })
        } else {
            // Body-less opaque: type-only elaboration (like axiom)
            let (ty_expr, section_fvars) = self.elab_decl_type(binders, ty)?;

            let ty_expr = self.metas.instantiate(&ty_expr);
            let ty_expr = self.metas.instantiate_levels(&ty_expr);

            let auto_implicits = self.take_auto_implicits();
            let header_binders = auto_implicits.len() + binders.len();
            let (ty_expr, _) = self.wrap_decl_type_auto_implicits(
                Self::section_binder_count(binders),
                ty_expr,
                &auto_implicits,
                Some(&section_fvars),
            )?;

            // SOUNDNESS: the kernel registers a body-less opaque as an axiom, so
            // its type must be inhabited, as Lean's `opaque` requires
            // (`mkInhabitantFor`): `opaque o : False` would otherwise be a proof
            // of `False` (review r6, X9; docs/DECISIONS.md R134). An `unsafe`
            // opaque is Lean's `sorry` when nothing inhabits it; at the front
            // door, which refuses every safe use of an unsafe constant (R135),
            // so is Clean's. `clean check` admits such uses, so it still asks.
            let unsafe_at_front_door =
                modifiers.is_unsafe && crate::lean_compile_checks::front_door_active();
            if !unsafe_at_front_door {
                match self.require_opaque_inhabitant(
                    &format!("opaque {name}"),
                    &ty_expr,
                    header_binders,
                    true,
                )? {
                    OpaqueInhabitant::Inhabited => {}
                    // Lean's inhabitant is then `Classical.ofNonempty`, which has
                    // no code: a computable `opaque` is "failed to compile
                    // definition" unless nothing compiles its value (an
                    // `@[extern]` or `@[implemented_by]` opaque, a proposition)
                    // or a `noncomputable section` marks it instead.
                    OpaqueInhabitant::Nonempty => {
                        let compiled_elsewhere = attrs.iter().any(|attr| {
                            matches!(attr, Attribute::ImplementedBy(_) | Attribute::Extern(_))
                        });
                        let erased =
                            crate::lean_compile_checks::declaration_is_erased(self.env, &ty_expr);
                        if !modifiers.is_noncomputable && !compiled_elsewhere && !erased {
                            if crate::lean_compile_checks::in_noncomputable_section() {
                                crate::lean_compile_checks::defer_noncomputable_mark(
                                    decl_name.clone(),
                                );
                            } else {
                                return Err(ElabError::CommandFailed {
                                    message: crate::lean_compile_checks::noncomputable_message(
                                        self.env,
                                        &Name::from_string("Classical.ofNonempty"),
                                    ),
                                });
                            }
                        }
                    }
                }
            }

            // Filter to surviving params only (#3396, same as Definition).
            let (surviving_universe_params, ty_expr) = self.finalize_level_params_ty(ty_expr)?;

            Ok(ElabResult::Opaque {
                name: decl_name,
                universe_params: surviving_universe_params,
                ty: ty_expr,
                val: None,
                modifiers: *modifiers,
            })
        }
    }

    /// Elaborate a `partial def name : T := body` as a sound opaque constant.
    ///
    /// The body is deliberately DISCARDED: Lean compiles a partial def to an
    /// opaque declaration plus an unsafe implementation, so kernel-wise it is a
    /// non-reducing constant of type `T`. Registering `name : T` opaquely lets
    /// the body's self-reference resolve (its only purpose here) while the
    /// non-terminating body is never kernel-checked — matching Lean.
    ///
    /// SOUNDNESS: an opaque `name : T` is an axiom `name : T` to the kernel, so
    /// `T` must be inhabited or the declaration is a false witness (`partial def
    /// f : False := f`). We require `Inhabited T` — Lean's own requirement — and
    /// FAIL LOUD if it cannot be synthesized. No `add_decl_unchecked` / bypass is
    /// used: the opaque type itself is kernel-checked.
    pub(super) fn elab_partial_def_opaque(
        &mut self,
        name: &SurfaceName,
        universe_params: &[SurfaceName],
        binders: &[SurfaceBinder],
        ty: &SurfaceExpr,
        attrs: &[Attribute],
        modifiers: &DeclModifiers,
    ) -> Result<ElabResult, ElabError> {
        self.set_decl_universe_params(universe_params);
        let decl_name = self.kernel_decl_name(name, modifiers, PrivateNameKind::Definition);
        self.ensure_known_attributes(attrs)?;
        self.collect_attributes(&decl_name, attrs);

        // The full signature type `T = (binders) → ty` (like an axiom / body-less
        // opaque).
        let (ty_expr, section_fvars) = self.elab_decl_type(binders, ty)?;
        let ty_expr = self.metas.instantiate(&ty_expr);
        let ty_expr = self.metas.instantiate_levels(&ty_expr);

        self.check_declaration_header(&[], Some(&ty_expr))?;

        // SOUNDNESS GUARD: require `Inhabited` of the RESULT type, read under
        // the type's binders opened as locals (Lean's partial fixpoint needs a
        // default of the result type). This is sufficient: if `retTy` is
        // inhabited under the binders then so is `(binders) → retTy`, so the
        // opaque `name : T` is a genuine witness. Shared with `opaque`
        // ([`Self::require_opaque_inhabitant`]), which also accepts `Nonempty`.
        self.require_opaque_inhabitant(
            &format!("partial def {name}"),
            &ty_expr,
            binders.len(),
            false,
        )?;

        let auto_implicits = self.take_auto_implicits();
        let (ty_expr, _) = self.wrap_decl_type_auto_implicits(
            Self::section_binder_count(binders),
            ty_expr,
            &auto_implicits,
            Some(&section_fvars),
        )?;

        let (surviving_universe_params, ty_expr) = self.finalize_level_params_ty(ty_expr)?;

        Ok(ElabResult::Opaque {
            name: decl_name,
            universe_params: surviving_universe_params,
            ty: ty_expr,
            val: None,
            modifiers: *modifiers,
        })
    }
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Make the `match` on the decreasing parameter the value of the whole
//! definition, as Lean's `brecOn` compilation effectively does.
//!
//! Clean lowers structural recursion at the `match` on the decreasing
//! parameter, so an induction hypothesis stands for the value of THAT match.
//! When the match is not the whole body — `1 + match n with …`, `if a = 0
//! then 5 else match b with …`, `match a with | 0 => … | _+1 => match b with
//! …` — the recursion re-ran only the match and dropped the context at every
//! level below the first (`f 2 = 1` for `1 + match n with | 0 => 0 | m+1 => f
//! m`; Lean 4.8.0: 3). Lean's `Structural` wraps the ENTIRE body in
//! `T.brecOn`, so every level re-runs the context.
//!
//! The same effect, in source: a `match` commutes with any context that does
//! not bind its scrutinee or capture its pattern variables,
//!
//! ```text
//! C[match d with | p₁ => e₁ | … | pₖ => eₖ]  =  match d with | p₁ => C[e₁] | … | pₖ => C[eₖ]
//! ```
//!
//! (both sides reduce to `C[eᵢ]` for the `pᵢ` that `d` matches). After the
//! rewrite the match IS the whole body, the recursor computes the whole
//! definition, and each induction hypothesis stands for the definition at
//! the smaller argument. The rewrite changes no value; it only moves where the
//! case split sits, and the kernel re-checks the lowered term.
//!
//! Engaged only for a recursive definition, on the OUTERMOST match on its
//! parameters below the root that contains every recursive call and has a
//! column that can carry the recursion (`descent::classify_descent`), when
//! only the forms `collect` walks lie between the root and that match (a `do`
//! block, a tactic block or any other form leaves the body alone). A body
//! that already IS a match on the parameters keeps today's lowering unless
//! every column of that match certainly cannot carry the recursion. Whatever
//! this declines is judged by the recursion-site check
//! (`infer::recursion_site`) as before.

use clean_kernel::name::Name;
use clean_kernel::Environment;
use clean_parser::{SurfaceBinder, SurfaceExpr, SurfaceMatchArm, SurfaceName, SurfacePattern};

use super::descent::{classify_descent, Descent, DescentRow};
use super::detect::recursive_calls_in;
use crate::stack_safe;

/// One step from a node to a child on the path to the match.
#[derive(Debug, Clone, Copy)]
enum Step {
    AppFn,
    AppArg(usize),
    Inner,
    AscribedExpr,
    LetVal,
    LetBody,
    IfCond,
    IfThen,
    IfElse,
    IfDecThen,
    IfDecElse,
    MatchScrut,
    MatchArm(usize),
    LamBody,
}

struct Candidate {
    path: Vec<Step>,
    /// Names bound by the binders on the path (the context's binders).
    bound: Vec<SurfaceName>,
}

fn pattern_names(pattern: &SurfacePattern, out: &mut Vec<SurfaceName>) {
    match pattern {
        SurfacePattern::Var(name) => out.push(name.clone()),
        SurfacePattern::As(name, inner) => {
            out.push(name.clone());
            pattern_names(inner, out);
        }
        SurfacePattern::Ctor(_, subs) => subs.iter().for_each(|sub| pattern_names(sub, out)),
        SurfacePattern::NumeralAdd(inner, _) => pattern_names(inner, out),
        SurfacePattern::Or(a, b) => {
            pattern_names(a, out);
            pattern_names(b, out);
        }
        SurfacePattern::StructInst { fields, .. } => {
            fields.iter().for_each(|(_, sub)| pattern_names(sub, out));
        }
        SurfacePattern::Wildcard
        | SurfacePattern::Ellipsis
        | SurfacePattern::Lit(_)
        | SurfacePattern::Inaccessible(_)
        | SurfacePattern::QPattern(_) => {}
    }
}

/// The parameter identifiers a match scrutinizes: one bare identifier, or the
/// parser's right-nested `Prod.mk` tuple of them (`match x, y with`).
fn scrutinee_params(scrut: &SurfaceExpr) -> Option<Vec<SurfaceName>> {
    let mut out = Vec::new();
    let mut current = scrut;
    loop {
        match current {
            SurfaceExpr::App(_, f, args)
                if matches!(&**f, SurfaceExpr::Ident(_, n) if n == &SurfaceName::generated_path("Prod.mk"))
                    && args.len() == 2
                    && args.iter().all(|a| a.name.is_none()) =>
            {
                let SurfaceExpr::Ident(_, name) = &args[0].expr else {
                    return None;
                };
                out.push(name.clone());
                current = &args[1].expr;
            }
            SurfaceExpr::Ident(_, name) => {
                out.push(name.clone());
                return Some(out);
            }
            _ => return None,
        }
    }
}

/// The per-column leaves of a (possibly tuple) arm pattern.
fn flatten_tuple(pattern: &SurfacePattern, columns: usize) -> Option<Vec<SurfacePattern>> {
    let mut out = Vec::new();
    let mut current = pattern;
    while out.len() + 1 < columns {
        match current {
            SurfacePattern::Ctor(name, subs)
                if name == &SurfaceName::generated_path("Prod.mk") && subs.len() == 2 =>
            {
                out.push(subs[0].clone());
                current = &subs[1];
            }
            _ => return None,
        }
    }
    out.push(current.clone());
    Some(out)
}

/// Collect, in pre-order, every `match` on parameters reachable from the root
/// through the forms this rewrite commutes with.
fn collect(
    e: &SurfaceExpr,
    params: &[SurfaceName],
    path: &mut Vec<Step>,
    bound: &mut Vec<SurfaceName>,
    out: &mut Vec<Candidate>,
) {
    stack_safe(|| {
        let visit = |child: &SurfaceExpr,
                     step: Step,
                     names: Vec<SurfaceName>,
                     path: &mut Vec<Step>,
                     bound: &mut Vec<SurfaceName>,
                     out: &mut Vec<Candidate>| {
            path.push(step);
            let depth = bound.len();
            bound.extend(names);
            collect(child, params, path, bound, out);
            bound.truncate(depth);
            path.pop();
        };
        match e {
            SurfaceExpr::Match(_, hyp, scrut, arms) => {
                if hyp.is_none()
                    && scrutinee_params(scrut).is_some_and(|names| {
                        names
                            .iter()
                            .all(|n| params.contains(n) && !bound.contains(n))
                    })
                {
                    out.push(Candidate {
                        path: path.clone(),
                        bound: bound.clone(),
                    });
                }
                visit(scrut, Step::MatchScrut, Vec::new(), path, bound, out);
                for (i, arm) in arms.iter().enumerate() {
                    let mut names: Vec<SurfaceName> = hyp.iter().cloned().collect();
                    pattern_names(&arm.pattern, &mut names);
                    visit(&arm.body, Step::MatchArm(i), names, path, bound, out);
                }
            }
            SurfaceExpr::App(_, f, args) => {
                visit(f, Step::AppFn, Vec::new(), path, bound, out);
                for (i, arg) in args.iter().enumerate() {
                    visit(&arg.expr, Step::AppArg(i), Vec::new(), path, bound, out);
                }
            }
            SurfaceExpr::Paren(_, inner) => visit(inner, Step::Inner, Vec::new(), path, bound, out),
            SurfaceExpr::Ascription(_, inner, _) => {
                visit(inner, Step::AscribedExpr, Vec::new(), path, bound, out)
            }
            SurfaceExpr::Let(_, binder, val, body) | SurfaceExpr::Have(_, binder, val, body) => {
                visit(val, Step::LetVal, Vec::new(), path, bound, out);
                visit(
                    body,
                    Step::LetBody,
                    vec![binder.name.clone()],
                    path,
                    bound,
                    out,
                );
            }
            SurfaceExpr::If(_, c, t, f) => {
                visit(c, Step::IfCond, Vec::new(), path, bound, out);
                visit(t, Step::IfThen, Vec::new(), path, bound, out);
                visit(f, Step::IfElse, Vec::new(), path, bound, out);
            }
            SurfaceExpr::IfDecidable(_, witness, _, t, f) => {
                visit(t, Step::IfDecThen, vec![witness.clone()], path, bound, out);
                visit(f, Step::IfDecElse, vec![witness.clone()], path, bound, out);
            }
            SurfaceExpr::Lambda(_, binders, body) => {
                let names = binders.iter().map(|b| b.name.clone()).collect();
                visit(body, Step::LamBody, names, path, bound, out);
            }
            _ => {}
        }
    })
}

fn child(e: &SurfaceExpr, step: Step) -> Option<&SurfaceExpr> {
    Some(match (e, step) {
        (SurfaceExpr::App(_, f, _), Step::AppFn) => f,
        (SurfaceExpr::App(_, _, args), Step::AppArg(i)) => &args.get(i)?.expr,
        (SurfaceExpr::Paren(_, inner), Step::Inner) => inner,
        (SurfaceExpr::Ascription(_, inner, _), Step::AscribedExpr) => inner,
        (SurfaceExpr::Let(_, _, val, _) | SurfaceExpr::Have(_, _, val, _), Step::LetVal) => val,
        (SurfaceExpr::Let(_, _, _, body) | SurfaceExpr::Have(_, _, _, body), Step::LetBody) => body,
        (SurfaceExpr::If(_, c, _, _), Step::IfCond) => c,
        (SurfaceExpr::If(_, _, t, _), Step::IfThen) => t,
        (SurfaceExpr::If(_, _, _, f), Step::IfElse) => f,
        (SurfaceExpr::IfDecidable(_, _, _, t, _), Step::IfDecThen) => t,
        (SurfaceExpr::IfDecidable(_, _, _, _, f), Step::IfDecElse) => f,
        (SurfaceExpr::Match(_, _, scrut, _), Step::MatchScrut) => scrut,
        (SurfaceExpr::Match(_, _, _, arms), Step::MatchArm(i)) => &arms.get(i)?.body,
        (SurfaceExpr::Lambda(_, _, body), Step::LamBody) => body,
        _ => return None,
    })
}

fn at<'e>(e: &'e SurfaceExpr, path: &[Step]) -> Option<&'e SurfaceExpr> {
    path.iter().try_fold(e, |node, step| child(node, *step))
}

/// `e` with the node at `path` replaced by `replacement`.
fn replace_at(e: &SurfaceExpr, path: &[Step], replacement: &SurfaceExpr) -> SurfaceExpr {
    let Some((step, rest)) = path.split_first() else {
        return replacement.clone();
    };
    let sub = |inner: &SurfaceExpr| Box::new(replace_at(inner, rest, replacement));
    match (e, *step) {
        (SurfaceExpr::App(s, f, args), Step::AppFn) => SurfaceExpr::App(*s, sub(f), args.clone()),
        (SurfaceExpr::App(s, f, args), Step::AppArg(i)) => {
            let mut args = args.clone();
            args[i].expr = replace_at(&args[i].expr, rest, replacement);
            SurfaceExpr::App(*s, f.clone(), args)
        }
        (SurfaceExpr::Paren(s, inner), Step::Inner) => SurfaceExpr::Paren(*s, sub(inner)),
        (SurfaceExpr::Ascription(s, inner, ty), Step::AscribedExpr) => {
            SurfaceExpr::Ascription(*s, sub(inner), ty.clone())
        }
        (SurfaceExpr::Let(s, b, val, body), Step::LetVal) => {
            SurfaceExpr::Let(*s, b.clone(), sub(val), body.clone())
        }
        (SurfaceExpr::Have(s, b, val, body), Step::LetVal) => {
            SurfaceExpr::Have(*s, b.clone(), sub(val), body.clone())
        }
        (SurfaceExpr::Let(s, b, val, body), Step::LetBody) => {
            SurfaceExpr::Let(*s, b.clone(), val.clone(), sub(body))
        }
        (SurfaceExpr::Have(s, b, val, body), Step::LetBody) => {
            SurfaceExpr::Have(*s, b.clone(), val.clone(), sub(body))
        }
        (SurfaceExpr::If(s, c, t, f), Step::IfCond) => {
            SurfaceExpr::If(*s, sub(c), t.clone(), f.clone())
        }
        (SurfaceExpr::If(s, c, t, f), Step::IfThen) => {
            SurfaceExpr::If(*s, c.clone(), sub(t), f.clone())
        }
        (SurfaceExpr::If(s, c, t, f), Step::IfElse) => {
            SurfaceExpr::If(*s, c.clone(), t.clone(), sub(f))
        }
        (SurfaceExpr::IfDecidable(s, w, p, t, f), Step::IfDecThen) => {
            SurfaceExpr::IfDecidable(*s, w.clone(), p.clone(), sub(t), f.clone())
        }
        (SurfaceExpr::IfDecidable(s, w, p, t, f), Step::IfDecElse) => {
            SurfaceExpr::IfDecidable(*s, w.clone(), p.clone(), t.clone(), sub(f))
        }
        (SurfaceExpr::Match(s, h, scrut, arms), Step::MatchScrut) => {
            SurfaceExpr::Match(*s, h.clone(), sub(scrut), arms.clone())
        }
        (SurfaceExpr::Match(s, h, scrut, arms), Step::MatchArm(i)) => {
            let mut arms = arms.clone();
            arms[i].body = replace_at(&arms[i].body, rest, replacement);
            SurfaceExpr::Match(*s, h.clone(), scrut.clone(), arms)
        }
        (SurfaceExpr::Lambda(s, binders, body), Step::LamBody) => {
            SurfaceExpr::Lambda(*s, binders.clone(), sub(body))
        }
        // `collect` only records paths through the forms above.
        (other, _) => other.clone(),
    }
}

/// Could `name` occur FREE in `e` — outside every binder of `e` that binds
/// it? Conservative: a form this does not look inside answers `true`, and so
/// does a pattern it cannot read.
fn may_mention_free(e: &SurfaceExpr, name: &SurfaceName) -> bool {
    let binds = |p: &SurfacePattern| {
        let mut names = Vec::new();
        pattern_names(p, &mut names);
        names.contains(name)
    };
    stack_safe(|| match e {
        // A dotted identifier `y.f` may be field notation on a local `y`.
        SurfaceExpr::Ident(_, n) | SurfaceExpr::NamedHole(_, n) => {
            n == name || n.split_first().is_some_and(|(first, _)| &first == name)
        }
        SurfaceExpr::Lit(..) | SurfaceExpr::Hole(..) | SurfaceExpr::Universe(..) => false,
        SurfaceExpr::App(_, f, args) => {
            may_mention_free(f, name) || args.iter().any(|a| may_mention_free(&a.expr, name))
        }
        SurfaceExpr::Lambda(_, binders, body)
        | SurfaceExpr::PatternMatchLambda(_, binders, body)
        | SurfaceExpr::Pi(_, binders, body) => {
            for binder in binders {
                if binder
                    .ty
                    .as_ref()
                    .is_some_and(|t| may_mention_free(t, name))
                {
                    return true;
                }
                if &binder.name == name {
                    return false;
                }
            }
            may_mention_free(body, name)
        }
        SurfaceExpr::Arrow(_, a, b) | SurfaceExpr::Ascription(_, a, b) => {
            may_mention_free(a, name) || may_mention_free(b, name)
        }
        SurfaceExpr::Let(_, binder, val, body) | SurfaceExpr::Have(_, binder, val, body) => {
            binder
                .ty
                .as_ref()
                .is_some_and(|t| may_mention_free(t, name))
                || may_mention_free(val, name)
                || (&binder.name != name && may_mention_free(body, name))
        }
        SurfaceExpr::LetRec(_, binder, val, body) => {
            &binder.name != name
                && (binder
                    .ty
                    .as_ref()
                    .is_some_and(|t| may_mention_free(t, name))
                    || may_mention_free(val, name)
                    || may_mention_free(body, name))
        }
        SurfaceExpr::LetPattern(_, pat, scrut, fallback, body)
        | SurfaceExpr::IfLet(_, pat, scrut, body, fallback) => {
            pattern_has_opaque(pat)
                || may_mention_free(scrut, name)
                || may_mention_free(fallback, name)
                || (!binds(pat) && may_mention_free(body, name))
        }
        SurfaceExpr::IfDecidable(_, w, p, t, f) => {
            may_mention_free(p, name)
                || (w != name && (may_mention_free(t, name) || may_mention_free(f, name)))
        }
        SurfaceExpr::If(_, c, t, f) => {
            may_mention_free(c, name) || may_mention_free(t, name) || may_mention_free(f, name)
        }
        SurfaceExpr::Match(_, hyp, scrut, arms) => {
            may_mention_free(scrut, name)
                || arms.iter().any(|arm| {
                    pattern_has_opaque(&arm.pattern)
                        || (hyp.as_ref() != Some(name)
                            && !binds(&arm.pattern)
                            && may_mention_free(&arm.body, name))
                })
        }
        SurfaceExpr::Paren(_, i)
        | SurfaceExpr::Proj(_, i, _)
        | SurfaceExpr::Explicit(_, i)
        | SurfaceExpr::NamedArg(_, _, i)
        | SurfaceExpr::Borrowed(_, i)
        | SurfaceExpr::OutParam(_, i)
        | SurfaceExpr::SemiOutParam(_, i)
        | SurfaceExpr::UniverseInst(_, i, _)
        | SurfaceExpr::LiftMethod(_, i) => may_mention_free(i, name),
        _ => true,
    })
}

fn pattern_has_opaque(p: &SurfacePattern) -> bool {
    match p {
        SurfacePattern::Inaccessible(_) | SurfacePattern::QPattern(_) => true,
        SurfacePattern::Ctor(_, subs) => subs.iter().any(pattern_has_opaque),
        SurfacePattern::As(_, inner) | SurfacePattern::NumeralAdd(inner, _) => {
            pattern_has_opaque(inner)
        }
        SurfacePattern::Or(a, b) => pattern_has_opaque(a) || pattern_has_opaque(b),
        _ => false,
    }
}

/// Rewrite a recursive definition's body so that the `match` on its
/// decreasing parameter is the whole body (see the module documentation).
/// `None` leaves the body as it is.
pub(crate) fn hoist_recursive_match(
    env: &Environment,
    func_name: &SurfaceName,
    binders: &[SurfaceBinder],
    body: &SurfaceExpr,
) -> Option<SurfaceExpr> {
    if func_name.is_anonymous() {
        return None;
    }
    let total_calls = recursive_calls_in(func_name, body).len();
    if total_calls == 0 {
        return None;
    }
    let params: Vec<SurfaceName> = binders.iter().map(|b| b.name.clone()).collect();
    let explicit: Vec<SurfaceName> = binders
        .iter()
        .filter(|b| matches!(b.info, clean_parser::SurfaceBinderInfo::Explicit))
        .map(|b| b.name.clone())
        .collect();
    let mut candidates = Vec::new();
    collect(
        body,
        &params,
        &mut Vec::new(),
        &mut Vec::new(),
        &mut candidates,
    );
    // How each column of a candidate match would carry the recursion; `None`
    // when its patterns cannot be read per column.
    let verdicts = |site: &SurfaceExpr| -> Option<Vec<Descent>> {
        let SurfaceExpr::Match(_, _, scrut, arms) = site else {
            return None;
        };
        let columns = scrutinee_params(scrut)?;
        let leaves = arms
            .iter()
            .map(|arm| flatten_tuple(&arm.pattern, columns.len()))
            .collect::<Option<Vec<_>>>()?;
        let rows: Vec<DescentRow<'_>> = leaves
            .iter()
            .zip(arms.iter())
            .map(|(pats, arm)| DescentRow {
                pats,
                body: &arm.body,
            })
            .collect();
        Some(
            columns
                .iter()
                .enumerate()
                .map(|(column, param)| {
                    let Some(call_pos) = explicit.iter().position(|p| p == param) else {
                        return Descent::Unknown;
                    };
                    let inductive: Option<Name> = binders
                        .iter()
                        .find(|b| &b.name == param)
                        .and_then(|b| b.ty.as_deref())
                        .and_then(type_head)
                        .and_then(|head| env.get_inductive(head.name()))
                        .map(|ind| ind.name.clone());
                    classify_descent(env, func_name, &rows, column, inductive.as_ref(), call_pos)
                })
                .collect(),
        )
    };
    // A whole-body match on the parameters keeps today's lowering unless no
    // column of it can carry the recursion.
    if candidates.first().is_some_and(|c| c.path.is_empty()) {
        match verdicts(body) {
            Some(v) if v.iter().all(|d| *d == Descent::Invalid) => {}
            _ => return None,
        }
    }
    // The arms of `site`, with every pattern variable that the context would
    // capture or shadow renamed to a fresh unspellable name (in its pattern
    // and, free, in its body). `None` when some renaming cannot be done.
    let renamed_arms =
        |candidate: &Candidate, site: &SurfaceExpr| -> Option<Vec<SurfaceMatchArm>> {
            let SurfaceExpr::Match(_, _, _, arms) = site else {
                return None;
            };
            let context = replace_at(body, &candidate.path, &SurfaceExpr::Hole(site.span()));
            let mut fresh = 0u64;
            let mut out = Vec::with_capacity(arms.len());
            for arm in arms {
                let mut vars = Vec::new();
                pattern_names(&arm.pattern, &mut vars);
                let mut pattern = arm.pattern.clone();
                let mut arm_body = arm.body.clone();
                for v in vars {
                    if !candidate.bound.contains(&v) && !may_mention_free(&context, &v) {
                        continue;
                    }
                    // A bare pattern identifier may be a constructor, which a
                    // renaming would turn into a binder.
                    if could_name_constructor(env, &v) {
                        return None;
                    }
                    let base = v.name().to_string();
                    let to = SurfaceName::unspellable(&base, fresh);
                    fresh += 1;
                    pattern = rename_pattern_binder(&pattern, &v, &to);
                    arm_body = rename_free(&arm_body, &v, &to)?;
                }
                out.push(SurfaceMatchArm {
                    span: arm.span,
                    pattern,
                    body: arm_body,
                });
            }
            Some(out)
        };
    let (chosen, arms) = candidates.into_iter().find_map(|candidate| {
        if candidate.path.is_empty() {
            return None;
        }
        let site @ SurfaceExpr::Match(_, _, scrut, _) = at(body, &candidate.path)? else {
            return None;
        };
        // Every recursive call must be under this match, and some column of
        // it must carry the recursion.
        if recursive_calls_in(func_name, site).len() != total_calls
            || !verdicts(site).is_some_and(|v| v.contains(&Descent::Valid))
        {
            return None;
        }
        // The context's binders must not shadow the scrutinee.
        let columns = scrutinee_params(scrut)?;
        if columns.iter().any(|c| candidate.bound.contains(c)) {
            return None;
        }
        let arms = renamed_arms(&candidate, site)?;
        Some((candidate, arms))
    })?;
    let Some(SurfaceExpr::Match(span, hyp, scrut, _)) = at(body, &chosen.path) else {
        return None;
    };
    let arms = arms
        .into_iter()
        .map(|arm| SurfaceMatchArm {
            span: arm.span,
            pattern: arm.pattern,
            body: replace_at(body, &chosen.path, &arm.body),
        })
        .collect();
    Some(SurfaceExpr::Match(*span, hyp.clone(), scrut.clone(), arms))
}

/// Could the bare identifier `name` denote a constructor (exactly, or by its
/// last component under some namespace)?
fn could_name_constructor(env: &Environment, name: &SurfaceName) -> bool {
    let last = name.name().last_component();
    env.constructors()
        .any(|c| &c.name == name.name() || (last.is_some() && c.name.last_component() == last))
}

fn rename_pattern_binder(
    pattern: &SurfacePattern,
    from: &SurfaceName,
    to: &SurfaceName,
) -> SurfacePattern {
    let r = |p: &SurfacePattern| rename_pattern_binder(p, from, to);
    match pattern {
        SurfacePattern::Var(name) if name == from => SurfacePattern::Var(to.clone()),
        SurfacePattern::As(name, inner) => SurfacePattern::As(
            if name == from {
                to.clone()
            } else {
                name.clone()
            },
            Box::new(r(inner)),
        ),
        SurfacePattern::Ctor(ctor, subs) => {
            SurfacePattern::Ctor(ctor.clone(), subs.iter().map(r).collect())
        }
        SurfacePattern::NumeralAdd(inner, k) => SurfacePattern::NumeralAdd(Box::new(r(inner)), *k),
        SurfacePattern::Or(a, b) => SurfacePattern::Or(Box::new(r(a)), Box::new(r(b))),
        other => other.clone(),
    }
}

/// Rename every FREE occurrence of `from` in `e` to `to`, which no source can
/// spell (so nothing in `e` can capture it). `None` for a form that may hold a
/// free occurrence this cannot rewrite.
fn rename_free(e: &SurfaceExpr, from: &SurfaceName, to: &SurfaceName) -> Option<SurfaceExpr> {
    if !may_mention_free(e, from) {
        return Some(e.clone());
    }
    let r = |x: &SurfaceExpr| rename_free(x, from, to).map(Box::new);
    let binds = |p: &SurfacePattern| {
        let mut names = Vec::new();
        pattern_names(p, &mut names);
        names.contains(from)
    };
    stack_safe(|| {
        Some(match e {
            SurfaceExpr::Ident(sp, n) if n == from => SurfaceExpr::Ident(*sp, to.clone()),
            // A dotted `from.f` is left to the paths that read it as written:
            // renaming only its head is not something this can show sound.
            SurfaceExpr::Ident(..) => return None,
            SurfaceExpr::App(sp, f, args) => {
                let mut new_args = Vec::with_capacity(args.len());
                for a in args {
                    let mut a2 = a.clone();
                    a2.expr = rename_free(&a.expr, from, to)?;
                    new_args.push(a2);
                }
                SurfaceExpr::App(*sp, r(f)?, new_args)
            }
            SurfaceExpr::Lambda(sp, binders, body) => {
                let mut new_binders = Vec::with_capacity(binders.len());
                let mut shadowed = false;
                for b in binders {
                    let mut b2 = b.clone();
                    if !shadowed {
                        if let Some(t) = &b.ty {
                            b2.ty = Some(r(t)?);
                        }
                    }
                    shadowed |= &b.name == from;
                    new_binders.push(b2);
                }
                let new_body = if shadowed { body.clone() } else { r(body)? };
                SurfaceExpr::Lambda(*sp, new_binders, new_body)
            }
            SurfaceExpr::Ascription(sp, a, b) => SurfaceExpr::Ascription(*sp, r(a)?, r(b)?),
            SurfaceExpr::Let(sp, binder, val, body) => {
                let mut b2 = binder.clone();
                if let Some(t) = &binder.ty {
                    b2.ty = Some(r(t)?);
                }
                let new_body = if &binder.name == from {
                    body.clone()
                } else {
                    r(body)?
                };
                SurfaceExpr::Let(*sp, b2, r(val)?, new_body)
            }
            SurfaceExpr::Have(sp, binder, val, body) => {
                let mut b2 = binder.clone();
                if let Some(t) = &binder.ty {
                    b2.ty = Some(r(t)?);
                }
                let new_body = if &binder.name == from {
                    body.clone()
                } else {
                    r(body)?
                };
                SurfaceExpr::Have(*sp, b2, r(val)?, new_body)
            }
            SurfaceExpr::LetPattern(sp, pat, scrut, fallback, body) => {
                if pattern_has_opaque(pat) {
                    return None;
                }
                let new_body = if binds(pat) { body.clone() } else { r(body)? };
                SurfaceExpr::LetPattern(*sp, pat.clone(), r(scrut)?, r(fallback)?, new_body)
            }
            SurfaceExpr::IfLet(sp, pat, scrut, then_, else_) => {
                if pattern_has_opaque(pat) {
                    return None;
                }
                let new_then = if binds(pat) { then_.clone() } else { r(then_)? };
                SurfaceExpr::IfLet(*sp, pat.clone(), r(scrut)?, new_then, r(else_)?)
            }
            SurfaceExpr::IfDecidable(sp, w, p, t, f) => {
                if w == from {
                    SurfaceExpr::IfDecidable(*sp, w.clone(), r(p)?, t.clone(), f.clone())
                } else {
                    SurfaceExpr::IfDecidable(*sp, w.clone(), r(p)?, r(t)?, r(f)?)
                }
            }
            SurfaceExpr::If(sp, c, t, f) => SurfaceExpr::If(*sp, r(c)?, r(t)?, r(f)?),
            SurfaceExpr::Match(sp, hyp, scrut, arms) => {
                let mut new_arms = Vec::with_capacity(arms.len());
                for arm in arms {
                    if pattern_has_opaque(&arm.pattern) {
                        return None;
                    }
                    let body = if hyp.as_ref() == Some(from) || binds(&arm.pattern) {
                        arm.body.clone()
                    } else {
                        rename_free(&arm.body, from, to)?
                    };
                    new_arms.push(SurfaceMatchArm {
                        span: arm.span,
                        pattern: arm.pattern.clone(),
                        body,
                    });
                }
                SurfaceExpr::Match(*sp, hyp.clone(), r(scrut)?, new_arms)
            }
            SurfaceExpr::Paren(sp, i) => SurfaceExpr::Paren(*sp, r(i)?),
            SurfaceExpr::Proj(sp, i, p) => SurfaceExpr::Proj(*sp, r(i)?, p.clone()),
            SurfaceExpr::Explicit(sp, i) => SurfaceExpr::Explicit(*sp, r(i)?),
            SurfaceExpr::NamedArg(sp, n, i) => SurfaceExpr::NamedArg(*sp, n.clone(), r(i)?),
            _ => return None,
        })
    })
}

fn type_head(ty: &SurfaceExpr) -> Option<&SurfaceName> {
    match ty {
        SurfaceExpr::Ident(_, name) => Some(name),
        SurfaceExpr::App(_, func, _) | SurfaceExpr::Paren(_, func) => type_head(func),
        _ => None,
    }
}

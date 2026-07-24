// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Detection algorithms for structural recursion.

use clean_parser::{Projection, SurfaceExpr};

use crate::stack_safe;

use super::{
    binder_shadows_name, normalize_root_prefix, pattern_binds_name, qualified_name_from_proj,
    RecursionInfo, RecursionNameParts, RecursiveArg, RecursiveCall,
};

/// Detect recursive calls in a surface expression
///
/// # Arguments
/// * `func_name` - Name of the function being defined
/// * `body` - The function body to analyze
///
/// # Returns
/// Information about recursion in the body
pub fn detect_recursion(func_name: &str, body: &SurfaceExpr) -> RecursionInfo {
    detect_recursion_with_params(func_name, body, &[])
}

/// Track AA: whether `body` contains a call to the (possibly dotted) function
/// `call_name`. Reuses the recursive-call detector with `call_name` as the
/// "self" name — a hit means the body applies that function somewhere. Used to
/// decide whether a fused nested-mutual fold's primary def must lower through
/// `T.rec` because it contains a SIBLING call (which becomes an IH).
pub fn body_mentions_call(body: &SurfaceExpr, call_name: &str) -> bool {
    detect_recursion(call_name, body).is_recursive
}

/// Detect recursive calls with parameter names for better heuristics (#403)
///
/// # Arguments
/// * `func_name` - Name of the function being defined
/// * `body` - The function body to analyze
/// * `param_names` - Names of function parameters (for decreasing arg detection)
///
/// # Returns
/// Information about recursion in the body
pub fn detect_recursion_with_params(
    func_name: &str,
    body: &SurfaceExpr,
    param_names: &[String],
) -> RecursionInfo {
    let mut calls = Vec::new();
    let name_parts = RecursionNameParts::new(func_name);
    find_recursive_calls(&name_parts, body, &mut calls, false, false);

    let is_recursive = !calls.is_empty();
    let decreasing_arg = if is_recursive {
        // Preferred position: a whole-body `match <param> with …` names the
        // canonical structural decreasing argument directly. The name-equality
        // heuristic below cannot see it when the decreasing pattern variable
        // SHADOWS the parameter (`def f (a b c) := match a with | 0 => …
        // | a + 1 => 1 + f a b c` — the call's first arg is the REBOUND
        // pattern `a`, one predecessor step smaller, but its NAME equals the
        // parameter, so the heuristic rejected position 0 and a fallback
        // picked a bogus trailing position; `is_match_on_decreasing_arg` then
        // never matched the real scrutinee and the self-call died
        // UnknownIdent). Preferring the scrutinee position is routing only:
        // the `.rec` lowering binds IHs solely for structurally smaller
        // components and the kernel re-checks the result, so a genuinely
        // non-decreasing call still fails loud downstream.
        let preferred = whole_body_match_scrutinee_pos(body, param_names);
        find_decreasing_arg(&calls, param_names, preferred)
    } else {
        None
    };

    RecursionInfo {
        is_recursive,
        calls,
        decreasing_arg,
    }
}

/// Position of the parameter a whole-body `match <param> with …` scrutinizes,
/// peeling any leading lambda wrappers. `None` for tuple/multi scrutinees,
/// non-ident scrutinees, or bodies that are not a top-level match.
fn whole_body_match_scrutinee_pos(body: &SurfaceExpr, param_names: &[String]) -> Option<usize> {
    whole_body_match(body).and_then(|(scrut, _)| {
        if let SurfaceExpr::Ident(_, name) = scrut {
            param_names.iter().position(|p| p == name)
        } else {
            None
        }
    })
}

/// The scrutinee and arms of a whole-body `match`, peeling any leading
/// lambda wrappers. `None` when the body is not a top-level match.
fn whole_body_match(
    body: &SurfaceExpr,
) -> Option<(&SurfaceExpr, &[clean_parser::SurfaceMatchArm])> {
    let mut cur = body;
    while let SurfaceExpr::Lambda(_, _, inner) | SurfaceExpr::PatternMatchLambda(_, _, inner) = cur
    {
        cur = inner;
    }
    if let SurfaceExpr::Match(_, _, scrut, arms) = cur {
        Some((scrut.as_ref(), arms))
    } else {
        None
    }
}

/// B97 (`let rec`/`where` lane): whether `body` is a whole-body
/// `match <param_names[dec_pos]> with …` in which at least one arm's pattern
/// REBINDS the scrutinized parameter's name.
///
/// Under that shape, a self-call argument whose NAME equals the parameter is
/// (in the rebinding arms) the rebound, structurally smaller pattern
/// component — so a name-equality "passes the parameter unchanged" check is
/// unreliable evidence of non-descent and must not reject the lift
/// (`let rec go (k : Nat) := match k with | 0 => 0 | k + 1 => go k`).
/// Routing only: the `.rec` lowering substitutes induction hypotheses solely
/// for genuinely smaller components and the kernel re-checks the result, so
/// a self-call that really passes the outer parameter unchanged still fails
/// loud downstream.
pub fn whole_body_match_rebinds_param(
    body: &SurfaceExpr,
    param_names: &[String],
    dec_pos: usize,
) -> bool {
    if whole_body_match_scrutinee_pos(body, param_names) != Some(dec_pos) {
        return false;
    }
    let Some(param) = param_names.get(dec_pos) else {
        return false;
    };
    whole_body_match(body).is_some_and(|(_, arms)| {
        arms.iter()
            .any(|arm| pattern_binds_name(&arm.pattern, param))
    })
}

/// Find all recursive calls in an expression
fn find_recursive_calls(
    func_name: &RecursionNameParts,
    expr: &SurfaceExpr,
    calls: &mut Vec<RecursiveCall>,
    shadowed_short: bool,
    shadowed_base: bool,
) {
    stack_safe(|| match expr {
        SurfaceExpr::App(_, _, _) => {
            // Collect all arguments from nested applications (#389)
            // For `f a b` represented as `App(App(f, [a]), [b])`, we want to
            // record all args [a, b] for the recursive call.
            let (base_func, all_args) = collect_app_spine(expr);

            // Check if the base function is a recursive call
            if is_recursive_call(func_name, base_func, shadowed_short, shadowed_base) {
                let rec_args: Vec<RecursiveArg> = all_args
                    .iter()
                    .map(|arg| {
                        if let SurfaceExpr::Ident(_, name) = &arg.expr {
                            RecursiveArg::Var(name.clone())
                        } else {
                            RecursiveArg::Other
                        }
                    })
                    .collect();
                calls.push(RecursiveCall { args: rec_args });
            }

            // Recurse into base function and all arguments
            find_recursive_calls(func_name, base_func, calls, shadowed_short, shadowed_base);
            for arg in all_args {
                find_recursive_calls(func_name, &arg.expr, calls, shadowed_short, shadowed_base);
            }
        }

        SurfaceExpr::Lambda(_, binders, body) => {
            let shadowed_body = shadowed_short
                || binders
                    .iter()
                    .any(|b| binder_shadows_name(b, func_name.short()));
            let shadowed_base_body = shadowed_base
                || func_name
                    .base()
                    .is_some_and(|base| binders.iter().any(|b| binder_shadows_name(b, base)));
            find_recursive_calls(func_name, body, calls, shadowed_body, shadowed_base_body);
        }

        SurfaceExpr::PatternMatchLambda(_, binders, body) => {
            let shadowed_body = shadowed_short
                || binders
                    .iter()
                    .any(|b| binder_shadows_name(b, func_name.short()));
            let shadowed_base_body = shadowed_base
                || func_name
                    .base()
                    .is_some_and(|base| binders.iter().any(|b| binder_shadows_name(b, base)));
            find_recursive_calls(func_name, body, calls, shadowed_body, shadowed_base_body);
        }

        SurfaceExpr::Pi(_, binders, body) => {
            let shadowed_body = shadowed_short
                || binders
                    .iter()
                    .any(|b| binder_shadows_name(b, func_name.short()));
            let shadowed_base_body = shadowed_base
                || func_name
                    .base()
                    .is_some_and(|base| binders.iter().any(|b| binder_shadows_name(b, base)));
            find_recursive_calls(func_name, body, calls, shadowed_body, shadowed_base_body);
        }

        SurfaceExpr::Arrow(_, from, to) => {
            find_recursive_calls(func_name, from, calls, shadowed_short, shadowed_base);
            find_recursive_calls(func_name, to, calls, shadowed_short, shadowed_base);
        }

        SurfaceExpr::Let(_, binder, val, body) => {
            find_recursive_calls(func_name, val, calls, shadowed_short, shadowed_base);
            let shadowed_body = shadowed_short || binder_shadows_name(binder, func_name.short());
            let shadowed_base_body = shadowed_base
                || func_name
                    .base()
                    .is_some_and(|base| binder_shadows_name(binder, base));
            find_recursive_calls(func_name, body, calls, shadowed_body, shadowed_base_body);
        }

        SurfaceExpr::LetRec(_, binder, val, body) => {
            let shadowed_body = shadowed_short || binder_shadows_name(binder, func_name.short());
            let shadowed_base_body = shadowed_base
                || func_name
                    .base()
                    .is_some_and(|base| binder_shadows_name(binder, base));
            find_recursive_calls(func_name, val, calls, shadowed_body, shadowed_base_body);
            find_recursive_calls(func_name, body, calls, shadowed_body, shadowed_base_body);
        }

        SurfaceExpr::LetPattern(_, pattern, scrutinee, fallback, body) => {
            find_recursive_calls(func_name, scrutinee, calls, shadowed_short, shadowed_base);
            find_recursive_calls(func_name, fallback, calls, shadowed_short, shadowed_base);
            let shadowed_body = shadowed_short || pattern_binds_name(pattern, func_name.short());
            let shadowed_base_body = shadowed_base
                || func_name
                    .base()
                    .is_some_and(|base| pattern_binds_name(pattern, base));
            find_recursive_calls(func_name, body, calls, shadowed_body, shadowed_base_body);
        }

        SurfaceExpr::If(_, cond, then_, else_) => {
            find_recursive_calls(func_name, cond, calls, shadowed_short, shadowed_base);
            find_recursive_calls(func_name, then_, calls, shadowed_short, shadowed_base);
            find_recursive_calls(func_name, else_, calls, shadowed_short, shadowed_base);
        }

        SurfaceExpr::IfLet(_, pattern, scrutinee, then_, else_) => {
            find_recursive_calls(func_name, scrutinee, calls, shadowed_short, shadowed_base);
            let shadowed_then = shadowed_short || pattern_binds_name(pattern, func_name.short());
            let shadowed_base_then = shadowed_base
                || func_name
                    .base()
                    .is_some_and(|base| pattern_binds_name(pattern, base));
            find_recursive_calls(func_name, then_, calls, shadowed_then, shadowed_base_then);
            find_recursive_calls(func_name, else_, calls, shadowed_short, shadowed_base);
        }

        SurfaceExpr::IfDecidable(_, witness, prop, then_, else_) => {
            find_recursive_calls(func_name, prop, calls, shadowed_short, shadowed_base);
            let shadowed_branches = shadowed_short || witness == func_name.short();
            let shadowed_base_branches =
                shadowed_base || func_name.base().is_some_and(|base| witness == base);
            find_recursive_calls(
                func_name,
                then_,
                calls,
                shadowed_branches,
                shadowed_base_branches,
            );
            find_recursive_calls(
                func_name,
                else_,
                calls,
                shadowed_branches,
                shadowed_base_branches,
            );
        }

        SurfaceExpr::Match(_, _, scrutinee, arms) => {
            find_recursive_calls(func_name, scrutinee, calls, shadowed_short, shadowed_base);
            for arm in arms {
                let shadowed_arm =
                    shadowed_short || pattern_binds_name(&arm.pattern, func_name.short());
                let shadowed_base_arm = shadowed_base
                    || func_name
                        .base()
                        .is_some_and(|base| pattern_binds_name(&arm.pattern, base));
                find_recursive_calls(func_name, &arm.body, calls, shadowed_arm, shadowed_base_arm);
            }
        }

        SurfaceExpr::Paren(_, inner) => {
            find_recursive_calls(func_name, inner, calls, shadowed_short, shadowed_base);
        }

        SurfaceExpr::Ascription(_, expr, ty) => {
            find_recursive_calls(func_name, expr, calls, shadowed_short, shadowed_base);
            find_recursive_calls(func_name, ty, calls, shadowed_short, shadowed_base);
        }

        SurfaceExpr::Proj(_, base, Projection::Named(field)) => {
            // A bare method dot-notation self-call `elemTy.bitWidth` (no enclosing
            // `App`) resolves to `Ty.bitWidth elemTy`. Record it as a recursive
            // call with the receiver `elemTy` as the sole argument so the
            // decreasing-argument search and IH substitution can see it.
            //
            // Only the *method-dot* shape is recorded here: the receiver is a
            // plain variable and the field equals the function's short name. The
            // namespace-qualified path form (`foo.bar` / `TrustIr.Ty.bitWidth`)
            // is a constant reference whose applied form is already recorded by
            // the `App` arm, so excluding it avoids double-counting the call.
            let is_method_dot = !shadowed_base
                && !shadowed_short
                && field == func_name.short()
                && matches!(base.as_ref(), SurfaceExpr::Ident(_, _))
                && qualified_name_from_proj(expr)
                    .is_none_or(|name| !matches_full(normalize_root_prefix(&name), func_name));
            if is_method_dot {
                if let SurfaceExpr::Ident(_, recv_name) = base.as_ref() {
                    calls.push(RecursiveCall {
                        args: vec![RecursiveArg::Var(recv_name.clone())],
                    });
                }
            }
            find_recursive_calls(func_name, base, calls, shadowed_short, shadowed_base);
        }
        SurfaceExpr::Proj(_, base, _) => {
            find_recursive_calls(func_name, base, calls, shadowed_short, shadowed_base);
        }

        SurfaceExpr::UniverseInst(_, expr, _) => {
            find_recursive_calls(func_name, expr, calls, shadowed_short, shadowed_base);
        }

        SurfaceExpr::NamedArg(_, _, expr) => {
            find_recursive_calls(func_name, expr, calls, shadowed_short, shadowed_base);
        }

        SurfaceExpr::OutParam(_, inner) | SurfaceExpr::SemiOutParam(_, inner) => {
            find_recursive_calls(func_name, inner, calls, shadowed_short, shadowed_base);
        }

        SurfaceExpr::QQuotation {
            inner, type_annot, ..
        } => {
            find_recursive_calls(func_name, inner, calls, shadowed_short, shadowed_base);
            if let Some(ty) = type_annot {
                find_recursive_calls(func_name, ty, calls, shadowed_short, shadowed_base);
            }
        }

        SurfaceExpr::QAntiquot { content, .. } => {
            if let clean_parser::QAntiquotContent::Expr(e) = content {
                find_recursive_calls(func_name, e, calls, shadowed_short, shadowed_base);
            }
        }

        SurfaceExpr::Explicit(_, inner) => {
            find_recursive_calls(func_name, inner, calls, shadowed_short, shadowed_base);
        }

        SurfaceExpr::StructLit { fields, base, .. } => {
            if let Some(b) = base {
                find_recursive_calls(func_name, b, calls, shadowed_short, shadowed_base);
            }
            for field in fields {
                find_recursive_calls(func_name, &field.val, calls, shadowed_short, shadowed_base);
            }
        }

        // Terminal expressions - no recursion to find
        SurfaceExpr::Ident(_, _)
        | SurfaceExpr::SyntheticSorry(_)
        | SurfaceExpr::Universe(_, _)
        | SurfaceExpr::Lit(_, _)
        | SurfaceExpr::Hole(_)
        | SurfaceExpr::NamedHole(_, _)
        | SurfaceExpr::SyntaxQuote(_, _) => {}

        // Tactic/calc blocks - opaque to recursive call detection
        SurfaceExpr::ByTactic(_, _) | SurfaceExpr::CalcBlock(_, _) => {}

        // Do blocks: walk into each element's sub-expressions so a self-call in a
        // `let x ← f …` bind or a sequenced action is detected (e.g.
        // `semVectorIntBinOp`'s `let rest ← semVectorIntBinOp … lhsRest rhsRest`).
        // Detection is conservative: it only records calls so structural recursion
        // is *set up*; the kernel re-checks the resulting `.rec` application, so a
        // spurious detection cannot make an unsound declaration pass. We do not
        // track shadowing introduced by do-binders here — a do-binder that
        // shadowed the function name is exceedingly unusual and would at worst
        // record a false self-call that the kernel check then rejects.
        SurfaceExpr::Do(_, elems) => {
            for elem in elems {
                find_recursive_calls_in_do_elem(
                    func_name,
                    elem,
                    calls,
                    shadowed_short,
                    shadowed_base,
                );
            }
        }

        // Nested action lift: recurse into inner expression
        SurfaceExpr::LiftMethod(_, inner) => {
            find_recursive_calls(func_name, inner, calls, shadowed_short, shadowed_base);
        }

        // Interpolated strings: recurse into expression parts
        SurfaceExpr::InterpolatedStr { parts, .. } => {
            for part in parts {
                if let clean_parser::InterpolationPart::Expr(inner) = part {
                    find_recursive_calls(func_name, inner, calls, shadowed_short, shadowed_base);
                }
            }
        }

        // `open X in <term>`: recurse into the sub-term to detect self-calls.
        SurfaceExpr::OpenIn { body, .. } => {
            find_recursive_calls(func_name, body, calls, shadowed_short, shadowed_base);
        }
    })
}

/// Walk a single `do`-block element, recursing into every contained
/// `SurfaceExpr` (and nested do-sequences) so recursive self-calls inside
/// do-notation are detected. Detection-only — see the `Do` arm of
/// `find_recursive_calls` for the soundness argument.
fn find_recursive_calls_in_do_elem(
    func_name: &RecursionNameParts,
    elem: &clean_parser::DoElem,
    calls: &mut Vec<RecursiveCall>,
    shadowed_short: bool,
    shadowed_base: bool,
) {
    use clean_parser::DoElem;
    let mut walk = |e: &SurfaceExpr, calls: &mut Vec<RecursiveCall>| {
        find_recursive_calls(func_name, e, calls, shadowed_short, shadowed_base);
    };
    let mut walk_seq = |seq: &[DoElem], calls: &mut Vec<RecursiveCall>| {
        for e in seq {
            find_recursive_calls_in_do_elem(func_name, e, calls, shadowed_short, shadowed_base);
        }
    };
    match elem {
        DoElem::Bind(_, _, e)
        | DoElem::Let(_, _, e)
        | DoElem::LetMut(_, _, e)
        | DoElem::Return(_, e)
        | DoElem::Expr(_, e)
        | DoElem::DbgTrace(_, e)
        | DoElem::Reassign(_, _, e)
        | DoElem::PatternReassign(_, _, e) => walk(e, calls),
        DoElem::LetRec(_, defs) => {
            for (_, e) in defs {
                walk(e, calls);
            }
        }
        DoElem::If(_, cond, then_seq, else_seq) => {
            walk(cond, calls);
            walk_seq(then_seq, calls);
            if let Some(seq) = else_seq {
                walk_seq(seq, calls);
            }
        }
        DoElem::IfLet(_, _, scrut, then_seq, else_seq)
        | DoElem::IfDecidable(_, _, scrut, then_seq, else_seq) => {
            walk(scrut, calls);
            walk_seq(then_seq, calls);
            if let Some(seq) = else_seq {
                walk_seq(seq, calls);
            }
        }
        DoElem::For(_, _, e, seq) | DoElem::While(_, e, seq) => {
            walk(e, calls);
            walk_seq(seq, calls);
        }
        DoElem::Match(_, scruts, arms) => {
            for s in scruts {
                walk(s, calls);
            }
            for arm in arms {
                walk_seq(&arm.body, calls);
            }
        }
        DoElem::TryCatch(_, body, catches, finally) => {
            walk_seq(body, calls);
            for c in catches {
                walk_seq(&c.body, calls);
            }
            if let Some(seq) = finally {
                walk_seq(seq, calls);
            }
        }
        DoElem::LetElse(_, _, e, seq) => {
            walk(e, calls);
            walk_seq(seq, calls);
        }
        DoElem::LetExpr(_, _, e, _, seq) => {
            walk(e, calls);
            walk_seq(seq, calls);
        }
        DoElem::Repeat(_, seq) => walk_seq(seq, calls),
        DoElem::Break(_) | DoElem::Continue(_) => {}
    }
}

/// Collect the function and all arguments from nested application nodes (#389)
///
/// For `f a b` represented as `App(App(f, [a]), [b])`, returns `(f, [a, b])`.
/// Arguments are collected in application order (leftmost first).
fn collect_app_spine(expr: &SurfaceExpr) -> (&SurfaceExpr, Vec<&clean_parser::SurfaceArg>) {
    let mut args = Vec::new();
    let mut current = expr;

    while let SurfaceExpr::App(_, func, app_args) = current {
        // Prepend these args (they come later in the spine but we collect from outer to inner)
        for arg in app_args.iter().rev() {
            args.push(arg);
        }
        current = func;
    }

    // Reverse to get args in correct order (innermost application's args first)
    args.reverse();
    (current, args)
}

/// True when `candidate` names the function `func_name.normalized_full()`,
/// tolerating an enclosing-namespace prefix.
///
/// A recursive `def Ty.bitWidth` written inside `namespace TrustIr` has
/// `normalized_full == "Ty.bitWidth"` (the surface name carries no namespace
/// prefix at detection time), yet its self-calls may be spelled with the full
/// qualified path `TrustIr.Ty.bitWidth`. Treat the candidate as a match when it
/// equals the full name *or* ends with `.<full>` so namespace-prefixed
/// self-references are recognised (Track R, Basic.lean `Ty.bitWidth`).
fn matches_full(candidate: &str, func_name: &RecursionNameParts) -> bool {
    let full = func_name.normalized_full();
    candidate == full || candidate.ends_with(&format!(".{full}"))
}

/// Check if an expression is a call to the function being defined
fn is_recursive_call(
    func_name: &RecursionNameParts,
    expr: &SurfaceExpr,
    shadowed_short: bool,
    shadowed_base: bool,
) -> bool {
    stack_safe(|| match expr {
        SurfaceExpr::Ident(_, name) => {
            let normalized = normalize_root_prefix(name);
            if func_name.base().is_none() {
                !shadowed_short && normalized == func_name.normalized_full()
            } else {
                (!shadowed_base && matches_full(normalized, func_name))
                    || (!shadowed_short && normalized == func_name.short())
            }
        }
        SurfaceExpr::Paren(_, inner) => {
            is_recursive_call(func_name, inner, shadowed_short, shadowed_base)
        }
        SurfaceExpr::Explicit(_, inner) => {
            is_recursive_call(func_name, inner, shadowed_short, shadowed_base)
        }
        SurfaceExpr::Ascription(_, inner, _) => {
            is_recursive_call(func_name, inner, shadowed_short, shadowed_base)
        }
        SurfaceExpr::UniverseInst(_, inner, _) => {
            is_recursive_call(func_name, inner, shadowed_short, shadowed_base)
        }
        SurfaceExpr::OutParam(_, inner) => {
            is_recursive_call(func_name, inner, shadowed_short, shadowed_base)
        }
        SurfaceExpr::SemiOutParam(_, inner) => {
            is_recursive_call(func_name, inner, shadowed_short, shadowed_base)
        }
        SurfaceExpr::Proj(_, base, Projection::Named(field)) => {
            // Two recognised proj-shaped self-calls:
            //
            // (1) Namespace-qualified path `TrustIr.Ty.bitWidth`: the whole
            //     dotted chain reduces to a constant name; match it (with
            //     namespace-prefix tolerance) against the function name.
            //
            // (2) Method dot-notation on the decreasing variable
            //     `elemTy.bitWidth`: `elemTy : Ty` resolves the call to
            //     `Ty.bitWidth elemTy`. Syntactically the base is a plain
            //     variable identifier and the field equals the function's short
            //     name. Treat this as a recursive call with the receiver as the
            //     sole argument so the structural lowering can route it through
            //     the induction hypothesis (Track R, Basic.lean `Ty.bitWidth`).
            if !shadowed_base {
                if let Some(name) = qualified_name_from_proj(expr) {
                    if matches_full(normalize_root_prefix(&name), func_name) {
                        return true;
                    }
                }
                if !shadowed_short
                    && field == func_name.short()
                    && matches!(base.as_ref(), SurfaceExpr::Ident(_, _))
                {
                    return true;
                }
            }
            false
        }
        SurfaceExpr::Proj(_, _, _) => false,
        _ => false,
    })
}

/// Find the decreasing argument position for structural recursion (#403, #433).
///
/// Prefers positions where the argument differs from the parameter name
/// (indicating structural decrease). Falls back to the last all-variable position.
pub(super) fn find_decreasing_arg(
    calls: &[RecursiveCall],
    param_names: &[String],
    preferred: Option<usize>,
) -> Option<usize> {
    if calls.is_empty() {
        return None;
    }

    let min_args = calls.iter().map(|c| c.args.len()).min().unwrap_or(0);
    let max_args = calls.iter().map(|c| c.args.len()).max().unwrap_or(0);

    if min_args != max_args {
        return None;
    }

    // Whole-body match-scrutinee preference (shadowed-rebind support): when the
    // body scrutinizes parameter `preferred` and every recursive call passes a
    // variable at that position, that position is the decreasing argument —
    // even when the variable's NAME equals the parameter (a pattern rebind).
    if let Some(pos) = preferred {
        if pos < min_args
            && calls
                .iter()
                .all(|call| matches!(call.args.get(pos), Some(RecursiveArg::Var(_))))
        {
            return Some(pos);
        }
    }

    let mut var_positions = Vec::new();
    for pos in 0..min_args {
        let all_vars = calls
            .iter()
            .all(|call| matches!(call.args.get(pos), Some(RecursiveArg::Var(_))));
        if all_vars {
            var_positions.push(pos);
        }
    }

    if var_positions.is_empty() {
        return None;
    }

    if !param_names.is_empty() {
        for &pos in &var_positions {
            if pos < param_names.len() {
                let param_name = &param_names[pos];
                let all_different = calls.iter().all(|call| {
                    if let Some(RecursiveArg::Var(arg_name)) = call.args.get(pos) {
                        arg_name != param_name
                    } else {
                        false
                    }
                });
                if all_different {
                    return Some(pos);
                }
            }
        }
    }

    // Fallback: last candidate (inductive argument typically comes last)
    var_positions.last().copied()
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Macro-expansion-time evaluation of *computed* `macro_rules` right-hand
//! sides (the metaprogramming-monad analog of [`super::user_term`]).
//!
//! # The gap this closes
//!
//! A `macro_rules` arm whose RHS is a pure syntax quotation
//!
//! ```text
//! macro_rules | `(twice $x) => `($x + $x)
//! ```
//!
//! is a template: [`super::registration::surface_expr_to_syntax_quote`] lowers
//! it directly and the macro expander substitutes the matched antiquotation
//! vars. But Lean also allows a *computed* RHS — a `do`-block (a `MacroM`
//! action) that builds and returns a `Syntax`:
//!
//! ```text
//! macro_rules | `(wrap $x) => do let inner := `(id $x); return `(f $inner)
//! ```
//!
//! Here the body is evaluated *at macro-expansion time*: the `let` binds the
//! quotation value `` `(id $x) `` to `inner`, and the trailing `` `(f $inner) ``
//! splices that value back in, so the arm is equivalent to the direct quotation
//! `` `(f (id $x)) ``. Before this module, [`super::registration`] ran the same
//! pure-template lowering on the *whole* `do`-block, which is not a quotation,
//! so the computed structure was silently mishandled.
//!
//! # The tractable, faithful subset evaluated here
//!
//! This module evaluates the common, deterministic shapes whose value is a
//! quotation built from the matched pattern variables and from `let`/`<-`
//! bindings of other quotations:
//!
//! - a `do`-block whose statements are zero or more **quotation bindings**
//!   followed by a trailing **quotation** value (`return `(…)`` or a bare
//!   trailing `` `(…) `` expression). A quotation binding is either a pure
//!   `let n := `(…)`` or a monadic `let n <- `(…)``: in `MacroM` a quotation
//!   has type `MacroM Syntax`, so the `<-` bind yields the same `Syntax` value
//!   the `:=` form makes available, and (modelling no hygiene gensym) the two
//!   are byte-identical;
//! - a single-statement computed body of either of those trailing forms;
//! - a trailing metaprogram-time `if <literal-bool> then return `(…)`` `else …`
//!   that selects among quotations;
//! - a **`throwError` `MacroM` effect** raised by the body — `throwError "msg"`,
//!   `throwErrorAt _ "msg"`, `throw "msg"`, or a fully-resolvable interpolation
//!   `throwError s!"…"` — whether as the trailing value, inside a literal-selected
//!   `if` branch, or as a bare (non-`do`) RHS. Faithful to Lean's `MacroM`, this
//!   means the macro FAILS to expand: we surface the user's message as a real
//!   macro diagnostic ([`MacroRegistrationError::MacroThrowError`], rendered with
//!   the same B87/B89 machinery the metaprog tactic/term evaluator uses), never a
//!   fabricated expansion.
//!
//! A `let`-bound name referenced by a later quotation's `$name` antiquotation is
//! resolved by **splicing the bound quotation's body** in place (wrapped in
//! parentheses to preserve grouping); a `$name` that refers to a *pattern*
//! variable is left as an antiquotation so the macro expander substitutes the
//! matched syntax exactly as in the pure-template path. The produced
//! [`clean_macro::SyntaxQuote`] is byte-identical to the equivalent direct
//! quotation, so the result flows through the normal expand → elaborate →
//! kernel-check pipeline unchanged.
//!
//! # What it DEFERS (and why that matters for soundness)
//!
//! Anything outside the subset above returns an honest
//! [`MacroRegistrationError::ComputedBodyUnsupported`] rather than a fabricated
//! expansion: a monadic bind whose action is a *non-quotation* (`x <- act` for
//! a real `MacroM` action such as `expandMacro x`), `if` over a
//! non-literal/non-`Bool` condition, loops, matches, and any non-quotation value.
//! A `throwError` whose message text depends on runtime-matched syntax (an
//! `s!"…"` hole bound to a pattern variable or a `let`-bound quotation) also
//! defers here, since the message cannot be rendered faithfully at expansion
//! time. Macro expansion only ever produces `Syntax`, which is elaborated and
//! kernel-checked downstream, so a deferred body surfaces as a registration error
//! at the call site — it is never silently mis-expanded. No kernel bypass, no
//! axioms.
//!
//! # Honest-pinned: fresh-name / hygiene gensym (`mkFreshId` / `addMacroScope`)
//!
//! A computed body that introduces a *fresh* binder — `let fresh <- mkFreshId`
//! then `` `(fun $fresh => …) `` — is NOT yet evaluated here, and DEFERS. This is
//! a genuine architectural gap, not a quick add, for one structural reason:
//!
//! - This evaluator runs **once, at registration time**, producing a single
//!   static [`SyntaxQuote`] template stored in the `MacroDef`. The macro expander
//!   ([`clean_macro::expand`]) then substitutes the matched antiquotations into
//!   that fixed template on *every* application.
//! - A faithful `mkFreshId` must yield a **distinct unique name per expansion**,
//!   threaded from the expander's live fresh-name counter. Clean already HAS that
//!   counter — [`clean_macro::hygiene::HygieneContext::fresh`] /
//!   [`clean_macro::hygiene::HygieneState::gensym`], deterministic (a monotone
//!   `AtomicU64`, no `Date.now`/random) and hygienic (scope-tagged) — but it lives
//!   in the *expander*, not at registration time, and bakes nothing into a static
//!   template.
//!
//! The precise design to close this (a focused follow-up, not done here):
//!   1. Store the computed body **unevaluated** in the `MacroDef` (a new
//!      `MacroDef` expansion variant alongside the static `SyntaxQuote`), instead
//!      of evaluating it once at registration.
//!   2. When the expander applies that arm, evaluate the body **lazily** with the
//!      matched antiquotation environment AND a `&mut HygieneContext` borrowed
//!      from the active `HygienicExpander`. `mkFreshId`/`addMacroScope` then call
//!      `HygieneContext::fresh`/`gensym`, producing a per-expansion hygienic
//!      unique name.
//!   3. Splice the fresh name as the resolved value of its `$fresh`
//!      antiquotation, exactly as `let`-bound quotations are spliced today.
//!
//! Until that lands, a fresh-name body defers honestly here.

use clean_parser::{DoElem, QAntiquotContent, Span, SurfaceArg, SurfaceExpr, SurfaceFieldAssign};

use super::registration::{quotation_category, MacroRegistrationError};
use crate::infer::user_tactic::{as_throw_error_message_in, is_throw_error_call};
use clean_macro::{Syntax, SyntaxQuote};

/// Reserved prefix marking a `let`-binding introduced by a fresh-name effect
/// (`mkFreshId` / `addMacroScope`). A `$name` resolving to such a binding is
/// spliced as `Ident("<this prefix><gensym prefix>")`, which the post-lowering
/// rewrite ([`rewrite_fresh_markers`]) converts into a
/// [`clean_macro::Syntax::mk_fresh_marker`] — gensym'd anew per expansion.
const FRESH_MARKER_SENTINEL: &str = "__clean_fresh_marker__";

/// The matched pattern variable names of a `macro_rules` arm (the antiquotation
/// names in the arm's pattern, e.g. `["x"]` for `` `(wrap $x) ``). A `$name`
/// referencing one of these is a *pattern* variable and stays an antiquotation
/// in the produced quotation; any other `$name` must resolve to a `let` binding.
type PatternVars = [String];

/// If `arm_expansion` is a *computed* (`do`-block) `macro_rules` RHS, evaluate
/// the supported subset to the equivalent quotation and return it as a
/// [`SyntaxQuote`].
///
/// Returns:
/// - `None` when `arm_expansion` is **not** a `do`-block — the caller keeps the
///   existing pure-template fast path, so previously-handled arms never regress;
/// - `Some(Ok(quote))` when the computed body is in the faithful subset and was
///   evaluated to a quotation byte-identical to the equivalent direct quotation;
/// - `Some(Err(..))` when the body is computed but outside the subset — an
///   honest defer that surfaces as a registration error rather than a silent
///   mis-expansion.
pub(super) fn evaluate_computed_macro_body(
    pattern: &SurfaceExpr,
    arm_expansion: &SurfaceExpr,
) -> Option<Result<SyntaxQuote, MacroRegistrationError>> {
    let pattern_vars = collect_pattern_vars(pattern);
    match arm_expansion {
        SurfaceExpr::Do(_, elems) => Some(eval_do_block(elems, &pattern_vars)),
        // A *bare* (non-`do`) `throwError "msg"` RHS is itself a `MacroM` action
        // that unconditionally raises the user's custom error — e.g.
        // `macro_rules | `(boom $x) => throwError "bad input"`. There is no
        // quotation value here, so it is not a pure-template arm; recognize it and
        // surface the error rather than falling through to the template path
        // (which would mis-lower the `throwError` call as a syntax template). A
        // `throwError` whose message is not renderable here (depends on
        // runtime-matched syntax) DEFERS honestly.
        expr if is_throw_error_call(expr) => Some(
            eval_throw_error(expr, &[])
                .unwrap_or_else(|| Err(unsupported("throwError message is not a literal"))),
        ),
        // Any other non-`do` RHS is a pure template: the caller keeps the existing
        // fast path so previously-handled arms never regress.
        _ => None,
    }
}

/// Evaluate a `do`-block body to the quotation it returns.
///
/// Threads a binding environment (name → resolved quotation body) through the
/// leading quotation-binding statements (pure `let n := `(…)`` or monadic
/// `let n <- `(…)``), then evaluates the trailing value statement
/// (`return `(…)``, a bare `` `(…) ``, or a metaprogram-time `if`).
fn eval_do_block(
    elems: &[DoElem],
    pattern_vars: &PatternVars,
) -> Result<SyntaxQuote, MacroRegistrationError> {
    // Quotation bindings introduced by leading `let n := `(…)`` or
    // `let n <- `(…)`` statements. Each value is the *parsed body* of the bound
    // quotation, ready to splice.
    let mut env: Vec<(String, SurfaceExpr)> = Vec::new();

    let Some((last, leading)) = elems.split_last() else {
        return Err(unsupported("empty do-block has no quotation value"));
    };

    for elem in leading {
        match elem {
            // A pure `let n := `(…)`` binds a quotation value usable by later
            // `$n` antiquotations. The bound value must itself be a quotation we
            // can resolve in the current environment.
            DoElem::Let(_, binder, value) => {
                // `let f := addMacroScope ident` introduces a fresh hygienic
                // name per expansion. Bind it to a fresh-marker sentinel rather
                // than resolving a quotation.
                if let Some(prefix) = fresh_name_prefix(value) {
                    env.push((binder.name.clone(), fresh_marker_sentinel(prefix)));
                } else {
                    let body = resolve_value_to_body(value, pattern_vars, &env)?;
                    env.push((binder.name.clone(), body));
                }
            }
            // A monadic bind `let n <- `(…)`` of a *syntax quotation*. In `MacroM`
            // a quotation `` `(…) `` has type `MacroM Syntax`, so binding its result
            // with `<-` yields the very `Syntax` value the quotation denotes — the
            // same value the pure `let n := `(…)`` form makes available. Because
            // this evaluator models no hygiene gensym, the two forms are
            // byte-identical, so we resolve the quotation body and bind it exactly
            // as for `let :=`. A bind whose action is *not* a quotation (a real
            // monadic action such as `let y <- expandMacro x`) falls through to
            // `resolve_value_to_body`, which requires a quotation and therefore
            // DEFERS honestly rather than fabricating a value.
            DoElem::Bind(_, binder, value) => {
                // `let f <- mkFreshId` is the canonical fresh-name effect: bind
                // `f` to a fresh-marker sentinel so each expansion gensyms a
                // distinct id (the per-expansion fix). Other monadic binds must
                // still be quotations or DEFER honestly.
                if let Some(prefix) = fresh_name_prefix(value) {
                    env.push((binder.name.clone(), fresh_marker_sentinel(prefix)));
                } else {
                    let body = resolve_value_to_body(value, pattern_vars, &env)?;
                    env.push((binder.name.clone(), body));
                }
            }
            // Any other leading statement (control flow, expression side-effect,
            // loops, matches, ...) is outside the deterministic quotation subset.
            _ => {
                return Err(unsupported(
                    "only pure `let n := `(…)`` or `let n <- `(…)`` quotation bindings may precede the returned quotation",
                ))
            }
        }
    }

    eval_value_elem(last, pattern_vars, &env)
}

/// Evaluate the trailing value statement of a `do`-block to a quotation.
fn eval_value_elem(
    elem: &DoElem,
    pattern_vars: &PatternVars,
    env: &[(String, SurfaceExpr)],
) -> Result<SyntaxQuote, MacroRegistrationError> {
    match elem {
        // `return `(…)`` or a bare trailing `` `(…) ``: the value is a quotation,
        // UNLESS it is a `throwError "msg"` action raising the user's custom error.
        DoElem::Return(_, value) | DoElem::Expr(_, value) => {
            if let Some(result) = eval_throw_error(value, env) {
                return result;
            }
            eval_value_expr(value, pattern_vars, env)
        }
        // A metaprogram-time `if <literal-bool> then return `(…)`` else …`
        // selects among quotations (both branches must themselves be evaluable
        // do-sequences).
        DoElem::If(_, cond, then_branch, else_branch) => {
            let take_then = literal_bool(cond).ok_or_else(|| {
                unsupported("computed `if` condition is not a literal `true`/`false`")
            })?;
            let chosen = if take_then {
                then_branch.as_slice()
            } else {
                let else_branch = else_branch.as_ref().ok_or_else(|| {
                    unsupported("computed `if` without an `else` branch cannot yield a quotation")
                })?;
                else_branch.as_slice()
            };
            eval_do_block(chosen, pattern_vars)
        }
        _ => Err(unsupported(
            "the returned do-block value must be a syntax quotation",
        )),
    }
}

/// Evaluate a value expression that must denote a quotation, returning it as a
/// [`SyntaxQuote`] with antiquotations resolved against the `let` environment.
fn eval_value_expr(
    value: &SurfaceExpr,
    pattern_vars: &PatternVars,
    env: &[(String, SurfaceExpr)],
) -> Result<SyntaxQuote, MacroRegistrationError> {
    let SurfaceExpr::SyntaxQuote(_, content) = value else {
        return Err(unsupported(
            "the returned do-block value must be a syntax quotation",
        ));
    };
    // Parse the quotation body, resolve `let`-bound `$name` antiquotations by
    // splicing, then lower with the *same* body→`Syntax` lowering the pure
    // template path uses (`surface_to_syntax` + delimiter-derived category). This
    // keeps the produced `Syntax` byte-identical to the equivalent direct
    // quotation — no lossy string rendering is involved.
    let body = clean_parser::parse_quotation_body(content)
        .map_err(|e| MacroRegistrationError::QuotationParse(e.to_string()))?;
    let resolved = resolve_antiquots(&body, pattern_vars, env)?;
    // Lower to macro `Syntax`, then rewrite any fresh-marker sentinel idents into
    // real fresh-marker nodes so the expander gensyms them per expansion.
    let lowered = rewrite_fresh_markers(super::surface_to_syntax(&resolved));
    Ok(SyntaxQuote::new(lowered, quotation_category(content)))
}

/// Whether `value` is a fresh-name effect whose binder must gensym per
/// expansion: `mkFreshId` (a `MacroM Name`/`Ident` action) or
/// `addMacroScope <ident>` / `MonadQuotation.addMacroScope <ident>`. Returns the
/// gensym prefix to seed readable names with.
fn fresh_name_prefix(value: &SurfaceExpr) -> Option<&'static str> {
    match value {
        // `mkFreshId` — a bare identifier naming the fresh-id effect.
        SurfaceExpr::Ident(_, name) if is_fresh_id_ident(name) => Some("x"),
        // `addMacroScope ident` — applied form; the argument names the base.
        SurfaceExpr::App(_, func, args) if !args.is_empty() => {
            let SurfaceExpr::Ident(_, fname) = func.as_ref() else {
                return None;
            };
            if is_add_macro_scope_ident(fname) {
                Some("x")
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Whether `name` denotes the `mkFreshId` fresh-identifier effect.
fn is_fresh_id_ident(name: &str) -> bool {
    matches!(
        name,
        "mkFreshId" | "Lean.mkFreshId" | "mkFreshUserName" | "Lean.Macro.mkFreshId"
    )
}

/// Whether `name` denotes the `addMacroScope` hygiene effect.
fn is_add_macro_scope_ident(name: &str) -> bool {
    matches!(
        name,
        "addMacroScope"
            | "Lean.addMacroScope"
            | "MonadQuotation.addMacroScope"
            | "Lean.MonadQuotation.addMacroScope"
    )
}

/// Build the sentinel `SurfaceExpr` a fresh-name binding resolves to: a bare
/// identifier whose name carries the [`FRESH_MARKER_SENTINEL`] prefix plus the
/// gensym prefix. [`rewrite_fresh_markers`] turns it into a fresh-marker node.
fn fresh_marker_sentinel(prefix: &str) -> SurfaceExpr {
    SurfaceExpr::Ident(Span::dummy(), format!("{FRESH_MARKER_SENTINEL}{prefix}"))
}

/// Rewrite every sentinel identifier (see [`fresh_marker_sentinel`]) in a lowered
/// `Syntax` tree into a [`clean_macro::Syntax::mk_fresh_marker`] node. The marker
/// is gensym'd per expansion by the hygienic expander, so each application of the
/// macro yields a distinct fresh id.
fn rewrite_fresh_markers(syntax: Syntax) -> Syntax {
    match syntax {
        Syntax::Ident(_, ref name) => {
            if let Some(prefix) = name.strip_prefix(FRESH_MARKER_SENTINEL) {
                Syntax::mk_fresh_marker(prefix)
            } else {
                syntax
            }
        }
        Syntax::Node(node) => {
            let kind = node.kind.clone();
            let children = node
                .children
                .iter()
                .map(|c| rewrite_fresh_markers(c.clone()))
                .collect();
            Syntax::node(kind, children)
        }
        other => other,
    }
}

/// If `value` is a `throwError`-family action (`throwError "msg"` /
/// `throwErrorAt _ "msg"` / `throw "msg"`, or a string-interpolation form
/// `throwError s!"…"`), evaluate the FULL `MacroM` effect it denotes at
/// macro-expansion time.
///
/// Faithful to Lean's `MacroM`, a `throwError` raised while expanding a macro
/// means the macro fails to expand: there is no `Syntax` result. We surface the
/// user's own message as a real macro diagnostic via
/// [`MacroRegistrationError::MacroThrowError`] — NOT a fabricated expansion (the
/// B72 lesson: an effect we cannot turn into syntax must error, never
/// mis-expand). The message is rendered with the SAME shared machinery the
/// metaprogram tactic/term evaluator uses ([`as_throw_error_message_in`], B87/B89):
/// a plain string literal renders verbatim, and an `s!"…"`/`m!"…"`/`f!"…"`
/// interpolation renders by resolving its `{expr}` holes against `env`.
///
/// Returns:
/// - `Some(Err(MacroThrowError(msg)))` — a `throwError` whose message renders
///   fully to `msg`; the macro fails with that diagnostic;
/// - `Some(Err(ComputedBodyUnsupported(..)))` — a `throwError` whose message is
///   *not* renderable at expansion time (an `s!"…"` hole referring to a
///   pattern-matched antiquotation or a `let`-bound quotation, whose text depends
///   on the runtime-matched syntax we do not have here): an honest DEFER, since
///   we must not fabricate the message text;
/// - `None` — `value` is not a `throwError` action, so the caller proceeds with
///   the normal quotation handling.
///
/// `env` carries the computed-body bindings (`let n := `(…)`` / `let n <- `(…)``)
/// as `(name, SurfaceExpr)` pairs — the very `Binding` shape
/// [`as_throw_error_message_in`] resolves interpolation holes against. Those
/// bindings hold quotation *bodies* (syntax templates), which are not concrete
/// renderable values, so any hole that references one declines and the message
/// defers honestly rather than rendering a template as if it were a value.
fn eval_throw_error(
    value: &SurfaceExpr,
    env: &[(String, SurfaceExpr)],
) -> Option<Result<SyntaxQuote, MacroRegistrationError>> {
    if !is_throw_error_call(value) {
        return None;
    }
    Some(match as_throw_error_message_in(value, env) {
        Some(message) => Err(MacroRegistrationError::MacroThrowError(message)),
        // A `throwError` whose message we cannot faithfully render here (its text
        // depends on runtime-matched syntax) DEFERS — we never fabricate the
        // message, and we never silently drop the `throwError` either.
        None => Err(unsupported(
            "throwError message could not be rendered at macro-expansion time \
             (it depends on runtime-matched syntax): the full MacroM monad is required",
        )),
    })
}

/// Resolve a `let`-bound value to its quotation body (parsed, with antiquotations
/// already resolved against the bindings in scope before it).
fn resolve_value_to_body(
    value: &SurfaceExpr,
    pattern_vars: &PatternVars,
    env: &[(String, SurfaceExpr)],
) -> Result<SurfaceExpr, MacroRegistrationError> {
    let SurfaceExpr::SyntaxQuote(_, content) = value else {
        return Err(unsupported(
            "a `let :=`/`let <-` binding in a computed macro body must bind a syntax quotation",
        ));
    };
    let body = clean_parser::parse_quotation_body(content)
        .map_err(|e| MacroRegistrationError::QuotationParse(e.to_string()))?;
    resolve_antiquots(&body, pattern_vars, env)
}

/// Replace each `$name` antiquotation in `expr` that refers to a `let` binding
/// with the bound quotation body (wrapped in parens to preserve grouping).
/// `$name` referring to a *pattern* variable is kept as an antiquotation so the
/// macro expander substitutes the matched syntax. An unknown `$name` (neither a
/// pattern var nor a binding) is an honest defer.
fn resolve_antiquots(
    expr: &SurfaceExpr,
    pattern_vars: &PatternVars,
    env: &[(String, SurfaceExpr)],
) -> Result<SurfaceExpr, MacroRegistrationError> {
    match expr {
        SurfaceExpr::QAntiquot {
            span,
            content: QAntiquotContent::Simple(name),
        } => {
            if let Some((_, body)) = env.iter().find(|(n, _)| n == name) {
                // Splice the bound quotation body, parenthesized so its internal
                // structure groups as a single argument at the splice site.
                Ok(SurfaceExpr::Paren(*span, Box::new(body.clone())))
            } else if pattern_vars.iter().any(|p| p == name) {
                // A matched pattern variable: keep the antiquotation verbatim.
                Ok(expr.clone())
            } else {
                Err(unsupported(
                    "`$name` in a computed macro body refers to neither a pattern variable nor a `let` binding",
                ))
            }
        }
        // Structural recursion through the quotation body shapes that can contain
        // antiquotations. Leaves are returned unchanged.
        SurfaceExpr::App(span, func, args) => {
            let func = Box::new(resolve_antiquots(func, pattern_vars, env)?);
            let args = args
                .iter()
                .map(|arg| {
                    Ok(SurfaceArg {
                        span: arg.span,
                        expr: resolve_antiquots(&arg.expr, pattern_vars, env)?,
                        name: arg.name.clone(),
                    })
                })
                .collect::<Result<Vec<_>, _>>()?;
            Ok(SurfaceExpr::App(*span, func, args))
        }
        SurfaceExpr::Paren(span, inner) => Ok(SurfaceExpr::Paren(
            *span,
            Box::new(resolve_antiquots(inner, pattern_vars, env)?),
        )),
        SurfaceExpr::Arrow(span, from, to) => Ok(SurfaceExpr::Arrow(
            *span,
            Box::new(resolve_antiquots(from, pattern_vars, env)?),
            Box::new(resolve_antiquots(to, pattern_vars, env)?),
        )),
        SurfaceExpr::Ascription(span, inner, ty) => Ok(SurfaceExpr::Ascription(
            *span,
            Box::new(resolve_antiquots(inner, pattern_vars, env)?),
            Box::new(resolve_antiquots(ty, pattern_vars, env)?),
        )),
        SurfaceExpr::Explicit(span, inner) => Ok(SurfaceExpr::Explicit(
            *span,
            Box::new(resolve_antiquots(inner, pattern_vars, env)?),
        )),
        SurfaceExpr::Proj(span, inner, proj) => Ok(SurfaceExpr::Proj(
            *span,
            Box::new(resolve_antiquots(inner, pattern_vars, env)?),
            proj.clone(),
        )),
        SurfaceExpr::If(span, cond, then_br, else_br) => Ok(SurfaceExpr::If(
            *span,
            Box::new(resolve_antiquots(cond, pattern_vars, env)?),
            Box::new(resolve_antiquots(then_br, pattern_vars, env)?),
            Box::new(resolve_antiquots(else_br, pattern_vars, env)?),
        )),
        SurfaceExpr::StructLit {
            span,
            struct_type,
            base,
            fields,
        } => Ok(SurfaceExpr::StructLit {
            span: *span,
            struct_type: struct_type
                .as_ref()
                .map(|t| resolve_antiquots(t, pattern_vars, env).map(Box::new))
                .transpose()?,
            base: base
                .as_ref()
                .map(|b| resolve_antiquots(b, pattern_vars, env).map(Box::new))
                .transpose()?,
            fields: fields
                .iter()
                .map(|f| {
                    Ok(SurfaceFieldAssign {
                        span: f.span,
                        name: f.name.clone(),
                        val: resolve_antiquots(&f.val, pattern_vars, env)?,
                    })
                })
                .collect::<Result<Vec<_>, _>>()?,
        }),
        // Other shapes (including non-`Simple` antiquotations such as splices and
        // typed antiquotations, which the subset does not model) are returned
        // unchanged; an unresolved binding-only `$name` therefore cannot hide here
        // because `Simple` is handled above and any binding-referencing shape must
        // route through it.
        other => Ok(other.clone()),
    }
}

/// Collect the antiquotation variable names of a `macro_rules` arm pattern.
///
/// The pattern is a syntax quotation such as `` `(wrap $x $y) ``; its `$x`/`$y`
/// antiquotations are the matched pattern variables. A pattern we cannot parse
/// yields an empty set (so every `$name` in the body must then resolve to a
/// `let` binding, and an unresolved one defers honestly).
fn collect_pattern_vars(pattern: &SurfaceExpr) -> Vec<String> {
    let SurfaceExpr::SyntaxQuote(_, content) = pattern else {
        return Vec::new();
    };
    let Ok(body) = clean_parser::parse_quotation_body(content) else {
        return Vec::new();
    };
    let mut vars = Vec::new();
    collect_simple_antiquots(&body, &mut vars);
    vars
}

/// Walk a parsed quotation body, recording every `$name` simple antiquotation.
fn collect_simple_antiquots(expr: &SurfaceExpr, out: &mut Vec<String>) {
    match expr {
        SurfaceExpr::QAntiquot {
            content: QAntiquotContent::Simple(name),
            ..
        } if !out.contains(name) => out.push(name.clone()),
        SurfaceExpr::App(_, func, args) => {
            collect_simple_antiquots(func, out);
            for arg in args {
                collect_simple_antiquots(&arg.expr, out);
            }
        }
        SurfaceExpr::Paren(_, inner)
        | SurfaceExpr::Explicit(_, inner)
        | SurfaceExpr::Proj(_, inner, _) => collect_simple_antiquots(inner, out),
        SurfaceExpr::Arrow(_, a, b) | SurfaceExpr::Ascription(_, a, b) => {
            collect_simple_antiquots(a, out);
            collect_simple_antiquots(b, out);
        }
        SurfaceExpr::If(_, c, t, e) => {
            collect_simple_antiquots(c, out);
            collect_simple_antiquots(t, out);
            collect_simple_antiquots(e, out);
        }
        _ => {}
    }
}

/// Whether `expr` is the literal boolean `true`/`false` (the only conditions a
/// metaprogram-time `if` in the subset decides on).
fn literal_bool(expr: &SurfaceExpr) -> Option<bool> {
    match expr {
        SurfaceExpr::Ident(_, name) if name == "true" || name == "True" => Some(true),
        SurfaceExpr::Ident(_, name) if name == "false" || name == "False" => Some(false),
        SurfaceExpr::Paren(_, inner) => literal_bool(inner),
        _ => None,
    }
}

/// Build an honest "computed body outside the supported subset" defer error.
fn unsupported(detail: &str) -> MacroRegistrationError {
    MacroRegistrationError::ComputedBodyUnsupported(detail.to_string())
}

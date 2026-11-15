// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Application and atom expression parsing.
//! Extracted from expr.rs as part of #307.

use super::expr_match::fold_right_nonempty;
use super::Parser;
use crate::lexer::TokenKind;
use crate::surface::*;
use crate::ParseError;

/// Cdot section desugaring (Lean's `(· + 1)` / `(·.snd)` / `(f ·)` anonymous
/// function notation).
///
/// A `·` inside parentheses is a placeholder for a fresh lambda parameter; the
/// enclosing parentheses delimit the function. `(· + 1)` desugars to
/// `fun __cdot_0 => __cdot_0 + 1`, `(·.snd)` to `fun __cdot_0 => __cdot_0.snd`,
/// and `(f · ·)` to `fun __cdot_0 __cdot_1 => f __cdot_0 __cdot_1` (one binder
/// per occurrence, left to right).
///
/// The walk replaces `·` placeholders in the *immediately enclosing* term only.
/// It descends through application/projection/ascription/arrow spines but stops
/// at any construct that introduces its own scope or its own parentheses
/// (`Lambda`, `Pi`, `let`, `match`, `if`, nested `Paren`, `do`, `by`, …) — an
/// inner `(· …)` has already been desugared to a `Lambda` by the time an outer
/// paren is processed, so its placeholders are invisible here. (Track EF)
pub(super) mod cdot {
    use crate::surface::*;

    /// Replace each `·` placeholder in `e` (in place, left to right) with a
    /// fresh `__cdot_N` variable, pushing the generated binder onto `binders`.
    /// Returns nothing; the placeholder count is `binders.len()` afterwards.
    fn rewrite(e: &mut SurfaceExpr, binders: &mut Vec<SurfaceBinder>) {
        match e {
            SurfaceExpr::Ident(span, name) if name.is_unescaped_component("·") => {
                // Unspellable: the binder encloses the user's own expression,
                // so a spellable `__cdot_0` captured a reference to a global
                // of that spelling — `(· + __cdot_0) 1` computed `2` (measured
                // 2026-09-25; Lean 4.8.0 reads the global).
                let fresh = SurfaceName::unspellable("__cdot", binders.len() as u64);
                let mut binder =
                    SurfaceBinder::new_typed(fresh.clone(), None, SurfaceBinderInfo::Explicit);
                // The `·` token's position orders this binder among the
                // section's parameters (`desugar`).
                binder.span = *span;
                binders.push(binder);
                *name = fresh;
            }
            // Application spine: rewrite the head and every positional/named arg.
            SurfaceExpr::App(_, head, args) => {
                rewrite(head, binders);
                for arg in args.iter_mut() {
                    rewrite(&mut arg.expr, binders);
                }
            }
            // Projection: `·.snd` — rewrite the projected base.
            SurfaceExpr::Proj(_, base, _) => rewrite(base, binders),
            // Type ascription / wrappers: rewrite the value (not type) side.
            SurfaceExpr::Ascription(_, inner, _)
            | SurfaceExpr::Explicit(_, inner)
            | SurfaceExpr::OutParam(_, inner)
            | SurfaceExpr::SemiOutParam(_, inner)
            | SurfaceExpr::UniverseInst(_, inner, _)
            | SurfaceExpr::LiftMethod(_, inner)
            | SurfaceExpr::NamedArg(_, _, inner) => rewrite(inner, binders),
            // Binary-operator arrows like `· → ·` are rare but supported.
            SurfaceExpr::Arrow(_, lhs, rhs) => {
                rewrite(lhs, binders);
                rewrite(rhs, binders);
            }
            // Everything else introduces its own scope or paren boundary; a
            // placeholder inside it belongs to a *different* (already-resolved)
            // section, so stop the walk here.
            _ => {}
        }
    }

    /// The placeholder a `·` operand of a notation template stands for
    /// until the enclosing parentheses bind it: an unspellable name keyed by
    /// the `·` token's source position, so the copies a template makes of one
    /// operand are one placeholder (and one binder).
    fn operand_placeholder(position: usize) -> SurfaceName {
        SurfaceName::unspellable("__cdot_operand", position as u64)
    }

    /// The source position an operand placeholder stands for, if `name` is
    /// one ([`operand_placeholder`]).
    fn operand_placeholder_position(name: &SurfaceName) -> Option<usize> {
        let clean_kernel::name::NameInner::Num(parent, position) = name.name().inner() else {
            return None;
        };
        let position = usize::try_from(*position).ok()?;
        name.same_syntax(&operand_placeholder(position))
            .then_some(())
            .filter(|()| **parent == clean_kernel::Name::anon().str("__cdot_operand"))
            .map(|()| position)
    }

    /// Replace each `·` on `operand`'s section spine (the positions [`desugar`]
    /// binds) with its operand placeholder. A notation template is expanded
    /// where it is parsed, so the `·` of `(N ·)` would otherwise end up inside
    /// the template, out of the reach of the enclosing parentheses — which
    /// Lean binds it to, as it expands the section before the notation.
    /// Returns the source positions of the replaced `·`s.
    pub(in crate::grammar) fn hoist_operand(operand: &mut SurfaceExpr) -> Vec<usize> {
        let mut positions = Vec::new();
        collect_spine_placeholders(operand, &mut positions);
        positions
    }

    fn collect_spine_placeholders(e: &mut SurfaceExpr, positions: &mut Vec<usize>) {
        match e {
            SurfaceExpr::Ident(span, name) if name.is_unescaped_component("·") => {
                positions.push(span.start);
                *name = operand_placeholder(span.start);
            }
            SurfaceExpr::App(_, head, args) => {
                collect_spine_placeholders(head, positions);
                for arg in args.iter_mut() {
                    collect_spine_placeholders(&mut arg.expr, positions);
                }
            }
            SurfaceExpr::Proj(_, base, _) => collect_spine_placeholders(base, positions),
            SurfaceExpr::Ascription(_, inner, _)
            | SurfaceExpr::Explicit(_, inner)
            | SurfaceExpr::OutParam(_, inner)
            | SurfaceExpr::SemiOutParam(_, inner)
            | SurfaceExpr::UniverseInst(_, inner, _)
            | SurfaceExpr::LiftMethod(_, inner)
            | SurfaceExpr::NamedArg(_, _, inner) => collect_spine_placeholders(inner, positions),
            SurfaceExpr::Arrow(_, lhs, rhs) => {
                collect_spine_placeholders(lhs, positions);
                collect_spine_placeholders(rhs, positions);
            }
            _ => {}
        }
    }

    /// If `e` contains `·` section placeholders, desugar it into an anonymous
    /// `fun __cdot_0 … => e'` lambda. Otherwise return `e` unchanged. `span` is
    /// the span of the enclosing parenthesized form.
    ///
    /// The placeholders of `·` operands of notation templates expanded
    /// inside `e` ([`hoist_operand`], their positions in `hoisted`) are bound
    /// here too, wherever the template put them — and when it put one only
    /// where no reference can stand (a structure field, a named argument) or
    /// nowhere at all, it is bound all the same: Lean expands `(N ·)` to `fun
    /// x✝ => N x✝` before `N`. Every binder is ordered by the source position
    /// of its `·`, as Lean orders a section's parameters; the positions bound
    /// here leave `hoisted`.
    pub(in crate::grammar) fn desugar(
        span: Span,
        mut e: SurfaceExpr,
        hoisted: &mut Vec<usize>,
    ) -> SurfaceExpr {
        let mut binders = Vec::new();
        rewrite(&mut e, &mut binders);
        let mut positioned: Vec<(usize, SurfaceBinder)> = Vec::new();
        if !hoisted.is_empty() {
            // The template walk lists every name `e` leaves unbound; those
            // that are operand placeholders are this section's. (A form the
            // walk refuses leaves them unbound: an unknown identifier, never
            // another binding.)
            if let Ok(free) =
                template_free_reference_spellings(&e, &[], &clean_kernel::Name::anon())
            {
                for name in free {
                    if let Some(position) = operand_placeholder_position(&name) {
                        positioned.push((
                            position,
                            SurfaceBinder::new_typed(
                                operand_placeholder(position),
                                None,
                                SurfaceBinderInfo::Explicit,
                            ),
                        ));
                    }
                }
            }
            let inside = |position: &usize| (span.start..span.end).contains(position);
            for position in hoisted.iter().copied().filter(inside) {
                if !positioned.iter().any(|(bound, _)| *bound == position) {
                    positioned.push((
                        position,
                        SurfaceBinder::new_typed(
                            operand_placeholder(position),
                            None,
                            SurfaceBinderInfo::Explicit,
                        ),
                    ));
                }
            }
            hoisted.retain(|position| !inside(position));
        }
        if binders.is_empty() && positioned.is_empty() {
            return e;
        }
        if !positioned.is_empty() {
            let mut spine: Vec<(usize, SurfaceBinder)> =
                binders.into_iter().map(|b| (b.span.start, b)).collect();
            spine.append(&mut positioned);
            spine.sort_by_key(|(position, _)| *position);
            binders = spine.into_iter().map(|(_, b)| b).collect();
        }
        SurfaceExpr::Lambda(span, binders, Box::new(e))
    }
}

/// Lean's `maxPrec` (`eval_prec max`): the level of an application argument
/// and of an application's function. A `postfix:max` operator's result sits
/// here, so it can head an application and be one of its arguments.
const MAX_PREC: u32 = 1024;

impl Parser {
    /// Application: f x y z
    pub(super) fn app_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        let head = self.atom_expr()?;
        self.app_expr_with_head(head)
    }

    /// [`Self::app_expr`] over a head that is already parsed.
    ///
    /// The `prefix:max` arm of `custom_notation.rs` builds its notation term
    /// and then continues into this loop, because at `max` the result is
    /// itself a max-precedence term and can head an application — the mirror
    /// of the `postfix:max` head rule below.
    pub(super) fn app_expr_with_head(
        &mut self,
        head: SurfaceExpr,
    ) -> Result<SurfaceExpr, ParseError> {
        let mut expr = head;
        let mut pending_args: Vec<SurfaceArg> = Vec::new();
        // Set once a `postfix:max` operator has been applied to the head.
        let mut head_is_notation = false;

        loop {
            // A `postfix:max` operator right after the HEAD, before any
            // argument: `postfix:max op => f` is `notation:max arg:max op`
            // (`Lean/Elab/Mixfix.lean:30-31`), a max-precedence term, which is
            // exactly what `app := trailing_parser:leadPrec:maxPrec many1
            // argument` (`Lean/Parser/Term.lean:853`) takes as its FUNCTION.
            // So `xᶜ i` is `(xᶜ) i`. Without this the head refused the
            // operator (`is_atom_start` rejects it), the application closed
            // with no argument, the postfix was applied by `custom_op_expr`
            // afterwards, and `i` had no consumer: `Pi.compl_apply`
            // (`Mathlib/Order/Basic.lean:513`) died "expected :=, | or where,
            // got Ident(i)". A postfix after an ARGUMENT is bound to that
            // argument below; postfixes below max keep their outer position.
            //
            // The notation term is the application's head SYNTAX, which Lean's
            // `elabAppFn` elaborates on its own (`| _ => elabTerm f none`,
            // `Lean/Elab/App.lean`) before applying the arguments; the `Paren`
            // node keeps it that separate unit here instead of a nested `App`
            // spine the elaborator would read as one flat application.
            if pending_args.is_empty() && self.has_custom_operators() {
                if let Some(op) = self.match_custom_operator(NotationKind::Postfix) {
                    if op.precedence >= MAX_PREC {
                        self.consume_custom_operator(&op);
                        let span = expr.span();
                        let head = std::mem::replace(&mut expr, SurfaceExpr::Hole(span));
                        let applied = self.expand_notation(&op.expansion, head.span(), &[head])?;
                        expr = SurfaceExpr::Paren(applied.span(), Box::new(applied));
                        head_is_notation = true;
                        continue;
                    }
                }
            }

            // Check for Dot FIRST - if followed by ident/number, it's a projection
            // If followed by {, it's universe instantiation (Foo.{u v})
            // Otherwise, let is_atom_start() handle it as anonymous constructor
            if self.check(&TokenKind::Dot) {
                // A dot is a projection only when adjacent to the previous
                // expression (no whitespace gap). `.notFound` after a space is a
                // new leading-dot constructor, not a projection on the preceding
                // expression. Without this check, `.error .notFound` would be
                // misparsed as `Proj(Ident(".error"), "notFound")` instead of
                // `App(Ident(".error"), Ident(".notFound"))`. (#3421)
                let dot_span = self.current_span();
                let prev_end = if let Some(last_arg) = pending_args.last() {
                    last_arg.expr.span().end
                } else {
                    expr.span().end
                };
                let dot_is_adjacent = dot_span.start == prev_end;
                let is_projection = dot_is_adjacent
                    && match self.peek_kind(1) {
                        Some(TokenKind::Ident(_) | TokenKind::NatLit(_)) => true,
                        Some(other) => other.as_keyword_str().is_some(),
                        None => false,
                    };
                let is_universe_inst =
                    dot_is_adjacent && matches!(self.peek_kind(1), Some(TokenKind::LBrace));

                if is_universe_inst {
                    self.advance(); // consume the dot
                    self.advance(); // consume the {

                    // Parse universe levels: `Foo.{u, v, w}` (Lean's canonical
                    // comma-separated form) — the space-separated `Foo.{u v w}`
                    // is also accepted (comma is optional).
                    let mut levels = Vec::new();
                    while !self.check(&TokenKind::RBrace) && !self.check(&TokenKind::Eof) {
                        levels.push(self.level_expr()?);
                        if self.check(&TokenKind::Comma) {
                            self.advance();
                        }
                    }
                    // Capture the CLOSING BRACE's own span (the line-399
                    // getElem pattern): `expect` advances, so a later
                    // `current_span()` is the FOLLOWING token — an
                    // over-extended span whose `end` defeats the byte-
                    // adjacency check for any postfix after `.{…}`
                    // (`X.{u}.ty` misparsed `.ty` as a leading-dot argument
                    // instead of a projection — refuter finding).
                    let end_span = self.expect(&TokenKind::RBrace)?.span;

                    // Like projection below, `.{…}` attaches to the LAST
                    // ARGUMENT when one is pending, not the application head:
                    // `@f PUnit.{u+1} x` instantiates `PUnit`, not `f` (the
                    // dot-adjacency check above already guarantees the levels
                    // hug the preceding atom). Head attachment only when there
                    // are no pending args (`Foo.{u v}` and `Foo.{u} x y`).
                    // Previously this always wrapped the head, silently
                    // re-leveling the FUNCTION — the U2 battery P14 bug.
                    if let Some(last_arg) = pending_args.pop() {
                        let span = last_arg.expr.span().merge(end_span);
                        let inst = SurfaceExpr::UniverseInst(span, Box::new(last_arg.expr), levels);
                        pending_args.push(SurfaceArg {
                            span,
                            expr: inst,
                            name: last_arg.name,
                        });
                    } else {
                        let span = expr.span().merge(end_span);
                        expr = SurfaceExpr::UniverseInst(span, Box::new(expr), levels);
                    }
                    continue;
                }

                if is_projection {
                    self.advance(); // consume the dot

                    // Projection attaches to the last argument, not the whole application.
                    // For `f x.y`, the projection `.y` attaches to `x`, giving `App(f, Proj(x, y))`,
                    // NOT `Proj(App(f, x), y)`.
                    let proj_base = if let Some(last_arg) = pending_args.pop() {
                        last_arg.expr
                    } else {
                        // No pending args - projection attaches to the base expression.
                        // Move current expr out, we'll replace it with the projection.
                        let span = expr.span();
                        std::mem::replace(&mut expr, SurfaceExpr::Hole(span))
                    };

                    let (projection, end_span) = match self.current_kind().clone() {
                        TokenKind::Ident(field) => {
                            let field = SurfaceName::component(field, self.current().ident_escaped);
                            let end_span = self.current_span();
                            self.advance();
                            (Projection::Named(field), end_span)
                        }
                        TokenKind::NatLit(n) => {
                            let end_span = self.current_span();
                            let index_line = self.current_line();
                            let index_col = end_span.start;
                            self.advance();
                            let idx = n.to_u64().and_then(|v| u32::try_from(v).ok()).ok_or_else(
                                || ParseError::UnexpectedToken {
                                    line: index_line,
                                    col: index_col,
                                    message: format!("projection index too large: {n}"),
                                },
                            )?;
                            (Projection::Index(idx), end_span)
                        }
                        other => {
                            if let Some(kw_str) = other.as_keyword_str() {
                                let end_span = self.current_span();
                                self.advance();
                                (
                                    Projection::Named(SurfaceName::component(kw_str, false)),
                                    end_span,
                                )
                            } else {
                                unreachable!("peek_kind already checked");
                            }
                        }
                    };

                    let proj_span = proj_base.span().merge(end_span);
                    let projected = SurfaceExpr::Proj(proj_span, Box::new(proj_base), projection);

                    // If we popped from pending_args, push the projected expr back.
                    // If we moved expr out (no pending args), put the projection there.
                    if matches!(&expr, SurfaceExpr::Hole(_)) {
                        expr = projected;
                    } else {
                        pending_args.push(SurfaceArg::positional(projected));
                    }
                    continue;
                }
                // If not a projection (e.g., `.` followed by something else),
                // fall through to is_atom_start() which will handle it as
                // anonymous constructor syntax if applicable
            }

            if self.stop_app_at_newline_lparen
                && matches!(self.current_kind(), TokenKind::LParen)
                && self.current().preceded_by_newline
            {
                break;
            }

            // Lean's `argument := checkWsBefore >> checkColGt …`
            // (`Lean/Parser/Term.lean:845-853`): a token at or left of the
            // saved position cannot be an argument. Inside a bracketed group
            // no position is saved (`withoutPosition`), so the check passes.
            if self.stop_app_at_newline_outer_indent
                && self.current().preceded_by_newline
                && !self.position_suppressed()
                && self
                    .indent_stack
                    .last()
                    .is_some_and(|col| self.current().col <= *col)
            {
                break;
            }

            // Stop collecting arguments at indentation boundaries (#1798).
            // When inside an indented block (e.g., a `by` tactic block),
            // a token on a new line whose column is less than the block's
            // reference column belongs to the outer block, not to this
            // application. Without this, `exact proof\n  exact h` would
            // parse as `exact (proof exact h)` instead of two separate tactics.
            if self.at_dedent() {
                break;
            }

            // Postfix ! (factorial / get-or-panic) — Part of #8, Part of #2550
            // In Lean 4, `!` after an expression is postfix (Nat.factorial or
            // getElem!) when the token AFTER `!` cannot start an expression.
            // This distinguishes `(n)!` (postfix) from `f ¬P` (prefix Not).
            if matches!(self.current_kind(), TokenKind::Not) {
                // Check if the token after `!` could start an expression
                // argument. Reuse the atom parser's start check so special
                // cases like `@f`, `do` under forbid_do, and error recovery
                // stay aligned without importing application-only stops like
                // termination hints.
                let next_could_be_arg = self.atom_expr_can_start_at(1)
                    || matches!(self.peek_kind(1), Some(TokenKind::Minus | TokenKind::Plus));
                if !next_could_be_arg {
                    let bang_span = self.current_span();
                    self.advance(); // consume !
                    let target = if let Some(last_arg) = pending_args.pop() {
                        last_arg.expr
                    } else {
                        let s = expr.span();
                        std::mem::replace(&mut expr, SurfaceExpr::Hole(s))
                    };
                    let result_span = target.span().merge(bang_span);
                    let bang_expr = SurfaceExpr::App(
                        result_span,
                        Box::new(SurfaceExpr::Ident(
                            bang_span,
                            SurfaceName::global_path("postfixBang"),
                        )),
                        vec![SurfaceArg::positional(target)],
                    );
                    if matches!(&expr, SurfaceExpr::Hole(_)) {
                        expr = bang_expr;
                    } else {
                        pending_args.push(SurfaceArg::positional(bang_expr));
                    }
                    continue;
                }
            }

            // Postfix `⁻¹` (group/field inverse `Inv.inv`). Attaches to the
            // immediately-preceding atom/application, exactly like the `!` bang
            // above. `x⁻¹` → `Inv.inv x` (Lean `postfix:max "⁻¹" => Inv.inv`).
            //
            // MAXIMAL MUNCH: `⁻¹` is also the PREFIX of a longer declared
            // symbol — `f ⁻¹' s` is `Set.preimage f s` (`infixl:80`,
            // `Mathlib/Data/Set/Operations.lean`), whose token sequence starts
            // with this very token. Lean resolves that from its token table by
            // longest match; consuming the inverse here first would strand the
            // trailing prime and lose the operator, so a registered operator
            // that matches at the cursor wins.
            if matches!(self.current_kind(), TokenKind::InvNotation)
                && !self.starts_custom_infix_or_postfix_at(0)
            {
                let inv_span = self.current_span();
                self.advance(); // consume ⁻¹
                let target = if let Some(last_arg) = pending_args.pop() {
                    last_arg.expr
                } else {
                    let s = expr.span();
                    std::mem::replace(&mut expr, SurfaceExpr::Hole(s))
                };
                let result_span = target.span().merge(inv_span);
                let inv_expr = SurfaceExpr::App(
                    result_span,
                    Box::new(SurfaceExpr::Ident(
                        inv_span,
                        SurfaceName::global_path("Inv.inv"),
                    )),
                    vec![SurfaceArg::positional(target)],
                );
                if matches!(&expr, SurfaceExpr::Hole(_)) {
                    expr = inv_expr;
                } else {
                    pending_args.push(SurfaceArg::positional(inv_expr));
                }
                continue;
            }

            // In a `show t by tac` type position, a `by` block is not an
            // application argument: it belongs to the `show` parser. Stop here
            // so `show_body` can dispatch the trailing `by` into a tactic block.
            if self.stop_app_at_by && matches!(self.current_kind(), TokenKind::By) {
                break;
            }

            // In an `induction e using r generalizing x` target position, the
            // `using`/`generalizing` clause keywords (plain identifier tokens to
            // the lexer) must NOT be consumed as application arguments to the
            // major premise `e`. Stop here so `parse_tactic_cases_induction` can
            // dispatch them into the recursor-override / generalizing clauses.
            if self.stop_app_at_generalizing_using
                && matches!(
                    self.current_kind(),
                    TokenKind::Ident(name) if name == "using" || name == "generalizing"
                )
            {
                break;
            }

            // GetElem indexing: `xs[i]`, `xs[i]!`, `xs[i]?`, `xs[i]'h`
            // (`Init/GetElem.lean:81-122`). A `[` byte-adjacent to the preceding
            // expression (no whitespace gap) is an index bracket, NOT a list
            // literal argument (`xs [i]` WITH a space stays application). Desugars
            // to `getElem xs i (by …)` / `getElem! xs i` / `getElem? xs i` /
            // `getElem xs i h`; the plain form's auto-proof is a `_` placeholder
            // (matching the parity fixture; the elaborator fills it).
            if matches!(self.current_kind(), TokenKind::LBracket) {
                let bracket_start = self.current_span().start;
                let prev_end = pending_args
                    .last()
                    .map_or_else(|| expr.span().end, |a| a.expr.span().end);
                if bracket_start == prev_end {
                    self.advance(); // consume `[`
                    let index = self.expr()?;
                    // The indexing target is the last-built argument (max-prec
                    // postfix), or the head expression when there are none.
                    let popped = pending_args.pop();
                    let target_from_arg = popped.is_some();
                    let target = match popped {
                        Some(last) => last.expr,
                        None => {
                            let s = expr.span();
                            std::mem::replace(&mut expr, SurfaceExpr::Hole(s))
                        }
                    };
                    let target_span = target.span();
                    let (head, third, end) = if self.check(&TokenKind::RBracketPrime) {
                        // `xs[i]'h` — explicit proof, `]'` one token. This form is
                        // lead-prec (not max), so it is illegal as a bare
                        // application argument (`Nat.succ l[1]'h` is a parse error).
                        if target_from_arg {
                            return Err(ParseError::UnexpectedToken {
                                line: self.current_line(),
                                col: self.current_span().start,
                                message: "`xs[i]'h` is not a max-precedence term \
                                          and cannot be a bare application argument \
                                          — parenthesize it `(xs[i]'h)`"
                                    .to_string(),
                            });
                        }
                        self.advance(); // consume `]'`
                        let proof = self.getelem_proof()?;
                        let end = proof.span();
                        ("getElem", Some(proof), end)
                    } else if self.check(&TokenKind::Colon) {
                        // Slice `xs[i:j]` / `xs[i:]` ⇒ `Array.toSubarray xs i [j]`
                        // (`Array.toSubarray (as) (start := 0) (stop := as.size)`,
                        // Init/Data/Array/Subarray.lean). The start index `i` was
                        // already parsed above. The empty-start forms `xs[:j]` /
                        // `xs[:]` are not produced here (the index parse consumed a
                        // start) — they remain a loud parse error until supported.
                        self.advance(); // consume `:`
                        if self.check(&TokenKind::RBracket) {
                            // `xs[i:]` — stop defaults to `as.size` (optParam).
                            let rb = self.expect(&TokenKind::RBracket)?.span;
                            ("Array.toSubarray", None, rb)
                        } else {
                            // `xs[i:j]`
                            let stop = self.expr()?;
                            let rb = self.expect(&TokenKind::RBracket)?.span;
                            ("Array.toSubarray", Some(stop), rb)
                        }
                    } else {
                        let rb_span = self.expect(&TokenKind::RBracket)?.span;
                        let rb_end = rb_span.end;
                        if matches!(self.current_kind(), TokenKind::Not)
                            && self.current_span().start == rb_end
                        {
                            let e = self.current_span();
                            self.advance();
                            ("getElem!", None, e)
                        } else if matches!(self.current_kind(), TokenKind::Question)
                            && self.current_span().start == rb_end
                        {
                            let e = self.current_span();
                            self.advance();
                            ("getElem?", None, e)
                        } else {
                            ("getElem", Some(SurfaceExpr::Hole(rb_span)), rb_span)
                        }
                    };
                    let full = target_span.merge(end);
                    let mut args = vec![
                        SurfaceArg::positional(target),
                        SurfaceArg::positional(index),
                    ];
                    if let Some(proof) = third {
                        args.push(SurfaceArg::positional(proof));
                    }
                    let getelem = SurfaceExpr::App(
                        full,
                        Box::new(SurfaceExpr::Ident(
                            target_span,
                            SurfaceName::global_path(head),
                        )),
                        args,
                    );
                    if target_from_arg {
                        pending_args.push(SurfaceArg::positional(getelem));
                    } else {
                        expr = getelem;
                    }
                    continue;
                }
            }

            // Lean `Term.ellipsis` (`Lean/Parser/Term.lean`): a trailing `..`
            // in ARGUMENT position means "fill every remaining explicit
            // parameter of the head with `_`" — `Subsingleton.elim ..`,
            // `inferInstanceAs (Decidable (Or ..))`, `elim_le_elim_iff ..`.
            // The parser cannot know the arity, so it records the marker and
            // `Elaborator::expand_app_ellipsis` expands it against the
            // inferred function type.
            //
            // `..` is overloaded three ways in this grammar, so the guards
            // below are load-bearing, not defensive:
            //
            //   * the RANGE operator `a..b` (`Set.Icc`, handled in
            //     expr_operators.rs) — excluded by requiring the NEXT token
            //     not to start an atom, so `a .. b` and `a..b` still reach the
            //     operator chain untouched;
            //   * `structInst`'s `optEllipsis` `{ x := y, .. }` and the
            //     structure-PATTERN ellipsis `{ le := A_le, .. }` — excluded
            //     by refusing a `..` that sits immediately before `}`, which
            //     is where both of those always appear. Lean resolves that
            //     position as the structure ellipsis too.
            //
            // Requiring whitespace before `..` mirrors Lean's own
            // `checkWsBefore` on `argument`, and keeps `f..g` (never an
            // ellipsis) out of this branch.
            if self.check(&TokenKind::DotDot) {
                let dot_span = self.current_span();
                let prev_end = pending_args
                    .last()
                    .map_or_else(|| expr.span().end, |last| last.expr.span().end);
                let ws_before = dot_span.start > prev_end;
                let next_starts_atom = self.is_atom_start_at(1);
                let next_is_rbrace = matches!(self.peek_kind(1), Some(TokenKind::RBrace));
                if ws_before && !next_starts_atom && !next_is_rbrace {
                    self.advance();
                    pending_args.push(SurfaceArg::ellipsis(dot_span));
                    // Lean's `..` is always the LAST argument.
                    break;
                }
                // Not an application ellipsis — leave the token for the range
                // operator / structInst / pattern parsers exactly as before.
                break;
            }

            if self.is_atom_start() {
                // Argument position is max precedence: `Type` is atomic here.
                self.type_atomic_in_arg = true;
                let mut arg = self.atom_expr()?;
                self.type_atomic_in_arg = false;
                // A user/imported `postfix:max` operator binds to the argument
                // ATOM, as in Lean: `Std.Irrefl rᶜ` is `Std.Irrefl (rᶜ)`. The
                // loosest-position postfix handling in `custom_notation.rs`
                // applied it to the whole application instead
                // (`Compl.compl (Std.Irrefl r)`, three instance rows in
                // `Mathlib/Order/Basic.lean`, measured 2026-09-11). Only
                // max-precedence postfixes bind here; lower ones keep their
                // outer position.
                if self.has_custom_operators() {
                    while let Some(op) = self.match_custom_operator(NotationKind::Postfix) {
                        if op.precedence < MAX_PREC {
                            break;
                        }
                        self.consume_custom_operator(&op);
                        arg = self.expand_notation(&op.expansion, arg.span(), &[arg])?;
                    }
                }

                // If the argument is a pattern-matching lambda, stop application parsing
                // Pattern-matching lambdas use layout-sensitive syntax and we can't
                // reliably determine where they end without indentation info
                let is_pattern_lambda = matches!(&arg, SurfaceExpr::PatternMatchLambda(_, _, _));

                // If the atom is a named argument (name := expr), propagate the
                // name through SurfaceArg so elab_app can match by name (#1230).
                let surface_arg = if let SurfaceExpr::NamedArg(_, ref name, ref inner) = arg {
                    SurfaceArg::named(name.clone(), (**inner).clone())
                } else {
                    SurfaceArg::positional(arg)
                };
                pending_args.push(surface_arg);

                if is_pattern_lambda {
                    // Stop collecting arguments after pattern-matching lambda
                    break;
                }
                continue;
            }

            break;
        }

        if pending_args.is_empty() {
            // A notation head with nothing applied to it needs no grouping:
            // hand back the bare notation term, exactly the shape the
            // loosest-position postfix loop produced before.
            if head_is_notation {
                if let SurfaceExpr::Paren(_, inner) = expr {
                    return Ok(*inner);
                }
            }
            Ok(expr)
        } else {
            let span = expr.span();
            let app = SurfaceExpr::App(span, Box::new(expr), pending_args);
            if let Some(origins) = &mut self.origins {
                origins.application(&app);
            }
            Ok(app)
        }
    }

    /// Parse the proof term after `xs[i]'` — a Lean `term:max`, i.e. an atom
    /// plus any byte-adjacent projection chain (`h`, `h'`, `(by decide)`, `h.1`),
    /// but NOT an application (`xs[1]'h y` leaves `y` for the enclosing loop).
    fn getelem_proof(&mut self) -> Result<SurfaceExpr, ParseError> {
        let mut e = self.atom_expr()?;
        loop {
            if !self.check(&TokenKind::Dot) || self.current_span().start != e.span().end {
                break;
            }
            let projects = match self.peek_kind(1) {
                Some(TokenKind::Ident(_) | TokenKind::NatLit(_)) => true,
                Some(other) => other.as_keyword_str().is_some(),
                None => false,
            };
            if !projects {
                break;
            }
            self.advance(); // consume `.`
            let (proj, end) = self.pipe_proj_field()?;
            e = SurfaceExpr::Proj(e.span().merge(end), Box::new(e), proj);
        }
        Ok(e)
    }

    pub(super) fn is_atom_start(&self) -> bool {
        self.is_atom_start_at(0)
    }

    fn kind_at(&self, offset: usize) -> Option<&TokenKind> {
        self.tokens.get(self.pos + offset).map(|t| &t.kind)
    }

    fn atom_expr_can_start_at(&self, offset: usize) -> bool {
        let Some(current_kind) = self.kind_at(offset) else {
            return false;
        };

        // Note: SetOption is NOT here because `set_option` should not be
        // considered an application argument. It appears at expression-start
        // only in the form `set_option ... in expr`, which is handled by
        // atom_expr() directly, but should not be consumed as an argument
        // to a preceding function call.

        // Special case: @ followed by identifier is explicit application (@f),
        // but @ followed by [ is an attribute (@[...])
        if matches!(current_kind, TokenKind::At) {
            return matches!(self.kind_at(offset + 1), Some(TokenKind::Ident(_)));
        }

        // Special case: `#[` is an array literal — a valid atom, hence a valid
        // application argument (`Array.size #[1, 2, 3]`, `Array.foldl f init
        // #[..]`). A bare `#` otherwise begins a top-level command (`#check`,
        // `#eval`, `#[...]` attribute-less command forms) that must NOT be
        // consumed as an argument. `atom_expr()` already dispatches `#[` to
        // `array_literal_body`; without recognizing it here the app-argument loop
        // stopped at `#`, leaving the head unapplied (`Array.size` elaborated as
        // the un-applied `Array ?α → Nat`, surfacing as a misleading universe
        // `Array {u} fvar` TypeMismatch downstream). List literals `[..]` were
        // always accepted here; this closes the array-literal parity gap.
        if matches!(current_kind, TokenKind::Hash) {
            return matches!(self.kind_at(offset + 1), Some(TokenKind::LBracket));
        }

        // Special case: when forbid_do is set, `do` is not an atom start.
        // Used by parse_do_for to prevent the collection expression from consuming
        // the `do` keyword that delimits the loop body. (#1808)
        if self.forbid_do && matches!(current_kind, TokenKind::Do) {
            return false;
        }

        Self::is_plain_atom_start(current_kind)
    }

    pub(super) fn is_atom_start_at(&self, offset: usize) -> bool {
        let Some(current_kind) = self.kind_at(offset) else {
            return false;
        };

        // Special case: termination_by, termination_by?, and decreasing_by are NOT atoms
        // when they appear after a definition body. They are termination hint keywords
        // that should terminate expression parsing so they can be parsed by
        // parse_termination_hints() in decl.rs. Without this check, the expression
        // parser consumes them as function arguments. (#1132)
        if matches!(
            current_kind,
            TokenKind::Ident(name) if Self::is_termination_hint_name(name)
        ) {
            return false;
        }

        // Special case: a term Lean parses at `leadPrec` never starts an
        // ARGUMENT. An application argument parses at `argPrec`
        // (`Lean/Parser/Term.lean`, `argument`), above `leadPrec`, so a
        // leading parser declared at `leadPrec` — or a non-atom-like
        // `syntax`/`macro` with no precedence, which defaults to it
        // (`Lean/Elab/Syntax.lean`, `precDefault`) — cannot be one. See
        // [`Self::starts_lead_prec_term_at`] for the tokens and the pinned
        // Lean refusals. `atom_expr_inner` serves both positions, so the
        // argument loops, which all ask here first, must stop at them.
        if self.starts_lead_prec_term_at(offset) {
            return false;
        }

        // Special case: a contextual top-level COMMAND keyword (`alias`,
        // `library_note`, `declare_aesop_rule_sets`, `declare_syntax_cat`,
        // `initialize_simps_projections`) is a soft keyword lexed as `Ident`.
        // When it begins a new line it starts the NEXT top-level command and
        // must terminate the preceding declaration-value expression — otherwise
        // `def x := 0` followed by `alias y := x` parses the value as the
        // application `0 alias y` (Nat applied to two args), and the `alias`
        // line then collapses to an error-recovery raw declaration. Distinct
        // decl-keyword tokens (`def`/`theorem`/…) are already rejected by
        // `is_plain_atom_start`; these soft keywords need the explicit check.
        // Gated on a line boundary (like the where-def / field-type checks
        // below) so a same-line identifier of the same spelling is never
        // mistaken for a command boundary. Fixes ~26 alias-cascade failures on
        // Mathlib/Logic/Basic (the `em`/`dec_em`/`by_contra` unknown-idents were
        // downstream of the swallowed `alias … := …` registrations).
        if matches!(
            current_kind,
            TokenKind::Ident(name) if Self::is_boundary_command_keyword(name)
        ) && self
            .tokens
            .get(self.pos + offset)
            .is_some_and(|t| t.preceded_by_newline)
        {
            return false;
        }

        // Special case: `local` is a soft keyword lexed as `Ident`. At the
        // start of a line it starts the NEXT command: `local instance i3 : C
        // := ⟨3⟩` followed by `local instance i4 : C := ⟨4⟩` used to parse the
        // first value as the application `⟨3⟩ local …` ("Too many
        // arguments"), refusing a file Lean 4.8.0 accepts (round-25 random
        // battery). See [`Self::starts_local_command_at`].
        if self.starts_local_command_at(offset) {
            return false;
        }

        // Special case: a line-start `meta` starts the NEXT command (plan item
        // `formats-module-spelling-refusals`). See
        // [`Self::starts_meta_command_at`].
        if self.starts_meta_command_at(offset) {
            return false;
        }

        // Special case: `catch` and `finally` are not atoms inside a try body.
        // Without this, `do try pure 1 catch e => pure 0` parses `catch` as an
        // argument to `pure 1` instead of a clause boundary. (#2969)
        if self.stop_at_catch_finally
            && matches!(
                current_kind,
                TokenKind::Ident(name) if name == "catch" || name == "finally"
            )
        {
            return false;
        }

        // Special case: inside a where-definition block, an identifier that
        // starts a new where-definition (ident ... :=) is NOT an atom.
        // Without this, `x := 1\n  y := 2` would parse `1 y` as application
        // in the body of `x`, consuming `y` as an argument.
        //
        // A new where-definition must START A LINE (Lean separates `where`
        // decls by indentation — `sepByIndent letRecDecl`,
        // `Lean/Parser/Term.lean:701-703`). Without the line-start
        // requirement, the `:=`-lookahead alone cuts APPLICATION ARGUMENTS
        // out of the previous body: in `a (m : Nat) : Nat := b m\n
        // b (m : Nat) : Nat := m + 1`, the argument `m` of `b m` is followed
        // (three tokens later, inside the NEXT definition) by `:=`, so it was
        // mistaken for a def start — truncating `a`'s body to `b` and
        // mangling the next header into `m (…)`.
        if self.in_where_block
            && matches!(current_kind, TokenKind::Ident(_))
            && self
                .tokens
                .get(self.pos + offset)
                .is_some_and(|t| t.preceded_by_newline)
            && self.peek_is_where_def_start(offset)
        {
            return false;
        }

        // Special case: inside a struct-literal field value, an identifier
        // immediately followed by `:=` marks the start of the next field
        // assignment and is NOT an atom. Without this, the comma-less Lean 4
        // style `{ x := 1 y := 2 }` would parse the value of `x` as `1 y`
        // (application) and consume `y` as a function argument. See #3517.
        if self.in_struct_field
            && matches!(current_kind, TokenKind::Ident(_))
            && self.kind_at(offset + 1) == Some(&TokenKind::ColonEq)
        {
            return false;
        }

        // Special case: inside an instance `where`-field value, an identifier
        // immediately followed by `:=` marks the start of the next field
        // assignment and is NOT an atom. This is what bounds a `fun .. => body`
        // field value, whose body is parsed via the general `expr` grammar:
        // `render := fun _ => Nat.succ Nat.zero` followed by `tag := 3` would
        // otherwise parse the body as `fun _ => Nat.succ Nat.zero tag` and drop
        // the `tag` field. Mirrors `in_struct_field`. See B53.
        if self.in_instance_field && matches!(current_kind, TokenKind::Ident(_)) {
            // `ident :=` — the single-token field boundary (any position).
            if self.kind_at(offset + 1) == Some(&TokenKind::ColonEq) {
                return false;
            }
            // `ident binders… :=` — a field defined with method binders
            // (`g x := …`). Require the field NAME to be newline-leading (fields
            // start on their own line) so a value's own application arguments —
            // never a field's `name binders… :=` shape at a line start — are not
            // mistaken for the next field. `field_assign_at` additionally keeps
            // the binders same-line. Fixes multi-field instance/structure bodies
            // whose fields take binders (`f x := …` then `g x := …`).
            let at = self.pos + offset;
            if self.tokens.get(at).is_some_and(|t| t.preceded_by_newline)
                && self.field_assign_at(at)
            {
                return false;
            }
        }

        // Special case: inside a structure/class field TYPE, an identifier that
        // begins a NEW LINE and is immediately followed by `:` is the next
        // field's name — it bounds the current field's type spine, not an
        // application argument or an operator's right operand. Because field
        // types are parsed with the full operator grammar (so `h : n = n`,
        // `property : 0 < val`, … work), this replaces the old app+arrow-only
        // `field_app_expr`'s field-boundary break. The newline requirement is
        // what keeps a same-line `(f x : T)` ascription / `(x y : T)` binder
        // group inside a field type intact (`x`/`y` are not newline-leading, so
        // they are never mistaken for the next field), matching Lean's
        // layout-sensitive `structExplicitBinder`. See brick B11.
        if self.in_field_type
            && matches!(current_kind, TokenKind::Ident(_))
            && self
                .tokens
                .get(self.pos + offset)
                .is_some_and(|t| t.preceded_by_newline)
            && matches!(
                self.kind_at(offset + 1),
                Some(TokenKind::Colon | TokenKind::ColonEq)
            )
        {
            return false;
        }
        // SAME-LINE next field: `structure Point where x : Nat y : Nat`. At the
        // TOP level of a field type a bare `ident :` cannot continue the current
        // type (a naked ascription is not an expression outside delimiters), so
        // it must be the next field's name — the newline requirement above was
        // over-conservative and made single-line multi-field structures parse
        // `Nat y` as an application (`TooManyArguments` + a parser-recovery raw
        // decl; pinned by `test_issue173_simple_structure_still_works`). Gated
        // on `field_delim_depth == 0` so everything the newline rule's comment
        // protects — `(f x : T)` ascriptions, `(x y : T)` binder groups — stays
        // inside its delimiter, where this arm never fires. `Colon` only:
        // a same-line `ident :=` is a default value, not a field boundary.
        if self.in_field_type
            && self.field_delim_depth == 0
            && matches!(current_kind, TokenKind::Ident(_))
            && matches!(self.kind_at(offset + 1), Some(TokenKind::Colon))
        {
            return false;
        }

        // NEXT PAREN FIELD GROUP: inside a `where` block a NEWLINE-LEADING
        // `(x… : T)` at the top level of a field type is the next
        // parenthesized field-binder group (`structure P where a : Nat
        // ⏎ (b c : Nat)`), not an application argument — the exact mirror of
        // the newline-leading `ident :` arm above, for the group spelling.
        // Without it the group is swallowed into the previous field's type as
        // `Nat (b c : Nat)`. The newline gate keeps a same-line `(f x : T)`
        // ascription argument intact; the depth gate keeps groups inside
        // delimiters intact. (A newline-leading `(f x : T)` ascription used as
        // a continuation argument is the shape Lean's colGt layout rule also
        // refuses at field indentation, so the boundary reading is the
        // Lean-faithful one.)
        if self.in_field_type
            && self.field_delim_depth == 0
            && matches!(self.kind_at(offset), Some(TokenKind::LParen))
            && self
                .tokens
                .get(self.pos + offset)
                .is_some_and(|t| t.preceded_by_newline)
        {
            let mut j = offset + 1;
            while matches!(self.kind_at(j), Some(TokenKind::Ident(_))) {
                j += 1;
            }
            if j > offset + 1 && matches!(self.kind_at(j), Some(TokenKind::Colon)) {
                return false;
            }
        }

        // A token that begins a user-declared infix/postfix operator (e.g. an
        // `Ident("~>")` symbol) is an operator, not an application argument.
        // Without this, `a ~> b` would parse as the application `a (~>) b`
        // before `custom_op_expr`'s operator loop could match the symbol. Only
        // consulted when the file actually declared operators, so existing
        // parses are unaffected.
        if self.starts_custom_infix_or_postfix_at(offset) {
            return false;
        }

        self.atom_expr_can_start_at(offset)
    }

    fn is_termination_hint_name(name: &str) -> bool {
        matches!(name, "termination_by" | "termination_by?" | "decreasing_by")
    }

    /// Whether the token at `offset` is an unescaped `local` that begins a
    /// line: Lean's `attrKind` keyword, which starts the next command (`local
    /// instance`, `local notation`, …), never an argument of the term before
    /// it.
    ///
    /// Every world Clean reads reserves it: v4.8.0, v4.30.0-rc2 and v4.33.1
    /// refuse `def local : Nat := 1` ("unexpected token 'local'; expected
    /// identifier"), and read `def y : Nat := f 1` followed by a `local
    /// instance …` line as two commands (measured 2026-10-25). This used to
    /// require a command keyword Clean lexes as a token after `local`, so the
    /// term before a `local notation3` or `local grind_pattern` line (Mathlib),
    /// or before the refused `local import` / `local section` / `local
    /// variable` (`tests/fixtures/module_spellings/modifier_matrix.tsv`), took
    /// `local` as an argument. The command after it is the dispatcher's
    /// (`decl::mod`'s `local` arm).
    pub(in crate::grammar) fn starts_local_command_at(&self, offset: usize) -> bool {
        self.tokens.get(self.pos + offset).is_some_and(|token| {
            matches!(&token.kind, TokenKind::Ident(name) if name == "local")
                && token.preceded_by_newline
                && !token.ident_escaped
        })
    }

    /// Whether the token at `offset` is an unescaped `meta` that begins a
    /// line: the module system's phase modifier, which starts the next
    /// command, never an argument of the term before it.
    ///
    /// The module system made `meta` a token. Pinned v4.30.0-rc2, v4.28.0,
    /// v4.32.1 and v4.33.1 refuse `def meta : Nat := 1` ("unexpected token
    /// 'meta'; expected identifier"). They read `def y : Nat := 1` followed
    /// by a `meta def z : Nat := 2` line as two declarations; Clean read the
    /// application `1 meta`, so `y` failed and the matrix rows that start with
    /// `meta` (`tests/fixtures/module_spellings/modifier_matrix.tsv`) were
    /// never at a command (measured 2026-10-25). Lean 4.8.0 still takes `meta`
    /// as an identifier, and every parse is at the Oracle
    /// (`crate::parse_world`). An escaped `«meta»` stays an identifier, as it
    /// does in Lean. Only a line-start `meta` is covered, like the soft command
    /// keywords: a same-line `1 meta def z` is still an application here,
    /// where Lean ends the term.
    pub(in crate::grammar) fn starts_meta_command_at(&self, offset: usize) -> bool {
        self.tokens.get(self.pos + offset).is_some_and(|token| {
            matches!(&token.kind, TokenKind::Ident(name) if name == "meta")
                && token.preceded_by_newline
                && !token.ident_escaped
        })
    }

    /// Contextual top-level command keywords that are lexed as `Ident` (soft
    /// keywords) and, at a line boundary, terminate a preceding declaration
    /// value expression. Kept in sync with the `Ident(name) if name == …`
    /// command dispatches in `decl/mod.rs`. The modifiers `local` and `meta`
    /// end a term the same way, in [`Self::starts_local_command_at`] and
    /// [`Self::starts_meta_command_at`].
    pub(in crate::grammar) fn is_boundary_command_keyword(name: &str) -> bool {
        // `include` / `omit` are reserved tokens in pinned Lean v4.30.0-rc2
        // (`def include : Nat := 1` is "unexpected token 'include'", and even
        // an indented `omit` ends the term before it). Clean lexes them as
        // identifiers, so without them here `theorem u : True := t 5`
        // followed by an `omit n` line parsed as the application `t 5 omit
        // n`: the `omit` never ran, and `u` failed with "2 argument(s)
        // remain".
        matches!(
            name,
            "include"
                | "omit"
                | "alias"
                | "grind_pattern"
                | "init_grind_norm"
                | "library_note"
                | "declare_aesop_rule_sets"
                | "declare_syntax_cat"
                | "initialize_simps_projections"
                | "initialize_simps_projections?"
        )
    }

    /// Peek ahead from `offset` to determine if the current position starts a
    /// where-clause local definition: `ident binders? (: ty)? :=`.
    ///
    /// Scans forward (without consuming) looking for `:=` before hitting a
    /// boundary (EOF, declaration start, `where` keyword). Returns true if
    /// `:=` is found, indicating this identifier is the start of a new where-def
    /// rather than a function argument in the current body expression.
    pub(in crate::grammar) fn peek_is_where_def_start(&self, offset: usize) -> bool {
        // Start after the identifier at `offset`
        let mut i = offset + 1;
        let mut depth: usize = 0;

        loop {
            let Some(kind) = self.kind_at(i) else {
                return false;
            };
            match kind {
                // Found := at depth 0 -- this is a where-def start
                TokenKind::ColonEq if depth == 0 => return true,
                // A `|` at depth 0 marks an EQUATION-form where-helper
                // (`g (binders)? (: T)? | pat => body …`), whose body starts with
                // `|` instead of `:=`. Without this, a multi-helper `where` block
                // whose helpers are defined by pattern-matching equations
                // (`f : Nat → Bool | 0 => … | _ => …` then `g : …`) never bounds
                // the first helper's last arm body, swallowing the next helper.
                // A `:=`-form helper's `:=` is reached first, so this never
                // pre-empts it (types do not contain a bare `|` at depth 0).
                TokenKind::Pipe if depth == 0 => return true,
                // Track bracket nesting to skip binder contents
                TokenKind::LParen | TokenKind::LBrace | TokenKind::LBracket => depth += 1,
                TokenKind::RParen | TokenKind::RBrace | TokenKind::RBracket => {
                    depth = depth.saturating_sub(1);
                }
                // Hit a boundary before finding := -- not a where-def
                TokenKind::Eof | TokenKind::End | TokenKind::Where => return false,
                // If we see a declaration keyword at depth 0, stop
                _ if depth == 0 && Self::is_decl_keyword_token(kind) => return false,
                _ => {}
            }
            i += 1;
            // Safety limit
            if i > offset + 50 {
                return false;
            }
        }
    }

    /// Check if a token kind is a declaration keyword that terminates where-def scanning.
    fn is_decl_keyword_token(kind: &TokenKind) -> bool {
        matches!(
            kind,
            TokenKind::Def
                | TokenKind::Theorem
                | TokenKind::Lemma
                | TokenKind::Axiom
                | TokenKind::Example
                | TokenKind::Inductive
                | TokenKind::Codata
                | TokenKind::Codef
                | TokenKind::Structure
                | TokenKind::Class
                | TokenKind::Instance
                | TokenKind::Import
                | TokenKind::Namespace
                | TokenKind::Section
        )
    }

    /// Whether the token at `offset` begins a term Lean 4.8 parses at
    /// `leadPrec`, which no application argument (`argPrec`) can be.
    ///
    /// Every one is refused in argument position by pinned Lean 4.8.0 (`id ∃ x
    /// : Nat, x = x`, `id ∀ …`, `id exists …`, `id Σ x : Nat, Fin x`, `id Σ'
    /// …`, `id if True then 1 else 2`, `id match 1 with | _ => 2`, `id show
    /// Nat from 1`, `id by trivial`: "type mismatch `id`" then "unexpected
    /// token"), and each is taken parenthesized or after `<|`. `∃!` is
    /// Mathlib's `macro "∃!" xs:explicitBinders ", " b:term : term`, the same
    /// shape as `exists`. `let`/`have`/`suffices` never reach the argument
    /// test (not in [`Self::is_plain_atom_start`]); `fun`/`λ` (`maxPrec`),
    /// `do` (`argPrec`) and `¬` (`notation:max`) are arguments in Lean too.
    /// Not covered: Mathlib's big operators (`∑`, `∏`, `⨆`, `⨅`, `∫`, `⨍`,
    /// `⋃`, `⋂`) and `Π`, whose precedences the pinned core toolchain cannot
    /// state; they stay arguments here.
    fn starts_lead_prec_term_at(&self, offset: usize) -> bool {
        let Some(token) = self.tokens.get(self.pos + offset) else {
            return false;
        };
        match &token.kind {
            TokenKind::Exists
            | TokenKind::ExistsUnique
            | TokenKind::Forall
            | TokenKind::Sigma
            | TokenKind::PSigma
            | TokenKind::If
            | TokenKind::Match
            | TokenKind::Show
            | TokenKind::By => true,
            // The ASCII `exists` binder (`expr_exists_kw.rs`): a keyword only
            // when not escaped.
            TokenKind::Ident(name) => {
                token.lean_keyword && !token.ident_escaped && name == "exists"
            }
            _ => false,
        }
    }

    fn is_plain_atom_start(current_kind: &TokenKind) -> bool {
        matches!(
            current_kind,
            TokenKind::Ident(_)
                | TokenKind::NatLit(_)
                | TokenKind::FloatLit(_)
                | TokenKind::CharLit(_)
                | TokenKind::StringLit(_)
                | TokenKind::InterpolatedString(_, _)
                | TokenKind::LParen
                | TokenKind::Type
                | TokenKind::Prop
                | TokenKind::Sort
                | TokenKind::Top    // ⊤ lattice top
                | TokenKind::Bot    // ⊥ lattice bottom
                | TokenKind::EmptySet // ∅ empty collection
                | TokenKind::Underscore
                | TokenKind::LAngle  // ⟨...⟩ anonymous constructor
                | TokenKind::LDAngle // ⟪...⟫ inner product
                | TokenKind::LFrench // ‹P› anonymous hypothesis
                | TokenKind::Not     // ¬ prefix operator
                | TokenKind::By      // by tactic
                | TokenKind::Sorry   // sorry
                | TokenKind::Rfl     // rfl
                | TokenKind::Match   // match expression
                | TokenKind::Do      // do notation
                | TokenKind::Exists  // ∃ exists
                | TokenKind::ExistsUnique // ∃! unique exists
                | TokenKind::Show    // show ... from ...
                | TokenKind::Dot    // .foo anonymous constructor as argument (#3421)
                // Note: Open is NOT included - `open` at start of line is a declaration,
                // not an expression argument. Use parentheses: f (open Foo in x)
                | TokenKind::LBrace  // record literals
                | TokenKind::LBracket // [a, b] list literals
                // Note: Hash is NOT included - `#foo` commands should only appear at declaration level,
                // not as expression arguments. Only `#[...]` array literals are valid in expressions,
                // but we handle that specially by checking for `#` followed by `[`
                | TokenKind::Fun     // fun x => ... lambdas
                | TokenKind::Lambda  // λ x => ... lambdas
                | TokenKind::If      // if ... then ... else ...
                // Note: Let is NOT included - let expressions cannot be bare function arguments
                // They must be parenthesized: f (let x := 1 in x)
                | TokenKind::Forall  // ∀ forall
                | TokenKind::Pi      // Π pi type
                | TokenKind::Sigma   // Σ sigma dependent-pair type
                | TokenKind::PSigma  // Σ' psigma dependent-pair type
                | TokenKind::BigSum  // ∑ big sum
                | TokenKind::BigProd // ∏ big product
                | TokenKind::BigSup  // ⨆ indexed supremum (iSup)
                | TokenKind::BigInf  // ⨅ indexed infimum (iInf)
                | TokenKind::Integral // ∫ integral
                | TokenKind::FintAvg // ⨍ average integral
                | TokenKind::BigUnion // ⋃ big union
                | TokenKind::BigInter // ⋂ big intersection
                | TokenKind::Cdot    // · section placeholder
                // Note: Dot already covered above (#3421)
                | TokenKind::SyntaxQuote(_)
                | TokenKind::Question // ?_, ?name synthetic hole (refine goals)
                | TokenKind::Error(_) // Allow error recovery to parse invalid characters
        )
    }

    /// Check if current position looks like the start of a pi-type binder.
    /// Uses lookahead to distinguish binders from list/tuple literals.
    /// This avoids expensive speculative parsing that caused O(2^n) behavior.
    ///
    /// Patterns that look like binders:
    /// - `(x :` or `(x y :` - explicit binder with type annotation
    /// - `(x)` followed by `→` - simple binder (rare, handled by backtrack)
    /// - `{x :` - implicit binder
    /// - `[Name` where Name starts uppercase - instance binder like [Ord A]
    /// - `[x :` - named instance binder
    ///
    /// Patterns that are NOT binders:
    /// - `[[` - nested list literal
    /// - `[1` or `["` - list with literal element
    /// - `((` - nested parentheses (might be tuple)
    pub(super) fn looks_like_binder_start(&self) -> bool {
        let curr = self.current_kind();
        let next = self.tokens.get(self.pos + 1).map(|t| &t.kind);

        // `⦃x : T⦄ → …` — a unicode strict-implicit binder always starts a Pi.
        if matches!(curr, TokenKind::StrictLBrace) {
            return true;
        }

        match (curr, next) {
            // `((` - nested parens, likely not a binder
            // `()` - unit, not a binder
            // `(` followed by literal - tuple, not binder
            // `{{` - nested braces, not a binder
            // `{}` - empty, not a binder
            // `[[` - nested list literal, NOT a binder
            // `[]` - empty list, not a binder
            // `[number` or `[string` - list literal
            (
                TokenKind::LParen,
                Some(
                    TokenKind::LParen
                    | TokenKind::RParen
                    | TokenKind::NatLit(_)
                    | TokenKind::FloatLit(_)
                    | TokenKind::CharLit(_)
                    | TokenKind::StringLit(_)
                    | TokenKind::InterpolatedString(_, _),
                ),
            )
            | (TokenKind::LBrace, Some(TokenKind::LBrace | TokenKind::RBrace))
            | (
                TokenKind::LBracket,
                Some(
                    TokenKind::LBracket
                    | TokenKind::RBracket
                    | TokenKind::NatLit(_)
                    | TokenKind::FloatLit(_)
                    | TokenKind::CharLit(_)
                    | TokenKind::StringLit(_)
                    | TokenKind::InterpolatedString(_, _),
                ),
            ) => false,

            // `(x` where x is an identifier - could be binder
            // `(` followed by other - might be binder
            // `{x` where x is an identifier - likely implicit binder
            // `{` followed by other - might be binder
            (TokenKind::LParen | TokenKind::LBrace, Some(TokenKind::Ident(_)) | _) => true,

            // `[Name` where Name starts uppercase — likely an anonymous instance
            // binder like `[Ord A]`; OR `[inst : C]` — a NAMED instance binder,
            // detected by a `:` after the identifier. Without the named case,
            // `[inst : Add Nat] → Nat` fell through to a (malformed) list literal
            // instead of an instance-implicit Pi (audit B3-instbinder-arrow).
            (TokenKind::LBracket, Some(TokenKind::Ident(name))) => {
                name.chars().next().is_some_and(char::is_uppercase)
                    || self.peek_kind(2) == Some(&TokenKind::Colon)
            }
            // `[` followed by lowercase ident - ambiguous, could be list or binder
            // Be conservative: only try binder if followed by `:` pattern
            (TokenKind::LBracket, _) => {
                // Check if there's a colon within the next few tokens
                // This is a heuristic to avoid exponential behavior
                for i in 1..=4 {
                    match self.tokens.get(self.pos + i).map(|t| &t.kind) {
                        Some(TokenKind::Colon) => return true,
                        Some(TokenKind::RBracket | TokenKind::LBracket | TokenKind::Comma) => {
                            return false
                        }
                        _ => {}
                    }
                }
                false
            }

            // Bare identifiers are NOT binders in arrow_expr context
            // The original code only tried binders for ( { [
            // `A → B` should parse as Arrow, not Pi with untyped binder
            _ => false,
        }
    }

    /// Check if current token can implicitly start a let body
    /// This is for handling layout-sensitive code where the body follows
    /// without an explicit `in` separator
    pub(super) fn is_implicit_body_start(&self) -> bool {
        // Identifiers and parenthesized expressions can implicitly start a body.
        // Quantifiers (∃, ∀) are included for PutnamBench letI chains where
        // the body starts with an existential on the next line.
        // Part of #8, Part of #2550.
        //
        // `match`/`fun`/`λ`/`do`/`by` start a full expression too. Without them,
        // the pervasive `let x := v \n match … with …` shape (every `semIntBinOp`/
        // `semUnOp`/`semOverflowOp` in trust-ir's `Semantics/Arith.lean`, and the
        // bulk of `Eval`/`Step`/`Compare`) hit the "expected `in` or `;`" error
        // because the `match` after a chained `let` was not recognised as the
        // implicit body. (Track EF)
        matches!(
            self.current_kind(),
            TokenKind::Ident(_)
                | TokenKind::LParen
                // An explicit application may follow a local declaration on
                // the next line, including the body of `let rec` equations.
                | TokenKind::At
                // `{ …` opens a struct-update / structure literal / set literal
                // (`{ mem with bytes := … }`), all valid expressions. Without it,
                // a `let f := … \n { mem with bytes := … }` body — trust-ir's
                // `State/Memory.lean` / `Semantics/Memory.lean` `Memory.writeBytes`
                // returning an updated record after a `let rec` — was not
                // recognised as the implicit let body, so the parser bailed out of
                // the `let` and recovered with a spurious raw declaration
                // ("parser recovery produced raw declaration"). (Task R)
                | TokenKind::LBrace
                | TokenKind::Exists
                | TokenKind::ExistsUnique
                | TokenKind::Forall
                | TokenKind::Pi
                | TokenKind::Sigma
                | TokenKind::BigSup
                | TokenKind::BigInf
                | TokenKind::Not
                | TokenKind::If
                | TokenKind::Match
                | TokenKind::Fun
                | TokenKind::Lambda
                | TokenKind::Do
                | TokenKind::By
                // `show T from e` / `suffices h : P from e` as the implicit body
                // of a chained `have`/`let` (`have h : p := hp ⏎ show p ∧ q from
                // …`). Without these the `show`/`suffices` keyword after a
                // newline-separated binding was not recognised as the body, so
                // the parser bailed to decl recovery. (B105)
                | TokenKind::Show
                | TokenKind::Suffices
                // `.ok …` / `.error …` anonymous-constructor application as an
                // implicit let body — pervasive in trust-ir's `Except`-valued
                // semantics (`let sl := …; .ok (wrap …)`). (Track EF)
                | TokenKind::Dot
                // `⟨…⟩` anonymous-constructor (pair / structure / ⟨witness, proof⟩)
                // as an implicit let/have body — pervasive: `let k := 7 ⏎ ⟨k, k⟩`.
                // Without this the `⟨` after a chained `let`/`have` was not
                // recognised as the implicit body, so the parser bailed and decl
                // recovery emitted a spurious raw declaration ("error-recovery …").
                | TokenKind::LAngle
                | TokenKind::NatLit(_)
                | TokenKind::FloatLit(_)
                | TokenKind::CharLit(_)
                // String and interpolated-string literals and list literals
                // are terms like the literals above: `let digits := … ⏎
                // "ok:f32:0x" ++ …` and `let m := … ⏎ s!"{sign}{m}p{e - 53}"`
                // (trust-ir `FloatFixtures.lean` / `ExecutableFixtures.lean`)
                // bailed to decl recovery here.
                | TokenKind::StringLit(_)
                | TokenKind::InterpolatedString(..)
                | TokenKind::LBracket
        ) || (matches!(self.current_kind(), TokenKind::Hash)
            && matches!(self.peek_kind(1), Some(TokenKind::LBracket)))
    }

    /// Parse an expression for implicit let body
    /// This parses a full expression - the caller handles determining when
    /// the body ends (typically by layout/indentation in Lean 4, which we
    /// approximate by checking for command-starting tokens).
    pub(super) fn implicit_let_body_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        // Parse a full expression - operators, applications, etc.
        // The expression ends naturally when we hit something that can't
        // continue the expression (like a new command or EOF).
        self.expr()
    }

    /// Parse the body expression of a `let` after parsing the value.
    pub(super) fn let_body_after_value(&mut self) -> Result<SurfaceExpr, ParseError> {
        if self.eat(&TokenKind::In) || self.eat(&TokenKind::Semicolon) {
            // Explicit separator
            return self.expr();
        }

        if matches!(self.current_kind(), TokenKind::Let) {
            // Next let is implicitly the body
            let let_span = self.current_span();
            self.advance();
            return self.let_body(let_span);
        }

        if matches!(self.current_kind(), TokenKind::Have) && self.current().preceded_by_newline {
            // A layout-separated have is the body of this let, just as a
            // following let is. Retain its opaque binding origin instead of
            // falling through to declaration recovery. Without the explicit
            // separator handled above, Lean's optSemicolon requires a newline.
            let have_span = self.current_span();
            self.advance();
            return self.have_body(have_span);
        }

        if self.is_implicit_body_start() {
            return self.implicit_let_body_expr();
        }

        Err(ParseError::UnexpectedToken {
            line: self.current_line(),
            col: self.current_span().start,
            message: format!(
                "expected `in` or `;` after let binding, got {:?}",
                self.current_kind()
            ),
        })
    }

    /// Atomic expressions
    /// Every level of nesting — a parenthesized or bracketed group, a
    /// `fun`/`∀` binder type, a notation operand — reaches the next through
    /// an atom, and not every such path re-enters through the guarded
    /// [`Self::expr`] (`binders_barriered` parses a binder type with
    /// `iff_expr`, custom operands use `expr_at_custom_level`). So the atom
    /// grows the stack on demand, as `expr_in_slot` does: one nesting level
    /// of the debug-build operator chain is ~60 frames, and two of them on
    /// the unguarded paths overflowed a 1 MB thread on the codata seed
    /// library (regression pin
    /// `codata_cmd_tests::test_codata_stream_encoding_survives_small_thread_stack`).
    pub(super) fn atom_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        stacker::maybe_grow(
            Self::EXPR_STACK_RED_ZONE,
            Self::EXPR_STACK_GROW_SIZE,
            || self.atom_expr_guarded(),
        )
    }

    fn atom_expr_guarded(&mut self) -> Result<SurfaceExpr, ParseError> {
        let origin_start = self.origins.as_ref().map(|_| self.pos);
        // Track delimiter depth within a structure-field TYPE: while this atom
        // is a delimited group, the same-line next-field boundary in
        // `can_start_arg` must not fire — `(f x : T)` / `(x y : T)` inside a
        // field type are ascriptions/binder groups, not the next field.
        let field_delim = self.in_field_type
            && matches!(
                self.current_kind(),
                TokenKind::LParen | TokenKind::LAngle | TokenKind::LBrace | TokenKind::LBracket
            );
        if field_delim {
            self.field_delim_depth += 1;
        }
        // Lean's `withoutPosition`: every bracketed term group parses its
        // contents with NO saved position (`Lean/Parser/Term.lean:183,187,201`
        // for `(…)`, `:210` for `⟨…⟩`, `:345` for `{…}`; list and array
        // literals and `‹…›` likewise), so a continuation line inside the
        // group is never cut at an enclosing block's column. Measured before
        // this rule: `exact (id⏎  h)` with `h` at the `by` column failed
        // "expected RParen, got Ident(h)" where Lean accepts it, and giving a
        // `·` bullet its own column frame would have spread that failure to
        // every bracketed continuation at a bullet's content column.
        let opens_group = matches!(
            self.current_kind(),
            TokenKind::LParen
                | TokenKind::LAngle
                | TokenKind::LBrace
                | TokenKind::LBracket
                | TokenKind::LFrench
        ) || (matches!(self.current_kind(), TokenKind::Hash)
            && matches!(self.peek_kind(1), Some(TokenKind::LBracket)));
        let saved_position = self.position_suppressed_at;
        if opens_group {
            self.position_suppressed_at = Some(self.indent_stack.len());
        }
        let result = self.atom_expr_inner();
        self.position_suppressed_at = saved_position;
        if field_delim {
            self.field_delim_depth -= 1;
        }
        if let (Some(start), Ok(expr)) = (origin_start, &result) {
            if let Some(origins) = &mut self.origins {
                if let Some(tokens) = self.tokens.get(start..self.pos) {
                    origins.atom(expr, tokens);
                } else {
                    origins.invalidate("atom observation crossed a parser rewind");
                }
            }
        }
        result
    }

    fn atom_expr_inner(&mut self) -> Result<SurfaceExpr, ParseError> {
        // Applies to THIS atom only. Cleared immediately so a nested parse
        // (e.g. the `expr()` behind `(`) sees the ordinary `Type u` grammar.
        let type_atomic = self.type_atomic_in_arg;
        self.type_atomic_in_arg = false;
        let span = self.current_span();

        match self.current_kind().clone() {
            TokenKind::Ident(name) => {
                let name = self.reference_token(&name);
                // `bif c then t else e` — Lean 4's Bool conditional
                // (`Init/Prelude`), sugar for `cond c t e`. It is a reserved
                // keyword in Lean (no `Decidable` needed), so intercept it here
                // before ordinary identifier resolution, mirroring `outParam`.
                if name.is_lean_keyword() && name.is_unescaped_component("bif") {
                    self.advance();
                    return self.bif_body(span);
                }
                // `exists x, p` — Lean's ASCII `∃` (`Init/NotationExtra.lean`
                // `macro "exists" xs:explicitBinders ", " b:term`). `exists`
                // is a keyword there, so in term position it can only begin
                // this binder; see `expr_exists_kw.rs`.
                if name.is_lean_keyword() && name.is_unescaped_component("exists") {
                    self.advance();
                    return self.exists_keyword_body(span);
                }
                // `↑e` / `⇑e` — Lean's prefix coercion operators (both lexed to
                // Ident("↑")) bind at max precedence to the immediately
                // following atom. Without this, `f ↑x` in ARGUMENT position
                // juxtaposes as `App(f, [↑, x])` — the bare `↑` becomes its own
                // argument and elaboration fails UnknownIdent("↑"). Grabbing the
                // next atom here produces the `App(Ident("↑"), [x])` shape the
                // elaborator's coercion arm already handles, uniformly in both
                // head and argument positions. A trailing bare `↑` (no operand)
                // still parses as a plain identifier and stays a loud unknown.
                if name.is_unescaped_component("↑") {
                    self.advance();
                    if self.is_atom_start() {
                        let inner = self.atom_expr()?;
                        let end_span = inner.span();
                        return Ok(SurfaceExpr::App(
                            span.merge(end_span),
                            Box::new(SurfaceExpr::Ident(span, name)),
                            vec![SurfaceArg::positional(inner)],
                        ));
                    }
                    return Ok(SurfaceExpr::Ident(span, name));
                }
                // Handle special identifiers that act as type-level operators
                if name.is_unescaped_component("outParam") {
                    self.advance();
                    // outParam requires an argument
                    if self.is_atom_start() {
                        let inner = self.atom_expr()?;
                        let end_span = inner.span();
                        return Ok(SurfaceExpr::OutParam(span.merge(end_span), Box::new(inner)));
                    }
                    // Just `outParam` alone - return as identifier
                    return Ok(SurfaceExpr::Ident(span, name));
                }

                if name.is_unescaped_component("semiOutParam") {
                    self.advance();
                    // semiOutParam requires an argument
                    if self.is_atom_start() {
                        let inner = self.atom_expr()?;
                        let end_span = inner.span();
                        return Ok(SurfaceExpr::SemiOutParam(
                            span.merge(end_span),
                            Box::new(inner),
                        ));
                    }
                    // Just `semiOutParam` alone - return as identifier
                    return Ok(SurfaceExpr::Ident(span, name));
                }

                // Q(α) - type quotation for Qq metaprogramming
                // Denotes expressions of type α
                // Uses parse_q_body to support antiquotations (e.g., Q(Sort $u))
                // Part of #23: Qq Phase 4 - consistent antiquotation handling
                if name.is_unescaped_component("Q") {
                    self.advance();
                    // FIX: the Qq TYPE quotation `Q(α)` is CONTIGUOUS — the `(`
                    // must immediately follow `Q` with no intervening whitespace,
                    // as in Lean's Qq. `Q (x)` (space) is an ordinary application
                    // of a local/where-bound `Q` to `(x)`. Without the byte-
                    // adjacency guard, `f Q (g Q)` mis-parsed as the quotation
                    // `Q(g Q)`, silently DROPPING the `Q` argument and returning a
                    // partial application. `span.end` is `Q`'s end byte; after the
                    // advance `current_span().start` is the next token's start,
                    // equal iff no space/comment sits between them. SOUNDNESS-SAFE:
                    // pure surface-parse disambiguation; the term is kernel-re-checked.
                    if self.check(&TokenKind::LParen) && self.current_span().start == span.end {
                        self.advance(); // consume '('
                        let inner = self.parse_q_body()?; // use parse_q_body for antiquot support
                                                          // Check for optional type annotation: Q(α : κ)
                        let type_annot = if self.eat(&TokenKind::Colon) {
                            Some(Box::new(self.expr()?))
                        } else {
                            None
                        };
                        let end_span = self.current_span();
                        self.expect(&TokenKind::RParen)?;
                        return Ok(SurfaceExpr::QQuotation {
                            span: span.merge(end_span),
                            kind: QQuotationKind::Type,
                            inner: Box::new(inner),
                            type_annot,
                        });
                    }
                    // Just `Q` alone - return as identifier
                    return Ok(SurfaceExpr::Ident(span, name));
                }

                // q(expr) - value quotation for Qq metaprogramming
                // Constructs expression values with potential antiquotations
                if name.is_unescaped_component("q") {
                    self.advance();
                    // FIX: the Qq VALUE quotation `q(e)` is CONTIGUOUS — the `(`
                    // must immediately follow `q` with no intervening whitespace
                    // (see the `Q` case above). This was the exact "arg-drop"
                    // repro: `Nat.add q (Nat.succ q)` (and `Lt q (…)`,
                    // `nat_lt_b q (…)`, `Le q (…)`) mis-parsed as `Nat.add q(…)`
                    // — the quotation `q(Nat.succ q)` — dropping the first `q`
                    // argument and leaving a partial `Nat.add : Nat -> Nat`.
                    if self.check(&TokenKind::LParen) && self.current_span().start == span.end {
                        self.advance(); // consume '('
                        let inner = self.parse_q_body()?;
                        // Check for optional type annotation: q(e : τ)
                        let type_annot = if self.eat(&TokenKind::Colon) {
                            Some(Box::new(self.expr()?))
                        } else {
                            None
                        };
                        let end_span = self.current_span();
                        self.expect(&TokenKind::RParen)?;
                        return Ok(SurfaceExpr::QQuotation {
                            span: span.merge(end_span),
                            kind: QQuotationKind::Value,
                            inner: Box::new(inner),
                            type_annot,
                        });
                    }
                    // Just `q` alone - return as identifier
                    return Ok(SurfaceExpr::Ident(span, name));
                }

                // calc block: `calc step1 _ = b := pf ...`
                if name.is_lean_keyword() && name.is_unescaped_component("calc") {
                    self.advance();
                    let steps = self.calc_steps()?;
                    let end = steps.last().map_or(span, |s| s.span);
                    return Ok(SurfaceExpr::CalcBlock(span.merge(end), steps));
                }

                // letI / haveI — instance let/have — Part of #8, Part of #2550
                // Parse identically to let/have; the `I` suffix tells the
                // elaborator to register an instance, which we don't need
                // to model at the surface syntax level.
                if name.is_lean_keyword() && name.is_unescaped_component("letI") {
                    self.advance();
                    return self.let_body(span);
                }
                if name.is_lean_keyword() && name.is_unescaped_component("haveI") {
                    self.advance();
                    return self.have_body(span);
                }

                self.advance();
                // Dotted access is parsed by app_expr()/qq_app_expr() as projections.
                // The elaborator resolves projections back to qualified constants when needed.
                Ok(SurfaceExpr::Ident(span, name))
            }

            TokenKind::NatLit(n) => {
                self.advance();
                Ok(SurfaceExpr::Lit(span, SurfaceLit::nat(n)))
            }

            TokenKind::FloatLit(f) => {
                self.advance();
                Ok(SurfaceExpr::Lit(span, SurfaceLit::Float(f)))
            }

            TokenKind::CharLit(c) => {
                self.advance();
                Ok(SurfaceExpr::Lit(span, SurfaceLit::Char(c)))
            }

            TokenKind::StringLit(s) => {
                self.advance();
                Ok(SurfaceExpr::Lit(span, SurfaceLit::String(s)))
            }

            TokenKind::InterpolatedString(kind, s) => {
                self.advance();
                let parts = crate::interpolation::parse_interpolation(&s).map_err(|e| {
                    ParseError::UnexpectedToken {
                        line: self.current_line(),
                        col: span.start,
                        message: format!("interpolation error: {e}"),
                    }
                })?;
                Ok(SurfaceExpr::InterpolatedStr { span, kind, parts })
            }

            // Quoted syntax/macros - treat as opaque holes for now
            TokenKind::SyntaxQuote(content) => {
                self.advance();
                Ok(SurfaceExpr::SyntaxQuote(span, content))
            }

            // Explicit application: @f - disables implicit argument insertion
            // @f x y means call f with all implicit args provided explicitly
            TokenKind::At => {
                self.advance(); // consume @
                                // Parse the expression following @
                                // This should be an identifier or parenthesized expression
                let mut inner = self.atom_expr()?;
                // `@Foo.bar.baz` — fold an ADJACENT dotted chain into the
                // identifier before wrapping in Explicit. Ordinary heads leave
                // dots to app_expr's projection postfix, whose
                // back-to-qualified-constant recovery does not look through
                // an Explicit node — `@Codata.IMIntl` otherwise resolves just
                // `Codata` and fails. Adjacency (no whitespace before the dot)
                // matches the leading-dot constructor rule above.
                if let SurfaceExpr::Ident(id_span, name) = &inner {
                    let mut full_name = name.clone();
                    let mut final_span = *id_span;
                    while self.check(&TokenKind::Dot) {
                        if self.current_span().start != final_span.end {
                            break;
                        }
                        if let Some(TokenKind::Ident(next)) = self.peek_kind(1).cloned() {
                            self.advance(); // dot
                            final_span = self.current_span();
                            let next = SurfaceName::component(next, self.current().ident_escaped);
                            self.advance(); // ident
                            full_name = full_name.append(&next);
                        } else {
                            break;
                        }
                    }
                    inner = SurfaceExpr::Ident(id_span.merge(final_span), full_name);
                }
                let end_span = inner.span();
                Ok(SurfaceExpr::Explicit(span.merge(end_span), Box::new(inner)))
            }

            TokenKind::Type => {
                self.advance();
                // Check for Type* (Mathlib syntax for implicit universe level)
                if self.eat(&TokenKind::Star) {
                    Ok(SurfaceExpr::Universe(span, UniverseExpr::TypeImplicit))
                // Check for explicit level: Type u, Type 1, Type (max u v),
                // Type $u, or a level hole `Type _` (levelMVarToParam — the `_`
                // becomes a fresh universe metavar during elaboration).
                } else if !type_atomic
                    && matches!(
                        self.current_kind(),
                        TokenKind::Ident(_)
                            | TokenKind::NatLit(_)
                            | TokenKind::LParen
                            | TokenKind::Dollar
                            | TokenKind::Underscore
                    )
                {
                    let level = self.level_expr()?;
                    Ok(SurfaceExpr::Universe(
                        span,
                        UniverseExpr::TypeLevel(Box::new(level)),
                    ))
                } else {
                    Ok(SurfaceExpr::Universe(span, UniverseExpr::Type))
                }
            }

            TokenKind::Prop => {
                // `Prop.le` is a NAME, not dot notation on the sort. Lean's
                // tokenizer is maximal-munch on identifiers, so only a bare
                // `Prop` is the keyword — measured on the pinned v4.30.0-rc2,
                // which accepts `def Prop.le : Nat := 3; def f : Nat :=
                // Prop.le`. Clean read the head as the sort and then reported
                // "Unknown identifier: le (dot notation on type-valued
                // expression)": `Mathlib/Order/Basic.lean`'s `instance
                // Prop.le : LE Prop` (declared at top level — its enclosing
                // `section «Prop»` is a SECTION, not a namespace) and every
                // use of it, `Prop.partialOrder` among them.
                //
                // `keyword_name_head` is the single definition of the rule and
                // is byte-adjacency-checked there, so `Prop .foo` and a bare
                // `Prop` are untouched.
                if self.keyword_name_head().is_some() {
                    let name = self.qualified_ident()?;
                    let end = self.prev_span();
                    return Ok(SurfaceExpr::Ident(span.merge(end), name));
                }
                self.advance();
                Ok(SurfaceExpr::Universe(span, UniverseExpr::Prop))
            }

            TokenKind::Sort => {
                self.advance();
                // Check for Sort* (Mathlib syntax for an implicit universe
                // level, the `Sort` analogue of `Type*`). Consumed here so the
                // `*` does not leak out as a stray multiplication operator.
                if self.eat(&TokenKind::Star) {
                    Ok(SurfaceExpr::Universe(span, UniverseExpr::SortStar))
                // Check for explicit level: Sort u, Sort 0, Sort (u + 1), Sort $u,
                // or a level hole `Sort _` (fresh universe metavar), etc.
                } else if let TokenKind::Ident(_)
                | TokenKind::NatLit(_)
                | TokenKind::LParen
                | TokenKind::Dollar
                | TokenKind::Underscore = self.current_kind()
                {
                    let level = self.level_expr()?;
                    Ok(SurfaceExpr::Universe(
                        span,
                        UniverseExpr::Sort(Box::new(level)),
                    ))
                } else {
                    // Sort without explicit level = Sort u for fresh universe variable
                    Ok(SurfaceExpr::Universe(span, UniverseExpr::SortImplicit))
                }
            }

            // ⊤ lattice top - desugars to Top.top (Mathlib convention)
            TokenKind::Top => {
                self.advance();
                Ok(SurfaceExpr::Ident(
                    span,
                    SurfaceName::global_path("Top.top"),
                ))
            }

            // ⊥ lattice bottom - desugars to Bot.bot (Mathlib convention)
            TokenKind::Bot => {
                self.advance();
                Ok(SurfaceExpr::Ident(
                    span,
                    SurfaceName::global_path("Bot.bot"),
                ))
            }

            // ∅ empty collection - desugars to EmptyCollection.emptyCollection
            TokenKind::EmptySet => {
                self.advance();
                Ok(SurfaceExpr::Ident(
                    span,
                    SurfaceName::global_path("EmptyCollection.emptyCollection"),
                ))
            }

            TokenKind::Underscore => {
                self.advance();
                Ok(SurfaceExpr::Hole(span))
            }

            // Synthetic hole: `?_`, `?name`, or a bare `?`. In Lean 4 these are
            // named metavariable holes (`Lean.Parser.Term.syntheticHole`) that
            // `refine` turns into fresh goals. We model the synthetic hole as a
            // `SurfaceExpr::Hole`: the elaborator already lowers a hole to a
            // fresh metavariable, and the refine bridge
            // (`PendingRefineMetaCollector`) collects each unassigned hole-meta
            // into its own goal — so `refine ⟨?_, ?_⟩` against `p ∧ q` leaves
            // exactly the two field goals.
            //
            // The `_` or identifier naming the hole must be byte-adjacent to the
            // `?` (no intervening whitespace), matching Lean's tokenization;
            // otherwise the `?` stands alone as an anonymous synthetic hole and
            // the following token is parsed separately. Folding the optional
            // suffix in here is what prevents the old error-recovery path from
            // gluing `?` and `_` into a spurious `App(Hole, [Hole])`.
            TokenKind::Question => {
                let question_end = span.end;
                self.advance();
                let adjacent = self.current_span().start == question_end;
                // `?<ident>` (a byte-adjacent identifier) is a NAMED synthetic
                // hole: `refine` tags its goal with `<ident>` so `case <ident>`
                // can select it. `?_` and a bare `?` stay anonymous holes.
                if adjacent {
                    if let TokenKind::Ident(name) = self.current_kind().clone() {
                        let name = self.name_token(&name)?;
                        let name_span = self.current_span();
                        self.advance();
                        return Ok(SurfaceExpr::NamedHole(span.merge(name_span), name));
                    }
                    if matches!(self.current_kind(), TokenKind::Underscore) {
                        let name_span = self.current_span();
                        self.advance();
                        return Ok(SurfaceExpr::Hole(span.merge(name_span)));
                    }
                }
                Ok(SurfaceExpr::Hole(span))
            }

            TokenKind::LParen => {
                self.advance();
                // Could be: (), (e), (x : T), (e : T), (e1, e2, ...) tuple, or (x := e) named arg

                // Empty tuple/unit
                if self.check(&TokenKind::RParen) {
                    let end_span = self.current_span();
                    self.advance();
                    return Ok(SurfaceExpr::Ident(
                        span.merge(end_span),
                        SurfaceName::global_path("Unit.unit"),
                    ));
                }

                // Check for named argument syntax: (ident := expr)
                // This is used in contexts like `f (α := o)` where α is a parameter name
                //
                // `haveI` / `letI` lex as identifiers but are Lean keywords, so
                // `(haveI := A; x ≤ y)` — the anonymous instance-`have` form
                // Mathlib's `Preorder.ext` family writes inside parentheses —
                // is a `have` body, never a named argument. Reading it as one
                // parsed `(haveI := A` and then died on the `;` with `expected
                // RParen, got Semicolon` (six raw-declaration rows in
                // `Mathlib/Order/Basic.lean`, measured 2026-09-11).
                if let TokenKind::Ident(name) = self.current_kind().clone() {
                    if matches!(self.peek_kind(1), Some(TokenKind::ColonEq))
                        && name != "haveI"
                        && name != "letI"
                    {
                        let name = self.name_token(&name)?;
                        self.advance(); // consume ident
                        self.advance(); // consume :=
                        let value = self.expr()?;
                        let rparen = self.expect(&TokenKind::RParen)?;
                        let end_span = rparen.span;
                        // Represent named argument as special application to placeholder
                        // The elaborator will handle this as a named argument
                        return Ok(SurfaceExpr::NamedArg(
                            span.merge(end_span),
                            name,
                            Box::new(value),
                        ));
                    }
                }

                let expr = self.expr()?;

                if self.eat(&TokenKind::Colon) {
                    // Type-less ascription `(e :)`: Lean's `typeAscription :=
                    // "(" term " :" optional term ")"` (`Lean/Parser/Term.lean:
                    // 182-183`). It elaborates `e` with no expected type
                    // (`Lean/Elab/BuiltinNotation.lean:433-435`), so it is its
                    // own node, not `(e : _)`. Measured before: `hf.left b <|
                    // (congr_fun h b :)` (`Function.Injective2.left'`, Mathlib
                    // `Logic/Function/Basic.lean:983`) died "unexpected token:
                    // RParen" and left an empty raw declaration.
                    if self.check(&TokenKind::RParen) {
                        let end_span = self.expect(&TokenKind::RParen)?.span;
                        let full_span = span.merge(end_span);
                        let expr = cdot::desugar(full_span, expr, &mut self.hoisted_operand_cdots);
                        return Ok(SurfaceExpr::App(
                            full_span,
                            Box::new(SurfaceExpr::Ident(
                                full_span,
                                type_ascription_without_type_head(),
                            )),
                            vec![SurfaceArg::positional(expr)],
                        ));
                    }
                    // Type ascription: (e : T)
                    let ty = self.expr()?;
                    // Use the RParen's span (not current_span() which is the NEXT token).
                    // This prevents the Ascription span from extending past the closing
                    // paren, which would break dot-adjacency checks in app_expr. (#3421)
                    let rparen = self.expect(&TokenKind::RParen)?;
                    let end_span = rparen.span;
                    let full_span = span.merge(end_span);
                    // Cdot section INSIDE an ascription: `(· < · : T)` desugars the
                    // VALUE to an anonymous lambda and ascribes it —
                    // `((fun x y => x < y) : T)`. The plain-paren branch below
                    // already runs `cdot::desugar`; the ascription branch must too,
                    // else the `·` placeholders leak as unknown identifiers (Mathlib
                    // writes `swap (· < · : α → α → _)`, `Injective (g ∘ · : …)`).
                    // A no-op when `expr` has no `·`, so ordinary `(e : T)` is
                    // unchanged. (Track EF — ascription case)
                    let expr = cdot::desugar(full_span, expr, &mut self.hoisted_operand_cdots);
                    Ok(SurfaceExpr::Ascription(
                        full_span,
                        Box::new(expr),
                        Box::new(ty),
                    ))
                } else if self.eat(&TokenKind::Comma) {
                    // Tuple: (e1, e2, ...)
                    let mut rest = Vec::new();
                    // Allow trailing comma before RParen
                    if !self.check(&TokenKind::RParen) {
                        rest.push(self.expr()?);
                        while self.eat(&TokenKind::Comma) {
                            if self.check(&TokenKind::RParen) {
                                break; // trailing comma
                            }
                            rest.push(self.expr()?);
                        }
                    }
                    let rparen = self.expect(&TokenKind::RParen)?;
                    let end_span = rparen.span;

                    // Build nested Prod.mk: (a, b, c) -> Prod.mk a (Prod.mk b c)
                    let result = fold_right_nonempty(expr, rest, |elem, acc| {
                        let s = span.merge(end_span);
                        SurfaceExpr::App(
                            s,
                            Box::new(SurfaceExpr::Ident(s, SurfaceName::global_path("Prod.mk"))),
                            vec![SurfaceArg::positional(elem), SurfaceArg::positional(acc)],
                        )
                    });

                    Ok(SurfaceExpr::Paren(span.merge(end_span), Box::new(result)))
                } else {
                    let rparen = self.expect(&TokenKind::RParen)?;
                    let end_span = rparen.span;
                    let full_span = span.merge(end_span);
                    // Cdot section: `(· + 1)` / `(·.snd)` / `(f ·)` desugar to an
                    // anonymous lambda. `desugar` is a no-op when `expr` has no
                    // `·` placeholders, so ordinary `(e)` is unchanged. (Track EF)
                    let expr = cdot::desugar(full_span, expr, &mut self.hoisted_operand_cdots);
                    Ok(SurfaceExpr::Paren(full_span, Box::new(expr)))
                }
            }

            TokenKind::Fun | TokenKind::Lambda => {
                self.advance();
                self.lambda_body(span)
            }

            TokenKind::Forall | TokenKind::Pi => {
                self.advance();
                self.forall_body(span)
            }

            TokenKind::Let => {
                self.advance();
                self.let_body(span)
            }

            TokenKind::If => {
                self.advance();
                self.if_body(span)
            }

            TokenKind::By => {
                self.advance();
                Ok(self.by_body(span))
            }

            TokenKind::Sorry => {
                self.advance();
                Ok(SurfaceExpr::Ident(span, SurfaceName::global_path("sorry")))
            }

            TokenKind::Rfl => {
                self.advance();
                Ok(SurfaceExpr::Ident(span, SurfaceName::global_path("rfl")))
            }

            TokenKind::Not => {
                // ¬ as prefix operator (Lean `prefix:40 "¬"`, `Init/Prelude.lean`).
                //
                // The lexer hands `¬` and ASCII `!` over as one token kind, but
                // Lean gives them different heads (`Init/Notation.lean`):
                // `notation:max "¬" p:40 => Not p` and `notation:max "!" b:40 =>
                // not b` (`Bool.not`, exported as `not`). `¬` is two bytes in
                // UTF-8 and `!` one, so the token's width tells them apart;
                // folding both into `Not` made `¬(a == b)` the BOOLEAN negation
                // (`not_beq_of_ne`, measured 2026-09-12).
                let head = if span.end.saturating_sub(span.start) == 1 {
                    "not"
                } else {
                    "Not"
                };
                self.advance();
                // The operand parses at precedence 40, so it captures the
                // comparison operators (`=`, `<`, `≤`, … at prec 50) and
                // everything tighter (application, `+`, …) but stops at the
                // looser connectives `∧`(35) / `∨`(30) / `→`(25). Hence
                // `¬ n = 0` is `¬ (n = 0)` (NOT the ill-typed `(¬ n) = 0`),
                // while `¬ a ∧ b` stays `(¬ a) ∧ b`. `cmp_expr` is exactly the
                // 50-and-tighter level (and itself re-enters `unary_expr` for a
                // nested leading `¬`, so `¬ ¬ p` = `Not (Not p)`).
                let inner = self.cmp_expr()?;
                let end_span = inner.span();
                // Overshoot repair, same as `build_connective_arrow_aware` and
                // `cmp_expr`'s `=`-arrow tail: the hand-written precedence
                // chain can hand back an `Arrow` whose DOMAIN is the actual
                // prec-40 operand. `¬p → q` must parse as `(¬p) → q` (Lean
                // `prefix:40 "¬"` vs `→` at 25), never `¬(p → q)` — the
                // 2026-08-17 srcelab class where every negation-domained
                // application failed and `(¬p → q) = ¬(p → q)` PROVED by rfl.
                // A user-parenthesized `¬(p → q)` arrives as `Paren(Arrow …)`,
                // not a bare `Arrow`, so it is untouched.
                match inner {
                    SurfaceExpr::Arrow(_, domain, codomain) => {
                        let not_span = span.merge(domain.span());
                        let negated = SurfaceExpr::App(
                            not_span,
                            Box::new(SurfaceExpr::Ident(span, SurfaceName::global_path(head))),
                            vec![SurfaceArg::positional(*domain)],
                        );
                        Ok(SurfaceExpr::Arrow(
                            span.merge(end_span),
                            Box::new(negated),
                            codomain,
                        ))
                    }
                    other => Ok(SurfaceExpr::App(
                        span.merge(end_span),
                        Box::new(SurfaceExpr::Ident(span, SurfaceName::global_path(head))),
                        vec![SurfaceArg::positional(other)],
                    )),
                }
            }

            TokenKind::LAngle => {
                // ⟨...⟩ anonymous constructor
                self.advance();
                self.anon_constructor_body(span)
            }

            TokenKind::LFrench => {
                // ‹P› anonymous hypothesis. Lean `Init/Tactics.lean` expands
                // `‹$type›` to `(show $type by assumption)` — the elaborator
                // discharges it against a matching hypothesis in context. We
                // build the same `Ascription(ByTactic[assumption], P)` shape the
                // `show t by tac` parser produces.
                self.advance();
                let ty = self.expr()?;
                let end_span = self.current_span();
                self.expect(&TokenKind::RFrench)?;
                let full = span.merge(end_span);
                let assumption = SurfaceTactic::Named {
                    span: full,
                    name: "assumption".to_string(),
                    args: vec![],
                };
                Ok(SurfaceExpr::Ascription(
                    full,
                    Box::new(SurfaceExpr::ByTactic(full, vec![assumption])),
                    Box::new(ty),
                ))
            }

            TokenKind::LDAngle => {
                // ⟪expr, expr⟫ inner product — Part of #8, Part of #2550
                // Desugars to inner_product(a, b). The closing ⟫ may be
                // followed by a subscript like _ℝ which is a separate token.
                self.advance();
                let first = self.expr()?;
                self.expect(&TokenKind::Comma)?;
                let second = self.expr()?;
                let end_span = self.current_span();
                self.expect(&TokenKind::RDAngle)?;
                Ok(SurfaceExpr::App(
                    span.merge(end_span),
                    Box::new(SurfaceExpr::Ident(span, SurfaceName::global_path("inner"))),
                    vec![
                        SurfaceArg::positional(first),
                        SurfaceArg::positional(second),
                    ],
                ))
            }

            TokenKind::LBrace => {
                self.advance();
                self.record_literal_body(span)
            }

            TokenKind::Match => {
                self.advance();
                self.match_body(span)
            }

            TokenKind::Open => {
                self.advance();
                self.open_expr_body(span)
            }

            TokenKind::Do if !self.forbid_do => {
                self.advance();
                self.do_body(span)
            }

            TokenKind::Exists => {
                // ∃ prefix for exists
                self.advance();
                self.exists_body(span)
            }

            TokenKind::Sigma => {
                // Σ prefix for the dependent-pair (Sigma) type binder
                self.advance();
                self.sigma_body(span, "Sigma")
            }

            TokenKind::PSigma => {
                // Σ' prefix for the PSigma dependent-pair type binder
                self.advance();
                self.sigma_body(span, "PSigma")
            }

            TokenKind::BigSup => {
                // ⨆ indexed supremum: `⨆ i, f i` ⇒ `iSup (fun i => f i)`. The
                // binder-body form desugars exactly like `Σ` (see `sigma_body`).
                self.advance();
                self.sigma_body(span, "iSup")
            }

            TokenKind::BigInf => {
                // ⨅ indexed infimum: `⨅ i, f i` ⇒ `iInf (fun i => f i)`.
                self.advance();
                self.sigma_body(span, "iInf")
            }

            TokenKind::ExistsUnique => {
                // ∃! prefix for unique exists - same as exists for parsing
                self.advance();
                self.exists_unique_body(span)
            }

            TokenKind::BigSum => {
                self.advance();
                self.bigop_body(span, "∑")
            }

            TokenKind::BigProd => {
                self.advance();
                self.bigop_body(span, "∏")
            }

            TokenKind::Integral => {
                self.advance();
                self.bigop_body(span, "∫")
            }

            TokenKind::FintAvg => {
                self.advance();
                self.bigop_body(span, "⨍")
            }

            TokenKind::BigUnion => {
                self.advance();
                self.bigop_body(span, "⋃")
            }

            TokenKind::BigInter => {
                self.advance();
                self.bigop_body(span, "⋂")
            }

            TokenKind::Show => {
                self.advance();
                self.show_body(span)
            }

            TokenKind::Have => {
                self.advance();
                self.have_body(span)
            }

            TokenKind::Suffices => {
                self.advance();
                self.suffices_body(span)
            }

            TokenKind::LBracket => {
                self.advance();
                self.list_literal_body(span)
            }

            TokenKind::SetOption => {
                self.advance();
                self.set_option_expr(span)
            }

            TokenKind::Hash => {
                // Array literal syntax `#[...]`
                let next_is_lbracket = matches!(
                    self.tokens.get(self.pos + 1).map(|t| &t.kind),
                    Some(TokenKind::LBracket)
                );
                self.advance();
                if next_is_lbracket {
                    let _ = self.expect(&TokenKind::LBracket)?;
                    self.array_literal_body(span)
                } else {
                    // Treat other uses of `#` in expressions as holes for now
                    Ok(SurfaceExpr::Hole(span))
                }
            }

            TokenKind::Dot => {
                // Anonymous constructor: .foo or .foo args
                // Leading dot indicates constructor whose type is inferred from context
                self.advance();
                match self.current_kind().clone() {
                    TokenKind::Ident(name) => {
                        let end_span = self.current_span();
                        let name = SurfaceName::component(name, self.current().ident_escaped);
                        self.advance();
                        // Build a dotted identifier like ".foo"
                        // The elaborator will resolve this to the appropriate constructor
                        let mut full_name = name.with_relative_constructor();
                        let mut final_span = end_span;
                        // Handle nested dotted access like .foo.bar
                        // Only consume the dot when it is adjacent to the previous
                        // identifier (no whitespace gap). Otherwise, `.error .notFound`
                        // would be incorrectly parsed as a single identifier
                        // `.error.notFound` instead of two separate leading-dot
                        // constructors resolved via application. (#3421)
                        while self.check(&TokenKind::Dot) {
                            let dot_span = self.current_span();
                            if dot_span.start != final_span.end {
                                // Whitespace before the dot: this is a new token,
                                // not a continuation of the dotted name.
                                break;
                            }
                            if let Some(TokenKind::Ident(next)) = self.peek_kind(1).cloned() {
                                self.advance(); // dot
                                final_span = self.current_span();
                                let next =
                                    SurfaceName::component(next, self.current().ident_escaped);
                                self.advance(); // ident
                                full_name = full_name.append(&next);
                            } else {
                                break;
                            }
                        }
                        Ok(SurfaceExpr::Ident(span.merge(final_span), full_name))
                    }
                    TokenKind::LParen => {
                        // .(expr) - parenthesized anonymous constructor call
                        self.advance(); // consume lparen
                        let inner = self.expr()?;
                        let end_span = self.current_span();
                        self.expect(&TokenKind::RParen)?;
                        // Represent as application of hole to inner
                        Ok(SurfaceExpr::App(
                            span.merge(end_span),
                            Box::new(SurfaceExpr::Hole(span)),
                            vec![SurfaceArg::positional(inner)],
                        ))
                    }
                    TokenKind::LBrace => {
                        // .{ field := value } - anonymous constructor with named fields
                        // Type is inferred from context, same as .foo anonymous constructors
                        self.advance(); // consume lbrace
                        self.record_literal_body(span)
                    }
                    // A KEYWORD token as a leading-dot name: `.rfl` lexes as
                    // [Dot][Rfl] because `rfl` is a keyword, and this arm only
                    // took Ident — while the projection postfix in this same
                    // file already accepts every as_keyword_str token after an
                    // adjacent dot. `ht v v .rfl` (Mathlib Logic/Basic:64) and
                    // `.default` are the shapes. Mirrors the Ident arm minus
                    // the nested-dot loop (a keyword constructor name is
                    // always terminal: `.rfl.symm` projects off the result,
                    // which the postfix path handles).
                    other => {
                        if let Some(kw) = other.as_keyword_str() {
                            let end_span = self.current_span();
                            self.advance();
                            Ok(SurfaceExpr::Ident(
                                span.merge(end_span),
                                SurfaceName::component(kw, false).with_relative_constructor(),
                            ))
                        } else {
                            Err(ParseError::UnexpectedToken {
                                line: self.current_line(),
                                col: self.current_span().start,
                                message: format!("expected identifier after '.', got {other:?}"),
                            })
                        }
                    }
                }
            }

            TokenKind::Cdot => {
                // · (middle dot / cdot) - section placeholder
                // Used in section notation: (· + ·) creates fun x y => x + y
                // We represent it as a special hole marker that the elaborator will resolve
                self.advance();
                Ok(SurfaceExpr::Ident(span, SurfaceName::generated_path("·")))
            }

            // |expr| absolute value notation - desugars to `abs expr`
            // Common in Mathlib for absolute value and norms
            TokenKind::Pipe => {
                self.advance(); // consume opening |
                let inner = self.expr()?;
                let end_span = self.current_span();
                self.expect(&TokenKind::Pipe)?;
                Ok(SurfaceExpr::App(
                    span.merge(end_span),
                    Box::new(SurfaceExpr::Ident(span, SurfaceName::global_path("abs"))),
                    vec![SurfaceArg::positional(inner)],
                ))
            }

            // ← expr or <- expr: monadic action lift (Lean 4 liftMethod)
            // Only valid inside do blocks; the elaborator rejects it elsewhere.
            // Reference: Lean 4 `Parser.Term.liftMethod` in src/Lean/Parser/Do.lean
            TokenKind::LeftArrow => {
                self.advance();
                let inner = self.expr()?;
                let end_span = inner.span();
                Ok(SurfaceExpr::LiftMethod(
                    span.merge(end_span),
                    Box::new(inner),
                ))
            }

            TokenKind::Error(ref err) => {
                // A lexer-error token in atom position is an unrecognized
                // character — in practice an unknown infix operator like `▸`
                // (subst), `∣` (divides), or `•` (scalar mult, split out of the
                // `·` section token). Previously an `UnexpectedChar` was turned
                // into a `SurfaceExpr::Hole` "to allow parsing to continue",
                // which fabricated a hole-slot: `a ▸ b` became `(a _ b)`, a
                // well-formed-looking application that can slip past elaboration
                // with the wrong meaning (audit P0-4). Brick 1 rejects it
                // loudly; the real operators land in Brick 3.
                let err = err.clone();
                let err_line = self.current_line();
                let err_col = span.start;
                self.advance();
                match err {
                    crate::lexer::LexError::UnexpectedChar(c) => Err(ParseError::UnexpectedToken {
                        line: err_line,
                        col: err_col,
                        message: format!(
                            "unknown operator or character '{c}' \
                                 (no infix/prefix rule for it)"
                        ),
                    }),
                    _ => Err(ParseError::UnexpectedToken {
                        line: err_line,
                        col: err_col,
                        message: format!("lexer error: {err}"),
                    }),
                }
            }

            _ => Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: span.start,
                message: format!("unexpected token: {:?}", self.current_kind()),
            }),
        }
    }
}

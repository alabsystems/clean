// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//! Operator precedence parsing: expr through unary_expr, extracted from expr.rs as part of #307.
use super::helpers::{
    is_typed_equiv_subscript, is_typed_morphism_subscript, typed_equiv_constructor,
    typed_morphism_constructor,
};
use super::Parser;
use crate::lexer::TokenKind;
use crate::surface::*;
use crate::ParseError;

impl Parser {
    /// Maximum expression nesting depth before returning an error.
    /// Each nesting level produces ~17 stack frames (operator precedence chain).
    /// 128 × 17 ≈ 2,176 frames, fits in 2MB proptest worker threads.
    /// 256 was too high and caused stack overflow in debug builds (#2961).
    /// Real Lean 4 code rarely exceeds 20-30 levels.
    const MAX_EXPR_DEPTH: u32 = 128;
    /// Debug builds have large parser frames; grow before the next recursive
    /// expression descent can exhaust small test-worker stacks.
    const EXPR_STACK_RED_ZONE: usize = 512 * 1024;
    const EXPR_STACK_GROW_SIZE: usize = 8 * 1024 * 1024;

    /// Parse an expression
    pub(super) fn expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        // Grow the stack on demand so deeply nested inputs hit the
        // MAX_EXPR_DEPTH guard instead of aborting with SIGABRT.
        stacker::maybe_grow(
            Self::EXPR_STACK_RED_ZONE,
            Self::EXPR_STACK_GROW_SIZE,
            || {
                self.expr_depth += 1;
                if self.expr_depth > Self::MAX_EXPR_DEPTH {
                    let col = self.current_span().start;
                    self.expr_depth -= 1;
                    return Err(ParseError::NestingTooDeep {
                        col,
                        depth: self.expr_depth + 1,
                        max: Self::MAX_EXPR_DEPTH,
                    });
                }
                // A full-expression position resets the custom-operator operand
                // level to the ambient floor (parenthesized subexpressions,
                // statement bodies, arrow codomains all accept any modeled
                // custom operator). See `custom_notation.rs` (B100).
                let result = self.with_custom_min_prec(
                    super::custom_notation::CUSTOM_PREC_FLOOR,
                    Self::hom_expr,
                );
                self.expr_depth -= 1;
                result
            },
        )
    }

    /// Morphism type `a ⟶ b` → `Quiver.Hom a b` (Lean `Combinatorics/Quiver`:
    /// `infixr:10 " ⟶ " => Quiver.Hom`, right-associative). The loosest binary
    /// operator — same precedence-10 level as `<|`/`$` — so it sits at the very
    /// top of the expression chain. Morphisms are between OBJECTS, so `⟶` never
    /// co-occurs with logical connectives in practice; a no-op token check when
    /// absent, so every other parse is unchanged.
    pub(super) fn hom_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        let left = self.pipe_expr()?;
        if self.eat(&TokenKind::HomArrow) {
            let right = self.hom_expr()?; // right-associative (infixr:10)
            let span = left.span().merge(right.span());
            Ok(SurfaceExpr::App(
                span,
                Box::new(SurfaceExpr::Ident(span, "Quiver.Hom".to_string())),
                vec![SurfaceArg::positional(left), SurfaceArg::positional(right)],
            ))
        } else {
            Ok(left)
        }
    }

    /// Backward pipe / low-precedence application: `f <| x` and `f $ x`
    /// (both `syntax:min` = precedence 10, right-associative, `Init/Notation.lean`
    /// `:521`/`:556`). Both desugar to plain application `f x`; the piped/dollar'd
    /// argument is the LAST operand. They share this level and interleave right:
    /// `f <| g $ x` = `f <| (g $ x)` = `f (g x)`.
    ///
    /// `$` fires ONLY when followed by whitespace (Lean's decl is
    /// `atomic(" $" ws)`): `f $x` (no space) is a pseudo-antiquotation `$x`, never
    /// low-precedence application, so it is left for the antiquotation / reject
    /// path rather than consumed here.
    pub(super) fn pipe_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        let left = self.fpipe_expr()?;

        // <| is right-associative: f <| g <| x = f <| (g <| x)
        if self.eat(&TokenKind::BackwardPipe) {
            let right = self.pipe_expr()?; // Recursive for right-associativity
            let span = left.span().merge(right.span());
            // f <| x is equivalent to f x (low-precedence application)
            return Ok(SurfaceExpr::App(
                span,
                Box::new(left),
                vec![SurfaceArg::positional(right)],
            ));
        }

        // `$` (low-precedence application), right-associative, only with a
        // trailing space so quotation antiquotations `$x` keep their meaning.
        if self.dollar_is_low_prec_app() {
            self.advance(); // consume `$`
            let right = self.pipe_expr()?;
            let span = left.span().merge(right.span());
            return Ok(SurfaceExpr::App(
                span,
                Box::new(left),
                vec![SurfaceArg::positional(right)],
            ));
        }

        Ok(left)
    }

    /// Whether the current token is a `$` that acts as the low-precedence
    /// application operator (Lean `syntax:min term atomic(" $" ws) term:min`).
    /// True iff the current token is `Dollar` AND the following token is not
    /// byte-adjacent (there is whitespace after the `$`). `f $x` (adjacent) is a
    /// pseudo-antiquotation, not application, so it returns false and the `$`
    /// stays for the reject/quotation path (a loud gap in plain term position).
    fn dollar_is_low_prec_app(&self) -> bool {
        if !matches!(self.current_kind(), TokenKind::Dollar) {
            return false;
        }
        let dollar_end = self.current_span().end;
        self.tokens
            .get(self.pos + 1)
            .is_some_and(|next| next.span.start != dollar_end)
    }

    /// Alternative-choice operator `a <|> b` (HOrElse.hOrElse, `syntax:20`,
    /// right-associative — `Init/Notation.lean:430`). Sits between the pipe layer
    /// (`<|`/`$`, prec 10) and `↔` (prec 20). Desugars to
    /// `HOrElse.hOrElse a (fun _ : Unit => b)` — Lean routes `<|>` through
    /// `binop_lazy%` (`Lean/Elab/Extra.lean:92`, `f a (fun () => b)`), whose
    /// load-bearing part for a single monad is exactly this RHS unit-thunk
    /// (Brick 3, `docs/plans/ELAB_ARMS_AUDIT_2026-07-08.md` §3(a)).
    fn orelse_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        let left = self.iff_expr()?;
        if self.eat(&TokenKind::OrElse) {
            let lspan = left.span();
            let right = self.orelse_expr()?; // right-associative
            let span = lspan.merge(right.span());
            return Ok(SurfaceExpr::App(
                span,
                Box::new(SurfaceExpr::Ident(lspan, "HOrElse.hOrElse".to_string())),
                vec![
                    SurfaceArg::positional(left),
                    SurfaceArg::positional(Self::unit_thunk(right)),
                ],
            ));
        }
        Ok(left)
    }

    /// Wrap `rhs` in the Lean-faithful RHS unit-thunk `fun _ : Unit => rhs`.
    ///
    /// Lean inserts this thunk syntactically for `<*>`/`<*`/`*>`
    /// (`Init/Prelude.lean` macro_rules: `f <*> x` → `Seq.seq f fun _ : Unit
    /// => x`) and via `binop_lazy%` for `>>`/`<|>` (`Lean/Elab/Extra.lean:92`
    /// = `f a (fun () => b)`). The class fields consume `Unit → β`, so the
    /// RHS is captured UNEVALUATED — the laziness that distinguishes
    /// `>>`/`*>`/`<|>` from eager application for effectful monads.
    fn unit_thunk(rhs: SurfaceExpr) -> SurfaceExpr {
        let rspan = rhs.span();
        let mut binder =
            SurfaceBinder::explicit("_", SurfaceExpr::Ident(rspan, "Unit".to_string()));
        binder.span = rspan;
        SurfaceExpr::Lambda(rspan, vec![binder], Box::new(rhs))
    }

    /// Forward pipe expressions: `x |> f` and `x |>.foo` (left-associative).
    ///
    /// Lean 4's `|>` (`infixl`) threads the left value into the right side:
    /// - `x |> f`      desugars to `f x` (low-precedence application).
    /// - `x |>.foo`    desugars to `x.foo` (dot/projection notation; e.g.
    ///   `n |>.succ` = `n.succ` = `Nat.succ n`).
    ///
    /// Left-associativity means `x |> f |> g` = `g (f x)` and
    /// `n |>.succ |>.succ` = `n.succ.succ`, so the chain is parsed with a loop
    /// that keeps folding the accumulated pipeline into the new right operand.
    ///
    /// This sits *below* backward pipe `<|` in the precedence chain (Lean: `<|`
    /// is looser than `|>`) and *above* `iff_expr`.
    fn fpipe_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        let mut left = self.orelse_expr()?;

        while self.eat(&TokenKind::ForwardPipe) {
            if self.check(&TokenKind::Dot) {
                // `x |>.foo args` — projection/dot notation on the piped value.
                // Lean's `|>.` is one token (`Term.pipeProj`, `checkNoWsBefore`
                // on the field), followed by a dotted rawIdent and `many
                // argument`: `x |>.foo y` = `(x.foo) y`, `1 |>.succ.succ` =
                // `1.succ.succ` (one node), and `x |>. succ` (whitespace before
                // the field) is a parse error.
                let dot_span = self.current_span();
                self.advance(); // consume the `.`
                if self.current_span().start != dot_span.end {
                    return Err(ParseError::UnexpectedToken {
                        line: self.current_line(),
                        col: self.current_span().start,
                        message: "`|>.` does not allow whitespace before the field name"
                            .to_string(),
                    });
                }
                let (projection, mut field_end) = self.pipe_proj_field()?;
                left = SurfaceExpr::Proj(left.span().merge(field_end), Box::new(left), projection);
                // A byte-adjacent `.field` chain is one rawIdent in Lean.
                while self.check(&TokenKind::Dot) && self.current_span().start == field_end.end {
                    self.advance();
                    let (proj, end) = self.pipe_proj_field()?;
                    field_end = end;
                    left = SurfaceExpr::Proj(left.span().merge(field_end), Box::new(left), proj);
                }
                // Trailing application arguments (`many argument`).
                let mut end = left.span();
                let mut args = Vec::new();
                while self.is_atom_start() {
                    let arg = self.atom_expr()?;
                    end = arg.span();
                    args.push(SurfaceArg::positional(arg));
                }
                if !args.is_empty() {
                    left = SurfaceExpr::App(left.span().merge(end), Box::new(left), args);
                }
            } else {
                // `x |> f` — low-precedence application: `f x`. The right
                // operand is parsed at `orelse_expr` precedence so a following
                // `|>`/`<|` re-enters this loop / the backward-pipe rule.
                let func = self.orelse_expr()?;
                let span = left.span().merge(func.span());
                left = SurfaceExpr::App(span, Box::new(func), vec![SurfaceArg::positional(left)]);
            }
        }

        Ok(left)
    }

    /// Read a single projection field after `|>.` (or a `.field` continuation):
    /// a named field, a numeric field index, or a keyword-spelled field. Returns
    /// the projection and the span of the field token.
    pub(super) fn pipe_proj_field(&mut self) -> Result<(Projection, Span), ParseError> {
        match self.current_kind().clone() {
            TokenKind::Ident(field) => {
                let end_span = self.current_span();
                self.advance();
                Ok((Projection::Named(field), end_span))
            }
            TokenKind::NatLit(n) => {
                let end_span = self.current_span();
                let index_line = self.current_line();
                let index_col = end_span.start;
                self.advance();
                let idx = n
                    .to_u64()
                    .and_then(|v| u32::try_from(v).ok())
                    .ok_or_else(|| ParseError::UnexpectedToken {
                        line: index_line,
                        col: index_col,
                        message: format!("projection index too large: {n}"),
                    })?;
                Ok((Projection::Index(idx), end_span))
            }
            other => {
                if let Some(kw_str) = other.as_keyword_str() {
                    let end_span = self.current_span();
                    self.advance();
                    Ok((Projection::Named(kw_str.to_string()), end_span))
                } else {
                    Err(ParseError::UnexpectedToken {
                        line: self.current_line(),
                        col: self.current_span().start,
                        message: format!(
                            "expected field name after `|>.`, got {:?}",
                            self.current_kind()
                        ),
                    })
                }
            }
        }
    }

    /// Re-associate a logical connective `op` whose right operand greedily
    /// swallowed a trailing `→` that actually binds LOOSER than `op`.
    ///
    /// Lean precedence: `↔`(20) < `→`(25) < `∨`(30) < `∧`(35). The hand-written
    /// precedence chain reaches `arrow_expr` (which consumes `→`) BELOW
    /// `and_expr`/`or_expr`/`iff_expr`, so when these connectives recurse on their
    /// right operand the inner `arrow_expr` eats a `→` that belongs to an
    /// enclosing implication. For `a ∧ b → c` the right operand comes back as
    /// `Arrow(b, c)`, which would wrongly build `a ∧ (b → c)`.
    ///
    /// This helper repairs that: when `right` is `Arrow(domain, codomain)`, the
    /// connective binds to the arrow's DOMAIN and the codomain floats up, giving
    /// `(a ∧ b) → c` (= `Arrow(And a b, c)`). When `right` is not an arrow the
    /// connective is built directly. This mirrors the existing arrow-splitting
    /// re-association already done for `=` in [`Self::cmp_expr`].
    ///
    /// `op_name` is the connective's head constant (`And`/`Or`/`Iff`).
    fn build_connective_arrow_aware(
        op_name: &str,
        left: SurfaceExpr,
        right: SurfaceExpr,
    ) -> SurfaceExpr {
        let op_span = left.span();
        match right {
            SurfaceExpr::Arrow(_, domain, codomain) => {
                // `left op (domain → codomain)` re-associates to
                // `(left op domain) → codomain` since `→` binds looser than `op`.
                let connective_span = op_span.merge(domain.span());
                let connective = SurfaceExpr::App(
                    connective_span,
                    Box::new(SurfaceExpr::Ident(op_span, op_name.to_string())),
                    vec![
                        SurfaceArg::positional(left),
                        SurfaceArg::positional(*domain),
                    ],
                );
                let full_span = connective_span.merge(codomain.span());
                SurfaceExpr::Arrow(full_span, Box::new(connective), codomain)
            }
            other => {
                let span = op_span.merge(other.span());
                SurfaceExpr::App(
                    span,
                    Box::new(SurfaceExpr::Ident(op_span, op_name.to_string())),
                    vec![SurfaceArg::positional(left), SurfaceArg::positional(other)],
                )
            }
        }
    }

    /// Iff expressions: A ↔ B (precedence 20)
    pub(super) fn iff_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        let mut left = self.or_expr()?;

        while self.eat(&TokenKind::Iff) {
            let right = self.or_expr()?;
            // `↔` binds looser than `→` (20 < 25), so a right operand of the form
            // `b → c` re-associates to `(a ↔ b) → c`.
            left = Self::build_connective_arrow_aware("Iff", left, right);
        }

        Ok(left)
    }

    /// Or expressions: A ∨ B (Prop, prec 30) and A || B (Bool.or, infixr:30).
    ///
    /// Both `∨` (`Or`) and `||` (`Bool.or`) are declared `infixr:30` in Lean 4:
    /// RIGHT-associative, so `a ∨ b ∨ c` parses as `a ∨ (b ∨ c)` (= `Or a (Or b c)`),
    /// not `(a ∨ b) ∨ c`. We recurse on the right operand (mirroring `and_expr`)
    /// rather than folding left. Right-nesting is what `rcases`/`obtain` Or-pattern
    /// alternation relies on for `rcases h with hp | hq | hr` on `p ∨ q ∨ r`.
    pub(super) fn or_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        let left = self.and_expr()?;
        let span = left.span();

        if self.eat(&TokenKind::Or) {
            let right = self.or_expr()?; // right-associative: a ∨ (b ∨ c)
                                         // `∨` binds TIGHTER than `→` (30 > 25). When the right operand greedily
                                         // swallowed a trailing `→` (e.g. `b → c` in `a ∨ b → c`), re-associate
                                         // to `(a ∨ b) → c`. A pure `a ∨ (b ∨ c)` right operand is NOT an arrow,
                                         // so right-associativity of `∨` is preserved.
            Ok(Self::build_connective_arrow_aware("Or", left, right))
        } else if self.eat(&TokenKind::PipePipe) {
            // Bool.or via the heterogeneous `||` operator (also infixr:30).
            let right = self.or_expr()?; // right-associative: a || (b || c)
            let s = span.merge(right.span());
            Ok(SurfaceExpr::App(
                s,
                Box::new(SurfaceExpr::Ident(span, "or".to_string())),
                vec![SurfaceArg::positional(left), SurfaceArg::positional(right)],
            ))
        } else {
            Ok(left)
        }
    }

    /// And expressions: A ∧ B (Prop, prec 35) and A && B (Bool.and, infixr:35).
    ///
    /// Both `∧` (`And`) and `&&` (`Bool.and`) are declared `infixr:35` in Lean 4
    /// (`Init/Notation.lean`): they are RIGHT-associative, so `a ∧ b ∧ c` parses
    /// as `a ∧ (b ∧ c)` (= `And a (And b c)`), not `(a ∧ b) ∧ c`. We therefore
    /// recurse on the right operand (the same shape as the other right-assoc
    /// operators here, e.g. `pipe_expr`/`cons_expr`) rather than folding left.
    /// Right-nesting is what `rcases`/`obtain` flattening relies on: `⟨a, b, c⟩`
    /// on `a ∧ b ∧ c` destructs the left field then recurses into the `b ∧ c`
    /// right field.
    pub(super) fn and_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        // The low custom-infix band owns levels 45–50 (notably the canonical
        // temporal `⊨` and `~>` relations). It wraps comparisons and remains
        // inside level-35 conjunction, preserving Lean's binding order.
        let left = self.low_custom_infix_expr()?;
        let span = left.span();

        if self.eat(&TokenKind::And) {
            let right = self.and_expr()?; // right-associative: a ∧ (b ∧ c)
                                          // `∧` binds TIGHTER than `→` (35 > 25). When the right operand
                                          // greedily swallowed a trailing `→` (e.g. `b → c` in `a ∧ b → c`),
                                          // re-associate to `(a ∧ b) → c`. A pure `a ∧ (b ∧ c)` right operand
                                          // is NOT an arrow, so right-associativity of `∧` is preserved.
            Ok(Self::build_connective_arrow_aware("And", left, right))
        } else if self.eat(&TokenKind::AmpAmp) {
            // Bool.and via the heterogeneous `&&` operator (also infixr:35).
            let right = self.and_expr()?; // right-associative: a && (b && c)
            let s = span.merge(right.span());
            Ok(SurfaceExpr::App(
                s,
                Box::new(SurfaceExpr::Ident(span, "and".to_string())),
                vec![SurfaceArg::positional(left), SurfaceArg::positional(right)],
            ))
        } else {
            Ok(left)
        }
    }

    /// Surface spelling of the current token IF it is one of Lean's `infix:50`
    /// NON-associative comparison / relation operators, else `None`.
    ///
    /// Sources (Lean v4.30): `Init/Notation.lean:375-381` (`≤`, `<`, `≥`, `>`,
    /// `=`, `==`), `Init/Core.lean:878` (`≠`), `Init/Core.lean:775` (`!=`),
    /// `Init/Notation.lean:381` (`≍`, HEq), `Init/Notation.lean:420-422`
    /// (`∈`, `∉`), `Init/Core.lean:539,542` (`⊆`, `⊂`). Every one is declared
    /// `infix:50` (or `notation:50 a:50 … b:50`), i.e. non-chaining. `≃` (Equiv)
    /// is deliberately excluded: it is Mathlib, not core, and its associativity
    /// is unverified here, so the enforcement below leaves it untouched.
    pub(super) fn comparison_op_spelling(&self) -> Option<&'static str> {
        Some(match self.current_kind() {
            TokenKind::Eq => "=",
            TokenKind::Ne => "≠",
            TokenKind::BNe => "!=",
            TokenKind::Lt => "<",
            TokenKind::Le => "≤",
            TokenKind::Gt => ">",
            TokenKind::Ge => "≥",
            TokenKind::HEq => "≍",
            TokenKind::Approx => "≈",
            TokenKind::DoubleEq => "==",
            TokenKind::Elem => "∈",
            TokenKind::NotElem => "∉",
            TokenKind::Subset => "⊆",
            TokenKind::ProperSubset => "⊂",
            TokenKind::Dvd => "∣",
            _ => return None,
        })
    }

    /// Comparison expressions: A = B, A ≠ B, A < B, A ≤ B, etc.
    /// Build `head left right`, splitting an arrow tail off `right` first:
    /// every infix:50 comparison binds TIGHTER than `→`, but `bind_expr`
    /// swallows the arrow into the RHS — `a < b → c` must parse as
    /// `(a < b) → c`, never `a < (b → c)`. Mirrors the long-standing `=`
    /// arm behavior; probed via `x ≠ Nat.zero → Nat` (ExpectedSort(Nat))
    /// and the `<`/`≤`/`∈` analogs.
    fn cmp_with_arrow_tail(
        span: Span,
        head: &str,
        left: SurfaceExpr,
        right: SurfaceExpr,
        end_span: Span,
    ) -> SurfaceExpr {
        let (right, arrow_tail) = match right {
            SurfaceExpr::Arrow(_, domain, codomain) => (*domain, Some(codomain)),
            other => (other, None),
        };
        let cmp = SurfaceExpr::App(
            span.merge(right.span()),
            Box::new(SurfaceExpr::Ident(span, head.to_string())),
            vec![SurfaceArg::positional(left), SurfaceArg::positional(right)],
        );
        match arrow_tail {
            Some(codomain) => SurfaceExpr::Arrow(span.merge(end_span), Box::new(cmp), codomain),
            None => cmp,
        }
    }

    /// Split an arrow tail off a comparison RHS (see [`Self::cmp_with_arrow_tail`]);
    /// for arms with non-standard argument order/wrapping (`∈`, `∉`).
    fn split_arrow_tail(right: SurfaceExpr) -> (SurfaceExpr, Option<Box<SurfaceExpr>>) {
        match right {
            SurfaceExpr::Arrow(_, domain, codomain) => (*domain, Some(codomain)),
            other => (other, None),
        }
    }

    pub(super) fn cmp_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        let mut left = self.bind_expr()?;
        // Tracks whether a 50-class comparison has already been consumed at this
        // level. Set at the END of the loop body for every comparison branch;
        // the two `≃`/Equiv branches `continue` past that assignment so they do
        // NOT participate (see the guard below and `comparison_op_spelling`).
        let mut saw_comparison = false;

        loop {
            // NON-associativity (audit P0-5). Lean declares `=`, `≠`, `!=`, `<`,
            // `≤`, `>`, `≥`, `==`, `≍`, `∈`, `∉`, `⊆`, `⊂` as `infix:50`, so
            // `a = b = c`, `a < b < c`, and even MIXED `a < b = c` are all PARSE
            // ERRORS in Lean (verified against v4.30). Clean historically folded
            // them left-associatively into `(a = b) = c` — which for `Prop`-valued
            // `=` even typechecks, shipping a tree Lean refuses. Once one 50-class
            // comparison is consumed, reject a second at this level loudly. (An
            // intervening looser operator — `→`, `∧`, … — is parsed at a different
            // chain level or swallowed by the `=` arrow-tail split below, so
            // `a = b → c = d` = `(a = b) → (c = d)` never trips this.)
            if saw_comparison {
                if let Some(op) = self.comparison_op_spelling() {
                    return Err(ParseError::UnexpectedToken {
                        line: self.current_line(),
                        col: self.current_span().start,
                        message: format!(
                            "'{op}' is not associative; comparison and equality \
                             operators do not chain in Lean — parenthesize one \
                             side, e.g. `(a = b) = c`"
                        ),
                    });
                }
            }
            let span = left.span();
            if self.eat(&TokenKind::Eq) {
                let right = self.bind_expr()?;
                let end_span = right.span();
                let (right, arrow_tail) = match right {
                    SurfaceExpr::Arrow(_, domain, codomain) => (*domain, Some(codomain)),
                    other => (other, None),
                };
                let eq_expr = SurfaceExpr::App(
                    span.merge(right.span()),
                    Box::new(SurfaceExpr::Ident(span, "Eq".to_string())),
                    vec![SurfaceArg::positional(left), SurfaceArg::positional(right)],
                );
                left = if let Some(codomain) = arrow_tail {
                    SurfaceExpr::Arrow(span.merge(end_span), Box::new(eq_expr), codomain)
                } else {
                    eq_expr
                };
            } else if self.eat(&TokenKind::Ne) {
                let right = self.bind_expr()?;
                let end_span = right.span();
                // Arrow-tail split, exactly as the `=` arm above: `≠` is
                // infix:50 and binds TIGHTER than `→`, but bind_expr swallows
                // the arrow into the RHS — `a ≠ b → c` must be `(a ≠ b) → c`,
                // not `a ≠ (b → c)` (probed: `x ≠ Nat.zero → Nat` produced
                // ExpectedSort(Nat)).
                let (right, arrow_tail) = match right {
                    SurfaceExpr::Arrow(_, domain, codomain) => (*domain, Some(codomain)),
                    other => (other, None),
                };
                let ne_expr = SurfaceExpr::App(
                    span.merge(right.span()),
                    Box::new(SurfaceExpr::Ident(span, "Ne".to_string())),
                    vec![SurfaceArg::positional(left), SurfaceArg::positional(right)],
                );
                left = if let Some(codomain) = arrow_tail {
                    SurfaceExpr::Arrow(span.merge(end_span), Box::new(ne_expr), codomain)
                } else {
                    ne_expr
                };
            } else if self.eat(&TokenKind::BNe) {
                // ASCII `a != b` is Boolean disequality (Bool), distinct from
                // `≠` → `Ne` (Prop). Lean defines `bne a b := !(a == b)`; we
                // desugar directly to `Bool.not (BEq.beq a b)` so resolution
                // reuses the same `==`/`Bool.not` heads clean already supports
                // (no dependence on a `bne` constant being in the prelude).
                let right = self.bind_expr()?;
                let end_span = right.span();
                let s = span.merge(end_span);
                let beq = SurfaceExpr::App(
                    s,
                    Box::new(SurfaceExpr::Ident(span, "BEq.beq".to_string())),
                    vec![SurfaceArg::positional(left), SurfaceArg::positional(right)],
                );
                left = SurfaceExpr::App(
                    s,
                    Box::new(SurfaceExpr::Ident(span, "Bool.not".to_string())),
                    vec![SurfaceArg::positional(beq)],
                );
            } else if self.eat(&TokenKind::Lt) {
                let right = self.bind_expr()?;
                let end_span = right.span();
                left = Self::cmp_with_arrow_tail(span, "LT.lt", left, right, end_span);
            } else if self.eat(&TokenKind::Le) {
                let right = self.bind_expr()?;
                let end_span = right.span();
                left = Self::cmp_with_arrow_tail(span, "LE.le", left, right, end_span);
            } else if self.eat(&TokenKind::Gt) {
                let right = self.bind_expr()?;
                let end_span = right.span();
                left = Self::cmp_with_arrow_tail(span, "GT.gt", left, right, end_span);
            } else if self.eat(&TokenKind::Ge) {
                let right = self.bind_expr()?;
                let end_span = right.span();
                left = Self::cmp_with_arrow_tail(span, "GE.ge", left, right, end_span);
            } else if self.eat(&TokenKind::HEq) {
                // Heterogeneous equality: a ≍ b
                let right = self.bind_expr()?;
                let end_span = right.span();
                left = SurfaceExpr::App(
                    span.merge(end_span),
                    Box::new(SurfaceExpr::Ident(span, "HEq".to_string())),
                    vec![SurfaceArg::positional(left), SurfaceArg::positional(right)],
                );
            } else if self.eat(&TokenKind::Approx) {
                // Setoid / quotient equivalence: `a ≈ b` → `HasEquiv.Equiv a b`
                // (Lean `Init/Core.lean`: `infix:50 " ≈ " => HasEquiv.Equiv`).
                // A non-chaining `infix:50` op like the others here, so it falls
                // through to the `saw_comparison` guard (no `continue`).
                let right = self.bind_expr()?;
                let end_span = right.span();
                left = SurfaceExpr::App(
                    span.merge(end_span),
                    Box::new(SurfaceExpr::Ident(span, "HasEquiv.Equiv".to_string())),
                    vec![SurfaceArg::positional(left), SurfaceArg::positional(right)],
                );
            } else if self.eat(&TokenKind::Equiv) {
                // Check for typed equivalence notation: ≃ₐ[R] (AlgEquiv)
                if let TokenKind::Ident(subscript) = self.current_kind().clone() {
                    if is_typed_equiv_subscript(&subscript)
                        && matches!(self.peek_kind(1), Some(TokenKind::LBracket))
                    {
                        self.advance(); // consume subscript
                        self.expect(&TokenKind::LBracket)?;
                        let param = self.expr()?;
                        self.expect(&TokenKind::RBracket)?;

                        let right = self.bind_expr()?;
                        let end_span = right.span();

                        // Map subscript to type constructor
                        let constructor = typed_equiv_constructor(&subscript);

                        // Build: Constructor param left right
                        // e.g., AlgEquiv R A B for A ≃ₐ[R] B
                        left = SurfaceExpr::App(
                            span.merge(end_span),
                            Box::new(SurfaceExpr::Ident(span, constructor.to_string())),
                            vec![
                                SurfaceArg::positional(param),
                                SurfaceArg::positional(left),
                                SurfaceArg::positional(right),
                            ],
                        );
                        continue;
                    }
                }

                // Plain equivalence/isomorphism: a ≃ b. `≃` (Equiv) is Mathlib,
                // not core; its associativity is unverified here, so it is left
                // OUT of the non-associativity enforcement — `continue` past the
                // `saw_comparison = true` at the end of the loop so a following
                // comparison keeps its historical behavior.
                let right = self.bind_expr()?;
                let end_span = right.span();
                left = SurfaceExpr::App(
                    span.merge(end_span),
                    Box::new(SurfaceExpr::Ident(span, "Equiv".to_string())),
                    vec![SurfaceArg::positional(left), SurfaceArg::positional(right)],
                );
                continue;
            } else if self.eat(&TokenKind::DoubleEq) {
                // BEq equality check: a == b
                let right = self.bind_expr()?;
                let end_span = right.span();
                left = Self::cmp_with_arrow_tail(span, "BEq.beq", left, right, end_span);
            } else if self.eat(&TokenKind::Elem) {
                // Membership: a ∈ b → Membership.mem b a (note argument swap per Lean 4 spec)
                let right = self.bind_expr()?;
                let end_span = right.span();
                let (right, arrow_tail) = Self::split_arrow_tail(right);
                let mem = SurfaceExpr::App(
                    span.merge(right.span()),
                    Box::new(SurfaceExpr::Ident(span, "Membership.mem".to_string())),
                    vec![SurfaceArg::positional(right), SurfaceArg::positional(left)],
                );
                left = match arrow_tail {
                    Some(codomain) => {
                        SurfaceExpr::Arrow(span.merge(end_span), Box::new(mem), codomain)
                    }
                    None => mem,
                };
            } else if self.eat(&TokenKind::NotElem) {
                // Not membership: a ∉ b → ¬(Membership.mem b a)
                let right = self.bind_expr()?;
                let end_span = right.span();
                let (right, arrow_tail) = Self::split_arrow_tail(right);
                let mem_expr = SurfaceExpr::App(
                    span.merge(right.span()),
                    Box::new(SurfaceExpr::Ident(span, "Membership.mem".to_string())),
                    vec![
                        SurfaceArg::positional(right.clone()),
                        SurfaceArg::positional(left),
                    ],
                );
                let not_expr = SurfaceExpr::App(
                    span.merge(right.span()),
                    Box::new(SurfaceExpr::Ident(span, "Not".to_string())),
                    vec![SurfaceArg::positional(mem_expr)],
                );
                left = match arrow_tail {
                    Some(codomain) => {
                        SurfaceExpr::Arrow(span.merge(end_span), Box::new(not_expr), codomain)
                    }
                    None => not_expr,
                };
            } else if self.eat(&TokenKind::Subset) {
                // a ⊆ b → HasSubset.Subset a b (infix:50)
                let right = self.bind_expr()?;
                let end_span = right.span();
                left = Self::cmp_with_arrow_tail(span, "HasSubset.Subset", left, right, end_span);
            } else if self.eat(&TokenKind::ProperSubset) {
                // a ⊂ b → HasSSubset.SSubset a b (infix:50)
                let right = self.bind_expr()?;
                let end_span = right.span();
                left = Self::cmp_with_arrow_tail(span, "HasSSubset.SSubset", left, right, end_span);
            } else if self.eat(&TokenKind::Dvd) {
                // a ∣ b → Dvd.dvd a b (infix:50, non-associative). `∣` (U+2223
                // DIVIDES) is distinct from the ASCII pattern bar `|`.
                let right = self.bind_expr()?;
                let end_span = right.span();
                left = Self::cmp_with_arrow_tail(span, "Dvd.dvd", left, right, end_span);
            } else {
                break;
            }
            // A 50-class comparison operator was consumed this iteration; a
            // second one at the same level is a non-associative chain, caught by
            // the guard at the top of the loop. The `≃`/Equiv branches `continue`
            // above and never reach this assignment.
            saw_comparison = true;
        }

        Ok(left)
    }

    /// Monadic bind: `m >>= f` (HBind.hBind, infixl:55). Binds tighter than the
    /// comparison operators (so `m >>= f = g` parses as `(m >>= f) = g`, matching
    /// Lean 4 where `>>=` is prec 55 and `=` is prec 50) but looser than the
    /// bitwise operators reached via `bitor_expr`.
    ///
    /// Desugars to `Bind.bind m f` — the same head the `do`-notation desugarer
    /// emits — so the existing monad-instance resolution path applies unchanged.
    pub(super) fn bind_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        let mut left = self.seq_expr()?;
        // Tracks whether a left-associative `>>=` (infixl:55) was consumed at
        // this level. The infixr:55 operators (`=<<`, `>=>`, `<=<`) require a
        // left operand tighter than 55, so they cannot follow a `>>=` result at
        // the same level — Lean rejects `a >>= f =<< b` with "expected end of
        // input". We reproduce that rejection instead of silently regrouping.
        let mut saw_bind = false;
        loop {
            if self.eat(&TokenKind::Bind) {
                let span = left.span();
                // infixl:55 — right operand at level 56.
                let right = self.with_custom_min_prec(56, Self::seq_expr)?;
                let s = span.merge(right.span());
                left = SurfaceExpr::App(
                    s,
                    Box::new(SurfaceExpr::Ident(span, "Bind.bind".to_string())),
                    vec![SurfaceArg::positional(left), SurfaceArg::positional(right)],
                );
                saw_bind = true;
            } else if let Some((head, sym)) = match self.current_kind() {
                TokenKind::BindLeft => Some(("Bind.bindLeft", "=<<")),
                TokenKind::KleisliR => Some(("Bind.kleisliRight", ">=>")),
                TokenKind::KleisliL => Some(("Bind.kleisliLeft", "<=<")),
                _ => None,
            } {
                if saw_bind {
                    return Err(ParseError::UnexpectedToken {
                        line: self.current_line(),
                        col: self.current_span().start,
                        message: format!(
                            "'{sym}' (infixr:55) cannot extend a left-associative \
                             '>>=' (infixl:55) result — parenthesize one side"
                        ),
                    });
                }
                let span = left.span();
                self.advance();
                // infixr:55 — right operand recurses at the same bind level.
                let right = self.with_custom_min_prec(55, Self::bind_expr)?;
                let s = span.merge(right.span());
                return Ok(SurfaceExpr::App(
                    s,
                    Box::new(SurfaceExpr::Ident(span, head.to_string())),
                    vec![SurfaceArg::positional(left), SurfaceArg::positional(right)],
                ));
            } else {
                break;
            }
        }
        Ok(left)
    }

    /// Sequencing / applicative operators at Lean precedence 60:
    /// `>>` (HAndThen.hAndThen, `syntax:60 term:61 " >> " term:60`, right-leaning),
    /// `<*>` (Seq.seq), `<*` (SeqLeft.seqLeft), `*>` (SeqRight.seqRight) — the last
    /// three `syntax:60 term:60 op term:61`, LEFT-associative and mutually
    /// interleaving. `>>` needs a left operand tighter than 60, so it cannot
    /// follow a `<*>`/`<*`/`*>` result at the same level (Lean: `a *> b >> c` is
    /// "expected end of input"); its right operand is `term:60`, so `a >> b *> c`
    /// = `a >> (b *> c)` and `m >> n >> o` right-nests.
    ///
    /// Desugars each operator to `<Head> lhs (fun _ : Unit => rhs)` — the RHS
    /// unit-thunk Lean inserts syntactically for `<*> <* *>` (`Init/
    /// Prelude.lean` macro_rules) and through `binop_lazy%` for `>>`
    /// (`Lean/Elab/Extra.lean:92`); see [`Self::unit_thunk`] (Brick 3).
    pub(super) fn seq_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        let mut left = self.bitor_expr()?;
        // Set once a left-associative level-60 op (`<*>`/`<*`/`*>`) is consumed,
        // making `left` a level-60 result that `>>` (needs 61) may not use.
        let mut saw_left_assoc = false;
        loop {
            if matches!(self.current_kind(), TokenKind::Seq) {
                if saw_left_assoc {
                    return Err(ParseError::UnexpectedToken {
                        line: self.current_line(),
                        col: self.current_span().start,
                        message: "'>>' (term:61 lhs) cannot extend a '<*>'/'<*'/'*>' \
                                  result at precedence 60 — parenthesize one side"
                            .to_string(),
                    });
                }
                let span = left.span();
                self.advance();
                // `>>` is right-associative: rhs parses at level 60 (this level).
                let right = self.with_custom_min_prec(60, Self::seq_expr)?;
                let s = span.merge(right.span());
                return Ok(SurfaceExpr::App(
                    s,
                    Box::new(SurfaceExpr::Ident(span, "HAndThen.hAndThen".to_string())),
                    vec![
                        SurfaceArg::positional(left),
                        SurfaceArg::positional(Self::unit_thunk(right)),
                    ],
                ));
            }
            let head = match self.current_kind() {
                TokenKind::SeqAp => "Seq.seq",
                TokenKind::SeqLeft => "SeqLeft.seqLeft",
                TokenKind::AndThen => "SeqRight.seqRight",
                _ => break,
            };
            let span = left.span();
            self.advance();
            // Left-associative: right operand parses at level 61 (`bitor_expr`).
            let right = self.with_custom_min_prec(61, Self::bitor_expr)?;
            let s = span.merge(right.span());
            left = SurfaceExpr::App(
                s,
                Box::new(SurfaceExpr::Ident(span, head.to_string())),
                vec![
                    SurfaceArg::positional(left),
                    SurfaceArg::positional(Self::unit_thunk(right)),
                ],
            );
            saw_left_assoc = true;
        }
        Ok(left)
    }

    /// Functor map `f <$> x` (Functor.map) and reverse map `x <&> f`
    /// (Functor.mapRev) — both `infixr:100` in Lean 4, sharing this level and
    /// right-associative: `f <$> a <&> g` = `f <$> (a <&> g)`. This is the
    /// TIGHTEST binary level in the chain (below only application/atoms), so
    /// `f <$> a + b` = `(f <$> a) + b`, `f <$> a ^ b` = `(f <$> a) ^ b`, and
    /// `f ∘ g <$> x` = `f ∘ (g <$> x)`. Operands descend through `unary_expr`
    /// (application binds tighter still).
    ///
    /// Desugars to `Functor.map f x` / `Functor.mapRev x f`, the standard Lean 4
    /// heads (source order), so the existing instance-resolution path applies.
    pub(super) fn map_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        let left = self.unary_expr()?;
        let head = match self.current_kind() {
            TokenKind::LeftDollarArrow => "Functor.map", // <$>
            TokenKind::MapRev => "Functor.mapRev",       // <&>
            _ => return Ok(left),
        };
        let span = left.span();
        self.advance();
        // Right-associative (infixr:100): recurse on the right so `f <$> g <$> x`
        // parses as `f <$> (g <$> x)` and `f <$> a <&> g` as `f <$> (a <&> g)`.
        let right = self.with_custom_min_prec(100, Self::map_expr)?;
        let s = span.merge(right.span());
        Ok(SurfaceExpr::App(
            s,
            Box::new(SurfaceExpr::Ident(span, head.to_string())),
            vec![SurfaceArg::positional(left), SurfaceArg::positional(right)],
        ))
    }

    /// Bitwise OR: A ||| B (HOr.hOr, infixl:55). Binds looser than `^^^`/`&&&`
    /// but tighter than the comparison operators — matching Lean 4 precedences.
    pub(super) fn bitor_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        let mut left = self.bitxor_expr()?;
        while self.eat(&TokenKind::BitOr) {
            let span = left.span();
            // infixl:55 — right operand at level 56.
            let right = self.with_custom_min_prec(56, Self::bitxor_expr)?;
            let s = span.merge(right.span());
            left = SurfaceExpr::App(
                s,
                Box::new(SurfaceExpr::Ident(span, "HOr.hOr".to_string())),
                vec![SurfaceArg::positional(left), SurfaceArg::positional(right)],
            );
        }
        Ok(left)
    }

    /// Bitwise XOR: A ^^^ B (HXor.hXor, infixl:58).
    pub(super) fn bitxor_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        let mut left = self.bitand_expr()?;
        while self.eat(&TokenKind::BitXor) {
            let span = left.span();
            // infixl:58 — right operand at level 59.
            let right = self.with_custom_min_prec(59, Self::bitand_expr)?;
            let s = span.merge(right.span());
            left = SurfaceExpr::App(
                s,
                Box::new(SurfaceExpr::Ident(span, "HXor.hXor".to_string())),
                vec![SurfaceArg::positional(left), SurfaceArg::positional(right)],
            );
        }
        Ok(left)
    }

    /// Bitwise AND: A &&& B (HAnd.hAnd, infixl:60). Binds tighter than `|||`/`^^^`
    /// but looser than `+`/`-` (reached via `arrow_expr → … → add_expr`).
    pub(super) fn bitand_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        let mut left = self.arrow_expr()?;
        while self.eat(&TokenKind::BitAnd) {
            let span = left.span();
            // infixl:60 — right operand at level 61.
            let right = self.with_custom_min_prec(61, Self::arrow_expr)?;
            let s = span.merge(right.span());
            left = SurfaceExpr::App(
                s,
                Box::new(SurfaceExpr::Ident(span, "HAnd.hAnd".to_string())),
                vec![SurfaceArg::positional(left), SurfaceArg::positional(right)],
            );
        }
        Ok(left)
    }

    /// Arrow types: A → B (right associative)
    pub(super) fn arrow_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        // Attempt to parse binder-style pi types: (x : T) → U, {x : T} → U, [x : T] → U
        // Use lookahead to avoid exponential backtracking on nested brackets/parens
        let saved_pos = self.pos;
        // The speculative `binders()` below may recognize a parenthesized
        // bounded binder (`(x ∈ s)`, `(r ≥ w)`) and stash its guard in
        // `pending_binder_guards`. Both exits must account for that stash:
        // on backtrack the tokens re-parse as a plain expression, so a
        // retained guard would smuggle a spurious antecedent into whatever
        // quantifier drains the stash next (found via the trust bridge:
        // `(hs : ¬(r ≥ Int.ofNat w))` in a ∀ body grew a phantom
        // `r ≥ Int.ofNat w →` around the body); on a successful Pi parse the
        // guards belong to THIS arrow's binders and must wrap THIS body.
        let saved_guards = self.pending_binder_guards.len();
        if self.looks_like_binder_start() {
            if let Ok(binders) = self.binders() {
                // A guard stashed during this speculation means `binders()`
                // consumed a parenthesized bounded binder (`(n > 0)`,
                // `(x ∈ s)`). That sugar belongs to QUANTIFIERS only (Lean's
                // binder predicates); in arrow position `(n > 0) → U` is a
                // plain arrow whose domain is the proposition `n > 0`, and in
                // a type ascription like `(hs : ¬(r ≥ w))` the inner group is
                // an ordinary expression. Accepting the binder reading here
                // both mis-parses the arrow AND leaks the stashed guard to
                // whatever quantifier drains it next (found via the trust
                // bridge: a ∀ body grew a phantom `r ≥ Int.ofNat w →`
                // antecedent). Reject the speculation entirely.
                if self.pending_binder_guards.len() == saved_guards && self.eat(&TokenKind::Arrow) {
                    // Pi-type body parses at full precedence (see the normal
                    // arrow case below): `(x : T) → P x = Q` is `… → (P x = Q)`.
                    let body = self.expr()?;
                    let start_span = binders
                        .first()
                        .map_or_else(|| self.current_span(), |b| b.span);
                    let span = start_span.merge(body.span());
                    return Ok(SurfaceExpr::Pi(span, binders, Box::new(body)));
                }
            }
            // Backtrack if this wasn't a binder-arrow form — including any
            // guard the speculative parse stashed.
            self.pos = saved_pos;
            self.pending_binder_guards.truncate(saved_guards);
        }

        let mut left = self.sum_expr()?;

        while self.eat(&TokenKind::Arrow) {
            // Check for typed morphism notation: →ₗ[R], →ₐ[R], ≃ₐ[R]
            // Pattern: Arrow + subscript identifier + [ + param + ]
            if let TokenKind::Ident(subscript) = self.current_kind().clone() {
                if is_typed_morphism_subscript(&subscript)
                    && matches!(self.peek_kind(1), Some(TokenKind::LBracket))
                {
                    self.advance(); // consume subscript
                    self.expect(&TokenKind::LBracket)?;
                    let param = self.expr()?;
                    self.expect(&TokenKind::RBracket)?;

                    let right = self.arrow_expr()?; // Right side of morphism
                    let span = left.span().merge(right.span());

                    // Map subscript to type constructor
                    let constructor = typed_morphism_constructor(&subscript);

                    // Build: Constructor param left right
                    // e.g., LinearMap R P M for P →ₗ[R] M
                    left = SurfaceExpr::App(
                        span,
                        Box::new(SurfaceExpr::Ident(span, constructor.to_string())),
                        vec![
                            SurfaceArg::positional(param),
                            SurfaceArg::positional(left),
                            SurfaceArg::positional(right),
                        ],
                    );
                    continue;
                }
            }

            // Normal arrow type: A → B.
            //
            // `→` is the loosest right-associative operator in Lean (prec 25),
            // so its codomain must parse at FULL expression precedence — it may
            // contain `=`, `∧`, `∨`, etc. Parsing the codomain with `expr()`
            // (rather than the tighter `arrow_expr`) makes `A → B = C` parse as
            // `A → (B = C)` and `A → B ∧ C` as `A → (B ∧ C)`, matching Lean.
            // Right-associativity is preserved because `expr()` descends back
            // into `arrow_expr` for any further `→`. (The companion `A = B → C`
            // case is handled by the arrow-splitting hack in `cmp_expr`.)
            let right = self.expr()?; // Right associative, full-precedence codomain
            let span = left.span().merge(right.span());
            left = SurfaceExpr::Arrow(span, Box::new(left), Box::new(right));
        }

        Ok(left)
    }

    /// Sum type: `A ⊕ B`. RIGHT-associative (Lean's `⊕` is `infixr:30`), so
    /// `A ⊕ B ⊕ C` is `A ⊕ (B ⊕ C)` = `Sum A (Sum B C)`. Precedence 30 sits
    /// between `→` (25, looser, handled by the enclosing `arrow_expr`) and `×`
    /// (35, tighter, `prod_expr`), so `A ⊕ B × C` is `A ⊕ (B × C)` and
    /// `A ⊕ B → C` is `(A ⊕ B) → C`. Desugars to `Sum A B`.
    pub(super) fn sum_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        let left = self.prod_expr()?;

        if self.eat(&TokenKind::Oplus) {
            let right = self.sum_expr()?; // recurse on the right → right-assoc
            let span = left.span().merge(right.span());
            Ok(SurfaceExpr::App(
                span,
                Box::new(SurfaceExpr::Ident(span, "Sum".to_string())),
                vec![SurfaceArg::positional(left), SurfaceArg::positional(right)],
            ))
        } else {
            Ok(left)
        }
    }

    /// If `e` is the value side of a typed binder group — a bare ident (`x`) or
    /// an all-ident application spine (`a b c`, how `(a b : T)` parses before
    /// the ascription) — return the `(span, name)` list; else `None`.
    fn binder_group_names(e: &SurfaceExpr) -> Option<Vec<(Span, String)>> {
        match e {
            SurfaceExpr::Ident(span, name) => Some(vec![(*span, name.clone())]),
            // `_` as a binder name in `(_ : T) × B` / `(_ : T) ×' B` — Lean
            // pretty-prints a non-dependent Sigma/PSigma with an anonymous `_`
            // binder, so round-tripping `(_ : Nat) ×' Nat` (⇒ `PSigma (fun _ :
            // Nat => Nat)`) requires recognizing the hole as the binder.
            SurfaceExpr::Hole(span) => Some(vec![(*span, "_".to_string())]),
            SurfaceExpr::App(_, f, args) => {
                let mut names = Self::binder_group_names(f)?;
                for arg in args {
                    if arg.name.is_some() {
                        return None;
                    }
                    match &arg.expr {
                        SurfaceExpr::Ident(span, name) => names.push((*span, name.clone())),
                        _ => return None,
                    }
                }
                Some(names)
            }
            _ => None,
        }
    }

    /// Product type: `A × B`. RIGHT-associative (Lean's `×` is `infixr:35`), so
    /// `A × B × C` is `A × (B × C)` = `Prod A (Prod B C)`, NOT `(A × B) × C`. A
    /// left fold here mis-typed every 3+-tuple (e.g. `Cid × Clause × List Int`),
    /// making `s.1`/`s.2` projections fail the kernel check.
    pub(super) fn prod_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        // `add_custom_expr` is the additive chain plus the loose custom-operator
        // continuation band (`custom_notation.rs`); a pass-through to `add_expr`
        // when the file declares no notation.
        let left = self.add_custom_expr()?;

        // Anonymous dependent-pair constructors (Lean `macro:35`,
        // `Init/NotationExtra.lean:93-94`): `(x : T) × b` ⇒ `Sigma (fun x : T =>
        // b)` and `(x : T) ×' b` ⇒ `PSigma (fun x : T => b)`. These are how Lean
        // pretty-prints EVERY Sigma/PSigma type, so round-tripping requires them.
        // The disambiguator from a non-dependent `A × B` is a parenthesized TYPED
        // binder group on the left — a single ident parses to `Ascription(Ident,
        // ty)`, a multi-ident group `(a b : T)` to `Ascription(App(a, [b…]), ty)`
        // (all-ident spine). Right-associative at prec 35:
        // `(a : Nat) × (b : Nat) × Fin (a + b)`; multi-ident groups right-nest
        // one Sigma per ident, mirroring `expandBracketedBinders`.
        if matches!(
            self.current_kind(),
            TokenKind::Times | TokenKind::TimesPrime
        ) {
            if let SurfaceExpr::Ascription(_, inner, ty) = &left {
                if let Some(names) = Self::binder_group_names(inner) {
                    let head = if matches!(self.current_kind(), TokenKind::Times) {
                        "Sigma"
                    } else {
                        "PSigma"
                    };
                    let binder_ty = ty.clone();
                    let lspan = left.span();
                    self.advance(); // consume × / ×'
                                    // Body is Lean `term:35`; parse through `cmp_expr` so it
                                    // reaches comparisons/`Dvd`/etc. (prec ≥ 50, tighter than 35)
                                    // AND re-descends into `prod_expr` for a right-associative
                                    // `×`/`×'` chain (`(a : Nat) × (b : Nat) × …`).
                    let rhs = self.cmp_expr()?;
                    let span = lspan.merge(rhs.span());
                    let mut result = rhs;
                    for (bspan, name) in names.into_iter().rev() {
                        let binder = SurfaceBinder {
                            span: bspan,
                            name,
                            ty: Some(binder_ty.clone()),
                            default: None,
                            info: SurfaceBinderInfo::Explicit,
                        };
                        let lambda = SurfaceExpr::Lambda(span, vec![binder], Box::new(result));
                        result = SurfaceExpr::App(
                            span,
                            Box::new(SurfaceExpr::Ident(lspan, head.to_string())),
                            vec![SurfaceArg::positional(lambda)],
                        );
                    }
                    return Ok(result);
                }
            }
        }

        if self.eat(&TokenKind::Times) {
            let right = self.prod_expr()?; // recurse on the right → right-assoc
            let span = left.span().merge(right.span());
            Ok(SurfaceExpr::App(
                span,
                Box::new(SurfaceExpr::Ident(span, "Prod".to_string())),
                vec![SurfaceArg::positional(left), SurfaceArg::positional(right)],
            ))
        } else if self.eat(&TokenKind::TimesPrime) {
            // Non-dependent `A ×' B` (the left is a plain type, not a `(x : T)`
            // binder group handled above) ⇒ `PSigma (fun (_ : A) => B)` — Lean's
            // `×'` notation for a non-dependent dependent-pair. Right-associative,
            // mirroring the `A × B` → `Prod` fold above.
            let left_span = left.span();
            let right = self.prod_expr()?;
            let span = left_span.merge(right.span());
            let binder = SurfaceBinder {
                span: left_span,
                name: "_".to_string(),
                ty: Some(Box::new(left)),
                default: None,
                info: SurfaceBinderInfo::Explicit,
            };
            let lambda = SurfaceExpr::Lambda(span, vec![binder], Box::new(right));
            Ok(SurfaceExpr::App(
                span,
                Box::new(SurfaceExpr::Ident(span, "PSigma".to_string())),
                vec![SurfaceArg::positional(lambda)],
            ))
        } else {
            Ok(left)
        }
    }

    /// Additive expressions: A + B, A - B
    pub(super) fn add_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        let mut left = self.cons_expr()?;

        loop {
            let span = left.span();
            if self.eat(&TokenKind::Plus) {
                // Right operand at cons level (67) — consistent with the other
                // `add`-level branches below — so tighter `::`/`⊔`/`⊓` bind into
                // the RHS: `a + b :: c` = `a + (b :: c)`, `a + b ⊔ c` = `a + (b ⊔ c)`.
                let right = self.with_custom_min_prec(66, Self::cons_expr)?;
                let end_span = right.span();
                left = SurfaceExpr::App(
                    span.merge(end_span),
                    Box::new(SurfaceExpr::Ident(span, "HAdd.hAdd".to_string())),
                    vec![SurfaceArg::positional(left), SurfaceArg::positional(right)],
                );
            } else if self.eat(&TokenKind::Minus) {
                let right = self.with_custom_min_prec(66, Self::cons_expr)?;
                let end_span = right.span();
                left = SurfaceExpr::App(
                    span.merge(end_span),
                    Box::new(SurfaceExpr::Ident(span, "HSub.hSub".to_string())),
                    vec![SurfaceArg::positional(left), SurfaceArg::positional(right)],
                );
            } else if self.eat(&TokenKind::PlusPlus) {
                // Append: a ++ b → HAppend.hAppend a b (Lean 4 infixl:65,
                // left-assoc, same precedence as + / -). Resolves through the
                // HAppend instance for the operand types (instHAppendString for
                // String). Before this branch the lexer split `++` into two
                // `Plus` tokens, parsing `a ++ b` as `HAdd.hAdd a b` with a
                // no-op prefix `+` — no String HAdd instance existed, so the
                // body leaked a fresh metavariable ("contains free variables").
                let right = self.with_custom_min_prec(66, Self::cons_expr)?;
                let end_span = right.span();
                left = SurfaceExpr::App(
                    span.merge(end_span),
                    Box::new(SurfaceExpr::Ident(span, "HAppend.hAppend".to_string())),
                    vec![SurfaceArg::positional(left), SurfaceArg::positional(right)],
                );
            } else if self.eat(&TokenKind::DotDot) {
                // Range: a..b → Set.Icc a b (Lean 4 infixl:68, used in ∫ x in a..b)
                let right = self.with_custom_min_prec(66, Self::cons_expr)?;
                let end_span = right.span();
                left = SurfaceExpr::App(
                    span.merge(end_span),
                    Box::new(SurfaceExpr::Ident(span, "Set.Icc".to_string())),
                    vec![SurfaceArg::positional(left), SurfaceArg::positional(right)],
                );
            } else if self.eat(&TokenKind::Union) {
                // Set union: a ∪ b → Union.union a b (Lean 4 infixl:65)
                let right = self.with_custom_min_prec(66, Self::cons_expr)?;
                let end_span = right.span();
                left = SurfaceExpr::App(
                    span.merge(end_span),
                    Box::new(SurfaceExpr::Ident(span, "Union.union".to_string())),
                    vec![SurfaceArg::positional(left), SurfaceArg::positional(right)],
                );
            } else {
                break;
            }
        }

        Ok(left)
    }

    /// Cons operator: x :: xs (right associative, precedence 67)
    pub(super) fn cons_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        let left = self.sup_expr()?;

        if self.eat(&TokenKind::ColonColon) {
            // infixr:67 — right operand at level 67 (right-associative).
            let right = self.with_custom_min_prec(67, Self::cons_expr)?;
            let span = left.span().merge(right.span());
            Ok(SurfaceExpr::App(
                span,
                Box::new(SurfaceExpr::Ident(span, "List.cons".to_string())),
                vec![SurfaceArg::positional(left), SurfaceArg::positional(right)],
            ))
        } else {
            Ok(left)
        }
    }

    /// Lattice join `a ⊔ b` → `Max.max a b` (Lean `Order/Notation.lean`:
    /// `syntax:68 term:68 " ⊔ " term:69`, left-associative, `macro_rules =>
    /// Max.max`). Sits between `::`/cons (67) and `⊓`/inf (69): binds looser
    /// than `⊓` and `*`, tighter than `+` and `::`.
    pub(super) fn sup_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        let mut left = self.inf_expr()?;
        while self.eat(&TokenKind::Sup) {
            let span = left.span();
            // left-associative at 68 — right operand at level 69.
            let right = self.with_custom_min_prec(69, Self::inf_expr)?;
            let end_span = right.span();
            left = SurfaceExpr::App(
                span.merge(end_span),
                Box::new(SurfaceExpr::Ident(span, "Max.max".to_string())),
                vec![SurfaceArg::positional(left), SurfaceArg::positional(right)],
            );
        }
        Ok(left)
    }

    /// Lattice meet `a ⊓ b` → `Min.min a b` (Lean `syntax:69 term:69 " ⊓ "
    /// term:70`, left-associative). Binds tighter than `⊔` (68), looser than
    /// `*` (70).
    pub(super) fn inf_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        let mut left = self.mul_expr()?;
        while self.eat(&TokenKind::Inf) {
            let span = left.span();
            // left-associative at 69 — right operand at level 70.
            let right = self.with_custom_min_prec(70, Self::mul_expr)?;
            let end_span = right.span();
            left = SurfaceExpr::App(
                span.merge(end_span),
                Box::new(SurfaceExpr::Ident(span, "Min.min".to_string())),
                vec![SurfaceArg::positional(left), SurfaceArg::positional(right)],
            );
        }
        Ok(left)
    }

    /// Category-morphism composition `f ≫ g` → `CategoryStruct.comp f g` (Lean
    /// `CategoryTheory/Category/Basic`: `scoped infixr:80 " ≫ "`,
    /// right-associative). Sits between pow/shift (75) and `×ˢ` (82): binds
    /// tighter than `^`/`*`, looser than `×ˢ`. (Category composition rarely
    /// mixes with arithmetic, but the precedence is placed faithfully.)
    pub(super) fn comp_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        let left = self.setprod_expr()?;
        if self.eat(&TokenKind::CatComp) {
            // infixr:80 — right operand at level 80 (right-associative).
            let right = self.with_custom_min_prec(80, Self::comp_expr)?;
            let span = left.span().merge(right.span());
            Ok(SurfaceExpr::App(
                span,
                Box::new(SurfaceExpr::Ident(span, "CategoryStruct.comp".to_string())),
                vec![SurfaceArg::positional(left), SurfaceArg::positional(right)],
            ))
        } else {
            Ok(left)
        }
    }

    /// Set/Finset product `a ×ˢ b` → `SProd.sprod a b` (Lean `Data/Set/Prod`:
    /// `infixr:82 " ×ˢ " => SProd.sprod`, right-associative). Sits between
    /// `≫` (80) and `∘`/compose (90): binds tighter than `≫`, looser than `∘`.
    pub(super) fn setprod_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        let left = self.compose_expr()?;
        if self.eat(&TokenKind::SetProd) {
            // infixr:82 — right operand at level 82 (right-associative).
            let right = self.with_custom_min_prec(82, Self::setprod_expr)?;
            let span = left.span().merge(right.span());
            Ok(SurfaceExpr::App(
                span,
                Box::new(SurfaceExpr::Ident(span, "SProd.sprod".to_string())),
                vec![SurfaceArg::positional(left), SurfaceArg::positional(right)],
            ))
        } else {
            Ok(left)
        }
    }

    /// Exponentiation `A ^ B` (right-assoc) and the bit-shift operators
    /// `A <<< B` / `A >>> B` (HShiftLeft/HShiftRight, infixl:75). All three share
    /// precedence 75 — higher than `* /` — but the shifts are left-associative.
    pub(super) fn pow_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        let mut left = self.comp_expr()?;
        loop {
            let span = left.span();
            if self.eat(&TokenKind::Caret) {
                // infixr:75 — right operand at level 75 (right-associative).
                let right = self.with_custom_min_prec(75, Self::pow_expr)?;
                let s = span.merge(right.span());
                return Ok(SurfaceExpr::App(
                    s,
                    Box::new(SurfaceExpr::Ident(span, "HPow.hPow".to_string())),
                    vec![SurfaceArg::positional(left), SurfaceArg::positional(right)],
                ));
            } else if self.eat(&TokenKind::ShiftL) {
                // infixl:75 shift — right operand at level 76 (left-associative).
                let right = self.with_custom_min_prec(76, Self::comp_expr)?;
                let s = span.merge(right.span());
                left = SurfaceExpr::App(
                    s,
                    Box::new(SurfaceExpr::Ident(
                        span,
                        "HShiftLeft.hShiftLeft".to_string(),
                    )),
                    vec![SurfaceArg::positional(left), SurfaceArg::positional(right)],
                );
            } else if self.eat(&TokenKind::ShiftR) {
                // infixl:75 shift — right operand at level 76 (left-associative).
                let right = self.with_custom_min_prec(76, Self::comp_expr)?;
                let s = span.merge(right.span());
                left = SurfaceExpr::App(
                    s,
                    Box::new(SurfaceExpr::Ident(
                        span,
                        "HShiftRight.hShiftRight".to_string(),
                    )),
                    vec![SurfaceArg::positional(left), SurfaceArg::positional(right)],
                );
            } else {
                return Ok(left);
            }
        }
    }

    /// Function composition: f ∘ g (right associative, Lean 4 infixr:90). Its
    /// operands descend through `map_expr` (`<$>`/`<&>`, infixr:100), so
    /// `f ∘ g <$> x` = `f ∘ (g <$> x)`.
    pub(super) fn compose_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        let left = self.map_expr()?;
        if self.eat(&TokenKind::Compose) {
            // infixr:90 — right operand at level 90 (right-associative).
            let right = self.with_custom_min_prec(90, Self::compose_expr)?;
            let span = left.span().merge(right.span());
            Ok(SurfaceExpr::App(
                span,
                Box::new(SurfaceExpr::Ident(span, "Function.comp".to_string())),
                vec![SurfaceArg::positional(left), SurfaceArg::positional(right)],
            ))
        } else {
            Ok(left)
        }
    }

    /// Scalar multiplication `a • b` (HSMul.hSMul, `infixr:73` —
    /// `Init/Notation.lean:296`). RIGHT-associative (`a • b • c` = `a • (b • c)`,
    /// verified with a non-associative witness). Precedence 73 sits strictly
    /// between `*` (70, its `mul_expr` caller) and `▸` (75, `subst_expr`), so
    /// `a * b • c` = `a * (b • c)`, `a + b • c` = `a + (b • c)`, `a • b ^ c` =
    /// `a • (b ^ c)`, and `a • b ▸ c` = `a • (b ▸ c)`. Desugars to `HSMul.hSMul
    /// a b` (the `leftact%` wrapper only affects elaborator coercion placement,
    /// not the parse-tree head). `•` (U+2022 BULLET) is distinct from the `·`
    /// (U+00B7) section placeholder.
    pub(super) fn smul_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        let left = self.subst_expr()?;
        if self.eat(&TokenKind::Smul) {
            let span = left.span();
            // infixr:73 — right operand at level 73 (right-associative).
            let right = self.with_custom_min_prec(73, Self::smul_expr)?;
            let s = span.merge(right.span());
            return Ok(SurfaceExpr::App(
                s,
                Box::new(SurfaceExpr::Ident(span, "HSMul.hSMul".to_string())),
                vec![SurfaceArg::positional(left), SurfaceArg::positional(right)],
            ));
        }
        Ok(left)
    }

    /// Rewrite / substitution `a ▸ b` (Term.subst, `trailing_parser:75`, right —
    /// `Lean/Parser/Term.lean:922`). The `sepBy1` separator arm is unreachable
    /// (the element parser at prec 75 consumes the next `▸` first), so it is a
    /// plain `infixr:75`: `a ▸ b ▸ c` = `a ▸ (b ▸ c)`. Precedence 75 binds
    /// tighter than `•` (73) and looser than `^` (80): `a ▸ b + c` = `(a ▸ b) + c`
    /// while `a + b ▸ c` = `a + (b ▸ c)`.
    ///
    /// Desugars to `Eq.rec a b` — the head Lean's `elabSubst` ultimately builds
    /// (via `mkEqRec`). The real subst elaborator is motive/orientation-driven
    /// and cannot be a fixed application, so this parse is Lean-shaped but
    /// elaboration of the two-argument form may fail loudly where clean-elab
    /// lacks the builtin.
    pub(super) fn subst_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        let left = self.neg_expr()?;
        if self.eat(&TokenKind::Subst) {
            let span = left.span();
            // infixr:75 — right operand at level 75 (right-to-left rewrite).
            let right = self.with_custom_min_prec(75, Self::subst_expr)?;
            let s = span.merge(right.span());
            return Ok(SurfaceExpr::App(
                s,
                Box::new(SurfaceExpr::Ident(span, "Eq.rec".to_string())),
                vec![SurfaceArg::positional(left), SurfaceArg::positional(right)],
            ));
        }
        Ok(left)
    }

    /// Prefix unary minus `-a` (`Neg.neg`) and no-op unary plus `+a`.
    ///
    /// Lean declares `-` as `prefix:75` (`Init/Notation.lean:293`): it binds
    /// LOOSER than `^` (`infixr:80`, `Init/Notation.lean:291`) but TIGHTER than
    /// `*`/`/`/`%` (`infixl:70`). So `-3 ^ 2` = `-(3 ^ 2)` = -9 and
    /// `-3 * 2` = `(-3) * 2` = -6 (verified `#eval` against Lean v4.30). The
    /// prefix argument is parsed at precedence 75, which in this hand-written
    /// chain is exactly `pow_expr` and everything tighter (`^` 80, `∘` 90,
    /// application, atoms) but NOT `*` 70. Nested negation `- -a` = `-(-a)`
    /// recurses back through `neg_expr`.
    ///
    /// This level sits between `mul_expr` (70, its caller) and `pow_expr` (80).
    /// Previously the prefix minus lived at the BOTTOM of the precedence chain
    /// (below `pow_expr`/`compose_expr`), so `-3 ^ 2` mis-parsed as `(-3) ^ 2`
    /// = 9 instead of Lean's `-(3 ^ 2)` = -9 — a SILENT wrong value the kernel
    /// re-check cannot catch (audit P0-1). Because the argument descends into
    /// `pow_expr` (not into `neg_expr` again), a bare `-` in a `^`/`∘` right
    /// operand — `2 ^ -3` — stays a loud error, matching Lean's rejection
    /// (`2 ^ -3`: "unexpected token at this precedence level"; use `2 ^ (-3)`).
    pub(super) fn neg_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        match self.current_kind() {
            TokenKind::Minus => {
                let start_span = self.current_span();
                self.advance();
                // prefix:75 — operand at level 75; nested `- -a` = `-(-a)`.
                let inner = self.with_custom_min_prec(75, Self::neg_expr)?;
                let span = start_span.merge(inner.span());
                Ok(SurfaceExpr::App(
                    span,
                    Box::new(SurfaceExpr::Ident(span, "Neg.neg".to_string())),
                    vec![SurfaceArg::positional(inner)],
                ))
            }
            TokenKind::Plus => {
                // Unary plus is a no-op; consume and parse the operand
                // (prefix:75, like unary minus above).
                self.advance();
                self.with_custom_min_prec(75, Self::neg_expr)
            }
            _ => self.pow_expr(),
        }
    }

    /// Post-prefix operator level: user-declared fixed-arity operators followed
    /// by application.
    ///
    /// Prefix unary minus/plus now live one level up in [`Self::neg_expr`] (Lean
    /// `prefix:75`, between `*` 70 and `^` 80); this method is the transparent
    /// hop into `custom_op_expr` retained for its existing call sites
    /// (`compose_expr`, and `¬`'s operand in `app_expr`). `custom_op_expr`
    /// recognizes user-declared `infixl`/`infixr`/`prefix`/`postfix` operators;
    /// when none are registered it is a pass-through to `app_expr`, leaving
    /// built-in operator parsing unchanged.
    pub(super) fn unary_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        self.custom_op_expr()
    }
}

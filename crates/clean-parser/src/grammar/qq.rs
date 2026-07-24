// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::Parser;
use crate::lexer::TokenKind;
use crate::surface::*;
use crate::ParseError;

impl Parser {
    // =========================================================================
    // Qq quotation parsing
    // =========================================================================

    /// Parse the body of a q(...) value quotation
    ///
    /// This handles antiquotations (`$x`, `$(expr)`, `$(x:type)`) within the
    /// quotation body.
    ///
    /// Part of #16: Qq quotation support
    pub(super) fn parse_q_body(&mut self) -> Result<SurfaceExpr, ParseError> {
        // Parse a full expression that can include antiquotations and infix operators
        // The antiquotation handling is done in qq_atom_expr
        self.qq_expr()
    }

    /// Parse an expression in Qq context (handles $ as antiquotation)
    /// This follows the same precedence hierarchy as normal expressions.
    /// Phase 3: Extended to support arrow, let, if, and ascription.
    pub(super) fn qq_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        // Start at the top-level expression precedence (arrow)
        self.qq_arrow_expr()
    }

    /// Qq-aware arrow types: $A -> $B (right associative)
    /// Part of #80: qq_expr parser extensions - Phase 3
    pub(super) fn qq_arrow_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        let mut left = self.qq_add_expr()?;

        while self.eat(&TokenKind::Arrow) {
            let right = self.qq_arrow_expr()?; // Right associative
            let span = left.span().merge(right.span());
            left = SurfaceExpr::Arrow(span, Box::new(left), Box::new(right));
        }

        Ok(left)
    }

    /// Qq-aware additive expressions: $a + $b
    pub(super) fn qq_add_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        let mut left = self.qq_mul_expr()?;

        loop {
            let span = left.span();
            if self.eat(&TokenKind::Plus) {
                let right = self.qq_mul_expr()?;
                let end_span = right.span();
                left = SurfaceExpr::App(
                    span.merge(end_span),
                    Box::new(SurfaceExpr::Ident(span, "HAdd.hAdd".to_string())),
                    vec![SurfaceArg::positional(left), SurfaceArg::positional(right)],
                );
            } else if self.eat(&TokenKind::Minus) {
                let right = self.qq_mul_expr()?;
                let end_span = right.span();
                left = SurfaceExpr::App(
                    span.merge(end_span),
                    Box::new(SurfaceExpr::Ident(span, "HSub.hSub".to_string())),
                    vec![SurfaceArg::positional(left), SurfaceArg::positional(right)],
                );
            } else {
                break;
            }
        }

        Ok(left)
    }

    /// Qq-aware multiplicative expressions: $a * $b
    pub(super) fn qq_mul_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        let mut left = self.qq_app_expr()?;

        loop {
            let span = left.span();
            if self.eat(&TokenKind::Star) {
                let right = self.qq_app_expr()?;
                let end_span = right.span();
                left = SurfaceExpr::App(
                    span.merge(end_span),
                    Box::new(SurfaceExpr::Ident(span, "HMul.hMul".to_string())),
                    vec![SurfaceArg::positional(left), SurfaceArg::positional(right)],
                );
            } else if self.eat(&TokenKind::Slash) {
                let right = self.qq_app_expr()?;
                let end_span = right.span();
                left = SurfaceExpr::App(
                    span.merge(end_span),
                    Box::new(SurfaceExpr::Ident(span, "HDiv.hDiv".to_string())),
                    vec![SurfaceArg::positional(left), SurfaceArg::positional(right)],
                );
            } else {
                break;
            }
        }

        Ok(left)
    }

    /// Qq-aware application expressions: f $x or $f x
    /// Also handles projections (Nat.add, x.field) and universe instantiation (Foo.{u});
    /// dotted names remain projections and are resolved by the elaborator.
    pub(super) fn qq_app_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        let mut expr = self.qq_atom_expr()?;
        let mut pending_args: Vec<SurfaceArg> = Vec::new();

        loop {
            // Check for Dot FIRST - if followed by ident/number, it's a projection.
            // If followed by {, it's universe instantiation (Foo.{u v})
            if self.check(&TokenKind::Dot) {
                // Peek at what follows the dot
                let is_projection = match self.peek_kind(1) {
                    Some(TokenKind::Ident(_) | TokenKind::NatLit(_)) => true,
                    Some(other) => other.as_keyword_str().is_some(),
                    None => false,
                };
                let is_universe_inst = matches!(self.peek_kind(1), Some(TokenKind::LBrace));

                if is_universe_inst {
                    self.advance(); // consume the dot
                    self.advance(); // consume the {

                    // Parse universe levels: `Foo.{u, v, w}` (Lean canonical
                    // comma-separated form); space-separated also accepted.
                    let mut levels = Vec::new();
                    while !self.check(&TokenKind::RBrace) && !self.check(&TokenKind::Eof) {
                        levels.push(self.level_expr()?);
                        if self.check(&TokenKind::Comma) {
                            self.advance();
                        }
                    }
                    self.expect(&TokenKind::RBrace)?;

                    let end_span = self.current_span();
                    let span = expr.span().merge(end_span);
                    expr = SurfaceExpr::UniverseInst(span, Box::new(expr), levels);
                    continue;
                }

                if is_projection {
                    self.advance(); // consume the dot

                    // Projection attaches to the last argument, not the whole application.
                    let proj_base = if let Some(last_arg) = pending_args.pop() {
                        last_arg.expr
                    } else {
                        let span = expr.span();
                        std::mem::replace(&mut expr, SurfaceExpr::Hole(span))
                    };

                    let (projection, end_span) = match self.current_kind().clone() {
                        TokenKind::Ident(field) => {
                            let end_span = self.current_span();
                            self.advance();
                            (Projection::Named(field), end_span)
                        }
                        TokenKind::NatLit(n) => {
                            let end_span = self.current_span();
                            self.advance();
                            let idx = n.to_u64().and_then(|v| u32::try_from(v).ok()).ok_or_else(
                                || ParseError::UnexpectedToken {
                                    line: self.current_line(),
                                    col: self.current_span().start,
                                    message: format!("projection index too large: {n}"),
                                },
                            )?;
                            (Projection::Index(idx), end_span)
                        }
                        other => {
                            if let Some(kw_str) = other.as_keyword_str() {
                                let end_span = self.current_span();
                                self.advance();
                                (Projection::Named(kw_str.to_string()), end_span)
                            } else {
                                unreachable!("peek_kind already checked");
                            }
                        }
                    };

                    let proj_span = proj_base.span().merge(end_span);
                    let projected = SurfaceExpr::Proj(proj_span, Box::new(proj_base), projection);

                    if matches!(&expr, SurfaceExpr::Hole(_)) {
                        expr = projected;
                    } else {
                        pending_args.push(SurfaceArg::positional(projected));
                    }
                    continue;
                }
                // If not a projection, break out of the loop
                break;
            }

            // Check for Qq-specific argument starts ($ or atom)
            if !self.is_qq_arg_start() {
                break;
            }

            let arg = self.qq_atom_expr()?;
            pending_args.push(SurfaceArg::positional(arg));
        }

        // Flush any remaining pending arguments
        if pending_args.is_empty() {
            Ok(expr)
        } else {
            let span = expr.span();
            Ok(SurfaceExpr::App(span, Box::new(expr), pending_args))
        }
    }

    /// Parse an atom in Qq context - handles antiquotation, let, if, ascription
    /// Part of #80: qq_expr parser extensions - Phase 3
    pub(super) fn qq_atom_expr(&mut self) -> Result<SurfaceExpr, ParseError> {
        if self.check(&TokenKind::Dollar) {
            return self.parse_qq_antiquot();
        }

        // Handle let expressions in Qq context
        // Part of #80: let y := $x in y
        if self.check(&TokenKind::Let) {
            let span = self.current_span();
            self.advance(); // consume 'let'
            return self.qq_let_body(span);
        }

        // Handle if expressions in Qq context
        // Part of #80: if $c then $a else $b
        if self.check(&TokenKind::If) {
            let span = self.current_span();
            self.advance(); // consume 'if'
            return self.qq_if_body(span);
        }

        // Handle parentheses specially - they need to recursively parse qq_expr
        // Also check for ascription: ($x : Type)
        // Part of #80: ascription support
        if self.check(&TokenKind::LParen) {
            let span = self.current_span();
            self.advance(); // consume '('
            let inner = self.qq_expr()?; // Use qq_expr for inner content

            // Check for ascription: (expr : type)
            if self.eat(&TokenKind::Colon) {
                let ty = self.qq_expr()?;
                let end_span = self.current_span();
                self.expect(&TokenKind::RParen)?;
                return Ok(SurfaceExpr::Ascription(
                    span.merge(end_span),
                    Box::new(inner),
                    Box::new(ty),
                ));
            }

            let end_span = self.current_span();
            self.expect(&TokenKind::RParen)?;
            return Ok(SurfaceExpr::Paren(span.merge(end_span), Box::new(inner)));
        }

        // Delegate to normal atom_expr for non-antiquotation atoms
        self.atom_expr()
    }

    /// Parse let expression body in Qq context
    /// Simplified version that supports: let name := value in body
    /// Part of #80: qq_expr parser extensions - Phase 3
    pub(super) fn qq_let_body(&mut self, start_span: Span) -> Result<SurfaceExpr, ParseError> {
        // Parse the name
        let name = match self.current_kind() {
            TokenKind::Ident(_) => self.ident()?,
            TokenKind::Underscore => {
                self.advance();
                "_".to_string()
            }
            _ => {
                return Err(ParseError::UnexpectedToken {
                    line: self.current_line(),
                    col: self.current_span().start,
                    message: format!(
                        "expected identifier in qq let binding, got {:?}",
                        self.current_kind()
                    ),
                })
            }
        };

        // Parse optional type annotation
        let ty = if self.eat(&TokenKind::Colon) {
            Some(self.qq_expr()?)
        } else {
            None
        };

        // Expect :=
        self.expect(&TokenKind::ColonEq)?;

        // Parse value (using qq_expr to support antiquotations)
        let val = self.qq_expr()?;

        // Expect 'in' or ';'
        if !self.eat(&TokenKind::In) && !self.eat(&TokenKind::Semicolon) {
            return Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current_span().start,
                message: format!(
                    "expected `in` or `;` after qq let binding, got {:?}",
                    self.current_kind()
                ),
            });
        }

        // Parse body
        let body = self.qq_expr()?;

        let span = start_span.merge(body.span());
        let binder = SurfaceBinder::new(name, ty, SurfaceBinderInfo::Explicit);

        Ok(SurfaceExpr::Let(
            span,
            binder,
            Box::new(val),
            Box::new(body),
        ))
    }

    /// Parse if expression body in Qq context
    /// Supports: if cond then then_branch else else_branch
    /// Part of #80: qq_expr parser extensions - Phase 3
    pub(super) fn qq_if_body(&mut self, start_span: Span) -> Result<SurfaceExpr, ParseError> {
        // Parse condition (using qq_expr to support antiquotations)
        let cond = self.qq_expr()?;

        self.expect(&TokenKind::Then)?;

        // Parse then branch
        let then_branch = self.qq_expr()?;

        self.expect(&TokenKind::Else)?;

        // Parse else branch
        let else_branch = self.qq_expr()?;

        let span = start_span.merge(else_branch.span());
        Ok(SurfaceExpr::If(
            span,
            Box::new(cond),
            Box::new(then_branch),
            Box::new(else_branch),
        ))
    }

    /// Parse $x, $(e), $(x : τ), or $[xs]* antiquotation
    pub(super) fn parse_qq_antiquot(&mut self) -> Result<SurfaceExpr, ParseError> {
        let start = self.current_span();
        self.expect(&TokenKind::Dollar)?;

        match self.current_kind() {
            // $[xs]* or $[xs,]+ - splice antiquotation
            TokenKind::LBracket => {
                self.advance(); // consume '['
                let name = self.ident()?;

                // Optional separator: $[xs,]* means separate with ","
                let separator = if self.check(&TokenKind::Comma) {
                    self.advance();
                    Some(",".to_string())
                } else if let TokenKind::StringLit(s) = self.current_kind().clone() {
                    self.advance();
                    Some(s)
                } else {
                    None
                };

                self.expect(&TokenKind::RBracket)?;

                // Expect * or + suffix
                let at_least_one = if self.check(&TokenKind::Star) {
                    self.advance();
                    false
                } else if self.check(&TokenKind::Plus) {
                    self.advance();
                    true
                } else {
                    return Err(ParseError::UnexpectedToken {
                        line: self.current_line(),
                        col: self.current_span().start,
                        message: format!(
                            "expected '*' or '+' after splice antiquotation, got {:?}",
                            self.current_kind()
                        ),
                    });
                };

                let end = self.current_span();
                Ok(SurfaceExpr::QAntiquot {
                    span: start.merge(end),
                    content: QAntiquotContent::Splice {
                        name,
                        separator,
                        at_least_one,
                    },
                })
            }

            // $(e) or $(x : τ)
            TokenKind::LParen => {
                self.advance(); // consume '('
                let inner = self.expr()?;

                if self.eat(&TokenKind::Colon) {
                    // $(x : τ) - typed antiquotation
                    // inner should be an identifier
                    let name = match &inner {
                        SurfaceExpr::Ident(_, n) => n.clone(),
                        _ => {
                            return Err(ParseError::UnexpectedToken {
                                line: self.current_line(),
                                col: inner.span().start,
                                message: format!(
                                    "expected identifier in typed antiquotation, got {inner:?}"
                                ),
                            });
                        }
                    };
                    let ty = self.expr()?;
                    let end = self.current_span();
                    self.expect(&TokenKind::RParen)?;
                    Ok(SurfaceExpr::QAntiquot {
                        span: start.merge(end),
                        content: QAntiquotContent::Typed {
                            name,
                            ty: Box::new(ty),
                        },
                    })
                } else {
                    // $(e) - expression antiquotation
                    let end = self.current_span();
                    self.expect(&TokenKind::RParen)?;
                    Ok(SurfaceExpr::QAntiquot {
                        span: start.merge(end),
                        content: QAntiquotContent::Expr(Box::new(inner)),
                    })
                }
            }

            // $x - simple identifier antiquotation
            TokenKind::Ident(name) => {
                let name = name.clone();
                let end = self.current_span();
                self.advance();
                Ok(SurfaceExpr::QAntiquot {
                    span: start.merge(end),
                    content: QAntiquotContent::Simple(name),
                })
            }

            other => Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current_span().start,
                message: format!("expected identifier, '(', or '[' after '$', got {other:?}"),
            }),
        }
    }

    /// Check if current token can start an argument in Qq context
    pub(super) fn is_qq_arg_start(&self) -> bool {
        // Same as is_atom_start() but includes $ for antiquotations
        self.check(&TokenKind::Dollar) || self.is_atom_start()
    }
}

#[cfg(test)]
mod quotation_body_tests {
    use crate::surface::{QAntiquotContent, SurfaceArg, SurfaceExpr};
    use crate::Parser;

    fn simple_name(arg: &SurfaceArg) -> Option<&str> {
        match &arg.expr {
            SurfaceExpr::QAntiquot {
                content: QAntiquotContent::Simple(name),
                ..
            } => Some(name.as_str()),
            _ => None,
        }
    }

    #[test]
    fn test_parse_quotation_body_simple_antiquot() {
        // `($x)` should parse to a single simple antiquotation, not a truncated atom.
        let expr = Parser::parse_quotation_body("($x)").expect("should parse `($x)`");
        match expr {
            SurfaceExpr::QAntiquot {
                content: QAntiquotContent::Simple(name),
                ..
            } => assert_eq!(name, "x"),
            other => panic!("expected simple antiquotation, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_quotation_body_binop_template_keeps_both_operands() {
        // The regression: `($x + $x)` must desugar to `HAdd.hAdd $x $x`, NOT silently
        // drop `+ $x` and yield just `$x`.
        let expr = Parser::parse_quotation_body("($x + $x)").expect("should parse `($x + $x)`");
        let SurfaceExpr::App(_, func, args) = expr else {
            panic!("expected an application for `$x + $x`, got {expr:?}");
        };
        assert!(
            matches!(func.as_ref(), SurfaceExpr::Ident(_, name) if name == "HAdd.hAdd"),
            "operator should desugar to HAdd.hAdd, got {func:?}"
        );
        assert_eq!(args.len(), 2, "binary operator must keep both operands");
        assert_eq!(simple_name(&args[0]), Some("x"));
        assert_eq!(simple_name(&args[1]), Some("x"));
    }

    #[test]
    fn test_parse_quotation_body_app_template() {
        // `(id $x)` parses to an application of `id` to antiquotation `$x`.
        let expr = Parser::parse_quotation_body("(id $x)").expect("should parse `(id $x)`");
        let SurfaceExpr::App(_, func, args) = expr else {
            panic!("expected application, got {expr:?}");
        };
        assert!(matches!(func.as_ref(), SurfaceExpr::Ident(_, n) if n == "id"));
        assert_eq!(args.len(), 1);
        assert_eq!(simple_name(&args[0]), Some("x"));
    }

    #[test]
    fn test_parse_quotation_body_trailing_input_errors() {
        // A malformed body with unbalanced trailing content should error rather than
        // silently truncating.
        let result = Parser::parse_quotation_body("($x + )");
        assert!(
            result.is_err(),
            "incomplete binary operator should fail to parse, got {result:?}"
        );
    }
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Parsing for class and instance declarations,
//! including instance field value expression parsing.

use super::super::Parser;
use crate::lexer::TokenKind;
use crate::surface::modifiers::DeclModifiers;
use crate::surface::*;
use crate::ParseError;

impl Parser {
    /// Parse a class declaration with default modifiers.
    pub(in crate::grammar) fn class_decl(
        &mut self,
        start_span: Span,
    ) -> Result<SurfaceDecl, ParseError> {
        self.class_decl_with_mods(start_span, DeclModifiers::default())
    }

    /// Parse a class declaration with explicit modifiers.
    ///
    /// ```text
    /// class Add (α : Type) where
    ///   add : α → α → α
    /// ```
    pub(in crate::grammar) fn class_decl_with_mods(
        &mut self,
        start_span: Span,
        modifiers: DeclModifiers,
    ) -> Result<SurfaceDecl, ParseError> {
        let name = self.decl_name()?;
        let universe_params = self.universe_params()?;
        let binders = self.optional_binders()?;

        // Optional extends clause: `class Foo extends Bar α, Baz β`
        // Parse as comma-separated list of type expressions
        let mut extends = Vec::new();
        if self.eat(&TokenKind::Extends) {
            // Parse first parent type (use app_expr to handle `Ring α` style applications)
            extends.push(Box::new(self.app_expr()?));
            // Parse additional parent types after commas
            while self.eat(&TokenKind::Comma) {
                extends.push(Box::new(self.app_expr()?));
            }
        }

        // Optional explicit result type: `class Foo : Type 1 where`
        let ty = if self.eat(&TokenKind::Colon) {
            Some(Box::new(self.expr()?))
        } else {
            None
        };

        // Older Lean 4 form: `class Foo params [extends …] := [ctor ::]
        // (f₁ : T₁) …` — `:=` introduces the anonymous constructor's
        // parenthesized field binders, equivalent to a `where` field block.
        // `SurfaceDecl::Class` carries no constructor name (the `where` path
        // likewise ignores one), so a leading `mk ::` is consumed and dropped.
        if self.eat(&TokenKind::ColonEq) {
            if matches!(self.current_kind(), TokenKind::Ident(_))
                && matches!(self.peek_kind(1), Some(TokenKind::ColonColon))
            {
                let _ = self.ident()?;
                self.expect(&TokenKind::ColonColon)?;
            }
            let fields = self.parse_paren_field_binders()?;
            return Ok(SurfaceDecl::Class {
                span: start_span,
                name,
                universe_params,
                binders,
                extends,
                ty,
                fields,
                modifiers,
            });
        }

        // Handle case where class has no fields
        if !self.check(&TokenKind::Where) {
            return Ok(SurfaceDecl::Class {
                span: start_span,
                name,
                universe_params,
                binders,
                extends,
                ty,
                fields: Vec::new(),
                modifiers,
            });
        }

        self.expect(&TokenKind::Where)?;

        // Parse fields (same as structure)
        let mut fields = Vec::new();
        while self.is_field_start() {
            let field_span = self.current_span();
            let field_name = self.ident()?;

            // Bare `name := value` — a field-default override of an inherited
            // field, same surface arm as the structure parser. The elaborator's
            // class path rejects it loudly (parent methods are prepended as own
            // fields there, so no inherited-field target exists). (B90)
            if self.eat(&TokenKind::ColonEq) {
                let default_val = self.field_type_expr()?;
                fields.push(SurfaceField {
                    span: field_span,
                    name: field_name,
                    ty: SurfaceExpr::Hole(field_span),
                    default: Some(default_val),
                    is_default_override: true,
                });
                continue;
            }

            self.expect(&TokenKind::Colon)?;
            let field_ty = self.field_type_expr()?;

            // Optional default value
            let default = if self.eat(&TokenKind::ColonEq) {
                Some(self.field_type_expr()?)
            } else {
                None
            };

            fields.push(SurfaceField {
                span: field_span,
                name: field_name,
                ty: field_ty,
                default,
                is_default_override: false,
            });
        }

        Ok(SurfaceDecl::Class {
            span: start_span,
            name,
            universe_params,
            binders,
            extends,
            ty,
            fields,
            modifiers,
        })
    }

    /// Parse an instance declaration
    ///
    /// ```text
    /// instance : Add Nat where
    ///   add := Nat.add
    /// ```
    ///
    /// Or with name:
    /// ```text
    /// instance instAddNat : Add Nat where
    ///   add := Nat.add
    /// ```
    ///
    /// Or with parameters:
    /// ```text
    /// instance [Add α] [Add β] : Add (α × β) where
    ///   add := fun (a, b) (c, d) => (add a c, add b d)
    /// ```
    ///
    /// Or with priority attribute:
    /// ```text
    /// @[instance 50] instance : Add Nat where ...
    /// @[defaultInstance] instance : ToString Nat where ...
    /// ```
    /// Parse an instance declaration with explicit modifiers.
    pub(in crate::grammar) fn instance_decl_with_mods(
        &mut self,
        start_span: Span,
        attrs: &[Attribute],
        modifiers: DeclModifiers,
    ) -> Result<SurfaceDecl, ParseError> {
        let universe_params = self.universe_params()?;

        // Optional `(priority := expr)` declaration option (before the instance
        // name/type). The numeric/keyword priority is CAPTURED (B12): a later
        // equal-priority instance otherwise silently wins over a higher-priority
        // earlier one under the most-recent-first resolution order.
        let mut inline_priority: Option<u32> = None;
        if self.check(&TokenKind::LParen) {
            let saved_pos = self.pos;
            self.advance();
            if let TokenKind::Ident(kw) = self.current_kind() {
                if kw == "priority"
                    && self.tokens.get(self.pos + 1).map(|t| &t.kind) == Some(&TokenKind::ColonEq)
                {
                    self.advance(); // consume `priority`
                    self.advance(); // consume `:=`
                    inline_priority = self.instance_priority_value();
                    // Consume the remainder of the option up to the matching `)`.
                    let mut depth = 1;
                    while depth > 0 && !matches!(self.current_kind(), TokenKind::Eof) {
                        match self.current_kind() {
                            TokenKind::LParen => depth += 1,
                            TokenKind::RParen => depth -= 1,
                            _ => {}
                        }
                        self.advance();
                    }
                } else {
                    // Not a priority option, backtrack
                    self.pos = saved_pos;
                }
            } else {
                self.pos = saved_pos;
            }
        }

        // Check for optional name: `instance instAddNat : ...`
        // vs anonymous: `instance : ...`
        // We need to distinguish between a name and a binder/colon
        let name = if let TokenKind::Ident(_) = self.current_kind() {
            let saved_pos = self.pos;
            if let Ok(candidate) = self.qualified_ident() {
                if self.check(&TokenKind::Colon) {
                    Some(candidate)
                } else {
                    self.pos = saved_pos;
                    None
                }
            } else {
                self.pos = saved_pos;
                None
            }
        } else {
            None
        };

        // Parse optional binders
        let binders = self.optional_binders()?;

        // Expect colon followed by class type
        self.expect(&TokenKind::Colon)?;
        let class_type = self.expr()?;

        let mut fields = Vec::new();
        if self.eat(&TokenKind::Where) {
            // Parse field assignments
            fields = self.parse_where_field_assigns()?;
        } else if self.eat(&TokenKind::ColonEq) {
            // Short instance form: `instance : Class := expr`
            let val = self.expr()?;
            fields.push(SurfaceFieldAssign {
                span: start_span,
                name: "_value".to_string(),
                val,
            });
        } else {
            return Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current_span().start,
                message: format!(
                    "expected `where` or `:=` in instance declaration, got {:?}",
                    self.current_kind()
                ),
            });
        }

        // Priority: the inline `(priority := …)` option takes precedence, then a
        // `@[instance N]` / `@[defaultInstance]` attribute.
        let priority =
            inline_priority.or_else(|| attrs.iter().find_map(Attribute::instance_priority));

        Ok(SurfaceDecl::Instance {
            span: start_span,
            name,
            universe_params,
            binders,
            class_type: Box::new(class_type),
            fields,
            priority,
            modifiers,
        })
    }

    /// Parse a run of `where` field assignments (`field := value`, with
    /// optional method binders and `field | pat => body` pattern sugar).
    /// Shared by instance declarations and the `def x : S where` struct-
    /// instance sugar (B90) — the loop body is the instance parser's original,
    /// moved verbatim.
    pub(in crate::grammar) fn parse_where_field_assigns(
        &mut self,
    ) -> Result<Vec<SurfaceFieldAssign>, ParseError> {
        let mut fields = Vec::new();
        while self.is_field_assign_start() {
            let field_span = self.current_span();
            let field_name = self.ident()?;
            // Lean lets field methods bind their parameters before `:=`,
            // e.g. `reprPrec m _ := body` / `beq a b := body`, desugaring to
            // `reprPrec := fun m _ => body`. Parse the optional binders and
            // wrap the value in a lambda below.
            let field_binders = self.instance_field_binders()?;
            let mut field_val = if self.check(&TokenKind::Pipe) {
                // Pattern-matching field sugar: `field | pat => body`
                // desugars to `field := fun | pat => body` (an anonymous
                // pattern-matching lambda). Reuse `lambda_body`, which builds
                // a `PatternMatchLambda` from the `| pat => body` alternatives.
                // The `in_instance_field` guard (set below in the value
                // helpers) is not needed here because `lambda_body` already
                // terminates each arm body at the next `|`/declaration
                // boundary. (Track EF)
                self.lambda_body(field_span)?
            } else {
                self.expect(&TokenKind::ColonEq)?;
                self.instance_field_value_expr()?
            };
            if !field_binders.is_empty() {
                let val_span = field_val.span();
                field_val = SurfaceExpr::Lambda(val_span, field_binders, Box::new(field_val));
            }

            fields.push(SurfaceFieldAssign {
                span: field_span,
                name: field_name,
                val: field_val,
            });
        }
        Ok(fields)
    }

    /// Parse the value of a `(priority := …)` instance option: a numeric literal
    /// or a Lean priority keyword (`high`/`default`/`mid`/`low`, the `prio`
    /// macros — `high = 10000`, `default/mid = 1000`, `low = 100`). Advances past
    /// the value it recognizes; returns `None` (without advancing) for anything
    /// else, so the caller's paren-skip still consumes the option cleanly.
    pub(in crate::grammar) fn instance_priority_value(&mut self) -> Option<u32> {
        match self.current_kind().clone() {
            TokenKind::NatLit(n) => {
                self.advance();
                n.to_u64().and_then(|v| u32::try_from(v).ok())
            }
            TokenKind::Ident(kw) => {
                let prio = match kw.as_str() {
                    "high" => Some(10000),
                    "default" | "mid" => Some(1000),
                    "low" => Some(100),
                    _ => None,
                };
                if prio.is_some() {
                    self.advance();
                }
                prio
            }
            _ => None,
        }
    }

    /// Check if current position looks like a field assignment start.
    ///
    /// A field assignment starts with an identifier followed by `:=`, OR by a
    /// run of method binders before `:=` (Lean's `field a b := body` /
    /// `field m _ := body` sugar). We scan forward over binder-shaped tokens —
    /// bare identifiers, `_` holes, and balanced `(...)` / `{...}` / `[...]`
    /// binder groups — and accept the field iff we reach a `:=` before any token
    /// that cannot appear in a binder list. This keeps single-token field
    /// assignments (`f := v`) working while also recognizing `reprPrec m _ :=`.
    pub(in crate::grammar) fn is_field_assign_start(&self) -> bool {
        if !matches!(self.current_kind(), TokenKind::Ident(_)) {
            return false;
        }
        // Position after the field name.
        let mut i = self.pos + 1;
        loop {
            match self.tokens.get(i).map(|t| &t.kind) {
                Some(TokenKind::ColonEq) => return true,
                // Lean's pattern-matching field sugar: `field | pat => body`
                // (and `field a | pat => body`) desugars to
                // `field := fun a => match a with | pat => body`. The field is
                // introduced by a `|` instead of `:=`, with no intervening
                // declaration boundary. Accept it as a field start. (Track EF)
                Some(TokenKind::Pipe) => return true,
                Some(TokenKind::Ident(_) | TokenKind::Underscore) => {
                    i += 1;
                }
                // Balanced binder groups `(...)`, `{...}`, `[...]`. Skip to the
                // matching close so a `:=` *inside* the group (e.g. a default
                // value) does not prematurely match.
                Some(open @ (TokenKind::LParen | TokenKind::LBrace | TokenKind::LBracket)) => {
                    let close = match open {
                        TokenKind::LParen => TokenKind::RParen,
                        TokenKind::LBrace => TokenKind::RBrace,
                        _ => TokenKind::RBracket,
                    };
                    let mut depth = 1usize;
                    i += 1;
                    while depth > 0 {
                        match self.tokens.get(i).map(|t| &t.kind) {
                            None => return false,
                            Some(k) if *k == *open => {
                                depth += 1;
                                i += 1;
                            }
                            Some(k) if *k == close => {
                                depth -= 1;
                                i += 1;
                            }
                            Some(_) => i += 1,
                        }
                    }
                }
                _ => return false,
            }
        }
    }

    /// Does the token at `start` begin a field assignment `name binders… :=`
    /// (or `name binders… |`), with the METHOD BINDERS on the SAME line as the
    /// name? Used to bound a preceding field's *value* (`is_atom_start` in
    /// `expr_app.rs`): the previous field's value must stop before `g x := …`,
    /// not swallow `g x` as application arguments (the multi-field-with-binders
    /// bug: `f x := x + 1` then `g x := x + 2`). The same-line binder requirement
    /// is essential — a value continuation argument on a NEW line must not be
    /// mistaken for a field's binder (the caller additionally requires the field
    /// name itself to be newline-leading). Mirrors [`Self::is_field_assign_start`]
    /// but parameterized by position and layout-aware for the boundary case.
    pub(in crate::grammar) fn field_assign_at(&self, start: usize) -> bool {
        if !matches!(
            self.tokens.get(start).map(|t| &t.kind),
            Some(TokenKind::Ident(_))
        ) {
            return false;
        }
        let mut i = start + 1;
        loop {
            let tok = self.tokens.get(i);
            match tok.map(|t| &t.kind) {
                Some(TokenKind::ColonEq | TokenKind::Pipe) => return true,
                // Method binders must be on the SAME line as the field name; a
                // newline-leading token is the next field or a value
                // continuation, not a binder — stop the scan.
                Some(TokenKind::Ident(_) | TokenKind::Underscore)
                    if tok.is_some_and(|t| !t.preceded_by_newline) =>
                {
                    i += 1;
                }
                Some(open @ (TokenKind::LParen | TokenKind::LBrace | TokenKind::LBracket))
                    if tok.is_some_and(|t| !t.preceded_by_newline) =>
                {
                    let close = match open {
                        TokenKind::LParen => TokenKind::RParen,
                        TokenKind::LBrace => TokenKind::RBrace,
                        _ => TokenKind::RBracket,
                    };
                    let mut depth = 1usize;
                    i += 1;
                    while depth > 0 {
                        match self.tokens.get(i).map(|t| &t.kind) {
                            None => return false,
                            Some(k) if *k == *open => {
                                depth += 1;
                                i += 1;
                            }
                            Some(k) if *k == close => {
                                depth -= 1;
                                i += 1;
                            }
                            Some(_) => i += 1,
                        }
                    }
                }
                _ => return false,
            }
        }
    }

    /// Parse the optional method binders that may appear between an instance
    /// field name and its `:=`, e.g. the `m _` in `reprPrec m _ := body`.
    ///
    /// Accepts bare identifiers, `_` holes, and the parenthesized / braced /
    /// bracketed binder groups handled by [`Self::optional_binders`]. Stops at
    /// the `:=` that begins the field value.
    pub(in crate::grammar) fn instance_field_binders(
        &mut self,
    ) -> Result<Vec<SurfaceBinder>, ParseError> {
        let mut binders = Vec::new();
        loop {
            match self.current_kind() {
                TokenKind::ColonEq => break,
                TokenKind::Underscore => {
                    let span = self.current_span();
                    self.advance();
                    binders.push(SurfaceBinder {
                        span,
                        name: "_".to_string(),
                        ty: None,
                        default: None,
                        info: SurfaceBinderInfo::Explicit,
                    });
                }
                TokenKind::Ident(name) => {
                    let span = self.current_span();
                    let name = name.clone();
                    self.advance();
                    binders.push(SurfaceBinder {
                        span,
                        name,
                        ty: None,
                        default: None,
                        info: SurfaceBinderInfo::Explicit,
                    });
                }
                TokenKind::LParen => binders.extend(self.explicit_binders()?),
                TokenKind::LBrace => binders.extend(self.implicit_binders()?),
                TokenKind::LBracket => binders.extend(self.instance_binders()?),
                // `⦃x : T⦄` — strict-implicit, same gap as `optional_binders`.
                TokenKind::StrictLBrace => binders.extend(self.strict_implicit_binders()?),
                _ => break,
            }
        }
        Ok(binders)
    }

    /// Parse an instance field value expression.
    /// This is like `expr()` but stops before identifiers that look like field assignments
    /// (i.e., identifiers followed by `:=`).
    ///
    /// The `instance_field_*_expr` helpers below stop at field-assignment
    /// boundaries only at their own application/arrow level. A field value that
    /// is a `fun .. => body` lambda parses its body via the general `expr`
    /// grammar (`atom_expr` → `lambda_body` → `expr`), which is *not*
    /// boundary-aware. Setting `in_instance_field` makes `is_atom_start` stop at
    /// the next `ident :=` everywhere downstream, so the lambda body in
    /// `render := fun _ => Nat.succ Nat.zero` terminates before `tag := 3`
    /// instead of swallowing `tag` as an argument. Mirrors
    /// `struct_field_value_expr`. See B53.
    pub(in crate::grammar) fn instance_field_value_expr(
        &mut self,
    ) -> Result<SurfaceExpr, ParseError> {
        let saved = self.in_instance_field;
        self.in_instance_field = true;
        // Parse the value via the full operator-precedence grammar so infix
        // operators (`++`, `+`, …) and multi-line operator continuations in a
        // field body are handled — e.g. `reprPrec m _ := "a" ++ repr x ++ "b"`.
        // The `in_instance_field` flag keeps `is_atom_start` (see expr_app.rs)
        // stopping at the next `ident :=` so a following field assignment is not
        // swallowed as an application argument. Previously this used a bespoke
        // app+arrow sub-grammar (`instance_field_arrow_expr`) that silently
        // dropped everything after the first infix operator.
        let result = self.expr();
        self.in_instance_field = saved;
        result
    }
}

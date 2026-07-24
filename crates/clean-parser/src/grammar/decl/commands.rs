// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Parsing for miscellaneous Lean 4 declaration commands:
//! example, import, namespace, section, universe, variable, open, export,
//! deriving instance, mutual, hash commands, abbrev, attribute, set_option,
//! and declare_aesop_rule_sets.

use super::super::Parser;
use crate::lexer::TokenKind;
use crate::surface::modifiers::DeclModifiers;
use crate::surface::*;
use crate::ParseError;

impl Parser {
    /// Parse example declaration: `example : ty := proof`
    pub(in crate::grammar) fn example_decl(
        &mut self,
        start_span: Span,
    ) -> Result<SurfaceDecl, ParseError> {
        let binders = self.optional_binders()?;

        let ty = if self.eat(&TokenKind::Colon) {
            Some(Box::new(self.expr()?))
        } else {
            None
        };

        self.expect(&TokenKind::ColonEq)?;
        let val = self.expr()?;

        Ok(SurfaceDecl::Example {
            span: start_span,
            binders,
            ty,
            val: Box::new(val),
        })
    }

    /// Parse import declaration: `import Lean.Data.List`
    pub(in crate::grammar) fn import_decl(
        &mut self,
        start_span: Span,
    ) -> Result<SurfaceDecl, ParseError> {
        let mut paths = Vec::new();

        // Lean 4 module system: `import all X` requests importing X's private
        // declarations too. `all` is not a reserved keyword (module names could
        // in principle collide), so only treat it as the import modifier when it
        // is immediately followed by another identifier (the module path). It is
        // transparent to checking — resolve X exactly as a bare `import X`.
        if matches!(self.current_kind(), TokenKind::Ident(name) if name == "all")
            && matches!(self.peek_kind(1), Some(TokenKind::Ident(_)))
        {
            self.advance();
        }

        loop {
            let path = self.module_path()?;
            paths.push(path);

            // Support comma or whitespace separated modules on same line
            if self.eat(&TokenKind::Comma) {
                continue;
            }

            // Whitespace-separated imports only continue on the same physical
            // line. An identifier-led command on the next line, such as
            // `local notation`, belongs to the file body.
            if self.current().preceded_by_newline
                || !matches!(self.current_kind(), TokenKind::Ident(_))
            {
                break;
            }
        }

        Ok(SurfaceDecl::Import {
            span: start_span,
            paths,
        })
    }

    /// Parse the body of a `namespace`/`section` block: declarations until the
    /// matching `end` (consumed by the caller) or end of file.
    ///
    /// This mirrors the file-level recovery in [`Parser::file`]: when an inner
    /// declaration fails to parse, the parser records the original error as a
    /// recovery diagnostic, emits a `RawDecl` placeholder for the malformed
    /// region, and resynchronizes at the next declaration-start token (which
    /// includes the closing `End`). Without this, a single malformed
    /// declaration inside a namespace propagated out of `namespace_decl`,
    /// collapsing the entire namespace into one top-level `RawDecl` and — worse
    /// — hoisting every *subsequent* in-namespace declaration out of the
    /// namespace, so its fully-qualified name silently lost the namespace
    /// prefix (`Foo.good` became `good`).
    ///
    /// Recovery here is forward-progressing: `skip_to_next_decl_with_recovery`
    /// always advances past at least one token (or onto a fresh decl-start /
    /// `End` / EOF), so the `while` loop below cannot spin in place.
    fn scoped_block_decls(&mut self) -> Vec<SurfaceDecl> {
        let mut decls = Vec::new();
        while !matches!(self.current_kind(), TokenKind::End | TokenKind::Eof) {
            let span = self.current_span();
            match self.decl() {
                Ok(d) => decls.push(d),
                Err(err) => {
                    decls.push(self.skip_to_next_decl_with_recovery("error-recovery", span, &err));
                }
            }
        }
        decls
    }

    /// Parse namespace declaration: `namespace Foo ... end Foo`
    ///
    /// Both the opening name and the closing `end Name` may be compound
    /// (dotted) identifiers, mirroring the Lean 4 grammar:
    ///
    /// ```text
    /// namespace ::= "namespace" QualifiedIdent
    /// end       ::= "end" QualifiedIdent?
    /// ```
    pub(in crate::grammar) fn namespace_decl(
        &mut self,
        start_span: Span,
    ) -> Result<SurfaceDecl, ParseError> {
        let name = self.qualified_ident()?;

        // Parse declarations until `end` or end of file
        // In Lean 4, `namespace` without `end` is valid - the namespace ends at file end
        let decls = self.scoped_block_decls();

        // `end` is optional - namespace can end at EOF
        if self.eat(&TokenKind::End) {
            // Optionally consume the namespace name after `end`.
            // Accept either a full qualified match (`end Foo.Bar.Baz`)
            // or a leaf-only match (`end Baz` against `Foo.Bar.Baz`)
            // to preserve the lenient behavior of earlier versions.
            self.try_consume_end_name(&name);
        }

        Ok(SurfaceDecl::Namespace {
            span: start_span,
            name,
            decls,
        })
    }

    /// Parse section declaration: `section [Name] ... end [Name]`
    pub(in crate::grammar) fn section_decl(
        &mut self,
        start_span: Span,
    ) -> Result<SurfaceDecl, ParseError> {
        // Section name is optional. `local` is NOT a section name: it is the
        // declaration modifier of the section's first inner decl (`section` +
        // `local instance …` / `local notation …`) — Lean reserves `local` as
        // a keyword, so a section can never be named `local`. Swallowing it
        // as the name silently DROPPED the modifier, so a `local instance`
        // registered as if global and leaked past `end` (B99, r82
        // `instprio_local_section_shadow`).
        let name = match self.current_kind() {
            TokenKind::Ident(id) if id != "local" => Some(self.ident()?),
            _ => None,
        };

        // Parse declarations until `end` or end of file
        // In Lean 4, `section` without `end` is valid - the section ends at file end
        let decls = self.scoped_block_decls();

        // `end` is optional - section can end at EOF
        if self.eat(&TokenKind::End) {
            // Optionally consume the section name after `end`. Sections can
            // be named with a compound (dotted) identifier in the wild even
            // though Lean 4 itself does not idiomatically use that; accept
            // either the full path or just the trailing segment.
            if let Some(n) = name.as_ref() {
                self.try_consume_end_name(n);
            }
        }

        Ok(SurfaceDecl::Section {
            span: start_span,
            name,
            decls,
        })
    }

    /// Consume an optional `Name` (possibly dotted) following a closing `end`
    /// keyword. Matches either the full opening name or just its trailing
    /// segment; leaves the parser position unchanged on mismatch so that the
    /// caller can produce a clearer diagnostic upstream.
    fn try_consume_end_name(&mut self, opening_name: &str) {
        // Peek ahead to assemble the dotted name without committing tokens.
        let mut lookahead = 0usize;
        let mut consumed_segments: Vec<String> = Vec::new();

        match self.peek_kind(lookahead) {
            Some(TokenKind::Ident(seg)) => {
                consumed_segments.push(seg.clone());
                lookahead += 1;
            }
            _ => return,
        }

        // Look for `.Ident` repetitions.
        while matches!(self.peek_kind(lookahead), Some(TokenKind::Dot)) {
            match self.peek_kind(lookahead + 1) {
                Some(TokenKind::Ident(next_seg)) => {
                    consumed_segments.push(next_seg.clone());
                    lookahead += 2;
                }
                _ => break,
            }
        }

        let full = consumed_segments.join(".");
        let leaf = opening_name.rsplit('.').next().unwrap_or(opening_name);

        // Accept either: full dotted match, or a single-segment leaf match.
        let accept = full == opening_name || (consumed_segments.len() == 1 && full == leaf);
        if !accept {
            return;
        }

        // Commit: advance past `lookahead` tokens.
        for _ in 0..lookahead {
            self.advance();
        }
    }

    /// Parse universe declaration: `universe u v`
    pub(in crate::grammar) fn universe_decl(
        &mut self,
        start_span: Span,
    ) -> Result<SurfaceDecl, ParseError> {
        let mut names = Vec::new();

        while let TokenKind::Ident(_) = self.current_kind() {
            names.push(self.ident()?);
        }

        if names.is_empty() {
            return Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current_span().start,
                message: "expected at least one universe parameter name".to_string(),
            });
        }

        Ok(SurfaceDecl::UniverseDecl {
            span: start_span,
            names,
        })
    }

    /// Parse variable declaration: `variable (x : Type)`
    pub(in crate::grammar) fn variable_decl(
        &mut self,
        start_span: Span,
    ) -> Result<SurfaceDecl, ParseError> {
        let binders = self.binders()?;

        Ok(SurfaceDecl::Variable {
            span: start_span,
            binders,
        })
    }

    /// Parse open command: `open Nat in ...` or `open Nat (add mul)` or `open scoped X`
    pub(in crate::grammar) fn open_decl(
        &mut self,
        start_span: Span,
    ) -> Result<SurfaceDecl, ParseError> {
        // Check for `open scoped` modifier
        let scoped = self.eat(&TokenKind::Scoped);

        let mut paths = Vec::new();

        loop {
            let path = self.module_path()?;

            // Check for specific names: `open Nat (add mul)`
            let mut names = Vec::new();
            let mut hiding = Vec::new();
            let mut renaming = Vec::new();

            if self.eat(&TokenKind::LParen) {
                while self.is_ident_like() {
                    names.push(self.ident_like()?);
                }
                self.expect(&TokenKind::RParen)?;
            } else if self.eat(&TokenKind::Hiding) {
                // Lean's grammar (`Lean/Parser/Command.lean`, `openHiding`) is
                // `"hiding" (ppSpace colGt ident)+`: hidden names are plain
                // identifiers belonging to the SAME command. The previous loop
                // used `is_ident_like()`, which also accepts keyword tokens, so
                // it swallowed the NEXT declaration's leading keyword and idents
                // (`open Foo hiding z ⏎ theorem pin : …` consumed `theorem` and
                // `pin` into the hiding list, leaving `: …` to error-recover as
                // a raw declaration — gap sweep B13, namespaces_scoping/p08).
                // Require true identifier tokens and stop at a newline boundary
                // (the next command).
                while matches!(self.current_kind(), TokenKind::Ident(_))
                    && !self.current().preceded_by_newline
                {
                    hiding.push(self.ident()?);
                }
                if hiding.is_empty() {
                    return Err(ParseError::UnexpectedToken {
                        line: self.current_line(),
                        col: self.current_span().start,
                        message: "expected at least one name after `hiding`".to_string(),
                    });
                }
            } else if self.eat(&TokenKind::Renaming) {
                loop {
                    let from = self.ident_like()?;
                    self.expect(&TokenKind::Arrow)?;
                    let to = self.ident_like()?;
                    renaming.push(OpenRename { from, to });
                    if !self.eat(&TokenKind::Comma) {
                        break;
                    }
                }
            }

            paths.push(OpenPath {
                path,
                names,
                hiding,
                renaming,
            });

            if self.check(&TokenKind::In)
                || self.current().preceded_by_newline
                || !matches!(self.current_kind(), TokenKind::Ident(_))
            {
                break;
            }
        }

        // Check for `in` followed by body
        let body = if self.eat(&TokenKind::In) {
            Some(Box::new(self.decl()?))
        } else {
            None
        };

        Ok(SurfaceDecl::Open {
            span: start_span,
            paths,
            body,
            scoped,
        })
    }

    /// Parse export command: `export Namespace (name1 name2 ...)`
    /// Makes names from another namespace visible in the current namespace.
    pub(in crate::grammar) fn export_decl(
        &mut self,
        start_span: Span,
    ) -> Result<SurfaceDecl, ParseError> {
        // Parse the namespace to export from
        let namespace = self.module_path()?;

        // Parse the names to export: (name1 name2 ...)
        self.expect(&TokenKind::LParen)?;
        let mut names = Vec::new();
        while self.is_ident_like() {
            names.push(self.ident_like()?);
        }
        if names.is_empty() {
            return Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current_span().start,
                message: "expected at least one name to export".to_string(),
            });
        }
        self.expect(&TokenKind::RParen)?;

        Ok(SurfaceDecl::Export {
            span: start_span,
            namespace,
            names,
        })
    }

    /// Parse standalone deriving instance command: `deriving instance Class1, Class2 for Type1, Type2`
    pub(in crate::grammar) fn deriving_instance_decl(
        &mut self,
        start_span: Span,
    ) -> Result<SurfaceDecl, ParseError> {
        // Expect `instance` keyword after `deriving`
        self.expect(&TokenKind::Instance)?;

        // Parse comma-separated class names
        let mut classes = Vec::new();
        classes.push(self.qualified_ident()?);
        while self.eat(&TokenKind::Comma) {
            classes.push(self.qualified_ident()?);
        }

        // Expect `for` (as identifier, not a keyword)
        match self.current_kind() {
            TokenKind::Ident(s) if s == "for" => {
                self.advance();
            }
            _ => {
                return Err(ParseError::UnexpectedToken {
                    line: self.current_line(),
                    col: self.current_span().start,
                    message: "expected 'for' after type class names".to_string(),
                });
            }
        }

        // Parse comma-separated type names
        let mut types = Vec::new();
        types.push(self.qualified_ident()?);
        while self.eat(&TokenKind::Comma) {
            types.push(self.qualified_ident()?);
        }

        Ok(SurfaceDecl::DerivingInstance {
            span: start_span,
            classes,
            types,
        })
    }

    /// Parse mutual block: `mutual ... end`
    pub(in crate::grammar) fn mutual_decl(
        &mut self,
        start_span: Span,
    ) -> Result<SurfaceDecl, ParseError> {
        let mut decls = Vec::new();

        while !matches!(self.current_kind(), TokenKind::End | TokenKind::Eof) {
            decls.push(self.decl()?);
        }

        self.expect(&TokenKind::End)?;

        Ok(SurfaceDecl::Mutual {
            span: start_span,
            decls,
        })
    }

    /// Parse hash commands: `#check`, `#eval`, `#print`
    pub(in crate::grammar) fn hash_command(
        &mut self,
        start_span: Span,
    ) -> Result<SurfaceDecl, ParseError> {
        match self.current_kind().clone() {
            TokenKind::Ident(cmd) => {
                self.advance();
                match cmd.as_str() {
                    "check" => {
                        let expr = self.expr()?;
                        Ok(SurfaceDecl::Check {
                            span: start_span,
                            expr: Box::new(expr),
                        })
                    }
                    "eval" => {
                        let expr = self.expr()?;
                        Ok(SurfaceDecl::Eval {
                            span: start_span,
                            expr: Box::new(expr),
                        })
                    }
                    "print" => {
                        let name = self.qualified_ident()?;
                        Ok(SurfaceDecl::Print {
                            span: start_span,
                            name,
                        })
                    }
                    "reduce" | "whnf" | "norm_num" => {
                        // Treat as eval
                        let expr = self.expr()?;
                        Ok(SurfaceDecl::Eval {
                            span: start_span,
                            expr: Box::new(expr),
                        })
                    }
                    _ => {
                        // Unknown hash command - try to skip it gracefully
                        self.skip_to_next_decl_token();
                        Ok(SurfaceDecl::Check {
                            span: start_span,
                            expr: Box::new(SurfaceExpr::Hole(start_span)),
                        })
                    }
                }
            }
            _ => Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current_span().start,
                message: format!("expected command after #, got {:?}", self.current_kind()),
            }),
        }
    }

    /// Parse abbrev declaration (like def but unfolds eagerly)
    /// Also handles `abbrev class` which creates an abbreviation for a class.
    ///
    /// In Lean 4, `abbrev` creates a definition with `@[reducible]` semantics:
    /// the kernel always unfolds it during definitional equality checking.
    /// We track this via `DeclModifiers.is_abbrev` so the elaborator can set
    /// `Reducibility::Reducible` on the kernel declaration. Part of #3391.
    pub(in crate::grammar) fn abbrev_decl(
        &mut self,
        start_span: Span,
        attrs: Vec<Attribute>,
    ) -> Result<SurfaceDecl, ParseError> {
        // Check if abbrev is a modifier for class
        if self.eat(&TokenKind::Class) {
            return self.class_decl(start_span);
        }
        // Parse like def but with is_abbrev = true
        let modifiers = DeclModifiers {
            is_abbrev: true,
            ..DeclModifiers::default()
        };
        self.def_decl_with_mods(start_span, attrs, modifiers)
    }

    /// Parse attribute command: `attribute [simp] foo bar`
    pub(in crate::grammar) fn attribute_cmd(
        &mut self,
        start_span: Span,
    ) -> Result<SurfaceDecl, ParseError> {
        let attrs = if self.check(&TokenKind::LBracket) {
            self.expect(&TokenKind::LBracket)?;
            let mut attrs = Vec::new();
            loop {
                let attr = if self.eat(&TokenKind::Minus) {
                    let attr_name = match self.current_kind().clone() {
                        TokenKind::Ident(name) => {
                            self.advance();
                            self.skip_attribute_args();
                            name
                        }
                        TokenKind::Instance => {
                            self.advance();
                            self.skip_attribute_args();
                            "instance".to_string()
                        }
                        _ => {
                            return Err(ParseError::UnexpectedToken {
                                line: self.current_line(),
                                col: self.current_span().start,
                                message: format!(
                                    "expected attribute name after '-', got {:?}",
                                    self.current_kind()
                                ),
                            });
                        }
                    };
                    AttributeCommandAttr::Remove(attr_name)
                } else {
                    AttributeCommandAttr::Add(self.single_attribute()?)
                };
                attrs.push(attr);
                if !self.eat(&TokenKind::Comma) {
                    break;
                }
            }
            self.expect(&TokenKind::RBracket)?;
            attrs
        } else {
            Vec::new()
        };

        let mut names = Vec::new();
        while let TokenKind::Ident(_) = self.current_kind() {
            names.push(self.qualified_ident()?);
        }

        Ok(SurfaceDecl::Attribute {
            span: start_span,
            attrs,
            names,
        })
    }

    /// Parse `set_option` command
    ///
    /// Supports two forms:
    /// - File-scope: `set_option maxHeartbeats 400000`
    /// - Per-declaration: `set_option maxHeartbeats 400000 in def foo := ...`
    pub(in crate::grammar) fn set_option_cmd(
        &mut self,
        start_span: Span,
    ) -> Result<SurfaceDecl, ParseError> {
        let name = self.qualified_ident()?;

        let value = match self.current_kind().clone() {
            TokenKind::Ident(v) if v != "in" => {
                self.advance();
                Some(v)
            }
            TokenKind::NatLit(n) => {
                self.advance();
                Some(n.to_string())
            }
            TokenKind::StringLit(s) => {
                self.advance();
                Some(s)
            }
            _ => None,
        };

        // Check for `in <declaration>` form (per-declaration scoping).
        let body = if self.eat(&TokenKind::In) {
            Some(Box::new(self.decl()?))
        } else {
            None
        };

        Ok(SurfaceDecl::SetOption {
            span: start_span,
            name,
            value,
            body,
        })
    }

    /// Parse `declare_aesop_rule_sets` command
    ///
    /// Syntax: `declare_aesop_rule_sets [Measurable, Continuous]`
    ///
    /// Declares named rule sets for domain-specific aesop tactics.
    pub(in crate::grammar) fn declare_aesop_rule_sets_decl(
        &mut self,
        start_span: Span,
    ) -> Result<SurfaceDecl, ParseError> {
        // Expect opening bracket
        if !self.eat(&TokenKind::LBracket) {
            return Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current_span().start,
                message: "expected '[' after declare_aesop_rule_sets".to_string(),
            });
        }

        let mut names = Vec::new();

        // Parse comma-separated list of identifiers
        while let TokenKind::Ident(name) = self.current_kind().clone() {
            names.push(name);
            self.advance();

            // Check for comma (more names) or closing bracket
            if !self.eat(&TokenKind::Comma) {
                break;
            }
        }

        // Expect closing bracket
        if !self.eat(&TokenKind::RBracket) {
            return Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current_span().start,
                message: "expected ']' after rule set names".to_string(),
            });
        }

        Ok(SurfaceDecl::DeclareAesopRuleSets {
            span: start_span,
            names,
        })
    }

    /// Parse the Batteries/Mathlib `alias` command.
    ///
    /// Forms:
    /// - `alias newName := target` — the plain form; `newName` becomes an alias
    ///   (a `def`) of the existing declaration `target`.
    /// - `alias newName ← target` — the historical reverse arrow; parsed the
    ///   same as the plain form (`newName := target`).
    /// - `alias ⟨fwdName, bwdName⟩ := iffThm` — the iff-destructuring form;
    ///   `fwdName := Iff.mp iffThm` and `bwdName := Iff.mpr iffThm`. A `_`
    ///   entry skips that direction.
    ///
    /// All forms desugar to real `def`s so the alias resolves like any other
    /// definition. Leading attributes/modifiers (`@[simp]`, `protected`, …)
    /// carry through to the generated `def`s.
    pub(in crate::grammar) fn alias_decl(
        &mut self,
        start_span: Span,
        attrs: Vec<Attribute>,
        modifiers: DeclModifiers,
    ) -> Result<SurfaceDecl, ParseError> {
        if self.eat(&TokenKind::LAngle) {
            // Iff-destructuring form: `alias ⟨fwd, bwd⟩ := iffThm`.
            let mut names: Vec<Option<String>> = Vec::new();
            loop {
                if self.eat(&TokenKind::Underscore) {
                    names.push(None);
                } else {
                    names.push(Some(self.qualified_ident()?));
                }
                if !self.eat(&TokenKind::Comma) {
                    break;
                }
            }
            self.expect(&TokenKind::RAngle)?;
            // Operator: `:=` (or the historical `←`).
            if !self.eat(&TokenKind::LeftArrow) {
                self.expect(&TokenKind::ColonEq)?;
            }
            let target = self.qualified_ident()?;
            // Each named direction i becomes `def name := Iff.<proj_i> target`.
            let mut defs = Vec::new();
            for (i, entry) in names.iter().enumerate() {
                let Some(name) = entry else { continue };
                let proj = if i == 0 { "Iff.mp" } else { "Iff.mpr" };
                let val = SurfaceExpr::App(
                    start_span,
                    Box::new(SurfaceExpr::Ident(start_span, proj.to_string())),
                    vec![SurfaceArg::positional(SurfaceExpr::Ident(
                        start_span,
                        target.clone(),
                    ))],
                );
                defs.push(Self::mk_alias_def(
                    start_span,
                    name.clone(),
                    val,
                    attrs.clone(),
                    modifiers,
                ));
            }
            if defs.len() == 1 {
                // Exactly one direction named — return the lone `def` directly.
                return Ok(defs.swap_remove(0));
            }
            Ok(SurfaceDecl::Mutual {
                span: start_span,
                decls: defs,
            })
        } else {
            // Plain form: `alias newName := target` (or `alias newName ← target`).
            let name = self.qualified_ident()?;
            if !self.eat(&TokenKind::LeftArrow) {
                self.expect(&TokenKind::ColonEq)?;
            }
            let target = self.qualified_ident()?;
            let val = SurfaceExpr::Ident(start_span, target);
            Ok(Self::mk_alias_def(start_span, name, val, attrs, modifiers))
        }
    }

    /// Build a `def newName := val` node standing in for an `alias`.
    fn mk_alias_def(
        span: Span,
        name: String,
        val: SurfaceExpr,
        attrs: Vec<Attribute>,
        modifiers: DeclModifiers,
    ) -> SurfaceDecl {
        SurfaceDecl::Def {
            span,
            name,
            universe_params: Vec::new(),
            binders: Vec::new(),
            ty: None,
            val: Box::new(val),
            attrs,
            termination: TerminationHints::default(),
            modifiers,
            where_decls: Vec::new(),
        }
    }

    /// Parse the Mathlib/Batteries `library_note «title»` documentation command.
    ///
    /// The title is a guillemet-quoted identifier (`«fact non-instances»`,
    /// lexed as a single identifier) or a string literal. The following
    /// `/-- … -/` note body is captured by the lexer's doc-comment side table,
    /// so nothing further is consumed here. The command carries no checkable
    /// content and elaborates to a no-op.
    pub(in crate::grammar) fn library_note_decl(
        &mut self,
        start_span: Span,
    ) -> Result<SurfaceDecl, ParseError> {
        let title = match self.current_kind().clone() {
            TokenKind::Ident(s) => {
                self.advance();
                s
            }
            TokenKind::StringLit(s) => {
                self.advance();
                s
            }
            other => {
                return Err(ParseError::UnexpectedToken {
                    line: self.current_line(),
                    col: self.current_span().start,
                    message: format!("expected note title after `library_note`, got {other:?}"),
                });
            }
        };
        Ok(SurfaceDecl::LibraryNote {
            span: start_span,
            title,
        })
    }
}

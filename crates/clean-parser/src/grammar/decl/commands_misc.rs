// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Parsing for the rest of the miscellaneous Lean 4 declaration commands
//! (see `commands.rs`): deriving instance, mutual, hash commands, abbrev,
//! attribute, set_option, declare_aesop_rule_sets, alias and library_note.

use super::super::Parser;
use crate::lexer::TokenKind;
use crate::surface::modifiers::DeclModifiers;
use crate::surface::*;
use crate::ParseError;

impl Parser {
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

    /// Parse hash commands: `#check`, `#eval`, `#reduce`, `#print`, `#print
    /// axioms`, `#guard` and `#guard_msgs` (the last four in
    /// `test_commands.rs`).
    ///
    /// Entered with the `#` token consumed.
    pub(in crate::grammar) fn hash_command(
        &mut self,
        start_span: Span,
    ) -> Result<SurfaceDecl, ParseError> {
        let hash_index = self.pos.saturating_sub(1);
        match self.current_kind().clone() {
            TokenKind::Ident(cmd) => {
                self.advance();
                match cmd.as_str() {
                    "print" if self.at_print_axioms_keyword() => self.print_axioms_decl(start_span),
                    "guard" => self.guard_decl(start_span),
                    "guard_msgs" => self.guard_msgs_decl(start_span, hash_index),
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
                    "reduce" => self.reduce_decl(start_span),
                    // `#whnf` and `#norm_num` are no commands of pinned Lean
                    // without Mathlib (`unexpected token '#'; expected
                    // command`), so they take the unknown-command refusal
                    // below. They used to be parsed as `#eval`, which ran
                    // their term and accepted the command.
                    // An unknown hash command is a named refusal, like every
                    // other unknown command (`decl::mod`'s identifier arm).
                    // It used to be skipped and replaced by `#check _`, whose
                    // hole reached the kernel as an unknown free variable, so
                    // `#guard`, `#guard_msgs` and `#print axioms` each failed
                    // as `Kernel check failed for [anonymous]` before they
                    // were parsed — a fabricated command standing in for one
                    // Clean never read.
                    other => {
                        let raw = format!("unknown command `#{other}`");
                        Ok(self.skip_to_next_decl(&raw, start_span))
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
    ///
    /// `modifiers` are the ones written before `abbrev` (`private abbrev`):
    /// they used to be dropped here, so a `private abbrev` was parsed as a
    /// public one and every importer could name it (G21 B2; Lean 4.8.0
    /// refuses an importer's use with `unknown identifier`).
    pub(in crate::grammar) fn abbrev_decl(
        &mut self,
        start_span: Span,
        attrs: Vec<Attribute>,
        modifiers: DeclModifiers,
    ) -> Result<SurfaceDecl, ParseError> {
        // Check if abbrev is a modifier for class
        if self.eat(&TokenKind::Class) {
            return self.class_decl_with_mods(start_span, modifiers);
        }
        // Parse like def but with is_abbrev = true
        let modifiers = DeclModifiers {
            is_abbrev: true,
            ..modifiers
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
        while let TokenKind::Ident(name) = self.current_kind() {
            // A command word at the start of a line ends the target list, as
            // a reserved token does in Lean: `attribute [coe] Subtype.val`
            // followed by `initialize_simps_projections Subtype (val → coe)`
            // used to take the command as two more targets (`Data/Subtype.lean`,
            // measured 2026-09-12).
            if self.current().preceded_by_newline && Self::is_boundary_command_keyword(name) {
                break;
            }
            // So does a line-start `local instance` / `local notation` …:
            // `attribute [instance] i16` followed by `local instance i17 …`
            // took `local` as a second target, the command failed ("attribute
            // target 'local' not found"), `i16` was never an instance, and the
            // declarations after it were credited against a state without it
            // (Lean 4.8.0 takes i16; round-25 random battery d006).
            if self.starts_local_command_at(0) {
                break;
            }
            // And a line-start `meta`, a token in pinned Lean
            // (`starts_meta_command_at`): `attribute [aesop …] boundNormNum`
            // followed by `meta def boundLinarith` (`Mathlib/Tactic/Bound.lean`).
            if self.starts_meta_command_at(0) {
                break;
            }
            names.push(self.qualified_ident()?);
        }

        let attribute = SurfaceDecl::Attribute {
            span: start_span,
            attrs,
            names,
        };
        // `attribute [...] names in <command>`: Lean's generic trailing
        // `cmd₁ in cmd₂` (`Lean/Parser/Command.lean:825-826`) expands to
        // `section cmd₁ <endLocalScope> cmd₂ end`
        // (`Lean/Elab/BuiltinCommand.lean:516-519`), so the attribute is
        // scoped to the one command. Measured before: the `in` became a raw
        // declaration and the command after it was parsed on its own
        // (Mathlib `Logic/Unique.lean:240`).
        if self.eat(&TokenKind::In) {
            let body = self.decl()?;
            return Ok(SurfaceDecl::Section {
                span: start_span,
                name: None,
                decls: vec![attribute, body],
                noncomputable: false,
            });
        }
        Ok(attribute)
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

        // `set_option hygiene b`: the templates declared while it is in
        // force are expanded with (or without) macro scopes.
        let hygiene = (name.is_unescaped_component("hygiene"))
            .then_some(value.as_deref())
            .flatten()
            .and_then(|value| match value {
                "false" => Some(true),
                "true" => Some(false),
                _ => None,
            });
        // Check for `in <declaration>` form (per-declaration scoping).
        let body = if self.eat(&TokenKind::In) {
            let outer = self.hygiene_off;
            if let Some(off) = hygiene {
                self.hygiene_off = off;
            }
            let body = self.decl();
            self.hygiene_off = outer;
            Some(Box::new(body?))
        } else {
            if let Some(off) = hygiene {
                self.hygiene_off = off;
            }
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
            names.push(self.name_token(&name)?);
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
    /// - `alias ⟨fwdName, bwdName⟩ := iffThm` — the iff-destructuring form;
    ///   `fwdName := Iff.mp iffThm` and `bwdName := Iff.mpr iffThm`. A `_`
    ///   entry skips that direction.
    ///
    /// Batteries' `elab`s (`Batteries/Tactic/Alias.lean`, rev 66e469188) spell
    /// the operator as the literal token `" := "` in both forms, so the Lean 3
    /// arrow spellings `alias foo ← bar` and `alias ⟨f, g⟩ ← bar` are refused
    /// here exactly as Lean refuses them (`unexpected token '←'; expected ':='`).
    ///
    /// Preserve the target's full telescope in a dedicated alias declaration.
    /// Leading attributes/modifiers carry through to each generated constant.
    pub(in crate::grammar) fn alias_decl(
        &mut self,
        start_span: Span,
        attrs: Vec<Attribute>,
        modifiers: DeclModifiers,
    ) -> Result<SurfaceDecl, ParseError> {
        if self.eat(&TokenKind::LAngle) {
            // Iff-destructuring form: `alias ⟨fwd, bwd⟩ := iffThm`.
            let mut names: Vec<Option<SurfaceName>> = Vec::with_capacity(2);
            for _ in 0..2 {
                if !names.is_empty() {
                    self.expect(&TokenKind::Comma)?;
                }
                if self.eat(&TokenKind::Underscore) {
                    names.push(None);
                } else {
                    names.push(Some(self.qualified_ident()?));
                }
            }
            self.expect(&TokenKind::RAngle)?;
            // Operator: `:=` only; Batteries has no `←` form.
            self.expect(&TokenKind::ColonEq)?;
            let target = self.qualified_ident()?;
            let names = names
                .into_iter()
                .enumerate()
                .filter_map(|(i, name)| name.map(|name| (name, Some(i == 0))))
                .collect();
            Ok(SurfaceDecl::Alias {
                span: Span {
                    start: start_span.start,
                    end: self.prev_span().end,
                },
                names,
                target,
                attrs,
                modifiers,
            })
        } else {
            // Plain form: `alias newName := target`.
            let name = self.qualified_ident()?;
            self.expect(&TokenKind::ColonEq)?;
            let target = self.qualified_ident()?;
            Ok(SurfaceDecl::Alias {
                span: Span {
                    start: start_span.start,
                    end: self.prev_span().end,
                },
                names: vec![(name, None)],
                target,
                attrs,
                modifiers,
            })
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

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Declaration parsing for Lean 4 syntax.
//!
//! Split into focused submodules:
//! - `def_theorem`: def, theorem, axiom, opaque, termination hints
//! - `inductive`: inductive, coinductive, constructor types
//! - `structure`: structure, deriving, field parsing, universe params, binders
//! - `class_instance`: class, instance, instance field parsing
//! - `commands`: example, import, namespace, section, universe, variable,
//!   open, export, mutual, hash commands, abbrev, attribute, set_option

mod class_instance;
mod commands;
mod def_theorem;
mod inductive;
mod structure;

pub(in crate::grammar) use def_theorem::EquationArmBoundary;

use super::Parser;
use crate::lexer::TokenKind;
use crate::surface::modifiers::{DeclModifiers, DeclScope, Visibility};
use crate::surface::*;
use crate::ParseError;

impl Parser {
    /// Parse a file (sequence of declarations)
    ///
    /// Uses error recovery: when a declaration fails to parse, the parser
    /// skips to the next declaration keyword and continues. This is critical
    /// for LLM-generated Lean code where individual declarations may have
    /// syntax errors but the rest of the file is valid.
    pub(super) fn file(&mut self) -> Result<Vec<SurfaceDecl>, ParseError> {
        let mut decls = Vec::new();

        while !matches!(self.current_kind(), TokenKind::Eof) {
            let span = self.current_span();
            match self.decl() {
                Ok(d) => decls.push(d),
                Err(err) => {
                    // A universe-offset-too-large error (`Sort (u + n)`, `n > 32`)
                    // is an unambiguous syntax error, not a resyncable typo. Skip
                    // the RawDecl recovery — whose generic "raw declaration"
                    // placeholder would launder the offset diagnostic into
                    // downstream garbage ("error-recovery 9999 Nat 0") — and
                    // propagate the typed error verbatim so the real
                    // `checkUniverseOffset` message (offset + max) reaches the
                    // user, matching Lean's loud rejection.
                    if matches!(err, ParseError::UniverseOffsetTooLarge { .. }) {
                        return Err(err);
                    }
                    // Recovery: skip to the next declaration keyword and
                    // insert a RawDecl placeholder for the malformed region.
                    decls.push(self.skip_to_next_decl_with_recovery("error-recovery", span, &err));
                }
            }
        }

        Ok(decls)
    }

    /// Parse a declaration
    pub(super) fn decl(&mut self) -> Result<SurfaceDecl, ParseError> {
        self.decl_with_modifiers(DeclModifiers::default())
    }

    /// Parse a declaration with accumulated modifiers.
    ///
    /// Modifiers (private, protected, partial, noncomputable, unsafe, scoped, local)
    /// are accumulated before the declaration keyword and threaded into the resulting
    /// `SurfaceDecl` node.
    fn decl_with_modifiers(&mut self, modifiers: DeclModifiers) -> Result<SurfaceDecl, ParseError> {
        // Parse leading attributes
        let attrs = self.attributes()?;

        let span = self.current_span();

        match self.current_kind() {
            TokenKind::Def => {
                self.advance();
                self.def_decl_with_mods(span, attrs, modifiers)
            }
            TokenKind::Theorem | TokenKind::Lemma => {
                self.advance();
                self.theorem_decl_with_mods(span, attrs, modifiers)
            }
            TokenKind::Axiom => {
                self.advance();
                self.axiom_decl_with_mods(span, attrs, modifiers)
            }
            TokenKind::Opaque => {
                self.advance();
                self.opaque_decl_with_mods(span, attrs, modifiers)
            }
            TokenKind::Inductive => {
                self.advance();
                self.inductive_decl_with_mods(span, modifiers)
            }
            TokenKind::Coinductive => {
                self.advance();
                self.coinductive_decl_with_mods(span, modifiers)
            }
            TokenKind::Codata => {
                self.advance();
                self.codata_decl_with_mods(span, modifiers)
            }
            TokenKind::Codef => {
                self.advance();
                self.codef_decl_with_mods(span, modifiers)
            }
            TokenKind::Structure => {
                self.advance();
                self.structure_decl_with_mods(span, modifiers)
            }
            TokenKind::Class => {
                self.advance();
                // `class inductive Foo …` (Lean `Command.lean`) declares an
                // inductive type that is additionally registered as a type
                // class. Parse the inductive body; the class-registration
                // (instance-search integration) is descoped — the type and its
                // constructors register exactly as a plain inductive, which is
                // what Lean accepts for the declaration.
                if matches!(self.current_kind(), TokenKind::Inductive) {
                    self.advance();
                    self.inductive_decl_with_mods(span, modifiers)
                } else {
                    self.class_decl_with_mods(span, modifiers)
                }
            }
            TokenKind::Instance => {
                self.advance();
                self.instance_decl_with_mods(span, &attrs, modifiers)
            }
            TokenKind::Example => {
                self.advance();
                self.example_decl(span)
            }
            TokenKind::Import => {
                self.advance();
                self.import_decl(span)
            }
            TokenKind::Namespace => {
                self.advance();
                self.namespace_decl(span)
            }
            TokenKind::Section => {
                self.advance();
                self.section_decl(span)
            }
            TokenKind::Universe => {
                self.advance();
                self.universe_decl(span)
            }
            TokenKind::Variable => {
                self.advance();
                self.variable_decl(span)
            }
            TokenKind::Open => {
                self.advance();
                self.open_decl(span)
            }
            TokenKind::Export => {
                self.advance();
                self.export_decl(span)
            }
            TokenKind::Deriving => {
                self.advance();
                self.deriving_instance_decl(span)
            }
            TokenKind::Mutual => {
                self.advance();
                self.mutual_decl(span)
            }
            TokenKind::Hash => {
                self.advance();
                self.hash_command(span)
            }
            // Handle modifiers (private, protected, partial, etc.)
            // Accumulate into DeclModifiers and recurse.
            TokenKind::Private => {
                self.advance();
                let mut mods = modifiers;
                mods.visibility = Visibility::Private;
                self.decl_with_modifiers(mods)
            }
            TokenKind::Protected => {
                self.advance();
                let mut mods = modifiers;
                mods.visibility = Visibility::Protected;
                self.decl_with_modifiers(mods)
            }
            // Lean 4 module-system visibility modifier. `public` may precede a
            // declaration (`public def`), an import (`public import X`), or a
            // section (`public section`). Visibility is transparent to
            // type-checking (it governs export/module semantics only), so we
            // record it and parse the following construct exactly as normal.
            TokenKind::Public => {
                self.advance();
                let mut mods = modifiers;
                mods.visibility = Visibility::Public;
                self.decl_with_modifiers(mods)
            }
            // Lean 4 module-system `module` header command. It declares the file
            // a module (Lean module system) and is a no-op for checking. It only
            // ever appears leading, before the first real declaration, so we
            // consume it and parse the following declaration in its place —
            // `module` itself contributes no node to the declaration stream.
            TokenKind::Module => {
                self.advance();
                self.decl_with_modifiers(modifiers)
            }
            TokenKind::Partial => {
                self.advance();
                let mut mods = modifiers;
                mods.is_partial = true;
                self.decl_with_modifiers(mods)
            }
            TokenKind::Unsafe => {
                self.advance();
                let mut mods = modifiers;
                mods.is_unsafe = true;
                self.decl_with_modifiers(mods)
            }
            TokenKind::Noncomputable => {
                self.advance();
                let mut mods = modifiers;
                mods.is_noncomputable = true;
                self.decl_with_modifiers(mods)
            }
            TokenKind::Abbrev => {
                self.advance();
                self.abbrev_decl(span, attrs)
            }
            TokenKind::Attribute => {
                self.advance();
                self.attribute_cmd(span)
            }
            TokenKind::SetOption => {
                self.advance();
                self.set_option_cmd(span)
            }
            // Macro system declarations
            TokenKind::Syntax => {
                self.advance();
                self.syntax_decl(span)
            }
            TokenKind::Macro => {
                self.advance();
                self.macro_decl(span)
            }
            TokenKind::MacroRules => {
                self.advance();
                self.macro_rules_decl(span)
            }
            TokenKind::Elab => {
                self.advance();
                self.elab_decl(span)
            }
            TokenKind::Notation => {
                self.advance();
                self.notation_decl(span, NotationKind::Notation, modifiers.scope)
            }
            TokenKind::Infixl => {
                self.advance();
                self.notation_decl(span, NotationKind::Infixl, modifiers.scope)
            }
            TokenKind::Infixr => {
                self.advance();
                self.notation_decl(span, NotationKind::Infixr, modifiers.scope)
            }
            TokenKind::Infix => {
                self.advance();
                self.notation_decl(span, NotationKind::Infix, modifiers.scope)
            }
            TokenKind::Prefix => {
                self.advance();
                self.notation_decl(span, NotationKind::Prefix, modifiers.scope)
            }
            TokenKind::Postfix => {
                self.advance();
                self.notation_decl(span, NotationKind::Postfix, modifiers.scope)
            }
            // Handle scoped modifier followed by other things
            TokenKind::Scoped => {
                self.advance();
                let mut mods = modifiers;
                mods.scope = DeclScope::Scoped;
                self.decl_with_modifiers(mods)
            }
            // Handle declare_syntax_cat as a proper command
            TokenKind::Ident(name) if name == "declare_syntax_cat" => {
                self.advance();
                self.declare_syntax_cat_decl(span)
            }
            // Handle declare_aesop_rule_sets for Mathlib-style domain tactics
            TokenKind::Ident(name) if name == "declare_aesop_rule_sets" => {
                self.advance();
                self.declare_aesop_rule_sets_decl(span)
            }
            // Batteries/Mathlib `alias newName := target` (and the `⟨fwd, bwd⟩`
            // iff-destructuring and `←` reverse forms) — desugared to real
            // `def`s so the alias resolves like any other definition.
            TokenKind::Ident(name) if name == "alias" => {
                self.advance();
                self.alias_decl(span, attrs, modifiers)
            }
            // Mathlib/Batteries `library_note «title»` documentation command —
            // a no-op that carries no checkable content.
            TokenKind::Ident(name) if name == "library_note" => {
                self.advance();
                self.library_note_decl(span)
            }
            // Mathlib `initialize_simps_projections S (proj → name …)` sets up the
            // `@[simps]` projection-name table — a no-op for kernel checking (Clean
            // does not model `@[simps]`). Real Lean registers the command via a
            // macro/elab; a drop-in must ACCEPT it (skip its arguments up to the
            // next declaration) rather than wall the file. Consume the arguments
            // and elaborate to a no-op (reusing the `LibraryNote` Skipped marker).
            TokenKind::Ident(name)
                if name == "initialize_simps_projections"
                    || name == "initialize_simps_projections?" =>
            {
                // The trace form `initialize_simps_projections?` lexes as a single
                // ident with the `?` glued on, so both spellings are matched here.
                self.advance();
                // The structure name (a possibly-dotted ident). `skip_to_next_decl`
                // is unusable here: it stops at the very first ident (idents can
                // start a command), leaving `S (proj → name)` to be mis-parsed.
                while matches!(self.current_kind(), TokenKind::Ident(_)) {
                    self.advance();
                    if !self.eat(&TokenKind::Dot) {
                        break;
                    }
                }
                // Optional balanced `( … )` projection spec (contains idents, `→`,
                // and possibly nested parens); consume it whole.
                if self.check(&TokenKind::LParen) {
                    let mut depth = 0usize;
                    loop {
                        match self.current_kind() {
                            TokenKind::LParen => {
                                depth += 1;
                                self.advance();
                            }
                            TokenKind::RParen => {
                                self.advance();
                                depth -= 1;
                                if depth == 0 {
                                    break;
                                }
                            }
                            TokenKind::Eof => break,
                            _ => {
                                self.advance();
                            }
                        }
                    }
                }
                Ok(SurfaceDecl::LibraryNote {
                    span,
                    title: "initialize_simps_projections".to_string(),
                })
            }
            // Handle 'local' modifier and continue with declaration
            TokenKind::Ident(name) if name == "local" => {
                self.advance();
                let mut mods = modifiers;
                mods.scope = DeclScope::Local;
                self.decl_with_modifiers(mods)
            }
            // Lean 4 module-system `meta import X` — a compile-time-only import.
            // `meta` is not a reserved keyword (it is a valid identifier
            // elsewhere), so this fires only when it directly precedes `import`.
            // The `meta` marker is transparent to checking: resolve X as usual.
            TokenKind::Ident(name)
                if name == "meta" && matches!(self.peek_kind(1), Some(TokenKind::Import)) =>
            {
                self.advance();
                self.decl_with_modifiers(modifiers)
            }
            // A stray `end` at the top level (no enclosing
            // `namespace`/`section`) is invalid Lean, but historically caused
            // an infinite loop here because (a) `decl_with_modifiers` had no
            // case for it, and (b) `End` is in `is_decl_keyword`, so the
            // recovery in `skip_to_next_decl_impl` exited its loop without
            // advancing past the offending token, leaving the cursor parked
            // on `end` for `file()` to dispatch again. We now consume the
            // `end` keyword (and an optional dotted name suffix) and report
            // the construct as a `RawDecl` so elaboration surfaces a real
            // diagnostic instead of hanging. See the audit at
            // `docs/mathbot/CLEAN-VERIFIER-AUDIT-2026-05-27.md` item 4.
            TokenKind::End => {
                self.advance();
                let mut content = String::from("stray-end");
                while let TokenKind::Ident(seg) = self.current_kind().clone() {
                    content.push(' ');
                    content.push_str(&seg);
                    self.advance();
                    if matches!(self.current_kind(), TokenKind::Dot) {
                        self.advance();
                        content.push('.');
                    } else {
                        break;
                    }
                }
                Ok(SurfaceDecl::RawDecl { span, content })
            }
            _ => {
                let raw = format!("{:?}", self.current_kind());
                Ok(self.skip_to_next_decl(&raw, span))
            }
        }
    }
}

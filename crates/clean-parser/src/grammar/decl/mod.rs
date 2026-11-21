// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Declaration parsing for Lean 4 syntax.
//!
//! Split into focused submodules:
//! - `def_theorem`: def, theorem, axiom, opaque
//! - `termination_hints`: termination clauses and recovery
//! - `inductive`: inductive, coinductive, constructor types
//! - `structure`: structure, deriving, field parsing, universe params, binders
//! - `class_instance`: class, instance, instance field parsing
//! - `commands`: example, import, namespace, section, universe, variable,
//!   open, export, mutual, hash commands, abbrev, attribute, set_option
//! - `header`: the file header (`module`, header imports)
//! - `doc_before`: whether a doc comment ends right before a token (the
//!   header ends at one, and a declaration doc comment opens a modifier prefix)
//! - `module_spelling`: pinned Lean's verdict on the modifiers in front of
//!   `import`, `section` and `variable`

mod class_instance;
mod commands;
mod commands_misc;
mod def_theorem;
mod doc_before;
mod header;
mod inductive;
mod module_spelling;
mod structure;
mod termination_hints;
mod test_commands;

use module_spelling::GuardedCommand;

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

        // The header (`module`? and the header imports, `header.rs`) is read
        // and recorded first, as Lean's `parseHeader` reads it before any
        // command; its imports enter the stream as `SurfaceDecl::Import`.
        self.file_header = self.file_header(&mut decls)?;

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
                    // user, matching Lean's loud rejection. A module-system
                    // refusal is the same: Lean's message, the file refused.
                    // After a recovered header import it is neither: Lean's
                    // first message is the header's, and pinned Lean reads no
                    // command after a header error (`header.rs`), so it is
                    // recovered like any other error.
                    if err.refuses_file() && !self.header_recovered {
                        return Err(err);
                    }
                    // Recovery: skip to the next declaration keyword and
                    // insert a RawDecl placeholder for the malformed region.
                    decls.push(self.skip_to_next_decl_with_recovery("error-recovery", span, &err));
                }
            }
            // A refusal raised inside a `namespace`/`section` body.
            if let Some(err) = self.file_refusal.take() {
                return Err(err);
            }
        }

        // A doc comment is a Lean token even though our lexer stores it in
        // the side table. Preserve a recovered header's earlier diagnostic.
        if let (false, Some(err)) = (self.header_recovered, self.eof_declaration_doc_refusal()) {
            return Err(err);
        }
        Ok(decls)
    }

    /// Parse a declaration.
    ///
    /// Every declaration starts with the parser's full red zone
    /// (`Parser::EXPR_STACK_RED_ZONE`): the frames between here and the first
    /// guarded expression entry (`expr_in_slot`) are unguarded, and a caller
    /// can arrive with little stack left — the elaborator, whose own red zone
    /// is smaller, parses the codata seed library in the middle of
    /// elaborating a `codata` command, and a 1 MB thread overflowed there
    /// (regression pin
    /// `codata_cmd_tests::test_codata_stream_encoding_survives_small_thread_stack`).
    pub(super) fn decl(&mut self) -> Result<SurfaceDecl, ParseError> {
        // A command nested in this one (`variable … in <command>`) has its
        // own modifier prefix; this one's is restored after it.
        let outer_command_start = std::mem::replace(&mut self.command_start, self.pos);
        let origin_checkpoint = self.origins.as_ref().map(|origins| origins.checkpoint());
        let documentation = self.documentation_before(self.pos);
        let mut decl = stacker::maybe_grow(
            Self::EXPR_STACK_RED_ZONE,
            Self::EXPR_STACK_GROW_SIZE,
            || {
                self.decl_with_modifiers(DeclModifiers {
                    visibility: self.default_visibility,
                    ..DeclModifiers::default()
                })
            },
        );
        if let Ok(declaration) = &mut decl {
            if let Some(modifiers) = declaration.modifiers_mut() {
                if documentation.is_some() {
                    modifiers.documentation = documentation;
                }
            }
        }
        self.command_start = outer_command_start;
        if let Some(origins) = &mut self.origins {
            match &decl {
                Ok(decl) => origins.declaration_root(decl),
                Err(_) => {
                    if let Some(checkpoint) = origin_checkpoint {
                        origins.rollback(checkpoint);
                    }
                }
            }
        }
        decl
    }

    /// Parse a declaration with accumulated modifiers.
    ///
    /// Modifiers (private, protected, partial, noncomputable, unsafe, scoped, local)
    /// are accumulated before the declaration keyword and threaded into the resulting
    /// `SurfaceDecl` node.
    fn decl_with_modifiers(&mut self, modifiers: DeclModifiers) -> Result<SurfaceDecl, ParseError> {
        self.decl_with_modifiers_and_attrs(modifiers, Vec::new())
    }

    /// [`Self::decl_with_modifiers`] carrying the attributes already parsed
    /// before a modifier. Lean's `declModifiers` puts `@[…]` BEFORE the
    /// visibility and `noncomputable`/`unsafe`/`partial` words, so
    /// `@[simp] private theorem` is the ordinary order; every modifier arm used
    /// to recurse through a fresh `attributes()` read and DROP what it had
    /// parsed — `@[simp] private theorem myf_eq` registered no simp lemma
    /// (measured 2026-09-12; Lean accepts the file).
    fn decl_with_modifiers_and_attrs(
        &mut self,
        modifiers: DeclModifiers,
        prior_attrs: Vec<Attribute>,
    ) -> Result<SurfaceDecl, ParseError> {
        if self.pos == self.command_start {
            if let Some(err) = self.leading_stacked_doc_refusal() {
                return Err(err);
            }
        }
        // Parse leading attributes (after any already carried in).
        let mut attrs = prior_attrs;
        attrs.extend(self.attributes()?);

        if matches!(
            self.current_kind(),
            TokenKind::Def | TokenKind::Abbrev | TokenKind::Instance
        ) && !attrs
            .iter()
            .any(|a| matches!(a, Attribute::Unknown(n) if n == "expose" || n == "no_expose"))
        {
            if let Some(exposed) = self.default_exposure {
                attrs.push(Attribute::Unknown(
                    if exposed { "expose" } else { "no_expose" }.into(),
                ));
            }
        }
        let span = self.current_span();
        // Column of the command keyword, for the binder-run line barrier.
        let keyword_col = self.current().col;

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
            // `import`, `section` and `variable` used to drop whatever
            // modifiers stood in front of them (`private import X`, `private
            // section`, `public variable` parsed as the bare command). Pinned
            // Lean takes only the prefixes `module_spelling` models, and no
            // prefix at all in front of an `import` past the header (plan item
            // `formats-module-spelling-refusals`). A declaration doc comment
            // is a prefix word too.
            TokenKind::Import => {
                if self.has_modifier_prefix() {
                    if let Some(err) = self.modifier_prefix_refusal(GuardedCommand::Import) {
                        return Err(err);
                    }
                }
                self.advance();
                self.import_decl(span)
            }
            TokenKind::Namespace => {
                self.advance();
                self.namespace_decl(span)
            }
            TokenKind::Section => {
                if self.has_modifier_prefix() {
                    if let Some(err) = self.modifier_prefix_refusal(GuardedCommand::Section) {
                        return Err(err);
                    }
                }
                self.advance();
                let previous_visibility =
                    std::mem::replace(&mut self.default_visibility, modifiers.visibility);
                let exposure = attrs
                    .iter()
                    .rev()
                    .find_map(|a| match a {
                        Attribute::Unknown(n) if n == "expose" => Some(true),
                        Attribute::Unknown(n) if n == "no_expose" => Some(false),
                        _ => None,
                    })
                    .or(self.default_exposure);
                let previous_exposure = std::mem::replace(&mut self.default_exposure, exposure);
                let section = self.section_decl(span);
                self.default_exposure = previous_exposure;
                self.default_visibility = previous_visibility;
                let mut section = section?;
                if let SurfaceDecl::Section { noncomputable, .. } = &mut section {
                    *noncomputable = modifiers.is_noncomputable;
                }
                Ok(section)
            }
            TokenKind::Universe => {
                self.advance();
                self.universe_decl(span, keyword_col)
            }
            TokenKind::Variable => {
                if self.has_modifier_prefix() {
                    if let Some(err) = self.modifier_prefix_refusal(GuardedCommand::Variable) {
                        return Err(err);
                    }
                }
                let visibility = self.has_modifier_prefix().then_some(modifiers.visibility);
                self.advance();
                self.variable_decl(span, keyword_col, visibility)
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
                self.decl_with_modifiers_and_attrs(mods, attrs)
            }
            TokenKind::Protected => {
                self.advance();
                let mut mods = modifiers;
                mods.visibility = Visibility::Protected;
                self.decl_with_modifiers_and_attrs(mods, attrs)
            }
            // Lean 4 module-system visibility modifier. `public` may precede a
            // declaration (`public def`) or a section (`public section`);
            // `public import X` in the header is read by `header.rs`, and one
            // past the header (after a command or a doc comment, where the
            // header ends) is refused at the `Import` arm. Visibility is
            // transparent to type-checking (it governs export/module
            // semantics only), so it is recorded and the following
            // construct parsed exactly as normal.
            TokenKind::Public => {
                self.advance();
                let mut mods = modifiers;
                mods.visibility = Visibility::Public;
                self.decl_with_modifiers_and_attrs(mods, attrs)
            }
            TokenKind::Partial => {
                self.advance();
                let mut mods = modifiers;
                mods.is_partial = true;
                self.decl_with_modifiers_and_attrs(mods, attrs)
            }
            TokenKind::Unsafe => {
                self.advance();
                let mut mods = modifiers;
                mods.is_unsafe = true;
                self.decl_with_modifiers_and_attrs(mods, attrs)
            }
            TokenKind::Noncomputable => {
                self.advance();
                let mut mods = modifiers;
                mods.is_noncomputable = true;
                self.decl_with_modifiers_and_attrs(mods, attrs)
            }
            TokenKind::Abbrev => {
                self.advance();
                self.abbrev_decl(span, attrs, modifiers)
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
                if self.check(&TokenKind::LBracket) {
                    return self.scoped_in_namespace_notation(mods, attrs);
                }
                self.decl_with_modifiers_and_attrs(mods, attrs)
            }
            // Lean 4 `include x y` / `omit x y` — section-variable inclusion
            // control. Pinned Lean v4.30.0-rc2 reserves both words (`def
            // include` is "unexpected token"), but Clean lexes them as
            // identifiers, so these fire only when the word is followed by an
            // identifier, which is the only name shape modelled; a line-start
            // one also ends a preceding term (`is_boundary_command_keyword`).
            //
            // Before this existed, `include h` was not a command to this
            // parser at all: the PRECEDING `variable` line's bare-name binder
            // run absorbed both words as untyped section variables, and the
            // minted `h` shadowed the real `(h : Involutive f)`. That is fixed
            // in two independent places — the barrier in `variable_decl` stops
            // the absorption, and this arm gives the command a meaning.
            TokenKind::Ident(name)
                if (name == "include" || name == "omit")
                    && self.peek_token(1).is_some_and(|t| {
                        matches!(t.kind, TokenKind::Ident(_)) && !t.preceded_by_newline
                    }) =>
            {
                let include = name == "include";
                self.advance();
                let names =
                    self.include_omit_names(if include { "include" } else { "omit" }, keyword_col)?;
                let command = if include {
                    SurfaceDecl::IncludeVars { span, names }
                } else {
                    SurfaceDecl::OmitVars { span, names }
                };
                // `include … in <command>` / `omit … in <command>`: Lean's
                // `cmd₁ in cmd₂` is `section cmd₁ cmd₂ end`, exactly as for
                // `variable … in` (`variable_decl`), and a section already
                // restores the included set at its end.
                if self.eat(&TokenKind::In) {
                    let body = self.decl()?;
                    return Ok(SurfaceDecl::Section {
                        span,
                        name: None,
                        decls: vec![command, body],
                        noncomputable: false,
                    });
                }
                Ok(command)
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
            // Batteries/Mathlib `alias newName := target` and the `⟨fwd, bwd⟩`
            // iff-destructuring form, kept as a dedicated `SurfaceDecl::Alias`.
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
                self.decl_with_modifiers_and_attrs(mods, attrs)
            }
            // `meta import X` past the header (the header's own is read by
            // `header.rs`): `meta` is not a reserved keyword (it is a valid
            // identifier elsewhere), so this fires only when it directly
            // precedes `import`, which the `Import` arm then refuses as Lean
            // does.
            TokenKind::Ident(name)
                if name == "meta" && matches!(self.peek_kind(1), Some(TokenKind::Import)) =>
            {
                self.advance();
                self.decl_with_modifiers_and_attrs(modifiers, attrs)
            }
            // `meta def` / `meta theorem` … — the module system's compile-time
            // phase marker (Lean's `declModifiers` `meta`), transparent to
            // checking like `meta import`. Only before a declaration keyword
            // or another modifier, so a term named `meta` is untouched
            // (`Mathlib/Order/Basic.lean`'s `meta def` in
            // `Mathlib.Tactic.GCongr`, measured 2026-09-12: "unknown command
            // `meta`").
            TokenKind::Ident(name)
                if name == "meta"
                    && matches!(
                        self.peek_kind(1),
                        Some(
                            TokenKind::Def
                                | TokenKind::Theorem
                                | TokenKind::Lemma
                                | TokenKind::Instance
                                | TokenKind::Abbrev
                                | TokenKind::Structure
                                | TokenKind::Class
                                | TokenKind::Inductive
                                | TokenKind::Opaque
                                | TokenKind::Axiom
                                | TokenKind::Partial
                                | TokenKind::Unsafe
                                | TokenKind::Noncomputable
                                | TokenKind::Private
                                | TokenKind::Protected
                                | TokenKind::Public
                        )
                    ) =>
            {
                self.advance();
                self.decl_with_modifiers_and_attrs(modifiers, attrs)
            }
            // Mathlib/Lean `grind_pattern [ident]? ident => term,+ (where …)?`
            // registers an E-matching pattern for `grind`. A no-op for
            // checking (skipping it only weakens `grind`, it never accepts
            // more); consumed to the next command so the preceding term does
            // not absorb it (`Logic/Basic.lean:722`, measured 2026-09-12).
            TokenKind::Ident(name) if name == "grind_pattern" || name == "init_grind_norm" => {
                self.advance();
                while !matches!(self.current_kind(), TokenKind::Eof)
                    && !(self.current().preceded_by_newline && self.current().col == 0)
                {
                    self.advance();
                }
                Ok(SurfaceDecl::LibraryNote {
                    span,
                    title: "grind_pattern".to_string(),
                })
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
            // An identifier in command position that no arm above claimed is
            // an UNKNOWN COMMAND. Name it.
            //
            // LANE FAILOPEN: the generic arm below labels the recovery with the
            // raw token debug (`Ident("frobnicate") frobnicate h`), which reads
            // as parser noise rather than as a refusal, and the words that
            // followed it were often not even reachable here — the preceding
            // `variable` had already eaten them. With that absorption closed,
            // this is the path every unrecognised command line takes, so it
            // says what it refused and why. A named refusal beats a silent
            // guess: the declaration still fails (`RawDecl` is an error at
            // elaboration), but the diagnostic now names the token.
            TokenKind::Ident(name) => {
                let raw = format!("unknown command `{name}`");
                Ok(self.skip_to_next_decl(&raw, span))
            }
            _ => {
                let raw = format!("{:?}", self.current_kind());
                Ok(self.skip_to_next_decl(&raw, span))
            }
        }
    }
}

impl Parser {
    /// Mathlib's `scoped[NS] <command>` (`Mathlib/Tactic/ScopedNS.lean`):
    /// `with_weak_namespace _root_.NS scoped <command>` -- the command runs as
    /// `scoped` with `NS`, an ABSOLUTE namespace, as the current one, wherever
    /// it is written. Only the notation commands are modelled: `NS` stands on
    /// the notation-namespace stack while the declaration is parsed (so the
    /// parser registers, gates and hygienically resolves it under `NS`), and
    /// the declaration carries `NS` as its `scope_ns` so the elaborator does
    /// the same. Any other command after `scoped[NS]` stays a parse error
    /// rather than being accepted against the wrong namespace.
    fn scoped_in_namespace_notation(
        &mut self,
        modifiers: DeclModifiers,
        attrs: Vec<Attribute>,
    ) -> Result<SurfaceDecl, ParseError> {
        // The caller dispatched here on the `[`.
        self.advance();
        let namespace = self.qualified_ident()?;
        if !self.eat(&TokenKind::RBracket) {
            return Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current().col as usize,
                message: format!(
                    "expected `]` closing `scoped[{namespace}`, got {:?}",
                    self.current_kind()
                ),
            });
        }
        if !matches!(
            self.current_kind(),
            TokenKind::Notation
                | TokenKind::Infixl
                | TokenKind::Infixr
                | TokenKind::Infix
                | TokenKind::Prefix
                | TokenKind::Postfix
        ) {
            let err = ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current().col as usize,
                message: format!(
                    "`scoped[{namespace}]` is modelled for notation commands only, got {:?}",
                    self.current_kind()
                ),
            };
            // Consume the refused command's keyword: recovery forces no
            // progress once `scoped[NS]` is consumed, so it would otherwise
            // re-dispatch the command as a fresh, unscoped declaration.
            self.advance();
            return Err(err);
        }
        let open_mark = self.open_scoped_notation_ns.len();
        self.notation_ns_stack.push(namespace.clone());
        let decl = self.decl_with_modifiers_and_attrs(modifiers, attrs);
        self.notation_ns_stack.pop();
        self.open_scoped_notation_ns.truncate(open_mark);
        match decl? {
            SurfaceDecl::Notation {
                span,
                kind,
                precedence,
                pattern,
                expansion,
                scope,
                ..
            } => Ok(SurfaceDecl::Notation {
                span,
                kind,
                precedence,
                pattern,
                expansion,
                scope,
                scope_ns: Some(namespace),
            }),
            other => Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current().col as usize,
                message: format!(
                    "`scoped[{namespace}]` produced a non-notation declaration {other:?}"
                ),
            }),
        }
    }
}

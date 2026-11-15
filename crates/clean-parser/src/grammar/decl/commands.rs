// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Parsing for miscellaneous Lean 4 declaration commands:
//! example, import, namespace, section, universe, variable, include/omit,
//! open and export. The remaining commands are in `commands_misc.rs`.

use super::super::Parser;
use crate::lexer::TokenKind;
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

    /// Parse an `import` command that is not a header import: one after the
    /// header has ended (Lean refuses those, "invalid 'import' command, it
    /// must be used in the beginning of the file"; Clean still reads them), or
    /// one `Parser::parse_decl` is handed. The target grammar is the
    /// past-header one, `Parser::import_target` (`all` is the modifier only
    /// before a same-line name); the header's own is
    /// `Parser::header_import_target`.
    pub(in crate::grammar) fn import_decl(
        &mut self,
        start_span: Span,
    ) -> Result<SurfaceDecl, ParseError> {
        let (_all, module) = self.import_target()?;
        Ok(SurfaceDecl::Import {
            span: start_span,
            paths: vec![module],
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
        // A `variable` declared in the block dies at its `end`, and so does
        // a `set_option hygiene` set in it.
        let section_variables = self.section_variable_names.len();
        let hygiene_off = self.hygiene_off;
        let decls = self.scoped_block_decls_inner();
        self.section_variable_names.truncate(section_variables);
        self.hygiene_off = hygiene_off;
        decls
    }

    fn scoped_block_decls_inner(&mut self) -> Vec<SurfaceDecl> {
        let mut decls = Vec::new();
        while !matches!(self.current_kind(), TokenKind::End | TokenKind::Eof)
            && self.file_refusal.is_none()
        {
            let span = self.current_span();
            match self.decl() {
                Ok(d) => decls.push(d),
                // A module-system refusal refuses the whole file wherever it
                // stands (plan item `formats-module-spelling-refusals`): every
                // enclosing block stops, and `file()` or the `parse_decl`
                // entry point that parsed the outermost block returns it.
                // After a recovered header import it is recovered below
                // instead, as `file()` recovers it (`header_recovered`).
                Err(err @ ParseError::ModuleSyntaxRefused { .. }) if !self.header_recovered => {
                    self.file_refusal = Some(err);
                }
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
        Ok(self.namespace_block(start_span, name))
    }

    /// Parse the body of a `namespace <name>` whose keyword and name are
    /// already consumed, and close it against whatever `end` follows.
    ///
    /// ## Why this is not just "parse decls, eat `end`"
    ///
    /// Lean pushes ONE scope per component of the `namespace` name and closes
    /// exactly as many scopes as the `end` name has components. So the `end`
    /// name's width — not the `namespace` name's — decides how much is closed,
    /// and a PARTIAL `end` legally leaves the outer components open.
    ///
    /// Ground truth, Lean 4.30.0-rc2 (`set_option pp.fullNames true`):
    ///
    /// ```text
    ///   namespace Bundle.Pretriv / def inner / end Pretriv
    ///   def after_partial / end Bundle
    ///     => Bundle.Pretriv.inner : Nat
    ///        Bundle.after_partial : Nat      -- NOT `after_partial`
    ///   namespace A.B.C / end B.C            -- a 2-of-3 suffix is legal too
    ///   namespace A.B.C / end A              -- error: "Expected `C`"
    /// ```
    ///
    /// Clean's surface tree is structural rather than a scope stack, so a
    /// partial `end` is NORMALISED here into the balanced tree that means the
    /// same thing: the closed components become an inner `Namespace` node, and
    /// the components left open become an outer `Namespace` node whose body
    /// CONTINUES with the rest of the enclosing block. `namespace Bundle.Pretriv
    /// … end Pretriv … end Bundle` therefore parses as
    /// `Namespace(Bundle, [Namespace(Pretriv, …), …])`.
    ///
    /// That normalisation is what keeps the elaborator honest without a second
    /// namespace mechanism: every `Namespace` node it sees is now exactly
    /// balanced by its own `end`, so restoring the whole entered prefix on exit
    /// (`NamespaceState::exit_namespace`, the 6557c358d fix) is correct for
    /// every shape rather than only for the exact-match one. Before this, the
    /// two shapes were in direct conflict and each fix broke the other — the
    /// A/B is in `crates/clean-elab/tests/namespace_dotted_end_cross_module.rs`.
    ///
    /// Recursion terminates because a partial `end` consumes at least one
    /// component, so `outer` is strictly shorter than `name`.
    fn namespace_block(&mut self, start_span: Span, name: SurfaceName) -> SurfaceDecl {
        // Track the namespace for parse-time scoped custom notation: a
        // `scoped infixl` inside the block is tagged with (and active in)
        // this path; `open` activations made inside die at `end`.
        let open_mark = self.enter_notation_namespace(&name);

        // Parse declarations until `end` or end of file
        // In Lean 4, `namespace` without `end` is valid - the namespace ends at file end
        let decls = self.scoped_block_decls();

        self.exit_notation_namespace(open_mark);

        // `end` is optional - namespace can end at EOF.
        let closed = if self.eat(&TokenKind::End) {
            self.try_consume_end_name(&name)
        } else {
            0
        };

        let component_count = name.component_syntax().len();
        // `closed == 0` is a bare `end` or a name that does not match this
        // block at all; `closed == component_count` is the exact match. Both
        // close the whole block, which is what the unsplit node means.
        if closed == 0 || closed >= component_count {
            return SurfaceDecl::Namespace {
                span: start_span,
                name,
                decls,
            };
        }

        // Peel structural components, including their lexical origin. A
        // quoted `«A.B»` remains one component throughout a partial close.
        let mut outer = name;
        let mut inner_name = SurfaceName::from_name(clean_kernel::Name::anon());
        for _ in 0..closed {
            inner_name = outer.last_component().append(&inner_name);
            outer = outer.parent();
        }
        let inner = SurfaceDecl::Namespace {
            span: start_span,
            name: inner_name,
            decls,
        };

        // The outer components are still open: their body is this inner node
        // followed by the remainder of the enclosing block.
        match self.namespace_block(start_span, outer) {
            SurfaceDecl::Namespace {
                span,
                name: outer_name,
                decls: rest,
            } => {
                let mut body = Vec::with_capacity(rest.len() + 1);
                body.push(inner);
                body.extend(rest);
                SurfaceDecl::Namespace {
                    span,
                    name: outer_name,
                    decls: body,
                }
            }
            // `namespace_block` only ever returns a `Namespace`; keep the
            // inner node rather than dropping it if that ever changes.
            other => other,
        }
    }

    /// Parse section declaration: `section [Name] ... end [Name]`
    pub(in crate::grammar) fn section_decl(
        &mut self,
        start_span: Span,
    ) -> Result<SurfaceDecl, ParseError> {
        // Section name is optional. `local` is NOT a section name: it is the
        // declaration modifier of the section's first inner decl (`section` +
        // `local instance …` / `local notation …`) — Lean reserves `local` as
        // a keyword; escaped `«local»` is still an ordinary section name. Swallowing it
        // as the name silently DROPPED the modifier, so a `local instance`
        // registered as if global and leaked past `end` (B99, r82
        // `instprio_local_section_shadow`).
        let name = match self.current_kind() {
            TokenKind::Ident(id) if id != "local" || self.current().ident_escaped => {
                Some(self.ident()?)
            }
            _ => None,
        };

        // Parse declarations until `end` or end of file
        // In Lean 4, `section` without `end` is valid - the section ends at file end
        // An `open` / `open scoped` inside the section activates scoped
        // custom notation WITHIN the section only.
        let open_mark = self.open_scoped_notation_mark();
        let decls = self.scoped_block_decls();
        self.truncate_open_scoped_notation(open_mark);

        // `end` is optional - section can end at EOF
        if self.eat(&TokenKind::End) {
            // Optionally consume the section name after `end`. Sections can
            // be named with a compound (dotted) identifier in the wild even
            // though Lean 4 itself does not idiomatically use that; accept
            // either the full path or just the trailing segment.
            if let Some(n) = name.as_ref() {
                // A section name is a single component, so the only suffix a
                // matching `end` can name is the whole of it: there is no
                // partial-close case to normalise the way `namespace_block`
                // does.
                let _ = self.try_consume_end_name(n);
            }
        }

        Ok(SurfaceDecl::Section {
            span: start_span,
            name,
            decls,
            noncomputable: false,
        })
    }

    /// Consume an optional `Name` (possibly dotted) following a closing `end`
    /// keyword, and report HOW MANY components of `opening_name` it closes.
    ///
    /// Lean's rule (`elabEnd`) is a component-wise SUFFIX match: `end X` closes
    /// the innermost `X`, and the name may name any number of trailing
    /// components of the open block. Measured on Lean 4.30.0-rc2:
    ///
    /// ```text
    ///   namespace A.B.C / end C       -- ok, leaves `A.B` open
    ///   namespace A.B.C / end B.C     -- ok, leaves `A` open
    ///   namespace A.B.C / end A.B.C   -- ok, back to the root
    ///   namespace A.B.C / end A       -- error: Expected `C`, but found `A`
    /// ```
    ///
    /// Returns the number of segments consumed, or `0` when nothing was
    /// consumed — a bare `end`, or a name that is not a suffix of
    /// `opening_name`. On `0` the parser position is left unchanged so the
    /// caller can produce a clearer diagnostic upstream.
    fn try_consume_end_name(&mut self, opening_name: &SurfaceName) -> usize {
        let start = self.pos;
        let Ok(found) = self.qualified_ident() else {
            self.pos = start;
            return 0;
        };
        // Lean's rule: the `end` name must be a component-wise SUFFIX of the
        // open block's name. An `end` naming MORE components than the block has
        // (`end Bundle.Trivialization` against `namespace Trivialization`)
        // reaches past this block into its enclosing ones; that is legal Lean
        // but is not representable in one structural node, so it is left
        // unconsumed for the caller's diagnostic rather than mis-closed here.
        let count = found.component_syntax().len();
        if count == 0 || !opening_name.has_suffix(&found) {
            self.pos = start;
            return 0;
        }
        count
    }

    /// Parse universe declaration: `universe u v`
    pub(in crate::grammar) fn universe_decl(
        &mut self,
        start_span: Span,
        keyword_col: u32,
    ) -> Result<SurfaceDecl, ParseError> {
        let mut names = Vec::new();

        // Same line discipline as `variable` (see `variable_decl`): a
        // `universe u` line must not absorb the command line that follows it.
        while let TokenKind::Ident(_) = self.current_kind() {
            if !names.is_empty() && self.current().preceded_by_newline {
                let col = self.current().col;
                if col <= keyword_col {
                    break;
                }
            }
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
    ///
    /// `keyword_col` is the column of the `variable` keyword itself. It arms
    /// [`Parser::binder_run_line_barrier`] so the bare-name binder run cannot
    /// swallow the next command line — the LANE FAILOPEN defect, where
    /// `include h` on the line after a `variable` became two untyped section
    /// variables and the second one shadowed the real `h`.
    pub(in crate::grammar) fn variable_decl(
        &mut self,
        start_span: Span,
        keyword_col: u32,
        visibility: Option<Visibility>,
    ) -> Result<SurfaceDecl, ParseError> {
        self.binder_run_line_barrier = Some(keyword_col);
        let binders = self.binders()?;
        let names_mark = self.section_variable_names.len();
        self.section_variable_names
            .extend(binders.iter().map(|binder| binder.name.clone()));
        let variable = SurfaceDecl::Variable {
            span: start_span,
            binders,
            visibility,
        };

        // `variable … in <command>`: Lean's `cmd₁ in cmd₂` is
        // `section cmd₁ cmd₂ end`, so the variables scope over that one
        // command and die after it (pinned Lean v4.30.0-rc2: `variable (n :
        // Nat) in def f : Nat := n + 1` gives `f : Nat → Nat`, and a later
        // `def g : Nat := n` is `Unknown identifier n`). The anonymous section
        // is exactly the node a written `section … end` produces.
        if self.eat(&TokenKind::In) {
            let body = self.decl();
            self.section_variable_names.truncate(names_mark);
            return Ok(SurfaceDecl::Section {
                span: start_span,
                name: None,
                decls: vec![variable, body?],
                noncomputable: false,
            });
        }
        Ok(variable)
    }

    /// Parse the name list of `include x y …` / `omit x y …`.
    ///
    /// Lean 4 includes a section `variable` in a declaration only when the
    /// declaration mentions it; `include` forces inclusion for every following
    /// declaration in the scope, and `omit` cancels a preceding `include`.
    ///
    /// Only the NAME form is modelled. Lean's `omit` also accepts bracketed
    /// instance binders (`omit [Foo α]`), which select by TYPE rather than by
    /// name; that shape never reaches here — the dispatcher requires an
    /// identifier after the keyword, so `omit [Foo α]` falls through to the
    /// unknown-command arm and is refused BY NAME. A named refusal is the
    /// intended outcome for a form this parser cannot model: the alternative
    /// is guessing, which is the defect this whole change removes.
    ///
    /// The empty-list branch is unreachable through the dispatcher (its guard
    /// already saw an identifier); it is the fail-closed guard for anyone who
    /// loosens that guard later.
    pub(in crate::grammar) fn include_omit_names(
        &mut self,
        keyword: &str,
        keyword_col: u32,
    ) -> Result<Vec<SurfaceName>, ParseError> {
        let mut names = Vec::new();
        while let TokenKind::Ident(_) = self.current_kind() {
            // SAME LINE DISCIPLINE AS `variable`, AND FOR THE SAME MEASURED
            // REASON. Without this, `include h` followed by `omit h` on the
            // next line parsed as ONE command with names `["h", "omit", "h"]`
            // — the run walked straight through the line break, so the `omit`
            // was never a command and never cancelled anything (measured
            // 2026-08-25: shape C of the parser probe yielded
            // `[Variable, IncludeVars, Theorem]`, three decls where four were
            // written). In Lean `include`/`omit` are TOKENS, so an ident run
            // can never absorb one; Clean lexes them as plain identifiers, so
            // the stop has to be explicit.
            //
            // The rule is the column rule, not a newline rule: a name may sit
            // on a continuation line as long as it starts to the RIGHT of the
            // keyword. That is strictly more permissive than Lean, so it can
            // only accept inputs Lean accepts.
            let token = self.current();
            if token.preceded_by_newline && token.col <= keyword_col {
                break;
            }
            names.push(self.ident()?);
        }

        if names.is_empty() {
            return Err(ParseError::UnexpectedToken {
                line: self.current_line(),
                col: self.current_span().start,
                message: format!("expected at least one section-variable name after `{keyword}`"),
            });
        }

        Ok(names)
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
                    names.push(self.open_list_name()?);
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

        // Activate scoped custom notation for the opened namespaces (Lean
        // `elabOpen`: only the SIMPLE forms — `open Foo` / `open scoped Foo`
        // — activate scoped declarations; `(only)` / `hiding` / `renaming`
        // import names without activating). For `open … in`, the activation
        // is bounded to the body parsed below.
        let scoped_mark = self.open_scoped_notation_mark();
        for open_path in &paths {
            if open_path.names.is_empty()
                && open_path.hiding.is_empty()
                && open_path.renaming.is_empty()
            {
                self.activate_open_scoped_notation_path(&open_path.path);
            }
        }

        // Check for `in` followed by body
        let body = if self.eat(&TokenKind::In) {
            let inner = self.decl();
            // Truncate on the error path too, so a malformed body does not
            // leave the activation in force for the rest of the file.
            self.truncate_open_scoped_notation(scoped_mark);
            Some(Box::new(inner?))
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

    /// One name of an `open Ns (…)` / `export Ns (…)` list. Lean's grammar
    /// is `ident+`, and an `ident` may be dotted: `export M (Zed.x)` makes
    /// `Zed.x` name `M.Zed.x`. Reading only the first component stopped the
    /// list at the `.`, the whole command was dropped by error recovery, and
    /// the file went on with `Zed.x` read as a field of a root value `Zed`
    /// (measured 2026-09-26: `Zed.x = 5` accepted; Lean 4.8.0: 4).
    fn open_list_name(&mut self) -> Result<SurfaceName, ParseError> {
        if matches!(self.current_kind(), TokenKind::Ident(_)) {
            self.qualified_ident()
        } else {
            self.ident_like()
        }
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
            names.push(self.open_list_name()?);
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
}

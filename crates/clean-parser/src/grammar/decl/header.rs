// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The file header (plan item `formats-module-spelling-refusals`).
//!
//! Pinned Lean v4.30.0-rc2 reads a header before any command
//! (`Lean/Parser/Module/Syntax.lean`):
//!
//! ```text
//! header := "module"? "prelude"? import*
//! import := atomic("public"? "meta"? "import ") "all"? ident
//! ```
//!
//! and `Lean.Parser.parseHeader` then refuses, at the modifier's own token,
//! a `public`, `meta` or `all` import in a file with no `module` (one message
//! each, in that order), and `public import all` in a module. The header ends
//! at the first token that does not continue it; `private import` is
//! therefore not a header import but a `private` declaration modifier in front
//! of the `import` keyword, which `decl::module_spelling` refuses.
//!
//! Lean's whitespace is `--` and `/- … -/` comments only: a declaration doc
//! comment (`/-- … -/`) and a module doc (`/-! … -/`) are tokens
//! (`Lean.Parser.whitespace`), which no header rule takes, so the header ends
//! at either one. Clean's lexer skips both as trivia, so the header asks
//! [`Parser::doc_met_before`] before each token of an import: an import after
//! a doc comment is past the header. A `module` after one
//! ([`Parser::doc_before`]) is an identifier in command position, refused
//! here in Lean's words; when a declaration doc comment has another after it
//! (`/-- a -/ /-! b -/ module`), at the end of the first, naming the second.
//! Inside an import's `atomic` prefix (`public /-- d -/ import`) the group
//! fails at the doc comment, so the header ends before the prefix and
//! `decl::module_spelling` refuses it; after `import` or `all` (`import /-! d
//! -/ Init`) Lean's identifier parser meets it, and the file is refused here
//! with "unexpected token '/-!'; expected identifier", naming the first of two
//! doc comments in a row.
//!
//! Lean's header parser stops at its first error, and pinned v4.30.0-rc2
//! reads no command after a header error (`module` / `import all` /
//! `#eval 1 + 1` / `def x : Nat := "s"` prints only `2:10: error: unexpected
//! token '#eval'; expected identifier`). So the header ends at the first
//! import whose module name does not parse, which Clean recovers as a
//! `RawDecl` placeholder, and that recovery stays the file's first error: no
//! later spelling refuses the file (the imports after it are read past the
//! header), and no `parseHeader` modifier message on the imports before it is
//! returned (Lean logs those after the parse error).
//!
//! `all` is a token of the header's token table (`Module.updateTokens`), so an
//! unescaped `all` after `import` is the modifier whether the module name is
//! on its line or the next.
//!
//! The header has its own token table, so `module` is a keyword only as the
//! file's first token: everywhere else it is an ordinary identifier (`def
//! module (j : Json)`, a structure field `module : Module` — trust-ir
//! `TrustIrEval/Decode.lean`, `Run.lean`); Lean 4.8.0 has no `module` token at
//! all.

use super::super::Parser;
use super::doc_before::DocBefore;
use super::module_spelling::GuardedCommand;
use crate::lexer::TokenKind;
use crate::surface::*;
use crate::{FileHeader, ImportSpec, ParseError};

/// One header import with the positions its refusals are reported at.
struct HeaderImport {
    spec: ImportSpec,
    /// The `import` keyword's span, which the `SurfaceDecl::Import` carries.
    span: Span,
    public_token: Option<usize>,
    meta_token: Option<usize>,
    all_token: Option<usize>,
}

/// Which modifiers the import at the cursor carries, before any is consumed.
#[derive(Clone, Copy)]
struct ImportForm {
    public: bool,
    meta: bool,
}

impl Parser {
    /// Read only the file header; no term/tactic parser or environment is needed.
    pub fn parse_header(input: &str) -> Result<FileHeader, ParseError> {
        Self::new(input).file_header(&mut Vec::new())
    }

    /// Parse the file header, push each header import onto `decls` as the
    /// `SurfaceDecl::Import` node the elaborator reads, and return the header.
    ///
    /// # Errors
    ///
    /// [`ParseError::ModuleSyntaxRefused`] with Lean's first header message: a
    /// doc comment inside an import, else `parseHeader`'s first modifier
    /// message. An import whose module name does not parse otherwise is
    /// recovered as before, as a `RawDecl` placeholder; the header ends there,
    /// no modifier message is returned, and `header_recovered` keeps every
    /// later refusal from refusing the file.
    pub(in crate::grammar) fn file_header(
        &mut self,
        decls: &mut Vec<SurfaceDecl>,
    ) -> Result<FileHeader, ParseError> {
        let first_is_module = self.pos == 0 && self.at_unescaped_ident("module");
        // Behind a doc comment, `module` is an identifier where a command
        // belongs: the end of a module doc's command, or the declaration a
        // doc comment opens, which Lean refuses at the doc comment after it
        // when one follows (`/-- a -/ /-! b -/ module`: `1:8`).
        match self.doc_before(self.pos).filter(|_| first_is_module) {
            Some(DocBefore::Module) => {
                let token = self.current();
                return Err(ParseError::ModuleSyntaxRefused {
                    line: token.line as usize,
                    col: token.col as usize,
                    message: "unexpected identifier; expected command".to_owned(),
                });
            }
            Some(DocBefore::Declaration { .. } | DocBefore::Stacked { .. }) => {
                self.command_start = self.pos;
                return Err(self
                    .modifier_prefix_refusal(GuardedCommand::Identifier)
                    .unwrap_or_else(|| ParseError::ModuleSyntaxRefused {
                        line: self.current().line as usize,
                        col: self.current().col as usize,
                        message: "unexpected identifier".to_owned(),
                    }));
            }
            None => {}
        }
        let is_module = first_is_module;
        if is_module {
            self.advance();
            self.default_visibility = Visibility::Private;
        }
        let is_prelude = self.at_unescaped_ident("prelude") && self.doc_before(self.pos).is_none();
        if is_prelude {
            let span = self.current_span();
            self.advance();
            decls.push(SurfaceDecl::Prelude { span });
        }
        let mut imports = Vec::new();
        let mut recovered = false;
        while let Some(form) = self.header_import_form() {
            let span = self.current_span();
            match self.header_import(form, is_module) {
                Ok(import) => {
                    decls.push(SurfaceDecl::Import {
                        span: import.span,
                        paths: vec![import.spec.module.clone()],
                    });
                    imports.push(import);
                }
                // A doc comment inside the import, in Lean's words. Lean logs
                // the header's parse errors before `parseHeader`'s modifier
                // messages (measured: `public import Init` / `import /-- d -/
                // Init` prints `2:6` first, then `1:0`), so it is returned
                // before `header_refusal` looks at the imports read so far.
                Err(err) if err.refuses_file() => return Err(err),
                // Recovered as the file loop recovers a failed command. Lean's
                // header parser stops at its first error, so the header ends
                // here: `module` / `import all` / `import /-- d -/ Init` is
                // pinned v4.30.0-rc2's `2:10: error: unexpected token
                // 'import'; expected identifier`, never the second import's
                // `3:6` doc-comment refusal.
                Err(err) => {
                    decls.push(self.skip_to_next_decl_with_recovery("error-recovery", span, &err));
                    recovered = true;
                    break;
                }
            }
        }
        // Lean logs `parseHeader`'s modifier messages after the header's parse
        // error (measured: `public import Init` / `import all` / `def x : Nat
        // := 1` prints `2:10` first, then `1:0`), so after a recovery none is
        // the file's first message.
        self.header_recovered = recovered;
        if let Some(err) = imports
            .iter()
            .filter(|_| !recovered)
            .find_map(|import| self.header_refusal(is_module, import))
        {
            return Err(err);
        }
        Ok(FileHeader {
            is_prelude,
            is_module,
            imports: imports.into_iter().map(|import| import.spec).collect(),
        })
    }

    /// The module names one header line imports, and whether the line held
    /// nothing else. Lean's header refusals are not applied: a dependency
    /// scanner reads the imports Lean resolves, and Lean resolves them even
    /// in a header it reports errors on (`parseHeader` only adds messages).
    pub(crate) fn header_line_modules(line: &str) -> Result<(Vec<SurfaceName>, bool), ParseError> {
        let mut parser = Parser::new(line);
        let mut modules = Vec::new();
        while let Some(form) = parser.header_import_form() {
            modules.push(parser.header_import(form, false)?.spec.module);
        }
        let consumed = matches!(parser.current_kind(), TokenKind::Eof);
        Ok((modules, consumed))
    }

    /// Whether the current token is the identifier `text`, unescaped.
    fn at_unescaped_ident(&self, text: &str) -> bool {
        matches!(self.current_kind(), TokenKind::Ident(name) if name == text)
            && !self.current().ident_escaped
    }

    /// Whether the tokens at the cursor are `public`? `meta`? `import`, Lean's
    /// `atomic` prefix of a header import, with no doc comment before any of
    /// them ([`Parser::doc_met_before`]). A doc comment is a token to Lean, so
    /// the `atomic` group fails at one anywhere in the prefix and the header
    /// ends before its first token (measured on pinned v4.30.0-rc2: `module` /
    /// `public /-- d -/ import Init` is refused at `2:6`, the end of `public`,
    /// with "unexpected token '/--'"); `decl::module_spelling` then refuses
    /// the prefix past the header.
    fn header_import_form(&self) -> Option<ImportForm> {
        let mut offset = 0;
        let public = matches!(self.peek_kind(0), Some(TokenKind::Public));
        if public {
            offset += 1;
        }
        let meta = self.peek_token(offset).is_some_and(|token| {
            matches!(&token.kind, TokenKind::Ident(name) if name == "meta") && !token.ident_escaped
        });
        if meta {
            offset += 1;
        }
        let form = matches!(self.peek_kind(offset), Some(TokenKind::Import))
            .then_some(ImportForm { public, meta })?;
        (0..=offset)
            .all(|ahead| self.doc_met_before(self.pos + ahead).is_none())
            .then_some(form)
    }

    /// Consume one header import of shape `form`.
    fn header_import(
        &mut self,
        form: ImportForm,
        is_module: bool,
    ) -> Result<HeaderImport, ParseError> {
        let public_token = form.public.then_some(self.pos);
        if form.public {
            self.advance();
        }
        let meta_token = form.meta.then_some(self.pos);
        if form.meta {
            self.advance();
        }
        let span = self.current_span();
        self.advance();
        let (all_token, module) = self.header_import_target()?;
        Ok(HeaderImport {
            spec: ImportSpec {
                module,
                is_exported: form.public || !is_module,
                is_meta: form.meta,
                import_all: all_token.is_some(),
            },
            span,
            public_token,
            meta_token,
            all_token,
        })
    }

    /// What follows a header import's `import` keyword: `all`? and ONE module
    /// name (`optional all >> identWithPartialTrailingDot`), with the `all`
    /// token's index.
    ///
    /// `Module.updateTokens` adds the header's `all` (`def «all»`,
    /// `Lean/Parser/Module/Syntax.lean`) to the token table the header is
    /// read with, so an unescaped `all` is that token wherever the module name
    /// stands: `module` / `import all` / `  Init` is `import all Init`
    /// (pinned v4.30.0-rc2 exits 0), and an `all` with no module name after
    /// it is refused by Lean ("unexpected token 'def'; expected identifier";
    /// here the name fails to parse and is recovered as a `RawDecl`). `«all»`
    /// is an identifier, and so is `all.Foo`, which Lean's identifier scan
    /// reads whole (pinned v4.30.0-rc2: "unknown module prefix 'all'").
    ///
    /// Clean's lexer skips a doc comment as trivia, where Lean's identifier
    /// parser meets it as a token: one before `all` or the module name refuses
    /// the file in Lean's words ([`Parser::refuse_doc_in_import`]).
    fn header_import_target(&mut self) -> Result<(Option<usize>, SurfaceName), ParseError> {
        self.refuse_doc_in_import()?;
        let all_token = self.at_header_all().then_some(self.pos);
        if all_token.is_some() {
            self.advance();
            self.refuse_doc_in_import()?;
        }
        Ok((all_token, self.module_path()?))
    }

    /// Whether the token at the cursor is the header's `all` token: an
    /// unescaped `all` not glued by a `.` to a following name part.
    fn at_header_all(&self) -> bool {
        let end = self.current().span.end;
        self.at_unescaped_ident("all")
            && !self
                .peek_token(1)
                .is_some_and(|next| matches!(next.kind, TokenKind::Dot) && next.span.start == end)
    }

    /// Lean's refusal of a doc comment ending immediately before the token at
    /// the cursor inside a header import, where its identifier parser stands:
    /// "unexpected token '/--'; expected identifier" (or `'/-!'`), at the end
    /// of the token before it (measured on pinned v4.30.0-rc2: `module` /
    /// `import /-! d -/ Init` at `2:6`, `import all /-- d -/ Init` at `2:10`).
    /// Of two in a row it names the first, where Lean stops (`import /-- a -/
    /// /-! b -/ Init`: `'/--'`).
    fn refuse_doc_in_import(&self) -> Result<(), ParseError> {
        let Some(doc) = self.doc_met_before(self.pos) else {
            return Ok(());
        };
        let (line, col) = self
            .pos
            .checked_sub(1)
            .and_then(|before| self.token_end_position(before))
            .unwrap_or_else(|| (self.current().line as usize, self.current().col as usize));
        Err(ParseError::ModuleSyntaxRefused {
            line,
            col,
            message: format!(
                "unexpected token '{}'; expected identifier",
                doc.lean_token()
            ),
        })
    }

    /// What follows an `import` keyword PAST the header (`import_decl`, which
    /// Lean refuses there: "invalid 'import' command, it must be used in the
    /// beginning of the file"): `all`? and ONE module name, with the `all`
    /// token's index. The header's own rule is
    /// [`Parser::header_import_target`].
    ///
    /// Past the header `all` is not a token, so it is the modifier only when
    /// another identifier follows it on the same line. ONE module per
    /// `import`, here as in the header (Lean 4.8.0's `import := "import "
    /// "runtime"? ident`): a second module on the same line is not part of
    /// the import. Lean reports "unexpected identifier; expected
    /// command" there and imports only the first (measured: with `Q: instance
    /// i2 : C := ⟨2⟩` and `P: instance i3 : C := ⟨3⟩`, `import Q P`
    /// elaborates `C.v` to 2). Clean used to import both — a file Lean
    /// rejects was credited, and with a value Lean never computes. What
    /// follows is left to the declaration parser, which refuses it the same
    /// way.
    pub(in crate::grammar) fn import_target(
        &mut self,
    ) -> Result<(Option<usize>, SurfaceName), ParseError> {
        let all_token = (!self.current().ident_escaped
            && matches!(self.current_kind(), TokenKind::Ident(name) if name == "all")
            && matches!(self.peek_kind(1), Some(TokenKind::Ident(_)))
            && self
                .tokens
                .get(self.pos + 1)
                .is_some_and(|next| next.line == self.current().line))
        .then_some(self.pos);
        if all_token.is_some() {
            self.advance();
        }
        Ok((all_token, self.module_path()?))
    }

    /// Lean's first `parseHeader` message on `import`, at the modifier's token.
    fn header_refusal(&self, is_module: bool, import: &HeaderImport) -> Option<ParseError> {
        let (token, message) = if !is_module {
            if let Some(token) = import.public_token {
                (
                    token,
                    "cannot use `public import` without `module`".to_owned(),
                )
            } else if let Some(token) = import.meta_token {
                (
                    token,
                    "cannot use `meta import` without `module`".to_owned(),
                )
            } else {
                let token = import.all_token?;
                (token, "cannot use `import all` without `module`".to_owned())
            }
        } else {
            import.public_token?;
            let token = import.all_token?;
            let module = &import.spec.module;
            (
                token,
                format!(
                    "cannot use `all` with `public import`; consider using separate \
                     `public import {module}` and `import all {module}` directives in order \
                     to import public data into the public scope and private data into the \
                     private scope."
                ),
            )
        };
        let token = self.tokens.get(token)?;
        Some(ParseError::ModuleSyntaxRefused {
            line: token.line as usize,
            col: token.col as usize,
            message,
        })
    }
}

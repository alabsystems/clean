// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_kernel::Name;

use super::Parser;
use crate::imported_term_prefixes::NUMERAL_PREFIX_PRECEDENCE;
use crate::lexer::TokenKind;
use crate::{ParseError, SurfaceArg, SurfaceExpr, SurfaceLit, SurfaceName};

/// Lean's application argument seat starts above the supported leading parser.
pub(super) const APPLICATION_ARGUMENT_PRECEDENCE: u32 = 1023;

impl Parser {
    pub(super) fn imported_term_prefix_kind(&self) -> Option<&Name> {
        if self.imported_term_prefixes.is_empty() {
            return None;
        }
        let stem = self.current();
        let TokenKind::Ident(text) = &stem.kind else {
            return None;
        };
        let suffix = self.tokens.get(self.pos + 1)?;
        if stem.ident_escaped
            || stem.lean_keyword
            || !matches!(suffix.kind, TokenKind::Percent)
            || stem.span.end != suffix.span.start
        {
            return None;
        }
        self.imported_term_prefixes.kind(text)
    }

    pub(super) fn parse_imported_term_prefix(
        &mut self,
        minimum_precedence: u32,
    ) -> Result<Option<SurfaceExpr>, ParseError> {
        let Some(kind) = self.imported_term_prefix_kind().cloned() else {
            return Ok(None);
        };
        if minimum_precedence > NUMERAL_PREFIX_PRECEDENCE {
            return Err(self.imported_prefix_error(format!(
                "imported term prefix cannot start a term at precedence {minimum_precedence}; parenthesize it"
            )));
        }
        let head = self.current_span().merge(self.tokens[self.pos + 1].span);
        self.advance();
        self.advance();
        let numeral_span = self.current_span();
        let numeral = match self.current_kind() {
            TokenKind::NatLit(numeral) if self.doc_met_before(self.pos).is_none() => {
                numeral.clone()
            }
            _ => {
                return Err(self
                    .imported_prefix_error("expected a numeral after imported term prefix".into()))
            }
        };
        self.advance();
        let arg = SurfaceExpr::Lit(numeral_span, SurfaceLit::nat(numeral));
        Ok(Some(SurfaceExpr::App(
            head.merge(numeral_span),
            Box::new(SurfaceExpr::Ident(
                head,
                SurfaceName::for_imported_term_kind(kind),
            )),
            vec![SurfaceArg::positional(arg)],
        )))
    }

    pub(super) fn imported_prefix_error(&self, message: String) -> ParseError {
        ParseError::UnexpectedToken {
            line: self.current_line(),
            col: self.current().col as usize,
            message,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        parse_file_seeded_in_world_with_imported_terms, ImportedTermPrefixError,
        ImportedTermPrefixes, LeanWorld, NotationSeed, SurfaceDecl, TacticPatterns,
    };

    fn registered() -> (Name, ImportedTermPrefixes) {
        let kind = Name::anon().str("Namespace.part").num(7).str("kind");
        let mut prefixes = ImportedTermPrefixes::default();
        prefixes
            .register_numeral_prefix(kind.clone(), 1022, "chosen% ")
            .expect("supported descriptor");
        (kind, prefixes)
    }

    #[test]
    fn imported_prefix_retains_kind_and_numeral_span() {
        let (kind, prefixes) = registered();
        let source = "def result := chosen% 0x11\n";
        let parsed = parse_file_seeded_in_world_with_imported_terms(
            source,
            &TacticPatterns::new(),
            &NotationSeed::default(),
            LeanWorld::Lean436,
            &prefixes,
        )
        .expect("parsed file");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let [SurfaceDecl::Def { val, .. }] = parsed.decls.as_slice() else {
            panic!("expected a definition");
        };
        assert!(is_invocation(val, &kind));
        let SurfaceExpr::App(span, head, args) = val.as_ref() else {
            panic!("expected the imported invocation");
        };
        assert_eq!(&source[span.start..span.end], "chosen% 0x11");
        let head_span = head.span();
        assert_eq!(&source[head_span.start..head_span.end], "chosen%");
        let [arg] = args.as_slice() else {
            panic!("expected one numeral");
        };
        assert!(matches!(arg.expr, SurfaceExpr::Lit(_, SurfaceLit::Nat(17))));
        assert_eq!(&source[arg.span.start..arg.span.end], "0x11");
        assert_eq!(SurfaceName::from_name(kind).imported_term_kind(), None);
    }

    fn is_invocation(expr: &SurfaceExpr, kind: &Name) -> bool {
        matches!(
            expr,
            SurfaceExpr::App(_, head, _)
                if matches!(head.as_ref(), SurfaceExpr::Ident(_, name)
                    if name.imported_term_kind() == Some(kind))
        )
    }

    #[test]
    fn imported_prefix_keeps_exact_token_and_application_boundaries() {
        let (kind, prefixes) = registered();
        let parse = |source: &str| {
            let mut parser = Parser::new(source);
            parser.imported_term_prefixes.clone_from(&prefixes);
            let term = parser.expr()?;
            assert!(matches!(parser.current_kind(), TokenKind::Eof));
            Ok::<_, ParseError>(term)
        };
        assert!(!is_invocation(&parse("chosen % 17").unwrap(), &kind));
        assert!(!is_invocation(&parse("longchosen%17").unwrap(), &kind));
        assert!(!is_invocation(&parse("«chosen»%17").unwrap(), &kind));
        assert!(is_invocation(&parse("chosen%17").unwrap(), &kind));
        assert!(parse("chosen% missing")
            .unwrap_err()
            .to_string()
            .contains("numeral"));
        assert!(parse("f chosen% 17")
            .unwrap_err()
            .to_string()
            .contains("precedence 1023"));
        assert!(parse("f (chosen% 17)").is_ok());
        assert!(parse("1 + chosen% 17").is_ok());
    }

    #[test]
    fn unsupported_and_competing_prefix_descriptors_are_refused() {
        let (kind, mut prefixes) = registered();
        assert_eq!(
            prefixes.register_numeral_prefix(kind.clone(), 1022, "chosen%"),
            Ok(())
        );
        assert!(matches!(
            prefixes.register_numeral_prefix(Name::anon().str("other"), 1022, "chosen%"),
            Err(ImportedTermPrefixError::Ambiguous(_))
        ));
        assert!(matches!(
            prefixes.register_numeral_prefix(kind.clone(), 1024, "other%"),
            Err(ImportedTermPrefixError::UnsupportedPrecedence(1024))
        ));
        assert!(matches!(
            prefixes.register_numeral_prefix(kind, 1022, "other %"),
            Err(ImportedTermPrefixError::UnsupportedLiteral(_))
        ));
    }
}

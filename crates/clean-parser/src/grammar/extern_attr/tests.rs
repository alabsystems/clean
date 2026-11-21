// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::SurfaceDecl;

fn metadata(source: &str) -> CompilerExternMetadata {
    let declaration = Parser::parse_decl_exact(source).expect("the full declaration parses");
    let SurfaceDecl::Axiom { attrs, .. } = declaration else {
        panic!("axiom fixture")
    };
    let [Attribute::ExternMetadata(metadata)] = attrs.as_slice() else {
        panic!("typed extern attribute: {attrs:?}")
    };
    metadata.clone()
}

#[test]
fn standard_entries_keep_order_backend_and_conflicting_symbols() {
    let actual = metadata("@[extern llvm \"same\" c \"other\" all \"conflict\"] axiom f : Nat");
    assert_eq!(
        actual,
        CompilerExternMetadata::Complete(CompilerExternDescriptor {
            arity: CompilerExternArity::Unspecified,
            entries: vec![
                CompilerExternEntry::Standard {
                    backend: Name::from_string("llvm"),
                    symbol: "same".into()
                },
                CompilerExternEntry::Standard {
                    backend: Name::from_string("c"),
                    symbol: "other".into()
                },
                CompilerExternEntry::Standard {
                    backend: Name::from_string("all"),
                    symbol: "conflict".into()
                },
            ],
        })
    );
}

#[test]
fn bare_source_symbol_has_only_the_grammar_default_backend() {
    let actual = metadata("@[extern \"symbol\"] axiom unrelatedSourceName : Nat");
    assert_eq!(
        actual,
        CompilerExternMetadata::Complete(CompilerExternDescriptor {
            arity: CompilerExternArity::Unspecified,
            entries: vec![CompilerExternEntry::Standard {
                backend: Name::from_string("all"),
                symbol: "symbol".into()
            }],
        })
    );
    assert!(matches!(
        metadata("@[extern] axiom f : Nat"),
        CompilerExternMetadata::Incomplete {
            reason: CompilerExternIncomplete::UnspecifiedSourceBinding,
            ..
        }
    ));
}

#[test]
fn unrepresented_or_trailing_extern_syntax_never_disappears() {
    for source in [
        "@[extern c] axiom f : Nat",
        "@[extern \"valid\" llvm] axiom f : Nat",
        "@[extern inline \"#1\"] axiom f : Nat",
        "@[extern 1 \"symbol\"] axiom f : Nat",
        "@[extern \"\"] axiom f : Nat",
    ] {
        assert!(
            Parser::parse_decl_exact(source).is_err(),
            "unrepresented source accepted: {source}"
        );
    }
}

#[test]
fn borrowed_type_application_stops_before_the_arrow_codomain() {
    let expression = Parser::parse_expr("@& Array Nat → Nat").expect("borrowed application domain");
    let crate::SurfaceExpr::Arrow(_, domain, result) = expression else {
        panic!("arrow")
    };
    assert!(
        matches!(domain.as_ref(), crate::SurfaceExpr::Borrowed(_, inner)
        if matches!(inner.as_ref(), crate::SurfaceExpr::App(_, _, args) if args.len() == 1))
    );
    assert!(
        matches!(result.as_ref(), crate::SurfaceExpr::Ident(_, n) if n.name() == &Name::from_string("Nat"))
    );
    assert!(Parser::parse_expr("@&").is_err());
}

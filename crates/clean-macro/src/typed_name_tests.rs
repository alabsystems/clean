// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::{HygieneState, MacroDef, SourceInfo, SurfaceName, Syntax, SyntaxKind, SyntaxQuote};
use clean_kernel::Name;
use clean_parser::NameComponentSyntax;
use std::collections::HashMap;

#[test]
fn typed_identifier_transport_preserves_components_origins_and_span() {
    let source = SurfaceName::component("A.B", true)
        .append(&SurfaceName::component("7", true))
        .append(&SurfaceName::from_name(Name::anon().num(7)));
    let info = SourceInfo::new(11, 29);
    let syntax = Syntax::ident_with_info(info.clone(), &source);
    assert!(syntax.as_ident().unwrap().same_syntax(&source));
    assert_eq!(syntax.source_info(), &info);
    assert_eq!(
        source.component_syntax(),
        &[
            NameComponentSyntax::Escaped,
            NameComponentSyntax::Escaped,
            NameComponentSyntax::Generated,
        ]
    );
    assert!(syntax
        .map(&Clone::clone)
        .as_ident()
        .unwrap()
        .same_syntax(&source));
    assert!(syntax.as_ident_tag().is_none());
}

#[test]
fn identifier_patterns_and_antiquotation_keys_do_not_join_equal_display_names() {
    for (left, right) in [
        (
            SurfaceName::component("A.B", true),
            SurfaceName::generated_path("A.B"),
        ),
        (
            SurfaceName::component("7", true),
            SurfaceName::from_name(Name::anon().num(7)),
        ),
    ] {
        assert_eq!(
            left.to_string(),
            right.to_string(),
            "close display collision control"
        );
        let def = MacroDef::new(
            "typed identity control",
            SyntaxKind::term(),
            Syntax::ident(&left),
            SyntaxQuote::term(Syntax::generated_ident("ok")),
        );
        assert!(def.try_match(&Syntax::ident(&left)).is_some());
        assert!(def.try_match(&Syntax::ident(&right)).is_none());
        let quote = SyntaxQuote::term(Syntax::mk_app(
            Syntax::generated_ident("pair"),
            vec![Syntax::mk_antiquot(&left), Syntax::mk_antiquot(&right)],
        ));
        let bindings = HashMap::from([
            (left.clone(), Syntax::ident(&left)),
            (right.clone(), Syntax::ident(&right)),
        ]);
        assert_eq!(bindings.len(), 2);
        let expanded = quote.substitute(&bindings);
        assert!(expanded
            .child(1)
            .unwrap()
            .as_ident()
            .unwrap()
            .same_syntax(&left));
        assert!(expanded
            .child(2)
            .unwrap()
            .as_ident()
            .unwrap()
            .same_syntax(&right));
    }
}

#[test]
fn quotation_lexer_preserves_escaped_dots_spaces_keywords_and_antiquotations() {
    for spelling in ["«A.B»", "A.B", "«7»", "«λ 星»", "«Type»", "«x:y»"] {
        let expected = clean_parser::parse_name(spelling).unwrap();
        let syntax = crate::quotation::parse_quotation(&format!("`({spelling})"))
            .unwrap()
            .syntax;
        assert!(
            syntax.as_ident().unwrap().same_syntax(&expected),
            "{spelling}"
        );
        let anti = crate::quotation::parse_quotation(&format!("`(${spelling})")).unwrap();
        assert!(
            anti.antiquot_names()[0].same_syntax(&expected),
            "{spelling}"
        );
    }
    let pair = crate::quotation::parse_quotation("`(f «a b» A.B)").unwrap();
    assert_eq!(pair.syntax.children().len(), 3);
    assert!(pair
        .syntax
        .child(1)
        .unwrap()
        .as_ident()
        .unwrap()
        .same_syntax(&SurfaceName::component("a b", true)));
    for bad in ["`(«unclosed)", "`($x:)", "`($[x]*junk)", "`($x..y)"] {
        assert!(crate::quotation::parse_quotation(bad).is_err(), "{bad}");
    }
}

#[test]
fn quotation_category_delimiter_preserves_custom_identity_and_body_names() {
    for (category, identity) in [
        ("attr", Name::anon().str("attr")),
        ("widget", Name::anon().str("widget")),
        ("«my.cat»", Name::anon().str("my.cat")),
        ("«a|b»", Name::anon().str("a|b")),
    ] {
        let quote =
            crate::quotation::parse_quotation(&format!("`({category}| «body|name»)")).unwrap();
        assert_eq!(quote.category.name(), &identity);
        assert!(quote
            .syntax
            .as_ident()
            .unwrap()
            .same_syntax(&SurfaceName::component("body|name", true)));
    }
    let quoted = crate::quotation::parse_quotation("`(«attr|body»)").unwrap();
    assert_eq!(quoted.category, SyntaxKind::term());
    assert_eq!(
        quoted.syntax.as_ident().unwrap().name(),
        &Name::anon().str("attr|body")
    );
    for malformed in [
        "`(attr||body)",
        "`(attr| x|y)",
        "`(my.cat| x)",
        "`(«unclosed| x)",
    ] {
        assert!(
            crate::quotation::parse_quotation(malformed).is_err(),
            "{malformed}"
        );
    }
}

#[test]
fn hygiene_preserves_typed_base_and_cannot_capture_source_scope_spelling() {
    let base = SurfaceName::component("A.B", true);
    let same_display = SurfaceName::generated_path("A.B");
    let key = SurfaceName::component("arg", false);
    let template = SyntaxQuote::term(Syntax::mk_let(
        Syntax::ident(&base),
        None,
        Syntax::mk_num(1),
        Syntax::mk_app(
            Syntax::generated_ident("pair"),
            vec![
                Syntax::ident(&base),
                Syntax::ident(&same_display),
                Syntax::mk_antiquot(&key),
            ],
        ),
    ));
    let mut state = HygieneState::new();
    let scope = state.push_scope();
    let renamed = base.append(&SurfaceName::from_name(
        Name::anon().str("_macro_binder").num(scope.0),
    ));
    // Every part of this adversarial caller name is a Str, even the digits.
    let caller = base
        .append(&SurfaceName::component("_macro_binder", true))
        .append(&SurfaceName::component(scope.0.to_string(), true));
    assert_ne!(renamed, caller);
    let expanded =
        template.substitute_hygienic(&HashMap::from([(key, Syntax::ident(&caller))]), &mut state);
    assert!(expanded
        .child(0)
        .unwrap()
        .as_ident()
        .unwrap()
        .same_syntax(&renamed));
    let body = expanded.child(2).unwrap();
    assert!(body
        .child(1)
        .unwrap()
        .as_ident()
        .unwrap()
        .same_syntax(&renamed));
    assert!(body
        .child(2)
        .unwrap()
        .as_ident()
        .unwrap()
        .same_syntax(&same_display));
    assert!(body
        .child(3)
        .unwrap()
        .as_ident()
        .unwrap()
        .same_syntax(&caller));
}

#[test]
fn quoted_wildcard_uses_plain_token_without_weakening_identifier_parser() {
    assert!(clean_parser::parse_name("_").is_err());
    for source in ["`_", "`(_)", "`(attr| _)", "`(widget| _)"] {
        let quote = crate::quotation::parse_quotation(source).unwrap();
        assert!(
            quote
                .syntax
                .as_ident()
                .unwrap()
                .same_syntax(&SurfaceName::component("_", false)),
            "{source}"
        );
    }
    for source in ["`«_»", "`(«_»)", "`(attr| «_»)", "`(widget| «_»)"] {
        let quote = crate::quotation::parse_quotation(source).unwrap();
        let name = quote.syntax.as_ident().unwrap();
        assert!(
            name.same_syntax(&SurfaceName::component("_", true)),
            "{source}"
        );
        assert!(!name.is_unescaped_component("_"));
    }
    assert!(crate::quotation::parse_quotation("`(attr| _|tail)").is_err());
}

#[test]
fn syntax_protocol_tags_do_not_accept_source_identifiers_or_qualified_aliases() {
    assert_eq!(Syntax::generated_ident("Type").as_ident_tag(), Some("Type"));
    for name in [
        SurfaceName::component("Type", true),
        SurfaceName::component("Type", false),
        SurfaceName::generated_path("A.Type"),
        SurfaceName::from_name(Name::anon().num(0)),
    ] {
        assert!(Syntax::ident(&name).as_ident_tag().is_none());
    }
}

#[test]
fn escaped_category_names_do_not_bypass_typed_antiquotation_shape() {
    let variable = SurfaceName::component("x", false);
    for escaped in [false, true] {
        let category = SurfaceName::component("ident", escaped);
        let pattern = Syntax::mk_antiquot_typed(&variable, &category);
        let def = MacroDef::new(
            "category",
            SyntaxKind::term(),
            pattern,
            SyntaxQuote::term(Syntax::mk_antiquot(&variable)),
        );
        assert!(def.try_match(&Syntax::generated_ident("name")).is_some());
        assert!(def.try_match(&Syntax::mk_num(7)).is_none());
        let quoted = crate::quotation::parse_quotation(if escaped {
            "`($x:«ident»)"
        } else {
            "`($x:ident)"
        })
        .unwrap();
        let source_rule = MacroDef::new(
            "source category",
            SyntaxKind::term(),
            quoted.syntax,
            SyntaxQuote::term(Syntax::mk_antiquot(&variable)),
        );
        assert!(source_rule
            .try_match(&Syntax::generated_ident("name"))
            .is_some());
        assert!(source_rule.try_match(&Syntax::mk_num(7)).is_none());
    }
}

#[test]
fn contextual_identifier_patterns_reject_escaped_keyword_and_relative_mutants() {
    let rule = |name: &SurfaceName| {
        MacroDef::new(
            "contextual",
            SyntaxKind::term(),
            Syntax::ident(name),
            SyntaxQuote::term(Syntax::mk_num(0)),
        )
    };
    for keyword in [
        "Type",
        "Prop",
        "Sort",
        "_",
        "sorry",
        "admit",
        "bif",
        "↑",
        "outParam",
        "semiOutParam",
        "Q",
        "q",
        "calc",
        "letI",
        "haveI",
        "·",
        "max",
        "imax",
    ] {
        let plain = SurfaceName::component(keyword, false);
        let escaped = SurfaceName::component(keyword, true);
        assert_eq!(plain, escaped);
        assert!(rule(&plain).try_match(&Syntax::ident(&plain)).is_some());
        assert!(rule(&plain).try_match(&Syntax::ident(&escaped)).is_none());
    }
    let ordinary = SurfaceName::component("x", false);
    assert!(rule(&ordinary)
        .try_match(&Syntax::ident(&SurfaceName::component("x", true)))
        .is_some());
    let ctor = SurfaceName::component("Ctor", false);
    let relative = ctor.clone().with_relative_constructor();
    assert_eq!(ctor, relative);
    assert!(Syntax::ident(&relative)
        .as_ident()
        .unwrap()
        .same_syntax(&relative));
    assert!(rule(&ctor).try_match(&Syntax::ident(&relative)).is_none());
    let rooted = SurfaceName::component("_root_", false).append(&ctor);
    let namespace = SurfaceName::component("_root_", true).append(&ctor);
    assert_eq!(rooted, namespace);
    assert!(rule(&rooted).try_match(&Syntax::ident(&rooted)).is_some());
    assert!(rule(&rooted)
        .try_match(&Syntax::ident(&namespace))
        .is_none());
}

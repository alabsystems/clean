// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_elab::ElabCtx;
use clean_kernel::Environment;
use clean_parser::parse_file_with_diagnostics;

#[test]
fn namespaces_keep_their_declared_syntax_rules_and_priorities() {
    let source = r#"
namespace Scope
syntax:51 (name := Nested.measured) (priority := default+1) "scopeMarker" : term
end Scope
namespace Other
syntax (name := Nested.measured) "otherMarker" : term
syntax (name := wide) (priority := 4000000000) "wideMarker" : term
end Other
"#;
    let input = parse_file_with_diagnostics(source).unwrap();
    assert!(input.diagnostics.is_empty(), "{:?}", input.diagnostics);
    let env = Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);
    for decl in &input.decls {
        ctx.elab_decl(decl).unwrap();
    }
    let rules = ctx.macro_ctx().registry();
    for (name, token, priority) in [
        ("Scope.Nested.measured", "scopeMarker", 1001_i64),
        ("Other.Nested.measured", "otherMarker", 1000),
        ("Other.wide", "wideMarker", 4000000000),
    ] {
        let rule = rules.get_by_name(name).unwrap();
        assert_eq!(rule.pattern.as_atom(), Some(token));
        assert_eq!(rule.priority, priority.into());
    }
    assert!(rules.get_by_name("Nested.measured").is_none());
}

#[test]
fn registering_the_lower_priority_last_preserves_the_winner_above_two_to_128() {
    let source = r#"
namespace Ranked
syntax (name := highRule) (priority := 340282366920938463463374607431768211457) "priorityProbe" : term
syntax (name := lowRule) (priority := 340282366920938463463374607431768211456) "priorityProbe" : term
end Ranked
"#;
    let parsed = parse_file_with_diagnostics(source).unwrap();
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let env = Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);
    for decl in &parsed.decls {
        ctx.elab_decl(decl).unwrap();
    }
    let registry = ctx.macro_ctx().registry();
    let high = registry.get_by_name("Ranked.highRule").unwrap();
    let low = registry.get_by_name("Ranked.lowRule").unwrap();
    assert_eq!(
        high.priority.to_string(),
        "340282366920938463463374607431768211457"
    );
    assert_eq!(
        low.priority.to_string(),
        "340282366920938463463374607431768211456"
    );
    assert_eq!(registry.get_by_kind(&high.kind)[0].name, "Ranked.highRule");
}

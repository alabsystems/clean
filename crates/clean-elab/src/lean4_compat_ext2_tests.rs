// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the extended Lean 4 compatibility layer.

use crate::lean4_compat_ext::Lean4Version;
use crate::lean4_compat_ext2::*;

// ── DoForm classification ───────────────────────────────────────────────────

#[test]
fn test_classify_do_form_let_returns_let_assign() {
    let form = classify_do_form("let").expect("should classify let");
    assert!(matches!(form, DoForm::LetAssign { .. }));
}

#[test]
fn test_classify_do_form_return_returns_return() {
    let form = classify_do_form("return").expect("should classify return");
    assert!(matches!(form, DoForm::Return { .. }));
}

#[test]
fn test_classify_do_form_if_returns_if_then_else() {
    assert_eq!(classify_do_form("if"), Some(DoForm::IfThenElse));
}

#[test]
fn test_classify_do_form_for_returns_for_in() {
    assert_eq!(classify_do_form("for"), Some(DoForm::ForIn));
}

#[test]
fn test_classify_do_form_try_returns_try_catch() {
    assert_eq!(classify_do_form("try"), Some(DoForm::TryCatch));
}

#[test]
fn test_classify_do_form_unless_returns_unless() {
    assert_eq!(classify_do_form("unless"), Some(DoForm::Unless));
}

#[test]
fn test_classify_do_form_unknown_returns_none() {
    assert_eq!(classify_do_form("match"), None);
    assert_eq!(classify_do_form(""), None);
}

// ── Attribute parsing ───────────────────────────────────────────────────────

#[test]
fn test_parse_attribute_simp() {
    assert_eq!(parse_attribute("simp").unwrap(), Lean4Attribute::Simp);
}

#[test]
fn test_parse_attribute_inline() {
    assert_eq!(parse_attribute("inline").unwrap(), Lean4Attribute::Inline);
}

#[test]
fn test_parse_attribute_reducible() {
    assert_eq!(
        parse_attribute("reducible").unwrap(),
        Lean4Attribute::Reducible
    );
}

#[test]
fn test_parse_attribute_irreducible() {
    assert_eq!(
        parse_attribute("irreducible").unwrap(),
        Lean4Attribute::Irreducible
    );
}

#[test]
fn test_parse_attribute_instance_no_priority() {
    assert_eq!(
        parse_attribute("instance").unwrap(),
        Lean4Attribute::Instance { priority: None }
    );
}

#[test]
fn test_parse_attribute_instance_with_priority() {
    assert_eq!(
        parse_attribute("instance 500").unwrap(),
        Lean4Attribute::Instance {
            priority: Some(500)
        }
    );
}

#[test]
fn test_parse_attribute_default_instance() {
    assert_eq!(
        parse_attribute("default_instance").unwrap(),
        Lean4Attribute::DefaultInstance { priority: None }
    );
}

#[test]
fn test_parse_attribute_implemented_by() {
    let attr = parse_attribute("implemented_by myImpl").unwrap();
    assert_eq!(
        attr,
        Lean4Attribute::ImplementedBy {
            impl_name: "myImpl".to_owned()
        }
    );
}

#[test]
fn test_parse_attribute_export() {
    let attr = parse_attribute("export lean_mk_nat").unwrap();
    assert_eq!(
        attr,
        Lean4Attribute::Export {
            name: "lean_mk_nat".to_owned()
        }
    );
}

#[test]
fn test_parse_attribute_extern_no_name() {
    assert_eq!(
        parse_attribute("extern").unwrap(),
        Lean4Attribute::Extern { name: None }
    );
}

#[test]
fn test_parse_attribute_extern_with_name() {
    let attr = parse_attribute("extern \"lean_io_prim\"").unwrap();
    assert_eq!(
        attr,
        Lean4Attribute::Extern {
            name: Some("lean_io_prim".to_owned())
        }
    );
}

#[test]
fn test_parse_attribute_deprecated_no_msg() {
    assert_eq!(
        parse_attribute("deprecated").unwrap(),
        Lean4Attribute::Deprecated { msg: None }
    );
}

#[test]
fn test_parse_attribute_coe() {
    assert_eq!(parse_attribute("coe").unwrap(), Lean4Attribute::Coe);
}

#[test]
fn test_parse_attribute_match_pattern() {
    assert_eq!(
        parse_attribute("match_pattern").unwrap(),
        Lean4Attribute::MatchPattern
    );
}

#[test]
fn test_parse_attribute_unknown_returns_error() {
    let err = parse_attribute("nonexistent_attr").unwrap_err();
    let msg = err.to_string();
    assert!(
        msg.contains("nonexistent_attr"),
        "error should mention the attribute name"
    );
}

#[test]
fn test_parse_attribute_all_simple_variants() {
    for (input, expected) in [
        ("simp", Lean4Attribute::Simp),
        ("always_inline", Lean4Attribute::AlwaysInline),
        ("noinline", Lean4Attribute::Noinline),
        ("semireducible", Lean4Attribute::Semireducible),
        ("class", Lean4Attribute::Class),
        ("csimp", Lean4Attribute::Csimp),
        ("congr", Lean4Attribute::Congr),
        ("ext", Lean4Attribute::Ext),
        ("refl", Lean4Attribute::Refl),
        ("symm", Lean4Attribute::Symm),
        ("macro_inline", Lean4Attribute::MacroInline),
        ("inline_if_reduce", Lean4Attribute::InlineIfReduce),
        ("specialize", Lean4Attribute::Specialize),
        ("nospecialize", Lean4Attribute::Nospecialize),
        ("init", Lean4Attribute::Init),
    ] {
        assert_eq!(
            parse_attribute(input).unwrap(),
            expected,
            "failed for {input}"
        );
    }
}

// ── Option handling ─────────────────────────────────────────────────────────

#[test]
fn test_parse_option_value_bool_true() {
    assert_eq!(
        parse_option_value("pp.all", "true").unwrap(),
        OptionValue::Bool(true)
    );
}

#[test]
fn test_parse_option_value_bool_false() {
    assert_eq!(
        parse_option_value("pp.notation", "false").unwrap(),
        OptionValue::Bool(false)
    );
}

#[test]
fn test_parse_option_value_nat() {
    assert_eq!(
        parse_option_value("maxRecDepth", "1000").unwrap(),
        OptionValue::Nat(1000)
    );
}

#[test]
fn test_parse_option_value_unknown_option_returns_string() {
    assert_eq!(
        parse_option_value("custom.option", "hello").unwrap(),
        OptionValue::String("hello".to_owned())
    );
}

#[test]
fn test_parse_option_value_bool_invalid_returns_error() {
    let err = parse_option_value("pp.all", "42").unwrap_err();
    assert!(err.to_string().contains("Bool"));
}

#[test]
fn test_parse_option_value_nat_invalid_returns_error() {
    let err = parse_option_value("maxRecDepth", "abc").unwrap_err();
    assert!(err.to_string().contains("Nat"));
}

#[test]
fn test_known_option_type_returns_correct_type() {
    assert_eq!(known_option_type("pp.all"), Some("Bool"));
    assert_eq!(known_option_type("maxHeartbeats"), Some("Nat"));
    assert_eq!(known_option_type("unknown.opt"), None);
}

#[test]
fn test_option_value_display() {
    assert_eq!(OptionValue::Bool(true).to_string(), "true");
    assert_eq!(OptionValue::Nat(42).to_string(), "42");
    assert_eq!(OptionValue::String("hi".to_owned()).to_string(), "\"hi\"");
}

// ── Auto-bound implicit ────────────────────────────────────────────────────

#[test]
fn test_auto_bound_mode_explicit() {
    assert_eq!(
        auto_bound_mode_from_brackets('(', ')'),
        Some(AutoBoundMode::Explicit)
    );
}

#[test]
fn test_auto_bound_mode_implicit() {
    assert_eq!(
        auto_bound_mode_from_brackets('{', '}'),
        Some(AutoBoundMode::Implicit)
    );
}

#[test]
fn test_auto_bound_mode_instance() {
    assert_eq!(
        auto_bound_mode_from_brackets('[', ']'),
        Some(AutoBoundMode::Instance)
    );
}

#[test]
fn test_auto_bound_mode_unknown_returns_none() {
    assert_eq!(auto_bound_mode_from_brackets('<', '>'), None);
}

// ── Universe inference ──────────────────────────────────────────────────────

#[test]
fn test_fresh_universe_name_no_collisions() {
    assert_eq!(fresh_universe_name(&[]), "u");
}

#[test]
fn test_fresh_universe_name_avoids_existing_u() {
    assert_eq!(fresh_universe_name(&["u".to_owned()]), "u_1");
}

#[test]
fn test_fresh_universe_name_avoids_multiple() {
    let existing = vec!["u".to_owned(), "u_1".to_owned(), "u_2".to_owned()];
    assert_eq!(fresh_universe_name(&existing), "u_3");
}

#[test]
fn test_universe_placeholder_fields() {
    let p = UniversePlaceholder {
        name: "u".to_owned(),
        is_auto: true,
    };
    assert!(p.is_auto);
    assert_eq!(p.name, "u");
}

// ── Notation compatibility ──────────────────────────────────────────────────

#[test]
fn test_precedence_valid_range() {
    assert!(Precedence::new(0).is_ok());
    assert!(Precedence::new(1024).is_ok());
    assert!(Precedence::new(1025).is_err());
}

#[test]
fn test_precedence_value() {
    let p = Precedence::new(65).unwrap();
    assert_eq!(p.value(), 65);
}

#[test]
fn test_default_precedence_for_infix() {
    let p = default_precedence_for_notation("infixl");
    assert_eq!(p.value(), 65);
}

#[test]
fn test_default_precedence_for_prefix() {
    let p = default_precedence_for_notation("prefix");
    assert_eq!(p.value(), 100);
}

#[test]
fn test_default_precedence_for_notation() {
    let p = default_precedence_for_notation("notation");
    assert_eq!(p, Precedence::DEFAULT);
}

// ── Tactic mapping ──────────────────────────────────────────────────────────

#[test]
fn test_resolve_tactic_ext_rw() {
    assert_eq!(resolve_tactic_ext("rw"), Some("rewrite"));
}

#[test]
fn test_resolve_tactic_ext_let() {
    assert_eq!(resolve_tactic_ext("let"), Some("let_tac"));
}

#[test]
fn test_resolve_tactic_ext_unknown() {
    assert_eq!(resolve_tactic_ext("apply"), None);
}

#[test]
fn test_resolve_tactic_ext_exact_question() {
    assert_eq!(resolve_tactic_ext("exact?"), Some("exact_search"));
}

// ── Instance priority ───────────────────────────────────────────────────────

#[test]
fn test_resolve_instance_priority_default() {
    assert_eq!(resolve_instance_priority(None), 100);
}

#[test]
fn test_resolve_instance_priority_explicit() {
    assert_eq!(resolve_instance_priority(Some(500)), 500);
}

#[test]
fn test_is_valid_instance_priority() {
    assert!(is_valid_instance_priority(100));
    assert!(is_valid_instance_priority(10_000));
    assert!(!is_valid_instance_priority(10_001));
}

// ── Feature flags ───────────────────────────────────────────────────────────

#[test]
fn test_feature_flags_v4_0_0() {
    let flags = CompatFeatureFlags::for_version(&Lean4Version::new(4, 0, 0));
    assert!(flags.auto_implicit);
    assert!(!flags.do_notation_v2);
    assert!(!flags.grind_tactic);
}

#[test]
fn test_feature_flags_v4_8_0_all_enabled() {
    let flags = CompatFeatureFlags::for_version(&Lean4Version::new(4, 8, 0));
    assert!(flags.do_notation_v2);
    assert!(flags.structure_eta);
    assert!(flags.match_discriminant_refinement);
    assert!(flags.mathverse_tactic);
    assert!(flags.grind_tactic);
    assert!(flags.auto_implicit);
    assert!(flags.relaxed_auto_implicit);
}

#[test]
fn test_feature_flags_enabled_count() {
    let flags = CompatFeatureFlags::for_version(&Lean4Version::new(4, 8, 0));
    assert_eq!(flags.enabled_count(), 7);
}

#[test]
fn test_feature_flags_v4_2_0_partial() {
    let flags = CompatFeatureFlags::for_version(&Lean4Version::new(4, 2, 0));
    assert!(flags.do_notation_v2);
    assert!(flags.structure_eta);
    assert!(flags.mathverse_tactic);
    assert!(!flags.match_discriminant_refinement);
    assert!(!flags.grind_tactic);
    assert!(!flags.relaxed_auto_implicit);
}

// ── Statistics ──────────────────────────────────────────────────────────────

#[test]
fn test_compat_stats_new_is_zero() {
    let stats = CompatStats::new();
    assert_eq!(stats.total(), 0);
}

#[test]
fn test_compat_stats_increment() {
    let stats = CompatStats::new();
    assert_eq!(stats.increment(CompatCounter::DoDesugar), 1);
    assert_eq!(stats.increment(CompatCounter::DoDesugar), 2);
    assert_eq!(stats.do_desugar_count.get(), 2);
}

#[test]
fn test_compat_stats_total_sums_all() {
    let stats = CompatStats::new();
    stats.increment(CompatCounter::DoDesugar);
    stats.increment(CompatCounter::AttrCompat);
    stats.increment(CompatCounter::TacticTranslate);
    assert_eq!(stats.total(), 3);
}

#[test]
fn test_compat_stats_all_counters() {
    let stats = CompatStats::new();
    for counter in [
        CompatCounter::DoDesugar,
        CompatCounter::WhereDesugar,
        CompatCounter::AnonCtor,
        CompatCounter::AttrCompat,
        CompatCounter::Option,
        CompatCounter::TacticTranslate,
        CompatCounter::AutoBound,
        CompatCounter::UniverseInfer,
        CompatCounter::NotationLookup,
        CompatCounter::Fallback,
    ] {
        stats.increment(counter);
    }
    assert_eq!(stats.total(), 10);
}

// ── WhereDesugar / AnonCtorDesugar ──────────────────────────────────────────

#[test]
fn test_where_desugar_fields() {
    let w = WhereDesugar {
        name: "helper".to_owned(),
        is_rec: false,
    };
    assert_eq!(w.name, "helper");
    assert!(!w.is_rec);
}

#[test]
fn test_anon_ctor_desugar_fields() {
    let a = AnonCtorDesugar {
        target_type: "Nat".to_owned(),
        arg_count: 1,
    };
    assert_eq!(a.target_type, "Nat");
    assert_eq!(a.arg_count, 1);
}

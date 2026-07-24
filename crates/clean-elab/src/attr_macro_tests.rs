// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for attribute macro expansion pipeline.

use clean_kernel::Name;
use clean_parser::Attribute;

use super::*;

// ============================================================================
// Registry creation
// ============================================================================

#[test]
fn test_registry_new_is_empty() {
    let registry = AttrMacroRegistry::new();
    assert!(registry.is_empty());
    assert_eq!(registry.len(), 0);
}

#[test]
fn test_registry_default_is_empty() {
    let registry = AttrMacroRegistry::default();
    assert!(registry.is_empty());
}

#[test]
fn test_registry_with_builtins_not_empty() {
    let registry = AttrMacroRegistry::with_builtins();
    assert!(!registry.is_empty());
    assert!(
        registry.len() >= 20,
        "expected at least 20 builtins, got {}",
        registry.len()
    );
}

#[test]
fn test_registry_with_builtins_has_simp() {
    let registry = AttrMacroRegistry::with_builtins();
    assert!(registry.is_registered("simp"));
}

#[test]
fn test_registry_with_builtins_has_all_expected() {
    let registry = AttrMacroRegistry::with_builtins();
    let expected = [
        "simp",
        "ext",
        "congr",
        "refl",
        "symm",
        "csimp",
        "reducible",
        "semireducible",
        "irreducible",
        "inline",
        "always_inline",
        "noinline",
        "macro_inline",
        "inline_if_reduce",
        "specialize",
        "nospecialize",
        "extern",
        "export",
        "implementedBy",
        "deprecated",
        "coe",
        "match_pattern",
        "class",
        "init",
        "instance",
        "default_instance",
    ];
    for name in &expected {
        assert!(registry.is_registered(name), "missing builtin: {name}");
    }
}

// ============================================================================
// Registration
// ============================================================================

#[test]
fn test_register_custom_macro() {
    let mut registry = AttrMacroRegistry::new();
    struct TestMacro;
    impl AttrMacro for TestMacro {
        fn expand(&self, _: &Name, _: &Attribute) -> Result<AttrMacroResult, ElabError> {
            Ok(AttrMacroResult::Custom("test_effect".to_owned()))
        }
    }
    registry
        .register("my_attr", 200, Box::new(TestMacro))
        .unwrap();
    assert!(registry.is_registered("my_attr"));
    assert_eq!(registry.len(), 1);
}

#[test]
fn test_register_duplicate_fails() {
    let mut registry = AttrMacroRegistry::with_builtins();
    struct DummyMacro;
    impl AttrMacro for DummyMacro {
        fn expand(&self, _: &Name, _: &Attribute) -> Result<AttrMacroResult, ElabError> {
            Ok(AttrMacroResult::Custom("dummy".to_owned()))
        }
    }
    let result = registry.register("simp", 100, Box::new(DummyMacro));
    assert!(result.is_err(), "duplicate registration should fail");
}

#[test]
fn test_registry_names_iterator() {
    let mut registry = AttrMacroRegistry::new();
    struct DummyMacro;
    impl AttrMacro for DummyMacro {
        fn expand(&self, _: &Name, _: &Attribute) -> Result<AttrMacroResult, ElabError> {
            Ok(AttrMacroResult::Custom("x".to_owned()))
        }
    }
    registry.register("alpha", 1, Box::new(DummyMacro)).unwrap();
    registry.register("beta", 2, Box::new(DummyMacro)).unwrap();
    let mut names: Vec<&str> = registry.names().collect();
    names.sort();
    assert_eq!(names, vec!["alpha", "beta"]);
}

// ============================================================================
// attr_name mapping
// ============================================================================

#[test]
fn test_attr_name_simp() {
    assert_eq!(attr_name(&Attribute::Simp { priority: None }), "simp");
}

#[test]
fn test_attr_name_ext() {
    assert_eq!(attr_name(&Attribute::Ext), "ext");
}

#[test]
fn test_attr_name_reducible() {
    assert_eq!(attr_name(&Attribute::Reducible), "reducible");
}

#[test]
fn test_attr_name_inline() {
    assert_eq!(attr_name(&Attribute::Inline), "inline");
}

#[test]
fn test_attr_name_extern() {
    assert_eq!(attr_name(&Attribute::Extern("foo".to_owned())), "extern");
}

#[test]
fn test_attr_name_unknown() {
    assert_eq!(
        attr_name(&Attribute::Unknown("my_custom".to_owned())),
        "my_custom"
    );
}

#[test]
fn test_attr_name_instance_priority() {
    assert_eq!(attr_name(&Attribute::InstancePriority(42)), "instance");
}

#[test]
fn test_attr_name_default_instance() {
    assert_eq!(
        attr_name(&Attribute::DefaultInstance { priority: None }),
        "default_instance"
    );
}

// ============================================================================
// Built-in macro expansion — individual macros
// ============================================================================

#[test]
fn test_simp_macro_no_priority() {
    let registry = AttrMacroRegistry::with_builtins();
    let name = Name::from_string("my_lemma");
    let attr = Attribute::Simp { priority: None };
    let entry = registry.get("simp").unwrap();
    let result = entry.handler.expand(&name, &attr).unwrap();
    assert_eq!(
        result,
        AttrMacroResult::RegisterSimpLemma { priority: None }
    );
}

#[test]
fn test_simp_macro_with_high_priority() {
    let registry = AttrMacroRegistry::with_builtins();
    let name = Name::from_string("my_lemma");
    let attr = Attribute::Simp {
        priority: Some(clean_parser::SimpPriority::High),
    };
    let entry = registry.get("simp").unwrap();
    let result = entry.handler.expand(&name, &attr).unwrap();
    assert_eq!(
        result,
        AttrMacroResult::RegisterSimpLemma {
            priority: Some(1500)
        }
    );
}

#[test]
fn test_simp_macro_with_low_priority() {
    let registry = AttrMacroRegistry::with_builtins();
    let name = Name::from_string("my_lemma");
    let attr = Attribute::Simp {
        priority: Some(clean_parser::SimpPriority::Low),
    };
    let entry = registry.get("simp").unwrap();
    let result = entry.handler.expand(&name, &attr).unwrap();
    assert_eq!(
        result,
        AttrMacroResult::RegisterSimpLemma {
            priority: Some(500)
        }
    );
}

#[test]
fn test_ext_macro() {
    let registry = AttrMacroRegistry::with_builtins();
    let name = Name::from_string("funext");
    let entry = registry.get("ext").unwrap();
    let result = entry.handler.expand(&name, &Attribute::Ext).unwrap();
    assert_eq!(result, AttrMacroResult::RegisterExtLemma);
}

#[test]
fn test_congr_macro() {
    let registry = AttrMacroRegistry::with_builtins();
    let name = Name::from_string("congr_lemma");
    let entry = registry.get("congr").unwrap();
    let result = entry.handler.expand(&name, &Attribute::Congr).unwrap();
    assert_eq!(result, AttrMacroResult::RegisterCongrLemma);
}

#[test]
fn test_reducible_macro() {
    let registry = AttrMacroRegistry::with_builtins();
    let name = Name::from_string("my_abbrev");
    let entry = registry.get("reducible").unwrap();
    let result = entry.handler.expand(&name, &Attribute::Reducible).unwrap();
    assert_eq!(
        result,
        AttrMacroResult::SetReducibility(ReducibilityLevel::Reducible)
    );
}

#[test]
fn test_semireducible_macro() {
    let registry = AttrMacroRegistry::with_builtins();
    let name = Name::from_string("my_def");
    let entry = registry.get("semireducible").unwrap();
    let result = entry
        .handler
        .expand(&name, &Attribute::Semireducible)
        .unwrap();
    assert_eq!(
        result,
        AttrMacroResult::SetReducibility(ReducibilityLevel::Semireducible)
    );
}

#[test]
fn test_irreducible_macro() {
    let registry = AttrMacroRegistry::with_builtins();
    let name = Name::from_string("my_opaque");
    let entry = registry.get("irreducible").unwrap();
    let result = entry
        .handler
        .expand(&name, &Attribute::Irreducible)
        .unwrap();
    assert_eq!(
        result,
        AttrMacroResult::SetReducibility(ReducibilityLevel::Irreducible)
    );
}

#[test]
fn test_inline_macro() {
    let registry = AttrMacroRegistry::with_builtins();
    let name = Name::from_string("fast_fn");
    let entry = registry.get("inline").unwrap();
    let result = entry.handler.expand(&name, &Attribute::Inline).unwrap();
    assert_eq!(result, AttrMacroResult::SetInline(InlineKind::Inline));
}

#[test]
fn test_always_inline_macro() {
    let registry = AttrMacroRegistry::with_builtins();
    let name = Name::from_string("critical_fn");
    let entry = registry.get("always_inline").unwrap();
    let result = entry
        .handler
        .expand(&name, &Attribute::AlwaysInline)
        .unwrap();
    assert_eq!(result, AttrMacroResult::SetInline(InlineKind::AlwaysInline));
}

#[test]
fn test_noinline_macro() {
    let registry = AttrMacroRegistry::with_builtins();
    let name = Name::from_string("big_fn");
    let entry = registry.get("noinline").unwrap();
    let result = entry.handler.expand(&name, &Attribute::Noinline).unwrap();
    assert_eq!(result, AttrMacroResult::SetInline(InlineKind::Noinline));
}

#[test]
fn test_extern_macro() {
    let registry = AttrMacroRegistry::with_builtins();
    let name = Name::from_string("lean_io_prim");
    let attr = Attribute::Extern("lean_io_prim_read".to_owned());
    let entry = registry.get("extern").unwrap();
    let result = entry.handler.expand(&name, &attr).unwrap();
    assert_eq!(
        result,
        AttrMacroResult::RegisterExtern {
            extern_name: "lean_io_prim_read".to_owned()
        }
    );
}

#[test]
fn test_export_macro() {
    let registry = AttrMacroRegistry::with_builtins();
    let name = Name::from_string("my_export");
    let attr = Attribute::Export("lean_my_export".to_owned());
    let entry = registry.get("export").unwrap();
    let result = entry.handler.expand(&name, &attr).unwrap();
    assert_eq!(
        result,
        AttrMacroResult::RegisterExport {
            export_name: "lean_my_export".to_owned()
        }
    );
}

#[test]
fn test_implemented_by_macro() {
    let registry = AttrMacroRegistry::with_builtins();
    let name = Name::from_string("slow_fn");
    let attr = Attribute::ImplementedBy("fast_fn_impl".to_owned());
    let entry = registry.get("implementedBy").unwrap();
    let result = entry.handler.expand(&name, &attr).unwrap();
    assert_eq!(
        result,
        AttrMacroResult::RegisterImplementedBy {
            impl_name: "fast_fn_impl".to_owned()
        }
    );
}

#[test]
fn test_deprecated_macro_no_message() {
    let registry = AttrMacroRegistry::with_builtins();
    let name = Name::from_string("old_fn");
    let attr = Attribute::Deprecated(None);
    let entry = registry.get("deprecated").unwrap();
    let result = entry.handler.expand(&name, &attr).unwrap();
    assert_eq!(
        result,
        AttrMacroResult::RegisterDeprecated { message: None }
    );
}

#[test]
fn test_deprecated_macro_with_message() {
    let registry = AttrMacroRegistry::with_builtins();
    let name = Name::from_string("old_fn");
    let attr = Attribute::Deprecated(Some("use new_fn instead".to_owned()));
    let entry = registry.get("deprecated").unwrap();
    let result = entry.handler.expand(&name, &attr).unwrap();
    assert_eq!(
        result,
        AttrMacroResult::RegisterDeprecated {
            message: Some("use new_fn instead".to_owned())
        }
    );
}

#[test]
fn test_coe_macro() {
    let registry = AttrMacroRegistry::with_builtins();
    let name = Name::from_string("nat_to_int");
    let entry = registry.get("coe").unwrap();
    let result = entry.handler.expand(&name, &Attribute::Coe).unwrap();
    assert_eq!(result, AttrMacroResult::RegisterCoercion);
}

#[test]
fn test_instance_macro() {
    let registry = AttrMacroRegistry::with_builtins();
    let name = Name::from_string("my_instance");
    let attr = Attribute::InstancePriority(500);
    let entry = registry.get("instance").unwrap();
    let result = entry.handler.expand(&name, &attr).unwrap();
    assert_eq!(result, AttrMacroResult::RegisterInstance { priority: 500 });
}

#[test]
fn test_default_instance_macro() {
    let registry = AttrMacroRegistry::with_builtins();
    let name = Name::from_string("fallback_inst");
    let entry = registry.get("default_instance").unwrap();
    let result = entry
        .handler
        .expand(&name, &Attribute::DefaultInstance { priority: None })
        .unwrap();
    assert_eq!(result, AttrMacroResult::RegisterDefaultInstance);
}

// ============================================================================
// Expansion pipeline
// ============================================================================

#[test]
fn test_expand_empty_attrs() {
    let registry = AttrMacroRegistry::with_builtins();
    let name = Name::from_string("my_decl");
    let result = expand_attributes(&name, &[], &registry);
    assert!(result.effects.is_empty());
    assert!(result.errors.is_empty());
    assert!(result.unhandled.is_empty());
}

#[test]
fn test_expand_single_attr() {
    let registry = AttrMacroRegistry::with_builtins();
    let name = Name::from_string("my_lemma");
    let attrs = vec![Attribute::Simp { priority: None }];
    let result = expand_attributes(&name, &attrs, &registry);
    assert_eq!(result.effects.len(), 1);
    assert_eq!(
        result.effects[0],
        AttrMacroResult::RegisterSimpLemma { priority: None }
    );
    assert!(result.errors.is_empty());
    assert!(result.unhandled.is_empty());
}

#[test]
fn test_expand_multiple_attrs() {
    let registry = AttrMacroRegistry::with_builtins();
    let name = Name::from_string("my_simp_ext");
    let attrs = vec![
        Attribute::Simp { priority: None },
        Attribute::Ext,
        Attribute::Inline,
    ];
    let result = expand_attributes(&name, &attrs, &registry);
    assert_eq!(result.effects.len(), 3);
    assert!(result.errors.is_empty());
}

#[test]
fn test_expand_unknown_attr_unhandled() {
    let registry = AttrMacroRegistry::with_builtins();
    let name = Name::from_string("my_decl");
    let attrs = vec![Attribute::Unknown("nonexistent".to_owned())];
    let result = expand_attributes(&name, &attrs, &registry);
    assert!(result.effects.is_empty());
    assert!(result.errors.is_empty());
    assert_eq!(result.unhandled.len(), 1);
    assert_eq!(result.unhandled[0], "nonexistent");
}

#[test]
fn test_expand_mixed_known_and_unknown() {
    let registry = AttrMacroRegistry::with_builtins();
    let name = Name::from_string("my_decl");
    let attrs = vec![
        Attribute::Simp { priority: None },
        Attribute::Unknown("custom_thing".to_owned()),
        Attribute::Inline,
    ];
    let result = expand_attributes(&name, &attrs, &registry);
    assert_eq!(result.effects.len(), 2);
    assert_eq!(result.unhandled.len(), 1);
    assert_eq!(result.unhandled[0], "custom_thing");
}

#[test]
fn test_expand_priority_ordering() {
    // Reducibility has priority 50, inline has 100.
    // Even though inline comes first in the list, reducibility should be expanded first.
    let registry = AttrMacroRegistry::with_builtins();
    let name = Name::from_string("my_decl");
    let attrs = vec![Attribute::Inline, Attribute::Reducible];
    let result = expand_attributes(&name, &attrs, &registry);
    assert_eq!(result.effects.len(), 2);
    // Reducible (priority 50) should come before Inline (priority 100)
    assert_eq!(
        result.effects[0],
        AttrMacroResult::SetReducibility(ReducibilityLevel::Reducible)
    );
    assert_eq!(
        result.effects[1],
        AttrMacroResult::SetInline(InlineKind::Inline)
    );
}

#[test]
fn test_expand_same_priority_preserves_order() {
    // simp and ext both have BUILTIN_PRIORITY=100, so source order is preserved.
    let registry = AttrMacroRegistry::with_builtins();
    let name = Name::from_string("my_decl");
    let attrs = vec![Attribute::Ext, Attribute::Simp { priority: None }];
    let result = expand_attributes(&name, &attrs, &registry);
    assert_eq!(result.effects.len(), 2);
    assert_eq!(result.effects[0], AttrMacroResult::RegisterExtLemma);
    assert_eq!(
        result.effects[1],
        AttrMacroResult::RegisterSimpLemma { priority: None }
    );
}

#[test]
fn test_expand_error_from_wrong_attr_type() {
    // The ExternAttrMacro expects Attribute::Extern but gets something else
    // if directly invoked. Through the pipeline this doesn't happen because
    // attr_name routes correctly. This tests direct handler invocation.
    let registry = AttrMacroRegistry::with_builtins();
    let name = Name::from_string("test");
    let entry = registry.get("extern").unwrap();
    let result = entry.handler.expand(&name, &Attribute::Inline);
    assert!(result.is_err());
}

#[test]
fn test_expand_custom_macro_in_pipeline() {
    let mut registry = AttrMacroRegistry::new();
    struct TagMacro;
    impl AttrMacro for TagMacro {
        fn expand(&self, _: &Name, _: &Attribute) -> Result<AttrMacroResult, ElabError> {
            Ok(AttrMacroResult::Custom("tagged".to_owned()))
        }
    }
    registry.register("my_tag", 50, Box::new(TagMacro)).unwrap();

    let name = Name::from_string("my_decl");
    let attrs = vec![Attribute::Unknown("my_tag".to_owned())];
    let result = expand_attributes(&name, &attrs, &registry);
    assert_eq!(result.effects.len(), 1);
    assert_eq!(
        result.effects[0],
        AttrMacroResult::Custom("tagged".to_owned())
    );
}

#[test]
fn test_expand_failing_custom_macro_collects_error() {
    let mut registry = AttrMacroRegistry::new();
    struct FailMacro;
    impl AttrMacro for FailMacro {
        fn expand(&self, _: &Name, _: &Attribute) -> Result<AttrMacroResult, ElabError> {
            Err(ElabError::Unsupported {
                feature: "intentional failure".to_owned(),
            })
        }
    }
    registry
        .register("fail_attr", 100, Box::new(FailMacro))
        .unwrap();

    let name = Name::from_string("my_decl");
    let attrs = vec![Attribute::Unknown("fail_attr".to_owned())];
    let result = expand_attributes(&name, &attrs, &registry);
    assert!(result.effects.is_empty());
    assert_eq!(result.errors.len(), 1);
    assert_eq!(result.errors[0].0, "fail_attr");
}

// ============================================================================
// Debug impls
// ============================================================================

#[test]
fn test_registry_debug() {
    let registry = AttrMacroRegistry::with_builtins();
    let debug_str = format!("{registry:?}");
    assert!(debug_str.contains("AttrMacroRegistry"));
    assert!(debug_str.contains("count"));
}

#[test]
fn test_expansion_result_debug() {
    let result = ExpansionResult {
        effects: vec![AttrMacroResult::RegisterExtLemma],
        errors: vec![],
        unhandled: vec!["foo".to_owned()],
    };
    let debug_str = format!("{result:?}");
    assert!(debug_str.contains("RegisterExtLemma"));
    assert!(debug_str.contains("foo"));
}

// ============================================================================
// Edge cases
// ============================================================================

#[test]
fn test_expand_aesop_is_unhandled() {
    // Aesop has its own dedicated path in the elaborator, not handled by
    // the attr_macro pipeline (no builtin macro registered for "aesop").
    let registry = AttrMacroRegistry::with_builtins();
    let name = Name::from_string("my_rule");
    let attrs = vec![Attribute::Aesop(clean_parser::AesopAttr {
        phase: clean_parser::AesopPhase::Safe,
        builder: clean_parser::AesopBuilder::Apply,
        builder_args: vec![],
        priority: None,
        rule_sets: vec![],
        index_mode: clean_parser::AesopIndexMode::Target,
    })];
    let result = expand_attributes(&name, &attrs, &registry);
    assert!(result.effects.is_empty());
    assert_eq!(result.unhandled.len(), 1);
    assert_eq!(result.unhandled[0], "aesop");
}

#[test]
fn test_expand_all_reducibility_levels() {
    let registry = AttrMacroRegistry::with_builtins();
    let name = Name::from_string("test");
    for (attr, expected) in [
        (Attribute::Reducible, ReducibilityLevel::Reducible),
        (Attribute::Semireducible, ReducibilityLevel::Semireducible),
        (Attribute::Irreducible, ReducibilityLevel::Irreducible),
    ] {
        let result = expand_attributes(&name, &[attr], &registry);
        assert_eq!(result.effects.len(), 1);
        assert_eq!(
            result.effects[0],
            AttrMacroResult::SetReducibility(expected)
        );
    }
}

#[test]
fn test_expand_all_inline_kinds() {
    let registry = AttrMacroRegistry::with_builtins();
    let name = Name::from_string("test");
    for (attr, expected) in [
        (Attribute::Inline, InlineKind::Inline),
        (Attribute::AlwaysInline, InlineKind::AlwaysInline),
        (Attribute::Noinline, InlineKind::Noinline),
        (Attribute::MacroInline, InlineKind::MacroInline),
        (Attribute::InlineIfReduce, InlineKind::InlineIfReduce),
    ] {
        let result = expand_attributes(&name, &[attr], &registry);
        assert_eq!(result.effects.len(), 1);
        assert_eq!(result.effects[0], AttrMacroResult::SetInline(expected));
    }
}

#[test]
fn test_expand_specialize_kinds() {
    let registry = AttrMacroRegistry::with_builtins();
    let name = Name::from_string("test");
    for (attr, expected) in [
        (Attribute::Specialize, SpecializeKind::Specialize),
        (Attribute::Nospecialize, SpecializeKind::Nospecialize),
    ] {
        let result = expand_attributes(&name, &[attr], &registry);
        assert_eq!(result.effects.len(), 1);
        assert_eq!(result.effects[0], AttrMacroResult::SetSpecialize(expected));
    }
}

#[test]
fn test_expand_many_attrs_on_same_decl() {
    let registry = AttrMacroRegistry::with_builtins();
    let name = Name::from_string("swiss_army");
    let attrs = vec![
        Attribute::Reducible,
        Attribute::Inline,
        Attribute::Simp { priority: None },
        Attribute::Ext,
        Attribute::Deprecated(Some("testing".to_owned())),
    ];
    let result = expand_attributes(&name, &attrs, &registry);
    assert_eq!(result.effects.len(), 5);
    assert!(result.errors.is_empty());
    assert!(result.unhandled.is_empty());
    // Reducible should come first (priority 50 vs 100)
    assert_eq!(
        result.effects[0],
        AttrMacroResult::SetReducibility(ReducibilityLevel::Reducible)
    );
}

#[test]
fn test_get_nonexistent_returns_none() {
    let registry = AttrMacroRegistry::with_builtins();
    assert!(registry.get("absolutely_nonexistent").is_none());
}

#[test]
fn test_is_registered_false_for_unknown() {
    let registry = AttrMacroRegistry::with_builtins();
    assert!(!registry.is_registered("unknown_attr_xyz"));
}

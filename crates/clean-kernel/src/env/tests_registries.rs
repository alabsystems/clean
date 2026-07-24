// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Registry tests extracted from env/tests.rs (#1417).
// Coverage for registries.rs: classes, instances, simp, aesop, hints,
// generation counter, and unchecked bulk operations.

use super::*;

// ============================================================================
// Registry tests (registries.rs coverage — previously 0 tests for 664 lines)
// ============================================================================

#[test]
fn test_register_class_and_lookup() {
    let mut env = Environment::new();
    let class_name = Name::from_string("Functor");

    assert!(!env.is_class(&class_name));
    assert_eq!(env.num_classes(), 0);
    assert!(
        env.get_class_info(&class_name).is_none(),
        "class should not exist before registration"
    );

    env.register_class(KernelClassInfo {
        name: class_name.clone(),
        num_params: 1,
        out_params: vec![],
        semi_out_params: vec![],
    });

    assert!(env.is_class(&class_name));
    assert_eq!(env.num_classes(), 1);
    let info = env.get_class_info(&class_name).unwrap();
    assert_eq!(info.name, class_name);
    assert_eq!(info.num_params, 1);
}

#[test]
fn test_register_class_overwrite() {
    let mut env = Environment::new();
    let name = Name::from_string("Monad");

    env.register_class(KernelClassInfo {
        name: name.clone(),
        num_params: 1,
        out_params: vec![],
        semi_out_params: vec![],
    });
    assert_eq!(env.get_class_info(&name).unwrap().num_params, 1);

    // Re-registering same name overwrites
    env.register_class(KernelClassInfo {
        name: name.clone(),
        num_params: 2,
        out_params: vec![0],
        semi_out_params: vec![],
    });
    assert_eq!(env.num_classes(), 1);
    assert_eq!(env.get_class_info(&name).unwrap().num_params, 2);
    assert_eq!(env.get_class_info(&name).unwrap().out_params, vec![0]);
}

#[test]
fn test_classes_iterator() {
    let mut env = Environment::new();
    for i in 0..5 {
        env.register_class(KernelClassInfo {
            name: Name::from_string(&format!("Class{i}")),
            num_params: i,
            out_params: vec![],
            semi_out_params: vec![],
        });
    }
    assert_eq!(env.num_classes(), 5);
    let names: Vec<_> = env.classes().map(|c| c.name.clone()).collect();
    assert_eq!(names.len(), 5);
    for i in 0..5 {
        assert!(names.contains(&Name::from_string(&format!("Class{i}"))));
    }
}

#[test]
fn test_register_instance_priority_ordering() {
    let mut env = Environment::new();
    let class = Name::from_string("Add");

    // Register instances with different priorities
    for (name, prio) in [
        ("instAddNat", 100u32),
        ("instAddInt", 200),
        ("instAddFloat", 50),
    ] {
        env.register_instance(KernelInstanceInfo {
            name: Name::from_string(name),
            class_name: class.clone(),
            priority: prio,
            type_: None,
            value: None,
        });
    }

    let instances = env.get_class_instances(&class);
    assert_eq!(instances.len(), 3);
    // Highest priority first
    assert_eq!(instances[0].name, Name::from_string("instAddInt"));
    assert_eq!(instances[0].priority, 200);
    assert_eq!(instances[1].name, Name::from_string("instAddNat"));
    assert_eq!(instances[1].priority, 100);
    assert_eq!(instances[2].name, Name::from_string("instAddFloat"));
    assert_eq!(instances[2].priority, 50);
}

/// Within one priority tier the MOST-RECENTLY-registered instance is first —
/// Lean 4's later-declared-wins semantics (`src/Lean/Meta/Instances.lean`,
/// `addInstanceEntry` prepends). Sweep B12 `classes_instances/p06`: a value-pin
/// bug (`Qw.v 0 = 2`) where the first-declared instance used to win.
#[test]
fn test_register_instance_equal_priority_most_recent_first() {
    let mut env = Environment::new();
    let class = Name::from_string("Qw");

    // Three equal-priority instances, registered oldest → newest.
    for name in ["instQwNat", "instQwNat_1", "instQwNat_2"] {
        env.register_instance(KernelInstanceInfo {
            name: Name::from_string(name),
            class_name: class.clone(),
            priority: 100,
            type_: None,
            value: None,
        });
    }

    let instances = env.get_class_instances(&class);
    assert_eq!(instances.len(), 3);
    // Most-recent (last registered) resolves first.
    assert_eq!(instances[0].name, Name::from_string("instQwNat_2"));
    assert_eq!(instances[1].name, Name::from_string("instQwNat_1"));
    assert_eq!(instances[2].name, Name::from_string("instQwNat"));
}

/// A higher-priority instance registered LATER still sorts ahead of an existing
/// lower-priority one, and a same-priority instance registered between them
/// lands most-recent-first within its own tier — the two orderings compose.
#[test]
fn test_register_instance_priority_dominates_recency() {
    let mut env = Environment::new();
    let class = Name::from_string("PrA");

    // Order of registration: high(200), then default(100), then a SECOND
    // default(100). Expected resolution order: [high, default2, default1].
    for (name, prio) in [
        ("instPrAHigh", 200u32),
        ("instPrADefault1", 100),
        ("instPrADefault2", 100),
    ] {
        env.register_instance(KernelInstanceInfo {
            name: Name::from_string(name),
            class_name: class.clone(),
            priority: prio,
            type_: None,
            value: None,
        });
    }

    let instances = env.get_class_instances(&class);
    assert_eq!(instances.len(), 3);
    assert_eq!(instances[0].name, Name::from_string("instPrAHigh"));
    assert_eq!(instances[1].name, Name::from_string("instPrADefault2"));
    assert_eq!(instances[2].name, Name::from_string("instPrADefault1"));
}

#[test]
fn test_is_instance_lookup() {
    let mut env = Environment::new();
    let inst_name = Name::from_string("instMonadIO");
    let other = Name::from_string("someFunc");

    assert!(!env.is_instance(&inst_name));

    env.register_instance(KernelInstanceInfo {
        name: inst_name.clone(),
        class_name: Name::from_string("Monad"),
        priority: 100,
        type_: None,
        value: None,
    });

    assert!(env.is_instance(&inst_name));
    assert!(!env.is_instance(&other));
}

#[test]
fn test_num_instances() {
    let mut env = Environment::new();
    assert_eq!(env.num_instances(), 0);

    for (i, class) in ["A", "B", "A"].iter().enumerate() {
        env.register_instance(KernelInstanceInfo {
            name: Name::from_string(&format!("inst{i}")),
            class_name: Name::from_string(class),
            priority: 100,
            type_: None,
            value: None,
        });
    }
    assert_eq!(env.num_instances(), 3);
}

#[test]
fn test_instances_iterator() {
    let mut env = Environment::new();
    for i in 0..4 {
        env.register_instance(KernelInstanceInfo {
            name: Name::from_string(&format!("inst{i}")),
            class_name: Name::from_string(&format!("Class{}", i % 2)),
            priority: 100,
            type_: None,
            value: None,
        });
    }
    let all: Vec<_> = env.instances().collect();
    assert_eq!(all.len(), 4);
}

#[test]
fn test_get_class_instances_empty() {
    let env = Environment::new();
    let instances = env.get_class_instances(&Name::from_string("Nonexistent"));
    assert!(instances.is_empty());
}

#[test]
fn test_register_simp_lemma_and_lookup() {
    let mut env = Environment::new();
    let name = Name::from_string("Nat.add_zero");

    assert!(!env.is_simp_lemma(&name));
    assert!(
        env.get_simp_lemma(&name).is_none(),
        "simp lemma should not exist before registration"
    );

    env.register_simp_lemma(name.clone(), SimpPriority::Default);
    assert!(env.is_simp_lemma(&name));
    let info = env.get_simp_lemma(&name).unwrap();
    assert_eq!(info.priority, SimpPriority::Default);
}

#[test]
fn test_simp_lemma_custom_priority() {
    let mut env = Environment::new();
    let name = Name::from_string("List.map_id");

    env.register_simp_lemma(name.clone(), SimpPriority::Custom(500));
    let info = env.get_simp_lemma(&name).unwrap();
    assert_eq!(info.priority, SimpPriority::Custom(500));
}

#[test]
fn test_get_simp_lemmas_iterator() {
    let mut env = Environment::new();
    env.register_simp_lemma(Name::from_string("a"), SimpPriority::Default);
    env.register_simp_lemma(Name::from_string("b"), SimpPriority::Custom(100));
    let lemmas: Vec<_> = env.get_simp_lemmas().collect();
    assert_eq!(lemmas.len(), 2);
}

#[test]
fn test_unregister_simp_lemma() {
    let mut env = Environment::new();
    let name = Name::from_string("Nat.add_zero");

    env.register_simp_lemma(name.clone(), SimpPriority::Default);
    assert!(env.unregister_simp_lemma(&name));
    assert!(!env.is_simp_lemma(&name));
    assert!(!env.unregister_simp_lemma(&name));
}

#[test]
fn test_register_extern_and_lookup() {
    let mut env = Environment::new();
    let decl = Name::from_string("lean_io_prim_handle_mk");

    assert!(!env.is_extern(&decl));
    assert_eq!(env.get_extern(&decl), None);

    env.register_extern(decl.clone(), "lean_io_handle_mk".to_string());
    assert!(env.is_extern(&decl));
    assert_eq!(env.get_extern(&decl).unwrap(), "lean_io_handle_mk");
}

#[test]
fn test_register_export_and_lookup() {
    let mut env = Environment::new();
    let decl = Name::from_string("MyLib.sort");

    assert!(!env.is_export(&decl));
    env.register_export(decl.clone(), "my_sort".to_string());
    assert!(env.is_export(&decl));
    assert_eq!(env.get_export(&decl).unwrap(), "my_sort");
}

#[test]
fn test_register_deprecated() {
    let mut env = Environment::new();
    let name = Name::from_string("oldFunc");

    assert!(!env.is_deprecated(&name));
    assert_eq!(env.get_deprecation_message(&name), None);

    env.register_deprecated(name.clone(), Some("use newFunc instead".to_string()));
    assert!(env.is_deprecated(&name));
    assert_eq!(
        env.get_deprecation_message(&name),
        Some(&Some("use newFunc instead".to_string()))
    );
}

#[test]
fn test_register_deprecated_no_message() {
    let mut env = Environment::new();
    let name = Name::from_string("oldFunc2");

    env.register_deprecated(name.clone(), None);
    assert!(env.is_deprecated(&name));
    assert_eq!(env.get_deprecation_message(&name), Some(&None));
}

#[test]
fn test_inline_hints() {
    let mut env = Environment::new();
    let name = Name::from_string("fastPath");

    assert!(!env.is_inline(&name));
    env.register_inline(name.clone());
    assert!(env.is_inline(&name));

    assert!(!env.is_noinline(&name));
    assert!(!env.is_always_inline(&name));
}

#[test]
fn test_noinline_hint() {
    let mut env = Environment::new();
    let name = Name::from_string("slowPath");

    assert!(!env.is_noinline(&name));
    env.register_noinline(name.clone());
    assert!(env.is_noinline(&name));
}

#[test]
fn test_always_inline_hint() {
    let mut env = Environment::new();
    let name = Name::from_string("criticalPath");

    assert!(!env.is_always_inline(&name));
    env.register_always_inline(name.clone());
    assert!(env.is_always_inline(&name));
}

#[test]
fn test_specialize_hint() {
    let mut env = Environment::new();
    let name = Name::from_string("genericOp");

    assert!(!env.is_specialize(&name));
    env.register_specialize(name.clone());
    assert!(env.is_specialize(&name));
}

#[test]
fn test_register_derive_handler() {
    let mut env = Environment::new();
    let class_name = Name::from_string("MyClass");
    let handler_name = Name::from_string("deriveMyClass");

    assert!(env.get_derive_handlers(&class_name).is_none());

    env.register_derive_handler(class_name.clone(), handler_name.clone());

    let handlers = env
        .get_derive_handlers(&class_name)
        .expect("derive handlers should be present");
    assert_eq!(handlers, std::slice::from_ref(&handler_name));

    // Duplicate registration should be ignored.
    env.register_derive_handler(class_name.clone(), handler_name.clone());
    let handlers = env
        .get_derive_handlers(&class_name)
        .expect("derive handlers should still be present");
    assert_eq!(handlers, &[handler_name]);
}

#[test]
fn test_csimp_lemma() {
    let mut env = Environment::new();
    let name = Name::from_string("Nat.add_comm");

    assert!(!env.is_csimp(&name));
    env.register_csimp(name.clone());
    assert!(env.is_csimp(&name));
}

#[test]
fn test_congr_lemma() {
    let mut env = Environment::new();
    let name = Name::from_string("congr_arg");

    assert!(!env.is_congr(&name));
    env.register_congr(name.clone());
    assert!(env.is_congr(&name));
}

#[test]
fn test_ext_lemma() {
    let mut env = Environment::new();
    let name = Name::from_string("funext");

    assert!(!env.is_ext(&name));
    env.register_ext(name.clone());
    assert!(env.is_ext(&name));
}

#[test]
fn test_refl_lemma() {
    let mut env = Environment::new();
    let name = Name::from_string("Eq.refl");

    assert!(!env.is_refl(&name));
    env.register_refl(name.clone());
    assert!(env.is_refl(&name));
}

#[test]
fn test_symm_lemma() {
    let mut env = Environment::new();
    let name = Name::from_string("Eq.symm");

    assert!(!env.is_symm(&name));
    env.register_symm(name.clone());
    assert!(env.is_symm(&name));
}

#[test]
fn test_set_reducibility() {
    let mut env = Environment::new();
    let name = Name::from_string("myDef");

    // set_reducibility on nonexistent constant returns false
    assert!(!env.set_reducibility(&name, Reducibility::Irreducible));

    // Add a constant
    env.constants.insert(
        name.clone(),
        ConstantInfo::new(name.clone(), vec![], Expr::prop(), Some(Expr::prop()), true),
    );

    assert_eq!(env.get_reducibility(&name), Some(Reducibility::Reducible)); // default

    assert!(env.set_reducibility(&name, Reducibility::Irreducible));
    assert_eq!(env.get_reducibility(&name), Some(Reducibility::Irreducible));

    assert!(env.set_reducibility(&name, Reducibility::Regular(0)));
    assert_eq!(env.get_reducibility(&name), Some(Reducibility::Regular(0)));
}

#[test]
fn test_set_reducibility_updates_legacy_flag() {
    let mut env = Environment::new();
    let name = Name::from_string("myDef");

    env.constants.insert(
        name.clone(),
        ConstantInfo::new(name.clone(), vec![], Expr::prop(), Some(Expr::prop()), true),
    );

    // Default: Reducible → is_reducible should be true
    assert!(env.constants.get(&name).unwrap().is_reducible);

    env.set_reducibility(&name, Reducibility::Irreducible);
    assert!(!env.constants.get(&name).unwrap().is_reducible);

    env.set_reducibility(&name, Reducibility::Reducible);
    assert!(env.constants.get(&name).unwrap().is_reducible);
}

#[test]
fn test_get_reducibility_nonexistent() {
    let env = Environment::new();
    assert_eq!(env.get_reducibility(&Name::from_string("nope")), None);
}

// ============================================================================
// Aesop rule registry tests
// ============================================================================

#[test]
fn test_aesop_rule_registration_by_phase() {
    let mut env = Environment::new();

    let safe_rule = AesopRule {
        name: Name::from_string("intro_and"),
        phase: AesopRulePhase::Safe,
        builder: AesopRuleBuilder::Apply,
        builder_args: vec![],
        priority: 100,
        index_mode: AesopIndexMode::Unindexed,
        transparency: TransparencyMode::Default,
    };
    let unsafe_rule = AesopRule {
        name: Name::from_string("apply_hyp"),
        phase: AesopRulePhase::Unsafe,
        builder: AesopRuleBuilder::Apply,
        builder_args: vec![],
        priority: 50,
        index_mode: AesopIndexMode::Unindexed,
        transparency: TransparencyMode::Default,
    };
    let norm_rule = AesopRule {
        name: Name::from_string("simp_all"),
        phase: AesopRulePhase::Norm,
        builder: AesopRuleBuilder::Simp,
        builder_args: vec![],
        priority: 100,
        index_mode: AesopIndexMode::Unindexed,
        transparency: TransparencyMode::Default,
    };

    env.register_aesop_rule(safe_rule);
    env.register_aesop_rule(unsafe_rule);
    env.register_aesop_rule(norm_rule);

    assert_eq!(env.get_aesop_safe_rules().len(), 1);
    assert_eq!(env.get_aesop_unsafe_rules().len(), 1);
    assert_eq!(env.get_aesop_norm_rules().len(), 1);

    assert_eq!(env.get_aesop_rules(AesopRulePhase::Safe).len(), 1);
    assert_eq!(env.get_aesop_rules(AesopRulePhase::Unsafe).len(), 1);
    assert_eq!(env.get_aesop_rules(AesopRulePhase::Norm).len(), 1);
}

#[test]
fn test_aesop_unsafe_rules_priority_order() {
    let mut env = Environment::new();

    for prio in [30u32, 90, 10, 60] {
        env.register_aesop_rule(AesopRule {
            name: Name::from_string(&format!("rule_p{prio}")),
            phase: AesopRulePhase::Unsafe,
            builder: AesopRuleBuilder::Apply,
            builder_args: vec![],
            priority: prio,
            index_mode: AesopIndexMode::Unindexed,
            transparency: TransparencyMode::Default,
        });
    }

    let rules = env.get_aesop_unsafe_rules();
    assert_eq!(rules.len(), 4);
    // Must be sorted highest-priority first
    assert_eq!(rules[0].priority, 90);
    assert_eq!(rules[1].priority, 60);
    assert_eq!(rules[2].priority, 30);
    assert_eq!(rules[3].priority, 10);
}

#[test]
fn test_declare_aesop_rule_set() {
    let mut env = Environment::new();
    let set_name = Name::from_string("Measurable");

    assert!(!env.is_aesop_rule_set_declared(&set_name));
    assert!(
        env.get_named_rule_set(&set_name).is_none(),
        "rule set should not exist before declaration"
    );

    env.declare_aesop_rule_set(set_name.clone());
    assert!(env.is_aesop_rule_set_declared(&set_name));
    let rule_set = env
        .get_named_rule_set(&set_name)
        .expect("declared rule set should be retrievable");
    assert!(
        rule_set.safe_rules.is_empty()
            && rule_set.unsafe_rules.is_empty()
            && rule_set.norm_rules.is_empty(),
        "freshly declared rule set should have no rules"
    );

    // Declaring again is idempotent (doesn't duplicate)
    env.declare_aesop_rule_set(set_name.clone());
    assert_eq!(env.get_declared_rule_sets().count(), 1);
}

#[test]
fn test_register_aesop_rule_to_set() {
    let mut env = Environment::new();
    let set_name = Name::from_string("Continuity");

    // Registering to undeclared set returns false
    let rule = AesopRule {
        name: Name::from_string("continuous_id"),
        phase: AesopRulePhase::Safe,
        builder: AesopRuleBuilder::Apply,
        builder_args: vec![],
        priority: 100,
        index_mode: AesopIndexMode::Unindexed,
        transparency: TransparencyMode::Default,
    };
    assert!(!env.register_aesop_rule_to_set(&set_name, rule.clone()));

    // Declare then register
    env.declare_aesop_rule_set(set_name.clone());
    assert!(env.register_aesop_rule_to_set(&set_name, rule));

    let set = env.get_named_rule_set(&set_name).unwrap();
    assert_eq!(set.safe_rules.len(), 1);
    assert_eq!(set.safe_rules[0].name, Name::from_string("continuous_id"));
}

#[test]
fn test_get_combined_rule_sets_empty_returns_default() {
    let mut env = Environment::new();

    // Add a default rule
    env.register_aesop_rule(AesopRule {
        name: Name::from_string("default_rule"),
        phase: AesopRulePhase::Safe,
        builder: AesopRuleBuilder::Apply,
        builder_args: vec![],
        priority: 100,
        index_mode: AesopIndexMode::Unindexed,
        transparency: TransparencyMode::Default,
    });

    // Empty set names → returns default rules
    let combined = env.get_combined_rule_sets(&[]);
    assert_eq!(combined.safe_rules.len(), 1);
}

#[test]
fn test_get_combined_rule_sets_merges() {
    let mut env = Environment::new();
    let set_a = Name::from_string("SetA");
    let set_b = Name::from_string("SetB");

    env.declare_aesop_rule_set(set_a.clone());
    env.declare_aesop_rule_set(set_b.clone());

    env.register_aesop_rule_to_set(
        &set_a,
        AesopRule {
            name: Name::from_string("rule_a"),
            phase: AesopRulePhase::Safe,
            builder: AesopRuleBuilder::Apply,
            builder_args: vec![],
            priority: 100,
            index_mode: AesopIndexMode::Unindexed,
            transparency: TransparencyMode::Default,
        },
    );
    env.register_aesop_rule_to_set(
        &set_b,
        AesopRule {
            name: Name::from_string("rule_b"),
            phase: AesopRulePhase::Unsafe,
            builder: AesopRuleBuilder::Forward,
            builder_args: vec![],
            priority: 50,
            index_mode: AesopIndexMode::Unindexed,
            transparency: TransparencyMode::Default,
        },
    );

    let combined = env.get_combined_rule_sets(&[set_a, set_b]);
    assert_eq!(combined.safe_rules.len(), 1);
    assert_eq!(combined.unsafe_rules.len(), 1);
}

#[test]
fn test_aesop_unindexed_rules_included_in_target_lookup() {
    let mut env = Environment::new();

    // Register an unindexed rule
    env.register_aesop_rule(AesopRule {
        name: Name::from_string("catch_all"),
        phase: AesopRulePhase::Safe,
        builder: AesopRuleBuilder::Apply,
        builder_args: vec![],
        priority: 100,
        index_mode: AesopIndexMode::Unindexed,
        transparency: TransparencyMode::Default,
    });

    // Unindexed rules should appear for any target lookup
    let rules = env.get_rules_for_target(&Name::from_string("Whatever"));
    assert_eq!(rules.len(), 1);
    assert_eq!(rules[0].name, Name::from_string("catch_all"));
}

#[test]
fn test_aesop_unindexed_rules_included_in_hyps_lookup() {
    let mut env = Environment::new();

    env.register_aesop_rule(AesopRule {
        name: Name::from_string("catch_all"),
        phase: AesopRulePhase::Safe,
        builder: AesopRuleBuilder::Apply,
        builder_args: vec![],
        priority: 100,
        index_mode: AesopIndexMode::Unindexed,
        transparency: TransparencyMode::Default,
    });

    let rules = env.get_rules_for_hyps(&[Name::from_string("Whatever")]);
    assert_eq!(rules.len(), 1);
}

#[test]
fn test_generation_increments_on_registry_mutations() {
    let mut env = Environment::new();
    let gen0 = env.generation;

    env.register_class(KernelClassInfo {
        name: Name::from_string("C1"),
        num_params: 0,
        out_params: vec![],
        semi_out_params: vec![],
    });
    assert!(env.generation > gen0, "register_class must bump generation");
    let gen1 = env.generation;

    env.register_instance(KernelInstanceInfo {
        name: Name::from_string("i1"),
        class_name: Name::from_string("C1"),
        priority: 100,
        type_: None,
        value: None,
    });
    assert!(
        env.generation > gen1,
        "register_instance must bump generation"
    );
}

// ====================================================================
// Tests for unchecked registration functions (Part of #1357)
// These functions bypass validation and are used for .olean import.
// ====================================================================

/// Test register_inductive_unchecked: inserts into both constants and inductives maps,
/// and bumps generation. This is the primary gap identified in the #1357 audit.
#[test]
fn test_register_inductive_unchecked_inserts_and_bumps_generation() {
    use crate::inductive::InductiveVal;

    let mut env = Environment::new();
    let gen_before = env.generation;

    let ind_name = Name::from_string("MyInd");
    let ind_val = InductiveVal {
        name: ind_name.clone(),
        level_params: vec![],
        type_: Expr::type_(), // Type 0
        num_params: 0,
        num_indices: 0,
        all_names: vec![ind_name.clone()],
        constructor_names: vec![],
        is_recursive: false,
        is_reflexive: false,
        is_large_elim: true,
        is_nested: false,
    };

    env.register_inductive_unchecked(ind_val);

    // Must appear in constants map
    let const_info = env.constants.get(&ind_name);
    assert!(
        const_info.is_some(),
        "register_inductive_unchecked must add to constants"
    );
    assert_eq!(const_info.unwrap().type_, Expr::type_());

    // Must appear in inductives map
    let ind_info = env.get_inductive(&ind_name);
    assert!(
        ind_info.is_some(),
        "register_inductive_unchecked must add to inductives"
    );
    assert_eq!(ind_info.unwrap().num_params, 0);

    // Must bump generation
    assert!(
        env.generation > gen_before,
        "register_inductive_unchecked must bump generation"
    );
}

/// Test extend_constants_unchecked: bulk inserts multiple constants and bumps generation.
/// Previously only used as test setup but never tested for its own behavior.
#[test]
fn test_extend_constants_unchecked_bulk_insert() {
    let mut env = Environment::new();
    let gen_before = env.generation;

    let names: Vec<Name> = (0..5)
        .map(|i| Name::from_string(&format!("c{i}")))
        .collect();

    let constants = names
        .iter()
        .map(|n| ConstantInfo::new(n.clone(), vec![], Expr::type_(), None, false));

    env.extend_constants_unchecked(constants);

    // All 5 must be present
    for name in &names {
        assert!(
            env.constants.get(name).is_some(),
            "extend_constants_unchecked must insert constant {name:?}"
        );
    }

    // Generation bumped exactly once (single extend call)
    assert!(
        env.generation > gen_before,
        "extend_constants_unchecked must bump generation"
    );
}

/// Test extend_inductives_unchecked: bulk inserts into both constants and inductives maps.
#[test]
fn test_extend_inductives_unchecked_bulk_insert() {
    use crate::inductive::InductiveVal;

    let mut env = Environment::new();
    let gen_before = env.generation;

    let ind_names: Vec<Name> = (0..3)
        .map(|i| Name::from_string(&format!("Ind{i}")))
        .collect();

    let inductives = ind_names.iter().map(|n| InductiveVal {
        name: n.clone(),
        level_params: vec![],
        type_: Expr::type_(),
        num_params: 0,
        num_indices: 0,
        all_names: vec![n.clone()],
        constructor_names: vec![],
        is_recursive: false,
        is_reflexive: false,
        is_large_elim: true,
        is_nested: false,
    });

    env.extend_inductives_unchecked(inductives);

    // All 3 must be in both maps
    for name in &ind_names {
        assert!(
            env.constants.get(name).is_some(),
            "extend_inductives_unchecked must add {name:?} to constants"
        );
        assert!(
            env.get_inductive(name).is_some(),
            "extend_inductives_unchecked must add {name:?} to inductives"
        );
    }

    assert!(
        env.generation > gen_before,
        "extend_inductives_unchecked must bump generation"
    );
}

/// Test extend_constructors_unchecked: bulk inserts into both constants and constructors maps.
#[test]
fn test_extend_constructors_unchecked_bulk_insert() {
    use crate::inductive::ConstructorVal;

    let mut env = Environment::new();
    let gen_before = env.generation;

    let ind_name = Name::from_string("TestInd");
    let ctor_names: Vec<Name> = (0..2)
        .map(|i| Name::from_string(&format!("TestInd.ctor{i}")))
        .collect();

    let constructors = ctor_names.iter().enumerate().map(|(i, n)| ConstructorVal {
        name: n.clone(),
        inductive_name: ind_name.clone(),
        level_params: vec![],
        type_: Expr::type_(),
        num_params: 0,
        num_fields: 0,
        constructor_idx: i as u32,
    });

    env.extend_constructors_unchecked(constructors);

    for name in &ctor_names {
        assert!(
            env.constants.get(name).is_some(),
            "extend_constructors_unchecked must add {name:?} to constants"
        );
        assert!(
            env.get_constructor(name).is_some(),
            "extend_constructors_unchecked must add {name:?} to constructors"
        );
    }

    assert!(
        env.generation > gen_before,
        "extend_constructors_unchecked must bump generation"
    );
}

/// Test register_constructor_unchecked: inserts into both maps without duplicate check.
#[test]
fn test_register_constructor_unchecked_inserts() {
    use crate::inductive::ConstructorVal;

    let mut env = Environment::new();
    let gen_before = env.generation;

    let ctor_name = Name::from_string("MyType.mk");
    let ctor_val = ConstructorVal {
        name: ctor_name.clone(),
        inductive_name: Name::from_string("MyType"),
        level_params: vec![],
        type_: Expr::type_(),
        num_params: 0,
        num_fields: 1,
        constructor_idx: 0,
    };

    env.register_constructor_unchecked(ctor_val);

    assert!(
        env.constants.get(&ctor_name).is_some(),
        "register_constructor_unchecked must add to constants"
    );
    assert!(
        env.get_constructor(&ctor_name).is_some(),
        "register_constructor_unchecked must add to constructors"
    );
    assert!(
        env.generation > gen_before,
        "register_constructor_unchecked must bump generation"
    );
}

// ====================================================================
// Tests for register_recursor_unchecked and extend_recursors_unchecked
// (Part of #1357 — previously zero coverage)
// ====================================================================

/// Test register_recursor_unchecked: inserts into both constants and recursors maps,
/// and bumps generation.
#[test]
fn test_register_recursor_unchecked_inserts_and_bumps_generation() {
    use crate::inductive::RecursorArgOrder;
    use crate::inductive::RecursorVal;

    let mut env = Environment::new();
    let gen_before = env.generation;

    let rec_name = Name::from_string("MyInd.rec");
    let rec_val = RecursorVal {
        name: rec_name.clone(),
        arg_order: RecursorArgOrder::MajorAfterMinors,
        level_params: vec![],
        type_: Expr::type_(),
        inductive_name: Name::from_string("MyInd"),
        num_params: 0,
        num_indices: 0,
        num_motives: 1,
        num_minors: 0,
        rules: vec![],
        is_k: false,
    };

    env.register_recursor_unchecked(rec_val);

    // Must appear in constants map
    let const_info = env.constants.get(&rec_name);
    assert!(
        const_info.is_some(),
        "register_recursor_unchecked must add to constants"
    );
    assert_eq!(const_info.unwrap().type_, Expr::type_());
    assert!(
        const_info.unwrap().value.is_none(),
        "recursor constant should have no value"
    );

    // Must appear in recursors map
    let rec_info = env.get_recursor(&rec_name);
    assert!(
        rec_info.is_some(),
        "register_recursor_unchecked must add to recursors"
    );
    assert_eq!(rec_info.unwrap().num_motives, 1);
    assert_eq!(rec_info.unwrap().inductive_name, Name::from_string("MyInd"));

    // Must bump generation
    assert!(
        env.generation > gen_before,
        "register_recursor_unchecked must bump generation"
    );
}

/// Test extend_recursors_unchecked: bulk inserts into both constants and recursors maps.
#[test]
fn test_extend_recursors_unchecked_bulk_insert() {
    use crate::inductive::RecursorArgOrder;
    use crate::inductive::RecursorVal;

    let mut env = Environment::new();
    let gen_before = env.generation;

    let rec_names: Vec<Name> = (0..3)
        .map(|i| Name::from_string(&format!("Ind{i}.rec")))
        .collect();

    let recursors = rec_names.iter().enumerate().map(|(i, n)| RecursorVal {
        name: n.clone(),
        arg_order: RecursorArgOrder::MajorAfterMinors,
        level_params: vec![],
        type_: Expr::type_(),
        inductive_name: Name::from_string(&format!("Ind{i}")),
        num_params: 0,
        num_indices: 0,
        num_motives: 1,
        num_minors: i as u32,
        rules: vec![],
        is_k: false,
    });

    env.extend_recursors_unchecked(recursors);

    // All 3 must be in both maps
    for (i, name) in rec_names.iter().enumerate() {
        assert!(
            env.constants.get(name).is_some(),
            "extend_recursors_unchecked must add {name:?} to constants"
        );
        let rec = env.get_recursor(name);
        assert!(
            rec.is_some(),
            "extend_recursors_unchecked must add {name:?} to recursors"
        );
        assert_eq!(rec.unwrap().num_minors, i as u32);
    }

    assert!(
        env.generation > gen_before,
        "extend_recursors_unchecked must bump generation"
    );
}

#[cfg(debug_assertions)]
fn test_inductive(name: &str) -> InductiveVal {
    InductiveVal {
        name: Name::from_string(name),
        level_params: vec![],
        type_: Expr::type_(),
        num_params: 0,
        num_indices: 0,
        all_names: vec![Name::from_string(name)],
        constructor_names: vec![],
        is_recursive: false,
        is_reflexive: false,
        is_large_elim: true,
        is_nested: false,
    }
}

#[cfg(debug_assertions)]
fn test_constructor(name: &str, ind_name: &str, constructor_idx: u32) -> ConstructorVal {
    ConstructorVal {
        name: Name::from_string(name),
        inductive_name: Name::from_string(ind_name),
        level_params: vec![],
        type_: Expr::type_(),
        num_params: 0,
        num_fields: 0,
        constructor_idx,
    }
}

#[cfg(debug_assertions)]
fn test_recursor(name: &str, ind_name: &str) -> RecursorVal {
    RecursorVal {
        name: Name::from_string(name),
        arg_order: crate::inductive::RecursorArgOrder::MajorAfterMinors,
        level_params: vec![],
        type_: Expr::type_(),
        inductive_name: Name::from_string(ind_name),
        num_params: 0,
        num_indices: 0,
        num_motives: 1,
        num_minors: 0,
        rules: vec![],
        is_k: false,
    }
}

#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "register_inductive_unchecked duplicate constant")]
fn test_register_inductive_unchecked_duplicate_panics_in_debug() {
    let mut env = Environment::new();
    env.register_inductive_unchecked(test_inductive("DupInd"));
    env.register_inductive_unchecked(test_inductive("DupInd"));
}

#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "register_constructor_unchecked duplicate constant")]
fn test_register_constructor_unchecked_duplicate_panics_in_debug() {
    let mut env = Environment::new();
    env.register_constructor_unchecked(test_constructor("DupCtor", "DupInd", 0));
    env.register_constructor_unchecked(test_constructor("DupCtor", "DupInd", 0));
}

#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "register_recursor_unchecked duplicate constant")]
fn test_register_recursor_unchecked_duplicate_panics_in_debug() {
    let mut env = Environment::new();
    env.register_recursor_unchecked(test_recursor("DupInd.rec", "DupInd"));
    env.register_recursor_unchecked(test_recursor("DupInd.rec", "DupInd"));
}

#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "insert_constants_raw duplicate constant")]
fn test_extend_constants_unchecked_existing_duplicate_panics_in_debug() {
    let mut env = Environment::new();
    let duplicate = Name::from_string("dup_const");
    env.extend_constants_unchecked(
        [ConstantInfo::new(
            duplicate.clone(),
            vec![],
            Expr::type_(),
            None,
            false,
        )]
        .into_iter(),
    );
    env.extend_constants_unchecked(
        [ConstantInfo::new(
            duplicate,
            vec![],
            Expr::type_(),
            None,
            false,
        )]
        .into_iter(),
    );
}

#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "insert_constants_raw duplicate constant in batch")]
fn test_extend_constants_unchecked_batch_duplicate_panics_in_debug() {
    let mut env = Environment::new();
    let duplicate = Name::from_string("dup_batch_const");
    env.extend_constants_unchecked(
        [
            ConstantInfo::new(duplicate.clone(), vec![], Expr::type_(), None, false),
            ConstantInfo::new(duplicate, vec![], Expr::type_(), None, false),
        ]
        .into_iter(),
    );
}

#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "extend_inductives_unchecked duplicate constant")]
fn test_extend_inductives_unchecked_existing_duplicate_panics_in_debug() {
    let mut env = Environment::new();
    env.register_inductive_unchecked(test_inductive("DupInd"));
    env.extend_inductives_unchecked([test_inductive("DupInd")].into_iter());
}

#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "extend_inductives_unchecked duplicate inductive in batch")]
fn test_extend_inductives_unchecked_batch_duplicate_panics_in_debug() {
    let mut env = Environment::new();
    env.extend_inductives_unchecked(
        [test_inductive("DupInd"), test_inductive("DupInd")].into_iter(),
    );
}

#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "extend_constructors_unchecked duplicate constant")]
fn test_extend_constructors_unchecked_existing_duplicate_panics_in_debug() {
    let mut env = Environment::new();
    env.register_constructor_unchecked(test_constructor("DupCtor", "DupInd", 0));
    env.extend_constructors_unchecked([test_constructor("DupCtor", "DupInd", 0)].into_iter());
}

#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "extend_constructors_unchecked duplicate constructor in batch")]
fn test_extend_constructors_unchecked_batch_duplicate_panics_in_debug() {
    let mut env = Environment::new();
    env.extend_constructors_unchecked(
        [
            test_constructor("DupCtor", "DupInd", 0),
            test_constructor("DupCtor", "DupInd", 1),
        ]
        .into_iter(),
    );
}

#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "extend_recursors_unchecked duplicate constant")]
fn test_extend_recursors_unchecked_existing_duplicate_panics_in_debug() {
    let mut env = Environment::new();
    env.register_recursor_unchecked(test_recursor("DupInd.rec", "DupInd"));
    env.extend_recursors_unchecked([test_recursor("DupInd.rec", "DupInd")].into_iter());
}

#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "extend_recursors_unchecked duplicate recursor in batch")]
fn test_extend_recursors_unchecked_batch_duplicate_panics_in_debug() {
    let mut env = Environment::new();
    env.extend_recursors_unchecked(
        [
            test_recursor("DupInd.rec", "DupInd"),
            test_recursor("DupInd.rec", "DupInd"),
        ]
        .into_iter(),
    );
}

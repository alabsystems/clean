// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the user-extensible elaboration hook system.

use super::*;
use std::sync::Arc;

// ============================================================================
// Registry construction and basic operations
// ============================================================================

#[test]
fn test_elab_hooks_new_registry_is_empty() {
    let registry = ElabHookRegistry::new();
    assert_eq!(registry.hook_count(), 0);
    for phase in ElabPhase::ALL {
        assert!(!registry.has_hooks(phase));
        assert!(registry.hooks_for_phase(phase).is_empty());
    }
}

#[test]
fn test_elab_hooks_default_trait_same_as_new() {
    let registry = ElabHookRegistry::default();
    assert_eq!(registry.hook_count(), 0);
}

#[test]
fn test_elab_hooks_register_and_lookup() {
    let mut registry = ElabHookRegistry::new();
    registry.register(ElabHookEntry {
        name: "test_hook".to_owned(),
        phase: ElabPhase::PreElaborate,
        priority: 100,
        hook: Arc::new(|_ctx| ElabHookResult::Continue),
    });

    assert!(registry.has_hooks(&ElabPhase::PreElaborate));
    assert_eq!(registry.hook_count(), 1);
    let hooks = registry.hooks_for_phase(&ElabPhase::PreElaborate);
    assert_eq!(hooks.len(), 1);
    assert_eq!(hooks[0].name, "test_hook");
    assert_eq!(hooks[0].priority, 100);
}

#[test]
fn test_elab_hooks_register_no_effect_on_other_phases() {
    let mut registry = ElabHookRegistry::new();
    registry.register(ElabHookEntry {
        name: "pre_hook".to_owned(),
        phase: ElabPhase::PreElaborate,
        priority: 100,
        hook: Arc::new(|_ctx| ElabHookResult::Continue),
    });

    assert!(!registry.has_hooks(&ElabPhase::PostElaborate));
    assert!(!registry.has_hooks(&ElabPhase::PreTypeCheck));
    assert!(!registry.has_hooks(&ElabPhase::PostTypeCheck));
    assert!(!registry.has_hooks(&ElabPhase::OnError));
}

// ============================================================================
// Priority ordering
// ============================================================================

#[test]
fn test_elab_hooks_priority_ordering_ascending() {
    let mut registry = ElabHookRegistry::new();

    // Register in non-sorted order
    registry.register(ElabHookEntry {
        name: "high".to_owned(),
        phase: ElabPhase::PreElaborate,
        priority: 300,
        hook: Arc::new(|_ctx| ElabHookResult::Continue),
    });
    registry.register(ElabHookEntry {
        name: "low".to_owned(),
        phase: ElabPhase::PreElaborate,
        priority: 100,
        hook: Arc::new(|_ctx| ElabHookResult::Continue),
    });
    registry.register(ElabHookEntry {
        name: "medium".to_owned(),
        phase: ElabPhase::PreElaborate,
        priority: 200,
        hook: Arc::new(|_ctx| ElabHookResult::Continue),
    });

    let hooks = registry.hooks_for_phase(&ElabPhase::PreElaborate);
    assert_eq!(hooks.len(), 3);
    assert_eq!(hooks[0].name, "low");
    assert_eq!(hooks[0].priority, 100);
    assert_eq!(hooks[1].name, "medium");
    assert_eq!(hooks[1].priority, 200);
    assert_eq!(hooks[2].name, "high");
    assert_eq!(hooks[2].priority, 300);
}

#[test]
fn test_elab_hooks_same_priority_stable_order() {
    let mut registry = ElabHookRegistry::new();

    registry.register(ElabHookEntry {
        name: "first".to_owned(),
        phase: ElabPhase::PostElaborate,
        priority: 100,
        hook: Arc::new(|_ctx| ElabHookResult::Continue),
    });
    registry.register(ElabHookEntry {
        name: "second".to_owned(),
        phase: ElabPhase::PostElaborate,
        priority: 100,
        hook: Arc::new(|_ctx| ElabHookResult::Continue),
    });

    let hooks = registry.hooks_for_phase(&ElabPhase::PostElaborate);
    assert_eq!(hooks.len(), 2);
    assert_eq!(
        hooks[0].name, "first",
        "insertion order preserved for equal priority"
    );
    assert_eq!(hooks[1].name, "second");
}

// ============================================================================
// run_hooks — Continue result
// ============================================================================

#[test]
fn test_elab_hooks_run_empty_phase_returns_continue() {
    let registry = ElabHookRegistry::new();
    let ctx = ElabHookContext::new(ElabPhase::PreElaborate);
    let result = registry.run_hooks(ElabPhase::PreElaborate, &ctx);
    assert!(matches!(result, ElabHookResult::Continue));
}

#[test]
fn test_elab_hooks_run_all_continue() {
    let mut registry = ElabHookRegistry::new();
    registry.register(ElabHookEntry {
        name: "a".to_owned(),
        phase: ElabPhase::PreElaborate,
        priority: 100,
        hook: Arc::new(|_ctx| ElabHookResult::Continue),
    });
    registry.register(ElabHookEntry {
        name: "b".to_owned(),
        phase: ElabPhase::PreElaborate,
        priority: 200,
        hook: Arc::new(|_ctx| ElabHookResult::Continue),
    });

    let ctx = ElabHookContext::new(ElabPhase::PreElaborate);
    let result = registry.run_hooks(ElabPhase::PreElaborate, &ctx);
    assert!(matches!(result, ElabHookResult::Continue));
}

// ============================================================================
// run_hooks — Replace result
// ============================================================================

#[test]
fn test_elab_hooks_run_replace_stops_processing() {
    let mut registry = ElabHookRegistry::new();

    // First hook replaces
    registry.register(ElabHookEntry {
        name: "replacer".to_owned(),
        phase: ElabPhase::PostElaborate,
        priority: 100,
        hook: Arc::new(|_ctx| ElabHookResult::Replace(Expr::prop())),
    });

    // Second hook should never fire (it would error)
    registry.register(ElabHookEntry {
        name: "should_not_run".to_owned(),
        phase: ElabPhase::PostElaborate,
        priority: 200,
        hook: Arc::new(|_ctx| ElabHookResult::Error("should not reach here".to_owned())),
    });

    let ctx = ElabHookContext::new(ElabPhase::PostElaborate);
    let result = registry.run_hooks(ElabPhase::PostElaborate, &ctx);
    match result {
        ElabHookResult::Replace(expr) => {
            assert_eq!(format!("{expr:?}"), format!("{:?}", Expr::prop()));
        }
        other => panic!("expected Replace, got {other:?}"),
    }
}

// ============================================================================
// run_hooks — Error result
// ============================================================================

#[test]
fn test_elab_hooks_run_error_stops_processing() {
    let mut registry = ElabHookRegistry::new();

    registry.register(ElabHookEntry {
        name: "erroring".to_owned(),
        phase: ElabPhase::PreTypeCheck,
        priority: 100,
        hook: Arc::new(|_ctx| ElabHookResult::Error("validation failed".to_owned())),
    });

    registry.register(ElabHookEntry {
        name: "should_not_run".to_owned(),
        phase: ElabPhase::PreTypeCheck,
        priority: 200,
        hook: Arc::new(|_ctx| ElabHookResult::Continue),
    });

    let ctx = ElabHookContext::new(ElabPhase::PreTypeCheck);
    let result = registry.run_hooks(ElabPhase::PreTypeCheck, &ctx);
    match result {
        ElabHookResult::Error(msg) => {
            assert_eq!(msg, "validation failed");
        }
        other => panic!("expected Error, got {other:?}"),
    }
}

// ============================================================================
// run_hooks — Skip result
// ============================================================================

#[test]
fn test_elab_hooks_run_skip_stops_and_returns_continue() {
    let mut registry = ElabHookRegistry::new();

    registry.register(ElabHookEntry {
        name: "skipper".to_owned(),
        phase: ElabPhase::PostTypeCheck,
        priority: 100,
        hook: Arc::new(|_ctx| ElabHookResult::Skip),
    });

    // This error hook should never fire because skip stops processing
    registry.register(ElabHookEntry {
        name: "should_not_run".to_owned(),
        phase: ElabPhase::PostTypeCheck,
        priority: 200,
        hook: Arc::new(|_ctx| ElabHookResult::Error("should not reach here".to_owned())),
    });

    let ctx = ElabHookContext::new(ElabPhase::PostTypeCheck);
    let result = registry.run_hooks(ElabPhase::PostTypeCheck, &ctx);
    // Skip converts to Continue
    assert!(
        matches!(result, ElabHookResult::Continue),
        "Skip should produce Continue as overall result"
    );
}

// ============================================================================
// Multiple phases
// ============================================================================

#[test]
fn test_elab_hooks_multiple_phases_independent() {
    let mut registry = ElabHookRegistry::new();

    registry.register(ElabHookEntry {
        name: "pre_hook".to_owned(),
        phase: ElabPhase::PreElaborate,
        priority: 100,
        hook: Arc::new(|_ctx| ElabHookResult::Continue),
    });
    registry.register(ElabHookEntry {
        name: "post_hook".to_owned(),
        phase: ElabPhase::PostElaborate,
        priority: 100,
        hook: Arc::new(|_ctx| ElabHookResult::Replace(Expr::type_())),
    });
    registry.register(ElabHookEntry {
        name: "error_hook".to_owned(),
        phase: ElabPhase::OnError,
        priority: 50,
        hook: Arc::new(|_ctx| ElabHookResult::Continue),
    });

    assert_eq!(registry.hook_count(), 3);
    assert!(registry.has_hooks(&ElabPhase::PreElaborate));
    assert!(registry.has_hooks(&ElabPhase::PostElaborate));
    assert!(registry.has_hooks(&ElabPhase::OnError));
    assert!(!registry.has_hooks(&ElabPhase::PreTypeCheck));
    assert!(!registry.has_hooks(&ElabPhase::PostTypeCheck));

    // PreElaborate returns Continue
    let ctx = ElabHookContext::new(ElabPhase::PreElaborate);
    assert!(matches!(
        registry.run_hooks(ElabPhase::PreElaborate, &ctx),
        ElabHookResult::Continue
    ));

    // PostElaborate returns Replace
    let ctx = ElabHookContext::new(ElabPhase::PostElaborate);
    assert!(matches!(
        registry.run_hooks(ElabPhase::PostElaborate, &ctx),
        ElabHookResult::Replace(_)
    ));
}

// ============================================================================
// Remove hook by name
// ============================================================================

#[test]
fn test_elab_hooks_remove_existing() {
    let mut registry = ElabHookRegistry::new();
    registry.register(ElabHookEntry {
        name: "removable".to_owned(),
        phase: ElabPhase::PreElaborate,
        priority: 100,
        hook: Arc::new(|_ctx| ElabHookResult::Continue),
    });

    assert_eq!(registry.hook_count(), 1);
    assert!(registry.remove("removable"));
    assert_eq!(registry.hook_count(), 0);
    assert!(!registry.has_hooks(&ElabPhase::PreElaborate));
}

#[test]
fn test_elab_hooks_remove_nonexistent_returns_false() {
    let mut registry = ElabHookRegistry::new();
    assert!(!registry.remove("nonexistent"));
}

#[test]
fn test_elab_hooks_remove_preserves_other_hooks() {
    let mut registry = ElabHookRegistry::new();
    registry.register(ElabHookEntry {
        name: "keep".to_owned(),
        phase: ElabPhase::PreElaborate,
        priority: 100,
        hook: Arc::new(|_ctx| ElabHookResult::Continue),
    });
    registry.register(ElabHookEntry {
        name: "remove_me".to_owned(),
        phase: ElabPhase::PreElaborate,
        priority: 200,
        hook: Arc::new(|_ctx| ElabHookResult::Continue),
    });

    assert!(registry.remove("remove_me"));
    assert_eq!(registry.hook_count(), 1);
    let hooks = registry.hooks_for_phase(&ElabPhase::PreElaborate);
    assert_eq!(hooks.len(), 1);
    assert_eq!(hooks[0].name, "keep");
}

// ============================================================================
// Clear all hooks
// ============================================================================

#[test]
fn test_elab_hooks_clear() {
    let mut registry = ElabHookRegistry::new();

    for (i, phase) in ElabPhase::ALL.iter().enumerate() {
        registry.register(ElabHookEntry {
            name: format!("hook_{i}"),
            phase: *phase,
            priority: 100,
            hook: Arc::new(|_ctx| ElabHookResult::Continue),
        });
    }

    assert_eq!(registry.hook_count(), 5);
    registry.clear();
    assert_eq!(registry.hook_count(), 0);

    for phase in ElabPhase::ALL {
        assert!(!registry.has_hooks(phase));
    }
}

// ============================================================================
// Hook context construction
// ============================================================================

#[test]
fn test_elab_hooks_context_minimal() {
    let ctx = ElabHookContext::new(ElabPhase::PreElaborate);
    assert_eq!(ctx.phase, ElabPhase::PreElaborate);
    assert!(ctx.expr.is_none());
    assert!(ctx.expected_type.is_none());
    assert!(ctx.decl_name.is_none());
    assert!(ctx.source_span.is_none());
}

#[test]
fn test_elab_hooks_context_builder_chain() {
    let ctx = ElabHookContext::new(ElabPhase::PostElaborate)
        .with_expr(Expr::type_())
        .with_expected_type(Expr::prop())
        .with_decl_name("my_theorem")
        .with_source_span(10, 42);

    assert_eq!(ctx.phase, ElabPhase::PostElaborate);
    assert!(ctx.expr.is_some());
    assert!(ctx.expected_type.is_some());
    assert_eq!(ctx.decl_name.as_deref(), Some("my_theorem"));
    assert_eq!(ctx.source_span, Some((10, 42)));
}

#[test]
fn test_elab_hooks_context_passed_to_hook() {
    let mut registry = ElabHookRegistry::new();

    // Hook that inspects context fields
    registry.register(ElabHookEntry {
        name: "inspector".to_owned(),
        phase: ElabPhase::PreElaborate,
        priority: 100,
        hook: Arc::new(|ctx| {
            if ctx.decl_name.as_deref() == Some("target") {
                ElabHookResult::Replace(Expr::prop())
            } else {
                ElabHookResult::Continue
            }
        }),
    });

    // Without matching name: Continue
    let ctx = ElabHookContext::new(ElabPhase::PreElaborate).with_decl_name("other");
    assert!(matches!(
        registry.run_hooks(ElabPhase::PreElaborate, &ctx),
        ElabHookResult::Continue
    ));

    // With matching name: Replace
    let ctx = ElabHookContext::new(ElabPhase::PreElaborate).with_decl_name("target");
    assert!(matches!(
        registry.run_hooks(ElabPhase::PreElaborate, &ctx),
        ElabHookResult::Replace(_)
    ));
}

// ============================================================================
// Multiple hooks same phase — execution order
// ============================================================================

#[test]
fn test_elab_hooks_multiple_same_phase_runs_in_order() {
    use std::sync::atomic::{AtomicU32, Ordering};

    let counter = Arc::new(AtomicU32::new(0));

    let mut registry = ElabHookRegistry::new();

    // Low priority (runs first): sets counter to 1
    let c = Arc::clone(&counter);
    registry.register(ElabHookEntry {
        name: "first".to_owned(),
        phase: ElabPhase::PreElaborate,
        priority: 100,
        hook: Arc::new(move |_ctx| {
            c.store(1, Ordering::SeqCst);
            ElabHookResult::Continue
        }),
    });

    // High priority (runs second): sets counter to 2
    let c = Arc::clone(&counter);
    registry.register(ElabHookEntry {
        name: "second".to_owned(),
        phase: ElabPhase::PreElaborate,
        priority: 200,
        hook: Arc::new(move |_ctx| {
            c.store(2, Ordering::SeqCst);
            ElabHookResult::Continue
        }),
    });

    let ctx = ElabHookContext::new(ElabPhase::PreElaborate);
    let result = registry.run_hooks(ElabPhase::PreElaborate, &ctx);
    assert!(matches!(result, ElabHookResult::Continue));

    // Counter should be 2 because the higher-priority hook ran last
    assert_eq!(counter.load(Ordering::SeqCst), 2);
}

// ============================================================================
// ElabPhase Display and equality
// ============================================================================

#[test]
fn test_elab_hooks_phase_display() {
    assert_eq!(ElabPhase::PreElaborate.to_string(), "PreElaborate");
    assert_eq!(ElabPhase::PostElaborate.to_string(), "PostElaborate");
    assert_eq!(ElabPhase::PreTypeCheck.to_string(), "PreTypeCheck");
    assert_eq!(ElabPhase::PostTypeCheck.to_string(), "PostTypeCheck");
    assert_eq!(ElabPhase::OnError.to_string(), "OnError");
}

#[test]
fn test_elab_hooks_phase_equality_and_hash() {
    use std::collections::HashSet;

    let mut set = HashSet::new();
    for phase in ElabPhase::ALL {
        assert!(set.insert(*phase), "each phase should be unique");
    }
    assert_eq!(set.len(), 5);

    // Same variant is equal
    assert_eq!(ElabPhase::PreElaborate, ElabPhase::PreElaborate);
    // Different variants are not equal
    assert_ne!(ElabPhase::PreElaborate, ElabPhase::PostElaborate);
}

// ============================================================================
// Debug formatting
// ============================================================================

#[test]
fn test_elab_hooks_entry_debug() {
    let entry = ElabHookEntry {
        name: "my_hook".to_owned(),
        phase: ElabPhase::OnError,
        priority: 42,
        hook: Arc::new(|_ctx| ElabHookResult::Continue),
    };
    let debug = format!("{entry:?}");
    assert!(debug.contains("my_hook"));
    assert!(debug.contains("42"));
    assert!(debug.contains("OnError"));
}

#[test]
fn test_elab_hooks_registry_debug() {
    let mut registry = ElabHookRegistry::new();
    registry.register(ElabHookEntry {
        name: "h".to_owned(),
        phase: ElabPhase::PreElaborate,
        priority: 1,
        hook: Arc::new(|_ctx| ElabHookResult::Continue),
    });
    let debug = format!("{registry:?}");
    assert!(debug.contains("ElabHookRegistry"));
    assert!(debug.contains("total_hooks"));
}

#[test]
fn test_elab_hooks_entry_clone() {
    let entry = ElabHookEntry {
        name: "cloneable".to_owned(),
        phase: ElabPhase::PreTypeCheck,
        priority: 50,
        hook: Arc::new(|_ctx| ElabHookResult::Continue),
    };
    let cloned = entry.clone();
    assert_eq!(cloned.name, "cloneable");
    assert_eq!(cloned.phase, ElabPhase::PreTypeCheck);
    assert_eq!(cloned.priority, 50);
}

// ============================================================================
// ElabHookResult variants
// ============================================================================

#[test]
fn test_elab_hooks_result_debug() {
    let continue_result = ElabHookResult::Continue;
    let replace_result = ElabHookResult::Replace(Expr::type_());
    let error_result = ElabHookResult::Error("oops".to_owned());
    let skip_result = ElabHookResult::Skip;

    assert!(format!("{continue_result:?}").contains("Continue"));
    assert!(format!("{replace_result:?}").contains("Replace"));
    assert!(format!("{error_result:?}").contains("oops"));
    assert!(format!("{skip_result:?}").contains("Skip"));
}

#[test]
fn test_elab_hooks_result_clone() {
    let original = ElabHookResult::Error("test".to_owned());
    let cloned = original.clone();
    match cloned {
        ElabHookResult::Error(msg) => assert_eq!(msg, "test"),
        other => panic!("expected Error, got {other:?}"),
    }
}

// ============================================================================
// ElabPhase::ALL coverage
// ============================================================================

#[test]
fn test_elab_hooks_phase_all_has_five_variants() {
    assert_eq!(ElabPhase::ALL.len(), 5);
}

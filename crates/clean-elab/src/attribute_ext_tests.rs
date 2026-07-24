// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the extended attribute elaboration module.

use clean_kernel::expr::{BinderInfo, Expr};
use clean_kernel::name::Name;

use crate::attribute_ext::{
    elaborate_attribute, validate_attribute_target, AttributeEntry, AttributeManager,
    ExtAttributeKind,
};

// ===========================================================================
// Helper
// ===========================================================================

fn mk_entry(kind: ExtAttributeKind, name: &str) -> AttributeEntry {
    AttributeEntry {
        kind,
        name: Name::from_string(name),
        added_in: None,
    }
}

fn mk_entry_ns(kind: ExtAttributeKind, name: &str, ns: &str) -> AttributeEntry {
    AttributeEntry {
        kind,
        name: Name::from_string(name),
        added_in: Some(Name::from_string(ns)),
    }
}

// ===========================================================================
// ExtAttributeKind tests
// ===========================================================================

#[test]
fn test_attribute_kind_name_all_variants() {
    assert_eq!(ExtAttributeKind::Simp.name(), "simp");
    assert_eq!(
        ExtAttributeKind::Instance { priority: None }.name(),
        "instance"
    );
    assert_eq!(
        ExtAttributeKind::Instance {
            priority: Some(500)
        }
        .name(),
        "instance"
    );
    assert_eq!(ExtAttributeKind::Reducible.name(), "reducible");
    assert_eq!(ExtAttributeKind::Irreducible.name(), "irreducible");
    assert_eq!(ExtAttributeKind::Inline { always: false }.name(), "inline");
    assert_eq!(
        ExtAttributeKind::Inline { always: true }.name(),
        "always_inline"
    );
    assert_eq!(ExtAttributeKind::NoInline.name(), "noinline");
    assert_eq!(
        ExtAttributeKind::Extern {
            abi: "lean_foo".to_owned()
        }
        .name(),
        "extern"
    );
    assert_eq!(ExtAttributeKind::Specialize.name(), "specialize");
    assert_eq!(ExtAttributeKind::NoSpecialize.name(), "nospecialize");
    assert_eq!(
        ExtAttributeKind::ImplementedBy {
            impl_name: "bar".to_owned()
        }
        .name(),
        "implementedBy"
    );
    assert_eq!(ExtAttributeKind::Macro.name(), "macro");
    assert_eq!(ExtAttributeKind::BuiltinInit.name(), "init");
    assert_eq!(
        ExtAttributeKind::Export {
            name: "c_fn".to_owned()
        }
        .name(),
        "export"
    );
    assert_eq!(ExtAttributeKind::Unfolding.name(), "unfolding");
    assert_eq!(ExtAttributeKind::Class.name(), "class");
    assert_eq!(ExtAttributeKind::Private.name(), "private");
    assert_eq!(ExtAttributeKind::Protected.name(), "protected");
    assert_eq!(ExtAttributeKind::Scoped.name(), "scoped");
}

#[test]
fn test_attribute_kind_same_kind_ignores_params() {
    let a = ExtAttributeKind::Instance { priority: None };
    let b = ExtAttributeKind::Instance {
        priority: Some(500),
    };
    assert!(a.same_kind(&b));
    assert!(b.same_kind(&a));
}

#[test]
fn test_attribute_kind_same_kind_different_variants() {
    assert!(!ExtAttributeKind::Simp.same_kind(&ExtAttributeKind::Reducible));
    assert!(!ExtAttributeKind::Inline { always: true }.same_kind(&ExtAttributeKind::NoInline));
}

#[test]
fn test_attribute_kind_equality_with_params() {
    assert_eq!(
        ExtAttributeKind::Instance {
            priority: Some(100)
        },
        ExtAttributeKind::Instance {
            priority: Some(100)
        }
    );
    assert_ne!(
        ExtAttributeKind::Instance {
            priority: Some(100)
        },
        ExtAttributeKind::Instance { priority: None }
    );
}

// ===========================================================================
// AttributeManager — registration and lookup
// ===========================================================================

#[test]
fn test_manager_new_is_empty() {
    let mgr = AttributeManager::new();
    assert_eq!(mgr.total_entries(), 0);
    assert_eq!(mgr.declaration_count(), 0);
}

#[test]
fn test_manager_register_single_attribute() {
    let mut mgr = AttributeManager::new();
    mgr.register_attribute(mk_entry(ExtAttributeKind::Simp, "my_lemma"))
        .expect("registration should succeed");
    assert_eq!(mgr.total_entries(), 1);
    assert_eq!(mgr.declaration_count(), 1);
}

#[test]
fn test_manager_register_multiple_different_attrs_same_decl() {
    let mut mgr = AttributeManager::new();
    mgr.register_attribute(mk_entry(ExtAttributeKind::Simp, "foo"))
        .expect("simp should succeed");
    mgr.register_attribute(mk_entry(ExtAttributeKind::Inline { always: false }, "foo"))
        .expect("inline should succeed");
    assert_eq!(mgr.total_entries(), 2);
    assert_eq!(mgr.declaration_count(), 1);
}

#[test]
fn test_manager_duplicate_attribute_error() {
    let mut mgr = AttributeManager::new();
    mgr.register_attribute(mk_entry(ExtAttributeKind::Simp, "my_lemma"))
        .expect("first registration should succeed");
    let result = mgr.register_attribute(mk_entry(ExtAttributeKind::Simp, "my_lemma"));
    assert!(result.is_err(), "duplicate simp on same decl should fail");
}

#[test]
fn test_manager_same_attr_different_decls_ok() {
    let mut mgr = AttributeManager::new();
    mgr.register_attribute(mk_entry(ExtAttributeKind::Simp, "lemma_a"))
        .expect("first should succeed");
    mgr.register_attribute(mk_entry(ExtAttributeKind::Simp, "lemma_b"))
        .expect("second should succeed");
    assert_eq!(mgr.declaration_count(), 2);
    assert_eq!(mgr.total_entries(), 2);
}

#[test]
fn test_manager_has_attribute() {
    let mut mgr = AttributeManager::new();
    let name = Name::from_string("decl");
    mgr.register_attribute(mk_entry(ExtAttributeKind::Reducible, "decl"))
        .expect("should succeed");
    assert!(mgr.has_attribute(&name, &ExtAttributeKind::Reducible));
    assert!(!mgr.has_attribute(&name, &ExtAttributeKind::Simp));
}

#[test]
fn test_manager_has_attribute_unknown_decl() {
    let mgr = AttributeManager::new();
    let name = Name::from_string("nonexistent");
    assert!(!mgr.has_attribute(&name, &ExtAttributeKind::Simp));
}

#[test]
fn test_manager_get_attributes_returns_all() {
    let mut mgr = AttributeManager::new();
    mgr.register_attribute(mk_entry(ExtAttributeKind::Simp, "foo"))
        .expect("should succeed");
    mgr.register_attribute(mk_entry(ExtAttributeKind::Reducible, "foo"))
        .expect("should succeed");
    mgr.register_attribute(mk_entry(ExtAttributeKind::Class, "foo"))
        .expect("should succeed");

    let attrs = mgr.get_attributes(&Name::from_string("foo"));
    assert_eq!(attrs.len(), 3);
}

#[test]
fn test_manager_get_attributes_empty_for_unknown() {
    let mgr = AttributeManager::new();
    let attrs = mgr.get_attributes(&Name::from_string("nonexistent"));
    assert!(attrs.is_empty());
}

// ===========================================================================
// Simp lemma collection
// ===========================================================================

#[test]
fn test_manager_get_simp_lemmas() {
    let mut mgr = AttributeManager::new();
    mgr.register_attribute(mk_entry(ExtAttributeKind::Simp, "simp_a"))
        .expect("should succeed");
    mgr.register_attribute(mk_entry(ExtAttributeKind::Simp, "simp_b"))
        .expect("should succeed");
    mgr.register_attribute(mk_entry(ExtAttributeKind::Reducible, "not_simp"))
        .expect("should succeed");

    let simps = mgr.get_simp_lemmas();
    assert_eq!(simps.len(), 2);
    let simp_strs: Vec<String> = simps.iter().map(|n| n.to_string()).collect();
    assert!(simp_strs.contains(&"simp_a".to_owned()));
    assert!(simp_strs.contains(&"simp_b".to_owned()));
}

#[test]
fn test_manager_get_simp_lemmas_empty() {
    let mgr = AttributeManager::new();
    assert!(mgr.get_simp_lemmas().is_empty());
}

// ===========================================================================
// Instance queries
// ===========================================================================

#[test]
fn test_manager_get_instances_with_priorities() {
    let mut mgr = AttributeManager::new();
    mgr.register_attribute(mk_entry(
        ExtAttributeKind::Instance {
            priority: Some(500),
        },
        "inst_high",
    ))
    .expect("should succeed");
    mgr.register_attribute(mk_entry(
        ExtAttributeKind::Instance {
            priority: Some(100),
        },
        "inst_normal",
    ))
    .expect("should succeed");
    mgr.register_attribute(mk_entry(
        ExtAttributeKind::Instance { priority: None },
        "inst_default",
    ))
    .expect("should succeed");

    let instances = mgr.get_instances();
    assert_eq!(instances.len(), 3);

    // Sorted by priority descending
    assert_eq!(instances[0].0.to_string(), "inst_high");
    assert_eq!(instances[0].1, 500);
    assert_eq!(instances[1].1, 100);
    // Default priority is 100
    assert_eq!(instances[2].1, 100);
}

#[test]
fn test_manager_get_instances_excludes_non_instances() {
    let mut mgr = AttributeManager::new();
    mgr.register_attribute(mk_entry(ExtAttributeKind::Simp, "lemma"))
        .expect("should succeed");
    mgr.register_attribute(mk_entry(
        ExtAttributeKind::Instance { priority: None },
        "inst",
    ))
    .expect("should succeed");

    let instances = mgr.get_instances();
    assert_eq!(instances.len(), 1);
    assert_eq!(instances[0].0.to_string(), "inst");
}

// ===========================================================================
// Reducibility and inline queries
// ===========================================================================

#[test]
fn test_manager_is_reducible() {
    let mut mgr = AttributeManager::new();
    mgr.register_attribute(mk_entry(ExtAttributeKind::Reducible, "my_def"))
        .expect("should succeed");
    assert!(mgr.is_reducible(&Name::from_string("my_def")));
    assert!(!mgr.is_reducible(&Name::from_string("other")));
}

#[test]
fn test_manager_is_irreducible() {
    let mut mgr = AttributeManager::new();
    mgr.register_attribute(mk_entry(ExtAttributeKind::Irreducible, "opaque_def"))
        .expect("should succeed");
    assert!(mgr.is_irreducible(&Name::from_string("opaque_def")));
    assert!(!mgr.is_irreducible(&Name::from_string("other")));
}

#[test]
fn test_manager_is_inline_regular() {
    let mut mgr = AttributeManager::new();
    mgr.register_attribute(mk_entry(
        ExtAttributeKind::Inline { always: false },
        "helper",
    ))
    .expect("should succeed");
    assert!(mgr.is_inline(&Name::from_string("helper")));
}

#[test]
fn test_manager_is_inline_always() {
    let mut mgr = AttributeManager::new();
    mgr.register_attribute(mk_entry(
        ExtAttributeKind::Inline { always: true },
        "hot_fn",
    ))
    .expect("should succeed");
    assert!(mgr.is_inline(&Name::from_string("hot_fn")));
}

#[test]
fn test_manager_is_class() {
    let mut mgr = AttributeManager::new();
    mgr.register_attribute(mk_entry(ExtAttributeKind::Class, "Monad"))
        .expect("should succeed");
    assert!(mgr.is_class(&Name::from_string("Monad")));
    assert!(!mgr.is_class(&Name::from_string("NotAClass")));
}

// ===========================================================================
// Namespace scoping
// ===========================================================================

#[test]
fn test_manager_namespace_filtering() {
    let mut mgr = AttributeManager::new();
    mgr.register_attribute(mk_entry_ns(ExtAttributeKind::Simp, "Nat.add_zero", "Nat"))
        .expect("should succeed");
    mgr.register_attribute(mk_entry(ExtAttributeKind::Reducible, "Nat.add_zero"))
        .expect("should succeed");

    let in_nat = mgr.get_attributes_in_namespace(
        &Name::from_string("Nat.add_zero"),
        &Name::from_string("Nat"),
    );
    assert_eq!(in_nat.len(), 1);
    assert!(matches!(in_nat[0].kind, ExtAttributeKind::Simp));

    let in_other = mgr.get_attributes_in_namespace(
        &Name::from_string("Nat.add_zero"),
        &Name::from_string("Int"),
    );
    assert!(in_other.is_empty());
}

#[test]
fn test_manager_namespace_filtering_no_attrs() {
    let mgr = AttributeManager::new();
    let attrs =
        mgr.get_attributes_in_namespace(&Name::from_string("no_such"), &Name::from_string("Ns"));
    assert!(attrs.is_empty());
}

// ===========================================================================
// elaborate_attribute
// ===========================================================================

#[test]
fn test_elaborate_attribute_simp() {
    let decl = Name::from_string("my_lemma");
    let entry = elaborate_attribute("simp", &decl, &[]).expect("should succeed");
    assert!(matches!(entry.kind, ExtAttributeKind::Simp));
    assert_eq!(entry.name.to_string(), "my_lemma");
    assert!(entry.added_in.is_none());
}

#[test]
fn test_elaborate_attribute_instance_no_priority() {
    let decl = Name::from_string("inst");
    let entry = elaborate_attribute("instance", &decl, &[]).expect("should succeed");
    assert!(matches!(
        entry.kind,
        ExtAttributeKind::Instance { priority: None }
    ));
}

#[test]
fn test_elaborate_attribute_instance_with_priority() {
    let decl = Name::from_string("inst");
    let entry = elaborate_attribute("instance", &decl, &["500"]).expect("should succeed");
    assert!(matches!(
        entry.kind,
        ExtAttributeKind::Instance {
            priority: Some(500)
        }
    ));
}

#[test]
fn test_elaborate_attribute_extern_with_abi() {
    let decl = Name::from_string("ffi_fn");
    let entry = elaborate_attribute("extern", &decl, &["lean_ffi_fn"]).expect("should succeed");
    if let ExtAttributeKind::Extern { abi } = &entry.kind {
        assert_eq!(abi, "lean_ffi_fn");
    } else {
        panic!("expected Extern variant");
    }
}

#[test]
fn test_elaborate_attribute_implemented_by() {
    let decl = Name::from_string("spec_fn");
    let entry = elaborate_attribute("implementedBy", &decl, &["fast_fn"]).expect("should succeed");
    if let ExtAttributeKind::ImplementedBy { impl_name } = &entry.kind {
        assert_eq!(impl_name, "fast_fn");
    } else {
        panic!("expected ImplementedBy variant");
    }
}

#[test]
fn test_elaborate_attribute_export_with_name() {
    let decl = Name::from_string("my_fn");
    let entry = elaborate_attribute("export", &decl, &["c_my_fn"]).expect("should succeed");
    if let ExtAttributeKind::Export { name } = &entry.kind {
        assert_eq!(name, "c_my_fn");
    } else {
        panic!("expected Export variant");
    }
}

#[test]
fn test_elaborate_attribute_all_simple_kinds() {
    let decl = Name::from_string("test_decl");
    let simple_attrs = [
        "reducible",
        "irreducible",
        "inline",
        "always_inline",
        "noinline",
        "specialize",
        "nospecialize",
        "macro",
        "init",
        "unfolding",
        "class",
        "private",
        "protected",
        "scoped",
    ];
    for attr_name in &simple_attrs {
        let entry = elaborate_attribute(attr_name, &decl, &[])
            .unwrap_or_else(|_| panic!("should succeed for @[{attr_name}]"));
        assert_eq!(entry.kind.name(), *attr_name);
    }
}

#[test]
fn test_elaborate_attribute_unknown_error() {
    let decl = Name::from_string("test_decl");
    let result = elaborate_attribute("nonexistent_attr", &decl, &[]);
    assert!(result.is_err());
}

// ===========================================================================
// validate_attribute_target
// ===========================================================================

#[test]
fn test_validate_simp_target_pi_ok() {
    // Pi type: forall (x : Nat), Prop
    let pi = Expr::pi(
        BinderInfo::Default,
        Expr::const_str("Nat"),
        Expr::const_str("Prop"),
    );
    validate_attribute_target(&ExtAttributeKind::Simp, &pi)
        .expect("simp on pi type should succeed");
}

#[test]
fn test_validate_simp_target_const_ok() {
    let c = Expr::const_str("Eq.refl");
    validate_attribute_target(&ExtAttributeKind::Simp, &c).expect("simp on const should succeed");
}

#[test]
fn test_validate_simp_target_bvar_fails() {
    let bv = Expr::bvar(0);
    let result = validate_attribute_target(&ExtAttributeKind::Simp, &bv);
    assert!(result.is_err(), "simp on bare bvar should fail");
}

#[test]
fn test_validate_instance_target_app_ok() {
    let app = Expr::app(Expr::const_str("Monad"), Expr::const_str("IO"));
    validate_attribute_target(&ExtAttributeKind::Instance { priority: None }, &app)
        .expect("instance on app should succeed");
}

#[test]
fn test_validate_instance_target_bvar_fails() {
    let bv = Expr::bvar(0);
    let result = validate_attribute_target(&ExtAttributeKind::Instance { priority: None }, &bv);
    assert!(result.is_err(), "instance on bare bvar should fail");
}

#[test]
fn test_validate_extern_target_pi_ok() {
    let pi = Expr::pi(
        BinderInfo::Default,
        Expr::const_str("Nat"),
        Expr::const_str("Nat"),
    );
    validate_attribute_target(
        &ExtAttributeKind::Extern {
            abi: "lean_fn".to_owned(),
        },
        &pi,
    )
    .expect("extern on pi should succeed");
}

#[test]
fn test_validate_implemented_by_target_lam_fails() {
    let lam = Expr::lam(BinderInfo::Default, Expr::const_str("Nat"), Expr::bvar(0));
    let result = validate_attribute_target(
        &ExtAttributeKind::ImplementedBy {
            impl_name: "fast".to_owned(),
        },
        &lam,
    );
    assert!(result.is_err(), "implementedBy on bare lambda should fail");
}

#[test]
fn test_validate_reducible_accepts_anything() {
    let bv = Expr::bvar(0);
    validate_attribute_target(&ExtAttributeKind::Reducible, &bv)
        .expect("reducible should accept any expression");
}

#[test]
fn test_validate_class_accepts_anything() {
    let bv = Expr::bvar(0);
    validate_attribute_target(&ExtAttributeKind::Class, &bv)
        .expect("class should accept any expression");
}

#[test]
fn test_validate_private_accepts_anything() {
    let bv = Expr::bvar(42);
    validate_attribute_target(&ExtAttributeKind::Private, &bv)
        .expect("private should accept any expression");
}

// ===========================================================================
// Edge cases
// ===========================================================================

#[test]
fn test_manager_register_all_18_kinds() {
    let mut mgr = AttributeManager::new();
    let kinds: Vec<ExtAttributeKind> = vec![
        ExtAttributeKind::Simp,
        ExtAttributeKind::Instance { priority: None },
        ExtAttributeKind::Reducible,
        ExtAttributeKind::Irreducible,
        ExtAttributeKind::Inline { always: false },
        ExtAttributeKind::NoInline,
        ExtAttributeKind::Extern {
            abi: "c".to_owned(),
        },
        ExtAttributeKind::Specialize,
        ExtAttributeKind::NoSpecialize,
        ExtAttributeKind::ImplementedBy {
            impl_name: "fast".to_owned(),
        },
        ExtAttributeKind::Macro,
        ExtAttributeKind::BuiltinInit,
        ExtAttributeKind::Export {
            name: "c_fn".to_owned(),
        },
        ExtAttributeKind::Unfolding,
        ExtAttributeKind::Class,
        ExtAttributeKind::Private,
        ExtAttributeKind::Protected,
        ExtAttributeKind::Scoped,
    ];
    for kind in &kinds {
        mgr.register_attribute(AttributeEntry {
            kind: kind.clone(),
            name: Name::from_string("universal_decl"),
            added_in: None,
        })
        .unwrap_or_else(|e| panic!("registration of {} should succeed: {e}", kind.name()));
    }
    assert_eq!(mgr.total_entries(), 18);
    assert_eq!(mgr.declaration_count(), 1);
}

#[test]
fn test_manager_duplicate_instance_same_kind_different_priority() {
    let mut mgr = AttributeManager::new();
    mgr.register_attribute(mk_entry(
        ExtAttributeKind::Instance {
            priority: Some(100),
        },
        "inst",
    ))
    .expect("first should succeed");
    // same_kind compares discriminant, so Instance{100} and Instance{500} collide
    let result = mgr.register_attribute(mk_entry(
        ExtAttributeKind::Instance {
            priority: Some(500),
        },
        "inst",
    ));
    assert!(result.is_err(), "duplicate instance kind should fail");
}

#[test]
fn test_manager_inline_and_noinline_are_different_kinds() {
    let mut mgr = AttributeManager::new();
    mgr.register_attribute(mk_entry(ExtAttributeKind::Inline { always: false }, "fn"))
        .expect("inline should succeed");
    // NoInline is a different discriminant from Inline
    mgr.register_attribute(mk_entry(ExtAttributeKind::NoInline, "fn"))
        .expect("noinline should succeed (different kind)");
    assert_eq!(mgr.total_entries(), 2);
}

#[test]
fn test_elaborate_attribute_instance_invalid_priority_string() {
    let decl = Name::from_string("inst");
    let entry = elaborate_attribute("instance", &decl, &["not_a_number"]).expect("should succeed");
    // Invalid priority string should parse as None
    assert!(matches!(
        entry.kind,
        ExtAttributeKind::Instance { priority: None }
    ));
}

#[test]
fn test_attribute_entry_clone() {
    let entry = mk_entry(ExtAttributeKind::Simp, "lemma");
    let cloned = entry.clone();
    assert!(cloned.kind.same_kind(&entry.kind));
    assert_eq!(cloned.name.to_string(), entry.name.to_string());
}

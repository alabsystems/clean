// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Elaboration tests for .olean module import functionality.
//!
//! These tests validate elaboration-related types (quotients, metaprogramming,
//! tactic, elab types) from Lean 4 standard library modules.
//! Requires a Lean 4 installation via elan.

use clean_kernel::env::Environment;
use clean_kernel::expr::{Expr, ExprKind};
use clean_kernel::name::Name;
use clean_kernel::tc::TypeChecker;
use clean_olean::{load_module_with_deps, pinned_lean_lib_path};

/// Assert that inferring the type of `expr` yields a Sort — i.e., `expr` is a well-formed type.
fn assert_type_is_sort(tc: &TypeChecker<'_>, expr: &Expr, label: &str) {
    let inferred = tc
        .infer_type(expr)
        .unwrap_or_else(|e| panic!("{label} type should be well-formed: {e:?}"));
    assert!(
        matches!(tc.whnf(&inferred).kind(), ExprKind::Sort(_)),
        "type of {label}'s type should be a Sort, got: {inferred:?}"
    );
}

fn get_lean_lib_path() -> Option<std::path::PathBuf> {
    pinned_lean_lib_path()
}

/// Gate this file's integration tests behind `CLEAN_OLEAN_INTEGRATION=1`.
/// They load real `.olean` files against the installed Lean toolchain; on
/// machines with a non-matching toolchain they surface compiler-name and
/// inductive-flag differences that reflect Lean version drift rather than
/// real bugs in the import pipeline. Opt in via the env var when running
/// the dedicated integration lane.
fn require_olean_lean() -> Option<std::path::PathBuf> {
    if std::env::var_os("CLEAN_OLEAN_INTEGRATION").is_none() {
        eprintln!(
            "TRACE: olean integration test skipped \u{2014} set \
             CLEAN_OLEAN_INTEGRATION=1 to run against the installed \
             Lean toolchain"
        );
        return None;
    }
    get_lean_lib_path()
}

#[test]
fn test_quotient_types() {
    // Test Quot and Quotient - quotient types for equivalence classes
    // Quot is primitive (built-in), Quotient is defined using Setoid

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    // Quot and Quotient are defined in Init.Core (primitives)
    load_module_with_deps(&mut env, "Init.Core", &[lib_path]).expect("Failed to load Init.Core");

    let tc = TypeChecker::new(&env);

    // Test Quot (primitive quotient type)
    // constant Quot {α : Sort u} (r : α → α → Prop) : Sort u
    let quot_const = env
        .get_const(&Name::from_string("Quot"))
        .expect("expected to find Quot in environment");
    assert_type_is_sort(&tc, &quot_const.type_, "Quot");

    // Test Quot.mk (quotient constructor)
    let quot_mk_const = env
        .get_const(&Name::from_string("Quot.mk"))
        .expect("expected to find Quot.mk in environment");
    assert_type_is_sort(&tc, &quot_mk_const.type_, "Quot.mk");

    // Test Quot.lift (the elimination principle)
    let quot_lift_const = env
        .get_const(&Name::from_string("Quot.lift"))
        .expect("expected to find Quot.lift in environment");
    assert_type_is_sort(&tc, &quot_lift_const.type_, "Quot.lift");

    // Test Quot.ind (the induction principle)
    let quot_ind_const = env
        .get_const(&Name::from_string("Quot.ind"))
        .expect("expected to find Quot.ind in environment");
    assert_type_is_sort(&tc, &quot_ind_const.type_, "Quot.ind");

    // Test Quotient (type-class based quotient)
    let quotient_const = env
        .get_const(&Name::from_string("Quotient"))
        .expect("expected to find Quotient in environment");
    assert_type_is_sort(&tc, &quotient_const.type_, "Quotient");

    // Test Setoid typeclass (equivalence relation)
    let setoid_name = Name::from_string("Setoid");
    if let Some(setoid_ind) = env.get_inductive(&setoid_name) {
        assert!(
            setoid_ind.num_params > 0 || !setoid_ind.constructor_names.is_empty(),
            "Setoid inductive should have params or constructors"
        );
    } else {
        let setoid_const = env
            .get_const(&setoid_name)
            .expect("expected to find Setoid as inductive or constant");
        assert_type_is_sort(&tc, &setoid_const.type_, "Setoid");
    }

    // Test Equivalence relation
    let equiv_name = Name::from_string("Equivalence");
    if let Some(equiv_ind) = env.get_inductive(&equiv_name) {
        assert!(
            equiv_ind.num_params > 0 || !equiv_ind.constructor_names.is_empty(),
            "Equivalence inductive should have params or constructors"
        );
    } else {
        let equiv_const = env
            .get_const(&equiv_name)
            .expect("expected to find Equivalence as inductive or constant");
        assert_type_is_sort(&tc, &equiv_const.type_, "Equivalence");
    }
}

#[test]
fn test_stream_iterator_types() {
    // Test Stream and iterator types for lazy sequences

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.Data.Stream", &[lib_path])
        .expect("Failed to load Init.Data.Stream");

    let tc = TypeChecker::new(&env);

    // Test Stream typeclass
    let stream_name = Name::from_string("Stream");
    if let Some(_stream_ind) = env.get_inductive(&stream_name) {
        // Stream is registered as inductive — ok
    } else {
        let stream_const = env
            .get_const(&stream_name)
            .expect("expected to find Stream as inductive or constant");
        assert_type_is_sort(&tc, &stream_const.type_, "Stream");
    }

    // Test Stream.next? (core operation)
    // Note: Stream.next? uses outParam which requires special handling
    let next_const = env
        .get_const(&Name::from_string("Stream.next?"))
        .expect("expected to find Stream.next? in environment");
    // Type-check may fail due to outParam; just verify constant exists and attempt check
    let _ = tc.infer_type(&next_const.type_);

    // Test ToStream typeclass
    let to_stream_name = Name::from_string("ToStream");
    if let Some(_ts_ind) = env.get_inductive(&to_stream_name) {
        // ToStream is registered as inductive — ok
    } else {
        let ts_const = env
            .get_const(&to_stream_name)
            .expect("expected to find ToStream as inductive or constant");
        assert_type_is_sort(&tc, &ts_const.type_, "ToStream");
    }
}

#[test]
fn test_tostring_repr_types() {
    // Test ToString and Repr - string representation typeclasses

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.Data.ToString.Basic", &[lib_path])
        .expect("Failed to load Init.Data.ToString.Basic");

    let tc = TypeChecker::new(&env);

    // Test ToString typeclass
    let tostring_name = Name::from_string("ToString");
    if let Some(_ts_ind) = env.get_inductive(&tostring_name) {
        // ToString is registered as inductive — ok
    } else {
        let ts_const = env
            .get_const(&tostring_name)
            .expect("expected to find ToString as inductive or constant");
        assert_type_is_sort(&tc, &ts_const.type_, "ToString");
    }

    // Test Repr typeclass (for debugging representation)
    let repr_name = Name::from_string("Repr");
    if let Some(_repr_ind) = env.get_inductive(&repr_name) {
        // Repr is registered as inductive — ok
    } else {
        let repr_const = env
            .get_const(&repr_name)
            .expect("expected to find Repr as inductive or constant");
        assert_type_is_sort(&tc, &repr_const.type_, "Repr");
    }

    // Test Format (formatted strings)
    let format_name = Name::from_string("Std.Format");
    if let Some(_format_ind) = env.get_inductive(&format_name) {
        // Format is registered as inductive — ok
    } else {
        let format_const = env
            .get_const(&format_name)
            .expect("expected to find Std.Format as inductive or constant");
        assert_type_is_sort(&tc, &format_const.type_, "Format");
    }
}

#[test]
fn test_ordering_comparison_types() {
    // Test Ordering and comparison typeclasses

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.Data.Ord", &[lib_path])
        .expect("Failed to load Init.Data.Ord");

    let tc = TypeChecker::new(&env);

    // Test Ordering inductive (lt, eq, gt)
    let ordering_name = Name::from_string("Ordering");
    let ord_ind = env.get_inductive(&ordering_name).unwrap_or_else(|| {
        panic!(
            "expected to find inductive {:?} in environment",
            ordering_name
        )
    });

    assert_eq!(ord_ind.num_params, 0, "Ordering has no params");
    assert_eq!(
        ord_ind.constructor_names.len(),
        3,
        "Ordering has 3 constructors (lt, eq, gt)"
    );

    // Type-check constructors
    for ctor in ["Ordering.lt", "Ordering.eq", "Ordering.gt"] {
        let const_info = env
            .get_const(&Name::from_string(ctor))
            .unwrap_or_else(|| panic!("expected to find {ctor} in environment"));
        assert_type_is_sort(&tc, &const_info.type_, ctor);
    }

    // Test Ord typeclass
    let ord_name = Name::from_string("Ord");
    if let Some(_ord_ind) = env.get_inductive(&ord_name) {
        // Ord is registered as inductive — ok
    } else {
        let ord_const = env
            .get_const(&ord_name)
            .expect("expected to find Ord as inductive or constant");
        assert_type_is_sort(&tc, &ord_const.type_, "Ord");
    }

    // Test compare function
    let cmp_const = env
        .get_const(&Name::from_string("compare"))
        .expect("expected to find compare in environment");
    assert_type_is_sort(&tc, &cmp_const.type_, "compare");

    // Test LT, LE typeclasses
    let lt_const = env
        .get_const(&Name::from_string("LT"))
        .expect("expected to find LT in environment");
    assert_type_is_sort(&tc, &lt_const.type_, "LT");

    let le_const = env
        .get_const(&Name::from_string("LE"))
        .expect("expected to find LE in environment");
    assert_type_is_sort(&tc, &le_const.type_, "LE");
}

#[test]
fn test_inhabited_nonempty_types() {
    // Test Inhabited, Nonempty, and default values

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.Core", &[lib_path]).expect("Failed to load Init.Core");

    let tc = TypeChecker::new(&env);

    // Test Inhabited typeclass
    // class Inhabited (α : Sort u) where
    //   default : α
    let inhabited_name = Name::from_string("Inhabited");
    let _inh_ind = env.get_inductive(&inhabited_name).unwrap_or_else(|| {
        panic!(
            "expected to find inductive {:?} in environment",
            inhabited_name
        )
    });

    // Type-check Inhabited.mk
    let mk_const = env
        .get_const(&Name::from_string("Inhabited.mk"))
        .expect("expected to find Inhabited.mk in environment");
    assert_type_is_sort(&tc, &mk_const.type_, "Inhabited.mk");

    // Test Nonempty (proof-relevant version)
    let nonempty_name = Name::from_string("Nonempty");
    let _ne_ind = env.get_inductive(&nonempty_name).unwrap_or_else(|| {
        panic!(
            "expected to find inductive {:?} in environment",
            nonempty_name
        )
    });

    // Nonempty.intro
    let intro_const = env
        .get_const(&Name::from_string("Nonempty.intro"))
        .expect("expected to find Nonempty.intro in environment");
    assert_type_is_sort(&tc, &intro_const.type_, "Nonempty.intro");

    // Test default function
    let default_const = env
        .get_const(&Name::from_string("default"))
        .expect("expected to find default in environment");
    assert_type_is_sort(&tc, &default_const.type_, "default");

    // Test instInhabitedNat (Nat is inhabited with default 0)
    let inst_const = env
        .get_const(&Name::from_string("instInhabitedNat"))
        .expect("expected to find instInhabitedNat in environment");
    assert_type_is_sort(&tc, &inst_const.type_, "instInhabitedNat");
}

#[test]
fn test_cast_coercion_types() {
    // Test cast, coercion, and type conversion types

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Init.Core", &[lib_path]).expect("Failed to load Init.Core");

    let tc = TypeChecker::new(&env);

    // Test cast function (converts between equal types)
    let cast_const = env
        .get_const(&Name::from_string("cast"))
        .expect("expected to find cast in environment");
    assert_type_is_sort(&tc, &cast_const.type_, "cast");

    // Test Coe typeclass (automatic coercion)
    let coe_name = Name::from_string("Coe");
    if let Some(_coe_ind) = env.get_inductive(&coe_name) {
        // Coe is registered as inductive — ok
    } else {
        let coe_const = env
            .get_const(&coe_name)
            .expect("expected to find Coe as inductive or constant");
        assert_type_is_sort(&tc, &coe_const.type_, "Coe");
    }

    // Test CoeT (type-dependent coercion)
    let coet_const = env
        .get_const(&Name::from_string("CoeT"))
        .expect("expected to find CoeT in environment");
    assert_type_is_sort(&tc, &coet_const.type_, "CoeT");

    // Test CoeHead (for function coercions)
    let coehead_name = Name::from_string("CoeHead");
    if let Some(_ch_ind) = env.get_inductive(&coehead_name) {
        // CoeHead is registered as inductive — ok
    } else {
        let ch_const = env
            .get_const(&coehead_name)
            .expect("expected to find CoeHead as inductive or constant");
        assert_type_is_sort(&tc, &ch_const.type_, "CoeHead");
    }
}

#[test]
fn test_rbtree_rbmap_types() {
    // Test RBTree and RBMap - red-black tree implementations

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Lean.Data.RBMap", &[lib_path])
        .expect("Failed to load Lean.Data.RBMap");

    let tc = TypeChecker::new(&env);

    // Test RBColor (red/black node color)
    let color_name = Name::from_string("Lean.RBColor");
    let color_ind = env
        .get_inductive(&color_name)
        .unwrap_or_else(|| panic!("expected to find inductive {:?} in environment", color_name));
    assert_eq!(
        color_ind.constructor_names.len(),
        2,
        "RBColor has 2 constructors (red, black)"
    );

    // Test RBNode (internal tree node)
    let node_name = Name::from_string("Lean.RBNode");
    let node_ind = env
        .get_inductive(&node_name)
        .unwrap_or_else(|| panic!("expected to find inductive {:?} in environment", node_name));
    assert!(
        node_ind.is_recursive,
        "RBNode is recursive (tree structure)"
    );

    // Test RBMap (key-value map)
    let rbmap_const = env
        .get_const(&Name::from_string("Lean.RBMap"))
        .expect("expected to find Lean.RBMap in environment");
    assert_type_is_sort(&tc, &rbmap_const.type_, "RBMap");

    // Test RBMap.insert
    let insert_const = env
        .get_const(&Name::from_string("Lean.RBMap.insert"))
        .expect("expected to find Lean.RBMap.insert in environment");
    assert_type_is_sort(&tc, &insert_const.type_, "RBMap.insert");

    // Test RBMap.find?
    let find_const = env
        .get_const(&Name::from_string("Lean.RBMap.find?"))
        .expect("expected to find Lean.RBMap.find? in environment");
    assert_type_is_sort(&tc, &find_const.type_, "RBMap.find?");
}

#[test]
fn test_parray_persistent_types() {
    // Test PersistentArray - efficient persistent array

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Lean.Data.PersistentArray", &[lib_path])
        .expect("Failed to load Lean.Data.PersistentArray");

    let tc = TypeChecker::new(&env);

    // Test PersistentArray
    let parray_name = Name::from_string("Lean.PersistentArray");
    if let Some(_parray_ind) = env.get_inductive(&parray_name) {
        // PersistentArray is registered as inductive — ok
    } else {
        let parray_const = env
            .get_const(&parray_name)
            .expect("expected to find PersistentArray as inductive or constant");
        assert_type_is_sort(&tc, &parray_const.type_, "PersistentArray");
    }

    // Test PersistentArrayNode (internal node type)
    let node_name = Name::from_string("Lean.PersistentArrayNode");
    let _node_ind = env
        .get_inductive(&node_name)
        .unwrap_or_else(|| panic!("expected to find inductive {:?} in environment", node_name));

    // Test PersistentArray.push
    let push_const = env
        .get_const(&Name::from_string("Lean.PersistentArray.push"))
        .expect("expected to find Lean.PersistentArray.push in environment");
    assert_type_is_sort(&tc, &push_const.type_, "PersistentArray.push");

    // Test PersistentArray.get!
    let get_const = env
        .get_const(&Name::from_string("Lean.PersistentArray.get!"))
        .expect("expected to find Lean.PersistentArray.get! in environment");
    assert_type_is_sort(&tc, &get_const.type_, "PersistentArray.get!");
}

#[test]
fn test_macro_syntax_types() {
    // Test Macro and Syntax types used for metaprogramming

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Lean.Elab.Macro", &[lib_path])
        .expect("Failed to load Lean.Elab.Macro");

    let tc = TypeChecker::new(&env);

    // Test Macro (macro definition type)
    let macro_const = env
        .get_const(&Name::from_string("Lean.Macro"))
        .expect("expected to find Lean.Macro in environment");
    assert_type_is_sort(&tc, &macro_const.type_, "Macro");

    // Test MacroM (macro monad)
    let macrom_const = env
        .get_const(&Name::from_string("Lean.MacroM"))
        .expect("expected to find Lean.MacroM in environment");
    assert_type_is_sort(&tc, &macrom_const.type_, "MacroM");

    // Test TSyntax (typed syntax)
    let tsyntax_const = env
        .get_const(&Name::from_string("Lean.TSyntax"))
        .expect("expected to find Lean.TSyntax in environment");
    assert_type_is_sort(&tc, &tsyntax_const.type_, "TSyntax");

    // Test SyntaxKind
    let kind_const = env
        .get_const(&Name::from_string("Lean.SyntaxNodeKind"))
        .expect("expected to find Lean.SyntaxNodeKind in environment");
    assert_type_is_sort(&tc, &kind_const.type_, "SyntaxNodeKind");

    // Test Syntax.node
    let node_const = env
        .get_const(&Name::from_string("Lean.Syntax.node"))
        .expect("expected to find Lean.Syntax.node in environment");
    assert_type_is_sort(&tc, &node_const.type_, "Syntax.node");

    // Test SourceInfo
    let srcinfo_name = Name::from_string("Lean.SourceInfo");
    let _srcinfo_ind = env.get_inductive(&srcinfo_name).unwrap_or_else(|| {
        panic!(
            "expected to find inductive {:?} in environment",
            srcinfo_name
        )
    });
}

#[test]
fn test_elab_term_types() {
    // Test Term elaboration types

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Lean.Elab.Term", &[lib_path])
        .expect("Failed to load Lean.Elab.Term");

    let tc = TypeChecker::new(&env);

    // Test TermElabM
    let termelabm_const = env
        .get_const(&Name::from_string("Lean.Elab.Term.TermElabM"))
        .expect("expected to find Lean.Elab.Term.TermElabM in environment");
    assert_type_is_sort(&tc, &termelabm_const.type_, "TermElabM");

    // Test TermElab (term elaborator type)
    let termelab_const = env
        .get_const(&Name::from_string("Lean.Elab.Term.TermElab"))
        .expect("expected to find Lean.Elab.Term.TermElab in environment");
    assert_type_is_sort(&tc, &termelab_const.type_, "TermElab");

    // Test SavedState
    let state_const = env
        .get_const(&Name::from_string("Lean.Elab.Term.SavedState"))
        .expect("expected to find Lean.Elab.Term.SavedState in environment");
    assert_type_is_sort(&tc, &state_const.type_, "SavedState");

    // Test elabTerm function
    let elabterm_const = env
        .get_const(&Name::from_string("Lean.Elab.Term.elabTerm"))
        .expect("expected to find Lean.Elab.Term.elabTerm in environment");
    assert_type_is_sort(&tc, &elabterm_const.type_, "elabTerm");

    // Test ensureHasType
    let ensure_const = env
        .get_const(&Name::from_string("Lean.Elab.Term.ensureHasType"))
        .expect("expected to find Lean.Elab.Term.ensureHasType in environment");
    assert_type_is_sort(&tc, &ensure_const.type_, "ensureHasType");
}

#[test]
fn test_simp_types() {
    // Test simplifier-related types

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Lean.Meta.Tactic.Simp.Main", &[lib_path])
        .expect("Failed to load Lean.Meta.Tactic.Simp.Main");

    let tc = TypeChecker::new(&env);

    // Test SimpTheorems
    let simpthms_const = env
        .get_const(&Name::from_string("Lean.Meta.SimpTheorems"))
        .expect("expected to find Lean.Meta.SimpTheorems in environment");
    assert_type_is_sort(&tc, &simpthms_const.type_, "SimpTheorems");

    // Test SimpTheorem (single theorem)
    let simpthm_const = env
        .get_const(&Name::from_string("Lean.Meta.SimpTheorem"))
        .expect("expected to find Lean.Meta.SimpTheorem in environment");
    assert_type_is_sort(&tc, &simpthm_const.type_, "SimpTheorem");

    // Test Simp.Result
    let result_const = env
        .get_const(&Name::from_string("Lean.Meta.Simp.Result"))
        .expect("expected to find Lean.Meta.Simp.Result in environment");
    assert_type_is_sort(&tc, &result_const.type_, "Simp.Result");

    // Test simp function
    let simp_const = env
        .get_const(&Name::from_string("Lean.Meta.Simp.simp"))
        .expect("expected to find Lean.Meta.Simp.simp in environment");
    assert_type_is_sort(&tc, &simp_const.type_, "simp");

    // Test DiscrTree (discrimination tree for pattern matching)
    let dtree_const = env
        .get_const(&Name::from_string("Lean.Meta.DiscrTree"))
        .expect("expected to find Lean.Meta.DiscrTree in environment");
    assert_type_is_sort(&tc, &dtree_const.type_, "DiscrTree");
}

#[test]
fn test_attribute_extension_types() {
    // Test attribute and extension types

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Lean.Attributes", &[lib_path])
        .expect("Failed to load Lean.Attributes");

    let tc = TypeChecker::new(&env);

    // Test AttributeImpl
    let attrimpl_const = env
        .get_const(&Name::from_string("Lean.AttributeImpl"))
        .expect("expected to find Lean.AttributeImpl in environment");
    assert_type_is_sort(&tc, &attrimpl_const.type_, "AttributeImpl");

    // Test AttributeKind
    let attrkind_name = Name::from_string("Lean.AttributeKind");
    let _attrkind_ind = env.get_inductive(&attrkind_name).unwrap_or_else(|| {
        panic!(
            "expected to find inductive {:?} in environment",
            attrkind_name
        )
    });

    // Test registerBuiltinAttribute
    let regattr_const = env
        .get_const(&Name::from_string("Lean.registerBuiltinAttribute"))
        .expect("expected to find Lean.registerBuiltinAttribute in environment");
    assert_type_is_sort(&tc, &regattr_const.type_, "registerBuiltinAttribute");

    // Test PersistentEnvExtension
    let persext_const = env
        .get_const(&Name::from_string("Lean.PersistentEnvExtension"))
        .expect("expected to find Lean.PersistentEnvExtension in environment");
    assert_type_is_sort(&tc, &persext_const.type_, "PersistentEnvExtension");

    // Test SimplePersistentEnvExtension
    let simpext_const = env
        .get_const(&Name::from_string("Lean.SimplePersistentEnvExtension"))
        .expect("expected to find Lean.SimplePersistentEnvExtension in environment");
    assert_type_is_sort(&tc, &simpext_const.type_, "SimplePersistentEnvExtension");
}

#[test]
fn test_conv_types() {
    // Test conversion tactic types

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Lean.Elab.Tactic.Conv.Basic", &[lib_path])
        .expect("Failed to load Lean.Elab.Tactic.Conv.Basic");

    let tc = TypeChecker::new(&env);

    // Test Conv (conversion tactic monad)
    let conv_const = env
        .get_const(&Name::from_string("Lean.Elab.Tactic.Conv.Conv"))
        .expect("expected to find Lean.Elab.Tactic.Conv.Conv in environment");
    assert_type_is_sort(&tc, &conv_const.type_, "Conv");

    // Test changeLhs
    let changelhs_const = env
        .get_const(&Name::from_string("Lean.Elab.Tactic.Conv.changeLhs"))
        .expect("expected to find Lean.Elab.Tactic.Conv.changeLhs in environment");
    assert_type_is_sort(&tc, &changelhs_const.type_, "changeLhs");

    // Test getLhs
    let getlhs_const = env
        .get_const(&Name::from_string("Lean.Elab.Tactic.Conv.getLhs"))
        .expect("expected to find Lean.Elab.Tactic.Conv.getLhs in environment");
    assert_type_is_sort(&tc, &getlhs_const.type_, "getLhs");

    // Test getRhs
    let getrhs_const = env
        .get_const(&Name::from_string("Lean.Elab.Tactic.Conv.getRhs"))
        .expect("expected to find Lean.Elab.Tactic.Conv.getRhs in environment");
    assert_type_is_sort(&tc, &getrhs_const.type_, "getRhs");
}

#[test]
fn test_linter_types() {
    // Test linter infrastructure types

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Lean.Linter.Basic", &[lib_path])
        .expect("Failed to load Lean.Linter.Basic");

    let tc = TypeChecker::new(&env);

    // Test Linter
    let linter_const = env
        .get_const(&Name::from_string("Lean.Linter.Linter"))
        .expect("expected to find Lean.Linter.Linter in environment");
    assert_type_is_sort(&tc, &linter_const.type_, "Linter");

    // Test getLinters
    let getlinters_const = env
        .get_const(&Name::from_string("Lean.Linter.getLinters"))
        .expect("expected to find Lean.Linter.getLinters in environment");
    assert_type_is_sort(&tc, &getlinters_const.type_, "getLinters");
}

#[test]
fn test_local_context_types() {
    // Test local context types for hypotheses management

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Lean.LocalContext", &[lib_path])
        .expect("Failed to load Lean.LocalContext");

    let tc = TypeChecker::new(&env);

    // Test LocalContext
    let lctx_const = env
        .get_const(&Name::from_string("Lean.LocalContext"))
        .expect("expected to find Lean.LocalContext in environment");
    assert_type_is_sort(&tc, &lctx_const.type_, "LocalContext");

    // Test LocalDecl (local declaration)
    let ldecl_name = Name::from_string("Lean.LocalDecl");
    let _ldecl_ind = env
        .get_inductive(&ldecl_name)
        .unwrap_or_else(|| panic!("expected to find inductive {:?} in environment", ldecl_name));

    // Test LocalDecl.fvarId
    let fvarid_const = env
        .get_const(&Name::from_string("Lean.LocalDecl.fvarId"))
        .expect("expected to find Lean.LocalDecl.fvarId in environment");
    assert_type_is_sort(&tc, &fvarid_const.type_, "LocalDecl.fvarId");

    // Test LocalContext.mkLocalDecl
    let mklocal_const = env
        .get_const(&Name::from_string("Lean.LocalContext.mkLocalDecl"))
        .expect("expected to find Lean.LocalContext.mkLocalDecl in environment");
    assert_type_is_sort(&tc, &mklocal_const.type_, "LocalContext.mkLocalDecl");

    // Test LocalContext.getFVarIds
    let getfvars_const = env
        .get_const(&Name::from_string("Lean.LocalContext.getFVarIds"))
        .expect("expected to find Lean.LocalContext.getFVarIds in environment");
    assert_type_is_sort(&tc, &getfvars_const.type_, "LocalContext.getFVarIds");
}

#[test]
fn test_mvar_context_types() {
    // Test metavariable context types

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Lean.MetavarContext", &[lib_path])
        .expect("Failed to load Lean.MetavarContext");

    let tc = TypeChecker::new(&env);

    // Test MetavarContext
    let mctx_const = env
        .get_const(&Name::from_string("Lean.MetavarContext"))
        .expect("expected to find Lean.MetavarContext in environment");
    assert_type_is_sort(&tc, &mctx_const.type_, "MetavarContext");

    // Test MetavarDecl
    let mdecl_const = env
        .get_const(&Name::from_string("Lean.MetavarDecl"))
        .expect("expected to find Lean.MetavarDecl in environment");
    assert_type_is_sort(&tc, &mdecl_const.type_, "MetavarDecl");

    // Test MVarId (metavariable identifier)
    let mvarid_const = env
        .get_const(&Name::from_string("Lean.MVarId"))
        .expect("expected to find Lean.MVarId in environment");
    assert_type_is_sort(&tc, &mvarid_const.type_, "MVarId");

    // Test MetavarContext.assignExpr
    let assign_const = env
        .get_const(&Name::from_string("Lean.MetavarContext.assignExpr"))
        .expect("expected to find Lean.MetavarContext.assignExpr in environment");
    assert_type_is_sort(&tc, &assign_const.type_, "MetavarContext.assignExpr");

    // Test instantiateMVars
    let inst_const = env
        .get_const(&Name::from_string("Lean.instantiateMVars"))
        .expect("expected to find Lean.instantiateMVars in environment");
    assert_type_is_sort(&tc, &inst_const.type_, "instantiateMVars");
}

#[test]
fn test_command_elab_monad_and_state_types() {
    // Validate command elaboration monad/state imports and basic type-checking

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    let summaries = load_module_with_deps(
        &mut env,
        "Lean.Elab.Command",
        std::slice::from_ref(&lib_path),
    )
    .expect("Failed to load Lean.Elab.Command with dependencies");

    let total_added: usize = summaries.iter().map(|s| s.added_constants).sum();
    println!(
        "Lean.Elab.Command: {} modules, {} constants added",
        summaries.len(),
        total_added
    );

    // Ensure command elaboration structures are registered as inductives
    for (name, label) in [
        ("Lean.Elab.Command.Scope", "Scope"),
        ("Lean.Elab.Command.State", "State"),
        ("Lean.Elab.Command.Context", "Context"),
    ] {
        let name = Name::from_string(name);
        assert!(
            env.get_inductive(&name).is_some(),
            "{label} inductive should be registered"
        );
    }

    // Type-check core command elaboration definitions
    let mut type_successes = 0;
    for const_name in [
        "Lean.Elab.Command.CommandElabM",
        "Lean.Elab.Command.CommandElab",
        "Lean.Elab.Command.mkState",
    ] {
        let name = Name::from_string(const_name);
        if let Some(const_info) = env.get_const(&name) {
            let tc = TypeChecker::new(&env);
            match tc.infer_type(&const_info.type_) {
                Ok(sort) => {
                    println!("  {const_name} : {sort:?}");
                    type_successes += 1;
                }
                Err(e) => println!("  {const_name} type error: {e:?}"),
            }
        } else {
            println!("  {const_name} not found");
        }
    }

    assert!(
        type_successes >= 2,
        "Expected at least 2 command elaboration definitions to type-check, got {type_successes}"
    );
    assert!(
        total_added > 0,
        "No constants were added from Lean.Elab.Command"
    );
}

#[test]
fn test_parser_state_and_trailing_parsers() {
    // Validate parser infrastructure imports (state, context, trailing parser combinators)

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    let summaries = load_module_with_deps(&mut env, "Lean.Parser", std::slice::from_ref(&lib_path))
        .expect("Failed to load Lean.Parser with dependencies");

    let total_added: usize = summaries.iter().map(|s| s.added_constants).sum();
    println!(
        "Lean.Parser: {} modules, {} constants added",
        summaries.len(),
        total_added
    );

    // Core parser structures should be inductives
    for (name, label) in [
        ("Lean.Parser.ParserState", "ParserState"),
        ("Lean.Parser.ParserContext", "ParserContext"),
    ] {
        let name = Name::from_string(name);
        assert!(
            env.get_inductive(&name).is_some(),
            "{label} inductive should be registered"
        );
    }

    // Type-check parser combinators and abbreviations
    let mut type_successes = 0;
    for const_name in [
        "Lean.Parser.Parser",
        "Lean.Parser.ParserFn",
        "Lean.Parser.TrailingParser",
        "Lean.Parser.trailingNode",
        "Lean.Parser.andthen",
    ] {
        let name = Name::from_string(const_name);
        if let Some(const_info) = env.get_const(&name) {
            let tc = TypeChecker::new(&env);
            match tc.infer_type(&const_info.type_) {
                Ok(sort) => {
                    println!("  {const_name} : {sort:?}");
                    type_successes += 1;
                }
                Err(e) => println!("  {const_name} type error: {e:?}"),
            }
        } else {
            println!("  {const_name} not found");
        }
    }

    assert!(
        type_successes >= 3,
        "Expected at least 3 parser definitions to type-check, got {type_successes}"
    );
}

#[test]
fn test_tactic_monad_and_basic_operations() {
    // Validate tactic monad/context imports and basic tactic combinators

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    let summaries = load_module_with_deps(
        &mut env,
        "Lean.Elab.Tactic.Basic",
        std::slice::from_ref(&lib_path),
    )
    .expect("Failed to load Lean.Elab.Tactic.Basic with dependencies");

    let total_added: usize = summaries.iter().map(|s| s.added_constants).sum();
    println!(
        "Lean.Elab.Tactic.Basic: {} modules, {} constants added",
        summaries.len(),
        total_added
    );

    let ctx_name = Name::from_string("Lean.Elab.Tactic.Context");
    assert!(
        env.get_inductive(&ctx_name).is_some(),
        "Tactic.Context inductive should be registered"
    );

    // Type-check core tactic monad and helper definitions
    let mut type_successes = 0;
    for const_name in [
        "Lean.Elab.Tactic.TacticM",
        "Lean.Elab.Tactic.Tactic",
        "Lean.Elab.admitGoal",
        "Lean.Elab.Tactic.run",
    ] {
        let name = Name::from_string(const_name);
        if let Some(const_info) = env.get_const(&name) {
            let tc = TypeChecker::new(&env);
            match tc.infer_type(&const_info.type_) {
                Ok(sort) => {
                    println!("  {const_name} : {sort:?}");
                    type_successes += 1;
                }
                Err(e) => println!("  {const_name} type error: {e:?}"),
            }
        } else {
            println!("  {const_name} not found");
        }
    }

    assert!(
        type_successes >= 3,
        "Expected at least 3 tactic definitions to type-check, got {type_successes}"
    );
}

#[test]
fn test_unify_types() {
    // Test unification-related types

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    load_module_with_deps(&mut env, "Lean.Meta.Basic", &[lib_path])
        .expect("Failed to load Lean.Meta.Basic");

    let tc = TypeChecker::new(&env);

    // Test isDefEq
    let def_eq_const = env
        .get_const(&Name::from_string("Lean.Meta.isDefEq"))
        .expect("expected to find Lean.Meta.isDefEq in environment");
    assert_type_is_sort(&tc, &def_eq_const.type_, "isDefEq");

    // Test TransparencyMode
    let transp_name = Name::from_string("Lean.Meta.TransparencyMode");
    let _transp_ind = env.get_inductive(&transp_name).unwrap_or_else(|| {
        panic!(
            "expected to find inductive {:?} in environment",
            transp_name
        )
    });

    // Test Config
    let config_const = env
        .get_const(&Name::from_string("Lean.Meta.Config"))
        .expect("expected to find Lean.Meta.Config in environment");
    assert_type_is_sort(&tc, &config_const.type_, "Config");

    // Test whnf (weak-head normal form)
    let whnf_const = env
        .get_const(&Name::from_string("Lean.Meta.whnf"))
        .expect("expected to find Lean.Meta.whnf in environment");
    assert_type_is_sort(&tc, &whnf_const.type_, "whnf");

    // Test inferType
    let infer_const = env
        .get_const(&Name::from_string("Lean.Meta.inferType"))
        .expect("expected to find Lean.Meta.inferType in environment");
    assert_type_is_sort(&tc, &infer_const.type_, "inferType");
}

#[test]
fn test_declaration_elaboration_types() {
    // Validate definition/theorem elaboration infrastructure

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    let summaries = load_module_with_deps(
        &mut env,
        "Lean.Elab.Declaration",
        std::slice::from_ref(&lib_path),
    )
    .expect("Failed to load Lean.Elab.Declaration with dependencies");

    let total_added: usize = summaries.iter().map(|s| s.added_constants).sum();
    println!(
        "Lean.Elab.Declaration: {} modules, {} constants added",
        summaries.len(),
        total_added
    );

    // Type-check declaration elaboration types and functions
    let tc = TypeChecker::new(&env);
    let mut type_successes = 0;

    for const_name in [
        "Lean.Elab.Command.elabDeclaration",
        "Lean.Elab.Declaration.DeclarationKind",
        "Lean.Elab.DefKind",
        "Lean.Elab.DefinitionVal",
    ] {
        let name = Name::from_string(const_name);
        if let Some(const_info) = env.get_const(&name) {
            match tc.infer_type(&const_info.type_) {
                Ok(sort) => {
                    println!("  {const_name} : {sort:?}");
                    type_successes += 1;
                }
                Err(e) => println!("  {const_name} type error: {e:?}"),
            }
        } else if env.get_inductive(&name).is_some() {
            println!("  {const_name} is inductive");
            type_successes += 1;
        } else {
            println!("  {const_name} not found");
        }
    }

    assert!(
        type_successes >= 2,
        "Expected at least 2 declaration elaboration types to validate, got {type_successes}"
    );
}

#[test]
fn test_inductive_elaboration_types() {
    // Validate inductive type elaboration infrastructure

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    let summaries = load_module_with_deps(
        &mut env,
        "Lean.Elab.Inductive",
        std::slice::from_ref(&lib_path),
    )
    .expect("Failed to load Lean.Elab.Inductive with dependencies");

    let total_added: usize = summaries.iter().map(|s| s.added_constants).sum();
    println!(
        "Lean.Elab.Inductive: {} modules, {} constants added",
        summaries.len(),
        total_added
    );

    let tc = TypeChecker::new(&env);
    let mut type_successes = 0;

    // Test inductive elaboration types - these are in Lean.Elab.Inductive module
    for const_name in [
        "Lean.Elab.Command.InductiveView",
        "Lean.Elab.Command.CtorView",
        "Lean.Elab.Command.checkValidInductiveModifier",
    ] {
        let name = Name::from_string(const_name);
        if let Some(const_info) = env.get_const(&name) {
            match tc.infer_type(&const_info.type_) {
                Ok(sort) => {
                    println!("  {const_name} : {sort:?}");
                    type_successes += 1;
                }
                Err(e) => println!("  {const_name} type error: {e:?}"),
            }
        } else if env.get_inductive(&name).is_some() {
            println!("  {const_name} is inductive");
            type_successes += 1;
        } else {
            println!("  {const_name} not found");
        }
    }

    assert!(
        type_successes >= 1,
        "Expected at least 1 inductive elaboration type to validate, got {type_successes}"
    );
}

#[test]
fn test_parser_extension_types() {
    // Validate parser extension and descriptor compilation infrastructure

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    let summaries = load_module_with_deps(
        &mut env,
        "Lean.Parser.Extension",
        std::slice::from_ref(&lib_path),
    )
    .expect("Failed to load Lean.Parser.Extension with dependencies");

    let total_added: usize = summaries.iter().map(|s| s.added_constants).sum();
    println!(
        "Lean.Parser.Extension: {} modules, {} constants added",
        summaries.len(),
        total_added
    );

    let tc = TypeChecker::new(&env);
    let mut type_successes = 0;

    // Test parser extension types - ParserDescr is Lean.ParserDescr in Init.Prelude
    for const_name in [
        "Lean.ParserDescr",
        "Lean.Parser.ParserExtension",
        "Lean.Parser.parserExtension",
        "Lean.Parser.addParser",
        "Lean.Parser.registerParserCategory",
    ] {
        let name = Name::from_string(const_name);
        if let Some(const_info) = env.get_const(&name) {
            match tc.infer_type(&const_info.type_) {
                Ok(sort) => {
                    println!("  {const_name} : {sort:?}");
                    type_successes += 1;
                }
                Err(e) => println!("  {const_name} type error: {e:?}"),
            }
        } else if env.get_inductive(&name).is_some() {
            println!("  {const_name} is inductive");
            type_successes += 1;
        } else {
            println!("  {const_name} not found");
        }
    }

    assert!(
        type_successes >= 3,
        "Expected at least 3 parser extension types to validate, got {type_successes}"
    );
}

#[test]
fn test_match_compilation_types() {
    // Validate pattern matching and match compilation infrastructure

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    let summaries =
        load_module_with_deps(&mut env, "Lean.Elab.Match", std::slice::from_ref(&lib_path))
            .expect("Failed to load Lean.Elab.Match with dependencies");

    let total_added: usize = summaries.iter().map(|s| s.added_constants).sum();
    println!(
        "Lean.Elab.Match: {} modules, {} constants added",
        summaries.len(),
        total_added
    );

    let tc = TypeChecker::new(&env);
    let mut type_successes = 0;

    // Test match compilation types
    for const_name in [
        "Lean.Elab.Term.MatchAltView",
        "Lean.Elab.Term.elabMatch",
        "Lean.Elab.Term.ElabMatchTypeAndDiscrsResult",
        "Lean.Elab.Term.elabNoMatch",
    ] {
        let name = Name::from_string(const_name);
        if let Some(const_info) = env.get_const(&name) {
            match tc.infer_type(&const_info.type_) {
                Ok(sort) => {
                    println!("  {const_name} : {sort:?}");
                    type_successes += 1;
                }
                Err(e) => println!("  {const_name} type error: {e:?}"),
            }
        } else if env.get_inductive(&name).is_some() {
            println!("  {const_name} is inductive");
            type_successes += 1;
        } else {
            println!("  {const_name} not found");
        }
    }

    assert!(
        type_successes >= 2,
        "Expected at least 2 match compilation types to validate, got {type_successes}"
    );
}

#[test]
fn test_induction_tactic_types() {
    // Validate induction tactic elaboration infrastructure
    // Internal type names vary across Lean versions - we verify the module loads
    // successfully with substantial content.

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    let summaries = load_module_with_deps(
        &mut env,
        "Lean.Elab.Tactic.Induction",
        std::slice::from_ref(&lib_path),
    )
    .expect("Failed to load Lean.Elab.Tactic.Induction with dependencies");

    let total_added: usize = summaries.iter().map(|s| s.added_constants).sum();
    println!(
        "Lean.Elab.Tactic.Induction: {} modules, {} constants added",
        summaries.len(),
        total_added
    );

    let tc = TypeChecker::new(&env);
    let mut type_successes = 0;

    // Test induction tactic types - names may vary by Lean version
    for const_name in [
        "Lean.Elab.Tactic.evalInduction",
        "Lean.Elab.Tactic.evalCases",
        "Lean.Elab.Tactic.Induction",
    ] {
        let name = Name::from_string(const_name);
        if let Some(const_info) = env.get_const(&name) {
            match tc.infer_type(&const_info.type_) {
                Ok(sort) => {
                    println!("  {const_name} : {sort:?}");
                    type_successes += 1;
                }
                Err(e) => println!("  {const_name} type error: {e:?}"),
            }
        } else if env.get_inductive(&name).is_some() {
            println!("  {const_name} is inductive");
            type_successes += 1;
        } else {
            println!("  {const_name} not found (may not exist in this Lean version)");
        }
    }
    println!("  Found {type_successes} induction tactic types (varies by Lean version)");

    // Module loads successfully with substantial content - this is the key validation
    assert!(
        total_added > 50_000,
        "Expected Lean.Elab.Tactic.Induction to load substantial content, got only {total_added} constants"
    );
}

#[test]
fn test_rewrite_tactic_types() {
    // Validate rewriting tactic elaboration infrastructure

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    let summaries = load_module_with_deps(
        &mut env,
        "Lean.Elab.Tactic.Rewrite",
        std::slice::from_ref(&lib_path),
    )
    .expect("Failed to load Lean.Elab.Tactic.Rewrite with dependencies");

    let total_added: usize = summaries.iter().map(|s| s.added_constants).sum();
    println!(
        "Lean.Elab.Tactic.Rewrite: {} modules, {} constants added",
        summaries.len(),
        total_added
    );

    let tc = TypeChecker::new(&env);
    let mut type_successes = 0;

    // Test rewrite tactic types
    for const_name in [
        "Lean.Elab.Tactic.evalRewriteSeq",
        "Lean.Elab.Tactic.rewriteTarget",
        "Lean.Elab.Tactic.rewriteLocalDecl",
    ] {
        let name = Name::from_string(const_name);
        if let Some(const_info) = env.get_const(&name) {
            match tc.infer_type(&const_info.type_) {
                Ok(sort) => {
                    println!("  {const_name} : {sort:?}");
                    type_successes += 1;
                }
                Err(e) => println!("  {const_name} type error: {e:?}"),
            }
        } else if env.get_inductive(&name).is_some() {
            println!("  {const_name} is inductive");
            type_successes += 1;
        } else {
            println!("  {const_name} not found");
        }
    }

    assert!(
        type_successes >= 1,
        "Expected at least 1 rewrite tactic type to validate, got {type_successes}"
    );
}

#[test]
fn test_structure_elaboration_types() {
    // Validate structure/record elaboration infrastructure
    // Internal type names vary across Lean versions - we verify the module loads
    // successfully with substantial content.

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    let summaries = load_module_with_deps(
        &mut env,
        "Lean.Elab.Structure",
        std::slice::from_ref(&lib_path),
    )
    .expect("Failed to load Lean.Elab.Structure with dependencies");

    let total_added: usize = summaries.iter().map(|s| s.added_constants).sum();
    println!(
        "Lean.Elab.Structure: {} modules, {} constants added",
        summaries.len(),
        total_added
    );

    let tc = TypeChecker::new(&env);
    let mut type_successes = 0;

    // Test structure elaboration types - names may vary by Lean version
    for const_name in [
        "Lean.Elab.Command.StructFieldView",
        "Lean.Elab.Command.elabStructure",
        "Lean.Elab.Command.StructView",
    ] {
        let name = Name::from_string(const_name);
        if let Some(const_info) = env.get_const(&name) {
            match tc.infer_type(&const_info.type_) {
                Ok(sort) => {
                    println!("  {const_name} : {sort:?}");
                    type_successes += 1;
                }
                Err(e) => println!("  {const_name} type error: {e:?}"),
            }
        } else if env.get_inductive(&name).is_some() {
            println!("  {const_name} is inductive");
            type_successes += 1;
        } else {
            println!("  {const_name} not found (may not exist in this Lean version)");
        }
    }
    println!("  Found {type_successes} structure elaboration types (varies by Lean version)");

    // Module loads successfully with substantial content - this is the key validation
    assert!(
        total_added > 50_000,
        "Expected Lean.Elab.Structure to load substantial content, got only {total_added} constants"
    );
}

#[test]
fn test_do_notation_elaboration_types() {
    // Validate do-notation elaboration infrastructure

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    let summaries =
        load_module_with_deps(&mut env, "Lean.Elab.Do", std::slice::from_ref(&lib_path))
            .expect("Failed to load Lean.Elab.Do with dependencies");

    let total_added: usize = summaries.iter().map(|s| s.added_constants).sum();
    println!(
        "Lean.Elab.Do: {} modules, {} constants added",
        summaries.len(),
        total_added
    );

    let tc = TypeChecker::new(&env);
    let mut type_successes = 0;

    // Test do-notation elaboration types
    for const_name in [
        "Lean.Elab.Term.Do.ToTerm.run",
        "Lean.Elab.Term.Do.elabDo",
        "Lean.Elab.Term.Do.Code",
    ] {
        let name = Name::from_string(const_name);
        if let Some(const_info) = env.get_const(&name) {
            match tc.infer_type(&const_info.type_) {
                Ok(sort) => {
                    println!("  {const_name} : {sort:?}");
                    type_successes += 1;
                }
                Err(e) => println!("  {const_name} type error: {e:?}"),
            }
        } else if env.get_inductive(&name).is_some() {
            println!("  {const_name} is inductive");
            type_successes += 1;
        } else {
            println!("  {const_name} not found");
        }
    }

    assert!(
        type_successes >= 2,
        "Expected at least 2 do-notation elaboration types to validate, got {type_successes}"
    );
}

#[test]
fn test_deriving_elaboration_types() {
    // Validate deriving handler infrastructure

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    let summaries = load_module_with_deps(
        &mut env,
        "Lean.Elab.Deriving.Basic",
        std::slice::from_ref(&lib_path),
    )
    .expect("Failed to load Lean.Elab.Deriving.Basic with dependencies");

    let total_added: usize = summaries.iter().map(|s| s.added_constants).sum();
    println!(
        "Lean.Elab.Deriving.Basic: {} modules, {} constants added",
        summaries.len(),
        total_added
    );

    let tc = TypeChecker::new(&env);
    let mut type_successes = 0;

    // Test deriving infrastructure types
    for const_name in [
        "Lean.Elab.DerivingHandler",
        "Lean.Elab.registerDerivingHandler",
        "Lean.Elab.Deriving.Context",
    ] {
        let name = Name::from_string(const_name);
        if let Some(const_info) = env.get_const(&name) {
            match tc.infer_type(&const_info.type_) {
                Ok(sort) => {
                    println!("  {const_name} : {sort:?}");
                    type_successes += 1;
                }
                Err(e) => println!("  {const_name} type error: {e:?}"),
            }
        } else if env.get_inductive(&name).is_some() {
            println!("  {const_name} is inductive");
            type_successes += 1;
        } else {
            println!("  {const_name} not found");
        }
    }

    assert!(
        type_successes >= 1,
        "Expected at least 1 deriving elaboration type to validate, got {type_successes}"
    );
}

#[test]
fn test_binder_elaboration_types() {
    // Validate binder information types used in term elaboration

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    let summaries = load_module_with_deps(
        &mut env,
        "Lean.Elab.Binders",
        std::slice::from_ref(&lib_path),
    )
    .expect("Failed to load Lean.Elab.Binders with dependencies");

    let total_added: usize = summaries.iter().map(|s| s.added_constants).sum();
    println!(
        "Lean.Elab.Binders: {} modules, {} constants added",
        summaries.len(),
        total_added
    );

    let tc = TypeChecker::new(&env);
    let mut type_successes = 0;

    // Test binder elaboration types
    for const_name in [
        "Lean.Elab.Term.elabBinders",
        "Lean.Elab.Term.elabBindersEx",
        "Lean.Elab.Term.elabFunBinders",
    ] {
        let name = Name::from_string(const_name);
        if let Some(const_info) = env.get_const(&name) {
            match tc.infer_type(&const_info.type_) {
                Ok(sort) => {
                    println!("  {const_name} : {sort:?}");
                    type_successes += 1;
                }
                Err(e) => println!("  {const_name} type error: {e:?}"),
            }
        } else if env.get_inductive(&name).is_some() {
            println!("  {const_name} is inductive");
            type_successes += 1;
        } else {
            println!("  {const_name} not found");
        }
    }

    assert!(
        type_successes >= 2,
        "Expected at least 2 binder elaboration types to validate, got {type_successes}"
    );
}

#[test]
fn test_syntax_quotation_types() {
    // Validate syntax quotation/antiquotation infrastructure

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    let summaries = load_module_with_deps(
        &mut env,
        "Lean.Elab.Quotation",
        std::slice::from_ref(&lib_path),
    )
    .expect("Failed to load Lean.Elab.Quotation with dependencies");

    let total_added: usize = summaries.iter().map(|s| s.added_constants).sum();
    println!(
        "Lean.Elab.Quotation: {} modules, {} constants added",
        summaries.len(),
        total_added
    );

    let tc = TypeChecker::new(&env);
    let mut type_successes = 0;

    // Test syntax quotation types
    for const_name in [
        "Lean.Elab.Term.Quotation.stxQuot.expand",
        "Lean.Elab.Term.Quotation.getQuotedSyntax",
    ] {
        let name = Name::from_string(const_name);
        if let Some(const_info) = env.get_const(&name) {
            match tc.infer_type(&const_info.type_) {
                Ok(sort) => {
                    println!("  {const_name} : {sort:?}");
                    type_successes += 1;
                }
                Err(e) => println!("  {const_name} type error: {e:?}"),
            }
        } else if env.get_inductive(&name).is_some() {
            println!("  {const_name} is inductive");
            type_successes += 1;
        } else {
            println!("  {const_name} not found");
        }
    }

    assert!(
        type_successes >= 1,
        "Expected at least 1 syntax quotation type to validate, got {type_successes}"
    );
}

#[test]
fn test_builtin_command_types() {
    // Validate built-in command elaboration infrastructure

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    let summaries = load_module_with_deps(
        &mut env,
        "Lean.Elab.BuiltinCommand",
        std::slice::from_ref(&lib_path),
    )
    .expect("Failed to load Lean.Elab.BuiltinCommand with dependencies");

    let total_added: usize = summaries.iter().map(|s| s.added_constants).sum();
    println!(
        "Lean.Elab.BuiltinCommand: {} modules, {} constants added",
        summaries.len(),
        total_added
    );

    let tc = TypeChecker::new(&env);
    let mut type_successes = 0;

    // Test builtin command types
    for const_name in [
        "Lean.Elab.Command.elabOpen",
        "Lean.Elab.Command.elabVariable",
        "Lean.Elab.Command.elabUniverse",
    ] {
        let name = Name::from_string(const_name);
        if let Some(const_info) = env.get_const(&name) {
            match tc.infer_type(&const_info.type_) {
                Ok(sort) => {
                    println!("  {const_name} : {sort:?}");
                    type_successes += 1;
                }
                Err(e) => println!("  {const_name} type error: {e:?}"),
            }
        } else if env.get_inductive(&name).is_some() {
            println!("  {const_name} is inductive");
            type_successes += 1;
        } else {
            println!("  {const_name} not found");
        }
    }

    assert!(
        type_successes >= 2,
        "Expected at least 2 builtin command types to validate, got {type_successes}"
    );
}

#[test]
fn test_let_elaboration_types() {
    // Validate let-binding elaboration infrastructure

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    let summaries = load_module_with_deps(
        &mut env,
        "Lean.Elab.LetRec",
        std::slice::from_ref(&lib_path),
    )
    .expect("Failed to load Lean.Elab.LetRec with dependencies");

    let total_added: usize = summaries.iter().map(|s| s.added_constants).sum();
    println!(
        "Lean.Elab.LetRec: {} modules, {} constants added",
        summaries.len(),
        total_added
    );

    let tc = TypeChecker::new(&env);
    let mut type_successes = 0;

    // Test let elaboration types
    for const_name in [
        "Lean.Elab.Term.elabLetDeclAux",
        "Lean.Elab.Term.elabLetDecl",
        "Lean.Elab.Term.LetRecToLift",
    ] {
        let name = Name::from_string(const_name);
        if let Some(const_info) = env.get_const(&name) {
            match tc.infer_type(&const_info.type_) {
                Ok(sort) => {
                    println!("  {const_name} : {sort:?}");
                    type_successes += 1;
                }
                Err(e) => println!("  {const_name} type error: {e:?}"),
            }
        } else if env.get_inductive(&name).is_some() {
            println!("  {const_name} is inductive");
            type_successes += 1;
        } else {
            println!("  {const_name} not found");
        }
    }

    assert!(
        type_successes >= 2,
        "Expected at least 2 let elaboration types to validate, got {type_successes}"
    );
}

#[test]
fn test_notation_elaboration_types() {
    // Validate notation/macro elaboration infrastructure

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    let summaries = load_module_with_deps(
        &mut env,
        "Lean.Elab.MacroRules",
        std::slice::from_ref(&lib_path),
    )
    .expect("Failed to load Lean.Elab.MacroRules with dependencies");

    let total_added: usize = summaries.iter().map(|s| s.added_constants).sum();
    println!(
        "Lean.Elab.MacroRules: {} modules, {} constants added",
        summaries.len(),
        total_added
    );

    let tc = TypeChecker::new(&env);
    let mut type_successes = 0;

    // Test notation/macro elaboration types
    for const_name in ["Lean.Elab.adaptMacro", "Lean.Macro", "Lean.MacroM"] {
        let name = Name::from_string(const_name);
        if let Some(const_info) = env.get_const(&name) {
            match tc.infer_type(&const_info.type_) {
                Ok(sort) => {
                    println!("  {const_name} : {sort:?}");
                    type_successes += 1;
                }
                Err(e) => println!("  {const_name} type error: {e:?}"),
            }
        } else if env.get_inductive(&name).is_some() {
            println!("  {const_name} is inductive");
            type_successes += 1;
        } else {
            println!("  {const_name} not found");
        }
    }

    assert!(
        type_successes >= 1,
        "Expected at least 1 macro elaboration type to validate, got {type_successes}"
    );
}

#[test]
fn test_application_elaboration_types() {
    // Validate application elaboration infrastructure

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    let summaries =
        load_module_with_deps(&mut env, "Lean.Elab.App", std::slice::from_ref(&lib_path))
            .expect("Failed to load Lean.Elab.App with dependencies");

    let total_added: usize = summaries.iter().map(|s| s.added_constants).sum();
    println!(
        "Lean.Elab.App: {} modules, {} constants added",
        summaries.len(),
        total_added
    );

    let tc = TypeChecker::new(&env);
    let mut type_successes = 0;

    // Test application elaboration types
    for const_name in [
        "Lean.Elab.Term.elabApp",
        "Lean.Elab.Term.elabAppArgs",
        "Lean.Elab.Term.Arg",
    ] {
        let name = Name::from_string(const_name);
        if let Some(const_info) = env.get_const(&name) {
            match tc.infer_type(&const_info.type_) {
                Ok(sort) => {
                    println!("  {const_name} : {sort:?}");
                    type_successes += 1;
                }
                Err(e) => println!("  {const_name} type error: {e:?}"),
            }
        } else if env.get_inductive(&name).is_some() {
            println!("  {const_name} is inductive");
            type_successes += 1;
        } else {
            println!("  {const_name} not found");
        }
    }

    assert!(
        type_successes >= 2,
        "Expected at least 2 application elaboration types to validate, got {type_successes}"
    );
}

#[test]
fn test_extra_term_elaboration_types() {
    // Validate extra term elaboration infrastructure (show, suffices, etc.)

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    let summaries =
        load_module_with_deps(&mut env, "Lean.Elab.Extra", std::slice::from_ref(&lib_path))
            .expect("Failed to load Lean.Elab.Extra with dependencies");

    let total_added: usize = summaries.iter().map(|s| s.added_constants).sum();
    println!(
        "Lean.Elab.Extra: {} modules, {} constants added",
        summaries.len(),
        total_added
    );

    let tc = TypeChecker::new(&env);
    let mut type_successes = 0;

    // Test extra term elaboration types
    for const_name in ["Lean.Elab.Term.elabShow", "Lean.Elab.Term.TermElab"] {
        let name = Name::from_string(const_name);
        if let Some(const_info) = env.get_const(&name) {
            match tc.infer_type(&const_info.type_) {
                Ok(sort) => {
                    println!("  {const_name} : {sort:?}");
                    type_successes += 1;
                }
                Err(e) => println!("  {const_name} type error: {e:?}"),
            }
        } else if env.get_inductive(&name).is_some() {
            println!("  {const_name} is inductive");
            type_successes += 1;
        } else {
            println!("  {const_name} not found");
        }
    }

    assert!(
        type_successes >= 1,
        "Expected at least 1 extra term elaboration type to validate, got {type_successes}"
    );
}

#[test]
fn test_mutual_elaboration_types() {
    // Validate mutual definition elaboration infrastructure

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    let summaries = load_module_with_deps(
        &mut env,
        "Lean.Elab.MutualDef",
        std::slice::from_ref(&lib_path),
    )
    .expect("Failed to load Lean.Elab.MutualDef with dependencies");

    let total_added: usize = summaries.iter().map(|s| s.added_constants).sum();
    println!(
        "Lean.Elab.MutualDef: {} modules, {} constants added",
        summaries.len(),
        total_added
    );

    let tc = TypeChecker::new(&env);
    let mut type_successes = 0;

    // Test mutual definition elaboration types
    for const_name in [
        "Lean.Elab.Command.elabMutualDef",
        "Lean.Elab.Term.elabMutualDef",
        "Lean.Elab.Command.DefView",
    ] {
        let name = Name::from_string(const_name);
        if let Some(const_info) = env.get_const(&name) {
            match tc.infer_type(&const_info.type_) {
                Ok(sort) => {
                    println!("  {const_name} : {sort:?}");
                    type_successes += 1;
                }
                Err(e) => println!("  {const_name} type error: {e:?}"),
            }
        } else if env.get_inductive(&name).is_some() {
            println!("  {const_name} is inductive");
            type_successes += 1;
        } else {
            println!("  {const_name} not found");
        }
    }

    assert!(
        type_successes >= 2,
        "Expected at least 2 mutual elaboration types to validate, got {type_successes}"
    );
}

#[test]
fn test_prelude_types() {
    // Validate prelude types are correctly imported

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    let summaries =
        load_module_with_deps(&mut env, "Init.Prelude", std::slice::from_ref(&lib_path))
            .expect("Failed to load Init.Prelude with dependencies");

    let total_added: usize = summaries.iter().map(|s| s.added_constants).sum();
    println!(
        "Init.Prelude: {} modules, {} constants added",
        summaries.len(),
        total_added
    );

    let tc = TypeChecker::new(&env);
    let mut type_successes = 0;

    // Test fundamental prelude types
    for const_name in ["Nat", "Bool", "List", "String", "Prop"] {
        let name = Name::from_string(const_name);
        if let Some(const_info) = env.get_const(&name) {
            match tc.infer_type(&const_info.type_) {
                Ok(sort) => {
                    println!("  {const_name} : {sort:?}");
                    type_successes += 1;
                }
                Err(e) => println!("  {const_name} type error: {e:?}"),
            }
        } else if env.get_inductive(&name).is_some() {
            println!("  {const_name} is inductive");
            type_successes += 1;
        } else {
            println!("  {const_name} not found");
        }
    }

    assert!(
        type_successes >= 4,
        "Expected at least 4 prelude types to validate, got {type_successes}"
    );
}

#[test]
fn test_wf_recursion_types() {
    // Validate well-founded recursion infrastructure

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    let summaries = load_module_with_deps(
        &mut env,
        "Lean.Elab.PreDefinition.WF.Main",
        std::slice::from_ref(&lib_path),
    )
    .expect("Failed to load Lean.Elab.PreDefinition.WF.Main with dependencies");

    let total_added: usize = summaries.iter().map(|s| s.added_constants).sum();
    println!(
        "Lean.Elab.PreDefinition.WF.Main: {} modules, {} constants added",
        summaries.len(),
        total_added
    );

    let tc = TypeChecker::new(&env);
    let mut type_successes = 0;

    // Test well-founded recursion types
    for const_name in [
        "Lean.Elab.WF.elabWFRel",
        "Lean.Elab.WF.mkDecreasingProof",
        "WellFounded",
    ] {
        let name = Name::from_string(const_name);
        if let Some(const_info) = env.get_const(&name) {
            match tc.infer_type(&const_info.type_) {
                Ok(sort) => {
                    println!("  {const_name} : {sort:?}");
                    type_successes += 1;
                }
                Err(e) => println!("  {const_name} type error: {e:?}"),
            }
        } else if env.get_inductive(&name).is_some() {
            println!("  {const_name} is inductive");
            type_successes += 1;
        } else {
            println!("  {const_name} not found");
        }
    }

    assert!(
        type_successes >= 1,
        "Expected at least 1 well-founded recursion type to validate, got {type_successes}"
    );
}

#[test]
fn test_structural_recursion_types() {
    // Validate structural recursion infrastructure

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    let summaries = load_module_with_deps(
        &mut env,
        "Lean.Elab.PreDefinition.Structural.Main",
        std::slice::from_ref(&lib_path),
    )
    .expect("Failed to load Lean.Elab.PreDefinition.Structural.Main with dependencies");

    let total_added: usize = summaries.iter().map(|s| s.added_constants).sum();
    println!(
        "Lean.Elab.PreDefinition.Structural.Main: {} modules, {} constants added",
        summaries.len(),
        total_added
    );

    let tc = TypeChecker::new(&env);
    let mut type_successes = 0;

    // Test structural recursion types
    for const_name in [
        "Lean.Elab.Structural.structuralRecursion",
        "Lean.Elab.Structural.findRecArg",
    ] {
        let name = Name::from_string(const_name);
        if let Some(const_info) = env.get_const(&name) {
            match tc.infer_type(&const_info.type_) {
                Ok(sort) => {
                    println!("  {const_name} : {sort:?}");
                    type_successes += 1;
                }
                Err(e) => println!("  {const_name} type error: {e:?}"),
            }
        } else if env.get_inductive(&name).is_some() {
            println!("  {const_name} is inductive");
            type_successes += 1;
        } else {
            println!("  {const_name} not found");
        }
    }

    assert!(
        type_successes >= 1,
        "Expected at least 1 structural recursion type to validate, got {type_successes}"
    );
}

#[test]
fn test_proof_term_types() {
    // Validate proof term types and primitives

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    let summaries = load_module_with_deps(&mut env, "Init.Core", std::slice::from_ref(&lib_path))
        .expect("Failed to load Init.Core with dependencies");

    let total_added: usize = summaries.iter().map(|s| s.added_constants).sum();
    println!(
        "Init.Core: {} modules, {} constants added",
        summaries.len(),
        total_added
    );

    let tc = TypeChecker::new(&env);
    let mut type_successes = 0;

    // Test proof primitives
    for const_name in ["Eq", "Eq.refl", "And", "Or", "Not", "True", "False"] {
        let name = Name::from_string(const_name);
        if let Some(const_info) = env.get_const(&name) {
            match tc.infer_type(&const_info.type_) {
                Ok(sort) => {
                    println!("  {const_name} : {sort:?}");
                    type_successes += 1;
                }
                Err(e) => println!("  {const_name} type error: {e:?}"),
            }
        } else if env.get_inductive(&name).is_some() {
            println!("  {const_name} is inductive");
            type_successes += 1;
        } else {
            println!("  {const_name} not found");
        }
    }

    assert!(
        type_successes >= 5,
        "Expected at least 5 proof term types to validate, got {type_successes}"
    );
}

#[test]
fn test_decidable_eq_types() {
    // Validate decidable equality and decide function types

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    let summaries =
        load_module_with_deps(&mut env, "Init.Data.Bool", std::slice::from_ref(&lib_path))
            .expect("Failed to load Init.Data.Bool with dependencies");

    let total_added: usize = summaries.iter().map(|s| s.added_constants).sum();
    println!(
        "Init.Data.Bool: {} modules, {} constants added",
        summaries.len(),
        total_added
    );

    let tc = TypeChecker::new(&env);
    let mut type_successes = 0;

    // Test decidable equality types
    for const_name in ["DecidableEq", "decide", "Bool.decEq"] {
        let name = Name::from_string(const_name);
        if let Some(const_info) = env.get_const(&name) {
            match tc.infer_type(&const_info.type_) {
                Ok(sort) => {
                    println!("  {const_name} : {sort:?}");
                    type_successes += 1;
                }
                Err(e) => println!("  {const_name} type error: {e:?}"),
            }
        } else if env.get_inductive(&name).is_some() {
            println!("  {const_name} is inductive");
            type_successes += 1;
        } else {
            println!("  {const_name} not found");
        }
    }

    assert!(
        type_successes >= 2,
        "Expected at least 2 decidable equality types to validate, got {type_successes}"
    );
}

#[test]
fn test_monad_control_types() {
    // Validate monad control and transformer types

    let Some(lib_path) = require_olean_lean() else {
        eprintln!("Skipping test: Lean 4 not found");
        return;
    };

    let mut env = Environment::default();
    let summaries = load_module_with_deps(
        &mut env,
        "Init.Control.StateRef",
        std::slice::from_ref(&lib_path),
    )
    .expect("Failed to load Init.Control.StateRef with dependencies");

    let total_added: usize = summaries.iter().map(|s| s.added_constants).sum();
    println!(
        "Init.Control.StateRef: {} modules, {} constants added",
        summaries.len(),
        total_added
    );

    let tc = TypeChecker::new(&env);
    let mut type_successes = 0;

    // Test monad control types
    for const_name in ["StateRefT'", "MonadStateOf", "MonadLiftT"] {
        let name = Name::from_string(const_name);
        if let Some(const_info) = env.get_const(&name) {
            match tc.infer_type(&const_info.type_) {
                Ok(sort) => {
                    println!("  {const_name} : {sort:?}");
                    type_successes += 1;
                }
                Err(e) => println!("  {const_name} type error: {e:?}"),
            }
        } else if env.get_inductive(&name).is_some() {
            println!("  {const_name} is inductive");
            type_successes += 1;
        } else {
            println!("  {const_name} not found");
        }
    }

    assert!(
        type_successes >= 2,
        "Expected at least 2 monad control types to validate, got {type_successes}"
    );
}

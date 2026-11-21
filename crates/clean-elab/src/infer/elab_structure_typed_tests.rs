// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::module_batch::{elaborate_module, BatchOptions, SourceUnit, UnitId};
use crate::FileContext;
use clean_kernel::Environment;

const DATA: &str = "inductive Data where\n  | make : Data\n";

fn check(source: &str) -> (Environment, crate::module_batch::ModuleOutcome) {
    let declarations = clean_parser::parse_file(source).expect("actual source parses");
    let mut env = Environment::new();
    let mut file = FileContext::new();
    let outcome = elaborate_module(
        &mut env,
        &mut file,
        &[SourceUnit {
            id: UnitId(0),
            decls: &declarations,
        }],
        BatchOptions::islands(),
    );
    (env, outcome)
}

fn accepted(source: &str) -> Environment {
    let (env, outcome) = check(source);
    assert!(
        outcome.is_clean() && outcome.committed,
        "{}",
        outcome.render_rejections()
    );
    env
}

#[test]
fn structure_member_identity_preserves_dots_and_numeric_constructors() {
    let owner = Name::anon().str("A.B");
    let quoted_field = Name::anon().str("x.y");
    let nested_field = Name::anon().str("x").str("y");
    assert_eq!(
        structure_member_name(&owner, &quoted_field),
        owner.clone().str("x.y")
    );
    assert_eq!(
        structure_member_name(&owner, &nested_field),
        owner.clone().str("x").str("y")
    );
    assert_eq!(
        structure_member_name(&owner, &Name::anon().num(7)),
        owner.clone().num(7)
    );
    assert_ne!(
        structure_member_name(&owner, &Name::anon().str("7")),
        owner.num(7)
    );
}

#[test]
fn structure_universe_rewrite_cannot_touch_a_display_twin() {
    let owner = Name::anon().str("A.B");
    let levels = [Name::anon().str("u.v")];
    let mut folder = FilterStructSelfLevels {
        struct_name: &owner,
        keep_params: &levels,
    };
    let member = Expr::const_(owner.clone().str("x.y"), vec![]);
    let twin = Expr::const_(Name::anon().str("A").str("B").str("x.y"), vec![]);
    assert_eq!(
        folder.fold_expr(&member),
        Expr::const_(
            owner.clone().str("x.y"),
            vec![Level::param(levels[0].clone())]
        )
    );
    assert_eq!(folder.fold_expr(&twin), twin);
}

#[test]
fn structure_parent_subobject_keeps_the_exact_final_string_component() {
    assert_eq!(
        parent_subobject_name(&Name::anon().str("A.B")).unwrap(),
        Name::anon().str("toA.B")
    );
    assert_eq!(
        parent_subobject_name(&Name::anon().str("A").str("B")).unwrap(),
        Name::anon().str("toB")
    );
    assert_eq!(
        parent_subobject_name(&Name::anon().str("7")).unwrap(),
        Name::anon().str("to7")
    );
    assert!(parent_subobject_name(&Name::anon().num(7)).is_err());
    assert!(parent_subobject_name(&Name::anon()).is_err());
}

#[test]
fn structure_source_preserves_quoted_owner_constructor_and_field_names() {
    let env = accepted(&format!(
        "{DATA}structure «A.B» where\n  «7» ::\n  «x.y» : Data\nstructure A.B where\n  x : Data\n"
    ));
    let owner = Name::anon().str("A.B");
    assert!(env.get_inductive(&owner).is_some());
    assert!(env.get_const(&owner.clone().str("7")).is_some());
    assert!(env.get_const(&owner.clone().num(7)).is_none());
    assert_eq!(
        env.get_structure_field_names(&owner).unwrap(),
        &[Name::anon().str("x.y")]
    );
    assert!(env.get_const(&owner.clone().str("x.y")).is_some());
    assert!(env.get_const(&owner.str("x").str("y")).is_none());
    assert!(env
        .get_const(&Name::anon().str("A").str("B").str("mk"))
        .is_some());
}

#[test]
fn structure_inheritance_preserves_quoted_parent_and_projection_names() {
    let env = accepted(&format!("{DATA}structure «A.B» where\n  «x.y» : Data\nstructure Child extends «A.B» where\n  other : Data\n"));
    let child = Name::anon().str("Child");
    assert_eq!(
        env.get_structure_field_names(&child).unwrap(),
        &[Name::anon().str("toA.B"), Name::anon().str("other")]
    );
    assert!(env.get_const(&child.clone().str("toA.B")).is_some());
    assert!(env.get_const(&child.clone().str("toA").str("B")).is_none());
    // Inherited projections follow the existing parity setting; the embedded
    // parent field is the invariant checked here, independent of that setting.
}

#[test]
fn inductive_source_preserves_quoted_owner_and_recursive_constructor_names() {
    let env = accepted("inductive «A.B» where\n  | «0» : «A.B»\n  | «step.more» : «A.B» → «A.B»\ninductive A.B where\n  | base : A.B\n");
    let owner = Name::anon().str("A.B");
    assert!(env.get_const(&owner.clone().str("0")).is_some());
    assert!(env.get_const(&owner.clone().num(0)).is_none());
    let ctor = env.get_const(&owner.clone().str("step.more")).unwrap();
    let constants = ctor.type_.collect_constants();
    assert!(constants.contains(&owner));
    assert!(!constants.contains(&Name::anon().str("A").str("B")));
    assert!(env.get_const(&owner.str("step").str("more")).is_none());
}

#[test]
fn class_instance_preserves_quoted_class_field_and_explicit_instance_name() {
    let env = accepted(&format!("{DATA}class «C.D» where\n  «x.y» : Data\ninstance «I.J» : «C.D» where\n  «x.y» := Data.make\n"));
    let class = Name::anon().str("C.D");
    let instance = env.get_const(&Name::anon().str("I.J")).unwrap();
    assert!(instance.type_.collect_constants().contains(&class));
    assert!(instance
        .value
        .as_ref()
        .unwrap()
        .collect_constants()
        .contains(&class.str("mk")));
    assert!(env.get_const(&Name::anon().str("I").str("J")).is_none());
}

#[test]
fn instance_source_value_field_cannot_be_confused_with_short_form_marker() {
    for field in ["_value", "«_value»"] {
        let env = accepted(&format!("{DATA}class C where\n  {field} : Data\ninstance witness : C where\n  {field} := Data.make\n"));
        let instance = env.get_const(&Name::anon().str("witness")).unwrap();
        assert!(instance
            .value
            .as_ref()
            .unwrap()
            .collect_constants()
            .contains(&Name::anon().str("C").str("mk")));
    }
    accepted(&format!(
        "{DATA}class C where\n  value : Data\ninstance witness : C := ⟨Data.make⟩\n"
    ));
}

#[test]
fn instance_unknown_or_duplicate_field_cannot_discard_an_assignment() {
    for fields in [
        "  value := Data.make\n  «value» := Data.make\n",
        "  value := Data.make\n  «extra.field» := unknownValue\n",
    ] {
        let (env, outcome) = check(&format!(
            "{DATA}class C where\n  value : Data\ninstance witness : C where\n{fields}"
        ));
        assert!(!outcome.is_clean() && !outcome.committed);
        assert!(env.get_const(&Name::anon().str("witness")).is_none());
    }
}

#[test]
fn class_output_dependency_refusal_restores_the_typed_local_scope() {
    let env = Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);
    let kept = clean_kernel::FVarId::new(40);
    ctx.push_local_let_with_fvar(
        SurfaceName::from_name(Name::from_string("kept")),
        kept,
        Expr::const_(Name::from_string("Nat"), vec![]),
        Expr::nat_lit(7),
    );
    let old_values = ctx.locals.let_values().clone();
    assert_eq!(old_values.get(&kept), Some(&Expr::nat_lit(7)));
    let old_binders = ctx.locals.binder_infos().clone();
    let bad =
        clean_parser::parse_file("class Retry (α : outParam Type) (x : α) where\n  val : α\n")
            .unwrap()
            .pop()
            .unwrap();
    let error = ctx
        .elab_decl(&bad)
        .expect_err("invalid class must refuse before publication");
    assert!(error
        .to_string()
        .contains("parameter #2 depends on `outParam`"));
    assert_eq!(ctx.locals.len(), 1);
    assert_eq!(ctx.locals[0].1, kept);
    assert_eq!(ctx.locals.let_values(), &old_values);
    assert_eq!(ctx.locals.binder_infos(), &old_binders);
    assert!(ctx.local_instances.is_empty());
    assert!(ctx
        .instances
        .get_class(&Name::from_string("Retry"))
        .is_none());
    let good = clean_parser::parse_file(
        "class Retry (α : outParam Type) (x : outParam α) where\n  val : α\n",
    )
    .unwrap()
    .pop()
    .unwrap();
    ctx.elab_decl(&good)
        .expect("valid retry sees no leaked class locals");
    assert_eq!(ctx.locals.len(), 1);
    assert_eq!(ctx.locals[0].1, kept);
}

#[test]
fn section_family_pruning_balances_zero_and_multiple_projection_scopes() {
    let env = Environment::with_prelude();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let kept = SurfaceName::generated_path("kept");
    let unused = SurfaceName::generated_path("unused");
    for source in [
        "variable (unused : Nat)\nstructure ScopeEmpty where\naxiom Later : kept = kept\n",
        "variable (unused : Nat)\nstructure ScopePair where\n  left : Nat\n  right : Nat\naxiom Later : kept = kept\n",
    ] {
        let mut ctx = ElabCtx::new(&env);
        let outer = ctx.push_local(kept.clone(), nat.clone());
        let mut file = FileContext::new();
        let ds = clean_parser::parse_file(source).expect("parse structures and sibling");
        let _ = crate::preprocess_decl_with_context(&ds[0], &mut file);
        let family = crate::preprocess_decl_with_context(&ds[1], &mut file);
        ctx.elab_decl(&family).expect("elaborate structure");
        assert_eq!(ctx.locals.len(), 1, "surrounding context after structure");
        assert_eq!(ctx.lookup_local(&kept).map(|(id, _)| id), Some(outer));
        assert!(ctx.lookup_local(&unused).is_none());
        ctx.elab_decl(&ds[2]).expect("following declaration can still use kept");
    }
}

#[test]
fn section_family_refusal_restores_ambient_locals_and_instances() {
    let env = Environment::with_prelude();
    for invalid in [
        "structure Bad where\n  bad : Nat 0",
        "inductive Bad where\n  | mk (bad : Nat 0) : Bad",
    ] {
        let code = format!(
            "variable {{α : Type}} [inst : Inhabited α]\n{invalid}\naxiom Later : kept = kept\n"
        );
        let ds = clean_parser::parse_file(&code).expect("parse ill-typed field");
        let mut ctx = ElabCtx::new(&env);
        let kept = SurfaceName::generated_path("kept");
        let id = ctx.push_local(kept.clone(), Expr::const_(Name::from_string("Nat"), vec![]));
        let mut file = FileContext::new();
        let _ = crate::preprocess_decl_with_context(&ds[0], &mut file);
        let family = crate::preprocess_decl_with_context(&ds[1], &mut file);
        assert!(ctx.elab_decl(&family).is_err());
        assert_eq!(ctx.locals.len(), 1);
        assert_eq!(ctx.lookup_local(&kept).map(|(i, _)| i), Some(id));
        assert!(ctx.local_instances.is_empty());
        ctx.elab_decl(&ds[2]).expect("unaffected sibling");
    }
}

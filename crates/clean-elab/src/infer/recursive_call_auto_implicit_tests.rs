// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
// `Name` is imported HERE rather than inherited through `use super::*`.
// The parent (`recursive_call.rs`) does not use it outside this cfg(test)
// child, so a lib-target `clippy --fix` removes it there -- and this file
// then fails `--cfg test` with ten E0433s. Naming it directly keeps the lib
// unit free of an unused import AND this module compiling.
use clean_kernel::{Environment, Level, Name};

fn context(parameters: Vec<RecursiveParam>) -> RecursiveDefContext {
    RecursiveDefContext {
        func_name: SurfaceName::component("count", false),
        decreasing_arg_pos: 0,
        decreasing_arg_name: SurfaceName::component("xs", false),
        inductive_type_name: None,
        ih_fvar: None,
        ih_type: None,
        ih_map: Default::default(),
        sibling_names: Vec::new(),
        sibling_types: Vec::new(),
        parameters,
        generalized_params: Vec::new(),
        index_params: Vec::new(),
        wf_measure: None,
        outer_locals_floor: None,
    }
}

#[test]
fn header_packet_preserves_order_identity_and_dependent_domains() {
    let env = Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);
    let name = SurfaceName::component("A.B", true);
    let alpha = ctx.add_auto_implicit(name.clone(), Expr::sort(Level::succ(Level::zero())));
    let element = ctx.add_auto_implicit(SurfaceName::component("x", false), Expr::fvar(alpha));
    let shadow = ctx.push_local(name.clone(), Expr::fvar(alpha));
    let original = RecursiveParam {
        name,
        binder_info: BinderInfo::Default,
        captured_section: false,
        fvar: shadow,
        type_: Expr::fvar(alpha),
    };
    ctx.recursive_def_ctx = Some(context(vec![original.clone()]));
    let packet = ctx.snapshot_auto_implicits_since(0);
    ctx.capture_recursive_auto_implicit_parameters()
        .expect("capture header packet");
    let parameters = ctx.recursive_def_ctx.as_ref().unwrap().parameters.clone();
    assert_eq!(
        parameters.iter().map(|p| p.fvar).collect::<Vec<_>>(),
        vec![alpha, element, shadow]
    );
    assert_eq!(parameters[0].binder_info, BinderInfo::Implicit);
    assert_eq!(parameters[1].binder_info, BinderInfo::Implicit);
    assert_eq!(parameters[1].type_, Expr::fvar(alpha));
    assert_eq!(parameters[2], original);
    assert!(parameters[0].name.same_syntax(&parameters[2].name));
    assert_ne!(parameters[0].fvar, parameters[2].fvar);
    assert_eq!(
        ctx.recursive_def_ctx
            .as_ref()
            .unwrap()
            .decreasing_binder_index(),
        Some(2)
    );
    ctx.capture_recursive_auto_implicit_parameters()
        .expect("capture header packet");
    assert_eq!(
        ctx.recursive_def_ctx.as_ref().unwrap().parameters,
        parameters
    );
    assert_eq!(ctx.snapshot_auto_implicits_since(0), packet);
}

#[test]
fn local_recursive_helper_does_not_import_outer_header_parameters() {
    let env = Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);
    ctx.add_auto_implicit(
        SurfaceName::component("alpha", false),
        Expr::sort(Level::succ(Level::zero())),
    );
    let n = ctx.push_local(
        SurfaceName::component("n", false),
        Expr::const_(Name::anon().str("Nat"), vec![]),
    );
    let parameters = vec![RecursiveParam {
        name: SurfaceName::component("n", false),
        binder_info: BinderInfo::Default,
        captured_section: false,
        fvar: n,
        type_: Expr::const_(Name::anon().str("Nat"), vec![]),
    }];
    ctx.recursive_def_ctx = Some(context(parameters.clone()));
    ctx.in_term_body = true;
    ctx.capture_recursive_auto_implicit_parameters()
        .expect("capture header packet");
    assert_eq!(
        ctx.recursive_def_ctx.as_ref().unwrap().parameters,
        parameters
    );
    assert_eq!(ctx.auto_implicit_count(), 1);
}

#[test]
fn header_packet_restores_recursive_parameters_after_body_success_and_error() {
    let env = Environment::with_prelude();
    for body in ["0", "unknownBodyName"] {
        let mut ctx = ElabCtx::new(&env);
        ctx.in_decl_context = true;
        ctx.add_auto_implicit(
            SurfaceName::component("A", false),
            Expr::sort(Level::succ(Level::zero())),
        );
        let n = ctx.push_local(
            SurfaceName::component("n", false),
            Expr::const_(Name::anon().str("Nat"), vec![]),
        );
        let parameters = vec![RecursiveParam {
            name: SurfaceName::component("n", false),
            binder_info: BinderInfo::Default,
            captured_section: false,
            fvar: n,
            type_: Expr::const_(Name::anon().str("Nat"), vec![]),
        }];
        ctx.recursive_def_ctx = Some(context(parameters.clone()));
        let packet = ctx.snapshot_auto_implicits_since(0);
        let ty = clean_parser::parse_expr("Nat").unwrap();
        let value = clean_parser::parse_expr(body).unwrap();
        let result = ctx.elab_def_body(&[], Some(&ty), &value);
        assert_eq!(result.is_ok(), body == "0", "{result:?}");
        if body != "0" {
            assert!(
                result
                    .as_ref()
                    .err()
                    .and_then(ElabError::unknown_ident_name)
                    .is_some(),
                "{result:?}"
            );
        }
        assert_eq!(
            ctx.recursive_def_ctx.as_ref().unwrap().parameters,
            parameters
        );
        assert_eq!(ctx.snapshot_auto_implicits_since(0), packet);
        assert!(!ctx.in_term_body);
    }
}

fn run_source(source: &str) -> (Environment, Vec<Result<crate::ElabResult, ElabError>>) {
    let mut env = Environment::with_prelude();
    let mut file = crate::FileContext::new();
    let declarations = clean_parser::parse_file(source).expect("actual source parses");
    let results = declarations
        .iter()
        .map(|decl| {
            let decl = crate::preprocess_decl_with_context(decl, &mut file);
            crate::elaborate_decl_and_register_with_context(&mut env, &decl, &mut file)
        })
        .collect();
    (env, results)
}

const VECTOR: &str = "inductive AutoVec (α : Type) : Nat → Type where\n  | nil : AutoVec α 0\n  | cons : α → AutoVec α n → AutoVec α (n+1)\n";

#[test]
fn auto_and_written_index_headers_both_compute_and_kernel_register() {
    for header in ["", "{α : Type} {n : Nat}"] {
        let source = format!("{VECTOR}def count {header} : AutoVec α n → Nat | .nil => 0 | .cons _ t => count t + 1\ntheorem count_two : count (.cons 1 (.cons 2 .nil)) = 2 := rfl");
        let (env, results) = run_source(&source);
        assert_eq!(results.len(), 3);
        assert!(results.iter().all(Result::is_ok), "{header}: {results:?}");
        assert!(env.get_const(&Name::anon().str("count_two")).is_some());
    }
    for header in ["", "{m n : Nat}"] {
        let source = format!("inductive AutoLE : Nat → Nat → Type where\n  | refl : AutoLE n n\n  | step : AutoLE m n → AutoLE m (n+1)\ndef gap {header} : AutoLE m n → Nat | .refl => 0 | .step h => gap h + 1\ntheorem gap_two : gap (.step (.step (.refl : AutoLE 3 3))) = 2 := rfl");
        let (env, results) = run_source(&source);
        assert_eq!(results.len(), 3);
        assert!(results.iter().all(Result::is_ok), "{header}: {results:?}");
        assert!(env.get_const(&Name::anon().str("gap_two")).is_some());
    }
}

#[test]
fn auto_header_wrong_result_fails_only_after_recursive_definition_registers() {
    let source = format!("{VECTOR}def count : AutoVec α n → Nat | .nil => 0 | .cons _ t => count t + 1\ntheorem count_wrong : count (.cons 1 (.cons 2 .nil)) = 3 := rfl");
    let (env, results) = run_source(&source);
    assert_eq!(results.len(), 3);
    assert!(results[0].is_ok() && results[1].is_ok(), "{results:?}");
    assert!(results[2].is_err(), "wrong value must not kernel-register");
    assert!(env.get_const(&Name::anon().str("count")).is_some());
    assert!(env.get_const(&Name::anon().str("count_wrong")).is_none());
}

#[test]
fn auto_header_supplied_wrong_fixed_type_and_wrong_index_remain_rejected() {
    let positive = format!("{VECTOR}def count : AutoVec α n → Nat | .nil => 0 | .cons _ t => @count α _ t + 1\ntheorem count_two : count (.cons 1 (.cons 2 .nil)) = 2 := rfl");
    let (env, results) = run_source(&positive);
    assert_eq!(results.len(), 3);
    assert!(
        results.iter().all(Result::is_ok),
        "explicit supplied-argument control: {results:?}"
    );
    assert!(env.get_const(&Name::anon().str("count_two")).is_some());
    for recursive_call in ["@count Bool n t", "@count α (n+1) t"] {
        let source = format!(
            "{VECTOR}def count : AutoVec α n → Nat | .nil => 0 | .cons _ t => {recursive_call} + 1"
        );
        let (env, results) = run_source(&source);
        assert_eq!(results.len(), 2);
        assert!(results[0].is_ok(), "setup must pass: {results:?}");
        assert!(
            matches!(results[1], Err(ElabError::TypeMismatch { .. })),
            "{recursive_call}: {results:?}"
        );
        assert!(env.get_const(&Name::anon().str("count")).is_none());
    }
}

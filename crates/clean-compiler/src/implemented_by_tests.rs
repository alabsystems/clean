// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! [`runtime_const_name`] follows a chain to its end, and names a cycle, a
//! missing link and an `unsafe` end instead of returning a body to compile.

use super::*;

fn n(s: &str) -> Name {
    Name::from_string(s)
}

#[test]
fn test_runtime_const_name_follows_chain_to_end() {
    let mut env = Environment::with_prelude();
    assert_eq!(
        runtime_const_name(&env, &n("Nat.succ")).expect("no binding"),
        n("Nat.succ")
    );

    env.register_implemented_by(n("Nat.add"), n("Nat.mul"));
    env.register_implemented_by(n("Nat.mul"), n("Nat.sub"));
    assert_eq!(
        runtime_const_name(&env, &n("Nat.add")).expect("an acyclic chain"),
        n("Nat.sub"),
        "the END of the chain runs, as in Lean"
    );
    assert_eq!(
        runtime_const_name(&env, &n("Nat.mul")).expect("an acyclic chain"),
        n("Nat.sub")
    );

    // An `unsafe` link that is not the end never runs: not refused.
    env.mark_unsafe(n("Nat.mul"));
    assert_eq!(
        runtime_const_name(&env, &n("Nat.add")).expect("only the end runs"),
        n("Nat.sub")
    );
}

#[test]
fn test_runtime_const_name_names_cycle_missing_and_unsafe_end() {
    let mut env = Environment::with_prelude();
    env.register_implemented_by(n("Nat.add"), n("Nat.mul"));
    env.register_implemented_by(n("Nat.mul"), n("Nat.add"));
    let err = runtime_const_name(&env, &n("Nat.add")).expect_err("a cycle must be named");
    assert!(
        matches!(&err, CompilerError::ImplementedByCycle { decl, repeated }
            if decl == &n("Nat.add") && repeated == &n("Nat.add")),
        "{err:?}"
    );
    assert!(err.to_string().ends_with("(implemented-by-cycle)"), "{err}");

    env.register_implemented_by(n("Nat.pow"), n("ws_absent_target"));
    match runtime_const_name(&env, &n("Nat.pow")) {
        Err(err @ CompilerError::ImplementedByMissingTarget { .. }) => {
            let text = err.to_string();
            assert!(
                text.starts_with("`Nat.pow` is @[implemented_by ws_absent_target]"),
                "{text}"
            );
            assert!(text.ends_with("(implemented-by)"), "{text}");
        }
        other => panic!("a missing target must be named, got {other:?}"),
    }

    // `s → u` with `u` unsafe, and `s → m → u`.
    env.register_implemented_by(n("Nat.sub"), n("Nat.div"));
    env.mark_unsafe(n("Nat.div"));
    env.register_implemented_by(n("Nat.mod"), n("Nat.sub"));
    for decl in ["Nat.sub", "Nat.mod"] {
        match runtime_const_name(&env, &n(decl)) {
            Err(err @ CompilerError::ImplementedByUnsafeTarget { .. }) => {
                let text = err.to_string();
                assert!(text.contains("implemented_by"), "{text}");
                assert!(text.contains("Nat.div"), "{text}");
                assert!(text.contains("`unsafe`"), "{text}");
                assert!(text.ends_with("(implemented-by)"), "{text}");
            }
            other => panic!("{decl}: an unsafe end must be named, got {other:?}"),
        }
    }
}

#[test]
fn test_has_compiler_attr_reads_both_registries() {
    let mut env = Environment::with_prelude();
    assert!(!has_compiler_attr(&env, &n("Nat.add")));
    env.register_extern(n("Nat.add"), "my_add".to_owned());
    assert!(has_compiler_attr(&env, &n("Nat.add")));
    assert!(!has_compiler_attr(&env, &n("Nat.mul")));
    env.register_implemented_by(n("Nat.mul"), n("Nat.add"));
    assert!(has_compiler_attr(&env, &n("Nat.mul")));
}

/// Under [`CodeMeaning::KernelValue`] a reference runs the constant it names,
/// whatever its binding, and the order record refuses nothing.
#[test]
fn test_kernel_value_meaning_substitutes_nothing() {
    let mut env = Environment::with_prelude();
    env.register_implemented_by(n("Nat.add"), n("Nat.mul"));
    env.register_implemented_by(n("Nat.pow"), n("ws_absent_target"));
    for name in ["Nat.add", "Nat.pow", "Nat.succ"] {
        assert_eq!(
            runtime_const_name_for(&env, &n(name), CodeMeaning::KernelValue).expect("no lookup"),
            n(name)
        );
    }
    assert_eq!(
        runtime_const_name_for(&env, &n("Nat.add"), CodeMeaning::LeanCompiled).expect("a chain"),
        n("Nat.mul")
    );
    record_order(
        &mut env,
        vec![(
            n("Nat.sub"),
            CompiledBefore {
                rebound: n("Nat.add"),
                via: n("Nat.add"),
            },
        )],
    );
    assert!(refuse_order_for(&env, CodeMeaning::LeanCompiled).is_err());
    assert!(refuse_order_for(&env, CodeMeaning::KernelValue).is_ok());
}

/// A link whose implementation has another type in this environment is
/// named, not followed (`docs/DECISIONS.md` R149: an imported binding's names
/// may resolve to resident declarations). `Nat.succ : Nat → Nat` cannot
/// implement `Nat.add : Nat → Nat → Nat`.
#[test]
fn test_runtime_const_name_names_a_type_mismatch() {
    let mut env = Environment::with_prelude();
    env.register_implemented_by(n("Nat.add"), n("Nat.succ"));
    match runtime_const_name(&env, &n("Nat.add")) {
        Err(err @ CompilerError::ImplementedByTypeMismatch { .. }) => {
            let text = err.to_string();
            assert!(
                text.starts_with("`Nat.add` is @[implemented_by Nat.succ]"),
                "{text}"
            );
            assert!(text.ends_with("(implemented-by)"), "{text}");
        }
        other => panic!("a type mismatch must be named, got {other:?}"),
    }
    // Same type: followed.
    env.register_implemented_by(n("Nat.add"), n("Nat.mul"));
    assert_eq!(
        runtime_const_name(&env, &n("Nat.add")).expect("same type"),
        n("Nat.mul")
    );
}

/// `externBody : Nat → Nat := fun n => Nat.add n n`, bound to a symbol: the
/// lowering of what compiled Lean runs refuses its body at both entries
/// (Lean calls the symbol), and the kernel-value lowering lowers it. Before
/// the refusal, `constant_to_decl` lowered the body.
#[test]
fn test_extern_with_body_refused_under_lean_compiled_only() {
    use clean_kernel::{BinderInfo, Declaration, Expr};
    let mut env = Environment::with_prelude();
    let nat = Expr::const_str("Nat");
    env.add_decl(Declaration::Definition {
        name: n("externBody"),
        level_params: vec![],
        type_: Expr::arrow(nat.clone(), nat.clone()),
        value: Expr::lam(
            BinderInfo::Default,
            nat,
            Expr::apps(Expr::const_str("Nat.add"), [Expr::bvar(0), Expr::bvar(0)]),
        ),
        is_reducible: false,
    })
    .expect("externBody is well-typed");
    let info = env.get_const(&n("externBody")).expect("added").clone();
    let lowered = crate::to_lcnf::constant_to_decl(&env, &info)
        .expect("no attribute yet: the body lowers")
        .expect("a definition is code");
    env.register_extern(n("externBody"), "clean_extern_body_test_symbol".to_owned());
    let err = crate::to_lcnf::constant_to_decl(&env, &info)
        .expect_err("compiled Lean never runs an @[extern] body");
    assert!(
        matches!(&err, CompilerError::ExternWithBody { decl, symbol }
            if decl == &n("externBody") && symbol == "clean_extern_body_test_symbol"),
        "{err:?}"
    );
    assert!(err.to_string().contains("(extern-body)"), "{err}");
    assert!(
        crate::to_lcnf::constant_to_decl_with_meaning(&env, &info, CodeMeaning::KernelValue)
            .expect("the kernel value is the body")
            .is_some()
    );
    let batch = crate::pass_manager::compile_lcnf_decls(
        std::slice::from_ref(&lowered),
        &env,
        &crate::pass_manager::PipelineConfig::default(),
    );
    let Err(err) = batch else {
        panic!("the pipeline must refuse a lowered @[extern] body");
    };
    assert!(err.to_string().contains("(extern-body)"), "{err}");
}

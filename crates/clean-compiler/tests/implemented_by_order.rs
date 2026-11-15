// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The ORDER refusal at the lowering every lane shares.
//!
//! `attribute [implemented_by fast] slow` written AFTER `caller`, which
//! reaches `slow`: pinned Lean v4.30.0-rc2 compiled `caller` before the
//! binding, and which body it runs then is its inliner's choice (battery rows
//! `attr_implemented_by_order*`: the `@[noinline]` caller prints the old `3`).
//! clean-elab records `caller` in the environment's order record
//! (`clean_compiler::implemented_by_order`). Trust's general lane elaborates
//! such a source through `clean_elab::module_batch` (`BatchOptions::islands()`)
//! and lowers each declaration with `clean_compiler::constant_to_decl`
//! (`collect_general_clean_ir`, then `compile_lcnf_to_trust_ir_with_report`),
//! which substituted `fast` into `caller` (`caller 1` = 2, Lean 3). Every
//! public lowering entry now refuses while the record is not empty:
//! `constant_to_decl`, `expr_to_code` and the batch pipeline
//! (`pass_manager::compile_lcnf_decls`, under every `compile_lcnf_*`).
//!
//! An integration test, so the binary links ONE copy of clean-compiler: the
//! record clean-elab writes is the one this crate reads. The crate's own
//! unit-test binary links two (the crate under test and clean-elab's), and
//! there the record clean-elab writes is invisible.

use clean_compiler::lcnf::{Decl, DeclValue, LetDecl, LetValue};
use clean_compiler::pass_manager::{compile_lcnf_decls, compile_lcnf_decls_for, PipelineConfig};
use clean_compiler::{
    constant_to_decl, constant_to_decl_with_meaning, implemented_by_order, CodeMeaning, CodeVisitor,
};
use clean_elab::module_batch::{elaborate_module, BatchOptions, SourceUnit, UnitId};
use clean_kernel::{Environment, Name};

const TAG: &str = "(implemented-by-order)";

/// `attr_implemented_by_order_noinline`, without its `main`.
const LATE: &str = "def fast (n : Nat) : Nat := n + 1\n\
                    @[noinline] def slow (n : Nat) : Nat := n + 2\n\
                    @[noinline] def caller (n : Nat) : Nat := slow n\n\
                    attribute [implemented_by fast] slow\n";

/// The same declarations with the binding on `slow` itself: no order record.
const ON_DECL: &str = "def fast (n : Nat) : Nat := n + 1\n\
                       @[noinline, implemented_by fast] def slow (n : Nat) : Nat := n + 2\n\
                       @[noinline] def caller (n : Nat) : Nat := slow n\n";

/// `source` elaborated the way Trust's island lane elaborates an island
/// (`trust_certify::clean_island_batch`): one unit of a header-first batch
/// over the prelude, `BatchOptions::islands()`.
fn island_env(source: &str) -> Environment {
    let patterns = clean_elab::tactic::builtins::builtin_tactic_patterns();
    let decls =
        clean_parser::parse_file_with_tactics(source, &patterns).expect("the island parses");
    let mut env = Environment::with_prelude();
    let mut file_ctx = clean_elab::FileContext::new();
    let units = [SourceUnit {
        id: UnitId(0),
        decls: &decls,
    }];
    let report = elaborate_module(&mut env, &mut file_ctx, &units, BatchOptions::islands())
        .render_rejections();
    assert!(report.is_empty(), "the island elaborates:\n{report}");
    env
}

/// `name` lowered as Trust's general lane lowers it.
fn lower(env: &Environment, name: &str) -> Result<Option<Decl>, clean_compiler::CompilerError> {
    let info = env
        .get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("`{name}` is in the environment"));
    constant_to_decl(env, info)
}

/// The constants a lowered body calls.
struct Calls;

impl CodeVisitor for Calls {
    type Result = Vec<String>;

    fn combine(&self, mut a: Vec<String>, b: Vec<String>) -> Vec<String> {
        a.extend(b);
        a
    }

    fn visit_let(&mut self, decl: &LetDecl, body: &clean_compiler::lcnf::Code) -> Vec<String> {
        let mut found = match &decl.value {
            LetValue::Const { name, .. } => vec![name.to_string()],
            _ => Vec::new(),
        };
        found.extend(self.visit_code(body));
        found
    }
}

fn calls(decl: &Decl) -> Vec<String> {
    match &decl.body {
        DeclValue::Code(code) => Calls.visit_code(code),
        other => panic!("`{}` lowered to code, got {other:?}", decl.name),
    }
}

/// The refusal names the tag, the rebound declaration and the referrer.
fn assert_order_refusal(err: &clean_compiler::CompilerError, what: &str) {
    let text = err.to_string();
    assert!(text.contains(TAG), "{what}: {text}");
    assert!(text.contains("`slow`"), "{what}: {text}");
    assert!(text.contains("`caller` names `slow`"), "{what}: {text}");
}

/// Trust's general lane: the batch accepts the late command and records
/// `caller`; `constant_to_decl` then refuses every declaration of the
/// environment by name, one that never reaches `slow` included, where it
/// used to lower `caller` calling `fast`. The control: with the binding on
/// the declaration there is no record, and `caller` lowers calling `fast`, as
/// Lean compiles it.
#[test]
fn test_constant_to_decl_refuses_every_declaration_after_a_late_implemented_by_command() {
    let control = island_env(ON_DECL);
    assert!(implemented_by_order(&control).is_none());
    let caller = lower(&control, "caller")
        .expect("no late binding: `caller` lowers")
        .expect("`caller` is code");
    assert!(
        calls(&caller).contains(&"fast".to_string()),
        "{:?}",
        calls(&caller)
    );

    let env = island_env(LATE);
    let recorded: Vec<String> = implemented_by_order(&env)
        .expect("the batch records the late command")
        .keys()
        .map(ToString::to_string)
        .collect();
    assert_eq!(recorded, vec!["caller".to_string()]);
    for name in ["caller", "fast", "slow"] {
        match lower(&env, name) {
            Err(err) => assert_order_refusal(&err, name),
            Ok(lowered) => panic!(
                "`{name}` lowered in an environment with a late binding: {:?}",
                lowered.as_ref().map(calls)
            ),
        }
    }
}

/// The batch pipeline every `compile_lcnf_*` entry runs refuses too, so a
/// caller that lowered its declarations before the command and compiles them
/// after it cannot bypass the refusal. The control: the same declarations
/// compile against the environment before the command.
#[test]
fn test_batch_pipeline_refuses_after_a_late_implemented_by_command() {
    let mut env = Environment::with_prelude();
    let mut file_ctx = clean_elab::FileContext::new();
    let elaborate = |env: &mut Environment, file_ctx: &mut clean_elab::FileContext, src: &str| {
        for decl in clean_parser::parse_file(src).expect("the source parses") {
            let processed = clean_elab::preprocess_decl_with_context(&decl, file_ctx);
            clean_elab::elaborate_decl_and_register_with_context(env, &processed, file_ctx)
                .unwrap_or_else(|e| panic!("`{src}` elaborates: {e}"));
        }
    };
    elaborate(
        &mut env,
        &mut file_ctx,
        "def fast (n : Nat) : Nat := n + 1\n\
         def slow (n : Nat) : Nat := n + 2\n\
         def caller (n : Nat) : Nat := slow n\n",
    );
    let decls: Vec<Decl> = ["caller", "slow"]
        .iter()
        .map(|name| {
            lower(&env, name)
                .expect("no late binding yet")
                .expect("code")
        })
        .collect();
    compile_lcnf_decls(&decls, &env, &PipelineConfig::default())
        .expect("the batch compiles before the command");

    elaborate(
        &mut env,
        &mut file_ctx,
        "attribute [implemented_by fast] slow\n",
    );
    match compile_lcnf_decls(&decls, &env, &PipelineConfig::default()) {
        Err(clean_compiler::pass_manager::PipelineError::Compiler(err)) => {
            assert_order_refusal(&err, "compile_lcnf_decls");
        }
        Err(other) => panic!("expected the order refusal, got {other}"),
        Ok(_) => panic!("the batch compiled in an environment with a late binding"),
    }
}

/// The kernel-value lowering (`clean extract`, `docs/DECISIONS.md` R149)
/// substitutes nothing: `caller` calls `slow` itself, with the binding on the
/// declaration and after the late command alike, and neither the lowering
/// nor the batch pipeline takes the order refusal, which is about which body
/// Lean's compiled code runs. The compiled-Lean lowering of the same
/// environments is unchanged (the tests above).
#[test]
fn test_kernel_value_lowering_substitutes_nothing_and_takes_no_order_refusal() {
    for (source, recorded) in [(ON_DECL, false), (LATE, true)] {
        let env = island_env(source);
        assert_eq!(implemented_by_order(&env).is_some(), recorded);
        let decls: Vec<Decl> = ["caller", "slow", "fast"]
            .iter()
            .map(|name| {
                let info = env
                    .get_const(&Name::from_string(name))
                    .unwrap_or_else(|| panic!("`{name}` is in the environment"));
                constant_to_decl_with_meaning(&env, info, CodeMeaning::KernelValue)
                    .unwrap_or_else(|e| panic!("`{name}` lowers at the kernel value: {e}"))
                    .unwrap_or_else(|| panic!("`{name}` is code"))
            })
            .collect();
        let called = calls(&decls[0]);
        assert!(
            called.contains(&"slow".to_string()) && !called.contains(&"fast".to_string()),
            "{source}: {called:?}"
        );
        compile_lcnf_decls_for(
            &decls,
            &env,
            &PipelineConfig::default(),
            CodeMeaning::KernelValue,
        )
        .unwrap_or_else(|e| panic!("{source}: the kernel-value batch compiles: {e}"));
    }
}

/// `expr_to_code`, the other public lowering entry, refuses as well.
#[test]
fn test_expr_to_code_refuses_after_a_late_implemented_by_command() {
    let env = island_env(LATE);
    let value = env
        .get_const(&Name::from_string("caller"))
        .and_then(|info| info.value.clone())
        .expect("`caller` has a value");
    let mut ctx = clean_compiler::to_lcnf::LcnfContext::new(&env);
    match clean_compiler::expr_to_code(&mut ctx, &value) {
        Err(err) => assert_order_refusal(&err, "expr_to_code"),
        Ok(code) => panic!("`caller`'s value lowered: {code:?}"),
    }
}

/// The Rust ABI (`compile_rust_abi`) refuses every root by name after the
/// late command, one that never reaches `slowW` included, as the native lanes
/// do (`native-implemented-by-order`); it compiled them, substituting `fastW`
/// into `callerW`. The record is the one clean-elab writes for the real
/// source (it used to be written by hand in the crate's unit-test binary,
/// which links two copies of this crate). The control: with the binding on
/// the declaration, both batches compile.
#[cfg(feature = "trust-ir-backend")]
mod rust_abi {
    use super::{island_env, TAG};
    use clean_compiler::pass_manager::PipelineConfig;
    use clean_compiler::rust_abi::{compile_rust_abi, RustAbiError, RustAbiOutput};
    use clean_kernel::{Environment, Name};

    /// The target Trust's general lane stamps on an aarch64 host.
    fn trust_target() -> trust_ir::TargetInfo {
        trust_ir::TargetInfo {
            triple: "aarch64-apple-darwin".to_string(),
            pointer_size: 8,
            endianness: trust_ir::Endianness::Little,
            abi: None,
            struct_passing: trust_ir::StructPassingPolicy::Unclassified,
        }
    }

    fn rust_abi(env: &Environment, roots: &[&str]) -> Result<RustAbiOutput, RustAbiError> {
        let roots: Vec<Name> = roots.iter().map(|r| Name::from_string(r)).collect();
        compile_rust_abi(
            env,
            &roots,
            &[],
            &PipelineConfig::default(),
            "clean-rust-abi::order",
            &trust_target(),
        )
    }

    const DECLS: &str = "def fastW (a : UInt64) : UInt64 := a + 1\n";
    const REST: &str = "def callerW (a : UInt64) : UInt64 := slowW a\n\
                        def otherW (a : UInt64) : UInt64 := a + 3\n";

    #[test]
    fn test_rust_abi_refuses_every_root_after_a_late_implemented_by_command() {
        // `callerW` runs `fastW`, which joins its batch.
        let batches: [&[&str]; 2] = [&["callerW", "fastW"], &["otherW"]];
        let control = island_env(&format!(
            "{DECLS}@[implemented_by fastW] def slowW (a : UInt64) : UInt64 := a + 2\n{REST}"
        ));
        for roots in batches {
            rust_abi(&control, roots)
                .unwrap_or_else(|e| panic!("{roots:?} compiles with no late binding: {e}"));
        }

        let env = island_env(&format!(
            "{DECLS}def slowW (a : UInt64) : UInt64 := a + 2\n{REST}\
             attribute [implemented_by fastW] slowW\n"
        ));
        for roots in batches {
            let err = rust_abi(&env, roots)
                .expect_err("no root of an environment with a late binding compiles");
            match &err {
                RustAbiError::Conflict { name, detail } => {
                    assert_eq!(name, roots[0]);
                    assert!(detail.contains(TAG), "{err}");
                    assert!(detail.contains("`callerW` names `slowW`"), "{err}");
                }
                other => panic!("expected {roots:?} refused by name, got {other:?}"),
            }
        }
    }
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Trust plan step 3.2 — Clean's compiler at the Rust ABI.
//!
//! A child of `emit_trust_ir`, so the `trust-ir-backend-lib` gate leg
//! (`-- emit_trust_ir`) runs it and every child below.
//!
//! The subjects are the two the Trust design
//! (`docs/design/2026-10-02-step3-lean-through-trust-ir.md` §1.5) measured:
//! the 64-bit `a + b` (`cleanWsum`, Trust's
//! `tests/run-make/trust-cg-clean-origin-below-gate`) and Lean-calls-Rust
//! (`twice_inc := inc (inc x)`, Trust's
//! `tests/two-language-programs/r18_lean_calls_rust`), plus the scalar,
//! `Bool` and `Nat` shapes of Trust's planner battery. Each island is built
//! the way Trust builds one: the prelude, the Rust callees declared as Trust's
//! `declare_rust_callees` declares them (a kernel `Opaque` with a hidden
//! inhabitant), then the island source elaborated and kernel-checked.

use super::*;
use crate::pass_manager::{compile_lcnf_to_trust_ir_with_report, PipelineConfig};
use crate::rust_abi::{compile_rust_abi, RustAbiError, RustAbiOutput, RustCallee};
use crate::to_lcnf::constant_to_decl;
use clean_kernel::env::Declaration;
use clean_kernel::{BinderInfo, Environment, Expr};
use trust_ir::inst::Inst;

#[path = "emit_trust_ir_rust_abi_digest_tests.rs"]
mod digest;
#[path = "emit_trust_ir_rust_abi_e2e_tests.rs"]
mod e2e;
#[path = "emit_trust_ir_rust_abi_nat_tests.rs"]
mod nat;
#[path = "emit_trust_ir_rust_abi_prims_tests.rs"]
mod prims;
#[path = "emit_trust_ir_rust_abi_resolve_tests.rs"]
mod resolve;
#[path = "emit_trust_ir_rust_abi_signature_tests.rs"]
mod signatures;

/// Subject 1 — the 64-bit add.
pub(super) const WSUM: &str = "def cleanWsum (a b : UInt64) : UInt64 := a + b\n";

/// Subject 2 — Lean calls Rust.
pub(super) const TWICE_INC: &str = "def twice_inc (x : UInt64) : UInt64 := inc (inc x)\n";

/// The three pipelines `clean compile -O0/-O1/-O2` select
/// (`cmd_compile::pipeline_config_from_opt_level`); Trust's general lane uses
/// the `-O1` one (`PipelineConfig::default()`).
pub(super) fn levels() -> [(&'static str, PipelineConfig); 3] {
    [
        ("-O0", crate::rc_repair::e2e_support::o0()),
        ("-O1", PipelineConfig::default()),
        (
            "-O2",
            PipelineConfig {
                opt: crate::opt::OptConfig::aggressive(),
                rc: crate::rc::RCConfig::aggressive(),
                boxing: crate::boxing::BoxingConfig::default(),
            },
        ),
    ]
}

/// The target Trust's general lane stamps on an aarch64 host.
pub(super) fn trust_target() -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".to_string(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::Unclassified,
    }
}

/// Trust's general-lane emit configuration, verbatim but for the crate name
/// (`collect_general_clean_ir`).
fn trust_lane_config() -> TrustIrConfig {
    TrustIrConfig {
        module_name: "clean-general::step32".to_string(),
        use_clean_dialect: false,
        runtime_lowering: RuntimeLowering::ExternCalls,
        target_info: Some(trust_target()),
        ..TrustIrConfig::default()
    }
}

/// A Rust `fn` the island calls, declared the way Trust's
/// `trust_certify::clean_island::declare_rust_callees` declares it: a kernel
/// `Opaque` of the carrier type with a hidden zero inhabitant.
pub(super) fn declare_rust_callee(
    env: &mut Environment,
    name: &str,
    params: &[&str],
    result: &str,
) {
    let ty = params.iter().rev().fold(Expr::const_str(result), |acc, p| {
        Expr::arrow(Expr::const_str(p), acc)
    });
    let zero = if result == "Bool" {
        Expr::const_str("Bool.false")
    } else {
        Expr::app(
            Expr::const_str(&format!("{result}.ofNat")),
            Expr::nat_lit(0),
        )
    };
    let value = params.iter().rev().fold(zero, |acc, p| {
        Expr::lam(BinderInfo::Default, Expr::const_str(p), acc)
    });
    env.add_decl(Declaration::Opaque {
        name: Name::from_string(name),
        level_params: vec![],
        type_: ty,
        value,
    })
    .unwrap_or_else(|e| panic!("declare Rust callee `{name}`: {e:?}"));
}

/// The island environment: the prelude, the declared Rust callees, then the
/// island source elaborated and kernel-checked into it.
pub(super) fn island_env(rust_callees: &[(&str, &[&str], &str)], source: &str) -> Environment {
    let mut env = Environment::with_prelude();
    for (name, params, result) in rust_callees {
        declare_rust_callee(&mut env, name, params, result);
    }
    let patterns = clean_elab::tactic::builtins::builtin_tactic_patterns();
    let declarations =
        clean_parser::parse_file_with_tactics(source, &patterns).expect("parse the island");
    let mut file = clean_elab::FileContext::new();
    for declaration in declarations {
        let processed = clean_elab::preprocess_decl_with_context(&declaration, &mut file);
        clean_elab::elaborate_decl_and_register_with_context_and_warning(
            &mut env, &processed, &mut file,
        )
        .expect("elaborate and kernel-check the island");
    }
    env
}

/// The symbol a test gives the Rust function `name` (any symbol distinct
/// from the Clean name shows the call targets the symbol, not the constant).
pub(super) fn rust_symbol(name: &str) -> String {
    format!("_ZN4r18_{}{name}17h0123456789abcdefE", name.len())
}

/// Compile `roots` at the Rust ABI the way Trust's recorder will call it.
pub(super) fn rust_abi(
    env: &Environment,
    roots: &[&str],
    callees: &[&str],
    pipeline: &PipelineConfig,
) -> Result<RustAbiOutput, RustAbiError> {
    let roots: Vec<Name> = roots.iter().map(|r| Name::from_string(r)).collect();
    let callees: Vec<RustCallee> = callees
        .iter()
        .map(|c| RustCallee {
            constant: Name::from_string(c),
            symbol: rust_symbol(c),
        })
        .collect();
    compile_rust_abi(
        env,
        &roots,
        &callees,
        pipeline,
        "clean-rust-abi::step32",
        &trust_target(),
    )
}

/// The defined function named `name`.
pub(super) fn function<'m>(module: &'m Module, name: &str) -> &'m trust_ir::Function {
    module
        .functions
        .iter()
        .find(|f| f.name == name && !f.blocks.is_empty())
        .unwrap_or_else(|| panic!("`{name}` is not defined in the module:\n{module}"))
}

/// Every instruction of `f` except constants, in block order.
pub(super) fn insts(f: &trust_ir::Function) -> Vec<&Inst> {
    f.blocks
        .iter()
        .flat_map(|b| b.body.iter().map(|n| &n.inst))
        .filter(|i| !matches!(i, Inst::Const { .. }))
        .collect()
}

/// The names `f` calls, in order.
pub(super) fn called(module: &Module, f: &trust_ir::Function) -> Vec<String> {
    insts(f)
        .into_iter()
        .filter_map(|i| match i {
            Inst::Call { callee, .. } => module
                .functions
                .iter()
                .find(|g| g.id == *callee)
                .map(|g| g.name.clone()),
            _ => None,
        })
        .collect()
}

/// What Trust's general lane emits for `roots` today: the measurement the
/// design records, printed beside the Rust-ABI output.
pub(super) fn general_lane(env: &Environment, roots: &[&str], pipeline: &PipelineConfig) -> String {
    let batch: Vec<crate::Decl> = roots
        .iter()
        .map(|r| {
            let info = env.get_const(&Name::from_string(r)).expect("root");
            constant_to_decl(env, info)
                .expect("lowers")
                .expect("computational")
        })
        .collect();
    match compile_lcnf_to_trust_ir_with_report(&batch, env, pipeline, &trust_lane_config()) {
        Ok((module, _)) => format!("{module}"),
        Err(e) => format!("refused: {e}"),
    }
}

/// A root whose compiled meaning is not its own body: pinned Lean runs an
/// `@[implemented_by]` declaration's target and never its value, so the Rust
/// ABI, which compiles a root from its body, refuses it by name. The target is
/// an ordinary root.
#[test]
fn test_rust_abi_refuses_implemented_by_root() {
    let env = island_env(
        &[],
        "def fastW (a : UInt64) : UInt64 := a + 1\n\
         @[implemented_by fastW]\n\
         def slowW (a : UInt64) : UInt64 := a + 2\n",
    );
    let err = rust_abi(&env, &["slowW"], &[], &PipelineConfig::default())
        .expect_err("an implemented_by root has no body of its own to compile");
    match &err {
        RustAbiError::Conflict { name, detail } => {
            assert_eq!(name, "slowW");
            assert!(detail.contains("implemented_by"), "{err}");
        }
        other => panic!("expected the root refused by name, got {other:?}"),
    }
    rust_abi(&env, &["fastW"], &[], &PipelineConfig::default()).expect("the target compiles");
}

// The ORDER refusal (every root after a late `attribute [implemented_by]`)
// is tested in `tests/implemented_by_order.rs`, over the record clean-elab
// writes for the real source: this unit-test binary links a second copy of
// clean-compiler through the clean-elab dev-dependency, whose record this
// copy cannot read, and two copies writing it race to register the
// extension (`crate::implemented_by::order`).

/// A csimp rule rewrites references from other bodies, while its source root
/// still has its own compiled body. The FFI-root guard must preserve that body.
#[test]
fn test_rust_abi_compiles_csimp_source_root() {
    let env = island_env(
        &[],
        "def fastW (a : UInt64) : UInt64 := a + 1\n\
         def slowW (a : UInt64) : UInt64 := a + 2\n\
         axiom replacement : slowW = fastW\n\
         attribute [csimp] replacement\n",
    );
    assert!(clean_kernel::env::csimp::has_replacement(
        &env,
        &Name::from_string("slowW")
    ));
    rust_abi(&env, &["slowW"], &[], &PipelineConfig::default())
        .expect("csimp does not remove the source root's own compiled body");
}

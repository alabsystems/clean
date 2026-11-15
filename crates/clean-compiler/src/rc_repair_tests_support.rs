// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Test support for the WS6.2 end-to-end tests: elaborate real Clean source
//! over the prelude, compile its `clean compile`-style dependency closure
//! through the full pipeline, and provide the C shims + driver that link the
//! result against the Clean runtime.
//!
//! The programs are the two the roadmap names:
//!
//! ```lean
//! def sqLet (a : UInt64) : UInt64 := let t := a + 1; t * t
//! def twiceApply (f : UInt64 → UInt64 → UInt64) (a : UInt64) : UInt64 :=
//!   let t := a + 1; f t t
//! ```
//!
//! `sqLet`'s `t` is the object result of the boxed `HAdd.hAdd` and is passed
//! twice to the consuming `HMul.hMul` (the `LetValue::Const` arm);
//! `twiceApply` passes it twice to a closure (the `LetValue::FVar` arm, which
//! stays generic after WS6.4 devirtualizes known instances).

use std::collections::HashSet;

use clean_kernel::{Environment, Expr, ExprVisitor, LevelVec, Name};

use crate::boxing::BoxingConfig;
use crate::ir::IRDecl;
use crate::lcnf::Decl;
use crate::mangle::mangle_name;
use crate::opt::OptConfig;
use crate::pass_manager::{compile_lcnf_decls_with_rc_repair, PipelineConfig, PipelineError};
use crate::rc::RCConfig;
use crate::rc_repair::RcRepairMode;
use crate::to_lcnf::constant_to_decl;

/// The WS6.2 source programs.
pub(crate) const SOURCE: &str = "def sqLet (a : UInt64) : UInt64 := let t := a + 1; t * t\n\
def twiceApply (f : UInt64 → UInt64 → UInt64) (a : UInt64) : UInt64 := let t := a + 1; f t t\n";

/// The roots the driver calls, plus the multiplication instance it hands to
/// `twiceApply` as `f` (`HMul.hMul` at `UInt64` IS this closure: R3's
/// single-method-class representation).
pub(crate) const ROOTS: &[&str] = &["sqLet", "twiceApply", "instHMulUInt64"];

/// `clean compile -O0`'s pipeline (`cmd_compile::pipeline_config_from_opt_level`):
/// no optimization, so no later devirtualization (WS6.4) can hide the path.
pub(crate) fn o0() -> PipelineConfig {
    PipelineConfig {
        opt: OptConfig::minimal(),
        rc: RCConfig::minimal(),
        boxing: BoxingConfig::minimal(),
    }
}

/// The prelude environment with [`SOURCE`] elaborated and kernel-checked into
/// it, exactly as `clean compile` builds it (`elaborate_file_to_env`).
pub(crate) fn elaborated_env() -> Environment {
    elaborated_env_with(SOURCE)
}

/// The prelude environment with `source` elaborated and kernel-checked into
/// it (see [`elaborated_env`]).
pub(crate) fn elaborated_env_with(source: &str) -> Environment {
    let mut env = Environment::with_prelude();
    env.init_io_ops().expect("initialize the IO prelude");
    let patterns = clean_elab::tactic::builtins::builtin_tactic_patterns();
    let declarations =
        clean_parser::parse_file_with_tactics(source, &patterns).expect("parse the WS6.2 source");
    let mut file = clean_elab::FileContext::new();
    for declaration in declarations {
        let processed = clean_elab::preprocess_decl_with_context(&declaration, &mut file);
        let registered = clean_elab::elaborate_decl_and_register_with_context_and_warning(
            &mut env, &processed, &mut file,
        )
        .expect("elaborate and kernel-check the WS6.2 source");
        assert!(registered.warning.is_none(), "unexpected trust warning");
    }
    env
}

/// The symbols [`SHIMS_C`] provides; the closure keeps them extern, exactly
/// like `clean-cli`'s `PRIMITIVE_DENYLIST` (the shim always wins).
pub(crate) const SHIMMED: &[&str] = &[
    "l_Nat_add",
    "l_Nat_mul",
    "l_Nat_sub",
    "l_Nat_div",
    "l_Nat_mod",
    "l_Nat_decEq",
    "l_Nat_ble",
    "l_Nat_blt",
    "l_Nat_beq",
    "l_Nat_shiftRight",
    "l_true",
    "l_false",
    "l_HAdd_mk",
    "l_HAdd_hAdd",
    "l_HMul_mk",
    "l_HMul_hMul",
    "l_UInt64_ofNat",
    "l_UInt64_toNat",
];

/// Verbatim copies of the `clean-cli` `native_build.rs` shim definitions for
/// [`SHIMMED`] (NAT / BOOL / TYPECLASS / UINT64 tables).
pub(crate) const SHIMS_C: &str = r#"
clean_obj* l_Nat_add(clean_obj* a, clean_obj* b) { return clean_nat_add(a, b); }
clean_obj* l_Nat_mul(clean_obj* a, clean_obj* b) { return clean_nat_mul(a, b); }
clean_obj* l_Nat_sub(clean_obj* a, clean_obj* b) { return clean_nat_sub(a, b); }
clean_obj* l_Nat_div(clean_obj* a, clean_obj* b) { return clean_nat_div(a, b); }
clean_obj* l_Nat_mod(clean_obj* a, clean_obj* b) { return clean_nat_mod(a, b); }
clean_obj* l_Nat_decEq(clean_obj* a, clean_obj* b) { return clean_nat_dec_eq(a, b); }
clean_obj* l_Nat_ble(clean_obj* a, clean_obj* b) { return clean_nat_ble(a, b); }
clean_obj* l_Nat_blt(clean_obj* a, clean_obj* b) { return clean_nat_blt(a, b); }
clean_obj* l_Nat_beq(clean_obj* a, clean_obj* b) { return clean_nat_beq(a, b); }
clean_obj* l_Nat_shiftRight(clean_obj* a, clean_obj* b) { return clean_nat_shift_right(a, b); }
clean_obj* l_true(void) { return clean_box(1); }
clean_obj* l_false(void) { return clean_box(0); }
clean_obj* l_HAdd_mk(clean_obj* a, clean_obj* b, clean_obj* g, clean_obj* addFn) { (void)a; (void)b; (void)g; return addFn; }
clean_obj* l_HAdd_hAdd(clean_obj* a, clean_obj* b, clean_obj* g, clean_obj* inst, clean_obj* x, clean_obj* y) { (void)a; (void)b; (void)g; return clean_apply_2(inst, x, y); }
clean_obj* l_HMul_mk(clean_obj* a, clean_obj* b, clean_obj* g, clean_obj* mulFn) { (void)a; (void)b; (void)g; return mulFn; }
clean_obj* l_HMul_hMul(clean_obj* a, clean_obj* b, clean_obj* g, clean_obj* inst, clean_obj* x, clean_obj* y) { (void)a; (void)b; (void)g; return clean_apply_2(inst, x, y); }
clean_obj* l_UInt64_ofNat(clean_obj* n) {
  unsigned __int128 v = clean_nat_to_u128(n);
  clean_dec(n);
  return clean_nat_of_u64((uint64_t)(v & 0xFFFFFFFFFFFFFFFFull));
}
clean_obj* l_UInt64_toNat(clean_obj* v) {
  unsigned __int128 x = clean_nat_to_u128(v);
  clean_dec(v);
  return clean_nat_of_u64((uint64_t)(x & 0xFFFFFFFFFFFFFFFFull));
}
"#;

/// The driver body: kernel-certified expectations (`sqLet a = (a + 1)^2 mod
/// 2^64`), printed one per line. `sqLet (2^64 - 1)` wraps `t` to `0` after
/// boxing `a` as a HEAP Nat cell (`>= 2^63`), so the RC discipline is
/// exercised on real heap objects, not only tagged immediates. It calls the
/// roots through `ws62_*` names that [`c_driver`] / [`trust_cg_driver`] bind
/// to each back end's symbols.
const DRIVER_BODY_C: &str = r#"
#include <inttypes.h>
int main(void) {
  printf("sqLet 3 = %" PRIu64 "\n", ws62_sqLet(3));
  printf("sqLet 18446744073709551615 = %" PRIu64 "\n", ws62_sqLet(18446744073709551615ull));
  printf("sqLet 7 = %" PRIu64 "\n", ws62_sqLet(7));
  printf("twiceApply HMul.hMul 3 = %" PRIu64 "\n", ws62_twiceApply(ws62_instHMulUInt64(), 3));
  printf("twiceApply HMul.hMul 18446744073709551615 = %" PRIu64 "\n",
         ws62_twiceApply(ws62_instHMulUInt64(), 18446744073709551615ull));
  return 0;
}
"#;

/// The driver for the C back end, appended AFTER the emitted translation
/// unit (which defines the mangled `l_*` symbols).
pub(crate) fn c_driver() -> String {
    format!(
        "#define ws62_sqLet l_sqLet\n#define ws62_twiceApply l_twiceApply\n\
         #define ws62_instHMulUInt64 l_instHMulUInt64\n{DRIVER_BODY_C}"
    )
}

/// The driver for a trust-cg object, whose functions carry the raw
/// link-time symbol (`Function.name`, e.g. `sqLet`), bound by asm label.
#[cfg(feature = "trust-ir-backend")]
pub(crate) fn trust_cg_driver() -> String {
    format!(
        "#if defined(__APPLE__)\n#define WS62_SYM(s) __asm__(\"_\" s)\n#else\n\
         #define WS62_SYM(s) __asm__(s)\n#endif\n\
         extern uint64_t ws62_sqLet(uint64_t a) WS62_SYM(\"sqLet\");\n\
         extern uint64_t ws62_twiceApply(clean_obj* f, uint64_t a) WS62_SYM(\"twiceApply\");\n\
         extern clean_obj* ws62_instHMulUInt64(void) WS62_SYM(\"instHMulUInt64\");\n\
         {DRIVER_BODY_C}"
    )
}

/// The expected driver output.
pub(crate) const EXPECTED: &[&str] = &[
    "sqLet 3 = 16",
    "sqLet 18446744073709551615 = 0",
    "sqLet 7 = 64",
    "twiceApply HMul.hMul 3 = 16",
    "twiceApply HMul.hMul 18446744073709551615 = 0",
];

/// Negative twin of [`EXPECTED`]: the first expectation off by one. A
/// harness that accepted it would accept a wrong program.
pub(crate) fn off_by_one() -> Vec<String> {
    let mut twin: Vec<String> = EXPECTED.iter().map(|s| s.to_string()).collect();
    twin[0] = "sqLet 3 = 17".to_string();
    twin
}

struct Deps(Vec<Name>);

impl ExprVisitor for Deps {
    type Result = ();
    fn combine(&self, _a: (), _b: ()) {}
    fn visit_const(&mut self, name: &Name, _levels: &LevelVec) {
        self.0.push(name.clone());
    }
}

fn deps_of(value: &Expr) -> Vec<Name> {
    let mut deps = Deps(Vec::new());
    deps.visit_expr(value);
    deps.0
}

fn compile(
    decls: &[Decl],
    env: &Environment,
    pipeline: &PipelineConfig,
    mode: RcRepairMode,
) -> Result<Vec<IRDecl>, PipelineError> {
    compile_lcnf_decls_with_rc_repair(decls, env, pipeline, mode).map(|a| a.boxed_ir_decls)
}

/// The `clean compile` closure of [`ROOTS`] (per-declaration probe; a shimmed
/// or non-compiling dependency stays extern), as LCNF declarations.
/// Only the trust-ir linkrun (behind `trust-ir-backend`) takes the closure
/// uncompiled; the C-backend tests use [`compile_closure_of`].
#[cfg(feature = "trust-ir-backend")]
pub(crate) fn closure_decls(env: &Environment, pipeline: &PipelineConfig) -> Vec<Decl> {
    closure_decls_of(env, pipeline, ROOTS)
}

/// The `clean compile` closure of `roots`: per-declaration probe, a shimmed
/// or non-compiling dependency stays extern.
pub(crate) fn closure_decls_of(
    env: &Environment,
    pipeline: &PipelineConfig,
    roots: &[&str],
) -> Vec<Decl> {
    let mut seen: HashSet<Name> = HashSet::new();
    let mut decls = Vec::new();
    let mut worklist: Vec<(Name, bool)> =
        roots.iter().map(|r| (Name::from_string(r), true)).collect();
    while let Some((name, root)) = worklist.pop() {
        if !seen.insert(name.clone()) {
            continue;
        }
        if !root && SHIMMED.contains(&mangle_name(&name).as_str()) {
            continue;
        }
        let Some(info) = env.get_const(&name) else {
            continue;
        };
        let Ok(Some(decl)) = constant_to_decl(env, info) else {
            assert!(!root, "root {name} must lower to LCNF");
            continue;
        };
        let compiles = compile(
            std::slice::from_ref(&decl),
            env,
            pipeline,
            RcRepairMode::Enabled,
        );
        if let Err(err) = compiles {
            assert!(
                !root,
                "root {name} must compile through the pipeline: {err}"
            );
            continue;
        }
        if let Some(value) = &info.value {
            worklist.extend(deps_of(value).into_iter().map(|d| (d, false)));
        }
        decls.push(decl);
    }
    decls
}

/// Compile the closure of `roots` (one module) under `mode`.
pub(crate) fn compile_closure_of(
    env: &Environment,
    pipeline: &PipelineConfig,
    mode: RcRepairMode,
    roots: &[&str],
) -> Result<Vec<IRDecl>, PipelineError> {
    let decls = closure_decls_of(env, pipeline, roots);
    compile(&decls, env, pipeline, mode)
}

/// Compile ONE root on its own under `mode` (the per-declaration probe).
pub(crate) fn compile_root(
    env: &Environment,
    root: &str,
    pipeline: &PipelineConfig,
    mode: RcRepairMode,
) -> Result<Vec<IRDecl>, PipelineError> {
    let info = env
        .get_const(&Name::from_string(root))
        .expect("root is defined");
    let decl = constant_to_decl(env, info)
        .expect("root lowers")
        .expect("root is computable");
    compile(std::slice::from_ref(&decl), env, pipeline, mode)
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::boxing::{explicit_boxing_with_config, BoxingConfig};
use crate::emit_c::{emit_c_with_config, CEmitConfig};
use crate::ir::FnId;
use crate::opt::OptConfig;
use crate::pass_manager::{compile_lcnf_decls, PipelineArtifacts, PipelineConfig};
use crate::rc::RCConfig;

fn name(s: &str) -> Name {
    Name::from_string(s)
}

#[test]
fn void_slots_remove_direct_and_join_arguments_but_keep_boxed_forcing() {
    let action = IRDecl {
        name: name("action"),
        params: vec![(VarId(0), IRType::Void)],
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: VarId(1),
            ty: IRType::Object,
            value: IRExpr::Apply {
                fn_id: FnId(name("tick")),
                args: Vec::new(),
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
        },
    };
    let hold = IRDecl {
        name: name("hold"),
        params: Vec::new(),
        return_type: IRType::Object,
        body: IRBody::VDecl {
            var: VarId(0),
            ty: IRType::Object,
            value: IRExpr::PartialApply {
                fn_id: FnId(name("action")),
                arity: 1,
                args: Vec::new(),
            },
            rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
        },
    };
    let direct = IRDecl {
        name: name("direct"),
        params: vec![(VarId(0), IRType::Object), (VarId(1), IRType::Void)],
        return_type: IRType::Object,
        body: IRBody::JDecl {
            jp: JoinPointId(0),
            params: vec![(VarId(2), IRType::Void), (VarId(3), IRType::Object)],
            body: Box::new(IRBody::Ret(IRArg::Var(VarId(3)))),
            rest: Box::new(IRBody::Jmp {
                jp: JoinPointId(0),
                args: vec![IRArg::Erased, IRArg::Var(VarId(0))],
            }),
        },
    };
    let mut decls = explicit_boxing_with_config(&[action, hold, direct], &BoxingConfig::minimal());
    check_decls(&decls).expect("logical declarations include the world slot");
    erase_void_parameters(&mut decls).expect("lower the physical calling convention");
    check_decls(&decls).expect("physical declarations and calls agree");
    let c = emit_c_with_config(&decls, CEmitConfig::default()).expect("emit checked C IR");
    assert!(c.contains("l_action(void)"), "{c}");
    assert!(c.contains("l_direct(clean_obj* _x0)"), "{c}");

    let driver = format!(
        r#"#include "clean_runtime.h"
static unsigned ticks;
static clean_obj* l_tick(void) {{ ++ticks; return clean_box(7); }}
{c}
int main(void) {{
    clean_runtime_init();
    clean_obj* a = l_hold();
    if (ticks != 0) return 1;
    size_t forced = clean_unbox(clean_apply_1(a, clean_box(0)));
    size_t argument = clean_unbox(l_direct(clean_box(42)));
    clean_runtime_finalize();
    return ticks == 1 && forced == 7 && argument == 42 ? 0 : 2;
}}
"#
    );
    run_c_driver(&driver);
}

fn run_c_driver(driver: &str) {
    let dir = tempfile::tempdir().expect("test build directory");
    std::fs::write(
        dir.path().join("clean_runtime.h"),
        clean_runtime::runtime_header(),
    )
    .expect("write runtime header");
    std::fs::write(
        dir.path().join("runtime.c"),
        clean_runtime::runtime_source().replacen(
            "../include/clean_runtime.h",
            "clean_runtime.h",
            1,
        ),
    )
    .expect("write runtime source");
    std::fs::write(dir.path().join("driver.c"), driver).expect("write C driver");
    let output = std::process::Command::new("cc")
        .current_dir(dir.path())
        .args([
            "-std=c11",
            "-Werror=implicit-function-declaration",
            "driver.c",
            "runtime.c",
            "-o",
            "run",
        ])
        .output()
        .expect("run C compiler");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(std::process::Command::new(dir.path().join("run"))
        .status()
        .expect("run compiled forcing test")
        .success());
}

#[test]
fn void_slot_with_a_live_operand_is_refused() {
    let mut args = vec![IRArg::Var(VarId(0)), IRArg::Erased];
    let original = args.clone();
    assert!(erase_arguments(&mut args, &[0]).is_err());
    assert_eq!(args, original);
}

#[test]
fn same_named_source_void_remains_a_physical_parameter() {
    let mut env = clean_kernel::Environment::with_prelude();
    register_source(
        &mut env,
        "def Void (_ : Type) : Type := Nat\n\
         structure LocalState where\n  state : Void Nat\n  value : Nat\n\n\
         def carry (n : Void Nat) : Nat := n\n",
    );
    assert!(crate::to_mono::has_trivial_structure(&name("LocalState"), &env).is_none());
    let artifacts = compile_source_roots(&env, &["carry"]);
    let carry = artifacts
        .boxed_ir_decls
        .iter()
        .find(|decl| decl.name == name("carry"))
        .unwrap();
    assert_eq!(carry.params.len(), 1);
}

fn checked_sdk_void_env(extra: &[&str]) -> clean_kernel::Environment {
    use clean_kernel::env::{ConstantOrigin, OriginTrust};
    use clean_kernel::{Environment, LeanWorld};
    use std::sync::Arc;

    let sdk = clean_olean::require_pinned_lean_lib_path().expect("installed pinned Lean");
    let mut base = Environment::for_lean_replay();
    clean_olean::declare_environment_world(&mut base, LeanWorld::ORACLE.tag())
        .expect("declare checked replay world");
    let mut imported = base.clone();
    clean_olean::load_module_with_deps(&mut imported, "Init.System.ST", &[sdk])
        .expect("load the actual SDK state-token definitions");
    let replay = clean_olean::ReplayedImportedSource::check(
        Arc::new(base),
        Arc::new(imported),
        [name("Void"), name("Void.nonemptyType")]
            .into_iter()
            .chain(extra.iter().map(|item| name(item)))
            .collect(),
    )
    .expect("replay the exact state-token declarations");
    let mut env = replay.checked_environment().clone();
    for name in [name("Void"), name("Void.nonemptyType")] {
        let checked = replay
            .checked_constant(&name)
            .expect("checked SDK definition");
        assert_eq!(
            replay
                .original_environment()
                .get_const(&name)
                .unwrap()
                .type_,
            checked.type_
        );
        let Some(ConstantOrigin::Olean { module, .. }) =
            replay.original_environment().get_constant_origin(&name)
        else {
            panic!("missing SDK provenance for {name}");
        };
        // These records in the rebuilt environment earned their check above.
        // Preserve the original module identity when presenting that checked
        // environment to the compiler.
        env.set_constant_origin(
            name,
            ConstantOrigin::Olean {
                module: module.clone(),
                trust: OriginTrust::KernelChecked,
            },
        );
    }
    assert!(crate::world_token::has_checked_void_layout(&env));
    if env.get_const(&name("Nat")).is_none() {
        env.init_nat()
            .expect("initialize Nat for the source control");
    }
    env
}

fn register_source(env: &mut clean_kernel::Environment, source: &str) {
    let declarations = clean_parser::parse_file(source).expect("parse state-token source");
    let mut context = clean_elab::FileContext::new();
    for declaration in declarations {
        let declaration = clean_elab::preprocess_decl_with_context(&declaration, &mut context);
        clean_elab::elaborate_decl_and_register_with_context_and_warning(
            env,
            &declaration,
            &mut context,
        )
        .expect("check state-token source");
    }
}

fn compile_source_roots(env: &clean_kernel::Environment, roots: &[&str]) -> PipelineArtifacts {
    let decls: Vec<_> = roots
        .iter()
        .map(|root| {
            let info = env
                .get_const(&name(root))
                .expect("ordinary source declaration");
            crate::to_lcnf::constant_to_decl(env, info)
                .expect("lower ordinary source declaration")
                .expect("computable ordinary source declaration")
        })
        .collect();
    let config = PipelineConfig {
        opt: OptConfig::minimal(),
        rc: RCConfig::minimal(),
        boxing: BoxingConfig::minimal(),
    };
    compile_lcnf_decls(&decls, env, &config).expect("compile the checked source")
}

#[test]
fn checked_sdk_void_parameter_erases_in_ordinary_source() {
    let mut env = checked_sdk_void_env(&[]);
    register_source(&mut env, "def carry (_ : Void Nat) (n : Nat) : Nat := n\n");
    let artifacts = compile_source_roots(&env, &["carry"]);
    let carry = artifacts
        .boxed_ir_decls
        .iter()
        .find(|decl| decl.name == name("carry"))
        .unwrap();
    assert_eq!(carry.params.len(), 1);
}

#[test]
fn checked_world_field_layout_preserves_payload_positions_and_result_tags() {
    let mut env = checked_sdk_void_env(&[
        "ST.Out.mk",
        "ST.Out.val",
        "EST.Out.ok",
        "EST.Out.error",
        "EST.Out.casesOn",
    ]);
    register_source(
        &mut env,
        "structure Packed where\n  first : Nat\n  state : Void Nat\n  second : Nat\n\n\
         structure StateFirst where\n  state : Void Nat\n  payload : Nat\n\n\
         def stateFirst (state : Void Nat) (n : Nat) : StateFirst := ⟨state, n⟩\n\
         def plainState (state : Void Nat) (n : Nat) : ST.Out Nat Nat := ST.Out.mk n state\n\
         def stateVal (r : ST.Out Nat Nat) : Nat := ST.Out.val r\n\
         def pack (state : Void Nat) (first second : Nat) : Packed := ⟨first, state, second⟩\n\
         def resultOk (state : Void Nat) (n : Nat) : EST.Out Nat Nat Nat := EST.Out.ok n state\n\
         def resultError (state : Void Nat) (n : Nat) : EST.Out Nat Nat Nat := EST.Out.error n state\n\
         def relay (r : EST.Out Nat Nat Nat) : EST.Out Nat Nat Nat :=\n\
         \x20 EST.Out.casesOn r (fun n s => EST.Out.ok n s) (fun n s => EST.Out.error n s)\n",
    );
    let roots = [
        "stateFirst",
        "StateFirst.payload",
        "plainState",
        "stateVal",
        "ST.Out.val",
        "pack",
        "Packed.first",
        "Packed.state",
        "Packed.second",
        "resultOk",
        "resultError",
        "relay",
    ];
    let artifacts = compile_source_roots(&env, &roots);
    check_decls(&artifacts.boxed_ir_decls).expect("compiler output passes IR checking");
    let c = artifacts
        .emit_c(CEmitConfig::default())
        .expect("emit the checked field layouts");
    let driver = format!(
        r#"{c}
int main(void) {{
    clean_runtime_init();
    clean_obj* st = l_plainState(clean_box(23));
    clean_obj* before = l_stateFirst(clean_box(19));
    if (st != clean_box(23) || l_stateVal(st) != st ||
        before != clean_box(19) || l_StateFirst_payload(before) != before) return 2;
    clean_obj* left = l_pack(clean_box(5), clean_box(13));
    clean_obj* right = l_pack(clean_box(5), clean_box(13));
    if (clean_is_scalar(left) || clean_num_child_fields(left) != 2) return 1;
    size_t first = clean_unbox(l_Packed_first(left));
    size_t second = clean_unbox(l_Packed_second(right));
    clean_obj* ok = l_relay(l_resultOk(clean_box(7)));
    clean_obj* err = l_relay(l_resultError(clean_box(11)));
    int failed = first != 5 || second != 13 ||
        clean_is_scalar(ok) || clean_is_scalar(err) ||
        clean_obj_tag(ok) != 0 || clean_obj_tag(err) != 1 ||
        clean_num_child_fields(ok) != 1 || clean_num_child_fields(err) != 1;
    if (!failed) {{
        failed = clean_unbox(clean_ctor_get(ok, 0)) != 7 ||
            clean_unbox(clean_ctor_get(err, 0)) != 11;
    }}
    clean_dec(ok);
    clean_dec(err);
    clean_runtime_finalize();
    return failed;
}}
"#
    );
    run_c_driver(&driver);
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use clean_kernel::env::{CompilerExternArity, CompilerExternEntry, CompilerExternMetadata};
use clean_kernel::{BinderInfo, Declaration};

#[test]
fn pinned_nat_add_requires_the_sdk_owner_definition_and_two_borrowed_arguments() {
    let directory = tempfile::tempdir().unwrap();
    let file = directory.path().join("Add.lean");
    std::fs::write(
        &file,
        "prelude\nimport Init.Prelude\n\ndef total (a b : Nat) : Nat := Nat.add a b\n",
    )
    .unwrap();
    let (env, _, _) = elaborate_file_with_inventory(&file).unwrap();
    let name = Name::interned("Nat.add");
    assert!(
        has_pinned_nat_add_binding(&env, &name),
        "world {:?}, owner {:?}, definition {:?}, extern {:?}",
        clean_olean::environment_world(&env),
        clean_olean::import::lean_declaration_artifact(&env, &name),
        env.native_fold_definition_verdict(&name),
        env.extern_metadata(&name)
    );
    assert!(
        require_stable_nat_add(&env).is_err(),
        "captured IR is versioned"
    );
    let source = CheckedNativeSource::default();
    let select = |env: &Environment| {
        source.select(
            env,
            None,
            &Name::interned("total"),
            0,
            None,
            crate::native_nat_display::NatDisplay::Bootstrap,
        )
    };
    select(&env).unwrap();
    let refuse = |changed: &Environment| {
        assert!(!has_pinned_nat_add_binding(changed, &name));
        let error = format!("{:#}", select(changed).err().expect("unbound extern"));
        assert!(
            error.contains("native-extern-body") && error.contains("Nat.add"),
            "{error}"
        );
    };

    let mut foreign = env.clone();
    assert!(foreign.set_constant_origin(
        name.clone(),
        ConstantOrigin::clean_payload(Some("Init.Prelude".to_owned()))
    ));
    refuse(&foreign);

    let Some(CompilerExternMetadata::Complete(descriptor)) = env.extern_metadata(&name).unwrap()
    else {
        panic!("missing genuine compiler descriptor")
    };
    let mut wrong_arity = descriptor.clone();
    wrong_arity.arity = CompilerExternArity::Legacy(Some(2));
    let mut wrong_backend = descriptor.clone();
    wrong_backend.entries = vec![CompilerExternEntry::Standard {
        backend: Name::interned("llvm"),
        symbol: "lean_nat_add".to_owned(),
    }];
    let mut wrong_symbol = descriptor.clone();
    wrong_symbol.entries = vec![CompilerExternEntry::Standard {
        backend: Name::interned("all"),
        symbol: "lean_nat_mul".to_owned(),
    }];
    for altered in [wrong_arity, wrong_backend, wrong_symbol] {
        let mut changed = env.clone();
        changed
            .register_extern_metadata(name.clone(), CompilerExternMetadata::Complete(altered))
            .unwrap();
        refuse(&changed);
    }
    let mut symbol_only = env.clone();
    symbol_only.register_extern(name.clone(), "lean_nat_add".to_owned());
    refuse(&symbol_only);
    let mut overridden = env.clone();
    overridden.register_implemented_by(name.clone(), Name::interned("total"));
    assert!(!has_pinned_nat_add_binding(&overridden, &name));

    let original = env.get_const(&name).unwrap();
    let nat = Expr::const_str("Nat");
    let first = Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::lam(BinderInfo::Default, nat.clone(), Expr::bvar(1)),
    );
    for (ty, body) in [
        (original.type_.clone(), first),
        (
            Expr::arrow(nat.clone(), Expr::arrow(nat.clone(), nat)),
            original.value.clone().unwrap(),
        ),
    ] {
        let mut changed = env.clone();
        assert!(changed.forget_decl(&name));
        changed
            .add_decl(Declaration::Definition {
                name: name.clone(),
                level_params: vec![],
                type_: ty,
                value: body,
                is_reducible: true,
            })
            .unwrap();
        changed.set_constant_origin(
            name.clone(),
            env.get_constant_origin(&name).unwrap().clone(),
        );
        changed
            .register_extern_metadata(
                name.clone(),
                CompilerExternMetadata::Complete(descriptor.clone()),
            )
            .unwrap();
        refuse(&changed);
    }
    let error = select_lcnf_decl(&CompileArgs {
        file: Some(file),
        decl: Some("total".to_owned()),
        emit: EmitFormat::C,
        opt_level: 0,
        output: None,
        link_artifact: Vec::new(),
    })
    .err()
    .expect("the generic emitter does not provide the runtime shim");
    assert!(format!("{error:#}").contains("native-extern-body"));
}

#[test]
fn pinned_nat_add_runs_row_counters_through_the_native_entry() {
    let directory = tempfile::tempdir().unwrap();
    let file = directory.path().join("Rows.lean");
    std::fs::write(
        &file,
        r#"prelude
import Init.Notation

@[noinline] def total (accepted refused : Nat) : Nat := accepted + refused
def answer : Nat := total (total 17 1) (total 23 1)
"#,
    )
    .unwrap();
    assert_output(&file, "answer", b"42\n");
}

fn assert_output(file: &Path, entry: &str, expected: &[u8]) {
    let artifact = crate::native_build::emit_native_c_artifact(file, entry, 0).unwrap();
    let binary = artifact.build_in_scratch(true).unwrap();
    let output = std::process::Command::new(binary.binary())
        .output()
        .unwrap();
    assert!(output.status.success(), "{:?}", output.stderr);
    assert_eq!(output.stdout, expected);
}

#[test]
fn pinned_nat_add_respects_a_caller_scoped_compiler_replacement() {
    let directory = tempfile::tempdir().unwrap();
    let file = directory.path().join("Scope.lean");
    std::fs::write(
        &file,
        r#"prelude
import Init.Prelude
@[noinline] def earlier (a b : Nat) : Nat := Nat.add a b
@[noinline] def chooseLeft (a _b : Nat) : Nat := a
@[implemented_by chooseLeft] def replacement (a b : Nat) : Nat := Nat.add a b
@[csimp] theorem substituteAdd : Eq Nat.add replacement := Eq.refl Nat.add
@[noinline] def later (a b : Nat) : Nat := Nat.add a b
def earlyAnswer := earlier 17 25
def lateAnswer := later 17 25
"#,
    )
    .unwrap();
    assert_output(&file, "earlyAnswer", b"42\n");
    assert_output(&file, "lateAnswer", b"17\n");
}

#[test]
#[ignore = "requires CLEAN_LEAN436_LIB pointing to the stable Lean distribution"]
fn pinned_nat_add_keeps_the_stable_captured_ir_binding_versioned() {
    use clean_kernel::LeanWorld;
    let lib = PathBuf::from(std::env::var_os("CLEAN_LEAN436_LIB").unwrap());
    let world = LeanWorld::Lean436;
    clean_olean::check_olean_file_in_world(lib.join("Init/Prelude.olean"), world).unwrap();
    let mut env = Environment::new();
    clean_olean::declare_environment_world(&mut env, world.tag()).unwrap();
    clean_olean::load_module_with_deps(&mut env, "Init.Prelude", &[lib]).unwrap();
    let name = Name::interned("Nat.add");
    require_stable_nat_add(&env).unwrap();
    assert_eq!(
        select_stable_core_shim(&env, env.get_const(&name).unwrap()).unwrap(),
        Some("l_Nat_add")
    );
    assert!(!has_pinned_nat_add_binding(&env, &name));
}

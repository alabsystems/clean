// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::native_ffi_audit::has_pinned_uint32_of_nat_binding;
use clean_kernel::env::{CompilerExternArity, CompilerExternMetadata};

#[test]
fn pinned_uint32_of_nat_requires_the_original_definition_and_compiler_binding() {
    let directory = tempfile::tempdir().unwrap();
    let file = directory.path().join("Word.lean");
    std::fs::write(
        &file,
        "prelude\nimport Init.Data.UInt.BasicAux\n\n\
         @[noinline] def convert (n : Nat) : UInt32 := UInt32.ofNat n\n",
    )
    .unwrap();
    let (mut env, _, _) = elaborate_file_with_inventory(&file).unwrap();
    let name = Name::interned("UInt32.ofNat");
    let info = env.get_const(&name).unwrap().clone();
    assert!(
        has_pinned_uint32_of_nat_binding(&env, &info),
        "world {:?}, origin {:?}, artifact {:?}, definition {:?}, extern {:?}",
        clean_olean::environment_world(&env),
        env.get_constant_origin(&name),
        clean_olean::import::lean_declaration_artifact(&env, &name),
        env.native_fold_definition_verdict(&name),
        env.extern_metadata(&name),
    );
    let source = CheckedNativeSource::default();
    let root = Name::interned("convert");
    let select = |env: &Environment| {
        source.select(
            env,
            None,
            &root,
            0,
            None,
            crate::native_nat_display::NatDisplay::Bootstrap,
        )
    };
    select(&env).expect("a native C artifact supplies the owned boxed shim");
    let generic = select_lcnf_decl(&CompileArgs {
        file: Some(file),
        decl: Some("convert".to_owned()),
        emit: EmitFormat::C,
        opt_level: 0,
        output: None,
        link_artifact: Vec::new(),
    })
    .err()
    .expect("generic compilation does not supply the owned boxed shim");
    assert!(format!("{generic:#}").contains("native-extern-body"));

    let mut local = env.clone();
    assert!(local.set_constant_origin(
        name.clone(),
        ConstantOrigin::clean_payload(Some("Init.Data.UInt.BasicAux".to_owned()))
    ));
    assert!(!has_pinned_uint32_of_nat_binding(&local, &info));
    assert!(format!("{:#}", select(&local).err().unwrap()).contains("native-extern-body"));

    let Some(CompilerExternMetadata::Complete(mut descriptor)) =
        env.extern_metadata(&name).unwrap()
    else {
        panic!("the SDK import must provide the full compiler descriptor");
    };
    descriptor.arity = CompilerExternArity::Legacy(Some(2));
    env.register_extern_metadata(name.clone(), CompilerExternMetadata::Complete(descriptor))
        .unwrap();
    assert!(!has_pinned_uint32_of_nat_binding(&env, &info));
    assert!(format!("{:#}", select(&env).err().unwrap()).contains("native-extern-body"));
    env.register_extern(name.clone(), "lean_uint32_of_nat".to_owned());
    assert!(!has_pinned_uint32_of_nat_binding(&env, &info));
    env.register_extern(name, "foreign_word".to_owned());
    let refusal = format!("{:#}", select(&env).err().unwrap());
    assert!(refusal.contains("native-extern-body") && refusal.contains("foreign_word"));
}

#[test]
fn pinned_uint32_of_nat_runs_a_full_width_natural_entry() {
    let directory = tempfile::tempdir().unwrap();
    let file = directory.path().join("Word.lean");
    std::fs::write(
        &file,
        r#"prelude
import Init.Data.UInt.BasicAux

def convert (n : Nat) : UInt32 := UInt32.ofNat n
def answer : Nat :=
  @UInt32.rec (fun _ => Nat) (fun bits => @Fin.val 4294967296 (@BitVec.toFin 32 bits))
    (convert 2854495385411919762116572086472942864751644143)
"#,
    )
    .unwrap();

    let artifact = crate::native_build::emit_native_c_artifact(&file, "answer", 0).unwrap();
    let binary = artifact.build_in_scratch(true).unwrap();
    let output = std::process::Command::new(binary.binary())
        .output()
        .unwrap();
    assert!(output.status.success(), "{:?}", output.stderr);
    assert_eq!(output.stdout, b"2309737967\n");
}

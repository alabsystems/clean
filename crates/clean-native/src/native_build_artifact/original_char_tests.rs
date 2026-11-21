// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use clean_elab::module_driver::{
    elaborate_prelude_header, module_environment_and_context_with_import_paths,
    preload_exported_term_syntax, EnvironmentSetup,
};
use clean_kernel::{BinderInfo, Declaration};

#[test]
#[ignore = "requires the original Lean 4.36 SDK in CLEAN_LEAN436_LIB and a C compiler"]
fn checked_char_program_preserves_scalar_boundaries_and_arbitrary_nats() {
    let project = tempfile::tempdir().unwrap();
    std::fs::write(
        project.path().join("lean-toolchain"),
        "leanprover/lean4:v4.36.0\n",
    )
    .unwrap();
    let file = project.path().join("Convert.lean");
    let source = "prelude\nimport Init.Prelude\n";
    std::fs::write(&file, source).unwrap();
    let world = clean_olean::source_world_for_file(&file, None).unwrap();
    let (header, header_decls) =
        clean_parser::Parser::parse_header_with_decls_in_world(source, world.world()).unwrap();
    let sdk = PathBuf::from(std::env::var_os("CLEAN_LEAN436_LIB").unwrap());
    let (mut env, mut ctx) = module_environment_and_context_with_import_paths(
        EnvironmentSetup::default(),
        &world,
        &header,
        vec![sdk],
    )
    .unwrap();
    ctx.set_main_module(Name::interned("Convert"));
    ctx.set_file_header(&header);
    elaborate_prelude_header(&mut env, &header_decls, &mut ctx).unwrap();
    preload_exported_term_syntax(&mut env, &mut ctx, &header, source, true).unwrap();
    assert!(ctx.stable_char_program().unwrap().matches_environment(&env));
    let nat = Expr::const_str("Nat");
    env.add_decl(Declaration::Definition {
        name: Name::interned("convertWitness"),
        level_params: vec![],
        type_: Expr::arrow(nat.clone(), Expr::const_str("Char")),
        value: Expr::lam(
            BinderInfo::Default,
            nat,
            Expr::app(Expr::const_str("Char.ofNat"), Expr::bvar(0)),
        ),
        is_reducible: false,
    })
    .unwrap();
    let compiled = emit_checked_native_c_artifact_in_context(
        &file,
        "convertWitness",
        &env,
        &CheckedNativeSource::default(),
        Some(&ctx),
        0,
    )
    .unwrap();
    let shims = select_shims_for_c_text_with_policy(&compiled.emitted_c, compiled.policy).unwrap();
    let program = format!(
        "#include \"clean_runtime.h\"\n{shims}\n{}\n{}",
        compiled.emitted_c,
        r#"
int main(void) {
    for (uint32_t i = 0; i <= 0x110001; ++i) {
        uint32_t expected = i <= 0x10ffff && (i < 0xd800 || i > 0xdfff) ? i : 0;
        if (l_convertWitness(clean_nat_of_u64(i)) != expected) return 1;
    }
    clean_obj* wide = clean_nat_shift_left(clean_box(1), clean_box(4096));
    clean_inc(wide);
    if (l_convertWitness(wide) != 0 || !clean_is_exclusive(wide)) return 2;
    clean_dec(wide);
    return 0;
}
"#
    );
    let executable = link_program_in_scratch(&program).unwrap();
    assert!(std::process::Command::new(executable.binary())
        .status()
        .unwrap()
        .success());
}

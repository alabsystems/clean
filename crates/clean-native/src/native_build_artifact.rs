// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Keep the checked source layout attached to the exact emitted C.

use super::*;
use crate::compile::CheckedNativeSource;
use crate::native_string_layout_policy::StringLayoutPolicy;
use clean_compiler::{pass_manager::PipelineConfig, Decl, RuntimeBindingClosure};
use clean_kernel::{Environment, Name};

/// Emitted C and its source-derived native carrier policy.
///
/// Its fields are private so an unrelated C string cannot reuse the policy.
#[derive(Debug)]
pub struct NativeCArtifact {
    decl: String,
    emitted_c: String,
    decl_type: Option<Expr>,
    policy: StringLayoutPolicy,
    state_entry: Option<state_entry::StateEntry>,
    uint8_of_nat_shim: bool,
}

impl NativeCArtifact {
    /// Build the exact emitted artifact with its checked source policy.
    ///
    /// # Errors
    /// Refuses an unsupported entry, uncovered extern, or failed native link.
    pub fn build_in_scratch(&self, nat_strict_guard: bool) -> anyhow::Result<BuiltBinary> {
        if self.state_entry.is_some() {
            return link_program_in_scratch(&self.render()?);
        }
        build_native_binary_with_policy(
            &self.decl,
            &self.emitted_c,
            self.decl_type.as_ref(),
            nat_strict_guard,
            self.policy,
            self.uint8_of_nat_shim,
        )
    }

    pub(super) fn render(&self) -> anyhow::Result<String> {
        render_native_translation_unit_with_policy(
            &self.decl,
            &self.emitted_c,
            self.decl_type.as_ref(),
            self.policy,
            self.state_entry.as_ref(),
            self.uint8_of_nat_shim,
        )
    }
}

/// Elaborate and emit a native C artifact without discarding its source policy.
///
/// # Errors
/// Preserves the production elaboration, fidelity-audit and emitter refusals.
pub fn emit_native_c_artifact(
    file: &Path,
    decl: &str,
    opt_level: u8,
) -> anyhow::Result<NativeCArtifact> {
    let root = crate::compile::parse_compile_decl_name(decl)?;
    let (env, opaques, declarations) = crate::compile::elaborate_file_with_inventory(file)?;
    let closure = pinned_direct_state_closure(&env, &root)?;
    let selected = crate::compile::select_file_declarations_for_native_c(
        &env,
        &opaques,
        &declarations,
        &root,
        opt_level,
        closure.as_ref(),
    )?;
    emit_selected_native_c(
        file,
        decl,
        &root,
        &selected.decls,
        &env,
        &selected.pipeline,
        closure.as_ref(),
    )
}

fn pinned_direct_state_closure(
    env: &Environment,
    root: &Name,
) -> anyhow::Result<Option<RuntimeBindingClosure>> {
    if !state_entry::StateEntry::is_pinned_direct_action(env, root) {
        return Ok(None);
    }
    crate::native_ffi_audit::refuse_compiled_before_binding(root, env)?;
    Ok(Some(RuntimeBindingClosure::check_executable(
        env,
        std::slice::from_ref(root),
    )?))
}

/// Compile a declaration from the exact environment and source leaves that
/// the caller's module driver just checked.
///
/// # Errors
/// Refuses a missing entry, unsupported body or unaudited native dependency.
pub fn emit_checked_native_c_artifact(
    file: &Path,
    decl: &str,
    env: &Environment,
    source: &CheckedNativeSource,
    opt_level: u8,
) -> anyhow::Result<NativeCArtifact> {
    emit_checked_native_c_artifact_in_context(file, decl, env, source, None, opt_level)
}

/// Emit a checked source entry using the artifacts captured during elaboration.
///
/// # Errors
/// Propagates import, compiler binding, ABI and native lowering refusals.
pub fn emit_checked_native_c_artifact_in_context(
    file: &Path,
    decl: &str,
    env: &Environment,
    source: &CheckedNativeSource,
    file_context: Option<&clean_elab::FileContext>,
    opt_level: u8,
) -> anyhow::Result<NativeCArtifact> {
    let root = crate::compile::parse_compile_decl_name(decl)?;
    // The complete stable SDK may contain bindings installed after unrelated
    // declarations were compiled. Check the actual root and preserve that
    // same closure through selection, transformed LCNF, IR and C emission.
    let world = file_context
        .map(clean_elab::FileContext::declared_lean_world)
        .transpose()?
        .flatten();
    if let (Some(declared), Some(imported)) = (world, clean_olean::environment_world(env)) {
        anyhow::ensure!(
            declared.tag() == imported,
            "native file context declares Lean world {} but the environment contains {imported}",
            declared.tag()
        );
    }
    let closure = if world == Some(clean_kernel::LeanWorld::Lean436)
        && clean_compiler::implemented_by_order(env).is_some()
    {
        Some(RuntimeBindingClosure::check_executable(
            env,
            std::slice::from_ref(&root),
        )?)
    } else {
        pinned_direct_state_closure(env, &root)?
    };
    use crate::native_nat_display::NatDisplay;
    let nat_display = NatDisplay::select(world, env, file_context);
    let selected = source.select(
        env,
        file_context,
        &root,
        opt_level,
        closure.as_ref(),
        nat_display,
    )?;
    let mut artifact = emit_selected_native_c(
        file,
        decl,
        &root,
        &selected.decls,
        env,
        &selected.pipeline,
        closure.as_ref(),
    )?;
    if nat_display != NatDisplay::Bootstrap {
        let code = c_scan_code(&artifact.emitted_c);
        let missing_body = |name| {
            c_references_symbol(&code, name)
                && !code
                    .lines()
                    .filter_map(emitted_declarator)
                    .any(|(symbol, _, definition)| symbol == name && definition)
        };
        anyhow::ensure!(
            !missing_body("l_instToStringNat"),
            "the selected stable ToString Nat dictionary was not compiled"
        );
        if missing_body("l_Nat_reprFast") {
            anyhow::ensure!(
                nat_display == NatDisplay::Original,
                "the selected Nat.reprFast requires its original compiled body"
            );
            artifact.emitted_c.insert_str(
                0,
                "clean_obj* l_Nat_reprFast(clean_obj* n) { return clean_nat_repr(n); }\n",
            );
        }
    }
    if let (Some(state), Some(imports)) = (
        &mut artifact.state_entry,
        file_context.and_then(clean_elab::FileContext::stable_io_error_imports),
    ) {
        state.select_error_formatter(env, imports);
    }
    if !selected.stdout.is_empty() {
        let mut source = io_error::stdout_error_tags(env)?;
        let code = c_scan_code(&artifact.emitted_c);
        source.push_str(include_str!("compile/stdio_errno_darwin.c"));
        if clean_compiler::world_token::has_checked_void_layout(env) {
            source.push_str("#define CLEAN_STDIO_ERASED_WORLD 1\n");
        }
        source.push_str(include_str!("compile/stdio_stream.c"));
        for (symbol, implementation, arguments) in selected.stdout.operations() {
            anyhow::ensure!(
                !code
                    .lines()
                    .filter_map(emitted_declarator)
                    .any(|(name, _, definition)| name == symbol && definition),
                "duplicate native stdout implementation of {symbol}"
            );
            let arities = symbol_use_arities(&code, symbol);
            if arities.is_empty() && !c_references_symbol(&code, symbol) {
                continue;
            }
            anyhow::ensure!(
                arities.len() == 1,
                "unsupported mixed native stdout call shapes for {symbol}: {arities:?}"
            );
            let arity = *arities
                .first()
                .ok_or_else(|| anyhow::anyhow!("missing native stdout call shape"))?;
            let definition = match (arguments,arity) {
                (1,1) => format!("clean_obj* {symbol}(clean_obj* w) {{ return {implementation}(w); }}\n"),
                (1,0) => format!("clean_obj* {symbol}(void) {{ return clean_alloc_closure((void*){implementation}, 1, 0); }}\n"),
                (2,2) => format!("clean_obj* {symbol}(clean_obj* s, clean_obj* w) {{ return {implementation}(s, w); }}\n"),
                (2,1) => format!("clean_obj* {symbol}(clean_obj* s) {{ return clean_alloc_closure((void*){implementation}, 2, 1, s); }}\n"),
                _ => anyhow::bail!("unsupported native stdout call shape for {symbol}: {arity} arguments"),
            };
            source.push_str(&definition);
        }
        artifact.emitted_c.insert_str(0, &source);
    }
    for (symbol, arity, definition) in [
        selected.original_char.then_some((
            "l_Char_ofNat",
            1,
            include_str!("compile/original_char.c"),
        )),
        selected.nat_dec_lt.then_some((
            "l_Nat_decLt",
            2,
            "clean_obj* l_Nat_decLt(clean_obj* a, clean_obj* b) { return clean_nat_blt(a, b); }\n",
        )),
        selected.nat_pow.then_some((
            "l_Nat_pow",
            2,
            "clean_obj* l_Nat_pow(clean_obj* a, clean_obj* b) { return clean_nat_pow(a, b); }\n",
        )),
        selected
            .bitvec32
            .map(|b| ("l_UInt32_ofBitVec", 1, b.definition())),
        selected
            .char_from_valid_nat
            .map(|b| ("l_Char_ofNatAux", 2, b.definition())),
    ]
    .into_iter()
    .flatten()
    {
        let code = c_scan_code(&artifact.emitted_c);
        anyhow::ensure!(
            !code
                .lines()
                .filter_map(emitted_declarator)
                .any(|(name, _, definition)| name == symbol && definition),
            "duplicate native implementation of the selected extern {symbol}"
        );
        if c_references_symbol(&code, symbol) {
            let arities = symbol_use_arities(&code, symbol);
            anyhow::ensure!(
                arities.len() == 1 && arities.contains(&arity),
                "unsupported native {symbol} call shapes: {arities:?}"
            );
            artifact.emitted_c.insert_str(0, definition);
        }
    }
    if let Some(binding) = selected.void_mk {
        let code = c_scan_code(&artifact.emitted_c);
        anyhow::ensure!(
            !code
                .lines()
                .filter_map(emitted_declarator)
                .any(|(name, _, definition)| name == "l_Void_mk" && definition),
            "duplicate native implementation of the selected Void.mk extern"
        );
        if c_references_symbol(&code, "l_Void_mk") {
            artifact.emitted_c.insert_str(0, binding.definition());
        }
    }
    Ok(artifact)
}

fn emit_selected_native_c(
    file: &Path,
    decl: &str,
    root: &Name,
    declarations: &[Decl],
    env: &Environment,
    pipeline: &PipelineConfig,
    closure: Option<&RuntimeBindingClosure>,
) -> anyhow::Result<NativeCArtifact> {
    let decl_type = env.get_const(root).map(|info| info.type_.clone());
    let emitted_c = match closure {
        Some(closure) => crate::compile::emit_decls_in_runtime_closure(
            declarations,
            env,
            EmitFormat::C,
            pipeline,
            Some(file),
            closure,
        ),
        None => crate::compile::emit_decls(
            declarations,
            env,
            EmitFormat::C,
            pipeline,
            Some(file),
            clean_compiler::CodeMeaning::LeanCompiled,
        ),
    }?;
    Ok(NativeCArtifact {
        decl: decl.to_owned(),
        emitted_c,
        decl_type,
        policy: StringLayoutPolicy::from_env(env),
        state_entry: state_entry::StateEntry::check(env, root, declarations)?,
        uint8_of_nat_shim: crate::native_ffi_audit::has_pinned_uint8_of_nat_binding(
            env,
            &Name::from_string("UInt8.ofNat"),
        ),
    })
}

#[cfg(test)]
#[path = "native_build_artifact/original_char_tests.rs"]
mod original_char_tests;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::native_ffi_audit::has_pinned_uint8_of_nat_binding;
    use clean_kernel::{BinderInfo, Declaration, LeanWorld};

    #[test]
    #[ignore = "requires CLEAN_LEAN436_LIB pointing to the stable Lean distribution"]
    fn stable_state_token_consumes_one_owned_value_in_emitted_native_code() {
        let lib = PathBuf::from(std::env::var_os("CLEAN_LEAN436_LIB").unwrap());
        let world = LeanWorld::Lean436;
        clean_olean::check_olean_file_in_world(lib.join("Init/System/ST.olean"), world)
            .expect("CLEAN_LEAN436_LIB must contain the original stable state module");
        let mut env = Environment::new();
        clean_olean::declare_environment_world(&mut env, world.tag()).unwrap();
        clean_olean::load_module_with_deps(&mut env, "Init.System.ST", std::slice::from_ref(&lib))
            .unwrap();
        let string = Expr::const_str("String");
        let root = Name::from_string("makeStateToken");
        env.add_decl(Declaration::Definition {
            name: root,
            level_params: vec![],
            type_: Expr::arrow(
                string.clone(),
                Expr::app(Expr::const_str("Void"), string.clone()),
            ),
            value: Expr::lam(
                BinderInfo::Default,
                string.clone(),
                Expr::apps(Expr::const_str("Void.mk"), [string, Expr::bvar(0)]),
            ),
            is_reducible: false,
        })
        .unwrap();

        let project = tempfile::tempdir().unwrap();
        let file = project.path().join("Main.lean");
        let mut context = clean_elab::FileContext::new();
        context.set_import_context(&file, Ok(clean_olean::ImportWorld::Explicit { world, lib }));
        let compile = |env: &Environment| {
            emit_checked_native_c_artifact_in_context(
                &file,
                "makeStateToken",
                env,
                &CheckedNativeSource::default(),
                Some(&context),
                0,
            )
        };
        let actual = compile(&env).unwrap();
        let program = actual.emitted_c
            + r#"
int main(void) {
    clean_runtime_init();
    clean_obj* kept = clean_mk_string("token");
    clean_inc(kept);
    clean_obj* result = l_makeStateToken(kept);
    int ok = result == clean_box(0) && clean_is_exclusive(kept);
    clean_dec(kept);
    clean_runtime_finalize();
    return ok ? 0 : 1;
}
"#;
        let built = link_program_in_scratch(&program).unwrap();
        assert!(std::process::Command::new(built.binary())
            .status()
            .unwrap()
            .success());

        env.register_extern(Name::from_string("Void.mk"), "different_callee".into());
        let error = compile(&env).unwrap_err();
        assert!(
            format!("{error:#}").contains("stable Void.mk requires its SDK extern metadata"),
            "{error:#}"
        );
    }

    #[test]
    fn checked_context_refuses_a_different_declared_world_before_binding_selection() {
        let project = tempfile::tempdir().unwrap();
        let file = project.path().join("Main.lean");
        std::fs::write(
            &file,
            "prelude\nimport Init.System.IO\n\
             def faster (n : Nat) : Nat := n\n\
             @[noinline] def slower (n : Nat) : Nat := n\n\
             @[noinline] def oldCaller (n : Nat) : Nat := slower n\n\
             attribute [implemented_by faster] slower\n\
             def main : IO UInt32 := fun s => EST.Out.ok 7 s\n",
        )
        .unwrap();
        let env = crate::compile::elaborate_file_to_env(&file).unwrap();
        let mut context = clean_elab::FileContext::new();
        context.set_import_context(
            &file,
            Ok(clean_olean::ImportWorld::Explicit {
                world: LeanWorld::Lean436,
                lib: project.path().to_owned(),
            }),
        );
        assert!(state_entry::StateEntry::is_pinned_direct_action(
            &env,
            &Name::interned("main")
        ));
        assert!(clean_compiler::implemented_by_order(&env).is_some());
        let compile = |env: &Environment, context| {
            emit_checked_native_c_artifact_in_context(
                &file,
                "main",
                env,
                &CheckedNativeSource::default(),
                context,
                0,
            )
        };
        let error = compile(&env, Some(&context)).unwrap_err().to_string();
        assert!(
            error.contains("declares Lean world v4.36.0 but the environment contains v4.30.0-rc2"),
            "{error}"
        );
        let error = compile(&env, None).unwrap_err().to_string();
        assert!(error.contains("native-implemented-by-order"), "{error}");
        let error = compile(&Environment::new(), Some(&context))
            .unwrap_err()
            .to_string();
        assert!(
            error.contains("declaration `main` was not found"),
            "{error}"
        );
    }

    #[test]
    fn pinned_direct_unit_runs_the_checked_success_constructor() {
        let project = tempfile::tempdir().unwrap();
        let file = project.path().join("Main.lean");
        std::fs::write(
            &file,
            "prelude\nimport Init.System.IO\ndef main : IO Unit := fun s => EST.Out.ok () s\n",
        )
        .unwrap();
        let entry = emit_native_c_artifact(&file, "main", 0).unwrap();
        assert!(entry.state_entry.is_some());
        let binary = entry.build_in_scratch(true).unwrap();
        let output = Command::new(binary.binary()).output().unwrap();
        assert_eq!(output.status.code(), Some(0), "{output:?}");
        assert!(output.stdout.is_empty() && output.stderr.is_empty());
    }

    #[test]
    fn pinned_direct_user_errors_run_the_original_message() {
        let project = tempfile::tempdir().unwrap();
        let file = project.path().join("Main.lean");
        std::fs::write(
            &file,
            r#"prelude
import Init.System.IO

def failedUnit : IO Unit := fun world => .error (.userError "first-action-failed") world
def failedStatus : IO UInt32 := fun world => EST.Out.error (IO.Error.userError "échec") world
"#,
        )
        .unwrap();
        for (entry, message) in [
            ("failedUnit", "first-action-failed"),
            ("failedStatus", "échec"),
        ] {
            let artifact = emit_native_c_artifact(&file, entry, 0).unwrap();
            let binary = artifact.build_in_scratch(true).unwrap();
            let output = Command::new(binary.binary()).output().unwrap();
            assert_eq!(output.status.code(), Some(1), "{entry}: {output:?}");
            assert!(output.stdout.is_empty(), "{entry}: {output:?}");
            assert_eq!(
                output.stderr,
                format!("uncaught exception: {message}\n").as_bytes(),
                "{entry}"
            );
        }
    }

    #[test]
    fn pinned_direct_status_runs_its_payload_and_checks_live_externs() {
        let project = tempfile::tempdir().unwrap();
        let file = project.path().join("Main.lean");
        std::fs::write(
            &file,
            "prelude\nimport Init.System.IO\n\
             @[noinline] def status : UInt32 := 23\n\
             @[extern \"foreign_status\"] opaque foreignStatus (n : UInt32) : UInt32\n\
             def main : IO UInt32 := fun s => EST.Out.ok status s\n\
             def unbound : IO UInt32 := fun s => EST.Out.ok (foreignStatus 7) s\n",
        )
        .unwrap();
        let entry = emit_native_c_artifact(&file, "main", 0).unwrap();
        assert!(entry.state_entry.is_some());
        let binary = entry.build_in_scratch(true).unwrap();
        let output = Command::new(binary.binary()).output().unwrap();
        assert_eq!(output.status.code(), Some(23), "{output:?}");
        assert!(output.stdout.is_empty() && output.stderr.is_empty());

        let error = emit_native_c_artifact(&file, "unbound", 0).unwrap_err();
        let error = format!("{error:#}");
        assert!(
            error.contains("foreignStatus") && error.contains("native-extern"),
            "{error}"
        );
    }

    #[test]
    fn pinned_uint8_conversion_uses_its_native_c_binding() {
        let directory = tempfile::tempdir().expect("temporary source directory");
        let file = directory.path().join("Byte.lean");
        std::fs::write(
            &file,
            "prelude\nimport Init\n\
             def parseByte (n : Nat) : UInt8 := UInt8.ofNat n\n\
             def answer : Nat := @UInt8.rec (fun _ => Nat) (fun bits => @Fin.val 256 (@BitVec.toFin 8 bits)) (parseByte 1461501637330902918203684832716283019655932543020)\n",
        )
        .expect("write imported byte program");

        let artifact = emit_native_c_artifact(&file, "answer", 0).expect("emit the byte program");
        assert!(artifact.uint8_of_nat_shim);
        let rendered = artifact.render().expect("render the checked byte call");
        assert!(rendered.contains("clean_nat_low_u64(n)"));
        assert!(!rendered.contains("lean_uint8_of_nat("));
        assert!(rendered.contains("clean_obj* l_answer("), "{rendered}");
        let binary = artifact
            .build_in_scratch(true)
            .expect("link the byte program");
        let output = Command::new(binary.binary())
            .output()
            .expect("run the byte program");
        assert!(output.status.success(), "{:?}", output.stderr);
        assert_eq!(output.stdout, b"44\n");

        let args = CompileArgs {
            file: Some(file),
            decl: Some("answer".to_owned()),
            emit: EmitFormat::C,
            opt_level: 0,
            output: None,
            link_artifact: Vec::new(),
        };
        let (mut env, _, _) = crate::compile::elaborate_file_with_inventory(
            args.file.as_deref().expect("the byte program has a file"),
        )
        .expect("elaborate the byte program");
        let name = Name::from_string("UInt8.ofNat");
        assert!(has_pinned_uint8_of_nat_binding(&env, &name));
        env.register_extern(name.clone(), "different_uint8_of_nat".to_owned());
        assert!(!has_pinned_uint8_of_nat_binding(&env, &name));
        let mut context = clean_elab::FileContext::new();
        context.set_import_context_for_file(args.file.as_ref().unwrap());
        let scoped_refusal = CheckedNativeSource::default()
            .select(
                &env,
                Some(&context),
                &Name::from_string("answer"),
                0,
                None,
                crate::native_nat_display::NatDisplay::Bootstrap,
            )
            .err()
            .expect("scoped C selection must refuse a different extern binding");
        let scoped_refusal = format!("{scoped_refusal:#}");
        assert!(
            scoped_refusal.contains("native-extern-body"),
            "{scoped_refusal}"
        );
        assert!(
            scoped_refusal.contains("different_uint8_of_nat"),
            "{scoped_refusal}"
        );
        let refusal = match crate::compile::select_lcnf_decl(&args) {
            Err(error) => error,
            Ok(_) => panic!("generic compilation accepted the scoped C binding"),
        };
        assert!(refusal.to_string().contains("native-extern-body"));
    }
}

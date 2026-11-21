// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The IO entry representation selected by the checked source environment.

use super::*;

#[path = "native_state_entry_pinned.rs"]
mod pinned;
#[path = "native_state_entry_pinned_error.rs"]
mod pinned_error;
use clean_compiler::{main_signature::MainSignature, Decl};
use clean_kernel::{BinderInfo, Environment, LeanWorld, Name, TypeChecker};

#[derive(Debug)]
pub(super) struct StateEntry {
    contract: EntryContract,
    /// The logical entry already executes its action when called.
    action_body: bool,
    /// The emitted direct function still takes the boxed token.
    physical_world_parameter: bool,
    erased_world_fields: bool,
    user_error: Option<u32>,
    errors: Option<super::io_error::ErrorPrinter>,
}

pub(super) fn imported(env: &Environment, name: &str, module: &str) -> bool {
    let name = Name::interned(name);
    clean_olean::import::lean_declaration_artifact(env, &name).as_deref() == Some(module)
        && !env.is_unsafe(&name)
        && !env.is_partial(&name)
        && !env.is_noncomputable(&name)
        && !env.has_implemented_by(&name)
        && !env.is_extern(&name)
}

/// Check the imported userError equation without reducing through any
/// dependency whose compiled body can differ from its logical value.
fn check_user_error_equation(
    env: &Environment,
    formatter: &Name,
    expected_closure: &[u8; 32],
) -> anyhow::Result<()> {
    anyhow::ensure!(
        env.closure_digest(formatter)? == *expected_closure
            && !clean_kernel::env::csimp::has_invalid_metadata(env)
            && !clean_kernel::env::csimp::has_replacement(env, formatter),
        "IO error formatter has different source or compiler metadata"
    );
    let mut reduced = env.clone();
    for name in env.dependency_closure(formatter)? {
        let rules = clean_kernel::env::csimp::rules_for(env, Some(&name));
        let replaced_call = !rules.is_empty()
            && env
                .get_const(&name)
                .and_then(|info| info.value.as_ref())
                .is_some_and(|value| {
                    let mut names = std::collections::HashSet::new();
                    value.used_constants_dag(
                        clean_kernel::expr::UsedConstants::WithProjectionStructures,
                        &mut names,
                    );
                    rules.iter().any(|rule| names.contains(&rule.from))
                });
        if env.is_extern(&name)
            || env.has_implemented_by(&name)
            || env.is_unsafe(&name)
            || env.is_partial(&name)
            || env.is_noncomputable(&name)
            || replaced_call
        {
            reduced.forget_decl(&name);
        }
    }
    let string = Expr::const_str("String");
    let message = Expr::lam(BinderInfo::Default, string.clone(), Expr::bvar(0));
    let format_user = Expr::lam(
        BinderInfo::Default,
        string,
        Expr::app(
            Expr::const_(formatter.clone(), vec![]),
            Expr::app(Expr::const_str("IO.Error.userError"), Expr::bvar(0)),
        ),
    );
    anyhow::ensure!(
        TypeChecker::new(&reduced).is_def_eq(&message, &format_user),
        "IO.Error.toString does not return the userError message through its original definitions"
    );
    Ok(())
}

fn stable_user_error(env: &Environment) -> anyhow::Result<u32> {
    // Logical closure of IO.Error.toString in the release SDK, commit 611c117b.
    const FORMATTER: [u8; 32] = [
        0xe4, 0xf9, 0x80, 0x26, 0x86, 0xf4, 0x7e, 0xb3, 0x5d, 0xb8, 0x55, 0xb1, 0x93, 0x73, 0x2f,
        0x65, 0x5a, 0x51, 0x71, 0x3e, 0xf4, 0x7b, 0x9c, 0xfe, 0xd8, 0x5f, 0x14, 0x6c, 0x20, 0x3f,
        0x8a, 0x2a,
    ];
    checked_user_error_tag(env, &FORMATTER)
}

fn checked_user_error_tag(env: &Environment, expected_closure: &[u8; 32]) -> anyhow::Result<u32> {
    let error = Expr::const_str("IO.Error");
    let user = Name::interned("IO.Error.userError");
    let user_ctor = env
        .get_constructor(&user)
        .ok_or_else(|| anyhow!("missing IO.Error.userError"))?;
    let string = Expr::const_str("String");
    let formatter = Name::interned("IO.Error.toString");
    anyhow::ensure!(
        imported(env, "IO.Error", "Init.System.IOError")
            && imported(env, "IO.Error.userError", "Init.System.IOError")
            && imported(env, "IO.Error.toString", "Init.System.IOError")
            && !env.is_extern(&formatter)
            && user_ctor.inductive_name == Name::interned("IO.Error")
            && user_ctor.num_params == 0
            && user_ctor.num_fields == 1
            && user_ctor.type_ == Expr::arrow(string.clone(), error.clone())
            && env
                .get_inductive(&user_ctor.inductive_name)
                .and_then(|i| i.constructor_names.get(user_ctor.constructor_idx as usize))
                == Some(&user)
            && env
                .get_const(&formatter)
                .is_some_and(|f| f.type_ == Expr::arrow(error, string.clone())),
        "invalid IO error formatter or constructor"
    );
    let (constructors, _) = clean_compiler::to_ir::build_ctor_env(&[user_ctor])?;
    anyhow::ensure!(
        constructors.get(&user).is_some_and(|layout| {
            layout.tag == user_ctor.constructor_idx
                && layout.num_objects == 1
                && layout.num_scalars == 0
                && matches!(layout.field_types.as_slice(), [field] if field.is_object())
        }),
        "invalid emitted IO.Error.userError layout"
    );
    check_user_error_equation(env, &formatter, expected_closure)?;
    Ok(user_ctor.constructor_idx)
}

impl StateEntry {
    pub(super) fn check(
        env: &Environment,
        root: &Name,
        declarations: &[Decl],
    ) -> anyhow::Result<Option<Self>> {
        let direct = pinned::direct_result(env, root);
        let pinned = direct.is_some();
        if !pinned && clean_olean::environment_world(env) != Some(LeanWorld::Lean436.tag()) {
            return Ok(None);
        }
        let Some(entry) = env.get_const(root) else {
            return Ok(None);
        };
        let Some(signature) = MainSignature::from_type(&entry.type_) else {
            return Ok(None);
        };
        if !pinned
            && clean_olean::import::lean_declaration_artifact(env, &Name::interned("IO")).is_none()
        {
            // Bootstrap IO uses the eager ABI.
            return Ok(None);
        }
        for name in ["IO", "EIO", "IO.RealWorld"] {
            anyhow::ensure!(
                imported(env, name, "Init.System.IO"),
                "invalid stable IO declaration `{name}`"
            );
        }
        for name in ["EST", "EST.Out", "EST.Out.ok", "EST.Out.error", "Void"] {
            anyhow::ensure!(
                imported(env, name, "Init.System.ST"),
                "invalid stable state declaration `{name}`"
            );
        }
        if !pinned {
            let token = Name::interned("Void.mk");
            let token = env
                .get_const(&token)
                .ok_or_else(|| anyhow!("missing stable Void.mk"))?;
            anyhow::ensure!(
                crate::compile::stable_void::VoidMk::select(env, token)?.is_some(),
                "missing stable state token binding"
            );
        }

        let world = Expr::const_str("IO.RealWorld");
        let token = Expr::app(Expr::const_str("Void"), world.clone());
        let error = Expr::const_str("IO.Error");
        let (_, io) = peel_entry_binders(&entry.type_);
        let ExprKind::App(_, value) = io.kind() else {
            bail!("missing checked IO result type")
        };
        let result = Expr::apps(
            Expr::const_str("EST.Out"),
            [error.clone(), world, value.as_ref().clone()],
        );
        let tc = TypeChecker::new(env);
        anyhow::ensure!(
            tc.is_def_eq(io, &Expr::arrow(token.clone(), result)),
            "stable IO does not reduce to its EST.Out action"
        );
        let family = env
            .get_inductive(&Name::interned("EST.Out"))
            .ok_or_else(|| anyhow!("missing EST.Out family"))?;
        anyhow::ensure!(
            family.num_params == 3
                && family.num_indices == 0
                && family.level_params.is_empty()
                && family.constructor_names
                    == [
                        Name::interned("EST.Out.ok"),
                        Name::interned("EST.Out.error")
                    ],
            "invalid EST.Out constructor family"
        );
        for (index, name) in family.constructor_names.iter().enumerate() {
            let ctor = env
                .get_constructor(name)
                .ok_or_else(|| anyhow!("missing {name} constructor"))?;
            let mut ty = Expr::apps(
                Expr::const_str("EST.Out"),
                [Expr::bvar(4), Expr::bvar(3), Expr::bvar(2)],
            );
            ty = Expr::pi(
                BinderInfo::Default,
                Expr::app(Expr::const_str("Void"), Expr::bvar(2)),
                ty,
            );
            ty = Expr::pi(
                BinderInfo::Default,
                Expr::bvar(if index == 0 { 0 } else { 2 }),
                ty,
            );
            for _ in 0..3 {
                ty = Expr::pi(BinderInfo::Implicit, Expr::type_(), ty);
            }
            anyhow::ensure!(
                ctor.constructor_idx as usize == index
                    && ctor.inductive_name == family.name
                    && ctor.num_params == 3
                    && ctor.num_fields == 2
                    && ctor.type_ == ty,
                "invalid stable result constructor `{name}`"
            );
        }
        let lowered = declarations
            .iter()
            .find(|d| &d.name == root)
            .ok_or_else(|| anyhow!("missing selected entry `{root}`"))?;
        let params = lowered.params.as_slice();
        if signature.takes_argv {
            anyhow::ensure!(
                params
                    .first()
                    .is_some_and(|p| is_list_string(&p.ty) && !p.borrow),
                "the selected entry does not take an owned List String"
            );
        }
        let count = usize::from(signature.takes_argv);
        let erased_world_fields = clean_compiler::world_token::has_checked_void_layout(env);
        let (action_body, physical_world_parameter) = match params.get(count..) {
            Some([]) => (false, false),
            Some([p]) if !p.borrow && tc.is_def_eq(&p.ty, &token) => (
                true,
                !(erased_world_fields && clean_compiler::world_token::is_void_type(&p.ty)),
            ),
            _ => bail!("the selected stable IO entry has an unsupported world parameter"),
        };
        let user_error = match direct {
            Some(direct) => {
                pinned::check_lowered_result(env, root, lowered, signature.returns_status, direct)?;
                match direct {
                    pinned::DirectResult::Success => None,
                    pinned::DirectResult::UserError(_) => Some(pinned_error::user_error_tag(env)?),
                }
            }
            None => Some(stable_user_error(env)?),
        };
        Ok(Some(Self {
            contract: EntryContract {
                kind: EntryKind::Io,
                args: if signature.takes_argv {
                    EntryArgs::Argv
                } else {
                    EntryArgs::None
                },
                exit: if signature.returns_status {
                    EntryExit::FromUInt32
                } else {
                    EntryExit::AlwaysZero
                },
            },
            action_body,
            physical_world_parameter,
            erased_world_fields,
            user_error,
            errors: None,
        }))
    }

    pub(super) fn contract(&self, emitted_c: &str, mangled: &str) -> anyhow::Result<EntryContract> {
        let count = usize::from(self.contract.args == EntryArgs::Argv)
            + usize::from(self.physical_world_parameter);
        let code = c_scan_code(emitted_c);
        let mut defined = false;
        for line in code.lines() {
            let Some((name, params, definition)) = emitted_declarator(line) else {
                continue;
            };
            if name != mangled {
                continue;
            }
            let ok = if count == 0 {
                params == "void" || params.is_empty()
            } else {
                params.split(',').count() == count
                    && params.split(',').all(|p| {
                        p.trim()
                            .strip_prefix("clean_obj* ")
                            .is_some_and(|n| !n.is_empty() && n.bytes().all(is_ident_byte))
                    })
            };
            anyhow::ensure!(
                line.trim_start().starts_with("clean_obj* ") && ok && !(defined && definition),
                "emitted entry `{mangled}` disagrees with its checked stable IO ABI"
            );
            defined |= definition;
        }
        anyhow::ensure!(defined, "missing emitted stable IO entry `{mangled}`");
        Ok(self.contract)
    }

    pub(super) fn select_error_formatter(
        &mut self,
        env: &Environment,
        imports: &clean_olean::StableIoErrorImports,
    ) {
        if clean_olean::environment_world(env) == Some(LeanWorld::Lean436.tag())
            && self.user_error.is_some()
            && imports.check_externs(env).is_ok()
        {
            self.errors = super::io_error::ErrorPrinter::check(env).ok();
        }
    }

    pub(super) fn driver(&self, callee: &str) -> String {
        let mut s = String::new();
        if let Some(errors) = &self.errors {
            s.push_str("#define CLEAN_DRIVER_EXTENDED_IO_ERRORS 1\n");
            s.push_str(errors.definition());
        }
        s.push_str(include_str!("native_state_entry.c"));
        let argv = self.contract.args == EntryArgs::Argv;
        if argv {
            s.push_str(ARGV_MARSHAL_HELPER)
        }
        let main_params = if argv {
            "int argc, char** argv"
        } else {
            "void"
        };
        s.push_str(&format!(
            "\nint main({main_params}) {{\n  clean_runtime_init();\n"
        ));
        let args = match (argv, self.physical_world_parameter) {
            (false, false) => "",
            (true, false) => "_args",
            (false, true) => "clean_box(0)",
            (true, true) => "_args, clean_box(0)",
        };
        if argv {
            s.push_str("  clean_obj* _args = clean_driver_argv_list(argc, argv);\n")
        }
        s.push_str(&format!("  clean_obj* result = {callee}({args});\n  int status = clean_driver_finish_io(result, {}, {}, {}, {});\n  fflush(stdout);\n  fflush(stderr);\n  clean_runtime_finalize();\n  return status;\n}}\n", u8::from(self.action_body),u8::from(self.erased_world_fields),u8::from(self.contract.exit==EntryExit::FromUInt32),self.user_error.unwrap_or(u32::MAX)));
        s
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_compiler::constant_to_decl_in_runtime_closure;
    use clean_kernel::{ConstantOrigin, Declaration};

    #[test]
    fn checks_the_selected_physical_world_layout_at_the_native_boundary() {
        for (erased, action_body, user_error) in [
            (false, true, Some(0)),
            (true, true, Some(0)),
            (true, false, Some(0)),
            (false, true, None),
        ] {
            let state = StateEntry {
                contract: EntryContract {
                    kind: EntryKind::Io,
                    args: EntryArgs::None,
                    exit: EntryExit::FromUInt32,
                },
                action_body,
                physical_world_parameter: action_body && !erased,
                erased_world_fields: erased,
                user_error,
                errors: None,
            };
            let mut source = String::new();
            if erased {
                source.push_str("#define TEST_ERASED_WORLD 1\n");
            }
            if !action_body {
                source.push_str("#define TEST_RETURN_ACTION 1\n");
            }
            source.push_str(include_str!("native_state_entry_test.c"));
            let dir = tempfile::tempdir().expect("native ABI test directory");
            let executable = super::super::build_extract_executable(
                dir.path(),
                "",
                &source,
                &state.driver("l_sourceEntry"),
            )
            .expect("compile the checked world driver");
            for (sample, status) in [
                ("status", 23),
                ("tag", 1),
                ("arity", 1),
                ("payload", 1),
                ("scalar", 1),
                ("error_tag", 1),
                ("user_error", 1),
                ("world", 1),
            ] {
                let out = std::process::Command::new(&executable)
                    .env("CLEAN_TEST_NATIVE_RESULT", sample)
                    .output()
                    .unwrap();
                assert_eq!(
                    out.status.code(),
                    Some(status),
                    "{erased} {action_body} {sample}"
                );
                assert!(out.stdout.is_empty());
                let expected_stderr = match sample {
                    "status" => "",
                    "user_error" if user_error.is_some() => "uncaught exception: boom\n",
                    _ => "clean: unsupported native IO result or error representation\n",
                };
                assert_eq!(out.stderr, expected_stderr.as_bytes());
            }
        }
    }

    #[test]
    #[ignore = "requires the official CLEAN_LEAN436_LIB"]
    fn stable_io_driver_rejects_substituted_source_and_raw_abis() {
        let lib = std::path::PathBuf::from(std::env::var_os("CLEAN_LEAN436_LIB").unwrap());
        let mut env = Environment::new();
        clean_olean::declare_environment_world(&mut env, LeanWorld::Lean436.tag()).unwrap();
        clean_olean::load_module_with_deps(&mut env, "Init.System.IO", &[lib]).unwrap();
        let root = Name::interned("sourceEntry");
        let world = Expr::const_str("IO.RealWorld");
        let status = Expr::const_str("UInt32");
        let token = Expr::app(Expr::const_str("Void"), world.clone());
        let code = Expr::app(Expr::const_str("UInt32.ofNat"), Expr::nat_lit(23u64));
        let value = Expr::apps(
            Expr::const_str("EST.Out.ok"),
            [
                Expr::const_str("IO.Error"),
                world,
                status.clone(),
                code,
                Expr::bvar(0),
            ],
        );
        env.add_decl(Declaration::Definition {
            name: root.clone(),
            level_params: vec![],
            type_: Expr::app(Expr::const_str("IO"), status),
            value: Expr::lam(BinderInfo::Default, token, value),
            is_reducible: false,
        })
        .unwrap();
        let closure = clean_compiler::RuntimeBindingClosure::check_executable(
            &env,
            std::slice::from_ref(&root),
        )
        .unwrap();
        let root_declaration =
            constant_to_decl_in_runtime_closure(&env, env.get_const(&root).unwrap(), &closure)
                .unwrap()
                .unwrap();
        let declarations = std::slice::from_ref(&root_declaration);
        let checked = StateEntry::check(&env, &root, declarations)
            .unwrap()
            .expect("stable entry");
        let name = "l_sourceEntry";
        checked
            .contract("clean_obj* l_sourceEntry(clean_obj* _x0) {", name)
            .unwrap();
        for c in ["clean_obj* l_sourceEntry(void) {", "clean_obj* l_sourceEntry(clean_obj* _x0, clean_obj* _x1) {", "uint32_t l_sourceEntry(clean_obj* _x0) {", "clean_obj* l_sourceEntry(uint32_t _x0) {", "clean_obj* l_sourceEntry(clean_obj* _x0);", "clean_obj* l_sourceEntry(clean_obj* _x0) {\nclean_obj* l_sourceEntry(clean_obj* _x0) {"] {
            assert!(checked.contract(c,name).is_err(),"{c}");
        }
        for n in [
            "EST.Out.ok",
            "IO.Error.toString",
            "IO.Error.userError",
            "IO.RealWorld",
        ] {
            let mut foreign = env.clone();
            assert!(foreign.set_constant_origin(
                Name::interned(n),
                ConstantOrigin::olean_import(Some("Other.Module".to_string()))
            ));
            assert!(
                StateEntry::check(&foreign, &root, declarations).is_err(),
                "{n}"
            );
        }
        let mut rebound = env.clone();
        rebound.register_extern(
            Name::interned("IO.Error.toString"),
            "wrong_error_formatter".into(),
        );
        assert!(StateEntry::check(&rebound, &root, declarations).is_err());
        let formatter = env.get_const(&Name::interned("IO.Error.toString")).unwrap();
        let ExprKind::Lam(_, _, body) = formatter.value.as_ref().unwrap().kind() else {
            panic!("expected stable SDK formatter lambda")
        };
        let ExprKind::Const(matcher, _) = body.get_app_fn().kind() else {
            panic!("expected stable SDK formatter match helper")
        };
        let mut overridden_helper = env.clone();
        overridden_helper.register_extern(matcher.clone(), "different_match_helper".into());
        assert!(StateEntry::check(&overridden_helper, &root, declarations).is_err());
        let mut nested = env.clone();
        nested.register_extern(Name::interned("Nat.div"), "lean_nat_div".into());
        assert!(super::super::io_error::ErrorPrinter::check(&nested).is_err());
        let mut changed_get = env.clone();
        changed_get.register_extern(
            Name::interned("String.Pos.Raw.get"),
            "lean_string_utf8_get".into(),
        );
        assert!(super::super::io_error::ErrorPrinter::check(&changed_get).is_err());
        let mut bad_root = root_declaration;
        bad_root.params[0].borrow = true;
        assert!(StateEntry::check(&env, &root, &[bad_root]).is_err());
    }
}

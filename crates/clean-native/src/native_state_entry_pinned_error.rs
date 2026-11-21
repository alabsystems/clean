// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The `userError` formatter selected by the pinned 4.30 SDK.

use super::*;

pub(super) fn user_error_tag(env: &Environment) -> anyhow::Result<u32> {
    // IO.Error.toString on Lean 4.30.0-rc2, 3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc.
    const FORMATTER: [u8; 32] = [
        0x4f, 0x03, 0xee, 0x21, 0x64, 0x07, 0x9f, 0x96, 0xf8, 0x2f, 0xb8, 0x42, 0x4d, 0x58, 0xf2,
        0xc1, 0x53, 0x0e, 0x8e, 0x0c, 0x3d, 0x7a, 0x60, 0x3e, 0x4c, 0x5b, 0x24, 0x45, 0xe6, 0x0f,
        0xf0, 0xb6,
    ];
    anyhow::ensure!(
        clean_olean::environment_world(env) == Some(LeanWorld::Lean430Rc2.tag()),
        "pinned userError formatter requires Lean 4.30.0-rc2"
    );
    super::checked_user_error_tag(env, &FORMATTER)
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::env::ConstantOrigin;

    #[test]
    fn pinned_error_formatter_checks_the_original_and_refuses_changed_compiler_meaning() {
        let dir = tempfile::tempdir().unwrap();
        let file = dir.path().join("Entry.lean");
        std::fs::write(&file, "prelude\nimport Init.System.IO\n\ndef originalError : IO UInt32 := fun w => EST.Out.error (IO.Error.userError \"probe\") w\n").unwrap();
        let env = crate::compile::elaborate_file_to_env(&file).unwrap();
        let user = Name::interned("IO.Error.userError");
        let formatter = Name::interned("IO.Error.toString");
        let constructor = env.get_constructor(&user).unwrap();
        assert_eq!(user_error_tag(&env).unwrap(), constructor.constructor_idx);
        let mut changed_body = env.clone();
        assert!(changed_body.forget_decl(&formatter));
        changed_body
            .add_decl(clean_kernel::env::Declaration::Definition {
                name: formatter.clone(),
                level_params: vec![],
                type_: env.get_const(&formatter).unwrap().type_.clone(),
                value: Expr::lam(
                    BinderInfo::Default,
                    Expr::const_str("IO.Error"),
                    Expr::str_lit("changed"),
                ),
                is_reducible: false,
            })
            .unwrap();
        assert_eq!(
            changed_body.get_constant_origin(&formatter),
            env.get_constant_origin(&formatter)
        );
        assert!(user_error_tag(&changed_body)
            .unwrap_err()
            .to_string()
            .contains("different source or compiler metadata"));
        let mut wrong_owner = env.clone();
        assert!(wrong_owner.set_constant_origin(
            user.clone(),
            ConstantOrigin::olean_import(Some("Other.Module".into()))
        ));
        assert!(user_error_tag(&wrong_owner)
            .unwrap_err()
            .to_string()
            .contains("formatter or constructor"));
        let mut replaced_formatter = env.clone();
        replaced_formatter
            .register_implemented_by(formatter.clone(), Name::interned("otherFormatter"));
        assert!(user_error_tag(&replaced_formatter)
            .unwrap_err()
            .to_string()
            .contains("formatter or constructor"));
        let info = env.get_const(&formatter).unwrap();
        let ExprKind::Lam(_, _, body) = info.value.as_ref().unwrap().kind() else {
            panic!("expected SDK formatter lambda")
        };
        let ExprKind::Const(matcher, _) = body.get_app_fn().kind() else {
            panic!("expected SDK formatter matcher")
        };
        let mut overridden_matcher = env.clone();
        overridden_matcher.register_extern(matcher.clone(), "different_error_matcher".into());
        assert!(user_error_tag(&overridden_matcher)
            .unwrap_err()
            .to_string()
            .contains("original definitions"));
    }

    #[test]
    #[ignore = "requires the official CLEAN_LEAN436_LIB"]
    fn pinned_error_formatter_refuses_the_stable_sdk_world() {
        let lib = std::path::PathBuf::from(std::env::var_os("CLEAN_LEAN436_LIB").unwrap());
        let mut stable = Environment::new();
        clean_olean::declare_environment_world(&mut stable, LeanWorld::Lean436.tag()).unwrap();
        clean_olean::load_module_with_deps(&mut stable, "Init.System.IO", &[lib]).unwrap();
        assert!(stable
            .get_const(&Name::interned("IO.Error.toString"))
            .is_some());
        assert!(user_error_tag(&stable)
            .unwrap_err()
            .to_string()
            .contains("requires Lean 4.30.0-rc2"));
        assert_eq!(
            super::super::stable_user_error(&stable).unwrap(),
            stable
                .get_constructor(&Name::interned("IO.Error.userError"))
                .unwrap()
                .constructor_idx
        );
    }
}

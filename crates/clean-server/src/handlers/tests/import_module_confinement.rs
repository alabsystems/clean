// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Each module file `importModule` reads from a client's search path, the
//! requested module's and every one an `.olean` header in its import graph
//! lists, must resolve under that search path (`trust_boundary::ModuleSearch`),
//! not only the search path under the workspace root. Unix only: the tests make
//! symbolic links.

use super::launch_token_of;
use crate::handlers::*;
use clean_kernel::{Declaration, Environment, Expr, Name};
use std::fs;
use std::path::Path;

/// A module whose one declaration is the axiom `<stem>.imported`, importing
/// `imports`, exported as `<stem>.olean` into `dir`.
fn write_axiom_module(dir: &Path, stem: &str, imports: &[(&str, bool)]) {
    let mut env = Environment::default();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(&format!("{stem}.imported")),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("an axiom whose type is Prop is admitted");
    let bytes = clean_olean::OleanExporter::export_with_env(
        &env,
        imports,
        &[],
        "c0de000000000000000000000000000000000003",
    )
    .expect("export the fixture module");
    fs::write(dir.join(format!("{stem}.olean")), bytes).expect("write the fixture module");
}

/// With `oleans/Ext -> <outside>`, module `Ext.Outside` in search path
/// `oleans` read `<outside>/Outside.olean` and installed its axiom, though
/// `oleans` resolves under the root; so did a part beside a module file
/// inside the search path (`Sib/Sibling.olean.private -> <outside>/...`). A
/// link that stays inside the search path is followed.
#[tokio::test]
async fn test_import_module_file_linked_out_of_its_search_path_is_refused() {
    use std::os::unix::fs::symlink;
    let root = tempfile::tempdir().expect("root");
    let outside = tempfile::tempdir().expect("outside");
    let oleans = root.path().join("oleans");
    fs::create_dir_all(oleans.join("Real")).expect("oleans/Real");
    fs::create_dir_all(oleans.join("Sib")).expect("oleans/Sib");
    write_axiom_module(&oleans.join("Real"), "Inside", &[]);
    write_axiom_module(&oleans.join("Sib"), "Sibling", &[]);
    write_axiom_module(outside.path(), "Outside", &[]);
    symlink(outside.path(), oleans.join("Ext")).expect("a directory link out of the search path");
    symlink(oleans.join("Real"), oleans.join("Alias")).expect("a directory link inside it");
    symlink(
        outside.path().join("Outside.olean"),
        oleans.join("Sib").join("Sibling.olean.private"),
    )
    .expect("a part linked out of the search path");

    let state = ServerState::from_root(root.path());
    let import = |module: &str| ImportModuleParams {
        module: module.to_string(),
        search_paths: vec!["oleans".to_string()],
        timeout_ms: Some(60_000),
        token: launch_token_of(&state),
    };
    // The server's root is the real root; a relative search path joins it.
    let real_oleans = fs::canonicalize(root.path())
        .expect("canonical root")
        .join("oleans");
    let real_outside = fs::canonicalize(outside.path()).expect("canonical outside");

    for (module, file) in [
        ("Ext.Outside", real_oleans.join("Ext").join("Outside.olean")),
        (
            "Sib.Sibling",
            real_oleans.join("Sib").join("Sibling.olean.private"),
        ),
    ] {
        let response = handle_import_module(&state, RequestId::Number(1), import(module)).await;
        let error = response.error.unwrap_or_else(|| {
            panic!(
                "{module}: importModule read a module file outside its search path: {:?}",
                response.result
            )
        });
        assert_eq!(
            (error.code, error.message),
            (
                crate::rpc::error_codes::OUTSIDE_WORKSPACE,
                format!(
                    "importModule refuses module `{module}`: its file `{}` resolves to `{}`, \
                     which is not under its search path `{}`",
                    file.display(),
                    real_outside.join("Outside.olean").display(),
                    real_oleans.display()
                )
            ),
            "{module}"
        );
    }
    {
        let env = state.env.read().await;
        for name in ["Outside.imported", "Sibling.imported"] {
            assert!(
                env.get_const(&Name::from_string(name)).is_none(),
                "{name} was imported"
            );
        }
    }

    // Control: a link that stays inside the search path is followed.
    let response = handle_import_module(&state, RequestId::Number(2), import("Alias.Inside")).await;
    assert!(
        response.error.is_none(),
        "a module through a link inside the search path: {:?}",
        response.error
    );
    let env = state.env.read().await;
    assert!(
        env.get_const(&Name::from_string("Inside.imported"))
            .is_some(),
        "the control imported its axiom"
    );
}

/// The imports an `.olean` header lists are resolved from the same search
/// paths, and a file one resolves to in a client's search path must resolve
/// under it too: with `oleans/Ext -> <outside>`, module `W`, whose own file
/// lies inside `oleans`, imports `Ext.Outside`, and the server read
/// `<outside>/Outside.olean` and installed both modules' axioms. Nothing is
/// installed now. An import through a link that stays inside is followed.
#[tokio::test]
async fn test_import_module_header_import_linked_out_of_its_search_path_is_refused() {
    use std::os::unix::fs::symlink;
    let root = tempfile::tempdir().expect("root");
    let outside = tempfile::tempdir().expect("outside");
    let oleans = root.path().join("oleans");
    fs::create_dir_all(oleans.join("Real")).expect("oleans/Real");
    write_axiom_module(&oleans.join("Real"), "Inside", &[]);
    write_axiom_module(outside.path(), "Outside", &[]);
    write_axiom_module(&oleans, "W", &[("Ext.Outside", false)]);
    write_axiom_module(&oleans, "V", &[("Alias.Inside", false)]);
    symlink(outside.path(), oleans.join("Ext")).expect("a directory link out of the search path");
    symlink(oleans.join("Real"), oleans.join("Alias")).expect("a directory link inside it");

    let state = ServerState::from_root(root.path());
    let import = |module: &str| ImportModuleParams {
        module: module.to_string(),
        search_paths: vec!["oleans".to_string()],
        timeout_ms: Some(60_000),
        token: launch_token_of(&state),
    };
    let real_oleans = fs::canonicalize(root.path())
        .expect("canonical root")
        .join("oleans");
    let real_outside = fs::canonicalize(outside.path()).expect("canonical outside");

    let response = handle_import_module(&state, RequestId::Number(1), import("W")).await;
    let error = response.error.unwrap_or_else(|| {
        panic!(
            "W's header import read a module file outside its search path: {:?}",
            response.result
        )
    });
    assert_eq!(
        (error.code, error.message),
        (
            crate::rpc::error_codes::OUTSIDE_WORKSPACE,
            format!(
                "importModule refuses module `W`: the file `{}` of `Ext.Outside`, in its import \
                 graph, resolves to `{}`, which is not under its search path `{}`",
                real_oleans.join("Ext").join("Outside.olean").display(),
                real_outside.join("Outside.olean").display(),
                real_oleans.display()
            )
        )
    );
    {
        let env = state.env.read().await;
        for name in ["W.imported", "Outside.imported"] {
            assert!(
                env.get_const(&Name::from_string(name)).is_none(),
                "{name} was imported"
            );
        }
    }

    // Control: an import through a link that stays inside the search path.
    let response = handle_import_module(&state, RequestId::Number(2), import("V")).await;
    assert!(
        response.error.is_none(),
        "a module whose import goes through a link inside the search path: {:?}",
        response.error
    );
    let env = state.env.read().await;
    for name in ["V.imported", "Inside.imported"] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "the control did not import {name}"
        );
    }
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bind the two stable source externs for the calling thread's stdout.

use anyhow::{ensure, Result};
use clean_kernel::{ConstantInfo, ConstantKind, Environment, Expr, LeanWorld, Name};

#[derive(Default)]
pub(crate) struct StdoutBindings {
    get: bool,
    set: bool,
}

impl StdoutBindings {
    pub(crate) fn is_empty(&self) -> bool {
        !self.get && !self.set
    }

    pub(crate) fn operations(&self) -> impl Iterator<Item = (&'static str, &'static str, usize)> {
        [
            (self.get, "l_IO_getStdout", "clean_stdio_get_stdout", 1),
            (self.set, "l_IO_setStdout", "clean_stdio_set_stdout", 2),
        ]
        .into_iter()
        .filter_map(|(used, n, imp, args)| used.then_some((n, imp, args)))
    }

    pub(crate) fn select(
        &mut self,
        env: &Environment,
        info: &ConstantInfo,
        context: Option<&clean_elab::FileContext>,
    ) -> Result<bool> {
        let get = info.name == Name::interned("IO.getStdout");
        if (!get && info.name != Name::interned("IO.setStdout"))
            || clean_olean::environment_world(env) != Some(LeanWorld::Lean436.tag())
        {
            return Ok(false);
        }
        ensure!(
            cfg!(all(target_os = "macos", target_arch = "aarch64")),
            "stable stdout's operating-system error ABI is unavailable on this host"
        );
        let imports = context
            .and_then(clean_elab::FileContext::stable_stdout_imports)
            .ok_or_else(|| {
                anyhow::anyhow!(
                    "stable stdout's original source and native IR are unavailable in this import"
                )
            })?;
        ensure!(
            imports.check_externs(env),
            "stable stdout's imported runtime operations changed"
        );
        let stream = Expr::const_str("IO.FS.Stream");
        let action = Expr::app(Expr::const_str("BaseIO"), stream.clone());
        let expected = if get {
            action
        } else {
            Expr::arrow(stream, action)
        };
        ensure!(
            info.type_ == expected
                && info.level_params.is_empty()
                && (info.kind == ConstantKind::Opaque
                    || (info.kind == ConstantKind::Axiom && info.value.is_none())),
            "stable stdout requires its original BaseIO telescope"
        );
        if self.is_empty() {
            check_source_layouts(env)?;
        }
        if get {
            self.get = true;
        } else {
            self.set = true;
        }
        Ok(true)
    }
}

fn check_source_layouts(env: &Environment) -> Result<()> {
    // Recheck the declarations actually registered in the file environment. This
    // covers modules already present when the explicit import graph was visited.
    for (text, owner, expected) in [
        (
            "IO.FS.Stream.ofHandle",
            "Init.System.IO",
            "097ad8394d414d95948f0b08e09f7645ad2b9726b117004e8aecd84137ef767e",
        ),
        (
            "IO.FS.Stream.mk",
            "Init.System.IO",
            "d757dd6c273cd860b44849a99ca7ce068912a2623021397e1fbd84a698fca8e2",
        ),
        (
            "IO.FS.Stream.putStr",
            "Init.System.IO",
            "0094a9f2a6652fce32caae85f8089c2d3ca1ed3007667068c85a98d488e456f8",
        ),
        (
            "IO.getStdout",
            "Init.System.IO",
            "71f55d542a8bf8a8664ac33c5bbc1ae476a7a986419a0ae699bc984a34ffbbb3",
        ),
        (
            "IO.setStdout",
            "Init.System.IO",
            "aaf5ada41f9aedad515c0312b6cbbc674429de1de7cd92822dc9b89c8964f47a",
        ),
        (
            "IO.Error",
            "Init.System.IOError",
            "88b2989db53e08d7c8c6acd95e9b17acf5a0e5235439d6d25085078cbf8e308b",
        ),
        (
            "ST.Out.mk",
            "Init.System.ST",
            "827028e7bce040c0c0c3f5872db275ace1838f081aa84727ce34ea3dfaffd373",
        ),
        (
            "EST.Out.ok",
            "Init.System.ST",
            "91550ed933765f79bfc81d153cca6bdff9f8ede52e558cbdfe18253ab7eae489",
        ),
        (
            "EST.Out.error",
            "Init.System.ST",
            "02d5edd70dd7bbfabfd6d4f9bbd5fc9d01c9669891d94f7141cf4989e308f1a8",
        ),
        (
            "String",
            "Init.Prelude",
            "4e1016a34c29883f88fc3a5aba9109e7396aa5d60a09e51455b924df4331f5fa",
        ),
        (
            "ByteArray",
            "Init.Prelude",
            "c817084beead982690c8fc0707b5f030496a71a890f16a8236fdc0fab6107741",
        ),
        (
            "Array",
            "Init.Prelude",
            "152108f3034fbd2d3dce3b5fcdb59fa836ba713873400febd2925c6efbdc8791",
        ),
        (
            "List",
            "Init.Prelude",
            "99738799cbac440684fad6ae9991529ac002c4f18e4b7459f9699111e77bba75",
        ),
        (
            "Bool",
            "Init.Prelude",
            "06acfb096d641b0452559da5319c955ccc87beb4ad9722d9a241541f25c0d875",
        ),
        (
            "Unit",
            "Init.Prelude",
            "3e29427d6726621c6d41136cdb0d64e640666f60af6b3ff14a3b6c48b7ed53ce",
        ),
        (
            "USize",
            "Init.Prelude",
            "535632ebb74900dc45653abfecf6e3523387d4e0e8fe35ccddc90e1661d0fafc",
        ),
    ] {
        let name = Name::interned(text);
        ensure!(
            clean_olean::import::lean_declaration_artifact(env, &name).as_deref() == Some(owner)
                && env
                    .closure_digest(&name)?
                    .iter()
                    .map(|b| format!("{b:02x}"))
                    .collect::<String>()
                    == expected,
            "stable stdout's registered source or layout changed at {name}"
        );
    }
    let stream = Name::interned("IO.FS.Stream");
    let ctor = Name::interned("IO.FS.Stream.mk");
    ensure!(
        clean_olean::import::lean_declaration_artifact(env, &ctor).as_deref()
            == Some("Init.System.IO")
            && env.get_inductive(&stream).is_some_and(|f| !f.is_recursive
                && f.num_params == 0
                && f.num_indices == 0
                && f.constructor_names == [ctor.clone()])
            && env
                .get_constructor(&ctor)
                .is_some_and(|c| c.inductive_name == stream
                    && c.num_params == 0
                    && c.constructor_idx == 0
                    && c.num_fields == 6),
        "stable stdout requires the six-method SDK stream layout"
    );
    let state = Name::interned("ST.Out.mk");
    ensure!(
        clean_olean::import::lean_declaration_artifact(env, &state).as_deref()
            == Some("Init.System.ST")
            && env.get_constructor(&state).is_some_and(|c| c.inductive_name
                == Name::interned("ST.Out")
                && c.constructor_idx == 0
                && c.num_params == 2
                && c.num_fields == 2),
        "stable stdout requires the SDK state result"
    );
    Ok(())
}

// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0
//! Compiled-value copies, precise refusal classification and pinned metadata.
use super::{data, PIN};
use clean_kernel::env::{ConstantInfo, ConstantKind, Declaration, Environment};
use clean_kernel::{KernelEnvError, KernelTypeError, Name, ReferenceRefusal};
use clean_olean::ndjson::ExportWriteMeta;
use std::collections::BTreeSet;
use std::path::Path;
use std::process::Command;

pub(super) fn kind(c: &ConstantInfo) -> &'static str {
    match c.kind {
        ConstantKind::Theorem => "theorem",
        ConstantKind::Definition => "definition",
        ConstantKind::Opaque => "opaque",
        ConstantKind::Axiom => "axiom",
    }
}
pub(super) fn mismatch<T>(result: &Result<T, ReferenceRefusal>) -> bool {
    matches!(
        result,
        Err(ReferenceRefusal::Kernel(KernelEnvError::TypeCheckFailed {
            source: KernelTypeError::TypeMismatch { .. },
            ..
        }))
    )
}
pub(super) fn checked_copy(c: &ConstantInfo, name: Name) -> Declaration {
    let level_params = c.level_params.clone();
    let type_ = c.type_.clone();
    let value = c.value.clone().expect("compiled stored value");
    match c.kind {
        ConstantKind::Theorem => Declaration::Theorem {
            name,
            level_params,
            type_,
            value,
        },
        ConstantKind::Definition => Declaration::Definition {
            name,
            level_params,
            type_,
            value,
            is_reducible: c.is_reducible,
        },
        ConstantKind::Opaque => Declaration::Opaque {
            name,
            level_params,
            type_,
            value,
        },
        ConstantKind::Axiom => panic!("own axiom cannot be a proof"),
    }
}
pub(super) fn closure(c: &Name, env: &Environment) -> BTreeSet<String> {
    let mut result = env.axiom_deps(c).expect("transitive axiom closure");
    result.extend(
        env.foundational_axiom_deps(c)
            .expect("foundational axiom closure"),
    );
    // Quot's four primitives are infrastructure. Lean collectAxioms counts
    // Quot.sound, not the primitive declarations; keep exactly Ax0 here.
    result
        .iter()
        .map(ToString::to_string)
        .filter(|n| !["Quot", "Quot.mk", "Quot.lift", "Quot.ind"].contains(&n.as_str()))
        .collect()
}
pub(super) fn metadata(lean: &Path) -> ExportWriteMeta {
    let ask = |flag: &str| {
        let out = Command::new(lean)
            .arg(flag)
            .output()
            .expect("pinned Lean identity");
        data::command_ok(flag, &out);
        String::from_utf8(out.stdout)
            .expect("Lean identity UTF8")
            .trim()
            .to_owned()
    };
    let version = ask("--version");
    let lean_version = version
        .split_once("version ")
        .and_then(|(_, s)| s.split_once(','))
        .expect("Lean version line")
        .0
        .to_owned();
    assert_eq!(format!("leanprover/lean4:v{lean_version}"), PIN);
    ExportWriteMeta {
        lean_version,
        lean_githash: ask("--githash"),
    }
}
pub(super) fn source_modules(root: &Path, dir: &Path, out: &mut BTreeSet<String>) {
    for item in std::fs::read_dir(dir).expect("theory sources") {
        let item = item.expect("source entry");
        let p = item.path();
        if item.file_name().to_string_lossy().starts_with('.') {
            continue;
        }
        if item.file_type().expect("source kind").is_dir() {
            source_modules(root, &p, out);
        } else if p.extension().is_some_and(|e| e == "lean") && item.file_name() != "lakefile.lean"
        {
            assert!(
                out.insert(
                    p.strip_prefix(root)
                        .expect("own source")
                        .with_extension("")
                        .to_string_lossy()
                        .replace(std::path::MAIN_SEPARATOR, ".")
                ),
                "duplicate source module"
            );
        }
    }
}

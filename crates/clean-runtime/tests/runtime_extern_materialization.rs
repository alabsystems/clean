// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Build-guard for the trust-cg inline-primitive bridge.
//!
//! `runtime_extern.c` materializes the header's `static inline` RC/box/field
//! primitives as real external symbols so the trust-cg `ExternCalls` backend
//! can bind them at link time. This test pins three properties the bridge must
//! keep:
//!
//!   1. `runtime_extern.c` compiles (crate-relative include rewritten to flat),
//!   2. it EXPORTS a real (defined-text) external symbol for each named
//!      primitive the trust-cg path calls, and
//!   3. it LINKS alongside `clean_runtime.o` with NO duplicate-symbol clash —
//!      i.e. the header stays `static inline` (emit_c inlines) while exactly one
//!      external definition of each name exists (in `runtime_extern.o`).
//!
//! A regression here (header primitive changed to non-inline, a rename typo, a
//! duplicate definition) fails the build the same way the trust-cg census would.

use std::path::{Path, PathBuf};
use std::process::Command;

fn find_c_compiler() -> Option<&'static str> {
    ["cc", "gcc", "clang"].into_iter().find(|compiler| {
        Command::new(compiler)
            .arg("--version")
            .output()
            .map(|o| o.status.success())
            .unwrap_or(false)
    })
}

fn include_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("include")
}

/// Symbols the trust-cg path lowers to external calls; each MUST be a defined
/// external symbol in `runtime_extern.o`.
const REQUIRED_SYMBOLS: &[&str] = &[
    "clean_inc",
    "clean_box",
    "clean_unbox",
    "clean_ctor_get",
    "clean_obj_tag",
    "clean_unbox_uint64",
    "clean_unbox_uint32",
    "clean_unbox_float",
    "clean_is_exclusive",
];

/// Write a crate source string to `dir`, rewriting the crate-relative header
/// include to a flat one so `-I<dir>` resolves it.
fn materialize(dir: &Path, name: &str, src: &str) -> PathBuf {
    let flat = src.replacen("../include/clean_runtime.h", "clean_runtime.h", 1);
    let p = dir.join(name);
    std::fs::write(&p, flat).expect("write source");
    p
}

#[test]
fn runtime_extern_materializes_linkable_primitive_symbols() {
    let Some(cc) = find_c_compiler() else {
        eprintln!("no C compiler (cc/gcc/clang) — skipping runtime_extern build-guard");
        return;
    };
    let dir = tempfile::tempdir().expect("tempdir");
    // Header next to the flattened sources so `#include "clean_runtime.h"` works.
    std::fs::write(
        dir.path().join("clean_runtime.h"),
        clean_runtime::runtime_header(),
    )
    .expect("write header");
    let rt_c = materialize(
        dir.path(),
        "clean_runtime.c",
        clean_runtime::runtime_source(),
    );
    let rte_c = materialize(
        dir.path(),
        "runtime_extern.c",
        clean_runtime::runtime_extern_source(),
    );

    let compile = |src: &Path, obj: &Path| {
        let out = Command::new(cc)
            .args(["-O2", "-std=c11", "-c"])
            .arg(src)
            .arg("-I")
            .arg(dir.path())
            .arg("-o")
            .arg(obj)
            .output()
            .expect("spawn cc");
        assert!(
            out.status.success(),
            "compiling {} failed:\n{}",
            src.display(),
            String::from_utf8_lossy(&out.stderr)
        );
    };

    let rt_o = dir.path().join("clean_runtime.o");
    let rte_o = dir.path().join("runtime_extern.o");
    // clean_runtime.c must still compile standalone (bridge does not touch it).
    compile(&rt_c, &rt_o);
    // runtime_extern.c must compile (bridge itself well-formed).
    compile(&rte_c, &rte_o);

    // (2) Every required primitive is a DEFINED external symbol in the bridge TU.
    let nm = Command::new("nm").arg(&rte_o).output().expect("spawn nm");
    assert!(nm.status.success(), "nm failed on {}", rte_o.display());
    let syms = String::from_utf8_lossy(&nm.stdout);
    let defined: std::collections::HashSet<&str> = syms
        .lines()
        .filter(|l| {
            let mut it = l.split_whitespace();
            // "<addr> T _name" — a defined text symbol.
            matches!(it.nth(1), Some("T"))
        })
        .filter_map(|l| l.split_whitespace().nth(2))
        // Strip the Mach-O leading underscore.
        .map(|s| s.strip_prefix('_').unwrap_or(s))
        .collect();
    for want in REQUIRED_SYMBOLS {
        assert!(
            defined.contains(want),
            "runtime_extern.o does not export a defined `{want}` symbol; got: {:?}",
            defined
        );
    }

    // (3) The two objects LINK together with no duplicate-symbol clash.
    let main_c = dir.path().join("m.c");
    std::fs::write(&main_c, "int main(void){return 0;}\n").expect("write main");
    let bin = dir.path().join("prog");
    let link = Command::new(cc)
        .arg("-O0")
        .arg(&main_c)
        .arg(&rt_o)
        .arg(&rte_o)
        .arg("-lm")
        .arg("-o")
        .arg(&bin)
        .output()
        .expect("spawn cc link");
    assert!(
        link.status.success(),
        "linking clean_runtime.o + runtime_extern.o failed (duplicate symbols?):\n{}",
        String::from_utf8_lossy(&link.stderr)
    );
    assert!(
        Command::new(&bin).status().expect("run").success(),
        "linked probe binary did not run"
    );
}

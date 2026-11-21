// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The trust-cg lane's link (runtime R0 of the design, §2.4): the trust-cg
//! object, the embedded C runtime, `runtime_extern.c` (the link-visible
//! forwarders for the header's `static inline` primitives, which trust-cg
//! calls out of line), the whole prelude shim union as one translation unit,
//! and the entry driver the C lane synthesizes — compiled and linked by the
//! host `cc` (`$CLEAN_CC`, `$CC`, else `cc`).
//!
//! # The entry symbol
//!
//! trust-ir names a function by its link symbol, and an ordinary Lean name IS
//! its symbol: the Lean entry `main` is the object's `main`. The C driver
//! therefore cannot also be `main`. On Mach-O the driver is linked as the
//! program's entry point under another name (`-Wl,-e,_clean_lx0_driver_main`;
//! `LC_MAIN` hands it `argc`/`argv` and `exit`s with its result, as for
//! `main`), and calls the Lean entry through an asm label. Other hosts refuse
//! by name rather than guess at an ELF equivalent.

use std::path::{Path, PathBuf};
use std::process::Command;

use super::checks::ModuleSelfChecks;
use super::{stderr_head, LaneError, LOWERED, RUNTIME};
use crate::native_build::{render_entry_driver, EntryArgs, EntryContract};

/// The driver's C name when the entry's own link symbol is `main`.
pub(crate) const DRIVER_ENTRY: &str = "clean_lx0_driver_main";
/// The C name the driver calls the Lean entry by (an asm label onto its symbol).
const ENTRY_ALIAS: &str = "clean_lx0_entry";

/// A linked program, and how its driver was entered.
pub(crate) struct Linked {
    pub(crate) binary: PathBuf,
    /// `main`, or `clean_lx0_driver_main (-e)` when the driver is the Mach-O
    /// entry point under another name.
    pub(crate) driver_entry: String,
}

/// The assembler-level spelling of a C symbol on this host.
fn asm_symbol(symbol: &str) -> String {
    if cfg!(target_vendor = "apple") {
        format!("_{symbol}")
    } else {
        symbol.to_owned()
    }
}

/// The driver translation unit: an asm-labelled declaration of the entry
/// `entry_symbol`, then the C lane's own driver ([`render_entry_driver`])
/// under `driver_fn`.
pub(crate) fn render_driver(
    contract: EntryContract,
    entry_symbol: &str,
    driver_fn: &str,
) -> String {
    let params = match contract.args {
        EntryArgs::None => "void",
        EntryArgs::Argv => "clean_obj*",
    };
    let mut s = format!(
        "/* Synthesized by clean native_trustcg: the entry driver for a trust-cg object.\n   \
         lowered: {LOWERED}; runtime: {RUNTIME}. */\n\
         #include <stdio.h>\n#include \"clean_runtime.h\"\n\n\
         extern clean_obj* {ENTRY_ALIAS}({params}) __asm__(\"{}\");\n",
        asm_symbol(entry_symbol)
    );
    s.push_str(&render_entry_driver(contract, ENTRY_ALIAS, driver_fn));
    s
}

/// Locate a C compiler: `$CLEAN_CC`, `$CC`, then `cc`/`gcc`/`clang` on PATH
/// (the C lane's order).
fn find_c_compiler() -> Option<String> {
    for var in ["CLEAN_CC", "CC"] {
        if let Ok(value) = std::env::var(var) {
            if !value.trim().is_empty() {
                return Some(value);
            }
        }
    }
    ["cc", "gcc", "clang"]
        .into_iter()
        .find(|cc| {
            Command::new(cc)
                .arg("--version")
                .output()
                .is_ok_and(|o| o.status.success())
        })
        .map(str::to_owned)
}

/// Write the runtime header, runtime, `runtime_extern.c`, the shim union and
/// the driver into `dir`; return the C sources to compile.
pub(super) fn materialize(
    dir: &Path,
    driver: &str,
    checks: &ModuleSelfChecks,
) -> Result<Vec<PathBuf>, LaneError> {
    let flat = |src: &str| src.replacen("../include/clean_runtime.h", "clean_runtime.h", 1);
    let write = |name: &str, text: &str| -> Result<PathBuf, LaneError> {
        let path = dir.join(name);
        std::fs::write(&path, text)
            .map_err(|e| LaneError::Link(format!("could not write {}: {e}", path.display())))?;
        Ok(path)
    };
    write("clean_runtime.h", clean_runtime::runtime_header())?;
    Ok(vec![
        write("driver.c", driver)?,
        write("shims.c", &checks.shim_translation_unit())?,
        write("clean_runtime.c", &flat(clean_runtime::runtime_source()))?,
        write(
            "runtime_extern.c",
            &flat(clean_runtime::runtime_extern_source()),
        )?,
    ])
}

/// Link `object` into a program in `dir`.
pub(crate) fn link_program(
    dir: &Path,
    object: &Path,
    checks: &ModuleSelfChecks,
) -> Result<Linked, LaneError> {
    let entry_is_main = checks.entry_symbol() == "main";
    if entry_is_main && !cfg!(target_vendor = "apple") {
        return Err(LaneError::Link(
            "the entry's link symbol is `main`, the C driver's own name; only the Mach-O \
             entry-point override (`-e`) is wired to link the driver under another name"
                .to_owned(),
        ));
    }
    let driver_fn = if entry_is_main { DRIVER_ENTRY } else { "main" };
    let driver = render_driver(checks.contract(), checks.entry_symbol(), driver_fn);
    let sources = materialize(dir, &driver, checks)?;
    let cc = find_c_compiler().ok_or_else(|| {
        LaneError::Link(
            "no C compiler found; set CLEAN_CC or CC, or install cc, gcc or clang".to_owned(),
        )
    })?;
    let binary = dir.join("program");
    let mut cmd = crate::native_c_toolchain::command(&cc)
        .map_err(|error| LaneError::Link(error.to_string()))?;
    cmd.args(["-O2", "-std=c11", "-I"])
        .arg(dir)
        .args(sources)
        .arg(object)
        .arg("-lm")
        .arg("-o")
        .arg(&binary);
    if entry_is_main {
        cmd.arg(format!("-Wl,-e,{}", asm_symbol(DRIVER_ENTRY)));
    }
    let out = cmd
        .output()
        .map_err(|e| LaneError::Link(format!("could not run the C compiler `{cc}`: {e}")))?;
    if !out.status.success() {
        let stderr = String::from_utf8_lossy(&out.stderr);
        let undefined = linker_undefined(&stderr);
        return Err(LaneError::Link(if undefined.is_empty() {
            stderr_head(&stderr, out.status.code())
        } else {
            format!("undefined symbols: {}", undefined.join(", "))
        }));
    }
    if !binary.is_file() {
        return Err(LaneError::Link(format!(
            "the C compiler reported success but wrote no program at {}",
            binary.display()
        )));
    }
    Ok(Linked {
        binary,
        driver_entry: if entry_is_main {
            format!("{DRIVER_ENTRY} (-e)")
        } else {
            "main".to_owned()
        },
    })
}

/// Symbols a linker reports undefined, in report order, de-duplicated, with
/// the Mach-O leading `_` removed: ld64's `"_sym", referenced from:` and GNU
/// ld's ``undefined reference to `sym'``.
pub(crate) fn linker_undefined(stderr: &str) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    let mut push = |sym: &str| {
        if !out.iter().any(|s| s == sym) {
            out.push(sym.to_owned());
        }
    };
    for line in stderr.lines() {
        if line.contains("referenced from") {
            if let Some(q0) = line.find('"') {
                if let Some(q1) = line[q0 + 1..].find('"') {
                    let inner = &line[q0 + 1..q0 + 1 + q1];
                    push(inner.strip_prefix('_').unwrap_or(inner));
                    continue;
                }
            }
        }
        if let Some(idx) = line.find("undefined reference to") {
            let rest = &line[idx..];
            if let (Some(b0), Some(b1)) = (rest.find('`'), rest.find('\'')) {
                if b0 < b1 {
                    push(&rest[b0 + 1..b1]);
                }
            }
        }
    }
    out
}

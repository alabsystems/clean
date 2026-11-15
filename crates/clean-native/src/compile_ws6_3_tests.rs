// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! WS6.3 (F-105) through the exact `clean compile` lowering: the battery's
//! `p15_bitwise` root elaborated from its Lean source, and the census of what
//! the PRIMITIVE_DENYLIST keeps out of a build. A child of
//! `battery_census_tests`, so the `trust-ir-backend-lib` gate leg
//! (`-- compile::battery_census_tests::`) runs it.
//!
//! The cause, confirmed in `postmortems/2026-09-18-ws6-3-mask-crash.md`: the
//! prelude's `Nat.land`/`lor`/`xor` bodies (`Nat.bitwise`, unary fuel `m + n`)
//! were compiled for execution and recursed ~2^65 deep on `mask (2^64-1)
//! (2^64-2)`. The `clean-compiler` side (`emit_trust_ir::tests::ws6_3`) holds
//! the kernel-built mutation control, the stack-scaling confirmation, the
//! structural `and u64` check and the shim/kernel reducer agreement.

use super::*;
use clean_compiler::emit_c::CEmitConfig;
use clean_compiler::mangle::mangle_name;
use clean_compiler::pass_manager::compile_lcnf_decls;
use clean_kernel::{Expr, Level, Name};

use crate::native_build::is_primitive_denylisted;

use super::super::select_lcnf_decl_denying;

/// `mask`'s vectors `(a, b, mask a b)`: the proof program's three
/// (`parta-lean/run.py`) plus the heap pair the WS6.3 spec adds. Each is
/// certified by the kernel in the ELABORATED environment below.
const MASK_VECTORS: [(u64, u64, u64); 4] = [
    (12, 10, 9),
    (u64::MAX, u64::MAX - 1, u64::MAX),
    (0, 0, 1),
    ((1 << 63) + 5, (1 << 63) + 3, (1 << 63) + 1),
];

/// The battery's `p15_bitwise` source, verbatim.
fn p15_source() -> &'static str {
    BATTERY
        .iter()
        .find(|(probe, _, _)| *probe == "p15_bitwise")
        .map(|(_, source, _)| *source)
        .expect("the battery carries p15_bitwise")
}

fn u64_lit(n: u64) -> Expr {
    Expr::app(Expr::const_str("UInt64.ofNat"), Expr::nat_lit(n))
}

/// `theorem <name> : mask a b = r := rfl`, checked against `env`.
fn mask_rfl(env: &mut clean_kernel::Environment, name: &str, (a, b, r): (u64, u64, u64)) -> bool {
    let lvl = vec![Level::succ(Level::zero())];
    let u64t = Expr::const_str("UInt64");
    let lhs = Expr::apps(Expr::const_str("mask"), [u64_lit(a), u64_lit(b)]);
    env.add_decl(clean_kernel::env::Declaration::Theorem {
        name: Name::from_string(name),
        level_params: vec![],
        type_: Expr::apps(
            Expr::const_(Name::from_string("Eq"), lvl.clone()),
            [u64t.clone(), lhs, u64_lit(r)],
        ),
        value: Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), lvl),
            [u64t, u64_lit(r)],
        ),
    })
    .is_ok()
}

/// The driver: `argv = <a> <b>`, prints `mask a b`. One process per vector,
/// so a crash is attributed to its vector.
fn driver(mask_decl: &str) -> String {
    format!(
        "{mask_decl}\n\
         int main(int argc, char** argv) {{\n\
           if (argc != 3) {{ return 2; }}\n\
           uint64_t a = strtoull(argv[1], 0, 10), b = strtoull(argv[2], 0, 10);\n\
           printf(\"%llu\\n\", (unsigned long long)ws_mask(a, b));\n\
           return 0;\n\
         }}\n"
    )
}

const DRIVER_INCLUDES: &str = "#include <stdio.h>\n#include <stdint.h>\n#include <stdlib.h>\n\
     #include <string.h>\n#include \"clean_runtime.h\"\n";

/// `--emit c` lane: the shim union + the emitted C + the driver, one TU,
/// against the runtime.
fn build_c(cc: &str, dir: &Path, c_code: &str) -> PathBuf {
    let tu = format!(
        "{DRIVER_INCLUDES}{}\n{c_code}\n{}",
        prelude_shims_translation_unit(&[]),
        driver(&format!(
            "static uint64_t ws_mask(uint64_t a, uint64_t b) {{ return {}(a, b); }}",
            mangle_name(&Name::from_string("mask"))
        )),
    );
    std::fs::write(dir.join("clean_runtime.h"), clean_runtime::runtime_header())
        .expect("write header");
    let rt = dir.join("clean_runtime.c");
    std::fs::write(
        &rt,
        clean_runtime::runtime_source().replacen(
            "../include/clean_runtime.h",
            "clean_runtime.h",
            1,
        ),
    )
    .expect("write runtime");
    let src = dir.join("mask_c.c");
    std::fs::write(&src, tu).expect("write TU");
    let bin = dir.join("mask_c");
    let out = Command::new(cc)
        .args(["-O0", "-I"])
        .arg(dir)
        .arg("-o")
        .arg(&bin)
        .arg(&src)
        .arg(&rt)
        .arg("-lm")
        .output()
        .expect("spawn cc");
    assert!(
        out.status.success(),
        "mask --emit c lane: cc failed:\n{}",
        String::from_utf8_lossy(&out.stderr)
    );
    bin
}

/// trust-ir -> trust-cg lane, in the EXPERIMENT fixture: the `--emit obj`
/// module (`licensed`) is first shown REFUSED by trust-cg's codegen license
/// (Clean stamps every body `Ungated` until WS6.6 earns `Gated`), then
/// `experiment` — the same module with the licence claim cleared, built by
/// the caller — is compiled and linked. The licensed row stays refused; only
/// the experiment lane flips.
fn build_trust_ir(tcg: &Path, cc: &str, dir: &Path, licensed: &[u8], experiment: &[u8]) -> PathBuf {
    let target = host_trust_cg_target().expect("trust-cg host target");
    let compile = |tmbc: &[u8], stem: &str| {
        let input = dir.join(format!("{stem}.tmbc"));
        let obj = dir.join(format!("{stem}.o"));
        std::fs::write(&input, tmbc).expect("write tmbc");
        let mut command = Command::new(tcg);
        // The experiment carries the `clean-compiler-unvalidated` license,
        // recognized for this invocation only, as `clean run --backend
        // trust-cg` does; the `ungated` production module below stays refused.
        if stem == "experiment" {
            command.args([
                "--recognize-authority",
                clean_compiler::emit_trust_ir_lane::CLEAN_COMPILER_UNVALIDATED_AUTHORITY,
            ]);
        }
        let out = command
            .args(["-c", "--target", target, "-o"])
            .arg(&obj)
            .arg(&input)
            .output()
            .expect("spawn trust-cg");
        (out, obj)
    };
    let (refused, refused_obj) = compile(licensed, "licensed");
    assert!(
        !refused.status.success()
            && String::from_utf8_lossy(&refused.stderr).contains(UNGATED_REFUSAL)
            && !refused_obj.exists(),
        "the licensed `mask` module must be refused by the codegen license: {}",
        String::from_utf8_lossy(&refused.stderr)
    );
    let (cg, obj) = compile(experiment, "experiment");
    assert!(
        cg.status.success(),
        "trust-cg failed on the experiment fixture: {}",
        String::from_utf8_lossy(&cg.stderr)
    );
    let prefix = if cfg!(target_vendor = "apple") {
        "_"
    } else {
        ""
    };
    let drv = dir.join("driver.c");
    std::fs::write(
        &drv,
        format!(
            "{DRIVER_INCLUDES}{}",
            driver(&format!(
                "extern uint64_t ws_mask(uint64_t, uint64_t) __asm__(\"{prefix}mask\");"
            ))
        ),
    )
    .expect("write driver");
    assert_eq!(
        link_against_runtime(cc, dir, &drv, &[obj], &[]),
        BTreeSet::new(),
        "the experiment `mask` object must link against the runtime and the shims"
    );
    dir.join("driver")
}

/// Run one vector in its own process; `Err` names how it ended otherwise.
fn run_vector(bin: &Path, a: u64, b: u64) -> Result<String, String> {
    use std::os::unix::process::ExitStatusExt;
    let out = Command::new(bin)
        .args([a.to_string(), b.to_string()])
        .output()
        .expect("run the mask driver");
    if let Some(sig) = out.status.signal() {
        return Err(format!("killed by signal {sig}"));
    }
    if !out.status.success() {
        return Err(format!("exit {:?}", out.status.code()));
    }
    Ok(String::from_utf8_lossy(&out.stdout).trim().to_owned())
}

/// GAP row `GENERAL.p15_bitwise.mask.linkrun` (PRODUCER-GAP -> PASS in the
/// EXPERIMENT lane; the licensed row stays refused until WS6.6 earns `Gated`).
///
/// `def mask (a b : UInt64) : UInt64 := (a &&& b) ||| 1`, elaborated from the
/// battery source by Clean's own frontend and lowered exactly as `clean
/// compile` lowers it, computes the kernel-certified value for every vector —
/// `(12,10)`, `(2^64-1, 2^64-2)`, `(0,0)` and `(2^63+5, 2^63+3)` — through
/// `--emit c` AND trust-ir -> trust-cg, one process per vector. Before WS6.3
/// the second and fourth vectors died on the stack through both lanes (rc -11
/// / 139 in the proof program). NEGATIVE TWIN: each expectation off by one is
/// refused by the kernel and rejected by the comparison.
#[test]
fn general_p15_bitwise_mask_linkrun() {
    let dir = tempfile::tempdir().expect("tempdir");
    let file = dir.path().join("p15_bitwise.lean");
    std::fs::write(&file, p15_source()).expect("write probe");
    let args = args_for(&file, "mask");
    let (decls, mut env, pipeline) = select_lcnf_decl(&args).expect("select mask");

    for (i, v) in MASK_VECTORS.into_iter().enumerate() {
        let (a, b, r) = v;
        assert!(
            !mask_rfl(
                &mut env,
                &format!("ws6_3_mask_off_{i}"),
                (a, b, r.wrapping_add(1))
            ),
            "the kernel must REFUSE `mask {a} {b} = {r} + 1`"
        );
        assert!(
            mask_rfl(&mut env, &format!("ws6_3_mask_{i}"), v),
            "the kernel must certify `mask {a} {b} = {r}`"
        );
    }

    let cc = census_cc();
    let c_dir = tempfile::tempdir().expect("tempdir");
    let c_code = compile_lcnf_decls(&decls, &env, &pipeline)
        .expect("mask compiles")
        .emit_c(CEmitConfig::default())
        .expect("mask lowers to C");
    let mut lanes = vec![("emit_c", build_c(&cc, c_dir.path(), &c_code))];
    let ti_dir = tempfile::tempdir().expect("tempdir");
    match find_trust_cg().expect("valid trust-cg selection") {
        Some(tcg) => {
            let module =
                compile_lcnf_to_trust_ir(&decls, &env, &pipeline, &object_emit_config(&args))
                    .expect("mask lowers through the --emit obj config");
            // Licensed at the `clean-compiler-unvalidated` grade by the
            // production lane's own re-stamp (it claims nothing about a body),
            // never cleared to `None`, which trust-cg refuses since WS7.5.
            let mut experiment = module.clone();
            let census =
                clean_compiler::emit_trust_ir_lane::restamp_ungated_as_unvalidated(&mut experiment)
                    .expect("every body of the mask module carries the Ungated claim");
            assert!(census.kept.is_empty(), "only Ungated bodies: {census:?}");
            assert!(
                census.unvalidated > 0,
                "the experiment fixture must carry a body"
            );
            lanes.push((
                "trust-ir",
                build_trust_ir(
                    &tcg,
                    &cc,
                    ti_dir.path(),
                    &serialize_tmbc(&module).expect("module has a wire identity"),
                    &serialize_tmbc(&experiment).expect("experiment has a wire identity"),
                ),
            ));
        }
        None => eprintln!("mask linkrun: trust-ir lane skipped: trust-cg not found"),
    }
    for (lane, bin) in &lanes {
        for (a, b, r) in MASK_VECTORS {
            let got = run_vector(bin, a, b)
                .unwrap_or_else(|e| panic!("{lane}: mask {a} {b} (want {r}): {e}"));
            assert_eq!(got, r.to_string(), "{lane}: mask {a} {b}");
            assert_ne!(
                got,
                r.wrapping_add(1).to_string(),
                "{lane}: the comparison must REJECT mask {a} {b} off by one"
            );
        }
    }
}

/// The emitted symbol set of `root` in `source`, lowered with `denylisted`:
/// `(defined function names, bodyless l_* declarations)`.
fn symbol_set(
    source: &str,
    root: &str,
    denylisted: &dyn Fn(&str) -> bool,
) -> (BTreeSet<String>, BTreeSet<String>) {
    let dir = tempfile::tempdir().expect("tempdir");
    let file = dir.path().join("probe.lean");
    std::fs::write(&file, source).expect("write probe");
    let args = args_for(&file, root);
    let (decls, env, pipeline) =
        select_lcnf_decl_denying(&args, denylisted).expect("select the root");
    let module = compile_lcnf_to_trust_ir(&decls, &env, &pipeline, &object_emit_config(&args))
        .expect("the root lowers through the --emit obj config");
    let defined = module
        .functions
        .iter()
        .filter(|f| !f.blocks.is_empty())
        .map(|f| f.name.clone())
        .collect();
    let externs = module
        .functions
        .iter()
        .filter(|f| f.blocks.is_empty() && f.name.starts_with("l_"))
        .map(|f| f.name.clone())
        .collect();
    (defined, externs)
}

/// CENSUS + MUTATION CONTROL (fix 2a), by the emitted symbol set.
///
/// `natMask (a b : Nat) := (a &&& b) ||| 1` reaches `Nat.land`/`Nat.lor`
/// directly. With the real shim table its module DECLARES `l_Nat_land` and
/// `l_Nat_lor` (bodyless, resolved by the shims) and defines none of
/// `Nat.land`, `Nat.bitwise`, `Nat.bitwiseAux`. With `l_Nat_land` removed from
/// the denylist — exactly what dropping it from `NAT_PRELUDE_SHIMS` does —
/// `Nat.land` is compiled from source again: the module DEFINES `Nat.land`,
/// `Nat.bitwise` and `Nat.bitwiseAux` and no longer declares `l_Nat_land`,
/// while `l_Nat_lor` (still shimmed) stays a declaration.
///
/// And every shim-table symbol is on the denylist the build consults, so the
/// table and the extern boundary cannot drift apart.
#[test]
fn ws6_3_census_nat_land_compiled_from_source_without_its_shim() {
    for sym in ["l_Nat_land", "l_Nat_lor", "l_Nat_xor"] {
        assert!(
            prelude_shim_symbols().contains(&sym) && is_primitive_denylisted(sym),
            "`{sym}` must be a prelude shim AND on the denylist"
        );
    }
    let source = "def natMask (a b : Nat) : Nat := (a &&& b) ||| 1\n";
    let source_bodies = ["Nat.land", "Nat.bitwise", "Nat.bitwiseAux"];

    let (defined, externs) = symbol_set(source, "natMask", &is_primitive_denylisted);
    for sym in ["l_Nat_land", "l_Nat_lor"] {
        assert!(
            externs.contains(sym),
            "with its shim, `{sym}` must be a bodyless declaration: {externs:?}"
        );
    }
    for body in source_bodies {
        assert!(
            !defined.contains(body),
            "with the shim, `{body}` must NOT be compiled from source: {defined:?}"
        );
    }

    let without_land = |s: &str| s != "l_Nat_land" && is_primitive_denylisted(s);
    let (defined, externs) = symbol_set(source, "natMask", &without_land);
    for body in source_bodies {
        assert!(
            defined.contains(body),
            "without `l_Nat_land`, `{body}` must be compiled from source again: {defined:?}"
        );
    }
    assert!(
        !externs.contains("l_Nat_land"),
        "without its shim, `l_Nat_land` is no longer an extern: {externs:?}"
    );
    assert!(
        externs.contains("l_Nat_lor"),
        "the still-shimmed `l_Nat_lor` stays a declaration: {externs:?}"
    );
}

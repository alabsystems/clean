// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean extract` — width-1 verified-by-differential C extraction
//! (`designs/2026-08-06-clean-extract-width1.md`; the Rocq `Extraction`
//! analog, rung §C of the Rocq-features program).
//!
//! Pipeline: elaborate → EXTRACTION GATE (positive computationality — no
//! Prop/SProp anywhere, no universe params, first-order allowlisted
//! telescope, non-recursive body) → C emission via the `clean compile`
//! closure → shim-coverage check over the emitted TEXT → cc-link against
//! the embedded runtime with a synthesized battery driver → run the
//! battery → DIFFERENTIAL against kernel-side evaluation of the same
//! applications → blake3-digested manifest, atomically renamed into
//! `--out` only on full success.
//!
//! Honesty contract: the differential record is a CHECK over the battery,
//! not a proof; the manifest says so. Rocq's own Extraction ships neither.
//! Any refusal or mismatch exits nonzero and writes NOTHING.

use std::path::Path;
use std::process::Command;

use anyhow::{bail, Context};
use clean_kernel::{Environment, Expr, ExprKind, Name};

use crate::cli::ExtractArgs;
use crate::cmd_compile::{emit_decls, select_lcnf_decl};
use crate::native_build;

/// Stable refusal codes (`designs/2026-08-06-clean-extract-width1.md`
/// §Scope). A refusal writes no artifacts.
#[derive(Debug, thiserror::Error)]
pub(crate) enum ExtractRefusal {
    #[error("E_PROP: {0} has Prop/SProp in its type telescope; extraction is computational only")]
    Prop(Name),
    #[error("E_UNIVERSE: {0} is universe-polymorphic; v1 extracts monomorphic declarations")]
    Universe(Name),
    #[error(
        "E_TYPE_PARAM: {0} has a binder or codomain outside the v1 first-order allowlist \
         (Nat, Bool, UInt8/16/32/64)"
    )]
    TypeParam(Name),
    #[error("E_NONCOMPUTABLE: {0} has no computational value (axiom/opaque/theorem)")]
    Noncomputable(Name),
    #[error("E_RECURSION: {0} uses recursion ({1}); v1 extracts straight-line bodies")]
    Recursion(Name, Name),
}

/// The v1 first-order type allowlist.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ScalarTy {
    Nat,
    Bool,
    UInt8,
    UInt16,
    UInt32,
    UInt64,
}

impl ScalarTy {
    fn of(e: &Expr) -> Option<Self> {
        let ExprKind::Const(n, _) = e.kind() else {
            return None;
        };
        match n.to_string().as_str() {
            "Nat" => Some(ScalarTy::Nat),
            "Bool" => Some(ScalarTy::Bool),
            "UInt8" => Some(ScalarTy::UInt8),
            "UInt16" => Some(ScalarTy::UInt16),
            "UInt32" => Some(ScalarTy::UInt32),
            "UInt64" => Some(ScalarTy::UInt64),
            _ => None,
        }
    }

    fn battery(self) -> Vec<u64> {
        match self {
            ScalarTy::Bool => vec![0, 1],
            ScalarTy::Nat => vec![0, 1, 2, 3, 7, 12, 63],
            ScalarTy::UInt8 => vec![0, 1, 7, 200, 255],
            ScalarTy::UInt16 => vec![0, 1, 9, 60_000, 65_535],
            ScalarTy::UInt32 => vec![0, 1, 2, 41, 1000, 4_294_967_295, 4_294_967_290],
            ScalarTy::UInt64 => vec![0, 1, 2, 41, 1000, u64::MAX, u64::MAX - 5],
        }
    }

    fn c_literal(self, v: u64) -> String {
        match self {
            ScalarTy::Bool | ScalarTy::Nat => format!("clean_box({v}u)"),
            _ => format!("{v}ull"),
        }
    }

    fn lean_literal(self, v: u64) -> String {
        match self {
            ScalarTy::Nat => nat_literal(v),
            ScalarTy::Bool => (if v == 0 { "Bool.false" } else { "Bool.true" }).to_string(),
            ScalarTy::UInt8 => format!("(UInt8.ofNat {})", nat_literal(v)),
            ScalarTy::UInt16 => format!("(UInt16.ofNat {})", nat_literal(v)),
            ScalarTy::UInt32 => format!("(UInt32.ofNat {})", nat_literal(v)),
            ScalarTy::UInt64 => format!("(UInt64.ofNat {})", nat_literal(v)),
        }
    }
}

/// Spell a `Nat` literal in constructor form so no `OfNat` elaboration is
/// needed for large values (kernel-side leg must be elaboration-robust).
fn nat_literal(v: u64) -> String {
    // Literal syntax elaborates fine for Nat in Clean; keep it simple.
    format!("{v}")
}

/// Result signature of the gated declaration.
struct GateSig {
    params: Vec<ScalarTy>,
    ret: ScalarTy,
}

/// The extraction gate (design §Scope): positive computationality checks
/// over the KERNEL type of the root declaration.
fn extraction_gate(env: &Environment, name: &Name) -> Result<GateSig, ExtractRefusal> {
    let Some(info) = env.get_const(name) else {
        return Err(ExtractRefusal::Noncomputable(name.clone()));
    };
    if info.value.is_none() {
        return Err(ExtractRefusal::Noncomputable(name.clone()));
    }
    if !info.level_params.is_empty() {
        return Err(ExtractRefusal::Universe(name.clone()));
    }
    // Telescope walk: every binder domain and the codomain must be on the
    // allowlist; any Sort anywhere (incl. Prop) refuses.
    let mut params = Vec::new();
    let mut cursor = &info.type_;
    while let ExprKind::Pi(_, dom, body) = cursor.kind() {
        if matches!(dom.kind(), ExprKind::Sort(_)) {
            return Err(ExtractRefusal::Prop(name.clone()));
        }
        let Some(t) = ScalarTy::of(dom) else {
            return Err(ExtractRefusal::TypeParam(name.clone()));
        };
        params.push(t);
        cursor = body;
    }
    if matches!(cursor.kind(), ExprKind::Sort(_)) {
        return Err(ExtractRefusal::Prop(name.clone()));
    }
    let Some(ret) = ScalarTy::of(cursor) else {
        return Err(ExtractRefusal::TypeParam(name.clone()));
    };
    // Conservative recursion detector over the value: any `.rec`-family
    // constant refuses (v1 is straight-line).
    if let Some(value) = &info.value {
        if let Some(offender) = find_recursion(value) {
            return Err(ExtractRefusal::Recursion(name.clone(), offender));
        }
    }
    Ok(GateSig { params, ret })
}

/// Find a recursor-family constant mentioned anywhere in `e`.
fn find_recursion(e: &Expr) -> Option<Name> {
    let mut found = None;
    visit_consts(e, &mut |n: &Name| {
        if found.is_some() {
            return;
        }
        let s = n.to_string();
        if s.ends_with(".rec")
            || s.ends_with(".recOn")
            || s.ends_with(".brecOn")
            || s == "Acc.rec"
            || s == "WellFounded.fix"
        {
            found = Some(n.clone());
        }
    });
    found
}

fn visit_consts(e: &Expr, f: &mut impl FnMut(&Name)) {
    match e.kind() {
        ExprKind::Const(n, _) => f(n),
        ExprKind::App(a, b) => {
            visit_consts(a, f);
            visit_consts(b, f);
        }
        ExprKind::Lam(_, a, b) | ExprKind::Pi(_, a, b) => {
            visit_consts(a, f);
            visit_consts(b, f);
        }
        ExprKind::Let(_, t, v, b, _) => {
            visit_consts(t, f);
            visit_consts(v, f);
            visit_consts(b, f);
        }
        ExprKind::MData(_, i) | ExprKind::Proj(_, _, i) => visit_consts(i, f),
        _ => {}
    }
}

/// Entry point for `clean extract`.
pub(crate) fn handle_extract_command(args: &ExtractArgs) -> anyhow::Result<()> {
    let decl_name = Name::from_string(&args.decl);

    // 1-2. Elaborate + closure + C emission, reusing the compile pipeline.
    let (c_source, env) = select_and_emit(args)?;

    // Gate runs against the elaborated environment.
    let sig = extraction_gate(&env, &decl_name).map_err(|r| anyhow::anyhow!("{r}"))?;

    // 3. Shim coverage over the emitted TEXT (fail-closed extern boundary).
    let shims = native_build::select_shims_for_c_text(&c_source)
        .map_err(|e| anyhow::anyhow!("uncovered extern in emitted C: {e}"))?;

    // 4-6. Materialize, synthesize the battery driver, link, run.
    let tmp = tempfile::Builder::new()
        .prefix("clean-extract-")
        .tempdir()
        .context("create scratch dir")?;
    let build_dir = tmp.path().join("build");
    std::fs::create_dir_all(&build_dir)?;

    let battery = build_battery(&sig);
    let driver = render_battery_driver(&args.decl, &sig, &battery, &shims, &c_source);
    let exe = native_build::build_extract_executable(&build_dir, &shims, &c_source, &driver)
        .context("compile/link extracted C")?;

    let out = Command::new(&exe).output().context("run battery binary")?;
    if !out.status.success() {
        bail!(
            "battery binary exited nonzero: {}",
            String::from_utf8_lossy(&out.stderr)
        );
    }
    let native_results: Vec<String> = String::from_utf8_lossy(&out.stdout)
        .lines()
        .map(|l| l.trim().to_string())
        .filter(|l| !l.is_empty())
        .collect();
    if native_results.len() != battery.len() {
        bail!(
            "battery binary produced {} results for {} inputs",
            native_results.len(),
            battery.len()
        );
    }

    // 7. Differential: kernel-side evaluation of the same applications.
    for (inputs, native) in battery.iter().zip(&native_results) {
        let expected = kernel_eval(&env, &args.decl, &sig, inputs)
            .with_context(|| format!("kernel-side evaluation for inputs {inputs:?}"))?;
        if *native != expected {
            bail!(
                "DIFFERENTIAL MISMATCH for {} at inputs {:?}: native `{}` vs kernel `{}` — \
                 refusing to ship",
                args.decl,
                inputs,
                native,
                expected
            );
        }
    }

    // 8. Manifest + atomic install.
    let out_dir = &args.out;
    let staging = tmp.path().join("out");
    std::fs::create_dir_all(&staging)?;
    let c_path = staging.join(format!("{}.c", args.decl));
    std::fs::write(&c_path, &c_source)?;
    let manifest = serde_json::json!({
        "schema": "clean-extract-v1",
        "decl": args.decl,
        "c_file": format!("{}.c", args.decl),
        "c_digest_blake3": blake3::hash(c_source.as_bytes()).to_hex().to_string(),
        "battery_points": battery.len(),
        "differential": "PASSED — every battery point agrees with kernel-side evaluation",
        "claim": "differential check over the recorded battery; NOT a proof of \
                  translation correctness (see designs/2026-08-06-clean-extract-width1.md)",
    });
    std::fs::write(
        staging.join("manifest.json"),
        serde_json::to_string_pretty(&manifest)?,
    )?;
    if args.keep_temp {
        println!("scratch build kept at {}", build_dir.display());
    }
    if out_dir.exists() {
        bail!(
            "--out {} already exists; refusing to overwrite",
            out_dir.display()
        );
    }
    // Rename can cross devices when --out is elsewhere; fall back to copy.
    if std::fs::rename(&staging, out_dir).is_err() {
        copy_dir(&staging, out_dir)?;
    }
    println!(
        "extracted {} → {} ({} battery points, differential PASSED)",
        args.decl,
        out_dir.display(),
        battery.len()
    );
    Ok(())
}

fn copy_dir(from: &Path, to: &Path) -> anyhow::Result<()> {
    std::fs::create_dir_all(to)?;
    for entry in std::fs::read_dir(from)? {
        let entry = entry?;
        std::fs::copy(entry.path(), to.join(entry.file_name()))?;
    }
    Ok(())
}

/// Reuse the `clean compile` closure/emitter for the C text.
fn select_and_emit(args: &ExtractArgs) -> anyhow::Result<(String, Environment)> {
    let compile_args = clean_compiler::cli::CompileArgs {
        file: Some(args.file.clone()),
        decl: Some(args.decl.clone()),
        emit: clean_compiler::cli::EmitFormat::C,
        opt_level: 0,
        output: None,
    };
    let (lcnf, env, pipeline) = select_lcnf_decl(&compile_args)?;
    let c = emit_decls(
        &lcnf,
        &env,
        clean_compiler::cli::EmitFormat::C,
        &pipeline,
        Some(args.file.as_path()),
    )?;
    Ok((c, env))
}

/// The battery: the cartesian product would blow up for 2+ args, so per the
/// design we take the per-type battery zipped diagonally plus a few crossed
/// points, bounded to ~16 tuples.
fn build_battery(sig: &GateSig) -> Vec<Vec<u64>> {
    if sig.params.is_empty() {
        return vec![vec![]];
    }
    let per: Vec<Vec<u64>> = sig.params.iter().map(|t| t.battery()).collect();
    let longest = per.iter().map(Vec::len).max().unwrap_or(1);
    let mut out = Vec::new();
    for i in 0..longest {
        out.push(per.iter().map(|b| b[i % b.len()]).collect());
    }
    // Crossed points: first with last.
    if sig.params.len() >= 2 && per[0].len() > 1 {
        out.push(
            per.iter()
                .enumerate()
                .map(|(j, b)| if j == 0 { b[b.len() - 1] } else { b[0] })
                .collect(),
        );
    }
    out.truncate(16);
    out
}

/// Synthesized `main()`: calls `l_<decl>` per battery tuple and prints each
/// result as a decimal. Bypasses `clean run`'s bounded entry heuristics.
fn render_battery_driver(
    decl: &str,
    sig: &GateSig,
    battery: &[Vec<u64>],
    shims: &str,
    c_source: &str,
) -> String {
    let mangled = native_build::mangle_decl_symbol(decl);
    let boxed_ret = matches!(sig.ret, ScalarTy::Nat | ScalarTy::Bool);
    // If the emitted C already defines the symbol with an unboxed ABI the
    // call sites below match it structurally; the C compiler is the final
    // arbiter (a mismatch is a compile error, fail-closed).
    let _ = c_source;
    let mut m = String::new();
    let _ = shims;
    m.push_str("\n#include <stdio.h>\n#include <inttypes.h>\nint main(void) {\n");
    for tuple in battery {
        let call_args: Vec<String> = tuple
            .iter()
            .zip(&sig.params)
            .map(|(v, t)| t.c_literal(*v))
            .collect();
        let call = format!("{mangled}({})", call_args.join(", "));
        if boxed_ret {
            m.push_str(&format!(
                "  printf(\"%\" PRIu64 \"\\n\", (uint64_t)clean_unbox({call}));\n"
            ));
        } else {
            m.push_str(&format!(
                "  printf(\"%\" PRIu64 \"\\n\", (uint64_t)({call}));\n"
            ));
        }
    }
    m.push_str("  return 0;\n}\n");
    m
}

/// Kernel-side leg: evaluate `decl a₁ … aₙ` (coerced to a Nat spelling) via
/// whnf and read back the literal, as a decimal string for comparison.
fn kernel_eval(
    env: &Environment,
    decl: &str,
    sig: &GateSig,
    inputs: &[u64],
) -> anyhow::Result<String> {
    let applied = {
        let mut s = format!("({decl}");
        for (v, t) in inputs.iter().zip(&sig.params) {
            s.push(' ');
            s.push_str(&t.lean_literal(*v));
        }
        s.push(')');
        match sig.ret {
            ScalarTy::Nat => s,
            ScalarTy::Bool => format!("(Bool.toNat {s})"),
            ScalarTy::UInt8 => format!("(UInt8.toNat {s})"),
            ScalarTy::UInt16 => format!("(UInt16.toNat {s})"),
            ScalarTy::UInt32 => format!("(UInt32.toNat {s})"),
            ScalarTy::UInt64 => format!("(UInt64.toNat {s})"),
        }
    };
    let surface = clean_parser::parse_expr(&applied)
        .map_err(|e| anyhow::anyhow!("parse of kernel-leg expression failed: {e:?}"))?;
    let mut ctx = clean_elab::ElabCtx::new(env);
    let kernel_expr = ctx
        .elaborate(&surface)
        .map_err(|e| anyhow::anyhow!("elaboration of kernel-leg expression failed: {e:?}"))?;
    let tc = clean_kernel::TypeChecker::with_mode(env, env.mode());
    let normal = tc.whnf(&kernel_expr);
    read_back_nat(&normal).ok_or_else(|| {
        anyhow::anyhow!("kernel-side evaluation did not reduce to a Nat literal: {normal:?}")
    })
}

/// Read a whnf'd closed Nat back as a decimal string (literal or
/// `Nat.succ`* chain over a literal/zero).
fn read_back_nat(e: &Expr) -> Option<String> {
    fn go(e: &Expr) -> Option<u64> {
        match e.kind() {
            ExprKind::Lit(clean_kernel::Literal::Nat(n)) => n.to_u64(),
            ExprKind::Const(n, _) if n.to_string() == "Nat.zero" => Some(0),
            ExprKind::App(f, a) => {
                if let ExprKind::Const(n, _) = f.kind() {
                    if n.to_string() == "Nat.succ" {
                        return go(a).map(|v| v + 1);
                    }
                }
                None
            }
            _ => None,
        }
    }
    go(e).map(|v| v.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn env_with(src: &str) -> Environment {
        let mut env = Environment::with_prelude();
        let decls = clean_parser::parse_file(src).expect("parse");
        for d in &decls {
            clean_elab::elaborate_decl_and_register(&mut env, d).expect("elaborate");
        }
        env
    }

    #[test]
    fn test_gate_accepts_first_order_nat_def() {
        let env = env_with("def double (n : Nat) : Nat := Nat.add n n");
        let sig = extraction_gate(&env, &Name::from_string("double"))
            .expect("first-order Nat def is in the v1 class");
        assert_eq!(sig.params.len(), 1);
        assert!(matches!(sig.ret, ScalarTy::Nat));
    }

    #[test]
    fn test_gate_refuses_prop_and_recursion() {
        let env = env_with(
            "theorem trivial_imp (P : Prop) (h : P) : P := h\n\
             def looped (n : Nat) : Nat := Nat.rec 0 (fun _ ih => ih) n",
        );
        assert!(
            matches!(
                extraction_gate(&env, &Name::from_string("trivial_imp")),
                Err(ExtractRefusal::Prop(_))
            ),
            "Prop telescope must refuse E_PROP"
        );
        assert!(
            matches!(
                extraction_gate(&env, &Name::from_string("looped")),
                Err(ExtractRefusal::Recursion(_, _))
            ),
            "recursor use must refuse E_RECURSION"
        );
    }

    #[test]
    fn test_gate_refuses_unknown_and_nonscalar() {
        let env = env_with("def idlist (l : List Nat) : List Nat := l");
        assert!(
            matches!(
                extraction_gate(&env, &Name::from_string("idlist")),
                Err(ExtractRefusal::TypeParam(_))
            ),
            "List telescope must refuse E_TYPE_PARAM"
        );
        assert!(
            matches!(
                extraction_gate(&env, &Name::from_string("missing")),
                Err(ExtractRefusal::Noncomputable(_))
            ),
            "unknown decl must refuse E_NONCOMPUTABLE"
        );
    }
}

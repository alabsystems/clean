// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean extract` — width-1 verified-by-differential extraction
//! (`designs/2026-08-06-clean-extract-width1.md`; the Rocq `Extraction`
//! analog, rung §C of the Rocq-features program).
//!
//! Pipeline: elaborate → EXTRACTION GATE (positive computationality — no
//! Prop/SProp anywhere, no universe params, first-order allowlisted
//! telescope, non-recursive body) → EMIT → build with a synthesized battery
//! driver → run the battery → DIFFERENTIAL against kernel-side evaluation of
//! the same applications → blake3-digested manifest, atomically renamed into
//! `--out` only on full success.
//!
//! Two backends share every step but the emit-and-build one:
//!
//! * `--backend c` (default): C emission via the `clean compile` closure, a
//!   shim-coverage check over the emitted TEXT, and a `cc` link against the
//!   embedded `clean-runtime`.
//! * `--backend rust`: readable, `unsafe`-free Rust emitted straight from the
//!   kernel value with plain scalar signatures, compiled by `rustc`. See
//!   [`crate::extract_rust`].
//!
//! Honesty contract: the differential record is a CHECK over the battery,
//! not a proof; the manifest says so. Rocq's own Extraction ships neither.
//! Any refusal or mismatch exits nonzero and writes NOTHING.

use std::path::Path;
use std::process::Command;

use anyhow::{bail, Context};
use clean_kernel::{Environment, Expr, ExprKind, Name};

use crate::cli::{ExtractArgs, ExtractBackend};
use crate::cmd_compile::{emit_decls, select_lcnf_decl};
use crate::extract_rust;
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
pub(crate) enum ScalarTy {
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
pub(crate) struct GateSig {
    pub(crate) params: Vec<ScalarTy>,
    pub(crate) ret: ScalarTy,
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
///
/// Both backends share the extraction GATE, the BATTERY and the DIFFERENTIAL;
/// they differ only in what gets emitted and how it is built.
pub(crate) fn handle_extract_command(args: &ExtractArgs) -> anyhow::Result<()> {
    match args.backend {
        ExtractBackend::C => handle_extract_c(args),
        ExtractBackend::Rust => handle_extract_rust(args),
        ExtractBackend::Wasm => handle_extract_wasm(args),
    }
}

/// The C backend: emit through the `clean compile --emit c` closure and link
/// against the embedded `clean-runtime`.
fn handle_extract_c(args: &ExtractArgs) -> anyhow::Result<()> {
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
    differential_check(&env, &args.decl, &sig, &battery, &native_results)?;

    // 8. Manifest + atomic install.
    let staging = tmp.path().join("out");
    std::fs::create_dir_all(&staging)?;
    let c_path = staging.join(format!("{}.c", args.decl));
    std::fs::write(&c_path, &c_source)?;
    let manifest = serde_json::json!({
        "schema": "clean-extract-v1",
        "decl": args.decl,
        "backend": "c",
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
    install_staged(args, &staging, battery.len())
}

/// The Rust backend: emit a readable, `unsafe`-free module straight from the
/// KERNEL value, compile it with `rustc`, and hold it to the same differential.
///
/// It deliberately does NOT go through the C emitter. That pipeline's output is
/// boxed `clean_obj*` against the Perceus runtime — correct for a runtime, and
/// not what "extract to a host language" means to a reader. See
/// [`crate::extract_rust`].
fn handle_extract_rust(args: &ExtractArgs) -> anyhow::Result<()> {
    let decl_name = Name::from_string(&args.decl);

    // 1. Elaborate through the SAME front half the C lane uses.
    let env = elaborate_for_extraction(args)?;

    // 2. The shared extraction gate.
    let sig = extraction_gate(&env, &decl_name).map_err(|r| anyhow::anyhow!("{r}"))?;

    // 3. Emit. Any construct outside the v1 table refuses with an `E_RUST_*`.
    let module = extract_rust::emit_rust_module(&env, &decl_name, &sig)
        .map_err(|e| anyhow::anyhow!("{e}"))?;
    let fn_name = extract_rust::rust_fn_name(&args.decl).map_err(|e| anyhow::anyhow!("{e}"))?;

    // 4-6. Synthesize the battery driver, compile with `rustc`, run.
    let tmp = tempfile::Builder::new()
        .prefix("clean-extract-rust-")
        .tempdir()
        .context("create scratch dir")?;
    let build_dir = tmp.path().join("build");
    std::fs::create_dir_all(&build_dir)?;

    let battery = build_battery(&sig);
    let driver = extract_rust::render_rust_battery_driver(&fn_name, &sig, &battery);
    let native_results = extract_rust::run_rust_battery(&module, &driver, &build_dir)
        .map_err(|e| anyhow::anyhow!("{e}"))?;
    if native_results.len() != battery.len() {
        bail!(
            "battery binary produced {} results for {} inputs",
            native_results.len(),
            battery.len()
        );
    }

    // 7. The SAME differential as the C lane.
    differential_check(&env, &args.decl, &sig, &battery, &native_results)?;

    // 8. Manifest + atomic install.
    let staging = tmp.path().join("out");
    std::fs::create_dir_all(&staging)?;
    std::fs::write(staging.join(format!("{fn_name}.rs")), &module)?;
    let manifest = serde_json::json!({
        "schema": "clean-extract-v1",
        "decl": args.decl,
        "backend": "rust",
        "rust_file": format!("{fn_name}.rs"),
        "rust_fn": fn_name,
        "rust_digest_blake3": blake3::hash(module.as_bytes()).to_hex().to_string(),
        "battery_points": battery.len(),
        "differential": "PASSED — every battery point agrees with kernel-side evaluation",
        "claim": "differential check over the recorded battery; NOT a proof of \
                  translation correctness (see designs/2026-08-06-clean-extract-width1.md)",
        "model": "Lean UIntW is modular and is emitted as wrapping_* on the matching \
                  Rust width; Lean Nat is unbounded and is MODELLED as u64, so emitted \
                  Nat.add/Nat.mul abort on overflow of the model rather than wrapping",
    });
    std::fs::write(
        staging.join("manifest.json"),
        serde_json::to_string_pretty(&manifest)?,
    )?;
    if args.keep_temp {
        println!("scratch build kept at {}", build_dir.display());
    }
    install_staged(args, &staging, battery.len())
}

/// The Wasm backend: lower the SAME IR the C lane emits from, then run the
/// battery on a real Wasm host.
///
/// `emit_wasm` was a library entry point with nothing driving it. This is the
/// verb, and it keeps the lane's contract intact rather than relaxing it for a
/// new backend:
///
/// * FIXED-WIDTH ONLY. Wasm `i32`/`i64` arithmetic is modular, which is exactly
///   Lean's `UIntW` semantics. Lean `Nat` is unbounded and has no faithful Wasm
///   scalar, so a `Nat` in the signature REFUSES here rather than silently
///   adopting a 64-bit model — the Rust backend makes that model explicit in its
///   manifest, and a wasm module has nowhere to say it.
/// * THE BATTERY ALWAYS RUNS. Executing needs a Wasm host on PATH. Without one
///   the extraction REFUSES; it does not write an artifact whose `differential`
///   field would be a claim nobody checked.
fn handle_extract_wasm(args: &ExtractArgs) -> anyhow::Result<()> {
    let decl_name = Name::from_string(&args.decl);

    // 1-2. Same front half and same gate as the other two lanes.
    let compile_args = compile_args_for(args);
    let (lcnf, env, pipeline) = select_lcnf_decl(&compile_args)?;
    let sig = extraction_gate(&env, &decl_name).map_err(|r| anyhow::anyhow!("{r}"))?;

    // 3. Fixed-width-only refusal, BEFORE any emission.
    for ty in sig.params.iter().chain(std::iter::once(&sig.ret)) {
        if matches!(ty, ScalarTy::Nat | ScalarTy::Bool) {
            bail!(
                "E_WASM_SCALAR: `{}` has a `{ty:?}` in its signature; the wasm backend \
                 handles fixed-width integers only (Wasm i32/i64 are modular like Lean \
                 UIntW; Lean Nat is unbounded and Bool has no settled ABI here). Use \
                 `--backend rust` for those.",
                args.decl
            );
        }
    }

    // 4. Lower to the SAME `boxed_ir_decls` the C emitter consumes, then emit.
    let artifacts = clean_compiler::pass_manager::compile_lcnf_decls(&lcnf, &env, &pipeline)
        .context("lower LCNF to IR for wasm emission")?;
    let wat = clean_compiler::emit_wasm::emit_wat(&artifacts.boxed_ir_decls)
        .map_err(|e| anyhow::anyhow!("wasm emission refused: {e}"))?;
    let module = clean_compiler::emit_wasm::emit_wasm_binary(&artifacts.boxed_ir_decls)
        .map_err(|e| anyhow::anyhow!("wasm emission refused: {e}"))?;

    // 5-6. Battery on a real host.
    let tmp = tempfile::Builder::new()
        .prefix("clean-extract-wasm-")
        .tempdir()
        .context("create scratch dir")?;
    let battery = build_battery(&sig);
    let native_results = run_wasm_battery(&module, &args.decl, &sig, &battery, tmp.path())?;
    if native_results.len() != battery.len() {
        bail!(
            "wasm host produced {} results for {} inputs",
            native_results.len(),
            battery.len()
        );
    }

    // 7. The SAME differential as the other lanes.
    differential_check(&env, &args.decl, &sig, &battery, &native_results)?;

    // 8. Manifest + atomic install.
    let staging = tmp.path().join("out");
    std::fs::create_dir_all(&staging)?;
    std::fs::write(staging.join(format!("{}.wat", args.decl)), &wat)?;
    std::fs::write(staging.join(format!("{}.wasm", args.decl)), &module)?;
    let manifest = serde_json::json!({
        "schema": "clean-extract-v1",
        "decl": args.decl,
        "backend": "wasm",
        "wat_file": format!("{}.wat", args.decl),
        "wasm_file": format!("{}.wasm", args.decl),
        "wat_digest_blake3": blake3::hash(wat.as_bytes()).to_hex().to_string(),
        "wasm_digest_blake3": blake3::hash(&module).to_hex().to_string(),
        "battery_points": battery.len(),
        "differential": "PASSED — every battery point agrees with kernel-side evaluation",
        "claim": "differential check over the recorded battery; NOT a proof of \
                  translation correctness (see designs/2026-08-06-clean-extract-width1.md)",
        "model": "Lean UIntW is modular and Wasm i32/i64 arithmetic is modular at the \
                  same widths, so no overflow model is interposed; narrower widths are \
                  masked to their declared width",
    });
    std::fs::write(
        staging.join("manifest.json"),
        serde_json::to_string_pretty(&manifest)?,
    )?;
    if args.keep_temp {
        println!("scratch build kept at {}", tmp.path().display());
    }
    install_staged(args, &staging, battery.len())
}

/// Run the battery against `module` on a Wasm host, returning one unsigned
/// decimal per input tuple.
///
/// Refuses when no host is on PATH: a wasm artifact whose battery never ran
/// would ship a `differential: PASSED` nobody earned.
fn run_wasm_battery(
    module: &[u8],
    export: &str,
    sig: &GateSig,
    battery: &[Vec<u64>],
    dir: &Path,
) -> anyhow::Result<Vec<String>> {
    let host = ["node", "wasmtime", "wasmer"]
        .into_iter()
        .find(|h| {
            Command::new(h)
                .arg("--version")
                .output()
                .is_ok_and(|o| o.status.success())
        })
        .ok_or_else(|| {
            anyhow::anyhow!(
                "E_WASM_NO_HOST: no Wasm host found on PATH (tried node, wasmtime, \
                 wasmer). `clean extract --backend wasm` runs the differential battery \
                 on a real host and refuses rather than shipping an unchecked module."
            )
        })?;
    if host != "node" {
        bail!(
            "E_WASM_NO_HOST: found `{host}`, but only `node` has a wired driver today; \
             install node or extend run_wasm_battery."
        );
    }

    let wasm_path = dir.join("module.wasm");
    std::fs::write(&wasm_path, module).context("write wasm module")?;

    // `>>> 0` reinterprets the i32 result as unsigned, matching the kernel-side
    // readback; i64 results arrive as BigInt and stringify directly.
    let unsigned = if matches!(sig.ret, ScalarTy::UInt64) {
        "BigInt.asUintN(64, r).toString()"
    } else {
        "(r >>> 0).toString()"
    };
    let cases: Vec<String> = battery
        .iter()
        .map(|inputs| {
            let args: Vec<String> = inputs
                .iter()
                .zip(&sig.params)
                .map(|(v, t)| {
                    if matches!(t, ScalarTy::UInt64) {
                        format!("{v}n")
                    } else {
                        v.to_string()
                    }
                })
                .collect();
            format!("[{}]", args.join(","))
        })
        .collect();
    let js = format!(
        r#"const fs = require('fs');
const bytes = fs.readFileSync({path:?});
const inst = new WebAssembly.Instance(new WebAssembly.Module(bytes), {{}});
const f = inst.exports[{export:?}];
if (typeof f !== 'function') {{
  console.error('export ' + {export:?} + ' not found');
  process.exit(1);
}}
for (const a of [{cases}]) {{
  const r = f(...a);
  console.log({unsigned});
}}
"#,
        path = wasm_path.to_string_lossy(),
        export = export,
        cases = cases.join(","),
        unsigned = unsigned,
    );
    let js_path = dir.join("run.js");
    std::fs::write(&js_path, js).context("write wasm battery driver")?;

    let out = Command::new(host)
        .arg(&js_path)
        .output()
        .context("spawn wasm host")?;
    if !out.status.success() {
        bail!(
            "wasm host rejected the module: {}",
            String::from_utf8_lossy(&out.stderr).trim()
        );
    }
    Ok(String::from_utf8_lossy(&out.stdout)
        .lines()
        .map(|l| l.trim().to_string())
        .filter(|l| !l.is_empty())
        .collect())
}

/// Move a fully-built staging directory into `--out`, refusing to overwrite.
fn install_staged(args: &ExtractArgs, staging: &Path, battery_points: usize) -> anyhow::Result<()> {
    let out_dir = &args.out;
    if out_dir.exists() {
        bail!(
            "--out {} already exists; refusing to overwrite",
            out_dir.display()
        );
    }
    // Rename can cross devices when --out is elsewhere; fall back to copy.
    if std::fs::rename(staging, out_dir).is_err() {
        copy_dir(staging, out_dir)?;
    }
    println!(
        "extracted {} → {} ({battery_points} battery points, differential PASSED)",
        args.decl,
        out_dir.display(),
    );
    Ok(())
}

/// Compare each battery point's NATIVE result against kernel-side evaluation.
///
/// Split out of [`handle_extract_command`] so the comparison is reachable from a
/// test with results the caller chooses. The design
/// (`designs/2026-08-06-clean-extract-width1.md`, item 10) calls this the
/// "never-green-by-construction" requirement: a differential that cannot fail
/// proves nothing, and the layer-2 claim resting on it would be unfalsifiable.
/// `test_differential_check_detects_a_wrong_native_result` is that probe.
fn differential_check(
    env: &Environment,
    decl: &str,
    sig: &GateSig,
    battery: &[Vec<u64>],
    native_results: &[String],
) -> anyhow::Result<()> {
    for (inputs, native) in battery.iter().zip(native_results) {
        let expected = kernel_eval(env, decl, sig, inputs)
            .with_context(|| format!("kernel-side evaluation for inputs {inputs:?}"))?;
        if *native != expected {
            bail!(
                "DIFFERENTIAL MISMATCH for {decl} at inputs {inputs:?}: native `{native}` vs \
                 kernel `{expected}` — refusing to ship"
            );
        }
    }
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

fn compile_args_for(args: &ExtractArgs) -> clean_compiler::cli::CompileArgs {
    clean_compiler::cli::CompileArgs {
        file: Some(args.file.clone()),
        decl: Some(args.decl.clone()),
        emit: clean_compiler::cli::EmitFormat::C,
        opt_level: 0,
        output: None,
    }
}

/// Elaborate the source file and select the declaration, keeping only the
/// ENVIRONMENT.
///
/// Both backends go through [`select_lcnf_decl`] so they see the same
/// environment: intra-project `import` resolution, elaboration trust-warning
/// refusals, and kernel-checked registration. The Rust backend discards the
/// LCNF — it translates the kernel value directly — but shares this front half
/// deliberately, so a decl cannot mean one thing to one backend and something
/// else to the other.
fn elaborate_for_extraction(args: &ExtractArgs) -> anyhow::Result<Environment> {
    let (_lcnf, env, _pipeline) = select_lcnf_decl(&compile_args_for(args))?;
    Ok(env)
}

/// Reuse the `clean compile` closure/emitter for the C text.
fn select_and_emit(args: &ExtractArgs) -> anyhow::Result<(String, Environment)> {
    let compile_args = compile_args_for(args);
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

    /// FALSIFIABILITY: the differential must be able to FAIL.
    ///
    /// `designs/2026-08-06-clean-extract-width1.md` item 10 calls this the
    /// "never-green-by-construction" guard, and states the reason plainly —
    /// without it "the whole layer-2 claim is unfalsifiable". A differential
    /// check that always passes is not evidence of anything, and the shipped
    /// manifest asserts `differential: PASSED` on the strength of it.
    ///
    /// So: take the SAME declaration and battery the passing e2e test uses, and
    /// hand the comparator one native result that is off by one. It must reject.
    ///
    /// What this proves and what it does not: it proves the comparison step
    /// genuinely discriminates, so a `PASSED` verdict carries information. It is
    /// not a tampered-BINARY probe — that is the design's stronger form, and it
    /// needs a build-injection seam the C lane does not have. The Rust lane DOES
    /// have one (its emitter and its build are both ours), so the stronger probe
    /// lives at `test_rust_backend_differential_rejects_a_tampered_emission`.
    #[test]
    fn test_differential_check_detects_a_wrong_native_result() {
        let env = env_with("def affineU (a b : UInt32) : UInt32 := UInt32.add (UInt32.mul a b) b");
        let sig = extraction_gate(&env, &Name::from_string("affineU")).expect("v1 class");
        let battery = build_battery(&sig);
        assert!(!battery.is_empty(), "battery must be non-empty");

        // The honest baseline: kernel evaluation agrees with itself.
        let truthful: Vec<String> = battery
            .iter()
            .map(|inputs| kernel_eval(&env, "affineU", &sig, inputs).expect("kernel eval"))
            .collect();
        differential_check(&env, "affineU", &sig, &battery, &truthful)
            .expect("kernel-side results must agree with themselves");

        // Now corrupt exactly one point.
        let mut tampered = truthful.clone();
        let victim = tampered.len() - 1;
        let bogus = truthful[victim]
            .parse::<u64>()
            .map_or_else(|_| "0".to_string(), |v| (v.wrapping_add(1)).to_string());
        tampered[victim] = bogus;

        let err = differential_check(&env, "affineU", &sig, &battery, &tampered)
            .expect_err("a wrong native result MUST be caught");
        assert!(
            err.to_string().contains("DIFFERENTIAL MISMATCH"),
            "expected a differential mismatch, got: {err}"
        );
    }

    /// The WASM backend is REACHABLE — `clean extract --backend wasm` runs the
    /// whole chain, differential included.
    ///
    /// `emit_wat`/`emit_wasm_binary` were public library entry points with no verb
    /// driving them. A backend nobody can invoke is not a feature, and its tests
    /// were built from hand-written `IRDecl`s, so nothing checked that the real
    /// pipeline ever produces IR inside the emitter's fragment.
    ///
    /// Uses the identity declaration deliberately: see
    /// `test_extract_wasm_refuses_uintw_arithmetic_through_the_boxed_nat_path`
    /// for why arithmetic does not reach the emitter yet.
    ///
    /// Running the battery needs a Wasm host. Rather than skip silently when
    /// there is none — the failure mode that lets a lane rot unnoticed — this
    /// asserts the OTHER branch explicitly: no host must produce the specific
    /// `E_WASM_NO_HOST` refusal, never a written artifact.
    #[test]
    fn test_extract_wasm_backend_runs_the_whole_chain() {
        let tmp = tempfile::Builder::new()
            .prefix("clean-extract-wasm-e2e-")
            .tempdir()
            .expect("scratch dir");
        let src_path = tmp.path().join("idu.lean");
        std::fs::write(&src_path, "def idU (a : UInt32) : UInt32 := a\n").expect("write source");
        let out_dir = tmp.path().join("out");

        let args = ExtractArgs {
            file: src_path,
            decl: "idU".to_string(),
            out: out_dir.clone(),
            backend: ExtractBackend::Wasm,
            keep_temp: false,
        };
        match handle_extract_command(&args) {
            Ok(()) => {
                let wat = std::fs::read_to_string(out_dir.join("idU.wat")).expect("emitted wat");
                assert!(
                    wat.contains(r#"(export "idU")"#),
                    "the module must export the declaration; got:\n{wat}"
                );
                assert!(
                    wat.contains("param $v0 i32") && wat.contains("result i32"),
                    "UInt32 must lower to i32 in and out; got:\n{wat}"
                );
                assert!(
                    out_dir.join("idU.wasm").exists(),
                    "the binary module must be written alongside the text"
                );
                let manifest: serde_json::Value = serde_json::from_str(
                    &std::fs::read_to_string(out_dir.join("manifest.json")).expect("manifest"),
                )
                .expect("manifest is JSON");
                assert_eq!(manifest["backend"], "wasm");
                assert!(
                    manifest["differential"]
                        .as_str()
                        .is_some_and(|d| d.starts_with("PASSED")),
                    "the differential must have RUN on a host, not been assumed: {manifest}"
                );
            }
            Err(e) => {
                let msg = e.to_string();
                assert!(
                    msg.contains("E_WASM_NO_HOST"),
                    "without a Wasm host the ONLY acceptable outcome is the explicit \
                     no-host refusal (never a written artifact); got: {msg}"
                );
                assert!(!out_dir.exists(), "a refused extraction must write nothing");
            }
        }
    }

    /// `Nat` is refused BEFORE emission, with its own diagnostic.
    ///
    /// Wasm i32/i64 arithmetic is modular, which is exactly Lean `UIntW`. Lean
    /// `Nat` is unbounded and has no faithful Wasm scalar — the Rust backend
    /// makes its u64 model explicit in the manifest, and a wasm module has
    /// nowhere to say that. So this refuses rather than adopting a silent model.
    #[test]
    fn test_extract_wasm_refuses_nat_signatures() {
        let tmp = tempfile::Builder::new()
            .prefix("clean-extract-wasm-nat-")
            .tempdir()
            .expect("scratch dir");
        let src_path = tmp.path().join("dbl.lean");
        std::fs::write(&src_path, "def double (n : Nat) : Nat := Nat.add n n\n")
            .expect("write source");
        let out_dir = tmp.path().join("out");

        let args = ExtractArgs {
            file: src_path,
            decl: "double".to_string(),
            out: out_dir.clone(),
            backend: ExtractBackend::Wasm,
            keep_temp: false,
        };
        let err = handle_extract_command(&args).expect_err("a Nat signature must refuse");
        assert!(
            err.to_string().contains("E_WASM_SCALAR"),
            "expected the fixed-width refusal, got: {err}"
        );
        assert!(!out_dir.exists(), "a refused extraction must write nothing");
    }

    /// MEASURED GAP: UIntW ARITHMETIC does not reach the emitter yet.
    ///
    /// `def duo (a b : UInt32) : UInt32 := UInt32.add a b` refuses, because the
    /// prelude's `UInt32.add` is compiled FROM SOURCE and routes through boxed
    /// `Nat` (`clean_box_uint32` → `l_UInt32_toNat` → `l_Nat_add` →
    /// `l_UInt32_ofNat`), so `boxed_ir_decls` carries `Object`-typed bindings
    /// that are outside the Wasm fragment.
    ///
    /// This is a REAL build item, and it is exactly what wiring the verb
    /// exposed: rank 11's emitter was tested against hand-built `IRDecl`s, so
    /// nothing had ever checked whether the pipeline actually produces IR in its
    /// fragment. Closing it means lowering saturated UIntW ops to native BinOps
    /// (as `emit_trust_ir`'s `uint_arith_binop` already does) instead of through
    /// boxed Nat.
    ///
    /// Pinned as a test so the day that lowering lands, this FAILS and says so.
    #[test]
    fn test_extract_wasm_refuses_uintw_arithmetic_through_the_boxed_nat_path() {
        let tmp = tempfile::Builder::new()
            .prefix("clean-extract-wasm-gap-")
            .tempdir()
            .expect("scratch dir");
        let src_path = tmp.path().join("duo.lean");
        std::fs::write(
            &src_path,
            "def duo (a b : UInt32) : UInt32 := UInt32.add a b\n",
        )
        .expect("write source");
        let out_dir = tmp.path().join("out");

        let args = ExtractArgs {
            file: src_path,
            decl: "duo".to_string(),
            out: out_dir.clone(),
            backend: ExtractBackend::Wasm,
            keep_temp: false,
        };
        let err = handle_extract_command(&args)
            .expect_err("UIntW arithmetic does not reach the Wasm fragment today");
        let msg = err.to_string();
        assert!(
            msg.contains("outside the Wasm fragment"),
            "expected the emitter's own fragment refusal (the boxed-Nat route), \
             got: {msg}"
        );
        assert!(!out_dir.exists(), "a refused extraction must write nothing");
    }

    /// END-TO-END: the design's canonical V1 pick actually extracts.
    ///
    /// `designs/2026-08-06-clean-extract-width1.md` names
    /// `def affineU (a b : UInt32) : UInt32 := UInt32.add (UInt32.mul a b) b`
    /// as the V1 target — the unique shape that both emits self-contained C and
    /// lands in trust-ir TV Fragment-2.
    ///
    /// It did not extract. Every UIntW declaration — including the minimal
    /// `duo` — bailed with "uncovered extern in emitted C: `l_UInt32_ofNat`",
    /// because the prelude's `UInt32.add`/`mul` compile from source and route
    /// through `UInt32.ofNat`, which had no shim. One missing symbol blocked the
    /// whole lane.
    ///
    /// It went unnoticed because THE CHAIN HAD NO TEST: the three tests beside
    /// this one exercise `extraction_gate` only, and the gate happily accepts
    /// `affineU` — the refusal happens two steps later, at the extern boundary.
    /// So this test runs the real command and asserts the real artifacts.
    #[test]
    fn test_extract_uintw_v1_pick_runs_the_whole_chain() {
        let tmp = tempfile::Builder::new()
            .prefix("clean-extract-e2e-")
            .tempdir()
            .expect("scratch dir");
        let src_path = tmp.path().join("affine.lean");
        std::fs::write(
            &src_path,
            "def affineU (a b : UInt32) : UInt32 := UInt32.add (UInt32.mul a b) b\n",
        )
        .expect("write source");
        let out_dir = tmp.path().join("out");

        let args = ExtractArgs {
            file: src_path,
            decl: "affineU".to_string(),
            out: out_dir.clone(),
            backend: ExtractBackend::C,
            keep_temp: false,
        };
        handle_extract_command(&args).expect("the V1 pick must extract end to end");

        let c = std::fs::read_to_string(out_dir.join("affineU.c")).expect("emitted C");
        assert!(
            c.contains("uint32_t l_affineU(uint32_t"),
            "the extracted entry must keep the unboxed uint32_t ABI; got:\n{c}"
        );

        let manifest: serde_json::Value = serde_json::from_str(
            &std::fs::read_to_string(out_dir.join("manifest.json")).expect("manifest"),
        )
        .expect("manifest is JSON");
        assert_eq!(manifest["decl"], "affineU");
        assert!(
            manifest["differential"]
                .as_str()
                .is_some_and(|d| d.starts_with("PASSED")),
            "the differential must PASS: {manifest}"
        );
        let points = manifest["battery_points"].as_u64().expect("battery_points");
        assert!(
            points >= 8,
            "the battery must actually have run points (incl. the 2^32 wraparound \
             pair that exercises `ofNat`'s truncation); got {points}"
        );
    }

    /// The `--backend` flag is actually WIRED to the clap surface, and `c`
    /// remains the default so the existing C lane is untouched.
    ///
    /// The e2e tests below call [`handle_extract_command`] directly — the same
    /// function `Commands::Extract` dispatches to — which proves the pipeline
    /// but not the argument plumbing. This closes that last gap without needing
    /// a binary build.
    #[test]
    fn test_backend_flag_is_wired_and_defaults_to_c() {
        use clap::Parser as _;

        let parse = |extra: &[&str]| {
            let mut argv = vec!["clean", "extract", "f.lean", "--decl", "d", "--out", "o"];
            argv.extend_from_slice(extra);
            match crate::cli_args::Cli::try_parse_from(argv)
                .expect("the extract surface must parse")
                .command
            {
                crate::cli_args::Commands::Extract(a) => a.backend,
                _ => panic!("`clean extract ...` must parse as Commands::Extract"),
            }
        };

        assert_eq!(
            parse(&[]),
            ExtractBackend::C,
            "the default must stay `c` — the Rust backend is additive"
        );
        assert_eq!(parse(&["--backend", "rust"]), ExtractBackend::Rust);
        assert_eq!(parse(&["--backend", "c"]), ExtractBackend::C);
        assert!(
            crate::cli_args::Cli::try_parse_from([
                "clean",
                "extract",
                "f.lean",
                "--decl",
                "d",
                "--out",
                "o",
                "--backend",
                "haskell",
            ])
            .is_err(),
            "an unknown backend must be rejected by the value enum"
        );
    }

    /// END-TO-END (Rust backend): the same V1 pick extracts to READABLE, SAFE
    /// Rust, and the shipped artifact is the thing a human would want.
    ///
    /// The C half of this rung ships a `clean_obj*`/Perceus translation unit —
    /// correct, and not what a Rocq user means by "extract to a host language".
    /// This asserts the properties that make the Rust artifact different in
    /// kind, not just in file extension: no `unsafe`, a plain `u32` signature,
    /// and the modular arithmetic spelled `wrapping_*` EXPLICITLY (Lean's
    /// `UInt32.add` wraps; bare `+` would panic in debug and wrap in release,
    /// so an implicit spelling would be a build-profile-dependent semantics).
    #[test]
    fn test_extract_rust_backend_runs_the_whole_chain() {
        let tmp = tempfile::Builder::new()
            .prefix("clean-extract-rust-e2e-")
            .tempdir()
            .expect("scratch dir");
        let src_path = tmp.path().join("affine.lean");
        std::fs::write(
            &src_path,
            "def affineU (a b : UInt32) : UInt32 := UInt32.add (UInt32.mul a b) b\n",
        )
        .expect("write source");
        let out_dir = tmp.path().join("out");

        let args = ExtractArgs {
            file: src_path,
            decl: "affineU".to_string(),
            out: out_dir.clone(),
            backend: ExtractBackend::Rust,
            keep_temp: false,
        };
        handle_extract_command(&args).expect("the V1 pick must extract to Rust end to end");

        let rs = std::fs::read_to_string(out_dir.join("affineU.rs")).expect("emitted Rust");
        assert!(
            rs.contains("pub fn affineU(a: u32, b: u32) -> u32"),
            "the emitted signature must be plain scalars, not boxed objects; got:\n{rs}"
        );
        assert!(
            rs.contains("a.wrapping_mul(b).wrapping_add(b)"),
            "Lean's UInt32 arithmetic is modular and must be spelled wrapping_* \
             explicitly; got:\n{rs}"
        );
        let code_only: String = rs
            .lines()
            .filter(|l| !l.trim_start().starts_with("//"))
            .collect::<Vec<_>>()
            .join("\n");
        assert!(
            !code_only.contains("unsafe"),
            "the emitted Rust must be safe; got:\n{rs}"
        );

        let manifest: serde_json::Value = serde_json::from_str(
            &std::fs::read_to_string(out_dir.join("manifest.json")).expect("manifest"),
        )
        .expect("manifest is JSON");
        assert_eq!(manifest["decl"], "affineU");
        assert_eq!(manifest["backend"], "rust");
        assert!(
            manifest["differential"]
                .as_str()
                .is_some_and(|d| d.starts_with("PASSED")),
            "the differential must PASS: {manifest}"
        );
        let points = manifest["battery_points"].as_u64().expect("battery_points");
        assert!(
            points >= 7,
            "the battery must actually have run points (incl. the 2^32 wraparound \
             pair); got {points}"
        );
    }

    /// END-TO-END (Rust backend, `Nat`): the second v1 pick from the rung brief.
    ///
    /// `Nat` is the interesting case because Lean's `Nat` is UNBOUNDED and the
    /// emitted `u64` is only a MODEL of it. The honest spelling therefore is not
    /// `wrapping_add` (which would silently give a wrong answer past 2^64) but
    /// `checked_add(..).expect(..)`, which aborts at the model's edge. This pins
    /// that choice so a later "simplification" to `+` or `wrapping_add` fails.
    #[test]
    fn test_extract_rust_backend_nat_models_are_checked_not_wrapping() {
        let tmp = tempfile::Builder::new()
            .prefix("clean-extract-rust-nat-")
            .tempdir()
            .expect("scratch dir");
        let src_path = tmp.path().join("double.lean");
        std::fs::write(&src_path, "def double (n : Nat) : Nat := Nat.add n n\n")
            .expect("write source");
        let out_dir = tmp.path().join("out");

        handle_extract_command(&ExtractArgs {
            file: src_path,
            decl: "double".to_string(),
            out: out_dir.clone(),
            backend: ExtractBackend::Rust,
            keep_temp: false,
        })
        .expect("the Nat pick must extract to Rust end to end");

        let rs = std::fs::read_to_string(out_dir.join("double.rs")).expect("emitted Rust");
        assert!(
            rs.contains("pub fn double(a: u64) -> u64"),
            "Nat is modelled as u64 in a plain signature; got:\n{rs}"
        );
        assert!(
            rs.contains("a.checked_add(a)") && rs.contains(".expect("),
            "Lean Nat does not wrap, so the u64 model must abort at its edge \
             rather than wrap; got:\n{rs}"
        );
        assert!(
            !rs.contains("wrapping_add"),
            "wrapping arithmetic would be WRONG for Nat; got:\n{rs}"
        );
    }

    /// FALSIFIABILITY, strong form: TAMPER WITH THE EMITTED PROGRAM.
    ///
    /// `test_differential_check_detects_a_wrong_native_result` probes the
    /// comparator with a hand-corrupted result string. This probes the whole
    /// Rust chain: take the module the emitter really produced, flip one
    /// operator in the emitted TEXT, then compile-and-run it for real and feed
    /// the genuine binary's output to the genuine differential. It must reject.
    ///
    /// This is the tampered-BINARY probe the design
    /// (`designs/2026-08-06-clean-extract-width1.md`, item 10) asks for and the
    /// C lane could not reach: the Rust backend owns its emitter and its build,
    /// so `run_rust_battery` takes the module as a PARAMETER, which is exactly
    /// the injection seam.
    #[test]
    fn test_rust_backend_differential_rejects_a_tampered_emission() {
        let env = env_with("def affineU (a b : UInt32) : UInt32 := UInt32.add (UInt32.mul a b) b");
        let name = Name::from_string("affineU");
        let sig = extraction_gate(&env, &name).expect("v1 class");
        let battery = build_battery(&sig);
        let module = extract_rust::emit_rust_module(&env, &name, &sig).expect("emit");
        let driver = extract_rust::render_rust_battery_driver("affineU", &sig, &battery);

        let tmp = tempfile::Builder::new()
            .prefix("clean-extract-tamper-")
            .tempdir()
            .expect("scratch dir");
        let honest_dir = tmp.path().join("honest");
        std::fs::create_dir_all(&honest_dir).expect("mkdir");
        let honest = extract_rust::run_rust_battery(&module, &driver, &honest_dir)
            .expect("the honest emission must build and run");
        assert_eq!(honest.len(), battery.len(), "one result per battery point");
        differential_check(&env, "affineU", &sig, &battery, &honest)
            .expect("the honest emission must pass the differential");

        // One operator, flipped. Still valid Rust; still compiles; wrong.
        let tampered = module.replace("wrapping_add", "wrapping_sub");
        assert_ne!(tampered, module, "the tamper must actually change the text");
        let tampered_dir = tmp.path().join("tampered");
        std::fs::create_dir_all(&tampered_dir).expect("mkdir");
        let bad = extract_rust::run_rust_battery(&tampered, &driver, &tampered_dir)
            .expect("the tampered emission still compiles — that is the point");
        let err = differential_check(&env, "affineU", &sig, &battery, &bad)
            .expect_err("a tampered emission MUST be caught by the differential");
        assert!(
            err.to_string().contains("DIFFERENTIAL MISMATCH"),
            "expected a differential mismatch, got: {err}"
        );
    }

    /// The Rust emitter is FAIL-CLOSED: an unrecognised constant refuses with a
    /// stable `E_RUST_*` code rather than guessing.
    ///
    /// `Nat.succ` passes the extraction gate (first-order `Nat → Nat`, no
    /// recursor mentioned) but has no entry in the v1 emission table. The wrong
    /// behaviour here would be to emit something plausible; the right behaviour
    /// is to refuse with a code the caller can act on.
    #[test]
    fn test_rust_emitter_refuses_constants_outside_the_v1_table() {
        let env = env_with("def g (n : Nat) : Nat := Nat.succ n");
        let name = Name::from_string("g");
        let sig = extraction_gate(&env, &name).expect("gate accepts a first-order Nat def");
        let err = extract_rust::emit_rust_module(&env, &name, &sig)
            .expect_err("an unlisted constant must REFUSE, not be guessed at");
        assert!(
            err.to_string().starts_with("E_RUST_UNSUPPORTED"),
            "expected a stable E_RUST_UNSUPPORTED refusal, got: {err}"
        );
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

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
    pub(crate) fn of(e: &Expr) -> Option<Self> {
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
            // `Nat` is the boxed runtime object; every FIXED-WIDTH scalar,
            // INCLUDING `Bool`, is unboxed. `emit_c`'s `emit_type` maps
            // `IRType::Bool` to `uint8_t`, so boxing a Bool argument produced
            // `passing 'clean_obj *' to parameter of type 'uint8_t'` and the
            // whole battery failed to link — which is how the first
            // control-flow declaration (`if b then x else y`) was blocked on
            // the C lane even though the emitter compiled it correctly.
            ScalarTy::Nat => format!("clean_box({v}u)"),
            ScalarTy::Bool => format!("(uint8_t){v}"),
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
        // `Nat.rec` IS ADMITTED. Structural recursion on `Nat` elaborates to it,
        // and the backends lower it to a loop whose bound is the scrutinee —
        // `Nat.rec z s n` is exactly "apply `s` n times starting from `z`". So
        // termination is not a new proof obligation: it is inherited from the
        // kernel, which accepted the definition only because the recursor is
        // well-founded, and it is MANIFEST in the emitted code as a counted
        // loop.
        //
        // Everything else still refuses, and the distinction is the point:
        //
        //   `WellFounded.fix` / `Acc.rec` — termination rests on an accessibility
        //   proof that is ERASED at extraction. Emitting a loop for those would
        //   assert a bound the artifact does not carry, and a non-terminating
        //   extraction HANGS the battery rather than failing it. That is the one
        //   failure mode this harness cannot report, so it must not be reachable.
        //
        //   Other `.rec`/`.recOn`/`.brecOn` — recursion over containers whose
        //   values are not in the v1 scalar allowlist anyway.
        if s == "Nat.rec" {
            return;
        }
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

    // 7b. TV leg (extract v1.2): kernel-decided translation certificate for
    // the trust-ir lowering of the same closure, when the build carries it.
    // A kernel REFUSAL is a detected miscompile — the extract fails closed.
    let tv = tv_certificate_entry(args)?;

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
        "tv": tv,
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

/// The TV leg of the extract manifest (v1.2): run the SAME L5CNF closure
/// through the trust-ir backend with `certify_translation` on (the default)
/// and report the target decl's kernel-decided certificate status.
///
/// THE CLAIM IS SCOPED HONESTLY. The certificate — minted by
/// `emit_trust_ir_tv`, independently re-checkable by trust-ir-build's
/// `clean_backend_tv` anchor — says the emitted TRUST-IR function denotes the
/// original kernel definition under the Nat-mod-2^w vocabulary (Fragment-2/4).
/// It says NOTHING about the `.c` text this extract ships; that text is held
/// only to the differential. The manifest wording keeps the two separate.
///
/// Fail-closed split:
/// - kernel REFUSAL (a detected miscompile of an in-fragment decl) — the
///   whole extract errors and writes nothing (the `?` at the call site);
/// - out-of-fragment decl — an honest `"skipped"` status with the minter's
///   reason, never a fake certificate.
#[cfg(feature = "trust-ir-backend")]
fn tv_certificate_entry(args: &ExtractArgs) -> anyhow::Result<serde_json::Value> {
    use clean_compiler::emit_trust_ir::TrustIrError;
    use clean_compiler::pass_manager::PipelineError;

    let compile_args = compile_args_for(args);
    let (lcnf, env, pipeline) = select_lcnf_decl(&compile_args)?;
    // The census/object-path config: `ExternCalls` carries the runtime ABI
    // import table, which is what lets `declare_extern_fallbacks` declare the
    // shim-dropped closure boundary (UInt32.toNat & co.) as typed extern
    // imports instead of dying `undefined function`. `Dialect` (the default)
    // has no runtime table, so emission failed on exactly those symbols.
    let emit_cfg = clean_compiler::emit_trust_ir::TrustIrConfig {
        runtime_lowering: clean_compiler::emit_trust_ir::RuntimeLowering::ExternCalls,
        ..clean_compiler::emit_trust_ir::TrustIrConfig::default()
    };
    let (_module, report) = match clean_compiler::pass_manager::compile_lcnf_to_trust_ir_with_report(
        &lcnf, &env, &pipeline, &emit_cfg,
    ) {
        Ok(ok) => ok,
        // A kernel REFUSAL is a DETECTED MISCOMPILE of an in-fragment decl:
        // the same L5CNF lowering feeds the shipped C, so nothing ships.
        Err(PipelineError::TrustIr(TrustIrError::TranslationRefused(refused))) => {
            anyhow::bail!(
                "TV leg: kernel REFUSED the translation certificate (detected                  miscompile) for {refused:?} — refusing to ship"
            );
        }
        // Any other error means the trust-ir backend cannot even EMIT this
        // closure (e.g. an extern the C lane covers with a shim is simply
        // undefined there). There is nothing to certify — an honest
        // "unattempted" with the reason, never a fake status either way.
        Err(other) => {
            return Ok(serde_json::json!({
                "status": "unattempted",
                "decl": args.decl,
                "reason": format!("trust-ir lowering unavailable for this closure: {other}"),
            }));
        }
    };
    let scope = "kernel-decided certificate that the emitted TRUST-IR function \
                 denotes the original kernel definition (Nat mod 2^w, \
                 Fragment-2/4); says NOTHING about the shipped .c text, which \
                 is held only to the differential";
    if report.certified.iter().any(|n| n == &args.decl) {
        return Ok(serde_json::json!({
            "status": "certified",
            "decl": args.decl,
            "scope": scope,
            "recheck": "trust-ir-build anchor clean_backend_tv",
            "closure_certified": report.certified,
            "closure_skipped": report.skipped.len(),
        }));
    }
    let reason = report
        .skipped
        .iter()
        .find(|(n, _)| n == &args.decl)
        .map(|(_, r)| r.clone())
        .unwrap_or_else(|| "no stored kernel value to certify against".to_string());
    Ok(serde_json::json!({
        "status": "skipped",
        "decl": args.decl,
        "reason": reason,
        "scope": scope,
        "closure_certified": report.certified,
        "closure_skipped": report.skipped.len(),
    }))
}

/// Without the `trust-ir-backend` feature there is no certificate machinery in
/// the binary at all — the manifest says so instead of silently omitting the
/// field (an absent field reads as "nobody thought about it"; this reads as
/// "not attempted, and here is why").
#[cfg(not(feature = "trust-ir-backend"))]
fn tv_certificate_entry(_args: &ExtractArgs) -> anyhow::Result<serde_json::Value> {
    Ok(serde_json::json!({
        "status": "unavailable",
        "note": "built without the trust-ir-backend feature; no TV certificate \
                 was attempted",
    }))
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

/// Elaborate the source file, keeping only the ENVIRONMENT.
///
/// Both backends go through [`crate::cmd_compile::elaborate_file_to_env`] so
/// they see the same environment: intra-project `import` resolution,
/// elaboration trust-warning refusals, and kernel-checked registration. A decl
/// cannot mean one thing to one backend and something else to the other.
///
/// What the Rust lane deliberately does NOT share is `select_lcnf_decl`'s
/// L5CNF lowering of the root: it translates the KERNEL value directly, and
/// requiring the root to also be L5CNF-lowerable rejected declarations inside
/// the Rust emitter's own fragment. Measured case: a three-arm Nat match
/// (`| 0 => 1 | 1 => 2 | _ => 0`) elaborates with a beta-redex default arm
/// (`(fun _ => 0) k`), which `to_lcnf` refuses (`Application head: Lam`) —
/// so both lanes refused a term the Rust table translates soundly.
fn elaborate_for_extraction(args: &ExtractArgs) -> anyhow::Result<Environment> {
    crate::cmd_compile::elaborate_file_to_env(&args.file)
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
    // Only `Nat` comes back boxed; `Bool` is a `uint8_t` like the other
    // fixed-width scalars (see `c_literal`).
    let boxed_ret = matches!(sig.ret, ScalarTy::Nat);
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

    /// UIntW ARITHMETIC reaches the Wasm emitter — the design's V1 pick, natively.
    ///
    /// This test previously pinned the OPPOSITE, and said so: wiring the verb
    /// revealed that `def duo (a b : UInt32) := UInt32.add a b` refused with
    /// "type Object is outside the Wasm fragment", because the prelude's
    /// `UInt32.add` is compiled FROM SOURCE through boxed `Nat`
    /// (`clean_box_uint32` → `UInt32.toNat` → `Nat.add` → `UInt32.ofNat`), so its
    /// `IRDecl` carried `Object` bindings that sank the whole module.
    ///
    /// The callee's body was never needed: `lower_expr` already lowered a
    /// saturated call to `UIntW.{add,sub,mul}` into the native instruction.
    /// `lower_module` now SKIPS the primitives themselves — the same shape as
    /// `native_build::is_primitive_denylisted` on the C side — keyed on the very
    /// table that lowers the call sites, so the skip set and the realized set
    /// cannot drift.
    ///
    /// The result is the design's canonical V1 pick as straight-line native Wasm:
    ///
    /// ```wat
    /// (func $l_affineU (export "affineU") (param $v0 i32) (param $v1 i32) (result i32)
    ///   local.get $v0  local.get $v1  i32.mul  local.set $v2
    ///   local.get $v2  local.get $v1  i32.add  local.set $v3
    ///   local.get $v3)
    /// ```
    ///
    /// No boxing, no calls, and the differential agrees with kernel evaluation on
    /// every battery point INCLUDING the 2^32 wraparound pair — which is what
    /// actually establishes that Wasm's modular i32 matches Lean's `UInt32`.
    #[test]
    fn test_extract_wasm_lowers_uintw_arithmetic_to_native_instructions() {
        let tmp = tempfile::Builder::new()
            .prefix("clean-extract-wasm-arith-")
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
            backend: ExtractBackend::Wasm,
            keep_temp: false,
        };
        match handle_extract_command(&args) {
            Ok(()) => {
                let wat =
                    std::fs::read_to_string(out_dir.join("affineU.wat")).expect("emitted wat");
                assert!(
                    wat.contains("i32.mul") && wat.contains("i32.add"),
                    "UIntW arithmetic must lower to NATIVE instructions, not calls \
                     through boxed Nat; got:\n{wat}"
                );
                assert!(
                    !wat.contains("call"),
                    "the emitted module must be call-free — a `call` means the boxed \
                     prelude body leaked back in; got:\n{wat}"
                );
                let manifest: serde_json::Value = serde_json::from_str(
                    &std::fs::read_to_string(out_dir.join("manifest.json")).expect("manifest"),
                )
                .expect("manifest is JSON");
                assert!(
                    manifest["differential"]
                        .as_str()
                        .is_some_and(|d| d.starts_with("PASSED")),
                    "the differential must have RUN: {manifest}"
                );
                assert!(
                    manifest["battery_points"].as_u64().expect("points") >= 8,
                    "the battery must include the wraparound pair that proves Wasm's \
                     modular i32 matches Lean UInt32: {manifest}"
                );
            }
            Err(e) => {
                let msg = e.to_string();
                assert!(
                    msg.contains("E_WASM_NO_HOST"),
                    "without a Wasm host the ONLY acceptable outcome is the explicit \
                     no-host refusal; got: {msg}"
                );
            }
        }
    }

    /// The battery must STRADDLE a Bool branch, or control-flow extraction is
    /// validating nothing.
    ///
    /// This is the anti-vacuity property for `if`. The differential compares
    /// native execution against kernel evaluation per battery point — but if
    /// every point supplied the same Bool, only ONE arm of the conditional
    /// would ever run, and a backend that emitted the branches backwards would
    /// still pass. `build_battery` zips per-type batteries with modular
    /// wraparound, so a Bool (battery `[0, 1]`) alternates against the longer
    /// integer battery. Pinned here because a later battery change could
    /// silently make a Bool constant and quietly hollow out every branch test.
    #[test]
    fn test_battery_straddles_a_bool_branch() {
        let sig = GateSig {
            params: vec![ScalarTy::Bool, ScalarTy::UInt32, ScalarTy::UInt32],
            ret: ScalarTy::UInt32,
        };
        let battery = build_battery(&sig);
        let bools: std::collections::HashSet<u64> =
            battery.iter().filter_map(|t| t.first().copied()).collect();
        assert!(
            bools.contains(&0) && bools.contains(&1),
            "the battery must exercise BOTH arms of a Bool conditional; got {bools:?} \
             over {} points",
            battery.len()
        );
    }

    /// CONTROL FLOW end to end: `if` extracts on the C and Rust lanes.
    ///
    /// This is the increment that takes extraction from "straight-line
    /// arithmetic" to something you could point at real code. Both lanes run
    /// the full chain — emit, build, run the battery, differential against
    /// kernel evaluation — and the battery straddles the branch (see above), so
    /// a backwards conditional would be caught rather than merely unexercised.
    ///
    /// The C lane could always EMIT the branch; what blocked it was the battery
    /// driver boxing a `Bool` argument while `emit_type` maps `IRType::Bool` to
    /// an unboxed `uint8_t`, so the program failed to link. The Rust lane needed
    /// `ite` in its emission table.
    #[test]
    fn test_extract_control_flow_if_on_c_and_rust() {
        for backend in [ExtractBackend::C, ExtractBackend::Rust] {
            let tmp = tempfile::Builder::new()
                .prefix("clean-extract-if-")
                .tempdir()
                .expect("scratch dir");
            let src_path = tmp.path().join("ifs.lean");
            std::fs::write(
                &src_path,
                "def pick (b : Bool) (x y : UInt32) : UInt32 := if b then x else y\n",
            )
            .expect("write source");
            let out_dir = tmp.path().join("out");

            let args = ExtractArgs {
                file: src_path,
                decl: "pick".to_string(),
                out: out_dir.clone(),
                backend,
                keep_temp: false,
            };
            handle_extract_command(&args)
                .unwrap_or_else(|e| panic!("`if` must extract on the {backend:?} lane: {e}"));

            let manifest: serde_json::Value = serde_json::from_str(
                &std::fs::read_to_string(out_dir.join("manifest.json")).expect("manifest"),
            )
            .expect("manifest is JSON");
            assert!(
                manifest["differential"]
                    .as_str()
                    .is_some_and(|d| d.starts_with("PASSED")),
                "{backend:?}: the differential must PASS: {manifest}"
            );

            if backend == ExtractBackend::Rust {
                let rs = std::fs::read_to_string(out_dir.join("pick.rs")).expect("emitted rust");
                assert!(
                    rs.contains("if a { b } else { c }"),
                    "the Rust lane must emit a real conditional with the arms in \
                     SOURCE order — swapping them would still typecheck; got:\n{rs}"
                );
                // Check for an `unsafe` BLOCK/fn, not the word — the module's
                // own header comment advertises "no `unsafe`", so a bare
                // substring test matches the promise instead of a violation.
                assert!(
                    !rs.contains("unsafe {") && !rs.contains("unsafe fn"),
                    "the readable-Rust guarantee must hold through control flow \
                     too; got:\n{rs}"
                );
            }
        }
    }

    /// `match` on a Nat extracts on both lanes — the second control-flow form,
    /// and the first that BINDS a variable.
    ///
    /// `Nat.casesOn` is what a `| 0 => … | k + 1 => …` match elaborates to. The
    /// successor arm binds the predecessor, so unlike `if` the emitter has to
    /// extend its scope rather than just pick between two closed expressions.
    ///
    /// The battery for a `Nat` parameter is `[0, 1, 2, 3, 7, 12, 63]`, so it
    /// contains `0` AND non-zero values — both arms run, which is what makes the
    /// differential meaningful here (see `test_battery_straddles_a_bool_branch`
    /// for the same property stated for `if`).
    #[test]
    fn test_extract_match_on_nat_on_c_and_rust() {
        const SRC: &str = "\
def predOr (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | k + 1 => k
";
        for backend in [ExtractBackend::C, ExtractBackend::Rust] {
            let tmp = tempfile::Builder::new()
                .prefix("clean-extract-match-")
                .tempdir()
                .expect("scratch dir");
            let src_path = tmp.path().join("mt.lean");
            std::fs::write(&src_path, SRC).expect("write source");
            let out_dir = tmp.path().join("out");

            let args = ExtractArgs {
                file: src_path,
                decl: "predOr".to_string(),
                out: out_dir.clone(),
                backend,
                keep_temp: false,
            };
            handle_extract_command(&args)
                .unwrap_or_else(|e| panic!("`match` must extract on the {backend:?} lane: {e}"));

            let manifest: serde_json::Value = serde_json::from_str(
                &std::fs::read_to_string(out_dir.join("manifest.json")).expect("manifest"),
            )
            .expect("manifest is JSON");
            assert!(
                manifest["differential"]
                    .as_str()
                    .is_some_and(|d| d.starts_with("PASSED")),
                "{backend:?}: the differential must PASS: {manifest}"
            );

            if backend == ExtractBackend::Rust {
                let rs = std::fs::read_to_string(out_dir.join("predOr.rs")).expect("emitted rust");
                assert!(
                    rs.contains("== 0") && rs.contains("- 1"),
                    "the successor arm must bind the PREDECESSOR, not the scrutinee; \
                     got:\n{rs}"
                );
                assert!(
                    !rs.contains("unsafe {") && !rs.contains("unsafe fn"),
                    "the readable-Rust guarantee must survive a binding match; got:\n{rs}"
                );
            }
        }
    }

    /// The THREE-ARM match — `| 0 => 1 | 1 => 2 | _ => 0` — extracts on the
    /// Rust lane.
    ///
    /// This is the traffic-light protocol stepper's SPEC step
    /// (`data/graduation/clean-streams`), and the first match whose
    /// elaboration carries a BETA-REDEX: the shared `_` arm arrives inside the
    /// successor branch as an application whose head is a LAMBDA, not a
    /// constant. `translate_beta_redex` binds each redex argument once with a
    /// `let` and translates the body in the extended scope.
    ///
    /// Rust lane only, deliberately: the C lane goes through the L5CNF
    /// lowering, which refuses this exact term (`Application head: Lam`).
    /// Pinning that refusal here would turn a lowering gap into a contract —
    /// the gap is a compiler-side build item, and `scripts/streams_green.sh`
    /// records whatever C-lane verdict it measures instead.
    ///
    /// The Nat battery is `[0, 1, 2, 3, 7, 12, 63]`, so the differential
    /// exercises all three arms AND the out-of-invariant points (7, 12, 63 all
    /// take the `_` arm) against kernel evaluation.
    #[test]
    fn test_extract_three_arm_match_on_rust() {
        const SRC: &str = "\
def stepCase (i : Nat) : Nat :=
  match i with
  | 0 => 1
  | 1 => 2
  | _ => 0
";
        let tmp = tempfile::Builder::new()
            .prefix("clean-extract-3arm-")
            .tempdir()
            .expect("scratch dir");
        let src_path = tmp.path().join("steps.lean");
        std::fs::write(&src_path, SRC).expect("write source");
        let out_dir = tmp.path().join("out");

        let args = ExtractArgs {
            file: src_path,
            decl: "stepCase".to_string(),
            out: out_dir.clone(),
            backend: ExtractBackend::Rust,
            keep_temp: false,
        };
        handle_extract_command(&args)
            .unwrap_or_else(|e| panic!("the three-arm match must extract on the Rust lane: {e}"));

        let manifest: serde_json::Value = serde_json::from_str(
            &std::fs::read_to_string(out_dir.join("manifest.json")).expect("manifest"),
        )
        .expect("manifest is JSON");
        assert!(
            manifest["differential"]
                .as_str()
                .is_some_and(|d| d.starts_with("PASSED")),
            "the differential must PASS: {manifest}"
        );

        let rs = std::fs::read_to_string(out_dir.join("stepCase.rs")).expect("emitted rust");
        for arm in ["1u64", "2u64", "0u64"] {
            assert!(
                rs.contains(arm),
                "all three arm values must appear in the emitted code; missing {arm}:\n{rs}"
            );
        }
        assert!(
            !rs.contains("unsafe {") && !rs.contains("unsafe fn"),
            "the readable-Rust guarantee must survive the redex; got:\n{rs}"
        );
    }

    /// The Nat battery exercises BOTH arms of a zero/succ match.
    ///
    /// Same anti-vacuity property as the Bool one: if every battery point were
    /// non-zero, the zero arm would never run and an emitter that dropped it
    /// entirely would still pass.
    #[test]
    fn test_battery_straddles_a_nat_zero_succ_match() {
        let sig = GateSig {
            params: vec![ScalarTy::Nat],
            ret: ScalarTy::Nat,
        };
        let battery = build_battery(&sig);
        let has_zero = battery.iter().any(|t| t.first() == Some(&0));
        let has_succ = battery.iter().any(|t| t.first().is_some_and(|v| *v > 0));
        assert!(
            has_zero && has_succ,
            "the battery must exercise both the zero and successor arms; got {battery:?}"
        );
    }

    /// The battery DIVIDES BY ZERO, which is what makes total division
    /// checkable at all.
    ///
    /// Lean's `Nat.div`/`Nat.mod` are total (`n / 0 = 0`, `n % 0 = n`) while
    /// Rust and C both fault. If no battery point had a zero divisor, an
    /// emitter using a bare `/` would pass the differential and then fault in
    /// production — the worst possible outcome for a tool whose entire claim is
    /// that the artifact agrees with the kernel.
    ///
    /// The zipped battery pairs equal indices, so it only supplies `(0, 0)`;
    /// the CROSSED point (first param's last value against the others' first)
    /// is what supplies a nonzero numerator over a zero divisor. That crossed
    /// point is therefore load-bearing, not a nicety.
    #[test]
    fn test_battery_divides_by_zero() {
        let sig = GateSig {
            params: vec![ScalarTy::Nat, ScalarTy::Nat],
            ret: ScalarTy::Nat,
        };
        let battery = build_battery(&sig);
        assert!(
            battery.iter().any(|t| t.get(1) == Some(&0)),
            "some battery point must have a ZERO divisor: {battery:?}"
        );
        assert!(
            battery
                .iter()
                .any(|t| t.get(1) == Some(&0) && t.first().is_some_and(|n| *n != 0)),
            "and one must divide a NONZERO numerator by zero — `0 / 0` alone does \
             not distinguish `n / 0 = 0` from a fault: {battery:?}"
        );
    }

    /// `Nat.div`/`Nat.mod` extract with LEAN's total semantics on both lanes.
    ///
    /// Verified live, not just asserted: with the guard removed and a bare `/`
    /// emitted, the battery binary dies with `attempt to divide by zero` and the
    /// extraction FAILS. The wrong emission does not silently disagree — it
    /// faults, and the harness refuses to ship it.
    #[test]
    fn test_extract_total_div_mod_on_c_and_rust() {
        const SRC: &str = "\
def divn (a b : Nat) : Nat := Nat.div a b
def modn (a b : Nat) : Nat := Nat.mod a b
";
        for (decl, zero_case) in [("divn", "0u64"), ("modn", "__d2n")] {
            for backend in [ExtractBackend::C, ExtractBackend::Rust] {
                let tmp = tempfile::Builder::new()
                    .prefix("clean-extract-div-")
                    .tempdir()
                    .expect("scratch dir");
                let src_path = tmp.path().join("dv.lean");
                std::fs::write(&src_path, SRC).expect("write source");
                let out_dir = tmp.path().join("out");

                let args = ExtractArgs {
                    file: src_path,
                    decl: decl.to_string(),
                    out: out_dir.clone(),
                    backend,
                    keep_temp: false,
                };
                handle_extract_command(&args).unwrap_or_else(|e| {
                    panic!("`{decl}` must extract on the {backend:?} lane: {e}")
                });

                let manifest: serde_json::Value = serde_json::from_str(
                    &std::fs::read_to_string(out_dir.join("manifest.json")).expect("manifest"),
                )
                .expect("manifest is JSON");
                assert!(
                    manifest["differential"]
                        .as_str()
                        .is_some_and(|d| d.starts_with("PASSED")),
                    "{decl}/{backend:?}: the differential must PASS: {manifest}"
                );

                if backend == ExtractBackend::Rust {
                    let rs = std::fs::read_to_string(out_dir.join(format!("{decl}.rs")))
                        .expect("emitted rust");
                    assert!(
                        rs.contains("== 0"),
                        "{decl}: the zero-divisor guard IS the semantics, not \
                         defensive coding; got:\n{rs}"
                    );
                    assert!(
                        rs.contains(zero_case),
                        "{decl}: the zero case must yield `{zero_case}` — `n / 0 = 0` \
                         but `n % 0 = n`, and swapping them typechecks; got:\n{rs}"
                    );
                }
            }
        }
    }

    /// The recursion boundary: `Nat.rec` in, well-founded recursion OUT.
    ///
    /// This is the safety property behind admitting recursion at all.
    /// `Nat.rec` lowers to a counted loop whose bound is the scrutinee, so
    /// termination is inherited from the kernel — which accepted the source
    /// definition only because the recursor is well-founded — and is manifest in
    /// the artifact.
    ///
    /// `WellFounded.fix` / `Acc.rec` are different in kind: their termination
    /// rests on an accessibility proof that extraction ERASES. Emitting a loop
    /// for those would assert a bound the artifact does not carry. And the
    /// failure mode is the one this harness CANNOT report — a non-terminating
    /// extraction hangs the differential battery rather than failing it. So they
    /// must stay refused, and that is asserted here rather than assumed.
    #[test]
    fn test_recursion_boundary_admits_nat_rec_and_refuses_well_founded() {
        let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![]);
        assert!(
            find_recursion(&nat_rec).is_none(),
            "`Nat.rec` must be admitted — it lowers to a counted loop"
        );
        for refused in [
            "WellFounded.fix",
            "Acc.rec",
            "List.rec",
            "Nat.brecOn",
            "Nat.recOn",
        ] {
            let e = Expr::const_(Name::from_string(refused), vec![]);
            assert!(
                find_recursion(&e).is_some(),
                "`{refused}` must STILL refuse: its termination is not a counted \
                 bound the extracted artifact carries"
            );
        }
    }

    /// RECURSION end to end: a structurally recursive definition extracts on
    /// both lanes, and the Rust artifact is a BOUNDED LOOP.
    ///
    /// `sumTo` is genuinely recursive in source — `sumTo k` in its own body —
    /// and elaborates through `Nat.rec`.
    #[test]
    fn test_extract_structural_recursion_on_c_and_rust() {
        const SRC: &str = "\
def sumTo (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | k + 1 => Nat.add (sumTo k) (Nat.succ k)
";
        for backend in [ExtractBackend::C, ExtractBackend::Rust] {
            let tmp = tempfile::Builder::new()
                .prefix("clean-extract-rec-")
                .tempdir()
                .expect("scratch dir");
            let src_path = tmp.path().join("rec.lean");
            std::fs::write(&src_path, SRC).expect("write source");
            let out_dir = tmp.path().join("out");

            let args = ExtractArgs {
                file: src_path,
                decl: "sumTo".to_string(),
                out: out_dir.clone(),
                backend,
                keep_temp: false,
            };
            handle_extract_command(&args).unwrap_or_else(|e| {
                panic!("structural recursion must extract on the {backend:?} lane: {e}")
            });

            let manifest: serde_json::Value = serde_json::from_str(
                &std::fs::read_to_string(out_dir.join("manifest.json")).expect("manifest"),
            )
            .expect("manifest is JSON");
            assert!(
                manifest["differential"]
                    .as_str()
                    .is_some_and(|d| d.starts_with("PASSED")),
                "{backend:?}: the differential must PASS: {manifest}"
            );

            if backend == ExtractBackend::Rust {
                let rs = std::fs::read_to_string(out_dir.join("sumTo.rs")).expect("emitted rust");
                assert!(
                    rs.contains("while") && rs.contains("+= 1"),
                    "the artifact must be a COUNTED loop — the bound is what makes \
                     termination manifest; got:\n{rs}"
                );
                // Count `sumTo(` — a CALL — not the bare name, which also
                // appears in the generated header comment. Exactly one
                // occurrence is the definition itself.
                assert_eq!(
                    rs.matches("sumTo(").count(),
                    1,
                    "the emitted function must not call ITSELF: unbounded recursion \
                     would HANG the battery rather than fail it, and a hang is the \
                     one outcome this harness cannot report; got:\n{rs}"
                );
            }
        }
    }

    /// `==` extracts on both lanes, composing `ite` with `BEq.beq`.
    ///
    /// `if i == 0 then …` elaborates the condition through
    /// `instBEqOfDecidableEq Nat instDecidableEqNat` — the decide-wrapper whose
    /// `beq a b` is literally `decide (a = b)`. That IS structural equality, so
    /// it is emitted as Rust `==`; the emitted body is the readable
    /// `if (a == 0u64) { … }` chain.
    #[test]
    fn test_extract_beq_chain_on_c_and_rust() {
        const SRC: &str = "\
def stepC (i : Nat) : Nat :=
  if i == 0 then 1 else if i == 1 then 2 else 0
";
        for backend in [ExtractBackend::C, ExtractBackend::Rust] {
            let tmp = tempfile::Builder::new()
                .prefix("clean-extract-beq-")
                .tempdir()
                .expect("scratch dir");
            let src_path = tmp.path().join("beq.lean");
            std::fs::write(&src_path, SRC).expect("write source");
            let out_dir = tmp.path().join("out");
            let args = ExtractArgs {
                file: src_path,
                decl: "stepC".to_string(),
                out: out_dir.clone(),
                backend,
                keep_temp: false,
            };
            handle_extract_command(&args)
                .unwrap_or_else(|e| panic!("`==` must extract on the {backend:?} lane: {e}"));
            let manifest: serde_json::Value = serde_json::from_str(
                &std::fs::read_to_string(out_dir.join("manifest.json")).expect("manifest"),
            )
            .expect("manifest is JSON");
            assert!(
                manifest["differential"]
                    .as_str()
                    .is_some_and(|d| d.starts_with("PASSED")),
                "{backend:?}: the differential must PASS: {manifest}"
            );
            if backend == ExtractBackend::Rust {
                let rs = std::fs::read_to_string(out_dir.join("stepC.rs")).expect("emitted");
                assert!(
                    rs.contains("== 0u64") && rs.contains("== 1u64"),
                    "the canonical instance must emit as Rust `==`; got:\n{rs}"
                );
            }
        }
    }

    /// THE FAIL-CLOSED DIRECTION, which is the load-bearing part: a CUSTOM
    /// `BEq` instance must REFUSE, never be emitted as `==`.
    ///
    /// `weird` below says every pair of Nats is equal. Emitting Rust `==` for
    /// it would be a silently wrong program — and the differential battery
    /// would only catch it if a battery point happened to land on a
    /// disagreement, which is exactly the kind of luck a fail-closed emitter
    /// must not rely on.
    #[test]
    fn test_extract_beq_custom_instance_refuses() {
        const SRC: &str = "\
def weird : BEq Nat := BEq.mk (fun _ _ => true)
def bad (a b : Nat) : Bool := @BEq.beq Nat weird a b
";
        let tmp = tempfile::Builder::new()
            .prefix("clean-extract-beq-bad-")
            .tempdir()
            .expect("scratch dir");
        let src_path = tmp.path().join("bad.lean");
        std::fs::write(&src_path, SRC).expect("write source");
        let out_dir = tmp.path().join("out");
        let args = ExtractArgs {
            file: src_path,
            decl: "bad".to_string(),
            out: out_dir.clone(),
            backend: ExtractBackend::Rust,
            keep_temp: false,
        };
        let err = handle_extract_command(&args)
            .expect_err("a custom BEq instance must refuse on the Rust lane");
        assert!(
            err.to_string().contains("weird") || err.to_string().contains("instance"),
            "the refusal must name the non-canonical instance; got: {err}"
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
        // `Nat.succ` used to be the unlisted example; it is now emitted (the
        // recursion work needed it). `Nat.beq` is a real prelude constant that
        // the v1 Rust table genuinely does not carry.
        let env = env_with("def g (n : Nat) : Bool := Nat.beq n n");
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
             def looped (l : List Nat) : Nat := List.rec 0 (fun _ _ ih => ih) l",
        );
        assert!(
            matches!(
                extraction_gate(&env, &Name::from_string("trivial_imp")),
                Err(ExtractRefusal::Prop(_))
            ),
            "Prop telescope must refuse E_PROP"
        );
        // `Nat.rec` is now ADMITTED (it lowers to a counted loop), so the
        // recursion refusal is pinned with a recursor that is still out of
        // scope. Changed deliberately, not because the old case regressed.
        assert!(
            matches!(
                extraction_gate(&env, &Name::from_string("looped")),
                Err(ExtractRefusal::Recursion(_, _) | ExtractRefusal::TypeParam(_))
            ),
            "a non-Nat recursor must still refuse"
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

    /// REGRESSION (measured hang): the kernel leg at `UInt32 ==` over big
    /// literals.
    ///
    /// `equ (4294967295 : UInt32) 4294967295` elaborates its numerals as
    /// `UInt32.ofNat (@OfNat.ofNat Nat 4294967295 (instOfNatNat _))`. The
    /// `instDecidableEqUInt32` native reducer used to DECLINE that wrapper
    /// shape (it only read raw `Nat` literals), so whnf fell back to
    /// δι-grinding the structural `decEq` — Θ(2^32) unary work, a
    /// multi-minute hang sampled as a nested `try_iota_reduction` tower.
    /// Fixed by peeling the CANONICAL `OfNat` wrapper in
    /// `get_uint_ctor_val` (clean-kernel `native_reducers_uint.rs`), which
    /// this exercises through the production `kernel_eval` path.
    ///
    /// The worker thread + timeout converts a regression back into a LOUD
    /// failure instead of a silent test-suite hang.
    #[test]
    fn test_kernel_eval_uint32_eq_big_literals_terminates() {
        let (tx, rx) = std::sync::mpsc::channel();
        std::thread::spawn(move || {
            let env = env_with("def equ (a b : UInt32) : Bool := a == b");
            let sig = GateSig {
                params: vec![ScalarTy::UInt32, ScalarTy::UInt32],
                ret: ScalarTy::Bool,
            };
            let big = 4_294_967_295u64;
            let results: Vec<(Vec<u64>, String)> = [
                (vec![big, big], "1"),
                (vec![big, 0], "0"),
                (vec![0, big], "0"),
                (vec![4_294_967_290, big], "0"),
            ]
            .into_iter()
            .map(|(inputs, want)| {
                let got = kernel_eval(&env, "equ", &sig, &inputs)
                    .expect("kernel leg must reduce UInt32 == to a literal");
                (inputs, format!("{got} (want {want})"))
            })
            .collect();
            let _ = tx.send(results);
        });
        let results = rx.recv_timeout(std::time::Duration::from_secs(120)).expect(
            "kernel leg must terminate — a timeout here is the Θ(2^32) decEq grind regressing",
        );
        for (inputs, got_want) in results {
            let (got, want) = got_want.split_once(" (want ").expect("format");
            let want = want.trim_end_matches(')');
            assert_eq!(got, want, "kernel leg wrong at inputs {inputs:?}");
        }
    }

    /// The v1.2 TV leg: the C-lane manifest carries an explicit `tv` entry in
    /// EVERY build. Feature off: an honest `"unavailable"` note (an absent
    /// field would read as "nobody thought about it"). Feature on: the
    /// kernel-decided certificate status for the target decl —
    /// `"certified"`/`"skipped"`, never a silent omission — plus the scope
    /// wording that keeps the trust-ir claim separate from the shipped .c
    /// text (which only the differential covers).
    #[test]
    fn test_extract_c_manifest_carries_tv_entry() {
        let tmp = tempfile::Builder::new()
            .prefix("clean-extract-tv-")
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
        handle_extract_command(&args).expect("affineU extracts on the C lane");
        let manifest: serde_json::Value = serde_json::from_str(
            &std::fs::read_to_string(out_dir.join("manifest.json")).expect("manifest"),
        )
        .expect("manifest is JSON");
        let tv = &manifest["tv"];
        if cfg!(feature = "trust-ir-backend") {
            // THE PIN AT ITS FINAL FORM (measured 2026-08-25): `affineU`
            // CERTIFIES. The ladder it climbed, each rung measured: Dialect
            // lowering died `undefined function` (no runtime table) →
            // ExternCalls emitted but the compositional certificate could not
            // ground (`UInt32.add`/`mul` were compiled from source, shadowing
            // the emitter's native-BinOp arm) → the emitter now skips the
            // primitives (emit_wasm's discipline) so the root's arithmetic IS
            // native wrapping BinOps, squarely inside the Fragment-2/3
            // vocabulary, and the kernel-decided mint closes. Regressing any
            // rung turns this back into skipped/unattempted and fails here.
            assert_eq!(
                tv["status"], "certified",
                "feature-on affineU must carry the kernel-decided certificate: {tv}"
            );
            assert!(
                tv["closure_certified"]
                    .as_array()
                    .is_some_and(|c| c.iter().any(|n| n == "affineU")),
                "the certified list must name the root: {tv}"
            );
            assert!(
                tv["scope"]
                    .as_str()
                    .is_some_and(|s| s.contains("NOTHING about the shipped .c")),
                "the honest scope wording must survive: {tv}"
            );
        } else {
            assert_eq!(
                tv["status"], "unavailable",
                "feature-off builds must say so explicitly: {tv}"
            );
        }
    }

    /// The user-visible closure of the same gap: `UInt32 ==` extracts on BOTH
    /// lanes with the full battery — whose diagonal includes the exact
    /// measured-hang pair `(4294967295, 4294967295)` and whose crossed point
    /// supplies a mixed big/zero comparison.
    #[test]
    fn test_extract_uint32_eq_on_c_and_rust() {
        const SRC: &str = "def equ (a b : UInt32) : Bool := a == b\n";
        for backend in [ExtractBackend::C, ExtractBackend::Rust] {
            let tmp = tempfile::Builder::new()
                .prefix("clean-extract-equ-")
                .tempdir()
                .expect("scratch dir");
            let src_path = tmp.path().join("equ.lean");
            std::fs::write(&src_path, SRC).expect("write source");
            let out_dir = tmp.path().join("out");
            let args = ExtractArgs {
                file: src_path,
                decl: "equ".to_string(),
                out: out_dir.clone(),
                backend,
                keep_temp: false,
            };
            handle_extract_command(&args)
                .unwrap_or_else(|e| panic!("UInt32 == must extract on the {backend:?} lane: {e}"));
            let manifest: serde_json::Value = serde_json::from_str(
                &std::fs::read_to_string(out_dir.join("manifest.json")).expect("manifest"),
            )
            .expect("manifest is JSON");
            assert!(
                manifest["differential"]
                    .as_str()
                    .is_some_and(|d| d.starts_with("PASSED")),
                "{backend:?}: the differential must PASS: {manifest}"
            );
            if backend == ExtractBackend::Rust {
                let rs = std::fs::read_to_string(out_dir.join("equ.rs")).expect("emitted");
                assert!(
                    rs.contains("(a == b)"),
                    "UInt32 == must emit as Rust `==`; got:\n{rs}"
                );
            }
        }
    }
}

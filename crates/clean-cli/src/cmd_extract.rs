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
//!   kernel value with plain scalar signatures, compiled by the admitted Trust
//!   oracle compiler (`clean_elab::oracle_compiler`: the `trustc` beside the
//!   running `clean`, or `CLEAN_NATIVE_DECIDE_TRUSTC`); without one the lane
//!   refuses with `E_RUST_TOOLCHAIN`. See [`crate::extract_rust`].
//!
//! Honesty contract: the differential record is a CHECK over the battery,
//! not a proof; the manifest says so. Rocq's own Extraction ships neither.
//! Any refusal or mismatch exits nonzero and writes NOTHING.
//!
//! Every lane means the KERNEL value. The C, wasm and TV lanes lower through
//! `to_lcnf` at `clean_compiler::CodeMeaning::KernelValue`
//! (`clean_native::select_lcnf_decl_kernel_meaning`, then the pipeline at the
//! same meaning): no reference to an `@[implemented_by f]` declaration is
//! compiled as one to `f`, as compiled Lean's would be, and every constant
//! lowers its own value, so a closure that reaches one extracts its kernel
//! value, and so does a file with a late `attribute [implemented_by]` command
//! (`docs/DECISIONS.md` R149; before it, both were refused by name).

use std::path::Path;
use std::process::Command;

use anyhow::{bail, Context};
use clean_elab::oracle_compiler::{self, OracleCompiler};
use clean_kernel::{Environment, Expr, ExprKind, Name};

use crate::cli::{ExtractArgs, ExtractBackend};
use crate::extract_rust;
use clean_compiler::CodeMeaning;
use clean_native::compile::emit_decls;
use clean_native::native_build;
use clean_native::select_lcnf_decl_kernel_meaning;

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
    handle_extract_command_with(args, || {
        oracle_compiler::oracle_compiler().map_err(|why| {
            anyhow::anyhow!(
                "{}",
                extract_rust::RustEmitError::Toolchain(format!(
                    "the differential battery compiles only with an admitted Trust compiler: \
                     {why}. Run the `clean` that sits beside a Trust toolchain's `trustc`, or \
                     set {} to the compiler binary itself, `$(trustc --print sysroot)/bin/trustc` \
                     (a shim on PATH is a script and is refused; a `clean` built inside a Trust \
                     toolchain admits only that toolchain's own commit)",
                    oracle_compiler::TRUSTC_ENV
                ))
            )
        })
    })
}

/// [`handle_extract_command`] with the Rust backend's oracle compiler supplied
/// by `oracle`, which only the Rust backend calls.
fn handle_extract_command_with<'c>(
    args: &ExtractArgs,
    oracle: impl FnOnce() -> anyhow::Result<&'c OracleCompiler>,
) -> anyhow::Result<()> {
    match args.backend {
        ExtractBackend::C => handle_extract_c(args),
        ExtractBackend::Rust => handle_extract_rust(args, oracle()?),
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
/// KERNEL value, compile it with the admitted Trust oracle `compiler`, and hold
/// it to the same differential.
///
/// It deliberately does NOT go through the C emitter. That pipeline's output is
/// boxed `clean_obj*` against the Perceus runtime — correct for a runtime, and
/// not what "extract to a host language" means to a reader. See
/// [`crate::extract_rust`].
fn handle_extract_rust(args: &ExtractArgs, compiler: &OracleCompiler) -> anyhow::Result<()> {
    let decl_name = Name::from_string(&args.decl);

    // 1. Elaborate through the SAME front half the C lane uses.
    let env = elaborate_for_extraction(args)?;

    // 2. The shared extraction gate.
    let sig = extraction_gate(&env, &decl_name).map_err(|r| anyhow::anyhow!("{r}"))?;

    // 3. Emit. Any construct outside the v1 table refuses with an `E_RUST_*`.
    let module = extract_rust::emit_rust_module(&env, &decl_name, &sig)
        .map_err(|e| anyhow::anyhow!("{e}"))?;
    let fn_name = extract_rust::rust_fn_name(&args.decl).map_err(|e| anyhow::anyhow!("{e}"))?;

    // 4-6. Synthesize the battery driver, compile with the admitted `trustc`, run.
    let tmp = tempfile::Builder::new()
        .prefix("clean-extract-rust-")
        .tempdir()
        .context("create scratch dir")?;
    let build_dir = tmp.path().join("build");
    std::fs::create_dir_all(&build_dir)?;

    let battery = build_battery(&sig);
    let driver = extract_rust::render_rust_battery_driver(&fn_name, &sig, &battery);
    let native_results = extract_rust::run_rust_battery(compiler, &module, &driver, &build_dir)
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
    let (lcnf, env, pipeline) = select_lcnf_decl_kernel_meaning(&compile_args)?;
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
    let artifacts = clean_compiler::pass_manager::compile_lcnf_decls_for(
        &lcnf,
        &env,
        &pipeline,
        CodeMeaning::KernelValue,
    )
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
    let (lcnf, env, pipeline) = select_lcnf_decl_kernel_meaning(&compile_args)?;
    // The census/object-path config: `ExternCalls` carries the runtime ABI
    // import table, which is what lets `declare_extern_fallbacks` declare the
    // shim-dropped closure boundary (UInt32.toNat & co.) as typed extern
    // imports instead of dying `undefined function`. `Dialect` (the default)
    // has no runtime table, so emission failed on exactly those symbols.
    let emit_cfg = clean_compiler::emit_trust_ir::TrustIrConfig {
        runtime_lowering: clean_compiler::emit_trust_ir::RuntimeLowering::ExternCalls,
        ..clean_compiler::emit_trust_ir::TrustIrConfig::default()
    };
    let (_module, report) =
        match clean_compiler::pass_manager::compile_lcnf_to_trust_ir_with_report_for(
            &lcnf,
            &env,
            &pipeline,
            &emit_cfg,
            CodeMeaning::KernelValue,
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
        link_artifact: Vec::new(),
    }
}

/// Elaborate the source file, keeping only the ENVIRONMENT.
///
/// Both backends go through [`clean_native::compile::elaborate_file_to_env`] so
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
    clean_native::compile::elaborate_file_to_env(&args.file)
}

/// Reuse the `clean compile` closure/emitter for the C text.
fn select_and_emit(args: &ExtractArgs) -> anyhow::Result<(String, Environment)> {
    let compile_args = compile_args_for(args);
    let (lcnf, env, pipeline) = select_lcnf_decl_kernel_meaning(&compile_args)?;
    let c = emit_decls(
        &lcnf,
        &env,
        clean_compiler::cli::EmitFormat::C,
        &pipeline,
        Some(args.file.as_path()),
        CodeMeaning::KernelValue,
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
#[path = "cmd_extract_tests.rs"]
mod tests;

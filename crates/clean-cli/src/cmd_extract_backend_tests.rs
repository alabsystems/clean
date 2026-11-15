// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `cmd_extract` unit tests for the `--backend` flag, the Rust lane, the
//! extraction gate and the `UInt32` lanes. A child of `cmd_extract::tests`,
//! split out to keep each test file under the 1000-line paragon bound.

use super::*;

/// The `--backend` flag is actually WIRED to the clap surface, and `c`
/// remains the default so the existing C lane is untouched.
///
/// The e2e tests below call [`handle_extract_command_with`] directly — the
/// function `Commands::Extract` dispatches through, with this toolchain's
/// `trustc` supplied — which proves the pipeline but not the argument
/// plumbing. This closes that last gap without needing
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
    extract(&args).expect("the V1 pick must extract to Rust end to end");

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
    std::fs::write(&src_path, "def double (n : Nat) : Nat := Nat.add n n\n").expect("write source");
    let out_dir = tmp.path().join("out");

    extract(&ExtractArgs {
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
    let honest = extract_rust::run_rust_battery(toolchain_trustc(), &module, &driver, &honest_dir)
        .expect("the honest emission must build and run");
    assert_eq!(honest.len(), battery.len(), "one result per battery point");
    differential_check(&env, "affineU", &sig, &battery, &honest)
        .expect("the honest emission must pass the differential");

    // One operator, flipped. Still valid Rust; still compiles; wrong.
    let tampered = module.replace("wrapping_add", "wrapping_sub");
    assert_ne!(tampered, module, "the tamper must actually change the text");
    let tampered_dir = tmp.path().join("tampered");
    std::fs::create_dir_all(&tampered_dir).expect("mkdir");
    let bad = extract_rust::run_rust_battery(toolchain_trustc(), &tampered, &driver, &tampered_dir)
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
    let results = rx
        .recv_timeout(std::time::Duration::from_secs(120))
        .expect("kernel leg must terminate — a timeout here is the Θ(2^32) decEq grind regressing");
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
    extract(&args).expect("affineU extracts on the C lane");
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
        extract(&args)
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

#[path = "cmd_extract_implemented_by_tests.rs"]
mod implemented_by;

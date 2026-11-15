// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unit tests for `cmd_extract`, split out of `cmd_extract.rs` to keep that
//! file under the 1000-line paragon bound.

use super::*;

/// This toolchain's admitted `trustc`: the one beside `$CARGO` (Targo exports
/// it to tests), else beside the Targo that built this crate. The Rust-backend
/// tests need it, and fail -- never skip -- without one.
fn toolchain_trustc() -> &'static OracleCompiler {
    static TRUSTC: std::sync::OnceLock<OracleCompiler> = std::sync::OnceLock::new();
    TRUSTC.get_or_init(|| {
        let cargo = std::env::var_os("CARGO")
            .map_or_else(|| std::path::PathBuf::from(env!("CARGO")), Into::into);
        oracle_compiler::admit_beside(&cargo)
            .unwrap_or_else(|err| panic!("no admitted trustc beside {cargo:?}: {err}"))
    })
}

/// `clean extract` with this toolchain's `trustc` as the oracle compiler.
fn extract(args: &ExtractArgs) -> anyhow::Result<()> {
    handle_extract_command_with(args, || Ok(toolchain_trustc()))
}

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
    match extract(&args) {
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
    std::fs::write(&src_path, "def double (n : Nat) : Nat := Nat.add n n\n").expect("write source");
    let out_dir = tmp.path().join("out");

    let args = ExtractArgs {
        file: src_path,
        decl: "double".to_string(),
        out: out_dir.clone(),
        backend: ExtractBackend::Wasm,
        keep_temp: false,
    };
    let err = extract(&args).expect_err("a Nat signature must refuse");
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
    match extract(&args) {
        Ok(()) => {
            let wat = std::fs::read_to_string(out_dir.join("affineU.wat")).expect("emitted wat");
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
        extract(&args).unwrap_or_else(|e| panic!("`if` must extract on the {backend:?} lane: {e}"));

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
        extract(&args)
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
    extract(&args)
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
            extract(&args)
                .unwrap_or_else(|e| panic!("`{decl}` must extract on the {backend:?} lane: {e}"));

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
        extract(&args).unwrap_or_else(|e| {
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
        extract(&args).unwrap_or_else(|e| panic!("`==` must extract on the {backend:?} lane: {e}"));
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
    let err = extract(&args).expect_err("a custom BEq instance must refuse on the Rust lane");
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
    extract(&args).expect("the V1 pick must extract end to end");

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

// The `--backend` flag, the Rust lane, the extraction gate and the `UInt32`
// lanes: a child module, so every test keeps the `cmd_extract::tests::` prefix.
#[path = "cmd_extract_backend_tests.rs"]
mod backend;

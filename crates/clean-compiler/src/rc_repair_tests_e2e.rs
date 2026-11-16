// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! WS6.2 end to end: real Clean source through the full pipeline, emitted
//! as C, linked against the Clean runtime and executed (AddressSanitizer on
//! hosts that support it), plus the mutation control with the post-boxing
//! repair disabled. Split out of `rc_repair_tests.rs` (module path
//! unchanged: `rc_repair::tests::end_to_end`).

use super::super::e2e_support::{
    c_driver, compile_closure_of, compile_root, elaborated_env, elaborated_env_with, o0,
    off_by_one, EXPECTED, ROOTS, SHIMS_C,
};
use super::super::RcRepairMode;
use crate::emit_c::{emit_c_with_config, CEmitConfig};
use crate::pass_manager::PipelineConfig;
use clean_kernel::Environment;
use std::path::Path;
use std::process::Command;

fn cc() -> String {
    let cc = std::env::var("CC").unwrap_or_else(|_| "cc".to_string());
    let found = Command::new(&cc)
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false);
    assert!(
        found,
        "a C compiler is required by the WS6.2 C-backend run ({cc}); this test asserts \
             the executed values and must not skip silently"
    );
    cc
}

fn asan_supported(cc: &str, dir: &Path) -> bool {
    let src = dir.join("asan_probe.c");
    let bin = dir.join("asan_probe");
    std::fs::write(&src, "int main(void){return 0;}\n").expect("write asan probe");
    Command::new(cc)
        .arg("-fsanitize=address")
        .arg("-o")
        .arg(&bin)
        .arg(&src)
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

/// Emit C for the closure, link it with the embedded runtime, the shims
/// and the driver, run it, and return (stdout lines, whether ASan was on).
fn run_emitted_c(pipeline: &PipelineConfig) -> (Vec<String>, bool) {
    run_emitted_c_of(&elaborated_env(), ROOTS, &c_driver(), pipeline)
}

/// [`run_emitted_c`] for the closure of `roots` in `env`, run by `driver`.
pub(super) fn run_emitted_c_of(
    env: &Environment,
    roots: &[&str],
    driver: &str,
    pipeline: &PipelineConfig,
) -> (Vec<String>, bool) {
    let decls = compile_closure_of(env, pipeline, RcRepairMode::Enabled, roots)
        .expect("the repaired closure compiles and passes verify_rc_linearity");
    let emitted = emit_c_with_config(
        &decls,
        CEmitConfig {
            check_ir: true,
            ..CEmitConfig::default()
        },
    )
    .expect("emit C for the closure");
    let cc = cc();
    let dir = tempfile::tempdir().expect("tempdir");
    std::fs::write(
        dir.path().join("clean_runtime.h"),
        clean_runtime::runtime_header(),
    )
    .expect("write runtime header");
    std::fs::write(
        dir.path().join("clean_runtime.c"),
        clean_runtime::runtime_source().replacen(
            "../include/clean_runtime.h",
            "clean_runtime.h",
            1,
        ),
    )
    .expect("write runtime source");
    let program = dir.path().join("ws62.c");
    std::fs::write(
        &program,
        format!("#include <stdio.h>\n#include \"clean_runtime.h\"\n{SHIMS_C}\n{emitted}\n{driver}"),
    )
    .expect("write program");
    let binary = dir.path().join("ws62");
    let asan = asan_supported(&cc, dir.path());
    let mut compile = Command::new(&cc);
    if asan {
        compile
            .arg("-fsanitize=address")
            .arg("-fno-omit-frame-pointer");
    }
    let out = compile
        .arg("-std=c11")
        .arg("-g")
        .arg("-o")
        .arg(&binary)
        .arg(&program)
        .arg(dir.path().join("clean_runtime.c"))
        .arg("-I")
        .arg(dir.path())
        .arg("-lm")
        .output()
        .expect("spawn cc");
    assert!(
        out.status.success(),
        "cc failed:\n{}",
        String::from_utf8_lossy(&out.stderr)
    );
    let run = Command::new(&binary).output().expect("run the driver");
    assert!(
            run.status.success(),
            "the emitted program crashed or exited nonzero (asan={asan}): {:?}\nstdout:\n{}\nstderr:\n{}",
            run.status,
            String::from_utf8_lossy(&run.stdout),
            String::from_utf8_lossy(&run.stderr)
        );
    assert!(
        !String::from_utf8_lossy(&run.stderr).contains("AddressSanitizer"),
        "AddressSanitizer reported:\n{}",
        String::from_utf8_lossy(&run.stderr)
    );
    let lines = String::from_utf8_lossy(&run.stdout)
        .lines()
        .map(str::to_string)
        .collect();
    (lines, asan)
}

/// Positive fixture, C back end at `-O0` (`OptConfig::minimal`): the
/// kernel-certified values, with no SIGBUS and — where the host supports
/// it — an AddressSanitizer-clean run. Negative twin: the off-by-one
/// expectation is rejected.
#[test]
fn emit_c_sqlet_and_twice_apply_run_linear_at_o0() {
    let (lines, asan) = run_emitted_c(&o0());
    assert_eq!(
        lines, EXPECTED,
        "wrong values from the C back end (asan={asan})"
    );
    assert_ne!(lines, off_by_one(), "the off-by-one twin must be rejected");
    if cfg!(target_os = "macos") {
        assert!(asan, "the macOS host toolchain supports -fsanitize=address");
    }
}

/// The same program through the default (`-O1`) pipeline, which also runs
/// reset/reuse expansion.
#[test]
fn emit_c_sqlet_and_twice_apply_run_linear_at_default_opt() {
    let (lines, _) = run_emitted_c(&PipelineConfig::default());
    assert_eq!(lines, EXPECTED);
}

/// Mutation control: with `rc_repair_boxed` disabled, the verifier
/// refuses BOTH programs at compile time with the named error — the
/// regression becomes a compile error instead of a double release.
/// With the repair on, the same roots compile.
///
/// At `-O1` and `-O2` WS6.4 resolves the known `HAdd`/`HMul` instances to
/// native `UInt64.add`/`UInt64.mul`, so `t` is a scalar and neither body
/// passes one owned object twice any more: `sqLet` holds no object at all
/// ([`sqlet_holds_no_object_once_instances_resolve`]), and `twiceApply` —
/// whose `f` is a runtime closure and stays generic — boxes `t` once per
/// use. Compiled on its own (the per-declaration probe, where `UInt64.add`
/// is an extern taking boxed operands) it is still REFUSED without the
/// repair, now for the boxing temporaries' leak, which pins that the repair
/// stays load-bearing at every level.
#[test]
fn rc_repair_disabled_refuses_sqlet_and_twice_apply_at_compile_time() {
    const DOUBLE_CONSUME: &str = "is consumed 2 times with 0 incs on path entry";
    const TEMP_LEAK: &str = "is consumed 0 times with 0 incs on path entry: \
                             1 reference(s) never released at return";
    let env = elaborated_env();
    let aggressive = PipelineConfig {
        opt: crate::opt::OptConfig::aggressive(),
        rc: crate::rc::RCConfig::aggressive(),
        boxing: crate::boxing::BoxingConfig::default(),
    };
    for (pipeline, rows) in [
        (
            o0(),
            &[("sqLet", DOUBLE_CONSUME), ("twiceApply", DOUBLE_CONSUME)][..],
        ),
        (PipelineConfig::default(), &[("twiceApply", TEMP_LEAK)][..]),
        (aggressive, &[("twiceApply", TEMP_LEAK)][..]),
    ] {
        for &(root, reason) in rows {
            let err = compile_root(&env, root, &pipeline, RcRepairMode::Disabled)
                .expect_err("an unrepaired body must be refused")
                .to_string();
            assert!(
                err.contains(&format!("RC linearity violation in {root}: object %"))
                    && err.contains(reason),
                "{root}: {err}"
            );
            compile_root(&env, root, &pipeline, RcRepairMode::Enabled)
                .unwrap_or_else(|e| panic!("{root} must compile with the repair: {e}"));
        }
    }
}

/// WS6.4: once `sqLet`'s instances resolve (`-O1`, `-O2`), its compiled body
/// in the `clean compile` closure is straight-line scalar `UInt64`
/// arithmetic — no object variable, no `inc`/`dec`, nothing for the RC
/// repair to fix. At `-O0` (no resolution) the double consume is still there
/// and refused, which is the control above.
#[test]
fn sqlet_holds_no_object_once_instances_resolve() {
    use crate::ir::{IRBody, IRType};
    fn scalar_straight_line(body: &IRBody) -> bool {
        match body {
            IRBody::VDecl { ty, rest, .. } => *ty != IRType::Object && scalar_straight_line(rest),
            IRBody::Ret(_) => true,
            _ => false,
        }
    }
    let env = elaborated_env();
    let aggressive = PipelineConfig {
        opt: crate::opt::OptConfig::aggressive(),
        rc: crate::rc::RCConfig::aggressive(),
        boxing: crate::boxing::BoxingConfig::default(),
    };
    for pipeline in [PipelineConfig::default(), aggressive] {
        let decls = compile_closure_of(&env, &pipeline, RcRepairMode::Enabled, &["sqLet"])
            .expect("the sqLet closure compiles");
        let sq = decls
            .iter()
            .find(|d| d.name.to_string() == "sqLet")
            .expect("sqLet is compiled");
        assert!(
            scalar_straight_line(&sq.body),
            "sqLet must hold no object once its instances resolve: {:#?}",
            sq.body
        );
    }
    // Control: at `-O0` the same closure's `sqLet` does hold objects.
    let decls = compile_closure_of(&env, &o0(), RcRepairMode::Enabled, &["sqLet"])
        .expect("the sqLet closure compiles at -O0");
    let sq = decls
        .iter()
        .find(|d| d.name.to_string() == "sqLet")
        .expect("sqLet is compiled");
    assert!(
        !scalar_straight_line(&sq.body),
        "-O0 must keep the boxed path"
    );
}
/// Adversarial (review): the repaired object is live into a `case` and
/// used DIFFERENTLY per arm — consumed twice in one arm, released unused
/// (`branchSq`) or returned through an unbox (`branchApply`) in the
/// other — and it is itself the result of a closure call. The repair has
/// to place the `inc` in one arm only and the release at the head of the
/// other; the heap values (`>= 2^63`) make a misplaced release a real
/// use-after-free under ASan, not a benign tagged-immediate no-op.
const BRANCH_SOURCE: &str = "def branchSq (b : Bool) (a : UInt64) : UInt64 := \
        let t := a + 1; match b with | true => t * t | false => 5\n\
        def branchApply (f : UInt64 → UInt64 → UInt64) (b : Bool) (a : UInt64) : UInt64 := \
        let t := f a a; match b with | true => f t t | false => t\n";

const BRANCH_ROOTS: &[&str] = &["branchSq", "branchApply", "instHMulUInt64"];

const BRANCH_DRIVER: &str = r#"
#include <inttypes.h>
int main(void) {
  printf("%" PRIu64 "\n", l_branchSq(1, 3));
  printf("%" PRIu64 "\n", l_branchSq(0, 3));
  printf("%" PRIu64 "\n", l_branchSq(1, 18446744073709551615ull));
  printf("%" PRIu64 "\n", l_branchSq(0, 18446744073709551615ull));
  printf("%" PRIu64 "\n", l_branchApply(l_instHMulUInt64(), 1, 3));
  printf("%" PRIu64 "\n", l_branchApply(l_instHMulUInt64(), 0, 3));
  printf("%" PRIu64 "\n", l_branchApply(l_instHMulUInt64(), 1, 3037000500ull));
  printf("%" PRIu64 "\n", l_branchApply(l_instHMulUInt64(), 0, 3037000500ull));
  return 0;
}
"#;

/// `(a+1)^2`, `5`, `0` (wraps), `5`; `(a*a)^2`, `a*a` — with
/// `3037000500^2 = 9223372037000250000 >= 2^63` a HEAP cell.
const BRANCH_EXPECTED: &[&str] = &[
    "16",
    "5",
    "0",
    "5",
    "81",
    "9",
    "21162740538052864",
    "9223372037000250000",
];

#[test]
fn emit_c_branching_repaired_objects_run_linear() {
    let env = elaborated_env_with(BRANCH_SOURCE);
    for pipeline in [o0(), PipelineConfig::default()] {
        let (lines, asan) = run_emitted_c_of(&env, BRANCH_ROOTS, BRANCH_DRIVER, &pipeline);
        assert_eq!(lines, BRANCH_EXPECTED, "wrong values (asan={asan})");
        // Negative twin: a one-off expectation is rejected.
        let mut twin: Vec<String> = BRANCH_EXPECTED.iter().map(|s| s.to_string()).collect();
        twin[1] = "6".to_string();
        assert_ne!(lines, twin, "the off-by-one twin must be rejected");
    }
    // Mutation control: without the repair the branch-local double
    // consume is refused at compile time, by name.
    for root in ["branchSq", "branchApply"] {
        let err = compile_root(&env, root, &o0(), RcRepairMode::Disabled)
            .expect_err("an unrepaired branch must be refused")
            .to_string();
        assert!(
            err.contains(&format!("RC linearity violation in {root}: object %")),
            "{root}: {err}"
        );
    }
}

// ── Second review (adversarial): repaired objects in other positions ──────

/// Repaired (LCNF-scalar, object-represented) values reaching positions the
/// first fixtures did not: CAPTURED by a closure and used twice inside it,
/// STORED twice in a structure whose fields are then projected, carried
/// through a structurally recursive accumulator, and wrapped in an `Option`
/// that is matched and used twice. Heap values (`>= 2^63`) make a misplaced
/// release a real use-after-free under ASan.
const REVIEW_SOURCE: &str = "def capt (a : UInt64) : UInt64 → UInt64 := let t := a + 1; fun x => x * t + t\n\
        def useCapt (a b : UInt64) : UInt64 := let f := capt a; f b + f b\n\
        def pairT (a : UInt64) : UInt64 × UInt64 := let t := a + 1; (t, t)\n\
        def usePair (a : UInt64) : UInt64 := let p := pairT a; p.1 * p.2\n\
        def optT (a : UInt64) : Option UInt64 := let t := a + 1; if t == 0 then none else some (t * t)\n\
        def useOpt (a : UInt64) : UInt64 := match optT a with | some v => v + v | none => 7\n";

const REVIEW_ROOTS: &[&str] = &["useCapt", "usePair", "useOpt"];

const REVIEW_DRIVER: &str = r#"
#include <inttypes.h>
int main(void) {
  printf("%" PRIu64 "\n", l_useCapt(3, 5));
  printf("%" PRIu64 "\n", l_useCapt(9223372036854775807ull, 1));
  printf("%" PRIu64 "\n", l_usePair(3));
  printf("%" PRIu64 "\n", l_usePair(9223372036854775807ull));
  printf("%" PRIu64 "\n", l_useOpt(3));
  printf("%" PRIu64 "\n", l_useOpt(18446744073709551615ull));
  printf("%" PRIu64 "\n", l_useOpt(9223372036854775807ull));
  return 0;
}
"#;

/// `2*(5*4+4)`, `2*(1*2^63+2^63) mod 2^64`, `4*4`, `2^63*2^63 mod 2^64`,
/// `2*16`, `7` (t wraps to 0), `2*(2^63)^2 mod 2^64`.
const REVIEW_EXPECTED: &[&str] = &["48", "0", "16", "0", "32", "7", "0"];

#[test]
fn emit_c_repaired_objects_captured_stored_and_wrapped_run_linear() {
    let env = elaborated_env_with(REVIEW_SOURCE);
    for pipeline in [o0(), PipelineConfig::default()] {
        let (lines, asan) = run_emitted_c_of(&env, REVIEW_ROOTS, REVIEW_DRIVER, &pipeline);
        assert_eq!(lines, REVIEW_EXPECTED, "wrong values (asan={asan})");
        let mut twin: Vec<String> = REVIEW_EXPECTED.iter().map(|s| s.to_string()).collect();
        twin[0] = "49".to_string();
        assert_ne!(lines, twin, "the off-by-one twin must be rejected");
    }
    // Mutation control: every one of these roots (the closure-lifted `capt`
    // body aside, which holds no unmanaged object) needs the repair — without
    // it each is refused by name, as a duplicate store / call (`pairT`,
    // `optT`) or a leaked product (`useCapt`, `usePair`, `useOpt`).
    for root in ["useCapt", "pairT", "usePair", "optT", "useOpt"] {
        let err = compile_root(&env, root, &o0(), RcRepairMode::Disabled)
            .expect_err("an unrepaired object must be refused")
            .to_string();
        assert!(
            err.contains(&format!("RC linearity violation in {root}: object %")),
            "{root}: {err}"
        );
    }
}

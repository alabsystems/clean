// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! WS6.3 — the `mask` crash (F-105): `Nat`/`UInt` bitwise ops get executable
//! implementations. A child of `emit_trust_ir::tests`, so the
//! `trust-ir-backend-lib` gate leg (`-- emit_trust_ir`) runs it.
//!
//! The confirmed cause (`postmortems/2026-09-18-ws6-3-mask-crash.md`): the
//! prelude's `Nat.land`/`Nat.lor`/`Nat.xor` are `Nat.bitwise f m n ≡
//! Nat.bitwiseAux f (m + n) m n`, a proof-oriented definition with UNARY fuel
//! `m + n` and no early stop. Compiled from source for execution it recurses
//! one level per unit of fuel, so a heap input (≥ 2^63) needs ~2^64 stack
//! frames and dies on the guard page (SIGSEGV on the main thread, SIGBUS on a
//! pthread) through BOTH backends — operational non-termination of a correct
//! denotation, not memory corruption. The fix is (2a) runtime shims
//! `clean_nat_land/lor/xor` on the prelude shim table, so the source body is
//! never compiled, and (2b) native `and`/`or` for `UInt{8,16,32,64}.land/lor`
//! in the trust-ir backend.

use super::*;

/// The kernel-built roots:
///
/// ```text
/// def mask    (a b : UInt64) : UInt64 := UInt64.lor (UInt64.land a b) 1
/// def natMask (a b : Nat)    : Nat    := Nat.lor (Nat.land a b) 1
/// ```
///
/// `mask` is the proof program's `p15_bitwise` root with the instance
/// dispatch resolved (`(a &&& b) ||| 1`); the elaborated source itself is the
/// clean-cli battery's `GENERAL.p15_bitwise.mask.linkrun` row. `natMask` is
/// the mutation control: it reaches `Nat.land`/`Nat.lor` directly, so it
/// passes only through fix (2a), never through (2b).
const WS6_3_ROOTS: [&str; 2] = ["mask", "natMask"];

/// The prelude `Nat` primitives the runtime shims AFTER WS6.3: WS6.1's list
/// plus the three bitwise ops (clean-cli `NAT_PRELUDE_SHIMS`).
const WS6_3_NAT_SHIMMED: &[&str] = &[
    "Nat.add",
    "Nat.mul",
    "Nat.sub",
    "Nat.div",
    "Nat.mod",
    "Nat.decEq",
    "Nat.shiftRight",
    "Nat.ble",
    "Nat.blt",
    "Nat.beq",
    "Nat.land",
    "Nat.lor",
    "Nat.xor",
];

/// The C shims for [`WS6_3_NAT_SHIMMED`] — WS6.1's text plus the bitwise
/// three, each exactly the clean-cli `NAT_PRELUDE_SHIMS` body.
fn ws6_3_nat_shims_c() -> String {
    format!(
        "{WS6_1_NAT_SHIMS_C}\
clean_obj* l_Nat_land(clean_obj* a, clean_obj* b) {{ return clean_nat_land(a, b); }}
clean_obj* l_Nat_lor(clean_obj* a, clean_obj* b) {{ return clean_nat_lor(a, b); }}
clean_obj* l_Nat_xor(clean_obj* a, clean_obj* b) {{ return clean_nat_xor(a, b); }}
"
    )
}

/// `UInt64.ofNat n` as a kernel term.
fn ws6_3_u64(n: u64) -> clean_kernel::Expr {
    clean_kernel::Expr::app(
        clean_kernel::Expr::const_str("UInt64.ofNat"),
        clean_kernel::Expr::nat_lit(n),
    )
}

/// `theorem <name> : <lhs> = <rhs> := rfl` at type `ty`.
fn ws6_3_rfl(
    name: &str,
    ty: clean_kernel::Expr,
    lhs: clean_kernel::Expr,
    rhs: clean_kernel::Expr,
) -> clean_kernel::env::Declaration {
    use clean_kernel::{Expr as KExpr, Level};
    let lvl = vec![Level::succ(Level::zero())];
    clean_kernel::env::Declaration::Theorem {
        name: Name::from_string(name),
        level_params: vec![],
        type_: KExpr::apps(
            KExpr::const_(Name::from_string("Eq"), lvl.clone()),
            [ty.clone(), lhs, rhs.clone()],
        ),
        value: KExpr::apps(KExpr::const_(Name::from_string("Eq.refl"), lvl), [ty, rhs]),
    }
}

/// `mask`'s vectors `(a, b, mask a b)`: the proof program's three
/// (`parta-lean/run.py`) plus the heap pair the spec adds.
const WS6_3_MASK_VECTORS: [(u64, u64, u64); 4] = [
    (12, 10, 9),
    (u64::MAX, u64::MAX - 1, u64::MAX),
    (0, 0, 1),
    ((1 << 63) + 5, (1 << 63) + 3, (1 << 63) + 1),
];

/// `natMask`'s heap vectors (every input ≥ 2^63, so the source body's fuel
/// `a + b` is ≥ 2^64) and one tagged control.
const WS6_3_NATMASK_VECTORS: [(u64, u64, u64); 3] = [
    ((1 << 63) + 5, (1 << 63) + 3, (1 << 63) + 1),
    (u64::MAX, (1 << 63) + 6, (1 << 63) + 7),
    (6, 3, 3),
];

/// The prelude plus [`WS6_3_ROOTS`] as kernel-checked definitions. Every
/// vector is certified by `rfl` (so the native expectations are the
/// kernel's), and each vector off by one is REFUSED, so the certification is
/// not vacuous.
fn ws6_3_env() -> clean_kernel::Environment {
    use clean_kernel::env::Declaration;
    use clean_kernel::{BinderInfo, Environment, Expr as KExpr};
    let mut env = Environment::try_with_prelude().expect("prelude environment");
    let u64t = KExpr::const_str("UInt64");
    let nat = KExpr::const_str("Nat");
    let bin = |t: &KExpr, body: KExpr| {
        KExpr::lam(
            BinderInfo::Default,
            t.clone(),
            KExpr::lam(BinderInfo::Default, t.clone(), body),
        )
    };
    let arrow2 = |t: &KExpr| KExpr::arrow(t.clone(), KExpr::arrow(t.clone(), t.clone()));
    let masked = |land: &str, lor: &str, one: KExpr| {
        KExpr::apps(
            KExpr::const_str(lor),
            [
                KExpr::apps(KExpr::const_str(land), [KExpr::bvar(1), KExpr::bvar(0)]),
                one,
            ],
        )
    };
    for (name, ty, value) in [
        (
            "mask",
            &u64t,
            bin(&u64t, masked("UInt64.land", "UInt64.lor", ws6_3_u64(1))),
        ),
        (
            "natMask",
            &nat,
            bin(&nat, masked("Nat.land", "Nat.lor", KExpr::nat_lit(1))),
        ),
    ] {
        env.add_decl(Declaration::Definition {
            name: Name::from_string(name),
            level_params: vec![],
            type_: arrow2(ty),
            value,
            is_reducible: true,
        })
        .unwrap_or_else(|e| panic!("{name} kernel-checks against the prelude: {e:?}"));
    }
    let certify = |env: &mut Environment,
                   root: &str,
                   ty: &KExpr,
                   lit: &dyn Fn(u64) -> KExpr,
                   v: (u64, u64, u64),
                   i: usize| {
        let (a, b, r) = v;
        let lhs = KExpr::apps(KExpr::const_str(root), [lit(a), lit(b)]);
        let wrong = r.wrapping_add(1);
        assert!(
            env.add_decl(ws6_3_rfl(
                &format!("ws6_3_{root}_off_by_one_{i}"),
                ty.clone(),
                lhs.clone(),
                lit(wrong)
            ))
            .is_err(),
            "the kernel must REFUSE `{root} {a} {b} = {wrong}`"
        );
        env.add_decl(ws6_3_rfl(
            &format!("ws6_3_{root}_vector_{i}"),
            ty.clone(),
            lhs,
            lit(r),
        ))
        .unwrap_or_else(|e| panic!("the kernel must certify `{root} {a} {b} = {r}`: {e:?}"));
    };
    for (i, v) in WS6_3_MASK_VECTORS.into_iter().enumerate() {
        certify(&mut env, "mask", &u64t, &ws6_3_u64, v, i);
    }
    for (i, v) in WS6_3_NATMASK_VECTORS.into_iter().enumerate() {
        certify(&mut env, "natMask", &nat, &KExpr::nat_lit, v, i);
    }
    env
}

/// The roots' closure (shimming `shimmed`) through the real pipeline.
fn ws6_3_artifacts(
    env: &clean_kernel::Environment,
    shimmed: &[&str],
) -> crate::pass_manager::PipelineArtifacts {
    use crate::pass_manager::{compile_lcnf_decls, PipelineConfig};
    let decls = ws6_1_closure_shimming(env, &WS6_3_ROOTS, shimmed);
    compile_lcnf_decls(&decls, env, &PipelineConfig::default())
        .expect("the WS6.3 closure compiles through the real pipeline")
}

/// The driver: `argv = <root: mask|natMask> <a> <b> <stack KiB>`. It runs the
/// root on a thread of exactly that stack size (so the step-1 stack scaling
/// is a parameter, not a shell limit) and prints the result in decimal.
///
/// The reverted-closure controls overflow that thread's stack ON PURPOSE (the
/// guard page: SIGBUS on a pthread, SIGSEGV on the main thread). The driver
/// catches both on an alternate signal stack and ends with `_exit(
/// WS6_3_FAULT_STATUS_BASE + signal)` ([`Ws63Outcome::StackFault`]): a process
/// killed by a crash signal makes macOS write a crash report on every run
/// (8 to 14 per run of this module, measured 2026-10-17 and 18), and
/// docs/DECISIONS.md R86 rules them out.
const WS6_3_DRIVER_MAIN: &str = r#"
#include <pthread.h>
#include <signal.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
/* The guard-page fault ends the driver with 100 + signal, never a crash
   signal; `_exit` is async-signal-safe. */
static void ws_fault(int sig) { _exit(100 + sig); }
static char ws_altstack[1 << 17];
struct ws_job { int nat; unsigned __int128 a, b; char out[64]; };
static unsigned __int128 ws_parse(const char* s) {
  unsigned __int128 v = 0;
  for (; *s; s++) { v = v * 10 + (unsigned)(*s - '0'); }
  return v;
}
static void ws_fmt(unsigned __int128 v, char* out) {
  char buf[64]; int i = 63; buf[i] = 0;
  if (v == 0) { buf[--i] = '0'; }
  while (v > 0) { buf[--i] = (char)('0' + (unsigned)(v % 10)); v /= 10; }
  strcpy(out, buf + i);
}
static void* ws_run(void* p) {
  struct ws_job* j = (struct ws_job*)p;
  /* The handler runs on this thread's alternate stack: its own is exhausted. */
  stack_t ss;
  memset(&ss, 0, sizeof ss);
  ss.ss_sp = ws_altstack;
  ss.ss_size = sizeof ws_altstack;
  if (sigaltstack(&ss, 0) != 0) { _exit(4); }
  if (j->nat) {
    clean_obj* r = ws_natmask(clean_nat_of_u128(j->a), clean_nat_of_u128(j->b));
    ws_fmt(clean_nat_to_u128(r), j->out);
  } else {
    ws_fmt((unsigned __int128)ws_mask((uint64_t)j->a, (uint64_t)j->b), j->out);
  }
  return 0;
}
int main(int argc, char** argv) {
  if (argc != 5) { return 2; }
  struct sigaction sa;
  memset(&sa, 0, sizeof sa);
  sa.sa_handler = ws_fault;
  sa.sa_flags = SA_ONSTACK;
  sigemptyset(&sa.sa_mask);
  if (sigaction(SIGSEGV, &sa, 0) != 0 || sigaction(SIGBUS, &sa, 0) != 0) { return 4; }
  struct ws_job j;
  memset(&j, 0, sizeof j);
  j.nat = strcmp(argv[1], "natMask") == 0;
  j.a = ws_parse(argv[2]);
  j.b = ws_parse(argv[3]);
  pthread_attr_t attr;
  pthread_attr_init(&attr);
  pthread_attr_setstacksize(&attr, (size_t)strtoull(argv[4], 0, 10) * 1024);
  pthread_t t;
  if (pthread_create(&t, &attr, ws_run, &j) != 0) { return 3; }
  pthread_join(t, 0);
  printf("%s\n", j.out);
  return 0;
}
"#;

/// Compile C sources (plus the runtime and `objects`) into one binary.
fn ws6_3_link(
    dir: &std::path::Path,
    label: &str,
    c_sources: &[(&str, String)],
    objects: &[&std::path::Path],
    arch: &str,
) -> std::path::PathBuf {
    let rt_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../clean-runtime");
    let bin = dir.join(format!("{label}_bin"));
    let mut cc = std::process::Command::new("cc");
    add_host_arch_link_arg(&mut cc, arch);
    cc.args(["-O0", "-I"])
        .arg(rt_dir.join("include"))
        .arg("-o")
        .arg(&bin);
    for (name, text) in c_sources {
        let path = dir.join(format!("{label}_{name}"));
        std::fs::write(&path, text).expect("write C source");
        cc.arg(path);
    }
    cc.arg(rt_dir.join("src/clean_runtime.c"));
    for obj in objects {
        cc.arg(obj);
    }
    cc.arg("-lpthread");
    let out = cc.output().expect("spawn cc");
    assert!(
        out.status.success(),
        "{label}: cc failed:\n{}",
        String::from_utf8_lossy(&out.stderr)
    );
    bin
}

/// `--emit c` lane binary.
fn ws6_3_build_c(
    c_code: &str,
    shims: &str,
    dir: &std::path::Path,
    label: &str,
    arch: &str,
) -> std::path::PathBuf {
    let m = |s: &str| crate::mangle::mangle_name(&Name::from_string(s));
    let tu = format!(
        "#include <stdio.h>\n#include <stdint.h>\n#include \"clean_runtime.h\"\n{shims}\n{c_code}\n\
         static uint64_t ws_mask(uint64_t a, uint64_t b) {{ return {}(a, b); }}\n\
         static clean_obj* ws_natmask(clean_obj* a, clean_obj* b) {{ return {}(a, b); }}\n\
         {WS6_3_DRIVER_MAIN}",
        m("mask"),
        m("natMask"),
    );
    launch::ws6_3_launched_driver(ws6_3_link(dir, label, &[("tu.c", tu)], &[], arch), label)
}

/// trust-ir -> trust-cg lane binary, in the EXPERIMENT (license-stripped)
/// fixture (the producer's `Ungated` refusal is checked first).
fn ws6_3_build_trust_ir(
    module: &Module,
    trust_cg: &std::path::Path,
    shims: &str,
    dir: &std::path::Path,
    label: &str,
    (target, arch): (&str, &str),
) -> std::path::PathBuf {
    let tmbc = dir.join(format!("{label}.tmbc"));
    let obj = dir.join(format!("{label}.o"));
    write_legacy_native_fixture(module, trust_cg, target, &tmbc);
    let cg = legacy_trust_cg(trust_cg)
        .args(["-c", "--target", target, "-o"])
        .arg(&obj)
        .arg(&tmbc)
        .output()
        .expect("spawn trust-cg");
    assert!(
        cg.status.success(),
        "{label}: trust-cg failed: {}",
        String::from_utf8_lossy(&cg.stderr)
    );
    let p = if cfg!(target_os = "macos") { "_" } else { "" };
    let driver = format!(
        "#include <stdio.h>\n#include <stdint.h>\n#include \"clean_runtime.h\"\n\
         extern uint64_t ws_mask(uint64_t, uint64_t) __asm__(\"{p}mask\");\n\
         extern clean_obj* ws_natmask(clean_obj*, clean_obj*) __asm__(\"{p}natMask\");\n\
         {WS6_3_DRIVER_MAIN}"
    );
    let rt_extern = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../clean-runtime/src/runtime_extern.c");
    let rt_extern = std::fs::read_to_string(rt_extern).expect("read runtime_extern.c");
    let shims = format!("#include \"clean_runtime.h\"\n{shims}");
    let bin = ws6_3_link(
        dir,
        label,
        &[
            ("driver.c", driver),
            ("shims.c", shims),
            ("runtime_extern.c", rt_extern),
        ],
        &[&obj],
        arch,
    );
    launch::ws6_3_launched_driver(bin, label)
}

/// The driver's guard-page handler ends it with this plus the signal number
/// (`ws_fault` in [`WS6_3_DRIVER_MAIN`]).
const WS6_3_FAULT_STATUS_BASE: i32 = 100;

/// `SIGSEGV` (11 on macOS and Linux): a guard-page fault on the main thread,
/// and on a Linux pthread.
const WS6_3_SIGSEGV: i32 = 11;

/// `SIGBUS` (10 on macOS, 7 on Linux): a guard-page fault on a macOS pthread.
const WS6_3_SIGBUS: i32 = if cfg!(target_os = "linux") { 7 } else { 10 };

/// How one driver process ended.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Ws63Outcome {
    /// Exited 0 and printed this value.
    Value(String),
    /// The root faulted on this signal (SIGSEGV or SIGBUS: the stack guard
    /// page) and the driver's handler ended it with
    /// `WS6_3_FAULT_STATUS_BASE + signal`.
    StackFault(i32),
    /// Killed by this signal: nothing the driver caught. A crash signal here
    /// (the handler did not run) is a crash report, never a stack fault.
    Signal(i32),
    /// Still running at the wall bound (killed by the harness).
    Timeout,
    /// Exited nonzero without a signal.
    Exit(i32),
}

/// Run `bin root a b stack_kib`, one process per vector, bounded by `wall`.
/// `bin` must already have passed [`launch::ws6_3_first_launch`]; a vector on
/// a never-launched driver panics instead of timing the OS's assessment.
fn ws6_3_run(
    bin: &std::path::Path,
    root: &str,
    (a, b): (u64, u64),
    stack_kib: u64,
    wall: std::time::Duration,
) -> Ws63Outcome {
    launch::ws6_3_require_first_launched(bin);
    ws6_3_exec(
        bin,
        &[
            root.to_string(),
            a.to_string(),
            b.to_string(),
            stack_kib.to_string(),
        ],
        wall,
    )
}

/// Run `bin args`, bounded by `wall`, and classify how it ended.
fn ws6_3_exec(bin: &std::path::Path, args: &[String], wall: std::time::Duration) -> Ws63Outcome {
    use std::os::unix::process::ExitStatusExt;
    let mut child = std::process::Command::new(bin)
        .args(args)
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::null())
        .spawn()
        .expect("spawn the WS6.3 driver");
    let start = std::time::Instant::now();
    let status = loop {
        if let Some(status) = child.try_wait().expect("poll the WS6.3 driver") {
            break status;
        }
        if start.elapsed() >= wall {
            let _ = child.kill();
            let _ = child.wait();
            return Ws63Outcome::Timeout;
        }
        std::thread::sleep(std::time::Duration::from_millis(10));
    };
    if let Some(sig) = status.signal() {
        return Ws63Outcome::Signal(sig);
    }
    if !status.success() {
        let code = status.code().unwrap_or(-1);
        return match code - WS6_3_FAULT_STATUS_BASE {
            sig @ (WS6_3_SIGSEGV | WS6_3_SIGBUS) => Ws63Outcome::StackFault(sig),
            _ => Ws63Outcome::Exit(code),
        };
    }
    let mut out = String::new();
    use std::io::Read as _;
    child
        .stdout
        .take()
        .expect("piped stdout")
        .read_to_string(&mut out)
        .expect("read driver stdout");
    Ws63Outcome::Value(out.trim().to_string())
}

/// The default stack the driver gives the root's thread (8 MiB, the macOS
/// main-thread default).
const WS6_3_STACK_KIB: u64 = 8 * 1024;

/// The wall bound for one driver process. Every passing vector finishes in
/// milliseconds and the measured stack overflow in ~15 ms; the bound only
/// catches a hang. It bounds a driver that has ALREADY been launched once
/// ([`launch::ws6_3_first_launch`], via [`launch::ws6_3_launched_driver`] in
/// both lane builders, and required by [`ws6_3_run`]), so it measures the
/// root, never the OS's first-launch assessment (see
/// [`launch::WS6_3_FIRST_LAUNCH_WALL`] for the measurement).
const WS6_3_WALL: std::time::Duration = std::time::Duration::from_secs(30);

/// A value outcome, for comparison.
fn ws6_3_value(v: u64) -> Ws63Outcome {
    Ws63Outcome::Value(v.to_string())
}

/// Whether `got` is how the source-compiled `Nat.bitwise` fails: a fault on
/// the stack guard page (caught by the driver, so no crash report) or still
/// running at the wall bound.
fn ws6_3_crashed_or_hung(got: &Ws63Outcome) -> bool {
    matches!(got, Ws63Outcome::StackFault(_) | Ws63Outcome::Timeout)
}

/// One lane's driver binary.
struct Ws63Lane {
    name: &'static str,
    bin: std::path::PathBuf,
}

/// Build both lanes' drivers for `art`: `--emit c` always, trust-ir ->
/// trust-cg when a trust-cg is found (the experiment, license-stripped
/// fixture). `shims` is the C text of the prelude shims the link provides.
fn ws6_3_lanes(
    art: &crate::pass_manager::PipelineArtifacts,
    shims: &str,
    dir: &std::path::Path,
    label: &str,
    host: (&str, &str),
) -> Vec<Ws63Lane> {
    let c_code = art
        .emit_c(crate::emit_c::CEmitConfig::default())
        .expect("the WS6.3 closure lowers to C");
    let mut lanes = vec![Ws63Lane {
        name: "emit_c",
        bin: ws6_3_build_c(&c_code, shims, dir, &format!("{label}_c"), host.1),
    }];
    match find_trust_cg() {
        Some(trust_cg) => {
            let module = art
                .emit_trust_ir(&ws6_1_extern_config())
                .expect("the WS6.3 closure lowers to trust-ir");
            lanes.push(Ws63Lane {
                name: "trust-ir",
                bin: ws6_3_build_trust_ir(
                    &module,
                    &trust_cg,
                    shims,
                    dir,
                    &format!("{label}_ti"),
                    host,
                ),
            });
        }
        None => eprintln!("{label}: trust-ir lane skipped: trust-cg binary not found"),
    }
    lanes
}

/// Every `BinOp` of `f`, as `(op, ty)`, and its number of calls.
fn ws6_3_ops_and_calls(f: &trust_ir::Function) -> (Vec<(BinOp, Ty)>, usize) {
    use trust_ir::inst::Inst;
    let mut ops = Vec::new();
    let mut calls = 0;
    for n in f.instructions() {
        match &n.inst {
            Inst::BinOp { op, ty, .. } => ops.push((*op, ty.clone())),
            Inst::Call { .. } | Inst::CallIndirect { .. } | Inst::Invoke { .. } => calls += 1,
            _ => {}
        }
    }
    (ops, calls)
}

/// 2b, STRUCTURAL, on the real pipeline: `UIntW.land a b` and `UIntW.lor a
/// b` at every width emit exactly ONE native `and`/`or` at `uW` and NO call,
/// the primitive itself is not emitted (the native arm is the only path), and
/// the module still validates and mints (the TV minter SKIPS `And`/`Or`,
/// which are outside Fragment-2, rather than refusing the compile).
///
/// Control (so the checker is not vacuous): `UIntW.div`, which stays out of
/// the native table (Lean's `x / 0 = 0`), is still a call.
#[test]
fn test_ws6_3_uint_land_lor_emit_one_native_op_and_no_call() {
    use crate::pass_manager::{compile_lcnf_to_trust_ir, PipelineConfig};
    use clean_kernel::env::Declaration;
    use clean_kernel::{BinderInfo, Environment, Expr as KExpr};

    let widths = [
        ("UInt8", Ty::U8),
        ("UInt16", Ty::U16),
        ("UInt32", Ty::U32),
        ("UInt64", Ty::U64),
    ];
    let mut env = Environment::try_with_prelude().expect("prelude environment");
    let mut roots = Vec::new();
    for (w, _) in &widths {
        for op in ["land", "lor", "div"] {
            let t = KExpr::const_str(w);
            let root = format!("ws6_3_{op}_{w}");
            env.add_decl(Declaration::Definition {
                name: Name::from_string(&root),
                level_params: vec![],
                type_: KExpr::arrow(t.clone(), KExpr::arrow(t.clone(), t.clone())),
                value: KExpr::lam(
                    BinderInfo::Default,
                    t.clone(),
                    KExpr::lam(
                        BinderInfo::Default,
                        t,
                        KExpr::apps(
                            KExpr::const_str(&format!("{w}.{op}")),
                            [KExpr::bvar(1), KExpr::bvar(0)],
                        ),
                    ),
                ),
                is_reducible: true,
            })
            .unwrap_or_else(|e| panic!("{root} kernel-checks: {e:?}"));
            roots.push(root);
        }
    }
    let root_refs: Vec<&str> = roots.iter().map(String::as_str).collect();
    let decls = ws6_1_closure_shimming(&env, &root_refs, WS6_3_NAT_SHIMMED);
    let module = compile_lcnf_to_trust_ir(
        &decls,
        &env,
        &PipelineConfig::default(),
        &ws6_1_extern_config(),
    )
    .expect("the land/lor/div roots lower and mint (the minter skips And/Or)");
    let errors = validate_module(&module);
    assert!(errors.is_empty(), "validate_module: {errors:?}");

    for (w, ty) in &widths {
        for (op, native) in [("land", BinOp::And), ("lor", BinOp::Or)] {
            let root = format!("ws6_3_{op}_{w}");
            let f = module
                .functions
                .iter()
                .find(|f| f.name == root)
                .unwrap_or_else(|| panic!("`{root}` is not emitted"));
            let (ops, calls) = ws6_3_ops_and_calls(f);
            assert_eq!(
                ops,
                vec![(native, ty.clone())],
                "`{root}` must be exactly one native {native:?} at {ty:?}"
            );
            assert_eq!(calls, 0, "`{root}` must make no call");
            let prim = format!("{w}.{op}");
            assert!(
                module.functions.iter().all(|f| f.name != prim),
                "the primitive `{prim}` itself must not be emitted"
            );
        }
        let root = format!("ws6_3_div_{w}");
        let f = module
            .functions
            .iter()
            .find(|f| f.name == root)
            .unwrap_or_else(|| panic!("`{root}` is not emitted"));
        let (_, calls) = ws6_3_ops_and_calls(f);
        assert!(
            calls > 0,
            "control: `{root}` is not native, so the checker must see its call"
        );
    }
}

/// POSITIVE (kernel-built `mask`) + MUTATION CONTROL (`natMask`), both lanes.
///
/// * With WS6.3: `mask` over the recorded vectors plus `(2^63+5, 2^63+3)`, and
///   `natMask` over HEAP inputs, compute the kernel-certified values through
///   `--emit c` AND trust-ir -> trust-cg; each expectation off by one is
///   rejected (negative twin).
/// * Fix (2a) reverted (`Nat.land`/`Nat.lor` compiled from source, the pre-
///   WS6.3 closure): every heap `natMask` vector crashes or hangs on both
///   lanes, as measured, while the tagged control still passes. `natMask`
///   never touches `UInt*.land`, so (2b) is not what makes it pass.
/// * With (2a) reverted, the trust-ir lane's `mask` still passes (2b alone:
///   no `Nat` op is reached), while the C lane's `mask` — which has no native
///   table and compiles `UInt64.land` through `Nat.land` — crashes on its heap
///   vectors: the named cause, per lane.
#[test]
fn test_ws6_3_mask_and_natmask_vectors_with_mutation_control() {
    // SELF-SKIP OK: native lanes (emit-c + trust-cg) link only for aarch64/x86_64 hosts; other arches have no binary to run, and the skip is logged.
    let Some(host) = ws6_1_host() else {
        eprintln!("WS6.3 vectors skipped: unsupported host arch");
        return;
    };
    let env = ws6_3_env();
    let dir = tempfile::tempdir().expect("tempdir");

    // WS6.3 as landed.
    let art = ws6_3_artifacts(&env, WS6_3_NAT_SHIMMED);
    for lane in ws6_3_lanes(&art, &ws6_3_nat_shims_c(), dir.path(), "fixed", host) {
        for (root, vectors) in [
            ("mask", &WS6_3_MASK_VECTORS[..]),
            ("natMask", &WS6_3_NATMASK_VECTORS[..]),
        ] {
            for &(a, b, r) in vectors {
                let got = ws6_3_run(&lane.bin, root, (a, b), WS6_3_STACK_KIB, WS6_3_WALL);
                assert_eq!(
                    got,
                    ws6_3_value(r),
                    "{}: {root} {a} {b} must be the kernel-certified {r}",
                    lane.name
                );
                assert_ne!(
                    got,
                    ws6_3_value(r.wrapping_add(1)),
                    "{}: the differential must REJECT {root} {a} {b} off by one",
                    lane.name
                );
            }
        }
    }

    // Fix (2a) reverted: the source-compiled `Nat.bitwise`.
    let reverted = ws6_3_artifacts(&env, WS6_1_NAT_SHIMMED);
    for lane in ws6_3_lanes(&reverted, WS6_1_NAT_SHIMS_C, dir.path(), "reverted", host) {
        for &(a, b, r) in &WS6_3_NATMASK_VECTORS {
            let got = ws6_3_run(&lane.bin, "natMask", (a, b), WS6_3_STACK_KIB, WS6_3_WALL);
            if a < (1 << 63) && b < (1 << 63) {
                assert_eq!(
                    got,
                    ws6_3_value(r),
                    "{}: the tagged control must still pass with (2a) reverted",
                    lane.name
                );
            } else {
                assert!(
                    ws6_3_crashed_or_hung(&got),
                    "{}: with (2a) reverted, natMask {a} {b} must crash or hang, got {got:?}",
                    lane.name
                );
            }
        }
        for &(a, b, r) in &WS6_3_MASK_VECTORS {
            let got = ws6_3_run(&lane.bin, "mask", (a, b), WS6_3_STACK_KIB, WS6_3_WALL);
            let heap = a >= (1 << 63) || b >= (1 << 63);
            if lane.name == "trust-ir" || !heap {
                assert_eq!(
                    got,
                    ws6_3_value(r),
                    "{}: mask {a} {b} (2b alone on trust-ir; tagged on C)",
                    lane.name
                );
            } else {
                assert!(
                    ws6_3_crashed_or_hung(&got),
                    "{}: with (2a) reverted, the C lane's mask {a} {b} reaches the \
                     source `Nat.land` and must crash or hang, got {got:?}",
                    lane.name
                );
            }
        }
    }
}

/// STEP 1, kept as a standing assertion of the NAMED cause: with the source
/// `Nat.bitwise` compiled (fix 2a reverted), the crash is STACK DEPTH linear
/// in the fuel `m + n`. `natMask (2^k) 0` (fuel 2^k, tagged operands, so no
/// heap cell is involved) overflows at a threshold `k*` that moves up by
/// EXACTLY one when the thread's stack doubles, while `mask (2^64-1)
/// (2^64-2)` (fuel ~2^65) overflows at every stack size. Measured
/// 2026-09-18 on both lanes: k* = 14 / 15 / 16 at 8 / 16 / 32 MiB.
#[test]
fn test_ws6_3_step1_crash_is_fuel_linear_stack_depth() {
    // SELF-SKIP OK: native lanes (emit-c + trust-cg) link only for aarch64/x86_64 hosts; other arches have no binary to run, and the skip is logged.
    let Some(host) = ws6_1_host() else {
        eprintln!("WS6.3 step-1 scaling skipped: unsupported host arch");
        return;
    };
    let env = ws6_3_env();
    let dir = tempfile::tempdir().expect("tempdir");
    let reverted = ws6_3_artifacts(&env, WS6_1_NAT_SHIMMED);
    for lane in ws6_3_lanes(&reverted, WS6_1_NAT_SHIMS_C, dir.path(), "scaling", host) {
        let threshold = |stack_kib: u64| {
            (8..=24u32)
                .find(|&k| {
                    let got = ws6_3_run(&lane.bin, "natMask", (1 << k, 0), stack_kib, WS6_3_WALL);
                    match got {
                        Ws63Outcome::Value(v) => {
                            assert_eq!(v, "1", "{}: natMask 2^{k} 0", lane.name);
                            false
                        }
                        Ws63Outcome::StackFault(_) => true,
                        other => panic!("{}: natMask 2^{k} 0 ended as {other:?}", lane.name),
                    }
                })
                .unwrap_or_else(|| panic!("{}: no overflow up to fuel 2^24", lane.name))
        };
        let stacks = [8 * 1024u64, 16 * 1024, 32 * 1024];
        let ks: Vec<u32> = stacks.iter().map(|&s| threshold(s)).collect();
        assert_eq!(
            ks,
            vec![ks[0], ks[0] + 1, ks[0] + 2],
            "{}: doubling the stack must double the fuel threshold (depth linear in fuel)",
            lane.name
        );
        for stack in stacks {
            let got = ws6_3_run(
                &lane.bin,
                "mask",
                (u64::MAX, u64::MAX - 1),
                stack,
                WS6_3_WALL,
            );
            if lane.name == "emit_c" {
                assert!(
                    matches!(got, Ws63Outcome::StackFault(_)),
                    "{}: fuel ~2^65 must overflow at every stack ({stack} KiB), got {got:?}",
                    lane.name
                );
            } else {
                // trust-ir's `mask` is native (2b): it never reaches `Nat`.
                assert_eq!(got, ws6_3_value(u64::MAX), "{}: mask via 2b", lane.name);
            }
        }
    }
}

/// The reducer-agreement test (the shims are TCB for the native path):
/// `clean_nat_land/lor/xor` on random u128 pairs (plus the tagged/heap/limb
/// edges) against the kernel's own `Nat.land/lor/xor` — each result must be
/// accepted by the kernel as `rfl`, and the same result off by one refused —
/// and against `clean-runtime`'s FFI natives (`builtin_nat_land` & co.) on
/// the pairs they cover (u64). The result's representation is checked too:
/// tagged below 2^63, heap at or above.
#[test]
fn test_ws6_3_nat_bitwise_shims_agree_with_the_kernel_reducer() {
    use clean_kernel::Expr as KExpr;
    use clean_runtime::ffi_bridge::{FfiBridge, Value};
    // SELF-SKIP OK: the C agreement driver links only for aarch64/x86_64 hosts; other arches have no driver to compare against the kernel, and the skip is logged.
    let Some(host) = ws6_1_host() else {
        eprintln!("WS6.3 reducer agreement skipped: unsupported host arch");
        return;
    };
    // Deterministic splitmix64, so a failure reproduces.
    let mut state: u64 = 0x5753_362e_3320_6d61;
    let mut next = || {
        state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = state;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    };
    let edges: [u128; 8] = [
        0,
        1,
        (1 << 63) - 1,
        1 << 63,
        u128::from(u64::MAX),
        1 << 64,
        u128::MAX - 1,
        u128::MAX,
    ];
    let mut pairs: Vec<(u128, u128)> = Vec::new();
    for &a in &edges {
        for &b in &edges {
            pairs.push((a, b));
        }
    }
    for i in 0..64 {
        let a = (u128::from(next()) << 64) | u128::from(next());
        let b = (u128::from(next()) << 64) | u128::from(next());
        // Mix widths: full u128, one limb, and tagged-range operands.
        let (a, b) = match i % 3 {
            0 => (a, b),
            1 => (a & u128::from(u64::MAX), b & u128::from(u64::MAX)),
            _ => (a & ((1 << 63) - 1), b >> 1),
        };
        pairs.push((a, b));
    }

    // The C driver: one line per pair, `land lor xor` plus a representation
    // flag per result (1 = tagged immediate).
    let mut table = String::from("static const unsigned long long WS_PAIRS[][4] = {\n");
    for (a, b) in &pairs {
        table.push_str(&format!(
            "  {{{}ull, {}ull, {}ull, {}ull}},\n",
            *a as u64,
            (*a >> 64) as u64,
            *b as u64,
            (*b >> 64) as u64
        ));
    }
    table.push_str("};\n");
    let main = format!(
        "#include <stdio.h>\n#include <stdint.h>\n#include \"clean_runtime.h\"\n{table}\
static void ws_put(unsigned __int128 v) {{\n\
  char buf[64]; int i = 63; buf[i] = 0;\n\
  if (v == 0) {{ buf[--i] = '0'; }}\n\
  while (v > 0) {{ buf[--i] = (char)('0' + (unsigned)(v % 10)); v /= 10; }}\n\
  printf(\"%s\", buf + i);\n\
}}\n\
int main(void) {{\n\
  size_t n = sizeof WS_PAIRS / sizeof WS_PAIRS[0];\n\
  for (size_t i = 0; i < n; i++) {{\n\
    clean_obj* (*ops[3])(clean_obj*, clean_obj*) = {{clean_nat_land, clean_nat_lor, clean_nat_xor}};\n\
    for (int k = 0; k < 3; k++) {{\n\
      clean_obj* a = clean_nat_big(WS_PAIRS[i][0], WS_PAIRS[i][1]);\n\
      clean_obj* b = clean_nat_big(WS_PAIRS[i][2], WS_PAIRS[i][3]);\n\
      clean_obj* r = ops[k](a, b);\n\
      ws_put(clean_nat_to_u128(r));\n\
      printf(\":%d%s\", clean_is_scalar(r) ? 1 : 0, k < 2 ? \" \" : \"\\n\");\n\
      clean_dec(r);\n\
    }}\n\
  }}\n\
  return 0;\n\
}}\n"
    );
    let dir = tempfile::tempdir().expect("tempdir");
    let bin = ws6_3_link(dir.path(), "agree", &[("main.c", main)], &[], host.1);
    let out = std::process::Command::new(&bin)
        .output()
        .expect("run the reducer-agreement driver");
    assert!(out.status.success(), "driver exited {:?}", out.status);
    let stdout = String::from_utf8_lossy(&out.stdout);
    let lines: Vec<&str> = stdout.lines().collect();
    assert_eq!(lines.len(), pairs.len(), "one line per pair");

    let mut env = clean_kernel::Environment::try_with_prelude().expect("prelude environment");
    let bridge = FfiBridge::new();
    let nat = KExpr::const_str("Nat");
    let ops: [(&str, fn(u128, u128) -> u128); 3] = [
        ("Nat.land", |a, b| a & b),
        ("Nat.lor", |a, b| a | b),
        ("Nat.xor", |a, b| a ^ b),
    ];
    for (i, ((a, b), line)) in pairs.iter().zip(&lines).enumerate() {
        let cells: Vec<&str> = line.split(' ').collect();
        assert_eq!(cells.len(), 3, "pair {i}: `{line}`");
        for (k, ((name, spec), cell)) in ops.iter().zip(&cells).enumerate() {
            let (value, tag) = cell.split_once(':').expect("value:tag");
            let got: u128 = value.parse().expect("decimal u128");
            // The kernel is the authority: its `Nat.<op> a b` must reduce to
            // exactly the runtime's answer.
            let lhs = KExpr::apps(
                KExpr::const_str(name),
                [KExpr::nat_lit_u128(*a), KExpr::nat_lit_u128(*b)],
            );
            env.add_decl(ws6_3_rfl(
                &format!("ws6_3_agree_{i}_{k}"),
                nat.clone(),
                lhs.clone(),
                KExpr::nat_lit_u128(got),
            ))
            .unwrap_or_else(|e| {
                panic!("the kernel must certify `{name} {a} {b} = {got}` (runtime): {e:?}")
            });
            if i % 16 == 0 {
                assert!(
                    env.add_decl(ws6_3_rfl(
                        &format!("ws6_3_agree_off_{i}_{k}"),
                        nat.clone(),
                        lhs,
                        KExpr::nat_lit_u128(got.wrapping_add(1)),
                    ))
                    .is_err(),
                    "the kernel must REFUSE `{name} {a} {b} = {got} + 1`"
                );
            }
            assert_eq!(got, spec(*a, *b), "{name} {a} {b}: bitwise spec");
            assert_eq!(
                tag == "1",
                got < (1 << 63),
                "{name} {a} {b} = {got}: tagged iff below 2^63"
            );
            if let (Ok(a64), Ok(b64)) = (u64::try_from(*a), u64::try_from(*b)) {
                let ffi = bridge
                    .call_native(name, &[Value::Nat(a64), Value::Nat(b64)])
                    .unwrap_or_else(|e| panic!("FFI {name} {a64} {b64}: {e:?}"));
                assert!(
                    matches!(ffi, Value::Nat(v) if u128::from(v) == got),
                    "FFI {name} {a64} {b64} disagrees with the runtime's {got}"
                );
            }
        }
    }
}

// WS6.3 review: adversarial vectors (narrow widths, function values, the
// shims' RC contract, compiled `Nat.xor`).
#[path = "emit_trust_ir_ws6_3_review_tests.rs"]
mod review;

#[path = "emit_trust_ir_ws6_3_launch_tests.rs"]
mod launch;

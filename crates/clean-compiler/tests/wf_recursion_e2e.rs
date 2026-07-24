// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! RUNG B BEHAVIORAL pin: WELL-FOUNDED recursion (`WellFounded.fix`,
//! `WellFounded.fixF`, `Acc.rec`) compiled from source computes the right
//! VALUES and TERMINATES, verified end-to-end — synthetic kernel definition →
//! LCNF → full pipeline → emitted C → host `cc` → executed against the real
//! clean runtime.
//!
//! The lowering ([`to_lcnf::lower::lower_wf_rec_apply`]) synthesizes a
//! value-recursive `go step v hr = step v [box0] (go step)` that recurses on
//! the recovered INDEX value and NEVER inspects the erased `Acc` scrutinee (a
//! `box(0)` proof). This test pins that a real recursion — `sum(n) = n +
//! (n-1) + .. + 0 = n(n+1)/2` — computed three ways (via `WellFounded.fixF`,
//! `WellFounded.fix`, and `Acc.rec` directly) returns the correct values and
//! terminates. The erased accessibility proof / hypothesis slots are `box(0)`
//! and are never dereferenced (would be a wild read the runtime crashes on).
//!
//! Skips (like the other native e2e tests) when no C compiler is found.

#![cfg(feature = "round-trip-compile")]

use std::collections::HashSet;
use std::path::{Path, PathBuf};
use std::process::Command;

use clean_compiler::emit_c::{emit_c_with_config, CEmitConfig};
use clean_compiler::pass_manager::{compile_lcnf_decls, PipelineConfig};
use clean_compiler::to_lcnf::constant_to_decl;
use clean_compiler::Decl;
use clean_kernel::env::ConstantInfo;
use clean_kernel::expr::{BinderData, BinderInfo};
use clean_kernel::{Environment, Expr, ExprVisitor, Level, LevelVec, Name};

fn runtime_include_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../clean-runtime/include")
}
fn runtime_c_source() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../clean-runtime/src/clean_runtime.c")
}
fn find_c_compiler() -> Option<String> {
    for compiler in ["cc", "gcc", "clang"] {
        if Command::new(compiler)
            .arg("--version")
            .output()
            .map(|o| o.status.success())
            .unwrap_or(false)
        {
            return Some(compiler.to_string());
        }
    }
    None
}

// --- kernel Expr builders -------------------------------------------------

fn dflt() -> BinderData {
    BinderInfo::Default.into()
}
fn lam(ty: Expr, body: Expr) -> Expr {
    Expr::lam(dflt(), ty, body)
}
fn pi(ty: Expr, body: Expr) -> Expr {
    Expr::pi(dflt(), ty, body)
}
fn cst(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), LevelVec::default())
}
fn nat() -> Expr {
    cst("Nat")
}
fn one() -> Vec<Level> {
    vec![Level::succ(Level::zero())]
}

/// `F : (n) (ih) -> Nat` for `sum` — the 2-ary `WellFounded.fix{,F}` step:
///   F n ih = Nat.casesOn n 0 (fun k => Nat.add (Nat.succ k) (ih k trivial))
/// `ih : Nat -> True -> Nat`; the `True` proof slot erases at runtime.
fn f_sum() -> Expr {
    let ih_ty = pi(nat(), pi(cst("True"), nat()));
    let succ_branch = lam(
        nat(), // fun k =>  (binders: n=2, ih=1, k=0)
        Expr::apps(
            cst("Nat.add"),
            [
                Expr::apps(cst("Nat.succ"), [Expr::bvar(0)]),
                Expr::apps(Expr::bvar(1), [Expr::bvar(0), cst("True.intro")]),
            ],
        ),
    );
    let cases = Expr::apps(
        Expr::const_(Name::from_string("Nat.casesOn"), one()),
        [
            lam(nat(), nat()),
            Expr::bvar(1),
            Expr::nat_lit(0),
            succ_branch,
        ],
    );
    lam(nat(), lam(ih_ty, cases))
}

/// The 3-ary `Acc.rec` minor `(x) (h) (ih) -> Nat` — same `sum` body; the
/// middle binder `h` (the erased accessibility subproof) is never used.
fn minor_sum() -> Expr {
    let ih_ty = pi(nat(), pi(cst("True"), nat()));
    let succ_branch = lam(
        nat(), // binders here: x=3, h=2, ih=1, k=0
        Expr::apps(
            cst("Nat.add"),
            [
                Expr::apps(cst("Nat.succ"), [Expr::bvar(0)]),
                Expr::apps(Expr::bvar(1), [Expr::bvar(0), cst("True.intro")]),
            ],
        ),
    );
    let cases = Expr::apps(
        Expr::const_(Name::from_string("Nat.casesOn"), one()),
        [
            lam(nat(), nat()),
            Expr::bvar(2),
            Expr::nat_lit(0),
            succ_branch,
        ],
    );
    lam(nat(), lam(cst("True"), lam(ih_ty, cases)))
}

fn dummy_r() -> Expr {
    lam(nat(), lam(nat(), cst("True")))
}
fn motive_c() -> Expr {
    lam(nat(), nat())
}

fn add_def(env: &mut Environment, name: &str, value: Expr) {
    env.add_constant_unchecked_for_test(ConstantInfo::new(
        Name::from_string(name),
        Vec::new(),
        pi(nat(), nat()),
        Some(lam(nat(), value)),
        false,
    ));
}

struct DepCollector {
    deps: Vec<Name>,
}
impl ExprVisitor for DepCollector {
    type Result = ();
    fn combine(&self, _a: (), _b: ()) {}
    fn visit_const(&mut self, name: &Name, _l: &LevelVec) {
        self.deps.push(name.clone());
    }
}
fn collect_deps(v: &Expr) -> Vec<Name> {
    let mut c = DepCollector { deps: Vec::new() };
    c.visit_expr(v);
    c.deps
}

/// Nat primitive shims (the `clean` native build's denylist table) — the
/// synthetic roots reach `Nat.add`/`Nat.sub`/`Nat.decEq` through the boxed-int
/// `Nat.casesOn` lowering.
const DENYLIST: &[&str] = &["l_Nat_add", "l_Nat_sub", "l_Nat_mul", "l_Nat_decEq"];

const SHIM_PREAMBLE: &str = r#"
#include "clean_runtime.h"
clean_obj* l_Nat_add(clean_obj* a, clean_obj* b) { return clean_box(clean_unbox(a) + clean_unbox(b)); }
clean_obj* l_Nat_sub(clean_obj* a, clean_obj* b) { size_t x = clean_unbox(a), y = clean_unbox(b); return clean_box(x < y ? 0 : x - y); }
clean_obj* l_Nat_mul(clean_obj* a, clean_obj* b) { return clean_box(clean_unbox(a) * clean_unbox(b)); }
clean_obj* l_Nat_decEq(clean_obj* a, clean_obj* b) { return clean_box(clean_unbox(a) == clean_unbox(b) ? 1 : 0); }
"#;

fn compile_closure(env: &Environment, roots: &[&str]) -> Vec<clean_compiler::ir::IRDecl> {
    let pipeline = PipelineConfig::default();
    let mut seen: HashSet<Name> = HashSet::new();
    let mut decls: Vec<Decl> = Vec::new();
    let mut worklist: Vec<Name> = roots.iter().map(|r| Name::from_string(r)).collect();
    while let Some(dep) = worklist.pop() {
        if !seen.insert(dep.clone()) {
            continue;
        }
        let Some(info) = env.get_const(&dep) else {
            continue;
        };
        if DENYLIST.contains(&clean_compiler::mangle::mangle_name(&dep).as_str()) {
            continue;
        }
        let Some(decl) = constant_to_decl(env, info).ok().flatten() else {
            continue;
        };
        if compile_lcnf_decls(std::slice::from_ref(&decl), env, &pipeline).is_err() {
            continue;
        }
        if let Some(value) = &info.value {
            worklist.extend(collect_deps(value));
        }
        decls.push(decl);
    }
    for root in roots {
        assert!(
            seen.contains(&Name::from_string(root)),
            "root {root} must compile from source (RUNG B)"
        );
    }
    compile_lcnf_decls(&decls, env, &pipeline)
        .expect("closure compiles through the full pipeline")
        .boxed_ir_decls
}

#[test]
fn test_well_founded_recursion_computes_correct_values() {
    let Some(cc) = find_c_compiler() else {
        eprintln!("wf e2e skipped: no C compiler found");
        return;
    };

    let mut env = Environment::with_prelude();
    let _ = env.init_io_ops();
    // wfSumF n  = WellFounded.fixF Nat r C F n acc      (2-ary step)
    add_def(
        &mut env,
        "wfSumF",
        Expr::apps(
            Expr::const_(Name::from_string("WellFounded.fixF"), one()),
            [
                nat(),
                dummy_r(),
                motive_c(),
                f_sum(),
                Expr::bvar(0),
                cst("True.intro"),
            ],
        ),
    );
    // wfSumFix n = WellFounded.fix Nat r C hwf F n       (drops WellFounded wrapper)
    add_def(
        &mut env,
        "wfSumFix",
        Expr::apps(
            Expr::const_(Name::from_string("WellFounded.fix"), one()),
            [
                nat(),
                dummy_r(),
                motive_c(),
                cst("True.intro"),
                f_sum(),
                Expr::bvar(0),
            ],
        ),
    );
    // wfSumAcc n = Acc.rec Nat r motive minor n acc      (3-ary minor, erased h = box0)
    add_def(
        &mut env,
        "wfSumAcc",
        Expr::apps(
            Expr::const_(
                Name::from_string("Acc.rec"),
                vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
            ),
            [
                nat(),
                dummy_r(),
                lam(nat(), lam(cst("True"), nat())),
                minor_sum(),
                Expr::bvar(0),
                cst("True.intro"),
            ],
        ),
    );

    let decls = compile_closure(&env, &["wfSumF", "wfSumFix", "wfSumAcc"]);
    let emitted = emit_c_with_config(
        &decls,
        CEmitConfig {
            check_ir: false,
            ..CEmitConfig::default()
        },
    )
    .expect("emit C for the well-founded closure");

    let main_body = r#"
int main(void) {
    size_t ns[] = {0, 1, 2, 3, 5, 10, 100};
    for (int i = 0; i < 7; i++) {
        size_t n = ns[i];
        size_t expect = n * (n + 1) / 2;
        printf("%zu %zu %zu %zu\n", n,
            clean_unbox(l_wfSumF(clean_box(n))),
            clean_unbox(l_wfSumFix(clean_box(n))),
            clean_unbox(l_wfSumAcc(clean_box(n))));
        (void)expect;
    }
    return 0;
}
"#;

    let dir = tempfile::tempdir().expect("tempdir");
    let source = dir.path().join("wf_e2e.c");
    let binary = dir.path().join("wf_e2e");
    std::fs::write(
        &source,
        format!("#include <stdio.h>\n{SHIM_PREAMBLE}\n{emitted}\n{main_body}"),
    )
    .expect("write source");

    let compile = Command::new(&cc)
        .arg("-o")
        .arg(&binary)
        .arg(&source)
        .arg(runtime_c_source())
        .arg("-I")
        .arg(runtime_include_dir())
        .output()
        .expect("spawn cc");
    assert!(
        compile.status.success(),
        "cc failed:\n{}",
        String::from_utf8_lossy(&compile.stderr)
    );

    let run = Command::new(&binary).output().expect("run wf_e2e");
    assert!(
        run.status.success(),
        "binary exited nonzero (nontermination / crash)"
    );
    let stdout = String::from_utf8_lossy(&run.stdout);
    for line in stdout.lines() {
        let v: Vec<u64> = line
            .split_whitespace()
            .map(|s| s.parse().unwrap())
            .collect();
        let (n, fixf, fix, acc) = (v[0], v[1], v[2], v[3]);
        let expect = n * (n + 1) / 2;
        assert_eq!(
            (fixf, fix, acc),
            (expect, expect, expect),
            "well-founded sum({n}) mismatch: fixF={fixf} fix={fix} acc={acc} expect={expect}\nfull:\n{stdout}"
        );
    }
    assert_eq!(
        stdout.lines().count(),
        7,
        "expected 7 result rows:\n{stdout}"
    );
}

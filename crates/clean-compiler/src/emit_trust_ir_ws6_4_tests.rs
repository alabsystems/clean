// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! WS6.4 — known-instance class methods resolve before boxing
//! (`HAdd`/`HMul`/… → native ops). A child of `emit_trust_ir::tests`, so the
//! `trust-ir-backend-lib` gate leg (`-- emit_trust_ir`) runs it.
//!
//! The rule and its unit-level mutation controls live in
//! `opt::resolve_instances`; this file pins the effect on REAL Clean source
//! through the full pipeline and the trust-ir back end:
//!
//! * the proof program's p03/p12/p14 roots emit zero `l_H*_h*` class-method
//!   calls at `-O1`/`-O2`, and `sqLet` is `add; mul; ret` at `U64` (the `-O0`
//!   control keeps both calls, so the check is not vacuous);
//! * the negative twin — a user class whose instance is built through a
//!   `match` — keeps its dynamic call, while the literal-`mk` twin resolves;
//! * the companion `UIntW.ofNat` fold's boundaries through the pipeline;
//! * the WS6.1 and WS6.2 differential oracles still pass at `-O1` and `-O2`
//!   (their own fixtures stay at `-O0`, where the boxed path they exercise
//!   is still visible).

use super::*;
use crate::pass_manager::{compile_lcnf_decls, PipelineConfig};
use crate::rc_repair::e2e_support::{closure_decls_of, elaborated_env_with, o0};
use trust_ir::inst::{BinOp, Inst};
use trust_ir::ty::Ty;
use trust_ir::Constant;

/// The proof program's p03 / p12 / p14 roots, verbatim
/// (`reports/2026-09-17-two-language-proof-program/rerun-lean-head/probes`).
const BATTERY_SOURCE: &str = "def sqLet (a : UInt64) : UInt64 := let t := a + 1; t * t\n\
def w8 (a b : UInt8) : UInt8 := a * b + 1\n\
def w16 (a b : UInt16) : UInt16 := a - b\n\
def w32 (a b : UInt32) : UInt32 := a + b * a\n\
def pickWide (a : UInt8) (b : UInt16) (c : UInt32) (d : UInt64) : UInt16 := b\n\
def inc (a : UInt64) : UInt64 := a + 1\n\
def inc2 (a : UInt64) : UInt64 := inc (inc a)\n";

const BATTERY_ROOTS: [&str; 7] = ["sqLet", "w8", "w16", "w32", "pickWide", "inc", "inc2"];

/// `clean compile -O2`'s pipeline (`cmd_compile::pipeline_config_from_opt_level`).
fn o2() -> PipelineConfig {
    PipelineConfig {
        opt: crate::opt::OptConfig::aggressive(),
        rc: crate::rc::RCConfig::aggressive(),
        boxing: crate::boxing::BoxingConfig::default(),
    }
}

/// The optimizing levels the rule runs at.
fn optimizing() -> [(&'static str, PipelineConfig); 2] {
    [("-O1", PipelineConfig::default()), ("-O2", o2())]
}

fn ws6_4_config() -> TrustIrConfig {
    TrustIrConfig {
        module_name: "ws6_4".to_string(),
        use_clean_dialect: true,
        runtime_lowering: RuntimeLowering::ExternCalls,
        ..TrustIrConfig::default()
    }
}

/// `source`'s `roots` closure compiled through `pipeline` and lowered to a
/// validated trust-ir module.
fn module_of(source: &str, roots: &[&str], pipeline: &PipelineConfig) -> Module {
    let env = elaborated_env_with(source);
    let decls = closure_decls_of(&env, pipeline, roots);
    let module = compile_lcnf_decls(&decls, &env, pipeline)
        .expect("the closure compiles through the real pipeline")
        .emit_trust_ir(&ws6_4_config())
        .expect("the closure lowers to trust-ir");
    let errors = validate_module(&module);
    assert!(errors.is_empty(), "validate_module: {errors:?}");
    module
}

/// `true` iff `name` spells a heterogeneous class-method projection:
/// `HAdd.hAdd` or its runtime shim `l_HAdd_hAdd` (any `H<Op>` class).
fn is_class_method(name: &str) -> bool {
    let bare = name.strip_prefix("l_").unwrap_or(name);
    let Some((class, method)) = bare.split_once(['.', '_']) else {
        return false;
    };
    class.len() > 1
        && class.starts_with('H')
        && method.len() == class.len()
        && method.starts_with('h')
        && method[1..] == class[1..]
}

fn function<'m>(module: &'m Module, name: &str) -> &'m trust_ir::Function {
    module
        .functions
        .iter()
        .find(|f| f.name == name && !f.blocks.is_empty())
        .unwrap_or_else(|| panic!("`{name}` is not defined in the module"))
}

/// The names of every function `f` calls directly.
fn callees(module: &Module, f: &trust_ir::Function) -> Vec<String> {
    f.instructions()
        .filter_map(|n| match &n.inst {
            Inst::Call { callee, .. } => module
                .functions
                .iter()
                .find(|g| g.id == *callee)
                .map(|g| g.name.clone()),
            _ => None,
        })
        .collect()
}

/// Every class-method call in `module`, as `"<caller> -> <callee>"`.
fn class_method_calls(module: &Module) -> Vec<String> {
    module
        .functions
        .iter()
        .flat_map(|f| {
            callees(module, f)
                .into_iter()
                .filter(|c| is_class_method(c))
                .map(move |c| format!("{} -> {c}", f.name))
        })
        .collect()
}

/// A straight-line body with its constants dropped.
fn non_const_insts(f: &trust_ir::Function) -> Vec<&Inst> {
    assert_eq!(f.blocks.len(), 1, "`{}` must be straight-line", f.name);
    f.blocks[0]
        .body
        .iter()
        .map(|n| &n.inst)
        .filter(|i| !matches!(i, Inst::Const { .. }))
        .collect()
}

#[test]
fn test_ws6_4_is_class_method_spelling() {
    for yes in [
        "l_HAdd_hAdd",
        "HAdd.hAdd",
        "l_HMul_hMul",
        "HSub.hSub",
        "l_HMod_hMod",
    ] {
        assert!(is_class_method(yes), "{yes}");
    }
    for no in [
        "UInt64.add",
        "l_Nat_add",
        "HAdd.mk",
        "l_HAdd_mk",
        "hAdd",
        "H.h",
        "HAdd.hMul",
    ] {
        assert!(!is_class_method(no), "{no}");
    }
}

/// Positive, structural: at `-O1` and `-O2` the p03/p12/p14 closure emits
/// ZERO class-method calls, every root calls nothing but another root
/// (`inc2 -> inc`), and each arithmetic root is its native op(s).
#[test]
fn test_ws6_4_battery_roots_emit_no_class_method_calls() {
    for (level, pipeline) in optimizing() {
        let module = module_of(BATTERY_SOURCE, &BATTERY_ROOTS, &pipeline);
        // The roots' own bodies. (Prelude dependencies the closure compiles
        // from source keep theirs where the rule does not apply — e.g.
        // `BitVec.toNat -> HPow.hPow`, whose `instHPow` is a λ over a `Pow`
        // instance, not a literal `mk`.)
        let from_roots: Vec<String> = class_method_calls(&module)
            .into_iter()
            .filter(|c| {
                BATTERY_ROOTS
                    .iter()
                    .any(|r| c.starts_with(&format!("{r} -> ")))
            })
            .collect();
        assert_eq!(
            from_roots,
            Vec::<String>::new(),
            "{level}: no root may call an `l_H*_h*` class method"
        );
        for root in BATTERY_ROOTS {
            let calls = callees(&module, function(&module, root));
            let allowed: &[&str] = if root == "inc2" { &["inc"] } else { &[] };
            assert!(
                calls.iter().all(|c| allowed.contains(&c.as_str())),
                "{level}: `{root}` must call only {allowed:?}, calls {calls:?}"
            );
        }
        for (root, ty, ops) in [
            ("w8", Ty::U8, &[BinOp::Mul, BinOp::Add][..]),
            ("w16", Ty::U16, &[BinOp::Sub][..]),
            ("w32", Ty::U32, &[BinOp::Mul, BinOp::Add][..]),
            ("inc", Ty::U64, &[BinOp::Add][..]),
        ] {
            let got: Vec<(BinOp, Ty)> = non_const_insts(function(&module, root))
                .into_iter()
                .filter_map(|i| match i {
                    Inst::BinOp { op, ty, .. } => Some((*op, ty.clone())),
                    _ => None,
                })
                .collect();
            let want: Vec<(BinOp, Ty)> = ops.iter().map(|op| (*op, ty.clone())).collect();
            assert_eq!(got, want, "{level}: `{root}`'s native ops");
        }
    }
}

/// Positive, structural: `sqLet` is exactly `add; mul; ret` at `U64` (its
/// `1` a constant), at `-O1` and `-O2`.
#[test]
fn test_ws6_4_sqlet_is_add_mul_ret_at_u64() {
    for (level, pipeline) in optimizing() {
        let module = module_of(BATTERY_SOURCE, &["sqLet"], &pipeline);
        let f = function(&module, "sqLet");
        match non_const_insts(f).as_slice() {
            [Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::U64,
                ..
            }, Inst::BinOp {
                op: BinOp::Mul,
                ty: Ty::U64,
                ..
            }, Inst::Return { .. }] => {}
            other => panic!("{level}: `sqLet` must be `add; mul; ret` at U64, got {other:?}"),
        }
    }
}

/// Control: at `-O0` (no resolution) the dynamic path is still there —
/// `sqLet` calls both `l_HAdd_hAdd` and `l_HMul_hMul` — so the zero-call
/// assertions above are not vacuous, and the WS6.1/WS6.2 fixtures that run
/// at `-O0` still see it.
#[test]
fn test_ws6_4_o0_keeps_the_dynamic_class_method_calls() {
    let module = module_of(BATTERY_SOURCE, &["sqLet"], &o0());
    let calls = callees(&module, function(&module, "sqLet"));
    for shim in ["l_HAdd_hAdd", "l_HMul_hMul"] {
        assert!(
            calls.iter().any(|c| c == shim),
            "-O0: `sqLet` must still call `{shim}`: {calls:?}"
        );
    }
}

/// A user class, one instance a literal `mk` application and one built
/// through a `match`, each used at an explicit instance.
const USER_CLASS_SOURCE: &str = "class MyOp (α : Type) where\n  op : α → α → α\n\
instance instMyOpLit : MyOp UInt64 := ⟨UInt64.add⟩\n\
instance instMyOpMatch : MyOp UInt64 := match (0 : Nat) with\n  | 0 => ⟨UInt64.add⟩\n  | _ => ⟨UInt64.sub⟩\n\
def useLit (a b : UInt64) : UInt64 := @MyOp.op UInt64 instMyOpLit a b\n\
def useMatch (a b : UInt64) : UInt64 := @MyOp.op UInt64 instMyOpMatch a b\n";

/// NEGATIVE TWIN: a user class whose instance value is NOT a literal `mk`
/// application (built through a `match`) keeps the dynamic `MyOp.op` call;
/// its literal-`mk` twin resolves to the native `add`. Both are registered
/// instances of the same class, so the only difference is the VALUE.
#[test]
fn test_ws6_4_match_built_instance_keeps_the_dynamic_call() {
    let env = elaborated_env_with(USER_CLASS_SOURCE);
    for inst in ["instMyOpLit", "instMyOpMatch"] {
        assert!(env.is_instance(&Name::from_string(inst)), "{inst}");
    }
    for (level, pipeline) in optimizing() {
        let module = module_of(USER_CLASS_SOURCE, &["useLit", "useMatch"], &pipeline);
        let dynamic = callees(&module, function(&module, "useMatch"));
        assert!(
            dynamic.iter().any(|c| c == "MyOp.op"),
            "{level}: `useMatch` must keep its dynamic `MyOp.op` call: {dynamic:?}"
        );
        let lit = function(&module, "useLit");
        assert_eq!(callees(&module, lit), Vec::<String>::new(), "{level}");
        assert!(
            matches!(
                non_const_insts(lit).as_slice(),
                [
                    Inst::BinOp {
                        op: BinOp::Add,
                        ty: Ty::U64,
                        ..
                    },
                    Inst::Return { .. }
                ]
            ),
            "{level}: `useLit` must be the native add"
        );
    }
}

/// The constant a straight-line, call-free function returns.
fn returned_const(f: &trust_ir::Function) -> Option<i128> {
    match f.blocks[0]
        .body
        .iter()
        .map(|n| &n.inst)
        .collect::<Vec<_>>()
        .as_slice()
    {
        [Inst::Const {
            value: Constant::Int(v),
            ..
        }, Inst::Return { .. }] => Some(*v),
        _ => None,
    }
}

/// The companion fold through the pipeline: the WS6.1 review roots
/// `UInt8.ofNat 5000000007` and `UInt16.ofNat 5000000007` compile at
/// `-O1`/`-O2` to the returned constants `7` and `61959` — no `Nat` is built
/// or read. `UInt8.ofNat (2^64 + 42)`, whose argument is a `Nat.add`/`Nat.mul`
/// computation the pipeline does not fold to a literal, is NOT folded: it
/// keeps its `UInt8.ofNat` call (the fold never guesses a value).
#[test]
fn test_ws6_4_of_nat_literal_roots_fold_to_constants() {
    for (level, pipeline) in optimizing() {
        let module = ws6_1_review_artifacts_at(&pipeline)
            .emit_trust_ir(&ws6_1_extern_config())
            .expect("the review closure lowers to trust-ir");
        for (root, want) in [("ws6_1_rv_lit8", 7), ("ws6_1_rv_lit16", 61959)] {
            let f = function(&module, root);
            assert_eq!(
                returned_const(f),
                Some(want),
                "{level}: `{root}` must fold to `{want}`: {:?}",
                f.blocks
            );
        }
        let big = callees(&module, function(&module, "ws6_1_rv_big8"));
        assert!(
            big.iter().any(|c| c == "UInt8.ofNat"),
            "{level}: a computed `Nat` argument must keep the `UInt8.ofNat` call: {big:?}"
        );
    }
}

// ---- the WS6.1 / WS6.2 differential oracles at -O1 and -O2 --------------

/// WS6.2's `GENERAL.p03_let.sqLet.linkrun` oracle (kernel-certified values,
/// off-by-one twin rejected) at `-O1`.
#[test]
fn test_ws6_4_ws6_2_sqlet_linkrun_at_o1() {
    ws6_2_sqlet_linkrun(&PipelineConfig::default(), "ws64_sqlet_o1", true);
}

/// WS6.2's sqLet oracle at `-O2`.
#[test]
fn test_ws6_4_ws6_2_sqlet_linkrun_at_o2() {
    ws6_2_sqlet_linkrun(&o2(), "ws64_sqlet_o2", true);
}

/// WS6.1's `w8` (kernel-certified `1 0 13`) and heap-`Nat` vector oracles,
/// through `--emit c` AND trust-ir -> trust-cg, at `-O1` and `-O2`; each `w8`
/// expectation off by one is rejected.
#[test]
fn test_ws6_4_ws6_1_w8_and_heap_oracles_at_o1_o2() {
    let Some(host) = ws6_1_host() else {
        eprintln!("WS6.1 oracles skipped: unsupported host arch");
        // SELF-SKIP OK: host-arch precondition -- the native C / trust-cg lanes only target aarch64 and x86_64; on any other ARCH there is nothing to link or run (skip is logged)
        return;
    };
    let w8_want: Vec<u64> = WS6_1_W8_VECTORS.iter().map(|v| v.2).collect();
    let trust_cg = find_trust_cg();
    let dir = tempfile::tempdir().expect("tempdir");
    for (level, pipeline) in optimizing() {
        let art = ws6_1_artifacts_at(&pipeline);
        let tag = level.trim_start_matches('-');
        let c_code = art
            .emit_c(crate::emit_c::CEmitConfig::default())
            .expect("p12 lowers to C");
        let mut lanes = vec![(
            "emit_c",
            ws6_1_run_c(
                &c_code,
                WS6_1_W8_MAIN,
                dir.path(),
                &format!("w8_c_{tag}"),
                host.1,
            ),
            ws6_1_run_c(
                &c_code,
                WS6_1_HEAP_MAIN,
                dir.path(),
                &format!("heap_c_{tag}"),
                host.1,
            ),
        )];
        match &trust_cg {
            Some(cg) => {
                let module = art
                    .emit_trust_ir(&ws6_1_extern_config())
                    .expect("p12 lowers to trust-ir");
                let w8 = format!("w8_ti_{tag}");
                let heap = format!("heap_ti_{tag}");
                lanes.push((
                    "trust-ir",
                    ws6_1_run_trust_ir(&module, cg, WS6_1_W8_MAIN, dir.path(), &w8, host),
                    ws6_1_run_trust_ir(&module, cg, WS6_1_HEAP_MAIN, dir.path(), &heap, host),
                ));
            }
            None => eprintln!("{level}: WS6.1 trust-ir lane skipped: trust-cg binary not found"),
        }
        for (lane, w8, heap) in &lanes {
            let lane = format!("{lane} {level}");
            ws6_1_check(&lane, w8, &w8_want).unwrap_or_else(|e| panic!("{e}"));
            ws6_1_check(&lane, heap, &WS6_1_HEAP_WANT).unwrap_or_else(|e| panic!("{e}"));
            for i in 0..w8_want.len() {
                let mut off = w8_want.clone();
                off[i] = (off[i] + 1) % 256;
                assert!(
                    ws6_1_check(&lane, w8, &off).is_err(),
                    "{lane}: the differential must REJECT expectation {i} off by one"
                );
            }
        }
    }
}

/// WS6.1's review vectors (literal cells, wide heap `Nat`s, `UInt32`/`USize`
/// readers) as a value oracle through both lanes at `-O1` and `-O2`. Their
/// mutation controls stay at `-O0` (`test_ws6_1_review_literal_and_wide_
/// heap_nat_vectors`), where the literal roots still read a boxed `Nat`.
#[test]
fn test_ws6_4_ws6_1_review_oracle_at_o1_o2() {
    let Some(host) = ws6_1_host() else {
        eprintln!("WS6.1 review oracle skipped: unsupported host arch");
        // SELF-SKIP OK: host-arch precondition -- the native C / trust-cg lanes only target aarch64 and x86_64; on any other ARCH there is nothing to link or run (skip is logged)
        return;
    };
    let trust_cg = find_trust_cg();
    let dir = tempfile::tempdir().expect("tempdir");
    for (level, pipeline) in optimizing() {
        let art = ws6_1_review_artifacts_at(&pipeline);
        let tag = level.trim_start_matches('-');
        let got = ws6_1_review_run_c(&art, dir.path(), &format!("review_c_{tag}"), host.1);
        ws6_1_check(&format!("emit_c {level}"), &got, &WS6_1_REVIEW_WANT)
            .unwrap_or_else(|e| panic!("{e}"));
        let Some(cg) = &trust_cg else {
            eprintln!("{level}: review trust-ir lane skipped: trust-cg binary not found");
            continue;
        };
        let module = art
            .emit_trust_ir(&ws6_1_extern_config())
            .expect("review closure lowers to trust-ir");
        let got = ws6_1_review_run_ti(&module, cg, dir.path(), &format!("review_ti_{tag}"), host);
        ws6_1_check(&format!("trust-ir {level}"), &got, &WS6_1_REVIEW_WANT)
            .unwrap_or_else(|e| panic!("{e}"));
    }
}

/// The battery roots' kernel-TV verdicts, `(certified, skipped-with-reason)`.
fn battery_tv(pipeline: &PipelineConfig) -> (Vec<String>, Vec<(String, String)>) {
    use crate::pass_manager::compile_lcnf_to_trust_ir_with_report;
    let env = elaborated_env_with(BATTERY_SOURCE);
    let decls = closure_decls_of(&env, pipeline, &BATTERY_ROOTS);
    let cfg = TrustIrConfig {
        certify_translation: true,
        ..ws6_4_config()
    };
    let (_, report) = compile_lcnf_to_trust_ir_with_report(&decls, &env, pipeline, &cfg)
        .expect("the battery closure lowers and mints");
    let root = |n: &str| BATTERY_ROOTS.contains(&n);
    let mut certified: Vec<String> = report.certified.into_iter().filter(|n| root(n)).collect();
    certified.sort();
    let mut skipped: Vec<(String, String)> = report
        .skipped
        .into_iter()
        .filter(|(n, _)| root(n))
        .collect();
    skipped.sort();
    (certified, skipped)
}

/// RATCHET (the increment's "Closes" line): the TV skip reasons "named
/// callee not TV-certifiable" (`inc2`) and "operand not resolvable to
/// bvVar" (`w32`) — and the boxed-arithmetic skips of `inc`/`w8`/`w16` — are
/// gone at `-O1`/`-O2`, where those five roots are now KERNEL-certified (so
/// the rule and the `UIntW.ofNat` fold are kernel-checked by the TV equation
/// for them). `-O0` keeps every root skipped. WS6.6 then taught the source
/// denoter `let` (zeta), which moved `sqLet` to certified at `-O1`/`-O2`
/// (its emitted body was already `add; mul; ret`). The one remaining skip is
/// WS6.6's mixed-width slice (WS1.15 S5, `pickWide`), pinned exactly so any
/// change of shape is visible.
#[test]
fn test_ws6_4_battery_tv_status_by_level() {
    let (certified, skipped) = battery_tv(&o0());
    assert_eq!(certified, Vec::<String>::new(), "-O0 certifies no root");
    let reason = |root: &str| {
        skipped
            .iter()
            .find(|(n, _)| n == root)
            .map(|(_, r)| r.clone())
            .unwrap_or_else(|| panic!("-O0: `{root}` must be skipped"))
    };
    assert!(reason("inc2").contains("a named callee is not TV-certifiable"));
    assert!(reason("w32").contains("not resolvable to a bvVar/bvConst"));
    assert_eq!(skipped.len(), BATTERY_ROOTS.len(), "-O0: {skipped:?}");

    for (level, pipeline) in optimizing() {
        let (certified, skipped) = battery_tv(&pipeline);
        assert_eq!(
            certified,
            ["inc", "inc2", "sqLet", "w16", "w32", "w8"],
            "{level}: kernel-certified roots"
        );
        let got: Vec<(&str, bool)> = skipped
            .iter()
            .map(|(n, r)| {
                let expected = match n.as_str() {
                    "pickWide" => r.contains("parameter type u8"),
                    _ => false,
                };
                (n.as_str(), expected)
            })
            .collect();
        assert_eq!(
            got,
            [("pickWide", true)],
            "{level}: remaining skips: {skipped:?}"
        );
    }
}

// ---- review: fields `to_mono` would rewrite, wide literals -------------

/// Adversarial review sources. `MyS`'s instance field is `Nat.succ` and
/// `MkW`'s a TRIVIAL-structure constructor (`Wrap` has one relevant field,
/// so at runtime a `Wrap` IS its `Nat`): both are closed constants of the
/// right type, so rule clauses 1–4 hold, but `to_mono` rewrites each at a
/// source-level call (`Nat.succ n` → `Nat.add n 1`, `Wrap.mk n` → `n`).
/// Resolved raw after `to_mono`, the first became `clean_alloc_ctor(1, 1,
/// 0, n)` where a `Nat` was expected and the second a heap cell where the
/// bare `Nat` was. `MkI`'s field `Int.ofNat` (a non-trivial constructor,
/// which `to_mono` leaves alone) is the twin that must still resolve.
const REVIEW_SOURCE: &str = "class MyS (α : Type) where\n  s : α → α\n\
instance instMySNat : MyS Nat := ⟨Nat.succ⟩\n\
def useS (n : Nat) : Nat := @MyS.s Nat instMySNat n\n\
structure Wrap where\n  v : Nat\n\
class MkW (α : Type) where\n  make : Nat → α\n\
instance instMkWrap : MkW Wrap := ⟨Wrap.mk⟩\n\
def useW (n : Nat) : Wrap := @MkW.make Wrap instMkWrap n\n\
def useWv (n : Nat) : Nat := (@MkW.make Wrap instMkWrap n).v\n\
class MkI where\n  make : Nat → Int\n\
instance instMkI : MkI := ⟨Int.ofNat⟩\n\
def useI (n : Nat) : Int := @MkI.make instMkI n\n\
def big64 : UInt64 := 18446744073709551615\n\
def wrap64 : UInt64 := 18446744073709551619\n\
def lit8 : UInt8 := 300\n\
def addBig (a : UInt64) : UInt64 := a + 18446744073709551615\n";

const REVIEW_ROOTS: [&str; 8] = [
    "useS", "useW", "useWv", "useI", "big64", "wrap64", "lit8", "addBig",
];

fn review_levels() -> [(&'static str, PipelineConfig); 3] {
    [
        ("-O0", o0()),
        ("-O1", PipelineConfig::default()),
        ("-O2", o2()),
    ]
}

/// Structural: the fields `to_mono` would rewrite keep their dynamic
/// class-method call at every level (a missed optimization, never a raw
/// constructor cell), while the `Int.ofNat` twin resolves at `-O1`/`-O2`.
#[test]
fn test_ws6_4_review_fields_to_mono_rewrites_are_not_resolved_raw() {
    for (level, pipeline) in optimizing() {
        let module = module_of(REVIEW_SOURCE, &["useS", "useW", "useWv", "useI"], &pipeline);
        for (root, method) in [
            ("useS", "MyS.s"),
            ("useW", "MkW.make"),
            ("useWv", "MkW.make"),
        ] {
            let calls = callees(&module, function(&module, root));
            assert!(
                calls.iter().any(|c| c == method),
                "{level}: `{root}` must keep its dynamic `{method}` call: {calls:?}"
            );
        }
        let calls = callees(&module, function(&module, "useI"));
        assert!(
            !calls.iter().any(|c| c == "MkI.make"),
            "{level}: `useI` (field `Int.ofNat`, left alone by to_mono) must resolve: {calls:?}"
        );
    }
}

/// Differential value oracle through `--emit c`: the review roots compute
/// the kernel's values — `useS 5 = 6`, `(useW 5).v = useWv 5 = 5` (a `Wrap`
/// is its `Nat`) at `-O0` (no resolution), `-O1` and `-O2`, and, at the
/// optimizing levels where the `UIntW.ofNat` fold runs, `2^64-1`,
/// `(2^64+3) mod 2^64 = 3`, `300 mod 256 = 44`, `(1 + (2^64-1)) mod 2^64 = 0`.
/// (The `UInt64` roots are not linked at `-O0`: there they call prelude
/// `UInt64.ofNat`/`HAdd.hAdd` shims this C lane does not provide.) Before
/// the review fix `useS`/`useW`/`useWv` returned constructor cells at
/// `-O1`/`-O2`.
#[test]
fn test_ws6_4_review_differential_values_across_levels() {
    let Some(host) = ws6_1_host() else {
        eprintln!("WS6.4 review oracle skipped: unsupported host arch");
        // SELF-SKIP OK: host-arch precondition -- the native C lane only targets aarch64 and x86_64; on any other ARCH there is nothing to link or run (skip is logged)
        return;
    };
    let m = |s: &str| crate::mangle::mangle_name(&Name::from_string(s));
    let nat_main = format!(
        "static void pr(clean_obj* o) {{ if (clean_is_scalar(o)) printf(\"%zu \", clean_unbox(o)); \
         else printf(\"cell%u \", (unsigned)clean_obj_tag(o)); }}\n\
         static void nat_roots(void) {{ pr({s}(clean_box(5))); pr({w}(clean_box(5))); \
         pr({wv}(clean_box(5))); }}\n",
        s = m("useS"),
        w = m("useW"),
        wv = m("useWv"),
    );
    let uint_main = format!(
        "static void uint_roots(void) {{ printf(\"%llu %llu %u %llu\", \
         (unsigned long long){b}(), (unsigned long long){w64}(), (unsigned){l8}(), \
         (unsigned long long){ab}(1)); }}\n",
        b = m("big64"),
        w64 = m("wrap64"),
        l8 = m("lit8"),
        ab = m("addBig"),
    );
    let nat_want: [u64; 3] = [6, 5, 5];
    let uint_want: [u64; 4] = [u64::MAX, 3, 44, 0];
    let dir = tempfile::tempdir().expect("tempdir");
    let env = elaborated_env_with(REVIEW_SOURCE);
    for (level, pipeline) in review_levels() {
        let with_uint = level != "-O0";
        // The `UInt64` roots' closure reaches the prelude `UInt64.ofNat` /
        // `UInt64.toNat` through `UInt64.add`'s body; compile them as roots so
        // the C lane links.
        let mut roots = vec!["useS", "useW", "useWv"];
        if with_uint {
            roots.extend(&REVIEW_ROOTS[3..]);
            roots.extend(["UInt64.ofNat", "UInt64.toNat"]);
        }
        let decls = closure_decls_of(&env, &pipeline, &roots);
        let c_code = compile_lcnf_decls(&decls, &env, &pipeline)
            .expect("the review closure compiles")
            .emit_c(crate::emit_c::CEmitConfig::default())
            .expect("the review closure lowers to C");
        let (uint_fn, uint_call) = if with_uint {
            (uint_main.as_str(), "uint_roots();")
        } else {
            ("", "")
        };
        let tu = format!(
            "#include <stdio.h>\n#include <stdint.h>\n#include \"clean_runtime.h\"\n\
             {WS6_1_NAT_SHIMS_C}\n{c_code}\n{nat_main}{uint_fn}\
             int main(void) {{ nat_roots(); {uint_call} printf(\"\\n\"); return 0; }}\n"
        );
        let tag = level.trim_start_matches('-');
        let got = ws6_1_build_and_run(
            dir.path(),
            &format!("ws64_review_{tag}"),
            &[("tu.c", tu)],
            &[],
            host.1,
        );
        let mut want = nat_want.to_vec();
        if with_uint {
            want.extend(uint_want);
        }
        ws6_1_check(&format!("emit_c {level}"), &got, &want).unwrap_or_else(|e| panic!("{e}"));
        // Mutation control on the comparator: `useS` off by one is rejected.
        let mut off = want.clone();
        off[0] = 5;
        assert!(ws6_1_check(level, &got, &off).is_err());
    }
}

/// Structural: the wide literal roots fold to returned constants at
/// `-O1`/`-O2` (the `UIntW.ofNat` fold on a two-limb and a `> i64::MAX`
/// literal), so the differential above exercises the fold, not a call.
#[test]
fn test_ws6_4_review_wide_literals_fold_to_constants() {
    for (level, pipeline) in optimizing() {
        let module = module_of(REVIEW_SOURCE, &["big64", "wrap64", "lit8"], &pipeline);
        for (root, want) in [("big64", i128::from(u64::MAX)), ("wrap64", 3), ("lit8", 44)] {
            let f = function(&module, root);
            let got = match returned_const(f) {
                Some(v) if v < 0 => v + (1i128 << 64),
                other => other.unwrap_or(-1),
            };
            assert_eq!(got, want, "{level}: `{root}`: {:?}", f.blocks);
        }
    }
}

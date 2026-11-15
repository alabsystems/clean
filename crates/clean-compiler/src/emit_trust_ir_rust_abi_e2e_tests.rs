// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! C1 and C2 on real island source through `compile_rust_abi`: scalar
//! primitives at the machine type, and Rust callees called directly at the
//! carrier ABI. Each subject is also run on the trust-ir reference
//! interpreter over the design's edge inputs (§6: 0, 1, MAX, MAX-1, wrapping
//! pairs) where the module has no bodyless callee.

use super::*;
use trust_ir::inst::{BinOp, ICmpOp};
use trust_ir::interpret::{InterpretValue, Interpreter};

const SHAPES: &str = "def fstIsl (a b : UInt64) : UInt64 := a\n\
def k7 (a : UInt8) : UInt8 := 7\n\
def comp16 (a b : UInt16) : UInt16 := (a + b) * a\n\
def cleanMin (a b : UInt64) : UInt64 := if a ≤ b then a else b\n\
def selLit (a b : UInt32) : UInt32 := if a < 10 then a else b\n\
def ltU8 (a b : UInt8) : Bool := decide (a < b)\n\
def eq32 (a b : UInt32) : Bool := a == b\n\
def selBeq (a b : UInt64) : UInt64 := if a == b then 1 else 0\n\
def bnot (a : Bool) : Bool := !a\n\
def band (a b : Bool) : Bool := a && b\n\
def bor (a b : Bool) : Bool := a || b\n\
def bxor (a b : Bool) : Bool := Bool.xor a b\n";

fn int(ty: &Ty, v: u64) -> InterpretValue {
    InterpretValue::int(ty.clone(), i128::from(v)).expect("in range")
}

/// Run `name` of a module with no bodyless callee on the reference
/// interpreter.
fn run(module: &Module, name: &str, args: Vec<InterpretValue>) -> InterpretValue {
    let f = function(module, name);
    let out = Interpreter::with_module(module)
        .execute_function(f, args)
        .unwrap_or_else(|e| panic!("interpreting `{name}`: {e}"));
    out.returns.into_iter().next().expect("one result")
}

fn as_u64(v: &InterpretValue) -> u64 {
    v.as_int().expect("an integer").as_unsigned() as u64
}

/// C1, subject 1: `a + b` at `UInt64` is ONE `add` at every level, the
/// module holds nothing else, and it computes `a + b mod 2^64`.
#[test]
fn c1_wsum_is_one_add_at_every_level() {
    let env = island_env(&[], WSUM);
    for (level, pipeline) in levels() {
        let out = rust_abi(&env, &["cleanWsum"], &[], &pipeline)
            .unwrap_or_else(|e| panic!("{level}: {e}"));
        eprintln!(
            "===== cleanWsum {level} — Trust general lane today =====\n{}\n\
             ===== cleanWsum {level} — Rust ABI =====\n{}",
            general_lane(&env, &["cleanWsum"], &pipeline),
            out.module
        );
        let f = function(&out.module, "cleanWsum");
        assert_eq!(
            insts(f),
            vec![
                &Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::U64,
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(1),
                },
                &Inst::Return {
                    values: vec![ValueId::new(2)],
                },
            ],
            "{level}: one add, no call"
        );
        assert_eq!(
            out.module.functions.len(),
            1,
            "{level}: no import, no wrapper"
        );
        assert!(!out.handle_bearing);
        // The in-process kernel TV self-check decided this body against the
        // definition (and its certificate was discarded: none is attached).
        assert!(
            out.rows[0].kernel_tv_self_check,
            "{level}: kernel TV self-check"
        );
        assert!(out.module.proof_certificates.is_empty());
        let m = u64::MAX;
        for (a, b) in [
            (0, 0),
            (1, 2),
            (m, 1),
            (m, m),
            (m - 1, 3),
            (1 << 63, 1 << 63),
        ] {
            let r = run(
                &out.module,
                "cleanWsum",
                vec![int(&Ty::U64, a), int(&Ty::U64, b)],
            );
            assert_eq!(
                as_u64(&r),
                a.wrapping_add(b),
                "{level}: cleanWsum({a}, {b})"
            );
        }
    }
}

/// C1: the planner battery's scalar and `Bool` shapes are native
/// instructions with no call, at every level, and compute their Lean values.
#[test]
fn c1_scalar_shapes_lower_to_native_instructions() {
    let env = island_env(&[], SHAPES);
    let roots = [
        "fstIsl", "k7", "comp16", "cleanMin", "selLit", "ltU8", "eq32", "selBeq", "bnot", "band",
        "bor", "bxor",
    ];
    for (level, pipeline) in levels() {
        let out = rust_abi(&env, &roots, &[], &pipeline).unwrap_or_else(|e| panic!("{level}: {e}"));
        let m = &out.module;
        for root in roots {
            let f = function(m, root);
            assert!(
                called(m, f).is_empty(),
                "{level}: `{root}` must make no call:\n{f}"
            );
        }
        assert_eq!(
            m.functions.len(),
            roots.len(),
            "{level}: nothing but the roots"
        );
        let has = |root: &str, want: &dyn Fn(&Inst) -> bool| {
            assert!(
                insts(function(m, root)).into_iter().any(want),
                "{level}: `{root}` lacks its native instruction:\n{}",
                function(m, root)
            );
        };
        has("comp16", &|i| {
            matches!(
                i,
                Inst::BinOp {
                    op: BinOp::Mul,
                    ty: Ty::U16,
                    ..
                }
            )
        });
        has("cleanMin", &|i| {
            matches!(
                i,
                Inst::ICmp {
                    op: ICmpOp::Ule,
                    ty: Ty::U64,
                    ..
                }
            )
        });
        has("selLit", &|i| {
            matches!(
                i,
                Inst::ICmp {
                    op: ICmpOp::Ult,
                    ty: Ty::U32,
                    ..
                }
            )
        });
        has("ltU8", &|i| {
            matches!(
                i,
                Inst::ICmp {
                    op: ICmpOp::Ult,
                    ty: Ty::U8,
                    ..
                }
            )
        });
        has("eq32", &|i| {
            matches!(
                i,
                Inst::ICmp {
                    op: ICmpOp::Eq,
                    ty: Ty::U32,
                    ..
                }
            )
        });
        has("selBeq", &|i| {
            matches!(
                i,
                Inst::ICmp {
                    op: ICmpOp::Eq,
                    ty: Ty::U64,
                    ..
                }
            )
        });
        for root in ["bnot", "band", "bor", "bxor"] {
            has(root, &|i| matches!(i, Inst::Select { ty: Ty::Bool, .. }));
        }

        // Values, on the edge inputs.
        let u = |ty: &Ty, v: u64| int(ty, v);
        let max = u64::MAX;
        for (a, b) in [
            (0u64, 0u64),
            (0, 1),
            (1, 0),
            (max, max - 1),
            (max - 1, max),
            (7, 7),
        ] {
            let r = run(m, "cleanMin", vec![u(&Ty::U64, a), u(&Ty::U64, b)]);
            assert_eq!(as_u64(&r), a.min(b), "{level}: cleanMin({a}, {b})");
            let r = run(m, "selBeq", vec![u(&Ty::U64, a), u(&Ty::U64, b)]);
            assert_eq!(as_u64(&r), u64::from(a == b), "{level}: selBeq({a}, {b})");
            let r = run(m, "fstIsl", vec![u(&Ty::U64, a), u(&Ty::U64, b)]);
            assert_eq!(as_u64(&r), a, "{level}: fstIsl({a}, {b})");
        }
        for (a, b) in [
            (0u64, 0u64),
            (9, 3),
            (10, 3),
            (u32::MAX as u64, 0),
            (11, 12),
        ] {
            let r = run(m, "selLit", vec![u(&Ty::U32, a), u(&Ty::U32, b)]);
            assert_eq!(
                as_u64(&r),
                if a < 10 { a } else { b },
                "{level}: selLit({a}, {b})"
            );
            let r = run(m, "eq32", vec![u(&Ty::U32, a), u(&Ty::U32, b)]);
            assert_eq!(r.as_bool(), Some(a == b), "{level}: eq32({a}, {b})");
        }
        for (a, b) in [(0u64, 0u64), (0, 255), (255, 0), (254, 255), (200, 100)] {
            let r = run(m, "ltU8", vec![u(&Ty::U8, a), u(&Ty::U8, b)]);
            assert_eq!(r.as_bool(), Some(a < b), "{level}: ltU8({a}, {b})");
            let r = run(m, "k7", vec![u(&Ty::U8, a)]);
            assert_eq!(as_u64(&r), 7, "{level}: k7({a})");
        }
        for (a, b) in [(0u64, 0u64), (1, 2), (u16::MAX as u64, 1), (300, 300)] {
            let r = run(m, "comp16", vec![u(&Ty::U16, a), u(&Ty::U16, b)]);
            let want = (a as u16).wrapping_add(b as u16).wrapping_mul(a as u16);
            assert_eq!(as_u64(&r), u64::from(want), "{level}: comp16({a}, {b})");
        }
        for a in [false, true] {
            let r = run(m, "bnot", vec![InterpretValue::bool(a)]);
            assert_eq!(r.as_bool(), Some(!a), "{level}: bnot({a})");
            for b in [false, true] {
                let args = || vec![InterpretValue::bool(a), InterpretValue::bool(b)];
                assert_eq!(
                    run(m, "band", args()).as_bool(),
                    Some(a && b),
                    "{level}: band"
                );
                assert_eq!(
                    run(m, "bor", args()).as_bool(),
                    Some(a || b),
                    "{level}: bor"
                );
                assert_eq!(
                    run(m, "bxor", args()).as_bool(),
                    Some(a ^ b),
                    "{level}: bxor"
                );
            }
        }
    }
}

const LEAN_CALLS_RUST: &str = "def twice_inc (x : UInt64) : UInt64 := inc (inc x)\n\
def inc_dbl (x : UInt64) : UInt64 := dbl (inc x)\n\
def diff (a b : UInt64) : UInt64 := sub2 a b\n\
def minus5 (x : UInt64) : UInt64 := sub2 x 5\n\
def quarter (x : UInt32) : UInt32 := half32 (half32 x)\n\
def small_half (x : UInt32) : Bool := is_small (half32 x)\n";

fn r18_env() -> Environment {
    island_env(
        &[
            ("inc", &["UInt64"], "UInt64"),
            ("dbl", &["UInt64"], "UInt64"),
            ("sub2", &["UInt64", "UInt64"], "UInt64"),
            ("half32", &["UInt32"], "UInt32"),
            ("is_small", &["UInt32"], "Bool"),
        ],
        LEAN_CALLS_RUST,
    )
}

/// C2, subject 2: `inc (inc x)` is two direct calls of the Rust symbol at
/// `(u64) -> u64`; no box, no `l_inc`, no Clean runtime.
#[test]
fn c2_twice_inc_calls_rust_at_the_carrier_abi() {
    let env = island_env(&[("inc", &["UInt64"], "UInt64")], TWICE_INC);
    let sym = rust_symbol("inc");
    for (level, pipeline) in levels() {
        let out = rust_abi(&env, &["twice_inc"], &["inc"], &pipeline)
            .unwrap_or_else(|e| panic!("{level}: {e}"));
        eprintln!(
            "===== twice_inc {level} — Trust general lane today =====\n{}\n\
             ===== twice_inc {level} — Rust ABI =====\n{}",
            general_lane(&env, &["twice_inc"], &pipeline),
            out.module
        );
        let m = &out.module;
        let callee = m
            .functions
            .iter()
            .find(|f| f.name == sym)
            .unwrap_or_else(|| panic!("{level}: the Rust symbol is declared"));
        assert!(
            callee.is_declaration(),
            "{level}: the Rust callee has no body here"
        );
        assert_eq!(callee.display_path.as_deref(), Some("inc"));
        assert_eq!(callee.calling_conv, trust_ir::CallingConv::Rust, "{level}");
        let callee_ty = m.func_type(callee.ty).expect("signature");
        assert_eq!(callee_ty.params, vec![Ty::U64]);
        assert_eq!(callee_ty.returns, vec![Ty::U64]);
        let f = function(m, "twice_inc");
        assert_eq!(
            insts(f),
            vec![
                &Inst::Call {
                    callee: callee.id,
                    args: vec![ValueId::new(0)],
                },
                &Inst::Call {
                    callee: callee.id,
                    args: vec![ValueId::new(1)],
                },
                &Inst::Return {
                    values: vec![ValueId::new(2)],
                },
            ],
            "{level}: call @inc; call @inc; ret"
        );
        assert_eq!(
            m.functions.len(),
            2,
            "{level}: the root and the Rust callee only"
        );
    }
}

/// C2 over r18's whole program: two different callees in both orders, a
/// two-argument callee in source argument ORDER, a numeral operand, and the
/// `u32` and `bool` carriers.
#[test]
fn c2_lean_calls_rust_battery() {
    let env = r18_env();
    let roots = [
        "twice_inc",
        "inc_dbl",
        "diff",
        "minus5",
        "quarter",
        "small_half",
    ];
    let callees = ["inc", "dbl", "sub2", "half32", "is_small"];
    for (level, pipeline) in levels() {
        let out =
            rust_abi(&env, &roots, &callees, &pipeline).unwrap_or_else(|e| panic!("{level}: {e}"));
        let m = &out.module;
        let s = |n: &str| rust_symbol(n);
        assert_eq!(
            called(m, function(m, "inc_dbl")),
            vec![s("inc"), s("dbl")],
            "{level}"
        );
        assert_eq!(
            called(m, function(m, "quarter")),
            vec![s("half32"), s("half32")],
            "{level}"
        );
        assert_eq!(
            called(m, function(m, "small_half")),
            vec![s("half32"), s("is_small")],
            "{level}"
        );
        // `sub2 a b`, not `sub2 b a`: the argument order is the source's.
        let diff = function(m, "diff");
        assert!(
            insts(diff)
                .iter()
                .any(|i| matches!(i, Inst::Call { args, .. }
                if *args == vec![ValueId::new(0), ValueId::new(1)])),
            "{level}: diff passes (a, b) in order:\n{diff}"
        );
        // The numeral is a `u64` constant at the callee's carrier.
        let minus5 = function(m, "minus5");
        assert!(
            minus5.blocks[0].body.iter().any(|n| matches!(
                &n.inst,
                Inst::Const {
                    ty: Ty::U64,
                    value: trust_ir::Constant::Int(5)
                }
            )),
            "{level}: minus5's operand is `5 : u64`:\n{minus5}"
        );
        let is_small = m
            .functions
            .iter()
            .find(|f| f.name == s("is_small"))
            .expect("is_small declared");
        let ty = m.func_type(is_small.ty).expect("signature");
        assert_eq!(
            (ty.params.clone(), ty.returns.clone()),
            (vec![Ty::U32], vec![Ty::Bool])
        );
        for root in roots {
            assert!(
                called(m, function(m, root))
                    .iter()
                    .all(|c| c.starts_with("_ZN4r18_")),
                "{level}: `{root}` calls only Rust symbols"
            );
        }
    }
}

/// The hidden inhabitant of a Rust callee is never what a call compiles to:
/// a callee that is not declared as one is REFUSED by name (the general
/// pipeline would have compiled its opaque value), and a declared callee
/// cannot also be a root.
#[test]
fn c2_an_undeclared_rust_callee_is_refused_by_name() {
    let env = island_env(&[("inc", &["UInt64"], "UInt64")], TWICE_INC);
    let err = rust_abi(&env, &["twice_inc"], &[], &PipelineConfig::default())
        .expect_err("`inc` is not a declared Rust callee");
    let text = err.to_string();
    assert!(
        text.contains("`twice_inc`") && text.contains("calls `inc`"),
        "{text}"
    );
    let err = rust_abi(
        &env,
        &["twice_inc", "inc"],
        &["inc"],
        &PipelineConfig::default(),
    )
    .expect_err("a root cannot be a Rust callee");
    assert!(matches!(err, RustAbiError::Conflict { .. }), "{err}");
}

/// A body outside the carrier closure is refused by name, never lowered
/// through the C runtime: a `String`-typed root, and a call to a prelude
/// function that is no primitive.
#[test]
fn c1_outside_the_carrier_closure_is_refused_by_name() {
    let env = island_env(
        &[],
        "def strLen (s : String) : Nat := s.length\n\
         def viaPred (a : UInt64) : UInt64 := UInt64.ofNat (Nat.pred a.toNat)\n",
    );
    let err = rust_abi(&env, &["strLen"], &[], &PipelineConfig::default())
        .expect_err("String is no carrier");
    assert!(matches!(err, RustAbiError::NotACarrier { .. }), "{err}");
    let err = rust_abi(&env, &["viaPred"], &[], &PipelineConfig::default())
        .expect_err("Nat.pred / UInt64.ofNat are no carrier primitive");
    let text = err.to_string();
    assert!(
        text.contains("`viaPred`") && text.contains("Options"),
        "{text}"
    );
}

/// C3: each root's emitted `FuncTy` IS its carrier signature, and the row
/// discloses it.
#[test]
fn c3_root_signatures_are_carrier_signatures() {
    let env = r18_env();
    let out = rust_abi(
        &env,
        &["diff", "small_half"],
        &["sub2", "half32", "is_small"],
        &PipelineConfig::default(),
    )
    .expect("compiles");
    for row in &out.rows {
        let f = out
            .module
            .functions
            .iter()
            .find(|f| f.id == row.func_id)
            .expect("row function");
        assert_eq!(f.name, row.symbol);
        assert_eq!(
            Some(&row.signature),
            crate::rust_abi::carrier_signature(&env, &row.declaration)
                .ok()
                .as_ref()
        );
        assert_eq!(
            f.body_gate,
            Some(BodyGate::Ungated),
            "no claim leaves the core"
        );
        // A Rust caller calls it as a Rust `fn` (Trust's join refuses a
        // convention mismatch between a declaration and its definition).
        assert_eq!(f.calling_conv, trust_ir::CallingConv::Rust);
    }
    assert!(out.module.proof_obligations.is_empty() && out.module.proof_certificates.is_empty());
}

#[test]
fn c1_integer_masks_get_kernel_tv_at_every_width_and_pipeline_level() {
    let source: String = [8, 16, 32, 64]
        .into_iter()
        .map(|w| {
            format!("def mask{w} (a b : UInt{w}) : UInt{w} := UInt{w}.lor (UInt{w}.land a b) 1\n")
        })
        .collect();
    let env = island_env(&[], &source);
    let names = ["mask8", "mask16", "mask32", "mask64"];
    for (level, pipeline) in levels() {
        let out = rust_abi(&env, &names, &[], &pipeline)
            .unwrap_or_else(|error| panic!("{level}: {error}"));
        assert_eq!(out.rows.len(), 4);
        assert!(
            out.rows.iter().all(|row| row.kernel_tv_self_check),
            "{level}: every actual emitted body must earn its kernel self-check"
        );
        for (name, width, ty) in [
            ("mask8", 8, Ty::U8),
            ("mask16", 16, Ty::U16),
            ("mask32", 32, Ty::U32),
            ("mask64", 64, Ty::U64),
        ] {
            let f = function(&out.module, name);
            assert!(called(&out.module, f).is_empty());
            assert!(insts(f)
                .iter()
                .any(|node| matches!(node, Inst::BinOp { op: BinOp::And, .. })));
            assert!(insts(f)
                .iter()
                .any(|node| matches!(node, Inst::BinOp { op: BinOp::Or, .. })));
            let max = if width == 64 {
                u64::MAX
            } else {
                (1u64 << width) - 1
            };
            for (a, b) in [(0, 0), (1, 0), (max, max), (max, 1), (max - 1, 3)] {
                let result = run(&out.module, name, vec![int(&ty, a), int(&ty, b)]);
                assert_eq!(as_u64(&result), (a & b) | 1, "{level}: {name}({a},{b})");
            }
        }
    }
}

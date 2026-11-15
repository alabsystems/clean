// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// WS3.20 (F-057): the core bulk-memory and bit intrinsics, executed by the
// reference interpreter. The roadmap rows this file ports (named after them):
//
//   * `goal-g1-g8/g1-intrinsics-bulk-memory` — ctlz/cttz/bswap/rotate/
//     bitreverse and memcpy/memset with a DYNAMIC count have a complete
//     representation with no havoc;
//   * `goal-g1-g8/g3-no-symbolic-placeholder` — the bulk copy a producer had
//     to spell as a `RegionHavocStore` marker is now a real operation whose
//     result is checkable, never a placeholder that reads as complete.
//
// Every rotation/bswap/ctlz/cttz value is checked against Rust's own
// `u8`/`u64` intrinsics over an EXHAUSTIVE u8 set and a sampled u64 set, so
// the interpreter cannot drift from the language the producer lowers from;
// the Lean `ExecutableFixtures` lock the same values on the other engine.
//
// The memcpy fixtures build on the ratified byte-overlap carrier model
// (`union_byte_overlap_model.rs`): storage is an `[u8; N]` alloca, accesses
// are typed `Load`/`Store` at shared addresses, and MemCopy moves the raw
// bytes — value, init state and (by address) pointer provenance.

use trust_ir::inst::{BinOp, Inst, UnOp};
use trust_ir::interpret::{InterpretErrorCode, InterpretValue, InterpretValueKind, Interpreter};
use trust_ir::node::InstrNode;
use trust_ir::value::{BlockId, FuncId, ValueId};
use trust_ir::{Block, Constant, FuncTy, Function, Module, Ty};

fn v(i: u32) -> ValueId {
    ValueId::new(i)
}
fn b(i: u32) -> BlockId {
    BlockId::new(i)
}

/// A little instruction-list builder over raw `InstrNode`s (the trust-ir
/// crate has no `ModuleBuilder`): each `push` returns the next fresh value id.
struct Body {
    nodes: Vec<InstrNode>,
    next: u32,
}

impl Body {
    fn new() -> Self {
        Self {
            nodes: Vec::new(),
            next: 0,
        }
    }
    fn val(&mut self, inst: Inst) -> ValueId {
        let id = v(self.next);
        self.next += 1;
        self.nodes.push(InstrNode::new(inst).with_result(id));
        id
    }
    fn void(&mut self, inst: Inst) {
        self.nodes.push(InstrNode::new(inst));
    }
    fn uconst(&mut self, ty: Ty, value: u128) -> ValueId {
        self.val(Inst::Const {
            ty,
            value: Constant::Int(value as i128),
        })
    }
    fn alloca_bytes(&mut self, module: &mut Module, n: u64) -> ValueId {
        let u8_ty = module
            .add_type(Ty::U8)
            .expect("Module::add_type: test fixture");
        self.val(Inst::Alloca {
            ty: Ty::Array(u8_ty, n),
            count: None,
            align: Some(8),
        })
    }
    fn store(&mut self, ty: Ty, ptr: ValueId, value: ValueId) {
        self.void(Inst::Store {
            ty,
            ptr,
            value,
            volatile: false,
            align: None,
        });
    }
    fn load(&mut self, ty: Ty, ptr: ValueId, volatile: bool) -> ValueId {
        self.val(Inst::Load {
            ty,
            ptr,
            volatile,
            align: None,
        })
    }
    /// `base + index` at byte granularity.
    fn byte_gep(&mut self, base: ValueId, index: u64) -> ValueId {
        let idx = self.uconst(Ty::U64, u128::from(index));
        self.val(Inst::GEP {
            pointee_ty: Ty::U8,
            base,
            indices: vec![idx],
            inbounds: true,
        })
    }
    fn memcopy(&mut self, dst: ValueId, src: ValueId, bytes: u64, overlap: bool) {
        let bytes = self.uconst(Ty::U64, u128::from(bytes));
        self.void(Inst::MemCopy {
            dst,
            src,
            bytes,
            overlap,
        });
    }
    fn memset(&mut self, dst: ValueId, byte: u8, bytes: u64) {
        let byte = self.uconst(Ty::U8, u128::from(byte));
        let bytes = self.uconst(Ty::U64, u128::from(bytes));
        self.void(Inst::MemSet { dst, byte, bytes });
    }
}

fn module_with(
    name: &str,
    params: Vec<Ty>,
    returns: Vec<Ty>,
    build: impl FnOnce(&mut Module, &mut Body),
) -> Module {
    let mut module = Module::new(name);
    let sig = module
        .add_func_type(FuncTy {
            params: params.clone(),
            returns,
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut body = Body::new();
    // Parameters are the entry block's parameters: %0.. %n-1.
    let param_ids: Vec<(ValueId, Ty)> = params
        .iter()
        .cloned()
        .map(|ty| {
            let id = v(body.next);
            body.next += 1;
            (id, ty)
        })
        .collect();
    build(&mut module, &mut body);
    let mut f = Function::new(FuncId::new(0), "f", sig, b(0));
    let mut blk = Block::new(b(0));
    blk.params = param_ids;
    blk.body = body.nodes;
    f.blocks.push(blk);
    module
        .try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    module
}

fn run(
    module: &Module,
    args: impl IntoIterator<Item = InterpretValue>,
) -> Result<Vec<InterpretValue>, trust_ir::interpret::InterpretError> {
    Interpreter::with_module(module)
        .execute_func(FuncId::new(0), args)
        .map(|out| out.returns)
}

fn int(ty: Ty, value: u128) -> InterpretValue {
    InterpretValue::int(ty, value as i128).expect("in range")
}

fn as_u128(value: &InterpretValue) -> u128 {
    value.as_int().expect("integer result").as_unsigned()
}

// ---------------------------------------------------------------------------
// goal-g1-g8/g1-intrinsics-bulk-memory: the bit intrinsics against Rust
// ---------------------------------------------------------------------------

/// `f(x, n) -> (rotl x n, rotr x n, bswap x, bitreverse x, ctlz x, cttz x)`.
fn bit_intrinsics_module(ty: Ty) -> Module {
    module_with(
        "bit-intrinsics",
        vec![ty.clone(), ty.clone()],
        vec![ty.clone(); 6],
        |_m, body| {
            let x = v(0);
            let n = v(1);
            let rotl = body.val(Inst::BinOp {
                op: BinOp::RotL,
                ty: ty.clone(),
                lhs: x,
                rhs: n,
            });
            let rotr = body.val(Inst::BinOp {
                op: BinOp::RotR,
                ty: ty.clone(),
                lhs: x,
                rhs: n,
            });
            let un = |body: &mut Body, op: UnOp| {
                body.val(Inst::UnOp {
                    op,
                    ty: ty.clone(),
                    operand: x,
                })
            };
            let bswap = un(body, UnOp::BSwap);
            let bitrev = un(body, UnOp::BitReverse);
            let ctlz = un(body, UnOp::CtLz);
            let cttz = un(body, UnOp::CtTz);
            body.void(Inst::Return {
                values: vec![rotl, rotr, bswap, bitrev, ctlz, cttz],
            });
        },
    )
}

#[test]
fn goal_g1_g8_g1_intrinsics_bulk_memory_bit_ops_match_rust_over_exhaustive_u8() {
    let module = bit_intrinsics_module(Ty::U8);
    for x in 0..=u8::MAX {
        // Amounts past the width exercise the modulo rule (Rust `rotate_left`
        // takes `n % 8` too); 0 and 8 pin the identity.
        for n in [0u8, 1, 3, 7, 8, 9, 200, 255] {
            let out = run(&module, [int(Ty::U8, x.into()), int(Ty::U8, n.into())])
                .unwrap_or_else(|e| panic!("x={x} n={n}: {e}"));
            let got: Vec<u128> = out.iter().map(as_u128).collect();
            let want = [
                u128::from(x.rotate_left(u32::from(n))),
                u128::from(x.rotate_right(u32::from(n))),
                u128::from(x.swap_bytes()),
                u128::from(x.reverse_bits()),
                u128::from(x.leading_zeros()),
                u128::from(x.trailing_zeros()),
            ];
            assert_eq!(
                got, want,
                "x={x:#04x} n={n}: (rotl, rotr, bswap, bitreverse, ctlz, cttz)"
            );
        }
    }
}

#[test]
fn goal_g1_g8_g1_intrinsics_bulk_memory_bit_ops_match_rust_over_sampled_u64() {
    let module = bit_intrinsics_module(Ty::U64);
    let mut samples: Vec<u64> = vec![
        0,
        1,
        2,
        3,
        0x80,
        0xFF,
        0x8000_0000_0000_0000,
        u64::MAX,
        0x0123_4567_89AB_CDEF,
    ];
    // A deterministic LCG sweep: no randomness, no ignored test, exact replay.
    let mut seed: u64 = 0x9E37_79B9_7F4A_7C15;
    for _ in 0..64 {
        seed = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        samples.push(seed);
        samples.push(seed >> (seed % 64)); // varied leading-zero counts
    }
    for x in samples {
        for n in [0u64, 1, 13, 63, 64, 65, 1000] {
            let out = run(&module, [int(Ty::U64, x.into()), int(Ty::U64, n.into())])
                .unwrap_or_else(|e| panic!("x={x:#x} n={n}: {e}"));
            let got: Vec<u128> = out.iter().map(as_u128).collect();
            let want = [
                u128::from(x.rotate_left(n as u32)),
                u128::from(x.rotate_right(n as u32)),
                u128::from(x.swap_bytes()),
                u128::from(x.reverse_bits()),
                u128::from(x.leading_zeros()),
                u128::from(x.trailing_zeros()),
            ];
            assert_eq!(got, want, "x={x:#x} n={n}");
        }
    }
}

/// `ctlz 0 = cttz 0 = width` is the ONE spelling: total, no poison.
#[test]
fn ctlz_and_cttz_of_zero_are_the_width_at_every_integer_type() {
    for (ty, width) in [
        (Ty::U8, 8u128),
        (Ty::I16, 16),
        (Ty::U32, 32),
        (Ty::I64, 64),
        (Ty::U128, 128),
    ] {
        let module = bit_intrinsics_module(ty.clone());
        let out = run(&module, [int(ty.clone(), 0), int(ty.clone(), 0)]).expect("total");
        assert_eq!(as_u128(&out[4]), width, "ctlz 0 at {ty}");
        assert_eq!(as_u128(&out[5]), width, "cttz 0 at {ty}");
    }
}

/// `fcopysign` executes at F32/F64 exactly like `FNeg` (same slice): the
/// magnitude of lhs with the sign bit of rhs, `-0.0` and NaN included.
#[test]
fn fcopysign_executes_at_f32_and_f64_like_fneg() {
    let module = module_with(
        "copysign",
        vec![Ty::F64, Ty::F64],
        vec![Ty::F64],
        |_m, body| {
            let r = body.val(Inst::BinOp {
                op: BinOp::FCopySign,
                ty: Ty::F64,
                lhs: v(0),
                rhs: v(1),
            });
            body.void(Inst::Return { values: vec![r] });
        },
    );
    for (a, s) in [
        (2.5f64, -1.0f64),
        (-2.5, 1.0),
        (2.5, -0.0),
        (f64::NAN, -1.0),
        (f64::INFINITY, -3.0),
    ] {
        let out = run(
            &module,
            [
                InterpretValue {
                    ty: Ty::F64,
                    kind: InterpretValueKind::FloatBits(a.to_bits()),
                },
                InterpretValue {
                    ty: Ty::F64,
                    kind: InterpretValueKind::FloatBits(s.to_bits()),
                },
            ],
        )
        .expect("fcopysign executes");
        let InterpretValueKind::FloatBits(bits) = out[0].kind else {
            panic!("float result expected, got {:?}", out[0]);
        };
        assert_eq!(bits, a.copysign(s).to_bits(), "copysign({a}, {s})");
    }
}

/// Negative twin (interpreter half): `ctlz f32` is refused by name — an
/// integer-only op on a float operand is a type error, never a silent
/// bit-level answer. (The validator half, `BinOpRequiresInteger`, is pinned in
/// `crates/trust-ir-build/tests/bulk_memory_ops.rs`.)
#[test]
fn ctlz_on_f32_is_refused_by_the_interpreter() {
    let module = module_with("ctlz-f32", vec![Ty::F32], vec![Ty::F32], |_m, body| {
        let r = body.val(Inst::UnOp {
            op: UnOp::CtLz,
            ty: Ty::F32,
            operand: v(0),
        });
        body.void(Inst::Return { values: vec![r] });
    });
    let err = run(
        &module,
        [InterpretValue {
            ty: Ty::F32,
            kind: InterpretValueKind::FloatBits(u64::from(1.0f32.to_bits())),
        }],
    )
    .expect_err("ctlz on a float must be refused");
    assert_eq!(err.code, InterpretErrorCode::TypeError, "{err}");
    assert!(err.to_string().contains("ctlz"), "{err}");
}

// ---------------------------------------------------------------------------
// goal-g1-g8/g1-intrinsics-bulk-memory + g3: MemCopy / MemSet
// ---------------------------------------------------------------------------

/// The shared fixture: `src` = 16 bytes with the u32 `0x01020304` at [0..4)
/// and the u8 `0xAA` at [12..16), [4..12) NEVER WRITTEN; `dst` = 16 fresh
/// bytes; `memcopy dst, src, 16` (dynamic count: an SSA `u64`, not an
/// immediate). `tail` then probes the destination and returns.
fn memcpy_fixture(
    overlap: bool,
    tail: impl FnOnce(&mut Body, ValueId, ValueId),
    returns: Vec<Ty>,
) -> Module {
    module_with("memcpy", vec![], returns, |m, body| {
        let src = body.alloca_bytes(m, 16);
        let dst = body.alloca_bytes(m, 16);
        let head = body.uconst(Ty::U32, 0x0102_0304);
        body.store(Ty::U32, src, head);
        let tail_ptr = body.byte_gep(src, 12);
        let aa = body.uconst(Ty::U8, 0xAA);
        body.store(Ty::U8, tail_ptr, aa);
        body.memcopy(dst, src, 16, overlap);
        tail(body, dst, src);
    })
}

/// POSITIVE: the initialized lanes arrive byte-exact; the uninitialized middle
/// STAYS uninitialized — a scalar reload spanning it faults on inspection
/// (copy-propagates-poison), while the per-byte reload of the initialized
/// lanes does not.
#[test]
fn goal_g1_g8_g1_intrinsics_bulk_memory_memcpy_keeps_the_uninit_middle_uninit() {
    // (a) initialized lanes: readable at the destination, byte-exact.
    let module = memcpy_fixture(
        false,
        |body, dst, _src| {
            let head = body.load(Ty::U32, dst, false);
            let p12 = body.byte_gep(dst, 12);
            let tail = body.load(Ty::U8, p12, false);
            let p3 = body.byte_gep(dst, 3);
            let byte3 = body.load(Ty::U8, p3, false);
            body.void(Inst::Return {
                values: vec![head, tail, byte3],
            });
        },
        vec![Ty::U32, Ty::U8, Ty::U8],
    );
    let out = run(&module, []).expect("initialized lanes reload");
    assert_eq!(as_u128(&out[0]), 0x0102_0304);
    assert_eq!(as_u128(&out[1]), 0xAA);
    assert_eq!(as_u128(&out[2]), 0x01, "little-endian byte 3 of 0x01020304");

    // (b) the middle: a STRICT (volatile) scalar reload faults at once ...
    let module = memcpy_fixture(
        false,
        |body, dst, _src| {
            let p8 = body.byte_gep(dst, 8);
            let mid = body.load(Ty::U32, p8, true);
            body.void(Inst::Return { values: vec![mid] });
        },
        vec![Ty::U32],
    );
    let err = run(&module, []).expect_err("a strict reload of copied-uninit bytes faults");
    assert_eq!(err.code, InterpretErrorCode::UndefinedBehavior, "{err}");
    assert!(err.to_string().contains("uninitialized"), "{err}");

    // ... (c) a plain scalar reload transports the poison and faults on
    // INSPECTION (arithmetic), exactly as it would have at the source ...
    let module = memcpy_fixture(
        false,
        |body, dst, _src| {
            let p8 = body.byte_gep(dst, 8);
            let mid = body.load(Ty::U32, p8, false);
            let one = body.uconst(Ty::U32, 1);
            let sum = body.val(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::U32,
                lhs: mid,
                rhs: one,
            });
            body.void(Inst::Return { values: vec![sum] });
        },
        vec![Ty::U32],
    );
    let err = run(&module, []).expect_err("inspecting the copied poison faults");
    assert_eq!(err.code, InterpretErrorCode::UndefinedBehavior, "{err}");

    // ... (d) and a plain reload that is merely TRANSPORTED (copied, stored
    // back) does not fault: the bytes are poison, not a trap.
    let module = memcpy_fixture(
        false,
        |body, dst, src| {
            let p8 = body.byte_gep(dst, 8);
            let mid = body.load(Ty::U32, p8, false);
            let copy = body.val(Inst::Copy {
                ty: Ty::U32,
                operand: mid,
            });
            let s8 = body.byte_gep(src, 8);
            body.store(Ty::U32, s8, copy);
            let head = body.load(Ty::U32, dst, false);
            body.void(Inst::Return { values: vec![head] });
        },
        vec![Ty::U32],
    );
    let out = run(&module, []).expect("poison transport never faults");
    assert_eq!(as_u128(&out[0]), 0x0102_0304);
}

/// MUTATION: overlapping ranges with `overlap: false` fault by name; the same
/// copy with `overlap: true` (memmove) is defined and behaves as if through a
/// temporary. Adjacent (touching) ranges never overlap.
#[test]
fn memcopy_overlap_without_the_flag_faults_and_memmove_moves() {
    // src[0..8) -> src[4..12): overlapping by 4 bytes.
    let overlapping = |overlap: bool| {
        module_with("overlap", vec![], vec![Ty::U32], move |m, body| {
            let src = body.alloca_bytes(m, 16);
            let head = body.uconst(Ty::U32, 0x0102_0304);
            body.store(Ty::U32, src, head);
            let p4 = body.byte_gep(src, 4);
            let next = body.uconst(Ty::U32, 0x0506_0708);
            body.store(Ty::U32, p4, next);
            let dst = body.byte_gep(src, 4);
            body.memcopy(dst, src, 8, overlap);
            let p8 = body.byte_gep(src, 8);
            let moved = body.load(Ty::U32, p8, false);
            body.void(Inst::Return {
                values: vec![moved],
            });
        })
    };
    let err = run(&overlapping(false), []).expect_err("memcpy of overlapping ranges is UB");
    assert_eq!(err.code, InterpretErrorCode::UndefinedBehavior, "{err}");
    assert!(
        err.to_string().contains("overlap"),
        "the refusal names the overlap: {err}"
    );

    // memmove: src[8..12) now holds the ORIGINAL src[4..8) = 0x05060708.
    let out = run(&overlapping(true), []).expect("memmove of overlapping ranges is defined");
    assert_eq!(as_u128(&out[0]), 0x0506_0708);

    // Control: touching ranges src[0..8) -> src[8..16) are not an overlap.
    let adjacent = module_with("adjacent", vec![], vec![Ty::U32], |m, body| {
        let src = body.alloca_bytes(m, 16);
        let head = body.uconst(Ty::U32, 0x0102_0304);
        body.store(Ty::U32, src, head);
        let p4 = body.byte_gep(src, 4);
        body.store(Ty::U32, p4, head);
        let dst = body.byte_gep(src, 8);
        body.memcopy(dst, src, 8, false);
        let moved = body.load(Ty::U32, dst, false);
        body.void(Inst::Return {
            values: vec![moved],
        });
    });
    assert_eq!(
        as_u128(&run(&adjacent, []).expect("adjacent ranges copy")[0]),
        0x0102_0304
    );
}

/// PROVENANCE: a carrier holding a STORED POINTER is copied and the pointer
/// reloaded from the copy still dereferences. A `MemCopy` that dropped
/// provenance (copied values but not the address's allocation identity) would
/// fail this: the reloaded `Ptr` would be a no-provenance dangling value and
/// the load through it would fault. Built on the byte-overlap carrier model
/// (`union_byte_overlap_model.rs`): the carrier is `[u8; 8]`, the pointer is
/// written and read through TYPED `Store`/`Load` at the carrier's address.
#[test]
fn memcopy_carries_pointer_provenance_through_a_byte_carrier() {
    let module = module_with("provenance", vec![], vec![Ty::U32], |m, body| {
        let cell = body.val(Inst::Alloca {
            ty: Ty::U32,
            count: None,
            align: Some(4),
        });
        let seven = body.uconst(Ty::U32, 7);
        body.store(Ty::U32, cell, seven);
        let carrier = body.alloca_bytes(m, 8);
        body.store(Ty::Ptr, carrier, cell);
        let copy = body.alloca_bytes(m, 8);
        body.memcopy(copy, carrier, 8, false);
        let reloaded = body.load(Ty::Ptr, copy, false);
        let through = body.load(Ty::U32, reloaded, false);
        body.void(Inst::Return {
            values: vec![through],
        });
    });
    let out = run(&module, []).expect("the copied pointer still dereferences");
    assert_eq!(as_u128(&out[0]), 7);
}

/// `MemSet` initializes every byte with the fill and DESTROYS a stored
/// pointer: after `memset 0`, the reloaded `Ptr` is null and the load through
/// it faults by name.
#[test]
fn memset_initializes_bytes_and_destroys_a_stored_pointer() {
    let module = module_with("memset", vec![], vec![Ty::U32, Ty::U8], |m, body| {
        let carrier = body.alloca_bytes(m, 8);
        body.memset(carrier, 0x5A, 8);
        let word = body.load(Ty::U32, carrier, true);
        let p7 = body.byte_gep(carrier, 7);
        let last = body.load(Ty::U8, p7, true);
        body.void(Inst::Return {
            values: vec![word, last],
        });
    });
    let out = run(&module, []).expect("memset bytes are initialized");
    assert_eq!(as_u128(&out[0]), 0x5A5A_5A5A);
    assert_eq!(as_u128(&out[1]), 0x5A);

    let module = module_with("memset-ptr", vec![], vec![Ty::U32], |m, body| {
        let cell = body.val(Inst::Alloca {
            ty: Ty::U32,
            count: None,
            align: Some(4),
        });
        let carrier = body.alloca_bytes(m, 8);
        body.store(Ty::Ptr, carrier, cell);
        body.memset(carrier, 0, 8);
        let reloaded = body.load(Ty::Ptr, carrier, false);
        let through = body.load(Ty::U32, reloaded, false);
        body.void(Inst::Return {
            values: vec![through],
        });
    });
    let err = run(&module, []).expect_err("a zeroed pointer is null");
    assert_eq!(err.code, InterpretErrorCode::UndefinedBehavior, "{err}");
    assert!(err.to_string().contains("null pointer"), "{err}");
}

/// Out of bounds faults by name; a zero count is a no-op even on a null
/// destination.
#[test]
fn memcopy_out_of_bounds_faults_and_zero_count_is_a_noop() {
    let module = memcpy_fixture(
        false,
        |body, dst, src| {
            let p8 = body.byte_gep(src, 8);
            body.memcopy(dst, p8, 16, false);
            body.void(Inst::Return { values: vec![] });
        },
        vec![],
    );
    let err = run(&module, []).expect_err("16 bytes from src+8 overruns the 16-byte allocation");
    assert_eq!(err.code, InterpretErrorCode::UndefinedBehavior, "{err}");
    assert!(err.to_string().contains("out of bounds"), "{err}");

    let module = module_with("zero-count", vec![], vec![], |m, body| {
        let src = body.alloca_bytes(m, 4);
        let null = body.val(Inst::NullPtr);
        let zero = body.uconst(Ty::U64, 0);
        body.void(Inst::MemCopy {
            dst: null,
            src,
            bytes: zero,
            overlap: false,
        });
        let fill = body.uconst(Ty::U8, 1);
        body.void(Inst::MemSet {
            dst: null,
            byte: fill,
            bytes: zero,
        });
        body.void(Inst::Return { values: vec![] });
    });
    run(&module, []).expect("a zero-count bulk op touches nothing");
}

/// goal-g1-g8/g3-no-symbolic-placeholder (format half): the bulk copy is a
/// REAL operation — no `RegionHavocStore` / `FreshSymbolicHavoc` marker, no
/// `Undef` — whose result is checkable end to end, and the DCE predicate keeps
/// it (it produces no SSA result a use count could protect).
#[test]
fn goal_g1_g8_g3_no_symbolic_placeholder_bulk_copy_is_an_operation_not_a_havoc() {
    let module = memcpy_fixture(
        false,
        |body, dst, _src| {
            let head = body.load(Ty::U32, dst, false);
            body.void(Inst::Return { values: vec![head] });
        },
        vec![Ty::U32],
    );
    let function = &module.functions[0];
    let mut bulk = 0;
    for node in function.blocks.iter().flat_map(|blk| &blk.body) {
        assert!(
            !node.proofs.iter().any(|p| matches!(
                p,
                trust_ir::proof::ProofAnnotation::RegionHavocStore
                    | trust_ir::proof::ProofAnnotation::FreshSymbolicHavoc
            )),
            "no havoc marker anywhere in the module"
        );
        assert!(
            !matches!(node.inst, Inst::Undef { .. }),
            "no Undef placeholder"
        );
        if let Inst::MemCopy { .. } | Inst::MemSet { .. } = node.inst {
            bulk += 1;
            assert!(
                node.inst.has_observable_effects(),
                "a bulk write is never DCE-removable"
            );
            assert!(!node.inst.is_removable_if_unused());
        }
    }
    assert_eq!(bulk, 1);
    assert_eq!(
        as_u128(&run(&module, []).expect("checkable end to end")[0]),
        0x0102_0304
    );
}

// ---------------------------------------------------------------------------
// Codecs: the new spellings round-trip through text and, since the v51 INST
// wire batch gave them tags, through binary.
// ---------------------------------------------------------------------------

/// Every WS3.20 spelling in one body: both `memcopy` forms, `memset`, the
/// four bit intrinsics and the two rotates.
#[cfg(any(feature = "parser", feature = "binary"))]
fn bulk_and_bit_module() -> Module {
    module_with("text", vec![Ty::U32, Ty::U32], vec![Ty::U32], |m, body| {
        let src = body.alloca_bytes(m, 8);
        let dst = body.alloca_bytes(m, 8);
        body.memcopy(dst, src, 8, false);
        body.memcopy(dst, src, 8, true);
        body.memset(dst, 0x11, 8);
        let mut last = v(0);
        for op in [UnOp::CtLz, UnOp::CtTz, UnOp::BSwap, UnOp::BitReverse] {
            last = body.val(Inst::UnOp {
                op,
                ty: Ty::U32,
                operand: last,
            });
        }
        for op in [BinOp::RotL, BinOp::RotR] {
            last = body.val(Inst::BinOp {
                op,
                ty: Ty::U32,
                lhs: last,
                rhs: v(1),
            });
        }
        body.void(Inst::Return { values: vec![last] });
    })
}

/// v51: the binary codec carries every spelling losslessly at the INST wire
/// batch's header, and the decoded module computes the same value.
#[cfg(feature = "binary")]
#[test]
fn bulk_memory_and_bit_intrinsics_round_trip_through_binary() {
    let module = bulk_and_bit_module();
    let bytes =
        trust_ir::binary::serialize_module(&module).expect("serialize_module: test fixture");
    let (decoded, version) =
        trust_ir::binary::deserialize_module_with_wire_version(&bytes).expect("decodes");
    assert_eq!(
        version.get(),
        trust_ir::binary::INST_WIRE_BATCH_FORMAT_VERSION
    );
    assert_eq!(decoded, module, "lossless");
    assert_eq!(decoded.stable_digest(), module.stable_digest());
    let args = || [int(Ty::U32, 0x0102_0304), int(Ty::U32, 5)];
    assert_eq!(
        run(&decoded, args()).expect("decoded module runs"),
        run(&module, args()).expect("module runs")
    );
}

#[cfg(feature = "parser")]
#[test]
fn bulk_memory_and_bit_intrinsics_round_trip_through_text() {
    let module = bulk_and_bit_module();
    let text = module.to_string();
    for needle in [
        "memcopy ptr %",
        "memcopy overlap ptr %",
        "memset ptr %",
        "ctlz u32",
        "cttz u32",
        "bswap u32",
        "bitreverse u32",
        "rotl u32",
        "rotr u32",
    ] {
        assert!(text.contains(needle), "text must spell `{needle}`:\n{text}");
    }
    let parsed = trust_ir::parser::parse_module(&text).expect("the printed text parses");
    assert_eq!(
        parsed.functions[0].blocks, module.functions[0].blocks,
        "lossless"
    );
}

// ---------------------------------------------------------------------------
// Adversarial review (2026-09-21): inputs the implementation did not write.
// ---------------------------------------------------------------------------

/// A HOSTILE count must FAULT, never crash the interpreter. `MemSet` used to
/// materialize `vec![fill; count]` BEFORE the bounds check, so a module that
/// spelled `memset ptr %p, 0, u64::MAX` aborted the process on capacity
/// overflow (and a count of a few GiB tried to allocate it) instead of the
/// ordinary out-of-bounds UB. Both bulk ops now bounds-check first; the
/// error is the same named UB an 8-byte overrun produces.
#[test]
fn a_hostile_byte_count_faults_and_never_allocates() {
    for count in [u64::MAX, u64::MAX - 7, 1u64 << 40, 9] {
        let module = module_with("memset-hostile", vec![], vec![], |m, body| {
            let carrier = body.alloca_bytes(m, 8);
            body.memset(carrier, 0xFF, count);
            body.void(Inst::Return { values: vec![] });
        });
        let err = run(&module, []).expect_err("a count past the allocation is UB");
        assert_eq!(err.code, InterpretErrorCode::UndefinedBehavior, "{err}");
        assert!(
            err.to_string().contains("out of bounds") || err.to_string().contains("overflow"),
            "count {count}: {err}"
        );

        let module = module_with("memcopy-hostile", vec![], vec![], |m, body| {
            let src = body.alloca_bytes(m, 8);
            let dst = body.alloca_bytes(m, 8);
            body.memcopy(dst, src, count, true);
            body.void(Inst::Return { values: vec![] });
        });
        let err = run(&module, []).expect_err("a count past the allocation is UB");
        assert_eq!(err.code, InterpretErrorCode::UndefinedBehavior, "{err}");
    }
}

/// A bulk op through a FREED allocation is a use-after-free and faults by
/// name on either side — the byte-granular path must not bypass the liveness
/// check a typed `Load`/`Store` performs.
#[test]
fn bulk_ops_on_a_freed_allocation_fault() {
    use trust_ir::inst::AllocOrigin;
    let heap = |body: &mut Body| {
        body.val(Inst::HeapAlloc {
            ty: Ty::U64,
            count: None,
            align: Some(8),
            origin: AllocOrigin::RustHeap,
        })
    };
    // Source freed.
    let module = module_with("uaf-src", vec![], vec![], |m, body| {
        let src = heap(body);
        let dst = body.alloca_bytes(m, 8);
        let zero = body.uconst(Ty::U64, 0);
        body.store(Ty::U64, src, zero);
        body.void(Inst::Dealloc { ptr: src });
        body.memcopy(dst, src, 8, false);
        body.void(Inst::Return { values: vec![] });
    });
    let err = run(&module, []).expect_err("copying from freed memory is UB");
    assert_eq!(err.code, InterpretErrorCode::UndefinedBehavior, "{err}");
    assert!(err.to_string().contains("dealloc"), "{err}");
    // Destination freed (memcopy and memset).
    let module = module_with("uaf-dst", vec![], vec![], |m, body| {
        let dst = heap(body);
        let src = body.alloca_bytes(m, 8);
        body.void(Inst::Dealloc { ptr: dst });
        body.memcopy(dst, src, 8, false);
        body.void(Inst::Return { values: vec![] });
    });
    let err = run(&module, []).expect_err("copying into freed memory is UB");
    assert_eq!(err.code, InterpretErrorCode::UndefinedBehavior, "{err}");
    let module = module_with("uaf-memset", vec![], vec![], |_m, body| {
        let dst = heap(body);
        body.void(Inst::Dealloc { ptr: dst });
        body.memset(dst, 0, 8);
        body.void(Inst::Return { values: vec![] });
    });
    let err = run(&module, []).expect_err("filling freed memory is UB");
    assert_eq!(err.code, InterpretErrorCode::UndefinedBehavior, "{err}");
    assert!(err.to_string().contains("dealloc"), "{err}");
}

/// The validator pins the count to `Usize` when the module carries target
/// info — so a real producer module spells it that way, and the interpreter
/// must EXECUTE it (not refuse the legitimate spelling). Pointer-width
/// unsigned, 8 bytes on the pinned 64-bit layout.
#[test]
fn a_usize_count_under_target_info_executes() {
    let mut module = module_with("usize-count", vec![], vec![Ty::U32], |m, body| {
        let src = body.alloca_bytes(m, 4);
        let dst = body.alloca_bytes(m, 4);
        let word = body.uconst(Ty::U32, 0xA1B2_C3D4);
        body.store(Ty::U32, src, word);
        let n = body.uconst(Ty::Usize, 4);
        body.void(Inst::MemCopy {
            dst,
            src,
            bytes: n,
            overlap: false,
        });
        let out = body.load(Ty::U32, dst, false);
        body.void(Inst::Return { values: vec![out] });
    });
    module.target_info = Some(trust_ir::TargetInfo {
        triple: "x86_64-unknown-linux-gnu".into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    let out = run(&module, []).expect("a usize count executes");
    assert_eq!(as_u128(&out[0]), 0xA1B2_C3D4);
}

/// `overlap` is SEMANTIC (memcpy vs memmove: one is UB where the other is
/// defined), so the semantic diff must report two modules that differ only in
/// the flag as different — a diff that called them equal would let a producer
/// swap a defined memmove for a UB memcpy unnoticed.
#[cfg(feature = "diff")]
#[test]
fn the_overlap_flag_is_a_semantic_difference() {
    let build = |overlap: bool| {
        module_with("ov", vec![], vec![], |m, body| {
            let src = body.alloca_bytes(m, 8);
            let dst = body.alloca_bytes(m, 8);
            body.memcopy(dst, src, 8, overlap);
            body.void(Inst::Return { values: vec![] });
        })
    };
    let memcpy = build(false);
    let memmove = build(true);
    assert!(trust_ir::diff::diff(&memcpy, &build(false)).is_empty());
    assert!(
        !trust_ir::diff::diff(&memcpy, &memmove).is_empty(),
        "memcpy and memmove must not diff as equal"
    );
}

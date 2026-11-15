//! Tests of [`super::check_allocation_bounds`]: the object-limit line, element
//! sizes on every target, the interval analysis and its scoping (one shape per
//! rule), and the work census. The transfer functions are checked against the
//! interpreter in `alloc_bound_property_tests.rs`, the whole analysis in
//! `alloc_bound_differential_tests.rs`.

use super::*;
use crate::inst::AssertKind;
use crate::node::InstrNode;
use crate::ty::{EnumLayoutDescriptor, EnumTagEncoding, EnumVariant, FatPtrKind, StructDef};
use crate::value::{FuncId, FuncTyId};
use crate::{Block, Function, SwitchCase, TargetInfo, TupleLayoutDescriptor};

const LIMIT_64: u128 = (1 << 63) - 1;

fn v(index: u32) -> ValueId {
    ValueId::new(index)
}

fn bb(index: u32) -> BlockId {
    BlockId::new(index)
}

fn def(result: u32, inst: Inst) -> InstrNode {
    InstrNode::new(inst).with_result(v(result))
}

fn konst(result: u32, ty: Ty, n: i128) -> InstrNode {
    def(
        result,
        Inst::Const {
            ty,
            value: Constant::Int(n),
        },
    )
}

fn alloca(result: u32, ty: Ty, count: Option<u32>) -> InstrNode {
    def(
        result,
        Inst::Alloca {
            ty,
            count: count.map(v),
            align: None,
        },
    )
}

fn heap(result: u32, ty: Ty, count: u32) -> InstrNode {
    def(
        result,
        Inst::HeapAlloc {
            ty,
            count: Some(v(count)),
            align: None,
            origin: crate::inst::AllocOrigin::RustHeap,
        },
    )
}

fn binop(result: u32, op: BinOp, ty: Ty, lhs: u32, rhs: u32) -> InstrNode {
    def(
        result,
        Inst::BinOp {
            op,
            ty,
            lhs: v(lhs),
            rhs: v(rhs),
        },
    )
}

fn icmp(result: u32, op: ICmpOp, ty: Ty, lhs: u32, rhs: u32) -> InstrNode {
    def(
        result,
        Inst::ICmp {
            op,
            ty,
            lhs: v(lhs),
            rhs: v(rhs),
        },
    )
}

fn zext(result: u32, from: Ty, to: Ty, operand: u32) -> InstrNode {
    def(
        result,
        Inst::Cast {
            op: CastOp::ZExt,
            src_ty: from,
            dst_ty: to,
            operand: v(operand),
        },
    )
}

fn ret() -> InstrNode {
    InstrNode::new(Inst::Return { values: vec![] })
}

fn br(target: u32, args: &[u32]) -> InstrNode {
    InstrNode::new(Inst::Br {
        target: bb(target),
        args: args.iter().copied().map(v).collect(),
    })
}

fn condbr(cond: u32, then: (u32, &[u32]), otherwise: (u32, &[u32])) -> InstrNode {
    InstrNode::new(Inst::CondBr {
        cond: v(cond),
        then_target: bb(then.0),
        then_args: then.1.iter().copied().map(v).collect(),
        else_target: bb(otherwise.0),
        else_args: otherwise.1.iter().copied().map(v).collect(),
    })
}

fn block(id: u32, params: &[(u32, Ty)], body: Vec<InstrNode>) -> Block {
    let mut block = Block::new(bb(id));
    for (value, ty) in params {
        block = block.with_param(v(*value), ty.clone());
    }
    block.body = body;
    block
}

/// One function `f` of these blocks; the first is the entry.
fn module_of(blocks: Vec<Block>) -> Module {
    let mut module = Module::new("alloc-bound");
    let entry = blocks[0].id;
    let mut func = Function::new(FuncId::new(0), "f", FuncTyId::new(0), entry);
    func.blocks = blocks;
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");
    module
}

/// A one-block function: the entry takes `n: u64`, runs `body`, returns.
fn straight(body: Vec<InstrNode>) -> Module {
    let mut body = body;
    body.push(ret());
    module_of(vec![block(0, &[(1, Ty::U64)], body)])
}

fn reasons(module: &Module) -> Vec<AllocBoundReason> {
    check_allocation_bounds(module)
        .into_iter()
        .map(|finding| finding.reason)
        .collect()
}

use AllocBoundReason::{
    ExceedsObjectLimit as Exceeds, UnboundedRuntimeCount as Unbounded,
    UnknownElementSize as Unsized,
};

fn on(mut module: Module, triple: &str, pointer_size: u32) -> Module {
    module.target_info = Some(TargetInfo {
        triple: triple.into(),
        pointer_size,
        endianness: crate::Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    module
}

#[test]
fn the_object_limit_is_isize_max_at_the_pointer_width() {
    assert_eq!(max_object_bytes(64), LIMIT_64);
    assert_eq!(max_object_bytes(32), (1 << 31) - 1);
    assert_eq!(max_object_bytes(16), (1 << 15) - 1);
    assert_eq!(max_object_bytes(128), (1 << 127) - 1);
    assert_eq!(max_object_bytes(1), 0);
    assert_eq!(max_object_bytes(0), 0);
    assert_eq!(max_object_bytes(200), u128::MAX);
}

/// No availability threshold: 512 MiB, 64 GiB and an exabyte are all sizes
/// the program states exactly, so none is reported. (The deleted 256 MiB
/// `ALLOC_BYTE_BUDGET` reported the first.)
#[test]
fn a_large_constant_allocation_is_bounded_whatever_its_size() {
    for (count, elem) in [
        (1i128 << 26, Ty::I64),
        (1 << 33, Ty::U64),
        (1 << 60, Ty::I8),
    ] {
        let module = straight(vec![konst(2, Ty::U64, count), alloca(3, elem, Some(2))]);
        assert_eq!(reasons(&module), vec![], "{count}");
    }
}

#[test]
fn a_constant_beyond_the_largest_object_can_never_succeed() {
    // 2^62 × i64 = 2^65 bytes > 2^63 - 1.
    let module = straight(vec![
        konst(2, Ty::U64, 1 << 62),
        alloca(3, Ty::I64, Some(2)),
    ]);
    let found = check_allocation_bounds(&module);
    assert_eq!(found.len(), 1);
    assert_eq!(found[0].reason, Exceeds);
    assert_eq!(found[0].kind, "alloca");
    assert_eq!(found[0].count, 1 << 62);
    assert_eq!(found[0].bytes, 1 << 65);
    assert_eq!(found[0].object_limit, LIMIT_64);
    let text = found[0].to_string();
    assert!(text.contains("36893488147419103232 bytes"), "{text}");
    assert!(text.contains("can never succeed"), "{text}");
}

/// Byte-exact at the line: the same count is within the limit for a 1-byte
/// element and beyond it for an 8-byte one, and `isize::MAX` itself fits.
#[test]
fn the_object_limit_is_byte_exact() {
    let cases: [(i128, Ty, Vec<AllocBoundReason>); 5] = [
        ((1 << 63) - 1, Ty::U8, vec![]),
        (1 << 63, Ty::U8, vec![Exceeds]),
        ((1 << 60) - 1, Ty::I64, vec![]),
        (1 << 60, Ty::I64, vec![Exceeds]),
        (1 << 60, Ty::I8, vec![]),
    ];
    for (count, elem, expected) in cases {
        let module = straight(vec![
            konst(2, Ty::U64, count),
            alloca(3, elem.clone(), Some(2)),
        ]);
        assert_eq!(reasons(&module), expected, "{count} x {elem}");
    }
}

#[test]
fn the_limit_follows_the_module_target() {
    let wasm32 = |mut module: Module| {
        module.target_info = Some(crate::TargetInfo {
            triple: "wasm32-unknown-unknown".into(),
            pointer_size: 4,
            endianness: crate::Endianness::Little,
            abi: None,
            struct_passing: Default::default(),
        });
        module
    };
    let big = straight(vec![konst(2, Ty::U64, 1 << 31), alloca(3, Ty::U8, Some(2))]);
    assert_eq!(reasons(&big), vec![]);
    let big = wasm32(big);
    let found = check_allocation_bounds(&big);
    assert_eq!(found[0].reason, Exceeds);
    assert_eq!(found[0].object_limit, (1 << 31) - 1);
    // A `usize` count is 32 bits there: its type range exceeds 2^31 - 1.
    let module = wasm32(module_of(vec![block(
        0,
        &[(1, Ty::Usize)],
        vec![alloca(3, Ty::U8, Some(1)), ret()],
    )]));
    assert_eq!(reasons(&module), vec![Unbounded]);
    // A `u16` count widened to `usize` is bounded there too.
    let module = wasm32(module_of(vec![block(
        0,
        &[(1, Ty::U16)],
        vec![
            zext(2, Ty::U16, Ty::Usize, 1),
            alloca(3, Ty::U64, Some(2)),
            ret(),
        ],
    )]));
    assert_eq!(reasons(&module), vec![]);
}

/// Elements are sized by the module's layout: aggregates and `bool` (one
/// byte; the pre-2026-09-30 lint read `bool`'s one BIT as zero bytes and
/// skipped every aggregate). A one-element allocation is judged by its
/// element's own size.
#[test]
fn elements_are_sized_by_the_module_layout() {
    let mut module = straight(vec![]);
    let u64_id = module
        .add_type(Ty::U64)
        .expect("Module::add_type: test fixture");
    let four = Ty::Array(u64_id, 4); // 32 bytes
    let body = &mut module.functions[0].blocks[0].body;
    body.pop();
    body.extend([
        alloca(3, Ty::I64, None),
        konst(4, Ty::U64, 1 << 59),
        alloca(5, four.clone(), Some(4)), // 2^64 bytes
        konst(6, Ty::U64, (1 << 58) - 1),
        alloca(7, four, Some(6)), // 2^63 - 32 bytes
        konst(8, Ty::U64, 1 << 63),
        alloca(9, Ty::Bool, Some(8)), // 2^63 bytes
        ret(),
    ]);
    let found = check_allocation_bounds(&module);
    let summary: Vec<_> = found.iter().map(|f| (f.reason, f.count, f.bytes)).collect();
    assert_eq!(
        summary,
        vec![(Exceeds, 1 << 59, 1 << 64), (Exceeds, 1 << 63, 1 << 63)]
    );
    // One element of 2^31 bytes is beyond a 32-bit target's largest object.
    let mut module = straight(vec![]);
    module.target_info = Some(crate::TargetInfo {
        triple: "wasm32-unknown-unknown".into(),
        pointer_size: 4,
        endianness: crate::Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    let u8_id = module
        .add_type(Ty::U8)
        .expect("Module::add_type: test fixture");
    let body = &mut module.functions[0].blocks[0].body;
    body.insert(0, alloca(2, Ty::Array(u8_id, 1 << 31), None));
    body.insert(1, alloca(3, Ty::Array(u8_id, (1 << 31) - 1), None));
    let found = check_allocation_bounds(&module);
    let summary: Vec<_> = found.iter().map(|f| (f.reason, f.count, f.bytes)).collect();
    assert_eq!(summary, vec![(Exceeds, 1, 1 << 31)]);
}

/// Constants fold with the interpreter's wrapping semantics: `u64::MAX + 2`
/// is `1`, and `2^31 * 2^31` is `2^62`.
#[test]
fn computed_constants_fold_exactly() {
    let module = straight(vec![
        konst(2, Ty::U64, u64::MAX.into()),
        konst(3, Ty::U64, 2),
        binop(4, BinOp::Add, Ty::U64, 2, 3),
        alloca(5, Ty::I64, Some(4)),
        konst(6, Ty::U64, 1 << 31),
        binop(7, BinOp::Mul, Ty::U64, 6, 6),
        alloca(8, Ty::I64, Some(7)),
        konst(9, Ty::U64, 28),
        konst(10, Ty::U64, 1),
        binop(11, BinOp::Shl, Ty::U64, 10, 9),
        alloca(12, Ty::I64, Some(11)),
    ]);
    let found = check_allocation_bounds(&module);
    assert_eq!(found.len(), 1, "{found:?}");
    assert_eq!((found[0].reason, found[0].count), (Exceeds, 1 << 62));
}

#[test]
fn a_bare_runtime_count_is_unbounded() {
    let module = straight(vec![alloca(2, Ty::I64, Some(1))]);
    let found = check_allocation_bounds(&module);
    assert_eq!(found.len(), 1);
    assert_eq!(found[0].reason, Unbounded);
    assert_eq!((found[0].count, found[0].bytes), (0, 0));
    let text = found[0].to_string();
    assert!(
        text.contains("9223372036854775807-byte object limit"),
        "{text}"
    );
    // So is a byte count of a runtime `u64`: 2^64 - 1 > 2^63 - 1.
    let module = straight(vec![heap(2, Ty::U8, 1)]);
    assert_eq!(reasons(&module), vec![Unbounded]);
}

#[test]
fn masks_remainders_shifts_and_narrowing_casts_bound_a_count() {
    let module = straight(vec![
        konst(2, Ty::U64, 0xFFFF),
        binop(3, BinOp::And, Ty::U64, 1, 2),
        alloca(4, Ty::I64, Some(3)),
        konst(5, Ty::U64, 1024),
        binop(6, BinOp::URem, Ty::U64, 1, 5),
        alloca(7, Ty::I64, Some(6)),
        konst(8, Ty::U64, 40),
        binop(9, BinOp::LShr, Ty::U64, 1, 8),
        alloca(10, Ty::I64, Some(9)),
        def(
            11,
            Inst::Cast {
                op: CastOp::Trunc,
                src_ty: Ty::U64,
                dst_ty: Ty::U32,
                operand: v(1),
            },
        ),
        zext(12, Ty::U32, Ty::U64, 11),
        // 2^32 - 1 elements of 8 bytes: 32 GiB, within the limit.
        alloca(13, Ty::I64, Some(12)),
    ]);
    assert_eq!(reasons(&module), vec![]);
}

/// `bb0: if n <op> K { bb1: alloc } else { bb2: alloc }`, with `n: count_ty`.
fn guarded(op: ICmpOp, count_ty: Ty, k: i128, elem: Ty) -> Module {
    module_of(vec![
        block(
            0,
            &[(1, count_ty.clone())],
            vec![
                konst(2, count_ty.clone(), k),
                icmp(3, op, count_ty, 1, 2),
                condbr(3, (1, &[]), (2, &[])),
            ],
        ),
        block(1, &[], vec![alloca(4, elem.clone(), Some(1)), ret()]),
        block(2, &[], vec![alloca(5, elem, Some(1)), ret()]),
    ])
}

#[test]
fn a_guard_bounds_the_count_where_it_dominates() {
    // Then-edge bounded (n < 1000); else-edge unbounded (n >= 1000).
    let found = check_allocation_bounds(&guarded(ICmpOp::Ult, Ty::U64, 1000, Ty::I64));
    assert_eq!(found.len(), 1);
    assert_eq!((found[0].reason, found[0].block), (Unbounded, 2));
    // Negated compare: the bound lands on the else edge.
    let found = check_allocation_bounds(&guarded(ICmpOp::Ugt, Ty::U64, 1000, Ty::I64));
    assert_eq!(found.len(), 1);
    assert_eq!(found[0].block, 1);
}

/// A guard against a sentinel above the limit is not a bound (`n <
/// u64::MAX`, the shape `usize::try_from` emits). Rust's own layout check,
/// `n <= isize::MAX / size_of::<T>()`, is.
#[test]
fn a_guard_against_a_huge_sentinel_does_not_bound() {
    // The then edge is unbounded; the else edge is exactly `u64::MAX`
    // elements, which can never be allocated.
    let module = guarded(ICmpOp::Ult, Ty::U64, u64::MAX.into(), Ty::I64);
    assert_eq!(reasons(&module), vec![Unbounded, Exceeds]);
    // The layout check's own failure edge (`n > isize::MAX / 8`) is the one
    // allocation that can never succeed.
    let module = guarded(ICmpOp::Ule, Ty::U64, (LIMIT_64 / 8) as i128, Ty::I64);
    let found = check_allocation_bounds(&module);
    assert_eq!(found.len(), 1);
    assert_eq!((found[0].reason, found[0].block), (Exceeds, 2));
    assert_eq!(found[0].bytes, 1 << 63);
}

/// `(n as i64) < 1000` passes every `n >= 2^63`: a signed guard does not
/// bound an unsigned count. It does bound a signed one, which must be
/// positive to allocate. (The pre-2026-09-30 lint discharged both.)
#[test]
fn a_signed_guard_bounds_only_a_signed_count() {
    let module = guarded(ICmpOp::Slt, Ty::U64, 1000, Ty::I64);
    assert_eq!(reasons(&module), vec![Unbounded, Unbounded]);
    let module = guarded(ICmpOp::Slt, Ty::I64, 1000, Ty::I64);
    let found = check_allocation_bounds(&module);
    assert_eq!(found.len(), 1);
    assert_eq!(found[0].block, 2);
}

#[test]
fn a_guard_reaches_a_count_passed_as_a_block_argument() {
    let module = module_of(vec![
        block(
            0,
            &[(1, Ty::U64)],
            vec![
                konst(2, Ty::U64, 1000),
                icmp(3, ICmpOp::Ult, Ty::U64, 1, 2),
                condbr(3, (1, &[1]), (2, &[1])),
            ],
        ),
        block(
            1,
            &[(10, Ty::U64)],
            vec![alloca(4, Ty::I64, Some(10)), ret()],
        ),
        block(
            2,
            &[(11, Ty::U64)],
            vec![alloca(5, Ty::I64, Some(11)), ret()],
        ),
    ]);
    let found = check_allocation_bounds(&module);
    assert_eq!(found.len(), 1);
    assert_eq!(found[0].block, 2);
}

/// Boolean negation's one spelling, `bxor %c, true` (SPEC_RATIFICATIONS
/// §3.2, WS2.21), negates a guard: `if !(n < 1000)` leaves the ELSE edge
/// bounded. `bxor %c, false` (either operand order) is `%c` itself, and an
/// exclusive-or with a value that is not a constant reads as no condition.
#[test]
fn a_guard_negated_by_bxor_true_bounds_the_other_edge() {
    let program = |flip: Option<bool>, swap: bool| {
        let mut entry = vec![konst(2, Ty::U64, 1000), icmp(3, ICmpOp::Ult, Ty::U64, 1, 2)];
        let k = match flip {
            Some(b) => {
                entry.push(def(
                    4,
                    Inst::Const {
                        ty: Ty::Bool,
                        value: Constant::Bool(b),
                    },
                ));
                4
            }
            None => 9, // the entry's `Bool` parameter: not a constant
        };
        let (lhs, rhs) = if swap { (k, 3) } else { (3, k) };
        entry.push(binop(5, BinOp::BXor, Ty::Bool, lhs, rhs));
        entry.push(condbr(5, (1, &[1]), (2, &[1])));
        module_of(vec![
            block(0, &[(1, Ty::U64), (9, Ty::Bool)], entry),
            block(
                1,
                &[(10, Ty::U64)],
                vec![alloca(6, Ty::I64, Some(10)), ret()],
            ),
            block(
                2,
                &[(11, Ty::U64)],
                vec![alloca(7, Ty::I64, Some(11)), ret()],
            ),
        ])
    };
    let blocks = |module: &Module| -> Vec<u32> {
        check_allocation_bounds(module)
            .into_iter()
            .map(|finding| finding.block)
            .collect()
    };
    for swap in [false, true] {
        // `!(n < 1000)` is true on the THEN edge: there `n` is unbounded.
        assert_eq!(blocks(&program(Some(true), swap)), vec![1], "swap={swap}");
        // `(n < 1000) ^ false` is the guard itself.
        assert_eq!(blocks(&program(Some(false), swap)), vec![2], "swap={swap}");
        // An exclusive-or with a runtime `Bool` bounds neither edge.
        assert_eq!(blocks(&program(None, swap)), vec![1, 2], "swap={swap}");
    }
}

/// WS2.21 review: only an EXCLUSIVE-or with a `Bool` constant is read as the
/// guard or its negation. The overloaded `xor` reads like `bxor`; a connective
/// that is constant whatever the guard (`bor %c, true`, `band %c, false`,
/// `bxor %c, %c`) must never be read as the guard, or the edge it always takes
/// would be wrongly bounded and an unbounded count silenced.
#[test]
fn only_an_exclusive_or_with_a_constant_reads_as_the_guard() {
    // `bb0(n, p)`: `%3 = n < 1000`, `%4 = const bool k`, `%5 = op %3, rhs`,
    // then `condbr %5` to `bb1(n)` / `bb2(n)`, each allocating `n` words.
    let program = |op: BinOp, k: bool, rhs: u32| {
        module_of(vec![
            block(
                0,
                &[(1, Ty::U64), (9, Ty::Bool)],
                vec![
                    konst(2, Ty::U64, 1000),
                    icmp(3, ICmpOp::Ult, Ty::U64, 1, 2),
                    def(
                        4,
                        Inst::Const {
                            ty: Ty::Bool,
                            value: Constant::Bool(k),
                        },
                    ),
                    binop(5, op, Ty::Bool, 3, rhs),
                    condbr(5, (1, &[1]), (2, &[1])),
                ],
            ),
            block(
                1,
                &[(10, Ty::U64)],
                vec![alloca(6, Ty::I64, Some(10)), ret()],
            ),
            block(
                2,
                &[(11, Ty::U64)],
                vec![alloca(7, Ty::I64, Some(11)), ret()],
            ),
        ])
    };
    let blocks = |module: &Module| -> Vec<u32> {
        check_allocation_bounds(module)
            .into_iter()
            .map(|finding| finding.block)
            .collect()
    };
    // The overloaded `xor bool` computes the same value as `bxor`.
    assert_eq!(blocks(&program(BinOp::Xor, true, 4)), vec![1]);
    assert_eq!(blocks(&program(BinOp::Xor, false, 4)), vec![2]);
    // Always true: the THEN edge is taken with `n` unbounded.
    for op in [BinOp::BOr, BinOp::Or] {
        assert!(
            blocks(&program(op, true, 4)).contains(&1),
            "{op:?} %c, true"
        );
    }
    // Always false: the ELSE edge is taken with `n` unbounded.
    for op in [BinOp::BAnd, BinOp::And] {
        assert!(
            blocks(&program(op, false, 4)).contains(&2),
            "{op:?} %c, false"
        );
    }
    for op in [BinOp::BXor, BinOp::Xor] {
        assert!(blocks(&program(op, true, 3)).contains(&2), "{op:?} %c, %c");
    }
}

/// A join is bounded only when every incoming edge passes a bounded value.
#[test]
fn a_join_is_bounded_only_when_every_edge_is() {
    let join = |second_arg: u32| {
        module_of(vec![
            block(
                0,
                &[(1, Ty::U64), (2, Ty::Bool)],
                vec![
                    konst(3, Ty::U64, 100),
                    konst(4, Ty::U64, 0xFF),
                    binop(5, BinOp::And, Ty::U64, 1, 4),
                    condbr(2, (1, &[3]), (1, &[second_arg])),
                ],
            ),
            block(
                1,
                &[(10, Ty::U64)],
                vec![alloca(6, Ty::I64, Some(10)), ret()],
            ),
        ])
    };
    assert_eq!(reasons(&join(5)), vec![]);
    assert_eq!(reasons(&join(1)), vec![Unbounded]);
}

/// `n.min(K)` is `select(n < K, n, K)`; `n.max(K)` is not bounded.
#[test]
fn min_through_select_bounds_a_count() {
    let select = |then_val: u32, else_val: u32| {
        straight(vec![
            konst(2, Ty::U64, 4096),
            icmp(3, ICmpOp::Ult, Ty::U64, 1, 2),
            def(
                4,
                Inst::Select {
                    ty: Ty::U64,
                    cond: v(3),
                    then_val: v(then_val),
                    else_val: v(else_val),
                },
            ),
            alloca(5, Ty::I64, Some(4)),
        ])
    };
    assert_eq!(reasons(&select(1, 2)), vec![]);
    assert_eq!(reasons(&select(2, 1)), vec![Unbounded]);
}

/// The checked multiplication `Layout::array` spells: `(bytes, overflowed) =
/// n * 8`; on the no-overflow edge `bytes` is the exact product. That alone
/// does not keep it under `isize::MAX`; the layout check after it does, and a
/// bound on `n` before it does.
#[test]
fn checked_multiplication_and_the_layout_check() {
    let program = |n_bound: Option<i128>, layout_check: bool| {
        let mut entry = vec![konst(2, Ty::U64, 8)];
        let mut blocks = Vec::new();
        let first = match n_bound {
            Some(k) => {
                entry.extend([
                    konst(3, Ty::U64, k),
                    icmp(4, ICmpOp::Ule, Ty::U64, 1, 3),
                    condbr(4, (1, &[]), (9, &[])),
                ]);
                blocks.push(block(0, &[(1, Ty::U64)], entry));
                None
            }
            None => Some(entry),
        };
        let mut multiply = vec![
            InstrNode::new(Inst::Overflow {
                op: OverflowOp::MulOverflow,
                ty: Ty::U64,
                lhs: v(1),
                rhs: v(2),
            })
            .with_results([v(5), v(6)]),
        ];
        multiply.push(condbr(6, (9, &[]), (if layout_check { 2 } else { 3 }, &[])));
        match first {
            Some(mut entry) => {
                entry.extend(multiply);
                blocks.push(block(0, &[(1, Ty::U64)], entry));
            }
            None => blocks.push(block(1, &[], multiply)),
        }
        blocks.push(block(
            2,
            &[],
            vec![
                konst(7, Ty::U64, LIMIT_64 as i128),
                icmp(8, ICmpOp::Ugt, Ty::U64, 5, 7),
                condbr(8, (9, &[]), (3, &[])),
            ],
        ));
        blocks.push(block(3, &[], vec![heap(10, Ty::U8, 5), ret()]));
        blocks.push(block(9, &[], vec![ret()]));
        module_of(blocks)
    };
    assert_eq!(reasons(&program(None, false)), vec![Unbounded]);
    assert_eq!(reasons(&program(None, true)), vec![]);
    assert_eq!(reasons(&program(Some(1000), false)), vec![]);
}

/// A loop-carried count is unbounded (its back edge is not walked when the
/// header is); a bounded value defined before the loop stays bounded in it.
#[test]
fn loop_carried_counts_are_unbounded_and_invariant_ones_are_not() {
    let module = module_of(vec![
        block(
            0,
            &[(1, Ty::U64)],
            vec![
                konst(2, Ty::U64, 0xFF),
                binop(3, BinOp::And, Ty::U64, 1, 2),
                konst(4, Ty::U64, 1),
                br(1, &[4]),
            ],
        ),
        block(
            1,
            &[(10, Ty::U64)],
            vec![
                alloca(5, Ty::I64, Some(10)),
                alloca(6, Ty::I64, Some(3)),
                binop(7, BinOp::Add, Ty::U64, 10, 4),
                icmp(8, ICmpOp::Ult, Ty::U64, 7, 3),
                condbr(8, (1, &[7]), (2, &[])),
            ],
        ),
        block(2, &[], vec![ret()]),
    ]);
    let found = check_allocation_bounds(&module);
    assert_eq!(found.len(), 1);
    assert_eq!((found[0].reason, found[0].block), (Unbounded, 1));
}

#[test]
fn assume_and_assert_bound_what_follows_them() {
    for fact in [
        Inst::Assume { cond: v(3) },
        Inst::Assert {
            cond: v(3),
            kind: AssertKind::Unspecified,
            site: None,
        },
    ] {
        let module = straight(vec![
            alloca(4, Ty::I64, Some(1)),
            konst(2, Ty::U64, 64),
            icmp(3, ICmpOp::Ult, Ty::U64, 1, 2),
            InstrNode::new(fact),
            alloca(5, Ty::I64, Some(1)),
        ]);
        let found = check_allocation_bounds(&module);
        assert_eq!(found.len(), 1, "only the allocation before the fact");
        assert_eq!(found[0].reason, Unbounded);
    }
}

#[test]
fn a_switch_case_bounds_its_edge() {
    let module = module_of(vec![
        block(
            0,
            &[(1, Ty::U64)],
            vec![InstrNode::new(Inst::Switch {
                value: v(1),
                default: bb(2),
                default_args: vec![],
                cases: vec![SwitchCase {
                    value: Constant::Int(5),
                    target: bb(1),
                    args: vec![],
                }],
                exhaustive_enum_unreachable: false,
            })],
        ),
        block(1, &[], vec![alloca(2, Ty::I64, Some(1)), ret()]),
        block(2, &[], vec![alloca(3, Ty::I64, Some(1)), ret()]),
    ]);
    let found = check_allocation_bounds(&module);
    assert_eq!(found.len(), 1);
    assert_eq!(found[0].block, 2);
}

/// Precision limit, in the sound direction: a value computed BEFORE a guard
/// on its operand keeps its unguarded range; computed after, it is bounded.
#[test]
fn a_guard_reaches_values_computed_in_its_region() {
    let program = |multiply_first: bool| {
        let multiply = binop(3, BinOp::Mul, Ty::U64, 1, 2);
        let mut entry = vec![konst(2, Ty::U64, 8), konst(4, Ty::U64, 1000)];
        let mut guarded = Vec::new();
        if multiply_first {
            entry.push(multiply);
        } else {
            guarded.push(multiply);
        }
        entry.extend([
            icmp(5, ICmpOp::Ule, Ty::U64, 1, 4),
            condbr(5, (1, &[]), (2, &[])),
        ]);
        guarded.extend([heap(6, Ty::U8, 3), ret()]);
        module_of(vec![
            block(0, &[(1, Ty::U64)], entry),
            block(1, &[], guarded),
            block(2, &[], vec![ret()]),
        ])
    };
    assert_eq!(reasons(&program(false)), vec![]);
    assert_eq!(reasons(&program(true)), vec![Unbounded]);
}

/// Dead code never allocates. A CFG the dominator analysis rejects (here a
/// block with no terminator) gets no branch facts: its guard is not trusted.
#[test]
fn unreachable_code_is_not_judged_and_a_malformed_cfg_gets_no_facts() {
    let module = module_of(vec![
        block(0, &[(1, Ty::U64)], vec![ret()]),
        block(1, &[], vec![alloca(2, Ty::I64, Some(1)), ret()]),
    ]);
    assert_eq!(reasons(&module), vec![]);
    let mut module = guarded(ICmpOp::Ult, Ty::U64, 1000, Ty::I64);
    module.functions[0].blocks[1].body.pop(); // bb1 loses its terminator
    assert_eq!(reasons(&module), vec![Unbounded, Unbounded]);
}

/// One pass, whatever the block order: a chain of `N` blocks each adding one
/// to the count, stored in REVERSE order in `func.blocks`. The count is
/// exactly `N`. (The pre-2026-09-30 constant folder iterated over the block
/// list to a fixpoint, one pass per block here, and its dominator sets were
/// O(blocks^2).)
#[test]
fn the_walk_is_one_pass_over_any_block_order() {
    const N: u32 = 20_000;
    let one = 1;
    let mut blocks = vec![block(
        0,
        &[(2, Ty::U64)],
        vec![konst(one, Ty::U64, 1), br(1, &[one])],
    )];
    for index in 1..N {
        let param = 10 + 2 * index;
        blocks.push(block(
            index,
            &[(param, Ty::U64)],
            vec![
                binop(param + 1, BinOp::Add, Ty::U64, param, one),
                br(index + 1, &[param + 1]),
            ],
        ));
    }
    let last = 10 + 2 * N;
    blocks.push(block(
        N,
        &[(last, Ty::U64)],
        vec![alloca(last + 1, Ty::I64, Some(last)), ret()],
    ));
    let entry = blocks.remove(0);
    blocks.reverse();
    blocks.insert(0, entry);
    let module = module_of(blocks);
    let (found, census) = check(&module);
    assert_eq!(found, vec![]);
    // The work is the program's size: each block, instruction and edge once.
    let nodes: usize = module.functions[0]
        .blocks
        .iter()
        .map(|b| b.body.len())
        .sum();
    assert_eq!(census.blocks, N as usize + 1);
    assert_eq!(census.nodes, nodes);
    assert_eq!(census.edges_recorded, N as usize);
    assert_eq!(census.arguments_joined, N as usize);
    // The exact count is observable at the line: N copies of an element of
    // `isize::MAX / (N - 1)` bytes cross it.
    let mut module = module;
    let elem = module
        .add_type(Ty::U8)
        .expect("Module::add_type: test fixture");
    let big = Ty::Array(elem, (LIMIT_64 / u128::from(N - 1)) as u64);
    let func = &mut module.functions[0];
    let tail = func.blocks.iter_mut().find(|b| b.id == bb(N)).unwrap();
    tail.body[0] = alloca(last + 1, big, Some(last));
    let found = check_allocation_bounds(&module);
    assert_eq!(found.len(), 1);
    assert_eq!((found[0].reason, found[0].count), (Exceeds, u128::from(N)));
}

/// Off the canonical scalar-ALIGNMENT table (i686, armv7, riscv32,
/// powerpc64le, s390x) a size is still a size: every scalar allocation is
/// judged as on a canonical target of the same pointer width. (The
/// 2026-09-30 rewrite first sized elements through `ty_layout_shape`, which
/// refuses every scalar there, and so reported nothing on those targets.)
#[test]
fn elements_are_sized_off_the_alignment_table_too() {
    let unchecked = |count_ty: Ty, elem: Ty| {
        module_of(vec![block(
            0,
            &[(1, count_ty)],
            vec![alloca(2, elem.clone(), Some(1)), heap(3, elem, 1), ret()],
        )])
    };
    for (triple, size) in [
        ("wasm32-unknown-unknown", 4),
        ("i686-unknown-linux-gnu", 4),
        ("armv7-unknown-linux-gnueabihf", 4),
        ("riscv32imac-unknown-none-elf", 4),
    ] {
        // A `usize` count of bytes reaches 2^32 - 1 > 2^31 - 1.
        let module = on(unchecked(Ty::Usize, Ty::U8), triple, size);
        assert_eq!(reasons(&module), vec![Unbounded, Unbounded], "{triple}");
        // 2^32 - 1 elements of 8 bytes can never fit 32 bits.
        let never = on(
            straight(vec![
                konst(2, Ty::U32, 0xFFFF_FFFF),
                alloca(3, Ty::U64, Some(2)),
            ]),
            triple,
            size,
        );
        let found = check_allocation_bounds(&never);
        let summary: Vec<_> = found.iter().map(|f| (f.reason, f.bytes)).collect();
        assert_eq!(summary, vec![(Exceeds, 0x7_FFFF_FFF8)], "{triple}");
        // A `u16` count of `u64`s is bounded.
        let module = on(unchecked(Ty::U16, Ty::U64), triple, size);
        assert_eq!(reasons(&module), vec![], "{triple}");
    }
    for (triple, size) in [
        ("x86_64-unknown-linux-gnu", 8),
        ("powerpc64le-unknown-linux-gnu", 8),
        ("s390x-unknown-linux-gnu", 8),
    ] {
        let module = on(unchecked(Ty::U64, Ty::U64), triple, size);
        assert_eq!(reasons(&module), vec![Unbounded, Unbounded], "{triple}");
        let module = on(unchecked(Ty::U32, Ty::I128), triple, size);
        assert_eq!(reasons(&module), vec![], "{triple}");
    }
}

/// An element of `2^61` bytes or more is judged exactly (sizes are `u128`
/// products), and one beyond `u128` exceeds every object.
#[test]
fn huge_elements_are_judged_exactly() {
    let mut module = straight(vec![]);
    let u8_id = module
        .add_type(Ty::U8)
        .expect("Module::add_type: test fixture");
    let half = module
        .add_type(Ty::Array(u8_id, 1 << 63))
        .expect("Module::add_type: test fixture"); // 2^63 bytes
    let wide = module
        .add_type(Ty::Array(half, 1 << 63))
        .expect("Module::add_type: test fixture"); // 2^126 bytes
    let body = &mut module.functions[0].blocks[0].body;
    body.pop();
    body.extend([
        alloca(2, Ty::Array(u8_id, 1 << 63), None),
        alloca(3, Ty::Array(u8_id, (1 << 63) - 1), None),
        alloca(4, Ty::Array(half, 1), Some(1)),
        alloca(5, Ty::Array(wide, 4), None), // 2^128 bytes: beyond u128
        alloca(6, Ty::Array(wide, 0), None), // zero of them: nothing
        ret(),
    ]);
    let found = check_allocation_bounds(&module);
    let summary: Vec<_> = found.iter().map(|f| (f.reason, f.count, f.bytes)).collect();
    assert_eq!(
        summary,
        vec![
            (Exceeds, 1, 1 << 63),
            (Exceeds, 1, 1 << 63),
            (Exceeds, 1, u128::MAX),
        ]
    );
    // A line beyond u128 (a pointer wider than 128 bits, which the validator
    // refuses) proves no product beyond u128 too big: it is reported as
    // unbounded, never as exceeding.
    let mut wide_target = on(module.clone(), "x86_64-unknown-linux-gnu", 32);
    wide_target.functions[0].blocks[0].body.retain(|node| {
        matches!(&node.inst, Inst::Alloca { ty: Ty::Array(id, 4), .. } if *id == wide)
            || node.is_terminator()
    });
    assert_eq!(reasons(&wide_target), vec![Unbounded]);
}

/// An element with no byte size is reported, never skipped; a zero-sized one
/// allocates nothing and is not.
#[test]
fn an_element_with_no_size_is_reported() {
    let mut module = straight(vec![]);
    let u8_id = module
        .add_type(Ty::U8)
        .expect("Module::add_type: test fixture");
    let missing = TyId::new(99);
    let cyclic = TyId::new(module.types.len() as u32);
    module
        .add_type(Ty::Array(cyclic, 2))
        .expect("Module::add_type: test fixture"); // ty.N = [ty.N; 2]
    let sizeless = module.add_struct(StructDef {
        id: crate::value::StructId::new(7),
        name: "NoSize".into(),
        fields: Vec::new(),
        size: None,
        align: None,
        repr: Default::default(),
        origin: None,
    });
    let body = &mut module.functions[0].blocks[0].body;
    body.pop();
    body.extend([
        alloca(2, Ty::Sequence(u8_id), None),
        alloca(3, Ty::Array(missing, 1), Some(1)),
        alloca(4, Ty::Array(cyclic, 1), None),
        alloca(5, Ty::Struct(sizeless), None),
        alloca(6, Ty::Tuple(vec![Ty::U8, Ty::U64]), None), // no descriptor
        alloca(7, Ty::Unit, Some(1)),
        alloca(8, Ty::Array(u8_id, 0), Some(1)),
        ret(),
    ]);
    let found = check_allocation_bounds(&module);
    let blocks: Vec<_> = found
        .iter()
        .map(|f| (f.reason, f.elem_ty.clone()))
        .collect();
    assert_eq!(found.len(), 5, "{blocks:?}");
    assert!(found.iter().all(|f| f.reason == Unsized), "{blocks:?}");
    let text = found[0].to_string();
    assert!(text.contains("has no byte size"), "{text}");
    // Unreachable, or with an undefined count, it is not judged at all.
    let module = guarded(ICmpOp::Slt, Ty::I64, 1, Ty::Sequence(u8_id));
    let found = check_allocation_bounds(&module);
    assert_eq!(found.len(), 1, "only the edge with positive counts");
    assert_eq!((found[0].reason, found[0].block), (Unsized, 2));
}

/// The sizes the lint uses are the layout authority's wherever it answers.
#[test]
fn element_sizes_are_the_layout_authoritys() {
    let mut module = straight(vec![]);
    let u8_id = module
        .add_type(Ty::U8)
        .expect("Module::add_type: test fixture");
    let u64_id = module
        .add_type(Ty::U64)
        .expect("Module::add_type: test fixture");
    let nested = module
        .add_type(Ty::Array(u64_id, 3))
        .expect("Module::add_type: test fixture");
    let pair = module.add_struct(StructDef {
        id: crate::value::StructId::new(1),
        name: "Pair".into(),
        fields: vec![
            crate::ty::FieldDef {
                name: "a".into(),
                ty: Ty::U8,
                offset: Some(0),
            },
            crate::ty::FieldDef {
                name: "b".into(),
                ty: Ty::U64,
                offset: Some(8),
            },
        ],
        size: Some(16),
        align: Some(8),
        repr: Default::default(),
        origin: None,
    });
    let canonical = module.add_enum(EnumDef::new(
        crate::value::EnumId::new(1),
        "E",
        vec![
            EnumVariant {
                name: "A".into(),
                fields: vec![Ty::U8],
                field_names: vec![],
            },
            EnumVariant {
                name: "B".into(),
                fields: vec![Ty::U64, Ty::U16],
                field_names: vec![],
            },
        ],
    ));
    let mut described = EnumDef::new(
        crate::value::EnumId::new(2),
        "D",
        vec![EnumVariant {
            name: "Only".into(),
            fields: vec![Ty::U32],
            field_names: vec![],
        }],
    );
    described.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Untagged,
        size: 4,
        align: 4,
        variant_field_offsets: vec![vec![0]],
    });
    let described = module.add_enum(described);
    let tuple_ty = Ty::Tuple(vec![Ty::U8, Ty::U32]);
    let tuple_id = module
        .add_type(tuple_ty.clone())
        .expect("Module::add_type: test fixture");
    module.tuple_layouts.push(TupleLayoutDescriptor {
        tuple_type: tuple_id,
        size: 8,
        align: 4,
        field_offsets: vec![0, 4],
    });
    let module = on(module, "x86_64-unknown-linux-gnu", 8);
    let pred = crate::value::PredId::new(0);
    let types = [
        Ty::Bool,
        Ty::I8,
        Ty::U16,
        Ty::F16,
        Ty::I32,
        Ty::F32,
        Ty::Char,
        Ty::U64,
        Ty::F64,
        Ty::I128,
        Ty::Usize,
        Ty::Isize,
        Ty::Ptr,
        Ty::Ref(Box::new(Ty::U8)),
        Ty::FatPtr(FatPtrKind::Slice(u8_id)),
        Ty::FatPtr(FatPtrKind::Str),
        Ty::Unit,
        Ty::Array(u8_id, 5),
        Ty::Array(nested, 2),
        Ty::Vector(Box::new(Ty::U32), 4),
        Ty::Vector(Box::new(Ty::Bool), 8),
        Ty::Struct(pair),
        Ty::Enum(canonical),
        Ty::Enum(described),
        tuple_ty,
        Ty::Refine(u64_id, pred),
    ];
    let mut sizer = Sizer::new(&module);
    for ty in types {
        let authority = module
            .ty_layout_shape(&ty)
            .ok()
            .and_then(|layout| layout.size_bytes())
            .unwrap_or_else(|| panic!("the authority sizes {ty}"));
        assert_eq!(
            sizer.bytes(&ty),
            Bytes::Exact(u128::from(authority)),
            "{ty}"
        );
    }
    // The same struct, tuple and described enum off the alignment table: the
    // authority refuses them there, the declared sizes stand. A canonical
    // enum's tag placement needs the alignments, so it is unsized there.
    let moved = on(module.clone(), "i686-unknown-linux-gnu", 4);
    let mut sizer = Sizer::new(&moved);
    assert_eq!(sizer.bytes(&Ty::Struct(pair)), Bytes::Exact(16));
    assert_eq!(sizer.bytes(&Ty::Enum(described)), Bytes::Exact(4));
    assert_eq!(
        sizer.bytes(&Ty::Tuple(vec![Ty::U8, Ty::U32])),
        Bytes::Exact(8)
    );
    assert_eq!(sizer.bytes(&Ty::Enum(canonical)), Bytes::Unknown);
    assert_eq!(sizer.bytes(&Ty::Usize), Bytes::Exact(4));
    assert_eq!(
        sizer.bytes(&Ty::FatPtr(FatPtrKind::Slice(u8_id))),
        Bytes::Exact(8)
    );
}

/// Sizing is memoized: a chain of `K` nested array types, each allocated,
/// computes each type once (an unmemoized recursion re-walks the chain under
/// every allocation, `K^2 / 2` steps).
#[test]
fn element_sizing_visits_each_type_once() {
    const K: u32 = 2_000;
    let mut module = straight(vec![]);
    let mut elem = module
        .add_type(Ty::U8)
        .expect("Module::add_type: test fixture");
    let body_len = module.functions[0].blocks[0].body.len();
    let mut allocations = Vec::new();
    for k in 0..K {
        elem = module
            .add_type(Ty::Array(elem, 1))
            .expect("Module::add_type: test fixture");
        allocations.push(alloca(10 + 2 * k, Ty::Array(elem, 1), None));
        allocations.push(alloca(11 + 2 * k, Ty::Array(elem, 1), None));
    }
    let body = &mut module.functions[0].blocks[0].body;
    body.splice(body_len - 1..body_len - 1, allocations);
    let (found, census) = check(&module);
    assert_eq!(found, vec![]);
    // Each allocated element type (allocated twice), and each type-table
    // entry, once.
    assert_eq!(census.sizes_computed, K as usize + module.types.len());
}

/// The line is the largest object, and only defined executions are judged:
/// an unchecked signed count of bytes (a non-positive count is UB at the
/// allocation, and the positive ones are at most `i64::MAX`) and a count
/// narrower than the pointer (`u32` of `u64`: at most 32 GiB) are within it.
/// An unchecked `usize` count of bytes, the 2026-06-16 OOM shape, is not.
#[test]
fn defined_executions_and_the_object_line_decide_silence() {
    let one = |count_ty: Ty, elem: Ty| {
        module_of(vec![block(
            0,
            &[(1, count_ty)],
            vec![alloca(2, elem, Some(1)), ret()],
        )])
    };
    assert_eq!(reasons(&one(Ty::I64, Ty::U8)), vec![]);
    assert_eq!(reasons(&one(Ty::U32, Ty::U64)), vec![]);
    assert_eq!(reasons(&one(Ty::Usize, Ty::U8)), vec![Unbounded]);
    assert_eq!(reasons(&one(Ty::I64, Ty::U16)), vec![Unbounded]);
}

/// `v != c` trims exactly one value off the end of `v`'s range that `c` sits
/// at: at the low end the least count becomes `c + 1` (one element of a
/// line-sized element still fits, so the site is unbounded, not "can never
/// succeed"); at the high end the bound becomes `c - 1`.
#[test]
fn a_not_equal_guard_trims_exactly_one_value() {
    let program = |c: i128, elem_len: u64| {
        let mut module = module_of(vec![
            block(
                0,
                &[(1, Ty::U64)],
                vec![
                    konst(2, Ty::U64, 0xFF),
                    binop(3, BinOp::And, Ty::U64, 1, 2),
                    konst(4, Ty::U64, c),
                    icmp(5, ICmpOp::Ne, Ty::U64, 3, 4),
                    condbr(5, (1, &[]), (2, &[])),
                ],
            ),
            block(1, &[], vec![ret()]),
            block(2, &[], vec![ret()]),
        ]);
        let u8_id = module
            .add_type(Ty::U8)
            .expect("Module::add_type: test fixture");
        module.functions[0].blocks[1]
            .body
            .insert(0, alloca(6, Ty::Array(u8_id, elem_len), Some(3)));
        module
    };
    // `(n & 0xFF) != 0`: counts 1..=255 of a line-sized element. One fits,
    // so the site is unbounded; a trim past 1 would call it never-fitting.
    let found = check_allocation_bounds(&program(0, LIMIT_64 as u64));
    assert_eq!(found.len(), 1);
    assert_eq!(found[0].reason, Unbounded, "one element fits: {found:?}");
    // `(n & 0xFF) != 255`: at most 254 elements of `isize::MAX / 254` bytes.
    let elem = (LIMIT_64 / 254) as u64;
    assert_eq!(reasons(&program(255, elem)), vec![]);
    assert_eq!(reasons(&program(254, elem)), vec![Unbounded]);
}

/// The overflow flag's TRUE edge carries no fact: there the result is the
/// wrapped value. Here every execution overflows (`n | 2^63` times 2), so the
/// unwrapped range is empty; reading it on the true edge would call the
/// allocation unreachable and drop it.
#[test]
fn the_overflow_edge_keeps_the_wrapped_result() {
    let module = module_of(vec![
        block(
            0,
            &[(1, Ty::U64)],
            vec![
                konst(2, Ty::U64, 1 << 63),
                binop(3, BinOp::Or, Ty::U64, 1, 2),
                konst(4, Ty::U64, 2),
                InstrNode::new(Inst::Overflow {
                    op: OverflowOp::MulOverflow,
                    ty: Ty::U64,
                    lhs: v(3),
                    rhs: v(4),
                })
                .with_results([v(5), v(6)]),
                condbr(6, (1, &[]), (2, &[])),
            ],
        ),
        block(1, &[], vec![heap(7, Ty::U8, 5), ret()]),
        block(2, &[], vec![heap(8, Ty::U8, 5), ret()]),
    ]);
    let found = check_allocation_bounds(&module);
    assert_eq!(found.len(), 1, "{found:?}");
    assert_eq!((found[0].reason, found[0].block), (Unbounded, 1));
}

/// Each rule of the analysis bounds the shape it is for. (Soundness of every
/// rule is `alloc_bound_property_tests.rs`; this is precision, so a rule that
/// silently gives up is caught too.) Every count derives from an unchecked
/// `n: u64` and sizes 8-byte elements, so without its rule each one would
/// be unbounded.
#[test]
fn every_rule_bounds_its_shape() {
    let n = 1;
    let shapes: Vec<(&str, Vec<InstrNode>, u32)> = vec![
        // 1000 - (n & 0xFF) is in 745..=1000.
        (
            "sub",
            vec![
                konst(2, Ty::U64, 0xFF),
                binop(3, BinOp::And, Ty::U64, n, 2),
                konst(4, Ty::U64, 1000),
                binop(5, BinOp::Sub, Ty::U64, 4, 3),
            ],
            5,
        ),
        (
            "or",
            vec![
                konst(2, Ty::U64, 0xFF),
                binop(3, BinOp::And, Ty::U64, n, 2),
                konst(4, Ty::U64, 0x100),
                binop(5, BinOp::Or, Ty::U64, 3, 4),
            ],
            5,
        ),
        (
            "xor",
            vec![
                konst(2, Ty::U64, 0xFF),
                binop(3, BinOp::And, Ty::U64, n, 2),
                konst(4, Ty::U64, 0x0F),
                binop(5, BinOp::Xor, Ty::U64, 3, 4),
            ],
            5,
        ),
        (
            "udiv",
            vec![
                konst(2, Ty::U64, 1 << 40),
                binop(3, BinOp::UDiv, Ty::U64, n, 2),
            ],
            3,
        ),
        (
            "shl by a bounded amount",
            vec![
                konst(2, Ty::U64, 0xFF),
                binop(3, BinOp::And, Ty::U64, n, 2),
                konst(4, Ty::U64, 7),
                binop(5, BinOp::And, Ty::U64, n, 4),
                binop(6, BinOp::Shl, Ty::U64, 3, 5),
            ],
            6,
        ),
        (
            "ctpop",
            vec![def(
                2,
                Inst::UnOp {
                    op: UnOp::CtPop,
                    ty: Ty::U64,
                    operand: v(n),
                },
            )],
            2,
        ),
        (
            "not of a high range",
            vec![
                konst(2, Ty::U64, (u64::MAX - 0xFF).into()),
                binop(3, BinOp::Or, Ty::U64, n, 2),
                def(
                    4,
                    Inst::UnOp {
                        op: UnOp::Not,
                        ty: Ty::U64,
                        operand: v(3),
                    },
                ),
            ],
            4,
        ),
    ];
    for (name, mut body, count) in shapes {
        body.push(alloca(99, Ty::I64, Some(count)));
        assert_eq!(reasons(&straight(body)), vec![], "{name}");
    }
    // Signed operations on non-negative values, and the casts between widths
    // and signedness: `m = n & 0xFFFF` as an `i64`.
    let masked = || {
        vec![
            konst(2, Ty::U64, 0xFFFF),
            binop(3, BinOp::And, Ty::U64, n, 2),
            def(
                4,
                Inst::Cast {
                    op: CastOp::Bitcast,
                    src_ty: Ty::U64,
                    dst_ty: Ty::I64,
                    operand: v(3),
                },
            ),
        ]
    };
    for (name, op) in [
        ("sdiv", BinOp::SDiv),
        ("srem", BinOp::SRem),
        ("ashr", BinOp::AShr),
    ] {
        let mut body = masked();
        body.extend([
            konst(5, Ty::I64, 3),
            binop(6, op, Ty::I64, 4, 5),
            alloca(99, Ty::I64, Some(6)),
        ]);
        assert_eq!(reasons(&straight(body)), vec![], "{name}");
    }
    // `(n & 0x7F) as i8 as i64`: a truncation, then a sign extension of
    // non-negative values.
    let body = vec![
        konst(2, Ty::U64, 0x7F),
        binop(3, BinOp::And, Ty::U64, n, 2),
        def(
            4,
            Inst::Cast {
                op: CastOp::Trunc,
                src_ty: Ty::U64,
                dst_ty: Ty::I8,
                operand: v(3),
            },
        ),
        def(
            5,
            Inst::Cast {
                op: CastOp::SExt,
                src_ty: Ty::I8,
                dst_ty: Ty::I64,
                operand: v(4),
            },
        ),
        alloca(99, Ty::I64, Some(5)),
    ];
    assert_eq!(reasons(&straight(body)), vec![], "trunc then sext");
    // `n == 1000` bounds its true edge.
    let found = check_allocation_bounds(&guarded(ICmpOp::Eq, Ty::U64, 1000, Ty::I64));
    assert_eq!(found.len(), 1);
    assert_eq!((found[0].reason, found[0].block), (Unbounded, 2));
    // A `Switch` default edge trims the case at the end of the range: with
    // `v = n & 0xFF` and a case 255, the default allocates at most 254
    // elements of `isize::MAX / 254` bytes.
    let mut module = module_of(vec![
        block(
            0,
            &[(1, Ty::U64)],
            vec![
                konst(2, Ty::U64, 0xFF),
                binop(3, BinOp::And, Ty::U64, 1, 2),
                InstrNode::new(Inst::Switch {
                    value: v(3),
                    default: bb(2),
                    default_args: vec![],
                    cases: vec![SwitchCase {
                        value: Constant::Int(255),
                        target: bb(1),
                        args: vec![],
                    }],
                    exhaustive_enum_unreachable: false,
                }),
            ],
        ),
        block(1, &[], vec![ret()]),
        block(2, &[], vec![ret()]),
    ]);
    let u8_id = module
        .add_type(Ty::U8)
        .expect("Module::add_type: test fixture");
    let elem = Ty::Array(u8_id, (LIMIT_64 / 254) as u64);
    module.functions[0].blocks[2]
        .body
        .insert(0, alloca(4, elem, Some(3)));
    assert_eq!(reasons(&module), vec![], "switch default");
}

/// A chain of type-table entries (`[ty.k-1; 1]`, refinements) is followed in
/// a loop: a chain far deeper than a thread's stack is sized, not a crash.
#[test]
fn a_long_type_chain_costs_no_stack() {
    const K: u32 = 200_000;
    let mut module = straight(vec![]);
    let mut elem = module
        .add_type(Ty::U64)
        .expect("Module::add_type: test fixture");
    for k in 0..K {
        elem = if k % 2 == 0 {
            module
                .add_type(Ty::Array(elem, 1))
                .expect("Module::add_type: test fixture")
        } else {
            module
                .add_type(Ty::Refine(elem, crate::value::PredId::new(0)))
                .expect("Module::add_type: test fixture")
        };
    }
    let body = &mut module.functions[0].blocks[0].body;
    body.insert(0, alloca(2, Ty::Array(elem, 1 << 60), None));
    body.insert(1, alloca(3, Ty::Array(elem, 1 << 59), None));
    let (found, census) = check(&module);
    let summary: Vec<_> = found.iter().map(|f| (f.reason, f.bytes)).collect();
    assert_eq!(summary, vec![(Exceeds, 1 << 63)]);
    assert_eq!(census.sizes_computed, 2 + module.types.len());
    // A cycle in a chain sizes nothing, in a loop too.
    let mut module = straight(vec![]);
    let first = TyId::new(0);
    for k in 0..K {
        // ty.k = [ty.(k + 1); 2], and the last entry closes the cycle.
        module
            .add_type(Ty::Array(TyId::new((k + 1) % K), 2))
            .expect("Module::add_type: test fixture");
    }
    let body = &mut module.functions[0].blocks[0].body;
    body.insert(0, alloca(2, Ty::Array(first, 1), None));
    assert_eq!(reasons(&module), vec![Unsized]);
}

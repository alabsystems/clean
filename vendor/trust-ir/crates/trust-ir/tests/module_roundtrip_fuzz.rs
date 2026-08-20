// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Module-level roundtrip fuzz test (issue #35).
//
// Where `aggregate_constant_fuzz.rs` hammers `Constant` trees, this file
// exercises whole `Module` values: functions, blocks, block params, every
// `Inst` variant and op sub-variant, every `Ty` form, all proof annotations,
// obligations, certificates, dialect ops, globals, and target info. One
// generated module is fed through all available serialization arms.
//
// The five roundtrip arms and the equality they assert:
//
//   TEXT      string fixed-point: s1 = display(m); m2 = parse(s1);
//             s2 = display(m2); assert s1 == s2.
//             A string fixed-point (NOT `m == m2`) because the text form is
//             intentionally lossy for some fields (the module `types` table,
//             function-level proofs, instruction spans, struct field
//             names/offsets, and table-def ids). Those fields are dropped
//             *symmetrically* — display omits them, so re-display omits them
//             too and the string is stable. Everything the text form *does*
//             emit must round-trip exactly, which is what this arm pins down.
//
//   BINARY    full structural equality: deserialize(serialize(m)) == m.
//
//   JSON      (serde) serde_json::from_str(to_string(m)) == m.
//
//   MSGPACK   (serde) rmp_serde::from_slice(to_vec(m)) == m.
//
//   CANONICAL (fmt) idempotency: c1 = canonical(m); m2 = parse(c1);
//             c2 = canonical(m2); assert c1 == c2.
//
// `Module` derives `PartialEq` with IEEE f64 equality, so every float that
// flows through the binary/serde arms is drawn from a "clean" pool of exactly
// representable values (no NaN / -0.0 / subnormal). Bit-exact float coverage
// for `Constant::Float` already lives in `aggregate_constant_fuzz.rs`; the
// float-bearing fields here (`Constant::Float`, `AttrValue::F64`,
// `BoundedOutput`, `GammaCrownBound::epsilon`) use the clean pool because they
// serialize through serde's *default* f64 codec, not the bit-exact one.
//
// Handwritten xorshift generator (not proptest/rand/cargo-fuzz) for the same
// zero-dependency reason documented in `aggregate_constant_fuzz.rs`.

#![cfg(all(feature = "parser", feature = "binary"))]

use trust_ir::inst::{BindingFrameDef, BindingSlot};
use trust_ir::value::BindingFrameId;
use trust_ir::{
    AtomicRMWOp, AttrValue, BinOp, Block, CallingConv, CastOp, ClosureTy, Constant, DialectInst,
    Divergence, Endianness, EnumDef, EnumVariant, FCmpOp, FatPtrKind, FieldDef, FuncTy, Function,
    Global, ICmpOp, Inst, InstrNode, Linkage, Module, ObligationKind, Ordering, OverflowOp,
    ProofAnnotation, ProofCertificate, ProofDigest, ProofEvidence, ProofFormula, ProofObligation,
    ProofStatus, RecordDef, SetRepr, SourceSpan, StructDef, SwitchCase, TargetInfo, TlsModel, Ty,
    UnOp,
};
use trust_ir::{
    BlockId, ClosureTyId, EnumId, FuncId, FuncTyId, ProofId, ProofTag, RecordId, StructId, TyId,
    ValueId,
};

// ---------------------------------------------------------------------------
// Deterministic xorshift64 generator (no external rand dep).
// ---------------------------------------------------------------------------

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self {
            state: if seed == 0 {
                0x9E37_79B9_7F4A_7C15
            } else {
                seed
            },
        }
    }

    fn next_u64(&mut self) -> u64 {
        let mut x = self.state;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.state = x;
        x
    }

    fn bounded(&mut self, n: u32) -> u32 {
        if n == 0 {
            0
        } else {
            (self.next_u64() as u32) % n
        }
    }

    fn chance(&mut self, n: u32) -> bool {
        self.bounded(n) == 0
    }

    fn one_of<'a, T>(&mut self, xs: &'a [T]) -> &'a T {
        let idx = self.bounded(xs.len() as u32) as usize;
        &xs[idx]
    }
}

// ---------------------------------------------------------------------------
// Shared "clean" pools.
// ---------------------------------------------------------------------------

/// Exactly-representable f64 values that round-trip through the text parser
/// and survive IEEE `PartialEq` after serde/binary. No NaN/-0.0/subnormal.
const CLEAN_FLOATS: &[f64] = &[
    0.0, 1.0, -1.0, 0.5, -0.5, 2.5, -2.5, 3.25, 100.0, -100.0, 0.125, 42.0,
];

/// Identifier-safe names. Struct/enum/record/global/function names are emitted
/// via `@ident` (unquoted) in the text form, so they must be identifier-like.
const IDENTS: &[&str] = &[
    "a", "b", "foo", "bar", "baz", "node", "edge", "x0", "y1", "tmp", "g_val", "f_main",
];

/// Simple ASCII strings used where the text form quotes via `{:?}`
/// (descriptions, prover names, formula payloads). Kept free of quotes,
/// backslashes, and control chars so the quoted form is trivially stable.
const PHRASES: &[&str] = &[
    "ok",
    "needs review",
    "precondition holds",
    "verified by ay",
    "manual audit",
    "loop bound 16",
];

fn clean_float(r: &mut Rng) -> f64 {
    *r.one_of(CLEAN_FLOATS)
}

fn ident(r: &mut Rng) -> String {
    (*r.one_of(IDENTS)).to_string()
}

fn phrase(r: &mut Rng) -> String {
    (*r.one_of(PHRASES)).to_string()
}

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}

fn b(n: u32) -> BlockId {
    BlockId::new(n)
}

// ---------------------------------------------------------------------------
// Exhaustive variant catalogs (shared by the kitchen-sink and the fuzzer).
// ---------------------------------------------------------------------------

fn all_binops() -> Vec<BinOp> {
    use BinOp::*;
    vec![
        Add, Sub, Mul, UDiv, SDiv, URem, SRem, FAdd, FSub, FMul, FDiv, FRem, And, Or, Xor, Shl,
        LShr,
        AShr,
        // NOTE: FMin/FMax and the boolean connectives BAnd/BOr/BXor are
        // deliberately absent. This catalog feeds generated modules that must
        // TYPE-CHECK, and these ops are not applicable to the integer operands
        // the generator produces -- BAnd/BOr/BXor are Bool-only by validation.
        // Their wire tags are covered directly by
        // `binary::bool_connective_tag_tests` instead.
    ]
}

fn all_unops() -> Vec<UnOp> {
    use UnOp::*;
    vec![Neg, FNeg, Not, CtPop]
}

fn all_overflow_ops() -> Vec<OverflowOp> {
    use OverflowOp::*;
    vec![AddOverflow, SubOverflow, MulOverflow]
}

fn all_icmp_ops() -> Vec<ICmpOp> {
    use ICmpOp::*;
    vec![Eq, Ne, Ult, Ule, Ugt, Uge, Slt, Sle, Sgt, Sge]
}

fn all_fcmp_ops() -> Vec<FCmpOp> {
    use FCmpOp::*;
    vec![OEq, ONe, OLt, OLe, OGt, OGe, UEq, UNe, ULt, ULe, UGt, UGe]
}

fn all_cast_ops() -> Vec<CastOp> {
    use CastOp::*;
    vec![
        Trunc,
        ZExt,
        SExt,
        FPTrunc,
        FPExt,
        FPToUI,
        FPToSI,
        UIToFP,
        SIToFP,
        PtrToInt,
        IntToPtr,
        PtrToPtr,
        Bitcast,
        Transmute,
        ReifyFnPointer,
        FPToSISat,
        FPToUISat,
    ]
}

fn all_atomic_rmw_ops() -> Vec<AtomicRMWOp> {
    use AtomicRMWOp::*;
    vec![Xchg, Add, Sub, And, Or, Xor, Max, Min, UMax, UMin]
}

fn all_orderings() -> Vec<Ordering> {
    use Ordering::*;
    vec![Relaxed, Acquire, Release, AcqRel, SeqCst]
}

/// All 30 proof annotations. Float-bearing variants use the clean pool.
fn all_proof_annotations() -> Vec<ProofAnnotation> {
    use ProofAnnotation::*;
    vec![
        InBounds,
        NotNull,
        ValidBorrow,
        UniqueBorrow,
        SharedBorrow,
        ValidDealloc,
        NoOverflow,
        NoWrap,
        DivNonZero,
        ShiftInRange,
        Pure,
        Terminates,
        Deterministic,
        Associative,
        Commutative,
        DataRaceFree,
        AtomicOrdering(Ordering::SeqCst),
        BoundedOutput { lo: -1.0, hi: 1.0 },
        Monotonic,
        NoAlias,
        Aligned(16),
        NoPanic,
        NoUndef,
        ReadonlyTable,
        AppendOnlyBuffer,
        AtomicSetInsert,
        ParallelMap,
        BoundedLoop(4096),
        DivergenceClass(Divergence::Uniform),
        Custom(ProofTag::new(7)),
    ]
}

fn all_obligation_kinds() -> Vec<ObligationKind> {
    use ObligationKind::*;
    vec![
        Precondition,
        Postcondition,
        LoopInvariant,
        TypeInvariant,
        RefinementType,
        TranslationValidation,
        MemorySafety,
        PanicFreedom,
        TemporalSafety,
        Liveness,
    ]
}

fn all_proof_statuses() -> Vec<ProofStatus> {
    use ProofStatus::*;
    vec![Pending, Discharged, Failed, Trusted, Certified]
}

/// All 8 evidence kinds. `epsilon` clean; strings are simple ASCII.
fn all_evidence() -> Vec<ProofEvidence> {
    use ProofEvidence::*;
    vec![
        SmtProof(vec![0, 1, 2, 250, 255]),
        LeanProof("theorem foo by simp".to_string()),
        KaniHarness("harness_check".to_string()),
        GammaCrownBound {
            epsilon: 0.5,
            verified_layers: 12,
        },
        TranslationValidation {
            rule_name: "fold_add_zero".to_string(),
            smt_hash: [3u8; 32],
        },
        Trusted("manual audit".to_string()),
        InheritedFromCallee {
            callee: FuncId::new(2),
            obligation: ProofId::new(1),
        },
        // One catalog entry per `ProofEvidence` variant (the exhaustiveness
        // invariant in `catalogs_are_exhaustive`). The `CleanCic` recheck-bearing
        // form is roundtripped separately in `binary.rs` /
        // `proof/tests.rs::proof_evidence_clean_cic_serde_roundtrip`.
        CleanCic {
            term: vec![0xDE, 0xAD, 0xBE, 0xEF],
            context: vec![0x01, 0x02, 0x03],
            lineage: ProofDigest::sha256([4u8; 32]),
            kernel_recheck: Some(trust_ir::CleanCicKernelRecheck {
                module: "Crownproof.SlackCertZ".to_string(),
                theorems: vec![
                    "NNVerify.farkas_scale".to_string(),
                    "NNVerify.farkas_combine_2_le_bound".to_string(),
                ],
                anchor: trust_ir::proof::KERNEL_ANCHOR_FARKAS_CONSTRUCTIVE.to_string(),
                allowed_axioms: vec![
                    "propext".to_string(),
                    "Classical.choice".to_string(),
                    "Quot.sound".to_string(),
                ],
            }),
        },
    ]
}

// ---------------------------------------------------------------------------
// Body builder: collects instruction nodes with auto-numbered SSA results.
// ---------------------------------------------------------------------------

struct Body {
    nodes: Vec<InstrNode>,
    next: u32,
}

impl Body {
    fn new(start: u32) -> Self {
        Self {
            nodes: Vec::new(),
            next: start,
        }
    }

    fn fresh(&mut self) -> ValueId {
        let id = ValueId::new(self.next);
        self.next += 1;
        id
    }

    /// Push a value-producing instruction with one fresh result.
    fn def(&mut self, inst: Inst) -> ValueId {
        let r = self.fresh();
        self.nodes.push(InstrNode::new(inst).with_result(r));
        r
    }

    /// Push a value-producing instruction with `n` fresh results.
    fn def_n(&mut self, inst: Inst, n: u32) -> Vec<ValueId> {
        let rs: Vec<ValueId> = (0..n).map(|_| self.fresh()).collect();
        self.nodes
            .push(InstrNode::new(inst).with_results(rs.iter().copied()));
        rs
    }

    /// Push a void instruction (no result).
    fn void(&mut self, inst: Inst) {
        self.nodes.push(InstrNode::new(inst));
    }

    /// Push a value-producing instruction carrying proof annotations.
    fn def_proofs(&mut self, inst: Inst, proofs: Vec<ProofAnnotation>) -> ValueId {
        let r = self.fresh();
        let mut node = InstrNode::new(inst).with_result(r);
        for p in proofs {
            node = node.with_proof(p);
        }
        self.nodes.push(node);
        r
    }
}

// ---------------------------------------------------------------------------
// Roundtrip oracles.
// ---------------------------------------------------------------------------

/// TEXT arm: display is a string fixed-point under parse.
fn rt_text(m: &Module, label: &str) {
    let s1 = format!("{m}");
    let m2 = trust_ir::parser::parse_module(&s1)
        .unwrap_or_else(|e| panic!("[{label}] text parse failed: {e}\n--- text ---\n{s1}\n---"));
    let s2 = format!("{m2}");
    assert_eq!(
        s1, s2,
        "[{label}] text display is not a parse fixed-point\n--- s1 ---\n{s1}\n--- s2 ---\n{s2}\n"
    );
}

/// BINARY arm: full structural equality.
fn rt_binary(m: &Module, label: &str) {
    let bytes = trust_ir::binary::serialize_module(m);
    let decoded = trust_ir::binary::deserialize_module(&bytes)
        .unwrap_or_else(|e| panic!("[{label}] binary decode failed: {e:?}"));
    assert!(
        &decoded == m,
        "[{label}] binary roundtrip changed the module"
    );
}

#[cfg(feature = "serde")]
fn rt_serde_json(m: &Module, label: &str) {
    let json = serde_json::to_string(m).expect("json encode");
    let decoded: Module =
        serde_json::from_str(&json).unwrap_or_else(|e| panic!("[{label}] json decode failed: {e}"));
    assert!(&decoded == m, "[{label}] json roundtrip changed the module");
}

#[cfg(feature = "serde")]
fn rt_serde_msgpack(m: &Module, label: &str) {
    let bytes = rmp_serde::to_vec(m).expect("msgpack encode");
    let decoded: Module = rmp_serde::from_slice(&bytes)
        .unwrap_or_else(|e| panic!("[{label}] msgpack decode failed: {e}"));
    assert!(
        &decoded == m,
        "[{label}] msgpack roundtrip changed the module"
    );
}

#[cfg(feature = "fmt")]
fn rt_canonical(m: &Module, label: &str) {
    let c1 = trust_ir::format::canonical(m);
    let m2 = trust_ir::parser::parse_module(&c1).unwrap_or_else(|e| {
        panic!("[{label}] canonical text failed to parse: {e}\n--- canonical ---\n{c1}\n---")
    });
    let c2 = trust_ir::format::canonical(&m2);
    assert_eq!(
        c1, c2,
        "[{label}] canonical formatter is not idempotent\n--- c1 ---\n{c1}\n--- c2 ---\n{c2}\n"
    );
}

/// Run every arm enabled by the current feature set.
fn roundtrip_all(m: &Module, label: &str) {
    rt_text(m, label);
    rt_binary(m, label);
    #[cfg(feature = "serde")]
    {
        rt_serde_json(m, label);
        rt_serde_msgpack(m, label);
    }
    #[cfg(feature = "fmt")]
    {
        rt_canonical(m, label);
    }
}

// ---------------------------------------------------------------------------
// Kitchen-sink: one deterministic module touching every variant.
// ---------------------------------------------------------------------------

/// Register one definition per table and return every `Ty` form, in order.
fn register_all_types(m: &mut Module) -> Vec<Ty> {
    let i64_tid: TyId = m.add_type(Ty::I64);
    let bool_tid: TyId = m.add_type(Ty::Bool);

    let s_id: StructId = m.add_struct(StructDef {
        id: StructId::new(0),
        name: "KS_Struct".to_string(),
        fields: vec![
            FieldDef {
                name: "fa".to_string(),
                ty: Ty::I32,
                offset: Some(0),
            },
            FieldDef {
                name: "fb".to_string(),
                ty: Ty::Bool,
                offset: Some(4),
            },
        ],
        size: Some(8),
        align: Some(4),

        repr: Default::default(),
    });
    let e_id: EnumId = m.add_enum(EnumDef {
        id: EnumId::new(0),
        name: "KS_Enum".to_string(),
        variants: vec![
            EnumVariant {
                name: "None".to_string(),
                fields: vec![],
                field_names: Vec::new(),
            },
            EnumVariant {
                name: "Some".to_string(),
                fields: vec![Ty::I32, Ty::Ptr],
                field_names: Vec::new(),
            },
        ],
        discriminants: Vec::new(),
        repr: None,
        layout: None,
    });
    let r_id: RecordId = m.add_record(RecordDef {
        id: RecordId::new(0),
        name: "KS_Record".to_string(),
        fields: vec![
            FieldDef {
                name: "rx".to_string(),
                ty: Ty::F64,
                offset: None,
            },
            FieldDef {
                name: "ry".to_string(),
                ty: Ty::I64,
                offset: None,
            },
        ],
    });
    let ft_id: FuncTyId = m.add_func_type(FuncTy {
        params: vec![Ty::I32, Ty::Ptr],
        returns: vec![Ty::Bool],
        is_vararg: false,
    });
    let ct_id: ClosureTyId = m.add_closure_type(ClosureTy {
        func: ft_id,
        captures: vec![Ty::I64, Ty::Bool],
    });

    vec![
        Ty::I8,
        Ty::I16,
        Ty::I32,
        Ty::I64,
        Ty::I128,
        Ty::U8,
        Ty::U16,
        Ty::U32,
        Ty::U64,
        Ty::U128,
        Ty::F16,
        Ty::F32,
        Ty::F64,
        Ty::Bool,
        Ty::Vector(Box::new(Ty::I32), 4),
        Ty::Ptr,
        Ty::FatPtr(FatPtrKind::Slice(i64_tid)),
        Ty::FatPtr(FatPtrKind::Str),
        Ty::FatPtr(FatPtrKind::TraitObject { trait_id: 9 }),
        Ty::Unit,
        Ty::Never,
        Ty::Struct(s_id),
        Ty::Array(i64_tid, 4),
        Ty::Tuple(vec![Ty::I32, Ty::Bool, Ty::Ptr]),
        Ty::Enum(e_id),
        Ty::Func(ft_id),
        Ty::Ref(Box::new(Ty::I32)),
        Ty::RefMut(Box::new(Ty::I32)),
        Ty::PtrConst(Box::new(Ty::U8)),
        Ty::PtrMut(Box::new(Ty::U8)),
        Ty::Rc(Box::new(Ty::I64)),
        Ty::Set(i64_tid, SetRepr::Bitset),
        Ty::Set(bool_tid, SetRepr::Boxed),
        Ty::Sequence(i64_tid),
        Ty::Record(r_id),
        Ty::Closure(ct_id),
    ]
}

/// Build a single block whose params cover every `Ty` form, then return.
fn ty_coverage_block(types: &[Ty]) -> Block {
    let mut blk = Block::new(b(0));
    blk.params = types
        .iter()
        .enumerate()
        .map(|(i, t)| (v(i as u32), t.clone()))
        .collect();
    blk.body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    blk
}

/// Build the giant instruction-coverage body in bb0; the function also has
/// bb1/bb2 as branch targets (with params) and bb3 (an `unreachable` sink).
fn inst_coverage_blocks() -> Vec<Block> {
    // bb0 params provide typed operands; results auto-number after them.
    let params: Vec<(ValueId, Ty)> = vec![
        (v(0), Ty::Ptr),
        (v(1), Ty::I64),
        (v(2), Ty::Bool),
        (v(3), Ty::F64),
        (v(4), Ty::I64),
        (v(5), Ty::Ptr),
        (v(6), Ty::I32),
        (v(7), Ty::F64),
    ];
    let (ptr, i, cond, fl, i2) = (v(0), v(1), v(2), v(3), v(4));

    let mut body = Body::new(8);

    // --- every BinOp op ---
    for op in all_binops() {
        let is_float = matches!(
            op,
            BinOp::FAdd | BinOp::FSub | BinOp::FMul | BinOp::FDiv | BinOp::FRem
        );
        let (ty, l, r) = if is_float {
            (Ty::F64, fl, v(7))
        } else {
            (Ty::I64, i, i2)
        };
        body.def(Inst::BinOp {
            op,
            ty,
            lhs: l,
            rhs: r,
        });
    }

    // --- every UnOp op ---
    for op in all_unops() {
        let (ty, operand) = if matches!(op, UnOp::FNeg) {
            (Ty::F64, fl)
        } else {
            (Ty::I64, i)
        };
        body.def(Inst::UnOp { op, ty, operand });
    }

    // --- every Overflow op (two results each) ---
    for op in all_overflow_ops() {
        body.def_n(
            Inst::Overflow {
                op,
                ty: Ty::I64,
                lhs: i,
                rhs: i2,
            },
            2,
        );
    }

    // --- every integer compare ---
    for op in all_icmp_ops() {
        body.def(Inst::ICmp {
            op,
            ty: Ty::I64,
            lhs: i,
            rhs: i2,
        });
    }

    // --- every float compare ---
    for op in all_fcmp_ops() {
        body.def(Inst::FCmp {
            op,
            ty: Ty::F64,
            lhs: fl,
            rhs: v(7),
        });
    }

    // --- every cast op ---
    for op in all_cast_ops() {
        body.def(Inst::Cast {
            op,
            src_ty: Ty::I32,
            dst_ty: Ty::I64,
            operand: i,
        });
    }

    // --- every atomic RMW op ---
    for op in all_atomic_rmw_ops() {
        body.def(Inst::AtomicRMW {
            op,
            ty: Ty::I64,
            ptr,
            value: i,
            ordering: Ordering::SeqCst,
        });
    }

    // --- every memory ordering (via fences) ---
    for ordering in all_orderings() {
        body.void(Inst::Fence { ordering });
    }

    // --- memory ops (both the Some/true and None/false field shapes) ---
    body.def_proofs(
        Inst::Load {
            ty: Ty::I64,
            ptr,
            volatile: true,
            align: Some(8),
        },
        vec![ProofAnnotation::InBounds, ProofAnnotation::NotNull],
    );
    body.def(Inst::Load {
        ty: Ty::I64,
        ptr,
        volatile: false,
        align: None,
    });
    body.void(Inst::Store {
        ty: Ty::I64,
        ptr,
        value: i,
        volatile: true,
        align: Some(4),
    });
    body.void(Inst::Store {
        ty: Ty::I64,
        ptr,
        value: i,
        volatile: false,
        align: None,
    });
    body.def(Inst::Alloca {
        ty: Ty::I64,
        count: Some(i),
        align: Some(16),
    });
    body.def(Inst::Alloca {
        ty: Ty::I64,
        count: None,
        align: None,
    });
    body.def(Inst::GEP {
        pointee_ty: Ty::I64,
        base: ptr,
        indices: vec![i, i2],
        inbounds: false,
    });

    // --- fat-pointer split/join ---
    body.def(Inst::PtrData {
        ptr_ty: Ty::Ptr,
        ptr,
    });
    body.def(Inst::PtrMetadata {
        ptr_ty: Ty::Ptr,
        metadata_ty: Ty::I64,
        ptr,
    });
    body.def(Inst::PtrFromParts {
        ptr_ty: Ty::Ptr,
        metadata_ty: Ty::I64,
        data: ptr,
        metadata: i,
    });

    // --- atomics ---
    body.def(Inst::AtomicLoad {
        ty: Ty::I64,
        ptr,
        ordering: Ordering::Acquire,
    });
    body.void(Inst::AtomicStore {
        ty: Ty::I64,
        ptr,
        value: i,
        ordering: Ordering::Release,
    });
    body.def_n(
        Inst::CmpXchg {
            ty: Ty::I64,
            ptr,
            expected: i,
            desired: i2,
            success: Ordering::SeqCst,
            failure: Ordering::Acquire,
        },
        2,
    );

    // --- calls ---
    body.def(Inst::Call {
        callee: FuncId::new(0),
        args: vec![i, i2],
    });
    body.def(Inst::CallIndirect {
        callee: ptr,
        sig: FuncTyId::new(0),
        args: vec![i],

        calling_conv: trust_ir::CallingConv::C,
    });

    // --- aggregates ---
    body.def(Inst::ExtractField {
        ty: Ty::I64,
        aggregate: ptr,
        field: 1,
    });
    body.def(Inst::InsertField {
        ty: Ty::I64,
        aggregate: ptr,
        field: 0,
        value: i,
    });
    body.def(Inst::ExtractElement {
        ty: Ty::I64,
        array: ptr,
        index: i,
    });
    body.def(Inst::InsertElement {
        ty: Ty::I64,
        array: ptr,
        index: i,
        value: i2,
    });

    // --- constants (scalar + one aggregate) ---
    body.def(Inst::Const {
        ty: Ty::I64,
        value: Constant::Int(-42),
    });
    body.def(Inst::Const {
        ty: Ty::F64,
        value: Constant::Float(3.25),
    });
    body.def(Inst::Const {
        ty: Ty::Bool,
        value: Constant::Bool(true),
    });
    body.def(Inst::Const {
        ty: Ty::Tuple(vec![Ty::I32, Ty::Bool]),
        value: Constant::Aggregate(vec![Constant::Int(7), Constant::Bool(false)]),
    });
    body.def(Inst::NullPtr);
    body.def(Inst::Undef { ty: Ty::I64 });

    // --- proof-carrying pseudo ops ---
    body.void(Inst::Assume { cond });
    body.void(Inst::Assert { cond });
    body.def(Inst::Copy {
        ty: Ty::I64,
        operand: i,
    });
    // Select uses a SCALAR type: a vector select would trigger the only
    // parse-time validation rule (`validate_vector_select_contracts`).
    body.def(Inst::Select {
        ty: Ty::I64,
        cond,
        then_val: i,
        else_val: i2,
    });

    // --- borrow / ARC / dealloc ---
    body.def(Inst::Borrow { ptr });
    body.def(Inst::BorrowMut { ptr });
    body.void(Inst::EndBorrow { borrow_ptr: ptr });
    body.void(Inst::Retain { ptr });
    body.void(Inst::Release { ptr });
    body.def(Inst::IsUnique { ptr });
    body.void(Inst::Dealloc { ptr });

    // --- binding frames ---
    let frame = body.def(Inst::OpenFrame {
        def: BindingFrameDef::new(
            BindingFrameId::new(0),
            "quant frame",
            vec![
                BindingSlot::new("i", Ty::I64),
                BindingSlot::new("j", Ty::Bool),
            ],
        ),
    });
    let frame2 = body.def(Inst::BindSlot {
        frame,
        slot: 0,
        value: i,
    });
    body.def(Inst::LoadSlot {
        frame: frame2,
        slot: 0,
        ty: Ty::I64,
    });
    body.void(Inst::CloseFrame { frame: frame2 });

    // --- dialect ops: every AttrValue kind, a non-default version, and the
    //     default-version/no-attr shape ---
    body.def(Inst::DialectOp(Box::new(
        DialectInst::new("verif", "bfs_step")
            .with_operands([ptr, i])
            .with_result_ty(Ty::I64)
            .with_attr("a_i64", AttrValue::I64(-7))
            .with_attr("a_u64", AttrValue::U64(42))
            .with_attr("a_f64", AttrValue::F64(2.5))
            .with_attr("a_bool", AttrValue::Bool(true))
            .with_attr("a_str", AttrValue::Str("frontier".to_string()))
            .with_attr("a_bytes", AttrValue::Bytes(vec![0xde, 0xad, 0xbe, 0xef]))
            .with_attr("a_ty", AttrValue::Ty(Ty::Ptr))
            .with_version(3),
    )));
    body.void(Inst::DialectOp(Box::new(DialectInst::new(
        "gpu", "barrier",
    ))));

    // --- a node carrying ALL 30 proof annotations (text #proof: path) ---
    body.def_proofs(
        Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I64,
            lhs: i,
            rhs: i2,
        },
        all_proof_annotations(),
    );

    // --- terminators (mid-block terminators parse fine; bb0 ends here) ---
    body.void(Inst::Br {
        target: b(1),
        args: vec![i, cond],
    });
    body.void(Inst::CondBr {
        cond,
        then_target: b(1),
        then_args: vec![i],
        else_target: b(2),
        else_args: vec![],
    });
    body.void(Inst::Switch {
        value: i,
        default: b(2),
        default_args: vec![i],
        cases: vec![
            SwitchCase {
                value: Constant::Int(0),
                target: b(1),
                args: vec![cond],
            },
            SwitchCase {
                value: Constant::Int(1),
                target: b(3),
                args: vec![],
            },
        ],
        exhaustive_enum_unreachable: false,
    });
    body.void(Inst::Return {
        values: vec![i, cond],
    });
    body.void(Inst::Unreachable);

    let mut bb0 = Block::new(b(0));
    bb0.params = params;
    bb0.body = body.nodes;

    // bb1/bb2 receive branch args; bb3 is an unreachable sink.
    let mut bb1 = Block::new(b(1));
    bb1.params = vec![(v(200), Ty::I64), (v(201), Ty::Bool)];
    bb1.body.push(InstrNode::new(Inst::Br {
        target: b(2),
        args: vec![v(200)],
    }));

    let mut bb2 = Block::new(b(2));
    bb2.params = vec![(v(210), Ty::I64)];
    bb2.body.push(InstrNode::new(Inst::Return {
        values: vec![v(210)],
    }));

    let mut bb3 = Block::new(b(3));
    bb3.body.push(InstrNode::new(Inst::Unreachable));

    vec![bb0, bb1, bb2, bb3]
}

fn build_kitchen_sink() -> Module {
    let mut m = Module::new("kitchen_sink");
    m.target_info = Some(TargetInfo {
        triple: "arm64-apple-macosx".to_string(),
        pointer_size: 64,
        endianness: Endianness::Little,
        // ABI pinning (v20): non-default values so the kitchen-sink pins the
        // stable ABI id + struct-passing policy through every format arm.
        abi: Some("aapcs64".to_string()),
        struct_passing: trust_ir::StructPassingPolicy::AlwaysMemory,
    });

    let types = register_all_types(&mut m);

    // fn 0: every-Ty params, single return.
    let ft0 = m.add_func_type(FuncTy {
        params: types.clone(),
        returns: vec![],
        is_vararg: false,
    });
    let mut f_types = Function::new(FuncId::new(0), "ks_types", ft0, b(0));
    f_types.blocks = vec![ty_coverage_block(&types)];
    // carry the first half of the annotations at function level (dropped in
    // text, preserved in binary/serde).
    f_types.proofs = all_proof_annotations();
    m.add_function(f_types);

    // fn 1: every instruction variant + sub-op, with a non-default linkage and
    // calling convention (their text emission is exercised here).
    let ft1 = m.add_func_type(FuncTy {
        params: vec![
            Ty::Ptr,
            Ty::I64,
            Ty::Bool,
            Ty::F64,
            Ty::I64,
            Ty::Ptr,
            Ty::I32,
            Ty::F64,
        ],
        returns: vec![Ty::I64],
        is_vararg: true,
    });
    let mut f_insts = Function::new(FuncId::new(1), "ks_insts", ft1, b(0));
    f_insts.linkage = Linkage::Internal;
    f_insts.calling_conv = CallingConv::Swift;
    f_insts.blocks = inst_coverage_blocks();
    // attach a span to the first node so the (text-dropped) span field is
    // present for the binary/serde arms.
    if let Some(first) = f_insts.blocks[0].body.first_mut() {
        first.span = Some(SourceSpan {
            file: 1,
            line: 10,
            col: 4,
        });
    }
    m.add_function(f_insts);

    // A global per linkage / tls / mutability shape worth covering.
    m.globals.push(Global {
        name: "g_ro".to_string(),
        ty: Ty::I64,
        mutable: false,
        initializer: Some(Constant::Int(7)),
        linkage: Linkage::External,
        tls: None,
        align: None,
    });
    m.globals.push(Global {
        name: "g_mut".to_string(),
        ty: Ty::F64,
        mutable: true,
        initializer: Some(Constant::Float(0.125)),
        linkage: Linkage::Internal,
        tls: Some(TlsModel::LocalExec),
        align: None,
    });
    m.globals.push(Global {
        name: "g_weak".to_string(),
        ty: Ty::Bool,
        mutable: false,
        initializer: None,
        linkage: Linkage::Weak,
        tls: Some(TlsModel::GeneralDynamic),
        align: None,
    });

    // Every obligation kind; statuses and formulae cycled across them.
    let statuses = all_proof_statuses();
    for (idx, kind) in all_obligation_kinds().into_iter().enumerate() {
        let status = statuses[idx % statuses.len()];
        let mut ob = ProofObligation::new(
            ProofId::new(idx as u32),
            kind,
            status,
            format!("obligation {idx}"),
        );
        // Give roughly half of them a formula (covering the optional-field
        // emission and both ProofFormula constructors).
        if idx % 2 == 0 {
            ob = ob.with_formula(ProofFormula::trust_types_json(
                "{\"op\":\"le\"}",
                "(<= x 1)",
                "Bool",
            ));
        } else if idx % 3 == 0 {
            ob = ob.with_formula(ProofFormula::smtlib2("(>= x 0)", "Bool"));
        }
        m.proof_obligations.push(ob);
    }

    // Every evidence kind, each pinned to an existing obligation id.
    for (idx, evidence) in all_evidence().into_iter().enumerate() {
        m.proof_certificates.push(ProofCertificate {
            obligation: ProofId::new(idx as u32),
            prover: format!("prover_{idx}"),
            evidence,
        });
    }

    m
}

// ---------------------------------------------------------------------------
// Randomized module generator (structure-aware).
// ---------------------------------------------------------------------------

/// A small pool of scalar types used for random block params / operands.
fn rand_scalar_ty(r: &mut Rng) -> Ty {
    match r.bounded(8) {
        0 => Ty::I32,
        1 => Ty::I64,
        2 => Ty::U32,
        3 => Ty::U64,
        4 => Ty::Bool,
        5 => Ty::F32,
        6 => Ty::F64,
        _ => Ty::Ptr,
    }
}

fn rand_scalar_const(r: &mut Rng) -> Constant {
    match r.bounded(3) {
        0 => Constant::Int((r.next_u64() as i64 % 1000) as i128),
        1 => Constant::Float(clean_float(r)),
        _ => Constant::Bool(r.chance(2)),
    }
}

/// Pick a random subset of the 30 proof annotations.
fn rand_proofs(r: &mut Rng) -> Vec<ProofAnnotation> {
    let all = all_proof_annotations();
    let mut out = Vec::new();
    for (idx, p) in all.into_iter().enumerate() {
        // ~1/4 chance each, deterministic per position.
        if (r.next_u64() as usize ^ idx).is_multiple_of(4) {
            out.push(p);
        }
    }
    out
}

/// Generate one instruction referencing operands in `[0, defined)`, returning
/// it plus its result arity. Restricted to variants whose round-trip does not
/// depend on a particular type relationship (the kitchen-sink owns exhaustive
/// variant coverage; this keeps the random structural permutations valid).
fn rand_inst(r: &mut Rng, defined: u32) -> (Inst, u32) {
    let operand = |r: &mut Rng| v(r.bounded(defined.max(1)));
    match r.bounded(20) {
        0 => (
            Inst::BinOp {
                op: *r.one_of(&all_binops()),
                ty: Ty::I64,
                lhs: operand(r),
                rhs: operand(r),
            },
            1,
        ),
        1 => (
            Inst::UnOp {
                op: *r.one_of(&all_unops()),
                ty: Ty::I64,
                operand: operand(r),
            },
            1,
        ),
        2 => (
            Inst::ICmp {
                op: *r.one_of(&all_icmp_ops()),
                ty: Ty::I64,
                lhs: operand(r),
                rhs: operand(r),
            },
            1,
        ),
        3 => (
            Inst::FCmp {
                op: *r.one_of(&all_fcmp_ops()),
                ty: Ty::F64,
                lhs: operand(r),
                rhs: operand(r),
            },
            1,
        ),
        4 => (
            Inst::Cast {
                op: *r.one_of(&all_cast_ops()),
                src_ty: Ty::I32,
                dst_ty: Ty::I64,
                operand: operand(r),
            },
            1,
        ),
        5 => (
            Inst::Load {
                ty: rand_scalar_ty(r),
                ptr: operand(r),
                volatile: r.chance(2),
                align: if r.chance(2) { Some(8) } else { None },
            },
            1,
        ),
        6 => (
            Inst::Store {
                ty: rand_scalar_ty(r),
                ptr: operand(r),
                value: operand(r),
                volatile: r.chance(2),
                align: if r.chance(2) { Some(4) } else { None },
            },
            0,
        ),
        7 => (
            Inst::Alloca {
                ty: rand_scalar_ty(r),
                count: if r.chance(2) { Some(operand(r)) } else { None },
                align: if r.chance(2) { Some(16) } else { None },
            },
            1,
        ),
        8 => (
            Inst::GEP {
                pointee_ty: rand_scalar_ty(r),
                base: operand(r),
                indices: vec![operand(r), operand(r)],
                inbounds: r.chance(2),
            },
            1,
        ),
        9 => (
            Inst::Const {
                ty: rand_scalar_ty(r),
                value: rand_scalar_const(r),
            },
            1,
        ),
        10 => (
            Inst::Copy {
                ty: rand_scalar_ty(r),
                operand: operand(r),
            },
            1,
        ),
        11 => (
            // Scalar select only (no vector-select parse validation).
            Inst::Select {
                ty: rand_scalar_ty(r),
                cond: operand(r),
                then_val: operand(r),
                else_val: operand(r),
            },
            1,
        ),
        12 => (
            Inst::AtomicRMW {
                op: *r.one_of(&all_atomic_rmw_ops()),
                ty: Ty::I64,
                ptr: operand(r),
                value: operand(r),
                ordering: *r.one_of(&all_orderings()),
            },
            1,
        ),
        13 => (
            Inst::AtomicLoad {
                ty: Ty::I64,
                ptr: operand(r),
                ordering: *r.one_of(&all_orderings()),
            },
            1,
        ),
        14 => (
            Inst::Fence {
                ordering: *r.one_of(&all_orderings()),
            },
            0,
        ),
        15 => (Inst::Borrow { ptr: operand(r) }, 1),
        16 => (Inst::IsUnique { ptr: operand(r) }, 1),
        17 => (Inst::Assume { cond: operand(r) }, 0),
        18 => (
            Inst::Undef {
                ty: rand_scalar_ty(r),
            },
            1,
        ),
        _ => (
            Inst::DialectOp(Box::new(
                DialectInst::new("verif", "step")
                    .with_operand(operand(r))
                    .with_result_ty(Ty::I64)
                    .with_attr("k", AttrValue::U64(r.next_u64() % 256)),
            )),
            1,
        ),
    }
}

/// Generate a random terminator targeting blocks in `[0, nblocks)`.
fn rand_terminator(r: &mut Rng, defined: u32, nblocks: u32) -> Inst {
    let operand = |r: &mut Rng| v(r.bounded(defined.max(1)));
    let blk = |r: &mut Rng| b(r.bounded(nblocks.max(1)));
    match r.bounded(5) {
        0 => Inst::Return {
            values: if r.chance(2) {
                vec![operand(r)]
            } else {
                vec![]
            },
        },
        1 => Inst::Br {
            target: blk(r),
            args: vec![],
        },
        2 => Inst::CondBr {
            cond: operand(r),
            then_target: blk(r),
            then_args: vec![],
            else_target: blk(r),
            else_args: vec![],
        },
        3 => Inst::Switch {
            value: operand(r),
            default: blk(r),
            default_args: vec![],
            cases: vec![SwitchCase {
                value: Constant::Int(r.bounded(4) as i128),
                target: blk(r),
                args: vec![],
            }],
            exhaustive_enum_unreachable: false,
        },
        _ => Inst::Unreachable,
    }
}

fn gen_function(r: &mut Rng, id: u32, ft: FuncTyId) -> Function {
    let nblocks = 1 + r.bounded(3);
    let mut func = Function::new(FuncId::new(id), ident(r), ft, b(0));
    func.linkage = *r.one_of(&[
        Linkage::External,
        Linkage::Internal,
        Linkage::Private,
        Linkage::Weak,
        Linkage::LinkOnce,
    ]);
    func.calling_conv = *r.one_of(&[
        CallingConv::C,
        CallingConv::Fast,
        CallingConv::Cold,
        CallingConv::Rust,
        CallingConv::Swift,
    ]);
    if r.chance(2) {
        func.proofs = rand_proofs(r);
    }

    // A single rolling SSA counter across the whole function keeps all
    // defined values unique (clean input for the canonical renumberer).
    let mut next: u32 = 0;
    for bi in 0..nblocks {
        let mut blk = Block::new(b(bi));
        // optional block params
        let nparams = r.bounded(3);
        for _ in 0..nparams {
            blk.params.push((v(next), rand_scalar_ty(r)));
            next += 1;
        }
        let nbody = r.bounded(6);
        for _ in 0..nbody {
            let defined = next.max(1);
            let (inst, arity) = rand_inst(r, defined);
            let mut node = InstrNode::new(inst);
            for _ in 0..arity {
                node = node.with_result(v(next));
                next += 1;
            }
            if r.chance(3) {
                for p in rand_proofs(r) {
                    node = node.with_proof(p);
                }
            }
            if r.chance(4) {
                node.span = Some(SourceSpan {
                    file: r.bounded(3),
                    line: r.bounded(100),
                    col: r.bounded(80),
                });
            }
            blk.body.push(node);
        }
        let term = rand_terminator(r, next.max(1), nblocks);
        blk.body.push(InstrNode::new(term));
        func.blocks.push(blk);
    }
    func
}

fn gen_module(r: &mut Rng) -> Module {
    let mut m = Module::new(phrase(r));

    if r.chance(2) {
        m.target_info = Some(TargetInfo {
            triple: ident(r),
            pointer_size: *r.one_of(&[32u32, 64]),
            endianness: if r.chance(2) {
                Endianness::Little
            } else {
                Endianness::Big
            },
            // ABI pinning (v20): fuzz the stable ABI id + struct-passing
            // policy so the new TargetInfo fields round-trip under mutation.
            abi: if r.chance(2) { Some(ident(r)) } else { None },
            struct_passing: if r.chance(2) {
                trust_ir::StructPassingPolicy::NativeC
            } else {
                trust_ir::StructPassingPolicy::AlwaysMemory
            },
        });
    }

    // structs (dense ids matching table position)
    let n_structs = r.bounded(3);
    for si in 0..n_structs {
        let nf = r.bounded(3);
        let fields = (0..nf)
            .map(|fi| FieldDef {
                name: format!("f{fi}"),
                ty: rand_scalar_ty(r),
                offset: if r.chance(2) {
                    Some(fi as u64 * 4)
                } else {
                    None
                },
            })
            .collect();
        m.add_struct(StructDef {
            id: StructId::new(si),
            name: format!("S{si}"),
            fields,
            size: if r.chance(2) { Some(16) } else { None },
            align: if r.chance(2) { Some(8) } else { None },

            repr: Default::default(),
        });
    }

    // enums
    let n_enums = r.bounded(2);
    for ei in 0..n_enums {
        let nv = 1 + r.bounded(3);
        let variants = (0..nv)
            .map(|vi| EnumVariant {
                name: format!("V{vi}"),
                fields: if r.chance(2) {
                    vec![rand_scalar_ty(r)]
                } else {
                    vec![]
                },
                field_names: Vec::new(),
            })
            .collect();
        // v19 canonical-layout fields, sometimes: an explicit first
        // discriminant (rest implicit — canonical trimmed form, so the text
        // format round-trips it verbatim) and sometimes a repr hint wide
        // enough for start..start+nv (start <= 100, nv <= 3, so U16 always
        // fits).
        let discriminants = if r.chance(2) {
            vec![Some(i128::from(r.bounded(101)))]
        } else {
            Vec::new()
        };
        let repr = if r.chance(3) {
            Some(trust_ir::ty::EnumTagRepr::U16)
        } else {
            None
        };
        m.add_enum(EnumDef {
            id: EnumId::new(ei),
            name: format!("E{ei}"),
            variants,
            discriminants,
            repr,
            layout: None,
        });
    }

    // records
    let n_records = r.bounded(2);
    for ri in 0..n_records {
        let nf = 1 + r.bounded(3);
        let fields = (0..nf)
            .map(|fi| FieldDef {
                name: format!("r{fi}"),
                ty: rand_scalar_ty(r),
                offset: None,
            })
            .collect();
        m.add_record(RecordDef {
            id: RecordId::new(ri),
            name: format!("R{ri}"),
            fields,
        });
    }

    // function types (positional ids). Always at least one for the functions.
    let n_ft = 1 + r.bounded(3);
    let mut fts = Vec::new();
    for _ in 0..n_ft {
        let np = r.bounded(3);
        let nr = r.bounded(2);
        let ft = m.add_func_type(FuncTy {
            params: (0..np).map(|_| rand_scalar_ty(r)).collect(),
            returns: (0..nr).map(|_| rand_scalar_ty(r)).collect(),
            is_vararg: r.chance(3),
        });
        fts.push(ft);
    }

    // closure types referencing valid func types
    let n_ct = r.bounded(2);
    for _ in 0..n_ct {
        let ft = *r.one_of(&fts);
        let nc = r.bounded(3);
        m.add_closure_type(ClosureTy {
            func: ft,
            captures: (0..nc).map(|_| rand_scalar_ty(r)).collect(),
        });
    }

    // globals (scalar clean initializers)
    let n_globals = r.bounded(3);
    for gi in 0..n_globals {
        let (ty, init) = match r.bounded(4) {
            0 => (
                Ty::I64,
                Some(Constant::Int((r.next_u64() as i64 % 500) as i128)),
            ),
            1 => (Ty::F64, Some(Constant::Float(clean_float(r)))),
            2 => (Ty::Bool, Some(Constant::Bool(r.chance(2)))),
            _ => (Ty::Ptr, None),
        };
        m.globals.push(Global {
            name: format!("g{gi}"),
            ty,
            mutable: r.chance(2),
            initializer: init,
            linkage: *r.one_of(&[Linkage::External, Linkage::Internal, Linkage::Private]),
            tls: if r.chance(3) {
                Some(*r.one_of(&[
                    TlsModel::LocalExec,
                    TlsModel::InitialExec,
                    TlsModel::GeneralDynamic,
                    TlsModel::LocalDynamic,
                ]))
            } else {
                None
            },
            align: if r.chance(3) {
                Some(*r.one_of(&[1u32, 8, 16, 32, 64]))
            } else {
                None
            },
        });
    }

    // functions
    let n_funcs = 1 + r.bounded(3);
    for fi in 0..n_funcs {
        let ft = *r.one_of(&fts);
        let func = gen_function(r, fi, ft);
        m.add_function(func);
    }

    // obligations
    let kinds = all_obligation_kinds();
    let statuses = all_proof_statuses();
    let n_ob = r.bounded(5);
    for oi in 0..n_ob {
        let mut ob = ProofObligation::new(
            ProofId::new(oi),
            r.one_of(&kinds).clone(),
            *r.one_of(&statuses),
            phrase(r),
        );
        if r.chance(2) {
            ob = ob.with_formula(ProofFormula::new(ident(r), phrase(r)));
        }
        m.proof_obligations.push(ob);
    }

    // certificates referencing (possibly out-of-range, which is fine for
    // roundtrip) obligation ids, cycling through every evidence kind.
    let evidences = all_evidence();
    let n_cert = r.bounded(4);
    for ci in 0..n_cert {
        m.proof_certificates.push(ProofCertificate {
            obligation: ProofId::new(r.bounded(n_ob.max(1))),
            prover: ident(r),
            evidence: evidences[(ci as usize) % evidences.len()].clone(),
        });
    }

    m
}

// ---------------------------------------------------------------------------
// Tests.
// ---------------------------------------------------------------------------

const N_CASES: u32 = 2048;
const SEED_MODULE: u64 = 0x7401_C0DE_5EED_0035;

#[test]
fn fuzz_module_roundtrip_all_formats() {
    let mut r = Rng::new(SEED_MODULE);
    for case in 0..N_CASES {
        let m = gen_module(&mut r);
        // Clone-equality is a precondition for any `== m` arm to be meaningful.
        assert!(m.clone() == m, "clone inequality at case {case}");
        roundtrip_all(&m, &format!("fuzz#{case}"));
    }
}

#[test]
fn kitchen_sink_every_variant_roundtrips() {
    let m = build_kitchen_sink();
    roundtrip_all(&m, "kitchen_sink");
}

/// Guards that the kitchen-sink genuinely instantiates every catalog at full
/// size, so the coverage promise in the module header cannot silently rot.
#[test]
fn catalogs_are_exhaustive() {
    assert_eq!(all_binops().len(), 18);
    assert_eq!(all_unops().len(), 4);
    assert_eq!(all_overflow_ops().len(), 3);
    assert_eq!(all_icmp_ops().len(), 10);
    assert_eq!(all_fcmp_ops().len(), 12);
    assert_eq!(all_cast_ops().len(), 17);
    assert_eq!(all_atomic_rmw_ops().len(), 10);
    assert_eq!(all_orderings().len(), 5);
    assert_eq!(all_proof_annotations().len(), 30);
    assert_eq!(all_obligation_kinds().len(), 10);
    assert_eq!(all_proof_statuses().len(), 5);
    assert_eq!(all_evidence().len(), 8);

    // The kitchen-sink module surfaces every type form as block params.
    let mut probe = Module::new("probe");
    assert_eq!(register_all_types(&mut probe).len(), 36);
}

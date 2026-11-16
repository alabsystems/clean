// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The **W2a synthetic chains** — the first synthetic-module tranche of the
//! GAP-2 battery (`docs/analysis/evalir-completion-plan-2026-08-24.md` §5
//! W2a): `select`, `undef`, `unreachable`, `extractelement`, `unop`
//! (not_/ctpop).
//!
//! Unlike the W1 wide chains, NOTHING here was emitted by a producer. Each
//! chain's fixture (`tests/fixtures/synth/*.trust-ir.txt`) and its registered
//! Clean twin (`eval_ir_w2a_synth.rs`, re-exported `ir_w2a_*_module_defs`)
//! were authored together for this measurement, because no clean-kernel body
//! exercises these constructors — that is the [`EnumModel::Synthetic`] label,
//! and it is why every chain records E3 absent by construction. What a green
//! row measures is therefore exactly and only: Clean's kernel and trust-ir's
//! reference interpreter compute the same outcome for the same module text.
//!
//! ## The two DECLARED executor deltas (measured 2026-08-25, trust-ir rev
//! `a4e81b6`, this box — the E2 half; the E1 half is authored and pends the
//! big-box run)
//!
//! * **`undef` has no measurable E2 leg.** The interpreter refuses to execute
//!   `Inst::Undef` ("executing undef would read an undefined value",
//!   `undefined_behavior`, `interpret.rs:619-623`); Clean's arm binds
//!   `IRScalar.undef_` and the module returns it (`ir_w2a_ud_on_run`). The
//!   row is a [`SynthExpect::DeclaredDelta`]: asserted to fault with exactly
//!   that code, printed, never counted as agreement.
//! * **`extractelement` out of bounds diverges by outcome CLASS.** Clean
//!   fails closed with `type_error bad_field` (`ir_w2a_ee_oob`); the
//!   interpreter reports `undefined_behavior` ("element 3 is out of bounds",
//!   `interpret.rs:4507-4516`). Also a `DeclaredDelta` — mapping either class
//!   onto the other would be the vocabulary lie the outcome map exists to
//!   refuse (`clean_verify::ir_semdiff::synth`).
//!
//! Cost offsets are DECLARED 0 on the value-returning rows of every chain;
//! fault rows are unpriced by shape (the interpreter reports no step count on
//! an error). The E2 half of the declaration is measured here by
//! `crystal_a3_synth_e2_instrument_smoke`; the E1 half (least fuels and their
//! tightness) pends the big box (`data/evalir_w2a.PENDING.md`).

use clean_verify::ir_semdiff::synth::{IrFaultName, SynthOutcome};
use clean_verify::ir_semdiff::wide::{wide_agg, wide_args, wide_bool, wide_int, WideEncoding};
use clean_verify::ir_semdiff::{EnumModel, RunResult};
use trust_ir::interpret::{InterpretValue, InterpretValueKind};
use trust_ir::ty::Ty;
use trust_ir::value::StructId;

use super::wide_exec::{iv_u32, SigSpec};

/// What one synthetic row expects of the two executors that exist for it.
pub enum SynthExpect {
    /// Both executors return this value; the row measures agreement, and the
    /// value candidate offered to the kernel first is E2's live answer.
    Ret(RunResult),
    /// Both executors halt with undefined behavior: E1 pins
    /// `IROutcome.ub <fault>` exactly; E2 must report `undefined_behavior`.
    /// Compared at outcome CLASS (`ir_semdiff::synth::OutcomeClass`), with
    /// the exact terms carried in the row's notes.
    UbAgree(IrFaultName),
    /// A MEASURED, DATED executor divergence: the Clean outcome and the
    /// interpreter code are both pinned exactly, printed, and counted as a
    /// declared delta — never agreement, never smoothed into a shared class.
    DeclaredDelta {
        /// What the Clean kernel must pin.
        clean: SynthOutcome,
        /// The exact `InterpretErrorCode` string E2 must report.
        e2_code: &'static str,
        /// The dated, cited reason this divergence is expected.
        why: &'static str,
    },
}

/// One measured input of a synthetic chain.
pub struct SynthInput {
    /// Human-readable label, printed with the row.
    pub label: &'static str,
    /// The `<args> <heap> <next-addr>` tail of the Clean `ir_eval` application.
    pub clean_tail: String,
    /// E2's arguments, handed straight to `execute_function` — every W2a
    /// subject takes its inputs by value, so no harness exists and no
    /// overhead is subtracted.
    pub trust_args: Vec<InterpretValue>,
    /// What this row expects.
    pub expect: SynthExpect,
}

/// One synthetic chain.
pub struct SynthChain {
    /// Short name, used in output and generated def names.
    pub name: &'static str,
    /// The committed synthetic fixture `(file, printed name)` under
    /// `tests/fixtures/` — always a single `synth/`-prefixed file.
    pub fixtures: &'static [(&'static str, &'static str)],
    /// The function id the fixture's body carries.
    pub func_ids: &'static [u32],
    /// struct declarations the composed module needs.
    pub type_decls: &'static str,
    /// Reconstituted signatures, by declared functy index.
    pub sigs: Vec<SigSpec>,
    /// The registered Clean module constant.
    pub clean_module: &'static str,
    /// The function id term inside that module.
    pub clean_fid: &'static str,
    /// The registered stage lines — re-exported from `eval_ir_w2a_synth.rs`,
    /// never re-typed.
    pub clean_defs: &'static [&'static str],
    /// How returned values are wrapped on the Clean side.
    pub encoding: WideEncoding,
    /// Always [`EnumModel::Synthetic`] in this table; carried per chain so the
    /// report prints it rather than implying it.
    pub enum_model: EnumModel,
    /// The declared clean-minus-trust cost offset on value-returning rows.
    pub expected_cost_offset: i64,
    /// Is the input set the WHOLE domain? True only for a genuinely
    /// enumerated domain (`unreachable`'s bool, `undef`'s nullary unit).
    pub total_domain: bool,
    /// Why E3 is absent — for a synthetic module, always by construction.
    pub shipped_absent: &'static str,
    /// The inputs.
    pub inputs: Vec<SynthInput>,
}

/// Why E3 is absent from every synthetic row — shared with the W2b lane
/// (`w2b_chains.rs`), which carries the same by-construction absence.
pub const SYNTHETIC_NO_E3: &str = "the module is SYNTHETIC — authored for this differential; no \
     producer emitted it, so no shipped compiled function exists to call. Absent by \
     construction, not by visibility.";

/// The synthetic chains, in measurement order.
pub fn synth_chains() -> Vec<SynthChain> {
    vec![
        select_probe(),
        undef_probe(),
        unreachable_probe(),
        extractelement_probe(),
        unop_probe(),
    ]
}

/// `select` — the branch-free conditional, `%3 = select u32 %0, %1, %2`.
/// Constructors: `select` (+ `ret`). No arithmetic: both arms transport
/// already-materialized scalars, which is why a `u32::MAX` sentinel row is
/// phrasable without any wrap residue.
fn select_probe() -> SynthChain {
    let case = |label, c: bool, a: u64, b: u64, expect: u64| SynthInput {
        label,
        clean_tail: format!(
            "{} ir_mem0 ir_d0",
            wide_args(&[wide_bool(c), wide_int(a), wide_int(b)])
        ),
        trust_args: vec![
            InterpretValue::bool(c),
            iv_u32(u32::try_from(a).expect("u32 domain")),
            iv_u32(u32::try_from(b).expect("u32 domain")),
        ],
        expect: SynthExpect::Ret(RunResult::Int(expect)),
    };
    SynthChain {
        name: "synth_select",
        fixtures: &[("synth/synth_select.trust-ir.txt", "@synth::select_probe")],
        func_ids: &[0],
        type_decls: "",
        sigs: vec![(910, vec![Ty::Bool, Ty::U32, Ty::U32], vec![Ty::U32])],
        clean_module: "ir_w2a_sel_module",
        clean_fid: "ir_d0",
        clean_defs: clean_verify::spec::ir_w2a_sel_module_defs(),
        encoding: WideEncoding::Scalar,
        enum_model: EnumModel::Synthetic,
        expected_cost_offset: 0,
        total_domain: false,
        shipped_absent: SYNTHETIC_NO_E3,
        inputs: vec![
            case("true picks then 3|9", true, 3, 9, 3),
            case("false picks else 3|9", false, 3, 9, 9),
            case("true on equal arms 0|0", true, 0, 0, 0),
            case("false swaps 7|1", false, 7, 1, 1),
            case(
                "true transports u32::MAX",
                true,
                4_294_967_295,
                2,
                4_294_967_295,
            ),
            case(
                "false transports u32::MAX",
                false,
                2,
                4_294_967_295,
                4_294_967_295,
            ),
        ],
    }
}

/// `undef` — `%0 = undef u32; ret %0`. The one W2a chain with NO measurable
/// E2 leg (module doc): its single row is the declared interpreter-bound
/// delta, and the Clean semantics is pinned kernel-side (`ir_w2a_ud_on_run`
/// plus this row's E1 obligation).
fn undef_probe() -> SynthChain {
    SynthChain {
        name: "synth_undef",
        fixtures: &[("synth/synth_undef.trust-ir.txt", "@synth::undef_probe")],
        func_ids: &[0],
        type_decls: "",
        sigs: vec![(911, vec![], vec![Ty::U32])],
        clean_module: "ir_w2a_ud_module",
        clean_fid: "ir_d0",
        clean_defs: clean_verify::spec::ir_w2a_ud_module_defs(),
        encoding: WideEncoding::Scalar,
        enum_model: EnumModel::Synthetic,
        expected_cost_offset: 0,
        // Nullary: the (unit) domain is fully enumerated by the single row.
        total_domain: true,
        shipped_absent: SYNTHETIC_NO_E3,
        inputs: vec![SynthInput {
            label: "the undef instruction executes",
            clean_tail: "(@IRList.nil IRScalar) ir_mem0 ir_d0".to_owned(),
            trust_args: vec![],
            expect: SynthExpect::DeclaredDelta {
                clean: SynthOutcome::RetUndef,
                e2_code: "undefined_behavior",
                why: "MEASURED 2026-08-25 at trust-ir a4e81b6: the reference interpreter \
                      refuses to execute Inst::Undef ('executing undef would read an \
                      undefined value', interpret.rs:619-623) where Clean's dispatch arm \
                      binds IRScalar.undef_ and returns it (ir_w2a_ud_on_run). An executor \
                      divergence on the whole constructor — recorded, never folded into \
                      agreement.",
            },
        }],
    }
}

/// `unreachable` — condbr to a returning arm or the unreachable arm. The
/// TOTAL bool domain: the false row is the constructor's entire semantics
/// (`ub unreachable` ↔ `undefined_behavior`, the one W2a fault edge where
/// both executors' vocabularies align at class), the true row pins that
/// containing the instruction is not UB.
fn unreachable_probe() -> SynthChain {
    let tail = |c: bool| format!("(ir_vl1 {}) ir_mem0 ir_d0", wide_bool(c));
    SynthChain {
        name: "synth_unreachable",
        fixtures: &[(
            "synth/synth_unreachable.trust-ir.txt",
            "@synth::unreachable_probe",
        )],
        func_ids: &[0],
        type_decls: "",
        sigs: vec![(912, vec![Ty::Bool], vec![Ty::U32])],
        clean_module: "ir_w2a_ur_module",
        clean_fid: "ir_d0",
        clean_defs: clean_verify::spec::ir_w2a_ur_module_defs(),
        encoding: WideEncoding::Scalar,
        enum_model: EnumModel::Synthetic,
        expected_cost_offset: 0,
        total_domain: true,
        shipped_absent: SYNTHETIC_NO_E3,
        inputs: vec![
            SynthInput {
                label: "true takes the returning arm",
                clean_tail: tail(true),
                trust_args: vec![InterpretValue::bool(true)],
                expect: SynthExpect::Ret(RunResult::Int(3)),
            },
            SynthInput {
                label: "false executes unreachable",
                clean_tail: tail(false),
                trust_args: vec![InterpretValue::bool(false)],
                expect: SynthExpect::UbAgree(IrFaultName::Unreachable),
            },
        ],
    }
}

/// `extractelement` — a computed-index element read out of a by-value
/// three-field container, `%2 = extractelement u32 %0, %1`. The three
/// in-range indices pin the index-to-slot map over the fixed triple
/// (5, 11, 2); the out-of-bounds row is the declared class delta.
fn extractelement_probe() -> SynthChain {
    const TRIPLE: [u64; 3] = [5, 11, 2];
    let case = |label, idx: u64, expect: SynthExpect| SynthInput {
        label,
        clean_tail: format!(
            "{} ir_mem0 ir_d0",
            wide_args(&[wide_agg(&TRIPLE), wide_int(idx)])
        ),
        trust_args: vec![
            iv_struct3(555, &TRIPLE),
            iv_u32(u32::try_from(idx).expect("index domain")),
        ],
        expect,
    };
    SynthChain {
        name: "synth_extractelement",
        fixtures: &[(
            "synth/synth_extractelement.trust-ir.txt",
            "@synth::extractelement_probe",
        )],
        func_ids: &[0],
        type_decls: "struct @Trip { u32, u32, u32 } id=555",
        sigs: vec![(913, vec![struct_ty(555), Ty::U32], vec![Ty::U32])],
        clean_module: "ir_w2a_ee_module",
        clean_fid: "ir_d0",
        clean_defs: clean_verify::spec::ir_w2a_ee_module_defs(),
        encoding: WideEncoding::Scalar,
        enum_model: EnumModel::Synthetic,
        expected_cost_offset: 0,
        total_domain: false,
        shipped_absent: SYNTHETIC_NO_E3,
        inputs: vec![
            case("index 0 reads 5", 0, SynthExpect::Ret(RunResult::Int(5))),
            case("index 1 reads 11", 1, SynthExpect::Ret(RunResult::Int(11))),
            case("index 2 reads 2", 2, SynthExpect::Ret(RunResult::Int(2))),
            case(
                "index 3 is out of bounds",
                3,
                SynthExpect::DeclaredDelta {
                    clean: SynthOutcome::TypeError(IrFaultName::BadField),
                    e2_code: "undefined_behavior",
                    why: "MEASURED 2026-08-25 at trust-ir a4e81b6: Clean's ir_ef_at fails \
                          closed with `type_error bad_field` (ir_w2a_ee_oob) where the \
                          interpreter reports the same read as undefined_behavior ('element \
                          3 is out of bounds', interpret.rs:4507-4516). A fault-CLASS \
                          divergence between the executors; mapping either class onto the \
                          other would falsify the outcome vocabulary.",
                },
            ),
        ],
    }
}

/// `unop` — `not` then `ctpop` CHAINED at width 8, so one body measures both
/// integer unary operators with the second consuming the first's output:
/// the answer is `8 - popcount(x)` for every u8 input.
fn unop_probe() -> SynthChain {
    let case = |label, x: u64| SynthInput {
        label,
        clean_tail: format!("(ir_vl1 {}) ir_mem0 ir_d0", wide_int(x)),
        trust_args: vec![iv_u8(x)],
        expect: SynthExpect::Ret(RunResult::Int(
            8 - u64::from(u8::try_from(x).expect("u8 domain").count_ones()),
        )),
    };
    SynthChain {
        name: "synth_unop",
        fixtures: &[("synth/synth_unop.trust-ir.txt", "@synth::unop_probe")],
        func_ids: &[0],
        type_decls: "",
        sigs: vec![(914, vec![Ty::U8], vec![Ty::U8])],
        clean_module: "ir_w2a_uo_module",
        clean_fid: "ir_d0",
        clean_defs: clean_verify::spec::ir_w2a_uo_module_defs(),
        encoding: WideEncoding::Scalar,
        enum_model: EnumModel::Synthetic,
        expected_cost_offset: 0,
        total_domain: false,
        shipped_absent: SYNTHETIC_NO_E3,
        inputs: vec![
            case("zero: ctpop(not 0) = 8", 0),
            case("saturated: ctpop(not 255) = 0", 255),
            case("alternating 0b10101010 -> 4", 170),
            case("one bit set -> 7", 1),
            case("high single bit 0b1000 -> 7", 8),
            case("low nibble 0b1111 -> 4", 15),
        ],
    }
}

fn iv_u8(n: u64) -> InterpretValue {
    InterpretValue::int(Ty::U8, i128::from(n)).expect("u8 is an integer type")
}

fn struct_ty(id: u32) -> Ty {
    Ty::Struct(StructId::new(id))
}

/// A by-value three-u32-field struct — the `extractelement` container.
fn iv_struct3(struct_id: u32, fields: &[u64; 3]) -> InterpretValue {
    InterpretValue {
        ty: Ty::Struct(StructId::new(struct_id)),
        kind: InterpretValueKind::Aggregate(
            fields
                .iter()
                .map(|f| iv_u32(u32::try_from(*f).expect("u32 domain")))
                .collect(),
        ),
    }
}

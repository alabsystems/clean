// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The **W2b synthetic chains** — the memory tranche of the GAP-2 battery
//! (`docs/analysis/evalir-completion-plan-2026-08-24.md` §5 W2b): `alloca`,
//! `ptrdata`, `ptrmetadata`, `ptrfromparts`.
//!
//! Same lane contract as `synth_chains.rs` (read its module doc first, and
//! `eval_ir_w2b_synth.rs`'s for why every module here is a COMPOSITION —
//! a memory constructor is only observable through the heap, so alloca/store/
//! load and the pointer projections appear together, with `store`/`load`/
//! `condbr` already carrying W1 agreement rows). Every chain is
//! [`EnumModel::Synthetic`], E3 absent by construction, and reuses the W2a
//! table structs verbatim.
//!
//! ## The one non-`Ret` row, and the fault-site split it sits on (measured
//! 2026-08-25 at trust-ir rev `a4e81b6`; E1 half authored, pends the big box)
//!
//! `alloca`'s uninitialized-read row is [`SynthExpect::UbAgree`] at
//! [`IrFaultName::Uninit`]: both executors call the program UB on that input,
//! but at DIFFERENT trace steps — Clean's `ir_load_value` faults `ub uninit`
//! at the load of the fresh cell, while the interpreter's plain load yields
//! inert `PartialBytes` poison and faults `undefined_behavior` only when the
//! value is INSPECTED, here at the `ret` signature check (`reject_partial`,
//! `interpret.rs:5402-5403`). The row compares at outcome CLASS, which is
//! honest for THIS module because its only path from the poisoned load ends
//! in an inspection; a module that merely copied the loaded value onward
//! would genuinely diverge (Clean UB, interpreter defined) and is recorded as
//! fragment residue in `data/evalir_w2b.PENDING.md`, not smoothed here.
//!
//! Clean's fat pointer carries `md : Nat`, so the metadata lane is measured
//! on the slice/str shape (a length both sides return as an integer); the
//! vtable/fnptr rebuild arms are kernel-witnessed in the stage
//! (`ir_w2b_pp_vtable`/`ir_w2b_pp_fnptr`) with their E2-comparable observable
//! being the DATA lane, which the `ptrfromparts` fat path measures.
//!
//! Cost offsets are DECLARED 0 on every value-returning row; the fault row is
//! unpriced by shape. The E2 half of the declaration is measured here by
//! `crystal_a3_w2b_e2_instrument_smoke`; the E1 half (least fuels and their
//! tightness) pends the big box (`data/evalir_w2b.PENDING.md`).

use clean_verify::ir_semdiff::synth::IrFaultName;
use clean_verify::ir_semdiff::wide::{wide_args, wide_bool, wide_int, wide_unit, WideEncoding};
use clean_verify::ir_semdiff::{EnumModel, RunResult};
use trust_ir::interpret::InterpretValue;
use trust_ir::ty::Ty;

use super::synth_chains::{SynthChain, SynthExpect, SynthInput, SYNTHETIC_NO_E3};
use super::wide_exec::{iv_u32, iv_u64, iv_unit};

/// The W2b chains, in measurement order.
pub fn w2b_chains() -> Vec<SynthChain> {
    vec![
        alloca_probe(),
        ptrdata_probe(),
        ptrmetadata_probe(),
        ptrfromparts_probe(),
    ]
}

/// `alloca` — one fresh u32 cell; a bool selector routes between the
/// initialized round-trip (store then load, the identity observation) and the
/// uninitialized read (the fresh-cell UB edge). Constructors under measure:
/// `alloca` (+ already-measured `store`/`load`/`condbr`/`ret`).
fn alloca_probe() -> SynthChain {
    let stored = |label, x: u64| SynthInput {
        label,
        clean_tail: format!(
            "{} ir_mem0 ir_d0",
            wide_args(&[wide_int(x), wide_bool(true)])
        ),
        trust_args: vec![
            iv_u32(u32::try_from(x).expect("u32 domain")),
            InterpretValue::bool(true),
        ],
        expect: SynthExpect::Ret(RunResult::Int(x)),
    };
    SynthChain {
        name: "synth_alloca",
        fixtures: &[("synth/synth_alloca.trust-ir.txt", "@synth::alloca_probe")],
        func_ids: &[0],
        type_decls: "",
        sigs: vec![(915, vec![Ty::U32, Ty::Bool], vec![Ty::U32])],
        clean_module: "ir_w2b_al_module",
        clean_fid: "ir_d0",
        clean_defs: clean_verify::spec::ir_w2b_al_module_defs(),
        encoding: WideEncoding::Scalar,
        enum_model: EnumModel::Synthetic,
        expected_cost_offset: 0,
        total_domain: false,
        shipped_absent: SYNTHETIC_NO_E3,
        inputs: vec![
            stored("store 7 then load", 7),
            stored("store 0 then load", 0),
            stored("store u32::MAX then load", 4_294_967_295),
            SynthInput {
                label: "load the fresh cell uninitialized",
                clean_tail: format!(
                    "{} ir_mem0 ir_d0",
                    wide_args(&[wide_int(5), wide_bool(false)])
                ),
                trust_args: vec![iv_u32(5), InterpretValue::bool(false)],
                // Both executors: UB. Clean pins `ub uninit` AT THE LOAD;
                // E2's poison faults undefined_behavior at the ret's
                // inspection (module doc). Class agreement, site split noted.
                expect: SynthExpect::UbAgree(IrFaultName::Uninit),
            },
        ],
    }
}

/// `ptrdata` — the thin data lane, observed by dereferencing the PROJECTED
/// pointer inside a store/load round-trip: `load (ptr_data p)` returns what
/// was stored through `p`, so identity is measured, not asserted.
fn ptrdata_probe() -> SynthChain {
    let case = |label, x: u64| SynthInput {
        label,
        clean_tail: format!("(ir_vl1 {}) ir_mem0 ir_d0", wide_int(x)),
        trust_args: vec![iv_u32(u32::try_from(x).expect("u32 domain"))],
        expect: SynthExpect::Ret(RunResult::Int(x)),
    };
    SynthChain {
        name: "synth_ptrdata",
        fixtures: &[("synth/synth_ptrdata.trust-ir.txt", "@synth::ptrdata_probe")],
        func_ids: &[0],
        type_decls: "",
        sigs: vec![(916, vec![Ty::U32], vec![Ty::U32])],
        clean_module: "ir_w2b_pd_module",
        clean_fid: "ir_d0",
        clean_defs: clean_verify::spec::ir_w2b_pd_module_defs(),
        encoding: WideEncoding::Scalar,
        enum_model: EnumModel::Synthetic,
        expected_cost_offset: 0,
        total_domain: false,
        shipped_absent: SYNTHETIC_NO_E3,
        inputs: vec![
            case("round-trip 7 through the projected lane", 7),
            case("round-trip 0", 0),
            case("round-trip u32::MAX", 4_294_967_295),
        ],
    }
}

/// `ptrmetadata` — rebuild a `fatptr<str>` from the fresh cell's address and
/// a u64 length, project the metadata lane back, return it: the length
/// round-trip both executors compare as an integer. (The thin arm returns
/// unit and is kernel-witnessed in the stage, `ir_w2b_pm_thin` — a
/// ret-of-unit row has no shared integer vocabulary.)
fn ptrmetadata_probe() -> SynthChain {
    let case = |label, x: u64, len: u64| SynthInput {
        label,
        clean_tail: format!("{} ir_mem0 ir_d0", wide_args(&[wide_int(x), wide_int(len)])),
        trust_args: vec![iv_u32(u32::try_from(x).expect("u32 domain")), iv_u64(len)],
        expect: SynthExpect::Ret(RunResult::Int(len)),
    };
    SynthChain {
        name: "synth_ptrmetadata",
        fixtures: &[(
            "synth/synth_ptrmetadata.trust-ir.txt",
            "@synth::ptrmetadata_probe",
        )],
        func_ids: &[0],
        type_decls: "",
        sigs: vec![(917, vec![Ty::U32, Ty::U64], vec![Ty::U64])],
        clean_module: "ir_w2b_pm_module",
        clean_fid: "ir_d0",
        clean_defs: clean_verify::spec::ir_w2b_pm_module_defs(),
        encoding: WideEncoding::Scalar,
        enum_model: EnumModel::Synthetic,
        expected_cost_offset: 0,
        total_domain: false,
        shipped_absent: SYNTHETIC_NO_E3,
        inputs: vec![
            case("length 0 round-trips", 5, 0),
            case("length 1 round-trips", 5, 1),
            case("length 2^32 exercises the full u64 lane", 9, 4_294_967_296),
        ],
    }
}

/// `ptrfromparts` — both rebuild arms, each observed through a dereference:
/// thin (unit metadata) loaded directly, fat (`fatptr<str>`, u64 length)
/// loaded through its `ptr_data`-projected data lane. With the `ptrmetadata`
/// chain this pins that a rebuilt fat pointer carries BOTH lanes intact; the
/// vtable/fnptr metadata arms are kernel-witnessed in the stage
/// (`ir_w2b_pp_vtable`/`ir_w2b_pp_fnptr` — module doc for why their metadata
/// lane has no E2-comparable integer observable).
fn ptrfromparts_probe() -> SynthChain {
    let case = |label, x: u64, len: u64, thin: bool| SynthInput {
        label,
        clean_tail: format!(
            "{} ir_mem0 ir_d0",
            wide_args(&[wide_int(x), wide_int(len), wide_unit(), wide_bool(thin)])
        ),
        trust_args: vec![
            iv_u32(u32::try_from(x).expect("u32 domain")),
            iv_u64(len),
            iv_unit(),
            InterpretValue::bool(thin),
        ],
        expect: SynthExpect::Ret(RunResult::Int(x)),
    };
    SynthChain {
        name: "synth_ptrfromparts",
        fixtures: &[(
            "synth/synth_ptrfromparts.trust-ir.txt",
            "@synth::ptrfromparts_probe",
        )],
        func_ids: &[0],
        type_decls: "",
        sigs: vec![(
            918,
            vec![Ty::U32, Ty::U64, Ty::Unit, Ty::Bool],
            vec![Ty::U32],
        )],
        clean_module: "ir_w2b_pp_module",
        clean_fid: "ir_d0",
        clean_defs: clean_verify::spec::ir_w2b_pp_module_defs(),
        encoding: WideEncoding::Scalar,
        enum_model: EnumModel::Synthetic,
        expected_cost_offset: 0,
        total_domain: false,
        shipped_absent: SYNTHETIC_NO_E3,
        inputs: vec![
            case("thin rebuild derefs to 7", 7, 0, true),
            case("thin rebuild transports u32::MAX", 4_294_967_295, 1, true),
            case("fat rebuild's data lane derefs to 7", 7, 0, false),
            case(
                "fat rebuild's data lane transports u32::MAX",
                4_294_967_295,
                3,
                false,
            ),
        ],
    }
}

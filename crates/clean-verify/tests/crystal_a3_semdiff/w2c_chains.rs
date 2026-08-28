// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The **W2c synthetic chains** — the call+module tranche of the GAP-2 battery
//! (`docs/analysis/evalir-completion-plan-2026-08-24.md` §5 W2c):
//! `callindirect`, `globaladdr`. The FINAL synthetic tranche: with these two,
//! every `IRInst` constructor except `overflow` (plan W3) and `fcmp` (plan W4)
//! has battery rows.
//!
//! Same lane contract as `synth_chains.rs` (read its module doc first, and
//! `eval_ir_w2c_synth.rs`'s for the module designs). Every chain is
//! [`EnumModel::Synthetic`], E3 absent by construction, and reuses the W2a
//! table structs verbatim.
//!
//! ## Why the `callindirect` chain carries TWO companion callees
//!
//! The constructor's semantics is that dispatch goes through the function-
//! pointer VALUE. One callee cannot show that (an identity callee's answer is
//! indistinguishable from "returned the argument"); two can: the same caller
//! body, the same payload, a different fnptr argument, a different answer —
//! measured on both executors per row.
//!
//! ## The one DECLARED executor delta (measured 2026-08-25, trust-ir rev
//! `a4e81b6`, this box — the E2 half; the E1 half is authored and pends the
//! big-box run)
//!
//! **The null function pointer diverges by CODE.** Clean's `ir_callind_exec`
//! pins `ub null_deref` (`ir_w2c_ci_on_null`); the reference interpreter
//! reports its own `invalid_function_pointer` code — not
//! `undefined_behavior`, so it is outside the two-class outcome map
//! (`interpret.rs:1415-1421`). A [`SynthExpect::DeclaredDelta`]: asserted to
//! reproduce exactly, printed, never counted as agreement. (The dangling-fnptr
//! and non-fnptr-callee edges sit on the same split at other sites and are
//! kernel-witnessed in the stage — `ir_w2c_ci_no_func`,
//! `ir_w2c_ci_not_fnptr` — rather than battery-measured.)
//!
//! `globaladdr`'s rows are all value-returning: the initializer read, and the
//! store-through-one-address / load-through-the-second aliasing observation.
//! The missing-global edge is kernel-witnessed value-level
//! (`ir_w2c_ga_no_global`; E2's out-of-range code is `missing_value`, also
//! outside the class map).
//!
//! Cost offsets are DECLARED 0 on every value-returning row; the fault row is
//! unpriced by shape. The E2 half of the declaration is measured here by
//! `crystal_a3_w2c_e2_instrument_smoke`; the E1 half (least fuels and their
//! tightness) pends the big box (`data/evalir_w2c.PENDING.md`).

use clean_verify::ir_semdiff::synth::{IrFaultName, SynthOutcome};
use clean_verify::ir_semdiff::wide::{
    wide_args, wide_bool, wide_fnptr, wide_int, wide_nullptr, WideEncoding,
};
use clean_verify::ir_semdiff::{EnumModel, RunResult};
use trust_ir::interpret::{InterpretValue, InterpretValueKind};
use trust_ir::ty::Ty;
use trust_ir::value::{FuncId, FuncTyId};

use super::synth_chains::{SynthChain, SynthExpect, SynthInput, SYNTHETIC_NO_E3};
use super::wide_exec::iv_u32;

/// The functy index both companion callees declare and the caller's
/// `call_indirect` names — the type every fnptr argument row carries.
const CALLEE_SIG: u32 = 920;

/// The W2c chains, in measurement order.
pub fn w2c_chains() -> Vec<SynthChain> {
    vec![callindirect_probe(), globaladdr_probe()]
}

/// A function-pointer argument value: `functy.920`-typed, resolving to the
/// composed module's function `id` (1 = the const11 callee, 2 = the identity
/// callee — `build_wide_module` reassigns the parsed functions to exactly
/// those ids).
fn iv_fnptr(id: u32) -> InterpretValue {
    InterpretValue {
        ty: Ty::Func(FuncTyId::new(CALLEE_SIG)),
        kind: InterpretValueKind::FnDef(FuncId::new(id)),
    }
}

/// The null function pointer at the same declared type — the declared-delta
/// row's argument.
fn iv_null_fnptr() -> InterpretValue {
    InterpretValue {
        ty: Ty::Func(FuncTyId::new(CALLEE_SIG)),
        kind: InterpretValueKind::NullPtr,
    }
}

/// `callindirect` — one caller, two companion callees, dispatch through the
/// fnptr ARGUMENT: `%2 = call_indirect %0(functy.920)(%1)`. Constructors
/// under measure: `callindirect` (+ already-measured `const_`/`ret` in the
/// callees).
fn callindirect_probe() -> SynthChain {
    let case = |label, callee: u32, x: u64, expect: u64| SynthInput {
        label,
        clean_tail: format!(
            "{} ir_mem0 ir_d0",
            wide_args(&[wide_fnptr(u64::from(callee)), wide_int(x)])
        ),
        trust_args: vec![
            iv_fnptr(callee),
            iv_u32(u32::try_from(x).expect("u32 domain")),
        ],
        expect: SynthExpect::Ret(RunResult::Int(expect)),
    };
    SynthChain {
        name: "synth_callindirect",
        fixtures: &[
            (
                "synth/synth_callindirect.trust-ir.txt",
                "@synth::callindirect_probe",
            ),
            (
                "synth/synth_callindirect_c11.trust-ir.txt",
                "@synth::ci_const11",
            ),
            (
                "synth/synth_callindirect_id.trust-ir.txt",
                "@synth::ci_ident",
            ),
        ],
        func_ids: &[0, 1, 2],
        type_decls: "",
        sigs: vec![
            (
                919,
                vec![Ty::Func(FuncTyId::new(CALLEE_SIG)), Ty::U32],
                vec![Ty::U32],
            ),
            (CALLEE_SIG, vec![Ty::U32], vec![Ty::U32]),
        ],
        clean_module: "ir_w2c_ci_module",
        clean_fid: "ir_d0",
        clean_defs: clean_verify::spec::ir_w2c_ci_module_defs(),
        encoding: WideEncoding::Scalar,
        enum_model: EnumModel::Synthetic,
        expected_cost_offset: 0,
        total_domain: false,
        shipped_absent: SYNTHETIC_NO_E3,
        inputs: vec![
            case("const11 callee ignores payload 7", 1, 7, 11),
            case("const11 callee ignores payload 0", 1, 0, 11),
            case("ident callee transports 7", 2, 7, 7),
            case(
                "ident callee transports u32::MAX",
                2,
                4_294_967_295,
                4_294_967_295,
            ),
            SynthInput {
                label: "null function pointer",
                clean_tail: format!(
                    "{} ir_mem0 ir_d0",
                    wide_args(&[wide_nullptr(), wide_int(7)])
                ),
                trust_args: vec![iv_null_fnptr(), iv_u32(7)],
                expect: SynthExpect::DeclaredDelta {
                    clean: SynthOutcome::Ub(IrFaultName::NullDeref),
                    e2_code: "invalid_function_pointer",
                    why: "MEASURED 2026-08-25 at trust-ir a4e81b6: Clean's ir_callind_exec \
                          pins calling through the null function pointer as `ub null_deref` \
                          (ir_w2c_ci_on_null) where the reference interpreter reports its \
                          own `invalid_function_pointer` code ('CallIndirect: null function \
                          pointer', interpret.rs:1415-1421) — not undefined_behavior, so it \
                          is outside the two-class outcome map. A fault-CODE divergence \
                          between the executors; mapping the code onto the UB class would \
                          falsify the outcome vocabulary.",
                },
            },
        ],
    }
}

/// `globaladdr` — the module's one global (`u32 = 7`, declared in
/// `type_decls`: a global is a module-level line, not a body line), read
/// through its address and written through one `global_addr` result then read
/// back through a SECOND — the repeated-address-of-aliases property measured,
/// not asserted. Constructors under measure: `globaladdr` (+ already-measured
/// `condbr`/`store`/`load`/`ret`).
fn globaladdr_probe() -> SynthChain {
    let case = |label, x: u64, write: bool, expect: u64| SynthInput {
        label,
        clean_tail: format!(
            "{} ir_mem0 ir_d0",
            wide_args(&[wide_int(x), wide_bool(write)])
        ),
        trust_args: vec![
            iv_u32(u32::try_from(x).expect("u32 domain")),
            InterpretValue::bool(write),
        ],
        expect: SynthExpect::Ret(RunResult::Int(expect)),
    };
    SynthChain {
        name: "synth_globaladdr",
        fixtures: &[(
            "synth/synth_globaladdr.trust-ir.txt",
            "@synth::globaladdr_probe",
        )],
        func_ids: &[0],
        type_decls: "global mut @SYNTH_G u32 = 7",
        sigs: vec![(921, vec![Ty::U32, Ty::Bool], vec![Ty::U32])],
        clean_module: "ir_w2c_ga_module",
        clean_fid: "ir_d0",
        clean_defs: clean_verify::spec::ir_w2c_ga_module_defs(),
        encoding: WideEncoding::Scalar,
        enum_model: EnumModel::Synthetic,
        expected_cost_offset: 0,
        total_domain: false,
        shipped_absent: SYNTHETIC_NO_E3,
        inputs: vec![
            case("false reads the initializer 7", 42, false, 7),
            case("store 42, load through the second address", 42, true, 42),
            case("store 0, load through the second address", 0, true, 0),
            case(
                "store u32::MAX, load through the second address",
                4_294_967_295,
                true,
                4_294_967_295,
            ),
        ],
    }
}

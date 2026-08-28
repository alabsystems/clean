// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The **W1 wide chains** — the fixture-widening lane of the GAP-2 battery
//! (`docs/analysis/evalir-completion-plan-2026-08-24.md` §5 W1).
//!
//! Every chain here runs a COMMITTED emitted body (`tests/fixtures/*.trust-ir.txt`)
//! whose minted Clean module is already registered by a chain stage; the
//! `clean_defs` re-export those stage lines rather than re-typing them, so the
//! differential cannot drift from the module the specification carries. What
//! W1 adds is MEASUREMENT — three-executor agreement rows over the nine
//! constructors those bodies exercise (`icmp`, `binop`, `cast`, `condbr`,
//! `call`, `store`, `gep`, `insertfield`, `assert`) — never semantics.
//!
//! **One planned subject is deliberately absent: `meta_tag_shl`.** Its return
//! value is `1u64 << 63`, and the registered stage leaves that term
//! deliberately UNREDUCED (`eval_ir_meta_tag.rs`, `env_push_low_local_meta_tag`
//! rationale: normalizing costs 2^63 `Nat.rec` unfoldings). A battery row
//! would therefore either hand the kernel a digit-literal RHS it cannot afford
//! to compare — hanging the gate, not failing it — or record a term-level
//! `Eq.refl` as if it were a digit comparison the kernel never made. The
//! honest classification is the one the plan already names: that row waits on
//! W0's large-literal obligation path (pow2-ladder RHS terms). The
//! constructors it would have contributed are all covered here by other
//! subjects (`assert`/`icmp` by `loose_bvar_range`, `binop` by
//! `and`/`or`/`lshr`, `cast` by `trunc`/`zext`).
//!
//! Cost offsets are DECLARED 0 on every chain, and the E2 half of that
//! declaration is MEASURED (2026-08-24, `crystal_a3_wide_e2_instrument_smoke`
//! on the authoring box): every row's interpreter step count equals the
//! executed-instruction count of its path — including the `call` chain, where
//! `has_loose_bvars` reports 13 = 4 caller + 9 callee instructions, exactly
//! the fuel the committed kernel witness `ir_hlb_w_zero` runs at. What remains
//! unmeasured until the first big-box gate run is the E1 half (the per-input
//! least-fuel thresholds and their tightness); a mismatch there is a RED to
//! report, not a knob to turn.

use clean_verify::ir_semdiff::wide::{wide_agg1, wide_args, wide_int, WideEncoding};
use clean_verify::ir_semdiff::{EnumModel, RunResult};
use trust_ir::interpret::InterpretValue;
use trust_ir::ty::Ty;

use super::wide_exec::{iv_struct1, iv_u32, iv_u64, iv_unit, SigSpec};

/// How E2 receives one input.
pub enum WideTrustInput {
    /// Constructed values handed straight to `execute_function` — the subject's
    /// own step count is the report, nothing subtracted.
    Args(Vec<InterpretValue>),
    /// A per-input TEXT harness (pointer-receiving subjects only): the harness
    /// function is appended to the composed module and executed with no
    /// arguments; `overhead` is its own straight-line instruction count,
    /// counted from the text below, never tuned.
    Harness { text: String, overhead: u64 },
}

/// One measured input of a wide chain.
pub struct WideInput {
    /// Human-readable label, printed with the row.
    pub label: &'static str,
    /// The `<args> <heap> <next-addr>` tail of the Clean `ir_eval` application.
    pub clean_tail: String,
    /// How E2 receives the input.
    pub trust: WideTrustInput,
    /// E3 — the shipped function's answer, precomputed by CALLING it, when it
    /// is reachable from this crate.
    pub shipped: Option<RunResult>,
}

/// One wide chain.
pub struct WideChain {
    /// Short name, used in output and generated def names.
    pub name: &'static str,
    /// Committed fixtures `(file, printed name)`, subject first.
    pub fixtures: &'static [(&'static str, &'static str)],
    /// The function id each fixture's body must carry so committed call
    /// operands resolve (`has_loose_bvars` calls `@func.3657`).
    pub func_ids: &'static [u32],
    /// struct/enum declarations the composed module needs (the crate-level
    /// dump carries no type tables).
    pub type_decls: &'static str,
    /// Reconstituted signatures, by declared functy index.
    pub sigs: Vec<SigSpec>,
    /// The registered Clean module constant.
    pub clean_module: &'static str,
    /// The function id term inside that module (`ir_d1` = the callee row of a
    /// two-function module).
    pub clean_fid: &'static str,
    /// The registered stage lines that build the module — re-exported, not
    /// re-typed.
    pub clean_defs: &'static [&'static str],
    /// How the returned value is wrapped on the Clean side.
    pub encoding: WideEncoding,
    /// How faithfully E2's type declarations model the real Rust types —
    /// `TagSurrogate` for `strict_monads`, whose struct.441 declaration is a
    /// self-consistent surrogate layout, `Exact` everywhere else.
    pub enum_model: EnumModel,
    /// The declared clean-minus-trust cost offset (see the module doc).
    pub expected_cost_offset: i64,
    /// Is the input set the WHOLE domain? Never rounded up: every chain here
    /// samples a `u32`/`u64`/byte-pair space except none — so every row below
    /// says `false` and prints as a SAMPLE.
    pub total_domain: bool,
    /// When `Some`, E2 is a bounded-interpreter lane that may lawfully refuse
    /// this body (recorded reason); a refusal is printed and the affected rows
    /// stay `Insufficient` — never folded into agreement, never a panic.
    pub e2_may_refuse: Option<&'static str>,
    /// Why E3 is absent, when it is.
    pub shipped_absent: Option<&'static str>,
    /// The inputs.
    pub inputs: Vec<WideInput>,
}

const PRIVATE_FN: &str = "the shipped fn is not `pub` outside clean-kernel and is not reachable \
     from this crate. Recorded as an absent leg rather than re-implemented: a \
     re-implementation would be another transcription agreeing with itself, \
     which is the failure mode this gate exists to detect.";

fn u32_args_tail(vals: &[u64]) -> String {
    let scalars: Vec<String> = vals.iter().map(|v| wide_int(*v)).collect();
    format!("{} ir_mem0 ir_d0", wide_args(&scalars))
}

fn agg1_args_tail(vals: &[u64]) -> String {
    let scalars: Vec<String> = vals.iter().map(|v| wide_agg1(*v)).collect();
    format!("{} ir_mem0 ir_d0", wide_args(&scalars))
}

/// The wide chains, in measurement order.
pub fn wide_chains() -> Vec<WideChain> {
    vec![
        bvar_in_range(),
        is_valid_char(),
        flat_flags_contains(),
        flat_flags_with(),
        node_id_index(),
        get_char_val_trunc(),
        has_loose_bvars(),
        loose_bvar_range(),
        strict_monads(),
        simp_priority_value(),
    ]
}

/// `expr::bvar_in_range` — `icmp` (eq/uge/ult) and BOTH `condbr`s, the
/// short-circuit CFG. Constructors: `icmp`, `condbr` (+ `const_`/`br`/`ret`).
fn bvar_in_range() -> WideChain {
    let case = |label, i: u64, s: u64, e: u64| WideInput {
        label,
        clean_tail: u32_args_tail(&[i, s, e]),
        trust: WideTrustInput::Args(vec![
            iv_u32(u32::try_from(i).expect("u32 domain")),
            iv_u32(u32::try_from(s).expect("u32 domain")),
            iv_u32(u32::try_from(e).expect("u32 domain")),
        ]),
        shipped: None,
    };
    WideChain {
        name: "bvar_in_range",
        fixtures: &[("bvar_in_range.trust-ir.txt", "@expr::bvar_in_range")],
        func_ids: &[0],
        type_decls: "",
        sigs: vec![(467, vec![Ty::U32, Ty::U32, Ty::U32], vec![Ty::Bool])],
        clean_module: "ir_br_module",
        clean_fid: "ir_d0",
        clean_defs: clean_verify::spec::ir_br_module_defs(),
        encoding: WideEncoding::Scalar,
        enum_model: EnumModel::Exact,
        expected_cost_offset: 0,
        total_domain: false,
        e2_may_refuse: None,
        shipped_absent: Some(PRIVATE_FN),
        inputs: vec![
            case("in_range 3 in [1,5)", 3, 1, 5),
            case("above_end 9 in [1,5)", 9, 1, 5),
            case("below_start 0 in [1,5)", 0, 1, 5),
            case("at_end 5 in [1,5)", 5, 1, 5),
            case("at_start 1 in [1,5)", 1, 1, 5),
            case("sentinel unbounded 3 >= 1", 3, 1, 4_294_967_295),
            case("sentinel unbounded 0 < 1", 0, 1, 4_294_967_295),
        ],
    }
}

/// `env::native_reducers_char::is_valid_char` — the OTHER `condbr` body, with
/// `icmp ult` at u64 against the surrogate-range constants.
fn is_valid_char() -> WideChain {
    let case = |label, n: u64| WideInput {
        label,
        clean_tail: format!("(ir_vl1 {}) ir_mem0 ir_d0", wide_int(n)),
        trust: WideTrustInput::Args(vec![iv_u64(n)]),
        shipped: None,
    };
    WideChain {
        name: "is_valid_char",
        fixtures: &[(
            "is_valid_char.trust-ir.txt",
            "@env::native_reducers_char::is_valid_char",
        )],
        func_ids: &[0],
        type_decls: "",
        sigs: vec![(377, vec![Ty::U64], vec![Ty::Bool])],
        clean_module: "ir_vc_module",
        clean_fid: "ir_d0",
        clean_defs: clean_verify::spec::ir_vc_module_defs(),
        encoding: WideEncoding::Scalar,
        enum_model: EnumModel::Exact,
        expected_cost_offset: 0,
        total_domain: false,
        e2_may_refuse: None,
        shipped_absent: Some(PRIVATE_FN),
        inputs: vec![
            case("zero", 0),
            case("ascii a", 97),
            case("below surrogates", 55_295),
            case("first surrogate", 55_296),
            case("last surrogate", 57_343),
            case("after surrogates", 57_344),
            case("max scalar", 1_114_111),
            case("past max scalar", 1_114_112),
            case("u32::MAX", 4_294_967_295),
        ],
    }
}

/// `FlatFlags::contains` — `binop` (`and` at u8) + `icmp eq`, over by-value
/// one-field structs.
fn flat_flags_contains() -> WideChain {
    let case = |label, x: u64, y: u64| WideInput {
        label,
        clean_tail: agg1_args_tail(&[x, y]),
        trust: WideTrustInput::Args(vec![iv_struct1(1017, iv_u8(x)), iv_struct1(1017, iv_u8(y))]),
        shipped: None,
    };
    WideChain {
        name: "flat_flags_contains",
        fixtures: &[(
            "flat_flags_contains.trust-ir.txt",
            "@flat::types::FlatFlags::contains",
        )],
        func_ids: &[0],
        type_decls: "struct @FlatFlags { u8 } id=1017",
        sigs: vec![(488, vec![struct_ty(1017), struct_ty(1017)], vec![Ty::Bool])],
        clean_module: "ir_fc_module",
        clean_fid: "ir_d0",
        clean_defs: clean_verify::spec::ir_fc_module_defs(),
        encoding: WideEncoding::Scalar,
        enum_model: EnumModel::Exact,
        expected_cost_offset: 0,
        total_domain: false,
        e2_may_refuse: None,
        shipped_absent: Some(PRIVATE_FN),
        inputs: vec![
            case("self contains self", 1, 1),
            case("disjoint", 1, 2),
            case("subset", 10, 2),
            case("both empty", 0, 0),
            case("anything contains empty", 10, 0),
            case("saturated", 255, 255),
            case("overlap only", 2, 3),
            case("proper subset", 15, 8),
        ],
    }
}

/// `FlatFlags::with` — `binop` (`or` at u8) + **`insertfield`** into a
/// `const struct` — the first aggregate-CONSTRUCTING body in the battery.
fn flat_flags_with() -> WideChain {
    let case = |label, x: u64, y: u64| WideInput {
        label,
        clean_tail: agg1_args_tail(&[x, y]),
        trust: WideTrustInput::Args(vec![iv_struct1(1017, iv_u8(x)), iv_struct1(1017, iv_u8(y))]),
        shipped: None,
    };
    WideChain {
        name: "flat_flags_with",
        fixtures: &[(
            "flat_flags_with.trust-ir.txt",
            "@flat::types::FlatFlags::with",
        )],
        func_ids: &[0],
        type_decls: "struct @FlatFlags { u8 } id=1017",
        sigs: vec![(
            489,
            vec![struct_ty(1017), struct_ty(1017)],
            vec![struct_ty(1017)],
        )],
        clean_module: "ir_fw_module",
        clean_fid: "ir_d0",
        clean_defs: clean_verify::spec::ir_fw_module_defs(),
        encoding: WideEncoding::AggInt,
        enum_model: EnumModel::Exact,
        expected_cost_offset: 0,
        total_domain: false,
        e2_may_refuse: None,
        shipped_absent: Some(PRIVATE_FN),
        inputs: vec![
            case("disjoint 1|2", 1, 2),
            case("overlap 10|6", 10, 6),
            case("identity 10|0", 10, 0),
            case("saturation 10|255", 10, 255),
            case("swap 2|1", 2, 1),
            case("empty 0|0", 0, 0),
        ],
    }
}

/// `NodeId::index` — `cast` (`zext` u32 → usize) over a by-value struct.
fn node_id_index() -> WideChain {
    let case = |label, n: u64| WideInput {
        label,
        clean_tail: format!("(ir_vl1 {}) ir_mem0 ir_d0", wide_agg1(n)),
        trust: WideTrustInput::Args(vec![iv_struct1(
            323,
            iv_u32(u32::try_from(n).expect("u32 domain")),
        )]),
        shipped: None,
    };
    WideChain {
        name: "node_id_index",
        fixtures: &[(
            "node_id_index.trust-ir.txt",
            "@cert::builder::state::NodeId::index",
        )],
        func_ids: &[0],
        type_decls: "struct @NodeId { u32 } id=323",
        sigs: vec![(97, vec![struct_ty(323)], vec![Ty::Usize])],
        clean_module: "ir_ni_module",
        clean_fid: "ir_d0",
        clean_defs: clean_verify::spec::ir_ni_module_defs(),
        encoding: WideEncoding::Scalar,
        enum_model: EnumModel::Exact,
        expected_cost_offset: 0,
        total_domain: false,
        e2_may_refuse: None,
        shipped_absent: Some(
            "`NodeId::index` is pub(super) in clean-kernel/src/cert/builder/state.rs and \
             not reachable from this crate; recorded absent, never re-implemented.",
        ),
        inputs: vec![
            case("zero", 0),
            case("one", 1),
            case("seven", 7),
            case("sign bit", 2_147_483_648),
            case("u32::MAX", 4_294_967_295),
        ],
    }
}

/// `get_char_val::{closure#0}` — `cast` (`trunc` u64 → u32), with the unit
/// closure-environment parameter passed and dropped.
fn get_char_val_trunc() -> WideChain {
    let case = |label, n: u64| WideInput {
        label,
        // The closure-env parameter is junk the body never reads —
        // `ir_gc_correct` quantifies over ANY first value, so `undef_` is the
        // honest Clean encoding of "present but meaningless".
        clean_tail: format!(
            "{} ir_mem0 ir_d0",
            wide_args(&["IRScalar.undef_".to_owned(), wide_int(n)])
        ),
        trust: WideTrustInput::Args(vec![iv_unit(), iv_u64(n)]),
        shipped: None,
    };
    WideChain {
        name: "get_char_val_trunc",
        fixtures: &[(
            "get_char_val_trunc.trust-ir.txt",
            "@env::native_reducers_beq_shortcircuit::get_char_val::{closure#0}",
        )],
        func_ids: &[0],
        type_decls: "",
        sigs: vec![(370, vec![Ty::Unit, Ty::U64], vec![Ty::U32])],
        clean_module: "ir_gc_module",
        clean_fid: "ir_d0",
        clean_defs: clean_verify::spec::ir_gc_module_defs(),
        encoding: WideEncoding::Scalar,
        enum_model: EnumModel::Exact,
        expected_cost_offset: 0,
        total_domain: false,
        e2_may_refuse: None,
        shipped_absent: Some(
            "the subject is a private closure inside `get_char_val`; there is no \
             callable shipped symbol to reach from this crate.",
        ),
        inputs: vec![
            case("zero", 0),
            case("one", 1),
            case("u32::MAX survives", 4_294_967_295),
            case("2^32 truncates to 0", 4_294_967_296),
            case("u64::MAX truncates to u32::MAX", 18_446_744_073_709_551_615),
        ],
    }
}

/// `ExprMeta::has_loose_bvars` — **`call`**: the subject's answer routes
/// through its committed CALLEE fixture (`loose_bvar_range`), composed into
/// one two-function module exactly as the minted `ir_hlb_module` carries both.
fn has_loose_bvars() -> WideChain {
    let case = |label, meta: u64| WideInput {
        label,
        clean_tail: format!("(ir_vl1 {}) ir_mem0 ir_d0", wide_agg1(meta)),
        trust: WideTrustInput::Args(vec![iv_struct1(29, iv_u64(meta))]),
        shipped: None,
    };
    WideChain {
        name: "has_loose_bvars",
        fixtures: &[
            (
                "has_loose_bvars.trust-ir.txt",
                "@expr::meta::ExprMeta::has_loose_bvars",
            ),
            (
                "loose_bvar_range_callee.trust-ir.txt",
                "@expr::meta::ExprMeta::loose_bvar_range",
            ),
        ],
        // The caller's committed text calls `@func.3657`; the callee body must
        // carry that id for the call to resolve.
        func_ids: &[0, 3657],
        type_decls: "struct @ExprMeta { u64 } id=29",
        sigs: vec![
            (435, vec![struct_ty(29)], vec![Ty::Bool]),
            (433, vec![struct_ty(29)], vec![Ty::U32]),
        ],
        clean_module: "ir_hlb_module",
        clean_fid: "ir_d0",
        clean_defs: clean_verify::spec::ir_hlb_module_defs(),
        encoding: WideEncoding::Scalar,
        enum_model: EnumModel::Exact,
        expected_cost_offset: 0,
        total_domain: false,
        e2_may_refuse: None,
        shipped_absent: Some(
            "`ExprMeta` is pub(crate) in clean-kernel/src/expr/meta.rs — the methods are \
             pub but no value of the type can be built from this crate; recorded absent.",
        ),
        inputs: vec![
            case("no loose bvars", 0),
            case("below range boundary", 17_592_186_044_415),
            case("range boundary 1<<44", 17_592_186_044_416),
            case("mid pattern", 1_759_218_604_441_607),
            case("high pattern", 72_057_594_037_927_935),
        ],
    }
}

/// `ExprMeta::loose_bvar_range` — **`assert`** (shift-in-range proof
/// obligation) + `binop lshr` + `cast zext`/`trunc`, run as its own subject at
/// the minted module's SECOND function id.
fn loose_bvar_range() -> WideChain {
    let case = |label, meta: u64| WideInput {
        label,
        clean_tail: format!("(ir_vl1 {}) ir_mem0 ir_d0", wide_agg1(meta)),
        trust: WideTrustInput::Args(vec![iv_struct1(29, iv_u64(meta))]),
        shipped: None,
    };
    WideChain {
        name: "loose_bvar_range",
        fixtures: &[(
            "loose_bvar_range_callee.trust-ir.txt",
            "@expr::meta::ExprMeta::loose_bvar_range",
        )],
        func_ids: &[0],
        type_decls: "struct @ExprMeta { u64 } id=29",
        sigs: vec![(433, vec![struct_ty(29)], vec![Ty::U32])],
        // The SAME minted module as `has_loose_bvars` — the callee is its
        // function 1. The gate registers shared defs once; this chain reuses
        // them at `ir_d1`.
        clean_module: "ir_hlb_module",
        clean_fid: "ir_d1",
        clean_defs: clean_verify::spec::ir_hlb_module_defs(),
        encoding: WideEncoding::Scalar,
        enum_model: EnumModel::Exact,
        expected_cost_offset: 0,
        total_domain: false,
        e2_may_refuse: None,
        shipped_absent: Some(
            "`ExprMeta` is pub(crate) in clean-kernel/src/expr/meta.rs — the methods are \
             pub but no value of the type can be built from this crate; recorded absent.",
        ),
        inputs: vec![
            case("zero", 0),
            case("below boundary -> 0", 17_592_186_044_415),
            case("boundary -> 1", 17_592_186_044_416),
            case("mid -> 100", 1_759_218_604_441_607),
            case("high -> 4095", 72_057_594_037_927_935),
        ],
    }
}

/// `Environment::set_lean4_core_strict_monads` — **`store`** (the heap write)
/// + `insertfield` at field 81 + void return, against the SAME prepared heap
/// the stage's concrete witnesses pin (`ir_sm_heap0`).
fn strict_monads() -> WideChain {
    let case = |label, b: bool| {
        let lit = if b { "true" } else { "false" };
        WideInput {
            label,
            clean_tail: format!(
                "{} ir_sm_heap0 ir_d1",
                wide_args(&[
                    "(IRScalar.ptr_ ir_d0)".to_owned(),
                    format!("(IRScalar.bool_ Bool.{lit})"),
                ])
            ),
            trust: WideTrustInput::Harness {
                // alloca, const struct, store, const bool, call, ret — 6
                // instructions of harness overhead, counted from this text.
                text: format!(
                    "fn @g2_wide_harness(functy.900) {{\nbb0:\n    \
                     %0 = alloca struct.441\n    \
                     %1 = const struct.441 {{ {zeros} }}\n    \
                     store struct.441 %1, ptr %0\n    \
                     %2 = const bool {lit}\n    \
                     call @func.0(%0, %2)\n    \
                     ret\n}}\n",
                    zeros = sm_const_fields(),
                ),
                overhead: 6,
            },
            shipped: None,
        }
    };
    WideChain {
        name: "strict_monads",
        fixtures: &[(
            "strict_monads.trust-ir.txt",
            "@env::Environment::set_lean4_core_strict_monads",
        )],
        func_ids: &[0],
        // A SURROGATE layout: the real struct.441 is Environment's 82
        // heterogeneous fields; E2 needs only a self-consistent layout in
        // which field 81 round-trips, because the harness both writes and
        // (via the subject) rewrites through the same declaration. Sound for
        // THIS body for the same reason TagSurrogate is sound for
        // `level_kind_ord`: nothing observed depends on the elided detail.
        type_decls: SM_TYPE_DECL.as_str(),
        sigs: vec![
            (404, vec![Ty::Ptr, Ty::Bool], vec![]),
            (900, vec![], vec![]),
        ],
        clean_module: "ir_sm_module",
        clean_fid: "ir_d0",
        clean_defs: clean_verify::spec::ir_sm_semdiff_defs(),
        encoding: WideEncoding::Scalar,
        enum_model: EnumModel::TagSurrogate,
        expected_cost_offset: 0,
        total_domain: false,
        // MEASURED 2026-08-24 on this box: the interpreter ACCEPTS the
        // whole-struct load/store of the 82-field surrogate (unit @4 steps on
        // both inputs), so this lane declares no refusal allowance — a future
        // refusal at the pinned trust-ir rev would be a red worth seeing.
        // The VALUE this chain measures is the void return; the heap write
        // itself is pinned kernel-side by the stage's ir_sm_exact /
        // ir_sm_final_mem, not by this differential.
        e2_may_refuse: None,
        shipped_absent: Some(
            "observing the shipped setter needs a constructed `Environment`; building \
             one here would be a harness the size of the subject's whole crate state. \
             Recorded absent.",
        ),
        inputs: vec![case("set true", true), case("set false", false)],
    }
}

/// `SimpPriority::value` — **`gep`** (byte offset 4 into the enum cell) +
/// `load` through it, the payload-read pattern the SimpPriority chain already
/// executes kernel-side (`eval_ir_priority.rs`).
fn simp_priority_value() -> WideChain {
    let default_case = WideInput {
        label: "Default -> 1000",
        clean_tail: "(ir_vl1 (IRScalar.ptr_ ir_d0)) (ir_cell ir_d0 (ir_var ir_d0 ir_sp0) ir_mem0) \
                     ir_d1"
            .to_owned(),
        trust: WideTrustInput::Harness {
            // alloca, const tag, store, const off, gep, const zero, store,
            // call, ret — 9 instructions. The payload lane is INITIALIZED
            // (to 0) even though the Default arm never reads it — measured
            // 2026-08-24 on this exact harness: the subject's whole-enum
            // `load` reads all 8 bytes, and an uninitialized payload lane is
            // poison whose projection faults `undefined_behavior` in the
            // byte-addressed interpreter. Clean's cell-addressed model has no
            // uninitialized-byte concept (the design reason EvalIR exists),
            // so its default heap is just the tag cell; the harness writes
            // zeros to hand E2 the fully-initialized memory any real caller's
            // frame would hold.
            text: "fn @g2_wide_harness(functy.901) {\nbb0:\n    \
                   %0 = alloca enum.127\n    \
                   %1 = const u32 0\n    \
                   store u32 %1, ptr %0\n    \
                   %2 = const i64 4\n    \
                   %3 = gep inbounds i8, ptr %0, %2\n    \
                   %4 = const u32 0\n    \
                   store u32 %4, ptr %3\n    \
                   %5 = call @func.0(%0)\n    \
                   ret %5\n}\n"
                .to_owned(),
            overhead: 9,
        },
        shipped: Some(RunResult::Int(u64::from(
            clean_kernel::env::SimpPriority::Default.value(),
        ))),
    };
    let custom = |label, v: u32| WideInput {
        label,
        clean_tail: format!(
            "(ir_vl1 (IRScalar.ptr_ ir_d0)) (ir_cell ir_d0 (ir_var ir_d1 ir_sp0) \
             (ir_cell ir_d4 {} ir_mem0)) ir_d1",
            wide_int(u64::from(v))
        ),
        trust: WideTrustInput::Harness {
            // alloca, const tag, store, const off, gep, const payload, store,
            // call, ret — 9 instructions, mirroring the subject's own
            // byte-offset access pattern.
            text: format!(
                "fn @g2_wide_harness(functy.901) {{\nbb0:\n    \
                 %0 = alloca enum.127\n    \
                 %1 = const u32 1\n    \
                 store u32 %1, ptr %0\n    \
                 %2 = const i64 4\n    \
                 %3 = gep inbounds i8, ptr %0, %2\n    \
                 %4 = const u32 {v}\n    \
                 store u32 %4, ptr %3\n    \
                 %5 = call @func.0(%0)\n    \
                 ret %5\n}}\n"
            ),
            overhead: 9,
        },
        shipped: Some(RunResult::Int(u64::from(
            clean_kernel::env::SimpPriority::Custom(v).value(),
        ))),
    };
    WideChain {
        name: "simp_priority_value",
        fixtures: &[(
            "simp_priority_value.trust-ir.txt",
            "@env::types::SimpPriority::value",
        )],
        func_ids: &[0],
        type_decls: "enum @SimpPriority repr(u32) { Default, Custom(u32) } id=127",
        sigs: vec![
            (147, vec![Ty::Ptr], vec![Ty::U32]),
            (901, vec![], vec![Ty::U32]),
        ],
        clean_module: "ir_pv_module",
        clean_fid: "ir_d0",
        clean_defs: clean_verify::spec::ir_pv_module_defs(),
        encoding: WideEncoding::Scalar,
        enum_model: EnumModel::Exact,
        expected_cost_offset: 0,
        total_domain: false,
        // MEASURED 2026-08-24 on this box: whole-enum load and byte-gep
        // payload access both execute (int @8 steps on every Custom row;
        // Default answers once its payload lane is initialized — see the
        // harness note), so this lane declares no refusal allowance. E3 (the
        // shipped pub `SimpPriority::value`) makes these the battery's only
        // wide rows with all three executors.
        e2_may_refuse: None,
        shipped_absent: None,
        inputs: vec![
            default_case,
            custom("Custom(7)", 7),
            custom("Custom(11)", 11),
            custom("Custom(0)", 0),
            custom("Custom(1000)", 1000),
        ],
    }
}

fn iv_u8(n: u64) -> InterpretValue {
    InterpretValue::int(Ty::U8, i128::from(n)).expect("u8 is an integer type")
}

fn struct_ty(id: u32) -> Ty {
    Ty::Struct(trust_ir::value::StructId::new(id))
}

/// The surrogate struct.441 declaration: 81 `u8` fields + `bool` at field 81.
static SM_TYPE_DECL: std::sync::LazyLock<String> = std::sync::LazyLock::new(|| {
    let fields = std::iter::repeat_n("u8", 81)
        .chain(std::iter::once("bool"))
        .collect::<Vec<_>>()
        .join(", ");
    format!("struct @EnvSurrogate {{ {fields} }} id=441")
});

/// The 82-field zero constant for the surrogate struct: 81 `0`s + `false`.
fn sm_const_fields() -> String {
    let mut fields = vec!["0"; 81];
    fields.push("false");
    fields.join(", ")
}

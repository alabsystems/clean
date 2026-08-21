// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The chains the GAP-2 differential covers, and **E3** — the shipped compiled
//! function, called directly.
//!
//! E3 is the leg that matters most and the one that is easiest to get wrong by
//! being lazy about it. It must be the REAL function from `clean-kernel`,
//! reached through `to_mir` + the rustc pass pipeline + LLVM. Where the shipped
//! function is not reachable from here (a private `fn`), that is recorded as an
//! absent leg — which downgrades the row to `Insufficient` unless two other
//! executors answered — and never faked by re-implementing the body.

use clean_kernel::mode::{CleanMode, SourceSystem};
use clean_verify::ir_semdiff::{ArgShape, EnumModel, ResultKind, RunResult};
use trust_ir::ty::Ty;

/// One chained body the differential runs.
pub struct Chain {
    /// Short name, used in output and in generated def names.
    pub name: &'static str,
    /// Committed emitted body, relative to `tests/fixtures/`.
    pub fixture: &'static str,
    /// The def-path name as the fixture prints it (rewritten before parsing;
    /// trust-ir's parser cannot read `::` in a function name).
    pub original_name: &'static str,
    /// trust-ir text declarations of every enum the body mentions. More than
    /// one when the parameter and the result are different enums.
    pub enum_decls: &'static str,
    /// Declared id of the ARGUMENT enum, selected by id rather than position.
    pub arg_enum: u32,
    /// The SSA value the body loads the enum into, for the payload guard.
    pub loaded_value: &'static str,
    /// The subject's return type.
    pub ret_ty: Ty,
    /// How the body receives its argument.
    pub arg_shape: ArgShape,
    /// How the returned value is encoded on the Clean side.
    pub result_kind: ResultKind,
    /// Name of the registered Clean module.
    pub clean_module: &'static str,
    /// The Clean definitions that build that module, in registration order.
    pub clean_defs: &'static [&'static str],
    /// How faithful the enum declaration is.
    pub enum_model: EnumModel,
    /// The clean-minus-trust cost offset this chain is DECLARED to have.
    ///
    /// Compared against the measured offset, and a mismatch is RED. A declared
    /// value is what turns cost from telemetry into a gate: uniformity alone
    /// cannot see a constant error, because a wrong harness overhead shifts
    /// every row by the same amount. It is not a free knob — the overhead it
    /// pins is independently counted from the harness's own instructions by
    /// `crystal_a3_harness_step_overhead_is_derived_not_tuned`.
    pub expected_cost_offset: i64,
    /// How many permutations of this switch's target blocks leave the observed
    /// value function UNCHANGED — the size of the blind spot a value-only
    /// differential has on this body.
    ///
    /// `1` means every wrong routing is observable. Anything larger is the
    /// number of distinct wrong routings this gate's value comparison cannot
    /// see, and is why routing is pinned structurally instead. Declared here
    /// and recomputed from the committed fixture by
    /// `crystal_a3_discriminating_power_is_measured`, so it cannot drift.
    pub value_preserving_target_permutations: u64,
    /// Every inhabitant of the argument type, exhaustively.
    pub domain: &'static [u32],
    /// Is `domain` the WHOLE domain? Never rounded up.
    pub total_domain: bool,
    /// E3, when the shipped function is reachable from this crate.
    pub shipped: Option<fn(u32) -> Option<RunResult>>,
    /// Why E3 is absent, when it is.
    pub shipped_absent: Option<&'static str>,
}

/// E3 for `CleanMode::has_cubical_layer` — the real shipped function.
fn shipped_has_cubical_layer(tag: u32) -> Option<RunResult> {
    // Declaration order in `clean-kernel/src/mode.rs`, which is what the
    // discriminant is: the enum is fieldless and carries no explicit values.
    let mode = match tag {
        0 => CleanMode::Constructive,
        1 => CleanMode::Impredicative,
        2 => CleanMode::Cubical,
        3 => CleanMode::Directed,
        4 => CleanMode::Classical,
        5 => CleanMode::SetTheoretic,
        _ => return None,
    };
    Some(RunResult::Bool(mode.has_cubical_layer()))
}

/// E3 for `CleanMode::from_source_system` — the real shipped function.
///
/// Declaration order in `clean-kernel/src/mode.rs:336`. Note tag 10
/// (`MetamathSet`) is the one the EMITTED switch has no case for: it reaches
/// the default edge. Enumerating the domain exhaustively is what puts a real
/// input on that edge rather than trusting that it behaves.
fn shipped_from_source_system(tag: u32) -> Option<RunResult> {
    let system = match tag {
        0 => SourceSystem::Lean4,
        1 => SourceSystem::Coq,
        2 => SourceSystem::Agda,
        3 => SourceSystem::CubicalAgda,
        4 => SourceSystem::IsabelleHOL,
        5 => SourceSystem::HOLLight,
        6 => SourceSystem::HOL4,
        7 => SourceSystem::Mizar,
        8 => SourceSystem::MetamathZFC,
        9 => SourceSystem::MetamathSet,
        10 => SourceSystem::PVS,
        11 => SourceSystem::ACL2,
        _ => return None,
    };
    Some(RunResult::EnumTag(
        CleanMode::from_source_system(system) as u32
    ))
}

/// The covered chains.
pub fn chains() -> Vec<Chain> {
    vec![
        Chain {
            name: "has_cubical_layer",
            fixture: "has_cubical_layer.trust-ir.txt",
            original_name: "@mode::CleanMode::has_cubical_layer",
            // CleanMode is genuinely FIELDLESS, so this declaration is exact:
            // six variants, implicit discriminants 0..5, u8 tag.
            enum_decls: "enum @CleanMode repr(u8) { Constructive, Impredicative, \
                         Cubical, Directed, Classical, SetTheoretic } id=13",
            arg_enum: 13,
            loaded_value: "%2",
            ret_ty: Ty::Bool,
            arg_shape: ArgShape::PointerCell,
            result_kind: ResultKind::Bool,
            clean_module: "ir_h2_module",
            // A FUNCTION, not a constant array: this chain's module is MINTED
            // (crystal A2, `src/ir_mint`), so the one source of truth is the
            // generated script `add_eval_ir_mode` replays. The contract this
            // field exists for is unchanged and is the reason it moved — the
            // differential must read the registered lines, not a copy.
            clean_defs: clean_verify::spec::ir_h2_module_defs(),
            enum_model: EnumModel::Exact,
            expected_cost_offset: 0,
            // bb1 and bb2 both emit `const bool true`; bb3 is the only false
            // target. Swapping bb1 and bb2 is invisible to a value comparison.
            value_preserving_target_permutations: 2,
            domain: &[0, 1, 2, 3, 4, 5],
            total_domain: true,
            shipped: Some(shipped_has_cubical_layer),
            shipped_absent: None,
        },
        Chain {
            name: "from_source_system",
            fixture: "from_source_system.trust-ir.txt",
            original_name: "@mode::CleanMode::from_source_system",
            // SourceSystem is fieldless: twelve variants, implicit 0..11.
            // TWO declarations: the parameter is `enum.178` (SourceSystem) and
            // the RESULT is `enum.13` (CleanMode). Declaring only one is a
            // `type_error`, which is how this was caught.
            enum_decls: "enum @SourceSystem repr(u8) { Lean4, Coq, Agda, CubicalAgda, \
                         IsabelleHOL, HOLLight, HOL4, Mizar, MetamathZFC, MetamathSet, \
                         PVS, ACL2 } id=178\n\n\
                         enum @CleanMode repr(u8) { Constructive, Impredicative, Cubical, \
                         Directed, Classical, SetTheoretic } id=13",
            arg_enum: 178,
            loaded_value: "%0",
            // The subject takes `enum.178` and RETURNS `enum.13` — the two are
            // different types, and conflating them is a `signature_mismatch`.
            ret_ty: Ty::Enum(trust_ir::value::EnumId::new(13)),
            // The parameter IS the aggregate: no `load` stands in front of the
            // switch, so a load-side misunderstanding cannot mask a switch-side
            // one.
            arg_shape: ArgShape::ValueAggregate,
            result_kind: ResultKind::EnumTag,
            clean_module: "ir_fs_module",
            clean_defs: clean_verify::spec::IR_FS_MODULE_DEFS,
            enum_model: EnumModel::Exact,
            expected_cost_offset: 0,
            // **THE CORRECTION, 2026-08-20.** This chain used to be described
            // as the differential's SHARPEST, on the grounds that "a contiguous
            // table can be got right by a mechanism that merely indexes, while
            // a hole cannot". Measured from the committed fixture, it is the
            // DULLEST of the three: six of its twelve target blocks
            // (bb5 bb6 bb7 bb10 bb11 bb12) emit the same `const enum.13 { 4 }`,
            // two more emit `{ 0 }` and two emit `{ 5 }`, so 2,880 permutations
            // of its targets leave every returned value unchanged.
            //
            // In particular the very off-by-one the hole was supposed to expose
            // — a positional encoder that routes case 11 to bb12 and tag 10 to
            // bb11 instead of the other way round — is observably wrong on
            // **0 of 12** inputs, and cost cannot separate them either: both
            // blocks are `const` + `br`, two instructions.
            //
            // The hole is still worth having and is still guarded
            // (`crystal_a3_default_edge_is_actually_reached`), because it puts a
            // real input on the DEFAULT edge. But what refuses a wrong ROUTE is
            // the structural tag-for-tag comparison of the registered Clean case
            // table against the emitted switch
            // (`crystal_a3_routing_pairwise_matches_the_emitted_switch`), not
            // this value differential.
            value_preserving_target_permutations: 2880,
            domain: &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11],
            total_domain: true,
            shipped: Some(shipped_from_source_system),
            shipped_absent: None,
        },
        Chain {
            name: "level_kind_ord",
            fixture: "level_kind_ord.trust-ir.txt",
            original_name: "@level::Level::kind_ord",
            // `Level` DOES carry payloads (Succ/Max/IMax/Param). They are
            // elided here, which is sound only because the body provably never
            // reads them — enforced mechanically by `payload_is_unread`, not
            // asserted. Recorded as TagSurrogate so the report says so.
            enum_decls: "enum @Level repr(u8) { Zero, Succ, Max, IMax, Param } id=2",
            arg_enum: 2,
            loaded_value: "%2",
            ret_ty: Ty::U8,
            arg_shape: ArgShape::PointerCell,
            result_kind: ResultKind::Int,
            clean_module: "ir_ko_module",
            clean_defs: clean_verify::spec::IR_KO_MODULE_DEFS,
            enum_model: EnumModel::TagSurrogate,
            expected_cost_offset: 0,
            // The ONLY fully discriminating chain of the three: five targets,
            // five distinct answers, so every wrong routing changes a returned
            // value and the differential sees it. It is also the one chain with
            // no E3 — the sharpest body here is the one with the fewest
            // executors, which is worth stating rather than averaging away.
            value_preserving_target_permutations: 1,
            domain: &[0, 1, 2, 3, 4],
            total_domain: true,
            shipped: None,
            shipped_absent: Some(
                "`Level::kind_ord` is a PRIVATE fn in clean-kernel/src/level/mod.rs:598 \
                 and is not reachable from this crate. Recorded as an absent leg rather \
                 than re-implemented: a re-implementation would be a fourth transcription \
                 agreeing with itself, which is exactly the failure mode this gate exists \
                 to detect.",
            ),
        },
    ]
}

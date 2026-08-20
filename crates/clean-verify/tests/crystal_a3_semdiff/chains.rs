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
            clean_defs: clean_verify::spec::IR_H2_MODULE_DEFS,
            enum_model: EnumModel::Exact,
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
            // TWO declarations: the parameter is `enum.175` (SourceSystem) and
            // the RESULT is `enum.13` (CleanMode). Declaring only one is a
            // `type_error`, which is how this was caught.
            enum_decls: "enum @SourceSystem repr(u8) { Lean4, Coq, Agda, CubicalAgda, \
                         IsabelleHOL, HOLLight, HOL4, Mizar, MetamathZFC, MetamathSet, \
                         PVS, ACL2 } id=175\n\n\
                         enum @CleanMode repr(u8) { Constructive, Impredicative, Cubical, \
                         Directed, Classical, SetTheoretic } id=13",
            arg_enum: 175,
            loaded_value: "%0",
            // The subject takes `enum.175` and RETURNS `enum.13` — the two are
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
            // THE POINT OF THIS CHAIN. The emitted switch lists cases
            // 0..9 and 11 — there is NO case 10. Tag 10 (PVS) reaches the
            // DEFAULT edge, and it is only reached because the domain is
            // enumerated exhaustively rather than sampled. A non-contiguous
            // case list with a hole in the middle is the sharpest available
            // test of the one thing GAP 2 names by name: whether Clean's
            // `switch` encoding routes like trust-ir's.
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

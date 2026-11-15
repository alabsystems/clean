// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The loader's record of the declarations it drops as duplicates.
//!
//! The loader keeps the FIRST declaration of a name. When a later module
//! declares a name another module (or the kernel) already holds, the rest of
//! that module is checked against the resident constant, and Lean's `addDecl`
//! would have refused the module's declaration as already declared. So every
//! such drop is recorded in `LoadSummary::shadowed_declarations`, for a
//! Lean-profile re-check to refuse, except the two that Lean itself accepts:
//!
//! - a restatement by another part of the SAME module (`.olean` /
//!   `.olean.server` / `.olean.private`), or of a quotient primitive (the
//!   kernel seeds Lean's canonical quotient; Lean's replay of a `quotInfo` is
//!   the kernel's own `quotDecl`);
//! - a theorem or axiom restated with the resident one's universe parameters
//!   and an equal type (`Lean.Environment.finalizeImport`'s `subsumesInfo`,
//!   and the duplicate-theorem skip of `Lean.Environment.Replay.replayConstant`).
//!   Lean realizes auxiliary theorems (`.eq_1`, `.congr_simp`, …) in whichever
//!   module first needs one, so honest `.olean`s restate them.

use super::convert::{convert_parsed_constant_to_type_stub, ConvertedConstant};
use super::convert_direct::convert_load_constant;
use super::convert_expr_direct::RegionPtrCache;
use super::load_parse::LoadModule;
use super::ExprInternCache;
use crate::module::{ConstantKind, ParsedModule};
use clean_kernel::env::{
    ConstantKind as KernelConstantKind, ConstantOrigin, Declaration, Environment, ProofValueElision,
};
use clean_kernel::expr::Expr;
use clean_kernel::name::Name;

/// A dropped duplicate: the constant's index in its module, its name, and who
/// holds the name.
pub(super) type ShadowedAt = (usize, Name, String);

/// The provenance of a resident constant that an incoming declaration of
/// `module` would duplicate, when that resident constant is NOT this module's
/// own: `None` when it is (a restatement by another part of the same module),
/// or when the incoming declaration is a quotient primitive.
pub(super) fn foreign_resident_provenance(
    env: &Environment,
    name: &Name,
    module: Option<&str>,
    incoming_is_quot: bool,
) -> Option<String> {
    if incoming_is_quot {
        return None;
    }
    let base = |m: &str| -> String {
        m.strip_suffix("._server")
            .or_else(|| m.strip_suffix("._private"))
            .unwrap_or(m)
            .to_owned()
    };
    let this = module.map(base);
    match env.get_constant_origin(name) {
        Some(ConstantOrigin::Olean {
            module: Some(m), ..
        })
        | Some(ConstantOrigin::CleanPayload {
            module: Some(m), ..
        }) => {
            let resident = base(m);
            if this.as_deref() == Some(resident.as_str()) {
                None
            } else {
                Some(format!("declared by module `{resident}`"))
            }
        }
        Some(ConstantOrigin::Kernel { .. }) => Some("seeded by the kernel".to_owned()),
        _ => Some("resident with no recorded provenance".to_owned()),
    }
}

/// Whether Lean's import accepts a declaration of `name` with `level_params`
/// and `type_`, from a theorem or axiom, as a restatement of the resident
/// constant: the resident one is a theorem or axiom with the same universe
/// parameters and an equal type, compared as Lean's `==` compares
/// expressions (binder annotations ignored, `clean_kernel::env::lean_expr_eqv`).
#[must_use]
pub fn lean_accepts_restatement(
    env: &Environment,
    name: &Name,
    level_params: &[Name],
    type_: &Expr,
) -> bool {
    env.get_const(name).is_some_and(|resident| {
        matches!(
            resident.kind,
            KernelConstantKind::Theorem | KernelConstantKind::Axiom
        ) && resident.level_params == level_params
            && clean_kernel::env::lean_expr_eqv(&resident.type_, type_)
    })
}

/// A dropped duplicate that restates the resident constant (see
/// [`lean_accepts_restatement`]): its name, who holds it, and whether the
/// incoming declaration is a theorem (Lean's replay skips a restated theorem
/// and refuses a restated axiom, `Lean/Replay.lean` `replayConstant`).
pub(super) type Restated = (Name, String, bool);

/// The dropped duplicates of a parsed `module`, split into those Lean would
/// refuse and the theorems or axioms that restate the resident constant.
pub(super) fn refused_duplicates_parsed(
    env: &Environment,
    module: &ParsedModule,
    shadowed: Vec<ShadowedAt>,
) -> (
    Vec<(Name, String)>,
    Vec<Restated>,
    Vec<super::PendingRestatement>,
) {
    let mut refused = Vec::new();
    let mut restated = Vec::new();
    let mut pending = Vec::new();
    for (i, name, held_by) in shadowed {
        let incoming = &module.constants[i];
        let restates = matches!(incoming.kind, ConstantKind::Theorem | ConstantKind::Axiom)
            && convert_parsed_constant_to_type_stub(incoming)
                .ok()
                .flatten()
                .is_some_and(|stub| {
                    lean_accepts_restatement(env, &name, &stub.level_params, &stub.type_)
                });
        if restates {
            let theorem = matches!(incoming.kind, ConstantKind::Theorem);
            if let Some(evidence) = super::restatement_evidence::matched(env, &name, theorem) {
                pending.push(evidence);
            }
            restated.push((name, held_by, theorem));
        } else {
            refused.push((name, held_by));
        }
    }
    (refused, restated, pending)
}

/// [`refused_duplicates_parsed`] for a module loaded straight from its region.
pub(super) fn refused_duplicates_loaded(
    env: &Environment,
    module: &LoadModule,
    shadowed: Vec<ShadowedAt>,
) -> (
    Vec<(Name, String)>,
    Vec<Restated>,
    Vec<super::PendingRestatement>,
) {
    if shadowed.is_empty() {
        return (Vec::new(), Vec::new(), Vec::new());
    }
    let region = module.region();
    let mut intern = ExprInternCache::with_capacity(64);
    let mut memo = RegionPtrCache::for_region();
    let mut refused = Vec::new();
    let mut restated = Vec::new();
    let mut pending = Vec::new();
    for (i, name, held_by) in shadowed {
        let incoming = &module.constants[i];
        let restates = matches!(incoming.kind, ConstantKind::Theorem | ConstantKind::Axiom)
            && match convert_load_constant(
                incoming,
                &region,
                &mut intern,
                &mut memo,
                ProofValueElision::OpaqueAndTheorem,
            ) {
                ConvertedConstant::Other(
                    _,
                    Ok((
                        Declaration::Theorem {
                            level_params,
                            type_,
                            ..
                        }
                        | Declaration::Axiom {
                            level_params,
                            type_,
                            ..
                        },
                        _,
                    )),
                    _,
                ) => lean_accepts_restatement(env, &name, &level_params, &type_),
                _ => false,
            };
        if restates {
            let theorem = matches!(incoming.kind, ConstantKind::Theorem);
            if let Some(evidence) = super::restatement_evidence::matched(env, &name, theorem) {
                pending.push(evidence);
            }
            restated.push((name, held_by, theorem));
        } else {
            refused.push((name, held_by));
        }
    }
    (refused, restated, pending)
}

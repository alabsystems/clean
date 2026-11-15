// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The comparand a TV certificate records, in the one spelling the minter and
//! the importer's source binding (WS6.8) share, so the two cannot normalize
//! differently.

use super::*;

/// The recorded COMPARAND of a TV certificate: `fun (G0…)(x…) => rhs`, the
/// source denotation closed over the callee symbols and then the parameters
/// (the re-checker strips `callees.len() + arity` binders). One spelling, used
/// by the minter ([`super::attempt_certify`]) and by the importer's source binding
/// ([`source_comparand_bytes`]), so the two cannot normalize differently.
pub(super) fn comparand_lambda(rhs_body: &Expr, arity: usize, callee_arities: &[usize]) -> Expr {
    let with_params = (0..arity).fold(rhs_body.clone(), |acc, _| {
        Expr::lam(BinderInfo::Default, Expr::const_str("Nat"), acc)
    });
    callee_arities.iter().rev().fold(with_params, |acc, ca| {
        Expr::lam(BinderInfo::Default, callee_fn_ty(*ca), acc)
    })
}

/// The `context` bytes the minter WOULD record for `func` (a function of
/// `module`) if `defn` were its source definition: the same denotations, the
/// same comparand closure, the same `bincode` encoding [`super::attempt_certify`]
/// writes into a `CleanCic` certificate.
///
/// This is the importer's half of the source binding (WS6.8): a client that
/// holds its OWN elaboration of an imported symbol recomputes the comparand
/// from it and demands byte equality with the far certificate's recorded
/// `context`. A far certificate minted against a different body — honestly
/// certified, same signature — then backs nothing in the client, because the
/// client's meaning of the symbol is not the one the dependency proved.
///
/// Only the fixed-width (U-w) comparand exists here: a Fragment-5 body is
/// decided but never minted (see [`super::FRAGMENT5_NOT_MINTED`]), so there is no
/// recorded comparand to equal and the function refuses. Every other failure
/// (a source outside the fragment, an escaped name the legacy identity does
/// not measure, a serialization failure) is an `Err` naming the step — the
/// caller writes no proof row for it.
pub(crate) fn source_comparand_bytes(
    module: &Module,
    func: &Function,
    defn: &Expr,
    source_environment: Option<&Environment>,
) -> Result<Vec<u8>, String> {
    if !crate::emit_trust_ir::names::legacy_source_identity_supported(defn) {
        return Err("legacy TV source identity is unmeasured for escaped typed names".to_string());
    }
    let lhs = denote_function(module, func).map_err(|e| format!("emitted side: {e}"))?;
    let nat_return = module
        .func_types
        .get(func.ty.as_usize())
        .and_then(|ft| ft.returns.first())
        .is_some_and(|t| matches!(t, Ty::Ptr));
    if nat_return {
        return Err(FRAGMENT5_NOT_MINTED.to_string());
    }
    let records = RecordVocab::from_module(module);
    let source = denote_source_with_requirements(
        defn,
        lhs.width,
        &lhs.callees,
        &records,
        source_environment,
    )
    .map_err(|e| format!("source side: {e}"))?;
    if source.requires_original_source_equation {
        let environment = source_environment
            .ok_or("propositional ite requires the original source environment and a checked source equation")?;
        check_original_source_equation(environment, &func.name, defn, &lhs)?;
    }
    let rhs = source.denotation;
    let callee_arities: Vec<usize> = lhs.callees.iter().map(|(_, a)| *a).collect();
    bincode::serialize(&comparand_lambda(&rhs.body, rhs.arity, &callee_arities))
        .map_err(|e| format!("comparand failed to serialize: {e}"))
}

// Copyright 2026 Andrew Yates | Apache-2.0
//! Separate untrusted foreign-adapter C proposal. No normal compiler route,
//! source check, runtime ownership, TV, body gate or permission is changed.
use super::CEmitter;
use crate::boxing::{mk_boxed_version_from_signature, CLOSURE_MAX_ARGS};
use crate::ffi_bridge::FfiBridge;
use crate::ir::{IRDecl, IRType, VarId};
use crate::ir_checker::{check_decls, IRError};
use clean_kernel::Name;
use std::collections::{HashMap, HashSet};
use thiserror::Error;

/// Actual proposed bindings, preserved separately from the logical call in IR.
#[derive(Debug, Clone)]
pub struct BoxedForeignCEntry {
    pub lean_name: Name,
    pub scalar_symbol: String,
    pub scalar_params: Vec<IRType>,
    pub scalar_return: IRType,
    pub boxed_symbol: String,
    pub adapter: IRDecl,
}

/// Source DATA for foreign adapters, never an implementation certificate.
#[derive(Debug, Clone)]
pub struct BoxedForeignCProposal {
    pub code: String,
    pub entries: Vec<BoxedForeignCEntry>,
}

#[derive(Debug, Error)]
pub enum ForeignCProposalError {
    #[error("foreign proposal needs exactly one metadata entry for {0}")]
    MissingOrAmbiguous(Name),
    #[error("foreign proposal repeats the logical identity {0}")]
    Duplicate(Name),
    #[error("foreign proposal exceeds the bounded fixed-entry DATA subset")]
    TooLarge,
    #[error("foreign proposal needs a plain C identifier for {0}")]
    InvalidSymbol(Name),
    #[error("foreign proposal has a scalar/boxed or boxed/boxed symbol collision: {0}")]
    SymbolCollision(String),
    #[error("foreign proposal reuses a scalar symbol with incompatible signatures: {0}")]
    IncompatibleAlias(String),
    #[error(transparent)]
    Ir(#[from] IRError),
}

/// Propose C for selected metadata-bound boxed entries using the existing
/// signature builder and C emitter. A function value refers to the returned
/// **boxed_symbol**, never to scalar_symbol as an Object callable.
///
/// The original logical Name stays in every adapter IR call; its separate
/// captured C symbol is used at C emission. No meaning is inferred from either
/// spelling. Only selected externs are emitted, so source/proof dependencies
/// in an FFI catalog do not become executable bodies or conflicting prototypes.
/// This bounded proposal covers at most32 entries and the existing fixed-arity
/// boxed subset (larger entries need the compiler's array/flat wrapper path).
/// This does not compile a logical extern body or clear its existing refusal.
/// The caller still owes original-source/foreign-implementation association,
/// erasure, heap/RC/NoUB, ABI, runtime and machine evidence independently.
///
/// # Errors
/// Refuses missing, ambiguous or repeated metadata identities and preserves
/// the ordinary structural IR and C-emitter refusals. No proof/token is returned.
pub fn propose_boxed_foreign_c(
    bridge: &FfiBridge,
    requested: &[Name],
) -> Result<BoxedForeignCProposal, ForeignCProposalError> {
    if requested.len() > 32 {
        return Err(ForeignCProposalError::TooLarge);
    }
    let mut seen = HashSet::new();
    let mut entries = Vec::new();
    for name in requested {
        if !seen.insert(name.clone()) {
            return Err(ForeignCProposalError::Duplicate(name.clone()));
        }
        let matches: Vec<_> = bridge
            .extern_decls()
            .iter()
            .filter(|entry| entry.lean_name == *name)
            .collect();
        let [entry] = matches.as_slice() else {
            return Err(ForeignCProposalError::MissingOrAmbiguous(name.clone()));
        };
        if entry.param_types.len() > CLOSURE_MAX_ARGS {
            return Err(ForeignCProposalError::TooLarge);
        }
        if entry.c_name.len() > 4096 {
            return Err(ForeignCProposalError::TooLarge);
        }
        let mut spelling = entry.c_name.bytes();
        if !spelling
            .next()
            .is_some_and(|b| b.is_ascii_alphabetic() || b == b'_')
            || !spelling.all(|b| b.is_ascii_alphanumeric() || b == b'_')
        {
            return Err(ForeignCProposalError::InvalidSymbol(name.clone()));
        }
        let params: Vec<_> = entry
            .param_types
            .iter()
            .enumerate()
            .map(|(index, ty)| (VarId(index as u32), ty.clone()))
            .collect();
        let adapter = mk_boxed_version_from_signature(name, &params, &entry.return_type);
        entries.push(BoxedForeignCEntry {
            lean_name: name.clone(),
            scalar_symbol: entry.c_name.clone(),
            scalar_params: entry.param_types.clone(),
            scalar_return: entry.return_type.clone(),
            boxed_symbol: String::new(),
            adapter,
        });
    }
    let declarations: Vec<_> = entries.iter().map(|entry| entry.adapter.clone()).collect();
    check_decls(&declarations)?;
    let mut emitter = CEmitter::new();
    // Derive every emitted boxed identity before emitting any declaration. Both
    // namespaces inhabit C's ordinary identifier namespace, even across entries.
    let mut boxed_symbols = HashSet::new();
    for entry in &mut entries {
        entry.boxed_symbol = emitter.emit_name(&entry.adapter.name);
        if !boxed_symbols.insert(entry.boxed_symbol.clone()) {
            return Err(ForeignCProposalError::SymbolCollision(
                entry.boxed_symbol.clone(),
            ));
        }
    }
    let mut scalar_signatures = HashMap::new();
    for entry in &entries {
        if boxed_symbols.contains(&entry.scalar_symbol) {
            return Err(ForeignCProposalError::SymbolCollision(
                entry.scalar_symbol.clone(),
            ));
        }
        let signature = (entry.scalar_params.clone(), entry.scalar_return.clone());
        if let Some(previous) =
            scalar_signatures.insert(entry.scalar_symbol.clone(), signature.clone())
        {
            if previous != signature {
                return Err(ForeignCProposalError::IncompatibleAlias(
                    entry.scalar_symbol.clone(),
                ));
            }
        }
    }
    emitter.emit_header();
    for entry in &mut entries {
        // Data-only explicit binding; no mutation of the original IR identity.
        emitter
            .proposed_foreign_symbols
            .insert(entry.lean_name.clone(), entry.scalar_symbol.clone());
        emitter.decl_shapes.insert(
            entry.lean_name.clone(),
            (entry.scalar_params.len(), entry.scalar_return.clone()),
        );
        let params = if entry.scalar_params.is_empty() {
            "void".to_string()
        } else {
            entry
                .scalar_params
                .iter()
                .map(|ty| emitter.emit_type(ty))
                .collect::<Vec<_>>()
                .join(", ")
        };
        emitter.writeln(&format!(
            "extern {} {}({});",
            emitter.emit_type(&entry.scalar_return),
            entry.scalar_symbol,
            params
        ));
    }
    emitter.emit_decls(&declarations)?;
    Ok(BoxedForeignCProposal {
        code: emitter.finish(),
        entries,
    })
}

#[cfg(test)]
mod tests;

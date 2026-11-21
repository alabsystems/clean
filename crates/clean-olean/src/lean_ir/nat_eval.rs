// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! First-order Nat calls into the captured interpreter IR of a Lean 4.36
//! module. The exported kernel signature selects the entry. The assembled
//! interpreter declarations supply the code, including same-module helpers.

use clean_kernel::{BigNat, Expr, ExprKind, Name};

use super::decode::{IrDecoder, IrLayout};
use super::exported_term_eval::evaluate_nat_in_region;
use super::module_ir::check_companion_layout;
use super::nat_program::{extract_nat_program, reject_base_initializers, CapturedNatProgram};
use crate::import::{
    assemble_load_part, parse_load_module, read_and_convert_expr_with_memo, ExprInternCache,
    RegionPtrCache,
};
use crate::module::{ConstantKind, DefinitionSafety};
use crate::region::CompactedRegion;
use crate::{CapturedModuleBytes, OleanError, OleanHeader, OleanResult};

#[cfg(test)]
mod tests;

/// An eligible exported Nat function and the exact immutable bytes that
/// supplied its signature. Its body is decoded only when called.
#[derive(Debug)]
pub struct ImportedNatFunction<'a> {
    captured: CapturedModuleBytes<'a>,
    function: Name,
    arity: usize,
    marked_meta: bool,
}

impl ImportedNatFunction<'_> {
    /// Number of positional Nat inputs in the exported kernel signature.
    #[must_use]
    pub const fn arity(&self) -> usize {
        self.arity
    }

    /// Whether the producer marked this exact definition as `meta`.
    #[must_use]
    pub const fn is_marked_meta(&self) -> bool {
        self.marked_meta
    }

    /// Execute marked meta code from the base part or ordinary code from the
    /// captured `.ir.sig` and `.ir` parts.
    ///
    /// # Errors
    /// Refuses absent, incompatible or malformed parts, an unsupported ABI
    /// or operation, incorrect argument count, and exhausted bounds.
    pub fn evaluate(&self, arguments: &[BigNat]) -> OleanResult<BigNat> {
        if arguments.len() != self.arity {
            return Err(refusal(
                &self.function,
                format!(
                    "expected {} Nat arguments, got {}",
                    self.arity,
                    arguments.len()
                ),
            ));
        }
        self.with_body(|region, root| {
            evaluate_nat_in_region(region, root, &self.function, arguments)
        })
    }

    /// Read a straight-line, acyclic Nat program from the exact captured IR.
    ///
    /// # Errors
    /// Refuses unreadable artifacts, initializers, unsupported operations,
    /// and inconsistent compiled call or local-variable records.
    pub fn native_program(&self) -> OleanResult<CapturedNatProgram> {
        reject_base_initializers(self.captured.base, &self.function)?;
        self.with_body(|region, root| extract_nat_program(region, root, &self.function, self.arity))
    }

    fn with_body<T>(
        &self,
        read: impl FnOnce(&CompactedRegion<'_>, u64) -> OleanResult<T>,
    ) -> OleanResult<T> {
        if self.marked_meta {
            let header = OleanHeader::parse(self.captured.base)?;
            let region = CompactedRegion::new(self.captured.base, header.base_addr);
            return read(&region, region.root_ptr()?);
        }
        let signature = self
            .captured
            .ir_signature
            .ok_or_else(|| refusal(&self.function, "missing captured .ir.sig"))?;
        let body = self
            .captured
            .ir
            .ok_or_else(|| refusal(&self.function, "missing captured .ir"))?;
        for (suffix, bytes) in [("ir.sig", signature), ("ir", body)] {
            check_companion_layout(
                &self.function,
                &self.captured.canonical_path.with_extension(suffix),
                bytes,
                IrLayout::Lean436,
            )
            .map_err(|error| refusal(&self.function, error))?;
        }
        let part = assemble_load_part(signature, None, body)
            .map_err(|error| refusal(&self.function, error))?;
        let region = CompactedRegion::new(&part.bytes, part.base_addr);
        read(&region, part.root_ptr)
    }
}

/// Check whether the supplied module's exported kernel records contain a
/// safe, monomorphic declaration with the exact shape `Nat → … → Nat`.
/// Lean 4.36 also exports some definitions as axiom stubs. Eligibility only
/// establishes their signature. Execution requires an actual IR body.
///
/// Pass a checked capture selected by the import policy. `Ok(None)` means
/// the named declaration is outside the entry shape or is absent from the
/// exported part. Once eligible, execution errors do not yield `None`.
///
/// # Errors
/// Refuses a foreign or malformed artifact and inconsistent declared names.
pub fn prepare_imported_nat_function<'a>(
    captured: CapturedModuleBytes<'a>,
    function: &Name,
) -> OleanResult<Option<ImportedNatFunction<'a>>> {
    check_companion_layout(
        function,
        captured.canonical_path,
        captured.base,
        IrLayout::Lean436,
    )
    .map_err(|error| refusal(function, error))?;
    let base = parse_load_module(captured.base.to_vec())?;
    if !base.is_module {
        return Ok(None);
    }
    if !base.inventory_arrays_valid || base.const_names.len() != base.constants.len() {
        return Err(refusal(function, "invalid exported declaration inventory"));
    }
    let mut names = base
        .const_names
        .iter()
        .enumerate()
        .filter(|(_, name)| *name == function);
    let mut constants = base
        .constants
        .iter()
        .enumerate()
        .filter(|(_, row)| row.kernel_name == *function);
    let constant = match (names.next(), constants.next()) {
        (None, None) => return Ok(None),
        (Some((entry, _)), Some((row, constant)))
            if entry == row && names.next().is_none() && constants.next().is_none() =>
        {
            constant
        }
        _ => {
            return Err(refusal(
                function,
                "inconsistent exported declaration identity",
            ))
        }
    };
    if !matches!(
        constant.kind,
        ConstantKind::Definition | ConstantKind::Axiom
    ) || constant.definition_safety != Some(DefinitionSafety::Safe)
        || !constant.kernel_level_params.is_empty()
    {
        return Ok(None);
    }
    let (type_, _) = read_and_convert_expr_with_memo(
        &base.region(),
        constant.type_ptr,
        &constant.name,
        &mut ExprInternCache::default(),
        &mut RegionPtrCache::for_region(),
    )
    .map_err(|error| refusal(function, error))?;
    let Some(arity) = nat_arity(&type_) else {
        return Ok(None);
    };
    Ok(Some(ImportedNatFunction {
        captured,
        function: function.clone(),
        arity,
        marked_meta: marked_meta(&base.region(), function)?,
    }))
}

fn marked_meta(region: &CompactedRegion<'_>, function: &Name) -> OleanResult<bool> {
    let marker = Name::anon()
        .str("_private")
        .str("Lean")
        .str("Compiler")
        .str("MetaAttr")
        .num(0)
        .str("Lean")
        .str("metaExt");
    let entries = region
        .ir_part_entries(region.root_ptr()?)
        .map_err(|error| refusal(function, error))?;
    let Some((_, table)) = entries.entries.iter().find(|(name, _)| *name == marker) else {
        return Ok(false);
    };
    const MAX_MARKED_NAMES: usize = 1 << 16;
    let mut found = false;
    let pointers = IrDecoder::new(region)
        .array(*table, "Lean.metaExt", MAX_MARKED_NAMES)
        .map_err(|error| refusal(function, error))?;
    for pointer in pointers {
        if region.read_kernel_name_ptr(pointer)? == *function {
            if found {
                return Err(refusal(function, "duplicate meta marker"));
            }
            found = true;
        }
    }
    Ok(found)
}

/// Check the source signature and execute one imported Nat function.
///
/// # Errors
/// Refuses an ineligible declaration and the errors of
/// [`ImportedNatFunction::evaluate`].
pub fn evaluate_imported_nat_function(
    captured: CapturedModuleBytes<'_>,
    function: &Name,
    arguments: &[BigNat],
) -> OleanResult<BigNat> {
    prepare_imported_nat_function(captured, function)?
        .ok_or_else(|| refusal(function, "no exported first-order Nat declaration"))?
        .evaluate(arguments)
}

fn nat_arity(mut type_: &Expr) -> Option<usize> {
    let nat = Name::anon().str("Nat");
    let is_nat = |expr: &Expr| matches!(expr.kind(), ExprKind::Const(name, levels) if *name == nat && levels.is_empty());
    let mut arity = 0;
    while let ExprKind::Pi(_, domain, body) = type_.kind() {
        if !is_nat(domain) {
            return None;
        }
        arity += 1;
        type_ = body;
    }
    is_nat(type_).then_some(arity)
}

fn refusal(function: &Name, detail: impl std::fmt::Display) -> OleanError {
    OleanError::Region(format!("imported Nat IR {function}: {detail}"))
}

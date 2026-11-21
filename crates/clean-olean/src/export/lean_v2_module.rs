// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Stable native declaration views and the IR envelope for modules with no code.

use std::collections::HashSet;

use clean_kernel::{ConstantInfo, ConstantKind, Name};

use super::lean_v2_extensions::{lean_quick_cmp, standard_extensions};
use super::{LeanV2RegionWriter, LeanV2Value};
use crate::module::DefinitionSafety;
use crate::{OleanError, OleanHeader, OleanResult, TypedImport};

#[cfg(test)]
mod tests;

/// How a declaration appears to ordinary importers of a Lean module.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LeanV2Visibility {
    /// Only the private view contains the declaration.
    Private,
    /// The public and server views expose the full record.
    Exported,
    /// The public and server views carry an axiom with the same signature.
    ExportedAsAxiom,
}

/// One complete source declaration and the metadata used by the views.
pub struct LeanV2ModuleDeclaration<'a> {
    /// Checked kernel declaration.
    pub info: &'a ConstantInfo,
    /// Stored Lean definition safety.
    pub safety: DefinitionSafety,
    /// Ordered mutual names, empty for an axiom.
    pub all: &'a [Name],
    /// Public visibility of this record in a split module.
    pub visibility: LeanV2Visibility,
    /// Complete axiom dependencies for an exported declaration.
    pub axioms: &'a [Name],
}

/// Module-level layout and native metadata.
pub struct LeanV2ModuleOptions<'a> {
    /// Whether to generate all three declaration views.
    pub is_module: bool,
    /// Namespaces registered by this source module.
    pub namespaces: &'a [Name],
    /// Generate the IR pair for a module whose declarations have no code.
    pub emit_ir: bool,
}

/// The native artifacts produced from one checked module.
#[derive(Debug)]
pub struct LeanV2ModuleParts {
    /// The base `.olean` file.
    pub base: Vec<u8>,
    /// The optional `.olean.server` file.
    pub server: Option<Vec<u8>>,
    /// The optional `.olean.private` file.
    pub private: Option<Vec<u8>>,
    /// The optional `.ir.sig` file.
    pub ir_signature: Option<Vec<u8>>,
    /// The optional `.ir` file.
    pub ir: Option<Vec<u8>>,
}

/// Serialize ordinary or split Lean 4.36 declaration records. The caller
/// supplies checked values and the source module's visibility and metadata.
/// # Errors
/// Refuses malformed records, unsupported native layouts, and IR output for
/// a declaration that needs executable code.
pub fn write_lean_v2_module(
    target: &OleanHeader,
    module: &Name,
    imports: &[TypedImport],
    declarations: &[LeanV2ModuleDeclaration<'_>],
    options: LeanV2ModuleOptions<'_>,
) -> OleanResult<LeanV2ModuleParts> {
    let mut seen = HashSet::new();
    for row in declarations {
        if row.info.name.is_anon() || !seen.insert(&row.info.name) {
            return Err(invalid(format!(
                "invalid or duplicate declaration `{}`",
                row.info.name
            )));
        }
        if row.visibility == LeanV2Visibility::ExportedAsAxiom
            && row.info.kind == ConstantKind::Axiom
        {
            return Err(invalid(format!(
                "axiom `{}` cannot be weakened",
                row.info.name
            )));
        }
    }
    let ir = match (options.is_module, options.emit_ir) {
        (true, true) => {
            if let Some(row) = declarations.iter().find(|row| {
                matches!(
                    row.info.kind,
                    ConstantKind::Definition | ConstantKind::Opaque
                )
            }) {
                return Err(invalid(format!(
                    "declaration `{}` requires an IR body",
                    row.info.name
                )));
            }
            Some(write_no_code_ir(target, module, imports)?)
        }
        (false, true) => return Err(invalid("ordinary files have no separate IR parts")),
        (_, false) => None,
    };
    let mut writer = LeanV2RegionWriter::for_module(target, module)?;
    let mut exported: Vec<_> = declarations
        .iter()
        .filter(|row| !options.is_module || row.visibility != LeanV2Visibility::Private)
        .collect();
    exported.sort_by(|a, b| lean_quick_cmp(&a.info.name, &b.info.name));
    let originals: Vec<_> = exported
        .iter()
        .filter(|row| options.is_module && row.visibility == LeanV2Visibility::ExportedAsAxiom)
        .map(|row| (&row.info.name, row.info.kind))
        .collect();
    let axioms: Vec<_> = exported
        .iter()
        .map(|row| (&row.info.name, row.axioms))
        .collect();
    let mut entries = standard_extensions(&mut writer, options.namespaces, &originals, &axioms)?;
    entries.push(write_no_package(&mut writer)?);
    let none = LeanV2Value::scalar(0)?;
    entries.push(write_extension(
        &mut writer,
        &Name::anon().str("Lean").str("deprecatedModuleExt"),
        &[none],
    )?);

    if !options.is_module {
        let (names, values) = write_records(&mut writer, declarations.iter(), false)?;
        return Ok(LeanV2ModuleParts {
            base: writer.finish_ordinary_module(imports, &names, &values, &[], &entries)?,
            server: None,
            private: None,
            ir_signature: None,
            ir: None,
        });
    }

    let (public_names, public_values) = write_records(&mut writer, exported.into_iter(), true)?;
    let base = writer.finish_split_part(imports, &public_names, &public_values, &entries)?;
    let server = writer.finish_split_part(imports, &public_names, &public_values, &entries)?;
    let (private_names, private_values) = write_records(&mut writer, declarations.iter(), false)?;
    let private = writer.finish_module_view(imports, &private_names, &private_values, &entries)?;
    let (signature, body) = ir.unzip();
    Ok(LeanV2ModuleParts {
        base,
        server: Some(server),
        private: Some(private),
        ir_signature: signature,
        ir: body,
    })
}

fn write_records<'a, 'b>(
    writer: &mut LeanV2RegionWriter,
    rows: impl Iterator<Item = &'a LeanV2ModuleDeclaration<'b>>,
    weaken: bool,
) -> OleanResult<(Vec<Name>, Vec<LeanV2Value>)>
where
    'b: 'a,
{
    let mut names = Vec::new();
    let mut values = Vec::new();
    for row in rows {
        names.push(row.info.name.clone());
        let value = if weaken && row.visibility == LeanV2Visibility::ExportedAsAxiom {
            let mut stub = row.info.clone();
            stub.kind = ConstantKind::Axiom;
            stub.value = None;
            let safety = match row.safety {
                DefinitionSafety::Safe => DefinitionSafety::Safe,
                DefinitionSafety::Unsafe | DefinitionSafety::Partial => DefinitionSafety::Unsafe,
            };
            writer.write_constant_info(&stub, safety)?
        } else {
            writer.write_constant_info_with_group(row.info, row.safety, row.all)?
        };
        values.push(value);
    }
    Ok((names, values))
}

fn write_no_code_ir(
    target: &OleanHeader,
    module: &Name,
    imports: &[TypedImport],
) -> OleanResult<(Vec<u8>, Vec<u8>)> {
    let mut ir = LeanV2RegionWriter::for_module(target, &module.clone().str("ir"))?;
    let signature = ir.finish_ir_signature()?;
    let entries = [
        write_extension(
            &mut ir,
            &Name::anon().str("Lean").str("IR").str("declMapExt"),
            &[],
        )?,
        write_extension(
            &mut ir,
            &Name::anon().str("Lean").str("regularInitAttr"),
            &[],
        )?,
        write_no_package(&mut ir)?,
    ];
    let body = ir.finish_module_view(imports, &[], &[], &entries)?;
    Ok((signature, body))
}

fn write_no_package(writer: &mut LeanV2RegionWriter) -> OleanResult<LeanV2Value> {
    let name = Name::anon()
        .str("_private")
        .str("Lean")
        .str("Compiler")
        .str("ModPkgExt")
        .num(0)
        .str("Lean")
        .str("modPkgExt");
    write_extension(writer, &name, &[LeanV2Value::scalar(0)?])
}

fn write_extension(
    writer: &mut LeanV2RegionWriter,
    name: &Name,
    rows: &[LeanV2Value],
) -> OleanResult<LeanV2Value> {
    let name = writer.write_name(name)?;
    let rows = writer.write_array(rows)?;
    writer.write_constructor(0, &[name, rows], &[])
}

fn invalid(detail: impl Into<String>) -> OleanError {
    OleanError::Region(detail.into())
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The two ownership arrays consumed by Lean 4.36 `finalizeImport` for a
//! source outside the module system. Compiler-generated closed constants
//! occur only in the selected IR's extraConstNames.

use super::decode::IrLayout;
use super::module_ir::check_companion_layout;
use crate::import::{assemble_load_part, read_typed_name_array};
use crate::region::{CompactedRegion, TypedModuleLayout};
use crate::{CapturedModuleBytes, OleanError, OleanResult, TypedImport};
use clean_kernel::Name;
use std::path::Path;
use std::sync::Arc;

/// Share ownership and content checks between native consumers of one loaded module.
/// The captured bytes and typed module name both come from the same import callback.
pub struct CapturedPrivateNativeModule<'a, 'b> {
    pub(super) name: &'a Name,
    pub(super) parts: CapturedModuleBytes<'b>,
    owners: std::cell::OnceCell<Option<PrivateOwners>>,
    digest: std::cell::OnceCell<[u8; 32]>,
}

impl<'a, 'b> CapturedPrivateNativeModule<'a, 'b> {
    /// Wrap an immutable module during its checked import.
    pub fn new(name: &'a Name, parts: CapturedModuleBytes<'b>) -> Self {
        Self {
            name,
            parts,
            owners: Default::default(),
            digest: Default::default(),
        }
    }

    fn inventory(&self) -> Option<&PrivateOwners> {
        self.owners
            .get_or_init(|| private_native_owners(self.name, self.parts).ok())
            .as_ref()
    }

    pub(super) fn owners(&self) -> Option<&[Name]> {
        Some(&self.inventory()?.names)
    }

    pub(super) fn phase_imports(&self) -> Option<&NativeImportHeaders> {
        self.inventory()?.imports.as_ref()
    }

    /// Ownership of the public ModuleData seen by a source in the module system.
    pub(super) fn public_owners(&self) -> OleanResult<Vec<Name>> {
        let p = self.parts;
        let base = check_companion_layout(self.name, p.canonical_path, p.base, IrLayout::Lean436)
            .map_err(|e| OleanError::Region(e.to_string()))?;
        let data = CompactedRegion::new(p.base, base.base_addr);
        let root = data.root_ptr()?;
        let mut names = field_names(&data, root, 1)?;
        names.extend(field_names(&data, root, 3)?);
        Ok(names)
    }

    pub(super) fn digest(&self) -> [u8; 32] {
        *self
            .digest
            .get_or_init(|| selected_module_digest(self.parts))
    }
}

struct PrivateOwners {
    names: Vec<Name>,
    imports: Option<NativeImportHeaders>,
}

/// Direct import arrays from the parts Lean can select as its main ModuleData.
#[derive(Clone)]
pub(super) struct NativeImportHeaders {
    pub(super) is_module: bool,
    pub(super) public: Arc<[TypedImport]>,
    pub(super) private: Arc<[TypedImport]>,
    pub(super) ir: Option<Arc<[TypedImport]>>,
}

/// Read the kernel names and generated IR names from the same captured parts
/// that a Lean 4.36 private import uses to assign each name's originating module.
///
/// # Errors
/// Refuses incompatible headers, incomplete selected parts and invalid inventories.
fn private_native_owners(
    module: &Name,
    captured: CapturedModuleBytes<'_>,
) -> OleanResult<PrivateOwners> {
    if captured.ir_signature.is_some() != captured.ir.is_some() {
        return Err(OleanError::Region(format!(
            "incomplete stable IR companion pair for {module}"
        )));
    }
    let path = captured.canonical_path;
    let check = |part: &Path, bytes: &[u8]| {
        check_companion_layout(module, part, bytes, IrLayout::Lean436)
            .map_err(|e| OleanError::Region(e.to_string()))
    };
    let base = check(path, captured.base)?;
    let region = CompactedRegion::new(captured.base, base.base_addr);
    let root = region.root_ptr()?;
    let is_module = module_flag(&region, root)?;
    let private = if is_module {
        let server = captured
            .server
            .ok_or_else(|| missing(module, ".olean.server"))?;
        let private = captured
            .private
            .ok_or_else(|| missing(module, ".olean.private"))?;
        check(&path.with_extension("olean.server"), server)?;
        check(&path.with_extension("olean.private"), private)?;
        Some(assemble_load_part(captured.base, Some(server), private)?)
    } else {
        None
    };
    let main = private
        .as_ref()
        .map(|part| CompactedRegion::new(&part.bytes, part.base_addr));
    let main = main.as_ref().unwrap_or(&region);
    let main_root = private.as_ref().map_or(root, |part| part.root_ptr);
    if module_flag(main, main_root)? != is_module {
        return Err(OleanError::Region(format!(
            "inconsistent module flag for {module}"
        )));
    }
    // The checked loader walks the base header. Lean's non-module importer
    // walks the selected private header, with importAll forced for every edge.
    // Only use this walk for code when it names the same modules in order.
    let imports = |region: &CompactedRegion<'_>, root| -> OleanResult<Vec<TypedImport>> {
        let offset = region.ptr_to_offset(root)?;
        region.read_typed_import_array(region.read_u64_at(offset + 8)?)
    };
    let public = imports(&region, root);
    let headers = if is_module {
        let public = public?;
        let private = imports(main, main_root)?;
        if !public
            .iter()
            .map(|i| &i.module_name)
            .eq(private.iter().map(|i| &i.module_name))
        {
            return Err(OleanError::Region(format!(
                "private import graph for {module} differs from its base header"
            )));
        }
        Some((Arc::from(public), Arc::from(private)))
    } else {
        // An unreadable legacy import array cannot authorize a phase path.
        public.ok().map(|imports| {
            let public = Arc::<[TypedImport]>::from(imports);
            (Arc::clone(&public), public)
        })
    };
    let mut names = field_names(main, main_root, 1)?;
    // None on the outside means an unreadable header. A missing companion pair
    // is valid and leaves no main ModuleData when only IR was requested.
    let mut ir_imports = Some(None);
    let extra = match captured.ir_signature {
        Some(sig) => {
            check(&path.with_extension("ir.sig"), sig)?;
            let ir = captured.ir.ok_or_else(|| missing(module, ".ir"))?;
            check(&path.with_extension("ir"), ir)?;
            let part = assemble_load_part(sig, None, ir);
            ir_imports = part.as_ref().ok().and_then(|part| {
                let data = CompactedRegion::new(&part.bytes, part.base_addr);
                imports(&data, part.root_ptr)
                    .ok()
                    .map(|edges| Some(Arc::from(edges)))
            });
            if is_module {
                let part = part?;
                let data = CompactedRegion::new(&part.bytes, part.base_addr);
                if !module_flag(&data, part.root_ptr)? {
                    return Err(OleanError::Region(format!(
                        "inconsistent IR module flag for {module}"
                    )));
                }
                field_names(&data, part.root_ptr, 3)?
            } else {
                field_names(main, main_root, 3)?
            }
        }
        None => field_names(main, main_root, 3)?,
    };
    names.extend(extra);
    Ok(PrivateOwners {
        names,
        imports: headers
            .zip(ir_imports)
            .map(|((public, private), ir)| NativeImportHeaders {
                is_module,
                public,
                private,
                ir,
            }),
    })
}

fn module_flag(region: &CompactedRegion<'_>, root: u64) -> OleanResult<bool> {
    if region.typed_module_layout_at(root)? != TypedModuleLayout::LeanV2 {
        return Err(OleanError::Region("expected stable ModuleData".to_owned()));
    }
    let offset = region.ptr_to_offset(root)?;
    match region.bytes_at(offset + 48, 1)?[0] {
        0 => Ok(false),
        1 => Ok(true),
        _ => Err(OleanError::Region("invalid stable module flag".to_owned())),
    }
}

pub(super) fn field_names(
    region: &CompactedRegion<'_>,
    root: u64,
    field: usize,
) -> OleanResult<Vec<Name>> {
    let offset = region.ptr_to_offset(root)?;
    let pointer = region.read_u64_at(offset + 8 + 8 * field)?;
    let (names, valid) = read_typed_name_array(region, pointer)?;
    if !valid {
        return Err(OleanError::Region(
            "invalid stable native name inventory".to_owned(),
        ));
    }
    Ok(names)
}

fn missing(module: &Name, suffix: &str) -> OleanError {
    OleanError::Region(format!("missing captured {suffix} for {module}"))
}

/// Five original stable SDK parts of Init.Prelude.
pub(super) const STABLE_PRELUDE_DIGEST: [u8; 32] = [
    0x77, 0xa6, 0x27, 0x54, 0xc6, 0xa9, 0xe7, 0x63, 0x7e, 0x00, 0x55, 0x9f, 0xcc, 0x00, 0x5a, 0xee,
    0xc7, 0x12, 0xe6, 0x86, 0xf9, 0xa8, 0xc4, 0x25, 0xbf, 0xa9, 0x48, 0xa1, 0x00, 0x2c, 0x49, 0xea,
];

/// Length-delimited identity of the original five private-import parts.
pub(super) fn selected_module_digest(capture: CapturedModuleBytes<'_>) -> [u8; 32] {
    use sha2::{Digest, Sha256};
    let mut hash = Sha256::new();
    hash.update(b"Clean captured stable native module\0");
    for part in [
        Some(capture.base),
        capture.server,
        capture.private,
        capture.ir_signature,
        capture.ir,
    ] {
        if let Some(bytes) = part {
            hash.update((bytes.len() as u64).to_le_bytes());
            hash.update(bytes);
        } else {
            hash.update(u64::MAX.to_le_bytes());
        }
    }
    hash.finalize().into()
}

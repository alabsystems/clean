// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! One module's compiled IR, read from exactly the files Lean's own import
//! would read.
//!
//! Lean v4.30 writes a module's IR in two places (`writeModule`,
//! `Lean/Environment.lean`):
//!
//! * the `Lean.IR.declMapExt` entries of the module data. For a
//!   `module`-system file the extension's `exportEntriesFnEx`
//!   (`Lean/Compiler/IR/CompilerM.lean`) keeps the `meta` closure with bodies
//!   and turns every other public declaration into an opaque `extern`; a
//!   non-`module` file keeps everything;
//! * for a `module`-system file only, a separate `.ir` file
//!   (`saveModuleData (fname.withExtension "ir") … (mkIRData env)`) whose
//!   entries are `exportIREntries`: every IR declaration, the
//!   `regularInitAttr` entries and `modPkgExt`.
//!
//! Which of those an importer SEES depends on the import. This reader
//! reproduces the root-level `private` import that a non-`module` file (such
//! as the census oracle) performs — `importModulesCore` with
//! `globalLevel := .private`, where every module is `importAll`:
//!
//! * the MAIN data (`ImportedModule.mainModule?` → `getData? .private`) is the
//!   `.olean.private` part of a `module` — assembled over its `.olean` and
//!   `.olean.server`, since `saveModuleDataParts` shares objects across parts —
//!   and the `.olean` of a non-`module` file;
//! * the INTERPRETER data (`ImportedModule.interpData? .private`) is the `.ir`
//!   file of a `module` and the main data again for a non-`module` file. A
//!   `.ir` beside a non-`module` file is still header-checked: Lean's
//!   `loadIR?` reads it, and a bad header fails the import, before
//!   `interpData?` sets it aside.
//!
//! A part Lean would require and cannot find is an error here too, never a
//! fallback: Lean's `finalizeImport` throws `missing data file` /
//! `missing IR data file` in exactly those cases.

use std::path::{Path, PathBuf};

use super::decode::IrDecoder;
use super::error::{LeanIrError, LeanIrResult};
use super::types::{Decl, ExternAttrData};
use crate::header::OleanHeader;
use crate::region::{is_ptr, CompactedRegion, TypedModuleLayout};
#[cfg(any(test, feature = "cli"))]
use clean_kernel::name::NameInner;
use clean_kernel::Name;

/// `Lean.IR.declMapExt`'s persisted name.
pub(crate) const DECL_MAP_EXT: &str = "Lean.IR.declMapExt";
/// `Lean.externAttr`'s persisted name.
pub(crate) const EXTERN_ATTR_EXT: &str = "Lean.externAttr";
/// `Lean.Compiler.implementedByAttr`'s persisted name.
pub(crate) const IMPLEMENTED_BY_EXT: &str = "Lean.Compiler.implementedByAttr";
/// `Lean.regularInitAttr`'s persisted name (`@[init]`).
pub(crate) const REGULAR_INIT_EXT: &str = "Lean.regularInitAttr";
/// `Lean.builtinInitAttr`'s persisted name (`@[builtin_init]`).
pub(crate) const BUILTIN_INIT_EXT: &str = "Lean.builtinInitAttr";

/// The only Lean version whose IR object layout this decoder has been
/// measured against. Any other version is refused: the IR types change
/// between releases (`IRType.struct` gained its `leanTypeName`, `Decl` lost
/// `ExternAttrData.arity?`), and a layout guess would decode garbage.
pub(crate) const MEASURED_LEAN_VERSION: &str = clean_kernel::LeanWorld::ORACLE.version();

/// Bound on one extension's entry array.
const MAX_ENTRIES: usize = 1 << 24;

/// Where a module's main data came from.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum MainSource {
    /// The `.olean` of a non-`module` file.
    Olean,
    /// The `.olean.private` part of a `module` file.
    OleanPrivate,
}

/// Where a module's interpreter data came from.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum InterpSource {
    /// The `.ir` file of a `module` file.
    IrFile,
    /// The main data (a non-`module` file; any `.ir` beside it is only header-checked).
    MainData,
}

/// Immutable file population captured by a checked import. An absent optional
/// file remains absent for every later lazy IR judgement; filesystem changes
/// cannot add a new input after the caller authenticated this population.
#[derive(Clone, Debug)]
pub(crate) struct CapturedIrInput {
    pub(crate) base: std::sync::Arc<[u8]>,
    pub(crate) server: Option<std::sync::Arc<[u8]>>,
    pub(crate) private: Option<std::sync::Arc<[u8]>>,
    pub(crate) ir: Option<std::sync::Arc<[u8]>>,
}

fn read_input(
    module: &Name,
    olean: &Path,
    path: &Path,
    captured: Option<&CapturedIrInput>,
) -> LeanIrResult<Vec<u8>> {
    let Some(captured) = captured else {
        return read_file(module, path);
    };
    let bytes = if path == olean {
        Some(captured.base.as_ref())
    } else if path == add_extension(olean, "server") {
        captured.server.as_deref()
    } else if path == add_extension(olean, "private") {
        captured.private.as_deref()
    } else if path == olean.with_extension("ir") {
        captured.ir.as_deref()
    } else {
        None
    };
    bytes
        .map(<[u8]>::to_vec)
        .ok_or_else(|| LeanIrError::MissingFile {
            module: super::format::name_to_string(module),
            path: path.to_path_buf(),
            detail: "file is absent from the checked captured artifact".to_owned(),
        })
}

/// A module's decoded IR and IR-related attribute entries. The census reads
/// every field; `.olean` import's late-binding judgement reads only
/// [`Self::ir_decls`], so a build without the `cli` feature reads the others
/// nowhere.
#[derive(Debug, Clone)]
#[cfg_attr(not(any(feature = "cli", test)), allow(dead_code))]
pub(crate) struct ModuleIr {
    /// The module's name.
    pub(crate) module: Name,
    /// Whether the module participates in the module system.
    pub(crate) is_module: bool,
    /// Source of [`Self::olean_decls`] and the attribute entries.
    pub(crate) main_source: MainSource,
    /// Source of [`Self::ir_decls`].
    pub(crate) interp_source: InterpSource,
    /// `declMapExt` entries of the main data (`getModuleEntries`).
    pub(crate) olean_decls: Vec<Decl>,
    /// `declMapExt` entries of the `.ir` file; `None` when the interpreter
    /// data IS the main data.
    ir_file_decls: Option<Vec<Decl>>,
    /// `externAttr` entries of the main data.
    pub(crate) extern_attr: Vec<(Name, ExternAttrData)>,
    /// `implementedByAttr` entries of the main data.
    pub(crate) implemented_by: Vec<(Name, Name)>,
    /// `regularInitAttr` entries of the main data.
    pub(crate) regular_init: Vec<(Name, Name)>,
    /// `regularInitAttr` entries of the `.ir` file (see `ir_file_decls`).
    ir_file_regular_init: Option<Vec<(Name, Name)>>,
    /// `builtinInitAttr` entries of the main data.
    pub(crate) builtin_init: Vec<(Name, Name)>,
    /// Deepest join-point/`case` nesting decoded in this module.
    pub(crate) max_nesting: usize,
}

impl ModuleIr {
    /// `declMapExt` entries of the interpreter data (`getModuleIREntries`).
    #[must_use]
    pub(crate) fn ir_decls(&self) -> &[Decl] {
        self.ir_file_decls.as_deref().unwrap_or(&self.olean_decls)
    }

    /// `regularInitAttr` entries of the interpreter data.
    #[cfg(any(test, feature = "cli"))]
    #[must_use]
    pub(crate) fn regular_init_ir(&self) -> &[(Name, Name)] {
        self.ir_file_regular_init
            .as_deref()
            .unwrap_or(&self.regular_init)
    }
}

/// The `entries` field of one `ModuleData`, by extension name.
pub(crate) struct PartEntries {
    pub(crate) is_module: bool,
    pub(crate) entries: Vec<(Name, u64)>,
}

impl PartEntries {
    pub(crate) fn get(&self, extension: &str) -> Option<u64> {
        self.entries
            .iter()
            .find(|(name, _)| name_is(name, extension))
            .map(|(_, pointer)| *pointer)
    }
}

/// Whether a typed `Name` is the string-component name spelled `dotted`
/// (extension names are ordinary identifiers, never quoted or numeric).
fn name_is(name: &Name, dotted: &str) -> bool {
    *name
        == dotted
            .split('.')
            .fold(Name::anon(), |parent, component| parent.str(component))
}

fn read_file(module: &Name, path: &Path) -> LeanIrResult<Vec<u8>> {
    std::fs::read(path).map_err(|e| LeanIrError::MissingFile {
        module: super::format::name_to_string(module),
        path: path.to_path_buf(),
        detail: e.to_string(),
    })
}

fn module_err(module: &Name, detail: impl Into<String>) -> LeanIrError {
    LeanIrError::Module {
        module: super::format::name_to_string(module),
        detail: detail.into(),
    }
}

/// Refuse a file whose Lean version is not [`MEASURED_LEAN_VERSION`].
fn check_version(module: &Name, path: &Path, bytes: &[u8]) -> LeanIrResult<OleanHeader> {
    let header = OleanHeader::parse(bytes)?;
    if header.lean_version.as_deref() != Some(MEASURED_LEAN_VERSION) {
        return Err(module_err(
            module,
            format!(
                "{} was written by Lean {:?}; the IR layout is measured only for {MEASURED_LEAN_VERSION}",
                path.display(),
                header.lean_version
            ),
        ));
    }
    Ok(header)
}

impl CompactedRegion<'_> {
    /// Read the `isModule` flag and the extension-entry table of the
    /// `ModuleData` at `root` (Lean v4.30 layout: five object fields then the
    /// `isModule` scalar).
    pub(crate) fn ir_part_entries(&self, root: u64) -> LeanIrResult<PartEntries> {
        if self.typed_module_layout_at(root)? != TypedModuleLayout::LeanV2 {
            return Err(LeanIrError::layout(
                "ModuleData",
                root,
                "IR decoding requires the Lean v4.30 ModuleData layout",
            ));
        }
        let offset = self.ptr_to_offset(root)?;
        let is_module = match self.bytes_at(offset + 48, 1)?[0] {
            0 => false,
            1 => true,
            other => {
                return Err(LeanIrError::layout(
                    "ModuleData",
                    root,
                    format!("isModule scalar {other} is neither 0 nor 1"),
                ))
            }
        };
        let decoder = IrDecoder::new(self);
        let table = self.read_u64_at(offset + 8 + 8 * 4)?;
        let mut entries: Vec<(Name, u64)> = Vec::new();
        for pair in decoder.array(table, "ModuleData.entries", MAX_ENTRIES)? {
            if !is_ptr(pair) {
                return Err(LeanIrError::layout(
                    "ModuleData.entries",
                    pair,
                    "entry is not a pair object",
                ));
            }
            let at = self.ptr_to_offset(pair)?;
            let header = self.read_header_at(at)?;
            if (header.rc, header.tag, header.other, header.cs_sz) != (0, 0, 2, 24) {
                return Err(LeanIrError::layout(
                    "ModuleData.entries",
                    pair,
                    "entry is not a `Name × Array EnvExtensionEntry` pair",
                ));
            }
            let name = self.read_kernel_name_ptr(self.read_u64_at(at + 8)?)?;
            let array = self.read_u64_at(at + 16)?;
            if entries.iter().any(|(seen, _)| *seen == name) {
                return Err(LeanIrError::layout(
                    "ModuleData.entries",
                    pair,
                    format!(
                        "extension {} listed twice",
                        super::format::name_to_string(&name)
                    ),
                ));
            }
            entries.push((name, array));
        }
        Ok(PartEntries { is_module, entries })
    }
}

/// The decoded payload of one part (main data or `.ir` file).
struct PartIr {
    decls: Vec<Decl>,
    extern_attr: Vec<(Name, ExternAttrData)>,
    implemented_by: Vec<(Name, Name)>,
    regular_init: Vec<(Name, Name)>,
    builtin_init: Vec<(Name, Name)>,
    max_nesting: usize,
}

fn decode_part(region: &CompactedRegion<'_>, part: &PartEntries) -> LeanIrResult<PartIr> {
    let mut decoder = IrDecoder::new(region);
    let mut decls = Vec::new();
    if let Some(array) = part.get(DECL_MAP_EXT) {
        for (index, pointer) in decoder
            .array(array, DECL_MAP_EXT, MAX_ENTRIES)?
            .into_iter()
            .enumerate()
        {
            let decl = decoder
                .decl(pointer)
                .map_err(|source| LeanIrError::InDecl {
                    index,
                    name: decoder
                        .decl_name(pointer)
                        .map_or_else(|| "?".to_owned(), |n| super::format::name_to_string(&n)),
                    extension: DECL_MAP_EXT,
                    source: Box::new(source),
                })?;
            decls.push(decl);
        }
    }
    let pairs = |extension: &'static str| -> LeanIrResult<Vec<(Name, Name)>> {
        match part.get(extension) {
            None => Ok(Vec::new()),
            Some(array) => decoder
                .array(array, extension, MAX_ENTRIES)?
                .into_iter()
                .map(|p| decoder.name_pair(p))
                .collect(),
        }
    };
    let implemented_by = pairs(IMPLEMENTED_BY_EXT)?;
    let regular_init = pairs(REGULAR_INIT_EXT)?;
    let builtin_init = pairs(BUILTIN_INIT_EXT)?;
    let extern_attr = match part.get(EXTERN_ATTR_EXT) {
        None => Vec::new(),
        Some(array) => decoder
            .array(array, EXTERN_ATTR_EXT, MAX_ENTRIES)?
            .into_iter()
            .map(|p| decoder.extern_pair(p))
            .collect::<LeanIrResult<Vec<_>>>()?,
    };
    Ok(PartIr {
        decls,
        extern_attr,
        implemented_by,
        regular_init,
        builtin_init,
        max_nesting: decoder.max_depth_seen,
    })
}

/// `X.olean` → `X.olean.<suffix>` (`OLeanLevel.adjustFileName`).
fn add_extension(path: &Path, suffix: &str) -> PathBuf {
    let mut os = path.as_os_str().to_owned();
    os.push(".");
    os.push(suffix);
    PathBuf::from(os)
}

/// The root component of a module name, as `mod.getRoot.toString (escape :=
/// false)` spells it.
#[cfg(any(test, feature = "cli"))]
fn root_package(module: &Name) -> Option<&str> {
    let mut current = module;
    loop {
        match current.inner() {
            NameInner::Str(parent, s) if parent.is_anon() => return Some(&**s),
            NameInner::Str(parent, _) | NameInner::Num(parent, _) => current = parent,
            NameInner::Anon => return None,
        }
    }
}

/// Resolve a module name to its base `.olean` exactly as Lean's `findOLean`
/// does (`Lean/Util/Path.lean`, `SearchPath.findWithExt`): the FIRST
/// search-path entry holding a directory named after the module's root
/// component, or a `<root>.olean` file, decides where the module must be. A
/// later entry is never consulted, and a module file absent from the chosen
/// entry is refused, as `findOLeanParts` throws `object file … does not exist`.
///
/// Measured against the pinned toolchain: with `LEAN_PATH=A:B`, an empty
/// `A/IrAdv/` directory and the module at `B/IrAdv.olean`, `import IrAdv` is
/// refused; the file-level first-hit rule this used to delegate to
/// (`resolve_typed_module_path`) read `B/IrAdv.olean` and printed a census.
#[cfg(any(test, feature = "cli"))]
pub(crate) fn find_module_ir_olean(
    module: &Name,
    search_paths: &[PathBuf],
) -> LeanIrResult<PathBuf> {
    let not_found = || LeanIrError::ModuleNotFound {
        module: super::format::name_to_string(module),
        searched: search_paths.len(),
    };
    let relative = crate::import::typed_module_rel_path(module).map_err(|_| not_found())?;
    let root = root_package(module).ok_or_else(not_found)?;
    let chosen = search_paths
        .iter()
        .find(|dir| dir.join(root).is_dir() || dir.join(format!("{root}.olean")).exists())
        .ok_or_else(not_found)?;
    let olean = chosen.join(relative);
    if !olean.exists() {
        return Err(LeanIrError::MissingFile {
            module: super::format::name_to_string(module),
            path: olean,
            detail: "object file does not exist in the first search-path entry holding the \
                     module's root package (Lean's `findOLean` never looks further)"
                .to_owned(),
        });
    }
    Ok(olean)
}

/// Load and decode one module's compiled IR from its resolved base `.olean`,
/// as a root-level `private` import sees it (see the module documentation).
///
/// # Errors
///
/// Refuses when a file Lean would read is missing, a file was written by a
/// Lean version other than [`MEASURED_LEAN_VERSION`], or any object fails to
/// decode.
pub(crate) fn load_module_ir_at(module: &Name, olean: &Path) -> LeanIrResult<ModuleIr> {
    load_module_ir_from(module, olean, None)
}

pub(crate) fn load_module_ir_captured(
    module: &Name,
    olean: &Path,
    captured: &CapturedIrInput,
) -> LeanIrResult<ModuleIr> {
    load_module_ir_from(module, olean, Some(captured))
}

fn load_module_ir_from(
    module: &Name,
    olean: &Path,
    captured: Option<&CapturedIrInput>,
) -> LeanIrResult<ModuleIr> {
    let base_bytes = read_input(module, olean, olean, captured)?;
    let base_header = check_version(module, olean, &base_bytes)?;
    let base = CompactedRegion::new(&base_bytes, base_header.base_addr);
    let base_root = base.root_ptr()?;
    let base_part = base.ir_part_entries(base_root)?;

    // Main data: `.olean.private` (over `.olean` + `.olean.server`) for a
    // `module`, else the `.olean` itself.
    let (main_source, main) = if base_part.is_module {
        let server_path = add_extension(olean, "server");
        let private_path = add_extension(olean, "private");
        let server_bytes = read_input(module, olean, &server_path, captured)?;
        let private_bytes = read_input(module, olean, &private_path, captured)?;
        check_version(module, &server_path, &server_bytes)?;
        check_version(module, &private_path, &private_bytes)?;
        let assembled = crate::import::assemble_incremental_part(
            &base_bytes,
            Some(&server_bytes),
            &private_bytes,
        )?;
        let region = CompactedRegion::new(&assembled.bytes, assembled.base_addr);
        let part = region.ir_part_entries(assembled.root_ptr)?;
        if !part.is_module {
            return Err(module_err(
                module,
                "the .olean says `module` but its .olean.private does not",
            ));
        }
        (MainSource::OleanPrivate, decode_part(&region, &part)?)
    } else {
        (MainSource::Olean, decode_part(&base, &base_part)?)
    };

    // Interpreter data: the `.ir` file of a `module`, else the main data.
    let (interp_source, ir) = if base_part.is_module {
        let ir_path = olean.with_extension("ir");
        let ir_bytes = read_input(module, olean, &ir_path, captured)?;
        let ir_header = check_version(module, &ir_path, &ir_bytes)?;
        let region = CompactedRegion::new(&ir_bytes, ir_header.base_addr);
        let part = region.ir_part_entries(region.root_ptr()?)?;
        if !part.is_module {
            return Err(module_err(
                module,
                "the .olean says `module` but its .ir does not",
            ));
        }
        (InterpSource::IrFile, Some(decode_part(&region, &part)?))
    } else {
        // Lean's `loadIR?` (`importModulesCore`, `Lean/Environment.lean`) reads
        // a `.ir` beside ANY module's `.olean` when one exists, before
        // `interpData?` decides that a non-`module` file's interpreter data is
        // its main data; a `.ir` whose header does not read fails the whole
        // import (`failed to read file …, invalid header`, measured with the
        // pinned toolchain on a non-`module` fixture). So a present `.ir` is
        // header-checked here too and then, as in Lean, not used.
        let ir_path = olean.with_extension("ir");
        if captured.map_or_else(|| ir_path.exists(), |input| input.ir.is_some()) {
            let ir_bytes = read_input(module, olean, &ir_path, captured)?;
            check_version(module, &ir_path, &ir_bytes)?;
        }
        (InterpSource::MainData, None)
    };

    let max_nesting = main
        .max_nesting
        .max(ir.as_ref().map_or(0, |part| part.max_nesting));
    let (ir_file_decls, ir_file_regular_init) = match ir {
        Some(part) => (Some(part.decls), Some(part.regular_init)),
        None => (None, None),
    };
    Ok(ModuleIr {
        module: module.clone(),
        is_module: base_part.is_module,
        main_source,
        interp_source,
        olean_decls: main.decls,
        ir_file_decls,
        extern_attr: main.extern_attr,
        implemented_by: main.implemented_by,
        regular_init: main.regular_init,
        ir_file_regular_init,
        builtin_init: main.builtin_init,
        max_nesting,
    })
}

/// The names of the declarations Lean compiled IR for in `module`: the
/// `declMapExt` entries of its interpreter data (the `.ir` file of a
/// `module`, which holds every IR declaration, private ones included; the
/// `.olean` of any other file), read for their names only. `.olean` import
/// reads it to tell whether a bound declaration was compiled
/// (`import::late_binding`).
///
/// # Errors
///
/// As [`load_module_ir_at`]: a missing or unreadable file, another Lean
/// version, or a row that is not a `Decl`.
pub(crate) fn load_module_ir_names_at(module: &Name, olean: &Path) -> LeanIrResult<Vec<Name>> {
    load_module_ir_names_from(module, olean, None)
}

pub(crate) fn load_module_ir_names_captured(
    module: &Name,
    olean: &Path,
    captured: &CapturedIrInput,
) -> LeanIrResult<Vec<Name>> {
    load_module_ir_names_from(module, olean, Some(captured))
}

fn load_module_ir_names_from(
    module: &Name,
    olean: &Path,
    captured: Option<&CapturedIrInput>,
) -> LeanIrResult<Vec<Name>> {
    let base_bytes = read_input(module, olean, olean, captured)?;
    let base_header = check_version(module, olean, &base_bytes)?;
    let base = CompactedRegion::new(&base_bytes, base_header.base_addr);
    let base_part = base.ir_part_entries(base.root_ptr()?)?;
    if !base_part.is_module {
        return decl_names(module, &base, &base_part);
    }
    let ir_path = olean.with_extension("ir");
    let ir_bytes = read_input(module, olean, &ir_path, captured)?;
    let ir_header = check_version(module, &ir_path, &ir_bytes)?;
    let region = CompactedRegion::new(&ir_bytes, ir_header.base_addr);
    let part = region.ir_part_entries(region.root_ptr()?)?;
    if !part.is_module {
        return Err(module_err(
            module,
            "the .olean says `module` but its .ir does not",
        ));
    }
    decl_names(module, &region, &part)
}

/// The `declMapExt` declaration names of one part.
fn decl_names(
    module: &Name,
    region: &CompactedRegion<'_>,
    part: &PartEntries,
) -> LeanIrResult<Vec<Name>> {
    let decoder = IrDecoder::new(region);
    let Some(array) = part.get(DECL_MAP_EXT) else {
        return Ok(Vec::new());
    };
    decoder
        .array(array, DECL_MAP_EXT, MAX_ENTRIES)?
        .into_iter()
        .enumerate()
        .map(|(index, pointer)| {
            decoder.decl_name(pointer).ok_or_else(|| {
                module_err(
                    module,
                    format!("{DECL_MAP_EXT} entry {index} is not a named `Decl`"),
                )
            })
        })
        .collect()
}

/// Read a module's direct imports only (for closure walks), from its base
/// `.olean`. Lean's `ModuleData.imports` is the header's import list at every
/// level (`mkModuleData` copies `env.header`), so the base part suffices.
///
/// # Errors
///
/// Refuses an unreadable base file or one written by another Lean version.
#[cfg(any(test, feature = "cli"))]
pub(crate) fn read_module_imports(module: &Name, olean: &Path) -> LeanIrResult<Vec<Name>> {
    let bytes = read_file(module, olean)?;
    check_version(module, olean, &bytes)?;
    Ok(crate::import::parse_typed_imports(&bytes)?
        .into_iter()
        .map(|import| import.module_name)
        .collect())
}

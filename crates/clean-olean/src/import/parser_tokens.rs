// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tokens contributed by the compiled parser extensions visible to a source file.
use super::load_parse::assemble_load_part;
use super::module_cache_direct::{read_required_part, CaptureBudget};
use super::{resolve_typed_module_path_in_world, ImportError, TypedImport, TypedImportFlags};
use crate::lean_ir::module_ir::PartEntries;
use crate::region::CompactedRegion;
use crate::{OleanError, OleanHeader, OleanResult};
use clean_kernel::{LeanWorld, Name};
use std::collections::HashSet;
use std::path::{Path, PathBuf};

/// One literal reserved globally or when the given namespace is active.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ParserToken {
    pub scope: Option<Name>,
    pub text: String,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Visibility {
    Public,
    All,
    Legacy,
}

impl Visibility {
    fn dependency(self, import: &TypedImport) -> OleanResult<Option<Self>> {
        let TypedImportFlags::LeanV2 {
            import_all,
            is_exported,
            ..
        } = import.flags
        else {
            return Err(OleanError::Region(
                "stable parser imports require Lean v2 flags".into(),
            ));
        };
        Ok(match self {
            Self::Legacy => Some(Self::Legacy),
            Self::Public if !is_exported => None,
            Self::All if import_all => Some(Self::All),
            _ => Some(Self::Public),
        })
    }
}

struct ModuleSyntax {
    imports: Vec<TypedImport>,
    tokens: Vec<ParserToken>,
}

fn syntax(
    region: &CompactedRegion<'_>,
    root: u64,
    entries: PartEntries,
) -> OleanResult<ModuleSyntax> {
    let offset = region.ptr_to_offset(root)?;
    let imports = region.read_typed_import_array(region.read_u64_at(offset + 8)?)?;
    let tokens = match entries.get("Lean.Parser.parserExtension") {
        Some(array) => region.stable_parser_tokens(array)?,
        None => Vec::new(),
    };
    Ok(ModuleSyntax { imports, tokens })
}

fn from_file(
    path: &Path,
    mode: Visibility,
    direct: bool,
    budget: &mut CaptureBudget,
) -> Result<ModuleSyntax, ImportError> {
    let file_error = |source| ImportError::FileParse {
        path: path.to_owned(),
        source,
    };
    let bytes = read_required_part(path, budget)?;
    super::world_gate::check_part_world(&path.display().to_string(), &bytes, LeanWorld::Lean436)?;
    let header = OleanHeader::parse(&bytes).map_err(file_error)?;
    if header.lean_version_str() != Some(LeanWorld::Lean436.version()) {
        return Err(file_error(OleanError::Region(format!(
            "expected Lean {}, found {:?}",
            LeanWorld::Lean436.version(),
            header.lean_version
        ))));
    }
    let base = CompactedRegion::new(&bytes, header.base_addr);
    let root = base.root_ptr().map_err(file_error)?;
    let entries = base
        .ir_part_entries(root)
        .map_err(|e| file_error(OleanError::Region(e.to_string())))?;
    if direct && mode != Visibility::Legacy && !entries.is_module {
        return Err(file_error(OleanError::Region(
            "cannot import a non-module from a module".into(),
        )));
    }
    if mode == Visibility::Public || !entries.is_module {
        return syntax(&base, root, entries).map_err(file_error);
    }
    let private_path = path.with_extension("olean.private");
    let server = read_required_part(&path.with_extension("olean.server"), budget)?;
    let private = read_required_part(&private_path, budget)?;
    let part_error = |source| ImportError::FileParse {
        path: private_path.clone(),
        source,
    };
    let part = assemble_load_part(&bytes, Some(&server), &private).map_err(part_error)?;
    let region = CompactedRegion::new(&part.bytes, part.base_addr);
    let entries = region
        .ir_part_entries(part.root_ptr)
        .map_err(|e| part_error(OleanError::Region(e.to_string())))?;
    syntax(&region, part.root_ptr, entries).map_err(part_error)
}

/// Collect the parser tokens visible inside a stable Lean source file. Root
/// imports include implicit Init when appropriate. Each Boolean is importAll.
/// A private import still contributes at its own use site. Its visibility to
/// a consumer of that module is determined by the flags in the compiled file.
///
/// # Errors
/// Returns the selected artifact's path on a failed read or a malformed part.
pub fn stable_imported_parser_tokens(
    roots: impl IntoIterator<Item = (Name, bool)>,
    is_module: bool,
    search_paths: &[PathBuf],
) -> Result<HashSet<ParserToken>, ImportError> {
    let mut pending: Vec<_> = roots
        .into_iter()
        .map(|(module, all)| {
            let mode = if !is_module {
                Visibility::Legacy
            } else if all {
                Visibility::All
            } else {
                Visibility::Public
            };
            (module, mode, true)
        })
        .collect();
    let mut budget = CaptureBudget::default();
    let mut seen = HashSet::new();
    let mut tokens = HashSet::new();
    // Process direct selectors first so an already visited dependency cannot
    // hide the non-module check on a later direct import.
    let mut next = Vec::new();
    while !pending.is_empty() {
        for (module, mode, direct) in pending.drain(..) {
            if !seen.insert((module.clone(), mode)) {
                continue;
            }
            let path = resolve_typed_module_path_in_world(
                &module,
                search_paths,
                Some(LeanWorld::Lean436.tag()),
            )?;
            let part = from_file(&path, mode, direct, &mut budget)?;
            tokens.extend(part.tokens);
            for import in part.imports {
                if let Some(child) = mode.dependency(&import)? {
                    next.push((import.module_name, child, false));
                }
            }
        }
        std::mem::swap(&mut pending, &mut next);
    }
    Ok(tokens)
}

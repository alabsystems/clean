// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Content-bound cache for production typed loading. ParsedModule is a legacy
//! display projection and is never used to reconstruct a cached declaration.

use super::load_parse::assemble_load_part;
use super::load_parse::{parse_load_module, parse_load_module_incremental, LoadModule};
use super::typed_imports::{typed_import_count, typed_import_count_from_region};
use super::{ImportError, ModuleCache, MAX_MODULE_CACHE_ENTRIES};
use std::path::{Path, PathBuf};
use std::sync::Arc;

mod capture;
pub(super) use capture::CaptureBudget;
pub use capture::ModuleCaptureLimits;

#[derive(Clone, PartialEq, Eq)]
struct PartIdentity {
    bytes: usize,
    digest: blake3::Hash,
}

impl PartIdentity {
    fn of(bytes: &[u8]) -> Self {
        Self {
            bytes: bytes.len(),
            digest: blake3::hash(bytes),
        }
    }
}

#[derive(Clone, PartialEq, Eq)]
struct ModuleIdentity {
    base: PartIdentity,
    server: Option<PartIdentity>,
    private: Option<PartIdentity>,
    // Unchecked legacy capture versus checked absence/content are distinct.
    captured_ir: Option<Option<PartIdentity>>,
}

/// One captured population: optional means absent on disk, never unreadable or
/// malformed. Every cache lookup reads and hashes all three paths, including
/// dependencies of an incremental companion; mtime is not a semantic identity.
pub(super) struct CapturedModule {
    pub(super) path: PathBuf,
    pub(super) base: Vec<u8>,
    pub(super) server: Option<Vec<u8>>,
    pub(super) private: Option<Vec<u8>>,
    pub(super) captured_ir: Option<Option<Vec<u8>>>,
    identity: ModuleIdentity,
}

pub(super) struct DirectModule {
    pub(super) base: LoadModule,
    pub(super) server: Option<LoadModule>,
    pub(super) private: Option<LoadModule>,
    identity: ModuleIdentity,
}

pub(super) fn read_optional(path: &Path) -> Result<Option<Vec<u8>>, ImportError> {
    capture::optional(path, &mut CaptureBudget::default())
}

impl CapturedModule {
    /// Charge every present root the actual Load decoder will materialize,
    /// including cumulative companion import rows that are not graph edges.
    /// Ordinary loaders do not install this additional caller policy.
    pub(super) fn charge_import_rows(&self, budget: &mut CaptureBudget) -> Result<(), ImportError> {
        let count = typed_import_count(&self.base).map_err(|source| ImportError::FileParse {
            path: self.path.clone(),
            source,
        })?;
        budget.imports(count)?;
        for (server, bytes, extension) in [
            (None, self.server.as_deref(), "olean.server"),
            (
                self.server.as_deref(),
                self.private.as_deref(),
                "olean.private",
            ),
        ] {
            if let Some(bytes) = bytes {
                let count = (|| {
                    let part = assemble_load_part(&self.base, server, bytes)?;
                    let region = crate::region::CompactedRegion::new(&part.bytes, part.base_addr);
                    typed_import_count_from_region(&region, part.root_ptr)
                })()
                .map_err(|source| ImportError::FileParse {
                    path: self.path.with_extension(extension),
                    source,
                })?;
                budget.imports(count)?;
            }
        }
        Ok(())
    }

    #[cfg(test)]
    pub(super) fn read(path: &Path) -> Result<Self, ImportError> {
        Self::read_with_budget(path, &mut CaptureBudget::default())
    }

    pub(super) fn read_with_budget(
        path: &Path,
        budget: &mut CaptureBudget,
    ) -> Result<Self, ImportError> {
        let canonical =
            std::fs::canonicalize(path).map_err(|source| ImportError::FileUnreadable {
                path: path.to_path_buf(),
                source,
            })?;
        let base = capture::required(path, budget)?;
        let server = capture::optional(&path.with_extension("olean.server"), budget)?;
        let private = capture::optional(&path.with_extension("olean.private"), budget)?;
        let identity = ModuleIdentity {
            base: PartIdentity::of(&base),
            server: server.as_deref().map(PartIdentity::of),
            private: private.as_deref().map(PartIdentity::of),
            captured_ir: None,
        };
        Ok(Self {
            path: canonical,
            base,
            server,
            private,
            captured_ir: None,
            identity,
        })
    }

    /// Freeze every extra input a later lazy compiled-IR judgement may read.
    /// Ordinary public loaders never call this and retain their old behavior.
    #[cfg(test)]
    pub(super) fn capture_ir(self, resolved: &Path) -> Result<Self, ImportError> {
        self.capture_ir_with_budget(resolved, &mut CaptureBudget::default())
    }

    pub(super) fn capture_ir_with_budget(
        mut self,
        resolved: &Path,
        budget: &mut CaptureBudget,
    ) -> Result<Self, ImportError> {
        let ir = capture::optional(&resolved.with_extension("ir"), budget)?;
        self.identity.captured_ir = Some(ir.as_deref().map(PartIdentity::of));
        self.captured_ir = Some(ir);
        Ok(self)
    }

    pub(super) fn parse(self) -> Result<DirectModule, ImportError> {
        let captured_ir = self.captured_ir.as_ref().map(|ir| {
            Arc::new(crate::lean_ir::module_ir::CapturedIrInput {
                base: Arc::from(self.base.as_slice()),
                server: self.server.as_deref().map(Arc::from),
                private: self.private.as_deref().map(Arc::from),
                ir: ir.as_deref().map(Arc::from),
            })
        });
        // Parse every present part before the bundle can enter the cache or an
        // Environment. A bad companion cannot become an apparently good base.
        let server = self
            .server
            .as_ref()
            .map(|bytes| parse_load_module_incremental(&self.base, None, bytes.clone()))
            .transpose()
            .map_err(|source| ImportError::FileParse {
                path: self.path.with_extension("olean.server"),
                source,
            })?;
        let private = self
            .private
            .map(|bytes| parse_load_module_incremental(&self.base, self.server.as_deref(), bytes))
            .transpose()
            .map_err(|source| ImportError::FileParse {
                path: self.path.with_extension("olean.private"),
                source,
            })?;
        let base = parse_load_module(self.base).map_err(|source| ImportError::FileParse {
            path: self.path.clone(),
            source,
        })?;
        let (mut base, mut server, mut private) = (
            base.read_from(&self.path),
            server.map(|part| part.read_from(&self.path)),
            private.map(|part| part.read_from(&self.path)),
        );
        base.captured_ir = captured_ir.clone();
        if let Some(part) = server.as_mut() {
            part.captured_ir = captured_ir.clone();
        }
        if let Some(part) = private.as_mut() {
            part.captured_ir = captured_ir;
        }
        Ok(DirectModule {
            base,
            server,
            private,
            identity: self.identity,
        })
    }
}

impl ModuleCache {
    pub(super) fn get_direct(&self, captured: &CapturedModule) -> Option<Arc<DirectModule>> {
        let key = captured.path.clone();
        let mut entries = self.entries.write().unwrap_or_else(|e| e.into_inner());
        match entries.get(&key) {
            Some(module) if module.identity == captured.identity => Some(Arc::clone(module)),
            Some(_) => {
                entries.remove(&key);
                None
            }
            None => None,
        }
    }

    pub(super) fn insert_direct(&self, path: PathBuf, module: DirectModule) -> Arc<DirectModule> {
        let module = Arc::new(module);
        let mut entries = self.entries.write().unwrap_or_else(|e| e.into_inner());
        if entries.len() >= MAX_MODULE_CACHE_ENTRIES {
            let keys: Vec<_> = entries.keys().take(entries.len() / 4).cloned().collect();
            for key in keys {
                entries.remove(&key);
            }
        }
        entries.insert(path, Arc::clone(&module));
        module
    }
}

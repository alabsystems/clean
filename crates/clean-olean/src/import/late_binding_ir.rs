// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The compiled IR a late-binding judgement reads (`super`), loaded from
//! beside a module's `.olean` once and only when a judgement needs it.

use std::collections::HashSet;
use std::path::{Path, PathBuf};

use clean_kernel::name::Name;

use crate::lean_ir::module_ir::{
    load_module_ir_at, load_module_ir_captured, load_module_ir_names_at,
    load_module_ir_names_captured, CapturedIrInput, ModuleIr,
};

/// A module's compiled IR, read from beside its `.olean` the first time it is
/// needed; `None` when it cannot be read (no file path, a missing file,
/// another Lean version). A `module`'s `.olean.server` / `.olean.private`
/// part reads the IR of its base `.olean` (and that file's `.ir`).
pub(super) struct IrSource {
    module: Option<Name>,
    olean: Option<PathBuf>,
    captured: Option<std::sync::Arc<CapturedIrInput>>,
    names: Option<Option<HashSet<Name>>>,
    bodies: Option<Option<ModuleIr>>,
}

impl IrSource {
    pub(super) fn new(
        module: Option<&str>,
        olean: Option<&Path>,
        captured: Option<std::sync::Arc<CapturedIrInput>>,
    ) -> Self {
        let module = module.map(|label| {
            let base = label
                .strip_suffix("._server")
                .or_else(|| label.strip_suffix("._private"))
                .unwrap_or(label);
            Name::from_string(base)
        });
        let olean = olean.map(|path| {
            let text = path.to_string_lossy();
            match text
                .strip_suffix(".server")
                .or_else(|| text.strip_suffix(".private"))
            {
                Some(base) if base.ends_with(".olean") => PathBuf::from(base),
                _ => path.to_path_buf(),
            }
        });
        Self {
            module,
            olean,
            captured,
            names: None,
            bodies: None,
        }
    }

    pub(super) fn names(&mut self) -> Option<&HashSet<Name>> {
        if self.names.is_none() {
            let read = match (&self.module, &self.olean) {
                (Some(module), Some(olean)) => self
                    .captured
                    .as_ref()
                    .map_or_else(
                        || load_module_ir_names_at(module, olean),
                        |captured| load_module_ir_names_captured(module, olean, captured),
                    )
                    .map_err(|error| tracing::debug!(%error, "module IR names unreadable"))
                    .ok()
                    .map(|names| names.into_iter().collect()),
                _ => None,
            };
            self.names = Some(read);
        }
        self.names.as_ref().and_then(Option::as_ref)
    }

    pub(super) fn bodies(&mut self) -> Option<&ModuleIr> {
        if self.bodies.is_none() {
            let read = match (&self.module, &self.olean) {
                (Some(module), Some(olean)) => self
                    .captured
                    .as_ref()
                    .map_or_else(
                        || load_module_ir_at(module, olean),
                        |captured| load_module_ir_captured(module, olean, captured),
                    )
                    .map_err(|error| tracing::debug!(%error, "module IR unreadable"))
                    .ok(),
                _ => None,
            };
            self.bodies = Some(read);
        }
        self.bodies.as_ref().and_then(Option::as_ref)
    }
}

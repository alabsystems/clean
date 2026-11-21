// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The environment a workspace module elaborates over.
//!
//! Lean elaborates every module whose header is not `prelude` over an
//! implicit `import Init` of the toolchain that builds it, and records `Init`
//! as that module's first import. `clean lake build` used to elaborate every
//! module over Clean's bootstrap prelude instead, so its artifacts cited
//! bootstrap `Eq`/`Nonempty`/`Iff` records that are not Lean's, and an
//! importer whose citation base is genuine `Init.Core` refused them
//! (`docs/DECISIONS.md`, 2026-11-15 K1 entries).
//!
//! The world comes from the rule `clean check` uses
//! ([`clean_olean::source_world_for_file`]): the project's `lean-toolchain`,
//! or the checkout's pin. Its genuine Init is loaded over the bare backbone
//! by the module driver's [`SourceModuleSetup`], and the module's cited
//! closure is re-admitted over [`foundation_import_base`], the citation base
//! `clean check` gives a genuine-Init consumer. A recent world's `prelude`
//! module begins with the same bare kernel environment as the checker.
//! Refused projects get the bootstrap prelude and search only their built
//! workspace dependencies.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

use clean_elab::module_driver::{foundation_import_base, EnvironmentSetup, SourceModuleSetup};
use clean_kernel::Environment;
use clean_olean::{ImportedConeGate, SourceWorldDecision};
use clean_parser::{FileHeader, Parser};

/// The grammar, header and artifact roots of one workspace module.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ModuleWorld {
    pub(crate) decision: SourceWorldDecision,
    header: FileHeader,
    pub(crate) stdlib_search_paths: Vec<PathBuf>,
}

impl ModuleWorld {
    /// Select the world of the module at `source` whose text is `content`.
    pub(crate) fn of(source: &Path, content: &str) -> Result<Self, String> {
        let decision = clean_olean::source_world_for_file(source, None)
            .map_err(|error| format!("cannot select the module's Lean world: {error}"))?;
        let header = Parser::parse_header_in_world(content, decision.world())
            .map_err(|error| format!("invalid module header: {error}"))?;
        let stdlib_search_paths = decision
            .imports()
            .map_or_else(|_| Vec::new(), clean_olean::search_paths_in_world);
        Ok(Self {
            decision,
            header,
            stdlib_search_paths,
        })
    }

    pub(crate) fn imports(&self) -> impl Iterator<Item = String> + '_ {
        self.header
            .imports
            .iter()
            .map(|import| import.module.name().to_string())
    }

    /// Whether the module implicitly imports genuine Init.
    pub(crate) fn imports_init(&self) -> bool {
        !self.header.is_prelude && self.decision.imports().is_ok()
    }
}

/// One world's genuine Init environment and citation base, built once per
/// process for the exact Init files it was loaded from, and cloned for every
/// module of that world.
#[derive(Debug)]
pub(crate) struct GenuineInit {
    decision: SourceWorldDecision,
    /// The digest of every part of every module of Init's closure, as the
    /// module's build trace records it: a rewritten Init is another key.
    files: BTreeMap<String, String>,
    environment: Environment,
    citation_base: ImportedConeGate,
}

impl GenuineInit {
    /// A fresh copy of genuine Init, before any of the module's own imports.
    pub(crate) fn environment(&self) -> Environment {
        self.environment.clone()
    }

    /// Genuine Init itself, the base of [`Self::environment`]'s copies.
    pub(crate) fn environment_ref(&self) -> &Environment {
        &self.environment
    }

    /// The pre-import citation base: the world's foundations re-admitted by
    /// the reference kernel, never a post-Init snapshot.
    pub(crate) fn citation_base(&self) -> ImportedConeGate {
        self.citation_base.clone()
    }
}

/// The Init closure's entries of a build trace's toolchain digests.
pub(crate) fn init_files(stdlib: &BTreeMap<String, String>) -> BTreeMap<String, String> {
    stdlib
        .iter()
        .filter(|(module, _)| *module == "Init" || module.starts_with("Init."))
        .map(|(module, digest)| (module.clone(), digest.clone()))
        .collect()
}

/// Every genuine Init this process has loaded. Loading and checking Init is
/// the dominant cost of a module's build, so every build of the process
/// (and every in-process test) shares it; the lock also keeps concurrent
/// builds from loading the same Init side by side.
static GENUINE_INIT: Mutex<Vec<Arc<GenuineInit>>> = Mutex::new(Vec::new());

/// `decision`'s genuine Init, read from the files `files` digests, loading
/// it on first use.
pub(crate) fn genuine_init(
    decision: &SourceWorldDecision,
    files: &BTreeMap<String, String>,
) -> Result<Arc<GenuineInit>, String> {
    let mut worlds = GENUINE_INIT.lock().unwrap_or_else(|e| e.into_inner());
    if let Some(found) = worlds
        .iter()
        .find(|w| &w.decision == decision && &w.files == files)
    {
        return Ok(Arc::clone(found));
    }
    let setup = EnvironmentSetup::default();
    let mut source = SourceModuleSetup::new(setup, decision).map_err(|e| e.to_string())?;
    let environment = clean_kernel::tc::with_declaration_budget_suspended(|| {
        source.initial_environment(&FileHeader::default())
    })
    .map_err(|e| e.to_string())?;
    let citation_base = foundation_import_base(decision).map_err(|e| e.to_string())?;
    let built = Arc::new(GenuineInit {
        decision: decision.clone(),
        files: files.clone(),
        environment,
        citation_base,
    });
    // An Init rewritten under a running process replaces its old entry.
    worlds.retain(|w| &w.decision != decision);
    worlds.push(Arc::clone(&built));
    Ok(built)
}

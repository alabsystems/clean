// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Test-only fixture discovery and pin comparison/writing. The digest engine
//! is the production `clean_olean::meaning_digest` implementation.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use clean_kernel::Name;
use clean_olean::{read_artifact, ArtifactDepth};
use serde::Serialize;

#[allow(unused_imports)] // each qualification target uses its own API subset
pub(crate) use clean_olean::meaning_digest::{MeaningDigests, MeaningError};

/// Set to `1`, a failing comparison also writes the measured committed pins.
pub(crate) const REPIN_VARIABLE: &str = "CLEAN_REPIN_STATEMENT_PINS";

/// Fixture discovery around the production package inventory.
pub(crate) struct Package(clean_olean::meaning_digest::Package);

impl std::ops::Deref for Package {
    type Target = clean_olean::meaning_digest::Package;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Package {
    /// The package of a fixture family: the theories its `ORDER` compiles,
    /// which must be exactly `theories` (in order) and be all the family
    /// compiles. Each theory's modules are its own `ORDER`'s stems, and the
    /// package's names are what each module's `.olean` in `compiled` declares.
    #[allow(dead_code)] // the mutation controls load single modules, not a fixture's theories
    pub(crate) fn of_fixture(compiled: &Path, family: &str, theories: &[&str]) -> Self {
        let order_path = clean_olean::test_support::fixture_root()
            .join(family)
            .join("ORDER");
        let order = std::fs::read_to_string(&order_path)
            .unwrap_or_else(|error| panic!("read {}: {error}", order_path.display()));
        let compiles: Vec<&str> = order_lines(&order).collect();
        let named: Vec<String> = theories.iter().map(|t| format!("theory {t}")).collect();
        assert_eq!(
            compiles,
            named.iter().map(String::as_str).collect::<Vec<_>>(),
            "the package of fixture family {family} is the theories its ORDER compiles, and it \
             compiles nothing else"
        );
        let theories_root = workspace_root().join("theories");
        let modules: Vec<String> = theories
            .iter()
            .flat_map(|theory| {
                let path = theories_root.join(theory).join("ORDER");
                let text = std::fs::read_to_string(&path)
                    .unwrap_or_else(|error| panic!("read {}: {error}", path.display()));
                order_lines(&text)
                    .map(|stem| stem.replace('/', "."))
                    .collect::<Vec<_>>()
            })
            .collect();
        Self::of_modules(compiled, modules)
    }

    /// An explicit inventory for a constructed-environment control.
    #[allow(dead_code)]
    pub(crate) fn of_names(names: BTreeSet<Name>) -> Self {
        Self(clean_olean::meaning_digest::Package::of_names(names))
    }

    /// Discover names from each module's own artifact, preserving the exact
    /// module order and repeated-declaration accounting in the production API.
    pub(crate) fn of_modules(compiled: &Path, modules: Vec<String>) -> Self {
        Self(clean_olean::meaning_digest::Package::of_module_names(
            modules.into_iter().map(|module| {
                let path = compiled.join(format!("{}.olean", module.replace('.', "/")));
                let artifact = read_artifact(&module, &path, ArtifactDepth::Names)
                    .unwrap_or_else(|error| panic!("read {}: {error}", path.display()));
                (module, artifact.names)
            }),
        ))
    }
}

/// An `ORDER` file's steps: trimmed, without blank lines and `#` comments.
fn order_lines(text: &str) -> impl Iterator<Item = &str> {
    text.lines()
        .map(str::trim)
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
}

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// The measured pins equal the committed ones; otherwise the failure names
/// the changed, unpinned and unmeasured keys and where the measurement went
/// ([`record_measured`]).
#[allow(dead_code)] // cic_l_level compares through its own typed refusal
pub(crate) fn check_pins(
    measured: &BTreeMap<String, String>,
    committed: &BTreeMap<String, String>,
    pin_file: &str,
) -> Result<(), String> {
    if measured == committed {
        return Ok(());
    }
    let changed: Vec<&String> = measured
        .iter()
        .filter(|(pin, digest)| committed.get(*pin).is_some_and(|c| c != *digest))
        .map(|(pin, _)| pin)
        .collect();
    let unpinned: Vec<&String> = measured
        .keys()
        .filter(|pin| !committed.contains_key(*pin))
        .collect();
    let unmeasured: Vec<&String> = committed
        .keys()
        .filter(|pin| !measured.contains_key(*pin))
        .collect();
    Err(format!(
        "observed statements differ from {pin_file}: meaning changed {changed:?}; measured \
         with no pin {unpinned:?}; pinned and not measured {unmeasured:?}\n{}",
        record_measured(measured, pin_file)
    ))
}

/// Where a failing pin comparison leaves what it measured. With
/// [`REPIN_VARIABLE`]`=1` that is the committed `pin_file` (relative to the
/// workspace root), rewritten in the committed format; otherwise a file under
/// the test's own temporary directory. Returns the sentence the failure
/// prints. Either way the run is a failure.
pub(crate) fn record_measured<T: Serialize>(
    measured: &BTreeMap<String, T>,
    pin_file: &str,
) -> String {
    let mut text = serde_json::to_string_pretty(measured).expect("render the pins");
    text.push('\n');
    let repin = std::env::var(REPIN_VARIABLE).is_ok_and(|value| value == "1");
    let path = if repin {
        workspace_root().join(pin_file)
    } else {
        let flat = pin_file.replace('/', "__");
        Path::new(env!("CARGO_TARGET_TMPDIR")).join(flat)
    };
    match std::fs::write(&path, text) {
        Ok(()) if repin => format!(
            "re-pinned {pin_file} ({} pins) from this run; it still fails: rebuild and run the \
             test again without {REPIN_VARIABLE} to confirm, and record the move in \
             docs/DECISIONS.md",
            measured.len()
        ),
        Ok(()) => format!(
            "the measured pins are at {}; re-pin by running the test with {REPIN_VARIABLE}=1",
            path.display()
        ),
        Err(error) => format!(
            "the measured pins were not written to {}: {error}",
            path.display()
        ),
    }
}

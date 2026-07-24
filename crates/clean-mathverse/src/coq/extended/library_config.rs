// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Library-specific configuration for the Coq extended importer.
//!
//! Each Coq ecosystem library (stdlib, MathComp, Flocq, CompCert, etc.) has
//! different import characteristics: expected theorem counts, axiom profiles,
//! phased import ordering, and module inclusion/exclusion lists.
//!
//! Preset configs are provided for the four target libraries. Custom configs
//! can be built with [`CoqLibraryConfigBuilder`].

use std::path::PathBuf;

use serde::{Deserialize, Serialize};

use crate::types::AxiomProfile;

/// Import phase for phased rollout.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ImportPhase {
    /// Core logic and datatypes (Init, Bool, Nat, List).
    Core = 0,
    /// Arithmetic and number theory (ZArith, QArith, Reals).
    Arithmetic = 1,
    /// Algebra and algebraic structures (MathComp ssralg, etc.).
    Algebra = 2,
    /// Analysis, topology, floating-point (Flocq, Coquelicot).
    Analysis = 3,
    /// Everything else (full library import).
    Full = 4,
}

impl ImportPhase {
    /// All phases in order.
    pub const ALL: &'static [ImportPhase] = &[
        ImportPhase::Core,
        ImportPhase::Arithmetic,
        ImportPhase::Algebra,
        ImportPhase::Analysis,
        ImportPhase::Full,
    ];
}

/// Configuration for importing a specific Coq library.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CoqLibraryConfig {
    /// Human-readable library name (e.g., "mathcomp").
    pub name: String,
    /// Directory containing SerAPI `.sexp` dumps for this library.
    pub sexp_dir: PathBuf,
    /// Default axiom profile bits for declarations from this library.
    pub default_axiom_profile: AxiomProfile,
    /// Approximate expected theorem count (for progress reporting).
    pub expected_theorems: usize,
    /// Module prefixes to include per phase. If empty, all modules are
    /// included in that phase.
    pub phase_modules: Vec<PhaseModuleSet>,
    /// Module prefixes to always exclude (e.g., extraction, testing modules).
    pub exclude_prefixes: Vec<String>,
}

/// Module inclusion set for one import phase.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PhaseModuleSet {
    pub phase: ImportPhase,
    /// Module prefixes included in this phase. Empty means "all remaining".
    pub include_prefixes: Vec<String>,
}

impl CoqLibraryConfig {
    /// Check whether a module path is included in the given phase.
    #[must_use]
    pub fn is_included(&self, module_path: &str, phase: ImportPhase) -> bool {
        // Always exclude blacklisted prefixes.
        if self
            .exclude_prefixes
            .iter()
            .any(|p| module_path.starts_with(p.as_str()))
        {
            return false;
        }

        // Find the phase module set.
        for pms in &self.phase_modules {
            if pms.phase == phase {
                if pms.include_prefixes.is_empty() {
                    return true; // empty = include all
                }
                return pms
                    .include_prefixes
                    .iter()
                    .any(|p| module_path.starts_with(p.as_str()));
            }
        }

        // If no phase config exists, only include in Full phase.
        phase == ImportPhase::Full
    }

    /// Return the phases that include the given module path, in order.
    #[must_use]
    pub fn phases_for_module(&self, module_path: &str) -> Vec<ImportPhase> {
        ImportPhase::ALL
            .iter()
            .copied()
            .filter(|&p| self.is_included(module_path, p))
            .collect()
    }
}

// ---- Preset configurations -------------------------------------------------

/// Coq standard library configuration.
#[must_use]
pub fn coq_stdlib_config(sexp_dir: PathBuf) -> CoqLibraryConfig {
    CoqLibraryConfig {
        name: "coq-stdlib".to_owned(),
        sexp_dir,
        default_axiom_profile: AxiomProfile::NONE,
        expected_theorems: 15_000,
        phase_modules: vec![
            PhaseModuleSet {
                phase: ImportPhase::Core,
                include_prefixes: vec![
                    "Coq.Init.".into(),
                    "Coq.Bool.".into(),
                    "Coq.Arith.".into(),
                    "Coq.Lists.".into(),
                    "Coq.NArith.".into(),
                ],
            },
            PhaseModuleSet {
                phase: ImportPhase::Arithmetic,
                include_prefixes: vec![
                    "Coq.ZArith.".into(),
                    "Coq.QArith.".into(),
                    "Coq.Numbers.".into(),
                    "Coq.PArith.".into(),
                ],
            },
            PhaseModuleSet {
                phase: ImportPhase::Algebra,
                include_prefixes: vec![
                    "Coq.Structures.".into(),
                    "Coq.Classes.".into(),
                    "Coq.Relations.".into(),
                    "Coq.Setoids.".into(),
                ],
            },
            PhaseModuleSet {
                phase: ImportPhase::Analysis,
                include_prefixes: vec!["Coq.Reals.".into(), "Coq.Floats.".into()],
            },
            PhaseModuleSet {
                phase: ImportPhase::Full,
                include_prefixes: vec![], // everything
            },
        ],
        exclude_prefixes: vec![
            "Coq.extraction.".into(),
            "Coq.ExtrOcaml".into(),
            "Coq.ExtrHaskell".into(),
        ],
    }
}

/// MathComp library configuration.
#[must_use]
pub fn mathcomp_config(sexp_dir: PathBuf) -> CoqLibraryConfig {
    CoqLibraryConfig {
        name: "mathcomp".to_owned(),
        sexp_dir,
        default_axiom_profile: AxiomProfile::CLASSICAL,
        expected_theorems: 50_000,
        phase_modules: vec![
            PhaseModuleSet {
                phase: ImportPhase::Core,
                include_prefixes: vec![
                    "mathcomp.ssreflect.".into(),
                    "mathcomp.ssrbool".into(),
                    "mathcomp.ssrnat".into(),
                    "mathcomp.ssrfun".into(),
                    "mathcomp.eqtype".into(),
                    "mathcomp.choice".into(),
                    "mathcomp.seq".into(),
                ],
            },
            PhaseModuleSet {
                phase: ImportPhase::Arithmetic,
                include_prefixes: vec![
                    "mathcomp.div".into(),
                    "mathcomp.prime".into(),
                    "mathcomp.binomial".into(),
                    "mathcomp.bigop".into(),
                    "mathcomp.fintype".into(),
                    "mathcomp.tuple".into(),
                    "mathcomp.finfun".into(),
                ],
            },
            PhaseModuleSet {
                phase: ImportPhase::Algebra,
                include_prefixes: vec!["mathcomp.algebra.".into(), "mathcomp.field.".into()],
            },
            PhaseModuleSet {
                phase: ImportPhase::Full,
                include_prefixes: vec![],
            },
        ],
        exclude_prefixes: vec!["mathcomp.test.".into(), "mathcomp.examples.".into()],
    }
}

/// Flocq floating-point library configuration.
#[must_use]
pub fn flocq_config(sexp_dir: PathBuf) -> CoqLibraryConfig {
    CoqLibraryConfig {
        name: "flocq".to_owned(),
        sexp_dir,
        default_axiom_profile: AxiomProfile::FLOAT_APPROX,
        expected_theorems: 3_000,
        phase_modules: vec![
            PhaseModuleSet {
                phase: ImportPhase::Core,
                include_prefixes: vec!["Flocq.Core.".into(), "Flocq.Definitions.".into()],
            },
            PhaseModuleSet {
                phase: ImportPhase::Arithmetic,
                include_prefixes: vec!["Flocq.Calc.".into(), "Flocq.Prop.".into()],
            },
            PhaseModuleSet {
                phase: ImportPhase::Analysis,
                include_prefixes: vec!["Flocq.IEEE754.".into(), "Flocq.Appli.".into()],
            },
            PhaseModuleSet {
                phase: ImportPhase::Full,
                include_prefixes: vec![],
            },
        ],
        exclude_prefixes: vec![],
    }
}

/// CompCert library configuration.
#[must_use]
pub fn compcert_config(sexp_dir: PathBuf) -> CoqLibraryConfig {
    CoqLibraryConfig {
        name: "compcert".to_owned(),
        sexp_dir,
        default_axiom_profile: AxiomProfile::AXIOMATIZED,
        expected_theorems: 30_000,
        phase_modules: vec![
            PhaseModuleSet {
                phase: ImportPhase::Core,
                include_prefixes: vec!["compcert.lib.".into(), "compcert.common.".into()],
            },
            PhaseModuleSet {
                phase: ImportPhase::Arithmetic,
                include_prefixes: vec!["compcert.cfrontend.".into(), "compcert.cparser.".into()],
            },
            PhaseModuleSet {
                phase: ImportPhase::Full,
                include_prefixes: vec![],
            },
        ],
        exclude_prefixes: vec!["compcert.extraction.".into(), "compcert.debug.".into()],
    }
}

// ---- Tests -----------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_coq_stdlib_core_phase() {
        let cfg = coq_stdlib_config(PathBuf::from("/tmp/coq-stdlib"));
        assert!(cfg.is_included("Coq.Init.Logic", ImportPhase::Core));
        assert!(cfg.is_included("Coq.Bool.Bool", ImportPhase::Core));
        assert!(!cfg.is_included("Coq.Reals.Rbase", ImportPhase::Core));
    }

    #[test]
    fn test_coq_stdlib_excludes_extraction() {
        let cfg = coq_stdlib_config(PathBuf::from("/tmp/coq-stdlib"));
        assert!(!cfg.is_included("Coq.extraction.OCaml", ImportPhase::Full));
        assert!(!cfg.is_included("Coq.ExtrOcamlBasic", ImportPhase::Full));
    }

    #[test]
    fn test_coq_stdlib_full_phase_includes_all() {
        let cfg = coq_stdlib_config(PathBuf::from("/tmp/coq-stdlib"));
        assert!(cfg.is_included("Coq.Strings.String", ImportPhase::Full));
        assert!(cfg.is_included("Coq.Reals.Rbase", ImportPhase::Full));
    }

    #[test]
    fn test_mathcomp_default_profile() {
        let cfg = mathcomp_config(PathBuf::from("/tmp/mathcomp"));
        assert!(cfg.default_axiom_profile.has(AxiomProfile::CLASSICAL));
    }

    #[test]
    fn test_flocq_default_profile() {
        let cfg = flocq_config(PathBuf::from("/tmp/flocq"));
        assert!(cfg.default_axiom_profile.has(AxiomProfile::FLOAT_APPROX));
    }

    #[test]
    fn test_phases_for_module() {
        let cfg = coq_stdlib_config(PathBuf::from("/tmp"));
        let phases = cfg.phases_for_module("Coq.Init.Logic");
        assert!(phases.contains(&ImportPhase::Core));
        assert!(phases.contains(&ImportPhase::Full));
        assert!(!phases.contains(&ImportPhase::Algebra));
    }

    #[test]
    fn test_compcert_excludes_debug() {
        let cfg = compcert_config(PathBuf::from("/tmp/compcert"));
        assert!(!cfg.is_included("compcert.debug.Foo", ImportPhase::Full));
    }

    #[test]
    fn test_import_phase_ordering() {
        assert!(ImportPhase::Core < ImportPhase::Arithmetic);
        assert!(ImportPhase::Arithmetic < ImportPhase::Algebra);
        assert!(ImportPhase::Algebra < ImportPhase::Analysis);
        assert!(ImportPhase::Analysis < ImportPhase::Full);
    }

    #[test]
    fn test_config_serialization_roundtrip() {
        let cfg = coq_stdlib_config(PathBuf::from("/tmp/test"));
        let json = serde_json::to_string(&cfg).expect("should serialize");
        let back: CoqLibraryConfig = serde_json::from_str(&json).expect("should deserialize");
        assert_eq!(back.name, cfg.name);
        assert_eq!(back.expected_theorems, cfg.expected_theorems);
    }
}

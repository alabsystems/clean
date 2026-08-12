// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Replace gamma-crown axioms with Lean 4 Init imported theorems.
//!
//! The gamma-crown NN verification pipeline assumes standard mathematical facts
//! (e.g., `Nat.add_comm`, `Nat.le_trans`) as axioms. This module loads those
//! theorems from the Lean 4 Init `.olean` modules — where they have kernel-verified
//! proof terms — and provides a mechanism to replace `Declaration::Axiom` entries
//! with `Declaration::Theorem` entries backed by real proofs.
//!
//! ## Axiom replacement workflow
//!
//! 1. Build an [`AxiomReplacementTable`] from a Lean 4 Init environment.
//! 2. For each gamma-crown axiom name, look up the matching Init theorem.
//! 3. If a match is found with a proof term, produce a `Declaration::Theorem`.
//! 4. Track replacement statistics for trust accounting.

use std::collections::HashMap;

use clean_kernel::env::Environment;
use clean_kernel::expr::Expr;
use clean_kernel::name::Name;

use super::mathlib_import::{
    find_lean_lib_path, find_mathlib_search_paths, load_init_modules, load_mathlib_modules,
};

// ---------------------------------------------------------------------------
// Axiom mapping table
// ---------------------------------------------------------------------------

/// A single axiom-to-theorem mapping entry.
#[derive(Clone, Debug)]
pub struct AxiomMapping {
    /// The gamma-crown axiom name (e.g., "nat_le_refl").
    pub axiom_name: &'static str,
    /// Candidate Lean 4 theorem names to search for, in priority order.
    pub lean_candidates: &'static [&'static str],
}

/// The canonical mapping from gamma-crown axiom names to Lean 4 Init theorems.
///
/// Each entry lists the gamma-crown axiom and the Lean 4 Init constant names
/// that could replace it. The first candidate found with a proof term wins.
pub fn gamma_crown_axiom_mappings() -> Vec<AxiomMapping> {
    vec![
        AxiomMapping {
            axiom_name: "mat_mul_assoc",
            lean_candidates: &["Matrix.mul_assoc"],
        },
        AxiomMapping {
            axiom_name: "nat_le_refl",
            lean_candidates: &["Nat.le_refl", "Nat.le.refl", "le_refl"],
        },
        AxiomMapping {
            axiom_name: "nat_le_trans",
            lean_candidates: &["Nat.le_trans", "Nat.le.step", "le_trans"],
        },
        AxiomMapping {
            axiom_name: "nat_le_antisymm",
            lean_candidates: &["Nat.le_antisymm", "le_antisymm"],
        },
        AxiomMapping {
            axiom_name: "add_comm",
            lean_candidates: &["Nat.add_comm", "Int.add_comm", "add_comm"],
        },
        AxiomMapping {
            axiom_name: "add_assoc",
            lean_candidates: &["Nat.add_assoc", "Int.add_assoc", "add_assoc"],
        },
        AxiomMapping {
            axiom_name: "mul_comm",
            lean_candidates: &["Nat.mul_comm", "Int.mul_comm", "mul_comm"],
        },
        AxiomMapping {
            axiom_name: "mul_assoc",
            lean_candidates: &["Nat.mul_assoc", "Int.mul_assoc", "mul_assoc"],
        },
        AxiomMapping {
            axiom_name: "add_zero",
            lean_candidates: &["Nat.add_zero", "Int.add_zero", "add_zero"],
        },
        AxiomMapping {
            axiom_name: "zero_add",
            lean_candidates: &["Nat.zero_add", "Int.zero_add", "zero_add"],
        },
        AxiomMapping {
            axiom_name: "mul_one",
            lean_candidates: &["Nat.mul_one", "Int.mul_one", "mul_one"],
        },
        AxiomMapping {
            axiom_name: "one_mul",
            lean_candidates: &["Nat.one_mul", "Int.one_mul", "one_mul"],
        },
    ]
}

/// Extended Mathlib axiom mappings for gamma-crown proofs.
///
/// These require Mathlib `.olean` files (not just Init). They map deeper
/// mathematical facts needed by specific gamma-crown conjectures:
///
/// - **Rat/Real field properties** (Category B axioms across all conjectures)
/// - **Matrix operations** (C010 zonotope_single_linear_eq, C003 spectral_norm)
/// - **Topology/Lipschitz** (C003 lip_product, compose_chain)
/// - **Order/lattice** (C007 merge_sound_helper, restrict_refines_helper)
/// - **Distribution/probability** (C029 pac_certification_bound)
pub fn mathlib_gamma_crown_axiom_mappings() -> Vec<AxiomMapping> {
    vec![
        // --- Rat field properties (Category B: trivial consequences) ---
        AxiomMapping {
            axiom_name: "rat_add_comm",
            lean_candidates: &["Rat.add_comm", "add_comm"],
        },
        AxiomMapping {
            axiom_name: "rat_add_assoc",
            lean_candidates: &["Rat.add_assoc", "add_assoc"],
        },
        AxiomMapping {
            axiom_name: "rat_mul_comm",
            lean_candidates: &["Rat.mul_comm", "mul_comm"],
        },
        AxiomMapping {
            axiom_name: "rat_mul_assoc",
            lean_candidates: &["Rat.mul_assoc", "mul_assoc"],
        },
        AxiomMapping {
            axiom_name: "rat_add_zero",
            lean_candidates: &["Rat.add_zero", "add_zero"],
        },
        AxiomMapping {
            axiom_name: "rat_zero_add",
            lean_candidates: &["Rat.zero_add", "zero_add"],
        },
        AxiomMapping {
            axiom_name: "rat_mul_one",
            lean_candidates: &["Rat.mul_one", "mul_one"],
        },
        AxiomMapping {
            axiom_name: "rat_one_mul",
            lean_candidates: &["Rat.one_mul", "one_mul"],
        },
        AxiomMapping {
            axiom_name: "rat_mul_inv_cancel",
            lean_candidates: &["Rat.mul_inv_cancel", "mul_inv_cancel", "div_mul_cancel"],
        },
        AxiomMapping {
            axiom_name: "rat_left_distrib",
            lean_candidates: &["Rat.mul_add", "mul_add", "left_distrib"],
        },
        AxiomMapping {
            axiom_name: "rat_right_distrib",
            lean_candidates: &["Rat.add_mul", "add_mul", "right_distrib"],
        },
        AxiomMapping {
            axiom_name: "rat_sub_self",
            lean_candidates: &["Rat.sub_self", "sub_self"],
        },
        AxiomMapping {
            axiom_name: "rat_neg_add_cancel",
            lean_candidates: &["Rat.neg_add_cancel", "neg_add_cancel", "neg_add_self"],
        },
        // --- Rat ordering (needed by interval arithmetic across conjectures) ---
        AxiomMapping {
            axiom_name: "rat_le_refl",
            lean_candidates: &["Rat.le_refl", "le_refl"],
        },
        AxiomMapping {
            axiom_name: "rat_le_trans",
            lean_candidates: &["Rat.le_trans", "le_trans"],
        },
        AxiomMapping {
            axiom_name: "rat_le_antisymm",
            lean_candidates: &["Rat.le_antisymm", "le_antisymm"],
        },
        AxiomMapping {
            axiom_name: "rat_le_total",
            lean_candidates: &["Rat.le_total", "le_total"],
        },
        AxiomMapping {
            axiom_name: "rat_add_le_add_left",
            lean_candidates: &["Rat.add_le_add_left", "add_le_add_left"],
        },
        AxiomMapping {
            axiom_name: "rat_mul_nonneg",
            lean_candidates: &["Rat.mul_nonneg", "mul_nonneg"],
        },
        // --- Matrix operations (C010, C003) ---
        AxiomMapping {
            axiom_name: "mat_add_comm",
            lean_candidates: &["Matrix.add_comm"],
        },
        AxiomMapping {
            axiom_name: "mat_mul_add",
            lean_candidates: &["Matrix.mul_add"],
        },
        AxiomMapping {
            axiom_name: "mat_add_mul",
            lean_candidates: &["Matrix.add_mul"],
        },
        AxiomMapping {
            axiom_name: "mat_mul_one",
            lean_candidates: &["Matrix.mul_one"],
        },
        AxiomMapping {
            axiom_name: "mat_one_mul",
            lean_candidates: &["Matrix.one_mul"],
        },
        AxiomMapping {
            axiom_name: "mat_transpose_transpose",
            lean_candidates: &["Matrix.transpose_transpose"],
        },
        AxiomMapping {
            axiom_name: "mat_transpose_mul",
            lean_candidates: &["Matrix.transpose_mul"],
        },
        // --- Real analysis (C003 Lipschitz, C028 Positivstellensatz) ---
        AxiomMapping {
            axiom_name: "real_abs_nonneg",
            lean_candidates: &["abs_nonneg", "Real.abs_nonneg"],
        },
        AxiomMapping {
            axiom_name: "real_abs_mul",
            lean_candidates: &["abs_mul", "Real.abs_mul"],
        },
        AxiomMapping {
            axiom_name: "real_triangle_ineq",
            lean_candidates: &["abs_add", "Real.abs_add"],
        },
        AxiomMapping {
            axiom_name: "real_sq_nonneg",
            lean_candidates: &["sq_nonneg", "Real.sq_nonneg"],
        },
        // --- Topology/metric (C003 compose_chain, lip_product) ---
        AxiomMapping {
            axiom_name: "lipschitz_comp",
            lean_candidates: &["LipschitzWith.comp", "LipschitzWith.comp'"],
        },
        AxiomMapping {
            axiom_name: "lipschitz_prod",
            lean_candidates: &["LipschitzWith.prod", "LipschitzWith.prod'"],
        },
        AxiomMapping {
            axiom_name: "dist_triangle",
            lean_candidates: &["dist_triangle", "Metric.dist_triangle"],
        },
        // --- Probability/measure (C029 PAC bounds) ---
        AxiomMapping {
            axiom_name: "measure_mono",
            lean_candidates: &["MeasureTheory.measure_mono"],
        },
        AxiomMapping {
            axiom_name: "prob_compl",
            lean_candidates: &["MeasureTheory.measure_compl"],
        },
    ]
}

/// All gamma-crown axiom mappings: Init + Mathlib combined.
///
/// Returns both the basic Init mappings and the extended Mathlib mappings
/// in a single list. Use this for comprehensive axiom replacement when
/// Mathlib `.olean` files are available.
pub fn all_gamma_crown_axiom_mappings() -> Vec<AxiomMapping> {
    let mut mappings = gamma_crown_axiom_mappings();
    mappings.extend(mathlib_gamma_crown_axiom_mappings());
    mappings
}

// ---------------------------------------------------------------------------
// Resolved replacement entry
// ---------------------------------------------------------------------------

/// A resolved axiom replacement: the gamma-crown axiom name mapped to a
/// concrete Init theorem with its type and proof term.
#[derive(Clone, Debug)]
pub struct ResolvedReplacement {
    /// Gamma-crown axiom name.
    pub axiom_name: String,
    /// Lean 4 theorem name that provides the replacement.
    pub lean_name: String,
    /// Type expression from the Init theorem.
    pub type_: Expr,
    /// Proof term from the Init theorem (Some if theorem, None if axiom/opaque).
    pub proof: Option<Expr>,
    /// Universe level parameters.
    pub level_params: Vec<Name>,
}

impl ResolvedReplacement {
    /// Whether this replacement has a real proof term (not just an axiom).
    #[must_use]
    pub fn has_proof(&self) -> bool {
        self.proof.is_some()
    }
}

// ---------------------------------------------------------------------------
// AxiomReplacementTable
// ---------------------------------------------------------------------------

/// A table of resolved gamma-crown axiom replacements from Lean 4 Init.
///
/// Built by loading Init modules and resolving each gamma-crown axiom name
/// against the loaded environment. Provides lookup by axiom name and
/// replacement statistics.
#[derive(Clone, Debug)]
pub struct AxiomReplacementTable {
    /// Resolved replacements keyed by gamma-crown axiom name.
    replacements: HashMap<String, ResolvedReplacement>,
    /// Axiom names that had no matching Init theorem.
    unresolved: Vec<String>,
    /// Total axioms in the mapping table.
    total_axioms: usize,
}

/// Statistics from building an axiom replacement table.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ReplacementStats {
    /// Total gamma-crown axioms in the mapping table.
    pub total_axioms: usize,
    /// Axioms resolved to Init theorems with proof terms.
    pub replaced_with_proof: usize,
    /// Axioms resolved to Init constants without proof terms (still axioms).
    pub resolved_no_proof: usize,
    /// Axioms with no matching Init constant.
    pub unresolved: usize,
}

impl AxiomReplacementTable {
    /// Build a replacement table by loading Lean 4 Init and resolving mappings.
    ///
    /// Returns `None` if the Lean 4 toolchain is not available.
    pub fn from_init() -> Option<Self> {
        let lib_path = find_lean_lib_path()?;
        Self::from_init_path(&lib_path)
    }

    /// Build a replacement table from a specific Lean 4 lib path.
    pub fn from_init_path(lean_lib_path: &std::path::Path) -> Option<Self> {
        let mut env = Environment::default();
        let result = load_init_modules(&mut env, lean_lib_path);

        if result.loaded_modules.is_empty() {
            return None;
        }

        Some(Self::from_environment(&env))
    }

    /// Build a replacement table from an already-loaded environment.
    ///
    /// Uses only the base Init axiom mappings. For environments that also
    /// contain Mathlib constants, use [`from_environment_extended`] instead.
    pub fn from_environment(env: &Environment) -> Self {
        Self::resolve_mappings(env, &gamma_crown_axiom_mappings())
    }

    /// Build a replacement table using the extended Mathlib mappings.
    ///
    /// Resolves both Init and Mathlib axiom mappings against the environment.
    /// The environment must have been loaded with the relevant Mathlib modules
    /// (e.g., `Mathlib.Data.Rat.Basic`, `Mathlib.Data.Matrix.Basic`, etc.)
    /// for the Mathlib-specific mappings to resolve.
    pub fn from_environment_extended(env: &Environment) -> Self {
        Self::resolve_mappings(env, &all_gamma_crown_axiom_mappings())
    }

    /// Build a replacement table by loading Init + Mathlib modules.
    ///
    /// Loads Init modules (always available) and attempts to load key Mathlib
    /// modules relevant to gamma-crown proofs. Returns `None` if the Lean 4
    /// toolchain is not available.
    ///
    /// This resolves both Init and Mathlib axiom mappings, providing the
    /// most comprehensive replacement table available.
    pub fn from_mathlib() -> Option<Self> {
        let lib_path = find_lean_lib_path()?;
        let mathlib_search_paths = find_mathlib_search_paths();

        let mut env = Environment::default();
        let init_result = load_init_modules(&mut env, &lib_path);

        if init_result.loaded_modules.is_empty() {
            return None;
        }

        // Load gamma-crown relevant Mathlib modules if available.
        if !mathlib_search_paths.is_empty() {
            let mathlib_modules = gamma_crown_mathlib_modules();
            let module_refs: Vec<&str> = mathlib_modules.iter().map(|s| s.as_str()).collect();
            let _mathlib_result =
                load_mathlib_modules(&mut env, &module_refs, &lib_path, &mathlib_search_paths);
        }

        Some(Self::from_environment_extended(&env))
    }

    /// Core resolution logic: resolve a list of axiom mappings against an environment.
    fn resolve_mappings(env: &Environment, mappings: &[AxiomMapping]) -> Self {
        let total_axioms = mappings.len();
        let mut replacements = HashMap::new();
        let mut unresolved = Vec::new();

        for mapping in mappings {
            let mut found = false;
            for &candidate in mapping.lean_candidates {
                let name = Name::from_string(candidate);
                if let Some(ci) = env.get_const(&name) {
                    let replacement = ResolvedReplacement {
                        axiom_name: mapping.axiom_name.to_string(),
                        lean_name: candidate.to_string(),
                        type_: ci.type_.clone(),
                        proof: ci.value.clone(),
                        level_params: ci.level_params.clone(),
                    };
                    replacements.insert(mapping.axiom_name.to_string(), replacement);
                    found = true;
                    break;
                }
            }
            if !found {
                unresolved.push(mapping.axiom_name.to_string());
            }
        }

        Self {
            replacements,
            unresolved,
            total_axioms,
        }
    }

    /// Look up a replacement by gamma-crown axiom name.
    #[must_use]
    pub fn get(&self, axiom_name: &str) -> Option<&ResolvedReplacement> {
        self.replacements.get(axiom_name)
    }

    /// Compute replacement statistics.
    #[must_use]
    pub fn stats(&self) -> ReplacementStats {
        let replaced_with_proof = self.replacements.values().filter(|r| r.has_proof()).count();
        let resolved_no_proof = self.replacements.len() - replaced_with_proof;

        ReplacementStats {
            total_axioms: self.total_axioms,
            replaced_with_proof,
            resolved_no_proof,
            unresolved: self.unresolved.len(),
        }
    }

    /// Iterator over all resolved replacements.
    pub fn resolved(&self) -> impl Iterator<Item = &ResolvedReplacement> {
        self.replacements.values()
    }

    /// List of axiom names that could not be resolved.
    #[must_use]
    pub fn unresolved_axioms(&self) -> &[String] {
        &self.unresolved
    }

    /// Total number of axioms in the mapping table.
    #[must_use]
    pub fn total_axioms(&self) -> usize {
        self.total_axioms
    }

    /// Number of successfully resolved replacements (with or without proof).
    #[must_use]
    pub fn num_resolved(&self) -> usize {
        self.replacements.len()
    }
}

// ---------------------------------------------------------------------------
// Environment patching
// ---------------------------------------------------------------------------

/// Result of applying axiom replacements to an environment.
#[derive(Clone, Debug, Default)]
pub struct PatchResult {
    /// Axioms successfully replaced with theorems (had proof terms).
    pub theorems_added: Vec<String>,
    /// Axioms matched but Init constant had no proof term.
    pub no_proof_available: Vec<String>,
    /// Axioms not found in the replacement table.
    pub not_in_table: Vec<String>,
    /// Errors encountered during add_decl (name, error message).
    pub errors: Vec<(String, String)>,
}

impl PatchResult {
    /// Number of axioms successfully replaced with proven theorems.
    #[must_use]
    pub fn num_replaced(&self) -> usize {
        self.theorems_added.len()
    }
}

/// Apply axiom replacements from an `AxiomReplacementTable` to an environment.
///
/// For each gamma-crown axiom name in `axiom_names`, if the table has a
/// resolved replacement with a proof term, registers a `Declaration::Theorem`
/// in the target environment. The theorem uses the Init theorem's type and
/// proof term but is registered under the gamma-crown axiom name so existing
/// references resolve correctly.
///
/// # Important
///
/// The target environment should NOT already contain declarations with the
/// axiom names. If a name already exists, `add_decl` will return a
/// duplicate-name error, which is recorded in `PatchResult::errors`.
pub fn apply_replacements(
    env: &mut Environment,
    table: &AxiomReplacementTable,
    axiom_names: &[&str],
) -> PatchResult {
    let mut result = PatchResult::default();

    for &axiom_name in axiom_names {
        let Some(replacement) = table.get(axiom_name) else {
            result.not_in_table.push(axiom_name.to_string());
            continue;
        };

        let Some(ref proof) = replacement.proof else {
            result.no_proof_available.push(axiom_name.to_string());
            continue;
        };

        let decl = clean_kernel::Declaration::Theorem {
            name: Name::from_string(axiom_name),
            level_params: replacement.level_params.clone(),
            type_: replacement.type_.clone(),
            value: proof.clone(),
        };

        match env.add_decl(decl) {
            Ok(()) => {
                result.theorems_added.push(axiom_name.to_string());
            }
            Err(e) => {
                result.errors.push((axiom_name.to_string(), format!("{e}")));
            }
        }
    }

    result
}

/// Build an environment pre-loaded with gamma-crown axiom replacements from Init.
///
/// Returns `None` if the Lean 4 toolchain is unavailable.
///
/// This is a convenience function that:
/// 1. Loads Init modules into a fresh environment.
/// 2. Builds the replacement table.
/// 3. Returns both the loaded environment and the table for further use.
pub fn load_init_with_replacements() -> Option<(Environment, AxiomReplacementTable)> {
    let lib_path = find_lean_lib_path()?;
    let mut env = Environment::default();
    let result = load_init_modules(&mut env, &lib_path);

    if result.loaded_modules.is_empty() {
        return None;
    }

    let table = AxiomReplacementTable::from_environment(&env);
    Some((env, table))
}

/// Build an environment pre-loaded with gamma-crown axiom replacements from
/// both Init and Mathlib.
///
/// Returns `None` if the Lean 4 toolchain is unavailable.
///
/// If Mathlib `.olean` files are not available, falls back to Init-only
/// replacements (same as [`load_init_with_replacements`]).
pub fn load_mathlib_with_replacements() -> Option<(Environment, AxiomReplacementTable)> {
    let lib_path = find_lean_lib_path()?;
    let mathlib_search_paths = find_mathlib_search_paths();

    let mut env = Environment::default();
    let init_result = load_init_modules(&mut env, &lib_path);

    if init_result.loaded_modules.is_empty() {
        return None;
    }

    // Load gamma-crown relevant Mathlib modules if available.
    if !mathlib_search_paths.is_empty() {
        let mathlib_modules = gamma_crown_mathlib_modules();
        let module_refs: Vec<&str> = mathlib_modules.iter().map(|s| s.as_str()).collect();
        let _mathlib_result =
            load_mathlib_modules(&mut env, &module_refs, &lib_path, &mathlib_search_paths);
    }

    let table = AxiomReplacementTable::from_environment_extended(&env);
    Some((env, table))
}

// ---------------------------------------------------------------------------
// Mathlib module list for gamma-crown
// ---------------------------------------------------------------------------

/// Mathlib modules that contain theorems needed by gamma-crown proofs.
///
/// These are loaded on-demand when building a Mathlib-based replacement table.
/// The list is kept minimal to avoid loading the entire Mathlib dependency tree.
///
/// Each module is listed with its gamma-crown relevance:
/// - `Mathlib.Data.Rat.Basic` — Rat field properties (Category B axioms)
/// - `Mathlib.Data.Rat.Order` — Rat ordering (interval arithmetic)
/// - `Mathlib.Data.Matrix.Basic` — Matrix ring ops (C003, C010)
/// - `Mathlib.Analysis.NormedSpace.Basic` — Norms/Lipschitz (C003)
/// - `Mathlib.Topology.MetricSpace.Lipschitz` — LipschitzWith (C003)
/// - `Mathlib.Analysis.SpecificLimits.Basic` — Real analysis (C028)
/// - `Mathlib.MeasureTheory.Measure.MeasureSpace` — Probability (C029)
/// - `Mathlib.Order.Basic` — Order properties (C007)
pub fn gamma_crown_mathlib_modules() -> Vec<String> {
    vec![
        "Mathlib.Data.Rat.Basic".to_string(),
        "Mathlib.Data.Rat.Order".to_string(),
        "Mathlib.Data.Matrix.Basic".to_string(),
        "Mathlib.Analysis.NormedSpace.Basic".to_string(),
        "Mathlib.Topology.MetricSpace.Lipschitz".to_string(),
        "Mathlib.Analysis.SpecificLimits.Basic".to_string(),
        "Mathlib.MeasureTheory.Measure.MeasureSpace".to_string(),
        "Mathlib.Order.Basic".to_string(),
    ]
}

#[cfg(test)]
#[path = "axiom_replacement_tests.rs"]
mod tests;

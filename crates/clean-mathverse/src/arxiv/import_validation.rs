// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Validates `import Mathlib.*` lines in LLM-generated Lean 4 code against a
//! known-valid whitelist, then rewrites fictional imports into explicit local
//! warning comments and `sorry`-backed stand-ins.

use std::collections::HashSet;

use serde::{Deserialize, Serialize};

/// Sorted whitelist of known-valid Mathlib modules for prefix validation.
pub const KNOWN_MATHLIB_MODULES: &[&str] = &[
    "Mathlib.Algebra.BigOperators.Ring.Finset",
    "Mathlib.Algebra.Field.Basic",
    "Mathlib.Algebra.Field.Defs",
    "Mathlib.Algebra.Group.Basic",
    "Mathlib.Algebra.Group.Defs",
    "Mathlib.Algebra.Order.Field.Basic",
    "Mathlib.Algebra.Order.Ring.Defs",
    "Mathlib.Algebra.Ring.Basic",
    "Mathlib.Analysis.InnerProductSpace.Basic",
    "Mathlib.Analysis.NormedSpace.Basic",
    "Mathlib.Analysis.SpecialFunctions.Exp",
    "Mathlib.Analysis.SpecialFunctions.Log.Basic",
    "Mathlib.Analysis.SpecificLimits.Basic",
    "Mathlib.CategoryTheory.Category.Basic",
    "Mathlib.CategoryTheory.Category.Cat",
    "Mathlib.CategoryTheory.Functor.Basic",
    "Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts",
    "Mathlib.Combinatorics.SimpleGraph.Basic",
    "Mathlib.Data.Bool.Basic",
    "Mathlib.Data.Complex.Basic",
    "Mathlib.Data.Complex.Exponential",
    "Mathlib.Data.ENNReal.Basic",
    "Mathlib.Data.Finset.Basic",
    "Mathlib.Data.Finset.Card",
    "Mathlib.Data.Fintype.Basic",
    "Mathlib.Data.Int.Basic",
    "Mathlib.Data.List.Basic",
    "Mathlib.Data.Matrix.Basic",
    "Mathlib.Data.NNReal.Basic",
    "Mathlib.Data.Nat.Basic",
    "Mathlib.Data.Rat.Defs",
    "Mathlib.Data.Real.Basic",
    "Mathlib.Data.Set.Basic",
    "Mathlib.Init",
    "Mathlib.LinearAlgebra.BilinearMap",
    "Mathlib.LinearAlgebra.Determinant",
    "Mathlib.LinearAlgebra.FiniteDimensional",
    "Mathlib.LinearAlgebra.GeneralLinearGroup",
    "Mathlib.LinearAlgebra.Matrix.Determinant",
    "Mathlib.LinearAlgebra.Matrix.Trace",
    "Mathlib.Logic.Basic",
    "Mathlib.MeasureTheory.Integral.Bochner",
    "Mathlib.MeasureTheory.MeasurableSpace.Basic",
    "Mathlib.MeasureTheory.Measure.MeasureSpace",
    "Mathlib.NumberTheory.ArithmeticFunction",
    "Mathlib.NumberTheory.LSeries.Dirichlet",
    "Mathlib.NumberTheory.PrimeCounting",
    "Mathlib.Order.Basic",
    "Mathlib.Order.Filter.Basic",
    "Mathlib.Order.Lattice",
    "Mathlib.SetTheory.Cardinal.Basic",
    "Mathlib.SetTheory.Ordinal.Basic",
    "Mathlib.Tactic.Abel",
    "Mathlib.Tactic.Basic",
    "Mathlib.Tactic.CancelDenoms",
    "Mathlib.Tactic.FieldSimp",
    "Mathlib.Tactic.Linarith",
    "Mathlib.Tactic.NormNum",
    "Mathlib.Tactic.Omega",
    "Mathlib.Tactic.Positivity",
    "Mathlib.Tactic.Ring",
    "Mathlib.Topology.Algebra.Module.Basic",
    "Mathlib.Topology.Basic",
    "Mathlib.Topology.MetricSpace.Basic",
    "Mathlib.Topology.UniformSpace.Basic",
];

/// Validation output for discovered Mathlib imports.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ImportValidationResult {
    pub valid_imports: Vec<String>,
    pub invalid_imports: Vec<String>,
    pub rewrites: Vec<ImportRewrite>,
}

/// Rewrite payload for one fictional import.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ImportRewrite {
    pub original_import: String,
    pub replacement_code: String,
}

#[must_use]
fn extract_mathlib_imports(lean_code: &str) -> Vec<String> {
    lean_code
        .lines()
        .flat_map(|line| {
            let trimmed = line.trim_start();
            if !trimmed.starts_with("import ") {
                return Vec::new();
            }

            trimmed
                .split_whitespace()
                .skip(1)
                .take_while(|token| !token.starts_with("--"))
                .filter(|token| token.starts_with("Mathlib."))
                .map(str::to_string)
                .collect()
        })
        .collect()
}

#[must_use]
fn is_known_mathlib_import(import_path: &str) -> bool {
    let mut candidate = import_path.trim();

    loop {
        if KNOWN_MATHLIB_MODULES.binary_search(&candidate).is_ok() {
            return true;
        }

        match candidate.rfind('.') {
            Some(index) if index > "Mathlib".len() => candidate = &candidate[..index],
            _ => return false,
        }
    }
}

#[must_use]
fn sanitize_identifier(component: &str) -> String {
    component
        .chars()
        .filter(|ch| ch.is_ascii_alphanumeric() || *ch == '_')
        .collect()
}

#[must_use]
fn singularize(component: &str) -> String {
    if let Some(stem) = component.strip_suffix("ies") {
        format!("{stem}y")
    } else if component.ends_with('s') && !component.ends_with("ss") && component.len() > 1 {
        component[..component.len() - 1].to_string()
    } else {
        component.to_string()
    }
}

#[must_use]
fn infer_stub_names(import_path: &str) -> Vec<String> {
    const GENERIC_COMPONENTS: &[&str] = &[
        "Algebra",
        "Analysis",
        "Basic",
        "CategoryTheory",
        "Combinatorics",
        "Core",
        "Data",
        "Defs",
        "Field",
        "Functor",
        "Group",
        "Init",
        "Instances",
        "Integral",
        "LinearAlgebra",
        "Logic",
        "Mathlib",
        "Measure",
        "MeasureTheory",
        "Module",
        "NumberTheory",
        "Order",
        "SetTheory",
        "Tactic",
        "Topology",
    ];

    let components: Vec<&str> = import_path.split('.').skip(1).collect();
    for component in components.into_iter().rev() {
        if GENERIC_COMPONENTS.contains(&component) {
            continue;
        }

        let stub_name = sanitize_identifier(&singularize(component));
        if !stub_name.is_empty() && stub_name != "Basic" {
            return vec![stub_name];
        }
    }

    extract_implied_types(import_path)
        .into_iter()
        .map(|name| sanitize_identifier(&name))
        .filter(|name| !name.is_empty() && name != "Basic")
        .collect()
}

#[must_use]
fn replacement_code_for_import(import_path: &str) -> String {
    let mut lines = vec![format!(
        "-- WARNING: removed fictional import: {import_path}"
    )];
    let stub_names = infer_stub_names(import_path);

    if stub_names.is_empty() {
        lines.push(format!(
            "-- NOTE: add local stand-ins for missing declarations from {import_path}"
        ));
    } else {
        for stub_name in stub_names {
            lines.push(format!("def {stub_name} (X : Type*) := sorry"));
        }
    }

    lines.join("\n")
}

/// Extract likely type names from an import path by taking its last component.
#[must_use]
pub fn extract_implied_types(import_path: &str) -> Vec<String> {
    import_path
        .rsplit('.')
        .next()
        .map(|component| vec![component.to_string()])
        .unwrap_or_default()
}

/// Validate all `import Mathlib.*` references in generated Lean code.
#[must_use]
pub fn validate_imports(lean_code: &str) -> ImportValidationResult {
    let mut valid_imports = Vec::new();
    let mut invalid_imports = Vec::new();
    let mut rewrites = Vec::new();

    for import_path in extract_mathlib_imports(lean_code) {
        if is_known_mathlib_import(&import_path) {
            valid_imports.push(import_path);
        } else {
            invalid_imports.push(import_path.clone());
            rewrites.push(ImportRewrite {
                original_import: import_path.clone(),
                replacement_code: replacement_code_for_import(&import_path),
            });
        }
    }

    ImportValidationResult {
        valid_imports,
        invalid_imports,
        rewrites,
    }
}

/// Remove fictional imports and replace them with warning comments and local
/// `sorry`-based placeholder definitions.
#[must_use]
pub fn rewrite_invalid_imports(lean_code: &str, result: &ImportValidationResult) -> String {
    let invalid: HashSet<&str> = result.invalid_imports.iter().map(String::as_str).collect();
    let mut output = Vec::new();

    for line in lean_code.lines() {
        let trimmed = line.trim_start();
        if !trimmed.starts_with("import ") {
            output.push(line.to_string());
            continue;
        }

        let tokens: Vec<&str> = trimmed
            .split_whitespace()
            .skip(1)
            .take_while(|token| !token.starts_with("--"))
            .collect();
        let removed_modules: Vec<&str> = tokens
            .iter()
            .copied()
            .filter(|token| token.starts_with("Mathlib.") && invalid.contains(token))
            .collect();

        if removed_modules.is_empty() {
            output.push(line.to_string());
            continue;
        }

        let kept_modules: Vec<&str> = tokens
            .iter()
            .copied()
            .filter(|token| !(token.starts_with("Mathlib.") && invalid.contains(token)))
            .collect();
        if !kept_modules.is_empty() {
            output.push(format!("import {}", kept_modules.join(" ")));
        }

        for removed in removed_modules {
            if let Some(rewrite) = result
                .rewrites
                .iter()
                .find(|rewrite| rewrite.original_import == removed)
            {
                output.push(rewrite.replacement_code.clone());
            } else {
                output.push(replacement_code_for_import(removed));
            }
        }
    }

    output.join("\n")
}

#[cfg(test)]
mod tests {
    use super::{
        extract_implied_types, rewrite_invalid_imports, validate_imports, KNOWN_MATHLIB_MODULES,
    };

    #[test]
    fn test_validate_known_import() {
        let result = validate_imports("import Mathlib.Data.Nat.Basic\n");
        assert_eq!(result.valid_imports, vec!["Mathlib.Data.Nat.Basic"]);
        assert!(result.invalid_imports.is_empty());
        assert!(result.rewrites.is_empty());
    }

    #[test]
    fn test_validate_unknown_import() {
        let result = validate_imports("import Mathlib.AlgebraicGeometry.Divisors.Basic\n");
        assert!(result.valid_imports.is_empty());
        assert_eq!(
            result.invalid_imports,
            vec!["Mathlib.AlgebraicGeometry.Divisors.Basic"]
        );
        assert_eq!(result.rewrites.len(), 1);
    }

    #[test]
    fn test_validate_mixed_imports() {
        let code = "\
import Mathlib.Data.Nat.Basic
import Mathlib.AlgebraicGeometry.Divisors.Basic
import Mathlib.Tactic.Ring
";
        let result = validate_imports(code);

        assert_eq!(result.valid_imports.len(), 2);
        assert_eq!(result.invalid_imports.len(), 1);
        assert!(result
            .valid_imports
            .iter()
            .any(|item| item == "Mathlib.Data.Nat.Basic"));
        assert!(result
            .valid_imports
            .iter()
            .any(|item| item == "Mathlib.Tactic.Ring"));
        assert!(result
            .invalid_imports
            .iter()
            .any(|item| item == "Mathlib.AlgebraicGeometry.Divisors.Basic"));
    }

    #[test]
    fn test_rewrite_removes_invalid() {
        let code = "\
import Mathlib.Data.Nat.Basic
import Mathlib.AlgebraicGeometry.Divisors.Basic

theorem demo : True := by
  trivial
";
        let result = validate_imports(code);
        let rewritten = rewrite_invalid_imports(code, &result);

        assert!(rewritten.contains("import Mathlib.Data.Nat.Basic"));
        assert!(!rewritten.contains("import Mathlib.AlgebraicGeometry.Divisors.Basic"));
        assert!(rewritten.contains(
            "-- WARNING: removed fictional import: Mathlib.AlgebraicGeometry.Divisors.Basic"
        ));
        assert!(rewritten.contains("def Divisor (X : Type*) := sorry"));
    }

    #[test]
    fn test_extract_implied_types() {
        assert_eq!(
            extract_implied_types("Mathlib.Foo.Bar.Baz"),
            vec!["Baz".to_string()]
        );
    }

    #[test]
    fn test_validate_empty_code() {
        let result = validate_imports("");
        assert!(result.valid_imports.is_empty());
        assert!(result.invalid_imports.is_empty());
        assert!(result.rewrites.is_empty());
    }

    #[test]
    fn test_known_modules_sorted() {
        for pair in KNOWN_MATHLIB_MODULES.windows(2) {
            assert!(
                pair[0] < pair[1],
                "known modules must be strictly sorted: {:?}",
                pair
            );
        }
    }
}

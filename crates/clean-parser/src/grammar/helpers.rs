// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

/// Check if a string is a typed morphism subscript (ₗ, ₐ, ₘ, etc.)
/// These appear in Mathlib notations like `→ₗ[R]` (LinearMap) and `→ₐ[R]` (AlgHom)
pub(super) fn is_typed_morphism_subscript(s: &str) -> bool {
    matches!(s, "ₗ" | "ₐ" | "ₘ" | "ₛₗ" | "ₙ")
}

/// Map typed morphism subscript to its type constructor name
pub(super) fn typed_morphism_constructor(subscript: &str) -> &'static str {
    match subscript {
        "ₗ" => "LinearMap",      // Linear map
        "ₐ" => "AlgHom",         // Algebra homomorphism
        "ₘ" => "ModuleHom",      // Module homomorphism
        "ₛₗ" => "SemilinearMap", // Semilinear map
        "ₙ" => "NatTrans",       // Natural transformation
        _ => "LinearMap", // Fallback (shouldn't happen due to is_typed_morphism_subscript check)
    }
}

/// Check if a string is a typed equivalence subscript (ₐ, ₗ, ₘ, etc.)
/// These appear in Mathlib notations like `≃ₐ[R]` (AlgEquiv) and `≃ₗ[R]` (LinearEquiv)
pub(super) fn is_typed_equiv_subscript(s: &str) -> bool {
    matches!(s, "ₐ" | "ₗ" | "ₘ" | "ₛₗ" | "ₗᵢ")
}

/// Map typed equivalence subscript to its type constructor name
pub(super) fn typed_equiv_constructor(subscript: &str) -> &'static str {
    match subscript {
        "ₐ" => "AlgEquiv",             // Algebra equivalence
        "ₗ" => "LinearEquiv",          // Linear equivalence
        "ₘ" => "ModuleEquiv",          // Module equivalence
        "ₛₗ" => "SemilinearEquiv",     // Semilinear equivalence
        "ₗᵢ" => "LinearIsometryEquiv", // Linear isometry equivalence
        _ => "AlgEquiv",               // Fallback
    }
}

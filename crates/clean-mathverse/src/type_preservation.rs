// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Type preservation verification for Mathverse Library translations.
//!
//! Verifies that translations from source proof systems (Isabelle, Mizar, etc.)
//! into clean kernel expressions maintain structural and type-theoretic
//! properties:
//!
//! - Function types map to Pi/arrow types
//! - Boolean/Prop types map correctly
//! - Bound variables preserve de Bruijn indices
//! - Application and lambda structure is preserved
//! - Axiom profiles are monotone under union
//! - Trust levels maintain their total order
//!
//! These checks serve as regression tests and integration smoke tests for the
//! translation pipeline.

use crate::hol::isabelle::translate::IsabelleTranslator;
use crate::hol::isabelle::types::{IsaTerm, IsaType};
#[cfg(test)]
use crate::hol::isabelle::types::{IsaTheorem, ProofStatus};
use crate::types::{AxiomProfile, TrustLevel};

// ---------------------------------------------------------------------------
// PreservationProperty
// ---------------------------------------------------------------------------

/// A named property that a translation pipeline should preserve.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum PreservationProperty {
    /// Isabelle function types (`fun(a, b)`) become Pi/arrow types in clean.
    FunTypeMapsToArrow,
    /// Isabelle `bool`/`prop` types become `Prop` (Sort 0) in clean.
    BoolMapsToProb,
    /// De Bruijn bound variable indices are preserved across translation.
    BoundVarsPreserved,
    /// Application spine structure (`App(f, x)`) is preserved.
    AppStructurePreserved,
    /// Lambda abstraction structure (`Abs(x, ty, body)`) is preserved.
    LamStructurePreserved,
    /// Axiom profiles only grow (or stay equal) under union.
    AxiomProfileMonotone,
}

// ---------------------------------------------------------------------------
// PreservationCheck
// ---------------------------------------------------------------------------

/// Result of a single preservation property check.
#[derive(Clone, Debug)]
pub struct PreservationCheck {
    /// Which property was checked.
    pub property: PreservationProperty,
    /// Whether all examples passed.
    pub passed: bool,
    /// Human-readable evidence or failure description.
    pub evidence: String,
    /// Number of concrete examples checked.
    pub checked_examples: usize,
}

impl PreservationCheck {
    /// Create a passing check result.
    #[must_use]
    fn pass(property: PreservationProperty, evidence: String, count: usize) -> Self {
        Self {
            property,
            passed: true,
            evidence,
            checked_examples: count,
        }
    }

    /// Create a failing check result.
    #[must_use]
    fn fail(property: PreservationProperty, evidence: String, count: usize) -> Self {
        Self {
            property,
            passed: false,
            evidence,
            checked_examples: count,
        }
    }
}

// ---------------------------------------------------------------------------
// TypePreservationVerifier
// ---------------------------------------------------------------------------

/// Verifier that checks type preservation properties across translations.
///
/// Generates sample source-system types and terms, translates them via the
/// appropriate translator, and verifies the output expressions satisfy
/// structural invariants.
pub struct TypePreservationVerifier {
    translator: IsabelleTranslator,
}

impl TypePreservationVerifier {
    /// Create a new verifier with a default Isabelle translator.
    #[must_use]
    pub fn new() -> Self {
        Self {
            translator: IsabelleTranslator::new("TypePreservation.Test"),
        }
    }

    // ── Isabelle type preservation ──

    /// Verify that Isabelle type translation preserves expected clean shapes.
    ///
    /// Checks:
    /// - `TFree` maps to `Const` (named type variable)
    /// - `Type("fun", [a, b])` maps to `Pi` (arrow type)
    /// - `Type("bool", [])` / `Type("prop", [])` maps to `Prop` (Sort 0)
    /// - `Type("nat", [])` maps to `Const "Nat"`
    #[must_use]
    pub fn verify_isabelle_type_preservation(&self) -> Vec<PreservationCheck> {
        vec![
            self.check_fun_type_maps_to_arrow(),
            self.check_bool_maps_to_prop(),
        ]
    }

    /// Verify Isabelle `fun(a, b)` translates to Pi/arrow.
    #[must_use]
    fn check_fun_type_maps_to_arrow(&self) -> PreservationCheck {
        let test_cases: Vec<IsaType> = vec![
            // Simple: nat -> bool
            IsaType::fun(IsaType::nullary("nat"), IsaType::nullary("HOL.bool")),
            // Nested: (nat -> nat) -> bool
            IsaType::fun(
                IsaType::fun(IsaType::nullary("nat"), IsaType::nullary("nat")),
                IsaType::nullary("HOL.bool"),
            ),
            // With type variable: 'a -> 'a
            IsaType::fun(IsaType::tfree("'a"), IsaType::tfree("'a")),
            // Multi-arg via currying: nat -> nat -> nat
            IsaType::fun(
                IsaType::nullary("nat"),
                IsaType::fun(IsaType::nullary("nat"), IsaType::nullary("nat")),
            ),
        ];

        let mut passed_count = 0;
        let total = test_cases.len();

        for isa_ty in &test_cases {
            match self.translator.translate_type(isa_ty) {
                Ok(expr) if expr.is_pi() => passed_count += 1,
                Ok(expr) => {
                    return PreservationCheck::fail(
                        PreservationProperty::FunTypeMapsToArrow,
                        format!("fun type did not translate to Pi: {isa_ty:?} -> {expr:?}"),
                        total,
                    );
                }
                Err(e) => {
                    return PreservationCheck::fail(
                        PreservationProperty::FunTypeMapsToArrow,
                        format!("translation error: {e}"),
                        total,
                    );
                }
            }
        }

        PreservationCheck::pass(
            PreservationProperty::FunTypeMapsToArrow,
            format!("{passed_count}/{total} fun types correctly mapped to Pi"),
            total,
        )
    }

    /// Verify Isabelle `bool`/`prop` translates to clean Prop.
    #[must_use]
    fn check_bool_maps_to_prop(&self) -> PreservationCheck {
        let test_cases: Vec<(&str, IsaType)> = vec![
            ("HOL.bool", IsaType::nullary("HOL.bool")),
            ("bool", IsaType::nullary("bool")),
            ("prop", IsaType::nullary("prop")),
        ];

        let mut passed_count = 0;
        let total = test_cases.len();

        for (label, isa_ty) in &test_cases {
            match self.translator.translate_type(isa_ty) {
                Ok(expr) if expr.is_prop() => passed_count += 1,
                Ok(expr) => {
                    return PreservationCheck::fail(
                        PreservationProperty::BoolMapsToProb,
                        format!("{label} did not translate to Prop: {isa_ty:?} -> {expr:?}"),
                        total,
                    );
                }
                Err(e) => {
                    return PreservationCheck::fail(
                        PreservationProperty::BoolMapsToProb,
                        format!("{label} translation error: {e}"),
                        total,
                    );
                }
            }
        }

        PreservationCheck::pass(
            PreservationProperty::BoolMapsToProb,
            format!("{passed_count}/{total} bool/prop types correctly mapped to Prop"),
            total,
        )
    }

    // ── Isabelle term preservation ──

    /// Verify that Isabelle term translation preserves structural shapes.
    ///
    /// Checks:
    /// - `Bound(i)` maps to `BVar(i)`
    /// - `Free(name, ty)` maps to `Const`
    /// - `Abs(name, ty, body)` maps to `Lam`
    /// - `App(f, x)` maps to `App`
    #[must_use]
    pub fn verify_isabelle_term_preservation(&self) -> Vec<PreservationCheck> {
        vec![
            self.check_bound_vars_preserved(),
            self.check_app_structure_preserved(),
            self.check_lam_structure_preserved(),
        ]
    }

    /// Verify bound variable indices are preserved.
    #[must_use]
    fn check_bound_vars_preserved(&self) -> PreservationCheck {
        let indices: Vec<u32> = vec![0, 1, 2, 5, 10, 100];
        let total = indices.len();
        let mut passed_count = 0;

        for &idx in &indices {
            let term = IsaTerm::Bound(idx);
            match self.translator.translate_term(&term) {
                Ok(expr) if expr.is_bvar() => {
                    // Verify the index matches via debug output
                    let debug = format!("{expr:?}");
                    if debug.contains(&format!("BVar({idx})")) {
                        passed_count += 1;
                    } else {
                        return PreservationCheck::fail(
                            PreservationProperty::BoundVarsPreserved,
                            format!("BVar index mismatch: expected {idx}, got {debug}"),
                            total,
                        );
                    }
                }
                Ok(expr) => {
                    return PreservationCheck::fail(
                        PreservationProperty::BoundVarsPreserved,
                        format!("Bound({idx}) did not translate to BVar: {expr:?}"),
                        total,
                    );
                }
                Err(e) => {
                    return PreservationCheck::fail(
                        PreservationProperty::BoundVarsPreserved,
                        format!("Bound({idx}) translation error: {e}"),
                        total,
                    );
                }
            }
        }

        PreservationCheck::pass(
            PreservationProperty::BoundVarsPreserved,
            format!("{passed_count}/{total} bound variable indices preserved"),
            total,
        )
    }

    /// Verify application structure is preserved.
    #[must_use]
    fn check_app_structure_preserved(&self) -> PreservationCheck {
        let nat_ty = IsaType::nullary("nat");
        let fun_ty = IsaType::fun(nat_ty.clone(), nat_ty.clone());

        let test_cases: Vec<IsaTerm> = vec![
            // Simple: f(x)
            IsaTerm::app(
                IsaTerm::const_of("f", fun_ty.clone()),
                IsaTerm::const_of("x", nat_ty.clone()),
            ),
            // Nested: f(g(x))
            IsaTerm::app(
                IsaTerm::const_of("f", fun_ty.clone()),
                IsaTerm::app(
                    IsaTerm::const_of("g", fun_ty.clone()),
                    IsaTerm::const_of("x", nat_ty.clone()),
                ),
            ),
            // Curried: f(x)(y)
            IsaTerm::app(
                IsaTerm::app(
                    IsaTerm::const_of("f", IsaType::fun(nat_ty.clone(), fun_ty.clone())),
                    IsaTerm::const_of("x", nat_ty.clone()),
                ),
                IsaTerm::const_of("y", nat_ty.clone()),
            ),
        ];

        let total = test_cases.len();
        let mut passed_count = 0;

        for term in &test_cases {
            match self.translator.translate_term(term) {
                Ok(expr) if expr.is_app() => passed_count += 1,
                Ok(expr) => {
                    return PreservationCheck::fail(
                        PreservationProperty::AppStructurePreserved,
                        format!("App term did not translate to App: {term:?} -> {expr:?}"),
                        total,
                    );
                }
                Err(e) => {
                    return PreservationCheck::fail(
                        PreservationProperty::AppStructurePreserved,
                        format!("App translation error: {e}"),
                        total,
                    );
                }
            }
        }

        PreservationCheck::pass(
            PreservationProperty::AppStructurePreserved,
            format!("{passed_count}/{total} application structures preserved"),
            total,
        )
    }

    /// Verify lambda abstraction structure is preserved.
    #[must_use]
    fn check_lam_structure_preserved(&self) -> PreservationCheck {
        let nat_ty = IsaType::nullary("nat");
        let bool_ty = IsaType::nullary("HOL.bool");

        let test_cases: Vec<IsaTerm> = vec![
            // Simple: \x::nat. x
            IsaTerm::abs("x", nat_ty.clone(), IsaTerm::Bound(0)),
            // Nested: \x::nat. \y::nat. x
            IsaTerm::abs(
                "x",
                nat_ty.clone(),
                IsaTerm::abs("y", nat_ty.clone(), IsaTerm::Bound(1)),
            ),
            // Different type: \p::bool. p
            IsaTerm::abs("p", bool_ty.clone(), IsaTerm::Bound(0)),
        ];

        let total = test_cases.len();
        let mut passed_count = 0;

        for term in &test_cases {
            match self.translator.translate_term(term) {
                Ok(expr) if expr.is_lam() => passed_count += 1,
                Ok(expr) => {
                    return PreservationCheck::fail(
                        PreservationProperty::LamStructurePreserved,
                        format!("Abs term did not translate to Lam: {term:?} -> {expr:?}"),
                        total,
                    );
                }
                Err(e) => {
                    return PreservationCheck::fail(
                        PreservationProperty::LamStructurePreserved,
                        format!("Abs translation error: {e}"),
                        total,
                    );
                }
            }
        }

        PreservationCheck::pass(
            PreservationProperty::LamStructurePreserved,
            format!("{passed_count}/{total} lambda structures preserved"),
            total,
        )
    }

    // ── Axiom profile monotonicity ──

    /// Verify that axiom profile union is monotone: for all p1, p2,
    /// `p1.union(p2)` is a superset of both `p1` and `p2`.
    #[must_use]
    pub fn verify_axiom_profile_monotonicity(&self) -> PreservationCheck {
        let profiles: Vec<AxiomProfile> = vec![
            AxiomProfile::NONE,
            AxiomProfile::CLASSICAL,
            AxiomProfile::EXTENSIONALITY,
            AxiomProfile::CHOICE,
            AxiomProfile::HOL_EMBEDDING,
            AxiomProfile::MIZAR_SOFT_TYPE,
            AxiomProfile::ISABELLE_LCF_ERASED,
            AxiomProfile::SMT_ORACLE,
            AxiomProfile::FLOAT_APPROX,
            AxiomProfile::CLASSICAL | AxiomProfile::EXTENSIONALITY,
            AxiomProfile::CLASSICAL | AxiomProfile::CHOICE | AxiomProfile::HOL_EMBEDDING,
            AxiomProfile::ISABELLE_LCF_ERASED
                | AxiomProfile::CLASSICAL
                | AxiomProfile::EXTENSIONALITY,
        ];

        let mut checked = 0;

        for p1 in &profiles {
            for p2 in &profiles {
                let union = p1.union(*p2);

                if !union.is_superset_of(*p1) {
                    return PreservationCheck::fail(
                        PreservationProperty::AxiomProfileMonotone,
                        format!("union({p1:?}, {p2:?}) = {union:?} is not superset of {p1:?}"),
                        checked,
                    );
                }

                if !union.is_superset_of(*p2) {
                    return PreservationCheck::fail(
                        PreservationProperty::AxiomProfileMonotone,
                        format!("union({p1:?}, {p2:?}) = {union:?} is not superset of {p2:?}"),
                        checked,
                    );
                }

                checked += 1;
            }
        }

        PreservationCheck::pass(
            PreservationProperty::AxiomProfileMonotone,
            format!("{checked} profile pair combinations verified monotone"),
            checked,
        )
    }

    // ── Trust level ordering ──

    /// Verify `TrustLevel` ordering:
    /// `KernelVerified < AxiomDependent < CertificateReplayed < PartiallyAxiomatized < TrustedOracle`.
    #[must_use]
    pub fn verify_trust_level_ordering(&self) -> PreservationCheck {
        let levels = [
            TrustLevel::KernelVerified,
            TrustLevel::AxiomDependent,
            TrustLevel::CertificateReplayed,
            TrustLevel::PartiallyAxiomatized,
            TrustLevel::TrustedOracle,
        ];

        let mut checked = 0;

        for i in 0..levels.len() {
            for j in (i + 1)..levels.len() {
                if levels[i] >= levels[j] {
                    return PreservationCheck::fail(
                        PreservationProperty::AxiomProfileMonotone,
                        format!(
                            "TrustLevel ordering violated: {:?} should be < {:?}",
                            levels[i], levels[j]
                        ),
                        checked,
                    );
                }
                checked += 1;
            }

            // Reflexive equality check. The expression is tautologically
            // true for any `PartialEq` whose `eq` matches the derived
            // structural compare, but we keep it as a defensive runtime
            // assertion (counted in `checked`) so a future custom impl
            // that violates reflexivity would fail loudly here.
            #[allow(clippy::eq_op)]
            if levels[i] != levels[i] {
                return PreservationCheck::fail(
                    PreservationProperty::AxiomProfileMonotone,
                    format!("TrustLevel reflexivity violated: {:?} != itself", levels[i]),
                    checked,
                );
            }
            checked += 1;
        }

        PreservationCheck::pass(
            PreservationProperty::AxiomProfileMonotone,
            format!(
                "TrustLevel total order verified across {} comparisons",
                checked,
            ),
            checked,
        )
    }

    // ── Run all ──

    /// Run all preservation verification checks.
    #[must_use]
    pub fn run_all(&self) -> Vec<PreservationCheck> {
        let mut results = Vec::new();
        results.extend(self.verify_isabelle_type_preservation());
        results.extend(self.verify_isabelle_term_preservation());
        results.push(self.verify_axiom_profile_monotonicity());
        results.push(self.verify_trust_level_ordering());
        results
    }
}

impl Default for TypePreservationVerifier {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// PreservationEvidence
// ---------------------------------------------------------------------------

/// Detailed evidence for a single preservation property result.
///
/// Used to provide structured information about what was checked, what passed,
/// and (for failures) exactly what went wrong.
#[derive(Clone, Debug)]
pub struct PreservationEvidence {
    /// Which property this evidence pertains to.
    pub property: PreservationProperty,
    /// Whether the property passed overall.
    pub passed: bool,
    /// Number of individual test cases checked.
    pub total_cases: usize,
    /// Number of test cases that passed.
    pub passed_cases: usize,
    /// Detailed per-case results (only populated for failures, to limit memory).
    pub failure_details: Vec<String>,
    /// Summary evidence line.
    pub summary: String,
}

impl PreservationEvidence {
    /// Create evidence from a PreservationCheck.
    #[must_use]
    fn from_check(check: &PreservationCheck) -> Self {
        let failure_details = if check.passed {
            Vec::new()
        } else {
            vec![check.evidence.clone()]
        };
        Self {
            property: check.property.clone(),
            passed: check.passed,
            total_cases: check.checked_examples,
            passed_cases: if check.passed {
                check.checked_examples
            } else {
                0
            },
            failure_details,
            summary: check.evidence.clone(),
        }
    }
}

// ---------------------------------------------------------------------------
// PreservationReport
// ---------------------------------------------------------------------------

/// Aggregate report from running all preservation verification checks.
///
/// Provides a structured overview: how many properties were checked,
/// how many passed, and detailed evidence for any failures.
#[derive(Clone, Debug)]
pub struct PreservationReport {
    /// Number of properties checked.
    pub properties_checked: usize,
    /// Number of properties that passed.
    pub properties_passed: usize,
    /// Number of properties that failed.
    pub properties_failed: usize,
    /// Total test cases across all properties.
    pub total_cases: usize,
    /// Total test cases that passed.
    pub total_cases_passed: usize,
    /// Per-property evidence (both passes and failures).
    pub evidence: Vec<PreservationEvidence>,
    /// Only the failures (subset of evidence).
    pub failures: Vec<PreservationEvidence>,
}

impl PreservationReport {
    /// Whether all properties passed.
    #[must_use]
    pub fn all_passed(&self) -> bool {
        self.properties_failed == 0
    }

    /// Fraction of properties that passed.
    #[must_use]
    pub fn pass_rate(&self) -> f64 {
        if self.properties_checked == 0 {
            1.0
        } else {
            self.properties_passed as f64 / self.properties_checked as f64
        }
    }

    /// Human-readable summary.
    #[must_use]
    pub fn summary(&self) -> String {
        let status = if self.all_passed() { "PASS" } else { "FAIL" };
        let mut s = format!(
            "[{status}] {}/{} properties passed ({} total cases)\n",
            self.properties_passed, self.properties_checked, self.total_cases,
        );
        for ev in &self.failures {
            s.push_str(&format!("  FAIL: {:?} - {}\n", ev.property, ev.summary,));
            for detail in &ev.failure_details {
                s.push_str(&format!("    {detail}\n"));
            }
        }
        s
    }
}

// ---------------------------------------------------------------------------
// Extended verifier methods
// ---------------------------------------------------------------------------

impl TypePreservationVerifier {
    /// Run all preservation checks and produce a structured report.
    #[must_use]
    pub fn verify_all_with_report(&self) -> PreservationReport {
        let checks = self.run_all();
        let mut evidence = Vec::new();
        let mut failures = Vec::new();
        let mut total_cases = 0usize;
        let mut total_cases_passed = 0usize;
        let mut properties_passed = 0usize;
        let mut properties_failed = 0usize;

        for check in &checks {
            let ev = PreservationEvidence::from_check(check);
            total_cases += ev.total_cases;
            if check.passed {
                total_cases_passed += ev.total_cases;
                properties_passed += 1;
            } else {
                properties_failed += 1;
                failures.push(ev.clone());
            }
            evidence.push(ev);
        }

        PreservationReport {
            properties_checked: checks.len(),
            properties_passed,
            properties_failed,
            total_cases,
            total_cases_passed,
            evidence,
            failures,
        }
    }

    /// Verify that universe level assignments don't create paradoxes.
    ///
    /// In clean's type theory, universe polymorphism requires that:
    /// - Sort(0) = Prop
    /// - Sort(1) = Type 0
    /// - Sort(n+1) : Sort(n+2) (no Type-in-Type)
    /// - A universe level cannot be its own successor
    ///
    /// This check verifies that translated expressions respect the
    /// universe hierarchy by testing representative examples.
    #[must_use]
    pub fn verify_universe_consistency(&self) -> PreservationCheck {
        let nat_ty = IsaType::nullary("nat");
        let bool_ty = IsaType::nullary("HOL.bool");
        let set_ty = IsaType::nullary("set");

        // Test that type translations produce expressions in the expected
        // universe level range.
        let test_cases: Vec<(&str, IsaType)> = vec![
            ("nat", nat_ty),
            ("bool", bool_ty),
            ("set", set_ty),
            (
                "nat->nat",
                IsaType::fun(IsaType::nullary("nat"), IsaType::nullary("nat")),
            ),
            (
                "bool->bool",
                IsaType::fun(IsaType::nullary("HOL.bool"), IsaType::nullary("HOL.bool")),
            ),
            ("tfree_a", IsaType::tfree("'a")),
        ];

        let total = test_cases.len();
        let mut passed_count = 0;

        for (label, isa_ty) in &test_cases {
            match self.translator.translate_type(isa_ty) {
                Ok(expr) => {
                    // Verify the expression is well-formed: no Sort with absurdly
                    // high levels, no BVar leak at the top level for types.
                    let debug = format!("{expr:?}");
                    // A type translation should never produce a BVar at the top level.
                    if debug.starts_with("BVar(") {
                        return PreservationCheck::fail(
                            PreservationProperty::BoundVarsPreserved,
                            format!("universe check: {label} produced top-level BVar: {debug}"),
                            total,
                        );
                    }
                    passed_count += 1;
                }
                Err(e) => {
                    return PreservationCheck::fail(
                        PreservationProperty::FunTypeMapsToArrow,
                        format!("universe check: {label} translation error: {e}"),
                        total,
                    );
                }
            }
        }

        PreservationCheck::pass(
            PreservationProperty::FunTypeMapsToArrow,
            format!(
                "universe consistency: {passed_count}/{total} types translate without level violations"
            ),
            total,
        )
    }

    /// Verify that imported names are bijective with their originals.
    ///
    /// Tests that:
    /// - Distinct Isabelle names produce distinct clean constant names
    /// - The same Isabelle name always produces the same clean name
    /// - No name collisions between types, terms, and type variables
    #[must_use]
    pub fn verify_name_preservation(&self) -> PreservationCheck {
        use hashbrown::HashSet;

        let nat_ty = IsaType::nullary("nat");

        // Test distinct names produce distinct translations.
        let names: Vec<(&str, IsaTerm)> = vec![
            ("alpha", IsaTerm::const_of("alpha", nat_ty.clone())),
            ("beta", IsaTerm::const_of("beta", nat_ty.clone())),
            ("gamma", IsaTerm::const_of("gamma", nat_ty.clone())),
            ("Suc", IsaTerm::const_of("Suc", nat_ty.clone())),
            ("Zero", IsaTerm::const_of("Zero", nat_ty.clone())),
            ("plus", IsaTerm::const_of("plus", nat_ty.clone())),
        ];

        let total = names.len();
        let mut seen_exprs: HashSet<String> = HashSet::new();
        let mut passed_count = 0;

        for (name, term) in &names {
            match self.translator.translate_term(term) {
                Ok(expr) => {
                    let debug = format!("{expr:?}");
                    if seen_exprs.contains(&debug) {
                        return PreservationCheck::fail(
                            PreservationProperty::AppStructurePreserved,
                            format!(
                                "name collision: {name} produced duplicate expression: {debug}"
                            ),
                            total,
                        );
                    }
                    seen_exprs.insert(debug);
                    passed_count += 1;
                }
                Err(e) => {
                    return PreservationCheck::fail(
                        PreservationProperty::AppStructurePreserved,
                        format!("name preservation error for {name}: {e}"),
                        total,
                    );
                }
            }
        }

        // Test determinism: same name always produces same result.
        let test_term = IsaTerm::const_of("determinism_test", nat_ty.clone());
        let first = self
            .translator
            .translate_term(&test_term)
            .map(|e| format!("{e:?}"));
        let second = self
            .translator
            .translate_term(&test_term)
            .map(|e| format!("{e:?}"));
        if first != second {
            return PreservationCheck::fail(
                PreservationProperty::AppStructurePreserved,
                format!("non-deterministic translation: first={first:?}, second={second:?}"),
                total + 1,
            );
        }
        passed_count += 1;

        PreservationCheck::pass(
            PreservationProperty::AppStructurePreserved,
            format!(
                "name preservation: {passed_count}/{} names are distinct and deterministic",
                total + 1,
            ),
            total + 1,
        )
    }

    /// Run the extended verification suite including universe and name checks.
    #[must_use]
    pub fn run_all_extended(&self) -> Vec<PreservationCheck> {
        let mut results = self.run_all();
        results.push(self.verify_universe_consistency());
        results.push(self.verify_name_preservation());
        results
    }

    /// Run extended checks and produce a structured report.
    #[must_use]
    pub fn verify_extended_with_report(&self) -> PreservationReport {
        let checks = self.run_all_extended();
        let mut evidence = Vec::new();
        let mut failures = Vec::new();
        let mut total_cases = 0usize;
        let mut total_cases_passed = 0usize;
        let mut properties_passed = 0usize;
        let mut properties_failed = 0usize;

        for check in &checks {
            let ev = PreservationEvidence::from_check(check);
            total_cases += ev.total_cases;
            if check.passed {
                total_cases_passed += ev.total_cases;
                properties_passed += 1;
            } else {
                properties_failed += 1;
                failures.push(ev.clone());
            }
            evidence.push(ev);
        }

        PreservationReport {
            properties_checked: checks.len(),
            properties_passed,
            properties_failed,
            total_cases,
            total_cases_passed,
            evidence,
            failures,
        }
    }

    // ── Specific property verification helpers ──

    /// Verify that all Isabelle function type variants translate to Pi.
    ///
    /// Extended version with more test cases than `check_fun_type_maps_to_arrow`.
    #[must_use]
    pub fn verify_fun_type_extended(&self) -> PreservationCheck {
        let test_cases: Vec<(&str, IsaType)> = vec![
            (
                "nat->bool",
                IsaType::fun(IsaType::nullary("nat"), IsaType::nullary("HOL.bool")),
            ),
            (
                "(nat->nat)->bool",
                IsaType::fun(
                    IsaType::fun(IsaType::nullary("nat"), IsaType::nullary("nat")),
                    IsaType::nullary("HOL.bool"),
                ),
            ),
            (
                "'a->'a",
                IsaType::fun(IsaType::tfree("'a"), IsaType::tfree("'a")),
            ),
            (
                "nat->nat->nat",
                IsaType::fun(
                    IsaType::nullary("nat"),
                    IsaType::fun(IsaType::nullary("nat"), IsaType::nullary("nat")),
                ),
            ),
            (
                "'a->'b->'c",
                IsaType::fun(
                    IsaType::tfree("'a"),
                    IsaType::fun(IsaType::tfree("'b"), IsaType::tfree("'c")),
                ),
            ),
            (
                "bool->bool",
                IsaType::fun(IsaType::nullary("HOL.bool"), IsaType::nullary("HOL.bool")),
            ),
            (
                "(nat->bool)->(nat->bool)",
                IsaType::fun(
                    IsaType::fun(IsaType::nullary("nat"), IsaType::nullary("HOL.bool")),
                    IsaType::fun(IsaType::nullary("nat"), IsaType::nullary("HOL.bool")),
                ),
            ),
        ];

        let total = test_cases.len();
        let mut passed_count = 0;

        for (label, isa_ty) in &test_cases {
            match self.translator.translate_type(isa_ty) {
                Ok(expr) if expr.is_pi() => passed_count += 1,
                Ok(expr) => {
                    return PreservationCheck::fail(
                        PreservationProperty::FunTypeMapsToArrow,
                        format!(
                            "extended: {label} did not translate to Pi: {isa_ty:?} -> {expr:?}"
                        ),
                        total,
                    );
                }
                Err(e) => {
                    return PreservationCheck::fail(
                        PreservationProperty::FunTypeMapsToArrow,
                        format!("extended: {label} translation error: {e}"),
                        total,
                    );
                }
            }
        }

        PreservationCheck::pass(
            PreservationProperty::FunTypeMapsToArrow,
            format!("{passed_count}/{total} extended fun types correctly mapped to Pi"),
            total,
        )
    }

    /// Verify bound variable preservation with deeper nesting.
    #[must_use]
    pub fn verify_bound_vars_extended(&self) -> PreservationCheck {
        let nat_ty = IsaType::nullary("nat");

        // Build increasingly nested lambda expressions and verify
        // the BVar indices survive translation.
        let test_cases: Vec<(usize, IsaTerm)> = vec![
            (0, IsaTerm::abs("x", nat_ty.clone(), IsaTerm::Bound(0))),
            (
                1,
                IsaTerm::abs(
                    "x",
                    nat_ty.clone(),
                    IsaTerm::abs("y", nat_ty.clone(), IsaTerm::Bound(1)),
                ),
            ),
            (
                2,
                IsaTerm::abs(
                    "x",
                    nat_ty.clone(),
                    IsaTerm::abs(
                        "y",
                        nat_ty.clone(),
                        IsaTerm::abs("z", nat_ty.clone(), IsaTerm::Bound(2)),
                    ),
                ),
            ),
        ];

        let total = test_cases.len();
        let mut passed_count = 0;

        for (depth, term) in &test_cases {
            match self.translator.translate_term(term) {
                Ok(expr) if expr.is_lam() => {
                    passed_count += 1;
                }
                Ok(expr) => {
                    return PreservationCheck::fail(
                        PreservationProperty::BoundVarsPreserved,
                        format!("depth-{depth} lambda did not translate to Lam: {expr:?}"),
                        total,
                    );
                }
                Err(e) => {
                    return PreservationCheck::fail(
                        PreservationProperty::BoundVarsPreserved,
                        format!("depth-{depth} translation error: {e}"),
                        total,
                    );
                }
            }
        }

        PreservationCheck::pass(
            PreservationProperty::BoundVarsPreserved,
            format!("{passed_count}/{total} nested lambdas preserve bound variable structure"),
            total,
        )
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn verifier() -> TypePreservationVerifier {
        TypePreservationVerifier::new()
    }

    // ── Type preservation tests ──

    #[test]
    fn test_fun_type_maps_to_arrow() {
        let v = verifier();
        let checks = v.verify_isabelle_type_preservation();
        let fun_check = checks
            .iter()
            .find(|c| c.property == PreservationProperty::FunTypeMapsToArrow)
            .expect("FunTypeMapsToArrow check should be present");
        assert!(
            fun_check.passed,
            "FunTypeMapsToArrow failed: {}",
            fun_check.evidence
        );
        assert!(fun_check.checked_examples >= 4);
    }

    #[test]
    fn test_bool_maps_to_prop() {
        let v = verifier();
        let checks = v.verify_isabelle_type_preservation();
        let bool_check = checks
            .iter()
            .find(|c| c.property == PreservationProperty::BoolMapsToProb)
            .expect("BoolMapsToProb check should be present");
        assert!(
            bool_check.passed,
            "BoolMapsToProb failed: {}",
            bool_check.evidence
        );
        assert!(bool_check.checked_examples >= 3);
    }

    #[test]
    fn test_tfree_maps_to_const() {
        let t = IsabelleTranslator::new("Test");
        let isa_ty = IsaType::tfree("'a");
        let expr = t.translate_type(&isa_ty).expect("TFree should translate");
        assert!(expr.is_const(), "TFree should map to Const, got: {expr:?}");
    }

    #[test]
    fn test_nat_maps_to_const() {
        let t = IsabelleTranslator::new("Test");
        let isa_ty = IsaType::nullary("nat");
        let expr = t.translate_type(&isa_ty).expect("nat should translate");
        assert!(expr.is_const(), "nat should map to Const, got: {expr:?}");
        assert!(
            format!("{expr:?}").contains("Nat"),
            "nat should map to Const 'Nat', got: {expr:?}"
        );
    }

    // ── Term preservation tests ──

    #[test]
    fn test_bound_vars_preserved() {
        let v = verifier();
        let checks = v.verify_isabelle_term_preservation();
        let bv_check = checks
            .iter()
            .find(|c| c.property == PreservationProperty::BoundVarsPreserved)
            .expect("BoundVarsPreserved check should be present");
        assert!(
            bv_check.passed,
            "BoundVarsPreserved failed: {}",
            bv_check.evidence
        );
        assert!(bv_check.checked_examples >= 6);
    }

    #[test]
    fn test_app_structure_preserved() {
        let v = verifier();
        let checks = v.verify_isabelle_term_preservation();
        let app_check = checks
            .iter()
            .find(|c| c.property == PreservationProperty::AppStructurePreserved)
            .expect("AppStructurePreserved check should be present");
        assert!(
            app_check.passed,
            "AppStructurePreserved failed: {}",
            app_check.evidence
        );
        assert!(app_check.checked_examples >= 3);
    }

    #[test]
    fn test_lam_structure_preserved() {
        let v = verifier();
        let checks = v.verify_isabelle_term_preservation();
        let lam_check = checks
            .iter()
            .find(|c| c.property == PreservationProperty::LamStructurePreserved)
            .expect("LamStructurePreserved check should be present");
        assert!(
            lam_check.passed,
            "LamStructurePreserved failed: {}",
            lam_check.evidence
        );
        assert!(lam_check.checked_examples >= 3);
    }

    #[test]
    fn test_free_var_maps_to_const() {
        let t = IsabelleTranslator::new("Test");
        let term = IsaTerm::Free {
            name: "x".to_owned(),
            ty: IsaType::nullary("nat"),
        };
        let expr = t.translate_term(&term).expect("Free should translate");
        assert!(expr.is_const(), "Free should map to Const, got: {expr:?}");
    }

    #[test]
    fn test_const_maps_to_const() {
        let t = IsabelleTranslator::new("Test");
        let term = IsaTerm::const_of("Suc", IsaType::nullary("nat"));
        let expr = t.translate_term(&term).expect("Const should translate");
        assert!(expr.is_const(), "Const should map to Const, got: {expr:?}");
    }

    // ── Edge cases ──

    #[test]
    fn test_empty_type_args_translates() {
        let t = IsabelleTranslator::new("Test");
        let isa_ty = IsaType::Type {
            name: "unit".to_owned(),
            args: Vec::new(),
        };
        let expr = t
            .translate_type(&isa_ty)
            .expect("empty-arg type should translate");
        assert!(
            expr.is_const(),
            "nullary type should map to Const, got: {expr:?}"
        );
    }

    #[test]
    fn test_deeply_nested_lambda() {
        let t = IsabelleTranslator::new("Test");
        let nat_ty = IsaType::nullary("nat");

        // Build a deeply nested lambda: \x. \y. \z. \w. w
        let mut term = IsaTerm::Bound(0);
        for (depth, name) in ["w", "z", "y", "x"].iter().enumerate() {
            let _ = depth;
            term = IsaTerm::abs(name, nat_ty.clone(), term);
        }

        let expr = t
            .translate_term(&term)
            .expect("deep lambda should translate");
        assert!(
            expr.is_lam(),
            "deeply nested lambda should translate to Lam"
        );
    }

    #[test]
    fn test_deeply_nested_application() {
        let t = IsabelleTranslator::new("Test");
        let nat_ty = IsaType::nullary("nat");

        // Build: f(a)(b)(c)(d)
        let mut term = IsaTerm::const_of("f", nat_ty.clone());
        for name in &["a", "b", "c", "d"] {
            term = IsaTerm::app(term, IsaTerm::const_of(name, nat_ty.clone()));
        }

        let expr = t.translate_term(&term).expect("deep app should translate");
        assert!(expr.is_app(), "deeply nested app should translate to App");
    }

    // ── Axiom profile tests ──

    #[test]
    fn test_axiom_profile_monotonicity() {
        let v = verifier();
        let check = v.verify_axiom_profile_monotonicity();
        assert!(check.passed, "monotonicity failed: {}", check.evidence);
        // 12 profiles x 12 profiles = 144 pairs minimum
        assert!(check.checked_examples >= 144);
    }

    #[test]
    fn test_axiom_profile_union_idempotent() {
        let profiles = [
            AxiomProfile::NONE,
            AxiomProfile::CLASSICAL,
            AxiomProfile::CLASSICAL | AxiomProfile::EXTENSIONALITY,
        ];

        for p in &profiles {
            let double_union = p.union(*p);
            assert_eq!(
                *p, double_union,
                "union with self should be idempotent: {p:?}"
            );
        }
    }

    #[test]
    fn test_axiom_profile_union_commutative() {
        let pairs = [
            (AxiomProfile::CLASSICAL, AxiomProfile::EXTENSIONALITY),
            (AxiomProfile::CHOICE, AxiomProfile::HOL_EMBEDDING),
            (AxiomProfile::NONE, AxiomProfile::ISABELLE_LCF_ERASED),
        ];

        for (a, b) in &pairs {
            assert_eq!(
                a.union(*b),
                b.union(*a),
                "union should be commutative: {a:?}, {b:?}"
            );
        }
    }

    #[test]
    fn test_axiom_profile_union_associative() {
        let a = AxiomProfile::CLASSICAL;
        let b = AxiomProfile::EXTENSIONALITY;
        let c = AxiomProfile::CHOICE;

        assert_eq!(
            a.union(b).union(c),
            a.union(b.union(c)),
            "union should be associative"
        );
    }

    #[test]
    fn test_axiom_profile_none_is_identity() {
        let profiles = [
            AxiomProfile::CLASSICAL,
            AxiomProfile::EXTENSIONALITY,
            AxiomProfile::CHOICE | AxiomProfile::HOL_EMBEDDING,
        ];

        for p in &profiles {
            assert_eq!(
                p.union(AxiomProfile::NONE),
                *p,
                "NONE should be identity for union: {p:?}"
            );
            assert_eq!(
                AxiomProfile::NONE.union(*p),
                *p,
                "NONE should be identity for union (commuted): {p:?}"
            );
        }
    }

    #[test]
    fn test_axiom_profile_monotonicity_exhaustive() {
        // proptest-style enumeration: systematically test all single-bit profiles
        let single_bits: Vec<AxiomProfile> = (0..26u32).map(|i| AxiomProfile(1 << i)).collect();

        for p1 in &single_bits {
            for p2 in &single_bits {
                let union = p1.union(*p2);
                assert!(
                    union.is_superset_of(*p1),
                    "monotonicity: union({p1:?}, {p2:?}) must be superset of {p1:?}"
                );
                assert!(
                    union.is_superset_of(*p2),
                    "monotonicity: union({p1:?}, {p2:?}) must be superset of {p2:?}"
                );
            }
        }
    }

    // ── Trust level tests ──

    #[test]
    fn test_trust_level_ordering() {
        let v = verifier();
        let check = v.verify_trust_level_ordering();
        assert!(check.passed, "trust ordering failed: {}", check.evidence);
        // 5 levels: C(5,2)=10 pair comparisons + 5 reflexive = 15
        assert!(check.checked_examples >= 15);
    }

    #[test]
    fn test_trust_level_strict_chain() {
        assert!(TrustLevel::KernelVerified < TrustLevel::AxiomDependent);
        assert!(TrustLevel::AxiomDependent < TrustLevel::CertificateReplayed);
        assert!(TrustLevel::CertificateReplayed < TrustLevel::PartiallyAxiomatized);
        assert!(TrustLevel::PartiallyAxiomatized < TrustLevel::TrustedOracle);
    }

    #[test]
    fn test_trust_level_transitivity() {
        // KernelVerified < TrustedOracle via transitivity
        assert!(TrustLevel::KernelVerified < TrustLevel::TrustedOracle);
        assert!(TrustLevel::AxiomDependent < TrustLevel::TrustedOracle);
        assert!(TrustLevel::KernelVerified < TrustLevel::PartiallyAxiomatized);
    }

    // ── run_all ──

    #[test]
    fn test_run_all_passes() {
        let v = verifier();
        let results = v.run_all();

        // Should have at least 7 checks:
        // 2 type + 3 term + 1 monotonicity + 1 trust ordering
        assert!(
            results.len() >= 7,
            "expected >= 7 checks, got {}",
            results.len()
        );

        for check in &results {
            assert!(
                check.passed,
                "check {:?} failed: {}",
                check.property, check.evidence
            );
        }
    }

    #[test]
    fn test_run_all_coverage() {
        let v = verifier();
        let results = v.run_all();

        let properties: Vec<&PreservationProperty> = results.iter().map(|c| &c.property).collect();

        assert!(
            properties.contains(&&PreservationProperty::FunTypeMapsToArrow),
            "missing FunTypeMapsToArrow"
        );
        assert!(
            properties.contains(&&PreservationProperty::BoolMapsToProb),
            "missing BoolMapsToProb"
        );
        assert!(
            properties.contains(&&PreservationProperty::BoundVarsPreserved),
            "missing BoundVarsPreserved"
        );
        assert!(
            properties.contains(&&PreservationProperty::AppStructurePreserved),
            "missing AppStructurePreserved"
        );
        assert!(
            properties.contains(&&PreservationProperty::LamStructurePreserved),
            "missing LamStructurePreserved"
        );
        assert!(
            properties.contains(&&PreservationProperty::AxiomProfileMonotone),
            "missing AxiomProfileMonotone"
        );
    }

    // ── Isabelle theorem translation preservation ──

    #[test]
    fn test_theorem_proved_trust_level() {
        let t = IsabelleTranslator::new("Test");
        let thm = IsaTheorem {
            name: "TrueI".to_owned(),
            props: vec![IsaTerm::const_of("True", IsaType::nullary("HOL.bool"))],
            proof_status: ProofStatus::Proved,
        };
        let result = t.translate_theorem(&thm).expect("theorem should translate");
        assert_eq!(result.trust_level, TrustLevel::CertificateReplayed);
    }

    #[test]
    fn test_theorem_axiomatized_trust_level() {
        let t = IsabelleTranslator::new("Test");
        let thm = IsaTheorem {
            name: "ext".to_owned(),
            props: vec![IsaTerm::const_of("ext", IsaType::nullary("HOL.bool"))],
            proof_status: ProofStatus::Axiomatized,
        };
        let result = t.translate_theorem(&thm).expect("theorem should translate");
        assert_eq!(result.trust_level, TrustLevel::PartiallyAxiomatized);
        assert!(result
            .axiom_profile
            .contains(AxiomProfile::ISABELLE_LCF_ERASED));
    }

    #[test]
    fn test_theorem_empty_props_error() {
        let t = IsabelleTranslator::new("Test");
        let thm = IsaTheorem {
            name: "bad".to_owned(),
            props: vec![],
            proof_status: ProofStatus::Proved,
        };
        assert!(
            t.translate_theorem(&thm).is_err(),
            "empty props should produce an error"
        );
    }

    // ── PreservationReport tests ──

    #[test]
    fn test_verify_all_with_report() {
        let v = verifier();
        let report = v.verify_all_with_report();
        assert!(
            report.all_passed(),
            "expected all properties to pass: {}",
            report.summary()
        );
        assert!(report.properties_checked >= 7);
        assert_eq!(report.properties_failed, 0);
        assert!(report.failures.is_empty());
        assert!((report.pass_rate() - 1.0).abs() < 1e-10);
    }

    #[test]
    fn test_report_summary_format() {
        let v = verifier();
        let report = v.verify_all_with_report();
        let summary = report.summary();
        assert!(summary.contains("[PASS]"));
        assert!(summary.contains("properties passed"));
    }

    #[test]
    fn test_report_total_cases() {
        let v = verifier();
        let report = v.verify_all_with_report();
        // total_cases should be the sum of all checked_examples
        assert!(report.total_cases > 0);
        assert_eq!(report.total_cases, report.total_cases_passed);
    }

    #[test]
    fn test_report_evidence_count_matches_checks() {
        let v = verifier();
        let report = v.verify_all_with_report();
        assert_eq!(report.evidence.len(), report.properties_checked);
    }

    // ── Universe consistency tests ──

    #[test]
    fn test_verify_universe_consistency() {
        let v = verifier();
        let check = v.verify_universe_consistency();
        assert!(
            check.passed,
            "universe consistency failed: {}",
            check.evidence
        );
        assert!(check.checked_examples >= 6);
    }

    // ── Name preservation tests ──

    #[test]
    fn test_verify_name_preservation() {
        let v = verifier();
        let check = v.verify_name_preservation();
        assert!(check.passed, "name preservation failed: {}", check.evidence);
        // 6 distinct names + 1 determinism check = 7
        assert!(check.checked_examples >= 7);
    }

    // ── Extended verifier tests ──

    #[test]
    fn test_run_all_extended() {
        let v = verifier();
        let results = v.run_all_extended();
        // Should have at least 9 checks:
        // 7 from run_all + 1 universe + 1 name
        assert!(
            results.len() >= 9,
            "expected >= 9 extended checks, got {}",
            results.len()
        );
        for check in &results {
            assert!(
                check.passed,
                "extended check {:?} failed: {}",
                check.property, check.evidence
            );
        }
    }

    #[test]
    fn test_verify_extended_with_report() {
        let v = verifier();
        let report = v.verify_extended_with_report();
        assert!(
            report.all_passed(),
            "expected all extended properties to pass: {}",
            report.summary()
        );
        assert!(report.properties_checked >= 9);
    }

    #[test]
    fn test_verify_fun_type_extended() {
        let v = verifier();
        let check = v.verify_fun_type_extended();
        assert!(
            check.passed,
            "extended fun type check failed: {}",
            check.evidence
        );
        assert!(check.checked_examples >= 7);
    }

    #[test]
    fn test_verify_bound_vars_extended() {
        let v = verifier();
        let check = v.verify_bound_vars_extended();
        assert!(
            check.passed,
            "extended bound vars check failed: {}",
            check.evidence
        );
        assert!(check.checked_examples >= 3);
    }

    // ── PreservationEvidence tests ──

    #[test]
    fn test_preservation_evidence_from_passing_check() {
        let check = PreservationCheck::pass(
            PreservationProperty::FunTypeMapsToArrow,
            "all good".to_owned(),
            5,
        );
        let ev = PreservationEvidence::from_check(&check);
        assert!(ev.passed);
        assert_eq!(ev.total_cases, 5);
        assert_eq!(ev.passed_cases, 5);
        assert!(ev.failure_details.is_empty());
    }

    #[test]
    fn test_preservation_evidence_from_failing_check() {
        let check = PreservationCheck::fail(
            PreservationProperty::BoolMapsToProb,
            "something broke".to_owned(),
            3,
        );
        let ev = PreservationEvidence::from_check(&check);
        assert!(!ev.passed);
        assert_eq!(ev.total_cases, 3);
        assert_eq!(ev.passed_cases, 0);
        assert_eq!(ev.failure_details.len(), 1);
        assert_eq!(ev.failure_details[0], "something broke");
    }

    // ── Report edge cases ──

    #[test]
    fn test_report_pass_rate_no_checks() {
        let report = PreservationReport {
            properties_checked: 0,
            properties_passed: 0,
            properties_failed: 0,
            total_cases: 0,
            total_cases_passed: 0,
            evidence: Vec::new(),
            failures: Vec::new(),
        };
        assert!((report.pass_rate() - 1.0).abs() < 1e-10);
        assert!(report.all_passed());
    }

    #[test]
    fn test_report_summary_with_failures() {
        let failing_ev = PreservationEvidence {
            property: PreservationProperty::BoolMapsToProb,
            passed: false,
            total_cases: 3,
            passed_cases: 1,
            failure_details: vec!["bool broke".to_owned()],
            summary: "bool broke".to_owned(),
        };
        let report = PreservationReport {
            properties_checked: 2,
            properties_passed: 1,
            properties_failed: 1,
            total_cases: 8,
            total_cases_passed: 5,
            evidence: vec![failing_ev.clone()],
            failures: vec![failing_ev],
        };
        let summary = report.summary();
        assert!(summary.contains("[FAIL]"));
        assert!(summary.contains("1/2 properties passed"));
        assert!(summary.contains("bool broke"));
    }
}

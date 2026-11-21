// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Checked positive-divisor agreement between the original subtraction and
//! restoring evaluators. This extends a vocabulary; it never changes either
//! evaluator, admits a program or drops the explicit bounded-fuel hypothesis.

use std::borrow::Cow;
use std::collections::HashSet;

use clean_kernel::{CertificationAudit, ConstantKind, Declaration, Expr, Name, TypeChecker};

use crate::spec::{SpecError, Specification};

mod canonical_arithmetic;
mod canonical_division;
#[cfg(test)]
mod canonical_division_tests;
#[path = "eval_ir_integer_normalization_v1.rs"]
mod integer_normalization;
#[cfg(test)]
mod output_bound_tests;
mod output_bounds;
#[cfg(test)]
mod shift_tests;
mod shifts;
mod shifts64;
#[cfg(test)]
mod shifts64_tests;
mod sources_a;
mod sources_b;
#[cfg(test)]
#[path = "eval_ir_positive_division_telescope_tests.rs"]
mod telescope_tests;
#[cfg(test)]
mod tests;
mod total_division;
#[cfg(test)]
mod total_division_test_support;
mod unsigned_compare;
#[cfg(test)]
mod unsigned_compare_tests;
mod word_add;
#[cfg(test)]
mod word_add_tests;
mod word_and_loop;
mod word_and_scalar;
#[cfg(test)]
mod word_and_tests;
mod word_lshr_canonical;
#[cfg(test)]
mod word_lshr_canonical_tests;
mod word_shl_canonical;
#[cfg(test)]
mod word_shl_canonical_boundaries;
#[cfg(test)]
mod word_shl_canonical_tests;
mod word_xor;
mod word_xor_loop;
mod word_xor_scalar;
#[cfg(test)]
mod word_xor_tests;

const AGREEMENT_ROOTS: [&str; 2] = ["ir_div_agrees_at_fuel", "ir_rem_agrees_at_fuel"];
const SHIFT_ROOTS: [&str; 5] = [
    "ir_byte_lshr_u64_by_three_v1",
    "ir_byte_ashr_i64_by_three_v1",
    "ir_byte_lshr_u64_max_by_three_v1",
    "ir_byte_ashr_i64_negative_one_by_three_v1",
    "ir_byte_ashr_i64_min_by_three_v1",
];

fn laws() -> impl Iterator<Item = (&'static str, &'static str)> + Clone {
    sources_a::LAWS.iter().chain(sources_b::LAWS).copied()
}

fn with_prerequisite(
    rows: impl Iterator<Item = (&'static str, &'static str)> + Clone,
) -> impl Iterator<Item = (&'static str, &'static str)> + Clone {
    // The historical full model has this checked Bool eliminator, but the
    // ordinary ByteV1 vocabulary deliberately omits its crystal-specific stage.
    // Reuse its original source without installing that unrelated stage.
    std::iter::once((
        "ir_bool_false_ne_true",
        super::eval_ir_lzd_fresh::bool_false_ne_true_source(),
    ))
    .chain(rows)
}

// Historical probes use the original dependency-scoped foundation spelling.
// Keep their statements and terms, spelling supplied type/motive arguments
// explicitly. Production uses the existing EvalIR bridge instead of introducing
// the foundation-only Eq.cong into the ordinary prelude.
#[cfg(test)]
pub(super) fn source_for_probe(name: &str) -> Option<&'static str> {
    laws()
        .find_map(|(key, source)| (key == name).then_some(source))
        .or_else(|| total_division::source_for_probe(name))
}

fn production_source(source: &'static str) -> Cow<'static, str> {
    if source.contains("Eq.cong") {
        Cow::Owned(source.replace("Eq.cong", "ir_eq_cong"))
    } else {
        Cow::Borrowed(source)
    }
}

fn preflight(
    spec: &Specification,
    rows: impl Iterator<Item = (&'static str, &'static str)>,
) -> Result<(), SpecError> {
    let mut names = HashSet::new();
    for (name, _) in rows {
        if !names.insert(name)
            || spec.get_definition(name).is_some()
            || spec.env().get_const(&Name::from_string(name)).is_some()
        {
            return Err(SpecError::EnvError(format!(
                "positive-division package name collision: {name}"
            )));
        }
    }
    Ok(())
}

/// Recheck the exact installed declaration, not cached specification metadata.
fn verify_storage(spec: &Specification, root: &str) -> Result<(), SpecError> {
    let name = Name::from_string(root);
    let definition = spec
        .get_definition(root)
        .ok_or_else(|| SpecError::UnknownDefinition(root.into()))?;
    let info = spec
        .env()
        .get_const(&name)
        .ok_or_else(|| SpecError::UnknownDefinition(root.into()))?;
    let value = info
        .value
        .as_ref()
        .ok_or_else(|| SpecError::MissingElaboration(root.into()))?;
    if definition.name != root
        || definition.is_axiom
        || definition.elaborated_type.as_ref() != Some(&info.type_)
        || definition.elaborated_value.as_ref() != Some(value)
        || info.type_.has_fvar_quick()
        || value.has_fvar_quick()
    {
        return Err(SpecError::TypeError(format!(
            "positive-division root {root} has inconsistent or open stored endpoints"
        )));
    }
    let declaration = match info.kind {
        ConstantKind::Definition => Declaration::Definition {
            name,
            level_params: info.level_params.clone(),
            type_: info.type_.clone(),
            value: value.clone(),
            is_reducible: info.is_reducible,
        },
        ConstantKind::Theorem => Declaration::Theorem {
            name,
            level_params: info.level_params.clone(),
            type_: info.type_.clone(),
            value: value.clone(),
        },
        ConstantKind::Opaque | ConstantKind::Axiom => {
            return Err(SpecError::TypeError(format!(
                "positive-division root {root} is not a value-bearing definition/theorem"
            )));
        }
    };
    spec.verify_definition(root)?;
    spec.env()
        .check_decl_readonly_strict(&declaration)
        .map_err(|error| SpecError::TypeError(format!("{root}: {error}")))?;
    for (kind, closure) in [
        ("axioms", spec.env().axiom_deps(&info.name)),
        ("trust markers", spec.env().trust_marker_deps(&info.name)),
    ] {
        let closure = closure.ok_or_else(|| SpecError::UnknownDefinition(root.into()))?;
        if !closure.is_empty() {
            return Err(SpecError::TypeError(format!(
                "positive-division root {root} depends on {kind}: {closure:?}"
            )));
        }
    }
    Ok(())
}

/// Include the named root's stored declaration and complete authority closure.
/// Computational roots use a typed reflexive judgment, not a claim that their
/// function type is Prop. Package admission audits the two agreement roots and
/// requires their combined closure to include every installed helper.
fn verify_root(spec: &Specification, root: &str) -> Result<CertificationAudit, SpecError> {
    verify_storage(spec, root)?;
    let info = spec
        .env()
        .get_const(&Name::from_string(root))
        .ok_or_else(|| SpecError::UnknownDefinition(root.into()))?;
    let term = Expr::const_(
        info.name.clone(),
        info.level_params
            .iter()
            .map(|name| clean_kernel::Level::param(name.clone()))
            .collect::<Vec<_>>(),
    );
    let mut checker = TypeChecker::new(spec.env());
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    if let Some(Some(value)) = spec.env().get_option("maxHeartbeats") {
        if let Ok(limit) = value.parse::<u32>() {
            checker.set_heartbeat_limit(limit);
        }
    }
    if let Some(Some(value)) = spec.env().get_option("tcMaxCacheEntries") {
        if let Ok(max) = value.parse::<usize>() {
            checker.set_max_cache_entries(max);
        }
    }
    let sort = checker
        .infer_sort(&info.type_)
        .map_err(|error| SpecError::TypeError(format!("{root}: {error}")))?;
    let (goal, proof) = if sort.is_zero() {
        (info.type_.clone(), term)
    } else {
        let goal = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![sort.clone()]),
            [info.type_.clone(), term.clone(), term.clone()],
        );
        let proof = Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![sort]),
            [info.type_.clone(), term],
        );
        (goal, proof)
    };
    let audit = spec.env().audit_certification(&goal, &proof);
    if !audit.is_certified() {
        return Err(SpecError::TypeError(format!(
            "positive-division root {root} failed strict rooted certification: {:?}",
            audit.issues
        )));
    }
    Ok(audit)
}

fn register_rows_and_check(
    spec: &mut Specification,
    rows: impl Iterator<Item = (&'static str, &'static str)> + Clone,
    roots: &[&str],
) -> Result<(), SpecError> {
    register_rows_and_check_described(
        spec,
        rows,
        roots,
        "constructive positive-divisor agreement at explicitly sufficient restoring fuel",
    )
}

fn register_rows_and_check_described(
    spec: &mut Specification,
    rows: impl Iterator<Item = (&'static str, &'static str)> + Clone,
    roots: &[&str],
    description: &str,
) -> Result<(), SpecError> {
    for (name, source) in rows.clone() {
        spec.add_recursive_def(
            &production_source(source),
            &format!("{name}: {description}"),
        )
        .map_err(|error| match error {
            SpecError::ParseError(message) => SpecError::ParseError(format!("{name}: {message}")),
            SpecError::ElabError(message) => SpecError::ElabError(format!("{name}: {message}")),
            SpecError::TypeError(message) => SpecError::TypeError(format!("{name}: {message}")),
            SpecError::EnvError(message) => SpecError::EnvError(format!("{name}: {message}")),
            // In particular, budget exhaustion is an unknown verdict, not a
            // mathematical rejection. Keep its typed outcome and bound intact.
            other => other,
        })?;
    }
    for (name, _) in rows.clone() {
        verify_storage(spec, name)?;
    }
    let mut covered = HashSet::new();
    for root in roots {
        covered.extend(verify_root(spec, root)?.dependencies);
    }
    for (name, _) in rows {
        if !covered.contains(&Name::from_string(name)) {
            return Err(SpecError::TypeError(format!(
                "positive-division helper {name} is outside the audited consumer closure"
            )));
        }
    }
    Ok(())
}

fn install_transactionally(
    spec: &mut Specification,
    rows: impl Iterator<Item = (&'static str, &'static str)> + Clone,
) -> Result<(), SpecError> {
    let rows = with_prerequisite(rows);
    preflight(spec, rows.clone())?;
    let mut candidate = spec.clone();
    register_rows_and_check(&mut candidate, rows, &AGREEMENT_ROOTS)?;
    *spec = candidate;
    Ok(())
}

fn install_shift_transactionally(
    spec: &mut Specification,
    rows: impl Iterator<Item = (&'static str, &'static str)> + Clone,
) -> Result<(), SpecError> {
    preflight(spec, rows.clone())?;
    let mut candidate = spec.clone();
    register_rows_and_check(&mut candidate, rows, &SHIFT_ROOTS)?;
    *spec = candidate;
    Ok(())
}

impl Specification {
    /// Install the fixed positive-division package atomically. Positive divisors
    /// are structural (`succ d`); the exact `m < divisor * 2^fuel` Boolean
    /// hypothesis remains explicit. Existing package names always refuse.
    /// The original checked Bool absurdity prerequisite is included; the
    /// historical 49-law table is unchanged. Default EvalIR/cache profiles and
    /// division-by-zero behavior are unchanged.
    /// The owner clone preserves its complete options/provenance/bookkeeping;
    /// external lazy-import materialization caches may warm but are not replaced.
    ///
    /// # Errors
    /// Collision, missing substrate, declaration or strict rooted audit refusal.
    pub(crate) fn install_eval_ir_positive_division_laws_v1_checked(
        &mut self,
    ) -> Result<(), SpecError> {
        install_transactionally(self, laws())
    }

    /// Add the actual U64 logical and I64 arithmetic shift-by-three laws to an
    /// owner with ByteV1 and the positive-division package already installed.
    /// The sole word premise is the full canonical 64-bit range; the arithmetic
    /// law preserves both sign branches. No evaluator or fault behavior changes.
    ///
    /// # Errors
    /// Collision, missing prerequisites, declaration or rooted audit refusal.
    pub(crate) fn install_eval_ir_u64_shift_by_three_laws_v1_checked(
        &mut self,
    ) -> Result<(), SpecError> {
        install_shift_transactionally(self, shifts::LAWS.iter().copied())
    }

    // A factory already owns its disposable vocabulary. Avoid a redundant
    // transaction clone: on failure the whole unreturned owner is discarded.
    pub(crate) fn into_positive_division_v1(mut self) -> Result<Self, SpecError> {
        let rows = with_prerequisite(laws());
        preflight(&self, rows.clone())?;
        register_rows_and_check(&mut self, rows, &AGREEMENT_ROOTS)?;
        Ok(self)
    }

    pub(crate) fn into_u64_shift_by_three_v1(mut self) -> Result<Self, SpecError> {
        preflight(&self, shifts::LAWS.iter().copied())?;
        register_rows_and_check(&mut self, shifts::LAWS.iter().copied(), &SHIFT_ROOTS)?;
        Ok(self)
    }
}

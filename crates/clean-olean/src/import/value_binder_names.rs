// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The `.olean` importer's half of the value binder name table
//! ([`clean_kernel::env::ValueForallBinderNames`], a per-name table of the
//! kernel environment): for each imported DEFINITION, how many leading `fun`
//! binders its value has and the names of the `∀` binders directly under
//! them, read off the raw `.olean` value (the direct path) or the parsed
//! value (the `ParsedModule` path). The elaborator fills the same table for
//! the definitions it elaborates and reads it to bind a named argument.

use clean_kernel::env::Environment;
use clean_kernel::name::Name;

use super::binder_spine::BinderSpine;
use super::ImportError;
use crate::expr::{expr_tags, ParsedExpr};
use crate::module::{ConstantKind, ParsedConstant};
use crate::region::{is_ptr, CompactedRegion};

/// The number of leading `lam` nodes of the expression at `ptr`, then the
/// names of the `forallE` nodes directly under them, outermost first
/// (`mdata` wrappers on the spine are looked through).
fn read_value_shape(
    region: &CompactedRegion<'_>,
    mut ptr: u64,
    constant: &str,
) -> Result<(usize, Vec<String>), ImportError> {
    let mut lambdas = 0;
    let mut names = Vec::new();
    let mut spine = BinderSpine::new(region, constant)?;
    while is_ptr(ptr) {
        spine.visit(ptr)?;
        let offset = region.ptr_to_offset(ptr)?;
        let header = region.read_header_at(offset)?;
        CompactedRegion::require_expr_fields(&header, offset)?;
        let field_base = offset + 8;
        match header.tag {
            // Layout of both binders: name, type, body (see
            // `convert_expr_direct`). A lambda under a `∀` ends the walk.
            expr_tags::LAM if names.is_empty() => {
                lambdas += 1;
                ptr = region.read_u64_at(field_base + 16)?;
            }
            expr_tags::FORALL_E => {
                let name_ptr = region.read_u64_at(field_base)?;
                names.push(region.resolve_name_ptr(name_ptr)?);
                ptr = region.read_u64_at(field_base + 16)?;
            }
            expr_tags::MDATA => {
                ptr = region.read_u64_at(field_base + 8)?;
            }
            _ => break,
        }
    }
    Ok((lambdas, names))
}

fn parsed_value_shape(value: &ParsedExpr) -> (usize, Vec<String>) {
    let mut lambdas = 0;
    let mut names = Vec::new();
    let mut e = value;
    loop {
        match e {
            ParsedExpr::Lam(_, _, body, _) if names.is_empty() => {
                lambdas += 1;
                e = body;
            }
            ParsedExpr::ForallE(name, _, body, _) => {
                names.push(name.clone());
                e = body;
            }
            ParsedExpr::MData(_, inner) => e = inner,
            _ => return (lambdas, names),
        }
    }
}

fn record_strings(env: &mut Environment, constant: &str, lambdas: usize, names: &[String]) {
    env.record_value_forall_binder_names(
        Name::interned(constant),
        lambdas,
        names.iter().map(|n| Name::interned(n)).collect(),
    );
}

/// Direct (zero-copy) path: record every DEFINITION of the module whose value
/// is a `∀` under its lambdas, reading the names straight from `region`.
pub(crate) fn record_value_binder_names_from_region<'a>(
    env: &mut Environment,
    region: &CompactedRegion<'_>,
    constants: impl IntoIterator<Item = (&'a str, &'a ConstantKind, u64)>,
) -> Result<(), ImportError> {
    for (name, kind, value_ptr) in constants {
        if !matches!(kind, ConstantKind::Definition) || value_ptr == 0 {
            continue;
        }
        let (lambdas, names) = read_value_shape(region, value_ptr, name)?;
        record_strings(env, name, lambdas, &names);
    }
    Ok(())
}

/// `ParsedModule` path: the same table, read off the parsed values.
pub(crate) fn record_value_binder_names_from_parsed(
    env: &mut Environment,
    constants: &[ParsedConstant],
) {
    for c in constants {
        if !matches!(c.kind, ConstantKind::Definition) {
            continue;
        }
        if let Some(value) = c.value.as_ref() {
            let (lambdas, names) = parsed_value_shape(value);
            record_strings(env, &c.name, lambdas, &names);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::ParsedBinderInfo;

    fn prop() -> ParsedExpr {
        ParsedExpr::Const("Prop".to_string(), vec![])
    }

    /// `fun α f => ∀ ⦃a₁ a₂⦄, body`: the shape of `Function.Injective`.
    fn injective_like() -> ParsedExpr {
        let forall_inner = ParsedExpr::ForallE(
            "a₂".to_string(),
            Box::new(prop()),
            Box::new(prop()),
            ParsedBinderInfo::StrictImplicit,
        );
        let forall_outer = ParsedExpr::ForallE(
            "a₁".to_string(),
            Box::new(prop()),
            Box::new(ParsedExpr::MData(Vec::new(), Box::new(forall_inner))),
            ParsedBinderInfo::StrictImplicit,
        );
        let lam_inner = ParsedExpr::Lam(
            "f".to_string(),
            Box::new(prop()),
            Box::new(forall_outer),
            ParsedBinderInfo::Default,
        );
        ParsedExpr::Lam(
            "α".to_string(),
            Box::new(prop()),
            Box::new(lam_inner),
            ParsedBinderInfo::Implicit,
        )
    }

    #[test]
    fn test_parsed_value_shape_counts_lambdas_then_names_the_foralls() {
        assert_eq!(
            parsed_value_shape(&injective_like()),
            (2, vec!["a₁".to_string(), "a₂".to_string()])
        );
    }

    #[test]
    fn test_parsed_value_shape_stops_at_a_lambda_under_a_forall() {
        let lam = ParsedExpr::Lam(
            "x".to_string(),
            Box::new(prop()),
            Box::new(prop()),
            ParsedBinderInfo::Default,
        );
        let forall = ParsedExpr::ForallE(
            "y".to_string(),
            Box::new(prop()),
            Box::new(lam),
            ParsedBinderInfo::Default,
        );
        assert_eq!(parsed_value_shape(&forall), (0, vec!["y".to_string()]));
    }

    #[test]
    fn test_recorded_value_shape_is_served_by_constant_and_empty_is_not_recorded() {
        let mut env = Environment::new();
        let inj = Name::from_string("Function.Injective");
        record_strings(
            &mut env,
            "Function.Injective",
            3,
            &["a₁".to_string(), "a₂".to_string()],
        );
        record_strings(&mut env, "id", 2, &[]);
        let got = env.get_value_forall_binder_names(&inj).expect("recorded");
        assert_eq!(got.lambdas, 3);
        assert_eq!(
            got.names
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>(),
            vec!["a₁".to_string(), "a₂".to_string()]
        );
        assert!(env
            .get_value_forall_binder_names(&Name::from_string("id"))
            .is_none());
    }
}

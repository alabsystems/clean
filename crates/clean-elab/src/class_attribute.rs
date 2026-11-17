// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Class target and parameter checks at the source registration boundary.
//! Based on Lean v4.35.0 Class.lean; this does not implement its universe metadata.

use clean_kernel::env::{ConstantKind, KernelClassInfo};
use clean_kernel::{BinderInfo, Environment, Expr, ExprKind, Name};
use clean_parser::Attribute;
use std::collections::HashSet;

use crate::ElabError;

fn marker(domain: &Expr, marker_name: &Name) -> bool {
    matches!(domain.kind(), ExprKind::App(function, _)
        if matches!(function.kind(), ExprKind::Const(name, _) if name == marker_name))
}

/// A collected public attribute retains its scope until authoritative validation.
#[derive(Clone, Debug)]
pub(crate) struct ClassAttribute {
    name: Name,
    non_global_scope: Option<&'static str>,
}

impl ClassAttribute {
    pub(crate) fn collect(name: &Name, attribute: &Attribute) -> Option<Self> {
        match attribute {
            Attribute::Class => Some(Self {
                name: name.clone(),
                non_global_scope: None,
            }),
            Attribute::Local(inner) | Attribute::Scoped(inner) => {
                let mut collected = Self::collect(name, inner)?;
                collected.non_global_scope = Some(match attribute {
                    Attribute::Local(_) => "local",
                    _ => "scoped",
                });
                Some(collected)
            }
            _ => None,
        }
    }
}

/// Validate the entire public packet before applying any attribute effects.
/// Duplicate targets in one packet are errors, just like already declared classes.
pub(crate) fn prepare_attributes(
    env: &Environment,
    attributes: &[ClassAttribute],
) -> Result<Vec<KernelClassInfo>, ElabError> {
    let mut names = HashSet::new();
    attributes
        .iter()
        .map(|attribute| {
            if let Some(scope) = attribute.non_global_scope {
                return Err(ElabError::InvalidClassAttributeScope { scope });
            }
            if env.is_class(&attribute.name) || !names.insert(attribute.name.clone()) {
                return Err(ElabError::ClassAlreadyDeclared {
                    name: attribute.name.clone(),
                });
            }
            declaration_metadata(env, &attribute.name)
        })
        .collect()
}

// Used by persistent source-kind controls as well as the public attribute path.
#[cfg(test)]
pub(crate) fn register(env: &mut Environment, name: &Name) -> Result<(), ElabError> {
    let attribute = ClassAttribute {
        name: name.clone(),
        non_global_scope: None,
    };
    for info in prepare_attributes(env, &[attribute])? {
        env.register_class(info);
    }
    Ok(())
}

/// A genuine new class may replace a prelude axiom's provisional metadata.
/// Public attributes use `prepare_attributes`, which refuses repeated registration.
pub(crate) fn register_new_declaration(
    env: &mut Environment,
    name: &Name,
) -> Result<(), ElabError> {
    let info = declaration_metadata(env, name)?;
    env.register_class(info);
    Ok(())
}

fn declaration_metadata(env: &Environment, name: &Name) -> Result<KernelClassInfo, ElabError> {
    let constant = env
        .get_const(name)
        .ok_or_else(|| ElabError::UnknownIdent(name.to_string()))?;
    let axiom = constant.kind == ConstantKind::Axiom
        && constant.value.is_none()
        && crate::source_kind::get(env, name) == Some(ConstantKind::Axiom)
        && env.get_constructor(name).is_none()
        && env.get_recursor(name).is_none()
        && env.get_quot(name).is_none();
    if env.is_staged_header(name) || (env.get_inductive(name).is_none() && !axiom) {
        return Err(ElabError::InvalidClassAttribute { name: name.clone() });
    }
    metadata_from_type(name, &constant.type_)
}

/// Check the elaborated telescope without reducing away parameter markers.
/// This is shared by unpublished class elaboration and authoritative attributes;
/// a local or namespace-shadowing `outParam` is not the global marker.
pub(crate) fn metadata_from_type(name: &Name, type_: &Expr) -> Result<KernelClassInfo, ElabError> {
    let out_marker = Name::from_string("outParam");
    let semi_marker = Name::from_string("semiOutParam");
    let mut out_params: Vec<usize> = Vec::new();
    let mut semi_out_params = Vec::new();
    let mut num_params = 0;
    let mut ty = type_;
    while let ExprKind::Pi(binder, domain, body) = ty.kind() {
        // Skipping enclosing Pis leaves each earlier parameter at this loose
        // index in the current domain. The kernel occurrence walker accounts
        // for binders *inside* that domain, including dependent subtype lambdas.
        let depends_on_output = out_params.iter().any(|position| {
            u32::try_from(num_params - 1 - position).is_ok_and(|index| domain.has_loose_bvar(index))
        });
        if marker(domain, &out_marker)
            || (depends_on_output && binder.info == BinderInfo::InstImplicit)
        {
            out_params.push(num_params);
        } else if depends_on_output {
            return Err(ElabError::InvalidClassOutParam {
                parameter: num_params + 1,
            });
        }
        if marker(domain, &semi_marker) {
            semi_out_params.push(num_params);
        }
        num_params += 1;
        ty = body;
    }
    Ok(KernelClassInfo {
        name: name.clone(),
        num_params,
        out_params,
        semi_out_params,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::Level;

    #[test]
    fn output_dependency_propagates_through_a_promoted_instance_identity() {
        let output = Expr::app(
            Expr::const_(Name::from_string("outParam"), vec![]),
            Expr::const_(Name::from_string("Nat"), vec![]),
        );
        let carrier = Expr::app(
            Expr::const_(Name::from_string("Carrier"), vec![]),
            Expr::bvar(0),
        );
        // The final domain mentions the immediately preceding instance only,
        // not the original output. Promotion must propagate that dependency.
        let projection = Expr::proj(Name::from_string("Carrier"), 0, Expr::bvar(0));
        let type_ = Expr::pi(
            BinderInfo::Default,
            output,
            Expr::pi(
                BinderInfo::InstImplicit,
                carrier,
                Expr::pi(BinderInfo::Default, projection, Expr::prop()),
            ),
        );
        assert!(matches!(
            metadata_from_type(&Name::from_string("C"), &type_),
            Err(ElabError::InvalidClassOutParam { parameter: 3 })
        ));
    }

    #[test]
    fn a_shadowing_input_identity_does_not_inherit_an_outputs_spelling() {
        let type_ = Expr::sort(Level::succ(Level::zero()));
        let output = Expr::app(
            Expr::const_(Name::from_string("outParam"), vec![]),
            type_.clone(),
        );
        // The third domain refers to the second parameter, not the first;
        // equal diagnostic binder names cannot change de Bruijn identity.
        let telescope = Expr::pi(
            BinderInfo::Default,
            output,
            Expr::pi(
                BinderInfo::Default,
                type_,
                Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::prop()),
            ),
        );
        let info = metadata_from_type(&Name::from_string("C"), &telescope).unwrap();
        assert_eq!(info.out_params, [0]);
        assert!(info.semi_out_params.is_empty());
    }
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Class target and parameter checks at the source registration boundary.
//! Based on Lean v4.35.0 Class.lean; this does not implement its universe metadata.

use clean_kernel::env::{ConstantKind, KernelClassInfo};
use clean_kernel::{BinderInfo, Environment, Expr, ExprKind, Name};

use crate::ElabError;

fn marker(domain: &Expr, marker_name: &Name) -> bool {
    matches!(domain.kind(), ExprKind::App(function, _)
        if matches!(function.kind(), ExprKind::Const(name, _) if name == marker_name))
}

pub(crate) fn register(env: &mut Environment, name: &Name) -> Result<(), ElabError> {
    if env.is_class(name) {
        return Err(ElabError::ClassAlreadyDeclared { name: name.clone() });
    }
    register_new_declaration(env, name)
}

/// Register a freshly kernel-admitted class declaration. Declaration admission
/// already rejects real name collisions; it may replace a prelude axiom shim
/// whose old class metadata must now be recomputed from the genuine telescope.
/// Attribute commands and annotations must instead use `register` above.
pub(crate) fn register_new_declaration(
    env: &mut Environment,
    name: &Name,
) -> Result<(), ElabError> {
    let constant = env
        .get_const(name)
        .ok_or_else(|| ElabError::UnknownIdent(name.to_string()))?;
    // Metadata can only restrict this predicate: a source-kind entry cannot
    // promote a stored definition, theorem or opaque into an axiom target.
    let axiom = constant.kind == ConstantKind::Axiom
        && crate::source_kind::get(env, name) == Some(ConstantKind::Axiom);
    if env.get_inductive(name).is_none() && !axiom {
        return Err(ElabError::InvalidClassAttribute { name: name.clone() });
    }
    let out_marker = Name::from_string("outParam");
    let semi_marker = Name::from_string("semiOutParam");
    let mut out_params: Vec<usize> = Vec::new();
    let mut semi_out_params = Vec::new();
    let mut num_params = 0;
    let mut ty = &constant.type_;
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
    env.register_class(KernelClassInfo {
        name: name.clone(),
        num_params,
        out_params,
        semi_out_params,
    });
    Ok(())
}

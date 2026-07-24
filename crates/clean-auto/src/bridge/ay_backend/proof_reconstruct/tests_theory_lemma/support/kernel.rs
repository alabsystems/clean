// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel environment bootstrap and type-check assertion helpers for
//! proof-reconstruction tests that verify reconstructed proof terms
//! pass kernel validation.

use clean_kernel::name::Name;
use clean_kernel::{Expr, FVarId};

pub(in super::super) fn mk_lra_kernel_env() -> clean_kernel::Environment {
    super::super::super::tests_e2e_lra::mk_env_for_lra()
}

pub(in super::super) fn mk_real_lra_kernel_env() -> clean_kernel::Environment {
    super::super::super::tests_e2e_lra::mk_env_for_real_lra()
}

fn mk_local_context(local_ctx_entries: &[(FVarId, &str, Expr)]) -> clean_kernel::LocalContext {
    use clean_kernel::{BinderInfo, LocalContext};

    let mut ctx = LocalContext::new();
    for (id, name, ty) in local_ctx_entries {
        ctx.push_with_id(
            *id,
            Name::from_string(name),
            ty.clone(),
            BinderInfo::Default,
        );
    }
    ctx
}

pub(in super::super) fn assert_lra_proof_type_checks(
    env: &clean_kernel::Environment,
    proof_term: &Expr,
    local_ctx_entries: &[(FVarId, &str, Expr)],
    msg: &str,
) {
    use clean_kernel::TypeChecker;

    let tc = TypeChecker::with_context(env, mk_local_context(local_ctx_entries));
    let inferred_type = tc
        .infer_type(proof_term)
        .expect("proof term should type-check in the kernel");

    let type_of_type = tc
        .infer_type(&inferred_type)
        .expect("inferred type should be well-typed");
    let prop = Expr::prop();
    assert!(
        tc.is_def_eq(&type_of_type, &prop),
        "{msg}: proof type should be a Prop, but its type is {:?}",
        type_of_type,
    );
}

pub(in super::super) fn assert_lra_proof_type_checks_to_false(
    env: &clean_kernel::Environment,
    proof_term: &Expr,
    local_ctx_entries: &[(FVarId, &str, Expr)],
    msg: &str,
) {
    use clean_kernel::TypeChecker;

    let tc = TypeChecker::with_context(env, mk_local_context(local_ctx_entries));
    let inferred_type = tc
        .infer_type(proof_term)
        .expect("proof term should type-check in the kernel");
    let expected_type = Expr::const_(Name::from_string("False"), vec![]);
    assert!(
        tc.is_def_eq(&inferred_type, &expected_type),
        "{msg}: expected False, got {:?}",
        inferred_type,
    );
}

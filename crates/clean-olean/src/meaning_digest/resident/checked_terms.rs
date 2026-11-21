// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use std::collections::BTreeSet;

use clean_kernel::tc::TypeChecker;
use clean_kernel::{ConstantInfo, ConstantKind, Declaration, Environment, Expr, Name};

use super::{MeaningDigests, Package, ResidentPinError};

pub(super) fn compare_term_closure(
    source: &Environment,
    reference: &Environment,
    closure: &BTreeSet<Name>,
    compared: &mut BTreeSet<Name>,
) -> Result<(), ResidentPinError> {
    for name in closure {
        if compared.contains(name) {
            continue;
        }
        let singleton = Package::of_names(BTreeSet::from([name.clone()]));
        let expected_digest = MeaningDigests::new(reference, &singleton).digest(name)?;
        let actual_digest = MeaningDigests::new(source, &singleton).digest(name)?;
        if actual_digest != expected_digest {
            let expected = reference
                .get_const(name)
                .ok_or_else(|| ResidentPinError::Term(name.clone()))?;
            let actual = source
                .get_const(name)
                .ok_or_else(|| ResidentPinError::Term(name.clone()))?;
            if !check_pair(source, actual, expected) || !check_pair(reference, expected, actual) {
                return Err(ResidentPinError::Term(name.clone()));
            }
        }
        compared.insert(name.clone());
    }
    Ok(())
}

fn check_pair(environment: &Environment, first: &ConstantInfo, second: &ConstantInfo) -> bool {
    if first.kind != second.kind
        || first.level_params != second.level_params
        || !matches!(first.kind, ConstantKind::Definition | ConstantKind::Theorem)
    {
        return false;
    }
    if first.type_ != second.type_ {
        let Ok(level) = TypeChecker::new(environment).infer_sort(&first.type_) else {
            return false;
        };
        if !checked_equality(
            environment,
            &first.level_params,
            &Expr::sort(level),
            &first.type_,
            &second.type_,
        ) {
            return false;
        }
    }
    if first.kind == ConstantKind::Definition {
        let (Some(left), Some(right)) = (&first.value, &second.value) else {
            return false;
        };
        if left != right
            && !checked_equality(environment, &first.level_params, &first.type_, left, right)
        {
            return false;
        }
    }
    true
}

fn checked_equality(
    environment: &Environment,
    parameters: &[Name],
    carrier: &Expr,
    left: &Expr,
    right: &Expr,
) -> bool {
    let Ok(level) = TypeChecker::new(environment).infer_sort(carrier) else {
        return false;
    };
    let equation = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![level.clone()]),
        [carrier.clone(), left.clone(), right.clone()],
    );
    let witness = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![level]),
        [carrier.clone(), left.clone()],
    );
    environment
        .check_decl_readonly_strict(&Declaration::Theorem {
            name: Name::from_string("_clean_w3.term_comparison"),
            level_params: parameters.to_vec(),
            type_: equation,
            value: witness,
        })
        .is_ok()
}

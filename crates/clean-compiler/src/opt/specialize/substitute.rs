// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Ground-value substitution helpers for specialization.
//!
//! Used by `candidate.rs` to inline ground arguments into specialized
//! function bodies and to wrap bodies with let bindings for FVarId validity.

use super::context::SpecKey;
use crate::lcnf::{Code, LetDecl, LetValue, Param};
use crate::CodeFolder;
use clean_kernel::FVarId;
use std::collections::HashMap;

/// CodeFolder that substitutes ground values for FVar references in let-values.
///
/// Only overrides `fold_let_value` — structural recursion over Code variants is
/// handled entirely by the CodeFolder trait defaults.
struct GroundSubFolder<'a> {
    subs: &'a HashMap<FVarId, LetValue>,
}

impl CodeFolder for GroundSubFolder<'_> {
    fn fold_let_value(&mut self, value: LetValue) -> LetValue {
        if let LetValue::FVar { ref fvar, .. } = value {
            if let Some(sub_value) = self.subs.get(fvar) {
                return sub_value.clone();
            }
        }
        value
    }
}

/// Substitute ground values for parameters in code.
pub(crate) fn substitute_ground_in_code(code: &Code, subs: &HashMap<FVarId, LetValue>) -> Code {
    GroundSubFolder { subs }.fold_code(code)
}

/// Wrap code with let bindings for ground parameters.
///
/// `substitute_ground_in_code` replaces `LetValue::FVar` references to ground
/// params but misses `Arg::FVar` in `Const`/`Ctor`/`Jmp` args and `Code::Return`.
/// Adding let bindings ensures the param FVarIds remain valid everywhere.
/// Part of #1954 Bug 3.
pub(crate) fn wrap_with_ground_bindings(
    body: Code,
    params: &[Param],
    spec_keys: &[SpecKey],
    subs: &HashMap<FVarId, LetValue>,
) -> Code {
    let mut wrapped = body;
    for (param, key) in params.iter().zip(spec_keys.iter()).rev() {
        if matches!(key, SpecKey::Ground(_)) {
            if let Some(binding) = subs.get(&param.fvar_id) {
                wrapped = Code::Let(
                    LetDecl {
                        fvar_id: param.fvar_id,
                        name: param.name.clone(),
                        ty: param.ty.clone(),
                        value: binding.clone(),
                    },
                    Box::new(wrapped),
                );
            }
        }
    }
    wrapped
}

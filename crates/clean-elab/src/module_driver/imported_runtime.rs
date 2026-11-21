// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Replay first-order Nat calls against the source driver's checked import.

use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::Arc;

use clean_kernel::{BigNat, Environment, Expr, ExprKind, Literal, Name};
use clean_olean::import::lean_declaration_artifact;
use clean_olean::{
    format_lean_nat, prepare_imported_nat_function, CapturedModuleBytes, ImportedNatFunction,
};

use crate::commands::EvalResult;
use crate::print_axioms::used_constants_in_order;
use crate::ElabError;

#[derive(Default)]
pub(crate) struct ImportedRuntime {
    by_origin: HashMap<String, Vec<RuntimeModule>>,
    pub(crate) char_program: Option<clean_olean::StableCharProgram>,
    pub(crate) nat_dictionary: Option<clean_olean::StableNatDictionary>,
    pub(crate) stdout_imports: Option<clean_olean::StableStdoutImports>,
    pub(crate) io_error_imports: Option<clean_olean::StableIoErrorImports>,
}

struct RuntimeModule {
    canonical_path: PathBuf,
    base: Arc<[u8]>,
    server: Option<Arc<[u8]>>,
    private: Option<Arc<[u8]>>,
    ir: Option<Arc<[u8]>>,
    ir_signature: Option<Arc<[u8]>>,
    visible_for_eval: bool,
    visible_for_native: bool,
    module_system: bool,
}

pub(crate) enum RuntimePhase {
    Eval,
    Native,
}

impl RuntimeModule {
    fn capture(&self) -> CapturedModuleBytes<'_> {
        CapturedModuleBytes {
            canonical_path: &self.canonical_path,
            base: &self.base,
            server: self.server.as_deref(),
            private: self.private.as_deref(),
            ir: self.ir.as_deref(),
            ir_signature: self.ir_signature.as_deref(),
        }
    }
}

impl ImportedRuntime {
    pub(crate) fn is_empty(&self) -> bool {
        self.by_origin.is_empty()
            && self.io_error_imports.is_none()
            && self.stdout_imports.is_none()
            && self.char_program.is_none()
            && self.nat_dictionary.is_none()
    }

    pub(crate) fn insert(
        &mut self,
        module: &Name,
        base: Arc<[u8]>,
        bytes: CapturedModuleBytes<'_>,
        visible_for_eval: bool,
        visible_for_native: bool,
        module_system: bool,
    ) {
        self.by_origin
            .entry(module.to_string())
            .or_default()
            .push(RuntimeModule {
                canonical_path: bytes.canonical_path.to_owned(),
                base,
                server: bytes.server.map(Arc::from),
                private: bytes.private.map(Arc::from),
                ir: bytes.ir.map(Arc::from),
                ir_signature: bytes.ir_signature.map(Arc::from),
                visible_for_eval,
                visible_for_native,
                module_system,
            });
    }

    pub(crate) fn prepare(
        &self,
        env: &Environment,
        name: &Name,
        phase: RuntimePhase,
    ) -> Result<Option<ImportedNatFunction<'_>>, ElabError> {
        let Some(origin) = lean_declaration_artifact(env, name) else {
            return Ok(None);
        };
        let Some(captures) = self.by_origin.get(&origin) else {
            return Ok(None);
        };
        // The ledger's origin label narrows the search. The declaration must
        // also match the exact typed name exported by the captured bytes.
        let [module] = captures.as_slice() else {
            return Err(refusal(format!(
                "ambiguous imported runtime module `{origin}`"
            )));
        };
        let Some(function) =
            prepare_imported_nat_function(module.capture(), name).map_err(refusal)?
        else {
            return Ok(None);
        };
        match phase {
            RuntimePhase::Eval if !module.visible_for_eval && !function.is_marked_meta() => {
                Err(refusal(format!(
                    "Invalid `meta` definition `_eval`, `{name}` is not accessible here; \
                     consider adding `public meta import {origin}`"
                )))
            }
            RuntimePhase::Native if module.module_system && function.is_marked_meta() => {
                Err(refusal(format!(
                    "native code may not access declaration `{name}` marked as `meta`"
                )))
            }
            RuntimePhase::Native if !module.visible_for_native => Err(refusal(format!(
                "native code may not access declaration `{name}` imported as `meta`; \
                 consider adding `import {origin}`"
            ))),
            _ => Ok(Some(function)),
        }
    }

    pub(crate) fn eval(
        &self,
        env: &Environment,
        expr: &Expr,
    ) -> Result<Option<EvalResult>, ElabError> {
        let mut functions = HashMap::new();
        for name in used_constants_in_order(expr) {
            if let Some(function) = self.prepare(env, &name, RuntimePhase::Eval)? {
                functions.insert(name, function);
            }
        }
        if functions.is_empty() {
            return Ok(None);
        }
        let value = eval_nat(expr, &functions, 0)?;
        Ok(Some(EvalResult {
            value: format_lean_nat(value.limbs()),
        }))
    }
}

fn eval_nat(
    expr: &Expr,
    functions: &HashMap<Name, ImportedNatFunction<'_>>,
    depth: usize,
) -> Result<BigNat, ElabError> {
    const MAX_CALL_DEPTH: usize = 128;
    if depth >= MAX_CALL_DEPTH {
        return Err(refusal("imported Nat evaluation depth exceeded"));
    }
    if let ExprKind::MData(_, inner) = expr.kind() {
        return eval_nat(inner, functions, depth + 1);
    }
    if let ExprKind::Lit(Literal::Nat(value)) = expr.kind() {
        return Ok(value.clone());
    }
    let head = expr.get_app_fn();
    if let ExprKind::Const(name, _) = head.kind() {
        if let Some(function) = functions.get(name) {
            let args = expr.get_app_args();
            if args.len() != function.arity() {
                return Err(refusal(format!(
                    "expected a saturated imported Nat call to `{name}`"
                )));
            }
            let values = args
                .iter()
                .map(|arg| eval_nat(arg, functions, depth + 1))
                .collect::<Result<Vec<_>, _>>()?;
            return function.evaluate(&values).map_err(refusal);
        }
        if *name == Name::anon().str("OfNat").str("ofNat") {
            let args = expr.get_app_args();
            if let [nat, index, instance] = args.as_slice() {
                let instance_args = instance.get_app_args();
                if matches!(nat.kind(), ExprKind::Const(name, levels)
                    if *name == Name::anon().str("Nat") && levels.is_empty())
                    && matches!(instance.get_app_fn().kind(), ExprKind::Const(name, levels)
                        if *name == Name::anon().str("instOfNatNat") && levels.is_empty())
                    && matches!(instance_args.as_slice(), [arg] if *arg == *index)
                {
                    if let ExprKind::Lit(Literal::Nat(value)) = index.kind() {
                        return Ok(value.clone());
                    }
                }
            }
        }
    }
    Err(refusal(
        "imported Nat evaluation expects a closed call built from saturated imported Nat functions and Nat literals",
    ))
}

fn refusal(detail: impl std::fmt::Display) -> ElabError {
    ElabError::CommandFailed {
        message: detail.to_string(),
    }
}

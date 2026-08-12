// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Public construction boundary for the kernel-checked EvalIR semantics.
//!
//! The EvalIR definitions are useful outside `clean-verify`'s own tests: Trust
//! binds literal program artifacts to temporal `Init`/`Next` definitions and
//! checks the resulting universal refinement theorem in this exact
//! environment.  Keeping construction here prevents consumers from rebuilding
//! a look-alike semantics or depending on the much larger full specification.

use crate::spec::{SpecError, Specification};

/// Build the dependency-scoped EvalIR specification on the stack size required
/// by its recursive declarations.
///
/// The returned environment contains foundation types plus the single
/// authoritative `eval_ir_*` syntax, state, operation, transition, and crystal
/// stages.  No authored program or proof is installed.
///
/// # Errors
/// Returns [`SpecError`] if any EvalIR declaration fails to parse, elaborate,
/// or kernel-check.
pub fn build_spec_with_stack() -> Result<Specification, SpecError> {
    const EVAL_IR_STACK_SIZE: usize = 64 * 1024 * 1024;
    std::thread::Builder::new()
        .name("clean-evalir-spec".to_owned())
        .stack_size(EVAL_IR_STACK_SIZE)
        .spawn(Specification::new_eval_ir_spec)
        .map_err(|error| {
            SpecError::EnvError(format!("cannot spawn EvalIR specification thread: {error}"))
        })?
        .join()
        .map_err(|_| SpecError::EnvError("EvalIR specification thread panicked".to_owned()))?
}

/// Build EvalIR in Clean's ordinary production prelude on the stack size
/// required by its recursive declarations.
///
/// This is the composition boundary for consumers that elaborate authored
/// Clean source over EvalIR.  It contains the same authoritative `IR*` and
/// `ir_*` declarations as [`build_spec_with_stack`], plus the standard logical,
/// notation, and typeclass declarations from `Environment::with_prelude`.
/// It intentionally does not construct Clean's unrelated full
/// self-verification specification.
///
/// # Errors
/// Returns [`SpecError`] if prelude or EvalIR construction fails, the worker
/// cannot be started, or the construction worker panics.
pub fn build_prelude_spec_with_stack() -> Result<Specification, SpecError> {
    const EVAL_IR_STACK_SIZE: usize = 64 * 1024 * 1024;
    std::thread::Builder::new()
        .name("clean-evalir-prelude-spec".to_owned())
        .stack_size(EVAL_IR_STACK_SIZE)
        .spawn(Specification::new_eval_ir_prelude_spec)
        .map_err(|error| {
            SpecError::EnvError(format!(
                "cannot spawn EvalIR prelude specification thread: {error}"
            ))
        })?
        .join()
        .map_err(|_| {
            SpecError::EnvError("EvalIR prelude specification thread panicked".to_owned())
        })?
}

#[cfg(test)]
mod tests {
    use clean_kernel::name::Name;

    #[test]
    fn prelude_builder_contains_one_evalir_authority_and_standard_classes() {
        let spec = super::build_prelude_spec_with_stack().expect("combined spec must build");
        for name in ["IRModule", "ir_init", "ir_step", "HAdd.hAdd", "instHAddNat"] {
            assert!(
                spec.env().get_const(&Name::from_string(name)).is_some(),
                "combined production environment is missing `{name}`"
            );
        }
    }
}

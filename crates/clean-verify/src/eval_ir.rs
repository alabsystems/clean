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

pub use crate::{
    build_canonical_arithmetic_byte_prelude_spec_v1_with_stack,
    build_positive_division_byte_prelude_spec_v1_with_stack,
    build_u64_shift_by_three_byte_prelude_spec_v1_with_stack,
    build_u64_shift_by_three_output_bounds_byte_prelude_spec_v1_with_stack,
};
use std::sync::{Mutex, OnceLock};

#[cfg(test)]
#[path = "eval_ir_release_tests.rs"]
mod release_tests;
#[path = "eval_ir_syntax_epoch.rs"]
mod syntax_epoch;
pub use syntax_epoch::{
    checked_syntax_identity, EvalIrSyntaxEpoch, EvalIrSyntaxIdentity, EVAL_IR_SYNTAX_EPOCH,
};

#[path = "eval_ir_package_reuse.rs"]
mod package_reuse;

#[cfg(test)]
#[path = "eval_ir_worker_budget_tests.rs"]
mod worker_budget_tests;

#[cfg(test)]
#[path = "eval_ir_reuse_tests.rs"]
mod reuse_tests;

/// Explicit measurement / differential tool (see the `eval_ir_reuse_measure` binary).
#[path = "eval_ir_reuse_measure.rs"]
pub mod reuse_measure;

/// Fixed, program-independent EvalIR vocabularies available for in-process reuse.
///
/// These profiles select the existing constructors, not caller-supplied
/// environments, declarations, proof terms, or serialized verification claims.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum EvalIrVocabulary {
    /// EvalIR with its dependency-scoped foundation.
    DependencyScoped,
    /// EvalIR in the ordinary Clean prelude.
    Prelude,
    /// The versioned byte/world profile in the ordinary Clean prelude.
    ByteV1,
}

/// Successful values only: a failed construction never becomes a vocabulary.
struct VocabularyCell {
    value: OnceLock<Specification>,
    syntax_epoch: EvalIrSyntaxEpoch,
    initializing: Mutex<()>,
}

impl VocabularyCell {
    const fn new() -> Self {
        Self {
            value: OnceLock::new(),
            syntax_epoch: EVAL_IR_SYNTAX_EPOCH,
            initializing: Mutex::new(()),
        }
    }

    fn get_or_try_init(
        &self,
        build: impl FnOnce() -> Result<Specification, SpecError>,
    ) -> Result<&Specification, SpecError> {
        if self.syntax_epoch != EVAL_IR_SYNTAX_EPOCH {
            return Err(SpecError::EnvError(
                "cached EvalIR syntax epoch mismatch".into(),
            ));
        }
        if let Some(value) = self.value.get() {
            return Ok(value);
        }
        let _initializing = self.initializing.lock().map_err(|_| {
            SpecError::EnvError("EvalIR vocabulary initialization lock poisoned".into())
        })?;
        if let Some(value) = self.value.get() {
            return Ok(value);
        }
        // `build` uses a separate worker and converts its panic to an error.
        // Err leaves the cell empty and releases the mutex for a later retry.
        let value = build()?;
        Ok(self.value.get_or_init(|| value))
    }
}

static DEPENDENCY_SCOPED: VocabularyCell = VocabularyCell::new();
static PRELUDE: VocabularyCell = VocabularyCell::new();
static BYTE_V1: VocabularyCell = VocabularyCell::new();

fn construction_override() -> bool {
    // A requested fresh-build budget (including an invalid spelling) must not
    // be hidden by an earlier success. The quality flag is a live add_decl
    // admission policy, not a diagnostic: stricter requests must execute it.
    std::env::var_os("CLEAN_SPEC_DECL_BUDGET").is_some()
        || std::env::var("CLEAN_STRICT_PROOF_QUALITY").is_ok_and(|value| value == "1")
}

fn build_fresh(vocabulary: EvalIrVocabulary) -> Result<Specification, SpecError> {
    let spec = match vocabulary {
        EvalIrVocabulary::DependencyScoped => build_on_stack(
            "clean-evalir-spec",
            "EvalIR",
            Specification::new_eval_ir_spec,
        ),
        EvalIrVocabulary::Prelude => build_on_stack(
            "clean-evalir-prelude-spec",
            "EvalIR prelude",
            Specification::new_eval_ir_prelude_spec,
        ),
        EvalIrVocabulary::ByteV1 => build_on_stack(
            "clean-evalir-byte-v1-spec",
            "byte EvalIR",
            Specification::new_eval_ir_byte_prelude_spec_v1,
        ),
    }?;
    checked_syntax_identity(spec.env(), EVAL_IR_SYNTAX_EPOCH).map_err(SpecError::EnvError)?;
    Ok(spec)
}

fn build_owned(vocabulary: EvalIrVocabulary) -> Result<Specification, SpecError> {
    if construction_override() {
        return build_fresh(vocabulary);
    }
    shared_specification_with_stack(vocabulary).cloned()
}

fn build_on_stack(
    thread_name: &'static str,
    label: &'static str,
    build: impl FnOnce() -> Result<Specification, SpecError> + Send + 'static,
) -> Result<Specification, SpecError> {
    const EVAL_IR_STACK_SIZE: usize = 64 * 1024 * 1024;
    std::thread::Builder::new()
        .name(thread_name.to_owned())
        .stack_size(EVAL_IR_STACK_SIZE)
        .spawn(move || {
            // Byte/Prelude constructors do not arm the Full specification's
            // declaration scope. Honor an explicit request in THIS worker,
            // before prelude construction; ordinary construction is unchanged.
            if std::env::var_os(crate::spec::decl_budget::SPEC_DECL_BUDGET_ENV).is_some() {
                crate::spec::decl_budget::with_spec_declaration_budget(|| {
                    // Some legacy infallible initializers panic on a kernel
                    // resource error. Inspect the latch before this scope
                    // drops; an exhausted build is typed unknown, never a
                    // mathematical refusal or generic worker-panic verdict.
                    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(build)) {
                        Ok(result) => crate::spec::decl_budget::finish_declaration(label, result),
                        Err(_) if clean_kernel::tc::declaration_budget_exhausted() => {
                            Err(SpecError::DeclarationBudgetExhausted {
                                declaration: label.into(),
                                limit: clean_kernel::tc::declaration_budget_limit(),
                            })
                        }
                        Err(payload) => std::panic::resume_unwind(payload),
                    }
                })
            } else {
                build()
            }
        })
        .map_err(|error| {
            SpecError::EnvError(format!(
                "cannot spawn {label} specification thread: {error}"
            ))
        })?
        .join()
        .map_err(|_| SpecError::EnvError(format!("{label} specification thread panicked")))?
}

/// Borrow one immutable, checked EvalIR vocabulary for this process.
///
/// The first successful request runs the selected original constructor with
/// all of its elaboration, kernel checks and dependency audits unchanged.
/// Concurrent first requests share that successful initialization. Construction
/// errors (including worker panics) propagate and are not cached: a later
/// request can retry. No disk snapshot or stored verification verdict is read.
///
/// Only these three fixed profiles can be retained, once each, until process
/// exit. There is no per-program cache. Read-only callers avoid copying the
/// environment; callers needing extensions can clone the specification. A
/// clone copies its owned maps/options while sharing immutable expression DAGs,
/// so registrations or option changes cannot affect the retained vocabulary.
/// The owned compatibility builders below perform that clone for their callers.
///
/// Construction uses the original fixed-profile worker environment, not the
/// caller's proof-checking options. Every endpoint claim, provider contract and
/// per-checker resource limit remains the consumer's responsibility. Reuse
/// supplies no source/Core/native proof authority. The raw `Specification`
/// constructors remain available for explicitly fresh construction.
///
/// An explicit `CLEAN_SPEC_DECL_BUDGET` or active
/// `CLEAN_STRICT_PROOF_QUALITY=1` declines shared reuse. The owned builders
/// instead execute the original fresh path, preserving requested construction
/// admission, including malformed-budget errors. Ordinary cache hits perform
/// no construction and spend no construction budget; endpoint checks retain
/// their own limits. Diagnostic trace flags do not select another vocabulary.
/// Process configuration must remain stable during a construction request.
///
/// # Errors
/// Returns the original construction error, or an environment error if the
/// construction worker cannot start/panics, a construction override requests
/// fresh checking, or the initialization lock is poisoned.
pub fn shared_specification_with_stack(
    vocabulary: EvalIrVocabulary,
) -> Result<&'static Specification, SpecError> {
    if construction_override() {
        return Err(SpecError::EnvError(
            "shared EvalIR vocabulary declined: construction policy requests a fresh owned builder"
                .into(),
        ));
    }
    // These raw constructors never call this module's cached builders. In
    // particular ByteV1 composes the *raw* prelude constructor. Keeping that
    // direction prevents recursive acquisition of an initialization mutex.
    let cell = match vocabulary {
        EvalIrVocabulary::DependencyScoped => &DEPENDENCY_SCOPED,
        EvalIrVocabulary::Prelude => &PRELUDE,
        EvalIrVocabulary::ByteV1 => &BYTE_V1,
    };
    cell.get_or_try_init(|| build_fresh(vocabulary))
}

/// Build the dependency-scoped EvalIR specification on the stack size required
/// by its recursive declarations.
///
/// The returned environment contains foundation types plus the single
/// authoritative `eval_ir_*` syntax, state, operation, transition, and crystal
/// stages.  No authored program or proof is installed.
/// The fixed vocabulary is initialized once per process; this returns an
/// independent owned clone. See [`shared_specification_with_stack`].
///
/// # Errors
/// Returns [`SpecError`] if any EvalIR declaration fails to parse, elaborate,
/// or kernel-check.
pub fn build_spec_with_stack() -> Result<Specification, SpecError> {
    build_owned(EvalIrVocabulary::DependencyScoped)
}

/// Build EvalIR in Clean's ordinary production prelude on the stack size
/// required by its recursive declarations.
///
/// This is the composition boundary for consumers that elaborate authored
/// Clean source over EvalIR. It contains the shared `IR*` and `ir_*` execution
/// vocabulary plus the standard logical, notation, and typeclass declarations
/// from `Environment::with_prelude`. Historical worked examples and the
/// dependency-scoped Crystal witnesses belong to [`build_spec_with_stack`].
/// It intentionally does not construct Clean's unrelated full
/// self-verification specification.
/// The fixed vocabulary is initialized once per process; this returns an
/// independent owned clone. See [`shared_specification_with_stack`].
///
/// # Errors
/// Returns [`SpecError`] if prelude or EvalIR construction fails, the worker
/// cannot be started, or the construction worker panics.
pub fn build_prelude_spec_with_stack() -> Result<Specification, SpecError> {
    build_owned(EvalIrVocabulary::Prelude)
}

/// Identity of the opt-in production-Prelude Nat/Bool reflection package.
/// This is distinct from every legacy/default vocabulary and is no proof receipt.
pub const NAT_BOOL_REFLECTION_PRELUDE_PROFILE_V1: &str = "clean-nat-bool-reflection-prelude-v1";

/// Build the fixed Nat equality and Boolean elimination proofs over production Prelude.
///
/// Reuses Clean's authoritative comparison and Boolean sources, without historical
/// Crystal examples or the dependency-scoped foundation. Every installed root and
/// its complete dependency closure is strictly rechecked with empty axiom and trust
/// closures, under ordinary finite kernel limits. Only the underlying Prelude may
/// be reused; this package is checked anew and returns an independent owned value.
/// No caller declaration, borrowed receipt or stored admission verdict is accepted.
/// Consumers must still check their own endpoint and retain this profile identity.
/// This does not establish source/Core/native execution or Rust verification.
///
/// # Errors
/// Returns the original Prelude construction error, or a package installation,
/// stored-declaration, rooted certification or worker error. Failure returns no package.
pub fn build_nat_bool_reflection_prelude_spec_v1_with_stack() -> Result<Specification, SpecError> {
    build_on_stack(
        "clean-nat-bool-reflection-prelude-v1",
        "Nat/Bool reflection PreludeV1",
        || build_owned(EvalIrVocabulary::Prelude)?.into_nat_bool_reflection_prelude_v1(),
    )
}

/// Build the versioned, byte-addressed EvalIR profile in the production prelude.
///
/// The shared execution driver is the same driver used by legacy `ir_steps`.
/// The byte profile additionally requires an explicit module-derived context
/// and retains its memory/provider world on terminal configurations. Building
/// this vocabulary does not certify any reflected module, provider, target
/// layout, or native image. Consumers must replay their actual endpoint claim
/// and discharge the representation and provider premises separately.
/// The fixed vocabulary is initialized once per process; this returns an
/// independent owned clone. See [`shared_specification_with_stack`].
///
/// # Errors
/// Returns [`SpecError`] if a declaration fails to parse, elaborate, or
/// kernel-check, or if the construction worker cannot start or panics.
pub fn build_byte_prelude_spec_v1_with_stack() -> Result<Specification, SpecError> {
    build_owned(EvalIrVocabulary::ByteV1)
}

/// Build an owned ByteV1 vocabulary with checked, bounded-fuel positive-divisor
/// agreement laws. The original evaluator definitions and default shared cache
/// are unchanged. A caller can use the actual scalar operation endpoints rather
/// than introducing a separate fast denotation or assuming a quotient.
///
/// The disposable owned vocabulary is returned only after strict rooted checks
/// of the complete package. This is not model/native admission or Rust proof.
///
/// # Errors
/// Original ByteV1 construction or positive-division installation/check failure.
pub(crate) fn build_positive_division_byte_prelude_spec_v1_owned(
) -> Result<Specification, SpecError> {
    package_reuse::build_owned_package(package_reuse::Package::PositiveDivisionByteV1)
}

/// Build the additive, strictly checked full64 shift-by-three consumer of the
/// positive-divisor package. This connects the actual EvalIR Lshr/AShr cases,
/// not a replacement evaluator or native-code admission certificate. Defaults
/// and process-cached ByteV1 owners are unchanged.
///
/// # Errors
/// Vocabulary, fixed-package declaration or strict rooted certification refusal.
pub(crate) fn build_u64_shift_by_three_byte_prelude_spec_v1_owned(
) -> Result<Specification, SpecError> {
    package_reuse::build_owned_package(package_reuse::Package::U64ShiftByThreeByteV1)
}

pub(crate) fn build_u64_shift_by_three_output_bounds_byte_prelude_spec_v1_owned(
) -> Result<Specification, SpecError> {
    package_reuse::build_owned_package(package_reuse::Package::U64ShiftByThreeOutputBoundsByteV1)
}

/// Build the explicit, program-independent canonical arithmetic ByteV1 profile.
///
/// This composes the existing checked positive-divisor library, full64 I64
/// AShr/U64 Lshr by three with derived output bounds, width-indexed signed and
/// unsigned wrapping Add with derived bounds, and unsigned Ult/Ule/Ugt/Uge on
/// both nominal integer carriers. It does not include all arithmetic or all
/// shift amounts. No evaluator, legacy/default profile, stack or proof limit
/// changes; no desired operation answer or branch truth is a premise.
///
/// A single disposable owner installs the existing sources and checks every
/// original root. Only complete successful fixed-library construction is
/// retained through the existing package machinery. Each request returns an
/// independent owned clone; live construction overrides execute fresh before
/// any warm hit. Actual program replay and source/native admission are separate.
///
/// # Errors
/// Vocabulary, name collision, package declaration or strict rooted refusal.
pub(crate) fn build_canonical_arithmetic_byte_prelude_spec_v1_owned(
) -> Result<Specification, SpecError> {
    package_reuse::build_owned_package(package_reuse::Package::CanonicalArithmeticByteV1)
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
        for name in [
            "ir_lzm_module",
            "ir_lz_module",
            "ir_lzb_module",
            "ir_lzc_module",
            "ir_lzd_module",
        ] {
            assert!(
                spec.env().get_const(&Name::from_string(name)).is_none(),
                "production execution vocabulary must not install historical Crystal example `{name}`"
            );
        }
    }

    #[test]
    fn byte_builder_rechecks_its_execution_and_world_roots() {
        let spec = super::build_byte_prelude_spec_v1_with_stack()
            .expect("production byte-profile constructor must build");
        for name in [
            "ir_drive_add_v1",
            "ir_byte_init_v1",
            "ir_byte_run_v1",
            "ir_byte_alloc_v1",
            "ir_byte_load_v1",
            "ir_byte_store_v1",
            "ir_byte_gep_v1",
            "ir_byte_retire_v1",
        ] {
            let definition = spec.get_definition(name).expect("production root exists");
            assert!(!definition.is_axiom, "{name} is not an assumption");
            assert!(definition.elaborated_value.is_some(), "{name} has a body");
            spec.verify_definition(name).expect("root kernel replay");
            let root = Name::from_string(name);
            assert!(spec
                .env()
                .axiom_deps(&root)
                .expect("root exists")
                .is_empty());
            assert!(spec
                .env()
                .trust_marker_deps(&root)
                .expect("root exists")
                .is_empty());
        }
    }
}

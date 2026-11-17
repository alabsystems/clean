// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Source-affine logical facts, never an executable scalar ABI permission.

use super::{ExternalLeanProgram, InputObservation, ReplayContextLimits, ReplayedLeanContext};
use clean_compiler::runtime_lcnf::RuntimeScopedEnvironmentCapture;
use clean_kernel::{ConstantInfo, LeanWorld, Name};
use clean_olean::{ImportedConeVerdict, ReplayedImportedSource, ReplayedSourceError};
use std::{cell::RefCell, sync::Arc};

mod budget;
mod checks;
mod discovery;
mod families;

/// The actual operation which refused; a failure never contains partial facts.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ScalarLayoutStage {
    SourceRoot,
    Discovery,
    Capture,
    SourceReplay,
    ContextReplay,
    RootSignature,
    NaturalNumbers,
    NaturalOrder,
    ScalarFamilies,
    Bounds,
    Projections,
}

#[derive(Debug, thiserror::Error)]
#[error("scalar layout inspection refused at {stage:?}: {cause}")]
pub struct ScalarLayoutFailure {
    stage: ScalarLayoutStage,
    cause: String,
    capture: Option<Arc<RuntimeScopedEnvironmentCapture>>,
    replay: Option<Box<ImportedConeVerdict>>,
}

impl ScalarLayoutFailure {
    pub fn stage(&self) -> ScalarLayoutStage {
        self.stage
    }
    pub fn cause(&self) -> &str {
        &self.cause
    }
    /// Combined bounded observation, if capture was reached; global diagnostics
    /// remain available from the original program independently.
    pub fn source_capture(&self) -> Option<&RuntimeScopedEnvironmentCapture> {
        self.capture.as_deref()
    }
    pub fn replay_verdict(&self) -> Option<&ImportedConeVerdict> {
        self.replay.as_deref()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ScalarLayoutWord {
    U32,
    U64,
}

/// Checked logical roles at one closed width. These are not physical offsets:
/// the shared compiler retains Object placeholders for erased proof fields.
pub struct ScalarWordLayoutFacts {
    word: ScalarLayoutWord,
    family: Name,
    constructor: Name,
    projection: Name,
    width: u32,
    bound: clean_kernel::Expr,
}
impl ScalarWordLayoutFacts {
    pub fn word(&self) -> ScalarLayoutWord {
        self.word
    }
    pub fn family(&self) -> &Name {
        &self.family
    }
    pub fn constructor(&self) -> &Name {
        &self.constructor
    }
    pub fn projection(&self) -> &Name {
        &self.projection
    }
    pub fn width(&self) -> u32 {
        self.width
    }
    pub fn bound(&self) -> &clean_kernel::Expr {
        &self.bound
    }
}

/// Private source/base/root custody and actual replay, borrowed from the owner.
/// No constructor accepts an Environment, favorable hashes or detached verdicts.
/// No selection, emission, loading, promotion or physical-layout API exists.
///
/// ```compile_fail
/// use clean_native::external_lean::CheckedScalarLayoutFacts;
/// fn cannot_execute(facts: &CheckedScalarLayoutFacts<'_>) {
///     let _ = facts.load_scalar_call();
/// }
/// ```
pub struct CheckedScalarLayoutFacts<'program> {
    program: &'program ExternalLeanProgram,
    root: Name,
    context: ReplayedLeanContext<'program>,
    replay: ReplayedImportedSource,
    capture: Arc<RuntimeScopedEnvironmentCapture>,
    words: [ScalarWordLayoutFacts; 2],
    visited_recursors: usize,
}
impl CheckedScalarLayoutFacts<'_> {
    pub fn word(&self, word: ScalarLayoutWord) -> &ScalarWordLayoutFacts {
        &self.words[match word {
            ScalarLayoutWord::U32 => 0,
            ScalarLayoutWord::U64 => 1,
        }]
    }
    pub fn root(&self) -> &Name {
        &self.root
    }
    pub fn world(&self) -> LeanWorld {
        self.program.world()
    }
    pub fn inputs(&self) -> &[InputObservation] {
        self.program.inputs()
    }
    pub fn source_capture(&self) -> &RuntimeScopedEnvironmentCapture {
        &self.capture
    }
    pub fn replay_verdict(&self) -> &ImportedConeVerdict {
        self.replay.verdict()
    }
    /// Whole-world records visited by the one bounded recursor discovery;
    /// separate from selected capture members.
    pub fn visited_recursors(&self) -> usize {
        self.visited_recursors
    }
    /// Original immutable records only, including opacity and imported flags.
    pub fn original_constant(&self, name: &Name) -> Option<&ConstantInfo> {
        self.context
            .declaration(name)
            .ok()
            .and_then(|_| self.program.env.get_const(name))
    }
    /// Original runtime annotation, disclosed without execution permission.
    pub fn original_extern(&self, name: &Name) -> Option<&str> {
        self.original_constant(name)?;
        self.program.env.get_extern(name).map(String::as_str)
    }
}

struct FailureContext {
    capture: Option<Arc<RuntimeScopedEnvironmentCapture>>,
    replay: Option<Box<ImportedConeVerdict>>,
}
impl FailureContext {
    fn fail(&self, stage: ScalarLayoutStage, cause: impl ToString) -> ScalarLayoutFailure {
        ScalarLayoutFailure {
            stage,
            cause: cause.to_string(),
            capture: self.capture.clone(),
            replay: self.replay.clone(),
        }
    }
}

impl ExternalLeanProgram {
    /// Inspect closed scalar logical layout in the same authenticated source
    /// context. Success cannot weaken either native capture/selection guard or
    /// the existing scalar_call source/layout/extern/signature contract.
    pub fn inspect_scalar_layout(
        &self,
        source_root: &Name,
        limits: ReplayContextLimits,
    ) -> Result<CheckedScalarLayoutFacts<'_>, ScalarLayoutFailure> {
        use ScalarLayoutStage as S;
        let mut failure = FailureContext {
            capture: None,
            replay: None,
        };
        let budget = RefCell::new(budget::Budget::new());
        budget
            .borrow_mut()
            .name(source_root)
            .map_err(|e| failure.fail(S::SourceRoot, e))?;
        if !self.module_names.contains(source_root) {
            return Err(failure.fail(
                S::SourceRoot,
                "root was not declared by the captured source module",
            ));
        }
        let mut roots =
            crate::scalar_call::scalar_source_roots().map_err(|e| failure.fail(S::Discovery, e))?;
        roots.insert(source_root.clone());
        let (plan, recursors, roots_vec) = discovery::discover(self, &mut roots, &budget)
            .map_err(|e| failure.fail(S::Discovery, e))?;
        // Capture original rows/attributes BEFORE replay or record digesting.
        for source in &self.source_capture().sources {
            let mut work = budget.borrow_mut();
            work.text(&source.module)
                .and_then(|()| work.text(&source.path))
                .and_then(|()| work.text(&source.source))
                .map_err(|e| failure.fail(S::Capture, e))?;
        }
        let capture = Arc::new(RuntimeScopedEnvironmentCapture::capture(
            &self.base,
            &self.env,
            self.source_capture().sources.clone(),
            &plan,
        ));
        failure.capture = Some(Arc::clone(&capture));
        if !capture.is_complete() {
            return Err(failure.fail(
                S::Capture,
                format!(
                    "incomplete combined capture: errors={:?}, row_failures={:?}",
                    capture.errors(),
                    capture.row_failures()
                ),
            ));
        }
        let replay = ReplayedImportedSource::check(
            Arc::clone(&self.custody.base),
            Arc::clone(&self.custody.source),
            roots.clone(),
        )
        .map_err(|error| {
            if let ReplayedSourceError::Replay(_, verdict) = &error {
                failure.replay = Some(Box::new((**verdict).clone()));
            }
            failure.fail(S::SourceReplay, error)
        })?;
        failure.replay = Some(Box::new(replay.verdict().clone()));
        replay
            .require_context(&self.custody.base, &self.custody.source, &roots)
            .map_err(|e| failure.fail(S::SourceReplay, e))?;
        for name in replay.members() {
            require_captured(&capture, name).map_err(|e| failure.fail(S::SourceReplay, e))?;
            if self.env.is_unsafe(name)
                || self.env.is_partial(name)
                || self.env.is_staged_header(name)
            {
                return Err(failure.fail(
                    S::SourceReplay,
                    format!("{name}: unsafe, partial or staged original record"),
                ));
            }
            replay
                .require_record(&self.env, name)
                .and_then(|()| replay.checked_constant(name).map(|_| ()))
                .map_err(|e| failure.fail(S::SourceReplay, e))?;
        }
        let context = self
            .replay_context(std::slice::from_ref(source_root))
            .and_then(|context| context.with_replayed_declarations(&roots_vec))
            .map_err(|error| {
                if let super::ExternalLeanError::Replay { verdict, .. } = &error {
                    failure.replay = Some(Box::new((**verdict).clone()));
                }
                failure.fail(S::ContextReplay, error)
            })?;
        // The bounded context must not inspect any record outside fresh actual
        // source-value evidence, including metadata-only family dependencies.
        for name in context.dependency_names() {
            require_captured(&capture, name).map_err(|e| failure.fail(S::ContextReplay, e))?;
            replay
                .require_record(&self.env, name)
                .and_then(|()| replay.checked_constant(name).map(|_| ()))
                .map_err(|e| failure.fail(S::SourceReplay, e))?;
        }
        let check = checks::Check {
            program: self,
            context: &context,
            replay: &replay,
            limits,
            recursors: &recursors,
            budget: &budget,
        };
        check
            .expected_type(source_root, &crate::scalar_call::scalar_type())
            .map_err(|e| failure.fail(S::RootSignature, e))?;
        check
            .naturals()
            .map_err(|e| failure.fail(S::NaturalNumbers, e))?;
        check
            .order()
            .map_err(|e| failure.fail(S::NaturalOrder, e))?;
        check
            .scalar_families()
            .map_err(|e| failure.fail(S::ScalarFamilies, e))?;
        let words = check.words().map_err(|(stage, e)| failure.fail(stage, e))?;
        let visited_recursors = budget.borrow().visited();
        Ok(CheckedScalarLayoutFacts {
            program: self,
            root: source_root.clone(),
            context,
            replay,
            capture,
            words,
            visited_recursors,
        })
    }
}

fn require_captured(capture: &RuntimeScopedEnvironmentCapture, name: &Name) -> Result<(), String> {
    if capture.members().contains(name) {
        Ok(())
    } else {
        Err(format!(
            "actual replay member {name} escaped complete combined source capture"
        ))
    }
}

#[cfg(test)]
mod tests;

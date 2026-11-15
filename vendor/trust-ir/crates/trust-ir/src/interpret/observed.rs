// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Explicit resource observation for original-source reference execution.
//!
//! An observer belongs to the caller's original operation. The interpreter
//! creates no grant, deadline, cancellation source, disk allowance or solver
//! invocation. This module is reference execution support, never proof authority.

use super::{InterpretError, InterpretOptions, InterpretOutcome};
use crate::value::{BlockId, FuncId};

pub(crate) mod btree;
mod execute;
mod value;

#[cfg(test)]
mod retirement_record_tests;
#[cfg(test)]
mod tests;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InstructionSite {
    pub function: FuncId,
    pub block: BlockId,
    pub instruction_index: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExecutionSite {
    Entry(FuncId),
    Instruction(InstructionSite),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum ExecutionPhase {
    CanonicalDigest,
    CanonicalSerialization,
    ModuleLookup,
    Validation,
    Reachability,
    AbiScan,
    Layout,
    DropGlueIndex,
    EntryArguments,
    BlockParameters,
    Instruction,
    SparseRun,
    RopeNode,
    LiteralElement,
    HostAllocation,
    ScratchRetirement,
    Publication,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ExecutionProgress {
    pub phase: ExecutionPhase,
    pub site: ExecutionSite,
    pub work: usize,
    pub copy_bytes: usize,
}

pub trait ExecutionObserver {
    type Refusal;

    fn admit(&mut self, progress: ExecutionProgress) -> Result<(), Self::Refusal>;
}

#[derive(Debug)]
pub struct ObservationRefusal<E> {
    pub progress: ExecutionProgress,
    pub cause: E,
}

/// Nonsemantic stop marker. The typed first cause stays in the original session.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ObservationStopped;

impl core::fmt::Display for ObservationStopped {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("original execution observer refused")
    }
}

impl std::error::Error for ObservationStopped {}

/// Inability to construct or traverse the observed representation. None of
/// these reasons is a Rust semantic failure or a proof/counterexample.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum ObservedValueError {
    AdmissionRefused,
    CapacityOverflow,
    AllocationFailed,
    InvalidRange,
    UnsupportedValue,
}

impl From<ObservationStopped> for ObservedValueError {
    fn from(_: ObservationStopped) -> Self {
        Self::AdmissionRefused
    }
}

impl core::fmt::Display for ObservedValueError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            Self::AdmissionRefused => "original execution observer refused",
            Self::CapacityOverflow => "observed representation capacity overflow",
            Self::AllocationFailed => "observed representation allocation failed",
            Self::InvalidRange => "observed representation range is invalid",
            Self::UnsupportedValue => "value representation is outside observed execution",
        })
    }
}

impl std::error::Error for ObservedValueError {}

/// One session per original operation, reused by every conversion and attempt.
/// There is intentionally no Clone, reset, replenish or mutable observer getter.
pub struct ObservedSession<'o, O: ExecutionObserver> {
    observer: &'o mut O,
    options: InterpretOptions,
    remaining_fuel: u64,
    first_refusal: Option<ObservationRefusal<O::Refusal>>,
}

impl<'o, O: ExecutionObserver> ObservedSession<'o, O> {
    pub fn new(options: InterpretOptions, observer: &'o mut O) -> Self {
        Self {
            observer,
            options,
            remaining_fuel: options.fuel,
            first_refusal: None,
        }
    }

    pub fn first_refusal(&self) -> Option<&ObservationRefusal<O::Refusal>> {
        self.first_refusal.as_ref()
    }

    pub fn remaining_fuel(&self) -> u64 {
        self.remaining_fuel
    }

    /// Debit input construction or other structural work using this same
    /// original observer. A refused session cannot resume on a later attempt.
    pub fn admit(&mut self, progress: ExecutionProgress) -> Result<(), ObservationStopped> {
        if self.first_refusal.is_some() {
            return Err(ObservationStopped);
        }
        match self.observer.admit(progress) {
            Ok(()) => Ok(()),
            Err(cause) => {
                self.first_refusal = Some(ObservationRefusal { progress, cause });
                Err(ObservationStopped)
            }
        }
    }

    pub(crate) fn begin_instruction(&mut self, site: InstructionSite) -> Result<(), StepStopped> {
        self.admit(ExecutionProgress {
            phase: ExecutionPhase::Instruction,
            site: ExecutionSite::Instruction(site),
            work: 1,
            copy_bytes: 0,
        })
        .map_err(|_| StepStopped::Admission)?;
        if self.remaining_fuel == 0 {
            return Err(StepStopped::Fuel);
        }
        self.remaining_fuel -= 1;
        Ok(())
    }

    /// Observe retirement in this same original session, including after a
    /// sticky refusal. This cannot clear a cause or resume normal admission.
    /// Cross-crate validators use it for actual owned cleanup, never as a
    /// fresh grant or permission to publish after cancellation.
    pub fn retirement_poll(&mut self, site: ExecutionSite) {
        self.retirement_step(site, 0);
    }

    /// Retain the original observer and first cause while retiring actual
    /// owned payload work. Cleanup cannot renew a grant or skip ownership just
    /// because an earlier admission stopped; its logical work remains visible.
    pub fn retirement_step(&mut self, site: ExecutionSite, work: usize) {
        self.retirement_record(site, work, 0);
    }

    /// Retire an actual complete logical record, preserving both work and
    /// copy-byte charges under this same original observer. Like retirement_step,
    /// this always delivers cleanup even after refusal, preserves the first
    /// typed cause, and can never resume normal admission or renew a budget.
    pub fn retirement_record(&mut self, site: ExecutionSite, work: usize, copy_bytes: usize) {
        let progress = ExecutionProgress {
            phase: ExecutionPhase::ScratchRetirement,
            site,
            work,
            copy_bytes,
        };
        if let Err(cause) = self.observer.admit(progress)
            && self.first_refusal.is_none()
        {
            self.first_refusal = Some(ObservationRefusal { progress, cause });
        }
    }

    pub(crate) fn structural(&mut self, site: ExecutionSite) -> SessionProgress<'_, 'o, O> {
        SessionProgress {
            session: self,
            site,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum StepStopped {
    Admission,
    Fuel,
}

pub(crate) trait StructuralProgress {
    fn admit(
        &mut self,
        phase: ExecutionPhase,
        work: usize,
        copy_bytes: usize,
    ) -> Result<(), ObservationStopped>;

    fn retirement_poll(&mut self);
}

pub(crate) struct SessionProgress<'s, 'o, O: ExecutionObserver> {
    session: &'s mut ObservedSession<'o, O>,
    site: ExecutionSite,
}

impl<O: ExecutionObserver> StructuralProgress for SessionProgress<'_, '_, O> {
    fn admit(
        &mut self,
        phase: ExecutionPhase,
        work: usize,
        copy_bytes: usize,
    ) -> Result<(), ObservationStopped> {
        self.session.admit(ExecutionProgress {
            phase,
            site: self.site,
            work,
            copy_bytes,
        })
    }

    fn retirement_poll(&mut self) {
        self.session.retirement_poll(self.site);
    }
}

pub(crate) trait ObservedRopeElem: super::rope::RopeElem {
    fn clone_observed(
        &self,
        progress: &mut impl StructuralProgress,
    ) -> Result<Self, ObservedValueError>;
    fn same_observed(
        &self,
        other: &Self,
        progress: &mut impl StructuralProgress,
    ) -> Result<bool, ObservedValueError>;
    fn retire_observed(self, progress: &mut impl StructuralProgress);
}

/// These outcomes are reference-execution data, not original-Rust credentials.
/// In particular entry rejection or interpreter incapacity is never a trap.
#[derive(Debug)]
#[non_exhaustive]
pub enum ObservedExit {
    Returned(InterpretOutcome),
    EntryRejected(InterpretError),
    ExecutedError {
        site: InstructionSite,
        error: InterpretError,
    },
    InterpreterLimit {
        site: ExecutionSite,
        error: InterpretError,
    },
    UnsupportedObservation {
        site: ExecutionSite,
        instruction: &'static str,
    },
    AdmissionRefused,
}

/// Constructed only by the observed interpreter after local scratch retirement.
/// Returned/error payloads still belong to the caller's original cleanup scope.
#[derive(Debug)]
pub struct ObservedReport {
    exit: ObservedExit,
    steps: u64,
    host_calls: u64,
}

impl ObservedReport {
    pub fn exit(&self) -> &ObservedExit {
        &self.exit
    }

    pub fn into_exit(self) -> ObservedExit {
        self.exit
    }

    pub fn steps(&self) -> u64 {
        self.steps
    }

    pub fn host_calls(&self) -> u64 {
        self.host_calls
    }
}

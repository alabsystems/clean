// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl SpecLinkViolation {
    /// Consume every owned field under the supplied original owner even after a
    /// sticky refusal; only the terminal zero-cost publication may return error.
    pub fn retire_observed<O: ExecutionObserver>(
        self,
        session: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        let mut work = Work { session, site };
        consume(self, &mut work);
        work.publication(0, 0)
    }
}
pub(super) fn consume_vec<O: ExecutionObserver>(
    mut rows: Vec<SpecLinkViolation>,
    work: &mut Work<'_, '_, O>,
) {
    loop {
        work.step(size_of::<Option<SpecLinkViolation>>().saturating_add(1));
        let Some(row) = rows.pop() else { break };
        consume(row, work);
    }
    work.step(size_of::<Vec<SpecLinkViolation>>().saturating_add(1));
    drop(rows);
    work.poll();
}
pub(super) fn consume<O: ExecutionObserver>(value: SpecLinkViolation, work: &mut Work<'_, '_, O>) {
    work.step(22);
    match value {
        SpecLinkViolation::DuplicateMachineIdentity { mut machine } => {
            work.retire_text(&mut machine);
        }
        SpecLinkViolation::DuplicateMemberIdentity {
            mut machine,
            member,
            mut name,
        } => {
            work.retire_text(&mut machine);
            work.fixed(member);
            work.retire_text(&mut name);
        }
        SpecLinkViolation::BlankSemanticValue {
            mut container,
            subject,
            field,
        } => {
            work.retire_text(&mut container);
            work.fixed(subject);
            work.fixed(field);
        }
        SpecLinkViolation::DuplicateBindingIdentity {
            mut machine,
            binding,
            mut identity,
        } => {
            work.retire_text(&mut machine);
            work.fixed(binding);
            work.retire_text(&mut identity);
        }
        SpecLinkViolation::AnchorWaiverConflict {
            mut machine,
            mut action,
        } => {
            work.retire_text(&mut machine);
            work.retire_text(&mut action);
        }
        SpecLinkViolation::ReferenceContainerMismatch {
            mut container,
            mut machine,
            mut action,
            from,
        } => {
            work.retire_text(&mut container);
            work.retire_text(&mut machine);
            work.retire_text(&mut action);
            work.fixed(from);
        }
        SpecLinkViolation::TypedTargetRequired {
            mut machine,
            mut action,
            target,
        } => {
            work.retire_text(&mut machine);
            work.retire_text(&mut action);
            work.fixed(target);
        }
        SpecLinkViolation::ProjectionTargetIncompatible {
            mut machine,
            mut action,
            mut detail,
        } => {
            work.retire_text(&mut machine);
            work.retire_text(&mut action);
            work.retire_text(&mut detail);
        }
        SpecLinkViolation::ExecutableTargetInvalid {
            mut machine,
            mut action,
            target,
            function,
            mut detail,
        } => {
            work.retire_text(&mut machine);
            work.retire_text(&mut action);
            work.fixed(target);
            work.fixed(function);
            work.retire_text(&mut detail);
        }
        SpecLinkViolation::ActionMissing {
            mut machine,
            mut action,
            from,
            mut detail,
        } => {
            work.retire_text(&mut machine);
            work.retire_text(&mut action);
            work.fixed(from);
            work.retire_text(&mut detail);
        }
        SpecLinkViolation::MachineMissing {
            mut machine,
            mut action,
            from,
            mut detail,
        } => {
            work.retire_text(&mut machine);
            work.retire_text(&mut action);
            work.fixed(from);
            work.retire_text(&mut detail);
        }
        SpecLinkViolation::ActionUncovered {
            mut machine,
            mut action,
        } => {
            work.retire_text(&mut machine);
            work.retire_text(&mut action);
        }
        SpecLinkViolation::ProjectionMissing {
            mut machine,
            mut action,
        } => {
            work.retire_text(&mut machine);
            work.retire_text(&mut action);
        }
        SpecLinkViolation::ProofUnresolved {
            mut machine,
            mut action,
            mut proof_name,
        } => {
            work.retire_text(&mut machine);
            work.retire_text(&mut action);
            work.retire_text(&mut proof_name);
        }
        SpecLinkViolation::ProofManifestRequired { mut machine } => {
            work.retire_text(&mut machine);
        }
        SpecLinkViolation::LinkedFormulaUnparsed {
            mut machine,
            mut invariant,
            mut detail,
        } => {
            work.retire_text(&mut machine);
            work.retire_text(&mut invariant);
            work.retire_text(&mut detail);
        }
        SpecLinkViolation::LinkedVariableUnparsed {
            mut machine,
            mut variable,
            mut detail,
        } => {
            work.retire_text(&mut machine);
            work.retire_text(&mut variable);
            work.retire_text(&mut detail);
        }
        SpecLinkViolation::LinkedTypedCarrierUnparsed {
            mut machine,
            subject,
            mut name,
            mut detail,
        } => {
            work.retire_text(&mut machine);
            work.fixed(subject);
            work.retire_text(&mut name);
            work.retire_text(&mut detail);
        }
        SpecLinkViolation::LinkedTypedCarrierDisagrees {
            mut machine,
            mut invariant,
            mut detail,
        } => {
            work.retire_text(&mut machine);
            work.retire_text(&mut invariant);
            work.retire_text(&mut detail);
        }
        SpecLinkViolation::SpecTypedBindingInvalid {
            mut machine,
            subject,
            mut name,
            mut binding,
            mut detail,
        } => {
            work.retire_text(&mut machine);
            work.fixed(subject);
            work.retire_text(&mut name);
            work.retire_text(&mut binding);
            work.retire_text(&mut detail);
        }
        SpecLinkViolation::SpecVariableSortMismatch {
            mut machine,
            mut variable,
            mut detail,
        } => {
            work.retire_text(&mut machine);
            work.retire_text(&mut variable);
            work.retire_text(&mut detail);
        }
        SpecLinkViolation::CleanTheoremUnresolved {
            mut machine,
            mut action,
            mut theorem,
            mut detail,
        } => {
            work.retire_text(&mut machine);
            work.retire_text(&mut action);
            work.retire_text(&mut theorem);
            work.retire_text(&mut detail);
        }
    }
}

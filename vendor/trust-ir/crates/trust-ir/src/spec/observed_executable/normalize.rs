// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
type Key<'a> = (u8, &'a str, &'a str, &'a str, &'a str, &'a str, u32);
fn key<'a, O: ExecutionObserver>(
    violation: &'a SpecLinkViolation,
    work: &mut Work<'_, '_, O>,
) -> R<Key<'a>> {
    work.admit(22, size_of::<Key<'_>>())?;
    Ok(match violation {
        SpecLinkViolation::DuplicateMachineIdentity { machine } => {
            (0, machine, "machine", "", "", "", 0)
        }
        SpecLinkViolation::DuplicateMemberIdentity {
            machine,
            member,
            name,
        } => (1, machine, member, name, "", "", 0),
        SpecLinkViolation::BlankSemanticValue {
            container,
            subject,
            field,
        } => (2, container, subject, field, "", "", 0),
        SpecLinkViolation::DuplicateBindingIdentity {
            machine,
            binding,
            identity,
        } => (3, machine, binding, identity, "", "", 0),
        SpecLinkViolation::AnchorWaiverConflict { machine, action } => {
            (4, machine, action, "", "", "", 0)
        }
        SpecLinkViolation::ReferenceContainerMismatch {
            container,
            machine,
            action,
            from,
        } => (5, container, machine, action, from, "", 0),
        SpecLinkViolation::TypedTargetRequired {
            machine,
            action,
            target,
        } => (6, machine, action, target, "", "", 0),
        SpecLinkViolation::ProjectionTargetIncompatible {
            machine,
            action,
            detail,
        } => (7, machine, action, detail, "", "", 0),
        SpecLinkViolation::ExecutableTargetInvalid {
            machine,
            action,
            target,
            function,
            detail,
        } => (8, machine, action, target, detail, "", *function),
        SpecLinkViolation::ActionMissing {
            machine,
            action,
            from,
            detail,
        } => (9, machine, action, from, detail, "", 0),
        SpecLinkViolation::ProjectionMissing { machine, action } => {
            (10, machine, action, "", "", "", 0)
        }
        SpecLinkViolation::ActionUncovered { machine, action } => {
            (11, machine, action, "", "", "", 0)
        }
        SpecLinkViolation::MachineMissing {
            machine,
            action,
            from,
            detail,
        } => (12, machine, action, from, detail, "", 0),
        SpecLinkViolation::ProofUnresolved {
            machine,
            action,
            proof_name,
        } => (13, machine, action, proof_name, "", "", 0),
        SpecLinkViolation::ProofManifestRequired { machine } => (14, machine, "", "", "", "", 0),
        SpecLinkViolation::LinkedVariableUnparsed {
            machine,
            variable,
            detail,
        } => (15, machine, variable, detail, "", "", 0),
        SpecLinkViolation::LinkedFormulaUnparsed {
            machine,
            invariant,
            detail,
        } => (16, machine, invariant, detail, "", "", 0),
        SpecLinkViolation::SpecVariableSortMismatch {
            machine,
            variable,
            detail,
        } => (17, machine, variable, detail, "", "", 0),
        SpecLinkViolation::SpecTypedBindingInvalid {
            machine,
            subject,
            name,
            binding,
            detail,
        } => (18, machine, subject, name, binding, detail, 0),
        SpecLinkViolation::CleanTheoremUnresolved {
            machine,
            action,
            theorem,
            detail,
        } => (19, machine, action, theorem, detail, "", 0),
        SpecLinkViolation::LinkedTypedCarrierUnparsed {
            machine,
            subject,
            name,
            detail,
        } => (20, machine, subject, name, detail, "", 0),
        SpecLinkViolation::LinkedTypedCarrierDisagrees {
            machine,
            invariant,
            detail,
        } => (21, machine, invariant, detail, "", "", 0),
    })
}
fn compare<O: ExecutionObserver>(
    left: &SpecLinkViolation,
    right: &SpecLinkViolation,
    work: &mut Work<'_, '_, O>,
) -> R<Ordering> {
    let left = key(left, work)?;
    let right = key(right, work)?;
    work.admit(1, 2 * size_of::<u8>())?;
    let order = left.0.cmp(&right.0);
    if order != Ordering::Equal {
        return Ok(order);
    }
    work.admit(1, 2 * size_of::<[&str; 5]>())?;
    let a = [left.1, left.2, left.3, left.4, left.5];
    let b = [right.1, right.2, right.3, right.4, right.5];
    let mut index = 0;
    while let Some(a) = work.at(&a, index)? {
        let b = work
            .at(&b, index)?
            .ok_or(ObservedValueError::InvalidRange)?;
        let order = work.compare(a, b)?;
        if order != Ordering::Equal {
            return Ok(order);
        }
        work.next(&mut index)?;
    }
    work.admit(1, 2 * size_of::<u32>())?;
    Ok(left.6.cmp(&right.6))
}
impl State<'_> {
    pub(super) fn normalize<O: ExecutionObserver>(&mut self, work: &mut Work<'_, '_, O>) -> R {
        let mut index = 1;
        loop {
            work.admit(1, 0)?;
            if index >= self.errors.len() {
                break;
            }
            let mut at = index;
            while at > 0 {
                work.admit(1, size_of::<usize>())?;
                let order = compare(&self.errors[at - 1], &self.errors[at], work)?;
                if order != Ordering::Greater {
                    break;
                }
                work.admit(3, 2 * size_of::<SpecLinkViolation>())?;
                self.errors.swap(at - 1, at);
                at -= 1;
            }
            work.next(&mut index)?;
        }
        let mut index = 1;
        loop {
            work.admit(1, 0)?;
            if index >= self.errors.len() {
                break;
            }
            if compare(&self.errors[index - 1], &self.errors[index], work)? == Ordering::Equal {
                // The exhaustive original key includes every current variant and field;
                // equality is full structural equality, including all static fields.
                let mut at = index;
                loop {
                    work.admit(2, size_of::<usize>())?;
                    let next = at
                        .checked_add(1)
                        .ok_or(ObservedValueError::CapacityOverflow)?;
                    if next >= self.errors.len() {
                        break;
                    }
                    work.admit(3, 2 * size_of::<SpecLinkViolation>())?;
                    self.errors.swap(at, next);
                    at = next;
                }
                work.admit(2, size_of::<Option<SpecLinkViolation>>())?;
                if self.pending.is_some() {
                    return Err(ObservedValueError::InvalidRange);
                }
                self.pending = self.errors.pop();
                work.step(size_of::<Option<SpecLinkViolation>>().saturating_add(1));
                if let Some(error) = self.pending.take() {
                    let _ = error.retire_observed(work.session, work.site);
                }
                work.admit(1, 0)?;
            } else {
                work.next(&mut index)?;
            }
        }
        Ok(())
    }
}

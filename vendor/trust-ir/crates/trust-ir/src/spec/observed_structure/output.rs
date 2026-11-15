// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[derive(Clone, Copy)]
pub(super) enum View<'a> {
    DuplicateMachineIdentity {
        machine: &'a str,
    },
    DuplicateMemberIdentity {
        machine: &'a str,
        member: &'static str,
        name: &'a str,
    },
    BlankSemanticValue {
        container: &'a str,
        subject: &'static str,
        field: &'static str,
    },
    DuplicateBindingIdentity {
        machine: &'a str,
        binding: &'static str,
        identity: &'a str,
    },
    AnchorWaiverConflict {
        machine: &'a str,
        action: &'a str,
    },
    ReferenceContainerMismatch {
        container: &'a str,
        machine: &'a str,
        action: &'a str,
        from: &'static str,
    },
    TypedTargetRequired {
        machine: &'a str,
        action: &'a str,
        target: &'static str,
    },
    ProjectionTargetIncompatible {
        machine: &'a str,
        action: &'a str,
        detail: &'a str,
    },
    ActionMissing {
        machine: &'a str,
        action: &'a str,
        from: &'static str,
        detail: &'a str,
    },
    MachineMissing {
        machine: &'a str,
        action: &'a str,
        from: &'static str,
        detail: &'a str,
    },
    ProjectionMissing {
        machine: &'a str,
        action: &'a str,
    },
    SpecTypedBindingInvalid {
        machine: &'a str,
        subject: &'static str,
        name: &'a str,
        binding: &'a str,
        detail: &'a str,
    },
    SpecVariableSortMismatch {
        machine: &'a str,
        variable: &'a str,
        detail: &'a str,
    },
}
pub(super) fn issue<O: ExecutionObserver>(
    errors: &mut Vec<SpecLinkViolation>,
    pending: &mut [String; 5],
    view: View<'_>,
    work: &mut Work<'_, '_, O>,
) -> R {
    work.admit(5, 0)?;
    for field in pending.iter() {
        if field.capacity() != 0 {
            return Err(ObservedValueError::InvalidRange);
        }
    }
    match view {
        View::DuplicateMachineIdentity { machine } => {
            work.text(machine, &mut pending[0])?;
            work.reserve(errors)?;
            work.admit(1, size_of::<SpecLinkViolation>())?;
            errors.push(SpecLinkViolation::DuplicateMachineIdentity {
                machine: take(&mut pending[0]),
            });
        }
        View::DuplicateMemberIdentity {
            machine,
            member,
            name,
        } => {
            work.text(machine, &mut pending[0])?;
            work.text(name, &mut pending[1])?;
            work.reserve(errors)?;
            work.admit(1, size_of::<SpecLinkViolation>())?;
            errors.push(SpecLinkViolation::DuplicateMemberIdentity {
                machine: take(&mut pending[0]),
                member,
                name: take(&mut pending[1]),
            });
        }
        View::BlankSemanticValue {
            container,
            subject,
            field,
        } => {
            work.text(container, &mut pending[0])?;
            work.reserve(errors)?;
            work.admit(1, size_of::<SpecLinkViolation>())?;
            errors.push(SpecLinkViolation::BlankSemanticValue {
                container: take(&mut pending[0]),
                subject,
                field,
            });
        }
        View::DuplicateBindingIdentity {
            machine,
            binding,
            identity,
        } => {
            work.text(machine, &mut pending[0])?;
            work.text(identity, &mut pending[1])?;
            work.reserve(errors)?;
            work.admit(1, size_of::<SpecLinkViolation>())?;
            errors.push(SpecLinkViolation::DuplicateBindingIdentity {
                machine: take(&mut pending[0]),
                binding,
                identity: take(&mut pending[1]),
            });
        }
        View::AnchorWaiverConflict { machine, action } => {
            work.text(machine, &mut pending[0])?;
            work.text(action, &mut pending[1])?;
            work.reserve(errors)?;
            work.admit(1, size_of::<SpecLinkViolation>())?;
            errors.push(SpecLinkViolation::AnchorWaiverConflict {
                machine: take(&mut pending[0]),
                action: take(&mut pending[1]),
            });
        }
        View::ReferenceContainerMismatch {
            container,
            machine,
            action,
            from,
        } => {
            work.text(container, &mut pending[0])?;
            work.text(machine, &mut pending[1])?;
            work.text(action, &mut pending[2])?;
            work.reserve(errors)?;
            work.admit(1, size_of::<SpecLinkViolation>())?;
            errors.push(SpecLinkViolation::ReferenceContainerMismatch {
                container: take(&mut pending[0]),
                machine: take(&mut pending[1]),
                action: take(&mut pending[2]),
                from,
            });
        }
        View::TypedTargetRequired {
            machine,
            action,
            target,
        } => {
            work.text(machine, &mut pending[0])?;
            work.text(action, &mut pending[1])?;
            work.reserve(errors)?;
            work.admit(1, size_of::<SpecLinkViolation>())?;
            errors.push(SpecLinkViolation::TypedTargetRequired {
                machine: take(&mut pending[0]),
                action: take(&mut pending[1]),
                target,
            });
        }
        View::ProjectionTargetIncompatible {
            machine,
            action,
            detail,
        } => {
            work.text(machine, &mut pending[0])?;
            work.text(action, &mut pending[1])?;
            work.text(detail, &mut pending[2])?;
            work.reserve(errors)?;
            work.admit(1, size_of::<SpecLinkViolation>())?;
            errors.push(SpecLinkViolation::ProjectionTargetIncompatible {
                machine: take(&mut pending[0]),
                action: take(&mut pending[1]),
                detail: take(&mut pending[2]),
            });
        }
        View::ActionMissing {
            machine,
            action,
            from,
            detail,
        } => {
            work.text(machine, &mut pending[0])?;
            work.text(action, &mut pending[1])?;
            work.text(detail, &mut pending[2])?;
            work.reserve(errors)?;
            work.admit(1, size_of::<SpecLinkViolation>())?;
            errors.push(SpecLinkViolation::ActionMissing {
                machine: take(&mut pending[0]),
                action: take(&mut pending[1]),
                from,
                detail: take(&mut pending[2]),
            });
        }
        View::MachineMissing {
            machine,
            action,
            from,
            detail,
        } => {
            work.text(machine, &mut pending[0])?;
            work.text(action, &mut pending[1])?;
            work.text(detail, &mut pending[2])?;
            work.reserve(errors)?;
            work.admit(1, size_of::<SpecLinkViolation>())?;
            errors.push(SpecLinkViolation::MachineMissing {
                machine: take(&mut pending[0]),
                action: take(&mut pending[1]),
                from,
                detail: take(&mut pending[2]),
            });
        }
        View::ProjectionMissing { machine, action } => {
            work.text(machine, &mut pending[0])?;
            work.text(action, &mut pending[1])?;
            work.reserve(errors)?;
            work.admit(1, size_of::<SpecLinkViolation>())?;
            errors.push(SpecLinkViolation::ProjectionMissing {
                machine: take(&mut pending[0]),
                action: take(&mut pending[1]),
            });
        }
        View::SpecTypedBindingInvalid {
            machine,
            subject,
            name,
            binding,
            detail,
        } => {
            work.text(machine, &mut pending[0])?;
            work.text(name, &mut pending[1])?;
            work.text(binding, &mut pending[2])?;
            work.text(detail, &mut pending[3])?;
            work.reserve(errors)?;
            work.admit(1, size_of::<SpecLinkViolation>())?;
            errors.push(SpecLinkViolation::SpecTypedBindingInvalid {
                machine: take(&mut pending[0]),
                subject,
                name: take(&mut pending[1]),
                binding: take(&mut pending[2]),
                detail: take(&mut pending[3]),
            });
        }
        View::SpecVariableSortMismatch {
            machine,
            variable,
            detail,
        } => {
            work.text(machine, &mut pending[0])?;
            work.text(variable, &mut pending[1])?;
            work.text(detail, &mut pending[2])?;
            work.reserve(errors)?;
            work.admit(1, size_of::<SpecLinkViolation>())?;
            errors.push(SpecLinkViolation::SpecVariableSortMismatch {
                machine: take(&mut pending[0]),
                variable: take(&mut pending[1]),
                detail: take(&mut pending[2]),
            });
        }
    }
    Ok(())
}

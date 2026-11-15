// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! All22 actual enum constructor witnesses; authored UNRUN.
use super::*;
pub(super) fn all() -> Vec<SpecLinkViolation> {
    vec![
        SpecLinkViolation::DuplicateMachineIdentity {
            machine: "DuplicateMachineIdentity_machine_λ".repeat(2),
        },
        SpecLinkViolation::DuplicateMemberIdentity {
            machine: "DuplicateMemberIdentity_machine_λ".repeat(3),
            member: "static",
            name: "DuplicateMemberIdentity_name_λ".repeat(5),
        },
        SpecLinkViolation::BlankSemanticValue {
            container: "BlankSemanticValue_container_λ".repeat(4),
            subject: "static",
            field: "static",
        },
        SpecLinkViolation::DuplicateBindingIdentity {
            machine: "DuplicateBindingIdentity_machine_λ".repeat(5),
            binding: "static",
            identity: "DuplicateBindingIdentity_identity_λ".repeat(7),
        },
        SpecLinkViolation::AnchorWaiverConflict {
            machine: "AnchorWaiverConflict_machine_λ".repeat(6),
            action: "AnchorWaiverConflict_action_λ".repeat(7),
        },
        SpecLinkViolation::ReferenceContainerMismatch {
            container: "ReferenceContainerMismatch_container_λ".repeat(7),
            machine: "ReferenceContainerMismatch_machine_λ".repeat(8),
            action: "ReferenceContainerMismatch_action_λ".repeat(9),
            from: "static",
        },
        SpecLinkViolation::TypedTargetRequired {
            machine: "TypedTargetRequired_machine_λ".repeat(8),
            action: "TypedTargetRequired_action_λ".repeat(9),
            target: "static",
        },
        SpecLinkViolation::ProjectionTargetIncompatible {
            machine: "ProjectionTargetIncompatible_machine_λ".repeat(9),
            action: "ProjectionTargetIncompatible_action_λ".repeat(10),
            detail: "ProjectionTargetIncompatible_detail_λ".repeat(11),
        },
        SpecLinkViolation::ExecutableTargetInvalid {
            machine: "ExecutableTargetInvalid_machine_λ".repeat(10),
            action: "ExecutableTargetInvalid_action_λ".repeat(11),
            target: "static",
            function: u32::MAX,
            detail: "ExecutableTargetInvalid_detail_λ".repeat(14),
        },
        SpecLinkViolation::ActionMissing {
            machine: "ActionMissing_machine_λ".repeat(11),
            action: "ActionMissing_action_λ".repeat(12),
            from: "static",
            detail: "ActionMissing_detail_λ".repeat(14),
        },
        SpecLinkViolation::MachineMissing {
            machine: "MachineMissing_machine_λ".repeat(12),
            action: "MachineMissing_action_λ".repeat(13),
            from: "static",
            detail: "MachineMissing_detail_λ".repeat(15),
        },
        SpecLinkViolation::ActionUncovered {
            machine: "ActionUncovered_machine_λ".repeat(13),
            action: "ActionUncovered_action_λ".repeat(14),
        },
        SpecLinkViolation::ProjectionMissing {
            machine: "ProjectionMissing_machine_λ".repeat(14),
            action: "ProjectionMissing_action_λ".repeat(15),
        },
        SpecLinkViolation::ProofUnresolved {
            machine: "ProofUnresolved_machine_λ".repeat(15),
            action: "ProofUnresolved_action_λ".repeat(16),
            proof_name: "ProofUnresolved_proof_name_λ".repeat(17),
        },
        SpecLinkViolation::ProofManifestRequired {
            machine: "ProofManifestRequired_machine_λ".repeat(16),
        },
        SpecLinkViolation::LinkedFormulaUnparsed {
            machine: "LinkedFormulaUnparsed_machine_λ".repeat(17),
            invariant: "LinkedFormulaUnparsed_invariant_λ".repeat(18),
            detail: "LinkedFormulaUnparsed_detail_λ".repeat(19),
        },
        SpecLinkViolation::LinkedVariableUnparsed {
            machine: "LinkedVariableUnparsed_machine_λ".repeat(18),
            variable: "LinkedVariableUnparsed_variable_λ".repeat(19),
            detail: "LinkedVariableUnparsed_detail_λ".repeat(20),
        },
        SpecLinkViolation::LinkedTypedCarrierUnparsed {
            machine: "LinkedTypedCarrierUnparsed_machine_λ".repeat(19),
            subject: "static",
            name: "LinkedTypedCarrierUnparsed_name_λ".repeat(21),
            detail: "LinkedTypedCarrierUnparsed_detail_λ".repeat(22),
        },
        SpecLinkViolation::LinkedTypedCarrierDisagrees {
            machine: "LinkedTypedCarrierDisagrees_machine_λ".repeat(20),
            invariant: "LinkedTypedCarrierDisagrees_invariant_λ".repeat(21),
            detail: "LinkedTypedCarrierDisagrees_detail_λ".repeat(22),
        },
        SpecLinkViolation::SpecTypedBindingInvalid {
            machine: "SpecTypedBindingInvalid_machine_λ".repeat(21),
            subject: "static",
            name: "SpecTypedBindingInvalid_name_λ".repeat(23),
            binding: "SpecTypedBindingInvalid_binding_λ".repeat(24),
            detail: "SpecTypedBindingInvalid_detail_λ".repeat(25),
        },
        SpecLinkViolation::SpecVariableSortMismatch {
            machine: "SpecVariableSortMismatch_machine_λ".repeat(22),
            variable: "SpecVariableSortMismatch_variable_λ".repeat(23),
            detail: "SpecVariableSortMismatch_detail_λ".repeat(24),
        },
        SpecLinkViolation::CleanTheoremUnresolved {
            machine: "CleanTheoremUnresolved_machine_λ".repeat(23),
            action: "CleanTheoremUnresolved_action_λ".repeat(24),
            theorem: "CleanTheoremUnresolved_theorem_λ".repeat(25),
            detail: "CleanTheoremUnresolved_detail_λ".repeat(26),
        },
    ]
}
pub(super) fn lengths(value: &SpecLinkViolation) -> Vec<usize> {
    match value {
        SpecLinkViolation::DuplicateMachineIdentity { machine } => vec![machine.len()],
        SpecLinkViolation::DuplicateMemberIdentity {
            machine,
            member: _,
            name,
        } => vec![machine.len(), name.len()],
        SpecLinkViolation::BlankSemanticValue {
            container,
            subject: _,
            field: _,
        } => vec![container.len()],
        SpecLinkViolation::DuplicateBindingIdentity {
            machine,
            binding: _,
            identity,
        } => vec![machine.len(), identity.len()],
        SpecLinkViolation::AnchorWaiverConflict { machine, action } => {
            vec![machine.len(), action.len()]
        }
        SpecLinkViolation::ReferenceContainerMismatch {
            container,
            machine,
            action,
            from: _,
        } => vec![container.len(), machine.len(), action.len()],
        SpecLinkViolation::TypedTargetRequired {
            machine,
            action,
            target: _,
        } => vec![machine.len(), action.len()],
        SpecLinkViolation::ProjectionTargetIncompatible {
            machine,
            action,
            detail,
        } => vec![machine.len(), action.len(), detail.len()],
        SpecLinkViolation::ExecutableTargetInvalid {
            machine,
            action,
            target: _,
            function: _,
            detail,
        } => vec![machine.len(), action.len(), detail.len()],
        SpecLinkViolation::ActionMissing {
            machine,
            action,
            from: _,
            detail,
        } => vec![machine.len(), action.len(), detail.len()],
        SpecLinkViolation::MachineMissing {
            machine,
            action,
            from: _,
            detail,
        } => vec![machine.len(), action.len(), detail.len()],
        SpecLinkViolation::ActionUncovered { machine, action } => vec![machine.len(), action.len()],
        SpecLinkViolation::ProjectionMissing { machine, action } => {
            vec![machine.len(), action.len()]
        }
        SpecLinkViolation::ProofUnresolved {
            machine,
            action,
            proof_name,
        } => vec![machine.len(), action.len(), proof_name.len()],
        SpecLinkViolation::ProofManifestRequired { machine } => vec![machine.len()],
        SpecLinkViolation::LinkedFormulaUnparsed {
            machine,
            invariant,
            detail,
        } => vec![machine.len(), invariant.len(), detail.len()],
        SpecLinkViolation::LinkedVariableUnparsed {
            machine,
            variable,
            detail,
        } => vec![machine.len(), variable.len(), detail.len()],
        SpecLinkViolation::LinkedTypedCarrierUnparsed {
            machine,
            subject: _,
            name,
            detail,
        } => vec![machine.len(), name.len(), detail.len()],
        SpecLinkViolation::LinkedTypedCarrierDisagrees {
            machine,
            invariant,
            detail,
        } => vec![machine.len(), invariant.len(), detail.len()],
        SpecLinkViolation::SpecTypedBindingInvalid {
            machine,
            subject: _,
            name,
            binding,
            detail,
        } => vec![machine.len(), name.len(), binding.len(), detail.len()],
        SpecLinkViolation::SpecVariableSortMismatch {
            machine,
            variable,
            detail,
        } => vec![machine.len(), variable.len(), detail.len()],
        SpecLinkViolation::CleanTheoremUnresolved {
            machine,
            action,
            theorem,
            detail,
        } => vec![machine.len(), action.len(), theorem.len(), detail.len()],
    }
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;
impl ObservationFrame {
    pub(crate) fn role(&self, role: InvocationRole) -> Self {
        Self {
            role,
            ..self.clone()
        }
    }
    pub(crate) fn ir_declarations(
        &self,
        owner: &'static str,
        decls: &[IRDecl],
    ) -> Option<ArtifactId> {
        let Ok(mut state) = self.recorder.shared.lock() else {
            return None;
        };
        if !state.reserve_artifact() {
            return None;
        }
        let mut meter = Meter::new(
            state.data.limits,
            state.data.retained_bytes,
            state.data.work,
        );
        let result = meter.ir_declarations(decls);
        if !state.measured(meter, result) {
            return None;
        }
        Some(state.store(
            owner,
            ArtifactPayload::IrDeclarations(decls.to_vec().into()),
            self.parent.clone(),
        ))
    }
}

#[cfg(feature = "trust-ir-backend")]
impl ObservationFrame {
    pub(crate) fn module(
        &self,
        owner: &'static str,
        module: &trust_ir::Module,
    ) -> Option<ArtifactId> {
        let Ok(mut state) = self.recorder.shared.lock() else {
            return None;
        };
        if !state.reserve_artifact() {
            return None;
        }
        let mut meter = Meter::new(
            state.data.limits,
            state.data.retained_bytes,
            state.data.work,
        );
        let result = meter.serialized(module);
        if !state.measured(meter, result) {
            return None;
        }
        Some(state.store(
            owner,
            ArtifactPayload::TrustIrModule(Arc::new(module.clone())),
            self.parent.clone(),
        ))
    }
}

#[cfg(feature = "trust-ir-backend")]
impl ObservationFrame {
    pub(crate) fn emission_input(
        &self,
        expr: &IRExpr,
        ty: &IRType,
        types: &std::collections::HashMap<crate::ir::VarId, IRType>,
        values: &std::collections::HashMap<crate::ir::VarId, trust_ir::ValueId>,
        parent: Option<ArtifactId>,
    ) -> Option<ArtifactId> {
        use crate::ir::{IRArg, IRExpr};
        let Ok(mut state) = self.recorder.shared.lock() else {
            return None;
        };
        if !state.reserve_artifact() {
            return None;
        }
        let mut meter = Meter::new(
            state.data.limits,
            state.data.retained_bytes,
            state.data.work,
        );
        let mut operands = Vec::new();
        let result = (|| {
            meter.ir_expr(expr)?;
            meter.ir_type(ty)?;
            let mut operand = |var| -> Result<(), ObservationGap> {
                meter.add(
                    size_of::<(crate::ir::VarId, Option<IRType>, Option<trust_ir::ValueId>)>() * 2,
                )?;
                if let Some(ty) = types.get(&var) {
                    meter.ir_type(ty)?;
                }
                operands.push((var, types.get(&var).cloned(), values.get(&var).copied()));
                Ok(())
            };
            let mut arg = |arg: &IRArg| -> Result<(), ObservationGap> {
                if let IRArg::Var(var) = arg {
                    operand(*var)?;
                }
                Ok(())
            };
            match expr {
                IRExpr::Ctor { args, .. }
                | IRExpr::Apply { args, .. }
                | IRExpr::PartialApply { args, .. } => {
                    for a in args {
                        arg(a)?;
                    }
                }
                IRExpr::ClosureApply { closure, args } => {
                    arg(closure)?;
                    for a in args {
                        arg(a)?;
                    }
                }
                IRExpr::Proj { arg: a, .. }
                | IRExpr::Tag(a)
                | IRExpr::Box { arg: a, .. }
                | IRExpr::Unbox { arg: a, .. } => arg(a)?,
                IRExpr::UProj { var, .. }
                | IRExpr::SProj { var, .. }
                | IRExpr::IsShared(var)
                | IRExpr::Reset(var) => operand(*var)?,
                IRExpr::Reuse { var, args, .. } => {
                    for a in args {
                        arg(a)?;
                    }
                    operand(*var)?;
                }
                IRExpr::Lit(_) | IRExpr::String(_) => {}
            }
            Ok(())
        })();
        if !state.measured(meter, result) {
            return None;
        }
        Some(state.store(
            "actual emitter input",
            ArtifactPayload::EmitterInput {
                value: Arc::new(expr.clone()),
                ty: ty.clone(),
                operands: operands.into(),
            },
            parent,
        ))
    }
    pub(crate) fn emission_operation(
        &self,
        before: Option<ArtifactId>,
        operation: EmissionOperation,
    ) {
        self.emission_operation_with_types(before, &[], &[], || operation);
    }
    pub(crate) fn emission_operation_with_types(
        &self,
        before: Option<ArtifactId>,
        types: &[&trust_ir::Ty],
        arguments: &[trust_ir::ValueId],
        make: impl FnOnce() -> EmissionOperation,
    ) {
        let Some(before) = before else {
            return;
        };
        let Ok(mut state) = self.recorder.shared.lock() else {
            return;
        };
        if !state.reserve_artifact() {
            return;
        }
        let mut meter = Meter::new(
            state.data.limits,
            state.data.retained_bytes,
            state.data.work,
        );
        let result = (|| {
            meter.add(size_of::<EmissionOperation>())?;
            for _ in arguments {
                meter.add(size_of::<trust_ir::ValueId>())?;
            }
            for ty in types {
                meter.serialized(*ty)?;
            }
            Ok(())
        })();
        if !state.measured(meter, result) {
            return;
        }
        // The fixed producer closure clones existing typed payloads only AFTER
        // their actual full structural/work preflight. Never an arbitrary pass.
        let after = state.store(
            "actual emitter operation",
            ArtifactPayload::EmissionOperation(make()),
            Some(before.clone()),
        );
        state.event(
            self,
            "TrustIR emitter dispatch",
            before,
            Some(after),
            "actual selected owner branch",
        );
    }
}

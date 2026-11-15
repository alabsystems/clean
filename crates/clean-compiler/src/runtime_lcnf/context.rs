// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{
    RuntimeCatalogDeclaration, RuntimeEnvironmentCapture, RuntimeSourceCaptureLimits,
    RuntimeSourceRecord,
};
use super::{RuntimeLcnfOutput, RuntimeLimits, RuntimeLowerError};
use clean_kernel::{Environment, ExprKind, Level, Name};
use clean_olean::import::runtime::{
    extract_olean_runtime_parts, RuntimeBody, RuntimeFamily, RuntimeOleanInput, RuntimeOleanPart,
    RuntimePartExtraction, RuntimePartIdentity,
};
use clean_olean::module::ConstantKind;
use std::collections::{BTreeMap, BTreeSet};

/// A caller selects a cumulative snapshot explicitly. Other supplied parts
/// remain observed; they are neither merged by Name nor discarded.
#[derive(Clone, Debug)]
pub struct RuntimeModuleInput {
    pub base: RuntimeOleanInput,
    pub server: Option<RuntimeOleanInput>,
    pub private: Option<RuntimeOleanInput>,
    pub selected: RuntimeOleanPart,
}

#[derive(Clone, Debug)]
pub struct RuntimeModuleCapture {
    pub selected: RuntimeOleanPart,
    pub parts: Vec<RuntimePartExtraction>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RuntimeRowOrigin {
    pub name: Name,
    pub provenance: RuntimeProvenance,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RuntimeProvenance {
    Captured {
        module_index: usize,
        part: RuntimePartIdentity,
        borrowed_prefix: Vec<RuntimePartIdentity>,
        row_index: usize,
    },
    Environment {
        snapshot_blake3: [u8; 32],
        row_index: usize,
        added_since_baseline: bool,
    },
}

#[derive(Clone, Debug)]
pub struct RuntimeContext {
    pub(super) modules: Vec<RuntimeModuleCapture>,
    pub(super) names: BTreeMap<Name, Vec<(usize, usize, usize)>>,
    pub(super) errors: Vec<RuntimeLowerError>,
    pub(super) catalog: BTreeMap<Name, Vec<(RuntimeCatalogDeclaration, RuntimeRowOrigin)>>,
    environment_capture: Option<RuntimeEnvironmentCapture>,
}

impl RuntimeContext {
    /// Diagnostic owned-IR and Trust-IR emission, conditional on captured headers.
    /// Keeps the full dependency report even when selecting/emitting fails. The
    /// named call/PAP closure is not a proof of dynamic-entry or runtime closure.
    #[cfg(feature = "trust-ir-backend")]
    pub fn lower_trust_ir_diagnostic(
        &self,
        root: &Name,
        limits: RuntimeLimits,
        mode: crate::emit_trust_ir::RuntimeLowering,
    ) -> Result<super::RuntimeEmissionOutput, RuntimeLowerError> {
        let captured = self.lower_ir(root, limits)?;
        let emission = super::emission::emit(&captured, limits, mode);
        Ok(super::RuntimeEmissionOutput { captured, emission })
    }
    /// Parse captured bytes through the public runtime reader. There is no
    /// entrypoint that converts a caller's favorable Name/body record into an
    /// authenticated context. This is still only diagnostic capture/typing.
    pub fn capture(inputs: Vec<RuntimeModuleInput>) -> Self {
        let modules = inputs
            .into_iter()
            .map(|input| RuntimeModuleCapture {
                selected: input.selected,
                parts: extract_olean_runtime_parts(input.base, input.server, input.private),
            })
            .collect();
        Self::index(modules)
    }

    /// Combine exact captured imports with an independently observed eager
    /// source-check delta. Both environments are read-only, and every source
    /// row (including bodyless partials) remains in the returned capture.
    /// No caller-supplied source string or provenance stamp grants admission.
    /// Duplicate identities across the two surfaces are refused, not selected
    /// by priority or by display name; no opaque-to-runtime substitution occurs.
    pub fn capture_with_environment(
        inputs: Vec<RuntimeModuleInput>,
        before: &Environment,
        after: &Environment,
        sources: Vec<RuntimeSourceRecord>,
    ) -> Self {
        Self::capture_with_environment_limits(
            inputs,
            before,
            after,
            sources,
            RuntimeSourceCaptureLimits::default(),
        )
    }

    /// Explicit limits only restrict observation. A truncated capture never
    /// obtains a digest or usable source catalog; original imported rows remain.
    pub fn capture_with_environment_limits(
        inputs: Vec<RuntimeModuleInput>,
        before: &Environment,
        after: &Environment,
        sources: Vec<RuntimeSourceRecord>,
        limits: RuntimeSourceCaptureLimits,
    ) -> Self {
        let mut context = Self::capture(inputs);
        let capture = RuntimeEnvironmentCapture::capture(before, after, sources, limits);
        context.errors.extend(
            capture
                .errors
                .iter()
                .cloned()
                .map(RuntimeLowerError::Capture),
        );
        if let Some(snapshot_blake3) = capture.snapshot_blake3 {
            let all = capture.after.iter().map(|r| (r.name.clone(), r)).collect();
            for (row_index, row) in capture.after.iter().enumerate() {
                context.catalog.entry(row.name.clone()).or_default().push((
                    row.catalog(&all),
                    RuntimeRowOrigin {
                        name: row.name.clone(),
                        provenance: RuntimeProvenance::Environment {
                            snapshot_blake3,
                            row_index,
                            added_since_baseline: capture.added.contains(&row.name),
                        },
                    },
                ));
            }
        }
        context.environment_capture = Some(capture);
        context
    }

    pub fn environment_capture(&self) -> Option<&RuntimeEnvironmentCapture> {
        self.environment_capture.as_ref()
    }

    pub(super) fn index(modules: Vec<RuntimeModuleCapture>) -> Self {
        let mut value = Self {
            modules,
            names: BTreeMap::new(),
            errors: Vec::new(),
            catalog: BTreeMap::new(),
            environment_capture: None,
        };
        for (module_index, module) in value.modules.iter().enumerate() {
            let Some((part_index, part)) = module
                .parts
                .iter()
                .enumerate()
                .find(|(_, part)| part.identity.part == module.selected)
            else {
                value.errors.push(RuntimeLowerError::Capture(format!(
                    "module {module_index}: selected {:?} part is absent",
                    module.selected
                )));
                continue;
            };
            if let Some(error) = &part.error {
                value.errors.push(RuntimeLowerError::Capture(format!(
                    "module {module_index} {:?}: {error}",
                    module.selected
                )));
            }
            if part.source_row_count != Some(part.rows.len()) {
                value.errors.push(RuntimeLowerError::Capture(format!(
                    "module {module_index}: unknown or inconsistent row population"
                )));
            }
            for (index, row) in part.rows.iter().enumerate() {
                if index != row.index {
                    value.errors.push(RuntimeLowerError::Capture(format!(
                        "module {module_index}: noncanonical row index {}",
                        row.index
                    )));
                }
                match &row.declaration {
                    Ok(declaration) => {
                        value
                            .names
                            .entry(declaration.name.clone())
                            .or_default()
                            .push((module_index, part_index, index));
                        value
                            .catalog
                            .entry(declaration.name.clone())
                            .or_default()
                            .push((
                                declaration.into(),
                                RuntimeRowOrigin {
                                    name: declaration.name.clone(),
                                    provenance: RuntimeProvenance::Captured {
                                        module_index,
                                        part: part.identity.clone(),
                                        borrowed_prefix: part.borrowed_prefix.clone(),
                                        row_index: index,
                                    },
                                },
                            ));
                    }
                    Err(error) => value.errors.push(RuntimeLowerError::Capture(format!(
                        "module {module_index} row {index}: unknown identity: {error}"
                    ))),
                }
            }
        }
        value
    }

    pub fn captures(&self) -> &[RuntimeModuleCapture] {
        &self.modules
    }
    pub fn capture_errors(&self) -> &[RuntimeLowerError] {
        &self.errors
    }

    pub fn declaration(
        &self,
        name: &Name,
    ) -> Result<&RuntimeCatalogDeclaration, RuntimeLowerError> {
        self.entry(name).map(|(row, _)| row)
    }

    pub fn origin(&self, name: &Name) -> Result<RuntimeRowOrigin, RuntimeLowerError> {
        self.entry(name).map(|(_, origin)| origin.clone())
    }

    fn entry(
        &self,
        name: &Name,
    ) -> Result<&(RuntimeCatalogDeclaration, RuntimeRowOrigin), RuntimeLowerError> {
        if let Some(error) = self.errors.first() {
            return Err(error.clone());
        }
        match self.catalog.get(name).map(Vec::as_slice) {
            None | Some([]) => Err(RuntimeLowerError::Missing(name.clone())),
            Some([row]) => Ok(row),
            Some(_) => Err(RuntimeLowerError::Ambiguous(name.clone())),
        }
    }

    pub fn dependency_closure(
        &self,
        root: &Name,
        limits: RuntimeLimits,
    ) -> Result<Vec<RuntimeRowOrigin>, RuntimeLowerError> {
        let mut pending = vec![root.clone()];
        let mut seen = BTreeSet::new();
        while let Some(name) = pending.pop() {
            if !seen.insert(name.clone()) {
                continue;
            }
            if seen.len() > limits.declarations {
                return Err(RuntimeLowerError::Resource("declaration closure"));
            }
            let declaration = self.declaration(&name)?;
            if !declaration.represented_fields_complete {
                return Err(RuntimeLowerError::Incomplete {
                    name,
                    detail: declaration.issues.join("; "),
                });
            }
            self.validate_family(declaration)?;
            pending.extend(declaration.dependencies.iter().cloned());
        }
        seen.into_iter().map(|name| self.origin(&name)).collect()
    }

    /// Lower the exact stored definition with a closed captured context. The
    /// returned LCNF has no attached proof/admission and is not yet runtime IR.
    pub fn lower_definition(
        &self,
        root: &Name,
        limits: RuntimeLimits,
    ) -> Result<RuntimeLcnfOutput, RuntimeLowerError> {
        let dependencies = self.dependency_closure(root, limits)?;
        super::lower::lower_definition(self, root, dependencies, limits)
    }

    /// Diagnostic, pre-reference-counting runtime IR. Every selected dependency
    /// has an explicit outcome; a successfully lowered root does not establish
    /// that its callees, runtime ABI, memory management or refinement are closed.
    pub fn lower_ir(
        &self,
        root: &Name,
        limits: RuntimeLimits,
    ) -> Result<super::RuntimeIrOutput, RuntimeLowerError> {
        super::ir::lower(self, root, limits)
    }

    fn validate_family(
        &self,
        declaration: &RuntimeCatalogDeclaration,
    ) -> Result<(), RuntimeLowerError> {
        let name = &declaration.name;
        let reject = |detail: &str| RuntimeLowerError::Family {
            name: name.clone(),
            detail: detail.into(),
        };
        match (&declaration.kind, &declaration.family) {
            (ConstantKind::Definition, RuntimeFamily::None) => {
                if !matches!(declaration.body, RuntimeBody::Stored(Ok(_))) {
                    return Err(RuntimeLowerError::MissingBody(name.clone()));
                }
            }
            (
                ConstantKind::Inductive,
                RuntimeFamily::Inductive {
                    all,
                    constructors,
                    num_params,
                    num_indices,
                    num_nested,
                    is_nested,
                    is_unsafe,
                    ..
                },
            ) => {
                // Initial data-family contract; larger dependent/nested families
                // are retained but not inferred from their names or arities.
                if all != std::slice::from_ref(name)
                    || *num_params != 0
                    || *num_indices != 0
                    || *num_nested != Some(0)
                    || *is_nested
                    || *is_unsafe
                    || constructors.is_empty()
                {
                    return Err(reject("only complete single nonparametric nonindexed safe data families are supported"));
                }
                let mut unique = BTreeSet::new();
                for (index, constructor) in constructors.iter().enumerate() {
                    if !unique.insert(constructor) {
                        return Err(reject("duplicate constructor identity"));
                    }
                    let row = self.declaration(constructor)?;
                    if !matches!(&row.family, RuntimeFamily::Constructor {
                        inductive, index: actual, num_params: params, ..
                    } if inductive == name && *actual as usize == index && params == num_params)
                    {
                        return Err(reject(
                            "constructor membership/index/parameter metadata disagrees",
                        ));
                    }
                }
            }
            (
                ConstantKind::Constructor,
                RuntimeFamily::Constructor {
                    inductive,
                    index,
                    num_params,
                    num_fields,
                    is_unsafe,
                },
            ) => {
                if *is_unsafe {
                    return Err(reject("unsafe family layout is unmeasured"));
                }
                let owner = self.declaration(inductive)?;
                if !matches!(&owner.family, RuntimeFamily::Inductive { constructors, num_params: params, .. }
                    if constructors.get(*index as usize) == Some(name) && params == num_params)
                {
                    return Err(reject("constructor owner metadata disagrees"));
                }
                let mut ty = declaration
                    .type_
                    .as_ref()
                    .map_err(|_| reject("constructor type decode failed"))?;
                let mut binders = 0u32;
                while let ExprKind::Pi(_, _, body) = ty.kind() {
                    binders = binders
                        .checked_add(1)
                        .ok_or_else(|| reject("constructor binder overflow"))?;
                    ty = body;
                }
                let expected_levels: Vec<_> = declaration
                    .level_params
                    .iter()
                    .cloned()
                    .map(Level::param)
                    .collect();
                if Some(binders) != num_params.checked_add(*num_fields)
                    || declaration.level_params.len() != owner.level_params.len()
                    || !matches!(ty.kind(), ExprKind::Const(head, levels) if head == inductive && levels.as_ref() == expected_levels.as_slice())
                {
                    return Err(reject("constructor header and field metadata disagree"));
                }
            }
            (
                ConstantKind::Recursor,
                RuntimeFamily::Recursor {
                    all,
                    num_params,
                    num_indices,
                    num_motives,
                    num_minors,
                    is_unsafe,
                    rules,
                    ..
                },
            ) => {
                if all.len() != 1 || *num_indices != 0 || *num_motives != 1 || *is_unsafe {
                    return Err(reject("recursor family shape is unmeasured"));
                }
                let owner = self.declaration(&all[0])?;
                let RuntimeFamily::Inductive {
                    constructors,
                    num_params: params,
                    ..
                } = &owner.family
                else {
                    return Err(reject("recursor owner is not a represented family"));
                };
                if params != num_params
                    || *num_minors as usize != constructors.len()
                    || rules.len() != constructors.len()
                {
                    return Err(reject("recursor rule/parameter population disagrees"));
                }
                for (rule, constructor) in rules.iter().zip(constructors) {
                    let target = self.declaration(constructor)?;
                    if &rule.constructor != constructor
                        || rule.rhs.is_err()
                        || !matches!(&target.family, RuntimeFamily::Constructor { num_fields, .. }
                            if *num_fields == rule.num_fields)
                    {
                        return Err(reject(
                            "recursor rule identity/field count/RHS is incomplete",
                        ));
                    }
                }
            }
            _ => {
                return Err(reject(
                    "logical stub, quotient, opaque or unsupported family kind",
                ))
            }
        }
        Ok(())
    }
}

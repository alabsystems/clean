//! Checked storage binding for a statically targeted closure environment.
//!
//! A closure layout describes captures, not a function-pointer word. Memory
//! transport therefore requires a unique typed constructor target in this exact
//! immutable module. Missing or conflicting targets cannot be reconstructed from
//! bytes. This query grants no source, execution or proof authority.
use crate::{ClosureLayoutDescriptor, ClosureTyId, Constant, FuncId, FuncTy, Inst, Module, Ty};

#[derive(Clone, Copy, Debug)]
pub struct ClosureStorageBinding<'module> {
    pub target: FuncId,
    pub layout: &'module ClosureLayoutDescriptor,
    pub captures: &'module [Ty],
}

impl Module {
    /// Closure environments whose bytes occur in a typed memory operation,
    /// including inline aggregate fields and nested captures. Pointer pointees
    /// and function signatures are not stored environment bytes.
    pub fn closure_storage_types(&self) -> std::collections::BTreeSet<ClosureTyId> {
        use std::collections::{BTreeSet, HashSet};
        let mut result = BTreeSet::new();
        let mut pending = Vec::new();
        for node in self.instructions() {
            match &node.inst {
                Inst::Alloca { ty, .. } | Inst::Load { ty, .. } | Inst::Store { ty, .. } => {
                    pending.push(ty.clone());
                }
                _ => {}
            }
        }
        let mut seen = HashSet::new();
        while let Some(ty) = pending.pop() {
            if !seen.insert(ty.clone()) {
                continue;
            }
            match ty {
                Ty::Closure(id) => {
                    result.insert(id);
                    if let Some(closure) = self.closure_type(id) {
                        pending.extend(closure.captures.iter().cloned());
                    }
                }
                Ty::Tuple(fields) => pending.extend(fields),
                // A tensor has no byte image, but its element is an inline
                // child exactly as a vector's is: following it only adds
                // closure types to check, which fails closed.
                Ty::Vector(element, _) | Ty::Tensor(element, _) => pending.push(*element),
                Ty::Array(element, _) => {
                    if let Some(element) = self.types.get(element.as_usize()) {
                        pending.push(element.clone());
                    }
                }
                Ty::Struct(id) => {
                    for definition in self.structs.iter().filter(|row| row.id == id) {
                        pending.extend(definition.fields.iter().map(|field| field.ty.clone()));
                    }
                }
                Ty::Enum(id) => {
                    for definition in self.enums.iter().filter(|row| row.id == id) {
                        pending.extend(
                            definition
                                .variants
                                .iter()
                                .flat_map(|variant| variant.fields.iter().cloned()),
                        );
                    }
                }
                _ => {}
            }
        }
        result
    }

    /// Bind a capture-only byte image to its unique constructor target. General
    /// dynamically targeted closures remain register values; they are not given
    /// an implicit function-pointer representation by this restricted operation.
    pub fn closure_storage_binding(
        &self,
        closure: ClosureTyId,
    ) -> Result<ClosureStorageBinding<'_>, &'static str> {
        self.validate_closure_layouts()
            .map_err(|_| "invalid closure layouts")?;
        let layout = self
            .closure_layout_descriptor(closure)
            .map_err(|_| "invalid closure layout")?
            .ok_or("missing closure layout")?;
        let ty = self.closure_type(closure).ok_or("missing closure type")?;
        let apparent = self.func_type(ty.func).ok_or("missing closure signature")?;
        if apparent.is_vararg || apparent.abi.is_some() {
            return Err("closure storage requires an unadapted signature");
        }
        let mut target = None;
        let mut bind = |found| {
            if target.is_some_and(|previous| previous != found) {
                return Err("conflicting closure storage targets");
            }
            target = Some(found);
            Ok(())
        };
        // Constants carry no nested type annotation. Refuse those forms rather
        // than guessing which closure type their target belongs to.
        let mut constant = |ty: &Ty, value: &Constant| {
            if let (Ty::Closure(id), Constant::Closure { func, captures }) = (ty, value) {
                if captures.iter().any(contains_closure) {
                    return Err("nested constant closure storage is unsupported");
                }
                if *id == closure {
                    bind(*func)?;
                }
            } else if contains_closure(value) {
                return Err("untyped constant closure storage is unsupported");
            }
            Ok(())
        };
        for node in self.instructions() {
            if let Inst::Const { ty, value } = &node.inst {
                constant(ty, value)?;
            }
        }
        for global in &self.globals {
            if let Some(value) = &global.initializer {
                constant(&global.ty, value)?;
            }
        }
        for node in self.instructions() {
            if let Inst::MakeClosure { ty, func, .. } = &node.inst
                && *ty == closure
            {
                bind(*func)?;
            }
        }
        let target = target.ok_or("missing closure storage target")?;
        let catalog = crate::ModuleFunctionCatalog::new(self);
        let function = catalog
            .unique(target)
            .ok_or("missing or ambiguous closure target")?;
        if function.is_declaration() {
            return Err("closure storage target has no body");
        }
        let mut params = ty.captures.clone();
        params.extend(apparent.params.iter().cloned());
        let physical = FuncTy {
            params,
            returns: apparent.returns.clone(),
            is_vararg: false,
            abi: None,
        };
        if self.func_type(function.ty) != Some(&physical) {
            return Err("closure storage target signature mismatch");
        }
        Ok(ClosureStorageBinding {
            target,
            layout,
            captures: &ty.captures,
        })
    }
}

fn contains_closure(value: &Constant) -> bool {
    let mut found = false;
    value.visit_constants(|value| found |= matches!(value, Constant::Closure { .. }));
    found
}

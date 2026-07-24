// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Context-aware runtime coercions for the evaluator.
//!
//! `crate::coercion` handles shape-based coercions that depend only on source
//! and target types. This module extends those rules with evaluator-only cases
//! that need `ExecContext` metadata, such as trait impl lookup and function
//! signature lookup.

use super::Interpreter;
use crate::coercion::coerce_value;
use crate::memory::Address;
use crate::types::{Lifetime, Mutability, RustType, VTable};
use crate::values::{FatPointer, Value};
use std::collections::HashSet;

impl Interpreter {
    pub(super) fn coerce_runtime_value(&self, value: &Value, target: &RustType) -> Option<Value> {
        coerce_value(value, &value.get_type(), target)
            .or_else(|| self.coerce_function_item(value, target))
            .or_else(|| self.coerce_unsized(value, target))
    }

    fn coerce_function_item(&self, value: &Value, target: &RustType) -> Option<Value> {
        let Value::FnPtr { name } = value else {
            return None;
        };
        let RustType::Function {
            params: target_params,
            ret: target_ret,
        } = target
        else {
            return None;
        };
        let func_def = self.ctx.get_function(name)?;

        let actual_params: Vec<_> = func_def
            .params
            .iter()
            .map(|(_, ty)| self.normalize_runtime_type(ty))
            .collect();
        let expected_params: Vec<_> = target_params
            .iter()
            .map(|ty| self.normalize_runtime_type(ty))
            .collect();
        if actual_params != expected_params {
            return None;
        }

        let actual_ret = self.normalize_runtime_type(&func_def.ret_ty);
        let expected_ret = self.normalize_runtime_type(target_ret);
        if actual_ret != expected_ret {
            return None;
        }

        Some(value.clone())
    }

    /// Dyn-trait coercions: concrete unsizing and dyn upcasting, including
    /// through wrapper types like Box, Rc, Arc, and references.
    ///
    /// Handles:
    /// - `T` → `dyn Trait` (bare unsizing)
    /// - `Box<T>` → `Box<dyn Trait>` (smart pointer unsizing)
    /// - `&[T; N]` → `&[T]` (array-to-slice unsizing)
    /// - `&T` → `&dyn Trait` (reference unsizing)
    /// - `dyn Sub` → `dyn Super` (trait-object upcasting)
    fn coerce_unsized(&self, value: &Value, target: &RustType) -> Option<Value> {
        // Bare unsizing: T → dyn Trait
        if let RustType::DynTrait { trait_name, .. } = target {
            return self.coerce_to_dyn_trait_value(value, trait_name);
        }

        // Box<T> → Box<dyn Trait>
        if let RustType::Box { inner } = target {
            if let RustType::DynTrait { trait_name, .. } = inner.as_ref() {
                return self.coerce_box_to_dyn_trait(value, trait_name);
            }
        }

        // &T → &dyn Trait (reference unsizing)
        if let RustType::Reference {
            inner: target_inner,
            mutability: target_mut,
            lifetime: target_lifetime,
        } = target
        {
            if let RustType::Slice { elem } = target_inner.as_ref() {
                return self.coerce_ref_to_slice(value, elem, *target_mut, target_lifetime);
            }
            if let RustType::DynTrait { trait_name, .. } = target_inner.as_ref() {
                return self.coerce_ref_to_dyn_trait(
                    value,
                    trait_name,
                    *target_mut,
                    target_lifetime,
                );
            }
        }

        None
    }

    /// Coerce a concrete value to `dyn Trait`, or upcast an existing trait
    /// object to one of its registered supertraits.
    fn coerce_to_dyn_trait_value(&self, value: &Value, trait_name: &str) -> Option<Value> {
        if let Value::TraitObject {
            data,
            vtable,
            lifetime: source_lifetime,
        } = value
        {
            return self.upcast_trait_object(data.as_ref(), vtable, trait_name, source_lifetime);
        }

        let concrete_type = match value {
            Value::Struct { name, .. } | Value::Enum { name, .. } | Value::Union { name, .. } => {
                name.as_str()
            }
            _ => return None,
        };

        let vtable = self.build_trait_object_vtable(concrete_type, trait_name)?;
        Some(Value::TraitObject {
            data: Box::new(value.clone()),
            vtable,
            lifetime: Lifetime::Static,
        })
    }

    fn coerce_box_to_dyn_trait(&self, value: &Value, target_trait: &str) -> Option<Value> {
        match value {
            Value::FatPtr(FatPointer {
                data_pointer,
                metadata,
            }) => {
                let source_trait = match metadata {
                    crate::values::FatPtrMetadata::VtablePtr(vtable_ptr) => {
                        vtable_ptr.trait_name.as_str()
                    }
                    crate::values::FatPtrMetadata::SliceLen(_) => return None,
                };
                if !self.trait_is_same_or_supertrait(source_trait, target_trait) {
                    return None;
                }
                Some(Value::FatPtr(FatPointer::vtable(
                    data_pointer.as_ref().clone(),
                    target_trait,
                )))
            }
            _ => {
                let concrete_type = value.concrete_type_name()?;
                self.build_trait_object_vtable(concrete_type, target_trait)?;
                Some(Value::FatPtr(FatPointer::vtable(
                    value.clone(),
                    target_trait,
                )))
            }
        }
    }

    fn coerce_ref_to_slice(
        &self,
        value: &Value,
        target_elem: &RustType,
        target_mutability: Mutability,
        target_lifetime: &Lifetime,
    ) -> Option<Value> {
        let Value::Reference {
            addr,
            mutability: src_mutability,
            lifetime: src_lifetime,
            referent,
        } = value
        else {
            return None;
        };
        let mut_ok =
            target_mutability == Mutability::Shared || *src_mutability == Mutability::Mutable;
        if !mut_ok {
            return None;
        }
        if !src_lifetime.outlives(target_lifetime) && src_lifetime != target_lifetime {
            return None;
        }
        let len = match referent.as_deref() {
            Some(Value::Array(values)) => {
                let elem_ty = values.first().map_or(RustType::Unit, Value::get_type);
                if elem_ty != *target_elem && !elem_ty.is_compatible(target_elem) {
                    return None;
                }
                values.len()
            }
            Some(_) => return None,
            None => self.reference_array_len(*addr, target_elem)?,
        };
        Some(Value::FatPtr(FatPointer::slice(
            Value::Reference {
                addr: *addr,
                mutability: target_mutability,
                lifetime: target_lifetime.clone(),
                referent: referent.clone(),
            },
            len,
        )))
    }

    fn coerce_ref_to_dyn_trait(
        &self,
        value: &Value,
        target_trait: &str,
        target_mutability: Mutability,
        target_lifetime: &Lifetime,
    ) -> Option<Value> {
        match value {
            Value::Reference {
                addr,
                mutability: src_mutability,
                lifetime: src_lifetime,
                referent,
            } => {
                let mut_ok = target_mutability == Mutability::Shared
                    || *src_mutability == Mutability::Mutable;
                if !mut_ok {
                    return None;
                }
                if !src_lifetime.outlives(target_lifetime) && src_lifetime != target_lifetime {
                    return None;
                }
                let concrete_type = referent
                    .as_deref()
                    .and_then(Value::concrete_type_name)
                    .map(str::to_string)
                    .or_else(|| self.reference_concrete_type_name(*addr))?;
                self.build_trait_object_vtable(&concrete_type, target_trait)?;
                Some(Value::FatPtr(FatPointer::vtable(
                    Value::Reference {
                        addr: *addr,
                        mutability: target_mutability,
                        lifetime: target_lifetime.clone(),
                        referent: referent.clone(),
                    },
                    target_trait,
                )))
            }
            Value::FatPtr(FatPointer {
                data_pointer,
                metadata,
            }) => {
                let source_trait = match metadata {
                    crate::values::FatPtrMetadata::VtablePtr(vtable_ptr) => {
                        vtable_ptr.trait_name.as_str()
                    }
                    crate::values::FatPtrMetadata::SliceLen(_) => return None,
                };
                let Value::Reference {
                    addr,
                    mutability: src_mutability,
                    lifetime: src_lifetime,
                    referent,
                } = data_pointer.as_ref()
                else {
                    return None;
                };
                let mut_ok = target_mutability == Mutability::Shared
                    || *src_mutability == Mutability::Mutable;
                if !mut_ok {
                    return None;
                }
                if !src_lifetime.outlives(target_lifetime) && src_lifetime != target_lifetime {
                    return None;
                }
                if !self.trait_is_same_or_supertrait(source_trait, target_trait) {
                    return None;
                }
                Some(Value::FatPtr(FatPointer::vtable(
                    Value::Reference {
                        addr: *addr,
                        mutability: target_mutability,
                        lifetime: target_lifetime.clone(),
                        referent: referent.clone(),
                    },
                    target_trait,
                )))
            }
            _ => None,
        }
    }

    fn reference_array_len(&self, addr: Address, target_elem: &RustType) -> Option<usize> {
        match self.ctx.memory.allocation_type(addr)? {
            RustType::Array { element, .. }
                if element.as_ref() == target_elem || element.is_compatible(target_elem) =>
            {
                self.ctx.memory.slice_len(addr)
            }
            _ => None,
        }
    }

    fn reference_concrete_type_name(&self, addr: Address) -> Option<String> {
        match self.ctx.memory.allocation_type(addr)? {
            RustType::Named { name, .. } => Some(name.clone()),
            _ => None,
        }
    }

    fn upcast_trait_object(
        &self,
        data: &Value,
        vtable: &VTable,
        target_trait: &str,
        target_lifetime: &Lifetime,
    ) -> Option<Value> {
        if !self.trait_is_same_or_supertrait(&vtable.trait_name, target_trait) {
            return None;
        }
        let concrete_type = data
            .concrete_type_name()
            .unwrap_or(vtable.concrete_type.as_str());
        let upcast_vtable = self.build_trait_object_vtable(concrete_type, target_trait)?;
        Some(Value::TraitObject {
            data: Box::new(data.clone()),
            vtable: upcast_vtable,
            lifetime: target_lifetime.clone(),
        })
    }

    pub(super) fn build_trait_object_vtable(
        &self,
        concrete_type: &str,
        trait_name: &str,
    ) -> Option<VTable> {
        let trait_def = self.ctx.get_trait_def(trait_name)?;
        let impl_info = self.ctx.get_trait_impl(trait_name, concrete_type)?;
        let mut vtable = VTable::new(trait_name.to_string(), concrete_type.to_string());

        for sig in &trait_def.methods {
            let impl_fn = impl_info.methods.get(&sig.name)?.clone();
            vtable.add_method(sig.name.clone(), impl_fn, sig.clone());
        }

        Some(vtable)
    }

    fn normalize_runtime_type(&self, ty: &RustType) -> RustType {
        self.ctx.normalize_type(ty).erase_anonymous_lifetimes()
    }

    fn trait_is_same_or_supertrait(&self, source_trait: &str, target_trait: &str) -> bool {
        let mut visited = HashSet::new();
        self.trait_reaches_target(source_trait, target_trait, &mut visited)
    }

    fn trait_reaches_target(
        &self,
        current_trait: &str,
        target_trait: &str,
        visited: &mut HashSet<String>,
    ) -> bool {
        if current_trait == target_trait {
            return true;
        }
        if !visited.insert(current_trait.to_string()) {
            return false;
        }
        self.ctx
            .get_trait_def(current_trait)
            .map(|def| {
                def.supertraits
                    .iter()
                    .any(|supertrait| self.trait_reaches_target(supertrait, target_trait, visited))
            })
            .unwrap_or(false)
    }
}

#[cfg(test)]
mod tests;
#[cfg(test)]
mod upcast_tests;

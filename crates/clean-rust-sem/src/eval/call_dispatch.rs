// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Call dispatch for the Rust interpreter.
//!
//! Handles function calls, method calls, trait dispatch, callable values
//! (closures/fn pointers), enum variant constructors, and trait signature
//! validation. Extracted from `eval/mod.rs` to reduce hotspot churn.

use super::closure_capture::{
    propagate_fnmut_captures, validate_capture_modes, CaptureBinding, CaptureMode,
};
use super::type_infer::contains_type_param;
use super::Interpreter;
use crate::expr::{EvalResult, Expr, Pattern, Stmt};
use crate::ownership::Place;
use crate::types::{ClosureKind, Mutability, RustType};
use crate::values::{FatPointer, OpaqueExpr, Value};
use std::collections::HashMap;

#[derive(Debug, Clone)]
struct BoundClosureCapture {
    binding: CaptureBinding,
    local_place: Place,
}

impl Interpreter {
    /// Evaluate a function call
    pub(super) fn eval_call(
        &mut self,
        func: &Expr,
        args: &[Expr],
        type_args: &[RustType],
    ) -> EvalResult {
        // For qualified names (e.g. `String::new`), try call_function directly
        // so intrinsic dispatch runs before Var evaluation would fail with
        // "undefined variable".
        if let Expr::Var { name, .. } = func {
            if name.contains("::") {
                let mut arg_values = Vec::with_capacity(args.len());
                for arg in args {
                    match self.eval(arg) {
                        EvalResult::Value(v) => arg_values.push(v),
                        other => return other,
                    }
                }
                return self.call_function(name, arg_values, type_args);
            }
        }

        // Evaluate function expression
        let func_val = match self.eval(func) {
            EvalResult::Value(v) => v,
            other => return other,
        };

        // Evaluate arguments
        let mut arg_values = Vec::with_capacity(args.len());
        for arg in args {
            match self.eval(arg) {
                EvalResult::Value(v) => arg_values.push(v),
                other => return other,
            }
        }

        if matches!(&func_val, Value::FnPtr { .. } | Value::Closure { .. }) {
            return self.call_callable_value(&func_val, arg_values, type_args);
        }

        // A closure / fn pointer reached through a `dyn Fn` trait object — i.e.
        // a `&dyn Fn(..)`, `Box<dyn FnMut(..)>`, or plain `&closure` — surfaces
        // here as a reference or vtable fat pointer rather than a bare callable.
        // Peel the indirection to recover the underlying closure and dispatch
        // through it, preserving the closure's Fn/FnMut/FnOnce capture semantics.
        if let Some(callable) = self.resolve_callable_trait_object(&func_val) {
            return self.call_callable_value(&callable, arg_values, type_args);
        }

        // Try to find function by name if func was a variable
        if let Expr::Var { name, .. } = func {
            self.call_function(name, arg_values, type_args)
        } else {
            EvalResult::Error("not a callable value".to_string())
        }
    }

    /// Resolve a callee value that is a closure or fn pointer reached through a
    /// `dyn Fn` / `dyn FnMut` / `dyn FnOnce` trait object to the underlying
    /// callable. Peels `&`/`&mut` references and vtable fat pointers (`&dyn Fn`,
    /// `Box<dyn Fn>`) until a `Value::Closure` or `Value::FnPtr` is found.
    ///
    /// Returns `None` for any non-callable trait object (for example a
    /// `&dyn Display`), so calling such a value continues to be rejected.
    fn resolve_callable_trait_object(&self, value: &Value) -> Option<Value> {
        match value {
            Value::Closure { .. } | Value::FnPtr { .. } => Some(value.clone()),
            // A `&dyn Fn` / `Box<dyn Fn>` is a vtable fat pointer; the underlying
            // closure lives behind its data pointer. Non-Fn trait objects are not
            // callable, so they fall through to `None`.
            Value::FatPtr(FatPointer {
                data_pointer,
                metadata: crate::values::FatPtrMetadata::VtablePtr(_),
            }) => self.resolve_callable_trait_object(data_pointer),
            Value::Reference {
                referent: Some(referent),
                ..
            } => self.resolve_callable_trait_object(referent),
            Value::TraitObject { data, .. } => self.resolve_callable_trait_object(data),
            _ => None,
        }
    }

    pub(super) fn eval_method_call(
        &mut self,
        receiver: &Expr,
        method: &str,
        args: &[Expr],
        type_args: &[RustType],
    ) -> EvalResult {
        let recv_val = match self.eval(receiver) {
            EvalResult::Value(v) => v,
            other => return other,
        };

        let receiver_arg = match self.method_receiver_param_type(&recv_val, method) {
            Some(param_ty) => {
                match self.prepare_method_receiver_arg(receiver, &recv_val, &param_ty) {
                    Ok(value) => Some(value),
                    Err(err) => return EvalResult::Error(err.to_string()),
                }
            }
            None => None,
        };
        let pending_receiver_addr = receiver_arg
            .as_ref()
            .and_then(Self::reference_addr)
            .filter(|addr| self.pending_method_receivers.contains_key(addr));

        let result = 'eval: {
            let mut arg_values = Vec::with_capacity(args.len());
            for arg in args {
                match self.eval(arg) {
                    EvalResult::Value(v) => arg_values.push(v),
                    other => break 'eval other,
                }
            }

            if let Some(result) = self.try_intrinsic_mutating_method(&recv_val, method, &arg_values)
            {
                let (result_value, updated_receiver) = match result {
                    Ok(values) => values,
                    Err(err) => break 'eval EvalResult::Error(err.to_string()),
                };
                match receiver {
                    Expr::Var { name, .. } if !self.update_var(name, updated_receiver) => {
                        break 'eval EvalResult::Error(format!(
                            "cannot update builtin method receiver `{name}`"
                        ));
                    }
                    Expr::Field { .. } | Expr::Index { .. } | Expr::Deref(_) => {
                        break 'eval EvalResult::Error(format!(
                            "mutating method `{method}` currently requires a direct variable receiver"
                        ));
                    }
                    _ => {}
                }
                break 'eval EvalResult::Value(result_value);
            }

            if let Some(result) = self.try_intrinsic_method(&recv_val, method, &arg_values) {
                break 'eval result;
            }

            if let Value::TraitObject { data, vtable, .. } = recv_val.clone() {
                let data_type = match data.concrete_type_name() {
                    Some(name) => name,
                    None => {
                        break 'eval EvalResult::Error(
                            "trait object data has no concrete type".to_string(),
                        );
                    }
                };
                if data_type != vtable.concrete_type {
                    break 'eval EvalResult::Error(format!(
                        "trait object concrete type mismatch: vtable expects `{}`, got `{}`",
                        vtable.concrete_type, data_type
                    ));
                }
                let sig = match vtable.get_signature(method) {
                    Some(sig) => sig,
                    None => {
                        break 'eval EvalResult::Error(format!(
                            "trait `{}` missing signature for method `{}`",
                            vtable.trait_name, method
                        ));
                    }
                };
                let self_mutability = match sig.receiver {
                    crate::types::ReceiverMode::Static => {
                        break 'eval EvalResult::Error(format!(
                            "trait associated function `{}` has no receiver and \
cannot be called through trait-object dispatch",
                            method
                        ));
                    }
                    crate::types::ReceiverMode::ByValue => None,
                    crate::types::ReceiverMode::ByRef => Some(Mutability::Shared),
                    crate::types::ReceiverMode::ByMut => Some(Mutability::Mutable),
                };
                if sig.params.len() != arg_values.len() {
                    break 'eval EvalResult::Error(format!(
                        "trait method `{}` expects {} args, got {}",
                        method,
                        sig.params.len(),
                        arg_values.len()
                    ));
                }
                let impl_fn = match vtable.get_impl(method) {
                    Some(name) => name.clone(),
                    None => {
                        break 'eval EvalResult::Error(format!(
                            "trait `{}` has no method `{}`",
                            vtable.trait_name, method
                        ));
                    }
                };

                let concrete_self_ty = self
                    .ctx
                    .get_trait_impl(&vtable.trait_name, &vtable.concrete_type)
                    .map(|info| info.self_ty.clone())
                    .unwrap_or_else(|| data.get_type());

                if let Err(err) =
                    self.validate_impl_signature(&impl_fn, method, sig, &concrete_self_ty)
                {
                    break 'eval EvalResult::Error(err.to_string());
                }

                // For reference receivers (&self / &mut self), borrow the owned
                // trait-object data rather than passing it by value.  The data
                // here is the concrete value (the trait object owns it), so we
                // form a fresh preserved reference of the requested mutability.
                let self_arg = match self_mutability {
                    None => *data,
                    Some(mutability) => match self.preserved_reference(*data, mutability) {
                        Ok(reference) => reference,
                        Err(err) => break 'eval EvalResult::Error(err.to_string()),
                    },
                };
                let mut all_args = vec![self_arg];
                all_args.extend(arg_values);
                break 'eval self.call_function(&impl_fn, all_args, type_args);
            }

            if let Value::FatPtr(FatPointer {
                data_pointer,
                metadata: crate::values::FatPtrMetadata::VtablePtr(vtable_ptr),
            }) = recv_val.clone()
            {
                let trait_name = vtable_ptr.trait_name;
                let concrete_type = match data_pointer.concrete_type_name() {
                    Some(name) => name,
                    None => {
                        break 'eval EvalResult::Error(
                            "fat pointer data has no concrete type".to_string(),
                        );
                    }
                };
                let vtable = match self.build_trait_object_vtable(concrete_type, &trait_name) {
                    Some(vtable) => vtable,
                    None => {
                        break 'eval EvalResult::Error(format!(
                            "missing vtable for dyn `{trait_name}` and concrete type `{concrete_type}`"
                        ));
                    }
                };
                let sig = match vtable.get_signature(method) {
                    Some(sig) => sig,
                    None => {
                        break 'eval EvalResult::Error(format!(
                            "trait `{}` missing signature for method `{}`",
                            vtable.trait_name, method
                        ));
                    }
                };
                let self_mutability = match sig.receiver {
                    crate::types::ReceiverMode::Static => {
                        break 'eval EvalResult::Error(format!(
                            "trait associated function `{}` has no receiver and \
cannot be called through trait-object dispatch",
                            method
                        ));
                    }
                    crate::types::ReceiverMode::ByValue => None,
                    crate::types::ReceiverMode::ByRef => Some(Mutability::Shared),
                    crate::types::ReceiverMode::ByMut => Some(Mutability::Mutable),
                };
                // A reference data pointer (the `&dyn` / `&mut dyn` case) is only
                // meaningful when the method takes a reference receiver.  A
                // by-value receiver through a reference fat pointer would move
                // out of a borrow, which is unsound, so keep rejecting it.
                let data_is_reference = matches!(
                    data_pointer.as_ref(),
                    Value::Reference { .. } | Value::RawPtr { .. }
                );
                if data_is_reference && self_mutability.is_none() {
                    break 'eval EvalResult::Error(format!(
                        "trait method `{}` takes a by-value receiver but the fat pointer \
borrows its data; cannot move out of a `&dyn` reference",
                        method
                    ));
                }
                // A `&mut self` receiver requires the underlying reference to be
                // mutable so the callee can write through it.
                if let (Some(Mutability::Mutable), Value::Reference { mutability, .. }) =
                    (self_mutability, data_pointer.as_ref())
                {
                    if *mutability != Mutability::Mutable {
                        break 'eval EvalResult::Error(format!(
                            "trait method `{}` requires &mut self but the fat pointer \
holds a shared reference",
                            method
                        ));
                    }
                }
                if sig.params.len() != arg_values.len() {
                    break 'eval EvalResult::Error(format!(
                        "trait method `{}` expects {} args, got {}",
                        method,
                        sig.params.len(),
                        arg_values.len()
                    ));
                }
                let impl_fn = match vtable.get_impl(method) {
                    Some(name) => name.clone(),
                    None => {
                        break 'eval EvalResult::Error(format!(
                            "trait `{}` has no method `{}`",
                            vtable.trait_name, method
                        ));
                    }
                };

                let concrete_self_ty = self
                    .ctx
                    .get_trait_impl(&vtable.trait_name, concrete_type)
                    .map(|info| info.self_ty.clone())
                    .unwrap_or_else(|| data_pointer.deref_view().get_type());

                if let Err(err) =
                    self.validate_impl_signature(&impl_fn, method, sig, &concrete_self_ty)
                {
                    break 'eval EvalResult::Error(err.to_string());
                }

                // Build the `self` argument:
                // - by-value receiver: pass the owned data (`Box<dyn>` case).
                // - reference receiver with a reference data pointer (`&dyn` /
                //   `&mut dyn`): forward that reference directly so the callee
                //   aliases the original place (and may mutate through it).
                // - reference receiver with owned data (`Box<dyn>` + `&self`):
                //   form a fresh preserved reference to the data.
                let self_arg = match (self_mutability, data_is_reference) {
                    (None, _) | (Some(_), true) => *data_pointer,
                    (Some(mutability), false) => {
                        match self.preserved_reference(*data_pointer, mutability) {
                            Ok(reference) => reference,
                            Err(err) => break 'eval EvalResult::Error(err.to_string()),
                        }
                    }
                };
                let mut all_args = vec![self_arg];
                all_args.extend(arg_values);
                break 'eval self.call_function(&impl_fn, all_args, type_args);
            }

            let mut all_args = vec![receiver_arg.unwrap_or_else(|| recv_val.clone())];
            all_args.extend(arg_values);

            if self.ctx.get_function(method).is_some() {
                break 'eval self.call_function(method, all_args, type_args);
            }

            let type_name = recv_val
                .concrete_type_name()
                .map(|s| s.to_string())
                .or_else(|| recv_val.get_type().name());

            if let Some(ref type_name) = type_name {
                if let Some((impl_fn, trait_name)) =
                    self.resolve_receiver_trait_method(type_name, method)
                {
                    let impl_fn = impl_fn.clone();
                    let trait_name = trait_name.to_string();

                    if let Some(trait_sig) =
                        self.ctx.get_trait_method_signature(&trait_name, method)
                    {
                        let concrete_self_ty = self
                            .ctx
                            .get_trait_impl(&trait_name, type_name)
                            .map(|info| info.self_ty.clone())
                            .unwrap_or_else(|| recv_val.get_type());
                        if let Err(err) = self.validate_impl_signature(
                            &impl_fn,
                            method,
                            trait_sig,
                            &concrete_self_ty,
                        ) {
                            break 'eval EvalResult::Error(err.to_string());
                        }
                    }

                    break 'eval self.call_function(&impl_fn, all_args, type_args);
                }
            }

            let type_info = type_name.unwrap_or_else(|| "<unknown>".to_string());
            EvalResult::Error(format!(
                "undefined method `{}` on type `{}`",
                method, type_info
            ))
        };

        if let Some(addr) =
            pending_receiver_addr.filter(|addr| self.pending_method_receivers.contains_key(addr))
        {
            self.cancel_pending_method_receiver(addr);
        }

        result
    }

    pub(super) fn call_callable_value(
        &mut self,
        callable: &Value,
        args: Vec<Value>,
        type_args: &[RustType],
    ) -> EvalResult {
        match callable {
            Value::FnPtr { name } => self.call_function(name, args, type_args),
            Value::Closure {
                fn_id,
                captures,
                kind,
                ..
            } => {
                let capture_places = self
                    .closure_capture_places
                    .get(fn_id)
                    .cloned()
                    .unwrap_or_default();
                self.push_scope();
                let bound_captures =
                    match self.bind_closure_captures_for_call(*kind, captures, &capture_places) {
                        Ok(bound_captures) => bound_captures,
                        Err(err) => {
                            self.pop_scope();
                            return EvalResult::Error(err);
                        }
                    };
                let result = self.call_function(fn_id, args, type_args);
                let updated_captures = self.materialize_bound_closure_captures(&bound_captures);
                self.pop_scope_for_eval_result(&result);
                let writeback_error =
                    propagate_fnmut_captures(self, &updated_captures, &capture_places).err();

                match (result, writeback_error) {
                    (EvalResult::Value(_), Some(err)) | (EvalResult::Return(_), Some(err)) => {
                        EvalResult::Error(err)
                    }
                    (other, _) => other,
                }
            }
            _ => EvalResult::Error("not a callable value".to_string()),
        }
    }

    fn bind_closure_captures_for_call(
        &mut self,
        kind: ClosureKind,
        captures: &[(String, Value, Mutability)],
        capture_places: &[(String, Place, Mutability)],
    ) -> Result<Vec<BoundClosureCapture>, String> {
        let mut bound_captures = Vec::new();

        for (name, value, capture_mutability) in captures {
            let origin_place = capture_places
                .iter()
                .find(|(capture_name, _, _)| capture_name == name)
                .map(|(_, place, _)| place.clone());
            let mode = if kind == ClosureKind::FnOnce {
                if value.get_type().is_copy() {
                    CaptureMode::ByCopy
                } else {
                    CaptureMode::ByMove
                }
            } else if *capture_mutability == Mutability::Mutable {
                CaptureMode::ByMutRef
            } else {
                CaptureMode::ByRef
            };
            let current_value = if mode == CaptureMode::ByMutRef {
                origin_place
                    .as_ref()
                    .and_then(|place| self.read_tracked_place_value(place).ok())
                    .unwrap_or_else(|| value.clone())
            } else {
                value.clone()
            };
            let drop_ty = current_value.get_type();
            let local_place = self.bind_with_drop_type_returning_place(
                name.clone(),
                current_value.clone(),
                drop_ty,
            );
            bound_captures.push(BoundClosureCapture {
                binding: CaptureBinding::new(name.clone(), mode, current_value),
                local_place,
            });
        }

        validate_capture_modes(
            kind,
            &bound_captures
                .iter()
                .map(|capture| capture.binding.clone())
                .collect::<Vec<_>>(),
        )?;
        Ok(bound_captures)
    }

    fn materialize_bound_closure_captures(
        &self,
        bound_captures: &[BoundClosureCapture],
    ) -> Vec<CaptureBinding> {
        bound_captures
            .iter()
            .map(|capture| {
                let current_value = self
                    .binding_value_for_place(&capture.local_place)
                    .map(|value| self.materialize_value(value))
                    .unwrap_or_else(|| capture.binding.current_value.clone());
                CaptureBinding::new(
                    capture.binding.name.clone(),
                    capture.binding.mode,
                    current_value,
                )
            })
            .collect()
    }

    /// Call a named function, optionally with explicit type arguments for
    /// generic monomorphization.
    pub(super) fn call_return_type_hint(
        &self,
        func: &Expr,
        type_args: &[RustType],
    ) -> Option<RustType> {
        let Expr::Var { name, .. } = func else {
            return None;
        };
        let func_def = self.ctx.get_function(name)?;

        let ret_ty = if type_args.is_empty() {
            func_def.ret_ty.clone()
        } else {
            let subst = RustType::build_type_param_subst(&func_def.type_params, type_args)?;
            func_def.ret_ty.substitute_type_params(&subst)
        };

        let ret_ty = self.normalized_runtime_type(&ret_ty);
        (!contains_type_param(&ret_ty)).then_some(ret_ty)
    }

    /// Call a named function, optionally with explicit type arguments for
    /// generic monomorphization.
    pub(super) fn call_function(
        &mut self,
        name: &str,
        args: Vec<Value>,
        type_args: &[RustType],
    ) -> EvalResult {
        self.call_function_with_arg_types(name, args, type_args, None)
    }

    pub(super) fn call_function_with_arg_types(
        &mut self,
        name: &str,
        args: Vec<Value>,
        type_args: &[RustType],
        actual_arg_types: Option<&[RustType]>,
    ) -> EvalResult {
        // User-defined functions and impl methods should shadow intrinsic helpers
        // for the same qualified name (e.g. a local `String::new`).
        let func_def = match self.ctx.get_function(name) {
            Some(f) => f.clone(),
            None => {
                if let Some(result) = self.try_call_tuple_enum_variant_constructor(name, &args) {
                    return result;
                }
                if let Some(result) = self.try_intrinsic(name, &args) {
                    return match result {
                        Ok(value) => EvalResult::Value(value),
                        Err(err) => EvalResult::Error(err.to_string()),
                    };
                }
                return EvalResult::Error(format!("undefined function: {name}"));
            }
        };

        // Explicit type args only apply to function-local generic params.
        let mut subst = if type_args.is_empty() {
            HashMap::new()
        } else {
            match RustType::build_type_param_subst(&func_def.type_params, type_args) {
                Some(s) => s
                    .into_iter()
                    .map(|(id, ty)| (id, self.ctx.normalize_type(&ty).erase_anonymous_lifetimes()))
                    .collect(),
                None => {
                    return EvalResult::Error(format!(
                        "function {} expects {} type args, got {}",
                        name,
                        func_def.type_params.len(),
                        type_args.len()
                    ));
                }
            }
        };

        let inferred_subst = match actual_arg_types {
            Some(actual_arg_types) => {
                self.infer_call_type_param_subst_from_types(&func_def.params, actual_arg_types)
            }
            None => self.infer_call_type_param_subst(&func_def.params, &args),
        };
        if let Some(err) = self.merge_type_param_subst(name, &mut subst, inferred_subst) {
            return err;
        }

        if let Some(err) = self.validate_type_param_bounds(name, &func_def.type_params, &subst) {
            return err;
        }
        if let Some(err) = self.validate_type_param_bounds(
            name,
            self.ctx.get_function_context_type_params(name),
            &subst,
        ) {
            return err;
        }

        // Monomorphize parameter types and return type when substitution
        // is active, so arity checks and return coercion use concrete types.
        let params: Vec<(String, RustType)> = if subst.is_empty() {
            func_def.params.clone()
        } else {
            func_def
                .params
                .iter()
                .map(|(n, ty)| (n.clone(), ty.substitute_type_params(&subst)))
                .collect()
        };
        let ret_ty = if subst.is_empty() {
            func_def.ret_ty.clone()
        } else {
            func_def.ret_ty.substitute_type_params(&subst)
        };

        // Check argument count
        if args.len() != params.len() {
            return EvalResult::Error(format!(
                "function {} expects {} args, got {}",
                name,
                params.len(),
                args.len()
            ));
        }

        // Async functions: build a self-contained thunk that captures the
        // argument values as let-bindings, then return it wrapped in Future.
        // The thunk is evaluated lazily when `.await`ed.
        if func_def.is_async {
            let mut stmts: Vec<Stmt> = Vec::with_capacity(params.len());
            for ((param_name, param_ty), arg_val) in params.iter().zip(&args) {
                stmts.push(Stmt::Let {
                    pattern: Pattern::Binding {
                        name: param_name.clone(),
                        mutable: false,
                        subpattern: None,
                    },
                    ty: Some(param_ty.clone()),
                    init: Some(Box::new(Expr::Literal(arg_val.clone()))),
                    else_block: None,
                });
            }
            let thunk = Expr::Block {
                stmts,
                expr: Some(Box::new(func_def.body.clone())),
            };
            return EvalResult::Value(Value::Future {
                body: OpaqueExpr(Box::new(thunk)),
            });
        }

        // Push new scope and stack frame
        self.recursion_depth += 1;
        self.push_scope();
        self.ctx.stack.push_frame();

        if let Err(err) = self.bind_call_params(&params, args) {
            self.ctx.stack.pop_frame();
            self.pop_scope();
            self.recursion_depth -= 1;
            return EvalResult::Error(err.to_string());
        }

        // Execute function body
        let result = self.eval(&func_def.body);

        // Release protectors before popping the frame so that the
        // Stacked Borrows model knows the call-duration protection is over.
        if self.aliasing_checks {
            self.release_current_frame_protectors();
        }

        // Pop scope and frame
        self.ctx.stack.pop_frame();
        self.pop_scope_for_eval_result(&result);
        self.recursion_depth -= 1;

        // Apply any declared return-type coercion before surfacing the value.
        match result {
            EvalResult::Return(v) | EvalResult::Value(v) => {
                EvalResult::Value(self.coerce_runtime_value(&v, &ret_ty).unwrap_or(v))
            }
            other => other,
        }
    }
}

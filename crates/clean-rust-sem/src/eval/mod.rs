// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rust Operational Semantics - Expression Evaluation
//!
//! This module implements a small-step operational semantics for Rust expressions.
//! It provides an interpreter that evaluates expressions in an execution context,
//! handling control flow, memory operations, and ownership tracking.
//!
//! ## Semantics Model
//!
//! The evaluation model follows Rust's operational semantics:
//!
//! - **Eager evaluation**: Arguments evaluated left-to-right before function application
//! - **Value semantics**: Values are copied/moved based on type's Copy trait
//! - **Control flow**: if/else, match, loops with break/continue
//! - **Memory model**: Stack-based locals with heap allocations
//!
//! ## Evaluation Rules (Big-Step)
//!
//! ```text
//! Literal:      ⟨lit⟩ ↓ lit
//! Variable:     ⟨x⟩ ↓ σ(x)          where σ is the environment
//! BinOp:        ⟨e1 ⊕ e2⟩ ↓ v1 ⊕ v2  where ⟨e1⟩ ↓ v1, ⟨e2⟩ ↓ v2
//! If-True:      ⟨if true { e1 } else { e2 }⟩ ↓ v1  where ⟨e1⟩ ↓ v1
//! If-False:     ⟨if false { e1 } else { e2 }⟩ ↓ v2  where ⟨e2⟩ ↓ v2
//! Block:        ⟨{ s1; ...; sn; e }⟩ ↓ v  where each si executes, ⟨e⟩ ↓ v
//! ```

pub(super) mod atomics;
mod call_dispatch;
mod call_dispatch_traits;
mod closure_capture;
mod drop_order;
mod error;
mod inline_asm;
mod interior_mutability;
mod intrinsics;
mod pattern_bindings;
mod runtime_coercion;
mod trait_subst;
mod type_infer;

use crate::error::RustSemError;
use crate::expr::{EnumVariantPayload, EvalResult, Expr, InlineAsm, Item, MatchArm, Pattern, Stmt};
use crate::memory::Address;
use crate::ownership::{AliasingModel, BorrowError, DropElaborator, Place};
use crate::stacked_borrows::{AccessKind, BorrowPermission, BorrowTag, ProtectorId};
use crate::stmt::{ExecContext, FunctionDef, PatternBindings, StmtResult};
use crate::types::{ClosureKind, IntType, Mutability, RustType, UintType};
use crate::values::{cast_value, eval_binop, eval_unop, EnumPayload, OpaqueExpr, Value};
use clean_kernel::sem_memory_model::{Address as SharedAddress, MemoryModel, MemoryValue};
use std::collections::{BTreeMap, HashMap, HashSet};

use self::closure_capture::{
    capture_mode_for_resolved_capture, validate_capture_modes, CaptureBinding,
};
use self::error::EvalError;
use self::interior_mutability::InteriorCellState;

/// Maximum recursion depth for interpreter (prevent stack overflow)
const MAX_RECURSION_DEPTH: usize = 1000;

/// Maximum loop iterations (prevent infinite loops during interpretation)
const MAX_LOOP_ITERATIONS: usize = 100_000;

#[derive(Debug, Clone)]
enum PlaceProjection {
    Field(String),
    Index(usize),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PendingMethodReceiverKind {
    TwoPhaseMut,
}

#[derive(Debug, Clone)]
struct PendingMethodReceiverBorrow {
    place: Place,
    tag: BorrowTag,
    protector: ProtectorId,
    kind: PendingMethodReceiverKind,
}

#[derive(Debug, Clone)]
pub(crate) struct LocalBinding {
    pub(crate) name: String,
    pub(crate) value: Value,
    pub(crate) drop_ty: RustType,
}

/// Interpreter state
#[derive(Debug)]
pub struct Interpreter {
    /// Execution context with memory, stack, functions, types
    pub ctx: ExecContext,
    /// Variable bindings in declaration order for each lexical scope.
    ///
    /// We keep shadowed same-scope bindings instead of overwriting them so
    /// tracked places can still resolve the original referent after a later
    /// `let` shadows the visible name.
    pub(crate) bindings: Vec<Vec<LocalBinding>>,
    /// Drop elaborators per scope - tracks values needing destruction
    pub drop_elaborators: Vec<DropElaborator>,
    /// Current recursion depth
    pub recursion_depth: usize,
    /// Mapping from variable names to the currently visible ownership `Place`.
    ///
    /// Populated lazily when `aliasing_checks` is true so that `lookup`
    /// and `update_var` can validate reads/writes through the stacked
    /// borrows model in `ctx.ownership`.
    name_places: HashMap<String, Place>,
    /// Per-scope ownership places in the same order as `bindings`.
    scope_places: Vec<Vec<(String, Place)>>,
    /// Provenance map from preserved reference values back to their source place.
    ///
    /// This lets call-frame protectors target the caller's referent instead
    /// of the callee-local binding when a function receives `&T`/`&mut T`.
    reference_places: HashMap<Address, Place>,
    /// Borrow tag each reference was created with.
    ///
    /// Populated alongside `reference_places` during `AddrOf` evaluation
    /// so that `Expr::Deref` can validate the read through the tag that
    /// was live when the reference was born, not the current tag on the
    /// referent place (which may have been overwritten by later accesses).
    reference_tags: HashMap<Address, BorrowTag>,
    /// Provenance map for raw pointers created from tracked references.
    ///
    /// The place remains address-keyed because multiple raw pointers to the
    /// same location still refer to the same referent place.
    raw_pointer_places: HashMap<Address, Place>,
    /// Reserved method receivers waiting for call-entry activation.
    pending_method_receivers: HashMap<Address, PendingMethodReceiverBorrow>,
    /// Defining places for each resolved closure capture, keyed by closure id.
    ///
    /// This lets `FnMut` calls refresh mutable captures from their original
    /// binding and write mutations back to that exact binding after the call,
    /// even if the closure is invoked from a different scope.
    closure_capture_places: HashMap<String, Vec<(String, Place, Mutability)>>,
    /// Shared runtime state for interior-mutable containers.
    interior_cells: HashMap<u64, InteriorCellState>,
    /// Counter for allocating deterministic interior container ids.
    next_interior_cell_id: u64,
    /// Counter for assigning deterministic `Place::Local` indices.
    local_counter: u32,
    /// Nested scope pops currently running because a panic is unwinding.
    scope_drop_unwind_depth: usize,
    /// When true, bind/lookup/update_var validate accesses through
    /// the stacked-borrows model.  Off by default so existing callers
    /// that do not set up ownership state are unaffected.
    pub aliasing_checks: bool,
    /// Active runtime aliasing model when checks are enabled.
    pub aliasing_model: AliasingModel,
    /// Places currently being dropped — prevents re-entrant Drop::drop calls.
    dropping_places: HashSet<Place>,
    /// Anonymous allocations created through the shared `MemoryModel` trait.
    shared_memory_roots: HashSet<Place>,
    /// Reverse map from shared memory addresses to interpreter places.
    shared_memory_addr_places: HashMap<SharedAddress, Place>,
}

impl Interpreter {
    /// Create a new interpreter
    #[must_use]
    pub fn new() -> Self {
        let mut interp = Self {
            ctx: ExecContext::new(),
            bindings: vec![Vec::new()],
            drop_elaborators: vec![DropElaborator::new()],
            recursion_depth: 0,
            name_places: HashMap::new(),
            scope_places: vec![Vec::new()],
            reference_places: HashMap::new(),
            reference_tags: HashMap::new(),
            raw_pointer_places: HashMap::new(),
            pending_method_receivers: HashMap::new(),
            closure_capture_places: HashMap::new(),
            interior_cells: HashMap::new(),
            next_interior_cell_id: 0,
            local_counter: 0,
            scope_drop_unwind_depth: 0,
            aliasing_checks: false,
            aliasing_model: AliasingModel::StackedBorrows,
            dropping_places: HashSet::new(),
            shared_memory_roots: HashSet::new(),
            shared_memory_addr_places: HashMap::new(),
        };
        // Push initial stack frame
        interp.ctx.stack.push_frame();
        interp
    }

    /// Enable or disable stacked-borrows aliasing checks on this interpreter.
    ///
    /// This is off by default so existing callers keep the historical runtime
    /// behavior unless they opt into the stricter aliasing model.
    #[must_use]
    pub fn with_aliasing_checks(mut self, enabled: bool) -> Self {
        self.aliasing_checks = enabled;
        self.ctx.ownership.set_aliasing_model(self.aliasing_model);
        self
    }

    /// Select the runtime aliasing model and enable aliasing checks.
    #[must_use]
    pub fn with_aliasing_model(mut self, model: AliasingModel) -> Self {
        self.aliasing_model = model;
        self.aliasing_checks = true;
        self.ctx.ownership.set_aliasing_model(model);
        self
    }

    /// Create interpreter with existing context
    #[must_use]
    pub fn with_context(ctx: ExecContext) -> Self {
        let mut interp = Self {
            ctx,
            bindings: vec![Vec::new()],
            drop_elaborators: vec![DropElaborator::new()],
            recursion_depth: 0,
            name_places: HashMap::new(),
            scope_places: vec![Vec::new()],
            reference_places: HashMap::new(),
            reference_tags: HashMap::new(),
            raw_pointer_places: HashMap::new(),
            pending_method_receivers: HashMap::new(),
            closure_capture_places: HashMap::new(),
            interior_cells: HashMap::new(),
            next_interior_cell_id: 0,
            local_counter: 0,
            scope_drop_unwind_depth: 0,
            aliasing_checks: false,
            aliasing_model: AliasingModel::StackedBorrows,
            dropping_places: HashSet::new(),
            shared_memory_roots: HashSet::new(),
            shared_memory_addr_places: HashMap::new(),
        };
        // Ensure we have at least one stack frame
        if interp.ctx.stack.depth() == 0 {
            interp.ctx.stack.push_frame();
        }
        interp
    }

    /// Push a new binding scope
    fn push_scope(&mut self) {
        self.bindings.push(Vec::new());
        self.drop_elaborators.push(DropElaborator::new());
        self.scope_places.push(Vec::new());
    }

    /// Pop a binding scope, running destructors for values going out of scope
    fn pop_scope(&mut self) {
        // Drain drops from the current scope (in reverse order)
        if let Some(mut elaborator) = self.drop_elaborators.pop() {
            for (place, ty) in elaborator.drain_drops() {
                self.call_drop(&place, &ty);
            }
        }
        self.bindings.pop();
        if let Some(scope_places) = self.scope_places.pop() {
            for (_, place) in &scope_places {
                self.shared_memory_roots.remove(place);
            }
            let mut restored_names = HashSet::new();
            for (name, _) in scope_places.into_iter().rev() {
                if !restored_names.insert(name.clone()) {
                    continue;
                }
                if let Some(place) = self.scope_places.iter().rev().find_map(|scope| {
                    scope
                        .iter()
                        .rev()
                        .find_map(|(candidate_name, candidate_place)| {
                            (candidate_name == &name).then(|| candidate_place.clone())
                        })
                }) {
                    self.name_places.insert(name, place);
                } else {
                    self.name_places.remove(&name);
                }
            }
        }
    }

    fn pop_scope_with_unwind(&mut self, unwinding: bool) {
        if unwinding {
            self.scope_drop_unwind_depth += 1;
        }
        self.pop_scope();
        if unwinding {
            self.scope_drop_unwind_depth -= 1;
        }
    }

    fn pop_scope_for_eval_result(&mut self, result: &EvalResult) {
        self.pop_scope_with_unwind(matches!(result, EvalResult::Panic(_)));
    }

    fn is_unwinding_scope_drop(&self) -> bool {
        self.scope_drop_unwind_depth > 0
    }

    /// Schedule a value for dropping when its scope ends.
    fn schedule_drop(&mut self, place: Place, ty: &RustType) {
        if let Some(elaborator) = self.drop_elaborators.last_mut() {
            elaborator.schedule_drop(place, ty.clone());
        }
    }

    fn drop_receiver_for_place(&mut self, place: &Place) -> Option<Value> {
        let referent = self.read_tracked_place_value(place).ok()?;
        let receiver = self
            .preserved_reference(referent, Mutability::Mutable)
            .ok()?;
        self.remember_reference_place(&receiver, place.clone());
        Some(receiver)
    }

    /// Call the drop implementation for a value if it has one.
    ///
    /// Follows Rust drop order: custom `Drop::drop` first (if impl exists),
    /// then recursive field drops in declaration order (first to last).
    /// Reference: https://doc.rust-lang.org/reference/destructors.html
    fn call_drop(&mut self, place: &Place, ty: &RustType) {
        self.release_interior_borrow_for_place(place);

        // Guard against re-entrant drops: when Drop::drop runs, its `self`
        // parameter is bound and scheduled for dropping. Without this guard,
        // popping the drop-function scope would re-trigger call_drop on the
        // same place, causing infinite recursion.
        if !self.dropping_places.insert(place.clone()) {
            return;
        }

        // Step 1: Call custom Drop impl if one is registered (#3047).
        if let RustType::Named { name, .. } = ty {
            if let Some(drop_fn_name) = self.ctx.get_drop_impl(name).cloned() {
                let receiver_param_ty = self
                    .ctx
                    .get_function(&drop_fn_name)
                    .and_then(|drop_fn| drop_fn.params.first())
                    .map(|(_, param_ty)| param_ty.clone());
                if let Some(RustType::Reference {
                    mutability: Mutability::Mutable,
                    inner,
                    ..
                }) = receiver_param_ty
                {
                    let actual_inner_ty = self.normalized_runtime_type(ty);
                    let expected_inner_ty = self.normalized_runtime_type(inner.as_ref());
                    let mut subst = HashMap::new();
                    if self.infer_type_param_subst(&expected_inner_ty, &actual_inner_ty, &mut subst)
                    {
                        if let Some(receiver) = self.drop_receiver_for_place(place) {
                            let runtime_receiver_ty = RustType::Reference {
                                lifetime: crate::types::Lifetime::Static,
                                mutability: Mutability::Mutable,
                                inner: Box::new(actual_inner_ty),
                            };
                            let runtime_arg_types = [runtime_receiver_ty];
                            let _ = self.call_function_with_arg_types(
                                &drop_fn_name,
                                vec![receiver],
                                &[],
                                Some(&runtime_arg_types),
                            );
                        }
                    }
                }
            }
        }

        // Step 2: Recursively drop children in Rust-specified order.
        for (child_place, child_ty) in self.drop_children_in_rust_order(place, ty) {
            self.call_drop(&child_place, &child_ty);
        }

        self.dropping_places.remove(place);
    }

    fn fresh_place(&mut self) -> Place {
        let idx = self.local_counter;
        self.local_counter += 1;
        Place::Local(idx)
    }

    /// Return (or create) the active `Place` for a variable name.
    fn place_for_name(&mut self, name: &str) -> Place {
        if let Some(place) = self.name_places.get(name) {
            return place.clone();
        }
        let place = self.fresh_place();
        self.name_places.insert(name.to_string(), place.clone());
        place
    }

    /// Allocate a fresh `Place` for a new binding in the current scope.
    fn bind_place_for_name(&mut self, name: &str) -> Place {
        let place = self.fresh_place();
        if let Some(scope) = self.scope_places.last_mut() {
            scope.push((name.to_string(), place.clone()));
        }
        self.name_places.insert(name.to_string(), place.clone());
        place
    }

    /// Try to resolve an expression to an ownership `Place`.
    ///
    /// Returns `Some(place)` for variable references, field projections,
    /// and dereferences whose tracked referent can be recovered. Returns
    /// `None` for expressions that don't correspond to a tracked place
    /// (e.g. literals, function calls, binary ops, untracked raw derefs).
    fn expr_to_place(&mut self, expr: &Expr) -> Option<Place> {
        match expr {
            Expr::Var { name, .. } => Some(self.place_for_name(name)),
            Expr::Field { base, field } => {
                let base_place = self.expr_to_place(base)?;
                Some(base_place.field(field))
            }
            Expr::Deref(inner) | Expr::RawDeref(inner) => {
                // Recover the pointer value from an already-tracked place
                // instead of re-evaluating the operand. Re-running `inner`
                // here would duplicate side effects for `&*call()` and similar
                // place expressions while merely trying to recover provenance.
                let inner_place = self.expr_to_place(inner)?;
                let pointer = self.read_tracked_place_value(&inner_place).ok()?;
                self.tracked_pointer_place(&pointer)
            }
            // Reference-to-raw-pointer casts preserve the synthetic address
            // used by tracked provenance, so reborrows through the cast
            // should resolve to the same pointer place.
            Expr::Cast {
                expr: inner,
                target: RustType::RawPtr { .. },
            } => self.expr_to_place(inner),
            Expr::Cast { .. } => None,
            Expr::Index { base, .. } => {
                // Index expressions have a dynamic index; we track the
                // base place but cannot represent the exact element.
                // Return the base for conservative validation.
                self.expr_to_place(base)
            }
            _ => None,
        }
    }

    fn remember_reference_place(&mut self, reference: &Value, place: Place) {
        if let Value::FatPtr(crate::values::FatPointer { data_pointer, .. }) = reference {
            self.remember_reference_place(data_pointer, place);
            return;
        }
        if let Value::Reference { addr, .. } = reference {
            // Store the borrow tag that was current when this reference was
            // created so that deref can validate against the birth tag.
            if let Some(tag) = self.ctx.ownership.borrow_tag(&place) {
                self.reference_tags.insert(*addr, tag);
            }
            self.reference_places.insert(*addr, place);
        }
    }

    fn method_receiver_place(
        &mut self,
        receiver_expr: &Expr,
        receiver_value: &Value,
    ) -> Option<Place> {
        self.tracked_pointer_place(receiver_value)
            .or_else(|| self.expr_to_place(receiver_expr))
    }

    fn reference_addr(value: &Value) -> Option<Address> {
        match value {
            Value::Reference { addr, .. } => Some(*addr),
            Value::FatPtr(crate::values::FatPointer { data_pointer, .. }) => {
                Self::reference_addr(data_pointer)
            }
            _ => None,
        }
    }

    fn referenced_place(&self, value: &Value) -> Option<Place> {
        match value {
            Value::Reference { addr, .. } => self.reference_places.get(addr).cloned(),
            Value::FatPtr(crate::values::FatPointer { data_pointer, .. }) => {
                self.referenced_place(data_pointer)
            }
            _ => None,
        }
    }

    fn cancel_pending_method_receiver(&mut self, addr: Address) {
        if let Some(pending) = self.pending_method_receivers.remove(&addr) {
            self.ctx.ownership.release_protector(pending.protector);
        }
        self.reference_places.remove(&addr);
        self.reference_tags.remove(&addr);
    }

    fn method_receiver_param_type(&self, receiver: &Value, method: &str) -> Option<RustType> {
        if let Some(def) = self.ctx.get_function(method) {
            return def.params.first().map(|(_, ty)| ty.clone());
        }

        let type_name = receiver
            .concrete_type_name()
            .map(str::to_string)
            .or_else(|| receiver.get_type().name())?;
        // Trait method lookup walks the shared HashMap-backed impl registry.
        // Keep this borrowed lookup on the hot path; materializing a fresh map
        // here would add avoidable allocation churn.
        let (impl_fn, _) = self.resolve_receiver_trait_method(&type_name, method)?;
        self.ctx
            .get_function(impl_fn)
            .and_then(|def| def.params.first())
            .map(|(_, ty)| ty.clone())
    }

    fn prepare_method_receiver_arg(
        &mut self,
        receiver_expr: &Expr,
        receiver_value: &Value,
        param_ty: &RustType,
    ) -> Result<Value, RustSemError> {
        let RustType::Reference { mutability, .. } = param_ty else {
            return Ok(receiver_value.clone());
        };

        // Auto-deref: when the receiver is already a reference (e.g. `r: &mut T`),
        // extract the referent before wrapping.  Models Rust's implicit reborrow:
        // `r.method()` where `r: &mut T` desugars to `(&mut *r).method()`.
        let referent = match receiver_value {
            Value::Reference {
                referent: Some(inner),
                ..
            } => inner.as_ref().clone(),
            _ => receiver_value.clone(),
        };

        let reference = self.preserved_reference(referent, *mutability)?;
        if let Some(place) = self.method_receiver_place(receiver_expr, receiver_value) {
            self.remember_reference_place(&reference, place.clone());
            if self.aliasing_checks && *mutability == Mutability::Mutable {
                let protector = self.ctx.ownership.new_protector();
                let reservation_tag = self
                    .ctx
                    .ownership
                    .reserve_mut_place(&place, Some(protector))
                    .map_err(|source| RustSemError::TwoPhaseReceiverReservation {
                        receiver_expr: format!("{receiver_expr:?}"),
                        source,
                    })?;
                let addr = Self::reference_addr(&reference)
                    .expect("preserved_reference always returns a reference value");
                self.reference_tags.insert(addr, reservation_tag);
                self.pending_method_receivers.insert(
                    addr,
                    PendingMethodReceiverBorrow {
                        place,
                        tag: reservation_tag,
                        protector,
                        kind: PendingMethodReceiverKind::TwoPhaseMut,
                    },
                );
            }
        }

        Ok(reference)
    }

    fn remember_raw_pointer_place(
        &mut self,
        raw_pointer: Value,
        place: Place,
        tag: BorrowTag,
    ) -> Value {
        if let Value::RawPtr {
            addr, mutability, ..
        } = raw_pointer
        {
            self.raw_pointer_places.insert(addr, place);
            return Value::RawPtr {
                addr,
                mutability,
                tag: Some(tag),
            };
        }
        raw_pointer
    }

    fn release_current_frame_protectors(&mut self) {
        let protectors: Vec<_> = self
            .ctx
            .stack
            .current_frame()
            .expect("invariant: frame was pushed at call start")
            .protectors
            .clone();
        for protector in protectors {
            self.ctx.ownership.release_protector(protector);
        }
    }

    fn bind_call_params(
        &mut self,
        params: &[(String, RustType)],
        args: Vec<Value>,
    ) -> Result<(), RustSemError> {
        for ((param_name, param_ty), arg_val) in params.iter().zip(args) {
            // Attempt implicit coercion when arg type doesn't match param type.
            let arg_val = self
                .coerce_runtime_value(&arg_val, param_ty)
                .unwrap_or(arg_val);
            let pending_addr = match param_ty {
                RustType::Reference { .. } => Self::reference_addr(&arg_val),
                _ => None,
            };
            if let Some(addr) = pending_addr {
                if let Some(pending) = self.pending_method_receivers.remove(&addr) {
                    self.bind_with_drop_type(param_name.clone(), arg_val, param_ty.clone());
                    match pending.kind {
                        PendingMethodReceiverKind::TwoPhaseMut => {
                            let activated_tag = match self.ctx.ownership.activate_mut_place(
                                &pending.place,
                                pending.tag,
                                Some(pending.protector),
                            ) {
                                Ok(tag) => tag,
                                Err(source) => {
                                    self.ctx.ownership.release_protector(pending.protector);
                                    return Err(RustSemError::TwoPhaseReceiverActivation {
                                        param_name: param_name.clone(),
                                        source,
                                    });
                                }
                            };
                            self.reference_tags.insert(addr, activated_tag);
                        }
                    }
                    self.ctx
                        .stack
                        .current_frame_mut()
                        .expect("invariant: frame was just pushed")
                        .protectors
                        .push(pending.protector);
                    continue;
                }
            }

            let (protected_place, ref_mutability, ref_addr) = match param_ty {
                RustType::Reference { mutability, .. } if self.aliasing_checks => {
                    let place = self
                        .referenced_place(&arg_val)
                        .unwrap_or_else(|| self.place_for_name(param_name));
                    let addr = match &arg_val {
                        Value::Reference { addr, .. } => Some(*addr),
                        _ => None,
                    };
                    (place, *mutability, addr)
                }
                _ => {
                    self.bind_with_drop_type(param_name.clone(), arg_val, param_ty.clone());
                    continue;
                }
            };

            self.bind_with_drop_type(param_name.clone(), arg_val, param_ty.clone());

            let RustType::Reference { lifetime, .. } = param_ty else {
                unreachable!("guard above matched only reference params");
            };
            let protector = self.ctx.ownership.new_protector();
            match self.ctx.ownership.add_borrow_with_protector(
                protected_place,
                ref_mutability,
                lifetime.clone(),
                Some(protector),
            ) {
                Ok(new_tag) => {
                    // Update the reference's birth tag to the protector's tag
                    // so the function body reads through the protected entry
                    // rather than the caller's (now-shadowed) tag.
                    if let Some(addr) = ref_addr {
                        self.reference_tags.insert(addr, new_tag);
                    }
                    self.ctx
                        .stack
                        .current_frame_mut()
                        .expect("invariant: frame was just pushed")
                        .protectors
                        .push(protector);
                }
                Err(source) => {
                    self.release_current_frame_protectors();
                    return Err(RustSemError::ProtectedBorrowSetup {
                        param_name: param_name.clone(),
                        source,
                    });
                }
            }
        }
        Ok(())
    }

    /// Validate a stacked-borrows read access for `name`, mutating the
    /// ownership state to disable Unique entries above the reader.
    ///
    /// Returns `Ok(())` if aliasing checks are disabled or if the access
    /// is permitted; returns `Err` with a human-readable message otherwise.
    fn validate_read(&mut self, name: &str) -> Result<(), RustSemError> {
        if !self.aliasing_checks {
            return Ok(());
        }
        let Some(place) = self.name_places.get(name).cloned() else {
            return Ok(());
        };
        let Some(tag) = self.ctx.ownership.borrow_tag(&place) else {
            return Ok(());
        };
        self.ctx
            .ownership
            .access_place(&place, tag, AccessKind::Read)
            .map_err(|source| RustSemError::StackedBorrowsReadRejected {
                name: name.to_string(),
                source,
            })
    }

    /// Validate a write that semantically overwrites the entire tracked place.
    fn validate_whole_place_write(&mut self, place: &Place) -> Result<(), BorrowError> {
        if !self.aliasing_checks {
            return Ok(());
        }
        let tag = self.ctx.ownership.current_or_root_tag(place);
        self.ctx
            .ownership
            .access_whole_place(place, tag, AccessKind::Write)
    }

    /// Look up a variable in the current scope chain.
    ///
    /// When aliasing checks are enabled, a read access is validated against
    /// the stacked-borrows model (transitioning Unique entries above the
    /// reader to Disabled).  The returned value is cloned so the mutable
    /// borrow on `self` is released before the caller continues.
    fn lookup(&mut self, name: &str) -> Option<Value> {
        self.lookup_typed(name).ok()
    }

    fn lookup_typed(&mut self, name: &str) -> Result<Value, EvalError> {
        let found = self
            .bindings
            .iter()
            .rev()
            .any(|scope| scope.iter().rev().any(|binding| binding.name == name));
        if !found {
            return Err(EvalError::UnboundVariable {
                name: name.to_string(),
            });
        }
        self.validate_read(name).map_err(EvalError::from)?;
        for scope in self.bindings.iter().rev() {
            if let Some(binding) = scope.iter().rev().find(|binding| binding.name == name) {
                return Ok(self.materialize_value(&binding.value));
            }
        }
        Err(EvalError::UnboundVariable {
            name: name.to_string(),
        })
    }

    #[must_use]
    fn value_type_name(value: &Value) -> String {
        match value.deref_view() {
            Value::Struct { name, .. } => format!("struct {name}"),
            Value::Enum { name, .. } => format!("enum {name}"),
            Value::Union { name, .. } => format!("union {name}"),
            Value::Tuple(_) => "tuple".to_string(),
            Value::Array(_) => "array".to_string(),
            other => format!("{:?}", other.get_type()),
        }
    }

    fn index_from_value(&self, index_value: &Value, context: &str) -> Result<usize, EvalError> {
        match index_value {
            Value::Uint { value, .. } => {
                usize::try_from(*value).map_err(|_| EvalError::OverflowError {
                    op: context.to_string(),
                })
            }
            Value::Int { value, .. } if *value >= 0 => {
                usize::try_from(*value).map_err(|_| EvalError::OverflowError {
                    op: context.to_string(),
                })
            }
            _ => Err(EvalError::TypeError {
                expected: "non-negative integer".to_string(),
                actual: Self::value_type_name(index_value),
                context: context.to_string(),
            }),
        }
    }

    fn field_access_value(base_value: &Value, field: &str) -> Result<Value, EvalError> {
        let base_value = base_value.deref_view();
        match base_value {
            Value::Struct { name, fields } => {
                fields
                    .get(field)
                    .cloned()
                    .ok_or_else(|| EvalError::FieldNotFound {
                        struct_name: name.clone(),
                        field: field.to_string(),
                    })
            }
            Value::Tuple(elems) => {
                let index =
                    field
                        .parse::<usize>()
                        .map_err(|_| EvalError::UnsupportedOperation {
                            op: "tuple field access".to_string(),
                            context: format!("invalid tuple field `{field}`"),
                        })?;
                elems
                    .get(index)
                    .cloned()
                    .ok_or(EvalError::IndexOutOfBounds {
                        index,
                        len: elems.len(),
                    })
            }
            _ => Err(EvalError::TypeError {
                expected: "struct or tuple".to_string(),
                actual: Self::value_type_name(base_value),
                context: format!("field access `{field}`"),
            }),
        }
    }

    fn index_access_value(base_value: &Value, index: usize) -> Result<Value, EvalError> {
        let base_value = base_value.deref_view();
        match base_value {
            Value::Array(elems) | Value::Tuple(elems) => {
                elems
                    .get(index)
                    .cloned()
                    .ok_or(EvalError::IndexOutOfBounds {
                        index,
                        len: elems.len(),
                    })
            }
            _ => Err(EvalError::TypeError {
                expected: "array or tuple".to_string(),
                actual: Self::value_type_name(base_value),
                context: "index access".to_string(),
            }),
        }
    }

    fn deref_value(&mut self, pointer: Value) -> Result<Value, EvalError> {
        if matches!(pointer, Value::RawPtr { .. }) {
            self.ctx
                .require_unsafe("dereference of raw pointer")
                .map_err(|_| EvalError::UnsupportedOperation {
                    op: "dereference of raw pointer".to_string(),
                    context: "requires unsafe block or function".to_string(),
                })?;
        }

        if self.aliasing_checks {
            if let Some(place) = self.tracked_pointer_place(&pointer) {
                if let Some(tag) = self.tracked_pointer_tag(&pointer) {
                    self.ctx
                        .ownership
                        .access_place(&place, tag, AccessKind::Read)
                        .map_err(EvalError::from)?;
                }
            }
        }

        if let Some(place) = self.tracked_pointer_place(&pointer) {
            return self
                .read_tracked_place_value(&place)
                .map_err(EvalError::from);
        }

        let actual = Self::value_type_name(&pointer);
        match pointer {
            Value::FatPtr(crate::values::FatPointer { data_pointer, .. }) => match *data_pointer {
                Value::Reference {
                    referent: Some(referent),
                    ..
                } => Ok(*referent),
                Value::Reference { addr, .. } | Value::RawPtr { addr, .. } => self
                    .ctx
                    .memory
                    .read_u64(addr)
                    .map(Value::u64)
                    .map_err(|err| EvalError::DerefFailed {
                        detail: err.to_string(),
                    }),
                other => Ok(other),
            },
            Value::RefCellRef { cell_id, .. } | Value::RefCellRefMut { cell_id, .. } => self
                .read_interior_cell_value(cell_id)
                .map_err(EvalError::from),
            Value::MutexGuard { lock_id, .. }
            | Value::RwLockReadGuard { lock_id, .. }
            | Value::RwLockWriteGuard { lock_id, .. } => self
                .read_interior_cell_value(lock_id)
                .map_err(EvalError::from),
            Value::Reference {
                referent: Some(referent),
                ..
            } => Ok(*referent),
            Value::Reference { addr, .. } | Value::RawPtr { addr, .. } => self
                .ctx
                .memory
                .read_u64(addr)
                .map(Value::u64)
                .map_err(|err| EvalError::DerefFailed {
                    detail: err.to_string(),
                }),
            _ => Err(EvalError::TypeError {
                expected: "pointer".to_string(),
                actual,
                context: "dereference".to_string(),
            }),
        }
    }

    fn addr_of_value(
        &mut self,
        inner: &Expr,
        referent: Value,
        mutability: Mutability,
    ) -> Result<Value, EvalError> {
        let referenced_place = if self.aliasing_checks {
            self.expr_to_place(inner)
        } else {
            None
        };

        if self.aliasing_checks {
            if let Some(place) = referenced_place.as_ref() {
                let permission = match mutability {
                    Mutability::Shared => BorrowPermission::SharedReadOnly,
                    Mutability::Mutable => BorrowPermission::Unique,
                };
                self.ctx
                    .ownership
                    .retag_place(place, permission, None)
                    .map_err(EvalError::from)?;
            }
        }

        let reference = self
            .preserved_reference(referent, mutability)
            .map_err(EvalError::from)?;
        if let Some(place) = referenced_place {
            self.remember_reference_place(&reference, place);
        }
        Ok(reference)
    }

    fn binop_value(
        op: crate::values::BinOp,
        left: &Value,
        right: &Value,
    ) -> Result<Value, EvalError> {
        if matches!(op, crate::values::BinOp::Div | crate::values::BinOp::Rem)
            && matches!(left, Value::Uint { .. } | Value::Int { .. })
            && matches!(right, Value::Uint { .. } | Value::Int { .. })
            && right.is_zero()
        {
            return Err(EvalError::DivisionByZero);
        }

        eval_binop(op, left, right).ok_or_else(|| EvalError::UnsupportedOperation {
            op: format!("{op:?}"),
            context: format!(
                "operands {} and {}",
                Self::value_type_name(left),
                Self::value_type_name(right)
            ),
        })
    }

    fn unop_value(op: crate::values::UnOp, value: &Value) -> Result<Value, EvalError> {
        eval_unop(op, value).ok_or_else(|| EvalError::UnsupportedOperation {
            op: format!("{op:?}"),
            context: format!("operand {}", Self::value_type_name(value)),
        })
    }

    fn set_value_at_path(
        container: &mut Value,
        path: &[PlaceProjection],
        value: Value,
    ) -> Result<(), EvalError> {
        if path.is_empty() {
            *container = value;
            return Ok(());
        }

        match &path[0] {
            PlaceProjection::Field(field) => match container {
                Value::Struct { name, fields } => {
                    let entry = fields
                        .get_mut(field)
                        .ok_or_else(|| EvalError::FieldNotFound {
                            struct_name: name.clone(),
                            field: field.clone(),
                        })?;
                    Self::set_value_at_path(entry, &path[1..], value)
                }
                _ => Err(EvalError::TypeError {
                    expected: "struct".to_string(),
                    actual: Self::value_type_name(container),
                    context: format!("field assignment `{field}`"),
                }),
            },
            PlaceProjection::Index(index) => match container {
                Value::Array(elems) | Value::Tuple(elems) => {
                    let len = elems.len();
                    let entry = elems
                        .get_mut(*index)
                        .ok_or(EvalError::IndexOutOfBounds { index: *index, len })?;
                    Self::set_value_at_path(entry, &path[1..], value)
                }
                _ => Err(EvalError::TypeError {
                    expected: "array or tuple".to_string(),
                    actual: Self::value_type_name(container),
                    context: "index assignment".to_string(),
                }),
            },
        }
    }

    fn binding_drop_type(&self, name: &str) -> Option<RustType> {
        self.bindings.iter().rev().find_map(|scope| {
            scope
                .iter()
                .rev()
                .find(|binding| binding.name == name)
                .map(|binding| binding.drop_ty.clone())
        })
    }

    fn binding_drop_type_hint(&self, expr: &Expr) -> Option<RustType> {
        match expr {
            Expr::Var { name, .. } => self.binding_drop_type(name),
            Expr::Struct {
                name,
                type_args,
                const_args,
                ..
            } => Some(RustType::Named {
                name: name.clone(),
                type_args: type_args.clone(),
                lifetime_args: vec![],
                const_args: const_args.clone(),
            }),
            Expr::EnumVariant {
                enum_name,
                type_args,
                const_args,
                ..
            } => Some(RustType::Named {
                name: enum_name.clone(),
                type_args: type_args.clone(),
                lifetime_args: vec![],
                const_args: const_args.clone(),
            }),
            Expr::Cast { target, .. } => Some(target.clone()),
            Expr::Call {
                func, type_args, ..
            } => self.call_return_type_hint(func, type_args),
            _ => None,
        }
    }

    fn drop_type_hint_for_value(&self, expr: &Expr, value: &Value) -> Option<RustType> {
        match expr {
            Expr::Tuple(elems) => {
                if let Value::Tuple(values) = value {
                    self.tuple_drop_type_hint(elems, values)
                } else {
                    None
                }
            }
            Expr::Array(elems) => self.array_literal_drop_type_hint(elems),
            Expr::ArrayRepeat { value: elem, .. } => {
                self.binding_drop_type_hint(elem)
                    .map(|elem_ty| RustType::Array {
                        element: Box::new(elem_ty),
                        len: crate::types::ConstGenericArg::usize(
                            if let Value::Array(arr) = value {
                                arr.len()
                            } else {
                                0
                            },
                        ),
                    })
            }
            _ => self.binding_drop_type_hint(expr),
        }
    }

    fn array_literal_drop_type_hint(&self, elems: &[Expr]) -> Option<RustType> {
        let first_hint = elems.iter().find_map(|e| self.binding_drop_type_hint(e));
        first_hint.map(|elem_ty| RustType::Array {
            element: Box::new(elem_ty),
            len: crate::types::ConstGenericArg::usize(elems.len()),
        })
    }

    /// Compute a tuple type hint by combining per-element expression hints
    /// with value-derived fallbacks. This preserves generic type arguments
    /// from constructor/call expressions while using accurate value types for
    /// elements without expression-level hints.
    fn tuple_drop_type_hint(&self, elems: &[Expr], values: &[Value]) -> Option<RustType> {
        if elems.len() != values.len() {
            return None;
        }
        let elem_hints: Vec<Option<RustType>> = elems
            .iter()
            .zip(values.iter())
            .map(|(expr, value)| self.drop_type_hint_for_value(expr, value))
            .collect();
        let has_any_hint = elem_hints.iter().any(Option::is_some);
        if !has_any_hint {
            return None;
        }
        let elem_types: Vec<RustType> = elems
            .iter()
            .zip(values.iter())
            .zip(elem_hints)
            .map(|((_expr, val), hint)| hint.unwrap_or_else(|| val.get_type()))
            .collect();
        Some(RustType::Tuple(elem_types))
    }

    /// Bind a variable in the current scope with an explicit drop type.
    fn bind_with_drop_type_returning_place(
        &mut self,
        name: String,
        value: Value,
        drop_ty: RustType,
    ) -> Place {
        let place = self.bind_place_for_name(&name);
        if let Some(scope) = self.bindings.last_mut() {
            scope.push(LocalBinding {
                name: name.clone(),
                value,
                drop_ty: drop_ty.clone(),
            });
        }
        // Register with stacked borrows when aliasing checks are enabled.
        if self.aliasing_checks {
            self.ctx.ownership.mark_owned(place.clone());
        }
        // Schedule drop for non-Copy types
        if !drop_ty.is_copy() {
            self.schedule_drop(place.clone(), &drop_ty);
        }
        place
    }

    /// Bind a variable in the current scope with an explicit drop type.
    fn bind_with_drop_type(&mut self, name: String, value: Value, drop_ty: RustType) {
        let _ = self.bind_with_drop_type_returning_place(name, value, drop_ty);
    }

    /// Bind a variable in the current scope
    fn bind(&mut self, name: String, value: Value) {
        let drop_ty = value.get_type();
        self.bind_with_drop_type(name, value, drop_ty);
    }

    /// Update an existing variable in the scope chain (for assignment).
    ///
    /// Searches from innermost scope outward. Returns `true` if the variable
    /// was found and updated, `false` if not found.
    fn update_var(&mut self, name: &str, value: Value) -> bool {
        let found = self
            .bindings
            .iter()
            .rev()
            .any(|scope| scope.iter().rev().any(|binding| binding.name == name));
        if !found {
            return false;
        }
        // Direct variable replacement semantically overwrites the entire
        // tracked place, so descendant field borrows must be invalidated too.
        let place = self.place_for_name(name);
        if let Err(_err) = self.validate_whole_place_write(&place) {
            return false;
        }
        self.replace_var(name, value)
    }

    /// Replace an existing variable binding without performing alias checks.
    fn replace_var(&mut self, name: &str, value: Value) -> bool {
        for scope in self.bindings.iter_mut().rev() {
            if let Some(binding) = scope.iter_mut().rev().find(|binding| binding.name == name) {
                binding.value = value;
                return true;
            }
        }
        false
    }

    // Reference-to-raw-pointer casts preserve the synthetic address allocated
    // for the original reference, while raw-pointer retags keep their own
    // birth tags in separate address-keyed tables.
    fn tracked_pointer_place(&self, value: &Value) -> Option<Place> {
        match value {
            Value::Reference { addr, .. } => self.reference_places.get(addr).cloned(),
            Value::FatPtr(crate::values::FatPointer { data_pointer, .. }) => {
                self.tracked_pointer_place(data_pointer)
            }
            Value::RawPtr { addr, .. } => self
                .raw_pointer_places
                .get(addr)
                .cloned()
                .or_else(|| self.reference_places.get(addr).cloned()),
            _ => None,
        }
    }

    fn tracked_pointer_tag(&self, value: &Value) -> Option<BorrowTag> {
        match value {
            Value::Reference { addr, .. } => self.reference_tags.get(addr).copied(),
            Value::FatPtr(crate::values::FatPointer { data_pointer, .. }) => {
                self.tracked_pointer_tag(data_pointer)
            }
            Value::RawPtr { addr, tag, .. } => {
                (*tag).or_else(|| self.reference_tags.get(addr).copied())
            }
            _ => None,
        }
    }

    fn raw_pointer_permission_for_tag(
        &self,
        place: &Place,
        tag: BorrowTag,
    ) -> Option<BorrowPermission> {
        // Raw-pointer casts must not upgrade the source capability. The only
        // relaxation is `Unique` -> `SharedReadWrite`, since raw pointers are
        // writable but no longer exclusive once materialized.
        self.ctx
            .ownership
            .borrow_permission(place, tag)
            .map(|permission| match permission {
                BorrowPermission::Unique | BorrowPermission::SharedReadWrite => {
                    BorrowPermission::SharedReadWrite
                }
                BorrowPermission::SharedReadOnly
                    if self.aliasing_model == AliasingModel::TreeBorrows =>
                {
                    // Tree Borrows is more permissive about shared references
                    // coexisting with raw-pointer mutation. The interpreter
                    // does not yet model `UnsafeCell` projection precisely, so
                    // shared-reference raw casts relax to a writable raw
                    // capability in Tree Borrows mode.
                    BorrowPermission::SharedReadWrite
                }
                BorrowPermission::SharedReadOnly => BorrowPermission::SharedReadOnly,
                BorrowPermission::Disabled => BorrowPermission::Disabled,
            })
    }

    fn tracked_place_root(&self, place: &Place) -> Option<Place> {
        match place {
            Place::Local(_) | Place::Static(_) => Some(place.clone()),
            Place::Field { base, .. } | Place::Index { base, .. } => self.tracked_place_root(base),
            Place::Deref(_) | Place::Downcast { .. } => None,
        }
    }

    fn binding_value_for_place(&self, place: &Place) -> Option<&Value> {
        for (bindings_scope, places_scope) in
            self.bindings.iter().zip(self.scope_places.iter()).rev()
        {
            debug_assert_eq!(bindings_scope.len(), places_scope.len());
            if let Some(idx) = places_scope
                .iter()
                .rposition(|(_, candidate_place)| candidate_place == place)
            {
                return Some(&bindings_scope[idx].value);
            }
        }
        None
    }

    fn replace_binding_value_for_place(&mut self, place: &Place, value: Value) -> bool {
        for (bindings_scope, places_scope) in
            self.bindings.iter_mut().zip(self.scope_places.iter()).rev()
        {
            debug_assert_eq!(bindings_scope.len(), places_scope.len());
            if let Some(idx) = places_scope
                .iter()
                .rposition(|(_, candidate_place)| candidate_place == place)
            {
                bindings_scope[idx].value = value;
                return true;
            }
        }
        false
    }

    fn insert_shared_memory_binding(&mut self, place: Place, size: usize) {
        let name = match place {
            Place::Local(idx) => format!("__shared_memory_{idx}"),
            _ => unreachable!("shared memory allocations always use fresh local places"),
        };
        let initial_value = Value::Array(vec![Value::u8(0); size]);
        let drop_ty = initial_value.get_type();

        self.scope_places
            .last_mut()
            .expect("invariant: interpreter always has at least one scope")
            .push((name.clone(), place));
        self.bindings
            .last_mut()
            .expect("invariant: interpreter always has at least one scope")
            .push(LocalBinding {
                name,
                value: initial_value,
                drop_ty,
            });
    }

    fn remove_binding_for_place(&mut self, place: &Place) -> bool {
        for (bindings_scope, places_scope) in self
            .bindings
            .iter_mut()
            .zip(self.scope_places.iter_mut())
            .rev()
        {
            debug_assert_eq!(bindings_scope.len(), places_scope.len());
            if let Some(idx) = places_scope
                .iter()
                .rposition(|(_, candidate_place)| candidate_place == place)
            {
                places_scope.remove(idx);
                bindings_scope.remove(idx);
                return true;
            }
        }
        false
    }

    fn shared_memory_root(&self, place: &Place) -> Option<Place> {
        let root = self.tracked_place_root(place)?;
        (self.shared_memory_roots.contains(&root) && self.binding_value_for_place(&root).is_some())
            .then_some(root)
    }

    fn tracked_place_to_path(
        &self,
        place: &Place,
    ) -> Result<(Place, Vec<PlaceProjection>), RustSemError> {
        fn collect_path(
            place: &Place,
            path: &mut Vec<PlaceProjection>,
        ) -> Result<(), RustSemError> {
            match place {
                Place::Local(_) | Place::Static(_) => Ok(()),
                Place::Field { base, field } => {
                    collect_path(base, path)?;
                    path.push(PlaceProjection::Field(field.clone()));
                    Ok(())
                }
                Place::Index { base, index } => {
                    collect_path(base, path)?;
                    let Place::Local(idx) = index.as_ref() else {
                        return Err(RustSemError::TrackedIndexPlaceNotConcrete);
                    };
                    let idx = usize::try_from(*idx)
                        .map_err(|_| RustSemError::TrackedIndexTooLarge { index: *idx })?;
                    path.push(PlaceProjection::Index(idx));
                    Ok(())
                }
                Place::Deref(_) => Err(RustSemError::TrackedDerefUnsupported),
                Place::Downcast { .. } => Err(RustSemError::TrackedDowncastUnsupported),
            }
        }

        let root = self.tracked_place_root(place).ok_or_else(|| {
            RustSemError::TrackedPlaceRootUnresolved {
                place: place.clone(),
            }
        })?;
        let mut path = Vec::new();
        collect_path(place, &mut path)?;
        Ok((root, path))
    }

    fn project_value(value: &Value, path: &[PlaceProjection]) -> Result<Value, RustSemError> {
        if path.is_empty() {
            return Ok(value.clone());
        }
        match &path[0] {
            PlaceProjection::Field(field) => match value {
                Value::Struct { fields, .. } => {
                    let field_value =
                        fields
                            .get(field)
                            .ok_or_else(|| RustSemError::StructFieldMissing {
                                field: field.clone(),
                            })?;
                    Self::project_value(field_value, &path[1..])
                }
                Value::Enum { payload, .. } => match payload.as_ref() {
                    EnumPayload::Struct(fields) => {
                        let field_value =
                            fields
                                .get(field)
                                .ok_or_else(|| RustSemError::EnumFieldMissing {
                                    field: field.clone(),
                                })?;
                        Self::project_value(field_value, &path[1..])
                    }
                    _ => Err(RustSemError::FieldAccessRequiresStructPayload),
                },
                _ => Err(RustSemError::FieldAccessOnNonStructValue),
            },
            PlaceProjection::Index(idx) => match value {
                Value::Array(elements) | Value::Tuple(elements) => {
                    let element = elements
                        .get(*idx)
                        .ok_or(RustSemError::IndexOutOfBounds { index: *idx })?;
                    Self::project_value(element, &path[1..])
                }
                Value::Enum { payload, .. } => match payload.as_ref() {
                    EnumPayload::Tuple(elements) => {
                        let element = elements
                            .get(*idx)
                            .ok_or(RustSemError::IndexOutOfBounds { index: *idx })?;
                        Self::project_value(element, &path[1..])
                    }
                    _ => Err(RustSemError::IndexAccessRequiresTuplePayload),
                },
                _ => Err(RustSemError::IndexAccessOnNonArrayValue),
            },
        }
    }

    fn set_projected_value(
        value: &mut Value,
        path: &[PlaceProjection],
        new_value: Value,
    ) -> Result<(), RustSemError> {
        if path.is_empty() {
            *value = new_value;
            return Ok(());
        }
        match &path[0] {
            PlaceProjection::Field(field) => match value {
                Value::Struct { fields, .. } => {
                    let field_value =
                        fields
                            .get_mut(field)
                            .ok_or_else(|| RustSemError::StructFieldMissing {
                                field: field.clone(),
                            })?;
                    Self::set_projected_value(field_value, &path[1..], new_value)
                }
                Value::Enum { payload, .. } => match payload.as_mut() {
                    EnumPayload::Struct(fields) => {
                        let field_value = fields.get_mut(field).ok_or_else(|| {
                            RustSemError::EnumFieldMissing {
                                field: field.clone(),
                            }
                        })?;
                        Self::set_projected_value(field_value, &path[1..], new_value)
                    }
                    _ => Err(RustSemError::FieldAssignmentRequiresStructPayload),
                },
                _ => Err(RustSemError::FieldAssignmentOnNonStructValue),
            },
            PlaceProjection::Index(idx) => match value {
                Value::Array(elements) | Value::Tuple(elements) => {
                    let element = elements
                        .get_mut(*idx)
                        .ok_or(RustSemError::IndexOutOfBounds { index: *idx })?;
                    Self::set_projected_value(element, &path[1..], new_value)
                }
                Value::Enum { payload, .. } => match payload.as_mut() {
                    EnumPayload::Tuple(elements) => {
                        let element = elements
                            .get_mut(*idx)
                            .ok_or(RustSemError::IndexOutOfBounds { index: *idx })?;
                        Self::set_projected_value(element, &path[1..], new_value)
                    }
                    _ => Err(RustSemError::IndexAssignmentRequiresTuplePayload),
                },
                _ => Err(RustSemError::IndexAssignmentOnNonArrayValue),
            },
        }
    }

    fn read_tracked_place_value(&self, place: &Place) -> Result<Value, RustSemError> {
        let (root, path) = self.tracked_place_to_path(place)?;
        // The pointer's exact tag was already validated at the pointee. Reusing
        // `lookup` here would re-run alias checks on the root variable instead.
        let root_value = self
            .binding_value_for_place(&root)
            .ok_or_else(|| RustSemError::UnboundTrackedRootRead { root: root.clone() })?;
        let value = Self::project_value(root_value, &path)?;
        Ok(self.materialize_value(&value))
    }

    fn write_tracked_place_value(
        &mut self,
        place: &Place,
        value: Value,
    ) -> Result<(), RustSemError> {
        let (root, path) = self.tracked_place_to_path(place)?;
        let mut root_value = self
            .binding_value_for_place(&root)
            .map(|value| self.materialize_value(value))
            .ok_or_else(|| RustSemError::UnboundTrackedRootWrite { root: root.clone() })?;
        Self::set_projected_value(&mut root_value, &path, value)?;
        if self.replace_binding_value_for_place(&root, root_value) {
            Ok(())
        } else {
            Err(RustSemError::UnboundTrackedRootWrite { root })
        }
    }

    fn assign_through_pointer_result(
        &mut self,
        pointer: Value,
        value: Value,
        raw_pointer: bool,
    ) -> Result<Value, EvalError> {
        let is_raw_pointer = matches!(pointer, Value::RawPtr { .. });
        if raw_pointer || is_raw_pointer {
            self.ctx
                .require_unsafe("dereference of raw pointer")
                .map_err(|_| EvalError::UnsupportedOperation {
                    op: "dereference of raw pointer".to_string(),
                    context: "requires unsafe block or function".to_string(),
                })?;
        }

        if self.aliasing_checks {
            if let Some(place) = self.tracked_pointer_place(&pointer) {
                if let Some(tag) = self.tracked_pointer_tag(&pointer) {
                    self.ctx
                        .ownership
                        .access_whole_place(&place, tag, AccessKind::Write)
                        .map_err(EvalError::from)?;
                }
            }
        }

        if let Some(place) = self.tracked_pointer_place(&pointer) {
            self.write_tracked_place_value(&place, value)
                .map_err(EvalError::from)?;
            return Ok(Value::Unit);
        }

        let actual = Self::value_type_name(&pointer);
        match pointer {
            Value::RefCellRefMut { cell_id, .. } => self
                .write_interior_cell_value(cell_id, value)
                .map(|()| Value::Unit)
                .map_err(EvalError::from),
            Value::MutexGuard { lock_id, .. } | Value::RwLockWriteGuard { lock_id, .. } => self
                .write_interior_cell_value(lock_id, value)
                .map(|()| Value::Unit)
                .map_err(EvalError::from),
            Value::RefCellRef { .. } => Err(EvalError::BorrowError {
                kind: "immutable_refcell_borrow".to_string(),
                context: "deref write requires mutable RefCell borrow".to_string(),
            }),
            Value::RwLockReadGuard { .. } => Err(EvalError::BorrowError {
                kind: "immutable_rwlock_borrow".to_string(),
                context: "deref write requires a write-locked RwLock guard".to_string(),
            }),
            Value::RawPtr { addr, .. } => match value.as_u64() {
                Some(bits) => self
                    .ctx
                    .memory
                    .write_u64(addr, bits)
                    .map(|()| Value::Unit)
                    .map_err(|err| EvalError::DerefWriteFailed {
                        detail: err.to_string(),
                    }),
                None => Err(EvalError::UnsupportedOperation {
                    op: "raw pointer write".to_string(),
                    context: "currently requires a u64-compatible value".to_string(),
                }),
            },
            Value::Reference { .. } => Err(EvalError::BorrowError {
                kind: "missing_reference_provenance".to_string(),
                context: "deref write requires tracked reference provenance".to_string(),
            }),
            _ => Err(EvalError::TypeError {
                expected: "pointer".to_string(),
                actual,
                context: "assignment through dereference".to_string(),
            }),
        }
    }

    /// Assign to a place expression (field, index, or variable).
    ///
    /// Decomposes the target into a root variable and a path of projections,
    /// then applies the mutation in-place and writes back the updated root.
    fn assign_place(&mut self, target: &Expr, val: Value) -> EvalResult {
        match target {
            Expr::Deref(inner) => {
                let pointer = match self.eval(inner) {
                    EvalResult::Value(value) => value,
                    other => return other,
                };
                return match self.assign_through_pointer_result(pointer, val, false) {
                    Ok(value) => EvalResult::Value(value),
                    Err(err) => EvalResult::Error(err.to_string()),
                };
            }
            Expr::RawDeref(inner) => {
                let pointer = match self.eval(inner) {
                    EvalResult::Value(value) => value,
                    other => return other,
                };
                return match self.assign_through_pointer_result(pointer, val, true) {
                    Ok(value) => EvalResult::Value(value),
                    Err(err) => EvalResult::Error(err.to_string()),
                };
            }
            _ => {}
        }

        // Collect the projection path from target back to the root variable.
        // E.g. `a.x[0].y = v` → root = "a", path = [Field("x"), Index(0), Field("y")]
        let mut path = Vec::new();
        let mut current = target;
        let root_name = loop {
            match current {
                Expr::Var { name, .. } => break name.clone(),
                Expr::Field { base, field } => {
                    path.push(PlaceProjection::Field(field.clone()));
                    current = base.as_ref();
                }
                Expr::Index { base, index } => {
                    let idx_val = match self.eval(index) {
                        EvalResult::Value(v) => v,
                        other => return other,
                    };
                    let idx = match self.index_from_value(&idx_val, "assignment index") {
                        Ok(index) => index,
                        Err(err) => return EvalResult::Error(err.to_string()),
                    };
                    path.push(PlaceProjection::Index(idx));
                    current = base.as_ref();
                }
                _ => {
                    return EvalResult::Error(
                        EvalError::UnsupportedOperation {
                            op: "assignment".to_string(),
                            context: "unsupported assignment target".to_string(),
                        }
                        .to_string(),
                    )
                }
            }
        };
        // path is root→leaf order reversed; reverse to get root→leaf
        path.reverse();

        let project_place = |base: Place, path: &[PlaceProjection]| {
            path.iter().fold(base, |assigned_place, proj| match proj {
                PlaceProjection::Field(field) => Place::Field {
                    base: Box::new(assigned_place),
                    field: field.clone(),
                },
                PlaceProjection::Index(index) => Place::Index {
                    base: Box::new(assigned_place),
                    index: Box::new(Place::Local(*index as u32)),
                },
            })
        };
        let root_place = self.place_for_name(&root_name);
        let assigned_place = project_place(root_place.clone(), &path);

        let mut root_val: Value = match self.lookup_typed(&root_name) {
            Ok(value) => value,
            Err(err) => return EvalResult::Error(err.to_string()),
        };

        // Projection writes should check the exact root place for whole-object
        // borrows such as `&s`, but only invalidate descendants of the
        // assigned sub-place (for example `s.x.y` when assigning `s.x`).
        if self.aliasing_checks && self.tracked_pointer_place(&root_val).is_none() {
            if path.is_empty() {
                if let Err(err) = self.validate_whole_place_write(&assigned_place) {
                    return EvalResult::Error(EvalError::from(err).to_string());
                }
            } else {
                let root_tag = self.ctx.ownership.current_or_root_tag(&root_place);
                if let Err(err) =
                    self.ctx
                        .ownership
                        .access_place(&root_place, root_tag, AccessKind::Write)
                {
                    return EvalResult::Error(EvalError::from(err).to_string());
                }
                let assigned_tag = self.ctx.ownership.current_or_root_tag(&assigned_place);
                if let Err(err) = self.ctx.ownership.access_whole_place(
                    &assigned_place,
                    assigned_tag,
                    AccessKind::Write,
                ) {
                    return EvalResult::Error(EvalError::from(err).to_string());
                }
            }
        }

        if !path.is_empty() {
            if let Some(pointer_place) = self.tracked_pointer_place(&root_val) {
                let projected_pointer_place = project_place(pointer_place.clone(), &path);
                if self.aliasing_checks {
                    let Some(pointer_tag) = self.tracked_pointer_tag(&root_val) else {
                        return EvalResult::Error(
                            EvalError::BorrowError {
                                kind: "missing_borrow_tag".to_string(),
                                context: "tracked receiver is missing a borrow tag".to_string(),
                            }
                            .to_string(),
                        );
                    };
                    if let Err(err) = self.ctx.ownership.access_whole_place(
                        &pointer_place,
                        pointer_tag,
                        AccessKind::Write,
                    ) {
                        return EvalResult::Error(EvalError::from(err).to_string());
                    }
                }
                if let Value::Reference {
                    referent: Some(referent),
                    ..
                } = &mut root_val
                {
                    if let Err(err) = Self::set_value_at_path(referent.as_mut(), &path, val.clone())
                    {
                        return EvalResult::Error(err.to_string());
                    }
                    if !self.replace_var(&root_name, root_val.clone()) {
                        return EvalResult::Error(
                            EvalError::UnboundVariable {
                                name: root_name.clone(),
                            }
                            .to_string(),
                        );
                    }
                }
                return match self.write_tracked_place_value(&projected_pointer_place, val) {
                    Ok(()) => EvalResult::Value(Value::Unit),
                    Err(err) => EvalResult::Error(EvalError::from(err).to_string()),
                };
            }
        }

        if let Err(e) = Self::set_value_at_path(&mut root_val, &path, val) {
            return EvalResult::Error(e.to_string());
        }

        if self.replace_var(&root_name, root_val) {
            EvalResult::Value(Value::Unit)
        } else {
            EvalResult::Error(EvalError::UnboundVariable { name: root_name }.to_string())
        }
    }

    /// Apply pattern bindings to current scope, using drop type hints when
    /// available to preserve generic type arguments that `Value::get_type()`
    /// would otherwise erase.
    fn apply_bindings(&mut self, bindings: PatternBindings) {
        for (name, value, _mutable, drop_type) in bindings.bindings {
            match drop_type {
                Some(ty) => self.bind_with_drop_type(name, value, ty),
                None => self.bind(name, value),
            }
        }
    }

    fn hoist_scope_items<'a>(
        &mut self,
        items: impl IntoIterator<Item = &'a Item>,
    ) -> Result<(), RustSemError> {
        let items = items.into_iter().collect::<Vec<_>>();

        for item in &items {
            match item {
                Item::Fn { .. }
                | Item::Struct { .. }
                | Item::Enum { .. }
                | Item::TraitDef(_)
                | Item::Union { .. } => self.process_item(item),
                Item::ImplAssociatedType { .. } => {}
                Item::Impl { .. }
                | Item::Const { .. }
                | Item::Static { .. }
                | Item::TypeAlias { .. }
                | Item::GlobalAsm(_) => {}
            }
        }

        for item in &items {
            if matches!(item, Item::Impl { .. }) {
                self.process_item(item);
            }
        }

        let mut const_items = Vec::new();
        for item in &items {
            match item {
                Item::Const { .. } | Item::Static { .. } => const_items.push(*item),
                Item::Impl { items, .. } => {
                    const_items.extend(
                        items
                            .iter()
                            .filter(|sub_item| matches!(sub_item, Item::Const { .. })),
                    );
                }
                Item::GlobalAsm(_) => {}
                _ => {}
            }
        }

        self.resolve_const_static_items(const_items)
    }

    fn hoist_block_items(&mut self, stmts: &[Stmt]) -> Result<(), RustSemError> {
        self.hoist_scope_items(stmts.iter().filter_map(|stmt| match stmt {
            Stmt::Item(item) => Some(item),
            Stmt::Let { .. } | Stmt::Expr(_) => None,
        }))
    }

    fn resolve_const_static_items<'a>(
        &mut self,
        items: impl IntoIterator<Item = &'a Item>,
    ) -> Result<(), RustSemError> {
        let mut pending = items.into_iter().collect::<Vec<_>>();
        while !pending.is_empty() {
            let mut next_pending = Vec::new();
            let mut progress = false;
            for item in pending {
                match self.try_process_const_static_item(item)? {
                    true => progress = true,
                    false => next_pending.push(item),
                }
            }

            if !progress {
                let unresolved = next_pending
                    .iter()
                    .map(|item| self.describe_unresolved_const_static(item))
                    .collect::<Vec<_>>()
                    .join(", ");
                return Err(RustSemError::UnresolvedConstStaticItems { unresolved });
            }

            pending = next_pending;
        }
        Ok(())
    }

    fn try_process_const_static_item(&mut self, item: &Item) -> Result<bool, RustSemError> {
        let (name, ty, value) = match item {
            Item::Const { name, ty, value }
            | Item::Static {
                name, ty, value, ..
            } => (name, ty, value),
            _ => return Ok(true),
        };

        match self.eval(value) {
            EvalResult::Value(v) => {
                self.bind_with_drop_type(name.clone(), v, ty.clone());
                Ok(true)
            }
            EvalResult::Error(err) if err.starts_with("unbound variable `") => Ok(false),
            EvalResult::Error(detail) => Err(RustSemError::ConstStaticResolutionFailed {
                name: name.clone(),
                detail,
            }),
            EvalResult::Return(_) => {
                Err(RustSemError::ConstStaticInitializerReturned { name: name.clone() })
            }
            EvalResult::Break { .. } => {
                Err(RustSemError::ConstStaticInitializerBrokeOut { name: name.clone() })
            }
            EvalResult::Continue { .. } => {
                Err(RustSemError::ConstStaticInitializerContinued { name: name.clone() })
            }
            EvalResult::Panic(message) => Err(RustSemError::ConstStaticInitializerPanicked {
                name: name.clone(),
                message,
            }),
        }
    }

    fn describe_unresolved_const_static(&mut self, item: &Item) -> String {
        let (name, value) = match item {
            Item::Const { name, value, .. } | Item::Static { name, value, .. } => (name, value),
            _ => return "non-const item".to_string(),
        };

        match self.eval(value) {
            EvalResult::Error(err) => format!("{name} ({err})"),
            EvalResult::Value(_) => name.clone(),
            EvalResult::Return(_) => format!("{name} (initializer returned from scope)"),
            EvalResult::Break { .. } => format!("{name} (initializer broke out of scope)"),
            EvalResult::Continue { .. } => format!("{name} (initializer continued a loop)"),
            EvalResult::Panic(msg) => format!("{name} (initializer panicked: {msg})"),
        }
    }

    /// Returns true when a break/continue label targets this loop.
    /// Unlabeled break/continue always targets the innermost loop.
    /// Labeled break/continue targets the loop whose label matches.
    #[must_use]
    fn targets_this_loop(target: &Option<String>, loop_label: &Option<String>) -> bool {
        match target {
            None => true,
            Some(l) => loop_label.as_deref() == Some(l.as_str()),
        }
    }

    fn for_loop_elements(iterable: Value) -> Result<Vec<Value>, RustSemError> {
        // Deref-view through references/guards so `for x in &collection`,
        // `for x in &mut collection`, `collection.iter()`, and
        // `collection.into_iter()` all iterate the underlying value. The
        // semantic model treats shared/owned iteration identically because
        // values are cloned per element rather than aliased.
        match iterable.deref_view() {
            Value::Array(elems) => Ok(elems.clone()),
            Value::Tuple(elems) => Ok(elems.clone()),
            Value::Range {
                start,
                end,
                inclusive,
            } => Self::range_elements(start.as_deref(), end.as_deref(), *inclusive),
            // `HashMap<K, V>` / `BTreeMap<K, V>` are modeled as a struct whose
            // `entries` field holds the `(K, V)` pairs as a `Value::Array` of
            // 2-tuples. Iterating a map (or its keys/values via `keys()` /
            // `values()`, which materialize an array) yields those pairs in the
            // order the model stores them. HashMap iteration order is
            // unspecified in Rust, so verification must not depend on it; this
            // mirrors how every other unordered-collection consumer in the
            // crate reads the `entries` array.
            Value::Struct { name, fields } if name == "HashMap" || name == "BTreeMap" => {
                match fields.get("entries") {
                    Some(Value::Array(entries)) => Ok(entries.clone()),
                    _ => Ok(Vec::new()),
                }
            }
            _ => Err(RustSemError::ForLoopRequiresIterable),
        }
    }

    /// Pair each loop element with the drop type hint projected from the
    /// iterable expression. Tuples project per-index; arrays reuse the
    /// element type; ranges yield `None` (integer `get_type()` is exact).
    fn for_loop_elements_with_hints(
        &self,
        iter_expr: &Expr,
        iter_value: &Value,
    ) -> Result<Vec<(Value, Option<RustType>)>, RustSemError> {
        let iter_hint = self.drop_type_hint_for_value(iter_expr, iter_value);
        let elements = Self::for_loop_elements(iter_value.clone())?;

        let paired: Vec<(Value, Option<RustType>)> = match iter_hint {
            Some(RustType::Tuple(ref elem_types)) => elements
                .into_iter()
                .enumerate()
                .map(|(i, v)| {
                    let hint = elem_types.get(i).cloned();
                    (v, hint)
                })
                .collect(),
            Some(RustType::Array { ref element, .. }) => {
                let elem_ty = element.as_ref().clone();
                elements
                    .into_iter()
                    .map(|v| (v, Some(elem_ty.clone())))
                    .collect()
            }
            _ => elements.into_iter().map(|v| (v, None)).collect(),
        };
        Ok(paired)
    }

    fn range_elements(
        start: Option<&Value>,
        end: Option<&Value>,
        inclusive: bool,
    ) -> Result<Vec<Value>, RustSemError> {
        match (start, end) {
            (
                Some(Value::Uint {
                    value: start,
                    ty: start_ty,
                }),
                Some(Value::Uint {
                    value: end,
                    ty: end_ty,
                }),
            ) => {
                if start_ty != end_ty {
                    return Err(RustSemError::ForLoopRangeTypeMismatch);
                }
                Self::collect_uint_range(*start, *end, *start_ty, inclusive)
            }
            (
                Some(Value::Int {
                    value: start,
                    ty: start_ty,
                }),
                Some(Value::Int {
                    value: end,
                    ty: end_ty,
                }),
            ) => {
                if start_ty != end_ty {
                    return Err(RustSemError::ForLoopRangeTypeMismatch);
                }
                Self::collect_int_range(*start, *end, *start_ty, inclusive)
            }
            (None, _) | (_, None) | (Some(Value::Unit), _) | (_, Some(Value::Unit)) => {
                Err(RustSemError::ForLoopRangeMissingBounds)
            }
            _ => Err(RustSemError::ForLoopRangeNonIntegerBounds),
        }
    }

    fn collect_uint_range(
        start: u128,
        end: u128,
        ty: UintType,
        inclusive: bool,
    ) -> Result<Vec<Value>, RustSemError> {
        if start > end || (!inclusive && start == end) {
            return Ok(Vec::new());
        }

        let mut values = Vec::new();
        let mut current = start;
        loop {
            values.push(Value::Uint { value: current, ty });
            if current == end {
                break;
            }
            current = current
                .checked_add(1)
                .ok_or(RustSemError::ForLoopRangeOverflow)?;
            if !inclusive && current == end {
                break;
            }
        }
        Ok(values)
    }

    fn collect_int_range(
        start: i128,
        end: i128,
        ty: IntType,
        inclusive: bool,
    ) -> Result<Vec<Value>, RustSemError> {
        if start > end || (!inclusive && start == end) {
            return Ok(Vec::new());
        }

        let mut values = Vec::new();
        let mut current = start;
        loop {
            values.push(Value::Int { value: current, ty });
            if current == end {
                break;
            }
            current = current
                .checked_add(1)
                .ok_or(RustSemError::ForLoopRangeOverflow)?;
            if !inclusive && current == end {
                break;
            }
        }
        Ok(values)
    }

    fn eval_inline_asm(&mut self, asm: &InlineAsm) -> EvalResult {
        inline_asm::eval_inline_asm(self, asm)
    }

    fn havoc_modeled_memory(&mut self) -> Result<(), RustSemError> {
        self.ctx.memory.havoc_all();

        let roots: Vec<Place> = self
            .scope_places
            .iter()
            .flat_map(|scope| scope.iter().map(|(_, place)| place.clone()))
            .collect();

        for root in roots {
            if matches!(
                self.binding_value_for_place(&root),
                Some(Value::FnPtr { .. })
            ) {
                continue;
            }
            self.write_tracked_place_value(&root, Value::Uninit)?;
        }

        Ok(())
    }

    /// Evaluate an expression
    pub fn eval(&mut self, expr: &Expr) -> EvalResult {
        // Check recursion depth
        if self.recursion_depth > MAX_RECURSION_DEPTH {
            return EvalResult::Error("maximum recursion depth exceeded".to_string());
        }

        match expr {
            Expr::Literal(v) => EvalResult::Value(v.clone()),

            Expr::Var { name, .. } => match self.lookup_typed(name) {
                Ok(value) => EvalResult::Value(value),
                Err(EvalError::UnboundVariable { .. }) => {
                    if self.ctx.get_function(name).is_some()
                        || Self::is_intrinsic_function_name(name)
                        || self.tuple_enum_variant_arity(name).is_some()
                    {
                        EvalResult::Value(Value::FnPtr { name: name.clone() })
                    } else {
                        EvalResult::Error(
                            EvalError::UnboundVariable { name: name.clone() }.to_string(),
                        )
                    }
                }
                Err(err) => EvalResult::Error(err.to_string()),
            },

            Expr::Field { base, field } => {
                let base_val = match self.eval(base) {
                    EvalResult::Value(v) => v,
                    other => return other,
                };
                match Self::field_access_value(&base_val, field) {
                    Ok(value) => EvalResult::Value(value),
                    Err(err) => EvalResult::Error(err.to_string()),
                }
            }

            Expr::Index { base, index } => {
                let base_val = match self.eval(base) {
                    EvalResult::Value(v) => v,
                    other => return other,
                };
                let index_val = match self.eval(index) {
                    EvalResult::Value(v) => v,
                    other => return other,
                };
                let idx = match self.index_from_value(&index_val, "index access") {
                    Ok(index) => index,
                    Err(err) => return EvalResult::Error(err.to_string()),
                };
                match Self::index_access_value(&base_val, idx) {
                    Ok(value) => EvalResult::Value(value),
                    Err(err) => EvalResult::Error(err.to_string()),
                }
            }

            Expr::Deref(inner) => {
                let inner_val = match self.eval(inner) {
                    EvalResult::Value(v) => v,
                    other => return other,
                };
                match self.deref_value(inner_val) {
                    Ok(value) => EvalResult::Value(value),
                    Err(err) => EvalResult::Error(err.to_string()),
                }
            }

            Expr::AddrOf {
                mutability,
                expr: inner,
            } => {
                let inner_val = match self.eval(inner) {
                    EvalResult::Value(v) => v,
                    other => return other,
                };
                match self.addr_of_value(inner, inner_val, *mutability) {
                    Ok(value) => EvalResult::Value(value),
                    Err(err) => EvalResult::Error(err.to_string()),
                }
            }

            Expr::Assign { target, value } => {
                let val = match self.eval(value) {
                    EvalResult::Value(v) => v,
                    other => return other,
                };
                self.assign_place(target, val)
            }

            Expr::AssignOp { op, target, value } => {
                let left_val = match self.eval(target) {
                    EvalResult::Value(v) => v,
                    other => return other,
                };
                let right_val = match self.eval(value) {
                    EvalResult::Value(v) => v,
                    other => return other,
                };
                let combined = match Self::binop_value(*op, &left_val, &right_val) {
                    Ok(value) => value,
                    Err(err) => return EvalResult::Error(err.to_string()),
                };
                self.assign_place(target, combined)
            }

            Expr::BinOp { op, left, right } => {
                let left_val = match self.eval(left) {
                    EvalResult::Value(v) => v,
                    other => return other,
                };
                let right_val = match self.eval(right) {
                    EvalResult::Value(v) => v,
                    other => return other,
                };
                match Self::binop_value(*op, &left_val, &right_val) {
                    Ok(value) => EvalResult::Value(value),
                    Err(err) => EvalResult::Error(err.to_string()),
                }
            }

            Expr::UnOp { op, expr: inner } => {
                let inner_val = match self.eval(inner) {
                    EvalResult::Value(v) => v,
                    other => return other,
                };
                match Self::unop_value(*op, &inner_val) {
                    Ok(value) => EvalResult::Value(value),
                    Err(err) => EvalResult::Error(err.to_string()),
                }
            }

            Expr::Cast {
                expr: inner,
                target,
            } => {
                let inner_val = match self.eval(inner) {
                    EvalResult::Value(v) => v,
                    other => return other,
                };
                // Enum-to-integer cast: look up variant discriminant from type registry
                if let Value::Enum {
                    name: enum_name,
                    variant: variant_name,
                    ..
                } = &inner_val
                {
                    if matches!(target, RustType::Int(_) | RustType::Uint(_)) {
                        if let Some(disc) = self.lookup_enum_discriminant(enum_name, variant_name) {
                            return match cast_value(
                                &Value::Int {
                                    value: disc,
                                    ty: IntType::I128,
                                },
                                target,
                            ) {
                                Some(v) => EvalResult::Value(v),
                                None => EvalResult::Error(format!(
                                    "enum discriminant cast to {target:?} failed"
                                )),
                            };
                        }
                    }
                }
                match cast_value(&inner_val, target) {
                    Some(v) => {
                        if self.aliasing_checks && matches!(target, RustType::RawPtr { .. }) {
                            if let Some(place) = self.tracked_pointer_place(&inner_val) {
                                let Some(source_tag) = self.tracked_pointer_tag(&inner_val) else {
                                    return EvalResult::Error(
                                        "tracked pointer cast is missing a borrow tag".to_string(),
                                    );
                                };
                                if let Err(err) = self.ctx.ownership.access_place(
                                    &place,
                                    source_tag,
                                    AccessKind::Read,
                                ) {
                                    return EvalResult::Error(format!(
                                        "stacked borrows: raw pointer cast rejected: {err}"
                                    ));
                                }
                                let Some(permission) =
                                    self.raw_pointer_permission_for_tag(&place, source_tag)
                                else {
                                    return EvalResult::Error(
                                        "tracked pointer cast is missing source permission"
                                            .to_string(),
                                    );
                                };
                                let tag = match self
                                    .ctx
                                    .ownership
                                    .retag_place_from_tag(&place, source_tag, permission, None)
                                {
                                    Ok(tag) => tag,
                                    Err(err) => {
                                        return EvalResult::Error(format!(
                                            "raw pointer retag failed: {err}"
                                        ))
                                    }
                                };
                                let raw_pointer = self.remember_raw_pointer_place(v, place, tag);
                                return EvalResult::Value(raw_pointer);
                            }
                        }
                        EvalResult::Value(v)
                    }
                    None => EvalResult::Error("cast failed".to_string()),
                }
            }

            Expr::Call {
                func,
                args,
                type_args,
            } => self.eval_call(func, args, type_args),

            Expr::MethodCall {
                receiver,
                method,
                args,
                type_args,
            } => self.eval_method_call(receiver, method, args, type_args),

            Expr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                let cond_val = match self.eval(condition) {
                    EvalResult::Value(v) => v,
                    other => return other,
                };
                let Value::Bool(cond_bool) = cond_val else {
                    return EvalResult::Error("condition must be boolean".to_string());
                };
                if cond_bool {
                    self.eval(then_branch)
                } else {
                    match else_branch {
                        Some(e) => self.eval(e),
                        None => EvalResult::Value(Value::Unit),
                    }
                }
            }

            Expr::Match { scrutinee, arms } => {
                let scrutinee_val = match self.eval(scrutinee) {
                    EvalResult::Value(v) => v,
                    other => return other,
                };
                let scrutinee_hint = self.drop_type_hint_for_value(scrutinee, &scrutinee_val);
                self.eval_match(&scrutinee_val, scrutinee_hint.as_ref(), arms)
            }

            Expr::Block { stmts, expr } => {
                self.push_scope();
                if let Err(err) = self.hoist_block_items(stmts) {
                    self.pop_scope();
                    return EvalResult::Error(err.to_string());
                }
                for stmt in stmts {
                    match self.exec_stmt(stmt) {
                        StmtResult::Ok => {}
                        StmtResult::Return(v) => {
                            self.pop_scope();
                            return EvalResult::Return(v);
                        }
                        StmtResult::Break { label, value } => {
                            self.pop_scope();
                            return EvalResult::Break { label, value };
                        }
                        StmtResult::Continue { label } => {
                            self.pop_scope();
                            return EvalResult::Continue { label };
                        }
                        StmtResult::Panic(msg) => {
                            self.pop_scope_with_unwind(true);
                            return EvalResult::Panic(msg);
                        }
                        StmtResult::Error(e) => {
                            self.pop_scope();
                            return EvalResult::Error(e);
                        }
                    }
                }
                let result = match expr {
                    Some(e) => self.eval(e),
                    None => EvalResult::Value(Value::Unit),
                };
                self.pop_scope_for_eval_result(&result);
                result
            }

            Expr::Tuple(elems) => {
                let mut values = Vec::with_capacity(elems.len());
                for e in elems {
                    match self.eval(e) {
                        EvalResult::Value(v) => values.push(v),
                        other => return other,
                    }
                }
                EvalResult::Value(Value::Tuple(values))
            }

            Expr::Array(elems) => {
                let mut values = Vec::with_capacity(elems.len());
                for e in elems {
                    match self.eval(e) {
                        EvalResult::Value(v) => values.push(v),
                        other => return other,
                    }
                }
                EvalResult::Value(Value::Array(values))
            }

            Expr::ArrayRepeat { value, count } => {
                let val = match self.eval(value) {
                    EvalResult::Value(v) => v,
                    other => return other,
                };
                EvalResult::Value(Value::Array(vec![val; *count]))
            }

            Expr::Struct {
                name,
                fields,
                type_args,
                const_args,
            } => {
                // Resolve declared field types for coercion (if struct def is registered).
                // When explicit type_args are provided, substitute type params in field types.
                let field_types: Option<Vec<(String, RustType)>> = match self.ctx.get_type(name) {
                    Some(crate::stmt::TypeDef::Struct {
                        fields,
                        type_params,
                        const_params,
                        ..
                    }) => {
                        let type_subst = if type_args.is_empty() {
                            HashMap::new()
                        } else {
                            match RustType::build_type_param_subst(type_params, type_args) {
                                Some(subst) => subst,
                                None => {
                                    return EvalResult::Error(format!(
                                        "struct {} expects {} type args, got {}",
                                        name,
                                        type_params.len(),
                                        type_args.len()
                                    ));
                                }
                            }
                        };
                        let const_subst = if const_args.is_empty() {
                            HashMap::new()
                        } else {
                            match RustType::build_const_param_subst(const_params, const_args) {
                                Some(subst) => subst,
                                None => {
                                    return EvalResult::Error(format!(
                                        "struct {} expects {} const args, got {}",
                                        name,
                                        const_params.len(),
                                        const_args.len()
                                    ));
                                }
                            }
                        };
                        if type_subst.is_empty() && const_subst.is_empty() {
                            Some(fields.clone())
                        } else {
                            Some(
                                fields
                                    .iter()
                                    .map(|(n, ty)| {
                                        (
                                            n.clone(),
                                            ty.substitute_type_params(&type_subst)
                                                .substitute_const_params(&const_subst),
                                        )
                                    })
                                    .collect(),
                            )
                        }
                    }
                    _ => None,
                };

                let mut field_values = BTreeMap::new();
                for (field_name, field_expr) in fields {
                    match self.eval(field_expr) {
                        EvalResult::Value(v) => {
                            // Coerce field value to declared field type when available.
                            let v = field_types
                                .as_ref()
                                .and_then(|ft| {
                                    ft.iter()
                                        .find(|(n, _)| n == field_name)
                                        .and_then(|(_, ty)| self.coerce_runtime_value(&v, ty))
                                })
                                .unwrap_or(v);
                            field_values.insert(field_name.clone(), v);
                        }
                        other => return other,
                    }
                }
                EvalResult::Value(Value::Struct {
                    name: name.clone(),
                    fields: field_values,
                })
            }

            Expr::EnumVariant {
                enum_name,
                variant,
                payload,
                type_args,
                const_args,
            } => {
                // Resolve variant payload types for coercion.
                // When explicit type_args are provided, substitute type params in payload types.
                let (variant_def, type_subst, const_subst) = match self.ctx.get_type(enum_name) {
                    Some(crate::stmt::TypeDef::Enum {
                        variants,
                        type_params,
                        const_params,
                        ..
                    }) => {
                        let type_subst = if type_args.is_empty() {
                            HashMap::new()
                        } else {
                            match RustType::build_type_param_subst(type_params, type_args) {
                                Some(subst) => subst,
                                None => {
                                    return EvalResult::Error(format!(
                                        "enum {} expects {} type args, got {}",
                                        enum_name,
                                        type_params.len(),
                                        type_args.len()
                                    ));
                                }
                            }
                        };
                        let const_subst = if const_args.is_empty() {
                            HashMap::new()
                        } else {
                            match RustType::build_const_param_subst(const_params, const_args) {
                                Some(subst) => subst,
                                None => {
                                    return EvalResult::Error(format!(
                                        "enum {} expects {} const args, got {}",
                                        enum_name,
                                        const_params.len(),
                                        const_args.len()
                                    ));
                                }
                            }
                        };
                        (
                            variants.iter().find(|v| v.name == *variant).cloned(),
                            type_subst,
                            const_subst,
                        )
                    }
                    _ => (None, HashMap::new(), HashMap::new()),
                };

                let enum_payload = match payload {
                    EnumVariantPayload::Unit => EnumPayload::Unit,
                    EnumVariantPayload::Tuple(exprs) => {
                        let tuple_types = variant_def.as_ref().and_then(|vd| match &vd.payload {
                            crate::stmt::EnumVariantType::Tuple(tys)
                                if type_subst.is_empty() && const_subst.is_empty() =>
                            {
                                Some(tys.clone())
                            }
                            crate::stmt::EnumVariantType::Tuple(tys) => Some(
                                tys.iter()
                                    .map(|ty| {
                                        ty.substitute_type_params(&type_subst)
                                            .substitute_const_params(&const_subst)
                                    })
                                    .collect(),
                            ),
                            _ => None,
                        });
                        let mut values = Vec::with_capacity(exprs.len());
                        for (i, e) in exprs.iter().enumerate() {
                            match self.eval(e) {
                                EvalResult::Value(v) => {
                                    let v = tuple_types
                                        .as_ref()
                                        .and_then(|tys| {
                                            tys.get(i)
                                                .and_then(|ty| self.coerce_runtime_value(&v, ty))
                                        })
                                        .unwrap_or(v);
                                    values.push(v);
                                }
                                other => return other,
                            }
                        }
                        EnumPayload::Tuple(values)
                    }
                    EnumVariantPayload::Struct(fields) => {
                        let struct_types = variant_def.as_ref().and_then(|vd| match &vd.payload {
                            crate::stmt::EnumVariantType::Struct(ft)
                                if type_subst.is_empty() && const_subst.is_empty() =>
                            {
                                Some(ft.clone())
                            }
                            crate::stmt::EnumVariantType::Struct(ft) => Some(
                                ft.iter()
                                    .map(|(n, ty)| {
                                        (
                                            n.clone(),
                                            ty.substitute_type_params(&type_subst)
                                                .substitute_const_params(&const_subst),
                                        )
                                    })
                                    .collect(),
                            ),
                            _ => None,
                        });
                        let mut field_values = BTreeMap::new();
                        for (name, expr) in fields {
                            match self.eval(expr) {
                                EvalResult::Value(v) => {
                                    let v = struct_types
                                        .as_ref()
                                        .and_then(|ft| {
                                            ft.iter().find(|(n, _)| n == name).and_then(
                                                |(_, ty)| self.coerce_runtime_value(&v, ty),
                                            )
                                        })
                                        .unwrap_or(v);
                                    field_values.insert(name.clone(), v);
                                }
                                other => return other,
                            }
                        }
                        EnumPayload::Struct(field_values)
                    }
                };
                EvalResult::Value(Value::Enum {
                    name: enum_name.clone(),
                    variant: variant.clone(),
                    payload: Box::new(enum_payload),
                })
            }

            Expr::Closure {
                params,
                body,
                captures,
                capture_by_value,
            } => {
                // Capture the current environment
                let mut captured_values = Vec::new();
                let mut captured_places = Vec::new();
                let mut captured_bindings = Vec::new();
                for (name, mutability) in captures {
                    if let Some(v) = self.lookup(name) {
                        captured_bindings.push(CaptureBinding::new(
                            name.clone(),
                            capture_mode_for_resolved_capture(*mutability, *capture_by_value, &v),
                            v.clone(),
                        ));
                        captured_values.push((name.clone(), v, *mutability));
                        captured_places.push((
                            name.clone(),
                            self.place_for_name(name),
                            *mutability,
                        ));
                    }
                }

                // Create closure value with unique ID
                let closure_id = format!(
                    "closure_{}",
                    self.ctx
                        .memory
                        .allocate(0)
                        .map(|a| a.alloc_id.0)
                        .unwrap_or(0)
                );

                // Infer return type from the closure body
                let ret_type = Self::infer_closure_return_type(body);

                // Extract param types from the params
                let param_types: Vec<RustType> = params.iter().map(|(_, ty)| ty.clone()).collect();

                // Determine closure kind from the captures that actually resolved
                // out of the current environment. Source-side capture collection
                // is intentionally conservative and may include locals that are
                // not visible when the closure is created.
                // Move closures stay conservatively classified as FnOnce when
                // any capture resolves. Capture-mode tracking still records
                // `ByCopy` vs `ByMove`, but kind inference remains conservative
                // until closure body use is modeled more precisely.
                let kind = if *capture_by_value && !captured_values.is_empty() {
                    ClosureKind::FnOnce
                } else {
                    ClosureKind::from_captures(
                        &captures
                            .iter()
                            .map(|(name, m)| (name.clone(), *m))
                            .collect::<Vec<_>>(),
                    )
                };
                if let Err(err) = validate_capture_modes(kind, &captured_bindings) {
                    return EvalResult::Error(err);
                }

                // Store the closure body as a function with inferred return type
                // Closures are never unsafe in their own right
                self.ctx.register_function(FunctionDef {
                    name: closure_id.clone(),
                    params: params.clone(),
                    ret_ty: ret_type.clone(),
                    body: (**body).clone(),
                    is_unsafe: false,
                    is_async: false,
                    type_params: vec![],
                });
                self.closure_capture_places
                    .insert(closure_id.clone(), captured_places);

                EvalResult::Value(Value::Closure {
                    fn_id: closure_id,
                    captures: captured_values,
                    param_types,
                    ret_type,
                    kind,
                })
            }

            Expr::Range {
                start,
                end,
                inclusive,
            } => {
                let start_val = match start {
                    Some(e) => match self.eval(e) {
                        EvalResult::Value(v) => Some(Box::new(v)),
                        other => return other,
                    },
                    None => None,
                };
                let end_val = match end {
                    Some(e) => match self.eval(e) {
                        EvalResult::Value(v) => Some(Box::new(v)),
                        other => return other,
                    },
                    None => None,
                };
                EvalResult::Value(Value::Range {
                    start: start_val,
                    end: end_val,
                    inclusive: *inclusive,
                })
            }

            Expr::Return(opt_expr) => {
                let val = match opt_expr {
                    Some(e) => match self.eval(e) {
                        EvalResult::Value(v) => v,
                        other => return other,
                    },
                    None => Value::Unit,
                };
                EvalResult::Return(val)
            }

            Expr::Break { label, value } => {
                let val = match value {
                    Some(e) => match self.eval(e) {
                        EvalResult::Value(v) => Some(v),
                        other => return other,
                    },
                    None => None,
                };
                EvalResult::Break {
                    label: label.clone(),
                    value: val,
                }
            }

            Expr::Continue { label } => EvalResult::Continue {
                label: label.clone(),
            },

            Expr::Loop { label, body } => {
                for _ in 0..MAX_LOOP_ITERATIONS {
                    let result = self.eval(body);
                    match &result {
                        EvalResult::Value(_) => {}
                        EvalResult::Continue { label: ref tgt }
                            if Self::targets_this_loop(tgt, label) => {}
                        EvalResult::Break {
                            label: ref tgt,
                            value,
                        } if Self::targets_this_loop(tgt, label) => {
                            return EvalResult::Value(value.clone().unwrap_or(Value::Unit));
                        }
                        _ => return result,
                    }
                }
                EvalResult::Error("maximum loop iterations exceeded".to_string())
            }

            Expr::While {
                label,
                condition,
                body,
            } => {
                for _ in 0..MAX_LOOP_ITERATIONS {
                    let cond_val = match self.eval(condition) {
                        EvalResult::Value(v) => v,
                        other => return other,
                    };
                    let Value::Bool(cond_bool) = cond_val else {
                        return EvalResult::Error("while condition must be boolean".to_string());
                    };
                    if !cond_bool {
                        return EvalResult::Value(Value::Unit);
                    }
                    let result = self.eval(body);
                    match &result {
                        EvalResult::Value(_) => {}
                        EvalResult::Continue { label: ref tgt }
                            if Self::targets_this_loop(tgt, label) => {}
                        EvalResult::Break {
                            label: ref tgt,
                            value,
                        } if Self::targets_this_loop(tgt, label) => {
                            return EvalResult::Value(value.clone().unwrap_or(Value::Unit));
                        }
                        _ => return result,
                    }
                }
                EvalResult::Error("maximum loop iterations exceeded".to_string())
            }

            Expr::For {
                label,
                pattern,
                iter,
                body,
            } => {
                let iter_val = match self.eval(iter) {
                    EvalResult::Value(v) => v,
                    other => return other,
                };
                let elements_with_hints = match self.for_loop_elements_with_hints(iter, &iter_val) {
                    Ok(elems) => elems,
                    Err(err) => return EvalResult::Error(err.to_string()),
                };

                for (i, (elem, elem_hint)) in elements_with_hints.into_iter().enumerate() {
                    if i >= MAX_LOOP_ITERATIONS {
                        return EvalResult::Error("maximum loop iterations exceeded".to_string());
                    }
                    self.push_scope();
                    if let Some(bindings) =
                        self.collect_typed_pattern_bindings(pattern, &elem, elem_hint.as_ref())
                    {
                        self.apply_bindings(bindings);
                    }
                    let result = self.eval(body);
                    match &result {
                        EvalResult::Value(_) => {}
                        EvalResult::Continue { label: ref tgt }
                            if Self::targets_this_loop(tgt, label) => {}
                        EvalResult::Break {
                            label: ref tgt,
                            value,
                        } if Self::targets_this_loop(tgt, label) => {
                            let v = value.clone().unwrap_or(Value::Unit);
                            self.pop_scope();
                            return EvalResult::Value(v);
                        }
                        _ => {
                            self.pop_scope_for_eval_result(&result);
                            return result;
                        }
                    }
                    self.pop_scope();
                }
                EvalResult::Value(Value::Unit)
            }

            Expr::Unsafe { block } => {
                // Enter unsafe context
                let was_unsafe = self.ctx.enter_unsafe();
                // Evaluate the block
                let result = self.eval(block);
                // Restore previous context
                self.ctx.exit_unsafe(was_unsafe);
                result
            }

            Expr::RawDeref(ptr_expr) => {
                // Raw pointer dereference requires unsafe context
                if let Err(e) = self.ctx.require_unsafe("dereference of raw pointer") {
                    return EvalResult::Error(e.to_string());
                }
                // Evaluate the pointer expression
                let ptr_val = match self.eval(ptr_expr) {
                    EvalResult::Value(v) => v,
                    other => return other,
                };
                if self.aliasing_checks {
                    if let Some(place) = self.tracked_pointer_place(&ptr_val) {
                        if let Some(tag) = self.tracked_pointer_tag(&ptr_val) {
                            if let Err(err) =
                                self.ctx
                                    .ownership
                                    .access_place(&place, tag, AccessKind::Read)
                            {
                                return EvalResult::Error(format!(
                                    "stacked borrows: raw deref read rejected: {err}"
                                ));
                            }
                        }
                    }
                }

                if let Some(place) = self.tracked_pointer_place(&ptr_val) {
                    return match self.read_tracked_place_value(&place) {
                        Ok(value) => EvalResult::Value(value),
                        Err(err) => EvalResult::Error(format!("raw deref failed: {err}")),
                    };
                }

                match ptr_val {
                    Value::RefCellRef { cell_id, .. } | Value::RefCellRefMut { cell_id, .. } => {
                        match self.read_interior_cell_value(cell_id) {
                            Ok(value) => EvalResult::Value(value),
                            Err(err) => EvalResult::Error(err.to_string()),
                        }
                    }
                    Value::MutexGuard { lock_id, .. }
                    | Value::RwLockReadGuard { lock_id, .. }
                    | Value::RwLockWriteGuard { lock_id, .. } => {
                        match self.read_interior_cell_value(lock_id) {
                            Ok(value) => EvalResult::Value(value),
                            Err(err) => EvalResult::Error(err.to_string()),
                        }
                    }
                    Value::RawPtr { addr, .. } => match self.ctx.memory.read_u64(addr) {
                        Ok(value) => EvalResult::Value(Value::u64(value)),
                        Err(err) => EvalResult::Error(format!("deref failed: {err}")),
                    },
                    _ => EvalResult::Error("expected raw pointer for dereference".to_string()),
                }
            }

            Expr::UnionInit { name, field } => {
                // Evaluate the field value
                let (field_name, field_expr) = field;
                let field_val = match self.eval(field_expr) {
                    EvalResult::Value(v) => v,
                    other => return other,
                };
                // Creating a union is safe (only reading requires unsafe)
                EvalResult::Value(Value::Union {
                    name: name.clone(),
                    active_field: field_name.clone(),
                    value: Box::new(field_val),
                })
            }

            Expr::UnionFieldAccess { union_expr, field } => {
                // Union field access requires unsafe context
                if let Err(e) = self.ctx.require_unsafe("union field access") {
                    return EvalResult::Error(e.to_string());
                }
                // Evaluate the union expression
                let union_val = match self.eval(union_expr) {
                    EvalResult::Value(v) => v,
                    other => return other,
                };
                match union_val {
                    Value::Union {
                        active_field,
                        value,
                        ..
                    } => {
                        if &active_field == field {
                            // Reading the same field that was written - safe
                            EvalResult::Value((*value).clone())
                        } else {
                            // Reading a different field - this is where transmute happens
                            // For now, return an error about potential UB
                            EvalResult::Error(format!(
                                "reading union field '{}' but '{}' was the last written field - potential UB",
                                field, active_field
                            ))
                        }
                    }
                    _ => EvalResult::Error("expected union value for field access".to_string()),
                }
            }

            Expr::Panic { message } => {
                // Evaluate the message expression (typically a string literal)
                let msg_val = match self.eval(message) {
                    EvalResult::Value(v) => v,
                    EvalResult::Panic(p) => return EvalResult::Panic(p),
                    other => return other,
                };
                // Convert value to string for panic message
                // Note: Rust semantics crate doesn't have a dedicated String type,
                // so we use the debug representation for any value
                let msg_str = format!("{:?}", msg_val);
                // Return Panic result (abort semantics - immediate termination)
                EvalResult::Panic(msg_str)
            }

            Expr::Async { body, .. } => {
                // An async block creates a Future value wrapping the unevaluated body.
                // The body is evaluated lazily when `.await`ed.
                EvalResult::Value(Value::Future {
                    body: OpaqueExpr(Box::new((**body).clone())),
                })
            }

            Expr::Await { base } => {
                // Evaluate the base expression to get a Future value
                let future_val = match self.eval(base) {
                    EvalResult::Value(v) => v,
                    other => return other,
                };
                match future_val {
                    Value::Future { body } => {
                        // Drive the future to completion synchronously.
                        // In the verification model there is no concurrency —
                        // `.await` simply evaluates the captured body expression.
                        self.eval(&body.0)
                    }
                    _ => EvalResult::Error("`.await` applied to non-future value".to_string()),
                }
            }
            Expr::InlineAsm(asm) => self.eval_inline_asm(asm),
        }
    }

    fn lookup_enum_discriminant(&self, enum_name: &str, variant_name: &str) -> Option<i128> {
        let type_def = self.ctx.get_type(enum_name)?;
        if let crate::stmt::TypeDef::Enum { variants, .. } = type_def {
            let has_any_discriminant = variants.iter().any(|v| v.discriminant.is_some());
            if !has_any_discriminant {
                return None;
            }
            let mut next_disc: i128 = 0;
            for v in variants {
                let disc = v.discriminant.unwrap_or(next_disc);
                if v.name == variant_name {
                    return Some(disc);
                }
                next_disc = disc + 1;
            }
        }
        None
    }

    fn tuple_enum_variant_arity(&self, name: &str) -> Option<(String, String, usize)> {
        match name {
            "Option::Some" => return Some(("Option".to_string(), "Some".to_string(), 1)),
            "Result::Ok" => return Some(("Result".to_string(), "Ok".to_string(), 1)),
            "Result::Err" => return Some(("Result".to_string(), "Err".to_string(), 1)),
            _ => {}
        }
        let (enum_name, variant_name) = name.rsplit_once("::")?;
        let type_def = self.ctx.get_type(enum_name)?;
        let crate::stmt::TypeDef::Enum { variants, .. } = type_def else {
            return None;
        };
        let variant = variants.iter().find(|v| v.name == variant_name)?;
        let crate::stmt::EnumVariantType::Tuple(fields) = &variant.payload else {
            return None;
        };
        Some((
            enum_name.to_string(),
            variant_name.to_string(),
            fields.len(),
        ))
    }

    fn try_call_tuple_enum_variant_constructor(
        &self,
        name: &str,
        args: &[Value],
    ) -> Option<EvalResult> {
        let (enum_name, variant_name, field_count) = self.tuple_enum_variant_arity(name)?;
        if args.len() != field_count {
            return Some(EvalResult::Error(format!(
                "enum variant constructor {name} expects {field_count} args, got {}",
                args.len()
            )));
        }
        Some(EvalResult::Value(Value::Enum {
            name: enum_name,
            variant: variant_name,
            payload: Box::new(EnumPayload::Tuple(args.to_vec())),
        }))
    }

    #[must_use]
    fn substitute_trait_default_body_item(
        item: &Item,
        concrete_self_ty: &RustType,
        trait_name: &str,
    ) -> Item {
        match item {
            Item::Fn {
                name,
                params,
                ret,
                body,
                is_unsafe,
                is_async,
                type_params,
            } => Item::Fn {
                name: name.clone(),
                params: params.clone(),
                ret: ret.clone(),
                body: Self::substitute_trait_default_body_expr(body, concrete_self_ty, trait_name),
                is_unsafe: *is_unsafe,
                is_async: *is_async,
                type_params: type_params.clone(),
            },
            Item::Impl {
                self_ty,
                trait_name: impl_trait_name,
                items,
                type_params,
                const_params,
            } => Item::Impl {
                self_ty: self_ty.clone(),
                trait_name: impl_trait_name.clone(),
                items: items
                    .iter()
                    .map(|item| {
                        Self::substitute_trait_default_body_item(item, concrete_self_ty, trait_name)
                    })
                    .collect(),
                type_params: type_params.clone(),
                const_params: const_params.clone(),
            },
            Item::Const { name, ty, value } => Item::Const {
                name: name.clone(),
                ty: ty.clone(),
                value: Self::substitute_trait_default_body_expr(
                    value,
                    concrete_self_ty,
                    trait_name,
                ),
            },
            Item::Static {
                name,
                ty,
                mutable,
                value,
            } => Item::Static {
                name: name.clone(),
                ty: ty.clone(),
                mutable: *mutable,
                value: Self::substitute_trait_default_body_expr(
                    value,
                    concrete_self_ty,
                    trait_name,
                ),
            },
            _ => item.clone(),
        }
    }

    /// Evaluate a match expression
    fn eval_match(
        &mut self,
        scrutinee: &Value,
        scrutinee_hint: Option<&RustType>,
        arms: &[MatchArm],
    ) -> EvalResult {
        for arm in arms {
            if let Some(bindings) =
                self.collect_typed_pattern_bindings(&arm.pattern, scrutinee, scrutinee_hint)
            {
                // Check guard if present
                if let Some(guard) = &arm.guard {
                    self.push_scope();
                    self.apply_bindings(bindings.clone());
                    let guard_result = self.eval(guard);
                    self.pop_scope_for_eval_result(&guard_result);

                    match guard_result {
                        EvalResult::Value(Value::Bool(true)) => {}
                        EvalResult::Value(Value::Bool(false)) => continue,
                        EvalResult::Value(_) => {
                            return EvalResult::Error("match guard must be boolean".to_string());
                        }
                        other => return other,
                    }
                }

                // Execute arm body
                self.push_scope();
                self.apply_bindings(bindings);
                let result = self.eval(&arm.body);
                self.pop_scope_for_eval_result(&result);
                return result;
            }
        }
        EvalResult::Error("non-exhaustive match".to_string())
    }

    /// Execute a statement
    pub fn exec_stmt(&mut self, stmt: &Stmt) -> StmtResult {
        match stmt {
            Stmt::Let {
                pattern,
                ty,
                init,
                else_block,
            } => {
                let init_val = match init {
                    Some(e) => match self.eval(e) {
                        EvalResult::Value(v) => v,
                        EvalResult::Return(v) => return StmtResult::Return(v),
                        EvalResult::Break { label, value } => {
                            return StmtResult::Break { label, value }
                        }
                        EvalResult::Continue { label } => return StmtResult::Continue { label },
                        EvalResult::Panic(msg) => return StmtResult::Panic(msg),
                        EvalResult::Error(e) => return StmtResult::Error(e),
                    },
                    None => Value::Uninit,
                };

                // Coerce init value to declared type when annotation present.
                let init_val = match ty {
                    Some(target_ty) => self
                        .coerce_runtime_value(&init_val, target_ty)
                        .unwrap_or(init_val),
                    None => init_val,
                };

                if let Pattern::Binding {
                    name,
                    subpattern: None,
                    ..
                } = pattern
                {
                    let drop_ty = ty
                        .clone()
                        .or_else(|| {
                            init.as_deref()
                                .and_then(|expr| self.drop_type_hint_for_value(expr, &init_val))
                        })
                        .unwrap_or_else(|| init_val.get_type());
                    self.bind_with_drop_type(name.clone(), init_val, drop_ty);
                    return StmtResult::Ok;
                }

                let drop_type_hint = ty.clone().or_else(|| {
                    init.as_deref()
                        .and_then(|expr| self.drop_type_hint_for_value(expr, &init_val))
                });
                match self.collect_typed_pattern_bindings(
                    pattern,
                    &init_val,
                    drop_type_hint.as_ref(),
                ) {
                    Some(bindings) => {
                        self.apply_bindings(bindings);
                        StmtResult::Ok
                    }
                    None => match else_block {
                        Some(block) => match self.eval(block) {
                            EvalResult::Return(v) => StmtResult::Return(v),
                            EvalResult::Break { label, value } => {
                                StmtResult::Break { label, value }
                            }
                            EvalResult::Continue { label } => StmtResult::Continue { label },
                            EvalResult::Panic(msg) => StmtResult::Panic(msg),
                            EvalResult::Error(e) => StmtResult::Error(e),
                            EvalResult::Value(_) => StmtResult::Error(
                                "let-else block must diverge (return, break, continue, or panic)"
                                    .to_string(),
                            ),
                        },
                        None => StmtResult::Error("pattern match failed in let".to_string()),
                    },
                }
            }

            Stmt::Expr(e) => match self.eval(e) {
                EvalResult::Value(_) => StmtResult::Ok,
                EvalResult::Return(v) => StmtResult::Return(v),
                EvalResult::Break { label, value } => StmtResult::Break { label, value },
                EvalResult::Continue { label } => StmtResult::Continue { label },
                EvalResult::Panic(msg) => StmtResult::Panic(msg),
                EvalResult::Error(e) => StmtResult::Error(e),
            },

            Stmt::Item(_) => StmtResult::Ok,
        }
    }

    /// Process an item declaration
    fn process_item(&mut self, item: &Item) {
        match item {
            Item::Fn {
                name,
                params,
                ret,
                body,
                is_unsafe,
                is_async,
                type_params,
                ..
            } => {
                self.ctx.register_function(FunctionDef {
                    name: name.clone(),
                    params: params.clone(),
                    ret_ty: ret.clone(),
                    body: body.clone(),
                    is_unsafe: *is_unsafe,
                    is_async: *is_async,
                    type_params: type_params.clone(),
                });
                // Also bind function pointer in scope
                self.bind(name.clone(), Value::FnPtr { name: name.clone() });
            }
            Item::Struct {
                name,
                fields,
                type_params,
                const_params,
            } => {
                self.ctx.register_type(crate::stmt::TypeDef::Struct {
                    name: name.clone(),
                    fields: fields.clone(),
                    type_params: type_params.clone(),
                    const_params: const_params.clone(),
                });
            }
            Item::Enum {
                name,
                variants,
                type_params,
                const_params,
            } => {
                let variant_defs: Vec<_> = variants
                    .iter()
                    .map(|variant| match variant {
                        crate::types::EnumVariant::Unit { name, discriminant } => {
                            crate::stmt::EnumVariantDef {
                                name: name.clone(),
                                payload: crate::stmt::EnumVariantType::Unit,
                                discriminant: *discriminant,
                            }
                        }
                        crate::types::EnumVariant::Tuple {
                            name,
                            fields,
                            discriminant,
                        } => crate::stmt::EnumVariantDef {
                            name: name.clone(),
                            payload: crate::stmt::EnumVariantType::Tuple(fields.clone()),
                            discriminant: *discriminant,
                        },
                        crate::types::EnumVariant::Struct {
                            name,
                            fields,
                            discriminant,
                        } => crate::stmt::EnumVariantDef {
                            name: name.clone(),
                            payload: crate::stmt::EnumVariantType::Struct(
                                fields
                                    .iter()
                                    .map(|field| (field.name.clone(), field.ty.clone()))
                                    .collect(),
                            ),
                            discriminant: *discriminant,
                        },
                    })
                    .collect();
                self.ctx.register_type(crate::stmt::TypeDef::Enum {
                    name: name.clone(),
                    variants: variant_defs,
                    type_params: type_params.clone(),
                    const_params: const_params.clone(),
                });
            }
            Item::TraitDef(def) => {
                self.ctx.register_full_trait_def(def.clone());
            }
            Item::ImplAssociatedType { .. } => {}
            Item::Union {
                name,
                fields,
                const_params,
                ..
            } => {
                self.ctx.register_type(crate::stmt::TypeDef::Union {
                    name: name.clone(),
                    fields: fields.clone(),
                    const_params: const_params.clone(),
                });
            }
            Item::Impl {
                self_ty,
                trait_name,
                items,
                type_params: impl_type_params,
                const_params: _impl_const_params,
                ..
            } => {
                // Register trait implementation if this is a trait impl
                if let Some(ref trait_name) = trait_name {
                    self.ctx
                        .register_trait_impl(trait_name.clone(), self_ty.clone());
                }
                // Process items in the impl block
                let inherent_type_name = trait_name.is_none().then(|| self_ty.name()).flatten();
                let trait_impl_type_name = trait_name
                    .as_ref()
                    .map(|_| self_ty.name().unwrap_or_else(|| "anonymous".to_string()));
                let mut explicit_method_names: Vec<String> = Vec::new();
                for sub_item in items {
                    match &sub_item {
                        Item::Fn {
                            name,
                            params,
                            ret,
                            body,
                            is_unsafe,
                            is_async,
                            type_params: method_type_params,
                            ..
                        } => {
                            explicit_method_names.push(name.clone());
                            let has_self_param = params
                                .first()
                                .is_some_and(|(param_name, _)| param_name == "self");
                            if inherent_type_name.is_some() && has_self_param {
                                self.ctx.register_function(FunctionDef {
                                    name: name.clone(),
                                    params: params.clone(),
                                    ret_ty: ret.clone(),
                                    body: body.clone(),
                                    is_unsafe: *is_unsafe,
                                    is_async: *is_async,
                                    type_params: method_type_params.clone(),
                                });
                                self.ctx.register_function_context_type_params(
                                    name.clone(),
                                    impl_type_params.clone(),
                                );
                                self.bind(name.clone(), Value::FnPtr { name: name.clone() });
                            }
                            if let Some(type_name) = &inherent_type_name {
                                let qualified_name = format!("{type_name}::{name}");
                                self.ctx.register_function(FunctionDef {
                                    name: qualified_name.clone(),
                                    params: params.clone(),
                                    ret_ty: ret.clone(),
                                    body: body.clone(),
                                    is_unsafe: *is_unsafe,
                                    is_async: *is_async,
                                    type_params: method_type_params.clone(),
                                });
                                self.ctx.register_function_context_type_params(
                                    qualified_name,
                                    impl_type_params.clone(),
                                );
                            }
                            if let (Some(trait_name), Some(type_name)) =
                                (&trait_name, &trait_impl_type_name)
                            {
                                let qualified_name =
                                    Self::trait_impl_function_name(type_name, trait_name, name);
                                self.ctx.register_function(FunctionDef {
                                    name: qualified_name.clone(),
                                    params: params.clone(),
                                    ret_ty: ret.clone(),
                                    body: body.clone(),
                                    is_unsafe: *is_unsafe,
                                    is_async: *is_async,
                                    type_params: method_type_params.clone(),
                                });
                                self.ctx.register_function_context_type_params(
                                    qualified_name.clone(),
                                    impl_type_params.clone(),
                                );
                                self.ctx.add_impl_method(
                                    trait_name,
                                    type_name,
                                    name.clone(),
                                    qualified_name,
                                );
                            }
                        }
                        Item::ImplAssociatedType {
                            name,
                            ty,
                            generic_params,
                            where_clause,
                        } => {
                            if let (Some(trait_name), Some(type_name)) =
                                (&trait_name, &trait_impl_type_name)
                            {
                                self.ctx.add_impl_associated_type(
                                    trait_name,
                                    type_name,
                                    name.clone(),
                                    generic_params.clone(),
                                    where_clause.clone(),
                                    ty.clone(),
                                );
                            }
                        }
                        Item::Const { .. } | Item::Static { .. } => {}
                        _ => self.process_item(sub_item),
                    }
                }

                // Register default method bodies for trait methods not explicitly provided
                if let Some(ref trait_name) = trait_name {
                    if let Some(trait_def) = self.ctx.get_trait_def(trait_name).cloned() {
                        for (method_name, default_body) in &trait_def.default_bodies {
                            if !explicit_method_names.contains(method_name) {
                                if let Some(type_name) = &trait_impl_type_name {
                                    let qualified_name = Self::trait_impl_function_name(
                                        type_name,
                                        trait_name,
                                        method_name,
                                    );
                                    // Substitute `Self` placeholders with the
                                    // concrete implementing type so that
                                    // signature validation and type metadata
                                    // reflect the actual types.
                                    let params = default_body
                                        .params
                                        .iter()
                                        .map(|(name, ty)| {
                                            (name.clone(), ty.substitute_self_type(self_ty))
                                        })
                                        .collect();
                                    let ret_ty = default_body.ret_ty.substitute_self_type(self_ty);
                                    let body = Self::substitute_trait_default_body_expr(
                                        &default_body.body,
                                        self_ty,
                                        trait_name,
                                    );
                                    self.ctx.register_function(FunctionDef {
                                        name: qualified_name.clone(),
                                        params,
                                        ret_ty,
                                        body,
                                        is_unsafe: false,
                                        is_async: false,
                                        type_params: vec![],
                                    });
                                    self.ctx.register_function_context_type_params(
                                        qualified_name.clone(),
                                        impl_type_params.clone(),
                                    );
                                    self.ctx.add_impl_method(
                                        trait_name,
                                        type_name,
                                        method_name.clone(),
                                        qualified_name,
                                    );
                                }
                            }
                        }
                    }
                }
            }
            Item::Const { name, ty, value }
            | Item::Static {
                name,
                ty,
                mutable: _,
                value,
            } => {
                if let EvalResult::Value(v) = self.eval(value) {
                    self.bind_with_drop_type(name.clone(), v, ty.clone());
                }
            }
            // Type aliases are resolved structurally during source ingestion and
            // carry no runtime behavior, so processing them is a no-op.
            Item::TypeAlias { .. } => {}
            Item::GlobalAsm(_) => {}
        }
    }

    /// Run a program (list of items followed by optional main expression)
    pub fn run_program(&mut self, items: &[Item], main_expr: Option<&Expr>) -> EvalResult {
        if let Err(err) = self.hoist_scope_items(items.iter()) {
            return EvalResult::Error(err.to_string());
        }

        // If there's a main function and no explicit main expression, call main
        if main_expr.is_none() && self.ctx.get_function("main").is_some() {
            return self.call_function("main", vec![], &[]);
        }

        // Evaluate main expression if provided
        match main_expr {
            Some(e) => self.eval(e),
            None => EvalResult::Value(Value::Unit),
        }
    }
}

impl Default for Interpreter {
    fn default() -> Self {
        Self::new()
    }
}

impl MemoryModel for Interpreter {
    type Error = RustSemError;

    fn allocate(&mut self, size: usize) -> Result<SharedAddress, Self::Error> {
        let place = self.fresh_place();
        self.insert_shared_memory_binding(place.clone(), size);
        self.shared_memory_roots.insert(place.clone());
        let raw = match place {
            Place::Local(idx) => u64::from(idx) + 1,
            _ => unreachable!("shared memory allocations always use fresh local places"),
        };
        let addr = SharedAddress::new(raw);
        self.shared_memory_addr_places.insert(addr, place);
        Ok(addr)
    }

    fn read(&self, addr: SharedAddress, offset: usize) -> Result<MemoryValue, Self::Error> {
        let place = self
            .shared_memory_addr_places
            .get(&addr)
            .ok_or_else(|| RustSemError::Eval(format!("invalid shared memory address {addr:?}")))?;
        let value = self
            .binding_value_for_place(place)
            .ok_or_else(|| RustSemError::Eval(format!("freed shared memory address {addr:?}")))?;
        let Value::Array(bytes) = value else {
            return Err(RustSemError::Eval(
                "shared memory allocation is not byte-addressable".to_string(),
            ));
        };
        match bytes.get(offset) {
            Some(Value::Uint {
                value,
                ty: UintType::U8,
            }) => Ok(MemoryValue::new(*value as u8)),
            Some(Value::Uninit) => Ok(MemoryValue::ZERO),
            Some(other) => Err(RustSemError::Eval(format!(
                "shared memory byte had non-byte value {other:?}"
            ))),
            None => Err(RustSemError::IndexOutOfBounds { index: offset }),
        }
    }

    fn write(
        &mut self,
        addr: SharedAddress,
        offset: usize,
        value: MemoryValue,
    ) -> Result<(), Self::Error> {
        let place = self
            .shared_memory_addr_places
            .get(&addr)
            .cloned()
            .ok_or_else(|| RustSemError::Eval(format!("invalid shared memory address {addr:?}")))?;
        let current = self
            .binding_value_for_place(&place)
            .cloned()
            .ok_or_else(|| RustSemError::Eval(format!("freed shared memory address {addr:?}")))?;
        let Value::Array(mut bytes) = current else {
            return Err(RustSemError::Eval(
                "shared memory allocation is not byte-addressable".to_string(),
            ));
        };
        if offset >= bytes.len() {
            return Err(RustSemError::IndexOutOfBounds { index: offset });
        }
        bytes[offset] = Value::u8(value.get());
        self.replace_binding_value_for_place(&place, Value::Array(bytes));
        Ok(())
    }

    fn free(&mut self, addr: SharedAddress) -> Result<(), Self::Error> {
        let place = self
            .shared_memory_addr_places
            .remove(&addr)
            .ok_or_else(|| RustSemError::Eval(format!("invalid shared memory address {addr:?}")))?;
        self.shared_memory_roots.remove(&place);
        if self.remove_binding_for_place(&place) {
            Ok(())
        } else {
            Err(RustSemError::Eval(format!(
                "freed shared memory address {addr:?}"
            )))
        }
    }

    fn is_valid(&self, addr: SharedAddress) -> bool {
        self.shared_memory_addr_places
            .get(&addr)
            .is_some_and(|place| {
                self.shared_memory_roots.contains(place)
                    && self.binding_value_for_place(place).is_some()
            })
    }
}

#[cfg(test)]
mod drop_generic_tests;
#[cfg(test)]
mod drop_order_enum_tests;
#[cfg(test)]
mod drop_order_tests;
#[cfg(test)]
mod hashmap_iter_tests;
#[cfg(test)]
mod memory_model_tests;
#[cfg(test)]
mod tests;
#[cfg(test)]
mod tests_atomics;
#[cfg(test)]
mod tests_dst;
#[cfg(test)]
mod tests_interior_mutability;
#[cfg(test)]
mod tests_support;

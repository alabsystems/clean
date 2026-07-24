// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Borrow Inference for Reference Counting
//!
//! Determines which function parameters can be borrowed (not ref-counted)
//! versus owned (must be inc/dec'd). Based on "Counting Immutable Beans"
//! (Ullrich & de Moura, IFL 2020).
//!
//! # Algorithm Overview
//!
//! 1. Initialize all reference-type parameters as borrowed
//! 2. Collect variables that MUST be owned (reset, consumed by owned params)
//! 3. Iterate to fixpoint marking params owned when needed
//! 4. Preserve tail calls by promoting borrowed→owned when needed
//!
//! # Ownership Model
//!
//! - **Owned (O)**: Function is responsible for consuming one RC token
//! - **Borrowed (B)**: Does not update reference count
//!
//! Part of #963 - Compiler IR infrastructure.

use crate::lcnf::{Alt, Arg, Code, Decl, DeclValue, LetValue};
use clean_kernel::{FVarId, Name};
use std::collections::{HashMap, HashSet};

/// Ownership status of a parameter.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub enum Ownership {
    /// Parameter is owned - caller transfers ownership.
    Owned,
    /// Parameter is borrowed - caller retains ownership.
    #[default]
    Borrowed,
}

/// Borrow annotations for a function.
#[derive(Clone, Debug, Default)]
pub struct FnBorrow {
    /// Ownership for each parameter (by index).
    pub params: Vec<Ownership>,
}

impl FnBorrow {
    /// Create with all parameters borrowed.
    pub fn all_borrowed(n: usize) -> Self {
        Self {
            params: vec![Ownership::Borrowed; n],
        }
    }

    /// Mark parameter at index as owned. Returns true if changed.
    pub fn mark_owned(&mut self, idx: usize) -> bool {
        if idx < self.params.len() && self.params[idx] == Ownership::Borrowed {
            self.params[idx] = Ownership::Owned;
            true
        } else {
            false
        }
    }
}

/// Borrow map for all functions in a compilation unit.
#[derive(Clone, Debug, Default)]
pub struct BorrowMap {
    /// Maps function name to its borrow annotations.
    fns: HashMap<Name, FnBorrow>,
}

impl BorrowMap {
    /// Create an empty borrow map.
    pub fn new() -> Self {
        Self::default()
    }

    /// Get borrow info for a function.
    pub fn get(&self, name: &Name) -> Option<&FnBorrow> {
        self.fns.get(name)
    }

    /// Insert or update borrow info for a function.
    pub fn insert(&mut self, name: Name, borrow: FnBorrow) {
        self.fns.insert(name, borrow);
    }

    /// Mark a parameter as owned. Returns true if changed.
    pub fn mark_owned(&mut self, name: &Name, idx: usize) -> bool {
        if let Some(borrow) = self.fns.get_mut(name) {
            borrow.mark_owned(idx)
        } else {
            false
        }
    }
}

/// Infer borrow annotations for a list of declarations.
///
/// This implements fixpoint iteration until annotations stabilize.
///
/// # Termination Guarantee
///
/// The algorithm is guaranteed to terminate because:
/// 1. **Monotonicity**: Ownership status only transitions `Borrowed → Owned`, never reverses.
///    See `mark_owned()` which only changes `Borrowed` to `Owned`.
/// 2. **Finite state space**: Each parameter has at most 2 states. With N total parameters
///    across all declarations, the maximum number of transitions is N.
/// 3. **Progress**: Each iteration either makes at least one transition (changing some
///    `Borrowed` → `Owned`) or terminates (changed == false).
///
/// Therefore, the loop terminates after at most N iterations, where N = Σ|params(d)|
/// for all declarations d. In practice, convergence is typically faster due to
/// limited ownership propagation chains.
///
/// # ENSURES
///
/// - All returned `FnBorrow` annotations are sound (no over-borrowing)
/// - Parameters marked `Borrowed` are guaranteed safe without RC operations
/// - Mutually recursive functions correctly propagate ownership through call cycles
pub fn infer_borrow(decls: &[Decl]) -> BorrowMap {
    let mut borrow_map = BorrowMap::new();

    // Phase 1: Initialize all reference params as borrowed
    for decl in decls {
        let n = decl.params.len();
        borrow_map.insert(decl.name.clone(), FnBorrow::all_borrowed(n));
    }

    // Phase 2: Fixpoint iteration
    loop {
        let mut changed = false;

        for decl in decls {
            if let DeclValue::Code(code) = &decl.body {
                // Collect variables that must be owned
                let mut owned_set = HashSet::new();
                collect_owned(code, &borrow_map, &mut owned_set);

                // Mark params owned if they appear in owned_set
                for (idx, param) in decl.params.iter().enumerate() {
                    if owned_set.contains(&param.fvar_id) && borrow_map.mark_owned(&decl.name, idx)
                    {
                        changed = true;
                    }
                }

                // Preserve tail calls: reverse direction (Lean 4 ownParamsUsingArgs).
                // For self-recursive tail calls, if the caller's argument is owned,
                // promote the callee's corresponding parameter to owned. Without this,
                // RC insertion would add `dec` after the tail call, breaking tail position.
                promote_tail_call_owned(
                    code,
                    &decl.name,
                    &owned_set,
                    &mut borrow_map,
                    &mut changed,
                );
            }
        }

        if !changed {
            break;
        }
    }

    borrow_map
}

/// Collect variables that MUST be owned in a function body.
///
/// A variable must be owned if:
/// - It's used in `reset x` (x must be owned to potentially mutate)
/// - It's passed as an owned argument to a function call
/// - It's stored in a constructor (transferred to new object)
/// - A projection from it is owned (ownership propagates backward)
fn collect_owned(code: &Code, borrow_map: &BorrowMap, owned_set: &mut HashSet<FVarId>) {
    match code {
        Code::Let(decl, body) => {
            // First recurse into body to find what's owned downstream
            collect_owned(body, borrow_map, owned_set);

            match &decl.value {
                // Projection: if result is owned, source must be owned
                LetValue::Proj { structure, .. } => {
                    if owned_set.contains(&decl.fvar_id) {
                        owned_set.insert(*structure);
                    }
                }

                // Constant application: mark args owned per callee's borrow info
                LetValue::Const { name, args, .. } => {
                    if let Some(fn_borrow) = borrow_map.get(name) {
                        for (idx, arg) in args.iter().enumerate() {
                            if let Arg::FVar(fvar) = arg {
                                if idx < fn_borrow.params.len()
                                    && fn_borrow.params[idx] == Ownership::Owned
                                {
                                    owned_set.insert(*fvar);
                                }
                            }
                        }
                    } else {
                        // Unknown function - be conservative, all args owned
                        for arg in args {
                            if let Arg::FVar(fvar) = arg {
                                owned_set.insert(*fvar);
                            }
                        }
                    }
                }

                // FVar application (higher-order): all args must be owned
                // Higher-order calls can't be analyzed statically
                LetValue::FVar { fvar, args } => {
                    // The function itself must be owned (consumed by call)
                    owned_set.insert(*fvar);
                    // All arguments must be owned
                    for arg in args {
                        if let Arg::FVar(fvar) = arg {
                            owned_set.insert(*fvar);
                        }
                    }
                }

                // Constructor: all args are stored, must be owned
                LetValue::Ctor { args, .. } => {
                    for arg in args {
                        if let Arg::FVar(fvar) = arg {
                            owned_set.insert(*fvar);
                        }
                    }
                }

                // Reuse: slot is consumed, args are stored (must be owned)
                LetValue::Reuse { slot, args, .. } => {
                    owned_set.insert(*slot);
                    for arg in args {
                        if let Arg::FVar(fvar) = arg {
                            owned_set.insert(*fvar);
                        }
                    }
                }

                // Literals and erased don't affect ownership
                LetValue::Lit(_) | LetValue::Erased => {}
            }
        }

        Code::Fun(fun_decl, body) | Code::JoinPoint(fun_decl, body) => {
            // Process nested function body
            collect_owned(&fun_decl.body, borrow_map, owned_set);
            // Continue to outer body
            collect_owned(body, borrow_map, owned_set);
        }

        Code::Cases(cases) => {
            // Process each alternative
            for alt in &cases.alts {
                let alt_body = match alt {
                    Alt::Ctor { body, .. } => body,
                    Alt::Default(body) => body,
                };
                collect_owned(alt_body, borrow_map, owned_set);
            }
        }

        // Terminals don't add owned requirements
        Code::Jmp { .. } | Code::Return(_) | Code::Unreachable(_) => {}
    }
}

/// Promote callee params to owned when the caller passes owned args at
/// self-recursive tail call sites (Lean 4 `ownParamsUsingArgs`).
///
/// For a self-recursive tail call `f(args)` where the result is returned
/// directly: if arg[i] is owned in the caller, mark f's param[i] as owned.
/// Without this, RC insertion would add `dec arg[i]` after the tail call,
/// breaking tail position.
///
/// Ref: Lean 4 `InferBorrow.lean:273-284` (`preserveTailCall`).
fn promote_tail_call_owned(
    code: &Code,
    fn_name: &Name,
    owned_set: &HashSet<FVarId>,
    borrow_map: &mut BorrowMap,
    changed: &mut bool,
) {
    match code {
        Code::Let(let_decl, body) => {
            if let LetValue::Const { name, args, .. } = &let_decl.value {
                // Only self-recursive tail calls (Lean 4: currDecl == f)
                if name == fn_name && is_tail_call(body, let_decl.fvar_id) {
                    // Reverse direction: if arg is owned, callee's param must be owned
                    for (idx, arg) in args.iter().enumerate() {
                        if let Arg::FVar(fvar) = arg {
                            if owned_set.contains(fvar) && borrow_map.mark_owned(name, idx) {
                                *changed = true;
                            }
                        }
                    }
                }
            }
            promote_tail_call_owned(body, fn_name, owned_set, borrow_map, changed);
        }

        Code::Fun(_, body) => {
            // Don't descend into nested function bodies (they have their
            // own borrow analysis). Continue through the outer body only.
            promote_tail_call_owned(body, fn_name, owned_set, borrow_map, changed);
        }

        Code::JoinPoint(fun_decl, body) => {
            // JoinPoints are part of the current function — recurse into
            // both the JP body and the continuation. A tail call inside a
            // JP is still a tail call of the outer function.
            // (Lean 4 collectCode:332-337 recurses into both decl.value and k)
            promote_tail_call_owned(&fun_decl.body, fn_name, owned_set, borrow_map, changed);
            promote_tail_call_owned(body, fn_name, owned_set, borrow_map, changed);
        }

        Code::Cases(cases) => {
            for alt in &cases.alts {
                let alt_body = match alt {
                    Alt::Ctor { body, .. } => body,
                    Alt::Default(body) => body,
                };
                promote_tail_call_owned(alt_body, fn_name, owned_set, borrow_map, changed);
            }
        }

        Code::Jmp { .. } | Code::Return(_) | Code::Unreachable(_) => {}
    }
}

/// Check if a let-binding's result is used in tail position.
fn is_tail_call(body: &Code, result_fvar: FVarId) -> bool {
    match body {
        Code::Return(fvar) => *fvar == result_fvar,
        _ => false,
    }
}

/// Infer borrow annotations for a single declaration.
///
/// Useful for testing or when processing declarations individually.
pub fn infer_borrow_single(decl: &Decl) -> FnBorrow {
    let map = infer_borrow(std::slice::from_ref(decl));
    map.get(&decl.name).cloned().unwrap_or_default()
}

#[cfg(test)]
mod tests;

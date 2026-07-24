// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Async/await expression lowering to VIR.
//!
//! Lowers `Expr::Async` and `Expr::Await` into VIR constructs:
//!
//! - `Expr::Async { body }` → separate `Body` for the async block code,
//!   packed as `Rvalue::Aggregate { kind: AggregateKind::Generator { def_id } }`.
//!
//! - `Expr::Await { base }` → evaluates the base (a future/generator), then
//!   emits a `Term::Call` that drives the future synchronously.
//!
//! ## Verification model
//!
//! For verification purposes there is no concurrency: `.await` synchronously
//! evaluates the future's body. This matches the interpreter's eager-await
//! semantics and is sound for single-threaded sequential verification.

use super::context::FunctionLoweringContext;
use super::VirLoweringError;
use crate::expr::{EnumVariantPayload, Expr, Stmt as SemStmt};
use crate::ownership::Place;
use crate::types::{Lifetime, Mutability, RustType};
use crate::vir::{AggregateKind, BorrowKind, Operand, RetagKind, Rvalue, Stmt as VirStmt, Term};
use std::collections::HashSet;

impl<'a> FunctionLoweringContext<'a> {
    /// Lower `Expr::Async { capture_by_value, body }` into a generator aggregate.
    ///
    /// Follows the same pattern as closure lowering:
    /// 1. Compute captures (free variables referenced in the body)
    /// 2. Lower the body as a separate `Body`
    /// 3. Emit a `Generator` aggregate at the construction site
    pub(super) fn lower_async_expr(
        &mut self,
        destination: Place,
        capture_by_value: bool,
        body: &Expr,
    ) -> Result<(), VirLoweringError> {
        let generator_id = self.next_generator_id();
        let def_id = format!("{}::{{async#{generator_id}}}", self.function_name);
        let destination_local = match &destination {
            Place::Local(local) => Some(*local),
            _ => None,
        };

        // Compute captures: collect variable names referenced in the body,
        // then filter to names that actually resolve in the enclosing scope.
        let mut var_names = HashSet::new();
        collect_expr_var_names(body, &mut var_names);

        let mut capture_operands = Vec::new();
        let mut capture_types = Vec::new();

        for name in &var_names {
            let Ok(local) = self.lookup_local(name) else {
                continue;
            };
            let Ok(local_ty) = self.local_ty(local) else {
                continue;
            };

            if capture_by_value {
                let operand = if local_ty.is_copy() {
                    Operand::Copy(Place::Local(local))
                } else {
                    Operand::Move(Place::Local(local))
                };
                capture_operands.push(operand);
                capture_types.push((name.clone(), local_ty, Mutability::Shared));
            } else {
                let borrow_kind = BorrowKind::Shared;
                let ref_ty = RustType::Reference {
                    lifetime: Lifetime::Anonymous(0),
                    mutability: Mutability::Shared,
                    inner: Box::new(local_ty.clone()),
                };
                let ref_local = self.alloc_local(None, ref_ty, Mutability::Shared);
                self.emit_ref_and_retag(
                    Place::Local(ref_local),
                    borrow_kind,
                    Place::Local(local),
                    RetagKind::Default,
                );
                capture_operands.push(Operand::Move(Place::Local(ref_local)));
                capture_types.push((name.clone(), local_ty, Mutability::Shared));
            }
        }

        // Build the generator body's parameter list from captures.
        // Captures use their original value types (same as closure lowering).
        let body_params: Vec<(String, RustType)> = capture_types
            .iter()
            .map(|(name, local_ty, _)| (name.clone(), local_ty.clone()))
            .collect();

        // Infer the output type of the async block body.
        let ret_ty = self.infer_closure_body_type(&body_params, body)?;
        let visible_symbols = self.visible_symbols();

        // Lower the async block body as a separate function.
        let (generator_body, nested_closures) = super::context::lower_function_with_closures(
            &def_id,
            &body_params,
            &ret_ty,
            body,
            &visible_symbols,
        )?;
        self.closure_bodies.push((def_id.clone(), generator_body));
        self.closure_bodies.extend(nested_closures);

        // Emit the generator aggregate at the construction site.
        self.emit(VirStmt::Assign {
            place: destination,
            rvalue: Rvalue::Aggregate {
                kind: AggregateKind::Generator {
                    def_id: def_id.clone(),
                },
                operands: capture_operands,
            },
        });
        if let Some(local) = destination_local {
            self.generator_def_ids.insert(local, def_id);
            self.remember_future_output(local, ret_ty);
        }

        Ok(())
    }

    /// Lower `Expr::Await { base }` by driving the future synchronously.
    ///
    /// Lowers the base expression, then emits a `Term::Call` that invokes
    /// the generator's body. This models the verification semantics where
    /// `.await` evaluates eagerly with no concurrency.
    pub(super) fn lower_await_expr(
        &mut self,
        destination: Place,
        base: &Expr,
    ) -> Result<(), VirLoweringError> {
        let base_ty = self.infer_expr_type(base)?;

        // Lower the base expression to get the future value.
        let future_local = self.alloc_local(None, base_ty, Mutability::Shared);
        self.lower_expr_into(Place::Local(future_local), base, false)?;

        if self.terminated {
            return Ok(());
        }

        let cont_block = self.new_block(Term::Unreachable);
        let unwind = self.call_unwind_action(&destination);
        self.current_block_mut().terminator = Term::Call {
            // Await the constructed future value, not the generator body fn
            // directly. This preserves captured state for async blocks and
            // async fns lowered to future-producing wrappers.
            func: Operand::Move(Place::Local(future_local)),
            args: vec![],
            destination,
            target: Some(cont_block),
            target_args: vec![],
            unwind,
        };
        self.switch_to_block(cont_block);

        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Free-variable collection for async block captures
// ---------------------------------------------------------------------------
// Mirrors `source::captures::collect_expr_var_names` but lives in the VIR
// lowering layer to avoid coupling between source parsing and VIR lowering.

fn collect_expr_var_names(expr: &Expr, names: &mut HashSet<String>) {
    match expr {
        Expr::Var { name, .. } => {
            names.insert(name.clone());
        }
        Expr::Literal(_) | Expr::Continue { .. } => {}
        // Single sub-expression variants
        Expr::UnOp { expr: sub, .. }
        | Expr::Cast { expr: sub, .. }
        | Expr::Deref(sub)
        | Expr::RawDeref(sub)
        | Expr::AddrOf { expr: sub, .. }
        | Expr::Field { base: sub, .. }
        | Expr::ArrayRepeat { value: sub, .. }
        | Expr::UnionFieldAccess {
            union_expr: sub, ..
        }
        | Expr::Closure { body: sub, .. }
        | Expr::Panic { message: sub }
        | Expr::Loop { body: sub, .. }
        | Expr::Unsafe { block: sub }
        | Expr::Await { base: sub }
        | Expr::Async { body: sub, .. } => collect_expr_var_names(sub, names),
        // Two sub-expression variants
        Expr::BinOp {
            left: a, right: b, ..
        }
        | Expr::Assign {
            target: a,
            value: b,
        }
        | Expr::AssignOp {
            target: a,
            value: b,
            ..
        }
        | Expr::Index { base: a, index: b }
        | Expr::While {
            condition: a,
            body: b,
            ..
        }
        | Expr::For {
            iter: a, body: b, ..
        } => {
            collect_expr_var_names(a, names);
            collect_expr_var_names(b, names);
        }
        Expr::Return(opt) | Expr::Break { value: opt, .. } => collect_opt(opt, names),
        Expr::Range { start, end, .. } => {
            collect_opt(start, names);
            collect_opt(end, names);
        }
        Expr::Call { func: e, args, .. }
        | Expr::MethodCall {
            receiver: e, args, ..
        } => {
            collect_expr_var_names(e, names);
            collect_slice(args, names);
        }
        Expr::Tuple(elems) | Expr::Array(elems) => collect_slice(elems, names),
        Expr::If {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_expr_var_names(condition, names);
            collect_expr_var_names(then_branch, names);
            collect_opt(else_branch, names);
        }
        Expr::Match { scrutinee, arms } => collect_match(scrutinee, arms, names),
        Expr::Block { stmts, expr } => collect_block(stmts, expr, names),
        Expr::Struct { fields, .. } => collect_named_fields(fields, names),
        Expr::UnionInit { field: (_, e), .. } => collect_expr_var_names(e, names),
        Expr::EnumVariant { payload, .. } => collect_payload(payload, names),
        Expr::InlineAsm(_) => {} // inline asm has no Rust-level variable captures
    }
}

fn collect_opt(opt: &Option<Box<Expr>>, names: &mut HashSet<String>) {
    if let Some(e) = opt {
        collect_expr_var_names(e, names);
    }
}

fn collect_slice(exprs: &[Expr], names: &mut HashSet<String>) {
    for e in exprs {
        collect_expr_var_names(e, names);
    }
}

fn collect_named_fields(fields: &[(String, Expr)], names: &mut HashSet<String>) {
    for (_, e) in fields {
        collect_expr_var_names(e, names);
    }
}

fn collect_match(scrutinee: &Expr, arms: &[crate::expr::MatchArm], names: &mut HashSet<String>) {
    collect_expr_var_names(scrutinee, names);
    for arm in arms {
        if let Some(guard) = &arm.guard {
            collect_expr_var_names(guard, names);
        }
        collect_expr_var_names(&arm.body, names);
    }
}

fn collect_block(stmts: &[SemStmt], expr: &Option<Box<Expr>>, names: &mut HashSet<String>) {
    for stmt in stmts {
        match stmt {
            SemStmt::Let {
                init, else_block, ..
            } => {
                collect_opt(init, names);
                collect_opt(else_block, names);
            }
            SemStmt::Expr(e) => collect_expr_var_names(e, names),
            SemStmt::Item(_) => {}
        }
    }
    collect_opt(expr, names);
}

fn collect_payload(payload: &EnumVariantPayload, names: &mut HashSet<String>) {
    match payload {
        EnumVariantPayload::Unit => {}
        EnumVariantPayload::Tuple(exprs) => collect_slice(exprs, names),
        EnumVariantPayload::Struct(fields) => collect_named_fields(fields, names),
    }
}

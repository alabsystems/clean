// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Straight-line semantic-AST to VIR lowering.

use super::loop_support::{CleanupLocal, LoopTarget};
use super::ops::{constant_from_value, lower_bin_op, lower_un_op};
use super::scoped_symbols::SymbolScope;
use super::{ProgramSymbols, VirLoweringError};
use crate::expr::Expr;
use crate::ownership::Place;
use crate::types::{Mutability, RustType};
use crate::vir::{
    BasicBlock, BasicBlockId, Body, LocalDecl, LocalId, Operand, Rvalue, Stmt as VirStmt, Term,
};
use std::collections::HashMap;

#[derive(Debug, Clone, Default)]
pub(super) struct Scope {
    pub(super) bindings: HashMap<String, LocalId>,
    pub(super) locals: Vec<LocalId>,
    pub(super) cleanup: Vec<CleanupLocal>,
    pub(super) symbols: SymbolScope,
}

/// Lower a function body, returning the body and any nested closure bodies.
pub(super) fn lower_function_with_closures(
    function_name: &str,
    params: &[(String, RustType)],
    ret: &RustType,
    body: &Expr,
    symbols: &ProgramSymbols,
) -> Result<(Body, Vec<(String, Body)>), VirLoweringError> {
    let mut ctx = FunctionLoweringContext::new(function_name, params, ret.clone(), symbols);
    ctx.emit_fn_entry_retags(params);
    ctx.lower_expr_into(Place::Local(0), body, false)?;
    if !ctx.terminated {
        ctx.pop_scope();
        ctx.current_block_mut().terminator = Term::Return;
    }
    Ok((ctx.body, ctx.closure_bodies))
}

pub(super) struct FunctionLoweringContext<'a> {
    pub(super) function_name: &'a str,
    pub(super) symbols: &'a ProgramSymbols,
    pub(super) body: Body,
    pub(super) scopes: Vec<Scope>,
    pub(super) closure_def_ids: HashMap<LocalId, String>,
    pub(super) generator_def_ids: HashMap<LocalId, String>,
    pub(super) future_output_tys: HashMap<LocalId, RustType>,
    pub(super) callable_future_output_tys: HashMap<LocalId, RustType>,
    pub(super) loop_stack: Vec<LoopTarget>,
    pub(super) terminated: bool,
    pub(super) current_block: BasicBlockId,
    pub(super) building_cleanup_blocks: bool,
    /// Accumulated closure bodies produced during lowering.
    pub(super) closure_bodies: Vec<(String, Body)>,
    closure_counter: u32,
    generator_counter: u32,
}

impl<'a> FunctionLoweringContext<'a> {
    pub(super) fn new(
        function_name: &'a str,
        params: &[(String, RustType)],
        ret: RustType,
        symbols: &'a ProgramSymbols,
    ) -> Self {
        let mut body = Body::new();
        body.add_local(LocalDecl::new(ret, Mutability::Mutable).with_name("return"));
        body.arg_count = params.len() as u32;
        body.add_block(BasicBlock::new(Term::Return));

        let mut root_scope = Scope::default();
        for (name, ty) in params {
            let local =
                body.add_local(LocalDecl::new(ty.clone(), Mutability::Shared).with_name(name));
            root_scope.bindings.insert(name.clone(), local);
        }

        Self {
            function_name,
            symbols,
            body,
            scopes: vec![root_scope],
            closure_def_ids: HashMap::new(),
            generator_def_ids: HashMap::new(),
            future_output_tys: HashMap::new(),
            callable_future_output_tys: HashMap::new(),
            loop_stack: Vec::new(),
            terminated: false,
            current_block: 0,
            building_cleanup_blocks: false,
            closure_bodies: Vec::new(),
            closure_counter: 0,
            generator_counter: 0,
        }
    }

    pub(super) fn lower_expr_into(
        &mut self,
        destination: Place,
        expr: &Expr,
        new_scope: bool,
    ) -> Result<(), VirLoweringError> {
        if self.terminated {
            return Ok(());
        }

        if self.try_lower_coerced_expr(&destination, expr)? {
            return Ok(());
        }

        match expr {
            Expr::Block { stmts, expr } => {
                self.lower_block_expr(destination, stmts, expr.as_deref(), new_scope)
            }
            Expr::Literal(value) => {
                let constant = constant_from_value(value)?;
                self.emit(VirStmt::Assign {
                    place: destination,
                    rvalue: Rvalue::Use(Operand::Constant(constant)),
                });
                Ok(())
            }
            Expr::Var { .. }
            | Expr::Field { .. }
            | Expr::Index { .. }
            | Expr::Deref(_)
            | Expr::RawDeref(_) => self.lower_place_like_expr_into(destination, expr),
            Expr::AddrOf { mutability, expr } => {
                self.lower_addr_of_expr(destination, *mutability, expr)
            }
            Expr::Assign { target, value } => self.lower_assign_expr(destination, target, value),
            Expr::AssignOp { op, target, value } => {
                self.lower_assign_op_expr(destination, *op, target, value)
            }
            Expr::Return(_) => self.lower_return(expr),
            Expr::Break { label, value } => {
                self.lower_break_expr(label.as_deref(), value.as_deref())
            }
            Expr::Continue { label } => self.lower_continue_expr(label.as_deref()),
            Expr::BinOp { op, left, right } => {
                let lhs = self.lower_operand(left)?;
                let rhs = self.lower_operand(right)?;
                self.emit(VirStmt::Assign {
                    place: destination,
                    rvalue: Rvalue::BinaryOp {
                        op: lower_bin_op(*op),
                        lhs,
                        rhs,
                    },
                });
                Ok(())
            }
            Expr::UnOp { op, expr } => {
                let operand = self.lower_operand(expr)?;
                self.emit(VirStmt::Assign {
                    place: destination,
                    rvalue: Rvalue::UnaryOp {
                        op: lower_un_op(*op),
                        operand,
                    },
                });
                Ok(())
            }
            Expr::Cast { expr, target } => self.lower_cast_expr(destination, expr, target),
            Expr::Tuple(elements) => self.lower_tuple_expr(destination, elements),
            Expr::Array(elements) => self.lower_array_expr(destination, elements),
            Expr::If {
                condition,
                then_branch,
                else_branch,
            } => self.lower_if_expr(destination, condition, then_branch, else_branch.as_deref()),
            Expr::Match { scrutinee, arms } => self.lower_match_expr(destination, scrutinee, arms),
            Expr::Loop { label, body } => self.lower_loop_expr(destination, label.as_deref(), body),
            Expr::While {
                label,
                condition,
                body,
            } => self.lower_while_expr(destination, label.as_deref(), condition, body),
            Expr::Struct { name, fields, .. } => self.lower_struct_expr(destination, name, fields),
            Expr::EnumVariant {
                enum_name,
                variant,
                payload,
                ..
            } => self.lower_enum_variant_expr(destination, enum_name, variant, payload),
            Expr::Call { func, args, .. } => self.lower_call_expr(destination, func, args),
            Expr::MethodCall {
                receiver,
                method,
                args,
                ..
            } => self.lower_method_call_expr(destination, receiver, method, args),
            Expr::Unsafe { block } => self.lower_expr_into(
                destination,
                block,
                matches!(block.as_ref(), Expr::Block { .. }),
            ),
            Expr::Panic { .. } => {
                self.current_block_mut().terminator = Term::Unreachable;
                self.terminated = true;
                Ok(())
            }
            Expr::ArrayRepeat { value, count } => {
                self.lower_array_repeat_expr(destination, value, *count)
            }
            Expr::Range {
                start,
                end,
                inclusive,
            } => self.lower_range_expr(destination, start.as_deref(), end.as_deref(), *inclusive),
            Expr::For {
                label,
                pattern,
                iter,
                body,
            } => self.lower_for_expr(destination, label.as_deref(), pattern, iter, body),
            Expr::Closure {
                params,
                body,
                captures,
                capture_by_value,
            } => self.lower_closure_expr(destination, params, body, captures, *capture_by_value),
            Expr::UnionInit { name, field } => self.lower_union_init_expr(destination, name, field),
            Expr::UnionFieldAccess { union_expr, field } => {
                self.lower_union_field_access_expr(destination, union_expr, field)
            }
            Expr::Async {
                capture_by_value,
                body,
            } => self.lower_async_expr(destination, *capture_by_value, body),
            Expr::Await { base } => self.lower_await_expr(destination, base),
            Expr::InlineAsm(asm) => self.lower_inline_asm_expr(destination, asm),
        }
    }

    pub(super) fn next_closure_id(&mut self) -> u32 {
        let id = self.closure_counter;
        self.closure_counter += 1;
        id
    }

    pub(super) fn next_generator_id(&mut self) -> u32 {
        let id = self.generator_counter;
        self.generator_counter += 1;
        id
    }
}

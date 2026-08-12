// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! C → clean Kernel Translation
//!
//! This module provides translation from C programs to clean kernel terms.
//! This enables verification of C programs using clean's theorem prover.
//!
//! ## Translation Strategy
//!
//! C programs are translated to clean terms following a deep embedding:
//!
//! 1. **Types**: C types → clean inductive types
//! 2. **Values**: C values → clean terms
//! 3. **Expressions**: C expressions → clean functions (state → result)
//! 4. **Statements**: C statements → clean monadic operations
//! 5. **Specifications**: ACSL specs → clean propositions
//!
//! ## Memory Model
//!
//! The C memory model is represented in clean as:
//!
//! ```text
//! inductive CType where
//!   | int : IntKind → Signedness → CType
//!   | ptr : CType → CType
//!   | struct : List (String × CType) → CType
//!   | ...
//!
//! structure Memory where
//!   blocks : BlockId → Option Block
//!   next_id : Nat
//!
//! def load : Memory → Pointer → CType → Result CValue
//! def store : Memory → Pointer → CValue → Result Memory
//! ```

use crate::expr::{BinOp, CExpr, UnaryOp};
use crate::spec::Spec;
use crate::stmt::CStmt;
use crate::types::{CType, FloatKind, IntKind, Signedness};
use clean_kernel::{Expr, ExprKind, Name};
use std::borrow::Cow;
use std::str::FromStr;

/// Create a Name from a string
fn name(s: &str) -> Name {
    Name::from_str(s).unwrap()
}

/// Translation context
pub struct TranslationContext {
    /// Variable name to de Bruijn level mapping
    var_levels: std::collections::HashMap<String, u32>,
    /// Current de Bruijn level
    current_level: u32,
    /// Generated definitions (reserved for emitting definitions to environment)
    _definitions: Vec<(Name, Expr)>,
}

impl Default for TranslationContext {
    fn default() -> Self {
        Self::new()
    }
}

impl TranslationContext {
    pub fn new() -> Self {
        Self {
            var_levels: std::collections::HashMap::new(),
            current_level: 0,
            _definitions: Vec::new(),
        }
    }

    /// Translate a C type to a clean expression
    ///
    /// C types are represented as terms of an inductive `CType` type:
    /// ```text
    /// inductive CType where
    ///   | void : CType
    ///   | int : IntKind → Signedness → CType
    ///   | float : FloatKind → CType
    ///   | ptr : CType → CType
    ///   | array : CType → Nat → CType
    ///   | struct : String → List (String × CType) → CType
    /// ```
    pub fn translate_type(&self, ty: &CType) -> Expr {
        match ty {
            CType::Void => {
                // CType.void
                Expr::const_(name("CType.void"), vec![])
            }

            CType::Int(kind, sign) => {
                // CType.int kind sign
                let kind_expr = self.translate_int_kind(*kind);
                let sign_expr = self.translate_signedness(*sign);
                Expr::app(
                    Expr::app(Expr::const_(name("CType.int"), vec![]), kind_expr),
                    sign_expr,
                )
            }

            CType::Float(kind) => {
                // CType.float kind
                let kind_expr = self.translate_float_kind(*kind);
                Expr::app(Expr::const_(name("CType.float"), vec![]), kind_expr)
            }

            CType::Pointer(inner) => {
                // CType.ptr inner
                let inner_expr = self.translate_type(inner);
                Expr::app(Expr::const_(name("CType.ptr"), vec![]), inner_expr)
            }

            CType::Array(elem, size) => {
                // CType.array elem size
                let elem_expr = self.translate_type(elem);
                let size_expr = self.translate_nat(*size);
                Expr::app(
                    Expr::app(Expr::const_(name("CType.array"), vec![]), elem_expr),
                    size_expr,
                )
            }

            CType::IncompleteArray(elem) => {
                // CType.incompleteArray elem (a flexible array member, C99
                // 6.7.2.1p18 — an array of unknown bound).
                let elem_expr = self.translate_type(elem);
                Expr::app(
                    Expr::const_(name("CType.incompleteArray"), vec![]),
                    elem_expr,
                )
            }

            CType::Struct {
                name: struct_name,
                fields,
            } => {
                // CType.struct name fields
                let name_expr = self.translate_string(struct_name.as_deref().unwrap_or(""));
                let fields_expr = self.translate_field_list(fields);
                Expr::app(
                    Expr::app(Expr::const_(name("CType.struct"), vec![]), name_expr),
                    fields_expr,
                )
            }

            CType::Union {
                name: union_name,
                fields,
            } => {
                let name_expr = self.translate_string(union_name.as_deref().unwrap_or(""));
                let fields_expr = self.translate_field_list(fields);
                Expr::app(
                    Expr::app(Expr::const_(name("CType.union"), vec![]), name_expr),
                    fields_expr,
                )
            }

            CType::Enum {
                name: enum_name,
                variants: _,
            } => {
                // Enums are represented as ints in C
                let name_expr = self.translate_string(enum_name.as_deref().unwrap_or(""));
                Expr::app(Expr::const_(name("CType.enum"), vec![]), name_expr)
            }

            CType::Function {
                return_type,
                params,
                variadic,
            } => {
                let ret_expr = self.translate_type(return_type);
                let params_expr = self.translate_param_types(params);
                let variadic_expr = self.translate_bool(*variadic);
                Expr::app(
                    Expr::app(
                        Expr::app(Expr::const_(name("CType.func"), vec![]), ret_expr),
                        params_expr,
                    ),
                    variadic_expr,
                )
            }

            CType::TypeDef(typedef_name) => {
                // Reference to typedef (should be resolved)
                Expr::const_(name(&format!("CType.typedef.{typedef_name}")), vec![])
            }

            CType::Qualified { ty, .. } => {
                // Ignore qualifiers for now
                self.translate_type(ty)
            }
        }
    }

    fn translate_int_kind(&self, kind: IntKind) -> Expr {
        let kind_name = match kind {
            IntKind::Bool => "IntKind.bool",
            IntKind::Char => "IntKind.char",
            IntKind::Short => "IntKind.short",
            IntKind::Int => "IntKind.int",
            IntKind::Long => "IntKind.long",
            IntKind::LongLong => "IntKind.longLong",
        };
        Expr::const_(name(kind_name), vec![])
    }

    fn translate_signedness(&self, sign: Signedness) -> Expr {
        let sign_name = match sign {
            Signedness::Signed => "Signedness.signed",
            Signedness::Unsigned => "Signedness.unsigned",
        };
        Expr::const_(name(sign_name), vec![])
    }

    fn translate_float_kind(&self, kind: FloatKind) -> Expr {
        let float_name = match kind {
            FloatKind::Float => "FloatKind.float",
            FloatKind::Double => "FloatKind.double",
            FloatKind::LongDouble => "FloatKind.longDouble",
        };
        Expr::const_(name(float_name), vec![])
    }

    fn translate_nat(&self, n: usize) -> Expr {
        // SOUNDNESS/robustness: lower to a single `Nat` literal rather than a
        // unary `Nat.succ` chain. The chain was O(n) in the value, so large
        // literals (e.g. the `INT_MIN`/`INT_MAX` bounds emitted by the
        // signed-overflow obligations) built a multi-billion-deep term and
        // overflowed the stack during translation. A literal is canonical, and
        // the structural prover (`try_extract_nat`) already reads
        // `Literal::Nat` directly.
        Expr::nat_lit(n as u64)
    }

    fn translate_int(&self, n: i64) -> Expr {
        // Represent as Int constructor
        if n >= 0 {
            Expr::app(
                Expr::const_(name("Int.ofNat"), vec![]),
                self.translate_nat(n as usize),
            )
        } else {
            // Handle i64::MIN correctly by computing magnitude as u64.
            // For negative i64 values, the magnitude is 0u64.wrapping_sub(n as u64).
            // This works for all negative values including i64::MIN:
            // - i64::MIN as u64 = 9223372036854775808
            // - 0u64.wrapping_sub(9223372036854775808) = 9223372036854775808
            // For other values like -5: -5i64 as u64 = 18446744073709551611
            // - 0u64.wrapping_sub(18446744073709551611) = 5
            let magnitude = 0u64.wrapping_sub(n as u64) as usize;
            Expr::app(
                Expr::const_(name("Int.negOfNat"), vec![]),
                self.translate_nat(magnitude),
            )
        }
    }

    fn translate_bool(&self, b: bool) -> Expr {
        if b {
            Expr::const_(name("Bool.true"), vec![])
        } else {
            Expr::const_(name("Bool.false"), vec![])
        }
    }

    fn translate_string(&self, s: &str) -> Expr {
        // Strings as lists of chars
        Expr::from_kind(ExprKind::Lit(clean_kernel::Literal::String(s.into())))
    }

    fn translate_field_list(&self, fields: &[crate::types::StructField]) -> Expr {
        // Build List (String × CType)
        let mut result = Expr::const_(name("List.nil"), vec![]);
        for field in fields.iter().rev() {
            let name_expr = self.translate_string(&field.name);
            let ty_expr = self.translate_type(&field.ty);
            let pair = Expr::app(
                Expr::app(Expr::const_(name("Prod.mk"), vec![]), name_expr),
                ty_expr,
            );
            result = Expr::app(
                Expr::app(Expr::const_(name("List.cons"), vec![]), pair),
                result,
            );
        }
        result
    }

    fn translate_param_types(&self, params: &[crate::types::FuncParam]) -> Expr {
        let mut result = Expr::const_(name("List.nil"), vec![]);
        for param in params.iter().rev() {
            let ty_expr = self.translate_type(&param.ty);
            result = Expr::app(
                Expr::app(Expr::const_(name("List.cons"), vec![]), ty_expr),
                result,
            );
        }
        result
    }

    /// Translate a C expression to a clean term
    ///
    /// C expressions are translated to functions: State → Result CValue
    pub fn translate_expr(&mut self, expr: &CExpr) -> Expr {
        match expr {
            CExpr::IntLit(n) => {
                // CValue.int n
                Expr::app(
                    Expr::const_(name("CValue.int"), vec![]),
                    self.translate_int(*n),
                )
            }

            CExpr::UIntLit(n) => Expr::app(
                Expr::const_(name("CValue.uint"), vec![]),
                self.translate_nat(*n as usize),
            ),

            CExpr::FloatLit(f) => {
                // CValue.float f (as string for now)
                Expr::app(
                    Expr::const_(name("CValue.float"), vec![]),
                    self.translate_string(&f.to_string()),
                )
            }

            CExpr::CharLit(c) => Expr::app(
                Expr::const_(name("CValue.int"), vec![]),
                self.translate_int(*c as i64),
            ),

            CExpr::StringLit(s) => Expr::app(
                Expr::const_(name("CValue.string"), vec![]),
                self.translate_string(s),
            ),

            CExpr::Var(var_name) => {
                if let Some(&level) = self.var_levels.get(var_name) {
                    // Use bound variable
                    let index = self.current_level - level - 1;
                    Expr::bvar(index)
                } else {
                    // Free variable / global
                    Expr::const_(name(&format!("var.{var_name}")), vec![])
                }
            }

            CExpr::BinOp { op, left, right } => {
                let left_expr = self.translate_expr(left);
                let right_expr = self.translate_expr(right);
                let op_name = self.translate_binop(*op);
                Expr::app(
                    Expr::app(Expr::const_(name(op_name), vec![]), left_expr),
                    right_expr,
                )
            }

            CExpr::UnaryOp { op, operand } => {
                let operand_expr = self.translate_expr(operand);
                let op_name = self.translate_unaryop(*op);
                Expr::app(Expr::const_(name(op_name), vec![]), operand_expr)
            }

            CExpr::Conditional {
                cond,
                then_expr,
                else_expr,
            } => {
                let cond_expr = self.translate_expr(cond);
                let then_e = self.translate_expr(then_expr);
                let else_e = self.translate_expr(else_expr);
                Expr::app(
                    Expr::app(
                        Expr::app(Expr::const_(name("CExpr.cond"), vec![]), cond_expr),
                        then_e,
                    ),
                    else_e,
                )
            }

            CExpr::Cast { ty, expr: e } => {
                let ty_expr = self.translate_type(ty);
                let e_expr = self.translate_expr(e);
                Expr::app(
                    Expr::app(Expr::const_(name("CExpr.cast"), vec![]), ty_expr),
                    e_expr,
                )
            }

            CExpr::SizeOf(arg) => match arg {
                crate::expr::SizeOfArg::Type(ty) => Expr::app(
                    Expr::const_(name("CValue.uint"), vec![]),
                    self.translate_nat(ty.size()),
                ),
                // SOUNDNESS (hole 6): `sizeof(expr)` must NOT collapse to a
                // concrete literal (previously `CValue.uint 0`), which made
                // `sizeof(x) == sizeof(y)` structurally equal for distinct `x`,
                // `y` and falsely "proved". Without type inference we cannot
                // know the size, so we lower to an OPERAND-DISTINCT symbolic
                // head `CExpr.sizeofExpr` applied to the translated operand, so
                // `sizeof(x)` and `sizeof(y)` stay distinct terms.
                // See docs/SOUNDNESS_FINDINGS_CLEAN_C_SEM_2026-07.md hole 6.
                crate::expr::SizeOfArg::Expr(inner) => {
                    let inner_expr = self.translate_expr(inner);
                    Expr::app(Expr::const_(name("CExpr.sizeofExpr"), vec![]), inner_expr)
                }
            },

            CExpr::AlignOf(ty) => Expr::app(
                Expr::const_(name("CValue.uint"), vec![]),
                self.translate_nat(ty.align()),
            ),

            CExpr::Call { func, args } => {
                let func_expr = self.translate_expr(func);
                let args_expr = self.translate_expr_list(args);
                Expr::app(
                    Expr::app(Expr::const_(name("CExpr.call"), vec![]), func_expr),
                    args_expr,
                )
            }

            CExpr::Index { array, index } => {
                let arr_expr = self.translate_expr(array);
                let idx_expr = self.translate_expr(index);
                Expr::app(
                    Expr::app(Expr::const_(name("CExpr.index"), vec![]), arr_expr),
                    idx_expr,
                )
            }

            CExpr::Member { object, field } => {
                let obj_expr = self.translate_expr(object);
                let field_expr = self.translate_string(field);
                Expr::app(
                    Expr::app(Expr::const_(name("CExpr.member"), vec![]), obj_expr),
                    field_expr,
                )
            }

            CExpr::Arrow { pointer, field } => {
                // p->field = (*p).field
                let deref = CExpr::UnaryOp {
                    op: UnaryOp::Deref,
                    operand: pointer.clone(),
                };
                let member = CExpr::Member {
                    object: Box::new(deref),
                    field: field.clone(),
                };
                self.translate_expr(&member)
            }

            CExpr::CompoundLiteral { ty, init } => {
                // (type){initializers}  (C99 6.5.2.5) lowers to the 2-arg
                // `CExpr.compoundLiteral` head: the translated object type first,
                // then the brace-enclosed initializer list. The list is built
                // with `List.cons`/`List.nil` exactly like `translate_expr_list`,
                // and each element is faithfully reflected by
                // `translate_initializer` (an uninterpreted `Initializer.*` head
                // applied to its translated sub-parts).
                let ty_expr = self.translate_type(ty);
                let init_expr = self.translate_initializer_list(init);
                Expr::app(
                    Expr::app(Expr::const_(name("CExpr.compoundLiteral"), vec![]), ty_expr),
                    init_expr,
                )
            }

            // SOUNDNESS (holes 5,6): remaining unsupported expression forms
            // lower to a VARIANT-DISTINCT head carrying their translated
            // sub-parts, so distinct expressions do NOT collapse to a single
            // `CExpr.unsupported` head (which would make unrelated expressions
            // structurally equal).
            CExpr::Generic {
                control,
                associations,
            } => {
                let ctrl = self.translate_expr(control);
                let mut result = Expr::app(Expr::const_(name("CExpr.generic"), vec![]), ctrl);
                for (_, e) in associations {
                    let e_expr = self.translate_expr(e);
                    result = Expr::app(result, e_expr);
                }
                result
            }

            CExpr::StmtExpr(stmts) => {
                let stmts_expr = self.translate_stmt_list(stmts);
                Expr::app(Expr::const_(name("CExpr.stmtExpr"), vec![]), stmts_expr)
            }
        }
    }

    /// Build a `List` of translated initializers with `List.cons`/`List.nil`,
    /// mirroring [`Self::translate_expr_list`].
    fn translate_initializer_list(&mut self, inits: &[crate::expr::Initializer]) -> Expr {
        let mut result = Expr::const_(name("List.nil"), vec![]);
        for init in inits.iter().rev() {
            let e = self.translate_initializer(init);
            result = Expr::app(
                Expr::app(Expr::const_(name("List.cons"), vec![]), e),
                result,
            );
        }
        result
    }

    /// Translate a single initializer to an uninterpreted `Initializer.*` head
    /// applied to its faithfully-translated sub-parts.
    ///
    /// - `Initializer::Expr(e)`        → `Initializer.expr <e>`
    /// - `Initializer::Designated{..}` → `Initializer.designated <designator> <init>`
    /// - `Initializer::List(items)`    → `Initializer.list <list-of-items>`
    fn translate_initializer(&mut self, init: &crate::expr::Initializer) -> Expr {
        use crate::expr::Initializer;
        match init {
            Initializer::Expr(e) => {
                let e_expr = self.translate_expr(e);
                Expr::app(Expr::const_(name("Initializer.expr"), vec![]), e_expr)
            }

            Initializer::Designated { designator, init } => {
                let desig_expr = self.translate_designator(designator);
                let init_expr = self.translate_initializer(init);
                Expr::app(
                    Expr::app(
                        Expr::const_(name("Initializer.designated"), vec![]),
                        desig_expr,
                    ),
                    init_expr,
                )
            }

            Initializer::List(items) => {
                let items_expr = self.translate_initializer_list(items);
                Expr::app(Expr::const_(name("Initializer.list"), vec![]), items_expr)
            }
        }
    }

    /// Translate a designator (`.field`, `[index]`, or a chain) to an
    /// uninterpreted `Designator.*` head.
    ///
    /// - `Designator::Field(name)`   → `Designator.field "name"` (the field name
    ///   is an opaque struct/union member name, carried as a string literal like
    ///   field names elsewhere in this module).
    /// - `Designator::Index(e)`      → `Designator.index <e>`
    /// - `Designator::Chain(parts)`  → `Designator.chain <list-of-parts>`
    fn translate_designator(&mut self, designator: &crate::expr::Designator) -> Expr {
        use crate::expr::Designator;
        match designator {
            Designator::Field(field) => {
                let field_expr = self.translate_string(field);
                Expr::app(Expr::const_(name("Designator.field"), vec![]), field_expr)
            }

            Designator::Index(idx) => {
                let idx_expr = self.translate_expr(idx);
                Expr::app(Expr::const_(name("Designator.index"), vec![]), idx_expr)
            }

            Designator::Chain(parts) => {
                let mut result = Expr::const_(name("List.nil"), vec![]);
                for part in parts.iter().rev() {
                    let p = self.translate_designator(part);
                    result = Expr::app(
                        Expr::app(Expr::const_(name("List.cons"), vec![]), p),
                        result,
                    );
                }
                Expr::app(Expr::const_(name("Designator.chain"), vec![]), result)
            }
        }
    }

    fn translate_binop(&self, op: BinOp) -> &'static str {
        match op {
            BinOp::Add => "CExpr.add",
            BinOp::Sub => "CExpr.sub",
            BinOp::Mul => "CExpr.mul",
            BinOp::Div => "CExpr.div",
            BinOp::Mod => "CExpr.mod",
            BinOp::BitAnd => "CExpr.bitAnd",
            BinOp::BitOr => "CExpr.bitOr",
            BinOp::BitXor => "CExpr.bitXor",
            BinOp::Shl => "CExpr.shl",
            BinOp::Shr => "CExpr.shr",
            BinOp::Eq => "CExpr.eq",
            BinOp::Ne => "CExpr.ne",
            BinOp::Lt => "CExpr.lt",
            BinOp::Le => "CExpr.le",
            BinOp::Gt => "CExpr.gt",
            BinOp::Ge => "CExpr.ge",
            BinOp::LogAnd => "CExpr.logAnd",
            BinOp::LogOr => "CExpr.logOr",
            BinOp::Assign => "CExpr.assign",
            BinOp::AddAssign => "CExpr.addAssign",
            BinOp::SubAssign => "CExpr.subAssign",
            BinOp::MulAssign => "CExpr.mulAssign",
            BinOp::DivAssign => "CExpr.divAssign",
            BinOp::ModAssign => "CExpr.modAssign",
            BinOp::BitAndAssign => "CExpr.bitAndAssign",
            BinOp::BitOrAssign => "CExpr.bitOrAssign",
            BinOp::BitXorAssign => "CExpr.bitXorAssign",
            BinOp::ShlAssign => "CExpr.shlAssign",
            BinOp::ShrAssign => "CExpr.shrAssign",
            BinOp::Comma => "CExpr.comma",
        }
    }

    fn translate_unaryop(&self, op: UnaryOp) -> &'static str {
        match op {
            UnaryOp::Neg => "CExpr.neg",
            UnaryOp::Pos => "CExpr.pos",
            UnaryOp::BitNot => "CExpr.bitNot",
            UnaryOp::LogNot => "CExpr.logNot",
            UnaryOp::Deref => "CExpr.deref",
            UnaryOp::AddrOf => "CExpr.addrOf",
            UnaryOp::PreInc => "CExpr.preInc",
            UnaryOp::PreDec => "CExpr.preDec",
            UnaryOp::PostInc => "CExpr.postInc",
            UnaryOp::PostDec => "CExpr.postDec",
        }
    }

    fn translate_expr_list(&mut self, exprs: &[CExpr]) -> Expr {
        let mut result = Expr::const_(name("List.nil"), vec![]);
        for expr in exprs.iter().rev() {
            let e = self.translate_expr(expr);
            result = Expr::app(
                Expr::app(Expr::const_(name("List.cons"), vec![]), e),
                result,
            );
        }
        result
    }

    /// Translate a C statement to a clean term
    ///
    /// Statements are translated to monadic operations: State → State × Result Unit
    pub fn translate_stmt(&mut self, stmt: &CStmt) -> Expr {
        match stmt {
            CStmt::Empty => Expr::const_(name("CStmt.skip"), vec![]),

            CStmt::Expr(e) => {
                let e_expr = self.translate_expr(e);
                Expr::app(Expr::const_(name("CStmt.expr"), vec![]), e_expr)
            }

            CStmt::Decl(decl) => {
                let name_expr = self.translate_string(&decl.name);
                let ty_expr = self.translate_type(&decl.ty);
                Expr::app(
                    Expr::app(Expr::const_(name("CStmt.decl"), vec![]), name_expr),
                    ty_expr,
                )
            }

            CStmt::Block(stmts) => {
                let stmts_expr = self.translate_stmt_list(stmts);
                Expr::app(Expr::const_(name("CStmt.block"), vec![]), stmts_expr)
            }

            CStmt::If {
                cond,
                then_stmt,
                else_stmt,
            } => {
                let cond_expr = self.translate_expr(cond);
                let then_expr = self.translate_stmt(then_stmt);
                let else_expr = else_stmt.as_ref().map_or_else(
                    || Expr::const_(name("CStmt.skip"), vec![]),
                    |s| self.translate_stmt(s),
                );
                Expr::app(
                    Expr::app(
                        Expr::app(Expr::const_(name("CStmt.if"), vec![]), cond_expr),
                        then_expr,
                    ),
                    else_expr,
                )
            }

            CStmt::While { cond, body } => {
                let cond_expr = self.translate_expr(cond);
                let body_expr = self.translate_stmt(body);
                Expr::app(
                    Expr::app(Expr::const_(name("CStmt.while"), vec![]), cond_expr),
                    body_expr,
                )
            }

            CStmt::DoWhile { body, cond } => {
                let body_expr = self.translate_stmt(body);
                let cond_expr = self.translate_expr(cond);
                Expr::app(
                    Expr::app(Expr::const_(name("CStmt.doWhile"), vec![]), body_expr),
                    cond_expr,
                )
            }

            CStmt::Switch { cond, body } => {
                // switch (cond) body  lowers to the 2-arg `CStmt.switch` head,
                // mirroring `CStmt.while`: the controlling expression first,
                // then the (compound) body holding the `case`/`default` arms.
                let cond_expr = self.translate_expr(cond);
                let body_expr = self.translate_stmt(body);
                Expr::app(
                    Expr::app(Expr::const_(name("CStmt.switch"), vec![]), cond_expr),
                    body_expr,
                )
            }

            CStmt::Case { label, stmt } => {
                // case expr: stmt  /  default: stmt  lowers to the 2-arg
                // `CStmt.case` head. The label is itself reflected as an
                // uninterpreted head: `CaseLabel.case expr` carries the
                // matched constant expression, `CaseLabel.default` is nullary.
                let label_expr = match label {
                    crate::stmt::CaseLabel::Case(e) => Expr::app(
                        Expr::const_(name("CaseLabel.case"), vec![]),
                        self.translate_expr(e),
                    ),
                    crate::stmt::CaseLabel::Default => {
                        Expr::const_(name("CaseLabel.default"), vec![])
                    }
                };
                let stmt_expr = self.translate_stmt(stmt);
                Expr::app(
                    Expr::app(Expr::const_(name("CStmt.case"), vec![]), label_expr),
                    stmt_expr,
                )
            }

            CStmt::For {
                init,
                cond,
                update,
                body,
            } => {
                // Optional statement (`init`) defaults to `CStmt.skip`, exactly
                // like the absent `else` branch of `CStmt.if`. Optional
                // expressions (`cond`, `update`) default to `CValue.unit`, the
                // same missing-CExpr convention used by `CStmt.return`.
                let init_expr = init.as_ref().map_or_else(
                    || Expr::const_(name("CStmt.skip"), vec![]),
                    |s| self.translate_stmt(s),
                );
                let cond_expr = cond.as_ref().map_or_else(
                    || Expr::const_(name("CValue.unit"), vec![]),
                    |c| self.translate_expr(c),
                );
                let update_expr = update.as_ref().map_or_else(
                    || Expr::const_(name("CValue.unit"), vec![]),
                    |u| self.translate_expr(u),
                );
                let body_expr = self.translate_stmt(body);
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(Expr::const_(name("CStmt.for"), vec![]), init_expr),
                            cond_expr,
                        ),
                        update_expr,
                    ),
                    body_expr,
                )
            }

            CStmt::Return(expr) => {
                let val_expr = expr.as_ref().map_or_else(
                    || Expr::const_(name("CValue.unit"), vec![]),
                    |e| self.translate_expr(e),
                );
                Expr::app(Expr::const_(name("CStmt.return"), vec![]), val_expr)
            }

            CStmt::Break => Expr::const_(name("CStmt.break"), vec![]),

            CStmt::Continue => Expr::const_(name("CStmt.continue"), vec![]),

            CStmt::Goto(label) => {
                // goto label;  lowers to the 1-arg `CStmt.goto` head. The target
                // label is an opaque program point — like the `at(e, label)`
                // program point in `Spec::At` and the struct/field names
                // elsewhere — so it is reflected as a string literal.
                let label_expr = self.translate_string(label);
                Expr::app(Expr::const_(name("CStmt.goto"), vec![]), label_expr)
            }

            CStmt::Label { name: lbl, stmt } => {
                // label: stmt  lowers to the 2-arg `CStmt.label` head, mirroring
                // `CStmt.case`: the label name (a string literal, like `goto`'s
                // target) first, then the faithfully-translated guarded
                // statement.
                let label_expr = self.translate_string(lbl);
                let stmt_expr = self.translate_stmt(stmt);
                Expr::app(
                    Expr::app(Expr::const_(name("CStmt.label"), vec![]), label_expr),
                    stmt_expr,
                )
            }

            _ => {
                // Default: unsupported statement
                Expr::const_(name("CStmt.unsupported"), vec![])
            }
        }
    }

    fn translate_stmt_list(&mut self, stmts: &[CStmt]) -> Expr {
        let mut result = Expr::const_(name("List.nil"), vec![]);
        for stmt in stmts.iter().rev() {
            let s = self.translate_stmt(stmt);
            result = Expr::app(
                Expr::app(Expr::const_(name("List.cons"), vec![]), s),
                result,
            );
        }
        result
    }

    /// Translate a specification to a clean proposition
    pub fn translate_spec(&mut self, spec: &Spec) -> Expr {
        match spec {
            Spec::True => Expr::const_(name("True"), vec![]),

            Spec::False => Expr::const_(name("False"), vec![]),

            Spec::Result => Expr::const_(name("Spec.result"), vec![]),

            Spec::Var(var_name) => {
                if let Some(&level) = self.var_levels.get(var_name) {
                    let index = self.current_level - level - 1;
                    Expr::bvar(index)
                } else {
                    Expr::const_(name(&format!("spec.{var_name}")), vec![])
                }
            }

            Spec::Int(n) => self.translate_int(*n),

            Spec::Expr(e) => self.translate_expr(e),

            Spec::Old(e) => {
                let e_expr = self.translate_spec(e);
                Expr::app(Expr::const_(name("Spec.old"), vec![]), e_expr)
            }

            // `at(e, label)` evaluates `e` in the program state at `label`.
            // It generalizes `old(e)`, which is `at(e, Pre)`; we lower it the
            // same way `Spec::Old` lowers to the uninterpreted head `Spec.old`,
            // but carry the label name as a second argument so distinct labels
            // remain distinguishable. The label is an opaque program point, so
            // it is represented as a string literal (mirroring how field and
            // variable names are lowered elsewhere in this module).
            Spec::At { expr, label } => {
                let e_expr = self.translate_spec(expr);
                let label_expr = self.translate_string(label);
                Expr::app(
                    Expr::app(Expr::const_(name("Spec.at"), vec![]), e_expr),
                    label_expr,
                )
            }

            Spec::And(specs) => {
                if specs.is_empty() {
                    return Expr::const_(name("True"), vec![]);
                }
                let mut result = self.translate_spec(&specs[0]);
                for spec in &specs[1..] {
                    let s = self.translate_spec(spec);
                    result = Expr::app(Expr::app(Expr::const_(name("And"), vec![]), result), s);
                }
                result
            }

            Spec::Or(specs) => {
                if specs.is_empty() {
                    return Expr::const_(name("False"), vec![]);
                }
                let mut result = self.translate_spec(&specs[0]);
                for spec in &specs[1..] {
                    let s = self.translate_spec(spec);
                    result = Expr::app(Expr::app(Expr::const_(name("Or"), vec![]), result), s);
                }
                result
            }

            Spec::Not(s) => {
                let s_expr = self.translate_spec(s);
                Expr::app(Expr::const_(name("Not"), vec![]), s_expr)
            }

            Spec::Implies(p, q) => {
                let p_expr = self.translate_spec(p);
                let q_expr = self.translate_spec(q);
                // Implication as Pi type: P → Q
                Expr::pi(clean_kernel::BinderInfo::Default, p_expr, q_expr)
            }

            Spec::Forall { var, ty, body } => {
                let ty_expr = self.translate_type(ty);
                // Bind variable
                self.var_levels.insert(var.clone(), self.current_level);
                self.current_level += 1;
                let body_expr = self.translate_spec(body);
                self.current_level -= 1;
                self.var_levels.remove(var);

                // ∀ x : ty, body
                Expr::pi(clean_kernel::BinderInfo::Default, ty_expr, body_expr)
            }

            Spec::Exists { var, ty, body } => {
                let ty_expr = self.translate_type(ty);
                self.var_levels.insert(var.clone(), self.current_level);
                self.current_level += 1;
                let body_expr = self.translate_spec(body);
                self.current_level -= 1;
                self.var_levels.remove(var);

                // Exists as Sigma type
                Expr::app(
                    Expr::app(Expr::const_(name("Exists"), vec![]), ty_expr.clone()),
                    Expr::lam(clean_kernel::BinderInfo::Default, ty_expr, body_expr),
                )
            }

            Spec::BinOp { op, left, right } => {
                let l = self.translate_spec(left);
                let r = self.translate_spec(right);
                // SOUNDNESS (holes 5,8): every operator lowers to an
                // OPERATOR-DISTINCT head. Operators without a canonical clean
                // constant used to collapse to a single `Spec.binop` head, so
                // `(a & b)` and `(a | b)` translated to structurally-equal
                // terms and were falsely "proved" equal. Embedding the operator
                // identity in the head name keeps distinct operations distinct.
                // See docs/SOUNDNESS_FINDINGS_CLEAN_C_SEM_2026-07.md holes 5,8.
                let op_name: Cow<'_, str> = match op {
                    BinOp::Eq => Cow::Borrowed("Eq"),
                    BinOp::Ne => Cow::Borrowed("Ne"),
                    BinOp::Lt => Cow::Borrowed("LT.lt"),
                    BinOp::Le => Cow::Borrowed("LE.le"),
                    BinOp::Gt => Cow::Borrowed("GT.gt"),
                    BinOp::Ge => Cow::Borrowed("GE.ge"),
                    BinOp::Add => Cow::Borrowed("HAdd.hAdd"),
                    BinOp::Sub => Cow::Borrowed("HSub.hSub"),
                    BinOp::Mul => Cow::Borrowed("HMul.hMul"),
                    BinOp::Div => Cow::Borrowed("HDiv.hDiv"),
                    // Uninterpreted, but per-operator distinct: e.g.
                    // `Spec.binop.BitAnd`, `Spec.binop.BitOr`, `Spec.binop.Shl`.
                    other => Cow::Owned(format!("Spec.binop.{other:?}")),
                };
                Expr::app(Expr::app(Expr::const_(name(&op_name), vec![]), l), r)
            }

            Spec::Valid(ptr) => {
                let ptr_expr = self.translate_spec(ptr);
                Expr::app(Expr::const_(name("Spec.valid"), vec![]), ptr_expr)
            }

            // ACSL memory-safety predicates.
            //
            // Like `Spec.valid` above (and the `Spec.old`/`Spec.result`/
            // aggregation heads), these lower to clearly-named uninterpreted
            // constants applied to the translated sub-specs. They let the C
            // verification surface *state* these contracts; the resulting term
            // is type-checked downstream like any other.
            Spec::ValidRead(ptr) => {
                let ptr_expr = self.translate_spec(ptr);
                Expr::app(Expr::const_(name("Spec.valid_read"), vec![]), ptr_expr)
            }

            Spec::ValidRange { ptr, lo, hi } => {
                let ptr_expr = self.translate_spec(ptr);
                let lo_expr = self.translate_spec(lo);
                let hi_expr = self.translate_spec(hi);
                // Spec.valid_range ptr lo hi
                Expr::app(
                    Expr::app(
                        Expr::app(Expr::const_(name("Spec.valid_range"), vec![]), ptr_expr),
                        lo_expr,
                    ),
                    hi_expr,
                )
            }

            Spec::Separated(ptrs) => {
                // Spec.separated applied to a `List` of the translated pointers,
                // built with `List.cons`/`List.nil` like `translate_stmt_list`.
                let mut list = Expr::const_(name("List.nil"), vec![]);
                for ptr in ptrs.iter().rev() {
                    let p = self.translate_spec(ptr);
                    list = Expr::app(Expr::app(Expr::const_(name("List.cons"), vec![]), p), list);
                }
                Expr::app(Expr::const_(name("Spec.separated"), vec![]), list)
            }

            Spec::Fresh(ptr) => {
                let ptr_expr = self.translate_spec(ptr);
                Expr::app(Expr::const_(name("Spec.fresh"), vec![]), ptr_expr)
            }

            Spec::Iff(p, q) => {
                let p_expr = self.translate_spec(p);
                let q_expr = self.translate_spec(q);
                // Spec.iff P Q
                Expr::app(
                    Expr::app(Expr::const_(name("Spec.iff"), vec![]), p_expr),
                    q_expr,
                )
            }

            // Bounded aggregations \sum/\product/\min/\max/\numof.
            //
            // A bounded aggregation `\op(lo, hi, k; body)` binds the integer
            // index `k` over the inclusive range `[lo, hi]`. We lower it the
            // same way the `\forall`/`\exists` quantifiers are lowered: the
            // body is translated under a fresh binder for `k`, yielding the
            // lambda `fun (k : Int) => body`, and the whole form is applied to
            // `lo`, `hi`, and that lambda.
            //
            // No total `Finset.sum`-style operator is available in this deep
            // embedding, so — as with the other ACSL operators (`Spec.valid`,
            // `Spec.old`, `Spec.result`) — each aggregation lowers to a
            // clearly-named uninterpreted constant rather than failing.
            Spec::Sum { lo, hi, var, body } => {
                self.translate_aggregation("Spec.sum", lo, hi, var, body)
            }

            Spec::Product { lo, hi, var, body } => {
                self.translate_aggregation("Spec.product", lo, hi, var, body)
            }

            Spec::Min { lo, hi, var, body } => {
                self.translate_aggregation("Spec.min", lo, hi, var, body)
            }

            Spec::Max { lo, hi, var, body } => {
                self.translate_aggregation("Spec.max", lo, hi, var, body)
            }

            Spec::NumOf { lo, hi, var, body } => {
                self.translate_aggregation("Spec.numof", lo, hi, var, body)
            }

            // SOUNDNESS (hole 8): remaining variants without a dedicated head
            // lower to a VARIANT-DISTINCT uninterpreted head applied to their
            // translated sub-specs, so distinct forms are NOT structurally
            // equal. `(if a then 1 else 2)` and `(if b then 3 else 4)` used to
            // collapse to a single nullary `Spec.unsupported` and were falsely
            // "proved" equal. Each head is `Spec.unsupported.<Variant>` and
            // carries the operands so operand identity is preserved.
            // See docs/SOUNDNESS_FINDINGS_CLEAN_C_SEM_2026-07.md hole 8.
            Spec::If {
                cond,
                then_spec,
                else_spec,
            } => {
                let c = self.translate_spec(cond);
                let t = self.translate_spec(then_spec);
                let e = self.translate_spec(else_spec);
                Expr::app(
                    Expr::app(
                        Expr::app(Expr::const_(name("Spec.unsupported.If"), vec![]), c),
                        t,
                    ),
                    e,
                )
            }

            Spec::Freeable(p) => self.translate_unsupported_unary("Spec.unsupported.Freeable", p),
            Spec::BlockLength(p) => {
                self.translate_unsupported_unary("Spec.unsupported.BlockLength", p)
            }
            Spec::Offset(p) => self.translate_unsupported_unary("Spec.unsupported.Offset", p),
            Spec::BaseAddr(p) => self.translate_unsupported_unary("Spec.unsupported.BaseAddr", p),

            Spec::Null => Expr::const_(name("Spec.unsupported.Null"), vec![]),

            Spec::UnaryOp { op, operand } => {
                let o = self.translate_spec(operand);
                Expr::app(
                    Expr::const_(name(&format!("Spec.unsupported.UnaryOp.{op:?}")), vec![]),
                    o,
                )
            }

            Spec::Let { var, value, body } => {
                let v = self.translate_spec(value);
                self.var_levels.insert(var.clone(), self.current_level);
                self.current_level += 1;
                let b = self.translate_spec(body);
                self.current_level -= 1;
                self.var_levels.remove(var);
                Expr::app(
                    Expr::app(Expr::const_(name("Spec.unsupported.Let"), vec![]), v),
                    Expr::lam(
                        clean_kernel::BinderInfo::Default,
                        self.translate_type(&CType::int()),
                        b,
                    ),
                )
            }

            Spec::Call { func, args } => {
                let mut result =
                    Expr::const_(name(&format!("Spec.unsupported.Call.{func}")), vec![]);
                for arg in args {
                    let a = self.translate_spec(arg);
                    result = Expr::app(result, a);
                }
                result
            }

            Spec::Index { base, index } => {
                let b = self.translate_spec(base);
                let i = self.translate_spec(index);
                Expr::app(
                    Expr::app(Expr::const_(name("Spec.unsupported.Index"), vec![]), b),
                    i,
                )
            }

            Spec::Member { object, field } => {
                let o = self.translate_spec(object);
                let f = self.translate_string(field);
                Expr::app(
                    Expr::app(Expr::const_(name("Spec.unsupported.Member"), vec![]), o),
                    f,
                )
            }
        }
    }

    /// Lower an unsupported unary spec form to a variant-distinct uninterpreted
    /// head applied to its translated operand, preserving operand identity.
    fn translate_unsupported_unary(&mut self, head: &str, operand: &Spec) -> Expr {
        let o = self.translate_spec(operand);
        Expr::app(Expr::const_(name(head), vec![]), o)
    }

    /// Lower a bounded aggregation `op(lo, hi, var; body)` to the kernel term
    /// `op lo hi (fun (var : Int) => body)`.
    ///
    /// The index `var` is bound while translating `body` so that occurrences of
    /// `var` inside the body resolve to the lambda's bound variable, mirroring
    /// the `\forall`/`\exists` quantifier lowering.
    fn translate_aggregation(
        &mut self,
        op: &str,
        lo: &Spec,
        hi: &Spec,
        var: &str,
        body: &Spec,
    ) -> Expr {
        let lo_expr = self.translate_spec(lo);
        let hi_expr = self.translate_spec(hi);

        // The aggregation index ranges over integers.
        let idx_ty = self.translate_type(&CType::int());

        self.var_levels.insert(var.to_string(), self.current_level);
        self.current_level += 1;
        let body_expr = self.translate_spec(body);
        self.current_level -= 1;
        self.var_levels.remove(var);

        let lambda = Expr::lam(clean_kernel::BinderInfo::Default, idx_ty, body_expr);

        Expr::app(
            Expr::app(Expr::app(Expr::const_(name(op), vec![]), lo_expr), hi_expr),
            lambda,
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::ExprKind;

    #[test]
    fn test_translate_int_type() {
        let ctx = TranslationContext::new();
        let ty = CType::int();
        let expr = ctx.translate_type(&ty);

        // Should produce CType.int IntKind.int Signedness.signed
        assert!(matches!(expr.kind(), ExprKind::App(_, _)));
    }

    #[test]
    fn test_translate_pointer_type() {
        let ctx = TranslationContext::new();
        let ty = CType::ptr(CType::int());
        let expr = ctx.translate_type(&ty);

        assert!(matches!(expr.kind(), ExprKind::App(_, _)));
    }

    #[test]
    fn test_translate_int_lit() {
        let mut ctx = TranslationContext::new();
        let e = CExpr::int(42);
        let expr = ctx.translate_expr(&e);

        assert!(matches!(expr.kind(), ExprKind::App(_, _)));
    }

    #[test]
    fn test_translate_binop() {
        let mut ctx = TranslationContext::new();
        let e = CExpr::add(CExpr::int(1), CExpr::int(2));
        let expr = ctx.translate_expr(&e);

        // Should produce CExpr.add (CValue.int 1) (CValue.int 2)
        assert!(matches!(expr.kind(), ExprKind::App(_, _)));
    }

    #[test]
    fn test_translate_if_stmt() {
        let mut ctx = TranslationContext::new();
        let stmt = CStmt::if_stmt(CExpr::int(1), CStmt::return_stmt(Some(CExpr::int(0))));
        let expr = ctx.translate_stmt(&stmt);

        assert!(matches!(expr.kind(), ExprKind::App(_, _)));
    }

    #[test]
    fn test_translate_while_stmt_head_constant() {
        let mut ctx = TranslationContext::new();
        let stmt = CStmt::while_loop(CExpr::int(1), CStmt::return_stmt(Some(CExpr::int(0))));
        let expr = ctx.translate_stmt(&stmt);

        let (head, args) = spine(&expr);
        assert_eq!(const_name(&head).as_deref(), Some("CStmt.while"));
        assert_eq!(args.len(), 2, "CStmt.while is applied to cond and body");
    }

    #[test]
    fn test_translate_for_stmt_full_spine() {
        // for (init; cond; update) body  lowers to the 4-arg `CStmt.for` head.
        let mut ctx = TranslationContext::new();
        let stmt = CStmt::for_loop(
            Some(CStmt::Expr(CExpr::int(0))),
            Some(CExpr::int(1)),
            Some(CExpr::int(2)),
            CStmt::return_stmt(Some(CExpr::int(0))),
        );
        let expr = ctx.translate_stmt(&stmt);

        let (head, args) = spine(&expr);
        assert_eq!(
            const_name(&head).as_deref(),
            Some("CStmt.for"),
            "for loop should lower to its own uninterpreted head constant"
        );
        assert_ne!(
            const_name(&head).as_deref(),
            Some("CStmt.unsupported"),
            "for loops must no longer fall through to CStmt.unsupported"
        );
        assert_eq!(
            args.len(),
            4,
            "CStmt.for is applied to init, cond, update, and body"
        );
    }

    #[test]
    fn test_translate_for_stmt_absent_components_use_defaults() {
        // for (;;) body  — all optional components absent. `init` defaults to
        // the `CStmt.skip` statement default; `cond`/`update` default to the
        // `CValue.unit` missing-CExpr default.
        let mut ctx = TranslationContext::new();
        let stmt = CStmt::for_loop(None, None, None, CStmt::return_stmt(Some(CExpr::int(0))));
        let expr = ctx.translate_stmt(&stmt);

        let (head, args) = spine(&expr);
        assert_eq!(const_name(&head).as_deref(), Some("CStmt.for"));
        assert_eq!(args.len(), 4);
        assert_eq!(
            const_name(&args[0]).as_deref(),
            Some("CStmt.skip"),
            "absent init uses the statement skip default"
        );
        assert_eq!(
            const_name(&args[1]).as_deref(),
            Some("CValue.unit"),
            "absent cond uses the missing-CExpr unit default"
        );
        assert_eq!(
            const_name(&args[2]).as_deref(),
            Some("CValue.unit"),
            "absent update uses the missing-CExpr unit default"
        );
    }

    #[test]
    fn test_translate_do_while_stmt_head_constant() {
        // do body while (cond);  lowers to the 2-arg `CStmt.doWhile` head with
        // body first, then cond.
        let mut ctx = TranslationContext::new();
        let stmt = CStmt::do_while(CStmt::return_stmt(Some(CExpr::int(0))), CExpr::int(1));
        let expr = ctx.translate_stmt(&stmt);

        let (head, args) = spine(&expr);
        assert_eq!(
            const_name(&head).as_deref(),
            Some("CStmt.doWhile"),
            "do-while should lower to its own uninterpreted head constant"
        );
        assert_ne!(
            const_name(&head).as_deref(),
            Some("CStmt.unsupported"),
            "do-while must no longer fall through to CStmt.unsupported"
        );
        assert_eq!(args.len(), 2, "CStmt.doWhile is applied to body and cond");
    }

    #[test]
    fn test_translate_switch_stmt_head_constant() {
        // switch (cond) body  lowers to the 2-arg `CStmt.switch` head, with the
        // controlling expression first and the body second — mirroring `while`.
        let mut ctx = TranslationContext::new();
        let stmt = CStmt::Switch {
            cond: CExpr::int(1),
            body: Box::new(CStmt::Block(vec![CStmt::break_stmt()])),
        };
        let expr = ctx.translate_stmt(&stmt);

        let (head, args) = spine(&expr);
        assert_eq!(
            const_name(&head).as_deref(),
            Some("CStmt.switch"),
            "switch should lower to its own uninterpreted head constant"
        );
        assert_ne!(
            const_name(&head).as_deref(),
            Some("CStmt.unsupported"),
            "switch must no longer fall through to CStmt.unsupported"
        );
        assert_eq!(args.len(), 2, "CStmt.switch is applied to cond and body");
        // The body sub-translation is itself faithfully reflected as a block.
        let (body_head, _) = spine(&args[1]);
        assert_eq!(const_name(&body_head).as_deref(), Some("CStmt.block"));
    }

    #[test]
    fn test_translate_case_label_stmt_head_constant() {
        // case 1: return 0;  lowers to `CStmt.case (CaseLabel.case 1) <stmt>`.
        let mut ctx = TranslationContext::new();
        let stmt = CStmt::Case {
            label: crate::stmt::CaseLabel::Case(CExpr::int(1)),
            stmt: Box::new(CStmt::return_stmt(Some(CExpr::int(0)))),
        };
        let expr = ctx.translate_stmt(&stmt);

        let (head, args) = spine(&expr);
        assert_eq!(
            const_name(&head).as_deref(),
            Some("CStmt.case"),
            "case label should lower to its own uninterpreted head constant"
        );
        assert_ne!(const_name(&head).as_deref(), Some("CStmt.unsupported"));
        assert_eq!(args.len(), 2, "CStmt.case is applied to label and stmt");

        // The label is itself a `CaseLabel.case <expr>` head applied to the
        // translated matched expression.
        let (label_head, label_args) = spine(&args[0]);
        assert_eq!(const_name(&label_head).as_deref(), Some("CaseLabel.case"));
        assert_eq!(
            label_args.len(),
            1,
            "CaseLabel.case carries the matched expr"
        );

        // The guarded statement is faithfully reflected as a `return`.
        let (stmt_head, _) = spine(&args[1]);
        assert_eq!(const_name(&stmt_head).as_deref(), Some("CStmt.return"));
    }

    #[test]
    fn test_translate_default_label_is_nullary_head() {
        // default: break;  lowers to `CStmt.case CaseLabel.default <stmt>`, with
        // the nullary `CaseLabel.default` head (no arguments).
        let mut ctx = TranslationContext::new();
        let stmt = CStmt::Case {
            label: crate::stmt::CaseLabel::Default,
            stmt: Box::new(CStmt::break_stmt()),
        };
        let expr = ctx.translate_stmt(&stmt);

        let (head, args) = spine(&expr);
        assert_eq!(const_name(&head).as_deref(), Some("CStmt.case"));
        assert_eq!(args.len(), 2);

        let (label_head, label_args) = spine(&args[0]);
        assert_eq!(
            const_name(&label_head).as_deref(),
            Some("CaseLabel.default"),
            "default label is the nullary CaseLabel.default head"
        );
        assert!(
            label_args.is_empty(),
            "CaseLabel.default takes no arguments"
        );
    }

    #[test]
    fn test_translate_goto_stmt_head_constant() {
        // goto done;  lowers to `CStmt.goto "done"`: the 1-arg head applied to
        // the target label as a string literal.
        let mut ctx = TranslationContext::new();
        let stmt = CStmt::Goto("done".to_string());
        let expr = ctx.translate_stmt(&stmt);

        let (head, args) = spine(&expr);
        assert_eq!(
            const_name(&head).as_deref(),
            Some("CStmt.goto"),
            "goto should lower to its own uninterpreted head constant"
        );
        assert_ne!(
            const_name(&head).as_deref(),
            Some("CStmt.unsupported"),
            "goto must no longer fall through to CStmt.unsupported"
        );
        assert_eq!(args.len(), 1, "CStmt.goto is applied to the target label");
        // The target label is carried verbatim as a string literal.
        assert!(
            matches!(
                args[0].kind(),
                ExprKind::Lit(clean_kernel::Literal::String(s)) if s.as_ref() == "done"
            ),
            "goto target should be the label name as a string literal, got {:?}",
            args[0].kind()
        );
    }

    #[test]
    fn test_translate_goto_distinct_targets_distinct_terms() {
        // Distinct labels must yield distinct lowered terms.
        let mut ctx = TranslationContext::new();
        let here = ctx.translate_stmt(&CStmt::Goto("L1".to_string()));
        let there = ctx.translate_stmt(&CStmt::Goto("L2".to_string()));
        assert_ne!(
            here, there,
            "goto L1 and goto L2 must lower to distinct terms"
        );
    }

    #[test]
    fn test_translate_label_stmt_head_constant() {
        // done: return 0;  lowers to `CStmt.label "done" <stmt>`, mirroring the
        // `CStmt.case` shape: a string-literal name then the nested statement.
        let mut ctx = TranslationContext::new();
        let stmt = CStmt::Label {
            name: "done".to_string(),
            stmt: Box::new(CStmt::return_stmt(Some(CExpr::int(0)))),
        };
        let expr = ctx.translate_stmt(&stmt);

        let (head, args) = spine(&expr);
        assert_eq!(
            const_name(&head).as_deref(),
            Some("CStmt.label"),
            "label should lower to its own uninterpreted head constant"
        );
        assert_ne!(
            const_name(&head).as_deref(),
            Some("CStmt.unsupported"),
            "label must no longer fall through to CStmt.unsupported"
        );
        assert_eq!(args.len(), 2, "CStmt.label is applied to name and stmt");
        // The name is carried as a string literal.
        assert!(
            matches!(
                args[0].kind(),
                ExprKind::Lit(clean_kernel::Literal::String(s)) if s.as_ref() == "done"
            ),
            "label name should be a string literal, got {:?}",
            args[0].kind()
        );
        // The guarded statement is faithfully reflected as a `return`.
        let (stmt_head, _) = spine(&args[1]);
        assert_eq!(
            const_name(&stmt_head).as_deref(),
            Some("CStmt.return"),
            "the labeled statement should be faithfully sub-translated"
        );
    }

    #[test]
    fn test_translate_compound_literal_head_constant() {
        // (struct point){1, 2}  lowers to the 2-arg `CExpr.compoundLiteral` head:
        // the translated object type first, then the initializer list. It must no
        // longer fall through to `CExpr.unsupported`.
        use crate::expr::Initializer;
        let mut ctx = TranslationContext::new();
        let e = CExpr::CompoundLiteral {
            ty: CType::int(),
            init: vec![
                Initializer::Expr(CExpr::int(1)),
                Initializer::Expr(CExpr::int(2)),
            ],
        };
        let expr = ctx.translate_expr(&e);

        let (head, args) = spine(&expr);
        assert_eq!(
            const_name(&head).as_deref(),
            Some("CExpr.compoundLiteral"),
            "compound literal should lower to its own uninterpreted head constant"
        );
        assert_ne!(
            const_name(&head).as_deref(),
            Some("CExpr.unsupported"),
            "compound literals must no longer fall through to CExpr.unsupported"
        );
        assert_eq!(
            args.len(),
            2,
            "CExpr.compoundLiteral is applied to the type and the initializer list"
        );

        // Second argument is a `List.cons` spine of translated initializers; the
        // first cell carries an `Initializer.expr` head.
        let (list_head, list_args) = spine(&args[1]);
        assert_eq!(
            const_name(&list_head).as_deref(),
            Some("List.cons"),
            "the initializer list should be a non-empty cons list"
        );
        let (elem_head, _) = spine(&list_args[0]);
        assert_eq!(
            const_name(&elem_head).as_deref(),
            Some("Initializer.expr"),
            "a simple-expression initializer reflects as Initializer.expr"
        );
    }

    #[test]
    fn test_translate_compound_literal_empty_init_is_nil() {
        // (int){} lowers with the empty initializer list as `List.nil`.
        let mut ctx = TranslationContext::new();
        let e = CExpr::CompoundLiteral {
            ty: CType::int(),
            init: vec![],
        };
        let expr = ctx.translate_expr(&e);

        let (head, args) = spine(&expr);
        assert_eq!(const_name(&head).as_deref(), Some("CExpr.compoundLiteral"));
        assert_eq!(args.len(), 2);
        assert_eq!(
            const_name(&args[1]).as_deref(),
            Some("List.nil"),
            "an empty initializer list lowers to List.nil"
        );
    }

    #[test]
    fn test_translate_compound_literal_designated_field_init() {
        // (struct s){.x = 7}  reflects a designated initializer as
        // `Initializer.designated (Designator.field "x") (Initializer.expr 7)`,
        // with the field name carried verbatim as a string literal.
        use crate::expr::{Designator, Initializer};
        let mut ctx = TranslationContext::new();
        let e = CExpr::CompoundLiteral {
            ty: CType::int(),
            init: vec![Initializer::Designated {
                designator: Designator::Field("x".to_string()),
                init: Box::new(Initializer::Expr(CExpr::int(7))),
            }],
        };
        let expr = ctx.translate_expr(&e);

        let (_, args) = spine(&expr);
        let (_, list_args) = spine(&args[1]);
        // First initializer is `Initializer.designated <designator> <init>`.
        let (init_head, init_args) = spine(&list_args[0]);
        assert_eq!(
            const_name(&init_head).as_deref(),
            Some("Initializer.designated"),
            "a designated initializer reflects as Initializer.designated"
        );
        assert_eq!(
            init_args.len(),
            2,
            "Initializer.designated is applied to a designator and an initializer"
        );
        // Designator is `Designator.field "x"`.
        let (desig_head, desig_args) = spine(&init_args[0]);
        assert_eq!(const_name(&desig_head).as_deref(), Some("Designator.field"));
        assert!(
            matches!(
                desig_args[0].kind(),
                ExprKind::Lit(clean_kernel::Literal::String(s)) if s.as_ref() == "x"
            ),
            "the designated field name should be carried as a string literal, got {:?}",
            desig_args[0].kind()
        );
        // Nested initializer is `Initializer.expr 7`.
        let (nested_head, _) = spine(&init_args[1]);
        assert_eq!(
            const_name(&nested_head).as_deref(),
            Some("Initializer.expr")
        );
    }

    #[test]
    fn test_translate_compound_literal_index_designator() {
        // (int[]){[2] = 5}  reflects an index designator as
        // `Designator.index <translated index>`, the index sub-expression being
        // faithfully translated.
        use crate::expr::{Designator, Initializer};
        let mut ctx = TranslationContext::new();
        let e = CExpr::CompoundLiteral {
            ty: CType::int(),
            init: vec![Initializer::Designated {
                designator: Designator::Index(Box::new(CExpr::int(2))),
                init: Box::new(Initializer::Expr(CExpr::int(5))),
            }],
        };
        let expr = ctx.translate_expr(&e);

        let (_, args) = spine(&expr);
        let (_, list_args) = spine(&args[1]);
        let (_, init_args) = spine(&list_args[0]);
        let (desig_head, desig_args) = spine(&init_args[0]);
        assert_eq!(
            const_name(&desig_head).as_deref(),
            Some("Designator.index"),
            "an array-index designator reflects as Designator.index"
        );
        assert_eq!(
            desig_args.len(),
            1,
            "Designator.index carries the translated index expression"
        );
        // The index `2` translates to `CValue.int (Int.ofNat 2)`.
        let (idx_head, _) = spine(&desig_args[0]);
        assert_eq!(
            const_name(&idx_head).as_deref(),
            Some("CValue.int"),
            "the designator index sub-expression should be faithfully translated"
        );
    }

    #[test]
    fn test_translate_compound_literal_nested_list_init() {
        // (int[2][2]){{1, 2}} reflects the inner brace group as
        // `Initializer.list <list>`, recursively translating its elements.
        use crate::expr::Initializer;
        let mut ctx = TranslationContext::new();
        let e = CExpr::CompoundLiteral {
            ty: CType::int(),
            init: vec![Initializer::List(vec![
                Initializer::Expr(CExpr::int(1)),
                Initializer::Expr(CExpr::int(2)),
            ])],
        };
        let expr = ctx.translate_expr(&e);

        let (_, args) = spine(&expr);
        let (_, list_args) = spine(&args[1]);
        let (init_head, init_args) = spine(&list_args[0]);
        assert_eq!(
            const_name(&init_head).as_deref(),
            Some("Initializer.list"),
            "a brace-enclosed initializer reflects as Initializer.list"
        );
        assert_eq!(
            init_args.len(),
            1,
            "Initializer.list is applied to the nested initializer list"
        );
        // The nested argument is itself a cons list of `Initializer.expr` cells.
        let (nested_list_head, nested_list_args) = spine(&init_args[0]);
        assert_eq!(const_name(&nested_list_head).as_deref(), Some("List.cons"));
        let (nested_elem_head, _) = spine(&nested_list_args[0]);
        assert_eq!(
            const_name(&nested_elem_head).as_deref(),
            Some("Initializer.expr")
        );
    }

    #[test]
    fn test_translate_forall_spec() {
        let mut ctx = TranslationContext::new();
        let spec = Spec::forall("i", CType::int(), Spec::ge(Spec::var("i"), Spec::int(0)));
        let expr = ctx.translate_spec(&spec);

        // Should produce Pi type
        assert!(matches!(expr.kind(), ExprKind::Pi(_, _, _)));
    }

    #[test]
    fn test_translate_and_spec() {
        let mut ctx = TranslationContext::new();
        let spec = Spec::and(vec![
            Spec::ge(Spec::var("x"), Spec::int(0)),
            Spec::le(Spec::var("x"), Spec::int(10)),
        ]);
        let expr = ctx.translate_spec(&spec);

        // Should produce nested And
        assert!(matches!(expr.kind(), ExprKind::App(_, _)));
    }

    /// Peel an n-ary application `f a1 a2 ...` into its head and argument list.
    /// Returns `(head, [a1, a2, ...])` in left-to-right order.
    fn spine(expr: &Expr) -> (Expr, Vec<Expr>) {
        let mut args = Vec::new();
        let mut cur = expr.clone();
        while let ExprKind::App(f, a) = cur.kind() {
            args.push((**a).clone());
            cur = (**f).clone();
        }
        args.reverse();
        (cur, args)
    }

    fn const_name(expr: &Expr) -> Option<String> {
        match expr.kind() {
            ExprKind::Const(n, _) => Some(n.to_string()),
            _ => None,
        }
    }

    #[test]
    fn test_translate_sum_spec_shape() {
        // \sum(0, n, k; a[k]) lowers to `Spec.sum 0 n (fun k => body)`.
        let mut ctx = TranslationContext::new();
        let spec = Spec::Sum {
            lo: Box::new(Spec::int(0)),
            hi: Box::new(Spec::var("n")),
            var: "k".to_string(),
            body: Box::new(Spec::var("k")),
        };
        let expr = ctx.translate_spec(&spec);

        let (head, args) = spine(&expr);
        assert_eq!(
            const_name(&head).as_deref(),
            Some("Spec.sum"),
            "aggregation head should be the named uninterpreted constant"
        );
        assert_eq!(args.len(), 3, "Spec.sum is applied to lo, hi, and a lambda");
        // Third argument is the body lambda binding the index.
        assert!(
            matches!(args[2].kind(), ExprKind::Lam(_, _, _)),
            "third argument should be `fun k => body`"
        );
    }

    #[test]
    fn test_translate_min_spec_head_constant() {
        let mut ctx = TranslationContext::new();
        let spec = Spec::Min {
            lo: Box::new(Spec::int(0)),
            hi: Box::new(Spec::var("n")),
            var: "k".to_string(),
            body: Box::new(Spec::var("k")),
        };
        let expr = ctx.translate_spec(&spec);

        let (head, args) = spine(&expr);
        assert_eq!(const_name(&head).as_deref(), Some("Spec.min"));
        assert_eq!(args.len(), 3);
    }

    #[test]
    fn test_translate_aggregation_heads_are_distinct() {
        // Each aggregation operator lowers to its own named constant.
        let mut ctx = TranslationContext::new();
        let cases = [
            (
                Spec::Product {
                    lo: Box::new(Spec::int(0)),
                    hi: Box::new(Spec::var("n")),
                    var: "k".to_string(),
                    body: Box::new(Spec::var("k")),
                },
                "Spec.product",
            ),
            (
                Spec::Max {
                    lo: Box::new(Spec::int(0)),
                    hi: Box::new(Spec::var("n")),
                    var: "k".to_string(),
                    body: Box::new(Spec::var("k")),
                },
                "Spec.max",
            ),
            (
                Spec::NumOf {
                    lo: Box::new(Spec::int(0)),
                    hi: Box::new(Spec::var("n")),
                    var: "k".to_string(),
                    body: Box::new(Spec::eq(Spec::var("k"), Spec::int(0))),
                },
                "Spec.numof",
            ),
        ];
        for (spec, expected) in cases {
            let expr = ctx.translate_spec(&spec);
            let (head, args) = spine(&expr);
            assert_eq!(
                const_name(&head).as_deref(),
                Some(expected),
                "{expected} should lower to its own head constant"
            );
            assert_eq!(args.len(), 3);
            assert!(matches!(args[2].kind(), ExprKind::Lam(_, _, _)));
        }
    }

    #[test]
    fn test_translate_numof_body_index_is_bound() {
        // The index `k` inside the body must resolve to the lambda's bound
        // variable (a bvar), not an opaque `spec.k` constant.
        let mut ctx = TranslationContext::new();
        let spec = Spec::NumOf {
            lo: Box::new(Spec::int(0)),
            hi: Box::new(Spec::var("n")),
            var: "k".to_string(),
            body: Box::new(Spec::eq(Spec::var("k"), Spec::int(0))),
        };
        let expr = ctx.translate_spec(&spec);
        let (_, args) = spine(&expr);
        let lambda = &args[2];
        let ExprKind::Lam(_, _, lam_body) = lambda.kind() else {
            panic!("expected a lambda for the aggregation body");
        };
        // Body is `Eq (bvar 0) 0`: the index occurrence must be a bound var.
        let (_, eq_args) = spine(lam_body);
        assert!(
            matches!(eq_args[0].kind(), ExprKind::BVar(_)),
            "bound index `k` should translate to a de Bruijn variable, got {:?}",
            eq_args[0].kind()
        );
    }

    #[test]
    fn test_translate_at_spec_shape() {
        // `at(x, Post)` lowers to `Spec.at <translated x> "Post"`: an
        // uninterpreted head applied to the translated expression and the
        // label name as a string literal.
        let mut ctx = TranslationContext::new();
        let spec = Spec::At {
            expr: Box::new(Spec::var("x")),
            label: "Post".to_string(),
        };
        let expr = ctx.translate_spec(&spec);

        let (head, args) = spine(&expr);
        assert_eq!(
            const_name(&head).as_deref(),
            Some("Spec.at"),
            "at(e, label) should lower to the named Spec.at head"
        );
        assert_eq!(
            args.len(),
            2,
            "Spec.at is applied to the expr and the label"
        );
        // First argument is the translated inner spec (the free variable `x`).
        assert_eq!(
            const_name(&args[0]).as_deref(),
            Some("spec.x"),
            "first argument should be the translated inner expression"
        );
        // Second argument is the label encoded as a string literal.
        assert!(
            matches!(
                args[1].kind(),
                ExprKind::Lit(clean_kernel::Literal::String(s)) if s.as_ref() == "Post"
            ),
            "second argument should be the label name as a string literal, got {:?}",
            args[1].kind()
        );
    }

    #[test]
    fn test_translate_at_named_label_preserves_label() {
        // A named (non-builtin) label is carried through verbatim, and distinct
        // labels yield distinct lowered terms.
        let mut ctx = TranslationContext::new();
        let here = ctx.translate_spec(&Spec::At {
            expr: Box::new(Spec::var("y")),
            label: "L1".to_string(),
        });
        let there = ctx.translate_spec(&Spec::At {
            expr: Box::new(Spec::var("y")),
            label: "L2".to_string(),
        });

        let (_, here_args) = spine(&here);
        let (_, _there_args) = spine(&there);
        assert!(
            matches!(
                here_args[1].kind(),
                ExprKind::Lit(clean_kernel::Literal::String(s)) if s.as_ref() == "L1"
            ),
            "named label should be preserved verbatim"
        );
        assert_ne!(
            here, there,
            "at(e, L1) and at(e, L2) must lower to distinct terms"
        );
    }

    #[test]
    fn test_translate_int_negative_one() {
        // Test a simple negative value
        let ctx = TranslationContext::new();
        let expr = ctx.translate_int(-1);

        // Should produce Int.negOfNat applied to 1
        assert!(matches!(expr.kind(), ExprKind::App(_, _)));
    }

    #[test]
    fn test_translate_int_negative_large() {
        // Test a larger negative value to ensure magnitude calculation is correct
        let ctx = TranslationContext::new();
        let expr = ctx.translate_int(-100);

        // Should produce Int.negOfNat applied to 100
        assert!(matches!(expr.kind(), ExprKind::App(_, _)));
    }

    #[test]
    fn test_translate_int_i64_min_magnitude_calculation() {
        // Verify that i64::MIN magnitude is calculated correctly without overflow.
        // We can't actually call translate_int(i64::MIN) because translate_nat
        // uses recursion and would stack overflow on such large values.
        // Instead, test the magnitude calculation logic directly.

        // For negative n, magnitude = 0u64.wrapping_sub(n as u64)
        let n = i64::MIN;
        let magnitude = 0u64.wrapping_sub(n as u64);

        // i64::MIN = -9223372036854775808
        // i64::MIN as u64 = 9223372036854775808 (two's complement)
        // 0u64.wrapping_sub(9223372036854775808) = 9223372036854775808
        assert_eq!(magnitude, 9_223_372_036_854_775_808_u64);

        // Test -1 similarly
        let n = -1i64;
        let magnitude = 0u64.wrapping_sub(n as u64);
        assert_eq!(magnitude, 1u64);

        // Test -5
        let n = -5i64;
        let magnitude = 0u64.wrapping_sub(n as u64);
        assert_eq!(magnitude, 5u64);
    }

    #[test]
    fn test_translate_valid_read_spec_shape() {
        // `\valid_read(p)` lowers to `Spec.valid_read <translated p>`: an
        // uninterpreted head applied to the translated pointer sub-spec.
        let mut ctx = TranslationContext::new();
        let spec = Spec::ValidRead(Box::new(Spec::var("p")));
        let expr = ctx.translate_spec(&spec);

        let (head, args) = spine(&expr);
        assert_eq!(
            const_name(&head).as_deref(),
            Some("Spec.valid_read"),
            "valid_read should lower to its own named head constant"
        );
        assert_eq!(args.len(), 1, "Spec.valid_read is applied to the pointer");
        assert_eq!(
            const_name(&args[0]).as_deref(),
            Some("spec.p"),
            "argument should be the translated inner pointer spec"
        );
        // A previously-unsupported predicate must no longer fall through.
        assert_ne!(const_name(&head).as_deref(), Some("Spec.unsupported"));
    }

    #[test]
    fn test_translate_valid_range_spec_shape() {
        // `\valid(p + (lo..hi))` lowers to `Spec.valid_range ptr lo hi`.
        let mut ctx = TranslationContext::new();
        let spec = Spec::ValidRange {
            ptr: Box::new(Spec::var("p")),
            lo: Box::new(Spec::int(0)),
            hi: Box::new(Spec::var("n")),
        };
        let expr = ctx.translate_spec(&spec);

        let (head, args) = spine(&expr);
        assert_eq!(
            const_name(&head).as_deref(),
            Some("Spec.valid_range"),
            "valid_range should lower to its own named head constant"
        );
        assert_eq!(
            args.len(),
            3,
            "Spec.valid_range is applied to ptr, lo, and hi"
        );
        // First argument is the translated pointer; the spine preserves order.
        assert_eq!(
            const_name(&args[0]).as_deref(),
            Some("spec.p"),
            "first argument should be the translated pointer spec"
        );
        assert_ne!(const_name(&head).as_deref(), Some("Spec.unsupported"));
    }

    #[test]
    fn test_translate_separated_spec_shape() {
        // `\separated(p, q, r)` lowers to `Spec.separated [p, q, r]`: the
        // head applied to a `List.cons`/`List.nil` list of translated specs.
        let mut ctx = TranslationContext::new();
        let spec = Spec::Separated(vec![Spec::var("p"), Spec::var("q"), Spec::var("r")]);
        let expr = ctx.translate_spec(&spec);

        let (head, args) = spine(&expr);
        assert_eq!(
            const_name(&head).as_deref(),
            Some("Spec.separated"),
            "separated should lower to its own named head constant"
        );
        assert_eq!(args.len(), 1, "Spec.separated is applied to a single list");

        // The single argument must be a `List.cons` spine ending in `List.nil`,
        // with the first cell carrying the first translated pointer `spec.p`.
        let (list_head, list_args) = spine(&args[0]);
        assert_eq!(
            const_name(&list_head).as_deref(),
            Some("List.cons"),
            "the argument should be a non-empty cons list of pointers"
        );
        assert_eq!(
            const_name(&list_args[0]).as_deref(),
            Some("spec.p"),
            "the first list element should be the translated first pointer"
        );
        assert_ne!(const_name(&head).as_deref(), Some("Spec.unsupported"));
    }

    #[test]
    fn test_translate_fresh_spec_shape() {
        // `\fresh(p)` lowers to `Spec.fresh <translated p>`.
        let mut ctx = TranslationContext::new();
        let spec = Spec::Fresh(Box::new(Spec::var("p")));
        let expr = ctx.translate_spec(&spec);

        let (head, args) = spine(&expr);
        assert_eq!(
            const_name(&head).as_deref(),
            Some("Spec.fresh"),
            "fresh should lower to its own named head constant"
        );
        assert_eq!(args.len(), 1, "Spec.fresh is applied to the pointer");
        assert_eq!(
            const_name(&args[0]).as_deref(),
            Some("spec.p"),
            "argument should be the translated inner pointer spec"
        );
        assert_ne!(const_name(&head).as_deref(), Some("Spec.unsupported"));
    }

    #[test]
    fn test_translate_iff_spec_shape() {
        // `P <==> Q` lowers to `Spec.iff <translated P> <translated Q>`.
        let mut ctx = TranslationContext::new();
        let spec = Spec::Iff(Box::new(Spec::var("p")), Box::new(Spec::var("q")));
        let expr = ctx.translate_spec(&spec);

        let (head, args) = spine(&expr);
        assert_eq!(
            const_name(&head).as_deref(),
            Some("Spec.iff"),
            "iff should lower to its own named head constant"
        );
        assert_eq!(args.len(), 2, "Spec.iff is applied to both operands");
        assert_eq!(
            const_name(&args[0]).as_deref(),
            Some("spec.p"),
            "first argument should be the translated left operand"
        );
        assert_eq!(
            const_name(&args[1]).as_deref(),
            Some("spec.q"),
            "second argument should be the translated right operand"
        );
        assert_ne!(const_name(&head).as_deref(), Some("Spec.unsupported"));
    }

    #[test]
    fn test_translate_memory_safety_heads_are_distinct() {
        // Each ACSL memory-safety predicate lowers to its own head constant,
        // and none of them collapse to the `Spec.unsupported` fallback.
        let mut ctx = TranslationContext::new();
        let cases = [
            (Spec::ValidRead(Box::new(Spec::var("p"))), "Spec.valid_read"),
            (Spec::Fresh(Box::new(Spec::var("p"))), "Spec.fresh"),
            (
                Spec::ValidRange {
                    ptr: Box::new(Spec::var("p")),
                    lo: Box::new(Spec::int(0)),
                    hi: Box::new(Spec::var("n")),
                },
                "Spec.valid_range",
            ),
            (
                Spec::Separated(vec![Spec::var("p"), Spec::var("q")]),
                "Spec.separated",
            ),
            (
                Spec::Iff(Box::new(Spec::var("p")), Box::new(Spec::var("q"))),
                "Spec.iff",
            ),
        ];
        for (spec, expected) in cases {
            let expr = ctx.translate_spec(&spec);
            let (head, _) = spine(&expr);
            assert_eq!(
                const_name(&head).as_deref(),
                Some(expected),
                "{expected} should lower to its own head constant, not the fallback"
            );
        }
    }
}

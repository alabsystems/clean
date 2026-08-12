// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! L5IR constant folding: evaluates compile-time-known expressions at the
//! low-level IR stage (after boxing/RC), complementing the L5CNF-level
//! `opt::constant_fold`. Supports Nat arithmetic, Bool logic, String concat,
//! and conditional elimination.
//!
//! Part of #3084 - IO/FFI/Native epic.

use crate::ir::{FnId, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRLiteral, VarId};
use std::collections::HashMap;

/// Configuration for the L5IR constant folding pass.
#[derive(Debug, Clone)]
pub(crate) struct ConstFoldConfig {
    /// Fold arithmetic operations on integer literals.
    pub fold_arithmetic: bool,
    /// Fold boolean logic operations.
    pub fold_boolean: bool,
    /// Fold string concatenation.
    pub fold_string: bool,
    /// Eliminate branches with compile-time-known scrutinees.
    pub fold_conditionals: bool,
    /// Maximum length for folded string results (prevents blowup).
    pub max_string_length: usize,
}

impl Default for ConstFoldConfig {
    fn default() -> Self {
        Self {
            fold_arithmetic: true,
            fold_boolean: true,
            fold_string: true,
            fold_conditionals: true,
            max_string_length: 4096,
        }
    }
}

/// Statistics collected during constant folding.
#[derive(Debug, Clone, Default)]
pub(crate) struct ConstFoldStats {
    /// Number of arithmetic operations folded.
    pub folded_arithmetic: usize,
    /// Number of boolean operations folded.
    pub folded_boolean: usize,
    /// Number of string operations folded.
    pub folded_string: usize,
    /// Number of conditionals eliminated.
    pub folded_conditionals: usize,
}

impl ConstFoldStats {
    /// Total number of expressions folded.
    pub fn total_folded(&self) -> usize {
        self.folded_arithmetic + self.folded_boolean + self.folded_string + self.folded_conditionals
    }
}

/// A compile-time-known value tracked during folding.
#[derive(Clone, Debug)]
pub(crate) enum KnownValue {
    Lit(IRLiteral),
    Bool(bool),
    String(String),
    Tag(u32),
}

/// Tracks known values for variables during folding.
pub(crate) struct KnownValues {
    bindings: HashMap<u32, KnownValue>,
}

impl KnownValues {
    pub(crate) fn new() -> Self {
        Self {
            bindings: HashMap::new(),
        }
    }

    pub(crate) fn insert(&mut self, var: VarId, value: KnownValue) {
        self.bindings.insert(var.0, value);
    }

    pub(crate) fn get(&self, var: VarId) -> Option<&KnownValue> {
        self.bindings.get(&var.0)
    }

    fn get_arg_u64(&self, arg: &IRArg) -> Option<u64> {
        match arg {
            IRArg::Var(v) => match self.get(*v)? {
                KnownValue::Lit(IRLiteral::UInt64(n)) => Some(*n),
                _ => None,
            },
            IRArg::Erased => None,
        }
    }

    fn get_arg_bool(&self, arg: &IRArg) -> Option<bool> {
        match arg {
            IRArg::Var(v) => match self.get(*v)? {
                KnownValue::Bool(b) => Some(*b),
                KnownValue::Lit(IRLiteral::Bool(b)) => Some(*b),
                _ => None,
            },
            IRArg::Erased => None,
        }
    }

    fn get_arg_string(&self, arg: &IRArg) -> Option<&str> {
        match arg {
            IRArg::Var(v) => match self.get(*v)? {
                KnownValue::String(s) => Some(s.as_str()),
                _ => None,
            },
            IRArg::Erased => None,
        }
    }
}

/// Try to fold an arithmetic operation on two u64 operands.
///
/// Returns `None` if the operation overflows or divides by zero,
/// preserving the original expression for runtime evaluation.
pub(crate) fn fold_arithmetic(op: &str, lhs: u64, rhs: u64) -> Option<u64> {
    match op {
        "Nat.add" => lhs.checked_add(rhs),
        "Nat.sub" => Some(lhs.saturating_sub(rhs)),
        "Nat.mul" => lhs.checked_mul(rhs),
        "Nat.div" => lhs.checked_div(rhs),
        "Nat.mod" => lhs.checked_rem(rhs),
        _ => None,
    }
}

/// Try to fold an arithmetic comparison on two u64 operands.
pub(crate) fn fold_nat_comparison(op: &str, lhs: u64, rhs: u64) -> Option<bool> {
    match op {
        "Nat.beq" => Some(lhs == rhs),
        "Nat.ble" => Some(lhs <= rhs),
        "Nat.blt" => Some(lhs < rhs),
        _ => None,
    }
}

/// Try to fold a boolean operation.
pub(crate) fn fold_boolean(op: &str, args: &[IRArg], known: &KnownValues) -> Option<bool> {
    match op {
        "Bool.and" | "Bool.true.and" if args.len() == 2 => {
            let a = known.get_arg_bool(&args[0])?;
            let b = known.get_arg_bool(&args[1])?;
            Some(a && b)
        }
        "Bool.or" | "Bool.true.or" if args.len() == 2 => {
            let a = known.get_arg_bool(&args[0])?;
            let b = known.get_arg_bool(&args[1])?;
            Some(a || b)
        }
        "Bool.not" if args.len() == 1 => {
            let a = known.get_arg_bool(&args[0])?;
            Some(!a)
        }
        _ => None,
    }
}

/// Try to fold a string operation.
pub(crate) fn fold_string_op(
    op: &str,
    args: &[IRArg],
    known: &KnownValues,
    max_len: usize,
) -> Option<String> {
    match op {
        "String.append" if args.len() == 2 => {
            let a = known.get_arg_string(&args[0])?;
            let b = known.get_arg_string(&args[1])?;
            let result_len = a.len().checked_add(b.len())?;
            if result_len > max_len {
                return None;
            }
            Some(format!("{}{}", a, b))
        }
        _ => None,
    }
}

/// Try to fold an `IRExpr::Apply` into a simpler expression.
fn try_fold_apply(
    fn_id: &FnId,
    args: &[IRArg],
    known: &KnownValues,
    config: &ConstFoldConfig,
    stats: &mut ConstFoldStats,
) -> Option<IRExpr> {
    let name_str = fn_id.0.to_string();

    // Arithmetic folding
    if config.fold_arithmetic {
        if let Some(result) = try_fold_arith_apply(&name_str, args, known) {
            stats.folded_arithmetic += 1;
            return Some(result);
        }
    }

    // Boolean folding
    if config.fold_boolean {
        if let Some(result) = fold_boolean(&name_str, args, known) {
            stats.folded_boolean += 1;
            return Some(IRExpr::Lit(IRLiteral::Bool(result)));
        }
    }

    // String folding
    if config.fold_string {
        if let Some(result) = fold_string_op(&name_str, args, known, config.max_string_length) {
            stats.folded_string += 1;
            return Some(IRExpr::String(result));
        }
    }

    None
}

/// Try to fold an arithmetic apply (either pure arithmetic or comparison).
fn try_fold_arith_apply(name_str: &str, args: &[IRArg], known: &KnownValues) -> Option<IRExpr> {
    if args.len() != 2 {
        return None;
    }

    let lhs = known.get_arg_u64(&args[0])?;
    let rhs = known.get_arg_u64(&args[1])?;

    // Try pure arithmetic first
    if let Some(result) = fold_arithmetic(name_str, lhs, rhs) {
        return Some(IRExpr::Lit(IRLiteral::UInt64(result)));
    }

    // Try comparison
    if let Some(result) = fold_nat_comparison(name_str, lhs, rhs) {
        return Some(IRExpr::Lit(IRLiteral::Bool(result)));
    }

    None
}

/// Fold an expression, returning a replacement if folding succeeded.
pub(crate) fn fold_expr(
    expr: &IRExpr,
    known: &KnownValues,
    config: &ConstFoldConfig,
    stats: &mut ConstFoldStats,
) -> IRExpr {
    match expr {
        IRExpr::Apply { fn_id, args } => {
            if let Some(folded) = try_fold_apply(fn_id, args, known, config, stats) {
                folded
            } else {
                expr.clone()
            }
        }
        _ => expr.clone(),
    }
}

/// Record known value from an expression into the known-values map.
fn record_known(var: VarId, expr: &IRExpr, known: &mut KnownValues) {
    match expr {
        IRExpr::Lit(lit) => {
            if let IRLiteral::Bool(b) = lit {
                known.insert(var, KnownValue::Bool(*b));
            }
            known.insert(var, KnownValue::Lit(lit.clone()));
        }
        IRExpr::String(s) => {
            known.insert(var, KnownValue::String(s.clone()));
        }
        IRExpr::Ctor { info, .. } => {
            known.insert(var, KnownValue::Tag(info.tag));
        }
        _ => {}
    }
}

/// Fold constant expressions within an IR body.
pub(crate) fn fold_body(
    body: &IRBody,
    known: &mut KnownValues,
    config: &ConstFoldConfig,
    stats: &mut ConstFoldStats,
) -> IRBody {
    match body {
        IRBody::VDecl {
            var,
            ty,
            value,
            rest,
        } => {
            let new_value = fold_expr(value, known, config, stats);
            record_known(*var, &new_value, known);
            IRBody::VDecl {
                var: *var,
                ty: ty.clone(),
                value: new_value,
                rest: Box::new(fold_body(rest, known, config, stats)),
            }
        }

        IRBody::JDecl {
            jp,
            params,
            body: jp_body,
            rest,
        } => {
            // Fold inside join point body with a separate scope
            let mut jp_known = KnownValues {
                bindings: known.bindings.clone(),
            };
            let new_jp_body = fold_body(jp_body, &mut jp_known, config, stats);
            IRBody::JDecl {
                jp: *jp,
                params: params.clone(),
                body: Box::new(new_jp_body),
                rest: Box::new(fold_body(rest, known, config, stats)),
            }
        }

        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => {
            // Try conditional elimination
            if config.fold_conditionals {
                if let Some(tag) = known.get(VarId(scrutinee.0)).and_then(|v| match v {
                    KnownValue::Tag(t) => Some(*t),
                    _ => None,
                }) {
                    // Find matching alternative
                    for alt in alts {
                        if alt.ctor.tag == tag {
                            stats.folded_conditionals += 1;
                            let mut alt_known = KnownValues {
                                bindings: known.bindings.clone(),
                            };
                            return fold_body(&alt.body, &mut alt_known, config, stats);
                        }
                    }
                }
            }

            // Cannot eliminate — fold each branch independently
            let new_alts: Vec<IRAlt> = alts
                .iter()
                .map(|alt| {
                    let mut alt_known = KnownValues {
                        bindings: known.bindings.clone(),
                    };
                    IRAlt {
                        ctor: alt.ctor.clone(),
                        body: Box::new(fold_body(&alt.body, &mut alt_known, config, stats)),
                    }
                })
                .collect();

            let new_default = default.as_ref().map(|d| {
                let mut def_known = KnownValues {
                    bindings: known.bindings.clone(),
                };
                Box::new(fold_body(d, &mut def_known, config, stats))
            });

            IRBody::Case {
                scrutinee: *scrutinee,
                alts: new_alts,
                default: new_default,
            }
        }

        IRBody::Inc { var, n, rest } => IRBody::Inc {
            var: *var,
            n: *n,
            rest: Box::new(fold_body(rest, known, config, stats)),
        },

        IRBody::Dec { var, rest } => IRBody::Dec {
            var: *var,
            rest: Box::new(fold_body(rest, known, config, stats)),
        },

        IRBody::Set {
            var,
            idx,
            value,
            rest,
        } => IRBody::Set {
            var: *var,
            idx: *idx,
            value: *value,
            rest: Box::new(fold_body(rest, known, config, stats)),
        },

        IRBody::SetTag { var, tag, rest } => IRBody::SetTag {
            var: *var,
            tag: *tag,
            rest: Box::new(fold_body(rest, known, config, stats)),
        },

        IRBody::USet {
            var,
            idx,
            value,
            rest,
        } => IRBody::USet {
            var: *var,
            idx: *idx,
            value: *value,
            rest: Box::new(fold_body(rest, known, config, stats)),
        },

        IRBody::SSet {
            var,
            n,
            offset,
            value,
            ty,
            rest,
        } => IRBody::SSet {
            var: *var,
            n: *n,
            offset: *offset,
            value: *value,
            ty: ty.clone(),
            rest: Box::new(fold_body(rest, known, config, stats)),
        },

        // Terminal nodes — no folding needed
        IRBody::Jmp { jp, args } => IRBody::Jmp {
            jp: *jp,
            args: args.clone(),
        },
        IRBody::Ret(arg) => IRBody::Ret(arg.clone()),
        IRBody::Unreachable => IRBody::Unreachable,
    }
}

/// Run the constant folding pass over a single IR declaration.
pub(crate) fn fold_decl(
    decl: &IRDecl,
    config: &ConstFoldConfig,
    stats: &mut ConstFoldStats,
) -> IRDecl {
    let mut known = KnownValues::new();
    let new_body = fold_body(&decl.body, &mut known, config, stats);
    IRDecl {
        name: decl.name.clone(),
        params: decl.params.clone(),
        return_type: decl.return_type.clone(),
        body: new_body,
    }
}

/// Run the L5IR constant folding pass over a set of declarations.
///
/// Returns the folded declarations and statistics about what was folded.
pub(crate) fn run_const_fold(
    decls: &[IRDecl],
    config: &ConstFoldConfig,
) -> (Vec<IRDecl>, ConstFoldStats) {
    let mut stats = ConstFoldStats::default();
    let folded = decls
        .iter()
        .map(|decl| fold_decl(decl, config, &mut stats))
        .collect();
    (folded, stats)
}

/// Run the L5IR constant folding pass with default configuration.
pub(crate) fn run_const_fold_default(decls: &[IRDecl]) -> (Vec<IRDecl>, ConstFoldStats) {
    run_const_fold(decls, &ConstFoldConfig::default())
}

#[cfg(test)]
#[path = "const_fold_tests.rs"]
mod tests;

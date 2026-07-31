// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended constant folding for L5IR: arithmetic, string, comparison,
//! bitwise operations, forward constant propagation, and branch elimination.
//!
//! Extends `const_fold` with fixpoint iteration, Int (signed) arithmetic,
//! bitwise operations, richer string ops (length, isEmpty, append), and
//! forward propagation of known variable bindings into downstream uses.
//!
//! Part of #3084 - IO/FFI/Native epic.

use crate::ir::{FnId, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRLiteral, VarId};
use std::collections::HashMap;

/// Configuration for the extended constant folding pass.
#[derive(Debug, Clone)]
pub(crate) struct ConstFoldExtConfig {
    pub(crate) fold_arithmetic: bool,
    pub(crate) fold_string_ops: bool,
    pub(crate) fold_comparisons: bool,
    pub(crate) fold_bitwise: bool,
    pub(crate) max_string_length: usize,
    pub(crate) max_iterations: usize,
}

impl Default for ConstFoldExtConfig {
    fn default() -> Self {
        Self {
            fold_arithmetic: true,
            fold_string_ops: true,
            fold_comparisons: true,
            fold_bitwise: true,
            max_string_length: 1024,
            max_iterations: 10,
        }
    }
}

/// Statistics collected during extended constant folding.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct ConstFoldExtStats {
    pub(crate) arithmetic_folds: usize,
    pub(crate) string_folds: usize,
    pub(crate) comparison_folds: usize,
    pub(crate) bitwise_folds: usize,
    pub(crate) branch_folds: usize,
    pub(crate) iterations: usize,
}

impl ConstFoldExtStats {
    pub(crate) fn total(&self) -> usize {
        self.arithmetic_folds
            + self.string_folds
            + self.comparison_folds
            + self.bitwise_folds
            + self.branch_folds
    }
    fn merge(&mut self, other: &Self) {
        self.arithmetic_folds += other.arithmetic_folds;
        self.string_folds += other.string_folds;
        self.comparison_folds += other.comparison_folds;
        self.bitwise_folds += other.bitwise_folds;
        self.branch_folds += other.branch_folds;
    }
}

// -- Known-value tracking ---------------------------------------------------

#[derive(Clone, Debug)]
enum KnownVal {
    Lit(IRLiteral),
    Str(String),
    Tag(u32),
}

struct KnownExt {
    vars: HashMap<VarId, KnownVal>,
}

impl KnownExt {
    fn new() -> Self {
        Self {
            vars: HashMap::new(),
        }
    }
    fn insert_from_expr(&mut self, var: VarId, expr: &IRExpr) {
        match expr {
            IRExpr::Lit(lit) => {
                self.vars.insert(var, KnownVal::Lit(lit.clone()));
            }
            IRExpr::String(s) => {
                self.vars.insert(var, KnownVal::Str(s.clone()));
            }
            IRExpr::Ctor { info, .. } => {
                self.vars.insert(var, KnownVal::Tag(info.tag));
            }
            _ => {}
        }
    }
    fn get_lit(&self, arg: &IRArg) -> Option<&IRLiteral> {
        match arg {
            IRArg::Var(v) => match self.vars.get(v)? {
                KnownVal::Lit(l) => Some(l),
                _ => None,
            },
            IRArg::Erased => None,
        }
    }
    fn get_string(&self, arg: &IRArg) -> Option<&str> {
        match arg {
            IRArg::Var(v) => match self.vars.get(v)? {
                KnownVal::Str(s) => Some(s),
                _ => None,
            },
            IRArg::Erased => None,
        }
    }
    fn get_tag(&self, var: VarId) -> Option<u32> {
        match self.vars.get(&var)? {
            KnownVal::Tag(t) => Some(*t),
            _ => None,
        }
    }
    fn clone_scope(&self) -> Self {
        Self {
            vars: self.vars.clone(),
        }
    }
}

// -- Pure folding helpers ---------------------------------------------------

/// Evaluate Nat or Int arithmetic on two integer operands.
///
/// `Nat` and `Int` are **unbounded** (bignum) in the kernel/runtime and never
/// wrap. Const-fold is limited to operands carried in a machine `u64`, so each
/// arm computes the EXACT value when representable and DECLINES (`None`)
/// otherwise — a wrapped result would be a miscompilation. In particular the
/// `Int.div`/`Int.mod` arms use `checked_div`/`checked_rem` so the lone signed
/// overflow `i64::MIN / -1` (true quotient `2^63`, not `i64`-representable)
/// declines rather than wrapping back to `i64::MIN`.
pub(crate) fn fold_arithmetic_op(op: &str, lhs: &IRLiteral, rhs: &IRLiteral) -> Option<IRLiteral> {
    let (l, r) = extract_u64_pair(lhs, rhs)?;
    let result = match op {
        "Nat.add" => l.checked_add(r)?,
        "Nat.sub" => l.saturating_sub(r),
        "Nat.mul" => l.checked_mul(r)?,
        "Nat.div" => l.checked_div(r)?,
        "Nat.mod" => l.checked_rem(r)?,
        "Int.add" => (l as i64).checked_add(r as i64)? as u64,
        "Int.sub" => (l as i64).checked_sub(r as i64)? as u64,
        "Int.mul" => (l as i64).checked_mul(r as i64)? as u64,
        "Int.div" if r != 0 => (l as i64).checked_div(r as i64)? as u64,
        "Int.mod" if r != 0 => (l as i64).checked_rem(r as i64)? as u64,
        _ => return None,
    };
    Some(IRLiteral::UInt64(result))
}

/// String fold via `KnownExt`. Returns `IRExpr::String` for concat,
/// `IRExpr::Lit` for length/isEmpty.
fn fold_string_apply(op: &str, args: &[IRArg], known: &KnownExt, max_len: usize) -> Option<IRExpr> {
    match op {
        "String.append" if args.len() == 2 => {
            let (a, b) = (known.get_string(&args[0])?, known.get_string(&args[1])?);
            if a.len().checked_add(b.len())? > max_len {
                return None;
            }
            Some(IRExpr::String(format!("{a}{b}")))
        }
        "String.length" if args.len() == 1 => {
            let s = known.get_string(&args[0])?;
            Some(IRExpr::Lit(IRLiteral::UInt64(s.len() as u64)))
        }
        "String.isEmpty" if args.len() == 1 => {
            let s = known.get_string(&args[0])?;
            Some(IRExpr::Lit(IRLiteral::Bool(s.is_empty())))
        }
        _ => None,
    }
}

/// Evaluate a comparison on two integer operands.
pub(crate) fn fold_comparison(op: &str, lhs: &IRLiteral, rhs: &IRLiteral) -> Option<bool> {
    let (l, r) = extract_u64_pair(lhs, rhs)?;
    match op {
        "Nat.beq" | "UInt64.beq" => Some(l == r),
        "Nat.ble" | "UInt64.ble" => Some(l <= r),
        "Nat.blt" | "UInt64.blt" => Some(l < r),
        "Int.beq" => Some((l as i64) == (r as i64)),
        "Int.ble" => Some((l as i64) <= (r as i64)),
        "Int.blt" => Some((l as i64) < (r as i64)),
        _ => None,
    }
}

/// Evaluate a bitwise operation on two `u64` operands.
pub(crate) fn fold_bitwise_op(op: &str, lhs: &IRLiteral, rhs: &IRLiteral) -> Option<IRLiteral> {
    let (l, r) = extract_u64_pair(lhs, rhs)?;
    let result = match op {
        "UInt64.land" => l & r,
        "UInt64.lor" => l | r,
        "UInt64.lxor" | "UInt64.xor" => l ^ r,
        "UInt64.shiftLeft" => l.checked_shl(r as u32).unwrap_or(0),
        "UInt64.shiftRight" => l.checked_shr(r as u32).unwrap_or(0),
        _ => return None,
    };
    Some(IRLiteral::UInt64(result))
}

/// Attempt to evaluate a pure `IRExpr` to a literal.
pub(crate) fn try_fold_expr(expr: &IRExpr) -> Option<IRLiteral> {
    match expr {
        IRExpr::Lit(lit) => Some(lit.clone()),
        _ => None,
    }
}

// -- Forward constant propagation -------------------------------------------

/// Walk body, track literal VDecl bindings, propagate into rest.
pub(crate) fn propagate_constants(body: &mut IRBody, known: &HashMap<VarId, IRLiteral>) {
    propagate_inner(body, &mut known.clone());
}

fn propagate_inner(body: &mut IRBody, known: &mut HashMap<VarId, IRLiteral>) {
    match body {
        IRBody::VDecl {
            var, value, rest, ..
        } => {
            if let IRExpr::Lit(lit) = value {
                known.insert(*var, lit.clone());
            }
            propagate_inner(rest, known);
        }
        IRBody::JDecl { body: jp, rest, .. } => {
            propagate_inner(jp, &mut known.clone());
            propagate_inner(rest, known);
        }
        IRBody::Case { alts, default, .. } => {
            for alt in alts.iter_mut() {
                propagate_inner(&mut alt.body, &mut known.clone());
            }
            if let Some(d) = default.as_mut() {
                propagate_inner(d, &mut known.clone());
            }
        }
        _ => {
            if let Some(rest) = rest_of_body_mut(body) {
                propagate_inner(rest, known);
            }
        }
    }
}

// -- Branch folding ---------------------------------------------------------

/// Eliminate branches whose scrutinee has a known literal tag value.
pub(crate) fn fold_known_branch(body: &mut IRBody, known: &HashMap<VarId, IRLiteral>) -> usize {
    let mut count = 0;
    fold_branch_inner(body, known, &mut count);
    count
}

fn fold_branch_inner(body: &mut IRBody, known: &HashMap<VarId, IRLiteral>, count: &mut usize) {
    match body {
        IRBody::VDecl {
            var, value, rest, ..
        } => {
            let mut nk = known.clone();
            if let IRExpr::Lit(lit) = value {
                nk.insert(*var, lit.clone());
            }
            fold_branch_inner(rest, &nk, count);
        }
        IRBody::JDecl { body: jp, rest, .. } => {
            fold_branch_inner(jp, known, count);
            fold_branch_inner(rest, known, count);
        }
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => {
            let tag = match known.get(scrutinee) {
                Some(IRLiteral::Bool(b)) => Some(u32::from(*b)),
                Some(IRLiteral::UInt64(v)) => Some(*v as u32),
                _ => None,
            };
            if let Some(t) = tag {
                if let Some(alt) = alts.iter().find(|a| a.ctor.tag == t) {
                    *count += 1;
                    let mut replacement = *alt.body.clone();
                    fold_branch_inner(&mut replacement, known, count);
                    *body = replacement;
                    return;
                }
            }
            for alt in alts.iter_mut() {
                fold_branch_inner(&mut alt.body, known, count);
            }
            if let Some(d) = default.as_mut() {
                fold_branch_inner(d, known, count);
            }
        }
        _ => {
            if let Some(rest) = rest_of_body_mut(body) {
                fold_branch_inner(rest, known, count);
            }
        }
    }
}

// -- Full single-pass fold --------------------------------------------------

fn fold_apply_ext(
    fn_id: &FnId,
    args: &[IRArg],
    known: &KnownExt,
    config: &ConstFoldExtConfig,
    stats: &mut ConstFoldExtStats,
) -> Option<IRExpr> {
    let name = fn_id.0.to_string();
    if config.fold_arithmetic && args.len() == 2 {
        if let (Some(l), Some(r)) = (known.get_lit(&args[0]), known.get_lit(&args[1])) {
            if let Some(v) = fold_arithmetic_op(&name, l, r) {
                stats.arithmetic_folds += 1;
                return Some(IRExpr::Lit(v));
            }
        }
    }
    if config.fold_comparisons && args.len() == 2 {
        if let (Some(l), Some(r)) = (known.get_lit(&args[0]), known.get_lit(&args[1])) {
            if let Some(v) = fold_comparison(&name, l, r) {
                stats.comparison_folds += 1;
                return Some(IRExpr::Lit(IRLiteral::Bool(v)));
            }
        }
    }
    if config.fold_bitwise && args.len() == 2 {
        if let (Some(l), Some(r)) = (known.get_lit(&args[0]), known.get_lit(&args[1])) {
            if let Some(v) = fold_bitwise_op(&name, l, r) {
                stats.bitwise_folds += 1;
                return Some(IRExpr::Lit(v));
            }
        }
    }
    if config.fold_string_ops {
        if let Some(v) = fold_string_apply(&name, args, known, config.max_string_length) {
            stats.string_folds += 1;
            return Some(v);
        }
    }
    None
}

fn fold_body_ext(
    body: &IRBody,
    known: &mut KnownExt,
    config: &ConstFoldExtConfig,
    stats: &mut ConstFoldExtStats,
) -> IRBody {
    match body {
        IRBody::VDecl {
            var,
            ty,
            value,
            rest,
        } => {
            let new_value = match value {
                IRExpr::Apply { fn_id, args } => fold_apply_ext(fn_id, args, known, config, stats)
                    .unwrap_or_else(|| value.clone()),
                _ => value.clone(),
            };
            known.insert_from_expr(*var, &new_value);
            IRBody::VDecl {
                var: *var,
                ty: ty.clone(),
                value: new_value,
                rest: Box::new(fold_body_ext(rest, known, config, stats)),
            }
        }
        IRBody::JDecl {
            jp,
            params,
            body: jp_body,
            rest,
        } => {
            let mut jk = known.clone_scope();
            IRBody::JDecl {
                jp: *jp,
                params: params.clone(),
                body: Box::new(fold_body_ext(jp_body, &mut jk, config, stats)),
                rest: Box::new(fold_body_ext(rest, known, config, stats)),
            }
        }
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => {
            if let Some(tag) = known.get_tag(*scrutinee) {
                for alt in alts {
                    if alt.ctor.tag == tag {
                        stats.branch_folds += 1;
                        return fold_body_ext(&alt.body, &mut known.clone_scope(), config, stats);
                    }
                }
            }
            let new_alts = alts
                .iter()
                .map(|alt| {
                    let mut ak = known.clone_scope();
                    IRAlt {
                        ctor: alt.ctor.clone(),
                        body: Box::new(fold_body_ext(&alt.body, &mut ak, config, stats)),
                    }
                })
                .collect();
            let new_def = default
                .as_ref()
                .map(|d| Box::new(fold_body_ext(d, &mut known.clone_scope(), config, stats)));
            IRBody::Case {
                scrutinee: *scrutinee,
                alts: new_alts,
                default: new_def,
            }
        }
        IRBody::Inc { var, n, rest } => IRBody::Inc {
            var: *var,
            n: *n,
            rest: Box::new(fold_body_ext(rest, known, config, stats)),
        },
        IRBody::Dec { var, rest } => IRBody::Dec {
            var: *var,
            rest: Box::new(fold_body_ext(rest, known, config, stats)),
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
            rest: Box::new(fold_body_ext(rest, known, config, stats)),
        },
        IRBody::SetTag { var, tag, rest } => IRBody::SetTag {
            var: *var,
            tag: *tag,
            rest: Box::new(fold_body_ext(rest, known, config, stats)),
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
            rest: Box::new(fold_body_ext(rest, known, config, stats)),
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
            rest: Box::new(fold_body_ext(rest, known, config, stats)),
        },
        IRBody::Jmp { jp, args } => IRBody::Jmp {
            jp: *jp,
            args: args.clone(),
        },
        IRBody::Ret(arg) => IRBody::Ret(arg.clone()),
        IRBody::Unreachable => IRBody::Unreachable,
    }
}

// -- Top-level entry points -------------------------------------------------

/// Run extended constant folding to fixpoint over declarations.
pub(crate) fn fold_constants_ext(
    decls: &mut [IRDecl],
    config: &ConstFoldExtConfig,
) -> ConstFoldExtStats {
    let mut total = ConstFoldExtStats::default();
    for iteration in 0..config.max_iterations {
        let mut iter_stats = ConstFoldExtStats::default();
        for decl in decls.iter_mut() {
            let mut known = KnownExt::new();
            decl.body = fold_body_ext(&decl.body, &mut known, config, &mut iter_stats);
        }
        total.merge(&iter_stats);
        total.iterations = iteration + 1;
        if iter_stats.total() == 0 {
            break;
        }
    }
    total
}

/// Run extended constant folding with default configuration.
pub(crate) fn fold_constants_ext_default(decls: &mut [IRDecl]) -> ConstFoldExtStats {
    fold_constants_ext(decls, &ConstFoldExtConfig::default())
}

// -- Helpers ----------------------------------------------------------------

fn extract_u64_pair(lhs: &IRLiteral, rhs: &IRLiteral) -> Option<(u64, u64)> {
    Some((extract_u64(lhs)?, extract_u64(rhs)?))
}

fn extract_u64(lit: &IRLiteral) -> Option<u64> {
    match lit {
        IRLiteral::UInt64(v) => Some(*v),
        IRLiteral::UInt32(v) => Some(*v as u64),
        IRLiteral::UInt16(v) => Some(*v as u64),
        IRLiteral::UInt8(v) => Some(*v as u64),
        IRLiteral::USize(v) => Some(*v as u64),
        _ => None,
    }
}

/// Extract a mutable reference to the `rest` continuation of pass-through
/// body nodes (Inc, Dec, Set, SetTag, USet, SSet). Returns `None` for
/// non-continuation nodes.
fn rest_of_body_mut(body: &mut IRBody) -> Option<&mut IRBody> {
    match body {
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => Some(rest),
        _ => None,
    }
}

#[cfg(test)]
#[path = "const_fold_ext_tests.rs"]
mod tests;

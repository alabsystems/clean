// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended native evaluation: profiling, tracing, budget control, and analysis.
//!
//! Part of #3084 - Native type compilation for UInt and Float.

use std::collections::HashMap;
use std::fmt;

use crate::native_eval::{eval_native, NativeEvalError, NativeValue};
use crate::native_types::{NativeExpr, NativeType};
use thiserror::Error;

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

#[derive(Debug, Error)]
#[non_exhaustive]
pub(crate) enum EvalExtError {
    #[error("step budget exceeded: limit {limit}, used {used}")]
    StepBudgetExceeded { limit: u64, used: u64 },
    #[error("allocation budget exceeded: limit {limit}, used {used}")]
    AllocationBudgetExceeded { limit: u64, used: u64 },
    #[error("depth budget exceeded: limit {limit}, reached {reached}")]
    DepthBudgetExceeded { limit: u32, reached: u32 },
    #[error("eval error: {0}")]
    Eval(#[from] NativeEvalError),
}

// ---------------------------------------------------------------------------
// TraceDetail / EvalBudget
// ---------------------------------------------------------------------------

/// Level of detail for evaluation traces.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
#[derive(Default)]
pub(crate) enum TraceDetail {
    Minimal,
    #[default]
    Steps,
    Full,
}

impl PartialOrd for TraceDetail {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for TraceDetail {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        fn rank(d: &TraceDetail) -> u8 {
            match d {
                TraceDetail::Minimal => 0,
                TraceDetail::Steps => 1,
                TraceDetail::Full => 2,
            }
        }
        rank(self).cmp(&rank(other))
    }
}

/// Configurable budget limits for evaluation (0 = unlimited).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct EvalBudget {
    pub(crate) max_steps: u64,
    pub(crate) max_allocations: u64,
    pub(crate) max_depth: u32,
}

impl Default for EvalBudget {
    fn default() -> Self {
        Self {
            max_steps: 10_000,
            max_allocations: 10_000,
            max_depth: 256,
        }
    }
}

impl EvalBudget {
    #[must_use]
    pub(crate) fn unlimited() -> Self {
        Self {
            max_steps: 0,
            max_allocations: 0,
            max_depth: 0,
        }
    }

    #[must_use]
    pub(crate) fn with_steps(max_steps: u64) -> Self {
        Self {
            max_steps,
            ..Self::default()
        }
    }
}

// ---------------------------------------------------------------------------
// TraceEntry / EvalProfile
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub(crate) struct TraceEntry {
    pub(crate) step: u64,
    pub(crate) depth: u32,
    pub(crate) description: String,
    pub(crate) result: Option<NativeValue>,
}

impl fmt::Display for TraceEntry {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let indent = "  ".repeat(self.depth as usize);
        match &self.result {
            Some(val) => write!(
                f,
                "[{:>4}] {}{} => {:?}",
                self.step, indent, self.description, val
            ),
            None => write!(f, "[{:>4}] {}{}", self.step, indent, self.description),
        }
    }
}

#[derive(Debug, Clone, Default)]
pub(crate) struct EvalProfile {
    pub(crate) total_steps: u64,
    pub(crate) total_allocations: u64,
    pub(crate) max_depth_reached: u32,
    pub(crate) op_counts: HashMap<String, u64>,
    pub(crate) trace: Vec<TraceEntry>,
}

impl EvalProfile {
    fn record_step(&mut self, op_key: &str) {
        self.total_steps += 1;
        *self.op_counts.entry(op_key.to_owned()).or_insert(0) += 1;
    }
    fn record_allocation(&mut self) {
        self.total_allocations += 1;
    }
    fn track_depth(&mut self, depth: u32) {
        if depth > self.max_depth_reached {
            self.max_depth_reached = depth;
        }
    }
}

impl fmt::Display for EvalProfile {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "EvalProfile:")?;
        writeln!(
            f,
            "  steps: {}, allocations: {}, max_depth: {}",
            self.total_steps, self.total_allocations, self.max_depth_reached
        )?;
        if !self.op_counts.is_empty() {
            let mut sorted: Vec<_> = self.op_counts.iter().collect();
            sorted.sort_by(|a, b| b.1.cmp(a.1));
            for (op, count) in sorted {
                writeln!(f, "  {}: {}", op, count)?;
            }
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// EvalStats (aggregate across evaluations)
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Default)]
pub(crate) struct EvalStats {
    pub(crate) eval_count: u64,
    pub(crate) total_steps: u64,
    pub(crate) total_allocations: u64,
    pub(crate) max_depth_seen: u32,
    pub(crate) cache_hits: u64,
    pub(crate) cache_misses: u64,
}

impl EvalStats {
    pub(crate) fn record(&mut self, profile: &EvalProfile) {
        self.eval_count += 1;
        self.total_steps += profile.total_steps;
        self.total_allocations += profile.total_allocations;
        if profile.max_depth_reached > self.max_depth_seen {
            self.max_depth_seen = profile.max_depth_reached;
        }
    }

    #[must_use]
    pub(crate) fn cache_hit_rate(&self) -> f64 {
        let total = self.cache_hits + self.cache_misses;
        if total == 0 {
            0.0
        } else {
            self.cache_hits as f64 / total as f64
        }
    }

    #[must_use]
    pub(crate) fn avg_steps(&self) -> f64 {
        if self.eval_count == 0 {
            0.0
        } else {
            self.total_steps as f64 / self.eval_count as f64
        }
    }
}

// ---------------------------------------------------------------------------
// Value / expression inspection
// ---------------------------------------------------------------------------

#[must_use]
pub(crate) fn inspect_value(val: &NativeValue) -> String {
    match val {
        NativeValue::UInt8(v) => format!("UInt8({})", v),
        NativeValue::UInt16(v) => format!("UInt16({})", v),
        NativeValue::UInt32(v) => format!("UInt32(0x{:08X} = {})", v, v),
        NativeValue::UInt64(v) => format!("UInt64(0x{:016X} = {})", v, v),
        NativeValue::USize(v) => format!("USize({})", v),
        NativeValue::Float(v) if v.is_nan() => "Float(NaN)".to_owned(),
        NativeValue::Float(v) if v.is_infinite() && v.is_sign_positive() => {
            "Float(+Inf)".to_owned()
        }
        NativeValue::Float(v) if v.is_infinite() => "Float(-Inf)".to_owned(),
        NativeValue::Float(v) => format!("Float({})", v),
        NativeValue::Bool(b) => format!("Bool({})", b),
    }
}

#[must_use]
pub(crate) fn inspect_expr(expr: &NativeExpr) -> String {
    match expr {
        NativeExpr::Lit(ty, bits) => format!("Lit({:?}, {})", ty, bits),
        NativeExpr::BinOp(op, lhs, rhs) => {
            format!("({} {:?} {})", inspect_expr(lhs), op, inspect_expr(rhs))
        }
        NativeExpr::UnaryOp(op, operand) => format!("{:?}({})", op, inspect_expr(operand)),
        NativeExpr::Var(name) => format!("Var({})", name),
        NativeExpr::Call(name, args) => {
            let a: Vec<_> = args.iter().map(inspect_expr).collect();
            format!("Call({}, [{}])", name, a.join(", "))
        }
    }
}

// ---------------------------------------------------------------------------
// Partial evaluation
// ---------------------------------------------------------------------------

/// Either a concrete value or a residual expression.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum PartialValue {
    Concrete(NativeValue),
    Symbolic(NativeExpr),
}

/// Partially evaluate `expr` substituting `bindings` for variables.
#[must_use]
pub(crate) fn partial_eval(
    expr: &NativeExpr,
    bindings: &HashMap<String, NativeValue>,
) -> PartialValue {
    match expr {
        NativeExpr::Lit(..) => eval_native(expr).map_or_else(
            |_| PartialValue::Symbolic(expr.clone()),
            PartialValue::Concrete,
        ),
        NativeExpr::Var(name) => match bindings.get(name.as_str()) {
            Some(val) => PartialValue::Concrete(val.clone()),
            None => PartialValue::Symbolic(expr.clone()),
        },
        NativeExpr::BinOp(op, lhs, rhs) => {
            let (l, r) = (partial_eval(lhs, bindings), partial_eval(rhs, bindings));
            let (sl, sr) = (partial_to_expr(&l), partial_to_expr(&r));
            let full = NativeExpr::BinOp(*op, Box::new(sl), Box::new(sr));
            if matches!(
                (&l, &r),
                (PartialValue::Concrete(_), PartialValue::Concrete(_))
            ) {
                eval_native(&full)
                    .map_or_else(|_| PartialValue::Symbolic(full), PartialValue::Concrete)
            } else {
                PartialValue::Symbolic(full)
            }
        }
        NativeExpr::UnaryOp(op, operand) => {
            let inner = partial_eval(operand, bindings);
            let subst = partial_to_expr(&inner);
            let full = NativeExpr::UnaryOp(*op, Box::new(subst));
            if matches!(&inner, PartialValue::Concrete(_)) {
                eval_native(&full)
                    .map_or_else(|_| PartialValue::Symbolic(full), PartialValue::Concrete)
            } else {
                PartialValue::Symbolic(full)
            }
        }
        NativeExpr::Call(name, args) => {
            let pa: Vec<_> = args.iter().map(|a| partial_eval(a, bindings)).collect();
            let sa: Vec<_> = pa.iter().map(partial_to_expr).collect();
            if pa.iter().all(|p| matches!(p, PartialValue::Concrete(_))) {
                let full = NativeExpr::Call(name.clone(), sa);
                eval_native(&full).map_or_else(
                    |_| {
                        PartialValue::Symbolic(NativeExpr::Call(
                            name.clone(),
                            pa.iter().map(partial_to_expr).collect(),
                        ))
                    },
                    PartialValue::Concrete,
                )
            } else {
                PartialValue::Symbolic(NativeExpr::Call(name.clone(), sa))
            }
        }
    }
}

fn partial_to_expr(pv: &PartialValue) -> NativeExpr {
    match pv {
        PartialValue::Concrete(val) => value_to_expr(val),
        PartialValue::Symbolic(expr) => expr.clone(),
    }
}

fn value_to_expr(val: &NativeValue) -> NativeExpr {
    match val {
        NativeValue::UInt8(v) => NativeExpr::Lit(NativeType::UInt8, u64::from(*v)),
        NativeValue::UInt16(v) => NativeExpr::Lit(NativeType::UInt16, u64::from(*v)),
        NativeValue::UInt32(v) => NativeExpr::Lit(NativeType::UInt32, u64::from(*v)),
        NativeValue::UInt64(v) => NativeExpr::Lit(NativeType::UInt64, *v),
        NativeValue::USize(v) => NativeExpr::Lit(NativeType::USize, *v),
        NativeValue::Float(v) => NativeExpr::Lit(NativeType::Float, v.to_bits()),
        NativeValue::Bool(b) => NativeExpr::Lit(NativeType::Bool, u64::from(*b)),
    }
}

// ---------------------------------------------------------------------------
// Profiled evaluation
// ---------------------------------------------------------------------------

/// Evaluate with profiling and budget enforcement.
pub(crate) fn eval_profiled(
    expr: &NativeExpr,
    budget: &EvalBudget,
    detail: TraceDetail,
) -> Result<(NativeValue, EvalProfile), EvalExtError> {
    let mut profile = EvalProfile::default();
    let result = eval_profiled_inner(expr, budget, detail, 0, &mut profile)?;
    Ok((result, profile))
}

fn eval_profiled_inner(
    expr: &NativeExpr,
    budget: &EvalBudget,
    detail: TraceDetail,
    depth: u32,
    profile: &mut EvalProfile,
) -> Result<NativeValue, EvalExtError> {
    if budget.max_depth > 0 && depth >= budget.max_depth {
        return Err(EvalExtError::DepthBudgetExceeded {
            limit: budget.max_depth,
            reached: depth,
        });
    }
    if budget.max_steps > 0 && profile.total_steps >= budget.max_steps {
        return Err(EvalExtError::StepBudgetExceeded {
            limit: budget.max_steps,
            used: profile.total_steps,
        });
    }
    if budget.max_allocations > 0 && profile.total_allocations >= budget.max_allocations {
        return Err(EvalExtError::AllocationBudgetExceeded {
            limit: budget.max_allocations,
            used: profile.total_allocations,
        });
    }
    profile.track_depth(depth);

    match expr {
        NativeExpr::Lit(ty, bits) => {
            profile.record_step("Lit");
            let val = eval_native(expr)?;
            if detail >= TraceDetail::Steps {
                profile.trace.push(TraceEntry {
                    step: profile.total_steps - 1,
                    depth,
                    description: format!("Lit({:?}, {})", ty, bits),
                    result: Some(val.clone()),
                });
            }
            Ok(val)
        }
        NativeExpr::BinOp(op, lhs, rhs) => {
            profile.record_step(&format!("{:?}", op));
            profile.record_allocation();
            let lv = eval_profiled_inner(lhs, budget, detail, depth + 1, profile)?;
            let rv = eval_profiled_inner(rhs, budget, detail, depth + 1, profile)?;
            let val = eval_native(expr)?;
            if detail >= TraceDetail::Steps {
                let desc = if detail == TraceDetail::Full {
                    format!("{} {:?} {}", inspect_value(&lv), op, inspect_value(&rv))
                } else {
                    format!("BinOp({:?})", op)
                };
                profile.trace.push(TraceEntry {
                    step: profile.total_steps - 1,
                    depth,
                    description: desc,
                    result: Some(val.clone()),
                });
            }
            Ok(val)
        }
        NativeExpr::UnaryOp(op, operand) => {
            profile.record_step(&format!("{:?}", op));
            profile.record_allocation();
            let _inner = eval_profiled_inner(operand, budget, detail, depth + 1, profile)?;
            let val = eval_native(expr)?;
            if detail >= TraceDetail::Steps {
                profile.trace.push(TraceEntry {
                    step: profile.total_steps - 1,
                    depth,
                    description: format!("UnaryOp({:?})", op),
                    result: Some(val.clone()),
                });
            }
            Ok(val)
        }
        NativeExpr::Var(name) => {
            profile.record_step("Var");
            Err(EvalExtError::Eval(NativeEvalError::UnresolvedVariable(
                name.clone(),
            )))
        }
        NativeExpr::Call(name, _) => {
            profile.record_step("Call");
            Err(EvalExtError::Eval(NativeEvalError::UnresolvedCall(
                name.clone(),
            )))
        }
    }
}

// ---------------------------------------------------------------------------
// Expression analysis
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Default)]
pub(crate) struct ExprAnalysis {
    pub(crate) node_count: u64,
    pub(crate) max_depth: u32,
    pub(crate) op_histogram: HashMap<String, u64>,
    pub(crate) var_count: u64,
    pub(crate) call_count: u64,
    pub(crate) lit_count: u64,
}

#[must_use]
pub(crate) fn analyze_expr(expr: &NativeExpr) -> ExprAnalysis {
    let mut a = ExprAnalysis::default();
    analyze_inner(expr, 0, &mut a);
    a
}

fn analyze_inner(expr: &NativeExpr, depth: u32, a: &mut ExprAnalysis) {
    a.node_count += 1;
    if depth > a.max_depth {
        a.max_depth = depth;
    }
    match expr {
        NativeExpr::Lit(..) => {
            a.lit_count += 1;
            *a.op_histogram.entry("Lit".to_owned()).or_insert(0) += 1;
        }
        NativeExpr::BinOp(op, lhs, rhs) => {
            *a.op_histogram.entry(format!("{:?}", op)).or_insert(0) += 1;
            analyze_inner(lhs, depth + 1, a);
            analyze_inner(rhs, depth + 1, a);
        }
        NativeExpr::UnaryOp(op, operand) => {
            *a.op_histogram.entry(format!("{:?}", op)).or_insert(0) += 1;
            analyze_inner(operand, depth + 1, a);
        }
        NativeExpr::Var(_) => {
            a.var_count += 1;
            *a.op_histogram.entry("Var".to_owned()).or_insert(0) += 1;
        }
        NativeExpr::Call(_, args) => {
            a.call_count += 1;
            *a.op_histogram.entry("Call".to_owned()).or_insert(0) += 1;
            for arg in args {
                analyze_inner(arg, depth + 1, a);
            }
        }
    }
}

/// Identify hot operations exceeding the given fraction of total steps.
#[must_use]
pub(crate) fn hot_ops(profile: &EvalProfile, threshold: f64) -> Vec<(String, u64)> {
    if profile.total_steps == 0 {
        return Vec::new();
    }
    let cutoff = (profile.total_steps as f64 * threshold) as u64;
    let mut result: Vec<_> = profile
        .op_counts
        .iter()
        .filter(|(_, &c)| c >= cutoff)
        .map(|(op, &c)| (op.clone(), c))
        .collect();
    result.sort_by_key(|b| std::cmp::Reverse(b.1));
    result
}

/// Format a trace as a multi-line string.
#[must_use]
pub(crate) fn format_trace(profile: &EvalProfile) -> String {
    profile.trace.iter().map(|e| format!("{}\n", e)).collect()
}

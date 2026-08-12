// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::error::CompilerError;
use crate::ir::{
    FnId, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRLiteral, IRType, JoinPointId, VarId,
};
use crate::lcnf::Code;
use crate::to_ir::{lower_code, ToIRConfig, ToIRState};
use clean_kernel::Name;
use std::collections::{BTreeSet, HashMap, HashSet};
use thiserror::Error;

#[derive(Debug, Clone)]
pub(crate) struct ExtLowerConfig {
    pub(crate) enable_jump_tables: bool,
    pub(crate) jump_table_min_density: f64,
    pub(crate) jump_table_min_cases: usize,
    pub(crate) enable_string_literals: bool,
    pub(crate) enable_foreign_calls: bool,
    pub(crate) enable_closure_alloc: bool,
    // Debug-only post-lowering IR validation, defaulted from
    // `cfg!(debug_assertions)`. Read only by `lower_extended`, which has no
    // caller yet (see the note there) — 2026-07-31.
    #[allow(dead_code)]
    pub(crate) enable_validation: bool,
}

impl Default for ExtLowerConfig {
    fn default() -> Self {
        Self {
            enable_jump_tables: true,
            jump_table_min_density: 0.5,
            jump_table_min_cases: 4,
            enable_string_literals: true,
            enable_foreign_calls: true,
            enable_closure_alloc: true,
            enable_validation: cfg!(debug_assertions),
        }
    }
}

#[derive(Debug, Clone, Default)]
pub(crate) struct LoweringStats {
    pub(crate) string_literals: u32,
    pub(crate) char_literals: u32,
    pub(crate) scientific_literals: u32,
    pub(crate) projections: u32,
    pub(crate) jump_tables: u32,
    pub(crate) linear_cases: u32,
    pub(crate) foreign_calls: u32,
    pub(crate) closure_allocs: u32,
    pub(crate) join_points: u32,
    pub(crate) panics: u32,
}

impl LoweringStats {
    pub(crate) fn report(&self) -> String {
        format!(
            "strings={}, chars={}, scientific={}, projections={}, jump_tables={}, linear_cases={}, foreign_calls={}, closure_allocs={}, join_points={}, panics={}",
            self.string_literals,
            self.char_literals,
            self.scientific_literals,
            self.projections,
            self.jump_tables,
            self.linear_cases,
            self.foreign_calls,
            self.closure_allocs,
            self.join_points,
            self.panics
        )
    }
}

#[derive(Debug)]
pub(crate) struct ExtLowerCtx {
    pub(crate) config: ExtLowerConfig,
    pub(crate) stats: LoweringStats,
    // The base `to_ir` state this extension threads through `lower_code`.
    // Read only by `lower_extended`, which has no caller yet (see the note
    // there) — 2026-07-31.
    #[allow(dead_code)]
    pub(crate) state: ToIRState,
}

impl ExtLowerCtx {
    pub(crate) fn new(config: ExtLowerConfig) -> Self {
        let _base = ToIRConfig::default();
        Self {
            config,
            stats: LoweringStats::default(),
            state: ToIRState::new(),
        }
    }
}

#[derive(Debug, Error)]
enum ExtLowerError {
    #[error("extended lowering feature disabled: {0}")]
    Disabled(&'static str),
    #[error("invalid extended IR: {0}")]
    Invalid(String),
}

impl From<ExtLowerError> for CompilerError {
    fn from(value: ExtLowerError) -> Self {
        match value {
            ExtLowerError::Disabled(feature) => {
                CompilerError::Unsupported(format!("extended lowering feature disabled: {feature}"))
            }
            ExtLowerError::Invalid(msg) => CompilerError::InvalidExpr(msg),
        }
    }
}

pub(crate) fn lower_string_literal(s: &str) -> (IRExpr, IRType) {
    (IRExpr::String(s.to_owned()), IRType::Object)
}

pub(crate) fn lower_char_literal(c: char) -> (IRExpr, IRType) {
    (IRExpr::Lit(IRLiteral::UInt32(c as u32)), IRType::UInt32)
}

pub(crate) fn lower_scientific_literal(mantissa: u64, exponent: i32) -> (IRExpr, IRType) {
    (
        IRExpr::Lit(IRLiteral::Float64(
            (mantissa as f64) * 10_f64.powi(exponent),
        )),
        IRType::Float64,
    )
}

pub(crate) fn lower_projection(
    ctx: &mut ExtLowerCtx,
    _type_name: &Name,
    idx: u32,
    structure: VarId,
) -> Result<(IRExpr, IRType), CompilerError> {
    bump(&mut ctx.stats.projections);
    Ok((
        IRExpr::Proj {
            idx,
            ty: IRType::Object,
            arg: IRArg::Var(structure),
        },
        IRType::Object,
    ))
}

pub(crate) fn analyze_case_density(alts: &[IRAlt], tag_range: u32) -> f64 {
    let slots = (tag_range as usize).saturating_add(1);
    if slots == 0 {
        return 0.0;
    }
    let used: HashSet<u32> = alts.iter().map(|alt| alt.ctor.tag).collect();
    used.len() as f64 / slots as f64
}

pub(crate) fn lower_case_jump_table(
    ctx: &mut ExtLowerCtx,
    scrutinee: VarId,
    mut alts: Vec<IRAlt>,
    default: Option<Box<IRBody>>,
    tag_range: u32,
) -> Result<IRBody, CompilerError> {
    let mut seen = BTreeSet::new();
    let mut max_tag = 0;
    for alt in &alts {
        if !seen.insert(alt.ctor.tag) {
            return Err(invalid(format!(
                "duplicate case tag {} for {:?}",
                alt.ctor.tag, alt.ctor.name
            )));
        }
        max_tag = max_tag.max(alt.ctor.tag);
    }
    if max_tag > tag_range {
        return Err(invalid(format!(
            "case tag {max_tag} exceeds range {tag_range}"
        )));
    }
    let density = analyze_case_density(&alts, tag_range);
    let use_jt = ctx.config.enable_jump_tables
        && alts.len() >= ctx.config.jump_table_min_cases
        && density >= ctx.config.jump_table_min_density
        && (default.is_some() || density >= 1.0);
    if use_jt {
        alts.sort_by_key(|alt| alt.ctor.tag);
        bump(&mut ctx.stats.jump_tables);
    } else {
        bump(&mut ctx.stats.linear_cases);
    }
    Ok(IRBody::Case {
        scrutinee,
        alts,
        default,
    })
}

pub(crate) fn lower_foreign_call(
    ctx: &mut ExtLowerCtx,
    fn_name: &Name,
    args: Vec<IRArg>,
    return_type: IRType,
) -> Result<(IRExpr, IRType), CompilerError> {
    if !ctx.config.enable_foreign_calls {
        return Err(disabled("foreign_calls"));
    }
    bump(&mut ctx.stats.foreign_calls);
    Ok((
        IRExpr::Apply {
            fn_id: FnId(fn_name.clone()),
            args,
        },
        return_type,
    ))
}

pub(crate) fn lower_closure_alloc(
    ctx: &mut ExtLowerCtx,
    fn_id: &FnId,
    arity: u16,
    captures: Vec<IRArg>,
) -> Result<(IRExpr, IRType), CompilerError> {
    if !ctx.config.enable_closure_alloc {
        return Err(disabled("closure_alloc"));
    }
    if arity == 0 || captures.len() >= arity as usize {
        return Err(invalid(format!(
            "partial application for {:?} must capture fewer than {} argument(s)",
            fn_id.0, arity
        )));
    }
    bump(&mut ctx.stats.closure_allocs);
    Ok((
        IRExpr::PartialApply {
            fn_id: fn_id.clone(),
            arity,
            args: captures,
        },
        IRType::Object,
    ))
}

pub(crate) fn lower_join_point_block(
    ctx: &mut ExtLowerCtx,
    jp_id: JoinPointId,
    params: Vec<(VarId, IRType)>,
    body: IRBody,
    rest: IRBody,
) -> Result<IRBody, CompilerError> {
    unique(params.iter().map(|(var, _)| *var), "join point parameter")?;
    bump(&mut ctx.stats.join_points);
    Ok(IRBody::JDecl {
        jp: jp_id,
        params,
        body: Box::new(body),
        rest: Box::new(rest),
    })
}

pub(crate) fn lower_panic(ctx: &mut ExtLowerCtx, msg: &str) -> IRBody {
    bump(&mut ctx.stats.panics);
    if !ctx.config.enable_string_literals {
        return IRBody::Unreachable;
    }
    let var = VarId(u32::MAX.saturating_sub(ctx.stats.panics));
    let (value, ty) = lower_string_literal(msg);
    IRBody::VDecl {
        var,
        ty,
        value,
        rest: Box::new(IRBody::Dec {
            var,
            rest: Box::new(IRBody::Unreachable),
        }),
    }
}

pub(crate) fn lower_sorry(ctx: &mut ExtLowerCtx) -> IRBody {
    lower_panic(ctx, "encountered sorry/axiom in lowered code")
}

pub(crate) fn validate_ir_body(body: &IRBody) -> Result<(), CompilerError> {
    let _ = validate(body, &HashSet::new(), &HashMap::new())?;
    Ok(())
}

pub(crate) fn validate_ir_decl(decl: &IRDecl) -> Result<(), CompilerError> {
    unique(
        decl.params.iter().map(|(var, _)| *var),
        "function parameter",
    )?;
    let scope: HashSet<VarId> = decl.params.iter().map(|(var, _)| *var).collect();
    let _ = validate(&decl.body, &scope, &HashMap::new())?;
    Ok(())
}

/// L5CNF -> L5IR lowering with the extended rewrites (jump tables, string and
/// scientific literals, foreign calls, closure allocation) layered on top of
/// the base `to_ir` pass.
// The extended lowering entry point, with no caller anywhere yet — the
// pipeline still goes straight to `to_ir::lower_code`, and the tests in
// `to_ir_ext_tests` cover the pieces (config, stats, validation) rather than
// this composition. Kept whole: it is the only thing that gives
// `rewrite_body`/`rewrite_expr` and the `ExtLowerConfig` knobs a purpose, and
// deleting it would discard the staged switch-over — 2026-07-31.
#[allow(dead_code)]
pub(crate) fn lower_extended(ctx: &mut ExtLowerCtx, code: &Code) -> Result<IRBody, CompilerError> {
    let lowered = lower_code(code, &mut ctx.state)?;
    let body = rewrite_body(ctx, &lowered)?;
    if ctx.config.enable_validation {
        validate_ir_body(&body)?;
    }
    Ok(body)
}

// Reachable only from `lower_extended`; see the note there — 2026-07-31.
#[allow(dead_code)]
fn rewrite_body(ctx: &mut ExtLowerCtx, body: &IRBody) -> Result<IRBody, CompilerError> {
    Ok(match body {
        IRBody::VDecl {
            var,
            ty,
            value,
            rest,
        } => IRBody::VDecl {
            var: *var,
            ty: ty.clone(),
            value: rewrite_expr(ctx, value)?,
            rest: Box::new(rewrite_body(ctx, rest)?),
        },
        IRBody::JDecl {
            jp,
            params,
            body,
            rest,
        } => {
            let rewritten_body = rewrite_body(ctx, body)?;
            let rewritten_rest = rewrite_body(ctx, rest)?;
            lower_join_point_block(ctx, *jp, params.clone(), rewritten_body, rewritten_rest)?
        }
        IRBody::Inc { var, n, rest } => IRBody::Inc {
            var: *var,
            n: *n,
            rest: Box::new(rewrite_body(ctx, rest)?),
        },
        IRBody::Dec { var, rest } => IRBody::Dec {
            var: *var,
            rest: Box::new(rewrite_body(ctx, rest)?),
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
            rest: Box::new(rewrite_body(ctx, rest)?),
        },
        IRBody::SetTag { var, tag, rest } => IRBody::SetTag {
            var: *var,
            tag: *tag,
            rest: Box::new(rewrite_body(ctx, rest)?),
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
            rest: Box::new(rewrite_body(ctx, rest)?),
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
            rest: Box::new(rewrite_body(ctx, rest)?),
        },
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => {
            let alts = alts
                .iter()
                .map(|alt| {
                    Ok(IRAlt {
                        ctor: alt.ctor.clone(),
                        body: Box::new(rewrite_body(ctx, &alt.body)?),
                    })
                })
                .collect::<Result<Vec<_>, CompilerError>>()?;
            let default = default
                .as_ref()
                .map(|body| rewrite_body(ctx, body).map(Box::new))
                .transpose()?;
            let tag_range = alts
                .iter()
                .map(|alt| alt.ctor.tag)
                .max()
                .map_or(0, |tag| tag);
            lower_case_jump_table(ctx, *scrutinee, alts, default, tag_range)?
        }
        IRBody::Jmp { jp, args } => IRBody::Jmp {
            jp: *jp,
            args: args.clone(),
        },
        IRBody::Ret(arg) => IRBody::Ret(arg.clone()),
        IRBody::Unreachable => IRBody::Unreachable,
    })
}

// Reachable only from `rewrite_body`; see the note on `lower_extended`
// — 2026-07-31.
#[allow(dead_code)]
fn rewrite_expr(ctx: &mut ExtLowerCtx, expr: &IRExpr) -> Result<IRExpr, CompilerError> {
    match expr {
        IRExpr::String(_) => {
            if !ctx.config.enable_string_literals {
                return Err(disabled("string_literals"));
            }
            bump(&mut ctx.stats.string_literals);
        }
        IRExpr::Lit(IRLiteral::Float64(_)) => bump(&mut ctx.stats.scientific_literals),
        IRExpr::Proj { .. } | IRExpr::UProj { .. } | IRExpr::SProj { .. } => {
            bump(&mut ctx.stats.projections)
        }
        IRExpr::PartialApply { .. } => bump(&mut ctx.stats.closure_allocs),
        _ => {}
    }
    Ok(expr.clone())
}

fn validate(
    body: &IRBody,
    scope: &HashSet<VarId>,
    jps: &HashMap<JoinPointId, usize>,
) -> Result<HashSet<VarId>, CompilerError> {
    match body {
        IRBody::VDecl {
            var, value, rest, ..
        } => {
            if scope.contains(var) {
                return Err(invalid(format!("duplicate var x{}", var.0)));
            }
            check_expr(value, scope)?;
            let mut next_scope = scope.clone();
            next_scope.insert(*var);
            let mut used = validate(rest, &next_scope, jps)?;
            if !used.contains(var) {
                return Err(invalid(format!(
                    "vdecl x{} is unused before scope exit",
                    var.0
                )));
            }
            collect_expr_uses(value, &mut used);
            used.remove(var);
            Ok(used)
        }
        IRBody::JDecl {
            jp,
            params,
            body,
            rest,
        } => {
            if jps.contains_key(jp) {
                return Err(invalid(format!("duplicate join point j{}", jp.0)));
            }
            unique(params.iter().map(|(var, _)| *var), "join point parameter")?;
            let mut next_scope = scope.clone();
            for (var, _) in params {
                if scope.contains(var) {
                    return Err(invalid(format!(
                        "join point parameter x{} shadows outer var",
                        var.0
                    )));
                }
                next_scope.insert(*var);
            }
            let mut next_jps = jps.clone();
            next_jps.insert(*jp, params.len());
            let mut used = validate(body, &next_scope, &next_jps)?;
            for (var, _) in params {
                used.remove(var);
            }
            used.extend(validate(rest, scope, &next_jps)?);
            Ok(used)
        }
        IRBody::Inc { var, rest, .. } | IRBody::Dec { var, rest } => {
            check_var(*var, scope, "rc op")?;
            let mut used = validate(rest, scope, jps)?;
            used.insert(*var);
            Ok(used)
        }
        IRBody::Set {
            var, value, rest, ..
        }
        | IRBody::USet {
            var, value, rest, ..
        }
        | IRBody::SSet {
            var, value, rest, ..
        } => {
            check_var(*var, scope, "set target")?;
            check_var(*value, scope, "set value")?;
            let mut used = validate(rest, scope, jps)?;
            used.insert(*var);
            used.insert(*value);
            Ok(used)
        }
        IRBody::SetTag { var, rest, .. } => {
            check_var(*var, scope, "setTag")?;
            let mut used = validate(rest, scope, jps)?;
            used.insert(*var);
            Ok(used)
        }
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => {
            check_var(*scrutinee, scope, "case scrutinee")?;
            let mut seen = BTreeSet::new();
            let mut used = HashSet::from([*scrutinee]);
            for alt in alts {
                if !seen.insert(alt.ctor.tag) {
                    return Err(invalid(format!("duplicate case tag {}", alt.ctor.tag)));
                }
                used.extend(validate(&alt.body, scope, jps)?);
            }
            if let Some(default) = default {
                used.extend(validate(default, scope, jps)?);
            }
            Ok(used)
        }
        IRBody::Jmp { jp, args } => {
            let expected = jps
                .get(jp)
                .copied()
                .ok_or_else(|| invalid(format!("orphan jump to j{}", jp.0)))?;
            if args.len() != expected {
                return Err(invalid(format!(
                    "jump to j{} has {} arg(s), expected {}",
                    jp.0,
                    args.len(),
                    expected
                )));
            }
            check_args(args, scope, "jump arg")?;
            Ok(arg_vars(args))
        }
        IRBody::Ret(arg) => {
            check_arg(arg, scope, "return")?;
            Ok(arg_vars(std::slice::from_ref(arg)))
        }
        IRBody::Unreachable => Ok(HashSet::new()),
    }
}

fn check_expr(expr: &IRExpr, scope: &HashSet<VarId>) -> Result<(), CompilerError> {
    let mut used = HashSet::new();
    collect_expr_uses(expr, &mut used);
    for var in used {
        check_var(var, scope, "expr")?;
    }
    if let IRExpr::PartialApply { arity, args, .. } = expr {
        if args.len() >= *arity as usize {
            return Err(invalid(format!(
                "partial apply captures {} arg(s) for arity {}",
                args.len(),
                arity
            )));
        }
    }
    Ok(())
}

fn check_args(
    args: &[IRArg],
    scope: &HashSet<VarId>,
    context: &'static str,
) -> Result<(), CompilerError> {
    for arg in args {
        check_arg(arg, scope, context)?;
    }
    Ok(())
}

fn check_arg(
    arg: &IRArg,
    scope: &HashSet<VarId>,
    context: &'static str,
) -> Result<(), CompilerError> {
    if let IRArg::Var(var) = arg {
        check_var(*var, scope, context)?;
    }
    Ok(())
}

fn check_var(
    var: VarId,
    scope: &HashSet<VarId>,
    context: &'static str,
) -> Result<(), CompilerError> {
    if scope.contains(&var) {
        Ok(())
    } else {
        Err(invalid(format!(
            "{context} references out-of-scope x{}",
            var.0
        )))
    }
}

fn unique(vars: impl IntoIterator<Item = VarId>, kind: &'static str) -> Result<(), CompilerError> {
    let mut seen = HashSet::new();
    for var in vars {
        if !seen.insert(var) {
            return Err(invalid(format!("duplicate {kind} x{}", var.0)));
        }
    }
    Ok(())
}

fn arg_vars(args: &[IRArg]) -> HashSet<VarId> {
    let mut used = HashSet::new();
    for arg in args {
        if let IRArg::Var(var) = arg {
            used.insert(*var);
        }
    }
    used
}

fn collect_expr_uses(expr: &IRExpr, used: &mut HashSet<VarId>) {
    match expr {
        IRExpr::Ctor { args, .. }
        | IRExpr::Apply { args, .. }
        | IRExpr::PartialApply { args, .. } => used.extend(arg_vars(args)),
        IRExpr::Proj { arg, .. }
        | IRExpr::Tag(arg)
        | IRExpr::Box { arg, .. }
        | IRExpr::Unbox { arg, .. } => {
            if let IRArg::Var(var) = arg {
                used.insert(*var);
            }
        }
        IRExpr::ClosureApply { closure, args } => {
            if let IRArg::Var(var) = closure {
                used.insert(*var);
            }
            used.extend(arg_vars(args));
        }
        IRExpr::UProj { var, .. }
        | IRExpr::SProj { var, .. }
        | IRExpr::IsShared(var)
        | IRExpr::Reset(var) => {
            used.insert(*var);
        }
        IRExpr::Reuse { var, args, .. } => {
            used.insert(*var);
            used.extend(arg_vars(args));
        }
        IRExpr::Lit(_) | IRExpr::String(_) => {}
    }
}

fn bump(value: &mut u32) {
    *value = value.saturating_add(1);
}
fn invalid(msg: impl Into<String>) -> CompilerError {
    ExtLowerError::Invalid(msg.into()).into()
}
fn disabled(feature: &'static str) -> CompilerError {
    ExtLowerError::Disabled(feature).into()
}

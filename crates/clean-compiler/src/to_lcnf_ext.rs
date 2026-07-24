// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Method's &self is intentionally retained; recursive call goes through self for future state.
#![allow(clippy::only_used_in_recursion)]

//! Extended kernel-to-LCNF conversion: lambda lifting, let-flattening,
//! case simplification, eta/beta reduction, join point detection,
//! erased argument elimination, statistics, and validation.
//!
//! Part of #3083.

use crate::lcnf::{Alt, Arg, Code, Decl, FunDecl, LetValue};
use crate::to_lcnf::FVarIdGen;
use clean_kernel::{Expr, FVarId, Name};
use std::collections::HashSet;

/// Configuration for extended LCNF conversion.
#[derive(Debug, Clone)]
pub(crate) struct ExtConvConfig {
    pub(crate) lambda_lifting: bool,
    pub(crate) let_flattening: bool,
    pub(crate) case_simplification: bool,
    pub(crate) eta_reduction: bool,
    pub(crate) beta_reduction: bool,
    pub(crate) join_point_detection: bool,
    pub(crate) erased_arg_elimination: bool,
    pub(crate) validate: bool,
}

impl Default for ExtConvConfig {
    fn default() -> Self {
        Self {
            lambda_lifting: true,
            let_flattening: true,
            case_simplification: true,
            eta_reduction: true,
            beta_reduction: true,
            join_point_detection: true,
            erased_arg_elimination: true,
            validate: false,
        }
    }
}

/// Statistics collected during extended conversion.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct ConvStats {
    pub(crate) lambdas_lifted: usize,
    pub(crate) lets_flattened: usize,
    pub(crate) cases_simplified: usize,
    pub(crate) eta_reductions: usize,
    pub(crate) beta_reductions: usize,
    pub(crate) join_points_detected: usize,
    pub(crate) erased_args_eliminated: usize,
    pub(crate) decls_processed: usize,
}

/// Validation error for LCNF invariants.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ValidationError {
    UnboundReturn(FVarId),
    UnboundLetRef(FVarId),
    UnboundJoinPoint(FVarId),
    EmptyCaseAlts,
}

/// Result of extended conversion for a single declaration.
#[derive(Debug, Clone)]
pub(crate) struct ExtConvResult {
    pub(crate) decl: Decl,
    pub(crate) lifted_decls: Vec<Decl>,
    pub(crate) stats: ConvStats,
    pub(crate) validation_errors: Vec<ValidationError>,
}

/// Apply extended transformations to an LCNF declaration.
pub(crate) fn convert_ext(decl: &Decl, config: &ExtConvConfig) -> ExtConvResult {
    let mut stats = ConvStats {
        decls_processed: 1,
        ..Default::default()
    };
    let mut fvar_gen = FVarIdGen::new();
    let mut lifted_decls = Vec::new();
    let mut result_decl = decl.clone();

    if let crate::lcnf::DeclValue::Code(ref mut code) = result_decl.body {
        if config.lambda_lifting {
            let lifted = lift_lambdas(code, &mut fvar_gen, &result_decl.name);
            stats.lambdas_lifted += lifted.len();
            lifted_decls.extend(lifted);
        }
        if config.let_flattening {
            stats.lets_flattened += flatten_lets(code);
        }
        if config.case_simplification {
            stats.cases_simplified += simplify_cases(code);
        }
        if config.eta_reduction {
            stats.eta_reductions += reduce_eta(code);
        }
        if config.beta_reduction {
            stats.beta_reductions += reduce_beta(code);
        }
        if config.join_point_detection {
            stats.join_points_detected += detect_join_points(code);
        }
        if config.erased_arg_elimination {
            stats.erased_args_eliminated += elim_erased(code);
        }
    }

    let validation_errors = if config.validate {
        validate_lcnf(&result_decl)
    } else {
        Vec::new()
    };
    ExtConvResult {
        decl: result_decl,
        lifted_decls,
        stats,
        validation_errors,
    }
}

/// Batch-convert multiple declarations with the extended pipeline.
pub(crate) fn convert_ext_batch(
    decls: &[Decl],
    config: &ExtConvConfig,
) -> (Vec<ExtConvResult>, ConvStats) {
    let mut total = ConvStats::default();
    let results: Vec<_> = decls
        .iter()
        .map(|d| {
            let r = convert_ext(d, config);
            total.lambdas_lifted += r.stats.lambdas_lifted;
            total.lets_flattened += r.stats.lets_flattened;
            total.cases_simplified += r.stats.cases_simplified;
            total.eta_reductions += r.stats.eta_reductions;
            total.beta_reductions += r.stats.beta_reductions;
            total.join_points_detected += r.stats.join_points_detected;
            total.erased_args_eliminated += r.stats.erased_args_eliminated;
            total.decls_processed += 1;
            r
        })
        .collect();
    (results, total)
}

// ─── Recursive alt visitor ──────────────────────────────────────────────────

fn for_each_alt(alts: &mut [Alt], f: &mut impl FnMut(&mut Code)) {
    for alt in alts {
        match alt {
            Alt::Ctor { body, .. } | Alt::Default(body) => f(body.as_mut()),
        }
    }
}

// ─── Lambda Lifting ─────────────────────────────────────────────────────────

fn lift_lambdas(code: &mut Code, fg: &mut FVarIdGen, parent: &Name) -> Vec<Decl> {
    let mut lifted = Vec::new();
    lift_inner(code, fg, parent, &mut lifted);
    lifted
}

fn lift_inner(code: &mut Code, fg: &mut FVarIdGen, parent: &Name, out: &mut Vec<Decl>) {
    match code {
        Code::Fun(fd, body) => {
            lift_inner(&mut fd.body, fg, parent, out);
            let name = Name::from_string(&format!("{}_lifted_{}", parent, out.len()));
            out.push(Decl::new(
                name,
                Vec::new(),
                fd.ty.clone(),
                fd.params.clone(),
                *fd.body.clone(),
                false,
            ));
            let mut nb = body.as_ref().clone();
            lift_inner(&mut nb, fg, parent, out);
            *code = nb;
        }
        Code::Let(_, body) => lift_inner(body.as_mut(), fg, parent, out),
        Code::JoinPoint(jp, body) => {
            lift_inner(&mut jp.body, fg, parent, out);
            lift_inner(body.as_mut(), fg, parent, out);
        }
        Code::Cases(c) => for_each_alt(&mut c.alts, &mut |b| lift_inner(b, fg, parent, out)),
        _ => {}
    }
}

// ─── Let Flattening ─────────────────────────────────────────────────────────

fn flatten_lets(code: &mut Code) -> usize {
    let mut n = 0;
    flatten_inner(code, &mut n);
    n
}

fn flatten_inner(code: &mut Code, n: &mut usize) {
    match code {
        Code::Let(_, body) => flatten_inner(body.as_mut(), n),
        Code::Fun(fd, body) => {
            flatten_inner(&mut fd.body, n);
            flatten_inner(body.as_mut(), n);
        }
        Code::JoinPoint(jp, body) => {
            flatten_inner(&mut jp.body, n);
            flatten_inner(body.as_mut(), n);
        }
        Code::Cases(c) => for_each_alt(&mut c.alts, &mut |b| flatten_inner(b, n)),
        _ => {}
    }
    if let Code::Let(_, _) = code {
        let (mut depth, mut cur) = (0usize, &*code);
        while let Code::Let(_, inner) = cur {
            depth += 1;
            cur = inner;
        }
        if depth > 1 {
            *n += depth - 1;
        }
    }
}

// ─── Case Simplification ───────────────────────────────────────────────────

fn simplify_cases(code: &mut Code) -> usize {
    let mut n = 0;
    simp_inner(code, &mut n);
    n
}

fn simp_inner(code: &mut Code, n: &mut usize) {
    match code {
        Code::Let(_, body) => simp_inner(body.as_mut(), n),
        Code::Fun(fd, body) => {
            simp_inner(&mut fd.body, n);
            simp_inner(body.as_mut(), n);
        }
        Code::JoinPoint(jp, body) => {
            simp_inner(&mut jp.body, n);
            simp_inner(body.as_mut(), n);
        }
        Code::Cases(cases) => {
            for_each_alt(&mut cases.alts, &mut |b| simp_inner(b, n));
            if cases.alts.len() == 1 {
                if let Some(Alt::Default(body)) = cases.alts.first() {
                    *code = *body.clone();
                    *n += 1;
                    return;
                }
            }
            if cases.alts.len() > 1 {
                let first = cases.alts.first().and_then(|a| ret_fvar(a.body()));
                if let Some(fv) = first {
                    if cases.alts.iter().all(|a| ret_fvar(a.body()) == Some(fv)) {
                        *code = Code::ret(fv);
                        *n += 1;
                    }
                }
            }
        }
        _ => {}
    }
}

fn ret_fvar(code: &Code) -> Option<FVarId> {
    if let Code::Return(fv) = code {
        Some(*fv)
    } else {
        None
    }
}

// ─── Eta Reduction ──────────────────────────────────────────────────────────

fn reduce_eta(code: &mut Code) -> usize {
    let mut n = 0;
    eta_inner(code, &mut n);
    n
}

fn eta_inner(code: &mut Code, n: &mut usize) {
    match code {
        Code::Fun(fd, body) => {
            eta_inner(&mut fd.body, n);
            eta_inner(body.as_mut(), n);
            if detect_eta(fd).is_some() {
                *n += 1;
            }
        }
        Code::Let(_, body) => eta_inner(body.as_mut(), n),
        Code::JoinPoint(jp, body) => {
            eta_inner(&mut jp.body, n);
            eta_inner(body.as_mut(), n);
        }
        Code::Cases(c) => for_each_alt(&mut c.alts, &mut |b| eta_inner(b, n)),
        _ => {}
    }
}

fn detect_eta(fd: &FunDecl) -> Option<FVarId> {
    if let Code::Let(ld, body) = fd.body.as_ref() {
        if let Code::Return(rv) = body.as_ref() {
            if *rv != ld.fvar_id {
                return None;
            }
            if let LetValue::FVar { fvar, args } = &ld.value {
                if args.len() == fd.params.len()
                    && args
                        .iter()
                        .zip(&fd.params)
                        .all(|(a, p)| matches!(a, Arg::FVar(id) if *id == p.fvar_id))
                {
                    return Some(*fvar);
                }
            }
        }
    }
    None
}

// ─── Beta Reduction ─────────────────────────────────────────────────────────

fn reduce_beta(code: &mut Code) -> usize {
    let mut n = 0;
    beta_inner(code, &mut n);
    n
}

fn beta_inner(code: &mut Code, n: &mut usize) {
    match code {
        Code::Let(_, body) => beta_inner(body.as_mut(), n),
        Code::Fun(fd, body) => {
            beta_inner(&mut fd.body, n);
            beta_inner(body.as_mut(), n);
            if fd.params.is_empty() && matches!(fd.body.as_ref(), Code::Return(_)) {
                *n += 1;
            }
        }
        Code::JoinPoint(jp, body) => {
            beta_inner(&mut jp.body, n);
            beta_inner(body.as_mut(), n);
        }
        Code::Cases(c) => for_each_alt(&mut c.alts, &mut |b| beta_inner(b, n)),
        _ => {}
    }
}

// ─── Join Point Detection ───────────────────────────────────────────────────

fn detect_join_points(code: &mut Code) -> usize {
    let mut n = 0;
    jp_inner(code, &mut n);
    n
}

fn jp_inner(code: &mut Code, n: &mut usize) {
    let old = std::mem::replace(code, Code::Unreachable(Expr::const_str("_")));
    *code = match old {
        Code::Fun(mut fd, mut body) => {
            jp_inner(&mut fd.body, n);
            jp_inner(body.as_mut(), n);
            if only_tail(fd.fvar_id, &body) {
                *n += 1;
                Code::JoinPoint(fd, body)
            } else {
                Code::Fun(fd, body)
            }
        }
        Code::Let(d, mut b) => {
            jp_inner(b.as_mut(), n);
            Code::Let(d, b)
        }
        Code::JoinPoint(mut jp, mut b) => {
            jp_inner(&mut jp.body, n);
            jp_inner(b.as_mut(), n);
            Code::JoinPoint(jp, b)
        }
        Code::Cases(mut c) => {
            for_each_alt(&mut c.alts, &mut |b| jp_inner(b, n));
            Code::Cases(c)
        }
        other => other,
    };
}

fn only_tail(fv: FVarId, code: &Code) -> bool {
    match code {
        Code::Jmp { .. } | Code::Return(_) | Code::Unreachable(_) => true,
        Code::Let(d, body) => !letval_has_ref(&d.value, fv) && only_tail(fv, body),
        Code::Fun(fd, body) => !code_refs(fv, &fd.body) && only_tail(fv, body),
        Code::JoinPoint(jp, body) => only_tail(fv, &jp.body) && only_tail(fv, body),
        Code::Cases(c) => c.alts.iter().all(|a| only_tail(fv, a.body())),
    }
}

fn letval_has_ref(v: &LetValue, t: FVarId) -> bool {
    match v {
        LetValue::FVar { fvar, args } => {
            *fvar == t || args.iter().any(|a| matches!(a, Arg::FVar(id) if *id == t))
        }
        LetValue::Const { args, .. }
        | LetValue::Ctor { args, .. }
        | LetValue::Reuse { args, .. } => {
            args.iter().any(|a| matches!(a, Arg::FVar(id) if *id == t))
        }
        LetValue::Proj { structure, .. } => *structure == t,
        _ => false,
    }
}

fn code_refs(t: FVarId, code: &Code) -> bool {
    match code {
        Code::Return(fv) => *fv == t,
        Code::Jmp { jp, args } => {
            *jp == t || args.iter().any(|a| matches!(a, Arg::FVar(id) if *id == t))
        }
        Code::Let(d, b) => letval_has_ref(&d.value, t) || code_refs(t, b),
        Code::Fun(fd, b) => code_refs(t, &fd.body) || code_refs(t, b),
        Code::JoinPoint(jp, b) => code_refs(t, &jp.body) || code_refs(t, b),
        Code::Cases(c) => c.alts.iter().any(|a| code_refs(t, a.body())),
        Code::Unreachable(_) => false,
    }
}

// ─── Erased Argument Elimination ────────────────────────────────────────────

fn elim_erased(code: &mut Code) -> usize {
    let mut n = 0;
    erased_inner(code, &mut n);
    n
}

fn erased_inner(code: &mut Code, n: &mut usize) {
    match code {
        Code::Let(d, body) => {
            *n += strip_erased(&mut d.value);
            erased_inner(body.as_mut(), n);
        }
        Code::Fun(fd, body) => {
            erased_inner(&mut fd.body, n);
            erased_inner(body.as_mut(), n);
        }
        Code::JoinPoint(jp, body) => {
            erased_inner(&mut jp.body, n);
            erased_inner(body.as_mut(), n);
        }
        Code::Jmp { args, .. } => {
            let b = args.len();
            args.retain(|a| !a.is_erased());
            *n += b - args.len();
        }
        Code::Cases(c) => for_each_alt(&mut c.alts, &mut |b| erased_inner(b, n)),
        _ => {}
    }
}

fn strip_erased(v: &mut LetValue) -> usize {
    let args = match v {
        LetValue::Const { args, .. }
        | LetValue::FVar { args, .. }
        | LetValue::Ctor { args, .. }
        | LetValue::Reuse { args, .. } => args,
        _ => return 0,
    };
    let b = args.len();
    args.retain(|a| !a.is_erased());
    b - args.len()
}

// ─── Validation ─────────────────────────────────────────────────────────────

/// Validate LCNF invariants: bound variables, join points, non-empty cases.
pub(crate) fn validate_lcnf(decl: &Decl) -> Vec<ValidationError> {
    let mut errs = Vec::new();
    let mut bound: HashSet<FVarId> = decl.params.iter().map(|p| p.fvar_id).collect();
    let mut jps: HashSet<FVarId> = HashSet::new();
    if let crate::lcnf::DeclValue::Code(ref code) = decl.body {
        val_code(code, &mut bound, &mut jps, &mut errs);
    }
    errs
}

fn val_code(
    code: &Code,
    bound: &mut HashSet<FVarId>,
    jps: &mut HashSet<FVarId>,
    errs: &mut Vec<ValidationError>,
) {
    match code {
        Code::Return(fv) => {
            if !bound.contains(fv) {
                errs.push(ValidationError::UnboundReturn(*fv));
            }
        }
        Code::Let(d, body) => {
            val_refs(&d.value, bound, errs);
            bound.insert(d.fvar_id);
            val_code(body, bound, jps, errs);
        }
        Code::Fun(fd, body) => {
            bound.insert(fd.fvar_id);
            let mut ib = bound.clone();
            fd.params.iter().for_each(|p| {
                ib.insert(p.fvar_id);
            });
            val_code(&fd.body, &mut ib, jps, errs);
            val_code(body, bound, jps, errs);
        }
        Code::JoinPoint(jp, body) => {
            jps.insert(jp.fvar_id);
            bound.insert(jp.fvar_id);
            let mut ib = bound.clone();
            jp.params.iter().for_each(|p| {
                ib.insert(p.fvar_id);
            });
            val_code(&jp.body, &mut ib, jps, errs);
            val_code(body, bound, jps, errs);
        }
        Code::Jmp { jp, args } => {
            if !jps.contains(jp) {
                errs.push(ValidationError::UnboundJoinPoint(*jp));
            }
            for a in args {
                if let Arg::FVar(id) = a {
                    if !bound.contains(id) {
                        errs.push(ValidationError::UnboundLetRef(*id));
                    }
                }
            }
        }
        Code::Cases(c) => {
            if c.alts.is_empty() {
                errs.push(ValidationError::EmptyCaseAlts);
            }
            if !bound.contains(&c.scrutinee) {
                errs.push(ValidationError::UnboundLetRef(c.scrutinee));
            }
            for alt in &c.alts {
                let mut ab = bound.clone();
                if let Alt::Ctor { params, .. } = alt {
                    params.iter().for_each(|p| {
                        ab.insert(p.fvar_id);
                    });
                }
                val_code(alt.body(), &mut ab, jps, errs);
            }
        }
        Code::Unreachable(_) => {}
    }
}

fn val_refs(v: &LetValue, bound: &HashSet<FVarId>, errs: &mut Vec<ValidationError>) {
    let mut check = |id: &FVarId| {
        if !bound.contains(id) {
            errs.push(ValidationError::UnboundLetRef(*id));
        }
    };
    match v {
        LetValue::FVar { fvar, args } => {
            check(fvar);
            args.iter().for_each(|a| {
                if let Arg::FVar(id) = a {
                    check(id);
                }
            });
        }
        LetValue::Const { args, .. }
        | LetValue::Ctor { args, .. }
        | LetValue::Reuse { args, .. } => args.iter().for_each(|a| {
            if let Arg::FVar(id) = a {
                check(id);
            }
        }),
        LetValue::Proj { structure, .. } => check(structure),
        _ => {}
    }
}

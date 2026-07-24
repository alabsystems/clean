// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! ExtendJoinPointContext — duplicate outer let-bindings into join point bodies.
//!
//! Based on Lean 4's `JoinPointContextExtender`
//! (`src/Lean/Compiler/LCNF/JoinPoints.lean`).
//!
//! Join points can only use variables visible at their definition site.
//! This pass identifies "small" let-bindings (literals, projections,
//! nullary constructors) defined *outside* a join point but *used inside*
//! its body, and duplicates them into the join point via extra parameters.
//! Subsequent passes (inlining, CSE, simp) can then optimize the join
//! point body independently.
//!
//! # Algorithm
//!
//! 1. Walk code, collecting *candidate* small let-bindings.
//! 2. On `Fun` boundary, clear candidates (cannot lift jp across fun).
//! 3. At each `JoinPoint`, find candidates used in but not defined in
//!    the body. Generate fresh FVarIds, prepend duplicated let-bindings,
//!    add extra parameters, and rewrite `Jmp` sites with extra args.
//!
//! Part of #1101 - ExtendJoinPointContext compiler pass.

use crate::lcnf::{Alt, Arg, Cases, Code, Decl, DeclValue, FunDecl, LetDecl, LetValue, Param};
use clean_kernel::FVarId;
use std::collections::{HashMap, HashSet};

/// Returns `true` if a let-value is small enough to duplicate into a
/// join point body without risking code bloat.
fn is_small_value(value: &LetValue) -> bool {
    match value {
        LetValue::Lit(_) | LetValue::Erased | LetValue::Proj { .. } => true,
        LetValue::Ctor { args, .. }
        | LetValue::Const { args, .. }
        | LetValue::FVar { args, .. } => args.is_empty(),
        LetValue::Reuse { .. } => false,
    }
}

/// Collect every `FVarId` referenced (not defined) in a `LetValue`.
fn collect_fvars_in_value(value: &LetValue, out: &mut HashSet<FVarId>) {
    match value {
        LetValue::Lit(_) | LetValue::Erased => {}
        LetValue::Proj { structure, .. } => {
            out.insert(*structure);
        }
        LetValue::Const { args, .. } | LetValue::Ctor { args, .. } => {
            collect_fvar_args(args, out);
        }
        LetValue::FVar { fvar, args } => {
            out.insert(*fvar);
            collect_fvar_args(args, out);
        }
        LetValue::Reuse { slot, args, .. } => {
            out.insert(*slot);
            collect_fvar_args(args, out);
        }
    }
}

/// Collect `FVarId`s from an argument list.
fn collect_fvar_args(args: &[Arg], out: &mut HashSet<FVarId>) {
    for a in args {
        if let Arg::FVar(id) = a {
            out.insert(*id);
        }
    }
}

/// Collect every `FVarId` referenced in a `Code` tree.
fn collect_fvars_in_code(code: &Code, out: &mut HashSet<FVarId>) {
    match code {
        Code::Let(decl, body) => {
            collect_fvars_in_value(&decl.value, out);
            collect_fvars_in_code(body, out);
        }
        Code::Fun(fdecl, body) | Code::JoinPoint(fdecl, body) => {
            collect_fvars_in_code(&fdecl.body, out);
            collect_fvars_in_code(body, out);
        }
        Code::Cases(cases) => {
            out.insert(cases.scrutinee);
            for alt in &cases.alts {
                collect_fvars_in_code(alt.body(), out);
            }
        }
        Code::Jmp { jp, args } => {
            out.insert(*jp);
            collect_fvar_args(args, out);
        }
        Code::Return(fv) => {
            out.insert(*fv);
        }
        Code::Unreachable(_) => {}
    }
}

/// Collect all `FVarId`s *defined* (bound) in a code tree.
fn collect_defined_fvars(code: &Code, defined: &mut HashSet<FVarId>) {
    match code {
        Code::Let(decl, body) => {
            defined.insert(decl.fvar_id);
            collect_defined_fvars(body, defined);
        }
        Code::Fun(fdecl, body) | Code::JoinPoint(fdecl, body) => {
            defined.insert(fdecl.fvar_id);
            for p in &fdecl.params {
                defined.insert(p.fvar_id);
            }
            collect_defined_fvars(&fdecl.body, defined);
            collect_defined_fvars(body, defined);
        }
        Code::Cases(cases) => {
            for alt in &cases.alts {
                if let Alt::Ctor { params, body, .. } = alt {
                    for p in params {
                        defined.insert(p.fvar_id);
                    }
                    collect_defined_fvars(body, defined);
                } else {
                    collect_defined_fvars(alt.body(), defined);
                }
            }
        }
        Code::Jmp { .. } | Code::Return(_) | Code::Unreachable(_) => {}
    }
}

// -- Substitution helpers ---------------------------------------------------

fn subst_args(args: &[Arg], s: &HashMap<FVarId, FVarId>) -> Vec<Arg> {
    args.iter()
        .map(|a| match a {
            Arg::FVar(fv) => Arg::FVar(*s.get(fv).unwrap_or(fv)),
            other => other.clone(),
        })
        .collect()
}

fn subst_let_value(v: &LetValue, s: &HashMap<FVarId, FVarId>) -> LetValue {
    if s.is_empty() {
        return v.clone();
    }
    match v {
        LetValue::Lit(_) | LetValue::Erased => v.clone(),
        LetValue::Proj {
            type_name,
            idx,
            structure,
        } => LetValue::Proj {
            type_name: type_name.clone(),
            idx: *idx,
            structure: *s.get(structure).unwrap_or(structure),
        },
        LetValue::Const { name, levels, args } => LetValue::Const {
            name: name.clone(),
            levels: levels.clone(),
            args: subst_args(args, s),
        },
        LetValue::FVar { fvar, args } => LetValue::FVar {
            fvar: *s.get(fvar).unwrap_or(fvar),
            args: subst_args(args, s),
        },
        LetValue::Ctor { name, levels, args } => LetValue::Ctor {
            name: name.clone(),
            levels: levels.clone(),
            args: subst_args(args, s),
        },
        LetValue::Reuse {
            slot,
            ctor_name,
            levels,
            args,
        } => LetValue::Reuse {
            slot: *s.get(slot).unwrap_or(slot),
            ctor_name: ctor_name.clone(),
            levels: levels.clone(),
            args: subst_args(args, s),
        },
    }
}

fn subst_code(code: &Code, s: &HashMap<FVarId, FVarId>) -> Code {
    if s.is_empty() {
        return code.clone();
    }
    match code {
        Code::Let(d, body) => Code::Let(
            LetDecl {
                fvar_id: d.fvar_id,
                name: d.name.clone(),
                ty: d.ty.clone(),
                value: subst_let_value(&d.value, s),
            },
            Box::new(subst_code(body, s)),
        ),
        Code::Fun(fd, body) => Code::Fun(
            rebuild_fd(fd, subst_code(&fd.body, s)),
            Box::new(subst_code(body, s)),
        ),
        Code::JoinPoint(fd, body) => Code::JoinPoint(
            rebuild_fd(fd, subst_code(&fd.body, s)),
            Box::new(subst_code(body, s)),
        ),
        Code::Cases(c) => Code::Cases(Cases {
            type_name: c.type_name.clone(),
            result_type: c.result_type.clone(),
            scrutinee: *s.get(&c.scrutinee).unwrap_or(&c.scrutinee),
            alts: c.alts.iter().map(|a| subst_alt(a, s)).collect(),
        }),
        Code::Jmp { jp, args } => Code::Jmp {
            jp: *s.get(jp).unwrap_or(jp),
            args: subst_args(args, s),
        },
        Code::Return(fv) => Code::Return(*s.get(fv).unwrap_or(fv)),
        Code::Unreachable(ty) => Code::Unreachable(ty.clone()),
    }
}

fn subst_alt(alt: &Alt, s: &HashMap<FVarId, FVarId>) -> Alt {
    match alt {
        Alt::Ctor {
            ctor_name,
            params,
            body,
        } => Alt::Ctor {
            ctor_name: ctor_name.clone(),
            params: params.clone(),
            body: Box::new(subst_code(body, s)),
        },
        Alt::Default(body) => Alt::Default(Box::new(subst_code(body, s))),
    }
}

fn rebuild_fd(fd: &FunDecl, body: Code) -> FunDecl {
    FunDecl {
        fvar_id: fd.fvar_id,
        name: fd.name.clone(),
        params: fd.params.clone(),
        ty: fd.ty.clone(),
        body: Box::new(body),
    }
}

// -- Fresh FVarId generation ------------------------------------------------

fn find_max_fvar(code: &Code) -> u64 {
    let mut m = 0u64;
    max_fvar_impl(code, &mut m);
    m
}

fn max_fvar_impl(code: &Code, m: &mut u64) {
    match code {
        Code::Let(d, body) => {
            bump(d.fvar_id, m);
            max_val(&d.value, m);
            max_fvar_impl(body, m);
        }
        Code::Fun(fd, body) | Code::JoinPoint(fd, body) => {
            bump(fd.fvar_id, m);
            for p in &fd.params {
                bump(p.fvar_id, m);
            }
            max_fvar_impl(&fd.body, m);
            max_fvar_impl(body, m);
        }
        Code::Cases(c) => {
            bump(c.scrutinee, m);
            for alt in &c.alts {
                if let Alt::Ctor { params, .. } = alt {
                    for p in params {
                        bump(p.fvar_id, m);
                    }
                }
                max_fvar_impl(alt.body(), m);
            }
        }
        Code::Jmp { jp, args } => {
            bump(*jp, m);
            for a in args {
                if let Arg::FVar(id) = a {
                    bump(*id, m);
                }
            }
        }
        Code::Return(fv) => bump(*fv, m),
        Code::Unreachable(_) => {}
    }
}

fn max_val(v: &LetValue, m: &mut u64) {
    match v {
        LetValue::Lit(_) | LetValue::Erased => {}
        LetValue::Proj { structure, .. } => bump(*structure, m),
        LetValue::Const { args, .. } | LetValue::Ctor { args, .. } => {
            for a in args {
                if let Arg::FVar(id) = a {
                    bump(*id, m);
                }
            }
        }
        LetValue::FVar { fvar, args } => {
            bump(*fvar, m);
            for a in args {
                if let Arg::FVar(id) = a {
                    bump(*id, m);
                }
            }
        }
        LetValue::Reuse { slot, args, .. } => {
            bump(*slot, m);
            for a in args {
                if let Arg::FVar(id) = a {
                    bump(*id, m);
                }
            }
        }
    }
}

fn bump(fv: FVarId, m: &mut u64) {
    let v = fv.as_u64();
    if v > *m {
        *m = v;
    }
}

fn fresh(c: &mut u64) -> FVarId {
    let id = *c;
    *c += 1;
    FVarId::new(id)
}

// -- Core pass implementation -----------------------------------------------

/// Extend join point contexts in an LCNF `Code` block.
#[must_use]
pub fn extend_jp_context_in_code(code: &Code) -> Code {
    let mut counter = find_max_fvar(code) + 1;
    extend_impl(code, &HashMap::new(), &mut counter)
}

/// Recursive pass: collects candidates and extends join points.
fn extend_impl(code: &Code, cands: &HashMap<FVarId, LetDecl>, ctr: &mut u64) -> Code {
    match code {
        Code::Let(d, body) => {
            let mut new_c = cands.clone();
            if is_small_value(&d.value) {
                new_c.insert(d.fvar_id, d.clone());
            }
            Code::Let(d.clone(), Box::new(extend_impl(body, &new_c, ctr)))
        }
        Code::Fun(fd, body) => {
            // Fun boundary clears candidates.
            let inner = extend_impl(&fd.body, &HashMap::new(), ctr);
            Code::Fun(
                rebuild_fd(fd, inner),
                Box::new(extend_impl(body, cands, ctr)),
            )
        }
        Code::JoinPoint(fd, body) => extend_jp(fd, body, cands, ctr),
        Code::Cases(c) => Code::Cases(Cases {
            type_name: c.type_name.clone(),
            result_type: c.result_type.clone(),
            scrutinee: c.scrutinee,
            alts: c.alts.iter().map(|a| extend_alt(a, cands, ctr)).collect(),
        }),
        _ => code.clone(),
    }
}

fn extend_alt(alt: &Alt, cands: &HashMap<FVarId, LetDecl>, ctr: &mut u64) -> Alt {
    match alt {
        Alt::Ctor {
            ctor_name,
            params,
            body,
        } => Alt::Ctor {
            ctor_name: ctor_name.clone(),
            params: params.clone(),
            body: Box::new(extend_impl(body, cands, ctr)),
        },
        Alt::Default(body) => Alt::Default(Box::new(extend_impl(body, cands, ctr))),
    }
}

/// Process a single `JoinPoint`: find outer candidates used inside,
/// duplicate them via extra parameters, rewrite Jmp sites.
fn extend_jp(fd: &FunDecl, body: &Code, cands: &HashMap<FVarId, LetDecl>, ctr: &mut u64) -> Code {
    let proc_jp_body = extend_impl(&fd.body, cands, ctr);

    // FVarIds used in the jp body.
    let mut used = HashSet::new();
    collect_fvars_in_code(&proc_jp_body, &mut used);

    // FVarIds defined inside the jp (params + body bindings).
    let mut jp_defined: HashSet<FVarId> = fd.params.iter().map(|p| p.fvar_id).collect();
    collect_defined_fvars(&proc_jp_body, &mut jp_defined);

    // Find candidates that are used but not defined inside the jp.
    let mut exts: Vec<(FVarId, FVarId, LetDecl)> = Vec::new();
    let mut ext_set = HashSet::new();
    let mut sorted_cands: Vec<FVarId> = cands.keys().copied().collect();
    sorted_cands.sort();

    for &orig in &sorted_cands {
        if !used.contains(&orig) || jp_defined.contains(&orig) {
            continue;
        }
        // Verify candidate dependencies are available.
        let decl = &cands[&orig];
        let mut deps = HashSet::new();
        collect_fvars_in_value(&decl.value, &mut deps);
        if !deps
            .iter()
            .all(|d| jp_defined.contains(d) || ext_set.contains(d))
        {
            continue;
        }
        let f = fresh(ctr);
        let fd_dup = LetDecl {
            fvar_id: f,
            name: decl.name.clone(),
            ty: decl.ty.clone(),
            value: decl.value.clone(),
        };
        exts.push((orig, f, fd_dup));
        ext_set.insert(orig);
    }

    if exts.is_empty() {
        let new_fd = rebuild_fd(fd, proc_jp_body);
        let proc_body = extend_impl(body, cands, ctr);
        return Code::JoinPoint(new_fd, Box::new(proc_body));
    }

    // Build substitution and apply it.
    let subst: HashMap<FVarId, FVarId> = exts.iter().map(|(o, f, _)| (*o, *f)).collect();

    let sub_body = subst_code(&proc_jp_body, &subst);

    // Prepend duplicated let-bindings (in order) before the jp body.
    let mut ext_body = sub_body;
    for (_, _, dup) in exts.iter().rev() {
        let mut d = dup.clone();
        d.value = subst_let_value(&d.value, &subst);
        ext_body = Code::Let(d, Box::new(ext_body));
    }

    // Extra params prepended to existing params.
    let extra_params: Vec<Param> = exts
        .iter()
        .map(|(_, f, d)| Param::new(*f, d.name.clone(), d.ty.clone()))
        .collect();
    let mut new_params = extra_params;
    new_params.extend(fd.params.iter().cloned());

    let new_fd = FunDecl {
        fvar_id: fd.fvar_id,
        name: fd.name.clone(),
        params: new_params,
        ty: fd.ty.clone(),
        body: Box::new(ext_body),
    };

    let extra_fvars: Vec<FVarId> = exts.iter().map(|(o, _, _)| *o).collect();
    let proc_body = extend_impl(body, cands, ctr);
    let rw_body = prepend_jmp_args(&proc_body, fd.fvar_id, &extra_fvars);

    Code::JoinPoint(new_fd, Box::new(rw_body))
}

/// Prepend extra `Arg::FVar` arguments at every `Jmp` targeting `target`.
fn prepend_jmp_args(code: &Code, target: FVarId, extra: &[FVarId]) -> Code {
    match code {
        Code::Let(d, body) => Code::Let(d.clone(), Box::new(prepend_jmp_args(body, target, extra))),
        Code::Fun(fd, body) => Code::Fun(
            rebuild_fd(fd, prepend_jmp_args(&fd.body, target, extra)),
            Box::new(prepend_jmp_args(body, target, extra)),
        ),
        Code::JoinPoint(fd, body) => {
            let jp_body = if fd.fvar_id != target {
                prepend_jmp_args(&fd.body, target, extra)
            } else {
                *fd.body.clone()
            };
            Code::JoinPoint(
                rebuild_fd(fd, jp_body),
                Box::new(prepend_jmp_args(body, target, extra)),
            )
        }
        Code::Cases(c) => Code::Cases(Cases {
            type_name: c.type_name.clone(),
            result_type: c.result_type.clone(),
            scrutinee: c.scrutinee,
            alts: c
                .alts
                .iter()
                .map(|a| prepend_jmp_alt(a, target, extra))
                .collect(),
        }),
        Code::Jmp { jp, args } if *jp == target => {
            let mut new_args: Vec<Arg> = extra.iter().map(|fv| Arg::FVar(*fv)).collect();
            new_args.extend(args.iter().cloned());
            Code::Jmp {
                jp: *jp,
                args: new_args,
            }
        }
        _ => code.clone(),
    }
}

fn prepend_jmp_alt(alt: &Alt, target: FVarId, extra: &[FVarId]) -> Alt {
    match alt {
        Alt::Ctor {
            ctor_name,
            params,
            body,
        } => Alt::Ctor {
            ctor_name: ctor_name.clone(),
            params: params.clone(),
            body: Box::new(prepend_jmp_args(body, target, extra)),
        },
        Alt::Default(body) => Alt::Default(Box::new(prepend_jmp_args(body, target, extra))),
    }
}

// -- Declaration-level entry point ------------------------------------------

/// Extend join point contexts in an LCNF declaration.
#[must_use]
pub fn extend_jp_context(decl: &Decl) -> Decl {
    let new_body = match &decl.body {
        DeclValue::Code(c) => DeclValue::Code(Box::new(extend_jp_context_in_code(c))),
        DeclValue::Extern(a) => DeclValue::Extern(a.clone()),
    };
    Decl {
        name: decl.name.clone(),
        level_params: decl.level_params.clone(),
        ty: decl.ty.clone(),
        params: decl.params.clone(),
        body: new_body,
        recursive: decl.recursive,
    }
}

#[cfg(test)]
mod tests;

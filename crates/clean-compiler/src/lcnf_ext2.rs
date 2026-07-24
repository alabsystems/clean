// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended LCNF transformations: substitution, alpha-equivalence, and
//! well-formedness validation.
//!
//! Statistics, free variables, summary, and complexity live in `lcnf_ext`.
//!
//! Part of #3082 — LCNF extensibility.

use crate::lcnf::{Alt, Arg, Cases, Code, FunDecl, LetDecl, LetValue};
use clean_kernel::FVarId;
use std::collections::{BTreeSet, HashMap};
use thiserror::Error;

// ════════════════════════════════════════════════════════════════════════════
// Error types
// ════════════════════════════════════════════════════════════════════════════

/// Errors from LCNF analysis and transformation.
#[derive(Debug, Error)]
#[non_exhaustive]
pub(crate) enum LcnfExtError {
    /// A free variable was used but never bound.
    #[error("unbound variable: FVarId({0})")]
    UnboundVariable(u64),

    /// Substitution target not found.
    #[error("substitution target FVarId({0}) not found in expression")]
    SubstitutionTargetNotFound(u64),

    /// A join point is jumped to with wrong argument count.
    #[error("join point FVarId({jp}) expects {expected} args, got {actual}")]
    JoinPointArityMismatch {
        jp: u64,
        expected: usize,
        actual: usize,
    },

    /// Duplicate binding for the same FVarId.
    #[error("duplicate binding for FVarId({0})")]
    DuplicateBinding(u64),
}

// ════════════════════════════════════════════════════════════════════════════
// Substitution
// ════════════════════════════════════════════════════════════════════════════

/// Substitute free variable occurrences in a `Code` tree.
///
/// Replaces every use-site `Arg::FVar(from)`, `Return(from)`, scrutinee, etc.
/// with `to`. Does NOT substitute into binding positions.
///
/// Returns an error if `from` never appeared in any use-site (the mapping
/// was vacuous), which often indicates a caller bug.
pub(crate) fn substitute_fvar(code: &Code, from: FVarId, to: FVarId) -> Result<Code, LcnfExtError> {
    let mut found = false;
    let result = subst_code(code, from, to, &mut found);
    if found {
        Ok(result)
    } else {
        Err(LcnfExtError::SubstitutionTargetNotFound(from.as_u64()))
    }
}

fn subst_code(code: &Code, from: FVarId, to: FVarId, found: &mut bool) -> Code {
    match code {
        Code::Let(decl, body) => {
            let new_value = subst_let_value(&decl.value, from, to, found);
            let new_decl = LetDecl {
                fvar_id: decl.fvar_id,
                name: decl.name.clone(),
                ty: decl.ty.clone(),
                value: new_value,
            };
            Code::Let(new_decl, Box::new(subst_code(body, from, to, found)))
        }
        Code::Fun(decl, body) => {
            let new_fun = subst_fun_decl(decl, from, to, found);
            Code::Fun(new_fun, Box::new(subst_code(body, from, to, found)))
        }
        Code::JoinPoint(decl, body) => {
            let new_fun = subst_fun_decl(decl, from, to, found);
            Code::JoinPoint(new_fun, Box::new(subst_code(body, from, to, found)))
        }
        Code::Cases(cases) => {
            let scrutinee = subst_fvar_id(cases.scrutinee, from, to, found);
            let alts = cases
                .alts
                .iter()
                .map(|alt| subst_alt(alt, from, to, found))
                .collect();
            Code::Cases(Cases {
                type_name: cases.type_name.clone(),
                result_type: cases.result_type.clone(),
                scrutinee,
                alts,
            })
        }
        Code::Jmp { jp, args } => {
            let new_jp = subst_fvar_id(*jp, from, to, found);
            let new_args = args.iter().map(|a| subst_arg(a, from, to, found)).collect();
            Code::Jmp {
                jp: new_jp,
                args: new_args,
            }
        }
        Code::Return(fvar) => Code::Return(subst_fvar_id(*fvar, from, to, found)),
        Code::Unreachable(ty) => Code::Unreachable(ty.clone()),
    }
}

fn subst_alt(alt: &Alt, from: FVarId, to: FVarId, found: &mut bool) -> Alt {
    match alt {
        Alt::Ctor {
            ctor_name,
            params,
            body,
        } => Alt::Ctor {
            ctor_name: ctor_name.clone(),
            params: params.clone(),
            body: Box::new(subst_code(body, from, to, found)),
        },
        Alt::Default(body) => Alt::Default(Box::new(subst_code(body, from, to, found))),
    }
}

fn subst_fun_decl(decl: &FunDecl, from: FVarId, to: FVarId, found: &mut bool) -> FunDecl {
    FunDecl {
        fvar_id: decl.fvar_id,
        name: decl.name.clone(),
        params: decl.params.clone(),
        ty: decl.ty.clone(),
        body: Box::new(subst_code(&decl.body, from, to, found)),
    }
}

fn subst_let_value(val: &LetValue, from: FVarId, to: FVarId, found: &mut bool) -> LetValue {
    match val {
        LetValue::Proj {
            type_name,
            idx,
            structure,
        } => LetValue::Proj {
            type_name: type_name.clone(),
            idx: *idx,
            structure: subst_fvar_id(*structure, from, to, found),
        },
        LetValue::FVar { fvar, args } => LetValue::FVar {
            fvar: subst_fvar_id(*fvar, from, to, found),
            args: args.iter().map(|a| subst_arg(a, from, to, found)).collect(),
        },
        LetValue::Const { name, levels, args } => LetValue::Const {
            name: name.clone(),
            levels: levels.clone(),
            args: args.iter().map(|a| subst_arg(a, from, to, found)).collect(),
        },
        LetValue::Ctor { name, levels, args } => LetValue::Ctor {
            name: name.clone(),
            levels: levels.clone(),
            args: args.iter().map(|a| subst_arg(a, from, to, found)).collect(),
        },
        LetValue::Reuse {
            slot,
            ctor_name,
            levels,
            args,
        } => LetValue::Reuse {
            slot: subst_fvar_id(*slot, from, to, found),
            ctor_name: ctor_name.clone(),
            levels: levels.clone(),
            args: args.iter().map(|a| subst_arg(a, from, to, found)).collect(),
        },
        LetValue::Lit(_) | LetValue::Erased => val.clone(),
    }
}

fn subst_arg(arg: &Arg, from: FVarId, to: FVarId, found: &mut bool) -> Arg {
    match arg {
        Arg::FVar(id) if *id == from => {
            *found = true;
            Arg::FVar(to)
        }
        _ => arg.clone(),
    }
}

fn subst_fvar_id(id: FVarId, from: FVarId, to: FVarId, found: &mut bool) -> FVarId {
    if id == from {
        *found = true;
        to
    } else {
        id
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Alpha-equivalence comparison
// ════════════════════════════════════════════════════════════════════════════

/// Check structural (alpha-equivalent) equality of two `Code` trees.
///
/// Bound variable identities are mapped positionally: the first let-binding
/// in each tree is matched, the second is matched, etc. Free variables must
/// be identical (same FVarId).
#[must_use]
pub(crate) fn alpha_eq(a: &Code, b: &Code) -> bool {
    let mut map_a = HashMap::new();
    let mut map_b = HashMap::new();
    let mut next_id: u64 = 0;
    alpha_eq_code(a, b, &mut map_a, &mut map_b, &mut next_id)
}

fn alpha_eq_code(
    a: &Code,
    b: &Code,
    map_a: &mut HashMap<FVarId, u64>,
    map_b: &mut HashMap<FVarId, u64>,
    next: &mut u64,
) -> bool {
    match (a, b) {
        (Code::Let(da, ba), Code::Let(db, bb)) => {
            if !alpha_eq_let_value(&da.value, &db.value, map_a, map_b) {
                return false;
            }
            let id = *next;
            *next += 1;
            map_a.insert(da.fvar_id, id);
            map_b.insert(db.fvar_id, id);
            alpha_eq_code(ba, bb, map_a, map_b, next)
        }
        (Code::Fun(da, ba), Code::Fun(db, bb))
        | (Code::JoinPoint(da, ba), Code::JoinPoint(db, bb)) => {
            if da.params.len() != db.params.len() {
                return false;
            }
            let id = *next;
            *next += 1;
            map_a.insert(da.fvar_id, id);
            map_b.insert(db.fvar_id, id);
            for (pa, pb) in da.params.iter().zip(db.params.iter()) {
                let pid = *next;
                *next += 1;
                map_a.insert(pa.fvar_id, pid);
                map_b.insert(pb.fvar_id, pid);
            }
            alpha_eq_code(&da.body, &db.body, map_a, map_b, next)
                && alpha_eq_code(ba, bb, map_a, map_b, next)
        }
        (Code::Cases(ca), Code::Cases(cb)) => {
            if !resolve_eq(ca.scrutinee, cb.scrutinee, map_a, map_b) {
                return false;
            }
            if ca.alts.len() != cb.alts.len() {
                return false;
            }
            ca.alts
                .iter()
                .zip(cb.alts.iter())
                .all(|(aa, ab)| alpha_eq_alt(aa, ab, &mut map_a.clone(), &mut map_b.clone(), next))
        }
        (Code::Jmp { jp: ja, args: aa }, Code::Jmp { jp: jb, args: ab }) => {
            resolve_eq(*ja, *jb, map_a, map_b)
                && aa.len() == ab.len()
                && aa
                    .iter()
                    .zip(ab.iter())
                    .all(|(x, y)| alpha_eq_arg(x, y, map_a, map_b))
        }
        (Code::Return(fa), Code::Return(fb)) => resolve_eq(*fa, *fb, map_a, map_b),
        (Code::Unreachable(_), Code::Unreachable(_)) => true,
        _ => false,
    }
}

fn alpha_eq_alt(
    a: &Alt,
    b: &Alt,
    map_a: &mut HashMap<FVarId, u64>,
    map_b: &mut HashMap<FVarId, u64>,
    next: &mut u64,
) -> bool {
    match (a, b) {
        (
            Alt::Ctor {
                ctor_name: na,
                params: pa,
                body: ba,
            },
            Alt::Ctor {
                ctor_name: nb,
                params: pb,
                body: bb,
            },
        ) => {
            if na != nb || pa.len() != pb.len() {
                return false;
            }
            for (x, y) in pa.iter().zip(pb.iter()) {
                let id = *next;
                *next += 1;
                map_a.insert(x.fvar_id, id);
                map_b.insert(y.fvar_id, id);
            }
            alpha_eq_code(ba, bb, map_a, map_b, next)
        }
        (Alt::Default(ba), Alt::Default(bb)) => alpha_eq_code(ba, bb, map_a, map_b, next),
        _ => false,
    }
}

fn alpha_eq_let_value(
    a: &LetValue,
    b: &LetValue,
    map_a: &HashMap<FVarId, u64>,
    map_b: &HashMap<FVarId, u64>,
) -> bool {
    match (a, b) {
        (LetValue::Lit(la), LetValue::Lit(lb)) => la == lb,
        (LetValue::Erased, LetValue::Erased) => true,
        (
            LetValue::Proj {
                type_name: na,
                idx: ia,
                structure: sa,
            },
            LetValue::Proj {
                type_name: nb,
                idx: ib,
                structure: sb,
            },
        ) => na == nb && ia == ib && resolve_eq(*sa, *sb, map_a, map_b),
        (
            LetValue::Const {
                name: na, args: aa, ..
            },
            LetValue::Const {
                name: nb, args: ab, ..
            },
        ) => {
            na == nb
                && aa.len() == ab.len()
                && aa
                    .iter()
                    .zip(ab.iter())
                    .all(|(x, y)| alpha_eq_arg(x, y, map_a, map_b))
        }
        (LetValue::FVar { fvar: fa, args: aa }, LetValue::FVar { fvar: fb, args: ab }) => {
            resolve_eq(*fa, *fb, map_a, map_b)
                && aa.len() == ab.len()
                && aa
                    .iter()
                    .zip(ab.iter())
                    .all(|(x, y)| alpha_eq_arg(x, y, map_a, map_b))
        }
        (
            LetValue::Ctor {
                name: na, args: aa, ..
            },
            LetValue::Ctor {
                name: nb, args: ab, ..
            },
        ) => {
            na == nb
                && aa.len() == ab.len()
                && aa
                    .iter()
                    .zip(ab.iter())
                    .all(|(x, y)| alpha_eq_arg(x, y, map_a, map_b))
        }
        (
            LetValue::Reuse {
                slot: sa,
                ctor_name: na,
                args: aa,
                ..
            },
            LetValue::Reuse {
                slot: sb,
                ctor_name: nb,
                args: ab,
                ..
            },
        ) => {
            resolve_eq(*sa, *sb, map_a, map_b)
                && na == nb
                && aa.len() == ab.len()
                && aa
                    .iter()
                    .zip(ab.iter())
                    .all(|(x, y)| alpha_eq_arg(x, y, map_a, map_b))
        }
        _ => false,
    }
}

fn alpha_eq_arg(
    a: &Arg,
    b: &Arg,
    map_a: &HashMap<FVarId, u64>,
    map_b: &HashMap<FVarId, u64>,
) -> bool {
    match (a, b) {
        (Arg::Erased, Arg::Erased) => true,
        (Arg::FVar(fa), Arg::FVar(fb)) => resolve_eq(*fa, *fb, map_a, map_b),
        (Arg::Index(ia), Arg::Index(ib)) => ia == ib,
        (Arg::Type(ea), Arg::Type(eb)) => ea == eb,
        _ => false,
    }
}

fn resolve_eq(
    a: FVarId,
    b: FVarId,
    map_a: &HashMap<FVarId, u64>,
    map_b: &HashMap<FVarId, u64>,
) -> bool {
    match (map_a.get(&a), map_b.get(&b)) {
        (Some(ia), Some(ib)) => ia == ib,
        (None, None) => a == b,
        _ => false,
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Validation (well-formedness)
// ════════════════════════════════════════════════════════════════════════════

/// Validate well-formedness of a `Code` tree.
///
/// Checks:
/// - Every used variable is bound (no dangling references).
/// - No duplicate bindings in the same scope.
/// - Join point jumps reference variables that were bound as JoinPoints.
pub(crate) fn validate(code: &Code) -> Result<(), LcnfExtError> {
    let mut bound = BTreeSet::new();
    let mut join_points: HashMap<FVarId, usize> = HashMap::new();
    validate_code(code, &mut bound, &mut join_points)
}

fn validate_code(
    code: &Code,
    bound: &mut BTreeSet<FVarId>,
    jps: &mut HashMap<FVarId, usize>,
) -> Result<(), LcnfExtError> {
    match code {
        Code::Let(decl, body) => {
            validate_let_value(&decl.value, bound)?;
            if !bound.insert(decl.fvar_id) {
                return Err(LcnfExtError::DuplicateBinding(decl.fvar_id.as_u64()));
            }
            validate_code(body, bound, jps)
        }
        Code::Fun(decl, body) => {
            if !bound.insert(decl.fvar_id) {
                return Err(LcnfExtError::DuplicateBinding(decl.fvar_id.as_u64()));
            }
            let mut inner = bound.clone();
            for p in &decl.params {
                inner.insert(p.fvar_id);
            }
            validate_code(&decl.body, &mut inner, &mut jps.clone())?;
            validate_code(body, bound, jps)
        }
        Code::JoinPoint(decl, body) => {
            if !bound.insert(decl.fvar_id) {
                return Err(LcnfExtError::DuplicateBinding(decl.fvar_id.as_u64()));
            }
            jps.insert(decl.fvar_id, decl.params.len());
            let mut inner = bound.clone();
            for p in &decl.params {
                inner.insert(p.fvar_id);
            }
            validate_code(&decl.body, &mut inner, &mut jps.clone())?;
            validate_code(body, bound, jps)
        }
        Code::Cases(cases) => {
            if !bound.contains(&cases.scrutinee) {
                return Err(LcnfExtError::UnboundVariable(cases.scrutinee.as_u64()));
            }
            for alt in &cases.alts {
                let mut alt_bound = bound.clone();
                if let Alt::Ctor { params, .. } = alt {
                    for p in params {
                        alt_bound.insert(p.fvar_id);
                    }
                }
                validate_code(alt.body(), &mut alt_bound, &mut jps.clone())?;
            }
            Ok(())
        }
        Code::Jmp { jp, args } => {
            if !bound.contains(jp) {
                return Err(LcnfExtError::UnboundVariable(jp.as_u64()));
            }
            if let Some(&expected) = jps.get(jp) {
                if args.len() != expected {
                    return Err(LcnfExtError::JoinPointArityMismatch {
                        jp: jp.as_u64(),
                        expected,
                        actual: args.len(),
                    });
                }
            }
            for arg in args {
                validate_arg(arg, bound)?;
            }
            Ok(())
        }
        Code::Return(fvar) => {
            if !bound.contains(fvar) {
                return Err(LcnfExtError::UnboundVariable(fvar.as_u64()));
            }
            Ok(())
        }
        Code::Unreachable(_) => Ok(()),
    }
}

fn validate_let_value(val: &LetValue, bound: &BTreeSet<FVarId>) -> Result<(), LcnfExtError> {
    match val {
        LetValue::Proj { structure, .. } => {
            if !bound.contains(structure) {
                return Err(LcnfExtError::UnboundVariable(structure.as_u64()));
            }
            Ok(())
        }
        LetValue::FVar { fvar, args } => {
            if !bound.contains(fvar) {
                return Err(LcnfExtError::UnboundVariable(fvar.as_u64()));
            }
            for a in args {
                validate_arg(a, bound)?;
            }
            Ok(())
        }
        LetValue::Const { args, .. } | LetValue::Ctor { args, .. } => {
            for a in args {
                validate_arg(a, bound)?;
            }
            Ok(())
        }
        LetValue::Reuse { slot, args, .. } => {
            if !bound.contains(slot) {
                return Err(LcnfExtError::UnboundVariable(slot.as_u64()));
            }
            for a in args {
                validate_arg(a, bound)?;
            }
            Ok(())
        }
        LetValue::Lit(_) | LetValue::Erased => Ok(()),
    }
}

fn validate_arg(arg: &Arg, bound: &BTreeSet<FVarId>) -> Result<(), LcnfExtError> {
    if let Arg::FVar(id) = arg {
        if !bound.contains(id) {
            return Err(LcnfExtError::UnboundVariable(id.as_u64()));
        }
    }
    Ok(())
}

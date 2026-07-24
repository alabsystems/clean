// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended IR ID normalization — alpha equivalence, hash-consing,
//! collision detection, and declaration name normalization.
//!
//! Builds on [`crate::ir_norm_ids`] (basic sequential renumbering) with:
//! - Separate var/JP counters and statistics tracking
//! - Alpha equivalence via canonical form comparison
//! - Content-based hashing for normalized IR
//! - Declaration name normalization (mangle/demangle)
//! - ID collision detection
//!
//! Part of #3083 — Extensibility.

use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};

use crate::ir::{IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRLiteral, IRType, JoinPointId, VarId};

/// Statistics collected during normalization.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct NormStats {
    pub(crate) vars_renamed: u32,
    pub(crate) jps_renamed: u32,
    pub(crate) collisions_found: u32,
}

/// Collisions found in an IR declaration.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct IdCollisions {
    pub(crate) duplicate_vars: Vec<u32>,
    pub(crate) duplicate_jps: Vec<u32>,
}

impl IdCollisions {
    #[must_use]
    pub(crate) fn total(&self) -> usize {
        self.duplicate_vars.len() + self.duplicate_jps.len()
    }
    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.duplicate_vars.is_empty() && self.duplicate_jps.is_empty()
    }
}

// ─── Extended normalization state ──────────────────────────────────────

struct ExtNormState {
    next_var: u32,
    next_jp: u32,
    var_map: HashMap<u32, u32>,
    jp_map: HashMap<u32, u32>,
    stats: NormStats,
}

impl ExtNormState {
    fn new() -> Self {
        Self {
            next_var: 0,
            next_jp: 0,
            var_map: HashMap::new(),
            jp_map: HashMap::new(),
            stats: NormStats::default(),
        }
    }
    fn bind_var(&mut self, v: VarId) -> VarId {
        let id = self.next_var;
        self.next_var += 1;
        if v.0 != id {
            self.stats.vars_renamed += 1;
        }
        self.var_map.insert(v.0, id);
        VarId(id)
    }
    fn bind_jp(&mut self, jp: JoinPointId) -> JoinPointId {
        let id = self.next_jp;
        self.next_jp += 1;
        if jp.0 != id {
            self.stats.jps_renamed += 1;
        }
        self.jp_map.insert(jp.0, id);
        JoinPointId(id)
    }
    fn nv(&self, v: VarId) -> VarId {
        VarId(self.var_map.get(&v.0).copied().unwrap_or(v.0))
    }
    fn nj(&self, jp: JoinPointId) -> JoinPointId {
        JoinPointId(self.jp_map.get(&jp.0).copied().unwrap_or(jp.0))
    }
    fn na(&self, arg: &IRArg) -> IRArg {
        match arg {
            IRArg::Var(v) => IRArg::Var(self.nv(*v)),
            IRArg::Erased => IRArg::Erased,
        }
    }
    fn nas(&self, args: &[IRArg]) -> Vec<IRArg> {
        args.iter().map(|a| self.na(a)).collect()
    }
}

fn ext_norm_expr(s: &ExtNormState, e: &IRExpr) -> IRExpr {
    match e {
        IRExpr::Ctor { info, args } => IRExpr::Ctor {
            info: info.clone(),
            args: s.nas(args),
        },
        IRExpr::Proj { idx, ty, arg } => IRExpr::Proj {
            idx: *idx,
            ty: ty.clone(),
            arg: s.na(arg),
        },
        IRExpr::Tag(a) => IRExpr::Tag(s.na(a)),
        IRExpr::Box { ty, arg } => IRExpr::Box {
            ty: ty.clone(),
            arg: s.na(arg),
        },
        IRExpr::Unbox { ty, arg } => IRExpr::Unbox {
            ty: ty.clone(),
            arg: s.na(arg),
        },
        IRExpr::Lit(l) => IRExpr::Lit(l.clone()),
        IRExpr::Apply { fn_id, args } => IRExpr::Apply {
            fn_id: fn_id.clone(),
            args: s.nas(args),
        },
        IRExpr::PartialApply { fn_id, arity, args } => IRExpr::PartialApply {
            fn_id: fn_id.clone(),
            arity: *arity,
            args: s.nas(args),
        },
        IRExpr::ClosureApply { closure, args } => IRExpr::ClosureApply {
            closure: s.na(closure),
            args: s.nas(args),
        },
        IRExpr::UProj { idx, var } => IRExpr::UProj {
            idx: *idx,
            var: s.nv(*var),
        },
        IRExpr::SProj { n, offset, var, ty } => IRExpr::SProj {
            n: *n,
            offset: *offset,
            var: s.nv(*var),
            ty: ty.clone(),
        },
        IRExpr::IsShared(v) => IRExpr::IsShared(s.nv(*v)),
        IRExpr::String(st) => IRExpr::String(st.clone()),
        IRExpr::Reset(v) => IRExpr::Reset(s.nv(*v)),
        IRExpr::Reuse { var, ctor, args } => IRExpr::Reuse {
            var: s.nv(*var),
            ctor: ctor.clone(),
            args: s.nas(args),
        },
    }
}

fn ext_norm_body(s: &mut ExtNormState, b: &IRBody) -> IRBody {
    match b {
        IRBody::VDecl {
            var,
            ty,
            value,
            rest,
        } => {
            let nv = ext_norm_expr(s, value);
            let nvar = s.bind_var(*var);
            IRBody::VDecl {
                var: nvar,
                ty: ty.clone(),
                value: nv,
                rest: Box::new(ext_norm_body(s, rest)),
            }
        }
        IRBody::JDecl {
            jp,
            params,
            body,
            rest,
        } => {
            let np: Vec<_> = params
                .iter()
                .map(|(v, t)| (s.bind_var(*v), t.clone()))
                .collect();
            let nb = ext_norm_body(s, body);
            let njp = s.bind_jp(*jp);
            IRBody::JDecl {
                jp: njp,
                params: np,
                body: Box::new(nb),
                rest: Box::new(ext_norm_body(s, rest)),
            }
        }
        IRBody::Inc { var, n, rest } => IRBody::Inc {
            var: s.nv(*var),
            n: *n,
            rest: Box::new(ext_norm_body(s, rest)),
        },
        IRBody::Dec { var, rest } => IRBody::Dec {
            var: s.nv(*var),
            rest: Box::new(ext_norm_body(s, rest)),
        },
        IRBody::Set {
            var,
            idx,
            value,
            rest,
        } => IRBody::Set {
            var: s.nv(*var),
            idx: *idx,
            value: s.nv(*value),
            rest: Box::new(ext_norm_body(s, rest)),
        },
        IRBody::SetTag { var, tag, rest } => IRBody::SetTag {
            var: s.nv(*var),
            tag: *tag,
            rest: Box::new(ext_norm_body(s, rest)),
        },
        IRBody::USet {
            var,
            idx,
            value,
            rest,
        } => IRBody::USet {
            var: s.nv(*var),
            idx: *idx,
            value: s.nv(*value),
            rest: Box::new(ext_norm_body(s, rest)),
        },
        IRBody::SSet {
            var,
            n,
            offset,
            value,
            ty,
            rest,
        } => IRBody::SSet {
            var: s.nv(*var),
            n: *n,
            offset: *offset,
            value: s.nv(*value),
            ty: ty.clone(),
            rest: Box::new(ext_norm_body(s, rest)),
        },
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => IRBody::Case {
            scrutinee: s.nv(*scrutinee),
            alts: alts
                .iter()
                .map(|a| IRAlt {
                    ctor: a.ctor.clone(),
                    body: Box::new(ext_norm_body(s, &a.body)),
                })
                .collect(),
            default: default.as_ref().map(|d| Box::new(ext_norm_body(s, d))),
        },
        IRBody::Jmp { jp, args } => IRBody::Jmp {
            jp: s.nj(*jp),
            args: s.nas(args),
        },
        IRBody::Ret(a) => IRBody::Ret(s.na(a)),
        IRBody::Unreachable => IRBody::Unreachable,
    }
}

// ─── Hash-consing helpers ──────────────────────────────────────────────

fn hash_arg(h: &mut impl Hasher, a: &IRArg) {
    match a {
        IRArg::Var(v) => {
            0u8.hash(h);
            v.0.hash(h);
        }
        IRArg::Erased => 1u8.hash(h),
    }
}

fn hash_type(h: &mut impl Hasher, ty: &IRType) {
    std::mem::discriminant(ty).hash(h);
    match ty {
        IRType::Struct(fs) => {
            fs.len().hash(h);
            for f in fs {
                hash_type(h, f);
            }
        }
        IRType::Union(vs) => {
            vs.len().hash(h);
            for v in vs {
                hash_type(h, v);
            }
        }
        _ => {}
    }
}

fn hash_lit(h: &mut impl Hasher, l: &IRLiteral) {
    match l {
        IRLiteral::Bool(v) => v.hash(h),
        IRLiteral::UInt8(v) => v.hash(h),
        IRLiteral::UInt16(v) => v.hash(h),
        IRLiteral::UInt32(v) => v.hash(h),
        IRLiteral::UInt64(v) => v.hash(h),
        IRLiteral::USize(v) => v.hash(h),
        IRLiteral::NatBig(v) => v.hash(h),
        IRLiteral::Float32(v) => v.to_bits().hash(h),
        IRLiteral::Float64(v) => v.to_bits().hash(h),
    }
}

fn hash_expr(h: &mut impl Hasher, e: &IRExpr) {
    std::mem::discriminant(e).hash(h);
    match e {
        IRExpr::Ctor { info, args } => {
            info.tag.hash(h);
            for a in args {
                hash_arg(h, a);
            }
        }
        IRExpr::Proj { idx, ty, arg } => {
            idx.hash(h);
            hash_type(h, ty);
            hash_arg(h, arg);
        }
        IRExpr::Tag(a) => hash_arg(h, a),
        IRExpr::Box { ty, arg } | IRExpr::Unbox { ty, arg } => {
            hash_type(h, ty);
            hash_arg(h, arg);
        }
        IRExpr::Lit(l) => hash_lit(h, l),
        IRExpr::Apply { fn_id, args } => {
            fn_id.0.hash(h);
            for a in args {
                hash_arg(h, a);
            }
        }
        IRExpr::PartialApply { fn_id, arity, args } => {
            fn_id.0.hash(h);
            arity.hash(h);
            for a in args {
                hash_arg(h, a);
            }
        }
        IRExpr::ClosureApply { closure, args } => {
            hash_arg(h, closure);
            for a in args {
                hash_arg(h, a);
            }
        }
        IRExpr::UProj { idx, var } => {
            idx.hash(h);
            var.0.hash(h);
        }
        IRExpr::SProj { n, offset, var, ty } => {
            n.hash(h);
            offset.hash(h);
            var.0.hash(h);
            hash_type(h, ty);
        }
        IRExpr::IsShared(v) | IRExpr::Reset(v) => v.0.hash(h),
        IRExpr::String(s) => s.hash(h),
        IRExpr::Reuse { var, ctor, args } => {
            var.0.hash(h);
            ctor.tag.hash(h);
            for a in args {
                hash_arg(h, a);
            }
        }
    }
}

fn hash_body(h: &mut impl Hasher, b: &IRBody) {
    std::mem::discriminant(b).hash(h);
    match b {
        IRBody::VDecl {
            var,
            ty,
            value,
            rest,
        } => {
            var.0.hash(h);
            hash_type(h, ty);
            hash_expr(h, value);
            hash_body(h, rest);
        }
        IRBody::JDecl {
            jp,
            params,
            body,
            rest,
        } => {
            jp.0.hash(h);
            for (v, t) in params {
                v.0.hash(h);
                hash_type(h, t);
            }
            hash_body(h, body);
            hash_body(h, rest);
        }
        IRBody::Inc { var, n, rest } => {
            var.0.hash(h);
            n.hash(h);
            hash_body(h, rest);
        }
        IRBody::Dec { var, rest } => {
            var.0.hash(h);
            hash_body(h, rest);
        }
        IRBody::Set {
            var,
            idx,
            value,
            rest,
        } => {
            var.0.hash(h);
            idx.hash(h);
            value.0.hash(h);
            hash_body(h, rest);
        }
        IRBody::SetTag { var, tag, rest } => {
            var.0.hash(h);
            tag.hash(h);
            hash_body(h, rest);
        }
        IRBody::USet {
            var,
            idx,
            value,
            rest,
        } => {
            var.0.hash(h);
            idx.hash(h);
            value.0.hash(h);
            hash_body(h, rest);
        }
        IRBody::SSet {
            var,
            n,
            offset,
            value,
            ty,
            rest,
        } => {
            var.0.hash(h);
            n.hash(h);
            offset.hash(h);
            value.0.hash(h);
            hash_type(h, ty);
            hash_body(h, rest);
        }
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => {
            scrutinee.0.hash(h);
            alts.len().hash(h);
            for a in alts {
                a.ctor.tag.hash(h);
                hash_body(h, &a.body);
            }
            default.is_some().hash(h);
            if let Some(d) = default {
                hash_body(h, d);
            }
        }
        IRBody::Jmp { jp, args } => {
            jp.0.hash(h);
            for a in args {
                hash_arg(h, a);
            }
        }
        IRBody::Ret(a) => hash_arg(h, a),
        IRBody::Unreachable => {}
    }
}

// ─── Collision detection ───────────────────────────────────────────────

fn collect_bindings(b: &IRBody, vars: &mut Vec<u32>, jps: &mut Vec<u32>) {
    match b {
        IRBody::VDecl { var, rest, .. } => {
            vars.push(var.0);
            collect_bindings(rest, vars, jps);
        }
        IRBody::JDecl {
            jp,
            params,
            body,
            rest,
        } => {
            jps.push(jp.0);
            for (v, _) in params {
                vars.push(v.0);
            }
            collect_bindings(body, vars, jps);
            collect_bindings(rest, vars, jps);
        }
        IRBody::Inc { rest, .. }
        | IRBody::Dec { rest, .. }
        | IRBody::Set { rest, .. }
        | IRBody::SetTag { rest, .. }
        | IRBody::USet { rest, .. }
        | IRBody::SSet { rest, .. } => collect_bindings(rest, vars, jps),
        IRBody::Case { alts, default, .. } => {
            for a in alts {
                collect_bindings(&a.body, vars, jps);
            }
            if let Some(d) = default {
                collect_bindings(d, vars, jps);
            }
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
    }
}

fn find_dups(ids: &[u32]) -> Vec<u32> {
    let mut seen = HashSet::new();
    let mut dups = HashSet::new();
    for &id in ids {
        if !seen.insert(id) {
            dups.insert(id);
        }
    }
    let mut v: Vec<u32> = dups.into_iter().collect();
    v.sort_unstable();
    v
}

// ─── Declaration name normalization ────────────────────────────────────

/// Normalize a declaration name for comparison: strip `_private.`/`_root_.`
/// prefixes, collapse consecutive dots, lowercase.
#[must_use]
pub(crate) fn normalize_decl_name(name: &str) -> String {
    let stripped = name
        .strip_prefix("_private.")
        .or_else(|| name.strip_prefix("_root_."))
        .unwrap_or(name);
    let mut result = String::with_capacity(stripped.len());
    let mut prev_dot = false;
    for ch in stripped.chars() {
        if ch == '.' {
            if !prev_dot && !result.is_empty() {
                result.push('.');
            }
            prev_dot = true;
        } else {
            prev_dot = false;
            for lc in ch.to_lowercase() {
                result.push(lc);
            }
        }
    }
    if result.ends_with('.') {
        result.pop();
    }
    result
}

/// Check if two declaration names are equivalent after normalization.
#[must_use]
pub(crate) fn decl_names_equivalent(a: &str, b: &str) -> bool {
    normalize_decl_name(a) == normalize_decl_name(b)
}

// ─── Public API ────────────────────────────────────────────────────────

/// Normalize with separate var/JP counters and statistics.
#[must_use]
pub(crate) fn normalize_ids_ext(decl: &IRDecl) -> (IRDecl, NormStats) {
    let mut s = ExtNormState::new();
    let params: Vec<_> = decl
        .params
        .iter()
        .map(|(v, ty)| (s.bind_var(*v), ty.clone()))
        .collect();
    let body = ext_norm_body(&mut s, &decl.body);
    (
        IRDecl {
            name: decl.name.clone(),
            params,
            return_type: decl.return_type.clone(),
            body,
        },
        s.stats,
    )
}

/// Compute canonical form (sequential IDs from 0).
#[must_use]
pub(crate) fn canonical_form(decl: &IRDecl) -> IRDecl {
    normalize_ids_ext(decl).0
}

/// Alpha equivalence: canonicalize both sides and compare structurally.
///
/// Two declarations are alpha-equivalent if they have the same structure
/// modulo renaming of `VarId` and `JoinPointId`. Names are NOT compared
/// (use [`decl_names_equivalent`] separately if needed).
#[must_use]
pub(crate) fn alpha_equiv(a: &IRDecl, b: &IRDecl) -> bool {
    let ca = canonical_form(a);
    let cb = canonical_form(b);
    // Compare via content hash (deterministic for canonical forms).
    content_hash(&ca) == content_hash(&cb)
        && format!("{:?}", ca.body) == format!("{:?}", cb.body)
        && ca.params.len() == cb.params.len()
        && ca
            .params
            .iter()
            .zip(cb.params.iter())
            .all(|((_, ta), (_, tb))| ta == tb)
        && ca.return_type == cb.return_type
}

/// Content-based hash for a (canonical) IR declaration.
#[must_use]
pub(crate) fn content_hash(decl: &IRDecl) -> u64 {
    let mut h = std::collections::hash_map::DefaultHasher::new();
    decl.params.len().hash(&mut h);
    for (v, ty) in &decl.params {
        v.0.hash(&mut h);
        hash_type(&mut h, ty);
    }
    hash_type(&mut h, &decl.return_type);
    hash_body(&mut h, &decl.body);
    h.finish()
}

/// Detect ID collisions (duplicate binding sites) in a declaration.
#[must_use]
pub(crate) fn detect_collisions(decl: &IRDecl) -> IdCollisions {
    let mut var_ids = Vec::new();
    let mut jp_ids = Vec::new();
    for (v, _) in &decl.params {
        var_ids.push(v.0);
    }
    collect_bindings(&decl.body, &mut var_ids, &mut jp_ids);
    IdCollisions {
        duplicate_vars: find_dups(&var_ids),
        duplicate_jps: find_dups(&jp_ids),
    }
}

/// Normalize and detect collisions in one pass.
#[must_use]
pub(crate) fn normalize_and_detect(decl: &IRDecl) -> (IRDecl, NormStats, IdCollisions) {
    let collisions = detect_collisions(decl);
    let (norm, mut stats) = normalize_ids_ext(decl);
    stats.collisions_found = collisions.total() as u32;
    (norm, stats, collisions)
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The per-member records a native-fold closure digest is made of
//! (`native_fold_authority.rs`).
//!
//! A member's RECORD is a pure function of its SNAPSHOT — the environment
//! entry's shallow clone (its expressions share their `Arc` children with the
//! environment, so a snapshot costs a few reference-count bumps). That is what
//! lets the authority cache survive environment growth: a closure is
//! re-validated by re-taking each member's snapshot and comparing it with the
//! memoized one, and `Expr` equality short-circuits on shared children
//! (`expr/kind.rs`, `ExprEqWalk`), so an unchanged member costs a pointer compare
//! rather than a re-hash. A member whose entry changed in any way is re-hashed.

use std::collections::{HashMap, HashSet};

use sha2::{Digest as _, Sha256};

use super::types::ConstantKind;
use super::Environment;
use crate::expr::{Expr, ExprKind, Literal};
use crate::level::Level;
use crate::name::Name;
use crate::quot::QuotKind;

/// Everything a member's record reads, cloned out of the environment.
#[derive(Clone, PartialEq)]
pub(super) enum Snapshot {
    Quot {
        kind: QuotKind,
        level_params: usize,
        ty: Expr,
    },
    Inductive {
        level_params: usize,
        params: u32,
        indices: u32,
        ty: Expr,
        all: Vec<Name>,
        ctors: Vec<Name>,
    },
    Constructor {
        inductive: Name,
        level_params: usize,
        params: u32,
        fields: u32,
        index: u32,
        ty: Expr,
    },
    Recursor {
        inductive: Name,
        arg_order: String,
        level_params: usize,
        counts: [u32; 4],
        is_k: bool,
        ty: Expr,
        rules: Vec<(Name, u32, Expr)>,
    },
    Constant {
        kind: ConstantKind,
        level_params: usize,
        ty: Expr,
        value: Option<Expr>,
    },
}

/// A member's memoized record: its snapshot, digest, the members its
/// computation reads, and whether it is an axiom.
#[derive(Clone)]
pub(super) struct MemberMemo {
    pub(super) snapshot: Snapshot,
    pub(super) spelled: String,
    pub(super) record: [u8; 32],
    pub(super) next: Vec<Name>,
    pub(super) axiom: bool,
}

/// Why a member has no record.
pub(super) enum MemberError {
    /// The environment does not hold the member.
    Absent,
    /// A value-less definition outside the inductive and quotient registries.
    NoValue,
    /// An expression form a canonical definition never contains.
    Unsupported,
}

impl Environment {
    /// The member's snapshot, taken in the registries' precedence (quotient,
    /// inductive, constructor, recursor, then the constant table: the
    /// inductive family is mirrored into the table as value-less entries).
    pub(super) fn fold_member_snapshot(&self, member: &Name) -> Result<Snapshot, MemberError> {
        if let Some(q) = self.get_quot(member) {
            return Ok(Snapshot::Quot {
                kind: q.kind,
                level_params: q.level_params.len(),
                ty: q.type_.clone(),
            });
        }
        if let Some(ind) = self.get_inductive(member) {
            return Ok(Snapshot::Inductive {
                level_params: ind.level_params.len(),
                params: ind.num_params,
                indices: ind.num_indices,
                ty: ind.type_.clone(),
                all: ind.all_names.clone(),
                ctors: ind.constructor_names.clone(),
            });
        }
        if let Some(ctor) = self.get_constructor(member) {
            return Ok(Snapshot::Constructor {
                inductive: ctor.inductive_name.clone(),
                level_params: ctor.level_params.len(),
                params: ctor.num_params,
                fields: ctor.num_fields,
                index: ctor.constructor_idx,
                ty: ctor.type_.clone(),
            });
        }
        if let Some(rec) = self.get_recursor(member) {
            return Ok(Snapshot::Recursor {
                inductive: rec.inductive_name.clone(),
                arg_order: format!("{:?}", rec.arg_order),
                level_params: rec.level_params.len(),
                counts: [
                    rec.num_params,
                    rec.num_indices,
                    rec.num_motives,
                    rec.num_minors,
                ],
                is_k: rec.is_k,
                ty: rec.type_.clone(),
                rules: rec
                    .rules
                    .iter()
                    .map(|r| (r.constructor_name.clone(), r.num_fields, r.rhs.clone()))
                    .collect(),
            });
        }
        let ci = self.get_const(member).ok_or(MemberError::Absent)?;
        if ci.kind == ConstantKind::Definition && ci.value.is_none() {
            return Err(MemberError::NoValue);
        }
        Ok(Snapshot::Constant {
            kind: ci.kind,
            level_params: ci.level_params.len(),
            ty: ci.type_.clone(),
            value: ci.value.clone(),
        })
    }
}

impl Snapshot {
    /// The member's record (a function of the snapshot alone).
    pub(super) fn memo(
        self,
        member: &Name,
        hasher: &mut ExprHasher,
    ) -> Result<MemberMemo, MemberError> {
        let mut next: Vec<Name> = Vec::new();
        let mut axiom = false;
        let mut h = Sha256::new();
        let mut digest = |e: &Expr| hasher.digest(e).map_err(|()| MemberError::Unsupported);
        match &self {
            Snapshot::Quot {
                kind,
                level_params,
                ty,
            } => {
                h.update(b"Q");
                h.update([*kind as u8]);
                put_u64(&mut h, *level_params as u64);
                h.update(digest(ty)?);
            }
            Snapshot::Inductive {
                level_params,
                params,
                indices,
                ty,
                all,
                ctors,
            } => {
                h.update(b"I");
                put_u64(&mut h, *level_params as u64);
                put_u64(&mut h, u64::from(*params));
                put_u64(&mut h, u64::from(*indices));
                h.update(digest(ty)?);
                for sibling in all {
                    put_str(&mut h, &sibling.to_string());
                    next.push(sibling.clone());
                }
                h.update(b"ctors");
                for ctor in ctors {
                    put_str(&mut h, &ctor.to_string());
                    next.push(ctor.clone());
                }
            }
            Snapshot::Constructor {
                inductive,
                level_params,
                params,
                fields,
                index,
                ty,
            } => {
                h.update(b"C");
                put_str(&mut h, &inductive.to_string());
                put_u64(&mut h, *level_params as u64);
                put_u64(&mut h, u64::from(*params));
                put_u64(&mut h, u64::from(*fields));
                put_u64(&mut h, u64::from(*index));
                h.update(digest(ty)?);
                next.push(inductive.clone());
            }
            Snapshot::Recursor {
                inductive,
                arg_order,
                level_params,
                counts,
                is_k,
                ty,
                rules,
            } => {
                h.update(b"R");
                put_str(&mut h, &inductive.to_string());
                put_str(&mut h, arg_order);
                put_u64(&mut h, *level_params as u64);
                for count in counts {
                    put_u64(&mut h, u64::from(*count));
                }
                h.update([u8::from(*is_k)]);
                h.update(digest(ty)?);
                for (ctor, fields, rhs) in rules {
                    put_str(&mut h, &ctor.to_string());
                    put_u64(&mut h, u64::from(*fields));
                    h.update(digest(rhs)?);
                }
                next.push(inductive.clone());
            }
            Snapshot::Constant {
                kind,
                level_params,
                ty,
                value,
            } => {
                put_u64(&mut h, *level_params as u64);
                match (kind, value) {
                    (ConstantKind::Definition, Some(value)) => {
                        h.update(b"D");
                        h.update(digest(ty)?);
                        h.update(digest(value)?);
                        let mut used = HashSet::new();
                        value.used_constants_dag(
                            crate::expr::UsedConstants::WithProjectionStructures,
                            &mut used,
                        );
                        let mut used: Vec<Name> = used.into_iter().collect();
                        used.sort_by_cached_key(Name::to_string);
                        next.extend(used);
                    }
                    (ConstantKind::Definition, None) => return Err(MemberError::NoValue),
                    (ConstantKind::Opaque, value) => {
                        h.update(b"O");
                        h.update(digest(ty)?);
                        if let Some(value) = value {
                            h.update(digest(value)?);
                        }
                    }
                    (ConstantKind::Axiom, _) => {
                        axiom = true;
                        h.update(b"A");
                        h.update(digest(ty)?);
                    }
                    (ConstantKind::Theorem, _) => h.update(b"T"),
                }
            }
        }
        Ok(MemberMemo {
            snapshot: self,
            spelled: member.to_string(),
            record: h.finalize().into(),
            next,
            axiom,
        })
    }
}

/// Structural equality up to binder annotations and `MData`.
pub(super) fn strip_binders_eq(a: &Expr, b: &Expr) -> bool {
    let mut hasher = ExprHasher::default();
    matches!((hasher.digest(a), hasher.digest(b)), (Ok(x), Ok(y)) if x == y)
}

pub(super) fn put_u64(h: &mut Sha256, v: u64) {
    h.update(v.to_le_bytes());
}

pub(super) fn put_str(h: &mut Sha256, s: &str) {
    put_u64(h, s.len() as u64);
    h.update(s.as_bytes());
}

fn level_digest(h: &mut Sha256, l: &Level) {
    match l {
        Level::Zero => h.update([0]),
        Level::Succ(x) => {
            h.update([1]);
            level_digest(h, x);
        }
        Level::Max(x, y) => {
            h.update([2]);
            level_digest(h, x);
            level_digest(h, y);
        }
        Level::IMax(x, y) => {
            h.update([3]);
            level_digest(h, x);
            level_digest(h, y);
        }
        Level::Param(n) => {
            h.update([4]);
            put_str(h, &n.to_string());
        }
    }
}

/// Merkle digests of expressions, memoized by node address: a node reached
/// through an `Arc` child keeps its address while the environment is borrowed
/// (the argument `used_constants_dag` makes), so a shared DAG costs its number
/// of distinct nodes. Explicit stack: no recursion-depth limit. One hasher
/// lives for one closure walk, never longer (addresses are only stable while
/// the environment is borrowed).
#[derive(Default)]
pub(super) struct ExprHasher {
    memo: HashMap<usize, [u8; 32]>,
}

impl ExprHasher {
    pub(super) fn digest(&mut self, root: &Expr) -> Result<[u8; 32], ()> {
        let mut stack: Vec<(&Expr, bool)> = vec![(root, false)];
        while let Some((e, expanded)) = stack.pop() {
            let key = std::ptr::from_ref(e) as usize;
            if self.memo.contains_key(&key) {
                continue;
            }
            let children = children_of(e)?;
            if !expanded {
                stack.push((e, true));
                for child in children.into_iter().rev() {
                    if !self
                        .memo
                        .contains_key(&(std::ptr::from_ref(child) as usize))
                    {
                        stack.push((child, false));
                    }
                }
                continue;
            }
            let d = self.node(e, &children);
            self.memo.insert(key, d);
        }
        // The ROOT may be a transient copy (a snapshot's own `Expr`, whose
        // address a later local can reuse), so its entry never outlives this
        // call; every other entry is an `Arc` child the borrowed environment
        // keeps alive for the whole walk.
        self.memo
            .remove(&(std::ptr::from_ref(root) as usize))
            .ok_or(())
    }

    fn child(&self, e: &Expr) -> [u8; 32] {
        self.memo
            .get(&(std::ptr::from_ref(e) as usize))
            .copied()
            .unwrap_or([0; 32])
    }

    fn node(&self, e: &Expr, children: &[&Expr]) -> [u8; 32] {
        let mut h = Sha256::new();
        match e.kind() {
            // Transparent to reduction: the node IS its child.
            ExprKind::MData(_, inner) => return self.child(inner),
            ExprKind::BVar(i) => {
                h.update([1]);
                put_u64(&mut h, u64::from(*i));
            }
            ExprKind::Sort(l) => {
                h.update([2]);
                level_digest(&mut h, l);
            }
            ExprKind::Const(n, levels) => {
                h.update([3]);
                put_str(&mut h, &n.to_string());
                put_u64(&mut h, levels.len() as u64);
                for l in levels.iter() {
                    level_digest(&mut h, l);
                }
            }
            ExprKind::App(..) => h.update([4]),
            ExprKind::Lam(..) => h.update([5]),
            ExprKind::Pi(..) => h.update([6]),
            ExprKind::Let(..) => h.update([7]),
            ExprKind::Lit(Literal::Nat(n)) => {
                h.update([8]);
                let limbs = n.limbs();
                let len = limbs.iter().rposition(|l| *l != 0).map_or(0, |i| i + 1);
                put_u64(&mut h, len as u64);
                for limb in &limbs[..len] {
                    put_u64(&mut h, *limb);
                }
            }
            ExprKind::Lit(Literal::String(s)) => {
                h.update([9]);
                put_str(&mut h, s);
            }
            ExprKind::Proj(s, i, _) => {
                h.update([10]);
                put_str(&mut h, &s.to_string());
                put_u64(&mut h, u64::from(*i));
            }
            // `children_of` refused every other form before this runs.
            _ => h.update([0xff]),
        }
        for child in children {
            h.update(self.child(child));
        }
        h.finalize().into()
    }
}

/// The digested children of a node, or `Err` for a form a canonical definition
/// never contains.
fn children_of(e: &Expr) -> Result<Vec<&Expr>, ()> {
    Ok(match e.kind() {
        ExprKind::BVar(_) | ExprKind::Sort(_) | ExprKind::Const(..) | ExprKind::Lit(_) => vec![],
        ExprKind::App(f, a) => vec![f.as_ref(), a.as_ref()],
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => vec![ty.as_ref(), body.as_ref()],
        ExprKind::Let(_, ty, val, body, _) => vec![ty.as_ref(), val.as_ref(), body.as_ref()],
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => vec![inner.as_ref()],
        _ => return Err(()),
    })
}

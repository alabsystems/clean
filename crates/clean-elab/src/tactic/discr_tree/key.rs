// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use std::cmp::Ordering;

use clean_kernel::{BigNat, FVarId, Literal, Name};

/// Shared discrimination-tree keys following Lean 4's core shape.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum DiscrKey {
    Star,
    Other,
    Lit(Literal),
    FVar(FVarId, usize),
    Const(Name, usize),
    Arrow,
    Proj(Name, u32, usize),
}

/// Indexing mode for path construction.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) enum IndexMode {
    #[default]
    Normal,
    NoIndexAtArgs,
}

/// A query result plus the number of extra arguments ignored by prefix matching.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Match<T> {
    pub(crate) value: T,
    pub(crate) extra_args: usize,
}

pub(crate) fn cmp_keys(lhs: &DiscrKey, rhs: &DiscrKey) -> Ordering {
    match (lhs, rhs) {
        (DiscrKey::Lit(lhs), DiscrKey::Lit(rhs)) => cmp_literals(lhs, rhs),
        (DiscrKey::FVar(lhs_id, lhs_arity), DiscrKey::FVar(rhs_id, rhs_arity)) => lhs_id
            .as_u64()
            .cmp(&rhs_id.as_u64())
            .then(lhs_arity.cmp(rhs_arity)),
        (DiscrKey::Const(lhs_name, lhs_arity), DiscrKey::Const(rhs_name, rhs_arity)) => {
            lhs_name.cmp(rhs_name).then(lhs_arity.cmp(rhs_arity))
        }
        (
            DiscrKey::Proj(lhs_name, lhs_idx, lhs_arity),
            DiscrKey::Proj(rhs_name, rhs_idx, rhs_arity),
        ) => lhs_name
            .cmp(rhs_name)
            .then(lhs_idx.cmp(rhs_idx))
            .then(lhs_arity.cmp(rhs_arity)),
        _ => key_rank(lhs).cmp(&key_rank(rhs)),
    }
}

fn key_rank(key: &DiscrKey) -> u8 {
    match key {
        DiscrKey::Star => 0,
        DiscrKey::Other => 1,
        DiscrKey::Lit(_) => 2,
        DiscrKey::FVar(_, _) => 3,
        DiscrKey::Const(_, _) => 4,
        DiscrKey::Arrow => 5,
        DiscrKey::Proj(_, _, _) => 6,
    }
}

fn cmp_literals(lhs: &Literal, rhs: &Literal) -> Ordering {
    match (lhs, rhs) {
        (Literal::Nat(lhs), Literal::Nat(rhs)) => cmp_big_nat(lhs, rhs),
        (Literal::String(lhs), Literal::String(rhs)) => lhs.cmp(rhs),
        (Literal::Nat(_), Literal::String(_)) => Ordering::Less,
        (Literal::String(_), Literal::Nat(_)) => Ordering::Greater,
    }
}

fn cmp_big_nat(lhs: &BigNat, rhs: &BigNat) -> Ordering {
    let lhs_limbs = lhs.limbs();
    let rhs_limbs = rhs.limbs();
    lhs_limbs
        .len()
        .cmp(&rhs_limbs.len())
        .then_with(|| lhs_limbs.iter().rev().cmp(rhs_limbs.iter().rev()))
}

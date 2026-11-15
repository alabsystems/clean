// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A small, owned sort representation used by the independent evaluator.

use carcara::ast::Sort;

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum S {
    Bool,
    Int,
    Real,
    Str,
    RegLan,
    Bv(usize),
    /// An uninterpreted sort (with its printed arguments).
    Atom(String),
    Array(Box<S>, Box<S>),
    /// Argument sorts and return sort.
    Fun(Vec<S>, Box<S>),
    /// A non-parametric datatype, by name. Its constructors are in the model's
    /// [`crate::datatypes::DtTable`].
    Dt(String),
    /// Anything the evaluator does not model (parametric datatypes, sets, sort variables, ...).
    Other(String),
}

impl S {
    pub fn from_sort(sort: &Sort) -> S {
        match sort {
            Sort::Bool => S::Bool,
            Sort::Int => S::Int,
            Sort::Real => S::Real,
            Sort::String => S::Str,
            Sort::RegLan => S::RegLan,
            Sort::BitVec(w) => S::Bv(*w),
            Sort::Atom(name, args) if args.is_empty() => S::Atom(name.to_string()),
            // In full: `Display` abridges a large sort, and this text names the sort.
            Sort::Atom(..) => S::Atom(sort.unabridged().to_string()),
            Sort::Array(i, e) => S::Array(Box::new(S::from_sort(i)), Box::new(S::from_sort(e))),
            Sort::Datatype { name, args } if args.is_empty() => S::Dt(name.to_string()),
            Sort::Function(sorts) => {
                let (ret, args) = sorts.split_last().expect("function sort has a return sort");
                S::Fun(
                    args.iter().map(|s| S::from_sort(s)).collect(),
                    Box::new(S::from_sort(ret)),
                )
            }
            other => S::Other(other.unabridged().to_string()),
        }
    }

    /// Is the carrier of this sort finite *in every model*? Uninterpreted sorts are finite in
    /// the models this battery builds (three elements), which is a legitimate model choice.
    pub fn is_finite(&self) -> bool {
        match self {
            S::Bool | S::Bv(_) | S::Atom(_) => true,
            S::Array(i, e) => i.is_finite() && e.is_finite(),
            S::Fun(args, ret) => args.iter().all(S::is_finite) && ret.is_finite(),
            _ => false,
        }
    }

    pub fn is_arith(&self) -> bool {
        matches!(self, S::Int | S::Real)
    }
}

pub const ATOM_CARD: u32 = 3;

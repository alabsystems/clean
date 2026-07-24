// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Native reducers for Lean 4 `Name` operations.

use crate::env::Environment;
use crate::expr::{Expr, ExprKind, Literal};
use crate::name::{Name, NameInner};
use std::sync::LazyLock;

pub(crate) mod names {
    use crate::name::Name;
    use std::sync::LazyLock;

    pub(crate) static LEAN_NAME_ANONYMOUS: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("Lean.Name.anonymous"));
    pub(crate) static LEAN_NAME_STR: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("Lean.Name.str"));
    pub(crate) static LEAN_NAME_NUM: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("Lean.Name.num"));
    pub(crate) static LEAN_NAME_MK_STR: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("Lean.Name.mkStr"));
    pub(crate) static LEAN_NAME_MK_NUM: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("Lean.Name.mkNum"));
    pub(crate) static LEAN_NAME_BEQ: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("Lean.Name.beq"));
    pub(crate) static LEAN_NAME_HASH: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("Lean.Name.hash"));
    pub(crate) static LEAN_NAME_TO_STRING: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("Lean.Name.toString"));
    pub(crate) static LEAN_NAME_APPEND: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("Lean.Name.append"));
}

pub(crate) fn get_string_val(e: &Expr) -> Option<&str> {
    match e.kind() {
        ExprKind::Lit(Literal::String(s)) => Some(s),
        _ => None,
    }
}

pub(crate) fn get_nat_val(e: &Expr) -> Option<u64> {
    match e.kind() {
        ExprKind::Lit(Literal::Nat(n)) => n.to_u64(),
        _ => None,
    }
}

pub(crate) fn get_name_val(e: &Expr) -> Option<Name> {
    let head = e.get_app_fn();
    let args = e.get_app_args();
    let ExprKind::Const(name, _) = head.kind() else {
        return None;
    };
    if *name == *names::LEAN_NAME_ANONYMOUS && args.is_empty() {
        Some(Name::anon())
    } else if *name == *names::LEAN_NAME_STR && args.len() == 2 {
        Some(get_name_val(args[0])?.str(get_string_val(args[1])?))
    } else if *name == *names::LEAN_NAME_NUM && args.len() == 2 {
        Some(get_name_val(args[0])?.num(get_nat_val(args[1])?))
    } else {
        None
    }
}

pub(crate) fn mk_name_expr(name: &Name) -> Expr {
    match name.inner() {
        NameInner::Anon => Expr::const_(names::LEAN_NAME_ANONYMOUS.clone(), vec![]),
        NameInner::Str(parent, s) => {
            let parent: &Name = parent;
            Expr::apps(
                Expr::const_(names::LEAN_NAME_STR.clone(), vec![]),
                [mk_name_expr(parent), Expr::str_lit(&**s)],
            )
        }
        NameInner::Num(parent, n) => {
            let parent: &Name = parent;
            Expr::apps(
                Expr::const_(names::LEAN_NAME_NUM.clone(), vec![]),
                [mk_name_expr(parent), Expr::nat_lit(*n)],
            )
        }
    }
}

pub(crate) fn get_bool_val(e: &Expr) -> Option<bool> {
    static BOOL_TRUE: LazyLock<Name> = LazyLock::new(|| Name::from_string("Bool.true"));
    static BOOL_FALSE: LazyLock<Name> = LazyLock::new(|| Name::from_string("Bool.false"));
    match e.get_app_fn().kind() {
        ExprKind::Const(name, _) if *name == *BOOL_TRUE => Some(true),
        ExprKind::Const(name, _) if *name == *BOOL_FALSE => Some(false),
        _ => None,
    }
}

pub(crate) fn mk_bool_expr(b: bool) -> Expr {
    static BOOL_TRUE: LazyLock<Name> = LazyLock::new(|| Name::from_string("Bool.true"));
    static BOOL_FALSE: LazyLock<Name> = LazyLock::new(|| Name::from_string("Bool.false"));
    Expr::const_(
        if b {
            BOOL_TRUE.clone()
        } else {
            BOOL_FALSE.clone()
        },
        vec![],
    )
}

enum NamePart {
    Str(String),
    Num(u64),
}

fn collect_name_parts(name: &Name) -> Vec<NamePart> {
    let mut parts = Vec::new();
    let mut current = name;
    loop {
        match current.inner() {
            NameInner::Anon => break,
            NameInner::Str(parent, s) => {
                parts.push(NamePart::Str(s.to_string()));
                let parent: &Name = parent;
                current = parent;
            }
            NameInner::Num(parent, n) => {
                parts.push(NamePart::Num(*n));
                let parent: &Name = parent;
                current = parent;
            }
        }
    }
    parts.reverse();
    parts
}

/// Get the Lean 4-compatible hash value for a Name.
///
/// Uses the cached hash computed at Name construction time via
/// Lean 4's `mixHash`-based algorithm (MurmurHash2-64A mixing).
pub(crate) fn lean4_name_hash(name: &Name) -> u64 {
    name.lean4_hash()
}

pub(crate) fn reduce_name_mk_str(args: &[&Expr]) -> Option<Expr> {
    Some(mk_name_expr(
        &get_name_val(args.first().copied()?)?.str(get_string_val(args.get(1)?)?),
    ))
}

pub(crate) fn reduce_name_mk_num(args: &[&Expr]) -> Option<Expr> {
    Some(mk_name_expr(
        &get_name_val(args.first().copied()?)?.num(get_nat_val(args.get(1)?)?),
    ))
}

pub(crate) fn reduce_name_beq(args: &[&Expr]) -> Option<Expr> {
    Some(mk_bool_expr(
        get_name_val(args.first().copied()?)? == get_name_val(args.get(1)?)?,
    ))
}

pub(crate) fn reduce_name_hash(args: &[&Expr]) -> Option<Expr> {
    Some(Expr::nat_lit(lean4_name_hash(&get_name_val(
        args.first().copied()?,
    )?)))
}

pub(crate) fn reduce_name_to_string(args: &[&Expr]) -> Option<Expr> {
    let name = get_name_val(args.first().copied()?)?;
    let sep = if get_bool_val(args.get(1)?)? { "." } else { "" };
    let s = if name.is_anon() {
        "[anonymous]".to_string()
    } else {
        collect_name_parts(&name)
            .into_iter()
            .map(|p| match p {
                NamePart::Str(s) => s,
                NamePart::Num(n) => n.to_string(),
            })
            .collect::<Vec<_>>()
            .join(sep)
    };
    Some(Expr::str_lit(&s))
}

pub(crate) fn reduce_name_append(args: &[&Expr]) -> Option<Expr> {
    let mut name = get_name_val(args.first().copied()?)?;
    for part in collect_name_parts(&get_name_val(args.get(1)?)?) {
        name = match part {
            NamePart::Str(s) => name.str(s),
            NamePart::Num(n) => name.num(n),
        };
    }
    Some(mk_name_expr(&name))
}

impl Environment {
    pub(crate) fn init_name_native_reducers(&mut self) {
        self.register_native_reducer(names::LEAN_NAME_MK_STR.clone(), reduce_name_mk_str);
        self.register_native_reducer(names::LEAN_NAME_MK_NUM.clone(), reduce_name_mk_num);
        self.register_native_reducer(names::LEAN_NAME_BEQ.clone(), reduce_name_beq);
        self.register_native_reducer(names::LEAN_NAME_HASH.clone(), reduce_name_hash);
        self.register_native_reducer(names::LEAN_NAME_TO_STRING.clone(), reduce_name_to_string);
        self.register_native_reducer(names::LEAN_NAME_APPEND.clone(), reduce_name_append);
    }
}

#[cfg(test)]
#[path = "native_reducers_name_tests.rs"]
mod tests;

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Encoding helpers for Metamath assertion and proof metadata.

use super::ast::Formula;
use super::translate::{ProofNode, Substitution};
use clean_kernel::{Expr, Name};

pub(super) fn decl_name(label: &str) -> Name {
    Name::interned(&format!("Metamath.{label}"))
}

pub(super) fn encode_assertion(
    kind: &str,
    label: &str,
    formula: &Formula,
    mandatory: &[String],
    essentials: &[String],
    disjoints: &[(String, String)],
) -> Expr {
    Expr::apps(
        mm_const("Metamath.Assertion.mk"),
        [
            Expr::str_lit(kind),
            Expr::str_lit(label),
            Expr::str_lit(&formula.typecode),
            encode_string_list(&formula.tokens),
            encode_string_list(mandatory),
            encode_string_list(essentials),
            encode_pair_list(disjoints),
        ],
    )
}

pub(super) fn encode_proof(node: &ProofNode) -> Expr {
    match node {
        ProofNode::Hyp { label, formula } => Expr::apps(
            mm_const("Metamath.Proof.hyp"),
            [
                Expr::str_lit(label),
                Expr::str_lit(&formula.typecode),
                encode_string_list(&formula.tokens),
            ],
        ),
        ProofNode::Apply {
            label,
            args,
            substitutions,
            result,
        } => Expr::apps(
            mm_const("Metamath.Proof.apply"),
            [
                Expr::str_lit(label),
                encode_expr_list(args.iter().map(encode_proof)),
                encode_expr_list(substitutions.iter().map(encode_substitution)),
                Expr::str_lit(&result.typecode),
                encode_string_list(&result.tokens),
            ],
        ),
    }
}

fn encode_substitution(binding: &Substitution) -> Expr {
    Expr::apps(
        mm_const("Metamath.Substitution.mk"),
        [
            Expr::str_lit(&binding.variable),
            Expr::str_lit(&binding.typecode),
            Expr::str_lit(&binding.formula.typecode),
            encode_string_list(&binding.formula.tokens),
        ],
    )
}

fn encode_string_list(items: &[String]) -> Expr {
    encode_expr_list(items.iter().map(Expr::str_lit))
}

fn encode_pair_list(pairs: &[(String, String)]) -> Expr {
    encode_expr_list(pairs.iter().map(|(left, right)| {
        Expr::apps(
            mm_const("Metamath.Pair.mk"),
            [Expr::str_lit(left), Expr::str_lit(right)],
        )
    }))
}

fn encode_expr_list(items: impl IntoIterator<Item = Expr>) -> Expr {
    let mut list = mm_const("Metamath.List.nil");
    let mut items: Vec<Expr> = items.into_iter().collect();
    while let Some(item) = items.pop() {
        list = Expr::apps(mm_const("Metamath.List.cons"), [item, list]);
    }
    list
}

fn mm_const(name: &str) -> Expr {
    Expr::const_(Name::interned(name), vec![])
}

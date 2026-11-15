// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unit pins for the imported zero-argument tactic-macro decoder, over terms
//! shaped exactly like the pinned v4.30.0-rc2 elaboration of
//! `macro "compareOfLessAndEq_rfl" : tactic => `(tactic| …)`.

use super::*;

fn s(v: &str) -> Expr {
    Expr::str_lit(v)
}
fn c(n: &str) -> Expr {
    Expr::const_(Name::from_string(n), vec![])
}
fn name1(a: &str) -> Expr {
    Expr::app(c("Lean.Name.mkStr1"), s(a))
}
fn name4(a: &str, b: &str, cc: &str, d: &str) -> Expr {
    Expr::apps(c("Lean.Name.mkStr4"), [s(a), s(b), s(cc), s(d)])
}
fn info() -> Expr {
    Expr::bvar(0)
}
fn atom(v: &str) -> Expr {
    Expr::apps(c("Lean.Syntax.atom"), [info(), s(v)])
}
fn node(n: usize, kind: Expr, children: Vec<Expr>) -> Expr {
    assert_eq!(children.len(), n);
    let mut args = vec![info(), kind];
    args.extend(children);
    Expr::apps(c(&format!("Lean.Syntax.node{n}")), args)
}
fn null_node(children: Vec<Expr>) -> Expr {
    let n = children.len();
    if n == 0 {
        // What the pinned elaboration emits for an absent optional:
        // `Lean.Syntax.node info `null (Array.mkArray0 Lean.Syntax)`.
        return Expr::apps(
            c("Lean.Syntax.node"),
            [
                info(),
                name1("null"),
                Expr::app(c("Array.mkArray0"), c("Lean.Syntax")),
            ],
        );
    }
    node(n, name1("null"), children)
}
/// An identifier the quotation pre-resolved to the declaration `decl`.
fn preresolved_ident(v: &str, decl: Expr) -> Expr {
    let val = Expr::apps(
        c("Lean.addMacroScope"),
        [Expr::bvar(1), name1(v), Expr::bvar(2)],
    );
    let pre = Expr::apps(c("Lean.Syntax.Preresolved.decl"), [decl, c("List.nil")]);
    let list = Expr::apps(
        c("List.cons"),
        [c("Lean.Syntax.Preresolved"), pre, c("List.nil")],
    );
    Expr::apps(c("Lean.Syntax.ident"), [info(), s("raw"), val, list])
}
fn scoped_ident(v: &str) -> Expr {
    let val = Expr::apps(
        c("Lean.addMacroScope"),
        [Expr::bvar(1), name1(v), Expr::bvar(2)],
    );
    Expr::apps(
        c("Lean.Syntax.ident"),
        [info(), s("raw"), val, c("List.nil")],
    )
}

#[test]
fn test_tactic_kind_name_capitalizes_the_atom() {
    assert_eq!(
        tactic_kind_name("compareOfLessAndEq_rfl").as_deref(),
        Some("tacticCompareOfLessAndEq_rfl")
    );
    assert_eq!(tactic_kind_name("  ").as_deref(), None);
}

#[test]
fn test_parser_descr_single_atom_reads_the_symbol_and_refuses_sequences() {
    let single = Expr::apps(
        c("Lean.ParserDescr.node"),
        [
            name1("tacticFoo"),
            Expr::nat_lit(1024),
            Expr::apps(
                c("Lean.ParserDescr.nonReservedSymbol"),
                [s("foo"), c("Bool.false")],
            ),
        ],
    );
    assert_eq!(parser_descr_single_atom(&single).as_deref(), Some("foo"));
    let with_arg = Expr::apps(
        c("Lean.ParserDescr.node"),
        [
            name1("tacticFoo"),
            Expr::nat_lit(1024),
            Expr::apps(
                c("Lean.ParserDescr.binary"),
                [name1("andthen"), c("x"), c("y")],
            ),
        ],
    );
    assert_eq!(parser_descr_single_atom(&with_arg), None);
}

#[test]
fn test_render_joins_sequences_with_semicolons_and_glues_config_items() {
    // `(intro a b; simp +decide only)`
    let intro = node(
        2,
        name4("Lean", "Parser", "Tactic", "intro"),
        vec![
            atom("intro"),
            null_node(vec![scoped_ident("a"), scoped_ident("b")]),
        ],
    );
    let config = node(
        2,
        name4("Lean", "Parser", "Tactic", "posConfigItem"),
        // As elaborated: the option name `decide` is pre-resolved to the
        // declaration `Decidable.decide`, and must still render as `+decide`.
        vec![
            atom("+"),
            preresolved_ident(
                "decide",
                Expr::apps(c("Lean.Name.mkStr2"), [s("Decidable"), s("decide")]),
            ),
        ],
    );
    let simp = node(
        4,
        name4("Lean", "Parser", "Tactic", "simp"),
        vec![
            atom("simp"),
            config,
            null_node(vec![]),
            null_node(vec![atom("only")]),
        ],
    );
    // A newline separator is an EMPTY null node; it must still become `;`.
    let seq = node(
        1,
        name4("Lean", "Parser", "Tactic", "tacticSeq1Indented"),
        vec![null_node(vec![intro, null_node(vec![]), simp])],
    );
    let paren = node(
        3,
        name4("Lean", "Parser", "Tactic", "paren"),
        vec![atom("("), seq, atom(")")],
    );
    let mut out = Vec::new();
    assert!(render_syntax(&paren, &mut out));
    assert_eq!(out.join(" "), "( intro a b ; simp +decide only )");
}

#[test]
fn test_render_prefers_a_single_preresolved_declaration() {
    let pre = Expr::apps(
        c("List.cons"),
        [
            c("Lean.Syntax.Preresolved"),
            Expr::apps(
                c("Lean.Syntax.Preresolved.decl"),
                [
                    Expr::apps(c("Lean.Name.mkStr2"), [s("Ord"), s("compare")]),
                    c("List.nil"),
                ],
            ),
            c("List.nil"),
        ],
    );
    let ident = Expr::apps(
        c("Lean.Syntax.ident"),
        [info(), s("compare"), name1("compare"), pre],
    );
    let mut out = Vec::new();
    assert!(render_syntax(&ident, &mut out));
    assert_eq!(out, vec!["Ord.compare".to_string()]);
}

#[test]
fn test_render_refuses_an_antiquotation_hole() {
    // A macro WITH arguments splices the bound input syntax (a bound variable
    // here) into its quotation; the renderer must refuse, not drop it.
    let spliced = node(
        2,
        name4("Lean", "Parser", "Tactic", "exact"),
        vec![atom("exact"), Expr::bvar(3)],
    );
    let mut out = Vec::new();
    assert!(!render_syntax(&spliced, &mut out));
}

#[test]
fn test_find_is_of_kind_and_first_node_locate_the_rule_parts() {
    let test = Expr::apps(
        c("Lean.Syntax.isOfKind"),
        [Expr::bvar(0), name1("tacticFoo")],
    );
    let rhs = node(
        1,
        name4("Lean", "Parser", "Tactic", "tacticRfl"),
        vec![atom("rfl")],
    );
    let value = Expr::apps(
        c("ite"),
        [c("T"), test, c("inst"), rhs.clone(), Expr::bvar(0)],
    );
    assert_eq!(find_is_of_kind(&value).as_deref(), Some("tacticFoo"));
    let found = find_first_syntax_node(&value).expect("the quotation node");
    let mut out = Vec::new();
    assert!(render_syntax(found, &mut out));
    assert_eq!(out, vec!["rfl".to_string()]);
}

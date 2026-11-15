// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Imported ZERO-ARGUMENT tactic macros:
//! `macro "compareOfLessAndEq_rfl" : tactic => `(tactic| (intro a b; …))`.
//!
//! Lean compiles such a command into two constants of the declaring module
//! (ground truth on the pinned v4.30.0-rc2, `Mathlib.Order.Defs.LinearOrder`):
//!
//! ```text
//! tacticCompareOfLessAndEq_rfl : ParserDescr :=
//!   ParserDescr.node `tacticCompareOfLessAndEq_rfl 1024
//!     (ParserDescr.nonReservedSymbol "compareOfLessAndEq_rfl" false)
//! _aux_Mathlib_Order_Defs_LinearOrder___macroRules_tacticCompareOfLessAndEq_rfl_1 : Macro :=
//!   fun x => … if __discr.isOfKind `tacticCompareOfLessAndEq_rfl = true then
//!     … pure { raw := Syntax.node3 info `Lean.Parser.Tactic.paren (Syntax.atom info "(") … }
//! ```
//!
//! The syntax kind is `<category> ++ capitalize(atom)` (`mkNameFromParserSyntax`,
//! `Lean/Elab/Syntax.lean`). Clean cannot run a compiled `Macro`, and did not
//! decode the olean's parser/macro extensions, so the name reached the tactic
//! evaluator as an unknown tactic — measured 2026-09-11 as class (11):
//! `LinearOrder.compare_eq_compareOfLessAndEq := by compareOfLessAndEq_rfl` is
//! the `autoParam` of every `LinearOrder` instance that omits that field
//! (`LinearOrder.ofSubsingleton`, the `PUnit` instance).
//!
//! This module recovers the expansion from the macro's own VALUE: the quotation
//! the rule returns is an ordinary kernel term built from `Lean.Syntax.node1`
//! … `node8` / `Lean.Syntax.node` / `Lean.Syntax.atom` / `Lean.Syntax.ident`,
//! rendered to token text that the ordinary tactic grammar parses. Only a
//! parser descriptor that is exactly ONE atom qualifies (no arguments, so no
//! antiquotation to substitute), only a single rule for the kind is accepted,
//! and a syntax node the renderer does not model REFUSES the whole macro —
//! the tactic then stays unknown, exactly the pre-existing failure, never a
//! substitute script whose success could accept what Lean rejects.

use super::*;
use crate::tactic::ProofState;
use clean_kernel::expr::Literal;

/// An expansion decoded from an imported macro rule.
pub(crate) struct ImportedTacticMacro {
    /// The `macroRules` constant the script was read from (diagnostics).
    pub(crate) rule: Name,
    /// The expansion as token text for the tactic grammar.
    pub(crate) script: String,
}

impl ElabCtx<'_> {
    /// The imported zero-argument tactic macro spelled `atom`, if exactly one
    /// such macro rule exists and its expansion decodes.
    pub(crate) fn imported_tactic_macro(&self, atom: &str) -> Option<ImportedTacticMacro> {
        let kind_suffix = tactic_kind_name(atom)?;
        let marker = "___macroRules_";
        let mut found: Vec<ImportedTacticMacro> = Vec::new();
        let consider = |name: &Name, found: &mut Vec<ImportedTacticMacro>| {
            let text = name.to_string();
            if !text.contains(marker) || !text.contains(&kind_suffix) {
                return;
            }
            if let Some(m) = self.decode_zero_arg_tactic_macro(name, atom) {
                found.push(m);
            }
        };
        for ci in self.env.constants() {
            consider(&ci.name, &mut found);
        }
        for name in self.env.lazy_source_names() {
            consider(&name, &mut found);
        }
        if std::env::var_os("CLEAN_MACRO_TRACE").is_some() {
            eprintln!(
                "imported-tactic-macro `{atom}` (kind `{kind_suffix}`): {} decoded rule(s)",
                found.len()
            );
        }
        // Several rules for one kind are tried most-recent-first by Lean's
        // macro attribute; with no declaration order to consult here, more
        // than one is refused rather than picked.
        if found.len() == 1 {
            found.pop()
        } else {
            None
        }
    }

    /// Run a decoded expansion as the tactic sequence it spells.
    pub(crate) fn eval_imported_tactic_macro(
        &mut self,
        ps: &mut ProofState,
        name: &str,
        expansion: &ImportedTacticMacro,
    ) -> Result<(), ElabError> {
        let parsed =
            clean_parser::parse_expr(&format!("by {}", expansion.script)).map_err(|e| {
                ElabError::Unsupported {
                    feature: format!(
                        "imported tactic macro `{name}` (rule `{}`) expands to `{}`, \
                     which the tactic grammar did not parse: {e}",
                        expansion.rule, expansion.script
                    ),
                }
            })?;
        let SurfaceExpr::ByTactic(_, tactics) = parsed else {
            return Err(ElabError::Unsupported {
                feature: format!(
                    "imported tactic macro `{name}` expands to `{}`, which is not a tactic block",
                    expansion.script
                ),
            });
        };
        crate::tactic::TacticEval::eval_seq(self, ps, &tactics).map_err(ElabError::from)
    }

    fn decode_zero_arg_tactic_macro(&self, rule: &Name, atom: &str) -> Option<ImportedTacticMacro> {
        let trace = std::env::var_os("CLEAN_MACRO_TRACE").is_some();
        let refuse = |why: &str| {
            if trace {
                eprintln!("imported-tactic-macro candidate `{rule}` refused: {why}");
            }
            None
        };
        let Some(value) = self.env.get_const(rule).and_then(|ci| ci.value.clone()) else {
            return refuse("no value in the environment");
        };
        let Some(kind) = find_is_of_kind(&value) else {
            return refuse("no `Syntax.isOfKind` test in its value");
        };
        // The kind's parser descriptor must be exactly the one atom.
        let Some(descr) = self
            .env
            .get_const(&Name::from_string(&kind))
            .and_then(|ci| ci.value.clone())
        else {
            return refuse(&format!("kind `{kind}` has no parser descriptor value"));
        };
        match parser_descr_single_atom(&descr) {
            Some(a) if a.trim() == atom => {}
            other => {
                return refuse(&format!(
                    "descriptor is not the single atom `{atom}`: {other:?}"
                ))
            }
        }
        let Some(rhs) = find_first_syntax_node(&value) else {
            return refuse("no `Lean.Syntax.node*` quotation in its value");
        };
        let mut out = Vec::new();
        if !render_syntax(rhs, &mut out) || out.is_empty() {
            return refuse(&format!("quotation did not render (partial: {out:?})"));
        }
        Some(ImportedTacticMacro {
            rule: rule.clone(),
            script: out.join(" "),
        })
    }
}

/// `tactic ++ capitalize(atom)` with whitespace turned into `_`, the syntax
/// kind Lean mints for `macro "atom" : tactic` (`mkNameFromParserSyntax`).
fn tactic_kind_name(atom: &str) -> Option<String> {
    let trimmed: String = atom
        .trim()
        .chars()
        .map(|c| if c.is_whitespace() { '_' } else { c })
        .collect();
    let mut chars = trimmed.chars();
    let first = chars.next()?;
    Some(format!("tactic{}{}", first.to_uppercase(), chars.as_str()))
}

/// The kind named by the rule's `Syntax.isOfKind __discr `kind` test.
fn find_is_of_kind(e: &Expr) -> Option<String> {
    let mut result = None;
    visit_apps(e, &mut |head, args| {
        if result.is_none() && head == "Lean.Syntax.isOfKind" && args.len() == 2 {
            let mut parts = Vec::new();
            if name_components(args[1], &mut parts) {
                result = Some(parts.join("."));
            }
        }
    });
    result
}

/// `ParserDescr.node kind prec (ParserDescr.nonReservedSymbol "atom" _)` or
/// `… (ParserDescr.symbol "atom")` → the atom. Anything else (arguments,
/// sequences, categories) is `None`.
fn parser_descr_single_atom(e: &Expr) -> Option<String> {
    let (head, args) = const_app(e)?;
    if head != "Lean.ParserDescr.node" || args.len() != 3 {
        return None;
    }
    let (inner, inner_args) = const_app(args[2])?;
    let lit = match inner.as_str() {
        "Lean.ParserDescr.nonReservedSymbol" if inner_args.len() == 2 => inner_args[0],
        "Lean.ParserDescr.symbol" if inner_args.len() == 1 => inner_args[0],
        _ => return None,
    };
    match lit.kind() {
        ExprKind::Lit(Literal::String(s)) => Some(s.to_string()),
        _ => None,
    }
}

/// The outermost `Lean.Syntax.node*` application, in pre-order: the
/// quotation the rule returns (the rule's other syntax values are the input
/// it inspects, which is never rebuilt with a node constructor).
fn find_first_syntax_node(e: &Expr) -> Option<&Expr> {
    if let Some((head, _)) = const_app(e) {
        if is_node_ctor(&head) {
            return Some(e);
        }
    }
    match e.kind() {
        ExprKind::App(f, a) => find_first_syntax_node(f).or_else(|| find_first_syntax_node(a)),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            find_first_syntax_node(ty).or_else(|| find_first_syntax_node(body))
        }
        ExprKind::Let(_, ty, val, body, _) => find_first_syntax_node(ty)
            .or_else(|| find_first_syntax_node(val))
            .or_else(|| find_first_syntax_node(body)),
        ExprKind::MData(_, inner) => find_first_syntax_node(inner),
        ExprKind::Proj(_, _, inner) => find_first_syntax_node(inner),
        _ => None,
    }
}

fn is_node_ctor(head: &str) -> bool {
    matches!(
        head,
        "Lean.Syntax.node"
            | "Lean.Syntax.node1"
            | "Lean.Syntax.node2"
            | "Lean.Syntax.node3"
            | "Lean.Syntax.node4"
            | "Lean.Syntax.node5"
            | "Lean.Syntax.node6"
            | "Lean.Syntax.node7"
            | "Lean.Syntax.node8"
    )
}

/// Render a syntax tree to tokens in source order. `false` on any shape the
/// renderer does not model.
fn render_syntax(e: &Expr, out: &mut Vec<String>) -> bool {
    let Some((head, args)) = const_app(e) else {
        return false;
    };
    match head.as_str() {
        "Lean.Syntax.atom" if args.len() == 2 => push_string_lit(args[1], out),
        "Lean.Syntax.ident" if args.len() == 4 => render_ident(args[2], args[3], out),
        "Lean.Syntax.missing" if args.is_empty() => true,
        h if is_node_ctor(h) && args.len() >= 2 => {
            let mut kind_parts = Vec::new();
            if !name_components(args[1], &mut kind_parts) {
                return false;
            }
            let kind = kind_parts.join(".");
            let mut children: Vec<&Expr> = Vec::new();
            if h == "Lean.Syntax.node" {
                if args.len() != 3 || !array_elems(args[2], &mut children) {
                    return false;
                }
            } else {
                let arity = h
                    .trim_start_matches("Lean.Syntax.node")
                    .parse::<usize>()
                    .unwrap_or(usize::MAX);
                if args.len() != arity + 2 {
                    return false;
                }
                children.extend(args[2..].iter().copied());
            }
            render_node(&kind, &children, out)
        }
        _ => false,
    }
}

fn render_node(kind: &str, children: &[&Expr], out: &mut Vec<String>) -> bool {
    match kind {
        // `+decide` / `-zeta`: the option name is glued to its sign — and it is
        // an OPTION name, so its own spelling is rendered, never the
        // declaration the quotation pre-resolved that spelling to (measured on
        // the pinned elaboration of Mathlib's `compareOfLessAndEq_rfl`:
        // `+decide` carries `Preresolved.decl `Decidable.decide`).
        "Lean.Parser.Tactic.posConfigItem" | "Lean.Parser.Tactic.negConfigItem" => {
            let mut parts = Vec::new();
            let rendered = children.iter().all(|c| match const_app(c) {
                Some((head, args)) if head == "Lean.Syntax.ident" && args.len() == 4 => {
                    render_ident_spelling(args[2], &mut parts)
                }
                _ => render_syntax(c, &mut parts),
            });
            if !rendered {
                return false;
            }
            out.push(parts.concat());
            true
        }
        // `sepByIndentSemicolon`: the separators alternate with the tactics and
        // are either a `;` atom or an empty node (a newline); both become `;`.
        "Lean.Parser.Tactic.tacticSeq1Indented" if children.len() == 1 => {
            let mut items = Vec::new();
            if !null_node_children(children[0], &mut items) {
                return false;
            }
            for (i, item) in items.iter().enumerate() {
                if i % 2 == 1 {
                    out.push(";".to_string());
                } else if !render_syntax(item, out) {
                    return false;
                }
            }
            true
        }
        _ => children.iter().all(|c| render_syntax(c, out)),
    }
}

/// The children of a `null`-kind node (`Syntax.node info `null #[…]` or
/// `Syntax.nodeN info `null …`).
fn null_node_children<'e>(e: &'e Expr, items: &mut Vec<&'e Expr>) -> bool {
    let Some((head, args)) = const_app(e) else {
        return false;
    };
    if !is_node_ctor(&head) || args.len() < 2 {
        return false;
    }
    let mut kind_parts = Vec::new();
    if !name_components(args[1], &mut kind_parts) || kind_parts != ["null"] {
        return false;
    }
    if head == "Lean.Syntax.node" {
        args.len() == 3 && array_elems(args[2], items)
    } else {
        items.extend(args[2..].iter().copied());
        true
    }
}

/// `Syntax.ident info raw val preresolved`: a single preresolved declaration
/// is the name the quotation MEANT (`compare` ↦ `Ord.compare`), so it is
/// rendered instead of the raw spelling; otherwise the identifier's own name
/// with its macro scopes dropped (`addMacroScope quotCtx `a scp` ↦ `a`).
fn render_ident(val: &Expr, preresolved: &Expr, out: &mut Vec<String>) -> bool {
    let mut resolved = Vec::new();
    if list_elems(preresolved, &mut resolved) && resolved.len() == 1 {
        if let Some((head, args)) = const_app(resolved[0]) {
            if head == "Lean.Syntax.Preresolved.decl" && args.len() == 2 {
                let mut parts = Vec::new();
                if name_components(args[0], &mut parts) {
                    out.push(parts.join("."));
                    return true;
                }
            }
        }
    }
    render_ident_spelling(val, out)
}

/// An identifier's own name with its macro scopes dropped
/// (`addMacroScope quotCtx `a scp` ↦ `a`).
fn render_ident_spelling(val: &Expr, out: &mut Vec<String>) -> bool {
    let name = match const_app(val) {
        Some((head, args)) if head == "Lean.addMacroScope" && args.len() == 3 => args[1],
        _ => val,
    };
    let mut parts = Vec::new();
    if !name_components(name, &mut parts) {
        return false;
    }
    out.push(parts.join("."));
    true
}

fn push_string_lit(e: &Expr, out: &mut Vec<String>) -> bool {
    match e.kind() {
        ExprKind::Lit(Literal::String(s)) => {
            out.push(s.to_string());
            true
        }
        _ => false,
    }
}

/// Elements of an `Array` literal: `Array.mkArray0` … `mkArray8` (what a
/// compiled quotation emits — an absent optional is
/// `Syntax.node info `null (Array.mkArray0 Syntax)`, measured on the pinned
/// v4.30.0-rc2 `Mathlib/Order/Defs/LinearOrder.olean`), `List.toArray`/
/// `Array.mk` over a list, `Array.push` chains, `Array.empty`/`Array.mkEmpty`.
fn array_elems<'e>(e: &'e Expr, items: &mut Vec<&'e Expr>) -> bool {
    let Some((head, args)) = const_app(e) else {
        return false;
    };
    if let Some(arity) = head
        .strip_prefix("Array.mkArray")
        .and_then(|n| n.parse::<usize>().ok())
    {
        // `Array.mkArrayN {α} a₁ … a_N`.
        if arity > 8 || args.len() != arity + 1 {
            return false;
        }
        items.extend(args[1..].iter().copied());
        return true;
    }
    match head.as_str() {
        "Array.push" if args.len() == 3 => {
            array_elems(args[1], items) && {
                items.push(args[2]);
                true
            }
        }
        "Array.empty" | "Array.mkEmpty" | "Array.emptyWithCapacity" => true,
        "List.toArray" | "Array.mk" if args.len() == 2 => list_elems(args[1], items),
        _ => false,
    }
}

fn list_elems<'e>(e: &'e Expr, items: &mut Vec<&'e Expr>) -> bool {
    let Some((head, args)) = const_app(e) else {
        return false;
    };
    match head.as_str() {
        "List.nil" => true,
        "List.cons" if args.len() == 3 => {
            items.push(args[1]);
            list_elems(args[2], items)
        }
        _ => false,
    }
}

/// A `Lean.Name` literal: `Name.anonymous`, `Name.str`/`mkStr`,
/// `Name.mkStr1` … `mkStr8`, `Name.num`/`mkNum`.
fn name_components(e: &Expr, parts: &mut Vec<String>) -> bool {
    let Some((head, args)) = const_app(e) else {
        return false;
    };
    let string = |a: &Expr| match a.kind() {
        ExprKind::Lit(Literal::String(s)) => Some(s.to_string()),
        _ => None,
    };
    match head.as_str() {
        "Lean.Name.anonymous" => true,
        "Lean.Name.str" | "Lean.Name.mkStr" if args.len() == 2 => {
            name_components(args[0], parts) && string(args[1]).map(|s| parts.push(s)).is_some()
        }
        "Lean.Name.num" | "Lean.Name.mkNum" if args.len() == 2 => {
            if !name_components(args[0], parts) {
                return false;
            }
            match args[1].kind() {
                ExprKind::Lit(Literal::Nat(n)) => {
                    parts.push(n.to_string());
                    true
                }
                _ => false,
            }
        }
        h if h.starts_with("Lean.Name.mkStr") => {
            let Ok(n) = h.trim_start_matches("Lean.Name.mkStr").parse::<usize>() else {
                return false;
            };
            if args.len() != n {
                return false;
            }
            args.iter()
                .all(|a| string(a).map(|s| parts.push(s)).is_some())
        }
        _ => false,
    }
}

/// `(head constant name, arguments)` of a constant-headed application.
fn const_app(e: &Expr) -> Option<(String, Vec<&Expr>)> {
    let head = e.get_app_fn();
    let ExprKind::Const(name, _) = head.kind() else {
        return None;
    };
    Some((name.to_string(), e.get_app_args().into_iter().collect()))
}

/// Call `f(head, args)` on every constant-headed application in `e`.
fn visit_apps(e: &Expr, f: &mut dyn FnMut(&str, &[&Expr])) {
    if let Some((head, args)) = const_app(e) {
        f(&head, &args);
    }
    match e.kind() {
        ExprKind::App(g, a) => {
            visit_apps(g, f);
            visit_apps(a, f);
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            visit_apps(ty, f);
            visit_apps(body, f);
        }
        ExprKind::Let(_, ty, val, body, _) => {
            visit_apps(ty, f);
            visit_apps(val, f);
            visit_apps(body, f);
        }
        ExprKind::MData(_, inner) | ExprKind::Proj(_, _, inner) => visit_apps(inner, f),
        _ => {}
    }
}

#[cfg(test)]
#[path = "imported_tactic_macro_tests.rs"]
mod tests;

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `autoParam` structure fields: a field declared `f : T := by tac` in Lean
//! is stored in the constructor as `(f : autoParam T S.f._autoParam)`, where
//! `S.f._autoParam : Lean.Syntax` is a `meta def` holding the tactic script
//! as a syntax tree. When a structure instance omits such a field, Lean runs
//! that script against `T` — `Preorder.lt_iff_le_not_ge := by intros; rfl`,
//! `LinearOrder.min_def := by intros; rfl` — and reports
//! "could not synthesize default value for field 'f' of 'S' using tactics"
//! when it fails.
//!
//! Clean had no notion of this: an omitted autoParam field was reported
//! `Missing field(s) for Preorder: lt_iff_le_not_ge`, so every Mathlib
//! `instance : Preorder _ where le_refl := …; le_trans := …` stopped there
//! (`Pi.preorder`, `Prod.instPreorder`, `LinearOrder.ofSubsingleton` at its
//! three, measured 2026-09-10).
//!
//! The script is recovered from the `_autoParam` constant's VALUE, an
//! ordinary kernel term built from `Lean.Syntax.node` / `Lean.mkAtom` /
//! `Lean.Syntax.ident` and `Array.push`/`Array.empty`, into its token text
//! (`intros ; rfl`), which the ordinary tactic grammar parses and the
//! ordinary `by`-bridge runs. Nothing is guessed: a syntax tree with a node
//! this decoder does not model is REFUSED, and the field then reports the
//! same failure Lean would report for a failing script — never a substitute
//! script, whose success could accept what Lean rejects.

use super::*;
use clean_kernel::expr::Literal;

impl ElabCtx<'_> {
    /// For each constructor FIELD of `struct_name`, in constructor order, the
    /// `_autoParam` script constant when the field's binder type is
    /// `autoParam T stx` with `stx` a constant; `None` otherwise.
    pub(super) fn structure_field_autoparams(
        &self,
        struct_name: &SurfaceName,
    ) -> Vec<Option<Name>> {
        let struct_name_obj = struct_name.name().clone();
        let Some(ind) = self.env.get_inductive(&struct_name_obj) else {
            return Vec::new();
        };
        let Some(ctor_name) = ind.constructor_names.first() else {
            return Vec::new();
        };
        let Some(ctor) = self.env.get_const(ctor_name) else {
            return Vec::new();
        };
        let mut out = Vec::new();
        let mut ty = &ctor.type_;
        let mut seen = 0usize;
        while let ExprKind::Pi(_, dom, body) = ty.kind() {
            if seen >= ind.num_params as usize {
                out.push(autoparam_script_const(dom));
            }
            seen += 1;
            ty = body;
        }
        out
    }

    /// Run the autoParam script `stx_const` against `goal` (the field's type
    /// with the `autoParam` wrapper stripped) and return the proof term.
    pub(super) fn discharge_autoparam_field(
        &mut self,
        struct_name: &SurfaceName,
        field: &str,
        stx_const: &Name,
        goal: &Expr,
    ) -> Result<Expr, ElabError> {
        let text = self.autoparam_script_text(stx_const).ok_or_else(|| {
            ElabError::StructureFieldTypeMismatch {
                struct_name: struct_name.name().clone(),
                field: field.to_string(),
                expected: goal.to_string(),
                actual: format!(
                    "could not synthesize default value for field '{field}' of \
                     '{struct_name}' using tactics: the autoParam script \
                     `{stx_const}` could not be decoded from its syntax tree"
                ),
            }
        })?;
        let by_expr = clean_parser::parse_expr(&format!("by {text}")).map_err(|e| {
            ElabError::StructureFieldTypeMismatch {
                struct_name: struct_name.name().clone(),
                field: field.to_string(),
                expected: goal.to_string(),
                actual: format!(
                    "could not synthesize default value for field '{field}' of \
                     '{struct_name}' using tactics: `by {text}` did not parse: {e}"
                ),
            }
        })?;
        self.elaborate_with_expected_type(&by_expr, Some(goal.clone()))
            .map_err(|e| ElabError::StructureFieldTypeMismatch {
                struct_name: struct_name.name().clone(),
                field: field.to_string(),
                expected: goal.to_string(),
                actual: format!(
                    "could not synthesize default value for field '{field}' of \
                     '{struct_name}' using tactics (`by {text}`): {e}"
                ),
            })
    }

    /// The token text of the `Lean.Syntax` value held by `stx_const`.
    pub(super) fn autoparam_script_text(&self, stx_const: &Name) -> Option<String> {
        let value = self.env.get_const(stx_const)?.value.clone()?;
        let mut tokens = Vec::new();
        if !syntax_tokens(&value, &mut tokens) {
            return None;
        }
        if tokens.is_empty() {
            return None;
        }
        Some(tokens.join(" "))
    }
}

/// `autoParam T stx` with `stx` a constant → that constant's name.
fn autoparam_script_const(dom: &Expr) -> Option<Name> {
    let head = dom.get_app_fn();
    let ExprKind::Const(name, _) = head.kind() else {
        return None;
    };
    if name.to_string() != "autoParam" {
        return None;
    }
    let args = dom.get_app_args();
    if args.len() != 2 {
        return None;
    }
    match args[1].kind() {
        ExprKind::Const(stx, _) => Some(stx.clone()),
        _ => None,
    }
}

/// Walk a `Lean.Syntax` term, appending its atoms and identifiers in source
/// order. Returns `false` on any node the decoder does not model.
fn syntax_tokens(e: &Expr, out: &mut Vec<String>) -> bool {
    let head = e.get_app_fn();
    let ExprKind::Const(name, _) = head.kind() else {
        return false;
    };
    let args = e.get_app_args();
    match name.to_string().as_str() {
        // Syntax.node (info) (kind) (args)
        "Lean.Syntax.node" if args.len() == 3 => array_children(args[2], out),
        // Syntax.atom (info) (val)
        "Lean.Syntax.atom" if args.len() == 2 => push_string_lit(args[1], out),
        // mkAtom (val) := Syntax.atom SourceInfo.none val
        "Lean.mkAtom" if args.len() == 1 => push_string_lit(args[0], out),
        // Syntax.ident (info) (rawVal) (val : Name) (preresolved)
        "Lean.Syntax.ident" if args.len() == 4 => push_name_lit(args[2], out),
        // mkIdent (val : Name)
        "Lean.mkIdent" if args.len() == 1 => push_name_lit(args[0], out),
        "Lean.Syntax.missing" if args.is_empty() => true,
        _ => false,
    }
}

/// Children of an `Array Syntax` built from `Array.push`/`Array.empty`,
/// `Array.mkEmpty`, `List.toArray`/`Array.mk` over `List.cons`/`List.nil`.
fn array_children(e: &Expr, out: &mut Vec<String>) -> bool {
    let head = e.get_app_fn();
    let ExprKind::Const(name, _) = head.kind() else {
        return false;
    };
    let args = e.get_app_args();
    match name.to_string().as_str() {
        // @Array.push α arr x
        "Array.push" if args.len() == 3 => {
            array_children(args[1], out) && syntax_tokens(args[2], out)
        }
        // @Array.empty α / @Array.mkEmpty α n / #[]
        "Array.empty" | "Array.mkEmpty" | "Array.emptyWithCapacity" => true,
        // @List.toArray α l / @Array.mk α l
        "List.toArray" | "Array.mk" if args.len() == 2 => list_children(args[1], out),
        _ => false,
    }
}

fn list_children(e: &Expr, out: &mut Vec<String>) -> bool {
    let head = e.get_app_fn();
    let ExprKind::Const(name, _) = head.kind() else {
        return false;
    };
    let args = e.get_app_args();
    match name.to_string().as_str() {
        "List.nil" => true,
        "List.cons" if args.len() == 3 => {
            syntax_tokens(args[1], out) && list_children(args[2], out)
        }
        _ => false,
    }
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

/// A `Lean.Name` literal built from `Name.anonymous` / `Name.str` /
/// `Name.mkStr` / `Name.num` / `Name.mkNum`, rendered dotted.
fn push_name_lit(e: &Expr, out: &mut Vec<String>) -> bool {
    let mut parts = Vec::new();
    if !name_components(e, &mut parts) {
        return false;
    }
    out.push(parts.join("."));
    true
}

fn name_components(e: &Expr, parts: &mut Vec<String>) -> bool {
    let head = e.get_app_fn();
    let ExprKind::Const(name, _) = head.kind() else {
        return false;
    };
    let args = e.get_app_args();
    match name.to_string().as_str() {
        "Lean.Name.anonymous" => true,
        "Lean.Name.str" | "Lean.Name.mkStr" if args.len() == 2 => {
            if !name_components(args[0], parts) {
                return false;
            }
            match args[1].kind() {
                ExprKind::Lit(Literal::String(s)) => {
                    parts.push(s.to_string());
                    true
                }
                _ => false,
            }
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
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn s(v: &str) -> Expr {
        Expr::str_lit(v)
    }
    fn c(n: &str) -> Expr {
        Expr::const_(Name::from_string(n), vec![])
    }
    fn info() -> Expr {
        c("Lean.SourceInfo.none")
    }
    fn node(kind: &str, children: Vec<Expr>) -> Expr {
        let mut arr = Expr::app(c("Array.empty"), c("Lean.Syntax"));
        for ch in children {
            arr = Expr::apps(c("Array.push"), [c("Lean.Syntax"), arr, ch]);
        }
        Expr::apps(c("Lean.Syntax.node"), [info(), c(kind), arr])
    }
    fn atom(v: &str) -> Expr {
        Expr::app(c("Lean.mkAtom"), s(v))
    }

    /// The exact shape `#print Preorder.lt_iff_le_not_ge._autoParam` shows on
    /// the pinned toolchain: `tacticSeq [tacticSeq1Indented [null [intros
    /// [atom "intros", null []], atom ";", tacticRfl [atom "rfl"]]]]`.
    #[test]
    fn decodes_intros_semicolon_rfl() {
        let intros = node(
            "Lean.Parser.Tactic.intros",
            vec![atom("intros"), node("null", vec![])],
        );
        let rfl = node("Lean.Parser.Tactic.tacticRfl", vec![atom("rfl")]);
        let seq = node(
            "Lean.Parser.Tactic.tacticSeq",
            vec![node(
                "Lean.Parser.Tactic.tacticSeq1Indented",
                vec![node("null", vec![intros, atom(";"), rfl])],
            )],
        );
        let mut out = Vec::new();
        assert!(syntax_tokens(&seq, &mut out));
        assert_eq!(out.join(" "), "intros ; rfl");
    }

    #[test]
    fn an_unmodelled_node_is_refused_not_guessed() {
        let weird = Expr::apps(c("Lean.Syntax.something"), [info(), atom("x")]);
        let mut out = Vec::new();
        assert!(!syntax_tokens(&weird, &mut out));
    }

    #[test]
    fn identifiers_render_dotted() {
        let name = Expr::apps(
            c("Lean.Name.mkStr"),
            [
                Expr::apps(c("Lean.Name.mkStr"), [c("Lean.Name.anonymous"), s("Nat")]),
                s("le_refl"),
            ],
        );
        let ident = Expr::app(c("Lean.mkIdent"), name);
        let mut out = Vec::new();
        assert!(syntax_tokens(&ident, &mut out));
        assert_eq!(out, vec!["Nat.le_refl".to_string()]);
    }
}

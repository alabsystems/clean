// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::common::{find_nested_identifier, node_text, parse_storage_class};
use super::{CParser, NodeExt, ParseError, ParseResult};
use crate::expr::{CExpr, Designator, Initializer};
use crate::stmt::{CStmt, StorageClass, VarDecl};
use crate::types::CType;
use tree_sitter::Node;

impl CParser {
    /// Parse compound statement (block)
    pub(super) fn parse_compound_stmt(&self, node: Node<'_>, source: &str) -> ParseResult<CStmt> {
        let mut stmts = Vec::new();

        for i in 0..node.child_count() {
            if let Some(child) = node.child_at(i) {
                if child.kind() == "{" || child.kind() == "}" {
                    continue;
                }

                let stmt = self.parse_stmt(child, source)?;
                if !matches!(stmt, CStmt::Empty) {
                    stmts.push(stmt);
                }
            }
        }

        Ok(CStmt::Block(stmts))
    }

    /// Parse a statement
    pub(super) fn parse_stmt(&self, node: Node<'_>, source: &str) -> ParseResult<CStmt> {
        match node.kind() {
            "compound_statement" => self.parse_compound_stmt(node, source),
            "expression_statement" => {
                if let Some(child) = node.child_at(0) {
                    if child.kind() == ";" {
                        return Ok(CStmt::Empty);
                    }
                    // `_Static_assert(expr, "msg")` / `static_assert(expr)` is
                    // surfaced by tree-sitter-c (0.24) as an ordinary
                    // `call_expression`. Recognize it here and lower to a
                    // dedicated static-assertion statement (C11 6.7.10).
                    if let Some(stmt) = self.try_parse_static_assert(child, source)? {
                        return Ok(stmt);
                    }
                    let expr = self.parse_expr(child, source)?;
                    Ok(CStmt::Expr(expr))
                } else {
                    Ok(CStmt::Empty)
                }
            }
            // C23 / some grammars expose a dedicated declaration node.
            "static_assert_declaration" | "static_assertion_declaration" => {
                self.parse_static_assert_decl(node, source)
            }
            "declaration" => self.parse_declaration(node, source),
            "if_statement" => self.parse_if_stmt(node, source),
            "while_statement" => self.parse_while_stmt(node, source),
            "for_statement" => self.parse_for_stmt(node, source),
            "do_statement" => self.parse_do_stmt(node, source),
            "return_statement" => self.parse_return_stmt(node, source),
            "break_statement" => Ok(CStmt::Break),
            "continue_statement" => Ok(CStmt::Continue),
            "goto_statement" => self.parse_goto_stmt(node, source),
            "labeled_statement" => self.parse_labeled_stmt(node, source),
            "switch_statement" => self.parse_switch_stmt(node, source),
            ";" => Ok(CStmt::Empty),
            "call_expression" => {
                if let Some(stmt) = self.try_parse_static_assert(node, source)? {
                    return Ok(stmt);
                }
                Ok(CStmt::Expr(self.parse_expr(node, source)?))
            }
            _ => {
                // Try parsing as expression
                if let Ok(expr) = self.parse_expr(node, source) {
                    Ok(CStmt::Expr(expr))
                } else {
                    Err(ParseError::Unsupported {
                        line: node.start_position().row + 1,
                        column: node.start_position().column + 1,
                        kind: node.kind().to_string(),
                    })
                }
            }
        }
    }

    /// Recognize a `_Static_assert` / `static_assert` spelled as a call
    /// expression and lower it to [`CStmt::StaticAssert`].
    ///
    /// Returns `Ok(None)` when `node` is an ordinary call expression (so the
    /// caller falls back to treating it as a normal expression statement).
    fn try_parse_static_assert(&self, node: Node<'_>, source: &str) -> ParseResult<Option<CStmt>> {
        if node.kind() != "call_expression" {
            return Ok(None);
        }

        let mut callee = None;
        let mut arg_list = None;
        for i in 0..node.child_count() {
            if let Some(child) = node.child_at(i) {
                match child.kind() {
                    "identifier" => callee = Some(node_text(child, source)),
                    "argument_list" => arg_list = Some(child),
                    _ => {}
                }
            }
        }

        match callee.as_deref() {
            Some("_Static_assert" | "static_assert") => {}
            _ => return Ok(None),
        }

        let arg_list = arg_list.ok_or_else(|| ParseError::MissingField {
            field: "argument_list".to_string(),
            node_kind: "_Static_assert".to_string(),
        })?;
        self.build_static_assert(arg_list, source).map(Some)
    }

    /// Build a [`CStmt::StaticAssert`] from a tree-sitter `argument_list` node.
    ///
    /// Accepts both the C11 two-argument form `(const-expr, "message")` and
    /// the C23 single-argument form `(const-expr)`.
    fn build_static_assert(&self, arg_list: Node<'_>, source: &str) -> ParseResult<CStmt> {
        let mut cond: Option<CExpr> = None;
        let mut message: Option<String> = None;

        for i in 0..arg_list.child_count() {
            if let Some(child) = arg_list.child_at(i) {
                match child.kind() {
                    "(" | ")" | "," => {}
                    "string_literal" => {
                        message = Some(static_assert_string_literal(child, source));
                    }
                    _ => {
                        if cond.is_none() {
                            cond = Some(self.parse_expr(child, source)?);
                        }
                    }
                }
            }
        }

        let cond = cond.ok_or_else(|| ParseError::MissingField {
            field: "constant-expression".to_string(),
            node_kind: "_Static_assert".to_string(),
        })?;

        Ok(CStmt::StaticAssert { cond, message })
    }

    /// Parse a dedicated `static_assert(ion)_declaration` grammar node (C23
    /// and some grammar variants). The condition is the first non-keyword
    /// expression child; the optional message is a string literal.
    fn parse_static_assert_decl(&self, node: Node<'_>, source: &str) -> ParseResult<CStmt> {
        let mut cond: Option<CExpr> = None;
        let mut message: Option<String> = None;

        for i in 0..node.child_count() {
            if let Some(child) = node.child_at(i) {
                match child.kind() {
                    "_Static_assert" | "static_assert" | "(" | ")" | "," | ";" => {}
                    "string_literal" => {
                        message = Some(static_assert_string_literal(child, source));
                    }
                    _ => {
                        if cond.is_none() {
                            if let Ok(expr) = self.parse_expr(child, source) {
                                cond = Some(expr);
                            }
                        }
                    }
                }
            }
        }

        let cond = cond.ok_or_else(|| ParseError::MissingField {
            field: "constant-expression".to_string(),
            node_kind: node.kind().to_string(),
        })?;

        Ok(CStmt::StaticAssert { cond, message })
    }

    /// Parse declaration statement
    fn parse_declaration(&self, node: Node<'_>, source: &str) -> ParseResult<CStmt> {
        let mut ty = CType::Void;
        let mut storage = StorageClass::Auto;
        let mut decls = Vec::new();

        for i in 0..node.child_count() {
            if let Some(child) = node.child_at(i) {
                match child.kind() {
                    "storage_class_specifier" => {
                        let text = node_text(child, source);
                        storage = parse_storage_class(&text);
                    }
                    "primitive_type"
                    | "type_identifier"
                    | "sized_type_specifier"
                    | "struct_specifier"
                    | "union_specifier"
                    | "enum_specifier" => {
                        ty = self.parse_type_node(child, source)?;
                    }
                    "init_declarator" => {
                        let decl =
                            self.parse_init_declarator(child, source, ty.clone(), storage)?;
                        decls.push(decl);
                    }
                    "identifier" => {
                        let name = node_text(child, source);
                        decls.push(VarDecl::new(name, ty.clone()).with_storage(storage));
                    }
                    "pointer_declarator" => {
                        let ptr_ty = CType::Pointer(Box::new(ty.clone()));
                        if let Some(name) = find_nested_identifier(child, source, &["identifier"]) {
                            decls.push(VarDecl::new(name, ptr_ty).with_storage(storage));
                        }
                    }
                    "array_declarator" => {
                        if let Some((name, size)) = self.parse_array_declarator(child, source)? {
                            let arr_ty = CType::Array(Box::new(ty.clone()), size);
                            decls.push(VarDecl::new(name, arr_ty).with_storage(storage));
                        }
                    }
                    _ => {}
                }
            }
        }

        if decls.is_empty() {
            Ok(CStmt::Empty)
        } else if decls.len() == 1 {
            Ok(CStmt::Decl(decls.remove(0)))
        } else {
            Ok(CStmt::Block(decls.into_iter().map(CStmt::Decl).collect()))
        }
    }

    /// Parse init_declarator
    fn parse_init_declarator(
        &self,
        node: Node<'_>,
        source: &str,
        base_ty: CType,
        storage: StorageClass,
    ) -> ParseResult<VarDecl> {
        let mut name = String::new();
        let mut ty = base_ty;
        let mut init = None;

        for i in 0..node.child_count() {
            if let Some(child) = node.child_at(i) {
                match child.kind() {
                    "identifier" => {
                        name = node_text(child, source);
                    }
                    "pointer_declarator" => {
                        ty = CType::Pointer(Box::new(ty));
                        if let Some(inner_name) =
                            find_nested_identifier(child, source, &["identifier"])
                        {
                            name = inner_name;
                        }
                    }
                    "array_declarator" => {
                        if let Some((arr_name, size)) =
                            self.parse_array_declarator(child, source)?
                        {
                            name = arr_name;
                            ty = CType::Array(Box::new(ty), size);
                        }
                    }
                    "=" => {}
                    _ => {
                        // Try to parse as initializer
                        if let Ok(expr) = self.parse_expr(child, source) {
                            init = Some(Initializer::Expr(expr));
                        } else if child.kind() == "initializer_list" {
                            init = Some(self.parse_initializer_list(child, source)?);
                        }
                    }
                }
            }
        }

        let mut decl = VarDecl::new(name, ty).with_storage(storage);
        if let Some(initializer) = init {
            decl = decl.with_init(initializer);
        }
        Ok(decl)
    }

    /// Parse initializer list
    pub(super) fn parse_initializer_list(
        &self,
        node: Node<'_>,
        source: &str,
    ) -> ParseResult<Initializer> {
        let mut items = Vec::new();

        for i in 0..node.child_count() {
            if let Some(child) = node.child_at(i) {
                match child.kind() {
                    "{" | "}" | "," => {}
                    "initializer_list" => {
                        items.push(self.parse_initializer_list(child, source)?);
                    }
                    "initializer_pair" => {
                        items.push(self.parse_initializer_pair(child, source)?);
                    }
                    _ => {
                        if let Ok(expr) = self.parse_expr(child, source) {
                            items.push(Initializer::Expr(expr));
                        }
                    }
                }
            }
        }

        Ok(Initializer::List(items))
    }

    /// Parse a designated initializer pair: `.field = value`, `[index] = value`,
    /// or a chained form such as `.a.b = value` / `[i].f = value`.
    ///
    /// Tree-sitter shape (C grammar):
    /// ```text
    /// initializer_pair
    ///   field_designator    '.' field_identifier      (one or more, in chain order)
    ///   subscript_designator '[' expr ']'             (one or more, in chain order)
    ///   '='
    ///   <value: expression or initializer_list>
    /// ```
    fn parse_initializer_pair(&self, node: Node<'_>, source: &str) -> ParseResult<Initializer> {
        let mut designators = Vec::new();
        let mut value: Option<Initializer> = None;

        for i in 0..node.child_count() {
            if let Some(child) = node.child_at(i) {
                match child.kind() {
                    "field_designator" => {
                        let field = find_nested_identifier(child, source, &["field_identifier"])
                            .ok_or_else(|| ParseError::MissingField {
                                field: "field_identifier".to_string(),
                                node_kind: "field_designator".to_string(),
                            })?;
                        designators.push(Designator::Field(field));
                    }
                    "subscript_designator" => {
                        // Grab the index expression between the brackets.
                        let mut idx = None;
                        for j in 0..child.child_count() {
                            if let Some(grandchild) = child.child_at(j) {
                                if !matches!(grandchild.kind(), "[" | "]") {
                                    idx = Some(self.parse_expr(grandchild, source)?);
                                    break;
                                }
                            }
                        }
                        let idx = idx.ok_or_else(|| ParseError::MissingField {
                            field: "index".to_string(),
                            node_kind: "subscript_designator".to_string(),
                        })?;
                        designators.push(Designator::Index(Box::new(idx)));
                    }
                    "=" => {}
                    "initializer_list" => {
                        value = Some(self.parse_initializer_list(child, source)?);
                    }
                    _ => {
                        if let Ok(expr) = self.parse_expr(child, source) {
                            value = Some(Initializer::Expr(expr));
                        }
                    }
                }
            }
        }

        let value = value.ok_or_else(|| ParseError::MissingField {
            field: "value".to_string(),
            node_kind: "initializer_pair".to_string(),
        })?;

        let designator = if designators.len() == 1 {
            match designators.into_iter().next() {
                Some(d) => d,
                None => {
                    return Err(ParseError::MissingField {
                        field: "designator".to_string(),
                        node_kind: "initializer_pair".to_string(),
                    });
                }
            }
        } else if designators.is_empty() {
            return Err(ParseError::MissingField {
                field: "designator".to_string(),
                node_kind: "initializer_pair".to_string(),
            });
        } else {
            Designator::Chain(designators)
        };

        Ok(Initializer::Designated {
            designator,
            init: Box::new(value),
        })
    }

    /// Parse if statement
    fn parse_if_stmt(&self, node: Node<'_>, source: &str) -> ParseResult<CStmt> {
        let mut cond = None;
        let mut then_branch = None;
        let mut else_branch = None;

        for i in 0..node.child_count() {
            if let Some(child) = node.child_at(i) {
                match child.kind() {
                    "parenthesized_expression" => {
                        if let Some(inner) = child.child_at(1) {
                            cond = Some(self.parse_expr(inner, source)?);
                        }
                    }
                    "if" | "else" | "(" | ")" => {}
                    _ => {
                        if cond.is_some() && then_branch.is_none() {
                            then_branch = Some(Box::new(self.parse_stmt(child, source)?));
                        } else if then_branch.is_some() {
                            else_branch = Some(Box::new(self.parse_stmt(child, source)?));
                        }
                    }
                }
            }
        }

        Ok(CStmt::If {
            cond: cond.unwrap_or(CExpr::IntLit(1)),
            then_stmt: then_branch.unwrap_or_else(|| Box::new(CStmt::Empty)),
            else_stmt: else_branch,
        })
    }

    /// Parse while statement
    fn parse_while_stmt(&self, node: Node<'_>, source: &str) -> ParseResult<CStmt> {
        let mut cond = None;
        let mut body = None;

        for i in 0..node.child_count() {
            if let Some(child) = node.child_at(i) {
                match child.kind() {
                    "parenthesized_expression" => {
                        if let Some(inner) = child.child_at(1) {
                            cond = Some(self.parse_expr(inner, source)?);
                        }
                    }
                    "while" | "(" | ")" => {}
                    _ => {
                        body = Some(Box::new(self.parse_stmt(child, source)?));
                    }
                }
            }
        }

        Ok(CStmt::While {
            cond: cond.unwrap_or(CExpr::IntLit(1)),
            body: body.unwrap_or_else(|| Box::new(CStmt::Empty)),
        })
    }

    /// Parse for statement
    fn parse_for_stmt(&self, node: Node<'_>, source: &str) -> ParseResult<CStmt> {
        let mut init = None;
        let mut cond = None;
        let mut update = None;
        let mut body = None;
        let mut phase = 0; // 0=init, 1=cond, 2=update, 3=body

        for i in 0..node.child_count() {
            if let Some(child) = node.child_at(i) {
                match child.kind() {
                    "for" | "(" | ")" => {}
                    ";" => {
                        phase += 1;
                    }
                    "declaration" => {
                        if phase == 0 {
                            init = Some(Box::new(self.parse_declaration(child, source)?));
                        }
                    }
                    _ => {
                        if phase == 0 {
                            if let Ok(expr) = self.parse_expr(child, source) {
                                init = Some(Box::new(CStmt::Expr(expr)));
                            }
                        } else if phase == 1 {
                            if let Ok(expr) = self.parse_expr(child, source) {
                                cond = Some(expr);
                            }
                        } else if phase == 2 {
                            if let Ok(expr) = self.parse_expr(child, source) {
                                update = Some(expr);
                            }
                        } else {
                            body = Some(Box::new(self.parse_stmt(child, source)?));
                        }
                    }
                }
            }
        }

        Ok(CStmt::For {
            init,
            cond,
            update,
            body: body.unwrap_or_else(|| Box::new(CStmt::Empty)),
        })
    }

    /// Parse do-while statement
    fn parse_do_stmt(&self, node: Node<'_>, source: &str) -> ParseResult<CStmt> {
        let mut body = None;
        let mut cond = None;

        for i in 0..node.child_count() {
            if let Some(child) = node.child_at(i) {
                match child.kind() {
                    "do" | "while" | "(" | ")" | ";" => {}
                    "parenthesized_expression" => {
                        if let Some(inner) = child.child_at(1) {
                            cond = Some(self.parse_expr(inner, source)?);
                        }
                    }
                    _ => {
                        body = Some(Box::new(self.parse_stmt(child, source)?));
                    }
                }
            }
        }

        Ok(CStmt::DoWhile {
            body: body.unwrap_or_else(|| Box::new(CStmt::Empty)),
            cond: cond.unwrap_or(CExpr::IntLit(1)),
        })
    }

    /// Parse return statement
    fn parse_return_stmt(&self, node: Node<'_>, source: &str) -> ParseResult<CStmt> {
        for i in 0..node.child_count() {
            if let Some(child) = node.child_at(i) {
                if child.kind() != "return" && child.kind() != ";" {
                    let expr = self.parse_expr(child, source)?;
                    return Ok(CStmt::Return(Some(expr)));
                }
            }
        }
        Ok(CStmt::Return(None))
    }

    /// Parse goto statement
    fn parse_goto_stmt(&self, node: Node<'_>, source: &str) -> ParseResult<CStmt> {
        for i in 0..node.child_count() {
            if let Some(child) = node.child_at(i) {
                // tree-sitter-c uses "statement_identifier" for goto labels
                if child.kind() == "identifier" || child.kind() == "statement_identifier" {
                    return Ok(CStmt::Goto(node_text(child, source)));
                }
            }
        }
        Err(ParseError::MissingField {
            field: "label".to_string(),
            node_kind: "goto_statement".to_string(),
        })
    }

    /// Parse labeled statement
    fn parse_labeled_stmt(&self, node: Node<'_>, source: &str) -> ParseResult<CStmt> {
        let mut label = String::new();
        let mut stmt = None;

        for i in 0..node.child_count() {
            if let Some(child) = node.child_at(i) {
                match child.kind() {
                    // tree-sitter-c uses "statement_identifier" for labels
                    "statement_identifier" | "identifier" => {
                        label = node_text(child, source);
                    }
                    ":" => {}
                    _ => {
                        stmt = Some(Box::new(self.parse_stmt(child, source)?));
                    }
                }
            }
        }

        Ok(CStmt::Label {
            name: label,
            stmt: stmt.unwrap_or_else(|| Box::new(CStmt::Empty)),
        })
    }

    /// Parse switch statement
    fn parse_switch_stmt(&self, node: Node<'_>, source: &str) -> ParseResult<CStmt> {
        let mut cond = None;
        let mut body = None;

        for i in 0..node.child_count() {
            if let Some(child) = node.child_at(i) {
                match child.kind() {
                    "parenthesized_expression" => {
                        if let Some(inner) = child.child_at(1) {
                            cond = Some(self.parse_expr(inner, source)?);
                        }
                    }
                    "compound_statement" => {
                        body = Some(Box::new(self.parse_switch_body(child, source)?));
                    }
                    _ => {}
                }
            }
        }

        Ok(CStmt::Switch {
            cond: cond.unwrap_or(CExpr::IntLit(0)),
            body: body.unwrap_or_else(|| Box::new(CStmt::Empty)),
        })
    }

    /// Parse switch body (convert case labels to Case statements)
    fn parse_switch_body(&self, node: Node<'_>, source: &str) -> ParseResult<CStmt> {
        let mut stmts = Vec::new();

        for i in 0..node.child_count() {
            if let Some(child) = node.child_at(i) {
                match child.kind() {
                    "{" | "}" => {}
                    "case_statement" => {
                        let stmt = self.parse_case_stmt(child, source)?;
                        stmts.push(stmt);
                    }
                    _ => {
                        let stmt = self.parse_stmt(child, source)?;
                        if !matches!(stmt, CStmt::Empty) {
                            stmts.push(stmt);
                        }
                    }
                }
            }
        }

        Ok(CStmt::Block(stmts))
    }

    /// Parse case statement
    fn parse_case_stmt(&self, node: Node<'_>, source: &str) -> ParseResult<CStmt> {
        let mut label = crate::stmt::CaseLabel::Default;
        let mut body_stmts = Vec::new();
        let mut after_colon = false;

        for i in 0..node.child_count() {
            if let Some(child) = node.child_at(i) {
                match child.kind() {
                    "case" => {}
                    "default" => {
                        label = crate::stmt::CaseLabel::Default;
                    }
                    ":" => {
                        after_colon = true;
                    }
                    _ => {
                        if after_colon {
                            let stmt = self.parse_stmt(child, source)?;
                            if !matches!(stmt, CStmt::Empty) {
                                body_stmts.push(stmt);
                            }
                        } else if let Ok(expr) = self.parse_expr(child, source) {
                            label = crate::stmt::CaseLabel::Case(expr);
                        }
                    }
                }
            }
        }

        let body = if body_stmts.is_empty() {
            CStmt::Empty
        } else if body_stmts.len() == 1 {
            body_stmts.remove(0)
        } else {
            CStmt::Block(body_stmts)
        };

        Ok(CStmt::Case {
            label,
            stmt: Box::new(body),
        })
    }
}

/// Extract the textual content of a tree-sitter `string_literal` node, with the
/// surrounding double quotes stripped. Prefers the dedicated `string_content`
/// child when present (tree-sitter-c shape), falling back to trimming quotes
/// from the raw node text.
fn static_assert_string_literal(node: Node<'_>, source: &str) -> String {
    for i in 0..node.child_count() {
        if let Some(child) = node.child_at(i) {
            if child.kind() == "string_content" {
                return node_text(child, source);
            }
        }
    }
    let raw = node_text(node, source);
    raw.trim_start_matches('"')
        .trim_end_matches('"')
        .to_string()
}

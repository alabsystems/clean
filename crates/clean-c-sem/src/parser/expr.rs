// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Expression dispatch and non-operator expression forms.

use super::common::node_text;
use super::{CParser, NodeExt, ParseError, ParseResult};
use crate::expr::{BinOp, CExpr, Initializer, SizeOfArg, UnaryOp};
use crate::types::CType;
use tree_sitter::Node;

impl CParser {
    /// Parse an expression
    pub(super) fn parse_expr(&self, node: Node<'_>, source: &str) -> ParseResult<CExpr> {
        match node.kind() {
            "number_literal" => {
                let text = node_text(node, source);
                self.parse_number_literal(&text)
            }
            "char_literal" => {
                let text = node_text(node, source);
                self.parse_char_literal(&text)
            }
            "string_literal" => {
                let text = node_text(node, source);
                // Remove quotes
                let inner = text.trim_start_matches('"').trim_end_matches('"');
                Ok(CExpr::StringLit(inner.to_string()))
            }
            "identifier" => Ok(CExpr::Var(node_text(node, source))),
            "true" => Ok(CExpr::IntLit(1)),
            "false" => Ok(CExpr::IntLit(0)),
            "null" | "NULL" => Ok(CExpr::null()),
            "parenthesized_expression" => {
                // Get inner expression
                if let Some(inner) = node.child_at(1) {
                    self.parse_expr(inner, source)
                } else {
                    Err(ParseError::MissingField {
                        field: "expression".to_string(),
                        node_kind: "parenthesized_expression".to_string(),
                    })
                }
            }
            "binary_expression" => self.parse_binary_expr(node, source),
            "unary_expression" => self.parse_unary_expr(node, source),
            "update_expression" => self.parse_update_expr(node, source),
            "assignment_expression" => self.parse_assignment_expr(node, source),
            "conditional_expression" => self.parse_conditional_expr(node, source),
            "call_expression" => self.parse_call_expr(node, source),
            "cast_expression" => self.parse_cast_expr(node, source),
            "subscript_expression" => self.parse_subscript_expr(node, source),
            "field_expression" => self.parse_field_expr(node, source),
            "pointer_expression" => self.parse_pointer_expr(node, source),
            "sizeof_expression" => self.parse_sizeof_expr(node, source),
            "alignof_expression" => self.parse_alignof_expr(node, source),
            "comma_expression" => self.parse_comma_expr(node, source),
            "compound_literal_expression" => self.parse_compound_literal(node, source),
            _ => Err(ParseError::Unsupported {
                line: node.start_position().row + 1,
                column: node.start_position().column + 1,
                kind: format!("expression: {}", node.kind()),
            }),
        }
    }

    /// Parse function call expression
    fn parse_call_expr(&self, node: Node<'_>, source: &str) -> ParseResult<CExpr> {
        let mut func = None;
        let mut args = Vec::new();

        for i in 0..node.child_count() {
            if let Some(child) = node.child_at(i) {
                match child.kind() {
                    "identifier" | "field_expression" => {
                        func = Some(self.parse_expr(child, source)?);
                    }
                    "argument_list" => {
                        args = self.parse_arg_list(child, source)?;
                    }
                    _ => {}
                }
            }
        }

        Ok(CExpr::Call {
            func: Box::new(func.ok_or_else(|| ParseError::MissingField {
                field: "function".to_string(),
                node_kind: "call_expression".to_string(),
            })?),
            args,
        })
    }

    /// Parse argument list
    fn parse_arg_list(&self, node: Node<'_>, source: &str) -> ParseResult<Vec<CExpr>> {
        let mut args = Vec::new();

        for i in 0..node.child_count() {
            if let Some(child) = node.child_at(i) {
                if child.kind() != "(" && child.kind() != ")" && child.kind() != "," {
                    args.push(self.parse_expr(child, source)?);
                }
            }
        }

        Ok(args)
    }

    /// Parse cast expression
    fn parse_cast_expr(&self, node: Node<'_>, source: &str) -> ParseResult<CExpr> {
        let mut ty = CType::Void;
        let mut expr = None;

        for i in 0..node.child_count() {
            if let Some(child) = node.child_at(i) {
                match child.kind() {
                    "(" | ")" => {}
                    "type_descriptor" => {
                        ty = self.parse_type_descriptor(child, source)?;
                    }
                    _ => {
                        expr = Some(self.parse_expr(child, source)?);
                    }
                }
            }
        }

        Ok(CExpr::Cast {
            ty,
            expr: Box::new(expr.ok_or_else(|| ParseError::MissingField {
                field: "expression".to_string(),
                node_kind: "cast_expression".to_string(),
            })?),
        })
    }

    /// Parse type descriptor
    fn parse_type_descriptor(&self, node: Node<'_>, source: &str) -> ParseResult<CType> {
        let mut ty = CType::Void;
        let mut pointer_count = 0;
        // Array bounds, outermost-first in source order (e.g. `int[2][3]` ->
        // [Some(2), Some(3)]). `None` is an unspecified bound (`int[]`), which
        // for a compound literal is inferred from the initializer count.
        let mut array_dims: Vec<Option<usize>> = Vec::new();

        for i in 0..node.child_count() {
            if let Some(child) = node.child_at(i) {
                match child.kind() {
                    "primitive_type"
                    | "type_identifier"
                    | "sized_type_specifier"
                    | "struct_specifier"
                    | "union_specifier"
                    | "enum_specifier" => {
                        ty = self.parse_type_node(child, source)?;
                    }
                    "abstract_pointer_declarator" => {
                        pointer_count += self.count_pointers(child);
                    }
                    "abstract_array_declarator" => {
                        self.collect_abstract_array_dims(child, source, &mut array_dims)?;
                    }
                    "*" => {
                        pointer_count += 1;
                    }
                    _ => {}
                }
            }
        }

        for _ in 0..pointer_count {
            ty = CType::Pointer(Box::new(ty));
        }

        // Wrap from the innermost dimension outward so `int[2][3]` becomes
        // `Array(Array(int, 3), 2)`. An unspecified bound is encoded as `0`
        // here; the compound-literal handler patches the outermost `0` from
        // the initializer count (C99 6.7.9p22).
        for dim in array_dims.into_iter().rev() {
            ty = CType::Array(Box::new(ty), dim.unwrap_or(0));
        }

        Ok(ty)
    }

    /// Collect bounds from a (possibly nested) `abstract_array_declarator`.
    ///
    /// Tree-sitter nests `int[2][3]` as
    /// `abstract_array_declarator(abstract_array_declarator [ 3 ]) [ 2 ]`,
    /// i.e. the outer node carries the *first* (leftmost) bound and wraps the
    /// inner declarator. We descend first so the collected vector is in
    /// outermost-first source order.
    fn collect_abstract_array_dims(
        &self,
        node: Node<'_>,
        source: &str,
        dims: &mut Vec<Option<usize>>,
    ) -> ParseResult<()> {
        let mut bound: Option<usize> = None;
        let mut nested: Option<Node<'_>> = None;
        for i in 0..node.child_count() {
            if let Some(child) = node.child_at(i) {
                match child.kind() {
                    "abstract_array_declarator" => nested = Some(child),
                    "number_literal" => {
                        let text = node_text(child, source);
                        bound = Some(self.parse_int_literal(&text)? as usize);
                    }
                    _ => {}
                }
            }
        }
        if let Some(inner) = nested {
            self.collect_abstract_array_dims(inner, source, dims)?;
        }
        dims.push(bound);
        Ok(())
    }

    /// Parse a C99 compound literal: `(type-name){ initializer-list }`.
    ///
    /// Semantically (C99 6.5.2.5) this denotes an unnamed object of the given
    /// type initialized by the brace list; the evaluator allocates storage and
    /// returns it as an lvalue. The tree-sitter shape is
    /// `compound_literal_expression( '(' type_descriptor ')' initializer_list )`.
    ///
    /// For an array type with an unspecified bound (`(int[]){1,2,3}`), the size
    /// is inferred from the number of top-level initializers, per 6.7.9p22.
    fn parse_compound_literal(&self, node: Node<'_>, source: &str) -> ParseResult<CExpr> {
        let mut ty: Option<CType> = None;
        let mut init: Option<Vec<Initializer>> = None;

        for i in 0..node.child_count() {
            if let Some(child) = node.child_at(i) {
                match child.kind() {
                    "type_descriptor" => {
                        ty = Some(self.parse_type_descriptor(child, source)?);
                    }
                    "initializer_list" => match self.parse_initializer_list(child, source)? {
                        Initializer::List(items) => init = Some(items),
                        // `parse_initializer_list` always returns `List`; treat
                        // any other shape as a single-element list defensively.
                        other => init = Some(vec![other]),
                    },
                    _ => {}
                }
            }
        }

        let mut ty = ty.ok_or_else(|| ParseError::MissingField {
            field: "type_descriptor".to_string(),
            node_kind: "compound_literal_expression".to_string(),
        })?;
        let init = init.ok_or_else(|| ParseError::MissingField {
            field: "initializer_list".to_string(),
            node_kind: "compound_literal_expression".to_string(),
        })?;

        // Infer an unspecified outermost array bound from the initializer count.
        if let CType::Array(elem, 0) = &ty {
            ty = CType::Array(elem.clone(), init.len());
        }

        Ok(CExpr::CompoundLiteral { ty, init })
    }

    /// Count pointer levels
    fn count_pointers(&self, node: Node<'_>) -> usize {
        let mut count = 0;
        for i in 0..node.child_count() {
            if let Some(child) = node.child_at(i) {
                if child.kind() == "*" {
                    count += 1;
                } else if child.kind() == "abstract_pointer_declarator" {
                    count += self.count_pointers(child);
                }
            }
        }
        if count == 0 {
            1
        } else {
            count
        }
    }

    /// Parse subscript expression (array access)
    fn parse_subscript_expr(&self, node: Node<'_>, source: &str) -> ParseResult<CExpr> {
        let mut array = None;
        let mut index = None;

        for i in 0..node.child_count() {
            if let Some(child) = node.child_at(i) {
                if child.kind() == "[" || child.kind() == "]" {
                    continue;
                }
                if array.is_none() {
                    array = Some(self.parse_expr(child, source)?);
                } else {
                    index = Some(self.parse_expr(child, source)?);
                }
            }
        }

        Ok(CExpr::Index {
            array: Box::new(array.ok_or_else(|| ParseError::MissingField {
                field: "array".to_string(),
                node_kind: "subscript_expression".to_string(),
            })?),
            index: Box::new(index.ok_or_else(|| ParseError::MissingField {
                field: "index".to_string(),
                node_kind: "subscript_expression".to_string(),
            })?),
        })
    }

    /// Parse field expression (struct.field or struct->field)
    fn parse_field_expr(&self, node: Node<'_>, source: &str) -> ParseResult<CExpr> {
        let mut base = None;
        let mut field = String::new();
        let mut is_ptr = false;

        for i in 0..node.child_count() {
            if let Some(child) = node.child_at(i) {
                match child.kind() {
                    "." => is_ptr = false,
                    "->" => is_ptr = true,
                    "field_identifier" => {
                        field = node_text(child, source);
                    }
                    _ => {
                        base = Some(self.parse_expr(child, source)?);
                    }
                }
            }
        }

        let base_expr = base.ok_or_else(|| ParseError::MissingField {
            field: "base".to_string(),
            node_kind: "field_expression".to_string(),
        })?;

        if is_ptr {
            // a->b
            Ok(CExpr::Arrow {
                pointer: Box::new(base_expr),
                field,
            })
        } else {
            // a.b
            Ok(CExpr::Member {
                object: Box::new(base_expr),
                field,
            })
        }
    }

    /// Parse pointer expression (& or *)
    fn parse_pointer_expr(&self, node: Node<'_>, source: &str) -> ParseResult<CExpr> {
        let mut op = None;
        let mut operand = None;

        for i in 0..node.child_count() {
            if let Some(child) = node.child_at(i) {
                match child.kind() {
                    "&" => op = Some(UnaryOp::AddrOf),
                    "*" => op = Some(UnaryOp::Deref),
                    _ => {
                        operand = Some(self.parse_expr(child, source)?);
                    }
                }
            }
        }

        Ok(CExpr::UnaryOp {
            op: op.ok_or_else(|| ParseError::MissingField {
                field: "operator".to_string(),
                node_kind: "pointer_expression".to_string(),
            })?,
            operand: Box::new(operand.ok_or_else(|| ParseError::MissingField {
                field: "operand".to_string(),
                node_kind: "pointer_expression".to_string(),
            })?),
        })
    }

    /// Parse sizeof expression
    fn parse_sizeof_expr(&self, node: Node<'_>, source: &str) -> ParseResult<CExpr> {
        for i in 0..node.child_count() {
            if let Some(child) = node.child_at(i) {
                match child.kind() {
                    "sizeof" | "(" | ")" => {}
                    "type_descriptor" => {
                        let ty = self.parse_type_descriptor(child, source)?;
                        return Ok(CExpr::SizeOf(SizeOfArg::Type(ty)));
                    }
                    "parenthesized_expression" => {
                        // sizeof(expr)
                        if let Some(inner) = child.child_at(1) {
                            let expr = self.parse_expr(inner, source)?;
                            return Ok(CExpr::SizeOf(SizeOfArg::Expr(Box::new(expr))));
                        }
                    }
                    _ => {
                        let expr = self.parse_expr(child, source)?;
                        return Ok(CExpr::SizeOf(SizeOfArg::Expr(Box::new(expr))));
                    }
                }
            }
        }

        Err(ParseError::MissingField {
            field: "operand".to_string(),
            node_kind: "sizeof_expression".to_string(),
        })
    }

    /// Parse `_Alignof` / `alignof` expression (C11 `<stdalign.h>`).
    ///
    /// The standard operand of `_Alignof` is a parenthesized type-name, which
    /// tree-sitter exposes as a `type_descriptor` child. The keyword child is
    /// either `_Alignof` or its `alignof` macro spelling. The result is an
    /// `AlignOf(CType)` node whose alignment the evaluator computes from the
    /// type model (`CType::align`).
    fn parse_alignof_expr(&self, node: Node<'_>, source: &str) -> ParseResult<CExpr> {
        for i in 0..node.child_count() {
            if let Some(child) = node.child_at(i) {
                match child.kind() {
                    "_Alignof" | "alignof" | "__alignof__" | "__alignof" | "(" | ")" => {}
                    "type_descriptor" => {
                        let ty = self.parse_type_descriptor(child, source)?;
                        return Ok(CExpr::AlignOf(ty));
                    }
                    "parenthesized_expression" => {
                        // `_Alignof(expr)` is a constraint violation in standard
                        // C11 (the operand must be a type-name); reject it rather
                        // than silently misinterpreting the operand.
                        return Err(ParseError::Unsupported {
                            line: child.start_position().row + 1,
                            column: child.start_position().column + 1,
                            kind: "alignof of an expression (operand must be a type-name)"
                                .to_string(),
                        });
                    }
                    _ => {
                        return Err(ParseError::Unsupported {
                            line: child.start_position().row + 1,
                            column: child.start_position().column + 1,
                            kind: "alignof of an expression (operand must be a type-name)"
                                .to_string(),
                        });
                    }
                }
            }
        }

        Err(ParseError::MissingField {
            field: "type".to_string(),
            node_kind: "alignof_expression".to_string(),
        })
    }

    /// Parse a comma expression (C11 6.5.17).
    ///
    /// The comma operator is **left-associative** and its value is the value of
    /// the right (last) operand; the left operands are evaluated only for their
    /// side effects. tree-sitter-c models a comma sequence *right-recursively*
    /// — `1, 2, 3` parses as `comma_expression(1, ",", comma_expression(2, ",",
    /// 3))` — so a naïve two-slot parse would either drop operands or build a
    /// right-associative tree. We instead flatten the full operand sequence in
    /// source order and fold it left-associatively, yielding the C-correct
    /// `BinOp(Comma, BinOp(Comma, 1, 2), 3)`.
    fn parse_comma_expr(&self, node: Node<'_>, source: &str) -> ParseResult<CExpr> {
        let mut operands = Vec::new();
        self.collect_comma_operands(node, source, &mut operands)?;

        // Fold the operands left-associatively into a chain of `BinOp(Comma, ..)`
        // nodes. The accumulator holds the left-associative prefix built so far.
        let mut acc: Option<CExpr> = None;
        for operand in operands {
            acc = Some(match acc {
                None => operand,
                Some(left) => CExpr::BinOp {
                    op: BinOp::Comma,
                    left: Box::new(left),
                    right: Box::new(operand),
                },
            });
        }

        // A `comma_expression` node always has at least two operands per the
        // grammar; the `unwrap_or` is a defensive fallback for a degenerate tree.
        Ok(acc.unwrap_or(CExpr::IntLit(0)))
    }

    /// Flatten a (possibly right-recursive) `comma_expression` subtree into its
    /// operand list, in left-to-right source order.
    ///
    /// Non-comma children are parsed as operands; a nested `comma_expression`
    /// child (tree-sitter's right-recursive tail) is descended into rather than
    /// parsed as a single operand, so that `1, 2, 3` flattens to `[1, 2, 3]`
    /// instead of `[1, (2, 3)]`.
    fn collect_comma_operands(
        &self,
        node: Node<'_>,
        source: &str,
        operands: &mut Vec<CExpr>,
    ) -> ParseResult<()> {
        for i in 0..node.child_count() {
            if let Some(child) = node.child_at(i) {
                match child.kind() {
                    "," => {}
                    "comma_expression" => {
                        self.collect_comma_operands(child, source, operands)?;
                    }
                    _ => operands.push(self.parse_expr(child, source)?),
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::expr::{BinOp, CExpr};
    use crate::parser::CParser;
    use crate::stmt::CStmt;

    /// Extract the single returned expression from `int f(void){ return <e>; }`.
    fn parse_returned_expr(src: &str) -> CExpr {
        let mut parser = CParser::new();
        let func = parser
            .parse_function(src)
            .expect("function with a return statement should parse");
        match func.body.as_ref() {
            CStmt::Block(stmts) => match stmts.first() {
                Some(CStmt::Return(Some(expr))) => expr.clone(),
                other => panic!("expected a single return statement, got {other:?}"),
            },
            other => panic!("expected a block body, got {other:?}"),
        }
    }

    fn comma(left: CExpr, right: CExpr) -> CExpr {
        CExpr::BinOp {
            op: BinOp::Comma,
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    #[test]
    fn test_parse_comma_expr_two_operands_builds_binary_comma() {
        // Regression guard: the two-operand case must keep working.
        let expr = parse_returned_expr("int f(void){ return (1, 2); }");
        assert_eq!(expr, comma(CExpr::IntLit(1), CExpr::IntLit(2)));
    }

    #[test]
    fn test_parse_comma_expr_three_operands_is_left_associative() {
        // C11 6.5.17: comma is left-associative, so `1, 2, 3` is `(1, 2), 3`,
        // *not* the right-associative `1, (2, 3)` that tree-sitter's grammar
        // shape would otherwise yield, and no operand may be dropped.
        let expr = parse_returned_expr("int f(void){ return (1, 2, 3); }");
        let expected = comma(comma(CExpr::IntLit(1), CExpr::IntLit(2)), CExpr::IntLit(3));
        assert_eq!(expr, expected);
    }

    #[test]
    fn test_parse_comma_expr_four_operands_is_depth_three_left_chain() {
        // `1, 2, 3, 4` => (((1, 2), 3), 4): a depth-3 left-associative chain.
        let expr = parse_returned_expr("int f(void){ return (1, 2, 3, 4); }");
        let expected = comma(
            comma(comma(CExpr::IntLit(1), CExpr::IntLit(2)), CExpr::IntLit(3)),
            CExpr::IntLit(4),
        );
        assert_eq!(expr, expected);
    }

    #[test]
    fn test_parse_comma_expr_three_operands_preserves_all_operands() {
        // Pin the specific corruption: every operand must survive the parse.
        let expr = parse_returned_expr("int f(void){ return (10, 20, 30); }");
        let leaves = collect_int_leaves(&expr);
        assert_eq!(leaves, vec![10, 20, 30]);
    }

    /// Collect integer-literal leaves left-to-right from a comma chain.
    fn collect_int_leaves(expr: &CExpr) -> Vec<i64> {
        let mut out = Vec::new();
        fn walk(e: &CExpr, out: &mut Vec<i64>) {
            match e {
                CExpr::BinOp {
                    op: BinOp::Comma,
                    left,
                    right,
                } => {
                    walk(left, out);
                    walk(right, out);
                }
                CExpr::IntLit(i) => out.push(*i),
                _ => {}
            }
        }
        walk(expr, &mut out);
        out
    }

    use crate::expr::{Designator, Initializer};
    use crate::types::CType;

    #[test]
    fn test_parse_compound_literal_scalar_int_builds_compound_literal() {
        // C99 6.5.2.5: `(int){42}` is a compound literal of type `int` with a
        // single initializer. Before this fix the dispatcher had no arm for the
        // tree-sitter `compound_literal_expression` node, so it failed to parse.
        let expr = parse_returned_expr("int f(void){ return (int){42}; }");
        match expr {
            CExpr::CompoundLiteral { ty, init } => {
                assert_eq!(ty, CType::int());
                assert_eq!(init, vec![Initializer::Expr(CExpr::IntLit(42))]);
            }
            other => panic!("expected a compound literal, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_compound_literal_struct_designated_keeps_designators() {
        // `(struct P){.x = 1, .y = 2}` must parse with designated initializers.
        let src = "struct P { int x; int y; }; \
                   int f(void){ return (struct P){.x = 1, .y = 2}.x; }";
        let mut parser = CParser::new();
        let func = parser
            .parse_function(src)
            .expect("compound literal with designated inits should parse");
        // The returned expression is `(<compound literal>).x`; reach into the
        // member access to inspect the literal.
        let compound = match func.body.as_ref() {
            CStmt::Block(stmts) => match stmts.first() {
                Some(CStmt::Return(Some(CExpr::Member { object, .. }))) => object.as_ref().clone(),
                other => panic!("expected `return <cl>.x;`, got {other:?}"),
            },
            other => panic!("expected a block body, got {other:?}"),
        };
        match compound {
            CExpr::CompoundLiteral { init, .. } => {
                assert_eq!(init.len(), 2, "both designated initializers must survive");
                assert!(matches!(
                    &init[0],
                    Initializer::Designated { designator: Designator::Field(f), .. } if f == "x"
                ));
                assert!(matches!(
                    &init[1],
                    Initializer::Designated { designator: Designator::Field(f), .. } if f == "y"
                ));
            }
            other => panic!("expected a compound literal, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_compound_literal_unsized_array_infers_length_from_inits() {
        // `(int[]){1, 2, 3}` is an array compound literal whose bound is
        // inferred from the initializer count (C99 6.7.9p22 applied to 6.5.2.5).
        let src = "int f(void){ return (int[]){1, 2, 3}[0]; }";
        let mut parser = CParser::new();
        let func = parser
            .parse_function(src)
            .expect("array compound literal should parse");
        let compound = match func.body.as_ref() {
            CStmt::Block(stmts) => match stmts.first() {
                Some(CStmt::Return(Some(CExpr::Index { array, .. }))) => array.as_ref().clone(),
                other => panic!("expected `return <cl>[0];`, got {other:?}"),
            },
            other => panic!("expected a block body, got {other:?}"),
        };
        match compound {
            CExpr::CompoundLiteral { ty, init } => {
                assert_eq!(ty, CType::Array(Box::new(CType::int()), 3));
                assert_eq!(init.len(), 3);
            }
            other => panic!("expected a compound literal, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_compound_literal_sized_array_keeps_explicit_bound() {
        // An explicit bound `(int[2]){...}` is preserved, not overwritten by the
        // initializer count.
        let src = "int f(void){ return (int[2]){7, 8}[1]; }";
        let mut parser = CParser::new();
        let func = parser
            .parse_function(src)
            .expect("sized array compound literal should parse");
        let compound = match func.body.as_ref() {
            CStmt::Block(stmts) => match stmts.first() {
                Some(CStmt::Return(Some(CExpr::Index { array, .. }))) => array.as_ref().clone(),
                other => panic!("expected `return <cl>[1];`, got {other:?}"),
            },
            other => panic!("expected a block body, got {other:?}"),
        };
        match compound {
            CExpr::CompoundLiteral { ty, .. } => {
                assert_eq!(ty, CType::Array(Box::new(CType::int()), 2));
            }
            other => panic!("expected a compound literal, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_compound_literal_nested_struct_with_array_field_parses() {
        // A nested compound literal: an outer struct initializer containing an
        // inner brace list for an array field. The whole thing must parse.
        let src = "struct V { int xs[2]; }; \
                   int f(void){ return (struct V){ .xs = {1, 2} }.xs[1]; }";
        let mut parser = CParser::new();
        let func = parser
            .parse_function(src)
            .expect("nested compound literal should parse");
        let compound = match func.body.as_ref() {
            CStmt::Block(stmts) => match stmts.first() {
                // `return (<cl>.xs)[1];` -> Index{ array: Member{ object: <cl> }}
                Some(CStmt::Return(Some(CExpr::Index { array, .. }))) => match array.as_ref() {
                    CExpr::Member { object, .. } => object.as_ref().clone(),
                    other => panic!("expected `<cl>.xs` inside index, got {other:?}"),
                },
                other => panic!("expected `return <cl>.xs[1];`, got {other:?}"),
            },
            other => panic!("expected a block body, got {other:?}"),
        };
        match compound {
            CExpr::CompoundLiteral { init, .. } => {
                assert_eq!(init.len(), 1, "the single `.xs = {{..}}` entry");
                match &init[0] {
                    Initializer::Designated {
                        designator: Designator::Field(f),
                        init,
                    } => {
                        assert_eq!(f, "xs");
                        assert!(
                            matches!(init.as_ref(), Initializer::List(items) if items.len() == 2),
                            "the array field's nested brace list must carry both elements",
                        );
                    }
                    other => panic!("expected `.xs = {{..}}`, got {other:?}"),
                }
            }
            other => panic!("expected a compound literal, got {other:?}"),
        }
    }
}

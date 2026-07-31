// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Function and declarator parsing.

use super::common::{find_nested_identifier, node_text, parse_storage_class, pointer_qualifiers};
use super::{CParser, NodeExt, ParseResult};
use crate::stmt::{CStmt, FuncDef, FuncParam, StorageClass};
use crate::types::CType;
use tree_sitter::Node;

impl CParser {
    /// Parse a function definition node
    pub(super) fn parse_function_node(&self, node: Node<'_>, source: &str) -> ParseResult<FuncDef> {
        let mut return_type = CType::Void;
        let mut name = String::new();
        let mut params = Vec::new();
        let mut body = CStmt::Empty;
        let mut storage = StorageClass::Auto;
        let mut variadic = false;
        let mut is_noreturn = false;

        for i in 0..node.child_count() {
            if let Some(child) = node.child_at(i) {
                match child.kind() {
                    // Storage class specifiers
                    "storage_class_specifier" => {
                        let text = node_text(child, source);
                        storage = parse_storage_class(&text);
                    }
                    // Type qualifiers; `_Noreturn` (C11 6.7.4) — and the
                    // `<stdnoreturn.h>` `noreturn` convenience macro — are
                    // surfaced by tree-sitter-c as a `type_qualifier` node.
                    "type_qualifier" => {
                        let text = node_text(child, source);
                        if text.trim() == "_Noreturn" || text.trim() == "noreturn" {
                            is_noreturn = true;
                        }
                    }
                    // Type specifiers
                    "primitive_type"
                    | "type_identifier"
                    | "sized_type_specifier"
                    | "struct_specifier"
                    | "union_specifier"
                    | "enum_specifier" => {
                        return_type = self.parse_type_node(child, source)?;
                    }
                    // Declarator (function name and parameters)
                    "function_declarator" => {
                        (name, params, variadic) = self.parse_func_declarator(child, source)?;
                    }
                    "pointer_declarator" => {
                        // Function returning pointer
                        if let Some(inner) = child.child_by_field_name("declarator") {
                            if inner.kind() == "function_declarator" {
                                (name, params, variadic) =
                                    self.parse_func_declarator(inner, source)?;
                                return_type = CType::Pointer(Box::new(return_type));
                            }
                        }
                    }
                    // Function body
                    "compound_statement" => {
                        body = self.parse_compound_stmt(child, source)?;
                    }
                    _ => {}
                }
            }
        }

        Ok(FuncDef {
            name,
            return_type,
            params,
            variadic,
            storage,
            is_noreturn,
            body: Box::new(body),
        })
    }

    /// Parse function declarator (name and parameters)
    fn parse_func_declarator(
        &self,
        node: Node<'_>,
        source: &str,
    ) -> ParseResult<(String, Vec<FuncParam>, bool)> {
        let mut name = String::new();
        let mut params = Vec::new();
        let mut variadic = false;

        for i in 0..node.child_count() {
            if let Some(child) = node.child_at(i) {
                match child.kind() {
                    "identifier" | "field_identifier" => {
                        name = node_text(child, source);
                    }
                    "parenthesized_declarator" => {
                        // Handle (*func)(...) patterns
                        if let Some(inner) = find_nested_identifier(child, source, &["identifier"])
                        {
                            name = inner;
                        }
                    }
                    "parameter_list" => {
                        (params, variadic) = self.parse_param_list(child, source)?;
                    }
                    _ => {}
                }
            }
        }

        Ok((name, params, variadic))
    }

    /// Parse parameter list
    fn parse_param_list(
        &self,
        node: Node<'_>,
        source: &str,
    ) -> ParseResult<(Vec<FuncParam>, bool)> {
        let mut params = Vec::new();
        let mut variadic = false;

        for i in 0..node.child_count() {
            if let Some(child) = node.child_at(i) {
                match child.kind() {
                    "parameter_declaration" => {
                        params.push(self.parse_param_decl(child, source)?);
                    }
                    "variadic_parameter" | "..." => {
                        variadic = true;
                    }
                    _ => {}
                }
            }
        }

        Ok((params, variadic))
    }

    /// Parse a parameter declaration
    fn parse_param_decl(&self, node: Node<'_>, source: &str) -> ParseResult<FuncParam> {
        let mut ty = CType::Void;
        let mut name = String::new();

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
                    "identifier" => {
                        name = node_text(child, source);
                    }
                    "pointer_declarator" => {
                        // A `type_qualifier` after the `*` (e.g. `int * restrict p`)
                        // qualifies the pointer itself (C99 6.7.3).
                        let quals = pointer_qualifiers(child, source);
                        ty = CType::with_qualifiers(
                            CType::Pointer(Box::new(ty)),
                            quals.is_const,
                            quals.is_volatile,
                            quals.is_restrict,
                        );
                        if let Some(inner_name) =
                            find_nested_identifier(child, source, &["identifier"])
                        {
                            name = inner_name;
                        }
                    }
                    "abstract_pointer_declarator" => {
                        let quals = pointer_qualifiers(child, source);
                        ty = CType::with_qualifiers(
                            CType::Pointer(Box::new(ty)),
                            quals.is_const,
                            quals.is_volatile,
                            quals.is_restrict,
                        );
                    }
                    "array_declarator" => {
                        // Handle array parameters (decay to pointers in function params)
                        ty = CType::Pointer(Box::new(ty));
                        if let Some(inner_name) =
                            find_nested_identifier(child, source, &["identifier"])
                        {
                            name = inner_name;
                        }
                    }
                    _ => {}
                }
            }
        }

        Ok(FuncParam { name, ty })
    }

    /// Parse array declarator
    pub(super) fn parse_array_declarator(
        &self,
        node: Node<'_>,
        source: &str,
    ) -> ParseResult<Option<(String, usize)>> {
        let (name, dim) = self.parse_array_declarator_dim(node, source)?;
        if name.is_empty() {
            Ok(None)
        } else {
            Ok(Some((name, dim.unwrap_or(0))))
        }
    }

    /// Parse an `array_declarator`, returning its declared name and the array
    /// bound if one was written.
    ///
    /// A missing bound (`int data[]`, i.e. an `array_declarator` with no
    /// dimension expression) yields `None`, which the caller distinguishes
    /// from an explicit zero (`int data[0]`, which yields `Some(0)`). For a
    /// struct's last member, a missing bound denotes a flexible array member
    /// (C99 6.7.2.1p18).
    pub(super) fn parse_array_declarator_dim(
        &self,
        node: Node<'_>,
        source: &str,
    ) -> ParseResult<(String, Option<usize>)> {
        let mut name = String::new();
        let mut dim: Option<usize> = None;

        for i in 0..node.child_count() {
            if let Some(child) = node.child_at(i) {
                match child.kind() {
                    "identifier" | "field_identifier" => {
                        name = node_text(child, source);
                    }
                    "number_literal" => {
                        let text = node_text(child, source);
                        dim = Some(self.parse_int_literal(&text)? as usize);
                    }
                    _ => {}
                }
            }
        }

        Ok((name, dim))
    }
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Type parsing: primitives, structs, unions, enums, and fields.

use super::common::{find_nested_identifier, node_text, pointer_qualifiers};
use super::{CParser, NodeExt, ParseResult};
use crate::types::{CType, FloatKind, IntKind, Signedness, StructField};
use tree_sitter::Node;

impl CParser {
    /// Parse a type node
    pub(super) fn parse_type_node(&self, node: Node, source: &str) -> ParseResult<CType> {
        match node.kind() {
            "primitive_type" => {
                let text = node_text(node, source);
                self.parse_primitive_type(&text)
            }
            "type_identifier" => {
                let name = node_text(node, source);
                // Common typedefs
                match name.as_str() {
                    "int8_t" => Ok(CType::Int(IntKind::Char, Signedness::Signed)),
                    "uint8_t" => Ok(CType::Int(IntKind::Char, Signedness::Unsigned)),
                    "int16_t" => Ok(CType::Int(IntKind::Short, Signedness::Signed)),
                    "uint16_t" => Ok(CType::Int(IntKind::Short, Signedness::Unsigned)),
                    "int32_t" => Ok(CType::Int(IntKind::Int, Signedness::Signed)),
                    "uint32_t" => Ok(CType::Int(IntKind::Int, Signedness::Unsigned)),
                    "int64_t" => Ok(CType::Int(IntKind::LongLong, Signedness::Signed)),
                    "uint64_t" => Ok(CType::Int(IntKind::LongLong, Signedness::Unsigned)),
                    "size_t" | "uintptr_t" => Ok(CType::Int(IntKind::Long, Signedness::Unsigned)),
                    "ssize_t" | "ptrdiff_t" | "intptr_t" => {
                        Ok(CType::Int(IntKind::Long, Signedness::Signed))
                    }
                    "bool" | "_Bool" => Ok(CType::Int(IntKind::Bool, Signedness::Unsigned)),
                    _ => Ok(CType::TypeDef(name)),
                }
            }
            "sized_type_specifier" => {
                let text = node_text(node, source);
                self.parse_sized_type(&text)
            }
            "struct_specifier" => self.parse_struct_node(node, source),
            "union_specifier" => self.parse_union_node(node, source),
            "enum_specifier" => self.parse_enum_node(node, source),
            _ => Ok(CType::TypeDef(node_text(node, source))),
        }
    }

    /// Parse primitive type
    fn parse_primitive_type(&self, text: &str) -> ParseResult<CType> {
        match text {
            "void" => Ok(CType::Void),
            "char" => Ok(CType::Int(IntKind::Char, Signedness::Signed)),
            "short" => Ok(CType::Int(IntKind::Short, Signedness::Signed)),
            "int" => Ok(CType::Int(IntKind::Int, Signedness::Signed)),
            "long" => Ok(CType::Int(IntKind::Long, Signedness::Signed)),
            "float" => Ok(CType::Float(FloatKind::Float)),
            "double" => Ok(CType::Float(FloatKind::Double)),
            "_Bool" | "bool" => Ok(CType::Int(IntKind::Bool, Signedness::Unsigned)),
            _ => Ok(CType::TypeDef(text.to_string())),
        }
    }

    /// Parse sized type specifier (unsigned int, long long, etc.)
    fn parse_sized_type(&self, text: &str) -> ParseResult<CType> {
        let text = text.trim();
        let parts: Vec<&str> = text.split_whitespace().collect();

        let mut signed = true;
        let mut kind = IntKind::Int;

        for part in parts {
            match part {
                "unsigned" => signed = false,
                "signed" => signed = true,
                "char" => kind = IntKind::Char,
                "short" => kind = IntKind::Short,
                "long" => {
                    kind = if kind == IntKind::Long {
                        IntKind::LongLong
                    } else {
                        IntKind::Long
                    };
                }
                _ => {} // default and unknown
            }
        }

        let signedness = if signed {
            Signedness::Signed
        } else {
            Signedness::Unsigned
        };
        Ok(CType::Int(kind, signedness))
    }

    /// Parse struct specifier
    fn parse_struct_node(&self, node: Node, source: &str) -> ParseResult<CType> {
        let mut name = None;
        let mut fields = Vec::new();

        for i in 0..node.child_count() {
            if let Some(child) = node.child_at(i) {
                match child.kind() {
                    "type_identifier" => {
                        name = Some(node_text(child, source));
                    }
                    "field_declaration_list" => {
                        fields = self.parse_field_list(child, source)?;
                    }
                    _ => {}
                }
            }
        }

        let ty = CType::Struct { name, fields };
        // Enforce C99 6.7.2.1p18 flexible-array-member rules: a `T[]` member
        // must be the last member of a struct that has at least one other
        // member.
        ty.validate_flexible_array_member()
            .map_err(|e| super::ParseError::TypeError {
                message: e.to_string(),
            })?;
        Ok(ty)
    }

    /// Parse union specifier
    fn parse_union_node(&self, node: Node, source: &str) -> ParseResult<CType> {
        let mut name = None;
        let mut fields = Vec::new();

        for i in 0..node.child_count() {
            if let Some(child) = node.child_at(i) {
                match child.kind() {
                    "type_identifier" => {
                        name = Some(node_text(child, source));
                    }
                    "field_declaration_list" => {
                        fields = self.parse_field_list(child, source)?;
                    }
                    _ => {}
                }
            }
        }

        let ty = CType::Union { name, fields };
        // A union may not contain a flexible array member (C99 6.7.2.1p18).
        ty.validate_flexible_array_member()
            .map_err(|e| super::ParseError::TypeError {
                message: e.to_string(),
            })?;
        Ok(ty)
    }

    /// Parse enum specifier
    fn parse_enum_node(&self, node: Node, source: &str) -> ParseResult<CType> {
        let mut name = None;
        let mut variants = Vec::new();
        let mut current_value: i64 = 0;

        for i in 0..node.child_count() {
            if let Some(child) = node.child_at(i) {
                match child.kind() {
                    "type_identifier" => {
                        name = Some(node_text(child, source));
                    }
                    "enumerator_list" => {
                        for j in 0..child.child_count() {
                            if let Some(enum_child) = child.child_at(j) {
                                if enum_child.kind() == "enumerator" {
                                    let (variant_name, value) =
                                        self.parse_enumerator(enum_child, source, current_value)?;
                                    current_value = value + 1;
                                    variants.push((variant_name, value));
                                }
                            }
                        }
                    }
                    _ => {}
                }
            }
        }

        Ok(CType::Enum { name, variants })
    }

    /// Parse an enumerator
    fn parse_enumerator(
        &self,
        node: Node,
        source: &str,
        default_value: i64,
    ) -> ParseResult<(String, i64)> {
        let mut name = String::new();
        let mut value = default_value;

        for i in 0..node.child_count() {
            if let Some(child) = node.child_at(i) {
                match child.kind() {
                    "identifier" => {
                        name = node_text(child, source);
                    }
                    "number_literal" => {
                        let text = node_text(child, source);
                        value = self.parse_int_literal(&text)?;
                    }
                    _ => {}
                }
            }
        }

        Ok((name, value))
    }

    /// Parse field declaration list
    fn parse_field_list(&self, node: Node, source: &str) -> ParseResult<Vec<StructField>> {
        let mut fields = Vec::new();

        for i in 0..node.child_count() {
            if let Some(child) = node.child_at(i) {
                if child.kind() == "field_declaration" {
                    if let Some(field) = self.parse_field_decl(child, source)? {
                        fields.push(field);
                    }
                }
            }
        }

        Ok(fields)
    }

    /// Parse a field declaration
    fn parse_field_decl(&self, node: Node, source: &str) -> ParseResult<Option<StructField>> {
        let mut ty = CType::Void;
        let mut name = String::new();
        // Bit-field width, if a `: width` clause is present. `Some(0)` denotes
        // an (unnamed) zero-width separator.
        let mut bit_width: Option<usize> = None;

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
                    "field_identifier" => {
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
                            find_nested_identifier(child, source, &["field_identifier"])
                        {
                            name = inner_name;
                        }
                    }
                    "array_declarator" => {
                        let (array_name, dim) = self.parse_array_declarator_dim(child, source)?;
                        if !array_name.is_empty() {
                            name = array_name;
                            // A struct member written `T arr[]` (no bound) is a
                            // flexible array member / incomplete array (C99
                            // 6.7.2.1p18); `T arr[0]` is a (zero-length) fixed
                            // array. The two are distinguished by whether a
                            // dimension expression was present.
                            ty = match dim {
                                Some(size) => CType::Array(Box::new(ty), size),
                                None => CType::IncompleteArray(Box::new(ty)),
                            };
                        }
                    }
                    // `unsigned a : 3;` — tree-sitter-c wraps the `: width`
                    // suffix in a `bitfield_clause` node holding the width
                    // expression (typically a `number_literal`).
                    "bitfield_clause" => {
                        bit_width = Some(self.parse_bitfield_width(child, source)?);
                    }
                    _ => {}
                }
            }
        }

        match (name.is_empty(), bit_width) {
            // An unnamed zero-width bit-field (`unsigned : 0;`) is a layout
            // directive that forces the next bit-field to a new storage unit,
            // so it must be preserved in the field list even though it has no
            // name and occupies no addressable storage.
            (true, Some(0)) => Ok(Some(StructField {
                name: String::new(),
                ty,
                bit_width: Some(0),
            })),
            // An unnamed, non-zero-width bit-field reserves padding bits but
            // cannot be referenced; treat it as a zero-width-style separator so
            // following named bit-fields still pack after it.
            (true, Some(_)) => Ok(None),
            (true, None) => Ok(None),
            (false, _) => Ok(Some(StructField {
                name,
                ty,
                bit_width,
            })),
        }
    }

    /// Parse the width of a `bitfield_clause` (`: expr`) into a bit count.
    fn parse_bitfield_width(&self, node: Node, source: &str) -> ParseResult<usize> {
        for i in 0..node.child_count() {
            if let Some(child) = node.child_at(i) {
                if child.kind() == "number_literal" {
                    let text = node_text(child, source);
                    let value = self.parse_int_literal(&text)?;
                    return usize::try_from(value).map_err(|_| super::ParseError::SyntaxError {
                        line: node.start_position().row + 1,
                        column: node.start_position().column + 1,
                        message: format!("invalid bit-field width: {value}"),
                    });
                }
            }
        }
        Err(super::ParseError::SyntaxError {
            line: node.start_position().row + 1,
            column: node.start_position().column + 1,
            message: "bit-field width is not an integer constant".to_string(),
        })
    }
}

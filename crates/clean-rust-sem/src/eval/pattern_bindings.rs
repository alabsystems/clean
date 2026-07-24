// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::Interpreter;
use crate::expr::{EnumPatternPayload, Pattern};
use crate::stmt::{EnumVariantType, PatternBindings, TypeDef};
use crate::types::RustType;
use crate::values::{EnumPayload, Value};
use std::collections::HashMap;

enum ProjectedEnumPayloadTypes {
    Unit,
    Tuple(Vec<RustType>),
    Struct(Vec<(String, RustType)>),
}

impl Interpreter {
    pub(super) fn collect_typed_pattern_bindings(
        &self,
        pattern: &Pattern,
        value: &Value,
        type_hint: Option<&RustType>,
    ) -> Option<PatternBindings> {
        let mut bindings = PatternBindings::new();

        match pattern {
            Pattern::Wildcard => Some(bindings),

            Pattern::Binding {
                name,
                mutable,
                subpattern,
            } => {
                if let Some(sub) = subpattern {
                    let sub_bindings =
                        self.collect_typed_pattern_bindings(sub, value, type_hint)?;
                    bindings.merge(sub_bindings);
                }
                bindings.add_typed(name.clone(), value.clone(), *mutable, type_hint.cloned());
                Some(bindings)
            }

            Pattern::Literal(lit) => {
                if value == lit {
                    Some(bindings)
                } else {
                    None
                }
            }

            Pattern::Tuple(patterns) => self.collect_tuple_pattern_bindings(
                patterns,
                value,
                bindings,
                Self::tuple_element_types(type_hint),
            ),

            Pattern::Struct {
                name,
                fields,
                rest: _,
            } => self.collect_struct_pattern_bindings(name, fields, value, bindings, type_hint),

            Pattern::EnumVariant {
                enum_name,
                variant,
                payload,
            } => self.collect_enum_pattern_bindings(
                enum_name, variant, payload, value, bindings, type_hint,
            ),

            Pattern::Or(patterns) => patterns
                .iter()
                .find_map(|pattern| self.collect_typed_pattern_bindings(pattern, value, type_hint)),

            Pattern::Range {
                start,
                end,
                inclusive,
            } => {
                let ok = match (start, end, value) {
                    (
                        Value::Uint { value: s, ty: ty_s },
                        Value::Uint { value: e, ty: ty_e },
                        Value::Uint { value: v, ty: ty_v },
                    ) if ty_s == ty_e && ty_s == ty_v => {
                        if *inclusive {
                            v >= s && v <= e
                        } else {
                            v >= s && v < e
                        }
                    }
                    (
                        Value::Int { value: s, ty: ty_s },
                        Value::Int { value: e, ty: ty_e },
                        Value::Int { value: v, ty: ty_v },
                    ) if ty_s == ty_e && ty_s == ty_v => {
                        if *inclusive {
                            v >= s && v <= e
                        } else {
                            v >= s && v < e
                        }
                    }
                    (Value::Char(s), Value::Char(e), Value::Char(v)) => {
                        if *inclusive {
                            v >= s && v <= e
                        } else {
                            v >= s && v < e
                        }
                    }
                    _ => return None,
                };
                if ok {
                    Some(bindings)
                } else {
                    None
                }
            }

            Pattern::Ref {
                mutability: _,
                pattern,
            } => {
                let peeled_hint = match type_hint {
                    Some(RustType::Reference { inner, .. }) => Some(inner.as_ref()),
                    _ => type_hint,
                };
                let inner_value = match value {
                    Value::Reference {
                        referent: Some(referent),
                        ..
                    } => referent.as_ref(),
                    _ => value,
                };
                self.collect_typed_pattern_bindings(pattern, inner_value, peeled_hint)
            }

            Pattern::Slice(patterns) => self.collect_slice_pattern_bindings(
                patterns,
                value,
                bindings,
                Self::array_element_type(type_hint),
            ),

            Pattern::Rest => Some(bindings),
        }
    }

    fn collect_tuple_pattern_bindings(
        &self,
        patterns: &[Pattern],
        value: &Value,
        mut bindings: PatternBindings,
        element_types: Option<&[RustType]>,
    ) -> Option<PatternBindings> {
        let Value::Tuple(values) = value else {
            return None;
        };
        if patterns.len() != values.len() {
            return None;
        }
        for (index, (pattern, value)) in patterns.iter().zip(values.iter()).enumerate() {
            let hint = element_types.and_then(|types| types.get(index));
            let sub_bindings = self.collect_typed_pattern_bindings(pattern, value, hint)?;
            bindings.merge(sub_bindings);
        }
        Some(bindings)
    }

    fn collect_slice_pattern_bindings(
        &self,
        patterns: &[Pattern],
        value: &Value,
        mut bindings: PatternBindings,
        element_type: Option<&RustType>,
    ) -> Option<PatternBindings> {
        let Value::Array(values) = value else {
            return None;
        };
        let rest_pos = patterns
            .iter()
            .position(|pattern| matches!(pattern, Pattern::Rest));
        match rest_pos {
            None => {
                if patterns.len() != values.len() {
                    return None;
                }
                for (pattern, value) in patterns.iter().zip(values.iter()) {
                    let sub_bindings =
                        self.collect_typed_pattern_bindings(pattern, value, element_type)?;
                    bindings.merge(sub_bindings);
                }
            }
            Some(pos) => {
                let before = &patterns[..pos];
                let after = &patterns[pos + 1..];
                let min_len = before.len() + after.len();
                if values.len() < min_len {
                    return None;
                }
                for (pattern, value) in before.iter().zip(values.iter()) {
                    let sub_bindings =
                        self.collect_typed_pattern_bindings(pattern, value, element_type)?;
                    bindings.merge(sub_bindings);
                }
                let suffix_start = values.len() - after.len();
                for (pattern, value) in after.iter().zip(values[suffix_start..].iter()) {
                    let sub_bindings =
                        self.collect_typed_pattern_bindings(pattern, value, element_type)?;
                    bindings.merge(sub_bindings);
                }
            }
        }
        Some(bindings)
    }

    fn collect_struct_pattern_bindings(
        &self,
        expected_name: &str,
        fields: &[(String, Pattern)],
        value: &Value,
        mut bindings: PatternBindings,
        type_hint: Option<&RustType>,
    ) -> Option<PatternBindings> {
        let Value::Struct {
            name,
            fields: struct_fields,
        } = value
        else {
            return None;
        };
        if name != expected_name {
            return None;
        }

        let field_types = self.project_struct_field_types(expected_name, type_hint);
        for (field_name, field_pattern) in fields {
            let field_value = struct_fields.get(field_name)?;
            let field_hint = field_types.as_ref().and_then(|types| {
                types
                    .iter()
                    .find(|(name, _)| name == field_name)
                    .map(|(_, ty)| ty)
            });
            let sub_bindings =
                self.collect_typed_pattern_bindings(field_pattern, field_value, field_hint)?;
            bindings.merge(sub_bindings);
        }
        Some(bindings)
    }

    fn collect_enum_pattern_bindings(
        &self,
        expected_enum: &str,
        expected_variant: &str,
        payload_pattern: &EnumPatternPayload,
        value: &Value,
        mut bindings: PatternBindings,
        type_hint: Option<&RustType>,
    ) -> Option<PatternBindings> {
        let Value::Enum {
            name,
            variant,
            payload,
        } = value
        else {
            return None;
        };
        if name != expected_enum || variant != expected_variant {
            return None;
        }

        let payload_types =
            self.project_enum_variant_payload_types(expected_enum, expected_variant, type_hint);

        match (payload_pattern, payload.as_ref()) {
            (EnumPatternPayload::Unit, EnumPayload::Unit) => Some(bindings),
            (EnumPatternPayload::Tuple(patterns), EnumPayload::Tuple(values)) => {
                if patterns.len() != values.len() {
                    return None;
                }
                let tuple_types = match payload_types.as_ref() {
                    Some(ProjectedEnumPayloadTypes::Tuple(types)) => Some(types.as_slice()),
                    _ => None,
                };
                for (index, (pattern, value)) in patterns.iter().zip(values.iter()).enumerate() {
                    let hint = tuple_types.and_then(|types| types.get(index));
                    let sub_bindings = self.collect_typed_pattern_bindings(pattern, value, hint)?;
                    bindings.merge(sub_bindings);
                }
                Some(bindings)
            }
            (EnumPatternPayload::Struct(patterns), EnumPayload::Struct(fields)) => {
                let struct_types = match payload_types.as_ref() {
                    Some(ProjectedEnumPayloadTypes::Struct(types)) => Some(types),
                    _ => None,
                };
                for (field_name, field_pattern) in patterns {
                    let field_value = fields.get(field_name)?;
                    let field_hint = struct_types.and_then(|types| {
                        types
                            .iter()
                            .find(|(name, _)| name == field_name)
                            .map(|(_, ty)| ty)
                    });
                    let sub_bindings = self.collect_typed_pattern_bindings(
                        field_pattern,
                        field_value,
                        field_hint,
                    )?;
                    bindings.merge(sub_bindings);
                }
                Some(bindings)
            }
            _ => None,
        }
    }

    fn project_struct_field_types(
        &self,
        struct_name: &str,
        type_hint: Option<&RustType>,
    ) -> Option<Vec<(String, RustType)>> {
        let Some(RustType::Named {
            name, type_args, ..
        }) = type_hint
        else {
            return None;
        };
        if name != struct_name {
            return None;
        }
        let TypeDef::Struct {
            fields,
            type_params,
            ..
        } = self.ctx.get_type(name)?
        else {
            return None;
        };
        Self::substitute_named_fields(fields, type_params, type_args)
    }

    fn project_enum_variant_payload_types(
        &self,
        enum_name: &str,
        variant_name: &str,
        type_hint: Option<&RustType>,
    ) -> Option<ProjectedEnumPayloadTypes> {
        let Some(RustType::Named {
            name, type_args, ..
        }) = type_hint
        else {
            return None;
        };
        if name != enum_name {
            return None;
        }
        let TypeDef::Enum {
            variants,
            type_params,
            ..
        } = self.ctx.get_type(name)?
        else {
            return None;
        };
        let variant = variants
            .iter()
            .find(|variant| variant.name == variant_name)?;
        let subst = Self::type_param_subst(type_params, type_args)?;
        match &variant.payload {
            EnumVariantType::Unit => Some(ProjectedEnumPayloadTypes::Unit),
            EnumVariantType::Tuple(types) => Some(ProjectedEnumPayloadTypes::Tuple(
                types
                    .iter()
                    .map(|ty| ty.substitute_type_params(&subst))
                    .collect(),
            )),
            EnumVariantType::Struct(fields) => Some(ProjectedEnumPayloadTypes::Struct(
                fields
                    .iter()
                    .map(|(name, ty)| (name.clone(), ty.substitute_type_params(&subst)))
                    .collect(),
            )),
        }
    }

    fn substitute_named_fields(
        fields: &[(String, RustType)],
        type_params: &[crate::types::TypeParamDef],
        type_args: &[RustType],
    ) -> Option<Vec<(String, RustType)>> {
        let subst = Self::type_param_subst(type_params, type_args)?;
        Some(
            fields
                .iter()
                .map(|(name, ty)| (name.clone(), ty.substitute_type_params(&subst)))
                .collect(),
        )
    }

    fn type_param_subst(
        type_params: &[crate::types::TypeParamDef],
        type_args: &[RustType],
    ) -> Option<HashMap<u32, RustType>> {
        if type_params.is_empty() {
            return Some(HashMap::new());
        }
        RustType::build_type_param_subst(type_params, type_args)
    }

    fn tuple_element_types(type_hint: Option<&RustType>) -> Option<&[RustType]> {
        match type_hint {
            Some(RustType::Tuple(types)) => Some(types.as_slice()),
            _ => None,
        }
    }

    fn array_element_type(type_hint: Option<&RustType>) -> Option<&RustType> {
        match type_hint {
            Some(RustType::Array { element, .. }) => Some(element.as_ref()),
            _ => None,
        }
    }
}

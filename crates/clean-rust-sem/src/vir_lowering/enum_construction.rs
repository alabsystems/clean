// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Enum-constructor operand lowering helpers.

use super::context::FunctionLoweringContext;
use super::{EnumPayloadInfo, VirLoweringError};
use crate::expr::EnumVariantPayload;
use crate::vir::Operand;

impl<'a> FunctionLoweringContext<'a> {
    pub(super) fn enum_constructor_operands(
        &mut self,
        payload_info: &EnumPayloadInfo,
        payload: &EnumVariantPayload,
        enum_name: &str,
        variant: &str,
    ) -> Result<Vec<Operand>, VirLoweringError> {
        match (payload_info, payload) {
            (EnumPayloadInfo::Unit, EnumVariantPayload::Unit) => Ok(Vec::new()),
            (EnumPayloadInfo::Tuple(expected), EnumVariantPayload::Tuple(values)) => {
                if expected.len() != values.len() {
                    return Err(VirLoweringError::Unsupported {
                        context: "enum constructor",
                        detail: format!(
                            "tuple variant `{enum_name}::{variant}` expects {} fields, got {}",
                            expected.len(),
                            values.len()
                        ),
                    });
                }
                self.materialize_operands_as(
                    values
                        .iter()
                        .zip(expected.iter())
                        .map(|(value, expected_ty)| (value, Some(expected_ty))),
                )
            }
            (
                EnumPayloadInfo::Struct {
                    fields: expected_fields,
                    ..
                },
                EnumVariantPayload::Struct(actual_fields),
            ) => {
                for (field_name, _) in actual_fields {
                    if !expected_fields
                        .iter()
                        .any(|(expected_name, _)| expected_name == field_name)
                    {
                        return Err(VirLoweringError::Unsupported {
                            context: "enum constructor",
                            detail: format!(
                                "struct variant `{enum_name}::{variant}` has no field `{field_name}`"
                            ),
                        });
                    }
                }
                let mut operands = Vec::with_capacity(expected_fields.len());
                for (field_name, expected_ty) in expected_fields {
                    if self.terminated {
                        break;
                    }
                    let field_expr = actual_fields
                        .iter()
                        .find_map(|(actual_name, expr)| (actual_name == field_name).then_some(expr))
                        .ok_or_else(|| VirLoweringError::Unsupported {
                            context: "enum constructor",
                            detail: format!(
                                "struct variant `{enum_name}::{variant}` is missing field `{field_name}`"
                            ),
                        })?;
                    operands.push(self.materialize_operand_as(field_expr, Some(expected_ty))?);
                }
                Ok(operands)
            }
            (EnumPayloadInfo::Unit, other) => Err(VirLoweringError::Unsupported {
                context: "enum constructor",
                detail: format!(
                    "unit variant `{enum_name}::{variant}` cannot be constructed with `{other:?}`"
                ),
            }),
            (EnumPayloadInfo::Tuple(_), other) => Err(VirLoweringError::Unsupported {
                context: "enum constructor",
                detail: format!(
                    "tuple variant `{enum_name}::{variant}` requires tuple payload, got `{other:?}`"
                ),
            }),
            (EnumPayloadInfo::Struct { .. }, other) => Err(VirLoweringError::Unsupported {
                context: "enum constructor",
                detail: format!(
                    "struct variant `{enum_name}::{variant}` requires named fields, got `{other:?}`"
                ),
            }),
        }
    }
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Enum constructor and pattern metadata helpers for VIR lowering.

use super::context::FunctionLoweringContext;
use super::pattern_binding::tuple_field_place;
use super::type_helpers::nominal_type_name;
use super::{EnumPayloadInfo, EnumVariantInfo, VirLoweringError};
use crate::expr::{EnumPatternPayload, EnumVariantPayload};
use crate::ownership::Place;
use crate::types::{Mutability, RustType, UintType};
use crate::vir::{
    AggregateKind, BasicBlockId, Operand, Rvalue, Stmt as VirStmt, SwitchTargets, Term,
};

impl<'a> FunctionLoweringContext<'a> {
    pub(super) fn lower_enum_variant_expr(
        &mut self,
        destination: Place,
        enum_name: &str,
        variant: &str,
        payload: &EnumVariantPayload,
    ) -> Result<(), VirLoweringError> {
        let destination_ty = self.place_type(&destination)?;
        let info = self.enum_variant_info_for_type(&destination_ty, enum_name, variant)?;

        let operands =
            self.enum_constructor_operands(&info.payload, payload, enum_name, variant)?;
        if self.terminated {
            return Ok(());
        }

        self.emit(VirStmt::Assign {
            place: destination,
            rvalue: Rvalue::Aggregate {
                kind: AggregateKind::Adt {
                    name: enum_name.to_string(),
                    variant_index: info.variant_index,
                },
                operands,
            },
        });
        Ok(())
    }

    pub(super) fn enum_variant_info_for_type(
        &self,
        enum_ty: &RustType,
        enum_name: &str,
        variant: &str,
    ) -> Result<EnumVariantInfo, VirLoweringError> {
        let actual_enum =
            nominal_type_name(enum_ty).ok_or_else(|| VirLoweringError::MissingType {
                context: format!(
                    "enum type for `{enum_name}::{variant}` in `{}`",
                    self.function_name
                ),
            })?;
        if actual_enum != enum_name {
            return Err(VirLoweringError::Unsupported {
                context: "enum pattern",
                detail: format!(
                    "pattern `{enum_name}::{variant}` does not match scrutinee type `{actual_enum:?}`"
                ),
            });
        }
        if let Some(info) = self.enum_variant(enum_name, variant).cloned() {
            return Ok(info);
        }
        self.builtin_enum_variant_info(enum_ty, variant)
            .ok_or_else(|| VirLoweringError::MissingType {
                context: format!(
                    "enum variant `{enum_name}::{variant}` in `{}`",
                    self.function_name
                ),
            })
    }

    pub(super) fn enum_variant_info_for_place(
        &self,
        scrutinee: &Place,
        enum_name: &str,
        variant: &str,
    ) -> Result<EnumVariantInfo, VirLoweringError> {
        let scrutinee_ty = self.place_type(scrutinee)?;
        self.enum_variant_info_for_type(&scrutinee_ty, enum_name, variant)
    }

    pub(super) fn downcast_place(scrutinee: Place, variant: &str) -> Place {
        Place::Downcast {
            base: Box::new(scrutinee),
            variant: variant.to_string(),
        }
    }

    pub(super) fn bind_enum_pattern(
        &mut self,
        scrutinee: Place,
        enum_name: &str,
        variant: &str,
        payload: &EnumPatternPayload,
    ) -> Result<(), VirLoweringError> {
        self.bind_enum_pattern_impl(scrutinee, enum_name, variant, payload, false)
    }

    /// Like `bind_enum_pattern` but binds payload fields by shared reference.
    /// Used for match-guard evaluation over non-Copy scrutinees.
    pub(super) fn bind_enum_pattern_by_ref(
        &mut self,
        scrutinee: Place,
        enum_name: &str,
        variant: &str,
        payload: &EnumPatternPayload,
    ) -> Result<(), VirLoweringError> {
        self.bind_enum_pattern_impl(scrutinee, enum_name, variant, payload, true)
    }

    fn bind_enum_pattern_impl(
        &mut self,
        scrutinee: Place,
        enum_name: &str,
        variant: &str,
        payload: &EnumPatternPayload,
        by_ref: bool,
    ) -> Result<(), VirLoweringError> {
        let info = self.enum_variant_info_for_place(&scrutinee, enum_name, variant)?;
        let downcast = Self::downcast_place(scrutinee, variant);
        match (&info.payload, payload) {
            (EnumPayloadInfo::Unit, EnumPatternPayload::Unit) => Ok(()),
            (EnumPayloadInfo::Tuple(expected), EnumPatternPayload::Tuple(patterns)) => {
                if expected.len() != patterns.len() {
                    return Err(VirLoweringError::Unsupported {
                        context: "enum pattern",
                        detail: format!(
                            "tuple variant `{enum_name}::{variant}` expects {} fields, got {}",
                            expected.len(),
                            patterns.len()
                        ),
                    });
                }
                for (idx, subpattern) in patterns.iter().enumerate() {
                    let place = tuple_field_place(downcast.clone(), idx);
                    if by_ref {
                        self.bind_pattern_by_ref(place, subpattern)?;
                    } else {
                        self.bind_pattern(place, subpattern)?;
                    }
                }
                Ok(())
            }
            (
                EnumPayloadInfo::Struct {
                    fields: expected_fields,
                    ..
                },
                EnumPatternPayload::Struct(fields),
            ) => {
                for (field_name, subpattern) in fields {
                    if !expected_fields
                        .iter()
                        .any(|(expected_name, _)| expected_name == field_name)
                    {
                        return Err(VirLoweringError::Unsupported {
                            context: "enum pattern",
                            detail: format!(
                                "struct variant `{enum_name}::{variant}` has no field `{field_name}`"
                            ),
                        });
                    }
                    let field_place = Place::Field {
                        base: Box::new(downcast.clone()),
                        field: field_name.clone(),
                    };
                    if by_ref {
                        self.bind_pattern_by_ref(field_place, subpattern)?;
                    } else {
                        self.bind_pattern(field_place, subpattern)?;
                    }
                }
                Ok(())
            }
            (EnumPayloadInfo::Unit, other) => Err(VirLoweringError::Unsupported {
                context: "enum pattern",
                detail: format!(
                    "unit variant `{enum_name}::{variant}` cannot use payload `{other:?}`"
                ),
            }),
            (EnumPayloadInfo::Tuple(_), other) => Err(VirLoweringError::Unsupported {
                context: "enum pattern",
                detail: format!(
                    "tuple variant `{enum_name}::{variant}` requires tuple payload, got `{other:?}`"
                ),
            }),
            (EnumPayloadInfo::Struct { .. }, other) => Err(VirLoweringError::Unsupported {
                context: "enum pattern",
                detail: format!(
                    "struct variant `{enum_name}::{variant}` requires named fields, got `{other:?}`"
                ),
            }),
        }
    }

    pub(super) fn lower_enum_pattern_test(
        &mut self,
        scrutinee: Place,
        enum_name: &str,
        variant: &str,
        payload: &EnumPatternPayload,
        success_block: BasicBlockId,
        failure_block: BasicBlockId,
    ) -> Result<(), VirLoweringError> {
        let scrutinee_ty = self.place_type(&scrutinee)?;
        if let Some(actual_enum) = nominal_type_name(&scrutinee_ty) {
            if actual_enum != enum_name && builtin_try_enum_mismatch(&actual_enum, enum_name) {
                self.current_block_mut().terminator = Term::Goto {
                    target: failure_block,
                    args: vec![],
                };
                return Ok(());
            }
        }
        let info = self.enum_variant_info_for_type(&scrutinee_ty, enum_name, variant)?;
        match (&info.payload, payload) {
            (EnumPayloadInfo::Unit, EnumPatternPayload::Unit) => {}
            (EnumPayloadInfo::Tuple(expected), EnumPatternPayload::Tuple(patterns)) => {
                if expected.len() != patterns.len() {
                    return Err(VirLoweringError::Unsupported {
                        context: "enum pattern",
                        detail: format!(
                            "tuple variant `{enum_name}::{variant}` expects {} fields, got {}",
                            expected.len(),
                            patterns.len()
                        ),
                    });
                }
            }
            (
                EnumPayloadInfo::Struct {
                    fields: expected_fields,
                    ..
                },
                EnumPatternPayload::Struct(fields),
            ) => {
                for (field_name, _) in fields {
                    if !expected_fields
                        .iter()
                        .any(|(expected_name, _)| expected_name == field_name)
                    {
                        return Err(VirLoweringError::Unsupported {
                            context: "enum pattern",
                            detail: format!(
                                "struct variant `{enum_name}::{variant}` has no field `{field_name}`"
                            ),
                        });
                    }
                }
            }
            (EnumPayloadInfo::Unit, other) => {
                return Err(VirLoweringError::Unsupported {
                    context: "enum pattern",
                    detail: format!(
                        "unit variant `{enum_name}::{variant}` cannot use payload `{other:?}`"
                    ),
                });
            }
            (EnumPayloadInfo::Tuple(_), other) => {
                return Err(VirLoweringError::Unsupported {
                    context: "enum pattern",
                    detail: format!(
                        "tuple variant `{enum_name}::{variant}` requires tuple payload, got `{other:?}`"
                    ),
                });
            }
            (EnumPayloadInfo::Struct { .. }, other) => {
                return Err(VirLoweringError::Unsupported {
                    context: "enum pattern",
                    detail: format!(
                        "struct variant `{enum_name}::{variant}` requires named fields, got `{other:?}`"
                    ),
                });
            }
        }

        let discriminant_local =
            self.alloc_local(None, RustType::Uint(UintType::Usize), Mutability::Mutable);
        self.emit(VirStmt::Assign {
            place: Place::Local(discriminant_local),
            rvalue: Rvalue::Discriminant(scrutinee.clone()),
        });

        let payload_block = match payload {
            EnumPatternPayload::Unit => success_block,
            _ => self.new_block(Term::Unreachable),
        };
        let mut targets = SwitchTargets::new(failure_block);
        targets.add(info.discriminant, payload_block);
        self.current_block_mut().terminator = Term::SwitchInt {
            discriminant: Operand::Copy(Place::Local(discriminant_local)),
            targets,
        };

        if payload_block == success_block {
            return Ok(());
        }

        self.switch_to_block(payload_block);
        let downcast = Self::downcast_place(scrutinee, variant);
        match payload {
            EnumPatternPayload::Unit => unreachable!("validated above"),
            EnumPatternPayload::Tuple(patterns) => {
                if patterns.is_empty() {
                    self.current_block_mut().terminator = Term::Goto {
                        target: success_block,
                        args: vec![],
                    };
                    return Ok(());
                }
                let mut current_block = self.current_block_id();
                for (idx, subpattern) in patterns.iter().enumerate() {
                    self.switch_to_block(current_block);
                    let next_success = if idx + 1 == patterns.len() {
                        success_block
                    } else {
                        self.new_block(Term::Unreachable)
                    };
                    self.lower_pattern_test(
                        tuple_field_place(downcast.clone(), idx),
                        subpattern,
                        next_success,
                        failure_block,
                    )?;
                    current_block = next_success;
                }
                Ok(())
            }
            EnumPatternPayload::Struct(fields) => {
                if fields.is_empty() {
                    self.current_block_mut().terminator = Term::Goto {
                        target: success_block,
                        args: vec![],
                    };
                    return Ok(());
                }
                let mut current_block = self.current_block_id();
                for (idx, (field_name, subpattern)) in fields.iter().enumerate() {
                    self.switch_to_block(current_block);
                    let next_success = if idx + 1 == fields.len() {
                        success_block
                    } else {
                        self.new_block(Term::Unreachable)
                    };
                    let field_place = Place::Field {
                        base: Box::new(downcast.clone()),
                        field: field_name.clone(),
                    };
                    self.lower_pattern_test(field_place, subpattern, next_success, failure_block)?;
                    current_block = next_success;
                }
                Ok(())
            }
        }
    }

    fn builtin_enum_variant_info(
        &self,
        enum_ty: &RustType,
        variant: &str,
    ) -> Option<EnumVariantInfo> {
        match enum_ty {
            RustType::Option { inner } => match variant {
                "None" => Some(EnumVariantInfo {
                    variant_index: 0,
                    discriminant: 0,
                    payload: EnumPayloadInfo::Unit,
                }),
                "Some" => Some(EnumVariantInfo {
                    variant_index: 1,
                    discriminant: 1,
                    payload: EnumPayloadInfo::Tuple(vec![(**inner).clone()]),
                }),
                _ => None,
            },
            RustType::Result { ok, err } => match variant {
                "Ok" => Some(EnumVariantInfo {
                    variant_index: 0,
                    discriminant: 0,
                    payload: EnumPayloadInfo::Tuple(vec![(**ok).clone()]),
                }),
                "Err" => Some(EnumVariantInfo {
                    variant_index: 1,
                    discriminant: 1,
                    payload: EnumPayloadInfo::Tuple(vec![(**err).clone()]),
                }),
                _ => None,
            },
            RustType::Reference { inner, .. }
            | RustType::RawPtr { inner, .. }
            | RustType::Box { inner }
            | RustType::Pin { inner } => self.builtin_enum_variant_info(inner, variant),
            _ => None,
        }
    }
}

fn builtin_try_enum_mismatch(actual_enum: &str, pattern_enum: &str) -> bool {
    matches!(
        (actual_enum, pattern_enum),
        ("Option", "Result") | ("Result", "Option")
    )
}

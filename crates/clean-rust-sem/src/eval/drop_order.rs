// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Composite child-order policy for Rust destructors.
//!
//! Implements the Rust Reference rule that struct fields drop in declaration
//! order, tuple fields drop in order, and array elements drop first to last.
//! Reference: <https://doc.rust-lang.org/reference/destructors.html>

use crate::ownership::Place;
use crate::types::RustType;
use crate::values::EnumPayload;

use super::Interpreter;

impl Interpreter {
    /// Return the ordered children of a composite place for drop purposes.
    ///
    /// The returned `Vec<(Place, RustType)>` lists child places and their types
    /// in Rust-specified drop order:
    /// - Tuple fields: `0..len`, left to right
    /// - Array elements: `0..len`, first to last
    /// - Named structs: declaration order from `TypeDef::Struct` (falls back
    ///   to runtime field-map iteration when no type definition is registered)
    pub(super) fn drop_children_in_rust_order(
        &self,
        place: &Place,
        ty: &RustType,
    ) -> Vec<(Place, RustType)> {
        match ty {
            RustType::Tuple(elems) => elems
                .iter()
                .enumerate()
                .map(|(idx, elem_ty)| {
                    let field_place = Place::Index {
                        base: Box::new(place.clone()),
                        index: Box::new(Place::Local(idx as u32)),
                    };
                    (field_place, elem_ty.clone())
                })
                .collect(),

            RustType::Array { element, len } => {
                let len = len.as_usize(&std::collections::HashMap::new()).unwrap_or(0);
                (0..len)
                    .map(|idx| {
                        let elem_place = Place::Index {
                            base: Box::new(place.clone()),
                            index: Box::new(Place::Local(idx as u32)),
                        };
                        (elem_place, element.as_ref().clone())
                    })
                    .collect()
            }

            RustType::Named {
                name, type_args, ..
            } => {
                let Ok(value) = self.read_tracked_place_value(place) else {
                    return Vec::new();
                };

                match value {
                    crate::values::Value::Struct { fields, .. } => {
                        let declared_fields: Option<Vec<(String, RustType)>> =
                            self.ctx.get_type(name).and_then(|td| match td {
                                crate::stmt::TypeDef::Struct {
                                    fields: decl_fields,
                                    type_params,
                                    ..
                                } => {
                                    let subst =
                                        RustType::build_type_param_subst(type_params, type_args)
                                            .unwrap_or_default();
                                    if subst.is_empty() {
                                        Some(decl_fields.clone())
                                    } else {
                                        Some(
                                            decl_fields
                                                .iter()
                                                .map(|(field_name, ty)| {
                                                    (
                                                        field_name.clone(),
                                                        ty.substitute_type_params(&subst),
                                                    )
                                                })
                                                .collect(),
                                        )
                                    }
                                }
                                _ => None,
                            });
                        let decl_order: Vec<String> = declared_fields
                            .as_ref()
                            .map(|df| df.iter().map(|(n, _)| n.clone()).collect())
                            .unwrap_or_else(|| fields.keys().cloned().collect());

                        decl_order
                            .into_iter()
                            .filter_map(|field_name| {
                                let field_val = fields.get(&field_name)?;
                                let child_ty = declared_fields
                                    .as_ref()
                                    .and_then(|df| {
                                        df.iter()
                                            .find(|(n, _)| *n == field_name)
                                            .map(|(_, ty)| ty.clone())
                                    })
                                    .filter(|ty| !matches!(ty, RustType::TypeParam(_)))
                                    .unwrap_or_else(|| field_val.get_type());
                                let field_place = Place::Field {
                                    base: Box::new(place.clone()),
                                    field: field_name,
                                };
                                Some((field_place, child_ty))
                            })
                            .collect()
                    }
                    crate::values::Value::Enum {
                        name: ref enum_name,
                        ref variant,
                        ref payload,
                    } => {
                        let variant_def = self.ctx.get_type(enum_name).and_then(|td| match td {
                            crate::stmt::TypeDef::Enum { variants, .. } => {
                                variants.iter().find(|v| v.name == *variant).cloned()
                            }
                            _ => None,
                        });

                        match payload.as_ref() {
                            EnumPayload::Unit => Vec::new(),
                            EnumPayload::Tuple(values) => {
                                let variant_types = variant_def.and_then(|vd| match vd.payload {
                                    crate::stmt::EnumVariantType::Tuple(tys) => Some(tys),
                                    _ => None,
                                });
                                values
                                    .iter()
                                    .enumerate()
                                    .map(|(idx, val)| {
                                        let child_ty = variant_types
                                            .as_ref()
                                            .and_then(|tys| tys.get(idx).cloned())
                                            .filter(|ty| !matches!(ty, RustType::TypeParam(_)))
                                            .unwrap_or_else(|| val.get_type());
                                        let child_place = Place::Index {
                                            base: Box::new(place.clone()),
                                            index: Box::new(Place::Local(idx as u32)),
                                        };
                                        (child_place, child_ty)
                                    })
                                    .collect()
                            }
                            EnumPayload::Struct(fields) => {
                                let declared_fields = variant_def.and_then(|vd| match vd.payload {
                                    crate::stmt::EnumVariantType::Struct(fields) => Some(fields),
                                    _ => None,
                                });
                                let decl_order: Vec<String> = declared_fields
                                    .as_ref()
                                    .map(|fields| fields.iter().map(|(n, _)| n.clone()).collect())
                                    .unwrap_or_else(|| fields.keys().cloned().collect());

                                decl_order
                                    .into_iter()
                                    .filter_map(|field_name| {
                                        let field_val = fields.get(&field_name)?;
                                        let child_ty = declared_fields
                                            .as_ref()
                                            .and_then(|decl_fields| {
                                                decl_fields
                                                    .iter()
                                                    .find(|(name, _)| *name == field_name)
                                                    .map(|(_, ty)| ty.clone())
                                            })
                                            .filter(|ty| !matches!(ty, RustType::TypeParam(_)))
                                            .unwrap_or_else(|| field_val.get_type());
                                        let child_place = Place::Field {
                                            base: Box::new(place.clone()),
                                            field: field_name,
                                        };
                                        Some((child_place, child_ty))
                                    })
                                    .collect()
                            }
                        }
                    }
                    _ => Vec::new(),
                }
            }

            _ => Vec::new(),
        }
    }
}

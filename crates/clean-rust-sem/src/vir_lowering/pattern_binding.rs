// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Pattern binding helpers — extracts values from matched patterns into locals.

use super::context::FunctionLoweringContext;
use super::VirLoweringError;
use crate::expr::Pattern;
use crate::ownership::Place;
use crate::types::Lifetime;
use crate::types::UintType;
use crate::types::{Mutability, RustType};
use crate::vir::{BinOp, BorrowKind, Constant, Operand, Rvalue, ScalarValue, Stmt as VirStmt};

impl<'a> FunctionLoweringContext<'a> {
    pub(super) fn bind_pattern(
        &mut self,
        scrutinee: Place,
        pattern: &Pattern,
    ) -> Result<(), VirLoweringError> {
        match pattern {
            Pattern::Wildcard | Pattern::Literal(_) => Ok(()),
            Pattern::Binding {
                name,
                mutable,
                subpattern,
            } => {
                if let Some(subpattern) = subpattern {
                    // `name @ subpattern`: the outer binding `name` claims the
                    // whole scrutinee, so the sub-bindings inside `subpattern`
                    // cannot also move fields out of it.  For a non-Copy
                    // scrutinee we therefore bind the subpattern *by reference*
                    // (RFC 2005 / Rust's `@`-with-sub-binding semantics: the
                    // inner bindings observe the value through shared borrows)
                    // and then move the whole value into `name` below.  For a
                    // Copy scrutinee each sub-binding is an independent copy, so
                    // the cheaper by-value path is sound and preserved.
                    if self.place_type(&scrutinee)?.is_copy() {
                        self.bind_pattern(scrutinee.clone(), subpattern)?;
                    } else {
                        self.bind_pattern_by_ref(scrutinee.clone(), subpattern)?;
                    }
                }
                let binding_ty = self.place_type(&scrutinee)?;
                let local = self.declare_binding(
                    name,
                    binding_ty,
                    if *mutable {
                        Mutability::Mutable
                    } else {
                        Mutability::Shared
                    },
                )?;
                self.propagate_async_output_metadata(&scrutinee, local);
                self.emit(VirStmt::Assign {
                    place: Place::Local(local),
                    rvalue: Rvalue::Use(self.place_operand(scrutinee)?),
                });
                Ok(())
            }
            Pattern::Ref { pattern, .. } => self.bind_pattern(scrutinee, pattern),
            Pattern::Tuple(patterns) => {
                let tuple_len = match self.place_type(&scrutinee)? {
                    RustType::Tuple(field_tys) => field_tys.len(),
                    other => {
                        return Err(VirLoweringError::Unsupported {
                            context: "tuple pattern",
                            detail: format!(
                                "tuple destructuring requires tuple scrutinee, got `{other:?}`"
                            ),
                        });
                    }
                };
                if tuple_len != patterns.len() {
                    return Err(VirLoweringError::Unsupported {
                        context: "tuple pattern",
                        detail: format!(
                            "tuple pattern arity mismatch: scrutinee has {tuple_len} fields, pattern has {}",
                            patterns.len()
                        ),
                    });
                }
                for (idx, subpattern) in patterns.iter().enumerate() {
                    self.bind_pattern(tuple_field_place(scrutinee.clone(), idx), subpattern)?;
                }
                Ok(())
            }
            Pattern::Struct { fields, .. } => {
                for (field_name, subpattern) in fields {
                    let field_place = Place::Field {
                        base: Box::new(scrutinee.clone()),
                        field: field_name.clone(),
                    };
                    self.bind_pattern(field_place, subpattern)?;
                }
                Ok(())
            }
            Pattern::EnumVariant {
                enum_name,
                variant,
                payload,
            } => self.bind_enum_pattern(scrutinee, enum_name, variant, payload),
            Pattern::Or(alternatives) => {
                // All or-pattern alternatives must bind the same names.
                // We bind from the first alternative only — pattern testing
                // has already determined which alternative matched.
                if let Some(first) = alternatives.first() {
                    self.bind_pattern(scrutinee, first)?;
                }
                Ok(())
            }
            Pattern::Range { .. } | Pattern::Rest => Ok(()),
            Pattern::Slice(patterns) => self.bind_slice_pattern_impl(scrutinee, patterns, false),
        }
    }

    /// Bind pattern variables as shared references to the scrutinee's fields.
    ///
    /// Used for match-guard evaluation over non-Copy scrutinees (MIR semantics):
    /// the guard sees `&T` bindings so the scrutinee is preserved for subsequent
    /// arms if the guard fails.  After the guard passes, the caller pops this
    /// scope and re-binds by move for the arm body.
    pub(super) fn bind_pattern_by_ref(
        &mut self,
        scrutinee: Place,
        pattern: &Pattern,
    ) -> Result<(), VirLoweringError> {
        match pattern {
            Pattern::Wildcard | Pattern::Literal(_) | Pattern::Range { .. } | Pattern::Rest => {
                Ok(())
            }
            Pattern::Binding {
                name, subpattern, ..
            } => {
                if let Some(sub) = subpattern {
                    self.bind_pattern_by_ref(scrutinee.clone(), sub)?;
                }
                let inner_ty = self.place_type(&scrutinee)?;
                let ref_ty = RustType::Reference {
                    inner: Box::new(inner_ty),
                    mutability: Mutability::Shared,
                    lifetime: Lifetime::Anonymous(0),
                };
                let local = self.declare_binding(name, ref_ty, Mutability::Shared)?;
                self.emit(VirStmt::Assign {
                    place: Place::Local(local),
                    rvalue: Rvalue::Ref {
                        borrow_kind: BorrowKind::Shared,
                        place: scrutinee,
                    },
                });
                Ok(())
            }
            Pattern::Ref { pattern, .. } => self.bind_pattern_by_ref(scrutinee, pattern),
            Pattern::Tuple(patterns) => {
                for (idx, subpattern) in patterns.iter().enumerate() {
                    self.bind_pattern_by_ref(
                        tuple_field_place(scrutinee.clone(), idx),
                        subpattern,
                    )?;
                }
                Ok(())
            }
            Pattern::Struct { fields, .. } => {
                for (field_name, subpattern) in fields {
                    let field_place = Place::Field {
                        base: Box::new(scrutinee.clone()),
                        field: field_name.clone(),
                    };
                    self.bind_pattern_by_ref(field_place, subpattern)?;
                }
                Ok(())
            }
            Pattern::EnumVariant {
                enum_name,
                variant,
                payload,
            } => self.bind_enum_pattern_by_ref(scrutinee, enum_name, variant, payload),
            Pattern::Or(alternatives) => {
                if let Some(first) = alternatives.first() {
                    self.bind_pattern_by_ref(scrutinee, first)?;
                }
                Ok(())
            }
            Pattern::Slice(patterns) => self.bind_slice_pattern_impl(scrutinee, patterns, true),
        }
    }

    fn bind_slice_pattern_impl(
        &mut self,
        scrutinee: Place,
        patterns: &[Pattern],
        by_ref: bool,
    ) -> Result<(), VirLoweringError> {
        let usize_ty = RustType::Uint(UintType::Usize);

        let rest_pos = patterns.iter().position(|p| matches!(p, Pattern::Rest));

        let (prefix_patterns, suffix_patterns) = match rest_pos {
            None => (patterns, &[][..]),
            Some(pos) => (&patterns[..pos], &patterns[pos + 1..]),
        };

        // We need the length local only if there are suffix bindings.
        let len_local = if !suffix_patterns.is_empty() {
            let local = self.alloc_local(None, usize_ty.clone(), Mutability::Mutable);
            self.emit(VirStmt::Assign {
                place: Place::Local(local),
                rvalue: Rvalue::Len(scrutinee.clone()),
            });
            Some(local)
        } else {
            None
        };

        // Bind prefix elements: index 0, 1, 2, ...
        for (i, subpat) in prefix_patterns.iter().enumerate() {
            if matches!(subpat, Pattern::Wildcard | Pattern::Rest) {
                continue;
            }
            let idx_local = self.alloc_local(None, usize_ty.clone(), Mutability::Mutable);
            self.emit(VirStmt::Assign {
                place: Place::Local(idx_local),
                rvalue: Rvalue::Use(Operand::Constant(Constant::Scalar(ScalarValue::Uint(
                    i as u128,
                )))),
            });
            let elem_place = Place::Index {
                base: Box::new(scrutinee.clone()),
                index: Box::new(Place::Local(idx_local)),
            };
            if by_ref {
                self.bind_pattern_by_ref(elem_place, subpat)?;
            } else {
                self.bind_pattern(elem_place, subpat)?;
            }
        }

        // Bind suffix elements: index len - reverse_offset.
        if let Some(len_local) = len_local {
            for (j, subpat) in suffix_patterns.iter().enumerate() {
                if matches!(subpat, Pattern::Wildcard | Pattern::Rest) {
                    continue;
                }
                let reverse_offset = suffix_patterns.len() - j;
                let idx_local = self.alloc_local(None, usize_ty.clone(), Mutability::Mutable);
                self.emit(VirStmt::Assign {
                    place: Place::Local(idx_local),
                    rvalue: Rvalue::BinaryOp {
                        op: BinOp::Sub,
                        lhs: Operand::Copy(Place::Local(len_local)),
                        rhs: Operand::Constant(Constant::Scalar(ScalarValue::Uint(
                            reverse_offset as u128,
                        ))),
                    },
                });
                let elem_place = Place::Index {
                    base: Box::new(scrutinee.clone()),
                    index: Box::new(Place::Local(idx_local)),
                };
                if by_ref {
                    self.bind_pattern_by_ref(elem_place, subpat)?;
                } else {
                    self.bind_pattern(elem_place, subpat)?;
                }
            }
        }

        Ok(())
    }
}

pub(super) fn tuple_field_place(base: Place, index: usize) -> Place {
    Place::Field {
        base: Box::new(base),
        field: index.to_string(),
    }
}

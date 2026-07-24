// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Variant names share an enum-prefix by design (e.g., 'KindFoo', 'KindBar' for KindKind enums); renaming is API-breaking.
#![allow(clippy::enum_variant_names)]

//! Closure capture helpers shared by closure construction and invocation.

use super::Interpreter;
use crate::ownership::Place;
use crate::types::{ClosureKind, Mutability};
use crate::values::Value;

/// Runtime capture mode for a resolved closure capture.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum CaptureMode {
    ByRef,
    ByMutRef,
    ByMove,
    ByCopy,
}

impl CaptureMode {
    const fn minimum_kind(self) -> ClosureKind {
        match self {
            Self::ByRef | Self::ByCopy => ClosureKind::Fn,
            Self::ByMutRef => ClosureKind::FnMut,
            Self::ByMove => ClosureKind::FnOnce,
        }
    }

    fn is_compatible_with(self, kind: ClosureKind) -> bool {
        self.minimum_kind().can_coerce_to(kind)
    }

    const fn description(self) -> &'static str {
        match self {
            Self::ByRef => "&T",
            Self::ByMutRef => "&mut T",
            Self::ByMove => "move",
            Self::ByCopy => "copy",
        }
    }
}

/// Resolved runtime state for a closure capture.
#[derive(Debug, Clone, PartialEq)]
pub(super) struct CaptureBinding {
    pub(super) name: String,
    pub(super) mode: CaptureMode,
    pub(super) current_value: Value,
}

impl CaptureBinding {
    pub(super) fn new(name: String, mode: CaptureMode, current_value: Value) -> Self {
        Self {
            name,
            mode,
            current_value,
        }
    }
}

pub(super) fn capture_mode_for_resolved_capture(
    mutability: Mutability,
    capture_by_value: bool,
    value: &Value,
) -> CaptureMode {
    if capture_by_value {
        if value.get_type().is_copy() {
            CaptureMode::ByCopy
        } else {
            CaptureMode::ByMove
        }
    } else if mutability == Mutability::Mutable {
        CaptureMode::ByMutRef
    } else {
        CaptureMode::ByRef
    }
}

pub(super) fn validate_capture_modes(
    kind: ClosureKind,
    captures: &[CaptureBinding],
) -> Result<(), String> {
    for capture in captures {
        if !capture.mode.is_compatible_with(kind) {
            return Err(format!(
                "closure kind `{kind:?}` is incompatible with capture `{}` in mode `{}`; requires at least `{:?}`",
                capture.name,
                capture.mode.description(),
                capture.mode.minimum_kind(),
            ));
        }
    }
    Ok(())
}

pub(super) fn propagate_fnmut_captures(
    interp: &mut Interpreter,
    captures: &[CaptureBinding],
    capture_places: &[(String, Place, Mutability)],
) -> Result<(), String> {
    for capture in captures {
        if capture.mode != CaptureMode::ByMutRef {
            continue;
        }
        let Some(target_place) = capture_places
            .iter()
            .find(|(name, _, mutability)| {
                name == &capture.name && *mutability == Mutability::Mutable
            })
            .map(|(_, place, _)| place.clone())
        else {
            continue;
        };

        if interp.binding_value_for_place(&target_place).is_none() {
            continue;
        }
        if let Err(err) = interp.validate_whole_place_write(&target_place) {
            return Err(format!("closure capture writeback rejected: {err}"));
        }
        if let Err(err) = interp.write_tracked_place_value(
            &target_place,
            interp.materialize_value(&capture.current_value),
        ) {
            return Err(format!("closure capture writeback failed: {err}"));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::Expr;
    use crate::values::BinOp;

    fn make_fnmut_increment_closure(capture_name: &str) -> Expr {
        Expr::Closure {
            params: vec![],
            body: Box::new(Expr::Assign {
                target: Box::new(Expr::Var {
                    name: capture_name.to_string(),
                    local_idx: 0,
                }),
                value: Box::new(Expr::BinOp {
                    op: BinOp::Add,
                    left: Box::new(Expr::Var {
                        name: capture_name.to_string(),
                        local_idx: 0,
                    }),
                    right: Box::new(Expr::Literal(Value::u32(1))),
                }),
            }),
            captures: vec![(capture_name.to_string(), Mutability::Mutable)],
            capture_by_value: false,
        }
    }

    #[test]
    fn fnmut_capture_writeback_updates_enclosing_scope() {
        let mut interp = Interpreter::new();
        interp.bind("x".to_string(), Value::u32(0));

        let closure_value = interp
            .eval(&make_fnmut_increment_closure("x"))
            .value()
            .expect("closure literal should evaluate to a closure");
        interp.bind("f".to_string(), closure_value);

        let call_expr = Expr::Call {
            func: Box::new(Expr::Var {
                name: "f".to_string(),
                local_idx: 0,
            }),
            args: vec![],
            type_args: vec![],
        };

        assert_eq!(interp.eval(&call_expr).value(), Some(Value::Unit));
        assert_eq!(interp.eval(&call_expr).value(), Some(Value::Unit));
        assert_eq!(interp.lookup("x"), Some(Value::u32(2)));
    }

    #[test]
    fn validate_capture_modes_rejects_invalid_trait_combinations() {
        assert!(validate_capture_modes(
            ClosureKind::FnMut,
            &[CaptureBinding::new(
                "x".to_string(),
                CaptureMode::ByMutRef,
                Value::u32(0),
            )],
        )
        .is_ok());

        let err = validate_capture_modes(
            ClosureKind::Fn,
            &[CaptureBinding::new(
                "x".to_string(),
                CaptureMode::ByMutRef,
                Value::u32(0),
            )],
        )
        .expect_err("Fn closures must reject mutable-reference captures");
        assert!(err.contains("Fn"));

        let err = validate_capture_modes(
            ClosureKind::FnMut,
            &[CaptureBinding::new(
                "x".to_string(),
                CaptureMode::ByMove,
                Value::Struct {
                    name: "S".to_string(),
                    fields: Default::default(),
                },
            )],
        )
        .expect_err("FnMut closures must reject move captures");
        assert!(err.contains("FnOnce"));
    }
}

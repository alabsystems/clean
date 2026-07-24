// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{ConstGenericArg, ConstGenericValue};
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ConstGenericBound {
    Eq(ConstGenericArg, ConstGenericArg),
    Ne(ConstGenericArg, ConstGenericArg),
    Lt(ConstGenericArg, ConstGenericArg),
    Le(ConstGenericArg, ConstGenericArg),
    Gt(ConstGenericArg, ConstGenericArg),
    Ge(ConstGenericArg, ConstGenericArg),
}

pub struct ConstGenericEval;

impl ConstGenericEval {
    #[must_use]
    pub fn eval(
        arg: &ConstGenericArg,
        subst: &HashMap<String, ConstGenericValue>,
    ) -> ConstGenericValue {
        dependent_const_eval(arg, &HashMap::new(), subst)
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ConstGenericUnifier {
    bindings: HashMap<String, ConstGenericValue>,
}

impl ConstGenericUnifier {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    #[must_use]
    pub fn bindings(&self) -> &HashMap<String, ConstGenericValue> {
        &self.bindings
    }

    pub fn unify(&mut self, lhs: &ConstGenericArg, rhs: &ConstGenericArg) -> bool {
        if let (Some(lhs), Some(rhs)) = (known(lhs, &self.bindings), known(rhs, &self.bindings)) {
            return lhs == rhs;
        }
        self.solve(lhs, rhs)
            .or_else(|| self.solve(rhs, lhs))
            .unwrap_or(false)
    }

    fn solve(&mut self, pattern: &ConstGenericArg, target: &ConstGenericArg) -> Option<bool> {
        let target = known(target, &self.bindings)?;
        Some(match pattern {
            ConstGenericArg::Param(name) => self.bind(name, target),
            ConstGenericArg::Neg(inner) => match target {
                ConstGenericValue::I32(value) => value
                    .checked_neg()
                    .map(|value| {
                        self.solve(
                            inner,
                            &ConstGenericArg::Value(ConstGenericValue::I32(value)),
                        )
                        .unwrap_or(false)
                    })
                    .unwrap_or(false),
                _ => false,
            },
            ConstGenericArg::Add(lhs, rhs) => self.solve_add(lhs, rhs, &target),
            ConstGenericArg::Sub(lhs, rhs) => self.solve_sub(lhs, rhs, &target),
            ConstGenericArg::Mul(lhs, rhs) => self.solve_mul(lhs, rhs, &target),
            ConstGenericArg::Div(_, _) | ConstGenericArg::Rem(_, _) | ConstGenericArg::Value(_) => {
                ConstGenericEval::eval(pattern, &self.bindings) == target
            }
        })
    }

    fn solve_add(
        &mut self,
        lhs: &ConstGenericArg,
        rhs: &ConstGenericArg,
        target: &ConstGenericValue,
    ) -> bool {
        match (known(lhs, &self.bindings), known(rhs, &self.bindings)) {
            (Some(lhs), None) => subtract(target, &lhs)
                .map(|missing| {
                    self.solve(rhs, &ConstGenericArg::Value(missing))
                        .unwrap_or(false)
                })
                .unwrap_or(false),
            (None, Some(rhs)) => subtract(target, &rhs)
                .map(|missing| {
                    self.solve(lhs, &ConstGenericArg::Value(missing))
                        .unwrap_or(false)
                })
                .unwrap_or(false),
            _ => {
                ConstGenericEval::eval(
                    &ConstGenericArg::Add(Box::new(lhs.clone()), Box::new(rhs.clone())),
                    &self.bindings,
                ) == *target
            }
        }
    }

    fn solve_sub(
        &mut self,
        lhs: &ConstGenericArg,
        rhs: &ConstGenericArg,
        target: &ConstGenericValue,
    ) -> bool {
        match (known(lhs, &self.bindings), known(rhs, &self.bindings)) {
            (Some(lhs), None) => subtract(&lhs, target)
                .map(|missing| {
                    self.solve(rhs, &ConstGenericArg::Value(missing))
                        .unwrap_or(false)
                })
                .unwrap_or(false),
            (None, Some(rhs)) => add(target, &rhs)
                .map(|missing| {
                    self.solve(lhs, &ConstGenericArg::Value(missing))
                        .unwrap_or(false)
                })
                .unwrap_or(false),
            _ => {
                ConstGenericEval::eval(
                    &ConstGenericArg::Sub(Box::new(lhs.clone()), Box::new(rhs.clone())),
                    &self.bindings,
                ) == *target
            }
        }
    }

    fn solve_mul(
        &mut self,
        lhs: &ConstGenericArg,
        rhs: &ConstGenericArg,
        target: &ConstGenericValue,
    ) -> bool {
        match (known(lhs, &self.bindings), known(rhs, &self.bindings)) {
            (Some(lhs), None) => divide(target, &lhs)
                .map(|missing| {
                    self.solve(rhs, &ConstGenericArg::Value(missing))
                        .unwrap_or(false)
                })
                .unwrap_or(false),
            (None, Some(rhs)) => divide(target, &rhs)
                .map(|missing| {
                    self.solve(lhs, &ConstGenericArg::Value(missing))
                        .unwrap_or(false)
                })
                .unwrap_or(false),
            _ => {
                ConstGenericEval::eval(
                    &ConstGenericArg::Mul(Box::new(lhs.clone()), Box::new(rhs.clone())),
                    &self.bindings,
                ) == *target
            }
        }
    }

    fn bind(&mut self, name: &str, value: ConstGenericValue) -> bool {
        match self.bindings.get(name) {
            Some(bound) => bound == &value,
            None => {
                self.bindings.insert(name.to_string(), value);
                true
            }
        }
    }
}

#[must_use]
pub fn dependent_const_eval(
    arg: &ConstGenericArg,
    defs: &HashMap<String, ConstGenericArg>,
    subst: &HashMap<String, ConstGenericValue>,
) -> ConstGenericValue {
    eval(arg, defs, subst, &mut HashSet::new())
}

pub fn validate_const_generic_bounds(
    bounds: &[ConstGenericBound],
    subst: &HashMap<String, ConstGenericValue>,
) -> Result<(), String> {
    for bound in bounds {
        let ok = match bound {
            ConstGenericBound::Eq(lhs, rhs) => compare(lhs, rhs, subst, |o| o == Some(true)),
            ConstGenericBound::Ne(lhs, rhs) => compare(lhs, rhs, subst, |o| o == Some(false)),
            ConstGenericBound::Lt(lhs, rhs) => ordered(lhs, rhs, subst, |o| o.is_lt()),
            ConstGenericBound::Le(lhs, rhs) => ordered(lhs, rhs, subst, |o| !o.is_gt()),
            ConstGenericBound::Gt(lhs, rhs) => ordered(lhs, rhs, subst, |o| o.is_gt()),
            ConstGenericBound::Ge(lhs, rhs) => ordered(lhs, rhs, subst, |o| !o.is_lt()),
        };
        if !ok {
            return Err(format!("failed const generic bound {bound:?}"));
        }
    }
    Ok(())
}

fn eval(
    arg: &ConstGenericArg,
    defs: &HashMap<String, ConstGenericArg>,
    subst: &HashMap<String, ConstGenericValue>,
    visiting: &mut HashSet<String>,
) -> ConstGenericValue {
    match arg {
        ConstGenericArg::Value(value) => value.clone(),
        ConstGenericArg::Param(name) => subst
            .get(name)
            .cloned()
            .or_else(|| {
                defs.get(name).and_then(|next| {
                    if !visiting.insert(name.clone()) {
                        return None;
                    }
                    let value = eval(next, defs, subst, visiting);
                    visiting.remove(name);
                    Some(value)
                })
            })
            .unwrap_or(ConstGenericValue::Unknown),
        ConstGenericArg::Add(lhs, rhs) => binary(lhs, rhs, defs, subst, visiting, add),
        ConstGenericArg::Sub(lhs, rhs) => binary(lhs, rhs, defs, subst, visiting, subtract),
        ConstGenericArg::Mul(lhs, rhs) => binary(lhs, rhs, defs, subst, visiting, multiply),
        ConstGenericArg::Div(lhs, rhs) => binary(lhs, rhs, defs, subst, visiting, divide),
        ConstGenericArg::Rem(lhs, rhs) => binary(lhs, rhs, defs, subst, visiting, remainder),
        ConstGenericArg::Neg(inner) => match eval(inner, defs, subst, visiting) {
            ConstGenericValue::I32(value) => value
                .checked_neg()
                .map(ConstGenericValue::I32)
                .unwrap_or(ConstGenericValue::Unknown),
            _ => ConstGenericValue::Unknown,
        },
    }
}

fn binary(
    lhs: &ConstGenericArg,
    rhs: &ConstGenericArg,
    defs: &HashMap<String, ConstGenericArg>,
    subst: &HashMap<String, ConstGenericValue>,
    visiting: &mut HashSet<String>,
    op: fn(&ConstGenericValue, &ConstGenericValue) -> Option<ConstGenericValue>,
) -> ConstGenericValue {
    let lhs = eval(lhs, defs, subst, visiting);
    let rhs = eval(rhs, defs, subst, visiting);
    op(&lhs, &rhs).unwrap_or(ConstGenericValue::Unknown)
}

fn compare(
    lhs: &ConstGenericArg,
    rhs: &ConstGenericArg,
    subst: &HashMap<String, ConstGenericValue>,
    predicate: impl FnOnce(Option<bool>) -> bool,
) -> bool {
    let lhs = ConstGenericEval::eval(lhs, subst);
    let rhs = ConstGenericEval::eval(rhs, subst);
    predicate(eq_value(&lhs, &rhs))
}

fn ordered(
    lhs: &ConstGenericArg,
    rhs: &ConstGenericArg,
    subst: &HashMap<String, ConstGenericValue>,
    predicate: impl FnOnce(std::cmp::Ordering) -> bool,
) -> bool {
    ordering(
        &ConstGenericEval::eval(lhs, subst),
        &ConstGenericEval::eval(rhs, subst),
    )
    .map(predicate)
    .unwrap_or(false)
}

fn known(
    arg: &ConstGenericArg,
    subst: &HashMap<String, ConstGenericValue>,
) -> Option<ConstGenericValue> {
    let value = ConstGenericEval::eval(arg, subst);
    (!matches!(value, ConstGenericValue::Unknown)).then_some(value)
}

fn eq_value(lhs: &ConstGenericValue, rhs: &ConstGenericValue) -> Option<bool> {
    (!matches!(
        (lhs, rhs),
        (ConstGenericValue::Unknown, _) | (_, ConstGenericValue::Unknown)
    ))
    .then_some(lhs == rhs)
}

fn ordering(lhs: &ConstGenericValue, rhs: &ConstGenericValue) -> Option<std::cmp::Ordering> {
    match (lhs, rhs) {
        (ConstGenericValue::Usize(lhs), ConstGenericValue::Usize(rhs)) => Some(lhs.cmp(rhs)),
        (ConstGenericValue::I32(lhs), ConstGenericValue::I32(rhs)) => Some(lhs.cmp(rhs)),
        (ConstGenericValue::Char(lhs), ConstGenericValue::Char(rhs)) => Some(lhs.cmp(rhs)),
        _ => None,
    }
}

fn add(lhs: &ConstGenericValue, rhs: &ConstGenericValue) -> Option<ConstGenericValue> {
    match (lhs, rhs) {
        (ConstGenericValue::Usize(lhs), ConstGenericValue::Usize(rhs)) => {
            lhs.checked_add(*rhs).map(ConstGenericValue::Usize)
        }
        (ConstGenericValue::I32(lhs), ConstGenericValue::I32(rhs)) => {
            lhs.checked_add(*rhs).map(ConstGenericValue::I32)
        }
        _ => None,
    }
}

fn subtract(lhs: &ConstGenericValue, rhs: &ConstGenericValue) -> Option<ConstGenericValue> {
    match (lhs, rhs) {
        (ConstGenericValue::Usize(lhs), ConstGenericValue::Usize(rhs)) => {
            lhs.checked_sub(*rhs).map(ConstGenericValue::Usize)
        }
        (ConstGenericValue::I32(lhs), ConstGenericValue::I32(rhs)) => {
            lhs.checked_sub(*rhs).map(ConstGenericValue::I32)
        }
        _ => None,
    }
}

fn multiply(lhs: &ConstGenericValue, rhs: &ConstGenericValue) -> Option<ConstGenericValue> {
    match (lhs, rhs) {
        (ConstGenericValue::Usize(lhs), ConstGenericValue::Usize(rhs)) => {
            lhs.checked_mul(*rhs).map(ConstGenericValue::Usize)
        }
        (ConstGenericValue::I32(lhs), ConstGenericValue::I32(rhs)) => {
            lhs.checked_mul(*rhs).map(ConstGenericValue::I32)
        }
        _ => None,
    }
}

fn divide(lhs: &ConstGenericValue, rhs: &ConstGenericValue) -> Option<ConstGenericValue> {
    match (lhs, rhs) {
        (ConstGenericValue::Usize(lhs), ConstGenericValue::Usize(rhs)) if *rhs != 0 => {
            Some(ConstGenericValue::Usize(*lhs / *rhs))
        }
        (ConstGenericValue::I32(lhs), ConstGenericValue::I32(rhs)) if *rhs != 0 => {
            lhs.checked_div(*rhs).map(ConstGenericValue::I32)
        }
        _ => None,
    }
}

fn remainder(lhs: &ConstGenericValue, rhs: &ConstGenericValue) -> Option<ConstGenericValue> {
    match (lhs, rhs) {
        (ConstGenericValue::Usize(lhs), ConstGenericValue::Usize(rhs)) if *rhs != 0 => {
            Some(ConstGenericValue::Usize(*lhs % *rhs))
        }
        (ConstGenericValue::I32(lhs), ConstGenericValue::I32(rhs)) if *rhs != 0 => {
            lhs.checked_rem(*rhs).map(ConstGenericValue::I32)
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{ConstParamDef, RustType, UintType};

    #[test]
    fn evaluates_dependent_const_expressions() {
        let expr = ConstGenericArg::Add(
            Box::new(ConstGenericArg::Param("M".to_string())),
            Box::new(ConstGenericArg::Value(ConstGenericValue::Usize(2))),
        );
        let defs = HashMap::from([(
            "M".to_string(),
            ConstGenericArg::Mul(
                Box::new(ConstGenericArg::Param("N".to_string())),
                Box::new(ConstGenericArg::Value(ConstGenericValue::Usize(3))),
            ),
        )]);
        let subst = HashMap::from([("N".to_string(), ConstGenericValue::Usize(4))]);
        assert_eq!(
            dependent_const_eval(&expr, &defs, &subst),
            ConstGenericValue::Usize(14)
        );
    }

    #[test]
    fn validates_const_bounds_and_solves_simple_unification() {
        let expr = ConstGenericArg::Add(
            Box::new(ConstGenericArg::Param("N".to_string())),
            Box::new(ConstGenericArg::Value(ConstGenericValue::Usize(1))),
        );
        let mut unifier = ConstGenericUnifier::new();
        assert!(unifier.unify(&expr, &ConstGenericArg::Value(ConstGenericValue::Usize(5))));
        assert_eq!(
            unifier.bindings().get("N"),
            Some(&ConstGenericValue::Usize(4))
        );
        assert!(validate_const_generic_bounds(
            &[ConstGenericBound::Ge(
                ConstGenericArg::Param("N".to_string()),
                ConstGenericArg::Value(ConstGenericValue::Usize(1)),
            )],
            unifier.bindings(),
        )
        .is_ok());
    }

    #[test]
    fn builds_and_applies_dependent_const_substitutions() {
        let defs = [ConstParamDef {
            name: "N".to_string(),
            ty: RustType::Uint(UintType::Usize),
        }];
        let ty = RustType::Array {
            element: Box::new(RustType::Uint(UintType::U8)),
            len: ConstGenericArg::Add(
                Box::new(ConstGenericArg::Param("N".to_string())),
                Box::new(ConstGenericArg::Value(ConstGenericValue::Usize(1))),
            ),
        };
        let subst = RustType::build_const_param_subst(
            &defs,
            &[ConstGenericArg::Value(ConstGenericValue::Usize(3))],
        )
        .expect("arity should match");
        assert_eq!(
            ty.substitute_const_params(&subst),
            RustType::Array {
                element: Box::new(RustType::Uint(UintType::U8)),
                len: ConstGenericArg::Value(ConstGenericValue::Usize(4)),
            }
        );
    }
}

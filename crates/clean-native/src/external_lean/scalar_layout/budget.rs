// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Resource-only borrowed traversal before retaining/copying source metadata.
//! No serializer, semantic evaluation or declaration authority is supplied.

use clean_compiler::runtime_lcnf::RuntimeSourceCaptureLimits;
use clean_kernel::expr::{BigNat, MDataValue};
use clean_kernel::name::NameInner;
use clean_kernel::{
    ConstructorVal, Expr, ExprKind, InductiveVal, Level, Literal, Name, RecursorVal,
};

pub(super) struct Budget {
    visited: usize,
    remaining_visits: usize,
    remaining_units: usize,
}
impl Budget {
    pub fn new() -> Self {
        let limits = RuntimeSourceCaptureLimits::default();
        Self {
            visited: 0,
            remaining_visits: limits.declarations,
            remaining_units: limits.source_bytes,
        }
    }
    fn spend(&mut self, units: usize) -> Result<(), String> {
        self.remaining_units = self
            .remaining_units
            .checked_sub(units)
            .ok_or("layout preparation expanded work/copy allowance exhausted")?;
        Ok(())
    }
    pub fn visit(&mut self) -> Result<(), String> {
        self.remaining_visits = self
            .remaining_visits
            .checked_sub(1)
            .ok_or("layout preparation exceeded its whole-world recursor visit allowance")?;
        self.visited += 1;
        Ok(())
    }
    pub fn visited(&self) -> usize {
        self.visited
    }
    pub fn text(&mut self, text: &str) -> Result<(), String> {
        self.spend(text.len())
    }
    pub fn name(&mut self, mut name: &Name) -> Result<(), String> {
        loop {
            self.spend(1)?;
            match name.inner() {
                NameInner::Anon => return Ok(()),
                NameInner::Str(parent, text) => {
                    self.text(text)?;
                    name = parent;
                }
                NameInner::Num(parent, _) => name = parent,
            }
        }
    }
    pub fn names(&mut self, names: &[Name]) -> Result<(), String> {
        self.spend(names.len())?;
        for name in names {
            self.name(name)?;
        }
        Ok(())
    }
    fn level(&mut self, level: &Level) -> Result<(), String> {
        let mut pending = vec![level];
        while let Some(level) = pending.pop() {
            self.spend(1)?;
            match level {
                Level::Zero => {}
                Level::Param(name) => self.name(name)?,
                Level::Succ(inner) => pending.push(inner),
                Level::Max(a, b) | Level::IMax(a, b) => pending.extend([a.as_ref(), b.as_ref()]),
            }
        }
        Ok(())
    }
    /// Expanded occurrences, not DAG allocation count. Payload lengths are
    /// charged before inspecting strings/limbs or doing any copy/instantiation.
    /// This is a finite work allowance, not an OS memory or serializer bound.
    pub fn expression(&mut self, expression: &Expr) -> Result<(), String> {
        let mut pending = vec![expression];
        while let Some(expr) = pending.pop() {
            self.spend(1)?;
            match expr.kind() {
                ExprKind::BVar(_) | ExprKind::FVar(_) => {}
                ExprKind::Sort(level) => self.level(level)?,
                ExprKind::Const(name, levels) => {
                    self.name(name)?;
                    self.spend(levels.len())?;
                    for level in levels {
                        self.level(level)?;
                    }
                }
                ExprKind::App(a, b) | ExprKind::Lam(_, a, b) | ExprKind::Pi(_, a, b) => {
                    pending.extend([a.as_ref(), b.as_ref()])
                }
                ExprKind::Let(name, ty, value, body, _) => {
                    self.name(name)?;
                    pending.extend([ty.as_ref(), value.as_ref(), body.as_ref()]);
                }
                ExprKind::Proj(name, _, inner) => {
                    self.name(name)?;
                    pending.push(inner);
                }
                ExprKind::MData(data, inner) => {
                    self.spend(data.len())?;
                    for (key, value) in data {
                        self.name(key)?;
                        match value {
                            MDataValue::String(text) => self.text(text)?,
                            MDataValue::Name(name) => self.name(name)?,
                            MDataValue::Bool(_) | MDataValue::Nat(_) => self.spend(1)?,
                        }
                    }
                    pending.push(inner);
                }
                ExprKind::Lit(Literal::String(text)) => self.text(text)?,
                ExprKind::Lit(Literal::Nat(BigNat::Big(limbs))) => self.spend(limbs.len())?,
                ExprKind::Lit(Literal::Nat(BigNat::Small(_))) => self.spend(1)?,
                _ => return Err("unsupported expression during bounded layout preparation".into()),
            }
        }
        Ok(())
    }
    pub fn inductive(&mut self, ind: &InductiveVal) -> Result<(), String> {
        self.name(&ind.name)?;
        self.names(&ind.level_params)?;
        self.expression(&ind.type_)?;
        self.names(&ind.all_names)?;
        self.names(&ind.constructor_names)
    }
    pub fn constructor(&mut self, ctor: &ConstructorVal) -> Result<(), String> {
        self.name(&ctor.name)?;
        self.name(&ctor.inductive_name)?;
        self.names(&ctor.level_params)?;
        self.expression(&ctor.type_)
    }
    pub fn recursor(&mut self, rec: &RecursorVal) -> Result<(), String> {
        self.name(&rec.name)?;
        self.name(&rec.inductive_name)?;
        self.names(&rec.level_params)?;
        self.expression(&rec.type_)?;
        self.spend(rec.rules.len())?;
        for rule in &rec.rules {
            self.name(&rule.constructor_name)?;
            self.spend(rule.recursive_fields.len())?;
            self.expression(&rule.rhs)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn scalar_layout_preparation_bounds_visits_names_and_expanded_copy_work() {
        let mut budget = Budget {
            visited: 0,
            remaining_visits: 1,
            remaining_units: 40,
        };
        budget.visit().unwrap();
        assert!(budget.visit().unwrap_err().contains("whole-world"));
        assert_eq!(budget.visited(), 1);
        let long = Name::anon().str("x".repeat(100));
        assert!(budget.name(&long).unwrap_err().contains("work/copy"));
        let mut budget = Budget {
            visited: 0,
            remaining_visits: 1,
            remaining_units: 500,
        };
        let mut expanded = Expr::nat_lit(0);
        for _ in 0..20 {
            expanded = Expr::app(expanded.clone(), expanded);
        }
        assert!(budget.expression(&expanded).is_err());
        assert!(budget.names(&vec![Name::anon(); 1000]).is_err());
    }
}

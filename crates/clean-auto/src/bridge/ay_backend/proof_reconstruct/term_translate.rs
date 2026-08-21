// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Term back-translation: ay TermId → kernel Expr.
//!
//! Translates ay's internal term representation back to the kernel's `Expr` type.
//! This is the reverse of `AyBackend::translate_expr`.

use super::expr_builders::{infer_universe_level, mk_add, mk_mul, mk_neg, sort_to_lean_type};
use super::expr_builders::{mk_and, mk_eq, mk_ite_checked, mk_le, mk_lt, mk_not, mk_or, mk_xor};
use super::trace::{ConstantView, TermView};
use super::{ReconstructResult, ReconstructionContext, ReconstructionError};
use ay_core::TermId;
use clean_kernel::expr::BinderInfo;
use clean_kernel::{Expr, FVarId};

impl<'a> ReconstructionContext<'a> {
    /// Translate a ay term to a kernel expression, with caching.
    ///
    /// Cache is bypassed when inside quantifier binders (`binder_names` non-empty)
    /// because the same TermId may translate to different expressions depending on
    /// binder context (e.g., `Var("x")` → `BVar(0)` inside a forall vs. FVar
    /// outside).
    pub fn translate_term(&mut self, term_id: TermId) -> ReconstructResult<Expr> {
        let in_binder = !self.binder_names.is_empty();
        if !in_binder {
            if let Some(cached) = self.term_cache.get(&term_id) {
                return Ok(cached.clone());
            }
        }

        let result = self.translate_term_inner(term_id)?;
        if !in_binder {
            self.term_cache.insert(term_id, result.clone());
        }
        Ok(result)
    }

    fn translate_term_inner(&mut self, term_id: TermId) -> ReconstructResult<Expr> {
        super::stack_safe(|| match self.trace().term(term_id) {
            TermView::Const(constant) => {
                let sort = self.trace().sort(term_id);
                Self::translate_constant(constant, sort)
            }
            TermView::Var { name, .. } => self.translate_var(name),
            TermView::Not(inner) => {
                let inner_expr = self.translate_term(inner)?;
                Ok(mk_not(&inner_expr))
            }
            TermView::NamedApp { name, args } => self.translate_app(name, args),
            TermView::IndexedApp { name, .. } => Err(ReconstructionError::UnsupportedTerm {
                description: format!("indexed symbol: {}", name),
            }),
            TermView::Ite(cond, then_br, else_br) => {
                let cond_expr = self.translate_term(cond)?;
                let then_expr = self.translate_term(then_br)?;
                let else_expr = self.translate_term(else_br)?;
                let sort = self.trace().sort(term_id);
                mk_ite_checked(sort, &cond_expr, &then_expr, &else_expr).ok_or(
                    ReconstructionError::UnsupportedTerm {
                        description: "no Decidable instance for ite condition".to_string(),
                    },
                )
            }
            TermView::Let { body } => {
                // Let bindings already resolved in TermStore; translate body directly
                self.translate_term(body)
            }
            TermView::Forall { vars, body } => {
                // Push binder names so translate_var resolves Var(name) → BVar(idx)
                let depth_before = self.binder_names.len();
                for (name, _sort) in vars.iter() {
                    self.binder_names.push(name.clone());
                }
                let mut result = self.translate_term(body)?;
                self.binder_names.truncate(depth_before);
                // Wrap in Pi binders from right to left (innermost last)
                for (_name, sort) in vars.iter().rev() {
                    let var_ty = sort_to_lean_type(sort);
                    result = Expr::pi(BinderInfo::Default, var_ty, result);
                }
                Ok(result)
            }
            TermView::Exists { vars, body } => {
                let depth_before = self.binder_names.len();
                for (name, _sort) in vars.iter() {
                    self.binder_names.push(name.clone());
                }
                let mut result = self.translate_term(body)?;
                self.binder_names.truncate(depth_before);
                // Wrap in @Exists α (fun x : α => body) from right to left
                for (_name, sort) in vars.iter().rev() {
                    let var_ty = sort_to_lean_type(sort);
                    let u = infer_universe_level(&var_ty);
                    let predicate = Expr::lam(BinderInfo::Default, var_ty.clone(), result);
                    result = Expr::app(
                        Expr::app(
                            Expr::const_(clean_kernel::name::Name::from_string("Exists"), vec![u]),
                            var_ty,
                        ),
                        predicate,
                    );
                }
                Ok(result)
            }
            TermView::Unknown => Err(ReconstructionError::UnsupportedTerm {
                description: "unknown term view variant".to_string(),
            }),
        })
    }

    fn translate_constant(constant: ConstantView<'_>, sort: &ay::Sort) -> ReconstructResult<Expr> {
        use clean_kernel::name::Name;

        match constant {
            ConstantView::Bool(true) => Ok(Expr::const_(Name::from_string("True"), vec![])),
            ConstantView::Bool(false) => Ok(Expr::const_(Name::from_string("False"), vec![])),
            ConstantView::Int(n) => Self::translate_int_constant(n, sort),
            ConstantView::Rational(r) => {
                if r.0.denom() != &num_bigint::BigInt::from(1) {
                    return Err(ReconstructionError::UnsupportedTerm {
                        description: format!(
                            "non-integer rational constant {}/{}",
                            r.0.numer(),
                            r.0.denom()
                        ),
                    });
                }
                Self::translate_int_constant(r.0.numer(), sort)
            }
            ConstantView::BitVec { value, width } => Err(ReconstructionError::UnsupportedTerm {
                description: format!("bitvector constant #b{} (width {})", value, width),
            }),
            ConstantView::String(s) => Err(ReconstructionError::UnsupportedTerm {
                description: format!("string constant {:?}", s),
            }),
            ConstantView::Unknown => Err(ReconstructionError::UnsupportedTerm {
                description: "unknown constant view variant".to_string(),
            }),
        }
    }

    /// Translate an integer constant to a Lean Expr, wrapping in the appropriate
    /// coercion for the target sort (Int.ofNat, Real.ofNat, Real.ofInt).
    fn translate_int_constant(n: &num_bigint::BigInt, sort: &ay::Sort) -> ReconstructResult<Expr> {
        use clean_kernel::name::Name;

        if n.sign() != num_bigint::Sign::Minus {
            let nat_lit: u64 = n
                .try_into()
                .map_err(|_| ReconstructionError::UnsupportedTerm {
                    description: format!("integer too large: {}", n),
                })?;
            let nat_expr = Expr::nat_lit(nat_lit);
            match sort {
                ay::Sort::Int => Ok(Expr::app(
                    Expr::const_(Name::from_string("Int.ofNat"), vec![]),
                    nat_expr,
                )),
                ay::Sort::Real => Ok(Expr::app(
                    Expr::const_(Name::from_string("Real.ofNat"), vec![]),
                    nat_expr,
                )),
                _ => Ok(nat_expr),
            }
        } else {
            let abs_minus_one: u64 =
                (-n - 1u64)
                    .try_into()
                    .map_err(|_| ReconstructionError::UnsupportedTerm {
                        description: format!("negative integer too large: {}", n),
                    })?;
            let int_expr = Expr::app(
                Expr::const_(Name::from_string("Int.negSucc"), vec![]),
                Expr::nat_lit(abs_minus_one),
            );
            if matches!(sort, ay::Sort::Real) {
                // Real sort: wrap in Real.ofInt so the type is Real, not Int.
                Ok(Expr::app(
                    Expr::const_(Name::from_string("Real.ofInt"), vec![]),
                    int_expr,
                ))
            } else {
                Ok(int_expr)
            }
        }
    }

    fn translate_var(&self, name: &str) -> ReconstructResult<Expr> {
        // Check binder stack first: last pushed = innermost = BVar(0).
        // This converts ay named variables to de Bruijn indices inside
        // quantifier bodies.
        for (i, binder_name) in self.binder_names.iter().rev().enumerate() {
            if binder_name == name {
                return Ok(Expr::bvar(i as u32));
            }
        }
        if let Some((expr, _ty)) = self.var_map.get_var(name) {
            return Ok(expr.clone());
        }
        // Try parsing "fvar_N" pattern
        if let Some(id_str) = name.strip_prefix("fvar_") {
            if let Ok(id) = id_str.parse::<u64>() {
                return Ok(Expr::fvar(FVarId::new(id)));
            }
        }
        Err(ReconstructionError::UnknownVariable {
            name: name.to_string(),
        })
    }

    fn translate_app(&mut self, name: &str, args: &[TermId]) -> ReconstructResult<Expr> {
        match (name, args.len()) {
            ("=", 2) => self.translate_equality_app(args),
            ("and", _) if args.len() >= 2 => self.translate_folded_bool_app(args, mk_and),
            ("or", _) if args.len() >= 2 => self.translate_folded_bool_app(args, mk_or),
            // `mk_implies` normally desugars to `or`, but imported/native Alethe
            // traces may retain either spelling. Both denote non-dependent
            // implication in the kernel.
            ("=>" | "implies", 2) => self.translate_implies_app(args),
            ("xor", 2) => self.translate_xor_app(args),
            ("<", 2) => self.translate_sorted_binary_app(args, mk_lt),
            ("<=", 2) => self.translate_sorted_binary_app(args, mk_le),
            // Normalize >=|> to <=|< with swapped arguments.
            // ay's decompose_arithmetic_eq/decompose_disequality create raw
            // Symbol::Named(">="|">") via mk_app, bypassing mk_ge/mk_gt.
            (">", 2) => self.translate_sorted_binary_app(&[args[1], args[0]], mk_lt),
            (">=", 2) => self.translate_sorted_binary_app(&[args[1], args[0]], mk_le),
            ("+", _) if args.len() >= 2 => self.translate_nary_arith_app(args, mk_add),
            ("*", _) if args.len() >= 2 => self.translate_nary_arith_app(args, mk_mul),
            ("-", 1) => self.translate_neg_app(args[0]),
            _ => self.translate_uninterpreted_app(name, args),
        }
    }

    fn translate_equality_app(&mut self, args: &[TermId]) -> ReconstructResult<Expr> {
        let lhs = self.translate_term(args[0])?;
        let rhs = self.translate_term(args[1])?;
        let ty = sort_to_lean_type(self.trace().sort(args[0]));
        Ok(mk_eq(&ty, &lhs, &rhs))
    }

    fn translate_folded_bool_app(
        &mut self,
        args: &[TermId],
        mk: fn(&Expr, &Expr) -> Expr,
    ) -> ReconstructResult<Expr> {
        let mut exprs = self.translate_args(args)?;
        let last = exprs.pop().expect("invariant: args.len() >= 2 guard");
        exprs
            .into_iter()
            .rev()
            .try_fold(last, |acc, expr| Ok(mk(&expr, &acc)))
    }

    fn translate_implies_app(&mut self, args: &[TermId]) -> ReconstructResult<Expr> {
        let lhs = self.translate_term(args[0])?;
        let rhs = self.translate_term(args[1])?;
        Ok(Expr::pi(BinderInfo::Default, lhs, rhs.lift(1)))
    }

    fn translate_xor_app(&mut self, args: &[TermId]) -> ReconstructResult<Expr> {
        let lhs = self.translate_term(args[0])?;
        let rhs = self.translate_term(args[1])?;
        Ok(mk_xor(&lhs, &rhs))
    }

    fn translate_sorted_binary_app(
        &mut self,
        args: &[TermId],
        mk: fn(&ay::Sort, &Expr, &Expr) -> Expr,
    ) -> ReconstructResult<Expr> {
        let lhs = self.translate_term(args[0])?;
        let rhs = self.translate_term(args[1])?;
        Ok(mk(self.trace().sort(args[0]), &lhs, &rhs))
    }

    fn translate_nary_arith_app(
        &mut self,
        args: &[TermId],
        mk: fn(&ay::Sort, &Expr, &Expr) -> Expr,
    ) -> ReconstructResult<Expr> {
        let exprs = self.translate_args(args)?;
        let sort = self.trace().sort(args[0]);
        let first = exprs[0].clone();
        exprs[1..]
            .iter()
            .try_fold(first, |acc, expr| Ok(mk(sort, &acc, expr)))
    }

    fn translate_neg_app(&mut self, arg: TermId) -> ReconstructResult<Expr> {
        let inner = self.translate_term(arg)?;
        Ok(mk_neg(self.trace().sort(arg), &inner))
    }

    fn translate_uninterpreted_app(
        &mut self,
        name: &str,
        args: &[TermId],
    ) -> ReconstructResult<Expr> {
        if let Some((func_expr, _)) = self.var_map.get_var(name) {
            let mut result = func_expr.clone();
            for &arg in args {
                result = Expr::app(result, self.translate_term(arg)?);
            }
            Ok(result)
        } else {
            Err(ReconstructionError::UnsupportedTerm {
                description: format!(
                    "unknown function application: {}({} args)",
                    name,
                    args.len()
                ),
            })
        }
    }

    fn translate_args(&mut self, args: &[TermId]) -> ReconstructResult<Vec<Expr>> {
        args.iter().map(|&arg| self.translate_term(arg)).collect()
    }
}

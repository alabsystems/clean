// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::super::{BridgeResult, SmtBridge};
use super::ExprKey;
use crate::smt::TermId;
use clean_kernel::{Expr, ExprKind, FVarId};

impl<'env> SmtBridge<'env> {
    /// Convert an expression to a hashable key.
    /// Delegates to [`ExprKey::from_expr`] - this method exists for ergonomic
    /// `self.expr_to_key(...)` call sites.
    pub(crate) fn expr_to_key(&self, expr: &Expr) -> Option<ExprKey> {
        ExprKey::from_expr(expr)
    }

    /// Translate a kernel term to an SMT term.
    ///
    /// Returns `BridgeResult<TermId>` so translation failures propagate as typed
    /// errors instead of being silently swallowed as `None`.
    pub(crate) fn translate_term(&mut self, expr: &Expr) -> BridgeResult<TermId> {
        // Strip MData transparently - metadata wrappers must not affect
        // translation identity (#2279)
        let expr = expr.strip_mdata();

        if let Some(term_id) = self
            .expr_to_key(expr)
            .and_then(|key| self.expr_to_term.get(&key).copied())
        {
            return Ok(term_id);
        }

        let term_id = match expr.kind() {
            ExprKind::FVar(fvar_id) => self.translate_fvar(*fvar_id),
            ExprKind::Const(name, _) => self.smt.const_term(name.to_string()),
            ExprKind::App(_, _) => self.translate_app_term(expr)?,
            ExprKind::Lit(lit) => match lit {
                clean_kernel::expr::Literal::Nat(n) => self.smt.int_term(n.clone()),
                clean_kernel::expr::Literal::String(s) => self.smt.const_term(format!("str_{s}")),
            },
            _ => self.fresh_lossy_term(expr, "term_"),
        };

        self.cache_translated_term(expr, term_id);
        Ok(term_id)
    }

    /// Infer and cache the type for a term if not already known.
    /// Uses the bridge's local context (if set) so FVar types resolve correctly.
    pub(super) fn try_populate_term_type(&mut self, term_id: TermId, expr: &Expr) {
        if !self.term_to_type.contains_key(&term_id) {
            let tc = self.make_tc();
            if let Ok(ty) = tc.infer_type(expr) {
                self.term_to_type.insert(term_id, ty);
            }
        }
    }

    fn translate_fvar(&mut self, fvar_id: FVarId) -> TermId {
        if let Some(&term_id) = self.fvar_to_term.get(&fvar_id) {
            return term_id;
        }

        let name = format!("fvar_{}", fvar_id.as_u64());
        let term_id = self.smt.const_term(name);
        self.fvar_to_term.insert(fvar_id, term_id);
        term_id
    }

    fn translate_app_term(&mut self, expr: &Expr) -> BridgeResult<TermId> {
        let head = expr.get_app_fn().strip_mdata();
        let args = expr.get_app_args();

        match head.kind() {
            ExprKind::Const(name, _) => self.translate_const_head_app(&name.to_string(), &args),
            ExprKind::FVar(fvar_id) => self.translate_fvar_head_app(*fvar_id, &args),
            _ => Ok(self.fresh_lossy_term(expr, "app_")),
        }
    }

    fn translate_const_head_app(&mut self, name: &str, args: &[&Expr]) -> BridgeResult<TermId> {
        if let Some(term_id) = self.try_translate_array_app(name, args)? {
            return Ok(term_id);
        }

        let arg_terms = self.translate_arg_terms(args)?;
        Ok(self.smt.app_term(name.to_string(), arg_terms))
    }

    fn translate_fvar_head_app(&mut self, fvar_id: FVarId, args: &[&Expr]) -> BridgeResult<TermId> {
        let func_name = format!("fvar_{}", fvar_id.as_u64());
        let arg_terms = self.translate_arg_terms(args)?;
        Ok(self.smt.app_term(func_name, arg_terms))
    }

    fn try_translate_array_app(
        &mut self,
        name: &str,
        args: &[&Expr],
    ) -> BridgeResult<Option<TermId>> {
        let array_term = match name {
            // Array select (read): Array.get α arr idx or getElem arr idx bound
            "Array.get" | "getElem" | "GetElem.getElem" if args.len() >= 2 => {
                let len = args.len();
                let arr = self.translate_term(args[len - 2])?;
                let idx = self.translate_term(args[len - 1])?;
                Some(self.smt.select_term(arr, idx))
            }
            // Array store (write): Array.set α arr idx val
            "Array.set" | "setElem" | "SetElem.setElem" if args.len() >= 3 => {
                let len = args.len();
                let arr = self.translate_term(args[len - 3])?;
                let idx = self.translate_term(args[len - 2])?;
                let val = self.translate_term(args[len - 1])?;
                Some(self.smt.store_term(arr, idx, val))
            }
            // C-style array access: select and store
            "select" if args.len() == 2 => {
                let arr = self.translate_term(args[0])?;
                let idx = self.translate_term(args[1])?;
                Some(self.smt.select_term(arr, idx))
            }
            "store" if args.len() == 3 => {
                let arr = self.translate_term(args[0])?;
                let idx = self.translate_term(args[1])?;
                let val = self.translate_term(args[2])?;
                Some(self.smt.store_term(arr, idx, val))
            }
            _ => None,
        };

        Ok(array_term)
    }

    fn translate_arg_terms(&mut self, args: &[&Expr]) -> BridgeResult<Vec<TermId>> {
        args.iter().map(|arg| self.translate_term(arg)).collect()
    }

    fn fresh_lossy_term(&mut self, expr: &Expr, prefix: &str) -> TermId {
        // Complex-headed applications and unsupported term forms are not
        // faithfully representable in the SMT bridge; track the fallback before
        // introducing an unconstrained placeholder.
        self.record_lossy_expr(expr);
        let name = format!("{prefix}{}", self.fresh_counter);
        self.fresh_counter += 1;
        self.smt.const_term(name)
    }

    fn cache_translated_term(&mut self, expr: &Expr, term_id: TermId) {
        if let Some(key) = self.expr_to_key(expr) {
            self.expr_to_term.insert(key, term_id);
        }
        self.term_to_expr.insert(term_id, expr.clone());
        self.try_populate_term_type(term_id, expr);
    }
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Elaboration, universe-parameter collection, and verification helpers.

use clean_elab::ElabCtx;
use clean_kernel::{Expr, ExprKind, Level, Name, TypeChecker};
use clean_parser::parse_expr;

use super::{SpecError, Specification};

impl Specification {
    /// Verify that a definition is well-typed.
    pub fn verify_definition(&self, name: &str) -> Result<(), SpecError> {
        let def = self
            .definitions
            .get(name)
            .ok_or_else(|| SpecError::UnknownDefinition(name.to_string()))?;

        let type_expr = def
            .elaborated_type
            .as_ref()
            .ok_or_else(|| SpecError::MissingElaboration(def.name.clone()))?;

        if let Some(value) = &def.elaborated_value {
            let tc = TypeChecker::with_mode(&self.env, self.env.mode());
            let inferred = tc
                .infer_type(value)
                .map_err(|e| SpecError::TypeError(format!("infer {}: {:?}", def.name, e)))?;

            if !tc.is_def_eq(&inferred, type_expr) {
                return Err(SpecError::TypeError(format!(
                    "Type mismatch for {}: {:?} vs {:?}",
                    def.name, inferred, type_expr
                )));
            }
        }

        Ok(())
    }

    /// Collect all `Level::Param` names from an expression (deduplicated, stable order).
    pub(crate) fn collect_level_params_expr(e: &Expr, out: &mut Vec<Name>) {
        let mut stack: Vec<&Expr> = vec![e];
        while let Some(curr) = stack.pop() {
            match curr.kind() {
                ExprKind::Sort(l) => Self::collect_level_params_level(l, out),
                ExprKind::Const(_, levels) => {
                    for l in levels {
                        Self::collect_level_params_level(l, out);
                    }
                }
                ExprKind::App(f, a) => {
                    stack.push(a);
                    stack.push(f);
                }
                ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                    stack.push(body);
                    stack.push(ty);
                }
                ExprKind::Let(_, ty, val, body, _) => {
                    stack.push(body);
                    stack.push(val);
                    stack.push(ty);
                }
                ExprKind::Proj(_, _, val) | ExprKind::MData(_, val) | ExprKind::Squash(val) => {
                    stack.push(val);
                }
                _ => {}
            }
        }
    }

    pub(crate) fn collect_level_params_level(l: &Level, out: &mut Vec<Name>) {
        let mut lstack = vec![l];
        while let Some(curr) = lstack.pop() {
            match curr {
                Level::Param(n) => {
                    if !out.contains(n) {
                        out.push(n.clone());
                    }
                }
                Level::Succ(inner) => lstack.push(inner),
                Level::Max(a, b) | Level::IMax(a, b) => {
                    lstack.push(b);
                    lstack.push(a);
                }
                Level::Zero => {}
            }
        }
    }

    /// Elaborate a clean source string in the current spec environment.
    pub(crate) fn elaborate_source(&self, src: &str, label: &str) -> Result<Expr, SpecError> {
        let surface =
            parse_expr(src).map_err(|e| SpecError::ParseError(format!("{label}: {e}")))?;
        let mut ctx = ElabCtx::new(&self.env);
        let expr = ctx
            .elaborate(&surface)
            .map_err(|e| SpecError::ElabError(format!("{label}: {e}")))?;
        // Instantiate solved metavariables and universe levels (fixes #134-style UnknownFVar errors).
        let expr = ctx.metas().instantiate(&expr);
        Ok(ctx.metas().instantiate_levels(&expr))
    }

    /// Elaborate a value and align its inferred universe parameters with an
    /// already elaborated expected type.
    ///
    /// The value is deliberately elaborated in inference mode first. Passing a
    /// polymorphic lambda directly to checking mode can solve two independent
    /// source universes to the same expected parameter before the whole binder
    /// telescope has been seen. Once collapsed, no post-pass can recover their
    /// independence (`Eq.cong` used to turn both `u` and `v` into `u_0`).
    ///
    /// Independent elaboration preserves the value's universe structure. We
    /// infer its type, construct a conflict-checked bijection from those fresh
    /// parameters to the expected type's parameters, apply it to the value, and
    /// require the renamed inferred type to be definitionally equal to the
    /// expected type. Declaration registration still performs the authoritative
    /// kernel check afterward.
    pub(crate) fn elaborate_source_checked(
        &self,
        src: &str,
        expected_ty: &Expr,
        label: &str,
    ) -> Result<Expr, SpecError> {
        let surface =
            parse_expr(src).map_err(|e| SpecError::ParseError(format!("{label}: {e}")))?;
        let mut ctx = ElabCtx::new(&self.env);
        let value = ctx
            .elaborate(&surface)
            .map_err(|e| SpecError::ElabError(format!("{label}: {e}")))?;
        let value = ctx.metas().instantiate(&value);
        let value = ctx.metas().instantiate_levels(&value);

        let tc = TypeChecker::with_mode(&self.env, self.env.mode());
        let inferred_ty = tc.infer_type(&value).map_err(|e| {
            SpecError::TypeError(format!(
                "{label}: cannot infer elaborated value type: {e:?}"
            ))
        })?;
        self.align_value_universes(expected_ty, &inferred_ty, value, label)
    }

    /// Align independently inferred value universes with the declared type.
    /// Every parameter on either inferred type must participate in a one-to-one
    /// correspondence. Ambiguous/collapsing mappings are rejected rather than
    /// using the historical "first mapping wins" behavior.
    fn align_value_universes(
        &self,
        expected_ty: &Expr,
        inferred_ty: &Expr,
        value: Expr,
        label: &str,
    ) -> Result<Expr, SpecError> {
        let mut pairs: Vec<(Name, Name)> = Vec::new();
        Self::collect_expr_param_pairs(inferred_ty, expected_ty, &mut pairs, label)?;

        let mut inferred_params = Vec::new();
        Self::collect_level_params_expr(inferred_ty, &mut inferred_params);
        let mut expected_params = Vec::new();
        Self::collect_level_params_expr(expected_ty, &mut expected_params);

        for param in &inferred_params {
            if !pairs.iter().any(|(source, _)| source == param) {
                return Err(SpecError::TypeError(format!(
                    "{label}: cannot align inferred universe parameter `{param}` with declared type"
                )));
            }
        }
        for param in &expected_params {
            if !pairs.iter().any(|(_, target)| target == param) {
                return Err(SpecError::TypeError(format!(
                    "{label}: declared universe parameter `{param}` has no inferred value counterpart"
                )));
            }
        }

        let substitution: Vec<(Name, Level)> = pairs
            .iter()
            .filter(|(source, target)| source != target)
            .map(|(source, target)| (source.clone(), Level::param(target.clone())))
            .collect();
        let aligned_value = value.instantiate_level_params(&substitution);
        let aligned_inferred_ty = inferred_ty.instantiate_level_params(&substitution);

        let tc = TypeChecker::with_mode(&self.env, self.env.mode());
        if !tc.is_def_eq(&aligned_inferred_ty, expected_ty) {
            return Err(SpecError::TypeError(format!(
                "{label}: universe-aligned inferred type is not definitionally equal to declared type"
            )));
        }

        let mut aligned_value_params = Vec::new();
        Self::collect_level_params_expr(&aligned_value, &mut aligned_value_params);
        if let Some(extra) = aligned_value_params
            .iter()
            .find(|param| !expected_params.contains(param))
        {
            return Err(SpecError::TypeError(format!(
                "{label}: elaborated value retains unaligned universe parameter `{extra}`"
            )));
        }

        Ok(aligned_value)
    }

    /// Parallel structural walk that harvests universe correspondences wherever
    /// the inferred and expected types have matching expression structure.
    /// Definitional equality is checked separately, so beta-redex differences in
    /// a conclusion do not prevent binder-domain parameters from being aligned.
    fn collect_expr_param_pairs(
        inferred: &Expr,
        expected: &Expr,
        out: &mut Vec<(Name, Name)>,
        label: &str,
    ) -> Result<(), SpecError> {
        match (inferred.kind(), expected.kind()) {
            (ExprKind::Sort(inferred_level), ExprKind::Sort(expected_level)) => {
                Self::collect_level_param_pairs(inferred_level, expected_level, out, label)?;
            }
            (
                ExprKind::Const(inferred_name, inferred_levels),
                ExprKind::Const(expected_name, expected_levels),
            ) if inferred_name == expected_name
                && inferred_levels.len() == expected_levels.len() =>
            {
                for (inferred_level, expected_level) in
                    inferred_levels.iter().zip(expected_levels.iter())
                {
                    Self::collect_level_param_pairs(inferred_level, expected_level, out, label)?;
                }
            }
            (
                ExprKind::App(inferred_fn, inferred_arg),
                ExprKind::App(expected_fn, expected_arg),
            ) => {
                Self::collect_expr_param_pairs(inferred_fn, expected_fn, out, label)?;
                Self::collect_expr_param_pairs(inferred_arg, expected_arg, out, label)?;
            }
            (
                ExprKind::Pi(_, inferred_ty, inferred_body),
                ExprKind::Pi(_, expected_ty, expected_body),
            )
            | (
                ExprKind::Lam(_, inferred_ty, inferred_body),
                ExprKind::Lam(_, expected_ty, expected_body),
            ) => {
                Self::collect_expr_param_pairs(inferred_ty, expected_ty, out, label)?;
                Self::collect_expr_param_pairs(inferred_body, expected_body, out, label)?;
            }
            _ => {}
        }
        Ok(())
    }

    fn collect_level_param_pairs(
        inferred: &Level,
        expected: &Level,
        out: &mut Vec<(Name, Name)>,
        label: &str,
    ) -> Result<(), SpecError> {
        match (inferred, expected) {
            (Level::Param(source), Level::Param(target)) => {
                if let Some((_, previous_target)) = out.iter().find(|(name, _)| name == source) {
                    if previous_target != target {
                        return Err(SpecError::TypeError(format!(
                            "{label}: inferred universe `{source}` ambiguously aligns with both `{previous_target}` and `{target}`"
                        )));
                    }
                    return Ok(());
                }
                if let Some((previous_source, _)) = out.iter().find(|(_, name)| name == target) {
                    if previous_source != source {
                        return Err(SpecError::TypeError(format!(
                            "{label}: inferred universes `{previous_source}` and `{source}` would both collapse onto declared universe `{target}`"
                        )));
                    }
                }
                out.push((source.clone(), target.clone()));
            }
            (Level::Succ(inferred), Level::Succ(expected)) => {
                Self::collect_level_param_pairs(inferred, expected, out, label)?;
            }
            (Level::Max(inferred_a, inferred_b), Level::Max(expected_a, expected_b))
            | (Level::IMax(inferred_a, inferred_b), Level::IMax(expected_a, expected_b)) => {
                Self::collect_level_param_pairs(inferred_a, expected_a, out, label)?;
                Self::collect_level_param_pairs(inferred_b, expected_b, out, label)?;
            }
            _ => {}
        }
        Ok(())
    }
}

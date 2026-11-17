// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Checked metadata shared by source admission and existing declaration producers.
//! Metadata writes never bypass declaration checking or promote verification provenance.

use super::{ConstantKind, Declaration, EnvError, Environment, Reducibility};
use crate::{BinderInfo, Expr, ExprKind, Name};

fn invalid(name: &Name, detail: &'static str) -> EnvError {
    EnvError::InvalidDeclarationShape {
        init: "checked declaration metadata",
        decl: name.clone(),
        detail,
    }
}

fn strip_metadata(mut expr: &Expr) -> &Expr {
    while let ExprKind::MData(_, inner) = expr.kind() {
        expr = inner;
    }
    expr
}

impl Environment {
    /// Fully check a definition and retain its explicit ordinary unfolding hint.
    ///
    /// This runs the unchanged `add_decl` checks. Only after successful checked
    /// insertion does it retain the supplied hint, without replacing the type,
    /// value, kind or verification provenance. It exposes no operation on an
    /// already resident declaration: duplicate names still refuse.
    ///
    /// The legacy flag must agree exactly with the hint. Other declaration kinds
    /// refuse, and every returned error precedes any insertion or metadata write.
    pub fn add_decl_with_reducibility(
        &mut self,
        decl: Declaration,
        hint: Reducibility,
    ) -> Result<(), EnvError> {
        let name = match &decl {
            Declaration::Definition {
                name, is_reducible, ..
            } => {
                if *is_reducible != matches!(hint, Reducibility::Reducible) {
                    return Err(invalid(name, "reducibility disagrees with the legacy flag"));
                }
                name.clone()
            }
            Declaration::Theorem { name, .. }
            | Declaration::Opaque { name, .. }
            | Declaration::Axiom { name, .. } => {
                return Err(invalid(
                    name,
                    "an explicit ordinary hint requires a definition",
                ));
            }
        };
        self.add_decl(decl)?;
        // SOUNDNESS: add_decl has just checked and inserted this exact definition
        // under exclusive &mut access. This existing metadata write changes no
        // logical payload or provenance, and invalidates the generation cache.
        // Its only false case is an absent name, impossible after successful
        // insertion above; do not silently accept that invariant violation.
        assert!(
            self.set_reducibility(&name, hint),
            "a successfully checked definition must remain resident"
        );
        Ok(())
    }

    fn checked_metadata_type(&self, name: &Name) -> Result<Expr, EnvError> {
        let info = self
            .get_const(name)
            .ok_or_else(|| invalid(name, "metadata requires an existing exact declaration name"))?;
        let ty = info.type_.clone();
        if ty.has_fvar_quick()
            || ty.has_expr_mvar_quick()
            || ty.has_level_mvar_quick()
            || ty.has_loose_bvars_quick()
        {
            return Err(invalid(
                name,
                "metadata requires a closed declaration signature",
            ));
        }
        let _sort = crate::tc::TypeChecker::new(self)
            .infer_sort(&ty)
            .map_err(|source| EnvError::TypeCheckFailed {
                name: name.clone(),
                source,
            })?;
        Ok(ty)
    }

    /// Register typed names and binder kinds against a checked resident telescope.
    ///
    /// `complete` requires every syntactic Pi slot; otherwise a validated prefix
    /// records the declared arguments of a lifted helper returning a function.
    /// Anonymous and shadowed binder names remain valid. Exact `Name` identities
    /// are retained, including distinct names with equal diagnostic displays.
    /// Every refusal precedes mutation. This checks metadata, not a proof value,
    /// and leaves staged/recheck/verification state unchanged.
    pub fn add_checked_param_infos(
        &mut self,
        name: &Name,
        infos: Vec<(Name, BinderInfo)>,
        complete: bool,
    ) -> Result<(), EnvError> {
        let ty = self.checked_metadata_type(name)?;
        let mut at = strip_metadata(&ty);
        for (_, kind) in &infos {
            let ExprKind::Pi(expected, _, body) = at.kind() else {
                return Err(invalid(
                    name,
                    "parameter metadata exceeds the declaration telescope",
                ));
            };
            if *kind != expected.info {
                return Err(invalid(
                    name,
                    "parameter binder kind disagrees with the declaration",
                ));
            }
            at = strip_metadata(body);
        }
        if complete && matches!(at.kind(), ExprKind::Pi(..)) {
            return Err(invalid(
                name,
                "complete parameter metadata omits a declaration binder",
            ));
        }
        // SOUNDNESS: the exact resident name, well-formed signature and every
        // supplied Pi slot were checked above. This shared write neither admits
        // a constant nor changes its type, body or verification provenance.
        self.set_typed_param_infos(name.clone(), infos);
        Ok(())
    }

    /// Restrict unfolding of an existing definition/proof with a checked signature.
    ///
    /// This supports bootstrap proof parking without claiming that a deferred
    /// value has already been checked. It retains the value and its provenance;
    /// later declaration validation remains mandatory. No hint can be relaxed.
    pub fn restrict_checked_unfolding(&mut self, name: &Name) -> Result<(), EnvError> {
        let _signature = self.checked_metadata_type(name)?;
        let info = self.get_const(name).ok_or_else(|| {
            invalid(
                name,
                "unfolding restriction requires an existing declaration",
            )
        })?;
        if info.value.is_none()
            || !matches!(
                info.kind,
                ConstantKind::Definition | ConstantKind::Theorem | ConstantKind::Opaque
            )
        {
            return Err(invalid(
                name,
                "unfolding restriction requires a definition or proof value",
            ));
        }
        if self.get_reducibility(name) != Some(Reducibility::Irreducible) {
            // SOUNDNESS: this only removes a permitted delta step, retaining
            // the checked signature, value, kind and verification obligations.
            self.set_reducibility(name, Reducibility::Irreducible);
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "checked_metadata_tests.rs"]
mod tests;

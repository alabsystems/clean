// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Batteries aliases copy a constant's telescope rather than infer a new def.
use super::elaborate_decl::PrivateNameKind;
use super::{ElabCtx, ElabResult};
use crate::ElabError;
use clean_kernel::{ConstantKind, Expr, ExprKind, Level, LocalContext, Name, TypeChecker};
use clean_parser::{Attribute, DeclModifiers, SurfaceName};

impl ElabCtx<'_> {
    pub(super) fn elab_alias_inner(
        &mut self,
        name: &SurfaceName,
        target: &SurfaceName,
        direction: Option<bool>,
        attrs: &[Attribute],
        modifiers: &DeclModifiers,
    ) -> Result<ElabResult, ElabError> {
        let resolved = self.with_term_body_scope(|ctx| ctx.elab_ident(target))?;
        let ExprKind::Const(target, _) = resolved.kind() else {
            return Err(ElabError::Unsupported {
                feature: "alias target must be a global constant".into(),
            });
        };
        let target = target.clone();
        let info = self
            .env
            .get_const(&target)
            .cloned()
            .ok_or_else(|| ElabError::UnknownIdent(target.to_string()))?;
        let levels: Vec<_> = info
            .level_params
            .iter()
            .cloned()
            .map(Level::param)
            .collect();
        let mut value = Expr::const_(target, levels);
        let mut ty = info.type_.clone();
        let theorem = direction.is_some() || info.kind == ConstantKind::Theorem;
        if let Some(forward) = direction {
            let mut locals = LocalContext::new();
            let mut binders = Vec::new();
            // Batteries' `mkIffMpApp` opens the telescope with `forallTelescope`
            // (no reduction) and matches `Iff` with `Expr.iff?` (syntactic), so a
            // binder or an `Iff` behind any definition, `abbrev` included, is
            // refused there; never whnf here.
            while let ExprKind::Pi(binder, domain, body) = ty.kind() {
                let id = locals.push(Name::anon(), domain.as_ref().clone(), *binder);
                value = Expr::app(value, Expr::fvar(id));
                binders.push((id, *binder, domain.as_ref().clone()));
                ty = body.instantiate(&Expr::fvar(id));
            }
            let arguments = ty.get_app_args();
            if !matches!(ty.get_app_fn().kind(), ExprKind::Const(n, _) if *n == Name::from_string("Iff"))
                || arguments.len() != 2
            {
                return Err(ElabError::Unsupported {
                    feature: "Target theorem must have the form ∀ x y z, a ↔ b".into(),
                });
            }
            value = Expr::apps(
                Expr::const_(
                    Name::from_string(if forward { "Iff.mp" } else { "Iff.mpr" }),
                    vec![],
                ),
                [arguments[0].clone(), arguments[1].clone(), value],
            );
            drop(arguments);
            for (id, binder, domain) in binders.into_iter().rev() {
                value = Expr::lam(binder, domain, value.abstract_fvar(id));
            }
            ty = TypeChecker::new(self.env)
                .infer_type(&value)
                .map_err(|error| ElabError::Unsupported {
                    feature: error.to_string(),
                })?;
        }
        let kind = if theorem {
            PrivateNameKind::Theorem
        } else {
            PrivateNameKind::Definition
        };
        let name = self.kernel_decl_name(name, modifiers, kind);
        self.ensure_known_attributes(attrs)?;
        let mut alias_attrs = attrs.to_vec();
        if !theorem
            && !attrs.iter().any(|attr| {
                matches!(
                    attr,
                    Attribute::Reducible | Attribute::Semireducible | Attribute::Irreducible
                )
            })
        {
            match info.reducibility {
                clean_kernel::env::Reducibility::Reducible => {
                    alias_attrs.push(Attribute::Reducible)
                }
                clean_kernel::env::Reducibility::Irreducible => {
                    alias_attrs.push(Attribute::Irreducible)
                }
                _ => {}
            }
        }
        self.collect_attributes(&name, &alias_attrs);
        let mut modifiers = modifiers.clone();
        modifiers.is_noncomputable |= self.env.is_noncomputable(&info.name);
        modifiers.is_unsafe |= self.env.is_unsafe(&info.name);
        if theorem {
            Ok(ElabResult::Theorem {
                name,
                universe_params: info.level_params,
                ty,
                proof: value,
                modifiers,
            })
        } else {
            Ok(ElabResult::Definition {
                name,
                universe_params: info.level_params,
                ty,
                val: value,
                modifiers,
            })
        }
    }
}

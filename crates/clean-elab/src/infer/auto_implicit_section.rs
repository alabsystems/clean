// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Close declaration-owned autos inside the captured section telescope.

use super::*;
use crate::tactic::hypothesis::collect_fvars;

impl ElabCtx<'_> {
    /// Section autos precede section parameters, including dependencies of
    /// their domains. Both public closure and the internal recursive binding
    /// consume this same discovery-ordered packet.
    pub(super) fn section_auto_prefix_count(
        autos: &[(SurfaceName, FVarId, Expr)],
        mut used: std::collections::HashSet<FVarId>,
    ) -> usize {
        let mut captured = 0;
        loop {
            let before = captured;
            for (index, (_, id, domain)) in autos.iter().enumerate() {
                if index < captured || used.contains(id) {
                    captured = captured.max(index + 1);
                    used.extend(collect_fvars(domain));
                }
            }
            if captured == before {
                return captured;
            }
        }
    }

    pub(super) fn section_binder_count(binders: &[SurfaceBinder]) -> usize {
        binders
            .iter()
            .take_while(|binder| binder.name.is_section_variable())
            .count()
    }

    pub(super) fn wrap_decl_auto_implicits(
        &mut self,
        sections: usize,
        ty: Expr,
        val: Expr,
        autos: &[(SurfaceName, FVarId, Expr)],
        section_fvars: Option<&[FVarId]>,
    ) -> Result<(Expr, Expr, usize), ElabError> {
        let (ty, val, captured) =
            self.wrap_decl_auto_implicits_inner(sections, ty, Some(val), autos, section_fvars)?;
        let Some(val) = val else {
            return Err(ElabError::InternalInvariant(
                "declaration auto closure lost its value".to_string(),
            ));
        };
        Ok((ty, val, captured))
    }

    pub(super) fn wrap_decl_type_auto_implicits(
        &mut self,
        sections: usize,
        ty: Expr,
        autos: &[(SurfaceName, FVarId, Expr)],
        section_fvars: Option<&[FVarId]>,
    ) -> Result<(Expr, usize), ElabError> {
        let (ty, _, captured) =
            self.wrap_decl_auto_implicits_inner(sections, ty, None, autos, section_fvars)?;
        Ok((ty, captured))
    }

    fn wrap_decl_auto_implicits_inner(
        &mut self,
        sections: usize,
        mut ty: Expr,
        mut val: Option<Expr>,
        autos: &[(SurfaceName, FVarId, Expr)],
        section_fvars: Option<&[FVarId]>,
    ) -> Result<(Expr, Option<Expr>, usize), ElabError> {
        if sections == 0 || autos.is_empty() {
            return Ok(match val {
                Some(val) => {
                    let (ty, val) = Self::wrap_with_auto_implicits(ty, val, autos);
                    (ty, Some(val), 0)
                }
                None => (Self::wrap_type_with_auto_implicits(ty, autos), None, 0),
            });
        }
        let ids = match section_fvars {
            Some(ids) if ids.len() == sections => ids.to_vec(),
            Some(_) => {
                return Err(ElabError::InternalInvariant(
                    "declaration section telescope lost its local identities".to_string(),
                ));
            }
            None => {
                // These early lowerings have not retained the original
                // section locals or captured them in their forward binding.
                // Invented identities would let the public wrapper expose a
                // different calling convention from the recursive body.
                return Err(ElabError::Unsupported {
                    feature: "section auto-implicit closure requires the original section locals"
                        .to_string(),
                });
            }
        };
        let auto_ids: std::collections::HashSet<_> = autos.iter().map(|(_, id, _)| *id).collect();
        if autos.iter().any(|(_, _, domain)| {
            collect_fvars(domain)
                .iter()
                .any(|id| !auto_ids.contains(id) && !ids.contains(id))
        }) {
            return Err(ElabError::Unsupported {
                feature: "auto-implicit type captures an unavailable declaration binder"
                    .to_string(),
            });
        }
        let mut telescope = Vec::with_capacity(sections);
        let mut used = std::collections::HashSet::new();
        for id in ids {
            let ExprKind::Pi(info, domain, body) = ty.kind() else {
                return Err(ElabError::InternalInvariant(
                    "declaration auto closure expected its section type prefix".to_string(),
                ));
            };
            let (info, domain, body) = (*info, domain.as_ref().clone(), body.as_ref().clone());
            used.extend(collect_fvars(&domain));
            let value_domain = match val.take() {
                Some(value) => {
                    let ExprKind::Lam(value_info, value_domain, value_body) = value.kind() else {
                        return Err(ElabError::InternalInvariant(
                            "declaration auto closure expected its section value prefix"
                                .to_string(),
                        ));
                    };
                    used.extend(collect_fvars(value_domain));
                    let domain = (*value_info, value_domain.as_ref().clone());
                    val = Some(value_body.instantiate(&Expr::fvar(id)));
                    Some(domain)
                }
                None => None,
            };
            ty = body.instantiate(&Expr::fvar(id));
            telescope.push((id, info, domain, value_domain));
        }
        let captured = Self::section_auto_prefix_count(autos, used);
        let (captured_autos, own_autos) = autos.split_at(captured);
        if captured_autos.iter().any(|(_, _, domain)| {
            collect_fvars(domain)
                .iter()
                .any(|id| section_fvars.is_some_and(|sections| sections.contains(id)))
        }) {
            return Err(ElabError::Unsupported {
                feature: "section auto-implicit depends on an explicitly provided section binder"
                    .to_string(),
            });
        }
        match val.take() {
            Some(value) => {
                let (new_ty, new_val) = Self::wrap_with_auto_implicits(ty, value, own_autos);
                ty = new_ty;
                val = Some(new_val);
            }
            None => ty = Self::wrap_type_with_auto_implicits(ty, own_autos),
        }
        for (id, info, domain, value_domain) in telescope.into_iter().rev() {
            ty = Expr::pi(info, domain, ty.abstract_fvar(id));
            if let (Some(value), Some((info, domain))) = (val.take(), value_domain) {
                val = Some(Expr::lam(info, domain, value.abstract_fvar(id)));
            }
        }
        Ok(match val {
            Some(value) => {
                let (ty, value) = Self::wrap_with_auto_implicits(ty, value, captured_autos);
                (ty, Some(value), captured)
            }
            None => (
                Self::wrap_type_with_auto_implicits(ty, captured_autos),
                None,
                captured,
            ),
        })
    }
}

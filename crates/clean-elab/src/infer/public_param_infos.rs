// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact names of the header telescope that elaboration actually publishes.

use clean_kernel::{BinderInfo, Environment, Expr, FVarId, Name};
use clean_parser::{SurfaceBinder, SurfaceName};

use super::{convert_binder_info, ElabCtx, ElabError, ElabResult};

#[derive(Debug)]
pub(crate) struct PublicParamInfos {
    name: Name,
    infos: Vec<(Name, BinderInfo)>,
    constructor_type: Option<Expr>,
}

impl ElabCtx<'_> {
    /// Autos and section binders close in different positions. Retain their
    /// identities here, before the kernel Pi nodes discard binder names.
    pub(super) fn note_public_param_infos(
        &mut self,
        decl: &Name,
        binders: &[SurfaceBinder],
        autos: &[(SurfaceName, FVarId, Expr)],
        captured: usize,
    ) {
        let names: Vec<_> = binders.iter().map(|b| b.name.clone()).collect();
        let kinds: Vec<_> = binders
            .iter()
            .map(|b| convert_binder_info(b.info))
            .collect();
        self.note_public_param_infos_from_names(decl, &names, &kinds, autos, captured);
    }

    pub(super) fn note_public_param_infos_from_names(
        &mut self,
        decl: &Name,
        names: &[SurfaceName],
        kinds: &[BinderInfo],
        autos: &[(SurfaceName, FVarId, Expr)],
        captured: usize,
    ) {
        let sections = names.iter().take_while(|n| n.is_section_variable()).count();
        let kept = self
            .section_prune_outcome
            .as_ref()
            .filter(|p| p.decl == *decl);
        let auto_infos = |slice: &[(SurfaceName, FVarId, Expr)]| {
            slice
                .iter()
                .map(|(n, _, _)| (n.name().clone(), BinderInfo::Implicit))
                .collect::<Vec<_>>()
        };
        let Some((captured_autos, own_autos)) = autos.split_at_checked(captured) else {
            return;
        };
        if kinds.len() != names.len() {
            return;
        }
        let mut infos = auto_infos(captured_autos);
        infos.extend(
            names[..sections]
                .iter()
                .zip(&kinds[..sections])
                .enumerate()
                .filter(|(i, _)| kept.is_none_or(|p| p.kept.get(*i).copied().unwrap_or(true)))
                .map(|(_, (n, k))| (n.name().clone(), *k)),
        );
        infos.extend(auto_infos(own_autos));
        infos.extend(
            names[sections..]
                .iter()
                .zip(&kinds[sections..])
                .map(|(n, k)| (n.name().clone(), *k)),
        );
        if !infos.is_empty() {
            self.public_param_infos.push(PublicParamInfos {
                name: decl.clone(),
                infos,
                constructor_type: None,
            });
        }
    }

    pub(super) fn note_constructor_param_infos(
        &mut self,
        name: &Name,
        type_: &Expr,
        infos: Vec<(Name, BinderInfo)>,
    ) {
        if infos.iter().any(|(name, _)| !name.is_anon()) {
            self.public_param_infos.push(PublicParamInfos {
                name: name.clone(),
                infos,
                constructor_type: Some(type_.clone()),
            });
        }
    }

    /// Equation theorems close their actual auto packet inside the body stage.
    /// Their outer finishing stage still owns section pruning.
    pub(super) fn prune_public_param_infos(&mut self, decl: &Name, offset: usize, kept: &[bool]) {
        for row in self
            .public_param_infos
            .iter_mut()
            .filter(|r| r.name == *decl)
        {
            let mut position = 0;
            row.infos.retain(|_| {
                let i = position;
                position += 1;
                i < offset || kept.get(i - offset).copied().unwrap_or(true)
            });
        }
    }

    /// Publish only rows belonging to successful leaves of this result. A
    /// failed sibling or a staging-header computation cannot name an unrelated
    /// constant already present in the registration environment.
    pub(crate) fn take_public_param_infos(
        &mut self,
        result: Option<&ElabResult>,
    ) -> Vec<PublicParamInfos> {
        let mut leaves = Vec::new();
        if let Some(result) = result {
            result.leaf_decls(&mut leaves);
        }
        std::mem::take(&mut self.public_param_infos)
            .into_iter()
            .filter(|row| {
                leaves.iter().any(|leaf| match leaf {
                    ElabResult::Definition { name, .. }
                    | ElabResult::Theorem { name, .. }
                    | ElabResult::Axiom { name, .. }
                    | ElabResult::Opaque { name, .. }
                    | ElabResult::Instance { name, .. } => *name == row.name,
                    ElabResult::Inductive { constructors, .. } => {
                        constructors.iter().any(|(name, _)| *name == row.name)
                    }
                    _ => false,
                })
            })
            .collect()
    }
}

impl PublicParamInfos {
    pub(crate) fn register(mut self, env: &mut Environment) -> Result<(), ElabError> {
        let Some(constant) = env.get_const(&self.name) else {
            return Ok(());
        };
        if self
            .constructor_type
            .as_ref()
            .is_some_and(|type_| *type_ != constant.type_)
        {
            // Kernel promotion can rebuild a family telescope. A constructor
            // with a rearranged signature retains the original metadata path.
            return Ok(());
        }
        let kinds = ElabCtx::pi_telescope_binder_infos(&constant.type_, self.infos.len());
        if kinds.len() != self.infos.len()
            || kinds.iter().zip(&self.infos).any(|(a, (_, b))| a != b)
        {
            // A lowering changed the header without updating its metadata. Do
            // not leave a shorter surface row naming the wrong Pi positions.
            tracing::debug!(name = %self.name, "public parameter metadata does not match its registered telescope");
            self.infos.clear();
        }
        env.add_checked_param_infos(&self.name, self.infos, false)
            .map_err(|error| ElabError::KernelRegistrationFailed {
                operation: "public parameter metadata".into(),
                detail: error.to_string(),
            })
    }
}

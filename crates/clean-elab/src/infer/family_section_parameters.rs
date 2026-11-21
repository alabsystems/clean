// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Section parameters of structures and inductives. Lean's `withUsed` examines
//! elaborated declarations before any constructor self-reference gains these
//! arguments. A local required by another retained parameter is retained too.

use super::ElabCtx;
use clean_kernel::{BinderInfo, Expr, FVarId};
use clean_parser::SurfaceBinder;

pub(super) fn section_prefix(binders: &[SurfaceBinder]) -> usize {
    binders
        .iter()
        .take_while(|b| b.name.is_section_variable())
        .count()
}

pub(super) fn constructor_parameter(info: BinderInfo) -> BinderInfo {
    if info == BinderInfo::Default {
        BinderInfo::Implicit
    } else {
        info
    }
}

impl ElabCtx<'_> {
    pub(super) fn used_family_section<'a>(
        &self,
        count: usize,
        ids: &[FVarId],
        domains: &'a [Expr],
        uses: impl Iterator<Item = &'a Expr>,
    ) -> Vec<usize> {
        if count == 0 {
            return Vec::new();
        }
        let roots: Vec<_> = domains[count..]
            .iter()
            .chain(uses)
            .map(|type_| self.metas.instantiate(type_))
            .collect();
        let used = self.demand_local_ctx(&roots.iter().collect::<Vec<_>>());
        (0..count).filter(|&i| used.get(ids[i]).is_some()).collect()
    }
}

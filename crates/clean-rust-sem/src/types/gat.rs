// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{Lifetime, RustType, TypeParamDef};
use crate::stmt::{GenericParam, TraitImplInfo, WherePredicate};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct GatDef {
    pub name: String,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub type_params: Vec<TypeParamDef>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub lifetime_params: Vec<String>,
    pub default_ty: Option<RustType>,
}
impl GatDef {
    #[must_use]
    pub fn from_generic_params(
        name: String,
        generic_params: &[GenericParam],
        default_ty: Option<RustType>,
    ) -> Self {
        let (mut type_params, mut lifetime_params) = (Vec::new(), Vec::new());
        for param in generic_params {
            match param {
                GenericParam::Type(param) => type_params.push(param.clone()),
                GenericParam::Lifetime(name) => lifetime_params.push(name.clone()),
            }
        }
        Self {
            name,
            type_params,
            lifetime_params,
            default_ty,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct GatProjection {
    pub self_ty: RustType,
    pub trait_name: String,
    pub assoc_name: String,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub type_args: Vec<RustType>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub lifetime_args: Vec<Lifetime>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub const_args: Vec<super::ConstGenericArg>,
}
impl GatProjection {
    #[must_use]
    pub fn new(
        self_ty: RustType,
        trait_name: String,
        assoc_name: String,
        type_args: Vec<RustType>,
        lifetime_args: Vec<Lifetime>,
    ) -> Self {
        Self {
            self_ty,
            trait_name,
            assoc_name,
            type_args,
            lifetime_args,
            const_args: vec![],
        }
    }
}
impl TryFrom<&RustType> for GatProjection {
    type Error = &'static str;
    fn try_from(ty: &RustType) -> Result<Self, Self::Error> {
        match ty {
            RustType::TypeProjection {
                self_ty,
                trait_name,
                assoc_name,
                assoc_type_args,
                assoc_lifetime_args,
                ..
            } => Ok(Self::new(
                (**self_ty).clone(),
                trait_name.clone(),
                assoc_name.clone(),
                assoc_type_args.clone(),
                assoc_lifetime_args.clone(),
            )),
            _ => Err("type is not a GAT projection"),
        }
    }
}
impl From<GatProjection> for RustType {
    fn from(projection: GatProjection) -> Self {
        RustType::TypeProjection {
            self_ty: Box::new(projection.self_ty),
            trait_name: projection.trait_name,
            assoc_name: projection.assoc_name,
            assoc_type_args: projection.type_args,
            assoc_lifetime_args: projection.lifetime_args,
            const_args: vec![],
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct GatSubstitution {
    pub self_ty: Option<RustType>,
    pub type_subst: HashMap<u32, RustType>,
    pub lifetime_subst: HashMap<String, Lifetime>,
}
impl GatSubstitution {
    pub fn new(def: &GatDef, type_args: &[RustType], lifetime_args: &[Lifetime]) -> Option<Self> {
        if def.type_params.len() != type_args.len()
            || def.lifetime_params.len() != lifetime_args.len()
        {
            return None;
        }
        Some(Self {
            self_ty: None,
            type_subst: def
                .type_params
                .iter()
                .zip(type_args.iter())
                .map(|(param, arg)| (param.id, arg.clone()))
                .collect(),
            lifetime_subst: def
                .lifetime_params
                .iter()
                .zip(lifetime_args.iter())
                .map(|(name, lifetime)| (name.clone(), lifetime.clone()))
                .collect(),
        })
    }
    pub fn for_projection(
        def: &GatDef,
        impl_self_ty: &RustType,
        projection: &GatProjection,
    ) -> Option<Self> {
        let (self_type_subst, self_lifetime_subst) =
            impl_self_ty.infer_generic_bindings(&projection.self_ty)?;
        Some(
            Self::new(def, &projection.type_args, &projection.lifetime_args)?.with_impl_bindings(
                projection.self_ty.clone(),
                self_type_subst,
                self_lifetime_subst,
            ),
        )
    }
    #[must_use]
    pub fn with_impl_bindings(
        mut self,
        self_ty: RustType,
        self_type_subst: HashMap<u32, RustType>,
        self_lifetime_subst: HashMap<String, Lifetime>,
    ) -> Self {
        self.self_ty = Some(self_ty);
        self.type_subst.extend(self_type_subst);
        for (name, lifetime) in self_lifetime_subst {
            self.lifetime_subst.entry(name).or_insert(lifetime);
        }
        self
    }
    #[must_use]
    pub fn apply(&self, ty: &RustType) -> RustType {
        let ty = self
            .self_ty
            .as_ref()
            .map_or_else(|| ty.clone(), |self_ty| ty.substitute_self_type(self_ty));
        ty.substitute_type_params(&self.type_subst)
            .substitute_named_lifetimes(&self.lifetime_subst)
    }
    #[must_use]
    pub fn type_binding(&self, id: u32) -> Option<&RustType> {
        self.type_subst.get(&id)
    }
    #[must_use]
    pub fn lifetime_binding(&self, name: &str) -> Option<&Lifetime> {
        self.lifetime_subst.get(name)
    }
}
#[must_use]
pub fn resolve_gat(projection: &GatProjection, impl_info: &TraitImplInfo) -> Option<RustType> {
    if impl_info.trait_name != projection.trait_name {
        return None;
    }
    let assoc = impl_info.associated_types.get(&projection.assoc_name)?;
    let def =
        GatDef::from_generic_params(projection.assoc_name.clone(), &assoc.generic_params, None);
    Some(GatSubstitution::for_projection(&def, &impl_info.self_ty, projection)?.apply(&assoc.ty))
}
pub fn validate_gat_bounds(
    def: &GatDef,
    where_clause: &[WherePredicate],
    subst: &GatSubstitution,
    mut type_satisfies_bound: impl FnMut(&RustType, &str) -> bool,
) -> Result<(), String> {
    for param in &def.type_params {
        let concrete_ty = subst
            .type_binding(param.id)
            .map(|ty| subst.apply(ty))
            .ok_or_else(|| format!("missing type argument for GAT parameter `{}`", param.name))?;
        for bound in &param.bounds {
            validate_bound(
                &def.name,
                &param.name,
                &concrete_ty,
                bound,
                subst,
                &mut type_satisfies_bound,
            )?;
        }
    }
    for predicate in where_clause {
        match predicate {
            WherePredicate::Type { ty, bounds } => {
                let concrete_ty = subst.apply(ty);
                for bound in bounds {
                    validate_bound(
                        &def.name,
                        "where-clause type",
                        &concrete_ty,
                        bound,
                        subst,
                        &mut type_satisfies_bound,
                    )?;
                }
            }
            WherePredicate::Lifetime { lifetime, bounds } => {
                let concrete = resolve_lifetime_name(lifetime, subst)?;
                for bound in bounds {
                    if !concrete.outlives(&resolve_lifetime_bound(bound, subst)?) {
                        return Err(format!(
                            "GAT `{}` requires lifetime `{lifetime}` to outlive `{bound}`",
                            def.name
                        ));
                    }
                }
            }
        }
    }
    Ok(())
}
fn validate_bound(
    gat_name: &str,
    subject: &str,
    concrete_ty: &RustType,
    bound: &str,
    subst: &GatSubstitution,
    type_satisfies_bound: &mut impl FnMut(&RustType, &str) -> bool,
) -> Result<(), String> {
    if let Some(bound) = bound.strip_prefix('\'') {
        if type_outlives(concrete_ty, &resolve_lifetime_name(bound, subst)?) {
            Ok(())
        } else {
            Err(format!(
                "GAT `{gat_name}` requires `{subject}` to outlive `'{bound}`"
            ))
        }
    } else if type_satisfies_bound(concrete_ty, bound) {
        Ok(())
    } else {
        Err(format!(
            "GAT `{gat_name}` requires `{subject}` to satisfy `{bound}`, got {concrete_ty:?}"
        ))
    }
}
fn resolve_lifetime_name(name: &str, subst: &GatSubstitution) -> Result<Lifetime, String> {
    if name == "static" {
        Ok(Lifetime::Static)
    } else {
        subst
            .lifetime_binding(name)
            .cloned()
            .ok_or_else(|| format!("missing lifetime argument for `{name}`"))
    }
}
fn resolve_lifetime_bound(bound: &str, subst: &GatSubstitution) -> Result<Lifetime, String> {
    resolve_lifetime_name(
        bound
            .strip_prefix('\'')
            .ok_or_else(|| format!("invalid lifetime bound `{bound}`"))?,
        subst,
    )
}
fn type_outlives(ty: &RustType, required: &Lifetime) -> bool {
    let mut lifetimes = Vec::new();
    collect_lifetimes(ty, &mut lifetimes);
    lifetimes
        .into_iter()
        .all(|lifetime| lifetime.outlives(required))
}
fn collect_lifetimes(ty: &RustType, out: &mut Vec<Lifetime>) {
    match ty {
        RustType::Reference {
            lifetime, inner, ..
        } => {
            out.push(lifetime.clone());
            collect_lifetimes(inner, out);
        }
        RustType::Named {
            type_args,
            lifetime_args,
            ..
        } => {
            out.extend(lifetime_args.iter().cloned());
            for arg in type_args {
                collect_lifetimes(arg, out);
            }
        }
        RustType::RawPtr { inner, .. }
        | RustType::Atomic { inner }
        | RustType::Box { inner }
        | RustType::Cell { inner }
        | RustType::RefCell { inner }
        | RustType::UnsafeCell { inner }
        | RustType::Pin { inner }
        | RustType::Option { inner } => collect_lifetimes(inner, out),
        RustType::Array { element, .. } | RustType::Vec { element } => {
            collect_lifetimes(element, out)
        }
        RustType::Slice { elem } => collect_lifetimes(elem, out),
        RustType::Tuple(elems) => elems.iter().for_each(|elem| collect_lifetimes(elem, out)),
        RustType::Function { params, ret } => {
            params
                .iter()
                .for_each(|param| collect_lifetimes(param, out));
            collect_lifetimes(ret, out);
        }
        RustType::Result { ok, err } => {
            collect_lifetimes(ok, out);
            collect_lifetimes(err, out);
        }
        RustType::Closure {
            params,
            ret,
            captures,
            ..
        } => {
            params
                .iter()
                .for_each(|param| collect_lifetimes(param, out));
            collect_lifetimes(ret, out);
            captures
                .iter()
                .for_each(|(_, ty, _)| collect_lifetimes(ty, out));
        }
        RustType::TypeProjection {
            self_ty,
            assoc_type_args,
            assoc_lifetime_args,
            ..
        } => {
            collect_lifetimes(self_ty, out);
            out.extend(assoc_lifetime_args.iter().cloned());
            assoc_type_args
                .iter()
                .for_each(|arg| collect_lifetimes(arg, out));
        }
        _ => {}
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::stmt::{AssociatedTypeValue, GenericParam, TraitImplInfo, WherePredicate};
    use crate::types::{IntType, Mutability, TypeVar};
    use std::collections::HashMap;
    fn tp(id: u32, name: &str, bounds: &[&str]) -> TypeParamDef {
        TypeParamDef {
            id,
            name: name.to_string(),
            bounds: bounds.iter().map(|bound| (*bound).to_string()).collect(),
        }
    }
    fn named(name: &str) -> RustType {
        RustType::Named {
            name: name.to_string(),
            type_args: vec![],
            lifetime_args: vec![],
            const_args: vec![],
        }
    }
    fn named1(name: &str, arg: RustType) -> RustType {
        RustType::Named {
            name: name.to_string(),
            type_args: vec![arg],
            lifetime_args: vec![],
            const_args: vec![],
        }
    }
    fn tvar(param: &TypeParamDef) -> RustType {
        RustType::TypeParam(TypeVar {
            id: param.id,
            name: Some(param.name.clone()),
        })
    }
    #[test]
    fn gat_def_splits_type_and_lifetime_params() {
        let param = tp(7, "T", &["Clone"]);
        let def = GatDef::from_generic_params(
            "Item".to_string(),
            &[
                GenericParam::lifetime("a"),
                GenericParam::type_param(param.clone()),
            ],
            Some(RustType::Unit),
        );
        assert_eq!(def.type_params, vec![param]);
        assert_eq!(def.lifetime_params, vec!["a".to_string()]);
        assert_eq!(def.default_ty, Some(RustType::Unit));
    }
    #[test]
    fn gat_projection_round_trips_with_rust_type() {
        let projection = GatProjection::new(
            named1("Vec", RustType::Int(IntType::I32)),
            "IntoIterator".to_string(),
            "Item".to_string(),
            vec![],
            vec![Lifetime::Named("a".to_string())],
        );
        assert_eq!(
            GatProjection::try_from(&RustType::from(projection.clone())),
            Ok(projection)
        );
    }
    #[test]
    fn gat_substitution_applies_self_and_local_args() {
        let param = tp(1, "T", &[]);
        let def = GatDef {
            name: "Item".to_string(),
            type_params: vec![param.clone()],
            lifetime_params: vec!["a".to_string()],
            default_ty: None,
        };
        let subst = GatSubstitution::new(
            &def,
            &[RustType::Int(IntType::I32)],
            &[Lifetime::Named("loan".to_string())],
        )
        .expect("arity should match")
        .with_impl_bindings(named("Book"), HashMap::new(), HashMap::new());
        let body = RustType::Tuple(vec![
            named("Self"),
            RustType::Reference {
                lifetime: Lifetime::Named("a".to_string()),
                mutability: Mutability::Shared,
                inner: Box::new(tvar(&param)),
            },
        ]);
        assert_eq!(
            subst.apply(&body),
            RustType::Tuple(vec![
                named("Book"),
                RustType::Reference {
                    lifetime: Lifetime::Named("loan".to_string()),
                    mutability: Mutability::Shared,
                    inner: Box::new(RustType::Int(IntType::I32)),
                },
            ])
        );
    }
    #[test]
    fn resolve_gat_substitutes_impl_self_and_projection_args() {
        let param = tp(2, "T", &[]);
        let impl_info = TraitImplInfo {
            trait_name: "LendingIterator".to_string(),
            self_ty: named1("Container", tvar(&param)),
            methods: HashMap::new(),
            associated_types: HashMap::from([(
                "Item".to_string(),
                AssociatedTypeValue {
                    generic_params: vec![GenericParam::lifetime("a")],
                    where_clause: vec![],
                    ty: RustType::Reference {
                        lifetime: Lifetime::Named("a".to_string()),
                        mutability: Mutability::Shared,
                        inner: Box::new(tvar(&param)),
                    },
                },
            )]),
        };
        let projection = GatProjection::new(
            named1("Container", RustType::Int(IntType::I32)),
            "LendingIterator".to_string(),
            "Item".to_string(),
            vec![],
            vec![Lifetime::Named("iter".to_string())],
        );
        assert_eq!(
            resolve_gat(&projection, &impl_info),
            Some(RustType::Reference {
                lifetime: Lifetime::Named("iter".to_string()),
                mutability: Mutability::Shared,
                inner: Box::new(RustType::Int(IntType::I32)),
            })
        );
    }
    #[test]
    fn validate_gat_bounds_checks_type_and_lifetime_predicates() {
        let param = tp(3, "T", &["Clone"]);
        let def = GatDef {
            name: "Item".to_string(),
            type_params: vec![param.clone()],
            lifetime_params: vec!["a".to_string(), "b".to_string()],
            default_ty: None,
        };
        let where_clause = vec![
            WherePredicate::Type {
                ty: tvar(&param),
                bounds: vec!["Clone".to_string()],
            },
            WherePredicate::Lifetime {
                lifetime: "a".to_string(),
                bounds: vec!["'b".to_string()],
            },
        ];
        let ok = GatSubstitution::new(
            &def,
            &[named("Widget")],
            &[
                Lifetime::Named("loan".to_string()),
                Lifetime::Named("loan".to_string()),
            ],
        )
        .expect("arity should match");
        assert!(validate_gat_bounds(&def, &where_clause, &ok, |ty, bound| {
            ty.name().as_deref() == Some("Widget") && bound == "Clone"
        })
        .is_ok());
        let err = validate_gat_bounds(
            &def,
            &where_clause,
            &GatSubstitution::new(
                &def,
                &[named("Unclonable")],
                &[Lifetime::Named("short".to_string()), Lifetime::Static],
            )
            .expect("arity should match"),
            |_, _| false,
        )
        .expect_err("bounds should fail");
        assert!(err.contains("Clone") || err.contains("outlive"));
    }
}

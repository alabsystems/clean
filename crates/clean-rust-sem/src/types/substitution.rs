// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Type substitution and normalization for `RustType`.
//!
//! - `substitute_self_type`: replace placeholder `Self` with a concrete type
//! - `substitute_type_params`: replace `TypeParam` variables with concrete types
//! - `erase_anonymous_lifetimes`: canonicalize elided lifetime identity

use std::collections::HashMap;

use super::{
    ConstGenericArg, ConstGenericEval, ConstGenericUnifier, ConstGenericValue, ConstParamDef,
    Lifetime, RustType, TypeVar,
};

/// Recursively transform a `RustType` by applying `f` at every node.
///
/// If `f` returns `Some(replacement)`, the replacement is used (without
/// further recursion into it). If `f` returns `None`, the standard
/// recursive descent into children proceeds.
fn map_type(ty: &RustType, f: &dyn Fn(&RustType) -> Option<RustType>) -> RustType {
    if let Some(replacement) = f(ty) {
        return replacement;
    }
    match ty {
        RustType::Reference {
            lifetime,
            mutability,
            inner,
        } => RustType::Reference {
            lifetime: lifetime.clone(),
            mutability: *mutability,
            inner: Box::new(map_type(inner, f)),
        },
        RustType::RawPtr { mutability, inner } => RustType::RawPtr {
            mutability: *mutability,
            inner: Box::new(map_type(inner, f)),
        },
        RustType::Array { element, len } => RustType::Array {
            element: Box::new(map_type(element, f)),
            len: len.clone(),
        },
        RustType::Slice { elem } => RustType::Slice {
            elem: Box::new(map_type(elem, f)),
        },
        RustType::Tuple(elems) => RustType::Tuple(elems.iter().map(|e| map_type(e, f)).collect()),
        RustType::Function { params, ret } => RustType::Function {
            params: params.iter().map(|p| map_type(p, f)).collect(),
            ret: Box::new(map_type(ret, f)),
        },
        RustType::Named {
            name,
            type_args,
            lifetime_args,
            const_args,
        } => RustType::Named {
            name: name.clone(),
            type_args: type_args.iter().map(|a| map_type(a, f)).collect(),
            lifetime_args: lifetime_args.clone(),
            const_args: const_args.clone(),
        },
        RustType::Box { inner }
        | RustType::Cell { inner }
        | RustType::RefCell { inner }
        | RustType::UnsafeCell { inner }
        | RustType::Pin { inner }
        | RustType::Option { inner } => {
            let mapped = Box::new(map_type(inner, f));
            match ty {
                RustType::Box { .. } => RustType::Box { inner: mapped },
                RustType::Cell { .. } => RustType::Cell { inner: mapped },
                RustType::RefCell { .. } => RustType::RefCell { inner: mapped },
                RustType::UnsafeCell { .. } => RustType::UnsafeCell { inner: mapped },
                RustType::Pin { .. } => RustType::Pin { inner: mapped },
                _ => RustType::Option { inner: mapped },
            }
        }
        RustType::Result { ok, err } => RustType::Result {
            ok: Box::new(map_type(ok, f)),
            err: Box::new(map_type(err, f)),
        },
        RustType::Vec { element } => RustType::Vec {
            element: Box::new(map_type(element, f)),
        },
        RustType::Closure {
            params,
            ret,
            captures,
            kind,
        } => RustType::Closure {
            params: params.iter().map(|p| map_type(p, f)).collect(),
            ret: Box::new(map_type(ret, f)),
            captures: captures
                .iter()
                .map(|(n, t, m)| (n.clone(), map_type(t, f), *m))
                .collect(),
            kind: *kind,
        },
        RustType::TypeProjection {
            self_ty,
            trait_name,
            assoc_name,
            assoc_type_args,
            assoc_lifetime_args,
            const_args,
        } => RustType::TypeProjection {
            self_ty: Box::new(map_type(self_ty, f)),
            trait_name: trait_name.clone(),
            assoc_name: assoc_name.clone(),
            assoc_type_args: assoc_type_args.iter().map(|arg| map_type(arg, f)).collect(),
            assoc_lifetime_args: assoc_lifetime_args.clone(),
            const_args: const_args.clone(),
        },
        _ => ty.clone(),
    }
}

impl RustType {
    /// Replace placeholder `Self` occurrences with a concrete implementing type.
    pub(crate) fn substitute_self_type(&self, concrete_self_ty: &RustType) -> RustType {
        map_type(self, &|ty| match ty {
            RustType::Named { name, .. } if name == "Self" => Some(concrete_self_ty.clone()),
            _ => None,
        })
    }

    /// Substitute generic type parameters with concrete types.
    ///
    /// Replaces every `TypeParam(TypeVar { id, .. })` whose `id` appears in
    /// `subst` with the mapped concrete type. Type parameters not in the map
    /// are left unchanged (open substitution).
    pub(crate) fn substitute_type_params(&self, subst: &HashMap<u32, RustType>) -> RustType {
        if subst.is_empty() {
            return self.clone();
        }
        map_type(self, &|ty| match ty {
            RustType::TypeParam(TypeVar { id, .. }) => subst.get(id).cloned(),
            _ => None,
        })
    }

    pub(crate) fn substitute_const_params(
        &self,
        subst: &HashMap<String, ConstGenericValue>,
    ) -> RustType {
        if subst.is_empty() {
            return self.clone();
        }
        match self {
            RustType::Reference {
                lifetime,
                mutability,
                inner,
            } => RustType::Reference {
                lifetime: lifetime.clone(),
                mutability: *mutability,
                inner: Box::new(inner.substitute_const_params(subst)),
            },
            RustType::RawPtr { mutability, inner } => RustType::RawPtr {
                mutability: *mutability,
                inner: Box::new(inner.substitute_const_params(subst)),
            },
            RustType::Array { element, len } => RustType::Array {
                element: Box::new(element.substitute_const_params(subst)),
                len: Self::substitute_const_arg(len, subst),
            },
            RustType::Slice { elem } => RustType::Slice {
                elem: Box::new(elem.substitute_const_params(subst)),
            },
            RustType::Tuple(elems) => RustType::Tuple(
                elems
                    .iter()
                    .map(|elem| elem.substitute_const_params(subst))
                    .collect(),
            ),
            RustType::Function { params, ret } => RustType::Function {
                params: params
                    .iter()
                    .map(|param| param.substitute_const_params(subst))
                    .collect(),
                ret: Box::new(ret.substitute_const_params(subst)),
            },
            RustType::Named {
                name,
                type_args,
                lifetime_args,
                const_args,
            } => RustType::Named {
                name: name.clone(),
                type_args: type_args
                    .iter()
                    .map(|arg| arg.substitute_const_params(subst))
                    .collect(),
                lifetime_args: lifetime_args.clone(),
                const_args: const_args
                    .iter()
                    .map(|arg| Self::substitute_const_arg(arg, subst))
                    .collect(),
            },
            RustType::Box { inner } => RustType::Box {
                inner: Box::new(inner.substitute_const_params(subst)),
            },
            RustType::Cell { inner } => RustType::Cell {
                inner: Box::new(inner.substitute_const_params(subst)),
            },
            RustType::RefCell { inner } => RustType::RefCell {
                inner: Box::new(inner.substitute_const_params(subst)),
            },
            RustType::UnsafeCell { inner } => RustType::UnsafeCell {
                inner: Box::new(inner.substitute_const_params(subst)),
            },
            RustType::Pin { inner } => RustType::Pin {
                inner: Box::new(inner.substitute_const_params(subst)),
            },
            RustType::Option { inner } => RustType::Option {
                inner: Box::new(inner.substitute_const_params(subst)),
            },
            RustType::Result { ok, err } => RustType::Result {
                ok: Box::new(ok.substitute_const_params(subst)),
                err: Box::new(err.substitute_const_params(subst)),
            },
            RustType::Vec { element } => RustType::Vec {
                element: Box::new(element.substitute_const_params(subst)),
            },
            RustType::Closure {
                params,
                ret,
                captures,
                kind,
            } => RustType::Closure {
                params: params
                    .iter()
                    .map(|param| param.substitute_const_params(subst))
                    .collect(),
                ret: Box::new(ret.substitute_const_params(subst)),
                captures: captures
                    .iter()
                    .map(|(name, ty, mutability)| {
                        (name.clone(), ty.substitute_const_params(subst), *mutability)
                    })
                    .collect(),
                kind: *kind,
            },
            RustType::TypeProjection {
                self_ty,
                trait_name,
                assoc_name,
                assoc_type_args,
                assoc_lifetime_args,
                const_args,
            } => RustType::TypeProjection {
                self_ty: Box::new(self_ty.substitute_const_params(subst)),
                trait_name: trait_name.clone(),
                assoc_name: assoc_name.clone(),
                assoc_type_args: assoc_type_args
                    .iter()
                    .map(|arg| arg.substitute_const_params(subst))
                    .collect(),
                assoc_lifetime_args: assoc_lifetime_args.clone(),
                const_args: const_args.clone(),
            },
            _ => self.clone(),
        }
    }

    /// Substitute named lifetimes with concrete lifetime arguments.
    pub(crate) fn substitute_named_lifetimes(&self, subst: &HashMap<String, Lifetime>) -> RustType {
        if subst.is_empty() {
            return self.clone();
        }
        match self {
            RustType::Reference {
                lifetime,
                mutability,
                inner,
            } => RustType::Reference {
                lifetime: Self::substitute_lifetime(lifetime, subst),
                mutability: *mutability,
                inner: Box::new(inner.substitute_named_lifetimes(subst)),
            },
            RustType::RawPtr { mutability, inner } => RustType::RawPtr {
                mutability: *mutability,
                inner: Box::new(inner.substitute_named_lifetimes(subst)),
            },
            RustType::Array { element, len } => RustType::Array {
                element: Box::new(element.substitute_named_lifetimes(subst)),
                len: len.clone(),
            },
            RustType::Slice { elem } => RustType::Slice {
                elem: Box::new(elem.substitute_named_lifetimes(subst)),
            },
            RustType::Tuple(elems) => RustType::Tuple(
                elems
                    .iter()
                    .map(|elem| elem.substitute_named_lifetimes(subst))
                    .collect(),
            ),
            RustType::Function { params, ret } => RustType::Function {
                params: params
                    .iter()
                    .map(|param| param.substitute_named_lifetimes(subst))
                    .collect(),
                ret: Box::new(ret.substitute_named_lifetimes(subst)),
            },
            RustType::Named {
                name,
                type_args,
                lifetime_args,
                const_args,
            } => RustType::Named {
                name: name.clone(),
                type_args: type_args
                    .iter()
                    .map(|arg| arg.substitute_named_lifetimes(subst))
                    .collect(),
                lifetime_args: lifetime_args
                    .iter()
                    .map(|lifetime| Self::substitute_lifetime(lifetime, subst))
                    .collect(),
                const_args: const_args.clone(),
            },
            RustType::Box { inner } => RustType::Box {
                inner: Box::new(inner.substitute_named_lifetimes(subst)),
            },
            RustType::Cell { inner } => RustType::Cell {
                inner: Box::new(inner.substitute_named_lifetimes(subst)),
            },
            RustType::RefCell { inner } => RustType::RefCell {
                inner: Box::new(inner.substitute_named_lifetimes(subst)),
            },
            RustType::UnsafeCell { inner } => RustType::UnsafeCell {
                inner: Box::new(inner.substitute_named_lifetimes(subst)),
            },
            RustType::Pin { inner } => RustType::Pin {
                inner: Box::new(inner.substitute_named_lifetimes(subst)),
            },
            RustType::Option { inner } => RustType::Option {
                inner: Box::new(inner.substitute_named_lifetimes(subst)),
            },
            RustType::Result { ok, err } => RustType::Result {
                ok: Box::new(ok.substitute_named_lifetimes(subst)),
                err: Box::new(err.substitute_named_lifetimes(subst)),
            },
            RustType::Vec { element } => RustType::Vec {
                element: Box::new(element.substitute_named_lifetimes(subst)),
            },
            RustType::DynTrait {
                trait_name,
                auto_traits,
            } => RustType::DynTrait {
                trait_name: trait_name.clone(),
                auto_traits: auto_traits.clone(),
            },
            RustType::Closure {
                params,
                ret,
                captures,
                kind,
            } => RustType::Closure {
                params: params
                    .iter()
                    .map(|param| param.substitute_named_lifetimes(subst))
                    .collect(),
                ret: Box::new(ret.substitute_named_lifetimes(subst)),
                captures: captures
                    .iter()
                    .map(|(name, ty, mutability)| {
                        (
                            name.clone(),
                            ty.substitute_named_lifetimes(subst),
                            *mutability,
                        )
                    })
                    .collect(),
                kind: *kind,
            },
            RustType::TypeProjection {
                self_ty,
                trait_name,
                assoc_name,
                assoc_type_args,
                assoc_lifetime_args,
                const_args,
            } => RustType::TypeProjection {
                self_ty: Box::new(self_ty.substitute_named_lifetimes(subst)),
                trait_name: trait_name.clone(),
                assoc_name: assoc_name.clone(),
                assoc_type_args: assoc_type_args
                    .iter()
                    .map(|arg| arg.substitute_named_lifetimes(subst))
                    .collect(),
                assoc_lifetime_args: assoc_lifetime_args
                    .iter()
                    .map(|lifetime| Self::substitute_lifetime(lifetime, subst))
                    .collect(),
                const_args: const_args.clone(),
            },
            _ => self.clone(),
        }
    }

    /// Build a substitution map from `TypeParamDef` declarations and concrete
    /// type arguments supplied at a call site or type instantiation.
    ///
    /// Returns `None` if the lengths don't match (arity mismatch).
    pub(crate) fn build_type_param_subst(
        type_param_defs: &[super::TypeParamDef],
        type_args: &[RustType],
    ) -> Option<HashMap<u32, RustType>> {
        if type_param_defs.len() != type_args.len() {
            return None;
        }
        Some(
            type_param_defs
                .iter()
                .zip(type_args.iter())
                .map(|(def, arg)| (def.id, arg.clone()))
                .collect(),
        )
    }

    pub(crate) fn build_const_param_subst(
        const_param_defs: &[ConstParamDef],
        const_args: &[ConstGenericArg],
    ) -> Option<HashMap<String, ConstGenericValue>> {
        if const_param_defs.len() != const_args.len() {
            return None;
        }
        let mut subst = HashMap::with_capacity(const_param_defs.len());
        for (def, arg) in const_param_defs.iter().zip(const_args.iter()) {
            subst.insert(def.name.clone(), ConstGenericEval::eval(arg, &subst));
        }
        Some(subst)
    }

    /// Infer generic type and lifetime bindings by structurally matching a
    /// generic pattern against a concrete type.
    pub(crate) fn infer_generic_bindings(
        &self,
        concrete: &RustType,
    ) -> Option<(HashMap<u32, RustType>, HashMap<String, Lifetime>)> {
        let mut type_bindings = HashMap::new();
        let mut lifetime_bindings = HashMap::new();
        if collect_generic_bindings(self, concrete, &mut type_bindings, &mut lifetime_bindings) {
            Some((type_bindings, lifetime_bindings))
        } else {
            None
        }
    }

    /// Erase anonymous lifetime identity so that types parsed in different
    /// scopes compare equal when only elided lifetime IDs differ.
    pub(crate) fn erase_anonymous_lifetimes(&self) -> RustType {
        map_type(self, &|ty| match ty {
            RustType::Reference {
                lifetime,
                mutability,
                inner,
            } => {
                let erased = Self::erase_lifetime(lifetime);
                if erased == *lifetime {
                    None // no change at this node, recurse normally
                } else {
                    Some(RustType::Reference {
                        lifetime: erased,
                        mutability: *mutability,
                        inner: Box::new(inner.erase_anonymous_lifetimes()),
                    })
                }
            }
            RustType::Named {
                name,
                type_args,
                lifetime_args,
                const_args,
            } => {
                let erased: Vec<_> = lifetime_args.iter().map(Self::erase_lifetime).collect();
                if erased == *lifetime_args {
                    None
                } else {
                    Some(RustType::Named {
                        name: name.clone(),
                        type_args: type_args
                            .iter()
                            .map(|a| a.erase_anonymous_lifetimes())
                            .collect(),
                        lifetime_args: erased,
                        const_args: const_args.clone(),
                    })
                }
            }
            _ => None,
        })
    }

    fn erase_lifetime(lt: &Lifetime) -> Lifetime {
        match lt {
            Lifetime::Anonymous(_) | Lifetime::Existential(_) => Lifetime::Anonymous(0),
            other => other.clone(),
        }
    }

    fn substitute_lifetime(lifetime: &Lifetime, subst: &HashMap<String, Lifetime>) -> Lifetime {
        match lifetime {
            Lifetime::Named(name) => subst.get(name).cloned().unwrap_or_else(|| lifetime.clone()),
            _ => lifetime.clone(),
        }
    }

    fn substitute_const_arg(
        arg: &ConstGenericArg,
        subst: &HashMap<String, ConstGenericValue>,
    ) -> ConstGenericArg {
        match arg {
            ConstGenericArg::Value(value) => ConstGenericArg::Value(value.clone()),
            ConstGenericArg::Param(name) => subst
                .get(name)
                .cloned()
                .map(ConstGenericArg::Value)
                .unwrap_or_else(|| ConstGenericArg::Param(name.clone())),
            ConstGenericArg::Add(lhs, rhs) => Self::fold_const_arg(ConstGenericArg::Add(
                Box::new(Self::substitute_const_arg(lhs, subst)),
                Box::new(Self::substitute_const_arg(rhs, subst)),
            )),
            ConstGenericArg::Sub(lhs, rhs) => Self::fold_const_arg(ConstGenericArg::Sub(
                Box::new(Self::substitute_const_arg(lhs, subst)),
                Box::new(Self::substitute_const_arg(rhs, subst)),
            )),
            ConstGenericArg::Mul(lhs, rhs) => Self::fold_const_arg(ConstGenericArg::Mul(
                Box::new(Self::substitute_const_arg(lhs, subst)),
                Box::new(Self::substitute_const_arg(rhs, subst)),
            )),
            ConstGenericArg::Div(lhs, rhs) => Self::fold_const_arg(ConstGenericArg::Div(
                Box::new(Self::substitute_const_arg(lhs, subst)),
                Box::new(Self::substitute_const_arg(rhs, subst)),
            )),
            ConstGenericArg::Rem(lhs, rhs) => Self::fold_const_arg(ConstGenericArg::Rem(
                Box::new(Self::substitute_const_arg(lhs, subst)),
                Box::new(Self::substitute_const_arg(rhs, subst)),
            )),
            ConstGenericArg::Neg(inner) => Self::fold_const_arg(ConstGenericArg::Neg(Box::new(
                Self::substitute_const_arg(inner, subst),
            ))),
        }
    }

    fn fold_const_arg(arg: ConstGenericArg) -> ConstGenericArg {
        match ConstGenericEval::eval(&arg, &HashMap::new()) {
            ConstGenericValue::Unknown => arg,
            value => ConstGenericArg::Value(value),
        }
    }
}

fn collect_generic_bindings(
    pattern: &RustType,
    concrete: &RustType,
    type_bindings: &mut HashMap<u32, RustType>,
    lifetime_bindings: &mut HashMap<String, Lifetime>,
) -> bool {
    match (pattern, concrete) {
        (RustType::TypeParam(TypeVar { id, .. }), concrete_ty) => {
            bind_type_param(*id, concrete_ty, type_bindings)
        }
        (RustType::Unit, RustType::Unit)
        | (RustType::Bool, RustType::Bool)
        | (RustType::Char, RustType::Char)
        | (RustType::Str, RustType::Str)
        | (RustType::Never, RustType::Never)
        | (RustType::Infer, RustType::Infer) => true,
        (RustType::Uint(lhs), RustType::Uint(rhs)) => lhs == rhs,
        (RustType::Int(lhs), RustType::Int(rhs)) => lhs == rhs,
        (RustType::Float(lhs), RustType::Float(rhs)) => lhs == rhs,
        (
            RustType::Reference {
                lifetime: lhs_lifetime,
                mutability: lhs_mutability,
                inner: lhs_inner,
            },
            RustType::Reference {
                lifetime: rhs_lifetime,
                mutability: rhs_mutability,
                inner: rhs_inner,
            },
        ) => {
            lhs_mutability == rhs_mutability
                && bind_lifetime(lhs_lifetime, rhs_lifetime, lifetime_bindings)
                && collect_generic_bindings(lhs_inner, rhs_inner, type_bindings, lifetime_bindings)
        }
        (
            RustType::RawPtr {
                mutability: lhs_mutability,
                inner: lhs_inner,
            },
            RustType::RawPtr {
                mutability: rhs_mutability,
                inner: rhs_inner,
            },
        ) => {
            lhs_mutability == rhs_mutability
                && collect_generic_bindings(lhs_inner, rhs_inner, type_bindings, lifetime_bindings)
        }
        (RustType::Atomic { inner: lhs_inner }, RustType::Atomic { inner: rhs_inner })
        | (RustType::Box { inner: lhs_inner }, RustType::Box { inner: rhs_inner })
        | (RustType::Cell { inner: lhs_inner }, RustType::Cell { inner: rhs_inner })
        | (RustType::RefCell { inner: lhs_inner }, RustType::RefCell { inner: rhs_inner })
        | (RustType::UnsafeCell { inner: lhs_inner }, RustType::UnsafeCell { inner: rhs_inner })
        | (RustType::Pin { inner: lhs_inner }, RustType::Pin { inner: rhs_inner })
        | (RustType::Option { inner: lhs_inner }, RustType::Option { inner: rhs_inner }) => {
            collect_generic_bindings(lhs_inner, rhs_inner, type_bindings, lifetime_bindings)
        }
        (
            RustType::Array {
                element: lhs_element,
                len: lhs_len,
            },
            RustType::Array {
                element: rhs_element,
                len: rhs_len,
            },
        ) => {
            const_args_compatible(std::slice::from_ref(lhs_len), std::slice::from_ref(rhs_len))
                && collect_generic_bindings(
                    lhs_element,
                    rhs_element,
                    type_bindings,
                    lifetime_bindings,
                )
        }
        (RustType::Slice { elem: lhs_elem }, RustType::Slice { elem: rhs_elem })
        | (RustType::Vec { element: lhs_elem }, RustType::Vec { element: rhs_elem }) => {
            collect_generic_bindings(lhs_elem, rhs_elem, type_bindings, lifetime_bindings)
        }
        (RustType::Tuple(lhs_elems), RustType::Tuple(rhs_elems)) => {
            lhs_elems.len() == rhs_elems.len()
                && lhs_elems.iter().zip(rhs_elems.iter()).all(|(lhs, rhs)| {
                    collect_generic_bindings(lhs, rhs, type_bindings, lifetime_bindings)
                })
        }
        (
            RustType::Function {
                params: lhs_params,
                ret: lhs_ret,
            },
            RustType::Function {
                params: rhs_params,
                ret: rhs_ret,
            },
        ) => {
            lhs_params.len() == rhs_params.len()
                && lhs_params.iter().zip(rhs_params.iter()).all(|(lhs, rhs)| {
                    collect_generic_bindings(lhs, rhs, type_bindings, lifetime_bindings)
                })
                && collect_generic_bindings(lhs_ret, rhs_ret, type_bindings, lifetime_bindings)
        }
        (
            RustType::Named {
                name: lhs_name,
                type_args: lhs_type_args,
                lifetime_args: lhs_lifetime_args,
                const_args: lhs_const_args,
            },
            RustType::Named {
                name: rhs_name,
                type_args: rhs_type_args,
                lifetime_args: rhs_lifetime_args,
                const_args: rhs_const_args,
            },
        ) => {
            lhs_name == rhs_name
                && lhs_type_args.len() == rhs_type_args.len()
                && lhs_lifetime_args.len() == rhs_lifetime_args.len()
                && const_args_compatible(lhs_const_args, rhs_const_args)
                && lhs_lifetime_args
                    .iter()
                    .zip(rhs_lifetime_args.iter())
                    .all(|(lhs, rhs)| bind_lifetime(lhs, rhs, lifetime_bindings))
                && lhs_type_args
                    .iter()
                    .zip(rhs_type_args.iter())
                    .all(|(lhs, rhs)| {
                        collect_generic_bindings(lhs, rhs, type_bindings, lifetime_bindings)
                    })
        }
        (
            RustType::Result {
                ok: lhs_ok,
                err: lhs_err,
            },
            RustType::Result {
                ok: rhs_ok,
                err: rhs_err,
            },
        ) => {
            collect_generic_bindings(lhs_ok, rhs_ok, type_bindings, lifetime_bindings)
                && collect_generic_bindings(lhs_err, rhs_err, type_bindings, lifetime_bindings)
        }
        (
            RustType::DynTrait {
                trait_name: lhs_trait_name,
                auto_traits: lhs_auto_traits,
            },
            RustType::DynTrait {
                trait_name: rhs_trait_name,
                auto_traits: rhs_auto_traits,
            },
        ) => lhs_trait_name == rhs_trait_name && lhs_auto_traits == rhs_auto_traits,
        (
            RustType::ImplTrait { traits: lhs_traits },
            RustType::ImplTrait { traits: rhs_traits },
        ) => lhs_traits == rhs_traits,
        (
            RustType::Closure {
                params: lhs_params,
                ret: lhs_ret,
                captures: lhs_captures,
                kind: lhs_kind,
            },
            RustType::Closure {
                params: rhs_params,
                ret: rhs_ret,
                captures: rhs_captures,
                kind: rhs_kind,
            },
        ) => {
            lhs_kind == rhs_kind
                && lhs_params.len() == rhs_params.len()
                && lhs_captures.len() == rhs_captures.len()
                && lhs_params.iter().zip(rhs_params.iter()).all(|(lhs, rhs)| {
                    collect_generic_bindings(lhs, rhs, type_bindings, lifetime_bindings)
                })
                && collect_generic_bindings(lhs_ret, rhs_ret, type_bindings, lifetime_bindings)
                && lhs_captures.iter().zip(rhs_captures.iter()).all(
                    |((lhs_name, lhs_ty, lhs_mutability), (rhs_name, rhs_ty, rhs_mutability))| {
                        lhs_name == rhs_name
                            && lhs_mutability == rhs_mutability
                            && collect_generic_bindings(
                                lhs_ty,
                                rhs_ty,
                                type_bindings,
                                lifetime_bindings,
                            )
                    },
                )
        }
        (
            RustType::TypeProjection {
                self_ty: lhs_self_ty,
                trait_name: lhs_trait_name,
                assoc_name: lhs_assoc_name,
                assoc_type_args: lhs_assoc_type_args,
                assoc_lifetime_args: lhs_assoc_lifetime_args,
                ..
            },
            RustType::TypeProjection {
                self_ty: rhs_self_ty,
                trait_name: rhs_trait_name,
                assoc_name: rhs_assoc_name,
                assoc_type_args: rhs_assoc_type_args,
                assoc_lifetime_args: rhs_assoc_lifetime_args,
                ..
            },
        ) => {
            lhs_trait_name == rhs_trait_name
                && lhs_assoc_name == rhs_assoc_name
                && lhs_assoc_type_args.len() == rhs_assoc_type_args.len()
                && lhs_assoc_lifetime_args.len() == rhs_assoc_lifetime_args.len()
                && collect_generic_bindings(
                    lhs_self_ty,
                    rhs_self_ty,
                    type_bindings,
                    lifetime_bindings,
                )
                && lhs_assoc_lifetime_args
                    .iter()
                    .zip(rhs_assoc_lifetime_args.iter())
                    .all(|(lhs, rhs)| bind_lifetime(lhs, rhs, lifetime_bindings))
                && lhs_assoc_type_args
                    .iter()
                    .zip(rhs_assoc_type_args.iter())
                    .all(|(lhs, rhs)| {
                        collect_generic_bindings(lhs, rhs, type_bindings, lifetime_bindings)
                    })
        }
        _ => false,
    }
}

fn const_args_compatible(lhs: &[ConstGenericArg], rhs: &[ConstGenericArg]) -> bool {
    lhs.len() == rhs.len() && {
        let mut unifier = ConstGenericUnifier::new();
        lhs.iter()
            .zip(rhs.iter())
            .all(|(lhs, rhs)| unifier.unify(lhs, rhs))
    }
}

fn bind_type_param(
    id: u32,
    concrete: &RustType,
    type_bindings: &mut HashMap<u32, RustType>,
) -> bool {
    match type_bindings.get(&id) {
        Some(existing) => existing == concrete,
        None => {
            type_bindings.insert(id, concrete.clone());
            true
        }
    }
}

fn bind_lifetime(
    pattern: &Lifetime,
    concrete: &Lifetime,
    lifetime_bindings: &mut HashMap<String, Lifetime>,
) -> bool {
    match pattern {
        Lifetime::Named(name) => match lifetime_bindings.get(name) {
            Some(existing) => existing == concrete,
            None => {
                lifetime_bindings.insert(name.clone(), concrete.clone());
                true
            }
        },
        _ => pattern == concrete,
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::super::*;

    fn type_param(id: u32, name: &str) -> RustType {
        RustType::TypeParam(TypeVar {
            id,
            name: Some(name.to_string()),
        })
    }

    #[test]
    fn test_substitute_type_params_simple_replacement() {
        let subst = HashMap::from([(0, RustType::Int(IntType::I32))]);
        assert_eq!(
            type_param(0, "T").substitute_type_params(&subst),
            RustType::Int(IntType::I32)
        );
    }

    #[test]
    fn test_substitute_type_params_unmapped_param_unchanged() {
        let subst = HashMap::from([(0, RustType::Int(IntType::I32))]);
        assert_eq!(
            type_param(1, "U").substitute_type_params(&subst),
            type_param(1, "U")
        );
    }

    #[test]
    fn test_substitute_type_params_empty_subst_is_identity() {
        assert_eq!(
            type_param(0, "T").substitute_type_params(&HashMap::new()),
            type_param(0, "T")
        );
    }

    #[test]
    fn test_substitute_type_params_recurses_through_vec() {
        let subst = HashMap::from([(0, RustType::Uint(UintType::U32))]);
        let ty = RustType::Vec {
            element: Box::new(type_param(0, "T")),
        };
        assert_eq!(
            ty.substitute_type_params(&subst),
            RustType::Vec {
                element: Box::new(RustType::Uint(UintType::U32))
            }
        );
    }

    #[test]
    fn test_substitute_type_params_recurses_through_named_type_args() {
        let subst = HashMap::from([(0, RustType::Str), (1, RustType::Int(IntType::I32))]);
        let ty = RustType::Named {
            name: "HashMap".to_string(),
            type_args: vec![type_param(0, "K"), type_param(1, "V")],
            lifetime_args: vec![],
            const_args: vec![],
        };
        assert_eq!(
            ty.substitute_type_params(&subst),
            RustType::Named {
                name: "HashMap".to_string(),
                type_args: vec![RustType::Str, RustType::Int(IntType::I32)],
                lifetime_args: vec![],
                const_args: vec![],
            }
        );
    }

    #[test]
    fn test_substitute_type_params_deeply_nested() {
        let subst = HashMap::from([
            (0, RustType::Uint(UintType::U32)),
            (
                1,
                RustType::Named {
                    name: "String".to_string(),
                    type_args: vec![],
                    lifetime_args: vec![],
                    const_args: vec![],
                },
            ),
        ]);
        let ty = RustType::Result {
            ok: Box::new(RustType::Option {
                inner: Box::new(RustType::Reference {
                    lifetime: Lifetime::Static,
                    mutability: Mutability::Shared,
                    inner: Box::new(type_param(0, "T")),
                }),
            }),
            err: Box::new(type_param(1, "E")),
        };
        let expected = RustType::Result {
            ok: Box::new(RustType::Option {
                inner: Box::new(RustType::Reference {
                    lifetime: Lifetime::Static,
                    mutability: Mutability::Shared,
                    inner: Box::new(RustType::Uint(UintType::U32)),
                }),
            }),
            err: Box::new(RustType::Named {
                name: "String".to_string(),
                type_args: vec![],
                lifetime_args: vec![],
                const_args: vec![],
            }),
        };
        assert_eq!(ty.substitute_type_params(&subst), expected);
    }

    #[test]
    fn test_substitute_type_params_function_type() {
        let subst = HashMap::from([(0, RustType::Bool)]);
        let ty = RustType::Function {
            params: vec![type_param(0, "T")],
            ret: Box::new(type_param(0, "T")),
        };
        assert_eq!(
            ty.substitute_type_params(&subst),
            RustType::Function {
                params: vec![RustType::Bool],
                ret: Box::new(RustType::Bool)
            }
        );
    }

    #[test]
    fn test_substitute_type_params_closure_with_captures() {
        let subst = HashMap::from([(0, RustType::Int(IntType::I64))]);
        let ty = RustType::Closure {
            params: vec![type_param(0, "T")],
            ret: Box::new(RustType::Unit),
            captures: vec![("x".to_string(), type_param(0, "T"), Mutability::Shared)],
            kind: ClosureKind::Fn,
        };
        assert_eq!(
            ty.substitute_type_params(&subst),
            RustType::Closure {
                params: vec![RustType::Int(IntType::I64)],
                ret: Box::new(RustType::Unit),
                captures: vec![(
                    "x".to_string(),
                    RustType::Int(IntType::I64),
                    Mutability::Shared
                )],
                kind: ClosureKind::Fn,
            }
        );
    }

    #[test]
    fn test_substitute_type_params_type_projection() {
        let subst = HashMap::from([(
            0,
            RustType::Vec {
                element: Box::new(RustType::Uint(UintType::U8)),
            },
        )]);
        let ty = RustType::TypeProjection {
            self_ty: Box::new(type_param(0, "T")),
            trait_name: "Iterator".to_string(),
            assoc_name: "Item".to_string(),
            assoc_type_args: vec![],
            assoc_lifetime_args: vec![],
            const_args: vec![],
        };
        assert_eq!(
            ty.substitute_type_params(&subst),
            RustType::TypeProjection {
                self_ty: Box::new(RustType::Vec {
                    element: Box::new(RustType::Uint(UintType::U8)),
                }),
                trait_name: "Iterator".to_string(),
                assoc_name: "Item".to_string(),
                assoc_type_args: vec![],
                assoc_lifetime_args: vec![],
                const_args: vec![],
            }
        );
    }

    #[test]
    fn test_substitute_type_params_leaves_concrete_unchanged() {
        let subst = HashMap::from([(0, RustType::Bool)]);
        assert_eq!(
            RustType::Int(IntType::I32).substitute_type_params(&subst),
            RustType::Int(IntType::I32)
        );
    }

    #[test]
    fn test_build_type_param_subst_success() {
        let defs = vec![
            TypeParamDef {
                id: 0,
                name: "T".to_string(),
                bounds: vec![],
            },
            TypeParamDef {
                id: 1,
                name: "U".to_string(),
                bounds: vec!["Clone".to_string()],
            },
        ];
        let args = vec![RustType::Int(IntType::I32), RustType::Bool];
        let subst = RustType::build_type_param_subst(&defs, &args).unwrap();
        assert_eq!(subst.len(), 2);
        assert_eq!(subst[&0], RustType::Int(IntType::I32));
        assert_eq!(subst[&1], RustType::Bool);
    }

    #[test]
    fn test_build_type_param_subst_arity_mismatch() {
        let defs = vec![TypeParamDef {
            id: 7,
            name: "T".to_string(),
            bounds: vec![],
        }];
        assert!(RustType::build_type_param_subst(
            &defs,
            &[RustType::Int(IntType::I32), RustType::Bool]
        )
        .is_none());
    }

    #[test]
    fn test_build_type_param_subst_preserves_declared_ids() {
        let defs = vec![
            TypeParamDef {
                id: 7,
                name: "T".to_string(),
                bounds: vec![],
            },
            TypeParamDef {
                id: 11,
                name: "U".to_string(),
                bounds: vec![],
            },
        ];
        let args = vec![RustType::Uint(UintType::U32), RustType::Bool];
        let subst = RustType::build_type_param_subst(&defs, &args).unwrap();
        assert_eq!(subst.len(), 2);
        assert_eq!(subst[&7], RustType::Uint(UintType::U32));
        assert_eq!(subst[&11], RustType::Bool);
    }

    #[test]
    fn test_substitute_self_type_recurses_through_nested_types() {
        let concrete_self = RustType::Named {
            name: "Counter".to_string(),
            type_args: vec![],
            lifetime_args: vec![],
            const_args: vec![],
        };
        let placeholder_self = RustType::Named {
            name: "Self".to_string(),
            type_args: vec![],
            lifetime_args: vec![],
            const_args: vec![],
        };
        let ty = RustType::Result {
            ok: Box::new(RustType::Option {
                inner: Box::new(RustType::Reference {
                    lifetime: Lifetime::Static,
                    mutability: Mutability::Shared,
                    inner: Box::new(placeholder_self.clone()),
                }),
            }),
            err: Box::new(RustType::TypeProjection {
                self_ty: Box::new(placeholder_self),
                trait_name: "Iterator".to_string(),
                assoc_name: "Item".to_string(),
                assoc_type_args: vec![],
                assoc_lifetime_args: vec![],
                const_args: vec![],
            }),
        };
        assert_eq!(
            ty.substitute_self_type(&concrete_self),
            RustType::Result {
                ok: Box::new(RustType::Option {
                    inner: Box::new(RustType::Reference {
                        lifetime: Lifetime::Static,
                        mutability: Mutability::Shared,
                        inner: Box::new(concrete_self.clone()),
                    }),
                }),
                err: Box::new(RustType::TypeProjection {
                    self_ty: Box::new(concrete_self),
                    trait_name: "Iterator".to_string(),
                    assoc_name: "Item".to_string(),
                    assoc_type_args: vec![],
                    assoc_lifetime_args: vec![],
                    const_args: vec![],
                }),
            }
        );
    }
}

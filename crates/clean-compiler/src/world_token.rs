// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Source identity for the erased state token from Lean's Init.System.ST.

use clean_kernel::{
    BinderInfo, ConstantKind, ConstantOrigin, DeclarationVerification, Environment, Expr, ExprKind,
    Level, Name, OriginTrust,
};

/// Whether this binder has the exact Void application lowered by the compiler.
pub fn is_void_type(ty: &Expr) -> bool {
    let ExprKind::App(head, _) = ty.strip_mdata().kind() else {
        return false;
    };
    matches!(head.strip_mdata().kind(), ExprKind::Const(name, levels)
        if *name == Name::interned("Void") && levels.is_empty())
}

/// Whether compiled direct calls and constructor fields erase Void for this environment.
/// Both defining SDK declarations must carry their checked import provenance.
pub fn has_checked_void_layout(env: &Environment) -> bool {
    let void = Name::interned("Void");
    let opaque = Name::interned("Void.nonemptyType");
    let checked = |name: &Name| {
        matches!(
            env.get_constant_origin(name),
            Some(ConstantOrigin::Olean {
                module: Some(module),
                trust: OriginTrust::KernelChecked,
            }) if module == "Init.System.ST"
        ) && env.declaration_verification(name) == Some(DeclarationVerification::FullKernelCheck)
            && !env.has_implemented_by(name)
            && !env.is_extern(name)
    };
    let (Some(void_info), Some(opaque_info)) = (env.get_const(&void), env.get_const(&opaque))
    else {
        return false;
    };
    let type_zero = Expr::type_();
    let nonempty = Expr::const_(Name::interned("NonemptyType"), vec![Level::zero()]);
    if !checked(&void)
        || !checked(&opaque)
        || void_info.kind != ConstantKind::Definition
        || opaque_info.kind != ConstantKind::Opaque
        || !void_info.level_params.is_empty()
        || !opaque_info.level_params.is_empty()
        || void_info.type_ != Expr::arrow(type_zero.clone(), type_zero.clone())
        || opaque_info.type_ != Expr::arrow(type_zero.clone(), nonempty)
    {
        return false;
    }
    let selected = Expr::app(Expr::const_(opaque, vec![]), Expr::bvar(0));
    let projection = Expr::proj(Name::interned("Subtype"), 0, selected.clone());
    let named_projection = Expr::app(
        Expr::const_(Name::interned("NonemptyType.type"), vec![Level::zero()]),
        selected,
    );
    [projection, named_projection].into_iter().any(|body| {
        void_info.value.as_ref() == Some(&Expr::lam(BinderInfo::Default, type_zero.clone(), body))
    })
}

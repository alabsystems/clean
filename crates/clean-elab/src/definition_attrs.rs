// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Definition exposure, the syntactic `:= rfl` definitional-equality tag, and
//! the `@[induction_eliminator]` registration
//! (`crate::tactic::custom_eliminator`).
use crate::{declared_here::AttributeSite, ElabError, ElabResult, FileContext};
use clean_kernel::{
    env::{self, AttrExtEntry, AttrExtState, ConstantKind, TransparencyMode},
    Expr, ExprKind, LocalContext, Name, TypeChecker,
};
use clean_parser::{Attribute, SurfaceDecl, SurfaceExpr};

#[derive(Clone, Debug)]
pub(crate) struct NamedAttribute {
    pub name: Name,
    pub attribute: String,
    pub site: AttributeSite,
}
fn error(message: impl Into<String>) -> ElabError {
    ElabError::Unsupported {
        feature: message.into(),
    }
}
fn tag(env: &mut env::Environment, name: &Name, attribute: &str) {
    env.add_ext_entry::<AttrExtState>(
        env::attr_ext_idx(),
        &AttrExtEntry {
            decl_name: name.clone(),
            attr_name: Name::from_string(attribute),
            priority: 0,
        },
    );
}
/// Recognized named attributes with real handlers; they are not silent unknowns.
pub(crate) fn modeled_name(name: &str) -> bool {
    matches!(
        name,
        "expose"
            | "no_expose"
            | "defeq"
            | "backward_defeq"
            | crate::tactic::custom_eliminator::INDUCTION_ELIMINATOR_ATTR
    )
}

pub(crate) fn apply(
    env: &mut env::Environment,
    file: Option<&FileContext>,
    attributes: Vec<NamedAttribute>,
) -> Result<(), ElabError> {
    for attr in attributes {
        match attr.attribute.as_str() {
            "expose" | "no_expose" => {
                let info = env
                    .get_const(&attr.name)
                    .ok_or_else(|| ElabError::UnknownIdent(attr.name.to_string()))?;
                if attr.site != AttributeSite::Declaration
                    || !matches!(
                        info.kind,
                        ConstantKind::Definition | ConstantKind::Theorem | ConstantKind::Opaque
                    )
                {
                    return Err(error(format!("Cannot add attribute [{}]: This attribute can only be added when declaring a def", attr.attribute)));
                }
                // The declaration's exposure is recorded before validation;
                // theorem/opaque values do not become unfoldable definitions.
            }
            "defeq" | "backward_defeq" => {
                validate(env, file, &attr.name)?;
                if attr.attribute == "defeq" {
                    tag(env, &attr.name, "defeq");
                }
                tag(env, &attr.name, "backward_defeq");
            }
            // `@[induction_eliminator]` / `attribute [induction_eliminator]`
            // (global kind; `local`/`scoped` are refused where written).
            crate::tactic::custom_eliminator::INDUCTION_ELIMINATOR_ATTR => {
                crate::tactic::custom_eliminator::register_induction_eliminator(env, &attr.name)
                    .map_err(|e| {
                        error(format!(
                            "Cannot add attribute [{}] to `{}`: {e}",
                            attr.attribute, attr.name
                        ))
                    })?;
            }
            other => {
                return Err(error(format!(
                    "attribute [{other}] on `{}` is not modeled",
                    attr.name
                )))
            }
        }
    }
    Ok(())
}
fn validate(
    env: &env::Environment,
    file: Option<&FileContext>,
    name: &Name,
) -> Result<(), ElabError> {
    let info = env
        .get_const(name)
        .ok_or_else(|| ElabError::UnknownIdent(name.to_string()))?;
    let public = file.is_some_and(FileContext::is_module_system) && !env.is_private(name);
    let exporting;
    let view = if public {
        exporting = env::exposure::exporting_view(env).map_err(error)?;
        &exporting
    } else {
        env
    };
    let mut locals = LocalContext::new();
    let mut ty = info.type_.clone();
    loop {
        let mut tc = TypeChecker::with_context(view, locals.clone());
        tc.set_transparency(TransparencyMode::All);
        ty = tc.whnf(&ty);
        if let ExprKind::Pi(binder, domain, body) = ty.kind() {
            let id = locals.push(Name::anon(), domain.as_ref().clone(), *binder);
            ty = body.instantiate(&Expr::fvar(id));
            continue;
        }
        let args = ty.get_app_args();
        if !matches!(ty.get_app_fn().kind(), ExprKind::Const(n, _) if *n == Name::from_string("Eq"))
            || args.len() != 3
        {
            return Err(error(
                "Not a definitional equality: the conclusion should be an equality",
            ));
        }
        if tc.is_def_eq(args[1], args[2]) {
            return Ok(());
        }
        return Err(error(if public {
            "Not a definitional equality: exported definitional equalities require unfolded definitions to be exposed"
        } else {
            "Not a definitional equality: the sides are not definitionally equal"
        }));
    }
}
/// Definition implementations remain in `env`; only the source exporting view
/// hides bodies that their module has not exposed.
pub(crate) fn record_definitions(
    env: &mut env::Environment,
    file: Option<&FileContext>,
    decl: &SurfaceDecl,
    result: &ElabResult,
) -> Result<(), ElabError> {
    if !file.is_some_and(FileContext::is_module_system) {
        return Ok(());
    }
    let (attrs, default_exposed) = match decl {
        SurfaceDecl::Def {
            attrs, modifiers, ..
        } => (attrs, modifiers.is_abbrev),
        SurfaceDecl::Instance { compiler_attrs, .. } => (compiler_attrs, true),
        SurfaceDecl::Alias { attrs, .. } => (attrs, true),
        _ => return Ok(()),
    };
    let expose = attrs
        .iter()
        .any(|a| matches!(a, Attribute::Unknown(n) if n == "expose"));
    let no_expose = attrs
        .iter()
        .any(|a| matches!(a, Attribute::Unknown(n) if n == "no_expose"));
    for name in crate::register::leaf_own_names(result) {
        let Some(info) = env.get_const(&name) else {
            continue;
        };
        if info.kind != ConstantKind::Definition {
            continue;
        }
        let default_exposed = if matches!(decl, SurfaceDecl::Instance { .. }) {
            let tc = TypeChecker::new(env);
            let sort = tc
                .infer_type(&info.type_)
                .map_err(|e| error(e.to_string()))?;
            let sort = tc.whnf(&sort);
            match sort.kind() {
                ExprKind::Sort(level) => !level.is_zero(),
                _ => return Err(error("instance type did not infer a sort")),
            }
        } else {
            default_exposed
        };
        let exposed = !env.is_private(&name) && !no_expose && (default_exposed || expose);
        env::exposure::record(env, name, exposed);
    }
    Ok(())
}

pub(crate) fn bare_rfl(value: &SurfaceExpr) -> bool {
    matches!(value, SurfaceExpr::Ident(_, name) if name.is_unescaped_component("rfl"))
}

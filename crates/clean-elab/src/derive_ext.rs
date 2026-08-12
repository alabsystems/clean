// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extends [`crate::derive_handlers`] with additional derive handlers and a
//! function-pointer registry for metadata-driven derivation.

// Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
// keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#![allow(dead_code)]
use std::collections::HashMap;

use clean_kernel::{
    BinderInfo, ConstructorVal, Declaration, Environment, Expr, InductiveVal, Level, Name,
};

use crate::derive::{instance_name, DeriveError, DeriveHandler};
use crate::derive_handlers::{
    lookup_constructors, mk_bool_true, mk_ind_type_applied, mk_instance_type,
    reject_complex_inductive, wrap_param_lambdas, wrap_param_pis,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ParamKind {
    Type,
    Value,
}

#[derive(Debug, Clone)]
pub(crate) struct TypeParam {
    pub(crate) name: String,
    pub(crate) kind: ParamKind,
}

#[derive(Debug, Clone)]
pub(crate) struct FieldInfo {
    pub(crate) name: String,
    pub(crate) field_type: Expr,
    pub(crate) index: u32,
}

#[derive(Debug, Clone)]
pub(crate) struct ConstructorInfo {
    pub(crate) name: String,
    pub(crate) fields: Vec<FieldInfo>,
    pub(crate) constructor_idx: u32,
}

#[derive(Debug, Clone)]
pub(crate) struct DeriveInput {
    pub(crate) type_name: String,
    pub(crate) type_params: Vec<TypeParam>,
    pub(crate) constructors: Vec<ConstructorInfo>,
    pub(crate) fields: Vec<FieldInfo>,
    pub(crate) ind_val: InductiveVal,
}

#[derive(Debug, Clone)]
pub(crate) struct DeriveOutput {
    pub(crate) instance_name: String,
    pub(crate) instance_type: Expr,
    pub(crate) instance_body: Expr,
}

pub(crate) type DeriveExtHandler =
    fn(&DeriveInput, &Environment) -> Result<DeriveOutput, DeriveError>;

#[derive(Debug, Clone)]
pub(crate) struct DeriveExtHandlers {
    handlers: HashMap<String, DeriveExtHandler>,
}

impl DeriveExtHandlers {
    pub(crate) fn new() -> Self {
        Self {
            handlers: HashMap::new(),
        }
    }

    pub(crate) fn register(&mut self, class_name: &str, handler: DeriveExtHandler) {
        self.handlers.insert(class_name.to_owned(), handler);
    }

    pub(crate) fn has_handler(&self, class_name: &str) -> bool {
        self.handlers.contains_key(class_name)
    }

    pub(crate) fn get(&self, class_name: &str) -> Option<&DeriveExtHandler> {
        self.handlers.get(class_name)
    }

    pub(crate) fn registered_classes(&self) -> Vec<&str> {
        self.handlers.keys().map(String::as_str).collect()
    }
}

fn synth_param_kind(param_type: &Expr) -> ParamKind {
    if matches!(param_type.kind(), clean_kernel::ExprKind::Sort(_)) {
        ParamKind::Type
    } else {
        ParamKind::Value
    }
}

fn next_pi_domain(current: &mut &Expr) -> Option<Expr> {
    match current.kind() {
        clean_kernel::ExprKind::Pi(_, domain, body) => {
            *current = body.as_ref();
            Some((**domain).clone())
        }
        _ => None,
    }
}

fn malformed_telescope(ind: &InductiveVal, detail: String) -> DeriveError {
    DeriveError::Unsupported {
        class_name: "derive metadata".to_owned(),
        ind_name: ind.name.to_string(),
        reason: detail,
    }
}

fn collect_type_params(ind: &InductiveVal) -> Result<Vec<TypeParam>, DeriveError> {
    let mut params = Vec::with_capacity(ind.num_params as usize);
    let mut current = &ind.type_;

    for idx in 0..ind.num_params {
        let param_type = next_pi_domain(&mut current).ok_or_else(|| {
            malformed_telescope(
                ind,
                format!(
                    "inductive telescope ended before declared parameter {idx} of {}",
                    ind.num_params
                ),
            )
        })?;
        params.push(TypeParam {
            name: format!("param{idx}"),
            kind: synth_param_kind(&param_type),
        });
    }

    Ok(params)
}

fn collect_ctor_fields(
    ind: &InductiveVal,
    ctor: &ConstructorVal,
) -> Result<Vec<FieldInfo>, DeriveError> {
    let mut current = &ctor.type_;
    let mut fields = Vec::with_capacity(ctor.num_fields as usize);

    for idx in 0..ctor.num_params {
        let _ = next_pi_domain(&mut current).ok_or_else(|| {
            malformed_telescope(
                ind,
                format!(
                    "constructor `{}` telescope ended before declared parameter {idx} of {}",
                    ctor.name, ctor.num_params
                ),
            )
        })?;
    }

    for idx in 0..ctor.num_fields {
        let field_type = next_pi_domain(&mut current).ok_or_else(|| {
            malformed_telescope(
                ind,
                format!(
                    "constructor `{}` telescope ended before declared field {idx} of {}",
                    ctor.name, ctor.num_fields
                ),
            )
        })?;
        fields.push(FieldInfo {
            name: format!("field{idx}"),
            field_type,
            index: idx,
        });
    }

    Ok(fields)
}

fn mk_ordering_eq() -> Expr {
    Expr::const_(Name::from_string("Ordering.eq"), vec![])
}

fn mk_ord_output(input: &DeriveInput, compare_body: Expr) -> DeriveOutput {
    let ind_ty = Expr::const_(input.ind_val.name.clone(), vec![]);
    let compare_val = Expr::lam(
        BinderInfo::Default,
        ind_ty.clone(),
        Expr::lam(BinderInfo::Default, ind_ty.clone(), compare_body),
    );
    let instance_type = Expr::app(
        Expr::const_str_levels("Ord", vec![Level::zero()]),
        ind_ty.clone(),
    );
    let instance_body = Expr::apps(
        Expr::const_str_levels("Ord.mk", vec![Level::zero()]),
        [ind_ty, compare_val],
    );

    DeriveOutput {
        instance_name: instance_name("Ord", &input.ind_val.name).to_string(),
        instance_type,
        instance_body,
    }
}

pub(crate) fn build_derive_input(
    ind: &InductiveVal,
    env: &Environment,
) -> Result<DeriveInput, DeriveError> {
    let ctors = lookup_constructors(ind, env)?;
    let constructors: Vec<ConstructorInfo> = ctors
        .iter()
        .map(|ctor| {
            Ok(ConstructorInfo {
                name: ctor.name.to_string(),
                fields: collect_ctor_fields(ind, ctor)?,
                constructor_idx: ctor.constructor_idx,
            })
        })
        .collect::<Result<_, DeriveError>>()?;
    let fields = constructors
        .iter()
        .flat_map(|ctor| ctor.fields.iter().cloned())
        .collect();

    Ok(DeriveInput {
        type_name: ind.name.to_string(),
        type_params: collect_type_params(ind)?,
        constructors,
        fields,
        ind_val: ind.clone(),
    })
}

pub(crate) fn mk_ordering_type() -> Expr {
    Expr::const_str("Ordering")
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct DeriveOrd;

impl DeriveHandler for DeriveOrd {
    fn class_name(&self) -> &str {
        "Ord"
    }

    fn derive(
        &self,
        ind: &InductiveVal,
        env: &Environment,
    ) -> Result<Vec<Declaration>, DeriveError> {
        reject_complex_inductive(ind, "Ord")?;
        let ctors = lookup_constructors(ind, env)?;
        if ind.num_params != 0 || !ind.level_params.is_empty() || !ctors.is_empty() {
            return Err(DeriveError::Unsupported {
                class_name: "Ord".to_owned(),
                ind_name: ind.name.to_string(),
                reason: "only a monomorphic empty type has a complete Ord construction".to_owned(),
            });
        }
        let ind_ty = Expr::const_(ind.name.clone(), vec![]);
        let compare_body = mk_ordering_eq();
        let compare_val = Expr::lam(
            BinderInfo::Default,
            ind_ty.clone(),
            Expr::lam(BinderInfo::Default, ind_ty.clone(), compare_body),
        );
        let inst_type = Expr::app(
            Expr::const_str_levels("Ord", vec![Level::zero()]),
            ind_ty.clone(),
        );
        let inst_val = Expr::apps(
            Expr::const_str_levels("Ord.mk", vec![Level::zero()]),
            [ind_ty, compare_val],
        );

        Ok(vec![Declaration::Definition {
            name: instance_name("Ord", &ind.name),
            level_params: ind.level_params.clone(),
            type_: inst_type,
            value: inst_val,
            is_reducible: true,
        }])
    }
}

pub(crate) fn derive_beq_ext(
    input: &DeriveInput,
    env: &Environment,
) -> Result<DeriveOutput, DeriveError> {
    let _ = env;
    let ind_ty = mk_ind_type_applied(&input.ind_val);
    if !(input.constructors.is_empty()
        || (input.constructors.len() == 1 && input.constructors[0].fields.is_empty()))
    {
        return Err(DeriveError::Unsupported {
            class_name: "BEq".to_owned(),
            ind_name: input.type_name.clone(),
            reason: "this legacy handler only has exact equality for an empty or \
                     singleton-nullary type"
                .to_owned(),
        });
    }
    let body = mk_bool_true();
    let beq_val = Expr::lam(
        BinderInfo::Default,
        ind_ty.clone(),
        Expr::lam(BinderInfo::Default, ind_ty, body),
    );
    let beq_val = wrap_param_lambdas(beq_val, input.ind_val.num_params);
    let instance_type = mk_instance_type("BEq", &input.ind_val);
    let instance_type = wrap_param_pis(instance_type, input.ind_val.num_params);
    let instance_body = Expr::app(Expr::const_str("BEq.mk"), beq_val);
    let instance_body = wrap_param_lambdas(instance_body, input.ind_val.num_params);

    Ok(DeriveOutput {
        instance_name: instance_name("BEq", &input.ind_val.name).to_string(),
        instance_type,
        instance_body,
    })
}

pub(crate) fn derive_hashable_ext(
    input: &DeriveInput,
    env: &Environment,
) -> Result<DeriveOutput, DeriveError> {
    let _ = env;
    Err(DeriveError::Unsupported {
        class_name: "Hashable".to_owned(),
        ind_name: input.type_name.clone(),
        reason: "this legacy handler has no structural hash construction".to_owned(),
    })
}

pub(crate) fn derive_repr_ext(
    input: &DeriveInput,
    env: &Environment,
) -> Result<DeriveOutput, DeriveError> {
    let _ = env;
    Err(DeriveError::Unsupported {
        class_name: "Repr".to_owned(),
        ind_name: input.type_name.clone(),
        reason: "this legacy handler has no constructor-sensitive representation".to_owned(),
    })
}

pub(crate) fn derive_inhabited_ext(
    input: &DeriveInput,
    env: &Environment,
) -> Result<DeriveOutput, DeriveError> {
    let _ = env;
    let first_ctor = input
        .constructors
        .first()
        .ok_or_else(|| DeriveError::Unsupported {
            class_name: "Inhabited".to_owned(),
            ind_name: input.type_name.clone(),
            reason: "type has no constructors".to_owned(),
        })?;

    if input.ind_val.num_params != 0
        || !input.ind_val.level_params.is_empty()
        || !first_ctor.fields.is_empty()
    {
        return Err(DeriveError::Unsupported {
            class_name: "Inhabited".to_owned(),
            ind_name: input.type_name.clone(),
            reason: "a closed nullary constructor is required; parameter and field \
                     instances are not synthesized by this handler"
                .to_owned(),
        });
    }

    let u = Level::succ(Level::zero());
    let ind_ty = Expr::const_(input.ind_val.name.clone(), vec![]);
    let default_val = Expr::const_(Name::from_string(&first_ctor.name), vec![]);
    let instance_type = Expr::app(
        Expr::const_str_levels("Inhabited", vec![u.clone()]),
        ind_ty.clone(),
    );
    let instance_body = Expr::apps(
        Expr::const_str_levels("Inhabited.mk", vec![u]),
        [ind_ty, default_val],
    );

    Ok(DeriveOutput {
        instance_name: instance_name("Inhabited", &input.ind_val.name).to_string(),
        instance_type,
        instance_body,
    })
}

pub(crate) fn derive_decidable_eq_ext(
    input: &DeriveInput,
    env: &Environment,
) -> Result<DeriveOutput, DeriveError> {
    let _ = env;
    Err(DeriveError::Unsupported {
        class_name: "DecidableEq".to_owned(),
        ind_name: input.type_name.clone(),
        reason: "this legacy handler has no proof-producing equality decision procedure".to_owned(),
    })
}

pub(crate) fn derive_ord_ext(
    input: &DeriveInput,
    env: &Environment,
) -> Result<DeriveOutput, DeriveError> {
    let _ = env;
    if input.ind_val.num_params != 0
        || !input.ind_val.level_params.is_empty()
        || !input.constructors.is_empty()
    {
        return Err(DeriveError::Unsupported {
            class_name: "Ord".to_owned(),
            ind_name: input.type_name.clone(),
            reason: "this legacy handler only supports a monomorphic empty type".to_owned(),
        });
    }
    let compare_body = mk_ordering_eq();
    Ok(mk_ord_output(input, compare_body))
}

pub(crate) fn register_ext_handlers(registry: &mut DeriveExtHandlers) {
    registry.register("BEq", derive_beq_ext);
    registry.register("Hashable", derive_hashable_ext);
    registry.register("Repr", derive_repr_ext);
    registry.register("Inhabited", derive_inhabited_ext);
    registry.register("DecidableEq", derive_decidable_eq_ext);
    registry.register("Ord", derive_ord_ext);
}

pub fn register_all_handlers(registry: &mut crate::derive::DeriveRegistry) {
    crate::derive_handlers::register_builtin_handlers(registry);
    registry.register_handler("Ord", Box::new(DeriveOrd));
    // Previously implemented but unregistered canonical handlers. Nonempty is
    // exact for a closed nullary witness; SizeOf is registered so unsupported
    // requests fail with a typed error instead of silently disappearing.
    registry.register_handler("Nonempty", Box::new(crate::derive_handlers::DeriveNonempty));
    registry.register_handler("SizeOf", Box::new(crate::derive_handlers::DeriveSizeOf));

    // `ToExpr` and `OfScientific` are pure *data* classes (no proof obligation).
    // Their batch-2 handlers synthesize genuine, kernel-checkable, sorry-free
    // instances for the shapes they accept (nullary enums / resolvable single-ctor
    // structs for `ToExpr`; `Nat`-field wrappers for `OfScientific`) and return a
    // typed `Unsupported` error for every other shape. They are wired through
    // `ExtDeriveHandler2Adapter`, which applies the central admission gate before
    // canonical registration.
    //
    // `Fintype` now has a GENUINE construction path for the dominant
    // nullary-enum shape: its batch-2 handler emits a real `Fintype.mk` carrying
    // an explicit `Finset.cons` carrier (with `noConfusion`-backed distinctness
    // `¬mem` witnesses) and a `.rec`-dispatched completeness proof — fully
    // kernel-checkable and sorry-free (see `fintype_nullary_enum_value`). For any
    // other shape (fields / recursion / parameters / `Empty`) the handler errors
    // up front. `Countable` remains unwired outside its genuine monomorphic Nat
    // wrapper construction; broader injection-to-`Nat` support is still needed.
    registry.register_handler(
        "Fintype",
        Box::new(crate::derive_handlers_ext::ExtDeriveHandler2Adapter::new(
            Box::new(crate::derive_handlers_ext::DeriveFintype),
        )),
    );
    registry.register_handler(
        "ToExpr",
        Box::new(crate::derive_handlers_ext::ExtDeriveHandler2Adapter::new(
            Box::new(crate::derive_handlers_ext::DeriveToExpr),
        )),
    );
    registry.register_handler(
        "OfScientific",
        Box::new(crate::derive_handlers_ext::ExtDeriveHandler2Adapter::new(
            Box::new(crate::derive_handlers_ext::DeriveOfScientific),
        )),
    );
}

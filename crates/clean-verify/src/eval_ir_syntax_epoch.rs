// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact identity of the current canonical instruction syntax, not execution authority.
//! The Release-retaining epoch changes the family and all dependent closure digests.
//! A header spelling or an old checked receipt is not a model identity.

use clean_kernel::inductive::RecursorArgOrder;
use clean_kernel::tc::LocalContext;
use clean_kernel::{BinderInfo, Environment, Expr, Level, Name, TypeChecker};

/// Canonical syntax epochs are deliberately distinct from byte execution profiles.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum EvalIrSyntaxEpoch {
    /// The former 32-constructor syntax; not accepted by current owners.
    BeforeRelease,
    /// The appended result-free Release operand, with explicitly unmodelled execution.
    RetainedRelease,
}

/// Syntax identity selected by every current model construction and cache cell.
pub const EVAL_IR_SYNTAX_EPOCH: EvalIrSyntaxEpoch = EvalIrSyntaxEpoch::RetainedRelease;

/// An observed model identity. This records syntax; it is not a checked program proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EvalIrSyntaxIdentity {
    /// Explicit syntax epoch; no alias to the former constructor family.
    pub epoch: EvalIrSyntaxEpoch,
    /// Exact transitive kernel identity, including inductive and recursor records.
    pub irinst_closure_digest: [u8; 32],
}

// Fixed canonical telescopes. The first32 rows are the previous epoch verbatim;
// this is an independent admission header, not a parse of the declaration being checked.
pub(super) const INSTRUCTION_HEADERS: &[(&str, &[&str])] = &[
    ("binop", &["IRBinOp", "IRTy", "Nat", "Nat"]),
    ("unop", &["IRUnOp", "IRTy", "Nat"]),
    ("overflow", &["IROverflowOp", "IRTy", "Nat", "Nat"]),
    ("icmp", &["IRICmpOp", "IRTy", "Nat", "Nat"]),
    ("fcmp", &["IRFCmpOp", "IRTy", "Nat", "Nat"]),
    ("cast", &["IRCastOp", "IRTy", "IRTy", "Nat"]),
    ("load", &["IRTy", "Nat", "Bool"]),
    ("store", &["IRTy", "Nat", "Nat", "Bool"]),
    ("alloca", &["IRTy", "IROption Nat"]),
    ("gep", &["IRTy", "Nat", "IRList Nat", "Bool"]),
    ("ptrdata", &["IRTy", "Nat"]),
    ("ptrmetadata", &["IRTy", "IRTy", "Nat"]),
    ("ptrfromparts", &["IRTy", "IRTy", "Nat", "Nat"]),
    ("br", &["Nat", "IRList Nat"]),
    ("condbr", &["Nat", "Nat", "IRList Nat", "Nat", "IRList Nat"]),
    (
        "switch",
        &["Nat", "Nat", "IRList Nat", "IRList IRSwitchCase", "Bool"],
    ),
    ("call", &["Nat", "IRList Nat"]),
    ("callindirect", &["Nat", "Nat", "IRList Nat", "Nat"]),
    ("ret", &["IRList Nat"]),
    ("extractfield", &["IRTy", "Nat", "Nat"]),
    ("insertfield", &["IRTy", "Nat", "Nat", "Nat"]),
    ("extractelement", &["IRTy", "Nat", "Nat"]),
    ("const_", &["IRTy", "IRConst"]),
    ("globaladdr", &["Nat"]),
    ("undef", &["IRTy"]),
    ("assert", &["Nat"]),
    ("unreachable", &[]),
    ("select", &["IRTy", "Nat", "Nat", "Nat"]),
    ("borrow", &["Nat"]),
    ("copy", &["IRTy", "Nat"]),
    ("atomic_fetch_add_relaxed_u64_seq", &["Nat", "Nat"]),
    ("atomic_fetch_add_relaxed_usize_seq", &["Nat", "Nat", "Nat"]),
    ("release", &["Nat"]),
];

fn field_type(text: &str) -> Expr {
    match text {
        "IRList Nat" => Expr::app(Expr::const_str("IRList"), Expr::const_str("Nat")),
        "IRList IRSwitchCase" => {
            Expr::app(Expr::const_str("IRList"), Expr::const_str("IRSwitchCase"))
        }
        "IROption Nat" => Expr::app(Expr::const_str("IROption"), Expr::const_str("Nat")),
        name => Expr::const_str(name),
    }
}

pub(super) fn constructor_type(fields: &[&str]) -> Expr {
    fields
        .iter()
        .rev()
        .fold(Expr::const_str("IRInst"), |rest, field| {
            Expr::pi(BinderInfo::Default, field_type(field), rest)
        })
}

// Independently expected complete nonrecursive eliminator telescope. Locals are
// abstracted when each binder closes, so motives cannot be captured by minor fields.
// This is fixed IRInst syntax, not a generic recursor/RHS authenticator.
fn eliminator_type(major_before_minors: bool) -> Expr {
    let mut context = LocalContext::new();
    let motive_type = Expr::pi(
        BinderInfo::Default,
        Expr::const_str("IRInst"),
        Expr::sort(Level::param(Name::from_string("u"))),
    );
    let motive_id = context.push(
        Name::from_string("motive"),
        motive_type.clone(),
        BinderInfo::Implicit,
    );
    let motive = Expr::fvar(motive_id);
    let mut binders = vec![(motive_id, BinderInfo::Implicit, motive_type)];
    let mut major = None;
    if major_before_minors {
        let ty = Expr::const_str("IRInst");
        let id = context.push(Name::from_string("major"), ty.clone(), BinderInfo::Default);
        binders.push((id, BinderInfo::Default, ty));
        major = Some(Expr::fvar(id));
    }
    for (name, fields) in INSTRUCTION_HEADERS {
        let mut minor_context = context.clone();
        let mut field_binders = vec![];
        let mut constructor = Expr::const_str(&format!("IRInst.{name}"));
        for (index, field) in fields.iter().enumerate() {
            let ty = field_type(field);
            let id = minor_context.push(
                Name::from_string(&format!("field_{index}")),
                ty.clone(),
                BinderInfo::Default,
            );
            field_binders.push((id, ty));
            constructor = Expr::app(constructor, Expr::fvar(id));
        }
        let mut minor_type = Expr::app(motive.clone(), constructor);
        for (id, ty) in field_binders.into_iter().rev() {
            minor_type = Expr::pi(BinderInfo::Default, ty, minor_type.abstract_fvar(id));
        }
        let id = context.push(
            Name::from_string(&format!("minor_{name}")),
            minor_type.clone(),
            BinderInfo::Default,
        );
        binders.push((id, BinderInfo::Default, minor_type));
    }
    let major = match major {
        Some(major) => major,
        None => {
            let ty = Expr::const_str("IRInst");
            let id = context.push(Name::from_string("major"), ty.clone(), BinderInfo::Default);
            binders.push((id, BinderInfo::Default, ty));
            Expr::fvar(id)
        }
    };
    let mut result = Expr::app(motive, major);
    for (id, info, ty) in binders.into_iter().rev() {
        result = Expr::pi(info, ty, result.abstract_fvar(id));
    }
    result
}

/// Require the exact canonical current family and observe its full closure identity.
///
/// Checks actual family, constructor and recursor metadata, not merely names or a
/// constructor count. The public checked builders call this before publishing any
/// cached vocabulary. Kernel admission/replay and program claims remain separate.
///
/// # Errors
/// Refuses an unsupported epoch, missing/different header, old32 family, or an
/// environment whose transitive identity cannot be reconstructed completely.
pub fn checked_syntax_identity(
    env: &Environment,
    expected: EvalIrSyntaxEpoch,
) -> Result<EvalIrSyntaxIdentity, String> {
    if expected != EVAL_IR_SYNTAX_EPOCH {
        return Err("EvalIR syntax epoch mismatch: current owner retains Release".into());
    }
    let name = Name::from_string("IRInst");
    let family = env
        .get_inductive(&name)
        .ok_or("missing canonical IRInst family")?;
    let names: Vec<_> = INSTRUCTION_HEADERS
        .iter()
        .map(|(suffix, _)| name.clone().str(*suffix))
        .collect();
    if family.name != name
        || family.constructor_names != names
        || !family.level_params.is_empty()
        || family.num_params != 0
        || family.num_indices != 0
        || family.all_names != [name.clone()]
        || family.type_ != Expr::sort(Level::succ(Level::zero()))
        || env.get_const(&name).is_none_or(|info| {
            info.name != name
                || info.type_ != family.type_
                || !info.level_params.is_empty()
                || info.value.is_some()
        })
        || family.is_recursive
        || family.is_reflexive
        || family.is_nested
        || !family.is_large_elim
    {
        return Err("EvalIR syntax epoch mismatch: expected exact Release33 family".into());
    }
    for (index, ((_, fields), ctor_name)) in INSTRUCTION_HEADERS.iter().zip(&names).enumerate() {
        let ctor = env
            .get_constructor(ctor_name)
            .ok_or("missing canonical instruction constructor")?;
        let expected_type = constructor_type(fields);
        if ctor.name != *ctor_name
            || ctor.inductive_name != name
            || !ctor.level_params.is_empty()
            || ctor.num_params != 0
            || ctor.num_fields as usize != fields.len()
            || ctor.constructor_idx as usize != index
            || ctor.type_ != expected_type
            || env.get_const(ctor_name).is_none_or(|info| {
                info.name != *ctor_name
                    || info.type_ != expected_type
                    || !info.level_params.is_empty()
                    || info.value.is_some()
            })
        {
            return Err(format!(
                "EvalIR syntax constructor header mismatch: {ctor_name}"
            ));
        }
    }
    for suffix in ["rec", "casesOn", "recOn"] {
        let rec_name = name.clone().str(suffix);
        let rec = env
            .get_recursor(&rec_name)
            .ok_or("missing canonical instruction eliminator")?;
        env.authenticate_recursor_readonly(&rec_name)?;
        let auxiliary = suffix != "rec";
        let expected_order = if auxiliary {
            RecursorArgOrder::MajorAfterMotive
        } else {
            RecursorArgOrder::MajorAfterMinors
        };
        let expected_type = eliminator_type(auxiliary);
        if rec.name != rec_name
            || rec.inductive_name != name
            || rec.arg_order != expected_order
            || rec.level_params != [Name::from_string("u")]
            || rec.type_ != expected_type
            || rec.num_params != 0
            || rec.num_indices != 0
            || rec.num_motives != 1
            || rec.num_minors != 33
            || rec.rules.len() != 33
            || rec.is_k
            || env.get_const(&rec_name).is_none_or(|info| {
                info.name != rec_name
                    || info.type_ != rec.type_
                    || info.level_params != rec.level_params
                    || info.value.is_some() != auxiliary
            })
        {
            return Err(format!(
                "EvalIR syntax eliminator header mismatch: {rec_name}"
            ));
        }
        if auxiliary {
            let primitive = name.clone().str("rec");
            let arities: Vec<_> = INSTRUCTION_HEADERS
                .iter()
                .map(|(_, fields)| (fields.len() as u32, 0))
                .collect();
            // IRInst has no recursive fields: casesOn's eta-adapted minors are
            // definitionally recOn's pass-through minors. Use the existing kernel
            // canonical-wrapper authenticator for BOTH value-bearing auxiliaries.
            env.authenticate_cases_on_wrapper_readonly(&rec_name, &primitive, &arities)?;
            let info = env
                .get_const(&rec_name)
                .ok_or("missing authenticated auxiliary")?;
            let value = info
                .value
                .as_ref()
                .ok_or("missing canonical auxiliary value")?;
            let mut checker = TypeChecker::new(env);
            checker.set_allow_unsafe(false);
            checker.set_allow_partial(false);
            checker
                .check_type(value, &expected_type)
                .map_err(|error| format!("{rec_name}: strict auxiliary check: {error:?}"))?;
            if checker.heartbeat_spent() || clean_kernel::tc::declaration_budget_exhausted() {
                return Err(format!(
                    "{rec_name}: auxiliary authentication resource stop"
                ));
            }
        }
        for (rule, ((_, fields), ctor_name)) in
            rec.rules.iter().zip(INSTRUCTION_HEADERS.iter().zip(&names))
        {
            if rule.constructor_name != *ctor_name
                || rule.num_fields as usize != fields.len()
                || rule.recursive_fields.iter().any(|recursive| *recursive)
            {
                return Err(format!(
                    "EvalIR syntax eliminator rule mismatch: {ctor_name}"
                ));
            }
        }
    }
    Ok(EvalIrSyntaxIdentity {
        epoch: expected,
        irinst_closure_digest: env
            .closure_digest(&name)
            .map_err(|error| error.to_string())?,
    })
}

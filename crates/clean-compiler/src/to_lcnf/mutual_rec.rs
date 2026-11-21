// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Mutual and nested-mutual valueless kernel recursor lowering (`num_motives > 1`,
//! `num_indices == 0`) to a single self-recursive LCNF `FunDecl` dispatching on a
//! member tag (`0..M-1`).
//!
//! Covers both ordinary mutual blocks (`Even.rec` / `Odd.rec`) and restored
//! nested-inductive blocks (`Head.rec`, `Cert.rec`, `Head.rec_1`, ...), where
//! companion recursors `<first>.rec_N` eliminate their container inductive
//! (`RecursorVal::major_induct`, e.g. `List`) and each recursive field's target
//! member in `0..M` is read and verified fail-closed directly from the kernel's
//! restored `RecursorRule.rhs`.

use super::lower::{
    classify_expr_arg, collect_app_args, expr_to_arg, infer_type_or_placeholder,
    is_erased_constructor_field_type, lower_code, rec_minor_strategy_for, ExprArgClass,
    RecMinorStrategy, MAX_RUNTIME_APPLY_ARGS, NON_HEAP_RUNTIME_REPR,
};
use super::sink_ih::sink_ih_bindings;
use super::LcnfContext;
use crate::error::CompilerError;
use crate::lcnf::{Alt, Arg, Cases, Code, FunDecl, LetValue, Param};
use clean_kernel::{Environment, Expr, ExprKind, FVarId, Name, RecursorArgOrder, RecursorRule};

/// One constructor field in a mutual/nested-mutual recursor rule.
pub(super) struct MutualRecFieldSpec {
    pub(super) ty: Expr,
    pub(super) erased: bool,
    /// When `Some(target_m)`, this field is structurally recursive and its IH
    /// is computed by calling `go(apply_minors.., target_m, field)`.
    pub(super) target_member: Option<usize>,
}

/// Constructor arm in a member's `Cases`.
struct MutualRecArmSpec {
    ctor_name: Name,
    fields: Vec<MutualRecFieldSpec>,
    strategy: RecMinorStrategy,
    global_minor_idx: usize,
}

/// One member (`0..M-1`) of the mutual / nested-mutual recursor family.
struct MutualRecMemberSpec {
    major_ind_name: Name,
    arms: Vec<MutualRecArmSpec>,
}

/// Recognized saturated (or no-major) application of a mutual or nested-mutual
/// valueless kernel recursor.
pub(super) struct MutualRecApplyParts {
    entry_member_idx: usize,
    members: Vec<MutualRecMemberSpec>,
    major: Option<Expr>,
    minors: Vec<Expr>,
    extras: Vec<Expr>,
    rec_app: Expr,
}

/// Recognize a mutual or nested-mutual valueless kernel recursor application
/// (`num_motives > 1`, `num_indices == 0`) that [`lower_mutual_rec_apply`] can
/// compile to a single tag-dispatched self-recursive local function.
///
/// Ctx-free and side-effect-free: returns `None` (fail-closed) on any
/// unsupported shape, leaving the stage-2 valueless-recursor guard intact.
pub(super) fn mutual_rec_apply_parts(
    env: &Environment,
    expr: &Expr,
) -> Option<MutualRecApplyParts> {
    let (head, args) = collect_app_args(expr);
    let ExprKind::Const(rec_name, _) = head.kind() else {
        return None;
    };
    let last = rec_name.last_component()?;
    if last != "rec" && !is_companion_rec_suffix(&last) {
        return None;
    }
    let rec = env.get_recursor(rec_name)?;
    if env
        .get_const(rec_name)
        .is_some_and(|info| info.value.is_some())
    {
        return None;
    }

    // Single-motive recursors stay on `rec_apply_parts`; indexed families stay declined.
    if rec.num_motives <= 1 || rec.num_indices != 0 {
        return None;
    }

    let num_params = rec.num_params as usize;
    let num_motives = rec.num_motives as usize;
    let num_minors = rec.num_minors as usize;

    // Reconstruct the exact ordered family `[orig_0.rec, .., orig_{k-1}.rec, first.rec_1, ..]`
    // of length `num_motives`, mirroring `clean-elab`'s `recursor_minor_rules`.
    let base_ind = env.get_inductive(&rec.inductive_name)?;
    let first = base_ind.all_names.first()?;
    if base_ind.all_names.is_empty() || base_ind.all_names.len() > num_motives {
        return None;
    }

    let mut family: Vec<(Name, Name, &clean_kernel::inductive::RecursorVal)> =
        Vec::with_capacity(num_motives);
    for member_name in &base_ind.all_names {
        let member_ind = env.get_inductive(member_name)?;
        if member_ind.all_names != base_ind.all_names
            || member_ind.num_indices > 0
            || member_ind.is_reflexive
        {
            return None;
        }
        let m_rec_name = member_name.clone().str("rec");
        let m_rec = env.get_recursor(&m_rec_name)?;
        if env
            .get_const(&m_rec_name)
            .is_some_and(|info| info.value.is_some())
        {
            return None;
        }
        if m_rec.inductive_name != *member_name
            || m_rec.num_params != rec.num_params
            || m_rec.num_indices != 0
            || m_rec.num_motives != rec.num_motives
            || m_rec.num_minors != rec.num_minors
        {
            return None;
        }
        let major_ind_name = m_rec.major_induct()?.clone();
        if major_ind_name != *member_name {
            return None;
        }
        family.push((m_rec_name, major_ind_name, m_rec));
    }

    let mut companion_idx = 1usize;
    while family.len() < num_motives {
        let comp_name = first.clone().str(format!("rec_{companion_idx}"));
        let comp_rec = env.get_recursor(&comp_name)?;
        if env
            .get_const(&comp_name)
            .is_some_and(|info| info.value.is_some())
        {
            return None;
        }
        if comp_rec.inductive_name != *first
            || comp_rec.num_params != rec.num_params
            || comp_rec.num_indices != 0
            || comp_rec.num_motives != rec.num_motives
            || comp_rec.num_minors != rec.num_minors
            || comp_rec.rules.is_empty()
        {
            return None;
        }
        let major_ind_name = comp_rec.major_induct()?.clone();
        let major_ind = env.get_inductive(&major_ind_name)?;
        if major_ind.num_indices > 0 || major_ind.is_reflexive {
            return None;
        }
        family.push((comp_name, major_ind_name, comp_rec));
        companion_idx += 1;
    }

    let entry_member_idx = family.iter().position(|(rname, _, _)| rname == rec_name)?;

    // Spine arity & decomposition: params + motives + minors + major (+ extras).
    let expected = num_params + num_motives + num_minors + 1;
    let no_major =
        args.len() + 1 == expected && matches!(rec.arg_order, RecursorArgOrder::MajorAfterMinors);
    if args.len() < expected && !no_major {
        return None;
    }
    let (major, minors_start) = if no_major {
        (None, num_params + num_motives)
    } else {
        let (major_idx, minors_start) = match rec.arg_order {
            RecursorArgOrder::MajorAfterMinors => (expected - 1, num_params + num_motives),
            RecursorArgOrder::MajorAfterMotive => {
                (num_params + num_motives, num_params + num_motives + 1)
            }
        };
        (Some(args[major_idx]), minors_start)
    };
    let minors = &args[minors_start..minors_start + num_minors];
    let extras = if no_major { &[][..] } else { &args[expected..] };

    let mut rec_app = expr;
    for _ in 0..extras.len() {
        let ExprKind::App(f, _) = rec_app.kind() else {
            return None;
        };
        rec_app = f.as_ref();
    }

    // Total rules across all members must equal `num_minors`.
    let total_rules: usize = family.iter().map(|(_, _, r)| r.rules.len()).sum();
    if total_rules != num_minors {
        return None;
    }

    let family_rec_names: Vec<Name> = family.iter().map(|(n, _, _)| n.clone()).collect();
    let mut members = Vec::with_capacity(num_motives);
    let mut global_minor_idx = 0usize;

    for (_, major_ind_name, m_rec) in &family {
        let major_ind = env.get_inductive(major_ind_name)?;
        let ind_str = major_ind_name.to_string();
        // Heap-represented multi-ctor / payload inductives only (`Nat`, `Bool`,
        // scalar carriers, and PUnit-like 1-ctor 0-field types are declined).
        if ind_str == "Bool"
            || ind_str == "Nat"
            || NON_HEAP_RUNTIME_REPR.contains(&ind_str.as_str())
        {
            return None;
        }
        if m_rec.rules.len() == 1 && m_rec.rules[0].num_fields == 0 {
            return None;
        }
        if major_ind.constructor_names.len() != m_rec.rules.len() {
            return None;
        }

        let mut arms = Vec::with_capacity(m_rec.rules.len());
        for (ctor_name, rule) in major_ind.constructor_names.iter().zip(m_rec.rules.iter()) {
            if rule.constructor_name != *ctor_name {
                return None;
            }
            let ctor = env.get_constructor(ctor_name)?;
            if ctor.num_fields != rule.num_fields {
                return None;
            }
            if !point_ctor_targets_inductive(
                &ctor.type_,
                ctor.num_params,
                ctor.num_fields,
                major_ind_name,
            ) {
                return None;
            }

            let fields = verify_and_extract_rule_fields(
                env,
                rule,
                num_params,
                num_motives,
                num_minors,
                global_minor_idx,
                &family_rec_names,
            )?;

            let minor = minors[global_minor_idx];
            let erased_flags: Vec<(bool, bool)> = fields
                .iter()
                .map(|f| (f.erased, f.target_member.is_some()))
                .collect();
            let strategy = rec_minor_strategy_for(minor, &erased_flags);
            if matches!(strategy, RecMinorStrategy::Apply) {
                let num_ihs = fields.iter().filter(|f| f.target_member.is_some()).count();
                if fields.len() + num_ihs > MAX_RUNTIME_APPLY_ARGS {
                    return None;
                }
            }

            arms.push(MutualRecArmSpec {
                ctor_name: ctor_name.clone(),
                fields,
                strategy,
                global_minor_idx,
            });
            global_minor_idx += 1;
        }

        members.push(MutualRecMemberSpec {
            major_ind_name: major_ind_name.clone(),
            arms,
        });
    }

    if let Some(major) = major {
        if classify_expr_arg(env, major) != ExprArgClass::Normal {
            return None;
        }
    }
    if minors
        .iter()
        .any(|minor| classify_expr_arg(env, minor) != ExprArgClass::Normal)
    {
        return None;
    }

    Some(MutualRecApplyParts {
        entry_member_idx,
        members,
        major: major.cloned(),
        minors: minors.iter().map(|m| (*m).clone()).collect(),
        extras: extras.iter().map(|e| (*e).clone()).collect(),
        rec_app: rec_app.clone(),
    })
}

fn is_companion_rec_suffix(s: &str) -> bool {
    let Some(digits) = s.strip_prefix("rec_") else {
        return false;
    };
    !digits.is_empty() && digits.bytes().all(|b| b.is_ascii_digit())
}

fn point_ctor_targets_inductive(
    ctor_ty: &Expr,
    num_params: u32,
    num_fields: u32,
    ind_name: &Name,
) -> bool {
    let binders = u64::from(num_params) + u64::from(num_fields);
    let mut cur = ctor_ty;
    for _ in 0..binders {
        let ExprKind::Pi(_, _, body) = cur.kind() else {
            return false;
        };
        cur = body.as_ref();
    }
    matches!(cur.get_app_fn().kind(), ExprKind::Const(head, _) if head == ind_name)
}

/// Authenticate `rule.rhs` byte-for-byte against the kernel's canonical
/// `λ params. λ motives. λ minors. λ fields. minor fields.. IHs..` template,
/// extracting the restored field types and each recursive field's target member
/// index in `0..num_motives`.
fn verify_and_extract_rule_fields(
    env: &Environment,
    rule: &RecursorRule,
    np: usize,
    nm: usize,
    n_minors: usize,
    global_minor_idx: usize,
    family_rec_names: &[Name],
) -> Option<Vec<MutualRecFieldSpec>> {
    let nf = rule.num_fields as usize;
    let flags: Vec<bool> = if rule.recursive_fields.len() == nf {
        rule.recursive_fields.clone()
    } else if rule.recursive_fields.is_empty() && nf == 0 {
        Vec::new()
    } else {
        return None;
    };

    let prefix_binders = np + nm + n_minors;
    let total_binders = prefix_binders + nf;

    let mut cur = &rule.rhs;
    for _ in 0..prefix_binders {
        let ExprKind::Lam(_, _, inner) = cur.kind() else {
            return None;
        };
        cur = inner.as_ref();
    }

    let mut field_tys = Vec::with_capacity(nf);
    for _ in 0..nf {
        let ExprKind::Lam(_, dom, inner) = cur.kind() else {
            return None;
        };
        field_tys.push(dom.as_ref().clone());
        cur = inner.as_ref();
    }

    let num_ihs = flags.iter().filter(|&&b| b).count();
    let (b_head, b_args) = collect_app_args(cur);
    let expected_minor_bvar = (nf + n_minors).checked_sub(1 + global_minor_idx)? as u32;
    if !matches!(b_head.kind(), ExprKind::BVar(idx) if *idx == expected_minor_bvar) {
        return None;
    }
    if b_args.len() != nf + num_ihs {
        return None;
    }
    for (i, b_arg) in b_args.iter().enumerate().take(nf) {
        let expected_field_bvar = (nf - 1 - i) as u32;
        if !matches!(b_arg.kind(), ExprKind::BVar(idx) if *idx == expected_field_bvar) {
            return None;
        }
    }

    let mut ih_cursor = 0usize;
    let mut specs = Vec::with_capacity(nf);
    for (i, field_ty) in field_tys.into_iter().enumerate() {
        let erased = is_erased_constructor_field_type(env, &field_ty);
        let target_member = if flags[i] {
            if erased {
                return None;
            }
            let ih_expr = b_args[nf + ih_cursor];
            ih_cursor += 1;
            // Reflexive (Lam-headed) or indexed IHs fail this exact Const-spine check.
            let (ih_head, ih_args) = collect_app_args(ih_expr);
            let ExprKind::Const(ih_rec_name, _) = ih_head.kind() else {
                return None;
            };
            let target_m = family_rec_names.iter().position(|n| n == ih_rec_name)?;
            if ih_args.len() != prefix_binders + 1 {
                return None;
            }
            for (j, ih_arg) in ih_args.iter().enumerate().take(np) {
                let exp = (total_binders - 1 - j) as u32;
                if !matches!(ih_arg.kind(), ExprKind::BVar(idx) if *idx == exp) {
                    return None;
                }
            }
            for j in 0..nm {
                let exp = (nf + n_minors + nm - 1 - j) as u32;
                if !matches!(ih_args[np + j].kind(), ExprKind::BVar(idx) if *idx == exp) {
                    return None;
                }
            }
            for j in 0..n_minors {
                let exp = (nf + n_minors - 1 - j) as u32;
                if !matches!(ih_args[np + nm + j].kind(), ExprKind::BVar(idx) if *idx == exp) {
                    return None;
                }
            }
            let exp_field = (nf - 1 - i) as u32;
            if !matches!(ih_args[prefix_binders].kind(), ExprKind::BVar(idx) if *idx == exp_field) {
                return None;
            }
            Some(target_m)
        } else {
            None
        };
        specs.push(MutualRecFieldSpec {
            ty: field_ty,
            erased,
            target_member,
        });
    }

    Some(specs)
}

/// Lower a recognized mutual or nested-mutual recursor application by
/// synthesizing a single self-recursive `go(apply_minors.., tag : Nat, scrut : Object) : Object`.
pub(super) fn lower_mutual_rec_apply(
    ctx: &mut LcnfContext<'_>,
    expr: &Expr,
    parts: MutualRecApplyParts,
) -> Result<(LetValue, Expr), CompilerError> {
    let total_minors = parts.minors.len();
    let mut apply_minor_fvars: Vec<FVarId> = Vec::new();
    let mut apply_param_of_minor: Vec<Option<usize>> = vec![None; total_minors];

    for member in &parts.members {
        for arm in &member.arms {
            if matches!(arm.strategy, RecMinorStrategy::Apply) {
                match expr_to_arg(ctx, &parts.minors[arm.global_minor_idx])? {
                    Arg::FVar(id) => {
                        apply_param_of_minor[arm.global_minor_idx] = Some(apply_minor_fvars.len());
                        apply_minor_fvars.push(id);
                    }
                    other => {
                        return Err(CompilerError::InvalidExpr(format!(
                            "mutual recursor minor premise did not lower to a variable: {other:?}"
                        )))
                    }
                }
            }
        }
    }

    let scrut_fvar = match &parts.major {
        None => None,
        Some(major) => match expr_to_arg(ctx, major)? {
            Arg::FVar(id) => Some(id),
            other => {
                return Err(CompilerError::InvalidExpr(format!(
                    "mutual recursor major premise did not lower to a variable: {other:?}"
                )))
            }
        },
    };

    let obj_ty = Expr::const_str("Object");
    let nat_ty = Expr::const_str("Nat");

    let go_fvar = ctx.fresh_fvar();
    let minor_params: Vec<Param> = apply_minor_fvars
        .iter()
        .map(|_| Param::new(ctx.fresh_fvar(), Name::anon(), obj_ty.clone()))
        .collect();
    let tag_param = Param::new(ctx.fresh_fvar(), Name::anon(), nat_ty.clone());
    let scrut_param = Param::new(ctx.fresh_fvar(), Name::anon(), obj_ty.clone());

    let call_result_ty = if parts.major.is_some() {
        infer_type_or_placeholder(ctx.env, &parts.rec_app)
    } else {
        Expr::const_str("_")
    };
    let outer_result_ty = if parts.extras.is_empty() && parts.major.is_some() {
        call_result_ty.clone()
    } else {
        infer_type_or_placeholder(ctx.env, expr)
    };

    let minor_param_fvars: Vec<FVarId> = minor_params.iter().map(|p| p.fvar_id).collect();

    // Build per-member `Cases` over `scrut_param`.
    let mut member_codes: Vec<Code> = Vec::with_capacity(parts.members.len());
    for member in &parts.members {
        let mut alts = Vec::with_capacity(member.arms.len());
        for arm in &member.arms {
            let apply_param =
                apply_param_of_minor[arm.global_minor_idx].map(|idx| minor_param_fvars[idx]);
            let body = build_mutual_rec_arm_body(
                ctx,
                go_fvar,
                &minor_param_fvars,
                arm,
                apply_param,
                scrut_param.fvar_id,
            )?;
            alts.push(Alt::ctor(arm.ctor_name.clone(), Vec::new(), body));
        }
        member_codes.push(Code::Cases(Cases::new(
            member.major_ind_name.clone(),
            obj_ty.clone(),
            scrut_param.fvar_id,
            alts,
        )));
    }

    // Chain `Bool` `Cases` on `Nat.beq tag_param m` from `M - 2` down to `0`,
    // with member `M - 1` as the final `Bool.false` branch.
    let mut iter = member_codes.into_iter().enumerate().rev();
    let Some((_, mut dispatch_code)) = iter.next() else {
        return Err(CompilerError::InvalidExpr(
            "mutual recursor family has no members".into(),
        ));
    };
    for (m_idx, m_code) in iter {
        let outer_pending = ctx.take_pending();
        let m_lit = ctx.add_let(Name::anon(), nat_ty.clone(), LetValue::nat(m_idx as u64));
        let is_m = ctx.add_let(
            Name::anon(),
            Expr::const_str("Bool"),
            LetValue::Const {
                name: Name::from_string("Nat.beq"),
                levels: Vec::new(),
                args: vec![Arg::FVar(tag_param.fvar_id), Arg::FVar(m_lit)],
            },
        );
        let switch = Code::Cases(Cases::new(
            Name::from_string("Bool"),
            obj_ty.clone(),
            is_m,
            vec![
                Alt::ctor(Name::from_string("Bool.false"), Vec::new(), dispatch_code),
                Alt::ctor(Name::from_string("Bool.true"), Vec::new(), m_code),
            ],
        ));
        dispatch_code = ctx.wrap_lets(switch);
        ctx.restore_pending(outer_pending);
    }

    let mut params = minor_params;
    params.push(tag_param);
    params.push(scrut_param);
    ctx.add_fun(FunDecl::new(
        go_fvar,
        Name::from_string("_mrec"),
        params,
        obj_ty,
        dispatch_code,
    ));

    let entry_tag_fvar = ctx.add_let(
        Name::anon(),
        nat_ty,
        LetValue::nat(parts.entry_member_idx as u64),
    );
    let mut call_args: Vec<Arg> = apply_minor_fvars.into_iter().map(Arg::FVar).collect();
    call_args.push(Arg::FVar(entry_tag_fvar));
    if let Some(scrut_fvar) = scrut_fvar {
        call_args.push(Arg::FVar(scrut_fvar));
    }
    let call_value = LetValue::FVar {
        fvar: go_fvar,
        args: call_args,
    };
    if parts.extras.is_empty() {
        return Ok((call_value, outer_result_ty));
    }

    let extra_args = parts
        .extras
        .iter()
        .map(|extra| expr_to_arg(ctx, extra))
        .collect::<Result<Vec<_>, _>>()?;
    let call_fvar = ctx.add_let(Name::anon(), call_result_ty, call_value);
    Ok((
        LetValue::FVar {
            fvar: call_fvar,
            args: extra_args,
        },
        outer_result_ty,
    ))
}

fn build_mutual_rec_arm_body(
    ctx: &mut LcnfContext<'_>,
    go_fvar: FVarId,
    minor_params: &[FVarId],
    arm: &MutualRecArmSpec,
    apply_param: Option<FVarId>,
    scrut: FVarId,
) -> Result<Code, CompilerError> {
    let outer_pending = ctx.take_pending();
    let mut pushed = 0usize;

    let mut field_slots: Vec<(Option<FVarId>, Option<usize>)> =
        Vec::with_capacity(arm.fields.len());
    for (field_idx, field) in arm.fields.iter().enumerate() {
        if field.erased {
            let dummy = ctx.add_let(Name::anon(), Expr::const_str("_"), LetValue::Erased);
            ctx.bvar_stack.push(dummy);
            pushed += 1;
            field_slots.push((None, None));
            continue;
        }
        let field_fvar = ctx.add_let(
            Name::anon(),
            field.ty.clone(),
            LetValue::Proj {
                type_name: arm.ctor_name.clone(),
                idx: field_idx as u32,
                structure: scrut,
            },
        );
        ctx.bvar_stack.push(field_fvar);
        pushed += 1;
        field_slots.push((Some(field_fvar), field.target_member));
    }

    let mut ih_fvars: Vec<FVarId> = Vec::new();
    for (field_fvar, target_member) in &field_slots {
        let (Some(field_fvar), Some(target_m)) = (field_fvar, target_member) else {
            continue;
        };
        let target_tag_fvar = ctx.add_let(
            Name::anon(),
            Expr::const_str("Nat"),
            LetValue::nat(*target_m as u64),
        );
        let mut rec_args: Vec<Arg> = minor_params.iter().copied().map(Arg::FVar).collect();
        rec_args.push(Arg::FVar(target_tag_fvar));
        rec_args.push(Arg::FVar(*field_fvar));
        let ih_fvar = ctx.add_let(
            Name::anon(),
            Expr::const_str("_"),
            LetValue::FVar {
                fvar: go_fvar,
                args: rec_args,
            },
        );
        ctx.bvar_stack.push(ih_fvar);
        pushed += 1;
        ih_fvars.push(ih_fvar);
    }

    let result = match (&arm.strategy, apply_param) {
        (RecMinorStrategy::Inline { body }, _) => {
            let body = body.clone();
            lower_code(ctx, &body)
        }
        (RecMinorStrategy::Apply, Some(minor_param)) => {
            let mut apply_args: Vec<Arg> = Vec::with_capacity(arm.fields.len() + ih_fvars.len());
            for (field_fvar, _) in &field_slots {
                match field_fvar {
                    Some(fvar) => apply_args.push(Arg::FVar(*fvar)),
                    None => apply_args.push(Arg::Erased),
                }
            }
            apply_args.extend(ih_fvars.iter().copied().map(Arg::FVar));
            if apply_args.is_empty() {
                Ok(ctx.wrap_lets(Code::Return(minor_param)))
            } else {
                let result_fvar = ctx.add_let(
                    Name::anon(),
                    Expr::const_str("_"),
                    LetValue::FVar {
                        fvar: minor_param,
                        args: apply_args,
                    },
                );
                Ok(ctx.wrap_lets(Code::Return(result_fvar)))
            }
        }
        (RecMinorStrategy::Apply, None) => Err(CompilerError::InvalidExpr(
            "mutual recursor Apply arm without a minor parameter".into(),
        )),
    };

    for _ in 0..pushed {
        ctx.bvar_stack.pop();
    }
    match result {
        Ok(body) => {
            ctx.restore_pending(outer_pending);
            Ok(sink_ih_bindings(body, &ih_fvars))
        }
        Err(err) => {
            ctx.abandon_pending(outer_pending);
            Err(err)
        }
    }
}

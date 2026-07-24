// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Body-rewriting traversals for extended closure conversion.
//!
//! These functions perform recursive `IRBody` rewrites that inline, lower, hoist,
//! or defunctionalize closure bindings discovered by [`super::closure_convert_ext`].

use crate::ir::{CtorInfo, FnId, IRAlt, IRArg, IRBody, IRDecl, IRExpr, IRType, VarId};
use clean_kernel::Name;

use super::closure_convert_ext::ClosureBinding;
use super::closure_convert_ext::ClosureInfo;

// ---------------------------------------------------------------------------
// Generic body-recursive dispatch
// ---------------------------------------------------------------------------

/// Apply `f` to each immediate sub-body of `body`, collecting a `(IRBody, T)`
/// pair via a fold combinator. Falls through to cloning leaf nodes.
fn map_subbodies<T: Default + std::ops::BitOrAssign>(
    body: &IRBody,
    f: &mut impl FnMut(&IRBody) -> (IRBody, T),
) -> (IRBody, T) {
    match body {
        IRBody::VDecl {
            var,
            ty,
            value,
            rest,
        } => {
            let (rest, t) = f(rest);
            (
                IRBody::VDecl {
                    var: *var,
                    ty: ty.clone(),
                    value: value.clone(),
                    rest: Box::new(rest),
                },
                t,
            )
        }
        IRBody::JDecl {
            jp,
            params,
            body: jp_body,
            rest,
        } => {
            let (jp_body, mut t) = f(jp_body);
            let (rest, t2) = f(rest);
            t |= t2;
            (
                IRBody::JDecl {
                    jp: *jp,
                    params: params.clone(),
                    body: Box::new(jp_body),
                    rest: Box::new(rest),
                },
                t,
            )
        }
        IRBody::Inc { var, n, rest } => {
            let (rest, t) = f(rest);
            (
                IRBody::Inc {
                    var: *var,
                    n: *n,
                    rest: Box::new(rest),
                },
                t,
            )
        }
        IRBody::Dec { var, rest } => {
            let (rest, t) = f(rest);
            (
                IRBody::Dec {
                    var: *var,
                    rest: Box::new(rest),
                },
                t,
            )
        }
        IRBody::Set {
            var,
            idx,
            value,
            rest,
        } => {
            let (rest, t) = f(rest);
            (
                IRBody::Set {
                    var: *var,
                    idx: *idx,
                    value: *value,
                    rest: Box::new(rest),
                },
                t,
            )
        }
        IRBody::SetTag { var, tag, rest } => {
            let (rest, t) = f(rest);
            (
                IRBody::SetTag {
                    var: *var,
                    tag: *tag,
                    rest: Box::new(rest),
                },
                t,
            )
        }
        IRBody::USet {
            var,
            idx,
            value,
            rest,
        } => {
            let (rest, t) = f(rest);
            (
                IRBody::USet {
                    var: *var,
                    idx: *idx,
                    value: *value,
                    rest: Box::new(rest),
                },
                t,
            )
        }
        IRBody::SSet {
            var,
            n,
            offset,
            value,
            ty,
            rest,
        } => {
            let (rest, t) = f(rest);
            (
                IRBody::SSet {
                    var: *var,
                    n: *n,
                    offset: *offset,
                    value: *value,
                    ty: ty.clone(),
                    rest: Box::new(rest),
                },
                t,
            )
        }
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => {
            let mut t = T::default();
            let alts = alts
                .iter()
                .map(|alt| {
                    let (body, at) = f(&alt.body);
                    t |= at;
                    IRAlt {
                        ctor: alt.ctor.clone(),
                        body: Box::new(body),
                    }
                })
                .collect();
            let default = default.as_ref().map(|b| {
                let (body, dt) = f(b);
                t |= dt;
                Box::new(body)
            });
            (
                IRBody::Case {
                    scrutinee: *scrutinee,
                    alts,
                    default,
                },
                t,
            )
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => (body.clone(), T::default()),
    }
}

/// Fold variant that collects a `usize` count instead of a bool.
fn map_subbodies_count(
    body: &IRBody,
    f: &mut impl FnMut(&IRBody) -> (IRBody, usize),
) -> (IRBody, usize) {
    match body {
        IRBody::VDecl {
            var,
            ty,
            value,
            rest,
        } => {
            let (rest, c) = f(rest);
            (
                IRBody::VDecl {
                    var: *var,
                    ty: ty.clone(),
                    value: value.clone(),
                    rest: Box::new(rest),
                },
                c,
            )
        }
        IRBody::JDecl {
            jp,
            params,
            body: jp_body,
            rest,
        } => {
            let (jp_body, c1) = f(jp_body);
            let (rest, c2) = f(rest);
            (
                IRBody::JDecl {
                    jp: *jp,
                    params: params.clone(),
                    body: Box::new(jp_body),
                    rest: Box::new(rest),
                },
                c1 + c2,
            )
        }
        IRBody::Inc { var, n, rest } => {
            let (rest, c) = f(rest);
            (
                IRBody::Inc {
                    var: *var,
                    n: *n,
                    rest: Box::new(rest),
                },
                c,
            )
        }
        IRBody::Dec { var, rest } => {
            let (rest, c) = f(rest);
            (
                IRBody::Dec {
                    var: *var,
                    rest: Box::new(rest),
                },
                c,
            )
        }
        IRBody::Set {
            var,
            idx,
            value,
            rest,
        } => {
            let (rest, c) = f(rest);
            (
                IRBody::Set {
                    var: *var,
                    idx: *idx,
                    value: *value,
                    rest: Box::new(rest),
                },
                c,
            )
        }
        IRBody::SetTag { var, tag, rest } => {
            let (rest, c) = f(rest);
            (
                IRBody::SetTag {
                    var: *var,
                    tag: *tag,
                    rest: Box::new(rest),
                },
                c,
            )
        }
        IRBody::USet {
            var,
            idx,
            value,
            rest,
        } => {
            let (rest, c) = f(rest);
            (
                IRBody::USet {
                    var: *var,
                    idx: *idx,
                    value: *value,
                    rest: Box::new(rest),
                },
                c,
            )
        }
        IRBody::SSet {
            var,
            n,
            offset,
            value,
            ty,
            rest,
        } => {
            let (rest, c) = f(rest);
            (
                IRBody::SSet {
                    var: *var,
                    n: *n,
                    offset: *offset,
                    value: *value,
                    ty: ty.clone(),
                    rest: Box::new(rest),
                },
                c,
            )
        }
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => {
            let mut count = 0;
            let alts = alts
                .iter()
                .map(|alt| {
                    let (body, c) = f(&alt.body);
                    count += c;
                    IRAlt {
                        ctor: alt.ctor.clone(),
                        body: Box::new(body),
                    }
                })
                .collect();
            let default = default.as_ref().map(|b| {
                let (body, c) = f(b);
                count += c;
                Box::new(body)
            });
            (
                IRBody::Case {
                    scrutinee: *scrutinee,
                    alts,
                    default,
                },
                count,
            )
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => (body.clone(), 0),
    }
}

/// Three-value fold variant returning `(IRBody, bool, bool)`.
fn map_subbodies_triple(
    body: &IRBody,
    f: &mut impl FnMut(&IRBody) -> (IRBody, bool, bool),
) -> (IRBody, bool, bool) {
    match body {
        IRBody::VDecl {
            var,
            ty,
            value,
            rest,
        } => {
            let (rest, a, b) = f(rest);
            (
                IRBody::VDecl {
                    var: *var,
                    ty: ty.clone(),
                    value: value.clone(),
                    rest: Box::new(rest),
                },
                a,
                b,
            )
        }
        IRBody::JDecl {
            jp,
            params,
            body: jp_body,
            rest,
        } => {
            let (jp_body, a1, b1) = f(jp_body);
            let (rest, a2, b2) = f(rest);
            (
                IRBody::JDecl {
                    jp: *jp,
                    params: params.clone(),
                    body: Box::new(jp_body),
                    rest: Box::new(rest),
                },
                a1 || a2,
                b1 || b2,
            )
        }
        IRBody::Inc { var, n, rest } => {
            let (rest, a, b) = f(rest);
            (
                IRBody::Inc {
                    var: *var,
                    n: *n,
                    rest: Box::new(rest),
                },
                a,
                b,
            )
        }
        IRBody::Dec { var, rest } => {
            let (rest, a, b) = f(rest);
            (
                IRBody::Dec {
                    var: *var,
                    rest: Box::new(rest),
                },
                a,
                b,
            )
        }
        IRBody::Set {
            var,
            idx,
            value,
            rest,
        } => {
            let (rest, a, b) = f(rest);
            (
                IRBody::Set {
                    var: *var,
                    idx: *idx,
                    value: *value,
                    rest: Box::new(rest),
                },
                a,
                b,
            )
        }
        IRBody::SetTag { var, tag, rest } => {
            let (rest, a, b) = f(rest);
            (
                IRBody::SetTag {
                    var: *var,
                    tag: *tag,
                    rest: Box::new(rest),
                },
                a,
                b,
            )
        }
        IRBody::USet {
            var,
            idx,
            value,
            rest,
        } => {
            let (rest, a, b) = f(rest);
            (
                IRBody::USet {
                    var: *var,
                    idx: *idx,
                    value: *value,
                    rest: Box::new(rest),
                },
                a,
                b,
            )
        }
        IRBody::SSet {
            var,
            n,
            offset,
            value,
            ty,
            rest,
        } => {
            let (rest, a, b) = f(rest);
            (
                IRBody::SSet {
                    var: *var,
                    n: *n,
                    offset: *offset,
                    value: *value,
                    ty: ty.clone(),
                    rest: Box::new(rest),
                },
                a,
                b,
            )
        }
        IRBody::Case {
            scrutinee,
            alts,
            default,
        } => {
            let (mut ra, mut rb) = (false, false);
            let alts = alts
                .iter()
                .map(|alt| {
                    let (body, a, b) = f(&alt.body);
                    ra |= a;
                    rb |= b;
                    IRAlt {
                        ctor: alt.ctor.clone(),
                        body: Box::new(body),
                    }
                })
                .collect();
            let default = default.as_ref().map(|bo| {
                let (body, a, b) = f(bo);
                ra |= a;
                rb |= b;
                Box::new(body)
            });
            (
                IRBody::Case {
                    scrutinee: *scrutinee,
                    alts,
                    default,
                },
                ra,
                rb,
            )
        }
        IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => (body.clone(), false, false),
    }
}

// ---------------------------------------------------------------------------
// Inline closure applications whose replacement body is already specialized
// for the call site.
// ---------------------------------------------------------------------------

pub(crate) fn inline_thunk_calls(
    body: &IRBody,
    closure_var: VarId,
    closure_body: &IRBody,
) -> (IRBody, bool) {
    match body {
        IRBody::VDecl {
            var,
            ty,
            value:
                IRExpr::ClosureApply {
                    closure: IRArg::Var(v),
                    args: _,
                },
            rest,
        } if *v == closure_var => (
            crate::inline_pass::splice_inlined(closure_body.clone(), *var, ty.clone(), rest),
            true,
        ),
        _ => map_subbodies(body, &mut |b| {
            inline_thunk_calls(b, closure_var, closure_body)
        }),
    }
}

// ---------------------------------------------------------------------------
// Inline bound closure calls (full argument substitution)
// ---------------------------------------------------------------------------

pub(crate) fn inline_bound_closure_calls(
    body: &IRBody,
    closure_var: VarId,
    binding: &ClosureBinding,
    callee: &IRDecl,
    next_fresh: &mut u32,
) -> (IRBody, usize) {
    match body {
        IRBody::VDecl {
            var,
            ty,
            value:
                IRExpr::ClosureApply {
                    closure: IRArg::Var(v),
                    args,
                },
            rest,
        } if *v == closure_var && binding.captured_args.len() + args.len() == binding.arity => {
            let mut full_args = binding.captured_args.clone();
            full_args.extend(args.iter().cloned());
            if full_args.len() != callee.params.len() {
                return lower_exact_closure_calls_to_apply(
                    body,
                    closure_var,
                    &binding.fn_id,
                    &binding.captured_args,
                    binding.arity,
                )
                .into_count();
            }
            let offset = *next_fresh;
            let span = crate::inline_pass::max_var_id(&callee.body)
                .max(callee.params.iter().map(|(v, _)| v.0).max().unwrap_or(0))
                .saturating_add(1);
            *next_fresh = next_fresh.saturating_add(span.saturating_add(1));
            let inlined = crate::inline_pass::substitute_args(
                &callee.body,
                &callee.params,
                &full_args,
                offset,
            );
            (
                crate::inline_pass::splice_inlined(inlined, *var, ty.clone(), rest),
                1,
            )
        }
        _ => map_subbodies_count(body, &mut |b| {
            inline_bound_closure_calls(b, closure_var, binding, callee, next_fresh)
        }),
    }
}

// ---------------------------------------------------------------------------
// Lower exact closure calls to direct Apply
// ---------------------------------------------------------------------------

pub(crate) fn lower_exact_closure_calls_to_apply(
    body: &IRBody,
    closure_var: VarId,
    fn_id: &FnId,
    captured_args: &[IRArg],
    arity: usize,
) -> (IRBody, bool) {
    match body {
        IRBody::VDecl {
            var,
            ty,
            value:
                IRExpr::ClosureApply {
                    closure: IRArg::Var(v),
                    args,
                },
            rest,
        } if *v == closure_var && captured_args.len() + args.len() == arity => {
            let mut full_args = captured_args.to_vec();
            full_args.extend(args.iter().cloned());
            (
                IRBody::VDecl {
                    var: *var,
                    ty: ty.clone(),
                    value: IRExpr::Apply {
                        fn_id: fn_id.clone(),
                        args: full_args,
                    },
                    rest: rest.clone(),
                },
                true,
            )
        }
        _ => map_subbodies(body, &mut |b| {
            lower_exact_closure_calls_to_apply(b, closure_var, fn_id, captured_args, arity)
        }),
    }
}

// ---------------------------------------------------------------------------
// Remove binding and rewrite closure calls to hoisted wrapper
// ---------------------------------------------------------------------------

pub(crate) fn remove_binding_and_rewrite_calls(
    body: &IRBody,
    closure_var: VarId,
    hoisted_name: &Name,
    arity: usize,
) -> (IRBody, bool, bool) {
    match body {
        IRBody::VDecl {
            var,
            value: IRExpr::PartialApply { .. },
            rest,
            ..
        } if *var == closure_var => {
            let (rest, _, rewritten) =
                remove_binding_and_rewrite_calls(rest, closure_var, hoisted_name, arity);
            (rest, true, rewritten)
        }
        IRBody::VDecl {
            var,
            ty,
            value:
                IRExpr::ClosureApply {
                    closure: IRArg::Var(v),
                    args,
                },
            rest,
        } if *v == closure_var && args.len() == arity => (
            IRBody::VDecl {
                var: *var,
                ty: ty.clone(),
                value: IRExpr::Apply {
                    fn_id: FnId(hoisted_name.clone()),
                    args: args.clone(),
                },
                rest: rest.clone(),
            },
            false,
            true,
        ),
        _ => map_subbodies_triple(body, &mut |b| {
            remove_binding_and_rewrite_calls(b, closure_var, hoisted_name, arity)
        }),
    }
}

// ---------------------------------------------------------------------------
// Build defunctionalized apply body
// ---------------------------------------------------------------------------

pub(crate) fn build_defunctionalized_apply_body(
    apply_decl: &IRDecl,
    binding: &ClosureBinding,
    info: &ClosureInfo,
) -> IRBody {
    let env_var = apply_decl.params[0].0;
    let mut next_var = apply_decl
        .params
        .iter()
        .map(|(v, _)| v.0)
        .max()
        .unwrap_or(0)
        + 1;
    let projected: Vec<VarId> = (0..info.captured.len())
        .map(|_| {
            let v = VarId(next_var);
            next_var += 1;
            v
        })
        .collect();
    let mut full_args: Vec<IRArg> = projected.iter().map(|v| IRArg::Var(*v)).collect();
    full_args.extend(
        apply_decl
            .params
            .iter()
            .skip(1)
            .map(|(v, _)| IRArg::Var(*v)),
    );
    let result = VarId(next_var);
    let mut body = IRBody::VDecl {
        var: result,
        ty: IRType::Object,
        value: IRExpr::Apply {
            fn_id: binding.fn_id.clone(),
            args: full_args,
        },
        rest: Box::new(IRBody::Ret(IRArg::Var(result))),
    };
    for (idx, var) in projected.into_iter().enumerate().rev() {
        body = IRBody::VDecl {
            var,
            ty: IRType::Object,
            value: IRExpr::Proj {
                idx: idx as u32,
                ty: IRType::Object,
                arg: IRArg::Var(env_var),
            },
            rest: Box::new(body),
        };
    }
    body
}

// ---------------------------------------------------------------------------
// Defunctionalize closure bindings and calls
// ---------------------------------------------------------------------------

pub(crate) fn defunctionalize_body(
    body: &IRBody,
    closure_var: VarId,
    binding: &ClosureBinding,
    apply_decl: &IRDecl,
    env_ctor: &CtorInfo,
) -> (IRBody, bool) {
    match body {
        IRBody::VDecl {
            var,
            ty,
            value: IRExpr::PartialApply { .. },
            rest,
        } if *var == closure_var => (
            IRBody::VDecl {
                var: *var,
                ty: ty.clone(),
                value: IRExpr::Ctor {
                    info: env_ctor.clone(),
                    args: binding
                        .captured_args
                        .iter()
                        .filter_map(|arg| match arg {
                            IRArg::Var(v) => Some(IRArg::Var(*v)),
                            IRArg::Erased => None,
                        })
                        .collect(),
                },
                rest: rest.clone(),
            },
            true,
        ),
        IRBody::VDecl {
            var,
            ty,
            value:
                IRExpr::ClosureApply {
                    closure: IRArg::Var(v),
                    args,
                },
            rest,
        } if *v == closure_var && binding.captured_args.len() + args.len() == binding.arity => {
            let mut full_args = vec![IRArg::Var(closure_var)];
            full_args.extend(args.iter().cloned());
            (
                IRBody::VDecl {
                    var: *var,
                    ty: ty.clone(),
                    value: IRExpr::Apply {
                        fn_id: FnId(apply_decl.name.clone()),
                        args: full_args,
                    },
                    rest: rest.clone(),
                },
                true,
            )
        }
        _ => map_subbodies(body, &mut |b| {
            defunctionalize_body(b, closure_var, binding, apply_decl, env_ctor)
        }),
    }
}

// ---------------------------------------------------------------------------
// Helper to convert (IRBody, bool) → (IRBody, usize)
// ---------------------------------------------------------------------------

trait IntoBoolCount {
    fn into_count(self) -> (IRBody, usize);
}

impl IntoBoolCount for (IRBody, bool) {
    fn into_count(self) -> (IRBody, usize) {
        (self.0, if self.1 { 1 } else { 0 })
    }
}

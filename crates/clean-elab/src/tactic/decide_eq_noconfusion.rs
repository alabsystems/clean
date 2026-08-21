// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! NoConfusion-based inequality proof builder for `decide_eq`.
//!
//! Builds kernel-checkable proofs of `Eq ty lhs rhs → False` using
//! `T.noConfusion` for types with visible constructor discrimination.
//! Supports distinct constructors of any registered inductive, plus recursive
//! discrimination for Nat, Bool, Int, Char, String, UInt8/16/32/64, List,
//! `Option`, `Prod`, and `Sum` over supported element/component types. String
//! literals recurse through `String -> List Char -> Char -> Nat`.
//! `Option`/`Prod`/`Sum` recurse into their payload/component types (e.g.
//! `Option (Prod Nat Nat)`, `Sum Nat Nat`).
//!
//! Part of #302, #2154: eliminates trustedAy from decide_eq inequality branch.

use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr, ExprKind};

use crate::stack_safe;

use clean_kernel::expr::Literal;

#[path = "decide_eq_noconfusion_fin.rs"]
mod fin;
#[path = "decide_eq_noconfusion_wrappers.rs"]
mod wrappers;

use fin::build_fin_ne_body;
use wrappers::{
    char_type, eq_level_for_type, list_type, to_char_view, to_int_view, to_uint_view, IntView,
};

/// View of a Nat expression in constructor form.
enum NatView {
    Zero,
    Succ(Expr),
}

/// View of a String expression in constructor form.
enum StringView {
    Mk { data: Expr, form: Expr },
}

struct ListConsView {
    form: Expr,
    head: Expr,
    tail: Expr,
}

/// View of a List expression in constructor form.
enum ListView {
    Nil(Box<Expr>),
    Cons(Box<ListConsView>),
}

/// View of an Option expression in constructor form.
enum OptionView {
    None(Box<Expr>),
    Some { form: Expr, value: Expr },
}

/// View of a Prod expression in constructor form (`Prod.mk fst snd`).
struct ProdView {
    form: Expr,
    fst: Expr,
    snd: Expr,
}

/// View of a Sum expression in constructor form (`Sum.inl`/`Sum.inr`).
///
/// Sum is the two-constructor analogue of Option: each constructor carries a
/// single payload, drawn from the left (`α`) or right (`β`) summand.
enum SumView {
    Inl { form: Expr, payload: Expr },
    Inr { form: Expr, payload: Expr },
}

/// Match a Nat expression as constructor form (zero or succ).
fn to_nat_view(expr: &Expr) -> Option<NatView> {
    match expr.kind() {
        ExprKind::Lit(Literal::Nat(n)) => {
            let val = n.to_u64()?;
            if val == 0 {
                Some(NatView::Zero)
            } else {
                Some(NatView::Succ(Expr::nat_lit(val - 1)))
            }
        }
        ExprKind::Const(name, _) if name.to_string() == "Nat.zero" => Some(NatView::Zero),
        ExprKind::App(f, arg) => {
            if let ExprKind::Const(name, _) = f.kind() {
                if name.to_string() == "Nat.succ" {
                    return Some(NatView::Succ(arg.as_ref().clone()));
                }
            }
            None
        }
        _ => None,
    }
}

/// Expand a Nat literal to outermost constructor form for kernel proof terms.
///
/// `Lit(0)` → `Nat.zero`, `Lit(n)` → `Nat.succ(Lit(n-1))`.
/// Non-literal expressions pass through unchanged.
///
/// The kernel's `noConfusionType` reduction uses `casesOn` which requires
/// visible outermost constructors. Bare Nat literals don't WHNF-reduce to
/// constructors (WHNF returns `Lit` as-is), so the casesOn gets stuck.
/// Expanding one layer gives the constructor the kernel needs.
fn nat_lit_to_outer_ctor(expr: &Expr) -> Expr {
    match expr.kind() {
        ExprKind::Lit(Literal::Nat(n)) => {
            if let Some(val) = n.to_u64() {
                if val == 0 {
                    Expr::const_(Name::from_string("Nat.zero"), vec![])
                } else {
                    Expr::app(
                        Expr::const_(Name::from_string("Nat.succ"), vec![]),
                        Expr::nat_lit(val - 1),
                    )
                }
            } else {
                expr.clone()
            }
        }
        _ => expr.clone(),
    }
}

/// Expand a String literal to the constructor form Lean uses internally.
///
/// `Lit("ab")` becomes `String.ofList (List.cons (Char.ofNat 97) ...)`.
fn string_lit_to_constructor_form(s: &str) -> Expr {
    let string_of_list = Expr::const_(Name::from_string("String.ofList"), vec![]);
    let char_type = Expr::const_(Name::from_string("Char"), vec![]);
    let list_nil = Expr::app(
        Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
        char_type.clone(),
    );

    let mut char_list = list_nil;
    for c in s.chars().rev() {
        let char_val = Expr::app(
            Expr::const_(Name::from_string("Char.ofNat"), vec![]),
            Expr::nat_lit(c as u64),
        );
        char_list = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
                    char_type.clone(),
                ),
                char_val,
            ),
            char_list,
        );
    }

    Expr::app(string_of_list, char_list)
}

/// Expand a String literal to a form the kernel can delta-reduce to `String.mk`.
fn string_to_noconfusion_form(expr: &Expr) -> Expr {
    match expr.kind() {
        ExprKind::Lit(Literal::String(s)) => string_lit_to_constructor_form(s),
        _ => expr.clone(),
    }
}

/// Bundled context for recursive noConfusion proof building.
struct NoConfusionCtx {
    type_name: String,
    type_params: Vec<Expr>,
    nc_levels: Vec<Level>,
    nc_name: Name,
    /// Per-param premise data for the v4.30 heterogeneous convention
    /// (designs/2026-07-03-noconfusion-ctoridx-convention.md §3):
    /// `(instantiated param type A_k, sort of A_k, dependent?)`. The
    /// application supplies `Eq.refl`/`HEq.refl` for each (lhs and rhs share
    /// the same param instantiation). Empty for 0-param types, whose
    /// noConfusion shape is unchanged.
    param_premises: Vec<(Expr, Level, bool)>,
}

/// Does `e` reference any of the `limit` innermost enclosing binders?
/// Used on a RAW inductive-type param domain to decide Eq vs HEq for the
/// param premise (mirrors the kernel generator's rule).
fn mentions_bound_below(e: &Expr, limit: usize, depth: u32) -> bool {
    match e.kind() {
        ExprKind::BVar(idx) => *idx >= depth && ((*idx - depth) as usize) < limit,
        ExprKind::App(f, a) => {
            mentions_bound_below(f, limit, depth) || mentions_bound_below(a, limit, depth)
        }
        ExprKind::Pi(_, domain, body) | ExprKind::Lam(_, domain, body) => {
            mentions_bound_below(domain, limit, depth)
                || mentions_bound_below(body, limit, depth + 1)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            mentions_bound_below(ty, limit, depth)
                || mentions_bound_below(val, limit, depth)
                || mentions_bound_below(body, limit, depth + 1)
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
            mentions_bound_below(inner, limit, depth)
        }
        _ => false,
    }
}

fn build_ctx(env: &Environment, eq_ty: &Expr) -> Option<NoConfusionCtx> {
    let (type_name, ind_levels) = match eq_ty.get_app_fn().kind() {
        ExprKind::Const(name, levels) => (name.to_string(), levels.to_vec()),
        _ => return None,
    };

    let no_confusion_name = Name::from_string(&format!("{type_name}.noConfusion"));
    let nc_info = env.get_const(&no_confusion_name)?;
    let nc_level_count = nc_info.level_params.len();

    // Motive is False : Prop = Sort 0, so motive_level = 0.
    let nc_levels = if nc_level_count > ind_levels.len() {
        [vec![Level::zero()], ind_levels.clone()].concat()
    } else {
        ind_levels.clone()
    };

    let type_params: Vec<Expr> = eq_ty
        .get_app_args()
        .iter()
        .map(|arg| (*arg).clone())
        .collect();

    // v4.30 heterogeneous premises: one Eq/HEq per inductive param, computed
    // from the inductive's registered type instantiated at the goal's levels
    // and param args.
    let param_premises: Vec<(Expr, Level, bool)> = {
        let ind = env.get_inductive(&Name::from_string(&type_name))?;
        let n = ind.num_params as usize;
        if type_params.len() != n {
            // Under-applied inductive head — no premise construction possible.
            return None;
        }
        if n == 0 {
            Vec::new()
        } else {
            // Dependency flags come from the RAW (uninstantiated) walk, where
            // `A_k` still sees earlier params as BVar(0..k-1) — this mirrors
            // the kernel generator's Eq-vs-HEq premise rule exactly.
            let mut deps = Vec::with_capacity(n);
            {
                let mut cur = &ind.type_;
                for k in 0..n {
                    let ExprKind::Pi(_, domain, body) = cur.kind() else {
                        return None;
                    };
                    deps.push(mentions_bound_below(domain, k, 0));
                    cur = body;
                }
            }
            let mut out = Vec::with_capacity(n);
            let mut cur = ind
                .type_
                .instantiate_level_params_direct(&ind.level_params, &ind_levels);
            for (k, arg) in type_params.iter().enumerate() {
                let ExprKind::Pi(_, domain, body) = cur.kind() else {
                    return None;
                };
                let dom_inst = domain.as_ref().clone();
                let tc = clean_kernel::tc::TypeChecker::with_mode(env, env.mode());
                let sort = tc.infer_sort(&dom_inst).ok()?;
                out.push((dom_inst, sort, deps[k]));
                cur = body.instantiate(arg);
            }
            out
        }
    };

    Some(NoConfusionCtx {
        type_name,
        type_params,
        nc_levels,
        nc_name: no_confusion_name,
        param_premises,
    })
}

fn to_string_view(expr: &Expr) -> Option<StringView> {
    let form = string_to_noconfusion_form(expr);
    match form.kind() {
        ExprKind::App(f, arg) => match f.kind() {
            ExprKind::Const(name, _) => match name.to_string().as_str() {
                "String.mk" | "String.ofList" => Some(StringView::Mk {
                    data: arg.as_ref().clone(),
                    form,
                }),
                _ => None,
            },
            _ => None,
        },
        _ => None,
    }
}

fn to_list_view(expr: &Expr) -> Option<ListView> {
    let head = expr.get_app_fn();
    let args = expr.get_app_args();
    match head.kind() {
        ExprKind::Const(name, _) if name.to_string() == "List.nil" && args.len() == 1 => {
            Some(ListView::Nil(Box::new(expr.clone())))
        }
        ExprKind::Const(name, _) if name.to_string() == "List.cons" && args.len() == 3 => {
            Some(ListView::Cons(Box::new(ListConsView {
                form: expr.clone(),
                head: args[1].clone(),
                tail: args[2].clone(),
            })))
        }
        _ => None,
    }
}

/// Match an Option expression as constructor form (`Option.none α` or
/// `Option.some α value`).
fn to_option_view(expr: &Expr) -> Option<OptionView> {
    let head = expr.get_app_fn();
    let args = expr.get_app_args();
    match head.kind() {
        ExprKind::Const(name, _) if name.to_string() == "Option.none" && args.len() == 1 => {
            Some(OptionView::None(Box::new(expr.clone())))
        }
        ExprKind::Const(name, _) if name.to_string() == "Option.some" && args.len() == 2 => {
            Some(OptionView::Some {
                form: expr.clone(),
                value: args[1].clone(),
            })
        }
        _ => None,
    }
}

/// Match a Prod expression as constructor form (`Prod.mk α β fst snd`).
fn to_prod_view(expr: &Expr) -> Option<ProdView> {
    let head = expr.get_app_fn();
    let args = expr.get_app_args();
    match head.kind() {
        ExprKind::Const(name, _) if name.to_string() == "Prod.mk" && args.len() == 4 => {
            Some(ProdView {
                form: expr.clone(),
                fst: args[2].clone(),
                snd: args[3].clone(),
            })
        }
        _ => None,
    }
}

/// Match a Sum expression as constructor form (`Sum.inl α β val` or
/// `Sum.inr α β val`). Both constructors carry two implicit type params
/// followed by a single payload, so the payload is `args[2]`.
fn to_sum_view(expr: &Expr) -> Option<SumView> {
    let head = expr.get_app_fn();
    let args = expr.get_app_args();
    match head.kind() {
        ExprKind::Const(name, _) if name.to_string() == "Sum.inl" && args.len() == 3 => {
            Some(SumView::Inl {
                form: expr.clone(),
                payload: args[2].clone(),
            })
        }
        ExprKind::Const(name, _) if name.to_string() == "Sum.inr" && args.len() == 3 => {
            Some(SumView::Inr {
                form: expr.clone(),
                payload: args[2].clone(),
            })
        }
        _ => None,
    }
}

/// Build a kernel-checkable inequality proof using T.noConfusion.
///
/// Returns `Some(proof)` where `proof : Eq ty lhs rhs → False` if the
/// inequality can be witnessed by constructor discrimination. For Nat,
/// handles recursive succ/succ stripping down to a zero/succ base case.
///
/// Returns `None` for types without a visible `.noConfusion` constant or
/// for non-manifest constructor forms. Part of #302, #2154.
///
/// REQUIRES: `eq_ty`, `lhs`, and `rhs` describe the same equality domain
/// REQUIRES: `eq_level` is the universe level to use for `Eq`
///
/// ENSURES: on `Some(proof)`, `proof` is a lambda whose binder type is `Eq eq_ty lhs rhs`
/// ENSURES: on `Some(proof)`, the lambda body is constructed to derive `False` via `.noConfusion`
/// ENSURES: returns `None` when no supported constructor-discrimination proof is available
pub(crate) fn build_noconfusion_ne_proof(
    env: &Environment,
    eq_ty: &Expr,
    lhs: &Expr,
    rhs: &Expr,
    eq_level: &Level,
) -> Option<Expr> {
    stack_safe(|| build_ne_body(env, eq_ty, lhs, rhs, eq_level, 0))
}

/// Recursive helper: build `fun (h : Eq ty lhs rhs) => ... → False`.
fn build_ne_body(
    env: &Environment,
    eq_ty: &Expr,
    lhs: &Expr,
    rhs: &Expr,
    eq_level: &Level,
    depth: usize,
) -> Option<Expr> {
    stack_safe(|| {
        if depth > 128 {
            return None;
        }

        let ctx = build_ctx(env, eq_ty)?;
        let false_expr = Expr::const_(Name::from_string("False"), vec![]);

        if ctx.type_name == "Nat" {
            let lv = to_nat_view(lhs)?;
            let rv = to_nat_view(rhs)?;

            // Expand Nat literals to visible constructors so noConfusionType can reduce;
            // the kernel still treats Lit(n) and Nat.succ(Lit(n-1)) as definitionally equal.
            let lhs_c = nat_lit_to_outer_ctor(lhs);
            let rhs_c = nat_lit_to_outer_ctor(rhs);
            let eq_app = mk_eq_expr(eq_ty, &lhs_c, &rhs_c, eq_level);

            match (&lv, &rv) {
                (NatView::Zero, NatView::Succ(_)) | (NatView::Succ(_), NatView::Zero) => {
                    let nc_app =
                        mk_noconfusion_app(&ctx, &false_expr, &lhs_c, &rhs_c, eq_ty, eq_level);
                    Some(Expr::lam(clean_kernel::BinderInfo::Default, eq_app, nc_app))
                }
                (NatView::Succ(pred_l), NatView::Succ(pred_r)) => {
                    let continuation =
                        build_ne_body(env, eq_ty, pred_l, pred_r, eq_level, depth + 1)?;
                    let nc_app =
                        mk_noconfusion_app(&ctx, &false_expr, &lhs_c, &rhs_c, eq_ty, eq_level);
                    let applied = Expr::app(nc_app, continuation);
                    Some(Expr::lam(
                        clean_kernel::BinderInfo::Default,
                        eq_app,
                        applied,
                    ))
                }
                _ => None,
            }
        } else if ctx.type_name == "Int" {
            let lhs_view = to_int_view(lhs)?;
            let rhs_view = to_int_view(rhs)?;
            let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
            let nat_eq_level = Level::succ(Level::zero());
            let eq_app = mk_eq_expr(eq_ty, lhs_view.form(), rhs_view.form(), eq_level);
            let nc_app = mk_noconfusion_app(
                &ctx,
                &false_expr,
                lhs_view.form(),
                rhs_view.form(),
                eq_ty,
                eq_level,
            );

            match (&lhs_view, &rhs_view) {
                (IntView::OfNat(_), IntView::NegSucc(_))
                | (IntView::NegSucc(_), IntView::OfNat(_)) => {
                    Some(Expr::lam(clean_kernel::BinderInfo::Default, eq_app, nc_app))
                }
                (IntView::OfNat(_), IntView::OfNat(_))
                | (IntView::NegSucc(_), IntView::NegSucc(_)) => {
                    let continuation = build_ne_body(
                        env,
                        &nat_ty,
                        lhs_view.field(),
                        rhs_view.field(),
                        &nat_eq_level,
                        depth + 1,
                    )?;
                    Some(Expr::lam(
                        clean_kernel::BinderInfo::Default,
                        eq_app,
                        Expr::app(nc_app, continuation),
                    ))
                }
            }
        } else if ctx.type_name == "Bool" {
            let eq_app = mk_eq_expr(eq_ty, lhs, rhs, eq_level);
            let nc_app = mk_noconfusion_app(&ctx, &false_expr, lhs, rhs, eq_ty, eq_level);
            Some(Expr::lam(clean_kernel::BinderInfo::Default, eq_app, nc_app))
        } else if ctx.type_name == "Char" {
            // Genuine v4.30 Char is the 2-field structure `Char.mk (val : UInt32)
            // (valid : val.isValidChar)`, so the 1-field noConfusion diagonal (a
            // bare-`Nat` field) no longer applies. Disprove `lhs = rhs` via the
            // code-point `Char.toNat`: `congrArg Char.toNat h : Char.toNat lhs =
            // Char.toNat rhs`, refuted by the `Nat` disproof of the code points
            // (`to_char_view.field`; `Char.toNat (Char.ofNat n) ≡ n` by the native
            // reducer). Mirrors the kernel's `mk_char_dec_is_false`; axiom-free —
            // `congrArg` needs no injectivity.
            let lhs_view = to_char_view(lhs)?;
            let rhs_view = to_char_view(rhs)?;

            let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
            let nat_eq_level = Level::succ(Level::zero());
            let nat_disproof = build_ne_body(
                env,
                &nat_ty,
                &lhs_view.field,
                &rhs_view.field,
                &nat_eq_level,
                depth + 1,
            )?;
            let eq_app = mk_eq_expr(eq_ty, &lhs_view.form, &rhs_view.form, eq_level);
            let one = Level::succ(Level::zero());
            // @congrArg.{1,1} Char Nat lhs rhs Char.toNat (h : lhs = rhs)
            let cong = Expr::apps(
                Expr::const_(Name::from_string("congrArg"), vec![one.clone(), one]),
                [
                    char_type(),
                    nat_ty.clone(),
                    lhs_view.form.clone(),
                    rhs_view.form.clone(),
                    Expr::const_(Name::from_string("Char.toNat"), vec![]),
                    Expr::bvar(0),
                ],
            );
            Some(Expr::lam(
                clean_kernel::BinderInfo::Default,
                eq_app,
                Expr::app(nat_disproof, cong),
            ))
        } else if ctx.type_name == "String" {
            let StringView::Mk {
                data: lhs_data,
                form: lhs_form,
            } = to_string_view(lhs)?;
            let StringView::Mk {
                data: rhs_data,
                form: rhs_form,
            } = to_string_view(rhs)?;

            let list_char_ty = list_type(char_type());
            let list_eq_level = Level::succ(Level::zero());
            let continuation = build_ne_body(
                env,
                &list_char_ty,
                &lhs_data,
                &rhs_data,
                &list_eq_level,
                depth + 1,
            )?;
            let eq_app = mk_eq_expr(eq_ty, &lhs_form, &rhs_form, eq_level);
            let nc_app =
                mk_noconfusion_app(&ctx, &false_expr, &lhs_form, &rhs_form, eq_ty, eq_level);
            Some(Expr::lam(
                clean_kernel::BinderInfo::Default,
                eq_app,
                Expr::app(nc_app, continuation),
            ))
        } else if matches!(
            ctx.type_name.as_str(),
            "UInt8" | "UInt16" | "UInt32" | "UInt64"
        ) {
            let lhs_view = to_uint_view(lhs, &ctx.type_name)?;
            let rhs_view = to_uint_view(rhs, &ctx.type_name)?;
            let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
            let nat_eq_level = Level::succ(Level::zero());
            let continuation = build_ne_body(
                env,
                &nat_ty,
                &lhs_view.field,
                &rhs_view.field,
                &nat_eq_level,
                depth + 1,
            )?;
            let eq_app = mk_eq_expr(eq_ty, &lhs_view.form, &rhs_view.form, eq_level);
            let nc_app = mk_noconfusion_app(
                &ctx,
                &false_expr,
                &lhs_view.form,
                &rhs_view.form,
                eq_ty,
                eq_level,
            );
            Some(Expr::lam(
                clean_kernel::BinderInfo::Default,
                eq_app,
                Expr::app(nc_app, continuation),
            ))
        } else if ctx.type_name == "Fin" {
            build_fin_ne_body(env, &ctx, eq_ty, lhs, rhs, eq_level, depth)
        } else if ctx.type_name == "List" {
            let elem_ty = ctx.type_params.first()?.clone();
            let elem_eq_level = eq_level_for_type(&elem_ty)?;
            let lhs_view = to_list_view(lhs)?;
            let rhs_view = to_list_view(rhs)?;

            match (lhs_view, rhs_view) {
                // Cross-constructor `nil`/`cons`: preserve goal lhs/rhs
                // orientation (#39 — same orientation fix as Option none/some).
                (ListView::Nil(lhs_form), ListView::Cons(rhs_cons)) => {
                    let lhs_form = lhs_form.as_ref();
                    let rhs_form = &rhs_cons.form;
                    let eq_app = mk_eq_expr(eq_ty, lhs_form, rhs_form, eq_level);
                    let nc_app =
                        mk_noconfusion_app(&ctx, &false_expr, lhs_form, rhs_form, eq_ty, eq_level);
                    Some(Expr::lam(clean_kernel::BinderInfo::Default, eq_app, nc_app))
                }
                (ListView::Cons(lhs_cons), ListView::Nil(rhs_form)) => {
                    let lhs_form = &lhs_cons.form;
                    let rhs_form = rhs_form.as_ref();
                    let eq_app = mk_eq_expr(eq_ty, lhs_form, rhs_form, eq_level);
                    let nc_app =
                        mk_noconfusion_app(&ctx, &false_expr, lhs_form, rhs_form, eq_ty, eq_level);
                    Some(Expr::lam(clean_kernel::BinderInfo::Default, eq_app, nc_app))
                }
                (ListView::Cons(lhs_cons), ListView::Cons(rhs_cons)) => {
                    // v4.30 convention: both cons fields (`head : α`,
                    // `tail : List α`) mention the param α, so the diagonal
                    // chain carries HEq hypotheses; the recursive Eq-based
                    // sub-proofs consume them through eq_of_heq.
                    let head_heq = mk_heq_expr(
                        &elem_ty,
                        &lhs_cons.head,
                        &elem_ty,
                        &rhs_cons.head,
                        &elem_eq_level,
                    );
                    let tail_heq =
                        mk_heq_expr(eq_ty, &lhs_cons.tail, eq_ty, &rhs_cons.tail, eq_level);

                    let continuation_body = if let Some(head_proof) = build_ne_body(
                        env,
                        &elem_ty,
                        &lhs_cons.head,
                        &rhs_cons.head,
                        &elem_eq_level,
                        depth + 1,
                    ) {
                        Expr::app(
                            head_proof,
                            mk_eq_of_heq(
                                &elem_ty,
                                &lhs_cons.head,
                                &rhs_cons.head,
                                Expr::bvar(1),
                                &elem_eq_level,
                            ),
                        )
                    } else {
                        let tail_proof = build_ne_body(
                            env,
                            eq_ty,
                            &lhs_cons.tail,
                            &rhs_cons.tail,
                            eq_level,
                            depth + 1,
                        )?;
                        Expr::app(
                            tail_proof,
                            mk_eq_of_heq(
                                eq_ty,
                                &lhs_cons.tail,
                                &rhs_cons.tail,
                                Expr::bvar(0),
                                eq_level,
                            ),
                        )
                    };

                    let continuation = Expr::lam(
                        clean_kernel::BinderInfo::Default,
                        head_heq,
                        Expr::lam(
                            clean_kernel::BinderInfo::Default,
                            tail_heq,
                            continuation_body,
                        ),
                    );
                    let eq_app = mk_eq_expr(eq_ty, &lhs_cons.form, &rhs_cons.form, eq_level);
                    let nc_app = mk_noconfusion_app(
                        &ctx,
                        &false_expr,
                        &lhs_cons.form,
                        &rhs_cons.form,
                        eq_ty,
                        eq_level,
                    );
                    Some(Expr::lam(
                        clean_kernel::BinderInfo::Default,
                        eq_app,
                        Expr::app(nc_app, continuation),
                    ))
                }
                _ => None,
            }
        } else if ctx.type_name == "Option" {
            let elem_ty = ctx.type_params.first()?.clone();
            let elem_eq_level = eq_level_for_type(&elem_ty)?;
            let lhs_view = to_option_view(lhs)?;
            let rhs_view = to_option_view(rhs)?;

            match (lhs_view, rhs_view) {
                // Cross-constructor `none`/`some`: noConfusionType reduces
                // directly to the goal, so `nc_app` discharges it. The
                // constructor forms MUST preserve the goal's lhs/rhs orientation
                // — `@Option.noConfusionType False lhs rhs` δι-reduces to `False`
                // for any pair of distinct constructors (both `some/none` and
                // `none/some` directions), so the lambda binder type is
                // `Eq (Option α) lhs rhs` matching the goal. (#39: previously
                // this arm hard-coded `none`=lhs/`some`=rhs, producing a
                // well-typed term of the WRONG orientation that `close_goal`'s
                // strict def-eq check rejected.)
                (OptionView::None(lhs_form), OptionView::Some { form: rhs_form, .. }) => {
                    let lhs_form = lhs_form.as_ref();
                    let eq_app = mk_eq_expr(eq_ty, lhs_form, &rhs_form, eq_level);
                    let nc_app =
                        mk_noconfusion_app(&ctx, &false_expr, lhs_form, &rhs_form, eq_ty, eq_level);
                    Some(Expr::lam(clean_kernel::BinderInfo::Default, eq_app, nc_app))
                }
                (OptionView::Some { form: lhs_form, .. }, OptionView::None(rhs_form)) => {
                    let rhs_form = rhs_form.as_ref();
                    let eq_app = mk_eq_expr(eq_ty, &lhs_form, rhs_form, eq_level);
                    let nc_app =
                        mk_noconfusion_app(&ctx, &false_expr, &lhs_form, rhs_form, eq_ty, eq_level);
                    Some(Expr::lam(clean_kernel::BinderInfo::Default, eq_app, nc_app))
                }
                // `some a`/`some b`: noConfusionType reduces to `(a = b → P) → P`,
                // so recurse into the payload to derive `a = b → False`.
                (
                    OptionView::Some {
                        form: lhs_form,
                        value: lhs_val,
                    },
                    OptionView::Some {
                        form: rhs_form,
                        value: rhs_val,
                    },
                ) => {
                    let value_proof = build_ne_body(
                        env,
                        &elem_ty,
                        &lhs_val,
                        &rhs_val,
                        &elem_eq_level,
                        depth + 1,
                    )?;
                    // v4.30 convention: the payload field `val : α` mentions
                    // the param, so the chain hypothesis is HEq — adapt the
                    // Eq-based payload proof with eq_of_heq.
                    let val_heq =
                        mk_heq_expr(&elem_ty, &lhs_val, &elem_ty, &rhs_val, &elem_eq_level);
                    let continuation = Expr::lam(
                        clean_kernel::BinderInfo::Default,
                        val_heq,
                        Expr::app(
                            value_proof,
                            mk_eq_of_heq(
                                &elem_ty,
                                &lhs_val,
                                &rhs_val,
                                Expr::bvar(0),
                                &elem_eq_level,
                            ),
                        ),
                    );
                    let eq_app = mk_eq_expr(eq_ty, &lhs_form, &rhs_form, eq_level);
                    let nc_app = mk_noconfusion_app(
                        &ctx,
                        &false_expr,
                        &lhs_form,
                        &rhs_form,
                        eq_ty,
                        eq_level,
                    );
                    Some(Expr::lam(
                        clean_kernel::BinderInfo::Default,
                        eq_app,
                        Expr::app(nc_app, continuation),
                    ))
                }
                // `none`/`none` are reflexively equal — no inequality proof.
                (OptionView::None(_), OptionView::None(_)) => None,
            }
        } else if ctx.type_name == "Prod" {
            // Prod is a single-constructor structure: noConfusionType for
            // `mk a b`/`mk c d` reduces to `(a = c → b = d → P) → P`. The
            // continuation receives both component equalities; deriving `False`
            // from either one suffices.
            let fst_ty = ctx.type_params.first()?.clone();
            let snd_ty = ctx.type_params.get(1)?.clone();
            let fst_eq_level = eq_level_for_type(&fst_ty)?;
            let snd_eq_level = eq_level_for_type(&snd_ty)?;
            let lhs_view = to_prod_view(lhs)?;
            let rhs_view = to_prod_view(rhs)?;

            // v4.30 convention: both components (`fst : α`, `snd : β`) mention
            // params, so the chain hypotheses are HEq; the recursive Eq-based
            // sub-proofs consume them through eq_of_heq.
            let fst_heq = mk_heq_expr(
                &fst_ty,
                &lhs_view.fst,
                &fst_ty,
                &rhs_view.fst,
                &fst_eq_level,
            );
            let snd_heq = mk_heq_expr(
                &snd_ty,
                &lhs_view.snd,
                &snd_ty,
                &rhs_view.snd,
                &snd_eq_level,
            );

            // BVar(1) = first-component hyp, BVar(0) = second-component hyp.
            let continuation_body = if let Some(fst_proof) = build_ne_body(
                env,
                &fst_ty,
                &lhs_view.fst,
                &rhs_view.fst,
                &fst_eq_level,
                depth + 1,
            ) {
                Expr::app(
                    fst_proof,
                    mk_eq_of_heq(
                        &fst_ty,
                        &lhs_view.fst,
                        &rhs_view.fst,
                        Expr::bvar(1),
                        &fst_eq_level,
                    ),
                )
            } else {
                let snd_proof = build_ne_body(
                    env,
                    &snd_ty,
                    &lhs_view.snd,
                    &rhs_view.snd,
                    &snd_eq_level,
                    depth + 1,
                )?;
                Expr::app(
                    snd_proof,
                    mk_eq_of_heq(
                        &snd_ty,
                        &lhs_view.snd,
                        &rhs_view.snd,
                        Expr::bvar(0),
                        &snd_eq_level,
                    ),
                )
            };

            let continuation = Expr::lam(
                clean_kernel::BinderInfo::Default,
                fst_heq,
                Expr::lam(
                    clean_kernel::BinderInfo::Default,
                    snd_heq,
                    continuation_body,
                ),
            );
            let eq_app = mk_eq_expr(eq_ty, &lhs_view.form, &rhs_view.form, eq_level);
            let nc_app = mk_noconfusion_app(
                &ctx,
                &false_expr,
                &lhs_view.form,
                &rhs_view.form,
                eq_ty,
                eq_level,
            );
            Some(Expr::lam(
                clean_kernel::BinderInfo::Default,
                eq_app,
                Expr::app(nc_app, continuation),
            ))
        } else if ctx.type_name == "Sum" {
            // Sum is the two-constructor analogue of Option: `inl` carries a
            // left-summand payload, `inr` a right-summand one.
            let left_ty = ctx.type_params.first()?.clone();
            let right_ty = ctx.type_params.get(1)?.clone();
            let left_eq_level = eq_level_for_type(&left_ty)?;
            let right_eq_level = eq_level_for_type(&right_ty)?;
            let lhs_view = to_sum_view(lhs)?;
            let rhs_view = to_sum_view(rhs)?;

            match (lhs_view, rhs_view) {
                // Cross-constructor `inl`/`inr`: noConfusionType reduces directly
                // to the goal, so `nc_app` discharges it (mirrors Option none/some).
                (SumView::Inl { form: lhs_form, .. }, SumView::Inr { form: rhs_form, .. })
                | (SumView::Inr { form: lhs_form, .. }, SumView::Inl { form: rhs_form, .. }) => {
                    let eq_app = mk_eq_expr(eq_ty, &lhs_form, &rhs_form, eq_level);
                    let nc_app = mk_noconfusion_app(
                        &ctx,
                        &false_expr,
                        &lhs_form,
                        &rhs_form,
                        eq_ty,
                        eq_level,
                    );
                    Some(Expr::lam(clean_kernel::BinderInfo::Default, eq_app, nc_app))
                }
                // `inl a`/`inl b`: noConfusionType reduces to `(a = b → P) → P`,
                // so recurse into the left payload to derive `a = b → False`.
                (
                    SumView::Inl {
                        form: lhs_form,
                        payload: lhs_val,
                    },
                    SumView::Inl {
                        form: rhs_form,
                        payload: rhs_val,
                    },
                ) => {
                    let payload_proof = build_ne_body(
                        env,
                        &left_ty,
                        &lhs_val,
                        &rhs_val,
                        &left_eq_level,
                        depth + 1,
                    )?;
                    // v4.30 convention: the payload mentions the param → HEq
                    // chain hypothesis, adapted with eq_of_heq.
                    let val_heq =
                        mk_heq_expr(&left_ty, &lhs_val, &left_ty, &rhs_val, &left_eq_level);
                    let continuation = Expr::lam(
                        clean_kernel::BinderInfo::Default,
                        val_heq,
                        Expr::app(
                            payload_proof,
                            mk_eq_of_heq(
                                &left_ty,
                                &lhs_val,
                                &rhs_val,
                                Expr::bvar(0),
                                &left_eq_level,
                            ),
                        ),
                    );
                    let eq_app = mk_eq_expr(eq_ty, &lhs_form, &rhs_form, eq_level);
                    let nc_app = mk_noconfusion_app(
                        &ctx,
                        &false_expr,
                        &lhs_form,
                        &rhs_form,
                        eq_ty,
                        eq_level,
                    );
                    Some(Expr::lam(
                        clean_kernel::BinderInfo::Default,
                        eq_app,
                        Expr::app(nc_app, continuation),
                    ))
                }
                // `inr a`/`inr b`: symmetric to the `inl`/`inl` case, recursing
                // into the right payload.
                (
                    SumView::Inr {
                        form: lhs_form,
                        payload: lhs_val,
                    },
                    SumView::Inr {
                        form: rhs_form,
                        payload: rhs_val,
                    },
                ) => {
                    let payload_proof = build_ne_body(
                        env,
                        &right_ty,
                        &lhs_val,
                        &rhs_val,
                        &right_eq_level,
                        depth + 1,
                    )?;
                    // v4.30 convention: HEq chain hypothesis (see inl/inl).
                    let val_heq =
                        mk_heq_expr(&right_ty, &lhs_val, &right_ty, &rhs_val, &right_eq_level);
                    let continuation = Expr::lam(
                        clean_kernel::BinderInfo::Default,
                        val_heq,
                        Expr::app(
                            payload_proof,
                            mk_eq_of_heq(
                                &right_ty,
                                &lhs_val,
                                &rhs_val,
                                Expr::bvar(0),
                                &right_eq_level,
                            ),
                        ),
                    );
                    let eq_app = mk_eq_expr(eq_ty, &lhs_form, &rhs_form, eq_level);
                    let nc_app = mk_noconfusion_app(
                        &ctx,
                        &false_expr,
                        &lhs_form,
                        &rhs_form,
                        eq_ty,
                        eq_level,
                    );
                    Some(Expr::lam(
                        clean_kernel::BinderInfo::Default,
                        eq_app,
                        Expr::app(nc_app, continuation),
                    ))
                }
            }
        } else {
            // Generic finite-inductive lane: different registered constructors
            // of the same inductive require no field-continuation.  The
            // generated noConfusionType reduces directly to False.
            //
            // This deliberately does not attempt same-constructor recursion:
            // that needs the type-specific Eq/HEq diagonal described above.
            let lhs_head = lhs.get_app_fn();
            let rhs_head = rhs.get_app_fn();
            let (ExprKind::Const(lhs_name, _), ExprKind::Const(rhs_name, _)) =
                (lhs_head.kind(), rhs_head.kind())
            else {
                return None;
            };
            if lhs_name == rhs_name {
                return None;
            }
            let lhs_ctor = env.get_constructor(lhs_name)?;
            let rhs_ctor = env.get_constructor(rhs_name)?;
            if lhs_ctor.inductive_name != rhs_ctor.inductive_name
                || lhs_ctor.inductive_name.to_string() != ctx.type_name
            {
                return None;
            }

            let eq_app = mk_eq_expr(eq_ty, lhs, rhs, eq_level);
            let nc_app = mk_noconfusion_app(&ctx, &false_expr, lhs, rhs, eq_ty, eq_level);
            Some(Expr::lam(clean_kernel::BinderInfo::Default, eq_app, nc_app))
        }
    })
}

/// Build `@Eq.{eq_level} eq_ty lhs rhs`.
///
/// REQUIRES: `eq_ty`, `lhs`, and `rhs` are well-formed Lean expressions
///
/// ENSURES: returns the expression `@Eq.{eq_level} eq_ty lhs rhs`
/// ENSURES: preserves the input expressions structurally except for assembling the `Eq` application
pub(crate) fn mk_eq_expr(eq_ty: &Expr, lhs: &Expr, rhs: &Expr, eq_level: &Level) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![eq_level.clone()]),
                eq_ty.clone(),
            ),
            lhs.clone(),
        ),
        rhs.clone(),
    )
}

/// Build `@HEq.{level} ty_a a ty_b b`.
///
/// Under the v4.30 heterogeneous convention, param-mentioning constructor
/// fields carry HEq diagonal hypotheses (design §3); at concrete goals both
/// sides share the same instantiated type.
pub(crate) fn mk_heq_expr(ty_a: &Expr, a: &Expr, ty_b: &Expr, b: &Expr, level: &Level) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("HEq"), vec![level.clone()]),
                    ty_a.clone(),
                ),
                a.clone(),
            ),
            ty_b.clone(),
        ),
        b.clone(),
    )
}

/// Build `@eq_of_heq.{level} ty a b h` — converts an HEq diagonal hypothesis
/// back to the Eq the recursive sub-proofs consume.
pub(crate) fn mk_eq_of_heq(ty: &Expr, a: &Expr, b: &Expr, h: Expr, level: &Level) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("eq_of_heq"), vec![level.clone()]),
                    ty.clone(),
                ),
                a.clone(),
            ),
            b.clone(),
        ),
        h,
    )
}

/// Build the v4.30 heterogeneous noConfusion application
/// (designs/2026-07-03-noconfusion-ctoridx-convention.md §3/§5-N2):
///
/// ```text
/// @T.noConfusion.{0, ls} False p… lhs p… rhs
///   (Eq.refl A₁ p₁) … (Eq.refl Aₙ pₙ)        -- per-param premises
///   (@heq_of_eq.{eq_level} eq_ty lhs rhs h)  -- t ≍ t' major premise
/// ```
///
/// (`HEq.refl` for dependent params.) For `num_params = 0` the schemes
/// coincide and this emits the classic `@T.noConfusion.{0,…} False lhs rhs h`.
///
/// `BVar(0)` refers to the immediately enclosing lambda binder (the equality
/// hypothesis `h : Eq eq_ty lhs rhs`). All other subterms are closed.
fn mk_noconfusion_app(
    ctx: &NoConfusionCtx,
    motive: &Expr,
    lhs: &Expr,
    rhs: &Expr,
    eq_ty: &Expr,
    eq_level: &Level,
) -> Expr {
    let mut nc = Expr::const_(ctx.nc_name.clone(), ctx.nc_levels.clone());
    nc = Expr::app(nc, motive.clone());
    for param in &ctx.type_params {
        nc = Expr::app(nc, param.clone());
    }
    nc = Expr::app(nc, lhs.clone());
    if ctx.param_premises.is_empty() {
        // 0-param: {P} {t} {t'} (h : t = t') — unchanged classic shape.
        return Expr::app(Expr::app(nc, rhs.clone()), Expr::bvar(0));
    }
    for param in &ctx.type_params {
        nc = Expr::app(nc, param.clone());
    }
    nc = Expr::app(nc, rhs.clone());
    for (param, (dom, sort, dep)) in ctx.type_params.iter().zip(&ctx.param_premises) {
        let refl_name = if *dep { "HEq.refl" } else { "Eq.refl" };
        let refl = Expr::app(
            Expr::app(
                Expr::const_(Name::from_string(refl_name), vec![sort.clone()]),
                dom.clone(),
            ),
            param.clone(),
        );
        nc = Expr::app(nc, refl);
    }
    // Major premise: heq_of_eq eq_ty lhs rhs h.
    let major = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("heq_of_eq"), vec![eq_level.clone()]),
                    eq_ty.clone(),
                ),
                lhs.clone(),
            ),
            rhs.clone(),
        ),
        Expr::bvar(0),
    );
    Expr::app(nc, major)
}

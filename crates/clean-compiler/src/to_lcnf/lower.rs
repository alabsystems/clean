// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! LCNF lowering: erasure analysis, expression conversion, and recursion detection.

use super::mentions::{code_called_constant_names, expr_called_constant_names};
use super::LcnfContext;
use crate::error::CompilerError;
use crate::lcnf::{Alt, Arg, Cases, Code, Decl, FunDecl, LetDecl, LetValue, Param};
use clean_kernel::{
    env::ConstantKind, tc::TypeChecker, ConstantInfo, Environment, Expr, ExprKind, Level, Name,
};
use std::collections::HashSet;

/// Check if an expression is computationally irrelevant (proof or type).
///
/// Returns true if the expression should be erased at runtime.
/// An expression is erasable if:
/// - It is a type (Sort _)
/// - It is an SProp value
/// - Its type is a Sort or SProp (types/proofs are computationally irrelevant)
///
/// Note: This is a conservative analysis. If type inference fails,
/// we assume the expression is NOT erasable (safe default).
pub fn is_erasable(env: &Environment, expr: &Expr) -> bool {
    matches!(
        classify_expr_arg(env, expr),
        ExprArgClass::Erased | ExprArgClass::Type
    )
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum ExprArgClass {
    Erased,
    Type,
    Normal,
}

/// Check if a type is a singleton (has exactly one constructor with no non-erased fields).
///
/// Singleton types are computationally irrelevant because they can only have one value.
/// Examples: Unit, PUnit, True (the proposition).
///
/// A type is singleton if:
/// 1. It is an inductive type
/// 2. It has exactly one constructor
/// 3. All fields of that constructor are erasable (proofs or types)
pub(super) fn is_singleton_type(env: &Environment, ty: &Expr) -> bool {
    // Get the head of the type (stripping applications)
    let head = ty.get_app_fn();

    // Check if it's a constant (inductive type name)
    let type_name = match head.kind() {
        ExprKind::Const(name, _) => name,
        _ => return false,
    };

    // Look up the inductive type
    let ind_val = match env.get_inductive(type_name) {
        Some(ind) => ind,
        None => return false,
    };

    // Must have exactly one constructor
    if ind_val.constructor_names.len() != 1 {
        return false;
    }

    // Look up the constructor
    let ctor_name = &ind_val.constructor_names[0];
    let ctor_val = match env.get_constructor(ctor_name) {
        Some(ctor) => ctor,
        None => return false,
    };

    // All fields must be erasable
    // num_fields is the count of non-parameter fields
    // If num_fields > 0, we need to check if each field type is erasable
    if ctor_val.num_fields == 0 {
        // No fields beyond parameters - definitely singleton
        return true;
    }

    // For constructors with fields, we need to check if all field types are erasable.
    // The constructor type is: (params...) → (field₁ : T₁) → ... → (fieldₙ : Tₙ) → IndType params
    // We need to skip num_params Pi binders, then check each remaining domain type.
    let ctor_type = &ctor_val.type_;

    // Skip parameters
    let mut current = ctor_type;
    for _ in 0..ctor_val.num_params {
        if let ExprKind::Pi(_, _, body) = current.kind() {
            current = body.as_ref();
        } else {
            return false; // Malformed constructor type
        }
    }

    // Now check each field - all must be erasable
    for _ in 0..ctor_val.num_fields {
        if let ExprKind::Pi(_, domain, body) = current.kind() {
            // Check whether values of this field type are erasable.
            if !is_erased_constructor_field_type(env, domain.as_ref()) {
                return false;
            }
            current = body.as_ref();
        } else {
            return false; // Malformed constructor type
        }
    }

    true
}

fn is_erased_constructor_field_type(env: &Environment, field_ty: &Expr) -> bool {
    if matches!(field_ty.kind(), ExprKind::Sort(_) | ExprKind::SProp) {
        return true;
    }

    let tc = TypeChecker::with_mode(env, env.mode());
    if let Ok(field_ty_type) = tc.infer_type(field_ty) {
        if field_ty_type.is_prop() || matches!(field_ty_type.kind(), ExprKind::SProp) {
            return true;
        }
    }

    is_singleton_type(env, field_ty)
}

pub(super) fn classify_expr_arg(env: &Environment, expr: &Expr) -> ExprArgClass {
    if matches!(expr.kind(), ExprKind::Sort(_) | ExprKind::SProp) {
        return ExprArgClass::Type;
    }

    // A Pi is ALWAYS a type (its own type is a Sort), even when the term is
    // open. Whole-term inference below fails on open terms (loose BVars from
    // the enclosing stripped binders), and its fail-closed `Normal` fallback
    // used to send type-position Pis (e.g. the motive body `a -> a -> Bool`
    // inside `BEq.beq`'s `BEq.rec` spine) into the let-value catch-all as an
    // "Expression form: Pi(..)" error. Classify syntactically instead (C5a).
    if matches!(expr.kind(), ExprKind::Pi(_, _, _)) {
        return ExprArgClass::Type;
    }

    // A lambda whose (fully peeled) body is a type is a type-level function —
    // the `motive` of a `<Ind>.rec` elimination (`fun _ => Bool` in
    // `Decidable.decide`, `fun _ => Nat` in `Fin.val`): no runtime content.
    // Whole-term inference cannot see this: for OPEN motives it fails
    // outright, and even for closed ones it infers a Pi, not a Sort. Only the
    // `Type` verdict propagates out of the peeled body — any other verdict
    // (including the fail-closed `Normal` on inference failure) falls through
    // to the ordinary inference path below, so data-returning lambdas are
    // never erased by this arm (C5a).
    if matches!(expr.kind(), ExprKind::Lam(_, _, _)) {
        let mut body = expr;
        while let ExprKind::Lam(_, _, b) = body.kind() {
            body = b.as_ref();
        }
        if classify_expr_arg(env, body) == ExprArgClass::Type {
            return ExprArgClass::Type;
        }
    }

    let tc = TypeChecker::with_mode(env, env.mode());
    let expr_type = match tc.infer_type(expr) {
        Ok(ty) => ty,
        // Whole-term inference FAILED — the expression carries loose BVars peeled
        // out of an enclosing binder (a Prop/Type subterm of a `<Ind>.rec`
        // motive, a `Decidable`-instance spine, or a proof body). Before falling
        // back to the fail-closed `Normal` verdict — which MATERIALIZED a
        // type/prop FORMER as a dangling runtime call (`l_And` / `l_Or` /
        // `l_Nat_le` in `Char.ofNat`'s decidability spine; the `l_Nat_le` /
        // `l_Eq` inside proof bodies) that the native link's shim selection
        // fails-closed on — try one exact SYNTACTIC check: an application whose
        // HEAD constant's DECLARED (closed) type is a Pi-telescope ending in a
        // `Sort`/`SProp` IS a type/prop, computationally irrelevant regardless of
        // the open arguments. The head's declared type is closed, so peeling its
        // telescope is exact — this fires only on a genuine type/prop former
        // (`And` / `Or` / `Nat.le` / `LT.lt` / `Decidable` / `List` / …), never
        // on a data constructor (codomain is the inductive it builds — an
        // application, not a `Sort`) or a data function. Closed terms keep their
        // existing (inference-based) classification below, unchanged.
        Err(_) => {
            let mut head = expr;
            loop {
                match head.kind() {
                    ExprKind::App(f, _) => head = f.as_ref(),
                    ExprKind::MData(_, inner) => head = inner.as_ref(),
                    _ => break,
                }
            }
            if let ExprKind::Const(head_name, _) = head.kind() {
                if let Some(head_info) = env.get_const(head_name) {
                    let mut codomain = &head_info.type_;
                    while let ExprKind::Pi(_, _, body) = codomain.kind() {
                        codomain = body.as_ref();
                    }
                    if matches!(codomain.kind(), ExprKind::Sort(_) | ExprKind::SProp) {
                        return ExprArgClass::Type;
                    }
                }
            }
            return ExprArgClass::Normal;
        }
    };

    // Check for proofs (Prop or SProp)
    if expr_type.is_prop() || matches!(expr_type.kind(), ExprKind::SProp) {
        return ExprArgClass::Erased;
    }

    // Check for types AND type/prop FORMERS (a Pi chain ending in a Sort:
    // `Nat.le : Nat → Nat → Prop`, `Or : Prop → Prop → Prop`, …). A former
    // has no runtime value; materializing a bare reference to one emitted a
    // call/closure over a symbol nothing can ever define (`instLENat`'s
    // `LE.mk Nat.le` produced `l_Nat_le()` — an uncompilable 0-arg call to
    // a 2-ary extern prototype, R3).
    if matches!(expr_type.kind(), ExprKind::Sort(_))
        || crate::to_mono::is_type_former_type(&expr_type)
    {
        return ExprArgClass::Type;
    }

    // Check for singleton types
    if is_singleton_type(env, &expr_type) {
        return ExprArgClass::Erased;
    }

    ExprArgClass::Normal
}

/// Convert a kernel expression to an L5CNF argument.
///
/// Simple expressions (FVar, erased) become arguments directly.
/// Complex expressions are let-bound first.
pub(super) fn expr_to_arg(ctx: &mut LcnfContext<'_>, expr: &Expr) -> Result<Arg, CompilerError> {
    match classify_expr_arg(ctx.env, expr) {
        ExprArgClass::Erased => return Ok(Arg::Erased),
        ExprArgClass::Type => return Ok(Arg::Type(expr.clone())),
        ExprArgClass::Normal => {}
    }

    // A partially-applied constructor used as a first-class value (`List.cons α`
    // as `instInsertList`'s `Insert.mk` field) has no faithful direct `Ctor`
    // placement — saturate it under fresh field binders so it lambda-lifts to a
    // closure via the existing saturated-call + apply discipline.
    if let Some(eta) = eta_expand_partial_ctor(ctx.env, expr) {
        return expr_to_arg(ctx, &eta);
    }

    match expr.kind() {
        // Free variable - direct reference
        ExprKind::FVar(id) => Ok(Arg::FVar(*id)),

        // Bound variable - look up in context
        ExprKind::BVar(idx) => {
            if let Some(fvar) = ctx.lookup_bvar(*idx) {
                Ok(Arg::FVar(fvar))
            } else {
                Err(CompilerError::InvalidExpr(format!(
                    "Unbound variable: BVar({idx})"
                )))
            }
        }

        // Runtime lambda argument - lower to a local LCNF function value.
        ExprKind::Lam(_, _, _) => {
            let fun = expr_to_local_fun(ctx, expr)?;
            let fvar = fun.fvar_id;
            ctx.add_fun(fun);
            Ok(Arg::FVar(fvar))
        }

        // Other expressions need to be let-bound
        _ => {
            // First convert to a let-bound value
            let (value, ty) = expr_to_let_value(ctx, expr)?;
            let fvar = ctx.add_let(Name::anon(), ty, value);
            Ok(Arg::FVar(fvar))
        }
    }
}

fn expr_to_local_fun(ctx: &mut LcnfContext<'_>, expr: &Expr) -> Result<FunDecl, CompilerError> {
    let fvar = ctx.fresh_fvar();
    let mut params = Vec::new();
    let mut curr = expr;
    let outer_pending = ctx.take_pending();

    while let ExprKind::Lam(_, ty, body) = curr.kind() {
        let param_fvar = ctx.push_binder();
        params.push(Param::new(param_fvar, Name::anon(), ty.as_ref().clone()));
        curr = body.as_ref();
    }

    let result_ty = infer_type_or_placeholder(ctx.env, curr);
    let body_result = expr_to_code(ctx, curr);

    for _ in &params {
        ctx.pop_binder();
    }

    let body = match body_result {
        Ok(body) => body,
        Err(err) => {
            ctx.abandon_pending(outer_pending);
            return Err(err);
        }
    };

    ctx.restore_pending(outer_pending);
    Ok(FunDecl::new(
        fvar,
        Name::from_string("_lambda"),
        params,
        result_ty,
        body,
    ))
}

/// Try to infer the type of an expression, falling back to placeholder `_`.
///
/// Uses the kernel type checker. If inference fails (e.g., unbound variables,
/// partial expressions), returns `Expr::const_str("_")` as a safe default.
fn infer_type_or_placeholder(env: &Environment, expr: &Expr) -> Expr {
    let tc = TypeChecker::with_mode(env, env.mode());
    tc.infer_type(expr).unwrap_or_else(|_| Expr::const_str("_"))
}

/// Whether a type expression is the synthetic `_` placeholder produced by
/// [`infer_type_or_placeholder`] on inference failure (rejected fail-closed
/// by `to_ir` in value positions — see `to_ir::types::expr_to_ir_type`).
fn is_type_placeholder(ty: &Expr) -> bool {
    matches!(ty.kind(), ExprKind::Const(name, _) if name.to_string() == "_")
}

/// Convert a kernel expression to an L5CNF let-value.
///
/// Returns the let-value and its type.
pub(super) fn expr_to_let_value(
    ctx: &mut LcnfContext<'_>,
    expr: &Expr,
) -> Result<(LetValue, Expr), CompilerError> {
    match expr.kind() {
        // Literals
        ExprKind::Lit(lit) => {
            let ty = match lit {
                clean_kernel::Literal::Nat(_) => Expr::const_str("Nat"),
                clean_kernel::Literal::String(_) => Expr::const_str("String"),
            };
            Ok((LetValue::Lit(lit.clone()), ty))
        }

        // Constant application - collect arguments
        ExprKind::Const(name, levels) => {
            let levels_vec: Vec<Level> = levels.iter().cloned().collect();
            // Look up type from environment, falling back to placeholder if not found
            let ty = ctx
                .env
                .instantiate_type(name, &levels_vec)
                .unwrap_or_else(|| Expr::const_str("_"));
            // Constructors stay spelled as `Const`; `to_ir::lower_const_application`
            // recognizes constructor names (via `ctor_env`) and emits a
            // `lean_alloc_ctor` allocation rather than a runtime-function call.
            Ok((
                LetValue::Const {
                    name: name.clone(),
                    levels: levels_vec,
                    args: Vec::new(),
                },
                ty,
            ))
        }

        // Application - flatten and convert
        ExprKind::App(_, _) => {
            // R1: a saturated valueless-kernel-recursor application becomes a
            // call to a synthesized local recursive function (the eliminator
            // compiled from source), instead of an extern `Const` call to a
            // symbol nothing can ever provide. Recognition is ctx-free and
            // fail-closed; declined spines keep the generic path below (and
            // with it the stage-2 recursor-call guard). Sitting here — the
            // single funnel for value-position applications — this covers
            // let-value, argument, AND (via `expr_to_code`'s fallthrough arm)
            // return positions; the dedicated `Nat.rec` / non-recursive
            // `<Ind>.rec`-as-`Cases` arms in `expr_to_code` still win their
            // shapes first in return position.
            // R3: a PROOF elimination over a multi-constructor Prop-sorted
            // inductive is ERASED here, before the synthesized-recursion
            // path can compile it into runtime code. The kernel's small-
            // elimination restriction makes every legal such application
            // Prop-valued (a proof), and its major premise is an ERASED
            // proof at runtime — the R2-shipped `Char.ofNatAux` carrier
            // compiled its `Or`-eliminating validity chain into a `go` that
            // `clean_ctor_get`s the fields of `box(0)` (a segfault on the
            // erased-proof ABI) and stranded the whole `2^32` bound chain
            // per call. See [`prop_multi_ctor_elim`].
            if prop_multi_ctor_elim(ctx.env, expr) {
                return Ok((LetValue::Erased, Expr::const_str("_")));
            }
            // RUNG B: a saturated WELL-FOUNDED eliminator (`Acc.rec`,
            // `WellFounded.fixF`, `WellFounded.fix`) becomes a synthesized
            // value-recursive `go` — recursion on the recovered INDEX value,
            // never on the erased `Acc` proof (the C3 erased-proof hazard).
            // Placed before `rec_apply_parts` (which declines reflexive `Acc`
            // structurally) and after `prop_multi_ctor_elim`. Fail-closed.
            if let Some(parts) = wf_rec_apply_parts(ctx.env, expr) {
                return lower_wf_rec_apply(ctx, expr, parts);
            }
            if let Some(parts) = rec_apply_parts(ctx.env, expr) {
                return lower_rec_apply(ctx, expr, parts);
            }
            let (head, args) = collect_app_args(expr);
            let lcnf_args = args
                .into_iter()
                .map(|a| expr_to_arg(ctx, a))
                .collect::<Result<Vec<_>, _>>()?;

            // Infer the result type of the full application expression.
            // Falls back to placeholder if inference fails (e.g., unbound variables).
            let app_ty = infer_type_or_placeholder(ctx.env, expr);

            match head.kind() {
                ExprKind::Const(name, levels) => {
                    let levels_vec: Vec<Level> = levels.iter().cloned().collect();
                    // Constructors (e.g. `Option.some 5`, `List.cons 7 []`) stay
                    // spelled as `Const`; `to_ir::lower_const_application` lowers
                    // constructor names to a `lean_alloc_ctor` allocation.
                    Ok((
                        LetValue::Const {
                            name: name.clone(),
                            levels: levels_vec,
                            args: lcnf_args,
                        },
                        app_ty,
                    ))
                }
                ExprKind::FVar(id) => Ok((
                    LetValue::FVar {
                        fvar: *id,
                        args: lcnf_args,
                    },
                    app_ty,
                )),
                ExprKind::BVar(idx) => {
                    if let Some(fvar) = ctx.lookup_bvar(*idx) {
                        Ok((
                            LetValue::FVar {
                                fvar,
                                args: lcnf_args,
                            },
                            app_ty,
                        ))
                    } else {
                        Err(CompilerError::InvalidExpr(format!(
                            "Unbound variable in application head: BVar({idx})"
                        )))
                    }
                }
                // Application head is a projection out of a (dictionary) value:
                // a typeclass method dispatched through its instance. E.g.
                // `Ord.compare` projects field 0 (the `compare` fn) out of its
                // `Ord` instance (a bound variable) and applies it. Bind the
                // projected function to a temporary via the same discipline
                // `expr_to_arg` uses for a projection value, then emit an
                // indirect call on it (the `FVar`/`BVar`-head form above).
                //
                // A Prop-/type-valued class head (`LE.le`, `LT.lt`,
                // `Membership.mem`) dispatches the SAME way but its result is
                // computationally irrelevant — erase the whole application to
                // the erased token (exactly Lean's own erasure), never a real
                // indirect call, matching the erased-stub discipline.
                ExprKind::Proj(..) => {
                    if is_erasable(ctx.env, expr) {
                        Ok((LetValue::Erased, Expr::const_str("_")))
                    } else {
                        match expr_to_arg(ctx, head)? {
                            Arg::FVar(fvar) => Ok((
                                LetValue::FVar {
                                    fvar,
                                    args: lcnf_args,
                                },
                                app_ty,
                            )),
                            _ => Err(CompilerError::Unsupported(format!(
                                "Application head projection did not bind to a variable: {head:?}"
                            ))),
                        }
                    }
                }
                _ => Err(CompilerError::Unsupported(format!(
                    "Application head: {head:?}"
                ))),
            }
        }

        // Projection
        ExprKind::Proj(type_name, idx, structure) => {
            let struct_arg = expr_to_arg(ctx, structure)?;
            let struct_fvar = match struct_arg {
                Arg::FVar(id) => id,
                _ => {
                    return Err(CompilerError::InvalidExpr(
                        "Projection on non-variable".into(),
                    ))
                }
            };
            // Infer the result type of the projection expression.
            let proj_ty = infer_type_or_placeholder(ctx.env, expr);
            Ok((
                LetValue::Proj {
                    type_name: type_name.clone(),
                    idx: *idx,
                    structure: struct_fvar,
                },
                proj_ty,
            ))
        }

        // Types and proofs
        ExprKind::Sort(_) | ExprKind::SProp => Ok((LetValue::Erased, Expr::const_str("_"))),

        // Other forms
        _ => Err(CompilerError::Unsupported(format!(
            "Expression form: {expr:?}"
        ))),
    }
}

/// Collect application arguments (reverse order).
pub(super) fn collect_app_args(expr: &Expr) -> (&Expr, Vec<&Expr>) {
    let mut args = Vec::new();
    let mut curr = expr;
    while let ExprKind::App(f, a) = curr.kind() {
        args.push(a.as_ref());
        curr = f.as_ref();
    }
    args.reverse();
    (curr, args)
}

/// Convert a definition body to L5CNF Code.
///
/// Handles lambda abstraction by converting to function parameters.
pub fn expr_to_code(ctx: &mut LcnfContext<'_>, expr: &Expr) -> Result<Code, CompilerError> {
    // Normalize a valueless-recursor spine the casesOn-shaped recognizers below
    // cannot peel as-spelled (rung 1: eta-reduced bare-variable minors —
    // `<Ind>.recOn`'s `@Char.rec motive mk t`; rung 3: subsingleton transport —
    // `@Eq.rec .. m .. h`, which collapses to its single minor). `None` leaves
    // `expr` untouched (fail-closed).
    let rec_norm = if matches!(expr.kind(), ExprKind::App(_, _)) {
        normalize_rec_app(ctx.env, expr)
    } else {
        None
    };
    let expr = rec_norm.as_ref().unwrap_or(expr);
    match expr.kind() {
        // Let binding: let x : T := val in body
        ExprKind::Let(_, ty, val, body, _) => {
            let (value, _) = expr_to_let_value(ctx, val)?;
            let fvar = ctx.add_let(Name::anon(), ty.as_ref().clone(), value);

            // Push the let-bound variable for the body
            ctx.bvar_stack.push(fvar);
            let result = expr_to_code(ctx, body)?;
            ctx.bvar_stack.pop();

            Ok(result)
        }

        // Two-way Bool conditionals (`cond` / `Bool.casesOn`) lower to a real
        // `Cases` node over `Bool`, rather than an opaque constant application.
        ExprKind::App(_, _) if bool_cond_branches(expr).is_some() => lower_bool_cond(ctx, expr),

        // The dependent-match spelling — an OVER-applied `Bool.rec` whose motive
        // returns a function saturated by a trailing `rfl` (`Nat.decLe` /
        // `Nat.decLt`) — lowers to the same two-alt `Bool` `Cases`, with the
        // minors beta-reduced against the trailing spine. Disjoint by arity from
        // the 4-arg `bool_cond_branches` above; without it the spine would fall
        // through to a bare `Apply(Bool.rec)` that the stage-2 guard demotes.
        ExprKind::App(_, _) if bool_dependent_rec_parts(ctx.env, expr).is_some() => {
            lower_bool_dependent_rec(ctx, expr)
        }

        // `match n with | 0 => .. | _ => ..` over `Nat` elaborates to
        // `Nat.casesOn motive zero_branch succ_lambda n` (or the `Nat.rec`
        // spelling). Nat is a boxed integer at runtime, so a generic tag
        // `switch` is unsound for the successor case (every `k >= 1` has a
        // distinct tag). Lower it explicitly instead.
        ExprKind::App(_, _) if nat_cases_branches(expr).is_some() => lower_nat_cases(ctx, expr),

        // A PROOF elimination (`<P>.rec` / `<P>.recOn` / `<P>.casesOn` where
        // `P` is a Prop-sorted inductive with ≥ 2 constructors) in return
        // position is a proof VALUE: erase it before `generic_cases_on` can
        // claim it as a runtime tag dispatch over an ERASED scrutinee (R3).
        // See [`prop_multi_ctor_elim`].
        ExprKind::App(_, _) if prop_multi_ctor_elim(ctx.env, expr) => {
            let fvar = ctx.add_let(Name::anon(), Expr::const_str("_"), LetValue::Erased);
            Ok(ctx.wrap_lets(Code::ret(fvar)))
        }

        // `if h : c then t else e` / `if c then t else e` elaborate to
        // fully-applied `dite` / `ite`. Lower to a real `Cases` over the
        // `Decidable` instance (which `to_mono`'s `dec_to_mono` turns into a
        // `Bool` switch), instead of an opaque call to the compiled `l_dite`
        // with the branches reified as CLOSURES. The closure spelling
        // allocates two closure cells per evaluation, and the one the
        // runtime applies is STRANDED by `clean_apply_n`'s borrow-lend
        // protocol (it never releases the closure cell) — the `Char.ofNat`
        // carrier leaked both per call (R3). See [`dite_ite_parts`] /
        // [`lower_dite_ite`].
        ExprKind::App(_, _) if dite_ite_parts(expr).is_some() => lower_dite_ite(ctx, expr),

        // Structural recursion over `Nat` (`Nat.rec motive zero succ major`) is
        // NOT special-cased here: it flows through the fallthrough arm into
        // the R1 synthesized-recursive-function path ([`rec_apply_parts`] /
        // [`lower_rec_apply`]), which synthesizes a local `go` whose captures
        // are lambda-lifted into threaded parameters. The retired dedicated
        // arm (`lower_nat_rec`) materialized the induction hypothesis as
        // `self_name(pred)` — the ENCLOSING declaration applied to the
        // predecessor ONLY — which under-applied every multi-parameter
        // declaration (`List.replicate n x`: the IH became a PAP closure
        // awaiting `x`, not the recursive value). The R1 path self-calls the
        // synthesized `go` instead, so the extra parameters are threaded
        // correctly by construction.

        // Generic `<Ind>.casesOn` for any (non-Nat, non-Bool) single-motive,
        // non-indexed inductive. `match` over `Option`, `List`, user structures,
        // etc. all elaborate to `<Ind>.casesOn motive major minor_0 .. minor_n`.
        // We lower to a `Cases` with one `Alt::ctor` per constructor, binding
        // each non-erased field via a `clean_ctor_get` projection. Placed AFTER
        // the Bool/Nat arms so those keep their special (boxed-int / 2-alt)
        // paths. See [`generic_cases_on`] / [`lower_generic_cases`].
        ExprKind::App(_, _) if generic_cases_on(ctx.env, expr).is_some() => {
            lower_generic_cases(ctx, expr)
        }

        // For non-binder expressions, convert to return
        _ => {
            let arg = expr_to_arg(ctx, expr)?;
            match arg {
                Arg::FVar(fvar) => Ok(ctx.wrap_lets(Code::ret(fvar))),
                Arg::Erased => {
                    // Erased return - create a dummy
                    let fvar = ctx.add_let(Name::anon(), Expr::const_str("_"), LetValue::Erased);
                    Ok(ctx.wrap_lets(Code::ret(fvar)))
                }
                Arg::Type(_) => Err(CompilerError::InvalidExpr(
                    "Cannot return a type directly".into(),
                )),
                Arg::Index(_) => Err(CompilerError::InvalidExpr(
                    "Cannot return an index literal directly".into(),
                )),
            }
        }
    }
}

/// Recognize a two-way `Bool` conditional application and return its
/// `(scrutinee, true_branch, false_branch)` sub-expressions.
///
/// Handles the two canonical Lean 4 spellings of a Bool eliminator:
///
/// * `cond {α} (c : Bool) (t e : α)` — branch order is `then` then `else`.
/// * `Bool.casesOn {motive} (c : Bool) (false_case) (true_case)` — Lean lists
///   the `false` alternative before the `true` one (constructor-tag order).
/// * `Bool.rec {motive} (minor_false) (minor_true) (c : Bool)` — the kernel
///   recursor spelling the elaborator emits for `if b then x else y`; the
///   scrutinee is the *last* argument and the minor premises are in
///   constructor-tag order (false then true).
///
/// Only the exact, fully-applied arities are matched; anything else returns
/// `None` so the caller falls back to the generic constant-application path.
/// The leading implicit (type / motive) argument is ignored — it is a type and
/// is erased by `expr_to_arg` regardless.
fn bool_cond_branches(expr: &Expr) -> Option<(&Expr, &Expr, &Expr)> {
    let (head, args) = collect_app_args(expr);
    let ExprKind::Const(name, _) = head.kind() else {
        return None;
    };
    match name.to_string().as_str() {
        // cond α c t e  ->  (c, then = t, else = e)
        "cond" if args.len() == 4 => Some((args[1], args[2], args[3])),
        // Bool.casesOn motive c false_case true_case -> (c, then = true, else = false)
        "Bool.casesOn" if args.len() == 4 => Some((args[1], args[3], args[2])),
        // Bool.rec motive minor_false minor_true major -> (major, then = true, else = false)
        //
        // This is the spine the elaborator actually emits for `if b then x else y`
        // with `b : Bool`: `Bool.rec.{u} motive minor_false minor_true b`. The
        // recursor lists the `Bool.false` minor premise before the `Bool.true`
        // one (constructor-tag order), so arg1 is the else-branch and arg2 is
        // the then-branch. The leading motive (arg0) is type-level and erased.
        "Bool.rec" if args.len() == 4 => Some((args[3], args[2], args[1])),
        _ => None,
    }
}

/// Lower a recognized two-way `Bool` conditional into a `Cases` node.
///
/// The scrutinee is bound as an FVar (its own let-bindings wrap the resulting
/// `Cases`), and each branch is lowered independently to `Code` with its own
/// pending-let scope, mirroring [`expr_to_local_fun`]. The two alternatives are
/// emitted in constructor-tag order (`Bool.false` then `Bool.true`).
fn lower_bool_cond(ctx: &mut LcnfContext<'_>, expr: &Expr) -> Result<Code, CompilerError> {
    let (scrutinee, then_expr, else_expr) = match bool_cond_branches(expr) {
        Some(parts) => parts,
        None => {
            return Err(CompilerError::Unsupported(
                "expected Bool conditional".into(),
            ))
        }
    };
    // Clone out of the borrow on `expr` before mutating `ctx`.
    let (then_expr, else_expr) = (then_expr.clone(), else_expr.clone());
    let result_type = infer_type_or_placeholder(ctx.env, expr);
    lower_bool_switch(ctx, scrutinee, &then_expr, &else_expr, result_type)
}

/// Emit a two-alternative `Cases` over `Bool` (`Bool.false` then `Bool.true`,
/// constructor-tag order) for a recognized two-way conditional. The scrutinee
/// is bound as an FVar (its own let-bindings wrap the resulting `Cases`), and
/// each branch is lowered independently in an isolated pending-let scope.
/// Shared by [`lower_bool_cond`] (the `cond`/`Bool.casesOn`/4-arg-`Bool.rec`
/// spellings) and [`lower_bool_dependent_rec`] (the over-applied dependent
/// `Bool.rec`).
fn lower_bool_switch(
    ctx: &mut LcnfContext<'_>,
    scrutinee: &Expr,
    then_expr: &Expr,
    else_expr: &Expr,
    result_type: Expr,
) -> Result<Code, CompilerError> {
    // Bind the scrutinee; any lets it introduces must wrap the whole `Cases`.
    let scrut_fvar = match expr_to_arg(ctx, scrutinee)? {
        Arg::FVar(id) => id,
        other => {
            return Err(CompilerError::InvalidExpr(format!(
                "Bool conditional scrutinee did not lower to a variable: {other:?}"
            )))
        }
    };

    let false_body = lower_branch(ctx, else_expr)?;
    let true_body = lower_branch(ctx, then_expr)?;

    let cases = Code::Cases(Cases::new(
        Name::from_string("Bool"),
        result_type,
        scrut_fvar,
        vec![
            Alt::ctor(Name::from_string("Bool.false"), Vec::new(), false_body),
            Alt::ctor(Name::from_string("Bool.true"), Vec::new(), true_body),
        ],
    ));
    Ok(ctx.wrap_lets(cases))
}

/// Recognize the DEPENDENT-match spelling of a two-way `Bool` elimination —
/// an OVER-applied `Bool.rec`: `Bool.rec.{u} motive minor_false minor_true
/// major extra_0 .. extra_{k-1}` (`k >= 1`). The elaborator emits this for
/// `match h : b with | true => .. | false => ..` (`Nat.decLe` / `Nat.decLt`):
/// the motive returns a function (`fun b => (Nat.ble n m = b) → Decidable ..`)
/// and the trailing `extra`s (the `rfl` equation proof) saturate it.
///
/// [`bool_cond_branches`] matches only the exact 4-arg `Bool.rec`, so this
/// shape would otherwise fall through to a bare `Apply(Bool.rec)` that the
/// stage-2 recursor-call guard demotes. By `Bool.rec`'s computation rule
/// `Bool.rec .. false extra.. = minor_false extra..` (and `.. true .. =
/// minor_true extra..`), the branches are the minors BETA-REDUCED against the
/// `extra`s — sound for ANY over-applied `Bool.rec`, dependent motive or not.
/// The equation proof is erased downstream, so `Nat.decLe`/`Nat.decLt` reduce
/// to the `Decidable.isFalse` / `Decidable.isTrue` constructions. Returns owned
/// `(major, then, else)`; `None` (fail-closed) unless the major is a real
/// runtime `Bool` value.
fn bool_dependent_rec_parts(env: &Environment, expr: &Expr) -> Option<(Expr, Expr, Expr)> {
    let (head, args) = collect_app_args(expr);
    let ExprKind::Const(name, _) = head.kind() else {
        return None;
    };
    // Strictly over-applied `Bool.rec`; the exact 4-arg spelling is
    // [`bool_cond_branches`]'s (disjoint by arity).
    if name.to_string() != "Bool.rec" || args.len() <= 4 {
        return None;
    }
    // Bool has no parameters: motive=args[0], minor_false=args[1],
    // minor_true=args[2], major=args[3], extras=args[4..].
    let major = args[3];
    // The major must scrutinize a real runtime Bool (not an erased proof).
    if classify_expr_arg(env, major) != ExprArgClass::Normal {
        return None;
    }
    let extras: Vec<Expr> = args[4..].iter().map(|a| (*a).clone()).collect();
    let else_branch = beta_reduce_spine(args[1], &extras);
    let then_branch = beta_reduce_spine(args[2], &extras);
    Some((major.clone(), then_branch, else_branch))
}

/// Lower the over-applied dependent `Bool.rec` ([`bool_dependent_rec_parts`])
/// to a two-alt `Cases` over `Bool`.
fn lower_bool_dependent_rec(ctx: &mut LcnfContext<'_>, expr: &Expr) -> Result<Code, CompilerError> {
    let (scrutinee, then_expr, else_expr) = bool_dependent_rec_parts(ctx.env, expr)
        .ok_or_else(|| CompilerError::Unsupported("expected dependent Bool.rec".into()))?;
    let result_type = infer_type_or_placeholder(ctx.env, expr);
    lower_bool_switch(ctx, &scrutinee, &then_expr, &else_expr, result_type)
}

/// Beta-reduce `head` applied to `args`, reducing lambda heads via
/// `Expr::instantiate` (the same discipline as `to_mono`'s reducer): each
/// leading `Lam` binder is instantiated with the next argument; a non-lambda
/// head with arguments still to apply builds a stuck `App` (lowered by the
/// normal Const/FVar application paths).
fn beta_reduce_spine(head: &Expr, args: &[Expr]) -> Expr {
    let mut reduced = head.clone();
    for arg in args {
        if let ExprKind::Lam(_, _, body) = reduced.kind() {
            reduced = body.instantiate(arg);
        } else {
            reduced = Expr::app(reduced, arg.clone());
        }
    }
    reduced
}

/// Lower a single conditional branch to `Code` in an isolated pending scope,
/// so the branch's local lets do not leak into the sibling branch or the
/// surrounding `Cases`.
fn lower_branch(ctx: &mut LcnfContext<'_>, expr: &Expr) -> Result<Code, CompilerError> {
    let outer_pending = ctx.take_pending();
    match expr_to_code(ctx, expr) {
        Ok(code) => {
            ctx.restore_pending(outer_pending);
            Ok(code)
        }
        Err(err) => {
            // The failed branch may have left partial lets pending; discard
            // them (never `restore_pending`, which asserts an empty scope).
            ctx.abandon_pending(outer_pending);
            Err(err)
        }
    }
}

/// Recognize an application of a PROOF ELIMINATOR: `<P>.rec`, `<P>.recOn`,
/// or `<P>.casesOn` where `P` is a Prop-sorted inductive whose elimination
/// produces ONLY proofs (no runtime content). Two constructor shapes qualify:
///
/// * **≥ 2 constructors** (`Or`, `Nat.le`, `List.Perm`, …). A multi-ctor Prop
///   can never be a subsingleton, so the kernel only admits SMALL elimination
///   (into `Prop`);
/// * **exactly 1 constructor that does NOT large-eliminate** (`Int.NonNeg`:
///   its `Nat` field is data, so the kernel forbids large elimination and the
///   motive is `… → Prop`). Detected via `InductiveVal::is_large_elim`.
///
/// In both shapes every well-typed application of one of these heads is itself
/// a proof — its major premise is an ERASED proof (`box 0`) at runtime — so
/// compiling the elimination would read the constructor tag and fields of a
/// value that does not exist. Erasing the whole application is both sound (it
/// is a proof) and required (the R2-shipped `Char.ofNatAux` compiled its
/// `Or`-eliminating validity proof into a synthesized `go` that segfaults on
/// `box(0)` and stranded its materialized `2^32` bound chain per call; and
/// `Int.NonNeg.casesOn`/`.recOn`'s `Int.NonNeg.rec` reference otherwise
/// survives to the FINAL IR and trips the stage-2 valueless-recursor guard —
/// the 2 census stage-2 residue roots).
///
/// Single-constructor Prop inductives that DO large-eliminate (`Eq`, `Acc`,
/// `And`, `Iff`, `HEq` — subsingleton elimination carries runtime content:
/// `Eq.rec` casts, `Acc.rec` well-founded recursion) are deliberately EXCLUDED
/// and keep their current paths, fail-closed. A 0-constructor Prop (`False`)
/// keeps its dedicated ex-falso path.
fn prop_multi_ctor_elim(env: &Environment, expr: &Expr) -> bool {
    let (head, _args) = collect_app_args(expr);
    let ExprKind::Const(name, _) = head.kind() else {
        return false;
    };
    let full = name.to_string();
    let Some(parent) = full
        .strip_suffix(".casesOn")
        .or_else(|| full.strip_suffix(".recOn"))
        .or_else(|| full.strip_suffix(".rec"))
    else {
        return false;
    };
    let parent_name = Name::from_string(parent);
    let Some(ind) = env.get_inductive(&parent_name) else {
        return false;
    };
    // Erasable proof-elimination shape: ≥2 ctors (never a subsingleton, so
    // small-elim only), OR exactly 1 ctor that does not large-eliminate (a
    // non-subsingleton single-ctor Prop like `Int.NonNeg`). A single-ctor
    // large-eliminator (`Eq`/`Acc`/`And`/…) carries runtime content and is
    // excluded; a 0-ctor Prop (`False`) keeps its ex-falso path.
    let n_ctors = ind.constructor_names.len();
    let erasable_ctor_shape = n_ctors >= 2 || (n_ctors == 1 && !ind.is_large_elim);
    if !erasable_ctor_shape {
        return false;
    }
    // Prop-sorted: the inductive's declared type ends in `Sort 0`.
    let mut ty = &ind.type_;
    loop {
        match ty.kind() {
            ExprKind::Pi(_, _, body) => ty = body.as_ref(),
            ExprKind::MData(_, inner) => ty = inner.as_ref(),
            _ => break,
        }
    }
    matches!(ty.kind(), ExprKind::Sort(level) if level.is_zero())
}

/// Which two-branch `Decidable` conditional a recognized application is.
enum DiteKind {
    /// `ite {α} c [inst] (t e : α)` — branch arguments are plain values.
    Ite,
    /// `dite {α} c [inst] (t : c → α) (e : ¬c → α)` — branch arguments are
    /// lambdas binding an (erased) proof.
    Dite,
}

/// Recognize a fully-applied `ite` / `dite` application and return its
/// `(kind, decidable_instance, then_branch, else_branch)` parts.
///
/// Only the exact 5-argument spelling is matched, and `dite` only when both
/// branches are lambdas (so the proof binder can be peeled and bound
/// erased); anything else declines to the generic constant-application path,
/// fail-closed.
fn dite_ite_parts(expr: &Expr) -> Option<(DiteKind, &Expr, &Expr, &Expr)> {
    let (head, args) = collect_app_args(expr);
    let ExprKind::Const(name, _) = head.kind() else {
        return None;
    };
    match name.to_string().as_str() {
        // ite α c inst t e -> (inst, then = t, else = e)
        "ite" if args.len() == 5 => Some((DiteKind::Ite, args[2], args[3], args[4])),
        // dite α c inst t e -> (inst, then = t·h, else = e·h), h erased
        "dite"
            if args.len() == 5
                && matches!(args[3].kind(), ExprKind::Lam(_, _, _))
                && matches!(args[4].kind(), ExprKind::Lam(_, _, _)) =>
        {
            Some((DiteKind::Dite, args[2], args[3], args[4]))
        }
        _ => None,
    }
}

/// Lower a recognized `ite` / `dite` into a `Cases` over the `Decidable`
/// instance (constructor-tag order: `isFalse` then `isTrue`), which
/// `to_mono`'s `dec_to_mono` rewrites into a `Bool` switch. `dite` branch
/// lambdas have their proof binder peeled and bound ERASED — the binder is a
/// proof by `dite`'s own signature, so no field projection is ever read from
/// the scrutinee.
fn lower_dite_ite(ctx: &mut LcnfContext<'_>, expr: &Expr) -> Result<Code, CompilerError> {
    let (kind, inst, then_expr, else_expr) = match dite_ite_parts(expr) {
        Some(parts) => parts,
        None => {
            return Err(CompilerError::Unsupported(
                "expected ite/dite application".into(),
            ))
        }
    };
    // Clone out of the borrow on `expr` before mutating `ctx`.
    let (inst, then_expr, else_expr) = (inst.clone(), then_expr.clone(), else_expr.clone());

    // Bind the scrutinee; any lets it introduces must wrap the whole `Cases`.
    let scrut_fvar = match expr_to_arg(ctx, &inst)? {
        Arg::FVar(id) => id,
        other => {
            return Err(CompilerError::InvalidExpr(format!(
                "Decidable instance did not lower to a variable: {other:?}"
            )))
        }
    };
    let result_type = infer_type_or_placeholder(ctx.env, expr);

    let (false_body, true_body) = match kind {
        DiteKind::Ite => (
            lower_branch(ctx, &else_expr)?,
            lower_branch(ctx, &then_expr)?,
        ),
        DiteKind::Dite => (
            lower_proof_binder_branch(ctx, &else_expr)?,
            lower_proof_binder_branch(ctx, &then_expr)?,
        ),
    };

    let cases = Code::Cases(Cases::new(
        Name::from_string("Decidable"),
        result_type,
        scrut_fvar,
        vec![
            Alt::ctor(
                Name::from_string("Decidable.isFalse"),
                Vec::new(),
                false_body,
            ),
            Alt::ctor(Name::from_string("Decidable.isTrue"), Vec::new(), true_body),
        ],
    ));
    Ok(ctx.wrap_lets(cases))
}

/// Lower a `dite` branch lambda: peel exactly one binder — a PROOF by
/// `dite`'s signature (`t : c → α`, `e : ¬c → α`) — bind it erased, and
/// lower the body in an isolated pending scope. The unconditional erasure is
/// deliberate: `is_erased_constructor_field_type` cannot classify the OPEN
/// proof domain (whole-term inference fails on loose bvars), and a
/// fallback projection here would read a field out of what is a `Bool` after
/// `dec_to_mono`.
fn lower_proof_binder_branch(
    ctx: &mut LcnfContext<'_>,
    minor: &Expr,
) -> Result<Code, CompilerError> {
    let ExprKind::Lam(_, _, body) = minor.kind() else {
        return Err(CompilerError::Unsupported(
            "dite branch is not a lambda".into(),
        ));
    };
    let body = body.as_ref().clone();
    let outer_pending = ctx.take_pending();
    let dummy = ctx.add_let(Name::anon(), Expr::const_str("_"), LetValue::Erased);
    ctx.bvar_stack.push(dummy);
    let result = expr_to_code(ctx, &body);
    ctx.bvar_stack.pop();
    match result {
        Ok(code) => {
            ctx.restore_pending(outer_pending);
            Ok(code)
        }
        Err(err) => {
            ctx.abandon_pending(outer_pending);
            Err(err)
        }
    }
}

/// Recognize a `Nat` case analysis and return its
/// `(scrutinee, zero_branch, succ_lambda)` sub-expressions.
///
/// Handles the two Lean 4 spellings the elaborator emits for `match n with
/// | 0 => .. | _ => ..`:
///
/// * `Nat.casesOn {motive} (zero_branch) (succ_lambda) (n)` — the eliminator
///   form; `succ_lambda` is `fun (pred : Nat) => body`.
/// `Nat.rec` (the structural recursor) is handled separately by the R1
/// synthesized-recursive-function path ([`rec_apply_parts`] /
/// [`lower_rec_apply`]), because its `succ` minor premise is binary
/// (`fun pred ih => body`) and the induction hypothesis `ih` must be
/// materialized as a recursive self-call rather than discarded.
///
/// Only the exact, fully-applied arity is matched; the leading motive (arg0)
/// is type-level and dropped.
fn nat_cases_branches(expr: &Expr) -> Option<(&Expr, &Expr, &Expr)> {
    let (head, args) = collect_app_args(expr);
    let ExprKind::Const(name, _) = head.kind() else {
        return None;
    };
    match name.to_string().as_str() {
        // Nat.casesOn motive n zero_branch succ_lambda -> (n, zero, succ_lambda)
        //
        // `casesOn` places the major premise (scrutinee) immediately after the
        // motive, then the minor premises in constructor order (`Nat.zero`
        // before `Nat.succ`). The `succ` minor is `fun (pred : Nat) => body`.
        "Nat.casesOn" if args.len() == 4 => Some((args[1], args[2], args[3])),
        _ => None,
    }
}

/// Lower a recognized `Nat` case analysis into a `Cases` node over `Nat`.
///
/// Because `Nat` is a boxed integer at runtime (`clean_obj_tag(box k) == k`),
/// a generic two-alt tag `switch` would only match the successor constructor
/// for `k == 1`. We avoid that by emitting:
///
/// * `Nat.zero` as a constructor alternative (tag `0`, matched exactly when
///   `n == 0`), and
/// * the successor case as the `Default` alternative (catches every `k >= 1`).
///
/// In the successor branch the predecessor is materialized as
/// `let pred := Nat.sub n 1`, bound to the `succ` lambda's parameter, so the
/// branch body sees the correct value. Each branch is lowered in its own
/// isolated pending scope (mirroring [`lower_bool_cond`]).
fn lower_nat_cases(ctx: &mut LcnfContext<'_>, expr: &Expr) -> Result<Code, CompilerError> {
    let (scrutinee, zero_expr, succ_lambda) = match nat_cases_branches(expr) {
        Some(parts) => parts,
        None => return Err(CompilerError::Unsupported("expected Nat cases".into())),
    };
    // Clone out of the borrow on `expr` before mutating `ctx`.
    let (scrutinee, zero_expr, succ_lambda) =
        (scrutinee.clone(), zero_expr.clone(), succ_lambda.clone());

    // The successor minor premise must be `fun (pred : Nat) => body`.
    let ExprKind::Lam(_, _, succ_body) = succ_lambda.kind() else {
        return Err(CompilerError::Unsupported(
            "Nat cases successor branch is not a lambda".into(),
        ));
    };
    let succ_body = succ_body.as_ref().clone();

    // Bind the scrutinee; any lets it introduces must wrap the whole `Cases`.
    let scrut_fvar = match expr_to_arg(ctx, &scrutinee)? {
        Arg::FVar(id) => id,
        other => {
            return Err(CompilerError::InvalidExpr(format!(
                "Nat cases scrutinee did not lower to a variable: {other:?}"
            )))
        }
    };
    let result_type = infer_type_or_placeholder(ctx.env, expr);

    // Zero branch: ordinary isolated lowering.
    let zero_body = lower_branch(ctx, &zero_expr)?;

    // Successor branch: bind `pred := Nat.sub n 1` inside an isolated scope,
    // push it as the lambda's bound variable, then lower the body.
    let succ_body_code = lower_succ_branch(ctx, scrut_fvar, &succ_body)?;

    let cases = Code::Cases(Cases::new(
        Name::from_string("Nat"),
        result_type,
        scrut_fvar,
        vec![
            Alt::ctor(Name::from_string("Nat.zero"), Vec::new(), zero_body),
            Alt::default(succ_body_code),
        ],
    ));
    Ok(ctx.wrap_lets(cases))
}

/// Lower the successor branch of a `Nat` case analysis in an isolated pending
/// scope, binding the `succ` lambda's predecessor parameter to `n - 1`.
fn lower_succ_branch(
    ctx: &mut LcnfContext<'_>,
    scrut_fvar: clean_kernel::FVarId,
    succ_body: &Expr,
) -> Result<Code, CompilerError> {
    let outer_pending = ctx.take_pending();

    // pred := Nat.sub n 1
    let nat_ty = Expr::const_str("Nat");
    let one_fvar = ctx.add_let(Name::anon(), nat_ty.clone(), LetValue::nat(1));
    let pred_fvar = ctx.add_let(
        Name::anon(),
        nat_ty,
        LetValue::Const {
            name: Name::from_string("Nat.sub"),
            levels: Vec::new(),
            args: vec![Arg::FVar(scrut_fvar), Arg::FVar(one_fvar)],
        },
    );

    // The successor lambda's parameter (BVar 0 in `succ_body`) is the predecessor.
    ctx.bvar_stack.push(pred_fvar);
    let result = expr_to_code(ctx, succ_body);
    ctx.bvar_stack.pop();

    let body = match result {
        Ok(body) => body,
        Err(err) => {
            ctx.abandon_pending(outer_pending);
            return Err(err);
        }
    };
    ctx.restore_pending(outer_pending);
    Ok(body)
}

/// Recognize a generic `<Ind>.casesOn` — or a `<Ind>.rec` over a
/// NON-recursive inductive — application for a single-motive, non-indexed
/// inductive that is NOT handled by a dedicated special case (`Nat`, `Bool`).
///
/// Returns `(inductive_name, major_premise, minor_premises)` where the minor
/// premises are in constructor-tag order (one per constructor).
///
/// A `casesOn` spine is `<Ind>.casesOn.{u} (params..) (motive) (indices..)
/// (major) (minor_0) .. (minor_{n-1})`. The inductive's type parameters appear
/// FIRST (e.g. `Option.casesOn Nat motive major minor_none minor_some`). For
/// non-indexed types (`num_indices == 0`) the expected arity is
/// `num_params + 1 (motive) + 1 (major) + num_constructors`. We require an exact
/// arity match so partial applications fall through to the generic path.
///
/// A `<Ind>.rec` spine over a non-recursive inductive is `casesOn` modulo
/// argument order (the kernel recursor lists the major premise per its
/// `RecursorArgOrder`): with no recursive constructor fields there are no
/// induction hypotheses, so each minor premise binds exactly the constructor's
/// fields — the same shape `lower_generic_cases` already handles. This is the
/// spelling the elaborator emits for e.g. `Decidable.decide`, `Fin.val`,
/// `Int.add`, `Char.decEq` (C5a). Recursors of RECURSIVE inductives
/// (`List.rec`, `Nat.rec`) bind extra IH binders and are NOT matched here.
///
/// Out of scope (returns `None`): `Nat`/`Bool` (special-cased above), indexed
/// families (`num_indices > 0`), and mutual blocks (`all_names.len() > 1` /
/// `num_motives > 1`).
pub(super) fn generic_cases_on<'a>(
    env: &Environment,
    expr: &'a Expr,
) -> Option<(Name, &'a Expr, Vec<&'a Expr>)> {
    let (head, args) = collect_app_args(expr);
    let ExprKind::Const(name, _) = head.kind() else {
        return None;
    };
    match name.last_component().as_deref() {
        Some("casesOn") => {}
        Some("rec") => return generic_nonrecursive_rec(env, name, &args),
        _ => return None,
    }
    let ind_name = strip_last_component(name)?;

    // Nat and Bool keep their dedicated lowering (boxed-int / 2-alt paths).
    let ind_str = ind_name.to_string();
    if ind_str == "Nat" || ind_str == "Bool" {
        return None;
    }

    let ind = env.get_inductive(&ind_name)?;

    // Indexed families and mutual blocks are out of scope for this lowering.
    if ind.num_indices > 0 || ind.all_names.len() > 1 {
        return None;
    }

    let num_ctors = ind.constructor_names.len();
    let num_params = ind.num_params as usize;
    // params + motive + major + one minor per constructor (num_indices == 0).
    let expected_arity = num_params + 2 + num_ctors;
    if args.len() != expected_arity {
        return None;
    }

    // Layout: [params..] motive major [minor_0 .. minor_{n-1}].
    let major_idx = num_params + 1;
    let major = args[major_idx];
    let minors: Vec<&Expr> = args[major_idx + 1..].to_vec();
    Some((ind_name, major, minors))
}

/// Verify a kernel recursor's rules pair 1:1 with the inductive's ordinary
/// (point) DATA constructors — the alignment assumption both recursor
/// recognizers ([`rec_apply_parts`] and [`generic_nonrecursive_rec`]) build
/// on when they treat `minors[i]` as the elimination method of
/// `constructors[i]`.
///
/// Checks, each declining fail-closed:
///
/// * rule count == constructor count, and `rules[i].constructor_name ==
///   constructor_names[i]` (names AND order);
/// * `rules[i].num_fields` matches the registered constructor's `num_fields`
///   and its Pi-telescope actually carries that many field binders;
/// * the constructor's CODOMAIN (after params + fields) is a direct
///   application of the inductive itself. A Cubical HIT **path constructor**
///   lands in a `Path`/`PathP` instead (`∥A∥.squash`, `S¹.loop`,
///   `Susp.merid`), and its "rule" is boundary-coherence machinery, not a
///   structural elimination arm — `Cases` tag dispatch over it is
///   meaningless;
/// * a field whose type is a DIRECT `<Ind> ..` occurrence must be FLAGGED
///   recursive by the rule. The kernel's standard recursor builder derives
///   `recursive_fields` from exactly this head test, so a mismatch means the
///   recursor is bespoke and its minor telescope is NOT the constructor
///   method list. The prop-truncation HIT recursor is the concrete violator:
///   its minors are `[isProp-witness, f]` against rules `[in, squash]` — the
///   rule NAMES align with the constructors, but `squash`'s `recursive_fields
///   = [false, false]` belies its two `∥A∥`-typed fields, and pairing
///   `minors[0] = isProp` with `in` miscompiles the elimination (the
///   adversarial-review probe shape).
///
/// The FORWARD direction (flagged recursive but not `<Ind>`-headed — the
/// reflexive/function-typed fields of `Acc`/`MyW`) is deliberately NOT
/// checked here: each recognizer already declines those via `is_reflexive`
/// (R1) or the any-recursive-flag gate (C5a).
fn recursor_rules_pair_with_constructors(
    env: &Environment,
    ind_name: &Name,
    ind: &clean_kernel::inductive::InductiveVal,
    rules: &[clean_kernel::inductive::RecursorRule],
) -> bool {
    if ind.constructor_names.len() != rules.len() {
        return false;
    }
    for (ctor_name, rule) in ind.constructor_names.iter().zip(rules.iter()) {
        if rule.constructor_name != *ctor_name {
            return false;
        }
        let Some(ctor) = env.get_constructor(ctor_name) else {
            return false;
        };
        if ctor.num_fields != rule.num_fields {
            return false;
        }

        // Walk the constructor telescope: params, then fields, then the
        // codomain — which must be `<Ind> ..` (a POINT constructor).
        let binders = ctor.num_params as u64 + u64::from(ctor.num_fields);
        let mut field_tys: Vec<&Expr> = Vec::with_capacity(ctor.num_fields as usize);
        let mut cur = &ctor.type_;
        for i in 0..binders {
            let ExprKind::Pi(_, dom, body) = cur.kind() else {
                return false;
            };
            if i >= ctor.num_params as u64 {
                field_tys.push(dom.as_ref());
            }
            cur = body.as_ref();
        }
        match cur.get_app_fn().kind() {
            ExprKind::Const(head, _) if head == ind_name => {}
            _ => return false,
        }

        // Converse recursion-flag consistency: a direct `<Ind> ..` field the
        // rule does NOT flag recursive is a metadata lie (bespoke recursor).
        for (j, field_ty) in field_tys.iter().enumerate() {
            let ind_headed = matches!(
                field_ty.get_app_fn().kind(),
                ExprKind::Const(head, _) if head == ind_name
            );
            let flagged = rule.recursive_fields.get(j).copied().unwrap_or(false);
            if ind_headed && !flagged {
                return false;
            }
        }
    }
    true
}

/// Normalize a valueless-kernel-recursor application the `casesOn`-shaped
/// recognizers cannot lower as-spelled into an equivalent form they can, or
/// (rung 3) directly into its runtime value. `None` (fail-closed) leaves the
/// spine untouched, so the stage-2 recursor-call guard still refuses a
/// genuinely un-lowerable recursor. Tries, in order:
///
/// * [`subsingleton_transport_to_minor`] — `@Eq.rec .. m .. h == m` and the
///   other single-`0`-field-constructor (subsingleton) transports;
/// * [`eta_expand_rec_minors`] — eta-expand a non-recursive recursor's
///   eta-reduced (bare-variable) minors into the `casesOn` telescope shape.
fn normalize_rec_app(env: &Environment, expr: &Expr) -> Option<Expr> {
    subsingleton_transport_to_minor(env, expr).or_else(|| eta_expand_rec_minors(env, expr))
}

/// Rung 3 (subsingleton transport): a saturated application of a VALUELESS
/// kernel recursor whose inductive has a SINGLE constructor with NO field
/// reduces at runtime to its single minor premise. The major premise and the
/// family indices are erased (a proof and its index data), and the sole
/// constructor has no payload to project, so the recursor is the
/// identity-on-minor transport: `@Eq.rec α a motive m b h == m`,
/// `@HEq.rec .. m .. == m` (likewise `True.rec` / `PUnit.rec`).
///
/// Genuinely DATA-BEARING, not an erasure: these are the large-eliminating
/// subsingletons — the motive is `Sort u`, not restricted to `Prop` — so the
/// transport carries real runtime data when `u > 0`, and this is a real win.
/// The pure-`Prop`, non-subsingleton eliminations (`Or.rec`, `And.rec`, and
/// the multi-constructor Props) are erased earlier by [`prop_multi_ctor_elim`];
/// they never reach here.
///
/// Both structural recognizers decline these fail-closed (`Eq` / `HEq` carry
/// indices; the single-`0`-field constructor is the explicit PUnit-like
/// decline), leaving the valueless-recursor refusal — so this arm is the only
/// path that wins them.
///
/// Returns `apps(minor, extras)` (an over-applied `motive b` function stays
/// applied to the trailing spine), or `None` (fail-closed) otherwise.
fn subsingleton_transport_to_minor(env: &Environment, expr: &Expr) -> Option<Expr> {
    let (head, args) = collect_app_args(expr);
    let ExprKind::Const(rec_name, _) = head.kind() else {
        return None;
    };
    if rec_name.last_component().as_deref() != Some("rec") {
        return None;
    }
    let rec = env.get_recursor(rec_name)?;
    // Only VALUELESS kernel recursors (a `*.rec` DEFINITION keeps its path).
    if env
        .get_const(rec_name)
        .is_some_and(|info| info.value.is_some())
    {
        return None;
    }
    // Single motive, single constructor / minor.
    if rec.num_motives != 1 || rec.num_minors != 1 || rec.rules.len() != 1 {
        return None;
    }
    // The sole constructor must carry NO field: only then is the minor the
    // whole runtime value (`I.rec .. minor .. major == minor`, no field
    // projection and no erased-argument application). This is exactly the
    // `Eq.refl` / `HEq.refl` / `True.intro` / `PUnit.unit` shape.
    if rec.rules[0].num_fields != 0 {
        return None;
    }
    // Only the kernel `X.rec` argument order (`params → motive → minor →
    // indices → major`): the single minor then sits right after the parameters
    // and the motive. `MajorAfterMotive` (casesOn-style) places the major
    // differently and is out of scope (declined fail-closed).
    if !matches!(
        rec.arg_order,
        clean_kernel::RecursorArgOrder::MajorAfterMinors
    ) {
        return None;
    }
    let ind = env.get_inductive(&rec.inductive_name)?;
    if ind.all_names.len() > 1 {
        return None;
    }

    let num_params = rec.num_params as usize;
    let minor_idx = num_params + 1; // params + the single motive
                                    // Saturation: params + motive + minor + indices + major.
    let arity = num_params + 1 + 1 + rec.num_indices as usize + 1;
    if args.len() < arity {
        return None;
    }
    let minor = args[minor_idx].clone();
    let extras: Vec<Expr> = args[arity..].iter().map(|a| (*a).clone()).collect();
    Some(Expr::apps(minor, extras))
}

/// Rung 1 (eta-expanded `recOn`): normalize a saturated VALUELESS-kernel-
/// recursor application over a NON-recursive inductive whose minor premises are
/// ETA-REDUCED (spelled as a bare eliminator variable, `@Char.rec motive mk t`)
/// into the `casesOn`-shaped form `@Char.rec motive (fun val isv => mk val isv)
/// t`, so [`generic_nonrecursive_rec`] can peel it.
///
/// `<Ind>.recOn` (and every scalar-carrier `<UIntN>.recOn` / `Float.recOn` /
/// `String.recOn`) stores its minor as the bare `recOn` parameter rather than a
/// lambda telescope; [`generic_nonrecursive_rec`] then declines it (a
/// bare-variable body has no field binders for `lower_ctor_branch` to project
/// into, so its De Bruijn indices would misalign). Eta-expanding the minor to
/// `fun f0..fk => mk f0..fk`, with the binder types read from the constructor's
/// own field telescope, reproduces the corresponding `casesOn` minor EXACTLY
/// (byte-identical to `Char.casesOn`'s minor — verified), so `recOn` then lowers
/// through the identical, census-proven `casesOn` `Cases` path.
///
/// Returns the rebuilt spine, or `None` when nothing needed expanding or the
/// shape is not a saturated non-recursive-recursor application (fail-closed: the
/// caller keeps the original expr, and the stage-2 recursor-call guard still
/// refuses a genuinely un-lowerable recursor).
///
/// Deliberately scoped to NON-recursive inductives: the eta-reduced minors of
/// RECURSIVE recursors are [`rec_apply_parts`]'s `RecMinorStrategy::Apply`
/// domain, which this normalization must not pre-empt.
fn eta_expand_rec_minors(env: &Environment, expr: &Expr) -> Option<Expr> {
    let (head, args) = collect_app_args(expr);
    let ExprKind::Const(rec_name, levels) = head.kind() else {
        return None;
    };
    if rec_name.last_component().as_deref() != Some("rec") {
        return None;
    }
    let rec = env.get_recursor(rec_name)?;
    // Only VALUELESS kernel recursors: a `*.rec` DEFINITION (with a stored
    // value) keeps its compiled-from-source path.
    if env
        .get_const(rec_name)
        .is_some_and(|info| info.value.is_some())
    {
        return None;
    }
    if rec.num_motives != 1 {
        return None;
    }
    let ind_name = rec.inductive_name.clone();
    let ind = env.get_inductive(&ind_name)?;
    // Non-recursive, single (non-mutual) inductive only — see the doc comment.
    if ind.is_recursive || ind.all_names.len() > 1 {
        return None;
    }
    if rec
        .rules
        .iter()
        .any(|rule| rule.recursive_fields.iter().any(|recursive| *recursive))
    {
        return None;
    }

    let num_params = rec.num_params as usize;
    let num_minors = rec.num_minors as usize;
    if rec.rules.len() != num_minors {
        return None;
    }
    // The minors sit directly after the parameters and the single motive; both
    // recursor argument orders agree on this prefix (they differ only in where
    // the major/indices land, all AFTER the minors here).
    let minors_start = num_params + 1;
    if args.len() < minors_start + num_minors {
        return None;
    }

    let mut new_args: Vec<Expr> = args.iter().map(|a| (*a).clone()).collect();
    let mut changed = false;
    for (i, rule) in rec.rules.iter().enumerate() {
        let num_fields = rule.num_fields as usize;
        if num_fields == 0 {
            continue;
        }
        // The eta-expanded arm applies the (compile-time-unknown) minor closure
        // to all `num_fields` projected fields; a dynamic closure apply wider
        // than the runtime's fast-path surface is un-lowerable (a saturating
        // apply above arity 32 would reach `clean_invoke`'s ceiling and
        // `clean_panic`; `emit_trust_ir`/`emit_c` refuse it). Decline so a
        // beyond-ceiling record eliminator keeps its fail-closed
        // valueless-recursor refusal — parity with [`rec_apply_parts`]'s
        // `RecMinorStrategy::Apply` guard.
        if num_fields > MAX_RUNTIME_APPLY_ARGS {
            return None;
        }
        let minor = &new_args[minors_start + i];
        // Count the minor's leading lambda binders (capped at num_fields).
        let mut depth = 0usize;
        let mut curr = minor;
        while depth < num_fields {
            match curr.kind() {
                ExprKind::Lam(_, _, body) => {
                    depth += 1;
                    curr = body.as_ref();
                }
                _ => break,
            }
        }
        if depth >= num_fields {
            continue; // already a full field telescope (the `casesOn` spelling)
        }
        let ctor = env.get_constructor(&rule.constructor_name)?;
        let field_tys = constructor_field_types(&ctor.type_, ctor.num_params);
        if field_tys.len() != num_fields {
            return None;
        }
        new_args[minors_start + i] = eta_expand_minor(minor, &field_tys);
        changed = true;
    }
    if !changed {
        return None;
    }
    let head = Expr::const_(rec_name.clone(), levels.clone());
    Some(Expr::apps(head, new_args))
}

/// Eta-expand an under-applied eliminator method `minor` to a full field
/// telescope `fun (f0:T0)..(f_{k-1}:T_{k-1}) => (minor↑k) f0 .. f_{k-1}`, where
/// `field_tys = [T0..T_{k-1}]` are the constructor's field types in its own
/// telescope De Bruijn context (`f0` is the OUTERMOST binder). Reproduces the
/// elaborator's `casesOn` minor.
fn eta_expand_minor(minor: &Expr, field_tys: &[Expr]) -> Expr {
    let k = field_tys.len() as u32;
    // Lift the minor past the k fresh binders, then apply it to f0..f_{k-1}
    // (f0 => BVar(k-1) at the innermost point, f_{k-1} => BVar(0)).
    let mut body = minor.lift(k);
    for j in (0..k).rev() {
        body = Expr::app(body, Expr::bvar(j));
    }
    for ty in field_tys.iter().rev() {
        body = Expr::lam(clean_kernel::expr::BinderInfo::Default, ty.clone(), body);
    }
    body
}

/// Eta-expand a partially-applied CONSTRUCTOR used as a first-class value
/// (`instInsertList`'s `⟨List.cons⟩` field is the bare `List.cons α` — a
/// constructor applied to its type parameter only, 0 of its 2 value fields).
///
/// A `Ctor` IR node demands the exact `num_params + num_fields` spine
/// ([`to_ir`]'s `ctor_field_args` refuses anything shorter fail-closed — there
/// is no faithful field placement for an under-saturated ctor). Rather than
/// demote the whole declaration to an extern boundary, saturate the ctor under
/// fresh field binders — `fun (f_m..f_{n-1}) => Ctor a_0..a_{m-1} f_m..f_{n-1}`
/// — so the body is a SATURATED ctor construction (lowered authoritatively from
/// `CtorMeta`) and the surrounding lambda lambda-lifts to a closure via the
/// existing saturated-call + apply discipline. This is exactly the eta-expansion
/// [`eta_expand_rec_minors`] applies to under-applied recursor minors, reusing
/// [`eta_expand_minor`]'s field-telescope De Bruijn construction — whose binder
/// types line up with the insertion context precisely because every leading
/// parameter is already present.
///
/// Fail-closed (returns `None`, keeping the baseline `CtorSpineMisaligned`
/// refusal) unless the head is a known constructor, the spine is strictly
/// UNDER-applied (`m < num_params + num_fields`), and EVERY inductive parameter
/// is present (`m >= num_params`) — a missing type parameter would misalign the
/// field-type telescope's De Bruijn context with the insertion context, so we
/// decline rather than risk an imprecise binder type.
fn eta_expand_partial_ctor(env: &Environment, expr: &Expr) -> Option<Expr> {
    let (head, args) = collect_app_args(expr);
    let ExprKind::Const(name, _levels) = head.kind() else {
        return None;
    };
    let ctor = env.get_constructor(name)?;
    // A SCALAR-CARRIER constructor (the C5b `UIntN`/`Char` newtype family, e.g.
    // `UInt8.ofBitVec`) must NOT be eta-expanded. Its runtime representation IS
    // its unboxed integer carrier, so `to_ir`'s C5b construction
    // (`lower_scalar_carrier_ctor`) aliases the ctor result to that carrier —
    // but only when the carrier is affirmatively at the target scalar width.
    // Saturating the ctor under a FRESH field binder makes the carrier an
    // Object-typed lambda parameter with no boxed-scalar evidence, which C5b
    // then refuses fail-closed (`ScalarCarrierObjectCarrier`) — regressing
    // `UIntN.decEq`, which lowered on base where these partials were never
    // eta-expanded. Decline here (reusing the SAME scalar-carrier recognition
    // C5b uses) to preserve that baseline. A normal heap ctor (`List.cons` /
    // `instInsertList`) is not a scalar carrier and still eta-expands.
    if crate::to_ir::pseudo_ops::scalar_carrier_target(name).is_some() {
        return None;
    }
    let num_params = ctor.num_params as usize;
    let num_fields = ctor.num_fields as usize;
    let total = num_params + num_fields;
    let m = args.len();
    // Saturated / over-applied ctors keep the direct `Ctor` path (an
    // over-applied ctor result is a `ClosureApply` handled downstream); only
    // strict under-application needs the closure. A spine missing a type
    // PARAMETER cannot be faithfully reconstructed here — decline fail-closed.
    if m >= total || m < num_params {
        return None;
    }
    let field_tys = constructor_field_types(&ctor.type_, ctor.num_params);
    if field_tys.len() != num_fields {
        return None;
    }
    // The missing binders are the not-yet-applied fields (`[m - num_params..]`),
    // in telescope order (outermost first) — exactly [`eta_expand_minor`]'s
    // expected `field_tys` shape.
    let missing_tys = &field_tys[m - num_params..];
    let partial = Expr::apps(head.clone(), args.into_iter().cloned().collect::<Vec<_>>());
    Some(eta_expand_minor(&partial, missing_tys))
}

/// The `<Ind>.rec` half of [`generic_cases_on`]: recognize a saturated kernel
/// recursor application over a single-motive, non-indexed, NON-recursive
/// inductive and return it in `(inductive, major, minors)` casesOn shape.
///
/// With no recursive constructor fields the recursor rules carry no induction
/// hypotheses, so each minor premise is exactly a casesOn minor (`fun field_0
/// .. field_k => body`). Anything else — recursive fields, indices, mutual
/// motives, non-exact arity — returns `None` and falls through to the generic
/// constant-application path (where the stage-2 recursor-call guard then
/// refuses it fail-closed rather than emitting a call to a bodyless recursor).
fn generic_nonrecursive_rec<'a>(
    env: &Environment,
    rec_name: &Name,
    args: &[&'a Expr],
) -> Option<(Name, &'a Expr, Vec<&'a Expr>)> {
    let rec = env.get_recursor(rec_name)?;
    let ind_name = rec.inductive_name.clone();

    // Nat and Bool keep their dedicated lowering (boxed-int / 2-alt paths).
    let ind_str = ind_name.to_string();
    if ind_str == "Nat" || ind_str == "Bool" {
        return None;
    }

    // Single motive (non-mutual), no indices, and NO recursive constructor
    // fields: only then is `rec` casesOn modulo argument order.
    if rec.num_motives != 1 || rec.num_indices != 0 {
        return None;
    }
    if rec
        .rules
        .iter()
        .any(|rule| rule.recursive_fields.iter().any(|recursive| *recursive))
    {
        return None;
    }

    // A single 0-field constructor (`PUnit`-likes) needs no tag dispatch and
    // its runtime value may be fully erased; keep the (baseline) generic
    // constant-application path instead of forcing a degenerate `Cases`.
    if rec.rules.len() == 1 && rec.rules[0].num_fields == 0 {
        return None;
    }

    // The rules must pair 1:1 with the inductive's point constructors (names,
    // order, field counts, `<Ind>`-codomains, recursion-flag consistency):
    // `lower_generic_cases` zips the minors positionally against
    // `constructor_names`, so a bespoke recursor whose minor telescope is NOT
    // the constructor method list (the Cubical HIT prop-truncation recursor —
    // minors `[isProp, f]`, rules `[in, squash]`, `squash`'s recursive fields
    // unflagged) would miscompile every arm. Its rule count must also equal
    // `num_minors` — the zip below would silently truncate otherwise.
    let ind = env.get_inductive(&ind_name)?;
    if rec.rules.len() != rec.num_minors as usize
        || !recursor_rules_pair_with_constructors(env, &ind_name, ind, &rec.rules)
    {
        return None;
    }

    let num_params = rec.num_params as usize;
    let num_minors = rec.num_minors as usize;
    // params + motive + minors + major (num_indices == 0); exact arity only,
    // so partial applications fall through.
    let expected_arity = num_params + 1 + num_minors + 1;
    if args.len() != expected_arity {
        return None;
    }

    let (major_idx, minors_start) = match rec.arg_order {
        // params → motive → minors → major
        clean_kernel::RecursorArgOrder::MajorAfterMinors => (expected_arity - 1, num_params + 1),
        // params → motive → major → minors (num_indices == 0)
        clean_kernel::RecursorArgOrder::MajorAfterMotive => (num_params + 1, num_params + 2),
    };
    let major = args[major_idx];
    let minors: Vec<&Expr> = args[minors_start..minors_start + num_minors].to_vec();

    // Scalar-carrier single-constructor eliminators (`Char.casesOn`: `Char` IS
    // its `UInt32`, the sole ctor `Char.mk` carries that scalar plus an erased
    // `isValidChar` proof) lower via the C5b identity-projection path — the
    // scrutinee stays an unboxed `UInt32` and the minor is applied to it, with
    // the erased proof materialized as an erased-typed unit dummy whose box is
    // a harmless tagged unit (RC on it is a scalar no-op). The retain-on-scalar
    // hazard the erased-binder decline below guards does NOT arise for this
    // shape — verified end-to-end (identity u32 projection, ASan-clean,
    // net-block-flat) — so scalar carriers are exempt from that decline.
    let relax_erased_scalar_carrier = ind.constructor_names.len() == 1
        && NON_HEAP_RUNTIME_REPR.contains(&ind_name.to_string().as_str());

    // Every minor premise must SYNTACTICALLY bind all of its constructor's
    // fields as lambdas: `lower_ctor_branch` peels exactly `num_fields`
    // binders and pushes a projection fvar for each, so a minor that is a
    // bare variable (the eta-reduced spelling inside `<Ind>.casesOn`-style
    // DEFINITIONS, whose minor is the enclosing function's own parameter)
    // would have its De Bruijn indices misaligned by the pushed projections.
    //
    // Additionally, no minor body may REFERENCE an erased field binder:
    // `lower_ctor_branch` binds erased fields (proofs/types) to an erased
    // dummy let, and a body that CONSUMES that dummy (e.g. the eta-expanded
    // `fun val isLt => h val isLt` inside `Fin.casesOn`) produces an
    // RC-managed erased value downstream — the trust-ir validator refuses
    // the resulting retain-on-scalar fail-closed. Unused erased binders
    // (`Decidable.decide`'s `fun h => false`) are fine.
    //
    // Either way the spelling falls through to the constant-application path
    // (the baseline extern treatment of the recursor callee).
    for (rule, minor) in rec.rules.iter().zip(minors.iter()) {
        let num_fields = rule.num_fields as usize;
        let mut erased_fields: Vec<bool> = Vec::with_capacity(num_fields);
        let mut curr = *minor;
        for _ in 0..num_fields {
            let ExprKind::Lam(_, ty, body) = curr.kind() else {
                return None;
            };
            // Mirror `lower_ctor_branch`'s erasure source: the lambda domain
            // (always present here — the loop above just peeled it).
            erased_fields.push(is_erased_constructor_field_type(env, ty.as_ref()));
            curr = body.as_ref();
        }
        for (field_idx, erased) in erased_fields.iter().enumerate() {
            // De Bruijn index of field `field_idx` inside the peeled body.
            let bvar_idx = (num_fields - 1 - field_idx) as u32;
            if *erased && !relax_erased_scalar_carrier && mentions_loose_bvar(curr, bvar_idx) {
                return None;
            }
        }
    }

    Some((ind_name, major, minors))
}

/// Whether `expr` mentions the loose bound variable `target` (de Bruijn,
/// adjusted under binders). CONSERVATIVE for expression forms this walker
/// does not model (cubical kinds, …): any loose variable reaching `target`'s
/// index range counts as a mention, so callers that fall back on `true` stay
/// fail-closed.
fn mentions_loose_bvar(expr: &Expr, target: u32) -> bool {
    // Fast prune: no loose bvar of index >= target at all.
    if expr.loose_bvar_range() <= target {
        return false;
    }
    match expr.kind() {
        ExprKind::BVar(idx) => *idx == target,
        ExprKind::App(f, a) => mentions_loose_bvar(f, target) || mentions_loose_bvar(a, target),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            mentions_loose_bvar(ty, target) || mentions_loose_bvar(body, target + 1)
        }
        ExprKind::Let(_, ty, value, body, _) => {
            mentions_loose_bvar(ty, target)
                || mentions_loose_bvar(value, target)
                || mentions_loose_bvar(body, target + 1)
        }
        ExprKind::Proj(_, _, structure) => mentions_loose_bvar(structure, target),
        ExprKind::MData(_, inner) | ExprKind::Squash(inner) => mentions_loose_bvar(inner, target),
        ExprKind::FVar(_)
        | ExprKind::Sort(_)
        | ExprKind::Const(_, _)
        | ExprKind::Lit(_)
        | ExprKind::SProp => false,
        // Unmodeled forms: conservative TRUE (there IS some loose bvar >=
        // target here, per the prune above).
        _ => true,
    }
}

/// Drop the last dotted component of a `Name` (`Option.casesOn` -> `Option`,
/// `List.casesOn` -> `List`). Returns `None` if the name has no parent
/// component (a single atom such as `casesOn`).
fn strip_last_component(name: &Name) -> Option<Name> {
    let s = name.to_string();
    let (prefix, _last) = s.rsplit_once('.')?;
    Some(Name::from_string(prefix))
}

/// Lower a recognized generic `<Ind>.casesOn` into a `Code::Cases` with one
/// `Alt::ctor` per constructor.
///
/// The major premise (scrutinee) is bound as an FVar (its own lets wrap the
/// whole `Cases`). For each constructor, the matching minor premise is a
/// lambda `fun (field_0) .. (field_k) => body` binding that constructor's
/// fields. We peel those binders and, for each NON-erased field, materialize a
/// projection `let field := Proj { type_name = ctor, idx, structure = scrut }`
/// (keyed by the *constructor* name so `to_ir` can recover that constructor's
/// field layout) and push the projection fvar onto the bvar stack so the body
/// sees the real payload. Erased fields (proofs/types) are bound to an erased
/// dummy to keep De Bruijn indices aligned without emitting a projection.
fn lower_generic_cases(ctx: &mut LcnfContext<'_>, expr: &Expr) -> Result<Code, CompilerError> {
    let (ind_name, major, minors) = match generic_cases_on(ctx.env, expr) {
        Some(parts) => parts,
        None => {
            return Err(CompilerError::Unsupported(
                "expected generic casesOn".into(),
            ))
        }
    };
    // Clone out of the borrow on `expr` before mutating `ctx`.
    let major = major.clone();
    let minors: Vec<Expr> = minors.into_iter().cloned().collect();

    // Resolve constructor names (tag order) before borrowing `ctx` mutably.
    let ind = ctx
        .env
        .get_inductive(&ind_name)
        .ok_or_else(|| CompilerError::Unsupported(format!("inductive {ind_name} not found")))?;
    let ctor_names: Vec<Name> = ind.constructor_names.clone();
    if ctor_names.len() != minors.len() {
        return Err(CompilerError::Unsupported(format!(
            "casesOn for {ind_name}: {} constructors but {} minor premises",
            ctor_names.len(),
            minors.len()
        )));
    }

    // Bind the scrutinee; its lets must wrap the whole `Cases`.
    let scrut_fvar = match expr_to_arg(ctx, &major)? {
        Arg::FVar(id) => id,
        other => {
            return Err(CompilerError::InvalidExpr(format!(
                "casesOn scrutinee did not lower to a variable: {other:?}"
            )))
        }
    };
    let result_type = infer_type_or_placeholder(ctx.env, expr);

    let mut alts = Vec::with_capacity(ctor_names.len());
    for (ctor_name, minor) in ctor_names.iter().zip(minors.iter()) {
        let body = lower_ctor_branch(ctx, scrut_fvar, ctor_name, minor)?;
        alts.push(Alt::ctor(ctor_name.clone(), Vec::new(), body));
    }

    let cases = Code::Cases(Cases::new(ind_name, result_type, scrut_fvar, alts));
    Ok(ctx.wrap_lets(cases))
}

/// Lower one constructor branch of a generic `casesOn` in an isolated pending
/// scope. Peels the minor premise's field binders, materializes a projection
/// for each non-erased field (bound to the scrutinee), pushes the binders onto
/// the bvar stack in field order, and lowers the peeled body.
fn lower_ctor_branch(
    ctx: &mut LcnfContext<'_>,
    scrut_fvar: clean_kernel::FVarId,
    ctor_name: &Name,
    minor: &Expr,
) -> Result<Code, CompilerError> {
    // Field types (in declaration order) for this constructor, derived from its
    // Pi-chain after skipping the parameters.
    let ctor = ctx
        .env
        .get_constructor(ctor_name)
        .ok_or_else(|| CompilerError::Unsupported(format!("constructor {ctor_name} not found")))?;
    let num_fields = ctor.num_fields as usize;
    let field_types = constructor_field_types(&ctor.type_, ctor.num_params);

    let outer_pending = ctx.take_pending();

    // Peel `num_fields` lambda binders off the minor premise, collecting each
    // field type from the lambda's domain (falls back to the ctor Pi-chain
    // type when the lambda domain is unavailable).
    let mut curr = minor.clone();
    let mut projections: Vec<(usize, FieldBindKind)> = Vec::with_capacity(num_fields);
    for field_idx in 0..num_fields {
        let lam_ty = match curr.kind() {
            ExprKind::Lam(_, ty, body) => {
                let ty = ty.as_ref().clone();
                curr = body.as_ref().clone();
                Some(ty)
            }
            _ => None,
        };
        let field_ty = lam_ty
            .or_else(|| field_types.get(field_idx).cloned())
            .unwrap_or_else(|| Expr::const_str("_"));

        let erased = is_erased_constructor_field_type(ctx.env, &field_ty);
        projections.push((
            field_idx,
            FieldBindKind {
                ty: field_ty,
                erased,
            },
        ));
    }

    // Materialize bindings outer-to-inner so `lookup_bvar` resolves correctly.
    for (field_idx, bind) in &projections {
        if bind.erased {
            // Keep De Bruijn alignment without emitting a projection.
            let dummy = ctx.add_let(Name::anon(), Expr::const_str("_"), LetValue::Erased);
            ctx.bvar_stack.push(dummy);
        } else {
            let field_fvar = ctx.add_let(
                Name::anon(),
                bind.ty.clone(),
                LetValue::Proj {
                    type_name: ctor_name.clone(),
                    idx: *field_idx as u32,
                    structure: scrut_fvar,
                },
            );
            ctx.bvar_stack.push(field_fvar);
        }
    }

    let result = expr_to_code(ctx, &curr);

    for _ in &projections {
        ctx.bvar_stack.pop();
    }

    let body = match result {
        Ok(body) => body,
        Err(err) => {
            ctx.abandon_pending(outer_pending);
            return Err(err);
        }
    };
    ctx.restore_pending(outer_pending);
    Ok(body)
}

/// Description of how a constructor field binder is materialized in a branch.
struct FieldBindKind {
    ty: Expr,
    erased: bool,
}

/// Extract the field types of a constructor from its type expression, skipping
/// the leading `num_params` parameter binders. Mirrors
/// `to_ir::ctor_env::extract_field_ir_types` but stays at the kernel-`Expr`
/// level (LCNF does not depend on IR types).
fn constructor_field_types(ctor_type: &Expr, num_params: u32) -> Vec<Expr> {
    let mut types = Vec::new();
    let mut current = ctor_type.clone();
    let mut idx = 0u32;
    while let ExprKind::Pi(_, domain, codomain) = current.kind() {
        if idx >= num_params {
            types.push(domain.as_ref().clone());
        }
        idx += 1;
        current = codomain.as_ref().clone();
    }
    types
}

/// Inductives whose RUNTIME representation is not a plain tagged heap
/// constructor object: unboxed scalar carriers (`Char` IS its `UInt32`, the
/// `UIntN` family, floats — the C5b scalar-carrier discipline) and primitive
/// containers with bespoke runtime layouts. `Cases` tag dispatch and
/// per-field `Proj` reads over these are either rewritten by `to_mono` in
/// ways the R1 lowering does not model, or outright unfaithful — so
/// [`rec_apply_parts`] declines them fail-closed and the application keeps
/// the baseline extern path.
///
/// Deliberately NOT listed (their `Cases`+`Proj` arm shapes are exactly what
/// `lower_generic_cases` already emits, census-proven through `to_mono`'s
/// dedicated handlers): `Int`, `Decidable`, `Array`, `BitVec`, and trivial
/// structures generally. `Nat` (boxed integer) is special-shaped inside the
/// R1 lowering; `Bool` is excluded by name (dedicated 2-alt path).
const NON_HEAP_RUNTIME_REPR: &[&str] = &[
    "Char",
    "UInt8",
    "UInt16",
    "UInt32",
    "UInt64",
    "USize",
    "Float",
    "Float32",
    "String",
    "ByteArray",
    "FloatArray",
    "Thunk",
    "Task",
];

/// The widest dynamic closure application the runtime/emitters model
/// (`clean_apply_0` .. `clean_apply_32` fast paths, backed by the runtime's
/// `clean_invoke` positional dispatch which caps saturating arity at 32;
/// `emit_trust_ir`/`emit_c` refuse `ClosureApply` beyond it fail-closed —
/// see `emit_apply_runtime`). Kept in lockstep with that runtime ceiling: a
/// wider arm must decline HERE so a saturating apply never reaches
/// `clean_invoke` above 32 (which would `clean_panic`). The 20/21 rung raised
/// this from 18 so `DivisionRing.casesOn`/`recOn` (arity-20 minor premise) and
/// `Field.casesOn`/`recOn` (arity 21) lower; 32 is generous headroom over
/// Field(21) for future wide classes.
const MAX_RUNTIME_APPLY_ARGS: usize = 32;

/// A saturated application of a VALUELESS kernel recursor `<Ind>.rec`,
/// decomposed for the R1 synthesized-recursive-function lowering
/// ([`lower_rec_apply`]).
///
/// Recognized (all conditions checked by [`rec_apply_parts`], each declining
/// fail-closed): single motive, no indices, single inductive block (no
/// mutuals), non-reflexive, non-nested, non-scalar-carrier runtime
/// representation, exact saturation, and — for every RECURSIVE constructor
/// field — a non-erased, DIRECT `<Ind> ..` occurrence, so the synthesized
/// function only ever recurses on a projected constructor component
/// (structural termination by construction).
pub(super) struct RecApplyParts {
    /// The inductive being eliminated.
    ind_name: Name,
    /// `Nat` has a boxed-integer runtime representation: its arms are the
    /// `Nat.zero` constructor alternative plus a `Default` alternative with
    /// `pred := n - 1` (no `Proj`s), mirroring [`lower_nat_cases`].
    is_nat: bool,
    /// The major premise (scrutinee) expression. `None` for the eta-reduced
    /// no-major spelling (`def rangeAux := Nat.rec m z s` — the definition IS
    /// the partially applied recursor): the lowered value is then the
    /// partial application `go minors..` (a closure awaiting the scrutinee),
    /// which lambda lifting turns into an under-applied `Const` — a
    /// `PartialApply` closure downstream. Only recognized for
    /// `MajorAfterMinors` recursors (major LAST), where a missing major is
    /// unambiguous.
    major: Option<Expr>,
    /// The minor premises, in constructor-tag order.
    minors: Vec<Expr>,
    /// Per-constructor arm layout, in constructor-tag order (parallel to
    /// `minors`).
    arms: Vec<RecArmSpec>,
    /// OVER-application arguments: a function-building motive (`List.foldl`'s
    /// `fun _ => β → β`) makes the recursor application return a closure that
    /// the spine immediately applies (`List.rec .. l init`). The synthesized
    /// call's result is closure-applied to these.
    extras: Vec<Expr>,
    /// The recursor application PREFIX (the spine minus `extras`), used to
    /// type the synthesized function's return value.
    rec_app: Expr,
}

/// Constructor-arm layout for [`lower_rec_apply`].
struct RecArmSpec {
    ctor_name: Name,
    fields: Vec<RecFieldSpec>,
    strategy: RecMinorStrategy,
}

/// How a constructor's minor premise is compiled into its `Cases` arm.
enum RecMinorStrategy {
    /// The minor syntactically binds all of the arm's `fields + IHs` (and
    /// its body consumes no erased field binder): the PEELED body is inlined
    /// into the arm, with projections / self-call IHs substituted for the
    /// binders — the classic eliminator IH substitution, and the shape
    /// equation-compiled definitions (`List.foldl`, `List.map`, `List.beq`)
    /// take. No closure is materialized, so the minor's free variables
    /// simply become captures of the synthesized function (lambda-lifted
    /// into plain parameters, threaded through the self-calls).
    ///
    /// A 0-binder minor (0-field constructor: `List.nil`'s value) is the
    /// degenerate inline case — the whole minor expression is the arm body.
    Inline { body: Expr },
    /// Fallback for every other spelling (the eta-reduced bare-variable
    /// minors of `recOn`-style wrapper DEFINITIONS, lambdas with too few
    /// binders, bodies consuming an erased field binder): the minor is
    /// lowered once at the call site and passed to the synthesized function
    /// as a closure parameter, applied in the arm (`clean_apply_n`, erased
    /// fields as boxed units).
    Apply,
}

/// One constructor field as seen by the synthesized recursive function.
struct RecFieldSpec {
    /// Declared field type (from the constructor's Pi-chain, after params);
    /// may contain loose bound variables — used only as the `Proj` binding's
    /// type annotation, same convention as [`lower_ctor_branch`].
    ty: Expr,
    /// Erased at runtime (proof / type / singleton): passed to the minor as
    /// `Arg::Erased`, no projection emitted.
    erased: bool,
    /// Recursive field (direct `<Ind> ..` occurrence): the arm computes its
    /// induction hypothesis by a self-call on the projected component.
    recursive: bool,
}

/// Recognize a saturated VALUELESS-kernel-recursor application `<Ind>.rec
/// (params..) motive (minors..) major` that [`lower_rec_apply`] can lower —
/// the R1 rung: RECURSIVE single-motive, non-indexed inductives (and the
/// leftover non-recursive spellings the C5a `Cases` path declines, e.g.
/// eta-reduced minors), compiled by synthesizing a real recursive function.
///
/// Everything here is ctx-free and side-effect-free: a `None` means the
/// application falls through to the generic constant-application path (where
/// the stage-2 recursor-call guard keeps refusing it fail-closed), never a
/// hard error.
///
/// Out of scope, each declined fail-closed (see [`RecApplyParts`]): indexed
/// families (`Eq.rec`, `HEq.rec`, `Nat.le.rec`), mutual blocks, reflexive
/// inductives (`Acc.rec` — well-founded, NOT structural — and every other
/// function-typed recursive field), nested inductives, scalar-carrier /
/// bespoke-layout runtime representations ([`NON_HEAP_RUNTIME_REPR`]),
/// PUnit-likes (single 0-field constructor: value may be fully erased;
/// parity with [`generic_nonrecursive_rec`]), BESPOKE recursors whose rules
/// are not the constructors' structural elimination rules — Cubical HIT
/// path constructors and lying recursion flags, verified by
/// [`recursor_rules_pair_with_constructors`] — erased recursive fields (an
/// IH over a runtime-erased proof cannot be computed), partial applications,
/// and proof-/type-class majors or minors (no runtime value to scrutinize /
/// apply).
pub(super) fn rec_apply_parts(env: &Environment, expr: &Expr) -> Option<RecApplyParts> {
    let (head, args) = collect_app_args(expr);
    let ExprKind::Const(rec_name, _) = head.kind() else {
        return None;
    };
    if rec_name.last_component().as_deref() != Some("rec") {
        return None;
    }
    let rec = env.get_recursor(rec_name)?;
    // Only VALUELESS kernel recursors: a definition that happens to be named
    // `*.rec` (with a stored value) keeps its compiled-from-source path.
    if env
        .get_const(rec_name)
        .is_some_and(|info| info.value.is_some())
    {
        return None;
    }

    // Single motive, no indices.
    if rec.num_motives != 1 || rec.num_indices != 0 {
        return None;
    }

    let ind_name = rec.inductive_name.clone();
    let ind = env.get_inductive(&ind_name)?;
    if ind.num_indices > 0 || ind.all_names.len() > 1 {
        return None;
    }
    // Reflexive (`Acc`: function-typed recursive field — recursion on it is
    // well-founded, not structural) and nested (recursive occurrence under
    // another type constructor) inductives have no one-field-one-IH
    // structural elimination.
    if ind.is_reflexive || ind.is_nested {
        return None;
    }

    let ind_str = ind_name.to_string();
    // `Bool.rec` keeps its dedicated 2-alt lowering (`bool_cond_branches`).
    if ind_str == "Bool" {
        return None;
    }
    let is_nat = ind_str == "Nat";
    if !is_nat && NON_HEAP_RUNTIME_REPR.contains(&ind_str.as_str()) {
        return None;
    }

    // PUnit-likes keep the baseline generic path (their runtime value may be
    // fully erased), exactly like `generic_nonrecursive_rec`.
    if rec.rules.len() == 1 && rec.rules[0].num_fields == 0 {
        return None;
    }

    // Saturated, OVER-applied, or (for MajorAfterMinors) missing exactly the
    // trailing major; anything shorter falls through. Extras beyond the
    // recursor's own arity arise from function-building motives
    // (`List.foldl`: `List.rec .. l init`) and are closure-applied to the
    // synthesized call's result. A spine that stops right before the major
    // (`def rangeAux := Nat.rec m z s`) IS the partially applied recursor;
    // its value lowers to the partial application `go minors..`.
    let num_params = rec.num_params as usize;
    let num_minors = rec.num_minors as usize;
    let expected = num_params + 1 + num_minors + 1;
    let no_major = args.len() + 1 == expected
        && matches!(
            rec.arg_order,
            clean_kernel::RecursorArgOrder::MajorAfterMinors
        );
    if args.len() < expected && !no_major {
        return None;
    }
    let (major, minors_start) = if no_major {
        (None, num_params + 1)
    } else {
        let (major_idx, minors_start) = match rec.arg_order {
            // params → motive → minors → major
            clean_kernel::RecursorArgOrder::MajorAfterMinors => (expected - 1, num_params + 1),
            // params → motive → major → minors (num_indices == 0)
            clean_kernel::RecursorArgOrder::MajorAfterMotive => (num_params + 1, num_params + 2),
        };
        (Some(args[major_idx]), minors_start)
    };
    let minors = &args[minors_start..minors_start + num_minors];
    let extras = if no_major { &[][..] } else { &args[expected..] };
    // The recursor-application prefix: strip the (outermost) extra `App`
    // layers off the spine.
    let mut rec_app = expr;
    for _ in 0..extras.len() {
        let ExprKind::App(f, _) = rec_app.kind() else {
            return None;
        };
        rec_app = f.as_ref();
    }

    // Constructor / rule / minor alignment (tag order). Beyond the counts,
    // the rules must genuinely BE the constructors' structural elimination
    // rules — names, order, field counts, point-constructor codomains, and
    // recursion-flag consistency ([`recursor_rules_pair_with_constructors`]).
    // The bespoke Cubical HIT recursors (prop-truncation: minors
    // `[isProp, f]` vs rules `[in, squash]`) pass the name check but violate
    // the pairing; they must decline here, keeping the baseline extern path.
    if ind.constructor_names.len() != rec.rules.len() || rec.rules.len() != num_minors {
        return None;
    }
    if !recursor_rules_pair_with_constructors(env, &ind_name, ind, &rec.rules) {
        return None;
    }

    let mut arms = Vec::with_capacity(rec.rules.len());
    for (ctor_name, (rule, minor)) in ind
        .constructor_names
        .iter()
        .zip(rec.rules.iter().zip(minors.iter()))
    {
        if rule.constructor_name != *ctor_name {
            return None;
        }
        let ctor = env.get_constructor(ctor_name)?;
        if ctor.num_fields != rule.num_fields {
            return None;
        }
        let field_tys = constructor_field_types(&ctor.type_, ctor.num_params);
        if field_tys.len() != rule.num_fields as usize {
            return None;
        }
        // Per-field recursion flags, HARDENED: a rule of a RECURSIVE inductive
        // whose `recursive_fields` metadata is absent (empty with fields
        // present) is ambiguous — a missed flag would apply the minor at the
        // wrong arity — so decline. Empty metadata is trusted only when the
        // inductive as a whole is non-recursive (all flags are then false).
        let flags: Vec<bool> = if rule.recursive_fields.len() == field_tys.len() {
            rule.recursive_fields.clone()
        } else if rule.recursive_fields.is_empty() && !ind.is_recursive {
            vec![false; field_tys.len()]
        } else {
            return None;
        };
        let mut fields = Vec::with_capacity(field_tys.len());
        for (j, field_ty) in field_tys.into_iter().enumerate() {
            let recursive = flags[j];
            let erased = is_erased_constructor_field_type(env, &field_ty);
            if recursive {
                // An IH is computed by recursing on the projected component,
                // so the field must be a RUNTIME value of the inductive
                // itself: non-erased and a direct `<Ind> ..` occurrence.
                // (Function-typed occurrences are already excluded via
                // `is_reflexive`; this re-checks directly, fail-closed.)
                if erased {
                    return None;
                }
                match field_ty.get_app_fn().kind() {
                    ExprKind::Const(head_name, _) if *head_name == ind_name => {}
                    _ => return None,
                }
            }
            fields.push(RecFieldSpec {
                ty: field_ty,
                erased,
                recursive,
            });
        }
        let strategy = rec_minor_strategy(minor, &fields);
        // An `Apply` arm materializes a `clean_apply_<n>` with one slot per
        // field (erased included) plus one per IH — INSIDE the synthesized
        // function, where dead-code elimination cannot remove it even when
        // the whole elimination is erased downstream. The runtime models
        // apply up to 32 args (`clean_invoke`'s positional ceiling;
        // `emit_trust_ir`/`emit_c` refuse larger), so an Apply arm whose
        // field+IH count exceeds 32 must decline HERE, keeping the baseline
        // extern/DCE treatment.
        if matches!(strategy, RecMinorStrategy::Apply) {
            let num_ihs = fields.iter().filter(|f| f.recursive).count();
            if fields.len() + num_ihs > MAX_RUNTIME_APPLY_ARGS {
                return None;
            }
        }
        arms.push(RecArmSpec {
            ctor_name: ctor_name.clone(),
            fields,
            strategy,
        });
    }

    // The major (when present) and every minor must be REAL runtime values:
    // a proof-class major has nothing to scrutinize at runtime, and an
    // erased/type-level minor has nothing to apply. Checked ctx-free so
    // declining has no side effects (the enclosing erased context — e.g. a
    // Prop-motive elimination whose whole application is erased downstream —
    // keeps its baseline treatment).
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

    Some(RecApplyParts {
        ind_name,
        is_nat,
        major: major.cloned(),
        minors: minors.iter().map(|minor| (*minor).clone()).collect(),
        arms,
        extras: extras.iter().map(|extra| (*extra).clone()).collect(),
        rec_app: rec_app.clone(),
    })
}

/// Decide how a minor premise is compiled into its arm (ctx-free).
///
/// `Inline` when the minor syntactically binds ALL of the arm's binders
/// (fields, then one IH per recursive field — the recursor minor telescope)
/// and the peeled body never mentions an ERASED field binder (whose runtime
/// slot is an erased dummy; consuming it downstream would be refused
/// fail-closed — the same guard as `generic_nonrecursive_rec`). A 0-binder
/// arm is always `Inline` (the minor expression IS the arm body).
///
/// Everything else — bare-variable minors (`recOn` wrappers), partial
/// lambdas, erased-binder-consuming bodies — is `Apply`.
fn rec_minor_strategy(minor: &Expr, fields: &[RecFieldSpec]) -> RecMinorStrategy {
    let num_ihs = fields.iter().filter(|f| f.recursive).count();
    let needed = fields.len() + num_ihs;

    // Peel exactly `needed` lambda binders.
    let mut body = minor;
    for _ in 0..needed {
        match body.kind() {
            ExprKind::Lam(_, _, inner) => body = inner.as_ref(),
            _ => return RecMinorStrategy::Apply,
        }
    }

    // Binder telescope erasure flags: fields (as computed), then IHs (never
    // erased — recursive fields are guaranteed non-erased by the
    // recognizer). A body mentioning an erased field binder cannot be
    // inlined (the binder's slot is an erased dummy).
    for (j, field) in fields.iter().enumerate() {
        if field.erased {
            let bvar_idx = (needed - 1 - j) as u32;
            if mentions_loose_bvar(body, bvar_idx) {
                return RecMinorStrategy::Apply;
            }
        }
    }

    RecMinorStrategy::Inline { body: body.clone() }
}

/// Lower a recognized saturated `<Ind>.rec` application ([`rec_apply_parts`])
/// by synthesizing a LOCAL RECURSIVE FUNCTION — the R1 rung. This is exactly
/// the semantics of the eliminator (Lean 4's old compiler lowered `.rec` the
/// same way: structural recursion on the major premise):
///
/// ```text
/// fun go (apply_minors..) (x : Ind) : R :=
///   cases x of
///   | ctor_i f_0 .. f_n =>
///       let f_j  := proj_j x                       -- non-erased fields
///       let ih_j := go apply_minors.. f_j          -- recursive fields only
///       <minor_i's peeled body>[f.., ih..]         -- Inline strategy
///       -- or: minor_i f_0 .. f_n ih_.. as a closure apply (Apply strategy)
/// in go apply_minors.. major
/// ```
///
/// * `go` recurses ONLY on projected constructor components (the IH
///   substitution), so the synthesized recursion terminates structurally on
///   every finite value — [`rec_apply_parts`] refuses any field where that
///   is not the case.
/// * `Inline` minors ([`RecMinorStrategy`]) put the minor's own body in the
///   arm; its free variables become captures of `go`, which lambda lifting
///   turns into plain leading parameters threaded through the self-calls
///   (`Decl { recursive: true }`). No closure is materialized — the common
///   equation-compiled shapes (`List.foldl`, `List.map`, `List.beq`,
///   `Nat.beq`) compile to first-order self-recursion.
/// * `Apply` minors (the eta-reduced `recOn`-wrapper spellings) are lowered
///   once at the call site and passed as closure parameters, applied per
///   arm with erased fields as `Arg::Erased` (boxed units).
/// * For `Nat` the arms follow the boxed-integer discipline of
///   [`lower_nat_cases`]: `Nat.zero` alternative + `Default` alternative with
///   `pred := n - 1` (no projections).
///
/// Returns the call-site value `go(apply_minors.., major)` as a `LetValue`,
/// so a recursor application is lowerable in ANY value position (let value,
/// argument, return). Over-applied spines closure-apply the call's result to
/// the extras; the no-major spelling returns the partial application itself.
pub(super) fn lower_rec_apply(
    ctx: &mut LcnfContext<'_>,
    expr: &Expr,
    parts: RecApplyParts,
) -> Result<(LetValue, Expr), CompilerError> {
    // Call-site lowering (current pending scope): the APPLY-strategy minors
    // in tag order, then the major. `rec_apply_parts` pre-classified all of
    // them `Normal`, so each lowers to a real variable; any residual error
    // here is a genuine lowering failure of the sub-expression itself (the
    // same failure the generic constant-application path would hit on the
    // same argument).
    let mut apply_minor_fvars: Vec<clean_kernel::FVarId> = Vec::new();
    let mut apply_param_of_tag: Vec<Option<usize>> = Vec::with_capacity(parts.arms.len());
    for (tag, arm) in parts.arms.iter().enumerate() {
        match arm.strategy {
            RecMinorStrategy::Inline { .. } => apply_param_of_tag.push(None),
            RecMinorStrategy::Apply => match expr_to_arg(ctx, &parts.minors[tag])? {
                Arg::FVar(id) => {
                    apply_param_of_tag.push(Some(apply_minor_fvars.len()));
                    apply_minor_fvars.push(id);
                }
                other => {
                    return Err(CompilerError::InvalidExpr(format!(
                        "recursor minor premise did not lower to a variable: {other:?}"
                    )))
                }
            },
        }
    }
    let scrut_fvar = match &parts.major {
        None => None,
        Some(major) => match expr_to_arg(ctx, major)? {
            Arg::FVar(id) => Some(id),
            other => {
                return Err(CompilerError::InvalidExpr(format!(
                    "recursor major premise did not lower to a variable: {other:?}"
                )))
            }
        },
    };

    // Synthesize `go`. Fresh parameter fvars: the Apply-strategy minors,
    // then the scrutinee. Parameter types must be to_ir-convertible in VALUE
    // position (the `_` placeholder is fail-closed rejected there): minors
    // are runtime closures — `Object`, the lambda-lifter's own closure-type
    // convention — and the scrutinee gets its inferred type when the kernel
    // checker can see it (open terms fall back to `Object`, which is also
    // what any inductive type lowers to).
    let go_fvar = ctx.fresh_fvar();
    let minor_params: Vec<Param> = apply_minor_fvars
        .iter()
        .map(|_| Param::new(ctx.fresh_fvar(), Name::anon(), Expr::const_str("Object")))
        .collect();
    let scrut_ty = if parts.is_nat {
        Expr::const_str("Nat")
    } else {
        match parts
            .major
            .as_ref()
            .map(|major| infer_type_or_placeholder(ctx.env, major))
        {
            Some(ty) if !is_type_placeholder(&ty) => ty,
            _ => Expr::const_str("Object"),
        }
    };
    let scrut_param = Param::new(ctx.fresh_fvar(), Name::anon(), scrut_ty);
    // The synthesized function returns the RECURSOR application's value; the
    // whole (possibly over-applied) expression's type is the value we hand
    // back to the caller. Both sit in return/let position downstream, where
    // the `_` placeholder is accepted (boxed calling convention). For the
    // no-major spelling the function's own result type is unknowable from
    // the spine (`rec_app`'s type is the partial-application Pi), so it
    // stays a placeholder.
    let go_result_ty = if parts.major.is_some() {
        infer_type_or_placeholder(ctx.env, &parts.rec_app)
    } else {
        Expr::const_str("_")
    };
    let result_ty = if parts.extras.is_empty() && parts.major.is_some() {
        go_result_ty.clone()
    } else {
        infer_type_or_placeholder(ctx.env, expr)
    };

    let minor_param_fvars: Vec<clean_kernel::FVarId> =
        minor_params.iter().map(|p| p.fvar_id).collect();
    let alts = build_rec_apply_alts(
        ctx,
        &parts,
        go_fvar,
        &minor_param_fvars,
        &apply_param_of_tag,
        scrut_param.fvar_id,
    )?;
    let cases = Code::Cases(Cases::new(
        parts.ind_name.clone(),
        go_result_ty.clone(),
        scrut_param.fvar_id,
        alts,
    ));

    let mut params = minor_params;
    params.push(scrut_param);
    ctx.add_fun(FunDecl::new(
        go_fvar,
        Name::from_string("_rec"),
        params,
        go_result_ty.clone(),
        cases,
    ));

    let mut call_args: Vec<Arg> = apply_minor_fvars.into_iter().map(Arg::FVar).collect();
    if let Some(scrut_fvar) = scrut_fvar {
        call_args.push(Arg::FVar(scrut_fvar));
    }
    let call_value = LetValue::FVar {
        fvar: go_fvar,
        args: call_args,
    };
    // No-major spelling: the value IS the partial application `go minors..`
    // (one argument short of `go`'s arity) — lambda lifting rewrites it into
    // an under-applied `Const`, i.e. a `PartialApply` closure downstream.
    if parts.extras.is_empty() {
        return Ok((call_value, result_ty));
    }

    // Over-applied spine: bind the synthesized call, then closure-apply its
    // result (a motive-built function) to the extra arguments.
    let extra_args = parts
        .extras
        .iter()
        .map(|extra| expr_to_arg(ctx, extra))
        .collect::<Result<Vec<_>, _>>()?;
    let call_fvar = ctx.add_let(Name::anon(), go_result_ty, call_value);
    Ok((
        LetValue::FVar {
            fvar: call_fvar,
            args: extra_args,
        },
        result_ty,
    ))
}

/// Count the leading lambda binders of an expression.
fn count_leading_lams(mut e: &Expr) -> usize {
    let mut n = 0;
    while let ExprKind::Lam(_, _, body) = e.kind() {
        n += 1;
        e = body.as_ref();
    }
    n
}

/// A recognized WELL-FOUNDED eliminator application — the RUNG-B shape.
///
/// `Acc r a : Prop` makes the eliminator's major premise (the accessibility
/// proof) an ERASED `box(0)` at runtime, so the recursion CANNOT be driven by
/// projecting that scrutinee (the C3 erased-proof segfault). It is instead a
/// recursion on the decreasing VALUE — recovered here from the recursor INDEX,
/// never from the erased proof — witnessed (at the type level only) by the
/// erased proof. [`lower_wf_rec_apply`] synthesizes a self-referential `go`
/// whose induction-hypothesis closure ignores the runtime-irrelevant proof.
pub(super) struct WfRecParts {
    /// The step function handed the value and the IH closure.
    ///
    /// * `Acc.rec`'s minor `(x) (h) (ih) -> motive x (Acc.intro x h)` — three
    ///   runtime slots, the middle (`h`, the erased accessibility subproof)
    ///   passed as `box(0)` (`has_erased_hyp`).
    /// * `WellFounded.fix{,F}`'s `F : (x) ((y) -> r y x -> C y) -> C x` — two
    ///   runtime slots (value, IH), no erased middle.
    step: Expr,
    /// The starting/decreasing value — the recursor INDEX. NEVER the erased
    /// `Acc` scrutinee.
    index: Expr,
    /// `Acc.rec` interposes an erased accessibility-subproof slot between the
    /// value and the IH; `WellFounded.fix{,F}`'s `F` does not.
    has_erased_hyp: bool,
    /// Over-application arguments (the eliminator's result is a function then
    /// applied further) — closure-applied to the synthesized call, mirroring
    /// [`RecApplyParts::extras`].
    extras: Vec<Expr>,
    /// The saturated eliminator sub-expression (spine minus `extras`), used to
    /// type the synthesized call's result.
    rec_app: Expr,
}

/// Recognize a saturated application of a well-founded eliminator —
/// `Acc.rec`, `WellFounded.fixF`, or `WellFounded.fix` — that
/// [`lower_wf_rec_apply`] can compile to a value-recursive `go`.
///
/// Ctx-free and side-effect-free: a `None` leaves the application on the
/// generic constant path (`Acc.rec` there is refused fail-closed by the
/// stage-2 link-honesty guard; `WellFounded.fix{,F}` stay honest extern
/// boundaries — definitions with values). Declined fail-closed:
///
/// * a step or index that is not a real runtime value (`classify_expr_arg`
///   `!= Normal`) — e.g. an `Acc.rec` over a Prop-sorted carrier whose index
///   cannot be recovered, exactly the "decreasing value not recoverable"
///   decline the RUNG-B contract mandates;
/// * `Acc.rec` with a `casesOn`-shaped minor — a lambda with fewer than the 3
///   telescope binders `(x)(h)(ih)`, i.e. NO induction hypothesis. That is
///   `Acc.casesOn`: a `Cases` over the erased `Acc` scrutinee that would
///   read its erased fields (the C3 hazard). Declined here — the well-founded
///   recursion path only compiles genuine recursion.
pub(super) fn wf_rec_apply_parts(env: &Environment, expr: &Expr) -> Option<WfRecParts> {
    let (head, args) = collect_app_args(expr);
    let ExprKind::Const(name, _) = head.kind() else {
        return None;
    };
    // Positional layout of each well-founded eliminator's SATURATED spine.
    // Every spine has SIX core arguments; `core` is that count (NOT
    // `value_idx + 1` — for `Acc.rec`/`fixF` the erased major/accessibility
    // proof sits at index 5, AFTER the value index, and must be dropped, not
    // mistaken for an over-application extra).
    let (step_idx, value_idx, has_erased_hyp) = match name.to_string().as_str() {
        // Acc.rec α r motive (minor) {a} (t)   — minor (x)(h)(ih); index a; erased major t.
        "Acc.rec" => (3usize, 4usize, true),
        // WellFounded.fixF α r C (F) (x) (a)   — F (x)(ih); index x; erased acc a.
        "WellFounded.fixF" => (3, 4, false),
        // WellFounded.fix α r C (hwf) (F) (x)  — F (x)(ih); index x; erased wf hwf.
        "WellFounded.fix" => (4, 5, false),
        _ => return None,
    };
    const CORE: usize = 6;
    // Extras beyond the six-arg core are over-application. A shorter spine is a
    // partial application — leave it on the generic path (a harmless PAP; the
    // erased major/proof it would eventually take is not present yet).
    let core = CORE;
    if args.len() < core {
        return None;
    }
    let extras = &args[core..];
    let mut rec_app = expr;
    for _ in 0..extras.len() {
        let ExprKind::App(f, _) = rec_app.kind() else {
            return None;
        };
        rec_app = f.as_ref();
    }

    let step = args[step_idx];
    let index = args[value_idx];
    // Both the step closure and the decreasing value must be REAL runtime
    // values; if the index is erased/type-level the decreasing value cannot be
    // recovered — decline fail-closed.
    if classify_expr_arg(env, step) != ExprArgClass::Normal {
        return None;
    }
    if classify_expr_arg(env, index) != ExprArgClass::Normal {
        return None;
    }
    // `Acc.rec` with a lambda minor of fewer than 3 binders is `Acc.casesOn`
    // (no IH) — the erased-field Cases the C3 hazard forbids. A non-lambda
    // minor (`Acc.recOn` passes its recursor param through) is trusted at its
    // 3-ary type.
    if has_erased_hyp
        && matches!(step.kind(), ExprKind::Lam(_, _, _))
        && count_leading_lams(step) < 3
    {
        return None;
    }

    Some(WfRecParts {
        step: step.clone(),
        index: index.clone(),
        has_erased_hyp,
        extras: extras.iter().map(|e| (*e).clone()).collect(),
        rec_app: rec_app.clone(),
    })
}

/// Lower a recognized well-founded eliminator ([`wf_rec_apply_parts`]) by
/// synthesizing a SELF-RECURSIVE local function — the RUNG-B rung.
///
/// ```text
/// fun go (step) (v) (hr) : Object :=      -- hr is the erased `r v _` slot
///   let ih  := go step                     -- PAP: closure awaiting (v', hr')
///   step v [box(0)] ih                     -- box(0) only for Acc.rec's `h`
/// in go step index [box(0)]
/// ```
///
/// * `go`'s own parameter list IS the induction hypothesis's runtime telescope
///   (the decreasing value `v` and the erased proof slot `hr`) plus the
///   captured `step`. The IH the step is handed — `go` partially applied to
///   `step` — is therefore a faithful `(v') (hr') |-> go step v' hr'`: it
///   recurses on the actual value `v'` and DROPS the erased proof `hr'`.
/// * `go` NEVER inspects the erased `Acc` scrutinee: the value is `v` (the
///   recovered index), the erased accessibility subproof is a `box(0)` slot,
///   and the major premise is simply not lowered.
/// * Termination is exactly the source's: `go step v'` runs only where the
///   step invokes its IH on `v'`, which the step (`F` / the minor) does solely
///   for `v'` with `r v' v` — a decrease witnessed by the erased proof. The
///   synthesized call graph is the well-founded recursion's, so it terminates
///   on every input the source does.
pub(super) fn lower_wf_rec_apply(
    ctx: &mut LcnfContext<'_>,
    expr: &Expr,
    parts: WfRecParts,
) -> Result<(LetValue, Expr), CompilerError> {
    // Call-site values (outer scope): the step closure and the starting value.
    let step_fvar = match expr_to_arg(ctx, &parts.step)? {
        Arg::FVar(id) => id,
        other => {
            return Err(CompilerError::InvalidExpr(format!(
                "well-founded step did not lower to a variable: {other:?}"
            )))
        }
    };
    let index_fvar = match expr_to_arg(ctx, &parts.index)? {
        Arg::FVar(id) => id,
        other => {
            return Err(CompilerError::InvalidExpr(format!(
                "well-founded index did not lower to a variable: {other:?}"
            )))
        }
    };

    // Synthesize `go`. All three parameters are boxed `Object`: `step` is a
    // runtime closure, `v` the boxed value, `hr` the erased proof slot the IH
    // application lands its (erased, `box(0)`) proof argument into.
    let go_fvar = ctx.fresh_fvar();
    let obj = || Expr::const_str("Object");
    let step_param = Param::new(ctx.fresh_fvar(), Name::anon(), obj());
    let v_param = Param::new(ctx.fresh_fvar(), Name::anon(), obj());
    let hr_param = Param::new(ctx.fresh_fvar(), Name::anon(), obj());

    // Build `go`'s body in an isolated pending scope (the outer call-site lets
    // for `step`/`index` are preserved and restored afterwards).
    let outer_pending = ctx.take_pending();
    // ih := go step   (one argument short of `go`'s arity 3 -> a PartialApply
    // closure downstream, awaiting the value and the erased proof slot).
    let ih_fvar = ctx.add_let(
        Name::anon(),
        obj(),
        LetValue::FVar {
            fvar: go_fvar,
            args: vec![Arg::FVar(step_param.fvar_id)],
        },
    );
    // step v [box(0):h] ih
    let mut apply_args: Vec<Arg> = Vec::with_capacity(3);
    apply_args.push(Arg::FVar(v_param.fvar_id));
    if parts.has_erased_hyp {
        apply_args.push(Arg::Erased);
    }
    apply_args.push(Arg::FVar(ih_fvar));
    let res_fvar = ctx.add_let(
        Name::anon(),
        obj(),
        LetValue::FVar {
            fvar: step_param.fvar_id,
            args: apply_args,
        },
    );
    let go_body = ctx.wrap_lets(Code::ret(res_fvar));
    ctx.restore_pending(outer_pending);

    ctx.add_fun(FunDecl::new(
        go_fvar,
        Name::from_string("_wf_rec"),
        vec![step_param, v_param, hr_param],
        obj(),
        go_body,
    ));

    // Entry: go step index <erased hr>.
    let call_value = LetValue::FVar {
        fvar: go_fvar,
        args: vec![Arg::FVar(step_fvar), Arg::FVar(index_fvar), Arg::Erased],
    };
    let result_ty = infer_type_or_placeholder(ctx.env, &parts.rec_app);
    if parts.extras.is_empty() {
        return Ok((call_value, result_ty));
    }

    // Over-applied spine: bind the call, then closure-apply the result to the
    // extra arguments (mirrors [`lower_rec_apply`]).
    let extra_args = parts
        .extras
        .iter()
        .map(|extra| expr_to_arg(ctx, extra))
        .collect::<Result<Vec<_>, _>>()?;
    let call_fvar = ctx.add_let(Name::anon(), result_ty, call_value);
    Ok((
        LetValue::FVar {
            fvar: call_fvar,
            args: extra_args,
        },
        infer_type_or_placeholder(ctx.env, expr),
    ))
}

/// Build the `Cases` alternatives of a synthesized recursive eliminator
/// function, honoring each arm's [`RecMinorStrategy`]. For `Nat` the two
/// arms take the boxed-integer shape (`Nat.zero` ctor alternative + `Default`
/// with `pred := n - 1`); everything else gets one constructor-tag-ordered
/// alternative per constructor with `Proj`-bound fields.
fn build_rec_apply_alts(
    ctx: &mut LcnfContext<'_>,
    parts: &RecApplyParts,
    go_fvar: clean_kernel::FVarId,
    minor_params: &[clean_kernel::FVarId],
    apply_param_of_tag: &[Option<usize>],
    scrut: clean_kernel::FVarId,
) -> Result<Vec<Alt>, CompilerError> {
    let mut alts = Vec::with_capacity(parts.arms.len());
    for (tag, arm) in parts.arms.iter().enumerate() {
        let apply_param = apply_param_of_tag[tag].map(|idx| minor_params[idx]);
        let body = if parts.is_nat {
            // Tag order pinned by the recognizer: 0 = Nat.zero (no fields),
            // 1 = Nat.succ (pred + IH via `Nat.sub`, no projections).
            if tag == 0 {
                build_rec_arm_body(ctx, go_fvar, minor_params, arm, apply_param, &[])?
            } else {
                build_nat_succ_arm_body(ctx, go_fvar, minor_params, arm, apply_param, scrut)?
            }
        } else {
            build_rec_arm_body(
                ctx,
                go_fvar,
                minor_params,
                arm,
                apply_param,
                &[(scrut, &arm.ctor_name)],
            )?
        };
        if parts.is_nat && tag == 1 {
            alts.push(Alt::default(body));
        } else {
            alts.push(Alt::ctor(arm.ctor_name.clone(), Vec::new(), body));
        }
    }
    Ok(alts)
}

/// Build one generic constructor arm. `proj_source` carries the scrutinee
/// and projection key for field binding; empty for the `Nat.zero` arm (whose
/// constructor has no fields).
///
/// Field bindings (in order), then IH bindings (one per recursive field, a
/// `go` self-call on the projected component — the ONLY self-call sites, so
/// the recursion is structural by construction). The arm body is then either
/// the minor's peeled body lowered in place (`Inline` — binders resolve to
/// the field/IH fvars pushed on the bvar stack) or a closure application of
/// the minor parameter (`Apply`).
fn build_rec_arm_body(
    ctx: &mut LcnfContext<'_>,
    go_fvar: clean_kernel::FVarId,
    minor_params: &[clean_kernel::FVarId],
    arm: &RecArmSpec,
    apply_param: Option<clean_kernel::FVarId>,
    proj_source: &[(clean_kernel::FVarId, &Name)],
) -> Result<Code, CompilerError> {
    let outer_pending = ctx.take_pending();
    let mut pushed = 0usize;

    // Fields: projections for non-erased fields, erased dummies otherwise
    // (De Bruijn alignment for Inline; `Arg::Erased` slots for Apply).
    let mut field_slots: Vec<(Option<clean_kernel::FVarId>, bool)> =
        Vec::with_capacity(arm.fields.len());
    for (field_idx, field) in arm.fields.iter().enumerate() {
        if field.erased {
            let dummy = ctx.add_let(Name::anon(), Expr::const_str("_"), LetValue::Erased);
            ctx.bvar_stack.push(dummy);
            pushed += 1;
            field_slots.push((None, false));
            continue;
        }
        let Some((scrut, ctor_name)) = proj_source.first() else {
            // Unreachable by construction (only Nat.zero has no proj source,
            // and it has no fields); fail closed rather than panic.
            ctx.abandon_pending(outer_pending);
            return Err(CompilerError::InvalidExpr(
                "recursor arm with fields but no projection source".into(),
            ));
        };
        let field_fvar = ctx.add_let(
            Name::anon(),
            field.ty.clone(),
            LetValue::Proj {
                type_name: (*ctor_name).clone(),
                idx: field_idx as u32,
                structure: *scrut,
            },
        );
        ctx.bvar_stack.push(field_fvar);
        pushed += 1;
        field_slots.push((Some(field_fvar), field.recursive));
    }

    // IHs: `ih := go(apply_minors.., field)` per recursive field, in field
    // order (the recursor minor telescope lists fields first, then IHs).
    let mut ih_fvars: Vec<clean_kernel::FVarId> = Vec::new();
    for (field_fvar, recursive) in &field_slots {
        if !*recursive {
            continue;
        }
        let Some(field_fvar) = field_fvar else {
            continue;
        };
        let mut rec_args: Vec<Arg> = minor_params.iter().copied().map(Arg::FVar).collect();
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
        // Inline: lower the peeled minor body; its binders (fields, then
        // IHs) resolve to the fvars pushed above.
        (RecMinorStrategy::Inline { body }, _) => {
            let body = body.clone();
            expr_to_code(ctx, &body)
        }
        // Apply: closure-apply the minor parameter to fields then IHs
        // (erased fields as boxed units); 0-binder arms return the minor
        // value itself.
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
            "recursor Apply arm without a minor parameter".into(),
        )),
    };

    for _ in 0..pushed {
        ctx.bvar_stack.pop();
    }
    match result {
        Ok(body) => {
            ctx.restore_pending(outer_pending);
            Ok(body)
        }
        Err(err) => {
            ctx.abandon_pending(outer_pending);
            Err(err)
        }
    }
}

/// Build the `Nat` successor arm (the `Default` alternative): binds
/// `pred := n - 1` (the boxed-integer stand-in for the constructor field)
/// and `ih := go(apply_minors.., pred)`, then inlines the minor's peeled
/// body or closure-applies the minor parameter to `(pred, ih)` — the
/// boxed-integer discipline of [`lower_nat_cases`].
fn build_nat_succ_arm_body(
    ctx: &mut LcnfContext<'_>,
    go_fvar: clean_kernel::FVarId,
    minor_params: &[clean_kernel::FVarId],
    arm: &RecArmSpec,
    apply_param: Option<clean_kernel::FVarId>,
    scrut: clean_kernel::FVarId,
) -> Result<Code, CompilerError> {
    let outer_pending = ctx.take_pending();

    // pred := Nat.sub n 1
    let nat_ty = Expr::const_str("Nat");
    let one_fvar = ctx.add_let(Name::anon(), nat_ty.clone(), LetValue::nat(1));
    let pred_fvar = ctx.add_let(
        Name::anon(),
        nat_ty,
        LetValue::Const {
            name: Name::from_string("Nat.sub"),
            levels: Vec::new(),
            args: vec![Arg::FVar(scrut), Arg::FVar(one_fvar)],
        },
    );

    // ih := go(apply_minors.., pred)
    let mut rec_args: Vec<Arg> = minor_params.iter().copied().map(Arg::FVar).collect();
    rec_args.push(Arg::FVar(pred_fvar));
    let ih_fvar = ctx.add_let(
        Name::anon(),
        Expr::const_str("_"),
        LetValue::FVar {
            fvar: go_fvar,
            args: rec_args,
        },
    );

    let result = match (&arm.strategy, apply_param) {
        (RecMinorStrategy::Inline { body }, _) => {
            let body = body.clone();
            // De Bruijn order in the peeled body: BVar 1 = pred, BVar 0 = ih.
            ctx.bvar_stack.push(pred_fvar);
            ctx.bvar_stack.push(ih_fvar);
            let result = expr_to_code(ctx, &body);
            ctx.bvar_stack.pop();
            ctx.bvar_stack.pop();
            result
        }
        (RecMinorStrategy::Apply, Some(minor_param)) => {
            let result_fvar = ctx.add_let(
                Name::anon(),
                Expr::const_str("_"),
                LetValue::FVar {
                    fvar: minor_param,
                    args: vec![Arg::FVar(pred_fvar), Arg::FVar(ih_fvar)],
                },
            );
            Ok(ctx.wrap_lets(Code::Return(result_fvar)))
        }
        (RecMinorStrategy::Apply, None) => Err(CompilerError::InvalidExpr(
            "recursor Apply arm without a minor parameter".into(),
        )),
    };

    match result {
        Ok(body) => {
            ctx.restore_pending(outer_pending);
            Ok(body)
        }
        Err(err) => {
            ctx.abandon_pending(outer_pending);
            Err(err)
        }
    }
}

/// Classify a definition as type-level machinery with no runtime content.
///
/// Used by [`constant_to_decl`] as a structured fallback when body lowering
/// fails: a qualifying declaration is *dropped* (`Ok(None)`, the same
/// convention as noncomputable/valueless constants) so downstream callers
/// treat it as an extern symbol, instead of surfacing a lowering error — or,
/// before the pending-scope hardening, panicking.
///
/// Two provably runtime-irrelevant shapes qualify:
///
/// * the declared type's Pi-telescope codomain is itself `Sort _` / `SProp`:
///   the definition *returns a type* (e.g. `Bool.noConfusionType`, and the
///   `Prop`-valued class heads `LE.le` / `LT.lt` / `Membership.mem`);
/// * the `noConfusion` eliminator family (`<Ind>.noConfusion` /
///   `<Ind>.noConfusionType`) — but only with structural Sort-codomain
///   EVIDENCE, never on the name alone: the declared codomain must either be
///   headed by a `Sort`-typed binder of the telescope (the `{P : Sort v}`
///   motive itself) or by a `*.noConfusionType` constant whose own declared
///   telescope-codomain is a `Sort`/`SProp`. A user data-returning definition
///   that merely NAMES itself `Foo.noConfusion : … → Nat` therefore does NOT
///   qualify and keeps its structured lowering error (C5a review hardening).
///
/// A definition that returns data (e.g. a hypothetical `… → Bool` /
/// `… → Nat` / `… → Int` head) NEVER qualifies — erasing a data-returning
/// definition would be silent miscompilation, so those keep their structured
/// lowering error (and the extern fallback covers callers), matching the C
/// pipeline's extern-drop treatment of the same heads.
fn is_type_level_machinery(env: &Environment, info: &ConstantInfo) -> bool {
    // (a) The definition returns a type: codomain of the declared type is a
    // Sort. (Checked on the *declared type*, which is closed, so no open-term
    // type inference is involved.) Binder domains are collected on the way
    // down so arm (b) can resolve a BVar-headed codomain to its binder.
    let mut domains: Vec<&Expr> = Vec::new();
    let mut codomain = &info.type_;
    while let ExprKind::Pi(_, domain, body) = codomain.kind() {
        domains.push(domain.as_ref());
        codomain = body.as_ref();
    }
    if matches!(codomain.kind(), ExprKind::Sort(_) | ExprKind::SProp) {
        return true;
    }

    // (b) The noConfusion eliminator family: the name gate alone is not
    // sufficient (a user def can be named `*.noConfusion` and return data),
    // so require Sort-codomain evidence on top of it.
    if !matches!(
        info.name.last_component().as_deref(),
        Some("noConfusion" | "noConfusionType")
    ) {
        return false;
    }
    let (head, _) = collect_app_args(codomain);
    match head.kind() {
        // Result IS the motive binder (`… → P …` with `P : … → Sort v` in the
        // telescope): resolve the BVar to its binder domain and require that
        // domain's own telescope-codomain to be a Sort/SProp.
        ExprKind::BVar(idx) => {
            let Some(binder_domain) = domains
                .len()
                .checked_sub(1 + *idx as usize)
                .and_then(|i| domains.get(i))
            else {
                return false;
            };
            matches!(
                telescope_codomain(binder_domain).kind(),
                ExprKind::Sort(_) | ExprKind::SProp
            )
        }
        // Result is `<Ind>.noConfusionType P v1 v2 …`: require the head
        // constant to be a `*.noConfusionType` whose own declared
        // telescope-codomain is a Sort/SProp.
        ExprKind::Const(head_name, _) => {
            head_name.last_component().as_deref() == Some("noConfusionType")
                && env.get_const(head_name).is_some_and(|head_info| {
                    matches!(
                        telescope_codomain(&head_info.type_).kind(),
                        ExprKind::Sort(_) | ExprKind::SProp
                    )
                })
        }
        _ => false,
    }
}

/// Peel the Pi telescope of a type expression and return its codomain.
fn telescope_codomain(ty: &Expr) -> &Expr {
    let mut codomain = ty;
    while let ExprKind::Pi(_, _, body) = codomain.kind() {
        codomain = body.as_ref();
    }
    codomain
}

/// Convert a constant definition to an L5CNF declaration.
///
/// Returns `Some(Decl)` for definitions with values, `None` for axioms/opaque
/// or noncomputable definitions (which are excluded from code generation),
/// and for type-level machinery whose body does not lower (see
/// [`is_type_level_machinery`]).
pub fn constant_to_decl(
    env: &Environment,
    info: &ConstantInfo,
) -> Result<Option<Decl>, CompilerError> {
    // Skip noncomputable definitions — they have no runtime representation.
    if env.is_noncomputable(&info.name) {
        return Ok(None);
    }

    // Only process definitions with values
    let value = match &info.value {
        Some(v) => v,
        None => return Ok(None), // Axioms and opaque definitions
    };

    let mut ctx = LcnfContext::new(env);

    // Collect lambda parameters
    let mut params = Vec::new();
    let mut curr_expr = value;

    while let ExprKind::Lam(_, ty, body) = curr_expr.kind() {
        let fvar = ctx.push_binder();
        params.push(Param::new(fvar, Name::anon(), ty.as_ref().clone()));
        curr_expr = body.as_ref();
    }

    // Convert body to code. If lowering fails and the declaration is
    // provably type-level machinery (returns a type / noConfusion family),
    // drop it via the structured `Ok(None)` convention instead of erroring:
    // callers then treat it as extern, exactly like theorems and
    // noncomputable definitions. The fallback fires only on failure, so any
    // such declaration that DOES lower (e.g. `Empty.noConfusionType`) keeps
    // compiling from source unchanged.
    // PROOF-VALUED DECLARATION (a definition that RETURNS a proof): the declared
    // (closed) kernel type says the fully-applied result lives in `Prop`, so the
    // whole body is a PROOF — runtime-irrelevant, erased at runtime exactly as
    // Lean's own compiler erases proofs. Compiling the proof term to runtime code
    // instead materializes references to type-formers (`Nat.le` / `Eq` / `And` /
    // `Or`) and sibling proof lemmas as DANGLING `l_*` externs, which the native
    // link's shim selection fails-closed on (the reason `Nat.decLe` / `Nat.decLt`
    // / `Char.ofNat` / … lowered-OK but would not LINK). Emit the faithful stub
    // `let r := ⟨erased⟩; return r` BEFORE attempting to lower the body, so a
    // proof lemma's spine (and its lambda-lifted helpers) is never emitted and no
    // dangling call is ever produced. `prop_valued_const(_, 0, _)` reads only the
    // closed declared type (no open-term inference), so this is EXACT — it fires
    // only for genuinely Prop-valued declarations, never a data-returning callee.
    // This mirrors the `is_type_level_machinery` erasure below (a definition that
    // returns a TYPE); together they extend the same mechanism that erased the
    // +94 bucket-A roots and `Int.NonNeg` to the proof-machinery residue.
    // Type-level machinery (a definition whose declared type's Pi-telescope
    // codomain is a `Sort`/`SProp`) is erased PROACTIVELY, exactly like a
    // Prop-valued const: its whole body is runtime-irrelevant, so erasing it to
    // the erased token is Lean's own compiler erasure — never a miscompilation.
    // Doing this before `expr_to_code` (rather than only as an Err fallback
    // below) keeps the class heads `LE.le`/`LT.lt`/`Membership.mem` erased even
    // now that their dictionary-projection body CAN lower (the `Proj` head arm
    // in `expr_to_let_value`); a data-returning callee like `Ord.compare`
    // (codomain `Ordering`) is NOT type-level machinery and still lowers.
    let body = if crate::to_mono::prop_valued_const(&info.name, 0, env)
        || is_type_level_machinery(env, info)
    {
        let r = ctx.fresh_fvar();
        Code::let_bind(
            LetDecl::new(r, Name::anon(), Expr::const_str("_"), LetValue::Erased),
            Code::Return(r),
        )
    } else {
        match expr_to_code(&mut ctx, curr_expr) {
            Ok(body) => body,
            // Type-level machinery (a definition that RETURNS a type) whose body
            // does not lower. Rather than dropping it to an extern boundary
            // (`Ok(None)`), emit a faithful erased-returning stub
            // `let r := ⟨erased⟩; return r`. `is_type_level_machinery` proved the
            // declared type's Pi-telescope codomain is a `Sort`/`SProp` (checked on
            // the closed declared type), so the whole body is runtime-irrelevant and
            // erasing it to the erased token is EXACTLY Lean's own compiler erasure —
            // never a miscompilation of runtime data. This lets such roots
            // (`Bool.noConfusionType`, the `LE.le`/`LT.lt`/`Membership.mem` class
            // heads, `DecidableEq`, `Nat.lt`, `Nat.isValidChar`, …) emit end-to-end
            // instead of only ever being extern-referenced. `fresh_fvar` draws from
            // the same generator as the params (no id collision); the stub is built
            // directly, discarding any partial locals the failed attempt accumulated.
            Err(_) if is_type_level_machinery(env, info) => {
                let r = ctx.fresh_fvar();
                Code::let_bind(
                    LetDecl::new(r, Name::anon(), Expr::const_str("_"), LetValue::Erased),
                    Code::Return(r),
                )
            }
            Err(err) => return Err(err),
        }
    };

    // Pop all binders
    for _ in &params {
        ctx.pop_binder();
    }

    // Detect recursion by checking whether any direct callee in the lowered body
    // reaches this declaration through the environment definition graph.
    let is_recursive = body_reaches_decl(env, &body, &info.name);
    let result_ty = strip_runtime_param_binders(&info.type_, params.len());

    Ok(Some(Decl::new(
        info.name.clone(),
        info.level_params.clone(),
        result_ty,
        params,
        body,
        is_recursive,
    )))
}

fn strip_runtime_param_binders(ty: &Expr, param_count: usize) -> Expr {
    let mut current = ty;
    for _ in 0..param_count {
        let ExprKind::Pi(_, _, body) = current.kind() else {
            break;
        };
        current = body.as_ref();
    }
    current.clone()
}

/// Approximate Lean 4's `markRecDecls` SCC marking without explicit block metadata.
///
/// Lean 4 lowers a whole declaration block and then marks a declaration
/// recursive when the block contains an executable reference to it. clean
/// currently lowers declarations one at a time, so we recover the same signal
/// by following runtime-relevant constant edges from this body through
/// environment definitions until we either revisit `target` or exhaust the
/// reachable graph.
fn body_reaches_decl(env: &Environment, body: &Code, target: &Name) -> bool {
    let mut stack: Vec<Name> = code_called_constant_names(body).into_iter().collect();
    let mut visited = HashSet::new();

    while let Some(name) = stack.pop() {
        if name == *target {
            return true;
        }
        if !visited.insert(name.clone()) {
            continue;
        }

        let Some(info) = env.get_const(&name) else {
            continue;
        };
        if !matches!(info.kind, ConstantKind::Definition) {
            continue;
        }

        let Some(value) = &info.value else {
            continue;
        };
        stack.extend(
            expr_called_constant_names(env, value)
                .into_iter()
                .filter(|dep| !visited.contains(dep)),
        );
    }

    false
}

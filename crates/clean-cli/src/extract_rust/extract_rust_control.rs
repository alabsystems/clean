// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! CONTROL-FLOW special forms of the v1 Rust emitter — `Nat.rec` (counted
//! loop), `Nat.casesOn` (zero/succ branch), and `ite`. Split from
//! `extract_rust.rs` when the `BEq.beq` arm took it past the 1000-line
//! paragon bar; the seam is the file's own: the special-form TABLE vs the
//! generic translation machinery, which stays in the parent.

use super::*;

/// `Nat.rec motive z (fun k ih => s) n` → a COUNTED LOOP.
///
/// `Nat.rec z s n` means "apply `s` n times starting from `z`", so it lowers to
///
/// ```text
/// { let t = <n>; let mut acc = <z>; let mut i = 0;
///   while i < t { let k = i; let ih = acc; acc = <s>; i += 1; }
///   acc }
/// ```
///
/// TERMINATION IS INHERITED, NOT ARGUED. The kernel accepted the source
/// definition only because `Nat.rec` is well-founded; the emitted loop runs
/// exactly `t` times, so the bound is manifest in the artifact. That is why the
/// gate admits `Nat.rec` while still refusing `WellFounded.fix`/`Acc.rec`,
/// whose termination rests on an accessibility proof that extraction ERASES.
/// The distinction matters practically: a non-terminating extraction would HANG
/// the differential battery rather than fail it, and a hang is the one outcome
/// this harness cannot report.
///
/// Emitted as a loop rather than a recursive `fn` deliberately — recursion depth
/// on a `Nat` battery point like 63 is fine, but the loop form makes the bound
/// syntactically obvious and cannot blow the stack.
pub(super) fn translate_nat_rec(
    args: &[&Expr],
    expected: ScalarTy,
    params: &[(String, ScalarTy)],
) -> Result<Rendered, RustEmitError> {
    let [_motive, zero_case, step, scrut] = args else {
        return Err(RustEmitError::Unsupported(format!(
            "`Nat.rec` applied to {} argument(s); expected 4 (motive, z, step, n)",
            args.len()
        )));
    };

    // The step is `fun k => fun ih => body`.
    let ExprKind::Lam(_, _, step1) = strip_mdata(step).kind() else {
        return Err(RustEmitError::Unsupported(format!(
            "`Nat.rec`'s step is a {}, not a lambda binding the index",
            form_name(strip_mdata(step).kind())
        )));
    };
    let ExprKind::Lam(_, _, step_body) = strip_mdata(step1).kind() else {
        return Err(RustEmitError::Unsupported(format!(
            "`Nat.rec`'s step binds only one argument (a {}); it must bind the index \
             AND the recursive result",
            form_name(strip_mdata(step1).kind())
        )));
    };

    let t = translate(scrut, ScalarTy::Nat, params)?;
    let z = translate(zero_case, expected, params)?;

    let depth = params.len();
    let (tn, acc, idx) = (
        format!("__t{depth}"),
        format!("__a{depth}"),
        format!("__i{depth}"),
    );
    let (kname, ihname) = (format!("__k{depth}"), format!("__h{depth}"));
    // Binder order: `k` then `ih`, so `ih` is the innermost de Bruijn index.
    let mut inner = params.to_vec();
    inner.push((kname.clone(), ScalarTy::Nat));
    inner.push((ihname.clone(), expected));
    let body = translate(step_body, expected, &inner)?;

    Ok(Rendered::atom(format!(
        "{{ let {tn} = {}; let mut {acc} = {}; let mut {idx}: u64 = 0; \
         while {idx} < {tn} {{ let {kname} = {idx}; let {ihname} = {acc}; \
         {acc} = {}; {idx} += 1; }} {acc} }}",
        t.text, z.text, body.text
    )))
}

/// `Nat.casesOn motive n z (fun k => s)` → a zero/succ branch.
///
/// The second control-flow form, and the first that BINDS a variable:
///
/// ```text
/// { let n = <scrut>; if n == 0 { <z> } else { let k = n - 1; <s> } }
/// ```
///
/// The scrutinee is bound ONCE rather than substituted into both arms — it can
/// be an arbitrary expression, and duplicating it would duplicate its work (and
/// its overflow `.expect`).
///
/// `k = n - 1` is safe by construction: it is only reached when `n != 0`, which
/// is exactly `Nat.succ`'s predecessor. That is the one place this emitter uses
/// bare subtraction rather than the checked form, and it is sound because the
/// branch condition establishes the precondition.
///
/// Like `ite`, this is allowed to carry a universe level: `motive` is
/// instantiated at the scalar result type, so emission stays monomorphic.
pub(super) fn translate_nat_cases(
    args: &[&Expr],
    expected: ScalarTy,
    params: &[(String, ScalarTy)],
) -> Result<Rendered, RustEmitError> {
    let [_motive, scrut, zero_case, succ_case] = args else {
        return Err(RustEmitError::Unsupported(format!(
            "`Nat.casesOn` applied to {} argument(s); expected 4 (motive, n, zero, succ)",
            args.len()
        )));
    };

    let ExprKind::Lam(_, _, succ_body) = strip_mdata(succ_case).kind() else {
        return Err(RustEmitError::Unsupported(format!(
            "`Nat.casesOn`'s successor branch is a {}, not a lambda binding the \
             predecessor",
            form_name(strip_mdata(succ_case).kind())
        )));
    };

    let n = translate(scrut, ScalarTy::Nat, params)?;
    let z = translate(zero_case, expected, params)?;

    // Synthetic names keyed on binder depth: they cannot collide with the
    // Lean-derived parameter names, which are alphabetic.
    let depth = params.len();
    let scrut_name = format!("__n{depth}");
    let pred_name = format!("__k{depth}");
    let mut inner = params.to_vec();
    inner.push((pred_name.clone(), ScalarTy::Nat));
    let succ = translate(succ_body, expected, &inner)?;

    Ok(Rendered::atom(format!(
        "{{ let {scrut_name} = {}; if {scrut_name} == 0 {{ {} }} else {{ let {pred_name} = \
         {scrut_name} - 1; {} }} }}",
        n.text, z.text, succ.text
    )))
}

/// A BETA-REDEX head: `(fun x₁ … xₙ => body) a₁ … aₙ` → let-bindings.
///
/// This is the shape match elaboration produces for a SHARED DEFAULT arm.
/// Measured on the three-arm `match i with | 0 => 1 | 1 => 2 | _ => 0`: the
/// `_` arm arrives inside the successor branch as `(fun _ : Nat => 0) k`, an
/// application whose head is a lambda rather than a constant. (The L5CNF
/// lowering refuses exactly this term — `Application head: Lam` — which is why
/// the C lane cannot extract it today; this emitter translates the kernel
/// value directly, so it handles the redex itself.)
///
/// Emitted as let-bindings rather than textual substitution: an argument can
/// be an arbitrary expression, and binding it once neither duplicates its work
/// nor its overflow `.expect` — same discipline as the scrutinee binding in
/// [`translate_nat_cases`].
///
/// ```text
/// { let x1 = <a1>; …; let xn = <an>; <body> }
/// ```
///
/// Fail-closed, per the v1 contract:
/// * every consumed binder's domain must be a v1 scalar (the `let` needs a
///   monomorphic Rust type);
/// * more arguments than leading lambdas refuses — the residue would need
///   substitution into an unknown head;
/// * leftover lambdas after the arguments run out refuse — a function-valued
///   expression cannot sit at a scalar result type.
pub(super) fn translate_beta_redex(
    head: &Expr,
    args: &[&Expr],
    expected: ScalarTy,
    params: &[(String, ScalarTy)],
) -> Result<Rendered, RustEmitError> {
    let mut lets: Vec<String> = Vec::new();
    let mut inner = params.to_vec();
    // Synthetic names keyed on the OUTER binder depth plus the binder's
    // position; `__r` is reserved to this helper, so they cannot collide with
    // Lean-derived parameter names (alphabetic) or the other helpers' names.
    let depth = params.len();
    let mut cursor = head;
    for (j, arg) in args.iter().enumerate() {
        let ExprKind::Lam(_, dom, body) = strip_mdata(cursor).kind() else {
            return Err(RustEmitError::Unsupported(format!(
                "beta-redex applies {} argument(s) to only {j} lambda binder(s); the \
                 v1 Rust backend does not substitute into a residual application",
                args.len()
            )));
        };
        let Some(ty) = ScalarTy::of(strip_mdata(dom)) else {
            return Err(RustEmitError::Unsupported(format!(
                "beta-redex binder {j} has a non-scalar domain (a {}); the v1 Rust \
                 backend binds redex arguments at v1 scalar types only",
                form_name(strip_mdata(dom).kind())
            )));
        };
        // The argument lives in the OUTER scope: it is translated against
        // `params`, never the extended scope — a redex argument cannot see the
        // binders it is being passed to.
        let rendered = translate(arg, ty, params)?;
        let name = format!("__r{depth}_{j}");
        lets.push(format!("let {name} = {};", rendered.text));
        inner.push((name, ty));
        cursor = body;
    }
    if matches!(strip_mdata(cursor).kind(), ExprKind::Lam(_, _, _)) {
        return Err(RustEmitError::Unsupported(
            "beta-redex is under-applied: lambda binders remain after the arguments \
             run out, so the expression is function-valued at a scalar result type"
                .to_string(),
        ));
    }
    let body = translate(cursor, expected, &inner)?;
    Ok(Rendered::atom(format!(
        "{{ {} {} }}",
        lets.join(" "),
        body.text
    )))
}

/// `ite α c inst t e` → `if <cond> { t } else { e }`.
///
/// This is the first CONTROL FLOW in the v1 Rust table. Lean elaborates
/// `if b then x else y` over a `Bool` through the `Decidable (b = true)`
/// coercion, so the recognized shape is
///
/// ```text
/// ite α (Eq Bool b Bool.true) (inst …) t e
/// ```
///
/// and the emitted condition is just `b`. Both branches are translated at the
/// SAME expected type, which is what keeps the emission monomorphic.
///
/// Deliberately narrow: any other decidable proposition (`Nat.decLt`, a
/// user-defined `Decidable`) REFUSES with the shape it actually saw, rather
/// than guessing a condition. A wrong branch condition is a silently wrong
/// program, and the differential battery would only catch it if a battery point
/// happened to straddle the branch.
pub(super) fn translate_ite(
    args: &[&Expr],
    expected: ScalarTy,
    params: &[(String, ScalarTy)],
) -> Result<Rendered, RustEmitError> {
    let [_alpha, cond, _inst, then_br, else_br] = args else {
        return Err(RustEmitError::Unsupported(format!(
            "`ite` applied to {} argument(s); expected 5 (α, c, inst, then, else)",
            args.len()
        )));
    };

    // Recognize `Eq Bool b Bool.true` (either orientation) and use `b`.
    let (eq_head, eq_args) = flatten_app(strip_mdata(cond));
    let cond_bool = match eq_head.kind() {
        ExprKind::Const(n, _) if n.to_string() == "Eq" && eq_args.len() == 3 => {
            let ty_is_bool = matches!(
                strip_mdata(eq_args[0]).kind(),
                ExprKind::Const(t, _) if t.to_string() == "Bool"
            );
            let is_true = |e: &Expr| matches!(strip_mdata(e).kind(), ExprKind::Const(t, _) if t.to_string() == "Bool.true");
            if !ty_is_bool {
                None
            } else if is_true(eq_args[2]) {
                Some(eq_args[1])
            } else if is_true(eq_args[1]) {
                Some(eq_args[2])
            } else {
                None
            }
        }
        _ => None,
    };
    let Some(cond_bool) = cond_bool else {
        return Err(RustEmitError::Unsupported(format!(
            "`ite` condition is `{}`, not a Bool decision (`b = true`); the v1 Rust \
             backend emits a branch only when the condition is a Bool it can name",
            form_name(strip_mdata(cond).kind())
        )));
    };

    let c = translate(cond_bool, ScalarTy::Bool, params)?;
    let t = translate(then_br, expected, params)?;
    let f = translate(else_br, expected, params)?;
    Ok(Rendered::atom(format!(
        "if {} {{ {} }} else {{ {} }}",
        c.text, t.text, f.text
    )))
}

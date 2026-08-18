// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Recursive-call rewriting with per-site decreasing proofs (WF phase 1).
//!
//! Rewrites every recursive call `f arg` in an elaborated body into
//! `rec arg h`, where `rec` is the `WellFounded.fix` fixpoint parameter and
//! `h : Nat.lt (measure arg) (measure param)` is a decreasing proof
//! synthesized at the call site by the discharge cascade in
//! [`super::decreasing`].
//!
//! The traversal opens every binder it walks under (pushing the hypothesis
//! into the elaboration context) so the discharge tactics see the call site's
//! full hypothesis set — e.g. the `h : 0 < n` bound by a `dite` branch.
//!
//! FAIL CLOSED: any shape this rewriter does not understand — a bare
//! first-class self-reference, a recursive call nested inside a recursive
//! argument, a call under an untraversed construct, or an undischargeable
//! obligation — returns [`WfReject`]. The caller converts that into the loud
//! `termination_by` diagnostic; nothing is ever papered over with `sorry`,
//! an axiom, or an unchecked declaration. As a backstop the caller re-checks
//! that no self-reference survives the rewrite, and the kernel re-checks the
//! full definition at registration.

use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind, FVarId};

use super::encoding::contains_fvar;
use super::measure_wf::measure_at;
use super::ElabCtx;

/// Why the call-site rewrite refused to compile the definition.
///
/// Deliberately a plain reason string: it is embedded into the canonical
/// fail-closed `termination_by` diagnostic by the caller, never surfaced raw.
pub(super) struct WfReject(pub(super) String);

impl WfReject {
    fn new(reason: impl Into<String>) -> Self {
        WfReject(reason.into())
    }
}

/// Everything the call-site rewriter needs to know about the definition.
pub(super) struct RecCallRewrite<'m> {
    /// FVar the elaborated body uses for self-references.
    pub(super) func_fvar: FVarId,
    /// FVar of the `WellFounded.fix` fixpoint parameter `rec`.
    pub(super) rec_fvar: FVarId,
    /// FVar of the recursion parameter `x`.
    pub(super) param_fvar: FVarId,
    /// The elaborated measure, expressed in terms of `param_fvar`.
    pub(super) measure_expr: &'m Expr,
}

impl ElabCtx<'_> {
    /// Rewrite recursive calls `f arg` to `rec arg proof`, synthesizing each
    /// decreasing proof. See the module docs for the fail-closed contract.
    pub(super) fn transform_rec_calls_proved(
        &mut self,
        e: &Expr,
        cfg: &RecCallRewrite<'_>,
    ) -> Result<Expr, WfReject> {
        // Fast path: no self-reference below this node — nothing to rewrite.
        if !contains_fvar(e, cfg.func_fvar) {
            return Ok(e.clone());
        }
        match e.kind() {
            ExprKind::FVar(_) => Err(WfReject::new(
                "the function is referenced without an argument \
                 (first-class self-reference)",
            )),
            ExprKind::App(..) => self.rewrite_app_spine(e, cfg),
            ExprKind::Lam(bd, ty, body) => {
                if contains_fvar(ty, cfg.func_fvar) {
                    return Err(WfReject::new(
                        "a self-reference occurs inside a binder type",
                    ));
                }
                let hyp_name = format!("_wf_hyp{}", self.locals.len());
                let fv = self.push_local(hyp_name, Expr::clone(ty));
                let opened = body.instantiate(&Expr::fvar(fv));
                let rewritten = self.transform_rec_calls_proved(&opened, cfg);
                self.pop_local();
                let rewritten = rewritten?;
                Ok(Expr::lam(*bd, Expr::clone(ty), rewritten.abstract_fvar(fv)))
            }
            ExprKind::Let(name, ty, val, body, non_dep) => {
                if contains_fvar(ty, cfg.func_fvar) {
                    return Err(WfReject::new(
                        "a self-reference occurs inside a let-binding type",
                    ));
                }
                let new_val = self.transform_rec_calls_proved(val, cfg)?;
                let fv = self.push_local(name.to_string(), Expr::clone(ty));
                let opened = body.instantiate(&Expr::fvar(fv));
                let rewritten = self.transform_rec_calls_proved(&opened, cfg);
                self.pop_local();
                let rewritten = rewritten?;
                Ok(Expr::let_named(
                    name.clone(),
                    Expr::clone(ty),
                    new_val,
                    rewritten.abstract_fvar(fv),
                    *non_dep,
                ))
            }
            ExprKind::MData(m, inner) => Ok(Expr::mdata(
                m.clone(),
                self.transform_rec_calls_proved(inner, cfg)?,
            )),
            ExprKind::Proj(s, i, inner) => Ok(Expr::proj(
                s.clone(),
                *i,
                self.transform_rec_calls_proved(inner, cfg)?,
            )),
            // Anything else that still CONTAINS a self-reference (Pi bodies,
            // extension nodes, …) is out of scope for phase 1: refuse loudly
            // rather than emit a term the kernel would reject with an
            // internal message — or worse, silently drop the reference.
            _ => Err(WfReject::new(
                "a recursive call occurs under a construct the well-founded \
                 lowering does not yet traverse",
            )),
        }
    }

    /// Rewrite an application spine that contains a self-reference.
    fn rewrite_app_spine(&mut self, e: &Expr, cfg: &RecCallRewrite<'_>) -> Result<Expr, WfReject> {
        // Decompose the spine `head a₁ … aₙ` (source order).
        let head = e.get_app_fn().clone();
        let args: Vec<Expr> = e.get_app_args().into_iter().map(Expr::clone).collect();

        let head_is_rec_call = matches!(head.kind(), ExprKind::FVar(id) if *id == cfg.func_fvar);
        if !head_is_rec_call {
            let mut out = self.transform_rec_calls_proved(&head, cfg)?;
            for a in &args {
                out = Expr::app(out, self.transform_rec_calls_proved(a, cfg)?);
            }
            return Ok(out);
        }

        // A genuine call site `f arg extra…`.
        let Some(arg) = args.first() else {
            // Unreachable (an App spine has at least one argument), but refuse
            // rather than panic if it ever is.
            return Err(WfReject::new(
                "internal: application spine with no arguments",
            ));
        };
        if contains_fvar(arg, cfg.func_fvar) {
            return Err(WfReject::new(
                "a recursive call occurs inside the argument of another \
                 recursive call",
            ));
        }

        // Obligation: Nat.lt (measure arg) (measure param).
        let goal = Expr::apps(
            Expr::const_(Name::from_string("Nat.lt"), vec![]),
            [
                measure_at(cfg.measure_expr, cfg.param_fvar, arg),
                cfg.measure_expr.clone(),
            ],
        );
        let proof = self.discharge_decreasing_goal(&goal).ok_or_else(|| {
            WfReject::new(
                "no decreasing proof was found for a recursive call site \
                 (tried: hypothesis lookup, Nat.sub_lt, omega, simp_arith). \
                 Consider restating the recursion so the decrease follows \
                 from a hypothesis in scope",
            )
        })?;

        let mut out = Expr::apps(Expr::fvar(cfg.rec_fvar), [arg.clone(), proof]);
        for extra in &args[1..] {
            out = Expr::app(out, self.transform_rec_calls_proved(extra, cfg)?);
        }
        Ok(out)
    }
}

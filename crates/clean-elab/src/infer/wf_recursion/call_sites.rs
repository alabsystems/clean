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
use clean_kernel::{BinderInfo, Expr, ExprKind, FVarId};

use super::decreasing::nat_lt_goal;
use super::encoding::contains_fvar;
use super::measure_wf::measure_at;
use super::ElabCtx;

/// Rewrite a non-dependent `@ite.{u} α c inst t e` into the dependent
/// `@dite.{u} α c inst (fun _ : c => t) (fun _ : ¬c => e)`.
///
/// # Why this exists
///
/// A non-dependent `ite` binds NO hypothesis, so the branches of
/// `if b == 0 then a else gcd b (a % b)` are elaborated in a context where
/// nothing at all is known about `b` — and the decrease `a % b < b` is
/// genuinely underivable there, not merely hard. `dite`'s branches ARE
/// functions of the decision, so after this rewrite the traversal's `Lam` arm
/// pushes `_ : ¬(b == 0 = true)` into scope exactly where the recursive call
/// sits, and the discharge cascade can reach for it.
///
/// This is Lean 4's own preprocessing step (`Lean.Elab.PreDefinition.WF.Ite`),
/// and it is applied HERE — inside the well-founded lowering, on the already
/// elaborated body — rather than as a source-level normalization, so it cannot
/// change the meaning of any non-recursive definition.
///
/// # Faithfulness
///
/// The rewrite is **definitional**, not merely sound. Both `ite` and `dite` are
/// `is_reducible` definitions (`clean-kernel/src/env/logic_ite.rs`) that δ-unfold
/// to the SAME application:
///
/// ```text
/// ite  c t e                    ≡ Decidable.casesOn c (fun _ => α) inst (fun _ : ¬c => e) (fun _ : c => t)
/// dite c (fun _ => t) (fun _ => e) ≡ Decidable.casesOn c (fun _ => α) inst (fun _ : ¬c => e) (fun _ : c => t)
/// ```
///
/// so the two terms are convertible by δ alone, with no propositional step and
/// no appeal to `propext` or funext. Asserted against the kernel rather than
/// argued in prose: `r4_bool_test_bridge_probes::probe_q2_*` registers
/// `(if b == 0 then a else a % b) = dite ((b == 0) = true) (fun _ => a) (fun _ => a % b) := rfl`,
/// which only type-checks because the kernel agrees.
///
/// Consequently the emitted definition's VALUE is def-eq to what the ordinary
/// elaboration produces — `gcd 12 18` still reduces to `6` by `rfl` — and the
/// kernel re-checks the whole definition at `add_decl` regardless. Returns
/// `None` for anything that is not a saturated `ite` spine; a spine with extra
/// arguments (an `ite` at a function type, applied) keeps them, since
/// `(ite c t e) x ≡ (dite c (fun _ => t) (fun _ => e)) x` by the same identity.
fn ite_to_dite(e: &Expr) -> Option<Expr> {
    let head = e.get_app_fn();
    let ExprKind::Const(name, levels) = head.kind() else {
        return None;
    };
    if *name != Name::from_string("ite") {
        return None;
    }
    let args = e.get_app_args();
    if args.len() < 5 {
        // A partially-applied `ite` has no branches to open; leave it alone.
        return None;
    }
    let (alpha, cond, inst) = (args[0], args[1], args[2]);
    let (then_v, else_v) = (args[3], args[4]);
    let not_cond = Expr::app(
        Expr::const_(Name::from_string("Not"), vec![]),
        Expr::clone(cond),
    );
    // The branches do not mention the decision, so each is a constant
    // function: the bodies are locally closed here (the traversal opens every
    // binder it walks under into an fvar), so no de Bruijn lifting is needed.
    let then_lam = Expr::lam(BinderInfo::Default, Expr::clone(cond), Expr::clone(then_v));
    let else_lam = Expr::lam(BinderInfo::Default, not_cond, Expr::clone(else_v));
    let mut out = Expr::apps(
        Expr::const_(Name::from_string("dite"), levels.clone()),
        [
            Expr::clone(alpha),
            Expr::clone(cond),
            Expr::clone(inst),
            then_lam,
            else_lam,
        ],
    );
    for extra in &args[5..] {
        out = Expr::app(out, Expr::clone(extra));
    }
    Some(out)
}

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

/// Which lowering the call site is being rewritten for.
///
/// Both variants owe the SAME obligation — `Nat.lt (measure args)
/// (measure params)` — and both fail closed if it is not discharged. They
/// differ only in how `rec` is spelled, because the two lowerings put a
/// different thing at the front of the fix telescope.
pub(super) enum RecShape<'m> {
    /// The measure names ONE parameter, which IS the fix's major premise
    /// (`build_wf_definition`). `f a⃗ ↦ rec aᵢ prf (other args…)`.
    SoleParameter {
        /// FVar of the recursion parameter `x` — the one the measure names.
        param_fvar: FVarId,
        /// Its position in the source parameter list. The rewrite reads the
        /// decreasing argument from THIS position of every call spine and
        /// re-threads the remaining arguments after the decreasing proof.
        param_index: usize,
    },
    /// The measure mentions SEVERAL parameters, so the fix runs on the
    /// measure's VALUE and every parameter rides in the motive
    /// (`sum_measure::build_wf_sum_definition`). `f a⃗ ↦ rec m hm a⃗ prf`.
    MeasureValue {
        /// FVar of `hm : Nat.lt m n`, the hypothesis tying the current
        /// parameters' measure to the course-of-values bound.
        hm_fvar: FVarId,
        /// Every source parameter, in order, with its type — the domain of
        /// the simultaneous substitution that builds each obligation.
        params: &'m [(FVarId, Expr)],
    },
}

/// Everything the call-site rewriter needs to know about the definition.
pub(super) struct RecCallRewrite<'m> {
    /// FVar the elaborated body uses for self-references.
    pub(super) func_fvar: FVarId,
    /// FVar of the `WellFounded.fix` fixpoint parameter `rec`.
    pub(super) rec_fvar: FVarId,
    /// Number of source parameters. A recursive call must supply all of them
    /// (a partial self-application has no `rec` spelling and is refused).
    pub(super) arity: usize,
    /// The elaborated measure, expressed in terms of the parameters' FVars.
    pub(super) measure_expr: &'m Expr,
    /// Which of the two lowerings is being built.
    pub(super) shape: RecShape<'m>,
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
            ExprKind::App(..) => {
                // A non-dependent `ite` whose branches hold the recursion binds
                // nothing, so normalize it to the dependent `dite` FIRST — see
                // `ite_to_dite` for the (definitional) faithfulness argument.
                // The result is a `dite` spine, never an `ite`, so this cannot
                // loop.
                //
                // Guarded on `dite`/`Not` actually being registered: a sparse
                // environment that has `ite` but not `dite` must keep the term
                // it already had rather than be handed one naming a constant
                // the kernel would reject at `add_decl`. `with_prelude` always
                // has both.
                if self.env.get_const(&Name::from_string("dite")).is_some()
                    && self.env.get_const(&Name::from_string("Not")).is_some()
                {
                    if let Some(dependent) = ite_to_dite(e) {
                        return self.transform_rec_calls_proved(&dependent, cfg);
                    }
                }
                self.rewrite_app_spine(e, cfg)
            }
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

        // A genuine call site `f a₀ … aₙ₋₁ extra…`. Every source parameter
        // must be supplied: `rec` abstracts only the recursion parameter, so
        // a partially-applied self-call has no spelling here.
        if args.len() < cfg.arity {
            return Err(WfReject::new(format!(
                "a recursive call supplies {} argument(s) but the definition \
                 has {} parameter(s); a partially-applied self-call is not \
                 lowered. Consider applying it to all of its parameters",
                args.len(),
                cfg.arity
            )));
        }
        let mut out = match &cfg.shape {
            RecShape::SoleParameter {
                param_fvar,
                param_index,
            } => self.rewrite_sole_parameter_call(cfg, &args, *param_fvar, *param_index)?,
            RecShape::MeasureValue { hm_fvar, params } => {
                self.rewrite_measure_value_call(cfg, &args, *hm_fvar, params)?
            }
        };
        for extra in &args[cfg.arity..] {
            out = Expr::app(out, self.transform_rec_calls_proved(extra, cfg)?);
        }
        Ok(out)
    }

    /// `f a⃗ ↦ rec aᵢ prf (other args…)` — the measure names ONE parameter,
    /// which is the fix's major premise.
    fn rewrite_sole_parameter_call(
        &mut self,
        cfg: &RecCallRewrite<'_>,
        args: &[Expr],
        param_fvar: FVarId,
        param_index: usize,
    ) -> Result<Expr, WfReject> {
        let Some(arg) = args.get(param_index) else {
            // Unreachable given the caller's arity check, but refuse rather
            // than panic if it ever is.
            return Err(WfReject::new(
                "internal: application spine shorter than the parameter list",
            ));
        };
        if contains_fvar(arg, cfg.func_fvar) {
            return Err(WfReject::new(
                "a recursive call occurs inside the argument of another \
                 recursive call",
            ));
        }

        // Obligation: Nat.lt (measure arg) (measure param). The measure names
        // ONE parameter, so this stays the phase-1 single-parameter goal no
        // matter how wide the signature is.
        let goal = nat_lt_goal(
            measure_at(cfg.measure_expr, param_fvar, arg),
            cfg.measure_expr.clone(),
        );
        let proof = self
            .discharge_decreasing_goal(&goal)
            .ok_or_else(|| undischarged(""))?;

        // `rec argᵢ proof : C argᵢ = Π (others) → ret`, so the remaining
        // source arguments follow the proof in their ORIGINAL relative order
        // — that is the order the motive re-bound them in.
        let mut out = Expr::apps(Expr::fvar(cfg.rec_fvar), [arg.clone(), proof]);
        for (index, other) in args.iter().enumerate().take(cfg.arity) {
            if index == param_index {
                continue;
            }
            out = Expr::app(out, self.transform_rec_calls_proved(other, cfg)?);
        }
        Ok(out)
    }

    /// `f a⃗ ↦ rec m hm a⃗ prf` — the measure mentions SEVERAL parameters, so
    /// the fix runs on the measure's VALUE (`sum_measure`).
    ///
    /// `rec m hm : Π p⃗', Nat.lt m[p⃗'] m → ret`, so every source argument is
    /// supplied in order and the decreasing proof comes LAST — the mirror
    /// image of the sole-parameter spelling, and the reason the two are
    /// separate functions rather than one with a flag.
    fn rewrite_measure_value_call(
        &mut self,
        cfg: &RecCallRewrite<'_>,
        args: &[Expr],
        hm_fvar: FVarId,
        params: &[(FVarId, Expr)],
    ) -> Result<Expr, WfReject> {
        // With a multi-parameter measure EVERY source argument feeds the
        // obligation, so a nested self-call in any of them would put an
        // unrewritten self-reference inside the goal. The sole-parameter path
        // only has to refuse this at the measure's own position; here it is
        // all of them.
        for (index, arg) in args.iter().enumerate().take(cfg.arity) {
            if contains_fvar(arg, cfg.func_fvar) {
                return Err(WfReject::new(format!(
                    "a recursive call occurs inside argument #{index} of \
                     another recursive call. With a measure over several \
                     parameters every argument feeds the decrease, so the \
                     inner call cannot be lowered there. Ways forward: \
                     (1) bind the inner call with `let` before the outer one; \
                     (2) restate the recursion so the measure names ONE \
                     parameter"
                )));
            }
        }

        let call_args: Vec<Expr> = args[..cfg.arity].to_vec();
        // Obligation: Nat.lt (measure args) (measure params). The substitution
        // is SIMULTANEOUS — see `measure_shape::measure_at_args`.
        let at_args = self.measure_at_args(cfg.measure_expr, params, &call_args);
        let goal = nat_lt_goal(at_args, cfg.measure_expr.clone());
        let proof = self.discharge_decreasing_goal(&goal).ok_or_else(|| {
            undischarged(
                ". The measure mentions several parameters, so the decrease \
                 must hold for the SUM: check that every branch guards the \
                 case where a summand is already zero",
            )
        })?;

        let mut out = Expr::apps(
            Expr::fvar(cfg.rec_fvar),
            [cfg.measure_expr.clone(), Expr::fvar(hm_fvar)],
        );
        for arg in call_args {
            out = Expr::app(out, arg);
        }
        Ok(Expr::app(out, proof))
    }
}

/// The one refusal both spellings share, with the fix and its options
/// (v7/D3). `extra` appends a shape-specific hint.
fn undischarged(extra: &str) -> WfReject {
    WfReject::new(format!(
        "no decreasing proof was found for a recursive call site (tried: \
         hypothesis lookup, Nat.sub_lt, Nat.mod_lt — each also with positivity \
         derived via Nat.pos_of_ne_zero from a `≠ 0` or a Bool `== 0` test — \
         then sum congruence via Nat.add_lt_add_left/_right/Nat.add_lt_add, \
         then omega, simp_arith, then the truncated-subtraction lane: sum \
         positivity, the strict linear residual, and a case split on \
         Nat.le_total that substitutes the larger parameter). Consider \
         restating the recursion so the decrease follows from a hypothesis in \
         scope{extra}"
    ))
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof-producing WHNF reduction.
//!
//! Extends the standard WHNF algorithm to optionally produce Lean proof terms
//! witnessing each reduction step. Each step produces a proof of type
//! `@Eq α input output`, and multiple steps are chained via `Eq.trans`.
//!
//! This is "Approach 2" from `designs/2026-02-01-computational-equality-proofs.md`.
//!
//! Part of #685.

use crate::expr::{stack_safe, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;
use crate::tc::TypeChecker;

/// Pre-interned names for proof term construction.
mod names {
    use crate::name::Name;
    use std::sync::LazyLock;

    pub static EQ_REFL: LazyLock<Name> = LazyLock::new(|| Name::from_string("Eq.refl"));
    pub static EQ_TRANS: LazyLock<Name> = LazyLock::new(|| Name::from_string("Eq.trans"));
    pub static EQ_SYMM: LazyLock<Name> = LazyLock::new(|| Name::from_string("Eq.symm"));
    pub static EQ_SUBST: LazyLock<Name> = LazyLock::new(|| Name::from_string("Eq.subst"));
    pub static CONGR_ARG: LazyLock<Name> = LazyLock::new(|| Name::from_string("congrArg"));
    pub static CONGR_FUN: LazyLock<Name> = LazyLock::new(|| Name::from_string("congrFun'"));
    pub static CONGR: LazyLock<Name> = LazyLock::new(|| Name::from_string("congr"));
}

/// What kind of reduction was applied in a proof-producing WHNF step.
#[derive(Debug, Clone)]
pub enum WhnfProofStep {
    /// Beta reduction: `(fun x => body) arg` ~> `body[arg/x]`
    Beta,
    /// Delta reduction: unfold constant definition
    Delta(Name),
    /// Zeta reduction: `let x := val in body` ~> `body[val/x]`
    Zeta,
    /// Iota reduction: recursor computation rule
    Iota,
    /// Projection reduction: `struct.field` ~> `value`
    Proj { struct_name: Name, idx: u32 },
    /// Transparent stripping: MData wrappers removed
    Transparent,
}

/// Arguments for `congrArg` proof construction.
pub struct CongrArgArgs {
    /// Universe level of domain type `α`
    pub u: Level,
    /// Universe level of codomain type `β`
    pub v: Level,
    /// Domain type `α`
    pub alpha: Expr,
    /// Codomain type `β`
    pub beta: Expr,
    /// Left value `a₁`
    pub a1: Expr,
    /// Right value `a₂`
    pub a2: Expr,
    /// Function `f : α → β`
    pub f: Expr,
    /// Proof `h : @Eq α a₁ a₂`
    pub h: Expr,
}

/// Constructs `@Eq` proof terms as Lean kernel `Expr` values.
pub struct EqProofBuilder;

impl EqProofBuilder {
    /// Construct `@Eq.refl.{u} α a : @Eq.{u} α a a`
    ///
    /// For single-step definitional reductions, the kernel verifies
    /// `@Eq.refl α reduced : @Eq α original reduced` because
    /// `original` is definitionally equal to `reduced` by one step.
    pub fn mk_eq_refl(u: Level, alpha: Expr, a: Expr) -> Expr {
        let eq_refl = Expr::const_(names::EQ_REFL.clone(), vec![u]);
        Expr::apps(eq_refl, [alpha, a])
    }

    /// Construct `@Eq.trans.{u} α a b c hab hbc : @Eq.{u} α a c`
    pub fn mk_eq_trans(
        u: Level,
        alpha: Expr,
        a: Expr,
        b: Expr,
        c: Expr,
        hab: Expr,
        hbc: Expr,
    ) -> Expr {
        let eq_trans = Expr::const_(names::EQ_TRANS.clone(), vec![u]);
        Expr::apps(eq_trans, [alpha, a, b, c, hab, hbc])
    }

    /// Construct `@Eq.symm.{u} α a b h : @Eq.{u} α b a`
    ///
    /// Given `h : @Eq α a b`, produces a proof of `@Eq α b a`.
    pub fn mk_eq_symm(u: Level, alpha: Expr, a: Expr, b: Expr, h: Expr) -> Expr {
        let eq_symm = Expr::const_(names::EQ_SYMM.clone(), vec![u]);
        Expr::apps(eq_symm, [alpha, a, b, h])
    }

    /// Construct `@congrArg.{u,v} α β a₁ a₂ f h : @Eq β (f a₁) (f a₂)`
    pub fn mk_congr_arg(args: CongrArgArgs) -> Expr {
        let congr_arg = Expr::const_(names::CONGR_ARG.clone(), vec![args.u, args.v]);
        Expr::apps(
            congr_arg,
            [args.alpha, args.beta, args.a1, args.a2, args.f, args.h],
        )
    }

    /// Construct `@congrFun'.{u,v} α β f g h a : @Eq β (f a) (g a)`
    ///
    /// Given `h : f = g` and `a : α`, produces proof of `f a = g a`.
    #[allow(clippy::too_many_arguments)]
    pub fn mk_congr_fun(
        u: Level,
        v: Level,
        alpha: Expr,
        beta: Expr,
        f: Expr,
        g: Expr,
        h: Expr,
        a: Expr,
    ) -> Expr {
        let congr_fun = Expr::const_(names::CONGR_FUN.clone(), vec![u, v]);
        Expr::apps(congr_fun, [alpha, beta, f, g, h, a])
    }

    /// Construct `@congr.{u,v} α β f₁ f₂ a₁ a₂ hf ha : @Eq β (f₁ a₁) (f₂ a₂)`
    ///
    /// Given `hf : f₁ = f₂` and `ha : a₁ = a₂`, produces proof of `f₁ a₁ = f₂ a₂`.
    #[allow(clippy::too_many_arguments)]
    pub fn mk_congr(
        u: Level,
        v: Level,
        alpha: Expr,
        beta: Expr,
        f1: Expr,
        f2: Expr,
        a1: Expr,
        a2: Expr,
        hf: Expr,
        ha: Expr,
    ) -> Expr {
        let congr = Expr::const_(names::CONGR.clone(), vec![u, v]);
        Expr::apps(congr, [alpha, beta, f1, f2, a1, a2, hf, ha])
    }

    /// Construct `@Eq.subst.{u} α motive a b h m : motive b`
    ///
    /// Given `h : a = b` and `m : motive a`, produces proof of `motive b`.
    pub fn mk_eq_subst(
        u: Level,
        alpha: Expr,
        motive: Expr,
        a: Expr,
        b: Expr,
        h: Expr,
        m: Expr,
    ) -> Expr {
        let eq_subst = Expr::const_(names::EQ_SUBST.clone(), vec![u]);
        Expr::apps(eq_subst, [alpha, motive, a, b, h, m])
    }

    /// Chain proof steps into a single proof via `Eq.trans`.
    ///
    /// Each entry is `(result_expr, proof_of_prev_eq_result)`.
    /// Returns the combined proof of `original = last_result`.
    pub(crate) fn chain_proofs(
        u: Level,
        alpha: Expr,
        original: Expr,
        steps: Vec<(Expr, Expr)>,
    ) -> Expr {
        assert!(!steps.is_empty(), "chain_proofs requires at least one step");
        let mut iter = steps.into_iter();
        let (first_result, first_proof) = iter
            .next()
            .expect("invariant: steps is non-empty (checked by assert above)");

        let start = original;
        let mut current_expr = first_result;
        let mut current_proof = first_proof;

        for (result, step_proof) in iter {
            let prev = current_expr;
            current_proof = Self::mk_eq_trans(
                u.clone(),
                alpha.clone(),
                start.clone(),
                prev,
                result.clone(),
                current_proof,
                step_proof,
            );
            current_expr = result;
        }

        current_proof
    }
}

/// Result of proof-producing WHNF.
#[derive(Debug, Clone)]
pub struct WhnfWithProof {
    /// The reduced expression (same as regular `whnf` would produce).
    pub result: Expr,
    /// Proof term of type `@Eq type_ original result`, or `None` if no reduction.
    pub proof: Option<Expr>,
    /// Reduction steps applied (for diagnostics).
    pub steps: Vec<WhnfProofStep>,
}

impl<'env> TypeChecker<'env> {
    /// Compute WHNF and produce a proof term witnessing the reduction.
    ///
    /// REQUIRES: `e : type_` and `type_ : Sort u`
    /// ENSURES: `result` equals `self.whnf(e)`
    /// ENSURES: If `proof = Some(p)`, then `p : @Eq type_ e result`
    pub fn whnf_with_proof(&self, e: &Expr, type_: &Expr, u: Level) -> WhnfWithProof {
        stack_safe(|| self.whnf_with_proof_inner(e, type_, u))
    }

    fn whnf_with_proof_inner(&self, e: &Expr, type_: &Expr, u: Level) -> WhnfWithProof {
        let mut steps_acc: Vec<(Expr, Expr, WhnfProofStep)> = Vec::new();
        let result = self.whnf_step_by_step(e, type_, &u, &mut steps_acc);

        if steps_acc.is_empty() {
            return WhnfWithProof {
                result,
                proof: None,
                steps: Vec::new(),
            };
        }

        let proof_steps: Vec<(Expr, Expr)> = steps_acc
            .iter()
            .map(|(result_expr, proof, _)| (result_expr.clone(), proof.clone()))
            .collect();
        let step_kinds: Vec<WhnfProofStep> =
            steps_acc.into_iter().map(|(_, _, kind)| kind).collect();
        let proof = EqProofBuilder::chain_proofs(u, type_.clone(), e.clone(), proof_steps);

        WhnfWithProof {
            result,
            proof: Some(proof),
            steps: step_kinds,
        }
    }

    /// Step-by-step WHNF that records each reduction as a proof step.
    fn whnf_step_by_step(
        &self,
        e: &Expr,
        type_: &Expr,
        u: &Level,
        steps: &mut Vec<(Expr, Expr, WhnfProofStep)>,
    ) -> Expr {
        match &e.kind {
            ExprKind::App(f, a) => {
                let f_whnf = self.whnf_impl(f);
                if let ExprKind::Lam(_, _, body) = &f_whnf.kind {
                    // Beta reduction: (fun x => body) arg ~> body[arg/x]
                    // When f itself was reduced (delta) before beta, we lump both
                    // into one step. The kernel verifies via delta+beta def-eq.
                    let reduced = body.instantiate(a);
                    let proof =
                        EqProofBuilder::mk_eq_refl(u.clone(), type_.clone(), reduced.clone());
                    steps.push((reduced.clone(), proof, WhnfProofStep::Beta));
                    self.whnf_step_by_step(&reduced, type_, u, steps)
                } else {
                    let head_changed = f_whnf != **f;
                    let app = if head_changed {
                        Expr::from_kind(ExprKind::App(std::sync::Arc::new(f_whnf), a.clone()))
                    } else {
                        e.clone()
                    };
                    if let Some(reduced) = self.try_iota_reduction(&app, true) {
                        // Iota: record one step covering head reduction + iota
                        let proof =
                            EqProofBuilder::mk_eq_refl(u.clone(), type_.clone(), reduced.clone());
                        steps.push((reduced.clone(), proof, WhnfProofStep::Iota));
                        self.whnf_step_by_step(&reduced, type_, u, steps)
                    } else if let Some(reduced) = self.try_quot_reduction(&app, true) {
                        let proof =
                            EqProofBuilder::mk_eq_refl(u.clone(), type_.clone(), reduced.clone());
                        steps.push((reduced.clone(), proof, WhnfProofStep::Iota));
                        self.whnf_step_by_step(&reduced, type_, u, steps)
                    } else if head_changed {
                        // Head reduced but no top-level reduction applied.
                        // Record the head reduction as a delta step so the proof
                        // chain covers App(f, a) → App(f_whnf, a).
                        let proof =
                            EqProofBuilder::mk_eq_refl(u.clone(), type_.clone(), app.clone());
                        steps.push((app.clone(), proof, WhnfProofStep::Delta(Name::anon())));
                        app
                    } else {
                        app
                    }
                }
            }
            ExprKind::Let(_, _, val, body, _) => {
                let reduced = body.instantiate(val);
                let proof = EqProofBuilder::mk_eq_refl(u.clone(), type_.clone(), reduced.clone());
                steps.push((reduced.clone(), proof, WhnfProofStep::Zeta));
                self.whnf_step_by_step(&reduced, type_, u, steps)
            }
            ExprKind::Const(name, levels) => {
                if let Some(val) = self.env.unfold_with_transparency(
                    name,
                    levels,
                    crate::env::TransparencyMode::Default,
                ) {
                    let proof = EqProofBuilder::mk_eq_refl(u.clone(), type_.clone(), val.clone());
                    steps.push((val.clone(), proof, WhnfProofStep::Delta(name.clone())));
                    self.whnf_step_by_step(&val, type_, u, steps)
                } else {
                    e.clone()
                }
            }
            ExprKind::FVar(id) => {
                let val_opt = self.ctx.borrow().get(*id).and_then(|d| d.value.clone());
                if let Some(val) = val_opt {
                    let proof = EqProofBuilder::mk_eq_refl(u.clone(), type_.clone(), val.clone());
                    steps.push((val.clone(), proof, WhnfProofStep::Zeta));
                    self.whnf_step_by_step(&val, type_, u, steps)
                } else {
                    e.clone()
                }
            }
            ExprKind::Proj(struct_name, idx, _) => {
                let reduced = self.whnf(e);
                if reduced != *e {
                    let proof =
                        EqProofBuilder::mk_eq_refl(u.clone(), type_.clone(), reduced.clone());
                    steps.push((
                        reduced.clone(),
                        proof,
                        WhnfProofStep::Proj {
                            struct_name: struct_name.clone(),
                            idx: *idx,
                        },
                    ));
                }
                reduced
            }
            ExprKind::MData(_, inner) => {
                // MData is definitionally transparent — stripping it
                // is a valid reduction step. Record it so the proof chain covers
                // the full path from `e` (wrapped) to the final result.
                if **inner != *e {
                    let proof = EqProofBuilder::mk_eq_refl(
                        u.clone(),
                        type_.clone(),
                        inner.as_ref().clone(),
                    );
                    steps.push((inner.as_ref().clone(), proof, WhnfProofStep::Transparent));
                }
                self.whnf_step_by_step(inner, type_, u, steps)
            }
            _ => e.clone(),
        }
    }
}

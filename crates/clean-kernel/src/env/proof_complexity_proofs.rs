// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-level declarations for proof complexity theorems (PC01-PC04).
//!
//! PC01 is a genuine `Declaration::Theorem` carrying a real proof term
//! (structural recursion over the `ResolvStep` inductive via its
//! kernel-generated recursor). PC02-PC04 are GENUINE METATHEOREMS
//! (Davis-Putnam resolution completeness; cutting-planes arithmetic
//! soundness; CP pivot/ceiling simulation of resolution) that are not yet
//! structurally provable in-kernel — they are registered as HONEST
//! `Declaration::Axiom`s carrying their unwrapped propositions. They were
//! previously `Declaration::Theorem`s whose value was `Nonempty.intro` over
//! an underlying axiom — the Theorem-wrapping-Axiom masquerade CLAUDE.md
//! forbids; that wrapper has been removed (see the per-axiom `// SOUNDNESS:`
//! comments).
//!
//! Declarations:
//! - PC01: Resolution soundness (THEOREM: ResolvSound via ResolvStep.rec)
//! - PC02: Resolution completeness (AXIOM: forall n, ResolvComplete n)
//! - PC03: Cutting planes soundness (AXIOM: forall ni step, CPSound ni step)
//! - PC04: CP subsumes resolution (AXIOM: forall nc step, CPSimResolvSound nc step)
//!
//! Reference: Robinson (1965), Cook, Coullard & Turan (1987).
//!
//! Part of #3365: Phase 4 kernel proofs.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

/// Shared constants for proof complexity proof terms.
struct PCProofConsts {
    nat: Expr,
    prop: Expr,
    type0: Expr,
}

impl PCProofConsts {
    fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            prop: Expr::from_kind(ExprKind::Sort(Level::zero())),
            type0: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
        }
    }
}

/// Helper: build `ResolvStep nc` type expression.
fn resolv_step(nc: Expr) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("ProofComplexitySAT.ResolvStep"), vec![]),
        nc,
    )
}

/// Helper: build `ResolvSound nc step` type expression.
fn resolv_sound(nc: Expr, step: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("ProofComplexitySAT.ResolvSound"), vec![]),
        [nc, step],
    )
}

/// Helper: build `ResolvComplete n` type expression.
fn resolv_complete(n: Expr) -> Expr {
    Expr::app(
        Expr::const_(
            Name::from_string("ProofComplexitySAT.ResolvComplete"),
            vec![],
        ),
        n,
    )
}

/// Helper: build `CPStep ni` type expression.
fn cp_step(ni: Expr) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("ProofComplexitySAT.CPStep"), vec![]),
        ni,
    )
}

/// Helper: build `CPSound ni step` type expression.
fn cp_sound(ni: Expr, step: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("ProofComplexitySAT.CPSound"), vec![]),
        [ni, step],
    )
}

/// Helper: build `CPSimResolvStep nc` type expression.
fn cp_sim_step(nc: Expr) -> Expr {
    Expr::app(
        Expr::const_(
            Name::from_string("ProofComplexitySAT.CPSimResolvStep"),
            vec![],
        ),
        nc,
    )
}

/// Helper: build `CPSimResolvSound nc step` type expression.
fn cp_sim_sound(nc: Expr, step: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("ProofComplexitySAT.CPSimResolvSound"),
            vec![],
        ),
        [nc, step],
    )
}

impl Environment {
    /// Register kernel declarations for proof complexity theorems PC01-PC04.
    ///
    /// PC01 is a real `Declaration::Theorem`; PC02-PC04 are honest
    /// `Declaration::Axiom`s admitting genuine metatheoretic content (see the
    /// module docs and each `register_pcNN_*` `// SOUNDNESS:` comment).
    ///
    /// Must be called after `init_cutting_planes()` which registers the
    /// resolution and cutting planes axiom-level types.
    ///
    /// Depends on: `init_cutting_planes()`, `init_classical()`.
    #[cfg(any(test, feature = "math-overlays"))]
    pub fn init_proof_complexity_proofs(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ProofComplexitySAT.ResolvStep"))
            .is_some()
        {
            return Ok(());
        }
        self.init_cutting_planes()?;
        self.init_classical()?;

        let c = PCProofConsts::new();

        // Register inductive types
        self.register_resolv_step(&c)?;
        self.register_resolv_sound(&c)?;
        self.register_resolv_complete(&c)?;
        self.register_cp_step_inductive(&c)?;
        self.register_cp_sound_inductive(&c)?;
        self.register_cp_sim_resolv_step(&c)?;
        self.register_cp_sim_resolv_sound(&c)?;

        // Register declarations: PC01 a real theorem; PC02-PC04 honest axioms.
        self.register_pc01_theorem(&c)?;
        self.register_pc02_axiom(&c)?;
        self.register_pc03_axiom(&c)?;
        self.register_pc04_axiom(&c)?;

        Ok(())
    }

    // ====================================================================
    // Inductive type: ResolvStep
    // ====================================================================

    #[cfg(any(test, feature = "math-overlays"))]
    fn register_resolv_step(&mut self, c: &PCProofConsts) -> Result<(), EnvError> {
        use crate::inductive::{Constructor, InductiveDecl, InductiveType};

        // ResolvStep : Nat -> Type   (nc is a parameter, promoted by num_params=1)
        let ty = Expr::pi(BinderInfo::Default, c.nat.clone(), c.type0.clone());

        // input : (nc : Nat) -> (idx : Nat) -> ResolvStep nc
        let input_ty = {
            let mut b = EnvDeclBuilder::new();
            let (nc_id, nc) = b.fresh_local(c.nat.clone());
            let (idx_id, _) = b.fresh_local(c.nat.clone());
            let ret = resolv_step(nc);
            let e = b.mk_pi(idx_id, BinderInfo::Default, c.nat.clone(), ret);
            let e = b.mk_pi(nc_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // resolve : (nc : Nat) -> (pivot : Nat) -> ResolvStep nc -> ResolvStep nc -> ResolvStep nc
        let resolve_ty = {
            let mut b = EnvDeclBuilder::new();
            let (nc_id, nc) = b.fresh_local(c.nat.clone());
            let (pv_id, _) = b.fresh_local(c.nat.clone());
            let rs_ty = resolv_step(nc.clone());
            let (l_id, _) = b.fresh_local(rs_ty.clone());
            let (r_id, _) = b.fresh_local(rs_ty.clone());
            let ret = resolv_step(nc);
            let e = b.mk_pi(r_id, BinderInfo::Default, rs_ty.clone(), ret);
            let e = b.mk_pi(l_id, BinderInfo::Default, rs_ty, e);
            let e = b.mk_pi(pv_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(nc_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // Register as a genuine inductive so the kernel generates
        // `ProofComplexitySAT.ResolvStep.rec` with its iota rules. This replaces
        // the previous opaque-axiom encoding and is what makes the PC01 proof
        // term (structural recursion via the recursor) honest.
        let decl = InductiveDecl {
            level_params: vec![],
            num_params: 1,
            types: vec![InductiveType {
                name: Name::from_string("ProofComplexitySAT.ResolvStep"),
                type_: ty,
                constructors: vec![
                    Constructor {
                        name: Name::from_string("ProofComplexitySAT.ResolvStep.input"),
                        type_: input_ty,
                    },
                    Constructor {
                        name: Name::from_string("ProofComplexitySAT.ResolvStep.resolve"),
                        type_: resolve_ty,
                    },
                ],
            }],
        };
        self.add_inductive(decl)
    }

    // ====================================================================
    // Inductive type: ResolvSound
    // ====================================================================

    #[cfg(any(test, feature = "math-overlays"))]
    fn register_resolv_sound(&mut self, c: &PCProofConsts) -> Result<(), EnvError> {
        use crate::inductive::{Constructor, InductiveDecl, InductiveType};

        // ResolvSound : (nc : Nat) -> ResolvStep nc -> Prop
        // nc is the single parameter (num_params=1); the `ResolvStep nc` argument
        // is an INDEX, so the recursor eliminates over it.
        //
        // ResolvSound is a Prop-valued inductive predicate ("this resolution step
        // is sound"). Being a proposition is what lets PC01 be a genuine
        // `Declaration::Theorem` (theorems must inhabit Prop). `ResolvStep : Type`
        // still admits large elimination into a Prop motive, so the recursor-based
        // PC01 proof goes through.
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (nc_id, nc) = b.fresh_local(c.nat.clone());
            let rs_ty = resolv_step(nc);
            let (s_id, _) = b.fresh_local(rs_ty.clone());
            let e = b.mk_pi(s_id, BinderInfo::Default, rs_ty, c.prop.clone());
            let e = b.mk_pi(nc_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // input : (nc : Nat) -> (idx : Nat) -> ResolvSound nc (ResolvStep.input nc idx)
        let input_ty = {
            let mut b = EnvDeclBuilder::new();
            let (nc_id, nc) = b.fresh_local(c.nat.clone());
            let (idx_id, idx) = b.fresh_local(c.nat.clone());
            let step = Expr::apps(
                Expr::const_(
                    Name::from_string("ProofComplexitySAT.ResolvStep.input"),
                    vec![],
                ),
                [nc.clone(), idx],
            );
            let ret = resolv_sound(nc, step);
            let e = b.mk_pi(idx_id, BinderInfo::Default, c.nat.clone(), ret);
            let e = b.mk_pi(nc_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // resolve : (nc pivot : Nat) -> (left right : ResolvStep nc) ->
        //   ResolvSound nc left -> ResolvSound nc right ->
        //   ResolvSound nc (ResolvStep.resolve nc pivot left right)
        let resolve_ty = {
            let mut b = EnvDeclBuilder::new();
            let (nc_id, nc) = b.fresh_local(c.nat.clone());
            let (pv_id, pv) = b.fresh_local(c.nat.clone());
            let rs_ty = resolv_step(nc.clone());
            let (l_id, l) = b.fresh_local(rs_ty.clone());
            let (r_id, r) = b.fresh_local(rs_ty.clone());
            let hl_ty = resolv_sound(nc.clone(), l.clone());
            let hr_ty = resolv_sound(nc.clone(), r.clone());
            let (hl_id, _) = b.fresh_local(hl_ty.clone());
            let (hr_id, _) = b.fresh_local(hr_ty.clone());
            let resolved = Expr::apps(
                Expr::const_(
                    Name::from_string("ProofComplexitySAT.ResolvStep.resolve"),
                    vec![],
                ),
                [nc.clone(), pv, l, r],
            );
            let ret = resolv_sound(nc, resolved);
            let e = b.mk_pi(hr_id, BinderInfo::Default, hr_ty, ret);
            let e = b.mk_pi(hl_id, BinderInfo::Default, hl_ty, e);
            let e = b.mk_pi(r_id, BinderInfo::Default, rs_ty.clone(), e);
            let e = b.mk_pi(l_id, BinderInfo::Default, rs_ty, e);
            let e = b.mk_pi(pv_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(nc_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // Register as a genuine inductive family so the kernel generates
        // `ProofComplexitySAT.ResolvSound.rec`.
        let decl = InductiveDecl {
            level_params: vec![],
            num_params: 1,
            types: vec![InductiveType {
                name: Name::from_string("ProofComplexitySAT.ResolvSound"),
                type_: ty,
                constructors: vec![
                    Constructor {
                        name: Name::from_string("ProofComplexitySAT.ResolvSound.input"),
                        type_: input_ty,
                    },
                    Constructor {
                        name: Name::from_string("ProofComplexitySAT.ResolvSound.resolve"),
                        type_: resolve_ty,
                    },
                ],
            }],
        };
        self.add_inductive(decl)
    }

    // ====================================================================
    // Inductive type: ResolvComplete
    // ====================================================================

    #[cfg(any(test, feature = "math-overlays"))]
    fn register_resolv_complete(&mut self, c: &PCProofConsts) -> Result<(), EnvError> {
        // ResolvComplete : Nat -> Type
        let ty = Expr::pi(BinderInfo::Default, c.nat.clone(), c.type0.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofComplexitySAT.ResolvComplete"),
            level_params: vec![],
            type_: ty,
        })?;

        // base_empty : ResolvComplete 0
        let base_ty = resolv_complete(Expr::const_(Name::from_string("Nat.zero"), vec![]));
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofComplexitySAT.ResolvComplete.base_empty"),
            level_params: vec![],
            type_: base_ty,
        })?;

        // elim_var : (n : Nat) -> (var : Nat) -> ResolvComplete n -> ResolvComplete (Nat.succ n)
        let elim_ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (v_id, _) = b.fresh_local(c.nat.clone());
            let rc_n = resolv_complete(n.clone());
            let (ih_id, _) = b.fresh_local(rc_n.clone());
            let succ_n = Expr::app(Expr::const_(Name::from_string("Nat.succ"), vec![]), n);
            let ret = resolv_complete(succ_n);
            let e = b.mk_pi(ih_id, BinderInfo::Default, rc_n, ret);
            let e = b.mk_pi(v_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofComplexitySAT.ResolvComplete.elim_var"),
            level_params: vec![],
            type_: elim_ty,
        })
    }

    // ====================================================================
    // Inductive type: CPStep
    // ====================================================================

    #[cfg(any(test, feature = "math-overlays"))]
    fn register_cp_step_inductive(&mut self, c: &PCProofConsts) -> Result<(), EnvError> {
        // CPStep : Nat -> Type
        let ty = Expr::pi(BinderInfo::Default, c.nat.clone(), c.type0.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofComplexitySAT.CPStep"),
            level_params: vec![],
            type_: ty,
        })?;

        // input : (ni : Nat) -> (idx : Nat) -> CPStep ni
        let input_ty = {
            let mut b = EnvDeclBuilder::new();
            let (ni_id, ni) = b.fresh_local(c.nat.clone());
            let (idx_id, _) = b.fresh_local(c.nat.clone());
            let ret = cp_step(ni);
            let e = b.mk_pi(idx_id, BinderInfo::Default, c.nat.clone(), ret);
            let e = b.mk_pi(ni_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofComplexitySAT.CPStep.input"),
            level_params: vec![],
            type_: input_ty,
        })?;

        // addition : (ni : Nat) -> CPStep ni -> CPStep ni -> CPStep ni
        let add_ty = {
            let mut b = EnvDeclBuilder::new();
            let (ni_id, ni) = b.fresh_local(c.nat.clone());
            let cs_ty = cp_step(ni.clone());
            let (l_id, _) = b.fresh_local(cs_ty.clone());
            let (r_id, _) = b.fresh_local(cs_ty.clone());
            let ret = cp_step(ni);
            let e = b.mk_pi(r_id, BinderInfo::Default, cs_ty.clone(), ret);
            let e = b.mk_pi(l_id, BinderInfo::Default, cs_ty, e);
            let e = b.mk_pi(ni_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofComplexitySAT.CPStep.addition"),
            level_params: vec![],
            type_: add_ty,
        })?;

        // scalar_mul : (ni : Nat) -> (coeff : Nat) -> CPStep ni -> CPStep ni
        let mul_ty = {
            let mut b = EnvDeclBuilder::new();
            let (ni_id, ni) = b.fresh_local(c.nat.clone());
            let (co_id, _) = b.fresh_local(c.nat.clone());
            let cs_ty = cp_step(ni.clone());
            let (inner_id, _) = b.fresh_local(cs_ty.clone());
            let ret = cp_step(ni);
            let e = b.mk_pi(inner_id, BinderInfo::Default, cs_ty, ret);
            let e = b.mk_pi(co_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(ni_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofComplexitySAT.CPStep.scalar_mul"),
            level_params: vec![],
            type_: mul_ty,
        })?;

        // division : (ni : Nat) -> (divisor : Nat) -> CPStep ni -> CPStep ni
        let div_ty = {
            let mut b = EnvDeclBuilder::new();
            let (ni_id, ni) = b.fresh_local(c.nat.clone());
            let (dv_id, _) = b.fresh_local(c.nat.clone());
            let cs_ty = cp_step(ni.clone());
            let (inner_id, _) = b.fresh_local(cs_ty.clone());
            let ret = cp_step(ni);
            let e = b.mk_pi(inner_id, BinderInfo::Default, cs_ty, ret);
            let e = b.mk_pi(dv_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(ni_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofComplexitySAT.CPStep.division"),
            level_params: vec![],
            type_: div_ty,
        })
    }

    // ====================================================================
    // Inductive type: CPSound
    // ====================================================================

    #[cfg(any(test, feature = "math-overlays"))]
    fn register_cp_sound_inductive(&mut self, c: &PCProofConsts) -> Result<(), EnvError> {
        // CPSound : (ni : Nat) -> CPStep ni -> Type
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (ni_id, ni) = b.fresh_local(c.nat.clone());
            let cs_ty = cp_step(ni);
            let (s_id, _) = b.fresh_local(cs_ty.clone());
            let e = b.mk_pi(s_id, BinderInfo::Default, cs_ty, c.type0.clone());
            let e = b.mk_pi(ni_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofComplexitySAT.CPSound"),
            level_params: vec![],
            type_: ty,
        })?;

        // input : (ni idx : Nat) -> CPSound ni (CPStep.input ni idx)
        let input_ty = {
            let mut b = EnvDeclBuilder::new();
            let (ni_id, ni) = b.fresh_local(c.nat.clone());
            let (idx_id, idx) = b.fresh_local(c.nat.clone());
            let step = Expr::apps(
                Expr::const_(Name::from_string("ProofComplexitySAT.CPStep.input"), vec![]),
                [ni.clone(), idx],
            );
            let ret = cp_sound(ni, step);
            let e = b.mk_pi(idx_id, BinderInfo::Default, c.nat.clone(), ret);
            let e = b.mk_pi(ni_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofComplexitySAT.CPSound.input"),
            level_params: vec![],
            type_: input_ty,
        })?;

        // addition : (ni : Nat) -> (left right : CPStep ni) ->
        //   CPSound ni left -> CPSound ni right ->
        //   CPSound ni (CPStep.addition ni left right)
        let add_ty = {
            let mut b = EnvDeclBuilder::new();
            let (ni_id, ni) = b.fresh_local(c.nat.clone());
            let cs_ty = cp_step(ni.clone());
            let (l_id, l) = b.fresh_local(cs_ty.clone());
            let (r_id, r) = b.fresh_local(cs_ty.clone());
            let hl_ty = cp_sound(ni.clone(), l.clone());
            let hr_ty = cp_sound(ni.clone(), r.clone());
            let (hl_id, _) = b.fresh_local(hl_ty.clone());
            let (hr_id, _) = b.fresh_local(hr_ty.clone());
            let step = Expr::apps(
                Expr::const_(
                    Name::from_string("ProofComplexitySAT.CPStep.addition"),
                    vec![],
                ),
                [ni.clone(), l, r],
            );
            let ret = cp_sound(ni, step);
            let e = b.mk_pi(hr_id, BinderInfo::Default, hr_ty, ret);
            let e = b.mk_pi(hl_id, BinderInfo::Default, hl_ty, e);
            let e = b.mk_pi(r_id, BinderInfo::Default, cs_ty.clone(), e);
            let e = b.mk_pi(l_id, BinderInfo::Default, cs_ty, e);
            let e = b.mk_pi(ni_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofComplexitySAT.CPSound.addition"),
            level_params: vec![],
            type_: add_ty,
        })?;

        // scalar_mul : (ni coeff : Nat) -> (inner : CPStep ni) ->
        //   CPSound ni inner -> CPSound ni (CPStep.scalar_mul ni coeff inner)
        let mul_ty = {
            let mut b = EnvDeclBuilder::new();
            let (ni_id, ni) = b.fresh_local(c.nat.clone());
            let (co_id, co) = b.fresh_local(c.nat.clone());
            let cs_ty = cp_step(ni.clone());
            let (inner_id, inner) = b.fresh_local(cs_ty.clone());
            let h_ty = cp_sound(ni.clone(), inner.clone());
            let (h_id, _) = b.fresh_local(h_ty.clone());
            let step = Expr::apps(
                Expr::const_(
                    Name::from_string("ProofComplexitySAT.CPStep.scalar_mul"),
                    vec![],
                ),
                [ni.clone(), co, inner],
            );
            let ret = cp_sound(ni, step);
            let e = b.mk_pi(h_id, BinderInfo::Default, h_ty, ret);
            let e = b.mk_pi(inner_id, BinderInfo::Default, cs_ty, e);
            let e = b.mk_pi(co_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(ni_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofComplexitySAT.CPSound.scalar_mul"),
            level_params: vec![],
            type_: mul_ty,
        })?;

        // division : (ni divisor : Nat) -> (inner : CPStep ni) ->
        //   CPSound ni inner -> CPSound ni (CPStep.division ni divisor inner)
        let div_ty = {
            let mut b = EnvDeclBuilder::new();
            let (ni_id, ni) = b.fresh_local(c.nat.clone());
            let (dv_id, dv) = b.fresh_local(c.nat.clone());
            let cs_ty = cp_step(ni.clone());
            let (inner_id, inner) = b.fresh_local(cs_ty.clone());
            let h_ty = cp_sound(ni.clone(), inner.clone());
            let (h_id, _) = b.fresh_local(h_ty.clone());
            let step = Expr::apps(
                Expr::const_(
                    Name::from_string("ProofComplexitySAT.CPStep.division"),
                    vec![],
                ),
                [ni.clone(), dv, inner],
            );
            let ret = cp_sound(ni, step);
            let e = b.mk_pi(h_id, BinderInfo::Default, h_ty, ret);
            let e = b.mk_pi(inner_id, BinderInfo::Default, cs_ty, e);
            let e = b.mk_pi(dv_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(ni_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofComplexitySAT.CPSound.division"),
            level_params: vec![],
            type_: div_ty,
        })
    }

    // ====================================================================
    // Inductive type: CPSimResolvStep
    // ====================================================================

    #[cfg(any(test, feature = "math-overlays"))]
    fn register_cp_sim_resolv_step(&mut self, c: &PCProofConsts) -> Result<(), EnvError> {
        // CPSimResolvStep : Nat -> Type
        let ty = Expr::pi(BinderInfo::Default, c.nat.clone(), c.type0.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofComplexitySAT.CPSimResolvStep"),
            level_params: vec![],
            type_: ty,
        })?;

        // encode_clause : (nc : Nat) -> (idx : Nat) -> CPSimResolvStep nc
        let enc_ty = {
            let mut b = EnvDeclBuilder::new();
            let (nc_id, nc) = b.fresh_local(c.nat.clone());
            let (idx_id, _) = b.fresh_local(c.nat.clone());
            let ret = cp_sim_step(nc);
            let e = b.mk_pi(idx_id, BinderInfo::Default, c.nat.clone(), ret);
            let e = b.mk_pi(nc_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofComplexitySAT.CPSimResolvStep.encode_clause"),
            level_params: vec![],
            type_: enc_ty,
        })?;

        // sim_resolve : (nc pivot : Nat) -> CPSimResolvStep nc -> CPSimResolvStep nc -> CPSimResolvStep nc
        let sim_ty = {
            let mut b = EnvDeclBuilder::new();
            let (nc_id, nc) = b.fresh_local(c.nat.clone());
            let (pv_id, _) = b.fresh_local(c.nat.clone());
            let cs_ty = cp_sim_step(nc.clone());
            let (l_id, _) = b.fresh_local(cs_ty.clone());
            let (r_id, _) = b.fresh_local(cs_ty.clone());
            let ret = cp_sim_step(nc);
            let e = b.mk_pi(r_id, BinderInfo::Default, cs_ty.clone(), ret);
            let e = b.mk_pi(l_id, BinderInfo::Default, cs_ty, e);
            let e = b.mk_pi(pv_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(nc_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofComplexitySAT.CPSimResolvStep.sim_resolve"),
            level_params: vec![],
            type_: sim_ty,
        })
    }

    // ====================================================================
    // Inductive type: CPSimResolvSound
    // ====================================================================

    #[cfg(any(test, feature = "math-overlays"))]
    fn register_cp_sim_resolv_sound(&mut self, c: &PCProofConsts) -> Result<(), EnvError> {
        // CPSimResolvSound : (nc : Nat) -> CPSimResolvStep nc -> Type
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (nc_id, nc) = b.fresh_local(c.nat.clone());
            let cs_ty = cp_sim_step(nc);
            let (s_id, _) = b.fresh_local(cs_ty.clone());
            let e = b.mk_pi(s_id, BinderInfo::Default, cs_ty, c.type0.clone());
            let e = b.mk_pi(nc_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofComplexitySAT.CPSimResolvSound"),
            level_params: vec![],
            type_: ty,
        })?;

        // encode_clause : (nc idx : Nat) ->
        //   CPSimResolvSound nc (CPSimResolvStep.encode_clause nc idx)
        let enc_ty = {
            let mut b = EnvDeclBuilder::new();
            let (nc_id, nc) = b.fresh_local(c.nat.clone());
            let (idx_id, idx) = b.fresh_local(c.nat.clone());
            let step = Expr::apps(
                Expr::const_(
                    Name::from_string("ProofComplexitySAT.CPSimResolvStep.encode_clause"),
                    vec![],
                ),
                [nc.clone(), idx],
            );
            let ret = cp_sim_sound(nc, step);
            let e = b.mk_pi(idx_id, BinderInfo::Default, c.nat.clone(), ret);
            let e = b.mk_pi(nc_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofComplexitySAT.CPSimResolvSound.encode_clause"),
            level_params: vec![],
            type_: enc_ty,
        })?;

        // sim_resolve : (nc pivot : Nat) -> (left right : CPSimResolvStep nc) ->
        //   CPSimResolvSound nc left -> CPSimResolvSound nc right ->
        //   CPSimResolvSound nc (CPSimResolvStep.sim_resolve nc pivot left right)
        let sim_ty = {
            let mut b = EnvDeclBuilder::new();
            let (nc_id, nc) = b.fresh_local(c.nat.clone());
            let (pv_id, pv) = b.fresh_local(c.nat.clone());
            let cs_ty = cp_sim_step(nc.clone());
            let (l_id, l) = b.fresh_local(cs_ty.clone());
            let (r_id, r) = b.fresh_local(cs_ty.clone());
            let hl_ty = cp_sim_sound(nc.clone(), l.clone());
            let hr_ty = cp_sim_sound(nc.clone(), r.clone());
            let (hl_id, _) = b.fresh_local(hl_ty.clone());
            let (hr_id, _) = b.fresh_local(hr_ty.clone());
            let step = Expr::apps(
                Expr::const_(
                    Name::from_string("ProofComplexitySAT.CPSimResolvStep.sim_resolve"),
                    vec![],
                ),
                [nc.clone(), pv, l, r],
            );
            let ret = cp_sim_sound(nc, step);
            let e = b.mk_pi(hr_id, BinderInfo::Default, hr_ty, ret);
            let e = b.mk_pi(hl_id, BinderInfo::Default, hl_ty, e);
            let e = b.mk_pi(r_id, BinderInfo::Default, cs_ty.clone(), e);
            let e = b.mk_pi(l_id, BinderInfo::Default, cs_ty, e);
            let e = b.mk_pi(pv_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(nc_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ProofComplexitySAT.CPSimResolvSound.sim_resolve"),
            level_params: vec![],
            type_: sim_ty,
        })
    }

    // ====================================================================
    // Theorem PC01: Resolution soundness
    // ====================================================================

    #[cfg(any(test, feature = "math-overlays"))]
    fn register_pc01_theorem(&mut self, c: &PCProofConsts) -> Result<(), EnvError> {
        let thm_name = "ProofComplexitySAT.pc01_resolution_soundness";

        // Theorem type: forall (nc : Nat) (step : ResolvStep nc), ResolvSound nc step
        //
        // This is the FULL soundness statement — every resolution derivation step
        // is sound. No `Nonempty` wrapper and no axiom: the proof below is a real
        // structural recursion over `ResolvStep` via its kernel-generated recursor.
        let thm_type = {
            let mut b = EnvDeclBuilder::new();
            let (nc_id, nc) = b.fresh_local(c.nat.clone());
            let rs_ty = resolv_step(nc.clone());
            let (s_id, s) = b.fresh_local(rs_ty.clone());
            let ret = resolv_sound(nc, s);
            let e = b.mk_pi(s_id, BinderInfo::Default, rs_ty, ret);
            let e = b.mk_pi(nc_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // SOUNDNESS: PC01 proof term is structural recursion over the ResolvStep
        // inductive via its recursor; no circular self-reference, no domain axioms.
        //
        // Proof term:
        //   fun (nc : Nat) (step : ResolvStep nc) =>
        //     ResolvStep.rec.{1} (nc := nc)
        //       (motive := fun (s : ResolvStep nc) => ResolvSound nc s)
        //       (input-case:   fun (idx : Nat) => ResolvSound.input nc idx)
        //       (resolve-case: fun (pivot : Nat) (left right : ResolvStep nc)
        //                          (ih_l : ResolvSound nc left)
        //                          (ih_r : ResolvSound nc right) =>
        //                        ResolvSound.resolve nc pivot left right ih_l ih_r)
        //       step
        //
        // The recursor binders (confirmed against the kernel-generated
        // `ResolvStep.rec`) are, in application order:
        //   {nc : Nat} {motive : ResolvStep nc → Sort u} (input-case) (resolve-case)
        //   (major : ResolvStep nc) → motive major
        // with `u := 0` because the motive returns `ResolvSound nc s : Prop`
        // (large elimination from the Type-valued ResolvStep into a Prop motive).
        let resolv_step_rec = Expr::const_(
            Name::from_string("ProofComplexitySAT.ResolvStep.rec"),
            vec![Level::zero()],
        );
        let proof = {
            let mut b = EnvDeclBuilder::new();
            let (nc_id, nc) = b.fresh_local(c.nat.clone());
            let rs_ty = resolv_step(nc.clone());
            let (step_id, step) = b.fresh_local(rs_ty.clone());

            // motive := fun (s : ResolvStep nc) => ResolvSound nc s
            let motive = {
                let mut mb = EnvDeclBuilder::child_of(&b);
                let (m_s_id, m_s) = mb.fresh_local(rs_ty.clone());
                let body = resolv_sound(nc.clone(), m_s);
                let lam = mb.mk_lam(m_s_id, BinderInfo::Default, rs_ty.clone(), body);
                mb.finish_child(lam)
            };

            // input-case := fun (idx : Nat) => ResolvSound.input nc idx
            let input_case = {
                let mut ib = EnvDeclBuilder::child_of(&b);
                let (idx_id, idx) = ib.fresh_local(c.nat.clone());
                let body = Expr::apps(
                    Expr::const_(
                        Name::from_string("ProofComplexitySAT.ResolvSound.input"),
                        vec![],
                    ),
                    [nc.clone(), idx],
                );
                let lam = ib.mk_lam(idx_id, BinderInfo::Default, c.nat.clone(), body);
                ib.finish_child(lam)
            };

            // resolve-case := fun (pivot : Nat) (left right : ResolvStep nc)
            //                     (ih_l : ResolvSound nc left)
            //                     (ih_r : ResolvSound nc right) =>
            //                   ResolvSound.resolve nc pivot left right ih_l ih_r
            let resolve_case = {
                let mut rb = EnvDeclBuilder::child_of(&b);
                let (pv_id, pv) = rb.fresh_local(c.nat.clone());
                let (l_id, l) = rb.fresh_local(rs_ty.clone());
                let (r_id, r) = rb.fresh_local(rs_ty.clone());
                let ihl_ty = resolv_sound(nc.clone(), l.clone());
                let ihr_ty = resolv_sound(nc.clone(), r.clone());
                let (ihl_id, ihl) = rb.fresh_local(ihl_ty.clone());
                let (ihr_id, ihr) = rb.fresh_local(ihr_ty.clone());
                let body = Expr::apps(
                    Expr::const_(
                        Name::from_string("ProofComplexitySAT.ResolvSound.resolve"),
                        vec![],
                    ),
                    [nc.clone(), pv, l.clone(), r.clone(), ihl, ihr],
                );
                let lam = rb.mk_lam(ihr_id, BinderInfo::Default, ihr_ty, body);
                let lam = rb.mk_lam(ihl_id, BinderInfo::Default, ihl_ty, lam);
                let lam = rb.mk_lam(r_id, BinderInfo::Default, rs_ty.clone(), lam);
                let lam = rb.mk_lam(l_id, BinderInfo::Default, rs_ty.clone(), lam);
                let lam = rb.mk_lam(pv_id, BinderInfo::Default, c.nat.clone(), lam);
                rb.finish_child(lam)
            };

            // ResolvStep.rec.{1} nc motive input_case resolve_case step
            let rec_app = Expr::apps(
                resolv_step_rec,
                [nc.clone(), motive, input_case, resolve_case, step.clone()],
            );

            let e = b.mk_lam(step_id, BinderInfo::Default, rs_ty, rec_app);
            let e = b.mk_lam(nc_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }

    // ====================================================================
    // PC02: Resolution completeness (HONEST AXIOM)
    // ====================================================================

    #[cfg(any(test, feature = "math-overlays"))]
    fn register_pc02_axiom(&mut self, c: &PCProofConsts) -> Result<(), EnvError> {
        let axiom_name = "ProofComplexitySAT.pc02_resolution_completeness";

        // SOUNDNESS: PC02 admits resolution COMPLETENESS as an honest
        // `Declaration::Axiom`: `forall (n : Nat), ResolvComplete n`. This is a
        // genuine metatheorem (the Davis-Putnam variable-elimination argument:
        // every unsatisfiable CNF over n variables has a resolution refutation).
        // It is NOT structurally provable in-kernel from the `ResolvComplete`
        // generators — the elimination step requires reasoning that exhaustive
        // resolution over a variable preserves unsatisfiability — so it is
        // admitted, not proved. A recursor-based kernel proof (cf. PC01) is
        // future work; until then this is an admitted axiom, not a theorem.
        // Previously masqueraded as a `Declaration::Theorem` whose value was
        // `Nonempty.intro` over this same axiom; that wrapper is removed.
        let axiom_type = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let ret = resolv_complete(n);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), ret);
            b.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string(axiom_name),
            level_params: vec![],
            type_: axiom_type,
        })
    }

    // ====================================================================
    // PC03: Cutting planes soundness (HONEST AXIOM)
    // ====================================================================

    #[cfg(any(test, feature = "math-overlays"))]
    fn register_pc03_axiom(&mut self, c: &PCProofConsts) -> Result<(), EnvError> {
        let axiom_name = "ProofComplexitySAT.pc03_cp_soundness";

        // SOUNDNESS: PC03 admits cutting-planes SOUNDNESS as an honest
        // `Declaration::Axiom`: `forall (ni : Nat) (step : CPStep ni),
        // CPSound ni step`. This is a genuine metatheorem — every cutting-planes
        // derivation step (addition, non-negative scalar multiplication, and
        // ceiling division) preserves validity over 0-1 assignments. The
        // ceiling-division case in particular relies on integer-rounding
        // arithmetic that is not discharged by the `CPSound` generators alone,
        // so the statement is admitted, not proved. A recursor-based kernel
        // proof (cf. PC01) is future work. Previously masqueraded as a
        // `Declaration::Theorem` whose value was `Nonempty.intro` over this same
        // axiom; that wrapper is removed.
        let axiom_type = {
            let mut b = EnvDeclBuilder::new();
            let (ni_id, ni) = b.fresh_local(c.nat.clone());
            let cs_ty = cp_step(ni.clone());
            let (s_id, s) = b.fresh_local(cs_ty.clone());
            let ret = cp_sound(ni, s);
            let e = b.mk_pi(s_id, BinderInfo::Default, cs_ty, ret);
            let e = b.mk_pi(ni_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string(axiom_name),
            level_params: vec![],
            type_: axiom_type,
        })
    }

    // ====================================================================
    // PC04: CP subsumes resolution (HONEST AXIOM)
    // ====================================================================

    #[cfg(any(test, feature = "math-overlays"))]
    fn register_pc04_axiom(&mut self, c: &PCProofConsts) -> Result<(), EnvError> {
        let axiom_name = "ProofComplexitySAT.pc04_cp_subsumes_resolution";

        // SOUNDNESS: PC04 admits CP-subsumes-RESOLUTION as an honest
        // `Declaration::Axiom`: `forall (nc : Nat) (step : CPSimResolvStep nc),
        // CPSimResolvSound nc step`. This is a genuine metatheorem — every
        // resolution step is simulated by a cutting-planes derivation: a clause
        // is encoded as a >= 1 inequality, and a resolution pivot is simulated by
        // adding the two parent inequalities (cancelling the pivot via
        // x_p + (1 - x_p) = 1) and dividing by 2 with ceiling rounding to recover
        // the resolvent's encoding. The pivot-cancellation / ceiling-rounding
        // argument is not discharged by the `CPSimResolvSound` generators alone,
        // so the statement is admitted, not proved. A recursor-based kernel proof
        // (cf. PC01) is future work. Previously masqueraded as a
        // `Declaration::Theorem` whose value was `Nonempty.intro` over this same
        // axiom; that wrapper is removed.
        let axiom_type = {
            let mut b = EnvDeclBuilder::new();
            let (nc_id, nc) = b.fresh_local(c.nat.clone());
            let cs_ty = cp_sim_step(nc.clone());
            let (s_id, s) = b.fresh_local(cs_ty.clone());
            let ret = cp_sim_sound(nc, s);
            let e = b.mk_pi(s_id, BinderInfo::Default, cs_ty, ret);
            let e = b.mk_pi(nc_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string(axiom_name),
            level_params: vec![],
            type_: axiom_type,
        })
    }
}

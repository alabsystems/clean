// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Core pair/dependent-pair initializers plus trust/bootstrap module wiring.

mod trust;

use super::decl_builder::EnvDeclBuilder;
use super::*;

impl Environment {
    /// Initialize Prod (non-dependent pair) structure
    ///
    /// structure Prod (α : Type u) (β : Type v) : Type (max u v) where
    ///   mk :: (fst : α) (snd : β)
    ///
    /// # Contract
    ///
    /// ENSURES: On success, `self.has_prod() == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())`
    /// ENSURES: Adds Prod, Prod.mk, Prod.fst, Prod.snd, Prod.rec
    pub fn init_prod(&mut self) -> Result<(), EnvError> {
        if self.prod_init {
            return Ok(());
        }

        let u = Name::from_string("u");
        let v = Name::from_string("v");

        let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(u.clone()))));
        let type_v = Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(v.clone()))));
        let result_sort = Expr::from_kind(ExprKind::Sort(Level::max(
            Level::succ(Level::param(u.clone())),
            Level::succ(Level::param(v.clone())),
        )));

        let prod_const = Expr::const_(
            Name::from_string("Prod"),
            vec![Level::param(u.clone()), Level::param(v.clone())],
        );

        // Prod : Type u → Type v → Type (max u v)
        let prod_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, _a) = b.fresh_local(type_u.clone());
            let (bv_id, _bv) = b.fresh_local(type_v.clone());
            let e = b.mk_pi(
                bv_id,
                BinderInfo::Implicit,
                type_v.clone(),
                result_sort.clone(),
            );
            let e = b.mk_pi(a_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        // Prod.mk : {α : Type u} → {β : Type v} → α → β → Prod α β
        let prod_mk_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_v.clone());
            let (fst_id, _fst) = b.fresh_local(alpha.clone());
            let (snd_id, _snd) = b.fresh_local(beta.clone());
            let result = Expr::app(Expr::app(prod_const.clone(), alpha.clone()), beta.clone());
            let e = b.mk_pi(snd_id, BinderInfo::Default, beta, result);
            let e = b.mk_pi(fst_id, BinderInfo::Default, alpha, e);
            let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_v.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        let prod_decl = InductiveDecl {
            level_params: vec![u.clone(), v.clone()],
            num_params: 2,
            types: vec![InductiveType {
                name: Name::from_string("Prod"),
                type_: prod_type,
                constructors: vec![Constructor {
                    name: Name::from_string("Prod.mk"),
                    type_: prod_mk_type,
                }],
            }],
        };

        self.add_inductive(prod_decl)?;

        // Prod.fst : {α : Type u} {β : Type v} → Prod α β → α
        let prod_fst_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_v.clone());
            let prod_ab = Expr::app(Expr::app(prod_const.clone(), alpha.clone()), beta.clone());
            let (s_id, _s) = b.fresh_local(prod_ab.clone());
            let e = b.mk_pi(s_id, BinderInfo::Default, prod_ab, alpha.clone());
            let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_v.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        // Prod.fst value = λ {α} {β} (self : Prod α β) => Expr.proj("Prod", 0, self)
        let prod_fst_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_v.clone());
            let prod_ab = Expr::app(Expr::app(prod_const.clone(), alpha.clone()), beta.clone());
            let (s_id, s) = b.fresh_local(prod_ab.clone());
            let body = Expr::proj(Name::from_string("Prod"), 0, s);
            let e = b.mk_lam(s_id, BinderInfo::Default, prod_ab, body);
            let e = b.mk_lam(beta_id, BinderInfo::Implicit, type_v.clone(), e);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Prod.fst"),
            level_params: vec![u.clone(), v.clone()],
            type_: prod_fst_type,
            value: prod_fst_value,
            is_reducible: true,
        })?;

        // Prod.snd : {α : Type u} {β : Type v} → Prod α β → β
        let prod_snd_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_v.clone());
            let prod_ab = Expr::app(Expr::app(prod_const.clone(), alpha.clone()), beta.clone());
            let (s_id, _s) = b.fresh_local(prod_ab.clone());
            let e = b.mk_pi(s_id, BinderInfo::Default, prod_ab, beta.clone());
            let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_v.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        // Prod.snd value = λ {α} {β} (self : Prod α β) => Expr.proj("Prod", 1, self)
        let prod_snd_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_v.clone());
            let prod_ab = Expr::app(Expr::app(prod_const.clone(), alpha.clone()), beta.clone());
            let (s_id, s) = b.fresh_local(prod_ab.clone());
            let body = Expr::proj(Name::from_string("Prod"), 1, s);
            let e = b.mk_lam(s_id, BinderInfo::Default, prod_ab, body);
            let e = b.mk_lam(beta_id, BinderInfo::Implicit, type_v.clone(), e);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Prod.snd"),
            level_params: vec![u.clone(), v.clone()],
            type_: prod_snd_type,
            value: prod_snd_value,
            is_reducible: true,
        })?;

        // Prod.swap : {α : Type u} {β : Type v} → Prod α β → Prod β α
        let prod_swap_return_const = Expr::const_(
            Name::from_string("Prod"),
            vec![Level::param(v.clone()), Level::param(u.clone())],
        );
        let prod_swap_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_v.clone());
            let prod_ab = Expr::app(Expr::app(prod_const.clone(), alpha.clone()), beta.clone());
            let (p_id, _p) = b.fresh_local(prod_ab.clone());
            let result = Expr::app(
                Expr::app(prod_swap_return_const, beta.clone()),
                alpha.clone(),
            );
            let e = b.mk_pi(p_id, BinderInfo::Default, prod_ab, result);
            let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_v.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        // Prod.swap value = λ {α} {β} (p : Prod α β), Prod.mk.{v,u} β α (p.snd) (p.fst)
        let prod_mk_swap_const = Expr::const_(
            Name::from_string("Prod.mk"),
            vec![Level::param(v.clone()), Level::param(u.clone())],
        );

        let prod_swap_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_v.clone());
            let prod_ab = Expr::app(Expr::app(prod_const.clone(), alpha.clone()), beta.clone());
            let (p_id, p) = b.fresh_local(prod_ab.clone());
            let body = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(prod_mk_swap_const.clone(), beta.clone()),
                        alpha.clone(),
                    ),
                    Expr::proj(Name::from_string("Prod"), 1, p.clone()),
                ),
                Expr::proj(Name::from_string("Prod"), 0, p),
            );
            let e = b.mk_lam(p_id, BinderInfo::Default, prod_ab, body);
            let e = b.mk_lam(beta_id, BinderInfo::Implicit, type_v.clone(), e);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        // FIDELITY (v4.31 retarget, 2026-07-04): Lean v4.31's `Prod.swap` has
        // `levelParams = [u_1, u_2]` in BINDER-APPEARANCE order for
        // `{α : Type u_1} → {β : Type u_2} → Prod α β → Prod β α` (verified via
        // `#print Prod.swap` on the v4.31 toolchain and by the instrumented
        // replay of `Prod.swap_lt_mk`: applications supply
        // `@Prod.swap.{u_2, u_3}` with α's level FIRST). Lean v4.8 ordered the
        // list REVERSED (`[u_2, u_1]`, β-level first — the previous fix here);
        // the auto-bound universe ordering changed between versions. The list
        // must be `[u, v]` (α's `u` first) so level substitution binds α↦first
        // arg; the reversed list yielded `Sort(Succ u_3)` vs `Sort(Succ u_2)`
        // mismatches on the 27-decl `Prod.swap_*` Order cluster on v4.31.
        // The type/value exprs are unchanged — only the param LIST order matters.
        self.add_decl(Declaration::Definition {
            name: Name::from_string("Prod.swap"),
            level_params: vec![u.clone(), v.clone()],
            type_: prod_swap_type,
            value: prod_swap_value,
            is_reducible: true,
        })?;

        // Prod.map : {α : Type u₁} {β : Type u₂} {γ : Type v₁} {δ : Type v₂} →
        //   (α → β) → (γ → δ) → Prod α γ → Prod β δ
        // Lean `Init/Prelude.lean`:
        //   @[reducible] def Prod.map (f : α → β) (g : γ → δ) : α × γ → β × δ
        //     | (a, c) => (f a, g c)
        // Registered as a reducible axiom-free projection fold. Non-recursive:
        // no recursor is needed — the pair is destructured with `Expr::proj`
        // (mirroring `Prod.swap`). Without this, `p.map f g` / `Prod.map f g p`
        // failed (missing const). The four universe params are in
        // binder-appearance order [α, β, γ, δ] (see the Prod.swap fidelity note).
        if self.get_const(&Name::from_string("Prod.map")).is_none() {
            let ua = Name::from_string("u_1");
            let ub = Name::from_string("u_2");
            let uc = Name::from_string("u_3");
            let ud = Name::from_string("u_4");
            let type_ua = Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(ua.clone()))));
            let type_ub = Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(ub.clone()))));
            let type_uc = Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(uc.clone()))));
            let type_ud = Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(ud.clone()))));
            // Prod α γ (input, universes [u₁, v₁]) and Prod β δ (output, [u₂, v₂]).
            let prod_ac = Expr::const_(
                Name::from_string("Prod"),
                vec![Level::param(ua.clone()), Level::param(uc.clone())],
            );
            let prod_bd = Expr::const_(
                Name::from_string("Prod"),
                vec![Level::param(ub.clone()), Level::param(ud.clone())],
            );
            let prod_mk_bd = Expr::const_(
                Name::from_string("Prod.mk"),
                vec![Level::param(ub.clone()), Level::param(ud.clone())],
            );

            // Prod.map type
            let prod_map_type = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_ua.clone());
                let (beta_id, beta) = b.fresh_local(type_ub.clone());
                let (gamma_id, gamma) = b.fresh_local(type_uc.clone());
                let (delta_id, delta) = b.fresh_local(type_ud.clone());
                // f : α → β  (child builder — references parent fvars α, β)
                let f_ty = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (a_id, _a) = c.fresh_local(alpha.clone());
                    let r = c.mk_pi(a_id, BinderInfo::Default, alpha.clone(), beta.clone());
                    c.finish_child(r)
                };
                // g : γ → δ
                let g_ty = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (a_id, _a) = c.fresh_local(gamma.clone());
                    let r = c.mk_pi(a_id, BinderInfo::Default, gamma.clone(), delta.clone());
                    c.finish_child(r)
                };
                let (f_id, _f) = b.fresh_local(f_ty.clone());
                let (g_id, _g) = b.fresh_local(g_ty.clone());
                let prod_in = Expr::app(Expr::app(prod_ac.clone(), alpha.clone()), gamma.clone());
                let (p_id, _p) = b.fresh_local(prod_in.clone());
                let result = Expr::app(Expr::app(prod_bd.clone(), beta.clone()), delta.clone());
                let e = b.mk_pi(p_id, BinderInfo::Default, prod_in, result);
                let e = b.mk_pi(g_id, BinderInfo::Default, g_ty, e);
                let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, e);
                let e = b.mk_pi(delta_id, BinderInfo::Implicit, type_ud.clone(), e);
                let e = b.mk_pi(gamma_id, BinderInfo::Implicit, type_uc.clone(), e);
                let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_ub.clone(), e);
                let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_ua.clone(), e);
                b.finish(e)
            };

            // Prod.map value:
            //   λ {α}{β}{γ}{δ} (f : α→β) (g : γ→δ) (p : Prod α γ) =>
            //     @Prod.mk β δ (f p.1) (g p.2)
            let prod_map_value = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_ua.clone());
                let (beta_id, beta) = b.fresh_local(type_ub.clone());
                let (gamma_id, gamma) = b.fresh_local(type_uc.clone());
                let (delta_id, delta) = b.fresh_local(type_ud.clone());
                let f_ty = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (a_id, _a) = c.fresh_local(alpha.clone());
                    let r = c.mk_pi(a_id, BinderInfo::Default, alpha.clone(), beta.clone());
                    c.finish_child(r)
                };
                let g_ty = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (a_id, _a) = c.fresh_local(gamma.clone());
                    let r = c.mk_pi(a_id, BinderInfo::Default, gamma.clone(), delta.clone());
                    c.finish_child(r)
                };
                let (f_id, f) = b.fresh_local(f_ty.clone());
                let (g_id, g) = b.fresh_local(g_ty.clone());
                let prod_in = Expr::app(Expr::app(prod_ac.clone(), alpha.clone()), gamma.clone());
                let (p_id, p) = b.fresh_local(prod_in.clone());
                // @Prod.mk β δ (f p.1) (g p.2)
                let fst = Expr::app(f, Expr::proj(Name::from_string("Prod"), 0, p.clone()));
                let snd = Expr::app(g, Expr::proj(Name::from_string("Prod"), 1, p));
                let body = Expr::app(
                    Expr::app(
                        Expr::app(Expr::app(prod_mk_bd.clone(), beta.clone()), delta.clone()),
                        fst,
                    ),
                    snd,
                );
                let e = b.mk_lam(p_id, BinderInfo::Default, prod_in, body);
                let e = b.mk_lam(g_id, BinderInfo::Default, g_ty, e);
                let e = b.mk_lam(f_id, BinderInfo::Default, f_ty, e);
                let e = b.mk_lam(delta_id, BinderInfo::Implicit, type_ud.clone(), e);
                let e = b.mk_lam(gamma_id, BinderInfo::Implicit, type_uc.clone(), e);
                let e = b.mk_lam(beta_id, BinderInfo::Implicit, type_ub.clone(), e);
                let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_ua.clone(), e);
                b.finish(e)
            };

            self.add_decl(Declaration::Definition {
                name: Name::from_string("Prod.map"),
                level_params: vec![ua, ub, uc, ud],
                type_: prod_map_type,
                value: prod_map_value,
                is_reducible: true,
            })?;
        }

        // Register structure fields for dot-projection support
        self.register_structure_fields(
            Name::from_string("Prod"),
            vec![Name::from_string("fst"), Name::from_string("snd")],
        )?;

        self.prod_init = true;
        Ok(())
    }

    /// Check if Prod has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_prod()` has been called successfully
    /// ENSURES: Pure function - no side effects
    #[allow(dead_code)] // Used by integration tests
    pub(crate) fn has_prod(&self) -> bool {
        self.prod_init
    }

    /// Initialize PProd (Sort-level pair) structure
    ///
    /// structure PProd (α : Sort u) (β : Sort v) : Sort (max (max 1 u) v) where
    ///   mk :: (fst : α) (snd : β)
    ///
    /// # Contract
    ///
    /// ENSURES: On success, `self.has_pprod() == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())`
    /// ENSURES: Adds PProd, PProd.mk, PProd.fst, PProd.snd, PProd.rec
    pub fn init_pprod(&mut self) -> Result<(), EnvError> {
        if self.pprod_init {
            return Ok(());
        }

        let u = Name::from_string("u");
        let v = Name::from_string("v");

        let sort_u = Expr::from_kind(ExprKind::Sort(Level::param(u.clone())));
        let sort_v = Expr::from_kind(ExprKind::Sort(Level::param(v.clone())));
        let result_sort = Expr::from_kind(ExprKind::Sort(Level::max(
            Level::max(Level::succ(Level::zero()), Level::param(u.clone())),
            Level::param(v.clone()),
        )));

        let pprod_const = Expr::const_(
            Name::from_string("PProd"),
            vec![Level::param(u.clone()), Level::param(v.clone())],
        );

        // PProd : Sort u → Sort v → Sort (max (max 1 u) v)
        let pprod_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, _a) = b.fresh_local(sort_u.clone());
            let (bv_id, _bv) = b.fresh_local(sort_v.clone());
            let e = b.mk_pi(
                bv_id,
                BinderInfo::Implicit,
                sort_v.clone(),
                result_sort.clone(),
            );
            let e = b.mk_pi(a_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };

        // PProd.mk : {α : Sort u} → {β : Sort v} → α → β → PProd α β
        let pprod_mk_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let (beta_id, beta) = b.fresh_local(sort_v.clone());
            let (fst_id, _fst) = b.fresh_local(alpha.clone());
            let (snd_id, _snd) = b.fresh_local(beta.clone());
            let result = Expr::app(Expr::app(pprod_const.clone(), alpha.clone()), beta.clone());
            let e = b.mk_pi(snd_id, BinderInfo::Default, beta, result);
            let e = b.mk_pi(fst_id, BinderInfo::Default, alpha, e);
            let e = b.mk_pi(beta_id, BinderInfo::Implicit, sort_v.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };

        let pprod_decl = InductiveDecl {
            level_params: vec![u.clone(), v.clone()],
            num_params: 2,
            types: vec![InductiveType {
                name: Name::from_string("PProd"),
                type_: pprod_type,
                constructors: vec![Constructor {
                    name: Name::from_string("PProd.mk"),
                    type_: pprod_mk_type,
                }],
            }],
        };

        self.add_inductive(pprod_decl)?;

        // PProd.fst : {α : Sort u} {β : Sort v} → PProd α β → α
        let pprod_fst_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let (beta_id, beta) = b.fresh_local(sort_v.clone());
            let pprod_ab = Expr::app(Expr::app(pprod_const.clone(), alpha.clone()), beta.clone());
            let (s_id, _s) = b.fresh_local(pprod_ab.clone());
            let e = b.mk_pi(s_id, BinderInfo::Default, pprod_ab, alpha.clone());
            let e = b.mk_pi(beta_id, BinderInfo::Implicit, sort_v.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };

        let pprod_fst_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let (beta_id, beta) = b.fresh_local(sort_v.clone());
            let pprod_ab = Expr::app(Expr::app(pprod_const.clone(), alpha.clone()), beta.clone());
            let (s_id, s) = b.fresh_local(pprod_ab.clone());
            let body = Expr::proj(Name::from_string("PProd"), 0, s);
            let e = b.mk_lam(s_id, BinderInfo::Default, pprod_ab, body);
            let e = b.mk_lam(beta_id, BinderInfo::Implicit, sort_v.clone(), e);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("PProd.fst"),
            level_params: vec![u.clone(), v.clone()],
            type_: pprod_fst_type,
            value: pprod_fst_value,
            is_reducible: true,
        })?;

        // PProd.snd : {α : Sort u} {β : Sort v} → PProd α β → β
        let pprod_snd_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let (beta_id, beta) = b.fresh_local(sort_v.clone());
            let pprod_ab = Expr::app(Expr::app(pprod_const.clone(), alpha.clone()), beta.clone());
            let (s_id, _s) = b.fresh_local(pprod_ab.clone());
            let e = b.mk_pi(s_id, BinderInfo::Default, pprod_ab, beta.clone());
            let e = b.mk_pi(beta_id, BinderInfo::Implicit, sort_v.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };

        let pprod_snd_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let (beta_id, beta) = b.fresh_local(sort_v.clone());
            let pprod_ab = Expr::app(Expr::app(pprod_const.clone(), alpha.clone()), beta.clone());
            let (s_id, s) = b.fresh_local(pprod_ab.clone());
            let body = Expr::proj(Name::from_string("PProd"), 1, s);
            let e = b.mk_lam(s_id, BinderInfo::Default, pprod_ab, body);
            let e = b.mk_lam(beta_id, BinderInfo::Implicit, sort_v.clone(), e);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("PProd.snd"),
            level_params: vec![u.clone(), v.clone()],
            type_: pprod_snd_type,
            value: pprod_snd_value,
            is_reducible: true,
        })?;

        // PProd.swap : {α : Sort u} {β : Sort v} → PProd α β → PProd β α
        let pprod_swap_return_const = Expr::const_(
            Name::from_string("PProd"),
            vec![Level::param(v.clone()), Level::param(u.clone())],
        );
        let pprod_swap_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let (beta_id, beta) = b.fresh_local(sort_v.clone());
            let pprod_ab = Expr::app(Expr::app(pprod_const.clone(), alpha.clone()), beta.clone());
            let (p_id, _p) = b.fresh_local(pprod_ab.clone());
            let result = Expr::app(
                Expr::app(pprod_swap_return_const, beta.clone()),
                alpha.clone(),
            );
            let e = b.mk_pi(p_id, BinderInfo::Default, pprod_ab, result);
            let e = b.mk_pi(beta_id, BinderInfo::Implicit, sort_v.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };

        let pprod_mk_swap_const = Expr::const_(
            Name::from_string("PProd.mk"),
            vec![Level::param(v.clone()), Level::param(u.clone())],
        );

        let pprod_swap_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let (beta_id, beta) = b.fresh_local(sort_v.clone());
            let pprod_ab = Expr::app(Expr::app(pprod_const.clone(), alpha.clone()), beta.clone());
            let (p_id, p) = b.fresh_local(pprod_ab.clone());
            let body = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(pprod_mk_swap_const.clone(), beta.clone()),
                        alpha.clone(),
                    ),
                    Expr::proj(Name::from_string("PProd"), 1, p.clone()),
                ),
                Expr::proj(Name::from_string("PProd"), 0, p),
            );
            let e = b.mk_lam(p_id, BinderInfo::Default, pprod_ab, body);
            let e = b.mk_lam(beta_id, BinderInfo::Implicit, sort_v.clone(), e);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("PProd.swap"),
            level_params: vec![u.clone(), v.clone()],
            type_: pprod_swap_type,
            value: pprod_swap_value,
            is_reducible: true,
        })?;

        self.register_structure_fields(
            Name::from_string("PProd"),
            vec![Name::from_string("fst"), Name::from_string("snd")],
        )?;

        self.pprod_init = true;
        Ok(())
    }

    /// Check if PProd has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_pprod()` has been called successfully
    /// ENSURES: Pure function - no side effects
    #[allow(dead_code)] // Used by integration tests
    pub(crate) fn has_pprod(&self) -> bool {
        self.pprod_init
    }

    /// Initialize Sigma (dependent pair) inductive type
    ///
    /// inductive Sigma {α : Type u} (β : α → Type v) : Type (max u v) where
    ///   | mk (a : α) (b : β a) : Sigma β
    ///
    /// # Contract
    ///
    /// ENSURES: On success, `self.has_sigma() == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())`
    /// ENSURES: Adds Sigma, Sigma.mk, Sigma.fst, Sigma.snd, Sigma.rec
    pub fn init_sigma(&mut self) -> Result<(), EnvError> {
        if self.sigma_init {
            return Ok(());
        }

        let u = Name::from_string("u");
        let v = Name::from_string("v");

        let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(u.clone()))));
        let type_v = Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(v.clone()))));
        let result_sort = Expr::from_kind(ExprKind::Sort(Level::max(
            Level::succ(Level::param(u.clone())),
            Level::succ(Level::param(v.clone())),
        )));

        let sigma_const = Expr::const_(
            Name::from_string("Sigma"),
            vec![Level::param(u.clone()), Level::param(v.clone())],
        );

        // Sigma : {α : Type u} → (α → Type v) → Type (max u v)
        let sigma_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let beta_ty = Expr::pi(BinderInfo::Default, alpha.clone(), type_v.clone());
            let (beta_id, _beta) = b.fresh_local(beta_ty.clone());
            let e = b.mk_pi(beta_id, BinderInfo::Default, beta_ty, result_sort.clone());
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        // Sigma.mk : {α : Type u} → {β : α → Type v} → (a : α) → β a → Sigma β
        //
        // Lean fidelity (`Init/Core.lean:266` structure Sigma, oracle
        // `#check @Sigma.mk` on v4.30.0-rc2): BOTH structure parameters are
        // implicit in the constructor — `{α}` AND `{β}`. β was previously
        // registered as an explicit binder, so the elaborator slotted the
        // first explicit operand of `Sigma.mk a b` into the `β : α → Type v`
        // position and every plain (non-`@`) `Sigma.mk` application failed
        // with a Pi-shaped TypeMismatch (audit row e08).
        let sigma_mk_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let beta_ty = Expr::pi(BinderInfo::Default, alpha.clone(), type_v.clone());
            let (beta_id, beta) = b.fresh_local(beta_ty.clone());
            let (a_id, a) = b.fresh_local(alpha.clone());
            let ba_ty = Expr::app(beta.clone(), a.clone());
            let (ba_id, _ba) = b.fresh_local(ba_ty.clone());
            let result = Expr::app(Expr::app(sigma_const.clone(), alpha.clone()), beta.clone());
            let e = b.mk_pi(ba_id, BinderInfo::Default, ba_ty, result);
            let e = b.mk_pi(a_id, BinderInfo::Default, alpha, e);
            let e = b.mk_pi(beta_id, BinderInfo::Implicit, beta_ty, e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        let sigma_decl = InductiveDecl {
            level_params: vec![u.clone(), v.clone()],
            num_params: 2,
            types: vec![InductiveType {
                name: Name::from_string("Sigma"),
                type_: sigma_type,
                constructors: vec![Constructor {
                    name: Name::from_string("Sigma.mk"),
                    type_: sigma_mk_type,
                }],
            }],
        };

        self.add_inductive(sigma_decl)?;

        // Sigma.fst : {α : Type u} {β : α → Type v} → Sigma β → α
        let sigma_fst_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let beta_ty = Expr::pi(BinderInfo::Default, alpha.clone(), type_v.clone());
            let (beta_id, beta) = b.fresh_local(beta_ty.clone());
            let sig_ty = Expr::app(Expr::app(sigma_const.clone(), alpha.clone()), beta.clone());
            let (s_id, _s) = b.fresh_local(sig_ty.clone());
            let e = b.mk_pi(s_id, BinderInfo::Default, sig_ty, alpha.clone());
            let e = b.mk_pi(beta_id, BinderInfo::Implicit, beta_ty, e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        let sigma_fst_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let beta_ty = Expr::pi(BinderInfo::Default, alpha.clone(), type_v.clone());
            let (beta_id, beta) = b.fresh_local(beta_ty.clone());
            let sig_ty = Expr::app(Expr::app(sigma_const.clone(), alpha.clone()), beta.clone());
            let (s_id, s) = b.fresh_local(sig_ty.clone());
            let body = Expr::proj(Name::from_string("Sigma"), 0, s);
            let e = b.mk_lam(s_id, BinderInfo::Default, sig_ty, body);
            let e = b.mk_lam(beta_id, BinderInfo::Implicit, beta_ty, e);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Sigma.fst"),
            level_params: vec![u.clone(), v.clone()],
            type_: sigma_fst_type,
            value: sigma_fst_value,
            is_reducible: true,
        })?;

        // Sigma.snd : {α : Type u} {β : α → Type v} → (p : Sigma β) → β (Sigma.fst p)
        let sigma_fst_const = Expr::const_(
            Name::from_string("Sigma.fst"),
            vec![Level::param(u.clone()), Level::param(v.clone())],
        );

        let sigma_snd_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let beta_ty = Expr::pi(BinderInfo::Default, alpha.clone(), type_v.clone());
            let (beta_id, beta) = b.fresh_local(beta_ty.clone());
            let sig_ty = Expr::app(Expr::app(sigma_const.clone(), alpha.clone()), beta.clone());
            let (s_id, s) = b.fresh_local(sig_ty.clone());
            let fst_app = Expr::app(
                Expr::app(
                    Expr::app(sigma_fst_const.clone(), alpha.clone()),
                    beta.clone(),
                ),
                s.clone(),
            );
            let result = Expr::app(beta.clone(), fst_app);
            let e = b.mk_pi(s_id, BinderInfo::Default, sig_ty, result);
            let e = b.mk_pi(beta_id, BinderInfo::Implicit, beta_ty, e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        let sigma_snd_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let beta_ty = Expr::pi(BinderInfo::Default, alpha.clone(), type_v.clone());
            let (beta_id, beta) = b.fresh_local(beta_ty.clone());
            let sig_ty = Expr::app(Expr::app(sigma_const.clone(), alpha.clone()), beta.clone());
            let (s_id, s) = b.fresh_local(sig_ty.clone());
            let body = Expr::proj(Name::from_string("Sigma"), 1, s);
            let e = b.mk_lam(s_id, BinderInfo::Default, sig_ty, body);
            let e = b.mk_lam(beta_id, BinderInfo::Implicit, beta_ty, e);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Sigma.snd"),
            level_params: vec![u.clone(), v.clone()],
            type_: sigma_snd_type,
            value: sigma_snd_value,
            is_reducible: true,
        })?;

        self.register_structure_fields(
            Name::from_string("Sigma"),
            vec![Name::from_string("fst"), Name::from_string("snd")],
        )?;

        self.sigma_init = true;
        Ok(())
    }

    /// Check if Sigma has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_sigma()` has been called successfully
    /// ENSURES: Pure function - no side effects
    #[allow(dead_code)] // Used by integration tests
    pub(crate) fn has_sigma(&self) -> bool {
        self.sigma_init
    }

    /// Initialize Subtype structure
    ///
    /// structure Subtype {α : Sort u} (p : α → Prop) : Sort (max 1 u) where
    ///   mk :: (val : α) (property : p val)
    ///
    /// # Contract
    ///
    /// ENSURES: On success, `self.has_subtype() == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())`
    /// ENSURES: Adds Subtype, Subtype.mk, Subtype.val, Subtype.property, Subtype.rec
    pub fn init_subtype(&mut self) -> Result<(), EnvError> {
        if self.subtype_init {
            return Ok(());
        }
        // IMPORT MODE (`suppress_lossy_structure_stubs`, v4.31 retarget
        // 2026-07-05): Clean's seeded `Subtype.mk`/`val`/`property` carry the
        // predicate binder EXPLICITLY — genuine v4.31 has it IMPLICIT — so the
        // seeded family shadows the genuine one and whnf sticks at
        // `Subtype.val` on large submodule-coercion terms
        // (`LieDerivation.ofGradingSum._proof_4`'s 5MB core). Gated INSIDE the
        // fn so all callers are covered; the import-mode reference closure is
        // empty (finset callers are call-site gated at mod.rs, USize's
        // platform-bits caller rides the init_usize gate). The genuine v4.31
        // Subtype inductive + projections import through the checked path.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }

        let u = Name::from_string("u");
        let sort_u = Expr::from_kind(ExprKind::Sort(Level::param(u.clone())));
        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
        let result_sort = Expr::from_kind(ExprKind::Sort(Level::max(
            Level::succ(Level::zero()),
            Level::param(u.clone()),
        )));

        let subtype_const =
            Expr::const_(Name::from_string("Subtype"), vec![Level::param(u.clone())]);

        // Subtype : {α : Sort u} → (α → Prop) → Sort (max 1 u)
        let subtype_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let p_ty = Expr::pi(BinderInfo::Default, alpha.clone(), prop.clone());
            let (p_id, _p) = b.fresh_local(p_ty.clone());
            let e = b.mk_pi(p_id, BinderInfo::Default, p_ty, result_sort.clone());
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };

        // Subtype.mk : {α : Sort u} → {p : α → Prop} → (val : α) → p val → Subtype p
        let subtype_mk_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let p_ty = Expr::pi(BinderInfo::Default, alpha.clone(), prop.clone());
            let (p_id, p) = b.fresh_local(p_ty.clone());
            let (val_id, val) = b.fresh_local(alpha.clone());
            let pval_ty = Expr::app(p.clone(), val.clone());
            let (pv_id, _pv) = b.fresh_local(pval_ty.clone());
            let result = Expr::app(Expr::app(subtype_const.clone(), alpha.clone()), p.clone());
            let e = b.mk_pi(pv_id, BinderInfo::Default, pval_ty, result);
            let e = b.mk_pi(val_id, BinderInfo::Default, alpha, e);
            let e = b.mk_pi(p_id, BinderInfo::Default, p_ty, e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };

        let subtype_decl = InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 2,
            types: vec![InductiveType {
                name: Name::from_string("Subtype"),
                type_: subtype_type,
                constructors: vec![Constructor {
                    name: Name::from_string("Subtype.mk"),
                    type_: subtype_mk_type,
                }],
            }],
        };

        self.add_inductive(subtype_decl)?;

        // Subtype.val : {α : Sort u} {p : α → Prop} → Subtype p → α
        let subtype_val_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let p_ty = Expr::pi(BinderInfo::Default, alpha.clone(), prop.clone());
            let (p_id, p) = b.fresh_local(p_ty.clone());
            let sub_ty = Expr::app(Expr::app(subtype_const.clone(), alpha.clone()), p.clone());
            let (s_id, _s) = b.fresh_local(sub_ty.clone());
            let e = b.mk_pi(s_id, BinderInfo::Default, sub_ty, alpha.clone());
            let e = b.mk_pi(p_id, BinderInfo::Default, p_ty, e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };

        let subtype_val_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let p_ty = Expr::pi(BinderInfo::Default, alpha.clone(), prop.clone());
            let (p_id, p) = b.fresh_local(p_ty.clone());
            let sub_ty = Expr::app(Expr::app(subtype_const.clone(), alpha.clone()), p.clone());
            let (s_id, s) = b.fresh_local(sub_ty.clone());
            let body = Expr::proj(Name::from_string("Subtype"), 0, s);
            let e = b.mk_lam(s_id, BinderInfo::Default, sub_ty, body);
            let e = b.mk_lam(p_id, BinderInfo::Default, p_ty, e);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Subtype.val"),
            level_params: vec![u.clone()],
            type_: subtype_val_type,
            value: subtype_val_value,
            is_reducible: true,
        })?;

        // Subtype.property : {α : Sort u} {p : α → Prop} → (h : Subtype p) → p h.val
        let subtype_val_const = Expr::const_(
            Name::from_string("Subtype.val"),
            vec![Level::param(u.clone())],
        );

        let subtype_property_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let p_ty = Expr::pi(BinderInfo::Default, alpha.clone(), prop.clone());
            let (p_id, p) = b.fresh_local(p_ty.clone());
            let sub_ty = Expr::app(Expr::app(subtype_const.clone(), alpha.clone()), p.clone());
            let (s_id, s) = b.fresh_local(sub_ty.clone());
            let h_val = Expr::app(
                Expr::app(
                    Expr::app(subtype_val_const.clone(), alpha.clone()),
                    p.clone(),
                ),
                s.clone(),
            );
            let result = Expr::app(p.clone(), h_val);
            let e = b.mk_pi(s_id, BinderInfo::Default, sub_ty, result);
            let e = b.mk_pi(p_id, BinderInfo::Default, p_ty, e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };

        let subtype_property_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let p_ty = Expr::pi(BinderInfo::Default, alpha.clone(), prop.clone());
            let (p_id, p) = b.fresh_local(p_ty.clone());
            let sub_ty = Expr::app(Expr::app(subtype_const.clone(), alpha.clone()), p.clone());
            let (s_id, s) = b.fresh_local(sub_ty.clone());
            let body = Expr::proj(Name::from_string("Subtype"), 1, s);
            let e = b.mk_lam(s_id, BinderInfo::Default, sub_ty, body);
            let e = b.mk_lam(p_id, BinderInfo::Default, p_ty, e);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Subtype.property"),
            level_params: vec![u.clone()],
            type_: subtype_property_type,
            value: subtype_property_value,
            is_reducible: true,
        })?;

        self.register_structure_fields(
            Name::from_string("Subtype"),
            vec![Name::from_string("val"), Name::from_string("property")],
        )?;

        self.subtype_init = true;
        Ok(())
    }

    /// Check if Subtype has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_subtype()` has been called successfully
    /// ENSURES: Pure function - no side effects
    #[allow(dead_code)] // Used by integration tests
    pub(crate) fn has_subtype(&self) -> bool {
        self.subtype_init
    }
}

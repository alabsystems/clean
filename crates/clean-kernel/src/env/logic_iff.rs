// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Iff (logical equivalence) structure and derived definitions
//!
//! This module contains:
//! - Iff inductive type with Iff.intro constructor
//! - Iff.mp, Iff.mpr (forward/backward implication)
//! - Iff.rfl, Iff.symm, Iff.trans
//!
//! Split from logic.rs for #307.

use super::decl_builder::EnvDeclBuilder;
use super::*;

impl Environment {
    /// Initialize Iff (logical equivalence) structure
    ///
    /// Iff : Prop → Prop → Prop
    /// structure Iff (a b : Prop) : Prop where
    ///   intro :: (mp : a → b) (mpr : b → a)
    ///
    /// This adds:
    /// - Iff inductive type with Iff.intro constructor
    /// - Iff.rec (auto-generated)
    /// - Iff.mp : {a b : Prop} → Iff a b → a → b
    /// - Iff.mpr : {a b : Prop} → Iff a b → b → a
    ///
    /// # Contract
    ///
    /// ENSURES: On success, `self.has_iff() == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())`
    /// ENSURES: Adds Iff, Iff.intro, Iff.mp, Iff.mpr, Iff.rec, etc.
    pub fn init_iff(&mut self) -> Result<(), EnvError> {
        if self.iff_init {
            return Ok(());
        }

        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
        let iff_const = Expr::const_(Name::from_string("Iff"), vec![]);

        // Iff type: Prop → Prop → Prop (no bvars needed — non-dependent)
        let iff_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, _) = b.fresh_local(prop.clone());
            let (b_id, _) = b.fresh_local(prop.clone());
            let r = prop.clone();
            let r = b.mk_pi(b_id, BinderInfo::Default, prop.clone(), r);
            let r = b.mk_pi(a_id, BinderInfo::Default, prop.clone(), r);
            b.finish(r)
        };

        // Iff.intro constructor type:
        // Π {a : Prop}, Π {b : Prop}, Π (mp : a → b), Π (mpr : b → a), Iff a b
        let intro_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a_var) = b.fresh_local(prop.clone());
            let (bb_id, bb_var) = b.fresh_local(prop.clone());
            // mp : a → b
            let a_to_b = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x_id, _) = c.fresh_local(a_var.clone());
                c.mk_pi(x_id, BinderInfo::Default, a_var.clone(), bb_var.clone())
            };
            let (mp_id, _) = b.fresh_local(a_to_b.clone());
            // mpr : b → a
            let b_to_a = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x_id, _) = c.fresh_local(bb_var.clone());
                c.mk_pi(x_id, BinderInfo::Default, bb_var.clone(), a_var.clone())
            };
            let (mpr_id, _) = b.fresh_local(b_to_a.clone());
            let result = Expr::app(Expr::app(iff_const.clone(), a_var), bb_var);
            let r = result;
            let r = b.mk_pi(mpr_id, BinderInfo::Default, b_to_a, r);
            let r = b.mk_pi(mp_id, BinderInfo::Default, a_to_b, r);
            let r = b.mk_pi(bb_id, BinderInfo::Implicit, prop.clone(), r);
            let r = b.mk_pi(a_id, BinderInfo::Implicit, prop.clone(), r);
            b.finish(r)
        };

        let iff_decl = InductiveDecl {
            level_params: vec![],
            num_params: 2,
            types: vec![InductiveType {
                name: Name::from_string("Iff"),
                type_: iff_type,
                constructors: vec![Constructor {
                    name: Name::from_string("Iff.intro"),
                    type_: intro_type,
                }],
            }],
        };

        self.add_inductive(iff_decl)?;

        let iff_rec_const = Expr::const_(Name::from_string("Iff.rec"), vec![Level::zero()]);
        let iff_intro_const = Expr::const_(Name::from_string("Iff.intro"), vec![]);
        let iff_mp_const = Expr::const_(Name::from_string("Iff.mp"), vec![]);
        let iff_mpr_const = Expr::const_(Name::from_string("Iff.mpr"), vec![]);

        // Iff.mp : {a b : Prop} → Iff a b → a → b
        let mp_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a_var) = b.fresh_local(prop.clone());
            let (bb_id, bb_var) = b.fresh_local(prop.clone());
            let iff_ab = Expr::app(Expr::app(iff_const.clone(), a_var.clone()), bb_var.clone());
            let (h_id, _) = b.fresh_local(iff_ab.clone());
            let (ha_id, _) = b.fresh_local(a_var.clone());
            let r = bb_var;
            let r = b.mk_pi(ha_id, BinderInfo::Default, a_var.clone(), r);
            let r = b.mk_pi(h_id, BinderInfo::Default, iff_ab, r);
            let r = b.mk_pi(bb_id, BinderInfo::Implicit, prop.clone(), r);
            let r = b.mk_pi(a_id, BinderInfo::Implicit, prop.clone(), r);
            b.finish(r)
        };

        // Iff.mp value: λ {a b} h ha, Iff.rec a b motive minor h ha
        let mp_value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a_var) = b.fresh_local(prop.clone());
            let (bb_id, bb_var) = b.fresh_local(prop.clone());
            let iff_ab = Expr::app(Expr::app(iff_const.clone(), a_var.clone()), bb_var.clone());
            let (h_id, h_var) = b.fresh_local(iff_ab.clone());
            let (ha_id, ha_var) = b.fresh_local(a_var.clone());
            // motive = λ (_ : Iff a b), a → b
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (m_id, _) = c.fresh_local(iff_ab.clone());
                let a_to_b_inner = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (x_id, _) = d.fresh_local(a_var.clone());
                    d.mk_pi(x_id, BinderInfo::Default, a_var.clone(), bb_var.clone())
                };
                c.mk_lam(m_id, BinderInfo::Default, iff_ab.clone(), a_to_b_inner)
            };
            // minor = λ (mp : a → b) (mpr : b → a), mp
            let minor = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let a_to_b_ty = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (x_id, _) = d.fresh_local(a_var.clone());
                    d.mk_pi(x_id, BinderInfo::Default, a_var.clone(), bb_var.clone())
                };
                let (mp_id, mp_var) = c.fresh_local(a_to_b_ty.clone());
                let b_to_a_ty = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (x_id, _) = d.fresh_local(bb_var.clone());
                    d.mk_pi(x_id, BinderInfo::Default, bb_var.clone(), a_var.clone())
                };
                let (mpr_id, _) = c.fresh_local(b_to_a_ty.clone());
                let r = mp_var;
                let r = c.mk_lam(mpr_id, BinderInfo::Default, b_to_a_ty, r);
                let r = c.mk_lam(mp_id, BinderInfo::Default, a_to_b_ty, r);
                c.finish_child(r)
            };
            // Iff.rec a b motive minor h ha
            let body = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(
                                Expr::app(iff_rec_const.clone(), a_var.clone()),
                                bb_var.clone(),
                            ),
                            motive,
                        ),
                        minor,
                    ),
                    h_var,
                ),
                ha_var,
            );
            let r = body;
            let r = b.mk_lam(ha_id, BinderInfo::Default, a_var.clone(), r);
            let r = b.mk_lam(h_id, BinderInfo::Default, iff_ab, r);
            let r = b.mk_lam(bb_id, BinderInfo::Implicit, prop.clone(), r);
            let r = b.mk_lam(a_id, BinderInfo::Implicit, prop.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Iff.mp"),
            level_params: vec![],
            type_: mp_type,
            value: mp_value,
            is_reducible: true,
        })?;

        // Iff.mpr : {a b : Prop} → Iff a b → b → a
        let mpr_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a_var) = b.fresh_local(prop.clone());
            let (bb_id, bb_var) = b.fresh_local(prop.clone());
            let iff_ab = Expr::app(Expr::app(iff_const.clone(), a_var.clone()), bb_var.clone());
            let (h_id, _) = b.fresh_local(iff_ab.clone());
            let (hb_id, _) = b.fresh_local(bb_var.clone());
            let r = a_var.clone();
            let r = b.mk_pi(hb_id, BinderInfo::Default, bb_var.clone(), r);
            let r = b.mk_pi(h_id, BinderInfo::Default, iff_ab, r);
            let r = b.mk_pi(bb_id, BinderInfo::Implicit, prop.clone(), r);
            let r = b.mk_pi(a_id, BinderInfo::Implicit, prop.clone(), r);
            b.finish(r)
        };

        let mpr_value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a_var) = b.fresh_local(prop.clone());
            let (bb_id, bb_var) = b.fresh_local(prop.clone());
            let iff_ab = Expr::app(Expr::app(iff_const.clone(), a_var.clone()), bb_var.clone());
            let (h_id, h_var) = b.fresh_local(iff_ab.clone());
            let (hb_id, hb_var) = b.fresh_local(bb_var.clone());
            // motive = λ (_ : Iff a b), b → a
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (m_id, _) = c.fresh_local(iff_ab.clone());
                let b_to_a_inner = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (x_id, _) = d.fresh_local(bb_var.clone());
                    d.mk_pi(x_id, BinderInfo::Default, bb_var.clone(), a_var.clone())
                };
                c.mk_lam(m_id, BinderInfo::Default, iff_ab.clone(), b_to_a_inner)
            };
            // minor = λ (mp : a → b) (mpr : b → a), mpr
            let minor = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let a_to_b_ty = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (x_id, _) = d.fresh_local(a_var.clone());
                    d.mk_pi(x_id, BinderInfo::Default, a_var.clone(), bb_var.clone())
                };
                let (mp_id, _) = c.fresh_local(a_to_b_ty.clone());
                let b_to_a_ty = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (x_id, _) = d.fresh_local(bb_var.clone());
                    d.mk_pi(x_id, BinderInfo::Default, bb_var.clone(), a_var.clone())
                };
                let (mpr_id, mpr_var) = c.fresh_local(b_to_a_ty.clone());
                let r = mpr_var;
                let r = c.mk_lam(mpr_id, BinderInfo::Default, b_to_a_ty, r);
                let r = c.mk_lam(mp_id, BinderInfo::Default, a_to_b_ty, r);
                c.finish_child(r)
            };
            let body = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(
                                Expr::app(iff_rec_const.clone(), a_var.clone()),
                                bb_var.clone(),
                            ),
                            motive,
                        ),
                        minor,
                    ),
                    h_var,
                ),
                hb_var,
            );
            let r = body;
            let r = b.mk_lam(hb_id, BinderInfo::Default, bb_var.clone(), r);
            let r = b.mk_lam(h_id, BinderInfo::Default, iff_ab, r);
            let r = b.mk_lam(bb_id, BinderInfo::Implicit, prop.clone(), r);
            let r = b.mk_lam(a_id, BinderInfo::Implicit, prop.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Iff.mpr"),
            level_params: vec![],
            type_: mpr_type,
            value: mpr_value,
            is_reducible: true,
        })?;

        // Iff.rfl : {a : Prop} → Iff a a
        let iff_rfl_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a_var) = b.fresh_local(prop.clone());
            let r = Expr::app(Expr::app(iff_const.clone(), a_var.clone()), a_var);
            let r = b.mk_pi(a_id, BinderInfo::Implicit, prop.clone(), r);
            b.finish(r)
        };

        let iff_rfl_value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a_var) = b.fresh_local(prop.clone());
            // id function: λ (h : a), h
            let id_fn = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (h_id, h_var) = c.fresh_local(a_var.clone());
                c.mk_lam(h_id, BinderInfo::Default, a_var.clone(), h_var)
            };
            // Iff.intro a a id id
            let body = Expr::app(
                Expr::app(
                    Expr::app(Expr::app(iff_intro_const.clone(), a_var.clone()), a_var),
                    id_fn.clone(),
                ),
                id_fn,
            );
            let r = b.mk_lam(a_id, BinderInfo::Implicit, prop.clone(), body);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Iff.rfl"),
            level_params: vec![],
            type_: iff_rfl_type,
            value: iff_rfl_value,
            is_reducible: true,
        })?;

        // Iff.symm : {a b : Prop} → Iff a b → Iff b a
        let iff_symm_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a_var) = b.fresh_local(prop.clone());
            let (bb_id, bb_var) = b.fresh_local(prop.clone());
            let iff_ab = Expr::app(Expr::app(iff_const.clone(), a_var.clone()), bb_var.clone());
            let (h_id, _) = b.fresh_local(iff_ab.clone());
            let iff_ba = Expr::app(Expr::app(iff_const.clone(), bb_var), a_var);
            let r = iff_ba;
            let r = b.mk_pi(h_id, BinderInfo::Default, iff_ab, r);
            let r = b.mk_pi(bb_id, BinderInfo::Implicit, prop.clone(), r);
            let r = b.mk_pi(a_id, BinderInfo::Implicit, prop.clone(), r);
            b.finish(r)
        };

        let iff_symm_value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a_var) = b.fresh_local(prop.clone());
            let (bb_id, bb_var) = b.fresh_local(prop.clone());
            let iff_ab = Expr::app(Expr::app(iff_const.clone(), a_var.clone()), bb_var.clone());
            let (h_id, h_var) = b.fresh_local(iff_ab.clone());
            // Iff.intro b a (Iff.mpr {a} {b} h) (Iff.mp {a} {b} h)
            let body = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(iff_intro_const.clone(), bb_var.clone()),
                        a_var.clone(),
                    ),
                    Expr::app(
                        Expr::app(
                            Expr::app(iff_mpr_const.clone(), a_var.clone()),
                            bb_var.clone(),
                        ),
                        h_var.clone(),
                    ),
                ),
                Expr::app(
                    Expr::app(Expr::app(iff_mp_const.clone(), a_var), bb_var),
                    h_var,
                ),
            );
            // Note: bb_var was moved above, rebind for mk_lam type
            let r = body;
            let r = b.mk_lam(h_id, BinderInfo::Default, iff_ab, r);
            let r = b.mk_lam(bb_id, BinderInfo::Implicit, prop.clone(), r);
            let r = b.mk_lam(a_id, BinderInfo::Implicit, prop.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Theorem {
            name: Name::from_string("Iff.symm"),
            level_params: vec![],
            type_: iff_symm_type,
            value: iff_symm_value,
        })?;

        // Iff.trans : {a b c : Prop} → Iff a b → Iff b c → Iff a c
        let iff_trans_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a_var) = b.fresh_local(prop.clone());
            let (bb_id, bb_var) = b.fresh_local(prop.clone());
            let (c_id, c_var) = b.fresh_local(prop.clone());
            let iff_ab = Expr::app(Expr::app(iff_const.clone(), a_var.clone()), bb_var.clone());
            let (h1_id, _) = b.fresh_local(iff_ab.clone());
            let iff_bc = Expr::app(Expr::app(iff_const.clone(), bb_var), c_var.clone());
            let (h2_id, _) = b.fresh_local(iff_bc.clone());
            let iff_ac = Expr::app(Expr::app(iff_const.clone(), a_var), c_var);
            let r = iff_ac;
            let r = b.mk_pi(h2_id, BinderInfo::Default, iff_bc, r);
            let r = b.mk_pi(h1_id, BinderInfo::Default, iff_ab, r);
            let r = b.mk_pi(c_id, BinderInfo::Implicit, prop.clone(), r);
            let r = b.mk_pi(bb_id, BinderInfo::Implicit, prop.clone(), r);
            let r = b.mk_pi(a_id, BinderInfo::Implicit, prop.clone(), r);
            b.finish(r)
        };

        let iff_trans_value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a_var) = b.fresh_local(prop.clone());
            let (bb_id, bb_var) = b.fresh_local(prop.clone());
            let (c_id, c_var) = b.fresh_local(prop.clone());
            let iff_ab = Expr::app(Expr::app(iff_const.clone(), a_var.clone()), bb_var.clone());
            let (h1_id, h1_var) = b.fresh_local(iff_ab.clone());
            let iff_bc = Expr::app(Expr::app(iff_const.clone(), bb_var.clone()), c_var.clone());
            let (h2_id, h2_var) = b.fresh_local(iff_bc.clone());
            // forward = λ (ha : a), Iff.mp h2 (Iff.mp h1 ha)
            let forward = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (ha_id, ha_var) = c.fresh_local(a_var.clone());
                let mp_h1_ha = Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(iff_mp_const.clone(), a_var.clone()),
                            bb_var.clone(),
                        ),
                        h1_var.clone(),
                    ),
                    ha_var,
                );
                let body = Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(iff_mp_const.clone(), bb_var.clone()),
                            c_var.clone(),
                        ),
                        h2_var.clone(),
                    ),
                    mp_h1_ha,
                );
                c.mk_lam(ha_id, BinderInfo::Default, a_var.clone(), body)
            };
            // backward = λ (hc : c), Iff.mpr h1 (Iff.mpr h2 hc)
            let backward = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (hc_id, hc_var) = c.fresh_local(c_var.clone());
                let mpr_h2_hc = Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(iff_mpr_const.clone(), bb_var.clone()),
                            c_var.clone(),
                        ),
                        h2_var,
                    ),
                    hc_var,
                );
                let body = Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(iff_mpr_const.clone(), a_var.clone()),
                            bb_var.clone(),
                        ),
                        h1_var,
                    ),
                    mpr_h2_hc,
                );
                c.mk_lam(hc_id, BinderInfo::Default, c_var.clone(), body)
            };
            // Iff.intro a c forward backward
            let body = Expr::app(
                Expr::app(
                    Expr::app(Expr::app(iff_intro_const.clone(), a_var), c_var),
                    forward,
                ),
                backward,
            );
            let r = body;
            let r = b.mk_lam(h2_id, BinderInfo::Default, iff_bc, r);
            let r = b.mk_lam(h1_id, BinderInfo::Default, iff_ab, r);
            let r = b.mk_lam(c_id, BinderInfo::Implicit, prop.clone(), r);
            let r = b.mk_lam(bb_id, BinderInfo::Implicit, prop.clone(), r);
            let r = b.mk_lam(a_id, BinderInfo::Implicit, prop.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Theorem {
            name: Name::from_string("Iff.trans"),
            level_params: vec![],
            type_: iff_trans_type,
            value: iff_trans_value,
        })?;

        self.iff_init = true;
        Ok(())
    }

    /// Check if Iff structure has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_iff()` has been called successfully
    /// ENSURES: Pure function - no side effects
    pub(crate) fn has_iff(&self) -> bool {
        self.iff_init
    }
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean 4.8.0 `Init` constants that Clean's prelude supplies, with Lean's
//! statements and constructive, kernel-checked proofs:
//!
//! ```text
//! Bool.of_not_eq_true  : ∀ {b : Bool}, ¬b = true → b = false
//! Bool.of_not_eq_false : ∀ {b : Bool}, ¬b = false → b = true
//! class Subsingleton (α : Sort u) : Prop where
//!   intro :: allEq : ∀ (a b : α), a = b
//! protected theorem Subsingleton.elim : ∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
//! instance instSubsingletonDecidable (p : Prop) : Subsingleton (Decidable p)
//! theorem cast_cast.{u_1} : ∀ {α β γ : Sort u_1} (ha : α = β) (hb : β = γ) (a : α),
//!   cast hb (cast ha a) = cast (ha.trans hb) a
//! ```
//!
//! (statements as Lean 4.8.0 prints them, `#check`/`#print`, measured
//! 2026-09-27).
//!
//! WHY THEY ARE HERE. A user file cannot declare a Lean core name: Lean
//! refuses it ("already declared"), and so does Clean
//! (`clean_elab::lean_core_names`). Clean's `simp` (the `Bool` disequality
//! rule: `h : b ≠ true` rewrites `b` to `false`) and `congr` (closing
//! differing `Decidable` instances) look these constants up by name, and the
//! only way a prelude-only file had them was to declare them itself — a
//! redeclaration Lean refuses. Supplying them keeps that capability, and
//! each use was measured against Lean 4.8.0, which proves the same goals
//! with the same tactics WITHOUT any declaration of these names (`simp only
//! [h]` on `b ≠ true` / `¬ b = false`, `congr` on differing `Decidable`
//! instances). `cast_cast` is a lemma the M-type graduation corpus
//! (`data/graduation/clean-mtype/proof/MType.lean`) used to prove itself
//! under Lean's name; it now cites this one, as it would under Lean.
//!
//! NOT supplied, deliberately, although test fixtures used to declare them:
//!
//! * `dif_pos`/`dif_neg`: Clean's `simp` collapses a `dite` through them even
//!   under `simp only [h]`, where Lean 4.8.0 leaves `if h : True then … else
//!   …` unsolved (measured) because `dite_true` is not in the set. Supplying
//!   them would make Clean accept proofs Lean refuses.
//! * `forall_congr`: with it, `simp` rewrites under a `Prop` binder, which
//!   routes `cert_mathverse` (and through it `grind`) into the `zify`
//!   rewrite whose proof cites the cast-overlay axiom `Nat.cast_eq_prop`
//!   that the checked environment does not hold ("Unknown constant", the
//!   same failure `intro h; zify; omega` already has on db37ea99b). `grind`
//!   then stopped closing `a = b ↔ b = a` (measured 2026-09-27). That
//!   overlay defect is not this module's to fix.
//!
//! IMPORT MODE seeds none of them: a file that imports real Lean `.olean`s
//! gets Lean's own declarations through the checked import path.
//!
//! Every proof is axiom-free: `Decidable.rec`/`Bool.rec`/`Subsingleton.rec`/
//! `Eq.rec` casework, `Eq.refl` and `absurd`.

use super::decl_builder::EnvDeclBuilder;
use super::{
    Constructor, Declaration, EnvError, Environment, InductiveDecl, InductiveType, KernelClassInfo,
    KernelInstanceInfo,
};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

fn konst(name: &str, levels: Vec<Level>) -> Expr {
    Expr::const_(Name::from_string(name), levels)
}

impl Environment {
    /// Register every constant of this module. Idempotent; a no-op in import
    /// mode (see the module documentation).
    pub(crate) fn register_lean_core_supply(&mut self) -> Result<(), EnvError> {
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        self.register_bool_of_not_eq()?;
        self.register_subsingleton()?;
        self.register_cast_cast()?;
        Ok(())
    }

    /// `cast_cast.{u_1} : ∀ {α β γ : Sort u_1} (ha : α = β) (hb : β = γ)
    /// (a : α), cast hb (cast ha a) = cast (Eq.trans ha hb) a`, by `Eq.rec`
    /// on `hb` (Lean: `subst ha; subst hb; rfl`): at `hb := rfl` both sides
    /// are `cast ha a` (ι-reduction of `cast rfl`, proof irrelevance for
    /// `Eq.trans ha rfl`).
    fn register_cast_cast(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("cast_cast");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        let u = Name::from_string("u_1");
        let lu = Level::param(u.clone());
        let sort_u = Expr::sort(lu.clone());
        let sort_eq = |x: Expr, y: Expr| {
            Expr::apps(
                konst("Eq", vec![Level::succ(lu.clone())]),
                [sort_u.clone(), x, y],
            )
        };
        let cast = |x: Expr, y: Expr, h: Expr, v: Expr| {
            Expr::apps(konst("cast", vec![lu.clone()]), [x, y, h, v])
        };
        let trans = |x: Expr, y: Expr, z: Expr, h1: Expr, h2: Expr| {
            Expr::apps(
                konst("Eq.trans", vec![Level::succ(lu.clone())]),
                [sort_u.clone(), x, y, z, h1, h2],
            )
        };
        // `cast hb (cast ha a) = cast (Eq.trans ha hb) a` at codomain `g`.
        let stmt = |alpha: &Expr, beta: &Expr, g: &Expr, ha: &Expr, hb: &Expr, a: &Expr| {
            let lhs = cast(
                beta.clone(),
                g.clone(),
                hb.clone(),
                cast(alpha.clone(), beta.clone(), ha.clone(), a.clone()),
            );
            let rhs = cast(
                alpha.clone(),
                g.clone(),
                trans(
                    alpha.clone(),
                    beta.clone(),
                    g.clone(),
                    ha.clone(),
                    hb.clone(),
                ),
                a.clone(),
            );
            Expr::apps(konst("Eq", vec![lu.clone()]), [g.clone(), lhs, rhs])
        };
        // The telescope `{α β γ : Sort u_1} (ha : α = β) (hb : β = γ) (a : α)`
        // closed over `body` as a Π (`value == false`) or a λ.
        let build = |value: bool| -> Expr {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let (beta_id, beta) = b.fresh_local(sort_u.clone());
            let (gamma_id, gamma) = b.fresh_local(sort_u.clone());
            let ha_ty = sort_eq(alpha.clone(), beta.clone());
            let (ha_id, ha) = b.fresh_local(ha_ty.clone());
            let hb_ty = sort_eq(beta.clone(), gamma.clone());
            let (hb_id, hb) = b.fresh_local(hb_ty.clone());
            let (a_id, a) = b.fresh_local(alpha.clone());
            let body = if value {
                // fun (g : Sort u_1) (h : β = g) => <stmt at g, h>
                let motive = {
                    let mut d = EnvDeclBuilder::child_of(&b);
                    let (g_id, g) = d.fresh_local(sort_u.clone());
                    let h_ty = sort_eq(beta.clone(), g.clone());
                    let (h_id, h) = d.fresh_local(h_ty.clone());
                    let r = stmt(&alpha, &beta, &g, &ha, &h, &a);
                    let r = d.mk_lam(h_id, BinderInfo::Default, h_ty, r);
                    d.finish_child(d.mk_lam(g_id, BinderInfo::Default, sort_u.clone(), r))
                };
                let minor = Expr::apps(
                    konst("Eq.refl", vec![lu.clone()]),
                    [
                        beta.clone(),
                        cast(alpha.clone(), beta.clone(), ha.clone(), a.clone()),
                    ],
                );
                // Eq.rec.{0, u_1+1} {Sort u_1} {β} {motive} minor {γ} hb
                Expr::apps(
                    konst("Eq.rec", vec![Level::zero(), Level::succ(lu.clone())]),
                    [
                        sort_u.clone(),
                        beta.clone(),
                        motive,
                        minor,
                        gamma.clone(),
                        hb.clone(),
                    ],
                )
            } else {
                stmt(&alpha, &beta, &gamma, &ha, &hb, &a)
            };
            let close = |id, bi, ty, r| {
                if value {
                    b.mk_lam(id, bi, ty, r)
                } else {
                    b.mk_pi(id, bi, ty, r)
                }
            };
            let r = close(a_id, BinderInfo::Default, alpha.clone(), body);
            let r = close(hb_id, BinderInfo::Default, hb_ty, r);
            let r = close(ha_id, BinderInfo::Default, ha_ty, r);
            let r = close(gamma_id, BinderInfo::Implicit, sort_u.clone(), r);
            let r = close(beta_id, BinderInfo::Implicit, sort_u.clone(), r);
            b.finish(close(alpha_id, BinderInfo::Implicit, sort_u.clone(), r))
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![u],
            type_: build(false),
            value: build(true),
        })
    }

    /// `Bool.of_not_eq_true` / `Bool.of_not_eq_false`, by `Bool.rec` as
    /// Lean's `| true, h => absurd rfl h | false, _ => rfl` (and its twin).
    fn register_bool_of_not_eq(&mut self) -> Result<(), EnvError> {
        self.init_bool()?;
        let one = Level::succ(Level::zero());
        let bool_c = konst("Bool", vec![]);
        let tt = konst("Bool.true", vec![]);
        let ff = konst("Bool.false", vec![]);
        let eq =
            |x: Expr, y: Expr| Expr::apps(konst("Eq", vec![one.clone()]), [bool_c.clone(), x, y]);
        let not = |x: Expr| Expr::app(konst("Not", vec![]), x);
        let refl = |x: Expr| Expr::apps(konst("Eq.refl", vec![one.clone()]), [bool_c.clone(), x]);

        // (name, the literal ruled out, the other literal)
        for (name, lit, other) in [
            ("Bool.of_not_eq_true", tt.clone(), ff.clone()),
            ("Bool.of_not_eq_false", ff.clone(), tt.clone()),
        ] {
            if self.get_const(&Name::from_string(name)).is_some() {
                continue;
            }
            // `¬ b = lit → b = other`
            let stmt = |b: Expr| {
                Expr::pi(
                    BinderInfo::Default,
                    not(eq(b.clone(), lit.clone())),
                    eq(b, other.clone()),
                )
            };
            let ty = {
                let mut b = EnvDeclBuilder::new();
                let (x_id, x) = b.fresh_local(bool_c.clone());
                b.finish(b.mk_pi(x_id, BinderInfo::Implicit, bool_c.clone(), stmt(x)))
            };
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (x_id, x) = b.fresh_local(bool_c.clone());
                let motive = {
                    let mut d = EnvDeclBuilder::child_of(&b);
                    let (y_id, y) = d.fresh_local(bool_c.clone());
                    d.finish_child(d.mk_lam(y_id, BinderInfo::Default, bool_c.clone(), stmt(y)))
                };
                // The minor for the constructor `k`: `k` is `lit` (absurd) or
                // `other` (reflexivity).
                let minor = |k: &Expr| {
                    let mut d = EnvDeclBuilder::child_of(&b);
                    let hyp_ty = not(eq(k.clone(), lit.clone()));
                    let (h_id, h) = d.fresh_local(hyp_ty.clone());
                    let proof = if *k == lit {
                        Expr::apps(
                            konst("absurd", vec![Level::zero()]),
                            [
                                eq(lit.clone(), lit.clone()),
                                eq(lit.clone(), other.clone()),
                                refl(lit.clone()),
                                h,
                            ],
                        )
                    } else {
                        refl(other.clone())
                    };
                    d.finish_child(d.mk_lam(h_id, BinderInfo::Default, hyp_ty, proof))
                };
                // Bool.rec motive (false case) (true case) x
                let body = Expr::apps(
                    konst("Bool.rec", vec![Level::zero()]),
                    [motive, minor(&ff), minor(&tt), x],
                );
                b.finish(b.mk_lam(x_id, BinderInfo::Implicit, bool_c.clone(), body))
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string(name),
                level_params: vec![],
                type_: ty,
                value,
            })?;
        }
        Ok(())
    }

    /// `class Subsingleton`, its projection `allEq`, the protected
    /// `Subsingleton.elim`, and the instance `instSubsingletonDecidable`.
    fn register_subsingleton(&mut self) -> Result<(), EnvError> {
        if self.get_const(&Name::from_string("Subsingleton")).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_decidable()?;
        let u = Name::from_string("u");
        let lu = Level::param(u.clone());
        let prop = Expr::sort(Level::zero());
        let sort_u = Expr::sort(lu.clone());
        let subsingleton = |alpha: Expr| Expr::app(konst("Subsingleton", vec![lu.clone()]), alpha);
        // `∀ (a b : α), a = b`
        let all_eq = |outer: &EnvDeclBuilder, alpha: &Expr| {
            let mut d = EnvDeclBuilder::child_of(outer);
            let (a_id, a) = d.fresh_local(alpha.clone());
            let (b_id, bb) = d.fresh_local(alpha.clone());
            let eq = Expr::apps(konst("Eq", vec![lu.clone()]), [alpha.clone(), a, bb]);
            let r = d.mk_pi(b_id, BinderInfo::Default, alpha.clone(), eq);
            d.finish_child(d.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r))
        };

        // Subsingleton.intro : {α : Sort u} → (∀ (a b : α), a = b) → Subsingleton α
        let intro_ty = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let field = all_eq(&b, &alpha);
            let (f_id, _f) = b.fresh_local(field.clone());
            let r = b.mk_pi(f_id, BinderInfo::Default, field, subsingleton(alpha));
            b.finish(b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), r))
        };
        self.add_inductive(InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 1,
            types: vec![InductiveType {
                name: Name::from_string("Subsingleton"),
                type_: Expr::pi(BinderInfo::Default, sort_u.clone(), prop.clone()),
                constructors: vec![Constructor {
                    name: Name::from_string("Subsingleton.intro"),
                    type_: intro_ty,
                }],
            }],
        })?;
        self.register_structure_fields(
            Name::from_string("Subsingleton"),
            vec![Name::from_string("allEq")],
        )?;
        self.register_class(KernelClassInfo {
            name: Name::from_string("Subsingleton"),
            num_params: 1,
            out_params: vec![],
            semi_out_params: vec![],
        });

        // `{α : Sort u} → [inst : Subsingleton α] → ∀ (a b : α), a = b`, the
        // type of both the projection and `Subsingleton.elim`; `value` builds
        // `fun {α} [inst] => Subsingleton.rec (fun allEq => allEq) inst` for the
        // projection, and `fun {α} [h] => @Subsingleton.allEq α h` for `elim`.
        let projection = |value: Option<&str>| -> Expr {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let inst_ty = subsingleton(alpha.clone());
            let (inst_id, inst) = b.fresh_local(inst_ty.clone());
            let field = all_eq(&b, &alpha);
            let body = match value {
                None => field,
                Some("allEq") => {
                    let motive = {
                        let mut d = EnvDeclBuilder::child_of(&b);
                        let (w_id, _w) = d.fresh_local(inst_ty.clone());
                        d.finish_child(d.mk_lam(
                            w_id,
                            BinderInfo::Default,
                            inst_ty.clone(),
                            field.clone(),
                        ))
                    };
                    let minor = {
                        let mut d = EnvDeclBuilder::child_of(&b);
                        let (f_id, f) = d.fresh_local(field.clone());
                        d.finish_child(d.mk_lam(f_id, BinderInfo::Default, field.clone(), f))
                    };
                    // Subsingleton eliminates into any sort (one constructor,
                    // every field a proof); its recursor takes the motive's
                    // level first, here `0`.
                    Expr::apps(
                        konst("Subsingleton.rec", vec![Level::zero(), lu.clone()]),
                        [alpha.clone(), motive, minor, inst.clone()],
                    )
                }
                Some(_) => Expr::apps(
                    konst("Subsingleton.allEq", vec![lu.clone()]),
                    [alpha.clone(), inst.clone()],
                ),
            };
            let close = |id, bi, ty, r| {
                if value.is_some() {
                    b.mk_lam(id, bi, ty, r)
                } else {
                    b.mk_pi(id, bi, ty, r)
                }
            };
            let r = close(inst_id, BinderInfo::InstImplicit, inst_ty, body);
            b.finish(close(alpha_id, BinderInfo::Implicit, sort_u.clone(), r))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("Subsingleton.allEq"),
            level_params: vec![u.clone()],
            type_: projection(None),
            value: projection(Some("allEq")),
        })?;
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("Subsingleton.elim"),
            level_params: vec![u.clone()],
            type_: projection(None),
            value: projection(Some("elim")),
        })?;
        self.mark_protected(Name::from_string("Subsingleton.elim"));

        self.register_subsingleton_decidable()
    }

    /// `instSubsingletonDecidable (p : Prop) : Subsingleton (Decidable p)`,
    /// by `Decidable.rec` on both instances as Lean's
    /// `| isTrue _, isTrue _ => rfl | isFalse _, isFalse _ => rfl` with the
    /// mixed cases `absurd`.
    fn register_subsingleton_decidable(&mut self) -> Result<(), EnvError> {
        let one = Level::succ(Level::zero());
        let prop = Expr::sort(Level::zero());
        let false_c = konst("False", vec![]);
        let dec = |p: &Expr| Expr::app(konst("Decidable", vec![]), p.clone());
        let is_true =
            |p: &Expr, h: Expr| Expr::apps(konst("Decidable.isTrue", vec![]), [p.clone(), h]);
        let is_false =
            |p: &Expr, h: Expr| Expr::apps(konst("Decidable.isFalse", vec![]), [p.clone(), h]);
        let eq =
            |p: &Expr, x: Expr, y: Expr| Expr::apps(konst("Eq", vec![one.clone()]), [dec(p), x, y]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(prop.clone());
            let r = Expr::app(konst("Subsingleton", vec![one.clone()]), dec(&p));
            b.finish(b.mk_pi(p_id, BinderInfo::Default, prop.clone(), r))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(prop.clone());
            let not_p = Expr::pi(BinderInfo::Default, p.clone(), false_c.clone());
            // allEq : ∀ (x y : Decidable p), x = y
            //   := fun x => Decidable.rec (motive := fun x => ∀ y, x = y)
            //        (fun f₁ y => Decidable.rec (motive := fun y => isFalse f₁ = y)
            //           (fun _ => rfl) (fun t₂ => absurd t₂ f₁) y)
            //        (fun t₁ y => Decidable.rec (motive := fun y => isTrue t₁ = y)
            //           (fun f₂ => absurd t₁ f₂) (fun _ => rfl) y) x
            let all_eq = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = d.fresh_local(dec(&p));
                // `∀ y, x' = y`
                let forall_eq = |outer: &EnvDeclBuilder, xv: Expr| {
                    let mut e = EnvDeclBuilder::child_of(outer);
                    let (y_id, y) = e.fresh_local(dec(&p));
                    e.finish_child(e.mk_pi(y_id, BinderInfo::Default, dec(&p), eq(&p, xv, y)))
                };
                let outer_motive = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let (w_id, w) = e.fresh_local(dec(&p));
                    let body = forall_eq(&e, w);
                    e.finish_child(e.mk_lam(w_id, BinderInfo::Default, dec(&p), body))
                };
                // The arm for a first instance `first` (built from `hyp`):
                // `fun (hyp : H) (y : Decidable p) => Decidable.rec … y`.
                let arm = |outer: &EnvDeclBuilder, positive: bool| {
                    let mut e = EnvDeclBuilder::child_of(outer);
                    let hyp_ty = if positive { p.clone() } else { not_p.clone() };
                    let (k_id, k) = e.fresh_local(hyp_ty.clone());
                    let first = if positive {
                        is_true(&p, k.clone())
                    } else {
                        is_false(&p, k.clone())
                    };
                    let (y_id, y) = e.fresh_local(dec(&p));
                    let inner_motive = {
                        let mut g = EnvDeclBuilder::child_of(&e);
                        let (v_id, v) = g.fresh_local(dec(&p));
                        let body = eq(&p, first.clone(), v);
                        g.finish_child(g.mk_lam(v_id, BinderInfo::Default, dec(&p), body))
                    };
                    let refl = Expr::apps(
                        konst("Eq.refl", vec![one.clone()]),
                        [dec(&p), first.clone()],
                    );
                    // second instance `isFalse f₂`
                    let false_arm = {
                        let mut g = EnvDeclBuilder::child_of(&e);
                        let (f_id, f) = g.fresh_local(not_p.clone());
                        let proof = if positive {
                            Expr::apps(
                                konst("absurd", vec![Level::zero()]),
                                [
                                    p.clone(),
                                    eq(&p, first.clone(), is_false(&p, f.clone())),
                                    k.clone(),
                                    f,
                                ],
                            )
                        } else {
                            // `isFalse f₁ = isFalse f₂` by proof irrelevance
                            refl.clone()
                        };
                        g.finish_child(g.mk_lam(f_id, BinderInfo::Default, not_p.clone(), proof))
                    };
                    // second instance `isTrue t₂`
                    let true_arm = {
                        let mut g = EnvDeclBuilder::child_of(&e);
                        let (t_id, t) = g.fresh_local(p.clone());
                        let proof = if positive {
                            // `isTrue t₁ = isTrue t₂` by proof irrelevance
                            refl.clone()
                        } else {
                            Expr::apps(
                                konst("absurd", vec![Level::zero()]),
                                [
                                    p.clone(),
                                    eq(&p, first.clone(), is_true(&p, t.clone())),
                                    t,
                                    k.clone(),
                                ],
                            )
                        };
                        g.finish_child(g.mk_lam(t_id, BinderInfo::Default, p.clone(), proof))
                    };
                    let body = Expr::apps(
                        konst("Decidable.rec", vec![Level::zero()]),
                        [p.clone(), inner_motive, false_arm, true_arm, y],
                    );
                    let r = e.mk_lam(y_id, BinderInfo::Default, dec(&p), body);
                    e.finish_child(e.mk_lam(k_id, BinderInfo::Default, hyp_ty, r))
                };
                let body = Expr::apps(
                    konst("Decidable.rec", vec![Level::zero()]),
                    [p.clone(), outer_motive, arm(&d, false), arm(&d, true), x],
                );
                d.finish_child(d.mk_lam(x_id, BinderInfo::Default, dec(&p), body))
            };
            let intro = Expr::apps(
                konst("Subsingleton.intro", vec![one.clone()]),
                [dec(&p), all_eq],
            );
            b.finish(b.mk_lam(p_id, BinderInfo::Default, prop.clone(), intro))
        };
        let name = Name::from_string("instSubsingletonDecidable");
        self.add_decl(Declaration::Definition {
            name: name.clone(),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })?;
        self.register_instance(KernelInstanceInfo {
            name,
            class_name: Name::from_string("Subsingleton"),
            priority: crate::env::LEAN_DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::ExprKind;

    const SUPPLIED: [&str; 8] = [
        "Bool.of_not_eq_true",
        "Bool.of_not_eq_false",
        "Subsingleton",
        "Subsingleton.intro",
        "Subsingleton.allEq",
        "Subsingleton.elim",
        "instSubsingletonDecidable",
        "cast_cast",
    ];

    /// Every supplied constant is in the default prelude, kernel-checked and
    /// axiom-free; import mode seeds none of them.
    #[test]
    fn supplied_core_constants_are_axiom_free_and_default_mode_only() {
        let env = Environment::with_prelude();
        for name in SUPPLIED {
            let n = Name::from_string(name);
            assert!(
                env.get_const(&n).is_some(),
                "`{name}` must be in the prelude"
            );
            let deps = env.axiom_deps(&n).expect("auditable closure");
            assert!(deps.is_empty(), "`{name}` must be axiom-free, got {deps:?}");
        }
        assert!(env.is_protected(&Name::from_string("Subsingleton.elim")));
        let import = Environment::try_with_prelude_for_import().expect("import prelude");
        for name in SUPPLIED {
            assert!(
                import.get_const(&Name::from_string(name)).is_none(),
                "import mode must leave `{name}` to the imported Lean environment"
            );
        }
    }

    /// The binder telescopes are Lean 4.8.0's (`#check` output in the module
    /// documentation): implicit/explicit/instance kinds in order.
    #[test]
    fn supplied_telescopes_match_lean() {
        let env = Environment::with_prelude();
        let spine = |name: &str| {
            let ty = env
                .get_const(&Name::from_string(name))
                .expect(name)
                .type_
                .clone();
            let mut out = Vec::new();
            let mut cur = &ty;
            while let ExprKind::Pi(bd, _, body) = &**cur {
                out.push(bd.info);
                cur = body.as_ref();
            }
            out
        };
        use BinderInfo::{Default as E, Implicit as I, InstImplicit as S};
        assert_eq!(spine("Bool.of_not_eq_true"), vec![I, E]);
        assert_eq!(spine("Bool.of_not_eq_false"), vec![I, E]);
        assert_eq!(spine("Subsingleton.elim"), vec![I, S, E, E]);
        assert_eq!(spine("instSubsingletonDecidable"), vec![E]);
        assert_eq!(spine("cast_cast"), vec![I, I, I, E, E, E]);
    }
}

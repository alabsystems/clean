// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Logical axioms: propext, Quot.sound, funext
//!
//! Connectives and other logic are in:
//! - logic_iff.rs: Iff (logical equivalence)
//! - logic_decidable.rs: Decidable, Classical axioms
//! - logic_true_false.rs: True, False, Not, Ne, absurd
//! - logic_connectives.rs: And, Exists
//!
//! Split from logic.rs for #307.

use super::decl_builder::EnvDeclBuilder;
use super::decl_emit::mk_apps;
use super::*;

impl Environment {
    /// Initialize propositional extensionality axiom — FAITHFUL Lean 4 form:
    ///
    /// ```text
    /// propext : {a b : Prop} → (a ↔ b) → a = b
    /// ```
    ///
    /// This is the EXACT object Lean exports in `Init.Core` (a single `Iff`
    /// argument, no level params). Clean historically registered the de-`Iff`'d
    /// EXPANDED curried form `{a b : Prop} → (a → b) → (b → a) → a = b`, which is
    /// logically equivalent BUT a structurally DIFFERENT object: any `.olean`
    /// term that applies the genuine `propext (h : a ↔ b)` then failed to
    /// type-check against the expanded stub — the kernel saw `expected: Pi(a→b)`,
    /// `inferred: Iff a b`. Virtually every `simp`/`Eq.mpr`-driven `*_iff_*` and
    /// `*.ext` rewrite proof (`Preorder.ext`, `Nat.coprime_pow_left_iff`,
    /// `isCancelMul_iff_forall_isRegular`, …) bottoms out at that mismatch.
    ///
    /// Registering the faithful `Iff`-shaped `propext` removes the divergence:
    /// the imported object IS the one Lean exported. Clean's own hand-built
    /// `propext`-applying prelude proofs were updated to supply the `Iff`
    /// argument via `Iff.intro a b h_mp h_mpr` (same proof content), so they
    /// continue to type-check against this faithful signature.
    ///
    /// # Contract
    ///
    /// REQUIRES: `init_eq()` and `init_iff()` (auto-initialized if not)
    /// ENSURES: On success, `self.has_propext() == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())`
    pub fn init_propext(&mut self) -> Result<(), EnvError> {
        if self.propext_init {
            return Ok(());
        }

        // propext requires Eq to be initialized first.
        if !self.eq_init {
            self.init_eq()?;
        }
        // The faithful `(a ↔ b)` argument type needs the genuine `Iff` structure.
        if !self.iff_init {
            self.init_iff()?;
        }

        let prop = Expr::prop();
        let iff_const = Expr::const_(Name::from_string("Iff"), vec![]);

        // propext : {a b : Prop} → (a ↔ b) → a = b
        let propext_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a_var) = b.fresh_local(prop.clone()); // a : Prop
            let (b_id, b_var) = b.fresh_local(prop.clone()); // b : Prop

            // h : a ↔ b
            let iff_ab = Expr::app(Expr::app(iff_const.clone(), a_var.clone()), b_var.clone());
            let (h_id, _) = b.fresh_local(iff_ab.clone());

            // Eq.{1} Prop a b  (α = Prop : Sort 1, so Eq is at level 1).
            let eq_a_b = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                        prop.clone(),
                    ),
                    a_var.clone(),
                ),
                b_var.clone(),
            );

            let r = eq_a_b;
            let r = b.mk_pi(h_id, BinderInfo::Default, iff_ab, r);
            let r = b.mk_pi(b_id, BinderInfo::Implicit, prop.clone(), r);
            let r = b.mk_pi(a_id, BinderInfo::Implicit, prop.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("propext"),
            level_params: vec![],
            type_: propext_type,
        })?;

        self.propext_init = true;
        Ok(())
    }

    /// Check if propext axiom has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_propext()` has been called successfully
    /// ENSURES: Pure function - no side effects
    #[cfg(test)]
    pub(crate) fn has_propext(&self) -> bool {
        self.propext_init
    }

    /// Initialize Quot.sound axiom
    ///
    /// Quot.sound : {α : Sort u} → {r : α → α → Prop} → {a b : α} → r a b → Quot.mk r a = Quot.mk r b
    ///
    /// This axiom states that related elements have equal quotients.
    ///
    /// # Contract
    ///
    /// REQUIRES: `init_eq()` and `init_quot()` called (auto-initialized if not)
    /// ENSURES: On success, `self.has_quot_sound() == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())`
    pub(crate) fn init_quot_sound(&mut self) -> Result<(), EnvError> {
        if self.quot_sound_init {
            return Ok(());
        }

        // Quot.sound requires Eq and Quot to be initialized first.
        if !self.eq_init {
            self.init_eq()?;
        }
        if !self.quot_init {
            self.init_quot();
        }

        // `init_quot` installs the full quotient bundle — Quot, Quot.mk,
        // Quot.lift, Quot.ind, and Quot.sound — with Quot.sound's type built by
        // `quot::quot_sound_type`. So in the normal path the axiom is already
        // present and must NOT be added again (that would be a DuplicateName
        // error). The guarded fallback below re-adds it from the same canonical
        // type builder only if some future change drops it from the bundle, so
        // the two paths can never drift apart.
        if self.get_const(&Name::from_string("Quot.sound")).is_none() {
            let u = Name::from_string("u");
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Quot.sound"),
                level_params: vec![u.clone()],
                type_: crate::quot::quot_sound_type(&u),
            })?;
        }

        self.quot_sound_init = true;
        Ok(())
    }

    /// Check if Quot.sound axiom has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_quot_sound()` has been called successfully
    /// ENSURES: Pure function - no side effects
    #[cfg(test)]
    pub(crate) fn has_quot_sound(&self) -> bool {
        self.quot_sound_init
    }

    /// Initialize function extensionality
    ///
    /// funext : {α : Sort u} → {β : α → Sort v} → {f g : (x : α) → β x} → (∀ x, f x = g x) → f = g
    ///
    /// This is a CHECKED `Declaration::Theorem`, NOT an axiom: it is derived from
    /// `Quot.sound` exactly as Lean 4 core derives it (Init/Core). Let
    /// `eqv f g := ∀ x, f x = g x` be extensional equality on `∀ x, β x`, and
    /// `extfunApp q x := Quot.lift (fun φ => φ x) (fun a b hab => hab x) q`. Then
    /// `extfunApp (Quot.mk eqv f)` ι-reduces (Quot.lift computation rule) to
    /// `fun x => f x`, which is `f` by function eta, so
    /// `congrArg extfunApp (Quot.sound h) : extfunApp (mk f) = extfunApp (mk g)`
    /// transports to `f = g`. The kernel's `add_decl` type-checks this proof
    /// term against `funext`'s declared type, so soundness rests only on
    /// `Quot.sound` (already foundational), not on a fresh `funext` axiom.
    ///
    /// # Contract
    ///
    /// REQUIRES: `init_eq()`, `init_quot()`, `init_quot_sound()` (auto-initialized)
    /// ENSURES: On success, `self.has_funext() == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())`
    pub fn init_funext(&mut self) -> Result<(), EnvError> {
        if self.funext_init {
            return Ok(());
        }

        // funext is proved from Quot.sound (via Quot.lift / congrArg), so it
        // requires Eq (for congrArg) and the full quotient bundle + Quot.sound.
        if !self.eq_init {
            self.init_eq()?;
        }
        if !self.quot_init {
            self.init_quot();
        }
        if !self.quot_sound_init {
            self.init_quot_sound()?;
        }

        let u = Name::from_string("u");
        let v = Name::from_string("v");
        let sort_u = Expr::from_kind(ExprKind::Sort(Level::param(u.clone())));
        let sort_v = Expr::from_kind(ExprKind::Sort(Level::param(v.clone())));

        // funext : {α : Sort u} → {β : α → Sort v} → {f g : (x : α) → β x} →
        //          (∀ x, f x = g x) → f = g
        let funext_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone()); // α : Sort u
                                                                   // β : α → Sort v
            let beta_ty = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x_id, _) = c.fresh_local(alpha.clone());
                c.mk_pi(x_id, BinderInfo::Default, alpha.clone(), sort_v.clone())
            };
            let (beta_id, beta) = b.fresh_local(beta_ty.clone());
            // f, g : (x : α) → β x
            let fn_ty = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x_id, x_var) = c.fresh_local(alpha.clone());
                let body = Expr::app(beta.clone(), x_var);
                c.mk_pi(x_id, BinderInfo::Default, alpha.clone(), body)
            };
            let (f_id, f_var) = b.fresh_local(fn_ty.clone()); // f
            let (g_id, g_var) = b.fresh_local(fn_ty.clone()); // g
                                                              // h : ∀ x, f x = g x  i.e.  Π (x : α), Eq (β x) (f x) (g x)
            let pointwise_eq_ty = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x_id, x_var) = c.fresh_local(alpha.clone());
                let eq_fx_gx = Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("Eq"), vec![Level::param(v.clone())]),
                            Expr::app(beta.clone(), x_var.clone()),
                        ),
                        Expr::app(f_var.clone(), x_var.clone()),
                    ),
                    Expr::app(g_var.clone(), x_var),
                );
                c.mk_pi(x_id, BinderInfo::Default, alpha.clone(), eq_fx_gx)
            };
            let (h_id, _) = b.fresh_local(pointwise_eq_ty.clone());
            // Result: Eq ((x : α) → β x) f g  at universe imax(u, v)
            let fn_type_for_eq = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x_id, x_var) = c.fresh_local(alpha.clone());
                let body = Expr::app(beta.clone(), x_var);
                c.mk_pi(x_id, BinderInfo::Default, alpha.clone(), body)
            };
            let eq_fg = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(
                            Name::from_string("Eq"),
                            vec![Level::imax(
                                Level::param(u.clone()),
                                Level::param(v.clone()),
                            )],
                        ),
                        fn_type_for_eq,
                    ),
                    f_var,
                ),
                g_var,
            );
            let r = eq_fg;
            let r = b.mk_pi(h_id, BinderInfo::Default, pointwise_eq_ty, r);
            let r = b.mk_pi(g_id, BinderInfo::Implicit, fn_ty.clone(), r);
            let r = b.mk_pi(f_id, BinderInfo::Implicit, fn_ty, r);
            let r = b.mk_pi(beta_id, BinderInfo::Implicit, beta_ty, r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), r);
            b.finish(r)
        };

        // Proof term: funext is derived from Quot.sound. See `funext_proof_value`.
        let funext_value = Self::funext_proof_value(&u, &v, &sort_u, &sort_v);

        // Guarded per house pattern: the quotient bundle / earlier inits never
        // register `funext`, but stay defensive against future drift.
        if self.get_const(&Name::from_string("funext")).is_none() {
            self.add_decl(Declaration::Theorem {
                name: Name::from_string("funext"),
                level_params: vec![u, v],
                type_: funext_type,
                value: funext_value,
            })?;
        }

        self.funext_init = true;
        Ok(())
    }

    /// Build the proof term for `funext`, derived from `Quot.sound`.
    ///
    /// Mirrors Lean 4 core (Init/Core). With
    /// `T := ∀ x, β x : Sort (imax u v)` and
    /// `eqv := fun (a b : T) => ∀ x, a x = b x : T → T → Prop`, define
    /// `extfunApp := fun (q : Quot eqv) (x : α) =>`
    /// `  @Quot.lift.{imax u v, v} T eqv (β x) (fun φ => φ x)`
    /// `    (fun a b (hab : eqv a b) => hab x) q`.
    /// Then `extfunApp (Quot.mk eqv c)` ι-reduces to `fun x => c x ≡ c` (eta),
    /// so the proof is
    /// `@congrArg.{imax u v, imax u v} (Quot eqv) T (Quot.mk eqv f) (Quot.mk eqv g)`
    /// `  extfunApp (@Quot.sound.{imax u v} T eqv f g h)`
    /// which has type `@Eq T (extfunApp (mk f)) (extfunApp (mk g))`,
    /// def-eq to `@Eq T f g`.
    fn funext_proof_value(u: &Name, v: &Name, sort_u: &Expr, sort_v: &Expr) -> Expr {
        let lvl_u = Level::param(u.clone());
        let lvl_v = Level::param(v.clone());
        let lvl_uv = Level::imax(lvl_u.clone(), lvl_v.clone());

        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(sort_u.clone()); // α : Sort u

        // β : α → Sort v
        let beta_ty = {
            let mut c = EnvDeclBuilder::child_of(&b);
            let (x_id, _) = c.fresh_local(alpha.clone());
            c.mk_pi(x_id, BinderInfo::Default, alpha.clone(), sort_v.clone())
        };
        let (beta_id, beta) = b.fresh_local(beta_ty.clone());

        // T := (x : α) → β x  (the function type, at Sort (imax u v))
        let fn_ty = |b: &EnvDeclBuilder| -> Expr {
            let mut c = EnvDeclBuilder::child_of(b);
            let (x_id, x_var) = c.fresh_local(alpha.clone());
            let body = Expr::app(beta.clone(), x_var);
            c.mk_pi(x_id, BinderInfo::Default, alpha.clone(), body)
        };
        let t_ty = fn_ty(&b);

        let (f_id, f_var) = b.fresh_local(t_ty.clone()); // f : T
        let (g_id, g_var) = b.fresh_local(t_ty.clone()); // g : T

        // h : ∀ x, f x = g x  i.e.  eqv f g
        let pointwise_eq_ty = {
            let mut c = EnvDeclBuilder::child_of(&b);
            let (x_id, x_var) = c.fresh_local(alpha.clone());
            let eq_fx_gx = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("Eq"), vec![lvl_v.clone()]),
                        Expr::app(beta.clone(), x_var.clone()),
                    ),
                    Expr::app(f_var.clone(), x_var.clone()),
                ),
                Expr::app(g_var.clone(), x_var),
            );
            c.mk_pi(x_id, BinderInfo::Default, alpha.clone(), eq_fx_gx)
        };
        let (h_id, h_var) = b.fresh_local(pointwise_eq_ty.clone());

        // eqv := fun (a b : T) => ∀ x, a x = b x   : T → T → Prop
        let eqv = {
            let mut c = EnvDeclBuilder::child_of(&b);
            let (a_id, a_var) = c.fresh_local(t_ty.clone());
            let (b_id, b_var) = c.fresh_local(t_ty.clone());
            let pw = {
                let mut d = EnvDeclBuilder::child_of(&c);
                let (x_id, x_var) = d.fresh_local(alpha.clone());
                let eq_ax_bx = Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("Eq"), vec![lvl_v.clone()]),
                            Expr::app(beta.clone(), x_var.clone()),
                        ),
                        Expr::app(a_var.clone(), x_var.clone()),
                    ),
                    Expr::app(b_var.clone(), x_var),
                );
                d.mk_pi(x_id, BinderInfo::Default, alpha.clone(), eq_ax_bx)
            };
            let pw = c.mk_lam(b_id, BinderInfo::Default, t_ty.clone(), pw);
            let pw = c.mk_lam(a_id, BinderInfo::Default, t_ty.clone(), pw);
            c.finish_child(pw)
        };

        // Quot eqv := @Quot.{imax u v} T eqv
        let quot_eqv = Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Quot"), vec![lvl_uv.clone()]),
                t_ty.clone(),
            ),
            eqv.clone(),
        );

        // @Quot.mk.{imax u v} T eqv c   (constructor applied to f or g)
        let quot_mk = |c_var: &Expr| -> Expr {
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("Quot.mk"), vec![lvl_uv.clone()]),
                        t_ty.clone(),
                    ),
                    eqv.clone(),
                ),
                c_var.clone(),
            )
        };
        let mk_f = quot_mk(&f_var);
        let mk_g = quot_mk(&g_var);

        // extfunApp := fun (q : Quot eqv) (x : α) =>
        //   @Quot.lift.{imax u v, v} T eqv (β x) (fun φ => φ x)
        //     (fun a b (hab : eqv a b) => hab x) q
        let extfun_app = {
            let mut c = EnvDeclBuilder::child_of(&b);
            let (q_id, q_var) = c.fresh_local(quot_eqv.clone());
            let (x_id, x_var) = c.fresh_local(alpha.clone());

            // lifted function: fun (φ : T) => φ x   : T → β x
            let lifted_fn = {
                let mut d = EnvDeclBuilder::child_of(&c);
                let (phi_id, phi_var) = d.fresh_local(t_ty.clone());
                let body = Expr::app(phi_var, x_var.clone());
                let lam = d.mk_lam(phi_id, BinderInfo::Default, t_ty.clone(), body);
                d.finish_child(lam)
            };

            // respect proof: fun (a b : T) (hab : eqv a b) => hab x
            //   : ∀ a b, eqv a b → (fun φ => φ x) a = (fun φ => φ x) b
            let respect = {
                let mut d = EnvDeclBuilder::child_of(&c);
                let (a_id, _a_var) = d.fresh_local(t_ty.clone());
                let (b_id, _b_var) = d.fresh_local(t_ty.clone());
                // hab : eqv a b ≡ ∀ y, a y = b y
                let hab_ty = Expr::app(Expr::app(eqv.clone(), _a_var.clone()), _b_var.clone());
                let (hab_id, hab_var) = d.fresh_local(hab_ty.clone());
                let body = Expr::app(hab_var, x_var.clone());
                let lam = d.mk_lam(hab_id, BinderInfo::Default, hab_ty, body);
                let lam = d.mk_lam(b_id, BinderInfo::Default, t_ty.clone(), lam);
                let lam = d.mk_lam(a_id, BinderInfo::Default, t_ty.clone(), lam);
                d.finish_child(lam)
            };

            // @Quot.lift.{imax u v, v} T eqv (β x) lifted_fn respect q
            let beta_x = Expr::app(beta.clone(), x_var.clone());
            let lift_app = mk_apps(
                Expr::const_(
                    Name::from_string("Quot.lift"),
                    vec![lvl_uv.clone(), lvl_v.clone()],
                ),
                vec![
                    t_ty.clone(),
                    eqv.clone(),
                    beta_x,
                    lifted_fn,
                    respect,
                    q_var.clone(),
                ],
            );
            let lam = c.mk_lam(x_id, BinderInfo::Default, alpha.clone(), lift_app);
            let lam = c.mk_lam(q_id, BinderInfo::Default, quot_eqv.clone(), lam);
            c.finish_child(lam)
        };

        // @Quot.sound.{imax u v} T eqv f g h : @Eq (Quot eqv) (mk f) (mk g)
        let sound = mk_apps(
            Expr::const_(Name::from_string("Quot.sound"), vec![lvl_uv.clone()]),
            vec![
                t_ty.clone(),
                eqv.clone(),
                f_var.clone(),
                g_var.clone(),
                h_var.clone(),
            ],
        );

        // @congrArg.{imax u v, imax u v} (Quot eqv) T (mk f) (mk g) extfunApp sound
        //   : @Eq T (extfunApp (mk f)) (extfunApp (mk g))   ≡   @Eq T f g
        let proof = mk_apps(
            Expr::const_(
                Name::from_string("congrArg"),
                vec![lvl_uv.clone(), lvl_uv.clone()],
            ),
            vec![quot_eqv, t_ty.clone(), mk_f, mk_g, extfun_app, sound],
        );

        // Close the binders: λ {α} {β} {f} {g} (h) => proof
        let r = b.mk_lam(h_id, BinderInfo::Default, pointwise_eq_ty, proof);
        let r = b.mk_lam(g_id, BinderInfo::Implicit, t_ty.clone(), r);
        let r = b.mk_lam(f_id, BinderInfo::Implicit, t_ty, r);
        let r = b.mk_lam(beta_id, BinderInfo::Implicit, beta_ty, r);
        let r = b.mk_lam(alpha_id, BinderInfo::Implicit, sort_u.clone(), r);
        b.finish(r)
    }

    /// Check if funext axiom has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_funext()` has been called successfully
    /// ENSURES: Pure function - no side effects
    #[cfg(test)]
    pub(crate) fn has_funext(&self) -> bool {
        self.funext_init
    }
}

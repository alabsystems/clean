// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Three `= true` ↔ proposition lemmas of Lean 4 core that `simp` arguments in
//! trust-ir name (gap G23, brick B3; design
//! `designs/2026-10-08-mutual-nested-recursion.md` §5.6), as real,
//! kernel-checked `Declaration::Theorem`s (NO axiom beyond the foundational
//! `propext`, NO `sorry`). Statements transcribed from the pinned Lean
//! (`#check` with `pp.all`):
//!
//! ```text
//! Bool.and_eq_true : ∀ (a b : Bool),
//!   @Eq Prop (@Eq Bool (Bool.and a b) true) (And (@Eq Bool a true) (@Eq Bool b true))
//! decide_eq_true_eq : ∀ {p : Prop} [inst : Decidable p],
//!   @Eq Prop (@Eq Bool (@Decidable.decide p inst) true) p
//! Option.isSome_iff_exists.{u} : ∀ {α : Type u} {x : Option α},
//!   Iff (@Eq Bool (@Option.isSome α x) true) (∃ a, x = some a)
//! ```
//!
//! Spelled as the pinned v4.30.0-rc2 states them (the reference of the
//! prelude collision census, `data/prelude_collision_census.json`), which
//! agrees with v4.8.0 up to the alias `and` for `Bool.and` (Clean's `&&`
//! elaborates to the reducible alias `and`, δ-equal to `Bool.and`).
//!
//! Proofs:
//! * `Bool.and_eq_true` — `propext` of an `Iff` whose forward half is the
//!   existing `Bool.and_eq_true_left/right` bridges and whose backward half is
//!   one `Bool.rec` on `a` (`and false b ≡ false`, `and true b ≡ b`).
//! * `decide_eq_true_eq` — `propext` of `of_decide_eq_true` and a
//!   `Decidable.rec` on the instance (`isFalse` refutes the carried proof,
//!   `isTrue` makes `decide` reduce to `true`).
//! * `Option.isSome_iff_exists` — one `Option.rec` on `x`: `none` has
//!   `isSome ≡ false` (a `Bool.noConfusion` one way, an `Eq.rec` transport of
//!   `none = some w` the other); `some v` is `⟨v, rfl⟩` / `rfl`.
//!
//! Lean's own `Option.isSome_iff_exists` also cites `Quot.sound` (through its
//! `simp` proof); this one does not. `propext` is foundational
//! (`FOUNDATIONAL_AXIOMS`), so `data/axiom_audit.json` and the prelude axiom
//! census are unchanged. Every declaration goes through checked `add_decl`.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

fn c(name: &str, levels: Vec<Level>) -> Expr {
    Expr::const_(Name::from_string(name), levels)
}

impl Environment {
    /// Register `Bool.and_eq_true`, `decide_eq_true_eq` and
    /// `Option.isSome_iff_exists`. Idempotent; a lemma whose ingredients this
    /// environment lacks is skipped (as its siblings in `logic_of_decide.rs`).
    ///
    /// A no-op in IMPORT MODE (as `register_lean_core_supply`): a file that
    /// imports real Lean `.olean`s gets Lean's own declarations of these names
    /// through the checked import path.
    pub(crate) fn register_eq_true_prop_lemmas(&mut self) -> Result<(), EnvError> {
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let have = |env: &Self, names: &[&str]| {
            names
                .iter()
                .all(|n| env.get_const(&Name::from_string(n)).is_some())
        };
        let base = [
            "propext",
            "Iff",
            "Iff.intro",
            "And",
            "And.intro",
            "And.left",
            "And.right",
            "Eq.refl",
        ];
        if !have(self, &base) {
            return Ok(());
        }
        if self
            .get_const(&Name::from_string("Bool.and_eq_true"))
            .is_none()
            && have(
                self,
                &[
                    "Bool.and",
                    "Bool.rec",
                    "Bool.and_eq_true_left",
                    "Bool.and_eq_true_right",
                ],
            )
        {
            self.register_bool_and_eq_true()?;
        }
        if self
            .get_const(&Name::from_string("decide_eq_true_eq"))
            .is_none()
            && have(
                self,
                &[
                    "Decidable.decide",
                    "Decidable.rec",
                    "of_decide_eq_true",
                    "False.elim",
                ],
            )
        {
            self.register_decide_eq_true_eq()?;
        }
        if self
            .get_const(&Name::from_string("Option.isSome_iff_exists"))
            .is_none()
            && have(
                self,
                &[
                    "Option.rec",
                    "Option.isSome",
                    "Exists",
                    "Exists.intro",
                    "Exists.rec",
                    "Eq.rec",
                    "Bool.noConfusion",
                ],
            )
        {
            self.register_option_is_some_iff_exists()?;
        }
        Ok(())
    }

    fn register_bool_and_eq_true(&mut self) -> Result<(), EnvError> {
        let one = Level::succ(Level::zero());
        let prop = Expr::prop();
        let bool_c = c("Bool", vec![]);
        let btrue = c("Bool.true", vec![]);
        let bfalse = c("Bool.false", vec![]);
        let eq = |ty: &Expr, l: Expr, r: Expr| {
            Expr::apps(c("Eq", vec![one.clone()]), [ty.clone(), l, r])
        };
        let eqt = |x: Expr| eq(&bool_c, x, btrue.clone());
        let and_b = |x: Expr, y: Expr| Expr::apps(c("Bool.and", vec![]), [x, y]);
        let and_p = |x: Expr, y: Expr| Expr::apps(c("And", vec![]), [x, y]);
        // ((a && b) = true) = (a = true ∧ b = true), over locals a b.
        let statement = |a: &Expr, b: &Expr| {
            eq(
                &prop,
                eqt(and_b(a.clone(), b.clone())),
                and_p(eqt(a.clone()), eqt(b.clone())),
            )
        };
        let type_ = {
            let mut bl = EnvDeclBuilder::new();
            let (a_id, a) = bl.fresh_local(bool_c.clone());
            let (b_id, b) = bl.fresh_local(bool_c.clone());
            let body = statement(&a, &b);
            let body = bl.mk_pi(b_id, BinderInfo::Default, bool_c.clone(), body);
            bl.finish(bl.mk_pi(a_id, BinderInfo::Default, bool_c.clone(), body))
        };
        let value = {
            let mut bl = EnvDeclBuilder::new();
            let (a_id, a) = bl.fresh_local(bool_c.clone());
            let (b_id, b) = bl.fresh_local(bool_c.clone());
            let lhs = eqt(and_b(a.clone(), b.clone()));
            let rhs = and_p(eqt(a.clone()), eqt(b.clone()));
            // mp : (a && b) = true → a = true ∧ b = true
            let (h_id, h) = bl.fresh_local(lhs.clone());
            let mp = Expr::apps(
                c("And.intro", vec![]),
                [
                    eqt(a.clone()),
                    eqt(b.clone()),
                    Expr::apps(
                        c("Bool.and_eq_true_left", vec![]),
                        [a.clone(), b.clone(), h.clone()],
                    ),
                    Expr::apps(
                        c("Bool.and_eq_true_right", vec![]),
                        [a.clone(), b.clone(), h],
                    ),
                ],
            );
            let mp = bl.mk_lam(h_id, BinderInfo::Default, lhs.clone(), mp);
            // mpr : by `Bool.rec` on a, motive
            //   fun a' => (a' = true ∧ b = true) → (a' && b) = true
            let motive = {
                let (x_id, x) = bl.fresh_local(bool_c.clone());
                let body = Expr::pi(
                    BinderInfo::Default,
                    and_p(eqt(x.clone()), eqt(b.clone())),
                    eqt(and_b(x, b.clone())),
                );
                bl.mk_lam(x_id, BinderInfo::Default, bool_c.clone(), body)
            };
            let case = |bl: &mut EnvDeclBuilder, lit: &Expr, proj: &str| {
                let hyp = and_p(eqt(lit.clone()), eqt(b.clone()));
                let (k_id, k) = bl.fresh_local(hyp.clone());
                let body = Expr::apps(c(proj, vec![]), [eqt(lit.clone()), eqt(b.clone()), k]);
                bl.mk_lam(k_id, BinderInfo::Default, hyp, body)
            };
            let case_false = case(&mut bl, &bfalse, "And.left");
            let case_true = case(&mut bl, &btrue, "And.right");
            let mpr = Expr::apps(
                c("Bool.rec", vec![Level::zero()]),
                [motive, case_false, case_true, a.clone()],
            );
            let iff = Expr::apps(c("Iff.intro", vec![]), [lhs.clone(), rhs.clone(), mp, mpr]);
            let body = Expr::apps(c("propext", vec![]), [lhs, rhs, iff]);
            let body = bl.mk_lam(b_id, BinderInfo::Default, bool_c.clone(), body);
            bl.finish(bl.mk_lam(a_id, BinderInfo::Default, bool_c.clone(), body))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("Bool.and_eq_true"),
            level_params: vec![],
            type_,
            value,
        })
    }

    fn register_decide_eq_true_eq(&mut self) -> Result<(), EnvError> {
        let one = Level::succ(Level::zero());
        let prop = Expr::prop();
        let bool_c = c("Bool", vec![]);
        let btrue = c("Bool.true", vec![]);
        let bfalse = c("Bool.false", vec![]);
        let eqb = |l: Expr, r: Expr| Expr::apps(c("Eq", vec![one.clone()]), [bool_c.clone(), l, r]);
        let dec = |p: &Expr| Expr::app(c("Decidable", vec![]), p.clone());
        let lhs_of = |p: &Expr, inst: &Expr| {
            eqb(
                Expr::apps(c("Decidable.decide", vec![]), [p.clone(), inst.clone()]),
                btrue.clone(),
            )
        };
        let type_ = {
            let mut bl = EnvDeclBuilder::new();
            let (p_id, p) = bl.fresh_local(prop.clone());
            let (i_id, inst) = bl.fresh_local(dec(&p));
            let body = Expr::apps(
                c("Eq", vec![one.clone()]),
                [prop.clone(), lhs_of(&p, &inst), p.clone()],
            );
            let body = bl.mk_pi(i_id, BinderInfo::InstImplicit, dec(&p), body);
            bl.finish(bl.mk_pi(p_id, BinderInfo::Implicit, prop.clone(), body))
        };
        let value = {
            let mut bl = EnvDeclBuilder::new();
            let (p_id, p) = bl.fresh_local(prop.clone());
            let (i_id, inst) = bl.fresh_local(dec(&p));
            let lhs = lhs_of(&p, &inst);
            let mp = Expr::apps(c("of_decide_eq_true", vec![]), [p.clone(), inst.clone()]);
            // mpr : `Decidable.rec` on inst, motive
            //   fun i => p → @Decidable.decide p i = true
            let motive = {
                let (j_id, j) = bl.fresh_local(dec(&p));
                let body = Expr::pi(
                    BinderInfo::Default,
                    p.clone(),
                    eqb(
                        Expr::apps(c("Decidable.decide", vec![]), [p.clone(), j]),
                        btrue.clone(),
                    ),
                );
                bl.mk_lam(j_id, BinderInfo::Default, dec(&p), body)
            };
            let not_p = Expr::app(c("Not", vec![]), p.clone());
            let case_false = {
                let (hn_id, hn) = bl.fresh_local(not_p.clone());
                let (hp_id, hp) = bl.fresh_local(p.clone());
                let body = Expr::apps(
                    c("False.elim", vec![Level::zero()]),
                    [eqb(bfalse.clone(), btrue.clone()), Expr::app(hn, hp)],
                );
                let body = bl.mk_lam(hp_id, BinderInfo::Default, p.clone(), body);
                bl.mk_lam(hn_id, BinderInfo::Default, not_p, body)
            };
            let case_true = {
                let (hq_id, _) = bl.fresh_local(p.clone());
                let (hp_id, _) = bl.fresh_local(p.clone());
                let body = Expr::apps(
                    c("Eq.refl", vec![one.clone()]),
                    [bool_c.clone(), btrue.clone()],
                );
                let body = bl.mk_lam(hp_id, BinderInfo::Default, p.clone(), body);
                bl.mk_lam(hq_id, BinderInfo::Default, p.clone(), body)
            };
            let mpr = Expr::apps(
                c("Decidable.rec", vec![Level::zero()]),
                [p.clone(), motive, case_false, case_true, inst.clone()],
            );
            let iff = Expr::apps(c("Iff.intro", vec![]), [lhs.clone(), p.clone(), mp, mpr]);
            let body = Expr::apps(c("propext", vec![]), [lhs, p.clone(), iff]);
            let body = bl.mk_lam(i_id, BinderInfo::InstImplicit, dec(&p), body);
            bl.finish(bl.mk_lam(p_id, BinderInfo::Implicit, prop.clone(), body))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("decide_eq_true_eq"),
            level_params: vec![],
            type_,
            value,
        })
    }

    fn register_option_is_some_iff_exists(&mut self) -> Result<(), EnvError> {
        let u_name = Name::from_string("u");
        let u = Level::param(u_name.clone());
        let u1 = Level::succ(u.clone());
        let one = Level::succ(Level::zero());
        let type_u = Expr::sort(u1.clone());
        let bool_c = c("Bool", vec![]);
        let btrue = c("Bool.true", vec![]);
        let bfalse = c("Bool.false", vec![]);
        let eqb = |l: Expr, r: Expr| Expr::apps(c("Eq", vec![one.clone()]), [bool_c.clone(), l, r]);
        let option = |alpha: &Expr| Expr::app(c("Option", vec![u.clone()]), alpha.clone());
        let none = |alpha: &Expr| Expr::app(c("Option.none", vec![u.clone()]), alpha.clone());
        let some = |alpha: &Expr, v: Expr| {
            Expr::apps(c("Option.some", vec![u.clone()]), [alpha.clone(), v])
        };
        let is_some = |alpha: &Expr, x: Expr| {
            Expr::apps(c("Option.isSome", vec![u.clone()]), [alpha.clone(), x])
        };
        let eq_opt = |alpha: &Expr, l: Expr, r: Expr| {
            Expr::apps(c("Eq", vec![u1.clone()]), [option(alpha), l, r])
        };
        // fun a => x = some a
        let pred = |bl: &mut EnvDeclBuilder, alpha: &Expr, x: &Expr| {
            let (a_id, a) = bl.fresh_local(alpha.clone());
            let body = eq_opt(alpha, x.clone(), some(alpha, a));
            bl.mk_lam(a_id, BinderInfo::Default, alpha.clone(), body)
        };
        let exists = |bl: &mut EnvDeclBuilder, alpha: &Expr, x: &Expr| {
            let p = pred(bl, alpha, x);
            Expr::apps(c("Exists", vec![u1.clone()]), [alpha.clone(), p])
        };
        let iff_of = |bl: &mut EnvDeclBuilder, alpha: &Expr, x: &Expr| {
            let l = eqb(is_some(alpha, x.clone()), btrue.clone());
            let r = exists(bl, alpha, x);
            Expr::apps(c("Iff", vec![]), [l, r])
        };
        let type_ = {
            let mut bl = EnvDeclBuilder::new();
            let (al_id, alpha) = bl.fresh_local(type_u.clone());
            let (x_id, x) = bl.fresh_local(option(&alpha));
            let body = iff_of(&mut bl, &alpha, &x);
            let body = bl.mk_pi(x_id, BinderInfo::Implicit, option(&alpha), body);
            bl.finish(bl.mk_pi(al_id, BinderInfo::Implicit, type_u.clone(), body))
        };
        let value = {
            let mut bl = EnvDeclBuilder::new();
            let (al_id, alpha) = bl.fresh_local(type_u.clone());
            let (x_id, x) = bl.fresh_local(option(&alpha));
            let motive = {
                let (y_id, y) = bl.fresh_local(option(&alpha));
                let body = iff_of(&mut bl, &alpha, &y);
                bl.mk_lam(y_id, BinderInfo::Default, option(&alpha), body)
            };
            let false_eq_true = eqb(bfalse.clone(), btrue.clone());
            // none: Iff (false = true) (∃ a, none = some a)
            let case_none = {
                let n = none(&alpha);
                let ex = exists(&mut bl, &alpha, &n);
                let mp = {
                    let (h_id, h) = bl.fresh_local(false_eq_true.clone());
                    let body = Expr::apps(
                        c("Bool.noConfusion", vec![Level::zero()]),
                        [ex.clone(), bfalse.clone(), btrue.clone(), h],
                    );
                    bl.mk_lam(h_id, BinderInfo::Default, false_eq_true.clone(), body)
                };
                let mpr = {
                    let (e_id, e) = bl.fresh_local(ex.clone());
                    let p = pred(&mut bl, &alpha, &n);
                    let ex_motive = {
                        let (t_id, _) = bl.fresh_local(ex.clone());
                        bl.mk_lam(t_id, BinderInfo::Default, ex.clone(), false_eq_true.clone())
                    };
                    let intro = {
                        let (w_id, w) = bl.fresh_local(alpha.clone());
                        let hyp = eq_opt(&alpha, n.clone(), some(&alpha, w.clone()));
                        let (h_id, h) = bl.fresh_local(hyp.clone());
                        // @Eq.rec (Option α) none
                        //   (fun y _ => isSome y = true → false = true)
                        //   (fun k => k) (some w) h (Eq.refl true)
                        let rec_motive = {
                            let (y_id, y) = bl.fresh_local(option(&alpha));
                            let eq_ty = eq_opt(&alpha, n.clone(), y.clone());
                            let (q_id, _) = bl.fresh_local(eq_ty.clone());
                            let body = Expr::pi(
                                BinderInfo::Default,
                                eqb(is_some(&alpha, y), btrue.clone()),
                                false_eq_true.clone(),
                            );
                            let body = bl.mk_lam(q_id, BinderInfo::Default, eq_ty, body);
                            bl.mk_lam(y_id, BinderInfo::Default, option(&alpha), body)
                        };
                        let refl_case = {
                            let (k_id, k) = bl.fresh_local(false_eq_true.clone());
                            bl.mk_lam(k_id, BinderInfo::Default, false_eq_true.clone(), k)
                        };
                        let body = Expr::apps(
                            c("Eq.rec", vec![Level::zero(), u1.clone()]),
                            [
                                option(&alpha),
                                n.clone(),
                                rec_motive,
                                refl_case,
                                some(&alpha, w),
                                h,
                                Expr::apps(
                                    c("Eq.refl", vec![one.clone()]),
                                    [bool_c.clone(), btrue.clone()],
                                ),
                            ],
                        );
                        let body = bl.mk_lam(h_id, BinderInfo::Default, hyp, body);
                        bl.mk_lam(w_id, BinderInfo::Default, alpha.clone(), body)
                    };
                    let body = Expr::apps(
                        c("Exists.rec", vec![u1.clone()]),
                        [alpha.clone(), p, ex_motive, intro, e],
                    );
                    bl.mk_lam(e_id, BinderInfo::Default, ex.clone(), body)
                };
                Expr::apps(c("Iff.intro", vec![]), [false_eq_true.clone(), ex, mp, mpr])
            };
            // some v: Iff (true = true) (∃ a, some v = some a)
            let case_some = {
                let (v_id, v) = bl.fresh_local(alpha.clone());
                let sv = some(&alpha, v.clone());
                let ex = exists(&mut bl, &alpha, &sv);
                let true_eq_true = eqb(btrue.clone(), btrue.clone());
                let mp = {
                    let (k_id, _) = bl.fresh_local(true_eq_true.clone());
                    let p = pred(&mut bl, &alpha, &sv);
                    let body = Expr::apps(
                        c("Exists.intro", vec![u1.clone()]),
                        [
                            alpha.clone(),
                            p,
                            v.clone(),
                            Expr::apps(
                                c("Eq.refl", vec![u1.clone()]),
                                [option(&alpha), sv.clone()],
                            ),
                        ],
                    );
                    bl.mk_lam(k_id, BinderInfo::Default, true_eq_true.clone(), body)
                };
                let mpr = {
                    let (k_id, _) = bl.fresh_local(ex.clone());
                    let body = Expr::apps(
                        c("Eq.refl", vec![one.clone()]),
                        [bool_c.clone(), btrue.clone()],
                    );
                    bl.mk_lam(k_id, BinderInfo::Default, ex.clone(), body)
                };
                let body = Expr::apps(c("Iff.intro", vec![]), [true_eq_true, ex, mp, mpr]);
                bl.mk_lam(v_id, BinderInfo::Default, alpha.clone(), body)
            };
            let body = Expr::apps(
                c("Option.rec", vec![Level::zero(), u.clone()]),
                [alpha.clone(), motive, case_none, case_some, x.clone()],
            );
            let body = bl.mk_lam(x_id, BinderInfo::Implicit, option(&alpha), body);
            bl.finish(bl.mk_lam(al_id, BinderInfo::Implicit, type_u.clone(), body))
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("Option.isSome_iff_exists"),
            level_params: vec![u_name],
            type_,
            value,
        })
    }
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Soundness/completeness bridges for `decide` — real kernel terms (NO `sorry`,
//! NO axiom):
//!
//! - `of_decide_eq_true  : ∀ {p : Prop} [Decidable p], decide p = true  → p`
//! - `of_decide_eq_false : ∀ {p : Prop} [Decidable p], decide p = false → ¬p`
//!
//! `decide p` unfolds (reducibly) to `@Decidable.decide p inst`, which is a
//! `Decidable.rec` on `inst` returning `Bool.false` for `isFalse` and
//! `Bool.true` for `isTrue`. Each bridge is itself a single `Decidable.rec` on
//! `inst` whose motive carries the `decide p i = <lit>` hypothesis:
//!   * of_true / isFalse:  `decide p (isFalse h) ≡ false`, so the hyp reduces to
//!     `false = true` — `Bool.noConfusion` inhabits the goal `p`.
//!   * of_true / isTrue:   returns the carried proof `h : p`.
//!   * of_false / isFalse: returns the carried proof `h : ¬p`.
//!   * of_false / isTrue:  hyp reduces to `true = false` — `Bool.noConfusion`.
//!
//! These back the Trust spec-elab MACHINE-INT equality certified monitor
//! (two-language design §1.1): a `u64` `a == b` clause decides via
//! `decide (Eq UInt64 a b)` using the wrapper `UInt64.decEq` instance, and cites
//! `of_decide_eq_true` (soundness) / `of_decide_eq_false` (completeness) — so no
//! bespoke `toNat`-injectivity lemma is needed.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `of_not_decide_eq_true`, the NEGATIVE-branch member of the
    /// `of_decide_*` family:
    ///
    /// ```text
    /// of_not_decide_eq_true : ∀ {p : Prop} [inst : Decidable p],
    ///                           Not (@Eq Bool (decide p) Bool.true) → Not p
    /// ```
    ///
    /// # Why it exists (and why the two siblings do not cover it)
    ///
    /// `of_decide_eq_false` consumes `decide p = false`. That is NOT what a
    /// negative branch hands you: a `dite` over a Bool test elaborates its
    /// condition to the Prop `decide p = true`, so the else-branch binder has
    /// type `¬(decide p = true)` — a NEGATION, not an equation at `false`.
    /// Bridging one to the other needs `Bool.not_eq_true`, an Eq-of-Props that
    /// costs `propext`. Proving the negative form directly by the same
    /// `Decidable.rec` casework keeps the closure EMPTY and is shorter.
    ///
    /// This is the generic half of the well-founded-recursion Bool-test lane:
    /// composed with `Nat.pos_of_ne_zero` it turns `¬(b == 0 = true)` into
    /// `0 < b`, which is `Nat.mod_lt`'s side condition.
    ///
    /// # Proof
    ///
    /// `@Decidable.rec.{0}` on `inst`, motive
    /// `fun i => Not (@Eq Bool (@Decidable.decide p i) Bool.true) → Not p`:
    ///
    /// * `isFalse hnp` — the goal IS `¬p`; return the carried `hnp`. The
    ///   hypothesis is discarded (it reduces to `¬(false = true)`, true but
    ///   unneeded).
    /// * `isTrue hp` — `decide p (isTrue hp) ≡ true`, so the hypothesis reduces
    ///   to `¬(true = true)` and `h (@Eq.refl.{1} Bool Bool.true) : False`;
    ///   `@False.elim.{0}` closes the `¬p` goal. (`hp` is unused: the branch is
    ///   unreachable, and it is refuted rather than assumed away.)
    ///
    /// # Import mode
    ///
    /// NOT gated, unlike `Nat.pos_of_ne_zero`. That gate exists because the
    /// name is a genuine Lean 4 core name whose binder convention Clean
    /// diverges from, so registering it first would shadow the imported
    /// original. `of_not_decide_eq_true` has no Lean counterpart to shadow —
    /// Lean core carries `of_decide_eq_true` / `of_decide_eq_false` (both
    /// registered ungated just below, with matching signatures) and
    /// `decide_eq_true`, but not this negative form.
    ///
    /// # Contract
    ///
    /// ENSURES: On success `of_not_decide_eq_true` is a proof-carrying
    /// `Theorem` with an empty axiom closure.
    /// ENSURES: Idempotent; a no-op if `decide`/`Decidable.rec` are absent.
    pub(crate) fn register_of_not_decide_eq_true(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("of_not_decide_eq_true");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_bool()?;
        self.init_true_false()?;
        self.init_decidable()?;
        if self.get_const(&Name::from_string("decide")).is_none()
            || self
                .get_const(&Name::from_string("Decidable.rec"))
                .is_none()
        {
            return Ok(());
        }

        let one = Level::succ(Level::zero());
        let prop = Expr::prop();
        let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
        let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let bfalse = Expr::const_(Name::from_string("Bool.false"), vec![]);
        let false_c = Expr::const_(Name::from_string("False"), vec![]);
        let not_c = Expr::const_(Name::from_string("Not"), vec![]);
        let decidable_c = Expr::const_(Name::from_string("Decidable"), vec![]);
        let decide_dec = Expr::const_(Name::from_string("Decidable.decide"), vec![]);
        let decide_c = Expr::const_(Name::from_string("decide"), vec![]);
        let eq_c = Expr::const_(Name::from_string("Eq"), vec![one.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![one]);
        let dec_rec = Expr::const_(Name::from_string("Decidable.rec"), vec![Level::zero()]);
        let false_elim = Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]);

        let dec_p = |p: &Expr| Expr::app(decidable_c.clone(), p.clone());
        let not_of = |x: Expr| Expr::app(not_c.clone(), x);
        // `¬(x = Bool.true)` — the shape a negative Bool-test branch binds.
        let ne_true =
            |x: Expr| not_of(Expr::apps(eq_c.clone(), [bool_c.clone(), x, btrue.clone()]));

        // ── type: ∀ {p} [inst : Decidable p], ¬(decide p inst = true) → ¬p ──
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(prop.clone());
            let (inst_id, inst) = b.fresh_local(dec_p(&p));
            let hyp = ne_true(Expr::apps(decide_c.clone(), [p.clone(), inst.clone()]));
            let (h_id, _h) = b.fresh_local(hyp.clone());
            let e = b.mk_pi(h_id, BinderInfo::Default, hyp, not_of(p.clone()));
            let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, dec_p(&p), e);
            b.finish(b.mk_pi(p_id, BinderInfo::Implicit, prop.clone(), e))
        };

        // ── value: λ {p} [inst]. @Decidable.rec.{0} p motive mf mt inst ──
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(prop.clone());
            let (inst_id, inst) = b.fresh_local(dec_p(&p));
            // `¬p` spelled as the Pi `p → False`, matching the siblings.
            let not_p = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (x_id, _x) = d.fresh_local(p.clone());
                d.finish_child(d.mk_pi(x_id, BinderInfo::Default, p.clone(), false_c.clone()))
            };
            // motive : λ (i : Decidable p). ¬(@Decidable.decide p i = true) → ¬p
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (i_id, i) = c.fresh_local(dec_p(&p));
                let hyp = ne_true(Expr::apps(decide_dec.clone(), [p.clone(), i.clone()]));
                let inner = {
                    let (hh_id, _hh) = c.fresh_local(hyp.clone());
                    c.mk_pi(hh_id, BinderInfo::Default, hyp, not_of(p.clone()))
                };
                c.finish_child(c.mk_lam(i_id, BinderInfo::Default, dec_p(&p), inner))
            };
            // isFalse minor : λ (hnp : ¬p) (_h : ¬(false = true)). hnp
            let minor_false = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (hnp_id, hnp) = c.fresh_local(not_p.clone());
                let hyp = ne_true(bfalse.clone());
                let (h_id, _h) = c.fresh_local(hyp.clone());
                let inner = c.mk_lam(h_id, BinderInfo::Default, hyp, hnp);
                c.finish_child(c.mk_lam(hnp_id, BinderInfo::Default, not_p.clone(), inner))
            };
            // isTrue minor : λ (_hp : p) (h : ¬(true = true)).
            //                  @False.elim.{0} (¬p) (h (@Eq.refl.{1} Bool true))
            let minor_true = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (hp_id, _hp) = c.fresh_local(p.clone());
                let hyp = ne_true(btrue.clone());
                let (h_id, h) = c.fresh_local(hyp.clone());
                let refl = Expr::apps(eq_refl.clone(), [bool_c.clone(), btrue.clone()]);
                let body = Expr::apps(false_elim.clone(), [not_of(p.clone()), Expr::app(h, refl)]);
                let inner = c.mk_lam(h_id, BinderInfo::Default, hyp, body);
                c.finish_child(c.mk_lam(hp_id, BinderInfo::Default, p.clone(), inner))
            };
            let rec_app = Expr::apps(
                dec_rec.clone(),
                [p.clone(), motive, minor_false, minor_true, inst.clone()],
            );
            let e = b.mk_lam(inst_id, BinderInfo::InstImplicit, dec_p(&p), rec_app);
            b.finish(b.mk_lam(p_id, BinderInfo::Implicit, prop.clone(), e))
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }

    /// Register `of_decide_eq_true` / `of_decide_eq_false` as kernel-checked,
    /// axiom-free theorems. Idempotent; no-op if `Decidable`/`decide` are absent.
    pub(crate) fn register_of_decide_lemmas(&mut self) -> Result<(), EnvError> {
        self.init_eq()?;
        self.init_bool()?;
        self.init_true_false()?;
        self.init_decidable()?;
        if self.get_const(&Name::from_string("decide")).is_none()
            || self
                .get_const(&Name::from_string("Decidable.rec"))
                .is_none()
        {
            return Ok(());
        }
        if self
            .get_const(&Name::from_string("Bool.noConfusion"))
            .is_none()
        {
            self.regenerate_missing_no_confusion();
        }

        let one = Level::succ(Level::zero());
        let zero_lvl = Level::zero();
        let prop = Expr::prop();
        let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
        let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let bfalse = Expr::const_(Name::from_string("Bool.false"), vec![]);
        let false_c = Expr::const_(Name::from_string("False"), vec![]);
        let decidable_c = Expr::const_(Name::from_string("Decidable"), vec![]);
        let decide_dec = Expr::const_(Name::from_string("Decidable.decide"), vec![]);
        let decide_c = Expr::const_(Name::from_string("decide"), vec![]);
        let eq_c = Expr::const_(Name::from_string("Eq"), vec![one.clone()]);
        // Motive eliminates into Prop (Sort 0).
        let dec_rec = Expr::const_(Name::from_string("Decidable.rec"), vec![zero_lvl.clone()]);
        let no_conf = Expr::const_(Name::from_string("Bool.noConfusion"), vec![zero_lvl]);

        let eqb = |x: Expr, lit: Expr| Expr::apps(eq_c.clone(), [bool_c.clone(), x, lit]);
        // `@Bool.noConfusion.{0} P a b h : P` for distinct ground `a b`.
        let noconf = |p: Expr, a: Expr, b: Expr, h: Expr| Expr::apps(no_conf.clone(), [p, a, b, h]);

        // Build one of the two lemmas. `lit` is the RHS of the decide-equation
        // (`Bool.true` for of_true, `Bool.false` for of_false); `concl` is the
        // conclusion given `p` (either `p` itself, or `¬p`). `keep_true`/
        // `keep_false` say which branch returns the carried proof vs. ex-falso.
        for spec in ["of_decide_eq_true", "of_decide_eq_false"] {
            if self.get_const(&Name::from_string(spec)).is_some() {
                continue;
            }
            let is_true_lemma = spec == "of_decide_eq_true";
            let lit = if is_true_lemma {
                btrue.clone()
            } else {
                bfalse.clone()
            };
            // conclusion as a function of the `Prop` local `p` (`p` or `¬p`).
            let concl = |p: &Expr| -> Expr {
                if is_true_lemma {
                    p.clone()
                } else {
                    Expr::app(Expr::const_(Name::from_string("Not"), vec![]), p.clone())
                }
            };

            let dec_p = |p: &Expr| Expr::app(decidable_c.clone(), p.clone());
            // `@decide p inst` (the reducible alias — matches the declared type).
            let decide_alias =
                |p: &Expr, inst: &Expr| Expr::apps(decide_c.clone(), [p.clone(), inst.clone()]);
            // `@Decidable.decide p i` (canonical — used inside the motive).
            let decide_canon =
                |p: &Expr, i: &Expr| Expr::apps(decide_dec.clone(), [p.clone(), i.clone()]);

            // ── type: ∀ {p} (inst : Decidable p), (decide p inst = lit) → concl p ──
            let type_ = {
                let mut b = EnvDeclBuilder::new();
                let (p_id, p) = b.fresh_local(prop.clone());
                let (inst_id, inst) = b.fresh_local(dec_p(&p));
                let hyp = eqb(decide_alias(&p, &inst), lit.clone());
                let (h_id, _h) = b.fresh_local(hyp.clone());
                let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl(&p));
                let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, dec_p(&p), e);
                b.finish(b.mk_pi(p_id, BinderInfo::Implicit, prop.clone(), e))
            };

            // ── value: λ {p} (inst). @Decidable.rec.{0} p motive mf mt inst ──
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (p_id, p) = b.fresh_local(prop.clone());
                let (inst_id, inst) = b.fresh_local(dec_p(&p));
                let not_p = {
                    let mut d = EnvDeclBuilder::child_of(&b);
                    let (x_id, _x) = d.fresh_local(p.clone());
                    d.finish_child(d.mk_pi(x_id, BinderInfo::Default, p.clone(), false_c.clone()))
                };
                // motive : λ (i : Decidable p). (@Decidable.decide p i = lit) → concl p
                let motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (i_id, i) = c.fresh_local(dec_p(&p));
                    let hyp = eqb(decide_canon(&p, &i), lit.clone());
                    let (hh_id, _hh) = c.fresh_local(hyp.clone());
                    let inner = c.mk_pi(hh_id, BinderInfo::Default, hyp, concl(&p));
                    c.finish_child(c.mk_lam(i_id, BinderInfo::Default, dec_p(&p), inner))
                };
                // isFalse minor : λ (hnp : ¬p) (h : decide(isFalse hnp) = lit). <body>
                //   decide(isFalse _) ≡ false. of_true → h : false = true → noConfusion;
                //   of_false → h : false = false; goal ¬p → return hnp.
                let minor_false = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (hnp_id, hnp) = c.fresh_local(not_p.clone());
                    let hyp = eqb(bfalse.clone(), lit.clone());
                    let (h_id, h) = c.fresh_local(hyp.clone());
                    let body = if is_true_lemma {
                        // h : false = true → p
                        noconf(p.clone(), bfalse.clone(), btrue.clone(), h)
                    } else {
                        // h : false = false → ¬p := hnp
                        hnp
                    };
                    let inner = c.mk_lam(h_id, BinderInfo::Default, hyp, body);
                    c.finish_child(c.mk_lam(hnp_id, BinderInfo::Default, not_p.clone(), inner))
                };
                // isTrue minor : λ (hp : p) (h : decide(isTrue hp) = lit). <body>
                //   decide(isTrue _) ≡ true. of_true → h : true = true; goal p → hp;
                //   of_false → h : true = false → noConfusion (goal ¬p).
                let minor_true = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (hp_id, hp) = c.fresh_local(p.clone());
                    let hyp = eqb(btrue.clone(), lit.clone());
                    let (h_id, h) = c.fresh_local(hyp.clone());
                    let body = if is_true_lemma {
                        hp
                    } else {
                        // h : true = false → ¬p
                        noconf(concl(&p), btrue.clone(), bfalse.clone(), h)
                    };
                    let inner = c.mk_lam(h_id, BinderInfo::Default, hyp, body);
                    c.finish_child(c.mk_lam(hp_id, BinderInfo::Default, p.clone(), inner))
                };
                let rec_app = Expr::apps(
                    dec_rec.clone(),
                    [p.clone(), motive, minor_false, minor_true, inst.clone()],
                );
                let e = b.mk_lam(inst_id, BinderInfo::InstImplicit, dec_p(&p), rec_app);
                b.finish(b.mk_lam(p_id, BinderInfo::Implicit, prop.clone(), e))
            };

            self.add_decl(Declaration::Theorem {
                name: Name::from_string(spec),
                level_params: vec![],
                type_,
                value,
            })?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tc::TypeChecker;

    #[test]
    fn test_of_decide_lemmas_type_check_and_axiom_free() {
        let mut env = Environment::with_prelude();
        env.register_of_decide_lemmas().expect("register");
        env.register_of_decide_lemmas().expect("idempotent");
        env.register_of_not_decide_eq_true().expect("register");
        env.register_of_not_decide_eq_true().expect("idempotent");
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in [
            "of_decide_eq_true",
            "of_decide_eq_false",
            "of_not_decide_eq_true",
        ] {
            let n = Name::from_string(name);
            let _ = tc
                .infer_type(&Expr::const_(n.clone(), vec![]))
                .unwrap_or_else(|e| panic!("{name} should type-check: {e:?}"));
            let deps = env.axiom_deps(&n).expect("registered");
            let names: Vec<String> = deps.iter().map(|x| x.to_string()).collect();
            assert!(names.is_empty(), "{name} must be axiom-free, got {names:?}");
        }
    }
}

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

    /// Register `decide_eq_decide`, the CONGRUENCE member of the `decide`
    /// family:
    ///
    /// ```text
    /// decide_eq_decide : ∀ {p q : Prop} {_ : Decidable p} {_ : Decidable q},
    ///                      (decide p = decide q) ↔ (p ↔ q)
    /// ```
    ///
    /// # Lean fidelity
    ///
    /// Transcribed from the pinned toolchain's own source —
    /// `leanprover/lean4` **v4.30.0-rc2**, `src/Init/PropLemmas.lean:512`
    /// (the tag this repo's `lean-toolchain` names):
    ///
    /// ```text
    /// @[simp, bool_to_prop] theorem decide_eq_decide
    ///     {p q : Prop} {_ : Decidable p} {_ : Decidable q} :
    ///     decide p = decide q ↔ (p ↔ q) :=
    ///   ⟨fun h => by rw [← decide_eq_true_iff (p := p), h, decide_eq_true_iff],
    ///    fun h => by simp [h]⟩
    /// ```
    ///
    /// Two details of that statement are easy to get wrong and are matched
    /// here deliberately:
    ///
    /// * it is an **`Iff`**, not the one-directional
    ///   `(p ↔ q) → decide p = decide q` that the name is usually quoted as.
    ///   Registering the implication under this name would shadow the genuine
    ///   Lean declaration with a WEAKER one, and every `.mp`/`.1` use site
    ///   imported from Lean would stop resolving;
    /// * the two `Decidable` binders are **implicit** (`{_ : …}`), not
    ///   instance-implicit (`[…]`) as in the `of_decide_*` siblings above.
    ///   Lean solves them by unification against the `decide p = decide q`
    ///   equation rather than by instance search, so a `[…]` spelling here
    ///   would diverge from the import exactly the way `Nat.pos_of_ne_zero`
    ///   does.
    ///
    /// The vendored Lean-core `.olean` set confirms the module: the name
    /// occurs in `Init/PropLemmas.olean` and in none of `Init/Core.olean`,
    /// `Init/SimpLemmas.olean` or `Init/Data/Bool.olean`.
    ///
    /// # Why it exists (and why the siblings do not cover it)
    ///
    /// `of_decide_eq_true` / `of_decide_eq_false` move between ONE decision and
    /// its proposition. They say nothing about TWO decisions over DIFFERENT
    /// propositions, which is the shape of every "this magic constant is the
    /// right one" contract: a guard's decision (`depth < 21`) proved equal to
    /// the arithmetic that fixes its constant (`3 * (depth + 1) < 64`, at
    /// `Nat`). Without this lemma that goal has nothing to reach for — `simp`
    /// reports `no progress made` — and each user re-derives the casework by
    /// hand. (Measured 2026-09-20 against the Trust pack built from
    /// `379912412b1`: `decide_eq_decide`, `Bool.decide_congr`,
    /// `decide_eq_true_eq` and `decide_eq_false_iff_not` were all
    /// `Unknown identifier` in this prelude.)
    ///
    /// # Proof
    ///
    /// `Iff.intro` over two nested `@Decidable.rec.{0}`, four arms each. NO
    /// `propext` and NO `Classical` — Lean's own proof goes through
    /// `decide_eq_true_iff` and `rw`, which would; the direct casework does
    /// not, and that is what keeps the axiom closure EMPTY. A Trust obligation
    /// discharged through this lemma can therefore still report
    /// `axiom_closure: Empty`.
    ///
    /// Forward (`decide p = decide q → (p ↔ q)`), on `(dp, dq)`:
    /// * `(isFalse, isFalse)` — both sides absurd; `Iff.intro` of two
    ///   `False.elim`s.
    /// * `(isFalse, isTrue)` / `(isTrue, isFalse)` — the hypothesis reduces to
    ///   `false = true` / `true = false`; `Bool.noConfusion`.
    /// * `(isTrue, isTrue)` — both carried proofs are in hand; `Iff.intro` of
    ///   two constant functions.
    ///
    /// Backward (`(p ↔ q) → decide p = decide q`) is the same square with the
    /// diagonal closed by `Eq.refl` and the off-diagonal refuted by pushing the
    /// carried proof through the `Iff`.
    ///
    /// # Import mode
    ///
    /// NOT gated, like the `of_decide_*` siblings: the statement above IS the
    /// Lean one, so a later import of the genuine declaration finds a matching
    /// signature rather than a divergent stub.
    ///
    /// # Contract
    ///
    /// REQUIRES: `Iff`, `Decidable`, `decide`, `Decidable.rec`, `Eq`, `Bool`,
    /// `False` — each initialised here if absent.
    /// ENSURES: On success `decide_eq_decide` is a proof-carrying `Theorem`
    /// with an empty axiom closure.
    /// ENSURES: Idempotent; a no-op if `decide`/`Decidable.rec` are absent.
    pub(crate) fn register_decide_eq_decide(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("decide_eq_decide");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_bool()?;
        self.init_true_false()?;
        self.init_decidable()?;
        self.init_iff()?;
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
        if self
            .get_const(&Name::from_string("Bool.noConfusion"))
            .is_none()
        {
            return Ok(());
        }

        let one = Level::succ(Level::zero());
        let zero_lvl = Level::zero();
        let prop = Expr::prop();
        let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
        let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let bfalse = Expr::const_(Name::from_string("Bool.false"), vec![]);
        let false_c = Expr::const_(Name::from_string("False"), vec![]);
        let iff_c = Expr::const_(Name::from_string("Iff"), vec![]);
        let iff_intro = Expr::const_(Name::from_string("Iff.intro"), vec![]);
        let iff_mp = Expr::const_(Name::from_string("Iff.mp"), vec![]);
        let iff_mpr = Expr::const_(Name::from_string("Iff.mpr"), vec![]);
        let decidable_c = Expr::const_(Name::from_string("Decidable"), vec![]);
        let decide_dec = Expr::const_(Name::from_string("Decidable.decide"), vec![]);
        let eq_c = Expr::const_(Name::from_string("Eq"), vec![one.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![one]);
        // Both motives eliminate into Prop (`Eq … : Prop`, `Iff … : Prop`).
        let dec_rec = Expr::const_(Name::from_string("Decidable.rec"), vec![zero_lvl.clone()]);
        let false_elim = Expr::const_(Name::from_string("False.elim"), vec![zero_lvl.clone()]);
        let no_conf = Expr::const_(Name::from_string("Bool.noConfusion"), vec![zero_lvl]);

        let dec_of = |p: &Expr| Expr::app(decidable_c.clone(), p.clone());
        let eqb = |x: Expr, y: Expr| Expr::apps(eq_c.clone(), [bool_c.clone(), x, y]);
        let refl = |x: Expr| Expr::apps(eq_refl.clone(), [bool_c.clone(), x]);
        let iff_of = |a: &Expr, b: &Expr| Expr::apps(iff_c.clone(), [a.clone(), b.clone()]);
        // `@Decidable.decide p i` — canonical: the declared TYPE and the
        // MOTIVES both spell it (Lean's statement does).
        let decide_canon =
            |p: &Expr, i: &Expr| Expr::apps(decide_dec.clone(), [p.clone(), i.clone()]);
        // `@Bool.noConfusion.{0} P a b h : P` for distinct ground `a b`.
        let noconf = |t: Expr, a: Expr, b: Expr, h: Expr| Expr::apps(no_conf.clone(), [t, a, b, h]);

        // ── type ──────────────────────────────────────────────────────────
        // ∀ {p q : Prop} {dp : Decidable p} {dq : Decidable q},
        //     Iff (Decidable.decide p dp = Decidable.decide q dq) (Iff p q)
        // — Lean's statement exactly: its head is `Decidable.decide`, which
        // `decide` merely aliases (pinned v4.30.0-rc2, `pp.explicit`). Until
        // 2026-09-30 it was stated over the alias `decide`, a recorded
        // divergence in `data/prelude_collision_census.json`.
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(prop.clone());
            let (q_id, q) = b.fresh_local(prop.clone());
            let (dp_id, dp) = b.fresh_local(dec_of(&p));
            let (dq_id, dq) = b.fresh_local(dec_of(&q));
            let concl = iff_of(
                &eqb(decide_canon(&p, &dp), decide_canon(&q, &dq)),
                &iff_of(&p, &q),
            );
            let e = b.mk_pi(dq_id, BinderInfo::Implicit, dec_of(&q), concl);
            let e = b.mk_pi(dp_id, BinderInfo::Implicit, dec_of(&p), e);
            let e = b.mk_pi(q_id, BinderInfo::Implicit, prop.clone(), e);
            b.finish(b.mk_pi(p_id, BinderInfo::Implicit, prop.clone(), e))
        };

        // ── value ─────────────────────────────────────────────────────────
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (p_id, p) = b.fresh_local(prop.clone());
            let (q_id, q) = b.fresh_local(prop.clone());
            let (dp_id, dp) = b.fresh_local(dec_of(&p));
            let (dq_id, dq) = b.fresh_local(dec_of(&q));

            // `¬x`, spelled as the Pi `x → False` (matches the siblings).
            let not_of = |b: &EnvDeclBuilder, x: &Expr| -> Expr {
                let mut d = EnvDeclBuilder::child_of(b);
                let (v_id, _v) = d.fresh_local(x.clone());
                d.finish_child(d.mk_pi(v_id, BinderInfo::Default, x.clone(), false_c.clone()))
            };
            let not_p = not_of(&b, &p);
            let not_q = not_of(&b, &q);
            let pq = iff_of(&p, &q);
            let goal_eq = eqb(decide_canon(&p, &dp), decide_canon(&q, &dq));

            // ---- BACKWARD: (p ↔ q) → decide p dp = decide q dq -------------
            let backward = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (h_id, h) = c.fresh_local(pq.clone());

                // Inner rec on `dq`, for a fixed outer literal `lit`
                // (`Bool.false` in the isFalse branch, `Bool.true` in isTrue).
                // `refute` builds the `False` proof for the arm that cannot
                // happen; `hit` is the arm where both sides agree.
                let inner = |c: &EnvDeclBuilder,
                             lit: &Expr,
                             refute_on_true: bool,
                             carried: &Expr| {
                    let d = EnvDeclBuilder::child_of(c);
                    let motive = {
                        let mut e = EnvDeclBuilder::child_of(&d);
                        let (j_id, j) = e.fresh_local(dec_of(&q));
                        let body = eqb(lit.clone(), decide_canon(&q, &j));
                        e.finish_child(e.mk_lam(j_id, BinderInfo::Default, dec_of(&q), body))
                    };
                    // isFalse arm : λ (hnq : ¬q). <…>
                    let minor_false = {
                        let mut e = EnvDeclBuilder::child_of(&d);
                        let (hnq_id, hnq) = e.fresh_local(not_q.clone());
                        let body = if refute_on_true {
                            // outer isFalse: q is false too — `false = false`.
                            refl(lit.clone())
                        } else {
                            // outer isTrue: `hp : p`, so `¬q` is absurd.
                            // goal `true = false`.
                            let contra = Expr::app(
                                hnq,
                                Expr::apps(
                                    iff_mp.clone(),
                                    [p.clone(), q.clone(), h.clone(), carried.clone()],
                                ),
                            );
                            Expr::apps(
                                false_elim.clone(),
                                [eqb(lit.clone(), bfalse.clone()), contra],
                            )
                        };
                        e.finish_child(e.mk_lam(hnq_id, BinderInfo::Default, not_q.clone(), body))
                    };
                    // isTrue arm : λ (hq : q). <…>
                    let minor_true = {
                        let mut e = EnvDeclBuilder::child_of(&d);
                        let (hq_id, hq) = e.fresh_local(q.clone());
                        let body = if refute_on_true {
                            // outer isFalse: `hnp : ¬p`, so `q` is absurd.
                            // goal `false = true`.
                            let contra = Expr::app(
                                carried.clone(),
                                Expr::apps(iff_mpr.clone(), [p.clone(), q.clone(), h.clone(), hq]),
                            );
                            Expr::apps(
                                false_elim.clone(),
                                [eqb(lit.clone(), btrue.clone()), contra],
                            )
                        } else {
                            refl(lit.clone())
                        };
                        e.finish_child(e.mk_lam(hq_id, BinderInfo::Default, q.clone(), body))
                    };
                    let app = Expr::apps(
                        dec_rec.clone(),
                        [q.clone(), motive, minor_false, minor_true, dq.clone()],
                    );
                    d.finish_child(app)
                };

                let motive = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (i_id, i) = d.fresh_local(dec_of(&p));
                    let body = eqb(decide_canon(&p, &i), decide_canon(&q, &dq));
                    d.finish_child(d.mk_lam(i_id, BinderInfo::Default, dec_of(&p), body))
                };
                // outer isFalse : λ (hnp : ¬p). <inner at Bool.false>
                let minor_false = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (hnp_id, hnp) = d.fresh_local(not_p.clone());
                    let body = inner(&d, &bfalse, true, &hnp);
                    d.finish_child(d.mk_lam(hnp_id, BinderInfo::Default, not_p.clone(), body))
                };
                // outer isTrue : λ (hp : p). <inner at Bool.true>
                let minor_true = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (hp_id, hp) = d.fresh_local(p.clone());
                    let body = inner(&d, &btrue, false, &hp);
                    d.finish_child(d.mk_lam(hp_id, BinderInfo::Default, p.clone(), body))
                };
                let app = Expr::apps(
                    dec_rec.clone(),
                    [p.clone(), motive, minor_false, minor_true, dp.clone()],
                );
                let lam = c.mk_lam(h_id, BinderInfo::Default, pq.clone(), app);
                c.finish_child(lam)
            };

            // ---- FORWARD: decide p dp = decide q dq → (p ↔ q) --------------
            // The motives carry the equation so each arm sees it already
            // reduced at that constructor (the `of_not_decide_eq_true` shape).
            let forward = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (h_id, h) = c.fresh_local(goal_eq.clone());

                let inner = |c: &EnvDeclBuilder, lit: &Expr, outer_true: bool, carried: &Expr| {
                    let d = EnvDeclBuilder::child_of(c);
                    let motive = {
                        let mut e = EnvDeclBuilder::child_of(&d);
                        let (j_id, j) = e.fresh_local(dec_of(&q));
                        let hyp = eqb(lit.clone(), decide_canon(&q, &j));
                        let (hh_id, _hh) = e.fresh_local(hyp.clone());
                        let body = e.mk_pi(hh_id, BinderInfo::Default, hyp, pq.clone());
                        e.finish_child(e.mk_lam(j_id, BinderInfo::Default, dec_of(&q), body))
                    };
                    // isFalse arm : λ (hnq : ¬q) (hh : lit = false). <…>
                    let minor_false = {
                        let mut e = EnvDeclBuilder::child_of(&d);
                        let (hnq_id, hnq) = e.fresh_local(not_q.clone());
                        let hyp = eqb(lit.clone(), bfalse.clone());
                        let (hh_id, hh) = e.fresh_local(hyp.clone());
                        let body = if outer_true {
                            // `true = false` — impossible.
                            noconf(pq.clone(), btrue.clone(), bfalse.clone(), hh)
                        } else {
                            // both false: `Iff.intro (p → q) (q → p)`, each
                            // arm absurd.
                            let mp = {
                                let mut f = EnvDeclBuilder::child_of(&e);
                                let (x_id, x) = f.fresh_local(p.clone());
                                let body = Expr::apps(
                                    false_elim.clone(),
                                    [q.clone(), Expr::app(carried.clone(), x)],
                                );
                                f.finish_child(f.mk_lam(x_id, BinderInfo::Default, p.clone(), body))
                            };
                            let mpr = {
                                let mut f = EnvDeclBuilder::child_of(&e);
                                let (y_id, y) = f.fresh_local(q.clone());
                                let body = Expr::apps(
                                    false_elim.clone(),
                                    [p.clone(), Expr::app(hnq.clone(), y)],
                                );
                                f.finish_child(f.mk_lam(y_id, BinderInfo::Default, q.clone(), body))
                            };
                            Expr::apps(iff_intro.clone(), [p.clone(), q.clone(), mp, mpr])
                        };
                        let lam = e.mk_lam(hh_id, BinderInfo::Default, hyp, body);
                        e.finish_child(e.mk_lam(hnq_id, BinderInfo::Default, not_q.clone(), lam))
                    };
                    // isTrue arm : λ (hq : q) (hh : lit = true). <…>
                    let minor_true = {
                        let mut e = EnvDeclBuilder::child_of(&d);
                        let (hq_id, hq) = e.fresh_local(q.clone());
                        let hyp = eqb(lit.clone(), btrue.clone());
                        let (hh_id, hh) = e.fresh_local(hyp.clone());
                        let body = if outer_true {
                            // both true: `Iff.intro (fun _ => hq) (fun _ => hp)`.
                            let mp = {
                                let mut f = EnvDeclBuilder::child_of(&e);
                                let (x_id, _x) = f.fresh_local(p.clone());
                                f.finish_child(f.mk_lam(
                                    x_id,
                                    BinderInfo::Default,
                                    p.clone(),
                                    hq.clone(),
                                ))
                            };
                            let mpr = {
                                let mut f = EnvDeclBuilder::child_of(&e);
                                let (y_id, _y) = f.fresh_local(q.clone());
                                f.finish_child(f.mk_lam(
                                    y_id,
                                    BinderInfo::Default,
                                    q.clone(),
                                    carried.clone(),
                                ))
                            };
                            Expr::apps(iff_intro.clone(), [p.clone(), q.clone(), mp, mpr])
                        } else {
                            // `false = true` — impossible.
                            noconf(pq.clone(), bfalse.clone(), btrue.clone(), hh)
                        };
                        let lam = e.mk_lam(hh_id, BinderInfo::Default, hyp, body);
                        e.finish_child(e.mk_lam(hq_id, BinderInfo::Default, q.clone(), lam))
                    };
                    let app = Expr::apps(
                        dec_rec.clone(),
                        [q.clone(), motive, minor_false, minor_true, dq.clone()],
                    );
                    d.finish_child(app)
                };

                let motive = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (i_id, i) = d.fresh_local(dec_of(&p));
                    let hyp = eqb(decide_canon(&p, &i), decide_canon(&q, &dq));
                    let (hh_id, _hh) = d.fresh_local(hyp.clone());
                    let body = d.mk_pi(hh_id, BinderInfo::Default, hyp, pq.clone());
                    d.finish_child(d.mk_lam(i_id, BinderInfo::Default, dec_of(&p), body))
                };
                let minor_false = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (hnp_id, hnp) = d.fresh_local(not_p.clone());
                    let body = inner(&d, &bfalse, false, &hnp);
                    d.finish_child(d.mk_lam(hnp_id, BinderInfo::Default, not_p.clone(), body))
                };
                let minor_true = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (hp_id, hp) = d.fresh_local(p.clone());
                    let body = inner(&d, &btrue, true, &hp);
                    d.finish_child(d.mk_lam(hp_id, BinderInfo::Default, p.clone(), body))
                };
                let app = Expr::apps(
                    dec_rec.clone(),
                    [p.clone(), motive, minor_false, minor_true, dp.clone()],
                );
                let applied = Expr::app(app, h);
                let lam = c.mk_lam(h_id, BinderInfo::Default, goal_eq.clone(), applied);
                c.finish_child(lam)
            };

            let intro = Expr::apps(
                iff_intro.clone(),
                [
                    eqb(decide_canon(&p, &dp), decide_canon(&q, &dq)),
                    pq.clone(),
                    forward,
                    backward,
                ],
            );
            let e = b.mk_lam(dq_id, BinderInfo::Implicit, dec_of(&q), intro);
            let e = b.mk_lam(dp_id, BinderInfo::Implicit, dec_of(&p), e);
            let e = b.mk_lam(q_id, BinderInfo::Implicit, prop.clone(), e);
            b.finish(b.mk_lam(p_id, BinderInfo::Implicit, prop.clone(), e))
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::ExprKind;
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

    /// `decide_eq_decide` registers, kernel-checks, and costs no axiom.
    ///
    /// The axiom-closure assertion is the load-bearing one: Lean's own proof of
    /// this lemma goes through `decide_eq_true_iff` and `rw`, which would pull
    /// in `propext`. The `Decidable.rec` casework registered here does not, and
    /// a Trust obligation discharged through it can still publish a row with
    /// `axiom_closure: Empty`. If this assertion ever starts failing, the
    /// *proof* changed — the statement is still true, but every downstream
    /// grade that says "Empty" has to be re-read.
    #[test]
    fn test_decide_eq_decide_type_checks_and_is_axiom_free() {
        let mut env = Environment::with_prelude();
        env.register_decide_eq_decide().expect("register");
        env.register_decide_eq_decide().expect("idempotent");
        let n = Name::from_string("decide_eq_decide");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(n.clone(), vec![]))
            .unwrap_or_else(|e| panic!("decide_eq_decide should type-check: {e:?}"));
        let deps = env.axiom_deps(&n).expect("registered");
        let names: Vec<String> = deps.iter().map(|x| x.to_string()).collect();
        assert!(
            names.is_empty(),
            "decide_eq_decide must be axiom-free, got {names:?}"
        );
    }

    /// LEAN FIDELITY. The registered statement must be the one at
    /// `leanprover/lean4` v4.30.0-rc2 `src/Init/PropLemmas.lean:512`:
    ///
    /// ```text
    /// {p q : Prop} {_ : Decidable p} {_ : Decidable q} :
    ///     decide p = decide q ↔ (p ↔ q)
    /// ```
    ///
    /// Two things are checked, and each is a way this could be registered
    /// WRONG while still being a true theorem:
    ///
    ///  * FOUR binders, ALL implicit. An instance-implicit `Decidable` binder
    ///    (the `of_decide_*` siblings' convention, and the obvious thing to
    ///    copy) diverges from Lean, so a later import of the genuine
    ///    declaration would find a mismatched signature — the
    ///    `Nat.pos_of_ne_zero` failure mode this file's header describes.
    ///  * the conclusion is headed by `Iff`, not by `Eq`. The name is usually
    ///    quoted as the one-directional `(p ↔ q) → decide p = decide q`;
    ///    registering THAT would shadow Lean's bidirectional lemma with a
    ///    weaker one and break every imported `.mp` use site.
    #[test]
    fn test_decide_eq_decide_matches_lean_signature() {
        let mut env = Environment::with_prelude();
        env.register_decide_eq_decide().expect("register");
        let decl = env
            .get_const(&Name::from_string("decide_eq_decide"))
            .expect("registered");
        let mut ty = decl.type_.clone();
        let mut binders = Vec::new();
        while let ExprKind::Pi(data, _dom, body) = ty.kind() {
            binders.push(data.info);
            ty = (**body).clone();
        }
        assert_eq!(
            binders,
            vec![
                BinderInfo::Implicit,
                BinderInfo::Implicit,
                BinderInfo::Implicit,
                BinderInfo::Implicit
            ],
            "Lean's binders are {{p q : Prop}} {{_ : Decidable p}} {{_ : Decidable q}} \
             — all four IMPLICIT, not instance-implicit"
        );
        // Head of the conclusion must be `Iff`.
        let mut head = ty.clone();
        while let ExprKind::App(f, _) = head.kind() {
            head = (**f).clone();
        }
        match head.kind() {
            ExprKind::Const(name, _) => assert_eq!(
                name.to_string(),
                "Iff",
                "the conclusion must be the Iff `decide p = decide q ↔ (p ↔ q)`, \
                 not the one-directional implication"
            ),
            other => panic!("conclusion head is not a constant: {other:?}"),
        }
    }

    /// THE DIRECTION a contract actually uses, and its NEGATIVE TWIN.
    ///
    /// Positive: `Iff.mpr` at the lemma gives `(p ↔ q) → decide p = decide q`,
    /// which is what closes a goal like "this guard's decision equals the
    /// arithmetic that fixes its constant".
    ///
    /// Negative: the UNCONDITIONAL congruence — the same value under a type
    /// with the `p ↔ q` premise deleted — is FALSE (take `p := True`,
    /// `q := False`), and the kernel must refuse to register it. A lemma this
    /// file accepted under that type would make any two decisions equal.
    #[test]
    fn test_decide_eq_decide_mpr_and_unconditional_twin_refused() {
        let mut env = Environment::with_prelude();
        env.register_decide_eq_decide().expect("register");
        let prop = Expr::prop();
        let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
        let one = Level::succ(Level::zero());
        let eq_c = Expr::const_(Name::from_string("Eq"), vec![one]);
        let iff_c = Expr::const_(Name::from_string("Iff"), vec![]);
        let iff_mpr = Expr::const_(Name::from_string("Iff.mpr"), vec![]);
        let decidable_c = Expr::const_(Name::from_string("Decidable"), vec![]);
        let decide_c = Expr::const_(Name::from_string("decide"), vec![]);
        let ded = Expr::const_(Name::from_string("decide_eq_decide"), vec![]);

        // POSITIVE: `@Iff.mpr (decide p dp = decide q dq) (p ↔ q)
        //              (@decide_eq_decide p q dp dq)` type-checks.
        let mut b = EnvDeclBuilder::new();
        let (p_id, p) = b.fresh_local(prop.clone());
        let (q_id, q) = b.fresh_local(prop.clone());
        let (dp_id, dp) = b.fresh_local(Expr::app(decidable_c.clone(), p.clone()));
        let (dq_id, dq) = b.fresh_local(Expr::app(decidable_c.clone(), q.clone()));
        let lhs = Expr::apps(decide_c.clone(), [p.clone(), dp.clone()]);
        let rhs = Expr::apps(decide_c.clone(), [q.clone(), dq.clone()]);
        let eqn = Expr::apps(eq_c.clone(), [bool_c.clone(), lhs, rhs]);
        let pq = Expr::apps(iff_c.clone(), [p.clone(), q.clone()]);
        let inst = Expr::apps(ded.clone(), [p.clone(), q.clone(), dp.clone(), dq.clone()]);
        let mpr = Expr::apps(iff_mpr, [eqn.clone(), pq.clone(), inst]);
        let want = {
            let (h_id, _h) = b.fresh_local(pq.clone());
            b.mk_pi(h_id, BinderInfo::Default, pq.clone(), eqn.clone())
        };
        let closed_val = {
            let e = b.mk_lam(
                dq_id,
                BinderInfo::Implicit,
                Expr::app(decidable_c.clone(), q.clone()),
                mpr,
            );
            let e = b.mk_lam(
                dp_id,
                BinderInfo::Implicit,
                Expr::app(decidable_c.clone(), p.clone()),
                e,
            );
            let e = b.mk_lam(q_id, BinderInfo::Implicit, prop.clone(), e);
            b.finish(b.mk_lam(p_id, BinderInfo::Implicit, prop.clone(), e))
        };
        let closed_ty = {
            let mut c = EnvDeclBuilder::new();
            let (p2_id, p2) = c.fresh_local(prop.clone());
            let (q2_id, q2) = c.fresh_local(prop.clone());
            let (dp2_id, dp2) = c.fresh_local(Expr::app(decidable_c.clone(), p2.clone()));
            let (dq2_id, dq2) = c.fresh_local(Expr::app(decidable_c.clone(), q2.clone()));
            let l = Expr::apps(decide_c.clone(), [p2.clone(), dp2.clone()]);
            let r = Expr::apps(decide_c.clone(), [q2.clone(), dq2.clone()]);
            let eqn2 = Expr::apps(eq_c.clone(), [bool_c.clone(), l, r]);
            let pq2 = Expr::apps(iff_c.clone(), [p2.clone(), q2.clone()]);
            let (h_id, _h) = c.fresh_local(pq2.clone());
            let e = c.mk_pi(h_id, BinderInfo::Default, pq2.clone(), eqn2);
            let e = c.mk_pi(
                dq2_id,
                BinderInfo::Implicit,
                Expr::app(decidable_c.clone(), q2.clone()),
                e,
            );
            let e = c.mk_pi(
                dp2_id,
                BinderInfo::Implicit,
                Expr::app(decidable_c.clone(), p2.clone()),
                e,
            );
            let e = c.mk_pi(q2_id, BinderInfo::Implicit, prop.clone(), e);
            c.finish(c.mk_pi(p2_id, BinderInfo::Implicit, prop.clone(), e))
        };
        let _ = want; // the per-instance shape, kept for readability of the type above
        let mut pos_env = env.clone();
        pos_env
            .add_decl(Declaration::Theorem {
                name: Name::from_string("decide_eq_decide_mpr_probe"),
                level_params: vec![],
                type_: closed_ty,
                value: closed_val.clone(),
            })
            .expect("Iff.mpr at decide_eq_decide must give (p <-> q) -> decide p = decide q");

        // NEGATIVE TWIN: the same value under the UNCONDITIONAL type — the
        // `p ↔ q` premise deleted. False at `p := True, q := False`.
        let bad_ty = {
            let mut c = EnvDeclBuilder::new();
            let (p2_id, p2) = c.fresh_local(prop.clone());
            let (q2_id, q2) = c.fresh_local(prop.clone());
            let (dp2_id, dp2) = c.fresh_local(Expr::app(decidable_c.clone(), p2.clone()));
            let (dq2_id, dq2) = c.fresh_local(Expr::app(decidable_c.clone(), q2.clone()));
            let l = Expr::apps(decide_c.clone(), [p2.clone(), dp2.clone()]);
            let r = Expr::apps(decide_c.clone(), [q2.clone(), dq2.clone()]);
            let eqn2 = Expr::apps(eq_c.clone(), [bool_c.clone(), l, r]);
            let e = c.mk_pi(
                dq2_id,
                BinderInfo::Implicit,
                Expr::app(decidable_c.clone(), q2.clone()),
                eqn2,
            );
            let e = c.mk_pi(
                dp2_id,
                BinderInfo::Implicit,
                Expr::app(decidable_c, p2.clone()),
                e,
            );
            let e = c.mk_pi(q2_id, BinderInfo::Implicit, prop.clone(), e);
            c.finish(c.mk_pi(p2_id, BinderInfo::Implicit, prop.clone(), e))
        };
        let mut neg_env = env.clone();
        let refused = neg_env.add_decl(Declaration::Theorem {
            name: Name::from_string("decide_eq_decide_unconditional_twin"),
            level_params: vec![],
            type_: bad_ty,
            value: closed_val,
        });
        assert!(
            refused.is_err(),
            "the UNCONDITIONAL congruence `decide p = decide q` with no `p <-> q` \
             premise is false and must be refused by the kernel"
        );
    }
}

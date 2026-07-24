// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bonami-Beckner campaign — `Fin.lastCases` ι-computation lemmas for the
//! coordinate-peel extension maps (`BoolAnalysis.extendF` / `extendT`).
//!
//! `extendF n x` / `extendT n x` are built on the constructive `Fin.lastCases`
//! eliminator at the constant motive `fun _ => Bool` (see
//! `boolean_analysis_peel.rs`). The four computation rules
//!
//! ```text
//! BoolAnalysis.extendF_castSucc : extendF n x (Fin.castSucc n i) = x i
//! BoolAnalysis.extendF_last     : extendF n x (Fin.last n)       = Bool.false
//! BoolAnalysis.extendT_castSucc : extendT n x (Fin.castSucc n i) = x i
//! BoolAnalysis.extendT_last     : extendT n x (Fin.last n)       = Bool.true
//! ```
//!
//! are NOT definitional: `Fin.lastCases` reduces by dispatching through
//! `Decidable.rec` on `Nat.decEq (Fin.val (Nat.succ n) j) n`, which is stuck for
//! a symbolic index `j`. We unstick it the same way `chi_flip_factor` handles its
//! `instDecidableEqFin` dispatch: case on the *actual* discriminant
//! `Nat.decEq val_j n` with a motive that reproduces the `Fin.lastCases` body
//! parameterized by the decidable, and close each branch.
//!
//! Once inside a branch, the kernel's **structure-eta** (`Fin` is single-ctor,
//! so `i ≡ Fin.mk n (Fin.val n i) (Fin.isLt n i)`) plus **proof irrelevance** on
//! the `Nat.lt` bound collapse the `Eq.ndrec` transport that `Fin.lastCases`
//! emits: the reconstructed index `Fin.mk n val_j hlt` is definitionally `i`
//! (castSucc case) and the transport along the resulting `Eq.refl` is the
//! identity. So:
//!
//! - **castSucc / isFalse** — `val (castSucc n i) ≡ val i`, the recovered index
//!   is defeq `i`, the branch reduces to `x i` ⇒ `Eq.refl`.
//! - **castSucc / isTrue** — `heq : val i = n` contradicts `Fin.isLt n i :
//!   val i < n` (transport `isLt` along `heq` to `n < n`, then `Nat.lt_irrefl`);
//!   `False.elim`.
//! - **last / isTrue** — `val (Fin.last n) ≡ n`, the top branch reduces to the
//!   appended bit ⇒ `Eq.refl`.
//! - **last / isFalse** — `hne : (n = n) → False` applied to `Eq.refl n` ⇒
//!   `False.elim`.
//!
//! All four are `ProofQuality::Constructive` with empty domain-axiom closure.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Which extension map / which index a computation lemma is about.
#[derive(Clone, Copy)]
enum PeelCase {
    /// `extendF`/`extendT` at `Fin.castSucc n i` — reduces to `x i`.
    CastSucc,
    /// `extendF`/`extendT` at `Fin.last n` — reduces to the appended bit.
    Last,
}

/// Shared constants for the peel computation lemmas.
struct PeelComputeConsts {
    l0: Level,
    l1: Level,
    nat: Expr,
    bool_: Expr,
    false_c: Expr,
    nat_succ: Expr,
    nat_deceq: Expr,
    nat_lt: Expr,
    nat_lt_irrefl: Expr,
    fin: Expr,
    fin_val: Expr,
    fin_islt: Expr,
    fin_last: Expr,
    fin_cast: Expr,
    hcpoint: Expr,
    extend_f: Expr,
    extend_t: Expr,
    bool_false: Expr,
    bool_true: Expr,
    eq1: Expr,
    eq_bool: Expr,
    eq_refl_bool: Expr,
    eq_ndrec_prop: Expr,
    dec: Expr,
    dec_rec: Expr,
    dec_rec_bool: Expr,
    false_elim_bool: Expr,
}

impl PeelComputeConsts {
    fn new() -> Self {
        let l0 = Level::zero();
        let l1 = Level::succ(l0.clone());
        Self {
            l0: l0.clone(),
            l1: l1.clone(),
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            bool_: Expr::const_(Name::from_string("Bool"), vec![]),
            false_c: Expr::const_(Name::from_string("False"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_deceq: Expr::const_(Name::from_string("Nat.decEq"), vec![]),
            nat_lt: Expr::const_(Name::from_string("Nat.lt"), vec![]),
            nat_lt_irrefl: Expr::const_(Name::from_string("Nat.lt_irrefl"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            fin_val: Expr::const_(Name::from_string("Fin.val"), vec![]),
            fin_islt: Expr::const_(Name::from_string("Fin.isLt"), vec![]),
            fin_last: Expr::const_(Name::from_string("Fin.last"), vec![]),
            fin_cast: Expr::const_(Name::from_string("Fin.castSucc"), vec![]),
            hcpoint: Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            extend_f: Expr::const_(Name::from_string("BoolAnalysis.extendF"), vec![]),
            extend_t: Expr::const_(Name::from_string("BoolAnalysis.extendT"), vec![]),
            bool_false: Expr::const_(Name::from_string("Bool.false"), vec![]),
            bool_true: Expr::const_(Name::from_string("Bool.true"), vec![]),
            // Eq.{1} : the equality is over Bool : Type 0 = Sort 1.
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_bool: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_refl_bool: Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
            // Eq.ndrec.{0,1} : motive (val i < n) lands in Prop (Sort 0), index
            // Nat lives in Sort 1.
            eq_ndrec_prop: Expr::const_(
                Name::from_string("Eq.ndrec"),
                vec![l0.clone(), l1.clone()],
            ),
            dec: Expr::const_(Name::from_string("Decidable"), vec![]),
            // Outer dispatch: motive D returns a Prop (an `Eq Bool …`), so the
            // top-level `Decidable.rec` eliminates into Sort 0.
            dec_rec: Expr::const_(Name::from_string("Decidable.rec"), vec![l0.clone()]),
            // Inner reconstruction inside `lastcases_body`: the `Fin.lastCases`
            // dispatch at the constant `Bool` motive eliminates into Bool : Sort 1,
            // so its `Decidable.rec` is `.{1}` (matching `Fin.lastCases`'s own use).
            dec_rec_bool: Expr::const_(Name::from_string("Decidable.rec"), vec![l1.clone()]),
            false_elim_bool: Expr::const_(Name::from_string("False.elim"), vec![l0]),
        }
    }

    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }

    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }

    fn succ(&self, n: &Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n.clone())
    }

    /// `@Fin.val (succ n) j`.
    fn val(&self, n_succ: &Expr, j: &Expr) -> Expr {
        Expr::apps(self.fin_val.clone(), [n_succ.clone(), j.clone()])
    }

    /// `@Eq Bool l r`.
    fn eq_bool(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq_bool.clone(), [self.bool_.clone(), l, r])
    }

    /// `@Eq Nat l r`.
    fn eq_nat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.nat.clone(), l, r])
    }

    /// `@Nat.lt a b`.
    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_lt.clone(), [a, b])
    }

    /// The extension map constant for the chosen bit (`extendF` / `extendT`).
    fn map_const(&self, use_true: bool) -> &Expr {
        if use_true {
            &self.extend_t
        } else {
            &self.extend_f
        }
    }

    /// The appended bit (`Bool.false` / `Bool.true`) — the RHS of the `last` rule.
    fn bit(&self, use_true: bool) -> &Expr {
        if use_true {
            &self.bool_true
        } else {
            &self.bool_false
        }
    }
}

impl Environment {
    /// Initialize the four `Fin.lastCases` ι-computation lemmas for the
    /// coordinate-peel extension maps. Idempotent; axiom-free.
    pub(crate) fn init_boolean_analysis_peel_compute(&mut self) -> Result<(), EnvError> {
        if self.boolean_analysis_peel_compute_init {
            return Ok(());
        }
        self.init_boolean_analysis_peel()?;
        self.register_nat_dec_eq_proof()?;
        self.register_nat_lt_irrefl_theorem()?;

        let c = PeelComputeConsts::new();
        self.register_peel_compute(
            &c,
            "BoolAnalysis.extendF_castSucc",
            false,
            PeelCase::CastSucc,
        )?;
        self.register_peel_compute(&c, "BoolAnalysis.extendF_last", false, PeelCase::Last)?;
        self.register_peel_compute(
            &c,
            "BoolAnalysis.extendT_castSucc",
            true,
            PeelCase::CastSucc,
        )?;
        self.register_peel_compute(&c, "BoolAnalysis.extendT_last", true, PeelCase::Last)?;

        self.boolean_analysis_peel_compute_init = true;
        Ok(())
    }

    /// Whether the peel computation lemmas have been initialized.
    pub(crate) fn has_boolean_analysis_peel_compute(&self) -> bool {
        self.boolean_analysis_peel_compute_init
    }

    fn register_peel_compute(
        &mut self,
        c: &PeelComputeConsts,
        name: &str,
        use_true: bool,
        case: PeelCase,
    ) -> Result<(), EnvError> {
        let name = Name::from_string(name);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let (ty, value) = match case {
            PeelCase::CastSucc => (
                Self::peel_castsucc_type(c, use_true),
                Self::peel_castsucc_value(c, use_true),
            ),
            PeelCase::Last => (
                Self::peel_last_type(c, use_true),
                Self::peel_last_value(c, use_true),
            ),
        };
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    // ───────────────────────── castSucc rule ─────────────────────────

    /// `∀ (n : Nat) (x : HCPoint n) (i : Fin n), extend n x (Fin.castSucc n i) = x i`.
    fn peel_castsucc_type(c: &PeelComputeConsts, use_true: bool) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let (x_id, x) = b.fresh_local(c.hcpoint_of(&n));
        let (i_id, i) = b.fresh_local(c.fin_of(&n));
        let cs = Expr::apps(c.fin_cast.clone(), [n.clone(), i.clone()]);
        let lhs = Expr::app(
            Expr::apps(c.map_const(use_true).clone(), [n.clone(), x.clone()]),
            cs,
        );
        let rhs = Expr::app(x.clone(), i.clone());
        let concl = c.eq_bool(lhs, rhs);
        let e = b.mk_pi(i_id, BinderInfo::Default, c.fin_of(&n), concl);
        let e = b.mk_pi(x_id, BinderInfo::Default, c.hcpoint_of(&n), e);
        let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
        b.finish(e)
    }

    fn peel_castsucc_value(c: &PeelComputeConsts, use_true: bool) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let (x_id, x) = b.fresh_local(c.hcpoint_of(&n));
        let (i_id, i) = b.fresh_local(c.fin_of(&n));

        let succ_n = c.succ(&n);
        let cs = Expr::apps(c.fin_cast.clone(), [n.clone(), i.clone()]);
        // val_j := Fin.val (succ n) (castSucc n i)  (≡ Fin.val n i definitionally)
        let val_j = c.val(&succ_n, &cs);
        // prop := Eq Nat val_j n
        let prop = c.eq_nat(val_j.clone(), n.clone());
        let rhs = Expr::app(x.clone(), i.clone());

        // The proof dispatches on the *actual* `Fin.lastCases` discriminant
        // `Nat.decEq val_j n` via `Decidable.rec` at the motive `D`. `D d` pins
        // that discriminant to `d` inside a faithful reconstruction of the
        // δ-exposed `Fin.lastCases` body (`lastcases_body`), so `D (Nat.decEq
        // val_j n)` is defeq to the goal `extend … (castSucc n i) = x i`.

        // D : (d : Decidable prop) → Prop :=
        //   fun d => @Eq Bool (lastcases_body d) (x i)
        let d_motive = {
            let mut m = EnvDeclBuilder::child_of(&b);
            let dec_prop = Expr::app(c.dec.clone(), prop.clone());
            let (d_id, d) = m.fresh_local(dec_prop.clone());
            let lc_body = c.lastcases_body(&m, &n, use_true, &x, &cs, &prop, &d);
            let body = c.eq_bool(lc_body, rhs.clone());
            m.finish_child(m.mk_lam(d_id, BinderInfo::Default, dec_prop, body))
        };

        // isFalse minor: fun (hne : prop → False) => Eq.refl Bool (x i)
        //   (lastCases reduces to `x i'` with i' ≡ i by struct-eta + proof irrel)
        let false_minor = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let not_p = Expr::pi(BinderInfo::Default, prop.clone(), c.false_c.clone());
            let (hne_id, _hne) = d.fresh_local(not_p.clone());
            let refl = Expr::apps(c.eq_refl_bool.clone(), [c.bool_.clone(), rhs.clone()]);
            d.finish_child(d.mk_lam(hne_id, BinderInfo::Default, not_p, refl))
        };

        // isTrue minor: fun (heq : prop) => False.elim goal (contradiction)
        //   heq : val (castSucc n i) = n ≡ val i = n contradicts Fin.isLt n i.
        let true_minor = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (heq_id, heq) = d.fresh_local(prop.clone());
            // hislt : Nat.lt (Fin.val n i) n  (≡ Nat.lt val_j n)
            let hislt = Expr::apps(c.fin_islt.clone(), [n.clone(), i.clone()]);
            // Transport hislt : (val_j < n) along heq : val_j = n  to  (n < n).
            //   @Eq.ndrec Nat val_j (fun m => Nat.lt m n) hislt n heq
            let lt_motive = {
                let mut g = EnvDeclBuilder::child_of(&d);
                let (m_id, mm) = g.fresh_local(c.nat.clone());
                let body = c.lt(mm.clone(), n.clone());
                g.finish_child(g.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), body))
            };
            let nn_lt = Expr::apps(
                c.eq_ndrec_prop.clone(),
                [
                    c.nat.clone(),
                    val_j.clone(),
                    lt_motive,
                    hislt,
                    n.clone(),
                    heq.clone(),
                ],
            );
            // Nat.lt_irrefl n (nn_lt) : False
            let absurd = Expr::apps(c.nat_lt_irrefl.clone(), [n.clone(), nn_lt]);
            // False.elim goal absurd, goal := (lastcases_body (isTrue heq)) = x i.
            // Use the branch's expected goal type `Eq Bool ?lhs (x i)`; since the
            // term is `False.elim`, the goal is filled by Decidable.rec's motive
            // and the kernel only needs `goal : Prop`. Provide the conclusion type
            // explicitly: @Eq Bool (lastcases_body (isTrue heq)) (x i). For
            // `False.elim` the first arg is the *result type*; supplying the RHS
            // shape is unnecessary because the elaborated motive instance fixes it.
            // We pass the motive-instance goal via Decidable.rec, so here we need a
            // proof of D (isTrue heq) = that goal: provide False.elim at that goal.
            let goal = {
                // lastcases_body specialised to the isTrue discriminant. Re-derive
                // via the motive so the type matches Decidable.rec's expectation.
                let is_true = c.decidable_is_true(&prop, &heq);
                c.lastcases_body_eq_goal(&d, &n, use_true, &x, &cs, &prop, &is_true, &rhs)
            };
            let elim = Expr::apps(c.false_elim_bool.clone(), [goal, absurd]);
            d.finish_child(d.mk_lam(heq_id, BinderInfo::Default, prop.clone(), elim))
        };

        // discriminant := Nat.decEq val_j n
        let discr = Expr::apps(c.nat_deceq.clone(), [val_j.clone(), n.clone()]);
        // @Decidable.rec.{0} prop D false_minor true_minor discr : D discr
        //   which is defeq to the goal `extend … (castSucc n i) = x i`.
        let rec_app = Expr::apps(
            c.dec_rec.clone(),
            [prop.clone(), d_motive, false_minor, true_minor, discr],
        );

        let e = b.mk_lam(i_id, BinderInfo::Default, c.fin_of(&n), rec_app);
        let e = b.mk_lam(x_id, BinderInfo::Default, c.hcpoint_of(&n), e);
        let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
        b.finish(e)
    }

    // ───────────────────────── last rule ─────────────────────────

    /// `∀ (n : Nat) (x : HCPoint n), extend n x (Fin.last n) = <bit>`.
    fn peel_last_type(c: &PeelComputeConsts, use_true: bool) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let (x_id, x) = b.fresh_local(c.hcpoint_of(&n));
        let last = Expr::app(c.fin_last.clone(), n.clone());
        let lhs = Expr::app(
            Expr::apps(c.map_const(use_true).clone(), [n.clone(), x.clone()]),
            last,
        );
        let concl = c.eq_bool(lhs, c.bit(use_true).clone());
        let e = b.mk_pi(x_id, BinderInfo::Default, c.hcpoint_of(&n), concl);
        let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
        b.finish(e)
    }

    fn peel_last_value(c: &PeelComputeConsts, use_true: bool) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let (x_id, x) = b.fresh_local(c.hcpoint_of(&n));

        let succ_n = c.succ(&n);
        let last = Expr::app(c.fin_last.clone(), n.clone());
        // val_j := Fin.val (succ n) (Fin.last n)  (≡ n definitionally)
        let val_j = c.val(&succ_n, &last);
        let prop = c.eq_nat(val_j.clone(), n.clone());
        let bit = c.bit(use_true).clone();

        // D d := @Eq Bool (lastcases_body d) bit
        let d_motive = {
            let mut m = EnvDeclBuilder::child_of(&b);
            let dec_prop = Expr::app(c.dec.clone(), prop.clone());
            let (d_id, d) = m.fresh_local(dec_prop.clone());
            let lc_body = c.lastcases_body(&m, &n, use_true, &x, &last, &prop, &d);
            let body = c.eq_bool(lc_body, bit.clone());
            m.finish_child(m.mk_lam(d_id, BinderInfo::Default, dec_prop, body))
        };

        // isFalse minor: fun (hne : (val_j = n) → False) =>
        //   False.elim goal (hne (Eq.refl Nat n))  — val_j ≡ n so refl gives prop.
        let false_minor = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let not_p = Expr::pi(BinderInfo::Default, prop.clone(), c.false_c.clone());
            let (hne_id, hne) = d.fresh_local(not_p.clone());
            // Eq.refl Nat n : Eq Nat n n  ≡  Eq Nat val_j n = prop (val_j ≡ n).
            let refl_n = Expr::apps(
                Expr::const_(Name::from_string("Eq.refl"), vec![c.l1.clone()]),
                [c.nat.clone(), n.clone()],
            );
            let absurd = Expr::app(hne.clone(), refl_n);
            let is_false = c.decidable_is_false(&prop, &hne);
            let goal =
                c.lastcases_body_eq_goal(&d, &n, use_true, &x, &last, &prop, &is_false, &bit);
            let elim = Expr::apps(c.false_elim_bool.clone(), [goal, absurd]);
            d.finish_child(d.mk_lam(hne_id, BinderInfo::Default, not_p, elim))
        };

        // isTrue minor: fun (heq : prop) => Eq.refl Bool bit
        //   lastCases reduces to the appended bit (last ≡ last by struct-eta).
        let true_minor = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (heq_id, _heq) = d.fresh_local(prop.clone());
            let refl = Expr::apps(c.eq_refl_bool.clone(), [c.bool_.clone(), bit.clone()]);
            d.finish_child(d.mk_lam(heq_id, BinderInfo::Default, prop.clone(), refl))
        };

        let discr = Expr::apps(c.nat_deceq.clone(), [val_j.clone(), n.clone()]);
        let rec_app = Expr::apps(
            c.dec_rec.clone(),
            [prop.clone(), d_motive, false_minor, true_minor, discr],
        );

        let e = b.mk_lam(x_id, BinderInfo::Default, c.hcpoint_of(&n), rec_app);
        let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
        b.finish(e)
    }
}

impl PeelComputeConsts {
    /// `@Fin.lastCases.{1} n (fun _ => Bool) bit x j` with discriminant pinned to
    /// `d` — i.e. the δ-exposed `Decidable.rec` body of `extend n x j`, expressed
    /// so the motive's free variable is exactly the Decidable `d`.
    ///
    /// Concretely this is the application of the registered `extend` map to `j`;
    /// the kernel δ-unfolds it to `@Decidable.rec prop dmotive isFalse isTrue
    /// (Nat.decEq val_j n)`. The motive `D` only needs to be *defeq* to that body
    /// after substituting the actual discriminant for `d`, which holds because the
    /// body below is literally `@Decidable.rec prop dmotive isFalse isTrue d`
    /// reached through the same δ-chain. We therefore return the
    /// `Decidable.rec`-of-`d` form by re-applying the eliminator the map uses.
    #[allow(clippy::too_many_arguments)]
    fn lastcases_body(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        use_true: bool,
        x: &Expr,
        j: &Expr,
        prop: &Expr,
        d: &Expr,
    ) -> Expr {
        // motive of Fin.lastCases dispatch: fun (_ : Decidable prop) => Bool.
        let dmotive = {
            let mut m = EnvDeclBuilder::child_of(parent);
            let dec_prop = Expr::app(self.dec.clone(), prop.clone());
            let (z_id, _z) = m.fresh_local(dec_prop.clone());
            m.finish_child(m.mk_lam(z_id, BinderInfo::Default, dec_prop, self.bool_.clone()))
        };
        let (false_minor, true_minor) = self.lastcases_minors(parent, n, use_true, x, j, prop);
        Expr::apps(
            self.dec_rec_bool.clone(),
            [prop.clone(), dmotive, false_minor, true_minor, d.clone()],
        )
    }

    /// The two `Fin.lastCases` minor premises at the constant `Bool` motive,
    /// specialised to `(n, bit, x, j)`. These reproduce the exact closures inside
    /// `Fin.lastCases` so that `Decidable.rec` ι-reduces identically.
    #[allow(clippy::too_many_arguments)]
    fn lastcases_minors(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        use_true: bool,
        x: &Expr,
        j: &Expr,
        prop: &Expr,
    ) -> (Expr, Expr) {
        let succ_n = self.succ(n);
        let fin_succ_n = self.fin_of(&succ_n);
        let val_j = self.val(&succ_n, j);
        let bit = self.bit(use_true).clone();

        let fin_mk = Expr::const_(Name::from_string("Fin.mk"), vec![]);
        let nat_le_of_ss = Expr::const_(Name::from_string("Nat.le_of_succ_le_succ"), vec![]);
        let nat_lt_of_le_ne = Expr::const_(Name::from_string("Nat.lt_of_le_of_ne"), vec![]);
        let fin_eq_of_val = Expr::const_(Name::from_string("Fin.eq_of_val_eq"), vec![]);
        let eq_symm = Expr::const_(Name::from_string("Eq.symm"), vec![self.l1.clone()]);
        let eq_refl_nat = Expr::const_(Name::from_string("Eq.refl"), vec![self.l1.clone()]);
        // Eq.ndrec.{1,1}: transport over Eq (Fin (succ n)) at the constant Bool
        // motive (Sort 1).
        let eq_ndrec_bool = Expr::const_(
            Name::from_string("Eq.ndrec"),
            vec![self.l1.clone(), self.l1.clone()],
        );
        let fin_last = Expr::const_(Name::from_string("Fin.last"), vec![]);

        // const Bool motive over Fin (succ n): fun (_ : Fin (succ n)) => Bool.
        let bool_motive = Expr::lam(BinderInfo::Default, fin_succ_n.clone(), self.bool_.clone());

        // isFalse minor: fun (hne : prop → False) =>
        //   @Eq.ndrec (Fin (succ n)) (castSucc n i') (fun _ => Bool) (x i') j e
        let false_minor = {
            let mut c = EnvDeclBuilder::child_of(parent);
            let not_p = Expr::pi(BinderInfo::Default, prop.clone(), self.false_c.clone());
            let (hne_id, hne) = c.fresh_local(not_p.clone());

            let hislt = Expr::apps(self.fin_islt.clone(), [succ_n.clone(), j.clone()]);
            let hle = Expr::apps(nat_le_of_ss.clone(), [val_j.clone(), n.clone(), hislt]);
            let hlt = Expr::apps(
                nat_lt_of_le_ne.clone(),
                [val_j.clone(), n.clone(), hle, hne.clone()],
            );
            let i_prime = Expr::apps(fin_mk.clone(), [n.clone(), val_j.clone(), hlt]);
            // cast i' for the const Bool motive is just `x i'`.
            let x_iprime = Expr::app(x.clone(), i_prime.clone());
            let cs = Expr::apps(self.fin_cast.clone(), [n.clone(), i_prime.clone()]);
            let hval = Expr::apps(eq_refl_nat.clone(), [self.nat.clone(), val_j.clone()]);
            let e = Expr::apps(
                fin_eq_of_val.clone(),
                [succ_n.clone(), cs.clone(), j.clone(), hval],
            );
            let transported = Expr::apps(
                eq_ndrec_bool.clone(),
                [
                    fin_succ_n.clone(),
                    cs,
                    bool_motive.clone(),
                    x_iprime,
                    j.clone(),
                    e,
                ],
            );
            c.finish_child(c.mk_lam(hne_id, BinderInfo::Default, not_p, transported))
        };

        // isTrue minor: fun (heq : prop) =>
        //   @Eq.ndrec (Fin (succ n)) (Fin.last n) (fun _ => Bool) bit j e
        let true_minor = {
            let mut c = EnvDeclBuilder::child_of(parent);
            let (heq_id, heq) = c.fresh_local(prop.clone());
            let last_n = Expr::app(fin_last.clone(), n.clone());
            let hval = Expr::apps(
                eq_symm.clone(),
                [self.nat.clone(), val_j.clone(), n.clone(), heq.clone()],
            );
            let e = Expr::apps(
                fin_eq_of_val.clone(),
                [succ_n.clone(), last_n.clone(), j.clone(), hval],
            );
            let transported = Expr::apps(
                eq_ndrec_bool.clone(),
                [fin_succ_n.clone(), last_n, bool_motive, bit, j.clone(), e],
            );
            c.finish_child(c.mk_lam(heq_id, BinderInfo::Default, prop.clone(), transported))
        };

        (false_minor, true_minor)
    }

    /// `@Decidable.isTrue prop heq : Decidable prop`.
    fn decidable_is_true(&self, prop: &Expr, heq: &Expr) -> Expr {
        let is_true = Expr::const_(Name::from_string("Decidable.isTrue"), vec![]);
        Expr::apps(is_true, [prop.clone(), heq.clone()])
    }

    /// `@Decidable.isFalse prop hne : Decidable prop`.
    fn decidable_is_false(&self, prop: &Expr, hne: &Expr) -> Expr {
        let is_false = Expr::const_(Name::from_string("Decidable.isFalse"), vec![]);
        Expr::apps(is_false, [prop.clone(), hne.clone()])
    }

    /// `@Eq Bool (lastcases_body d) rhs` — the branch goal type, used as the
    /// explicit result type for `False.elim` in the contradictory branch.
    #[allow(clippy::too_many_arguments)]
    fn lastcases_body_eq_goal(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        use_true: bool,
        x: &Expr,
        j: &Expr,
        prop: &Expr,
        d: &Expr,
        rhs: &Expr,
    ) -> Expr {
        let body = self.lastcases_body(parent, n, use_true, x, j, prop, d);
        self.eq_bool(body, rhs.clone())
    }
}

#[cfg(test)]
mod tests {
    use crate::env::types::ConstantKind;
    use crate::env::{Environment, ProofQuality};
    use crate::expr::Expr;
    use crate::name::Name;
    use crate::tc::TypeChecker;

    const LEMMAS: &[&str] = &[
        "BoolAnalysis.extendF_castSucc",
        "BoolAnalysis.extendF_last",
        "BoolAnalysis.extendT_castSucc",
        "BoolAnalysis.extendT_last",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_peel_compute()
            .expect("init_boolean_analysis_peel_compute should succeed");
        env
    }

    #[test]
    fn test_init_idempotent() {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_peel_compute()
            .expect("first init");
        env.init_boolean_analysis_peel_compute()
            .expect("second init should be a no-op");
        assert!(env.has_boolean_analysis_peel_compute());
    }

    #[test]
    fn test_lemmas_registered_as_theorems() {
        let env = env();
        for name in LEMMAS {
            let info = env
                .get_const(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} should be registered"));
            assert_eq!(
                info.kind,
                ConstantKind::Theorem,
                "{name} must be a Theorem, got {:?}",
                info.kind
            );
        }
    }

    #[test]
    fn test_lemmas_type_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in LEMMAS {
            let e = Expr::const_(Name::from_string(name), vec![]);
            let _ = tc
                .infer_type(&e)
                .unwrap_or_else(|err| panic!("{name} should kernel-type-check, got: {err:?}"));
        }
    }

    #[test]
    fn test_lemmas_constructive_and_axiom_free() {
        let env = env();
        for name in LEMMAS {
            let deps = env
                .axiom_deps(&Name::from_string(name))
                .unwrap_or_else(|| panic!("axiom_deps should work for {name}"));
            let dep_names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
            assert!(
                dep_names.is_empty(),
                "{name} must have empty domain-axiom closure, got {dep_names:?}"
            );
            assert_eq!(
                env.proof_quality(&Name::from_string(name)),
                Some(ProofQuality::Constructive),
                "{name} must be Constructive"
            );
        }
    }
}

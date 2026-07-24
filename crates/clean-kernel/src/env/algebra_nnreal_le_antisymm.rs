// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — `NNReal.le_antisymm` (antisymmetry of the carrier
//! order), axiom-free.
//!
//! # Why this module exists (the missing brick for full `√(x·y) = √x·√y`)
//!
//! The square-level cross-term splitting `NNReal.sqrtGen_mul_sq` (both `√x·√y`
//! and `√(x·y)` square to `ofRat (x·y)`) is landed, but converting "both square
//! to the same thing" into the GENUINE EQUALITY `√(x·y) = √x·√y` needs
//! antisymmetry of `NNReal.le` (see the NOTE in `algebra_nnreal_sqrt_gen_mul.rs`
//! §"the full equality … is blocked on `NNReal.le_antisymm`"). This module
//! supplies exactly that brick.
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! - `NNReal.le_antisymm : ∀ a b : NNReal,`
//!     `NNReal.le a b → NNReal.le b a → @Eq NNReal a b`.
//!
//! # Proof
//!
//! Nested `Quot.ind` on `a` then `b` reduces the goal to: given representatives
//! `f, g : CauSeq` with `hfg : CauSeq.le f g` and `hgf : CauSeq.le g f`, produce
//! `Quot.mk Equiv f = Quot.mk Equiv g`. That is `Quot.sound f g heq` for an
//! `heq : Equiv f g`, where the equivalence is built pointwise: for `ε > 0`,
//! instantiate `hfg` and `hgf` at `ε` to get `∃N1, ∀n≥N1, vf n < vg n + ε` and
//! `∃N2, ∀n≥N2, vg n < vf n + ε`; witness `N := Nat.max N1 N2`, and at each
//! `n ≥ N` the two one-sided bounds (lifted to `n` via `Nat.le_max_left/right`
//! + `Nat.le_trans`) are exactly the two conjuncts of the `Equiv` bound pair.
//!
//! Because the lift target of `NNReal.le` is `Prop` and the hypotheses arrive on
//! `Quot.mk` representatives, `NNReal.le (Quot.mk f)(Quot.mk g)` ι-reduces to
//! `CauSeq.le f g`, so `hfg`/`hgf` are consumed directly as `CauSeq.le`.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, closure ⊆
//! {Quot.sound, propext, Classical.choice} ∪ Eq builtins (here exactly
//! `{Quot.sound}` modulo foundational). NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural` / `Real` / `Rat.dist`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles for antisymmetry.
struct AntiConsts {
    nat: Expr,
    rat: Expr,
    rat_zero: Expr,
    causeq: Expr,
    causeq_seq: Expr,
    causeq_equiv: Expr,
    nnrat_val: Expr,
    rat_add: Expr,
    rat_lt: Expr,
    nat_le: Expr,
    nat_max: Expr,
    nat_le_max_left: Expr,
    nat_le_max_right: Expr,
    nat_le_trans: Expr,
    and_c: Expr,
    and_intro: Expr,
    exists_c: Expr,
    exists_intro: Expr,
    exists_elim: Expr,
    quot: Expr,
    quot_mk: Expr,
    quot_sound: Expr,
    quot_ind: Expr,
    eq1: Expr,
}

impl AntiConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            causeq: k("NNReal.CauSeq"),
            causeq_seq: k("NNReal.CauSeq.seq"),
            causeq_equiv: k("NNReal.CauSeq.Equiv"),
            nnrat_val: k("NNRat.val"),
            rat_add: k("Rat.add"),
            rat_lt: k("Rat.lt"),
            nat_le: k("Nat.le"),
            nat_max: k("Nat.max"),
            nat_le_max_left: k("Nat.le_max_left"),
            nat_le_max_right: k("Nat.le_max_right"),
            nat_le_trans: k("Nat.le_trans"),
            and_c: k("And"),
            and_intro: k("And.intro"),
            exists_c: Expr::const_(Name::from_string("Exists"), vec![l1.clone()]),
            exists_intro: Expr::const_(Name::from_string("Exists.intro"), vec![l1.clone()]),
            exists_elim: Expr::const_(Name::from_string("Exists.elim"), vec![l1.clone()]),
            quot: Expr::const_(Name::from_string("Quot"), vec![l1.clone()]),
            quot_mk: Expr::const_(Name::from_string("Quot.mk"), vec![l1.clone()]),
            quot_sound: Expr::const_(Name::from_string("Quot.sound"), vec![l1.clone()]),
            quot_ind: Expr::const_(Name::from_string("Quot.ind"), vec![l1.clone()]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1]),
        }
    }

    fn nnreal(&self) -> Expr {
        Expr::apps(
            self.quot.clone(),
            [self.causeq.clone(), self.causeq_equiv.clone()],
        )
    }
    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    fn nat_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a, b])
    }
    /// `NNRat.val (NNReal.CauSeq.seq x n) : Rat`.
    fn vseq(&self, x: &Expr, n: &Expr) -> Expr {
        let seq = Expr::app(self.causeq_seq.clone(), x.clone());
        let at = Expr::app(seq, n.clone());
        Expr::app(self.nnrat_val.clone(), at)
    }
    fn quot_mk(&self, l: &Expr) -> Expr {
        Expr::apps(
            self.quot_mk.clone(),
            [self.causeq.clone(), self.causeq_equiv.clone(), l.clone()],
        )
    }
    fn nnle(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("NNReal.le"), vec![]),
            [a.clone(), b.clone()],
        )
    }
    fn eq_nn(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.nnreal(), a.clone(), b.clone()])
    }
    /// `Nat.max a b`.
    fn nmax(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nat_max.clone(), [a.clone(), b.clone()])
    }
    fn nat_le_trans(&self, a: &Expr, b: &Expr, cc: &Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(
            self.nat_le_trans.clone(),
            [a.clone(), b.clone(), cc.clone(), hab, hbc],
        )
    }
    /// `And p q : Prop`.
    fn and_ty(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.and_c.clone(), [p, q])
    }
    fn and_intro(&self, p: Expr, q: Expr, hp: Expr, hq: Expr) -> Expr {
        Expr::apps(self.and_intro.clone(), [p, q, hp, hq])
    }
    /// The Equiv bound pair at index `m`, tolerance `eps`:
    /// `And (vf m < vg m + eps)(vg m < vf m + eps)`.
    fn bound_pair(&self, f: &Expr, g: &Expr, m: &Expr, eps: &Expr) -> Expr {
        let vf = self.vseq(f, m);
        let vg = self.vseq(g, m);
        let left = self.lt(vf.clone(), self.add(vg.clone(), eps.clone()));
        let right = self.lt(vg, self.add(vf, eps.clone()));
        self.and_ty(left, right)
    }
    /// The one-sided domination predicate body `fun N => ∀ n, N≤n → vf n < vg n + eps`.
    fn le_pred(&self, parent: &EnvDeclBuilder, f: &Expr, g: &Expr, eps: &Expr) -> Expr {
        let mut bn = EnvDeclBuilder::child_of(parent);
        let (n_id, n_cap) = bn.fresh_local(self.nat.clone());
        let inner = {
            let mut bi = EnvDeclBuilder::child_of(&bn);
            let (m_id, m) = bi.fresh_local(self.nat.clone());
            let hle = self.nat_le(n_cap.clone(), m.clone());
            let (hle_id, _hle) = bi.fresh_local(hle.clone());
            let concl = self.lt(self.vseq(f, &m), self.add(self.vseq(g, &m), eps.clone()));
            let e = bi.mk_pi(hle_id, BinderInfo::Default, hle, concl);
            let e = bi.mk_pi(m_id, BinderInfo::Default, self.nat.clone(), e);
            bi.finish_child(e)
        };
        bn.finish_child(bn.mk_lam(n_id, BinderInfo::Default, self.nat.clone(), inner))
    }
    /// The Equiv predicate body `fun N => ∀ n, N≤n → bound_pair f g n eps`.
    fn equiv_pred(&self, parent: &EnvDeclBuilder, f: &Expr, g: &Expr, eps: &Expr) -> Expr {
        let mut bn = EnvDeclBuilder::child_of(parent);
        let (n_id, n_cap) = bn.fresh_local(self.nat.clone());
        let inner = {
            let mut bi = EnvDeclBuilder::child_of(&bn);
            let (m_id, m) = bi.fresh_local(self.nat.clone());
            let hle = self.nat_le(n_cap.clone(), m.clone());
            let (hle_id, _hle) = bi.fresh_local(hle.clone());
            let concl = self.bound_pair(f, g, &m, eps);
            let e = bi.mk_pi(hle_id, BinderInfo::Default, hle, concl);
            let e = bi.mk_pi(m_id, BinderInfo::Default, self.nat.clone(), e);
            bi.finish_child(e)
        };
        bn.finish_child(bn.mk_lam(n_id, BinderInfo::Default, self.nat.clone(), inner))
    }
    /// `∃ N, equiv_pred f g eps N : Prop`.
    fn exists_equiv(&self, parent: &EnvDeclBuilder, f: &Expr, g: &Expr, eps: &Expr) -> Expr {
        Expr::apps(
            self.exists_c.clone(),
            [self.nat.clone(), self.equiv_pred(parent, f, g, eps)],
        )
    }
    /// `le_pred f g eps N` fully applied (Π form).
    fn le_pred_at(
        &self,
        parent: &EnvDeclBuilder,
        f: &Expr,
        g: &Expr,
        eps: &Expr,
        cap: &Expr,
    ) -> Expr {
        let mut bn = EnvDeclBuilder::child_of(parent);
        let (m_id, m) = bn.fresh_local(self.nat.clone());
        let hle = self.nat_le(cap.clone(), m.clone());
        let (hle_id, _hle) = bn.fresh_local(hle.clone());
        let concl = self.lt(self.vseq(f, &m), self.add(self.vseq(g, &m), eps.clone()));
        let e = bn.mk_pi(hle_id, BinderInfo::Default, hle, concl);
        let e = bn.mk_pi(m_id, BinderInfo::Default, self.nat.clone(), e);
        bn.finish_child(e)
    }
    fn quot_sound(&self, a: &Expr, b: &Expr, h: Expr) -> Expr {
        Expr::apps(
            self.quot_sound.clone(),
            [
                self.causeq.clone(),
                self.causeq_equiv.clone(),
                a.clone(),
                b.clone(),
                h,
            ],
        )
    }
}

impl Environment {
    /// Register `NNReal.le_antisymm`. Idempotent.
    pub fn init_algebra_nnreal_le_antisymm(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_le()?; // NNReal.le, CauSeq.le, Equiv
        self.init_and()?;
        self.init_exists()?;
        self.register_nat_minmax_proofs()?; // Nat.max, le_max_left/right
        self.register_nat_le_trans_proof()?; // Nat.le_trans
        self.init_quot(); // Quot.sound, Quot.ind

        let c = AntiConsts::new();
        self.register_le_antisymm(&c)?;
        Ok(())
    }

    fn register_le_antisymm(&mut self, c: &AntiConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.le_antisymm");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let nnreal = c.nnreal();
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(nnreal.clone());
            let (bv_id, bv) = b.fresh_local(nnreal.clone());
            let hab = c.nnle(&a, &bv);
            let (hab_id, _hab) = b.fresh_local(hab.clone());
            let hba = c.nnle(&bv, &a);
            let (hba_id, _hba) = b.fresh_local(hba.clone());
            let concl = c.eq_nn(&a, &bv);
            let e = b.mk_pi(hba_id, BinderInfo::Default, hba, concl);
            let e = b.mk_pi(hab_id, BinderInfo::Default, hab, e);
            let e = b.mk_pi(bv_id, BinderInfo::Default, nnreal.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, nnreal.clone(), e);
            b.finish(e)
        };
        let value = build_antisymm_value(c, &nnreal);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// `fun a b => Quot.ind (motive_a)(minor_a) a`, where `minor_a f` does the inner
/// `Quot.ind` on `b` and the leaf `fun f g hfg hgf => Quot.sound f g (witness)`.
fn build_antisymm_value(c: &AntiConsts, nnreal: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(nnreal.clone());
    let (bv_id, bv) = b.fresh_local(nnreal.clone());

    // motive_a : fun a' => NNReal.le a' b → NNReal.le b a' → a' = b.
    let motive_a = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (ap_id, ap) = mb.fresh_local(nnreal.clone());
        let hab = c.nnle(&ap, &bv);
        let (hab_id, _h) = mb.fresh_local(hab.clone());
        let hba = c.nnle(&bv, &ap);
        let (hba_id, _h2) = mb.fresh_local(hba.clone());
        let concl = c.eq_nn(&ap, &bv);
        let e = mb.mk_pi(hba_id, BinderInfo::Default, hba, concl);
        let e = mb.mk_pi(hab_id, BinderInfo::Default, hab, e);
        mb.finish_child(mb.mk_lam(ap_id, BinderInfo::Default, nnreal.clone(), e))
    };

    // minor_a : fun (f : CauSeq) => <inner ind on b at Quot.mk f>.
    let minor_a = {
        let mut fb = EnvDeclBuilder::child_of(&b);
        let (f_id, f) = fb.fresh_local(c.causeq.clone());
        let qf = c.quot_mk(&f);

        // motive_b : fun b' => NNReal.le (Quot.mk f) b' → NNReal.le b' (Quot.mk f) → (Quot.mk f) = b'.
        let motive_b = {
            let mut mb = EnvDeclBuilder::child_of(&fb);
            let (bp_id, bp) = mb.fresh_local(nnreal.clone());
            let hab = c.nnle(&qf, &bp);
            let (hab_id, _h) = mb.fresh_local(hab.clone());
            let hba = c.nnle(&bp, &qf);
            let (hba_id, _h2) = mb.fresh_local(hba.clone());
            let concl = c.eq_nn(&qf, &bp);
            let e = mb.mk_pi(hba_id, BinderInfo::Default, hba, concl);
            let e = mb.mk_pi(hab_id, BinderInfo::Default, hab, e);
            mb.finish_child(mb.mk_lam(bp_id, BinderInfo::Default, nnreal.clone(), e))
        };

        // minor_b : fun (g : CauSeq) => fun hfg hgf => Quot.sound f g (witness).
        let minor_b = {
            let mut gb = EnvDeclBuilder::child_of(&fb);
            let (g_id, g) = gb.fresh_local(c.causeq.clone());
            let qg = c.quot_mk(&g);
            // hfg : NNReal.le (Quot.mk f)(Quot.mk g) ≡ CauSeq.le f g.
            let hfg_ty = c.nnle(&qf, &qg);
            let (hfg_id, hfg) = gb.fresh_local(hfg_ty.clone());
            let hgf_ty = c.nnle(&qg, &qf);
            let (hgf_id, hgf) = gb.fresh_local(hgf_ty.clone());

            // The hypotheses reduce (def-eq) to CauSeq.le f g and CauSeq.le g f;
            // we re-type them at those reduced types via the kernel's defeq by
            // passing them where CauSeq.le is expected (Quot.lift ι-rule).
            let witness = build_equiv_witness(c, &gb, &f, &g, &hfg, &hgf);
            let sound = c.quot_sound(&f, &g, witness); // Quot.mk f = Quot.mk g

            let e = gb.mk_lam(hgf_id, BinderInfo::Default, hgf_ty, sound);
            let e = gb.mk_lam(hfg_id, BinderInfo::Default, hfg_ty, e);
            gb.finish_child(gb.mk_lam(g_id, BinderInfo::Default, c.causeq.clone(), e))
        };

        let inner_ind = Expr::apps(
            c.quot_ind.clone(),
            [
                c.causeq.clone(),
                c.causeq_equiv.clone(),
                motive_b,
                minor_b,
                bv.clone(),
            ],
        );
        fb.finish_child(fb.mk_lam(f_id, BinderInfo::Default, c.causeq.clone(), inner_ind))
    };

    let outer_ind = Expr::apps(
        c.quot_ind.clone(),
        [
            c.causeq.clone(),
            c.causeq_equiv.clone(),
            motive_a,
            minor_a,
            a.clone(),
        ],
    );
    let e = b.mk_lam(bv_id, BinderInfo::Default, nnreal.clone(), outer_ind);
    let e = b.mk_lam(a_id, BinderInfo::Default, nnreal.clone(), e);
    b.finish(e)
}

/// Build `heq : Equiv f g` from `hfg : CauSeq.le f g` and `hgf : CauSeq.le g f`
/// (the hypotheses arrive typed at `NNReal.le (Quot.mk f)(Quot.mk g)` etc, which
/// ι-reduces to `CauSeq.le f g`; we consume them directly).
fn build_equiv_witness(
    c: &AntiConsts,
    parent: &EnvDeclBuilder,
    f: &Expr,
    g: &Expr,
    hfg: &Expr,
    hgf: &Expr,
) -> Expr {
    // Goal (Equiv f g body): ∀ ε, 0<ε → ∃ N, ∀ n, N≤n → bound_pair f g n ε.
    let mut bb = EnvDeclBuilder::child_of(parent);
    let (eps_id, eps) = bb.fresh_local(c.rat.clone());
    let hpos_ty = c.lt(c.rat_zero.clone(), eps.clone());
    let (hpos_id, hpos) = bb.fresh_local(hpos_ty.clone());

    // hfg ε hpos : ∃ N1, ∀ n, N1≤n → vf n < vg n + ε.
    let exists_fg = Expr::apps(hfg.clone(), [eps.clone(), hpos.clone()]);
    // hgf ε hpos : ∃ N2, ∀ n, N2≤n → vg n < vf n + ε.
    let exists_gf = Expr::apps(hgf.clone(), [eps.clone(), hpos.clone()]);

    let goal_exists = c.exists_equiv(&bb, f, g, &eps);
    let pred_fg = c.le_pred(&bb, f, g, &eps);
    let pred_gf = c.le_pred(&bb, g, f, &eps);

    // elim over exists_fg, then over exists_gf.
    let elim_fg = {
        let mut bo = EnvDeclBuilder::child_of(&bb);
        let (n1_id, n1) = bo.fresh_local(c.nat.clone());
        let hn1_ty = c.le_pred_at(&bo, f, g, &eps, &n1);
        let (hn1_id, hn1) = bo.fresh_local(hn1_ty.clone());

        let elim_gf = {
            let mut bi = EnvDeclBuilder::child_of(&bo);
            let (n2_id, n2) = bi.fresh_local(c.nat.clone());
            let hn2_ty = c.le_pred_at(&bi, g, f, &eps, &n2);
            let (hn2_id, hn2) = bi.fresh_local(hn2_ty.clone());

            let nmax = c.nmax(&n1, &n2);

            let witness = {
                let mut bw = EnvDeclBuilder::child_of(&bi);
                let (m_id, m) = bw.fresh_local(c.nat.clone());
                let hle_ty = c.nat_le(nmax.clone(), m.clone());
                let (hle_id, hle) = bw.fresh_local(hle_ty.clone());

                let le_max_l = Expr::apps(c.nat_le_max_left.clone(), [n1.clone(), n2.clone()]);
                let le_max_r = Expr::apps(c.nat_le_max_right.clone(), [n1.clone(), n2.clone()]);
                let n1_le_m = c.nat_le_trans(&n1, &nmax, &m, le_max_l, hle.clone());
                let n2_le_m = c.nat_le_trans(&n2, &nmax, &m, le_max_r, hle);

                // left  : vf m < vg m + ε   (hn1 m n1_le_m).
                let left = Expr::apps(hn1.clone(), [m.clone(), n1_le_m]);
                // right : vg m < vf m + ε   (hn2 m n2_le_m).
                let right = Expr::apps(hn2.clone(), [m.clone(), n2_le_m]);

                let vf = c.vseq(f, &m);
                let vg = c.vseq(g, &m);
                let l_ty = c.lt(vf.clone(), c.add(vg.clone(), eps.clone()));
                let r_ty = c.lt(vg, c.add(vf, eps.clone()));
                let proof = c.and_intro(l_ty, r_ty, left, right);

                let e = bw.mk_lam(hle_id, BinderInfo::Default, hle_ty, proof);
                let e = bw.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
                bw.finish_child(e)
            };

            let intro = Expr::apps(
                c.exists_intro.clone(),
                [c.nat.clone(), c.equiv_pred(&bi, f, g, &eps), nmax, witness],
            );
            let e = bi.mk_lam(hn2_id, BinderInfo::Default, hn2_ty, intro);
            let e = bi.mk_lam(n2_id, BinderInfo::Default, c.nat.clone(), e);
            bi.finish_child(e)
        };

        let elim2 = Expr::apps(
            c.exists_elim.clone(),
            [
                c.nat.clone(),
                pred_gf.clone(),
                goal_exists.clone(),
                exists_gf.clone(),
                elim_gf,
            ],
        );
        let e = bo.mk_lam(hn1_id, BinderInfo::Default, hn1_ty, elim2);
        let e = bo.mk_lam(n1_id, BinderInfo::Default, c.nat.clone(), e);
        bo.finish_child(e)
    };

    let elim = Expr::apps(
        c.exists_elim.clone(),
        [c.nat.clone(), pred_fg, goal_exists, exists_fg, elim_fg],
    );

    let e = bb.mk_lam(hpos_id, BinderInfo::Default, hpos_ty, elim);
    let e = bb.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    bb.finish_child(e)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const THEOREMS: &[&str] = &["NNReal.le_antisymm"];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_le_antisymm()
            .expect("init_algebra_nnreal_le_antisymm");
        env.init_algebra_nnreal_le_antisymm().expect("idempotent");
        env
    }

    #[test]
    fn test_le_antisymm_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in THEOREMS {
            let nm = Name::from_string(name);
            let info = env
                .get_const(&nm)
                .unwrap_or_else(|| panic!("{name} registered"));
            let value = info.value.clone().expect("value present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        }
    }

    #[test]
    fn test_le_antisymm_constructive_empty_closure() {
        let env = env();
        for name in THEOREMS {
            let nm = Name::from_string(name);
            let info = env.get_const(&nm).expect("registered");
            assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be Theorem");
            assert_eq!(
                env.proof_quality(&nm),
                Some(ProofQuality::Constructive),
                "{name} must be Constructive"
            );
            assert!(
                env.axiom_deps(&nm).expect("deps").is_empty(),
                "{name} closure must be foundational-only: {:?}",
                env.axiom_deps(&nm)
            );
        }
    }
}

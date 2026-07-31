// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive support lemmas for the `fourier_weight_parseval` discharge.
//!
//! The target identity (O'Donnell §1.4) is the level decomposition
//!   `Σ_{k=0}^{n} W^k[f] = Σ_S f̂(S)²`
//! where `W^k[f] = Σ_{|S|=k} f̂(S)²` is `FourierWeightAtLevel`. The proof
//! swaps the (level k, subset-index j) double sum and collapses the inner
//! k-sum pointwise: for a fixed subset `S = hcDecode n j` with popcount
//! `m = |S| ≤ n`, exactly one level `k ∈ {0,…,n}` matches the gate
//! `ind(Nat.beq m (Fin.val k))`, so the inner sum is `1` and the squared
//! coefficient is recovered.
//!
//! This module registers the reusable Nat/Fin primitives that discharge that
//! collapse with an EMPTY admitted-axiom closure:
//!
//! - `Nat.eq_of_beq_eq_true : ∀ a b, Nat.beq a b = true → a = b`
//!   — the missing forward reflection of `Nat.beq` (the false direction is the
//!     pre-existing `Nat.ne_of_beq_false`). Nested `Nat.rec` on `a` then `b`,
//!     mirroring `Nat.decEq`'s construction.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared constants for the `Nat.eq_of_beq_eq_true` proof.
struct BeqConsts {
    nat: Expr,
    bool_c: Expr,
    btrue: Expr,
    bfalse: Expr,
    zero: Expr,
    succ_c: Expr,
    nat_beq: Expr,
    eq_bool: Expr,
    eq_nat: Expr,
    eq_refl: Expr,
    nat_rec0: Expr,
    no_conf: Expr,
    congr_arg: Expr,
}

impl BeqConsts {
    fn new() -> Self {
        let one = Level::succ(Level::zero());
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            bool_c: Expr::const_(Name::from_string("Bool"), vec![]),
            btrue: Expr::const_(Name::from_string("Bool.true"), vec![]),
            bfalse: Expr::const_(Name::from_string("Bool.false"), vec![]),
            zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            succ_c: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_beq: Expr::const_(Name::from_string("Nat.beq"), vec![]),
            eq_bool: Expr::const_(Name::from_string("Eq"), vec![one.clone()]),
            eq_nat: Expr::const_(Name::from_string("Eq"), vec![one.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![one.clone()]),
            nat_rec0: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            no_conf: Expr::const_(Name::from_string("Bool.noConfusion"), vec![Level::zero()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![one.clone(), one]),
        }
    }
    fn succ(&self, x: Expr) -> Expr {
        Expr::app(self.succ_c.clone(), x)
    }
    fn beq(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.nat_beq.clone(), [x, y])
    }
    /// `@Eq Bool (Nat.beq x y) true`.
    fn beq_true(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(
            self.eq_bool.clone(),
            [self.bool_c.clone(), self.beq(x, y), self.btrue.clone()],
        )
    }
    /// `@Eq Nat l r`.
    fn eqn(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq_nat.clone(), [self.nat.clone(), l, r])
    }
    /// `@Bool.noConfusion.{0} P false true h : P`.
    fn noconf(&self, p: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.no_conf.clone(),
            [p, self.bfalse.clone(), self.btrue.clone(), h],
        )
    }
    /// Inner motive at fixed `a`: `fun (b : Nat) => Nat.beq a b = true → a = b`.
    fn inner_motive(&self, parent: &EnvDeclBuilder, a: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let (bv_id, bv) = b.fresh_local(self.nat.clone());
        let h_ty = self.beq_true(a.clone(), bv.clone());
        let concl = self.eqn(a.clone(), bv.clone());
        let body = Expr::arrow(h_ty, concl);
        b.finish_child(b.mk_lam(bv_id, BinderInfo::Default, self.nat.clone(), body))
    }
    /// Inner Pi-type `∀ b, Nat.beq a b = true → a = b` (the outer motive body).
    fn inner_prop(&self, parent: &EnvDeclBuilder, a: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let (bv_id, bv) = b.fresh_local(self.nat.clone());
        let h_ty = self.beq_true(a.clone(), bv.clone());
        let concl = self.eqn(a.clone(), bv.clone());
        let body = Expr::arrow(h_ty, concl);
        b.finish_child(b.mk_pi(bv_id, BinderInfo::Default, self.nat.clone(), body))
    }
}

impl Environment {
    /// Register `Nat.eq_of_beq_eq_true : ∀ (a b : Nat), Nat.beq a b = true → a = b`
    /// as a kernel-checked, constructive theorem. Idempotent.
    ///
    /// Outer `Nat.rec` on `a` with motive `C a := ∀ b, Nat.beq a b = true → a = b`;
    /// each branch is an inner `Nat.rec` on `b`. The four leaf cases:
    ///   * `(0, 0)`: `Eq.refl 0`.
    ///   * `(0, succ k)`: `Nat.beq 0 (succ k) ≡ false`, so the hypothesis is
    ///     `false = true`; `Bool.noConfusion` inhabits the goal `0 = succ k`.
    ///   * `(succ n, 0)`: symmetric — `Nat.beq (succ n) 0 ≡ false`.
    ///   * `(succ n, succ k)`: `Nat.beq (succ n)(succ k) ≡ Nat.beq n k`, so the
    ///     hypothesis is `Nat.beq n k = true`; `ih n k h : n = k` lifts to
    ///     `succ n = succ k` by `congrArg Nat.succ`.
    pub(crate) fn register_nat_eq_of_beq_eq_true(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE withholds the Clean-native `Nat.beq` definition so the
        // genuine Lean value can import. This theorem is stated directly over
        // that withheld head and must travel with the same overlay cluster.
        // Guard the registrar itself because callers outside prelude setup may
        // invoke it on an import environment too.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        let name = Name::from_string("Nat.eq_of_beq_eq_true");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        // SOUNDNESS: import-mode Nat core arithmetic cluster gate — the
        // theorem is stated over the import-gated `Nat.beq` seed (see
        // order_nat_cmp.rs::init_nat_cmp); with the seed withheld the
        // statement cannot even be formed ("Unknown constant: Nat.beq" broke
        // `try_with_prelude_for_import` outright). The genuine olean lemma
        // imports through the checked path instead. Same gate discipline as
        // `register_nat_ble_le_lemmas`; default lane byte-identical.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        self.init_eq()?;
        self.init_nat()?;
        self.init_bool()?;
        self.init_nat_cmp()?; // Nat.beq
        if self
            .get_const(&Name::from_string("Bool.noConfusion"))
            .is_none()
        {
            self.regenerate_missing_no_confusion();
        }

        let c = BeqConsts::new();

        // ── Type: ∀ (a b : Nat), Nat.beq a b = true → a = b ──
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.nat.clone());
            let (bv_id, bv) = b.fresh_local(c.nat.clone());
            let h_ty = c.beq_true(a.clone(), bv.clone());
            let (h_id, _h) = b.fresh_local(h_ty.clone());
            let concl = c.eqn(a.clone(), bv.clone());
            let e = b.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // value : @Nat.rec.{0} outer_c z_case s_case
        let value = {
            let b = EnvDeclBuilder::new();

            // outer motive : fun (a : Nat) => ∀ b, Nat.beq a b = true → a = b
            let outer_c = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = d.fresh_local(c.nat.clone());
                let body = c.inner_prop(&d, &a);
                d.finish_child(d.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), body))
            };

            // ── zCase (a = 0): inner Nat.rec on b ──
            let z_case = {
                let d = EnvDeclBuilder::child_of(&b);
                let z_motive = c.inner_motive(&d, &c.zero);
                // b = 0 : fun (h : Nat.beq 0 0 = true) => Eq.refl 0
                let z_inner_z = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let h_ty = c.beq_true(c.zero.clone(), c.zero.clone());
                    let (h_id, _h) = e.fresh_local(h_ty.clone());
                    let body = Expr::apps(c.eq_refl.clone(), [c.nat.clone(), c.zero.clone()]);
                    e.finish_child(e.mk_lam(h_id, BinderInfo::Default, h_ty, body))
                };
                // b = succ k : fun (k) (_ih) (h : Nat.beq 0 (succ k) = true) =>
                //   Bool.noConfusion (0 = succ k) h
                let z_inner_s = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let (k_id, k) = e.fresh_local(c.nat.clone());
                    let ih_ty = c.inner_motive_app(&e, &c.zero, &k);
                    let (ih_id, _ih) = e.fresh_local(ih_ty.clone());
                    let h_ty = c.beq_true(c.zero.clone(), c.succ(k.clone()));
                    let (h_id, h) = e.fresh_local(h_ty.clone());
                    let goal = c.eqn(c.zero.clone(), c.succ(k.clone()));
                    let body = c.noconf(goal, h);
                    let inner = e.mk_lam(h_id, BinderInfo::Default, h_ty, body);
                    let inner = e.mk_lam(ih_id, BinderInfo::Default, ih_ty, inner);
                    e.finish_child(e.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), inner))
                };
                let rec = Expr::apps(c.nat_rec0.clone(), [z_motive, z_inner_z, z_inner_s]);
                d.finish_child(rec)
            };

            // ── sCase (a = succ n): fun (n) (ih_n : C n) => inner Nat.rec on b ──
            let s_case = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (n_id, n) = d.fresh_local(c.nat.clone());
                let ih_n_ty = c.inner_prop(&d, &n);
                let (ihn_id, ih_n) = d.fresh_local(ih_n_ty.clone());
                let sn = c.succ(n.clone());
                let s_motive = c.inner_motive(&d, &sn);

                // b = 0 : fun (h : Nat.beq (succ n) 0 = true) =>
                //   Bool.noConfusion (succ n = 0) h
                let s_inner_z = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let h_ty = c.beq_true(sn.clone(), c.zero.clone());
                    let (h_id, h) = e.fresh_local(h_ty.clone());
                    let goal = c.eqn(sn.clone(), c.zero.clone());
                    let body = c.noconf(goal, h);
                    e.finish_child(e.mk_lam(h_id, BinderInfo::Default, h_ty, body))
                };
                // b = succ k : fun (k) (_ih) (h : Nat.beq (succ n)(succ k) = true) =>
                //   congrArg Nat.succ (ih_n k h)
                let s_inner_s = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let (k_id, k) = e.fresh_local(c.nat.clone());
                    let ih_ty = c.inner_motive_app(&e, &sn, &k);
                    let (ih_id, _ih) = e.fresh_local(ih_ty.clone());
                    let h_ty = c.beq_true(sn.clone(), c.succ(k.clone()));
                    let (h_id, h) = e.fresh_local(h_ty.clone());
                    // ih_n k h : n = k  (h accepted at `Nat.beq n k = true` by def-eq)
                    let n_eq_k = Expr::apps(ih_n.clone(), [k.clone(), h.clone()]);
                    let body = Expr::apps(
                        c.congr_arg.clone(),
                        [
                            c.nat.clone(),
                            c.nat.clone(),
                            n.clone(),
                            k.clone(),
                            c.succ_c.clone(),
                            n_eq_k,
                        ],
                    );
                    let inner = e.mk_lam(h_id, BinderInfo::Default, h_ty, body);
                    let inner = e.mk_lam(ih_id, BinderInfo::Default, ih_ty, inner);
                    e.finish_child(e.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), inner))
                };
                let rec = Expr::apps(c.nat_rec0.clone(), [s_motive, s_inner_z, s_inner_s]);
                let inner = d.mk_lam(ihn_id, BinderInfo::Default, ih_n_ty, rec);
                d.finish_child(d.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), inner))
            };

            let body = Expr::apps(c.nat_rec0.clone(), [outer_c, z_case, s_case]);
            b.finish(body)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }
}

impl BeqConsts {
    /// `(inner_motive a) b` β-reduced = `Nat.beq a b = true → a = b`, the IH type
    /// passed to the inner `Nat.rec` successor minor premise.
    fn inner_motive_app(&self, parent: &EnvDeclBuilder, a: &Expr, b: &Expr) -> Expr {
        let _ = parent;
        let h_ty = self.beq_true(a.clone(), b.clone());
        let concl = self.eqn(a.clone(), b.clone());
        Expr::arrow(h_ty, concl)
    }
}

/// Shared constants for the `fourier_level_collapse` proof.
#[cfg(any(test, feature = "math-overlays"))]
struct CollapseConsts {
    nat: Expr,
    rat: Expr,
    fin: Expr,
    bool_c: Expr,
    btrue: Expr,
    bfalse: Expr,
    nat_succ: Expr,
    #[cfg(test)]
    nat_lt: Expr,
    nat_beq: Expr,
    nat_beq_refl: Expr,
    nat_succ_le_succ: Expr,
    nat_eq_of_beq: Expr,
    fin_mk: Expr,
    fin_val: Expr,
    fin_eq_of_val_eq: Expr,
    fin_sum: Expr,
    fin_sum_diag: Expr,
    ind: Expr,
    rat_mul: Expr,
    rat_one: Expr,
    rat_zero: Expr,
    rat_one_mul: Expr,
    rat_zero_mul: Expr,
    bool_rec: Expr,
    false_elim: Expr,
    eq1: Expr,
    eq_refl1: Expr,
    eq_trans1: Expr,
    eq_symm1: Expr,
    congr_arg: Expr,
}

#[cfg(any(test, feature = "math-overlays"))]
impl CollapseConsts {
    fn new() -> Self {
        let one = Level::succ(Level::zero());
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            bool_c: Expr::const_(Name::from_string("Bool"), vec![]),
            btrue: Expr::const_(Name::from_string("Bool.true"), vec![]),
            bfalse: Expr::const_(Name::from_string("Bool.false"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            #[cfg(test)]
            nat_lt: Expr::const_(Name::from_string("Nat.lt"), vec![]),
            nat_beq: Expr::const_(Name::from_string("Nat.beq"), vec![]),
            nat_beq_refl: Expr::const_(Name::from_string("Nat.beq_refl"), vec![]),
            nat_succ_le_succ: Expr::const_(Name::from_string("Nat.succ_le_succ"), vec![]),
            nat_eq_of_beq: Expr::const_(Name::from_string("Nat.eq_of_beq_eq_true"), vec![]),
            fin_mk: Expr::const_(Name::from_string("Fin.mk"), vec![]),
            fin_val: Expr::const_(Name::from_string("Fin.val"), vec![]),
            fin_eq_of_val_eq: Expr::const_(Name::from_string("Fin.eq_of_val_eq"), vec![]),
            fin_sum: Expr::const_(Name::from_string("Fin.sum"), vec![]),
            fin_sum_diag: Expr::const_(Name::from_string("Fin.sum_diag_collapse"), vec![]),
            ind: Expr::const_(Name::from_string("BoolAnalysis.ind"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            rat_one: Expr::const_(Name::from_string("Rat.one"), vec![]),
            rat_zero: Expr::const_(Name::from_string("Rat.zero"), vec![]),
            rat_one_mul: Expr::const_(Name::from_string("Rat.one_mul"), vec![]),
            rat_zero_mul: Expr::const_(Name::from_string("Rat.zero_mul"), vec![]),
            bool_rec: Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
            false_elim: Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![one.clone()]),
            eq_refl1: Expr::const_(Name::from_string("Eq.refl"), vec![one.clone()]),
            eq_trans1: Expr::const_(Name::from_string("Eq.trans"), vec![one.clone()]),
            eq_symm1: Expr::const_(Name::from_string("Eq.symm"), vec![one.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![one.clone(), one]),
        }
    }
    fn succ(&self, x: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), x)
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn beq(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.nat_beq.clone(), [x, y])
    }
    /// `@Fin.val n k`.
    fn val(&self, n: &Expr, k: &Expr) -> Expr {
        Expr::apps(self.fin_val.clone(), [n.clone(), k.clone()])
    }
    /// `@Eq Bool l r`.
    fn eq_bool(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.bool_c.clone(), l, r])
    }
    /// `@Eq Nat l r`.
    #[cfg(test)]
    fn eq_nat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.nat.clone(), l, r])
    }
    /// `@Eq (Fin n) l r`.
    fn eq_fin(&self, n: &Expr, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.fin_of(n), l, r])
    }
    /// `@Eq Rat l r`.
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), l, r])
    }
    /// `Rat.mul (ind (Nat.beq m (Fin.val (n+1) k))) x` — the summand at `k`.
    fn summand(&self, np1: &Expr, m: &Expr, x: &Expr, k: &Expr) -> Expr {
        let gate = Expr::app(self.ind.clone(), self.beq(m.clone(), self.val(np1, k)));
        Expr::apps(self.rat_mul.clone(), [gate, x.clone()])
    }
    /// `fun (k : Fin (n+1)) => summand k` — the diag-collapse function `g`.
    fn g_fn(&self, parent: &EnvDeclBuilder, np1: &Expr, m: &Expr, x: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin = self.fin_of(np1);
        let (k_id, k) = b.fresh_local(fin.clone());
        let body = self.summand(np1, m, x, &k);
        b.finish_child(b.mk_lam(k_id, BinderInfo::Default, fin, body))
    }
    fn trans_rat(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans1.clone(), [self.rat.clone(), a, b, cc, h1, h2])
    }
}

#[cfg(any(test, feature = "math-overlays"))]
impl Environment {
    /// Register `BoolAnalysis.fourier_level_collapse :
    ///   ∀ (n m : Nat) (x : Rat), Nat.le m n →
    ///     Fin.sum (Nat.succ n)
    ///       (fun (k : Fin (n+1)) => Rat.mul (ind (Nat.beq m (Fin.val (n+1) k))) x)
    ///       = x`
    /// as a kernel-checked, constructive theorem. Idempotent.
    ///
    /// The level-index indicator collapse: for a popcount `m ≤ n`, exactly one
    /// level `k ∈ {0,…,n}` satisfies `Nat.beq m (Fin.val k)`, so the gated sum
    /// reduces to the single matched term `1·x = x`. Proved via
    /// `Fin.sum_diag_collapse (n+1) j g` at the diagonal `j := Fin.mk (n+1) m h`
    /// (`h : Nat.lt m (n+1)` from `Nat.succ_le_succ` on the `m ≤ n` premise):
    ///   * diagonal `g j = Rat.mul (ind (Nat.beq m m)) x ≡ Rat.mul 1 x = x`
    ///     (`Nat.beq_refl`, `ind true ≡ Rat.one`, `Rat.one_mul`);
    ///   * off-diagonal `k ≠ j ⟹ g k = 0`: case on `Nat.beq m (Fin.val k)` —
    ///     in the `true` branch `Nat.eq_of_beq_eq_true` gives `m = Fin.val k`,
    ///     hence `Fin.val k = Fin.val j` and `Fin.eq_of_val_eq` gives `k = j`,
    ///     contradicting `k ≠ j`; so the gate is `false`, `ind false ≡ 0`, and
    ///     `Rat.zero_mul x = 0`.
    pub(crate) fn register_fourier_level_collapse(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.fourier_level_collapse");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        // Prerequisites.
        self.init_boolean_analysis()?; // ind, Fin.sum, Rat foundations
        self.register_nat_eq_of_beq_eq_true()?;
        self.register_nat_beq_lemmas()?; // Nat.beq_refl
        self.register_nat_arith_order_proofs()?; // Nat.succ_le_succ
        self.register_fin_dec_eq_proof()?; // Fin.eq_of_val_eq
        self.register_fin_sum_diag_collapse_theorem()?;
        self.rat_quotient_payoff_into_live()?; // Rat.zero_mul
        {
            let qc = crate::env::algebra_rat_quotient::RatRawConsts::new();
            self.register_rat_q_structural(&qc)?; // Rat.one_mul
        }

        let c = CollapseConsts::new();

        // ── Type: ∀ (n m : Nat)(x : Rat), Nat.le m n → Fin.sum (n+1) g = x ──
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let np1 = c.succ(n.clone());
            // hle : Nat.le m n
            let nat_le = Expr::const_(Name::from_string("Nat.le"), vec![]);
            let hle_ty = Expr::apps(nat_le.clone(), [m.clone(), n.clone()]);
            let (h_id, _h) = b.fresh_local(hle_ty.clone());
            let g = c.g_fn(&b, &np1, &m, &x);
            let lhs = Expr::apps(c.fin_sum.clone(), [np1.clone(), g]);
            let concl = c.eq_rat(lhs, x.clone());
            let e = b.mk_pi(h_id, BinderInfo::Default, hle_ty, concl);
            let e = b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let np1 = c.succ(n.clone());
            let nat_le = Expr::const_(Name::from_string("Nat.le"), vec![]);
            let hle_ty = Expr::apps(nat_le.clone(), [m.clone(), n.clone()]);
            let (h_id, hle) = b.fresh_local(hle_ty.clone());

            let fin_np1 = c.fin_of(&np1);
            let g = c.g_fn(&b, &np1, &m, &x);

            // h_lt : Nat.lt m (n+1) ≡ Nat.le (succ m)(succ n) := Nat.succ_le_succ m n hle
            let h_lt = Expr::apps(
                c.nat_succ_le_succ.clone(),
                [m.clone(), n.clone(), hle.clone()],
            );
            // j := @Fin.mk (n+1) m h_lt   (Fin.val j ≡ m, Fin.isLt j ≡ h_lt)
            let j = Expr::apps(c.fin_mk.clone(), [np1.clone(), m.clone(), h_lt.clone()]);

            // ── off-diagonal hypothesis H : ∀ (k : Fin(n+1)),
            //      (k = j → False) → g k = Rat.zero ──
            let hyp = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (k_id, k) = d.fresh_local(fin_np1.clone());
                let ne_ty = Expr::arrow(
                    c.eq_fin(&np1, k.clone(), j.clone()),
                    Expr::const_(Name::from_string("False"), vec![]),
                );
                let (hne_id, hne) = d.fresh_local(ne_ty.clone());

                // gate := Nat.beq m (Fin.val (n+1) k)
                let valk = c.val(&np1, &k);
                let gate = c.beq(m.clone(), valk.clone());

                // bool-case motive : fun (bb : Bool) =>
                //   @Eq Bool gate bb → @Eq Bool gate false
                let motive = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let (bb_id, bb) = e.fresh_local(c.bool_c.clone());
                    let body = Expr::arrow(
                        c.eq_bool(gate.clone(), bb.clone()),
                        c.eq_bool(gate.clone(), c.bfalse.clone()),
                    );
                    e.finish_child(e.mk_lam(bb_id, BinderInfo::Default, c.bool_c.clone(), body))
                };
                // false-case : fun (hbf : gate = false) => hbf
                let false_case = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let hbf_ty = c.eq_bool(gate.clone(), c.bfalse.clone());
                    let (hbf_id, hbf) = e.fresh_local(hbf_ty.clone());
                    e.finish_child(e.mk_lam(hbf_id, BinderInfo::Default, hbf_ty, hbf))
                };
                // true-case : fun (hbt : gate = true) => False.elim (gate = false) contra
                let true_case = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let hbt_ty = c.eq_bool(gate.clone(), c.btrue.clone());
                    let (hbt_id, hbt) = e.fresh_local(hbt_ty.clone());
                    // m_eq_valk : m = Fin.val k := Nat.eq_of_beq_eq_true m (val k) hbt
                    let m_eq_valk = Expr::apps(
                        c.nat_eq_of_beq.clone(),
                        [m.clone(), valk.clone(), hbt.clone()],
                    );
                    // valk_eq_m : Fin.val k = m := Eq.symm m_eq_valk
                    let valk_eq_m = Expr::apps(
                        c.eq_symm1.clone(),
                        [c.nat.clone(), m.clone(), valk.clone(), m_eq_valk],
                    );
                    // Fin.val (n+1) j ≡ m, so valk_eq_m : Fin.val k = Fin.val j (def-eq).
                    //   eq_of_val_eq needs @Eq Nat (Fin.val k)(Fin.val j).
                    let valj = c.val(&np1, &j);
                    let valk_eq_valj = valk_eq_m; // def-eq retarget (Fin.val j ≡ m)
                    let _ = valj;
                    // k_eq_j : k = j := Fin.eq_of_val_eq (n+1) k j valk_eq_valj
                    let k_eq_j = Expr::apps(
                        c.fin_eq_of_val_eq.clone(),
                        [np1.clone(), k.clone(), j.clone(), valk_eq_valj],
                    );
                    // contra : False := hne k_eq_j
                    let contra = Expr::app(hne.clone(), k_eq_j);
                    // False.elim (gate = false) contra
                    let goal_false = c.eq_bool(gate.clone(), c.bfalse.clone());
                    let body = Expr::apps(c.false_elim.clone(), [goal_false, contra]);
                    e.finish_child(e.mk_lam(hbt_id, BinderInfo::Default, hbt_ty, body))
                };
                // gate_false : gate = false :=
                //   @Bool.rec motive false_case true_case gate (Eq.refl Bool gate)
                let rec = Expr::apps(
                    c.bool_rec.clone(),
                    [motive, false_case, true_case, gate.clone()],
                );
                let gate_false = Expr::app(
                    rec,
                    Expr::apps(c.eq_refl1.clone(), [c.bool_c.clone(), gate.clone()]),
                );

                // ind_zero : ind gate = Rat.zero
                //   := congrArg ind gate_false  then  ind false ≡ Rat.zero (def-eq)
                //   We retarget directly: congrArg gives `ind gate = ind false`;
                //   `ind false` ≡ `Rat.zero`, so the same term has type
                //   `ind gate = Rat.zero` by def-eq.
                let ind_gate = Expr::app(c.ind.clone(), gate.clone());
                let ind_false = Expr::app(c.ind.clone(), c.bfalse.clone());
                let ind_zero = Expr::apps(
                    c.congr_arg.clone(),
                    [
                        c.bool_c.clone(),
                        c.rat.clone(),
                        gate.clone(),
                        c.bfalse.clone(),
                        c.ind.clone(),
                        gate_false,
                    ],
                ); // : ind gate = ind false ≡ Rat.zero
                let _ = ind_false;

                // gk = Rat.mul (ind gate) x.  Want gk = Rat.zero.
                //   step1 : Rat.mul (ind gate) x = Rat.mul Rat.zero x
                //             := congrArg (fun y => Rat.mul y x) ind_zero
                let mul_by_x = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let (y_id, y) = e.fresh_local(c.rat.clone());
                    let body = Expr::apps(c.rat_mul.clone(), [y, x.clone()]);
                    e.finish_child(e.mk_lam(y_id, BinderInfo::Default, c.rat.clone(), body))
                };
                let mul_ind_x = Expr::apps(c.rat_mul.clone(), [ind_gate.clone(), x.clone()]);
                let mul_zero_x = Expr::apps(c.rat_mul.clone(), [c.rat_zero.clone(), x.clone()]);
                let step1 = Expr::apps(
                    c.congr_arg.clone(),
                    [
                        c.rat.clone(),
                        c.rat.clone(),
                        ind_gate.clone(),
                        c.rat_zero.clone(),
                        mul_by_x,
                        ind_zero,
                    ],
                ); // : Rat.mul (ind gate) x = Rat.mul Rat.zero x
                   // step2 : Rat.mul Rat.zero x = Rat.zero := Rat.zero_mul x
                let step2 = Expr::app(c.rat_zero_mul.clone(), x.clone());
                let gk_zero = c.trans_rat(mul_ind_x, mul_zero_x, c.rat_zero.clone(), step1, step2);

                let e = d.mk_lam(hne_id, BinderInfo::Default, ne_ty, gk_zero);
                d.finish_child(d.mk_lam(k_id, BinderInfo::Default, fin_np1.clone(), e))
            };

            // collapse : Fin.sum (n+1) g = g j   := Fin.sum_diag_collapse (n+1) j g hyp
            let collapse = Expr::apps(
                c.fin_sum_diag.clone(),
                [np1.clone(), j.clone(), g.clone(), hyp],
            );

            // g j = Rat.mul (ind (Nat.beq m m)) x  (Fin.val j ≡ m).
            //   diag_x : g j = x
            //   beq_mm_true : Nat.beq m m = true := Nat.beq_refl m
            let beq_mm = c.beq(m.clone(), m.clone());
            let beq_mm_true = Expr::app(c.nat_beq_refl.clone(), m.clone());
            // ind (Nat.beq m m) = ind true ≡ Rat.one
            //   ind_eq_one : ind (Nat.beq m m) = Rat.one
            //     := congrArg ind beq_mm_true  (ind true ≡ Rat.one def-eq)
            let ind_mm = Expr::app(c.ind.clone(), beq_mm.clone());
            let ind_eq_one = Expr::apps(
                c.congr_arg.clone(),
                [
                    c.bool_c.clone(),
                    c.rat.clone(),
                    beq_mm.clone(),
                    c.btrue.clone(),
                    c.ind.clone(),
                    beq_mm_true,
                ],
            ); // : ind (Nat.beq m m) = ind true ≡ Rat.one
               // gj = Rat.mul (ind (Nat.beq m m)) x  (this is `g j` after Fin.val j ≡ m).
               //   stepA : Rat.mul (ind (Nat.beq m m)) x = Rat.mul Rat.one x
            let mul_by_x2 = {
                let mut e = EnvDeclBuilder::child_of(&b);
                let (y_id, y) = e.fresh_local(c.rat.clone());
                let body = Expr::apps(c.rat_mul.clone(), [y, x.clone()]);
                e.finish_child(e.mk_lam(y_id, BinderInfo::Default, c.rat.clone(), body))
            };
            let mul_indmm_x = Expr::apps(c.rat_mul.clone(), [ind_mm.clone(), x.clone()]);
            let mul_one_x = Expr::apps(c.rat_mul.clone(), [c.rat_one.clone(), x.clone()]);
            let step_a = Expr::apps(
                c.congr_arg.clone(),
                [
                    c.rat.clone(),
                    c.rat.clone(),
                    ind_mm.clone(),
                    c.rat_one.clone(),
                    mul_by_x2,
                    ind_eq_one,
                ],
            ); // : Rat.mul (ind (Nat.beq m m)) x = Rat.mul Rat.one x
               // stepB : Rat.mul Rat.one x = x := Rat.one_mul x
            let step_b = Expr::app(c.rat_one_mul.clone(), x.clone());
            let gj_eq_x = c.trans_rat(mul_indmm_x.clone(), mul_one_x, x.clone(), step_a, step_b); // : g j = x   (mul_indmm_x ≡ g j by Fin.val j ≡ m)

            // proof : Fin.sum (n+1) g = x  := Eq.trans collapse gj_eq_x
            let sum_g = Expr::apps(c.fin_sum.clone(), [np1.clone(), g.clone()]);
            let gj = Expr::app(g.clone(), j.clone());
            let proof = c.trans_rat(sum_g, gj, x.clone(), collapse, gj_eq_x);

            let e = b.mk_lam(h_id, BinderInfo::Default, hle_ty, proof);
            let e = b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }
}

/// Shared constants for the `Fin.sumNat_le_card` proof.
#[cfg(any(test, feature = "math-overlays"))]
struct SumNatLeConsts {
    nat: Expr,
    fin: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_one: Expr,
    nat_add: Expr,
    nat_le: Expr,
    nat_le_refl: Expr,
    nat_add_le_add: Expr,
    fin_sum_nat: Expr,
    fin_cast_succ: Expr,
    fin_last: Expr,
    nat_rec1: Expr,
}

#[cfg(any(test, feature = "math-overlays"))]
impl SumNatLeConsts {
    fn new() -> Self {
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        Self {
            nat: nat.clone(),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            nat_zero: nat_zero.clone(),
            nat_succ: nat_succ.clone(),
            nat_one: Expr::app(nat_succ, nat_zero),
            nat_add: Expr::const_(Name::from_string("Nat.add"), vec![]),
            nat_le: Expr::const_(Name::from_string("Nat.le"), vec![]),
            nat_le_refl: Expr::const_(Name::from_string("Nat.le_refl"), vec![]),
            nat_add_le_add: Expr::const_(Name::from_string("Nat.add_le_add"), vec![]),
            fin_sum_nat: Expr::const_(Name::from_string("Fin.sumNat"), vec![]),
            fin_cast_succ: Expr::const_(Name::from_string("Fin.castSucc"), vec![]),
            fin_last: Expr::const_(Name::from_string("Fin.last"), vec![]),
            nat_rec1: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
        }
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn fin_to_nat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.fin_of(n), self.nat.clone())
    }
    fn succ(&self, x: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), x)
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a, b])
    }
    fn sum_nat(&self, n: Expr, g: Expr) -> Expr {
        Expr::apps(self.fin_sum_nat.clone(), [n, g])
    }
    /// `∀ (i : Fin n), Nat.le (g i) 1` — the bounded-summand hypothesis at `g`.
    fn bound_hyp(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin.clone());
        let body = self.le(Expr::app(g.clone(), i), self.nat_one.clone());
        b.finish_child(b.mk_pi(i_id, BinderInfo::Default, fin, body))
    }
    /// Motive `C n := ∀ (g : Fin n → Nat), (∀ i, g i ≤ 1) → Fin.sumNat n g ≤ n`.
    fn motive_body(&self, parent: &EnvDeclBuilder, n: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let g_ty = self.fin_to_nat(n);
        let (g_id, g) = b.fresh_local(g_ty.clone());
        let h_ty = self.bound_hyp(&b, n, &g);
        let concl = self.le(self.sum_nat(n.clone(), g.clone()), n.clone());
        let inner = Expr::arrow(h_ty, concl);
        b.finish_child(b.mk_pi(g_id, BinderInfo::Default, g_ty, inner))
    }
}

#[cfg(any(test, feature = "math-overlays"))]
impl Environment {
    /// Register `Fin.sumNat_le_card :
    ///   ∀ (n : Nat) (g : Fin n → Nat), (∀ i, Nat.le (g i) 1) → Nat.le (Fin.sumNat n g) n`
    /// as a kernel-checked, constructive theorem. Idempotent.
    ///
    /// `Nat.rec` on `n`. Base `Fin.sumNat 0 g ≡ 0 ≤ 0` (`Nat.le_refl`). Step
    /// peels `Fin.sumNat (k+1) g ≡ Nat.add (Fin.sumNat k (g∘castSucc)) (g (last k))`
    /// and combines the IH `Fin.sumNat k (g∘castSucc) ≤ k` with `g (last k) ≤ 1`
    /// via `Nat.add_le_add` into `≤ Nat.add k 1 ≡ Nat.succ k`.
    pub(crate) fn register_fin_sum_nat_le_card(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Fin.sumNat_le_card");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?; // Fin.sumNat, Fin.castSucc, Fin.last
        self.register_nat_arith_order_proofs()?; // Nat.le_refl, Nat.add_le_add

        let c = SumNatLeConsts::new();

        // ── Type: ∀ (n g), (∀ i, g i ≤ 1) → Fin.sumNat n g ≤ n ──
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let g_ty = c.fin_to_nat(&n);
            let (g_id, g) = b.fresh_local(g_ty.clone());
            let h_ty = c.bound_hyp(&b, &n, &g);
            let (h_id, _h) = b.fresh_local(h_ty.clone());
            let concl = c.le(c.sum_nat(n.clone(), g.clone()), n.clone());
            let e = b.mk_pi(h_id, BinderInfo::Default, h_ty, concl);
            let e = b.mk_pi(g_id, BinderInfo::Default, g_ty, e);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        let value = {
            let b = EnvDeclBuilder::new();

            // motive : fun (n : Nat) => ∀ g, (∀ i, g i ≤ 1) → Fin.sumNat n g ≤ n
            let motive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (n_id, n) = d.fresh_local(c.nat.clone());
                let body = c.motive_body(&d, &n);
                d.finish_child(d.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body))
            };

            // base : motive 0 = fun (g) (_h) => Nat.le_refl 0
            //   (Fin.sumNat 0 g ≡ Nat.zero, so Nat.le_refl 0 : 0 ≤ 0 ≡ Fin.sumNat 0 g ≤ 0)
            let base = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let g_ty = c.fin_to_nat(&c.nat_zero);
                let (g_id, g) = d.fresh_local(g_ty.clone());
                let h_ty = c.bound_hyp(&d, &c.nat_zero, &g);
                let (h_id, _h) = d.fresh_local(h_ty.clone());
                let body = Expr::app(c.nat_le_refl.clone(), c.nat_zero.clone());
                let e = d.mk_lam(h_id, BinderInfo::Default, h_ty, body);
                d.finish_child(d.mk_lam(g_id, BinderInfo::Default, g_ty, e))
            };

            // step : fun (k) (ih : motive k) (g : Fin (k+1) → Nat) (h : ∀ i, g i ≤ 1) =>
            //   Nat.add_le_add (Fin.sumNat k (g∘castSucc)) k (g (last k)) 1
            //     (ih (g∘castSucc) (h∘castSucc)) (h (last k))
            let step = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (k_id, k) = d.fresh_local(c.nat.clone());
                let ih_ty = c.motive_body(&d, &k);
                let (ih_id, ih) = d.fresh_local(ih_ty.clone());
                let sk = c.succ(k.clone());
                let g_ty = c.fin_to_nat(&sk);
                let (g_id, g) = d.fresh_local(g_ty.clone());
                let h_ty = c.bound_hyp(&d, &sk, &g);
                let (h_id, h) = d.fresh_local(h_ty.clone());

                // g∘castSucc : Fin k → Nat := fun (i : Fin k) => g (Fin.castSucc k i)
                let g_cast = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let fin_k = c.fin_of(&k);
                    let (i_id, i) = e.fresh_local(fin_k.clone());
                    let cast_i = Expr::apps(c.fin_cast_succ.clone(), [k.clone(), i]);
                    let body = Expr::app(g.clone(), cast_i);
                    e.finish_child(e.mk_lam(i_id, BinderInfo::Default, fin_k, body))
                };
                // h∘castSucc : ∀ (i : Fin k), (g∘castSucc) i ≤ 1
                //   := fun (i : Fin k) => h (Fin.castSucc k i)
                let h_cast = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let fin_k = c.fin_of(&k);
                    let (i_id, i) = e.fresh_local(fin_k.clone());
                    let cast_i = Expr::apps(c.fin_cast_succ.clone(), [k.clone(), i]);
                    let body = Expr::app(h.clone(), cast_i);
                    e.finish_child(e.mk_lam(i_id, BinderInfo::Default, fin_k, body))
                };
                // ih_app : Fin.sumNat k (g∘castSucc) ≤ k := ih (g∘castSucc) (h∘castSucc)
                let ih_app = Expr::apps(ih.clone(), [g_cast.clone(), h_cast]);
                // last_k : Fin (k+1) := Fin.last k
                let last_k = Expr::app(c.fin_last.clone(), k.clone());
                // h_last : g (last k) ≤ 1 := h (Fin.last k)
                let h_last = Expr::app(h.clone(), last_k.clone());

                let sum_k_cast = c.sum_nat(k.clone(), g_cast.clone());
                let g_last = Expr::app(g.clone(), last_k);
                // Nat.add_le_add (sum_k_cast) k (g_last) 1 ih_app h_last
                //   : Nat.le (Nat.add sum_k_cast g_last) (Nat.add k 1)
                //   ≡ Nat.le (Fin.sumNat (k+1) g) (Nat.succ k)   (both sides def-eq)
                let body = Expr::apps(
                    c.nat_add_le_add.clone(),
                    [
                        sum_k_cast,
                        k.clone(),
                        g_last,
                        c.nat_one.clone(),
                        ih_app,
                        h_last,
                    ],
                );
                let _ = c.nat_add.clone();
                let e = d.mk_lam(h_id, BinderInfo::Default, h_ty, body);
                let e = d.mk_lam(g_id, BinderInfo::Default, g_ty, e);
                let e = d.mk_lam(ih_id, BinderInfo::Default, ih_ty, e);
                d.finish_child(d.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e))
            };

            // @Nat.rec.{1} motive base step
            let body = Expr::apps(c.nat_rec1.clone(), [motive, base, step]);
            b.finish(body)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }
}

#[cfg(any(test, feature = "math-overlays"))]
impl Environment {
    /// Register `BoolAnalysis.indNat_le_one :
    ///   ∀ (b : Bool), Nat.le (@Bool.rec (fun _ => Nat) Nat.zero (Nat.succ Nat.zero) b) (Nat.succ Nat.zero)`
    /// as a kernel-checked, constructive theorem. Idempotent.
    ///
    /// The `{0,1}` indicator `indNat b` is bounded by `1`: a `Bool.rec` case
    /// split — `false ↦ 0 ≤ 1` (`Nat.zero_le 1`), `true ↦ 1 ≤ 1` (`Nat.le_refl 1`).
    /// This is exactly the per-coordinate bound feeding `Fin.sumNat_le_card` for
    /// the popcount `|hcDecode n j| ≤ n`.
    pub(crate) fn register_ind_nat_le_one(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.indNat_le_one");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_nat()?;
        self.init_bool()?;
        self.init_le()?;
        self.register_nat_arith_order_proofs()?; // Nat.le_refl
        self.register_nat_ble_le_lemmas()?; // Nat.zero_le

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_one = Expr::app(nat_succ.clone(), nat_zero.clone());
        let nat_le = Expr::const_(Name::from_string("Nat.le"), vec![]);
        let nat_le_refl = Expr::const_(Name::from_string("Nat.le_refl"), vec![]);
        let nat_zero_le = Expr::const_(Name::from_string("Nat.zero_le"), vec![]);
        let bool_rec = Expr::const_(
            Name::from_string("Bool.rec"),
            vec![Level::succ(Level::zero())],
        );
        // `fun (_ : Bool) => Nat` — the Nat motive for indNat.
        let nat_motive = || Expr::lam(BinderInfo::Default, bool_c.clone(), nat.clone());
        // indNat b = @Bool.rec (fun _ => Nat) 0 1 b
        let ind_nat = |b: Expr| {
            Expr::apps(
                bool_rec.clone(),
                [nat_motive(), nat_zero.clone(), nat_one.clone(), b],
            )
        };
        let le = |a: Expr, b: Expr| Expr::apps(nat_le.clone(), [a, b]);

        // Type: ∀ (b : Bool), Nat.le (indNat b) 1
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (bv_id, bv) = b.fresh_local(bool_c.clone());
            let concl = le(ind_nat(bv.clone()), nat_one.clone());
            b.finish(b.mk_pi(bv_id, BinderInfo::Default, bool_c.clone(), concl))
        };

        // value: fun (b : Bool) =>
        //   @Bool.rec.{0} (fun bb => Nat.le (indNat bb) 1) (Nat.zero_le 1) (Nat.le_refl 1) b
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (bv_id, bv) = b.fresh_local(bool_c.clone());

            // motive : fun (bb : Bool) => Nat.le (indNat bb) 1
            let motive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (bb_id, bb) = d.fresh_local(bool_c.clone());
                let body = le(ind_nat(bb.clone()), nat_one.clone());
                d.finish_child(d.mk_lam(bb_id, BinderInfo::Default, bool_c.clone(), body))
            };
            // false-case : Nat.le 0 1 := Nat.zero_le 1  (indNat false ≡ 0)
            let false_case = Expr::app(nat_zero_le.clone(), nat_one.clone());
            // true-case : Nat.le 1 1 := Nat.le_refl 1  (indNat true ≡ 1)
            let true_case = Expr::app(nat_le_refl.clone(), nat_one.clone());
            // @Bool.rec.{0} motive false_case true_case b
            let bool_rec0 = Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);
            let body = Expr::apps(bool_rec0, [motive, false_case, true_case, bv.clone()]);
            b.finish(b.mk_lam(bv_id, BinderInfo::Default, bool_c.clone(), body))
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_,
            value,
        })
    }
}

/// Shared constants for the `fourier_weight_parseval` assembly.
#[cfg(any(test, feature = "math-overlays"))]
struct WeightConsts {
    nat: Expr,
    rat: Expr,
    fin: Expr,
    bool_c: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_pow: Expr,
    nat_beq: Expr,
    fin_val: Expr,
    fin_sum: Expr,
    fin_sum_nat: Expr,
    fin_sum_swap: Expr,
    fin_sum_congr: Expr,
    hc_decode: Expr,
    fourier_coeff: Expr,
    ind: Expr,
    ind_nat_le_one: Expr,
    sum_nat_le_card: Expr,
    level_collapse: Expr,
    bool_rec: Expr,
    rat_mul: Expr,
    eq_trans1: Expr,
}

#[cfg(any(test, feature = "math-overlays"))]
impl WeightConsts {
    fn new() -> Self {
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        Self {
            nat: nat.clone(),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            bool_c: Expr::const_(Name::from_string("Bool"), vec![]),
            nat_zero,
            nat_succ,
            nat_pow: Expr::const_(Name::from_string("Nat.pow"), vec![]),
            nat_beq: Expr::const_(Name::from_string("Nat.beq"), vec![]),
            fin_val: Expr::const_(Name::from_string("Fin.val"), vec![]),
            fin_sum: Expr::const_(Name::from_string("Fin.sum"), vec![]),
            fin_sum_nat: Expr::const_(Name::from_string("Fin.sumNat"), vec![]),
            fin_sum_swap: Expr::const_(Name::from_string("Fin.sum_swap"), vec![]),
            fin_sum_congr: Expr::const_(Name::from_string("Fin.sum_congr"), vec![]),
            hc_decode: Expr::const_(Name::from_string("BoolAnalysis.hcDecode"), vec![]),
            fourier_coeff: Expr::const_(
                Name::from_string("BoolAnalysis.FourierCoefficient"),
                vec![],
            ),
            ind: Expr::const_(Name::from_string("BoolAnalysis.ind"), vec![]),
            ind_nat_le_one: Expr::const_(Name::from_string("BoolAnalysis.indNat_le_one"), vec![]),
            sum_nat_le_card: Expr::const_(Name::from_string("Fin.sumNat_le_card"), vec![]),
            level_collapse: Expr::const_(
                Name::from_string("BoolAnalysis.fourier_level_collapse"),
                vec![],
            ),
            bool_rec: Expr::const_(
                Name::from_string("Bool.rec"),
                vec![Level::succ(Level::zero())],
            ),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            eq_trans1: Expr::const_(
                Name::from_string("Eq.trans"),
                vec![Level::succ(Level::zero())],
            ),
        }
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn succ(&self, x: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), x)
    }
    /// `Nat.pow 2 n`.
    fn pow2(&self, n: &Expr) -> Expr {
        let two = self.succ(self.succ(self.nat_zero.clone()));
        Expr::apps(self.nat_pow.clone(), [two, n.clone()])
    }
    /// `@Fin.val n k`.
    fn val(&self, n: &Expr, k: &Expr) -> Expr {
        Expr::apps(self.fin_val.clone(), [n.clone(), k.clone()])
    }
    /// `hcDecode n j`.
    fn decode(&self, n: &Expr, j: &Expr) -> Expr {
        Expr::apps(self.hc_decode.clone(), [n.clone(), j.clone()])
    }
    /// `FourierCoefficient n f (hcDecode n j)` — the coefficient `c j`.
    fn coeff(&self, n: &Expr, f: &Expr, j: &Expr) -> Expr {
        Expr::apps(
            self.fourier_coeff.clone(),
            [n.clone(), f.clone(), self.decode(n, j)],
        )
    }
    /// `Rat.mul (c j) (c j)` — the squared coefficient `c j²`.
    fn coeff_sq(&self, n: &Expr, f: &Expr, j: &Expr) -> Expr {
        let cj = self.coeff(n, f, j);
        Expr::apps(self.rat_mul.clone(), [cj.clone(), cj])
    }
    /// `indNat ((hcDecode n j) i) = @Bool.rec (fun _=>Nat) 0 1 (S i)`.
    fn ind_nat(&self, n: &Expr, j: &Expr, i: &Expr) -> Expr {
        let nat_one = self.succ(self.nat_zero.clone());
        let nat_motive = Expr::lam(BinderInfo::Default, self.bool_c.clone(), self.nat.clone());
        let s_i = Expr::app(self.decode(n, j), i.clone());
        Expr::apps(
            self.bool_rec.clone(),
            [nat_motive, self.nat_zero.clone(), nat_one, s_i],
        )
    }
    /// `fun (i : Fin n) => indNat ((hcDecode n j) i)` — the popcount summand fn.
    fn popcount_fn(&self, parent: &EnvDeclBuilder, n: &Expr, j: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let body = self.ind_nat(n, j, &i);
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }
    /// `Fin.sumNat n (popcount_fn n j)` — the popcount `pc j = |hcDecode n j|`.
    fn popcount(&self, parent: &EnvDeclBuilder, n: &Expr, j: &Expr) -> Expr {
        Expr::apps(
            self.fin_sum_nat.clone(),
            [n.clone(), self.popcount_fn(parent, n, j)],
        )
    }
    /// `F k j = Rat.mul (ind (Nat.beq (pc j) (Fin.val (n+1) k))) (c j²)` — the
    /// 2-arg integrand for `Fin.sum_swap`.
    fn integrand(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        f: &Expr,
        np1: &Expr,
        k: &Expr,
        j: &Expr,
    ) -> Expr {
        let pc = self.popcount(parent, n, j);
        let beq = Expr::apps(self.nat_beq.clone(), [pc, self.val(np1, k)]);
        let gate = Expr::app(self.ind.clone(), beq);
        Expr::apps(self.rat_mul.clone(), [gate, self.coeff_sq(n, f, j)])
    }
    fn trans_rat(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans1.clone(), [self.rat.clone(), a, b, cc, h1, h2])
    }
}

#[cfg(any(test, feature = "math-overlays"))]
impl Environment {
    /// Build the constructive proof term for `fourier_weight_parseval` at the
    /// abstract `(n, f)`. Returns the value whose type is (def-eq to)
    /// `fourier_weight_parseval_helper n f`.
    ///
    /// Assembly (`Eq.trans` of two legs):
    ///   * `swap := Fin.sum_swap (n+1) (2^n) F` exchanges the level/subset sums;
    ///   * the inner `k`-sum collapses pointwise by `fourier_level_collapse n
    ///     (pc j) (c j²)` (premise `pc j ≤ n` via `Fin.sumNat_le_card` +
    ///     `indNat_le_one`), folded over `j` by `Fin.sum_congr`.
    ///
    /// Both legs land at `Fin.sum (2^n) (fun j => c j²)`, def-eq to the RHS
    /// `subsetSum n (fun S => f̂(S)²)`.
    pub(crate) fn fourier_weight_parseval_value(&self) -> Expr {
        let c = WeightConsts::new();
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let bool_fn_n = {
            // BoolFn n = HCPoint n → Bool ; reuse the kernel's BoolFn carrier.
            let bool_fn = Expr::const_(Name::from_string("BoolAnalysis.BoolFn"), vec![]);
            Expr::app(bool_fn, n.clone())
        };
        let (f_id, f) = b.fresh_local(bool_fn_n.clone());
        let np1 = c.succ(n.clone());
        let pow = c.pow2(&n);

        // F : Fin (n+1) → Fin (2^n) → Rat
        let big_f = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let fin_np1 = c.fin_of(&np1);
            let (k_id, k) = d.fresh_local(fin_np1.clone());
            let inner = {
                let mut e = EnvDeclBuilder::child_of(&d);
                let fin_pow = c.fin_of(&pow);
                let (j_id, j) = e.fresh_local(fin_pow.clone());
                let body = c.integrand(&e, &n, &f, &np1, &k, &j);
                e.finish_child(e.mk_lam(j_id, BinderInfo::Default, fin_pow, body))
            };
            d.finish_child(d.mk_lam(k_id, BinderInfo::Default, fin_np1, inner))
        };

        // swap : Fin.sum (n+1) (fun k => Fin.sum (2^n) (fun j => F k j))
        //      = Fin.sum (2^n) (fun j => Fin.sum (n+1) (fun k => F k j))
        let swap = Expr::apps(
            c.fin_sum_swap.clone(),
            [np1.clone(), pow.clone(), big_f.clone()],
        );

        // pointwise congr proof over j : Fin (2^n):
        //   fun (j : Fin (2^n)) =>
        //     fourier_level_collapse n (pc j) (c j²) (h_le j)
        // h_le j := Fin.sumNat_le_card n (popcount_fn n j) (fun i => indNat_le_one (S i))
        let mid_fn = {
            // mid_fn : fun j => Fin.sum (n+1) (fun k => F k j)
            let mut d = EnvDeclBuilder::child_of(&b);
            let fin_pow = c.fin_of(&pow);
            let (j_id, j) = d.fresh_local(fin_pow.clone());
            let inner = {
                let mut e = EnvDeclBuilder::child_of(&d);
                let fin_np1 = c.fin_of(&np1);
                let (k_id, k) = e.fresh_local(fin_np1.clone());
                let body = c.integrand(&e, &n, &f, &np1, &k, &j);
                e.finish_child(e.mk_lam(k_id, BinderInfo::Default, fin_np1, body))
            };
            let body = Expr::apps(c.fin_sum.clone(), [np1.clone(), inner]);
            d.finish_child(d.mk_lam(j_id, BinderInfo::Default, fin_pow, body))
        };
        let csq_fn = {
            // csq_fn : fun j => c j²
            let mut d = EnvDeclBuilder::child_of(&b);
            let fin_pow = c.fin_of(&pow);
            let (j_id, j) = d.fresh_local(fin_pow.clone());
            let body = c.coeff_sq(&n, &f, &j);
            d.finish_child(d.mk_lam(j_id, BinderInfo::Default, fin_pow, body))
        };
        let pointwise = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let fin_pow = c.fin_of(&pow);
            let (j_id, j) = d.fresh_local(fin_pow.clone());
            // h_each : ∀ i, indNat (S i) ≤ 1 := fun i => indNat_le_one (S i)
            let h_each = {
                let mut e = EnvDeclBuilder::child_of(&d);
                let fin_n = c.fin_of(&n);
                let (i_id, i) = e.fresh_local(fin_n.clone());
                let s_i = Expr::app(c.decode(&n, &j), i.clone());
                let body = Expr::app(c.ind_nat_le_one.clone(), s_i);
                e.finish_child(e.mk_lam(i_id, BinderInfo::Default, fin_n, body))
            };
            // h_le : pc j ≤ n := Fin.sumNat_le_card n (popcount_fn n j) h_each
            let pc_fn = c.popcount_fn(&d, &n, &j);
            let h_le = Expr::apps(c.sum_nat_le_card.clone(), [n.clone(), pc_fn, h_each]);
            let pc = c.popcount(&d, &n, &j);
            let csq = c.coeff_sq(&n, &f, &j);
            // fourier_level_collapse n (pc j) (c j²) h_le
            let body = Expr::apps(c.level_collapse.clone(), [n.clone(), pc, csq, h_le]);
            d.finish_child(d.mk_lam(j_id, BinderInfo::Default, fin_pow, body))
        };
        // congr_leg : Fin.sum (2^n) mid_fn = Fin.sum (2^n) csq_fn
        //   := Fin.sum_congr (2^n) mid_fn csq_fn pointwise
        let congr_leg = Expr::apps(
            c.fin_sum_congr.clone(),
            [pow.clone(), mid_fn.clone(), csq_fn.clone(), pointwise],
        );

        // The two endpoints, written so the kernel sees the def-eq chain.
        let lhs = Expr::apps(
            c.fin_sum.clone(),
            [np1.clone(), {
                // fun k => Fin.sum (2^n) (fun j => F k j) ≡ FourierWeightAtLevel n f (val k)
                let mut d = EnvDeclBuilder::child_of(&b);
                let fin_np1 = c.fin_of(&np1);
                let (k_id, k) = d.fresh_local(fin_np1.clone());
                let inner = {
                    let mut e = EnvDeclBuilder::child_of(&d);
                    let fin_pow = c.fin_of(&pow);
                    let (j_id, j) = e.fresh_local(fin_pow.clone());
                    let body = c.integrand(&e, &n, &f, &np1, &k, &j);
                    e.finish_child(e.mk_lam(j_id, BinderInfo::Default, fin_pow, body))
                };
                let body = Expr::apps(c.fin_sum.clone(), [pow.clone(), inner]);
                d.finish_child(d.mk_lam(k_id, BinderInfo::Default, fin_np1, body))
            }],
        );
        let mid = Expr::apps(c.fin_sum.clone(), [pow.clone(), mid_fn]);
        let rhs = Expr::apps(c.fin_sum.clone(), [pow.clone(), csq_fn]);

        // proof : lhs = rhs  := Eq.trans swap congr_leg
        //   lhs ≡ Fin.sum (n+1) (fun k => FourierWeightAtLevel n f (val k))   (δ FWAL)
        //   rhs ≡ subsetSum n (fun S => f̂(S)²)                                (δ subsetSum)
        let proof = c.trans_rat(lhs, mid, rhs, swap, congr_leg);

        let e = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n, proof);
        let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
        b.finish(e)
    }

    /// Register the prerequisite lemmas the `fourier_weight_parseval` proof term
    /// references, so its transitive axiom closure stays empty. Idempotent.
    pub(crate) fn register_fourier_weight_parseval_support(&mut self) -> Result<(), EnvError> {
        self.register_nat_eq_of_beq_eq_true()?;
        self.register_ind_nat_le_one()?;
        self.register_fin_sum_nat_le_card()?;
        self.register_fourier_level_collapse()?;
        self.register_fin_sum_swap_theorem()?;
        // Fin.sum_congr is provided by init_fin_sum (pulled in via the support
        // lemmas above), no extra registrar needed.
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    #[test]
    fn test_nat_eq_of_beq_eq_true_is_constructive() {
        let mut env = Environment::new();
        env.register_nat_eq_of_beq_eq_true()
            .expect("first registration");
        env.register_nat_eq_of_beq_eq_true().expect("idempotent");
        let name = Name::from_string("Nat.eq_of_beq_eq_true");
        let info = env.get_const(&name).expect("registered");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&info.value.clone().expect("proof"), &info.type_)
            .expect("Nat.eq_of_beq_eq_true must type-check");
        assert!(
            env.axiom_deps(&name).expect("deps").is_empty(),
            "Nat.eq_of_beq_eq_true must be axiom-free"
        );
        assert_eq!(
            env.proof_quality(&name).expect("quality"),
            ProofQuality::Constructive,
        );
    }

    #[test]
    fn test_ind_nat_le_one_is_constructive() {
        let mut env = Environment::new();
        env.register_ind_nat_le_one().expect("first registration");
        env.register_ind_nat_le_one().expect("idempotent");
        let name = Name::from_string("BoolAnalysis.indNat_le_one");
        let info = env.get_const(&name).expect("registered");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&info.value.clone().expect("proof"), &info.type_)
            .expect("indNat_le_one must type-check");
        assert!(
            env.axiom_deps(&name).expect("deps").is_empty(),
            "indNat_le_one must be axiom-free, got {:?}",
            env.axiom_deps(&name)
        );
        assert_eq!(
            env.proof_quality(&name).expect("quality"),
            ProofQuality::Constructive,
        );
    }

    #[test]
    fn test_fin_sum_nat_le_card_is_constructive() {
        let mut env = Environment::new();
        env.register_fin_sum_nat_le_card()
            .expect("first registration");
        env.register_fin_sum_nat_le_card().expect("idempotent");
        let name = Name::from_string("Fin.sumNat_le_card");
        let info = env.get_const(&name).expect("registered");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&info.value.clone().expect("proof"), &info.type_)
            .expect("Fin.sumNat_le_card must type-check");
        assert!(
            env.axiom_deps(&name).expect("deps").is_empty(),
            "Fin.sumNat_le_card must be axiom-free, got {:?}",
            env.axiom_deps(&name)
        );
        assert_eq!(
            env.proof_quality(&name).expect("quality"),
            ProofQuality::Constructive,
        );
    }

    #[test]
    fn test_fourier_level_collapse_is_constructive() {
        let mut env = Environment::new();
        env.register_fourier_level_collapse()
            .expect("first registration");
        env.register_fourier_level_collapse().expect("idempotent");
        let name = Name::from_string("BoolAnalysis.fourier_level_collapse");
        let info = env.get_const(&name).expect("registered");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&info.value.clone().expect("proof"), &info.type_)
            .expect("fourier_level_collapse must type-check");
        assert!(
            env.axiom_deps(&name).expect("deps").is_empty(),
            "fourier_level_collapse must be axiom-free, got {:?}",
            env.axiom_deps(&name)
        );
        assert_eq!(
            env.proof_quality(&name).expect("quality"),
            ProofQuality::Constructive,
        );
    }

    #[test]
    fn test_fourier_weight_parseval_is_checked_constructive_theorem() {
        use crate::env::types::ConstantKind;
        let mut env = Environment::new();
        env.init_fourier_boolean().expect("init fourier boolean");
        let name = Name::from_string("BoolAnalysis.fourier_weight_parseval");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "fourier_weight_parseval must be a CHECKED Theorem, not an axiom"
        );
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&info.value.clone().expect("proof"), &info.type_)
            .expect("fourier_weight_parseval proof must check against its type");
        assert!(
            env.axiom_deps(&name).expect("deps").is_empty(),
            "fourier_weight_parseval must be axiom-free, got {:?}",
            env.axiom_deps(&name)
        );
        assert_eq!(
            env.proof_quality(&name).expect("quality"),
            ProofQuality::Constructive,
            "fourier_weight_parseval must be Constructive"
        );
        // The helper must remain a reducible Definition.
        let hname = Name::from_string("BoolAnalysis.fourier_weight_parseval_helper");
        assert_eq!(
            env.get_const(&hname).expect("helper").kind,
            ConstantKind::Definition,
        );
    }
}

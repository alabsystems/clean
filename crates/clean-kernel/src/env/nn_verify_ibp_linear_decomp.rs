// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! W+/W- decomposition definitions and properties for IBP linear soundness.
//!
//! Extracted from `nn_verify_ibp_linear` for file-size compliance (#307).
//!
//! ## Definitions
//!
//! - `NNVerify.w_pos` — W+ = max(W, 0) element-wise (positive part)
//! - `NNVerify.w_neg` — W- = min(W, 0) element-wise (negative part)
//!
//! ## Opaque (sorry-inhabited — mathematically sound properties)
//!
//! - `NNVerify.w_decompose` — W[i,j] = W+[i,j] + W-[i,j]
//! - `NNVerify.w_pos_nonneg` — W+[i,j] >= 0
//! - `NNVerify.w_neg_nonpos` — W-[i,j] <= 0
//!
//! Part of #3244, #3366.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Constants for W+/W- decomposition registration.
pub(super) struct DecompConsts {
    pub(super) nat: Expr,
    pub(super) rat: Expr,
    pub(super) fin: Expr,
    pub(super) nn_mat: Expr,
    pub(super) rat_zero: Expr,
    pub(super) rat_max: Expr,
    pub(super) rat_min: Expr,
    pub(super) rat_add: Expr,
    pub(super) le_le: Expr,
    pub(super) inst_le_rat: Expr,
    pub(super) eq: Expr,
    pub(super) w_pos: Expr,
    pub(super) w_neg: Expr,
    // Bool + Bool.rec machinery for the `w_decompose` case split.
    pub(super) bool_t: Expr,
    pub(super) bool_true: Expr,
    pub(super) bool_false: Expr,
    /// `@Bool.rec.{1}` — Rat-valued case split (motive lands in `Sort 1`).
    pub(super) bool_rec_rat: Expr,
    /// `@Bool.rec.{0}` — Prop-valued case split (motive lands in `Sort 0`).
    pub(super) bool_rec_prop: Expr,
    pub(super) rat_ble: Expr,
    /// `@Eq.symm.{1}`.
    pub(super) eq_symm: Expr,
    /// `@Eq.refl.{1}`.
    pub(super) eq_refl: Expr,
    pub(super) rat_zero_add: Expr,
    pub(super) rat_add_zero: Expr,
}

impl DecompConsts {
    pub(super) fn new() -> Self {
        let t1 = Level::succ(Level::zero());
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            nn_mat: Expr::const_(Name::from_string("NNVerify.NNMat"), vec![]),
            rat_zero: Expr::const_(Name::from_string("Rat.zero"), vec![]),
            rat_max: Expr::const_(Name::from_string("Rat.max"), vec![]),
            rat_min: Expr::const_(Name::from_string("Rat.min"), vec![]),
            rat_add: Expr::const_(Name::from_string("Rat.add"), vec![]),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_rat: Expr::const_(Name::from_string("instLERat"), vec![]),
            eq: Expr::const_(Name::from_string("Eq"), vec![t1.clone()]),
            w_pos: Expr::const_(Name::from_string("NNVerify.w_pos"), vec![]),
            w_neg: Expr::const_(Name::from_string("NNVerify.w_neg"), vec![]),
            bool_t: Expr::const_(Name::from_string("Bool"), vec![]),
            bool_true: Expr::const_(Name::from_string("Bool.true"), vec![]),
            bool_false: Expr::const_(Name::from_string("Bool.false"), vec![]),
            bool_rec_rat: Expr::const_(Name::from_string("Bool.rec"), vec![t1.clone()]),
            bool_rec_prop: Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
            rat_ble: Expr::const_(Name::from_string("Rat.ble"), vec![]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![t1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![t1]),
            rat_zero_add: Expr::const_(Name::from_string("Rat.zero_add"), vec![]),
            rat_add_zero: Expr::const_(Name::from_string("Rat.add_zero"), vec![]),
        }
    }

    fn mat_of(&self, m: Expr, n: Expr) -> Expr {
        Expr::app(Expr::app(self.nn_mat.clone(), m), n)
    }

    fn rat_le(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(self.le_le.clone(), self.rat.clone()),
                    self.inst_le_rat.clone(),
                ),
                lhs,
            ),
            rhs,
        )
    }

    fn rat_eq(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::app(self.eq.clone(), self.rat.clone()), lhs),
            rhs,
        )
    }

    fn w_pos_app(&self, m: &Expr, n: &Expr, w: &Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::app(self.w_pos.clone(), m.clone()), n.clone()),
            w.clone(),
        )
    }

    fn w_neg_app(&self, m: &Expr, n: &Expr, w: &Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::app(self.w_neg.clone(), m.clone()), n.clone()),
            w.clone(),
        )
    }

    fn rat_add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }

    /// `Rat.ble a b : Bool`.
    fn rat_ble_app(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_ble.clone(), [a, b])
    }

    /// `@Eq.refl.{1} Rat v`.
    fn refl_rat(&self, v: Expr) -> Expr {
        Expr::apps(self.eq_refl.clone(), [self.rat.clone(), v])
    }

    /// `@Eq.symm.{1} Rat x y h`.
    fn symm_rat(&self, x: Expr, y: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.rat.clone(), x, y, h])
    }

    /// `@Eq.{2} Bool x y` — the `Bool`-valued discriminant equation type.
    fn eq_bool(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [self.bool_t.clone(), x, y],
        )
    }

    /// `@Eq.refl.{2} Bool v`.
    fn refl_bool(&self, v: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [self.bool_t.clone(), v],
        )
    }

    /// `@Bool.rec.{1} (fun _ => Rat) f t scrut` — the Rat-valued case split that
    /// `Rat.max` / `Rat.min` δ-reduce to (`f` on `false`, `t` on `true`).
    fn bool_rec_rat_app(&self, parent: &EnvDeclBuilder, f: Expr, t: Expr, scrut: Expr) -> Expr {
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(parent);
            let (x_id, _x) = mb.fresh_local(self.bool_t.clone());
            let lam = mb.mk_lam(
                x_id,
                BinderInfo::Default,
                self.bool_t.clone(),
                self.rat.clone(),
            );
            mb.finish_child(lam)
        };
        Expr::apps(self.bool_rec_rat.clone(), [motive, f, t, scrut])
    }
}

impl Environment {
    /// Register W+/W- decomposition definitions and properties.
    ///
    /// Called by `init_nn_verify_ibp_linear`. Depends on `init_rat_minmax`.
    pub(crate) fn register_w_decomp(&mut self) -> Result<(), EnvError> {
        // `register_w_decompose` proves `W = max(0,W) + min(0,W)` constructively
        // by a `Bool.rec` split on `Rat.ble Rat.zero (W i j)`, discharging each
        // branch with `Rat.add_zero` / `Rat.zero_add`. Register those
        // dependencies up front (idempotent / guarded).
        self.register_rat_minmax_proofs()?; // Rat.ble, Rat.min, Rat.max defs
        self.register_rat_zero_add_proof()?; // Rat.zero_add
        self.register_rat_add_zero_proof()?; // Rat.add_zero
        let c = DecompConsts::new();
        self.register_w_pos(&c)?;
        self.register_w_neg(&c)?;
        self.register_w_decompose(&c)?;
        self.register_w_pos_nonneg(&c)?;
        self.register_w_neg_nonpos(&c)
    }

    /// `NNVerify.w_pos (m n : Nat) (W : NNMat m n) : NNMat m n`
    /// := `fun i j => Rat.max Rat.zero (W i j)`
    fn register_w_pos(&mut self, c: &DecompConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.w_pos"))
            .is_some()
        {
            return Ok(());
        }
        let w_pos_type = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let mat_mn = c.mat_of(m.clone(), n.clone());
            let (_w_id, _w) = b.fresh_local(mat_mn.clone());
            let result = c.mat_of(m.clone(), n.clone());
            let e = b.mk_pi(_w_id, BinderInfo::Default, mat_mn, result);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        let w_pos_value = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let mat_mn = c.mat_of(m.clone(), n.clone());
            let (w_id, w) = b.fresh_local(mat_mn.clone());
            let fin_m = Expr::app(c.fin.clone(), m.clone());
            let fin_n = Expr::app(c.fin.clone(), n.clone());
            let inner = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (i_id, i) = ch.fresh_local(fin_m.clone());
                let inner2 = {
                    let mut ch2 = EnvDeclBuilder::child_of(&ch);
                    let (j_id, j) = ch2.fresh_local(fin_n.clone());
                    let w_ij = Expr::app(Expr::app(w.clone(), i.clone()), j);
                    let body = Expr::app(Expr::app(c.rat_max.clone(), c.rat_zero.clone()), w_ij);
                    let r = ch2.mk_lam(j_id, BinderInfo::Default, fin_n.clone(), body);
                    ch2.finish_child(r)
                };
                let r = ch.mk_lam(i_id, BinderInfo::Default, fin_m.clone(), inner2);
                ch.finish_child(r)
            };
            let e = b.mk_lam(w_id, BinderInfo::Default, mat_mn, inner);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNVerify.w_pos"),
            level_params: vec![],
            type_: w_pos_type,
            value: w_pos_value,
            is_reducible: true,
        })
    }

    /// `NNVerify.w_neg (m n : Nat) (W : NNMat m n) : NNMat m n`
    /// := `fun i j => Rat.min Rat.zero (W i j)`
    fn register_w_neg(&mut self, c: &DecompConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.w_neg"))
            .is_some()
        {
            return Ok(());
        }
        let w_neg_type = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let mat_mn = c.mat_of(m.clone(), n.clone());
            let (_w_id, _w) = b.fresh_local(mat_mn.clone());
            let result = c.mat_of(m.clone(), n.clone());
            let e = b.mk_pi(_w_id, BinderInfo::Default, mat_mn, result);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        let w_neg_value = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let mat_mn = c.mat_of(m.clone(), n.clone());
            let (w_id, w) = b.fresh_local(mat_mn.clone());
            let fin_m = Expr::app(c.fin.clone(), m.clone());
            let fin_n = Expr::app(c.fin.clone(), n.clone());
            let inner = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let (i_id, i) = ch.fresh_local(fin_m.clone());
                let inner2 = {
                    let mut ch2 = EnvDeclBuilder::child_of(&ch);
                    let (j_id, j) = ch2.fresh_local(fin_n.clone());
                    let w_ij = Expr::app(Expr::app(w.clone(), i.clone()), j);
                    let body = Expr::app(Expr::app(c.rat_min.clone(), c.rat_zero.clone()), w_ij);
                    let r = ch2.mk_lam(j_id, BinderInfo::Default, fin_n.clone(), body);
                    ch2.finish_child(r)
                };
                let r = ch.mk_lam(i_id, BinderInfo::Default, fin_m.clone(), inner2);
                ch.finish_child(r)
            };
            let e = b.mk_lam(w_id, BinderInfo::Default, mat_mn, inner);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNVerify.w_neg"),
            level_params: vec![],
            type_: w_neg_type,
            value: w_neg_value,
            is_reducible: true,
        })
    }

    /// `NNVerify.w_decompose`: W[i,j] = W+[i,j] + W-[i,j].
    fn register_w_decompose(&mut self, c: &DecompConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.w_decompose"))
            .is_some()
        {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let mat_mn = c.mat_of(m.clone(), n.clone());
            let (w_id, w) = b.fresh_local(mat_mn.clone());
            let fin_m = Expr::app(c.fin.clone(), m.clone());
            let fin_n = Expr::app(c.fin.clone(), n.clone());
            let (i_id, i) = b.fresh_local(fin_m.clone());
            let (j_id, j) = b.fresh_local(fin_n.clone());
            let w_ij = Expr::app(Expr::app(w.clone(), i.clone()), j.clone());
            let wp = c.w_pos_app(&m, &n, &w);
            let wn = c.w_neg_app(&m, &n, &w);
            let wp_ij = Expr::app(Expr::app(wp, i.clone()), j.clone());
            let wn_ij = Expr::app(Expr::app(wn, i), j);
            let rhs = Expr::app(Expr::app(c.rat_add.clone(), wp_ij), wn_ij);
            let body = c.rat_eq(w_ij, rhs);
            let e = b.mk_pi(j_id, BinderInfo::Default, fin_n, body);
            let e = b.mk_pi(i_id, BinderInfo::Default, fin_m, e);
            let e = b.mk_pi(w_id, BinderInfo::Default, mat_mn, e);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        // CONSTRUCTIVE PROOF (TCB-shrink, soundness-certificate floor):
        // `w_decompose` states `W[i,j] = max(0, W[i,j]) + min(0, W[i,j])`, the
        // standard max/min decomposition identity over an ordered field. It is
        // now a genuine kernel-checked `Declaration::Theorem` (no `sorry`,
        // closure ⊆ FOUNDATIONAL ∪ the constructive `Rat.zero_add`/`Rat.add_zero`
        // Theorems). After β/δ-reduction the goal is
        //   `Eq Rat b (Rat.add (Rat.max Rat.zero b) (Rat.min Rat.zero b))`
        // with `b ≡ W i j`. Both `Rat.max Rat.zero b` and `Rat.min Rat.zero b`
        // δ-reduce to a `@Bool.rec` on the SAME discriminant `Rat.ble Rat.zero b`
        // (`max` is `Bool.rec 0 b ·`, `min` is `Bool.rec b 0 ·`). A dependent
        // `@Bool.rec.{0}` split on that discriminant (motive carrying the
        // `Eq Bool (ble 0 b) x → …` reflection, as in `Rat.min_def'`) gives:
        //   - false branch: `max ≡ 0`, `min ≡ b`; goal `b = 0 + b`, closed by
        //     `Eq.symm (Rat.zero_add b)`;
        //   - true  branch: `max ≡ b`, `min ≡ 0`; goal `b = b + 0`, closed by
        //     `Eq.symm (Rat.add_zero b)`.
        // applied to `Eq.refl Bool (Rat.ble Rat.zero b)`.
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let mat_mn = c.mat_of(m.clone(), n.clone());
            let (w_id, w) = b.fresh_local(mat_mn.clone());
            let fin_m = Expr::app(c.fin.clone(), m.clone());
            let fin_n = Expr::app(c.fin.clone(), n.clone());
            let (i_id, i) = b.fresh_local(fin_m.clone());
            let (j_id, j) = b.fresh_local(fin_n.clone());
            // b_ij ≡ W i j : Rat.
            let b_ij = Expr::app(Expr::app(w, i.clone()), j.clone());
            let zero = c.rat_zero.clone();
            // Discriminant `d := Rat.ble Rat.zero b_ij` — the shared `Bool.rec`
            // scrutinee that both `Rat.max Rat.zero b` and `Rat.min Rat.zero b`
            // unfold onto.
            let disc = c.rat_ble_app(zero.clone(), b_ij.clone());

            // Dependent motive on the discriminant `x : Bool`:
            //   fun (x : Bool) => Eq Bool d x →
            //     Eq Rat b (Rat.add (Bool.rec 0 b x) (Bool.rec b 0 x))
            let motive = {
                let mut mb = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = mb.fresh_local(c.bool_t.clone());
                let heq_ty = c.eq_bool(disc.clone(), x.clone());
                let (heq_id, _) = mb.fresh_local(heq_ty.clone());
                let max_x = c.bool_rec_rat_app(&mb, zero.clone(), b_ij.clone(), x.clone());
                let min_x = c.bool_rec_rat_app(&mb, b_ij.clone(), zero.clone(), x.clone());
                let rhs = c.rat_add(max_x, min_x);
                let body = c.rat_eq(b_ij.clone(), rhs);
                let body = mb.mk_pi(heq_id, BinderInfo::Default, heq_ty, body);
                let lam = mb.mk_lam(x_id, BinderInfo::Default, c.bool_t.clone(), body);
                mb.finish_child(lam)
            };

            // false branch: max ≡ 0, min ≡ b; goal `b = 0 + b`.
            let false_minor = {
                let mut fb = EnvDeclBuilder::child_of(&b);
                let heq_ty = c.eq_bool(disc.clone(), c.bool_false.clone());
                let (heq_id, _) = fb.fresh_local(heq_ty.clone());
                // Rat.zero_add b : Rat.add 0 b = b. Symm gives b = 0 + b.
                let zero_add = Expr::app(c.rat_zero_add.clone(), b_ij.clone());
                let proof = c.symm_rat(
                    c.rat_add(zero.clone(), b_ij.clone()),
                    b_ij.clone(),
                    zero_add,
                );
                let lam = fb.mk_lam(heq_id, BinderInfo::Default, heq_ty, proof);
                fb.finish_child(lam)
            };

            // true branch: max ≡ b, min ≡ 0; goal `b = b + 0`.
            let true_minor = {
                let mut tb = EnvDeclBuilder::child_of(&b);
                let heq_ty = c.eq_bool(disc.clone(), c.bool_true.clone());
                let (heq_id, _) = tb.fresh_local(heq_ty.clone());
                // Rat.add_zero b : Rat.add b 0 = b. Symm gives b = b + 0.
                let add_zero = Expr::app(c.rat_add_zero.clone(), b_ij.clone());
                let proof = c.symm_rat(
                    c.rat_add(b_ij.clone(), zero.clone()),
                    b_ij.clone(),
                    add_zero,
                );
                let lam = tb.mk_lam(heq_id, BinderInfo::Default, heq_ty, proof);
                tb.finish_child(lam)
            };

            let rec_app = Expr::apps(
                c.bool_rec_prop.clone(),
                [motive, false_minor, true_minor, disc.clone()],
            );
            let applied = Expr::app(rec_app, c.refl_bool(disc));

            let e = b.mk_lam(j_id, BinderInfo::Default, fin_n, applied);
            let e = b.mk_lam(i_id, BinderInfo::Default, fin_m, e);
            let e = b.mk_lam(w_id, BinderInfo::Default, mat_mn, e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.w_decompose"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNVerify.w_pos_nonneg`: 0 <= W+[i,j].
    fn register_w_pos_nonneg(&mut self, c: &DecompConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.w_pos_nonneg"))
            .is_some()
        {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let mat_mn = c.mat_of(m.clone(), n.clone());
            let (w_id, w) = b.fresh_local(mat_mn.clone());
            let fin_m = Expr::app(c.fin.clone(), m.clone());
            let fin_n = Expr::app(c.fin.clone(), n.clone());
            let (i_id, i) = b.fresh_local(fin_m.clone());
            let (j_id, j) = b.fresh_local(fin_n.clone());
            let wp = c.w_pos_app(&m, &n, &w);
            let wp_ij = Expr::app(Expr::app(wp, i), j);
            let body = c.rat_le(c.rat_zero.clone(), wp_ij);
            let e = b.mk_pi(j_id, BinderInfo::Default, fin_n, body);
            let e = b.mk_pi(i_id, BinderInfo::Default, fin_m, e);
            let e = b.mk_pi(w_id, BinderInfo::Default, mat_mn, e);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        // CONSTRUCTIVE PROOF (soundness-certificate capstone): `w_pos_nonneg`
        // is now a genuine sorry-free `Declaration::Theorem`. After β/δ
        // reduction `(w_pos m n W) i j ≡ Rat.max Rat.zero (W i j)`, so the goal
        // `0 ≤ (w_pos m n W) i j` is inhabited by
        // `Rat.le_max_left Rat.zero (W i j)`
        //   : LE.le Rat instLERat Rat.zero (Rat.max Rat.zero (W i j)).
        // Closure: `Rat.le_max_left` (foundational lattice axiom),
        // `Rat.max`/`Rat.zero` (foundational). Zero `sorry`.
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let mat_mn = c.mat_of(m.clone(), n.clone());
            let (w_id, w) = b.fresh_local(mat_mn.clone());
            let fin_m = Expr::app(c.fin.clone(), m.clone());
            let fin_n = Expr::app(c.fin.clone(), n.clone());
            let (i_id, i) = b.fresh_local(fin_m.clone());
            let (j_id, j) = b.fresh_local(fin_n.clone());
            let w_ij = Expr::app(Expr::app(w, i), j);
            // Rat.le_max_left Rat.zero (W i j).
            let proof = Expr::apps(
                Expr::const_(Name::from_string("Rat.le_max_left"), vec![]),
                [c.rat_zero.clone(), w_ij],
            );
            let e = b.mk_lam(j_id, BinderInfo::Default, fin_n, proof);
            let e = b.mk_lam(i_id, BinderInfo::Default, fin_m, e);
            let e = b.mk_lam(w_id, BinderInfo::Default, mat_mn, e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.w_pos_nonneg"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNVerify.w_neg_nonpos`: W-[i,j] <= 0.
    fn register_w_neg_nonpos(&mut self, c: &DecompConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.w_neg_nonpos"))
            .is_some()
        {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let mat_mn = c.mat_of(m.clone(), n.clone());
            let (w_id, w) = b.fresh_local(mat_mn.clone());
            let fin_m = Expr::app(c.fin.clone(), m.clone());
            let fin_n = Expr::app(c.fin.clone(), n.clone());
            let (i_id, i) = b.fresh_local(fin_m.clone());
            let (j_id, j) = b.fresh_local(fin_n.clone());
            let wn = c.w_neg_app(&m, &n, &w);
            let wn_ij = Expr::app(Expr::app(wn, i), j);
            let body = c.rat_le(wn_ij, c.rat_zero.clone());
            let e = b.mk_pi(j_id, BinderInfo::Default, fin_n, body);
            let e = b.mk_pi(i_id, BinderInfo::Default, fin_m, e);
            let e = b.mk_pi(w_id, BinderInfo::Default, mat_mn, e);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        // CONSTRUCTIVE PROOF (soundness-certificate capstone): `w_neg_nonpos`
        // is now a genuine sorry-free `Declaration::Theorem`. After β/δ
        // reduction `(w_neg m n W) i j ≡ Rat.min Rat.zero (W i j)`, so the goal
        // `(w_neg m n W) i j ≤ 0` is inhabited by
        // `Rat.min_le_left Rat.zero (W i j)`
        //   : LE.le Rat instLERat (Rat.min Rat.zero (W i j)) Rat.zero.
        // Closure: `Rat.min_le_left` (foundational lattice axiom),
        // `Rat.min`/`Rat.zero` (foundational). Zero `sorry`.
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(c.nat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let mat_mn = c.mat_of(m.clone(), n.clone());
            let (w_id, w) = b.fresh_local(mat_mn.clone());
            let fin_m = Expr::app(c.fin.clone(), m.clone());
            let fin_n = Expr::app(c.fin.clone(), n.clone());
            let (i_id, i) = b.fresh_local(fin_m.clone());
            let (j_id, j) = b.fresh_local(fin_n.clone());
            let w_ij = Expr::app(Expr::app(w, i), j);
            // Rat.min_le_left Rat.zero (W i j).
            let proof = Expr::apps(
                Expr::const_(Name::from_string("Rat.min_le_left"), vec![]),
                [c.rat_zero.clone(), w_ij],
            );
            let e = b.mk_lam(j_id, BinderInfo::Default, fin_n, proof);
            let e = b.mk_lam(i_id, BinderInfo::Default, fin_m, e);
            let e = b.mk_lam(w_id, BinderInfo::Default, mat_mn, e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.w_neg_nonpos"),
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

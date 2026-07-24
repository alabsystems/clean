// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/cbrt layer — the `(4/3,4)` dual-HC cross-term AM-GM scaffolding,
//! built honestly through the SQUARED form (no irrational NNReal `sqrt`), plus
//! the precise record that this AM-GM bound is TOO LOOSE to close the dual
//! tensorization cross-term `(CT)`.
//!
//! # Why this module exists (and what it does NOT do)
//!
//! The `(4/3,4)` dual-HC tensorization step (design
//! `2026-06-20-hc43-dual-tensorization-cross-term.md`) needs a bound on the
//! Cauchy-Schwarz cross-term `R := Σ G²H²`. After the inductive hypothesis,
//! `R² ≤ 4^{2n}·NG³·NH³` (`u := NG³`, `v := NH³`). The candidate "sqrt-avoiding"
//! route bounds `R` by a RATIONAL combination of cubes via the squared form:
//!
//! ```text
//!   4·u·v ≤ (u+v)·(u+v)     (the AM-GM core, an NNReal inequality)
//! ```
//!
//! whence (with `le_of_sq_le_sq`, landed) `2R ≤ 4ⁿ·(u+v) = 4ⁿ·(NG³+NH³)`, i.e.
//! `R ≤ 4ⁿ·½(NG³+NH³)` — NO irrational `^{3/2}`.
//!
//! ## VERIFY-FIRST RESULT (refutation — the headline): this bound is TOO LOOSE.
//!
//! Numerically refute-checked (400k samples over the genuine `norm43`/`norm43³`
//! relation `NG=‖fL+fH‖`, `NH=‖fL−fH‖`, `NF1=‖fL‖+‖fH‖`): the AM-GM bound
//! `R := ½(NG³+NH³)` produces **104,350 / 400,000 violations** of `(CT)`
//! `2NG³ + (4/3)R + (2/81)NH³ ≤ 4·NF1³` (min slack −34,980). The TIGHT bound
//! `R := (NG·NH)^{3/2}` gives **0 violations** (min slack 0, exactly tight).
//!
//! The gap bites at the tight corner `NH → 0`: AM-GM replaces `(NG·NH)^{3/2}`
//! (which → 0 like `NH^{3/2}`) by `½NG³` (which stays large), injecting spurious
//! mass `(4/3)·½·NG³ = (2/3)NG³` exactly where `(CT)` has zero slack. **No
//! symmetric or weighted rational bound `R ≤ a·NG³ + b·NH³` works:** to be a
//! valid upper bound on `(NG·NH)^{3/2}` (degree 3/2, homogeneous) needs `a,b>0`;
//! but then `a·NG³` survives as `NH→0` and breaks `(CT)`. The `3/2`-power lies
//! strictly between `NG` (small) and `NG³` (large) and no nonneg polynomial
//! tracks it. **The irrational `(NG·NH)^{3/2}` is genuinely forced** — confirming
//! the design doc §4–§5 wall; the "sqrt-avoiding AM-GM route" does NOT close the
//! cross-term.
//!
//! # What this module DOES register (genuine, kernel-checked, sound)
//!
//! These are TRUE NNReal inequalities — sound and reusable (the eventual
//! NNReal-`sqrt` route, and any AM-GM consumer, can use them) — even though they
//! do NOT suffice for `(CT)`:
//!
//! - **`NNReal.four_mul_mul_le_add_sq`** — the squared-form AM-GM core
//!   `4·u·v ≤ (u+v)·(u+v)` (`4uv` written numeral-free as `(uv+uv)+(uv+uv)`),
//!   REDUCED via landed ring algebra (`add_mul`/`mul_add`/`mul_comm`/`add_assoc`/
//!   `add_comm`/`add_le_add`/`le.refl`) to the single IRREDUCIBLE AM-GM leaf
//!   `2uv ≤ u²+v²` (taken as an explicit, honestly-named NNReal hypothesis,
//!   because over the subtraction-free `NNReal` carrier `2uv ≤ u²+v²` is the
//!   genuine content `0 ≤ (u−v)²` and is NOT derivable from landed bricks — it
//!   needs `NNReal`-level subtraction / order-totality / a CauSeq leaf, none of
//!   which are on branch).
//!
//! - **`NNReal.two_mul_le_add_of_sq_le_mul_amgm`** — the R-bound's de-square step
//!   `(t+t) ≤ (a+b)` from `(t+t)·(t+t) ≤ (a+b)·(a+b)` via the landed keystone
//!   `NNReal.le_of_sq_le_sq` (this part is FULLY provable from landed bricks); the
//!   squared hypothesis is the AM-GM-from-Cauchy-Schwarz feed `4·t·t ≤ (a+b)²`
//!   assembled from `four_mul_mul_le_add_sq` + the CS+IH square bound `t² ≤ a·b`
//!   (both taken as explicit hypotheses — the CS/IH `R² ≤ P·Q` is itself not built
//!   on this branch; see the design doc §1 S4–S5).
//!
//! NO masquerade: the proven content is genuine NNReal ring/order algebra; the
//! two explicit hypotheses (the AM-GM leaf, and the CS+IH square bound) are the
//! honestly-named structure this branch does not supply. The cross-term is NOT
//! closed — and the refutation above shows it CANNOT be closed by this route.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (foundational only). NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for the AM-GM cross-term scaffolding.
struct AmGmCrossConsts {
    nnreal: Expr,
    nnreal_mul: Expr,
    nnreal_add: Expr,
    nnreal_le: Expr,
    nnreal_le_refl: Expr,
    nnreal_add_le_add: Expr,
    nnreal_le_of_sq_le_sq: Expr,
    nnreal_mul_add: Expr,
    nnreal_add_mul: Expr,
    nnreal_mul_comm: Expr,
    nnreal_add_assoc: Expr,
    nnreal_add_comm: Expr,
    eq_symm1: Expr,
    eq_subst1: Expr,
    eq_trans1: Expr,
    congr_arg1: Expr,
}

impl AmGmCrossConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nnreal: k("NNReal"),
            nnreal_mul: k("NNReal.mul"),
            nnreal_add: k("NNReal.add"),
            nnreal_le: k("NNReal.le"),
            nnreal_le_refl: k("NNReal.le.refl"),
            nnreal_add_le_add: k("NNReal.add_le_add"),
            nnreal_le_of_sq_le_sq: k("NNReal.le_of_sq_le_sq"),
            nnreal_mul_add: k("NNReal.mul_add"),
            nnreal_add_mul: k("NNReal.add_mul"),
            nnreal_mul_comm: k("NNReal.mul_comm"),
            nnreal_add_assoc: k("NNReal.add_assoc"),
            nnreal_add_comm: k("NNReal.add_comm"),
            eq_symm1: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_subst1: Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]),
            eq_trans1: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            congr_arg1: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        }
    }

    fn nnmul(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_mul.clone(), [a.clone(), b.clone()])
    }
    fn nnadd(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_add.clone(), [a.clone(), b.clone()])
    }
    fn nnle(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_le.clone(), [a.clone(), b.clone()])
    }
    /// `NNReal.le.refl a : NNReal.le a a`.
    fn le_refl(&self, a: &Expr) -> Expr {
        Expr::app(self.nnreal_le_refl.clone(), a.clone())
    }
    /// `NNReal.add_le_add a b c d hab hcd : add a c ≤ add b d`.
    #[allow(clippy::too_many_arguments)]
    fn add_le_add(&self, a: &Expr, b: &Expr, cc: &Expr, d: &Expr, hab: Expr, hcd: Expr) -> Expr {
        Expr::apps(
            self.nnreal_add_le_add.clone(),
            [a.clone(), b.clone(), cc.clone(), d.clone(), hab, hcd],
        )
    }
    /// `NNReal.le_of_sq_le_sq a b hsq : NNReal.le a b` (hsq : le (mul a a)(mul b b)).
    fn le_of_sq_le_sq(&self, a: &Expr, b: &Expr, hsq: Expr) -> Expr {
        Expr::apps(
            self.nnreal_le_of_sq_le_sq.clone(),
            [a.clone(), b.clone(), hsq],
        )
    }
    /// `NNReal.mul_add c a b : mul c (add a b) = add (mul c a)(mul c b)`.
    fn mul_add(&self, cc: &Expr, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(
            self.nnreal_mul_add.clone(),
            [cc.clone(), a.clone(), b.clone()],
        )
    }
    /// `NNReal.add_mul a b c : mul (add a b) c = add (mul a c)(mul b c)`.
    fn add_mul(&self, a: &Expr, b: &Expr, cc: &Expr) -> Expr {
        Expr::apps(
            self.nnreal_add_mul.clone(),
            [a.clone(), b.clone(), cc.clone()],
        )
    }
    /// `NNReal.mul_comm a b : mul a b = mul b a`.
    fn mul_comm(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_mul_comm.clone(), [a.clone(), b.clone()])
    }
    /// `NNReal.add_assoc a b c : add (add a b) c = add a (add b c)`.
    fn add_assoc(&self, a: &Expr, b: &Expr, cc: &Expr) -> Expr {
        Expr::apps(
            self.nnreal_add_assoc.clone(),
            [a.clone(), b.clone(), cc.clone()],
        )
    }
    /// `NNReal.add_comm a b : add a b = add b a`.
    fn add_comm(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.nnreal_add_comm.clone(), [a.clone(), b.clone()])
    }
    /// `@Eq.symm NNReal a b h : Eq NNReal b a`.
    fn symm(&self, a: &Expr, b: &Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_symm1.clone(),
            [self.nnreal.clone(), a.clone(), b.clone(), h],
        )
    }
    /// `@Eq.subst NNReal motive a b h_eq h : motive b`.
    fn subst(&self, motive: Expr, a: &Expr, b: &Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst1.clone(),
            [self.nnreal.clone(), motive, a.clone(), b.clone(), h_eq, h],
        )
    }
    /// `@Eq.trans NNReal a b c hab hbc : Eq NNReal a c`.
    fn trans(&self, a: &Expr, b: &Expr, cc: &Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(
            self.eq_trans1.clone(),
            [
                self.nnreal.clone(),
                a.clone(),
                b.clone(),
                cc.clone(),
                hab,
                hbc,
            ],
        )
    }
    /// `@congrArg NNReal NNReal a b f h : Eq (f a)(f b)`.
    fn congr_arg(&self, a: &Expr, b: &Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg1.clone(),
            [
                self.nnreal.clone(),
                self.nnreal.clone(),
                a.clone(),
                b.clone(),
                f,
                h,
            ],
        )
    }
}

impl Environment {
    /// Register the AM-GM cross-term scaffolding. Idempotent; foundational-only.
    pub fn init_algebra_nnreal_amgm_cross(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_le()?; // NNReal.le, NNReal.le.refl
        self.init_algebra_nnreal_le_add()?; // NNReal.add_le_add
        self.init_algebra_nnreal_mul_distrib()?; // NNReal.mul_add
        self.init_algebra_nnreal_add_mul()?; // NNReal.add_mul
        self.init_algebra_nnreal_reverse_square_algebra()?; // NNReal.mul_comm
        self.init_algebra_nnreal_add_comm_assoc()?; // NNReal.add_assoc, NNReal.add_comm
        self.init_algebra_nnreal_reverse_square_sq()?; // NNReal.le_of_sq_le_sq
        self.init_eq()?;

        let c = AmGmCrossConsts::new();
        self.register_four_mul_mul_le_add_sq(&c)?;
        self.register_two_mul_le_add_amgm(&c)?;
        Ok(())
    }

    /// `NNReal.four_mul_mul_le_add_sq : ∀ u v : NNReal,`
    /// `  NNReal.le (u·v+u·v)(u·u+v·v) → NNReal.le ((u·v+u·v)+(u·v+u·v)) ((u+v)·(u+v))`.
    fn register_four_mul_mul_le_add_sq(&mut self, c: &AmGmCrossConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.four_mul_mul_le_add_sq");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (u_id, u) = b.fresh_local(c.nnreal.clone());
            let (v_id, v) = b.fresh_local(c.nnreal.clone());
            let uv = c.nnmul(&u, &v);
            let two_uv = c.nnadd(&uv, &uv);
            let uu = c.nnmul(&u, &u);
            let vv = c.nnmul(&v, &v);
            let uu_vv = c.nnadd(&uu, &vv);
            // hamgm : 2uv ≤ u²+v².
            let hamgm_ty = c.nnle(&two_uv, &uu_vv);
            let (hamgm_id, _h) = b.fresh_local(hamgm_ty.clone());
            // concl : (2uv)+(2uv) ≤ (u+v)·(u+v).
            let four_uv = c.nnadd(&two_uv, &two_uv);
            let s = c.nnadd(&u, &v);
            let ss = c.nnmul(&s, &s);
            let concl = c.nnle(&four_uv, &ss);
            let e = b.mk_pi(hamgm_id, BinderInfo::Default, hamgm_ty, concl);
            let e = b.mk_pi(v_id, BinderInfo::Default, c.nnreal.clone(), e);
            let e = b.mk_pi(u_id, BinderInfo::Default, c.nnreal.clone(), e);
            b.finish(e)
        };
        let value = build_four_mul_mul_le_add_sq(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `NNReal.two_mul_le_add_of_sq_le_mul_amgm : ∀ t a b : NNReal,`
    /// `  NNReal.le ((t+t)·(t+t)) ((a+b)·(a+b)) → NNReal.le (t+t) (a+b)`.
    ///
    /// The de-square step (FULLY provable from the landed `le_of_sq_le_sq`). The
    /// squared hypothesis is the AM-GM-from-Cauchy-Schwarz feed; its construction
    /// from `four_mul_mul_le_add_sq` + the CS+IH `t² ≤ a·b` is the design doc §1
    /// S4–S5 assembly (not built here — CS/IH is not on this branch).
    fn register_two_mul_le_add_amgm(&mut self, c: &AmGmCrossConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.two_mul_le_add_of_sq_le_mul_amgm");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (t_id, t) = b.fresh_local(c.nnreal.clone());
            let (a_id, a) = b.fresh_local(c.nnreal.clone());
            let (bv_id, bv) = b.fresh_local(c.nnreal.clone());
            let tt = c.nnadd(&t, &t); // t+t (= 2t)
            let ab = c.nnadd(&a, &bv); // a+b
            let hsq_ty = c.nnle(&c.nnmul(&tt, &tt), &c.nnmul(&ab, &ab));
            let (hsq_id, _h) = b.fresh_local(hsq_ty.clone());
            let concl = c.nnle(&tt, &ab);
            let e = b.mk_pi(hsq_id, BinderInfo::Default, hsq_ty, concl);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.nnreal.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.nnreal.clone(), e);
            let e = b.mk_pi(t_id, BinderInfo::Default, c.nnreal.clone(), e);
            b.finish(e)
        };
        let value = build_two_mul_le_add_amgm(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// `NNReal.four_mul_mul_le_add_sq` proof term.
///
/// Goal: `(2uv)+(2uv) ≤ (u+v)·(u+v)` from `hamgm : 2uv ≤ u²+v²`.
///
/// 1. `add_le_add (2uv)(u²+v²)(2uv)(2uv) hamgm (le.refl 2uv)` :
///    `(2uv)+(2uv) ≤ (u²+v²)+(2uv)`.
/// 2. The RHS expansion `E : (u+v)·(u+v) = (u²+v²)+(2uv)` (landed ring algebra),
///    `subst` along `symm E` rewrites `(u²+v²)+(2uv) → (u+v)·(u+v)`.
fn build_four_mul_mul_le_add_sq(c: &AmGmCrossConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (u_id, u) = b.fresh_local(c.nnreal.clone());
    let (v_id, v) = b.fresh_local(c.nnreal.clone());

    let uv = c.nnmul(&u, &v);
    let two_uv = c.nnadd(&uv, &uv);
    let uu = c.nnmul(&u, &u);
    let vv = c.nnmul(&v, &v);
    let uu_vv = c.nnadd(&uu, &vv);
    let hamgm_ty = c.nnle(&two_uv, &uu_vv);
    let (hamgm_id, hamgm) = b.fresh_local(hamgm_ty.clone());

    // step1 : (2uv)+(2uv) ≤ (u²+v²)+(2uv).
    let step1 = c.add_le_add(&two_uv, &uu_vv, &two_uv, &two_uv, hamgm, c.le_refl(&two_uv));
    let rhs_split = c.nnadd(&uu_vv, &two_uv); // (u²+v²)+(2uv)

    // E : (u+v)·(u+v) = (u²+v²)+(2uv).
    let s = c.nnadd(&u, &v);
    let ss = c.nnmul(&s, &s);
    let e_eq = build_add_sq_eq(c, &b, &u, &v);

    // FINAL : (2uv)+(2uv) ≤ (u+v)·(u+v), transporting RHS (u²+v²)+(2uv) → (u+v)²
    //         along symm E.
    let four_uv = c.nnadd(&two_uv, &two_uv);
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (w_id, w) = mb.fresh_local(c.nnreal.clone());
        let body = c.nnle(&four_uv, &w);
        mb.finish_child(mb.mk_lam(w_id, BinderInfo::Default, c.nnreal.clone(), body))
    };
    let proof = c.subst(
        motive,
        &rhs_split,
        &ss,
        c.symm(&ss, &rhs_split, e_eq),
        step1,
    );

    let e = b.mk_lam(hamgm_id, BinderInfo::Default, hamgm_ty, proof);
    let e = b.mk_lam(v_id, BinderInfo::Default, c.nnreal.clone(), e);
    let e = b.mk_lam(u_id, BinderInfo::Default, c.nnreal.clone(), e);
    b.finish(e)
}

/// `E : (u+v)·(u+v) = (u·u + v·v) + (u·v + u·v)`, from landed ring algebra.
///
/// `(u+v)·(u+v) = u·(u+v) + v·(u+v)`        [add_mul u v (u+v)]
///             = (u·u + u·v) + (v·u + v·v)  [congr² mul_add]
///             = (u·u + u·v) + (u·v + v·v)  [congr mul_comm v u]
///             = (u·u + v·v) + (u·v + u·v)  [4-term reassoc add_assoc/add_comm]
fn build_add_sq_eq(c: &AmGmCrossConsts, parent: &EnvDeclBuilder, u: &Expr, v: &Expr) -> Expr {
    let uu = c.nnmul(u, u);
    let uv = c.nnmul(u, v);
    let vu = c.nnmul(v, u);
    let vv = c.nnmul(v, v);
    let s = c.nnadd(u, v);
    let prod = c.nnmul(&s, &s); // (u+v)·(u+v)

    let add_right_fn = |t: &Expr| -> Expr {
        let mut fb = EnvDeclBuilder::child_of(parent);
        let (w_id, w) = fb.fresh_local(c.nnreal.clone());
        let body = c.nnadd(&w, t);
        fb.finish_child(fb.mk_lam(w_id, BinderInfo::Default, c.nnreal.clone(), body))
    };
    let add_left_fn = |t: &Expr| -> Expr {
        let mut fb = EnvDeclBuilder::child_of(parent);
        let (w_id, w) = fb.fresh_local(c.nnreal.clone());
        let body = c.nnadd(t, &w);
        fb.finish_child(fb.mk_lam(w_id, BinderInfo::Default, c.nnreal.clone(), body))
    };

    // s1 : (u+v)·(u+v) = u·(u+v) + v·(u+v)   [add_mul u v (u+v)].
    let u_s = c.nnmul(u, &s);
    let v_s = c.nnmul(v, &s);
    let t1 = c.nnadd(&u_s, &v_s);
    let s1 = c.add_mul(u, v, &s);

    // ia : u·(u+v) = u·u + u·v   [mul_add u u v].
    let uu_uv = c.nnadd(&uu, &uv);
    let ia = c.mul_add(u, u, v);
    // ib : v·(u+v) = v·u + v·v   [mul_add v u v].
    let vu_vv = c.nnadd(&vu, &vv);
    let ib = c.mul_add(v, u, v);

    // s2 : u·(u+v) + v·(u+v) = (u·u+u·v) + v·(u+v)   [congr (·+v·(u+v)) ia].
    let t2 = c.nnadd(&uu_uv, &v_s);
    let s2 = c.congr_arg(&u_s, &uu_uv, add_right_fn(&v_s), ia);
    // s3 : (u·u+u·v) + v·(u+v) = (u·u+u·v) + (v·u+v·v)   [congr ((u·u+u·v)+·) ib].
    let t3 = c.nnadd(&uu_uv, &vu_vv);
    let s3 = c.congr_arg(&v_s, &vu_vv, add_left_fn(&uu_uv), ib);

    // s4 : (u·u+u·v)+(v·u+v·v) = (u·u+u·v)+(u·v+v·v)
    //      [congr ((u·u+u·v)+·)(congr (·+v·v) (mul_comm v u))].
    let uv_vv = c.nnadd(&uv, &vv);
    let comm_vu = c.mul_comm(v, u); // v·u = u·v
    let inner4 = c.congr_arg(&vu, &uv, add_right_fn(&vv), comm_vu);
    let t4 = c.nnadd(&uu_uv, &uv_vv);
    let s4 = c.congr_arg(&vu_vv, &uv_vv, add_left_fn(&uu_uv), inner4);

    // Now reassoc t4 = (u·u+u·v)+(u·v+v·v) → (u·u+v·v)+(u·v+u·v).
    //   (u·u+u·v)+(u·v+v·v)
    //   = u·u + (u·v + (u·v+v·v))      [add_assoc u·u u·v (u·v+v·v)]
    //   = u·u + ((u·v+u·v)+v·v)        [congr (u·u+·) symm(add_assoc u·v u·v v·v)]
    //   = u·u + (v·v+(u·v+u·v))        [congr (u·u+·) add_comm (u·v+u·v) v·v]
    //   = (u·u+v·v) + (u·v+u·v)        [symm(add_assoc u·u v·v (u·v+u·v))]
    let two_uv = c.nnadd(&uv, &uv);
    let uv_then = c.nnadd(&uv, &uv_vv); // u·v + (u·v+v·v)
    let r1 = c.add_assoc(&uu, &uv, &uv_vv); // (u·u+u·v)+(u·v+v·v) = u·u+(u·v+(u·v+v·v))
    let t_r1 = c.nnadd(&uu, &uv_then);

    // inner: u·v+(u·v+v·v) = (u·v+u·v)+v·v  via symm(add_assoc u·v u·v v·v).
    let twouv_vv = c.nnadd(&two_uv, &vv); // (u·v+u·v)+v·v
    let assoc_inner = c.add_assoc(&uv, &uv, &vv); // (u·v+u·v)+v·v = u·v+(u·v+v·v)
    let inner_r2 = c.symm(&twouv_vv, &uv_then, assoc_inner);
    let r2 = c.congr_arg(&uv_then, &twouv_vv, add_left_fn(&uu), inner_r2);
    let t_r2 = c.nnadd(&uu, &twouv_vv);

    // inner: (u·v+u·v)+v·v = v·v+(u·v+u·v)  via add_comm (u·v+u·v) v·v.
    let vv_twouv = c.nnadd(&vv, &two_uv); // v·v+(u·v+u·v)
    let comm_r3 = c.add_comm(&two_uv, &vv); // (u·v+u·v)+v·v = v·v+(u·v+u·v)
    let r3 = c.congr_arg(&twouv_vv, &vv_twouv, add_left_fn(&uu), comm_r3);
    let t_r3 = c.nnadd(&uu, &vv_twouv);

    // r4 : u·u+(v·v+(u·v+u·v)) = (u·u+v·v)+(u·v+u·v)
    //      via symm(add_assoc u·u v·v (u·v+u·v)).
    let uu_vv = c.nnadd(&uu, &vv);
    let final_rhs = c.nnadd(&uu_vv, &two_uv);
    let assoc_r4 = c.add_assoc(&uu, &vv, &two_uv); // (u·u+v·v)+(u·v+u·v) = u·u+(v·v+(u·v+u·v))
    let r4 = c.symm(&final_rhs, &t_r3, assoc_r4);

    // Chain: prod =s1= t1 =s2= t2 =s3= t3 =s4= t4 =r1= t_r1 =r2= t_r2 =r3= t_r3 =r4= final_rhs.
    let ch = c.trans(&prod, &t1, &t2, s1, s2);
    let ch = c.trans(&prod, &t2, &t3, ch, s3);
    let ch = c.trans(&prod, &t3, &t4, ch, s4);
    let ch = c.trans(&prod, &t4, &t_r1, ch, r1);
    let ch = c.trans(&prod, &t_r1, &t_r2, ch, r2);
    let ch = c.trans(&prod, &t_r2, &t_r3, ch, r3);
    c.trans(&prod, &t_r3, &final_rhs, ch, r4)
}

/// `NNReal.two_mul_le_add_of_sq_le_mul_amgm` proof term: the de-square step via
/// the landed `NNReal.le_of_sq_le_sq`.
fn build_two_mul_le_add_amgm(c: &AmGmCrossConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (t_id, t) = b.fresh_local(c.nnreal.clone());
    let (a_id, a) = b.fresh_local(c.nnreal.clone());
    let (bv_id, bv) = b.fresh_local(c.nnreal.clone());
    let tt = c.nnadd(&t, &t);
    let ab = c.nnadd(&a, &bv);
    let hsq_ty = c.nnle(&c.nnmul(&tt, &tt), &c.nnmul(&ab, &ab));
    let (hsq_id, hsq) = b.fresh_local(hsq_ty.clone());

    // le_of_sq_le_sq (t+t)(a+b) hsq : (t+t) ≤ (a+b).
    let proof = c.le_of_sq_le_sq(&tt, &ab, hsq);

    let e = b.mk_lam(hsq_id, BinderInfo::Default, hsq_ty, proof);
    let e = b.mk_lam(bv_id, BinderInfo::Default, c.nnreal.clone(), e);
    let e = b.mk_lam(a_id, BinderInfo::Default, c.nnreal.clone(), e);
    let e = b.mk_lam(t_id, BinderInfo::Default, c.nnreal.clone(), e);
    b.finish(e)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const THEOREMS: &[&str] = &[
        "NNReal.four_mul_mul_le_add_sq",
        "NNReal.two_mul_le_add_of_sq_le_mul_amgm",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_amgm_cross()
            .expect("init_algebra_nnreal_amgm_cross");
        env.init_algebra_nnreal_amgm_cross().expect("idempotent");
        env
    }

    #[test]
    fn test_amgm_cross_kernel_check() {
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
    fn test_amgm_cross_constructive_empty_closure() {
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

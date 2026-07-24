// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — proof terms for `NNReal.le` (the binary `Quot.lift`
//! value, `le_refl`, `le_trans`, and the `propext` respect lemmas).
//!
//! Split out of `algebra_nnreal_le.rs` to keep both files under the 500-line
//! cap. All terms here are kernel-checked when the parent registers them; this
//! module introduces NO declarations of its own (no `add_decl`).
//!
//! # The ε/2-chain engine (`build_eventual_bound`)
//!
//! Every respect direction and `le_trans` shares one shape: combine two
//! eventual strict bounds `a < b + ε/2` and `b < c + ε/2` (sharing the middle
//! `b` at index `n ≥ max N1 N2`) into `a < c + ε`. `build_eventual_bound`
//! produces the `∃ N, ∀ n, N≤n → (va n) < (vc n + ε)` witness from the two
//! source `∃`-bounds, taking `N := Nat.max N1 N2`, chaining via `Rat.lt_trans`
//! and `Rat.add_lt_add_right`, and recombining `((vc+ε/2)+ε/2) = vc+ε` with
//! `eq_recombine`. The three call sites differ only in which sequences play the
//! roles of `a`, `b`, `c`.

use super::algebra_nnreal_le_recovered::NNLeConsts;
use super::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Combine two eventual strict half-bounds into a full-ε eventual bound.
///
/// Inputs (all under `parent`'s fvar scope):
/// - `va`,`vb`,`vc`: the three per-index value sequences (as `&dyn Fn(&m) -> Rat`).
/// - `eps`,`half`: the tolerance and `eps/2`.
/// - `src_ab`: `∃ N1, ∀ n, N1≤n → (va n) < (vb n + half)`.
/// - `src_bc`: `∃ N2, ∀ n, N2≤n → (vb n) < (vc n + half)`.
/// - `a`,`b`,`cc`: the three CauSeqs (for `pred_n`/`pred_n_at` shape building).
///
/// Output: `∃ N, ∀ n, N≤n → (va n) < (vc n + eps)`.
#[allow(clippy::too_many_arguments)]
fn build_eventual_bound(
    c: &NNLeConsts,
    parent: &EnvDeclBuilder,
    a: &Expr,
    b: &Expr,
    cc: &Expr,
    eps: &Expr,
    half: &Expr,
    src_ab: Expr,
    src_bc: Expr,
) -> Expr {
    // Goal: ∃ N, ∀ n, N≤n → (va n) < (vc n + eps).
    let goal_exists = c.exists_pred(parent, a, cc, eps);
    let pred_ab = c.pred_n(parent, a, b, half);
    let pred_bc = c.pred_n(parent, b, cc, half);

    // Outer elim over src_ab: bind N1, hN1.
    let elim_outer = {
        let mut bo = EnvDeclBuilder::child_of(parent);
        let (n1_id, n1) = bo.fresh_local(c.nat.clone());
        let hn1_ty = c.pred_n_at(&bo, a, b, half, &n1);
        let (hn1_id, hn1) = bo.fresh_local(hn1_ty.clone());

        // Inner elim over src_bc: bind N2, hN2.
        let elim_inner = {
            let mut bi = EnvDeclBuilder::child_of(&bo);
            let (n2_id, n2) = bi.fresh_local(c.nat.clone());
            let hn2_ty = c.pred_n_at(&bi, b, cc, half, &n2);
            let (hn2_id, hn2) = bi.fresh_local(hn2_ty.clone());

            let nmax = Expr::apps(c.nat_max.clone(), [n1.clone(), n2.clone()]);

            // witness : ∀ n, max≤n → (va n) < (vc n + eps).
            let witness = {
                let mut bw = EnvDeclBuilder::child_of(&bi);
                let (m_id, m) = bw.fresh_local(c.nat.clone());
                let hle_ty = c.nat_le(nmax.clone(), m.clone());
                let (hle_id, hle) = bw.fresh_local(hle_ty.clone());

                let le_max_l = Expr::apps(c.nat_le_max_left.clone(), [n1.clone(), n2.clone()]);
                let le_max_r = Expr::apps(c.nat_le_max_right.clone(), [n1.clone(), n2.clone()]);
                let n1_le_m =
                    c.nat_le_trans(n1.clone(), nmax.clone(), m.clone(), le_max_l, hle.clone());
                let n2_le_m = c.nat_le_trans(n2.clone(), nmax.clone(), m.clone(), le_max_r, hle);

                let va = c.vseq(a, &m);
                let vb = c.vseq(b, &m);
                let vc = c.vseq(cc, &m);

                // hab : (va) < (vb + half) ;  hbc : (vb) < (vc + half).
                let hab = Expr::apps(hn1.clone(), [m.clone(), n1_le_m]);
                let hbc = Expr::apps(hn2.clone(), [m.clone(), n2_le_m]);

                // step1 : (vb+half) < ((vc+half)+half)  := add_lt_add_right vb (vc+half) half hbc.
                let vc_half = c.add(vc.clone(), half.clone());
                let step1 = c.add_lt_add_right(vb.clone(), vc_half.clone(), half.clone(), hbc);
                // step2 : va < ((vc+half)+half)  := lt_trans va (vb+half) ((vc+half)+half) hab step1.
                let vb_half = c.add(vb.clone(), half.clone());
                let vc_hh = c.add(vc_half.clone(), half.clone());
                let step2 = c.lt_trans(va.clone(), vb_half, vc_hh.clone(), hab, step1);
                // recombine ((vc+half)+half) = (vc+eps) ; transport step2 via motive t := va < t.
                let rec = c.eq_recombine(&bw, &vc, eps);
                let vc_eps = c.add(vc.clone(), eps.clone());
                let motive = {
                    let mut mb = EnvDeclBuilder::child_of(&bw);
                    let (t_id, t) = mb.fresh_local(c.rat.clone());
                    let body = c.lt(va.clone(), t);
                    mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                let proof = c.subst_rat(motive, vc_hh, vc_eps, rec, step2);

                let e = bw.mk_lam(hle_id, BinderInfo::Default, hle_ty, proof);
                let e = bw.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
                bw.finish_child(e)
            };

            let intro = Expr::apps(
                c.exists_intro.clone(),
                [c.nat.clone(), c.pred_n(&bi, a, cc, eps), nmax, witness],
            );
            let e = bi.mk_lam(hn2_id, BinderInfo::Default, hn2_ty, intro);
            let e = bi.mk_lam(n2_id, BinderInfo::Default, c.nat.clone(), e);
            bi.finish_child(e)
        };

        let elim_bc = Expr::apps(
            c.exists_elim.clone(),
            [
                c.nat.clone(),
                pred_bc.clone(),
                goal_exists.clone(),
                src_bc,
                elim_inner,
            ],
        );
        let e = bo.mk_lam(hn1_id, BinderInfo::Default, hn1_ty, elim_bc);
        let e = bo.mk_lam(n1_id, BinderInfo::Default, c.nat.clone(), e);
        bo.finish_child(e)
    };

    Expr::apps(
        c.exists_elim.clone(),
        [c.nat.clone(), pred_ab, goal_exists, src_ab, elim_outer],
    )
}

/// `eps/2` and its positivity proof from `hpos : 0 < eps`.
fn half_pos(c: &NNLeConsts, eps: &Expr, hpos: &Expr) -> (Expr, Expr) {
    let half = c.half(eps.clone());
    let heps2 = Expr::apps(c.rat_half_pos.clone(), [eps.clone(), hpos.clone()]);
    (half, heps2)
}

/// One side of `LE` from an `Equiv`-conjunct, as the `∃`-bound at `half`.
/// Given `hequiv : Equiv x y` (applied at `half`,`heps2` it yields
/// `∃ N, ∀ n, N≤n → And (vx<vy+half)(vy<vx+half)`), peel it and re-pack the
/// chosen conjunct (`use_left`) into `∃ N, ∀ n, N≤n → (lhs)<(rhs)+half`.
///
/// `use_left = true`  → conjunct `vx < vy + half`  (sequences `(x, y)`).
/// `use_left = false` → conjunct `vy < vx + half`  (sequences `(y, x)`).
#[allow(clippy::too_many_arguments)]
fn equiv_conjunct_bound(
    c: &NNLeConsts,
    parent: &EnvDeclBuilder,
    x: &Expr,
    y: &Expr,
    half: &Expr,
    heps2: &Expr,
    hequiv: &Expr,
    use_left: bool,
) -> Expr {
    // src : ∃ N, ∀ n, N≤n → And (vx<vy+half)(vy<vx+half).
    let src = Expr::apps(hequiv.clone(), [half.clone(), heps2.clone()]);

    // predicate of `src` (the Equiv body's And-form at `half`).
    let pred_and = {
        let mut bn = EnvDeclBuilder::child_of(parent);
        let (n_id, n_cap) = bn.fresh_local(c.nat.clone());
        let inner = {
            let mut bi = EnvDeclBuilder::child_of(&bn);
            let (m_id, m) = bi.fresh_local(c.nat.clone());
            let hle = c.nat_le(n_cap.clone(), m.clone());
            let (hle_id, _h) = bi.fresh_local(hle.clone());
            let vx = c.vseq(x, &m);
            let vy = c.vseq(y, &m);
            let l = c.lt(vx.clone(), c.add(vy.clone(), half.clone()));
            let r = c.lt(vy.clone(), c.add(vx.clone(), half.clone()));
            let concl = Expr::apps(c.and_c.clone(), [l, r]);
            let e = bi.mk_pi(hle_id, BinderInfo::Default, hle, concl);
            let e = bi.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
            bi.finish_child(e)
        };
        let lam = bn.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), inner);
        bn.finish_child(lam)
    };

    // The output sequences for the chosen conjunct.
    let (oa, ob) = if use_left { (x, y) } else { (y, x) };
    let goal = c.exists_pred(parent, oa, ob, half);

    let elim_fn = {
        let mut be = EnvDeclBuilder::child_of(parent);
        let (n_id, n_cap) = be.fresh_local(c.nat.clone());
        // hN : ∀ n, N≤n → And (vx<vy+half)(vy<vx+half).
        let hn_ty = {
            let mut bi = EnvDeclBuilder::child_of(&be);
            let (m_id, m) = bi.fresh_local(c.nat.clone());
            let hle = c.nat_le(n_cap.clone(), m.clone());
            let (hle_id, _h) = bi.fresh_local(hle.clone());
            let vx = c.vseq(x, &m);
            let vy = c.vseq(y, &m);
            let l = c.lt(vx.clone(), c.add(vy.clone(), half.clone()));
            let r = c.lt(vy.clone(), c.add(vx.clone(), half.clone()));
            let concl = Expr::apps(c.and_c.clone(), [l, r]);
            let e = bi.mk_pi(hle_id, BinderInfo::Default, hle, concl);
            let e = bi.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
            bi.finish_child(e)
        };
        let (hn_id, hn) = be.fresh_local(hn_ty.clone());

        // witness : ∀ n, N≤n → (voa)<(vob)+half  (the chosen conjunct).
        let witness = {
            let mut bw = EnvDeclBuilder::child_of(&be);
            let (m_id, m) = bw.fresh_local(c.nat.clone());
            let hle_ty = c.nat_le(n_cap.clone(), m.clone());
            let (hle_id, hle) = bw.fresh_local(hle_ty.clone());
            let vx = c.vseq(x, &m);
            let vy = c.vseq(y, &m);
            let l = c.lt(vx.clone(), c.add(vy.clone(), half.clone()));
            let r = c.lt(vy.clone(), c.add(vx.clone(), half.clone()));
            let base = Expr::apps(hn.clone(), [m.clone(), hle]);
            let proof = if use_left {
                c.and_left(l, r, base)
            } else {
                c.and_right(l, r, base)
            };
            let e = bw.mk_lam(hle_id, BinderInfo::Default, hle_ty, proof);
            let e = bw.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
            bw.finish_child(e)
        };
        let intro = Expr::apps(
            c.exists_intro.clone(),
            [
                c.nat.clone(),
                c.pred_n(&be, oa, ob, half),
                n_cap.clone(),
                witness,
            ],
        );
        let e = be.mk_lam(hn_id, BinderInfo::Default, hn_ty, intro);
        let e = be.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
        be.finish_child(e)
    };

    Expr::apps(
        c.exists_elim.clone(),
        [c.nat.clone(), pred_and, goal, src, elim_fn],
    )
}

/// Build a single implication `LE A B → LE A' B'` where the middle bridge is
/// supplied by one `Equiv`-conjunct and the hypothesis `LE`. `swap_kind`
/// selects which respect we are proving:
/// - `Side::Right`: `f` fixed, vary `g`→`g2` via `hequiv : Equiv g g2`.
///     forward: `LE f g → LE f g2`  (bridge `g < g2 + half`, sequences a=f,b=g,c=g2).
///     backward: `LE f g2 → LE f g` (bridge `g2 < g + half`).
/// - `Side::Left`: `g` fixed, vary `f`→`f2` via `hequiv : Equiv f f2`.
///     forward: `LE f g → LE f2 g`  (bridge `f2 < f + half`, sequences a=f2,b=f,c=g).
///     backward: `LE f2 g → LE f g`.
///
/// Implemented uniformly: given the hypothesis-`LE` source (at `half`) and the
/// equiv-conjunct bridge (at `half`), `build_eventual_bound` chains them.
struct ImplSpec<'a> {
    /// The CauSeq that is the LHS of the *conclusion* `LE` (the `a` of the goal).
    concl_lhs: &'a Expr,
    /// The CauSeq that is the RHS of the conclusion `LE` (the `c` of the goal).
    concl_rhs: &'a Expr,
    /// The shared middle CauSeq (`b`).
    mid: &'a Expr,
    /// Whether the equiv-bridge is the *first* leg (a<b) or the *second* (b<c).
    bridge_is_first: bool,
}

/// Build the implication function `(h : LE concl_lhs' concl_rhs') → LE concl_lhs concl_rhs`
/// — but expressed directly as a lambda taking the source `LE`. Returns the
/// lambda `fun (hle : LE hyp_lhs hyp_rhs) => <eventual bound proof of LE concl_lhs concl_rhs>`.
#[allow(clippy::too_many_arguments)]
fn build_impl(
    c: &NNLeConsts,
    parent: &EnvDeclBuilder,
    hyp_lhs: &Expr,
    hyp_rhs: &Expr,
    spec: &ImplSpec,
    // The equiv used for the bridge, plus which conjunct (true = left conjunct).
    hequiv: &Expr,
    bridge_x: &Expr,
    bridge_y: &Expr,
    bridge_use_left: bool,
) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let hyp_ty = c.causeq_le(hyp_lhs.clone(), hyp_rhs.clone());
    let (h_id, h) = b.fresh_local(hyp_ty.clone());

    // Body : LE concl_lhs concl_rhs = ∀ ε,0<ε → ∃ …
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let hpos_ty = c.lt(c.rat_zero.clone(), eps.clone());
    let (hpos_id, hpos) = b.fresh_local(hpos_ty.clone());
    let (half, heps2) = half_pos(c, &eps, &hpos);

    // hyp source at half: ∃ N, ∀ n, N≤n → (v hyp_lhs) < (v hyp_rhs)+half.
    let src_hyp = Expr::apps(h.clone(), [half.clone(), heps2.clone()]);
    // equiv bridge at half (the chosen conjunct).
    let src_bridge = equiv_conjunct_bound(
        c,
        &b,
        bridge_x,
        bridge_y,
        &half,
        &heps2,
        hequiv,
        bridge_use_left,
    );

    // Order the two legs (a<b, b<c) per spec.bridge_is_first.
    let (src_ab, src_bc) = if spec.bridge_is_first {
        (src_bridge, src_hyp)
    } else {
        (src_hyp, src_bridge)
    };

    let bound = build_eventual_bound(
        c,
        &b,
        spec.concl_lhs,
        spec.mid,
        spec.concl_rhs,
        &eps,
        &half,
        src_ab,
        src_bc,
    );

    let e = b.mk_lam(hpos_id, BinderInfo::Default, hpos_ty, bound);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(h_id, BinderInfo::Default, hyp_ty, e);
    b.finish_child(e)
}

/// `le_respects_right f g g2 (hgg2 : Equiv g g2) : Eq Prop (LE f g) (LE f g2)`.
fn le_respects_right(
    c: &NNLeConsts,
    parent: &EnvDeclBuilder,
    f: &Expr,
    g: &Expr,
    g2: &Expr,
    hgg2: &Expr,
) -> Expr {
    // forward : LE f g → LE f g2. bridge = (g < g2 + half) [left conjunct of Equiv g g2].
    //   legs: a=f<b=g (hyp), b=g<c=g2 (bridge) → bridge is SECOND leg.
    let fwd_spec = ImplSpec {
        concl_lhs: f,
        concl_rhs: g2,
        mid: g,
        bridge_is_first: false,
    };
    let fwd = build_impl(
        c, parent, f, g, &fwd_spec, hgg2, g, g2, /*use_left=*/ true,
    );

    // backward : LE f g2 → LE f g. bridge = (g2 < g + half) [right conjunct].
    //   legs: a=f<b=g2 (hyp), b=g2<c=g (bridge) → bridge SECOND.
    let bwd_spec = ImplSpec {
        concl_lhs: f,
        concl_rhs: g,
        mid: g2,
        bridge_is_first: false,
    };
    let bwd = build_impl(
        c, parent, f, g2, &bwd_spec, hgg2, g, g2, /*use_left=*/ false,
    );

    let p1 = c.causeq_le(f.clone(), g.clone());
    let p2 = c.causeq_le(f.clone(), g2.clone());
    c.propext(p1, p2, fwd, bwd)
}

/// `le_respects_left f f2 g (hff2 : Equiv f f2) : Eq Prop (LE f g) (LE f2 g)`.
fn le_respects_left(
    c: &NNLeConsts,
    parent: &EnvDeclBuilder,
    f: &Expr,
    f2: &Expr,
    g: &Expr,
    hff2: &Expr,
) -> Expr {
    // forward : LE f g → LE f2 g. bridge = (f2 < f + half) [right conjunct of Equiv f f2].
    //   legs: a=f2<b=f (bridge), b=f<c=g (hyp) → bridge FIRST.
    let fwd_spec = ImplSpec {
        concl_lhs: f2,
        concl_rhs: g,
        mid: f,
        bridge_is_first: true,
    };
    let fwd = build_impl(
        c, parent, f, g, &fwd_spec, hff2, f, f2, /*use_left=*/ false,
    );

    // backward : LE f2 g → LE f g. bridge = (f < f2 + half) [left conjunct].
    //   legs: a=f<b=f2 (bridge), b=f2<c=g (hyp) → bridge FIRST.
    let bwd_spec = ImplSpec {
        concl_lhs: f,
        concl_rhs: g,
        mid: f2,
        bridge_is_first: true,
    };
    let bwd = build_impl(
        c, parent, f2, g, &bwd_spec, hff2, f, f2, /*use_left=*/ true,
    );

    let p1 = c.causeq_le(f.clone(), g.clone());
    let p2 = c.causeq_le(f2.clone(), g.clone());
    c.propext(p1, p2, fwd, bwd)
}

/// `NNReal.le := fun a b => Quot.lift (outer_f)(outer_h) a` (binary lift into
/// Prop). Mirrors `Qat.le`.
pub(crate) fn build_nnreal_le_value(c: &NNLeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.nnreal.clone());
    let (bv_id, bv) = b.fresh_local(c.nnreal.clone());

    // inner_lift first bb := Quot.lift (fun q => LE first q)(respect_right) bb.
    let inner_lift = |parent: &EnvDeclBuilder, first: &Expr, second: &Expr| -> Expr {
        let inner_f = {
            let mut bi = EnvDeclBuilder::child_of(parent);
            let (q_id, q) = bi.fresh_local(c.causeq.clone());
            let body = c.causeq_le(first.clone(), q.clone());
            let lam = bi.mk_lam(q_id, BinderInfo::Default, c.causeq.clone(), body);
            bi.finish_child(lam)
        };
        let inner_h = {
            let mut bi = EnvDeclBuilder::child_of(parent);
            let (q_id, q) = bi.fresh_local(c.causeq.clone());
            let (q2_id, q2) = bi.fresh_local(c.causeq.clone());
            let hh = c.equiv(q.clone(), q2.clone());
            let (hq_id, hq) = bi.fresh_local(hh.clone());
            let body = le_respects_right(c, &bi, first, &q, &q2, &hq);
            let lam = bi.mk_lam(hq_id, BinderInfo::Default, hh, body);
            let lam = bi.mk_lam(q2_id, BinderInfo::Default, c.causeq.clone(), lam);
            let lam = bi.mk_lam(q_id, BinderInfo::Default, c.causeq.clone(), lam);
            bi.finish_child(lam)
        };
        Expr::apps(
            c.quot_lift_prop.clone(),
            [
                c.causeq.clone(),
                c.causeq_equiv.clone(),
                c.prop.clone(),
                inner_f,
                inner_h,
                second.clone(),
            ],
        )
    };

    // outer_f := fun (p : CauSeq) => inner_lift p bv.
    let outer_f = {
        let mut bo = EnvDeclBuilder::child_of(&b);
        let (p_id, p) = bo.fresh_local(c.causeq.clone());
        let body = inner_lift(&bo, &p, &bv);
        let lam = bo.mk_lam(p_id, BinderInfo::Default, c.causeq.clone(), body);
        bo.finish_child(lam)
    };

    // outer_h : ∀ p p2, Equiv p p2 → Eq Prop (inner_lift p bv)(inner_lift p2 bv).
    // Via Quot.ind on bv: each leaf is le_respects_left p p2 q hp (propext).
    let outer_h = {
        let mut bh = EnvDeclBuilder::child_of(&b);
        let (p_id, p) = bh.fresh_local(c.causeq.clone());
        let (p2_id, p2) = bh.fresh_local(c.causeq.clone());
        let hyp = c.equiv(p.clone(), p2.clone());
        let (hp_id, hp) = bh.fresh_local(hyp.clone());

        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&bh);
            let (x_id, x) = mb.fresh_local(c.nnreal.clone());
            let lhs = inner_lift(&mb, &p, &x);
            let rhs = inner_lift(&mb, &p2, &x);
            let eq_prop = Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [c.prop.clone(), lhs, rhs],
            );
            mb.finish_child(mb.mk_lam(x_id, BinderInfo::Default, c.nnreal.clone(), eq_prop))
        };
        let minor = {
            let mut mb = EnvDeclBuilder::child_of(&bh);
            let (q_id, q) = mb.fresh_local(c.causeq.clone());
            // Eq Prop (LE p q)(LE p2 q) := le_respects_left p p2 q hp.
            let body = le_respects_left(c, &mb, &p, &p2, &q, &hp);
            mb.finish_child(mb.mk_lam(q_id, BinderInfo::Default, c.causeq.clone(), body))
        };
        let ind = Expr::apps(
            c.quot_ind.clone(),
            [
                c.causeq.clone(),
                c.causeq_equiv.clone(),
                motive,
                minor,
                bv.clone(),
            ],
        );
        let lam = bh.mk_lam(hp_id, BinderInfo::Default, hyp, ind);
        let lam = bh.mk_lam(p2_id, BinderInfo::Default, c.causeq.clone(), lam);
        let lam = bh.mk_lam(p_id, BinderInfo::Default, c.causeq.clone(), lam);
        bh.finish_child(lam)
    };

    let outer = Expr::apps(
        c.quot_lift_prop.clone(),
        [
            c.causeq.clone(),
            c.causeq_equiv.clone(),
            c.prop.clone(),
            outer_f,
            outer_h,
            a.clone(),
        ],
    );
    let e = b.mk_lam(bv_id, BinderInfo::Default, c.nnreal.clone(), outer);
    let e = b.mk_lam(a_id, BinderInfo::Default, c.nnreal.clone(), e);
    b.finish(e)
}

/// `NNReal.le_refl : ∀ x, NNReal.le x x`.
pub(crate) fn build_le_refl_proof(c: &NNLeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(c.nnreal.clone());

    // Quot.ind motive: fun x => NNReal.le x x  (≡ CauSeq.LE p p at leaf).
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (u_id, u) = mb.fresh_local(c.nnreal.clone());
        let body = Expr::apps(
            Expr::const_(Name::from_string("NNReal.le"), vec![]),
            [u.clone(), u.clone()],
        );
        mb.finish_child(mb.mk_lam(u_id, BinderInfo::Default, c.nnreal.clone(), body))
    };
    let minor = {
        let mut bp = EnvDeclBuilder::child_of(&b);
        let (p_id, p) = bp.fresh_local(c.causeq.clone());
        // Goal at leaf: NNReal.le (mk p)(mk p) ≡ CauSeq.LE p p.
        let body = build_causeq_le_refl(c, &bp, &p);
        bp.finish_child(bp.mk_lam(p_id, BinderInfo::Default, c.causeq.clone(), body))
    };
    let ind = Expr::apps(
        c.quot_ind.clone(),
        [
            c.causeq.clone(),
            c.causeq_equiv.clone(),
            motive,
            minor,
            x.clone(),
        ],
    );
    let e = b.mk_lam(x_id, BinderInfo::Default, c.nnreal.clone(), ind);
    b.finish(e)
}

/// `CauSeq.LE p p` : the diagonal `refl` pattern.
fn build_causeq_le_refl(c: &NNLeConsts, parent: &EnvDeclBuilder, p: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let hpos_ty = c.lt(c.rat_zero.clone(), eps.clone());
    let (hpos_id, hpos) = b.fresh_local(hpos_ty.clone());

    let witness = {
        let mut bw = EnvDeclBuilder::child_of(&b);
        let (m_id, m) = bw.fresh_local(c.nat.clone());
        let hle = c.nat_le(c.nat_zero.clone(), m.clone());
        let (hle_id, _h) = bw.fresh_local(hle.clone());
        let v = c.vseq(p, &m);
        // p0 : (v+0) < (v+ε) ; transport (v+0)→v via add_zero.
        let p0 = c.add_lt_add_left(c.rat_zero.clone(), eps.clone(), v.clone(), hpos.clone());
        let v_eps = c.add(v.clone(), eps.clone());
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&bw);
            let (t_id, t) = mb.fresh_local(c.rat.clone());
            let body = c.lt(t, v_eps.clone());
            mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let v_zero = c.add(v.clone(), c.rat_zero.clone());
        let proof = c.subst_rat(motive, v_zero, v.clone(), c.add_zero(v.clone()), p0);
        let e = bw.mk_lam(hle_id, BinderInfo::Default, hle, proof);
        let e = bw.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
        bw.finish_child(e)
    };
    let intro = Expr::apps(
        c.exists_intro.clone(),
        [
            c.nat.clone(),
            c.pred_n(&b, p, p, &eps),
            c.nat_zero.clone(),
            witness,
        ],
    );
    let e = b.mk_lam(hpos_id, BinderInfo::Default, hpos_ty, intro);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish_child(e)
}

/// `NNReal.le_trans : ∀ x y z, NNReal.le x y → NNReal.le y z → NNReal.le x z`.
pub(crate) fn build_le_trans_proof(c: &NNLeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(c.nnreal.clone());
    let (y_id, y) = b.fresh_local(c.nnreal.clone());
    let (z_id, z) = b.fresh_local(c.nnreal.clone());
    let nnle = Expr::const_(Name::from_string("NNReal.le"), vec![]);
    let le = |a: Expr, bb: Expr| Expr::apps(nnle.clone(), [a, bb]);

    // Triple Quot.ind: x then y then z. At the (mk p)(mk q)(mk r) leaf the goal
    // reduces to CauSeq.LE p q → CauSeq.LE q r → CauSeq.LE p r.
    let motive_x = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (u_id, u) = mb.fresh_local(c.nnreal.clone());
        let h1 = le(u.clone(), y.clone());
        let (h1_id, _) = mb.fresh_local(h1.clone());
        let h2 = le(y.clone(), z.clone());
        let (h2_id, _) = mb.fresh_local(h2.clone());
        let concl = le(u.clone(), z.clone());
        let e = mb.mk_pi(h2_id, BinderInfo::Default, h2, concl);
        let e = mb.mk_pi(h1_id, BinderInfo::Default, h1, e);
        mb.finish_child(mb.mk_lam(u_id, BinderInfo::Default, c.nnreal.clone(), e))
    };
    let minor_x = {
        let mut bp = EnvDeclBuilder::child_of(&b);
        let (p_id, p) = bp.fresh_local(c.causeq.clone());
        let mk_p = c.quot_mk(p.clone());
        let motive_y = {
            let mut mb = EnvDeclBuilder::child_of(&bp);
            let (v_id, v) = mb.fresh_local(c.nnreal.clone());
            let h1 = le(mk_p.clone(), v.clone());
            let (h1_id, _) = mb.fresh_local(h1.clone());
            let h2 = le(v.clone(), z.clone());
            let (h2_id, _) = mb.fresh_local(h2.clone());
            let concl = le(mk_p.clone(), z.clone());
            let e = mb.mk_pi(h2_id, BinderInfo::Default, h2, concl);
            let e = mb.mk_pi(h1_id, BinderInfo::Default, h1, e);
            mb.finish_child(mb.mk_lam(v_id, BinderInfo::Default, c.nnreal.clone(), e))
        };
        let minor_y = {
            let mut bq = EnvDeclBuilder::child_of(&bp);
            let (q_id, q) = bq.fresh_local(c.causeq.clone());
            let mk_q = c.quot_mk(q.clone());
            let motive_z = {
                let mut mb = EnvDeclBuilder::child_of(&bq);
                let (w_id, w) = mb.fresh_local(c.nnreal.clone());
                let h1 = le(mk_p.clone(), mk_q.clone());
                let (h1_id, _) = mb.fresh_local(h1.clone());
                let h2 = le(mk_q.clone(), w.clone());
                let (h2_id, _) = mb.fresh_local(h2.clone());
                let concl = le(mk_p.clone(), w.clone());
                let e = mb.mk_pi(h2_id, BinderInfo::Default, h2, concl);
                let e = mb.mk_pi(h1_id, BinderInfo::Default, h1, e);
                mb.finish_child(mb.mk_lam(w_id, BinderInfo::Default, c.nnreal.clone(), e))
            };
            let minor_z = {
                let mut br = EnvDeclBuilder::child_of(&bq);
                let (r_id, rr) = br.fresh_local(c.causeq.clone());
                let body = build_causeq_le_trans(c, &br, &p, &q, &rr);
                br.finish_child(br.mk_lam(r_id, BinderInfo::Default, c.causeq.clone(), body))
            };
            let ind_z = Expr::apps(
                c.quot_ind.clone(),
                [
                    c.causeq.clone(),
                    c.causeq_equiv.clone(),
                    motive_z,
                    minor_z,
                    z.clone(),
                ],
            );
            bq.finish_child(bq.mk_lam(q_id, BinderInfo::Default, c.causeq.clone(), ind_z))
        };
        let ind_y = Expr::apps(
            c.quot_ind.clone(),
            [
                c.causeq.clone(),
                c.causeq_equiv.clone(),
                motive_y,
                minor_y,
                y.clone(),
            ],
        );
        bp.finish_child(bp.mk_lam(p_id, BinderInfo::Default, c.causeq.clone(), ind_y))
    };
    let ind_x = Expr::apps(
        c.quot_ind.clone(),
        [
            c.causeq.clone(),
            c.causeq_equiv.clone(),
            motive_x,
            minor_x,
            x.clone(),
        ],
    );
    let e = b.mk_lam(z_id, BinderInfo::Default, c.nnreal.clone(), ind_x);
    let e = b.mk_lam(y_id, BinderInfo::Default, c.nnreal.clone(), e);
    let e = b.mk_lam(x_id, BinderInfo::Default, c.nnreal.clone(), e);
    b.finish(e)
}

/// `CauSeq.LE p q → CauSeq.LE q r → CauSeq.LE p r` (the ε/2-chain).
fn build_causeq_le_trans(
    c: &NNLeConsts,
    parent: &EnvDeclBuilder,
    p: &Expr,
    q: &Expr,
    r: &Expr,
) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let hpq_ty = c.causeq_le(p.clone(), q.clone());
    let (hpq_id, hpq) = b.fresh_local(hpq_ty.clone());
    let hqr_ty = c.causeq_le(q.clone(), r.clone());
    let (hqr_id, hqr) = b.fresh_local(hqr_ty.clone());

    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let hpos_ty = c.lt(c.rat_zero.clone(), eps.clone());
    let (hpos_id, hpos) = b.fresh_local(hpos_ty.clone());
    let (half, heps2) = half_pos(c, &eps, &hpos);

    // src_ab : ∃ N, ∀ n, N≤n → (vp)<(vq)+half := hpq half heps2.
    let src_ab = Expr::apps(hpq.clone(), [half.clone(), heps2.clone()]);
    // src_bc : ∃ N, ∀ n, N≤n → (vq)<(vr)+half := hqr half heps2.
    let src_bc = Expr::apps(hqr.clone(), [half.clone(), heps2]);

    let bound = build_eventual_bound(c, &b, p, q, r, &eps, &half, src_ab, src_bc);

    let e = b.mk_lam(hpos_id, BinderInfo::Default, hpos_ty, bound);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(hqr_id, BinderInfo::Default, hqr_ty, e);
    let e = b.mk_lam(hpq_id, BinderInfo::Default, hpq_ty, e);
    b.finish_child(e)
}

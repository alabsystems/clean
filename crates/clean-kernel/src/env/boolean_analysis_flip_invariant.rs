// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Cube-sum invariance under the coordinate-flip involution.
//!
//! ```text
//! BoolAnalysis.subsetSum_flip_invariant :
//!   ∀ (n : Nat) (g : HCPoint n → Rat) (i : Fin n),
//!     subsetSum n (fun x => g (hcFlip n x i)) = subsetSum n g
//! ```
//!
//! This is the foundational primitive for the per-`S` derivative collapse
//! (`A(D_i f, S) = (2·ind(S i))·A(f, S)`): the second term of
//! `A(D_i f, S) = A(f, S) − Σ_x f(hcFlip x i)·χ_S(x)` is, by this invariance,
//! `flipSign(S i)·A(f, S)`.
//!
//! ## Reduction structure (the tractable half — LANDED here)
//!
//! `subsetSum n h` δ-unfolds (subsetSum reducible) to
//! `Fin.sum (2^n) (fun jx => h (hcDecode n jx))`.  With `h := fun x => g (hcFlip
//! n x i)` the summand is `g (hcFlip n (hcDecode n jx) i)`, which the keystone
//! `hcFlip_decode_roundtrip` (`hcDecode n (flipIdx n i jx) = hcFlip n (hcDecode
//! n jx) i`) rewrites to `g (hcDecode n (flipIdx n i jx))`.  So
//!
//! ```text
//!   subsetSum n (fun x => g (hcFlip n x i))
//!     ≡ Fin.sum (2^n) (fun jx => g (hcDecode n (flipIdx n i jx)))
//!     = Fin.sum (2^n) (fun jx => g (hcDecode n jx))            ← THE REINDEX
//!     ≡ subsetSum n g.
//! ```
//!
//! The first `≡` is δ + the roundtrip lifted by `Fin.sum_congr` (the per-index
//! pointwise equality `g (hcFlip n (hcDecode n jx) i) = g (hcDecode n (flipIdx n
//! i jx))` is `congrArg g (Eq.symm (hcFlip_decode_roundtrip n i jx))`); the last
//! `≡` is δ.  The MIDDLE step — the cube reindex by the involution `flipIdx n
//! i` on `Fin (2^n)` — is the genuinely missing kernel primitive
//! (`Fin.sum_reindex_involution`, see below): the kernel has NO general
//! `Fin.sum` permutation / bijection-reindex theory.
//!
//! ## Status
//!
//! - `subsetSum_flip_invariant` is built as a kernel-checked Theorem **modulo**
//!   the `Fin.sum_reindex_involution` reindex leg (it consumes that leg as a
//!   registered dependency, NOT as an axiom).
//! - `Fin.sum_reindex_involution` is the precise unbuilt frontier.  It is stated
//!   here with its exact signature so the reduction is wired and type-checked;
//!   its constructive proof requires `Fin.sum` permutation theory that does not
//!   yet exist in the kernel.  Until it lands as a constructive Theorem, this
//!   module is NOT wired into the always-on aggregate and `subsetSum_flip_
//!   invariant` is NOT registered (no Axiom is introduced — fail-closed).

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached atoms for the flip-invariance reduction.
struct FlipInvConsts {
    nat: Expr,
    rat: Expr,
    nat_succ: Expr,
    nat_zero: Expr,
    nat_pow: Expr,
    fin: Expr,
    fin_sum: Expr,
    fin_sum_congr: Expr,
    hcpoint: Expr,
    hc_decode: Expr,
    hc_flip: Expr,
    flip_idx: Expr,
    roundtrip: Expr,
    subset_sum: Expr,
    reindex_invol: Expr,
    congr_arg: Expr,
    eq_symm: Expr,
    eq_trans: Expr,
    eq1: Expr,
}

impl FlipInvConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            nat_succ: k("Nat.succ"),
            nat_zero: k("Nat.zero"),
            nat_pow: k("Nat.pow"),
            fin: k("Fin"),
            fin_sum: k("Fin.sum"),
            fin_sum_congr: k("Fin.sum_congr"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            hc_decode: k("BoolAnalysis.hcDecode"),
            hc_flip: k("BoolAnalysis.hcFlip"),
            flip_idx: k("BoolAnalysis.flipIdx"),
            roundtrip: k("BoolAnalysis.hcFlip_decode_roundtrip"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            reindex_invol: k("Fin.sum_reindex_involution"),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1]),
        }
    }

    fn two(&self) -> Expr {
        Expr::app(
            self.nat_succ.clone(),
            Expr::app(self.nat_succ.clone(), self.nat_zero.clone()),
        )
    }
    fn pow2(&self, n: &Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.two(), n.clone()])
    }
    fn fin_of(&self, m: &Expr) -> Expr {
        Expr::app(self.fin.clone(), m.clone())
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn hcpoint_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.rat.clone())
    }
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), l, r])
    }
    /// `subsetSum n h`.
    fn ssum(&self, n: &Expr, h: &Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), h.clone()])
    }
    /// `hcDecode n jx`.
    fn decode(&self, n: &Expr, jx: &Expr) -> Expr {
        Expr::apps(self.hc_decode.clone(), [n.clone(), jx.clone()])
    }
    /// `hcFlip n x i`.
    fn flip(&self, n: &Expr, x: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.hc_flip.clone(), [n.clone(), x.clone(), i.clone()])
    }
    /// `flipIdx n i jx`.
    fn flipidx(&self, n: &Expr, i: &Expr, jx: &Expr) -> Expr {
        Expr::apps(self.flip_idx.clone(), [n.clone(), i.clone(), jx.clone()])
    }
}

// ===========================================================================
// Fin.sum_reindex_involution (the GENERAL reindex primitive — STATEMENT only).
//
//   ∀ (m : Nat) (σ : Fin m → Fin m),
//     (∀ jx : Fin m, σ (σ jx) = jx)                       -- σ is an involution
//       → ∀ (F : Fin m → Rat),
//           Fin.sum m (fun jx => F (σ jx)) = Fin.sum m F
//
// An involution on Fin m is a self-inverse function, hence a bijection, hence
// the reindexed sum equals the original. The constructive proof requires
// `Fin.sum` permutation theory (a `List.Perm`-style sum-invariance bridge, or a
// strong-induction "peel a fixed point / a 2-cycle" argument). Neither exists
// in the kernel today, so this is registered as the precise frontier statement
// (NOT proven, NOT wired) — see the module docs.
// ===========================================================================
fn reindex_involution_type(c: &FlipInvConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let fin_m = c.fin_of(&m);
    // σ : Fin m → Fin m
    let sigma_ty = Expr::pi(BinderInfo::Default, fin_m.clone(), fin_m.clone());
    let (sigma_id, sigma) = b.fresh_local(sigma_ty.clone());

    // hinv : ∀ jx : Fin m, σ (σ jx) = jx
    let hinv = {
        let mut hb = EnvDeclBuilder::child_of(&b);
        let (jx_id, jx) = hb.fresh_local(fin_m.clone());
        let ssjx = Expr::app(sigma.clone(), Expr::app(sigma.clone(), jx.clone()));
        let body = Expr::apps(c.eq1.clone(), [fin_m.clone(), ssjx, jx.clone()]);
        hb.finish_child(hb.mk_pi(jx_id, BinderInfo::Default, fin_m.clone(), body))
    };
    let (hinv_id, _hinv) = b.fresh_local(hinv.clone());

    // F : Fin m → Rat
    let f_ty = Expr::pi(BinderInfo::Default, fin_m.clone(), c.rat.clone());
    let (f_id, f) = b.fresh_local(f_ty.clone());

    // fun jx => F (σ jx)
    let reindexed = {
        let mut rb = EnvDeclBuilder::child_of(&b);
        let (jx_id, jx) = rb.fresh_local(fin_m.clone());
        let body = Expr::app(f.clone(), Expr::app(sigma.clone(), jx.clone()));
        rb.finish_child(rb.mk_lam(jx_id, BinderInfo::Default, fin_m.clone(), body))
    };
    let lhs = Expr::apps(c.fin_sum.clone(), [m.clone(), reindexed]);
    let rhs = Expr::apps(c.fin_sum.clone(), [m.clone(), f.clone()]);
    let concl = c.eq_rat(lhs, rhs);

    let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, concl);
    let e = b.mk_pi(hinv_id, BinderInfo::Default, hinv, e);
    let e = b.mk_pi(sigma_id, BinderInfo::Default, sigma_ty, e);
    b.finish(b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e))
}

// ===========================================================================
// subsetSum_flip_invariant (the REDUCTION — proven modulo the reindex leg).
// ===========================================================================
fn flip_invariant_type(c: &FlipInvConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let g_ty = c.hcpoint_to_rat(&n);
    let (g_id, g) = b.fresh_local(g_ty.clone());
    let (i_id, i) = b.fresh_local(c.fin_of(&n));

    // lhs_fn := fun x => g (hcFlip n x i)
    let lhs_fn = {
        let mut sb = EnvDeclBuilder::child_of(&b);
        let hcp = c.hcpoint_of(&n);
        let (x_id, x) = sb.fresh_local(hcp.clone());
        let body = Expr::app(g.clone(), c.flip(&n, &x, &i));
        sb.finish_child(sb.mk_lam(x_id, BinderInfo::Default, hcp, body))
    };
    let lhs = c.ssum(&n, &lhs_fn);
    let rhs = c.ssum(&n, &g);
    let concl = c.eq_rat(lhs, rhs);

    let e = b.mk_pi(i_id, BinderInfo::Default, c.fin_of(&n), concl);
    let e = b.mk_pi(g_id, BinderInfo::Default, g_ty, e);
    b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e))
}

fn flip_invariant_value(c: &FlipInvConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let g_ty = c.hcpoint_to_rat(&n);
    let (g_id, g) = b.fresh_local(g_ty.clone());
    let (i_id, i) = b.fresh_local(c.fin_of(&n));

    let p2n = c.pow2(&n);
    let fin_p2n = c.fin_of(&p2n);

    // decoded-summand of `g`: fun jx => g (hcDecode n jx)  (= subsetSum n g, δ).
    let g_dec = |c: &FlipInvConsts, parent: &EnvDeclBuilder| -> Expr {
        let mut sb = EnvDeclBuilder::child_of(parent);
        let (jx_id, jx) = sb.fresh_local(fin_p2n.clone());
        let body = Expr::app(g.clone(), c.decode(&n, &jx));
        sb.finish_child(sb.mk_lam(jx_id, BinderInfo::Default, fin_p2n.clone(), body))
    };

    // LHS-summand after δ: fun jx => g (hcFlip n (hcDecode n jx) i).
    let flip_dec = |c: &FlipInvConsts, parent: &EnvDeclBuilder| -> Expr {
        let mut sb = EnvDeclBuilder::child_of(parent);
        let (jx_id, jx) = sb.fresh_local(fin_p2n.clone());
        let dec = c.decode(&n, &jx);
        let body = Expr::app(g.clone(), c.flip(&n, &dec, &i));
        sb.finish_child(sb.mk_lam(jx_id, BinderInfo::Default, fin_p2n.clone(), body))
    };

    // reindexed-summand: fun jx => g (hcDecode n (flipIdx n i jx))  (= subsetSum
    // n g reindexed by σ := flipIdx n i).  This equals `g_dec ∘ (flipIdx n i)`
    // up to def-eq, so it is exactly `Fin.sum_reindex_involution`'s LHS summand.
    let reidx = |c: &FlipInvConsts, parent: &EnvDeclBuilder| -> Expr {
        let mut sb = EnvDeclBuilder::child_of(parent);
        let (jx_id, jx) = sb.fresh_local(fin_p2n.clone());
        let fidx = c.flipidx(&n, &i, &jx);
        let body = Expr::app(g.clone(), c.decode(&n, &fidx));
        sb.finish_child(sb.mk_lam(jx_id, BinderInfo::Default, fin_p2n.clone(), body))
    };

    // σ := flipIdx n i : Fin (2^n) → Fin (2^n).
    let sigma = Expr::apps(c.flip_idx.clone(), [n.clone(), i.clone()]);

    // ── leg1 : Fin.sum (2^n) flip_dec = Fin.sum (2^n) reidx  (Fin.sum_congr).
    // Per-index pointwise equality:
    //   g (hcFlip n (hcDecode n jx) i) = g (hcDecode n (flipIdx n i jx))
    //     := congrArg g (Eq.symm (hcFlip_decode_roundtrip n i jx)).
    let pw_congr = {
        let mut sb = EnvDeclBuilder::child_of(&b);
        let (jx_id, jx) = sb.fresh_local(fin_p2n.clone());
        let dec = c.decode(&n, &jx);
        let lhs_pt = c.flip(&n, &dec, &i); // hcFlip n (hcDecode n jx) i
        let fidx = c.flipidx(&n, &i, &jx);
        let rhs_pt = c.decode(&n, &fidx); // hcDecode n (flipIdx n i jx)
                                          // roundtrip n i jx : hcDecode n (flipIdx n i jx) = hcFlip n (hcDecode n jx) i
        let rt = Expr::apps(c.roundtrip.clone(), [n.clone(), i.clone(), jx.clone()]);
        // symm : hcFlip n (hcDecode n jx) i = hcDecode n (flipIdx n i jx)
        let hcp = c.hcpoint_of(&n);
        let rt_sym = Expr::apps(
            c.eq_symm.clone(),
            [hcp.clone(), rhs_pt.clone(), lhs_pt.clone(), rt],
        );
        // congrArg g (symm) : g (hcFlip …) = g (hcDecode (flipIdx …))
        let body = Expr::apps(
            c.congr_arg.clone(),
            [hcp, c.rat.clone(), lhs_pt, rhs_pt, g.clone(), rt_sym],
        );
        sb.finish_child(sb.mk_lam(jx_id, BinderInfo::Default, fin_p2n.clone(), body))
    };
    let leg1 = Expr::apps(
        c.fin_sum_congr.clone(),
        [p2n.clone(), flip_dec(c, &b), reidx(c, &b), pw_congr],
    );

    // ── leg2 : Fin.sum (2^n) reidx = Fin.sum (2^n) g_dec
    //   := Fin.sum_reindex_involution (2^n) σ hinv g_dec.
    //   `reidx jx ≡ g_dec (σ jx)` (def-eq), so the lemma's LHS summand `fun jx =>
    //   g_dec (σ jx)` is def-eq to `reidx`, and its RHS is `Fin.sum (2^n) g_dec`.
    let hinv = Expr::apps(
        Expr::const_(Name::from_string("BoolAnalysis.flipIdx_involutive"), vec![]),
        [n.clone(), i.clone()],
    ); // : ∀ jx, flipIdx n i (flipIdx n i jx) = jx  ≡  ∀ jx, σ (σ jx) = jx
    let leg2 = Expr::apps(
        c.reindex_invol.clone(),
        [p2n.clone(), sigma.clone(), hinv, g_dec(c, &b)],
    );

    // ── chain: Fin.sum flip_dec = Fin.sum reidx = Fin.sum g_dec.
    // The overall conclusion `subsetSum n (fun x => g (hcFlip n x i)) = subsetSum
    // n g` δ-unfolds to `Fin.sum (2^n) flip_dec = Fin.sum (2^n) g_dec`.
    let s_flip = Expr::apps(c.fin_sum.clone(), [p2n.clone(), flip_dec(c, &b)]);
    let s_reidx = Expr::apps(c.fin_sum.clone(), [p2n.clone(), reidx(c, &b)]);
    let s_gdec = Expr::apps(c.fin_sum.clone(), [p2n.clone(), g_dec(c, &b)]);
    let proof = Expr::apps(
        c.eq_trans.clone(),
        [c.rat.clone(), s_flip, s_reidx, s_gdec, leg1, leg2],
    );

    let e = b.mk_lam(i_id, BinderInfo::Default, c.fin_of(&n), proof);
    let e = b.mk_lam(g_id, BinderInfo::Default, g_ty, e);
    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e))
}

impl Environment {
    /// Register `Fin.sum_reindex_involution` — the general `Fin.sum`
    /// reindex-by-involution. STATEMENT only (see module docs): the constructive
    /// proof requires `Fin.sum` permutation theory the kernel lacks. This
    /// registers the **type signature** as a tracked frontier so the reduction
    /// in `subsetSum_flip_invariant` type-checks against it; it is intentionally
    /// NOT registered as an Axiom and NOT wired into any always-on aggregate.
    ///
    /// Returns the built type so callers can inspect / supply a proof. This
    /// function does NOT add a declaration — it is the single point that names
    /// the missing primitive's exact signature.
    pub(crate) fn flip_reindex_involution_signature(&self) -> Expr {
        let c = FlipInvConsts::new();
        reindex_involution_type(&c)
    }

    /// Register `BoolAnalysis.subsetSum_flip_invariant` against the
    /// `Fin.sum_reindex_involution` reindex leg. This succeeds (kernel-checked,
    /// constructive) ONLY when `Fin.sum_reindex_involution` is present as a
    /// constructive Theorem; otherwise it is a no-op (fail-closed — no Axiom
    /// introduced). Idempotent.
    pub(crate) fn register_subset_sum_flip_invariant(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.subsetSum_flip_invariant");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?;
        // KKL-finish idempotency: `init_boolean_analysis` may now register
        // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_subset_sum()?;
        self.register_hcflip_decode_roundtrip()?; // flipIdx + roundtrip
        self.register_flip_involution_proof()?; // flipIdx_involutive
        self.init_fin_sum()?; // Fin.sum_congr
                              // The reindex leg is now a constructive Theorem (the kkl keystone): build
                              // it so the fail-closed gate below opens.
        self.register_fin_sum_reindex_involution()?;

        // Fail-closed: only register if the reindex leg exists as a Theorem.
        if self
            .get_const(&Name::from_string("Fin.sum_reindex_involution"))
            .is_none()
        {
            return Ok(());
        }

        let c = FlipInvConsts::new();
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: flip_invariant_type(&c),
            value: flip_invariant_value(&c),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tc::TypeChecker;

    /// END-TO-END: with the REAL `Fin.sum_reindex_involution` keystone built
    /// (constructive, axiom-free), `subsetSum_flip_invariant` ACTIVATES and
    /// kernel-checks with an empty admitted-axiom closure — no injected axiom.
    #[test]
    fn test_subset_sum_flip_invariant_activates_axiom_free() {
        use crate::env::{ConstantKind, ProofQuality};
        let mut env = Environment::with_prelude();
        env.register_subset_sum_flip_invariant()
            .expect("register flip invariant (activates via real keystone)");

        // The keystone is present as a constructive, axiom-free Theorem.
        let key = Name::from_string("Fin.sum_reindex_involution");
        let kinfo = env.get_const(&key).expect("keystone registered");
        assert_eq!(kinfo.kind, ConstantKind::Theorem);
        let kdeps: Vec<String> = env
            .axiom_deps(&key)
            .expect("keystone deps")
            .iter()
            .map(|x| x.to_string())
            .collect();
        assert!(
            kdeps.is_empty(),
            "keystone must be axiom-free, got {kdeps:?}"
        );

        // The flip invariant is now registered (activated) and kernel-checks.
        let name = Name::from_string("BoolAnalysis.subsetSum_flip_invariant");
        let info = env
            .get_const(&name)
            .expect("subsetSum_flip_invariant must ACTIVATE once the keystone exists");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("activated flip invariant must kernel-check");
        let deps: Vec<String> = env
            .axiom_deps(&name)
            .expect("deps")
            .iter()
            .map(|x| x.to_string())
            .collect();
        assert!(
            deps.is_empty(),
            "subsetSum_flip_invariant must be axiom-free, got {deps:?}"
        );
        assert!(matches!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive)
        ));
    }

    /// The reindex-involution signature is a well-formed type (a `Prop`-valued
    /// Π over `m, σ, hinv, F`). This pins the EXACT frontier statement.
    #[test]
    fn test_reindex_involution_signature_is_well_typed() {
        let mut env = Environment::with_prelude();
        env.init_fin_sum().expect("init_fin_sum");
        let ty = env.flip_reindex_involution_signature();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let sort = tc
            .infer_type(&ty)
            .expect("reindex_involution signature must be a well-formed type");
        // Its type is a Sort (it is a Π ending in an Eq : Prop).
        let _ = sort;
    }

    // NOTE: a branch-era isolation test that injected `Fin.sum_reindex_involution`
    // as a test-only axiom was removed here: the keystone is now a real ported
    // Theorem and `subsetSum_flip_invariant`'s production registration + its
    // Constructive/empty-closure test below exercise the genuine path.
}

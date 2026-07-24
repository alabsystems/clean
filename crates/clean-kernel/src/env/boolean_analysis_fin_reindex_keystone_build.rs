// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Term builders for `Fin.sum_reindex_involution` (the keystone). `include!`d
// into `boolean_analysis_fin_reindex_keystone.rs`; shares `KeystoneConsts`.

// ===========================================================================
// Type: ∀ (m : Nat), M m
//   = ∀ m σ (∀x σ(σ x)=x) F, Σ_m (F∘σ) = Σ_m F
// ===========================================================================
fn keystone_type(c: &KeystoneConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let body = c.motive_body(&b, &m); // M m
    b.finish(b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), body))
}

/// The `Nat.rec` motive `M : Nat → Prop := fun m => M m`.
fn keystone_motive(c: &KeystoneConsts) -> Expr {
    let mut d = EnvDeclBuilder::new();
    let (m_id, m) = d.fresh_local(c.nat.clone());
    let body = c.motive_body(&d, &m);
    d.finish(d.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), body))
}

/// base : M 0 = ∀ σ hinv F, Σ_0 (F∘σ) = Σ_0 F.
///   Both `Σ_0` ι-reduce to `Rat.zero`; `Eq.refl Rat Rat.zero`.
fn keystone_base(c: &KeystoneConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let fin0 = c.fin_of(&zero);
    let sigma_ty = Expr::pi(BinderInfo::Default, fin0.clone(), fin0.clone());
    let (sigma_id, sigma) = b.fresh_local(sigma_ty.clone());
    let hinv_ty = {
        let mut e = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = e.fresh_local(fin0.clone());
        let ssx = Expr::app(sigma.clone(), Expr::app(sigma.clone(), x.clone()));
        let body = c.eq_fin(&zero, ssx, x.clone());
        e.finish_child(e.mk_pi(x_id, BinderInfo::Default, fin0.clone(), body))
    };
    let (hinv_id, _hinv) = b.fresh_local(hinv_ty.clone());
    let f_ty = c.fin_to_rat(&zero);
    let (f_id, _f) = b.fresh_local(f_ty.clone());
    // Eq.refl Rat Rat.zero : Σ_0 (F∘σ) = Σ_0 F   (both ι-reduce to Rat.zero)
    let refl = Expr::apps(c.eq_refl1.clone(), [c.rat.clone(), c.rat_zero.clone()]);
    let e = b.mk_lam(f_id, BinderInfo::Default, f_ty, refl);
    let e = b.mk_lam(hinv_id, BinderInfo::Default, hinv_ty, e);
    b.finish(b.mk_lam(sigma_id, BinderInfo::Default, sigma_ty, e))
}

include!("boolean_analysis_fin_reindex_keystone_build2.rs");

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive proof that the `Fin`-index transport `cast_fin` (an `Eq.ndrec`
//! over a `Nat` equality `e : b = a`, the `castP` used by `hcSumSplit`'s
//! off-diagonal split) is value-preserving:
//!
//! - `Fin.val_cast : ∀ (a b : Nat) (i : Fin b) (e : @Eq Nat b a),`
//!     `@Eq Nat (@Fin.val a (@Eq.ndrec Nat b (fun m => Fin m) i a e)) (@Fin.val b i)`
//!
//! The transport `cast_fin b a i e := @Eq.ndrec Nat b (fun m => Fin m) i a e`
//! carries `i : Fin b` to `Fin a` along `e`. `Fin.val` reads off the underlying
//! `Nat`, which the transport does not touch. The proof is the same `Eq.rec`-on-`e`
//! shape that `Fin.sum_cast` (rung 5) uses: the motive abstracts the *target* `a`,
//! and at `a = b`, `e = rfl` the `Eq.ndrec` collapses to the identity, so the
//! goal becomes `@Eq Nat (Fin.val b i) (Fin.val b i)`, closed by `Eq.refl`.
//!
//! This is the pointwise push-through the off-diagonal induction consumes to
//! turn `Fin.val (castP (castAdd ...))` (stuck at symbolic `n` over the
//! `2^n + 2^n = 2^(n+1)` transport) back into the bare `Fin.val` the rung-4
//! `testBit_*` bit lemmas accept.
//!
//! Kernel-checked, `ProofQuality::Constructive` (empty admitted-axiom closure):
//! the only leaves are `Eq.rec` / `Eq.ndrec` / `Eq.refl` / `Fin.val` built-ins.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

struct FinValCastConsts {
    nat: Expr,
    fin: Expr,
    fin_val: Expr,
    /// `Eq.{1}` over `Nat` (the equality of `Fin.val`s, a `Nat` equation).
    eq_nat: Expr,
    eq_refl_nat: Expr,
    /// `Eq.rec.{motive_u = 0, alpha_u = 1}` — motive lands in `Prop` (`Sort 0`),
    /// transporting over a `Nat` (`Sort 1`) equality.
    eq_rec: Expr,
    /// `Eq.ndrec.{motive_u = 1, alpha_u = 1}` — the `Fin`-transport (`fun m => Fin m`
    /// lands in `Type 0 = Sort 1`).
    eq_ndrec_fin: Expr,
}

impl FinValCastConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            fin_val: Expr::const_(Name::from_string("Fin.val"), vec![]),
            eq_nat: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_refl_nat: Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
            eq_rec: Expr::const_(Name::from_string("Eq.rec"), vec![Level::zero(), l1.clone()]),
            eq_ndrec_fin: Expr::const_(Name::from_string("Eq.ndrec"), vec![l1.clone(), l1]),
        }
    }

    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    /// `@Fin.val n i`.
    fn val(&self, n: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.fin_val.clone(), [n.clone(), i.clone()])
    }
    /// `@Eq Nat l r`.
    fn eq_nat_(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq_nat.clone(), [self.nat.clone(), l, r])
    }
    /// `@Eq.refl Nat x`.
    fn refl_nat(&self, x: Expr) -> Expr {
        Expr::apps(self.eq_refl_nat.clone(), [self.nat.clone(), x])
    }

    /// `@Eq.ndrec Nat b (fun m => Fin m) i a e : Fin a` — the `cast_fin`
    /// transport, identical to `boolean_analysis_hc_sum_split_proof::cast_fin`.
    fn cast_fin(&self, parent: &EnvDeclBuilder, b: &Expr, a: &Expr, i: &Expr, e: &Expr) -> Expr {
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(parent);
            let (m_id, m) = mb.fresh_local(self.nat.clone());
            let body = self.fin_of(&m);
            mb.finish_child(mb.mk_lam(m_id, BinderInfo::Default, self.nat.clone(), body))
        };
        Expr::apps(
            self.eq_ndrec_fin.clone(),
            [
                self.nat.clone(),
                b.clone(),
                motive,
                i.clone(),
                a.clone(),
                e.clone(),
            ],
        )
    }
}

/// `Fin.val_cast : ∀ (a b : Nat) (i : Fin b) (e : @Eq Nat b a),`
/// `  @Eq Nat (@Fin.val a (cast_fin b a i e)) (@Fin.val b i)`.
fn build_fin_val_cast(c: &FinValCastConsts) -> (Expr, Expr) {
    // concl(a, b, i, e) := Eq Nat (Fin.val a (cast_fin b a i e)) (Fin.val b i).
    let concl = |parent: &EnvDeclBuilder, a: &Expr, b: &Expr, i: &Expr, e: &Expr| -> Expr {
        let casted = c.cast_fin(parent, b, a, i, e);
        c.eq_nat_(c.val(a, &casted), c.val(b, i))
    };

    // Type: ∀ (a b : Nat) (i : Fin b) (e : Eq Nat b a), concl a b i e.
    let type_ = {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(c.nat.clone());
        let (bb_id, bb) = b.fresh_local(c.nat.clone());
        let (i_id, i) = b.fresh_local(c.fin_of(&bb));
        let e_ty = c.eq_nat_(bb.clone(), a.clone());
        let (e_id, e) = b.fresh_local(e_ty.clone());
        let body = concl(&b, &a, &bb, &i, &e);
        let r = b.mk_pi(e_id, BinderInfo::Default, e_ty, body);
        let r = b.mk_pi(i_id, BinderInfo::Default, c.fin_of(&bb), r);
        let r = b.mk_pi(bb_id, BinderInfo::Default, c.nat.clone(), r);
        let r = b.mk_pi(a_id, BinderInfo::Default, c.nat.clone(), r);
        b.finish(r)
    };

    // Value: fun (a b : Nat) (i : Fin b) (e : Eq Nat b a) =>
    //   @Eq.rec Nat b
    //     (motive := fun (a' : Nat) (e' : Eq Nat b a') =>
    //        Eq Nat (Fin.val a' (cast_fin b a' i e')) (Fin.val b i))
    //     (base := @Eq.refl Nat (Fin.val b i))
    //     a e
    //
    // The motive abstracts the TARGET `a`, leaving `b`/`i` fixed; `Eq.rec` on
    // `e : b = a`. At `a = b, e = rfl`, `cast_fin b b i rfl` ι-reduces to `i`
    // (Eq.ndrec at refl is the identity transport), so the motive at `(b, rfl)`
    // is `Eq Nat (Fin.val b i) (Fin.val b i)`, inhabited by the `Eq.refl` base.
    let value = {
        let mut vb = EnvDeclBuilder::new();
        let (a_id, a) = vb.fresh_local(c.nat.clone());
        let (bb_id, bb) = vb.fresh_local(c.nat.clone());
        let (i_id, i) = vb.fresh_local(c.fin_of(&bb));
        let e_ty = c.eq_nat_(bb.clone(), a.clone());
        let (e_id, e) = vb.fresh_local(e_ty.clone());

        // motive : (a' : Nat) → (e' : Eq Nat b a') → Prop.
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&vb);
            let (ap_id, ap) = mb.fresh_local(c.nat.clone());
            let ep_ty = c.eq_nat_(bb.clone(), ap.clone());
            let (ep_id, ep) = mb.fresh_local(ep_ty.clone());
            let body = concl(&mb, &ap, &bb, &i, &ep);
            let lam = mb.mk_lam(ep_id, BinderInfo::Default, ep_ty, body);
            let lam = mb.mk_lam(ap_id, BinderInfo::Default, c.nat.clone(), lam);
            mb.finish_child(lam)
        };

        // base : motive b rfl = Eq Nat (Fin.val b (cast_fin b b i rfl)) (Fin.val b i)
        //   cast_fin b b i rfl ≡ i, so this is Eq Nat (Fin.val b i) (Fin.val b i);
        //   @Eq.refl Nat (Fin.val b i) inhabits it.
        let base = c.refl_nat(c.val(&bb, &i));

        // @Eq.rec Nat b motive base a e : motive a e.
        let rec_app = Expr::apps(
            c.eq_rec.clone(),
            [
                c.nat.clone(),
                bb.clone(),
                motive,
                base,
                a.clone(),
                e.clone(),
            ],
        );
        let lam = vb.mk_lam(e_id, BinderInfo::Default, e_ty, rec_app);
        let lam = vb.mk_lam(i_id, BinderInfo::Default, c.fin_of(&bb), lam);
        let lam = vb.mk_lam(bb_id, BinderInfo::Default, c.nat.clone(), lam);
        let lam = vb.mk_lam(a_id, BinderInfo::Default, c.nat.clone(), lam);
        vb.finish(lam)
    };

    (type_, value)
}

impl Environment {
    /// Register `Fin.val_cast` (B1) as a kernel-checked, constructive theorem.
    /// Idempotent.
    pub(crate) fn register_fin_val_cast_theorem(&mut self) -> Result<(), EnvError> {
        self.init_eq()?;
        self.init_fin_sum()?; // brings `Fin`, `Fin.val`.

        if self.get_const(&Name::from_string("Fin.val_cast")).is_some() {
            return Ok(());
        }
        let c = FinValCastConsts::new();
        let (type_, value) = build_fin_val_cast(&c);
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("Fin.val_cast"),
            level_params: vec![],
            type_,
            value,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn make_env() -> Environment {
        let mut env = Environment::new();
        env.register_fin_val_cast_theorem()
            .expect("register_fin_val_cast_theorem");
        env
    }

    #[test]
    fn test_fin_val_cast_is_constructive_theorem() {
        let env = make_env();
        let name = "Fin.val_cast";
        let info = env
            .get_const(&Name::from_string(name))
            .expect("Fin.val_cast should be registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be a Theorem");
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("Fin.val_cast proof must check: {e:?}"));
        assert_eq!(
            env.proof_quality(&Name::from_string(name)),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
        assert!(
            env.axiom_deps(&Name::from_string(name))
                .expect("deps")
                .is_empty(),
            "axiom closure must be empty"
        );
    }
}

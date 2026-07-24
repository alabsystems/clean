// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Constructive `Fin.lastCases` — the dependent last-element case eliminator for
//! the FAITHFUL `Fin` carrier (`Fin.mk : {n} → (val : Nat) → (isLt : Nat.lt val n)
//! → Fin n`). A real kernel-checked term (NO `sorry`, NO axiom).
//!
//! ```text
//! Fin.lastCases :
//!   {n : Nat} → {motive : Fin (Nat.succ n) → Sort u}
//!   → (last : motive (Fin.last n))
//!   → (cast : (i : Fin n) → motive (Fin.castSucc n i))
//!   → (i : Fin (Nat.succ n)) → motive i
//! ```
//!
//! Every `i : Fin (Nat.succ n)` is either the top element `Fin.last n`
//! (when `Fin.val i = n`) or the image `Fin.castSucc n i'` of some `i' : Fin n`
//! (when `Fin.val i < n`). With the faithful carrier these two cases are decided
//! computably and the index is reconstructed, so the eliminator is a genuine
//! definition rather than an axiom.
//!
//! # Construction
//!
//! Dispatch on `Nat.decEq (Fin.val i) n` via `Decidable.rec`:
//!
//! - **`isTrue (heq : Fin.val i = n)`** — then `i ≡ Fin.last n`. We have
//!   `Fin.val (Fin.last n) ≡ n` by ι, so `Eq.symm heq : Fin.val (Fin.last n)
//!   = Fin.val i` (up to the definitional `Fin.val (Fin.last n) ≡ n`).
//!   `Fin.eq_of_val_eq (Nat.succ n) (Fin.last n) i …` gives `e : Fin.last n = i`,
//!   and `Eq.ndrec last e : motive i`.
//! - **`isFalse (hne : Fin.val i = n → False)`** — then `Fin.val i < n`. From
//!   `Fin.isLt (Nat.succ n) i : Nat.lt (Fin.val i) (Nat.succ n) ≡
//!   Nat.le (Nat.succ (Fin.val i)) (Nat.succ n)` and
//!   `Nat.le_of_succ_le_succ` we get `hle : Nat.le (Fin.val i) n`; with `hne`,
//!   `Nat.lt_of_le_of_ne` yields `hlt : Nat.lt (Fin.val i) n`. Build
//!   `i' := Fin.mk n (Fin.val i) hlt : Fin n`; since
//!   `Fin.val (Fin.castSucc n i') ≡ Fin.val i' ≡ Fin.val i`,
//!   `Fin.eq_of_val_eq` gives `e : Fin.castSucc n i' = i`, and
//!   `Eq.ndrec (cast i') e : motive i`.
//!
//! Both `Eq.ndrec` transports carry the dependent motive `motive`, so
//! `Fin.lastCases` is a full dependent eliminator.
//!
//! # Axiom closure
//!
//! Mentions only generated recursors / reducible definitions / axiom-free
//! Theorems: `Fin`/`Fin.mk`/`Fin.val`/`Fin.isLt`/`Fin.last`/`Fin.castSucc`/
//! `Fin.eq_of_val_eq`, `Nat`/`Nat.lt`/`Nat.le`/`Nat.succ`/`Nat.decEq`/
//! `Nat.le_of_succ_le_succ`/`Nat.lt_of_le_of_ne`, `Eq`/`Eq.ndrec`/`Eq.symm`/
//! `Eq.refl`, `Decidable`(`.rec`). So `env.axiom_deps("Fin.lastCases")` is empty.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register the constructive `Fin.lastCases` dependent eliminator.
    /// Idempotent; axiom-free.
    ///
    /// REQUIRES: `Fin` (faithful carrier) + `Fin.val`/`Fin.isLt`/`Fin.last`/
    ///           `Fin.castSucc`/`Fin.eq_of_val_eq`, `Nat`/`Nat.lt`/`Nat.le`/
    ///           `Nat.decEq`/`Nat.le_of_succ_le_succ`/`Nat.lt_of_le_of_ne`,
    ///           `Eq`(+`Eq.ndrec`/`Eq.symm`/`Eq.refl`), `Decidable`(+rec).
    pub(crate) fn register_fin_last_cases(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("Fin.lastCases"))
            .is_some_and(|c| c.kind == super::types::ConstantKind::Definition)
        {
            return Ok(());
        }

        // Dependencies: Fin.sum init provides Fin.last / Fin.castSucc.
        self.init_eq()?;
        self.init_nat()?;
        self.init_fin()?;
        self.init_lt()?;
        self.init_decidable()?;
        self.register_nat_dec_eq_proof()?;
        self.register_fin_dec_eq_proof()?; // Fin.eq_of_val_eq
        self.init_nat_totality_proofs()?; // Nat.lt_of_le_of_ne (axiom-free thm)
                                          // Register `Nat.le_of_succ_le_succ` as an axiom-free Theorem DIRECTLY,
                                          // not via `init_nat_succ_lt` — the latter also admits `Nat.lt_succ_iff`
                                          // as a fresh TCB axiom, which would re-grow the trusted base we are
                                          // shrinking. `register_nat_le_of_succ_le_succ_theorem` is self-contained
                                          // (kernel-checked, empty axiom closure).
        self.register_nat_le_of_succ_le_succ_theorem()?;
        // `Fin.last` / `Fin.castSucc` are registered by the LIGHTWEIGHT ensures
        // (independent of `Fin.sum`), NOT via `init_fin_sum`. This matters because
        // `init_fin_sum` itself now pulls in the `Fin.sum_single` proof, which
        // depends on `Fin.lastCases` — calling `init_fin_sum` here would create a
        // registration cycle. The ensures are idempotent.
        {
            let c = super::nn_verify_fin_sum::FinSumConsts::new();
            self.ensure_fin_cast_succ(&c)?;
            self.ensure_fin_last(&c)?;
        }

        // ----- shared constants -----
        let u = Name::from_string("u");
        let lu = Level::param(u.clone());
        let l0 = Level::zero();
        let l1 = Level::succ(l0.clone());

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_deceq = Expr::const_(Name::from_string("Nat.decEq"), vec![]);
        let nat_le_of_ss = Expr::const_(Name::from_string("Nat.le_of_succ_le_succ"), vec![]);
        let nat_lt_of_le_ne = Expr::const_(Name::from_string("Nat.lt_of_le_of_ne"), vec![]);

        let fin_c = Expr::const_(Name::from_string("Fin"), vec![]);
        let fin_mk = Expr::const_(Name::from_string("Fin.mk"), vec![]);
        let fin_val = Expr::const_(Name::from_string("Fin.val"), vec![]);
        let fin_islt = Expr::const_(Name::from_string("Fin.isLt"), vec![]);
        let fin_last = Expr::const_(Name::from_string("Fin.last"), vec![]);
        let fin_cast = Expr::const_(Name::from_string("Fin.castSucc"), vec![]);
        let fin_eq_of_val = Expr::const_(Name::from_string("Fin.eq_of_val_eq"), vec![]);

        // Eq.ndrec.{u, 1}: transporting along an `Eq (Fin (succ n)) a b` (Fin lives
        // in Sort 1 = Type 0, so the equality-index universe is 1); the motive
        // lands in `Sort u`.
        let eq_ndrec = Expr::const_(Name::from_string("Eq.ndrec"), vec![lu.clone(), l1.clone()]);
        let eq_symm = Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]);
        let eq1 = Expr::const_(Name::from_string("Eq"), vec![l1.clone()]);

        let dec = Expr::const_(Name::from_string("Decidable"), vec![]);
        // Decidable.rec eliminating into Sort u (the dispatch's motive returns
        // `motive i : Sort u`).
        let dec_rec = Expr::const_(Name::from_string("Decidable.rec"), vec![lu.clone()]);
        let eq_nat = Expr::const_(Name::from_string("Eq"), vec![l1.clone()]);

        // helpers
        let fin_n = |n: Expr| Expr::app(fin_c.clone(), n);
        let succ = |n: Expr| Expr::app(nat_succ.clone(), n);
        let val = |n: Expr, x: Expr| Expr::apps(fin_val.clone(), [n, x]);
        let eq_n = |l: Expr, r: Expr| Expr::apps(eq_nat.clone(), [nat.clone(), l, r]);

        let sort_u = Expr::sort(lu.clone());

        // ───────────────────────── Type ─────────────────────────
        // {n : Nat} → {motive : Fin (succ n) → Sort u}
        //   → motive (Fin.last n)
        //   → ((i : Fin n) → motive (Fin.castSucc n i))
        //   → (i : Fin (succ n)) → motive i
        let lc_type = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let succ_n = succ(n.clone());
            let fin_succ_n = fin_n(succ_n.clone());
            let motive_ty = Expr::pi(BinderInfo::Default, fin_succ_n.clone(), sort_u.clone());
            let (m_id, motive) = b.fresh_local(motive_ty.clone());

            // last : motive (Fin.last n)
            let last_n = Expr::app(fin_last.clone(), n.clone());
            let last_ty = Expr::app(motive.clone(), last_n);
            let (last_id, _last) = b.fresh_local(last_ty.clone());

            // cast : (i : Fin n) → motive (Fin.castSucc n i)
            let cast_ty = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (i_id, i) = c.fresh_local(fin_n(n.clone()));
                let cast_i = Expr::apps(fin_cast.clone(), [n.clone(), i]);
                let body = Expr::app(motive.clone(), cast_i);
                c.finish_child(c.mk_pi(i_id, BinderInfo::Default, fin_n(n.clone()), body))
            };
            let (cast_id, _cast) = b.fresh_local(cast_ty.clone());

            // (i : Fin (succ n)) → motive i
            let (i_id, i) = b.fresh_local(fin_succ_n.clone());
            let concl = Expr::app(motive.clone(), i);

            let r = b.mk_pi(i_id, BinderInfo::Default, fin_succ_n, concl);
            let r = b.mk_pi(cast_id, BinderInfo::Default, cast_ty, r);
            let r = b.mk_pi(last_id, BinderInfo::Default, last_ty, r);
            let r = b.mk_pi(m_id, BinderInfo::Implicit, motive_ty, r);
            let r = b.mk_pi(n_id, BinderInfo::Implicit, nat.clone(), r);
            b.finish(r)
        };

        // ───────────────────────── Value ─────────────────────────
        let lc_value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let succ_n = succ(n.clone());
            let fin_succ_n = fin_n(succ_n.clone());
            let motive_ty = Expr::pi(BinderInfo::Default, fin_succ_n.clone(), sort_u.clone());
            let (m_id, motive) = b.fresh_local(motive_ty.clone());

            let last_n = Expr::app(fin_last.clone(), n.clone());
            let last_ty = Expr::app(motive.clone(), last_n.clone());
            let (last_id, last) = b.fresh_local(last_ty.clone());

            let cast_ty = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (i_id, i) = c.fresh_local(fin_n(n.clone()));
                let cast_i = Expr::apps(fin_cast.clone(), [n.clone(), i]);
                let body = Expr::app(motive.clone(), cast_i);
                c.finish_child(c.mk_pi(i_id, BinderInfo::Default, fin_n(n.clone()), body))
            };
            let (cast_id, cast) = b.fresh_local(cast_ty.clone());

            let (i_id, i) = b.fresh_local(fin_succ_n.clone());

            // val_i := Fin.val (succ n) i
            let val_i = val(succ_n.clone(), i.clone());
            // prop := Eq Nat val_i n
            let prop = eq_n(val_i.clone(), n.clone());

            // dmotive : (Decidable prop) → Sort u
            //   := fun (_ : Decidable prop) => motive i
            let dmotive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let dec_prop = Expr::app(dec.clone(), prop.clone());
                let (d_id, _d) = c.fresh_local(dec_prop.clone());
                let body = Expr::app(motive.clone(), i.clone());
                c.finish_child(c.mk_lam(d_id, BinderInfo::Default, dec_prop, body))
            };

            // isFalse minor: fun (hne : prop → False) => …  : motive i
            //   build i' = Fin.mk n val_i hlt, then transport `cast i'` along
            //   `Fin.castSucc n i' = i`.
            let is_false_min = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let false_c = Expr::const_(Name::from_string("False"), vec![]);
                let not_p = Expr::pi(BinderInfo::Default, prop.clone(), false_c);
                let (hne_id, hne) = c.fresh_local(not_p.clone());

                // hisLt : Fin.isLt (succ n) i : Nat.lt val_i (succ n)
                //        ≡ Nat.le (succ val_i) (succ n)
                let hislt = Expr::apps(fin_islt.clone(), [succ_n.clone(), i.clone()]);
                // hle : Nat.le_of_succ_le_succ val_i n hislt : Nat.le val_i n
                let hle = Expr::apps(nat_le_of_ss.clone(), [val_i.clone(), n.clone(), hislt]);
                // hlt : Nat.lt_of_le_of_ne val_i n hle hne : Nat.lt val_i n
                //   (LE.le / LT.lt typeclass forms in the lemma type are defeq to
                //    the bare Nat.le / Nat.lt; hne : prop → False matches Eq → False)
                let hlt = Expr::apps(
                    nat_lt_of_le_ne.clone(),
                    [val_i.clone(), n.clone(), hle, hne.clone()],
                );
                // i' := Fin.mk n val_i hlt : Fin n
                let i_prime = Expr::apps(fin_mk.clone(), [n.clone(), val_i.clone(), hlt]);
                // cast i' : motive (Fin.castSucc n i')
                let cast_ip = Expr::app(cast.clone(), i_prime.clone());
                // cs := Fin.castSucc n i' : Fin (succ n)
                let cs = Expr::apps(fin_cast.clone(), [n.clone(), i_prime.clone()]);

                // hval : Fin.val (succ n) cs = Fin.val (succ n) i
                //   Fin.val (succ n) (Fin.castSucc n i') ≡ Fin.val n i' ≡ val_i,
                //   and Fin.val (succ n) i ≡ val_i, so this is Eq.refl Nat val_i —
                //   well-typed up to the kernel's defeq folding of both sides.
                let eq_refl_nat = Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]);
                let hval = Expr::apps(eq_refl_nat, [nat.clone(), val_i.clone()]);
                // e : Fin.castSucc n i' = i
                //   Fin.eq_of_val_eq (succ n) cs i hval
                let e = Expr::apps(
                    fin_eq_of_val.clone(),
                    [succ_n.clone(), cs.clone(), i.clone(), hval],
                );

                // @Eq.ndrec.{u,1} (Fin (succ n)) cs motive (cast i') i e : motive i
                let transported = Expr::apps(
                    eq_ndrec.clone(),
                    [
                        fin_succ_n.clone(),
                        cs.clone(),
                        motive.clone(),
                        cast_ip,
                        i.clone(),
                        e,
                    ],
                );
                c.finish_child(c.mk_lam(hne_id, BinderInfo::Default, not_p, transported))
            };

            // isTrue minor: fun (heq : prop) => …  : motive i
            //   transport `last` along `Fin.last n = i`.
            let is_true_min = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (heq_id, heq) = c.fresh_local(prop.clone());

                // hval : Fin.val (succ n) (Fin.last n) = Fin.val (succ n) i
                //   Fin.val (succ n) (Fin.last n) ≡ n,  Fin.val (succ n) i ≡ val_i,
                //   so goal ≡ Eq Nat n val_i, which is Eq.symm heq (heq : val_i = n).
                let hval = Expr::apps(
                    eq_symm.clone(),
                    [nat.clone(), val_i.clone(), n.clone(), heq.clone()],
                );

                // e : Fin.last n = i := Fin.eq_of_val_eq (succ n) (Fin.last n) i hval
                let e = Expr::apps(
                    fin_eq_of_val.clone(),
                    [succ_n.clone(), last_n.clone(), i.clone(), hval],
                );
                // @Eq.ndrec.{u,1} (Fin (succ n)) (Fin.last n) motive last i e : motive i
                let transported = Expr::apps(
                    eq_ndrec.clone(),
                    [
                        fin_succ_n.clone(),
                        last_n.clone(),
                        motive.clone(),
                        last.clone(),
                        i.clone(),
                        e,
                    ],
                );
                c.finish_child(c.mk_lam(heq_id, BinderInfo::Default, prop.clone(), transported))
            };

            // discriminant := Nat.decEq val_i n : Decidable (Eq Nat val_i n)
            let discr = Expr::apps(nat_deceq.clone(), [val_i.clone(), n.clone()]);
            // @Decidable.rec.{u} prop dmotive isFalse_min isTrue_min discriminant
            let rec_app = Expr::apps(
                dec_rec.clone(),
                [prop.clone(), dmotive, is_false_min, is_true_min, discr],
            );

            let r = b.mk_lam(i_id, BinderInfo::Default, fin_succ_n, rec_app);
            let r = b.mk_lam(cast_id, BinderInfo::Default, cast_ty, r);
            let r = b.mk_lam(last_id, BinderInfo::Default, last_ty, r);
            let r = b.mk_lam(m_id, BinderInfo::Implicit, motive_ty, r);
            let r = b.mk_lam(n_id, BinderInfo::Implicit, nat.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Fin.lastCases"),
            level_params: vec![u],
            type_: lc_type,
            value: lc_value,
            is_reducible: true,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{ConstantKind, ProofQuality};
    use crate::tc::TypeChecker;

    #[test]
    fn test_fin_last_cases_type_checks_and_axiom_free() {
        let mut env = Environment::with_prelude();
        env.register_fin_last_cases().expect("register");
        env.register_fin_last_cases().expect("idempotent");

        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(
                Name::from_string("Fin.lastCases"),
                vec![Level::param(Name::from_string("u"))],
            ))
            .expect("Fin.lastCases should type-check");

        let kind = env
            .get_const(&Name::from_string("Fin.lastCases"))
            .expect("registered")
            .kind;
        assert_eq!(
            kind,
            ConstantKind::Definition,
            "Fin.lastCases must be a Definition"
        );

        let deps = env
            .axiom_deps(&Name::from_string("Fin.lastCases"))
            .expect("registered");
        let names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            names.is_empty(),
            "Fin.lastCases must be axiom-free, got {names:?}"
        );

        assert!(
            matches!(
                env.proof_quality(&Name::from_string("Fin.lastCases")),
                Some(ProofQuality::NotATheorem)
            ),
            "Fin.lastCases is a Definition (NotATheorem for proof-quality)"
        );
    }
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL pre-build — K0 layer: the `Fin.prod` level-weight carrier.
//!
//! The KKL spectral weight `ρ^(2·|S|)` over a subset `S ⊆ [n]`, carried as a
//! coordinatewise `Fin.prod` (one factor `ρ·ρ` per element of `S`, `1`
//! otherwise) so it avoids any `popcount`/`powNat` round-trip in the inner
//! Fourier bookkeeping:
//!
//! ```text
//! BoolAnalysis.levelWt (ρ : Rat) (n : Nat) (S : HCPoint n) : Rat :=
//!   Fin.prod n (fun i => @Bool.rec (fun _ => Rat) Rat.one (Rat.mul ρ ρ) (S i))
//! ```
//!
//! (`Bool.rec`'s `false` branch is `1`, its `true` branch is `ρ·ρ`, so the
//! factor is `ρ·ρ` exactly on the coordinates `S` selects.)
//!
//! Registered as a reducible `Declaration::Definition`; the closure bottoms out
//! in reducible `Fin.prod` / `Bool.rec` / `Rat.mul`, all admitted-axiom-free, so
//! any theorem stated over it stays `Constructive`. Idempotent.
//!
//! The `Rat.powNat (ρ·ρ) |S|` relation (folding the `Fin.prod` into a
//! popcount-indexed power) needs a `Nat`-valued popcount carrier and a `Nat.rec`
//! induction; it is deferred to the K0/K1 assembly run (see the module residual
//! note in the KKL handoff).

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// `BoolAnalysis.levelWt (ρ : Rat) (n : Nat) (S : HCPoint n) : Rat`
    /// `:= Fin.prod n (fun i => if S i then ρ·ρ else 1)`.
    ///
    /// The `Fin.prod` level-weight carrier (`ρ^(2|S|)` without popcount/powNat).
    /// Reducible. Idempotent.
    pub(crate) fn register_level_wt(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.levelWt");
        if self
            .get_const(&name)
            .is_some_and(|info| matches!(info.kind, crate::env::types::ConstantKind::Definition))
        {
            return Ok(());
        }
        self.init_boolean_analysis_foundations()?; // HCPoint, Fin.prod

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let bool_ = Expr::const_(Name::from_string("Bool"), vec![]);
        let fin = Expr::const_(Name::from_string("Fin"), vec![]);
        let fin_prod = Expr::const_(Name::from_string("Fin.prod"), vec![]);
        let rat_mul = Expr::const_(Name::from_string("Rat.mul"), vec![]);
        let rat_one = Expr::const_(Name::from_string("Rat.one"), vec![]);
        let bool_rec = Expr::const_(
            Name::from_string("Bool.rec"),
            vec![Level::succ(Level::zero())],
        );
        let hcpoint = Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]);

        // motive: fun (_ : Bool) => Rat
        let bool_to_rat_motive = Expr::lam(BinderInfo::Default, bool_.clone(), rat.clone());
        let hcpoint_of = |n: &Expr| Expr::app(hcpoint.clone(), n.clone());

        // Type: (ρ : Rat) -> (n : Nat) -> HCPoint n -> Rat
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (rho_id, _rho) = b.fresh_local(rat.clone());
            let (n_id, n) = b.fresh_local(nat.clone());
            let s_type = hcpoint_of(&n);
            let (s_id, _s) = b.fresh_local(s_type.clone());
            let r = b.mk_pi(s_id, BinderInfo::Default, s_type, rat.clone());
            let r = b.mk_pi(n_id, BinderInfo::Default, nat.clone(), r);
            let r = b.mk_pi(rho_id, BinderInfo::Default, rat.clone(), r);
            b.finish(r)
        };

        // Value: fun (ρ) (n) (S) =>
        //   Fin.prod n (fun (i : Fin n) =>
        //     @Bool.rec (fun _ => Rat) Rat.one (Rat.mul ρ ρ) (S i))
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (rho_id, rho) = b.fresh_local(rat.clone());
            let (n_id, n) = b.fresh_local(nat.clone());
            let s_type = hcpoint_of(&n);
            let (s_id, s) = b.fresh_local(s_type.clone());

            let factor = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let fin_n = Expr::app(fin.clone(), n.clone());
                let (i_id, i) = ch.fresh_local(fin_n.clone());
                let s_i = Expr::app(s.clone(), i);
                let rho_sq = Expr::apps(rat_mul.clone(), [rho.clone(), rho.clone()]);
                // @Bool.rec motive (false→1) (true→ρ·ρ) (S i)
                let body = Expr::apps(
                    bool_rec.clone(),
                    [bool_to_rat_motive.clone(), rat_one.clone(), rho_sq, s_i],
                );
                ch.finish_child(ch.mk_lam(i_id, BinderInfo::Default, fin_n, body))
            };
            let body = Expr::apps(fin_prod.clone(), [n.clone(), factor]);
            let r = b.mk_lam(s_id, BinderInfo::Default, s_type, body);
            let r = b.mk_lam(n_id, BinderInfo::Default, nat.clone(), r);
            let r = b.mk_lam(rho_id, BinderInfo::Default, rat.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::tc::TypeChecker;

    #[test]
    fn test_level_wt_is_reducible_definition() {
        let mut env = Environment::new();
        env.init_boolean_analysis().expect("init_boolean_analysis");
        env.register_level_wt().expect("register_level_wt");
        let info = env
            .get_const(&Name::from_string("BoolAnalysis.levelWt"))
            .expect("registered");
        assert_eq!(info.kind, ConstantKind::Definition);
        let value = info.value.clone().expect("value present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("levelWt value must check against its type");
    }

    #[test]
    fn test_level_wt_idempotent() {
        let mut env = Environment::new();
        env.init_boolean_analysis().expect("init_boolean_analysis");
        env.register_level_wt().expect("first");
        env.register_level_wt().expect("second (idempotent)");
    }
}

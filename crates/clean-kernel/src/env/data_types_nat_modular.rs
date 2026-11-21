// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Checked modular identities over the actual default prelude remainder body.
//! Import mode leaves canonical imported definitions and proofs to their owner.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::{BinderInfo, Expr, Level, Name};

fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}
fn call(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(c(name), args)
}
fn nat() -> Expr {
    c("Nat")
}
fn zero() -> Expr {
    c("Nat.zero")
}
fn succ(x: Expr) -> Expr {
    Expr::app(c("Nat.succ"), x)
}
fn eq(lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [nat(), lhs, rhs],
    )
}
fn rec_prop(motive: Expr, base: Expr, step: Expr, major: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
        [motive, base, step, major],
    )
}
fn remainder(a: Expr, n: Expr) -> Expr {
    call("Nat.mod", [a, n])
}
fn mod_mod() -> Declaration {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(nat());
    let (n_id, n) = b.fresh_local(nat());
    let r = remainder(a.clone(), n.clone());
    let type_ = eq(remainder(r.clone(), n.clone()), r);
    let mut mb = EnvDeclBuilder::child_of(&b);
    let (m_id, m) = mb.fresh_local(nat());
    let r = remainder(a.clone(), m.clone());
    let out = eq(remainder(r.clone(), m), r);
    let out = mb.mk_lam(m_id, BinderInfo::Default, nat(), out);
    let motive = mb.finish_child(out);
    let base = call("Nat.divmodAux.mod_zero", [remainder(a.clone(), zero())]);
    let mut sb = EnvDeclBuilder::child_of(&b);
    let (m_id, m) = sb.fresh_local(nat());
    let ih_ty = Expr::app(motive.clone(), m.clone());
    let (ih_id, _) = sb.fresh_local(ih_ty.clone());
    let positive = call(
        "Nat.succ_le_succ",
        [zero(), m.clone(), call("Nat.zero_le", [m.clone()])],
    );
    let modulus = succ(m);
    let r = remainder(a.clone(), modulus.clone());
    let bound = call("Nat.mod_lt", [a.clone(), modulus.clone(), positive]);
    let proof = call("Nat.mod_eq_of_lt", [r, modulus, bound]);
    let out = sb.mk_lam(ih_id, BinderInfo::Default, ih_ty, proof);
    let out = sb.mk_lam(m_id, BinderInfo::Default, nat(), out);
    let step = sb.finish_child(out);
    let value = rec_prop(motive, base, step, n);
    let type_ = b.mk_pi(n_id, BinderInfo::Default, nat(), type_);
    let type_ = b.mk_pi(a_id, BinderInfo::Default, nat(), type_);
    let value = b.mk_lam(n_id, BinderInfo::Default, nat(), value);
    let value = b.mk_lam(a_id, BinderInfo::Default, nat(), value);
    Declaration::Theorem {
        name: Name::from_string("Nat.mod_mod"),
        level_params: vec![],
        type_: b.finish(type_),
        value: b.finish(value),
    }
}

impl Environment {
    pub(crate) fn register_nat_modular_identities(&mut self) -> Result<(), EnvError> {
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        self.init_nat_div_mod_lemmas()?;
        // Reuse the existing checked proof rather than competing for its name.
        self.init_nat_floor_order_lemmas()?;
        self.ensure_exact_checked_decl(mod_mod())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::reference::ReferenceKernel;

    #[test]
    fn modular_identities_are_checked_axiom_free_and_idempotent() {
        let mut env = Environment::with_prelude();
        for name in ["Nat.mod_eq_of_lt", "Nat.mod_mod"] {
            let name = Name::from_string(name);
            assert!(env
                .get_const(&name)
                .expect("checked theorem")
                .value
                .is_some());
            assert!(env.axiom_deps(&name).expect("closure").is_empty());
        }
        let before = (env.num_constants(), env.num_instances());
        env.register_nat_modular_identities()
            .expect("repeat initialization");
        assert_eq!((env.num_constants(), env.num_instances()), before);
    }

    #[test]
    fn modular_identities_preserve_import_ownership() {
        let mut env = Environment::try_with_prelude_for_import().expect("import prelude");
        env.register_nat_modular_identities()
            .expect("import suppression");
        for name in ["Nat.mod_eq_of_lt", "Nat.mod_mod"] {
            assert!(env.get_const(&Name::from_string(name)).is_none(), "{name}");
        }
    }

    #[test]
    fn reference_replays_generic_modular_proofs_and_refuses_changed_remainder() {
        let env = Environment::with_prelude();
        let mut reference = ReferenceKernel::new(env).expect("reference theory");
        for name in ["Nat.mod_eq_of_lt", "Nat.mod_mod"] {
            let type_ = reference
                .environment()
                .get_const(&Name::from_string(name))
                .expect("actual theorem")
                .type_
                .clone();
            let alias = Name::from_string(&format!("modular_reference_{name}"));
            reference
                .add_checked(Declaration::Theorem {
                    name: alias.clone(),
                    level_params: vec![],
                    type_,
                    value: c(name),
                })
                .expect("replay the actual universal theorem and its closure");
            assert!(reference
                .environment()
                .axiom_deps(&alias)
                .expect("closure")
                .is_empty());
        }
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(nat());
        let (n_id, n) = b.fresh_local(nat());
        let r = remainder(a, n.clone());
        let changed = eq(remainder(r.clone(), n), succ(r));
        let changed = b.mk_pi(n_id, BinderInfo::Default, nat(), changed);
        let changed = b.mk_pi(a_id, BinderInfo::Default, nat(), changed);
        let before = reference.environment().num_constants();
        assert!(
            reference
                .add_checked(Declaration::Theorem {
                    name: Name::from_string("modular_changed_remainder"),
                    level_params: vec![],
                    type_: b.finish(changed),
                    value: c("Nat.mod_mod"),
                })
                .is_err(),
            "the original proof cannot add one to every remainder"
        );
        assert_eq!(reference.environment().num_constants(), before);
    }
}

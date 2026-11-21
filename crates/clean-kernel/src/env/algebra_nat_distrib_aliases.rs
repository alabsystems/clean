// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Canonical Lean API names for the existing constructive distributivity proofs.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::{BinderInfo, Expr, Level, Name};

fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}
fn add(a: Expr, b: Expr) -> Expr {
    Expr::apps(c("Nat.add"), [a, b])
}
fn mul(a: Expr, b: Expr) -> Expr {
    Expr::apps(c("Nat.mul"), [a, b])
}

fn declaration(left: bool, changed: bool) -> Declaration {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c("Nat"));
    let (b_id, bb) = b.fresh_local(c("Nat"));
    let (d_id, d) = b.fresh_local(c("Nat"));
    let (name, original, lhs, rhs) = if left {
        (
            "Nat.mul_add",
            "Nat.left_distrib",
            mul(a.clone(), add(bb.clone(), d.clone())),
            add(mul(a.clone(), bb), mul(a, d)),
        )
    } else {
        (
            "Nat.add_mul",
            "Nat.right_distrib",
            mul(add(a.clone(), bb.clone()), d.clone()),
            add(mul(a, d.clone()), mul(bb, d)),
        )
    };
    let rhs = if changed {
        Expr::app(c("Nat.succ"), rhs)
    } else {
        rhs
    };
    let type_ = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [c("Nat"), lhs, rhs],
    );
    let type_ = b.mk_pi(d_id, BinderInfo::Default, c("Nat"), type_);
    let type_ = b.mk_pi(b_id, BinderInfo::Default, c("Nat"), type_);
    let type_ = b.mk_pi(a_id, BinderInfo::Default, c("Nat"), type_);
    Declaration::Theorem {
        name: Name::from_string(name),
        level_params: vec![],
        type_: b.finish(type_),
        value: c(original),
    }
}

impl Environment {
    pub(crate) fn register_nat_distrib_aliases(&mut self) -> Result<(), EnvError> {
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        self.register_nat_left_distrib_proof()?;
        self.register_nat_right_distrib_proof()?;
        for left in [true, false] {
            self.ensure_exact_checked_decl(declaration(left, false))?;
        }
        // Both declarations are protected in the repository-pinned Lean source.
        self.mark_protected(Name::from_string("Nat.mul_add"));
        self.mark_protected(Name::from_string("Nat.add_mul"));
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::reference::ReferenceKernel;

    #[test]
    fn canonical_distributivity_names_are_checked_protected_and_idempotent() {
        let mut env = Environment::with_prelude();
        for name in ["Nat.mul_add", "Nat.add_mul"] {
            let name = Name::from_string(name);
            assert!(env
                .get_const(&name)
                .expect("canonical theorem")
                .value
                .is_some());
            assert!(env.axiom_deps(&name).expect("closure").is_empty());
            assert!(env.is_protected(&name));
        }
        let before = (env.num_constants(), env.num_instances());
        env.register_nat_distrib_aliases()
            .expect("repeat registration");
        assert_eq!((env.num_constants(), env.num_instances()), before);
    }

    #[test]
    fn canonical_distributivity_names_preserve_checked_import_ownership() {
        let mut env = Environment::try_with_prelude_for_import().expect("import theory");
        env.register_nat_distrib_aliases()
            .expect("import suppression");
        for name in ["Nat.mul_add", "Nat.add_mul"] {
            let name = Name::from_string(name);
            assert!(env.get_const(&name).is_none());
            assert!(!env.is_protected(&name));
        }
    }

    #[test]
    fn reference_replays_both_distributivity_proofs_and_refuses_an_extra_unit() {
        let env = Environment::with_prelude();
        let mut reference = ReferenceKernel::new(env).expect("reference theory");
        for left in [true, false] {
            let mut original = declaration(left, false);
            let Declaration::Theorem { name, value, .. } = &mut original else {
                unreachable!()
            };
            *value = c(if left { "Nat.mul_add" } else { "Nat.add_mul" });
            *name = Name::from_string(if left {
                "distrib_reference_left"
            } else {
                "distrib_reference_right"
            });
            let alias = name.clone();
            reference
                .add_checked(original)
                .expect("actual universal proof closure");
            assert!(reference
                .environment()
                .axiom_deps(&alias)
                .expect("closure")
                .is_empty());
            let mut changed = declaration(left, true);
            let Declaration::Theorem { name, value, .. } = &mut changed else {
                unreachable!()
            };
            *value = c(if left { "Nat.mul_add" } else { "Nat.add_mul" });
            *name = Name::from_string("distrib_extra_unit");
            let before = reference.environment().num_constants();
            assert!(reference.add_checked(changed).is_err());
            assert_eq!(reference.environment().num_constants(), before);
            assert!(reference
                .environment()
                .get_const(&Name::from_string("distrib_extra_unit"))
                .is_none());
        }
    }
}

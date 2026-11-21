// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Checked distributivity over the real width-generic BitVec operations.
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::{BinderInfo, Expr, Level, Name};

fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}
fn call(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(c(name), args)
}
fn one() -> Level {
    Level::succ(Level::zero())
}
fn eq(carrier: Expr, a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![one()]),
        [carrier, a, b],
    )
}
fn trans(carrier: Expr, a: Expr, b: Expr, d: Expr, first: Expr, second: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq.trans"), vec![one()]),
        [carrier, a, b, d, first, second],
    )
}
fn symm(carrier: Expr, a: Expr, b: Expr, proof: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq.symm"), vec![one()]),
        [carrier, a, b, proof],
    )
}
fn congr(
    parent: &EnvDeclBuilder,
    carrier: Expr,
    from: Expr,
    to: Expr,
    proof: Expr,
    f: impl FnOnce(Expr) -> Expr,
) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let (id, x) = b.fresh_local(carrier.clone());
    let out = b.mk_lam(id, BinderInfo::Default, carrier.clone(), f(x));
    let function = b.finish_child(out);
    Expr::apps(
        Expr::const_(Name::from_string("congrArg"), vec![one(), one()]),
        [carrier.clone(), carrier, from, to, function, proof],
    )
}
fn nadd(a: Expr, b: Expr) -> Expr {
    call("Nat.add", [a, b])
}
fn nmul(a: Expr, b: Expr) -> Expr {
    call("Nat.mul", [a, b])
}
fn modulo(a: Expr, n: Expr) -> Expr {
    call("Nat.mod", [a, n])
}

fn distributivity(left: bool) -> Declaration {
    let mut b = EnvDeclBuilder::new();
    let (w_id, w) = b.fresh_local(c("Nat"));
    let carrier = Expr::app(c("BitVec"), w.clone());
    let (x_id, x) = b.fresh_local(carrier.clone());
    let (y_id, y) = b.fresh_local(carrier.clone());
    let (z_id, z) = b.fresh_local(carrier.clone());
    let add = |a: Expr, d: Expr| call("BitVec.add", [w.clone(), a, d]);
    let mul = |a: Expr, d: Expr| call("BitVec.mul", [w.clone(), a, d]);
    let (name, lhs, rhs, proof) = if !left {
        let lhs = mul(add(x.clone(), y.clone()), z.clone());
        let rhs = add(mul(x.clone(), z.clone()), mul(y.clone(), z.clone()));
        let a = call("BitVec.toNat", [w.clone(), x.clone()]);
        let d = call("BitVec.toNat", [w.clone(), y.clone()]);
        let e = call("BitVec.toNat", [w.clone(), z.clone()]);
        let modulus = Environment::two_pow(w.clone());
        let sum = nadd(a.clone(), d.clone());
        let reduced_sum = modulo(sum.clone(), modulus.clone());
        let twice_sum = modulo(reduced_sum.clone(), modulus.clone());
        let reduced_e = modulo(e.clone(), modulus.clone());
        let ae = nmul(a.clone(), e.clone());
        let de = nmul(d.clone(), e.clone());
        let terms = [
            modulo(nmul(reduced_sum.clone(), e.clone()), modulus.clone()),
            modulo(nmul(twice_sum.clone(), reduced_e.clone()), modulus.clone()),
            modulo(
                nmul(reduced_sum.clone(), reduced_e.clone()),
                modulus.clone(),
            ),
            modulo(nmul(sum.clone(), e.clone()), modulus.clone()),
            modulo(nadd(ae.clone(), de.clone()), modulus.clone()),
            modulo(
                nadd(
                    modulo(ae.clone(), modulus.clone()),
                    modulo(de.clone(), modulus.clone()),
                ),
                modulus.clone(),
            ),
        ];
        let proofs = [
            call(
                "Nat.mul_mod",
                [reduced_sum.clone(), e.clone(), modulus.clone()],
            ),
            congr(
                &b,
                c("Nat"),
                twice_sum,
                reduced_sum,
                call("Nat.mod_mod", [sum.clone(), modulus.clone()]),
                |v| modulo(nmul(v, reduced_e), modulus.clone()),
            ),
            symm(
                c("Nat"),
                terms[3].clone(),
                terms[2].clone(),
                call("Nat.mul_mod", [sum.clone(), e.clone(), modulus.clone()]),
            ),
            congr(
                &b,
                c("Nat"),
                nmul(sum, e.clone()),
                nadd(ae.clone(), de.clone()),
                call("Nat.right_distrib", [a, d, e]),
                |v| modulo(v, modulus.clone()),
            ),
            call("Nat.add_mod", [ae, de, modulus]),
        ];
        let mut proof = proofs[0].clone();
        for i in 1..proofs.len() {
            proof = trans(
                c("Nat"),
                terms[0].clone(),
                terms[i].clone(),
                terms[i + 1].clone(),
                proof,
                proofs[i].clone(),
            );
        }
        let proof = call(
            "BitVec.eq_of_toNat_eq",
            [w.clone(), lhs.clone(), rhs.clone(), proof],
        );
        ("BitVec.add_mul", lhs, rhs, proof)
    } else {
        let terms = [
            mul(x.clone(), add(y.clone(), z.clone())),
            mul(add(y.clone(), z.clone()), x.clone()),
            add(mul(y.clone(), x.clone()), mul(z.clone(), x.clone())),
            add(mul(x.clone(), y.clone()), mul(z.clone(), x.clone())),
            add(mul(x.clone(), y.clone()), mul(x.clone(), z.clone())),
        ];
        let proofs = [
            call(
                "BitVec.mul_comm",
                [w.clone(), x.clone(), add(y.clone(), z.clone())],
            ),
            call(
                "BitVec.add_mul",
                [w.clone(), y.clone(), z.clone(), x.clone()],
            ),
            congr(
                &b,
                carrier.clone(),
                mul(y.clone(), x.clone()),
                mul(x.clone(), y.clone()),
                call("BitVec.mul_comm", [w.clone(), y.clone(), x.clone()]),
                |v| add(v, mul(z.clone(), x.clone())),
            ),
            congr(
                &b,
                carrier.clone(),
                mul(z.clone(), x.clone()),
                mul(x.clone(), z.clone()),
                call("BitVec.mul_comm", [w.clone(), z.clone(), x.clone()]),
                |v| add(mul(x.clone(), y.clone()), v),
            ),
        ];
        let mut proof = proofs[0].clone();
        for i in 1..proofs.len() {
            proof = trans(
                carrier.clone(),
                terms[0].clone(),
                terms[i].clone(),
                terms[i + 1].clone(),
                proof,
                proofs[i].clone(),
            );
        }
        ("BitVec.mul_add", terms[0].clone(), terms[4].clone(), proof)
    };
    let mut type_ = eq(carrier.clone(), lhs, rhs);
    let mut value = proof;
    for (id, domain) in [
        (z_id, carrier.clone()),
        (y_id, carrier.clone()),
        (x_id, carrier),
        (w_id, c("Nat")),
    ] {
        type_ = b.mk_pi(id, BinderInfo::Implicit, domain.clone(), type_);
        value = b.mk_lam(id, BinderInfo::Implicit, domain, value);
    }
    Declaration::Theorem {
        name: Name::from_string(name),
        level_params: vec![],
        type_: b.finish(type_),
        value: b.finish(value),
    }
}

impl Environment {
    pub(crate) fn register_bitvec_distributivity(&mut self) -> Result<(), EnvError> {
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        self.register_nat_remainder_uniqueness()?;
        self.register_bitvec_arithmetic()?;
        self.ensure_exact_checked_decl(distributivity(false))?;
        self.ensure_exact_checked_decl(distributivity(true))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::reference::ReferenceKernel;
    #[test]
    fn bitvec_distributivity_is_checked_axiom_free_and_idempotent() {
        let mut env = Environment::with_prelude();
        for name in ["BitVec.add_mul", "BitVec.mul_add"] {
            let name = Name::from_string(name);
            assert!(env
                .get_const(&name)
                .expect("actual theorem")
                .value
                .is_some());
            assert!(env.axiom_deps(&name).expect("closure").is_empty());
        }
        let before = (env.num_constants(), env.num_instances());
        env.register_bitvec_distributivity()
            .expect("idempotent registration");
        assert_eq!((env.num_constants(), env.num_instances()), before);
    }
    #[test]
    fn bitvec_distributivity_preserves_checked_import_ownership() {
        let mut env = Environment::try_with_prelude_for_import().expect("import prelude");
        env.register_bitvec_distributivity()
            .expect("import suppression");
        for name in ["BitVec.add_mul", "BitVec.mul_add"] {
            assert!(env.get_const(&Name::from_string(name)).is_none());
        }
    }
    #[test]
    fn reference_replays_both_universal_distributivity_proofs_and_refuses_extra_unit() {
        let mut reference =
            ReferenceKernel::new(Environment::with_prelude()).expect("reference theory");
        for left in [false, true] {
            let Declaration::Theorem { name, type_, .. } = distributivity(left) else {
                unreachable!()
            };
            let alias = Name::from_string(&format!("distrib_reference_{name}"));
            reference
                .add_checked(Declaration::Theorem {
                    name: alias.clone(),
                    level_params: vec![],
                    type_: type_.clone(),
                    value: Expr::const_(name.clone(), vec![]),
                })
                .expect("actual complete universal proof");
            assert!(reference
                .environment()
                .axiom_deps(&alias)
                .expect("closure")
                .is_empty());
            let mut b = EnvDeclBuilder::new();
            let (w_id, w) = b.fresh_local(c("Nat"));
            let carrier = Expr::app(c("BitVec"), w.clone());
            let (x_id, x) = b.fresh_local(carrier.clone());
            let (y_id, y) = b.fresh_local(carrier.clone());
            let (z_id, z) = b.fresh_local(carrier.clone());
            let add = |a: Expr, d: Expr| call("BitVec.add", [w.clone(), a, d]);
            let mul = |a: Expr, d: Expr| call("BitVec.mul", [w.clone(), a, d]);
            let (lhs, rhs) = if left {
                (
                    mul(x.clone(), add(y.clone(), z.clone())),
                    add(mul(x.clone(), y.clone()), mul(x.clone(), z.clone())),
                )
            } else {
                (
                    mul(add(x.clone(), y.clone()), z.clone()),
                    add(mul(x.clone(), z.clone()), mul(y.clone(), z.clone())),
                )
            };
            let extra = call("BitVec.ofNat", [w.clone(), Expr::nat_lit(1)]);
            let mut changed = eq(carrier.clone(), lhs, add(rhs, extra));
            for (id, domain) in [
                (z_id, carrier.clone()),
                (y_id, carrier.clone()),
                (x_id, carrier),
                (w_id, c("Nat")),
            ] {
                changed = b.mk_pi(id, BinderInfo::Implicit, domain, changed);
            }
            let before = (
                reference.environment().num_constants(),
                reference.environment().num_instances(),
            );
            let mutant = Name::from_string(&format!("distrib_changed_{name}"));
            assert!(reference
                .add_checked(Declaration::Theorem {
                    name: mutant.clone(),
                    level_params: vec![],
                    type_: b.finish(changed),
                    value: Expr::const_(name, vec![]),
                })
                .is_err());
            assert!(reference.environment().get_const(&mutant).is_none());
            assert_eq!(
                (
                    reference.environment().num_constants(),
                    reference.environment().num_instances()
                ),
                before
            );
        }
    }
}

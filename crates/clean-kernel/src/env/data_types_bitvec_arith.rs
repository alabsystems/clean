// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Checked, width-generic BitVec arithmetic from Lean 4.30's BasicAux/Basic.
//! Both operations use the existing logical ofNat/toNat definitions. This
//! adds no axiom, native reduction rule, or substitute finite carrier.

use super::decl_builder::EnvDeclBuilder;
use super::{
    Declaration, EnvError, Environment, KernelInstanceInfo, LEAN_DEFAULT_INSTANCE_PRIORITY,
};
use crate::{BinderInfo, Expr, Level, Name};

fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

impl Environment {
    pub(crate) fn register_bitvec_arithmetic(&mut self) -> Result<(), EnvError> {
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        self.register_bitvec_of_nat()?;
        self.init_add()?;
        self.init_mul()?;
        for (operation, natural, class, instance) in [
            ("BitVec.add", "Nat.add", "Add", "BitVec.instAdd"),
            ("BitVec.mul", "Nat.mul", "Mul", "BitVec.instMul"),
        ] {
            let mut b = EnvDeclBuilder::new();
            let (w_id, w) = b.fresh_local(c("Nat"));
            let carrier = Expr::app(c("BitVec"), w.clone());
            let (x_id, x) = b.fresh_local(carrier.clone());
            let (y_id, y) = b.fresh_local(carrier.clone());
            let x_nat = Expr::apps(c("BitVec.toNat"), [w.clone(), x]);
            let y_nat = Expr::apps(c("BitVec.toNat"), [w.clone(), y]);
            let body = Expr::apps(
                c("BitVec.ofNat"),
                [w.clone(), Expr::apps(c(natural), [x_nat, y_nat])],
            );
            let ty = b.mk_pi(y_id, BinderInfo::Default, carrier.clone(), carrier.clone());
            let ty = b.mk_pi(x_id, BinderInfo::Default, carrier.clone(), ty);
            let ty = b.mk_pi(w_id, BinderInfo::Implicit, c("Nat"), ty);
            let value = b.mk_lam(y_id, BinderInfo::Default, carrier.clone(), body);
            let value = b.mk_lam(x_id, BinderInfo::Default, carrier, value);
            let value = b.mk_lam(w_id, BinderInfo::Implicit, c("Nat"), value);
            self.ensure_exact_checked_decl(Declaration::Definition {
                name: Name::from_string(operation),
                level_params: vec![],
                type_: b.finish(ty),
                value: b.finish(value),
                is_reducible: true,
            })?;

            let mut b = EnvDeclBuilder::new();
            let (w_id, w) = b.fresh_local(c("Nat"));
            let carrier = Expr::app(c("BitVec"), w.clone());
            let class_const = Expr::const_(Name::from_string(class), vec![Level::zero()]);
            let class_ctor = Expr::const_(
                Name::from_string(&format!("{class}.mk")),
                vec![Level::zero()],
            );
            let ty = Expr::app(class_const, carrier.clone());
            let ty = b.mk_pi(w_id, BinderInfo::Implicit, c("Nat"), ty);
            let value = Expr::apps(class_ctor, [carrier, Expr::app(c(operation), w)]);
            let value = b.mk_lam(w_id, BinderInfo::Implicit, c("Nat"), value);
            self.ensure_exact_checked_decl(Declaration::Definition {
                name: Name::from_string(instance),
                level_params: vec![],
                type_: b.finish(ty),
                value: b.finish(value),
                is_reducible: true,
            })?;
            self.ensure_exact_instance(KernelInstanceInfo {
                name: Name::from_string(instance),
                class_name: Name::from_string(class),
                priority: LEAN_DEFAULT_INSTANCE_PRIORITY,
                type_: None,
                value: None,
            })?;
        }
        self.register_bitvec_mul_comm()?;
        self.register_bitvec_eq_of_to_nat_eq()
    }

    /// Equality of the actual Fin payloads determines equality of BitVecs.
    /// Destructure both wrappers: no symbolic structure-eta is assumed.
    fn register_bitvec_eq_of_to_nat_eq(&mut self) -> Result<(), EnvError> {
        self.register_fin_dec_eq_proof()?;
        let type1 = Level::succ(Level::zero());
        let equality = |carrier: Expr, x: Expr, y: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
                [carrier, x, y],
            )
        };
        let mut b = EnvDeclBuilder::new();
        let (w_id, w) = b.fresh_local(c("Nat"));
        let carrier = Expr::app(c("BitVec"), w.clone());
        let modulus = Self::two_pow(w.clone());
        let payload = Expr::app(c("Fin"), modulus.clone());
        let to_nat = |x: Expr| Expr::apps(c("BitVec.toNat"), [w.clone(), x]);
        let of_fin = |x: Expr| Expr::apps(c("BitVec.ofFin"), [w.clone(), x]);
        let (x_id, x) = b.fresh_local(carrier.clone());
        let (y_id, y) = b.fresh_local(carrier.clone());
        let h_ty = equality(c("Nat"), to_nat(x.clone()), to_nat(y.clone()));
        let (h_id, h) = b.fresh_local(h_ty.clone());
        let goal = equality(carrier.clone(), x.clone(), y.clone());
        let outer_motive = {
            let mut m = EnvDeclBuilder::child_of(&b);
            let (v_id, v) = m.fresh_local(carrier.clone());
            let hyp = equality(c("Nat"), to_nat(v.clone()), to_nat(y.clone()));
            let out = Expr::pi(
                BinderInfo::Default,
                hyp,
                equality(carrier.clone(), v, y.clone()),
            );
            let out = m.mk_lam(v_id, BinderInfo::Default, carrier.clone(), out);
            m.finish_child(out)
        };
        let mut outer = EnvDeclBuilder::child_of(&b);
        let (a_id, a) = outer.fresh_local(payload.clone());
        let of_a = of_fin(a.clone());
        let inner_motive = {
            let mut m = EnvDeclBuilder::child_of(&outer);
            let (v_id, v) = m.fresh_local(carrier.clone());
            let hyp = equality(c("Nat"), to_nat(of_a.clone()), to_nat(v.clone()));
            let out = Expr::pi(
                BinderInfo::Default,
                hyp,
                equality(carrier.clone(), of_a.clone(), v),
            );
            let out = m.mk_lam(v_id, BinderInfo::Default, carrier.clone(), out);
            m.finish_child(out)
        };
        let inner_minor = {
            let mut inner = EnvDeclBuilder::child_of(&outer);
            let (d_id, d) = inner.fresh_local(payload.clone());
            let hyp = equality(c("Nat"), to_nat(of_a), to_nat(of_fin(d.clone())));
            let (proof_id, proof) = inner.fresh_local(hyp.clone());
            let fin_eq = Expr::apps(
                c("Fin.eq_of_val_eq"),
                [modulus, a.clone(), d.clone(), proof],
            );
            let out = Expr::apps(
                Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]),
                [
                    payload.clone(),
                    carrier.clone(),
                    a,
                    d,
                    Expr::app(c("BitVec.ofFin"), w.clone()),
                    fin_eq,
                ],
            );
            let out = inner.mk_lam(proof_id, BinderInfo::Default, hyp, out);
            let out = inner.mk_lam(d_id, BinderInfo::Default, payload.clone(), out);
            inner.finish_child(out)
        };
        let rec = Expr::const_(Name::from_string("BitVec.rec"), vec![Level::zero()]);
        let inner = Expr::apps(rec.clone(), [w.clone(), inner_motive, inner_minor, y]);
        let outer_minor = outer.mk_lam(a_id, BinderInfo::Default, payload, inner);
        let outer_minor = outer.finish_child(outer_minor);
        let value = Expr::apps(rec, [w, outer_motive, outer_minor, x, h]);
        let type_ = b.mk_pi(h_id, BinderInfo::Default, h_ty.clone(), goal);
        let type_ = b.mk_pi(y_id, BinderInfo::Implicit, carrier.clone(), type_);
        let type_ = b.mk_pi(x_id, BinderInfo::Implicit, carrier.clone(), type_);
        let type_ = b.mk_pi(w_id, BinderInfo::Implicit, c("Nat"), type_);
        let value = b.mk_lam(h_id, BinderInfo::Default, h_ty, value);
        let value = b.mk_lam(y_id, BinderInfo::Implicit, carrier.clone(), value);
        let value = b.mk_lam(x_id, BinderInfo::Implicit, carrier, value);
        let value = b.mk_lam(w_id, BinderInfo::Implicit, c("Nat"), value);
        self.ensure_exact_checked_decl(Declaration::Theorem {
            name: Name::from_string("BitVec.eq_of_toNat_eq"),
            level_params: vec![],
            type_: b.finish(type_),
            value: b.finish(value),
        })
    }

    /// The canonical width-generic commutativity statement, proved by mapping
    /// the existing constructive Nat equality through the logical ofNat.
    fn register_bitvec_mul_comm(&mut self) -> Result<(), EnvError> {
        self.register_nat_mul_comm_proof()?;
        let mut b = EnvDeclBuilder::new();
        let (w_id, w) = b.fresh_local(c("Nat"));
        let carrier = Expr::app(c("BitVec"), w.clone());
        let (x_id, x) = b.fresh_local(carrier.clone());
        let (y_id, y) = b.fresh_local(carrier.clone());
        let x_nat = Expr::apps(c("BitVec.toNat"), [w.clone(), x.clone()]);
        let y_nat = Expr::apps(c("BitVec.toNat"), [w.clone(), y.clone()]);
        let natural_lhs = Expr::apps(c("Nat.mul"), [x_nat.clone(), y_nat.clone()]);
        let natural_rhs = Expr::apps(c("Nat.mul"), [y_nat.clone(), x_nat.clone()]);
        let type1 = Level::succ(Level::zero());
        let type_ = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![type1.clone()]),
            [
                carrier.clone(),
                Expr::apps(c("BitVec.mul"), [w.clone(), x.clone(), y.clone()]),
                Expr::apps(c("BitVec.mul"), [w.clone(), y, x]),
            ],
        );
        let value = Expr::apps(
            Expr::const_(Name::from_string("congrArg"), vec![type1.clone(), type1]),
            [
                c("Nat"),
                carrier.clone(),
                natural_lhs,
                natural_rhs,
                Expr::app(c("BitVec.ofNat"), w),
                Expr::apps(c("Nat.mul_comm"), [x_nat, y_nat]),
            ],
        );
        let type_ = b.mk_pi(y_id, BinderInfo::Default, carrier.clone(), type_);
        let type_ = b.mk_pi(x_id, BinderInfo::Default, carrier.clone(), type_);
        let type_ = b.mk_pi(w_id, BinderInfo::Implicit, c("Nat"), type_);
        let value = b.mk_lam(y_id, BinderInfo::Default, carrier.clone(), value);
        let value = b.mk_lam(x_id, BinderInfo::Default, carrier, value);
        let value = b.mk_lam(w_id, BinderInfo::Implicit, c("Nat"), value);
        self.ensure_exact_checked_decl(Declaration::Theorem {
            name: Name::from_string("BitVec.mul_comm"),
            level_params: vec![],
            type_: b.finish(type_),
            value: b.finish(value),
        })?;
        self.mark_protected(Name::from_string("BitVec.mul_comm"));
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::reference::ReferenceKernel;

    #[test]
    fn bitvec_arithmetic_is_checked_axiom_free_and_idempotent() {
        let mut env = Environment::with_prelude();
        for name in [
            "BitVec.add",
            "BitVec.mul",
            "BitVec.instAdd",
            "BitVec.instMul",
            "BitVec.mul_comm",
            "BitVec.eq_of_toNat_eq",
            "BitVec.decEq",
            "instDecidableEqBitVec",
        ] {
            let name = Name::from_string(name);
            let info = env
                .get_const(&name)
                .expect("canonical arithmetic declaration");
            assert!(info.value.is_some(), "{name} has a checked value");
            assert!(env.axiom_deps(&name).expect("closure").is_empty(), "{name}");
        }
        for name in ["BitVec.instAdd", "BitVec.instMul", "instDecidableEqBitVec"] {
            assert!(env.is_instance(&Name::from_string(name)));
        }
        assert!(env.is_protected(&Name::from_string("BitVec.mul_comm")));
        let population = (env.num_constants(), env.num_instances());
        env.register_bitvec_arithmetic()
            .expect("idempotent registration");
        env.register_bitvec_dec_eq_instance()
            .expect("idempotent equality instance");
        assert_eq!((env.num_constants(), env.num_instances()), population);
    }

    #[test]
    fn bitvec_arithmetic_is_withheld_for_checked_source_import() {
        let mut env = Environment::try_with_prelude_for_import().expect("import prelude");
        env.register_bitvec_arithmetic()
            .expect("import mode leaves source ownership");
        env.register_bitvec_dec_eq_instance()
            .expect("import mode withholds the equality index");
        assert!(!env.is_instance(&Name::from_string("instDecidableEqBitVec")));
        assert!(!env.is_protected(&Name::from_string("BitVec.mul_comm")));
        for name in [
            "BitVec.add",
            "BitVec.mul",
            "BitVec.instAdd",
            "BitVec.instMul",
            "BitVec.mul_comm",
            "BitVec.eq_of_toNat_eq",
            "BitVec.decEq",
            "instDecidableEqBitVec",
        ] {
            assert!(env.get_const(&Name::from_string(name)).is_none(), "{name}");
        }
    }

    #[test]
    fn bitvec_mul_comm_reference_checks_all_widths_and_refuses_a_changed_statement() {
        let env = Environment::with_prelude();
        let original = env
            .get_const(&Name::from_string("BitVec.mul_comm"))
            .expect("generic commutativity");
        let type_ = original.type_.clone();
        let mut reference = ReferenceKernel::new(env).expect("reference prelude");
        let proof = c("BitVec.mul_comm");
        reference
            .add_checked(Declaration::Theorem {
                name: Name::from_string("bitvec_mul_comm_reference"),
                level_params: vec![],
                type_,
                value: proof.clone(),
            })
            .expect("replay the actual generic theorem and its inherited closure");
        assert!(reference
            .environment()
            .axiom_deps(&Name::from_string("bitvec_mul_comm_reference"))
            .expect("closure")
            .is_empty());

        let mut b = EnvDeclBuilder::new();
        let (w_id, w) = b.fresh_local(c("Nat"));
        let carrier = Expr::app(c("BitVec"), w.clone());
        let (x_id, x) = b.fresh_local(carrier.clone());
        let (y_id, y) = b.fresh_local(carrier.clone());
        let lhs = Expr::apps(c("BitVec.mul"), [w.clone(), x.clone(), y.clone()]);
        let rhs = Expr::apps(
            c("BitVec.add"),
            [
                w.clone(),
                Expr::apps(c("BitVec.mul"), [w.clone(), y, x]),
                Expr::apps(c("BitVec.ofNat"), [w, Expr::nat_lit(1)]),
            ],
        );
        let bad = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [carrier.clone(), lhs, rhs],
        );
        let bad = b.mk_pi(y_id, BinderInfo::Default, carrier.clone(), bad);
        let bad = b.mk_pi(x_id, BinderInfo::Default, carrier, bad);
        let bad = b.mk_pi(w_id, BinderInfo::Implicit, c("Nat"), bad);
        let before = reference.environment().num_constants();
        assert!(
            reference
                .add_checked(Declaration::Theorem {
                    name: Name::from_string("bitvec_mul_comm_changed"),
                    level_params: vec![],
                    type_: b.finish(bad),
                    value: proof,
                })
                .is_err(),
            "the same proof cannot certify an extra residue"
        );
        assert_eq!(reference.environment().num_constants(), before);
    }

    #[test]
    fn bitvec_arithmetic_reference_replays_wraparound_and_refuses_changed_results() {
        let env = Environment::with_prelude();
        let mut reference = ReferenceKernel::new(env).expect("reference prelude");
        let max = u64::MAX;
        let cases = [
            (0, 3, 4, 0, 0),
            (1, 1, 1, 0, 1),
            (3, 7, 3, 2, 5),
            (8, 255, 2, 1, 254),
            (65, max, 1, u128::from(max) + 1, u128::from(max)),
            (
                128,
                max,
                max,
                2 * u128::from(max),
                u128::from(max) * u128::from(max),
            ),
        ];
        for (index, (width, x, y, sum, product)) in cases.into_iter().enumerate() {
            for (operation, expected) in [("BitVec.add", sum), ("BitVec.mul", product)] {
                let w = Expr::nat_lit(width);
                let bv = |n| Expr::apps(c("BitVec.ofNat"), [w.clone(), Expr::nat_lit(n)]);
                let actual = Expr::apps(c(operation), [w.clone(), bv(x), bv(y)]);
                let actual = Expr::apps(c("BitVec.toNat"), [w, actual]);
                let eq = |rhs| {
                    Expr::apps(
                        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                        [c("Nat"), actual.clone(), rhs],
                    )
                };
                let proof = Expr::apps(
                    Expr::const_(
                        Name::from_string("Eq.refl"),
                        vec![Level::succ(Level::zero())],
                    ),
                    [c("Nat"), actual.clone()],
                );
                reference
                    .add_checked(Declaration::Theorem {
                        name: Name::from_string(&format!("bitvec_reference_{index}_{operation}")),
                        level_params: vec![],
                        type_: eq(Expr::nat_lit_u128(expected)),
                        value: proof.clone(),
                    })
                    .expect("actual logical arithmetic computes the expected residue");
                let before = reference.environment().num_constants();
                assert!(
                    reference
                        .add_checked(Declaration::Theorem {
                            name: Name::from_string(&format!("bitvec_changed_{index}_{operation}")),
                            level_params: vec![],
                            type_: eq(Expr::nat_lit_u128(expected + 1)),
                            value: proof,
                        })
                        .is_err(),
                    "unchanged proof must refuse a changed result"
                );
                assert_eq!(reference.environment().num_constants(), before);
            }
        }
    }

    #[test]
    fn bitvec_extensionality_reference_replays_and_refuses_original_proof_for_extra_unit() {
        let env = Environment::with_prelude();
        let original = Name::from_string("BitVec.eq_of_toNat_eq");
        let type_ = env
            .get_const(&original)
            .expect("actual extensionality")
            .type_
            .clone();
        let mut reference = ReferenceKernel::new(env).expect("reference theory");
        let alias = Name::from_string("bitvec_extensionality_reference");
        reference
            .add_checked(Declaration::Theorem {
                name: alias.clone(),
                level_params: vec![],
                type_,
                value: Expr::const_(original.clone(), vec![]),
            })
            .expect("replay complete universal proof");
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
        let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
        let hyp = Expr::apps(
            eq.clone(),
            [
                c("Nat"),
                Expr::apps(c("BitVec.toNat"), [w.clone(), x.clone()]),
                Expr::apps(c("BitVec.toNat"), [w.clone(), y.clone()]),
            ],
        );
        let (h_id, _) = b.fresh_local(hyp.clone());
        let one = Expr::apps(c("BitVec.ofNat"), [w.clone(), Expr::nat_lit(1)]);
        let wrong = Expr::apps(c("BitVec.add"), [w, y, one]);
        let type_ = Expr::apps(eq, [carrier.clone(), x, wrong]);
        let type_ = b.mk_pi(h_id, BinderInfo::Default, hyp, type_);
        let type_ = b.mk_pi(y_id, BinderInfo::Implicit, carrier.clone(), type_);
        let type_ = b.mk_pi(x_id, BinderInfo::Implicit, carrier, type_);
        let type_ = b.mk_pi(w_id, BinderInfo::Implicit, c("Nat"), type_);
        let before = (
            reference.environment().num_constants(),
            reference.environment().num_instances(),
        );
        let name = Name::from_string("bitvec_extensionality_extra_unit");
        assert!(reference
            .add_checked(Declaration::Theorem {
                name: name.clone(),
                level_params: vec![],
                type_: b.finish(type_),
                value: Expr::const_(original, vec![]),
            })
            .is_err());
        assert!(reference.environment().get_const(&name).is_none());
        assert_eq!(
            (
                reference.environment().num_constants(),
                reference.environment().num_instances()
            ),
            before
        );
    }
}

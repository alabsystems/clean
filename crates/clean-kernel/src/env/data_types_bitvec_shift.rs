// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Constructive bounds needed by the BitVec logical-shift constructor.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::{BinderInfo, Expr, Level, Name};

fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn bound(parent: &EnvDeclBuilder, count: Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let (n_id, n) = b.fresh_local(c("Nat"));
    let shifted = Expr::apps(c("Nat.iterDiv2"), [count, n.clone()]);
    let result = Expr::apps(c("Nat.le"), [shifted, n]);
    let result = b.mk_pi(n_id, BinderInfo::Default, c("Nat"), result);
    b.finish_child(result)
}

impl Environment {
    /// Seed both Nat amounts and independently sized BitVec amounts. No
    /// homogeneous ShiftLeft/ShiftRight dictionary exists for BitVec in Lean.
    pub(crate) fn register_bitvec_shifts(&mut self) -> Result<(), EnvError> {
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        self.register_bitvec_of_nat()?;
        self.register_bitvec_shift_bound()?;
        self.init_hshiftleft()?;
        self.init_hshiftright()?;
        for (operation, nat_operation, class) in [
            ("BitVec.shiftLeft", "Nat.shiftLeft", "HShiftLeft"),
            ("BitVec.ushiftRight", "Nat.shiftRight", "HShiftRight"),
        ] {
            if self.get_const(&Name::from_string(operation)).is_none() {
                let mut b = EnvDeclBuilder::new();
                let (w_id, w) = b.fresh_local(c("Nat"));
                let carrier = Expr::app(c("BitVec"), w.clone());
                let (x_id, x) = b.fresh_local(carrier.clone());
                let (n_id, n) = b.fresh_local(c("Nat"));
                let x_nat = Expr::apps(c("BitVec.toNat"), [w.clone(), x.clone()]);
                let shifted = Expr::apps(c(nat_operation), [x_nat.clone(), n.clone()]);
                let body = if class == "HShiftLeft" {
                    Expr::apps(c("BitVec.ofNat"), [w.clone(), shifted])
                } else {
                    let bound = Expr::apps(c("BitVec.shiftBound"), [n, x_nat.clone()]);
                    let succ_shift = Expr::app(c("Nat.succ"), shifted.clone());
                    let succ_x = Expr::app(c("Nat.succ"), x_nat.clone());
                    let old_bound = Expr::proj(
                        Name::from_string("Fin"),
                        1,
                        Expr::apps(c("BitVec.toFin"), [w.clone(), x]),
                    );
                    let bound = Expr::apps(
                        c("Nat.le_trans"),
                        [
                            succ_shift,
                            succ_x,
                            Self::two_pow(w.clone()),
                            Expr::apps(c("Nat.succ_le_succ"), [shifted.clone(), x_nat, bound]),
                            old_bound,
                        ],
                    );
                    Expr::apps(c("BitVec.ofNatLT"), [w.clone(), shifted, bound])
                };
                let ty = b.mk_pi(n_id, BinderInfo::Default, c("Nat"), carrier.clone());
                let ty = b.mk_pi(x_id, BinderInfo::Default, carrier.clone(), ty);
                let ty = b.mk_pi(w_id, BinderInfo::Implicit, c("Nat"), ty);
                let value = b.mk_lam(n_id, BinderInfo::Default, c("Nat"), body);
                let value = b.mk_lam(x_id, BinderInfo::Default, carrier, value);
                let value = b.mk_lam(w_id, BinderInfo::Implicit, c("Nat"), value);
                self.add_decl(Declaration::Definition {
                    name: Name::from_string(operation),
                    level_params: vec![],
                    type_: b.finish(ty),
                    value: b.finish(value),
                    is_reducible: true,
                })?;
            }
            for bitvec_amount in [false, true] {
                let name = Name::from_string(&format!(
                    "BitVec.inst{class}{}",
                    if bitvec_amount { "" } else { "Nat" }
                ));
                if self.get_const(&name).is_some() {
                    continue;
                }
                let mut b = EnvDeclBuilder::new();
                let (w_id, w) = b.fresh_local(c("Nat"));
                let carrier = Expr::app(c("BitVec"), w.clone());
                let other_width = bitvec_amount.then(|| b.fresh_local(c("Nat")));
                let amount = other_width
                    .as_ref()
                    .map_or_else(|| c("Nat"), |(_, m)| Expr::app(c("BitVec"), m.clone()));
                let op = if let Some((_, m)) = &other_width {
                    let (x_id, x) = b.fresh_local(carrier.clone());
                    let (y_id, y) = b.fresh_local(amount.clone());
                    let body = Expr::apps(
                        c(operation),
                        [w.clone(), x, Expr::apps(c("BitVec.toNat"), [m.clone(), y])],
                    );
                    let body = b.mk_lam(y_id, BinderInfo::Default, amount.clone(), body);
                    b.mk_lam(x_id, BinderInfo::Default, carrier.clone(), body)
                } else {
                    Expr::app(c(operation), w)
                };
                let levels = vec![Level::zero(); 3];
                let ty = Expr::apps(
                    Expr::const_(Name::from_string(class), levels.clone()),
                    [carrier.clone(), amount.clone(), carrier.clone()],
                );
                let value = Expr::apps(
                    Expr::const_(Name::from_string(&format!("{class}.mk")), levels),
                    [carrier.clone(), amount, carrier, op],
                );
                let (ty, value) = if let Some((m_id, _)) = other_width {
                    (
                        b.mk_pi(m_id, BinderInfo::Implicit, c("Nat"), ty),
                        b.mk_lam(m_id, BinderInfo::Implicit, c("Nat"), value),
                    )
                } else {
                    (ty, value)
                };
                let ty = b.mk_pi(w_id, BinderInfo::Implicit, c("Nat"), ty);
                let value = b.mk_lam(w_id, BinderInfo::Implicit, c("Nat"), value);
                self.add_decl(Declaration::Definition {
                    name: name.clone(),
                    level_params: vec![],
                    type_: b.finish(ty),
                    value: b.finish(value),
                    is_reducible: true,
                })?;
                self.register_instance(super::KernelInstanceInfo {
                    name,
                    class_name: Name::from_string(class),
                    priority: 1000,
                    type_: None,
                    value: None,
                });
            }
        }
        self.register_bitvec_shift_equations()
    }

    /// State the Nat semantics independently of the implementation's operation
    /// table. Kernel checking of reflexivity unfolds the actual shift body at
    /// symbolic width, value and count; ground-value testing is not the proof.
    fn register_bitvec_shift_equations(&mut self) -> Result<(), EnvError> {
        for (lemma, operation, nat_operation, left) in [
            (
                "BitVec.toNat_shiftLeft",
                "BitVec.shiftLeft",
                "Nat.shiftLeft",
                true,
            ),
            (
                "BitVec.toNat_ushiftRight",
                "BitVec.ushiftRight",
                "Nat.shiftRight",
                false,
            ),
        ] {
            let name = Name::from_string(lemma);
            if self.get_const(&name).is_some() {
                continue;
            }
            let mut b = EnvDeclBuilder::new();
            let (w_id, w) = b.fresh_local(c("Nat"));
            let carrier = Expr::app(c("BitVec"), w.clone());
            // Preserve Lean's exact telescopes: {w n} {x} on the left,
            // and {w} (x) (n) on the right.
            let ((x_id, x), (n_id, n)) = if left {
                let count = b.fresh_local(c("Nat"));
                let value = b.fresh_local(carrier.clone());
                (value, count)
            } else {
                let value = b.fresh_local(carrier.clone());
                let count = b.fresh_local(c("Nat"));
                (value, count)
            };
            let input_nat = Expr::apps(c("BitVec.toNat"), [w.clone(), x.clone()]);
            let rhs = Expr::apps(c(nat_operation), [input_nat, n.clone()]);
            let rhs = if left {
                Expr::apps(c("Nat.mod"), [rhs, Self::two_pow(w.clone())])
            } else {
                rhs
            };
            let lhs = Expr::apps(
                c("BitVec.toNat"),
                [w.clone(), Expr::apps(c(operation), [w, x, n])],
            );
            let universe = vec![Level::succ(Level::zero())];
            let ty = Expr::apps(
                Expr::const_(Name::from_string("Eq"), universe.clone()),
                [c("Nat"), lhs, rhs.clone()],
            );
            let value = Expr::apps(
                Expr::const_(Name::from_string("Eq.refl"), universe),
                [c("Nat"), rhs],
            );
            let (ty, value) = if left {
                let ty = b.mk_pi(x_id, BinderInfo::Implicit, carrier.clone(), ty);
                let value = b.mk_lam(x_id, BinderInfo::Implicit, carrier, value);
                (
                    b.mk_pi(n_id, BinderInfo::Implicit, c("Nat"), ty),
                    b.mk_lam(n_id, BinderInfo::Implicit, c("Nat"), value),
                )
            } else {
                let ty = b.mk_pi(n_id, BinderInfo::Default, c("Nat"), ty);
                let value = b.mk_lam(n_id, BinderInfo::Default, c("Nat"), value);
                (
                    b.mk_pi(x_id, BinderInfo::Default, carrier.clone(), ty),
                    b.mk_lam(x_id, BinderInfo::Default, carrier, value),
                )
            };
            let ty = b.mk_pi(w_id, BinderInfo::Implicit, c("Nat"), ty);
            let value = b.mk_lam(w_id, BinderInfo::Implicit, c("Nat"), value);
            self.add_decl(Declaration::Theorem {
                name,
                level_params: vec![],
                type_: b.finish(ty),
                value: b.finish(value),
            })?;
        }
        Ok(())
    }

    /// Prove `∀ count n, Nat.iterDiv2 count n ≤ n` by induction on count.
    /// The step uses the checked div2/parity invariant, never a native reducer
    /// or a bound supplied as an axiom. Import mode obtains library declarations
    /// from checked oleans instead of seeding Clean's native bitwise bodies.
    pub(crate) fn register_bitvec_shift_bound(&mut self) -> Result<(), EnvError> {
        if self.suppress_lossy_structure_stubs
            || self
                .get_const(&Name::from_string("BitVec.shiftBound"))
                .is_some()
        {
            return Ok(());
        }
        self.register_nat_shiftright_def()?;
        self.register_nat_mul_left_cancel_succ_proof()?;
        self.register_nat_le_trans_proof()?;

        let mut b = EnvDeclBuilder::new();
        let (i_id, i) = b.fresh_local(c("Nat"));
        let theorem_type = b.mk_pi(i_id, BinderInfo::Default, c("Nat"), bound(&b, i.clone()));
        let theorem_type = b.finish(theorem_type);
        let motive = {
            let mut m = EnvDeclBuilder::new();
            let (j_id, j) = m.fresh_local(c("Nat"));
            let body = m.mk_lam(j_id, BinderInfo::Default, c("Nat"), bound(&m, j));
            m.finish(body)
        };
        let base = {
            let mut z = EnvDeclBuilder::new();
            let (n_id, n) = z.fresh_local(c("Nat"));
            let proof = Expr::app(c("Nat.le_refl"), n);
            let proof = z.mk_lam(n_id, BinderInfo::Default, c("Nat"), proof);
            z.finish(proof)
        };
        let step = {
            let mut s = EnvDeclBuilder::new();
            let (j_id, j) = s.fresh_local(c("Nat"));
            let ih_ty = bound(&s, j.clone());
            let (ih_id, ih) = s.fresh_local(ih_ty.clone());
            let (n_id, n) = s.fresh_local(c("Nat"));
            let half = Expr::app(c("Nat.div2"), n.clone());
            let parity = Expr::app(c("Nat.div2Par"), n.clone());
            let sum = Expr::apps(c("Nat.add"), [half.clone(), parity.clone()]);
            let half_le = Expr::apps(
                c("Nat.le_trans"),
                [
                    half.clone(),
                    sum,
                    n.clone(),
                    Expr::apps(c("Nat.le_add_right"), [half.clone(), parity]),
                    Expr::app(c("Nat.div2_add_par_le"), n.clone()),
                ],
            );
            let shifted = Expr::apps(c("Nat.iterDiv2"), [j.clone(), half.clone()]);
            let proof = Expr::apps(
                c("Nat.le_trans"),
                [shifted, half.clone(), n, Expr::app(ih, half), half_le],
            );
            let proof = s.mk_lam(n_id, BinderInfo::Default, c("Nat"), proof);
            let proof = s.mk_lam(ih_id, BinderInfo::Default, ih_ty, proof);
            let proof = s.mk_lam(j_id, BinderInfo::Default, c("Nat"), proof);
            s.finish(proof)
        };
        let proof = Expr::apps(
            Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            [motive, base, step, i],
        );
        let proof = b.mk_lam(i_id, BinderInfo::Default, c("Nat"), proof);
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("BitVec.shiftBound"),
            level_params: vec![],
            type_: theorem_type,
            value: b.finish(proof),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::TypeChecker;

    #[test]
    fn bitvec_shift_definitions_and_dictionaries_are_checked() {
        let env = Environment::with_prelude();
        let tc = TypeChecker::new(&env);
        for name in [
            "BitVec.shiftLeft",
            "BitVec.ushiftRight",
            "BitVec.instHShiftLeftNat",
            "BitVec.instHShiftLeft",
            "BitVec.instHShiftRightNat",
            "BitVec.instHShiftRight",
            "BitVec.toNat_shiftLeft",
            "BitVec.toNat_ushiftRight",
        ] {
            let name = Name::from_string(name);
            let info = env.get_const(&name).expect("shift declaration");
            tc.check_type(info.value.as_ref().expect("checked value"), &info.type_)
                .expect("checked body");
            assert!(env.axiom_deps(&name).expect("closure").is_empty(), "{name}");
        }
        for (w, x, n, left, right) in [
            (0, 0, 8, 0, 0),
            (3, 1, 0, 1, 1),
            (3, 7, 1, 6, 3),
            (3, 1, 3, 0, 0),
            (3, 7, 8, 0, 0),
            (8, 255, 1, 254, 127),
            (8, 1, 8, 0, 0),
        ] {
            let bv =
                |value| Expr::apps(c("BitVec.ofNat"), [Expr::nat_lit(w), Expr::nat_lit(value)]);
            for (op, expected) in [("BitVec.shiftLeft", left), ("BitVec.ushiftRight", right)] {
                let actual = Expr::apps(c(op), [Expr::nat_lit(w), bv(x), Expr::nat_lit(n)]);
                let stored = env.get_const(&Name::from_string(op)).expect("operation");
                let delta = Expr::apps(
                    stored.value.clone().expect("body"),
                    [Expr::nat_lit(w), bv(x), Expr::nat_lit(n)],
                );
                assert!(
                    tc.is_def_eq(&delta, &bv(expected)),
                    "stored {op} body w={w} x={x} n={n}"
                );
                let result_nat = Expr::apps(c("BitVec.toNat"), [Expr::nat_lit(w), actual.clone()]);
                assert!(
                    !tc.is_def_eq(&result_nat, &Expr::nat_lit(expected ^ 1)),
                    "wrong computed value must be refused"
                );
                assert!(
                    tc.is_def_eq(&actual, &bv(expected)),
                    "{op} width={w} value={x} count={n}"
                );
            }
        }
        for name in ["instShiftLeftBitVec", "instShiftRightBitVec"] {
            assert!(env.get_const(&Name::from_string(name)).is_none());
        }
    }

    #[test]
    fn bitvec_shift_bound_is_universal_and_axiom_free() {
        let mut env = Environment::with_prelude();
        env.register_bitvec_shift_bound()
            .expect("checked induction");
        let name = Name::from_string("BitVec.shiftBound");
        let info = env.get_const(&name).expect("bound theorem");
        let tc = TypeChecker::new(&env);
        tc.check_type(info.value.as_ref().expect("proof body"), &info.type_)
            .expect("universal proof typechecks");
        assert!(env.axiom_deps(&name).expect("closure").is_empty());
        for (count, n) in [(0, 0), (0, 255), (1, 255), (8, 255), (256, 1)] {
            let proof = Expr::apps(
                c("BitVec.shiftBound"),
                [Expr::nat_lit(count), Expr::nat_lit(n)],
            );
            let expected = Expr::apps(
                c("Nat.le"),
                [
                    Expr::apps(
                        c("Nat.shiftRight"),
                        [Expr::nat_lit(n), Expr::nat_lit(count)],
                    ),
                    Expr::nat_lit(n),
                ],
            );
            tc.check_type(&proof, &expected)
                .expect("shift-definition bridge");
        }
    }
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::checks::{c, lam, n, pi, Check};
use clean_kernel::{Environment, Expr};

impl Check<'_, '_> {
    pub fn naturals(&self) -> Result<(), String> {
        let nat = self.family("Nat", 0, 0, true, true, 2)?;
        // Reuse the kernel's existing natural/literal roles. Expected records
        // describe comparands only; they are never installed over the source.
        let canonical = Environment::try_with_prelude().map_err(|e| e.to_string())?;
        let expected = canonical
            .get_inductive(&n("Nat"))
            .ok_or("missing canonical Nat")?;
        if nat.constructor_names != expected.constructor_names {
            return Err(
                "actual Nat zero/successor roles differ from the kernel literal contract".into(),
            );
        }
        self.expected_type(&nat.name, &Expr::type_())?;
        let zero = self.constructor(&nat.constructor_names[0])?;
        let succ = self.constructor(&nat.constructor_names[1])?;
        if zero.num_fields != 0 || succ.num_fields != 1 {
            return Err("wrong Nat constructor fields".into());
        }
        self.expected_type(&zero.name, &c("Nat"))?;
        self.expected_type(&succ.name, &pi(c("Nat"), c("Nat")))?;
        self.equal(
            &Expr::const_(zero.name.clone(), vec![]),
            &Expr::nat_lit(0),
            "actual Nat zero/literal role",
        )?;
        self.equal(
            &Expr::app(Expr::const_(succ.name.clone(), vec![]), Expr::nat_lit(0)),
            &Expr::nat_lit(1),
            "actual Nat successor/literal role",
        )
    }
    pub fn order(&self) -> Result<(), String> {
        let le = self.family("Nat.le", 1, 1, true, false, 2)?;
        self.expected_type(&le.name, &pi(c("Nat"), pi(c("Nat"), Expr::prop())))?;
        let refl = self.constructor(&le.constructor_names[0])?;
        let step = self.constructor(&le.constructor_names[1])?;
        if refl.num_fields != 0 || step.num_fields != 2 {
            return Err("wrong natural-order constructor field roles".into());
        }
        self.expected_type(
            &refl.name,
            &pi(
                c("Nat"),
                Expr::apps(c("Nat.le"), [Expr::bvar(0), Expr::bvar(0)]),
            ),
        )?;
        let nat = self
            .program
            .env
            .get_inductive(&n("Nat"))
            .ok_or("missing Nat")?;
        let succ = Expr::const_(nat.constructor_names[1].clone(), vec![]);
        let step_type = pi(
            c("Nat"),
            pi(
                c("Nat"),
                pi(
                    Expr::apps(c("Nat.le"), [Expr::bvar(1), Expr::bvar(0)]),
                    Expr::apps(
                        c("Nat.le"),
                        [Expr::bvar(2), Expr::app(succ.clone(), Expr::bvar(1))],
                    ),
                ),
            ),
        );
        self.expected_type(&step.name, &step_type)?;
        self.expected_type(&n("Nat.lt"), &pi(c("Nat"), pi(c("Nat"), Expr::prop())))?;
        // This compares the ACTUAL relation to a standard constructor-bound
        // order, after checking Nat.le's family/constructors/recursor meaning.
        // A redefined always-true Nat.lt cannot appear on both sides.
        self.equal(
            &c("Nat.lt"),
            &lam(
                c("Nat"),
                lam(
                    c("Nat"),
                    Expr::apps(c("Nat.le"), [Expr::app(succ, Expr::bvar(1)), Expr::bvar(0)]),
                ),
            ),
            "actual Nat.lt strict natural order",
        )
    }
    pub fn scalar_families(&self) -> Result<(), String> {
        let fin = self.family("Fin", 1, 0, false, true, 1)?;
        let bv = self.family("BitVec", 1, 0, false, true, 1)?;
        self.expected_type(&fin.name, &pi(c("Nat"), Expr::type_()))?;
        self.expected_type(&bv.name, &pi(c("Nat"), Expr::type_()))?;
        let fin_ctor = self.constructor(&fin.constructor_names[0])?;
        let bv_ctor = self.constructor(&bv.constructor_names[0])?;
        if fin_ctor.num_fields != 2 || bv_ctor.num_fields != 1 {
            return Err("wrong Fin/BitVec computational/proof field roles".into());
        }
        let fin_ctor_type = pi(
            c("Nat"),
            pi(
                c("Nat"),
                pi(
                    Expr::apps(c("Nat.lt"), [Expr::bvar(0), Expr::bvar(1)]),
                    Expr::app(c("Fin"), Expr::bvar(2)),
                ),
            ),
        );
        self.expected_type(&fin_ctor.name, &fin_ctor_type)?;
        let bv_ctor_type = pi(
            c("Nat"),
            pi(
                Expr::app(
                    c("Fin"),
                    Expr::apps(c("Nat.pow"), [Expr::nat_lit(2), Expr::bvar(0)]),
                ),
                Expr::app(c("BitVec"), Expr::bvar(1)),
            ),
        );
        self.expected_type(&bv_ctor.name, &bv_ctor_type)?;
        for (family, width) in [("UInt32", 32), ("UInt64", 64)] {
            let ind = self.family(family, 0, 0, false, true, 1)?;
            self.expected_type(&ind.name, &Expr::type_())?;
            let ctor = self.constructor(&ind.constructor_names[0])?;
            if ctor.num_fields != 1 {
                return Err(format!("{family}: unexpected hidden field"));
            }
            self.expected_type(
                &ctor.name,
                &pi(Expr::app(c("BitVec"), Expr::nat_lit(width)), c(family)),
            )?;
        }
        Ok(())
    }
}

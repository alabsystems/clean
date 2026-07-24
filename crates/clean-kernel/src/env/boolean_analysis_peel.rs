// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bonami-Beckner campaign — coordinate-peel extension maps.
//!
//! The B7 hypercontractivity induction peels the last coordinate of a cube
//! point: a function `F : HCPoint (n+1) → Rat` is reconstructed from its two
//! restrictions to the `b = false` / `b = true` halves. The structural
//! ingredient is the pair of **extension maps**
//!
//! ```text
//! BoolAnalysis.extendF (n : Nat) (x : HCPoint n) : HCPoint (n+1)
//! BoolAnalysis.extendT (n : Nat) (x : HCPoint n) : HCPoint (n+1)
//! ```
//!
//! `extendF n x` is the point of the `(n+1)`-cube whose first `n` coordinates
//! agree with `x` and whose last coordinate (`Fin.last n`) is `false`;
//! `extendT n x` is the same with last coordinate `true`. Both are built on the
//! constructive dependent eliminator `Fin.lastCases`, at the constant motive
//! `fun _ => Bool`:
//!
//! ```text
//! extendF n x := fun (j : Fin (n+1)) =>
//!   @Fin.lastCases n (fun _ => Bool) Bool.false x j
//! extendT n x := fun (j : Fin (n+1)) =>
//!   @Fin.lastCases n (fun _ => Bool) Bool.true  x j
//! ```
//!
//! The `cast` branch of `Fin.lastCases` has type `(i : Fin n) → motive
//! (Fin.castSucc n i)`, which at the constant motive is `(i : Fin n) → Bool` —
//! exactly `x : HCPoint n`, so `x` is passed directly with no wrapper. The
//! `last` branch supplies the appended bit.
//!
//! Both are reducible `Declaration::Definition`s — no axiom is added or removed.
//! Since `Fin.lastCases` is axiom-free (constructive), so are these.
//!
//! NOTE (run-7 residual): the pointwise computation rules
//!   `extendF n x (Fin.castSucc n i) = x i`,  `extendF n x (Fin.last n) = false`
//! (and the `extendT` mirror) are NOT defeq — `Fin.lastCases` reduces only when
//! the index's `Fin.val` is a literal (it dispatches through `Decidable.rec` on
//! `decEq (val j) n`). They require the `Fin.lastCases` ι-style computation
//! lemmas, which the codebase has not yet extracted as standalone theorems; see
//! the module note for the follow-on.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared constants for the peel extension maps.
struct PeelConsts {
    nat: Expr,
    bool_: Expr,
    nat_succ: Expr,
    fin: Expr,
    bool_false: Expr,
    bool_true: Expr,
    /// `@Fin.lastCases.{1}` — motive lands in `Sort 1` (Bool : Type 0 = Sort 1).
    fin_last_cases: Expr,
}

impl PeelConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            bool_: Expr::const_(Name::from_string("Bool"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            bool_false: Expr::const_(Name::from_string("Bool.false"), vec![]),
            bool_true: Expr::const_(Name::from_string("Bool.true"), vec![]),
            fin_last_cases: Expr::const_(Name::from_string("Fin.lastCases"), vec![l1]),
        }
    }

    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }

    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            n.clone(),
        )
    }

    fn succ(&self, n: &Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n.clone())
    }

    /// The constant motive `fun (_ : Fin (n+1)) => Bool`.
    fn const_bool_motive(&self, parent: &EnvDeclBuilder, n: &Expr) -> Expr {
        let mut c = EnvDeclBuilder::child_of(parent);
        let fin_succ_n = self.fin_of(&self.succ(n));
        let (j_id, _j) = c.fresh_local(fin_succ_n.clone());
        let lam = c.mk_lam(j_id, BinderInfo::Default, fin_succ_n, self.bool_.clone());
        c.finish_child(lam)
    }

    /// `(n : Nat) → HCPoint n → HCPoint (n+1)` — the shared type of both maps.
    fn extend_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(self.nat.clone());
        let (x_id, _x) = b.fresh_local(self.hcpoint_of(&n));
        let concl = self.hcpoint_of(&self.succ(&n));
        let e = b.mk_pi(x_id, BinderInfo::Default, self.hcpoint_of(&n), concl);
        let e = b.mk_pi(n_id, BinderInfo::Default, self.nat.clone(), e);
        b.finish(e)
    }

    /// `fun n x => fun (j : Fin (n+1)) =>
    ///     @Fin.lastCases n (fun _ => Bool) <bit> x j`.
    fn extend_value(&self, bit: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(self.nat.clone());
        let (x_id, x) = b.fresh_local(self.hcpoint_of(&n));

        let motive = self.const_bool_motive(&b, &n);
        let fin_succ_n = self.fin_of(&self.succ(&n));

        // body(j) := @Fin.lastCases.{1} n motive bit x j
        let body = {
            let mut c = EnvDeclBuilder::child_of(&b);
            let (j_id, j) = c.fresh_local(fin_succ_n.clone());
            let app = Expr::apps(
                self.fin_last_cases.clone(),
                [n.clone(), motive.clone(), bit.clone(), x.clone(), j],
            );
            let lam = c.mk_lam(j_id, BinderInfo::Default, fin_succ_n, app);
            c.finish_child(lam)
        };

        let e = b.mk_lam(x_id, BinderInfo::Default, self.hcpoint_of(&n), body);
        let e = b.mk_lam(n_id, BinderInfo::Default, self.nat.clone(), e);
        b.finish(e)
    }
}

impl Environment {
    /// Initialize the Bonami-Beckner coordinate-peel extension maps.
    ///
    /// Registers `BoolAnalysis.extendF` / `BoolAnalysis.extendT` as reducible
    /// `Declaration::Definition`s. Idempotent.
    ///
    /// Depends on the boolean-analysis foundations (`HCPoint`, `Bool`, `Fin`,
    /// `Fin.castSucc`/`Fin.last`) and the constructive `Fin.lastCases`
    /// eliminator. No axiom is added or removed.
    pub(crate) fn init_boolean_analysis_peel(&mut self) -> Result<(), EnvError> {
        if self.boolean_analysis_peel_init {
            return Ok(());
        }
        self.init_boolean_analysis_foundations()?;
        self.register_fin_last_cases()?;

        let c = PeelConsts::new();
        self.register_extend(&c, "BoolAnalysis.extendF", &c.bool_false)?;
        self.register_extend(&c, "BoolAnalysis.extendT", &c.bool_true)?;

        self.boolean_analysis_peel_init = true;
        Ok(())
    }

    fn register_extend(&mut self, c: &PeelConsts, name: &str, bit: &Expr) -> Result<(), EnvError> {
        let name = Name::from_string(name);
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: c.extend_type(),
            value: c.extend_value(bit),
            is_reducible: true,
        })
    }

    /// Whether the coordinate-peel extension maps have been initialized.
    pub(crate) fn has_boolean_analysis_peel(&self) -> bool {
        self.boolean_analysis_peel_init
    }
}

#[cfg(test)]
mod tests {
    use crate::env::types::ConstantKind;
    use crate::env::Environment;
    use crate::expr::{Expr, ExprKind};
    use crate::name::Name;
    use crate::tc::TypeChecker;

    const MAPS: &[&str] = &["BoolAnalysis.extendF", "BoolAnalysis.extendT"];

    fn env() -> Environment {
        let mut env = Environment::new();
        env.init_boolean_analysis_peel()
            .expect("init_boolean_analysis_peel should succeed");
        env
    }

    #[test]
    fn test_init_idempotent() {
        let mut env = Environment::new();
        env.init_boolean_analysis_peel().expect("first init");
        env.init_boolean_analysis_peel()
            .expect("second init should be a no-op");
        assert!(env.has_boolean_analysis_peel());
    }

    #[test]
    fn test_maps_registered_as_definitions() {
        let env = env();
        for name in MAPS {
            let info = env
                .get_const(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} should be registered"));
            assert_eq!(
                info.kind,
                ConstantKind::Definition,
                "{name} must be a reducible Definition, got {:?}",
                info.kind
            );
        }
    }

    #[test]
    fn test_maps_type_check_to_extension_arrow() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in MAPS {
            let e = Expr::const_(Name::from_string(name), vec![]);
            let ty = tc
                .infer_type(&e)
                .unwrap_or_else(|err| panic!("{name} should kernel-type-check, got: {err:?}"));
            assert!(
                matches!(ty.kind(), ExprKind::Pi(..)),
                "{name} type should be `(n) → HCPoint n → HCPoint (n+1)` Pi, got {:?}",
                ty.kind()
            );
        }
    }

    /// Both maps are axiom-free: `Fin.lastCases` and the foundations they build
    /// on have empty domain-axiom closure.
    #[test]
    fn test_maps_axiom_free() {
        let env = env();
        for name in MAPS {
            let deps = env
                .axiom_deps(&Name::from_string(name))
                .unwrap_or_else(|| panic!("axiom_deps should work for {name}"));
            let dep_names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
            assert!(
                dep_names.is_empty(),
                "{name} must have empty domain-axiom closure, got {dep_names:?}"
            );
        }
    }
}

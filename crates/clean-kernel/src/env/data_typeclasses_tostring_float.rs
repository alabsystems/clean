// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `Float.toString` and `instToStringFloat` for the builtin prelude (G27).
//!
//! Lean 4.8.0 (`src/Init/Data/Float.lean`) declares
//!
//! ```lean
//! @[extern "lean_float_to_string"] opaque Float.toString : Float → String
//! instance : ToString Float := ⟨Float.toString⟩
//! ```
//!
//! `Float.toString` is an `@[extern]` OPAQUE: its value is not definitional,
//! so pinned Lean refuses `toString (2.5 : Float) = "2.500000" := rfl`. The
//! prelude mirrors that exactly: the constant is a `Declaration::Opaque` (never
//! δ-unfolded, never an `Axiom`, so it adds nothing to `axiom_deps`) whose
//! type-correct placeholder body `fun _ => ""` no reduction ever reaches. The
//! native reducer registered under the same name
//! (`native_reducers_float.rs`, `reduce_float_to_string`) is NOT admitted by
//! the kernel: it has no `fold` row in `native_fold_canon.tsv` and the Lean
//! theory excludes the opaque-extern Float family
//! (`tc/fold_admission.rs::registry_reducer_admitted`). The refusal of the
//! `rfl` twin is pinned by
//! `float_tostring_rfl_stays_refused` below and by
//! `reports/trust-ir-semantics-probe/repros/G27-*`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{
    Declaration, EnvError, Environment, KernelInstanceInfo, LEAN_DEFAULT_INSTANCE_PRIORITY,
};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Declare the opaque `Float.toString : Float → String` and register
    /// `instToStringFloat : ToString Float := ⟨Float.toString⟩`.
    ///
    /// A cut-down environment without `Float`, `String` or `ToString` gets
    /// neither (the caller's other instances follow the same rule).
    pub(super) fn add_tostring_float_instance(&mut self) -> Result<(), EnvError> {
        let registered =
            |env: &Environment, n: &str| env.get_const(&Name::from_string(n)).is_some();
        if !registered(self, "Float")
            || !registered(self, "String")
            || !registered(self, "ToString")
        {
            return Ok(());
        }
        let float_const = Expr::const_(Name::from_string("Float"), vec![]);
        let string_const = Expr::const_(Name::from_string("String"), vec![]);
        let to_string_name = Name::from_string("Float.toString");

        let placeholder = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, _x) = b.fresh_local(float_const.clone());
            let e = b.mk_lam(
                x_id,
                BinderInfo::Default,
                float_const.clone(),
                Expr::str_lit(""),
            );
            b.finish(e)
        };
        self.add_decl_if_absent(Declaration::Opaque {
            name: to_string_name.clone(),
            level_params: vec![],
            type_: Expr::pi(BinderInfo::Default, float_const.clone(), string_const),
            value: placeholder,
        })?;

        let inst_name = Name::from_string("instToStringFloat");
        if self.get_const(&inst_name).is_some() {
            return Ok(());
        }
        let level = Level::zero();
        let ts_ty = Expr::app(
            Expr::const_(Name::from_string("ToString"), vec![level.clone()]),
            float_const.clone(),
        );
        let value = Expr::apps(
            Expr::const_(Name::from_string("ToString.mk"), vec![level]),
            [float_const, Expr::const_(to_string_name, vec![])],
        );
        self.add_decl(Declaration::Definition {
            name: inst_name.clone(),
            level_params: vec![],
            type_: ts_ty,
            value,
            is_reducible: true,
        })?;
        self.register_instance(KernelInstanceInfo {
            name: inst_name,
            class_name: Name::from_string("ToString"),
            priority: LEAN_DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::env::{ConstantKind, Environment};
    use crate::expr::Expr;
    use crate::name::Name;
    use crate::tc::TypeChecker;

    fn float_lit_2_5() -> Expr {
        // `Float.ofScientific 25 true 1` — the lowering of the literal `2.5`.
        Expr::apps(
            Expr::const_(Name::from_string("Float.ofScientific"), vec![]),
            [
                Expr::nat_lit(25),
                Expr::const_(Name::from_string("Bool.true"), vec![]),
                Expr::nat_lit(1),
            ],
        )
    }

    #[test]
    fn test_prelude_float_tostring_is_opaque_and_instance_registered() {
        let env = Environment::with_prelude();
        let c = env
            .get_const(&Name::from_string("Float.toString"))
            .expect("Float.toString must be declared by the builtin prelude");
        assert_eq!(
            c.kind,
            ConstantKind::Opaque,
            "Float.toString must be opaque (Lean 4.8: @[extern] opaque)"
        );
        assert!(
            env.get_const(&Name::from_string("instToStringFloat"))
                .is_some(),
            "instToStringFloat must be registered"
        );
        let deps = env
            .axiom_deps(&Name::from_string("instToStringFloat"))
            .expect("instToStringFloat axiom closure");
        assert!(
            deps.is_empty(),
            "instToStringFloat must be axiom-free, got {deps:?}"
        );
    }

    /// The negative twin of G27: `Float.toString 2.5` must NOT be definitionally
    /// `"2.500000"` (pinned Lean 4.8 refuses the `rfl`). The registered native
    /// reducer would compute exactly that string if it were admitted.
    #[test]
    fn float_tostring_rfl_stays_refused() {
        let env = Environment::with_prelude();
        let lhs = Expr::app(
            Expr::const_(Name::from_string("Float.toString"), vec![]),
            float_lit_2_5(),
        );
        let tc = TypeChecker::new(&env);
        assert!(
            !tc.is_def_eq(&lhs, &Expr::str_lit("2.500000")),
            "Float.toString must stay opaque to the kernel: the native reducer must not fire"
        );
        // Also through the bit-pattern constructor form the reducer reads directly.
        let bits = Expr::app(
            Expr::const_(Name::from_string("Float.mk"), vec![]),
            Expr::nat_lit(2.5_f64.to_bits()),
        );
        let lhs2 = Expr::app(
            Expr::const_(Name::from_string("Float.toString"), vec![]),
            bits,
        );
        let tc2 = TypeChecker::new(&env);
        assert!(
            !tc2.is_def_eq(&lhs2, &Expr::str_lit("2.500000")),
            "Float.toString (Float.mk bits) must not reduce under the builtin prelude"
        );
    }
}

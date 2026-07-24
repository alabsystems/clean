// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Fast synthetic tests for incremental environment kernel type-checking.
//!
//! These exercise the same incremental `Environment::add_decl` code path as
//! `verify_measurement_incremental`, but use hand-constructed kernel expressions
//! instead of real `.olean` files. This allows the test to run in <1 second
//! without any external toolchain dependency.
//!
//! The slow full-library version is gated behind `feature = "slow_tests"` in
//! `verify_measurement_incremental.rs`.

#[cfg(test)]
mod tests {
    use clean_kernel::expr::{BinderInfo, Expr};
    use clean_kernel::level::Level;
    use clean_kernel::{Declaration, Environment, Name};

    /// Test incremental axiom loading: later axioms depend on earlier ones.
    ///
    /// This mirrors the real Init module loading pattern where constants
    /// reference previously-declared constants.
    #[test]
    fn test_incremental_env_axiom_chain() {
        let mut env = Environment::new();

        // Pass 1: Load a chain of axioms where each references the previous.
        // Axiom A : Prop
        let decl_a = Declaration::Axiom {
            name: Name::from_string("A"),
            level_params: vec![],
            type_: Expr::prop(),
        };
        env.add_decl(decl_a).expect("axiom A should be accepted");

        // Axiom B : Prop
        let decl_b = Declaration::Axiom {
            name: Name::from_string("B"),
            level_params: vec![],
            type_: Expr::prop(),
        };
        env.add_decl(decl_b).expect("axiom B should be accepted");

        // Axiom f : A -> B  (depends on A and B being in env)
        let type_f = Expr::pi(
            BinderInfo::Default,
            Expr::const_(Name::from_string("A"), vec![]),
            Expr::const_(Name::from_string("B"), vec![]),
        );
        let decl_f = Declaration::Axiom {
            name: Name::from_string("f"),
            level_params: vec![],
            type_: type_f,
        };
        env.add_decl(decl_f)
            .expect("axiom f : A -> B should be accepted (A, B in env)");

        // Axiom g : B -> A  (depends on B and A being in env)
        let type_g = Expr::pi(
            BinderInfo::Default,
            Expr::const_(Name::from_string("B"), vec![]),
            Expr::const_(Name::from_string("A"), vec![]),
        );
        let decl_g = Declaration::Axiom {
            name: Name::from_string("g"),
            level_params: vec![],
            type_: type_g,
        };
        env.add_decl(decl_g)
            .expect("axiom g : B -> A should be accepted");
    }

    /// Test that axiom referencing an unknown constant fails (without the
    /// incremental environment, this is the dominant failure mode at ~99.67%).
    #[test]
    fn test_incremental_env_missing_constant_fails() {
        let mut env = Environment::new();

        // Try to add axiom that references non-existent constant
        let type_bad = Expr::pi(
            BinderInfo::Default,
            Expr::const_(Name::from_string("NonExistent"), vec![]),
            Expr::prop(),
        );
        let decl = Declaration::Axiom {
            name: Name::from_string("bad"),
            level_params: vec![],
            type_: type_bad,
        };
        let result = env.add_decl(decl);
        assert!(
            result.is_err(),
            "axiom referencing unknown constant should be rejected"
        );
    }

    /// Test incremental theorem verification after axiom loading.
    ///
    /// This mirrors the two-pass approach in verify_measurement_incremental:
    /// Pass 1 loads axioms, Pass 2 checks theorem values.
    #[test]
    fn test_incremental_env_theorem_after_axioms() {
        let mut env = Environment::new();

        // Pass 1: Load axiom
        let decl_a = Declaration::Axiom {
            name: Name::from_string("P"),
            level_params: vec![],
            type_: Expr::prop(),
        };
        env.add_decl(decl_a).expect("axiom P should be accepted");

        // Pass 2: Add a theorem P -> P with proof (fun h : P => h)
        // type = P -> P = Pi (P) P
        let thm_type = Expr::pi(
            BinderInfo::Default,
            Expr::const_(Name::from_string("P"), vec![]),
            Expr::const_(Name::from_string("P"), vec![]),
        );
        // value = fun (h : P) => h = Lam (P) (bvar 0)
        let thm_value = Expr::lam(
            BinderInfo::Default,
            Expr::const_(Name::from_string("P"), vec![]),
            Expr::bvar(0),
        );

        let thm_decl = Declaration::Theorem {
            name: Name::from_string("P_implies_P"),
            level_params: vec![],
            type_: thm_type,
            value: thm_value,
        };
        env.add_decl(thm_decl)
            .expect("theorem P -> P should be accepted with identity proof");
    }

    /// Test incremental loading with universe-polymorphic declarations.
    #[test]
    fn test_incremental_env_universe_polymorphic() {
        let mut env = Environment::new();

        let u = Name::from_string("u");

        // Axiom T : Sort u (a universe-polymorphic type)
        let decl_t = Declaration::Axiom {
            name: Name::from_string("T"),
            level_params: vec![u.clone()],
            type_: Expr::sort(Level::param(u.clone())),
        };
        env.add_decl(decl_t)
            .expect("axiom T : Sort u should be accepted");

        // Axiom mk : T.{u} (an element of T at any universe level)
        let decl_mk = Declaration::Axiom {
            name: Name::from_string("mk"),
            level_params: vec![u.clone()],
            type_: Expr::const_(Name::from_string("T"), vec![Level::param(u.clone())]),
        };
        env.add_decl(decl_mk)
            .expect("axiom mk : T.{u} should be accepted (T in env)");
    }

    /// Test definition (value + non-Prop type) in incremental mode.
    #[test]
    fn test_incremental_env_definition() {
        let mut env = Environment::new();

        // Axiom A : Prop
        let decl_a = Declaration::Axiom {
            name: Name::from_string("A"),
            level_params: vec![],
            type_: Expr::prop(),
        };
        env.add_decl(decl_a).expect("axiom A");

        // Definition id_A : A -> A := fun (x : A) => x
        let id_type = Expr::pi(
            BinderInfo::Default,
            Expr::const_(Name::from_string("A"), vec![]),
            Expr::const_(Name::from_string("A"), vec![]),
        );
        let id_value = Expr::lam(
            BinderInfo::Default,
            Expr::const_(Name::from_string("A"), vec![]),
            Expr::bvar(0),
        );

        let def_decl = Declaration::Definition {
            name: Name::from_string("id_A"),
            level_params: vec![],
            type_: id_type,
            value: id_value,
            is_reducible: true,
        };
        env.add_decl(def_decl)
            .expect("definition id_A : A -> A should be accepted");
    }

    /// Test that the incremental pattern handles a batch of constants,
    /// counting pass/fail like the real measurement test does.
    #[test]
    fn test_incremental_env_batch_counting() {
        let mut env = Environment::new();

        let mut axiom_pass = 0usize;
        let mut axiom_fail = 0usize;

        // Batch 1: Simple axioms that should all pass
        for i in 0..10 {
            let decl = Declaration::Axiom {
                name: Name::from_string(&format!("Const{i}")),
                level_params: vec![],
                type_: Expr::prop(),
            };
            match env.add_decl(decl) {
                Ok(()) => axiom_pass += 1,
                Err(_) => axiom_fail += 1,
            }
        }

        // Batch 2: Axioms referencing batch 1 (should pass in incremental mode)
        for i in 0..5 {
            let type_ref = Expr::pi(
                BinderInfo::Default,
                Expr::const_(Name::from_string(&format!("Const{i}")), vec![]),
                Expr::const_(Name::from_string(&format!("Const{}", i + 5)), vec![]),
            );
            let decl = Declaration::Axiom {
                name: Name::from_string(&format!("Arrow{i}")),
                level_params: vec![],
                type_: type_ref,
            };
            match env.add_decl(decl) {
                Ok(()) => axiom_pass += 1,
                Err(_) => axiom_fail += 1,
            }
        }

        // Batch 3: An axiom referencing unknown constant (should fail)
        let bad_decl = Declaration::Axiom {
            name: Name::from_string("BadRef"),
            level_params: vec![],
            type_: Expr::pi(
                BinderInfo::Default,
                Expr::const_(Name::from_string("DoesNotExist"), vec![]),
                Expr::prop(),
            ),
        };
        match env.add_decl(bad_decl) {
            Ok(()) => axiom_pass += 1,
            Err(_) => axiom_fail += 1,
        }

        // Verify counts
        assert_eq!(axiom_pass, 15, "expected 15 axioms accepted");
        assert_eq!(axiom_fail, 1, "expected 1 axiom rejected");

        // Pass 2: Theorem check on a subset
        let mut thm_pass = 0usize;
        let mut thm_fail = 0usize;

        // Theorem Const0 -> Const0 with identity proof (should pass)
        let thm = Declaration::Theorem {
            name: Name::from_string("id_Const0"),
            level_params: vec![],
            type_: Expr::pi(
                BinderInfo::Default,
                Expr::const_(Name::from_string("Const0"), vec![]),
                Expr::const_(Name::from_string("Const0"), vec![]),
            ),
            value: Expr::lam(
                BinderInfo::Default,
                Expr::const_(Name::from_string("Const0"), vec![]),
                Expr::bvar(0),
            ),
        };
        match env.add_decl(thm) {
            Ok(()) => thm_pass += 1,
            Err(_) => thm_fail += 1,
        }

        assert_eq!(thm_pass, 1, "expected 1 theorem verified");
        assert_eq!(thm_fail, 0, "expected 0 theorem failures");
    }
}

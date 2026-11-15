// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The final `false` across modes, transparencies and the `reduction-stats`
//! counter. Each pinned-Lean verdict quoted here is a file in
//! `reports/proof-irrel-three-valued-2026-10-17/`.

use super::{axiom_env, definition, eq_nat, fixture_env, konst, lam, lit, nat, refl_nat};
use crate::env::{Environment, Reducibility, TransparencyMode};
use crate::expr::{BinderInfo, Expr};
use crate::mode::CleanMode;
use crate::name::Name;
use crate::tc::TypeChecker;

#[test]
fn test_fibrant_modes_keep_proof_irrel_undecided() {
    let env = axiom_env();
    for mode in [CleanMode::Cubical, CleanMode::Directed] {
        let tc = TypeChecker::with_mode(&env, mode);
        assert_eq!(
            tc.is_def_eq_proof_irrel(&konst("Q"), &konst("R")),
            None,
            "{mode:?}: the fibrant layer never uses definitional proof irrelevance"
        );
    }
}

/// `MyEq n := n = n`, a family of propositions: `Nat → Prop`.
fn add_my_eq(env: &mut Environment, name: &str) {
    let my_eq = lam(nat(), eq_nat(Expr::bvar(0), Expr::bvar(0)));
    let my_eq_type = Expr::pi(BinderInfo::Default, nat(), Expr::prop());
    env.add_decl(definition(name, my_eq_type, my_eq, false))
        .expect("MyEq fixture");
}

/// `MyEq n := n = n` (semireducible) and `@[reducible] foo : MyEq 3 := rfl`.
/// Pinned Lean (`cc_<version>.txt`): `withReducible isDefEq foo (Eq.refl 3)`
/// and the `.instances` spelling are false (Meta's `isDefEqProofIrrel` is
/// final on `.false`); the default transparency and `Kernel.isDefEq` say true.
/// That holds under `backward.isDefEq.respectTransparency`'s default, true;
/// with it false Meta says true at all three (`RespectTransparency_<version>.txt`),
/// an option Clean does not model.
#[test]
fn test_proof_irrel_false_is_final_at_reducible_transparency_as_lean_meta() {
    let mut env = fixture_env();
    add_my_eq(&mut env, "MyEq");
    let foo_type = Expr::app(konst("MyEq"), lit(3));
    env.add_decl(definition("foo", foo_type, refl_nat(lit(3)), true))
        .expect("foo");
    let (foo, refl) = (konst("foo"), refl_nat(lit(3)));
    for transparency in [TransparencyMode::Reducible, TransparencyMode::Instances] {
        let mut tc = TypeChecker::new(&env);
        tc.set_transparency(transparency);
        tc.set_honor_reducibility(true);
        assert_eq!(tc.is_def_eq_proof_irrel(&foo, &refl), Some(false));
        assert!(
            !tc.is_def_eq(&foo, &refl),
            "{transparency:?}: `MyEq 3` and `3 = 3` differ here, so the proofs do"
        );
    }
    let tc = TypeChecker::new(&env);
    assert_eq!(tc.is_def_eq_proof_irrel(&foo, &refl), Some(true));
    assert!(
        tc.is_def_eq(&foo, &refl),
        "default transparency unfolds MyEq"
    );
}

/// `MyEqI n := n = n` and a semireducible `foo : MyEqI 3 := rfl`; then
/// `MyEqI` becomes `@[irreducible]`. At `Default` with reducibility honoured
/// (the elaborator's main checker), `MyEqI` stays folded, so the propositions
/// differ and the proofs are unequal at once, though `foo` itself would
/// unfold. Pinned Lean (`IrreducibleDefault_<version>.txt`): Meta at
/// `.default` says false, also with `backward.isDefEq.respectTransparency
/// false`; `.all` and `Kernel.isDefEq` say true.
#[test]
fn test_proof_irrel_false_is_final_at_default_transparency_over_an_irreducible_head() {
    let mut env = fixture_env();
    add_my_eq(&mut env, "MyEqI");
    let foo_type = Expr::app(konst("MyEqI"), lit(3));
    env.add_decl(definition("foo", foo_type, refl_nat(lit(3)), false))
        .expect("foo");
    assert!(env.set_reducibility(&Name::from_string("MyEqI"), Reducibility::Irreducible));
    let (foo, refl) = (konst("foo"), refl_nat(lit(3)));
    let mut tc = TypeChecker::new(&env);
    tc.set_transparency(TransparencyMode::Default);
    tc.set_honor_reducibility(true);
    assert_eq!(tc.is_def_eq_proof_irrel(&foo, &refl), Some(false));
    assert!(
        !tc.is_def_eq(&foo, &refl),
        "Default, honouring reducibility: `MyEqI 3` stays folded, so the proofs differ"
    );
    // Controls: `All` unfolds an irreducible head, and so does the kernel,
    // which never honours reducibility.
    for (transparency, honor) in [
        (TransparencyMode::All, true),
        (TransparencyMode::Default, false),
    ] {
        let mut tc = TypeChecker::new(&env);
        tc.set_transparency(transparency);
        tc.set_honor_reducibility(honor);
        assert_eq!(tc.is_def_eq_proof_irrel(&foo, &refl), Some(true));
        assert!(
            tc.is_def_eq(&foo, &refl),
            "{transparency:?}, honour {honor}: MyEqI unfolds"
        );
    }
}

/// One final `true` and one final `false` are counted apart from
/// "undecided" in the report's `proof-irrel:` line.
#[cfg(feature = "reduction-stats")]
#[test]
fn test_reduction_stats_counts_proof_irrel_false_apart_from_undecided() {
    use crate::tc::reduction_stats::{reduction_stats_report, reduction_stats_reset};
    let env = axiom_env();
    reduction_stats_reset();
    assert!(TypeChecker::new(&env).is_def_eq(&konst("P"), &konst("Q")));
    assert!(!TypeChecker::new(&env).is_def_eq(&konst("Q"), &konst("R")));
    let report = reduction_stats_report(0);
    let line = report
        .lines()
        .find_map(|line| line.strip_prefix("proof-irrel: "))
        .unwrap_or_else(|| panic!("no proof-irrel line in:\n{report}"));
    let counts: Vec<&str> = line.split(" / ").collect();
    assert_eq!(
        counts.get(..2),
        Some(&["1 true", "1 false"][..]),
        "proof-irrel: {line}"
    );
    assert!(
        counts.get(2).is_some_and(|none| none.ends_with(" none")),
        "proof-irrel: {line}"
    );
}

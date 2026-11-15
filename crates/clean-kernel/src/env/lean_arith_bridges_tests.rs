// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::env::lean_nat_spelling::LeanNat;
use crate::env::ConstantKind;
use crate::tc::TypeChecker;

fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

/// Every constant the module registers is in the DEFAULT prelude, is a
/// kernel-checked definition, and rests on no axiom.
#[test]
fn lean_arith_bridges_are_axiom_free_definitions_in_the_prelude() {
    let env = Environment::with_prelude();
    let mut names: Vec<String> = BRIDGES.iter().map(|b| b.0.to_owned()).collect();
    names.extend(["Nat.instDiv", "Nat.instMod", "Div.div", "Mod.mod"].map(str::to_owned));
    for ty in UINTS {
        names.push(format!("instDiv{ty}"));
        names.push(format!("{ty}.instOfNat"));
    }
    for name in names {
        let ci = env
            .get_const(&Name::from_string(&name))
            .unwrap_or_else(|| panic!("{name} must be in the default prelude"));
        assert_eq!(
            ci.kind,
            ConstantKind::Definition,
            "{name} must be a Definition"
        );
        let deps = env
            .axiom_deps(&Name::from_string(&name))
            .unwrap_or_else(|| panic!("{name}: axiom_deps None"));
        assert!(deps.is_empty(), "{name} rests on {deps:?}");
    }
}

/// The Lean spellings COMPUTE: `7 / 2` through `instHDiv Nat Nat.instDiv` is
/// `3`, `7 % 2` through `instHMod Nat Nat.instMod` is `1`, and
/// `(OfNat.ofNat UInt8 300 (UInt8.instOfNat 300)).toNat` is `300 % 256 = 44`.
/// Controls: a wrong value is refused each time.
#[test]
fn lean_arith_spellings_compute_to_the_bare_functions() {
    let env = Environment::with_prelude();
    let tc = TypeChecker::new(&env);
    let lit = Expr::nat_lit;
    let div = LeanNat::div(lit(7), lit(2));
    assert!(tc.is_def_eq(&div, &lit(3)), "7 / 2 must be 3");
    assert!(!tc.is_def_eq(&div, &lit(4)), "7 / 2 must not be 4");
    let modulo = LeanNat::modulo(lit(7), lit(2));
    assert!(tc.is_def_eq(&modulo, &lit(1)), "7 % 2 must be 1");
    assert!(!tc.is_def_eq(&modulo, &lit(0)), "7 % 2 must not be 0");
    let add = LeanNat::add(lit(2), lit(3));
    assert!(tc.is_def_eq(&add, &lit(5)), "2 + 3 must be 5");
    let mul = LeanNat::mul(lit(2), lit(3));
    assert!(tc.is_def_eq(&mul, &lit(6)), "2 * 3 must be 6");

    let u8_ = c("UInt8");
    let of_nat = Expr::apps(
        Expr::const_(Name::from_string("OfNat.ofNat"), vec![Level::zero()]),
        [u8_, lit(300), Expr::app(c("UInt8.instOfNat"), lit(300))],
    );
    let to_nat = Expr::app(c("UInt8.toNat"), of_nat);
    assert!(
        tc.is_def_eq(&to_nat, &lit(44)),
        "(300 : UInt8).toNat must be 44"
    );
    assert!(!tc.is_def_eq(&to_nat, &lit(300)), "UInt8 must wrap");
}

/// The new Lean-core instance constants are NOT registered with the resolver:
/// `/` at `Nat` keeps elaborating through `instHDivNat` (module doc).
#[test]
fn lean_arith_instances_do_not_enter_the_resolver() {
    let env = Environment::with_prelude();
    for name in [
        "Nat.instDiv",
        "Nat.instMod",
        "instHDiv",
        "instHMod",
        "instDivUInt8",
    ] {
        assert!(
            !env.is_instance(&Name::from_string(name)),
            "{name} must not be a registered instance"
        );
    }
}

/// Import mode withholds them all; the genuine Lean declarations import.
#[test]
fn import_prelude_withholds_the_lean_arith_bridges() {
    let env = Environment::try_with_prelude_for_import().expect("import prelude must build");
    for name in ["instHDiv", "Nat.instDiv", "UInt8.instOfNat", "instDivUInt8"] {
        assert!(
            env.get_const(&Name::from_string(name)).is_none(),
            "{name} must NOT be seeded in the import prelude"
        );
    }
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The Lean-world pin battery for native-fold authority
//! (`clean_kernel::env::native_fold_authority`, table
//! `crates/clean-kernel/src/env/native_fold_canon.tsv`).
//!
//! A name-keyed kernel fold (`reduce_nat`, `reduce_int`, the registered native
//! reducers, `Lean.reduceBool`, string literals) fires only when the
//! environment's definition of its head has a δ-closure digest the kernel holds
//! as canonical. For Lean's own definitions those digests are minted HERE, from
//! the pinned toolchain's `Init` decoded exactly as the re-check lanes decode it
//! (`Environment::for_lean_replay` + `load_module_with_deps`), and the mixed
//! world `clean check --imports-prefer-olean` builds (the import-mode prelude
//! under the same `Init`). Every minted row is REVIEWED
//! (`clean_kernel::env::native_fold_review`): a row whose own rules agree with
//! Lean's definition three ways is pinned `fold`, a row a `fold` row needs is
//! pinned `definition` (its closure is known, its rules stay off), the rest
//! are unpinned. The battery fails when the pinned rows and a fresh reviewed
//! mint disagree; `CLEAN_NATIVE_FOLD_REPIN=1` rewrites that world's rows.
//!
//! Before the review (measured 2026-09-28) every minted row was pinned, which
//! turned on `String.drop`'s and `String.take`'s reducers over Lean 4.30's
//! `Init`, where both return a `String.Slice` that remembers its string:
//! `String.drop "abc" 1 = String.drop "xbc" 1` checked by `rfl` in the default
//! theory, in both worlds. [`test_lean_string_drop_take_slices_are_not_identified`]
//! is that attack.
//!
//! It also pins COMPLETENESS where it matters most: Lean's `Nat.gcd` is
//! well-founded recursion, so without its fold `Nat.gcd` on literals of any
//! size is a `WellFounded.fix` unwinding, and the `decide`/`norm_num` proofs
//! Mathlib states over it stop checking.

use std::path::Path;

use clean_kernel::env::Environment;
use clean_kernel::expr::Expr;
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::tc::TypeChecker;
use clean_olean::load_module_with_deps;

#[path = "support/fold_canon.rs"]
mod fold_canon;
use fold_canon::{check_world, mint_reviewed, repin_requested};

/// The pinned toolchain (`lean-toolchain`); its `Init` is the one every
/// `.olean` re-check lane and `clean check` import.
const PINNED: &str = "v4.30.0-rc2";

/// The pinned toolchain's `lib/lean`, through the repository's own locator
/// (`clean_olean::require_pinned_lean_lib_path`: `CLEAN_OLEAN_PINNED_LEAN_LIB`,
/// `$ELAN_HOME`, `~/.elan`, then `elan run`), never a fixed `~/.elan` path.
/// The locator answers only for the workspace pin, so the directory it returns
/// must be `PINNED`'s.
fn pinned_lib() -> std::path::PathBuf {
    pinned_lib_for(PINNED)
}

fn pinned_lib_for(version: &str) -> std::path::PathBuf {
    // A workspace pin move must not mint new Init under an old world's name.
    let expected_toolchain = format!("leanprover/lean4:{version}");
    assert_eq!(
        include_str!("../../../lean-toolchain").trim(),
        expected_toolchain,
        "native-fold world's version must match the workspace Lean pin"
    );
    if let Some(compiled_toolchain) = option_env!("CLEAN_OLEAN_PINNED_LEAN_TOOLCHAIN") {
        assert_eq!(
            compiled_toolchain, expected_toolchain,
            "native-fold world's version must match the compiled Lean pin"
        );
    }
    let lib = clean_olean::require_pinned_lean_lib_path()
        .unwrap_or_else(|e| panic!("{e} (this battery pins lean-{version})"));
    let toolchain_dir = lib
        .parent()
        .and_then(Path::parent)
        .and_then(Path::file_name)
        .map(|n| n.to_string_lossy().into_owned())
        .unwrap_or_default();
    assert!(
        toolchain_dir.ends_with(&format!("---{version}")),
        "the workspace pin moved off {version} ({toolchain_dir}); re-mint this battery's worlds"
    );
    lib
}

fn load_init(mut env: Environment, lib: &Path) -> Environment {
    assert!(
        lib.join("Init/Prelude.olean").is_file(),
        "no Init at {}",
        lib.display()
    );
    let load = |env: &mut Environment| {
        load_module_with_deps(env, "Init", &[lib.to_path_buf()])
            .unwrap_or_else(|e| panic!("load Init ({}): {e}", lib.display()));
    };
    // Loaded under the COMPILED table, re-pin or not: the environment the
    // re-check lanes build is the one to pin, and it depends on the table —
    // a proof `Init` stores that a refused fold used to break loads as a
    // theorem, not as an axiom fallback. Measured 2026-09-29: loaded with every
    // fold by name (the mint bypass), `utf8DecodeChar?.assemble₂._proof_3` and
    // `…assemble₃._proof_7` fall back to axioms, so `String.length`,
    // `String.front` and `String.get` mint no row (259 rows); under the table
    // they are theorems and those heads mint (267 rows). Only the FIRST mint of
    // a new world, whose `Nat` heads have no row yet, needs the bypass load:
    // `CLEAN_NATIVE_FOLD_BOOTSTRAP_LOAD=1`, then re-pin again without it.
    if repin_requested() && std::env::var_os("CLEAN_NATIVE_FOLD_BOOTSTRAP_LOAD").is_some() {
        clean_kernel::env::native_fold_mint_bypass::run(|| load(&mut env));
    } else {
        load(&mut env);
    }
    env
}

fn nat() -> Expr {
    Expr::const_(Name::from_string("Nat"), vec![])
}

/// `rfl : lhs = rhs` at `Nat`.
fn nat_rfl(env: &Environment, lhs: Expr, rhs: Expr) -> bool {
    let eq = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [nat(), lhs, rhs.clone()],
    );
    let refl = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [nat(), rhs],
    );
    TypeChecker::new(env).check_type(&refl, &eq).is_ok()
}

#[test]
fn test_lean_init_fold_digests_are_pinned() {
    let world = format!("lean-{PINNED}");
    let env = load_init(Environment::for_lean_replay(), &pinned_lib());
    check_world(&world, &mint_reviewed(&world, &env));
    if repin_requested() {
        // The compiled table is the one this binary was built with; the
        // completeness checks below need the re-pinned one (rebuild, rerun).
        // `check_world` has already re-pinned, so a re-pin run ends RED
        // rather than reporting `ok` with nothing measured.
        panic!(
            "CLEAN_NATIVE_FOLD_REPIN is set: lean-{PINNED} rows re-pinned (if they drifted) but the completeness checks were NOT run against the compiled table; rebuild and rerun without CLEAN_NATIVE_FOLD_REPIN"
        );
    }
    // Completeness: Lean's own `Nat.gcd` (well-founded) and the rest of the
    // `reduce_nat` heads fold over the pinned Init, at sizes δ cannot reach.
    for head in [
        "Nat.add",
        "Nat.sub",
        "Nat.mul",
        "Nat.div",
        "Nat.mod",
        "Nat.gcd",
        "Nat.pow",
        "Nat.beq",
        "Nat.ble",
        "Nat.land",
        "Nat.lor",
        "Nat.xor",
        "Nat.shiftLeft",
        "Nat.shiftRight",
    ] {
        assert!(
            env.native_fold_authorized(&Name::from_string(head)),
            "{head} must fold over Lean's Init: {:?}",
            env.native_fold_verdict(&Name::from_string(head))
        );
    }
    let big = 1u64 << 40;
    let gcd = Expr::apps(
        Expr::const_(Name::from_string("Nat.gcd"), vec![]),
        [Expr::nat_lit(big * 6), Expr::nat_lit(big * 4)],
    );
    assert!(
        nat_rfl(&env, gcd, Expr::nat_lit(big * 2)),
        "Nat.gcd (6·2^40) (4·2^40) = 2^41"
    );
}

#[test]
fn test_mixed_import_prelude_fold_digests_are_pinned() {
    let world = format!("clean-import+lean-{PINNED}");
    let base = Environment::try_with_prelude_for_import().expect("import-mode prelude");
    let env = load_init(base, &pinned_lib());
    check_world(&world, &mint_reviewed(&world, &env));
}

fn mixed_env() -> Environment {
    let base = Environment::try_with_prelude_for_import().expect("import-mode prelude");
    load_init(base, &pinned_lib())
}

/// `rfl : lhs = rhs` at the type of `lhs`, in the environment's own (default,
/// `Extended`) theory; the kernel's error when it does not check.
fn rfl_default(env: &Environment, lhs: &Expr, rhs: &Expr) -> Result<(), String> {
    let tc = TypeChecker::new(env);
    let ty = tc.infer_type(lhs).map_err(|e| format!("{e:?}"))?;
    let sort = tc.whnf(&tc.infer_type(&ty).map_err(|e| format!("{e:?}"))?);
    let clean_kernel::expr::ExprKind::Sort(level) = sort.kind() else {
        return Err(format!("not a sort: {sort:?}"));
    };
    let eq = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![level.clone()]),
        [ty.clone(), lhs.clone(), rhs.clone()],
    );
    let refl = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![level.clone()]),
        [ty, rhs.clone()],
    );
    tc.check_type(&refl, &eq).map_err(|e| {
        let s = format!("{e:?}");
        s.chars().take(200).collect()
    })
}

fn app2(head: &str, a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string(head), vec![]), [a, b])
}

/// The finding (2026-09-28): over Lean 4.30's `Init`, in the DEFAULT theory,
/// `String.drop`/`String.take` folded to a `String` literal, while Lean's
/// definitions return a `String.Slice` that remembers the string it was cut
/// from — so slices of DIFFERENT strings were identified. Measured ACCEPTED on
/// `origin/main` (`bd68da97a`) in both the replay world and the mixed world
/// `clean check --imports-prefer-olean` builds. Each attack has a positive
/// control: a reviewed `String` fold still fires in the same environment.
#[test]
fn test_lean_string_drop_take_slices_are_not_identified() {
    let s = Expr::str_lit;
    let lit = Expr::nat_lit;
    for (label, env) in [
        (
            "lean-v4.30.0-rc2",
            load_init(Environment::for_lean_replay(), &pinned_lib()),
        ),
        ("clean-import+lean-v4.30.0-rc2", mixed_env()),
    ] {
        for (what, lhs, rhs) in [
            (
                "String.drop \"abc\" 1 = String.drop \"xbc\" 1",
                app2("String.drop", s("abc"), lit(1)),
                app2("String.drop", s("xbc"), lit(1)),
            ),
            (
                "String.take \"abc\" 2 = String.take \"abx\" 2",
                app2("String.take", s("abc"), lit(2)),
                app2("String.take", s("abx"), lit(2)),
            ),
            (
                "String.drop \"abc\" 0 = String.drop \"xabc\" 1",
                app2("String.drop", s("abc"), lit(0)),
                app2("String.drop", s("xabc"), lit(1)),
            ),
        ] {
            assert!(
                rfl_default(&env, &lhs, &rhs).is_err(),
                "ATTACK ACCEPTED ({label}): {what} by rfl — two slices of different strings identified"
            );
        }
        for head in ["String.drop", "String.take"] {
            assert!(
                !env.native_fold_authorized(&Name::from_string(head)),
                "{label}: {head}'s reducer must not fire over Lean 4.30's definition: {:?}",
                env.native_fold_verdict(&Name::from_string(head))
            );
        }
        // Positive control: a reviewed String fold, and Lean's own slice
        // definition still computes (δι, no reducer) the slice's copy.
        rfl_default(&env, &app2("String.append", s("ab"), s("cd")), &s("abcd"))
            .unwrap_or_else(|e| panic!("{label}: String.append \"ab\" \"cd\" = \"abcd\": {e}"));
        assert!(
            env.native_fold_authorized(&Name::from_string("String.append")),
            "{label}: String.append must still fold"
        );
        let copy = Expr::app(
            Expr::const_(Name::from_string("String.Slice.copy"), vec![]),
            app2("String.drop", s("abc"), lit(1)),
        );
        rfl_default(&env, &copy, &s("bc"))
            .unwrap_or_else(|e| panic!("{label}: (String.drop \"abc\" 1).copy = \"bc\": {e}"));
    }
}

/// `BitVec.ofNat`'s reducer returns a raw `Nat` payload where Lean's
/// definition returns a `BitVec` constructor. No false acceptance was found
/// (distinct values stay distinct), but the payload is not a `BitVec`, so a
/// Lean-TRUE equation between `BitVec.ofNat 8 5` and the constructor form was
/// REFUSED in the default theory on `origin/main`. Its row is now
/// `definition`: the reducer is off, the closure still reads as the literal
/// carrier the reviewed `BitVec` comparisons consume.
#[test]
fn test_lean_bitvec_of_nat_is_a_carrier_not_a_fold() {
    let env = load_init(Environment::for_lean_replay(), &pinned_lib());
    let lit = Expr::nat_lit;
    let c = |s: &str| Expr::const_(Name::from_string(s), vec![]);
    let of_nat = |v: u64| app2("BitVec.ofNat", lit(8), lit(v));
    // `@BitVec.ofFin 8 (@Fin.mk 256 5 (of_decide_eq_true rfl))`.
    let lt = Expr::apps(
        Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]),
        [nat(), c("instLTNat"), lit(5), lit(256)],
    );
    let proof = Expr::apps(
        c("of_decide_eq_true"),
        [
            lt,
            app2("Nat.decLt", lit(5), lit(256)),
            Expr::apps(
                Expr::const_(
                    Name::from_string("Eq.refl"),
                    vec![Level::succ(Level::zero())],
                ),
                [c("Bool"), c("Bool.true")],
            ),
        ],
    );
    let ctor = Expr::apps(
        c("BitVec.ofFin"),
        [lit(8), Expr::apps(c("Fin.mk"), [lit(256), lit(5), proof])],
    );
    rfl_default(&env, &of_nat(5), &ctor)
        .unwrap_or_else(|e| panic!("BitVec.ofNat 8 5 = BitVec.ofFin ⟨5, _⟩ (true in Lean): {e}"));
    rfl_default(&env, &of_nat(261), &of_nat(5)).expect("BitVec.ofNat 8 261 = BitVec.ofNat 8 5");
    assert!(
        rfl_default(&env, &of_nat(5), &of_nat(6)).is_err(),
        "BitVec.ofNat 8 5 = BitVec.ofNat 8 6 must be refused"
    );
    assert!(!env.native_fold_authorized(&Name::from_string("BitVec.ofNat")));
    assert!(env.native_fold_definition_admitted(&Name::from_string("BitVec.ofNat")));
}

#[test]
#[should_panic(expected = "native-fold world's version must match the workspace Lean pin")]
fn test_native_fold_world_rejects_wrong_version_before_import() {
    let _ = pinned_lib_for("v0.0.0-invalid");
}

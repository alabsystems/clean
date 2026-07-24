// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for sound mutual structural recursion via product packing
//! (Track H, task 2).
//!
//! Beyond end-to-end elaboration, these enforce the wave's RIGOROUS soundness
//! bar for the new kernel terms: every synthesized constant (the packed
//! function and each projection wrapper) must `infer_type` successfully AND
//! have an EMPTY `axiom_deps` closure — proving no `WellFounded.fix`-with-sorry
//! or faked termination axiom leaked through. The `rfl` checks force the kernel
//! to reduce the lowered (single, structural) `T.rec` application across the
//! mutual cycle.

use crate::elaborate_decl_and_register;
use clean_kernel::{Environment, Name, TypeChecker};
use clean_parser::parse_file;

fn elab_all(code: &str) -> Environment {
    let mut env = Environment::with_prelude();
    let decls = parse_file(code).expect("should parse");
    for (i, decl) in decls.iter().enumerate() {
        if let clean_parser::SurfaceDecl::RawDecl { content, span } = decl {
            panic!("decl {i} fell through to RawDecl: content={content:?}, span={span:?}");
        }
        elaborate_decl_and_register(&mut env, decl)
            .unwrap_or_else(|e| panic!("decl {i} failed to elaborate: {e:?}"));
    }
    env
}

fn assert_sound_const(env: &Environment, name: &str) {
    let n = Name::from_string(name);
    let info = env
        .get_const(&n)
        .unwrap_or_else(|| panic!("{name} should be registered"));
    let value = info
        .value
        .as_ref()
        .unwrap_or_else(|| panic!("{name} should be a definition with a value"));
    let tc = TypeChecker::new(env);
    let inferred = tc
        .infer_type(value)
        .unwrap_or_else(|e| panic!("infer_type({name}.value) failed: {e:?}"));
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "{name}: inferred value type not def-eq to declared type"
    );
    let deps = env
        .axiom_deps(&n)
        .unwrap_or_else(|| panic!("{name} registered, axiom_deps should return Some"));
    let dep_names: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
    assert!(
        dep_names.is_empty(),
        "{name} must have EMPTY axiom closure (sound structural pack), got {dep_names:?}"
    );
}

const EVEN_ODD_SRC: &str = r#"
mutual
  def isEven : Nat -> Bool
    | 0 => true
    | Nat.succ n => isOdd n
  def isOdd : Nat -> Bool
    | 0 => false
    | Nat.succ n => isEven n
end
"#;

#[test]
fn test_mutual_even_odd_registers_pack_and_wrappers() {
    let env = elab_all(EVEN_ODD_SRC);
    assert!(env.get_const(&Name::from_string("isEven")).is_some());
    assert!(env.get_const(&Name::from_string("isOdd")).is_some());
    assert!(
        env.get_const(&Name::from_string("isEven.isOdd.pack"))
            .is_some(),
        "packed structural function should be registered"
    );
}

#[test]
fn test_mutual_even_odd_soundness() {
    let env = elab_all(EVEN_ODD_SRC);
    // Packed structural function and BOTH projection wrappers must be
    // well-typed with no axiom dependency.
    assert_sound_const(&env, "isEven.isOdd.pack");
    assert_sound_const(&env, "isEven");
    assert_sound_const(&env, "isOdd");
}

#[test]
fn test_mutual_even_odd_computes_via_kernel_rfl() {
    let code = r#"
mutual
  def isEven : Nat -> Bool
    | 0 => true
    | Nat.succ n => isOdd n
  def isOdd : Nat -> Bool
    | 0 => false
    | Nat.succ n => isEven n
end

theorem ev0 : isEven 0 = true := rfl
theorem ev4 : isEven 4 = true := rfl
theorem ev3 : isEven 3 = false := rfl
theorem od3 : isOdd 3 = true := rfl
theorem od0 : isOdd 0 = false := rfl
"#;
    let env = elab_all(code);
    for thm in ["ev0", "ev4", "ev3", "od3", "od0"] {
        let deps = env
            .axiom_deps(&Name::from_string(thm))
            .unwrap_or_else(|| panic!("{thm} should be registered"));
        assert!(
            deps.is_empty(),
            "{thm} rfl proof must have empty axiom closure, got {:?}",
            deps.iter().map(|d| d.to_string()).collect::<Vec<_>>()
        );
    }
}

#[test]
fn test_mutual_three_way_mod3_soundness_and_compute() {
    let code = r#"
mutual
  def isZeroMod3 : Nat -> Bool
    | 0 => true
    | Nat.succ n => isTwoMod3 n
  def isOneMod3 : Nat -> Bool
    | 0 => false
    | Nat.succ n => isZeroMod3 n
  def isTwoMod3 : Nat -> Bool
    | 0 => false
    | Nat.succ n => isOneMod3 n
end

theorem z6 : isZeroMod3 6 = true := rfl
theorem o4 : isOneMod3 4 = true := rfl
theorem t5 : isTwoMod3 5 = true := rfl
"#;
    let env = elab_all(code);
    assert_sound_const(&env, "isZeroMod3.isOneMod3.isTwoMod3.pack");
    assert_sound_const(&env, "isZeroMod3");
    assert_sound_const(&env, "isOneMod3");
    assert_sound_const(&env, "isTwoMod3");
    for thm in ["z6", "o4", "t5"] {
        assert!(
            env.get_const(&Name::from_string(thm)).is_some(),
            "{thm} should kernel-check"
        );
    }
}

#[test]
fn test_mutual_over_user_inductive_soundness() {
    let code = r#"
inductive Lst where
  | nil : Lst
  | cons : Nat -> Lst -> Lst

mutual
  def countA : Lst -> Nat
    | Lst.nil => 0
    | Lst.cons _ t => Nat.succ (countB t)
  def countB : Lst -> Nat
    | Lst.nil => 0
    | Lst.cons _ t => countA t
end

theorem ca3 : countA (Lst.cons 1 (Lst.cons 2 (Lst.cons 3 Lst.nil))) = 2 := rfl
"#;
    let env = elab_all(code);
    assert_sound_const(&env, "countA.countB.pack");
    assert_sound_const(&env, "countA");
    assert_sound_const(&env, "countB");
    assert!(env.get_const(&Name::from_string("ca3")).is_some());
}

/// A mutual block of THEOREMS (not packable defs) must be LEFT to the existing
/// `elab_mutual` path — the desugar must decline and synthesize no `.pack`.
#[test]
fn test_mutual_theorems_not_packed() {
    let code = r#"
mutual
  theorem ta : True := True.intro
  theorem tb : True := True.intro
end
"#;
    let env = elab_all(code);
    assert!(env.get_const(&Name::from_string("ta")).is_some());
    assert!(env.get_const(&Name::from_string("tb")).is_some());
    assert!(
        env.get_const(&Name::from_string("ta.tb.pack")).is_none(),
        "theorem mutual block must NOT be product-packed"
    );
}

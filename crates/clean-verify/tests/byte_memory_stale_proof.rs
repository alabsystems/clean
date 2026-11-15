// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Reduced regression for checking a retained proof against changed byte memory.
//! Uses the real byte vocabulary; no TY model, authored memory semantics or new
//! assumptions. A changed reflexive proposition is true, but the old proof is
//! not its witness. Resource exhaustion cannot count as that rejection.

use clean_kernel::{BinderInfo, Environment, Expr, KernelTypeError, Level, Name, TypeChecker};
use clean_verify::eval_ir::build_byte_prelude_spec_v1_with_stack;

const LANES: [u64; 5] = [64, 33, u64::MAX, 23, u64::MAX];

fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn app(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(c(name), Expr::app)
}

fn option_nat() -> Expr {
    app("IROption", [c("Nat")])
}

fn memory(lanes: [u64; 5]) -> Expr {
    let empty = Expr::lam(
        BinderInfo::Default,
        c("Nat"),
        app("IROption.none", [c("Nat")]),
    );
    lanes
        .into_iter()
        .enumerate()
        .fold(empty, |bytes, (index, word)| {
            app(
                "ir_byte_write_word_v1",
                [
                    bytes,
                    Expr::nat_lit(128 + index as u64 * 8),
                    Expr::nat_lit(8),
                    Expr::nat_lit(word),
                ],
            )
        })
}

fn eq(ty: Expr, left: Expr, right: Expr) -> Expr {
    [ty, left, right].into_iter().fold(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        Expr::app,
    )
}

fn refl(ty: Expr, value: Expr) -> Expr {
    [ty, value].into_iter().fold(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        Expr::app,
    )
}

fn checker(env: &Environment) -> TypeChecker<'_> {
    let mut checker = TypeChecker::new(env);
    checker.set_heartbeat_limit(2_000_000);
    checker.set_max_cache_entries(100_000);
    checker
}

fn accept(env: &Environment, proof: &Expr, claim: &Expr) {
    let checker = checker(env);
    checker
        .check_type(claim, &Expr::prop())
        .expect("claim is a proposition");
    checker
        .check_type(proof, claim)
        .expect("own or concrete proof replays");
    assert!(!checker.heartbeat_spent());
}

fn reject(env: &Environment, proof: &Expr, claim: &Expr) {
    let checker = checker(env);
    checker
        .check_type(claim, &Expr::prop())
        .expect("changed claim remains a proposition");
    let result = checker.check_type(proof, claim);
    assert!(
        !checker.heartbeat_spent(),
        "a resource failure is not a rejection witness"
    );
    assert!(
        matches!(result, Err(KernelTypeError::TypeMismatch { .. })),
        "expected a type mismatch, not success or a different checker failure"
    );
}

#[test]
fn byte_memory_rejects_original_proof_for_each_changed_reflexive_claim() {
    eprintln!("byte-memory: build production vocabulary");
    let spec = build_byte_prelude_spec_v1_with_stack().expect("production byte vocabulary");
    let env = spec.env();
    let ty = Expr::arrow(c("Nat"), option_nat());
    let original = memory(LANES);
    let proof = refl(ty.clone(), original.clone());
    eprintln!("byte-memory: original reflexivity");
    accept(env, &proof, &eq(ty.clone(), original.clone(), original));
    for index in 0..LANES.len() {
        let mut changed = LANES;
        changed[index] ^= 1;
        let bytes = memory(changed);
        let claim = eq(ty.clone(), bytes.clone(), bytes.clone());
        eprintln!("byte-memory: lane={index} changed reflexivity");
        accept(env, &refl(ty.clone(), bytes), &claim);
        eprintln!("byte-memory: lane={index} original-proof rejection");
        reject(env, &proof, &claim);
        eprintln!("byte-memory: lane={index} rejection complete");
    }
}

#[test]
fn byte_memory_concrete_reads_observe_all_five_independently_changed_words() {
    let spec = build_byte_prelude_spec_v1_with_stack().expect("production byte vocabulary");
    let env = spec.env();
    let original = memory(LANES);
    for changed_index in 0..LANES.len() {
        let mut changed = LANES;
        changed[changed_index] ^= 1;
        let bytes = memory(changed);
        for index in 0..LANES.len() {
            eprintln!("byte-read: changed={changed_index} observed={index}");
            let read = |memory| {
                app(
                    "ir_byte_read_word_v1",
                    [
                        memory,
                        Expr::nat_lit(8),
                        Expr::nat_lit(128 + index as u64 * 8),
                    ],
                )
            };
            let expected = |word| app("IROption.some", [c("Nat"), Expr::nat_lit(word)]);
            let old_value = expected(LANES[index]);
            let new_value = expected(changed[index]);
            accept(
                env,
                &refl(option_nat(), old_value.clone()),
                &eq(option_nat(), read(original.clone()), old_value.clone()),
            );
            accept(
                env,
                &refl(option_nat(), new_value.clone()),
                &eq(option_nat(), read(bytes.clone()), new_value),
            );
            if index == changed_index {
                reject(
                    env,
                    &refl(option_nat(), old_value.clone()),
                    &eq(option_nat(), read(bytes.clone()), old_value),
                );
            }
        }
    }
}

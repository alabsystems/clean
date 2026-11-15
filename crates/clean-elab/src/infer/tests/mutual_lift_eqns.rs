// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Gap G23 / ledger class (92), brick B3: equations of lifted `mutual`
//! members — `simp [f]` / `simp only [f] at h` through the per-constructor
//! equations the lift records (`infer/mutual_lift/eqns.rs`), `rw [f.eq_N]`
//! through the named lemmas minted per source arm (`infer/mutual_lift/arms.rs`),
//! and the three Lean core lemmas the blocks' proofs name
//! (`clean-kernel/src/env/logic_eq_true_props.rs`).
//!
//! Fixtures and verdicts as in `mutual_lift.rs` (`tests/fixtures/mutual_nested/`,
//! `verdicts.json` re-derived from the pinned Lean binaries). Every accepted
//! shape carries a Lean-refused twin.

use super::mutual_lift_tests::{
    accepts_all, fixture, fresh, lean_accepts, refuses_last, registered, run_file,
};
use super::*;
use clean_kernel::env::Environment;

/// The recorded per-constructor equations of `member`.
fn equations(env: &mut Environment, member: &str) -> Vec<Expr> {
    env.get_ext_state_or_init::<crate::MutualLiftState>(crate::mutual_lift_idx())
        .and_then(|state| state.get(&Name::from_string(member)).cloned())
        .unwrap_or_else(|| panic!("`{member}` has a registry entry"))
        .equations
}

/// Every member has one equation per constructor of its major premise's type,
/// and no equation names a recursor (`T.rec`, `T.rec_N`, what a lifted value
/// applies): the right-hand sides are surface form. A case split the source
/// makes on ANOTHER column stays a `casesOn` there, as it does in the
/// structural synthesis, and simp's iota reduces it once it meets a
/// constructor.
fn assert_surface_equations(env: &mut Environment, members: &[(&str, usize)]) {
    for (member, count) in members {
        let eqs = equations(env, member);
        assert_eq!(
            eqs.len(),
            *count,
            "`{member}`: one equation per constructor"
        );
        for eq in &eqs {
            assert!(!eq.has_fvar_quick(), "`{member}`: a closed statement");
            for c in eq.collect_constants() {
                let last = c.to_string();
                let last = last.rsplit('.').next().unwrap_or_default();
                let is_rec = last == "rec" || last.starts_with("rec_");
                assert!(
                    !(is_rec && env.get_recursor(&c).is_some()),
                    "`{member}`'s equation names the recursor `{c}`: {eq}"
                );
            }
        }
    }
}

/// A minted `f.eq_N` is a kernel-checked theorem whose value is `Eq.refl`.
fn assert_minted(env: &Environment, names: &[&str]) {
    for name in names {
        let c = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("`{name}` minted"));
        assert!(
            matches!(c.kind, clean_kernel::env::ConstantKind::Theorem),
            "`{name}` is a theorem"
        );
        let value = c.value.as_ref().expect("a proof");
        assert!(
            value
                .collect_constants()
                .contains(&Name::from_string("Eq.refl")),
            "`{name}` is proved by `Eq.refl`"
        );
    }
}

fn assert_not_minted(env: &Environment, names: &[&str]) {
    for name in names {
        assert!(!registered(env, name), "`{name}` must not be minted");
    }
}

/// Judge k1: s1 `simp [P.beq]`, s2 `simp only [P.listBeq, Bool.and_eq_true] at
/// h`, s3 a catch-all on mixed constructors, r2 `rw [P.beq.eq_2]`, n1–n4 the
/// lemmas ascribed exactly as Lean 4.8 prints them.
#[test]
fn test_mutual_lift_eqns_simp_at_and_rw() {
    let fixture = fixture!("eqns_simp.lean");
    assert!(lean_accepts(fixture.0));
    let mut env = fresh();
    accepts_all(&mut env, fixture);
    assert_surface_equations(&mut env, &[("P.beq", 2), ("P.listBeq", 2)]);
    assert_minted(
        &env,
        &[
            "P.beq.eq_1",
            "P.beq.eq_2",
            "P.listBeq.eq_1",
            "P.listBeq.eq_2",
        ],
    );
    // Catch-all arms (Lean: hypothesis form) and `eq_def` stay unminted.
    assert_not_minted(
        &env,
        &["P.beq.eq_3", "P.listBeq.eq_3", "P.beq.eq_def", "P.beq.eq_4"],
    );
    for (twin, last) in [
        (fixture!("eqns_simp_twin.lean"), "s1f"),
        (fixture!("eqns_simp_at_twin.lean"), "s2f"),
    ] {
        assert!(!lean_accepts(twin.0));
        let err = refuses_last(&mut fresh(), twin, last);
        assert!(
            !err.contains("P.rec"),
            "{}: no goal left by simp names the lifted recursor: {err}",
            twin.0
        );
    }
}

/// Pinned open: Lean 4.8 has `P.beq.eq_3` in hypothesis form; Clean mints no
/// catch-all equation, so `#check @P.beq.eq_3` is an unknown identifier. This
/// fails the day the catch-all lemma is minted.
#[test]
fn test_mutual_lift_eqns_catchall_lemma_pinned_open() {
    let fixture = fixture!("eqns_catchall_pin.lean");
    assert!(lean_accepts(fixture.0), "Lean 4.8 has the catch-all lemma");
    let outcomes = run_file(&mut fresh(), fixture.1);
    let (last, init) = outcomes.split_last().expect("declarations");
    assert!(
        init.iter().all(Result::is_ok),
        "the block registers: {init:?}"
    );
    let err = last
        .as_ref()
        .expect_err("`P.beq.eq_3` is not minted (pinned open)");
    assert!(err.contains("P.beq.eq_3"), "{err}");
}

/// Judge k3 (the Pred.denote shape, a shared slot): `rw [Q.denote.eq_4]`, every
/// `eq_N` statement as Lean 4.8's `#check` prints it, `simp [f]` through the
/// shared slot, and the two mis-wiring controls.
#[test]
fn test_mutual_lift_eqns_denote_shared_slot() {
    let fixture = fixture!("eqns_denote.lean");
    assert!(lean_accepts(fixture.0));
    let mut env = fresh();
    accepts_all(&mut env, fixture);
    assert_surface_equations(
        &mut env,
        &[("Q.denote", 4), ("Q.denoteAll", 2), ("Q.denoteAny", 2)],
    );
    assert_minted(
        &env,
        &[
            "Q.denote.eq_1",
            "Q.denote.eq_2",
            "Q.denote.eq_3",
            "Q.denote.eq_4",
            "Q.denoteAll.eq_1",
            "Q.denoteAll.eq_2",
            "Q.denoteAny.eq_1",
            "Q.denoteAny.eq_2",
        ],
    );
    assert_not_minted(&env, &["Q.denote.eq_5", "Q.denote.eq_def"]);
    for (twin, last) in [
        (fixture!("eqns_denote_twin.lean"), "e2f"),
        (fixture!("eqns_denote_simp_twin.lean"), "bad"),
    ] {
        assert!(!lean_accepts(twin.0));
        refuses_last(&mut fresh(), twin, last);
    }
}

/// Judge k5 (block 10): `simp [constWidthAmbiguous]` with `ty` open closes only
/// because the equations are per constructor of `c`, the chosen major.
#[test]
fn test_mutual_lift_eqns_follow_major_choice() {
    let fixture = fixture!("eqns_major_choice.lean");
    assert!(lean_accepts(fixture.0));
    let mut env = fresh();
    accepts_all(&mut env, fixture);
    assert_surface_equations(
        &mut env,
        &[("constWidthAmbiguous", 5), ("constFieldsAmbiguous", 2)],
    );
    // A term-mode `match` mints no named lemma (pinned): only equation form.
    assert_not_minted(&env, &["constWidthAmbiguous.eq_1"]);
    assert_minted(&env, &["constFieldsAmbiguous.eq_1"]);
    let twin = fixture!("eqns_major_choice_twin.lean");
    assert!(!lean_accepts(twin.0));
    refuses_last(&mut fresh(), twin, "a1f");
}

/// pos_grandchild: through the `Nat × C` intermediate; the cons equation
/// splits the pair, as Lean's `C.fsz.eq_2` does.
#[test]
fn test_mutual_lift_eqns_pair_intermediate() {
    let fixture = fixture!("eqns_pair.lean");
    assert!(lean_accepts(fixture.0));
    let mut env = fresh();
    accepts_all(&mut env, fixture);
    assert_surface_equations(&mut env, &[("C.sz", 2), ("C.fsz", 2)]);
    let cons = equations(&mut env, "C.fsz")
        .pop()
        .expect("the cons equation");
    assert!(
        cons.collect_constants()
            .contains(&Name::from_string("Prod.mk")),
        "the pair is split into `Prod.mk`: {cons}"
    );
    assert_minted(&env, &["C.fsz.eq_1", "C.fsz.eq_2", "C.sz.eq_2"]);
    let twin = fixture!("eqns_pair_wrong.lean");
    assert!(!lean_accepts(twin.0));
    refuses_last(&mut fresh(), twin, "bad");
}

/// Block 11 (TemplateProps.lean:34): mutual theorems whose arms pass a sibling
/// to `simp`; the negative control recurses on the major premise itself.
#[test]
fn test_mutual_lift_eqns_theorem_block_with_simp_siblings() {
    let fixture = fixture!("eqns_theorem_simp.lean");
    assert!(lean_accepts(fixture.0));
    let mut env = fresh();
    accepts_all(&mut env, fixture);
    for name in ["substTy_embed", "substTys_embeds"] {
        assert!(registered(&env, name), "`{name}` registered");
    }
    // Theorems record no equations and mint no lemmas.
    assert!(equations(&mut env, "substTy_embed").is_empty());
    assert_not_minted(&env, &["substTy_embed.eq_1"]);
    let neg = fixture!("eqns_theorem_simp_neg.lean");
    assert!(!lean_accepts(neg.0));
    let outcomes = run_file(&mut fresh(), neg.1);
    assert!(
        outcomes.last().is_some_and(Result::is_err),
        "the theorem block calling a sibling on the major premise is refused"
    );
}

/// The three core lemmas, kernel-checked, with `propext` their only axiom.
#[test]
fn test_mutual_lift_eqns_prelude_lemmas() {
    let fixture = fixture!("eqns_prelude.lean");
    assert!(lean_accepts(fixture.0));
    let mut env = fresh();
    accepts_all(&mut env, fixture);
    for name in [
        "Bool.and_eq_true",
        "decide_eq_true_eq",
        "Option.isSome_iff_exists",
    ] {
        let axioms = crate::print_axioms::collect_axioms(&env, &Name::from_string(name))
            .expect("axiom census");
        assert!(
            axioms.iter().all(|a| a.to_string() == "propext"),
            "`{name}` depends only on propext: {axioms:?}"
        );
    }
    let twin = fixture!("eqns_prelude_twin.lean");
    assert!(!lean_accepts(twin.0));
    refuses_last(&mut fresh(), twin, "o4f");
}

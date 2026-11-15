// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Level canonicalization == spec, and `is_geq` applies Lean's rules: sound
//! for the lattice order, and incomplete as Lean's rules are (R174). Its
//! operands are ck0's canonical forms, which are not always Lean's normal
//! forms (`level_as_written.rs`). The soundness is checked against levels
//! evaluated directly, at every small assignment.

use clean_ck0::Level;
use proptest::prelude::*;

#[test]
fn test_imax_right_zero_collapses_to_zero() {
    // imax(_, 0) = 0 (Prop-elimination), at construction.
    let l = Level::imax(Level::param(0), Level::zero());
    assert_eq!(l, Level::zero());
    assert!(l.is_zero());
}

#[test]
fn test_imax_nonzero_right_becomes_max() {
    // imax(u0, succ 0) = max(u0, 1) — right operand provably nonzero.
    let l = Level::imax(Level::param(0), Level::nat(1));
    let expected = Level::max(Level::param(0), Level::nat(1));
    assert_eq!(l, expected);
}

#[test]
fn test_max_is_sorted_and_deduped() {
    // max(u1, u0) and max(u0, u1) canonicalize equal; max(u0,u0)=u0.
    let a = Level::max(Level::param(1), Level::param(0));
    let b = Level::max(Level::param(0), Level::param(1));
    assert_eq!(a, b, "Max operands canonicalize order-insensitively");
    let dup = Level::max(Level::param(0), Level::param(0));
    assert_eq!(dup, Level::param(0), "duplicate Max operands collapse");
}

#[test]
fn test_max_explicit_subsumed_by_offset() {
    // max(1, succ(u0)) keeps both (u0 may be 0); max(0, u0) = u0.
    let z = Level::max(Level::zero(), Level::param(0));
    assert_eq!(z, Level::param(0), "max(0, u) = u");
}

#[test]
fn test_is_geq_reflexive_and_zero_minimum() {
    let u = Level::param(0);
    assert!(Level::is_geq(&u, &u));
    assert!(Level::is_geq(&u, &Level::zero()), "everything >= 0");
    assert!(Level::is_geq(&Level::succ(u.clone()), &u), "succ u >= u");
    assert!(!Level::is_geq(&Level::zero(), &Level::nat(1)), "0 not >= 1");
}

/// `succ (imax u v) >= imax u v` holds at every assignment, but Lean's
/// `is_geq` answers `false`: it splits the `imax` on the right, and neither
/// `u` nor `v` is below `succ (imax u v)` by its rules. So does ck0's (R174).
#[test]
fn test_is_geq_offset_of_irreducible_imax_is_false_as_in_lean() {
    let imax_uv = Level::imax(Level::param(0), Level::param(1));
    assert!(!Level::is_geq(&Level::succ(imax_uv.clone()), &imax_uv));
    let max_uv = Level::max(Level::param(0), Level::param(1));
    assert!(
        Level::is_geq(&Level::succ(max_uv.clone()), &max_uv),
        "control: max"
    );
}

#[test]
fn test_succ_distributes_over_max() {
    // succ(max(u0,u1)) canonicalizes to max(succ u0, succ u1).
    let inner = Level::max(Level::param(0), Level::param(1));
    let s = Level::succ(inner).normalize();
    let expected = Level::max(Level::succ(Level::param(0)), Level::succ(Level::param(1)));
    assert_eq!(s, expected);
}

/// Levels built from `succ` and `max` only: on these `succ l >= l` is one of
/// Lean's answers (with `imax` it need not be).
fn arb_level_without_imax() -> impl Strategy<Value = Level> {
    let leaf = prop_oneof![
        Just(Level::zero()),
        (0u32..4).prop_map(Level::param),
        (0u32..5).prop_map(Level::nat),
    ];
    leaf.prop_recursive(4, 32, 4, |inner| {
        prop_oneof![
            inner.clone().prop_map(Level::succ),
            (inner.clone(), inner).prop_map(|(a, b)| Level::max(a, b)),
        ]
    })
}

fn arb_level() -> impl Strategy<Value = Level> {
    let leaf = prop_oneof![
        Just(Level::zero()),
        (0u32..4).prop_map(Level::param),
        (0u32..5).prop_map(Level::nat),
    ];
    leaf.prop_recursive(4, 32, 4, |inner| {
        prop_oneof![
            inner.clone().prop_map(Level::succ),
            (inner.clone(), inner.clone()).prop_map(|(a, b)| Level::max(a, b)),
            (inner.clone(), inner).prop_map(|(a, b)| Level::imax(a, b)),
        ]
    })
}

proptest! {
    #[test]
    fn prop_normalize_idempotent(l in arb_level()) {
        // Smart constructors already canonicalize, so normalize is a no-op fixpoint.
        let n1 = l.normalize();
        let n2 = n1.normalize();
        prop_assert_eq!(n1, n2);
    }

    #[test]
    fn prop_canonical_eq_is_structural(l in arb_level()) {
        // A level built two different ways but equal canonical form must be ==.
        let again = l.normalize();
        prop_assert_eq!(l, again);
    }

    #[test]
    fn prop_is_geq_reflexive(l in arb_level()) {
        prop_assert!(Level::is_geq(&l, &l));
    }

    #[test]
    fn prop_succ_geq_base(l in arb_level_without_imax()) {
        prop_assert!(Level::is_geq(&Level::succ(l.clone()), &l));
    }

    #[test]
    fn prop_zero_is_minimum(l in arb_level()) {
        prop_assert!(Level::is_geq(&l, &Level::zero()));
    }
}

/// A level as written, evaluated directly rather than through ck0.
#[derive(Debug, Clone)]
enum Syn {
    Zero,
    Param(u32),
    Succ(Box<Syn>),
    Max(Box<Syn>, Box<Syn>),
    IMax(Box<Syn>, Box<Syn>),
}

impl Syn {
    fn level(&self) -> Level {
        match self {
            Syn::Zero => Level::zero(),
            Syn::Param(i) => Level::param(*i),
            Syn::Succ(a) => Level::succ(a.level()),
            Syn::Max(a, b) => Level::max(a.level(), b.level()),
            Syn::IMax(a, b) => Level::imax(a.level(), b.level()),
        }
    }

    fn eval(&self, at: &[u32; 3]) -> u32 {
        match self {
            Syn::Zero => 0,
            Syn::Param(i) => at[usize::try_from(*i).expect("a small index")],
            Syn::Succ(a) => a.eval(at) + 1,
            Syn::Max(a, b) => a.eval(at).max(b.eval(at)),
            Syn::IMax(a, b) => match b.eval(at) {
                0 => 0,
                r => a.eval(at).max(r),
            },
        }
    }

    /// This level and every level inside it.
    fn parts(&self, out: &mut Vec<Syn>) {
        out.push(self.clone());
        match self {
            Syn::Succ(a) => a.parts(out),
            Syn::Max(a, b) | Syn::IMax(a, b) => {
                a.parts(out);
                b.parts(out);
            }
            Syn::Zero | Syn::Param(_) => {}
        }
    }
}

fn arb_syn() -> impl Strategy<Value = Syn> {
    let leaf = prop_oneof![Just(Syn::Zero), (0u32..3).prop_map(Syn::Param)];
    leaf.prop_recursive(4, 24, 2, |inner| {
        prop_oneof![
            inner.clone().prop_map(|a| Syn::Succ(Box::new(a))),
            (inner.clone(), inner.clone()).prop_map(|(a, b)| Syn::Max(Box::new(a), Box::new(b))),
            (inner.clone(), inner).prop_map(|(a, b)| Syn::IMax(Box::new(a), Box::new(b))),
        ]
    })
}

/// A `true` from `is_geq` holds at each of the 27 assignments of `0..=2` to
/// the three parameters.
fn sound(l1: &Syn, l2: &Syn) -> Result<(), String> {
    if !Level::is_geq(&l1.level(), &l2.level()) {
        return Ok(());
    }
    for k in 0..27u32 {
        let at = [k % 3, k / 3 % 3, k / 9];
        if l1.eval(&at) < l2.eval(&at) {
            return Err(format!(
                "is_geq({l1:?}, {l2:?}) is true, and fails at {at:?}"
            ));
        }
    }
    Ok(())
}

/// Pairs where a rule applied to the wrong side would answer `true`.
#[test]
fn test_is_geq_sound_on_imax_examples() {
    let p = Syn::Param;
    let imax = |a: Syn, b: Syn| Syn::IMax(Box::new(a), Box::new(b));
    let succ = |a: Syn| Syn::Succ(Box::new(a));
    for (l1, l2) in [
        (imax(p(0), p(1)), p(0)),
        (succ(imax(p(0), p(1))), succ(p(0))),
        (p(0), imax(p(1), p(0))),
        (imax(p(0), imax(p(1), p(2))), p(1)),
    ] {
        sound(&l1, &l2).expect("sound");
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(2000))]

    #[test]
    fn prop_is_geq_sound(l1 in arb_syn(), l2 in arb_syn()) {
        let verdict = sound(&l1, &l2);
        prop_assert!(verdict.is_ok(), "{:?}", verdict);
    }

    #[test]
    fn prop_is_geq_sound_against_its_parts(l in arb_syn()) {
        let mut parts = Vec::new();
        l.parts(&mut parts);
        for part in &parts {
            let up = sound(&l, part);
            prop_assert!(up.is_ok(), "{:?}", up);
            let down = sound(part, &l);
            prop_assert!(down.is_ok(), "{:?}", down);
        }
    }
}

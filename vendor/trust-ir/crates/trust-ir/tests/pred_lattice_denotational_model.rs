// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// THE LEAN SOUNDNESS THEOREMS, MODEL-CHECKED AGAINST THE REAL IMPLEMENTATION.
//
// `lean/trust_ir-semantics/TrustIr/Pred.lean` gives the predicate lattice a
// denotation `⟦p⟧ : Value -> Prop` and
// `TrustIr/Proofs/PredLatticeProps.lean` proves, against that denotation:
//
//   implies_sound          : implies a b = true -> forall v, ⟦a⟧ v -> ⟦b⟧ v
//   join_upper_bound_left  : forall v, ⟦a⟧ v -> ⟦join a b⟧ v
//   join_upper_bound_right : forall v, ⟦b⟧ v -> ⟦join a b⟧ v
//   denote_Top             : ⟦top⟧ v, for every v
//
// Those proofs are UNCHECKED: there is no Lean toolchain on the box they were
// written on. This test is the honest substitute available in pure Rust — it
// re-implements the SAME denotation (arm for arm, see the comments) and
// exhaustively checks the same statements over a finite lattice and a finite
// value domain, against the SHIPPED decision procedure (`PredTable::implies`
// and `PredTable::join_pred`, not a re-implementation of them).
//
// What that buys, precisely: a counterexample to any of the four theorems that
// lives inside this lattice x domain would fail this test. It is evidence for
// the theorems' CONTENT, not a proof of them — a proof quantifies over all
// predicates and all values, and only a kernel can discharge that.

use trust_ir::pred::{Pred, PredTable, Space, Universe};
use trust_ir::{Constant, PredId, UnivId};

/// The semantic domain, mirroring the cases of the Lean `Value` that the
/// denotation distinguishes. Integer width is deliberately absent: a predicate
/// constrains the NUMBER, not the carrier width (Lean: `∃ w, v = .int w n`).
#[derive(Clone, Copy, Debug, PartialEq)]
enum V {
    Int(i128),
    Bool(bool),
    Ptr(u64),
    Null,
    /// Stands for every value the lattice cannot look inside (a float, an
    /// aggregate, …). In Lean this is the arbitrary, universally quantified
    /// `m : Constant → Value → Prop`; here one particular `m` is chosen, which
    /// is a legitimate instance of the universally quantified statement.
    Other,
}

/// Lean `constDenote`. Keyed constants get their exact meaning; a non-keyed
/// constant (float here) is handed to the chosen `m`.
fn const_matches(c: &Constant, v: V) -> bool {
    match (c, v) {
        (Constant::Int(n), V::Int(m)) => *n == m,
        (Constant::Bool(b), V::Bool(x)) => *b == x,
        (Constant::Float(_), V::Other) => true,
        _ => false,
    }
}

/// The DENOTATIONAL cardinality of a universe: the number of distinct members.
///
/// Computed here independently of `Universe::cardinality` on purpose — if the
/// shipped cardinality ever disagreed with the true one in a direction that
/// mattered, the soundness sweep below would catch it rather than inherit it.
fn true_cardinality(u: &Universe) -> Option<u128> {
    match u {
        Universe::IntRange { lo, hi } => {
            if lo > hi {
                None
            } else {
                Some((hi.wrapping_sub(*lo) as u128).checked_add(1)?)
            }
        }
        Universe::Members(items) => {
            let mut keys: Vec<(u8, i128)> = Vec::new();
            for c in items {
                let key = match c {
                    Constant::Int(v) => (0u8, *v),
                    Constant::Bool(b) => (1u8, i128::from(*b)),
                    // A universe with a member the lattice cannot order has no
                    // usable cardinality.
                    _ => return None,
                };
                if !keys.contains(&key) {
                    keys.push(key);
                }
            }
            (!keys.is_empty()).then_some(keys.len() as u128)
        }
    }
}

/// Lean `Universe.contains`: `self ∈ U`.
fn univ_contains(u: &Universe, v: V) -> bool {
    match u {
        Universe::IntRange { lo, hi } => matches!(v, V::Int(n) if *lo <= n && n <= *hi),
        Universe::Members(items) => items.iter().any(|c| const_matches(c, v)),
    }
}

/// Lean `Pred.denote`, arm for arm.
fn denote(preds: &[Pred], univs: &[Universe], p: &Pred, v: V, depth: u32) -> bool {
    if depth > 64 {
        // The sample lattice is acyclic; this only guards the recursion.
        return false;
    }
    match p {
        // `∃ w n, v = .int w n ∧ lo ≤ n ∧ n ≤ hi`
        Pred::Interval { lo, hi } => matches!(v, V::Int(n) if *lo <= n && n <= *hi),
        // `∃ c ∈ items, constDenote c v`
        Pred::FiniteSet(items) => items.iter().any(|c| const_matches(c, v)),
        Pred::InUniverse(u, space) => match univs.get(u.as_usize()) {
            // A dangling universe id is not a fact.
            None => false,
            Some(univ) => match space {
                // `v ∈ U`
                Space::Member => univ_contains(univ, v),
                // `0 ≤ v < |U|` — the ORDINAL, not a member.
                Space::Index => match true_cardinality(univ) {
                    None => false,
                    Some(card) => {
                        matches!(v, V::Int(n) if n >= 0 && (n as u128) < card)
                    }
                },
            },
        },
        // `∃ w n, v = .int w n ∧ n ≠ 0`
        Pred::NonZero => matches!(v, V::Int(n) if n != 0),
        // `v ≠ nullPtr`
        Pred::NonNull => v != V::Null,
        Pred::Conj(children) => children.iter().all(|c| match preds.get(c.as_usize()) {
            None => false,
            Some(child) => denote(preds, univs, child, v, depth + 1),
        }),
        Pred::Disj(children) => children.iter().any(|c| match preds.get(c.as_usize()) {
            None => false,
            Some(child) => denote(preds, univs, child, v, depth + 1),
        }),
        // NO INFORMATION: true of everything. This is the formal content of
        // "a MISSING predicate is `Top`".
        Pred::Top => true,
        Pred::Bottom => false,
    }
}

fn ints(vs: &[i128]) -> Vec<Constant> {
    vs.iter().copied().map(Constant::Int).collect()
}

/// Universes: two ranges (one a subset of the other), one explicit extension
/// whose members are NOT its indices (the shape of the shipped miscompile),
/// one disjoint extension, and one non-canonical extension.
fn universes() -> Vec<Universe> {
    vec![
        Universe::IntRange { lo: 1, hi: 8 },           // 0
        Universe::IntRange { lo: 1, hi: 4 },           // 1
        Universe::Members(ints(&[1, 2, 3])),           // 2
        Universe::Members(ints(&[5, 6])),              // 3
        Universe::Members(ints(&[3, 1, 1])),           // 4: NON-canonical
        Universe::Members(vec![Constant::Bool(true)]), // 5
    ]
}

/// A lattice touching every constructor, every `Space`, both universe shapes,
/// and the connectives at two depths. Children are strictly ascending and
/// strictly older than their parent, exactly as the validator requires.
fn predicates() -> Vec<Pred> {
    vec![
        Pred::Top,                                          // 0
        Pred::Bottom,                                       // 1
        Pred::Interval { lo: 0, hi: 3 },                    // 2
        Pred::Interval { lo: 2, hi: 9 },                    // 3
        Pred::Interval { lo: 1, hi: 8 },                    // 4
        Pred::Interval { lo: -3, hi: -1 },                  // 5
        Pred::Interval { lo: 0, hi: 7 },                    // 6
        Pred::FiniteSet(ints(&[1, 3])),                     // 7
        Pred::FiniteSet(ints(&[1, 2, 3])),                  // 8
        Pred::FiniteSet(ints(&[0, 1])),                     // 9
        Pred::FiniteSet(ints(&[0, 1, 2, 3, 4, 5, 6, 7])),   // 10
        Pred::FiniteSet(vec![Constant::Bool(true)]),        // 11
        Pred::FiniteSet(vec![Constant::Float(1.5)]),        // 12: NON-canonical
        Pred::NonZero,                                      // 13
        Pred::NonNull,                                      // 14
        Pred::InUniverse(UnivId::new(0), Space::Member),    // 15
        Pred::InUniverse(UnivId::new(0), Space::Index),     // 16
        Pred::InUniverse(UnivId::new(1), Space::Member),    // 17
        Pred::InUniverse(UnivId::new(1), Space::Index),     // 18
        Pred::InUniverse(UnivId::new(2), Space::Member),    // 19
        Pred::InUniverse(UnivId::new(2), Space::Index),     // 20
        Pred::InUniverse(UnivId::new(3), Space::Member),    // 21
        Pred::InUniverse(UnivId::new(4), Space::Member),    // 22
        Pred::InUniverse(UnivId::new(4), Space::Index),     // 23
        Pred::InUniverse(UnivId::new(5), Space::Member),    // 24
        Pred::InUniverse(UnivId::new(9), Space::Member),    // 25: DANGLING univ
        Pred::Conj(vec![PredId::new(2), PredId::new(3)]),   // 26
        Pred::Disj(vec![PredId::new(2), PredId::new(3)]),   // 27
        Pred::Conj(vec![PredId::new(7), PredId::new(13)]),  // 28
        Pred::Disj(vec![PredId::new(7), PredId::new(21)]),  // 29
        Pred::Conj(vec![PredId::new(15), PredId::new(13)]), // 30
        Pred::Disj(vec![PredId::new(17), PredId::new(19)]), // 31
        Pred::Conj(vec![PredId::new(26), PredId::new(27)]), // 32
        Pred::Disj(vec![PredId::new(26), PredId::new(31)]), // 33
    ]
}

fn domain() -> Vec<V> {
    let mut vs: Vec<V> = (-4..=10).map(V::Int).collect();
    vs.push(V::Bool(true));
    vs.push(V::Bool(false));
    vs.push(V::Ptr(7));
    vs.push(V::Null);
    vs.push(V::Other);
    vs
}

/// `implies_sound`, model-checked: every implication the SHIPPED decision
/// procedure certifies really does hold in the denotation.
///
/// This is the theorem the whole consumption rule rests on. A single failure
/// here is a miscompile of the class the typed value model exists to close: a
/// convention mismatch that passes validation silently.
#[test]
fn implies_is_sound_over_the_denotation() {
    let preds = predicates();
    let univs = universes();
    let table = PredTable::new(&preds, &univs);
    let domain = domain();

    let mut certified = 0usize;
    let mut checked = 0usize;
    for a in 0..preds.len() {
        for b in 0..preds.len() {
            let holds = table.implies(PredId::new(a as u32), PredId::new(b as u32));
            if !holds {
                continue;
            }
            certified += 1;
            for &v in &domain {
                checked += 1;
                if denote(&preds, &univs, &preds[a], v, 0) {
                    assert!(
                        denote(&preds, &univs, &preds[b], v, 0),
                        "UNSOUND: implies(pred.{a}, pred.{b}) certified {} => {}, but {v:?} \
                         satisfies the left and not the right",
                        preds[a],
                        preds[b]
                    );
                }
            }
        }
    }

    // Non-vacuity: the sweep must actually exercise certified implications.
    assert!(
        certified > 200,
        "only {certified} implications certified over {}x{} pairs — the sweep is too weak \
         to be evidence",
        preds.len(),
        preds.len()
    );
    assert!(checked > 4_000, "only {checked} (pred-pair, value) checks");

    // Non-degeneracy of the DENOTATION itself. A denotation that answered
    // `false` everywhere would make the sweep above vacuous, so every
    // satisfiable predicate must have a witness, and the two unsatisfiable
    // ones must have none.
    let mut witnesses = 0usize;
    for (i, p) in preds.iter().enumerate() {
        let sat = domain
            .iter()
            .filter(|&&v| denote(&preds, &univs, p, v, 0))
            .count();
        witnesses += sat;
        let expect_empty = matches!(p, Pred::Bottom)
            // pred.25 is stated over a DANGLING universe id: not a fact.
            || matches!(p, Pred::InUniverse(u, _) if u.as_usize() >= univs.len());
        if expect_empty {
            assert_eq!(sat, 0, "pred.{i} ({p}) must denote nothing");
        } else {
            assert!(
                sat > 0,
                "pred.{i} ({p}) has no witness — the denotation is degenerate"
            );
        }
    }
    assert!(
        witnesses > 100,
        "only {witnesses} satisfied (pred, value) pairs"
    );

    eprintln!(
        "implies soundness: {certified} certified implications over {} ordered pairs, \
         {checked} (implication, value) checks, 0 unsound; denotation non-degenerate \
         ({witnesses} satisfied (pred, value) pairs over {} values)",
        preds.len() * preds.len(),
        domain.len()
    );
}

/// `join_upper_bound_left` / `join_upper_bound_right`, model-checked: the join
/// is above BOTH inputs, so a control-flow merge can only ever LOSE
/// information — never silently gain a convention neither side had.
#[test]
fn join_is_an_upper_bound_over_the_denotation() {
    let preds = predicates();
    let univs = universes();
    let table = PredTable::new(&preds, &univs);
    let domain = domain();

    let mut tops = 0usize;
    for a in 0..preds.len() {
        for b in 0..preds.len() {
            let joined = table.join_pred(PredId::new(a as u32), PredId::new(b as u32));
            if matches!(joined, Pred::Top) {
                tops += 1;
            }
            for &v in &domain {
                if denote(&preds, &univs, &preds[a], v, 0) {
                    assert!(
                        denote(&preds, &univs, &joined, v, 0),
                        "join(pred.{a}, pred.{b}) = {joined} is not above the LEFT input {} \
                         at {v:?}",
                        preds[a]
                    );
                }
                if denote(&preds, &univs, &preds[b], v, 0) {
                    assert!(
                        denote(&preds, &univs, &joined, v, 0),
                        "join(pred.{a}, pred.{b}) = {joined} is not above the RIGHT input {} \
                         at {v:?}",
                        preds[b]
                    );
                }
            }
        }
    }
    eprintln!(
        "join upper bound: {} joins checked over {} values each; {tops} decayed to top",
        preds.len() * preds.len(),
        domain.len()
    );
}

/// `denote_Top` and its consequence: `Top` holds of everything, so a dropped
/// fact licenses nothing that is not already universally true.
#[test]
fn top_denotes_everything_and_licenses_nothing() {
    let preds = predicates();
    let univs = universes();
    let table = PredTable::new(&preds, &univs);
    let domain = domain();

    for &v in &domain {
        assert!(
            denote(&preds, &univs, &Pred::Top, v, 0),
            "top must hold of {v:?}"
        );
        assert!(
            !denote(&preds, &univs, &Pred::Bottom, v, 0),
            "bottom must hold of nothing, but held of {v:?}"
        );
    }

    // Whatever `top` certifies must be true of the whole domain — i.e. the
    // consumption site gained nothing by accepting a dropped fact.
    let top = PredId::new(0);
    assert!(matches!(preds[0], Pred::Top));
    for b in 0..preds.len() {
        if !table.implies(top, PredId::new(b as u32)) {
            continue;
        }
        for &v in &domain {
            assert!(
                denote(&preds, &univs, &preds[b], v, 0),
                "top certified pred.{b} ({}) but it fails at {v:?} — a dropped fact would \
                 have licensed a real constraint",
                preds[b]
            );
        }
    }
}

/// The miscompile class itself: over ANY pair of universes, an INDEX claim and
/// a MEMBER claim never certify one another. (`index_never_implies_member` in
/// the Lean development.)
#[test]
fn no_index_member_crossing_is_ever_certified() {
    let preds = predicates();
    let univs = universes();
    let table = PredTable::new(&preds, &univs);

    let mut pairs = 0usize;
    for a in 0..preds.len() {
        for b in 0..preds.len() {
            let (Pred::InUniverse(_, sa), Pred::InUniverse(_, sb)) = (&preds[a], &preds[b]) else {
                continue;
            };
            if sa == sb {
                continue;
            }
            pairs += 1;
            assert!(
                !table.implies(PredId::new(a as u32), PredId::new(b as u32)),
                "pred.{a} ({}) certified pred.{b} ({}) across encoding conventions — this is \
                 the shipped miscompile",
                preds[a],
                preds[b]
            );
        }
    }
    assert!(pairs >= 10, "only {pairs} cross-convention pairs exercised");
}

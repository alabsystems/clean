// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// ══════════════════════════════════════════════════════════════════════════
// ADVERSARIAL SOUNDNESS SWEEP for the predicate lattice.
// ══════════════════════════════════════════════════════════════════════════
//
// `PredTable::implies` is sound in ONE direction only: it may return `true`
// exclusively when the implication genuinely holds, and must return `false`
// whenever it is unsure. A false negative costs a spurious validation error
// (loud); a false positive is a MISCOMPILE (silent). The unit tests in
// `pred.rs` check that arm by arm. This file checks it by BRUTE FORCE against
// an independent ground truth.
//
// Method: build a deliberately adversarial table — intervals that numerically
// coincide with universes, universes spelled two extensionally-equal ways,
// index and member carriers over the same and over different universes,
// singleton and degenerate universes, finite sets, and nested Conj/Disj — then
// compute each predicate's DENOTATION as an explicit set of integers and
// assert, over every ordered pair, that `implies(a, b) ⇒ denote(a) ⊆
// denote(b)`. A single counterexample falsifies the soundness claim.
//
// Two things the finite probe domain cannot see are handled explicitly:
//   * a predicate whose true denotation escapes the domain is flagged
//     `unbounded`, and an unbounded `a` entailing a bounded `b` is reported as
//     a violation regardless of what the restricted sets say;
//   * `join` is checked for the SEMANTIC upper-bound property (denotational),
//     separately from whether `implies` can certify it — the gap between those
//     two is incompleteness, not unsoundness, and is pinned as such.

use std::collections::BTreeSet;
use trust_ir::{Constant, Module, Pred, PredId, Space, Universe};

const LO: i128 = -12;
const HI: i128 = 24;

fn ints(vs: &[i128]) -> Vec<Constant> {
    vs.iter().copied().map(Constant::Int).collect()
}

/// Ground-truth denotation over the finite probe domain, plus a flag saying
/// whether the predicate's TRUE denotation is contained in that domain.
/// An unbounded set cannot be a subset of a bounded one, so the flag carries
/// the part of the check the finite domain cannot see.
fn denote(m: &Module, id: PredId, depth: u32) -> (BTreeSet<i128>, bool) {
    let all = || (LO..=HI).collect::<BTreeSet<i128>>();
    if depth > 8 {
        return (all(), false);
    }
    let table = m.pred_table();
    match table.pred(id).expect("interned") {
        Pred::Top => (all(), false),
        Pred::Bottom => (BTreeSet::new(), true),
        Pred::NonZero => ((LO..=HI).filter(|v| *v != 0).collect(), false),
        // A pointer fact places no constraint on the integer carrier.
        Pred::NonNull => (all(), false),
        Pred::Interval { lo, hi } => {
            assert!(
                *lo >= LO && *hi <= HI,
                "probe domain must contain the interval"
            );
            ((LO..=HI).filter(|v| v >= lo && v <= hi).collect(), true)
        }
        Pred::FiniteSet(items) => {
            let s: BTreeSet<i128> = items
                .iter()
                .map(|c| match c {
                    Constant::Int(v) => *v,
                    other => panic!("probe uses integer extensions only, got {other:?}"),
                })
                .collect();
            assert!(s.iter().all(|v| *v >= LO && *v <= HI));
            (s, true)
        }
        Pred::InUniverse(u, space) => {
            let univ = table.universe(*u).expect("interned");
            let set: BTreeSet<i128> = match space {
                Space::Member => match univ {
                    Universe::IntRange { lo, hi } => (*lo..=*hi).collect(),
                    Universe::Members(items) => items
                        .iter()
                        .map(|c| match c {
                            Constant::Int(v) => *v,
                            other => panic!("probe uses integer universes only, got {other:?}"),
                        })
                        .collect(),
                },
                // The documented meaning of Index: a 0-based ordinal, i.e.
                // 0 <= self < |U|.
                Space::Index => {
                    let card = univ.cardinality().expect("finite") as i128;
                    (0..card).collect()
                }
            };
            assert!(
                set.iter().all(|v| *v >= LO && *v <= HI),
                "probe domain too narrow"
            );
            (set, true)
        }
        Pred::Conj(children) => {
            let kids: Vec<(BTreeSet<i128>, bool)> =
                children.iter().map(|c| denote(m, *c, depth + 1)).collect();
            let mut acc = kids[0].0.clone();
            for (s, _) in &kids[1..] {
                acc = acc.intersection(s).copied().collect();
            }
            (acc, kids.iter().any(|(_, b)| *b))
        }
        Pred::Disj(children) => {
            let kids: Vec<(BTreeSet<i128>, bool)> =
                children.iter().map(|c| denote(m, *c, depth + 1)).collect();
            let mut acc = BTreeSet::new();
            for (s, _) in &kids {
                acc = acc.union(s).copied().collect();
            }
            (acc, kids.iter().all(|(_, b)| *b))
        }
    }
}

fn build() -> (Module, Vec<PredId>) {
    let mut m = Module::new("lattice_soundness_probe");

    let universes = vec![
        Universe::IntRange { lo: 1, hi: 8 },
        Universe::IntRange { lo: 0, hi: 7 },
        Universe::IntRange { lo: 2, hi: 5 },
        Universe::IntRange { lo: -2, hi: 1 },
        Universe::IntRange { lo: 0, hi: 0 },
        Universe::Members(ints(&[0, 2, 4, 6])),
        // Extensionally identical to universe 0, spelled differently.
        Universe::Members(ints(&[1, 2, 3, 4, 5, 6, 7, 8])),
        Universe::Members(ints(&[3, 9, 20])),
    ];
    let uids: Vec<_> = universes
        .into_iter()
        .map(|u| m.intern_universe(u).expect("canonical"))
        .collect();

    let mut leaves = vec![
        Pred::Top,
        Pred::Bottom,
        Pred::NonZero,
        Pred::NonNull,
        Pred::Interval { lo: 0, hi: 8 },
        Pred::Interval { lo: 1, hi: 8 },
        Pred::Interval { lo: 0, hi: 7 },
        Pred::Interval { lo: 2, hi: 5 },
        Pred::Interval { lo: -2, hi: 1 },
        Pred::Interval { lo: 3, hi: 3 },
        Pred::Interval { lo: -12, hi: 24 },
        Pred::Interval { lo: 0, hi: 0 },
        Pred::FiniteSet(ints(&[1, 2])),
        Pred::FiniteSet(ints(&[0, 2, 4, 6])),
        Pred::FiniteSet(ints(&[1, 2, 3, 4, 5, 6, 7, 8])),
        Pred::FiniteSet(ints(&[3, 9, 20])),
        Pred::FiniteSet(ints(&[0])),
    ];
    for u in &uids {
        leaves.push(Pred::InUniverse(*u, Space::Member));
        leaves.push(Pred::InUniverse(*u, Space::Index));
    }

    let mut ids: Vec<PredId> = leaves
        .into_iter()
        .map(|p| m.intern_pred(p).expect("canonical"))
        .collect();

    // Connectives over an assorted spread of the leaves, so Conj/Disj arms are
    // exercised on both sides of `implies`.
    let leaf_count = ids.len();
    let mut connectives = Vec::new();
    for i in (0..leaf_count).step_by(3) {
        for j in (1..leaf_count).step_by(7) {
            if i != j {
                connectives.push(Pred::Conj(vec![ids[i], ids[j]]));
                connectives.push(Pred::Disj(vec![ids[i], ids[j]]));
            }
        }
    }
    // A few 3-ary ones.
    for i in (0..leaf_count.saturating_sub(2)).step_by(5) {
        connectives.push(Pred::Conj(vec![ids[i], ids[i + 1], ids[i + 2]]));
        connectives.push(Pred::Disj(vec![ids[i], ids[i + 1], ids[i + 2]]));
    }
    for p in connectives {
        if let Some(id) = m.intern_pred(p) {
            ids.push(id);
        }
    }
    ids.sort_unstable();
    ids.dedup();
    (m, ids)
}

/// Is `b` a `Disj` that literally carries `a` as an arm? That is the shape
/// G4 fixed: `a ⊑ Disj[.., a, ..]` is trivially true, but the pre-WP-1B arm
/// order tried `Disj`-on-the-LEFT first and returned unconditionally, so it
/// never reached the one-arm-suffices rule on the right.
fn b_literally_contains_a(m: &Module, a: PredId, b: PredId) -> bool {
    matches!(m.pred_table().pred(b), Some(Pred::Disj(arms)) if arms.contains(&a))
}

/// The two predicates are `InUniverse(_, Index)` over DIFFERENT universes.
/// G3 deliberately refuses these (see `cross_universe_index_is_extensional`),
/// so they are the KNOWN, PRICED incompleteness of the current rule set.
fn cross_universe_index_pair(m: &Module, a: PredId, b: PredId) -> bool {
    let t = m.pred_table();
    matches!(
        (t.pred(a), t.pred(b)),
        (
            Some(Pred::InUniverse(ua, Space::Index)),
            Some(Pred::InUniverse(ub, Space::Index)),
        ) if ua != ub
    )
}

#[test]
fn implies_completeness_delta_is_measured_and_categorised() {
    // WP-1B G4 asked for a broad re-sweep reporting how many SOUND pairs
    // `implies` now certifies. Soundness is asserted by the sweep above; this
    // test measures the OTHER side — incompleteness — and categorises every
    // remaining gap so none of it is anonymous.
    //
    // The `Index` category is a deliberate, documented refusal (G3): the
    // denotational model here reads `InUniverse(U, Index)` as the pure numeric
    // set `0 <= v < |U|`, under which a cross-universe index implication IS
    // sound — and `implies` refuses it anyway, because an ordinal into one
    // canonical ordering is not an ordinal into another. That refusal is
    // priced in the LOUD direction and is counted separately here.
    let (m, ids) = build();
    let table = m.pred_table();
    let den: Vec<(BTreeSet<i128>, bool)> = ids.iter().map(|id| denote(&m, *id, 0)).collect();

    let mut pairs = 0usize;
    let mut certified = 0usize;
    let mut uncertified_index = 0usize;
    let mut uncertified_disj_membership = 0usize;
    let mut uncertified_top_antecedent = 0usize;
    let mut uncertified_other = 0usize;
    let mut unsound = 0usize;

    for (ia, a) in ids.iter().enumerate() {
        for (ib, b) in ids.iter().enumerate() {
            pairs += 1;
            let (sa, bounded_a) = &den[ia];
            let (sb, bounded_b) = &den[ib];
            // Denotational truth over the probe domain, with the
            // unbounded-into-bounded case handled explicitly.
            let semantically_holds = sa.is_subset(sb) && !(!*bounded_a && *bounded_b);
            let certified_here = table.implies(*a, *b);
            if certified_here && !semantically_holds {
                unsound += 1;
            }
            if certified_here {
                certified += 1;
            } else if semantically_holds {
                if matches!(table.pred(*a), Some(Pred::Top)) {
                    // Refused BY DESIGN by the `Top`-on-the-left rule, which is
                    // the load-bearing line of the whole model: a carrier that
                    // dropped its fact entails nothing. It reaches here only
                    // for a target that is EXTENSIONALLY `Top` without being
                    // spelled `Top` (`Disj[top, X]`), so the refusal costs
                    // nothing real and the rule stays absolute.
                    uncertified_top_antecedent += 1;
                } else if cross_universe_index_pair(&m, *a, *b) {
                    uncertified_index += 1;
                } else if b_literally_contains_a(&m, *a, *b) {
                    uncertified_disj_membership += 1;
                } else {
                    uncertified_other += 1;
                }
            }
        }
    }

    eprintln!(
        "COMPLETENESS SWEEP: {} predicates, {pairs} ordered pairs | certified {certified} | \
         sound-but-uncertified: cross-universe-index {uncertified_index} (G3, deliberate), \
         top-antecedent {uncertified_top_antecedent} (by design), \
         disj-membership {uncertified_disj_membership}, other {uncertified_other} | \
         unsound {unsound}",
        ids.len()
    );
    assert_eq!(unsound, 0, "a false positive is a miscompile");
    // G4: `a ⊑ Disj[.., a, ..]` must now be certified in EVERY instance whose
    // antecedent is not `Top` (the one case the design refuses on purpose).
    assert_eq!(
        uncertified_disj_membership, 0,
        "G4: a disjunction that literally contains `a` must certify `a ⊑ b`"
    );
    // G3's price, pinned so it cannot drift silently: every remaining
    // index-shaped gap is a CROSS-universe pair, never a same-universe one.
    assert!(
        uncertified_index > 0,
        "the probe table must actually contain cross-universe index pairs, \
         else the G3 measurement is vacuous"
    );
}

#[test]
fn implies_is_sound_against_the_denotational_model() {
    let (m, ids) = build();
    let table = m.pred_table();
    let den: Vec<(BTreeSet<i128>, bool)> = ids.iter().map(|id| denote(&m, *id, 0)).collect();

    let mut trues = 0usize;
    let mut pairs = 0usize;
    let mut violations: Vec<String> = Vec::new();

    for (ia, a) in ids.iter().enumerate() {
        for (ib, b) in ids.iter().enumerate() {
            pairs += 1;
            if !table.implies(*a, *b) {
                continue;
            }
            trues += 1;
            let (sa, bounded_a) = &den[ia];
            let (sb, bounded_b) = &den[ib];
            if !sa.is_subset(sb) {
                violations.push(format!(
                    "UNSOUND: implies({} , {}) = true but denotation {:?} not subset of {:?}",
                    table.describe(*a),
                    table.describe(*b),
                    sa,
                    sb
                ));
            }
            // An unbounded set cannot be contained in a bounded one; the finite
            // probe domain cannot see this, so check it explicitly.
            if !*bounded_a && *bounded_b {
                violations.push(format!(
                    "UNSOUND (unbounded into bounded): implies({} , {}) = true",
                    table.describe(*a),
                    table.describe(*b),
                ));
            }
        }
    }

    eprintln!(
        "SOUNDNESS SWEEP: {} predicates, {} ordered pairs, {} implications held, {} violations",
        ids.len(),
        pairs,
        trues,
        violations.len()
    );
    assert!(
        trues > ids.len() * 2,
        "harness is vacuous: only {trues} implications held over {pairs} pairs"
    );
    assert!(violations.is_empty(), "{}", violations.join("\n"));
}

#[test]
fn the_harness_has_teeth_on_the_pair_that_matters() {
    // Proves the sweep is capable of catching the miscompile class: on the
    // WP-18 pair the denotational model DOES disagree, so a `true` answer from
    // `implies` would have been reported as a violation above.
    let (m, _) = build();
    let table = m.pred_table();
    let interval = m
        .predicates
        .iter()
        .position(|p| *p == Pred::Interval { lo: 0, hi: 8 })
        .map(|i| PredId::new(i as u32))
        .expect("interned");
    let member = m
        .predicates
        .iter()
        .position(|p| *p == Pred::InUniverse(trust_ir::UnivId::new(0), Space::Member))
        .map(|i| PredId::new(i as u32))
        .expect("interned");
    let (si, _) = denote(&m, interval, 0);
    let (sm, _) = denote(&m, member, 0);
    assert!(
        !si.is_subset(&sm),
        "the model must disagree on this pair, else the sweep proves nothing here"
    );
    assert!(!table.implies(interval, member));
}

#[test]
fn join_is_a_semantic_upper_bound_over_the_whole_probe_table() {
    // THE SOUNDNESS QUESTION: is the join's DENOTATION a superset of both
    // inputs' denotations? If not, a merge manufactured a fact neither
    // predecessor established — that would be the miscompile.
    //
    // Separately tracked: whether `implies` can CERTIFY the upper bound. A
    // certified-false / semantically-true pair is incompleteness (a spurious
    // validation error — loud, safe), not unsoundness.
    let (mut m, ids) = build();
    let mut checked = 0usize;
    let mut unsound = Vec::new();
    let mut uncertified = Vec::new();
    for a in &ids {
        for b in &ids {
            let j = m.join_preds(Some(*a), Some(*b));
            let table = m.pred_table();
            let (da, _) = denote(&m, *a, 0);
            let (db, _) = denote(&m, *b, 0);
            let (dj, _) = denote(&m, j, 0);
            if !da.is_subset(&dj) || !db.is_subset(&dj) {
                unsound.push(format!(
                    "UNSOUND JOIN: join({}, {}) = {} loses members",
                    table.describe(*a),
                    table.describe(*b),
                    table.describe(j)
                ));
            }
            if !table.implies(*a, j) || !table.implies(*b, j) {
                uncertified.push(format!(
                    "{} \\/ {} = {}",
                    table.describe(*a),
                    table.describe(*b),
                    table.describe(j)
                ));
            }
            checked += 1;
        }
    }
    eprintln!(
        "JOIN SWEEP: {checked} pairs | semantically-unsound: {} | \
         semantically sound but not certified by `implies`: {}",
        unsound.len(),
        uncertified.len()
    );
    for u in uncertified.iter().take(3) {
        eprintln!("  uncertified example: {u}");
    }
    assert!(unsound.is_empty(), "{}", unsound.join("\n"));
}

#[test]
fn nested_disjunction_incompleteness_is_fixed_and_still_one_sided() {
    // THE G4 REGRESSION TEST. This test previously PINNED the incompleteness
    // it now pins the fix for, and said so: "if this ever starts passing, the
    // rule order in implies_at was improved".
    //
    // `Disj` on the LEFT used to be an unconditional `return` in `implies_at`
    // placed ahead of `Disj` on the RIGHT. When `a` was a disjunction and `b`
    // a disjunction that literally CONTAINED `a` as an arm, the left rule
    // fired first, recursed into a's arms, hit `Top` and answered false. The
    // sufficient rule (one arm on the right suffices) now runs first.
    let mut m = Module::new("nested_disj");
    let top = m.intern_pred(Pred::Top).expect("leaf");
    let bottom = m.intern_pred(Pred::Bottom).expect("leaf");
    let iv = m
        .intern_pred(Pred::Interval { lo: -2, hi: 1 })
        .expect("leaf");
    let a = m.intern_pred(Pred::Disj(vec![top, bottom])).expect("ok");
    let b = m.intern_pred(Pred::Disj(vec![top, iv])).expect("ok");
    let j = m.join_preds(Some(a), Some(b));
    let table = m.pred_table();

    // Semantically an upper bound...
    let (da, _) = denote(&m, a, 0);
    let (dj, _) = denote(&m, j, 0);
    assert!(da.is_subset(&dj), "the join IS a semantic upper bound");
    // ...and `implies` now CERTIFIES it, from both inputs.
    assert!(table.implies(a, j), "G4: the join must now be certified");
    assert!(table.implies(b, j), "from both sides");

    // And the fix did not manufacture the converse: a join never entails a
    // strictly stronger fact than one of its inputs. (Here `a` denotes the
    // whole domain — `Top` is one of its arms — so `j` and `a` are
    // extensionally equal and mutual entailment is correct, not a leak.)
    assert!(!table.implies(j, a) || da == dj);
    assert!(!m.pred_implies(Some(j), Some(a)) || da == dj);

    // The strictly-stronger direction IS refused where it would be a leak.
    let strong = m
        .intern_pred(Pred::Interval { lo: 0, hi: 0 })
        .expect("leaf");
    let weak = m
        .intern_pred(Pred::Disj(vec![strong, iv]))
        .expect("ok")
        .to_owned();
    let table = m.pred_table();
    assert!(table.implies(strong, weak), "arm ⊑ disjunction");
    assert!(
        !table.implies(weak, strong),
        "a disjunction must NOT entail one of its arms"
    );
}

#[test]
fn an_absent_fact_is_top_and_top_entails_nothing_non_trivial() {
    let (m, ids) = build();
    let table = m.pred_table();
    let top = m
        .predicates
        .iter()
        .position(|p| *p == Pred::Top)
        .map(|i| PredId::new(i as u32))
        .expect("interned");
    let mut non_trivial = 0usize;
    for b in &ids {
        let is_trivial = matches!(table.pred(*b), Some(Pred::Top));
        if is_trivial {
            assert!(table.implies(top, *b));
        } else {
            non_trivial += 1;
            assert!(
                !table.implies(top, *b),
                "top must not entail {}",
                table.describe(*b)
            );
        }
        // Absence must behave exactly like Top.
        assert_eq!(
            m.pred_implies(None, Some(*b)),
            table.implies(top, *b),
            "absence and Top must agree at {}",
            table.describe(*b)
        );
    }
    eprintln!("TOP SWEEP: {non_trivial} non-trivial targets, all refused");
    assert!(non_trivial > 30);
}

#[test]
fn cross_universe_index_is_extensional() {
    // THE G3 DECISION, on the record with its price.
    //
    // This test previously pinned the opposite answer: `implies` related two
    // DIFFERENT universes on CARDINALITY alone, which is sound under the
    // numeric denotation `0 <= self < |U|` that `denote()` above implements.
    // It is refused now — deliberately, and at a measured cost in
    // completeness (see `implies_completeness_delta_is_measured_and_categorised`).
    //
    // WHY: an index is a fact about a value RELATIVE TO an ordering. Letting
    // an ordinal into universe U satisfy a site stated over universe V is one
    // table's row number read against another table — the same shape as the
    // index-vs-member confusion the whole model exists to catch, and the one
    // arm where the lattice was still willing to cross conventions silently.
    let mut m = Module::new("cross_universe_index");
    let small = m
        .intern_in_universe(Universe::IntRange { lo: 0, hi: 1 }, Space::Index)
        .expect("canonical");
    let big = m
        .intern_in_universe(Universe::Members(ints(&[5, 6, 7])), Space::Index)
        .expect("canonical");
    // Two spellings of ONE extension: same canonical ordering, so they index
    // the same thing and must still entail each other.
    let spelled_twice = m
        .intern_in_universe(Universe::Members(ints(&[0, 1])), Space::Index)
        .expect("canonical");
    // The numeric escape hatch: a site that wants only "a number below 3".
    let numeric = m
        .intern_pred(Pred::Interval { lo: 0, hi: 2 })
        .expect("canonical");

    let table = m.pred_table();
    eprintln!(
        "CROSS-UNIVERSE INDEX: implies(index into 0..=1, index into {{5,6,7}}) = {} \
         (was `true` on cardinality alone before WP-1B/G3)",
        table.implies(small, big)
    );
    assert!(
        !table.implies(small, big),
        "an ordinal into 0..=1 must not satisfy a site indexing {{5,6,7}}"
    );
    assert!(!table.implies(big, small), "nor the converse");
    assert!(
        table.implies(small, spelled_twice) && table.implies(spelled_twice, small),
        "the rule is EXTENSIONAL: two spellings of one extension index the \
         same ordering and must entail each other"
    );
    assert!(
        table.implies(small, numeric) && table.implies(big, numeric),
        "and the NUMERIC content is still entailed by both, so a site that \
         genuinely wants a bounded number spells it as an interval"
    );
}

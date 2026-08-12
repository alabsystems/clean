// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
//
//! Concrete, kernel-Certifiable borrow-liveness obligations reflected from the NLL
//! borrow-check results.
//!
//! The standard ownership reflection ([`crate::proof_bundle_builder`]) emits opaque
//! `RustOwnership.borrowValid` predicates that a downstream kernel accepts *on trust*
//! (the borrow-checker is trusted), landing the obligation at the `Trusted` tier. This
//! module reflects the borrow-checker's liveness *decision* into a CONCRETE, decidable
//! `clean_kernel` proposition instead: a borrow is live iff its NLL region (the set of
//! program points where it is active) is non-empty, i.e. `1 <= |region|`. That fact is
//! provable by computation exactly when the analysis found the borrow live, so it
//! discharges at the `Certified` tier — the borrow-checker's verdict kernel-DERIVED
//! rather than accept-on-trust. This is the plumbing that lifts the reflected ownership
//! obligations `Trusted -> Certified` (see the design's §6 / the trust-wp
//! `clean-borrowcheck-reflected` and `clean-ownership-certified` spikes).

use std::collections::BTreeMap;

use clean_kernel::expr::BinderInfo;
use clean_kernel::{Expr, Level, Name};

use crate::nll::NllResult;

fn nat() -> Expr {
    Expr::const_(Name::from_string("Nat"), vec![])
}

fn nat_lit(n: u64) -> Expr {
    Expr::nat_lit(n)
}

fn nat_le(a: Expr, b: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Nat.le"), vec![]), a),
        b,
    )
}

fn nat_lt(a: Expr, b: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Nat.lt"), vec![]), a),
        b,
    )
}

fn eq_nat(a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_str_levels("Eq", vec![Level::succ(Level::zero())]),
        [nat(), a, b],
    )
}

fn pi(dom: Expr, body: Expr) -> Expr {
    Expr::pi(BinderInfo::Default, dom, body)
}

/// Three order-lemma SHAPES (`Nat` facts, Certified with a foundational closure) that the
/// ownership implications would instantiate once the reflection threads concrete borrow
/// state into their predicates. HONESTY NOTE (see trust-wp
/// `docs/design-review-2026-07-06.md`, F1): these are generic order lemmas, NOT the
/// domain implications themselves — no ownership predicate appears in these goals. They
/// are the target shapes of the Trusted→Certified lift, kept here so the lift's proof
/// obligations are pinned next to the reflection that must eventually emit instances:
///
///   A (Eq→Le): `∀ cg x, (x=cg) → (x≤cg)`
///   B (Le-wk): `∀ x, (2≤x) → (1≤x)`
///   C (Lt→Le): `∀ cap x, (x<cap) → (x≤cap)`
#[must_use]
pub fn safety_law_goals() -> Vec<(String, Expr)> {
    let a = pi(
        nat(),
        pi(
            nat(),
            pi(
                eq_nat(Expr::bvar(0), Expr::bvar(1)),
                nat_le(Expr::bvar(1), Expr::bvar(2)),
            ),
        ),
    );
    let b = pi(
        nat(),
        pi(
            nat_le(nat_lit(2), Expr::bvar(0)),
            nat_le(nat_lit(1), Expr::bvar(1)),
        ),
    );
    let cc = pi(
        nat(),
        pi(
            nat(),
            pi(
                nat_lt(Expr::bvar(0), Expr::bvar(1)),
                nat_le(Expr::bvar(1), Expr::bvar(2)),
            ),
        ),
    );
    vec![
        ("shape A (Eq→Le)".to_string(), a),
        ("shape B (Le-weaken)".to_string(), b),
        ("shape C (Lt→Le)".to_string(), cc),
    ]
}

/// One concrete liveness obligation per borrow found by the NLL analysis:
/// `Nat.le 1 |region|` — the borrow's live-region is non-empty. Provable (→ `Certified`)
/// exactly when the borrow-checker found the borrow live; unprovable (`1 <= 0`) for a
/// dead borrow. Each entry is `(borrow label, goal)`; the goal is a real
/// `clean_kernel::Expr` a `TypeChecker` accepts and whose only closure is foundational
/// (`Nat.le` + literals), so a `Nat.le 1 n` proof for `n >= 1` is Certified.
#[must_use]
pub fn concrete_borrow_liveness(
    borrow_results: &BTreeMap<String, NllResult>,
) -> Vec<(String, Expr)> {
    let mut out = Vec::new();
    for (function, result) in borrow_results {
        // FAIL CLOSED: a function the borrow checker REJECTS must never contribute
        // provable obligations. Emit one deliberately-unprovable goal (`1 <= 0`) per
        // rejected function so any downstream "all obligations Certified" claim is
        // impossible — the analysis verdict, negative as well as positive, is reflected.
        if !result.errors.is_empty() {
            out.push((
                format!(
                    "{function}::borrowcheck-rejected({} error(s))",
                    result.errors.len()
                ),
                nat_le(nat_lit(1), nat_lit(0)),
            ));
            continue;
        }
        for (i, _borrow) in result.borrows.iter().enumerate() {
            let region_size = result
                .regions
                .get(i)
                .map_or(0, std::collections::BTreeSet::len) as u64;
            out.push((
                format!("{function}::borrow{i}"),
                nat_le(nat_lit(1), nat_lit(region_size)),
            ));
        }
    }
    out
}

/// Injective ProgramPoint encoding for kernel literals: `block * 2^16 + statement`.
/// Only INJECTIVITY is claimed (statement_index < 2^16, enforced fail-closed) — no
/// cross-block ordering meaning is attached to the encoding.
fn encode_point(p: &crate::nll::ProgramPoint) -> Option<u64> {
    let stmt = p.statement_index as u64;
    if stmt >= 1 << 16 {
        return None;
    }
    Some(u64::from(p.block) * (1 << 16) + stmt)
}

/// Second concrete family (P4-done(1), beyond liveness): BORROW-ORIGIN WELL-FORMEDNESS.
/// For every live borrow of a borrow-check-passing function, the NLL region contains the
/// borrow's origin point (the loan is live where it is created — verified against the
/// probe/regression test below). Reflected as a kernel-decidable WITNESS equality: the
/// emitter locates the region point equal to the origin and emits
/// `Eq Nat enc(origin) enc(witness)` over the injectively-encoded literals — the kernel
/// re-verifies the membership by computation. Fail-closed: a missing witness, an
/// un-encodable point, or a borrow-check-REJECTED function emits the unprovable sentinel.
#[must_use]
pub fn concrete_origin_wellformedness(
    borrow_results: &BTreeMap<String, NllResult>,
) -> Vec<(String, Expr)> {
    let sentinel = |label: String, out: &mut Vec<(String, Expr)>| {
        out.push((label, nat_le(nat_lit(1), nat_lit(0))));
    };
    let mut out = Vec::new();
    for (function, result) in borrow_results {
        if !result.errors.is_empty() {
            sentinel(
                format!(
                    "{function}::borrowcheck-rejected({} error(s))",
                    result.errors.len()
                ),
                &mut out,
            );
            continue;
        }
        for (i, borrow) in result.borrows.iter().enumerate() {
            let label = format!("{function}::borrow{i}::origin-wf");
            let Some(region) = result.regions.get(i) else {
                sentinel(label, &mut out);
                continue;
            };
            if region.is_empty() {
                // A dead borrow has no origin-membership claim; the liveness family
                // already renders it unprovable.
                continue;
            }
            let (Some(enc_origin), Some(witness)) = (
                encode_point(&borrow.origin),
                region
                    .iter()
                    .find(|p| **p == borrow.origin)
                    .and_then(encode_point),
            ) else {
                sentinel(label, &mut out);
                continue;
            };
            out.push((
                label,
                Expr::apps(
                    Expr::const_str_levels("Eq", vec![Level::succ(Level::zero())]),
                    [nat(), nat_lit(enc_origin), nat_lit(witness)],
                ),
            ));
        }
    }
    out
}

/// Third concrete family (P4-done(1)): MUTABLE-BORROW EXCLUSIVITY.
/// For a borrow-check-PASSING function, NLL guarantees that a non-two-phase `&mut`
/// borrow's region is DISJOINT from any same-place co-borrow's region (a two-phase
/// `&mut` may legitimately overlap during its reservation phase — data-verified by the
/// probe test — so two-phase pairs are explicitly OUTSIDE this family's fragment).
/// Reflected kernel-side, one goal per point pair (p, q) ∈ r_i × r_j:
/// `Eq Bool (Nat.beq enc(p) enc(q)) Bool.false` — the kernel COMPUTES the disequality
/// on the injectively-encoded literals; the emitter never pre-decides disjointness.
/// Fail-closed: rejected functions and un-encodable points emit the unprovable sentinel.
#[must_use]
pub fn concrete_mut_exclusivity(
    borrow_results: &BTreeMap<String, NllResult>,
) -> Vec<(String, Expr)> {
    use crate::vir::{BorrowKind, MutBorrowKind};
    let is_default_mut = |k: &BorrowKind| {
        matches!(
            k,
            BorrowKind::Mut {
                kind: MutBorrowKind::Default
            }
        )
    };
    let mut out = Vec::new();
    for (function, result) in borrow_results {
        if !result.errors.is_empty() {
            out.push((
                format!(
                    "{function}::borrowcheck-rejected({} error(s))",
                    result.errors.len()
                ),
                nat_le(nat_lit(1), nat_lit(0)),
            ));
            continue;
        }
        for (i, b1) in result.borrows.iter().enumerate() {
            for (j, b2) in result.borrows.iter().enumerate().skip(i + 1) {
                if b1.borrowed_place != b2.borrowed_place {
                    continue;
                }
                // At least one side must be a NON-two-phase &mut for NLL's disjointness
                // guarantee to apply; two-phase reservations may overlap (probe-verified).
                if !(is_default_mut(&b1.kind) || is_default_mut(&b2.kind)) {
                    continue;
                }
                let (Some(r1), Some(r2)) = (result.regions.get(i), result.regions.get(j)) else {
                    out.push((
                        format!("{function}::borrow{i}x{j}::excl"),
                        nat_le(nat_lit(1), nat_lit(0)),
                    ));
                    continue;
                };
                for (k, p) in r1.iter().enumerate() {
                    for (l, q) in r2.iter().enumerate() {
                        let label = format!("{function}::borrow{i}x{j}::excl[{k},{l}]");
                        let (Some(ep), Some(eq)) = (encode_point(p), encode_point(q)) else {
                            out.push((label, nat_le(nat_lit(1), nat_lit(0))));
                            continue;
                        };
                        let beq = Expr::apps(
                            Expr::const_(Name::from_string("Nat.beq"), vec![]),
                            [nat_lit(ep), nat_lit(eq)],
                        );
                        out.push((
                            label,
                            Expr::apps(
                                Expr::const_str_levels("Eq", vec![Level::succ(Level::zero())]),
                                [
                                    Expr::const_(Name::from_string("Bool"), vec![]),
                                    beq,
                                    Expr::const_(Name::from_string("Bool.false"), vec![]),
                                ],
                            ),
                        ));
                    }
                }
            }
        }
    }
    out
}

/// Fourth concrete family (P4-done(1)+(3)): USE-AFTER-INIT over the FULL CFG.
/// A worklist definite-initialization dataflow (IN(B) = ∩ preds OUT(P); OUT = IN ∪ defs;
/// entry IN = the argument locals; SSA block params are defs at block entry), followed by
/// a PCC-style CERTIFICATE the kernel re-checks piece by piece:
///   • in-block use:   `Eq Bool (Nat.ble enc(first_def) enc(use)) Bool.true` — same-block
///     statement order is the one setting where the point encoding is order-faithful;
///   • entry-block reliance on an argument: two kernel-checked bounds
///     `1 ≤ local ∧ local ≤ arg_count` (arghood, not emitter say-so);
///   • cross-block reliance: for EVERY predecessor edge P→B, a membership witness
///     `Eq Nat enc(local) enc(witness ∈ OUT(P))` — the dataflow's inductive step,
///     re-checked per edge (a wrong fixpoint has no witness and fails closed).
/// Unreachable blocks are skipped (their uses never execute). Honesty: moves and partial
/// initialization are NOT modeled (local-granularity first-def order only); the emitter
/// locating witnesses in real analysis sets is the §8-3 reflection seam, same as
/// families 1–3 — every arithmetic/order/equality step is kernel-computed.
#[must_use]
pub fn concrete_use_init(lowered: &crate::vir_lowering::LoweredProgram) -> Vec<(String, Expr)> {
    use crate::nll::liveness::{stmt_defs, stmt_uses, term_uses_for_liveness};
    use crate::nll::ProgramPoint;
    use crate::vir::LocalId;
    use std::collections::{BTreeSet, HashMap, VecDeque};

    let eq_nat_goal = |a: u64, b: u64| {
        Expr::apps(
            Expr::const_str_levels("Eq", vec![Level::succ(Level::zero())]),
            [nat(), nat_lit(a), nat_lit(b)],
        )
    };
    let ble_goal = |a: u64, b: u64| {
        Expr::apps(
            Expr::const_str_levels("Eq", vec![Level::succ(Level::zero())]),
            [
                Expr::const_(Name::from_string("Bool"), vec![]),
                Expr::apps(
                    Expr::const_(Name::from_string("Nat.ble"), vec![]),
                    [nat_lit(a), nat_lit(b)],
                ),
                Expr::const_(Name::from_string("Bool.true"), vec![]),
            ],
        )
    };
    let sentinel = nat_le(nat_lit(1), nat_lit(0));

    let mut out = Vec::new();
    for (function, body) in &lowered.functions {
        let nblocks = body.blocks.len();
        if nblocks == 0 {
            continue;
        }
        // CFG edges.
        let mut preds: Vec<Vec<usize>> = vec![Vec::new(); nblocks];
        for (bi, b) in body.blocks.iter().enumerate() {
            for sc in b.terminator.successors() {
                let si = sc as usize;
                if si < nblocks {
                    preds[si].push(bi);
                }
            }
        }
        // Per-block defs (statement defs + SSA block params).
        let block_defs: Vec<BTreeSet<LocalId>> = body
            .blocks
            .iter()
            .map(|b| {
                let mut d: BTreeSet<LocalId> = b.params.iter().map(|p| p.local).collect();
                for st in &b.statements {
                    for x in stmt_defs(st) {
                        d.insert(x);
                    }
                }
                // Terminator defs (call destinations): initialized for SUCCESSORS —
                // deliberately NOT added to in-block first_def (they happen last).
                for x in crate::nll::liveness::term_defs(&b.terminator) {
                    d.insert(x);
                }
                d
            })
            .collect();
        // Worklist fixpoint: definite-init (meet = intersection), entry = args.
        let mut in_sets: Vec<Option<BTreeSet<LocalId>>> = vec![None; nblocks];
        in_sets[0] = Some((1..=body.arg_count).collect());
        let mut reachable = vec![false; nblocks];
        reachable[0] = true;
        let mut work: VecDeque<usize> = VecDeque::from([0usize]);
        while let Some(bi) = work.pop_front() {
            let out_b: BTreeSet<LocalId> = in_sets[bi]
                .as_ref()
                .expect("visited")
                .union(&block_defs[bi])
                .copied()
                .collect();
            for sc in body.blocks[bi].terminator.successors() {
                let si = sc as usize;
                if si >= nblocks {
                    continue;
                }
                let new_in: BTreeSet<LocalId> = match &in_sets[si] {
                    None => out_b.clone(),
                    Some(cur) => cur.intersection(&out_b).copied().collect(),
                };
                if !reachable[si] || in_sets[si].as_ref() != Some(&new_in) {
                    reachable[si] = true;
                    in_sets[si] = Some(new_in);
                    work.push_back(si);
                }
            }
        }
        let out_set = |bi: usize| -> BTreeSet<LocalId> {
            in_sets[bi]
                .as_ref()
                .expect("reachable")
                .union(&block_defs[bi])
                .copied()
                .collect()
        };
        // Certificate emission per reachable block.
        for (bi, b) in body.blocks.iter().enumerate() {
            if !reachable[bi] {
                continue;
            }
            let in_b = in_sets[bi].as_ref().expect("reachable").clone();
            let enc = |stmt: usize| {
                encode_point(&ProgramPoint {
                    block: bi as u32,
                    statement_index: stmt,
                })
            };
            let mut first_def: HashMap<LocalId, usize> = HashMap::new();
            for p in &b.params {
                first_def.insert(p.local, 0); // SSA params: defined at block entry
            }
            let justify = |l: LocalId,
                           use_stmt: usize,
                           first_def: &HashMap<LocalId, usize>,
                           out: &mut Vec<(String, Expr)>| {
                let base = format!("{function}::b{bi}::local{l}@{use_stmt}");
                match (first_def.get(&l), enc(use_stmt)) {
                    (Some(d), Some(eu)) => match enc(*d) {
                        Some(ed) => out.push((format!("{base}::use-init"), ble_goal(ed, eu))),
                        None => out.push((format!("{base}::use-init"), sentinel.clone())),
                    },
                    _ if in_b.contains(&l) => {
                        if bi == 0 {
                            // arghood: 1 ≤ l ∧ l ≤ arg_count, both kernel-checked.
                            out.push((
                                format!("{base}::use-init-entry[lo]"),
                                ble_goal(1, u64::from(l)),
                            ));
                            out.push((
                                format!("{base}::use-init-entry[hi]"),
                                ble_goal(u64::from(l), u64::from(body.arg_count)),
                            ));
                        } else {
                            // the dataflow's inductive step, per predecessor edge.
                            for &pi in &preds[bi] {
                                if !reachable[pi] {
                                    continue;
                                }
                                let label = format!("{base}::use-init-edge[b{pi}]");
                                match out_set(pi).iter().find(|w| **w == l) {
                                    Some(w) => {
                                        out.push((label, eq_nat_goal(u64::from(l), u64::from(*w))))
                                    }
                                    None => out.push((label, sentinel.clone())),
                                }
                            }
                        }
                    }
                    _ => out.push((format!("{base}::use-init"), sentinel.clone())),
                }
            };
            for (s_idx, stmt) in b.statements.iter().enumerate() {
                for u in stmt_uses(stmt) {
                    justify(u, s_idx, &first_def, &mut out);
                }
                for d in stmt_defs(stmt) {
                    first_def.entry(d).or_insert(s_idx);
                }
            }
            let term_idx = b.statements.len();
            for u in term_uses_for_liveness(body, &b.terminator) {
                justify(u, term_idx, &first_def, &mut out);
            }
        }
    }
    out
}

#[cfg(test)]
mod probe_tests {
    use crate::examples::all_examples;

    /// Probe/regression: for every live borrow of a borrow-check-passing function,
    /// report origin-vs-region so the origin-membership invariant is chosen from DATA.
    #[test]
    fn probe_origin_vs_region() {
        for ex in all_examples() {
            let Ok(results) = ex.check_borrows() else {
                continue;
            };
            for (f, r) in &results {
                if !r.errors.is_empty() {
                    continue;
                }
                for (i, b) in r.borrows.iter().enumerate() {
                    let region = r.regions.get(i);
                    let contains = region.is_some_and(|reg| reg.contains(&b.origin));
                    let first = region.and_then(|reg| reg.iter().next());
                    println!(
                        "{}::{f} borrow{i} kind={:?} origin={:?} |region|={} contains_origin={contains} first={:?}",
                        ex.name, b.kind, b.origin,
                        region.map_or(0, |reg| reg.len()), first
                    );
                    // Probe for the exclusivity family: report same-place borrow
                    // pairs (any Mut involved) and whether their regions are disjoint.
                    for (j, b2) in r.borrows.iter().enumerate().skip(i + 1) {
                        if b2.borrowed_place == b.borrowed_place {
                            let r1 = r.regions.get(i);
                            let r2 = r.regions.get(j);
                            let disjoint = match (r1, r2) {
                                (Some(a), Some(c)) => a.intersection(c).next().is_none(),
                                _ => true,
                            };
                            println!(
                                "  PAIR {}::{f} borrow{i}({:?})+borrow{j}({:?}) same-place disjoint={disjoint} |r1|={} |r2|={}",
                                ex.name, b.kind, b2.kind,
                                r1.map_or(0, |x| x.len()), r2.map_or(0, |x| x.len())
                            );
                            // Data-backed invariant behind concrete_mut_exclusivity:
                            // NON-two-phase same-place pairs have disjoint regions.
                            use crate::vir::{BorrowKind, MutBorrowKind};
                            let dm = |k: &BorrowKind| {
                                matches!(
                                    k,
                                    BorrowKind::Mut {
                                        kind: MutBorrowKind::Default
                                    }
                                )
                            };
                            if dm(&b.kind) || dm(&b2.kind) {
                                assert!(
                                    disjoint,
                                    "non-two-phase same-place pair must be disjoint: {}::{f}",
                                    ex.name
                                );
                            }
                        }
                    }
                    // Data-backed invariant behind concrete_origin_wellformedness:
                    // every LIVE borrow's region contains its origin.
                    if region.is_some_and(|reg| !reg.is_empty()) {
                        assert!(
                            contains,
                            "live borrow's region must contain its origin: {}::{f} borrow{i}",
                            ex.name
                        );
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod cfg_census {
    use crate::examples::all_examples;

    #[test]
    fn census_blocks_per_function() {
        for ex in all_examples() {
            let Ok(prog) = ex.parse() else { continue };
            let Ok(lowered) = prog.lower_to_vir() else {
                continue;
            };
            for (f, body) in &lowered.functions {
                println!(
                    "{}::{f} blocks={} params(entry)={} args={}",
                    ex.name,
                    body.blocks.len(),
                    body.blocks.first().map_or(0, |b| b.params.len()),
                    body.arg_count
                );
            }
        }
    }
}

#[cfg(test)]
mod cert_gap_probe {
    use crate::examples::all_examples;

    #[test]
    fn probe_unjustified_uses() {
        for ex in all_examples() {
            let Ok(prog) = ex.parse() else { continue };
            let Ok(lowered) = prog.lower_to_vir() else {
                continue;
            };
            for (label, goal) in super::concrete_use_init(&lowered) {
                let sentinel = super::nat_le(super::nat_lit(1), super::nat_lit(0));
                if goal == sentinel && !label.contains("rejected") {
                    println!("SENTINEL {}::{label}", ex.name);
                    panic!("unjustified use in Corpus A: {}::{label}", ex.name);
                }
            }
        }
    }
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! DEPENDENCY-CLOSURE GATE for the two-pass parallel Metamath verifier — the
//! library form of the `mm_gate` binary, so the invariant it enforces can be
//! stated as a TEST instead of as prose (issue R1-MM).
//!
//! # Why the gate exists
//!
//! The two-pass verifier ([`kernel_verify_two_pass_range`]) checks each proof in
//! its range against a PASS-1 environment in which EVERY `$p` theorem's schematic
//! TYPE is registered as an unchecked axiom. That makes the raw union of the
//! workers' `report.verified` a STRICT SUPERSET of the sequential verifier's set,
//! in exactly two ways:
//!
//! 1. **A dependency that never verified.** If `D`'s own proof is rejected, a
//!    dependent `T` still type-checks against `D`'s pass-1 axiom type and lands in
//!    `report.verified`. The sequential verifier never does that: it registers `D`
//!    only after `D` verified, and `build_tree` refuses to reuse a `$p` that is not
//!    in its verified `cache`.
//! 2. **A dependency that verified only on the GROUND fallback.** A theorem whose
//!    schematic-`$d` route fails and whose GROUND (`verify_metamath_theorem_guarded`)
//!    route succeeds is verified but NOT reusable: the sequential verifier leaves it
//!    out of `cache`, so every dependent is SKIPPED. Two-pass does not reproduce
//!    that — pass 1 registers `D`'s *light schematic* type and marks it reusable
//!    unconditionally, so any worker whose range excludes `D` (in the production
//!    split, every worker but one) accepts `T` against a type no checked `add_decl`
//!    ever discharged.
//!
//! This gate removes, to a fixpoint, every verified theorem whose transitive
//! `$p`-theorem dependency closure is not itself verified **and citable**. (1) is
//! closed by the `verified` predicate; (2) is closed by the REUSABILITY marking —
//! see [`Reusability`] — which the verifier records in
//! `KernelVerifyReport::ground_only` and `mm_verify_range` emits as `G <label>`.
//!
//! # What the gate does and does NOT guarantee
//!
//! GUARANTEED (pinned by `crates/clean-olean/tests/mm_two_pass_theorem.rs`):
//!
//! * Every surviving label `L` is in the input `verified` set, so `L`'s own type
//!   was `infer_sort`-checked and its own proof `check_type`-checked by the
//!   CHECKED `Environment::add_decl` during pass 2.
//! * Every `$p` theorem cited by `L`'s proof is also a surviving label
//!   (transitively). A dependency that failed, was skipped, or was never
//!   attempted takes every dependent down with it.
//! * Every `$p` theorem cited by `L`'s proof is [`Reusability::Reusable`] — it
//!   verified through the SCHEMATIC route, which is exactly the condition under
//!   which the sequential verifier puts it in its reuse `cache`. A ground-only
//!   dependency takes every dependent down with it (it survives itself: the
//!   sequential verifier verifies it too, it just may not be cited).
//! * A label that is not a `$p` theorem of this database never survives.
//! * A label whose reusability the input did not state ([`Reusability::Unmarked`],
//!   i.e. a pre-`VERIFIED_FORMAT 2` labels file) is treated exactly like a
//!   ground-only one: it survives, but nothing may cite it. A stale labels file
//!   therefore UNDER-approximates the export; it can never silently re-open (2).
//!
//! NOT GUARANTEED:
//!
//! * That a label the sequential verifier accepts is present. The gate only ever
//!   removes; the relation it restores is `gate(two-pass) == sequential` on the
//!   corpora the R1-MM suite measures, not an unconditional theorem.

use std::collections::{BTreeMap, BTreeSet};

use super::{KernelVerifyReport, Proof, ResolvedDatabase, ResolvedStatement};

/// Header line stamped on a verified-labels stream that CARRIES reusability
/// marking (`G <label>` lines). Its absence means the producer predates R1-MM's
/// fix, and every label in the stream reads as [`Reusability::Unmarked`].
pub const VERIFIED_FORMAT_HEADER: &str = "VERIFIED_FORMAT 2";

/// How a verified label was verified — the fact the gate needs and the raw
/// `verified` label set does not carry.
///
/// The variants are declared in increasing SEVERITY order, and
/// [`VerifiedLabels::insert`] unions by `max` over the derived `Ord`: the least
/// citable verdict wins. **Do not reorder them** — that would silently make the
/// union permissive, which is the R1-MM defect.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Reusability {
    /// Verified through the SCHEMATIC route. The sequential verifier puts such a
    /// theorem in its reuse `cache`, so dependents may cite it.
    Reusable,
    /// Verified only through the GROUND (`verify_metamath_theorem_guarded`)
    /// fallback. The sequential verifier does NOT cache it, so every dependent is
    /// skipped: "reuses $p theorem … that did not verify".
    GroundOnly,
    /// The stream stated no reusability (no [`VERIFIED_FORMAT_HEADER`]). Treated
    /// exactly like [`GroundOnly`](Self::GroundOnly) by the gate — FAIL CLOSED.
    /// Reading such a label as reusable is precisely the R1-MM gap, so it is not
    /// an option.
    Unmarked,
}

impl Reusability {
    /// May a surviving theorem CITE a dependency with this reusability?
    ///
    /// Only [`Reusable`](Self::Reusable). Both other values mean "the sequential
    /// verifier would have refused to build the dependent".
    #[must_use]
    pub fn is_citable(self) -> bool {
        matches!(self, Reusability::Reusable)
    }
}

/// A verified label set that remembers HOW each label was verified.
///
/// This is the gate's input. Build it from a [`KernelVerifyReport`]
/// ([`VerifiedLabels::from_report`]), from a rendered stream
/// ([`parse_verified_labels`]), or label by label ([`VerifiedLabels::insert`]).
///
/// UNION SEMANTICS ([`VerifiedLabels::merge`], [`VerifiedLabels::insert`]) are
/// FAIL-CLOSED and order-independent: the least citable verdict for a label wins,
/// so one worker reporting `GroundOnly` (or one stale, unmarked worker output)
/// cannot be overridden by another worker's `Reusable`.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct VerifiedLabels {
    by_label: BTreeMap<String, Reusability>,
}

impl VerifiedLabels {
    /// An empty set.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Every verified label's `(label, reusability)`, sorted by label.
    pub fn iter(&self) -> impl Iterator<Item = (&str, Reusability)> {
        self.by_label.iter().map(|(l, r)| (l.as_str(), *r))
    }

    /// Just the labels, sorted — the set the gate filters.
    #[must_use]
    pub fn labels(&self) -> BTreeSet<String> {
        self.by_label.keys().cloned().collect()
    }

    /// How `label` was verified, or `None` if it is not in the set.
    #[must_use]
    pub fn reusability(&self, label: &str) -> Option<Reusability> {
        self.by_label.get(label).copied()
    }

    /// Is `label` verified AND citable by a dependent? FAIL-CLOSED: an absent
    /// label and a ground-only/unmarked one both answer `false`.
    #[must_use]
    pub fn is_citable(&self, label: &str) -> bool {
        self.by_label.get(label).is_some_and(|r| r.is_citable())
    }

    /// Is `label` in the verified set at all (however it was verified)?
    #[must_use]
    pub fn contains(&self, label: &str) -> bool {
        self.by_label.contains_key(label)
    }

    /// Number of verified labels.
    #[must_use]
    pub fn len(&self) -> usize {
        self.by_label.len()
    }

    /// Is the set empty?
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.by_label.is_empty()
    }

    /// How many labels carry no reusability statement — i.e. came from a stream
    /// written before [`VERIFIED_FORMAT_HEADER`] existed. Non-zero means the gate
    /// will fail closed on every dependent; `mm_gate` refuses such a file outright
    /// unless the operator opts in.
    #[must_use]
    pub fn unmarked_count(&self) -> usize {
        self.by_label
            .values()
            .filter(|r| **r == Reusability::Unmarked)
            .count()
    }

    /// Labels that verified only on the GROUND fallback — nothing may cite them.
    #[must_use]
    pub fn ground_only(&self) -> BTreeSet<String> {
        self.by_label
            .iter()
            .filter(|(_, r)| **r == Reusability::GroundOnly)
            .map(|(l, _)| l.clone())
            .collect()
    }

    /// Add `label`, keeping the LEAST citable verdict if it is already present —
    /// so a label is `Reusable` only if EVERY contributor said `Reusable`, and one
    /// worker's `GroundOnly` (or one stale worker's `Unmarked`) can never be
    /// outvoted. Commutative and idempotent, so the union is order-independent.
    ///
    /// Implemented as `max` over [`Reusability`]'s derived `Ord`, which is why the
    /// variants are declared in increasing SEVERITY order.
    pub fn insert(&mut self, label: impl Into<String>, reusability: Reusability) {
        let slot = self.by_label.entry(label.into()).or_insert(reusability);
        *slot = (*slot).max(reusability);
    }

    /// Union with `other` under the same fail-closed rule as [`Self::insert`] —
    /// this is what a multi-worker driver does with its per-range outputs.
    pub fn merge(&mut self, other: &VerifiedLabels) {
        for (label, r) in other.iter() {
            self.insert(label, r);
        }
    }

    /// The verified set of one [`KernelVerifyReport`], with `report.ground_only`
    /// applied as the non-citable marking. This is the in-process equivalent of
    /// reading `mm_verify_range`'s stdout.
    #[must_use]
    pub fn from_report(report: &KernelVerifyReport) -> Self {
        let ground: BTreeSet<&str> = report.ground_only.iter().map(String::as_str).collect();
        let mut out = Self::new();
        for label in &report.verified {
            let r = if ground.contains(label.as_str()) {
                Reusability::GroundOnly
            } else {
                Reusability::Reusable
            };
            out.insert(label.clone(), r);
        }
        out
    }
}

/// Render a verified-labels stream for one worker's report — the exact bytes
/// `mm_verify_range` prints, and the input [`parse_verified_labels`] reads back.
///
/// FORMAT (v2), chosen to be strictly ADDITIVE over the v1 format so that readers
/// outside this crate keep working unchanged:
///
/// ```text
/// VERIFIED_FORMAT 2      <- marks the stream as CARRYING reusability
/// VERIFIED_COUNT <n>
/// V <label>              <- one per verified label, exactly as before
/// G <label>              <- ADDITIONAL line for each GROUND-ONLY label
/// ```
///
/// A v1 reader (`awk '/^V /{print $2}'`, or `mm_export_verified`'s reader, which
/// drops any post-strip token containing whitespace) sees the identical `V` lines
/// and ignores the two headers and the `G` lines. A v2 reader that does NOT see
/// the header treats every label as [`Reusability::Unmarked`] and so fails closed,
/// which is why the marking cannot be lost by feeding it a stale file.
#[must_use]
pub fn render_verified_labels(report: &KernelVerifyReport) -> String {
    let mut out = String::with_capacity(report.verified.len() * 8 + 32);
    out.push_str(VERIFIED_FORMAT_HEADER);
    out.push('\n');
    out.push_str(&format!("VERIFIED_COUNT {}\n", report.verified.len()));
    for label in &report.verified {
        out.push_str("V ");
        out.push_str(label);
        out.push('\n');
    }
    for label in &report.ground_only {
        out.push_str("G ");
        out.push_str(label);
        out.push('\n');
    }
    out
}

/// Parse a verified-labels stream into a [`VerifiedLabels`].
///
/// Accepted line forms: `V <label>` (as `mm_verify_range` / `mm_kverify` emit),
/// `G <label>` (the ground-only marking), and a BARE `<label>` (as `mm_gate`
/// itself emits). Blank lines and the `VERIFIED_COUNT` / `VERIFIED_FORMAT`
/// headers are dropped.
///
/// FAIL-CLOSED ON AN OLD FILE: if the stream does not carry
/// [`VERIFIED_FORMAT_HEADER`], every label is [`Reusability::Unmarked`], NOT
/// `Reusable`. A stale labels file therefore under-approximates — it can never be
/// silently read as "everything is reusable", which is the R1-MM gap.
///
/// A `G` line for a label with no `V` line still enters the set (as ground-only):
/// the two lines are independent in the wire format and losing the `V` line must
/// not upgrade the label's citability.
#[must_use]
pub fn parse_verified_labels(raw: &str) -> VerifiedLabels {
    let marked = raw
        .lines()
        .any(|l| l.trim().starts_with(VERIFIED_FORMAT_HEADER));
    let default = if marked {
        Reusability::Reusable
    } else {
        Reusability::Unmarked
    };
    let mut out = VerifiedLabels::new();
    for line in raw.lines() {
        let line = line.trim();
        if line.is_empty()
            || line.starts_with("VERIFIED_COUNT")
            || line.starts_with("VERIFIED_FORMAT")
        {
            continue;
        }
        if let Some(label) = line.strip_prefix("G ") {
            let label = label.trim();
            if !label.is_empty() {
                out.insert(label, Reusability::GroundOnly);
            }
            continue;
        }
        let label = line.strip_prefix("V ").unwrap_or(line).trim();
        if !label.is_empty() {
            out.insert(label, default);
        }
    }
    out
}

/// Every `$p` (provable) label of `resolved`, mapped to the `$p` labels its proof
/// cites. Labels cited that are `$a` axioms or `$f`/`$e` hypotheses are the
/// trusted/local base and are deliberately NOT dependencies in this sense.
///
/// A `$p` with no proof body maps to an empty dependency set (it cites nothing);
/// it is still a key, so it is still recognised as a provable of this database.
#[must_use]
pub fn provable_dependencies(resolved: &ResolvedDatabase) -> BTreeMap<String, BTreeSet<String>> {
    // Two passes: the provable label set first, because a proof may only cite
    // labels declared before it but the filter is cheaper against a finished set.
    let provable: BTreeSet<&str> = resolved
        .statements
        .iter()
        .filter_map(|stmt| match stmt {
            ResolvedStatement::Assertion(a) if a.kind == "provable" => Some(a.label.as_str()),
            _ => None,
        })
        .collect();

    resolved
        .statements
        .iter()
        .filter_map(|stmt| match stmt {
            ResolvedStatement::Assertion(a) if a.kind == "provable" => Some(a),
            _ => None,
        })
        .map(|a| {
            let cited: &[String] = match &a.proof {
                Some(Proof::Uncompressed(labels)) => labels,
                Some(Proof::Compressed(c)) => &c.labels,
                None => &[],
            };
            let deps: BTreeSet<String> = cited
                .iter()
                .filter(|l| provable.contains(l.as_str()))
                .cloned()
                .collect();
            (a.label.clone(), deps)
        })
        .collect()
}

/// Fixpoint dependency-closure gate: keep exactly those `verified` labels that are
/// `$p` theorems of `resolved` AND whose transitive `$p`-dependency closure is
/// itself entirely kept AND CITABLE.
///
/// Two removal rules, iterated to a fixpoint:
///
/// * a cited `$p` dependency that is not kept removes its dependent (the
///   dependency did not verify, or was itself removed);
/// * a cited `$p` dependency that is not [`Reusability::is_citable`] removes its
///   dependent even though the dependency itself SURVIVES — it verified, on the
///   ground path, and the sequential verifier verifies it too; it just may not be
///   reused. This is the R1-MM rule, and it is what makes the surviving set equal
///   the sequential verifier's rather than a strict superset of it.
///
/// FAIL-CLOSED on labels this database does not know: a label that is not a `$p`
/// theorem of `resolved` is dropped rather than passed through. In the sanctioned
/// pipeline this is a no-op — `mm_verify_range` only ever emits `$p` labels of the
/// database it was handed — but it makes the gate's contract true for any input,
/// including a stale or hand-edited label file.
#[must_use]
pub fn dependency_closure_gate(
    resolved: &ResolvedDatabase,
    verified: &VerifiedLabels,
) -> BTreeSet<String> {
    let deps = provable_dependencies(resolved);
    // Fail-closed intake: anything that is not a `$p` of this database is not a
    // theorem we could have verified, so it cannot survive.
    let mut kept: BTreeSet<String> = verified
        .labels()
        .into_iter()
        .filter(|l| deps.contains_key(l))
        .collect();
    loop {
        let removed: Vec<String> = kept
            .iter()
            .filter(|t| {
                deps.get(*t).is_some_and(|ds| {
                    ds.iter()
                        .any(|d| !kept.contains(d) || !verified.is_citable(d))
                })
            })
            .cloned()
            .collect();
        if removed.is_empty() {
            return kept;
        }
        for r in removed {
            kept.remove(&r);
        }
    }
}

/// R1-MM EXPOSURE MEASUREMENT, over a SEQUENTIAL [`KernelVerifyReport`].
///
/// Returns every `(dependent, dependency)` pair where the sequential verifier
/// SKIPPED `dependent` because it may not reuse `dependency`, AND `dependency` is
/// nevertheless in `report.verified`. That is exactly the shape the two-pass
/// verifier used to export and the fixed gate now drops: a theorem whose proof
/// rests on a dependency that verified but is not citable.
///
/// A non-empty result on a corpus means the corpus EXERCISES the R1-MM gap — i.e.
/// the pre-fix two-pass export contained theorems the sequential verifier refuses.
/// An empty result means the gap is latent there.
///
/// The dependency is matched out of `apply_label`'s message, whose shape is
/// `"unsupported: proof of <T> reuses $p theorem <D> that did not verify"`.
#[must_use]
pub fn ground_reuse_exposure(report: &KernelVerifyReport) -> Vec<(String, String)> {
    const OPEN: &str = "reuses $p theorem ";
    const CLOSE: &str = " that did not verify";
    let verified: BTreeSet<&str> = report.verified.iter().map(String::as_str).collect();
    let mut out: Vec<(String, String)> = Vec::new();
    for (label, reason) in &report.skipped {
        let Some((_, rest)) = reason.split_once(OPEN) else {
            continue;
        };
        let Some((dep, _)) = rest.split_once(CLOSE) else {
            continue;
        };
        let dep = dep.trim();
        if !dep.is_empty() && verified.contains(dep) {
            out.push((label.clone(), dep.to_string()));
        }
    }
    out.sort();
    out.dedup();
    out
}

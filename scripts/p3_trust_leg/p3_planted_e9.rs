// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! P3, Trust leg: the planted proof of `False` through `trust-certify`'s
//! island door and its E9 lane, which ends in the `ReferenceCertificate` the
//! compiler's `Certified` mint requires (`trust_certify::reference_certificate_for`).
//!
//! This file belongs to Clean (`scripts/p3_trust_leg/`), not to Trust: Clean's
//! `scripts/patched_kernel_control_trust.py` copies it into a scratch copy of
//! Trust's tree as `crates/trust-certify/tests/p3_planted_e9.rs`, once over an
//! unmodified `first-party/clean` and once over the copy whose
//! `TypeChecker::check_type` also accepts `Nat.zero : False` (P3's mutant M1),
//! and runs it in each. Nothing of it lands in Trust.
//!
//! The sites, in order:
//!
//! * `trust.island.source`: the planted SOURCE through Trust's island door
//!   (`check_clean_island`). Its elaborator compares a body with its type by
//!   `is_def_eq`, which M1 does not touch, so it is expected to refuse in both
//!   legs: that refusal is the same kernel's other entry, not an independent
//!   check (a mutant one function over would pass it).
//! * `kernel.add_decl`: the planted theorem made resident in the island
//!   environment through clean-kernel's own door, `Environment::add_decl`. No
//!   Trust code runs here; it stands in for an island constant that reached the
//!   environment, which the island door above does not let this source do (the
//!   `trust.*.let_rec*` rows at the end reach it from source). The rows after
//!   it, up to those, are therefore conditional on that residency.
//! * `trust.island.reference_recheck`: the island's reference gate
//!   (`reference_mint::check_registered_in`) on the resident constant.
//! * `trust.e9.certify_ensures_discharge`, `trust.e9.reference_entry`,
//!   `trust.e9.registered_certificate`: `ensures false by p3_planted` through
//!   the E9 lane: the audited certificate, the fenced entry's certificate on
//!   it, and the certificate the compiler reads back for the row's payload. In
//!   Trust's Rust contract surface `false` in proposition position elaborates
//!   to Lean's `False`; the test asks the elaborator and fails unless the goal
//!   is exactly the constant `False`, the type M1 accepts `Nat.zero` at.
//! * `trust.reference_mint.check_closed_in`: the fenced entry asked directly
//!   about the closed pair, whatever is resident.
//! * `trust.reference_mint.check_island_judgment_in.universe`: the other
//!   branch of the island's anonymous-judgment check (`IslandReference::
//!   check_judgment` is crate-private; this is its public kernel path), on
//!   `∀ (_ : Sort u), False` proved by `fun _ => p3_planted`: a universe
//!   parameter sends it through the entry's `add_checked`.
//! * `trust.e9.grade.kernel_discharge_ensures_citation`: the E9 grade the
//!   compiler's cited lane reads before it routes the clause and mints
//!   (`kernel_discharge_ensures_citation_in`, then `cert_meter::grade`). The
//!   compiler climbs the conditional rungs only when this grade fails, so the
//!   planted pair never reaches them.
//! * `trust.e9.domains.*`: the exact-domain E9 mint
//!   (`certify_ensures_discharge_with_domains`), the same three stages as the
//!   scalar lane above. Nothing in the compiler calls this lane at the
//!   measured Trust (it mints through the scalar lane only), and its fenced
//!   entry is the same `check_closed_in` call on the same pair as
//!   `trust.e9.reference_entry` and `trust.reference_mint.check_closed_in`.
//! * `trust.island.example_source`, `trust.island_batch.example_source`:
//!   `example : False := Nat.zero` through the island door and the batched
//!   door (`CleanIslandSession::check_all`), the feeders of
//!   `IslandReference::check_judgment`. Like `trust.island.source`, the
//!   elaborator's `is_def_eq` refuses it in both legs.
//! * `trust.calculus.*`: a calculus row (`certify_calculus_row`) over a
//!   STAND-IN VF5 family admitted by `calculus_row::test_support::
//!   pin_own_digest` (Trust's `calculus-row-test-support` feature; no
//!   production pin admits any base today). `producer_annotation` hands the
//!   planted pair to the row as the producer's annotation, judged as an
//!   application argument (by `is_le`, not `check_type`), so both legs refuse;
//!   `certify_calculus_row` and `registered_bound` cite the resident
//!   `p3_planted` from the family's `row_of`. The test registers the
//!   certificate itself (`calculus_row::register`, as the compiler's own
//!   calculus tests do: no Trust code path certifies or registers a calculus
//!   row at the measured Trust), and `registered_bound` is the compiler's
//!   lookup (`calculus_row_certificate_bound`) on it.
//! * `trust.refutation.*`: presented violation-refutation evidence. The
//!   honest certificate for `x < 0 ∧ 0 < x` (`certify_vc`) is presented again
//!   with its term replaced by `Nat.zero` and its lineage recomputed (an
//!   unkeyed hash, reimplemented here). `replay_presented_vc_evidence` and
//!   `reference_certificate_for` read the reference entry, which judges the
//!   term closed over the obligation's hypotheses, a shape M1 does not match;
//!   `recheck_presented_linear_int_vc` checks the open term at `False` and
//!   consults no reference entry. Where the replay is refused is measured by
//!   the runner, not here: it runs this test with `TRUST_KR0_DEBUG=1`, Trust's
//!   measurement-only report of each reference-entry refusal (lane `int`).
//! * `trust.island.let_rec_source`, `trust.island_batch.let_rec_source`: the
//!   planted pair from SOURCE, `theorem p3_letrec_src : False := let rec go :
//!   False := Nat.zero; go`, through both island doors (the batched one is the
//!   compiler's, whose session environment it stashes for the in-walk E9
//!   lane). Read at Clean `e64e4b790`: the elaborator lifts the non-recursive
//!   `let rec` with no check of the helper's annotated value (it leaves that
//!   mismatch to the kernel), the parent's body type is `False`, so its
//!   `is_def_eq` gate has nothing to refuse, and the helper is registered as
//!   the theorem `p3_letrec_src.go : False := Nat.zero`, whose `add_decl`
//!   asks `check_type` exactly the planted pair. So M1 alone decides these
//!   doors.
//! * `trust.e9.let_rec.*`, `trust.e9.let_rec_parent.*`: on the batched door's
//!   session environment, `ensures false by <helper>` (its stored value is
//!   `Nat.zero`) and `ensures false by p3_letrec_src` (its value is the helper,
//!   whose declaration the audit's dependency walk re-checks), each through
//!   the scalar E9 lane's three stages and the grade, under a function name of
//!   its own so no payload repeats another row's. With the door refused the
//!   session has no environment and nothing is cited.
//!
//! Controls run in both legs and must pass, or the leg measures nothing
//! (`P3 VACUOUS`): the honest source `theorem p3_honest_src : True :=
//! True.intro` is accepted by the island door, `ensures true by p3_honest`
//! reaches a registered certificate through both E9 mints and is graded
//! certified, `∀ (_ : Sort u), True` by `fun _ =>
//! p3_honest` passes the universe branch, `example : True := True.intro`
//! passes both doors, the honest stand-in family certifies and binds a
//! calculus row, and the honest refutation certificate is issued, replayed
//! cold under a recomputed lineage (which checks the reimplemented hash) and
//! rechecked by the linear-Int lane; and the honest `let rec` source
//! (`theorem p3_letrec_honest_src : True := let rec go : True := True.intro;
//! go`) passes both doors, and its helper and parent are cited through the E9
//! lane and graded certified.
//!
//! Every pin, control and row is printed before anything is asserted (the
//! shared contract, below), so a red run still shows the whole measurement.
//!
//! The file is split at module boundaries. `scripts/p3_trust_leg/` mirrors the
//! `tests/` directory it is installed into, and the runner records every
//! installed file's digest: `p3_planted_e9/` holds `lanes.rs` (the island
//! doors and the E9 lane), `evidence.rs` (the calculus row and the refutation
//! evidence), `controls.rs` and `planted.rs`; `p3_contract/contract.rs` is
//! shared with the temporal test (the declared kernel, the liveness check, the
//! printed lines and the comparison with the pins). Cargo takes neither
//! directory for a test target of its own.

#[path = "p3_contract/contract.rs"]
mod contract;
#[path = "p3_planted_e9/controls.rs"]
mod controls;
#[path = "p3_planted_e9/evidence.rs"]
mod evidence;
#[path = "p3_planted_e9/lanes.rs"]
mod lanes;
#[path = "p3_planted_e9/planted.rs"]
mod planted;

use clean_kernel::Environment;

use crate::contract::{Outcome, Pin};

const FUNCTION: &str = "p3_trust_leg_fn";
const PLANTED_SOURCE: &str = "theorem p3_planted_src : False := Nat.zero\n";
const HONEST_SOURCE: &str = "theorem p3_honest_src : True := True.intro\n";
const PLANTED_EXAMPLE: &str = "example : False := Nat.zero\n";
const HONEST_EXAMPLE: &str = "example : True := True.intro\n";
const LET_REC_SOURCE: &str =
    "theorem p3_letrec_src : False :=\n  let rec go : False := Nat.zero\n  go\n";
const HONEST_LET_REC_SOURCE: &str =
    "theorem p3_letrec_honest_src : True :=\n  let rec go : True := True.intro\n  go\n";
const CALCULUS_ARTIFACT: &[u8] = b"p3-calculus-row-artifact";
/// Trust's `LINEAGE_DOMAIN` (`trust-certify/src/lib.rs`).
const LINEAGE_DOMAIN: &[u8] = b"trust-certify.cleancic.v3";

/// The outcome each site is pinned to, per declared kernel (`contract::Pin`).
const PINS: &[Pin] = &[
    ("trust.island.source", Outcome::Refused, Outcome::Refused),
    ("kernel.add_decl", Outcome::Refused, Outcome::Minted),
    ("trust.island.reference_recheck", Outcome::Refused, Outcome::Minted),
    ("trust.e9.certify_ensures_discharge", Outcome::Refused, Outcome::Minted),
    ("trust.e9.reference_entry", Outcome::Refused, Outcome::Minted),
    ("trust.e9.registered_certificate", Outcome::Refused, Outcome::Minted),
    ("trust.reference_mint.check_closed_in", Outcome::Refused, Outcome::Minted),
    ("trust.reference_mint.check_island_judgment_in.universe", Outcome::Refused, Outcome::Minted),
    ("trust.e9.grade.kernel_discharge_ensures_citation", Outcome::Refused, Outcome::Minted),
    ("trust.e9.domains.certify_ensures_discharge_with_domains", Outcome::Refused, Outcome::Minted),
    ("trust.e9.domains.reference_entry", Outcome::Refused, Outcome::Minted),
    ("trust.e9.domains.registered_certificate", Outcome::Refused, Outcome::Minted),
    ("trust.island.example_source", Outcome::Refused, Outcome::Refused),
    ("trust.island_batch.example_source", Outcome::Refused, Outcome::Refused),
    ("trust.calculus.producer_annotation", Outcome::Refused, Outcome::Refused),
    ("trust.calculus.certify_calculus_row", Outcome::Refused, Outcome::Minted),
    ("trust.calculus.registered_bound", Outcome::Refused, Outcome::Minted),
    ("trust.refutation.replay_presented_vc_evidence", Outcome::Refused, Outcome::Refused),
    ("trust.refutation.reference_certificate", Outcome::Refused, Outcome::Refused),
    ("trust.refutation.recheck_presented_linear_int_vc", Outcome::Refused, Outcome::Minted),
    ("trust.island.let_rec_source", Outcome::Refused, Outcome::Minted),
    ("trust.island_batch.let_rec_source", Outcome::Refused, Outcome::Minted),
    ("trust.e9.let_rec.certify_ensures_discharge", Outcome::Refused, Outcome::Minted),
    ("trust.e9.let_rec.reference_entry", Outcome::Refused, Outcome::Minted),
    ("trust.e9.let_rec.registered_certificate", Outcome::Refused, Outcome::Minted),
    ("trust.e9.let_rec.grade", Outcome::Refused, Outcome::Minted),
    ("trust.e9.let_rec_parent.certify_ensures_discharge", Outcome::Refused, Outcome::Minted),
    ("trust.e9.let_rec_parent.reference_entry", Outcome::Refused, Outcome::Minted),
    ("trust.e9.let_rec_parent.registered_certificate", Outcome::Refused, Outcome::Minted),
    ("trust.e9.let_rec_parent.grade", Outcome::Refused, Outcome::Minted),
];

#[test]
fn p3_planted_false_through_trust_certify_e9_lane() {
    let mut failures = Vec::new();
    let mut env = Environment::with_prelude();
    let declared = contract::start(PINS, &env, &mut failures);
    lanes::check_goals(&mut failures);
    let honest = controls::controls(&mut env, &mut failures);
    contract::report_controls(&honest.control, &mut failures);
    let rows = planted::rows(&mut env, &honest, &mut failures);
    contract::finish(&rows, PINS, declared, failures);
}

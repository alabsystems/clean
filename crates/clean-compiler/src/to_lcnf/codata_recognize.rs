// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Validated recognition of corecursive definitions (rank 7, brick B3).
//!
//! # Why this is not a name match
//!
//! The rank-7 direct-lazy lowering needs to know that a definition's body is a
//! generated corecursor application, so it can emit `Corec`/`Delay`/`Force`
//! instead of the generic `M`-type path. The design's unanimous DO-NOT is that
//! this must never be inferred from a name: `C.corec` is a *user-derivable*
//! name — nothing stops anyone writing `def Stream.corec` — so a name match
//! would let a hand-written definition impersonate generated codata.
//!
//! [`CodataOrigin`] exists to remove the guessing, but it is a **hint**, not
//! evidence. Holding one authorizes nothing. This module's job is to take the
//! hint and go *check it against the current environment*, declining unless
//! every claim in it still holds. The hint says what to look at; these checks
//! are what justify acting.
//!
//! # Fail-closed
//!
//! Every path returns [`None`] on the slightest mismatch, in the style of
//! `rec_apply_parts`. Declining is safe: rank 7's generic fallback does not
//! compile at all (`verify_recursor_calls_certifiable` refuses a valueless
//! recursor reaching final IR, and the codata corecursor bottoms out in
//! `Nat.rec` over a type family), so a decline surfaces as a hard compile
//! error rather than a silently different program. That is the honest outcome.
//!
//! # What this brick does NOT yet establish
//!
//! This is deliberately the *first* half of recognition, and it lands with its
//! must-refuse battery before any emitter exists, so nothing can act on a
//! partial check.
//!
//! It validates the corecursor's **identity and shape in the current
//! environment**: that the origin resolves, that the head constant is that
//! exact corecursor, that the corecursor still carries the recorded slot names,
//! that it is a real definition with a stored value, that its result type is
//! headed by the recorded carrier, and that the application is saturated at the
//! recorded arity.
//!
//! It also REPLAYS the corecursor's own canonical generated body (B3b): the
//! body must be the seed primitive for its lane applied to the carrier's own
//! polynomial descriptor. That closes the gap where a hand-written definition
//! with the right type and parameter names would pass identity checks alone.
//!
//! What remains outstanding: the replay pins the body's canonical HEAD and
//! descriptor, not every argument position, and nothing here reasons about the
//! codef's clause bodies. A full generator-equivalence replay is still future
//! work, so [`RecognizedCorec`] is evidence that recognition is sound to act
//! on — NOT a proof that the emitted program refines the source. That proof is
//! the observational soundness artifact (B7) and it does not exist yet.

use clean_kernel::{CodataLane, Environment, Expr, ExprKind, Name};

use super::lower::collect_app_args;

/// A corecursive application whose [`CodataOrigin`] hint has been re-checked
/// against the environment.
///
/// See the module docs for exactly which claims this represents — in
/// particular it is NOT yet a full canonical-body replay.
#[derive(Clone, Debug)]
pub struct RecognizedCorec {
    /// The codata carrier, re-resolved (not merely quoted from the hint).
    pub carrier: Name,
    /// The corecursor constant actually applied.
    pub corec: Name,
    /// Which lane generated it — drives which canonical shape applies.
    pub lane: CodataLane,
    /// The corecursor's arguments, in application order.
    pub args: Vec<Expr>,
    /// How many of those are the per-field slot lambdas.
    pub slot_count: usize,
    /// How many parameter binders the codef itself declares -- the leading
    /// lambdas peeled off before the corecursor application was found.
    pub param_count: usize,
}

/// Recognize `value` as the validated corecursive body of `def_name`.
///
/// Returns `None` — decline — unless every recorded claim re-checks. See the
/// module docs; a decline is a hard compile error downstream, by design.
pub fn recognize_codata_corec(
    env: &Environment,
    def_name: &Name,
    value: &Expr,
) -> Option<RecognizedCorec> {
    // (1) The hint. Absence downgrades: no origin, no recognition. An
    // environment restored from an artifact carries no origins at all
    // (`#[serde(skip)]`), so this correctly declines there too.
    let origin = env.get_codata_origin(def_name)?;

    // (2) Peel the codef's OWN parameter binders. A `codef f (n : Nat) (acc :
    // Nat) : C n` stores `fun n acc => @C.corec …`, so the corecursor
    // application sits under one lambda per declared parameter; only a
    // parameterless codef stores the application directly. Peeling is not
    // cosmetic -- these binders are the corecursive value's parameters and the
    // emitter needs their count.
    let mut body = value;
    let mut param_count = 0usize;
    while let ExprKind::Lam(_, _, inner) = body.kind() {
        body = inner.as_ref();
        param_count += 1;
    }

    // The body must then be an application whose head is a constant.
    let (head, args) = collect_app_args(body);
    let ExprKind::Const(applied, _) = head.kind() else {
        return None;
    };

    // (3) That constant must be THE corecursor the origin names. This is a
    // filter, not the evidence -- everything below re-derives from the
    // environment rather than from the hint.
    if applied != &origin.corec {
        return None;
    }

    // (4) The corecursor must still resolve, and must be a real definition
    // with a stored value. A valueless constant of the same name (an axiom, or
    // a kernel recursor) is NOT the generated corecursor, and would be refused
    // downstream anyway.
    let corec_info = env.get_const(&origin.corec)?;
    corec_info.value.as_ref()?;

    // (5) RE-DERIVE the slot names from the corecursor as it exists in this
    // environment, by the same rule the generator used, and require the result
    // to equal what was recorded. Re-deriving rather than reading the hint is
    // the point: a corecursor that has been replaced or re-registered with a
    // different shape no longer reproduces its own recorded slots.
    let (live_slots, derived_lane) = derive_slot_names(env, &origin.corec)?;
    if !slots_match(&live_slots, &origin.slots) {
        return None;
    }
    // The lane is itself a claim, so check it against the derived shape rather
    // than trusting it -- a hint whose lane was flipped would otherwise select
    // the wrong canonical form downstream.
    if derived_lane != origin.lane {
        return None;
    }

    // (6a) CARRIER PROVENANCE: the `codata` command must have generated this
    // carrier in THIS environment. Without it, recognition was satisfiable
    // without the codata command ever running -- a hand-written type plus a
    // hand-written `<C>.corec` with the right parameter names passed every
    // other check (found by adversarial review). Absence declines, and an
    // environment restored from an artifact has no marks at all.
    if !env.is_codata_carrier(&origin.carrier) {
        return None;
    }

    // (6) The recorded carrier must resolve, and the corecursor's result type
    // must actually be headed by it. This is the structural link between the
    // corecursor and the codata type, re-derived from the corecursor's own
    // stored type rather than taken on faith from the hint.
    env.get_const(&origin.carrier)?;
    if !result_head_is(&corec_info.type_, &origin.carrier) {
        return None;
    }

    // (7) REPLAY the corecursor's own canonical generated body (B3b). Steps
    // (4)-(6) establish identity and shape; a hand-written definition with the
    // right type, the right parameter names and the right carrier would still
    // pass all of them. This is the step that looks at what the corecursor
    // actually DOES.
    replay_canonical_corec_body(env, &origin.corec, &origin.carrier, origin.lane)?;

    // (8) Saturation: the application must supply at least one argument per
    // recorded slot, plus the initial state. An unsaturated (partially
    // applied) corecursor is not a corecursive VALUE and must not be
    // recognized as one.
    let slot_count = origin.slots.len();
    if args.len() <= slot_count {
        return None;
    }

    Some(RecognizedCorec {
        carrier: origin.carrier.clone(),
        corec: origin.corec.clone(),
        lane: origin.lane,
        args: args.into_iter().cloned().collect(),
        slot_count,
        param_count,
    })
}

/// Replay a corecursor's own canonical generated body (B3b).
///
/// Steps (4)-(6) of recognition establish that the corecursor has the right
/// identity, shape and carrier. None of them looks at what it computes, so a
/// hand-written definition carrying the right type and parameter names would
/// satisfy every one of them. This is the check that closes that gap.
///
/// The generator emits exactly one canonical form per lane: parameter lambdas
/// wrapping an application of the seed primitive `Codata.ucorec` (plain) or
/// `Codata.IMcorec` (indexed) to the carrier's own polynomial descriptor
/// (`<C>.shapeF`, `<C>.posF`, `<C>.tgtF`). Both halves are required: the
/// primitive alone would accept a corecursor over somebody ELSE's descriptor.
///
/// # Why anchoring on `Codata.*` is not the name-matching this module forbids
///
/// The rule is that recognition must not key off a name a USER can mint.
/// `C.corec` is exactly such a name — that is the whole reason `CodataOrigin`
/// exists. `Codata.*` is reserved by the seed library, and
/// `ensure_codata_seeds` refuses to seed when a foreign `Codata.*` constant is
/// present.
///
/// An earlier version of this comment claimed more than the code supported. It
/// asserted that a `Codata.ucorec` in a seeded environment is necessarily the
/// seed's own. It was not: the seed's idempotence check short-circuited on the
/// sentinel `Codata.IMIntl` BEFORE the namespace pre-scan, and that sentinel is
/// an ordinary user-definable name, so a single squatted definition turned
/// seeding into a no-op and left the namespace open. The check now requires
/// several witnesses, which closes that particular route.
///
/// The honest statement of what carries the weight: the load-bearing gate is
/// CARRIER PROVENANCE (step 6a — the `codata` command must have generated the
/// carrier in this environment), not this namespace argument. An adversarial
/// review demonstrated a source file that hand-wrote its own carrier,
/// descriptors, `Codata.ucorec` and `C.corec`, minted a real origin through
/// `codef`, and passed this replay — recognition was breakable from source
/// with the namespace argument intact. Treat the reservation as
/// defence-in-depth; provenance is the gate.
fn replay_canonical_corec_body(
    env: &Environment,
    corec: &Name,
    carrier: &Name,
    lane: CodataLane,
) -> Option<()> {
    let value = env.get_const(corec)?.value.clone()?;

    // Peel the corecursor's own parameter lambdas.
    let mut body = &value;
    while let ExprKind::Lam(_, _, inner) = body.kind() {
        body = inner.as_ref();
    }

    let (head, args) = collect_app_args(body);
    let ExprKind::Const(prim, _) = head.kind() else {
        return None;
    };

    // The seed primitive for this lane, and no other.
    let want = match lane {
        CodataLane::Plain => "Codata.ucorec",
        CodataLane::Indexed => "Codata.IMcorec",
    };
    if prim.to_string() != want {
        return None;
    }

    // Over THIS carrier's descriptor, AT THE POSITIONS the generator puts it.
    //
    // Checking only that the descriptors are MENTIONED somewhere in the
    // application was too weak: a body could satisfy it by naming them inside
    // an unused argument while the corecursor actually ran on somebody else's
    // descriptor, and the emitted index would then advance per `C.tgtF` while
    // the corecursor advanced per the foreign one. Measured positions (they are
    // the leading arguments, after the index type in the indexed lane):
    //
    //   Codata.ucorec  <C>.shapeF <C>.posF <C>.tgtF …
    //   Codata.IMcorec I <C>.shapeF <C>.posF <C>.tgtF …
    let base = match lane {
        CodataLane::Plain => 0,
        CodataLane::Indexed => 1,
    };
    for (k, suffix) in ["shapeF", "posF", "tgtF"].iter().enumerate() {
        let want = Name::from_string(&format!("{carrier}.{suffix}"));
        env.get_const(&want)?;
        let arg = args.get(base + k)?;
        match arg.kind() {
            ExprKind::Const(n, _) if n == &want => {}
            _ => return None,
        }
    }

    Some(())
}

/// Re-derive a corecursor's per-field slot names, and whether it is indexed,
/// from the environment.
///
/// This mirrors the generator's own rule (`codata_cmd.rs`): the slots are the
/// EXPLICIT parameters, less the trailing state argument, less the index for an
/// indexed corecursor. It is deliberately a re-derivation rather than a read of
/// the recorded list — comparing a re-derivation against the record is what
/// makes a tampered or replaced corecursor fail.
///
/// The indexed lane is identified the same way the generator identifies it: the
/// generated per-field slots are `F`-suffixed, so a trailing explicit parameter
/// that is not `F`-suffixed is the index.
fn derive_slot_names(env: &Environment, corec: &Name) -> Option<(Vec<String>, CodataLane)> {
    let names = env.get_param_names(corec)?;
    let infos = env.get_param_binder_infos(corec)?;
    if names.len() != infos.len() {
        return None;
    }
    let mut slots: Vec<String> = names
        .iter()
        .zip(infos.iter())
        .filter(|(_, i)| matches!(i, clean_kernel::BinderInfo::Default))
        .map(|(n, _)| n.clone())
        .collect();
    // The trailing explicit parameter is the initial state.
    slots.pop()?;
    let lane = if slots.last().is_some_and(|s| !s.ends_with('F')) {
        // One more trailing explicit parameter that is not a field slot: the index.
        slots.pop();
        CodataLane::Indexed
    } else {
        CodataLane::Plain
    };
    if slots.is_empty() {
        return None;
    }
    Some((slots, lane))
}

/// Do the corecursor's re-derived slot names match the recorded ones exactly?
fn slots_match(live: &[String], recorded: &[String]) -> bool {
    live.len() == recorded.len() && live.iter().zip(recorded).all(|(a, b)| a == b)
}

/// Is `ty`'s Pi-result headed by the constant `want`?
fn result_head_is(ty: &Expr, want: &Name) -> bool {
    let mut cur = ty;
    while let ExprKind::Pi(_, _, body) = cur.kind() {
        cur = body.as_ref();
    }
    let mut head = cur;
    while let ExprKind::App(f, _) = head.kind() {
        head = f.as_ref();
    }
    matches!(head.kind(), ExprKind::Const(n, _) if n == want)
}

#[cfg(test)]
#[path = "codata_recognize_tests.rs"]
mod tests;

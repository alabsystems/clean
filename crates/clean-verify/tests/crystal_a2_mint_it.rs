// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Crystal A2 — the MINT gate for `ir_it`, THE CRYSTAL'S DESIGNATED TARGET.**
//!
//! Same three readers and the same questions as `crystal_a2_mint.rs` and
//! `crystal_a2_mint_its.rs`; read `crystal_a2_mint.rs`'s header and
//! `src/ir_mint/mod.rs` for what this establishes and what it does not.
//!
//! **Why this file exists.** Eighteen chains had an A2 mint gate and the target
//! did not. Reader A's projection for `TypeChecker::infer_type` has been
//! committed since 2026-09-16 (`generated/ir_it.core.txt` and its
//! `.prov.json`), and `eval_ir_it.rs` replays the minted script — but nothing
//! made reader B read the emitted text or reader C read the elaborated term. On
//! the sibling chain that was not a formality: writing `crystal_a2_mint_its.rs`
//! found that a published "first `usize`" claim and a published reader-agreement
//! claim had both been made about a body reader B had never read, because reader
//! B refused the fixture outright until a `usize` lane existed. A hand reading is
//! not a gate. This is the target's gate.
//!
//! # How this chain differs from every other one, and what the gate pins
//!
//! `ir_it` is not a larger `ir_its`. It is the first chained body with real
//! shape. Two of its properties invert assertions the sibling gates make, and a
//! third looked like it did and did not:
//!
//! * **Control flow and calls.** Six blocks, a `switch` with an `unreachable`
//!   default, and TWO calls — `tick_heartbeat` and `infer_type_fast`. Every
//!   other A2 gate asserts the ABSENCE of `switch`/`call` as the reason its A4
//!   needs no activation induction. Here their PRESENCE is the pin.
//! * **The unwitnessed ledger is NOT empty** — exactly one slot, `bb1#1 switch
//!   arg4`, because trust-ir's `Display` never prints
//!   `Switch.exhaustive_enum_unreachable`. `crystal_a2_mint_its.rs` asserts an
//!   empty ledger and is right to; asserting it here would be false. The gate
//!   pins the count at one and pins WHICH slot, so a second unwitnessed slot
//!   appearing is a failure rather than a silent widening of what the emitted
//!   text is allowed not to say.
//! * **The self-func pin turned out to be INERT here, and that was measured
//!   rather than reasoned.** This file first asserted the opposite — that a body
//!   which CALLS things needs `self_crate_id` interned first or every callee id
//!   shifts. The gate failed on its own arm. A callee interns at 1 whether or
//!   not the self id is pinned (`Reader::with_self_at` says so in a comment),
//!   and the pin only bites for a body that calls ITSELF, which this one does
//!   not. `m10` now pins the EQUALITY, with the no-self-call premise checked
//!   beside it, so the day that premise breaks the arm fires. Writing the gate
//!   is what corrected the claim, which is the second time on this pair of
//!   chains that has happened.
//!
//! # What this gate does NOT establish
//!
//! Anything about link 2b. No codegen flip fires for this body at either opt
//! level, so nothing here binds the term to the shipped artifact. What the gate
//! establishes is the A2 question only: that the term `eval_ir_it.rs`'s
//! definitions are about IS the emitted body, by three readers that do not share
//! a path. It is also silent on whether the lowering that produced the bundle is
//! complete — it is not; the bundle is a partial closure and says so.

use clean_verify::ir_mint::{self, SelfFunc, Sx};

const PREFIX: &str = "ir_it";
const MODULE_CONST: &str = "ir_it_module";
const FIXTURE: &str = ir_mint::IR_IT_EMITTED;

/// This body's own crate-level `@func.N` id, from the tag table's `funcs` lane
/// row whose `role` is `SELF`. Pinned as a literal here and CHECKED against the
/// table in `m10`, so the two cannot drift apart silently.
const SELF_FUNC_ID: u32 = 0;

fn tags() -> ir_mint::Tags {
    ir_mint::tags::parse(ir_mint::IR_IT_TAGS).expect("the committed tag table must parse")
}

fn core_a() -> Sx {
    ir_mint::parse(ir_mint::IR_IT_CORE).expect("the committed core module must parse")
}

fn core_b() -> Sx {
    ir_mint::read_emitted_with_pins(FIXTURE, SelfFunc::Pinned(SELF_FUNC_ID), Some(64))
        .expect("reader B must read the committed emitted trust-ir under the self and width pins")
        .0
}

fn canon(sx: &Sx) -> String {
    ir_mint::print(sx).expect("a core module must print")
}

// ────────────────────────────────────────────────────────────────────────────
// M1 — the committed core is canonical, and it is THIS body.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m1_committed_core_round_trips_its_printer() {
    let a = core_a();
    assert_eq!(
        canon(&a),
        ir_mint::IR_IT_CORE,
        "the committed core module is not what its own canonical printer produces"
    );
    let text = ir_mint::IR_IT_CORE;
    assert!(
        text.contains("(switch"),
        "the target's core MUST carry the switch — its absence would mean the projection \
         flattened the discriminant test this body exists to perform:\n{text}"
    );
    assert!(
        text.contains("(call "),
        "and the calls, which is what makes this body's closure nontrivial and its A4 a \
         different problem from every single-block chain's"
    );
    assert!(
        text.contains("(unreachable)"),
        "and the unreachable default arm — the slot the emitted text cannot witness"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M2 — reader B equals reader A, with the ONE documented unwitnessed slot.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m2_reader_b_equals_reader_a_modulo_one_named_slot() {
    let (masked, ledger) =
        ir_mint::mask_text_unwitnessed(&core_a()).expect("reader A's module must mask");
    assert_eq!(
        canon(&masked),
        canon(&core_b()),
        "the artifact BINARY (reader A, via a2project over the infer_type callee bundle) and \
         the emitted TEXT (reader B) disagree about THE DESIGNATED TARGET. Until this file \
         existed, that agreement had never been checked by a reader at all."
    );
    assert_eq!(
        ledger.len(),
        1,
        "exactly ONE unwitnessed slot is expected here, not zero and not two. Zero would mean \
         the switch's exhaustiveness flag had become printable; two would mean the emitted \
         text stopped determining something it used to. Ledger: {ledger:?}"
    );
    let slot = format!("{:?}", ledger[0]);
    assert!(
        slot.contains("switch"),
        "and the one slot must be the SWITCH arm, which is the only thing trust-ir's Display \
         is documented not to print: {slot}"
    );
    assert!(
        ir_mint::IR_IT_RECORD.contains("exhaustive_enum_unreachable"),
        "and the mint record must name the reason, so the exemption is a written claim"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M3 — `mint` of the committed core IS the committed, registered script.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m3_mint_reproduces_the_registered_script() {
    let minted = ir_mint::mint(&core_a(), PREFIX, &tags())
        .expect("mint")
        .text();
    assert_eq!(
        minted,
        ir_mint::IR_IT_DEFS,
        "minting the committed core does not reproduce the committed script that \
         `eval_ir_it.rs` replays — so the definitions the target's results are stated over are \
         not the lines this core mints to"
    );
    assert_eq!(
        minted.lines().filter(|l| !l.trim().is_empty()).count(),
        13,
        "thirteen definitions — six blocks, the function, the module, and the rest. The count \
         is pinned because a dropped block would still mint, still parse, and still be a \
         perfectly good module of a DIFFERENT function"
    );
    assert!(
        ir_mint::IR_IT_RECORD.contains("\"def_count\": 13"),
        "and the mint record must agree with what mint just produced"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M4 — reader C: the ELABORATED term decodes back to the committed core.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m4_the_registered_kernel_term_decodes_to_the_committed_core() {
    let spec = clean_verify::test_utils::shared_spec();
    let decoded = ir_mint::decode(spec.env(), MODULE_CONST, &tags()).expect("decode ir_it_module");
    assert_eq!(
        canon(&decoded),
        ir_mint::IR_IT_CORE,
        "the ELABORATED term registered under `{MODULE_CONST}` does not decode to the committed \
         core module. This is the check that keeps `mint` out of the trusted base: reader C \
         never sees the minter's output, and it is what makes anything proved over \
         `ir_it_module` a statement about the EMITTED body rather than about whatever the \
         minter happened to write."
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M7 — the tag table still matches the artifact.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m7_the_tag_table_still_matches_the_artifact() {
    assert!(
        FIXTURE.contains("(functy.0)"),
        "the emitted body must still carry signature index 0; if it does not, the artifact was \
         re-interned and this table needs a one-line REVIEWED re-pin"
    );
    assert!(
        ir_mint::IR_IT_TAGS.contains("\"functy\": 0"),
        "and the committed table must record it"
    );
    assert!(
        FIXTURE.contains("struct.") && FIXTURE.contains("@func."),
        "unlike every single-block chain, this body DOES name aggregates and DOES call — the \
         non-empty structs and funcs lanes are what must be pinned, not their emptiness"
    );
    for id in [
        "struct.1",
        "struct.2",
        "struct.16",
        "struct.18",
        "struct.19",
    ] {
        assert!(
            FIXTURE.contains(id),
            "the emitted text must still name {id}; the structs lane pins five rows and a \
             dropped one would silently shrink what the tag table has to explain"
        );
    }
}

// ────────────────────────────────────────────────────────────────────────────
// M9 — the target width is RECORDED, and this body's sites are `isize`.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m9_the_target_width_is_recorded_rather_than_assumed() {
    assert!(
        FIXTURE.contains("isize") && !FIXTURE.contains("usize"),
        "this body's target-dependent tokens are `isize` and there are NO `usize` ones — the \
         exact reverse of `ir_its`, and the reason its gate's usize arms are not copied here"
    );
    assert!(
        ir_mint::IR_IT_PROVENANCE.contains("\"usize_bits\": 64"),
        "reader A must RECORD the width it was given"
    );
    assert!(
        ir_mint::IR_IT_PROVENANCE.contains("\"isize_sites_resolved\": 4")
            && ir_mint::IR_IT_PROVENANCE.contains("\"usize_sites_resolved\": 0"),
        "and how many sites it resolved with it — four isize, zero usize. A recorded count is \
         what makes a silently-changed width visible; the resolved core text cannot show it, \
         because both a pinned isize and a native i64 spell (int 64)."
    );
    assert!(
        ir_mint::IR_IT_TAGS.contains("\"isize_sites\": 4"),
        "and the tag table's lane must pin the SITE COUNT independently of reader A"
    );
    assert!(
        ir_mint::IR_IT_TAGS.contains("erasure_note"),
        "and it must say out loud what the resolution erases"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M10 — what the SELF-FUNC pin does here, MEASURED rather than assumed.
// ────────────────────────────────────────────────────────────────────────────

/// **This arm was WRONG when first written, and the corrected form is the
/// useful one.** It asserted that reading this body without its own func id
/// must DISAGREE with reading it with one, reasoning that interning the self id
/// first shifts every callee index. The gate failed, and the implementation
/// says plainly why (`Reader::with_self_at`):
///
/// ```text
/// // With no namespace and a pinned self this is `1`, and with no pin it is
/// // `1` as well — index 0 stays reserved and empty.
/// ```
///
/// A callee interns at 1 in BOTH modes. The pin only changes what a body reads
/// when it calls ITSELF, and this one does not — it calls `tick_heartbeat` and
/// `infer_type_fast`, and the tag table's SELF row says so in as many words
/// ("NOT called recursively in this body"). That row earns its place for
/// NAMESPACE reasons instead: it is what keeps `call 1` from resolving to this
/// body, the 2026-08-20 defect.
///
/// So the honest pin is the EQUALITY, and it is not vacuous. It holds only
/// because this body has no self-call; the day `infer_type` reads as calling
/// itself — a recursive lowering, or a callee renumbering that collides with
/// index 0 — the two readings diverge and this fires.
#[test]
fn m10_the_self_pin_is_inert_here_because_the_body_has_no_self_call() {
    let unpinned = ir_mint::read_emitted_with_pins(FIXTURE, SelfFunc::Unpinned, Some(64))
        .expect("reader B must read this body without a self pin too")
        .0;
    assert_eq!(
        canon(&unpinned),
        canon(&core_b()),
        "reading this body WITH and WITHOUT its own func id must agree, because it never \
         calls itself and a callee interns at 1 either way. A divergence here means the body \
         acquired a self-call, or callee interning changed — either of which makes the tag \
         table's SELF row load-bearing in a way it currently is not."
    );
    assert!(
        !FIXTURE.contains("call @func.0("),
        "and the premise of that equality, checked rather than assumed: this body calls \
         @func.19 and @func.2, never @func.0 — itself"
    );
}

#[test]
fn m10_the_self_func_id_matches_the_tag_table() {
    let table = ir_mint::IR_IT_TAGS;
    assert!(
        table.contains("\"role\": \"SELF"),
        "the funcs lane must mark exactly which row is this body itself"
    );
    assert!(
        table.contains(&format!("\"crate_id\": {SELF_FUNC_ID}")),
        "and the literal pinned in this file ({SELF_FUNC_ID}) must be the id the table records \
         — otherwise reader B is being handed a number nothing checks"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M11 — the SIDECAR LANE's interface differences are pinned.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m11_the_sidecar_lane_interface_is_pinned() {
    assert!(
        FIXTURE.starts_with("fn @"),
        "this body's header carries NO calling-convention keyword, where every crate-module \
         chain prints `rustcc`. A body that drifted back to the crate lane would start \
         `rustcc fn @` and must be refused here"
    );
    assert!(
        FIXTURE.contains("; #producer: trust-ir"),
        "and its producer stamp is `trust-ir`, not `trust` — the sidecar bundle's own"
    );
    assert!(
        ir_mint::IR_IT_TAGS.contains("\"calling_conv\": \"ccc\"")
            && ir_mint::IR_IT_TAGS.contains("\"producer\": \"trust-ir\""),
        "and the committed table must pin both, so the difference is a claim rather than an \
         accident nobody wrote down"
    );
    assert!(
        ir_mint::IR_IT_PROVENANCE.contains("dump-infertype-O3-part"),
        "reader A must record that the dump is the infer_type callee bundle and not the crate \
         module"
    );
    assert!(
        ir_mint::IR_IT_PROVENANCE.contains("\"artifact_func_index\": 0"),
        "and that this is index 0 of it — the target, not one of its callees"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M8 — the mint DISCRIMINATES: one-token counterfactuals are different cores.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m8_the_mint_discriminates_one_token_counterfactuals() {
    // (a) The switch's two arms exchanged. Same blocks, same instructions, a
    // different function: the Ok lane would run the error path.
    let swapped = FIXTURE.replace("switch %4 [ 0: bb5 1: bb4", "switch %4 [ 0: bb4 1: bb5");
    let s = ir_mint::read_emitted_with_pins(&swapped, SelfFunc::Pinned(SELF_FUNC_ID), Some(64))
        .expect("the arm-swapped twin must still read")
        .0;
    assert_ne!(
        canon(&s),
        canon(&core_b()),
        "exchanging the switch's arms must produce a DIFFERENT core module — otherwise nothing \
         proved over this module distinguishes the fast path from the error path"
    );

    // (b) One call dropped to the other callee. `tick_heartbeat` and
    // `infer_type_fast` are the two halves of why this body's closure is hard;
    // confusing them must not be invisible.
    let recalled = FIXTURE.replace("call @func.19(%0)", "call @func.2(%0)");
    let r = ir_mint::read_emitted_with_pins(&recalled, SelfFunc::Pinned(SELF_FUNC_ID), Some(64))
        .expect("the re-called twin must still read")
        .0;
    assert_ne!(
        canon(&r),
        canon(&core_b()),
        "calling a different callee must produce a DIFFERENT core module"
    );
}

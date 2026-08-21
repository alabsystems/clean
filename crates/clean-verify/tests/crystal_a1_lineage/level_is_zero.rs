// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Measured-open A1 lineage for the designated `Level::is_zero` target.
//!
//! Link 2a (proved module = emitted module) is still open here. These tests pin
//! both the emitted body and the exact closure wall. When the wall moves they
//! deliberately fail, requiring a real transcription and equality gate.
//!
//! ## 2026-08-20 — the wall is UNCHANGED, and now it is itemized
//!
//! Crystal A2 (`src/ir_mint`) mints `has_cubical_layer`'s module from the
//! emitted artifact. It deliberately does **not** touch `ir_lz_module`, so the
//! `assert_ne!` below stands exactly as written and is not inverted.
//!
//! Two things the same machinery measured about this body, though, because they
//! correct the record rather than move the gate:
//!
//! * The emitted `is_zero` body projects to a COMPLETE core module
//!   (`src/spec/core_spec/generated/ir_lz.core.txt`: ten blocks, two `gep`s,
//!   four calls to two callees, a short-circuit through a second join block).
//!   Transcribability was never the blocker.
//! * Minting it refuses today for exactly one nameable reason — numeral 64 is
//!   outside the registered `ir_d0..ir_d16` atom pool — pinned by
//!   `crystal_a2_mint`'s `level_is_zero_mints_only_up_to_a_named_refusal`.
//!
//! ## 2026-08-20, second entry — the stated wall was HALF A WALL
//!
//! What this file said, verbatim, until today:
//!
//! > What actually costs something is downstream: a minted `ir_lz_module`
//! > contains `call` to a callee that is not in the module, `ir_call_exec` is
//! > fail-closed on that, and `ir_lz_correct` would become unprovable about the
//! > minted term. Closing 2a here means RETIRING that theorem, not repairing
//! > it. That is a decision, not a build item, and it is not taken here.
//!
//! **The middle clause was false, and it is the clause that carries the safety.**
//! `ir_call_exec` resolves through `ir_func_find`, and `ir_func_find` matches on
//! the candidate function's OWN id — the recursor arm is
//! `(fun (i : Nat) … (ir_nat_eqb i k))` where `i` is `IRFunc`'s first field
//! (`src/spec/core_spec/eval_ir_state.rs`). The minter hard-coded the projected
//! function's own id to `0` while interning CALLEE ids by first use, also from
//! `0`, in a **separate** namespace, and the two collided on that numeral: the
//! core read `(func 0 …)` for `Level::is_zero` with `(call 0 …)` for
//! `LevelArc::deref` — a different function — and `(call 1 …)` for the genuine
//! self-call.
//!
//! So a minted `ir_lz_module` would **not** have gone stuck on the deref.
//! `ir_func_find` would have found `is_zero`, and the machine would have
//! silently executed a recursive call to `is_zero` where the program calls
//! `deref` — a type-confused program the semantics accepts. Only the real
//! self-call went stuck. The wall stood in front of the harmless half and left
//! the harmful half open.
//!
//! **The collision itself is closed** (same day, sibling lane): both writers of
//! the core form now draw the function's own id and its callee ids from one
//! namespace, and `generated/ir_lz.core.txt` reads `(call 1 …)` for the deref
//! and `(call 0 …)` for the recursive call. What remains here is the
//! consequence, which the collision was hiding, and
//! `level_is_zero_callee_identity.rs` holds both worlds to account mechanically
//! rather than in prose.
//!
//! ## With callee identity fixed, is a minted `ir_lz_module` safe — and does
//! `ir_lz_correct` survive?
//!
//! **Safe: yes. Survives: no — and it is REFUTED, not merely unprovable.**
//!
//! *Safe.* With the function's own id and the callee ids drawn from one
//! namespace, `call deref` names an id no `IRFunc` in the module carries,
//! `ir_func_find` returns `IROption.none`, and `ir_call_exec` halts
//! `IROutcome.stuck IRFault.no_func`. That is the fail-closed behaviour the old
//! comment claimed, and with the collision gone it is true. No misroute remains.
//!
//! *But the theorem does not survive.* `ir_lz_correct` asserts, for **every**
//! `l` with `EncodesLiveLevelRef mem r l` and enough fuel, that `ir_eval`
//! returns `ret (bool (level_is_zero l))`. The emitted body reaches a `deref`
//! call on exactly two arms — `Max` (case 2 -> bb4) and `IMax` (the default edge,
//! bb5) — while `Zero` (bb1), `Succ` (bb2) and `Param` (bb3) return a constant
//! with no call at all. `emitted_recursive_arms_are_the_ones_that_call_out`
//! (same sibling file) pins that split. Over a minted module that defines only `is_zero`, the machine
//! therefore halts *stuck* on every `Max` and every `IMax`, where the theorem
//! says it returns. The statement is false there, so retiring is not a stylistic
//! choice between two provable framings: the theorem as written cannot be
//! restated over the minted module without dropping two of its five arms.
//!
//! **So the decision still needs taking — but it is a different decision, and it
//! has a build item under it after all.** The blocker is not "a call has no
//! callee"; it is that the reachable closure is not BODYFUL, which is exactly
//! the `a0_criteria.bodyful_reachable_closure == FAIL` this file already
//! asserts. Minting the deref in is not enough either: its own entry block calls
//! two further functions (`level_is_zero_deref_callee.trust-ir.txt`, straight
//! line, not a panic branch) that the artifact carries as declarations only. The
//! honest statement is that `ir_lz_correct` survives a minted `ir_lz_module`
//! only when the transitive callee closure is lowered with bodies — a named,
//! measurable producer build item — and that retiring the theorem is the
//! alternative to doing that work, not a substitute for understanding it.
//!
//! None of this moves the `assert_ne!` wall below, and none of it is taken here.

use std::path::PathBuf;

use super::*;

/// Record the emitted body verbatim so it cannot silently rot.
#[test]
fn emitted_body_is_recorded_verbatim() {
    let text = fixture("level_is_zero.trust-ir.txt");
    assert!(
        text.starts_with("rustcc fn @level::Level::is_zero("),
        "the fixture must be the is_zero body itself"
    );
    let emitted = parse_emitted(&text);

    assert_eq!(
        emitted.blocks,
        (0..10).collect::<Vec<u32>>(),
        "10 blocks, bb0..bb9"
    );
    assert_eq!(
        emitted.cases,
        BTreeMap::from([(0, 1), (1, 2), (2, 4), (4, 3)]),
        "four EXPLICIT switch cases: Zero->bb1, Succ->bb2, Max->bb4, Param->bb3"
    );
    assert_eq!(
        emitted.default, 5,
        "the default edge carries the reachable IMax arm"
    );
    assert_eq!(
        emitted.param_blocks,
        BTreeSet::from([6, 9]),
        "two join blocks take bool block parameters"
    );
    assert!(
        text.contains("gep inbounds i8, ptr %0, %8")
            && text.contains("gep inbounds i8, ptr %0, %10"),
        "payload reads are geps at byte offsets 8 and 16"
    );
    assert!(!text.contains("unreachable"));
}

/// Pin the exact reason link 2a remains open and the live CFG divergence.
#[test]
fn is_not_transcribed_and_the_wall_stands() {
    let evidence: serde_json::Value = serde_json::from_str(&fixture("level_is_zero.a0.json"))
        .expect("the A0 evidence must be valid JSON");
    assert_eq!(evidence["def_path"].as_str(), Some("level::Level::is_zero"));
    assert_eq!(evidence["lowered"].as_bool(), Some(true));
    assert_eq!(evidence["spliced"].as_bool(), Some(true));
    assert_eq!(
        evidence["unsupported"].as_array().map(Vec::is_empty),
        Some(true)
    );
    assert_eq!(evidence["derived_mir"]["verdict"].as_str(), Some("agreed"));
    assert_eq!(
        evidence["a0_criteria"]["bodyful_reachable_closure"].as_str(),
        Some("FAIL")
    );
    assert_eq!(
        evidence["a0_criteria"]["flip_event_observed"].as_str(),
        Some("FAIL")
    );
    assert_eq!(evidence["flip_event"]["fired"].as_bool(), Some(false));

    let body = fixture("level_is_zero.trust-ir.txt");
    let callee = fixture("level_is_zero_deref_callee.trust-ir.txt");

    // The deref call site, identified STRUCTURALLY rather than by its index.
    //
    // This assertion used to read `body.contains("call @func.4914")`, with a
    // comment saying "func 4914 is that deref". `@func.N` is a whole-crate
    // function-table index: it moves whenever clean-kernel gains or loses an
    // item, and whenever the producer changes how many bodies it lowers, with
    // not one instruction changed. Measured 2026-08-19: a producer-only A/B on
    // a byte-identical clean tree moved `@func.N` on this very body. So the
    // literal was a gate that fires on renumbering — the kind that gets
    // switched off, taking the real check with it.
    //
    // The claim worth keeping has no index in it: is_zero calls a one-argument
    // function whose RESULT is immediately consumed by the other callee, and
    // that first function is `<LevelArc as Deref>::deref`. That is read off the
    // dataflow, so it survives renumbering and still fails if the call
    // structure moves.
    let sites = call_sites(&body);
    assert_eq!(
        sites.len(),
        6,
        "six resolved call sites, matching `calls.resolved` in the A0 evidence"
    );
    let callees: BTreeSet<u32> = sites.iter().map(|s| s.callee).collect();
    assert_eq!(callees.len(), 2, "two distinct callees, three sites each");

    let consumed: BTreeSet<u32> = sites.iter().flat_map(|s| s.args.iter().copied()).collect();
    let deref_ids: BTreeSet<u32> = sites
        .iter()
        .filter(|s| consumed.contains(&s.result))
        .map(|s| s.callee)
        .collect();
    assert_eq!(
        deref_ids.len(),
        1,
        "exactly one callee's result feeds the other call — that one is the deref"
    );
    let deref_id = *deref_ids
        .iter()
        .next()
        .expect("invariant: the set was just asserted to hold one element");
    assert_eq!(
        sites.iter().filter(|s| s.callee == deref_id).count(),
        3,
        "the deref is called once per payload read"
    );
    assert!(
        callee.starts_with("rustcc fn @<level::LevelArc as std::ops::Deref>::deref("),
        "the pinned callee fixture must be that deref (observed at @func.{deref_id} when the \
         body fixture was taken; the index is recorded, never asserted)"
    );

    // The deref's own callees: two distinct functions, both declaration-only.
    // Their indices are not asserted either, and could not be checked from a
    // fixture in any case — that they are bodyless is what
    // `a0_criteria.bodyful_reachable_closure == FAIL`, asserted above, records.
    let deref_sites = call_sites(&callee);
    assert_eq!(deref_sites.len(), 2, "the deref makes exactly two calls");
    assert_eq!(
        deref_sites
            .iter()
            .map(|s| s.callee)
            .collect::<BTreeSet<u32>>()
            .len(),
        2,
        "to two distinct functions, which keep the reachable closure non-bodyful"
    );

    let clean = parse_clean(
        &std::fs::read_to_string(
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("src/spec/core_spec/eval_ir_crystal.rs"),
        )
        .expect("eval_ir_crystal.rs must be readable"),
        "def ir_lz_b",
    );
    assert_eq!(clean.blocks, (0..7).collect::<Vec<u32>>());
    assert_eq!(
        clean.cases,
        BTreeMap::from([(0, 1), (1, 2), (2, 3), (3, 5), (4, 2)])
    );
    assert_eq!(clean.default, 6);
    assert!(clean.param_blocks.is_empty());

    let emitted = parse_emitted(&body);
    assert_ne!(
        emitted, clean,
        "the wall moved: transcribe the body and replace this with equality"
    );
    assert_ne!(
        emitted.default, clean.default,
        "emitted default bb{} is reachable IMax; Clean default bb{} is a trap",
        emitted.default, clean.default
    );
}

/// One `%r = call @func.N(%a, %b)` site, with every index kept as a NUMBER
/// rather than as text, so nothing downstream can accidentally pin one.
struct CallSite {
    result: u32,
    callee: u32,
    args: Vec<u32>,
}

/// Parse the call sites out of an emitted body.
///
/// Deliberately tolerant of everything a whole-crate renumbering can change and
/// intolerant of everything it cannot: the register numbers, the callee index
/// and the argument list are read as data, and a line that looks like a call
/// but does not parse is a hard failure rather than a skip — a silently dropped
/// call site would weaken every count asserted against it.
fn call_sites(body: &str) -> Vec<CallSite> {
    let mut out = Vec::new();
    for raw in body.lines() {
        let line = raw.split("; #").next().unwrap_or(raw).trim();
        let Some((lhs, rhs)) = line.split_once(" = call @func.") else {
            // A call shape this parser does not read — a void call, say — must
            // stop the test, not be skipped: every assertion above is a COUNT,
            // and a silently dropped call site makes each of them agree with a
            // body that has more calls than it thinks.
            assert!(
                !line.contains("call @func."),
                "call-shaped line this parser does not read: `{line}`. Counting call sites is \
                 the whole mechanism here, so an unread one fails closed rather than lowering \
                 every count by one."
            );
            continue;
        };
        let result = lhs
            .trim()
            .strip_prefix('%')
            .and_then(|s| s.parse::<u32>().ok())
            .unwrap_or_else(|| panic!("call result is not a register: `{line}`"));
        let (id, rest) = rhs
            .split_once('(')
            .unwrap_or_else(|| panic!("call has no argument list: `{line}`"));
        let callee = id
            .parse::<u32>()
            .unwrap_or_else(|e| panic!("callee index is not a number ({e}): `{line}`"));
        let args = rest
            .trim_end()
            .strip_suffix(')')
            .unwrap_or_else(|| panic!("call argument list is unterminated: `{line}`"))
            .split(',')
            .map(str::trim)
            .filter(|a| !a.is_empty())
            .map(|a| {
                a.strip_prefix('%')
                    .and_then(|s| s.parse::<u32>().ok())
                    .unwrap_or_else(|| panic!("call argument is not a register: `{line}`"))
            })
            .collect();
        out.push(CallSite {
            result,
            callee,
            args,
        });
    }
    out
}

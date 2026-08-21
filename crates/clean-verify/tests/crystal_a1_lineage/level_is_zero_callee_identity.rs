// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Callee identity in a minted `ir_lz_module`, and what it costs
//! `ir_lz_correct`.**
//!
//! The reasoning these tests hold to account is in `level_is_zero.rs`'s header,
//! under "the stated wall was HALF A WALL". In one line: `ir_call_exec` decides
//! "not in the module" through `ir_func_find`, which matches a candidate on the
//! candidate's OWN id — so a minter that numbers the projected function `0` and
//! also interns callee ids from `0` makes an external call resolve to the caller
//! instead of going stuck.
//!
//! The collision that caused was closed the same day by a sibling lane, so
//! `minted_ir_lz_core_never_lets_the_deref_call_resolve` now takes its post-fix
//! branch. It keeps both branches anyway: the pre-fix shape is exactly
//! documented, so a regression to it fails here with the reason attached rather
//! than silently restoring a semantics that accepts a type-confused program.

use std::path::PathBuf;

use super::*;

/// **The mechanism that made the old claim false, pinned at its source.**
///
/// "A callee that is not in the module" is decided by `ir_func_find`, which
/// matches a candidate against the candidate's OWN id. That single fact is why a
/// minter which numbers a function `0` and also interns callees from `0` can
/// make an external call resolve to the caller. If the spec ever matched on
/// something else, the reasoning in this file's header would need redoing, so it
/// is asserted rather than described.
#[test]
fn ir_func_find_matches_on_the_functions_own_id() {
    let spec = std::fs::read_to_string(
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("src/spec/core_spec/eval_ir_state.rs"),
    )
    .expect("eval_ir_state.rs must be readable");
    let at = spec
        .find("def ir_func_find ")
        .expect("the spec must define ir_func_find");
    let body = &spec[at..at + 700];
    assert!(
        body.contains("IRFunc.rec"),
        "ir_func_find must destructure the candidate IRFunc: {body}"
    );
    assert!(
        body.contains("(fun (i : Nat) (_ : IRList Nat) (_ : Nat) (_ : IRList IRBlock) => "),
        "ir_func_find must bind the candidate's FIRST field — its id: {body}"
    );
    assert!(
        body.contains("(ir_nat_eqb i k)"),
        "ir_func_find must compare that first field against the requested id. A call is \
         'not in the module' exactly when no function CARRIES that id, which is why callee \
         ids and function ids may not be two namespaces: {body}"
    );
}

/// **A minted `ir_lz_module` must never let the `deref` call RESOLVE.**
///
/// The invariant: of the two callees the emitted body has, the one identified by
/// dataflow as `LevelArc::deref` (its result feeds the other call) must be absent
/// from the module, so `ir_call_exec` goes stuck; the self-call must be present,
/// so recursion works.
///
/// Today's committed core violates it, which is the defect this file's header
/// records, so the test recognises the two shapes explicitly. That is deliberate:
/// a plain assertion of the invariant would be a red on `main` until another lane
/// lands the namespace fix, and a plain assertion of the violation would go red
/// the moment it does. Both branches assert something real, and an unrecognised
/// third shape fails closed.
#[test]
fn minted_ir_lz_core_never_lets_the_deref_call_resolve() {
    let core = std::fs::read_to_string(
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("src/spec/core_spec/generated/ir_lz.core.txt"),
    )
    .expect("the minted ir_lz core must be readable");

    let defined: BTreeSet<u32> = core
        .match_indices("(func ")
        .filter_map(|(i, _)| {
            core[i + 6..]
                .split_whitespace()
                .next()
                .and_then(|t| t.parse::<u32>().ok())
        })
        .collect();
    assert_eq!(
        defined.len(),
        1,
        "the projection mints exactly the subject function"
    );

    // `(node (results R) (call C (args A)))` — result and callee, as numbers.
    let mut calls: Vec<(u32, u32, Vec<u32>)> = Vec::new();
    for (i, _) in core.match_indices("(call ") {
        let head = &core[..i];
        let result = head
            .rfind("(results ")
            .map(|r| &head[r + 9..])
            .and_then(|t| t.split(')').next())
            .and_then(|t| t.trim().parse::<u32>().ok())
            .expect("a call node declares one result id");
        let rest = &core[i + 6..];
        let callee = rest
            .split_whitespace()
            .next()
            .and_then(|t| t.parse::<u32>().ok())
            .expect("a call names a callee id");
        let args = rest
            .find("(args ")
            .map(|a| &rest[a + 6..])
            .and_then(|t| t.split(')').next())
            .map(|t| {
                t.split_whitespace()
                    .filter_map(|x| x.parse::<u32>().ok())
                    .collect::<Vec<u32>>()
            })
            .unwrap_or_default();
        calls.push((result, callee, args));
    }
    let callees: BTreeSet<u32> = calls.iter().map(|(_, c, _)| *c).collect();
    assert_eq!(
        callees.len(),
        2,
        "two distinct callees, as in the emitted body"
    );

    // The deref is the callee whose result is consumed by the other call.
    let consumed: BTreeSet<u32> = calls
        .iter()
        .flat_map(|(_, _, a)| a.iter().copied())
        .collect();
    let deref: BTreeSet<u32> = calls
        .iter()
        .filter(|(r, _, _)| consumed.contains(r))
        .map(|(_, c, _)| *c)
        .collect();
    assert_eq!(
        deref.len(),
        1,
        "exactly one callee's result feeds the other"
    );
    let deref = *deref.iter().next().expect("invariant: one element");
    let selfcall = *callees
        .iter()
        .find(|c| **c != deref)
        .expect("the other callee is the self-call");

    if defined.contains(&deref) {
        // Pre-fix: the two id namespaces collide on 0.
        assert_eq!(
            (
                defined.iter().copied().collect::<Vec<u32>>(),
                deref,
                selfcall
            ),
            (vec![0], 0, 1),
            "the id-namespace collision is present but not in its recorded shape. Re-derive \
             this file's header before touching the test."
        );
        eprintln!(
            "RECORDED DEFECT (D1): (func 0) is Level::is_zero and (call 0) is LevelArc::deref, \
             so ir_func_find would RESOLVE the deref call to is_zero itself. Only the genuine \
             self-call, interned to 1, goes stuck. When callee identity is fixed, this branch \
             stops being taken and the invariant below is enforced instead."
        );
    } else {
        assert!(
            defined.contains(&selfcall),
            "callee identity was fixed but the SELF-call no longer resolves: recursion in the \
             minted module is stuck, which is a different defect and not an improvement"
        );
        eprintln!(
            "callee identity is fixed: deref (@{deref}) is absent -> stuck no_func; \
             self-call (@{selfcall}) resolves. `ir_lz_correct` is now REFUTED rather than \
             mis-executed — see this file's header."
        );
    }
}

/// **Which arms of the emitted body call out, and which do not.**
///
/// This is the evidence for "`ir_lz_correct` is refuted, not merely unprovable"
/// over a minted module: `Max` and `IMax` reach a call to a callee that is not
/// `is_zero`, so on those two arms the machine halts stuck where the theorem
/// says it returns `ret (bool …)`. `Zero`, `Succ` and `Param` return a constant
/// and would still satisfy it.
#[test]
fn emitted_recursive_arms_are_the_ones_that_call_out() {
    let body = fixture("level_is_zero.trust-ir.txt");
    let emitted = parse_emitted(&body);

    // Block -> does its own text contain a call?
    let mut calls_in: BTreeMap<u32, bool> = BTreeMap::new();
    let mut cur: Option<u32> = None;
    for raw in body.lines() {
        let line = raw.split("; #").next().unwrap_or(raw).trim();
        if let Some(rest) = line.strip_prefix("bb") {
            if let Ok(id) = rest
                .split(|c: char| !c.is_ascii_digit())
                .next()
                .unwrap_or("")
                .parse::<u32>()
            {
                cur = Some(id);
                calls_in.insert(id, false);
                continue;
            }
        }
        if let Some(id) = cur {
            if line.contains("call @func.") {
                calls_in.insert(id, true);
            }
        }
    }

    // Zero -> bb1, Succ -> bb2, Param -> bb3: constant arms, no call.
    for (tag, block) in [(0u32, 1u32), (1, 2), (4, 3)] {
        assert_eq!(emitted.cases.get(&tag), Some(&block));
        assert_eq!(
            calls_in.get(&block),
            Some(&false),
            "tag {tag} routes to bb{block}, which must return a constant with no call: those \
             are the arms a minted module could still satisfy"
        );
    }
    // Max -> bb4, and IMax on the default edge: both call out.
    assert_eq!(emitted.cases.get(&2), Some(&4), "Max routes to bb4");
    for block in [4u32, emitted.default] {
        assert_eq!(
            calls_in.get(&block),
            Some(&true),
            "bb{block} carries a recursive arm and MUST contain a call. It is the arm on which \
             a minted module that omits the callee goes stuck, refuting ir_lz_correct rather \
             than leaving it unproved."
        );
    }
    eprintln!(
        "arm split: Zero/Succ/Param return constants (bb1 bb2 bb3); Max (bb4) and IMax (bb{}) \
         call out. A minted ir_lz_module without the deref is REFUTED on 2 of 5 arms.",
        emitted.default
    );
}

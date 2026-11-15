// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Link 2a for the call chain: `expr::meta::ExprMeta::has_loose_bvars`
//! (caller: call / const u32 0 / icmp ugt / ret) and
//! `expr::meta::ExprMeta::loose_bvar_range` (callee: extractfield u64 /
//! const 44 / const 64 / icmp ult / assert `#proof: shift_in_range` / zext /
//! lshr / trunc / ret).** TWO fixtures, ONE registered two-function module.
//!
//! The obligation no earlier chain had is the call site's TARGET. `@func.N`
//! renumbers on any producer change — measured on `level_is_zero` and AGAIN
//! here (fixture `@func.3657` at the time -- `@func.1729` since the 2026-10-07
//! rebaseline -- tip census `func_id: 3650`, same body). So
//! the emitted index is READ AS DATA, and the identity is asserted two other
//! ways: Clean-side, the registered call's target equals the registered
//! callee `IRFunc`'s OWN id and differs from the caller's (the
//! `ir_func_find` rule, whose silent violation was the level_is_zero minter
//! collision); emitted-side, the same-era freshness record shows the
//! callee's `func_id` IS the index the caller's call names.
//!
//! ## Evidence honesty — asserted below from committed records, not prose
//!
//! CALLER: `agreed`, `markers_exact` TRUE over 4 real marker lines, flips
//! with lineage == coverage row, asserts=0, ONE resolved call, bodyful
//! closure — and **`deferred_to_seam` is TRUE** (baseline seam evidence
//! 2/4), recorded, never hidden. **The CALLEE does not flip and its
//! derived-MIR differential is REFUSED BY THE SHIM ("pending local const
//! awaiting finalizer eval") in BOTH producer eras** — its evidence is the
//! pinned emitted IR plus the reflected lemma, and link 2b for this chain
//! is WEAKER than the ten single-body chains' (spec module doc).

use super::*;

use crate::emitted_cfg::clean_named_const_source;
use crate::freshness::read_json;

/// One `%r = call @func.N(%a, ...)` site, indices as NUMBERS — the
/// `level_is_zero` reader, fail-closed: a call-shaped line this parser cannot
/// read stops the test rather than lowering every count by one.
struct CallSite {
    result: u32,
    callee: u32,
    args: Vec<u32>,
}

fn call_sites(body: &str) -> Vec<CallSite> {
    let mut out = Vec::new();
    for raw in body.lines() {
        let line = raw.split("; #").next().unwrap_or(raw).trim();
        let Some((lhs, rhs)) = line.split_once(" = call @func.") else {
            assert!(
                !line.contains("call @func."),
                "call-shaped line this parser does not read: `{line}`"
            );
            continue;
        };
        let num = |t: &str, what: &str| -> u32 {
            t.trim()
                .trim_start_matches('%')
                .parse::<u32>()
                .unwrap_or_else(|e| panic!("{what} is not a number ({e}): `{line}`"))
        };
        let result = num(lhs, "call result");
        let (id, rest) = rhs
            .split_once('(')
            .unwrap_or_else(|| panic!("call has no argument list: `{line}`"));
        let callee = num(id, "callee index");
        let args = rest
            .trim_end()
            .strip_suffix(')')
            .unwrap_or_else(|| panic!("call argument list is unterminated: `{line}`"))
            .split(',')
            .map(str::trim)
            .filter(|a| !a.is_empty())
            .map(|a| num(a, "call argument"))
            .collect();
        out.push(CallSite {
            result,
            callee,
            args,
        });
    }
    out
}

/// The numeral after `IRInst.call ir_d` / `IRFunc.mk ir_d`.
fn clean_id_after(src: &str, marker: &str) -> u32 {
    src.split_once(marker)
        .and_then(|(_, r)| r.split_whitespace().next())
        .and_then(|t| t.parse::<u32>().ok())
        .unwrap_or_else(|| panic!("no `{marker}K` numeral in: {src}"))
}

/// Expected-lane shorthand: every lane in these bodies lives in block 0.
fn b0<V>(v: Vec<V>) -> BTreeMap<u32, Vec<V>> {
    BTreeMap::from([(0, v)])
}

fn spec(name: &str) -> String {
    clean_named_const_source("eval_ir_has_loose_bvars.rs", name)
}

/// One definition of the MINTED module script, by its `def` name.
///
/// Since 2026-08-23 `ir_hlb_module` and both its functions are MINTED rather
/// than hand-transcribed (`tests/crystal_a2_mint_hlb.rs`, `src/ir_mint`): this
/// gate reads the same generated script the spec replays, so it compares the
/// emitted artifact against the registered term and not against a second hand.
/// Historically it made an incorrect transcription FAIL; it does not make a
/// correct one automatic, and the mint is what does.
fn minted(name: &str) -> String {
    clean_block_sources("generated/ir_hlb.defs.txt", &format!("def {name} "))
}

/// THE CALLER GATE: the module Clean proves about must be the module trustc
/// emitted — the call sits in `order` plus this file's structural reader,
/// because `Cfg` has no operand lane for it.
#[test]
fn has_loose_bvars_caller_matches_the_emitted_artifact() {
    let text = fixture("has_loose_bvars.trust-ir.txt");
    assert!(
        text.starts_with("rustcc fn @expr::meta::ExprMeta::has_loose_bvars("),
        "the fixture must be has_loose_bvars itself"
    );
    let emitted = parse_emitted(&text);
    let clean = parse_clean(&minted("ir_hlb_b0"), "def ir_hlb_b0");

    assert_eq!(emitted.blocks, vec![0u32], "one block, bb0");
    let cls = |c: &str, rs: Vec<u32>| (c.to_string(), rs);
    assert_eq!(
        emitted.order,
        b0(vec![
            cls("call", vec![1]),
            cls("const", vec![2]),
            cls("icmp", vec![3]),
            cls("ret", vec![]),
        ]),
        "four instructions, the call FIRST, in this order and no other"
    );
    assert_eq!(emitted.int_consts, b0(vec![(2u32, 0u32)]));
    assert_eq!(emitted.const_tys, b0(vec![(2u32, "uint32".to_string())]));
    // ugt of the CALL'S RESULT against the constant; operand order matters.
    assert_eq!(
        emitted.icmps,
        b0(vec![("ugt".to_string(), 3u32, 1u32, 2u32)])
    );
    assert_eq!(
        emitted.icmp_tys,
        b0(vec![("ugt".to_string(), 3u32, "uint32".to_string())])
    );
    // The body returns the comparison, not the call result.
    assert_eq!(emitted.rets, b0(vec![3u32]));
    // The caller reads no field, casts nothing, computes only the icmp.
    let stray = emitted.extracts.len()
        + emitted.casts.len()
        + emitted.binops.len()
        + emitted.asserts.len()
        + emitted.loads.len()
        + emitted.condbrs.len()
        + emitted.cases.len();
    assert_eq!(
        stray, 0,
        "a lane this body should not populate is non-empty"
    );
    // The call, structurally: one site, consuming exactly the receiver,
    // binding the id the icmp reads; the INDEX is data (module doc).
    let sites = call_sites(&text);
    assert_eq!(sites.len(), 1, "exactly one call site");
    assert_eq!(sites[0].result, 1);
    assert_eq!(sites[0].args, vec![0], "it passes the receiver %0 only");
    assert!(
        text.contains("bb0(%0: struct.765):"),
        "one by-value parameter of type struct.765 — ExprMeta"
    );
    assert_entry_params(&text, &minted("ir_hlb_func"), "has_loose_bvars (caller)");
    assert_lanes(&emitted, &clean, "has_loose_bvars (caller)");
}

/// THE CALLEE GATE: full instruction lanes — the `lshr` in
/// `binops`/`binop_tys`, both casts, and the assert lane.
#[test]
fn loose_bvar_range_callee_matches_the_emitted_artifact() {
    let text = fixture("loose_bvar_range_callee.trust-ir.txt");
    assert!(
        text.starts_with("rustcc fn @expr::meta::ExprMeta::loose_bvar_range("),
        "the pinned callee fixture must be loose_bvar_range itself"
    );
    let emitted = parse_emitted(&text);
    let clean = parse_clean(&minted("ir_lbr_b0"), "def ir_lbr_b0");
    let s = str::to_string;

    assert_eq!(emitted.blocks, vec![0u32], "one block, bb0");
    // One field read: the packed u64 at field 0.
    assert_eq!(emitted.extracts, b0(vec![(1u32, 0u32, 0u32)]));
    assert_eq!(emitted.extract_tys, b0(vec![(1u32, s("uint64"))]));
    // TWO constants in one block: the shift amount and the width bound.
    assert_eq!(emitted.int_consts, b0(vec![(2u32, 44u32), (3u32, 64u32)]));
    assert_eq!(emitted.icmps, b0(vec![(s("ult"), 4u32, 2u32, 3u32)]));
    // The shift_in_range panic arm asserts the icmp's result.
    assert_eq!(emitted.asserts, b0(vec![4u32]));
    // zext of the AMOUNT, trunc of the SHIFTED value — opposite operations.
    assert_eq!(
        emitted.casts,
        b0(vec![(s("zext"), 5, 2), (s("trunc"), 7, 6)])
    );
    assert_eq!(
        emitted.cast_tys,
        b0(vec![
            (s("zext"), 5, s("uint32"), s("uint64")),
            (s("trunc"), 7, s("uint64"), s("uint32")),
        ])
    );
    // The lshr: field value shifted by the zext'd amount, at u64 — the
    // width whose range check the assert guards.
    assert_eq!(emitted.binops, b0(vec![(s("lshr"), 6u32, 1u32, 5u32)]));
    assert_eq!(emitted.binop_tys, b0(vec![(s("lshr"), 6u32, s("uint64"))]));
    assert_eq!(emitted.rets, b0(vec![7u32]));
    // The callee makes no calls — its reachable closure is itself.
    assert!(!text.contains("call @func."));
    assert_entry_params(&text, &minted("ir_lbr_func"), "loose_bvar_range (callee)");
    assert_lanes(&emitted, &clean, "loose_bvar_range (callee)");
}

/// THE CROSS-FIXTURE CHECK: the registered call targets the registered
/// callee's OWN id, from one namespace — the invariant whose silent violation
/// was the level_is_zero minter collision.
#[test]
fn has_loose_bvars_call_targets_the_callee_fixture_function() {
    let caller = fixture("has_loose_bvars.trust-ir.txt");
    let callee = fixture("loose_bvar_range_callee.trust-ir.txt");
    // Emitted side: asserted by def-path, never by `@func.N`.
    assert_eq!(call_sites(&caller).len(), 1);
    assert_eq!(call_sites(&callee).len(), 0);
    assert!(callee.starts_with("rustcc fn @expr::meta::ExprMeta::loose_bvar_range("));
    // Clean side: `ir_func_find` matches on the candidate's OWN id — anything
    // but the callee's id goes stuck or silently runs a different function,
    // and the caller's own id is exactly the level_is_zero minter collision.
    let target = clean_id_after(&minted("ir_hlb_b0"), "IRInst.call ir_d");
    let lbr = clean_id_after(&minted("ir_lbr_func"), "IRFunc.mk ir_d");
    let hlb = clean_id_after(&minted("ir_hlb_func"), "IRFunc.mk ir_d");
    assert_eq!(target, lbr, "the call must target the callee's own id");
    assert_ne!(target, hlb, "…and must not name the caller's own id");
    // Both functions in the module; the headless counterfactual has no callee.
    let module = minted("ir_hlb_module");
    assert!(module.contains("ir_hlb_func") && module.contains("ir_lbr_func"));
    assert!(!spec("SRC_IR_HLB_HEADLESS").contains("ir_lbr_func"));
}

/// Artifact-side drifts: each lane is load-bearing by measurement, in both
/// bodies — plus the two facts only the structural reader can see (the
/// call's argument and its callee index).
#[test]
fn has_loose_bvars_the_lanes_catch_a_drifted_artifact() {
    let caller = parse_emitted(&fixture("has_loose_bvars.trust-ir.txt"));
    let head = "rustcc fn @x(functy.410) {\nbb0(%0: struct.765):\n";
    let body = |mid: &str| {
        parse_emitted(&format!(
            "{head}    %1 = call @func.1729(%0)\n{mid}    ret %3\n}}\n"
        ))
    };
    // ugt -> uge; the icmp at u64; comparing the RECEIVER instead of the
    // call result; the call DELETED (the order lane must see that one).
    let as_uge = body("    %2 = const u32 0\n    %3 = icmp uge u32 %1, %2\n");
    assert_eq!(caller.order, as_uge.order);
    assert_ne!(caller.icmps, as_uge.icmps);
    let at_u64 = body("    %2 = const u32 0\n    %3 = icmp ugt u64 %1, %2\n");
    assert_eq!(caller.icmps, at_u64.icmps);
    assert_ne!(caller.icmp_tys, at_u64.icmp_tys);
    let wrong_op = body("    %2 = const u32 0\n    %3 = icmp ugt u32 %0, %2\n");
    assert_ne!(caller.icmps, wrong_op.icmps);
    let no_call = parse_emitted(&format!(
        "{head}    %2 = const u32 0\n    %3 = icmp ugt u32 %1, %2\n    ret %3\n}}\n"
    ));
    assert_ne!(caller.order, no_call.order);
    // A DIFFERENT ARGUMENT and a RENUMBERED callee index: both invisible to
    // every Cfg lane (the equalities ARE the measurement), both visible to
    // the structural reader.
    let base = fixture("has_loose_bvars.trust-ir.txt");
    let wrong_arg = format!(
        "{head}    %1 = call @func.1729(%1)\n    %2 = const u32 0\n    %3 = icmp ugt u32 %1, %2\n    ret %3\n}}\n"
    );
    let renumbered = format!(
        "{head}    %1 = call @func.9999(%0)\n    %2 = const u32 0\n    %3 = icmp ugt u32 %1, %2\n    ret %3\n}}\n"
    );
    assert_eq!(caller, parse_emitted(&wrong_arg));
    assert_eq!(caller, parse_emitted(&renumbered));
    assert_ne!(call_sites(&base)[0].args, call_sites(&wrong_arg)[0].args);
    assert_ne!(
        call_sites(&base)[0].callee,
        call_sites(&renumbered)[0].callee
    );

    let callee = parse_emitted(&fixture("loose_bvar_range_callee.trust-ir.txt"));
    let cb = |l6: &str, l10: &str| {
        parse_emitted(&format!(
            "{head}    %1 = extractfield u64 %0, 0\n    %2 = const u32 44\n    %3 = const u32 64\n    \
             %4 = icmp ult u32 %2, %3\n{l6}    %5 = zext u32 %2 to u64\n{l10}    \
             %7 = trunc u64 %6 to u32\n    ret %7\n}}\n"
        ))
    };
    // lshr -> ashr (only the binop lane); lshr at u32 (only its type lane).
    let as_ashr = cb("    assert %4\n", "    %6 = ashr u64 %1, %5\n");
    assert_eq!(callee.order, as_ashr.order, "order sees only the class");
    assert_ne!(callee.binops, as_ashr.binops);
    let at_u32 = cb("    assert %4\n", "    %6 = lshr u32 %1, %5\n");
    assert_eq!(callee.binops, at_u32.binops);
    assert_ne!(callee.binop_tys, at_u32.binop_tys);
    // The assert DELETED; the assert on a different scrutinee; the shift by
    // the RAW FIELD instead of the zext'd amount.
    let no_assert = cb("", "    %6 = lshr u64 %1, %5\n");
    assert_ne!(callee.asserts, no_assert.asserts);
    assert_ne!(callee.order, no_assert.order);
    let wrong_assert = cb("    assert %1\n", "    %6 = lshr u64 %1, %5\n");
    assert_eq!(callee.order, wrong_assert.order);
    assert_ne!(callee.asserts, wrong_assert.asserts);
    let wrong_shift = cb("    assert %4\n", "    %6 = lshr u64 %1, %1\n");
    assert_ne!(callee.binops, wrong_shift.binops);
}

/// The other direction: perturb the registered spec sources and parse them
/// with the same reader the gates use.
#[test]
fn has_loose_bvars_the_lanes_catch_a_drifted_spec_module_too() {
    let caller = parse_emitted(&fixture("has_loose_bvars.trust-ir.txt"));
    let b0 = minted("ir_hlb_b0");
    let mutate = |src: &str, from: &str, to: &str, marker: &str| {
        let mutated = src.replace(from, to);
        assert_ne!(mutated, src, "the mutation `{from}` must apply");
        parse_clean(&mutated, marker)
    };
    let good = parse_clean(&b0, "def ir_hlb_b0");
    assert_eq!(caller.icmps, good.icmps, "the unmutated module must agree");
    // ult for ugt; then returning the call result raw.
    let as_ult = mutate(&b0, "IRICmpOp.ugt", "IRICmpOp.ult", "def ir_hlb_b0");
    assert_ne!(caller.icmps, as_ult.icmps);
    let wrong_ret = mutate(&b0, "(ir_nl1 ir_d3)", "(ir_nl1 ir_d1)", "def ir_hlb_b0");
    assert_ne!(caller.rets, wrong_ret.rets);
    // The CALL TARGET moved to the caller's own id — the collision. Every Cfg
    // lane is blind to it (measured by this equality); the cross-fixture
    // check is what fails, via the id reader.
    let collided = b0.replace("IRInst.call ir_d1", "IRInst.call ir_d0");
    assert_eq!(caller, parse_clean(&collided, "def ir_hlb_b0"));
    assert_ne!(
        clean_id_after(&collided, "IRInst.call ir_d"),
        clean_id_after(&b0, "IRInst.call ir_d")
    );

    let callee = parse_emitted(&fixture("loose_bvar_range_callee.trust-ir.txt"));
    let lb0 = minted("ir_lbr_b0");
    let lgood = parse_clean(&lb0, "def ir_lbr_b0");
    assert_eq!(callee.binops, lgood.binops);
    assert_eq!(callee.asserts, lgood.asserts);
    // Shift amount 46; ashr for lshr; the assert deleted; the trunc reading
    // the raw field instead of the shifted value.
    let at_46 = mutate(&lb0, "IRConst.int_ 44", "IRConst.int_ 46", "def ir_lbr_b0");
    assert_ne!(callee.int_consts, at_46.int_consts);
    let as_ashr = mutate(&lb0, "IRBinOp.lshr", "IRBinOp.ashr", "def ir_lbr_b0");
    assert_ne!(callee.binops, as_ashr.binops);
    let no_assert = mutate(&lb0, "(ir_nd (IRInst.assert ir_d4)) ", "", "def ir_lbr_b0");
    assert_ne!(callee.asserts, no_assert.asserts);
    let wrong_trunc = mutate(
        &lb0,
        "(IRTy.uint_ 32) ir_d6",
        "(IRTy.uint_ 32) ir_d1",
        "def ir_lbr_b0",
    );
    assert_ne!(callee.casts, wrong_trunc.casts);
}

/// **The emitted-side half of the callee identity, as a test rather than data.**
///
/// The Clean-side gate above pins the reflected call's target to `ir_lbr_func`'s
/// own id; this pins the EMITTED side: the caller fixture's `call @func.N`
/// operand must equal the callee's `func_id` in the same-era record, so the two
/// fixtures cannot silently be from different eras (func ids are whole-crate
/// numbering and renumber per build).
#[test]
fn emitted_call_target_matches_the_callee_record() {
    let caller = fixture("has_loose_bvars.trust-ir.txt");
    let target: u32 = caller
        .lines()
        .find_map(|l| l.split("call @func.").nth(1))
        .and_then(|t| t.split('(').next())
        .and_then(|t| t.trim().parse().ok())
        .expect("the caller fixture must contain exactly one `call @func.N`");
    // The live-dump report the CURRENT fixtures were cut from (the 2026-10-07
    // rebaseline's strict report; it was the lane18 report until then).
    let record = read_json("data/crystal_fixture_freshness_2026-10-07_047ebd051_strict.json");
    let callee_fid = record["bodies"]["loose_bvar_range_callee"]["at_head"]["func_id"]
        .as_u64()
        .expect("the record must carry the callee's func_id") as u32;
    assert_eq!(
        target, callee_fid,
        "the emitted call targets func.{target} but the same-era record says the callee is \
         func.{callee_fid} — the two fixtures are from different builds"
    );
}

// The tip-era census and lineage-fixture EVIDENCE gates, at recorded
// strength — split out (rust_excellence 500-line rule) following the ninth
// and tenth chains' pattern.
#[path = "has_loose_bvars_evidence.rs"]
mod evidence;

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A1 lineage for the designated `Level::is_zero` target — the rows that state
//! what the chain's theorems are ABOUT.
//!
//! ## 2026-08-22 — the decision (lane LZW)
//!
//! The mint derived the emitted body mechanically and diffed it against the
//! registered module; they differed in four classes, printed verbatim by the
//! gate (`tests/crystal_a2_mint_lz.rs`). The registered module was therefore
//! the hand SEMANTIC MODEL of `Level::is_zero` with the deref inlined, and
//! `ir_lz_correct` / `ir_lz_machine_sound` were theorems about a module the
//! compiler does not emit. Decision memo:
//! `designs/2026-08-22-is-zero-model-vs-minted-decision.md`. What landed:
//!
//! * the hand model is `ir_lzm_module` (`eval_ir_crystal.rs`), and the A4/A5
//!   theorems are `ir_lzm_correct` / `ir_lzm_machine_sound` — about the MODEL;
//! * the MINTED module is registered as `ir_lz_module`
//!   (`eval_ir_level_minted.rs`, replayed from `generated/ir_lz.defs.txt`),
//!   gated M1–M10 like every other chain, with reader C (M4) now covering the
//!   designated target;
//! * over the minted module the A4 sentence is REFUTED, kernel-checked
//!   (`ir_lz_minted_refutes_a4_on_max`): the `Max` and `IMax` arms call
//!   `<LevelArc as Deref>::deref`, which the module does not define, and go
//!   `stuck no_func` where A4 says they return. Link 4 is OPEN.
//!
//! The rows below pin all of that from the sources, so the next lane finds it
//! by a failing test rather than by memory: the emitted body (verbatim), the
//! four divergence classes (class by class, both sides parsed), which module
//! each theorem names, and the one measurement behind "Option A does not buy
//! the theorem" — the deref callee itself does not read, let alone mint.
//!
//! ## 2026-08-20 — the stated wall was HALF A WALL (kept: it is the reason the
//! callee-identity lane exists)
//!
//! `ir_call_exec` resolves through `ir_func_find`, which matches on the
//! candidate's OWN id. The minter used to number the projected function `0`
//! while interning callees from `0` in a separate namespace, so `(call 0 …)`
//! for `LevelArc::deref` would have RESOLVED to `is_zero` itself — a
//! type-confused program the semantics accepted. The namespaces are one now
//! (self interned first; `generated/ir_lz.core.txt` reads `(call 1 …)` for the
//! deref and `(call 0 …)` for the recursion), the deref call goes `stuck
//! no_func`, and `level_is_zero_callee_identity.rs` holds both worlds to
//! account mechanically.

use std::path::PathBuf;

use clean_verify::ir_mint;

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
    // *** THE LAYOUT OBLIGATION, PINNED BY VALUE — NOT BY REGISTER NAME. ***
    //
    // This assertion used to read `text.contains("gep inbounds i8, ptr %0, %8")`
    // and claim "byte offsets 8 and 16". It checked neither. `%8` is an SSA
    // REGISTER NAME; what it HOLDS is decided by a separate `const i64` line, so
    // the old check passed unchanged if `repr(Rust)` moved the fields and `%8`
    // became `const i64 24`. An assertion whose message claims more than it
    // tests is worse than none: it reports the obligation as guarded.
    //
    // The offsets matter because `EncodesLevelArcF` (eval_ir_lzb.rs) places the
    // two `LevelArc` pointers at heap cells `a+8` and `a+16` to match them. That
    // correspondence is an ASSUMPTION about `repr(Rust)` field placement, which
    // is unspecified and free to reorder, and it is NOT discharged here. What
    // this does is stop it drifting SILENTLY: resolve each gep's offset register
    // through its `const i64` binding and pin the resulting values.
    let consts: BTreeMap<&str, u64> = regex_lite_const_i64(&text).into_iter().collect();
    let offsets: Vec<u64> = text
        .lines()
        .filter_map(|l| l.split_once("gep inbounds i8, ptr %0, %"))
        .map(|(_, rest)| rest.split_whitespace().next().unwrap_or(""))
        .map(|reg| {
            *consts.get(reg).unwrap_or_else(|| {
                panic!("gep offset register %{reg} has no `const i64` binding in the fixture")
            })
        })
        .collect();
    assert_eq!(
        offsets,
        vec![8u64, 16, 16],
        "the emitted body geps the receiver to these BYTE OFFSETS, and EncodesLevelArcF \
         places its field cells at a+8 / a+16 to match. If this fails, repr(Rust) moved the \
         LevelArc fields and the representation relation describes a layout the compiler no \
         longer emits"
    );
    assert!(!text.contains("unreachable"));
}

/// The A0 verdicts as the fixture records them, and the dataflow identity of
/// the deref callee — unchanged by the decision, re-pinned so the closure
/// question stays measured.
#[test]
fn a0_evidence_and_the_deref_callee_are_pinned() {
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
        Some("FAIL"),
        "the closure is not bodyful: architectural (rustc has no cross-crate THIR)"
    );
    // The 2026-08-13 top-level flip verdict is historical; the fixture's own
    // `current_source_bound_pin` (2026-08-21) records the flip FIRING. Both
    // are pinned as what they are.
    assert_eq!(
        evidence["a0_criteria"]["flip_event_observed"].as_str(),
        Some("FAIL")
    );
    assert_eq!(evidence["flip_event"]["fired"].as_bool(), Some(false));
    assert_eq!(
        evidence["current_source_bound_pin"]["flip_event"]["fired"].as_bool(),
        Some(true),
        "the source-bound pin is the current flip status; the top-level block is the 2026-08-13 \
         measurement it supersedes"
    );
    assert_eq!(
        evidence["current_source_bound_pin"]["derived_mir"]["markers_exact"].as_bool(),
        Some(true)
    );

    let body = fixture("level_is_zero.trust-ir.txt");
    let callee = fixture("level_is_zero_deref_callee.trust-ir.txt");

    // The deref call site, identified STRUCTURALLY rather than by its index
    // (`@func.N` moves under renumbering — measured 2026-08-19): is_zero calls
    // a one-argument function whose RESULT is immediately consumed by the
    // other callee, and that first function is `<LevelArc as Deref>::deref`.
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
}

/// **The four recorded divergence classes, class by class, both sides parsed
/// from source.** The model (`def ir_lzm_b…` in `eval_ir_crystal.rs`) against
/// the emitted body (the fixture). If either side moves, the class that moved
/// is named.
#[test]
fn the_model_and_the_emitted_body_differ_in_four_recorded_classes() {
    let body = fixture("level_is_zero.trust-ir.txt");
    let emitted = parse_emitted(&body);
    let model_src = std::fs::read_to_string(
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("src/spec/core_spec/eval_ir_crystal.rs"),
    )
    .expect("eval_ir_crystal.rs must be readable");
    let model = parse_clean(&model_src, "def ir_lzm_b");

    // Class 1 — THE SWITCH: arms, default, and the exhaustive flag.
    assert_eq!(
        model.cases,
        BTreeMap::from([(0, 1), (1, 2), (2, 3), (3, 5), (4, 2)]),
        "model: five arms, Succ and Param sharing b2"
    );
    assert_eq!(
        model.default, 6,
        "model: the default is the unreachable trap"
    );
    assert_eq!(
        emitted.cases,
        BTreeMap::from([(0, 1), (1, 2), (2, 4), (4, 3)]),
        "emitted: four arms, Param in its own block"
    );
    assert_eq!(emitted.default, 5, "emitted: IMax rides the default edge");
    let model_b0 = model_src
        .split("def ir_lzm_b0 ")
        .nth(1)
        .and_then(|r| r.split("def ir_lzm_b1 ").next())
        .expect("the model's b0 source");
    assert!(
        model_b0.contains("ir_sc0))))) Bool.true"),
        "model: exhaustive_enum_unreachable TRUE"
    );
    assert!(
        ir_mint::IR_LZ_CORE.contains("(case 2 4 (args))) false)"),
        "emitted (reader A): exhaustive_enum_unreachable FALSE"
    );
    assert!(
        !body.contains("unreachable") && model_src.contains("(ir_nd IRInst.unreachable)"),
        "the trap exists only in the model"
    );

    // Class 2 — per-arm RET vs BR to a join with a bool block parameter.
    assert!(model.param_blocks.is_empty(), "model: no join blocks");
    assert_eq!(emitted.param_blocks, BTreeSet::from([6, 9]));
    let model_blocks: Vec<String> = (0..7).map(|k| model_block(&model_src, k)).collect();
    let model_rets = model_blocks
        .iter()
        .filter(|b| b.contains("IRInst.ret"))
        .count();
    assert_eq!(model_rets, 4, "model: b1, b2, b4, b5 each return");
    assert_eq!(
        body.lines()
            .filter(|l| l.trim().starts_with("ret "))
            .count(),
        1,
        "emitted: exactly one ret, in the join bb6"
    );

    // Class 3 — the deref: inlined null-check + assert + ONE self-call in the
    // model; gep + call deref + call self in the emitted body.
    let recursive: Vec<&String> = model_blocks
        .iter()
        .filter(|b| b.contains("IRInst.call"))
        .collect();
    assert_eq!(recursive.len(), 3, "model: b3, b4, b5 recurse");
    for b in &recursive {
        assert!(
            b.contains("IRInst.extractfield")
                && b.contains("IRConst.null_")
                && b.contains("IRInst.icmp")
                && b.contains("IRInst.assert")
                && b.contains("IRInst.call ir_d0")
                && !b.contains("IRInst.call ir_d1")
                && !b.contains("IRInst.gep"),
            "model arm: extractfield + null + icmp + assert + self-call only:\n{b}"
        );
    }
    assert!(
        !body.contains("assert") && !body.contains("null"),
        "emitted: no assert, no null constant"
    );
    assert_eq!(
        body.lines().filter(|l| l.contains("= gep ")).count(),
        3,
        "emitted: three geps (offsets 8, 16, 16)"
    );
    assert_eq!(
        call_sites(&body)
            .iter()
            .map(|s| s.callee)
            .collect::<BTreeSet<u32>>()
            .len(),
        2,
        "emitted: two callees — the deref and itself"
    );

    // Class 4 — the block census.
    assert_eq!(model.blocks, (0..7).collect::<Vec<u32>>());
    assert_eq!(emitted.blocks, (0..10).collect::<Vec<u32>>());

    assert_ne!(emitted, model, "the wall: the two CFGs differ");
}

/// **Which module each theorem is about — source-bound.** The A4/A5 theorems
/// name the MODEL; the chain's name is carried by the MINTED module; the
/// refutation quantifies over the minted one. A rename that silently put the
/// theorems back over the chain's name fails here.
#[test]
fn the_theorems_are_about_the_model_and_the_minted_module_carries_the_chain_name() {
    let correct = spec_source("eval_ir_correct.rs");
    let a4 = correct
        .split("def ir_lzm_correct ")
        .nth(1)
        .and_then(|r| r.split(" := ").next())
        .expect("ir_lzm_correct's statement");
    assert!(
        a4.contains("ir_eval fuel ir_lzm_module ir_d0"),
        "A4 quantifies over the MODEL: {a4}"
    );
    assert!(
        !a4.contains("ir_lz_module"),
        "and not over the minted module"
    );
    assert!(
        correct.contains("def ir_lzm_machine_sound ")
            && !correct.contains("def ir_lz_correct ")
            && !correct.contains("def ir_lz_machine_sound "),
        "the old names are gone from the theorem file"
    );

    assert!(
        ir_mint::IR_LZ_DEFS.contains("def ir_lz_module : IRModule :="),
        "the minted script defines the chain-named module"
    );
    let minted_stage = spec_source("eval_ir_level_minted.rs");
    assert!(
        minted_stage.contains("include_str!(\"generated/ir_lz.defs.txt\")"),
        "and the spec registers it by replaying that script"
    );
    let refutation = minted_stage
        .split("def ir_lz_minted_refutes_a4_on_max ")
        .nth(1)
        .expect("the refutation is registered");
    assert!(
        refutation.contains("ir_eval fuel ir_lz_module ir_d0 (ir_vl1 r) mem na")
            && refutation.contains("bool_true_ne_false C"),
        "the refutation's hypothesis is A4 over the MINTED module and its conclusion is every C"
    );
    assert!(
        minted_stage.contains("\"ir_lz_on_max_stuck\"")
            && minted_stage.contains("\"ir_lz_on_imax_stuck\"")
            && minted_stage.contains("(IROutcome.stuck IRFault.no_func)"),
        "the stuck witnesses are registered (their `def` lines are assembled by `witness()`, \
         so the names are pinned as the literals that call it)"
    );
}

/// **Option A, measured.** "Rebase the theorems onto the minted module by
/// minting the deref callee too" needs the deref to read; it does not. The
/// fixture `level_is_zero_deref_callee.trust-ir.txt` is refused by reader B
/// and by the projection gate, and the refusal names the construct. Even if it
/// read, its entry block is two calls to `Option::as_deref` / `Option::expect`
/// — declaration-only in the artifact — so a two-function module would go
/// stuck one call deeper, not return.
#[test]
fn option_a_measured_the_deref_callee_does_not_read() {
    let callee = fixture("level_is_zero_deref_callee.trust-ir.txt");
    let e = ir_mint::read_emitted(&callee).map(|_| ()).expect_err(
        "the deref callee must be REFUSED by reader B, not read into an incoherent module",
    );
    let msg = format!("{e}");
    assert!(
        msg.contains("global_addr"),
        "the refusal is the `global_addr` of the expect message — a global the module would not \
         declare: {msg}"
    );
    let tags = ir_mint::tags::parse(ir_mint::IR_LZ_TAGS).expect("the lz tag table parses");
    let e = ir_mint::project(&callee, &tags)
        .map(|_| ())
        .expect_err("and by the projection gate");
    eprintln!("deref callee: reader B refuses: {msg}\n          projection refuses: {e}");
    assert!(
        callee.contains("global_addr @global.") && callee.contains("ptr_from_parts"),
        "the constructs that keep it out of the fragment are in the fixture"
    );
}

/// The Rust source of the model's block `k` — from its `def ir_lzm_b{k}`
/// literal to the next registration call — so per-block content can be
/// asserted with `IRInst.`-prefixed needles that no description string spells.
fn model_block(src: &str, k: u32) -> String {
    let start = src
        .find(&format!("\"def ir_lzm_b{k} "))
        .unwrap_or_else(|| panic!("the model has no block b{k}"));
    let rest = &src[start..];
    let end = rest.find("self.add_recursive_def(").unwrap_or(rest.len());
    rest[..end].to_string()
}

/// One `%r = call @func.N(%a, %b)` site, with every index kept as a NUMBER
/// rather than as text, so nothing downstream can accidentally pin one.
struct CallSite {
    result: u32,
    callee: u32,
    args: Vec<u32>,
}

/// Parse the call sites out of an emitted body. Tolerant of everything a
/// whole-crate renumbering can change and intolerant of everything it cannot:
/// a call-shaped line this parser does not read is a hard failure, because
/// every assertion above is a COUNT.
fn call_sites(body: &str) -> Vec<CallSite> {
    let mut out = Vec::new();
    for raw in body.lines() {
        let line = raw.split("; #").next().unwrap_or(raw).trim();
        let Some((lhs, rhs)) = line.split_once(" = call @func.") else {
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

/// Every `%N = const i64 V` binding in a trust-ir body, as `(N, V)`.
///
/// A three-line parser rather than a dependency: this crate's test targets do
/// not pull `regex`, and the fixture's format is fixed (`TrustIr text format
/// v1`). It exists so a gep's offset can be resolved to the VALUE it uses
/// instead of the register name it mentions.
fn regex_lite_const_i64(text: &str) -> Vec<(&str, u64)> {
    text.lines()
        .filter_map(|l| l.trim().strip_prefix('%'))
        .filter_map(|r| r.split_once(" = const i64 "))
        .filter_map(|(reg, rest)| {
            rest.split_whitespace()
                .next()
                .and_then(|v| v.parse::<u64>().ok())
                .map(|v| (reg, v))
        })
        .collect()
}

/// The `ir_lzb_deref` model's Arc-data offset, and the thing that keeps the
/// spec and the machine in step.
///
/// AUDIT r16 M16-6 found this as a THIRD, unrecorded clause of the clause-(a)
/// residual: four committed artifacts enumerated it as exactly two things, and
/// `designs/2026-08-26-a0-semantic-no-escape.md` states the residual as the
/// identity `Some(x).as_deref().expect(_) == &*x`, which the model did not
/// implement — it returned the loaded field word, `x`, where
/// `<Arc<T> as Deref>::deref` returns the address of the Arc's DATA, past the
/// strong/weak header. That was not a weak assumption but a false one: it made
/// `EncodesLevelArcF` unsatisfiable by any real `Level` heap at exactly the
/// `Succ`/`Max`/`IMax` nodes link 4 is about.
///
/// **The strengthening has landed.** `ir_lzb_deref` carries a `const i64 16`
/// and a `gep`, `EncodesLevelArcF` places each child at `Nat.add b ir_d16`, and
/// the two `Eq.refl` cost equations moved with it (`ir_lzb_cost_halts_max`
/// 37 → 41, `ir_lzb_cost_halts_imax` 20 → 22). So the model no longer ASSUMES
/// an offset of zero — it assumes THIS one, and this test is what says the
/// machine still agrees. If `Arc`'s header ever changed size, the spec would be
/// describing a heap the compiler does not build, and the failure would
/// otherwise be silent: every theorem over `ir_lzb_module` would still be
/// kernel-checked, and every one of them would be about the wrong memory.
#[test]
fn deref_model_arc_data_offset_is_what_the_model_assumes() {
    use clean_kernel::level::Level;
    use std::sync::Arc;
    /// What `ir_lzb_deref` computes: the stored field word plus this, spelled
    /// `IRConst.int_ ir_d16` in `SRC_DEREF_B0` and `Nat.add b ir_d16` in
    /// `EncodesLevelArcF`'s three recursive arms.
    const ARC_DATA_OFFSET_THE_MODEL_ASSUMES: usize = 16;
    /// What the machine does, measured. Ledger row A-CLZ-DEREF-ARC-DATA-OFFSET.
    const ARC_DATA_OFFSET_MEASURED: usize = 16;

    let opt: Option<Arc<Level>> = Some(Arc::new(Level::zero()));
    // SAFETY: `Option<Arc<Level>>` is niche-packed to exactly one pointer-sized
    // word -- asserted by `deref_model_layout_premise_none_is_the_null_niche`
    // below, which is the premise this test extends. The word is read as an
    // integer and never dereferenced.
    let stored: usize = unsafe { *(std::ptr::addr_of!(opt).cast::<usize>()) };
    let data = opt.as_deref().expect("Some") as *const Level as usize;
    let measured = data.wrapping_sub(stored);
    assert_eq!(
        measured, ARC_DATA_OFFSET_MEASURED,
        "the Arc data offset moved. Every theorem over `ir_lzb_module` stands on \
         the gap between the pointer stored in a `LevelArc` field and what \
         `<LevelArc as Deref>::deref` returns (the Arc's DATA pointer). The \
         recorded measurement is {}; the machine now says {}. Re-measure before \
         touching anything else.",
        ARC_DATA_OFFSET_MEASURED, measured
    );
    assert_eq!(
        measured, ARC_DATA_OFFSET_THE_MODEL_ASSUMES,
        "the model and the machine have come apart. `ir_lzb_deref` geps by {} \
         and `EncodesLevelArcF` places every child at `b + {}`, but the machine's \
         offset is {}. Nothing here would fail on its own: the spec would still \
         kernel-check, and every theorem over `ir_lzb_module` would be about a \
         heap the compiler does not build. Change the model's `IRConst.int_` and \
         the relation's three recursive arms together, and re-derive \
         `ir_lzb_cost_halts_max` / `ir_lzb_cost_halts_imax`.",
        ARC_DATA_OFFSET_THE_MODEL_ASSUMES, ARC_DATA_OFFSET_THE_MODEL_ASSUMES, measured
    );
}

/// The `ir_lzb_deref` model's LAYOUT premise, pinned as a compiled assertion.
///
/// The clause-(a) residual (owner ruling 2026-08-27, `data/crystal_a0_discharge.json`)
/// states: *"`Option<Arc<Level>>`'s `None` is the null niche, and
/// `as_deref().expect()` is load + null-check + assert."* The second half is
/// checked by `ir_lzb_deref_refuses_none` (the model traps on a null field);
/// the FIRST half was prose until this test. If `Option<Arc<Level>>` were not
/// niche-packed — a discriminant byte beside the pointer — the emitted body's
/// single 8-byte field load that the model mirrors would be reading the wrong
/// thing, and every theorem over `ir_lzb_module` would be about a layout the
/// machine does not use.
///
/// `Arc` is `NonNull`-based, so rustc packs `None` as the null pointer value
/// and the whole `Option` occupies exactly one pointer. Assert that, plus the
/// `LevelArc` wrapper being layout-transparent to it, so the receiver really is
/// one pointer-sized cell at offset 0 — the cell the minted body geps from.
#[test]
fn deref_model_layout_premise_none_is_the_null_niche() {
    use clean_kernel::level::{Level, LevelArc};
    use std::mem::size_of;
    use std::sync::Arc;
    assert_eq!(
        size_of::<Option<Arc<Level>>>(),
        size_of::<Arc<Level>>(),
        "Option<Arc<Level>> must be niche-packed: None IS the null pointer, \
         no separate discriminant -- the ir_lzb_deref model's load+null-check \
         premise depends on it"
    );
    assert_eq!(
        size_of::<Arc<Level>>(),
        size_of::<usize>(),
        "Arc<Level> is one thin pointer"
    );
    assert_eq!(
        size_of::<LevelArc>(),
        size_of::<Option<Arc<Level>>>(),
        "the LevelArc wrapper adds no bytes: the receiver is exactly the \
         niche-packed Option cell the emitted body reads"
    );
}

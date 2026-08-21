// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **THE COVERAGE DENOMINATOR FOR THE WHOLE A1 GATE: ten chains against every
//! lane, pinned.**
//!
//! Every lane in `emitted_cfg.rs` was added by whichever chain needed it, and
//! each time the author re-checked the earlier chains by hand. Two of those
//! late additions were found only because somebody asked what a gate compares:
//!
//! * a cast was in NO lane, so a cast-only body parsed to an ENTIRELY EMPTY
//!   `Cfg` on both sides and two empty CFGs compare equal;
//! * until `rets`, nothing had ever looked at what a body RETURNS;
//! * and until the tenth chain, `Inst::Assert` was in no lane — it binds no
//!   result, carries no type and has no target, so DELETING it changed nothing
//!   the gate read.
//!
//! An equality gate over a shape whose lanes are all empty passes vacuously, so
//! "all nine chains are green" means nothing without a statement of WHICH lanes
//! each chain actually exercises. That statement is this file. Each chain pins
//! the exact set of lanes that are NON-EMPTY on its body; every lane not in that
//! set is empty, and empty on BOTH sides, which is checked here rather than
//! assumed.
//!
//! A body that gains or loses a construct fails here, in the one place that
//! names the construct, instead of silently shrinking what the gate compares.
//!
//! ## What this does NOT establish
//!
//! That a non-empty lane is genuinely COMPARED. Emptiness is a denominator, not
//! a proof: a lane could be non-empty on both sides and never asserted. That is
//! proved by mutation instead — `scripts/crystal_lane_matrix_battery.sh` runs
//! one case per chain x lane cell in each direction and requires the gate to go
//! RED for every one. `7093bb0b7` records **164/164, 0 blind** — 100 artifact
//! mutations (`TABLE`) and 64 spec mutations (`SPEC_TABLE`).
//!
//! **That 164/164 predates the 2026-08-19 operand audit and does NOT cover the
//! two lanes it added.** Six more rows now exist and have NOT been run — see
//! `operand_audit.rs`, which states exactly what is measured about each.
//!
//! (Corrected 2026-08-17: this comment read "155 cases ... 100 artifact and 55
//! spec" after the count had already moved. The rows are countable —
//! `TABLE` and `SPEC_TABLE` in that script — so a stale number here is a stale
//! number about a gate, which is the one place it must not be.)

use super::*;

/// One chain: the gate's four coordinates plus the lanes its body exercises.
struct Chain {
    who: &'static str,
    fixture: &'static str,
    spec: &'static str,
    blocks_prefix: &'static str,
    block_marker: &'static str,
    func_prefix: &'static str,
    /// Exactly the lanes that are NON-EMPTY on this body. Everything else is
    /// empty — and empty on both sides, which this file checks.
    nonempty: &'static [&'static str],
}

/// `blocks` is on every row (a body has blocks) and `rets` is on every row
/// (every chained body ends in one). The interesting content is which of the
/// other twenty each chain reaches.
const CHAINS: &[Chain] = &[
    Chain {
        who: "has_cubical_layer",
        fixture: "has_cubical_layer.trust-ir.txt",
        // The FIRST chain whose registered module is MINTED rather than hand
        // written (crystal A2, `src/ir_mint`). The comparator, the lane set and
        // this row's expectations are unchanged: only the file the Clean side
        // is read from moved, from seven `const SRC_IR_H2_*` strings to the
        // generated script `eval_ir_mode.rs` now replays.
        spec: "generated/ir_h2.defs.txt",
        blocks_prefix: "def ir_h2_",
        block_marker: "def ir_h2_b",
        func_prefix: "def ir_h2_func",
        nonempty: &[
            "blocks",
            "consts",
            "cases",
            "default",
            "branches",
            "param_blocks",
            "extracts",
            "extract_tys",
            "loads",
            "load_tys",
            "rets",
            "order",
            "const_tys",
            "edge_args",
            "block_params",
            "switch_on",
        ],
    },
    Chain {
        who: "level_kind_ord",
        fixture: "level_kind_ord.trust-ir.txt",
        spec: "eval_ir_kind_ord.rs",
        blocks_prefix: "const SRC_IR_KO_B",
        block_marker: "def ir_ko_b",
        func_prefix: "const SRC_IR_KO_FUNC",
        nonempty: &[
            "blocks",
            "int_consts",
            "cases",
            "default",
            "branches",
            "param_blocks",
            "extracts",
            "extract_tys",
            "loads",
            "load_tys",
            "rets",
            "order",
            "const_tys",
            "edge_args",
            "block_params",
            "switch_on",
        ],
    },
    Chain {
        who: "from_source_system",
        fixture: "from_source_system.trust-ir.txt",
        spec: "eval_ir_from_source.rs",
        blocks_prefix: "const SRC_IR_FS_B",
        block_marker: "def ir_fs_b",
        func_prefix: "const SRC_IR_FS_FUNC",
        // No `loads`: the argument arrives BY VALUE, which is what made this
        // chain structurally different from the first two.
        nonempty: &[
            "blocks",
            "agg_consts",
            "cases",
            "default",
            "branches",
            "param_blocks",
            "extracts",
            "extract_tys",
            "rets",
            "order",
            "const_tys",
            "edge_args",
            "block_params",
            "switch_on",
        ],
    },
    Chain {
        who: "flat_flags_contains",
        fixture: "flat_flags_contains.trust-ir.txt",
        spec: "eval_ir_contains.rs",
        blocks_prefix: "const SRC_IR_FC_B",
        block_marker: "def ir_fc_b",
        func_prefix: "const SRC_IR_FC_FUNC",
        // ONE block: it computes and returns, so it reaches no control-flow lane
        // and materializes no constant at all.
        nonempty: &[
            "blocks",
            "extracts",
            "extract_tys",
            "icmps",
            "binops",
            "binop_tys",
            "icmp_tys",
            "rets",
            "order",
        ],
    },
    Chain {
        who: "bvar_in_range",
        fixture: "bvar_in_range.trust-ir.txt",
        spec: "eval_ir_bvar_range.rs",
        blocks_prefix: "const SRC_IR_BR_B",
        block_marker: "def ir_br_b",
        func_prefix: "const SRC_IR_BR_FUNC",
        // Branches instead of dispatching, so `cases` / `default` / `switch_on`
        // are empty where the first three chains fill them.
        nonempty: &[
            "blocks",
            "consts",
            "int_consts",
            "branches",
            "param_blocks",
            "icmps",
            "condbrs",
            "icmp_tys",
            "rets",
            "order",
            "const_tys",
            "edge_args",
            "block_params",
        ],
    },
    Chain {
        who: "is_valid_char",
        fixture: "is_valid_char.trust-ir.txt",
        spec: "eval_ir_valid_char.rs",
        blocks_prefix: "const SRC_IR_VC_B",
        block_marker: "def ir_vc_b",
        func_prefix: "const SRC_IR_VC_FUNC",
        nonempty: &[
            "blocks",
            "consts",
            "int_consts",
            "branches",
            "param_blocks",
            "icmps",
            "condbrs",
            "icmp_tys",
            "rets",
            "order",
            "const_tys",
            "edge_args",
            "block_params",
        ],
    },
    Chain {
        who: "expr_path_step_clone",
        fixture: "expr_path_step_clone.trust-ir.txt",
        spec: "eval_ir_path_step.rs",
        blocks_prefix: "const SRC_IR_EP_B",
        block_marker: "def ir_ep_b",
        func_prefix: "const SRC_IR_EP_FUNC",
        nonempty: &[
            "blocks",
            "agg_consts",
            "cases",
            "default",
            "branches",
            "param_blocks",
            "extracts",
            "extract_tys",
            "loads",
            "load_tys",
            "rets",
            "order",
            "const_tys",
            "edge_args",
            "block_params",
            "switch_on",
        ],
    },
    Chain {
        who: "float_div",
        fixture: "float_div.trust-ir.txt",
        spec: "eval_ir_float_div.rs",
        blocks_prefix: "const SRC_IR_FD_B",
        block_marker: "def ir_fd_b",
        func_prefix: "const SRC_IR_FD_FUNC",
        // FOUR lanes on the whole body. This is the row that says why the
        // eighth chain had to add `binop_tys` and `rets`: without them the row
        // would read `blocks, binops` and the gate would be comparing a block
        // list and an operand pair.
        nonempty: &["blocks", "binops", "binop_tys", "rets", "order"],
    },
    Chain {
        who: "get_char_val_trunc",
        fixture: "get_char_val_trunc.trust-ir.txt",
        spec: "eval_ir_trunc.rs",
        blocks_prefix: "const SRC_IR_GC_B",
        block_marker: "def ir_gc_b",
        func_prefix: "const SRC_IR_GC_FUNC",
        // And this is the row that says why the ninth had to add `casts` and
        // `cast_tys`: without them it would read `blocks, rets` — one block and
        // a returned id — for a body whose entire content is the cast.
        nonempty: &["blocks", "casts", "cast_tys", "rets", "order"],
    },
    Chain {
        who: "meta_tag_shl",
        fixture: "meta_tag_shl.trust-ir.txt",
        spec: "eval_ir_meta_tag.rs",
        blocks_prefix: "const SRC_IR_MT_B0",
        block_marker: "def ir_mt_b0",
        func_prefix: "const SRC_IR_MT_FUNC",
        // The TENTH chain, and the only row with `asserts` in it. It is also
        // the row that made the three constant lanes per-INSTRUCTION: three
        // integer constants in ONE block, which the block-keyed lanes kept one
        // of.
        nonempty: &[
            "blocks",
            "int_consts",
            "icmps",
            "binops",
            "binop_tys",
            "icmp_tys",
            "casts",
            "cast_tys",
            "rets",
            "const_tys",
            "asserts",
            "order",
        ],
    },
    Chain {
        who: "simp_priority_value",
        fixture: "simp_priority_value.trust-ir.txt",
        // MINTED, like has_cubical_layer: the Clean side is the generated
        // script, not hand-written constants.
        spec: "generated/ir_pv.defs.txt",
        blocks_prefix: "def ir_pv_",
        block_marker: "def ir_pv_b",
        func_prefix: "def ir_pv_func",
        // The ELEVENTH chain, and the ONLY row with `geps` in it — which is
        // why the lane exists at all. Read this row against `has_cubical_layer`
        // above: same load/extractfield/switch/join skeleton, and then a
        // SECOND load whose pointer is an address this body computed.
        nonempty: &[
            "blocks",
            "int_consts",
            "cases",
            "default",
            "branches",
            "param_blocks",
            "extracts",
            "extract_tys",
            "loads",
            "load_tys",
            "geps",
            "rets",
            "const_tys",
            "edge_args",
            "block_params",
            "switch_on",
            "order",
        ],
    },
];

/// Every lane of `Cfg`, paired with the predicate "this lane is non-empty".
///
/// The list is what the matrix is stated in, so it has to be TOTAL over the
/// shape. `every_cfg_field_is_a_named_lane` proves that against the struct
/// itself rather than against this comment.
fn lanes(c: &Cfg) -> Vec<(&'static str, bool)> {
    vec![
        ("blocks", !c.blocks.is_empty()),
        ("consts", !c.consts.is_empty()),
        ("int_consts", !c.int_consts.is_empty()),
        ("agg_consts", !c.agg_consts.is_empty()),
        ("cases", !c.cases.is_empty()),
        ("default", c.default != u32::MAX),
        ("branches", !c.branches.is_empty()),
        ("param_blocks", !c.param_blocks.is_empty()),
        ("extracts", !c.extracts.is_empty()),
        ("extract_tys", !c.extract_tys.is_empty()),
        ("insertfields", !c.insertfields.is_empty()),
        ("stores", !c.stores.is_empty()),
        ("loads", !c.loads.is_empty()),
        ("load_tys", !c.load_tys.is_empty()),
        ("geps", !c.geps.is_empty()),
        ("icmps", !c.icmps.is_empty()),
        ("binops", !c.binops.is_empty()),
        ("condbrs", !c.condbrs.is_empty()),
        ("binop_tys", !c.binop_tys.is_empty()),
        ("icmp_tys", !c.icmp_tys.is_empty()),
        ("casts", !c.casts.is_empty()),
        ("cast_tys", !c.cast_tys.is_empty()),
        ("rets", !c.rets.is_empty()),
        ("const_tys", !c.const_tys.is_empty()),
        ("edge_args", !c.edge_args.is_empty()),
        ("block_params", !c.block_params.is_empty()),
        ("asserts", !c.asserts.is_empty()),
        ("switch_on", c.switch_on != u32::MAX),
        ("order", !c.order.is_empty()),
    ]
}

/// THE MATRIX. Eleven chains x **twenty-nine** lanes, pinned cell by cell.
///
/// (Twenty-seven until 2026-08-20, when `insertfields` and `stores` were added
/// AHEAD of the last three chains — two of whose committed fixtures
/// (`flat_flags_with`, `strict_monads`) are built around instructions no lane
/// read: an insertfield's FIELD INDEX and a store's every operand were
/// compared by nothing, since `order` sees only class-plus-results. Every row
/// below is pinned WITHOUT them, so both lanes are checked empty-on-both-sides
/// across every chain in the matrix by this very test. Discrimination proofs:
/// `lane_matrix_writes.rs`.)
///
/// (Twenty-six until 2026-08-20, when the eleventh chain added `geps` — the
/// lane for an instruction no chained body had ever contained, so a
/// transcription that gep'd a different base, by a different index, at a
/// different element type, or that dropped `inbounds`, compared EQUAL in every
/// other lane. Same class as `extract_tys` and `load_tys` below.)
///
/// (Twenty-four until 2026-08-19, when the operand-completeness audit added
/// `extract_tys` and `load_tys` — the two slots that were printed by the
/// artifact, carried by the registered term, and read by neither parser.
/// Corrected 2026-08-17: this read "twenty-three" while `lanes()` enumerated
/// twenty-four. The count is not load-bearing here — `every_cfg_field_is_a_named_lane`
/// proves the enumeration against `Cfg`'s own fields with equal cardinality, so
/// the GATE was right and only the sentence was wrong — but a wrong number in a
/// gate's own doc-comment is what a reader quotes.)
#[test]
fn the_lane_matrix_is_pinned_for_every_chain() {
    for ch in CHAINS {
        let emitted = parse_emitted(&fixture(ch.fixture));
        let clean = parse_clean(
            &clean_block_sources(ch.spec, ch.blocks_prefix),
            ch.block_marker,
        );
        let e = lanes(&emitted);
        let c = lanes(&clean);

        // EMPTY-AND-BLIND is the category this file exists to refuse: a lane
        // non-empty on one side and empty on the other means one parser reads a
        // construct the other does not, and the vacuous half compares equal to
        // anything.
        for ((ln, en), (_, cn)) in e.iter().zip(c.iter()) {
            assert_eq!(
                en, cn,
                "{}: lane `{ln}` is non-empty on ONE side only (emitted {en}, Clean {cn}). One \
                 parser reads a construct the other drops, which is how a lane becomes vacuous \
                 without anything failing.",
                ch.who
            );
        }

        let measured: Vec<&str> = e
            .iter()
            .filter(|(_, n)| *n)
            .map(|(ln, _)| *ln)
            .collect::<Vec<_>>();
        let mut pinned = ch.nonempty.to_vec();
        pinned.sort_unstable();
        let mut measured_sorted = measured.clone();
        measured_sorted.sort_unstable();
        assert_eq!(
            measured_sorted, pinned,
            "{}: the set of NON-EMPTY lanes changed. Measured {measured:?}; pinned {:?}. Either \
             the body gained a construct — add the lane, do not widen this list — or it LOST one, \
             which shrinks what the gate compares and is the vacuity mode this file is the \
             denominator for.",
            ch.who, ch.nonempty
        );
    }
}

/// **PARSER TOTALITY: every instruction the nine bodies contain has a lane.**
///
/// The cast was in no lane at all, and nothing noticed until a chain's body was
/// nothing but a cast. This reads the mnemonics straight out of the fixtures and
/// requires each to be one the parser routes somewhere — so the NEXT construct
/// to appear in an emitted body fails here, naming itself, instead of being
/// silently skipped by the `_ => {}` arm.
#[test]
fn every_emitted_mnemonic_has_a_lane() {
    // mnemonic -> the lane(s) `parse_emitted` routes it to.
    const ROUTED: &[(&str, &str)] = &[
        ("and", "binops + binop_tys"),
        ("assert", "asserts"),
        ("bitcast", "casts + cast_tys"),
        ("br", "branches + edge_args"),
        ("condbr", "condbrs + edge_args"),
        ("const", "consts | int_consts | agg_consts, and const_tys"),
        ("extractfield", "extracts"),
        ("fdiv", "binops + binop_tys"),
        ("icmp", "icmps + icmp_tys"),
        ("gep", "geps"),
        ("load", "loads"),
        ("ret", "rets"),
        ("sext", "casts + cast_tys"),
        ("shl", "binops + binop_tys"),
        ("switch", "cases + default + switch_on"),
        ("trunc", "casts + cast_tys"),
    ];
    let mut seen: BTreeSet<String> = BTreeSet::new();
    for ch in CHAINS {
        for raw in fixture(ch.fixture).lines() {
            let line = raw.split("; #").next().unwrap_or(raw).trim();
            if line.is_empty()
                || line.starts_with("rustcc")
                || line.starts_with("bb")
                || line.starts_with(';')
                || line == "}"
            {
                continue;
            }
            let body = line.split_once(" = ").map_or(line, |(_, r)| r);
            if let Some(op) = body.split_whitespace().next() {
                seen.insert(op.trim_end_matches(',').to_string());
            }
        }
    }
    let routed: BTreeSet<String> = ROUTED.iter().map(|(m, _)| (*m).to_string()).collect();
    assert_eq!(
        seen, routed,
        "the set of instruction mnemonics in the ten fixtures changed. Every one must be routed \
         to a lane by `parse_emitted`; a mnemonic the parser does not name falls through its \
         `_ => {{}}` arm and is compared by NOTHING, on both sides, which is exactly how a cast \
         survived until the ninth chain."
    );
}

#[path = "lane_matrix_shape.rs"]
mod shape_checks;

#[path = "lane_matrix_writes.rs"]
mod writes_lane_proofs;

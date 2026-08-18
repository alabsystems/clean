// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The emitted-side parser: trust-ir text in, `Cfg` out.**
//!
//! Split out of `emitted_cfg.rs` on 2026-08-16, when the lane-completeness audit
//! added four lanes and took that file past the size it had already been split
//! at twice. Nothing about the shape changed in the move — `emitted_cfg.rs`
//! keeps `Cfg`, the shared token helpers and the lane comparator; this file
//! kept the two readers that produce a `Cfg`, and on 2026-08-17 the CLEAN one
//! moved on to `emitted_cfg_parse_clean.rs` for the same reason again.
//!
//! **The rule the audit added, and the reason this file exists as a unit:** a
//! parser that silently drops an operand slot is the same defect as a missing
//! lane. `switch`'s scrutinee, `br`/`condbr`'s block arguments, a block's
//! parameter ids and a constant's TYPE were each read by neither side until
//! 2026-08-16, and each is semantic input to `eval_ir_machine` — see the
//! per-lane doc comments on `Cfg`. Anything this file cannot read must FAIL
//! LOUDLY (`switch` with block arguments) rather than parse to nothing on both
//! sides and compare equal.

use std::collections::{BTreeMap, BTreeSet};

use super::emitted_cfg_types::norm_emitted_ty;
use super::{header_param_ids, id_of, split_commas_top, split_top, target_and_args, Cfg};

/// Every arithmetic and bitwise `binop` opcode trust-ir prints.
const ARITH: &[&str] = &[
    "add", "sub", "mul", "udiv", "sdiv", "urem", "srem", "shl", "lshr", "ashr", "and", "or", "xor",
    "fadd", "fsub", "fmul", "fdiv", "frem",
];

/// All 17 of `trust_ir::CastOp`, so an opcode this chain does not use cannot
/// fall through to the arithmetic arm or be silently dropped.
const CASTS: &[&str] = &[
    "trunc",
    "zext",
    "sext",
    "fptrunc",
    "fpext",
    "fptoui",
    "fptosi",
    "uitofp",
    "sitofp",
    "ptrtoint",
    "inttoptr",
    "ptrtoptr",
    "bitcast",
    "transmute",
    "reifyfnpointer",
    "fptosisat",
    "fptouisat",
];

pub(crate) fn parse_emitted(text: &str) -> Cfg {
    let mut consts: BTreeMap<u32, Vec<(u32, bool)>> = BTreeMap::new();
    let (mut cases, mut branches) = (BTreeMap::new(), BTreeMap::new());
    let (mut default, mut param_blocks, mut blocks, mut cur) =
        (u32::MAX, BTreeSet::new(), vec![], None);
    let mut int_consts: BTreeMap<u32, Vec<(u32, u32)>> = BTreeMap::new();
    let mut agg_consts: BTreeMap<u32, Vec<(u32, u32)>> = BTreeMap::new();
    let mut extracts: BTreeMap<u32, Vec<(u32, u32, u32)>> = BTreeMap::new();
    let mut loads: BTreeMap<u32, Vec<(u32, u32)>> = BTreeMap::new();
    let mut icmps: BTreeMap<u32, Vec<(String, u32, u32, u32)>> = BTreeMap::new();
    let mut binops: BTreeMap<u32, Vec<(String, u32, u32, u32)>> = BTreeMap::new();
    let mut condbrs: BTreeMap<u32, (u32, u32, u32)> = BTreeMap::new();
    let mut binop_tys: BTreeMap<u32, Vec<(String, u32, String)>> = BTreeMap::new();
    let mut icmp_tys: BTreeMap<u32, Vec<(String, u32, String)>> = BTreeMap::new();
    let mut rets: BTreeMap<u32, Vec<u32>> = BTreeMap::new();
    let mut casts: BTreeMap<u32, Vec<(String, u32, u32)>> = BTreeMap::new();
    let mut cast_tys: BTreeMap<u32, Vec<(String, u32, String, String)>> = BTreeMap::new();
    let mut const_tys: BTreeMap<u32, Vec<(u32, String)>> = BTreeMap::new();
    let mut edge_args: BTreeMap<u32, Vec<Vec<u32>>> = BTreeMap::new();
    let mut block_params: BTreeMap<u32, Vec<u32>> = BTreeMap::new();
    let mut switch_on = u32::MAX;
    let mut asserts: BTreeMap<u32, Vec<u32>> = BTreeMap::new();
    let mut order: BTreeMap<u32, Vec<(String, Vec<u32>)>> = BTreeMap::new();
    for raw in text.lines() {
        let line = raw.split("; #").next().unwrap_or(raw).trim();
        // PROGRAM ORDER, before any lane: the ordered `(class, result)` of every
        // instruction in the block, whether or not this parser has a lane for
        // its operands. Every other lane is per-KIND, so the INTERLEAVING of
        // kinds is compared by nothing else: moving `and u8 %2, %3` above the
        // extractfields that bind %2 and %3 leaves `binops`, `extracts`,
        // `icmps` and every type lane bit-identical, and reads two bindings
        // that do not exist yet.
        if let Some(b) = cur {
            if let Some((class, rs)) = emitted_class(line) {
                order.entry(b).or_default().push((class, rs));
            }
        }
        // `%r = <op> …` / `%r, %s = <op> …` — the value-producing lanes. The
        // LHS is a LIST: `mul.overflow` binds two ids, and reading it with a
        // bare `id_of` returned `None` and dropped the whole instruction.
        if let (Some(b), Some((lhs, rhs))) = (cur, line.split_once(" = ")) {
            if let Some(&r) = emitted_results(lhs).first() {
                let t = split_top(rhs);
                match t.first().map(String::as_str) {
                    // `%2 = extractfield u8 %0, 0`
                    Some("extractfield") => {
                        if let (Some(src), Some(k)) = (
                            t.get(2).and_then(|s| id_of(s)),
                            t.get(3).and_then(|s| id_of(s)),
                        ) {
                            extracts.entry(b).or_default().push((r, src, k));
                        }
                    }
                    // `%2 = load enum.2, ptr %0`
                    Some("load") => {
                        if let Some(src) = t.last().and_then(|s| id_of(s)) {
                            loads.entry(b).or_default().push((r, src));
                        }
                    }
                    // `%6 = icmp eq u8 %4, %5`
                    Some("icmp") => {
                        if let (Some(op), Some(a), Some(c)) = (
                            t.get(1),
                            t.get(3).and_then(|s| id_of(s)),
                            t.get(4).and_then(|s| id_of(s)),
                        ) {
                            icmps.entry(b).or_default().push((op.clone(), r, a, c));
                            icmp_tys.entry(b).or_default().push((
                                op.clone(),
                                r,
                                norm_emitted_ty(t.get(2).map_or("", String::as_str)),
                            ));
                        }
                    }
                    // `%4 = const bool true` / `const u8 3` / `const enum.13 { 0 }`
                    // — the RESULT id and the TYPE. The three value lanes below
                    // carry neither, and both are semantic input: `ir_const_eval`
                    // canonicalizes an integer constant modulo 2^w and faults a
                    // scalar constant at an aggregate type.
                    Some("const") => {
                        const_tys
                            .entry(b)
                            .or_default()
                            .push((r, norm_emitted_ty(t.get(1).map_or("", String::as_str))));
                        emitted_const_value(
                            b,
                            r,
                            &t,
                            &mut consts,
                            &mut int_consts,
                            &mut agg_consts,
                        );
                    }
                    // `%2 = trunc u64 %1 to u32` — op, SOURCE type, operand,
                    // the literal `to`, DESTINATION type
                    // (`trust-ir/src/display.rs:664`).
                    Some(op) if CASTS.contains(&op) => {
                        if let (Some(a), Some("to")) = (
                            t.get(2).and_then(|s| id_of(s)),
                            t.get(3).map(String::as_str),
                        ) {
                            casts.entry(b).or_default().push((op.to_string(), r, a));
                            cast_tys.entry(b).or_default().push((
                                op.to_string(),
                                r,
                                norm_emitted_ty(t.get(1).map_or("", String::as_str)),
                                norm_emitted_ty(t.get(4).map_or("", String::as_str)),
                            ));
                        }
                    }
                    // `%4 = and u8 %2, %3`
                    Some(op) if ARITH.contains(&op) => {
                        if let (Some(a), Some(c)) = (
                            t.get(2).and_then(|s| id_of(s)),
                            t.get(3).and_then(|s| id_of(s)),
                        ) {
                            binops.entry(b).or_default().push((op.to_string(), r, a, c));
                            binop_tys.entry(b).or_default().push((
                                op.to_string(),
                                r,
                                norm_emitted_ty(t.get(1).map_or("", String::as_str)),
                            ));
                        }
                    }
                    _ => {}
                }
            }
        }
        // `assert %4`. One operand, no result, no target: the failure edge is
        // in the SEMANTICS (`ir_assert_b`'s `false` minor is
        // `IROutcome.ub IRFault.assert_failed`), not in the instruction. Anything
        // past the scrutinee is REFUSED rather than dropped.
        if let (Some(b), Some(rest)) = (cur, line.strip_prefix("assert ")) {
            let toks = split_top(rest);
            assert_eq!(
                toks.len(),
                1,
                "an `assert` carries {} operands ({rest:?}), and this parser reads exactly one \
                 — the scrutinee. trust-ir's Assert has no target and no type; if that has \
                 changed, add the lane rather than letting the extra slot parse to nothing on \
                 both sides.",
                toks.len()
            );
            let c = id_of(&toks[0])
                .unwrap_or_else(|| panic!("an `assert`'s scrutinee is not an SSA id: {rest:?}"));
            asserts.entry(b).or_default().push(c);
        }
        // `ret %3` / bare `ret`. The lane nothing looked at until the eighth
        // chain, whose entire body is one instruction and this terminator.
        if let Some(b) = cur {
            if line == "ret" || line.starts_with("ret ") {
                let ids = line
                    .strip_prefix("ret")
                    .unwrap_or("")
                    .split_whitespace()
                    .filter_map(id_of)
                    .collect::<Vec<u32>>();
                rets.insert(b, ids);
            }
        }
        // `condbr %6, bb1, bb2` — and, when the lowerer emits them,
        // `condbr %6, bb1(%7), bb2(%8)`. Both edges' ARGUMENT lists are
        // recorded: `ir_condbr_b` hands them to `ir_jump`, which resolves them
        // and binds them into the target block's parameters.
        if let (Some(b), Some(rest)) = (cur, line.strip_prefix("condbr ")) {
            let t = split_top(rest);
            if let (Some(c), Some((tt, targs)), Some((et, eargs))) = (
                t.first().and_then(|s| id_of(s)),
                t.get(1).and_then(|s| target_and_args(s)),
                t.get(2).and_then(|s| target_and_args(s)),
            ) {
                condbrs.insert(b, (c, tt, et));
                edge_args.insert(b, vec![targs, eargs]);
            }
        }
        if let Some(rest) = line.strip_prefix("bb") {
            if let Some((num, tail)) = rest.split_once([':', '(']) {
                if let Ok(id) = num.parse::<u32>() {
                    blocks.push(id);
                    cur = Some(id);
                    // A parameter list is `bbN(%k: ty):`; the entry block's `(%0: ptr)`
                    // is the FUNCTION parameter, so only non-entry blocks count.
                    if (raw.contains("(%") || tail.starts_with('%')) && id != 0 {
                        param_blocks.insert(id);
                        let ps = header_param_ids(line);
                        if !ps.is_empty() {
                            block_params.insert(id, ps);
                        }
                    }
                }
            }
        } else if line.contains("switch") {
            if let Some(v) = line
                .split_once("switch ")
                .and_then(|(_, r)| r.split_whitespace().next())
                .and_then(id_of)
            {
                switch_on = v;
            }
            if let Some(inner) = line.split_once('[').and_then(|(_, r)| r.split_once(']')) {
                assert!(
                    !inner.0.contains('('),
                    "a switch arm carries BLOCK ARGUMENTS ({}), which this parser does not read. \
                     `ir_switch_n` hands `ir_case_args` / the default args to `ir_jump`, so they \
                     are semantic input; refusing loudly is the `?usize` rule — a slot this \
                     parser cannot read must never parse to nothing on both sides and compare \
                     equal.",
                    inner.0.trim()
                );
                for tok in inner.0.split_whitespace().collect::<Vec<_>>().chunks(2) {
                    if let [k, v] = tok {
                        let tgt = v
                            .trim_start_matches("bb")
                            .parse::<u32>()
                            .unwrap_or(u32::MAX);
                        if k.starts_with("default") {
                            default = tgt;
                        } else if let Ok(val) = k.trim_end_matches(':').parse::<u32>() {
                            cases.insert(val, tgt);
                        }
                    }
                }
            }
        }
        if let Some(t) = line.strip_prefix("br bb") {
            if let (Some(b), Some((tgt, args))) = (cur, target_and_args(t)) {
                branches.insert(b, tgt);
                edge_args.insert(b, vec![args]);
            }
        }
    }
    Cfg {
        consts,
        int_consts,
        agg_consts,
        cases,
        default,
        branches,
        param_blocks,
        blocks,
        extracts,
        loads,
        icmps,
        binops,
        condbrs,
        binop_tys,
        icmp_tys,
        rets,
        casts,
        cast_tys,
        const_tys,
        edge_args,
        block_params,
        asserts,
        switch_on,
        order,
    }
}

/// The SSA ids an emitted assignment's left-hand side binds: `%2` -> `[2]`,
/// `%2, %3` -> `[2, 3]`.
///
/// **A list since 2026-08-16.** `mul.overflow` binds two — the wrapped product
/// and the overflow flag — and it is the shape of nine of the crate's
/// twenty-one assert-carrying CTFE flips. A bare `id_of("%2, %3")` returns
/// `None`, which dropped the instruction out of EVERY lane including `order`.
fn emitted_results(lhs: &str) -> Vec<u32> {
    split_commas_top(lhs)
        .iter()
        .filter_map(|t| id_of(t.trim()))
        .collect()
}

/// Record a `const` instruction's VALUE in whichever of the three value lanes
/// its literal belongs to. A shape none of them can read records nothing here
/// and is caught by `assert_lanes`'s no-constant-dropped check.
fn emitted_const_value(
    b: u32,
    r: u32,
    t: &[String],
    consts: &mut BTreeMap<u32, Vec<(u32, bool)>>,
    int_consts: &mut BTreeMap<u32, Vec<(u32, u32)>>,
    agg_consts: &mut BTreeMap<u32, Vec<(u32, u32)>>,
) {
    let (Some(ty), Some(lit)) = (t.get(1), t.get(2)) else {
        return;
    };
    if ty == "bool" {
        // `const bool true` / `const bool false`
        if lit == "true" || lit == "false" {
            consts.entry(b).or_default().push((r, lit == "true"));
        }
        return;
    }
    let width_typed = ty
        .strip_prefix(['u', 'i'])
        .is_some_and(|w| !w.is_empty() && w.chars().all(|c| c.is_ascii_digit()));
    if width_typed {
        // `const u8 3`
        if let Ok(v) = lit.parse::<u32>() {
            int_consts.entry(b).or_default().push((r, v));
        }
    } else if lit == "{" {
        // Exactly `const enum.13 { K }` — a one-element aggregate whose element
        // is an integer (`Constant::Aggregate`'s text form,
        // `trust-ir/src/display.rs:1280`). Anything longer or nested is
        // deliberately NOT recorded, so a body with a richer constant cannot
        // silently reuse this lane — it fails the no-constant-dropped check.
        if let (Some(k), Some(close)) = (t.get(3), t.get(4)) {
            if close == "}" {
                if let Ok(v) = k.parse::<u32>() {
                    agg_consts.entry(b).or_default().push((r, v));
                }
            }
        }
    }
}

/// The `(class, results)` an emitted line contributes to the program-order lane,
/// or `None` for anything that is not an instruction (a block header, the
/// function header, a bare comment, the closing brace).
///
/// The class vocabulary is the CLEAN one — `and` and `fdiv` are both `binop`,
/// `trunc` is `cast` — because the lane is compared against
/// `IRInst.<ctor>` names. An opcode with no lane at all still gets its own
/// class rather than being dropped, so the order lane is also where an
/// unmodelled instruction shows up.
fn emitted_class(line: &str) -> Option<(String, Vec<u32>)> {
    if line.is_empty() || line == "}" || line.starts_with("rustcc") || line.starts_with(';') {
        return None;
    }
    // A block header (`bb4(%1: bool):`) is not an instruction, and at this point
    // `cur` is still the PREVIOUS block, so recording it would mis-attribute it.
    if line
        .strip_prefix("bb")
        .and_then(|r| r.split_once([':', '(']))
        .and_then(|(n, _)| n.parse::<u32>().ok())
        .is_some()
    {
        return None;
    }
    let (head, rs) = match line.split_once(" = ") {
        Some((lhs, rhs)) => (
            split_top(rhs).first().cloned().unwrap_or_default(),
            emitted_results(lhs),
        ),
        None => (
            line.split_whitespace().next().unwrap_or("").to_string(),
            Vec::new(),
        ),
    };
    if head.is_empty() {
        return None;
    }
    let class = if ARITH.contains(&head.as_str()) {
        "binop".to_string()
    } else if CASTS.contains(&head.as_str()) {
        "cast".to_string()
    } else {
        head
    };
    Some((class, rs))
}

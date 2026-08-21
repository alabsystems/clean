// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The Clean-side reader: registered spec sources in, `Cfg` out.**
//!
//! Split out of `emitted_cfg_parse.rs` VERBATIM on 2026-08-17 — `clean_insts`
//! and `parse_clean` moved unchanged, not one line of either altered — because
//! that file had reached 773 lines and `data/paragon_ratchet.json`'s
//! `files_over_500` is shrink-only. `emitted_cfg_parse.rs` keeps the EMITTED
//! reader; this file keeps the CLEAN one. The split is along the seam the gate
//! already has: the two readers share `Cfg` and the token helpers and call
//! nothing of each other.
//!
//! The rule from the 2026-08-16 lane-completeness audit applies here unchanged:
//! a parser that silently drops an operand slot is the same defect as a missing
//! lane, so anything this file cannot read must FAIL LOUDLY rather than parse
//! to nothing on both sides and compare equal.

use std::collections::{BTreeMap, BTreeSet};

use super::emitted_cfg_types::{clean_ty_aliases, norm_clean_ty, numerals_in};
use super::{split_top, Cfg};

/// One Clean-side instruction: the text inside `(IRInst. … )` and the SSA id
/// the enclosing node binds it to (`ir_nd1 (…) ir_d7` binds 7; `ir_nd (…)`
/// binds nothing).
///
/// Extracted by parenthesis matching rather than by splitting on whitespace,
/// because an instruction's arguments are themselves parenthesised terms.
pub(crate) fn clean_insts(body: &str) -> Vec<(String, Vec<u32>)> {
    // BYTE indices throughout. `(` and `)` are single-byte and therefore always
    // char boundaries, but the spec sources contain non-ASCII (box-drawing rules
    // in the surrounding comments), so a char-index scan and a `&str` slice
    // cannot be mixed: doing so panicked mid-codepoint the first time this ran.
    let bytes = body.as_bytes();
    let mut out = Vec::new();
    let mut i = 0usize;
    while i < bytes.len() {
        if bytes[i] == b'(' && body[i..].starts_with("(IRInst.") {
            let (mut depth, mut j) = (0i32, i);
            while j < bytes.len() {
                match bytes[j] {
                    b'(' => depth += 1,
                    b')' => {
                        depth -= 1;
                        if depth == 0 {
                            break;
                        }
                    }
                    _ => {}
                }
                j += 1;
            }
            if j >= bytes.len() {
                break;
            }
            let inst: String = body[i + 1..j].to_string();
            // The next whitespace-delimited token after the closing paren is
            // the node's result id, unless the node ends there.
            let tail: &str = &body[j + 1..];
            // The trailing punctuation is trimmed as a SET, not just `)`. These
            // declarations are Rust string literals, so a node that is LAST in
            // its block ends `… ir_d3)))";` — and trimming only `)` left
            // `3)))";`, which parsed as nothing and dropped the node's result
            // id. Measured, not hypothetical: it is what a program-order
            // perturbation hit on 2026-08-16. Every real declaration ends in a
            // terminator, which binds nothing, so it had never been reached.
            // A node's result slot is `ir_dK` for `ir_nd1`, the whole
            // parenthesised list for a multi-result node (`ir_nd2 (…) (ir_nl2
            // ir_d2 ir_d3)`), and absent for `ir_nd`. All three are read as a
            // LIST since 2026-08-16: a two-result node's ids were dropped
            // wholesale before, and dropped ids compare equal to dropped ids.
            let next = tail
                .split_whitespace()
                .next()
                .filter(|t| !t.starts_with(')'))
                .unwrap_or("");
            let results = if next.starts_with("(ir_nl") {
                numerals_in(split_top(tail).first().map_or("", String::as_str))
            } else {
                next.trim_end_matches([')', '"', ';', ','])
                    .strip_prefix("ir_d")
                    .and_then(|t| t.parse::<u32>().ok())
                    .into_iter()
                    .collect()
            };
            out.push((inst, results));
            i = j + 1;
        } else {
            i += 1;
        }
    }
    out
}

/// The same facts, read off the registered Clean spec sources.
///
/// `block_marker` is the `def` prefix the block declarations share, e.g.
/// `"def ir_h2_b"` or `"def ir_lz_b"`.
pub(crate) fn parse_clean(src: &str, block_marker: &str) -> Cfg {
    // `ir_dN` numerals; blocks are `IRBlock.mk ir_dID params ...`.
    let n = |s: &str| s.trim().trim_start_matches("ir_d").parse::<u32>().ok();
    let mut consts: BTreeMap<u32, Vec<(u32, bool)>> = BTreeMap::new();
    let (mut cases, mut branches) = (BTreeMap::new(), BTreeMap::new());
    let (mut default, mut param_blocks, mut blocks) = (u32::MAX, BTreeSet::new(), vec![]);
    let mut int_consts: BTreeMap<u32, Vec<(u32, u32)>> = BTreeMap::new();
    let mut agg_consts: BTreeMap<u32, Vec<(u32, u32)>> = BTreeMap::new();
    let mut extracts: BTreeMap<u32, Vec<(u32, u32, u32)>> = BTreeMap::new();
    let mut loads: BTreeMap<u32, Vec<(u32, u32)>> = BTreeMap::new();
    let mut load_tys: BTreeMap<u32, Vec<(u32, String, bool)>> = BTreeMap::new();
    let mut geps: BTreeMap<u32, Vec<(u32, String, u32, Vec<u32>, bool)>> = BTreeMap::new();
    let mut extract_tys: BTreeMap<u32, Vec<(u32, String)>> = BTreeMap::new();
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
    let aliases = clean_ty_aliases();
    for decl in src.split(block_marker).skip(1) {
        let body = decl.split_once(":=").map(|(_, b)| b).unwrap_or(decl);
        let after = body.split_once("IRBlock.mk").map(|(_, r)| r).unwrap_or("");
        // Parenthesis-aware, so the parameter list `(ir_nl1 ir_d1)` is ONE
        // token instead of two: the id inside it is the join parameter, which
        // `ir_bind_params` binds the incoming block arguments to.
        let top = split_top(after);
        let id = top.first().and_then(|s| n(s)).unwrap_or(u32::MAX);
        blocks.push(id);
        let params = top.get(1).map_or("", String::as_str);
        if params != "ir_nl0" && id != 0 {
            param_blocks.insert(id);
            let ps = numerals_in(params);
            if !ps.is_empty() {
                block_params.insert(id, ps);
            }
        }
        if let Some(sw) = body.split_once("IRInst.switch").map(|(_, r)| r) {
            let toks: Vec<&str> = sw.split_whitespace().collect();
            // `switch <scrut> <dflt> <dargs> (ir_sc <v> <tgt> (ir_sc …))`
            if let Some(v) = toks.first().and_then(|t| n(t)) {
                switch_on = v;
            }
            if let Some(d) = toks.get(1).and_then(|t| n(t)) {
                default = d;
            }
            // The default-argument slot and the arm-argument slots are semantic
            // input (`ir_switch_n` hands both to `ir_jump`). `ir_sc` hardwires
            // arm arguments to `ir_nl0`, so an arm built any other way, or a
            // non-empty default list, is REFUSED rather than dropped.
            assert_eq!(
                toks.get(2).copied(),
                Some("ir_nl0"),
                "the registered switch carries DEFAULT BLOCK ARGUMENTS, which this parser does \
                 not read: {sw}"
            );
            assert!(
                !sw.contains("IRSwitchCase.mk"),
                "the registered switch builds an arm outside `ir_sc`, whose argument list this \
                 parser does not read: {sw}"
            );
            let mut rest = sw;
            while let Some((_, r)) = rest.split_once("ir_sc ") {
                let mut t = r.split_whitespace();
                if let (Some(v), Some(g)) = (t.next().and_then(n), t.next().and_then(n)) {
                    cases.insert(v, g);
                }
                rest = r;
            }
        }
        if let Some(br) = body.split_once("IRInst.br").map(|(_, r)| r) {
            if let Some(t) = br.split_whitespace().next().and_then(n) {
                branches.insert(id, t);
            }
        }
        // The instruction lanes, node by node, so a node's RESULT id travels
        // with it. `n` is applied to every operand, so a literal that is not an
        // `ir_dK` numeral is dropped rather than silently mis-read.
        for (inst, results) in clean_insts(body) {
            let t = split_top(&inst);
            let head = t.first().map(String::as_str).unwrap_or("");
            let result = results.first().copied();
            fn strip<'a>(tok: &'a str, pfx: &str) -> &'a str {
                tok.trim_start_matches(pfx).trim_end_matches('_')
            }
            // Program order, for EVERY node — including constructors with no
            // lane, so an instruction this parser does not model still has to
            // appear in the same place on both sides.
            order
                .entry(id)
                .or_default()
                .push((strip(head, "IRInst.").to_string(), results.clone()));
            match head {
                // `IRInst.extractfield <ty> <agg> <field>` — the TYPE slot has
                // been read since the 2026-08-19 operand audit; before that it
                // was carried by the term, printed by the artifact, and
                // compared by nothing.
                "IRInst.extractfield" => {
                    if let (Some(r), Some(src), Some(k)) = (
                        result,
                        t.get(2).and_then(|s| n(s)),
                        t.get(3).and_then(|s| n(s)),
                    ) {
                        extracts.entry(id).or_default().push((r, src, k));
                        extract_tys.entry(id).or_default().push((
                            r,
                            norm_clean_ty(t.get(1).map_or("", String::as_str), &aliases),
                        ));
                    }
                }
                // `IRInst.load <ty> <ptr> <volatile>` — all three. The
                // constructor has exactly three operands, so a term with any
                // other arity is REFUSED rather than half-read.
                "IRInst.load" => {
                    assert_eq!(
                        t.len(),
                        4,
                        "the registered load carries {} operands ({inst}); `IRInst.load : IRTy \
                         -> Nat -> Bool -> IRInst` has exactly three and this parser reads all \
                         three",
                        t.len().saturating_sub(1)
                    );
                    let vol = match t.get(3).map(String::as_str) {
                        Some("Bool.true") => true,
                        Some("Bool.false") => false,
                        other => panic!(
                            "the registered load's VOLATILE slot is {other:?}, which is neither \
                             Bool.true nor Bool.false ({inst}). It is compared against the \
                             emitted `volatile` prefix, so an unreadable value here would \
                             compare equal to nothing rather than to the artifact."
                        ),
                    };
                    if let (Some(r), Some(src)) = (result, t.get(2).and_then(|s| n(s))) {
                        loads.entry(id).or_default().push((r, src));
                        load_tys.entry(id).or_default().push((
                            r,
                            norm_clean_ty(t.get(1).map_or("", String::as_str), &aliases),
                            vol,
                        ));
                    }
                }
                // `IRInst.gep <ty> <base> <idxs> <inbounds>` — all four. The
                // index slot is an `IRList Nat` and is read as a LIST, because
                // `ir_sum_idx` adds the whole list: a term that kept one index
                // and dropped the rest computes a different address and binds
                // the same SSA id.
                "IRInst.gep" => {
                    assert_eq!(
                        t.len(),
                        5,
                        "the registered gep carries {} operands ({inst}); `IRInst.gep : IRTy -> \
                         Nat -> IRList Nat -> Bool -> IRInst` has exactly four and this parser \
                         reads all four",
                        t.len().saturating_sub(1)
                    );
                    let inb = match t.get(4).map(String::as_str) {
                        Some("Bool.true") => true,
                        Some("Bool.false") => false,
                        other => panic!(
                            "the registered gep's INBOUNDS slot is {other:?}, which is neither \
                             Bool.true nor Bool.false ({inst}). It is compared against the \
                             emitted `inbounds` keyword, so an unreadable value here would \
                             compare equal to nothing rather than to the artifact."
                        ),
                    };
                    let idxs = numerals_in(t.get(3).map_or("", String::as_str));
                    assert!(
                        !idxs.is_empty(),
                        "the registered gep's INDEX LIST reads empty ({inst}); an empty list \
                         offsets by zero, and a slot that parses to nothing on one side would \
                         compare equal to a dropped index on the other"
                    );
                    if let (Some(r), Some(base)) = (result, t.get(2).and_then(|s| n(s))) {
                        geps.entry(id).or_default().push((
                            r,
                            norm_clean_ty(t.get(1).map_or("", String::as_str), &aliases),
                            base,
                            idxs,
                            inb,
                        ));
                    }
                }
                "IRInst.icmp" => {
                    if let (Some(op), Some(r), Some(a), Some(b)) = (
                        t.get(1),
                        result,
                        t.get(3).and_then(|s| n(s)),
                        t.get(4).and_then(|s| n(s)),
                    ) {
                        icmps.entry(id).or_default().push((
                            strip(op, "IRICmpOp.").to_string(),
                            r,
                            a,
                            b,
                        ));
                        icmp_tys.entry(id).or_default().push((
                            strip(op, "IRICmpOp.").to_string(),
                            r,
                            norm_clean_ty(t.get(2).map_or("", String::as_str), &aliases),
                        ));
                    }
                }
                "IRInst.binop" => {
                    if let (Some(op), Some(r), Some(a), Some(b)) = (
                        t.get(1),
                        result,
                        t.get(3).and_then(|s| n(s)),
                        t.get(4).and_then(|s| n(s)),
                    ) {
                        binops.entry(id).or_default().push((
                            strip(op, "IRBinOp.").to_string(),
                            r,
                            a,
                            b,
                        ));
                        binop_tys.entry(id).or_default().push((
                            strip(op, "IRBinOp.").to_string(),
                            r,
                            norm_clean_ty(t.get(2).map_or("", String::as_str), &aliases),
                        ));
                    }
                }
                "IRInst.cast" => {
                    if let (Some(op), Some(r), Some(a)) =
                        (t.get(1), result, t.get(4).and_then(|s| n(s)))
                    {
                        casts.entry(id).or_default().push((
                            strip(op, "IRCastOp.").to_string(),
                            r,
                            a,
                        ));
                        cast_tys.entry(id).or_default().push((
                            strip(op, "IRCastOp.").to_string(),
                            r,
                            norm_clean_ty(t.get(2).map_or("", String::as_str), &aliases),
                            norm_clean_ty(t.get(3).map_or("", String::as_str), &aliases),
                        ));
                    }
                }
                // `IRInst.const_ <ty> <const>` — the TYPE slot, the bound
                // RESULT id, and the VALUE. All three are per-node since
                // 2026-08-16; the value lanes used to be one per BLOCK and a
                // block materializing four constants kept one of each kind.
                "IRInst.const_" => {
                    if let Some(r) = result {
                        const_tys.entry(id).or_default().push((
                            r,
                            norm_clean_ty(t.get(1).map_or("", String::as_str), &aliases),
                        ));
                        let k = t.get(2).map_or("", String::as_str);
                        if k.contains("IRConst.bool_ Bool.true") {
                            consts.entry(id).or_default().push((r, true));
                        } else if k.contains("IRConst.bool_ Bool.false") {
                            consts.entry(id).or_default().push((r, false));
                        } else if let Some((_, rest)) = k.split_once("ir_cvar ") {
                            // `ir_cvar ir_dK` — the AGGREGATE builder,
                            // `IRConst.aggv (ir_cs1 (IRConst.int_ k))`.
                            if let Some(v) = rest
                                .split_whitespace()
                                .next()
                                .and_then(|x| n(x.trim_end_matches(')')))
                            {
                                agg_consts.entry(id).or_default().push((r, v));
                            }
                        } else if let Some((_, rest)) = k.split_once("IRConst.int_ ") {
                            if let Some(v) = rest
                                .split_whitespace()
                                .next()
                                .and_then(|x| n(x.trim_end_matches(')')))
                            {
                                int_consts.entry(id).or_default().push((r, v));
                            }
                        }
                    }
                }
                // `IRInst.assert <c>` — one operand, no result, no target.
                "IRInst.assert" => {
                    assert_eq!(
                        t.len(),
                        2,
                        "the registered assert carries {} operands ({inst}), and this parser \
                         reads exactly one — the scrutinee",
                        t.len().saturating_sub(1)
                    );
                    assert!(
                        results.is_empty(),
                        "the registered assert BINDS a result ({results:?}); Assert is \
                         value-less and the machine advances past it without binding"
                    );
                    if let Some(c) = t.get(1).and_then(|x| n(x)) {
                        asserts.entry(id).or_default().push(c);
                    }
                }
                "IRInst.ret" => {
                    rets.insert(id, numerals_in(t.get(1).map_or("", String::as_str)));
                }
                // `IRInst.br <tgt> <args>`
                "IRInst.br" => {
                    edge_args.insert(id, vec![numerals_in(t.get(2).map_or("", String::as_str))]);
                }
                // `IRInst.condbr <c> <tt> <targs> <et> <eargs>`
                "IRInst.condbr" => {
                    if let (Some(c), Some(tt), Some(et)) = (
                        t.get(1).and_then(|s| n(s)),
                        t.get(2).and_then(|s| n(s)),
                        t.get(4).and_then(|s| n(s)),
                    ) {
                        condbrs.insert(id, (c, tt, et));
                        edge_args.insert(
                            id,
                            vec![
                                numerals_in(t.get(3).map_or("", String::as_str)),
                                numerals_in(t.get(5).map_or("", String::as_str)),
                            ],
                        );
                    }
                }
                _ => {}
            }
        }
    }
    blocks.sort_unstable();
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
        extract_tys,
        loads,
        load_tys,
        geps,
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

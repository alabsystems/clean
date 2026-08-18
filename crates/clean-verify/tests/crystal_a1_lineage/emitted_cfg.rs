// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The CFG shape both sides of the A1 gate are compared in, and the lane
//! comparator that reads it.**
//!
//! Split out of `crystal_a1_lineage.rs` on 2026-08-14, when the sixth and
//! seventh chains took that file to 945 lines against the 500-line convention
//! it had already been flagged against twice. The two parsers moved on again on
//! 2026-08-16 into `emitted_cfg_parse.rs`, for the same reason; this file is the
//! shape, the shared token helpers, and the comparator.
//!
//! Two parsers, one shape. `parse_emitted` reads the trust-ir text trustc
//! emitted; `parse_clean` reads the registered Clean spec sources. The gate is
//! that they produce the same `Cfg`.
//!
//! **Every field of `Cfg` is a lane, and a lane exists because something can
//! differ in it while every other lane stays bit-identical.** That is the whole
//! design rule: `consts` / `int_consts` / `agg_consts` are three lanes and not
//! one because `const bool true`, `const u8 1` and `const enum.13 { 1 }` are
//! different values of different types produced by different evaluators;
//! `condbrs` is a lane because exchanging a conditional branch's targets
//! negates what a body computes and changes nothing else; `icmps` carries its
//! operator AND its operand order because `uge` and `ugt` differ at one input
//! pair and `0xDFFF < n` is not `n < 0xDFFF`.
//!
//! Adding a chain whose body contains a construct with no lane here means
//! adding the lane, not asserting the correspondence.
//!
//! ## The 2026-08-16 lane-completeness audit
//!
//! Every lane above was added by whichever chain needed it, and each time the
//! earlier chains were re-checked by hand. The audit did it systematically —
//! nine chains against every lane, every EMPTY cell justified against the
//! emitted fixture rather than against the parser — and found the lane set
//! **incomplete in five places**, four of them the cast's exact failure mode: a
//! construct present in the bodies that no lane read, so both sides parsed it to
//! nothing and compared equal.
//!
//! * **`const_tys`** — a constant's TYPE and its bound RESULT id. `ir_const_eval`
//!   canonicalizes an integer constant modulo 2^w (`ir_const_eval_int_still_wraps`:
//!   7 at width 2 is 3) and FAULTS a scalar constant at an aggregate type
//!   (`ir_const_eval_int_rejects_agg_ty`). Six chains materialise constants and
//!   none of them compared either fact.
//! * **`edge_args`** — the block ARGUMENTS a `br` or `condbr` passes.
//!   `ir_jump` resolves them and `ir_bind_params` binds them into the target
//!   block's parameters, so they are the entire value flow of a join. Six chains
//!   carry them; a transcription in which every arm passed the FIRST arm's
//!   constant agreed with every lane this file had.
//! * **`block_params`** — the join block's parameter ids. `param_blocks` recorded
//!   only WHICH blocks take one, so the two join parameters of `bvar_in_range`
//!   (`ir_d3` and `ir_d4`) could be exchanged invisibly.
//! * **`switch_on`** — the switch SCRUTINEE. Four chains dispatch on one, and
//!   dispatching on the LOADED value instead of the extracted discriminant
//!   changed no other lane.
//! * **`order`** — the block as a SEQUENCE. Every lane above is per-KIND, so
//!   nothing ordered two different kinds against each other: hoisting
//!   `flat_flags_contains`'s `and` above the extractfields that bind its
//!   operands left six lanes bit-identical and read two bindings that do not
//!   exist yet.
//! * The fifth was not a missing lane but a missing CALL: the seventh chain
//!   compared `consts` on one side only and never against Clean's. That is now
//!   structurally impossible — `assert_lanes` ends in a whole-`Cfg` equality, so
//!   a lane cannot be added to the shape and left uncompared by a chain.

use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;

// The type vocabulary both sides are compared in — split out when the
// eighth chain's three lanes took this file past the size it was split
// at once already.
#[path = "emitted_cfg_types.rs"]
mod emitted_cfg_types;

// The two readers. Split out by the 2026-08-16 audit, for the same reason,
// then split from each other on 2026-08-17 when the four lanes that audit
// added took the pair to 773 lines. Same seam either way: `Cfg` and the
// token helpers live here, a reader lives in its own file.
#[path = "emitted_cfg_parse.rs"]
mod emitted_cfg_parse;
#[path = "emitted_cfg_parse_clean.rs"]
mod emitted_cfg_parse_clean;

pub(crate) use emitted_cfg_parse::parse_emitted;
pub(crate) use emitted_cfg_parse_clean::parse_clean;
use emitted_cfg_types::numerals_in;

pub(crate) fn fixture(name: &str) -> String {
    let p = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures")
        .join(name);
    std::fs::read_to_string(&p).unwrap_or_else(|e| {
        panic!(
            "crystal A1: fixture {} is missing or unreadable ({e}). It is the EMITTED trust-ir \
             this gate exists to check against; without it the gate would pass vacuously, so it \
             fails closed instead.",
            p.display()
        )
    })
}

/// The emitted function's CFG, reduced to the facts a theorem about it depends on.
#[derive(Debug, PartialEq, Eq)]
pub(crate) struct Cfg {
    /// block id -> the ordered `(result, value)` of the BOOLEAN constants it
    /// materializes.
    ///
    /// **De-collapsed from `BTreeMap<u32, bool>` on 2026-08-16 by the TENTH
    /// chain.** It was one value per block, and `assert_lanes` carried a
    /// ratchet that failed closed the moment a body materialized two — which
    /// is exactly what every CTFE assert-carrying body does: `META_TAG`'s one
    /// block materializes THREE integer constants, and the `no_overflow`
    /// shape materializes two integers and two Bools. The ratchet named the
    /// repair ("de-collapse them into per-instruction lanes") and this is it;
    /// the RESULT id travels with the value for the same reason it does in
    /// `const_tys`.
    pub(crate) consts: BTreeMap<u32, Vec<(u32, bool)>>,
    /// block id -> the INTEGER constant it materializes, if any.
    ///
    /// A separate lane from `consts` because a body whose answers are `u8`
    /// (`Level::kind_ord`) shares no constant constructor with one whose
    /// answers are `bool` (`CleanMode::has_cubical_layer`) — in the Clean
    /// semantics they are `IRConst.int_` and `IRConst.bool_`, which route
    /// through different evaluators. Folding them into one map would let a
    /// `const bool true` arm compare equal to a `const u8 1` arm.
    pub(crate) int_consts: BTreeMap<u32, Vec<(u32, u32)>>,
    /// block id -> the discriminant of the AGGREGATE constant it materializes.
    ///
    /// A third lane, kept apart from the other two for the same reason they are
    /// kept apart from each other: `mode::CleanMode::from_source_system` emits
    /// `const enum.13 { k }` — a `trust_ir::Constant::Aggregate`, which is
    /// `IRConst.aggv` on the Clean side and routes through `ir_const_agg_eval`,
    /// not through `ir_const_int_eval`. Folding it into `int_consts` would let
    /// `const u8 4` compare equal to `const enum.13 { 4 }`, which are different
    /// values of different types produced by different evaluators.
    pub(crate) agg_consts: BTreeMap<u32, Vec<(u32, u32)>>,
    /// switch case value -> target block
    pub(crate) cases: BTreeMap<u32, u32>,
    /// the switch's default target
    pub(crate) default: u32,
    /// block id -> branch target
    pub(crate) branches: BTreeMap<u32, u32>,
    /// every non-entry block that takes a block parameter
    pub(crate) param_blocks: BTreeSet<u32>,
    pub(crate) blocks: Vec<u32>,
    /// block id -> the ordered `(result, source, field index)` of its
    /// `extractfield`s.
    ///
    /// A lane of its own because the two chains that COMPUTE read fields more
    /// than once: `flat::types::FlatFlags::contains` emits `extractfield u8 %1,
    /// 0` **twice**, once for the operand of the `and` and once for the operand
    /// of the `icmp`. A transcription that common-subexpression-eliminates the
    /// second one is a shorter body than the shipped artifact, and every lane
    /// that existed before this one would have compared equal anyway.
    ///
    /// The instruction's TYPE is deliberately absent: `eval_ir_machine` steps
    /// `IRInst.extractfield t a k` to `ir_ef_at (ir_getd s a) k`, in which `t`
    /// does not occur. A lane for it would compare something no theorem here
    /// depends on. The same holds for `load`'s type and volatile flag.
    pub(crate) extracts: BTreeMap<u32, Vec<(u32, u32, u32)>>,
    /// block id -> the ordered `(result, pointer operand)` of its `load`s.
    pub(crate) loads: BTreeMap<u32, Vec<(u32, u32)>>,
    /// block id -> the ordered `(op, result, lhs, rhs)` of its `icmp`s.
    ///
    /// The operator is part of the body: `uge` and `ugt` differ at exactly one
    /// input pair, and `expr::bvar_in_range` contains two `icmp uge` with
    /// IDENTICAL operands in two different blocks — so the result id has to be
    /// compared as well, or the two would be indistinguishable.
    pub(crate) icmps: BTreeMap<u32, Vec<(String, u32, u32, u32)>>,
    /// block id -> the ordered `(op, result, lhs, rhs)` of its arithmetic and
    /// bitwise `binop`s.
    pub(crate) binops: BTreeMap<u32, Vec<(String, u32, u32, u32)>>,
    /// block id -> `(condition, then target, else target)` of its `condbr`.
    ///
    /// The lane the first three chains have nothing in: they dispatch with a
    /// `switch`, whose cases were already compared. Swapping a `condbr`'s two
    /// targets inverts the predicate the body computes and changes no other
    /// lane, so without this the CFG gate would be blind to it.
    pub(crate) condbrs: BTreeMap<u32, (u32, u32, u32)>,
    /// block id -> the ordered `(op, result, NORMALIZED TYPE)` of its `binop`s.
    ///
    /// **Added 2026-08-15 by the EIGHTH chain (`reduce_float_div::{closure#0}`),
    /// and it is the lane float arithmetic forced.** The `binops` lane carries a
    /// binop's operator and its operands and drops its TYPE, which was survivable
    /// while every chained arithmetic body was an integer one: `and u8` versus
    /// `and u16` is a different function, but no transcription in this program
    /// had got it wrong. For a float body the type is not a detail — binary32 has
    /// an 8-bit exponent field and binary64 an 11-bit one, so `fdiv f32` and
    /// `fdiv f64` classify the same bit pattern differently and
    /// `ir_float_binop` DECIDES only width 64. A module transcribed at
    /// `IRTy.float_ 32` computes `unmodelled` where the artifact computes a
    /// value, and it agreed with every lane this file had.
    pub(crate) binop_tys: BTreeMap<u32, Vec<(String, u32, String)>>,
    /// block id -> the ordered `(op, result, NORMALIZED TYPE)` of its `icmp`s.
    ///
    /// The same lane for comparisons, added at the same time and for the same
    /// reason — `ir_int_cmp` reads the width off the type and canonicalizes both
    /// operands at it, so `icmp ult u32` and `icmp ult u64` are different
    /// predicates. Three earlier chains carry integer comparisons whose width was
    /// never compared; this closes them too.
    pub(crate) icmp_tys: BTreeMap<u32, Vec<(String, u32, String)>>,
    /// block id -> the ordered `(op, result, operand)` of its `cast`s.
    ///
    /// **Added 2026-08-16 by the NINTH chain
    /// (`get_char_val::{closure#0}`), the first over a CAST.** Until it, a cast
    /// was in no lane at all: `%2 = trunc u64 %1 to u32` produced an empty `Cfg`
    /// on both sides, so a transcription with no cast in it, or with the cast
    /// reading a different SSA id, compared equal to the artifact on every lane
    /// this file had. The operand is carried for the same reason `icmps` carries
    /// its operands — a cast of `%0` and a cast of `%1` are different functions
    /// and differ nowhere else.
    pub(crate) casts: BTreeMap<u32, Vec<(String, u32, u32)>>,
    /// block id -> the ordered `(op, result, NORMALIZED SRC, NORMALIZED DST)` of
    /// its `cast`s.
    ///
    /// **The lane the cast forced, and it is the same hole `binop_tys` closed for
    /// float arithmetic — twice over, because a cast has TWO types.** Both are
    /// semantic input and both are checked, measured against the registered
    /// semantics rather than assumed:
    ///
    /// * DESTINATION: `ir_trunc_int` returns `ir_wrap dw x`, so `trunc u64 -> u32`
    ///   and `trunc u64 -> u8` are different functions on the same operand.
    /// * SOURCE: the guard is `ir_nat_leb dw sw`, so `trunc u8 -> u32` is
    ///   `ir_width_fault` where `trunc u64 -> u32` is a value. The source width
    ///   decides FAULT versus VALUE, which is why it cannot be dropped as
    ///   "the operand's type, already implied".
    ///
    /// Kept apart from `casts` for the design rule this file is built on: a width
    /// change is invisible to the operand lane and an operand change is invisible
    /// to the type lane.
    pub(crate) cast_tys: BTreeMap<u32, Vec<(String, u32, String, String)>>,
    /// block id -> the ordered value ids its `ret` returns.
    ///
    /// **Added 2026-08-15 by the EIGHTH chain, and the more embarrassing of the
    /// two.** Nothing in this file looked at what a body RETURNS. Every chained
    /// module ends in a `ret`, and until now a transcription that returned a
    /// different SSA id — the first argument instead of the computed answer —
    /// agreed with the emitted CFG on every lane: same blocks, same
    /// instructions, same constants, same branch targets. On a body whose entire
    /// content is one `fdiv` and one `ret` that is not a corner case, it is the
    /// whole function.
    pub(crate) rets: BTreeMap<u32, Vec<u32>>,
    /// block id -> the ordered `(result, NORMALIZED TYPE)` of its `const`s.
    ///
    /// **Added 2026-08-16 by the lane-completeness audit.** The three value
    /// lanes above carry a constant's VALUE and nothing else — not its type, not
    /// the SSA id it binds. Both are semantic input, and the registered
    /// semantics say so in executed form:
    ///
    /// * `ir_const_eval_int_still_wraps` — `ir_const_eval ir_u2 (IRConst.int_ 7)`
    ///   is `value (int_ 3)`. An integer constant is canonicalized modulo 2^w, so
    ///   `IRConst.int_ 4294967295` transcribed at `ir_tU8` is 255 and
    ///   `bvar_in_range`'s sentinel comparison decides a different predicate.
    /// * `ir_const_eval_int_rejects_agg_ty` — a scalar constant at an aggregate
    ///   type is `type_error not_int`, not a value.
    ///
    /// The RESULT id travels with it because the four chains whose constants feed
    /// only a block argument (`has_cubical_layer`, `level_kind_ord`,
    /// `from_source_system`, `expr_path_step_clone`) bind an id that appears in
    /// no other compared lane.
    pub(crate) const_tys: BTreeMap<u32, Vec<(u32, String)>>,
    /// block id -> the ordered argument list of each outgoing edge: one list for
    /// a `br`, two (then, else) for a `condbr`.
    ///
    /// **Added 2026-08-16 by the lane-completeness audit, and it is the join's
    /// entire value flow.** `IRInst.br tgt args` steps to `ir_jump m s tgt args`,
    /// which is `ir_jump_func s tgt (ir_resolve s args) …` and ends in
    /// `ir_bind_params ps vs` — the arguments ARE what the join block's parameter
    /// becomes. `branches` compared only the target, so in every switch-shaped
    /// chain a transcription whose twelve arms all passed the FIRST arm's
    /// constant agreed with `blocks`, `cases`, `default`, `branches`,
    /// `param_blocks`, the three constant lanes and `rets` — while computing one
    /// answer for every input.
    ///
    /// A `switch` contributes no entry: `ir_sc` hardwires arm arguments to
    /// `ir_nl0` and both parsers REFUSE a switch that carries any, rather than
    /// dropping them.
    pub(crate) edge_args: BTreeMap<u32, Vec<Vec<u32>>>,
    /// non-entry block id -> the ordered ids of its block parameters.
    ///
    /// **Added 2026-08-16 by the lane-completeness audit.** `param_blocks` is a
    /// SET: it records which blocks take a parameter and neither how many nor
    /// which ids. `ir_bind_params` binds the incoming arguments to exactly these
    /// ids, so `bvar_in_range`'s two join blocks — `ir_d3` in bb3 and `ir_d4` in
    /// bb6 — could be exchanged, or a join could bind an id nothing reads, with
    /// every lane still comparing equal.
    ///
    /// The ENTRY block is excluded on both sides: its emitted parameter list is
    /// the FUNCTION signature, whose Clean-side counterpart lives on `IRFunc`,
    /// not on `IRBlock`. `assert_entry_params` compares that pair.
    pub(crate) block_params: BTreeMap<u32, Vec<u32>>,
    /// block id -> the ordered SCRUTINEE value ids of its `assert`s.
    ///
    /// **Added 2026-08-16 by the TENTH chain
    /// (`tc::local_context::LocalContext::push_low_local::META_TAG`), the first
    /// over a PANIC ARM.** Until it, `Inst::Assert` was in no lane: the
    /// instruction binds no result, carries no type and has no branch target, so
    /// a transcription that DELETED it, or that asserted a different SSA id,
    /// differed from the artifact in nothing this file read. `order` records
    /// that an `assert` is there and where; this records WHAT it asserts, which
    /// is the whole of its semantic content —
    /// `IRInst.assert c => ir_assert_exec s (ir_getd s c)`, and a `false` there
    /// is `IROutcome.ub IRFault.assert_failed`.
    ///
    /// **There is deliberately no lane for the failure TARGET, because trust-ir
    /// has none** — the failing edge is implicit in the semantics, not an
    /// operand. Both parsers REFUSE an assert carrying anything past its
    /// scrutinee rather than dropping it, which is the `?usize` rule: a slot a
    /// parser cannot read must never parse to nothing on both sides.
    pub(crate) asserts: BTreeMap<u32, Vec<u32>>,
    /// the value id the block's `switch` dispatches on, or `u32::MAX`.
    ///
    /// **Added 2026-08-16 by the lane-completeness audit.** `IRInst.switch v …`
    /// steps through `ir_getd s v`, so the scrutinee decides which arm runs. Four
    /// chains dispatch on one and none compared it: each loads a value and
    /// extracts its discriminant, and a transcription that switched on the LOADED
    /// value instead of the extracted tag matched `cases`, `default`, `loads`,
    /// `extracts` and every other lane.
    pub(crate) switch_on: u32,
    /// block id -> the ordered `(instruction class, bound results)` of the WHOLE
    /// block, in program order.
    ///
    /// **Added 2026-08-16 by the lane-completeness audit, and it is the lane
    /// every other lane in this file is structurally unable to be.** All twenty-two
    /// above are per-KIND: `extracts` keeps the extractfields in order,
    /// `binops` keeps the binops in order, and nothing keeps the two ordered
    /// AGAINST EACH OTHER. `flat::types::FlatFlags::contains` is the measured
    /// case — its block is
    ///
    /// ```text
    /// extractfield -> %2 ; extractfield -> %3 ; and %2, %3 -> %4 ;
    /// extractfield -> %5 ; icmp %4, %5 -> %6 ; ret %6
    /// ```
    ///
    /// and hoisting the `and` above the two extractfields leaves `extracts`,
    /// `binops`, `icmps`, `binop_tys`, `icmp_tys` and `rets` **bit-identical**
    /// while the machine reads %2 and %3 through `ir_getd` before anything binds
    /// them. A block is a sequence, not a bag, and until this lane the gate
    /// compared it as a bag.
    ///
    /// The class vocabulary is Clean's `IRInst` constructor names, so `and` and
    /// `fdiv` are both `binop` and `trunc` is `cast` — the operator itself is
    /// already carried, exactly once, by `binops` / `casts`. An instruction with
    /// NO lane still gets a class here, which makes this lane the runtime half of
    /// the parser-totality check in `lane_matrix.rs`.
    ///
    /// **The result slot became a LIST on 2026-08-16 (tenth chain).** It was one
    /// `u32`, read with `unwrap_or(u32::MAX)` — so a node binding two ids
    /// (`%2, %3 = mul.overflow usize %0, %1`, the shape of nine of the crate's
    /// twenty-one assert-carrying CTFE flips) scored `u32::MAX` on the emitted
    /// side and `u32::MAX` on the Clean side and compared equal *whatever ids
    /// either bound*. A value-less instruction is the empty list, which is also
    /// how `assert` and the terminators are distinguished from a node that binds
    /// something — a transcription that gave the `assert` a result id now fails
    /// here.
    pub(crate) order: BTreeMap<u32, Vec<(String, Vec<u32>)>>,
}

/// Split on whitespace at parenthesis depth zero, so a parenthesised argument
/// (`(ir_nl1 ir_d7)`) stays ONE token instead of becoming three.
pub(crate) fn split_top(s: &str) -> Vec<String> {
    let (mut out, mut cur, mut depth) = (Vec::new(), String::new(), 0i32);
    for ch in s.chars() {
        match ch {
            '(' => {
                depth += 1;
                cur.push(ch);
            }
            ')' => {
                depth -= 1;
                cur.push(ch);
            }
            c if c.is_whitespace() && depth == 0 => {
                if !cur.is_empty() {
                    out.push(std::mem::take(&mut cur));
                }
            }
            c => cur.push(c),
        }
    }
    if !cur.is_empty() {
        out.push(cur);
    }
    out
}

/// `%12` / `%12,` / `bb3` -> 12 / 3.
pub(crate) fn id_of(tok: &str) -> Option<u32> {
    tok.trim_end_matches(',')
        .trim_start_matches('%')
        .trim_start_matches("bb")
        .parse::<u32>()
        .ok()
}

/// A branch target and its block arguments: `4(%7, %8),` -> `(4, [7, 8])`;
/// `4,` -> `(4, [])`.
///
/// The `bb` prefix is optional, because `parse_emitted` reaches `br` through
/// `strip_prefix("br bb")` and `condbr` through whole tokens (`bb1(%7),`).
/// Splitting the argument group off BEFORE parsing the id is the point: an
/// unadorned `id_of` returns `None` on `bb1(%7),`, which would have dropped a
/// `condbr` out of its own lane the first time the lowerer emitted one with
/// arguments.
pub(crate) fn target_and_args(tok: &str) -> Option<(u32, Vec<u32>)> {
    let t = tok.trim().trim_end_matches(',');
    let (head, rest) = t.split_once('(').map_or((t, None), |(h, r)| (h, Some(r)));
    let target = id_of(head)?;
    let args = rest
        .and_then(|r| r.rsplit_once(')'))
        .map(|(inner, _)| {
            split_commas_top(inner)
                .iter()
                .filter_map(|a| id_of(a))
                .collect()
        })
        .unwrap_or_default();
    Some((target, args))
}

/// Split on commas at parenthesis depth zero, so `%0: (), %1: u64` is two
/// entries and a parenthesised type never splits a parameter in half.
pub(crate) fn split_commas_top(s: &str) -> Vec<String> {
    let (mut out, mut cur, mut depth) = (Vec::new(), String::new(), 0i32);
    for ch in s.chars() {
        match ch {
            '(' => {
                depth += 1;
                cur.push(ch);
            }
            ')' => {
                depth -= 1;
                cur.push(ch);
            }
            ',' if depth == 0 => out.push(std::mem::take(&mut cur)),
            c => cur.push(c),
        }
    }
    if !cur.trim().is_empty() {
        out.push(cur);
    }
    out
}

/// The parameter ids in an emitted block header: `bb4(%1: bool):` -> `[1]`,
/// `bb0(%0: (), %1: u64):` -> `[0, 1]`, `bb3:` -> `[]`.
pub(crate) fn header_param_ids(line: &str) -> Vec<u32> {
    line.split_once('(')
        .and_then(|(_, r)| r.rsplit_once(')'))
        .map(|(inner, _)| {
            split_commas_top(inner)
                .iter()
                .filter_map(|p| id_of(p.split(':').next().unwrap_or("").trim()))
                .collect()
        })
        .unwrap_or_default()
}

/// **The FUNCTION signature, which is not in `Cfg` and had no gate on seven of
/// the nine chains.**
///
/// The emitted entry block's parameter list is the function's parameters;
/// Clean's `IRBlock.mk ir_d0 ir_nl0 …` carries none, because the Clean-side
/// counterpart is `IRFunc.mk <id> <params> <entry> <blocks>`. So `block_params`
/// cannot compare them and deliberately excludes the entry block — this does,
/// against the registered `IRFunc`.
///
/// `ir_bind_params (ir_func_params f) vs` is how a call binds arguments, so a
/// module whose function declares the wrong parameter ids reads its inputs from
/// bindings that do not exist. Two chains asserted their `IRFunc` by hand, in
/// two different ad-hoc shapes; the other seven asserted nothing.
pub(crate) fn assert_entry_params(text: &str, func_src: &str, who: &str) {
    let header = text
        .lines()
        .map(str::trim)
        .find(|l| l.starts_with("bb"))
        .unwrap_or_else(|| panic!("{who}: the emitted body declares no block at all"));
    let emitted_params = header_param_ids(header);
    let emitted_entry = header
        .trim_start_matches("bb")
        .split_once([':', '('])
        .and_then(|(num, _)| num.parse::<u32>().ok())
        .unwrap_or_else(|| panic!("{who}: unreadable entry block header {header:?}"));

    let after = func_src
        .split_once("IRFunc.mk")
        .map(|(_, r)| r)
        .unwrap_or_else(|| panic!("{who}: the registered IRFunc source has no `IRFunc.mk`"));
    let top = split_top(after);
    let clean_params = numerals_in(top.get(1).map_or("", String::as_str));
    let clean_entry = top
        .get(2)
        .and_then(|t| t.trim().trim_start_matches("ir_d").parse::<u32>().ok())
        .unwrap_or_else(|| panic!("{who}: the registered IRFunc has no entry block id"));

    assert_eq!(
        emitted_params, clean_params,
        "{who}: FUNCTION PARAMETER ids differ: emitted entry header {header:?} binds {:?}, the \
         registered IRFunc binds {:?}. `ir_bind_params (ir_func_params f) vs` binds a call's \
         arguments to exactly these ids, so a module that declares different ones reads its \
         inputs from bindings that were never made.",
        emitted_params, clean_params
    );
    assert_eq!(
        emitted_entry, clean_entry,
        "{who}: ENTRY BLOCK differs: the emitted body starts at bb{emitted_entry}, the registered \
         IRFunc names bb{clean_entry} — the block execution actually begins in."
    );
}

/// The registered spec sources for one chain's blocks, in one string.
///
/// `file` is the `core_spec` module and `const_prefix` the shared name of its
/// block constants (`const SRC_IR_H2_B…`, `def ir_lz_b…`).
pub(crate) fn clean_block_sources(file: &str, const_prefix: &str) -> String {
    let p = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("src/spec/core_spec")
        .join(file);
    let src = std::fs::read_to_string(&p)
        .unwrap_or_else(|e| panic!("{} must be readable ({e})", p.display()));
    src.lines()
        .filter(|l| l.trim_start().starts_with(const_prefix))
        .map(|l| l.trim_start().to_string())
        .collect::<Vec<_>>()
        .join("\n")
}

/// The instruction lanes, asserted for every chain in one place.
///
/// Added when the first two COMPUTING bodies were chained
/// (`flat::types::FlatFlags::contains`, `expr::bvar_in_range`). The three
/// pre-existing chains dispatch on a discriminant and materialise constants, so
/// their `icmps` / `binops` / `condbrs` are empty on both sides — but their
/// `loads` and `extracts` are not, and those had never been compared at all:
/// before this, a transcription that read field 1 instead of field 0, or
/// loaded a different SSA id, agreed with every lane the gate had.
///
/// **It ends in a whole-`Cfg` equality, and that is not decoration.** The
/// 2026-08-16 audit found the seventh chain comparing `consts` on the emitted
/// side only — it asserted `emitted.consts.is_empty()` and never against
/// Clean's, so a Clean-side `IRConst.bool_` in `ir_ep_*` was invisible. Named
/// per-lane assertions give a readable failure; the final equality is what makes
/// the set of them TOTAL, for every chain and for every lane added later.
pub(crate) fn assert_lanes(emitted: &Cfg, clean: &Cfg, who: &str) {
    assert_eq!(
        emitted.loads, clean.loads,
        "{who}: LOAD lane differs: emitted {:?} vs Clean {:?}. Each entry is (result id, pointer \
         operand); a load bound to a different SSA id feeds the rest of the block a different \
         value.",
        emitted.loads, clean.loads
    );
    assert_eq!(
        emitted.extracts, clean.extracts,
        "{who}: EXTRACTFIELD lane differs: emitted {:?} vs Clean {:?}. Each entry is (result, \
         source, field index) IN EMISSION ORDER, so a dropped duplicate read or a field index \
         off by one fails here.",
        emitted.extracts, clean.extracts
    );
    assert_eq!(
        emitted.icmps, clean.icmps,
        "{who}: ICMP lane differs: emitted {:?} vs Clean {:?}. Each entry is (op, result, lhs, \
         rhs); `uge` and `ugt` differ at exactly one input pair, and swapping lhs/rhs turns one \
         into the other.",
        emitted.icmps, clean.icmps
    );
    assert_eq!(
        emitted.binops, clean.binops,
        "{who}: BINOP lane differs: emitted {:?} vs Clean {:?}. `and` and `or` are the same \
         shape and a different function.",
        emitted.binops, clean.binops
    );
    assert_eq!(
        emitted.condbrs, clean.condbrs,
        "{who}: CONDBR lane differs: emitted {:?} vs Clean {:?}. Each entry is (condition, then \
         target, else target); exchanging the two targets negates the predicate the body \
         computes and changes no other lane.",
        emitted.condbrs, clean.condbrs
    );
    assert_eq!(
        emitted.binop_tys, clean.binop_tys,
        "{who}: BINOP TYPE lane differs: emitted {:?} vs Clean {:?}. The type on an arithmetic \
         instruction is SEMANTIC INPUT, not decoration — `ir_int2_wrap` reads the width off it \
         and canonicalizes modulo 2^w, and `ir_float_binop` decides only binary64. `fdiv f32` \
         and `fdiv f64` are different operations and differ in NO other lane here.",
        emitted.binop_tys, clean.binop_tys
    );
    assert_eq!(
        emitted.icmp_tys, clean.icmp_tys,
        "{who}: ICMP TYPE lane differs: emitted {:?} vs Clean {:?}. `ir_int_cmp` reads the width \
         off the type and canonicalizes BOTH operands at it, so a comparison transcribed at the \
         wrong width decides a different predicate on the same operands.",
        emitted.icmp_tys, clean.icmp_tys
    );
    assert_eq!(
        emitted.rets, clean.rets,
        "{who}: RET lane differs: emitted {:?} vs Clean {:?}. Each entry is the ordered value \
         ids a block returns. Returning a different SSA id — an argument instead of the computed \
         answer — is a different function and, before this lane existed, agreed with every other \
         lane in this file.",
        emitted.rets, clean.rets
    );
    assert_eq!(
        emitted.casts, clean.casts,
        "{who}: CAST lane differs: emitted {:?} vs Clean {:?}. Each entry is (op, result, \
         operand). `zext` and `trunc` are the same shape and opposite operations — one embeds, \
         the other DISCARDS the high bits — and before this lane existed a body whose whole \
         content is a cast produced an EMPTY Cfg on both sides.",
        emitted.casts, clean.casts
    );
    assert_eq!(
        emitted.cast_tys, clean.cast_tys,
        "{who}: CAST TYPE lane differs: emitted {:?} vs Clean {:?}. Each entry is (op, result, \
         SOURCE, DESTINATION) and BOTH types are semantic input: `ir_trunc_int` returns \
         `ir_wrap dw x` so the destination decides which residue, and its guard is \
         `ir_nat_leb dw sw` so the source decides FAULT versus VALUE. Neither is implied by the \
         operand.",
        emitted.cast_tys, clean.cast_tys
    );
    assert_eq!(
        emitted.const_tys, clean.const_tys,
        "{who}: CONST TYPE lane differs: emitted {:?} vs Clean {:?}. Each entry is (result, \
         type). `ir_const_eval` canonicalizes an integer constant MODULO 2^w — 7 at width 2 is 3 \
         — and FAULTS a scalar constant at an aggregate type, so a constant transcribed at the \
         wrong type is a different value or no value at all, while the three value lanes compare \
         equal.",
        emitted.const_tys, clean.const_tys
    );
    assert_eq!(
        emitted.edge_args, clean.edge_args,
        "{who}: EDGE ARGUMENT lane differs: emitted {:?} vs Clean {:?}. Each entry is the \
         ordered argument list of each outgoing edge. `ir_jump` resolves them and \
         `ir_bind_params` binds them to the target's parameters, so these ARE the value a join \
         block receives: a set of arms that all pass the FIRST arm's constant branches to the \
         same targets, materializes the same constants, and computes one answer for every input.",
        emitted.edge_args, clean.edge_args
    );
    assert_eq!(
        emitted.block_params, clean.block_params,
        "{who}: BLOCK PARAMETER lane differs: emitted {:?} vs Clean {:?}. `param_blocks` records \
         only WHICH blocks take a parameter; `ir_bind_params` binds the incoming arguments to \
         exactly THESE ids, so two join blocks whose parameters are exchanged agree on every \
         other lane.",
        emitted.block_params, clean.block_params
    );
    assert_eq!(
        emitted.asserts, clean.asserts,
        "{who}: ASSERT lane differs: emitted {:?} vs Clean {:?}. Each entry is the ordered \
         SCRUTINEE value id of a block's asserts. `IRInst.assert c` steps to `ir_assert_exec s \
         (ir_getd s c)`, whose `false` arm is `IROutcome.ub IRFault.assert_failed` — the panic \
         arm. The instruction binds no result and carries no type, so before this lane existed a \
         transcription that asserted a DIFFERENT SSA id (one that happens to be `true`) differed \
         from the artifact in nothing this file read.",
        emitted.asserts, clean.asserts
    );
    assert_eq!(
        emitted.switch_on, clean.switch_on,
        "{who}: SWITCH SCRUTINEE lane differs: emitted %{} vs Clean %{}. `IRInst.switch v …` \
         steps through `ir_getd s v`, so dispatching on the LOADED value instead of the \
         extracted discriminant selects a different arm while `cases`, `default`, `loads` and \
         `extracts` all compare equal.",
        emitted.switch_on, clean.switch_on
    );
    assert_eq!(
        emitted.order, clean.order,
        "{who}: PROGRAM ORDER lane differs: emitted {:?} vs Clean {:?}. Each entry is the ordered \
         (instruction class, bound result) of a whole block. Every other lane here is per-KIND, \
         so the INTERLEAVING of kinds is compared by this one alone: hoisting a `binop` above the \
         `extractfield`s that bind its operands leaves every operand and type lane bit-identical \
         and reads two bindings that do not exist yet.",
        emitted.order, clean.order
    );
    // Casts are the only lane whose EMITTED side is checked for resolution too.
    // `usize` normalizes to `?usize` — deliberately, since resolving it to a
    // width is a target assumption — so a later chain over one of the two `zext
    // u32 -> usize` bodies fails here loudly instead of comparing an unresolved
    // token against a resolved one and reporting a lane difference nobody can
    // read.
    for (side, m) in [("emitted", &emitted.cast_tys), ("Clean", &clean.cast_tys)] {
        for (b, tys) in m {
            for (op, r, src, dst) in tys {
                assert!(
                    !src.starts_with('?') && !dst.starts_with('?'),
                    "{who}: bb{b} {side}-side cast {op} -> %{r} has an UNRESOLVED type \
                     ({src:?} -> {dst:?}). Two unresolved tokens compare equal, which is the \
                     silent-no-op mode this lane exists to close."
                );
            }
        }
    }
    for (b, tys) in &clean.binop_tys {
        for (op, r, ty) in tys {
            assert!(
                !ty.starts_with('?'),
                "{who}: bb{b} binop {op} -> %{r} has an UNRESOLVED Clean-side type {ty:?}. An \
                 unresolved type would compare equal to another unresolved one, which is the \
                 silent-no-op mode this lane exists to close."
            );
        }
    }
    for (b, tys) in &clean.icmp_tys {
        for (op, r, ty) in tys {
            assert!(
                !ty.starts_with('?'),
                "{who}: bb{b} icmp {op} -> %{r} has an UNRESOLVED Clean-side type {ty:?}."
            );
        }
    }
    // The same resolution rule for the new type lane, on BOTH sides — a `?`
    // token here would compare equal to another `?` token and reintroduce
    // exactly what the lane was added to close.
    for (side, m) in [("emitted", &emitted.const_tys), ("Clean", &clean.const_tys)] {
        for (b, tys) in m {
            for (r, ty) in tys {
                assert!(
                    !ty.starts_with('?'),
                    "{who}: bb{b} {side}-side const -> %{r} has an UNRESOLVED type {ty:?}."
                );
            }
        }
    }
    // NO CONSTANT IS DROPPED — the replacement for the one-constant-per-block
    // ratchet, and strictly stronger than it.
    //
    // Until 2026-08-16 the three VALUE lanes were `BTreeMap<u32, V>`: one
    // constant per block, so a block materializing two kept only one and the
    // other's value was never compared. The ratchet that stood here refused such
    // a body outright and named the repair — de-collapse into per-instruction
    // lanes — which the tenth chain had to do, because EVERY assert-carrying
    // CTFE flip in the crate materializes three or four constants in one block.
    //
    // The lanes are now per-instruction, so the ratchet's premise is gone; what
    // replaces it checks the property the ratchet was protecting DIRECTLY. Every
    // `const` node in the program-order lane binds exactly one result, and that
    // result must appear in exactly one of the three value lanes at the same
    // block. A constant this file cannot read therefore FAILS rather than
    // silently contributing nothing to either side — the `?usize` rule, applied
    // to values instead of types.
    for (side, cfg) in [("emitted", emitted), ("Clean", clean)] {
        for (b, seq) in &cfg.order {
            let seen: BTreeSet<u32> = cfg
                .consts
                .get(b)
                .into_iter()
                .flatten()
                .map(|(r, _)| *r)
                .chain(cfg.int_consts.get(b).into_iter().flatten().map(|(r, _)| *r))
                .chain(cfg.agg_consts.get(b).into_iter().flatten().map(|(r, _)| *r))
                .collect();
            for (class, results) in seq {
                if class != "const_" && class != "const" {
                    continue;
                }
                assert_eq!(
                    results.len(),
                    1,
                    "{who}: bb{b} {side}-side const binds {results:?} — a constant binds exactly \
                     one result"
                );
                assert!(
                    seen.contains(&results[0]),
                    "{who}: bb{b} {side}-side const -> %{} is in NO value lane ({:?} / {:?} / \
                     {:?}). Its value is therefore compared by nothing, which is the \
                     silent-agreement mode the three value lanes exist to close. Extend the \
                     parser for the constant's shape; do not leave it unread.",
                    results[0],
                    cfg.consts.get(b),
                    cfg.int_consts.get(b),
                    cfg.agg_consts.get(b)
                );
            }
        }
    }
    // TOTALITY. Every lane above is compared by name for a readable failure;
    // this is what guarantees the list is COMPLETE. A field added to `Cfg` and
    // forgotten here, or a chain that hand-writes its own lane list and omits
    // one, fails on this line instead of passing blind — which is exactly what
    // happened to `expr_path_step_clone`'s `consts` until 2026-08-16.
    assert_eq!(
        emitted, clean,
        "{who}: the two CFGs differ in a lane this call did not name. Either the lane was added \
         to `Cfg` and not to `assert_lanes` — add the named assertion, do not delete this one — \
         or the chain compares it AFTER calling `assert_lanes`, in which case this fired first \
         and did its job."
    );
}

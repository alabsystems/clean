// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The emitted side's program-order CLASSIFIER, and the SSA ids a line
//! binds.**
//!
//! Split out of `emitted_cfg_parse.rs` on 2026-09-10, when the `ir_lzc` chain
//! (the first module with a global) added the rename table below and took that
//! file past the repo's 500-line convention it had already been split at three
//! times. Nothing about the shape changed in the move.

use super::{id_of, split_commas_top, split_top, ARITH, CASTS};

/// The mnemonics whose PRINTED spelling carries a separator the Clean
/// constructor does not, as `(emitted, Clean)`.
///
/// The order lane compares CLEAN class names — see the doc on
/// [`emitted_class`] — so a spelling difference between `trust-ir`'s printer
/// and the `IRInst` constructor is a rename, not a lane difference, and it has
/// to be stated ONCE rather than discovered per chain. `trust-ir/src/display.rs`
/// prints `global_addr` and `ptr_from_parts`; the registered constructors are
/// `IRInst.globaladdr` and `IRInst.ptrfromparts` (`crates/clean-verify`'s
/// `parse_clean` records them generically, by stripping `IRInst.`).
///
/// **What is deliberately NOT here, and why the list is short.** `ptr_data`
/// and `ptr_metadata` print with the same underscore and are OUTSIDE reader
/// B's fragment (`src/ir_mint/emitted_inst.rs` refuses them), so a body using
/// one must FAIL this comparator rather than compare: mapping them would let a
/// chain the minter cannot read produce two equal order lanes. Adding a row
/// here is therefore a claim that the Clean side has a constructor for it.
///
/// **The invariant, enforced rather than promised** — a row may only delete
/// separators: `rhs == lhs.replace('_', "")`, checked by
/// [`class_renames_are_spelling_only`]. That is what stops the hazard the
/// paragraph above names from being a typo away: `ptr_data` normalises to
/// `ptrdata`, so a row mapping it onto the EXISTING constructor
/// `ptrfromparts` is refused by the test rather than silently comparing two
/// different instructions as equal. It also keeps the table from becoming a
/// place where a lane difference can be hidden as a spelling one.
const CLASS_RENAMES: &[(&str, &str)] = &[
    ("global_addr", "globaladdr"),
    ("ptr_from_parts", "ptrfromparts"),
];

/// Every rename is SPELLING-ONLY: the Clean constructor is the emitted
/// mnemonic with its separators removed, and nothing else.
///
/// Lives beside the table because the table is what it guards, and runs in
/// every test binary that reads this parser.
#[test]
fn class_renames_are_spelling_only() {
    for (emitted, clean) in CLASS_RENAMES {
        assert_eq!(
            emitted.replace('_', ""),
            *clean,
            "`{emitted}` -> `{clean}` is not a respelling: a rename row may only delete \
             separators. Mapping a mnemonic onto a DIFFERENT constructor makes two unequal \
             instructions compare equal in the order lane"
        );
        assert_ne!(
            emitted, clean,
            "`{emitted}` needs no rename: a row that changes nothing is dead weight in the \
             table"
        );
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
pub(super) fn emitted_class(line: &str) -> Option<(String, Vec<u32>)> {
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
    } else if let Some((_, clean)) = CLASS_RENAMES.iter().find(|(e, _)| *e == head) {
        (*clean).to_string()
    } else if head == "volatile" {
        // `volatile` is a FLAG, printed as a prefix on `load` (value position)
        // and on `store` (statement position); the class is the instruction it
        // prefixes. Reading the flag as an opcode would put a class the Clean
        // vocabulary has no constructor for into the program-order lane — and
        // hardwiring `load`, as this arm did until 2026-08-20, would have
        // called a volatile store a load. (A volatile store is then REFUSED by
        // `emitted_store`; this arm only keeps the order lane honest about
        // what it saw before that refusal fires.)
        let after = line.split_once(" = ").map_or(line, |(_, r)| r);
        after
            .split_whitespace()
            .nth(1)
            .unwrap_or("volatile")
            .to_string()
    } else {
        head
    };
    Some((class, rs))
}

/// The SSA ids an emitted assignment's left-hand side binds: `%2` -> `[2]`,
/// `%2, %3` -> `[2, 3]`.
///
/// **A list since 2026-08-16.** `mul.overflow` binds two — the wrapped product
/// and the overflow flag — and it is the shape of nine of the crate's
/// twenty-one assert-carrying CTFE flips. A bare `id_of("%2, %3")` returns
/// `None`, which dropped the instruction out of EVERY lane including `order`.
pub(super) fn emitted_results(lhs: &str) -> Vec<u32> {
    split_commas_top(lhs)
        .iter()
        .filter_map(|t| id_of(t.trim()))
        .collect()
}

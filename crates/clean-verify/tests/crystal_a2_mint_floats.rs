// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Crystal A2 — the MINT gate for the FLOAT family
//! (`reduce_float_add/sub/mul/div::{closure#0}`).**
//!
//! Same three readers and the same questions as `crystal_a2_mint.rs`; read
//! that file's header and `src/ir_mint/mod.rs` for what this establishes and
//! what it does not. One test binary for the tranche rather than one per chain
//! because the three bodies are ONE shape with one token changed — a shared
//! table makes the per-chain denominators explicit, and the pairwise
//! discrimination check at the bottom is only meaningful over the set.
//!
//! **What is new here:**
//!
//! * The unwitnessed ledger is EMPTY — the first minted chains without a
//!   `switch`, so the one field trust-ir's `Display` never prints does not
//!   occur, and M2 compares reader A against reader B EXACTLY, with no mask.
//! * The tag tables' aggregate lanes are all measured EMPTY (`f64` is a
//!   machine type, not a crate table entry), so the load-bearing half of each
//!   table is the INTERFACE: the `f64` parameter rows separate each body from
//!   an `f32` twin that projects to the same core module.
//! * The three minted scripts differ pairwise in exactly the binop mnemonic,
//!   and `m8_the_mint_discriminates_the_operator` measures that the mint
//!   DISCRIMINATES the three — the sharpest possible mutation for this shape.
//!
//! The migration off the hand transcriptions (2026-08-21) found NO semantic
//! divergence for any of the three. Two notation-level divergences, printed
//! here because the migration rule is that a divergence is a FINDING:
//!
//! ```text
//! hand:   IRInst.binop IRBinOp.fadd ir_fa_tf64 ir_d1 ir_d2      (alias)
//! minted: IRInst.binop IRBinOp.fadd (IRTy.float_ 64) ir_d1 ir_d2
//! hand:   IRFunc.mk ir_d0 (ir_nl3 ir_d0 ir_d1 ir_d2) ir_d0
//! minted: IRFunc.mk ir_d0 (IRList.cons Nat ir_d0 (IRList.cons Nat ir_d1
//!             (IRList.cons Nat ir_d2 (IRList.nil Nat)))) ir_d0
//! ```
//!
//! Both are definitionally equal to the hand forms (`ir_fa_tf64` unfolds to
//! `IRTy.float_ 64`; `ir_nl3 a b c` unfolds to that cons spine), so every
//! downstream theorem kept proving unchanged.

use clean_verify::ir_mint::{self, Sx};

#[allow(dead_code)]
use crate::emitted_cfg;

use emitted_cfg::{assert_lanes, parse_clean, parse_emitted};

/// One minted float chain: its committed artifacts and its identity facts.
struct Chain {
    prefix: &'static str,
    op: &'static str,
    fixture: &'static str,
    core: &'static str,
    defs: &'static str,
    record: &'static str,
    tags: &'static str,
}

const CHAINS: &[Chain] = &[
    Chain {
        prefix: "ir_fa",
        op: "fadd",
        fixture: include_str!("fixtures/float_add.trust-ir.txt"),
        core: ir_mint::IR_FA_CORE,
        defs: ir_mint::IR_FA_DEFS,
        record: ir_mint::IR_FA_RECORD,
        tags: ir_mint::IR_FA_TAGS,
    },
    Chain {
        prefix: "ir_fs2",
        op: "fsub",
        fixture: include_str!("fixtures/float_sub.trust-ir.txt"),
        core: ir_mint::IR_FS2_CORE,
        defs: ir_mint::IR_FS2_DEFS,
        record: ir_mint::IR_FS2_RECORD,
        tags: ir_mint::IR_FS2_TAGS,
    },
    Chain {
        prefix: "ir_fm",
        op: "fmul",
        fixture: include_str!("fixtures/float_mul.trust-ir.txt"),
        core: ir_mint::IR_FM_CORE,
        defs: ir_mint::IR_FM_DEFS,
        record: ir_mint::IR_FM_RECORD,
        tags: ir_mint::IR_FM_TAGS,
    },
    Chain {
        prefix: "ir_fd",
        op: "fdiv",
        fixture: include_str!("fixtures/float_div.trust-ir.txt"),
        core: ir_mint::IR_FD_CORE,
        defs: ir_mint::IR_FD_DEFS,
        record: ir_mint::IR_FD_RECORD,
        tags: ir_mint::IR_FD_TAGS,
    },
];

impl Chain {
    fn tags(&self) -> ir_mint::Tags {
        ir_mint::tags::parse(self.tags)
            .unwrap_or_else(|e| panic!("{}: the committed tag table must parse: {e}", self.prefix))
    }

    fn core_a(&self) -> Sx {
        ir_mint::parse(self.core).unwrap_or_else(|e| {
            panic!("{}: the committed core module must parse: {e}", self.prefix)
        })
    }

    fn core_b(&self) -> Sx {
        ir_mint::read_emitted(self.fixture).unwrap_or_else(|e| {
            panic!(
                "{}: reader B must read the committed emitted trust-ir: {e}",
                self.prefix
            )
        })
    }
}

fn canon(sx: &Sx) -> String {
    ir_mint::print(sx).expect("a core module must print")
}

// ────────────────────────────────────────────────────────────────────────────
// M1 — each committed core is canonical, and it is the one-binop body.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m1_committed_cores_round_trip_their_printer() {
    for c in CHAINS {
        assert_eq!(
            canon(&c.core_a()),
            c.core,
            "{}: the committed core module is not what its own canonical printer produces",
            c.prefix
        );
        // COVERAGE DENOMINATOR: two empty modules round-trip too.
        assert!(
            c.core.contains(&format!("(binop {} (float 64) 1 2)", c.op)),
            "{}: the committed core must carry the one {} this chain exists for:\n{}",
            c.prefix,
            c.op,
            c.core
        );
        assert!(
            c.core.contains("(ret (vals 3))"),
            "{}: and the ret of ITS RESULT, not an operand:\n{}",
            c.prefix,
            c.core
        );
        for absent in ["(call ", "(switch ", "(load ", "(store "] {
            assert!(
                !c.core.contains(absent),
                "{}: this body has no `{absent}`; a core module with one is not it",
                c.prefix
            );
        }
    }
}

// ────────────────────────────────────────────────────────────────────────────
// M2 — reader B (the emitted TEXT) equals reader A (the artifact BINARY),
// EXACTLY: the unwitnessed ledger is EMPTY on these bodies.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m2_reader_b_equals_reader_a_with_an_empty_ledger() {
    for c in CHAINS {
        let (masked, ledger) = ir_mint::mask_text_unwitnessed(&c.core_a())
            .unwrap_or_else(|e| panic!("{}: reader A's module must mask: {e}", c.prefix));
        assert_eq!(
            canon(&masked),
            canon(&c.core_b()),
            "{}: the artifact BINARY (reader A) and the emitted TEXT (reader B) disagree",
            c.prefix
        );
        assert!(
            ledger.is_empty(),
            "{}: no `switch` means no slot the text cannot show — the first EXACT M2 in the \
             tree. A non-empty ledger here means the body stopped being the one-binop shape: \
             {ledger:?}",
            c.prefix
        );
    }
}

// ────────────────────────────────────────────────────────────────────────────
// M3 — `mint` of each committed core IS the committed, registered script.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m3_mint_reproduces_the_registered_scripts() {
    for c in CHAINS {
        let minted = ir_mint::mint(&c.core_a(), c.prefix, &c.tags())
            .unwrap_or_else(|e| panic!("{}: mint: {e}", c.prefix))
            .text();
        assert_eq!(
            minted, c.defs,
            "{}: the committed definition script is not what `mint` produces from the committed \
             core module. The committed script is the one the spec stage REGISTERS, so a \
             difference here means the proved module is again hand-edited.",
            c.prefix
        );
        assert!(
            c.record.contains(&ir_mint::digest(&minted)),
            "{}: the mint record's defs digest does not match the minted script",
            c.prefix
        );
        assert!(
            c.record.contains(&ir_mint::digest(c.core)),
            "{}: the mint record's core digest does not match the committed core module",
            c.prefix
        );
        // No aggregate, no alias: the script's first line is the entry block.
        assert!(
            minted.starts_with(&format!("def {}_b0 : IRBlock", c.prefix)),
            "{}: an aggregate alias appeared in a chain whose aggregate lanes are measured \
             empty:\n{minted}",
            c.prefix
        );
    }
}

// ────────────────────────────────────────────────────────────────────────────
// M5 — the A1 lane comparator, unchanged, over the MINTED script.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m5_the_a1_comparator_agrees_over_the_minted_scripts() {
    for c in CHAINS {
        let emitted = parse_emitted(c.fixture);
        let clean = parse_clean(c.defs, &format!("def {}_b", c.prefix));
        assert_lanes(&emitted, &clean, &format!("{} (minted)", c.prefix));
        assert_eq!(emitted.blocks, clean.blocks);
        assert!(
            !emitted.binops.is_empty(),
            "coverage denominator: two empty binop lanes compare equal, and this body has one"
        );
        assert_eq!(emitted.binops, clean.binops);
        assert_eq!(emitted.binop_tys, clean.binop_tys);
        assert_eq!(emitted.rets, clean.rets);
    }
}

// ────────────────────────────────────────────────────────────────────────────
// M10 — each committed fixture projects under its pinned interface.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m10_the_committed_fixtures_project_under_their_pinned_interfaces() {
    for c in CHAINS {
        let t = c.tags();
        let p = ir_mint::project(c.fixture, &t)
            .unwrap_or_else(|e| panic!("{}: the committed fixture must project: {e}", c.prefix));
        assert_eq!(
            canon(&p.core),
            c.core,
            "{}: projecting under the interface pin must produce the committed core",
            c.prefix
        );
        let tys: Vec<&str> = p.interface.params.iter().map(|s| s.ty.as_str()).collect();
        assert_eq!(
            tys,
            ["ptr", "f64", "f64"],
            "{}: the parameter-type lane is the load-bearing half of this chain's table",
            c.prefix
        );
        assert!(
            p.interface.block_params.is_empty() && p.interface.aligns.is_empty(),
            "{}: no join block and no memory instruction — measured, not assumed",
            c.prefix
        );
    }
}

/// The interface pin DISCRIMINATES: an `f32` twin, a foreign calling
/// convention and a moved `functy` are each refused, and the refusal names the
/// slot. The core module alone separates NONE of the first two — that is what
/// the blind-slot list records and why the pin exists.
#[test]
fn m10_the_interface_pins_bite() {
    for c in CHAINS {
        let t = c.tags();
        for (from, to, slot) in [
            ("%1: f64", "%1: f32", "parameter"),
            ("rustcc fn @", "ccc fn @", "calling convention"),
            ("(functy.363)", "(functy.364)", "functy"),
        ] {
            let mutated = c.fixture.replace(from, to);
            assert_ne!(mutated, c.fixture, "{}: the mutation must bite", c.prefix);
            let e = ir_mint::project(&mutated, &t).map(|_| ()).expect_err(
                "a body whose interface is not the pinned one must be REFUSED, never accepted",
            );
            assert!(
                format!("{e}").contains(slot) || format!("{e:?}").contains("Mismatch"),
                "{}: the refusal must name the drifted slot ({slot}): {e}",
                c.prefix
            );
        }
    }
}

// ────────────────────────────────────────────────────────────────────────────
// M8 — the mint DISCRIMINATES the operator across the tranche.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m8_the_mint_discriminates_the_operator() {
    // Pairwise: three bodies, one token apart, three distinct core digests and
    // three distinct minted scripts.
    for (i, a) in CHAINS.iter().enumerate() {
        for b in &CHAINS[i + 1..] {
            assert_ne!(
                ir_mint::digest(a.core),
                ir_mint::digest(b.core),
                "{} and {} must not share a core digest",
                a.prefix,
                b.prefix
            );
            assert_ne!(a.defs, b.defs);
        }
    }
    // …and the registered ops are exactly the ones each chain claims.
    for c in CHAINS {
        let want = format!("IRBinOp.{}", c.op);
        assert!(
            c.defs.contains(&want),
            "{}: the minted script must carry {want}",
            c.prefix
        );
        for other in CHAINS.iter().filter(|o| o.prefix != c.prefix) {
            assert!(
                !c.defs.contains(&format!("IRBinOp.{}", other.op)),
                "{}: the minted script must not carry {}'s operator",
                c.prefix,
                other.prefix
            );
        }
    }
}

// ────────────────────────────────────────────────────────────────────────────
// M4 — reader C: each ELABORATED KERNEL TERM decodes back to its committed
// core. The expensive check (one full Specification build), LAST.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m4_the_registered_kernel_terms_decode_to_the_committed_cores() {
    let spec = clean_verify::test_utils::shared_spec();
    for c in CHAINS {
        let module_const = format!("{}_module", c.prefix);
        let decoded = ir_mint::decode(spec.env(), &module_const, &c.tags())
            .unwrap_or_else(|e| panic!("decode {module_const}: {e}"));
        assert_eq!(
            canon(&decoded),
            c.core,
            "the ELABORATED term registered under `{module_const}` does not decode to the \
             committed core module. This is the check that keeps `mint` out of the trusted \
             base: reader C never sees the minter's output."
        );
    }
}

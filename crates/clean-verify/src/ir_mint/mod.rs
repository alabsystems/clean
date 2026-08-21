// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Crystal A2 — MINT the proved module instead of transcribing it.**
//!
//! Link 2a says: the module the crystal PROVES ABOUT is the module the
//! compiler EMITTED. Before this module, the only mechanism behind that
//! sentence was `tests/crystal_a1_lineage.rs`: a hand-written CFG comparator
//! over a hand-written spec module. Its own docs named the hole —
//! *"`ir_h2_module` remains hand-transcribed. This gate makes an incorrect
//! transcription FAIL rather than making a correct one automatic."*
//!
//! This module makes a correct one automatic, and it found a live defect the
//! first time it ran. See "The defect this found" below.
//!
//! # Three readers, one object
//!
//! | reader | input | lives |
//! |---|---|---|
//! | **A** | the artifact BINARY (`clean_kernel.trust-ir.bin`), via `trust_ir`'s own decoder and its own `format::canonicalize` | `scripts/crystal_a2_project` (committed and reviewable, but not a workspace member — it depends on the sibling `trust` checkout), output committed as `generated/ir_<chain>.core.txt` |
//! | **B** | the emitted trust-ir TEXT committed at `tests/fixtures/<chain>.trust-ir.txt` | [`emitted`], in this crate, no producer dependency |
//! | **C** | the ELABORATED KERNEL TERM registered under `ir_<chain>_module` | [`decode`], in this crate |
//!
//! All three produce the same object — a *core module* ([`core`]) — and the
//! gate compares them as canonical text. Reader C is what keeps [`mint`] out
//! of the trusted base: it never sees the minter's output, only the `Expr`
//! the specification registered, so a minter that mistranslated an operator is
//! caught by a reader that could not have made the same mistake for the same
//! reason.
//!
//! # The renumbering fact, and how this survives it
//!
//! `func.N`, `enum.N`, `struct.N` and `#loc` file indices MOVE under a producer
//! change with zero instructions changed — measured, and a gate that fires on
//! that is a false-alarm generator. The core form normalizes them away:
//!
//! * crate-level interning ids are renumbered densely **by first use**;
//! * SSA value ids are the producer's OWN dense canonical renumbering
//!   (`trust_ir::format::canonicalize`), not a rule invented here;
//! * spans, names and producer tags are erased.
//!
//! Measured over three real dumps of the shipped `clean-kernel`
//! (trust `wave-tr-fix` 2026-08-12 binary-format v36, `mfclose` 2026-08-13 v36,
//! `lane2rv` 2026-08-19 v37), for all eleven chained bodies: every artifact
//! `func_id` moved (e.g. `has_cubical_layer` 5246 → 4177,
//! `expr_path_step_clone` 7475 → 6301), `expr_path_step_clone`'s enum id moved
//! 181 → 176 — the exact drift class `docs/CRYSTAL_STATUS.md` records as an
//! open failure — and **all eleven core digests were byte-identical across all
//! three producers.** The full table is `generated/ir_mint.producer_ab.json`;
//! the projector that produced it is `scripts/crystal_a2_project`, committed so
//! the derivation of a committed artifact is re-runnable rather than folklore.
//!
//! # The second defect this found: one numeral, two functions
//!
//! `(func N …)` and `(call M …)` name the SAME namespace — `ir_func_find`
//! resolves a callee by scanning for a function whose OWN id equals it, and
//! `ir_call_exec` goes through it. Both writers of the core form nevertheless
//! filled that namespace from two counters, each starting at `0`: the own id
//! was a hard-coded literal, the callees were interned by first use. In
//! `level_is_zero` the numeral `0` therefore denoted both `Level::is_zero` and
//! `<LevelArc as Deref>::deref`, and the two were interchangeable — exchanging
//! the two `@func.N` literals in the emitted fixture produced a BYTE-IDENTICAL
//! core module for a program that composes its two calls the other way round.
//! M1 through M7 all pass on either.
//!
//! It also made a committed safety claim false. `crystal_a1_lineage` justified
//! leaving link 2a open partly on "a minted `ir_lz_module` contains `call` to a
//! callee that is not in the module, `ir_call_exec` is fail-closed on that" —
//! but the deref sat at `0`, the module's one function has id `0`, so
//! `ir_func_find` would have RESOLVED it, silently turning a call to `deref`
//! into a recursive call to `is_zero`. Only the genuine self-call went stuck.
//!
//! The namespaces are now one, self interned first: [`SelfFunc`] and
//! `tests/crystal_a2_mint/callee_identity.rs`, which carries the constructed
//! counterexample permanently. Reader A can do this unaided; reader B is TOLD,
//! by the `funcs` lane of the chain's tag table, and told nothing is
//! [`SelfFunc::Unpinned`] — under which index `0` stays reserved and empty.
//!
//! # The first defect this found
//!
//! `Inst::Switch.exhaustive_enum_unreachable` is a real field of the emitted
//! instruction that trust-ir's `Display` **never prints**
//! (`display.rs` matches `Inst::Switch { .., .. }`). It is therefore invisible
//! to every text-anchored lane, including the A1 CFG comparator. The
//! hand-written `ir_h2_b0` carried `Bool.true`. All three artifact binaries say
//! **false**, and so do the four sibling chains' hand transcriptions. The
//! minted module carries the measured value. Nothing in `eval_ir_machine`
//! dispatches on the flag (`IRInst.switch v dflt dargs cases exh =>
//! ir_switch_exec m s (ir_getd s v) dflt dargs cases` drops it), so no theorem
//! moved — but a theorem was being stated about a module the compiler does not
//! emit, and it no longer is.
//!
//! # What this establishes, and what it does not
//!
//! ESTABLISHED: the registered `ir_<chain>_module` is **generated** from the
//! emitted artifact rather than transcribed, its generation is deterministic
//! and re-checkable in-tree, and three independent readers — one of them the
//! elaborated kernel term itself — agree on it, under a normalization that is
//! measured to be invariant across three producers.
//!
//! NOT ESTABLISHED, and not to be read in:
//!
//! * **This is not the hook-time mini-module.** Reader A projects the function
//!   out of the ASSEMBLED crate artifact. `trust`'s own
//!   `lineage.rs` states that assembly's meaning-preservation "proof does not
//!   exist". So this gate cannot recompute `body_lineage_digest` and cannot
//!   assert digest identity with the flip event. That check needs a producer
//!   change (publish the hook-time mini-module) and is left open in writing.
//! * **Encoding correspondence is still assumed.** That Clean's `IRInst`
//!   encoding of `switch`/`br` MEANS what trust-ir's does is not re-derived
//!   here; it is the shape table's declaration.
//! * The declared erasures are enumerated, one list, at
//!   `data/crystal_mint_blind_slots.json`, each row anchored to the source line
//!   that erases it and several carrying a constructed witness (two emitted
//!   bodies differing only in that slot). `tests/crystal_a2_mint/blind_slots.rs`
//!   is the lane that keeps that list from rotting, and on 2026-08-20 it did
//!   exactly that: closing four slots broke the four anchors that claimed them.
//!
//!   **What is still outside the fragment after that closure**: `align`, the
//!   function-type id, parameter types, block-parameter types, calling
//!   convention and linkage are all still absent from the core module, and no
//!   core digest moved. What changed is the ACCEPTANCE. [`project`] — the
//!   gate's one entry point — reads the function's name, its LINKAGE, its
//!   CALLING CONVENTION, its SIGNATURE INDEX, every parameter's type, every
//!   `align` operand, the KINDS of annotation clause and the `#producer`
//!   token, and refuses a body whose interface is not the one the chain's tag
//!   table pins. So `bb0(%0: ptr)` and `bb0(%0: Rc<enum.13>)` are still one
//!   core module and are no longer one accepted artifact.
//!
//!   Of the rest: a `global_addr` is now REFUSED outright rather than interned
//!   into a module whose global list is hard-coded empty; a callee index the
//!   table does not pin, or pins as a different crate id, is refused; and the
//!   three operands `ir_exec` genuinely drops —
//!   `Switch.exhaustive_enum_unreachable` and `CallIndirect`'s signature and
//!   convention — are now KERNEL-CHECKED inert
//!   (`ir_exec_switch_exh_irrelevant`, `ir_exec_callind_sig_irrelevant`,
//!   `ir_exec_callind_conv_irrelevant`), to the standard
//!   `ir_ty_is_agg_enum_any` set, instead of argued in a comment.
//!
//!   **Corrected 2026-08-20 (third pass).** This paragraph used to end: *"the
//!   calling convention and linkage of a FUNCTION remain permanently blind to
//!   readers B and C: the producer prints neither."* That was false.
//!   `trust_ir::display`'s `impl Display for Function` prints both, suppressing
//!   each only when it holds its default — the `rustcc` at the head of every
//!   fixture IS the calling convention — and `trust_ir::parser` reads both
//!   back. Both are now read and compared. What is genuinely open is narrower:
//!   the convention of a DIRECT CALLEE, which `trust_ir::Inst::Call` does not
//!   carry at all, so it is a cross-function fact rather than a text-reader
//!   blindness.
//!
//!   The same pass closed two more things this reader had no row for.
//!   `functy.N` — trust-ir's fourth crate-level namespace — is now pinned and
//!   compared, because `FuncTy` is `{ params, returns, is_vararg }` and a body
//!   differing only in that numeral can be a variadic function where the pin
//!   says otherwise. And [`read_emitted`] is now TOTAL over its input: it used
//!   to `break` at the first `}` and ignore the remainder, so a text carrying a
//!   whole second function projected to the same core module as the first
//!   alone. Non-blank content after the close is a refusal, and a body with no
//!   close is refused as truncated.
//! * One residual survives every check here: a MATCHED pair of mistakes in
//!   [`mint`] and [`decode`] (both mapping `and` to `or_`). The shape table is
//!   the mitigation — one row per constructor, read by both directions — and
//!   the name-parity test fails closed if a constructor lacks one.

pub mod core;
mod decode;
mod emitted;
mod emitted_inst;
mod error;
mod interface;
mod mint;
mod shape;
pub mod tags;

#[cfg(test)]
mod tests;

pub use core::{digest, parse, print, Sx};
pub use decode::decode;
pub use emitted::{
    read as read_emitted, read_with_self as read_emitted_with_self,
    read_with_tags as read_emitted_with_tags, ObservedTags, SelfFunc, CALLING_CONVS, CLAUSE_KINDS,
    DEFAULT_CALLING_CONV, DEFAULT_LINKAGE, LINKAGES, SELF_FUNC_INDEX,
};
pub use error::{CoreError, DecodeError, EmittedError, InterfaceError, MintError};
pub use interface::{project, Interface, ParamSlot, Projection};
pub use mint::{mint, MintedScript};
pub use tags::Tags;

/// The committed core module of the width-one chain, produced by reader A.
pub const IR_H2_CORE: &str = include_str!("../spec/core_spec/generated/ir_h2.core.txt");
/// The committed minted definition script of the width-one chain.
pub const IR_H2_DEFS: &str = include_str!("../spec/core_spec/generated/ir_h2.defs.txt");
/// The committed mint record: provenance, digests and the unwitnessed ledger.
pub const IR_H2_RECORD: &str = include_str!("../spec/core_spec/generated/ir_h2.mint.json");
/// The committed tag table of the width-one chain: canonical first-use index →
/// the crate-level interning id the artifact names.
pub const IR_H2_TAGS: &str = include_str!("../spec/core_spec/generated/ir_h2.tags.json");
/// The committed core module of the ELEVENTH chain,
/// `env::types::SimpPriority::value` — the first chained body that computes an
/// address with a `gep` and loads through the result.
pub const IR_PV_CORE: &str = include_str!("../spec/core_spec/generated/ir_pv.core.txt");
/// The committed minted definition script of the `gep` chain.
pub const IR_PV_DEFS: &str = include_str!("../spec/core_spec/generated/ir_pv.defs.txt");
/// The committed mint record of the `gep` chain.
pub const IR_PV_RECORD: &str = include_str!("../spec/core_spec/generated/ir_pv.mint.json");
/// The committed tag table of the `gep` chain. Its one enum is interned at
/// **127**, outside the `ir_d0..ir_d16` atom pool, which is why
/// `mint::interning_id` exists.
pub const IR_PV_TAGS: &str = include_str!("../spec/core_spec/generated/ir_pv.tags.json");
/// The committed core module of the designated target `level::Level::is_zero`,
/// produced by reader A. Not minted — see `crystal_a2_mint`'s
/// `level_is_zero_mints_only_up_to_a_named_refusal` — but read by the callee
/// identity lane, which is the only chain in the set that CALLS anything.
pub const IR_LZ_CORE: &str = include_str!("../spec/core_spec/generated/ir_lz.core.txt");
/// The committed tag table of the designated target. Its `funcs` lane is the
/// only one in the tree that is non-empty, because `level_is_zero` is the only
/// chained body that calls anything.
pub const IR_LZ_TAGS: &str = include_str!("../spec/core_spec/generated/ir_lz.tags.json");

/// One field that a given reader structurally cannot witness.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Unwitnessed {
    /// The block the instruction sits in.
    pub block: String,
    /// The node's index within the block.
    pub node: usize,
    /// The instruction mnemonic.
    pub inst: String,
    /// The slot's position in the instruction's declared argument list.
    pub slot: usize,
}

impl std::fmt::Display for Unwitnessed {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "bb{}#{} {} arg{}",
            self.block, self.node, self.inst, self.slot
        )
    }
}

/// Apply reader B's blindness to a fully-witnessed core module: every flag the
/// emitted TEXT cannot show becomes `?`.
///
/// Comparing `mask(A)` against `B` is exact — no tolerance, no fuzz — and the
/// slots that were masked are returned so the gate can print them rather than
/// quietly accept them.
///
/// # Errors
/// Returns [`CoreError`] when `a` is not a well-formed core module.
pub fn mask_text_unwitnessed(a: &Sx) -> Result<(Sx, Vec<Unwitnessed>), CoreError> {
    let mut ledger = Vec::new();
    let masked = mask_rec(a, &mut ledger, "", 0)?;
    Ok((masked, ledger))
}

fn mask_rec(
    sx: &Sx,
    ledger: &mut Vec<Unwitnessed>,
    block: &str,
    node: usize,
) -> Result<Sx, CoreError> {
    match sx {
        Sx::Atom(a) => Ok(Sx::Atom(a.clone())),
        Sx::List(items) => {
            let head = items.first().and_then(|h| h.atom().ok()).unwrap_or("");
            match head {
                "block" => {
                    // `(block ID (params …) (nodes …))` — the block id has to
                    // be in scope while its nodes are walked, so the ledger can
                    // name the slot rather than just count it.
                    if items.len() != 4 {
                        return Err(CoreError::Shape(format!(
                            "(block id (params ..) (nodes ..)) takes 4 items, found {}",
                            items.len()
                        )));
                    }
                    let bid = items[1].atom()?.to_string();
                    let mut ns = Vec::new();
                    for (i, n) in items[3].tagged("nodes")?.iter().enumerate() {
                        ns.push(mask_rec(n, ledger, &bid, i)?);
                    }
                    Ok(Sx::List(vec![
                        items[0].clone(),
                        items[1].clone(),
                        items[2].clone(),
                        Sx::tag("nodes", ns),
                    ]))
                }
                // `switch`'s LAST argument is `exhaustive_enum_unreachable`.
                "switch" => {
                    let mut out = items.clone();
                    if let Some(last) = out.last_mut() {
                        ledger.push(Unwitnessed {
                            block: block.to_string(),
                            node,
                            inst: "switch".into(),
                            slot: items.len() - 2,
                        });
                        *last = Sx::a("?");
                    }
                    Ok(Sx::List(out))
                }
                _ => {
                    let mut out = Vec::with_capacity(items.len());
                    for i in items {
                        out.push(mask_rec(i, ledger, block, node)?);
                    }
                    Ok(Sx::List(out))
                }
            }
        }
    }
}

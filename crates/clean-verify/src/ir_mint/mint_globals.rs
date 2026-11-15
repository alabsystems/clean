// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The globals lane**: the one module-table global shape, and the minting,
//! namespace check and decoding that go through it.
//!
//! Split out of [`super::mint`], [`super::shape`] and [`super::decode`] rather
//! than grown inside them: a global is the one module-table object that is
//! neither a function nor a block, and all three of its sides — the shape
//! table row, the minter's `(globals …)` parse plus its three-way namespace
//! check, and reader C's read-back — are one unit that changes together.
//!
//! The decoder half is an inherent `impl` on [`Decoder`], which lives here so
//! the global list reads back through the SAME [`GLOBAL`] row the minter wrote
//! through. The order matters on both sides: the registered term lists the
//! globals in the order `ir_global_find` walks, so it is part of the module's
//! identity and the M4 digest comparison sees a reordering.

use std::collections::BTreeSet;
use std::fmt::Write as _;

use clean_kernel::Expr;

use super::core::{for_each_inst, Sx};
use super::decode::Decoder;
use super::error::{CoreError, DecodeError, MintError};
use super::mint::{arg, nat};
use super::shape::Arg;
use super::tags::Tags;

/// The one MODULE-TABLE GLOBAL shape: `(global <id> <initializer>)` in the
/// core module's `(globals …)` list, `IRGlobal.mk <id> <initializer>` in the
/// minted script.
#[derive(Debug, Clone, Copy)]
pub(crate) struct GlobalShape {
    /// The core mnemonic.
    pub(crate) core: &'static str,
    /// The Clean `IRGlobal` constructor.
    pub(crate) clean: &'static str,
    /// The argument kinds, in order.
    pub(crate) args: &'static [Arg],
}

/// `(global <Arg::Nat> <Arg::Const>)` ↔ `IRGlobal.mk`, and NOTHING else.
///
/// `IRGlobal.mk : Nat → IRConst → IRGlobal` (`eval_ir_syntax.rs`) takes the
/// global's id and its initializer. The global's TYPE (`[u8 x 34]`), its NAME
/// and its linkage have no slot in the module at all; they are pinned in the
/// tag table's `globals` lane and compared by `project` — the `param-type`
/// pattern over again — so the minter and the decoder never see them and can
/// neither erase nor invent them.
///
/// The two slots sit on the two sides of the structural/datum line the
/// `extractfield` index (in [`super::shape::INSTS`]) drew: the id is
/// STRUCTURAL — a position in this module, the index `ir_global_find` walks
/// and `(globaladdr k)` names, rendered through the `ir_d0..ir_d130` pool and
/// REFUSED above it — and the initializer's bytes are DATA, each `(int b)`
/// rendered through the data policy (`ir_d8` for 8, the literal `108` for
/// 108), which is what keeps a 34-byte string initializer mintable without a
/// 108-entry pool.
pub(crate) const GLOBAL: GlobalShape = GlobalShape {
    core: "global",
    clean: "IRGlobal.mk",
    args: &[Arg::Nat, Arg::Const],
};

/// One `(global k C)` entry of the module's global list, with its index
/// already rendered through the STRUCTURAL pool.
pub(super) struct GlobalEntry<'a> {
    /// The global's index — the position `(globaladdr k)` names.
    pub(super) index: u32,
    /// The `(global k C)` items, `k` then `C`, in [`GLOBAL`]'s order.
    items: &'a [Sx],
}

/// Parse the module's `(globals …)` list: `(global k C)` entries whose index
/// `k` equals their position.
///
/// Dense and ordered is not a style rule. The list order IS the order
/// `ir_global_find` walks and `ir_init` materializes cells in, so it is a fact
/// about the module exactly as the function list's order is — and a
/// `(global 1 …)` at position 0 would mint a module whose `(globaladdr 0)`
/// resolves to nothing while the machine's cell 0 holds global 1's bytes.
///
/// The index is rendered through [`nat`] here, before anything else is asked
/// of the entry, so an index above the atom pool refuses as
/// [`MintError::Numeral`] rather than as a downstream shape complaint.
pub(super) fn parse_globals(items: &[Sx]) -> Result<Vec<GlobalEntry<'_>>, MintError> {
    let mut out = Vec::with_capacity(items.len());
    for (position, g) in items.iter().enumerate() {
        let gi = g.tagged(GLOBAL.core)?;
        if gi.len() != GLOBAL.args.len() {
            return Err(CoreError::Shape(format!(
                "`({} k C)` takes {} items, found {}",
                GLOBAL.core,
                GLOBAL.args.len(),
                gi.len()
            ))
            .into());
        }
        let raw = gi[0].num()?;
        // The refusal for an index the pool lacks, stated before the position
        // check reads the same numeral as an ordering fault.
        nat(raw)?;
        let index = u32::try_from(raw)
            .map_err(|_| CoreError::Shape(format!("global index {raw} does not fit u32")))?;
        if usize::try_from(index).ok() != Some(position) {
            return Err(CoreError::Shape(format!(
                "the module's global list is out of order or not dense: position {position} \
                 carries `(global {index} …)`. The list order IS the order `ir_global_find` \
                 walks, so it is a fact about the module"
            ))
            .into());
        }
        out.push(GlobalEntry { index, items: gi });
    }
    Ok(out)
}

/// `IRGlobal.mk <id> <initializer>` for one entry, through [`GLOBAL`].
pub(super) fn global(g: &GlobalEntry<'_>, tags: &Tags) -> Result<String, MintError> {
    let mut out = String::from(GLOBAL.clean);
    for (kind, x) in GLOBAL.args.iter().zip(g.items) {
        let _ = write!(out, " {}", arg(*kind, x, tags)?);
    }
    Ok(out)
}

/// **The global namespace, every index in it accounted for THREE ways.**
///
/// `(global k …)` and `(globaladdr k)` name the same namespace —
/// `ir_global_find` resolves an address by scanning the module's global list
/// for the entry whose own id equals it — so the list, the instructions and
/// the tag table's `globals` lane must agree exactly:
///
/// * every `(globaladdr k)` must have a `(global k …)` — an address into an
///   entry the module does not declare is `stuck no_global` at run time and a
///   numeral standing for nothing at mint time;
/// * every `(global k …)` must be addressed by some instruction — an entry
///   nothing reaches is a cell the machine materializes for no reader, and
///   would mint 34 bytes of initializer that no theorem is about;
/// * every index, declared or addressed, must be PINNED by
///   [`Tags::global_pin`] — exactly as [`super::mint::check_func_namespace`] refuses an
///   unpinned callee. The pin is where the name, the resolved type and the
///   linkage live, since [`GLOBAL`] has no slot for any of them; a
///   module that minted an unpinned global would register bytes under an
///   index whose identity nothing recorded, and only `project` — which a
///   hand-built core never passes through — would ever have said so.
pub(super) fn check_global_namespace(
    core: &Sx,
    globals: &[GlobalEntry<'_>],
    tags: &Tags,
) -> Result<(), MintError> {
    let declared: BTreeSet<u32> = globals.iter().map(|g| g.index).collect();
    for k in &declared {
        tags.global_pin(*k)?;
    }
    let mut addressed: BTreeSet<u32> = BTreeSet::new();
    for_each_inst(core, |block, node, inst| {
        let l = inst.list()?;
        if l.first().and_then(|h| h.atom().ok()) != Some("globaladdr") {
            return Ok(());
        }
        let raw = l
            .get(1)
            .ok_or_else(|| {
                CoreError::Shape(format!("bb{block}#{node}: `globaladdr` with no index"))
            })?
            .num()?;
        let k = u32::try_from(raw)
            .map_err(|_| CoreError::Shape(format!("global index {raw} does not fit u32")))?;
        if !declared.contains(&k) {
            return Err(CoreError::Shape(format!(
                "bb{block}#{node}: `(globaladdr {k})` addresses a global the module's \
                 `(globals …)` list does not declare (declared: {declared:?}). The address and \
                 the entry are one namespace, and an index with no entry is a numeral standing \
                 for nothing"
            )));
        }
        tags.global_pin(k)?;
        addressed.insert(k);
        Ok(())
    })?;
    for g in globals {
        if !addressed.contains(&g.index) {
            return Err(CoreError::Shape(format!(
                "`(global {} …)` is declared and no instruction addresses it: a global list \
                 entry nothing names is a cell the machine would materialize for no reader",
                g.index
            ))
            .into());
        }
    }
    Ok(())
}

impl Decoder<'_> {
    /// The module's GLOBAL LIST, read back entry by entry through [`GLOBAL`].
    ///
    /// The order is the order the registered term lists them in, which is the
    /// order `ir_global_find` walks — so it is part of the module's identity,
    /// and a reordering shows up in the M4 digest comparison rather than being
    /// normalised away here.
    ///
    /// # Errors
    /// Returns [`DecodeError`] if the term is not an `IRList IRGlobal`, or if
    /// any entry is not exactly an `IRGlobal.mk` application of the arity
    /// [`GLOBAL`] declares.
    pub(super) fn globals(&self, e: &Expr) -> Result<Sx, DecodeError> {
        let gs = self.list(e, "IRGlobal", "the global list")?;
        let mut out = Vec::with_capacity(gs.len());
        for g in &gs {
            out.push(self.global(g)?);
        }
        Ok(Sx::tag("globals", out))
    }

    /// `IRGlobal.mk <id> <initializer>` → `(global <nat> <cst>)`, through
    /// [`GLOBAL`]: the id reads back as a `Nat`, the initializer through
    /// [`Self::cst`], and a term whose head is anything else is a refusal.
    fn global(&self, e: &Expr) -> Result<Sx, DecodeError> {
        let sh = GLOBAL;
        let a = self.ctor(e, sh.clean, "a global", sh.args.len())?;
        let mut out = Vec::with_capacity(a.len());
        for (kind, x) in sh.args.iter().zip(&a) {
            out.push(self.arg(*kind, x, "a global")?);
        }
        Ok(Sx::tag(sh.core, out))
    }
}

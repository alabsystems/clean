// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The INTERFACE: the artifact facts the core module deliberately does not
//! carry, read from the emitted text and pinned in the chain's tag table.**
//!
//! `data/crystal_mint_blind_slots.json` enumerates every field the emitted
//! artifact carries and the committed core module does not. Five of its rows
//! carried a CONSTRUCTED WITNESS — a pair of emitted bodies that denote
//! different programs and project to one core module. This module is where
//! four of those five stop being accepted.
//!
//! # Why here and not in the core module
//!
//! Clean's `IRModule` has nowhere to put a parameter type: `IRFunc` carries an
//! id, parameter SSA ids, an entry block and blocks, and no type at all
//! (`eval_ir_syntax.rs`). Putting the parameter type into the core module would
//! therefore mean changing the specification's own inductive, which moves every
//! registered term, every core digest and every theorem that mentions one. That
//! is not what a blind slot warrants.
//!
//! So this follows the M7 split exactly, and for the same reason: the fact that
//! MOVES under a producer change stays out of the module's identity, and the
//! fact the module cannot express is pinned in a reviewed table that a gate
//! checks against the artifact. What changes is that the pair is no longer
//! ACCEPTED — [`project`] is the gate's one entry point and it refuses a body
//! whose interface is not the pinned one.
//!
//! # Producer invariance, which is the hard half
//!
//! A parameter type is printed with crate-level table entries in it:
//! `expr_path_step_clone`'s join block binds `%1: enum.181`, and that same
//! enum is `enum.176` under the 2026-08-19 producer with not one instruction
//! changed. Pinning the printed token verbatim would make this lane a
//! false-alarm generator — the exact failure mode the core form exists to
//! absorb.
//!
//! [`Tags::canon_ty`](super::Tags::canon_ty) is the answer: every
//! `<kind>.<digits>` in the token is resolved THROUGH the chain's tag table to
//! the canonical first-use index the core module already uses (`enum.13` →
//! `enum#0`), and an id the table does not list becomes `<kind>#?`. The pinned
//! form is therefore invariant under exactly the renumbering the core form is
//! invariant under, and under nothing else: `ptr` and `Rc<enum.13>` are
//! `ptr` and `Rc<enum#0>`, which are not equal.

use std::collections::BTreeSet;

use super::core::Sx;
use super::emitted::ObservedTags;
use super::emitted::{DEFAULT_CALLING_CONV, DEFAULT_LINKAGE};
use super::error::InterfaceError;
use super::tags::Tags;

/// One parameter of a function or of a block: where it sits, which SSA id it
/// binds, and its printed type.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ParamSlot {
    /// The block whose header binds it.
    pub block: u32,
    /// Its 0-based position in that header.
    pub index: u32,
    /// The SSA id it binds — the ONLY half of this slot the core module keeps.
    pub ssa: u32,
    /// Its printed type. Raw as read; canonical after
    /// [`Interface::canonicalize`].
    pub ty: String,
}

impl std::fmt::Display for ParamSlot {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "bb{}#{} %{}: {}",
            self.block, self.index, self.ssa, self.ty
        )
    }
}

/// Everything the emitted text says about a body that the core module does not
/// encode — and that a reader of the text CAN witness.
///
/// Deliberately not a grab-bag: a field belongs here when the artifact prints
/// it, the fragment cannot hold it, and two bodies differing only in it denote
/// different programs.
///
/// Three of these fields were added on 2026-08-20 **after the row that excused
/// them turned out to rest on a false premise about the producer**, which is
/// worth keeping in the type that fixes it. `data/crystal_mint_blind_slots.json`
/// said of calling convention and linkage: *"the producer prints neither, so no
/// text reader CAN witness either."* `trust_ir`'s own `Display for Function`
/// says otherwise —
///
/// ```text
/// if self.linkage != Linkage::External { write!(f, "{} ", self.linkage)?; }
/// if self.calling_conv != CallingConv::C { write!(f, "{} ", self.calling_conv)?; }
/// write!(f, "fn @{}(functy.{ft_idx})", self.name)?;
/// ```
///
/// — it prints BOTH, suppressing each only when it holds its default, and
/// `parser.rs`'s `try_parse_calling_conv` / `is_func_prefix` read them back.
/// The `rustcc` in every fixture header IS the calling convention. So the slot
/// was never blind: it was witnessed by accident, by a reader that matched the
/// literal prefix `"rustcc fn @"` and could not say what it had just refused.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Interface {
    /// The name in the `… fn @…` header.
    pub function_name: String,
    /// The function's LINKAGE, as the header spells it — or `external` when the
    /// header spells none, because the producer suppresses the default.
    ///
    /// ABSENCE IS A VALUE here and has to be read as one. That is why this is a
    /// `String` and not an `Option<String>`: an unprinted linkage is `external`,
    /// not "unknown", and modelling it as unknown is how a slot goes blind.
    pub linkage: String,
    /// The function's CALLING CONVENTION, same rule: the header's token, or
    /// `ccc` when it prints none.
    pub calling_conv: String,
    /// The whole-crate function-TYPE table index in the header, `functy.N`.
    ///
    /// Recorded and, since 2026-08-20, COMPARED. It is the last of trust-ir's
    /// four crate-level namespaces to get a pin — `enum.N`, `struct.N` and
    /// `@func.N` already had one — and it was the last numeral in the pipeline
    /// that stood for nothing: `FuncTy` is `{ params, returns, is_vararg }`
    /// (`trust-ir/src/ty.rs`), and neither `is_vararg` nor an unreached
    /// `returns` is recoverable from the printed body. Two bodies differing
    /// only in this numeral are a variadic and a non-variadic function, and
    /// before this field the gate accepted them as one.
    pub functy: u32,
    /// The `; #producer:` token, when the body carries one.
    ///
    /// The one clause whose CONTENT is compared. The other four allowed kinds
    /// (`loc`, `scope`, `names`, `proof`) carry debug info or a claim ABOUT the
    /// body; this one names WHO COMPILED IT, which is the fact link 2a exists
    /// to establish.
    pub producer: Option<String>,
    /// The entry block's parameters — the function's parameters in this
    /// producer's shape.
    pub params: Vec<ParamSlot>,
    /// Every non-entry block's parameters, in block order.
    pub block_params: Vec<ParamSlot>,
    /// The alignment operand of every memory instruction, in program order, in
    /// reader A's own recorded spelling (`load:None`, `load:Some(8)`).
    pub aligns: Vec<String>,
    /// The KINDS of trailing `; #…` clause the body carries.
    pub clauses: BTreeSet<String>,
}

/// The values trust-ir's printer SUPPRESSES, and therefore the values a header
/// that prints no such token carries.
impl Default for Interface {
    fn default() -> Self {
        Self {
            function_name: String::new(),
            linkage: DEFAULT_LINKAGE.to_string(),
            calling_conv: DEFAULT_CALLING_CONV.to_string(),
            functy: 0,
            producer: None,
            params: Vec::new(),
            block_params: Vec::new(),
            aligns: Vec::new(),
            clauses: BTreeSet::new(),
        }
    }
}

impl Interface {
    /// The producer-invariant form: every crate-level id inside a printed type
    /// resolved through the chain's tag table.
    #[must_use]
    pub(crate) fn canonicalize(&self, tags: &Tags) -> Self {
        let map = |ps: &[ParamSlot]| -> Vec<ParamSlot> {
            ps.iter()
                .map(|p| ParamSlot {
                    ty: tags.canon_ty(&p.ty),
                    ..p.clone()
                })
                .collect()
        };
        Self {
            params: map(&self.params),
            block_params: map(&self.block_params),
            ..self.clone()
        }
    }
}

/// A body read from the emitted text: the core module the theorems are about,
/// AND the interface the module does not carry.
///
/// The two halves are returned together on purpose. Before 2026-08-20 the gate
/// compared only the first half, and the blind-slot list is the record of what
/// that let through.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Projection {
    /// The core module. Unchanged by this module — its digest did not move.
    pub core: Sx,
    /// The crate-level ids the ROOT body named.
    pub tags: ObservedTags,
    /// The ROOT body's interface, CANONICALIZED against the chain's tag table.
    pub interface: Interface,
    /// EVERY body's interface, in module order — `interfaces[0]` is
    /// [`interface`](Self::interface). One entry for a one-body chain, which is
    /// every chain before `has_loose_bvars`.
    pub interfaces: Vec<Interface>,
    /// EVERY body's observed crate-level ids, in module order — `bodies[0]` is
    /// [`tags`](Self::tags).
    pub bodies: Vec<ObservedTags>,
}

/// Read an emitted body and accept it only if it is the body the chain's tag
/// table describes.
///
/// This is the gate's one acceptance predicate. It refuses — never adjusts —
/// when the artifact and the pin disagree, so a slot that used to be erased is
/// now a hard stop with the two values printed.
///
/// # Errors
/// Returns [`InterfaceError::Read`] when the text is not readable at all, and
/// one of the interface variants when the artifact does not match the pin.
pub fn project(text: &str, tags: &Tags) -> Result<Projection, InterfaceError> {
    // The chain's bodies, in MODULE ORDER. One for every chain before
    // `has_loose_bvars`, in which case this is exactly the previous read.
    let declared = tags.body_canonicals();
    // The MODULE-TABLE PREAMBLE first: the `type ty.N = …` and `global …`
    // rows the printer emits before the first function, read by
    // `emitted_globals` into the declarations `interface_globals::check_globals`
    // compares against the tag table's `globals` lane. Every committed fixture before `ir_lzc`
    // carries none, so the split hands them to `split_bodies` whole.
    let (preamble_lines, bodies_text) = super::emitted_globals::split_preamble(text);
    let preamble = super::emitted_globals::parse(&preamble_lines)?;
    // The bodies' line numbers are offset by the preamble, so a refusal the
    // split raises names the FILE line and not a body-relative one.
    let chunks = super::emitted::split_bodies(bodies_text, declared.len(), preamble_lines.len())?;
    // The namespace the tag table already accounts for: every body of this
    // module at its canonical index, so a call to a SIBLING reads as that
    // sibling and not as a fresh foreign callee.
    //
    // The ROOT may be [`SelfFunc::Unpinned`] — that is the honest reading for a
    // body whose `funcs` lane is empty because it calls nothing, which is
    // twelve of the eighteen chains — and then it contributes no namespace
    // entry and index 0 stays reserved, exactly as before this lane. An EXTRA
    // body must be pinned: its canonical index is a numeral the module's
    // `(func N …)` carries, and an unpinned one would stand for nothing.
    let mut namespace = std::collections::BTreeMap::new();
    let mut selves = Vec::with_capacity(declared.len());
    for canonical in &declared {
        let sf = if *canonical == super::SELF_FUNC_INDEX {
            tags.self_func()
        } else {
            let (crate_id, _) = tags
                .func_pin(*canonical)
                .map_err(|e| InterfaceError::Unpinned(format!("{e}")))?;
            super::SelfFunc::Pinned(*crate_id)
        };
        if let super::SelfFunc::Pinned(id) = sf {
            namespace.insert(id, *canonical);
        }
        selves.push(sf);
    }
    // The GLOBAL namespace the tag table accounts for, built from its
    // `globals` lane exactly as `namespace` is built from `funcs`: crate-level
    // `@global.N` id -> canonical index. Its presence is what lets reader B
    // read a `global_addr` at all (a bare read refuses one); every other
    // committed table omits the lane, so this is empty for them and a body of
    // theirs that addressed a global would intern above nothing and then be
    // refused by `check_globals`.
    let global_namespace: std::collections::BTreeMap<u32, u32> = tags
        .globals
        .iter()
        .map(|(canonical, pin)| (pin.crate_id, *canonical))
        .collect();
    let mut cores = Vec::new();
    let mut interfaces = Vec::new();
    let mut bodies = Vec::new();
    let enum_namespace = tags.enum_namespace();
    let struct_namespace = tags.struct_namespace();
    let mut usize_seen = 0u32;
    let mut isize_seen = 0u32;
    for ((chunk, canonical), sf) in chunks.iter().zip(&declared).zip(&selves) {
        let (core, observed) = super::emitted::read_body(
            chunk,
            *sf,
            *canonical,
            &namespace,
            tags.usize_pin.map(|u| u.bits),
            &global_namespace,
            (&enum_namespace, &struct_namespace),
        )?;
        let pinned = tags
            .body_interface(*canonical)
            .map_err(|e| InterfaceError::Unpinned(format!("{e}")))?;
        let interface = observed.interface.canonicalize(tags);
        check_body(&interface, pinned, &observed, tags)?;
        usize_seen = usize_seen.saturating_add(observed.usize_seen);
        isize_seen = isize_seen.saturating_add(observed.isize_seen);
        // The one function reader B just read, lifted out of its one-function
        // wrapper so the chain's functions can be spliced into ONE module.
        let one = core
            .tagged("module")
            .and_then(|m| m[0].tagged("funcs"))
            .map_err(|e| InterfaceError::Unpinned(format!("{e}")))?
            .first()
            .cloned()
            .ok_or_else(|| {
                InterfaceError::Unpinned("reader B produced a module with no function".into())
            })?;
        cores.push(one);
        interfaces.push(interface);
        bodies.push(observed);
    }
    // The module's GLOBAL LIST, spliced from the preamble in canonical order
    // once every body's `global_addr` and every pin and every declaration
    // account for one another. Empty — the literal `(globals)` — for every
    // chain whose table has no lane, which is every chain before `ir_lzc`.
    // The AGGREGATE lanes first: which crate `enum`/`struct` each body's
    // `enum.N` / `struct.N` denotes. Before the globals check because a module
    // whose two bodies disagree about what `(enum 0)` means is not a module,
    // and the reason it runs at all is the `aggregate-id` blind slot — until
    // 2026-09-10 nothing compared an observed aggregate id to anything.
    super::interface_aggregates::check_aggregates(&bodies, tags)?;
    let globals =
        super::interface_globals::check_globals(&bodies, &preamble, &global_namespace, tags)?;
    let core = Sx::tag(
        "module",
        vec![Sx::tag("funcs", cores), Sx::tag("globals", globals)],
    );
    let observed = bodies
        .first()
        .cloned()
        .ok_or_else(|| InterfaceError::Unpinned("a chain declares at least one body".into()))?;
    let interface = interfaces
        .first()
        .cloned()
        .unwrap_or_else(|| observed.interface.canonicalize(tags));
    // The `usize` site count, summed over the chain's bodies. When the lane is
    // pinned, the chain must contain EXACTLY the pinned number of `usize`
    // tokens: the resolved core text spells each site as the plain fixed-width
    // integer, so this count — not the core — is what refuses a body whose
    // `usize` became a literal `u64` (or the reverse). When the lane is absent
    // the reader has already refused any `usize`, so the count is zero.
    let pinned_usize = tags.usize_pin.map_or(0, |u| u.sites);
    if usize_seen != pinned_usize {
        return Err(InterfaceError::Mismatch {
            slot: "usize sites".into(),
            pinned: format!("{pinned_usize} `usize` site(s)"),
            found: format!("{usize_seen} `usize` site(s)"),
        });
    }
    // `isize` the same way, and counted SEPARATELY on purpose. The two tokens
    // share a width by Rust's own definition, so they share the lane's `bits`;
    // they do not share a count, because a chain that swapped one for the
    // other would resolve to a different core (`(int n)` against `(uint n)`)
    // and a single summed pin would accept the swap.
    let pinned_isize = tags.usize_pin.map_or(0, |u| u.isize_sites);
    if isize_seen != pinned_isize {
        return Err(InterfaceError::Mismatch {
            slot: "isize sites".into(),
            pinned: format!("{pinned_isize} `isize` site(s)"),
            found: format!("{isize_seen} `isize` site(s)"),
        });
    }
    Ok(Projection {
        core,
        tags: observed,
        interface,
        interfaces,
        bodies,
    })
}

/// Every per-body check: the header, the parameters, the alignments, the
/// annotation kinds and the callee namespace.
fn check_body(
    interface: &Interface,
    pinned_iface: &Interface,
    observed: &ObservedTags,
    tags: &Tags,
) -> Result<(), InterfaceError> {
    if interface.function_name != pinned_iface.function_name {
        return Err(InterfaceError::FunctionName {
            pinned: pinned_iface.function_name.clone(),
            found: interface.function_name.clone(),
        });
    }
    // Linkage, calling convention and the signature index. All three are in
    // the ONE header line, all three are printed by the producer, and all three
    // were unread until 2026-08-20 — the first two by a literal-prefix match
    // that could not name what it refused, the third not at all.
    for (slot, found, pinned) in [
        ("linkage", &interface.linkage, &pinned_iface.linkage),
        (
            "calling convention",
            &interface.calling_conv,
            &pinned_iface.calling_conv,
        ),
    ] {
        if found != pinned {
            return Err(InterfaceError::Mismatch {
                slot: slot.into(),
                pinned: pinned.clone(),
                found: found.clone(),
            });
        }
    }
    if interface.functy != pinned_iface.functy {
        return Err(InterfaceError::Mismatch {
            slot: "signature index".into(),
            pinned: format!("functy.{}", pinned_iface.functy),
            found: format!("functy.{}", interface.functy),
        });
    }
    if interface.producer != pinned_iface.producer {
        return Err(InterfaceError::Mismatch {
            slot: "producer".into(),
            pinned: format!("{:?}", pinned_iface.producer),
            found: format!("{:?}", interface.producer),
        });
    }
    check_params("parameter", &interface.params, &pinned_iface.params)?;
    check_params(
        "block parameter",
        &interface.block_params,
        &pinned_iface.block_params,
    )?;
    if interface.aligns != pinned_iface.aligns {
        return Err(InterfaceError::Mismatch {
            slot: "align".into(),
            pinned: format!("{:?}", pinned_iface.aligns),
            found: format!("{:?}", interface.aligns),
        });
    }
    if interface.clauses != pinned_iface.clauses {
        return Err(InterfaceError::Mismatch {
            slot: "annotation clause kinds".into(),
            pinned: format!("{:?}", pinned_iface.clauses),
            found: format!("{:?}", interface.clauses),
        });
    }
    // Every callee index must be a function the table NAMES, and must be the
    // one it names. A canonical index with no row is a numeral standing for
    // nothing — precisely the shape of the 2026-08-20 collision, one namespace
    // further out — and an index whose crate id is not the pinned one is a call
    // to a DIFFERENT function, which the core module cannot see at all.
    for (canonical, crate_id) in &observed.funcs {
        let (pinned, name) = tags
            .func_pin(*canonical)
            .map_err(|e| InterfaceError::Unpinned(format!("{e}")))?;
        if pinned != crate_id {
            return Err(InterfaceError::Mismatch {
                slot: format!("callee {canonical} (`{name}`)"),
                pinned: format!("@func.{pinned}"),
                found: format!("@func.{crate_id}"),
            });
        }
    }
    Ok(())
}

fn check_params(
    what: &str,
    found: &[ParamSlot],
    pinned: &[ParamSlot],
) -> Result<(), InterfaceError> {
    if found != pinned {
        return Err(InterfaceError::Mismatch {
            slot: what.into(),
            pinned: pinned
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(", "),
            found: found
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(", "),
        });
    }
    Ok(())
}

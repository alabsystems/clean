// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Reader B**: the emitted trust-ir text `trustc` wrote, read into a core
//! module in this repo, with no dependency on the producer's crates.
//!
//! It exists so that the committed `.core.txt` (reader A, produced from the
//! artifact BINARY by the offline projector) has an independent second reader
//! standing behind it. A transcription mistake in either shows up as a diff
//! between the two, unless both make the SAME mistake — the named residual.
//!
//! Two things this reader structurally cannot do, and does not pretend to:
//!
//! * `Switch.exhaustive_enum_unreachable` is never printed by trust-ir's
//!   `Display` (`display.rs` matches `Inst::Switch { .., .. }`). This reader
//!   emits `?` there. `?` cannot be minted, so the flag has exactly one
//!   in-repo witness — the binary projection — and the gate says so out loud.
//! * `align` is printed but has no `IRInst` field, so it cannot reach the core
//!   module. It is READ nonetheless, into
//!   [`ObservedTags::interface`], where the chain's tag table pins it — until
//!   2026-08-20 `load` split its operand list on the first comma and threw the
//!   rest away, so `load enum.13, ptr %0, align 8` and `load enum.13, ptr %0`
//!   were one core module and nothing anywhere recorded the difference.
//!
//! Everything else in the printed text is read, and anything unrecognised is a
//! refusal.
//!
//! # The function's own index, and why it is not a literal
//!
//! A core module carries the function's own id in `(func N …)` and a callee id
//! in `(call M …)`. Those are ONE namespace, not two, because that is what the
//! specification's own `ir_func_find` says: it resolves a callee by scanning
//! for a function whose OWN id equals it (`eval_ir_state.rs`, the `ir_nat_eqb i
//! k` arm), and `ir_call_exec` goes through `ir_func_find`.
//!
//! Until 2026-08-20 this reader wrote the literal `0` for the function's own id
//! while interning callees from a separate counter that also started at `0`. In
//! `level_is_zero` that made the numeral `0` denote two different functions in
//! one module — the body itself and `<LevelArc as Deref>::deref` — and the two
//! were interchangeable: swapping the two `@func.N` literals in the fixture
//! produced a BYTE-IDENTICAL core module for a program that composes its two
//! calls the other way round. [`SelfFunc`] closes that: index `0` is the
//! function's own index and belongs to no other callee, so a callee can only
//! reach `0` by BEING the body, and only when the body's own id was pinned.

use std::collections::{BTreeMap, BTreeSet};

use super::core::Sx;
use super::error::{CoreError, EmittedError};
use super::interface::{Interface, ParamSlot};

/// Read a canonical emitted trust-ir function body into a core module.
///
/// # Errors
/// Returns [`EmittedError`] on any line the reader does not recognise, and on
/// any construct with no image in the Clean fragment.
pub fn read(text: &str) -> Result<Sx, EmittedError> {
    Ok(read_with_tags(text)?.0)
}

/// The canonical index reserved for the function's OWN id.
///
/// It is a reservation, not a convention: nothing else may be interned at it,
/// so `(call 0 …)` in a core module means "a call to this very function" and
/// cannot mean anything else.
pub const SELF_FUNC_INDEX: u32 = 0;

/// Whether the body's own crate-level function id is known to this read.
///
/// The emitted text names the body by NAME (`rustcc fn @level::Level::is_zero`)
/// and names its callees by whole-crate INDEX (`call @func.4925`), so a text
/// reader cannot tell on its own that one of those indices is the body itself.
/// Reader A, which reads the artifact binary, can. Pinning the id closes that
/// gap for reader B; leaving it unpinned keeps reader B fail-closed instead of
/// guessing.
///
/// The precise property, because "unpinned is worse" is not quite it. Reader A
/// interns the own id first and then walks the body, so its foreign callees are
/// `1, 2, …` in first-use order — which is exactly what [`Unpinned`] produces.
/// So an unpinned read AGREES with reader A on every body that does not call
/// ITSELF, and DISAGREES on every body that does. The pin is needed for
/// recursion and for nothing else, and its absence is a loud disagreement
/// rather than a quiet one.
///
/// [`Unpinned`]: SelfFunc::Unpinned
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum SelfFunc {
    /// The body's own id was not supplied. Index [`SELF_FUNC_INDEX`] stays
    /// reserved and empty, callees are interned from `1`, and a self-call
    /// therefore reads as an UNRESOLVABLE callee. That disagrees loudly with
    /// reader A rather than silently agreeing with it, which is the point.
    #[default]
    Unpinned,
    /// The body's own crate-level `@func.N` id, from the chain's tag table.
    /// It occupies [`SELF_FUNC_INDEX`], so a `call @func.<id>` reads as a call
    /// to this very function.
    Pinned(u32),
}

/// The crate-level interning ids one reader observed, indexed by the canonical
/// first-use index the core module uses.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ObservedTags {
    /// canonical enum index -> the `enum.N` the artifact printed IN AN
    /// INSTRUCTION.
    ///
    /// A map rather than a vector, and filtered by USE, for the reason the
    /// `funcs` lane below is: under a chain's tag table the reader is
    /// pre-seeded with the whole `enums` lane, so the raw->canonical map holds
    /// entries this body never named. Reporting those would make
    /// `interface_aggregates::check_aggregates` compare the lane against
    /// itself. A PARAMETER type is not here either: it reaches the lane
    /// through `Tags::canon_ty` instead, which is why `ir_fs` pins an `enums`
    /// row (canonical 1, `enum.178`) that no instruction in its body names.
    pub enums: BTreeMap<u32, u32>,
    /// canonical struct index -> the `struct.N` the artifact printed IN AN
    /// INSTRUCTION. See [`ObservedTags::enums`].
    pub structs: BTreeMap<u32, u32>,
    /// canonical func index -> the `@func.N` the artifact printed.
    ///
    /// A map rather than a vector because [`SELF_FUNC_INDEX`] is present only
    /// when the body's own id was pinned; under [`SelfFunc::Unpinned`] the
    /// entries start at `1` and the hole is the declared blindness.
    pub funcs: BTreeMap<u32, u32>,
    /// canonical global index -> the `@global.N` the artifact printed.
    ///
    /// EMPTY on every BARE read (`read`, `read_with_tags`, `read_with_self`,
    /// `read_with_pins`): those entry points carry no global namespace, and a
    /// `global_addr` under them is REFUSED rather than interned, because the
    /// per-body module they emit prints a hard-coded empty `(globals)` list
    /// and a canonical index into it would denote an entry the module does
    /// not declare. Under [`read_body`] — the entry point `project` uses, with
    /// the chain's tag-table `globals` lane as the namespace — a `global_addr`
    /// resolves through that namespace (or interns above it on first use) and
    /// the raw id lands here, in canonical order, for `project` to compare
    /// against the pins. See `Reader::global_index`.
    pub globals: Vec<u32>,
    /// how the body's own id reached this read
    pub self_func: SelfFunc,
    /// How many `usize` tokens this read RESOLVED through a pinned target
    /// width. `0` for every body without the type. The chain's tag table pins
    /// the same count, and [`project`](super::project) compares the two — that
    /// comparison, not the core text, is what catches a `u64`-for-`usize`
    /// swap, because the core module deliberately spells the resolved type as
    /// the plain fixed-width integer (reader C could never reproduce a
    /// distinction Clean's `IRTy` does not have).
    pub usize_seen: u32,
    /// How many TUPLE types the body spells. Same posture as `usize_seen`:
    /// the arity-only image erases the element types, so the count is what a
    /// tag table pins and what makes a same-arity swap visible.
    pub tuple_seen: u32,
    /// Exactly how many `isize` tokens this body contained, counted the same
    /// way and pinned separately.
    pub isize_seen: u32,
    /// The `functy.N` in the header. RECORDED, never gated: it is a whole-crate
    /// signature-table index, it moves under a producer change with no
    /// instruction changed, and `scripts/crystal_fixture_freshness.py` already
    /// reports the drift as its AMBER `functy-index` class.
    pub functy: u32,
    /// The artifact facts the core module does not carry and a text reader CAN
    /// witness: the function's name, every parameter's TYPE, every `align`
    /// operand, and the kinds of trailing annotation clause. Compared against
    /// the chain's pinned table by [`project`](super::project).
    pub interface: Interface,
}

/// Read the body AND report the crate-level ids it named.
///
/// The core module deliberately does not carry those ids — they move under a
/// producer change with no instruction changed. They are reported separately so
/// a gate can check the committed tag table against the artifact without the
/// module's identity depending on them.
///
/// # Errors
/// Returns [`EmittedError`] exactly as [`read`] does.
pub fn read_with_tags(text: &str) -> Result<(Sx, ObservedTags), EmittedError> {
    read_with_self(text, SelfFunc::Unpinned)
}

/// Read the body with its own crate-level function id supplied, and report the
/// crate ids it named.
///
/// This is the entry point a gate uses when the body CALLS something. Without
/// the pin, index [`SELF_FUNC_INDEX`] is reserved and empty and a self-call
/// reads as an unresolvable callee — see [`SelfFunc`].
///
/// # Errors
/// Returns [`EmittedError`] exactly as [`read`] does.
pub fn read_with_self(text: &str, self_func: SelfFunc) -> Result<(Sx, ObservedTags), EmittedError> {
    read_with_pins(text, self_func, None)
}

/// [`read_with_self`], with the chain's pinned `usize` width supplied.
///
/// `usize` is TARGET-DEPENDENT, so this reader refuses the token unless the
/// width is stated: `None` (what every other entry point passes) keeps the
/// refusal, `Some(bits)` resolves each site to `(uint bits)` and counts it
/// into [`ObservedTags::usize_seen`] for the tag table's site-count pin.
///
/// # Errors
/// Returns [`EmittedError`] exactly as [`read`] does, plus the named `usize`
/// refusal when the width is `None` and the text contains the type.
pub fn read_with_pins(
    text: &str,
    self_func: SelfFunc,
    usize_bits: Option<u32>,
) -> Result<(Sx, ObservedTags), EmittedError> {
    // A BARE read: no global namespace, so a `global_addr` is refused — see
    // `Reader::global_index`.
    read_one(
        text,
        self_func,
        SELF_FUNC_INDEX,
        &BTreeMap::new(),
        usize_bits,
        None,
        None,
    )
}

/// Read ONE body of a chain whose module may contain several, with the chain's
/// function namespace supplied.
///
/// `self_canonical` is the index this body occupies in that namespace — `0` for
/// every one-body chain, and the reason this parameter exists at all is that a
/// SIBLING body does not occupy `0`: `loose_bvar_range` is `(func 1 …)` of the
/// module `has_loose_bvars` is `(func 0 …)` of, and a reader that wrote the
/// literal `0` for both would produce a module whose two functions share an id.
///
/// `namespace` pre-seeds crate-level `@func.N` ids that the chain's tag table
/// has already accounted for, so a call to a SIBLING body reads as that
/// sibling's canonical index rather than interning above the chain. It does not
/// weaken the read: a callee the namespace does not carry still interns, and
/// still has to be a row of the tag table, and a call to the WRONG sibling is a
/// different core module.
///
/// `global_namespace` is the chain's tag-table `globals` lane, crate-level
/// `@global.N` id -> canonical index. Its PRESENCE is what lets a
/// `global_addr` read at all: every bare entry point above carries none and
/// refuses the instruction (the per-body module prints an empty `(globals)`
/// list, so a canonical index into it would name nothing), while `project`
/// reads through this one and then checks the observed globals against the
/// pins and the module-table preamble. An id the namespace does not carry
/// still interns above it, and still has to be a row of the tag table.
///
/// # Errors
/// Returns [`EmittedError`] exactly as [`read`] does.
pub(crate) fn read_body(
    text: &str,
    self_func: SelfFunc,
    self_canonical: u32,
    namespace: &BTreeMap<u32, u32>,
    usize_bits: Option<u32>,
    global_namespace: &BTreeMap<u32, u32>,
    agg_namespace: (&BTreeMap<u32, u32>, &BTreeMap<u32, u32>),
) -> Result<(Sx, ObservedTags), EmittedError> {
    read_one(
        text,
        self_func,
        self_canonical,
        namespace,
        usize_bits,
        Some(global_namespace),
        Some(agg_namespace),
    )
}

/// The one reader every entry point goes through. `global_namespace` is
/// `None` for a bare read and `Some` under a chain's tag table; nothing else
/// distinguishes the two, and that one difference is exactly whether a
/// `global_addr` is refused or resolved.
fn read_one(
    text: &str,
    self_func: SelfFunc,
    self_canonical: u32,
    namespace: &BTreeMap<u32, u32>,
    usize_bits: Option<u32>,
    global_namespace: Option<&BTreeMap<u32, u32>>,
    agg_namespace: Option<(&BTreeMap<u32, u32>, &BTreeMap<u32, u32>)>,
) -> Result<(Sx, ObservedTags), EmittedError> {
    let mut r = Reader::with_self_at(self_func, self_canonical, namespace);
    r.usize_bits = usize_bits;
    // The AGGREGATE namespaces, the `funcs` and `globals` pattern one lane
    // over. A bare read passes none and interns from 0 in first-seen order,
    // which is what every entry point but `project` has always done. Under a
    // chain's tag table the reader starts from the lane, so two bodies of one
    // module that name DIFFERENT aggregates resolve to different canonical
    // indices instead of both claiming 0 — which is what made a module
    // assembled from two artifacts inexpressible.
    if let Some((enums, structs)) = agg_namespace {
        r.enums = enums.clone();
        r.structs = structs.clone();
    }
    if let Some(ns) = global_namespace {
        // A newly-seen global interns ABOVE everything the chain accounts
        // for, the `funcs` arithmetic one namespace over — except that no
        // index is reserved here, so with an empty lane the first one is `0`.
        r.next_global = ns
            .values()
            .copied()
            .max()
            .map_or(0, |m| m.saturating_add(1));
        r.global_namespace = Some(ns.clone());
    }
    let sx = r.run(text)?;
    let invert = |m: &BTreeMap<u32, u32>| {
        let mut v: Vec<(u32, u32)> = m.iter().map(|(raw, canon)| (*canon, *raw)).collect();
        v.sort_unstable();
        v.into_iter().map(|(_, raw)| raw).collect::<Vec<u32>>()
    };
    let entry = r.entry.unwrap_or_default();
    let (params, block_params): (Vec<ParamSlot>, Vec<ParamSlot>) = r
        .param_slots
        .iter()
        .cloned()
        .partition(|p| p.block == entry);
    let tags = ObservedTags {
        // The aggregates THIS body named in an instruction — never a
        // pre-seeded lane entry, and never a parameter type. Same shape and
        // same reason as the `funcs` lane just below.
        enums: r
            .enums
            .iter()
            .filter(|(raw, _)| r.enum_used.contains(*raw))
            .map(|(raw, canon)| (*canon, *raw))
            .collect(),
        structs: r
            .structs
            .iter()
            .filter(|(raw, _)| r.struct_used.contains(*raw))
            .map(|(raw, canon)| (*canon, *raw))
            .collect(),
        // SELF and the callees the body actually NAMED — never a pre-seeded
        // sibling the body does not call. That keeps this lane meaning what it
        // has always meant: the crate ids THIS body witnessed.
        funcs: r
            .funcs
            .iter()
            .filter(|(raw, _)| {
                r.func_used.contains(*raw)
                    || matches!(self_func, SelfFunc::Pinned(id) if id == **raw)
            })
            .map(|(raw, canon)| (*canon, *raw))
            .collect(),
        globals: invert(&r.globals),
        self_func,
        usize_seen: r.usize_seen,
        tuple_seen: r.tuple_seen,
        isize_seen: r.isize_seen,
        functy: r.functy,
        interface: Interface {
            function_name: r.fn_name.clone(),
            linkage: r.linkage.clone(),
            calling_conv: r.calling_conv.clone(),
            functy: r.functy,
            producer: r.producer.clone(),
            params,
            block_params,
            aligns: r.aligns.clone(),
            clauses: r.clauses.clone(),
        },
    };
    Ok((sx, tags))
}

/// Split an emitted trust-ir text into EXACTLY `n` function bodies.
///
/// A body ends at the line whose code is `}` — `Display for Function` always
/// emits one, at column 0, and the reader that consumes each chunk refuses a
/// text that runs out without it. Anything after the `n`-th body is REFUSED
/// with the surplus named, which is the same rule the one-body reader has
/// enforced since 2026-08-20 and for the same reason: a reader that stops early
/// and ignores the remainder is not total over its own input, and no
/// enumeration of erasures can cover what it drops.
///
/// `base` is the number of lines that precede `text` in the file it was cut
/// from — the module-table preamble `emitted_globals::split_preamble` took off
/// the front — so every `line` a refusal here names is the FILE line. It is 0
/// for every fixture without a preamble.
///
/// # Errors
/// Returns [`EmittedError`] when the text holds fewer or more than `n` bodies.
pub(crate) fn split_bodies(text: &str, n: usize, base: usize) -> Result<Vec<String>, EmittedError> {
    let mut out: Vec<String> = Vec::new();
    let mut cur = String::new();
    let mut open = false;
    for (i, raw) in text.lines().enumerate() {
        let (code, _) = reader::strip_comment(raw);
        let code = code.trim();
        if out.len() == n {
            if !code.is_empty() {
                return Err(EmittedError::Syntax {
                    line: base + i + 1,
                    msg: format!(
                        "`{code}` follows the closing brace of the last of the {n} function \
                         bod{} this chain's tag table declares. A text carrying an extra \
                         function, a module table or anything else is not the artifact the table \
                         describes, and reading it would drop the surplus unread",
                        if n == 1 { "y" } else { "ies" }
                    ),
                });
            }
            continue;
        }
        cur.push_str(raw);
        cur.push('\n');
        if !code.is_empty() {
            open = true;
        }
        if code == "}" {
            out.push(std::mem::take(&mut cur));
            open = false;
        }
    }
    if open {
        return Err(EmittedError::Syntax {
            line: base + text.lines().count(),
            msg: "the last function body has no closing brace. `Display for Function` always \
                  emits one, so text that runs out without it is a TRUNCATED artifact — and \
                  reading a truncated body as a complete one is the same erasure as ignoring a \
                  tail, from the other end"
                .into(),
        });
    }
    if out.len() != n {
        return Err(EmittedError::Syntax {
            line: base + text.lines().count(),
            msg: format!(
                "this chain's tag table declares {n} function bod{}, and the emitted text holds \
                 {}",
                if n == 1 { "y" } else { "ies" },
                out.len()
            ),
        });
    }
    Ok(out)
}

pub(super) struct Reader {
    enums: BTreeMap<u32, u32>,
    structs: BTreeMap<u32, u32>,
    funcs: BTreeMap<u32, u32>,
    /// The crate-level `@func.N` ids a `call` in THIS body actually named.
    func_used: BTreeSet<u32>,
    /// The aggregate ids this body named IN AN INSTRUCTION, as opposed to the
    /// ones pre-seeded from the chain's lanes.
    enum_used: BTreeSet<u32>,
    struct_used: BTreeSet<u32>,
    /// The next canonical index a newly-seen callee takes.
    next_func: u32,
    /// The canonical index this body's own `(func N …)` carries.
    self_canonical: u32,
    /// The crate-level `@global.N` ids a `global_addr` in THIS body named,
    /// each at its canonical index. Only ever populated under a namespace.
    globals: BTreeMap<u32, u32>,
    /// The chain's tag-table `globals` lane (crate id -> canonical), or
    /// `None` on a bare read — in which case a `global_addr` is refused.
    global_namespace: Option<BTreeMap<u32, u32>>,
    /// The next canonical index a newly-seen global takes, above the lane.
    next_global: u32,
    line: usize,
    fn_name: String,
    /// The header's linkage keyword, PRE-SET to the value the producer
    /// suppresses. A header that prints none leaves this untouched and that is
    /// the reading, not a default standing in for a missing one.
    linkage: String,
    /// The header's calling-convention keyword, same rule.
    calling_conv: String,
    functy: u32,
    producer: Option<String>,
    entry: Option<u32>,
    param_slots: Vec<ParamSlot>,
    aligns: Vec<String>,
    clauses: BTreeSet<String>,
    usize_bits: Option<u32>,
    usize_seen: u32,
    tuple_seen: u32,
    isize_seen: u32,
}

impl Default for Reader {
    fn default() -> Self {
        Self {
            enums: BTreeMap::new(),
            structs: BTreeMap::new(),
            funcs: BTreeMap::new(),
            func_used: BTreeSet::new(),
            enum_used: BTreeSet::new(),
            struct_used: BTreeSet::new(),
            next_func: 1,
            self_canonical: SELF_FUNC_INDEX,
            globals: BTreeMap::new(),
            global_namespace: None,
            next_global: 0,
            line: 0,
            fn_name: String::new(),
            linkage: DEFAULT_LINKAGE.to_string(),
            calling_conv: DEFAULT_CALLING_CONV.to_string(),
            functy: 0,
            producer: None,
            entry: None,
            param_slots: Vec::new(),
            aligns: Vec::new(),
            clauses: BTreeSet::new(),
            usize_bits: None,
            usize_seen: 0,
            tuple_seen: 0,
            isize_seen: 0,
        }
    }
}

/// The linkage keywords `trust_ir::Display for Function` can print before `fn`.
///
/// A CLOSED list, matched exactly. `external` is in it because trust-ir's
/// PARSER accepts it (`is_func_prefix`) even though the printer suppresses it,
/// and a reader that refused text its own producer's parser accepts would be
/// wrong about the format rather than strict about it.
pub const LINKAGES: [&str; 5] = ["external", "internal", "linkonce", "private", "weak"];

/// The calling-convention keywords the same printer can print, from
/// `impl Display for CallingConv`.
pub const CALLING_CONVS: [&str; 5] = ["ccc", "coldcc", "fastcc", "rustcc", "swiftcc"];

/// The linkage a header that prints no linkage keyword carries:
/// `Linkage::External`, which `Display for Function` suppresses.
pub const DEFAULT_LINKAGE: &str = "external";

/// The calling convention a header that prints no convention keyword carries:
/// `CallingConv::C`, which `Display for Function` suppresses and
/// `try_parse_calling_conv` restores.
pub const DEFAULT_CALLING_CONV: &str = "ccc";

/// The trailing-annotation clause kinds this reader knows are inert.
///
/// It is an ALLOWLIST, and that is the point. Until 2026-08-20 the reader
/// dropped every `  ; #…` suffix whatever it said, so a producer that started
/// annotating an instruction with something trust-bearing would have been
/// erased in silence — the exact failure the `exhaustive_enum_unreachable`
/// flag already demonstrates one level in. An unlisted kind is now a refusal,
/// which forces a review instead of an erasure.
///
/// Each entry is listed for a stated reason, and since 2026-08-20 the list
/// separates the kinds whose CONTENT is erased from the one whose content is
/// not:
///
/// * `#loc` (file-table index, line, column) and `#scope` (an index into the
///   function's own scope tree) are debug-info coordinates. Their content is
///   erased, and that erasure is now MEASURED rather than asserted: two bodies
///   differing only in `#loc` content denote the same program, so a gate that
///   separated them would be refusing a pair it has no business refusing.
/// * `#names` is the source-level name of an SSA id — debug info in the same
///   sense.
/// * `#proof` is a claim ABOUT the body, not part of it. `ir_exec` has no proof
///   notion, so the content cannot change what the module computes. It is
///   erased deliberately and this sentence is the record of that decision.
/// * `#producer` is the exception. Its content names WHICH COMPILER emitted the
///   function, which is the very fact link 2a exists to establish, and it does
///   not renumber. It is READ and COMPARED — see
///   [`Interface::producer`](super::Interface::producer).
pub const CLAUSE_KINDS: [&str; 5] = ["loc", "names", "producer", "proof", "scope"];

#[path = "emitted_reader.rs"]
mod reader;

impl Reader {
    /// A reader that knows (or does not know) which crate-level id the body it
    /// is about to read belongs to.
    ///
    /// The pin is applied by interning the own id FIRST, so it takes
    /// [`SELF_FUNC_INDEX`] and every callee is pushed above it.
    fn with_self_at(
        self_func: SelfFunc,
        self_canonical: u32,
        namespace: &BTreeMap<u32, u32>,
    ) -> Self {
        let mut r = Self {
            self_canonical,
            ..Self::default()
        };
        if let SelfFunc::Pinned(id) = self_func {
            r.funcs.insert(id, self_canonical);
            r.next_func = 1;
        }
        for (id, canonical) in namespace {
            r.funcs.insert(*id, *canonical);
        }
        // A newly-seen callee interns ABOVE everything the chain accounts for.
        // With no namespace and a pinned self this is `1`, and with no pin it is
        // `1` as well — index 0 stays reserved and empty. Both are exactly the
        // pre-2026-08-23 arithmetic; the max is what a multi-body chain needs.
        r.next_func = r
            .funcs
            .values()
            .copied()
            .max()
            .map_or(1, |m| m.saturating_add(1))
            .max(1);
        r
    }

    fn syn(&self, msg: impl Into<String>) -> EmittedError {
        EmittedError::Syntax {
            line: self.line,
            msg: msg.into(),
        }
    }

    fn core(&self, e: CoreError) -> EmittedError {
        EmittedError::Core {
            line: self.line,
            source: e,
        }
    }

    fn intern(map: &mut BTreeMap<u32, u32>, id: u32) -> u32 {
        let n = u32::try_from(map.len()).unwrap_or(u32::MAX);
        *map.entry(id).or_insert(n)
    }

    /// The canonical index of a crate-level function id, in the ONE namespace
    /// the function's own id also lives in.
    ///
    /// Under [`SelfFunc::Pinned`] the own id is already interned at
    /// [`SELF_FUNC_INDEX`], so it is returned for the self-call and callees
    /// intern above it. Under [`SelfFunc::Unpinned`] the reserved index is left
    /// empty and callees start at `1`, so no callee can ever be mistaken for
    /// the body.
    fn func_index(&mut self, id: u32) -> u32 {
        self.func_used.insert(id);
        if let Some(n) = self.funcs.get(&id) {
            return *n;
        }
        let n = self.next_func;
        self.next_func = n.saturating_add(1);
        self.funcs.insert(id, n);
        n
    }

    fn val(&mut self, tok: &str) -> Result<u32, EmittedError> {
        tok.trim()
            .strip_prefix('%')
            .and_then(|n| n.parse::<u32>().ok())
            .ok_or_else(|| self.syn(format!("`{tok}` is not an SSA value")))
    }

    fn blk(&mut self, tok: &str) -> Result<u32, EmittedError> {
        tok.trim()
            .strip_prefix("bb")
            .and_then(|n| n.parse::<u32>().ok())
            .ok_or_else(|| self.syn(format!("`{tok}` is not a block label")))
    }

    fn node(&mut self, line: &str) -> Result<Sx, EmittedError> {
        let (results, body) = match line.split_once(" = ") {
            Some((lhs, rhs)) if lhs.starts_with('%') => {
                (vec![Sx::a(self.val(lhs)?.to_string())], rhs)
            }
            _ => (Vec::new(), line),
        };
        let inst = self.inst(body.trim())?;
        Ok(Sx::tag("node", vec![Sx::tag("results", results), inst]))
    }

    fn ty(&mut self, s: &str) -> Result<Sx, EmittedError> {
        let s = s.trim();
        let t = |k: &str| Ok(Sx::tag(k, vec![]));
        let n = |k: &str, w: &str| Ok(Sx::tag(k, vec![Sx::a(w.to_string())]));
        match s {
            "bool" => t("bool"),
            "ptr" => t("ptr"),
            "()" => t("unit"),
            "!" => t("never"),
            "i8" => n("int", "8"),
            "i16" => n("int", "16"),
            "i32" => n("int", "32"),
            "i64" => n("int", "64"),
            "i128" => n("int", "128"),
            "u8" => n("uint", "8"),
            "u16" => n("uint", "16"),
            "u32" => n("uint", "32"),
            "u64" => n("uint", "64"),
            "u128" => n("uint", "128"),
            // A TUPLE, spelled `(a, b, ...)` by the producer. `IRTy.tuple_`
            // takes a Nat and the reflected module has no tuple table to index,
            // so that Nat is the ARITY -- and the element types are ERASED.
            //
            // Counted, exactly as `usize` is and for the same reason: two tuple
            // types of the same arity read to the SAME `(tuple k)`, so the core
            // text cannot tell `(u32, bool)` from `(u64, ptr)`. The count is what
            // a tag table can pin and what makes that swap visible; the resolved
            // core is not asked to carry it.
            _ if s.starts_with('(') && s.ends_with(')') && s.contains(',') => {
                let inner = &s[1..s.len() - 1];
                let mut depth = 0i32;
                let mut arity = 1usize;
                for c in inner.chars() {
                    match c {
                        '(' | '<' | '[' => depth += 1,
                        ')' | '>' | ']' => depth -= 1,
                        ',' if depth == 0 => arity += 1,
                        _ => {}
                    }
                }
                self.tuple_seen += 1;
                n("tuple", &arity.to_string())
            }
            "usize" => match self.usize_bits {
                // Resolved to the plain fixed-width integer and COUNTED. The
                // core module does not remember the token was `usize` -- the
                // registered kernel term has no way to say so -- and the
                // recorded posture is the site count the tag table pins.
                Some(bits) => {
                    self.usize_seen += 1;
                    n("uint", &bits.to_string())
                }
                None => Err(self.core(CoreError::NoImage(format!(
                    "type `{s}` without a pinned target width: `usize` is TARGET-DEPENDENT, and \
                     resolving it silently would bake an unstated word-size assumption into the \
                     core module. Pin the chain's tag-table `usize` lane (a target fact) and \
                     read through it."
                )))),
            },
            // `isize` rides the SAME pin as `usize`, and that is a language
            // guarantee rather than a convenience: Rust defines both as the
            // width of the platform's pointer, so a target where they differ
            // does not exist to be wrong about. What is NOT shared is the site
            // count -- the tag table pins `usize` and `isize` sites
            // separately, so a chain cannot satisfy one token's pin with the
            // other's occurrences.
            //
            // Resolved to the SIGNED fixed-width integer. The core module does
            // not remember the token was `isize`, exactly as it does not
            // remember `usize`; the recorded posture is the site count.
            "isize" => match self.usize_bits {
                Some(bits) => {
                    self.isize_seen += 1;
                    n("int", &bits.to_string())
                }
                None => Err(self.core(CoreError::NoImage(format!(
                    "type `{s}` without a pinned target width: `isize` is TARGET-DEPENDENT, and \
                     resolving it silently would bake an unstated word-size assumption into the \
                     core module. Pin the chain's tag-table `usize` lane (a target fact -- Rust \
                     defines `isize` and `usize` as the same width) and read through it."
                )))),
            },
            "f32" => n("float", "32"),
            "f64" => n("float", "64"),
            _ => {
                if let Some(k) = s.strip_prefix("enum.") {
                    let id = k.parse::<u32>().map_err(|_| self.syn("bad enum id"))?;
                    let k = Self::intern(&mut self.enums, id);
                    self.enum_used.insert(id);
                    return n("enum", &k.to_string());
                }
                if let Some(k) = s.strip_prefix("struct.") {
                    let id = k.parse::<u32>().map_err(|_| self.syn("bad struct id"))?;
                    let k = Self::intern(&mut self.structs, id);
                    self.struct_used.insert(id);
                    return n("struct", &k.to_string());
                }
                if let Some(kind) = s.strip_prefix("fatptr<").and_then(|x| x.strip_suffix('>')) {
                    // `&str` images as a fat pointer to bytes,
                    // `IRTy.fatptr_ (IRTy.uint_ 8)`; crystal E5 (decision memo
                    // §23) gives the M0 producer's three other kinds their OWN
                    // constructors: `container_len` -> `(containerlen)`,
                    // `container_vtable` -> `(containervtable)`, and `dyn.N` ->
                    // `(fatdyn N)`, keeping the trait id. Reader A spells them
                    // the same way. `slice ty.N` stays REFUSED here and in reader
                    // A alike, which is what keeps the image INJECTIVE on the
                    // accepted fragment: `fatptr` takes one type argument
                    // (`shape.rs`), so str and slice would collapse if both were
                    // accepted. The pointer-type operand is inert at evaluation;
                    // since E5 the METADATA type of `ptr_metadata` is not (the
                    // machine reads the word at it), which is why it is spelled
                    // exactly rather than erased.
                    if kind == "str" {
                        return Ok(Sx::tag("fatptr", vec![n("uint", "8")?]));
                    }
                    if kind == "container_len" {
                        return t("containerlen");
                    }
                    if kind == "container_vtable" {
                        return t("containervtable");
                    }
                    if let Some(id) = kind.strip_prefix("dyn.") {
                        let trait_id = id
                            .parse::<u32>()
                            .map_err(|_| self.syn(format!("bad trait id in `{s}`")))?;
                        return n("fatdyn", &trait_id.to_string());
                    }
                    return Err(self.core(CoreError::NoImage(format!(
                        "fat pointer kind `{kind}` in type `{s}`: `str`, `container_len`, \
                         `container_vtable` and `dyn.N` have declared images; a `slice ty.N` fat \
                         pointer is REFUSED in both readers so that the image stays injective on \
                         the accepted fragment"
                    ))));
                }
                Err(self.core(CoreError::NoImage(format!("type `{s}`"))))
            }
        }
    }

    fn cst(&mut self, s: &str) -> Result<Sx, EmittedError> {
        let s = s.trim();
        if s == "true" || s == "false" {
            return Ok(Sx::tag("bool", vec![Sx::a(s.to_string())]));
        }
        if let Some(inner) = s.strip_prefix('{').and_then(|x| x.strip_suffix('}')) {
            let mut elems = vec![];
            for e in inner.split(',').map(str::trim).filter(|e| !e.is_empty()) {
                // Crystal E3b: an UNWRITTEN aggregate lane (trust-ir `Constant::Uninit`, printed
                // `uninit`) images as `(undef)` -- `IRConst.undef_`, which `ir_const_value`
                // materialises as the `IRScalar.undef_` lane the machine already gives an
                // unwritten cell: `ir_insert_field` replaces it, `ir_ef_at` hands it back, and
                // every evaluator that needs a value rejects it. Read ONLY as a lane: a whole
                // constant `uninit` falls through to the refusal below, as trust-ir's validator
                // refuses it.
                if e == "uninit" {
                    elems.push(Sx::tag("undef", vec![]));
                    continue;
                }
                elems.push(self.cst(e)?);
            }
            return Ok(Sx::tag("agg", elems));
        }
        if s.chars().all(|c| c.is_ascii_digit()) && !s.is_empty() {
            return Ok(Sx::tag("int", vec![Sx::a(s.to_string())]));
        }
        if s == "phantomdata" {
            // The zero-sized marker, 2026-09-16. Read as its OWN tag, never
            // rewritten to `unit`: the producer keeps `Constant::PhantomData`
            // distinct (trust_ir constant.rs:140) and prints it by this name,
            // so merging the two here would make two different emitted bodies
            // project to one core module and reader B would stop being able to
            // tell them apart.
            return Ok(Sx::tag("phantomdata", vec![]));
        }
        Err(self.core(CoreError::NoImage(format!("constant literal `{s}`"))))
    }

    fn args(&mut self, s: &str) -> Result<Vec<Sx>, EmittedError> {
        let mut out = Vec::new();
        for a in s.split(',').map(str::trim).filter(|a| !a.is_empty()) {
            out.push(Sx::a(self.val(a)?.to_string()));
        }
        Ok(out)
    }

    /// `bb4(%3, %4)` or `bb4` — the target and its block arguments.
    fn target(&mut self, s: &str) -> Result<(u32, Vec<Sx>), EmittedError> {
        let s = s.trim();
        match s.find('(') {
            Some(p) => {
                let inner = s[p..]
                    .strip_prefix('(')
                    .and_then(|x| x.strip_suffix(')'))
                    .ok_or_else(|| self.syn("unbalanced block-argument list"))?;
                Ok((self.blk(&s[..p])?, self.args(inner)?))
            }
            None => Ok((self.blk(s)?, Vec::new())),
        }
    }

    fn inst(&mut self, s: &str) -> Result<Sx, EmittedError> {
        super::emitted_inst::parse(self, s)
    }
}

// The instruction-form reader is large enough to own its file; it is the only
// part of this reader that has to know trust-ir's printed grammar form by
// form.
pub(super) type EmittedReader = Reader;

impl Reader {
    pub(super) fn e_syn(&self, m: String) -> EmittedError {
        self.syn(m)
    }
    pub(super) fn e_core(&self, e: CoreError) -> EmittedError {
        self.core(e)
    }
    pub(super) fn r_val(&mut self, t: &str) -> Result<u32, EmittedError> {
        self.val(t)
    }
    pub(super) fn r_ty(&mut self, t: &str) -> Result<Sx, EmittedError> {
        self.ty(t)
    }
    pub(super) fn r_cst(&mut self, t: &str) -> Result<Sx, EmittedError> {
        self.cst(t)
    }
    pub(super) fn r_args(&mut self, t: &str) -> Result<Vec<Sx>, EmittedError> {
        self.args(t)
    }
    pub(super) fn r_target(&mut self, t: &str) -> Result<(u32, Vec<Sx>), EmittedError> {
        self.target(t)
    }
    pub(super) fn r_func(&mut self, id: u32) -> u32 {
        self.func_index(id)
    }
    pub(super) fn self_canonical(&self) -> u32 {
        self.self_canonical
    }
    /// The canonical index of a crate-level `@global.N` id — or a REFUSAL on
    /// a bare read, which is the `global-index` blind slot kept closed on the
    /// path that cannot account for it.
    ///
    /// Both readers used to intern the global id for the instruction and then
    /// emit `(globals)` — a hard-coded EMPTY list — so `(globaladdr 0)` named
    /// an entry the module does not declare. That is the 2026-08-20 callee
    /// collision's exact shape, one namespace out, and it was latent only
    /// because no chained body addressed a global (measured: all eleven, then
    /// all eighteen). From 2026-08-20 to 2026-09-09 the instruction was
    /// refused outright. It is now read on exactly ONE path: under a chain's
    /// tag-table `globals` lane, via [`read_body`], where `project` goes on to
    /// compare every observed global against its pin and the module-table
    /// preamble that carries its bytes. A BARE read still emits the empty
    /// list and still refuses — the message names the global and the empty
    /// list that would make the module incoherent, and now says where to
    /// read it instead.
    ///
    /// Under a namespace this is the `func_index` pattern one namespace over:
    /// a pinned id resolves to its canonical index, an unpinned one interns
    /// above the lane on first use, and either way the raw id is recorded so
    /// [`ObservedTags::globals`] reports what THIS body addressed.
    pub(super) fn global_index(&mut self, id: u32) -> Result<u32, EmittedError> {
        let Some(ns) = &self.global_namespace else {
            return Err(self.core(CoreError::NoImage(format!(
                "`global_addr @global.{id}`: a bare read emits a module whose `(globals)` list \
                 is empty, so a canonical global index would denote an entry the module does \
                 not declare; read it through project under a tag table with a globals lane"
            ))));
        };
        if let Some(n) = self.globals.get(&id) {
            return Ok(*n);
        }
        let n = match ns.get(&id) {
            Some(pinned) => *pinned,
            None => {
                let n = self.next_global;
                self.next_global = n.saturating_add(1);
                n
            }
        };
        self.globals.insert(id, n);
        Ok(n)
    }

    /// Record a memory instruction's alignment operand, in reader A's own
    /// spelling (`load:None`, `load:Some(8)`), so the two records compare.
    pub(super) fn r_align(&mut self, slot: String) {
        self.aligns.push(slot);
    }
}

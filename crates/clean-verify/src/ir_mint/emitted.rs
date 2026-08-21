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
    /// canonical enum index -> the `enum.N` the artifact printed
    pub enums: Vec<u32>,
    /// canonical struct index -> the `struct.N` the artifact printed
    pub structs: Vec<u32>,
    /// canonical func index -> the `@func.N` the artifact printed.
    ///
    /// A map rather than a vector because [`SELF_FUNC_INDEX`] is present only
    /// when the body's own id was pinned; under [`SelfFunc::Unpinned`] the
    /// entries start at `1` and the hole is the declared blindness.
    pub funcs: BTreeMap<u32, u32>,
    /// canonical global index -> the `@global.N` the artifact printed.
    ///
    /// Always EMPTY today, and not because no body has a global: the reader
    /// REFUSES a `global_addr` outright, so an interned one can never reach
    /// here. See `Reader::r_global`.
    pub globals: Vec<u32>,
    /// how the body's own id reached this read
    pub self_func: SelfFunc,
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
    let mut r = Reader::with_self(self_func);
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
        enums: invert(&r.enums),
        structs: invert(&r.structs),
        funcs: r.funcs.iter().map(|(raw, canon)| (*canon, *raw)).collect(),
        globals: invert(&r.globals),
        self_func,
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

pub(super) struct Reader {
    enums: BTreeMap<u32, u32>,
    structs: BTreeMap<u32, u32>,
    funcs: BTreeMap<u32, u32>,
    globals: BTreeMap<u32, u32>,
    self_func: SelfFunc,
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
}

impl Default for Reader {
    fn default() -> Self {
        Self {
            enums: BTreeMap::new(),
            structs: BTreeMap::new(),
            funcs: BTreeMap::new(),
            globals: BTreeMap::new(),
            self_func: SelfFunc::default(),
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
    fn with_self(self_func: SelfFunc) -> Self {
        let mut r = Self {
            self_func,
            ..Self::default()
        };
        if let SelfFunc::Pinned(id) = self_func {
            r.funcs.insert(id, SELF_FUNC_INDEX);
        }
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
        if let Some(n) = self.funcs.get(&id) {
            return *n;
        }
        let used = u32::try_from(self.funcs.len()).unwrap_or(u32::MAX);
        let n = match self.self_func {
            SelfFunc::Pinned(_) => used,
            SelfFunc::Unpinned => used.saturating_add(1),
        };
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
            "f32" => n("float", "32"),
            "f64" => n("float", "64"),
            _ => {
                if let Some(k) = s.strip_prefix("enum.") {
                    let id = k.parse::<u32>().map_err(|_| self.syn("bad enum id"))?;
                    return n("enum", &Self::intern(&mut self.enums, id).to_string());
                }
                if let Some(k) = s.strip_prefix("struct.") {
                    let id = k.parse::<u32>().map_err(|_| self.syn("bad struct id"))?;
                    return n("struct", &Self::intern(&mut self.structs, id).to_string());
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
                elems.push(self.cst(e)?);
            }
            return Ok(Sx::tag("agg", elems));
        }
        if s.chars().all(|c| c.is_ascii_digit()) && !s.is_empty() {
            return Ok(Sx::tag("int", vec![Sx::a(s.to_string())]));
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
    /// A `global_addr` is REFUSED, and that is the `global-index` blind slot
    /// being closed rather than tolerated.
    ///
    /// Both readers used to intern the global id for the instruction and then
    /// emit `(globals)` — a hard-coded EMPTY list — so `(globaladdr 0)` named
    /// an entry the module does not declare. That is the 2026-08-20 callee
    /// collision's exact shape, one namespace out, and it was latent only
    /// because no chained body addresses a global (measured: all eleven).
    /// `mint` already refuses a non-empty global list and `decode` refuses a
    /// module with globals in it, so a body with a global could never have been
    /// minted anyway — it could only have been read into an incoherent core
    /// module. It is now refused at the read.
    pub(super) fn r_global(&mut self, id: u32) -> Result<u32, EmittedError> {
        Err(self.core(CoreError::NoImage(format!(
            "`global_addr @global.{id}`: this reader emits a module whose `(globals)` list is \
             empty, so a canonical global index would denote an entry the module does not \
             declare. Projecting one needs the global list to be projected too — which is a \
             producer-side and minter-side change, not a reader-side default"
        ))))
    }

    /// Record a memory instruction's alignment operand, in reader A's own
    /// spelling (`load:None`, `load:Some(8)`), so the two records compare.
    pub(super) fn r_align(&mut self, slot: String) {
        self.aligns.push(slot);
    }
}

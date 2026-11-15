// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The tag table: where crate-level interning ids live, so that the proved
//! module does not carry them.**
//!
//! Two facts about `%2 = load enum.13, ptr %0` are kept apart on purpose:
//!
//! 1. **which aggregate slot the body reads**, and whether two slots are the
//!    same type. That is a property of the BODY. The core module carries it as
//!    a canonical FIRST-USE index, and it is producer-stable.
//! 2. **which crate table entry the artifact named.** That is a property of the
//!    BUILD. Measured over three producer dumps of the shipped kernel,
//!    `has_cubical_layer`'s id did not move and `expr_path_step_clone`'s moved
//!    181 → 176 with not one instruction changed.
//!
//! Folding (2) into the module the theorems are about makes a re-interning look
//! like a proof about a different program — the false-alarm failure mode a gate
//! over emitted IR dies of. Keeping it here makes a re-interning a one-line
//! reviewed change to a committed table.
//!
//! The registered term still carries the crate id, because the 2026-08-19
//! load-type correction is right that a model which cannot tell `enum.13` from
//! `enum.0` cannot see a wrong load: [`mint`](super::mint) emits the alias
//! `def ir_h2_tmode : IRTy := IRTy.enum_ ir_d13` from this table and has the
//! body load it. What changed is where the 13 comes from — a reviewed table
//! that a gate checks against the artifact, instead of a literal in a term.

use std::collections::BTreeMap;

use super::error::CoreError;
use super::interface::{Interface, ParamSlot};
use super::tags_encodings::encodings_lane;
pub(crate) use super::tags_encodings::{EncKind, EncPin};

/// One aggregate namespace's canonical-index → crate-id map, plus the Clean
/// alias minted for each entry.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Tags {
    /// canonical first-use index → (crate-level id, alias name)
    pub enums: BTreeMap<u32, (u32, String)>,
    /// canonical first-use index → (crate-level id, alias name)
    pub structs: BTreeMap<u32, (u32, String)>,
    /// canonical index → (crate-level `@func.N` id, the function's NAME).
    ///
    /// Canonical index [`SELF_FUNC_INDEX`](super::SELF_FUNC_INDEX) is the
    /// body's OWN entry; the rest are its callees in first-use order.
    ///
    /// This lane exists for a different reason than `enums` and `structs`, and
    /// the difference is the whole point. Those two pin a BUILD fact so it can
    /// stay out of the module's identity. This one pins an IDENTITY fact the
    /// emitted text cannot express at all: the text names the body by name and
    /// its callees by whole-crate index, so nothing in the text says which
    /// index is the body itself. Recording the name alongside the id makes the
    /// stable half reviewable and the moving half re-pinnable, and it is what
    /// lets reader B resolve a self-call — see [`SelfFunc`](super::SelfFunc).
    pub funcs: BTreeMap<u32, (u32, String)>,
    /// The name of the body this chain is about, as the `rustcc fn @…` header
    /// spells it.
    ///
    /// Unlike the three lanes above this is a STABLE fact, and it is recorded
    /// for the opposite reason: the ids move and the name does not. Measured
    /// over the three producer dumps of `ir_mint.producer_ab.json`, every
    /// `@func.N` moved and no `crate_func_names_seen` entry did.
    pub body: String,
    /// The artifact's INTERFACE: the facts the core module cannot hold and the
    /// emitted text does print. See [`super::interface`].
    pub interface: Interface,
    /// The `usize` TARGET FACT, present only on a chain whose body contains
    /// the type. `usize` is target-dependent; a table without this lane keeps
    /// both text readers fail-closed on the token, and a table with it states
    /// the resolved width (a fact about the recorded producer target, never an
    /// assumption) and the exact number of sites the body resolves, which is
    /// what catches a `u64`-for-`usize` swap the resolved core text cannot.
    pub usize_pin: Option<UsizePin>,
    /// The chain's NON-ROOT bodies: canonical function index → (the Clean name
    /// prefix its definitions carry, its own interface).
    ///
    /// EMPTY for every one-body chain, which is all seventeen that came before
    /// `has_loose_bvars` — and the emptiness is what keeps their minted
    /// scripts byte-identical under this lane's arrival.
    ///
    /// A chain is more than one body when the emitted MODULE contains more
    /// than one function, which is a different fact from calling one:
    /// `level_is_zero` calls `<LevelArc as Deref>::deref` and its module
    /// defines only itself, so its `funcs` lane has two rows and this lane has
    /// none. Here both `has_loose_bvars` and `loose_bvar_range` are DEFINED in
    /// the module — that is what makes `ir_call_exec` resolve rather than go
    /// `stuck no_func` — so the callee needs a name prefix of its own and an
    /// interface of its own, and both are pinned here rather than written by
    /// hand into the specification.
    pub extra_bodies: BTreeMap<u32, (String, Interface)>,
    /// The chain's MODULE-TABLE GLOBALS: canonical global index → the identity
    /// the core module cannot hold.
    ///
    /// EMPTY for every chain before `ir_lzc`, and the emptiness is what keeps
    /// their committed tables parsing unchanged under this lane's arrival: a
    /// table that omits the lane reads as "this module's global list is
    /// empty", which is what all eighteen chains and `ir_lzb` measured.
    ///
    /// `IRGlobal.mk : Nat -> IRConst` carries the global's id and its
    /// initializer and NOTHING else — no type slot, no linkage slot. So the
    /// array TYPE (`[u8 x 34]`) and the linkage (`internal`) are the
    /// `param-type` pattern over again: erased from the module, pinned here,
    /// and COMPARED by `project` (a `compared` ledger row, never an `erased`
    /// one). The NAME is the stable half, exactly as it is for `funcs`: the
    /// `@global.N` id moves under a producer re-interning and the name does
    /// not, and reader B resolves the module-table row by that name.
    pub(crate) globals: BTreeMap<u32, GlobalPin>,
    /// The chain's ENCODINGS lane: how an aggregate's byte image decodes.
    ///
    /// Empty for every chain minted before Phase B, and the minter emits
    /// `IRModule.mk` when it is empty — so those chains keep their exact terms
    /// and `ir_mod_encs` sends them to the empty table, where the
    /// encoding-aware load iota-reduces to the identity. A chain WITH rows is
    /// minted as `IRModule.mkv`.
    ///
    /// Rows are DERIVED from the artifact's `EnumLayoutDescriptor`s by reader
    /// A and refused clause by clause; `IREnc`'s own rule is that a hand-typed
    /// row is never a pin, so a row here that reader A did not derive is a
    /// fabrication and `crystal_a2_mint`'s M7 lane compares the two.
    pub(crate) encodings: Vec<EncPin>,
}

/// One pinned module-table global — see [`Tags::globals`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct GlobalPin {
    /// The crate-level `@global.N` id the artifact names — the MOVING half.
    pub crate_id: u32,
    /// The global's name as the module table spells it, without the `@`
    /// (`__trust_promoted_4557`) — the STABLE half a reviewer checks.
    pub name: String,
    /// The RESOLVED array type, `[u8 x 34]`: the element resolved through the
    /// dump's `type ty.N = …` table, never the raw `[ty.N x LEN]` token, which
    /// is a whole-crate type-table index and renumbers like every other one.
    /// A row may also carry `observed_ty` with that raw token; it is recorded
    /// for review and never compared, like a param row's `observed_ty`.
    pub ty: String,
    /// The linkage keyword, one of [`LINKAGES`](super::LINKAGES). Pinned
    /// rather than defaulted for the reason `interface.linkage` is: the
    /// printer emits it only when it is not the default.
    pub linkage: String,
}

/// The pinned resolution of `usize` for one chain — a TARGET fact.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UsizePin {
    /// The width `usize` resolves to on the recorded producer target.
    pub bits: u32,
    /// Exactly how many `usize` tokens the chain's emitted body contains.
    pub sites: u32,
    /// Exactly how many `isize` tokens it contains. Same width by Rust's own
    /// definition, so the same `bits`; a SEPARATE count, so one token's pin
    /// cannot be satisfied by the other's occurrences. Absent means zero,
    /// which is what every chain before the Phase-B callee bodies measured.
    pub isize_sites: u32,
}

impl Tags {
    /// The alias and crate id for a canonical enum index.
    ///
    /// # Errors
    /// Returns [`CoreError::NoImage`] when the table does not list the index —
    /// fail-closed, because minting an unlisted aggregate would have to invent
    /// a crate id.
    pub fn enum_alias(&self, canonical: u32) -> Result<&(u32, String), CoreError> {
        self.enums.get(&canonical).ok_or_else(|| {
            CoreError::NoImage(format!(
                "enum canonical index {canonical} is not in the chain's tag table; the crate-level \
                 id it carries in the artifact is not recorded, and minting one would invent it"
            ))
        })
    }

    /// The alias and crate id for a canonical struct index.
    ///
    /// # Errors
    /// Returns [`CoreError::NoImage`] when the table does not list the index.
    pub(crate) fn struct_alias(&self, canonical: u32) -> Result<&(u32, String), CoreError> {
        self.structs.get(&canonical).ok_or_else(|| {
            CoreError::NoImage(format!(
                "struct canonical index {canonical} is not in the chain's tag table"
            ))
        })
    }

    /// The canonical index a crate-level enum id maps back to.
    ///
    /// # Errors
    /// Returns [`CoreError::NoImage`] when no entry carries that crate id.
    pub(crate) fn enum_canonical(&self, crate_id: u32) -> Result<u32, CoreError> {
        self.enums
            .iter()
            .find(|(_, (id, _))| *id == crate_id)
            .map(|(c, _)| *c)
            .ok_or_else(|| {
                CoreError::NoImage(format!(
                    "the registered term names enum id {crate_id}, which the chain's tag table \
                     does not list. Either the artifact was re-interned and the table needs a \
                     reviewed update, or the term is about a different type."
                ))
            })
    }

    /// The canonical index a crate-level struct id maps back to.
    ///
    /// # Errors
    /// Returns [`CoreError::NoImage`] when no entry carries that crate id.
    pub(crate) fn struct_canonical(&self, crate_id: u32) -> Result<u32, CoreError> {
        self.structs
            .iter()
            .find(|(_, (id, _))| *id == crate_id)
            .map(|(c, _)| *c)
            .ok_or_else(|| {
                CoreError::NoImage(format!(
                    "the registered term names struct id {crate_id}, which the chain's tag table \
                     does not list"
                ))
            })
    }

    /// The crate-level id and NAME recorded for a canonical function index.
    ///
    /// # Errors
    /// Returns [`CoreError::NoImage`] when the table does not list the index —
    /// fail-closed, exactly as the aggregate lanes are, because a callee index
    /// with no recorded identity is a numeral standing for nothing.
    pub fn func_pin(&self, canonical: u32) -> Result<&(u32, String), CoreError> {
        self.funcs.get(&canonical).ok_or_else(|| {
            CoreError::NoImage(format!(
                "function canonical index {canonical} is not in the chain's tag table; the \
                 crate-level id and the name it carries in the artifact are not recorded, so \
                 nothing pins WHICH function this index denotes"
            ))
        })
    }

    /// The canonical index a crate-level function id maps back to.
    ///
    /// # Errors
    /// Returns [`CoreError::NoImage`] when no entry carries that crate id.
    #[cfg(test)]
    pub(crate) fn func_canonical(&self, crate_id: u32) -> Result<u32, CoreError> {
        self.funcs
            .iter()
            .find(|(_, (id, _))| *id == crate_id)
            .map(|(c, _)| *c)
            .ok_or_else(|| {
                CoreError::NoImage(format!(
                    "the artifact names function id {crate_id}, which the chain's tag table does \
                     not list"
                ))
            })
    }

    /// The pinned identity — crate id, name, resolved type, linkage — of a
    /// canonical global index.
    ///
    /// # Errors
    /// Returns [`CoreError::NoImage`] when the table does not list the index —
    /// fail-closed, exactly as [`Tags::func_pin`] is, and for the same reason:
    /// a `(global k …)` or `(globaladdr k)` with no recorded name, type and
    /// linkage is a numeral standing for nothing.
    pub(crate) fn global_pin(&self, canonical: u32) -> Result<&GlobalPin, CoreError> {
        self.globals.get(&canonical).ok_or_else(|| {
            CoreError::NoImage(format!(
                "global canonical index {canonical} is not in the chain's tag table; the \
                 crate-level id, the name, the array type and the linkage it carries in the \
                 artifact's module table are not recorded, so nothing pins WHICH global this \
                 index denotes"
            ))
        })
    }

    /// The canonical index a crate-level `@global.N` id maps back to.
    ///
    /// # Errors
    /// Returns [`CoreError::NoImage`] when no entry carries that crate id.
    // Test-only, like its structural sibling `func_canonical` above: the mint
    // pipeline pins canonical -> crate id and never needs the inverse; the
    // inverse exists so the tag lane's invertibility is CHECKED rather than
    // assumed (`ir_mint::tests`). Without the gate the narrowed `pub(crate)`
    // form is dead in the non-test lib build and `-D warnings` refuses it.
    #[cfg(test)]
    pub(crate) fn global_canonical(&self, crate_id: u32) -> Result<u32, CoreError> {
        self.globals
            .iter()
            .find(|(_, pin)| pin.crate_id == crate_id)
            .map(|(c, _)| *c)
            .ok_or_else(|| {
                CoreError::NoImage(format!(
                    "the artifact names global id {crate_id}, which the chain's tag table does \
                     not list. Either the artifact was re-interned and the table needs a reviewed \
                     update, or the module table row is about a different global."
                ))
            })
    }

    /// The body's OWN crate-level function id, as
    /// [`SelfFunc`](super::SelfFunc).
    ///
    /// A table with no `funcs` row is [`SelfFunc::Unpinned`](super::SelfFunc),
    /// which is the honest reading for a body that calls nothing: there is no
    /// callee namespace to disambiguate, and inventing an id would be a claim
    /// the table does not make.
    #[must_use]
    pub fn self_func(&self) -> super::SelfFunc {
        match self.funcs.get(&super::SELF_FUNC_INDEX) {
            Some((id, _)) => super::SelfFunc::Pinned(*id),
            None => super::SelfFunc::Unpinned,
        }
    }

    /// The producer-invariant form of a printed type token.
    ///
    /// Every `<kind>.<digits>` in the token is a whole-crate table index that
    /// renumbers under a producer change with no instruction changed — measured:
    /// `expr_path_step_clone`'s join block binds `%1: enum.181` under two
    /// producers and `%1: enum.176` under the third. So the token is rewritten
    /// through THIS table, to the same canonical first-use index the core module
    /// carries: `enum.13` becomes `enum#0` when the table lists 13 at canonical
    /// 0, and an id the table does not list becomes `<kind>#?`.
    ///
    /// The result is invariant under exactly the renumbering the core form is
    /// invariant under, and under nothing else — `ptr` and `Rc<enum.13>` stay
    /// `ptr` and `Rc<enum#0>`, which is the discrimination the `param-type`
    /// blind slot needed.
    #[must_use]
    pub(crate) fn canon_ty(&self, tok: &str) -> String {
        let mut out = String::with_capacity(tok.len());
        let mut ident = String::new();
        let mut it = tok.chars().peekable();
        while let Some(c) = it.next() {
            if c.is_ascii_alphanumeric() || c == '_' {
                ident.push(c);
                continue;
            }
            if c == '.' && !ident.is_empty() && it.peek().is_some_and(char::is_ascii_digit) {
                let mut digits = String::new();
                while let Some(&d) = it.peek() {
                    if !d.is_ascii_digit() {
                        break;
                    }
                    digits.push(d);
                    it.next();
                }
                let id: u32 = digits.parse().unwrap_or(u32::MAX);
                let canonical = match ident.as_str() {
                    "enum" => self.enum_canonical(id).ok(),
                    "struct" => self.struct_canonical(id).ok(),
                    _ => None,
                };
                match canonical {
                    Some(k) => out.push_str(&format!("{ident}#{k}")),
                    None => out.push_str(&format!("{ident}#?")),
                }
                ident.clear();
                continue;
            }
            out.push_str(&ident);
            ident.clear();
            out.push(c);
        }
        out.push_str(&ident);
        out
    }

    /// The chain's `enums` lane as a crate id -> canonical index namespace.
    ///
    /// The same shape `project` builds for `funcs` and `globals`, and for the
    /// same purpose: a body of a multi-body module resolves an aggregate id
    /// through the CHAIN's numbering rather than through its own first-seen
    /// order, so two bodies that name different types cannot both claim
    /// canonical 0.
    #[must_use]
    pub(crate) fn enum_namespace(&self) -> BTreeMap<u32, u32> {
        self.enums.iter().map(|(k, (id, _))| (*id, *k)).collect()
    }

    /// The chain's `structs` lane as a crate id -> canonical index namespace.
    /// See [`Tags::enum_namespace`].
    #[must_use]
    pub(crate) fn struct_namespace(&self) -> BTreeMap<u32, u32> {
        self.structs.iter().map(|(k, (id, _))| (*id, *k)).collect()
    }

    /// The canonical function indices of the bodies the MODULE contains, in
    /// module order.
    ///
    /// Always starts at [`SELF_FUNC_INDEX`](super::SELF_FUNC_INDEX) — the root
    /// is the body the chain is named for — and continues in ascending
    /// canonical order, which is the order reader A projects them in.
    #[must_use]
    pub(crate) fn body_canonicals(&self) -> Vec<u32> {
        let mut v = vec![super::SELF_FUNC_INDEX];
        v.extend(self.extra_bodies.keys().copied());
        v
    }

    /// The Clean definition-name prefix for one body, given the chain prefix.
    ///
    /// The root's prefix IS the chain's, so a one-body chain never consults
    /// this lane and mints exactly what it always did.
    pub(crate) fn body_prefix<'a>(&'a self, canonical: u32, chain: &'a str) -> &'a str {
        match self.extra_bodies.get(&canonical) {
            Some((prefix, _)) => prefix,
            None => chain,
        }
    }

    /// The pinned interface of one body.
    ///
    /// # Errors
    /// Returns [`CoreError::NoImage`] when the index is neither the root nor a
    /// listed extra body — fail-closed, because an unpinned interface is the
    /// `param-type` blind slot again, one body further out.
    pub(crate) fn body_interface(&self, canonical: u32) -> Result<&Interface, CoreError> {
        if canonical == super::SELF_FUNC_INDEX {
            return Ok(&self.interface);
        }
        self.extra_bodies
            .get(&canonical)
            .map(|(_, i)| i)
            .ok_or_else(|| {
                CoreError::NoImage(format!(
                    "canonical function index {canonical} is a BODY of this module and the tag                      table pins no interface for it"
                ))
            })
    }

    /// The alias definitions, in canonical order, that [`mint`](super::mint)
    /// emits ahead of the block definitions.
    #[must_use]
    pub(crate) fn alias_defs(&self) -> Vec<String> {
        let mut out = Vec::new();
        for (id, alias) in self.enums.values() {
            out.push(format!(
                "def {alias} : IRTy := IRTy.enum_ {}",
                crate::ir_mint::mint::interning_id(*id)
            ));
        }
        for (id, alias) in self.structs.values() {
            out.push(format!(
                "def {alias} : IRTy := IRTy.struct_ {}",
                crate::ir_mint::mint::interning_id(*id)
            ));
        }
        out
    }
}

/// Parse a committed tag table.
///
/// Fail-closed on every shape error: a table that cannot be read is never
/// treated as an empty one, because an empty table mints a module with no
/// aliases and would look like a successful generation.
///
/// # Errors
/// Returns [`CoreError::Shape`] on malformed JSON or a malformed row.
pub fn parse(json: &str) -> Result<Tags, CoreError> {
    let v: serde_json::Value = serde_json::from_str(json)
        .map_err(|e| CoreError::Shape(format!("tag table is not JSON: {e}")))?;
    let mut tags = Tags::default();
    // `funcs` is required like the other two. A table that simply omitted it
    // would read as "this body calls nothing", which is exactly the silent
    // default the 2026-08-20 callee-namespace defect lived in.
    for (key, dest) in [("enums", 0u8), ("structs", 1u8), ("funcs", 2u8)] {
        let rows = v
            .get(key)
            .and_then(serde_json::Value::as_array)
            .ok_or_else(|| CoreError::Shape(format!("tag table has no `{key}` array")))?;
        for row in rows {
            let canonical = u32::try_from(
                row.get("canonical")
                    .and_then(serde_json::Value::as_u64)
                    .ok_or_else(|| CoreError::Shape(format!("{key} row has no `canonical`")))?,
            )
            .map_err(|_| CoreError::Shape(format!("{key} row's `canonical` does not fit u32")))?;
            let crate_id = u32::try_from(
                row.get("crate_id")
                    .and_then(serde_json::Value::as_u64)
                    .ok_or_else(|| CoreError::Shape(format!("{key} row has no `crate_id`")))?,
            )
            .map_err(|_| CoreError::Shape(format!("{key} row's `crate_id` does not fit u32")))?;
            // Aggregates carry the Clean ALIAS the minter emits; functions
            // carry the function's NAME, which is what actually pins identity
            // across a re-interning.
            let label_key = if dest == 2 { "name" } else { "alias" };
            let label = row
                .get(label_key)
                .and_then(serde_json::Value::as_str)
                .ok_or_else(|| CoreError::Shape(format!("{key} row has no `{label_key}`")))?
                .to_string();
            let map = match dest {
                0 => &mut tags.enums,
                1 => &mut tags.structs,
                _ => &mut tags.funcs,
            };
            if map.insert(canonical, (crate_id, label)).is_some() {
                return Err(CoreError::Shape(format!(
                    "{key} canonical index {canonical} appears twice"
                )));
            }
        }
    }
    // Every lane must be INVERTIBLE, not just the enums: `enum_canonical`,
    // `struct_canonical` and `func_canonical` all map a crate id back to one
    // canonical index, and two rows sharing a crate id would make that
    // first-match-wins rather than a function.
    for (key, map) in [
        ("enum", &tags.enums),
        ("struct", &tags.structs),
        ("func", &tags.funcs),
    ] {
        let mut seen: Vec<u32> = map.values().map(|(id, _)| *id).collect();
        seen.sort_unstable();
        seen.dedup();
        if seen.len() != map.len() {
            return Err(CoreError::Shape(format!(
                "two canonical {key} indices claim the same crate id, so the map is not invertible"
            )));
        }
    }
    encodings_lane(&v, &mut tags)?;
    if let Some(u) = v.get("usize") {
        let bits = u32::try_from(
            u.get("bits")
                .and_then(serde_json::Value::as_u64)
                .ok_or_else(|| CoreError::Shape("`usize` lane has no `bits`".into()))?,
        )
        .map_err(|_| CoreError::Shape("`usize.bits` does not fit u32".into()))?;
        let sites = u32::try_from(
            u.get("sites")
                .and_then(serde_json::Value::as_u64)
                .ok_or_else(|| CoreError::Shape("`usize` lane has no `sites`".into()))?,
        )
        .map_err(|_| CoreError::Shape("`usize.sites` does not fit u32".into()))?;
        // A pin for a body with no site would be a stale target assumption
        // riding along unexercised; a chain without the type omits the lane.
        let isize_sites =
            match u.get("isize_sites") {
                None => 0,
                Some(x) => u32::try_from(x.as_u64().ok_or_else(|| {
                    CoreError::Shape("`usize.isize_sites` is not a number".into())
                })?)
                .map_err(|_| CoreError::Shape("`usize.isize_sites` does not fit u32".into()))?,
            };
        // A pin for a body with no site of EITHER token would be a stale
        // target assumption riding along unexercised; a chain that names
        // neither omits the lane. The two counts are summed here and compared
        // separately later, so a chain carrying only `isize` still pins the
        // width through this lane rather than needing one of its own.
        if bits == 0 || sites.saturating_add(isize_sites) == 0 {
            return Err(CoreError::Shape(
                "`usize` lane must pin a non-zero width and at least one `usize` or `isize` site"
                    .into(),
            ));
        }
        tags.usize_pin = Some(UsizePin {
            bits,
            sites,
            isize_sites,
        });
    }
    // `globals` is OPTIONAL, and its absence means "this module's global list
    // is empty". That default is the honest one — it is what every chain
    // before `ir_lzc` measured — and it is the reason their committed tables
    // parse unchanged under this lane's arrival. A core module that names a
    // global the lane does not list is refused by `global_pin`, never
    // defaulted.
    if let Some(rows) = v.get("globals") {
        let rows = rows
            .as_array()
            .ok_or_else(|| CoreError::Shape("`globals` must be an array of global rows".into()))?;
        for row in rows {
            let n = |field: &str| -> Result<u32, CoreError> {
                u32::try_from(
                    row.get(field)
                        .and_then(serde_json::Value::as_u64)
                        .ok_or_else(|| CoreError::Shape(format!("globals row has no `{field}`")))?,
                )
                .map_err(|_| CoreError::Shape(format!("globals row's `{field}` does not fit u32")))
            };
            let s = |field: &str| -> Result<String, CoreError> {
                row.get(field)
                    .and_then(serde_json::Value::as_str)
                    .map(ToString::to_string)
                    .ok_or_else(|| CoreError::Shape(format!("globals row has no `{field}` string")))
            };
            let canonical = n("canonical")?;
            let pin = GlobalPin {
                crate_id: n("crate_id")?,
                name: s("name")?,
                ty: s("ty")?,
                linkage: s("linkage")?,
            };
            // The same keyword discipline as `interface.linkage`: a value the
            // producer cannot print is a typo, not a pin.
            if !super::LINKAGES.contains(&pin.linkage.as_str()) {
                return Err(CoreError::Shape(format!(
                    "globals row {canonical} (`{}`) has linkage `{}`, which is not one of {:?}",
                    pin.name,
                    pin.linkage,
                    super::LINKAGES
                )));
            }
            if tags.globals.insert(canonical, pin).is_some() {
                return Err(CoreError::Shape(format!(
                    "globals canonical index {canonical} appears twice"
                )));
            }
        }
        // Invertible on the crate id, like every other lane: `global_canonical`
        // maps an `@global.N` back to ONE canonical index.
        let mut ids: Vec<u32> = tags.globals.values().map(|g| g.crate_id).collect();
        ids.sort_unstable();
        ids.dedup();
        if ids.len() != tags.globals.len() {
            return Err(CoreError::Shape(
                "two canonical global indices claim the same crate id, so the map is not \
                 invertible"
                    .into(),
            ));
        }
        // And invertible on the NAME, which is what reader B resolves the
        // module-table row by: two rows sharing a name would make that
        // resolution first-match-wins rather than a function.
        let mut names: Vec<&str> = tags.globals.values().map(|g| g.name.as_str()).collect();
        names.sort_unstable();
        names.dedup();
        if names.len() != tags.globals.len() {
            return Err(CoreError::Shape(
                "two canonical global indices claim the same name".into(),
            ));
        }
        // Dense from 0: the lane indexes the ONE namespace `(global k …)` and
        // `(globaladdr k)` share, and a hole in it would be a global index no
        // row accounts for.
        let expected: Vec<u32> =
            (0..u32::try_from(tags.globals.len()).unwrap_or(u32::MAX)).collect();
        let got: Vec<u32> = tags.globals.keys().copied().collect();
        if got != expected {
            return Err(CoreError::Shape(format!(
                "the `globals` lane must be dense from 0: found canonical indices {got:?}"
            )));
        }
    }
    // The `funcs` lane is dense from 0: it indexes the ONE namespace the core
    // module's `(func N …)` and `(call M …)` share, and a hole in it would mean
    // a callee index no row accounts for.
    let expected: Vec<u32> = (0..u32::try_from(tags.funcs.len()).unwrap_or(u32::MAX)).collect();
    let got: Vec<u32> = tags.funcs.keys().copied().collect();
    if got != expected {
        return Err(CoreError::Shape(format!(
            "the `funcs` lane must be dense from {}: found canonical indices {got:?}",
            super::SELF_FUNC_INDEX
        )));
    }
    // `body` and `interface` are REQUIRED for the same reason `funcs` is: a
    // table that simply omitted them would read as "this chain pins no
    // interface", which is exactly the silent default the `param-type` and
    // `function-name` blind slots lived in.
    tags.body = v
        .get("body")
        .and_then(serde_json::Value::as_str)
        .ok_or_else(|| {
            CoreError::Shape(
                "tag table has no `body`: nothing would pin WHICH function the core module is \
                 about, and the module itself carries no name"
                    .into(),
            )
        })?
        .to_string();
    let iface = v
        .get("interface")
        .and_then(serde_json::Value::as_object)
        .ok_or_else(|| {
            CoreError::Shape(
                "tag table has no `interface` object: the parameter types, alignments and \
                 annotation kinds the core module cannot hold would be pinned by nothing"
                    .into(),
            )
        })?;
    tags.interface = interface_lane(iface, tags.body.clone())?;
    // `extra_bodies` is OPTIONAL, and its absence means "this module defines
    // one function". That default is the honest one — it is what every chain
    // before `has_loose_bvars` measured — and it is the reason those chains'
    // committed scripts do not move under this lane.
    if let Some(rows) = v.get("extra_bodies") {
        let rows = rows.as_array().ok_or_else(|| {
            CoreError::Shape("`extra_bodies` must be an array of body rows".into())
        })?;
        for row in rows {
            let canonical = u32::try_from(
                row.get("canonical")
                    .and_then(serde_json::Value::as_u64)
                    .ok_or_else(|| {
                        CoreError::Shape("extra_bodies row has no `canonical`".into())
                    })?,
            )
            .map_err(|_| {
                CoreError::Shape("extra_bodies row's `canonical` does not fit u32".into())
            })?;
            if canonical == super::SELF_FUNC_INDEX {
                return Err(CoreError::Shape(
                    "canonical index 0 is the ROOT body; it is pinned by the top-level `body` and                      `interface`, and listing it again would create a second source of truth"
                        .into(),
                ));
            }
            // Every body is a function of this module, so it must be a row of
            // the ONE namespace `(func N …)` and `(call M …)` share. A body
            // the `funcs` lane does not list is a numeral standing for
            // nothing, exactly like an unpinned callee.
            let (_, pinned_name) = tags.func_pin(canonical)?;
            let pinned_name = pinned_name.clone();
            let prefix = row
                .get("prefix")
                .and_then(serde_json::Value::as_str)
                .ok_or_else(|| {
                    CoreError::Shape(
                        "extra_bodies row has no `prefix`: its Clean definitions would have to                          share the chain's names and collide with the root's blocks"
                            .into(),
                    )
                })?
                .to_string();
            let name = row
                .get("body")
                .and_then(serde_json::Value::as_str)
                .ok_or_else(|| CoreError::Shape("extra_bodies row has no `body`".into()))?
                .to_string();
            if name != pinned_name {
                return Err(CoreError::Shape(format!(
                    "extra body {canonical} says `{name}` and the `funcs` lane says                      `{pinned_name}`; the two name the same function or the table is wrong"
                )));
            }
            let sub = row
                .get("interface")
                .and_then(serde_json::Value::as_object)
                .ok_or_else(|| {
                    CoreError::Shape(format!(
                        "extra body {canonical} (`{name}`) has no `interface` object"
                    ))
                })?;
            if tags
                .extra_bodies
                .insert(canonical, (prefix, interface_lane(sub, name)?))
                .is_some()
            {
                return Err(CoreError::Shape(format!(
                    "extra_bodies canonical index {canonical} appears twice"
                )));
            }
        }
        // Two bodies sharing a name prefix would mint two `<prefix>_b0` lines
        // and the second would fail to register — or, worse, register a block
        // the other function's `IRFunc` then names.
        let mut prefixes: Vec<&str> = tags
            .extra_bodies
            .values()
            .map(|(p, _)| p.as_str())
            .collect();
        prefixes.sort_unstable();
        let n = prefixes.len();
        prefixes.dedup();
        if prefixes.len() != n {
            return Err(CoreError::Shape(
                "two bodies of this module share a Clean name prefix".into(),
            ));
        }
    }
    Ok(tags)
}

/// One `interface` object — the root's, or an extra body's.
fn interface_lane(
    iface: &serde_json::Map<String, serde_json::Value>,
    function_name: String,
) -> Result<Interface, CoreError> {
    Ok(Interface {
        function_name,
        linkage: keyword_lane(iface, "linkage", &super::LINKAGES)?,
        calling_conv: keyword_lane(iface, "calling_conv", &super::CALLING_CONVS)?,
        functy: functy_lane(iface)?,
        producer: producer_lane(iface)?,
        params: params_lane(iface, "params")?,
        block_params: params_lane(iface, "block_params")?,
        aligns: str_lane(iface, "aligns")?,
        clauses: str_lane(iface, "clauses")?.into_iter().collect(),
    })
}

/// One pinned header KEYWORD — the linkage or the calling convention.
///
/// Required, and required to be a keyword the producer can actually print. A
/// table that omitted the key would pin the reader's default, which is exactly
/// the silent agreement the `cc-and-linkage` row spent four months describing
/// as "permanently blind": both sides would say `external`/`ccc` and neither
/// would have looked.
fn keyword_lane(
    iface: &serde_json::Map<String, serde_json::Value>,
    key: &str,
    allowed: &[&str],
) -> Result<String, CoreError> {
    let v = iface
        .get(key)
        .and_then(serde_json::Value::as_str)
        .ok_or_else(|| {
            CoreError::Shape(format!(
                "`interface` has no `{key}` string. trust-ir's printer emits this keyword only \
                 when it is NOT the default, so an unpinned one would agree with the reader's \
                 default by construction and the slot would be blind again"
            ))
        })?;
    if !allowed.contains(&v) {
        return Err(CoreError::Shape(format!(
            "`interface.{key}` is `{v}`, which is not one of {allowed:?}"
        )));
    }
    Ok(v.to_string())
}

/// The pinned `functy.N` — trust-ir's fourth crate-level namespace.
///
/// Pinned VERBATIM, exactly as the `funcs` lane pins a callee's `@func.N`, and
/// for the same reason: there is no first-use canonicalisation available (a
/// body has exactly one header signature, so interning it would map every body
/// to `functy#0` and pin nothing), and the printed text carries no signature
/// table to resolve the index through. So this moves under a producer
/// re-interning and is re-pinned under review — the M7 bargain, not an
/// exception to it.
fn functy_lane(iface: &serde_json::Map<String, serde_json::Value>) -> Result<u32, CoreError> {
    let n = iface
        .get("functy")
        .and_then(serde_json::Value::as_u64)
        .ok_or_else(|| {
            CoreError::Shape(
                "`interface` has no `functy` number. `FuncTy` is `{ params, returns, is_vararg }` \
                 and the printed body shows none of the three directly, so an unpinned signature \
                 index is a numeral standing for nothing"
                    .into(),
            )
        })?;
    u32::try_from(n).map_err(|_| CoreError::Shape("`interface.functy` does not fit u32".into()))
}

/// The pinned `; #producer:` token, or an EXPLICIT `null` for a body that
/// carries no producer clause.
///
/// `null` is required rather than allowing the key to be absent, so "this body
/// names no producer" is something the table SAYS and not something it fails to
/// say.
fn producer_lane(
    iface: &serde_json::Map<String, serde_json::Value>,
) -> Result<Option<String>, CoreError> {
    match iface.get("producer") {
        None => Err(CoreError::Shape(
            "`interface` has no `producer` key. Use `null` for a body that carries no \
             `; #producer:` clause — the absence has to be pinned, not merely unmentioned"
                .into(),
        )),
        Some(serde_json::Value::Null) => Ok(None),
        Some(serde_json::Value::String(s)) => Ok(Some(s.clone())),
        Some(other) => Err(CoreError::Shape(format!(
            "`interface.producer` must be a string or null, found {other}"
        ))),
    }
}

/// One pinned parameter lane of the `interface` object.
fn params_lane(
    iface: &serde_json::Map<String, serde_json::Value>,
    key: &str,
) -> Result<Vec<ParamSlot>, CoreError> {
    let rows = iface
        .get(key)
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| CoreError::Shape(format!("`interface` has no `{key}` array")))?;
    let n = |row: &serde_json::Value, field: &str| -> Result<u32, CoreError> {
        u32::try_from(
            row.get(field)
                .and_then(serde_json::Value::as_u64)
                .ok_or_else(|| CoreError::Shape(format!("{key} row has no `{field}`")))?,
        )
        .map_err(|_| CoreError::Shape(format!("{key} row's `{field}` does not fit u32")))
    };
    let mut out = Vec::with_capacity(rows.len());
    for row in rows {
        // `ty` is the CANONICAL form -- crate ids resolved through this table.
        // A row may also carry `observed_ty` and `rust_type`; both are recorded
        // for review and neither is compared, because the raw token moves under
        // a producer change and a Rust type name is not in the artifact at all.
        let ty = row
            .get("ty")
            .and_then(serde_json::Value::as_str)
            .ok_or_else(|| CoreError::Shape(format!("{key} row has no `ty`")))?
            .to_string();
        out.push(ParamSlot {
            block: n(row, "block")?,
            index: n(row, "index")?,
            ssa: n(row, "ssa")?,
            ty,
        });
    }
    Ok(out)
}

/// One pinned string lane of the `interface` object.
fn str_lane(
    iface: &serde_json::Map<String, serde_json::Value>,
    key: &str,
) -> Result<Vec<String>, CoreError> {
    iface
        .get(key)
        .and_then(serde_json::Value::as_array)
        .ok_or_else(|| CoreError::Shape(format!("`interface` has no `{key}` array")))?
        .iter()
        .map(|x| {
            x.as_str()
                .map(ToString::to_string)
                .ok_or_else(|| CoreError::Shape(format!("`interface.{key}` holds a non-string")))
        })
        .collect()
}

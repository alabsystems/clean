// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Crystal A2 — the MINT gate for `ir_lzc`: the designated target
//! `level::Level::is_zero` TOGETHER WITH the real body of
//! `<level::LevelArc as std::ops::Deref>::deref`.**
//!
//! Same three readers and the same questions as `crystal_a2_mint.rs`; read that
//! file's header and `src/ir_mint/mod.rs` for what this establishes and what it
//! does not. Two things are new in kind here, and one thing is deliberately
//! NOT claimed.
//!
//! # New: the FIRST module with a non-empty `(globals …)` list
//!
//! The deref builds the `&str` its `expect` call takes out of a MODULE-TABLE
//! GLOBAL — `@__trust_promoted_1135`, the 34 bytes of
//! `live LevelArc must contain a level`. So this chain is the first whose core
//! module carries `(global 0 (agg (int 108) …))`, the first whose minted script
//! carries an `IRGlobal` line, and the first whose reader-B input is a TRIPLE:
//! the module-table preamble rows, then the two bodies in module order.
//! `IRGlobal.mk : Nat → IRConst → IRGlobal` has no slot for the global's name,
//! type or linkage, so all three are pinned in the tag table's `globals` lane
//! and COMPARED by `project`, and [`m10_the_interface_pins_bite`] is where
//! each stops being a comment.
//!
//! # New: a body that calls DECLARATIONS, and A4 NOT claimed
//!
//! `ir_lz` calls the deref and does not define it, so `ir_call_exec` goes
//! `stuck no_func` at canonical 1. Here the deref IS defined and that call
//! RESOLVES; what is stuck is one call deeper, at the deref's own `call 2` into
//! `std::option::Option::<T>::as_deref`, which the crate artifact carries as a
//! header with no instruction. Canonicals 2 and 3 are `funcs` rows with
//! `defined: false` — the first of their kind — and the ids that identify them
//! are the Phase-B join key, because the artifact holds a SECOND declaration of
//! `as_deref` under the same NAME (`functy.947`, dump-control:118003) that only
//! the crate id and the functy tell apart. So this module still halts stuck,
//! and NOTHING here asserts A4 or A5 over `ir_lzc_module`: what is established
//! is representation equality with the artifact. Phase B derives those two
//! bodies; Phase A pins their identity so that it can.
//!
//! `(func 0 …)` of the committed core is BYTE-IDENTICAL to `(func 0 …)` of
//! [`ir_mint::IR_LZ_CORE`] — [`m1_committed_core_round_trips_its_printer`]
//! checks it — so `ir_lz` and every gate over it stay byte-frozen, and the
//! `Eq.refl` tying the two minted functions together lands with the
//! specification. M4 is in [`lzc_m4`], M5 in [`lzc_a1`], M10 in
//! [`lzc_interface`].

use clean_verify::ir_mint::{self, Sx};

#[allow(dead_code)]
use crate::emitted_cfg;

const PREFIX: &str = "ir_lzc";
/// The module-table PREAMBLE: the `type ty.0 = u8` row and the `global …` row
/// the deref names. Not part of either body's text — a module-table fact — so
/// it is a fixture of its own, cut from the same dump.
const GLOBALS: &str = include_str!("fixtures/level_is_zero_deref_globals.trust-ir-rows.txt");
const IS_ZERO: &str = include_str!("fixtures/level_is_zero.trust-ir.txt");
const DEREF: &str = include_str!("fixtures/level_is_zero_deref_callee.trust-ir.txt");

/// The chain's reader-B input: the preamble, then the two bodies in MODULE
/// ORDER. The order is not a formatting choice — it is the order
/// `ir_func_find` walks, and the tag table's `funcs`/`extra_bodies` lanes pin
/// it by name, so a swapped concatenation is refused rather than silently read.
fn fixture() -> String {
    format!("{GLOBALS}{IS_ZERO}{DEREF}")
}

fn tags() -> ir_mint::Tags {
    ir_mint::tags::parse(ir_mint::IR_LZC_TAGS).expect("the committed tag table must parse")
}

fn core_a() -> Sx {
    ir_mint::parse(ir_mint::IR_LZC_CORE).expect("the committed core module must parse")
}

/// Reader B over the whole triple, told the chain's function and global
/// namespaces.
fn core_b() -> Sx {
    ir_mint::project(&fixture(), &tags())
        .expect("reader B must read the committed preamble and the two committed bodies")
        .core
}

fn canon(sx: &Sx) -> String {
    ir_mint::print(sx).expect("a core module must print")
}

/// The `(func N …)` block of a committed core module, by the function's own id
/// — the lines from `    (func N` to the end of that function, exclusive of
/// the `  )` that closes the module's `funcs` list.
fn func_block(core: &str, id: u32) -> String {
    let head = format!("    (func {id}");
    let mut out = String::new();
    let mut inside = false;
    for line in core.lines() {
        if line.starts_with("    (func ") {
            inside = line == head;
        } else if line == "  )" {
            inside = false;
        }
        if inside {
            out.push_str(line);
            out.push('\n');
        }
    }
    assert!(!out.is_empty(), "no `(func {id} …)` block:\n{core}");
    out
}

/// The mint record, parsed. Every M7 comparison reads it as JSON rather than
/// as a substring, so a row that drifted cannot pass by appearing elsewhere in
/// the file.
fn record() -> serde_json::Value {
    serde_json::from_str(ir_mint::IR_LZC_RECORD).expect("the committed mint record must be JSON")
}

/// Reader A's OWN committed output — `generated/ir_lzc.core.prov.json`, written
/// by `scripts/crystal_a2_project` in the same run that wrote
/// [`ir_mint::IR_LZC_CORE`]. This, and not the mint record's hand-maintained
/// `reader_a` transcription of it, is what M7 compares the tag table against.
fn prov() -> serde_json::Value {
    serde_json::from_str(ir_mint::IR_LZC_PROVENANCE)
        .expect("reader A's committed provenance must be JSON")
}

/// The committed tag table's `globals` lane, read as JSON.
///
/// This is an integration test, so it is an EXTERNAL reader of the crate: going
/// through a typed accessor would force the pin struct and its getter public for
/// one caller. The artifact is what the two readers have to agree with anyway,
/// so it is read directly and structurally.
fn tag_globals() -> Vec<serde_json::Value> {
    let t: serde_json::Value =
        serde_json::from_str(ir_mint::IR_LZC_TAGS).expect("the committed tag table must be JSON");
    t["globals"]
        .as_array()
        .unwrap_or_else(|| panic!("the tag table's globals lane must be an array"))
        .clone()
}

fn strings(v: &serde_json::Value) -> Vec<String> {
    v.as_array()
        .unwrap_or_else(|| panic!("expected an array, found {v}"))
        .iter()
        .map(|x| {
            x.as_str()
                .unwrap_or_else(|| panic!("expected a string, found {x}"))
                .to_string()
        })
        .collect()
}

/// The def path a producer DECLARATION name spells, or `None` for any other
/// name.
///
/// The producer names a bodyless row by its plain def path unless that name
/// collides inside the crate, and then by
/// `!trust_bodyless_instance::<def-path>::<definition>-<hex(key)>`
/// (trust-ir's `crate_module.rs` `declaration_name`, recovered the same way by
/// `scripts/crystal_sidecar_closure.py`). The 2026-10-07 rebaseline's dump
/// carries three `as_deref` instances, so both declarations of this chain are
/// spelled that way there. Recovery is EXACT: the definition is 32 lowercase
/// hex digits, the key is non-empty hex that decodes to UTF-8, and the decoded
/// key must name the recovered def path as its `havoc:` subject -- so the
/// suffix is the collision key of THIS path, not any text after a `::`.
fn bodyless_instance_def_path(name: &str) -> Option<String> {
    let rest = name.strip_prefix("!trust_bodyless_instance::")?;
    let (path, suffix) = rest.rsplit_once("::")?;
    let (definition, key) = suffix.split_once('-')?;
    let is_hex = |s: &str| !s.is_empty() && s.bytes().all(|b| b.is_ascii_hexdigit());
    if definition.len() != 32 || !is_hex(definition) || !is_hex(key) || key.len() % 2 != 0 {
        return None;
    }
    let bytes: Vec<u8> = (0..key.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&key[i..i + 2], 16))
        .collect::<Result<_, _>>()
        .ok()?;
    let decoded = String::from_utf8(bytes).ok()?;
    decoded
        .strip_prefix("havoc:")?
        .strip_prefix(path)?
        .starts_with('|')
        .then(|| path.to_string())
}

/// The recovery M7 leans on refuses every near miss: a key naming another
/// path, a short definition, odd or non-hex key text, and a plain name.
#[test]
fn bodyless_instance_recovery_is_exact() {
    let hex = |s: &str| s.bytes().map(|b| format!("{b:02x}")).collect::<String>();
    let def = "d9e4897297e644f6566e272e35e17dd6";
    let path = "std::option::Option::<T>::as_deref";
    let good = format!(
        "!trust_bodyless_instance::{path}::{def}-{}",
        hex(&format!("havoc:{path}|concrete-v1:01"))
    );
    assert_eq!(bodyless_instance_def_path(&good).as_deref(), Some(path));
    for bad in [
        // the key names a DIFFERENT path
        format!(
            "!trust_bodyless_instance::{path}::{def}-{}",
            hex("havoc:std::option::Option::<T>::expect|concrete-v1:01")
        ),
        // the key's subject is only a prefix of the path
        format!(
            "!trust_bodyless_instance::{path}::{def}-{}",
            hex("havoc:std::option::Option::<T>::as_der|concrete-v1:01")
        ),
        // a definition that is not 32 hex digits
        format!(
            "!trust_bodyless_instance::{path}::{}-{}",
            &def[1..],
            hex(&format!("havoc:{path}|x"))
        ),
        // odd-length / non-hex key
        format!("!trust_bodyless_instance::{path}::{def}-abc"),
        format!("!trust_bodyless_instance::{path}::{def}-zz"),
        // no prefix: a plain name is compared verbatim, never recovered
        path.to_string(),
    ] {
        assert_eq!(bodyless_instance_def_path(&bad), None, "{bad}");
    }
}

fn u64s(v: &serde_json::Value) -> Vec<u64> {
    v.as_array()
        .unwrap_or_else(|| panic!("expected an array, found {v}"))
        .iter()
        .map(|x| {
            x.as_u64()
                .unwrap_or_else(|| panic!("expected a number, found {x}"))
        })
        .collect()
}

// ────────────────────────────────────────────────────────────────────────────
// M1 — the committed core is canonical: two functions, one global, and a
// function 0 that IS the designated target's frozen projection.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m1_committed_core_round_trips_its_printer() {
    assert_eq!(
        canon(&core_a()),
        ir_mint::IR_LZC_CORE,
        "the committed core module is not what its own canonical printer produces"
    );
    let text = ir_mint::IR_LZC_CORE;
    for (needle, want, why) in [
        ("(block ", 11, "ten blocks in the root, one in the deref"),
        ("(func ", 2, "the root and the deref, both DEFINED"),
        (
            "(global ",
            1,
            "the promoted `expect` message, the only global",
        ),
        (
            "(call 2 ",
            1,
            "the deref's call into `as_deref` — a DECLARATION",
        ),
        ("(call 3 ", 1, "…and into `expect`, the other one"),
        ("(ptrfromparts ", 1, "the `&str` the deref builds"),
        ("(globaladdr 0)", 1, "…over the address of global 0"),
    ] {
        assert_eq!(
            text.matches(needle).count(),
            want,
            "`{needle}` must occur {want} time(s) — {why}:\n{text}"
        );
    }
    assert_eq!(
        func_block(text, 0),
        func_block(ir_mint::IR_LZ_CORE, 0),
        "function 0 must be the DESIGNATED TARGET'S OWN projection, byte for byte. This chain \
         RE-MINTS `level::Level::is_zero` under `ir_lzc_*` names beside the deref; it does not \
         re-project it, and `ir_lz` stays frozen"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M2 — reader B equals reader A modulo the one slot the text cannot show.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m2_reader_b_equals_reader_a_modulo_the_switch_flag() {
    let (masked, ledger) =
        ir_mint::mask_text_unwitnessed(&core_a()).expect("reader A's module must mask");
    assert_eq!(
        canon(&masked),
        canon(&core_b()),
        "the artifact BINARY (reader A) and the emitted TEXT (reader B) disagree about this \
         module"
    );
    assert_eq!(ledger.len(), 1, "exactly one unwitnessed slot: {ledger:?}");
    assert_eq!(
        ledger[0].to_string(),
        "bb0#2 switch arg4",
        "the ROOT's switch flag, and nothing from the deref: that body carries no switch, so \
         every one of its six instructions is witnessed by the emitted text"
    );
    assert_eq!(
        strings(&record()["text_unwitnessed"]),
        vec!["bb0#2 switch arg4".to_string()],
        "…and the committed mint record says exactly that"
    );
}

/// Reader B is TOTAL over its input: a surplus body, a swapped pair, a missing
/// body, a preamble in the wrong place and a missing preamble are each refused
/// BY NAME rather than dropped or misread.
#[test]
fn m2_reader_b_refuses_a_malformed_triple() {
    let t = tags();
    for (what, text, needle) in [
        (
            "a third body",
            format!("{GLOBALS}{IS_ZERO}{DEREF}{DEREF}"),
            "function bod",
        ),
        (
            "the two bodies swapped",
            format!("{GLOBALS}{DEREF}{IS_ZERO}"),
            "level::Level::is_zero",
        ),
        (
            "the deref alone",
            format!("{GLOBALS}{DEREF}"),
            "function bod",
        ),
        (
            "the preamble AFTER the bodies",
            format!("{IS_ZERO}{DEREF}{GLOBALS}"),
            "a module table",
        ),
        (
            "no preamble at all",
            format!("{IS_ZERO}{DEREF}"),
            "global declaration",
        ),
    ] {
        let e = ir_mint::project(&text, &t)
            .map(|_| ())
            .err()
            .unwrap_or_else(|| panic!("{what}: must be REFUSED, never read"));
        assert!(
            format!("{e}").contains(needle),
            "{what}: the refusal must name `{needle}`, and says: {e}"
        );
    }
}

// ────────────────────────────────────────────────────────────────────────────
// M3 — `mint` of the committed core IS the committed script.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m3_mint_reproduces_the_committed_script() {
    let minted = ir_mint::mint(&core_a(), PREFIX, &tags())
        .expect("the committed core mints")
        .text();
    assert_eq!(
        minted,
        ir_mint::IR_LZC_DEFS,
        "the committed definition script is not what `mint` produces from the committed core \
         module"
    );
    assert!(
        ir_mint::IR_LZC_RECORD.contains(&ir_mint::digest(&minted)),
        "the mint record's defs digest does not match the minted script"
    );
    assert!(
        ir_mint::IR_LZC_RECORD.contains(&ir_mint::digest(ir_mint::IR_LZC_CORE)),
        "the mint record's core digest does not match the committed core module"
    );
    // The deref's Clean name prefix comes from the TABLE, not from the minter,
    // and the global line is the first the mint has ever produced.
    for needle in [
        "def ir_lad_b0 ",
        "def ir_lad_func ",
        "def ir_lzc_g0 ",
        "IRInst.ptrfromparts",
        "IRInst.globaladdr",
    ] {
        assert!(
            minted.contains(needle),
            "the minted script must carry `{needle}`:\n{minted}"
        );
    }
    assert!(
        ir_mint::IR_LZC_TAGS.contains("\"prefix\": \"ir_lad\""),
        "…and `ir_lad` is pinned in the table, not chosen by the minter"
    );
    // THE NUMERAL POLICY, illustrated on the one artifact that forced it. A
    // global's index is STRUCTURAL and renders through the `ir_d0..ir_d130`
    // pool; its 34 initializer bytes are DATA and render through the data
    // policy, so 108 is the literal `108` and never the atom `ir_d108`, which
    // the specification does not declare. What PINS the policy is the byte
    // equality against `IR_LZC_DEFS` above; what these three buy is narrower
    // and worth stating exactly: a guard against a DATA pool widened past 108.
    // The cutoff is 16 (`ir_mint/mint.rs`) and every byte of this initializer
    // is >= 32, so a pool widened to anything between 17 and 108 would respell
    // this global's other bytes as atoms and leave both assertions true. No
    // sharper witness exists in this artifact.
    assert!(
        minted.contains("IRConst.int_ 108"),
        "byte 108 is DATA and renders as the literal:\n{minted}"
    );
    assert!(
        !minted.contains("IRConst.int_ ir_d108"),
        "…and never as an atom the specification never introduced:\n{minted}"
    );
    assert!(
        minted.contains("IRGlobal.mk ir_d0 "),
        "…while the global's INDEX is structural:\n{minted}"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M7 — the tag table, reader A's OWN committed output, and the record that
// transcribes it all still name the same artifact.
//
// The pins are compared against `generated/ir_lzc.core.prov.json` — the file
// `scripts/crystal_a2_project` wrote beside the core in the same run — and the
// mint record's `reader_a` block is then compared against that same file. So a
// tag pin that drifts from the ARTIFACT goes red, and so does a record whose
// hand-maintained transcription drifts from the reader. Comparing the pins
// against the record alone would have checked a transcription against a
// transcription.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m7_the_tag_table_still_matches_the_artifact() {
    let t = tags();
    let p = prov();
    // FUNCS: the four ids and the four names, in canonical order, against the
    // ids and names reader A recorded when it walked the binary.
    let ids: Vec<u64> = t.funcs.values().map(|(id, _)| u64::from(*id)).collect();
    let names: Vec<String> = t.funcs.values().map(|(_, n)| n.clone()).collect();
    assert_eq!(
        ids,
        u64s(&p["crate_func_ids_seen"]),
        "the tag table's funcs ids and reader A's own provenance disagree"
    );
    // A BODY's name is compared verbatim. A DECLARATION (`defined: false`) may
    // be spelled by the producer as its collision-disambiguated bodyless
    // instance, and is then compared through the EXACT recovery above -- the
    // table keeps the def path, which is what `sidecar_join.callee_def_path`
    // joins on. A body row is never matched through the recovery.
    let declared: Vec<bool> = {
        let raw: serde_json::Value = serde_json::from_str(ir_mint::IR_LZC_TAGS)
            .expect("the committed tag table must be JSON");
        raw["funcs"]
            .as_array()
            .expect("the tag table's funcs lane must be an array")
            .iter()
            .map(|row| row["defined"] == serde_json::Value::Bool(false))
            .collect()
    };
    let seen = strings(&p["crate_func_names_seen"]);
    assert_eq!(
        (names.len(), declared.len()),
        (seen.len(), seen.len()),
        "the tag table's funcs names and reader A's own provenance disagree in length"
    );
    for (i, (pinned, read)) in names.iter().zip(&seen).enumerate() {
        let recovered = if declared[i] {
            bodyless_instance_def_path(read)
        } else {
            None
        };
        assert!(
            read == pinned || recovered.as_deref() == Some(pinned.as_str()),
            "the tag table's funcs names and reader A's own provenance disagree at canonical \
             {i}: pinned `{pinned}`, reader A `{read}`"
        );
    }
    assert_eq!(
        declared,
        [false, false, true, true],
        "two bodies and two declarations"
    );
    assert_eq!(ids.len(), 4, "two bodies and two declarations");
    // GLOBALS: the id, the name, and the two forms of the type — the tag side
    // read straight out of the committed artifact by [`tag_globals`].
    let g = tag_globals();
    assert_eq!(g.len(), 1, "the one pinned global");
    let g_ids: Vec<u64> = g
        .iter()
        .map(|x| {
            x["crate_id"]
                .as_u64()
                .expect("every pin carries a crate id")
        })
        .collect();
    let g_names: Vec<String> = g
        .iter()
        .map(|x| {
            x["name"]
                .as_str()
                .expect("every pin carries a name")
                .to_string()
        })
        .collect();
    assert_eq!(
        g_ids,
        u64s(&p["crate_global_ids_seen"]),
        "the tag table's globals ids and reader A's own provenance disagree"
    );
    assert_eq!(
        g_names,
        strings(&p["crate_global_names_seen"]),
        "the tag table's globals names and reader A's own provenance disagree"
    );
    // The RAW token is recorded on both sides and compared to neither pin:
    // `ty.0` is a whole-crate type-table index and renumbers.
    assert_eq!(
        strings(&p["global_tys_erased"]),
        vec!["[ty.0 x 34]".to_string()],
    );
    assert_eq!(
        g[0]["observed_ty"], "[ty.0 x 34]",
        "the tag table records the raw token beside the resolved one"
    );
    // The RESOLVED element type is a TWO-READER fact: reader A resolved `ty.0`
    // through the binary's own type table, reader B through the `type ty.0 =
    // u8` row of the committed preamble fixture, and the pin is what they must
    // both agree with.
    assert_eq!(
        strings(&p["global_tys_resolved"]),
        vec!["[u8 x 34]".to_string()],
        "reader A's resolved element type and the tag table's pin disagree"
    );
    assert_eq!(
        g[0]["ty"], "[u8 x 34]",
        "the tag table pins the RESOLVED element type reader A also reports"
    );
    assert_eq!(
        g[0]["linkage"], "internal",
        "…and the linkage the module table spells"
    );
    assert!(
        GLOBALS.contains("type ty.0 = u8"),
        "…and reader B's route to it is this row of the preamble fixture"
    );
    // The artifact still names what the table pins.
    assert!(
        DEREF.contains("call @func.4924(") && DEREF.contains("call @func.4925("),
        "the deref must still call the two DECLARATIONS by the pinned ids; if not, the artifact \
         was re-interned and this table needs a one-line REVIEWED re-pin"
    );
    assert!(
        DEREF.contains("global_addr @global.1135"),
        "…and still address the pinned global"
    );
}

/// The mint record's `reader_a` block is a HAND-MAINTAINED transcription of
/// `generated/ir_lzc.core.prov.json`, which nothing else in the tree would
/// notice going stale. Every lane M7 reads out of the provenance is compared
/// here against the record's copy of it, and the record's
/// `artifact_core_digest` — the digest a2project printed for this projection —
/// against the digest reader A wrote into its own file.
#[test]
fn m7_the_record_still_transcribes_reader_as_own_provenance() {
    let p = prov();
    let a = record()["reader_a"].clone();
    for lane in [
        "crate_func_ids_seen",
        "crate_func_names_seen",
        "crate_global_ids_seen",
        "crate_global_names_seen",
        "global_tys_erased",
        "global_tys_resolved",
    ] {
        assert_eq!(
            a[lane], p[lane],
            "the mint record's `reader_a.{lane}` is no longer what reader A's own committed \
             provenance says; re-transcribe the record from generated/ir_lzc.core.prov.json"
        );
    }
    assert_eq!(
        record()["artifact_core_digest"],
        p["core_digest"],
        "the record's artifact_core_digest and reader A's own core_digest disagree"
    );
    assert_eq!(
        a["dump_sha256"], p["dump_sha256"],
        "…and the two disagree about WHICH binary was projected"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// M8 — the mint discriminates this chain from its two nearest neighbours.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn m8_the_mint_discriminates_across_the_minted_set() {
    for (who, core) in [
        ("ir_lz", ir_mint::IR_LZ_CORE),
        ("ir_hlb", ir_mint::IR_HLB_CORE),
        ("ir_h2", ir_mint::IR_H2_CORE),
    ] {
        assert_ne!(
            ir_mint::digest(ir_mint::IR_LZC_CORE),
            ir_mint::digest(core),
            "ir_lzc and {who} must not share a core digest"
        );
    }
    // The two neighbours, and what separates this chain from each. `ir_lz` is
    // the SAME ROOT BODY projected alone — one function, no global; `ir_hlb`
    // is the other two-function module — two functions, still no global.
    assert_eq!(
        ir_mint::IR_LZ_CORE.matches("(func ").count(),
        1,
        "ir_lz DEFINES one function and calls a second it does not define"
    );
    assert_eq!(ir_mint::IR_HLB_CORE.matches("(func ").count(), 2);
    assert!(
        ir_mint::IR_LZ_CORE.contains("  (globals)\n")
            && ir_mint::IR_HLB_CORE.contains("  (globals)\n"),
        "…and neither of them carries a global: ir_lzc is the first module that does"
    );
}

// The remaining lanes, in submodules because this file is at the 500-line
// convention (`crystal_a2_mint_hlb.rs` split its migration record out the same
// way); each uses this file's helpers through `super::`. `lzc_a1` is M5, the A1
// lane comparator over BOTH bodies — it needs helpers that hand each body its
// OWN definition lines, so they live beside it. `lzc_interface` is M10, the
// interface per body and per global. `lzc_m4` is reader C, the only lane here
// that pays a full Specification build. rustfmt orders the declarations, not
// the reading; read them in that order.
#[path = "crystal_a2_mint/lzc_a1.rs"]
mod lzc_a1;
#[path = "crystal_a2_mint/lzc_interface.rs"]
mod lzc_interface;
#[path = "crystal_a2_mint/lzc_m4.rs"]
mod lzc_m4;

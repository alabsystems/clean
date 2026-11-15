// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The `encodings` tag lane, and every refusal it makes.**
//!
//! The lane landed with the Phase-B `IRModule.mkv` arm and had NO test of its
//! own for two commits: the rows were exercised only by the chain that happens
//! to carry them, so every refusal in it was a gate nobody had seen fail. The
//! standing rule (`docs/GATE_REGISTRY.md` R-rules) is that such a gate is
//! `exit 0` until somebody falsifies it, and these are the falsifications.
//!
//! What each refusal is FOR, since none of them is arbitrary:
//!
//! * **kind** — `IREnc` has two constructors and the reader mints both. A
//!   third name is a row the reader cannot mint, and dropping it silently
//!   would leave the minted table smaller than the derived one with nothing
//!   saying so.
//! * **(kind, canonical) uniqueness** — `ir_enc_find` takes the FIRST match,
//!   so two rows at one key make the table's meaning depend on its order. The
//!   key is the PAIR, exactly as `ir_enc_matches` reads it: this chain's own
//!   table carries a niche row at 1 (`enum.1`) and a wrapper row at 1
//!   (`struct.1`), which are two different types, and an id-only key would
//!   refuse the real table.
//! * **slot < fields** — `ir_spine_with_slot i c` is `Nat.sub c (succ i)`, and
//!   `Nat.sub` TRUNCATES. At `i >= c` the spine is SHORT rather than
//!   ill-formed, so the row would mint and mean something nobody derived.
//! * **none /= some** — `ir_niche_image` gives the zero word `no` and every
//!   other word `so`. Equal, the row claims one variant answers both.

use super::tags;

/// The committed table with its `encodings` array replaced by `rows`.
fn with_encodings(rows: &str) -> String {
    let t = super::IR_LZD_TAGS;
    let open = t
        .find("\"encodings\":")
        .expect("the committed table has an encodings lane");
    let start = t[open..].find('[').expect("an array") + open;
    let mut depth = 0usize;
    let end = t[start..]
        .char_indices()
        .find_map(|(i, c)| {
            match c {
                '[' => depth += 1,
                ']' => depth -= 1,
                _ => {}
            }
            (depth == 0).then_some(start + i + 1)
        })
        .expect("a balanced array");
    format!("{}{rows}{}", &t[..start], &t[end..])
}

/// The control: the committed rows, unperturbed, parse.
///
/// Without it every refusal below could be passing because the harness itself
/// is broken — the failure mode the *Proof soundness rules* call a gate that
/// cannot say yes.
#[test]
fn the_committed_four_row_table_parses() {
    let t = tags::parse(&with_encodings(
        r#"[{"canonical":1,"kind":"nicheptr","none_variant":0,"some_variant":1,"payload":"(ptr)"},
            {"canonical":2,"kind":"nicheptr","none_variant":0,"some_variant":1,"payload":"(struct 0)"},
            {"canonical":0,"kind":"ptrwrap","slot":0,"fields":3,"payload":"(struct 1)"},
            {"canonical":1,"kind":"ptrwrap","slot":0,"fields":1,"payload":"(ptr)"}]"#,
    ))
    .expect("the committed rows must parse");
    assert_eq!(t.encodings.len(), 4, "four rows");
    assert!(
        matches!(
            t.encodings[2].kind,
            tags::EncKind::Wrap { slot: 0, fields: 3 }
        ),
        "the Arc row is a 3-field wrapper at slot 0: {:?}",
        t.encodings[2].kind
    );
}

/// **A niche row at 1 and a wrapper row at 1 are NOT a collision.**
///
/// This is the case an id-only uniqueness check gets wrong, and it is not
/// hypothetical — it is the shape of the crystal's own committed table. The
/// test is here so that tightening the check back to the id alone fails.
#[test]
fn one_canonical_index_may_carry_one_row_of_each_kind() {
    let t = tags::parse(&with_encodings(
        r#"[{"canonical":1,"kind":"nicheptr","none_variant":0,"some_variant":1,"payload":"(ptr)"},
            {"canonical":1,"kind":"ptrwrap","slot":0,"fields":1,"payload":"(ptr)"}]"#,
    ))
    .expect("`ir_enc_matches` keys on (kind, id), so these describe enum.1 and struct.1");
    assert_eq!(t.encodings.len(), 2);
}

#[test]
fn two_rows_of_the_same_kind_at_one_canonical_index_are_refused() {
    let e = tags::parse(&with_encodings(
        r#"[{"canonical":1,"kind":"nicheptr","none_variant":0,"some_variant":1,"payload":"(ptr)"},
            {"canonical":1,"kind":"nicheptr","none_variant":1,"some_variant":0,"payload":"(ptr)"}]"#,
    ))
    .expect_err("`ir_enc_find` takes the first match, so this table means whichever came first");
    let m = format!("{e}");
    assert!(
        m.contains("(kind, canonical)"),
        "the refusal must name the key: {m}"
    );
}

#[test]
fn a_wrapper_row_whose_slot_is_not_below_its_field_count_is_refused() {
    for (slot, fields) in [(1u32, 1u32), (3, 3), (7, 2)] {
        let e = tags::parse(&with_encodings(&format!(
            r#"[{{"canonical":0,"kind":"ptrwrap","slot":{slot},"fields":{fields},"payload":"(ptr)"}}]"#
        )))
        .expect_err("`Nat.sub` truncates, so an out-of-range slot mints a SHORT spine");
        let m = format!("{e}");
        assert!(
            m.contains("truncates") && m.contains(&format!("slot {slot}")),
            "the refusal must name the slot and the reason: {m}"
        );
    }
}

#[test]
fn a_niche_row_naming_one_variant_for_both_words_is_refused() {
    let e = tags::parse(&with_encodings(
        r#"[{"canonical":1,"kind":"nicheptr","none_variant":1,"some_variant":1,"payload":"(ptr)"}]"#,
    ))
    .expect_err("a niche row distinguishes two variants or it is not a niche row");
    let m = format!("{e}");
    assert!(
        m.contains("BOTH"),
        "the refusal must say what is contradictory: {m}"
    );
}

#[test]
fn a_kind_this_reader_cannot_mint_is_refused_rather_than_dropped() {
    for kind in ["tagged", "nicheint", "ptrwarp", ""] {
        let e = tags::parse(&with_encodings(&format!(
            r#"[{{"canonical":0,"kind":"{kind}","slot":0,"fields":1,"payload":"(ptr)"}}]"#
        )))
        .expect_err("an unmintable kind is refused, never dropped");
        let m = format!("{e}");
        assert!(
            m.contains("refused rather than dropped"),
            "the refusal must say it is not a drop: {m}"
        );
    }
}

/// A wrapper row with no `slot`, and a niche row with no `none_variant`, are
/// each refused by name — the `n()` helper's own message, checked because a
/// missing number would otherwise read as a zero.
#[test]
fn a_row_missing_the_number_its_kind_needs_is_refused_by_name() {
    let e = tags::parse(&with_encodings(
        r#"[{"canonical":0,"kind":"ptrwrap","fields":1,"payload":"(ptr)"}]"#,
    ))
    .expect_err("a ptrwrap row needs a slot");
    assert!(format!("{e}").contains("`slot`"), "{e}");
    let e = tags::parse(&with_encodings(
        r#"[{"canonical":0,"kind":"nicheptr","some_variant":1,"payload":"(ptr)"}]"#,
    ))
    .expect_err("a nicheptr row needs a none_variant");
    assert!(format!("{e}").contains("`none_variant`"), "{e}");
}

/// **An absent lane is the canonical layout, not an error.**
///
/// Every chain minted before Phase B has no `encodings` key at all, and their
/// tables must keep parsing unchanged — that is what makes the `mkv` arm
/// additive rather than a migration.
#[test]
fn a_table_with_no_encodings_lane_still_parses_and_mints_the_mk_arm() {
    let mut v: serde_json::Value =
        serde_json::from_str(super::IR_LZD_TAGS).expect("the committed table is JSON");
    let removed = v
        .as_object_mut()
        .expect("an object")
        .remove("encodings")
        .expect("the committed table has an encodings lane to remove");
    assert_eq!(
        removed.as_array().map(Vec::len),
        Some(4),
        "it removed the four rows"
    );
    let stripped = serde_json::to_string(&v).expect("re-serialize");
    let tags = tags::parse(&stripped).expect("a pre-Phase-B table must parse unchanged");
    assert!(tags.encodings.is_empty(), "no rows");

    let c = super::parse(super::IR_LZD_CORE).expect("reader A's core");
    let m = super::mint(&c, "ir_lzd", &tags).expect("it must still mint");
    let module = m
        .lines
        .iter()
        .find(|l| l.starts_with("def ir_lzd_module "))
        .expect("a module line");
    assert!(
        module.contains("IRModule.mk ") && !module.contains("IRModule.mkv"),
        "no rows means the `mk` arm, which `ir_mod_encs` sends to the EMPTY table:\n{module}"
    );
    assert!(
        !m.lines.iter().any(|l| l.contains(": IREnc :=")),
        "and no IREnc definitions are minted at all"
    );
}

/// **THE KEY MUST BE THE NUMBER THE ALIAS CARRIES.**
///
/// `ir_enc_matches` compares a row's first `Nat` against the number an
/// `IRTy.enum_` / `IRTy.struct_` presents, and an aggregate renders as the
/// chain's ALIAS, whose definition carries the CRATE-level id. A row minted at
/// the CANONICAL index therefore keys on a number no type in the module ever
/// presents.
///
/// `ir_lzd` shipped exactly that way on 2026-09-10 and nothing said so, because
/// no test executed a load at those types. The failure was not silence: this
/// chain's canonical indices and crate ids OVERLAP, so one mis-keyed row fired
/// at the wrong type (`Option<Arc<Level>>` decoded under the row derived for
/// `Option<&Level>`, dropping the Arc view) and another became SELF-REFERENTIAL
/// — `ptrwrap` at `struct.0` with payload `struct.0` — nesting once per unit of
/// the view's fuel and then falling back to the identity. The `extractfield`
/// after the load then faulted `not_agg`, 24 steps in, which is where it was
/// found.
///
/// This test reads the minted script and nothing else: for every `IREnc` line,
/// the key must equal the id in the alias definition of the type that row is
/// about. It needs no spec build, so it fails in a second rather than in a
/// kernel run.
#[test]
fn the_encodings_keys_are_the_ids_the_aliases_carry() {
    let t = tags::parse(super::IR_LZD_TAGS).expect("the committed tag table");
    let c = super::parse(super::IR_LZD_CORE).expect("reader A's core");
    let m = super::mint(&c, "ir_lzd", &t).expect("the module mints");

    // alias name -> the id its definition carries, per kind.
    let mut alias_id: std::collections::BTreeMap<String, (char, u32)> =
        std::collections::BTreeMap::new();
    for line in &m.lines {
        if let Some(rest) = line.strip_prefix("def ") {
            if let Some((name, body)) = rest.split_once(" : IRTy := ") {
                for (kind, tag) in [('e', "IRTy.enum_ ir_d"), ('s', "IRTy.struct_ ir_d")] {
                    if let Some(n) = body.strip_prefix(tag) {
                        let id: u32 = n.trim().parse().expect("an atom-pool numeral");
                        alias_id.insert(name.trim().to_string(), (kind, id));
                    }
                }
            }
        }
    }
    assert!(
        alias_id.len() >= 5,
        "this chain names five aggregates: {alias_id:?}"
    );

    let rows: Vec<&String> = m
        .lines
        .iter()
        .filter(|l| l.contains(" : IREnc := "))
        .collect();
    assert_eq!(
        rows.len(),
        t.encodings.len(),
        "one minted row per pinned row"
    );
    for (line, pin) in rows.iter().zip(&t.encodings) {
        let body = line.split(" : IREnc := ").nth(1).expect("a body");
        let parts: Vec<&str> = body.split_whitespace().collect();
        let (ctor, key) = (parts[0], parts[1]);
        let want_kind = match pin.kind {
            tags::EncKind::Niche { .. } => {
                assert_eq!(ctor, "IREnc.nicheptr", "{line}");
                'e'
            }
            tags::EncKind::Wrap { .. } => {
                assert_eq!(ctor, "IREnc.ptrwrap", "{line}");
                's'
            }
        };
        let (want_id, _) = if want_kind == 'e' {
            t.enum_alias(pin.canonical)
                .expect("the row's canonical index is named")
        } else {
            t.struct_alias(pin.canonical)
                .expect("the row's canonical index is named")
        };
        assert_eq!(
            key,
            &format!("ir_d{want_id}"),
            "the row keyed at canonical {} must carry the CRATE id {want_id} that its alias \
             definition carries, or `ir_enc_matches` can never fire for it:\n{line}",
            pin.canonical
        );
    }

    // And the ROW THIS CHAIN DEPENDS ON, by name: the Arc wrapper's payload is
    // the NonNull alias, and the two must be DIFFERENT aggregates. A row whose
    // payload type resolves back to the row's own key is the self-referential
    // shape that consumed the view's fuel and then read as the identity.
    for (line, pin) in rows.iter().zip(&t.encodings) {
        let payload = line.split_whitespace().last().expect("a payload");
        if let Some((kind, id)) = alias_id.get(payload) {
            let (own_id, _) = match pin.kind {
                tags::EncKind::Niche { .. } => t.enum_alias(pin.canonical).expect("named"),
                tags::EncKind::Wrap { .. } => t.struct_alias(pin.canonical).expect("named"),
            };
            let own_kind = if matches!(pin.kind, tags::EncKind::Niche { .. }) {
                'e'
            } else {
                's'
            };
            assert!(
                !(*kind == own_kind && id == own_id),
                "a row whose payload type IS the type it describes re-enters the view once per \
                 unit of fuel and then reads as the identity:\n{line}"
            );
        }
    }
}

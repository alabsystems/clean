// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Reader B over the COMMITTED FIXTURE CORPUS — the one test that walks every
//! `tests/fixtures/*.trust-ir*.txt` this crate ships and prints, per fixture,
//! whether reader B read it or why it refused.
//!
//! A sibling of [`super::tests`] rather than a section inside it: the corpus
//! denominator is one unit that grows with every chain (the pinned
//! `node_id_index` read, the `ir_hlb` pair, the `ir_lzc` triple), and the file
//! it used to sit in is already over the repository's 500-line cap — the same
//! reason [`super::tests_globals`] is a sibling.

use super::{core, read_emitted, tags, SelfFunc};

#[test]
fn reader_b_reads_every_committed_chain_fixture_or_says_why() {
    // Coverage, printed rather than assumed. A fixture reader B cannot read is
    // recorded here with its refusal; it is never silently skipped.
    let fixtures: &[(&str, &str)] = &[
        (
            "has_cubical_layer",
            include_str!("../../tests/fixtures/has_cubical_layer.trust-ir.txt"),
        ),
        (
            "level_kind_ord",
            include_str!("../../tests/fixtures/level_kind_ord.trust-ir.txt"),
        ),
        (
            "from_source_system",
            include_str!("../../tests/fixtures/from_source_system.trust-ir.txt"),
        ),
        (
            "expr_path_step_clone",
            include_str!("../../tests/fixtures/expr_path_step_clone.trust-ir.txt"),
        ),
        (
            "level_is_zero",
            include_str!("../../tests/fixtures/level_is_zero.trust-ir.txt"),
        ),
        (
            "bvar_in_range",
            include_str!("../../tests/fixtures/bvar_in_range.trust-ir.txt"),
        ),
        (
            "flat_flags_contains",
            include_str!("../../tests/fixtures/flat_flags_contains.trust-ir.txt"),
        ),
        (
            "flat_flags_with",
            include_str!("../../tests/fixtures/flat_flags_with.trust-ir.txt"),
        ),
        (
            "float_div",
            include_str!("../../tests/fixtures/float_div.trust-ir.txt"),
        ),
        (
            "get_char_val_trunc",
            include_str!("../../tests/fixtures/get_char_val_trunc.trust-ir.txt"),
        ),
        (
            "is_valid_char",
            include_str!("../../tests/fixtures/is_valid_char.trust-ir.txt"),
        ),
        (
            "meta_tag_shl",
            include_str!("../../tests/fixtures/meta_tag_shl.trust-ir.txt"),
        ),
        (
            "strict_monads",
            include_str!("../../tests/fixtures/strict_monads.trust-ir.txt"),
        ),
    ];
    let mut report = String::from("\nreader B over the committed chain fixtures\n");
    let mut ok = 0usize;
    // `node_id_index` is read through its PIN, separately below: its body
    // contains `usize`, which reader B refuses by design until the chain's
    // tag table states the width. The pinned read is part of this
    // denominator, not an exemption from it.
    for (name, text) in fixtures {
        match read_emitted(text) {
            Ok(sx) => {
                core::print(&sx).expect("a read fixture must print");
                ok += 1;
                report.push_str(&format!("  {name:<22} READ\n"));
            }
            Err(e) => report.push_str(&format!("  {name:<22} REFUSED: {e}\n")),
        }
    }
    let ni_text = include_str!("../../tests/fixtures/node_id_index.trust-ir.txt");
    match super::emitted::read_with_pins(ni_text, SelfFunc::Unpinned, Some(64)) {
        Ok((sx, tags)) => {
            core::print(&sx).expect("a read fixture must print");
            assert_eq!(tags.usize_seen, 1, "one resolved usize site");
            ok += 1;
            report.push_str("  node_id_index          READ (usize pinned at 64)\n");
        }
        Err(e) => report.push_str(&format!("  node_id_index          REFUSED: {e}\n")),
    }
    // The CALL chain's two bodies are read through the chain's tag table, not
    // bare, and that is not a concession: its module holds TWO functions, so
    // reader B has to be told how many bodies the text carries and which
    // canonical index each occupies. Read bare, the pair would produce two
    // `(func 0 …)` modules — right for neither, and a module whose two
    // functions share an id is one `ir_func_find` cannot walk.
    let hlb = include_str!("../../tests/fixtures/has_loose_bvars.trust-ir.txt");
    let lbr = include_str!("../../tests/fixtures/loose_bvar_range_callee.trust-ir.txt");
    let ht = tags::parse(super::IR_HLB_TAGS).expect("the hlb tag table must parse");
    match super::project(&format!("{hlb}{lbr}"), &ht) {
        Ok(p) => {
            core::print(&p.core).expect("a read chain must print");
            assert_eq!(p.interfaces.len(), 2, "one interface per body");
            ok += 1;
            report.push_str("  has_loose_bvars+callee READ (two bodies, one module)\n");
        }
        Err(e) => report.push_str(&format!("  has_loose_bvars+callee REFUSED: {e}\n")),
    }
    // The `ir_lzc` TRIPLE: the module-table PREAMBLE fixture, then the two
    // bodies in module order. The preamble is a fixture of its own because the
    // rows it carries (`type ty.0 = u8`, `global internal @__trust_promoted_4557
    // …`) are module-table facts and not part of either body's text — and
    // reader B needs them, because the deref takes a global's ADDRESS and the
    // core module holds the global's BYTES. Read without the preamble the
    // triple is refused, not silently read with an empty global list; the
    // gate's `m2_reader_b_refuses_*` cases pin that.
    let lzc_globals =
        include_str!("../../tests/fixtures/level_is_zero_deref_globals.trust-ir-rows.txt");
    let lzc_is_zero = include_str!("../../tests/fixtures/level_is_zero.trust-ir.txt");
    let lzc_deref = include_str!("../../tests/fixtures/level_is_zero_deref_callee.trust-ir.txt");
    let lt = tags::parse(super::IR_LZC_TAGS).expect("the lzc tag table must parse");
    match super::project(&format!("{lzc_globals}{lzc_is_zero}{lzc_deref}"), &lt) {
        Ok(p) => {
            core::print(&p.core).expect("a read chain must print");
            assert_eq!(p.interfaces.len(), 2, "one interface per body");
            ok += 1;
            report.push_str("  level_is_zero+deref    READ (two bodies, one global)\n");
        }
        Err(e) => report.push_str(&format!("  level_is_zero+deref    REFUSED: {e}\n")),
    }
    println!("{report}");
    assert_eq!(
        ok,
        fixtures.len() + 3,
        "reader B must read every committed chain fixture:{report}"
    );
}

/// **The three DERIVED callee bodies, read.**
///
/// Phase B's module retires the authored `ir_lzb_deref` by putting the real
/// bodies of `Option::as_deref`, `Option::expect` and `<Arc<T>>::deref` into
/// the module beside the deref that calls them. Those three come from the
/// callee sidecar, not from the crate module, and they use three instruction
/// forms no committed chain fixture contains: `alloca`, `borrow` and `copy`.
/// Reader B refused all three by name until this lane, which is the recorded
/// posture for a mnemonic outside the fragment.
///
/// This test reads the COMMITTED BUNDLE and cuts the bodies out of it, rather
/// than transcribing them into a `const`. A transcription is a second copy of
/// the thing under test, and the failure it hides is the one that matters: a
/// printed form the producer emits and the transcription tidied.
///
/// Read BARE, one body at a time. That is deliberate and it is not the whole
/// question: a bare read has no funcs namespace, so `as_deref`'s call to
/// `<Arc<T>>::deref` is refused the way any bare read refuses a call it cannot
/// resolve. What this establishes is the INSTRUCTION FORMS, which is what was
/// missing; the namespace is the chain's tag table's job and lands with it.
#[test]
fn reader_b_reads_the_derived_callee_bodies_instruction_forms() {
    const BUNDLE: &str = include_str!(
        "../../../../data/crystal_callee_sidecar_step1_2026-09-09/clean_kernel.callees.trust-ir.txt"
    );
    // Cut every `fn @NAME(functy.N) {` .. `}` block out of the bundle. The
    // bundle also carries a module header, a type table and trailing
    // `obligation` rows, none of which is a body.
    let mut bodies: Vec<(String, String)> = Vec::new();
    let mut cur: Option<(String, String)> = None;
    for line in BUNDLE.lines() {
        if let Some(rest) = line.strip_prefix("fn @") {
            if let Some(open) = rest.find("(functy.") {
                cur = Some((rest[..open].to_string(), format!("{line}\n")));
                continue;
            }
        }
        if let Some((_, text)) = cur.as_mut() {
            text.push_str(line);
            text.push('\n');
            if line.starts_with('}') {
                let done = cur.take().expect("a block was open");
                bodies.push(done);
            }
        }
    }
    assert_eq!(
        bodies.len(),
        3,
        "the committed bundle carries exactly three derived bodies"
    );

    // Every instruction form the three bodies use, so that a body reading for
    // the WRONG reason (an arm silently accepting the line as something else)
    // cannot pass unnoticed. The three this lane adds are asserted present.
    let mut forms: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    for (_, text) in &bodies {
        for line in text.lines() {
            let t = line.split(';').next().unwrap_or("").trim();
            let t = t.split_once(" = ").map_or(t, |(_, rhs)| rhs);
            if let Some(head) = t.split_whitespace().next() {
                if !head.is_empty() && head.chars().all(|c| c.is_ascii_lowercase() || c == '_') {
                    forms.insert(head.to_string());
                }
            }
        }
    }
    for want in ["alloca", "borrow", "copy"] {
        assert!(
            forms.contains(want),
            "the bundle must exercise `{want}`; it carries {forms:?}"
        );
    }

    // Read through a PINNED target width. Two of the three contain `isize`
    // (`zext u8 %n to isize`, the discriminant widening), which reader B
    // refuses bare for exactly the reason it refuses `usize`: the width is a
    // target fact and resolving it silently would bake an unstated word size
    // into the core module. 64 is this target's, and it is supplied here the
    // same way `node_id_index` supplies it above.
    let mut report = String::from("\nreader B over the DERIVED callee bodies\n");
    let mut read = 0usize;
    let mut isize_sites = 0u32;
    for (name, text) in &bodies {
        let short: String = name.chars().take(46).collect();
        match super::emitted::read_with_pins(text, SelfFunc::Unpinned, Some(64)) {
            Ok((sx, tags)) => {
                core::print(&sx).expect("a read body must print");
                isize_sites += tags.isize_seen;
                read += 1;
                report.push_str(&format!(
                    "  {short:<48} READ ({} isize site(s))\n",
                    tags.isize_seen
                ));
            }
            Err(e) => report.push_str(&format!("  {short:<48} REFUSED: {e}\n")),
        }
    }
    println!("{report}");
    assert_eq!(
        read, 3,
        "every derived callee body must read; a refusal here is an instruction \
         form or a type reader B still cannot parse:{report}"
    );
    assert_eq!(
        isize_sites, 2,
        "the two discriminant widenings are the chain's only `isize` sites, and \
         they are COUNTED so the tag table can pin them:{report}"
    );

    // The refusal is still there when the width is NOT pinned, so the pin is
    // load-bearing rather than decorative.
    let with_isize = bodies
        .iter()
        .find(|(_, t)| t.contains(" to isize"))
        .expect("two bodies widen a discriminant to isize");
    let e = read_emitted(&with_isize.1)
        .map(|_| ())
        .expect_err("an unpinned `isize` must still be refused");
    assert!(
        format!("{e}").contains("TARGET-DEPENDENT"),
        "the refusal must name why, not merely refuse: {e}"
    );
}

/// **THE FIVE-BODY DERIVED MODULE PROJECTS AS ONE CLOSED MODULE.**
///
/// This is what Phase B is for. Link 4 for `level::Level::is_zero` holds today
/// over `ir_lzb_module`, whose function 1 is an AUTHORED model of the deref.
/// Retiring it needs the deref's own callees to be bodies of the same module,
/// and this test measures that they can be.
///
/// Five bodies from TWO artifacts: `level::Level::is_zero` and
/// `<level::LevelArc as std::ops::Deref>::deref` from the committed crate
/// fixtures, and `Option::as_deref`, `Option::expect` and
/// `<Arc<Level> as Deref>::deref` cut from the committed callee-sidecar
/// bundle. NINE calls, every one resolving to a canonical index 0..=4 — there
/// is no call to a function the module does not define, which is exactly what
/// `ir_lz` and `ir_lzc` could not say.
///
/// THE CONCATENATION NEEDS NO RENUMBERING, and that is asserted rather than
/// assumed because it is luck and not design: the crate bodies name `enum.3`
/// and call `@func.1947/1961/4925/4924` (`enum.2` and `@func.3894/3905/6516/7211`
/// before the 2026-10-07 rebaseline), the sidecar bodies name `enum.0`,
/// `enum.1`, `struct.0`, `struct.3` and call `@func.2`, and the two id sets
/// are disjoint. A re-dump that collided would break this, and the assertion
/// says so rather than letting a silent overlap through.
///
/// WHAT THIS DOES NOT CLAIM. It projects; it does not MINT. The minter is fed
/// reader A's core, not reader B's, and reader B's carries `?` for the
/// `switch` flag trust-ir's printer never prints — so `mint` over this
/// projection correctly refuses. Minting `ir_lzd` needs the merged text run
/// through `scripts/crystal_a2_project`, which is the next step and not this
/// one. Nor does anything here assert A4 or A5.
#[test]
fn the_five_body_derived_module_projects_as_one_closed_module() {
    const BUNDLE: &str = include_str!(
        "../../../../data/crystal_callee_sidecar_step1_2026-09-09/clean_kernel.callees.trust-ir.txt"
    );
    const GLOBALS: &str =
        include_str!("../../tests/fixtures/level_is_zero_deref_globals.trust-ir-rows.txt");
    const IS_ZERO: &str = include_str!("../../tests/fixtures/level_is_zero.trust-ir.txt");
    const DEREF: &str =
        include_str!("../../tests/fixtures/level_is_zero_deref_callee.trust-ir.txt");

    let mut cut: std::collections::BTreeMap<String, String> = std::collections::BTreeMap::new();
    let mut cur: Option<(String, String)> = None;
    for line in BUNDLE.lines() {
        if let Some(rest) = line.strip_prefix("fn @") {
            if let Some(open) = rest.find("(functy.") {
                cur = Some((rest[..open].to_string(), format!("{line}\n")));
                continue;
            }
        }
        if let Some((_, text)) = cur.as_mut() {
            text.push_str(line);
            text.push('\n');
            if line.starts_with('}') {
                let (n, t) = cur.take().expect("open");
                cut.insert(n, t);
            }
        }
    }
    let pick = |needle: &str| -> (String, String) {
        let (k, v) = cut
            .iter()
            .find(|(k, _)| k.contains(needle))
            .unwrap_or_else(|| panic!("no derived body matching {needle}"));
        (k.clone(), v.clone())
    };
    let (n_as_deref, as_deref) = pick("as_deref");
    let (n_expect, expect) = pick("::expect::");
    let (n_arc, arc) = pick("as core::ops::deref::Deref>::deref");

    let table = format!(
        r#"{{"body":"level::Level::is_zero",
  "interface":{{"linkage":"external","calling_conv":"rustcc","functy":0,"producer":"trust",
   "params":[{{"block":0,"index":0,"ssa":0,"ty":"ptr"}}],
   "block_params":[{{"block":6,"index":0,"ssa":1,"ty":"bool"}},
                   {{"block":9,"index":0,"ssa":2,"ty":"bool"}}],
   "aligns":["load:None"],"clauses":["loc","names","producer"]}},
  "enums":[{{"canonical":0,"crate_id":3,"alias":"ir_lzd_tlevel"}},
           {{"canonical":1,"crate_id":0,"alias":"ir_lzd_topt_ref"}},
           {{"canonical":2,"crate_id":1,"alias":"ir_lzd_topt_arc"}}],
  "structs":[{{"canonical":0,"crate_id":3,"alias":"ir_lzd_tarc"}},
             {{"canonical":1,"crate_id":0,"alias":"ir_lzd_tnonnull"}}],
  "funcs":[{{"canonical":0,"crate_id":1961,"name":"level::Level::is_zero"}},
           {{"canonical":1,"crate_id":1947,"name":"<level::LevelArc as std::ops::Deref>::deref"}},
           {{"canonical":2,"crate_id":4924,"name":"{n_as_deref}"}},
           {{"canonical":3,"crate_id":4925,"name":"{n_expect}"}},
           {{"canonical":4,"crate_id":2,"name":"{n_arc}"}}],
  "extra_bodies":[
   {{"canonical":1,"prefix":"ir_lad","body":"<level::LevelArc as std::ops::Deref>::deref",
     "interface":{{"linkage":"external","calling_conv":"rustcc","functy":22,"producer":"trust",
      "params":[{{"block":0,"index":0,"ssa":0,"ty":"ptr"}}],"block_params":[],"aligns":[],
      "clauses":["loc","names","producer"]}}}},
   {{"canonical":2,"prefix":"ir_lad2","body":"{n_as_deref}",
     "interface":{{"linkage":"external","calling_conv":"ccc","functy":1,"producer":"trust-ir",
      "params":[{{"block":0,"index":0,"ssa":0,"ty":"ptr"}}],"block_params":[],
      "aligns":["alloca:None","load:None","store:None","load:None","store:None"],
      "clauses":["producer","proof"]}}}},
   {{"canonical":3,"prefix":"ir_lad3","body":"{n_expect}",
     "interface":{{"linkage":"external","calling_conv":"ccc","functy":0,"producer":"trust-ir",
      "params":[{{"block":0,"index":0,"ssa":0,"ty":"enum#1"}},
                {{"block":0,"index":1,"ssa":1,"ty":"fatptr<str>"}}],
      "block_params":[],"aligns":[],"clauses":["producer","proof"]}}}},
   {{"canonical":4,"prefix":"ir_lad4","body":"{n_arc}",
     "interface":{{"linkage":"external","calling_conv":"ccc","functy":2,"producer":"trust-ir",
      "params":[{{"block":0,"index":0,"ssa":0,"ty":"ptr"}}],"block_params":[],
      "aligns":["load:None"],"clauses":["producer","proof"]}}}}],
  "globals":[{{"canonical":0,"crate_id":1135,"name":"__trust_promoted_1135","ty":"[u8 x 34]",
    "linkage":"internal"}}],
  "usize":{{"bits":64,"sites":0,"isize_sites":2}}}}"#
    );
    // The disjointness the straight concatenation rests on.
    let agg_ids = |t: &str| -> std::collections::BTreeSet<String> {
        let mut out = std::collections::BTreeSet::new();
        for tok in t.split(|c: char| !(c.is_ascii_alphanumeric() || c == '.' || c == '_')) {
            if tok.starts_with("enum.") || tok.starts_with("struct.") {
                out.insert(tok.to_string());
            }
        }
        out
    };
    let crate_side = agg_ids(&format!("{IS_ZERO}{DEREF}"));
    let sidecar_side = agg_ids(&format!("{as_deref}{expect}{arc}"));
    let overlap: Vec<&String> = crate_side.intersection(&sidecar_side).collect();
    assert!(
        overlap.is_empty(),
        "the two artifacts' aggregate ids overlap at {overlap:?}; the straight concatenation \
         below is only sound because they are disjoint, so a re-dump that collides needs a \
         renumbering pass rather than this test relaxed"
    );

    let t = tags::parse(&table).expect("the five-body tag table must parse");
    let text = format!("{GLOBALS}{IS_ZERO}{DEREF}{as_deref}{expect}{arc}");
    let p = super::project(&text, &t).expect("the five-body derived module must project");
    assert_eq!(p.interfaces.len(), 5, "one interface per body");
    let printed = core::print(&p.core).expect("print");
    assert_eq!(
        printed.matches("(func ").count(),
        5,
        "five functions in one module"
    );
    assert_eq!(
        printed.matches("(global ").count(),
        1,
        "the promoted expect message"
    );

    // THE CLOSURE. Nine calls, and every one names a function this module
    // defines. `ir_lz` went stuck at the deref it did not define; `ir_lzc`
    // went one deeper, at `as_deref`. This module has no such call.
    assert_eq!(printed.matches("(call ").count(), 9, "nine calls");
    let resolved: usize = (0..5)
        .map(|k| printed.matches(&format!("(call {k}")).count())
        .sum();
    assert_eq!(
        resolved, 9,
        "every call must name a canonical index this module defines (0..=4); a call above 4 \
         would be the `stuck no_func` this whole chain exists to remove"
    );

    // …and the minter correctly REFUSES reader B's core, which is why the mint
    // is fed reader A's. Asserted so the boundary between the two readers is
    // measured rather than remembered.
    let e = super::mint(&p.core, "ir_lzd", &t)
        .map(|_| ())
        .expect_err("reader B's core carries `?` for the unprinted switch flag");
    assert!(
        format!("{e}").contains("could not witness"),
        "the refusal must be the unwitnessed-flag one, not something else: {e}"
    );

    // ── THE SECOND READER, and it is CROSS-DUMP ────────────────────────────
    //
    // Reader A projected `ir_lzd` from `dump-sidecar-O3`, where `is_zero` is
    // `@func.1815` and the promoted message is `@global.1055`. Reader B here
    // reads the committed fixtures, cut since the 2026-10-07 rebaseline from
    // the clean 047ebd051 dump, where the same bodies are `@func.1961` and
    // `@global.1135` (`@func.3905` / `@global.4557` on the control dump). Different artifacts,
    // different whole-crate numbering, same bodies.
    //
    // They must still produce the SAME core, and that is not a coincidence to
    // be checked loosely: the core is written in CANONICAL indices, and each
    // reader resolves its own dump's ids through its own tag table. So this is
    // a STRONGER agreement than the usual two-reader check, which compares two
    // readers of ONE artifact. It also needs no new fixture, which matters:
    // adding one is gated by `check_crystal_fixture_pins.py`, a review act.
    //
    // Masked on both sides, because reader B cannot witness the `switch` flag
    // trust-ir's printer never emits and reader A reads it from the binary.
    // The mask is the ONLY licensed difference and the ledger is asserted to
    // be exactly that one field.
    let a = core::parse(super::IR_LZD_CORE).expect("reader A's committed core parses");
    let (a_masked, a_led) = super::mask_text_unwitnessed(&a).expect("mask A");
    let (b_masked, b_led) = super::mask_text_unwitnessed(&p.core).expect("mask B");
    assert_eq!(
        core::print(&b_masked).expect("print B"),
        core::print(&a_masked).expect("print A"),
        "reader A (dump-sidecar-O3, merged + joined) and reader B (the committed control-dump \
         fixtures + the committed sidecar bundle) disagree about the five-body module. They read \
         DIFFERENT artifacts with different whole-crate ids, so the cores agreeing is the claim; \
         a disagreement here is a real one and not a numbering artefact"
    );
    assert_eq!(
        a_led.len(),
        b_led.len(),
        "the two readers must have the SAME unwitnessed ledger; a field one of them can see and \
         the other cannot is the kind of difference this mask must never hide"
    );
    assert!(
        !a_led.is_empty(),
        "the mask must have masked something — the `switch` flag — or this comparison is not \
         checking what it says it checks"
    );
}

/// **The re-emitter the failure message names.**
///
/// Every mint test's message says "re-emit rather than hand-editing", and until
/// 2026-09-10 there was nothing to re-emit WITH — so the only way to move a
/// `defs.txt` was the edit the message forbids. `CLEAN_IR_MINT_REEMIT=1` writes
/// the minted script back over the committed one and then FAILS anyway, naming
/// the file it wrote: a re-emit is a change to a committed artifact and must be
/// reviewed as one, never absorbed by a green run.
fn reemit_or_compare(slug: &str, minted: &str, committed: &str) {
    if minted == committed {
        return;
    }
    if std::env::var_os("CLEAN_IR_MINT_REEMIT").is_some() {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("src/spec/core_spec/generated")
            .join(format!("{slug}.defs.txt"));
        std::fs::write(&path, minted).expect("re-emit must be able to write the artifact");
        panic!(
            "RE-EMITTED {}: the committed script was stale and has been rewritten. Review the \
             diff and re-run WITHOUT CLEAN_IR_MINT_REEMIT.",
            path.display()
        );
    }
    assert_eq!(
        minted, committed,
        "the minted script and the committed one disagree; re-emit rather than hand-editing \
         (CLEAN_IR_MINT_REEMIT=1 to rewrite {slug}.defs.txt, which then fails on purpose)"
    );
}

/// **`ir_lzd` MINTS: the five-body derived module as an `IRModule`.**
///
/// This is the artifact that retires the authored `ir_lzb_deref`. Reader A
/// projected it from TWO compiler artifacts — the crate module's own `.bin`
/// and the callee sidecar's bundle — relocating the bundle's function ids
/// above the crate module's and retargeting the crate DECLARATIONS to the
/// bodies the sidecar supplies, through the sidecar manifest's own join. Both
/// input digests and both retargets are in `ir_lzd.core.prov.json`.
///
/// The result is CLOSED: five functions, nine calls, every call naming a
/// canonical index the module defines. `ir_lz` was stuck at the deref it did
/// not define; `ir_lzc` one call deeper at `as_deref`; this module has no such
/// call, and no authored function in it.
///
/// IT HAS ITS SECOND READER, and the paragraph that stood here saying it did
/// not is RETRACTED — it was written before the comparison was tried, and the
/// reason it seemed impossible was wrong. It read: reader B's input "would
/// have to be cut from the SAME dump reader A read", and adding such a fixture
/// is gated by `check_crystal_fixture_pins.py`, a review act. Both halves of
/// that are false. The core is written in CANONICAL indices, and each reader
/// resolves its own dump's ids through its own tag table, so two readers of
/// DIFFERENT dumps of the same bodies must still produce the same core. They
/// do: [`the_five_body_derived_module_projects_as_one_closed_module`] reads
/// the committed CONTROL-dump fixtures plus the committed sidecar bundle and
/// compares its core, masked, against reader A's — which came from
/// `dump-sidecar-O3` where the same bodies are `@func.1815` and
/// `@global.1055` rather than `@func.3905` and `@global.4557`.
///
/// That is a STRONGER agreement than the older chains have, which compare two
/// readers of ONE artifact, and it needed no new fixture at all.
///
/// What is still absent is A4 and A5: nothing here asserts either.
#[test]
fn ir_lzd_mints_the_five_body_derived_module() {
    let t = tags::parse(super::IR_LZD_TAGS).expect("the five-body tag table must parse");
    let c = core::parse(super::IR_LZD_CORE).expect("reader A's committed core must parse");
    let m = super::mint(&c, "ir_lzd", &t).expect("the five-body module must mint");
    reemit_or_compare("ir_lzd", &(m.lines.join("\n") + "\n"), super::IR_LZD_DEFS);

    // FIVE functions in one `IRModule.mk`, in module order.
    let module = m
        .lines
        .iter()
        .find(|l| l.starts_with("def ir_lzd_module "))
        .expect("a module line");
    for f in [
        "ir_lzd_func",
        "ir_lzd_f1_func",
        "ir_lzd_f2_func",
        "ir_lzd_f3_func",
        "ir_lzd_f4_func",
    ] {
        assert!(module.contains(f), "the module must carry {f}:\n{module}");
    }
    assert_eq!(
        module.matches("@IRList.cons IRFunc").count(),
        5,
        "exactly five functions:\n{module}"
    );

    // The closure, read off reader A's core rather than asserted.
    let printed = super::IR_LZD_CORE;
    assert_eq!(printed.matches("(func ").count(), 5, "five function bodies");
    assert_eq!(printed.matches("(call ").count(), 9, "nine calls");
    let resolved: usize = (0..5)
        .map(|k| printed.matches(&format!("(call {k}")).count())
        .sum();
    assert_eq!(
        resolved, 9,
        "every call must name a canonical index this module defines; a call above 4 is the \
         `stuck no_func` this chain exists to remove"
    );

    // The two retargets are RECORDED, not implied: without them the module
    // would hold the bodyless declarations and still be stuck.
    for pair in ["\"declaration\": 4938", "\"declaration\": 4939"] {
        assert!(
            super::IR_LZD_PROVENANCE.contains(pair),
            "reader A must record which declaration each body was joined to: {pair}"
        );
    }
}

/// **`ir_cf` gets its reader-B comparison** — the check every other
/// chain's committed core already had, and these two did not.
///
/// Measured 2026-09-20: `generated/ir_{cf,sh}.core.txt` and
/// `generated/ir_{cf,sh}.emitted.txt` were BOTH committed, their
/// `ir_<m>_module` was registered in the spec, and `ir_mint` mentioned neither
/// module anywhere — no `IR_*_CORE`, no gate, no libtest. So each had exactly
/// ONE reader, the one that produced the file, and nothing in the tree would
/// have noticed the committed core drifting from the committed emitted text.
///
/// Masked on both sides for the same reason every sibling comparison masks:
/// reader B cannot witness a `switch`'s exhaustive flag, which trust-ir's
/// printer never emits and reader A reads from the binary. The ledgers are
/// asserted EQUAL and the mask is only licensed where both readers are blind
/// together — a field one can see and the other cannot is exactly what this
/// must never hide.
#[test]
fn ir_cf_core_agrees_with_its_emitted_text() {
    // `ir_sh` is NOT in this loop, and the reason is measured rather than
    // assumed. With the usize width pinned it still refuses at
    // `NoImage("type `(usize,`")` — a TUPLE in its emitted text, which needs the
    // tag table's aggregate/type lane and not merely a word size. That is a
    // second, different interface fact, so `ir_sh` keeps its one-reader status
    // until someone reads that lane properly. Forcing it into this loop would
    // mean relaxing the comparison to pass, which is the opposite of the point.
    // A HELPER CALLED ONCE PER CHAIN, not a one-element loop. The loop shape
    // said "a second chain is expected here", which is true, but clippy's
    // `single_element_loop` refuses it and an `#[allow]` would have to be
    // removed again the day `ir_sh` lands. A call per chain says the same thing
    // and adding one is a line rather than a shape change.
    fn check_chain(name: &str, core_text: &str, emitted: &str, tag_text: &str) {
        let t = tags::parse(tag_text)
            .unwrap_or_else(|e| panic!("{name}: the committed tag table must parse: {e:?}"));
        let a = core::parse(core_text)
            .unwrap_or_else(|e| panic!("{name}: reader A's committed core must parse: {e:?}"));
        // `read_with_self`, NOT `project`. `project` joins a MULTI-BODY module
        // against a tag table — it is what `ir_lzd`'s five-body case needs — and
        // on a single-body chain it fails on a pinned-name mismatch
        // (`..from_output` against `..from_output::<__trust_args@8..>`), which
        // is an interface difference and not a disagreement about the body.
        // Measured here before the harness was corrected.
        // `read_with_pins`, and the `Some(64)` is LOAD-BEARING: it is the pinned
        // usize width. Without it `ir_sh` is refused outright — "`usize` is
        // TARGET-DEPENDENT, and resolving it silently would bake an unstated
        // word-size assumption into the core module" — which is the reader
        // protecting a real property, not an obstacle. 64 is this target's word
        // size and the same constant `crystal_a2_mint_it.rs` pins.
        //
        // NOT `project`: that joins a MULTI-BODY module against a tag table
        // (what `ir_lzd`'s five-body case needs) and fails here on a pinned-name
        // mismatch (`..from_output` vs `..from_output::<__trust_args@8..>`),
        // which is an interface difference and not a disagreement about a body.
        let (b_core, _observed) = super::read_emitted_with_pins(emitted, t.self_func(), Some(64))
            .unwrap_or_else(|e| panic!("{name}: reader B must read the emitted text: {e:?}"));

        let (a_masked, a_led) =
            super::mask_text_unwitnessed(&a).unwrap_or_else(|e| panic!("{name}: mask A: {e:?}"));
        let (b_masked, b_led) = super::mask_text_unwitnessed(&b_core)
            .unwrap_or_else(|e| panic!("{name}: mask B: {e:?}"));

        assert_eq!(
            core::print(&b_masked).unwrap_or_else(|e| panic!("{name}: print B: {e:?}")),
            core::print(&a_masked).unwrap_or_else(|e| panic!("{name}: print A: {e:?}")),
            "{name}: the committed CORE (reader A) and the committed EMITTED text (reader B) \
             disagree about this module. Until 2026-09-20 nothing compared them."
        );
        assert_eq!(
            a_led.len(),
            b_led.len(),
            "{name}: the two readers must have the SAME unwitnessed ledger; a field one can see \
             and the other cannot is what this mask must never hide"
        );
    }

    check_chain(
        "ir_cf",
        super::IR_CF_CORE,
        super::IR_CF_EMITTED,
        super::IR_CF_TAGS,
    );
}

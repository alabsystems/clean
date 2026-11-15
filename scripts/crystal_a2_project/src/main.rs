// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! READER A of the crystal-A2 mint gate: crate-level trust-ir `.bin` -> the
//! canonical CORE MODULE text `clean-verify` commits and mints from.
//!
//! Reads the binary the compiler emitted, finds ONE function by name, applies
//! the PRODUCER's own canonical form (`trust_ir::format::canonicalize` — dense
//! SSA renumbering, the same rendering the committed `.trust-ir.txt` fixtures
//! are), projects it onto the fragment Clean's `IRModule` encodes, renumbers
//! the crate-level interning tables by first use, and prints the result.
//!
//! Fail-closed everywhere: an unmappable type, constant or instruction is an
//! error, never an approximation. Its output is a COMMITTED artifact
//! (`crates/clean-verify/src/spec/core_spec/generated/ir_*.core.txt`) that two
//! independent in-tree readers check, so a defect here shows up as a
//! disagreement in `tests/crystal_a2_mint.rs` rather than as a silent pass.

// A wildcard arm over a trust_ir enum compiles unchanged when trust-ir adds a
// variant, so the projector would refuse a shape nobody classified. Every
// enum match here names its variants, and scripts/check_lint_coverage.py holds
// the WHOLE crate to that -- tests included -- on every invocation (the
// pre-push hook's `lint-coverage` leg and scripts/local_gate.sh): its typed
// scan (scripts/lint_types, rustc itself over the THIR) refuses any catch-all
// -- `_`, a binding, a field left out, the failure branch of an `if let` or a
// `let .. else` -- standing for variants of a trust_ir enum (or of this
// crate's own) that another alternative names, and clippy's three wildcard
// lints, FORBIDDEN on the command line (an `#[allow]` here is error E0453),
// refuse what they read.
#![deny(
    clippy::wildcard_enum_match_arm,
    clippy::match_wildcard_for_single_variants,
    clippy::wildcard_in_or_patterns
)]

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use sha2::{Digest, Sha256};
use trust_ir::constant::Constant;
use trust_ir::inst::{CastOp, Inst};
use trust_ir::ty::Ty;

use deep::{Agg, Tables};
use ops::{binop, cast, cc, fcmp, icmp, ovop, unop};

mod byte_sites;

fn main() {
    let mut raw_args: Vec<String> = std::env::args().collect();
    // This diagnostic reads the unchanged module. It must precede every
    // legacy flag, merge, canonicalization, and nominal-ID interning path.
    if raw_args.iter().any(|arg| arg == "--byte-sites") {
        match byte_sites::run(&raw_args[1..]) {
            Ok(report) => println!("{report}"),
            Err(error) => {
                eprintln!("byte-sites: {error}");
                std::process::exit(2);
            }
        }
        return;
    }
    // `--usize-bits <N>`: the ONE target fact this projector will resolve, and
    // only because it was stated on the command line. `usize` is
    // target-dependent; without this flag a body containing one is REFUSED
    // (see `Projector::ty`), and with it the resolution is RECORDED in the
    // provenance JSON so the chain's tag table can pin it as a target fact
    // rather than inherit it silently.
    let mut usize_bits: Option<u32> = None;
    if let Some(i) = raw_args.iter().position(|a| a == "--usize-bits") {
        let v = raw_args
            .get(i + 1)
            .unwrap_or_else(|| panic!("--usize-bits takes a value"));
        usize_bits = Some(v.parse::<u32>().expect("--usize-bits takes a bit width"));
        raw_args.drain(i..=i + 1);
    }
    // `--with <function-name>`, repeatable: an ADDITIONAL function projected
    // into the SAME core module, after the root, under ONE interning
    // namespace. It exists because a chain can be more than one body — the
    // caller/callee pair of `has_loose_bvars` is one module with two functions
    // — and a module whose second function was written by hand would leave
    // exactly the transcription hole this projector exists to close. Without
    // the flag the projection is the one-function module every earlier chain
    // committed, byte for byte.
    // `--merge <bin>`, repeatable: an artifact whose functions join the
    // `--with` pool. It exists because the Phase-B module's five bodies live in
    // TWO artifacts — the crate module's own `.bin` and the callee sidecar's
    // bundle — and a projector that could read only one would have to be fed a
    // module somebody merged by hand, which is the transcription hole this
    // producer exists to close.
    //
    // Each merged artifact's FUNCTION IDS ARE RELOCATED above every id the
    // module already carries, because a function id is an index into its own
    // module and the same number means different functions in two artifacts.
    // Everything else is left alone deliberately, and that is measured rather
    // than assumed: this projector never reads `module.enums` or
    // `module.structs` except through the table of the artifact that named the
    // id (`artifact_of`), and it reads `module.globals` / `module.types` only
    // for a global's bytes and element type, which a merged artifact may not
    // declare (`fold_in` refuses one that does).
    //
    // `--join <manifest.json>`: a callee sidecar's own manifest, which is what
    // says WHICH crate-module declaration each derived body is the body OF. It
    // belongs to the `--merge` it FOLLOWS on the command line, and its member
    // ids are relocated by THAT artifact's shift; a `--join` before every
    // `--merge` is refused. Without it a merged module holds both — the
    // bodyless declaration the caller calls, and the body sitting beside it,
    // unreferenced — and the module is still stuck at the call. Measured:
    // without this flag the five-body projection defines functions
    // {0, 1, 4, 5, 6} and calls {0, 1, 2, 3, 5}, so `call 2` and `call 3` name
    // declarations the module does not define.
    // `--tls-cells <manifest.json>` (crystal D11): the callee sidecar's manifest whose
    // `tls_cells` rows CERTIFY the thread-local statics the bodies address. A
    // `trust_rust.thread_local_addr` op is imaged (as the address of an INPUT cell) only for a
    // symbol a certified row names; without the flag every such op is refused, as before.
    // `--ptr-bitcast-identity` (crystal D12, decision memo §18): image `bitcast ptr -> ptr` as
    // `copy (ptr)`, the identity. Opt-in, so a committed chain re-projects byte-identical until it
    // is deliberately re-minted under D12 (`ir_itc` carries four such bitcasts).
    let ptr_bitcast_identity =
        if let Some(i) = raw_args.iter().position(|a| a == "--ptr-bitcast-identity") {
            raw_args.drain(i..=i);
            true
        } else {
            false
        };
    let mut tls_manifests: Vec<String> = Vec::new();
    while let Some(i) = raw_args.iter().position(|a| a == "--tls-cells") {
        let v = raw_args
            .get(i + 1)
            .unwrap_or_else(|| panic!("--tls-cells takes a path to a sidecar manifest"))
            .clone();
        tls_manifests.push(v);
        raw_args.drain(i..=i + 1);
    }
    let merge = take_merges(&mut raw_args);
    let mut with: Vec<String> = Vec::new();
    while let Some(i) = raw_args.iter().position(|a| a == "--with") {
        let v = raw_args
            .get(i + 1)
            .unwrap_or_else(|| panic!("--with takes a function name"))
            .clone();
        with.push(v);
        raw_args.drain(i..=i + 1);
    }
    // `--layouts`: print every enum's producer-provided layout descriptor and
    // exit. A measurement mode, not a projection: the encodings row Phase B
    // needs (`IREnc.nicheptr`) must be DERIVED from these descriptors, so the
    // first question is always whether the artifact carries one.
    if let Some(i) = raw_args.iter().position(|a| a == "--layouts") {
        raw_args.drain(i..=i);
        for path in raw_args.iter().skip(1) {
            let bytes = std::fs::read(path).unwrap_or_else(|e| panic!("read {path}: {e}"));
            let m = trust_ir::binary::deserialize_module(&bytes).expect("deserialize");
            println!("### {path}");
            for e in &m.enums {
                println!(
                    "  enum.{} {:<52} layout={:?}",
                    e.id.0,
                    e.name.chars().take(52).collect::<String>(),
                    e.layout
                );
            }
        }
        return;
    }
    let args = raw_args;
    if args.len() < 4 {
        eprintln!(
            "usage: a2project <crate.trust-ir.bin> <function-name> <out-dir> [slug] \
             [--with <function-name>]... \
             [--merge <other.bin> [--join <manifest.json>]...]... \
             [--tls-cells <manifest.json>]... [--usize-bits <N>] \
             [--ptr-bitcast-identity]"
        );
        std::process::exit(2);
    }
    let bin_path = &args[1];
    let fname = &args[2];
    let out_dir = &args[3];
    let slug = args
        .get(4)
        .cloned()
        .unwrap_or_else(|| fname.replace("::", "_"));

    let bytes = std::fs::read(bin_path).expect("read .bin");
    let mut h = Sha256::new();
    h.update(&bytes);
    let bin_sha = hex(&h.finalize());

    let raw = trust_ir::binary::deserialize_module(&bytes).expect("deserialize");
    // Trust's OWN published canonical form: dense SSA renumbering (block
    // params in block-id order, then instruction results in program order).
    // The emitted `.txt` this repo commits is exactly this rendering, so
    // reader A and reader B are normalized by the SAME rule -- and that rule
    // is the producer's, not one invented here. It also erases the builder's
    // arena layout, which `format.rs` states is not a logical property.
    let mut module = trust_ir::format::canonicalize(&raw);
    let mut merged_shas: Vec<(String, String)> = Vec::new();
    let mut inputs = Vec::with_capacity(merge.len());
    for m in &merge {
        let path = &m.path;
        let bytes = std::fs::read(path).unwrap_or_else(|e| panic!("read --merge {path}: {e}"));
        let mut h = Sha256::new();
        h.update(&bytes);
        merged_shas.push((path.clone(), hex(&h.finalize())));
        let other = trust_ir::format::canonicalize(
            &trust_ir::binary::deserialize_module(&bytes).expect("deserialize --merge"),
        );
        let joins = m
            .joins
            .iter()
            .map(|jpath| {
                let text = std::fs::read_to_string(jpath)
                    .unwrap_or_else(|e| panic!("read --join {jpath}: {e}"));
                (jpath.clone(), text)
            })
            .collect();
        inputs.push(MergeInput {
            path: path.clone(),
            module: other,
            joins,
        });
    }
    let (merged, prov_join) = merge_all(&mut module, inputs);
    let module = module;
    let (idx, func) = module
        .functions
        .iter()
        .enumerate()
        .find(|(_, f)| f.name == *fname)
        .unwrap_or_else(|| panic!("function {fname} not in {bin_path}"));
    let dup = module.functions.iter().filter(|f| f.name == *fname).count();
    assert_eq!(dup, 1, "function name is not unique in the artifact: {dup}");

    // Callee ids resolve to NAMES here and nowhere else: the artifact carries
    // the function table, the emitted TEXT does not. That is why the tag
    // table's `funcs` lane records the name reader A read and reader B cannot.
    let names: BTreeMap<u32, String> = module
        .functions
        .iter()
        .map(|f| (f.id.0, f.name.clone()))
        .collect();

    // The chain's bodies, ROOT FIRST. The order is load-bearing: it is the
    // order the functions appear in the minted `IRModule`, and `ir_func_find`
    // walks that list, so it is a fact about the module and not a formatting
    // choice.
    let mut chain: Vec<&trust_ir::Function> = vec![func];
    for name in &with {
        let f = module
            .functions
            .iter()
            .find(|f| f.name == *name)
            .unwrap_or_else(|| panic!("function {name} not in {bin_path}"));
        let dups = module.functions.iter().filter(|g| g.name == *name).count();
        assert_eq!(
            dups, 1,
            "function name is not unique in the artifact: {dups}"
        );
        chain.push(f);
    }

    let mut tls_certified: BTreeMap<String, String> = BTreeMap::new();
    for path in &tls_manifests {
        let text = std::fs::read_to_string(path)
            .unwrap_or_else(|e| panic!("read --tls-cells {path}: {e}"));
        for (symbol, static_path) in
            certified_tls_cells(&text).unwrap_or_else(|e| panic!("--tls-cells {path}: {e}"))
        {
            tls_certified.insert(symbol, static_path);
        }
    }
    let (text, mut p) = project_merged_certified(
        &module,
        &merged,
        &chain,
        usize_bits,
        tls_certified,
        ptr_bitcast_identity,
    )
    .unwrap_or_else(|e| panic!("projection refused: {e}"));
    let digest = core_digest(&text);
    // The `usize` / `isize` sites the BODIES resolved, counted before the
    // encodings derivation below interns payload types: the tag table pins
    // these against the emitted text's sites.
    let (usize_seen, isize_seen) = (p.usize_seen, p.isize_seen);

    // ── THE ENCODINGS ROWS, DERIVED ────────────────────────────────────────
    //
    // `IREnc.nicheptr K none some T` says an aggregate's byte image is a
    // niche-encoded two-variant enum over a pointer payload: the ZERO word is
    // the `none` variant, any other word is `some` carrying a payload of type
    // T. Its own rule is that a hand-typed row is never a pin, so every row
    // here comes from the artifact's `EnumLayoutDescriptor` and each clause is
    // REFUSED rather than approximated -- and every row that survives its
    // clauses is then RUN against trust-ir's reference interpreter on concrete
    // words (`reference_gate`), and refused when the two decodes differ.
    //
    // An enum with no descriptor contributes NO row: it keeps trust-ir's
    // canonical tagged-union layout, which is what every chain before this one
    // was minted under. A descriptor that is neither a row's shape nor that
    // canonical layout is REFUSED and recorded.
    //
    // Derived BEFORE the provenance is written, so `crate_enum_ids_seen` lists
    // every enum the module names -- a payload the derivation interned
    // included -- as `crate_struct_ids_seen` always did.
    let (encs, enc_refusals) = derive_encodings(&module, &merged, &mut p)
        .unwrap_or_else(|e| panic!("projection refused: {e}"));

    std::fs::create_dir_all(out_dir).expect("mkdir");
    std::fs::write(format!("{out_dir}/{slug}.core.txt"), &text).expect("write core");

    let mut prov = String::new();
    let _ = writeln!(prov, "{{");
    let _ = writeln!(
        prov,
        " \"reader\": \"A (trust-ir binary -> core), a2project\","
    );
    let _ = writeln!(prov, " \"dump\": {:?},", bin_path);
    let _ = writeln!(prov, " \"dump_sha256\": \"{bin_sha}\",");
    let _ = writeln!(prov, " \"module_name\": {:?},", module.name);
    if !merged_shas.is_empty() {
        let rows: Vec<String> = merged_shas
            .iter()
            .map(|(p, h)| format!("{{\"path\": {p:?}, \"sha256\": {h:?}}}"))
            .collect();
        let _ = writeln!(prov, " \"merged_artifacts\": [{}],", rows.join(", "));
    }
    if !prov_join.is_empty() {
        let _ = writeln!(prov, " \"retargeted_calls\": [");
        let _ = writeln!(prov, "{}", prov_join.join(",\n"));
        let _ = writeln!(prov, " ],");
    }
    let _ = writeln!(prov, " \"function_name\": {:?},", func.name);
    let _ = writeln!(prov, " \"artifact_func_index\": {idx},");
    let _ = writeln!(prov, " \"artifact_func_id\": {},", func.id.0);
    let _ = writeln!(prov, " \"artifact_functy_id\": {},", func.ty.0);
    // The three header facts reader B started COMPARING on 2026-08-20. Recorded
    // here so they stop being single-witness: until this runs, the linkage, the
    // calling convention and the producer token are pinned from reader B's
    // reading of the emitted TEXT alone, which is the mirror image of the
    // `switch-exhaustive-flag` slot standing on reader A alone.
    //
    // All three are printed by `trust_ir::display`'s `impl Display for
    // Function`, each suppressed when it holds its default — which is exactly
    // why `data/crystal_mint_blind_slots.json` was wrong to call them
    // unwitnessable, and exactly why they are spelled out unconditionally here.
    let _ = writeln!(prov, " \"artifact_linkage\": \"{}\",", func.linkage);
    let _ = writeln!(
        prov,
        " \"artifact_calling_conv\": \"{}\",",
        func.calling_conv
    );
    let producer = func
        .producer
        .as_ref()
        .map(ToString::to_string)
        .map(|value| json_string(&value))
        .unwrap_or_else(|| "null".to_owned());
    let _ = writeln!(prov, " \"artifact_producer\": {producer},");
    if let Some(bits) = p.usize_bits {
        let _ = writeln!(prov, " \"usize_bits\": {bits},");
        let _ = writeln!(prov, " \"usize_sites_resolved\": {usize_seen},");
        let _ = writeln!(prov, " \"isize_sites_resolved\": {isize_seen},");
    }
    let _ = writeln!(prov, " \"core_digest\": \"{digest}\",");
    if !with.is_empty() {
        // Recorded only for a MULTI-BODY chain, so every earlier chain's
        // committed provenance file stays byte-identical. One row per body, in
        // module order, each carrying the canonical index the shared namespace
        // gave it — which is the fact a text reader cannot see.
        let _ = writeln!(prov, " \"chain_functions\": [");
        for (i, f) in chain.iter().enumerate() {
            let canonical = p.funcs.get(&f.id.0).copied().unwrap_or(u32::MAX);
            let _ = writeln!(
                prov,
                "  {{ \"module_index\": {i}, \"canonical\": {canonical}, \"name\": {}, \
                 \"artifact_func_id\": {}, \"artifact_functy_id\": {}, \"linkage\": \"{}\", \
                 \"calling_conv\": \"{}\" }}{}",
                json_string(&f.name),
                f.id.0,
                f.ty.0,
                f.linkage,
                f.calling_conv,
                if i + 1 == chain.len() { "" } else { "," }
            );
        }
        let _ = writeln!(prov, " ],");
    }
    // Crystal D10 (decision memo §15): a chain that imaged a native atomic under the SEQ premise
    // says so, and how many; a chain that did not prints nothing new, so every earlier
    // provenance file is byte-identical.
    if p.seq_atomic_images > 0 {
        let _ = writeln!(
            prov,
            " \"seq_atomic_images\": {}, \"seq_premise\": {},",
            p.seq_atomic_images,
            json_string(SEQ_PREMISE)
        );
    }
    // Crystal D11 (decision memo §17): a chain that imaged a thread-local address under the TLS
    // premise says so, which cells, and the premise; a chain that did not prints nothing new.
    if p.tls_input_images > 0 {
        let cells: Vec<String> = p
            .tls_cells
            .iter()
            .map(|(k, sym)| {
                format!(
                    "{{\"canonical\": {k}, \"symbol\": {}, \"static\": {}}}",
                    json_string(sym),
                    json_string(p.tls_certified.get(sym).map_or("", String::as_str))
                )
            })
            .collect();
        let _ = writeln!(
            prov,
            " \"tls_input_images\": {}, \"tls_input_cells\": [{}], \"tls_premise\": {},",
            p.tls_input_images,
            cells.join(", "),
            json_string(TLS_PREMISE)
        );
    }
    // Crystal (decision memo §18): a chain that imaged a UB halt, a `bitcast ptr -> ptr` or a
    // negative integer constant says so and how many; a chain that did not prints nothing new,
    // so every earlier provenance file is byte-identical.
    if p.ub_halt_images > 0 {
        let _ = writeln!(prov, " \"ub_halt_images\": {},", p.ub_halt_images);
    }
    if p.ptr_bitcast_identities > 0 {
        let _ = writeln!(
            prov,
            " \"ptr_bitcast_identities\": {},",
            p.ptr_bitcast_identities
        );
    }
    if p.vtable_reads > 0 {
        let _ = writeln!(
            prov,
            " \"vtable_reads\": {}, \"vtable_image\": {},",
            p.vtable_reads,
            json_string(VTABLE_IMAGE)
        );
    }
    if p.negative_int_images > 0 {
        let _ = writeln!(prov, " \"negative_int_images\": {},", p.negative_int_images);
    }
    if !p.omitted_declarations.is_empty() {
        let names: Vec<String> = p
            .omitted_declarations
            .iter()
            .map(|n| json_string(n))
            .collect();
        let _ = writeln!(prov, " \"omitted_declarations\": [{}],", names.join(", "));
    }
    let _ = writeln!(prov, " \"crate_enum_ids_seen\": {:?},", p.enum_order);
    let _ = writeln!(prov, " \"encodings_derived\": [{}],", encs.join(", "));
    let _ = writeln!(prov, " \"encodings_refused\": {enc_refusals:?},");
    let _ = writeln!(prov, " \"crate_struct_ids_seen\": {:?},", p.struct_order);
    let _ = writeln!(prov, " \"crate_func_ids_seen\": {:?},", p.func_order);
    let seen_names: Vec<&str> = p
        .func_order
        .iter()
        .map(|id| {
            names
                .get(id)
                .map_or("<not in the artifact function table>", String::as_str)
        })
        .collect();
    let _ = writeln!(prov, " \"crate_func_names_seen\": {:?},", seen_names);
    if !p.global_order.is_empty() {
        // Recorded only for a chain that TOUCHES a global (2026-09-09, the
        // `ir_lzc` deref chain is the first), so every earlier chain's
        // committed provenance file stays byte-identical — the same rule
        // `chain_functions` above follows. `IRGlobal` has no type slot and
        // no linkage slot, so the array type (`[ty.0 x 34]`, resolved here
        // through the module's type table to `[u8 x 34]`) and the linkage
        // are ERASED from the core and recorded here for the tag table to
        // pin and `project` to compare. Mutability, TLS and alignment are
        // not erased: `global_init`'s walk REFUSES a global carrying any of
        // them, and `global_flags_refused` says so in the artifact rather
        // than leaving the reader to infer it from the code.
        let _ = writeln!(prov, " \"crate_global_ids_seen\": {:?},", p.global_order);
        let _ = writeln!(
            prov,
            " \"crate_global_names_seen\": {:?},",
            p.global_names_seen
        );
        let _ = writeln!(prov, " \"global_tys_erased\": {:?},", p.global_tys_erased);
        let _ = writeln!(
            prov,
            " \"global_tys_resolved\": {:?},",
            p.global_tys_resolved
        );
        let _ = writeln!(
            prov,
            " \"global_linkages_erased\": {:?},",
            p.global_linkages_erased
        );
        let _ = writeln!(
            prov,
            " \"global_flags_refused\": [\"mutable\", \"tls\", \"align\"],"
        );
        let resolved: Vec<String> = p
            .type_table_resolved
            .iter()
            .map(|(id, ty)| format!("ty.{id}={ty}"))
            .collect();
        let _ = writeln!(prov, " \"type_table_resolved\": {:?},", resolved);
    }
    let _ = writeln!(prov, " \"aligns_erased\": {:?},", p.aligns);
    let _ = writeln!(prov, " \"param_tys_erased\": {:?},", p.param_tys);
    let _ = writeln!(prov, " \"block_param_tys_erased\": {:?}", p.block_param_tys);
    let _ = writeln!(prov, "}}");
    std::fs::write(format!("{out_dir}/{slug}.core.prov.json"), prov).expect("write prov");

    println!(
        "{slug}\t{digest}\tfunc_index={idx}\tfunc_id={}\tenums={:?}",
        func.id.0, p.enum_order
    );
}

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

/// Quote one UTF-8 string as JSON without adding a serialization dependency to
/// this sealed standalone projector. Rust's `Option<String>:?` is not JSON
/// (`Some("trust")` caused the current provenance bug), and `String`'s debug
/// escaping is not a promised JSON encoding either.
fn json_string(value: &str) -> String {
    let mut out = String::with_capacity(value.len() + 2);
    out.push('"');
    for ch in value.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\u{08}' => out.push_str("\\b"),
            '\u{0c}' => out.push_str("\\f"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            ch if ch <= '\u{1f}' => {
                use std::fmt::Write as _;
                let _ = write!(out, "\\u{:04x}", u32::from(ch));
            }
            ch => out.push(ch),
        }
    }
    out.push('"');
    out
}

/// Crystal D11: the (symbol, static path) of every `tls_cells` row a callee-sidecar manifest
/// renders with `"certified": true`. The manifest renders one row per line inside the
/// `"tls_cells": [` array (trust `callee_sidecar.rs`, `ManifestV1::render`); a manifest with no
/// such array is an error, so a projection asked to trust a certificate cannot pass on an
/// artifact that never carried one.
fn certified_tls_cells(text: &str) -> Result<Vec<(String, String)>, String> {
    let mut lines = text.lines();
    if !lines.any(|l| l.trim() == "\"tls_cells\": [") {
        return Err(
            "the manifest carries no `tls_cells` array (the producer ran without the \
                    `tls-cells` lane)"
                .into(),
        );
    }
    let mut out = Vec::new();
    for line in lines {
        let row = line.trim();
        if row == "]," || row == "]" {
            return Ok(out);
        }
        let symbol = json_field_string(row, "symbol")
            .ok_or_else(|| format!("row without a symbol: {row}"))?;
        let static_path = json_field_string(row, "static")
            .ok_or_else(|| format!("row without a static: {row}"))?;
        let flag = |key: &str| -> Result<bool, String> {
            match (
                row.contains(&format!("\"{key}\": true,")),
                row.contains(&format!("\"{key}\": false,")),
            ) {
                (true, false) => Ok(true),
                (false, true) => Ok(false),
                _ => Err(format!("row with no single boolean `{key}`: {row}")),
            }
        };
        let certified = flag("certified")?;
        // Re-derived, never trusted: `certified` must be the conjunction of the three facts.
        let facts = flag("unique_symbol")? && flag("pointer_free")? && flag("definitely_not_sync")?;
        if certified != facts {
            return Err(format!(
                "row whose `certified` is not the conjunction of its facts: {row}"
            ));
        }
        if certified {
            out.push((symbol, static_path));
        }
    }
    Err("the `tls_cells` array is not closed".into())
}

/// The JSON string value of `"key": "..."` in one rendered row, unescaped (`\"`, `\\`, `\/`,
/// `\n`, `\r`, `\t`, `\b`, `\f`, `\uXXXX` -- everything `json_str` in the producer emits).
fn json_field_string(row: &str, key: &str) -> Option<String> {
    let at = row.find(&format!("\"{key}\": \""))? + key.len() + 5;
    let mut out = String::new();
    let mut chars = row[at..].chars();
    loop {
        match chars.next()? {
            '"' => return Some(out),
            '\\' => match chars.next()? {
                '"' => out.push('"'),
                '\\' => out.push('\\'),
                '/' => out.push('/'),
                'n' => out.push('\n'),
                'r' => out.push('\r'),
                't' => out.push('\t'),
                'b' => out.push('\u{8}'),
                'f' => out.push('\u{c}'),
                'u' => {
                    let hex: String = chars.by_ref().take(4).collect();
                    out.push(char::from_u32(u32::from_str_radix(&hex, 16).ok()?)?);
                }
                _ => return None,
            },
            c => out.push(c),
        }
    }
}

/// The placeholder a TLS input cell's `globaladdr` carries until `project_chain` fixes its id.
/// It cannot occur in a core module otherwise: no id, constant or name the projector prints
/// contains `@@`.
fn tls_placeholder(j: usize) -> String {
    format!("@@TLS{j}@@")
}

fn core_digest(text: &str) -> String {
    let mut h = Sha256::new();
    h.update(b"clean.ir_mint.core.v1\0");
    h.update(text.as_bytes());
    hex(&h.finalize())
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::deep::Agg;
    use super::reference::{self, Img};
    use super::{
        artifact_of, call_target, derive_encodings, derive_rows, fold_in, json_string, merge_all,
        project_merged, take_merges, MergeInput, Projector, Row, Shape,
    };
    use trust_ir::constant::Constant;
    use trust_ir::inst::Inst;
    use trust_ir::ty::{EnumDef, FieldDef, StructDef, StructRepr, Ty};
    use trust_ir::value::{BlockId, EnumId, FuncId, FuncTyId, StructId, ValueId};

    /// THE SECOND DIFFERENTIAL (verifier r8, 2026-09-25): 27 shapes the
    /// generated one never produces -- packed and transparent wrappers,
    /// signed, pointer-width, 128-bit, bool and float fields, references and
    /// raw pointers, a struct wider than its field, a struct trust-ir cannot
    /// lay out, an i64 niche lane, wasm32 -- each projected and derived, and
    /// every row the projector MINTS decoded by the Clean view and by trust-ir's
    /// interpreter at about 2,500 words each (the gate's own, 1,200 LCG words,
    /// 0..1024, 5120..5400 and every power of two and its predecessor up to
    /// 2^128), not only the gate's. The verifier wrote it to show that the
    /// gate's finite probe set was the only thing refusing a narrow field in a
    /// wide struct; the fill clause refuses those by shape now, and the tally
    /// at the end keeps the test from passing vacuously.
    #[test]
    fn every_minted_row_decodes_as_the_reference_on_shapes_the_generator_skips() {
        let mut oracle_trace = String::new();
        let mut seed: u128 = 0x2545_f491_4f6c_dd1d;
        let mut extra: Vec<u128> = Vec::new();
        for _ in 0..600 {
            seed = seed
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            extra.push(seed >> 7);
            extra.push((seed >> 64) & 0xffff);
        }
        for w in 0..1024u128 {
            extra.push(w);
        }
        for w in 5120..5400u128 {
            extra.push(w);
        }
        for sh in 0..128u32 {
            extra.push(1u128 << sh);
            extra.push((1u128 << sh).wrapping_sub(1));
        }
        let lane64 = trust_ir::ty::EnumTagRepr::U64;
        let mk = |id: u32,
                  fields: Vec<(Ty, Option<u64>)>,
                  size: Option<u64>,
                  align: Option<u64>,
                  repr: StructRepr| StructDef {
            id: StructId::new(id),
            name: format!("S{id}"),
            fields: fields
                .into_iter()
                .enumerate()
                .map(|(i, (ty, offset))| FieldDef {
                    name: format!("f{i}"),
                    ty,
                    offset,
                })
                .collect(),
            size,
            align,
            repr,
            origin: None,
        };
        let zst = || mk(30, vec![], Some(0), Some(1), StructRepr::Rust);
        let zst16 = || mk(32, vec![], Some(0), Some(16), StructRepr::Rust);
        let niche_opt = |payload: Ty, lane: trust_ir::ty::EnumTagRepr, size: u64| {
            let mut d = enum_with(
                1,
                trust_ir::ty::EnumTagEncoding::Niche {
                    untagged_variant: 1,
                    niche_variants_start: 0,
                    niche_variants_end: 0,
                    niche_start: 0,
                    niche_offset: 0,
                    niche_ty: lane,
                },
                vec![vec![], vec![payload]],
                size,
                vec![vec![], vec![0]],
            );
            d.layout.as_mut().expect("layout").align = size.min(8);
            d
        };
        let t8 = Some(target(8));
        let w32 = Some(trust_ir::TargetInfo {
            triple: "wasm32-unknown-unknown".into(),
            ..target(4)
        });
        type C = (
            &'static str,
            Ty,
            Vec<StructDef>,
            Vec<EnumDef>,
            u32,
            Option<trust_ir::TargetInfo>,
        );
        let cases: Vec<C> = vec![
            (
                "W{ptr} size16 align16",
                Ty::Struct(StructId::new(10)),
                vec![mk(
                    10,
                    vec![(Ty::Ptr, Some(0))],
                    Some(16),
                    Some(16),
                    StructRepr::Rust,
                )],
                vec![],
                64,
                t8.clone(),
            ),
            (
                "W{ptr} size None offset None",
                Ty::Struct(StructId::new(10)),
                vec![mk(10, vec![(Ty::Ptr, None)], None, None, StructRepr::Rust)],
                vec![],
                64,
                t8.clone(),
            ),
            (
                "W{zst16@8, ptr@None} size 8",
                Ty::Struct(StructId::new(10)),
                vec![
                    mk(
                        10,
                        vec![(Ty::Struct(StructId::new(32)), Some(8)), (Ty::Ptr, None)],
                        Some(8),
                        Some(8),
                        StructRepr::Rust,
                    ),
                    zst16(),
                ],
                vec![],
                64,
                t8.clone(),
            ),
            (
                "W{ptr} packed(1)",
                Ty::Struct(StructId::new(10)),
                vec![mk(
                    10,
                    vec![(Ty::Ptr, Some(0))],
                    Some(8),
                    Some(1),
                    StructRepr::Packed(1),
                )],
                vec![],
                64,
                t8.clone(),
            ),
            (
                "W{ptr} transparent",
                Ty::Struct(StructId::new(10)),
                vec![
                    mk(
                        10,
                        vec![(Ty::Ptr, Some(0)), (Ty::Struct(StructId::new(30)), Some(0))],
                        Some(8),
                        Some(8),
                        StructRepr::Transparent,
                    ),
                    zst(),
                ],
                vec![],
                64,
                t8.clone(),
            ),
            (
                "W{i64}",
                Ty::Struct(StructId::new(10)),
                vec![mk(
                    10,
                    vec![(Ty::I64, Some(0))],
                    Some(8),
                    Some(8),
                    StructRepr::Rust,
                )],
                vec![],
                64,
                t8.clone(),
            ),
            (
                "W{isize}",
                Ty::Struct(StructId::new(10)),
                vec![mk(
                    10,
                    vec![(Ty::Isize, Some(0))],
                    Some(8),
                    Some(8),
                    StructRepr::Rust,
                )],
                vec![],
                64,
                t8.clone(),
            ),
            (
                "W{usize}",
                Ty::Struct(StructId::new(10)),
                vec![mk(
                    10,
                    vec![(Ty::Usize, Some(0))],
                    Some(8),
                    Some(8),
                    StructRepr::Rust,
                )],
                vec![],
                64,
                t8.clone(),
            ),
            (
                "W{u32} size 8",
                Ty::Struct(StructId::new(10)),
                vec![mk(
                    10,
                    vec![(Ty::U32, Some(0))],
                    Some(8),
                    Some(8),
                    StructRepr::Rust,
                )],
                vec![],
                64,
                t8.clone(),
            ),
            (
                "W{i8}",
                Ty::Struct(StructId::new(10)),
                vec![mk(
                    10,
                    vec![(Ty::I8, Some(0))],
                    Some(1),
                    Some(1),
                    StructRepr::Rust,
                )],
                vec![],
                64,
                t8.clone(),
            ),
            (
                "W{u16}",
                Ty::Struct(StructId::new(10)),
                vec![mk(
                    10,
                    vec![(Ty::U16, Some(0))],
                    Some(2),
                    Some(2),
                    StructRepr::Rust,
                )],
                vec![],
                64,
                t8.clone(),
            ),
            (
                "W{u128}",
                Ty::Struct(StructId::new(10)),
                vec![mk(
                    10,
                    vec![(Ty::U128, Some(0))],
                    Some(16),
                    Some(16),
                    StructRepr::Rust,
                )],
                vec![],
                64,
                t8.clone(),
            ),
            (
                "W{i128}",
                Ty::Struct(StructId::new(10)),
                vec![mk(
                    10,
                    vec![(Ty::I128, Some(0))],
                    Some(16),
                    Some(16),
                    StructRepr::Rust,
                )],
                vec![],
                64,
                t8.clone(),
            ),
            (
                "W{&u8}",
                Ty::Struct(StructId::new(10)),
                vec![mk(
                    10,
                    vec![(Ty::Ref(Box::new(Ty::U8)), Some(0))],
                    Some(8),
                    Some(8),
                    StructRepr::Rust,
                )],
                vec![],
                64,
                t8.clone(),
            ),
            (
                "W{&mut u64}",
                Ty::Struct(StructId::new(10)),
                vec![mk(
                    10,
                    vec![(Ty::RefMut(Box::new(Ty::U64)), Some(0))],
                    Some(8),
                    Some(8),
                    StructRepr::Rust,
                )],
                vec![],
                64,
                t8.clone(),
            ),
            (
                "W{*mut u8}",
                Ty::Struct(StructId::new(10)),
                vec![mk(
                    10,
                    vec![(Ty::PtrMut(Box::new(Ty::U8)), Some(0))],
                    Some(8),
                    Some(8),
                    StructRepr::Rust,
                )],
                vec![],
                64,
                t8.clone(),
            ),
            (
                "W{bool}",
                Ty::Struct(StructId::new(10)),
                vec![mk(
                    10,
                    vec![(Ty::Bool, Some(0))],
                    Some(1),
                    Some(1),
                    StructRepr::Rust,
                )],
                vec![],
                64,
                t8.clone(),
            ),
            (
                "W{f64}",
                Ty::Struct(StructId::new(10)),
                vec![mk(
                    10,
                    vec![(Ty::F64, Some(0))],
                    Some(8),
                    Some(8),
                    StructRepr::Rust,
                )],
                vec![],
                64,
                t8.clone(),
            ),
            (
                "wasm32 W{u64}",
                Ty::Struct(StructId::new(10)),
                vec![mk(
                    10,
                    vec![(Ty::U64, Some(0))],
                    Some(8),
                    Some(8),
                    StructRepr::Rust,
                )],
                vec![],
                32,
                w32.clone(),
            ),
            (
                "wasm32 W{usize}",
                Ty::Struct(StructId::new(10)),
                vec![mk(
                    10,
                    vec![(Ty::Usize, Some(0))],
                    Some(4),
                    Some(4),
                    StructRepr::Rust,
                )],
                vec![],
                32,
                w32.clone(),
            ),
            (
                "Option<&u8>",
                Ty::Enum(EnumId::new(1)),
                vec![],
                vec![niche_opt(Ty::Ref(Box::new(Ty::U8)), lane64, 8)],
                64,
                t8.clone(),
            ),
            (
                "Option<*mut u8> i64 lane",
                Ty::Enum(EnumId::new(1)),
                vec![],
                vec![niche_opt(
                    Ty::PtrMut(Box::new(Ty::U8)),
                    trust_ir::ty::EnumTagRepr::I64,
                    8,
                )],
                64,
                t8.clone(),
            ),
            (
                "Option<W{&u8}>",
                Ty::Enum(EnumId::new(1)),
                vec![mk(
                    10,
                    vec![(Ty::Ref(Box::new(Ty::U8)), Some(0))],
                    Some(8),
                    Some(8),
                    StructRepr::Rust,
                )],
                vec![niche_opt(Ty::Struct(StructId::new(10)), lane64, 8)],
                64,
                t8.clone(),
            ),
            (
                "Option<W{ptr} size None>",
                Ty::Enum(EnumId::new(1)),
                vec![mk(10, vec![(Ty::Ptr, None)], None, None, StructRepr::Rust)],
                vec![niche_opt(Ty::Struct(StructId::new(10)), lane64, 8)],
                64,
                t8.clone(),
            ),
            (
                "Option<W{ptr} packed>",
                Ty::Enum(EnumId::new(1)),
                vec![mk(
                    10,
                    vec![(Ty::Ptr, Some(0))],
                    Some(8),
                    Some(1),
                    StructRepr::Packed(1),
                )],
                vec![niche_opt(Ty::Struct(StructId::new(10)), lane64, 8)],
                64,
                t8.clone(),
            ),
            (
                "target-less Option<ptr>",
                Ty::Enum(EnumId::new(1)),
                vec![],
                vec![niche_opt(Ty::Ptr, lane64, 8)],
                64,
                None,
            ),
            (
                "wasm32 Option<&u8>",
                Ty::Enum(EnumId::new(1)),
                vec![],
                vec![niche_opt(
                    Ty::Ref(Box::new(Ty::U8)),
                    trust_ir::ty::EnumTagRepr::U32,
                    4,
                )],
                32,
                w32.clone(),
            ),
        ];
        let mut report = Vec::new();
        let mut mismatches = 0usize;
        let mut tally: BTreeMap<&str, (usize, usize)> = BTreeMap::new();
        for (name, root, structs, enums, bits, tgt) in cases {
            oracle_trace.push_str(&format!("case {name}\n"));
            let mut module = trust_ir::Module::new("primary");
            module.functions.push(function(
                0,
                "a",
                Some(vec![Inst::Undef { ty: root.clone() }]),
            ));
            module.structs = structs;
            module.enums = enums;
            module.target_info = tgt;
            let chain: Vec<&trust_ir::Function> = module.functions.iter().collect();
            let p = project_merged(&module, &[], &chain, Some(bits));
            let Ok((_, mut p)) = p else {
                report.push(format!("{name}: projection refused"));
                continue;
            };
            let (rows, refused) = match super::derive_rows(&module, &[], &mut p) {
                Ok(x) => x,
                Err(e) => {
                    oracle_trace.push_str(&format!("derive refused {e}\n"));
                    report.push(format!("{name}: derive refused {e}"));
                    continue;
                }
            };
            oracle_trace.push_str(&format!("refused {refused:?}\n"));
            tally.insert(name, (rows.len(), refused.len()));
            let mut line = format!("{name}: minted {} refused {}", rows.len(), refused.len());
            for r in &rows {
                match reference::reference_images(
                    &probe_of(&module.enums, &module.structs, module.target_info.as_ref()),
                    r.key().0,
                    r.raw,
                    &extra,
                ) {
                    Err(e) => {
                        oracle_trace.push_str(&format!("reference refused {e}\n"));
                        line.push_str(&format!(" [MINTED ROW REFERENCE ERR {e}]"));
                        mismatches += 1;
                    }
                    Ok(images) => {
                        oracle_trace.push_str(&format!(
                            "{} {}.{} {images:?}\n",
                            r.kind(),
                            r.key().0.tag(),
                            r.raw
                        ));
                        let bad: Vec<String> = images
                            .iter()
                            .filter_map(|(w, want)| {
                                let got = reference::load_view(&rows, &r.image(), Img::Word(*w));
                                (!got.agrees(want))
                                    .then(|| format!("{w:#x}: model {got} ref {want}"))
                            })
                            .take(3)
                            .collect();
                        if !bad.is_empty() {
                            mismatches += 1;
                            line.push_str(&format!(
                                " [MISMATCH {}.{} {:?}]",
                                r.key().0.tag(),
                                r.raw,
                                bad
                            ));
                        } else {
                            line.push_str(&format!(
                                " [{} {}.{} ok over {} words]",
                                r.kind(),
                                r.key().0.tag(),
                                r.raw,
                                images.len()
                            ));
                        }
                    }
                }
            }
            if rows.is_empty() && !refused.is_empty() {
                line.push_str(&format!(
                    " first refusal: {}",
                    refused[0].chars().take(140).collect::<String>()
                ));
            }
            report.push(line);
        }
        assert_eq!(
            mismatches,
            0,
            "a minted row disagrees with the reference:\n{}",
            report.join("\n")
        );
        use sha2::Digest as _;
        let oracle_digest = format!("{:x}", sha2::Sha256::digest(oracle_trace.as_bytes()));
        eprintln!(
            "REFERENCE_ORACLE_TRACE sha256={oracle_digest} bytes={}",
            oracle_trace.len()
        );
        assert_eq!(
            oracle_digest, "f3dafbe5ae5c4f387a4d50adf35fd79872e0be8810564bbfe56f960fbefef139",
            "parameterizing the probe changed a word/image or refusal: {oracle_trace}"
        );
        let report = report.join("\n");
        for (name, minted) in [
            ("W{ptr} packed(1)", 1),
            ("W{ptr} transparent", 1),
            ("W{u128}", 1),
            ("wasm32 W{u64}", 1),
            ("Option<W{&u8}>", 2),
            ("Option<*mut u8> i64 lane", 1),
            ("target-less Option<ptr>", 1),
            ("wasm32 Option<&u8>", 1),
            ("W{u32} size 8", 0),
            ("W{ptr} size16 align16", 0),
            ("W{bool}", 0),
            ("Option<W{ptr} size None>", 0),
        ] {
            assert_eq!(
                tally.get(name).map(|t| t.0),
                Some(minted),
                "{name}:\n{report}"
            );
        }
        let rows: usize = tally.values().map(|t| t.0).sum();
        assert!(
            tally.len() == 27 && rows >= 20,
            "vacuity: {} shapes, {rows} rows minted:\n{report}",
            tally.len()
        );
    }

    #[test]
    fn producer_values_are_json_strings_not_rust_option_debug() {
        assert_eq!(json_string("trust"), r#""trust""#);
        assert_eq!(
            json_string("quoted \" producer\\line\n\u{0001}"),
            r#""quoted \" producer\\line\n\u0001""#
        );
    }

    /// A one-function artifact whose body is `const <value>; ret`.
    fn artifact_with_const(value: Constant) -> trust_ir::Module {
        let mut block = trust_ir::Block::new(BlockId::new(0));
        block.body.push(
            trust_ir::InstrNode::new(Inst::Const { ty: Ty::Ptr, value })
                .with_result(ValueId::new(0)),
        );
        block
            .body
            .push(trust_ir::InstrNode::new(Inst::Return { values: vec![] }));
        let mut f = trust_ir::Function::new(FuncId::new(0), "f", FuncTyId::new(0), BlockId::new(0));
        f.blocks.push(block);
        let mut m = trust_ir::Module::new("merged");
        m.functions.push(f);
        m
    }

    fn symbol_addr() -> Constant {
        Constant::SymbolAddr {
            symbol: "g".to_string(),
            addend: 0,
        }
    }

    /// `SymbolAddr` names its target by NAME against the merged module's symbol
    /// table, which trust-ir documents as possibly a FUNCTION; `fold_in`
    /// relocates `FuncId`s only, so the merge must refuse it rather than pass
    /// it through unrelocated.
    #[test]
    #[should_panic(expected = "may name a function")]
    fn fold_in_refuses_a_symbol_addr_constant() {
        fold_in(
            &mut trust_ir::Module::new("primary"),
            artifact_with_const(symbol_addr()),
            "sidecar.bin",
        );
    }

    /// The same refusal when the `SymbolAddr` sits inside an aggregate
    /// (the fat-pointer shape `[SymbolAddr, Int]` trust-ir admits).
    #[test]
    #[should_panic(expected = "may name a function")]
    fn fold_in_refuses_a_nested_symbol_addr_constant() {
        fold_in(
            &mut trust_ir::Module::new("primary"),
            artifact_with_const(Constant::Aggregate(vec![symbol_addr(), Constant::Int(3)])),
            "sidecar.bin",
        );
    }

    /// A chain root that CALLS a bodiless declaration (`call @func.1`, the `premise-decls`
    /// lowering of a foreign premise), with the declaration also named in the chain.
    fn module_calling_a_declaration() -> trust_ir::Module {
        let mut block = trust_ir::Block::new(BlockId::new(0));
        block.body.push(trust_ir::InstrNode::new(Inst::Call {
            callee: FuncId::new(1),
            args: vec![],
        }));
        block
            .body
            .push(trust_ir::InstrNode::new(Inst::Return { values: vec![] }));
        let mut root =
            trust_ir::Function::new(FuncId::new(0), "root", FuncTyId::new(0), BlockId::new(0));
        root.blocks.push(block);
        let decl = trust_ir::Function::declaration(
            FuncId::new(1),
            "alloc::alloc::{extern#0}::__rust_alloc",
            FuncTyId::new(1),
            trust_ir::FunctionSummary::new(),
        );
        let mut m = trust_ir::Module::new("sidecar");
        m.functions.push(root);
        m.functions.push(decl);
        m
    }

    /// Crystal D10: one body carrying every native atomic the SEQ image covers, over a pointer
    /// parameter `%0`: `%2 = atomicrmw add %0, %1`, `%3,%4 = cmpxchg %0, %1, %2`,
    /// `%5 = atomic_load %0`, `atomic_store %5 -> %0`, `fence`, `ret`.
    fn atomic_body(op: trust_ir::inst::AtomicRMWOp) -> trust_ir::Module {
        atomic_body_with(op, false)
    }

    /// [`atomic_body`], its `cmpxchg` WEAK when `weak` (trust-ir v48's flag).
    fn atomic_body_with(op: trust_ir::inst::AtomicRMWOp, weak: bool) -> trust_ir::Module {
        use trust_ir::inst::Ordering as O;
        let v = ValueId::new;
        let mut b = trust_ir::Block::new(BlockId::new(0));
        b.params = vec![(v(0), Ty::Ptr), (v(1), Ty::U64)];
        b.body.push(
            trust_ir::InstrNode::new(Inst::AtomicRMW {
                op,
                ty: Ty::U64,
                ptr: v(0),
                value: v(1),
                ordering: O::Relaxed,
            })
            .with_result(v(2)),
        );
        b.body.push(
            trust_ir::InstrNode::new(Inst::CmpXchg {
                ty: Ty::U64,
                ptr: v(0),
                expected: v(1),
                desired: v(2),
                success: O::SeqCst,
                failure: O::Acquire,
                weak,
            })
            .with_result(v(3))
            .with_result(v(4)),
        );
        b.body.push(
            trust_ir::InstrNode::new(Inst::AtomicLoad {
                ty: Ty::U64,
                ptr: v(0),
                ordering: O::Acquire,
            })
            .with_result(v(5)),
        );
        b.body.push(trust_ir::InstrNode::new(Inst::AtomicStore {
            ty: Ty::U64,
            ptr: v(0),
            value: v(5),
            ordering: O::Release,
        }));
        b.body.push(trust_ir::InstrNode::new(Inst::Fence {
            ordering: O::SeqCst,
        }));
        b.body.push(trust_ir::InstrNode::new(Inst::Return {
            values: vec![v(5)],
        }));
        let mut f =
            trust_ir::Function::new(FuncId::new(0), "atomics", FuncTyId::new(0), BlockId::new(0));
        f.blocks.push(b);
        let mut m = trust_ir::Module::new("sidecar");
        m.functions.push(f);
        m
    }

    /// Crystal D10: every native atomic is imaged as its SEQUENTIAL nodes, the intermediates bound
    /// ABOVE every id the body binds, the fence as nothing; and provenance records it.
    #[test]
    fn a_native_atomic_is_imaged_sequentially_under_seq() {
        let m = atomic_body(trust_ir::inst::AtomicRMWOp::Add);
        let mut p = Projector::default();
        let core = p
            .project_chain(&m, &[&m.functions[0]])
            .expect("the SEQ image projects");
        let want = [
            "(node (results 2) (load (uint 64) 0 false))",
            "(node (results 6) (binop add (uint 64) 2 1))",
            "(node (results) (store (uint 64) 0 6 false))",
            "(node (results 3) (load (uint 64) 0 false))",
            "(node (results 4) (icmp eq (uint 64) 3 1))",
            "(node (results 7) (select (uint 64) 4 2 3))",
            "(node (results) (store (uint 64) 0 7 false))",
            "(node (results 5) (load (uint 64) 0 false))",
            "(node (results) (store (uint 64) 0 5 false))",
            "(node (results) (ret (vals 5)))",
        ];
        let got: Vec<&str> = core
            .lines()
            .map(str::trim)
            .filter(|l| l.starts_with("(node "))
            .collect();
        assert_eq!(got, want, "{core}");
        assert_eq!(p.seq_atomic_images, 5, "rmw, cmpxchg, load, store, fence");
        let xchg = atomic_body(trust_ir::inst::AtomicRMWOp::Xchg);
        let core = Projector::default()
            .project_chain(&xchg, &[&xchg.functions[0]])
            .expect("xchg");
        assert!(
            core.contains("(node (results) (store (uint 64) 0 1 false))"),
            "{core}"
        );
    }

    /// Crystal D10: an `atomicrmw` whose op the image does not compute is refused BY NAME, and a
    /// body with no atomic projects exactly as before (no seq counter, nothing new).
    #[test]
    fn an_unimaged_rmw_op_is_refused_and_an_atomic_free_body_is_unchanged() {
        let m = atomic_body(trust_ir::inst::AtomicRMWOp::UMax);
        let err = Projector::default()
            .project_chain(&m, &[&m.functions[0]])
            .expect_err("umax has no SEQ image");
        assert!(err.contains("no SEQ image for `atomicrmw UMax`"), "{err}");
        let plain = module_calling_a_declaration();
        let mut p = Projector::default();
        p.project_chain(&plain, &[&plain.functions[0], &plain.functions[1]])
            .expect("plain");
        assert_eq!(p.seq_atomic_images, 0);
    }

    /// Crystal D10 at trust-ir v48: the pinned trust-ir now DECODES a weak compare-exchange (the
    /// D3 arm's `.bin` carries them), and the SEQ image refuses it BY NAME -- a weak CAS may fail
    /// spuriously, which the strong image deletes. The same body with the flag cleared images.
    #[test]
    fn a_weak_cmpxchg_is_refused_by_name_and_the_strong_one_images() {
        let m = atomic_body_with(trust_ir::inst::AtomicRMWOp::Add, true);
        let err = Projector::default()
            .project_chain(&m, &[&m.functions[0]])
            .expect_err("a weak cmpxchg has no SEQ image");
        assert!(err.contains("WEAK cmpxchg"), "{err}");
        // Control: the strong twin projects.
        let strong = atomic_body(trust_ir::inst::AtomicRMWOp::Add);
        Projector::default()
            .project_chain(&strong, &[&strong.functions[0]])
            .expect("the strong cmpxchg images");
    }

    /// A bodiless declaration in the chain is OMITTED, never projected and never a refusal:
    /// the module defines only the root, and the root's call still names the declaration's
    /// canonical id, so the machine is `stuck no_func` there.
    #[test]
    fn a_bodiless_declaration_in_the_chain_is_omitted() {
        let m = module_calling_a_declaration();
        let mut p = Projector::default();
        let core = p
            .project_chain(&m, &[&m.functions[0], &m.functions[1]])
            .expect("a declaration is omitted, not refused");
        assert_eq!(core.matches("(func ").count(), 1, "{core}");
        assert!(core.contains("(func 0\n"), "{core}");
        assert_eq!(
            p.funcs.get(&1),
            Some(&1),
            "the call interns the declaration's id"
        );
        assert!(
            !core.contains("(func 1\n"),
            "the declaration has no image: {core}"
        );
        assert_eq!(
            p.omitted_declarations,
            vec!["alloc::alloc::{extern#0}::__rust_alloc"]
        );
    }

    /// The ROOT must have a body: a declaration named as the chain root is refused by name.
    #[test]
    fn a_bodiless_root_is_refused() {
        let m = module_calling_a_declaration();
        let err = Projector::default()
            .project_chain(&m, &[&m.functions[1]])
            .expect_err("a declaration has no body to project");
        assert!(err.contains("bodiless declaration"), "{err}");
    }

    /// Crystal D1: `borrow_mut` projects exactly as `borrow` (one arm in trust-ir's reference
    /// interpreter), and `end_borrow` is still refused.
    #[test]
    fn borrow_mut_takes_the_borrow_image() {
        let mut p = Projector::default();
        let v = ValueId::new(3);
        assert_eq!(p.inst(&Inst::BorrowMut { ptr: v }).unwrap(), "(borrow 3)");
        assert_eq!(p.inst(&Inst::Borrow { ptr: v }).unwrap(), "(borrow 3)");
        let err = p.inst(&Inst::EndBorrow { borrow_ptr: v }).unwrap_err();
        assert!(err.contains("EndBorrow"), "{err}");
    }

    /// A body `%0 = trust_rust.thread_local_addr [symbol=S]; ret %0`, optionally after taking the
    /// address of an ordinary global first.
    fn tls_body(symbol: &str, with_global: bool) -> trust_ir::Module {
        let mut b = trust_ir::Block::new(BlockId::new(0));
        let mut m = trust_ir::Module::new("sidecar");
        if with_global {
            m.globals.push(trust_ir::Global {
                name: "g".into(),
                ty: Ty::Struct(trust_ir::value::StructId::new(0)),
                mutable: false,
                initializer: Some(Constant::Aggregate(vec![Constant::Int(1)])),
                linkage: trust_ir::Linkage::Internal,
                tls: None,
                align: None,
                section: None,
                visibility: trust_ir::Visibility::default(),
                retained: false,
            });
            b.body.push(
                trust_ir::InstrNode::new(Inst::GlobalAddr {
                    global: trust_ir::value::GlobalId::new(0),
                })
                .with_result(ValueId::new(1)),
            );
        }
        let op = trust_ir::dialect::trust_rust::thread_local_addr(symbol);
        b.body.push(
            trust_ir::InstrNode::new(Inst::DialectOp(Box::new(op))).with_result(ValueId::new(0)),
        );
        b.body.push(trust_ir::InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        }));
        let mut f =
            trust_ir::Function::new(FuncId::new(0), "tls", FuncTyId::new(0), BlockId::new(0));
        f.blocks.push(b);
        m.functions.push(f);
        m
    }

    /// Crystal D11: a CERTIFIED thread-local address images as the address of an INPUT cell that
    /// shares the canonical global namespace; an uncertified one, and every other dialect op, is
    /// refused; the input cell is printed in a form no core reader parses as an IRConst.
    #[test]
    fn a_certified_thread_local_address_images_as_an_input_cell() {
        let m = tls_body("k::BUDGET::VAL", false);
        let err = Projector::default()
            .project_chain(&m, &[&m.functions[0]])
            .expect_err("no certificate, no image");
        assert!(err.contains("no D11 image"), "{err}");
        let mut p = Projector::default();
        p.tls_certified
            .insert("k::BUDGET::VAL".into(), "k::BUDGET".into());
        let core = p.project_chain(&m, &[&m.functions[0]]).expect("certified");
        // With no artifact global the cell is id 1, never 0: EvalIR's `ptrtoint` of `ptr_ 0` is
        // the integer 0, which `try_with`'s null test would read as a NULL TLS address.
        assert!(core.contains("(node (results 0) (globaladdr 1))"), "{core}");
        assert!(
            core.contains("(globals (global 1 (tls_input \"k::BUDGET::VAL\")))"),
            "{core}"
        );
        assert!(
            !core.contains("@@"),
            "every placeholder is replaced: {core}"
        );
        assert_eq!(p.tls_input_images, 1);
        // After the artifact's globals: the global is 0, so the cell is 1.
        let m = tls_body("k::BUDGET::VAL", true);
        let mut p = Projector::default();
        p.tls_certified
            .insert("k::BUDGET::VAL".into(), "k::BUDGET".into());
        let core = p.project_chain(&m, &[&m.functions[0]]).expect("certified");
        assert!(core.contains("(node (results 1) (globaladdr 0))"), "{core}");
        assert!(core.contains("(node (results 0) (globaladdr 1))"), "{core}");
        assert!(
            core.contains(
                "(globals (global 0 (agg (int 1))) (global 1 (tls_input \"k::BUDGET::VAL\")))"
            ),
            "{core}"
        );
        // Any other dialect op is refused by name.
        let mut other = trust_ir::dialect::trust_rust::thread_local_addr("x");
        other.op = "not_an_op".into();
        let node =
            trust_ir::InstrNode::new(Inst::DialectOp(Box::new(other))).with_result(ValueId::new(0));
        let err = Projector::default()
            .tls_input_image(&node)
            .expect_err("unknown op");
        assert!(err.contains("no Clean IRInst image"), "{err}");
    }

    /// Crystal D11: the certificate reader takes exactly the `"certified": true` rows of a
    /// manifest's `tls_cells` array, unescapes their strings, and refuses a manifest without one.
    #[test]
    fn the_tls_certificate_is_read_from_the_manifest() {
        let manifest = "{\n  \"schema\": \"x\",\n  \"tls_cells\": [\n    \
            {\"symbol\": \"a::{closure#1}::VAL\", \"static\": \"a\\\"q\", \"def_path_hash\": \"h\", \
            \"ty\": \"T\", \"unique_symbol\": true, \"pointer_free\": true, \
            \"definitely_not_sync\": true, \"freeze\": false, \"needs_drop\": false, \
            \"certified\": true, \"refused\": []},\n    \
            {\"symbol\": \"b\", \"static\": \"b\", \"def_path_hash\": \"h\", \"ty\": \"T\", \
            \"unique_symbol\": true, \"pointer_free\": false, \"definitely_not_sync\": true, \
            \"freeze\": false, \"needs_drop\": false, \"certified\": false, \
            \"refused\": [\"the type is not pointer-free\"]}\n  ],\n  \"escaping\": []\n}\n";
        let got = super::certified_tls_cells(manifest).expect("reads");
        assert_eq!(
            got,
            vec![("a::{closure#1}::VAL".to_string(), "a\"q".to_string())]
        );
        let forged = manifest.replacen("\"pointer_free\": true", "\"pointer_free\": false", 1);
        let err = super::certified_tls_cells(&forged).expect_err("a forged certificate");
        assert!(err.contains("conjunction"), "{err}");
        assert!(super::certified_tls_cells("{\n  \"escaping\": []\n}\n").is_err());
    }

    /// Function `id` named `name`: a DECLARATION when `body` is `None`, else
    /// one block holding `body` then `ret`.
    fn function(id: u32, name: &str, body: Option<Vec<Inst>>) -> trust_ir::Function {
        let mut f =
            trust_ir::Function::new(FuncId::new(id), name, FuncTyId::new(0), BlockId::new(0));
        if let Some(insts) = body {
            let mut block = trust_ir::Block::new(BlockId::new(0));
            for inst in insts {
                block.body.push(trust_ir::InstrNode::new(inst));
            }
            block
                .body
                .push(trust_ir::InstrNode::new(Inst::Return { values: vec![] }));
            f.blocks.push(block);
        }
        f
    }

    fn call(callee: u32) -> Inst {
        Inst::Call {
            callee: FuncId::new(callee),
            args: vec![],
        }
    }

    /// A sidecar manifest root joining crate declaration `decl` to member
    /// `member`, in the one-root-per-line shape `joins_of` reads.
    fn manifest(decl: u32, member: u32) -> String {
        format!(
            "{{\"roots\": [\n  {{\"caller\": \"caller\", \"crate_decl_func_ids\": [{decl}], \
             \"sidecar_func_id\": {member}, \"outcome\": \"resolved\"}}\n]}}\n"
        )
    }

    /// A one-body artifact whose enum table holds ONE enum at raw id 1, named
    /// `enum_name` — so two artifacts disagree about what `enum.1` is.
    fn artifact(body: &str, enum_name: &str) -> trust_ir::Module {
        let mut m = trust_ir::Module::new(body);
        m.functions.push(function(0, body, Some(vec![])));
        m.enums
            .push(EnumDef::new(EnumId::new(1), enum_name, Vec::new()));
        m
    }

    /// Every call's callee, in program order, across `module`.
    fn callees(module: &trust_ir::Module) -> Vec<u32> {
        let mut module = module.clone();
        let mut out = Vec::new();
        for f in &mut module.functions {
            for b in &mut f.blocks {
                for n in &mut b.body {
                    out.extend(call_target(&mut n.inst).map(|callee| callee.0));
                }
            }
        }
        out
    }

    /// With TWO merges, an aggregate first named by a body from the SECOND
    /// artifact is defined by the second artifact's table. The lookup used to
    /// take the first artifact whose shift the id reached — the lowest — so it
    /// read `one::E` for a body from `two`.
    #[test]
    fn a_body_from_the_second_merge_reads_the_second_merges_tables() {
        let mut module = trust_ir::Module::new("primary");
        module.functions.push(function(0, "root", Some(vec![])));
        let (merged, _) = merge_all(
            &mut module,
            vec![
                MergeInput {
                    path: "one.bin".into(),
                    module: artifact("a1", "one::E"),
                    joins: vec![],
                },
                MergeInput {
                    path: "two.bin".into(),
                    module: artifact("a2", "two::E"),
                    joins: vec![],
                },
            ],
        );
        let id_of = |name: &str| {
            module
                .functions
                .iter()
                .find(|f| f.name == name)
                .map(|f| f.id.0)
                .expect("merged function")
        };
        let table = |func: u32| {
            artifact_of(&merged, func)
                .expect("in some artifact")
                .map(|m| m.enums[0].name.clone())
        };
        assert_eq!(
            table(id_of("root")),
            None,
            "a primary body reads the module's table"
        );
        assert_eq!(table(id_of("a1")).as_deref(), Some("one::E"));
        assert_eq!(table(id_of("a2")).as_deref(), Some("two::E"));
        let past = merged.last().expect("two merges").end;
        assert!(
            artifact_of(&merged, past).is_err(),
            "an id past every artifact's range is refused, not given the module's table"
        );
    }

    /// With TWO merges, each `--join` retargets into the artifact it follows.
    /// Every join used to run once per merge, relocated by THAT merge's shift,
    /// so the first iteration sent `decl2` into `one`'s range (`body1`) and
    /// the second found nothing left to move.
    #[test]
    fn each_join_retargets_into_the_artifact_it_follows() {
        let mut module = trust_ir::Module::new("primary");
        module
            .functions
            .push(function(0, "caller", Some(vec![call(1), call(2)])));
        module.functions.push(function(1, "decl1", None));
        module.functions.push(function(2, "decl2", None));
        let (merged, prov) = merge_all(
            &mut module,
            vec![
                MergeInput {
                    path: "one.bin".into(),
                    module: artifact("body1", "one::E"),
                    joins: vec![("one.manifest.json".into(), manifest(1, 0))],
                },
                MergeInput {
                    path: "two.bin".into(),
                    module: artifact("body2", "two::E"),
                    joins: vec![("two.manifest.json".into(), manifest(2, 0))],
                },
            ],
        );
        let id_of = |name: &str| {
            module
                .functions
                .iter()
                .find(|f| f.name == name)
                .map(|f| f.id.0)
                .expect("merged function")
        };
        assert_eq!(
            callees(&module),
            vec![id_of("body1"), id_of("body2")],
            "decl1 joins one's member and decl2 joins two's"
        );
        assert_eq!(merged.len(), 2);
        assert_eq!(
            prov.len(),
            2,
            "one provenance row per join, not one per join per merge"
        );
    }

    /// Project bodies `a1` and `a2`, each `undef` of `ty`, out of two merged
    /// artifacts whose tables `define` names `first` and `second`; with
    /// `in_primary`, `a1` is the primary module's own body and table instead.
    fn project_two(
        ty: &Ty,
        define: fn(&mut trust_ir::Module, &str),
        first: &str,
        second: &str,
        in_primary: bool,
    ) -> Result<String, String> {
        let body =
            |id: u32, name: &str| function(id, name, Some(vec![Inst::Undef { ty: ty.clone() }]));
        let make = |name: &str, def: &str| {
            let mut m = trust_ir::Module::new(name);
            m.functions.push(body(0, name));
            define(&mut m, def);
            m
        };
        let mut module = trust_ir::Module::new("primary");
        if in_primary {
            module.functions.push(body(0, "a1"));
            define(&mut module, first);
        } else {
            module.functions.push(function(0, "root", Some(vec![])));
        }
        let mut inputs = vec![MergeInput {
            path: "two.bin".into(),
            module: make("a2", second),
            joins: vec![],
        }];
        if !in_primary {
            inputs.insert(
                0,
                MergeInput {
                    path: "one.bin".into(),
                    module: make("a1", first),
                    joins: vec![],
                },
            );
        }
        let (merged, _) = merge_all(&mut module, inputs);
        let chain: Vec<&trust_ir::Function> = module
            .functions
            .iter()
            .filter(|f| f.name == "a1" || f.name == "a2")
            .collect();
        assert_eq!(chain.len(), 2);
        project_merged(&module, &merged, &chain, None).map(|(core, _)| core)
    }

    fn define_enum_1(m: &mut trust_ir::Module, name: &str) {
        m.enums.push(EnumDef::new(EnumId::new(1), name, Vec::new()));
    }

    fn define_struct_1(m: &mut trust_ir::Module, name: &str) {
        m.structs.push(struct_def(1, name, Vec::new(), 0));
    }

    /// Two merged artifacts both use raw `enum.1`, for DIFFERENT types. Raw
    /// aggregate ids are not relocated and intern into one namespace, so both
    /// bodies would print `(enum 0)` and the encodings row would read one
    /// artifact's definition for both: refused, not projected.
    #[test]
    fn one_raw_enum_id_two_artifacts_define_differently_is_refused() {
        let refused = project_two(
            &Ty::Enum(EnumId::new(1)),
            define_enum_1,
            "one::E",
            "two::E",
            false,
        )
        .expect_err("two definitions of enum.1 under one canonical id");
        assert!(
            refused.starts_with("enum.1 is named by bodies from merge@1 and merge@2"),
            "{refused}"
        );
    }

    /// The struct twin, and the primary module against a merge.
    #[test]
    fn one_raw_struct_id_primary_and_merge_define_differently_is_refused() {
        let refused = project_two(
            &Ty::Struct(StructId::new(1)),
            define_struct_1,
            "p::S",
            "m::S",
            true,
        )
        .expect_err("two definitions of struct.1 under one canonical id");
        assert!(
            refused.starts_with("struct.1 is named by bodies from merge@1 and module"),
            "{refused}"
        );
    }

    /// The same raw id with the SAME definition in both is one type.
    #[test]
    fn one_raw_aggregate_id_defined_identically_projects() {
        for (ty, define) in [
            (
                Ty::Enum(EnumId::new(1)),
                define_enum_1 as fn(&mut trust_ir::Module, &str),
            ),
            (Ty::Struct(StructId::new(1)), define_struct_1),
        ] {
            for in_primary in [false, true] {
                let core = project_two(&ty, define, "same::A", "same::A", in_primary)
                    .unwrap_or_else(|e| panic!("identical definitions: {e}"));
                assert!(core.contains(" 0)"), "{core}");
            }
        }
    }

    /// A struct named `name` of byte `size` holding `fields`, at raw id `id`.
    fn struct_def(id: u32, name: &str, fields: Vec<Ty>, size: u64) -> StructDef {
        StructDef {
            id: StructId::new(id),
            name: name.into(),
            fields: fields
                .into_iter()
                .enumerate()
                .map(|(i, ty)| FieldDef {
                    name: format!("f{i}"),
                    ty,
                    offset: Some(0),
                })
                .collect(),
            size: Some(size),
            align: Some(8),
            repr: StructRepr::default(),
            origin: None,
        }
    }

    /// A PAYLOAD type interned by the encodings derivation belongs to the
    /// artifact whose table it was read from. `a1` (from one.bin) names a
    /// one-field wrapper `struct.1` whose payload is one.bin's `struct.2`;
    /// `a2` (from two.bin) names two.bin's DIFFERENT `struct.2`. Attributing
    /// the payload to whichever body was projected last (`a2`) hid the clash,
    /// and the wrapper's row read `(struct 1)` -- two.bin's type -- as one.bin's
    /// payload.
    #[test]
    fn a_payload_type_is_interned_as_its_definers_and_a_clash_is_refused() {
        let mut module = trust_ir::Module::new("primary");
        module.functions.push(function(0, "root", Some(vec![])));
        let undef = |id: u32, name: &str, raw: u32| {
            function(
                id,
                name,
                Some(vec![Inst::Undef {
                    ty: Ty::Struct(StructId::new(raw)),
                }]),
            )
        };
        let mut one = trust_ir::Module::new("one");
        one.functions.push(undef(0, "a1", 1));
        one.structs.push(struct_def(
            1,
            "one::Wrapper",
            vec![Ty::Struct(StructId::new(2))],
            8,
        ));
        one.structs.push(struct_def(2, "one::P", vec![], 8));
        let mut two = trust_ir::Module::new("two");
        two.functions.push(undef(0, "a2", 2));
        two.structs.push(struct_def(2, "two::Q", vec![], 8));
        let (merged, _) = merge_all(
            &mut module,
            vec![
                MergeInput {
                    path: "one.bin".into(),
                    module: one,
                    joins: vec![],
                },
                MergeInput {
                    path: "two.bin".into(),
                    module: two,
                    joins: vec![],
                },
            ],
        );
        let chain: Vec<&trust_ir::Function> = module
            .functions
            .iter()
            .filter(|f| f.name == "a1" || f.name == "a2")
            .collect();
        let (_, mut p) = project_merged(&module, &merged, &chain, None)
            .expect("the bodies alone name each raw id from one artifact");
        let refused = derive_encodings(&module, &merged, &mut p)
            .expect_err("one.bin's payload struct.2 is not two.bin's struct.2");
        assert!(
            refused.starts_with("struct.2 is named by bodies from merge@1 and merge@2"),
            "{refused}"
        );
    }

    /// Two merged artifacts, each with ONE body `undef struct.1`, whose tables
    /// `one` and `two` fill in; projected together, then the encodings rows.
    fn project_nested(
        one: fn(&mut trust_ir::Module),
        two: fn(&mut trust_ir::Module),
    ) -> Result<(String, Vec<String>, Vec<String>), String> {
        let body = |name: &str| {
            function(
                0,
                name,
                Some(vec![Inst::Undef {
                    ty: Ty::Struct(StructId::new(1)),
                }]),
            )
        };
        let mut module = trust_ir::Module::new("primary");
        module.functions.push(function(0, "root", Some(vec![])));
        let mut a = trust_ir::Module::new("one");
        a.functions.push(body("a1"));
        one(&mut a);
        let mut b = trust_ir::Module::new("two");
        b.functions.push(body("a2"));
        two(&mut b);
        let (merged, _) = merge_all(
            &mut module,
            vec![
                MergeInput {
                    path: "one.bin".into(),
                    module: a,
                    joins: vec![],
                },
                MergeInput {
                    path: "two.bin".into(),
                    module: b,
                    joins: vec![],
                },
            ],
        );
        let chain: Vec<&trust_ir::Function> = module
            .functions
            .iter()
            .filter(|f| f.name == "a1" || f.name == "a2")
            .collect();
        let (core, mut p) = project_merged(&module, &merged, &chain, None)?;
        let (encs, refused) = derive_encodings(&module, &merged, &mut p)?;
        Ok((core, encs, refused))
    }

    /// `struct.1` = `W { f0: struct.2 }`, one field, printed identically in both.
    fn wrapper_over_struct_2(m: &mut trust_ir::Module) {
        m.structs
            .push(struct_def(1, "W", vec![Ty::Struct(StructId::new(2))], 8));
    }

    /// THE VERIFIER'S PROBE (r6, 2026-09-24). `struct.1` is `W`, one field of
    /// `Ty::Struct(2)`, in BOTH artifacts -- its printed definition is
    /// byte-identical -- while `struct.2` is `one::P` (a `u64`) in one.bin and
    /// `two::Q` (two `u8`s) in two.bin. The shallow comparison passed it: both
    /// bodies projected `(undef (struct 0))` and the single ptrwrap row gave
    /// payload `(struct 1)`, read from merge@1, for both. Compared deeply it is
    /// two types under one raw id, and refused.
    #[test]
    fn a_nested_raw_id_two_artifacts_define_differently_is_refused() {
        let refused = project_nested(
            |m| {
                wrapper_over_struct_2(m);
                m.structs.push(struct_def(2, "one::P", vec![Ty::U64], 8));
            },
            |m| {
                wrapper_over_struct_2(m);
                m.structs
                    .push(struct_def(2, "two::Q", vec![Ty::U8, Ty::U8], 2));
            },
        )
        .expect_err("struct.1 reaches one::P in one.bin and two::Q in two.bin");
        assert!(
            refused.starts_with("struct.1 is named by bodies from merge@1 and merge@2"),
            "{refused}"
        );
    }

    /// The control: the nested id defined identically in both is one type,
    /// all the way down, and projects -- with the wrapper row it always had.
    #[test]
    fn a_nested_raw_id_defined_identically_projects() {
        let same = |m: &mut trust_ir::Module| {
            wrapper_over_struct_2(m);
            m.structs.push(struct_def(2, "same::P", vec![Ty::U64], 8));
        };
        let (core, encs, _) = project_nested(same, same)
            .unwrap_or_else(|e| panic!("identical all the way down: {e}"));
        assert!(core.contains("(undef (struct 0))"), "{core}");
        assert!(
            encs.iter()
                .any(|r| r.contains("\"kind\": \"ptrwrap\"") && r.contains("(struct 1)")),
            "{encs:?}"
        );
    }

    /// A nested `ty.N` indexes the artifact's OWN type table: `[ty.0 x 4]` is
    /// four `u8`s in one.bin and four `u64`s in two.bin.
    #[test]
    fn a_nested_type_table_entry_two_artifacts_define_differently_is_refused() {
        fn array_of_ty0(m: &mut trust_ir::Module) {
            m.structs.push(struct_def(
                1,
                "W",
                vec![Ty::Array(trust_ir::value::TyId::new(0), 4)],
                8,
            ));
        }
        let refused = project_nested(
            |m| {
                array_of_ty0(m);
                m.types.push(Ty::U8);
            },
            |m| {
                array_of_ty0(m);
                m.types.push(Ty::U64);
            },
        )
        .expect_err("ty.0 is u8 in one.bin and u64 in two.bin");
        assert!(
            refused.starts_with("struct.1 is named by bodies"),
            "{refused}"
        );
    }

    /// A recursive type terminates, and two identical cycles agree.
    #[test]
    fn a_cyclic_definition_terminates_and_compares() {
        let node = |m: &mut trust_ir::Module| {
            m.structs.push(struct_def(
                1,
                "Node",
                vec![Ty::PtrConst(Box::new(Ty::Struct(StructId::new(1))))],
                8,
            ));
        };
        project_nested(node, node).unwrap_or_else(|e| panic!("one cyclic type: {e}"));
    }

    /// Fail-closed: an artifact-local id the comparison does not resolve (here
    /// a function type) cannot be shown to mean one thing in two artifacts.
    #[test]
    fn an_unresolved_local_id_in_a_shared_definition_is_refused() {
        let func = |m: &mut trust_ir::Module| {
            m.structs
                .push(struct_def(1, "F", vec![Ty::Func(FuncTyId::new(0))], 8));
        };
        let refused = project_nested(func, func)
            .expect_err("func.0 is an index into each artifact's own table");
        assert!(
            refused.starts_with("struct.1 is named by bodies"),
            "{refused}"
        );
    }

    /// One enum at raw id 1, descriptor `encoding`, variants `variants`, named
    /// by one body of the PRIMARY module; its encodings rows and refusals.
    fn encodings_of(
        encoding: trust_ir::ty::EnumTagEncoding,
        variants: Vec<Vec<Ty>>,
    ) -> (Vec<String>, Vec<String>) {
        let mut module = trust_ir::Module::new("primary");
        module.functions.push(function(
            0,
            "a",
            Some(vec![Inst::Undef {
                ty: Ty::Enum(EnumId::new(1)),
            }]),
        ));
        let mut def = EnumDef::new(
            EnumId::new(1),
            "E",
            variants
                .into_iter()
                .enumerate()
                .map(|(i, fields)| trust_ir::ty::EnumVariant {
                    name: format!("V{i}"),
                    fields,
                    field_names: Vec::new(),
                })
                .collect(),
        );
        def.layout = Some(trust_ir::ty::EnumLayoutDescriptor {
            encoding,
            size: 8,
            align: 8,
            variant_field_offsets: Vec::new(),
        });
        module.enums.push(def);
        let chain: Vec<&trust_ir::Function> = module.functions.iter().collect();
        let (_, mut p) = project_merged(&module, &[], &chain, None).expect("projects");
        derive_encodings(&module, &[], &mut p).expect("no collision")
    }

    /// An `Untagged` descriptor stores NO tag, and trust-ir's canonical layout
    /// budgets one: refused and recorded, never passed off as "canonical
    /// layout, no row" (verifier r6, 2026-09-24 -- it fell through a
    /// `let Niche { .. } = … else { continue }`).
    #[test]
    fn an_untagged_descriptor_is_refused_and_recorded() {
        let (encs, refused) =
            encodings_of(trust_ir::ty::EnumTagEncoding::Untagged, vec![vec![Ty::Ptr]]);
        assert!(encs.is_empty(), "{encs:?}");
        assert_eq!(refused.len(), 1, "{refused:?}");
        assert!(
            refused[0].starts_with("enum.1: its layout descriptor is Untagged"),
            "{refused:?}"
        );
    }

    #[test]
    fn a_single_inhabited_descriptor_retains_its_selected_variant_in_the_refusal() {
        for variant in [0, 1] {
            let variants = (0..2)
                .map(|index| vec![if index == variant { Ty::Ptr } else { Ty::Never }])
                .collect();
            let (encs, refused) = encodings_of(
                trust_ir::ty::EnumTagEncoding::SingleInhabited { variant },
                variants,
            );
            assert!(encs.is_empty(), "{encs:?}");
            assert_eq!(refused.len(), 1, "{refused:?}");
            assert!(refused[0].contains("SingleInhabited"), "{refused:?}");
            assert!(
                refused[0].contains(&format!("selected variant {variant}")),
                "{refused:?}"
            );
        }
    }

    // ── VERIFIER r7 (2026-09-24) ───────────────────────────────────────────
    //
    // Each test below failed on f4ae4acfe (the r7 fix) or passed there for the
    // wrong reason; see the A/B in the commit that added them.

    /// A primary module whose one body is `undef root`, with `structs` and
    /// `enums` as its tables, projected under `usize_bits` and `target`: its
    /// encodings rows, its refusals, and the enum ids interned by the end.
    fn derive_over(
        root: Ty,
        structs: Vec<StructDef>,
        enums: Vec<EnumDef>,
        usize_bits: Option<u32>,
        target: Option<trust_ir::TargetInfo>,
    ) -> (Vec<String>, Vec<String>, Vec<u32>) {
        let mut module = trust_ir::Module::new("primary");
        module
            .functions
            .push(function(0, "a", Some(vec![Inst::Undef { ty: root }])));
        module.structs = structs;
        module.enums = enums;
        module.target_info = target;
        let chain: Vec<&trust_ir::Function> = module.functions.iter().collect();
        let (_, mut p) = project_merged(&module, &[], &chain, usize_bits).expect("projects");
        let (encs, refused) = derive_encodings(&module, &[], &mut p).expect("no collision");
        (encs, refused, p.enum_order.clone())
    }

    /// Enum `id` with `variants` and the descriptor `encoding` / `size` /
    /// `offsets`.
    fn enum_with(
        id: u32,
        encoding: trust_ir::ty::EnumTagEncoding,
        variants: Vec<Vec<Ty>>,
        size: u64,
        offsets: Vec<Vec<u64>>,
    ) -> EnumDef {
        let mut def = EnumDef::new(
            EnumId::new(id),
            "E",
            variants
                .into_iter()
                .enumerate()
                .map(|(i, fields)| trust_ir::ty::EnumVariant {
                    name: format!("V{i}"),
                    fields,
                    field_names: Vec::new(),
                })
                .collect(),
        );
        def.layout = Some(trust_ir::ty::EnumLayoutDescriptor {
            encoding,
            size,
            align: 8,
            variant_field_offsets: offsets,
        });
        def
    }

    /// The `Option<ptr>` niche: variant 0 is the zero word, variant 1 carries
    /// the word, over a 64-bit lane.
    fn option_niche(niche_ty: trust_ir::ty::EnumTagRepr) -> trust_ir::ty::EnumTagEncoding {
        trust_ir::ty::EnumTagEncoding::Niche {
            untagged_variant: 1,
            niche_variants_start: 0,
            niche_variants_end: 0,
            niche_start: 0,
            niche_offset: 0,
            niche_ty,
        }
    }

    /// `Option<payload>` at raw `enum.1`, niche-encoded exactly as a pointer
    /// word, with the descriptor's `size` and `some` offsets overridable.
    fn option_of(payload: Ty, niche_ty: trust_ir::ty::EnumTagRepr) -> EnumDef {
        enum_with(
            1,
            option_niche(niche_ty),
            vec![vec![], vec![payload]],
            8,
            vec![vec![], vec![0]],
        )
    }

    fn target(pointer_size: u32) -> trust_ir::TargetInfo {
        trust_ir::TargetInfo {
            triple: "x86_64-unknown-linux-gnu".into(),
            pointer_size,
            endianness: trust_ir::Endianness::Little,
            abi: None,
            struct_passing: trust_ir::StructPassingPolicy::default(),
        }
    }

    /// PROBE 1. An `Untagged` enum reached only as a WRAPPER's payload was
    /// never examined: the struct loop walked a clone of `struct_order` taken
    /// before it, and the enum interned by the wrapper row came after both
    /// loops. It got the canonical layout, silently: a ptrwrap row with payload
    /// `(rawconst (enum 0))` and `refused=[]`.
    #[test]
    fn an_untagged_enum_reached_through_a_wrapper_payload_is_refused() {
        let (encs, refused, enums) = derive_over(
            Ty::Struct(StructId::new(1)),
            vec![struct_def(
                1,
                "W",
                vec![Ty::PtrConst(Box::new(Ty::Enum(EnumId::new(2))))],
                8,
            )],
            vec![enum_with(
                2,
                trust_ir::ty::EnumTagEncoding::Untagged,
                vec![vec![Ty::Ptr]],
                8,
                vec![vec![0]],
            )],
            None,
            None,
        );
        assert!(
            encs.iter().any(|r| r.contains("(rawconst (enum 0))")),
            "{encs:?}"
        );
        assert!(
            refused
                .iter()
                .any(|r| r.starts_with("enum.2: its layout descriptor is Untagged")),
            "{refused:?}"
        );
        assert_eq!(enums, vec![2], "the payload's enum is interned");
    }

    /// PROBE 2. A niche `Option<ptr>` reached only as a wrapper's payload got
    /// neither its nicheptr row nor a refusal.
    #[test]
    fn a_niche_enum_reached_through_a_wrapper_payload_gets_its_row() {
        let mut option = option_of(Ty::Ptr, trust_ir::ty::EnumTagRepr::U64);
        option.id = EnumId::new(2);
        let (encs, refused, _) = derive_over(
            Ty::Struct(StructId::new(1)),
            vec![struct_def(1, "W", vec![Ty::Enum(EnumId::new(2))], 8)],
            vec![option],
            Some(64),
            None,
        );
        assert!(
            encs.iter()
                .any(|r| r.contains("\"crate_id\": 2, \"kind\": \"nicheptr\"")),
            "{encs:?} {refused:?}"
        );
    }

    /// PROBE 3. An `Untagged` enum reached only through a NICHE row's payload
    /// (`Option<*const U>`), likewise.
    #[test]
    fn an_untagged_enum_reached_through_a_niche_payload_is_refused() {
        let (encs, refused, _) = derive_over(
            Ty::Enum(EnumId::new(1)),
            vec![],
            vec![
                option_of(
                    Ty::PtrConst(Box::new(Ty::Enum(EnumId::new(2)))),
                    trust_ir::ty::EnumTagRepr::U64,
                ),
                enum_with(
                    2,
                    trust_ir::ty::EnumTagEncoding::Untagged,
                    vec![vec![Ty::Ptr]],
                    8,
                    vec![vec![0]],
                ),
            ],
            Some(64),
            None,
        );
        assert!(
            encs.iter()
                .any(|r| r.contains("\"crate_id\": 1, \"kind\": \"nicheptr\"")),
            "{encs:?} {refused:?}"
        );
        assert!(
            refused
                .iter()
                .any(|r| r.starts_with("enum.2: its layout descriptor is Untagged")),
            "{refused:?}"
        );
    }

    /// PROBE 4. A pointer wrapper (`NonNull`-shaped) reached only as another
    /// wrapper's payload got no ptrwrap row.
    #[test]
    fn a_wrapper_reached_through_a_wrapper_payload_gets_its_row() {
        let (encs, refused, _) = derive_over(
            Ty::Struct(StructId::new(1)),
            vec![
                struct_def(1, "Outer", vec![Ty::Struct(StructId::new(2))], 8),
                struct_def(2, "NonNull", vec![Ty::Ptr], 8),
            ],
            vec![],
            None,
            None,
        );
        assert!(
            encs.iter()
                .any(|r| r.contains("\"crate_id\": 2, \"kind\": \"ptrwrap\"")),
            "{encs:?} {refused:?}"
        );
    }

    /// PROBE 5. A nested id NEITHER artifact defines rendered
    /// `struct.2<undefined>` with no label, so the two agreed on it and
    /// `struct.1` projected as one type with a ptrwrap row, payload `(struct 1)`.
    #[test]
    fn a_nested_id_neither_artifact_defines_is_not_one_type() {
        let refused = project_nested(wrapper_over_struct_2, wrapper_over_struct_2)
            .expect_err("struct.2 is defined by neither artifact");
        assert!(
            refused.starts_with("struct.1 is named by bodies from merge@1 and merge@2"),
            "{refused}"
        );
    }

    /// PROBE 6. The same at TOP level: `struct.1` defined by neither artifact
    /// projected Ok, with one artifact's refusal recorded.
    #[test]
    fn a_top_level_id_neither_artifact_defines_is_not_one_type() {
        let refused =
            project_nested(|_| {}, |_| {}).expect_err("struct.1 is defined by neither artifact");
        assert!(
            refused.starts_with("struct.1 is named by bodies from merge@1 and merge@2"),
            "{refused}"
        );
    }

    /// `enum.1` with variants `[[], [ptr]]` and a `Direct` descriptor, alone
    /// in the primary module.
    fn direct(tag_offset: u64, size: u64, offsets: Vec<Vec<u64>>) -> (Vec<String>, Vec<String>) {
        let (encs, refused, _) = derive_over(
            Ty::Enum(EnumId::new(1)),
            vec![],
            vec![enum_with(
                1,
                trust_ir::ty::EnumTagEncoding::Direct { tag_offset },
                vec![vec![], vec![Ty::Ptr]],
                size,
                offsets,
            )],
            None,
            Some(target(8)),
        );
        (encs, refused)
    }

    /// The control: a `Direct` descriptor that states EXACTLY trust-ir's
    /// canonical tagged-union layout -- a `u8` tag at byte 0, the pointer at
    /// the payload offset 8, 16 bytes -- gets no row and no refusal.
    #[test]
    fn a_direct_descriptor_stating_the_canonical_layout_gets_no_row_and_no_refusal() {
        let (encs, refused) = direct(0, 16, vec![vec![], vec![8]]);
        assert!(
            encs.is_empty() && refused.is_empty(),
            "{encs:?} {refused:?}"
        );
    }

    /// PROBE 7. `Direct { tag_offset: 8 }` passed as canonical, with no row
    /// and no refusal; so did any size and any field order.
    #[test]
    fn a_direct_descriptor_off_the_canonical_layout_is_refused() {
        for (tag_offset, size, offsets, clause) in [
            (8, 16, vec![vec![], vec![0]], "the tag is at byte 8, not 0"),
            (0, 8, vec![vec![], vec![8]], "size 8 bytes, canonical 16"),
            (
                0,
                16,
                vec![vec![], vec![0]],
                "field offsets [[], [0]], canonical [[], [8]]",
            ),
        ] {
            let (encs, refused) = direct(tag_offset, size, offsets);
            assert!(encs.is_empty(), "{encs:?}");
            assert!(
                refused.len() == 1
                    && refused[0].starts_with("enum.1: its Direct descriptor is not trust-ir's")
                    && refused[0].contains(clause),
                "`{clause}`: {refused:?}"
            );
        }
    }

    /// The control: `Option<ptr>` niche-encoded as one 64-bit pointer word,
    /// stated by the command line and the artifact alike, gets its row.
    #[test]
    fn an_option_pointer_niche_gets_its_row() {
        let (encs, refused, _) = derive_over(
            Ty::Enum(EnumId::new(1)),
            vec![],
            vec![option_of(Ty::Ptr, trust_ir::ty::EnumTagRepr::U64)],
            Some(64),
            Some(target(8)),
        );
        assert!(refused.is_empty(), "{refused:?}");
        assert_eq!(encs.len(), 1, "{encs:?}");
        assert!(encs[0].contains("\"kind\": \"nicheptr\""), "{encs:?}");
    }

    /// `niche_ty` was ignored and any single-field payload accepted. Each
    /// clause the one-pointer-word row depends on is now its own refusal.
    #[test]
    fn a_niche_that_is_not_one_pointer_word_is_refused() {
        let u64_lane = trust_ir::ty::EnumTagRepr::U64;
        let mut none_field = option_of(Ty::Ptr, u64_lane);
        none_field.variants[0].fields.push(Ty::U8);
        let mut some_at_8 = option_of(Ty::Ptr, u64_lane);
        some_at_8
            .layout
            .as_mut()
            .expect("a descriptor")
            .variant_field_offsets = vec![vec![], vec![8]];
        let mut wide = option_of(Ty::Ptr, u64_lane);
        wide.layout.as_mut().expect("a descriptor").size = 16;
        for (def, bits, tgt, clause) in [
            (
                option_of(Ty::Ptr, trust_ir::ty::EnumTagRepr::U8),
                Some(64),
                None,
                "niche_ty is U8, a 8-bit lane, not the 64-bit pointer word",
            ),
            (
                option_of(Ty::U64, u64_lane),
                Some(64),
                None,
                "the payload U64 is not a thin pointer",
            ),
            (
                none_field,
                Some(64),
                None,
                "the none variant carries 1 field(s)",
            ),
            (
                some_at_8,
                Some(64),
                None,
                "the some variant's field offsets are Some([8])",
            ),
            (
                wide,
                Some(64),
                None,
                "the descriptor's size is 16 bytes, not one 64-bit word",
            ),
            (
                option_of(Ty::Ptr, u64_lane),
                None,
                None,
                "no pointer width is stated (--usize-bits)",
            ),
        ] {
            let (encs, refused, _) =
                derive_over(Ty::Enum(EnumId::new(1)), vec![], vec![def], bits, tgt);
            assert!(encs.is_empty(), "`{clause}`: {encs:?}");
            assert!(
                refused.len() == 1 && refused[0].contains(clause),
                "`{clause}`: {refused:?}"
            );
        }
    }

    /// The ir_lzd shape: `Option<Arc<_>>` whose payload is a wrapper over a
    /// wrapper over the pointer word, ZST markers beside it. A row, and the
    /// wrappers' own rows -- run against the reference, too. The tables are the
    /// committed sidecar text's (`data/crystal_callee_sidecar_step1_2026-09-09/
    /// clean_kernel.callees.trust-ir.txt`): `Arc { struct.0, struct.1,
    /// struct.2 } size=8`, NonNull one pointer, PhantomData and Global
    /// field-less, size 0, align 1.
    #[test]
    fn a_niche_over_a_wrapper_of_a_pointer_gets_its_row() {
        let zst = |id: u32, name: &str| {
            let mut s = struct_def(id, name, vec![], 0);
            s.align = Some(1);
            s
        };
        let (encs, refused, _) = derive_over(
            Ty::Enum(EnumId::new(1)),
            vec![
                struct_def(
                    3,
                    "Arc",
                    vec![
                        Ty::Struct(StructId::new(0)),
                        Ty::Struct(StructId::new(9)),
                        Ty::Struct(StructId::new(2)),
                    ],
                    8,
                ),
                struct_def(0, "NonNull", vec![Ty::PtrConst(Box::new(Ty::U8))], 8),
                zst(9, "PhantomData"),
                zst(2, "Global"),
            ],
            vec![option_of(
                Ty::Struct(StructId::new(3)),
                trust_ir::ty::EnumTagRepr::U64,
            )],
            Some(64),
            None,
        );
        assert!(refused.is_empty(), "{refused:?}");
        assert!(
            encs.iter().any(|r| r.contains("\"kind\": \"nicheptr\""))
                && encs
                    .iter()
                    .filter(|r| r.contains("\"kind\": \"ptrwrap\""))
                    .count()
                    == 2,
            "{encs:?}"
        );
    }

    /// A struct with no fields that is not zero-sized is OPAQUE, and was
    /// skipped as "no wrapper, no refusal" -- read as the canonical, zero-sized
    /// layout. A wrapper whose one field is not at byte 0 is not its word.
    #[test]
    fn an_opaque_struct_and_an_offset_wrapper_field_are_refused() {
        let mut offset = struct_def(1, "W", vec![Ty::Ptr], 16);
        offset.fields[0].offset = Some(8);
        for (def, clause) in [
            (
                struct_def(1, "Opaque", vec![], 24),
                "struct.1: declares no fields and size Some(24)",
            ),
            (
                offset,
                "struct.1: its one non-ZST field sits at byte 8, not 0",
            ),
        ] {
            let (encs, refused, _) =
                derive_over(Ty::Struct(StructId::new(1)), vec![def], vec![], None, None);
            assert!(encs.is_empty(), "{encs:?}");
            assert!(
                refused.len() == 1 && refused[0].starts_with(clause),
                "`{clause}`: {refused:?}"
            );
        }
    }

    // ── VERIFIER r7b (2026-09-24) ──────────────────────────────────────────
    //
    // Each named test below is a case the r7b verifier MEASURED; each failed on
    // cffdd8075 (and on 45f9ead15). The differential test after them is the
    // mechanism that replaced the clause-by-clause judgements those cases
    // slipped between: every minted row is run against trust-ir's reference.

    fn wasm32() -> trust_ir::TargetInfo {
        trust_ir::TargetInfo {
            triple: "wasm32-unknown-unknown".into(),
            ..target(4)
        }
    }

    fn probe_of<'a>(
        enums: &'a [EnumDef],
        structs: &'a [StructDef],
        target: Option<&'a trust_ir::TargetInfo>,
    ) -> reference::Probe<'a> {
        reference::Probe {
            enums,
            structs,
            types: &[],
            target,
        }
    }

    /// (1) A niche descriptor over EXPLICIT discriminants. trust-ir's
    /// interpreter synthesizes a niche-decoded tag as the variant's EFFECTIVE
    /// DISCRIMINANT (`synthesized_tag_value`); `ir_niche_image` images the
    /// zero word `[int_ none]` and any other `[int_ some, payload]` -- variant
    /// INDICES. Measured: the zero word decodes to tag 5 (the row said 0), a
    /// non-zero word to tag 6 (the row said 1); the row was minted.
    #[test]
    fn a_niche_over_explicit_discriminants_is_refused() {
        let mut def = option_of(Ty::Ptr, trust_ir::ty::EnumTagRepr::U64);
        def.discriminants = vec![Some(5), Some(6)];
        let t8 = target(8);
        let images = reference::reference_images(
            &probe_of(std::slice::from_ref(&def), &[], Some(&t8)),
            Agg::Enum,
            1,
            &[],
        )
        .expect("the reference decodes the descriptor");
        for (w, img) in &images {
            let want = if *w == 0 {
                Img::Agg(vec![Img::Word(5)])
            } else {
                Img::Agg(vec![Img::Word(6), Img::Word(*w)])
            };
            assert_eq!(*img, want, "the reference's tag is the discriminant");
        }
        let (encs, refused, _) = derive_over(
            Ty::Enum(EnumId::new(1)),
            vec![],
            vec![def],
            Some(64),
            Some(t8),
        );
        assert!(encs.is_empty(), "{encs:?}");
        assert_eq!(
            refused,
            vec![
                "enum.1: its nicheptr row does not decode as the reference does: at the word 0x0 \
                 the row images [0x0] and trust-ir's reference interpreter decodes [0x5]"
                    .to_string()
            ]
        );
    }

    /// (2) A row whose PAYLOAD row is refused is refused too, to a fixpoint.
    /// `Option<Box<char>>`: Box over NonNull over `*const char`; `char` has no
    /// Clean image, so NonNull's row is refused -- and the Box and Option rows
    /// stood, imaging the Some payload `Box { ptr }` where the reference
    /// decodes `Box { NonNull { ptr } }`.
    #[test]
    fn a_row_whose_payload_row_is_refused_is_refused() {
        let (encs, refused, _) = derive_over(
            Ty::Enum(EnumId::new(1)),
            vec![
                struct_def(3, "Box", vec![Ty::Struct(StructId::new(0))], 8),
                struct_def(0, "NonNull", vec![Ty::PtrConst(Box::new(Ty::Char))], 8),
            ],
            vec![option_of(
                Ty::Struct(StructId::new(3)),
                trust_ir::ty::EnumTagRepr::U64,
            )],
            Some(64),
            None,
        );
        assert!(encs.is_empty(), "{encs:?}");
        let starts = [
            "struct.0: its one non-ZST field has no Clean image",
            "enum.1: its nicheptr row does not decode as the reference does",
            "struct.3: its ptrwrap row does not decode as the reference does",
        ];
        assert_eq!(refused.len(), starts.len(), "{refused:?}");
        for (r, s) in refused.iter().zip(starts) {
            assert!(r.starts_with(s), "`{s}`: {refused:?}");
        }
    }

    /// (3) A zero-sized marker WITH a field is not a ZST slot: `ir_zst_spine`
    /// images a slot `aggv vnil`, the reference's decode of a zero-FIELD
    /// aggregate, and `Invariant(PhantomData)` decodes to
    /// `Aggregate([Aggregate([])])`. `Handle { ptr, Invariant }` minted a
    /// wrapper row imaging it `aggv vnil`.
    #[test]
    fn a_zero_sized_marker_with_a_field_is_not_a_zst_slot() {
        let mut phantom = struct_def(3, "PhantomData", vec![], 0);
        phantom.align = Some(1);
        let mut invariant = struct_def(2, "Invariant", vec![Ty::Struct(StructId::new(3))], 0);
        invariant.align = Some(1);
        let handle = struct_def(1, "Handle", vec![Ty::Ptr, Ty::Struct(StructId::new(2))], 8);
        let structs = vec![handle, invariant, phantom];
        let images =
            reference::reference_images(&probe_of(&[], &structs, None), Agg::Struct, 1, &[])
                .expect("the reference decodes Handle");
        assert_eq!(
            images[1].1,
            Img::Agg(vec![Img::Word(1), Img::Agg(vec![Img::Agg(vec![])])]),
            "the marker is a live slot to the reference"
        );
        let (encs, refused, _) =
            derive_over(Ty::Struct(StructId::new(1)), structs, vec![], None, None);
        assert!(encs.is_empty(), "{encs:?}");
        assert!(
            refused.len() == 1 && refused[0].starts_with("struct.1: 2 non-ZST field(s)"),
            "{refused:?}"
        );
    }

    /// (4) One raw id judged under one target is refused for another. A
    /// `Direct { size 16, [[], [8]] }` enum defined identically in a 64-bit
    /// primary and a wasm32 merge: trust-ir's canonical layout is 16 bytes at
    /// 64 bits and 8 at 32, and the descriptor was judged canonical -- under
    /// the definer's target only -- for the wasm32 body too.
    #[test]
    fn a_layout_judged_under_one_target_is_not_taken_for_another() {
        let def = enum_with(
            1,
            trust_ir::ty::EnumTagEncoding::Direct { tag_offset: 0 },
            vec![vec![], vec![Ty::Ptr]],
            16,
            vec![vec![], vec![8]],
        );
        let size_at = |t: trust_ir::TargetInfo| {
            let mut probe = trust_ir::Module::new("probe");
            let mut bare = def.clone();
            bare.layout = None;
            probe.enums = vec![bare];
            probe.target_info = Some(t);
            super::canonical_enum_layout(&probe, &def).map(|(size, _, _)| size)
        };
        assert_eq!(
            (size_at(target(8)), size_at(wasm32())),
            (Ok(16), Ok(8)),
            "trust-ir lays the enum out differently at the two widths"
        );
        let undef = |id: u32, name: &str| {
            function(
                id,
                name,
                Some(vec![Inst::Undef {
                    ty: Ty::Enum(EnumId::new(1)),
                }]),
            )
        };
        let mut module = trust_ir::Module::new("primary");
        module.target_info = Some(target(8));
        module.functions.push(undef(0, "a1"));
        module.enums.push(def.clone());
        let mut other = trust_ir::Module::new("merged");
        other.target_info = Some(wasm32());
        other.functions.push(undef(0, "a2"));
        other.enums.push(def);
        let (merged, _) = merge_all(
            &mut module,
            vec![MergeInput {
                path: "wasm32.bin".into(),
                module: other,
                joins: vec![],
            }],
        );
        let chain: Vec<&trust_ir::Function> = module.functions.iter().collect();
        let refused = project_merged(&module, &merged, &chain, None)
            .map(|(core, _)| core)
            .expect_err("two layout targets");
        assert!(
            refused.starts_with(
                "the artifacts' layout targets differ (module 64-bit Little, merge@1 32-bit Little)"
            ),
            "{refused}"
        );
    }

    /// (4, the flag) A wasm32 artifact under `--usize-bits 64` imaged `usize`
    /// as `(uint 64)`, with no refusal. At its own width it projects.
    #[test]
    fn an_artifact_whose_width_is_not_usize_bits_is_refused() {
        let mut module = trust_ir::Module::new("primary");
        module.target_info = Some(wasm32());
        module
            .functions
            .push(function(0, "a", Some(vec![Inst::Undef { ty: Ty::Usize }])));
        let chain: Vec<&trust_ir::Function> = module.functions.iter().collect();
        let refused = project_merged(&module, &[], &chain, Some(64))
            .map(|(core, _)| core)
            .expect_err("a 32-bit artifact under a 64-bit usize");
        assert!(
            refused.starts_with("module is a 32-bit-pointer artifact and --usize-bits says 64"),
            "{refused}"
        );
        let (core, _) = project_merged(&module, &[], &chain, Some(32))
            .unwrap_or_else(|e| panic!("its own width: {e}"));
        assert!(core.contains("(undef (uint 32))"), "{core}");
    }

    fn niche(canonical: usize, none: usize, some: usize, payload: &str) -> Row {
        Row {
            canonical,
            raw: 0,
            first_by: 0,
            table: String::new(),
            decl: String::new(),
            payload: payload.into(),
            shape: Shape::Niche { none, some },
        }
    }

    fn wrap(canonical: usize, slot: usize, fields: usize, payload: &str) -> Row {
        Row {
            canonical,
            raw: 0,
            first_by: 0,
            table: String::new(),
            decl: String::new(),
            payload: payload.into(),
            shape: Shape::Wrap { slot, fields },
        }
    }

    /// The model half of the gate on the shapes `eval_ir_machine.rs` states,
    /// with the expected images typed by hand: `ir_niche_image` (the zero word
    /// is the `none` tag alone, any other word the `some` tag and the payload),
    /// `ir_spine_with_slot` (the word at slot i, `aggv vnil` elsewhere, length
    /// c), a payload imaged through ITS row, first-match on (kind, id), the
    /// identity at a type with no row, and fuel = the table's length (a table
    /// that chains into itself stops, it does not loop). This pins what the
    /// Rust model DOES; that the definitions it was transliterated from are
    /// still the registered ones is
    /// `the_model_transliterates_these_exact_clean_definitions`, which reads
    /// them (verifier r8: this test alone never did).
    #[test]
    fn the_model_images_the_shapes_the_clean_view_states() {
        use reference::load_view;
        let w = |n| Img::Word(n);
        let a = |v: Vec<Img>| Img::Agg(v);
        let rows = vec![niche(0, 0, 1, "(ptr)")];
        assert_eq!(load_view(&rows, "(enum 0)", w(0)), a(vec![w(0)]));
        assert_eq!(load_view(&rows, "(enum 0)", w(9)), a(vec![w(1), w(9)]));
        assert_eq!(load_view(&rows, "(struct 0)", w(9)), w(9), "no row");
        assert_eq!(
            load_view(&rows, "(enum 0)", a(vec![w(3)])),
            a(vec![w(3)]),
            "an aggregate passes through"
        );
        let arc = vec![
            niche(1, 0, 1, "(struct 0)"),
            wrap(0, 0, 3, "(struct 1)"),
            wrap(1, 1, 2, "(rawconst (uint 8))"),
        ];
        assert_eq!(
            load_view(&arc, "(enum 1)", w(8)),
            a(vec![
                w(1),
                a(vec![a(vec![a(vec![]), w(8)]), a(vec![]), a(vec![])])
            ])
        );
        let first = vec![wrap(0, 0, 1, "(ptr)"), wrap(0, 0, 2, "(ptr)")];
        assert_eq!(load_view(&first, "(struct 0)", w(8)), a(vec![w(8)]));
        let cycle = vec![wrap(0, 0, 1, "(struct 0)")];
        assert_eq!(
            load_view(&cycle, "(struct 0)", w(8)),
            a(vec![a(vec![w(8)])]),
            "one row of fuel for the payload, then the identity"
        );
    }

    /// The file whose definitions `mod reference` transliterates.
    const CLEAN_VIEW: &str = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../crates/clean-verify/src/spec/core_spec/eval_ir_machine.rs"
    );

    /// Each definition the Rust model transliterates, and the sha256 of the
    /// Lean text `add_recursive_def` registers for it -- the call's first
    /// argument, decoded from the Rust source exactly as the compiler would
    /// (one literal, raw or not, or a `concat!` of them).
    const TRANSLITERATED: [(&str, &str); 11] = [
        (
            "ir_enc_len",
            "45352fb2b27adc9e3a37e7d2b2fa2a54327f38b010949244b3815b1b3bde8518",
        ),
        (
            "ir_enc_matches",
            "4bc6a84d3d9e38b57e21b4395f0d143a6fd9a2899152aa493d6e325e2e9398ee",
        ),
        (
            "ir_enc_find",
            "5175f1ed1e650a1cf16f2faf95009ab6bebcfd592a9a06e5d2fce1d585c18ed4",
        ),
        (
            "ir_zst_spine",
            "7919f8c0bffda734f15e6188760de66a85ec117a017dc7cb9f82d33761f5989d",
        ),
        (
            "ir_spine_with_slot",
            "89d32aa20303e34ba1fae9cf3d1e8e31e3f4b21eebb1d05874e90920ff0f0bc1",
        ),
        (
            "ir_niche_image",
            "804fc666a17aead44fd16b87d3229e1511c6788fcb53afe58ea41347a8ccd239",
        ),
        (
            "ir_wrap_image",
            "1f4436b13d06439cdaa79ed5348ee5877d24b4083745bf78953fdddae42cb001",
        ),
        (
            "ir_view_word",
            "76bf49bcfdb898a8648c12a942a4fad7f5225d2f728d75c9d70a0bc46c09a7f6",
        ),
        (
            "ir_view_ty",
            "e4d22798ddd2a3e559cb3c1a379e8fd7e92f1086bb1337419df2668b945dbd80",
        ),
        (
            "ir_view_result",
            "097b2a61318246c8b2d65be19327f7b15b6907f2eea2c528345edb8c3e8a08a8",
        ),
        (
            "ir_load_view",
            "01e1cb0c43648c760cf6508a44a6e4568977dca71d69a320c513a94ca4cae543",
        ),
    ];

    /// One Rust string literal at the start of `s` -- `"..."` with the escapes
    /// the definitions use, `r"..."` or `r#"..."#` -- decoded, and the rest.
    /// Anything else is None: an escape this does not know fails the pin.
    fn rust_literal(s: &str) -> Option<(String, &str)> {
        if let Some(r) = s.strip_prefix('r') {
            let hashes = r.len() - r.trim_start_matches('#').len();
            let body = r[hashes..].strip_prefix('"')?;
            let close = format!("\"{}", "#".repeat(hashes));
            let end = body.find(&close)?;
            return Some((body[..end].to_string(), &body[end + close.len()..]));
        }
        let body = s.strip_prefix('"')?;
        let mut out = String::new();
        let mut chars = body.char_indices().peekable();
        while let Some((i, c)) = chars.next() {
            match c {
                '"' => return Some((out, &body[i + 1..])),
                '\\' => match chars.next()?.1 {
                    'n' => out.push('\n'),
                    't' => out.push('\t'),
                    '\\' => out.push('\\'),
                    '"' => out.push('"'),
                    '\'' => out.push('\''),
                    '\n' => while chars.next_if(|(_, c)| c.is_whitespace()).is_some() {},
                    _ => return None,
                },
                c => out.push(c),
            }
        }
        None
    }

    /// A CODE token of Rust source: comments are dropped, and a string or char
    /// literal is ONE token holding its source text, so nothing written inside
    /// a comment or a literal can read as a registration.
    #[derive(Clone, Copy, Debug)]
    enum Tok<'s> {
        Ident(&'s str),
        Lit(&'s str),
        Punct(char),
    }

    impl<'s> Tok<'s> {
        /// The identifier this token is, if it is one.
        fn ident(self) -> Option<&'s str> {
            match self {
                Tok::Ident(id) => Some(id),
                Tok::Lit(_) | Tok::Punct(_) => None,
            }
        }

        /// The punctuation this token is, if it is one.
        fn punct(self) -> Option<char> {
            match self {
                Tok::Punct(c) => Some(c),
                Tok::Ident(_) | Tok::Lit(_) => None,
            }
        }
    }

    /// `src` as code tokens; None on a comment or literal that does not end.
    fn code_tokens(src: &str) -> Option<Vec<Tok<'_>>> {
        let word = |c: char| c.is_alphanumeric() || c == '_';
        let mut out = Vec::new();
        let mut i = 0;
        while i < src.len() {
            let rest = &src[i..];
            let c = rest.chars().next()?;
            let n = if c.is_whitespace() {
                c.len_utf8()
            } else if rest.starts_with("//") {
                rest.find('\n').unwrap_or(rest.len())
            } else if rest.starts_with("/*") {
                block_comment_len(rest)?
            } else if let Some(n) = literal_len(rest) {
                out.push(Tok::Lit(&rest[..n]));
                n
            } else if c == '\'' {
                // a lifetime or a label: never a literal, never an identifier here
                1 + rest[1..]
                    .find(|ch: char| !word(ch))
                    .unwrap_or(rest.len() - 1)
            } else if word(c) {
                let n = rest.find(|ch: char| !word(ch)).unwrap_or(rest.len());
                if !c.is_ascii_digit() {
                    out.push(Tok::Ident(&rest[..n]));
                }
                n
            } else {
                out.push(Tok::Punct(c));
                c.len_utf8()
            };
            i += n;
        }
        Some(out)
    }

    /// The byte length of the (nested) block comment at the start of `s`.
    fn block_comment_len(s: &str) -> Option<usize> {
        let (mut depth, mut j) = (0usize, 0usize);
        while j < s.len() {
            if s[j..].starts_with("/*") {
                depth += 1;
                j += 2;
            } else if s[j..].starts_with("*/") {
                depth -= 1;
                j += 2;
                if depth == 0 {
                    return Some(j);
                }
            } else {
                j += s[j..].chars().next()?.len_utf8();
            }
        }
        None
    }

    /// The byte length of the string, raw-string or char literal (with an
    /// optional `b`/`c` prefix) at the start of `s`; None for anything else.
    fn literal_len(s: &str) -> Option<usize> {
        let body = s.strip_prefix(['b', 'c']).unwrap_or(s);
        let pre = s.len() - body.len();
        if let Some(r) = body.strip_prefix('r') {
            let hashes = r.len() - r.trim_start_matches('#').len();
            let inner = r[hashes..].strip_prefix('"')?;
            let close = format!("\"{}", "#".repeat(hashes));
            return Some(pre + 1 + hashes + 1 + inner.find(&close)? + close.len());
        }
        if let Some(inner) = body.strip_prefix('"') {
            let mut escaped = false;
            for (k, c) in inner.char_indices() {
                if escaped {
                    escaped = false;
                } else if c == '\\' {
                    escaped = true;
                } else if c == '"' {
                    return Some(pre + 1 + k + 1);
                }
            }
            return None;
        }
        let inner = body.strip_prefix('\'')?;
        let mut chars = inner.char_indices();
        let (_, first) = chars.next()?;
        if first == '\\' {
            let (skip, _) = chars.next()?;
            return Some(pre + 1 + skip + 1 + inner[skip + 1..].find('\'')? + 1);
        }
        let (k, next) = chars.next()?;
        (next == '\'').then_some(pre + 1 + k + 1)
    }

    /// The first argument of a call -- one string literal, or a `concat!` of
    /// them -- decoded; None for anything else.
    fn literal_argument(toks: &[Tok<'_>]) -> Option<String> {
        let concat = match toks {
            [name, bang, open, rest @ ..]
                if name.ident() == Some("concat")
                    && bang.punct() == Some('!')
                    && open.punct() == Some('(') =>
            {
                Some(rest)
            }
            _ => None,
        };
        let Some(mut rest) = concat else {
            return match toks.first() {
                Some(Tok::Lit(raw)) => rust_literal(raw).map(|(text, _)| text),
                Some(Tok::Ident(_) | Tok::Punct(_)) | None => None,
            };
        };
        let mut out = String::new();
        loop {
            let (raw, tail) = match rest {
                [Tok::Lit(raw), tail @ ..] => (raw, tail),
                [Tok::Ident(_) | Tok::Punct(_), ..] | [] => return None,
            };
            out.push_str(&rust_literal(raw)?.0);
            rest = tail
                .split_first()
                .filter(|(comma, _)| comma.punct() == Some(','))
                .map_or(tail, |(_, after)| after);
            if rest.first().and_then(|t| t.punct()) == Some(')') {
                return Some(out);
            }
        }
    }

    /// Every Lean text registered for `def <name>` -- the decoded first
    /// argument of each `add_recursive_def(` call IN CODE whose text starts
    /// with it -- and how many string literals in code carry `def <name> ` at
    /// all. None when some `add_recursive_def(` call's first argument is not a
    /// literal this decodes: a registration the pin cannot read fails it.
    fn registered_defs(src: &str, name: &str) -> Option<(Vec<String>, usize)> {
        let head = format!("def {name} ");
        let toks = code_tokens(src)?;
        let mut defs = Vec::new();
        let mut copies = 0;
        for (k, tok) in toks.iter().enumerate() {
            match tok {
                Tok::Lit(raw) => copies += usize::from(raw.contains(&head)),
                Tok::Ident(id) => {
                    if *id == "add_recursive_def"
                        && toks.get(k + 1).and_then(|t| t.punct()) == Some('(')
                    {
                        let text = literal_argument(&toks[k + 2..])?;
                        if text.starts_with(&head) {
                            defs.push(text);
                        }
                    }
                }
                Tok::Punct(_) => {}
            }
        }
        Some((defs, copies))
    }

    /// verifier r8b (2026-09-25): the pin read the FIRST `add_recursive_def(`
    /// in the RAW file, comments included, so a stale copy of `ir_niche_image`
    /// left in a comment AHEAD of the real registration was read as the
    /// registered one -- the real one could then image nullptr as the some tag
    /// under a green pin. The registrations are read from code tokens now; a
    /// second copy anywhere in code, or a registration this cannot decode,
    /// fails the pin instead of choosing.
    #[test]
    fn a_pinned_text_left_in_a_comment_is_not_the_registered_one() {
        let src = concat!(
            "/* superseded: self.add_recursive_def(r\"def f (x : Nat) : Nat := old\", \"\") */\n",
            "// self.add_recursive_def(\"def f (x : Nat) : Nat := older\", \"\")\n",
            "let q = '\"'; let s = \"/* not a comment */\"; let l: &'static str = s;\n",
            "self.add_recursive_def(r\"def f (x : Nat) : Nat := new\", \"d\")?;\n",
        );
        assert_eq!(
            registered_defs(src, "f"),
            Some((vec!["def f (x : Nat) : Nat := new".to_string()], 1))
        );
        let twice = format!(
            "{src}fn dead() {{ self.add_recursive_def(r\"def f (x : Nat) : Nat := old\", \"\"); }}\n"
        );
        assert_eq!(
            registered_defs(&twice, "f").map(|(d, n)| (d.len(), n)),
            Some((2, 2))
        );
        let decoy = format!("{src}const OLD: &str = \"def f (x : Nat) : Nat := old\";\n");
        assert_eq!(
            registered_defs(&decoy, "f").map(|(d, n)| (d.len(), n)),
            Some((1, 2))
        );
        let unread = format!("{src}self.add_recursive_def(&format!(\"def g\"), \"\");\n");
        assert_eq!(registered_defs(&unread, "f"), None);
    }

    /// THE MODEL'S PIN TO CLEAN, READ -- not asserted (verifier r8,
    /// 2026-09-25). `mod reference` is a hand transliteration of eleven
    /// definitions in `eval_ir_machine.rs`, and until this test nothing in
    /// the projector's suite read that file: had `ir_niche_image`,
    /// `ir_spine_with_slot`, `ir_view_ty` or `ir_load_view` changed, every
    /// row the gate judged would have been judged against a view Clean no
    /// longer registers, and the suite would have stayed green. Each
    /// definition's registered text is hashed here; a change to any of them
    /// fails this test with the new text, and the fix is to re-read the
    /// transliteration against it -- then re-pin. What this does NOT decide is
    /// that the transliteration is right: that was checked by reading, once,
    /// against the texts these digests pin, and is exercised by
    /// `the_model_images_the_shapes_the_clean_view_states` and by the
    /// differential tests against trust-ir's interpreter.
    #[test]
    fn the_model_transliterates_these_exact_clean_definitions() {
        use sha2::{Digest, Sha256};
        let src = std::fs::read_to_string(CLEAN_VIEW)
            .unwrap_or_else(|e| panic!("{CLEAN_VIEW} is the Clean view the model copies: {e}"));
        let mut drifted = Vec::new();
        for (name, pinned) in TRANSLITERATED {
            let (texts, copies) = registered_defs(&src, name).unwrap_or_else(|| {
                panic!(
                    "{CLEAN_VIEW}: an `add_recursive_def(` whose first argument is not a \
                     literal this reads -- every registration must be one the pin can read"
                )
            });
            let [text] = texts.as_slice() else {
                panic!(
                    "{CLEAN_VIEW} registers `def {name}` {} time(s) in code, not once",
                    texts.len()
                )
            };
            assert_eq!(
                copies, 1,
                "{CLEAN_VIEW}: {copies} string literals in code carry `def {name} ` -- the one \
                 registration must be the only copy"
            );
            let digest = super::hex(&Sha256::digest(text.as_bytes()));
            if digest != pinned {
                drifted.push(format!("{name} (sha256 {digest}):\n{text}"));
            }
        }
        assert!(
            drifted.is_empty(),
            "the Clean view moved under the Rust model -- re-read `mod reference` against each \
             definition below, then re-pin TRANSLITERATED:\n\n{}",
            drifted.join("\n\n")
        );
    }

    /// verifier r8 (2026-09-25): a struct whose one live field does not fill
    /// it -- a `u32` in 8 bytes, a pointer in 16 -- was refused only because
    /// `reference::probe_words` happens to hold words above the field's width.
    /// It is refused by SHAPE now, whatever the probe words are, and a niche
    /// over such a wrapper is no pointer word.
    #[test]
    fn a_field_that_does_not_fill_its_struct_is_refused_by_shape() {
        for (name, field, size, tgt, bits) in [
            ("u32 in 8 bytes", Ty::U32, 8, Some(target(8)), 64),
            ("ptr in 16 bytes", Ty::Ptr, 16, Some(target(8)), 64),
            ("u64 in 16 bytes", Ty::U64, 16, Some(target(8)), 64),
            ("u16 in 4 bytes, wasm32", Ty::U16, 4, Some(wasm32()), 32),
        ] {
            let (encs, refused, _) = derive_over(
                Ty::Struct(StructId::new(10)),
                vec![laid(10, "W", vec![field], size, size.min(8))],
                vec![],
                Some(bits),
                tgt,
            );
            assert!(encs.is_empty(), "{name}: {encs:?}");
            assert!(
                refused.len() == 1
                    && refused[0].starts_with("struct.10: its one non-ZST field is ")
                    && refused[0].contains("the stored word is not that field"),
                "{name}: {refused:?}"
            );
        }
        let (encs, refused, _) = derive_over(
            Ty::Enum(EnumId::new(1)),
            vec![laid(10, "W", vec![Ty::Ptr], 16, 8)],
            vec![option_of(
                Ty::Struct(StructId::new(10)),
                trust_ir::ty::EnumTagRepr::U64,
            )],
            Some(64),
            Some(target(8)),
        );
        assert!(encs.is_empty(), "{encs:?}");
        assert!(
            refused
                .iter()
                .any(|r| r.starts_with("enum.1: ") && r.contains("is not a thin pointer")),
            "{refused:?}"
        );
    }

    /// HOW DECISIVE THE PROBE WORDS ARE, PINNED (verifier r8, 2026-09-25). The
    /// reference gate compares a row with trust-ir's interpreter at
    /// `reference::probe_words` only, and nothing tested that those words tell
    /// a wrong row from the reference: cut them to words <= 0x8000 and every
    /// other test passed. Each row below is WRONG -- the model images some
    /// word differently from the reference -- and the gate's own probe words
    /// (no extra words) must find a word where they differ. The structural
    /// clauses refuse most of these first; this pins the second line on its
    /// own, so neither can be weakened silently.
    #[test]
    fn the_probe_words_alone_tell_each_wrong_row_from_the_reference() {
        let t8 = target(8);
        let w32 = wasm32();
        let mut swapped_tags = option_of(Ty::Ptr, trust_ir::ty::EnumTagRepr::U64);
        swapped_tags.discriminants = vec![Some(1), Some(0)];
        let mut discriminants = option_of(Ty::Ptr, trust_ir::ty::EnumTagRepr::U64);
        discriminants.discriminants = vec![Some(5), Some(6)];
        let mut none_at_one = option_of(Ty::Ptr, trust_ir::ty::EnumTagRepr::U64);
        if let Some(l) = none_at_one.layout.as_mut() {
            l.encoding = trust_ir::ty::EnumTagEncoding::Niche {
                untagged_variant: 1,
                niche_variants_start: 0,
                niche_variants_end: 0,
                niche_start: 1,
                niche_offset: 0,
                niche_ty: trust_ir::ty::EnumTagRepr::U64,
            };
        }
        let marker = [
            laid(30, "PhantomData", vec![], 0, 1),
            laid(31, "Invariant", vec![Ty::Struct(StructId::new(30))], 0, 1),
        ];
        let narrow = |field: Ty, size: u64| vec![laid(10, "W", vec![field], size, size.min(8))];
        let mut handle = vec![laid(
            10,
            "Handle",
            vec![Ty::Ptr, Ty::Struct(StructId::new(31))],
            8,
            8,
        )];
        handle.extend(marker);
        type Wrong<'a> = (
            &'a str,
            Row,
            Vec<StructDef>,
            Vec<EnumDef>,
            Option<&'a trust_ir::TargetInfo>,
        );
        let raw = |mut r: Row, id: u32| {
            r.raw = id;
            r
        };
        let cases: Vec<Wrong<'_>> = vec![
            (
                "W{u32} in 8 bytes",
                raw(wrap(0, 0, 1, "(uint 32)"), 10),
                narrow(Ty::U32, 8),
                vec![],
                Some(&t8),
            ),
            (
                "W{u16} in 8 bytes",
                raw(wrap(0, 0, 1, "(uint 16)"), 10),
                narrow(Ty::U16, 8),
                vec![],
                Some(&t8),
            ),
            (
                "W{u8} in 8 bytes",
                raw(wrap(0, 0, 1, "(uint 8)"), 10),
                narrow(Ty::U8, 8),
                vec![],
                Some(&t8),
            ),
            (
                "W{ptr} in 16 bytes",
                raw(wrap(0, 0, 1, "(ptr)"), 10),
                narrow(Ty::Ptr, 16),
                vec![],
                Some(&t8),
            ),
            (
                "W{u64} in 16 bytes",
                raw(wrap(0, 0, 1, "(uint 64)"), 10),
                narrow(Ty::U64, 16),
                vec![],
                Some(&t8),
            ),
            (
                "wasm32 W{u16} in 4 bytes",
                raw(wrap(0, 0, 1, "(uint 16)"), 10),
                narrow(Ty::U16, 4),
                vec![],
                Some(&w32),
            ),
            (
                "Handle{ptr, Invariant} as slot 0 of 2",
                raw(wrap(0, 0, 2, "(ptr)"), 10),
                handle,
                vec![],
                Some(&t8),
            ),
            (
                "Option<ptr> with its tags swapped",
                raw(niche(0, 1, 0, "(ptr)"), 1),
                vec![],
                vec![option_of(Ty::Ptr, trust_ir::ty::EnumTagRepr::U64)],
                Some(&t8),
            ),
            (
                "Option<ptr> over discriminants [1, 0]",
                raw(niche(0, 0, 1, "(ptr)"), 1),
                vec![],
                vec![swapped_tags],
                Some(&t8),
            ),
            (
                "Option<ptr> over discriminants [5, 6]",
                raw(niche(0, 0, 1, "(ptr)"), 1),
                vec![],
                vec![discriminants],
                Some(&t8),
            ),
            (
                "Option<ptr> whose none word is 1",
                raw(niche(0, 0, 1, "(ptr)"), 1),
                vec![],
                vec![none_at_one],
                Some(&t8),
            ),
        ];
        let mut blind = Vec::new();
        for (name, row, structs, enums, tgt) in cases {
            let agg = row.key().0;
            let images =
                reference::reference_images(&probe_of(&enums, &structs, tgt), agg, row.raw, &[])
                    .unwrap_or_else(|e| panic!("{name}: the reference cannot run it: {e}"));
            let rows = [row];
            let tells: Vec<String> = images
                .iter()
                .filter(|(w, want)| {
                    !reference::load_view(&rows, &rows[0].image(), Img::Word(*w)).agrees(want)
                })
                .map(|(w, _)| format!("{w:#x}"))
                .collect();
            if tells.is_empty() {
                blind.push(name);
            }
        }
        assert!(
            blind.is_empty(),
            "the gate's probe words cannot tell these WRONG rows from the reference, so the \
             reference gate would mint them wherever a structural clause does not refuse them \
             first: {blind:?}"
        );
    }

    /// A struct of `fields` at raw `id`, `size`/`align` bytes, every field at
    /// byte 0 (one live field beside zero-sized markers).
    fn laid(id: u32, name: &str, fields: Vec<Ty>, size: u64, align: u64) -> StructDef {
        let mut s = struct_def(id, name, fields, size);
        s.align = Some(align);
        s
    }

    /// One generated case: a root type over the tables, and the target.
    struct Case {
        name: String,
        root: Ty,
        structs: Vec<StructDef>,
        enums: Vec<EnumDef>,
        bits: u32,
        target: Option<trust_ir::TargetInfo>,
    }

    /// THE DIFFERENTIAL TEST. Generated layouts -- explicit and swapped
    /// discriminants, both niche arrangements, the pointer lane and a byte
    /// lane, wrapper chains up to three deep ending in a pointer, a typed
    /// pointer, a `char` pointer, a `char`, a pointer-width integer or an
    /// inner `Option`, beside no marker, a field-less ZST before or after the
    /// word, or a zero-sized marker WITH a field; target-less, x86_64 and
    /// wasm32 -- each projected and derived. Every row the projector MINTS is
    /// then decoded by the Clean view and by trust-ir's reference interpreter
    /// at the gate's probe words and 24 more, and the two must agree on every
    /// one: a row that cannot match the reference was refused, not minted.
    /// The tally at the end keeps the test from passing vacuously.
    #[test]
    fn every_minted_row_decodes_as_the_reference_on_generated_layouts() {
        let targets: [(&str, Option<trust_ir::TargetInfo>, u32); 3] = [
            ("none", None, 64),
            ("x86_64", Some(target(8)), 64),
            ("wasm32", Some(wasm32()), 32),
        ];
        let mut cases: Vec<Case> = Vec::new();
        for (label, tgt, bits) in &targets {
            let word = u64::from(*bits / 8);
            let lane = if *bits == 64 {
                trust_ir::ty::EnumTagRepr::U64
            } else {
                trust_ir::ty::EnumTagRepr::U32
            };
            let int = if *bits == 64 { Ty::U64 } else { Ty::U32 };
            let inners: [(&str, Ty); 6] = [
                ("ptr", Ty::Ptr),
                ("*const u8", Ty::PtrConst(Box::new(Ty::U8))),
                ("*const char", Ty::PtrConst(Box::new(Ty::Char))),
                ("char", Ty::Char),
                ("int", int),
                ("Option<ptr>", Ty::Enum(EnumId::new(20))),
            ];
            let markers = ["", "zst-before", "zst-after", "zst-with-field"];
            let option = |id: u32,
                          payload: Ty,
                          discs: &[Option<i128>],
                          swapped: bool,
                          lane: trust_ir::ty::EnumTagRepr| {
                let (variants, untagged, niche) = if swapped {
                    (vec![vec![payload], vec![]], 0, 1)
                } else {
                    (vec![vec![], vec![payload]], 1, 0)
                };
                let offsets = if swapped {
                    vec![vec![0], vec![]]
                } else {
                    vec![vec![], vec![0]]
                };
                let mut def = enum_with(
                    id,
                    trust_ir::ty::EnumTagEncoding::Niche {
                        untagged_variant: untagged,
                        niche_variants_start: niche,
                        niche_variants_end: niche,
                        niche_start: 0,
                        niche_offset: 0,
                        niche_ty: lane,
                    },
                    variants,
                    word,
                    offsets,
                );
                def.layout.as_mut().expect("a descriptor").align = word;
                def.discriminants = discs.to_vec();
                def
            };
            for (inner_name, inner) in &inners {
                for marker in markers {
                    for depth in 0..=3usize {
                        // The chain: struct 10 wraps struct 11 wraps ... wraps
                        // the inner type; markers are structs 30 and 31.
                        let mut structs = vec![
                            laid(30, "PhantomData", vec![], 0, 1),
                            laid(31, "Invariant", vec![Ty::Struct(StructId::new(30))], 0, 1),
                        ];
                        let mut enums = vec![option(20, Ty::Ptr, &[], false, lane)];
                        for k in 0..depth {
                            let id = 10 + u32::try_from(k).expect("small");
                            let field = if k + 1 == depth {
                                inner.clone()
                            } else {
                                Ty::Struct(StructId::new(id + 1))
                            };
                            let fields = match marker {
                                "zst-before" => vec![Ty::Struct(StructId::new(30)), field],
                                "zst-after" => vec![field, Ty::Struct(StructId::new(30))],
                                "zst-with-field" => vec![field, Ty::Struct(StructId::new(31))],
                                _ => vec![field],
                            };
                            structs.push(laid(id, "W", fields, word, word));
                        }
                        let chain = if depth == 0 {
                            inner.clone()
                        } else {
                            Ty::Struct(StructId::new(10))
                        };
                        if depth > 0 {
                            cases.push(Case {
                                name: format!("{label} {marker} W^{depth}<{inner_name}>"),
                                root: chain.clone(),
                                structs: structs.clone(),
                                enums: enums.clone(),
                                bits: *bits,
                                target: tgt.clone(),
                            });
                        }
                        let discs: [&[Option<i128>]; 4] = [
                            &[],
                            &[Some(0), Some(1)],
                            &[Some(5), Some(6)],
                            &[Some(1), Some(0)],
                        ];
                        for d in discs {
                            for swapped in [false, true] {
                                let mut enums = enums.clone();
                                enums.push(option(1, chain.clone(), d, swapped, lane));
                                cases.push(Case {
                                    name: format!(
                                        "{label} {marker} Option{d:?}{}<W^{depth}<{inner_name}>>",
                                        if swapped { " swapped" } else { "" }
                                    ),
                                    root: Ty::Enum(EnumId::new(1)),
                                    structs: structs.clone(),
                                    enums,
                                    bits: *bits,
                                    target: tgt.clone(),
                                });
                            }
                        }
                        enums.push(option(1, chain, &[], false, trust_ir::ty::EnumTagRepr::U8));
                        cases.push(Case {
                            name: format!(
                                "{label} {marker} Option<u8 lane><W^{depth}<{inner_name}>>"
                            ),
                            root: Ty::Enum(EnumId::new(1)),
                            structs,
                            enums,
                            bits: *bits,
                            target: tgt.clone(),
                        });
                    }
                }
            }
        }
        // 24 extra words per row, from a fixed LCG: not the gate's own.
        let mut seed: u128 = 0x9e37_79b9_7f4a_7c15;
        let extra: Vec<u128> = (0..24)
            .map(|_| {
                seed = seed
                    .wrapping_mul(6_364_136_223_846_793_005)
                    .wrapping_add(1_442_695_040_888_963_407);
                seed >> 17
            })
            .collect();
        let (mut minted, mut refused_rows) = (0usize, 0usize);
        let mut outcome: BTreeMap<String, (usize, Vec<String>)> = BTreeMap::new();
        for case in &cases {
            let mut module = trust_ir::Module::new("primary");
            module.functions.push(function(
                0,
                "a",
                Some(vec![Inst::Undef {
                    ty: case.root.clone(),
                }]),
            ));
            module.structs = case.structs.clone();
            module.enums = case.enums.clone();
            module.target_info = case.target.clone();
            let chain: Vec<&trust_ir::Function> = module.functions.iter().collect();
            let (_, mut p) = project_merged(&module, &[], &chain, Some(case.bits))
                .unwrap_or_else(|e| panic!("{}: {e}", case.name));
            let (rows, refused) =
                derive_rows(&module, &[], &mut p).unwrap_or_else(|e| panic!("{}: {e}", case.name));
            for r in &rows {
                let images = reference::reference_images(
                    &probe_of(&module.enums, &module.structs, module.target_info.as_ref()),
                    r.key().0,
                    r.raw,
                    &extra,
                )
                .unwrap_or_else(|e| {
                    panic!("{}: a MINTED row the reference cannot run: {e}", case.name)
                });
                for (w, want) in images {
                    let got = reference::load_view(&rows, &r.image(), Img::Word(w));
                    assert_eq!(
                        got,
                        want,
                        "{}: the minted {} row for {}.{} images the word {w:#x} as {got}, the \
                         reference decodes {want}",
                        case.name,
                        r.kind(),
                        r.key().0.tag(),
                        r.raw
                    );
                }
            }
            minted += rows.len();
            refused_rows += refused.len();
            outcome.insert(case.name.clone(), (rows.len(), refused));
        }
        let get = |name: &str| {
            outcome
                .get(name)
                .unwrap_or_else(|| panic!("no generated case {name}"))
        };
        for tgt in ["none", "x86_64"] {
            // The committed shapes mint: Option<ptr>, and Option<Arc>-like
            // chains with a field-less marker beside the word.
            assert_eq!(get(&format!("{tgt}  Option[]<W^0<ptr>>")).0, 1);
            assert_eq!(
                get(&format!("{tgt} zst-after Option[]<W^2<*const u8>>")).0,
                3
            );
            assert_eq!(get(&format!("{tgt}  Option[] swapped<W^0<ptr>>")).0, 1);
            // The verifier's cases are refused.
            for refused in [
                format!("{tgt}  Option[Some(5), Some(6)]<W^0<ptr>>"),
                format!("{tgt}  Option[Some(1), Some(0)]<W^0<ptr>>"),
                format!("{tgt}  Option[]<W^2<*const char>>"),
                format!("{tgt} zst-with-field W^1<ptr>"),
            ] {
                let (n, why) = get(&refused);
                assert_eq!(*n, 0, "{refused}: {why:?}");
            }
        }
        assert_eq!(
            get("wasm32  Option[]<W^0<ptr>>").0,
            1,
            "a 32-bit niche over the 32-bit word mints"
        );
        assert!(
            minted >= 300 && refused_rows >= 300,
            "vacuity: {} cases, {minted} rows minted, {refused_rows} refused",
            cases.len()
        );
    }

    /// The refusal a niche descriptor with a RANGE of niched variants records
    /// is one sentence, not the line-wrapped literal ir_lzd's provenance
    /// committed (`is not a single` + eighteen spaces + `variant`).
    #[test]
    fn a_niche_range_refusal_reads_as_one_sentence() {
        let (_, refused) = encodings_of(
            trust_ir::ty::EnumTagEncoding::Niche {
                untagged_variant: 2,
                niche_variants_start: 0,
                niche_variants_end: 1,
                niche_start: 0,
                niche_offset: 0,
                niche_ty: trust_ir::ty::EnumTagRepr::U64,
            },
            vec![vec![], vec![], vec![Ty::Ptr]],
        );
        assert!(
            refused
                .iter()
                .any(|r| r.contains("niche variants 0..1 is not a single variant")),
            "{refused:?}"
        );
    }

    /// The command line pairs each `--join` with the `--merge` before it.
    #[test]
    fn take_merges_pairs_each_join_with_the_merge_it_follows() {
        let mut args: Vec<String> = [
            "a2project",
            "c.bin",
            "f",
            "out",
            "--merge",
            "one.bin",
            "--join",
            "m1",
            "--with",
            "g",
            "--merge",
            "two.bin",
            "--join",
            "m2",
            "--join",
            "m3",
        ]
        .iter()
        .map(|s| (*s).to_string())
        .collect();
        let merges = take_merges(&mut args);
        let got: Vec<(&str, Vec<&str>)> = merges
            .iter()
            .map(|m| {
                (
                    m.path.as_str(),
                    m.joins.iter().map(String::as_str).collect(),
                )
            })
            .collect();
        assert_eq!(
            got,
            vec![("one.bin", vec!["m1"]), ("two.bin", vec!["m2", "m3"])]
        );
        assert_eq!(args, ["a2project", "c.bin", "f", "out", "--with", "g"]);
    }

    #[test]
    #[should_panic(expected = "precedes every --merge")]
    fn a_join_before_every_merge_is_refused() {
        let mut args: Vec<String> = ["a2project", "--join", "m1", "--merge", "one.bin"]
            .iter()
            .map(|s| (*s).to_string())
            .collect();
        take_merges(&mut args);
    }

    /// A member id past its own artifact's functions is refused naming THAT
    /// artifact. `retarget` only asks whether SOME function has the id, which
    /// a later artifact's body would answer once every merge is folded.
    #[test]
    #[should_panic(expected = "is not a function of --merge one.bin")]
    fn a_join_member_outside_its_artifact_is_refused() {
        let mut module = trust_ir::Module::new("primary");
        module
            .functions
            .push(function(0, "caller", Some(vec![call(1)])));
        module.functions.push(function(1, "decl1", None));
        merge_all(
            &mut module,
            vec![
                MergeInput {
                    path: "one.bin".into(),
                    module: artifact("body1", "one::E"),
                    joins: vec![("one.manifest.json".into(), manifest(1, 1))],
                },
                MergeInput {
                    path: "two.bin".into(),
                    module: artifact("body2", "two::E"),
                    joins: vec![],
                },
            ],
        );
    }

    /// Control: a constant that names no function still merges.
    #[test]
    fn fold_in_merges_a_function_free_constant() {
        let mut primary = trust_ir::Module::new("primary");
        let shift = fold_in(
            &mut primary,
            artifact_with_const(Constant::Int(7)),
            "sidecar.bin",
        );
        assert_eq!(shift, 0, "an empty primary shifts nothing");
        assert_eq!(primary.functions.len(), 1);
    }

    /// trust-ir v47 (`Inst::Drop`, the crystal lane's wave-DS, landed on
    /// trust-ir main): this reader has no image for a destructor run, so the
    /// projection REFUSES it by name. The merge relocation, whose job is only
    /// to move `FuncId`s, carries it through untouched -- it names no function
    /// and no global -- and the projection is what refuses it.
    #[test]
    fn a_drop_is_refused_by_name_and_merges_unrelocated() {
        let drop_inst = Inst::Drop {
            ty: Ty::I64,
            ptr: ValueId::new(0),
        };
        let err = super::Projector::default()
            .inst(&drop_inst)
            .expect_err("a Drop has no IRInst image");
        assert!(err.contains("trust_ir::Inst::Drop"), "{err}");

        let mut merged = trust_ir::Module::new("merged");
        merged
            .functions
            .push(function(0, "f", Some(vec![drop_inst.clone()])));
        let mut primary = trust_ir::Module::new("primary");
        fold_in(&mut primary, merged, "sidecar.bin");
        assert_eq!(
            primary.functions[0].blocks[0].body[0].inst, drop_inst,
            "the relocation must carry the Drop through unchanged"
        );
        // Control: the instruction beside it in the same position projects.
        assert_eq!(
            super::Projector::default()
                .inst(&Inst::Return { values: vec![] })
                .expect("a Return has an IRInst image"),
            "(ret (vals))"
        );
    }

    /// verifier r11v: `ops::cc` was `c as u32`, which gave every calling
    /// convention -- the seven trust-ir added in wire v45 included, `CUnwind`
    /// among them -- a number by its discriminant, with no classification, and
    /// the typed scan did not read a cast. The five conventions Clean's text
    /// reader names keep the wire tag they have always imaged to; every other
    /// one is refused by name.
    #[test]
    fn a_calling_convention_clean_does_not_name_is_refused() {
        use trust_ir::CallingConv as K;
        let call = |calling_conv| Inst::CallIndirect {
            callee: ValueId::new(0),
            sig: FuncTyId::new(0),
            args: vec![],
            calling_conv,
        };
        // `ALL` is in wire-tag order; the five before v45 lead it.
        assert_eq!(
            format!("{:?}", &K::ALL[..5]),
            "[C, Fast, Cold, Rust, Swift]"
        );
        assert_eq!(
            K::ALL.len(),
            12,
            "five conventions and the seven of wire v45"
        );
        for (tag, conv) in K::ALL.into_iter().enumerate() {
            let got = super::Projector::default().inst(&call(conv));
            if tag < 5 {
                assert_eq!(
                    got,
                    Ok(format!("(callindirect 0 0 (args) {tag})")),
                    "{conv:?}"
                );
            } else {
                let err = got.expect_err("a v45 convention has no IR image");
                assert!(err.contains(&format!("{conv:?}")), "{err}");
            }
        }
    }

    /// trust-ir v49 (`Constant::Uninit`, an UNWRITTEN struct/tuple lane): no
    /// Clean image is decided, so every position this reader reads a constant
    /// from REFUSES it by name -- a bare constant, a lane of an aggregate, and a
    /// global initializer -- and it is never mistaken for a function name by
    /// the merge. The same aggregate with the lane written projects.
    #[test]
    fn an_unwritten_lane_is_refused_by_name_in_every_position() {
        let mut p = super::Projector::default();
        let bare = p
            .cst(&Constant::Uninit)
            .expect_err("a bare unwritten lane has no IRConst image");
        assert!(bare.contains("Constant::Uninit"), "{bare}");
        let lane = p
            .cst(&Constant::Aggregate(vec![
                Constant::Int(1),
                Constant::Uninit,
            ]))
            .expect_err("an aggregate with an unwritten lane has no IRConst image");
        assert!(lane.contains("Constant::Uninit"), "{lane}");
        // The lane's `global_init` pairs the initializer with the global's
        // TYPE (crystal plan step 18); an unwritten lane is refused at an
        // array type and at a struct type alike.
        let module = trust_ir::Module::new("m");
        for ty in [
            Ty::Array(trust_ir::value::TyId::new(0), 1),
            Ty::Struct(trust_ir::value::StructId::new(0)),
        ] {
            let global = p
                .global_init(&module, &ty, &Constant::Uninit)
                .expect_err("an unwritten lane never initializes a global");
            assert!(global.contains("Uninit"), "{global}");
        }
        // Nor is it an element of a struct/tuple global's initializer.
        let elem = p
            .global_elem(&module, &Constant::Uninit)
            .expect_err("an unwritten lane is no global element");
        assert!(elem.contains("Constant::Uninit"), "{elem}");
        assert!(!super::constant_may_name_function(&Constant::Uninit));
        assert!(!super::constant_may_name_function(&Constant::Aggregate(
            vec![Constant::Int(1), Constant::Uninit]
        )));
        // Control: the lane written.
        assert_eq!(
            p.cst(&Constant::Aggregate(vec![
                Constant::Int(1),
                Constant::Int(2)
            ]))
            .expect("a written aggregate projects"),
            "(agg (int 1) (int 2))"
        );
    }

    /// The reference half: an unwritten lane is not a value, so its image is
    /// OPAQUE and never equals a word the Clean view can produce -- a probe
    /// that met one reads as a disagreement, not as a pass.
    #[test]
    fn an_unwritten_lane_images_as_opaque_and_equals_no_word() {
        let v = trust_ir::InterpretValue {
            ty: Ty::I64,
            kind: trust_ir::InterpretValueKind::Uninit,
        };
        let img = reference::image(&v);
        // Exact equality, not a `matches!` (its expansion is a catch-all this
        // crate's lint run cannot see).
        assert_eq!(img, Img::Opaque(String::from("unwritten i64 lane")));
        assert_ne!(img, Img::Word(0));
    }

    /// trust-ir v50 (`Constant::Splat`, the constant-size uniform array): no
    /// Clean image is decided, so every position this reader reads a constant
    /// from REFUSES it by name -- a bare constant, a lane of an aggregate, and
    /// a global initializer. The refusal reads the variant and nothing else,
    /// so a length of 2 and a length of `u64::MAX` get the SAME answer: a
    /// reader that walked the lanes would not return from the second, and one
    /// that expanded them would not fit it in memory.
    #[test]
    fn a_splat_is_refused_by_name_whatever_its_length() {
        let splat = |elem: Constant, len| Constant::Splat {
            elem: Box::new(elem),
            len,
        };
        let (small, huge) = (
            splat(Constant::Int(0), 2),
            splat(Constant::Int(0), u64::MAX),
        );
        let mut p = super::Projector::default();
        let bare_small = p.cst(&small).expect_err("a splat has no IRConst image");
        let bare_huge = p.cst(&huge).expect_err("a splat has no IRConst image");
        assert!(bare_small.contains("Constant::Splat"), "{bare_small}");
        assert_eq!(
            bare_small, bare_huge,
            "the refusal must not depend on the length"
        );
        let lane = p
            .cst(&Constant::Aggregate(vec![Constant::Int(1), huge.clone()]))
            .expect_err("an aggregate with a splat lane has no IRConst image");
        assert_eq!(lane, bare_huge);
        // The lane's `global_init` pairs the initializer with the global's
        // TYPE (crystal plan step 18); a splat is refused at an array type, the
        // one a well-formed splat global has.
        let module = trust_ir::Module::new("m");
        let array_ty = Ty::Array(trust_ir::value::TyId::new(0), 2);
        let global_small = p
            .global_init(&module, &array_ty, &small)
            .expect_err("a splat has no global-initializer image");
        let global_huge = p
            .global_init(&module, &array_ty, &huge)
            .expect_err("a splat has no global-initializer image");
        assert!(global_small.contains("of the form Splat"), "{global_small}");
        assert_eq!(
            global_small, global_huge,
            "the refusal must not depend on the length"
        );
        // The merge classification: every lane IS the element, so the element
        // answers for all of them, at any length.
        assert!(!super::constant_may_name_function(&huge));
        assert!(super::constant_may_name_function(&splat(
            Constant::FnDef(FuncId::new(0)),
            u64::MAX
        )));
        // Control: the list spelling in the same position still projects.
        assert_eq!(
            p.global_init(
                &module,
                &array_ty,
                &Constant::Array(vec![Constant::Int(1), Constant::Int(2)])
            )
            .expect("an `array[…]` initializer projects"),
            "(agg (int 1) (int 2))"
        );
    }

    /// A splat that names a function is refused by the merge at any length,
    /// exactly as its list spelling is.
    #[test]
    #[should_panic(expected = "carries a constant that may name a function")]
    fn fold_in_refuses_a_huge_splat_that_names_a_function() {
        let mut primary = trust_ir::Module::new("primary");
        fold_in(
            &mut primary,
            artifact_with_const(Constant::Splat {
                elem: Box::new(Constant::FnDef(FuncId::new(0))),
                len: u64::MAX,
            }),
            "sidecar.bin",
        );
    }

    /// trust-ir v50 (`Inst::ArraySplat`, the register twin of
    /// `Constant::Splat`): no IRInst image, so the projection REFUSES it by
    /// name without reading its length; the merge relocation carries it
    /// through untouched (a `Ty` and one `ValueId`, no function or global);
    /// and a `--join` does not read it as a call.
    #[test]
    fn an_array_splat_is_refused_by_name_and_merges_unrelocated() {
        let splat = |len| Inst::ArraySplat {
            ty: Ty::Array(trust_ir::value::TyId::new(0), len),
            value: ValueId::new(0),
        };
        let (small, huge) = (splat(1), splat(u64::MAX));
        let err_small = super::Projector::default()
            .inst(&small)
            .expect_err("an ArraySplat has no IRInst image");
        let err_huge = super::Projector::default()
            .inst(&huge)
            .expect_err("an ArraySplat has no IRInst image");
        assert!(
            err_small.contains("trust_ir::Inst::ArraySplat"),
            "{err_small}"
        );
        assert_eq!(
            err_small, err_huge,
            "the refusal must not depend on the length"
        );

        let mut merged = trust_ir::Module::new("merged");
        merged
            .functions
            .push(function(0, "f", Some(vec![huge.clone()])));
        let mut primary = trust_ir::Module::new("primary");
        fold_in(&mut primary, merged, "sidecar.bin");
        assert_eq!(
            primary.functions[0].blocks[0].body[0].inst, huge,
            "the relocation must carry the ArraySplat through unchanged"
        );
        let mut inst = huge.clone();
        assert_eq!(call_target(&mut inst), None, "an ArraySplat is not a call");
    }

    fn runtime_closure_body(with_closure: bool) -> trust_ir::Module {
        let mut module = trust_ir::Module::new("runtime_closure");
        for params in [vec![], vec![Ty::U32]] {
            module.func_types.push(trust_ir::FuncTy {
                params,
                returns: vec![Ty::U32],
                is_vararg: false,
                abi: None,
            });
        }
        module.closure_types.push(trust_ir::ClosureTy {
            func: FuncTyId::new(0),
            captures: vec![Ty::U32],
        });
        let mut block = trust_ir::Block::new(BlockId::new(0));
        block.body.push(
            trust_ir::InstrNode::new(Inst::Const {
                ty: Ty::U32,
                value: Constant::Int(7),
            })
            .with_result(ValueId::new(0)),
        );
        if with_closure {
            block.body.push(
                trust_ir::InstrNode::new(Inst::MakeClosure {
                    ty: trust_ir::ClosureTyId::new(0),
                    func: FuncId::new(1),
                    captures: vec![ValueId::new(0)],
                })
                .with_result(ValueId::new(1)),
            );
        }
        block.body.push(trust_ir::InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        }));
        let mut root =
            trust_ir::Function::new(FuncId::new(0), "root", FuncTyId::new(0), BlockId::new(0));
        root.blocks.push(block);
        module.try_add_function(root).expect("root fixture");
        let mut target =
            trust_ir::Function::new(FuncId::new(1), "target", FuncTyId::new(1), BlockId::new(0));
        let mut block = trust_ir::Block::new(BlockId::new(0));
        block.params.push((ValueId::new(0), Ty::U32));
        block.body.push(trust_ir::InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        }));
        target.blocks.push(block);
        module.try_add_function(target).expect("target fixture");
        module
    }

    #[test]
    fn runtime_closure_is_refused_even_when_its_result_is_unused() {
        let scalar = runtime_closure_body(false);
        let closure = runtime_closure_body(true);
        for module in [&scalar, &closure] {
            let outcome = trust_ir::Interpreter::with_module(module)
                .execute_func(FuncId::new(0), [])
                .expect("valid fixture executes");
            assert_eq!(outcome.returns[0].as_int().expect("U32").as_signed(), 7);
        }
        Projector::default()
            .project_chain(&scalar, &[&scalar.functions[0]])
            .expect("the scalar twin projects");
        for ptr_bitcast_identity in [false, true] {
            let error = Projector {
                ptr_bitcast_identity,
                ..Projector::default()
            }
            .project_chain(&closure, &[&closure.functions[0]])
            .expect_err("an unused runtime closure still has no image");
            assert!(error.contains("MakeClosure"), "{error}");
        }
        let mut constructor = closure.functions[0].blocks[0].body[1].inst.clone();
        assert_eq!(
            call_target(&mut constructor),
            None,
            "construction is not a call"
        );
        assert!(!super::inst_is_const_bool_false(&constructor));
    }

    #[test]
    #[should_panic(expected = "MakeClosure")]
    fn fold_in_refuses_a_runtime_closure_target() {
        fold_in(
            &mut trust_ir::Module::new("primary"),
            runtime_closure_body(true),
            "sidecar.bin",
        );
    }
}

/// Crystal decision memo §18: the three images this projector gained there, pinned on
/// synthetic bodies. Inline, because the projector is ONE source file
/// (`tests::the_projector_is_one_source_file`).
///
/// * D12: `bitcast ptr -> ptr` is `copy (ptr)`; every other bitcast keeps its cast image.
/// * A negative integer constant is its width-W bit pattern; a type with no width keeps the
///   refusal.
/// * An undefined-behaviour halt (the trust bridge's `assert false` sited by a "reaching `X` is
///   undefined behavior" obligation) is `unreachable` -- a halt E2's device refuses -- while a
///   PANIC halt, the same instructions sited by the panic wording, stays the sanctioned `assert`.
///   The SAME synthetic body, projected under the two wordings, differs in exactly that node.
#[cfg(test)]
mod d12_tests {
    use super::{ub_halt_sites_of, Projector};
    use trust_ir::constant::Constant;
    use trust_ir::inst::{CastOp, Inst};
    use trust_ir::ty::Ty;
    use trust_ir::value::{BlockId, FuncId, FuncTyId, ProofId, ValueId};

    fn node(inst: Inst, result: Option<u32>) -> trust_ir::InstrNode {
        let n = trust_ir::InstrNode::new(inst);
        match result {
            Some(r) => n.with_result(ValueId::new(r)),
            None => n,
        }
    }

    fn nodes(core: &str) -> Vec<&str> {
        core.lines()
            .map(str::trim)
            .filter(|l| l.starts_with("(node "))
            .collect()
    }

    #[test]
    fn d12_a_ptr_to_ptr_bitcast_is_a_copy_and_no_other_bitcast_is() {
        let bitcast = |src: Ty, dst: Ty| {
            node(
                Inst::Cast {
                    op: CastOp::Bitcast,
                    src_ty: src,
                    dst_ty: dst,
                    operand: ValueId::new(4),
                },
                Some(5),
            )
        };
        // Off by default: every committed chain re-projects byte-identical.
        let mut off = Projector::default();
        assert_eq!(
            off.ptr_bitcast_identity_image(&bitcast(Ty::Ptr, Ty::Ptr))
                .unwrap(),
            None
        );
        let mut p = Projector {
            ptr_bitcast_identity: true,
            ..Projector::default()
        };
        assert_eq!(
            p.ptr_bitcast_identity_image(&bitcast(Ty::Ptr, Ty::Ptr))
                .unwrap(),
            Some(vec!["(node (results 5) (copy (ptr) 4))".to_string()])
        );
        assert_eq!(p.ptr_bitcast_identities, 1);
        // A bitcast between different types, or two identical non-pointer types, is not D12's.
        for (s, d) in [
            (Ty::Ptr, Ty::I64),
            (Ty::I64, Ty::Ptr),
            (Ty::I32, Ty::U32),
            (Ty::U64, Ty::U64),
        ] {
            assert_eq!(p.ptr_bitcast_identity_image(&bitcast(s, d)).unwrap(), None);
        }
        // PtrToPtr is its own cast with its own EvalIR arm; D12 does not touch it.
        let ptrtoptr = node(
            Inst::Cast {
                op: CastOp::PtrToPtr,
                src_ty: Ty::Ptr,
                dst_ty: Ty::Ptr,
                operand: ValueId::new(4),
            },
            Some(5),
        );
        assert_eq!(p.ptr_bitcast_identity_image(&ptrtoptr).unwrap(), None);
        assert_eq!(p.ptr_bitcast_identities, 1);
    }

    #[test]
    fn a_negative_int_constant_is_its_width_bit_pattern() {
        let c = |ty: Ty, v: i128| {
            node(
                Inst::Const {
                    ty,
                    value: Constant::Int(v),
                },
                Some(1),
            )
        };
        let mut p = Projector {
            usize_bits: Some(64),
            ..Projector::default()
        };
        for (ty, v, want) in [
            (
                Ty::I64,
                -1,
                "(node (results 1) (const (int 64) (int 18446744073709551615)))",
            ),
            (Ty::I8, -128, "(node (results 1) (const (int 8) (int 128)))"),
            (
                Ty::I32,
                -7,
                "(node (results 1) (const (int 32) (int 4294967289)))",
            ),
            (Ty::U8, -1, "(node (results 1) (const (uint 8) (int 255)))"),
            (
                Ty::Isize,
                -2,
                "(node (results 1) (const (int 64) (int 18446744073709551614)))",
            ),
            (
                Ty::I128,
                -1,
                "(node (results 1) (const (int 128) (int 340282366920938463463374607431768211455)))",
            ),
        ] {
            assert_eq!(
                p.negative_int_const_image(&c(ty, v)).unwrap(),
                Some(vec![want.to_string()])
            );
        }
        assert_eq!(p.negative_int_images, 6);
        // Non-negative constants are the ordinary arm's; a type with no width is not imaged here.
        assert_eq!(p.negative_int_const_image(&c(Ty::I64, 0)).unwrap(), None);
        assert_eq!(p.negative_int_const_image(&c(Ty::Bool, -1)).unwrap(), None);
        assert_eq!(p.negative_int_const_image(&c(Ty::Ptr, -1)).unwrap(), None);
        // `isize` without the pinned width stays the ordinary arm's refusal.
        let mut unpinned = Projector::default();
        assert_eq!(
            unpinned
                .negative_int_const_image(&c(Ty::Isize, -1))
                .unwrap(),
            None
        );
    }

    const UB: &str =
        "reaching `core::hint::unreachable_unchecked::precondition_check` is undefined \
                      behavior; this program point must be proven unreachable";
    const PANIC: &str = "panic call `core::panicking::panic` must be unreachable";

    /// `bb0: %0 = const bool false; assert %0; unreachable`, with one obligation of wording `desc`
    /// sited at instruction `k` of that block (the bridge's `add_obligation_for_last_inst`).
    fn halt_body(desc: &str, k: Option<u32>) -> trust_ir::Module {
        let mut b = trust_ir::Block::new(BlockId::new(0));
        b.body.push(node(
            Inst::Const {
                ty: Ty::Bool,
                value: Constant::Bool(false),
            },
            Some(0),
        ));
        b.body.push(node(
            Inst::Assert {
                cond: ValueId::new(0),
                kind: trust_ir::AssertKind::Unspecified,
                site: None,
            },
            None,
        ));
        b.body.push(node(Inst::Unreachable, None));
        let mut f =
            trust_ir::Function::new(FuncId::new(0), "halts", FuncTyId::new(0), BlockId::new(0));
        f.blocks.push(b);
        let mut m = trust_ir::Module::new("sidecar");
        m.functions.push(f);
        let mut o = trust_ir::ProofObligation::new(
            ProofId::new(0),
            trust_ir::ObligationKind::PanicFreedom,
            trust_ir::ProofStatus::Pending,
            desc,
        )
        .with_function(FuncId::new(0));
        if let Some(k) = k {
            o = o.with_site(trust_ir::ObligationSite::new(
                FuncId::new(0),
                BlockId::new(0),
                k,
            ));
        }
        m.proof_obligations.push(o);
        m
    }

    fn project(m: &trust_ir::Module) -> Result<(String, u32), String> {
        let (sites, unsited) = ub_halt_sites_of(m, 0);
        let mut p = Projector {
            ub_halt_sites: sites,
            ub_unsited: unsited,
            ..Projector::default()
        };
        let core = p.project_chain(m, &[&m.functions[0]])?;
        Ok((core, p.ub_halt_images))
    }

    /// THE SYNTHETIC BODY. Its UB-sited halt projects to `unreachable` (which halts `ub
    /// unreachable`, refused by `ir_sanctioned`), and the SAME body with the PANIC wording projects
    /// to the `assert` (which halts `ub assert_failed`, admitted as a sanctioned panic). Nothing else
    /// in the two projections differs.
    #[test]
    fn a_ub_halt_is_unreachable_and_a_panic_halt_stays_the_sanctioned_assert() {
        let (ub, n) = project(&halt_body(UB, Some(1))).expect("a sited UB halt projects");
        assert_eq!(n, 1);
        assert_eq!(
            nodes(&ub),
            [
                "(node (results 0) (const (bool) (bool false)))",
                "(node (results) (unreachable))",
                "(node (results) (unreachable))",
            ],
            "{ub}"
        );
        let (panic, n) = project(&halt_body(PANIC, Some(1))).expect("a panic halt projects");
        assert_eq!(n, 0);
        assert_eq!(
            nodes(&panic),
            [
                "(node (results 0) (const (bool) (bool false)))",
                "(node (results) (assert 0))",
                "(node (results) (unreachable))",
            ],
            "{panic}"
        );
        let differing: Vec<(&str, &str)> = nodes(&ub)
            .into_iter()
            .zip(nodes(&panic))
            .filter(|(a, b)| a != b)
            .collect();
        assert_eq!(
            differing,
            [(
                "(node (results) (unreachable))",
                "(node (results) (assert 0))"
            )]
        );
    }

    /// Fail-closed: a UB obligation sited anywhere but a halting assert, and one with no site, have
    /// no image -- never the sanctioned `assert`.
    #[test]
    fn a_ub_halt_that_cannot_be_located_is_refused() {
        let err = project(&halt_body(UB, Some(0))).expect_err("sited at the const, not the assert");
        assert!(
            err.contains("not an `assert` of a `const bool false`"),
            "{err}"
        );
        let err = project(&halt_body(UB, Some(2))).expect_err("sited at the terminator");
        assert!(err.contains("not an `assert`"), "{err}");
        let err = project(&halt_body(UB, None)).expect_err("no site");
        assert!(err.contains("with no site"), "{err}");
        // The wording must be the bridge's exactly: a near miss is not a UB halt, so the body is
        // projected as the sanctioned assert it looks like (and link 3 then keys no `ub-terminal`).
        let near =
            "reaching `x` is undefined behaviour; this program point must be proven unreachable";
        let (core, n) = project(&halt_body(near, Some(1))).expect("not a UB wording");
        assert_eq!(n, 0);
        assert!(core.contains("(assert 0)"), "{core}");
    }

    /// A MERGED artifact's UB halt site is its own obligation's, relocated by the shift its
    /// functions got (`merge_all` -> `Merged::ub_sites` -> `project_merged_certified`). The
    /// primary's body sits at the merged obligation's UNRELOCATED site `(0, 0, 1)` and carries
    /// the panic wording, so a site left unshifted would image the primary's sanctioned `assert`
    /// and leave the merged UB halt an `assert`: both halves are asserted.
    #[test]
    fn a_merged_artifacts_ub_halt_is_relocated_with_its_body() {
        let mut module = halt_body(PANIC, Some(1));
        module.functions[0].name = "root".into();
        let inputs = vec![super::MergeInput {
            path: "ub.bin".into(),
            module: halt_body(UB, Some(1)),
            joins: vec![],
        }];
        let (merged, _) = super::merge_all(&mut module, inputs);
        assert_eq!(merged.len(), 1);
        assert_eq!(
            merged[0].shift, 1,
            "the merged body lands above the primary's"
        );
        let chain: Vec<&trust_ir::Function> = module.functions.iter().collect();
        let (core, p) =
            super::project_merged(&module, &merged, &chain, None).expect("both bodies project");
        assert_eq!(p.ub_halt_images, 1);
        assert_eq!(
            nodes(&core),
            [
                "(node (results 0) (const (bool) (bool false)))",
                "(node (results) (assert 0))",
                "(node (results) (unreachable))",
                "(node (results 0) (const (bool) (bool false)))",
                "(node (results) (unreachable))",
                "(node (results) (unreachable))",
            ],
            "{core}"
        );
    }
}

/// Crystal E5 (decision memo §23): the fat-pointer kinds the M0 producer emits have images, and
/// D14's vtable read is CERTIFIED against the vtable image; every other use of a vtable word, a
/// non-canonical metadata type and a constant at one of the kinds are refused BY NAME.
#[cfg(test)]
mod m0_tests {
    use super::{d14_vtable_certify, Projector};
    use trust_ir::constant::Constant;
    use trust_ir::inst::{CastOp, Inst};
    use trust_ir::ty::Ty;
    use trust_ir::value::{BlockId, FuncId, FuncTyId, TyId, ValueId};
    use trust_ir::FatPtrKind;

    fn p64() -> Projector {
        Projector {
            usize_bits: Some(64),
            ..Projector::default()
        }
    }

    #[test]
    fn addressable_storage_has_no_initialized_value_image() {
        let mut p = p64();
        assert_eq!(p.ty(&Ty::U64).unwrap(), "(uint 64)");
        for (size, align) in [(0, 1), (8, 8), (32, 16)] {
            let storage = Ty::Storage(trust_ir::StorageLayout::new(size, align));
            let refusal = p.ty(&storage).unwrap_err();
            assert!(refusal.contains("no Clean IRTy image"), "{refusal}");
            assert!(refusal.contains("Storage"), "{refusal}");
            assert!(!super::is_zst(&storage, &[]));
        }
    }

    #[test]
    fn each_m0_fat_kind_has_its_e5_image() {
        let mut p = Projector::default();
        for (kind, image) in [
            (FatPtrKind::ContainerLen, "(containerlen)"),
            (FatPtrKind::ContainerVtable, "(containervtable)"),
            (FatPtrKind::TraitObject { trait_id: 7 }, "(fatdyn 7)"),
            (
                FatPtrKind::TraitObject {
                    trait_id: 265_360_036,
                },
                "(fatdyn 265360036)",
            ),
        ] {
            assert_eq!(p.ty(&Ty::FatPtr(kind)).expect("an M0 kind images"), image);
        }
        // Controls: `Str` keeps its image, distinct from all three; `Slice` keeps the generic
        // refusal, and nothing else.
        assert_eq!(
            p.ty(&Ty::FatPtr(FatPtrKind::Str)).expect("str images"),
            "(fatptr (uint 8))"
        );
        let slice = p
            .ty(&Ty::FatPtr(FatPtrKind::Slice(TyId::new(0))))
            .expect_err("a slice has no image");
        assert_eq!(
            slice,
            "no Clean IRTy image for trust_ir::Ty::FatPtr(Slice(TyId(0)))"
        );
    }

    /// The knobs of [`vtable_body`], one per way a body can use a vtable word.
    #[derive(Clone)]
    struct Shape {
        kind: FatPtrKind,
        /// copy/bitcast hops between the metadata and the gep
        hops: usize,
        /// load through the metadata (the vtable) rather than the data pointer
        from_vtable: bool,
        /// the gep's byte offset
        offset: i128,
        /// the load's type
        load_ty: Ty,
        /// the declared metadata type
        meta_ty: Ty,
        /// a trailing use of the vtable word itself
        tail: Tail,
    }

    #[derive(Clone, Copy, PartialEq, Eq)]
    enum Tail {
        /// `ptr_from_parts fatptr<dyn.3> ptr %2, ptr %1`: D14's rebuild over the same vtable
        Rebuild,
        /// `store usize %5, ptr %1`: a write through the vtable word
        Store,
        /// `ret %1`: the vtable word escapes
        Escape,
    }

    fn d14() -> Shape {
        Shape {
            kind: FatPtrKind::ContainerVtable,
            hops: 0,
            from_vtable: true,
            offset: 16,
            load_ty: Ty::Usize,
            meta_ty: Ty::Ptr,
            tail: Tail::Rebuild,
        }
    }

    /// `bb0(%0)`: `%1 = ptr_metadata <kind> %0 to <meta>`, `%2 = ptr_data`, the hops, `%3 = const
    /// i64 <offset>`, `%4 = gep i8`, `%5 = load <ty>`, then the tail: D14's align read, as the
    /// bridge emits it, when every knob is `d14()`'s.
    fn vtable_body(sh: Shape) -> trust_ir::Module {
        let v = ValueId::new;
        let mut b = trust_ir::Block::new(BlockId::new(0));
        b.params = vec![(v(0), Ty::FatPtr(sh.kind))];
        let mut push = |inst: Inst, r: Option<u32>| {
            let node = trust_ir::InstrNode::new(inst);
            b.body.push(match r {
                Some(r) => node.with_result(v(r)),
                None => node,
            })
        };
        push(
            Inst::PtrMetadata {
                ptr_ty: Ty::FatPtr(sh.kind),
                metadata_ty: sh.meta_ty.clone(),
                ptr: v(0),
            },
            Some(1),
        );
        push(
            Inst::PtrData {
                ptr_ty: Ty::FatPtr(sh.kind),
                ptr: v(0),
            },
            Some(2),
        );
        let mut cur = if sh.from_vtable { 1 } else { 2 };
        for h in 0..sh.hops {
            let r = 10 + u32::try_from(h).expect("few hops");
            let inst = if h % 2 == 0 {
                Inst::Copy {
                    ty: Ty::Ptr,
                    operand: v(cur),
                }
            } else {
                Inst::Cast {
                    op: CastOp::Bitcast,
                    src_ty: Ty::Ptr,
                    dst_ty: Ty::Ptr,
                    operand: v(cur),
                }
            };
            push(inst, Some(r));
            cur = r;
        }
        push(
            Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(sh.offset),
            },
            Some(3),
        );
        push(
            Inst::GEP {
                pointee_ty: Ty::I8,
                base: v(cur),
                indices: vec![v(3)],
                inbounds: true,
            },
            Some(4),
        );
        push(
            Inst::Load {
                ty: sh.load_ty.clone(),
                ptr: v(4),
                volatile: false,
                align: None,
            },
            Some(5),
        );
        match sh.tail {
            Tail::Rebuild => {
                push(
                    Inst::PtrFromParts {
                        ptr_ty: Ty::FatPtr(FatPtrKind::TraitObject { trait_id: 3 }),
                        metadata_ty: Ty::Ptr,
                        data: v(2),
                        metadata: v(1),
                    },
                    Some(6),
                );
                push(Inst::Return { values: vec![v(5)] }, None);
            }
            Tail::Store => {
                push(
                    Inst::Store {
                        ty: Ty::Usize,
                        ptr: v(1),
                        value: v(5),
                        volatile: false,
                        align: None,
                    },
                    None,
                );
                push(Inst::Return { values: vec![v(5)] }, None);
            }
            Tail::Escape => push(Inst::Return { values: vec![v(1)] }, None),
        }
        let mut f = trust_ir::Function::new(
            FuncId::new(0),
            "reads_vtable",
            FuncTyId::new(0),
            BlockId::new(0),
        );
        f.blocks.push(b);
        let mut m = trust_ir::Module::new("sidecar");
        m.functions.push(f);
        m
    }

    fn project(p: &mut Projector, sh: Shape) -> Result<String, String> {
        let m = vtable_body(sh);
        p.project_chain(&m, &[&m.functions[0]])
    }

    #[test]
    fn the_d14_align_read_is_certified_and_projects_exactly() {
        let mut p = p64();
        let core = project(&mut p, d14()).expect("D14's align read has an image");
        for node in [
            "(ptrmetadata (containervtable) (ptr) 0)",
            "(ptrdata (containervtable) 0)",
            "(gep (int 8) 1 (idx 3) true)",
            "(load (uint 64) 4 false)",
            "(ptrfromparts (fatdyn 3) (ptr) 2 1)",
        ] {
            assert!(core.contains(node), "missing `{node}` in\n{core}");
        }
        assert_eq!(p.vtable_reads, 1);
        // The size slot (+8) is certified too, and so is the read through copy and cast hops,
        // from a trait object as from a dyn-tailed container.
        for sh in [
            Shape { offset: 8, ..d14() },
            Shape { hops: 3, ..d14() },
            Shape {
                kind: FatPtrKind::TraitObject { trait_id: 3 },
                hops: 2,
                ..d14()
            },
        ] {
            let m = vtable_body(sh);
            assert_eq!(
                d14_vtable_certify(&m.functions[0], Some(64))
                    .expect("certified")
                    .len(),
                1
            );
        }
        // A load through the DATA pointer is no vtable read at all.
        let data = vtable_body(Shape {
            from_vtable: false,
            ..d14()
        });
        assert_eq!(
            d14_vtable_certify(&data.functions[0], Some(64)).expect("no vtable read"),
            Vec::<(u32, u64)>::new()
        );
    }

    #[test]
    fn every_uncertified_use_of_a_vtable_word_is_refused_by_name() {
        for (sh, why) in [
            (
                Shape {
                    offset: 24,
                    ..d14()
                },
                "at byte offset 24",
            ),
            (Shape { offset: 4, ..d14() }, "at byte offset 4"),
            (
                Shape {
                    load_ty: Ty::U64,
                    ..d14()
                },
                "a load of the vtable word",
            ),
            (
                Shape {
                    tail: Tail::Store,
                    ..d14()
                },
                "is an operand of `Store`",
            ),
            (
                Shape {
                    tail: Tail::Escape,
                    ..d14()
                },
                "is an operand of `Return`",
            ),
        ] {
            let got = project(&mut p64(), sh).expect_err("an uncertified vtable use");
            assert!(
                got.starts_with(
                    "`reads_vtable` uses its VTABLE outside the certified image (crystal D14/E5)"
                ),
                "{got}"
            );
            assert!(got.contains(why), "{why}: {got}");
        }
        // The layout is certified at 64 bits only.
        let got = project(
            &mut Projector {
                usize_bits: Some(32),
                ..Projector::default()
            },
            d14(),
        )
        .expect_err("32-bit");
        assert!(got.contains("64-bit target only"), "{got}");
    }

    /// Reader A over the committed E5 slices of real m0off bodies
    /// (`crates/clean-verify/tests/fixtures/e5/`): each slice projects to the core committed
    /// beside it, which Clean's reader B, the minter and the kernel run of
    /// `tests/eval_ir/e5_fat_images.rs` then hold to trust-ir's reference interpreter. Read at
    /// RUN time, so the crate compiles no file outside itself.
    ///
    /// The projector reads trust-ir BINARY only (its dependency is exactly `binary` + `fmt`,
    /// `scripts/check_workspace_dependency_boundary.py`), so the slices are committed twice: the
    /// reviewable TEXT, which reader B and the reference interpreter parse, and its binary
    /// encoding (`trust_ir::binary::serialize_module` of the parsed text). The two are bound
    /// here by trust-ir's own printer: the binary, decoded and rendered canonically, IS the text
    /// minus its `;` comment lines, so neither can move without the other.
    #[test]
    fn the_e5_slices_of_real_bodies_project_to_their_committed_cores() {
        let dir = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../crates/clean-verify/tests/fixtures/e5"
        );
        let read = |f: &str| {
            std::fs::read_to_string(format!("{dir}/{f}"))
                .unwrap_or_else(|e| panic!("{dir}/{f} is a committed E5 fixture: {e}"))
        };
        let bin = format!("{dir}/e5_m0off_slices.trust-ir.bin");
        let bytes =
            std::fs::read(&bin).unwrap_or_else(|e| panic!("{bin} is a committed E5 fixture: {e}"));
        let module =
            trust_ir::binary::deserialize_module(&bytes).expect("the E5 binary fixture decodes");
        let uncommented = |t: &str| -> String {
            t.lines()
                .filter(|l| !l.starts_with(';'))
                .map(|l| format!("{l}\n"))
                .collect()
        };
        assert_eq!(
            uncommented(&trust_ir::format::canonical(&module)),
            uncommented(&read("e5_m0off_slices.trust-ir.txt")),
            "the binary fixture is not the encoding of the committed text"
        );
        let mut images = 0;
        for slug in [
            "get_const_d14",
            "get_const_vtable_read",
            "get_const_rebuild",
            "name_eq_arc_str_deref",
            "name_eq_ptr_eq",
            "nameinner_clone_data",
        ] {
            let name = format!("e5::{slug}");
            let f = module
                .functions
                .iter()
                .find(|f| f.name == name)
                .unwrap_or_else(|| panic!("{name} is not in the fixture"));
            let mut p = p64();
            let core = p
                .project_chain(&module, &[f])
                .unwrap_or_else(|e| panic!("{name}: {e}"));
            assert_eq!(core, read(&format!("e5_{slug}.core.txt")), "{name}");
            images += p.vtable_reads;
        }
        // The D14 read is certified in the whole slice and in its read half: two loads.
        assert_eq!(images, 2);
    }

    #[test]
    fn a_non_canonical_metadata_type_and_a_fat_constant_are_refused_by_name() {
        // A vtable word read as an integer is the reference's type error, and the machine would
        // bind the word as an integer at that type.
        let got = project(
            &mut p64(),
            Shape {
                meta_ty: Ty::U64,
                from_vtable: false,
                ..d14()
            },
        )
        .expect_err("a vtable word at u64");
        assert!(
            got.contains("ptr_metadata: the declared metadata type `u64` is not"),
            "{got}"
        );
        // A length read as a pointer, the other way round.
        let got = project(
            &mut p64(),
            Shape {
                kind: FatPtrKind::ContainerLen,
                from_vtable: false,
                ..d14()
            },
        )
        .expect_err("a length at ptr");
        assert!(got.contains("canonical `u64`"), "{got}");
        let mut p = p64();
        for kind in [
            FatPtrKind::ContainerLen,
            FatPtrKind::ContainerVtable,
            FatPtrKind::TraitObject { trait_id: 3 },
        ] {
            let got = p
                .inst(&Inst::Const {
                    ty: Ty::FatPtr(kind),
                    value: Constant::Aggregate(vec![Constant::Int(0), Constant::Int(0)]),
                })
                .expect_err("a fat constant");
            assert!(got.contains("has no null lane"), "{got}");
        }
    }
}

#[derive(Default)]
struct Projector {
    enums: BTreeMap<u32, u32>,
    structs: BTreeMap<u32, u32>,
    funcs: BTreeMap<u32, u32>,
    globals: BTreeMap<u32, u32>,
    enum_order: Vec<u32>,
    /// raw enum id -> the artifact function id that FIRST named it.
    ///
    /// Needed because a merged projection reads TWO artifacts, and an
    /// aggregate id is an index into its own module: `enum.1` named by a body
    /// from the sidecar bundle is a different type from `enum.1` named by a
    /// body from the crate module. Interning alone cannot tell them apart, and
    /// the encodings derivation has to read a DEFINITION, so it needs to know
    /// whose table to read it out of.
    enum_first_seen_by: BTreeMap<u32, u32>,
    /// raw struct id -> the artifact function id that FIRST named it, for the
    /// same reason as the enum twin above.
    struct_first_seen_by: BTreeMap<u32, u32>,
    /// raw enum / struct id -> EVERY function whose body (or whose artifact's
    /// payload type) named it, not only the first, so `aggregate_collisions`
    /// can see a raw id that two artifacts name.
    enum_named_by: BTreeMap<u32, BTreeSet<u32>>,
    struct_named_by: BTreeMap<u32, BTreeSet<u32>>,
    /// Whose id space an interned aggregate id is in, for the maps above: the
    /// function being projected, or -- in `derive_encodings` -- the function
    /// whose artifact's table the payload type was read from.
    current_func: u32,
    struct_order: Vec<u32>,
    func_order: Vec<u32>,
    /// Crate global ids in first-use order: position = canonical index, the
    /// same rule as `func_order`. Filled by `global_id` from a `globaladdr`
    /// site and walked by `project_chain` to print the `(globals …)` list.
    global_order: Vec<u32>,
    /// Per canonical global: the artifact's name (`__trust_promoted_4557`),
    /// the UNRESOLVED type as the artifact spells it (`[ty.0 x 34]`), the
    /// same type resolved through the module's type table (`[u8 x 34]`),
    /// and the linkage. All four are erased from the core module —
    /// `IRGlobal` carries an id and a constant and nothing else — so they
    /// are recorded in provenance for the tag table to pin.
    global_names_seen: Vec<String>,
    global_tys_erased: Vec<String>,
    global_tys_resolved: Vec<String>,
    global_linkages_erased: Vec<String>,
    /// Every `ty.N` a global's array type named, with its resolution from
    /// `module.types` — the type-table rows reader B reads from the fixture's
    /// `type ty.N = …` preamble line.
    type_table_resolved: BTreeMap<u32, String>,
    aligns: Vec<String>,
    param_tys: Vec<String>,
    block_param_tys: Vec<String>,
    /// The pinned width `usize` resolves to, from `--usize-bits`. `None`
    /// REFUSES the type — a target assumption must be stated, never inherited.
    usize_bits: Option<u32>,
    /// How many `usize` sites the flag resolved, recorded in provenance so the
    /// tag table's pinned count has an artifact-side witness.
    usize_seen: u32,
    isize_seen: u32,
    /// Bodiless DECLARATIONS named in the chain and OMITTED from it (crystal plan step 18: the
    /// trust bridge's `premise-decls` lane declares one per FOREIGN premise). Recorded in
    /// provenance only when non-empty, so every earlier chain's provenance is byte-identical.
    omitted_declarations: Vec<String>,
    /// Crystal D10: native atomic instructions imaged by [`Projector::seq_atomic_image`].
    seq_atomic_images: u32,
    /// Crystal D11 (`--tls-cells <manifest>`): the thread-local symbols the callee sidecar's
    /// manifest CERTIFIES (`tls_cells` rows with `"certified": true`), symbol -> static path.
    /// Empty: no `trust_rust.thread_local_addr` has an image.
    tls_certified: BTreeMap<String, String>,
    /// Crystal D11: the TLS input cells the chain addresses, as (canonical global id, symbol), in
    /// first-use order. Their ids follow every artifact global and are never 0 (`project_chain`).
    tls_cells: Vec<(u32, String)>,
    /// Crystal D11: `thread_local_addr` ops imaged by [`Projector::tls_input_image`].
    tls_input_images: u32,
    /// Crystal D12 (decision memo §18, `--ptr-bitcast-identity`): image `bitcast ptr -> ptr` as
    /// `copy (ptr)`. OFF by default, so every committed chain re-projects byte-identical --
    /// `ir_itc` carries four such bitcasts under their `(cast bitcast ..)` image.
    ptr_bitcast_identity: bool,
    /// Crystal D12: `bitcast ptr -> ptr` nodes imaged as `copy (ptr)` by
    /// [`Projector::ptr_bitcast_identity_image`].
    ptr_bitcast_identities: u32,
    /// Crystal (memo §18): negative integer constants imaged as their width-W bit pattern by
    /// [`Projector::negative_int_const_image`].
    negative_int_images: u32,
    /// Crystal (memo §15, lead ruling on D10; executed §18): the (function id, block id,
    /// instruction index) of every halting `assert` the trust bridge lowered for a reached
    /// undefined-behaviour callee, read off its obligation ([`ub_halt_sites_of`]).
    ub_halt_sites: std::collections::BTreeSet<(u32, u32, u32)>,
    /// Function ids that carry an undefined-behaviour halt obligation with NO site (u32::MAX: no
    /// function either). Such a body is refused: its halt cannot be located, so it cannot be
    /// kept out of the sanctioned-panic arm.
    ub_unsited: std::collections::BTreeSet<u32>,
    /// Undefined-behaviour halts imaged as `unreachable` by [`Projector::ub_halt_image`].
    ub_halt_images: u32,
    /// Crystal D14/E5 (memo §23): the vtable slot loads [`d14_vtable_certify`] certified.
    vtable_reads: usize,
}

pub(crate) type R<T> = Result<T, String>;

/// Crystal D10 (decision memo §15): the premise under which [`Projector::seq_atomic_image`] is
/// EXACT. Not a FOREIGN, FOREIGN-CALLBACK or INPUT premise (memo §7): an ENVIRONMENT premise,
/// the one entry D10 admits in that class.
pub(crate) const SEQ_PREMISE: &str = "SEQ: no other thread writes a memory cell that a native \
    atomic instruction of the projected bodies reads or writes while the projected run is live, \
    so each atomic instruction computes exactly its sequential image and every ordering and \
    fence is vacuous";

/// Crystal E5 (decision memo §23): what a certified vtable read is exact OVER. Not a premise the
/// projector discharges: the caller's heap holds the vtable image at the word's address, which a
/// representation relation states (`ir_vtable_slot`, `ir_vtable_cells`) and rustc's
/// `tcx.vtable_allocation(source, principal)` fixes.
pub(crate) const VTABLE_IMAGE: &str = "VTABLE: a vtable word of a `dyn`-carrying wide pointer \
    addresses rustc's vtable allocation for its (source, principal) pair, laid out \
    [drop_in_place, size, align, methods..] one 8-byte word per slot, read-only; the certified \
    loads read its size (+8) and align (+16) words (ir_vtable_cells, ir_vtable_align_load)";

/// Crystal D11 (decision memo §17): the premise under which [`Projector::tls_input_image`] is
/// EXACT. An INPUT premise with a TYPE-COMPLETE certificate (the callee sidecar's `tls_cells`
/// row: the symbol names one static, its type is pointer-free and definitely `!Sync`), never an
/// ENVIRONMENT one: the only entry of that class stays SEQ.
pub(crate) const TLS_PREMISE: &str = "TLS: each distinct symbol of a \
    `trust_rust.thread_local_addr` op in the projected bodies names ONE thread-local static, \
    certified by the callee sidecar's `tls_cells` row (unique symbol, pointer-free type, \
    definitely !Sync), and every evaluation of the op during the projected run yields the \
    address of that static's instance on the running thread: non-null, dereferenceable, live, \
    and disjoint from every other allocation the run reaches -- the MIR meaning of \
    Rvalue::ThreadLocalRef on one thread, which the op's version-1 schema withholds; the cell's \
    content when the run starts is an INPUT, quantified over every value of the static's type \
    (never its initializer); and no agent outside the run writes the cell while it is live -- \
    another thread cannot hold a reference to a !Sync thread-local's instance without a data \
    race, which the adequacy step excludes for every non-atomic cell, and the same thread \
    re-enters only through code of the run or a FOREIGN-CALLBACK contract";

impl Projector {
    /// The Clean image of a type, for the encodings derivation.
    ///
    /// Takes `&mut self` because `ty` interns, and that is CORRECT here rather
    /// than a wart: a payload type named by an encodings row must be a type the
    /// module already carries, so interning it is how the row and the bodies
    /// end up naming the SAME canonical aggregate.
    fn ty_of(&mut self, t: &Ty) -> R<String> {
        self.ty(t)
    }

    fn enum_id(&mut self, id: u32) -> u32 {
        self.enum_named_by
            .entry(id)
            .or_default()
            .insert(self.current_func);
        let n = self.enums.len() as u32;
        *self.enums.entry(id).or_insert_with(|| {
            self.enum_order.push(id);
            self.enum_first_seen_by.insert(id, self.current_func);
            n
        })
    }
    fn struct_id(&mut self, id: u32) -> u32 {
        self.struct_named_by
            .entry(id)
            .or_default()
            .insert(self.current_func);
        let n = self.structs.len() as u32;
        *self.structs.entry(id).or_insert_with(|| {
            self.struct_order.push(id);
            self.struct_first_seen_by.insert(id, self.current_func);
            n
        })
    }
    fn func_id(&mut self, id: u32) -> u32 {
        let n = self.funcs.len() as u32;
        *self.funcs.entry(id).or_insert_with(|| {
            self.func_order.push(id);
            n
        })
    }
    fn global_id(&mut self, id: u32) -> u32 {
        let n = self.globals.len() as u32;
        *self.globals.entry(id).or_insert_with(|| {
            self.global_order.push(id);
            n
        })
    }

    /// Project one OR MORE functions into a single core module, under ONE
    /// crate-level interning namespace.
    ///
    /// Each function's own id is interned immediately before its body is
    /// walked, so the root takes canonical index 0 and every callee — a
    /// sibling body included — interns above it in first-use order. For a
    /// one-function chain this is exactly the previous behaviour, and every
    /// committed `ir_*.core.txt` is byte-identical under it.
    fn project_chain(
        &mut self,
        module: &trust_ir::Module,
        fs: &[&trust_ir::Function],
    ) -> R<String> {
        if fs.is_empty() {
            return Err("a core module carries at least one function".into());
        }
        // Trust (crystal plan step 18): a bodiless DECLARATION -- what the bridge's
        // `premise-decls` lane emits for a FOREIGN premise, no blocks and no body anywhere -- has
        // no `IRFunc` image, so it is OMITTED rather than refused: a call to it then names an id
        // no `(func ...)` of the module defines, which `ir_call_exec` answers `stuck no_func`.
        // That is the one honest reading of a premise until a returns-under-contract rule
        // exists (E-phase). The ROOT is the body being projected and must have one.
        if fs[0].blocks.is_empty() {
            return Err(format!(
                "the root `{}` is a bodiless declaration: there is no body to project",
                fs[0].name
            ));
        }
        let mut out = String::new();
        out.push_str("(module\n");
        out.push_str("  (funcs\n");
        for f in fs {
            if f.blocks.is_empty() {
                self.omitted_declarations.push(f.name.clone());
                continue;
            }
            self.current_func = f.id.0;
            out.push_str(&self.project_one(f)?);
        }
        out.push_str("  )\n");
        // The module's global list: every global some body of the chain
        // took the address of, in first-use order, each carrying its
        // INITIALIZER as the `IRConst` the machine seeds its cell with
        // (`ir_mem_concat` prepends one slot per global, keyed by this
        // canonical index — a global's id IS its address). A chain that
        // touches no global prints the literal `(globals)` every committed
        // core carries, byte for byte; the list form appeared 2026-09-09
        // with the `<LevelArc as Deref>::deref` body, whose `expect`
        // message is a promoted `[u8 x 34]` array.
        // Crystal D11: the TLS input cells take ids AFTER every artifact global, and never 0.
        // EvalIR's address of a global IS its id, and `ptrtoint` of `ptr_ 0` is the integer 0, so
        // a cell at id 0 would read as NULL to the `is_null` test `LocalKey::try_with` makes on
        // exactly this address -- the image would send the run down the AccessError arm, which
        // the deployed program (a non-null TLS address, D11) never takes. The bodies were walked
        // before the artifact globals were all known, so they carry a placeholder, replaced here.
        let tls_base = (self.global_order.len() as u32).max(1);
        for (j, cell) in self.tls_cells.iter_mut().enumerate() {
            cell.0 = tls_base + j as u32;
            out = out.replace(&tls_placeholder(j), &cell.0.to_string());
        }
        if self.global_order.is_empty() && self.tls_cells.is_empty() {
            out.push_str("  (globals)\n");
        } else {
            out.push_str("  (globals");
            for k in 0..self.global_order.len() {
                let raw = self.global_order[k];
                let g = module.globals.get(raw as usize).ok_or_else(|| {
                    format!(
                        "globaladdr names @global.{raw}, absent from the artifact's global table"
                    )
                })?;
                // Fail closed on the three printed fields the core cannot
                // carry and reader B's preamble refuses by the same names
                // (`mut`, `tls(..)`, `align(..)`): an erasure here with no
                // refusal on the other side would let a `mut` global project
                // to the same core as an immutable one.
                if g.mutable {
                    return Err(format!(
                        "global @{} is `mut`: a mutable global has no image in the core module \
                         (the machine seeds its cell once and never writes it back)",
                        g.name
                    ));
                }
                if let Some(tls) = g.tls {
                    return Err(format!(
                        "global @{} is thread-local (tls({tls})): no image in the core module",
                        g.name
                    ));
                }
                if let Some(align) = g.align {
                    return Err(format!(
                        "global @{} carries align({align}): no image in the core module",
                        g.name
                    ));
                }
                let init = g.initializer.as_ref().ok_or_else(|| {
                    format!(
                        "global @{} has no initializer: a declaration-only global has no cell \
                         content for the machine to seed",
                        g.name
                    )
                })?;
                let resolved = self.global_ty_resolved(module, &g.name, &g.ty)?;
                let c = self.global_init(module, &g.ty, init)?;
                let _ = write!(out, " (global {k} {c})");
                self.global_names_seen.push(g.name.clone());
                self.global_tys_erased.push(format!("{}", g.ty));
                self.global_tys_resolved.push(resolved);
                self.global_linkages_erased.push(format!("{}", g.linkage));
            }
            // Crystal D11: an INPUT cell has no initializer to seed -- its content at the run's
            // start is quantified over, never the static's initializer. The form is one no core
            // reader parses as an `IRConst`, so a mint over it fails CLOSED until the quantified
            // statement form exists.
            for (k, symbol) in &self.tls_cells {
                let _ = write!(out, " (global {k} (tls_input {}))", json_string(symbol));
            }
            out.push_str(")\n");
        }
        out.push_str(")\n");
        Ok(out)
    }

    /// Resolve a global's `Ty::Array(ty.N, len)` through the module's type
    /// table and spell it the way the emitted text spells a resolved array
    /// (`[u8 x 34]`), recording the `ty.N = …` row it consulted. A STRUCT- or
    /// TUPLE-typed global (crystal plan step 18: the trust bridge's
    /// `const-images` lane materialises an immutable constant allocation as
    /// one) consults no type-table row and spells as its `fn ty` image. Every
    /// other global type is refused; `global_init` pairs each accepted type
    /// with exactly one initializer form (the POSITION rule).
    fn global_ty_resolved(&mut self, module: &trust_ir::Module, name: &str, ty: &Ty) -> R<String> {
        // A `match` naming every variant, not `matches!`: the macro expands to a
        // `_ => false` arm the wildcard lints never see (clippy skips macro
        // expansions), which is why scripts/check_lint_coverage.py refuses it here.
        let aggregate = match ty {
            Ty::Ext(e) => e.unreachable(),
            Ty::Struct(_) | Ty::Tuple(_) => true,
            Ty::Array(..)
            | Ty::Ptr
            | Ty::PtrConst(_)
            | Ty::PtrMut(_)
            | Ty::Ref(_)
            | Ty::RefMut(_)
            | Ty::I8
            | Ty::I16
            | Ty::I32
            | Ty::I64
            | Ty::I128
            | Ty::U8
            | Ty::U16
            | Ty::U32
            | Ty::U64
            | Ty::U128
            | Ty::Isize
            | Ty::Usize
            | Ty::Char
            | Ty::Error
            | Ty::F16
            | Ty::F32
            | Ty::F64
            | Ty::Bool
            | Ty::Unit
            | Ty::Never
            | Ty::Enum(_)
            | Ty::Rc(_)
            | Ty::Vector(..)
            | Ty::FatPtr(_)
            | Ty::Func(_)
            | Ty::Set(..)
            | Ty::Sequence(_)
            | Ty::Record(_)
            | Ty::Closure(_)
            | Ty::Refine(..)
            | Ty::Dialect(_)
            | Ty::Tensor(..)
            | Ty::Storage(_)
            | Ty::Handle(_) => false,
        };
        if aggregate {
            return self.ty(ty);
        }
        let (elem, len) = match ty {
            Ty::Ext(e) => e.unreachable(),
            Ty::Array(elem, len) => (elem, len),
            // Every other variant NAMED (a `let .. else` until main's lint r11:
            // its `else` stood for them all, and for any variant trust-ir adds).
            // `Struct`/`Tuple` returned above; they are named here for the same
            // reason and never reach this arm.
            Ty::I8
            | Ty::I16
            | Ty::I32
            | Ty::I64
            | Ty::I128
            | Ty::U8
            | Ty::U16
            | Ty::U32
            | Ty::U64
            | Ty::U128
            | Ty::Isize
            | Ty::Usize
            | Ty::Char
            | Ty::Error
            | Ty::F16
            | Ty::F32
            | Ty::F64
            | Ty::Bool
            | Ty::Vector(..)
            | Ty::Ptr
            | Ty::FatPtr(_)
            | Ty::Unit
            | Ty::Never
            | Ty::Struct(_)
            | Ty::Tuple(_)
            | Ty::Enum(_)
            | Ty::Func(_)
            | Ty::Ref(_)
            | Ty::RefMut(_)
            | Ty::PtrConst(_)
            | Ty::PtrMut(_)
            | Ty::Rc(_)
            | Ty::Set(..)
            | Ty::Sequence(_)
            | Ty::Record(_)
            | Ty::Closure(_)
            | Ty::Refine(..)
            | Ty::Dialect(_)
            | Ty::Tensor(..)
            | Ty::Storage(_)
            | Ty::Handle(_) => {
                return Err(format!(
                    "global @{name} has type `{ty}`: only an array-typed global has an image \
                     in the core module (its initializer is the cell's `IRConst.agg`)"
                ))
            }
        };
        let elem_ty = module.types.get(elem.0 as usize).ok_or_else(|| {
            format!(
                "global @{name} names ty.{}, absent from the artifact's type table",
                elem.0
            )
        })?;
        let elem_text = format!("{elem_ty}");
        if elem_text.contains("ty.") {
            return Err(format!(
                "global @{name}: element type ty.{} resolves to `{elem_text}`, which still \
                 names the type table — a nested table reference is not a resolution",
                elem.0
            ));
        }
        self.type_table_resolved
            .entry(elem.0)
            .or_insert_with(|| elem_text.clone());
        Ok(format!("[{elem_text} x {len}]"))
    }

    fn project_one(&mut self, f: &trust_ir::Function) -> R<String> {
        let mut out = String::new();
        // Crystal (memo §15/§18): a UB halt that cannot be located cannot be kept out of the
        // sanctioned-panic arm, so its body has no image.
        if self.ub_unsited.contains(&f.id.0) || self.ub_unsited.contains(&u32::MAX) {
            return Err(format!(
                "`{}` carries an undefined-behaviour halt obligation with no site: its halt \
                 cannot be located, so it cannot be kept out of the sanctioned-panic arm",
                f.name
            ));
        }
        // Crystal D14, imaged by E5 (memo §23): a body's reads of a VTABLE word are certified
        // against the vtable image -- a load of the size or align slot through a byte offset from
        // the word, and the word passed on unchanged as a new wide pointer's metadata -- and every
        // other use of the word is refused by name, before any per-node refusal.
        let reads = d14_vtable_certify(f, self.usize_bits).map_err(|why| {
            format!(
                "`{}` uses its VTABLE outside the certified image (crystal D14/E5): {why}",
                f.name
            )
        })?;
        self.vtable_reads += reads.len();
        // *** ONE NAMESPACE. *** The function's own id and its callee ids are
        // the same namespace by the specification's own semantics:
        // `ir_func_find` resolves a callee by scanning for a function whose OWN
        // id equals it, and `ir_call_exec` goes through `ir_func_find`. Until
        // 2026-08-20 this printed the literal `0` here while interning callees
        // from a counter that also started at 0, so in `level_is_zero` the
        // numeral 0 denoted BOTH the body and `<LevelArc as Deref>::deref` --
        // and swapping the two `@func.N` literals in the emitted text produced
        // a byte-identical core module for a different program. Interning the
        // own id FIRST gives it index 0, gives the self-call index 0 too, and
        // pushes every other callee above it.
        let self_idx = self.func_id(f.id.0);
        out.push_str(&format!("    (func {self_idx}\n"));
        // Parameters: the entry block's parameters ARE the function parameters
        // in this producer's shape; Clean's IRFunc carries their ids only.
        let entry = f
            .blocks
            .iter()
            .find(|b| b.id == f.entry)
            .ok_or_else(|| format!("entry block {:?} missing", f.entry))?;
        for p in &entry.params {
            self.param_tys.push(format!("{:?}", p.1));
        }
        let ps: Vec<String> = entry.params.iter().map(|p| p.0 .0.to_string()).collect();
        out.push_str(&format!("      (params{})\n", pad(&ps)));
        out.push_str(&format!("      (entry {})\n", f.entry.0));
        out.push_str("      (blocks\n");
        // Crystal D10: the ids a SEQ atomic image binds for its intermediate values, above every id
        // the body itself binds, so an image never shadows a producer value.
        let mut fresh = f.max_value_id() + 1;
        for b in &f.blocks {
            out.push_str(&format!("        (block {}\n", b.id.0));
            if b.id != f.entry {
                for p in &b.params {
                    self.block_param_tys.push(format!("bb{}:{:?}", b.id.0, p.1));
                }
            }
            let bps: Vec<String> = if b.id == f.entry {
                Vec::new()
            } else {
                b.params.iter().map(|p| p.0 .0.to_string()).collect()
            };
            out.push_str(&format!("          (params{})\n", pad(&bps)));
            out.push_str("          (nodes\n");
            for (k, n) in b.body.iter().enumerate() {
                // Crystal (memo §15/§18): an undefined-behaviour halt is `unreachable`, never the
                // sanctioned-panic `assert`.
                if let Some(nodes) = self.ub_halt_image(f, b, k)? {
                    for node in nodes {
                        out.push_str(&format!("            {node}\n"));
                    }
                    continue;
                }
                // Crystal D12 (memo §18): `bitcast ptr -> ptr` is the identity, imaged as `copy`.
                if let Some(nodes) = self.ptr_bitcast_identity_image(n)? {
                    for node in nodes {
                        out.push_str(&format!("            {node}\n"));
                    }
                    continue;
                }
                // Crystal (memo §18): a negative integer constant is its width-W bit pattern.
                if let Some(nodes) = self.negative_int_const_image(n)? {
                    for node in nodes {
                        out.push_str(&format!("            {node}\n"));
                    }
                    continue;
                }
                // Crystal D10: a native atomic is imaged as the SEQUENTIAL nodes that compute it.
                if let Some(nodes) = self.seq_atomic_image(n, &mut fresh)? {
                    for node in nodes {
                        out.push_str(&format!("            {node}\n"));
                    }
                    continue;
                }
                // Crystal D11: a certified thread-local address is the address of its INPUT cell.
                if let Some(nodes) = self.tls_input_image(n)? {
                    for node in nodes {
                        out.push_str(&format!("            {node}\n"));
                    }
                    continue;
                }
                let rs: Vec<String> = n.results.iter().map(|r| r.0.to_string()).collect();
                let i = self.inst(&n.inst)?;
                out.push_str(&format!("            (node (results{}) {})\n", pad(&rs), i));
            }
            out.push_str("          ))\n");
        }
        out.push_str("      ))\n");
        Ok(out)
    }

    fn ty(&mut self, t: &Ty) -> R<String> {
        Ok(match t {
            Ty::Ext(e) => e.unreachable(),
            Ty::Bool => "(bool)".into(),
            Ty::I8 => "(int 8)".into(),
            Ty::I16 => "(int 16)".into(),
            Ty::I32 => "(int 32)".into(),
            Ty::I64 => "(int 64)".into(),
            Ty::I128 => "(int 128)".into(),
            Ty::U8 => "(uint 8)".into(),
            Ty::U16 => "(uint 16)".into(),
            Ty::U32 => "(uint 32)".into(),
            Ty::U64 => "(uint 64)".into(),
            Ty::U128 => "(uint 128)".into(),
            Ty::Usize => match self.usize_bits {
                // The image is the plain fixed-width integer: the CORE MODULE
                // deliberately does not remember that the artifact said
                // `usize`, because reader C (the registered kernel term) could
                // never reproduce that distinction -- Clean's IRTy has no
                // usize. What survives instead: this projector RECORDS the
                // resolution (bits + site count) in provenance, and the tag
                // table pins both, so a `u64`-for-`usize` swap is caught at
                // the pinned site count, not by the core text.
                Some(bits) => {
                    self.usize_seen += 1;
                    format!("(uint {bits})")
                }
                None => {
                    return Err(
                        "no Clean IRTy image for trust_ir::Ty::Usize without a pinned target \
                         width: `usize` is TARGET-DEPENDENT, and resolving it silently would \
                         bake an unstated word-size assumption into a committed core module. \
                         Pass --usize-bits <N> (a target fact, recorded in provenance and \
                         pinned in the chain's tag table) to resolve it."
                            .into(),
                    )
                }
            },
            // `isize` rides the SAME stated width, and that is Rust's own
            // definition rather than a convenience: both are the width of the
            // platform's pointer, so a target where they differ does not exist
            // to be wrong about. The image is the SIGNED fixed-width integer,
            // and the site count is kept SEPARATE from `usize`'s so the
            // chain's tag table can pin each — a body that swapped one token
            // for the other resolves to a different core, and one summed pin
            // would accept the swap. Same refusal without the flag, for the
            // same reason.
            Ty::Isize => match self.usize_bits {
                Some(bits) => {
                    self.isize_seen += 1;
                    format!("(int {bits})")
                }
                None => {
                    return Err(
                        "no Clean IRTy image for trust_ir::Ty::Isize without a pinned target \
                         width: `isize` is TARGET-DEPENDENT, and resolving it silently would \
                         bake an unstated word-size assumption into a committed core module. \
                         Pass --usize-bits <N> (a target fact -- Rust defines `isize` and \
                         `usize` as the same width -- recorded in provenance and pinned in the \
                         chain's tag table) to resolve it."
                            .into(),
                    )
                }
            },
            Ty::F32 => "(float 32)".into(),
            Ty::F64 => "(float 64)".into(),
            Ty::Ptr => "(ptr)".into(),
            Ty::Unit => "(unit)".into(),
            Ty::Never => "(never)".into(),
            Ty::Struct(id) => format!("(struct {})", self.struct_id(id.0)),
            Ty::Enum(id) => format!("(enum {})", self.enum_id(id.0)),
            Ty::Ref(inner) => format!("(ref {})", self.ty(inner)?),
            Ty::RefMut(inner) => format!("(refmut {})", self.ty(inner)?),
            Ty::PtrConst(inner) => format!("(rawconst {})", self.ty(inner)?),
            Ty::PtrMut(inner) => format!("(rawmut {})", self.ty(inner)?),
            Ty::Rc(inner) => format!("(rc {})", self.ty(inner)?),
            // `&str` images as a fat pointer to bytes. Only `Str` has an
            // image: every other `FatPtrKind` is refused by name below, which
            // is what makes the image INJECTIVE on the accepted fragment — no
            // erasure row is needed because no two accepted types collapse.
            // Reader B accepts exactly `fatptr<str>` by the same rule.
            Ty::FatPtr(trust_ir::FatPtrKind::Str) => "(fatptr (uint 8))".into(),
            // Crystal E5 (decision memo §23): the M0 producer's three other kinds, each onto
            // its OWN IRTy constructor, so the image stays injective (`(containerlen)` is not
            // `Str`'s `(fatptr (uint 8))`, and `(fatdyn N)` keeps the trait id). The cell
            // machine admits all three as shape class 5, the class of `IRScalar.fat_`, and reads
            // `ptr_metadata`'s word at the declared metadata type -- a length for
            // `container_len`, a vtable address for the other two -- as the reference does.
            // Reader B spells the same three (`ir_mint::emitted`).
            Ty::FatPtr(trust_ir::FatPtrKind::ContainerLen) => "(containerlen)".into(),
            Ty::FatPtr(trust_ir::FatPtrKind::ContainerVtable) => "(containervtable)".into(),
            Ty::FatPtr(trust_ir::FatPtrKind::TraitObject { trait_id }) => {
                format!("(fatdyn {trait_id})")
            }
            // `IRTy.tuple_` takes a Nat and there is no tuple table in the
            // reflected module to index, so that Nat can only be the ARITY.
            //
            // WHAT THIS ERASES, said out loud because it is the ir_ni posture and
            // not a silent widening: two tuple types of the same arity image to
            // the SAME `(tuple k)`, so a body differing from another only by
            // `(u32, bool)` vs `(u64, ptr)` projects to the same core module. The
            // core text cannot tell them apart and is not asked to; the chain's
            // tag table records the observed spelling and its A2 gate asserts it
            // against the emitted text, which is where that swap is caught --
            // exactly how ir_ni catches a `u64`-for-`usize` swap with a count
            // rather than with the resolved core.
            //
            // It is arity-only rather than richer because the machine needs
            // nothing else: `insertfield` and `extractfield` ignore the declared
            // type and work structurally over the value's spine, and a tuple LOAD
            // has no recorded size so it fails closed on the path where the
            // element types would have mattered.
            Ty::Tuple(es) => format!("(tuple {})", es.len()),
            // A FUNCTION type (`functy.N`): a fn-pointer value's type, and the type a
            // `fndef<func.K>` constant carries (crystal plan step 18, the trust bridge's
            // `fn-values` lane). `IRTy.func_` takes a Nat and the core module carries no
            // signature table, so the Nat is the artifact's RAW `functy` index -- the SAME
            // index `callindirect` prints raw above, and for the same reason: the cell
            // machine never reads it (`ir_exec_callind_sig_irrelevant` pins that a call's
            // signature index cannot change its step, and no load/store/cast arm dispatches
            // on a `func_` type). What it erases is the signature itself, exactly as
            // `callindirect`'s raw index does.
            Ty::Func(id) => format!("(func {})", id.0),
            // Every variant `IRTy` has no image for, NAMED rather than
            // wildcarded, so a variant trust-ir adds fails to compile here
            // until someone decides whether it has one.
            other @ (Ty::Char
            | Ty::Error
            | Ty::F16
            | Ty::Vector(..)
            | Ty::FatPtr(trust_ir::FatPtrKind::Slice(_))
            | Ty::Array(..)
            | Ty::Set(..)
            | Ty::Sequence(_)
            | Ty::Record(_)
            | Ty::Closure(_)
            | Ty::Refine(..)
            | Ty::Dialect(_)
            | Ty::Tensor(..)
            | Ty::Storage(_)
            | Ty::Handle(_)) => return Err(no_ty_image(other)),
        })
    }

    /// A GLOBAL INITIALIZER, and nothing else, paired with the global's TYPE:
    /// an array-typed global takes `Constant::Array` (`array[…]`), which `cst`
    /// keeps refusing, so `array[…]` can never appear inside a `const` node; a
    /// struct- or tuple-typed global (crystal plan step 18, `const-images`)
    /// takes `Constant::Aggregate` (`{…}`). Both read as `IRConst.agg` in the
    /// core -- the one cell the machine seeds for the global and a load returns
    /// whole -- and the global's type is what keeps the two forms apart.
    fn global_init(&mut self, module: &trust_ir::Module, ty: &Ty, c: &Constant) -> R<String> {
        match (ty, c) {
            // trust-ir D1b: the extension type is uninhabited in this build. Every
            // initializer form NAMED, not wildcarded, for the reason `ty` gives.
            (
                Ty::Ext(e),
                Constant::Array(_)
                | Constant::Int(_)
                | Constant::U128(_)
                | Constant::Bytes { .. }
                | Constant::Float(_)
                | Constant::Bool(_)
                | Constant::Aggregate(_)
                | Constant::Vector(_)
                | Constant::Sequence(_)
                | Constant::Set(_)
                | Constant::Record(_)
                | Constant::Closure { .. }
                | Constant::FnDef(_)
                | Constant::SymbolAddr { .. }
                | Constant::PhantomData
                | Constant::Uninit
                | Constant::TensorBlob { .. }
                | Constant::Splat { .. }
                | Constant::Ext(_),
            ) => e.unreachable(),
            (Ty::Array(..), Constant::Array(v)) => {
                let mut s = String::from("(agg");
                for e in v {
                    s.push(' ');
                    s.push_str(&self.cst(e)?);
                }
                s.push(')');
                Ok(s)
            }
            (Ty::Struct(_) | Ty::Tuple(_), Constant::Aggregate(v)) => {
                let mut s = String::from("(agg");
                for e in v {
                    s.push(' ');
                    s.push_str(&self.global_elem(module, e)?);
                }
                s.push(')');
                Ok(s)
            }
            // Named, not wildcarded -- the TYPE as well as the constant: a
            // shape trust-ir adds fails to compile here until someone decides
            // whether it may initialize a global. The accepted pairs above are
            // the only two; every other (type, initializer) pair is refused.
            // (Until the 2026-09-26 merge of origin/main the type slot was a
            // `_`, a catch-all nested in the pattern that no wildcard lint
            // sees and main's r10 lint scan refuses.)
            (
                Ty::Array(..)
                | Ty::Struct(_)
                | Ty::Tuple(_)
                | Ty::Ptr
                | Ty::PtrConst(_)
                | Ty::PtrMut(_)
                | Ty::Ref(_)
                | Ty::RefMut(_)
                | Ty::I8
                | Ty::I16
                | Ty::I32
                | Ty::I64
                | Ty::I128
                | Ty::U8
                | Ty::U16
                | Ty::U32
                | Ty::U64
                | Ty::U128
                | Ty::Isize
                | Ty::Usize
                | Ty::Char
                | Ty::Error
                | Ty::F16
                | Ty::F32
                | Ty::F64
                | Ty::Bool
                | Ty::Unit
                | Ty::Never
                | Ty::Enum(_)
                | Ty::Rc(_)
                | Ty::Vector(..)
                | Ty::FatPtr(_)
                | Ty::Func(_)
                | Ty::Set(..)
                | Ty::Sequence(_)
                | Ty::Record(_)
                | Ty::Closure(_)
                | Ty::Refine(..)
                | Ty::Dialect(_)
                | Ty::Storage(_)
                | Ty::Tensor(..)
                | Ty::Handle(_),
                other @ (Constant::Array(_)
                | Constant::Int(_)
                | Constant::U128(_)
                | Constant::Bytes { .. }
                | Constant::Float(_)
                | Constant::Bool(_)
                | Constant::Aggregate(_)
                | Constant::Vector(_)
                | Constant::Sequence(_)
                | Constant::Set(_)
                | Constant::Record(_)
                | Constant::Closure { .. }
                | Constant::FnDef(_)
                | Constant::SymbolAddr { .. }
                | Constant::PhantomData),
            ) => Err(format!(
                "no Clean IRConst image for a global initializer of the form {} at type {ty}: \
                 an array-typed global takes `array[…]`, a struct/tuple-typed one `{{…}}`",
                constant_variant_name(other)
            )),
            // trust-ir v50 (`ARRAY_SPLAT_FORMAT_VERSION`): `len` copies of one
            // element, the ONE spelling trust-ir §3.1 allows for a uniform
            // array of two or more elements. Clean's `IRConst` has no repeat
            // constructor, so the only image would be `len` copies of the
            // element: a projection whose size follows the array's LENGTH, not
            // the artifact's size. Refused by name at every type, reading
            // neither the element nor the length, until Clean's core gains a
            // constant-size image.
            (
                Ty::Array(..)
                | Ty::Struct(_)
                | Ty::Tuple(_)
                | Ty::Ptr
                | Ty::PtrConst(_)
                | Ty::PtrMut(_)
                | Ty::Ref(_)
                | Ty::RefMut(_)
                | Ty::I8
                | Ty::I16
                | Ty::I32
                | Ty::I64
                | Ty::I128
                | Ty::U8
                | Ty::U16
                | Ty::U32
                | Ty::U64
                | Ty::U128
                | Ty::Isize
                | Ty::Usize
                | Ty::Char
                | Ty::Error
                | Ty::F16
                | Ty::F32
                | Ty::F64
                | Ty::Bool
                | Ty::Unit
                | Ty::Never
                | Ty::Enum(_)
                | Ty::Rc(_)
                | Ty::Vector(..)
                | Ty::FatPtr(_)
                | Ty::Func(_)
                | Ty::Set(..)
                | Ty::Sequence(_)
                | Ty::Record(_)
                | Ty::Closure(_)
                | Ty::Refine(..)
                | Ty::Dialect(_)
                | Ty::Storage(_)
                | Ty::Tensor(..)
                | Ty::Handle(_),
                Constant::Splat { .. },
            ) => Err(String::from(
                "no Clean IRConst image for a global initializer of the form Splat: a uniform \
                 array (trust-ir v50) has no constant-size IRConst image, and this projector \
                 does not expand it element by element",
            )),
            // trust-ir v70: a content-addressed weight blob is a tensor value whose
            // bytes live in the module's blob table; Clean's `IRConst` has no
            // tensor image. Refused by name at every type, reading neither the
            // digest nor the extents.
            (
                Ty::Array(..)
                | Ty::Struct(_)
                | Ty::Tuple(_)
                | Ty::Ptr
                | Ty::PtrConst(_)
                | Ty::PtrMut(_)
                | Ty::Ref(_)
                | Ty::RefMut(_)
                | Ty::I8
                | Ty::I16
                | Ty::I32
                | Ty::I64
                | Ty::I128
                | Ty::U8
                | Ty::U16
                | Ty::U32
                | Ty::U64
                | Ty::U128
                | Ty::Isize
                | Ty::Usize
                | Ty::Char
                | Ty::Error
                | Ty::F16
                | Ty::F32
                | Ty::F64
                | Ty::Bool
                | Ty::Unit
                | Ty::Never
                | Ty::Enum(_)
                | Ty::Rc(_)
                | Ty::Vector(..)
                | Ty::FatPtr(_)
                | Ty::Func(_)
                | Ty::Set(..)
                | Ty::Sequence(_)
                | Ty::Record(_)
                | Ty::Closure(_)
                | Ty::Refine(..)
                | Ty::Dialect(_)
                | Ty::Storage(_)
                | Ty::Tensor(..)
                | Ty::Handle(_),
                Constant::TensorBlob { .. },
            ) => Err(String::from(
                "no Clean IRConst image for a global initializer of the form TensorBlob: a \
                 content-addressed tensor weight (trust-ir v70) has no IRConst image",
            )),
            // trust-ir D1b: the extension lane is uninhabited in this build.
            (
                Ty::Array(..)
                | Ty::Struct(_)
                | Ty::Tuple(_)
                | Ty::Ptr
                | Ty::PtrConst(_)
                | Ty::PtrMut(_)
                | Ty::Ref(_)
                | Ty::RefMut(_)
                | Ty::I8
                | Ty::I16
                | Ty::I32
                | Ty::I64
                | Ty::I128
                | Ty::U8
                | Ty::U16
                | Ty::U32
                | Ty::U64
                | Ty::U128
                | Ty::Isize
                | Ty::Usize
                | Ty::Char
                | Ty::Error
                | Ty::F16
                | Ty::F32
                | Ty::F64
                | Ty::Bool
                | Ty::Unit
                | Ty::Never
                | Ty::Enum(_)
                | Ty::Rc(_)
                | Ty::Vector(..)
                | Ty::FatPtr(_)
                | Ty::Func(_)
                | Ty::Set(..)
                | Ty::Sequence(_)
                | Ty::Record(_)
                | Ty::Closure(_)
                | Ty::Refine(..)
                | Ty::Dialect(_)
                | Ty::Storage(_)
                | Ty::Tensor(..)
                | Ty::Handle(_),
                Constant::Ext(e),
            ) => e.unreachable(),
            // trust-ir v49 (`UNINIT_LANE_FORMAT_VERSION`): an UNWRITTEN
            // struct/tuple lane. trust-ir-build's validator already refuses it
            // in a global initializer, so reaching this arm means the module
            // was never validated; refused by name at every type either way.
            (
                Ty::Array(..)
                | Ty::Struct(_)
                | Ty::Tuple(_)
                | Ty::Ptr
                | Ty::PtrConst(_)
                | Ty::PtrMut(_)
                | Ty::Ref(_)
                | Ty::RefMut(_)
                | Ty::I8
                | Ty::I16
                | Ty::I32
                | Ty::I64
                | Ty::I128
                | Ty::U8
                | Ty::U16
                | Ty::U32
                | Ty::U64
                | Ty::U128
                | Ty::Isize
                | Ty::Usize
                | Ty::Char
                | Ty::Error
                | Ty::F16
                | Ty::F32
                | Ty::F64
                | Ty::Bool
                | Ty::Unit
                | Ty::Never
                | Ty::Enum(_)
                | Ty::Rc(_)
                | Ty::Vector(..)
                | Ty::FatPtr(_)
                | Ty::Func(_)
                | Ty::Set(..)
                | Ty::Sequence(_)
                | Ty::Record(_)
                | Ty::Closure(_)
                | Ty::Refine(..)
                | Ty::Dialect(_)
                | Ty::Storage(_)
                | Ty::Tensor(..)
                | Ty::Handle(_),
                Constant::Uninit,
            ) => Err(String::from(
                "no Clean IRConst image for a global initializer of the form Uninit: an \
                 unwritten aggregate lane (trust-ir v49) is admissible only as a direct lane \
                 of a struct/tuple `Const`, never as a global initializer",
            )),
        }
    }

    /// One element of a struct/tuple global's initializer. A relocatable
    /// FUNCTION address (`symaddr<name>`, addend 0) is the one element form a
    /// body's `cst` never meets: it images as the `(cfunc k)` of the module
    /// function of EXACTLY that name, which is what the machine's
    /// `ir_callind_exec` dispatches on. A name no function carries, a name two
    /// carry, or a nonzero addend is refused; a data-global address has no
    /// image. Nested aggregates recurse; every other element is `cst`.
    fn global_elem(&mut self, module: &trust_ir::Module, c: &Constant) -> R<String> {
        match c {
            Constant::SymbolAddr { symbol, addend: 0 } => {
                let mut named = module.functions.iter().filter(|f| f.name == *symbol);
                let (Some(f), None) = (named.next(), named.next()) else {
                    return Err(format!(
                        "symaddr<{symbol}> names no function, or several, of the artifact: \
                         only the address of exactly one module function has an image"
                    ));
                };
                Ok(format!("(cfunc {})", self.func_id(f.id.0)))
            }
            Constant::Aggregate(v) => {
                let mut s = String::from("(agg");
                for e in v {
                    s.push(' ');
                    s.push_str(&self.global_elem(module, e)?);
                }
                s.push(')');
                Ok(s)
            }
            // Every other element is a body constant, imaged (or refused) by
            // `cst` -- a `symaddr` with a nonzero addend included, and trust-ir
            // v50's uniform array, which `cst` refuses by name without reading
            // its element or length. Named, not wildcarded, for the reason `ty`
            // gives.
            other @ (Constant::Int(_)
            | Constant::U128(_)
            | Constant::Bytes { .. }
            | Constant::Float(_)
            | Constant::Bool(_)
            | Constant::Array(_)
            | Constant::Vector(_)
            | Constant::Sequence(_)
            | Constant::Set(_)
            | Constant::Record(_)
            | Constant::Closure { .. }
            | Constant::FnDef(_)
            | Constant::SymbolAddr { .. }
            | Constant::PhantomData
            | Constant::Splat { .. }) => self.cst(other),
            // trust-ir v49 (`UNINIT_LANE_FORMAT_VERSION`): trust-ir-build's
            // validator (`validate_uninit_lanes`) refuses an unwritten lane
            // ANYWHERE in a global initializer, nested lanes included, so it
            // is refused here by name as well rather than handed to `cst`.
            Constant::Uninit => Err(String::from(
                "no Clean IRConst image for Constant::Uninit as an element of a global \
                 initializer: an unwritten aggregate lane (trust-ir v49) is admissible only \
                 as a direct lane of a struct/tuple `Const`, never in a global initializer",
            )),
            // trust-ir v70: a content-addressed weight blob is a tensor value
            // whose bytes live in the module's blob table; EvalIR has no tensor
            // value, so it is refused by name rather than handed to `cst`.
            Constant::TensorBlob { .. } => Err(String::from(
                "no Clean IRConst image for Constant::TensorBlob (a content-addressed tensor \
                 weight, trust-ir v70) in a global initializer",
            )),
            Constant::Ext(e) => e.unreachable(),
        }
    }

    fn cst(&mut self, c: &Constant) -> R<String> {
        Ok(match c {
            Constant::Ext(e) => e.unreachable(),
            Constant::Int(v) => {
                if *v < 0 {
                    return Err(format!("negative Constant::Int({v}) has no Nat image"));
                }
                format!("(int {v})")
            }
            Constant::U128(v) => format!("(int {v})"),
            Constant::Bool(b) => format!("(bool {b})"),
            Constant::FnDef(id) => format!("(cfunc {})", self.func_id(id.0)),
            Constant::Float(x) => format!("(float {})", x.to_bits()),
            Constant::Aggregate(v) => {
                let mut s = String::from("(agg");
                for e in v {
                    s.push(' ');
                    s.push_str(&self.cst(e)?);
                }
                s.push(')');
                s
            }
            // The zero-sized marker. Imaged 2026-09-16, when this refusal is
            // what stopped `tc::heartbeat::tick_heartbeat` -- the one callee
            // whose absence makes infer_type's call closure cyclic -- from
            // projecting at all. A separate Clean constructor rather than a
            // rewrite to `unit`, because the producer keeps the two distinct
            // (trust_ir constant.rs:140) and a reader that silently merged them
            // would make two different emitted bodies project to one core.
            Constant::PhantomData => String::from("(phantomdata)"),
            // Named, not wildcarded, for the reason `ty` gives. `Array` is
            // refused HERE and accepted only by `global_init`: the position a
            // `(agg …)` is read from is what keeps the two shapes apart.
            other @ (Constant::Bytes { .. }
            | Constant::Array(_)
            | Constant::Vector(_)
            | Constant::Sequence(_)
            | Constant::Set(_)
            | Constant::Record(_)
            | Constant::Closure { .. }
            | Constant::SymbolAddr { .. }) => {
                return Err(format!("no Clean IRConst image for {other:?}"))
            }
            // trust-ir v49: an UNWRITTEN struct/tuple lane. It is the absence
            // of a value, typed only by its position in the enclosing
            // aggregate, and trust-ir forbids reading it. Whether Clean images
            // it (EvalIR's `undef_` lane is the candidate) is the crystal
            // lane's decision; until one is made and tested, this reader
            // refuses it by name rather than invent an image -- in particular
            // it is NOT `(undef …)`, which spells a havoc, an unknown VALUE.
            Constant::Uninit => {
                return Err(String::from(
                    "no Clean IRConst image for Constant::Uninit (an unwritten aggregate lane, \
                     trust-ir v49): not yet imaged by this projector",
                ))
            }
            // trust-ir v50: the uniform array. `Array` is refused in this
            // position (it reads only as a global initializer), and so is its
            // one-spelling twin; `global_init` says why it has no image there
            // either. Neither the element nor the length is read.
            Constant::Splat { .. } => {
                return Err(String::from(
                    "no Clean IRConst image for Constant::Splat (a uniform array, trust-ir \
                     v50): an array constant has no image inside a `const` node",
                ))
            }
            // trust-ir v70: a weight blob names tensor elements by digest;
            // EvalIR has no tensor value. Neither the digest nor the extents
            // are read.
            Constant::TensorBlob { .. } => {
                return Err(String::from(
                    "no Clean IRConst image for Constant::TensorBlob (a content-addressed \
                     tensor weight, trust-ir v70)",
                ))
            }
        })
    }

    /// Crystal D10 (decision memo §15): the EvalIR image of a NATIVE atomic instruction under the
    /// premise SEQ ([`SEQ_PREMISE`]) -- the sequence of existing `IRInst` nodes that computes, in
    /// a run no other thread interleaves with, exactly what the atomic computes: its result and
    /// the memory it leaves. `None` for every other instruction (the caller then images it with
    /// [`Projector::inst`]). No `IRInst` constructor is added and `ir_exec` is unchanged; the
    /// trust-ir module keeps the native op, so what is proved is still what codegen reads.
    ///
    /// Under SEQ every ordering is sequentially consistent with nothing to order against, so an
    /// ordering is read and imaged by nothing and a `fence` has an EMPTY image. An `atomicrmw`
    /// whose op the image does not compute exactly without new machinery (`max`/`min`/`umax`/
    /// `umin`: a comparison whose signedness the op name carries) is REFUSED by name, as is
    /// a WEAK compare-exchange, which may fail spuriously where the strong image cannot (the
    /// pinned trust-ir decodes its `weak` flag since v48; before that it never arrived).
    fn seq_atomic_image(
        &mut self,
        n: &trust_ir::InstrNode,
        fresh: &mut u32,
    ) -> R<Option<Vec<String>>> {
        use trust_ir::inst::AtomicRMWOp as A;
        let one = |n: &trust_ir::InstrNode, what: &str| -> R<u32> {
            match n.results.as_slice() {
                [r] => Ok(r.0),
                other => Err(format!(
                    "{what} binds {} results, its image binds one",
                    other.len()
                )),
            }
        };
        let nodes = match &n.inst {
            Inst::AtomicLoad { ty, ptr, .. } => {
                let r = one(n, "atomic_load")?;
                vec![format!(
                    "(node (results {r}) (load {} {} false))",
                    self.ty(ty)?,
                    ptr.0
                )]
            }
            Inst::AtomicStore { ty, ptr, value, .. } => {
                if !n.results.is_empty() {
                    return Err("atomic_store binds a result; its image binds none".into());
                }
                vec![format!(
                    "(node (results) (store {} {} {} false))",
                    self.ty(ty)?,
                    ptr.0,
                    value.0
                )]
            }
            Inst::AtomicRMW {
                op, ty, ptr, value, ..
            } => {
                let r = one(n, "atomicrmw")?;
                let t = self.ty(ty)?;
                let load = format!("(node (results {r}) (load {t} {} false))", ptr.0);
                let binop = match op {
                    A::Xchg => None,
                    A::Add => Some("add"),
                    A::Sub => Some("sub"),
                    A::And => Some("and"),
                    A::Or => Some("or"),
                    A::Xor => Some("xor"),
                    A::Max | A::Min | A::UMax | A::UMin => {
                        return Err(format!(
                        "no SEQ image for `atomicrmw {op:?}` (D10 images xchg/add/sub/and/or/xor)"
                    ))
                    }
                };
                match binop {
                    None => vec![
                        load,
                        format!("(node (results) (store {t} {} {} false))", ptr.0, value.0),
                    ],
                    Some(b) => {
                        let new = *fresh;
                        *fresh += 1;
                        vec![
                            load,
                            format!("(node (results {new}) (binop {b} {t} {r} {}))", value.0),
                            format!("(node (results) (store {t} {} {new} false))", ptr.0),
                        ]
                    }
                }
            }
            Inst::CmpXchg {
                ty,
                ptr,
                expected,
                desired,
                weak,
                ..
            } => {
                // trust-ir v48 decodes the `weak` flag (the pinned trust-ir
                // before it could not read a weak CAS at all). A weak CAS may
                // FAIL SPURIOUSLY with the expected value in memory, even in a
                // run no other thread interleaves with, so the strong image
                // below would delete a behaviour: refused by name.
                if *weak {
                    return Err(String::from(
                        "no Clean IRInst image for a WEAK cmpxchg under premise SEQ: it may fail \
                         spuriously, which the strong load/icmp/select/store image deletes \
                         (trust-ir v48 `weak`)",
                    ));
                }
                let [old, ok] = n.results.as_slice() else {
                    return Err(format!(
                        "cmpxchg binds {} results, its image binds two",
                        n.results.len()
                    ));
                };
                let t = self.ty(ty)?;
                let new = *fresh;
                *fresh += 1;
                vec![
                    format!("(node (results {}) (load {t} {} false))", old.0, ptr.0),
                    format!(
                        "(node (results {}) (icmp eq {t} {} {}))",
                        ok.0, old.0, expected.0
                    ),
                    format!(
                        "(node (results {new}) (select {t} {} {} {}))",
                        ok.0, desired.0, old.0
                    ),
                    format!("(node (results) (store {t} {} {new} false))", ptr.0),
                ]
            }
            Inst::Fence { .. } => {
                if !n.results.is_empty() {
                    return Err("fence binds a result; its image binds none".into());
                }
                Vec::new()
            }
            // Every other instruction is not a native atomic: `inst` images it.
            // Named, not wildcarded, for the reason `ty` gives -- a variant
            // trust-ir adds fails to compile here until someone decides whether
            // it is an atomic this image must compute.
            Inst::BinOp { .. }
            | Inst::UnOp { .. }
            | Inst::Overflow { .. }
            | Inst::ICmp { .. }
            | Inst::FCmp { .. }
            | Inst::Cast { .. }
            | Inst::Load { .. }
            | Inst::Store { .. }
            | Inst::Alloca { .. }
            | Inst::Borrow { .. }
            | Inst::BorrowMut { .. }
            | Inst::Copy { .. }
            | Inst::GEP { .. }
            | Inst::PtrData { .. }
            | Inst::PtrMetadata { .. }
            | Inst::PtrFromParts { .. }
            | Inst::Br { .. }
            | Inst::CondBr { .. }
            | Inst::Switch { .. }
            | Inst::Call { .. }
            | Inst::CallIndirect { .. }
            | Inst::Return { .. }
            | Inst::ExtractField { .. }
            | Inst::InsertField { .. }
            | Inst::ExtractElement { .. }
            | Inst::Const { .. }
            | Inst::GlobalAddr { .. }
            | Inst::Undef { .. }
            | Inst::Assert { .. }
            | Inst::Unreachable
            | Inst::Select { .. }
            | Inst::MemCopy { .. }
            | Inst::MemSet { .. }
            | Inst::HeapAlloc { .. }
            | Inst::InsertElement { .. }
            | Inst::NullPtr
            | Inst::Assume { .. }
            | Inst::SeqMapAddK { .. }
            | Inst::SeqMapNot { .. }
            | Inst::SeqMap { .. }
            | Inst::EndBorrow { .. }
            | Inst::Retain { .. }
            | Inst::Release { .. }
            | Inst::IsUnique { .. }
            | Inst::Dealloc { .. }
            | Inst::OpenFrame { .. }
            | Inst::BindSlot { .. }
            | Inst::LoadSlot { .. }
            | Inst::CloseFrame { .. }
            | Inst::CoroSuspend { .. }
            | Inst::Invoke { .. }
            | Inst::LandingPad { .. }
            | Inst::Resume { .. }
            | Inst::AssertInvoke { .. }
            | Inst::ArraySplat { .. }
            | Inst::CallCannotUnwind { .. }
            | Inst::CallIndirectCannotUnwind { .. }
            | Inst::DropInvoke { .. }
            | Inst::InvokeIndirect { .. }
            | Inst::DialectOp(..)
            // trust-ir v47's destructor run is no atomic; `inst` refuses it.
            | Inst::Drop { .. }
            | Inst::MakeAggregate { .. }
            | Inst::TensorContract { .. }
            | Inst::TensorMap { .. }
            | Inst::TensorReduce { .. }
            | Inst::TensorView { .. }
            | Inst::TensorGather { .. }
            | Inst::TensorScatter { .. }
            | Inst::MakeClosure { .. } => return Ok(None),
        };
        self.seq_atomic_images += 1;
        Ok(Some(nodes))
    }

    /// Crystal D11 (decision memo §17): the EvalIR image of a `trust_rust.thread_local_addr` op
    /// under the premise TLS ([`TLS_PREMISE`]) -- `(globaladdr k)` of the INPUT cell `k` its
    /// symbol names, one cell per distinct symbol, sharing the canonical global namespace. `None`
    /// for every other instruction. Only a symbol the callee sidecar's manifest CERTIFIES
    /// (`--tls-cells`) is imaged; any other `trust_rust.thread_local_addr`, and every other
    /// dialect op, is refused by name. No `IRInst` constructor is added and `ir_exec` is
    /// unchanged; the trust-ir module keeps the op, so what is proved is what codegen reads.
    fn tls_input_image(&mut self, n: &trust_ir::InstrNode) -> R<Option<Vec<String>>> {
        let op = match &n.inst {
            Inst::DialectOp(op) => op,
            // Every other instruction is no dialect op, so it has no D11 image. Named, not the
            // `else` of a `let .. else` (main's lint r11 refuses that catch-all): a variant
            // trust-ir adds fails to compile here until someone says whether it is one.
            Inst::Call { .. }
            | Inst::Drop { .. }
            | Inst::Invoke { .. }
            | Inst::CallIndirect { .. }
            | Inst::SeqMap { .. }
            | Inst::GlobalAddr { .. }
            | Inst::Const { .. }
            | Inst::BinOp { .. }
            | Inst::UnOp { .. }
            | Inst::Overflow { .. }
            | Inst::ICmp { .. }
            | Inst::FCmp { .. }
            | Inst::Cast { .. }
            | Inst::Load { .. }
            | Inst::Store { .. }
            | Inst::Alloca { .. }
            | Inst::HeapAlloc { .. }
            | Inst::GEP { .. }
            | Inst::PtrData { .. }
            | Inst::PtrMetadata { .. }
            | Inst::PtrFromParts { .. }
            | Inst::AtomicLoad { .. }
            | Inst::AtomicStore { .. }
            | Inst::AtomicRMW { .. }
            | Inst::CmpXchg { .. }
            | Inst::Fence { .. }
            | Inst::Br { .. }
            | Inst::CondBr { .. }
            | Inst::Switch { .. }
            | Inst::Return { .. }
            | Inst::ExtractField { .. }
            | Inst::InsertField { .. }
            | Inst::ExtractElement { .. }
            | Inst::InsertElement { .. }
            | Inst::NullPtr
            | Inst::Undef { .. }
            | Inst::Assume { .. }
            | Inst::Assert { .. }
            | Inst::Unreachable
            | Inst::Copy { .. }
            | Inst::Select { .. }
            | Inst::SeqMapAddK { .. }
            | Inst::SeqMapNot { .. }
            | Inst::Borrow { .. }
            | Inst::BorrowMut { .. }
            | Inst::EndBorrow { .. }
            | Inst::Retain { .. }
            | Inst::Release { .. }
            | Inst::IsUnique { .. }
            | Inst::Dealloc { .. }
            | Inst::MemCopy { .. }
            | Inst::MemSet { .. }
            | Inst::OpenFrame { .. }
            | Inst::BindSlot { .. }
            | Inst::LoadSlot { .. }
            | Inst::CloseFrame { .. }
            | Inst::CoroSuspend { .. }
            | Inst::LandingPad { .. }
            | Inst::Resume { .. }
            | Inst::AssertInvoke { .. }
            | Inst::ArraySplat { .. }
            | Inst::CallCannotUnwind { .. }
            | Inst::CallIndirectCannotUnwind { .. }
            | Inst::DropInvoke { .. }
            | Inst::InvokeIndirect { .. }
            | Inst::MakeAggregate { .. }
            | Inst::TensorContract { .. }
            | Inst::TensorMap { .. }
            | Inst::TensorReduce { .. }
            | Inst::TensorView { .. }
            | Inst::TensorGather { .. }
            | Inst::TensorScatter { .. }
            | Inst::MakeClosure { .. } => return Ok(None),
        };
        let spec = trust_ir::dialect::trust_rust::decode_thread_local_addr(op).map_err(|e| {
            format!(
                "no Clean IRInst image for trust_ir::Inst::DialectOp `{}.{}` ({e:?}): only a \
                 certified trust_rust.thread_local_addr has one (D11)",
                op.dialect, op.op
            )
        })?;
        let [r] = n.results.as_slice() else {
            return Err(format!(
                "trust_rust.thread_local_addr binds {} results, its image binds one",
                n.results.len()
            ));
        };
        if !self.tls_certified.contains_key(spec.symbol) {
            return Err(format!(
                "no D11 image for trust_rust.thread_local_addr [symbol={}]: no certified \
                 `tls_cells` row names it (pass the callee sidecar's manifest with --tls-cells)",
                spec.symbol
            ));
        }
        let j = match self.tls_cells.iter().position(|(_, s)| s == spec.symbol) {
            Some(j) => j,
            None => {
                self.tls_cells.push((u32::MAX, spec.symbol.to_string()));
                self.tls_cells.len() - 1
            }
        };
        self.tls_input_images += 1;
        // The cell's id is fixed in `project_chain`, after every artifact global (never 0).
        Ok(Some(vec![format!(
            "(node (results {}) (globaladdr {}))",
            r.0,
            tls_placeholder(j)
        )]))
    }

    /// Crystal D12 (decision memo §18, the lead's ruling; `--ptr-bitcast-identity`): a `bitcast`
    /// between IDENTICAL types preserves the value, so its EvalIR image is `copy` at that type,
    /// which is exact. ONLY
    /// `ptr -> ptr`: trust-ir's reference interpreter runs it as `expect_ty(operand, ptr)`, a width
    /// check both sides pass, and `eval_bitcast`'s `src_ty == dst_ty => operand` identity arm;
    /// EvalIR's `copy (ptr)` is its shape check and the same rebind. A bitcast between DIFFERENT
    /// types keeps its `(cast bitcast ..)` image, which EvalIR decides only for two integers of
    /// one width (`ir_bitcast_eval`). `None` for every other instruction.
    fn ptr_bitcast_identity_image(&mut self, n: &trust_ir::InstrNode) -> R<Option<Vec<String>>> {
        if !self.ptr_bitcast_identity {
            return Ok(None);
        }
        let (op, src_ty, dst_ty, operand) = match &n.inst {
            Inst::Cast {
                op,
                src_ty,
                dst_ty,
                operand,
            } => (op, src_ty, dst_ty, operand),
            // Every other instruction is no cast. Named, not the `else` of a `let .. else`
            // (main's lint r11 refuses that catch-all).
            Inst::Call { .. }
            | Inst::Drop { .. }
            | Inst::Invoke { .. }
            | Inst::CallIndirect { .. }
            | Inst::SeqMap { .. }
            | Inst::GlobalAddr { .. }
            | Inst::DialectOp(..)
            | Inst::Const { .. }
            | Inst::BinOp { .. }
            | Inst::UnOp { .. }
            | Inst::Overflow { .. }
            | Inst::ICmp { .. }
            | Inst::FCmp { .. }
            | Inst::Load { .. }
            | Inst::Store { .. }
            | Inst::Alloca { .. }
            | Inst::HeapAlloc { .. }
            | Inst::GEP { .. }
            | Inst::PtrData { .. }
            | Inst::PtrMetadata { .. }
            | Inst::PtrFromParts { .. }
            | Inst::AtomicLoad { .. }
            | Inst::AtomicStore { .. }
            | Inst::AtomicRMW { .. }
            | Inst::CmpXchg { .. }
            | Inst::Fence { .. }
            | Inst::Br { .. }
            | Inst::CondBr { .. }
            | Inst::Switch { .. }
            | Inst::Return { .. }
            | Inst::ExtractField { .. }
            | Inst::InsertField { .. }
            | Inst::ExtractElement { .. }
            | Inst::InsertElement { .. }
            | Inst::NullPtr
            | Inst::Undef { .. }
            | Inst::Assume { .. }
            | Inst::Assert { .. }
            | Inst::Unreachable
            | Inst::Copy { .. }
            | Inst::Select { .. }
            | Inst::SeqMapAddK { .. }
            | Inst::SeqMapNot { .. }
            | Inst::Borrow { .. }
            | Inst::BorrowMut { .. }
            | Inst::EndBorrow { .. }
            | Inst::Retain { .. }
            | Inst::Release { .. }
            | Inst::IsUnique { .. }
            | Inst::Dealloc { .. }
            | Inst::MemCopy { .. }
            | Inst::MemSet { .. }
            | Inst::OpenFrame { .. }
            | Inst::BindSlot { .. }
            | Inst::LoadSlot { .. }
            | Inst::CloseFrame { .. }
            | Inst::CoroSuspend { .. }
            | Inst::LandingPad { .. }
            | Inst::Resume { .. }
            | Inst::AssertInvoke { .. }
            | Inst::ArraySplat { .. }
            | Inst::CallCannotUnwind { .. }
            | Inst::CallIndirectCannotUnwind { .. }
            | Inst::DropInvoke { .. }
            | Inst::InvokeIndirect { .. }
            | Inst::MakeAggregate { .. }
            | Inst::TensorContract { .. }
            | Inst::TensorMap { .. }
            | Inst::TensorReduce { .. }
            | Inst::TensorView { .. }
            | Inst::TensorGather { .. }
            | Inst::TensorScatter { .. }
            | Inst::MakeClosure { .. } => return Ok(None),
        };
        // Named matches, not a nested pattern (a `Cast` pattern naming `Bitcast` and `Ty::Ptr`
        // needs an alternative that leaves those fields out, which main's lint r11 refuses) and
        // not equalities (lint r11b refuses a variant told apart by value).
        if !(cast_is_bitcast(op) && ty_is_bare_ptr(src_ty) && ty_is_bare_ptr(dst_ty)) {
            return Ok(None);
        }
        let [r] = n.results.as_slice() else {
            return Err(format!(
                "bitcast ptr -> ptr binds {} results, its image binds one",
                n.results.len()
            ));
        };
        self.ptr_bitcast_identities += 1;
        Ok(Some(vec![format!(
            "(node (results {}) (copy (ptr) {}))",
            r.0, operand.0
        )]))
    }

    /// Crystal (decision memo §18): a NEGATIVE `Constant::Int(v)` at an integer type of width W.
    /// EvalIR carries an integer as a width-W BIT PATTERN in a Nat (`ir_const_int_eval` reduces
    /// the stored Nat with `ir_wrap W`; `ir_sext_value` and the signed comparisons read it back
    /// two's-complement), and trust-ir's reference interpreter builds the same pattern
    /// (`InterpretInt::from_i128`: `(v as u128) & mask(W)`). So the image is `(int P)` with `P`
    /// that pattern -- exact, for a signed or an unsigned type alike. A `usize`/`isize` needs the
    /// pinned `--usize-bits` (otherwise `None`, and the ordinary arm refuses the type); a
    /// non-integer type, and a negative constant inside an aggregate or a global, keep their
    /// refusal. `None` for every other instruction.
    fn negative_int_const_image(&mut self, n: &trust_ir::InstrNode) -> R<Option<Vec<String>>> {
        let (ty, v) = match &n.inst {
            Inst::Const {
                ty,
                value: Constant::Int(v),
            } => (ty, v),
            // Every other constant, and every other instruction, NAMED (the `else` of a `let ..
            // else` until main's lint r11 refused it as a catch-all).
            Inst::Const {
                value:
                    Constant::U128(_)
                    | Constant::Bytes { .. }
                    | Constant::Float(_)
                    | Constant::Bool(_)
                    | Constant::Array(_)
                    | Constant::Aggregate(_)
                    | Constant::Vector(_)
                    | Constant::Sequence(_)
                    | Constant::Set(_)
                    | Constant::Record(_)
                    | Constant::Closure { .. }
                    | Constant::FnDef(_)
                    | Constant::SymbolAddr { .. }
                    | Constant::PhantomData
                    | Constant::Uninit
                    | Constant::TensorBlob { .. }
                    | Constant::Splat { .. },
                ..
            } => return Ok(None),
            Inst::Const {
                value: Constant::Ext(e),
                ..
            } => e.unreachable(),
            Inst::Call { .. }
            | Inst::Drop { .. }
            | Inst::Invoke { .. }
            | Inst::CallIndirect { .. }
            | Inst::SeqMap { .. }
            | Inst::GlobalAddr { .. }
            | Inst::DialectOp(..)
            | Inst::BinOp { .. }
            | Inst::UnOp { .. }
            | Inst::Overflow { .. }
            | Inst::ICmp { .. }
            | Inst::FCmp { .. }
            | Inst::Cast { .. }
            | Inst::Load { .. }
            | Inst::Store { .. }
            | Inst::Alloca { .. }
            | Inst::HeapAlloc { .. }
            | Inst::GEP { .. }
            | Inst::PtrData { .. }
            | Inst::PtrMetadata { .. }
            | Inst::PtrFromParts { .. }
            | Inst::AtomicLoad { .. }
            | Inst::AtomicStore { .. }
            | Inst::AtomicRMW { .. }
            | Inst::CmpXchg { .. }
            | Inst::Fence { .. }
            | Inst::Br { .. }
            | Inst::CondBr { .. }
            | Inst::Switch { .. }
            | Inst::Return { .. }
            | Inst::ExtractField { .. }
            | Inst::InsertField { .. }
            | Inst::ExtractElement { .. }
            | Inst::InsertElement { .. }
            | Inst::NullPtr
            | Inst::Undef { .. }
            | Inst::Assume { .. }
            | Inst::Assert { .. }
            | Inst::Unreachable
            | Inst::Copy { .. }
            | Inst::Select { .. }
            | Inst::SeqMapAddK { .. }
            | Inst::SeqMapNot { .. }
            | Inst::Borrow { .. }
            | Inst::BorrowMut { .. }
            | Inst::EndBorrow { .. }
            | Inst::Retain { .. }
            | Inst::Release { .. }
            | Inst::IsUnique { .. }
            | Inst::Dealloc { .. }
            | Inst::MemCopy { .. }
            | Inst::MemSet { .. }
            | Inst::OpenFrame { .. }
            | Inst::BindSlot { .. }
            | Inst::LoadSlot { .. }
            | Inst::CloseFrame { .. }
            | Inst::CoroSuspend { .. }
            | Inst::LandingPad { .. }
            | Inst::Resume { .. }
            | Inst::AssertInvoke { .. }
            | Inst::ArraySplat { .. }
            | Inst::CallCannotUnwind { .. }
            | Inst::CallIndirectCannotUnwind { .. }
            | Inst::DropInvoke { .. }
            | Inst::InvokeIndirect { .. }
            | Inst::MakeAggregate { .. }
            | Inst::TensorContract { .. }
            | Inst::TensorMap { .. }
            | Inst::TensorReduce { .. }
            | Inst::TensorView { .. }
            | Inst::TensorGather { .. }
            | Inst::TensorScatter { .. }
            | Inst::MakeClosure { .. } => return Ok(None),
        };
        if *v >= 0 {
            return Ok(None);
        }
        let width: u32 = match ty {
            Ty::I8 | Ty::U8 => 8,
            Ty::I16 | Ty::U16 => 16,
            Ty::I32 | Ty::U32 => 32,
            Ty::I64 | Ty::U64 => 64,
            Ty::I128 | Ty::U128 => 128,
            Ty::Usize | Ty::Isize => match self.usize_bits {
                Some(b) if (1..=128).contains(&b) => b,
                Some(_) | None => return Ok(None),
            },
            // Every type with no integer width, NAMED rather than wildcarded (the
            // crate root's rule): the ordinary `const` arm keeps its refusal, so a
            // variant trust-ir adds fails to compile here until someone decides
            // whether it carries a bit pattern.
            Ty::Bool
            | Ty::Char
            | Ty::Error
            | Ty::F16
            | Ty::F32
            | Ty::F64
            | Ty::Ptr
            | Ty::Unit
            | Ty::Never
            | Ty::Struct(_)
            | Ty::Enum(_)
            | Ty::Ref(_)
            | Ty::RefMut(_)
            | Ty::PtrConst(_)
            | Ty::PtrMut(_)
            | Ty::Rc(_)
            | Ty::FatPtr(_)
            | Ty::Tuple(_)
            | Ty::Func(_)
            | Ty::Vector(..)
            | Ty::Array(..)
            | Ty::Set(..)
            | Ty::Sequence(_)
            | Ty::Record(_)
            | Ty::Closure(_)
            | Ty::Refine(..)
            | Ty::Dialect(_)
            | Ty::Tensor(..)
            | Ty::Storage(_)
            | Ty::Handle(_) => return Ok(None),
            Ty::Ext(e) => e.unreachable(),
        };
        let [r] = n.results.as_slice() else {
            return Err(format!(
                "const binds {} results, its image binds one",
                n.results.len()
            ));
        };
        let mask = if width >= 128 {
            u128::MAX
        } else {
            (1u128 << width) - 1
        };
        // Two's complement: the reinterpretation of the i128 carrier, masked to W bits.
        #[allow(clippy::cast_sign_loss)]
        let pattern = (*v as u128) & mask;
        let t = self.ty(ty)?;
        self.negative_int_images += 1;
        Ok(Some(vec![format!(
            "(node (results {}) (const {t} (int {pattern})))",
            r.0
        )]))
    }

    /// Crystal (decision memo §15, the lead's ruling on D10, executed in §18): a reached
    /// `unreachable_unchecked` (`CallHalt::UndefinedBehavior`) is lowered by the trust bridge as
    /// `assert false` -- the SAME halting shape as a panic -- plus the obligation "reaching `X` is
    /// undefined behavior; this program point must be proven unreachable", sited at that assert.
    /// Imaged as that assert, the run halts `ub assert_failed`, which E2's device admits as a
    /// SANCTIONED panic (`eval_ir_ctr.rs` `ir_sanctioned`). So the assert AT THE OBLIGATION'S SITE
    /// images as `unreachable`, which halts `ub unreachable`: a halt the device refuses
    /// (`ir_sanctioned_unreachable`, `ir_bad_halt_unreachable`). The site must be an `assert` of a
    /// `const bool false` bound in the same block; anything else there is refused, never guessed.
    /// `None` at every other node.
    fn ub_halt_image(
        &mut self,
        f: &trust_ir::Function,
        b: &trust_ir::Block,
        k: usize,
    ) -> R<Option<Vec<String>>> {
        let Ok(k32) = u32::try_from(k) else {
            return Ok(None);
        };
        if !self.ub_halt_sites.contains(&(f.id.0, b.id.0, k32)) {
            return Ok(None);
        }
        let n = &b.body[k];
        // A `match` naming every variant (an `if let` until main's lint r11 refused its failure
        // branch as a catch-all): only an `assert` is a halt this image may replace, and
        // everything else is refused below.
        let halting = match &n.inst {
            // Kindless and siteless only: a kinded (trust-ir v52) or sited (v54) `assert` has
            // no Clean IRInst image (`inst` refuses it), so it is no halt this image replaces.
            Inst::Assert { cond, kind, site } => {
                kind.is_unspecified()
                    && site.is_none()
                    && n.results.is_empty()
                    && b.body[..k].iter().any(|m| {
                        // A named match, not `matches!` (its `_ => false` arm is a catch-all the
                        // wildcard lints never see) and not an `==` against a built
                        // `Inst::Const` (lint r11b refuses a variant told apart by value).
                        m.results.as_slice() == [*cond] && inst_is_const_bool_false(&m.inst)
                    })
            }
            Inst::Call { .. }
            | Inst::Drop { .. }
            | Inst::Invoke { .. }
            | Inst::CallIndirect { .. }
            | Inst::SeqMap { .. }
            | Inst::GlobalAddr { .. }
            | Inst::DialectOp(..)
            | Inst::Const { .. }
            | Inst::BinOp { .. }
            | Inst::UnOp { .. }
            | Inst::Overflow { .. }
            | Inst::ICmp { .. }
            | Inst::FCmp { .. }
            | Inst::Cast { .. }
            | Inst::Load { .. }
            | Inst::Store { .. }
            | Inst::Alloca { .. }
            | Inst::HeapAlloc { .. }
            | Inst::GEP { .. }
            | Inst::PtrData { .. }
            | Inst::PtrMetadata { .. }
            | Inst::PtrFromParts { .. }
            | Inst::AtomicLoad { .. }
            | Inst::AtomicStore { .. }
            | Inst::AtomicRMW { .. }
            | Inst::CmpXchg { .. }
            | Inst::Fence { .. }
            | Inst::Br { .. }
            | Inst::CondBr { .. }
            | Inst::Switch { .. }
            | Inst::Return { .. }
            | Inst::ExtractField { .. }
            | Inst::InsertField { .. }
            | Inst::ExtractElement { .. }
            | Inst::InsertElement { .. }
            | Inst::NullPtr
            | Inst::Undef { .. }
            | Inst::Assume { .. }
            | Inst::Unreachable
            | Inst::Copy { .. }
            | Inst::Select { .. }
            | Inst::SeqMapAddK { .. }
            | Inst::SeqMapNot { .. }
            | Inst::Borrow { .. }
            | Inst::BorrowMut { .. }
            | Inst::EndBorrow { .. }
            | Inst::Retain { .. }
            | Inst::Release { .. }
            | Inst::IsUnique { .. }
            | Inst::Dealloc { .. }
            | Inst::MemCopy { .. }
            | Inst::MemSet { .. }
            | Inst::OpenFrame { .. }
            | Inst::BindSlot { .. }
            | Inst::LoadSlot { .. }
            | Inst::CloseFrame { .. }
            | Inst::CoroSuspend { .. }
            | Inst::LandingPad { .. }
            | Inst::Resume { .. }
            | Inst::AssertInvoke { .. }
            | Inst::ArraySplat { .. }
            | Inst::CallCannotUnwind { .. }
            | Inst::CallIndirectCannotUnwind { .. }
            | Inst::DropInvoke { .. }
            | Inst::InvokeIndirect { .. }
            | Inst::MakeAggregate { .. }
            | Inst::TensorContract { .. }
            | Inst::TensorMap { .. }
            | Inst::TensorReduce { .. }
            | Inst::TensorView { .. }
            | Inst::TensorGather { .. }
            | Inst::TensorScatter { .. }
            | Inst::MakeClosure { .. } => false,
        };
        if !halting {
            return Err(format!(
                "`{}` bb{} #{k}: an undefined-behaviour halt obligation names this node, which is \
                 not an `assert` of a `const bool false` bound before it in the block; no image \
                 keeps it out of the sanctioned-panic arm",
                f.name, b.id.0
            ));
        }
        self.ub_halt_images += 1;
        Ok(Some(vec!["(node (results) (unreachable))".to_string()]))
    }

    #[allow(clippy::too_many_lines)]
    /// Crystal E5 (memo §23): the machine reads a wide pointer's metadata word AT the node's
    /// declared metadata type, and the reference refuses a declared type that is not the pointer
    /// type's canonical one (trust-ir `FatPtrKind::metadata_ty`: a pointer-sized unsigned length or
    /// a thin `Ty::Ptr` vtable word; `()` for a thin pointer). The machine does not re-check the
    /// PAIR, so the projector does, fail-closed; trust-ir's validator refuses the same pair
    /// statically (`PointerMetadataTypeMismatch`).
    fn check_metadata_ty(&self, op: &str, ptr_ty: &Ty, metadata_ty: &Ty) -> R<()> {
        let canonical = match fat_kind_of(ptr_ty) {
            Some(kind) => {
                let bits = self.usize_bits.ok_or_else(|| {
                    format!(
                        "{op} over `{ptr_ty}`: its canonical metadata type is pointer-sized, and \
                         this projection pins no --usize-bits"
                    )
                })?;
                kind.metadata_ty(bits).ok_or_else(|| {
                    format!("{op} over `{ptr_ty}`: no canonical metadata type at {bits} bits")
                })?
            }
            None => match vt_ty(ptr_ty) {
                VtTy::Thin => Ty::Unit,
                VtTy::Byte | VtTy::Usize | VtTy::Other => {
                    return Err(format!("{op} over `{ptr_ty}`, which is not pointer-like"))
                }
            },
        };
        // Compared through a key read off a named match, not `&canonical != metadata_ty`: main's
        // lint r11b refuses a variant told apart by value. A canonical type outside the key set
        // (none exists in trust-ir) is refused, never matched.
        let canonical_key = metadata_ty_key(&canonical);
        if canonical_key.is_none() || canonical_key != metadata_ty_key(metadata_ty) {
            return Err(format!(
                "{op}: the declared metadata type `{metadata_ty}` is not `{ptr_ty}`'s canonical \
                 `{canonical}`; the reference refuses the pair and the machine reads the word at \
                 the declared type (crystal E5)"
            ));
        }
        Ok(())
    }

    fn inst(&mut self, i: &Inst) -> R<String> {
        Ok(match i {
            Inst::BinOp { op, ty, lhs, rhs } => format!(
                "(binop {} {} {} {})",
                binop(*op)?,
                self.ty(ty)?,
                lhs.0,
                rhs.0
            ),
            Inst::UnOp { op, ty, operand } => {
                format!("(unop {} {} {})", unop(*op)?, self.ty(ty)?, operand.0)
            }
            Inst::Overflow { op, ty, lhs, rhs } => format!(
                "(overflow {} {} {} {})",
                ovop(*op),
                self.ty(ty)?,
                lhs.0,
                rhs.0
            ),
            Inst::ICmp { op, ty, lhs, rhs } => {
                format!("(icmp {} {} {} {})", icmp(*op), self.ty(ty)?, lhs.0, rhs.0)
            }
            Inst::FCmp { op, ty, lhs, rhs } => {
                format!("(fcmp {} {} {} {})", fcmp(*op), self.ty(ty)?, lhs.0, rhs.0)
            }
            Inst::Cast {
                op,
                src_ty,
                dst_ty,
                operand,
            } => format!(
                "(cast {} {} {} {})",
                cast(*op)?,
                self.ty(src_ty)?,
                self.ty(dst_ty)?,
                operand.0
            ),
            Inst::Load {
                ty,
                ptr,
                volatile,
                align,
            } => {
                self.aligns.push(format!("load:{align:?}"));
                format!("(load {} {} {volatile})", self.ty(ty)?, ptr.0)
            }
            Inst::Store {
                ty,
                ptr,
                value,
                volatile,
                align,
            } => {
                self.aligns.push(format!("store:{align:?}"));
                format!("(store {} {} {} {volatile})", self.ty(ty)?, ptr.0, value.0)
            }
            Inst::Alloca { ty, count, align } => {
                self.aligns.push(format!("alloca:{align:?}"));
                let c = match count {
                    Some(v) => format!("(some {})", v.0),
                    None => "(none)".into(),
                };
                format!("(alloca {} {c})", self.ty(ty)?)
            }
            // The trust-ir BRIDGE's two. They reach this projector for the
            // first time with the Phase-B callee bundle: the THIR lowerer
            // emits neither, and the bridge that lowers the sidecar's
            // monomorphized MIR emits both. The core forms are
            // `IRInst.borrow` `[Val]` and `IRInst.copy` `[Ty, Val]`
            // (`ir_mint::shape`), and reader B prints the same two, so the
            // two independent readers stay comparable.
            // Crystal D1: `BorrowMut` takes the SAME image as `Borrow`, because trust-ir's reference
            // interpreter executes the two in ONE arm (interpret.rs at this projector's pinned rev,
            // `Inst::Borrow { ptr } | Inst::BorrowMut { ptr } =>`: the result is the operand's
            // pointer after `expect_pointer`, a fat pointer passed through verbatim), and EvalIR's
            // `borrow` is that arm transcribed (`ir_borrow_eval`). The formal Lean model's
            // permission map (`semBorrowMut` requires the allocation `.owned`) is a borrow
            // DISCIPLINE check the reference interpreter and EvalIR both omit; wherever the Lean
            // model accepts, all three compute the same value. What the callee sidecar's closure
            // shims execute is exactly this: `&mut` of the zero-sized environment's stack slot.
            Inst::Borrow { ptr } | Inst::BorrowMut { ptr } => format!("(borrow {})", ptr.0),
            Inst::Copy { ty, operand } => format!("(copy {} {})", self.ty(ty)?, operand.0),
            Inst::GEP {
                pointee_ty,
                base,
                indices,
                inbounds,
            } => {
                let ix: Vec<String> = indices.iter().map(|v| v.0.to_string()).collect();
                format!(
                    "(gep {} {} (idx{}) {inbounds})",
                    self.ty(pointee_ty)?,
                    base.0,
                    pad(&ix)
                )
            }
            Inst::PtrData { ptr_ty, ptr } => {
                format!("(ptrdata {} {})", self.ty(ptr_ty)?, ptr.0)
            }
            Inst::PtrMetadata {
                ptr_ty,
                metadata_ty,
                ptr,
            } => {
                self.check_metadata_ty("ptr_metadata", ptr_ty, metadata_ty)?;
                format!(
                    "(ptrmetadata {} {} {})",
                    self.ty(ptr_ty)?,
                    self.ty(metadata_ty)?,
                    ptr.0
                )
            }
            Inst::PtrFromParts {
                ptr_ty,
                metadata_ty,
                data,
                metadata,
            } => {
                self.check_metadata_ty("ptr_from_parts", ptr_ty, metadata_ty)?;
                format!(
                    "(ptrfromparts {} {} {} {})",
                    self.ty(ptr_ty)?,
                    self.ty(metadata_ty)?,
                    data.0,
                    metadata.0
                )
            }
            Inst::Br { target, args } => {
                let a: Vec<String> = args.iter().map(|v| v.0.to_string()).collect();
                format!("(br {} (args{}))", target.0, pad(&a))
            }
            Inst::CondBr {
                cond,
                then_target,
                then_args,
                else_target,
                else_args,
            } => {
                let ta: Vec<String> = then_args.iter().map(|v| v.0.to_string()).collect();
                let ea: Vec<String> = else_args.iter().map(|v| v.0.to_string()).collect();
                format!(
                    "(condbr {} {} (args{}) {} (args{}))",
                    cond.0,
                    then_target.0,
                    pad(&ta),
                    else_target.0,
                    pad(&ea)
                )
            }
            Inst::Switch {
                value,
                default,
                default_args,
                cases,
                exhaustive_enum_unreachable,
            } => {
                let da: Vec<String> = default_args.iter().map(|v| v.0.to_string()).collect();
                let mut cs = String::from("(cases");
                for c in cases {
                    let ca: Vec<String> = c.args.iter().map(|v| v.0.to_string()).collect();
                    let _ = write!(cs, " (case {} {} (args{}))", c.value, c.target.0, pad(&ca));
                }
                cs.push(')');
                format!(
                    "(switch {} {} (args{}) {cs} {exhaustive_enum_unreachable})",
                    value.0,
                    default.0,
                    pad(&da)
                )
            }
            Inst::Call { callee, args } => {
                let a: Vec<String> = args.iter().map(|v| v.0.to_string()).collect();
                format!("(call {} (args{}))", self.func_id(callee.0), pad(&a))
            }
            Inst::CallIndirect {
                callee,
                sig,
                args,
                calling_conv,
            } => {
                let a: Vec<String> = args.iter().map(|v| v.0.to_string()).collect();
                format!(
                    "(callindirect {} {} (args{}) {})",
                    callee.0,
                    sig.0,
                    pad(&a),
                    cc(*calling_conv)?
                )
            }
            Inst::Return { values } => {
                let v: Vec<String> = values.iter().map(|x| x.0.to_string()).collect();
                format!("(ret (vals{}))", pad(&v))
            }
            Inst::ExtractField {
                ty,
                aggregate,
                field,
            } => format!("(extractfield {} {} {field})", self.ty(ty)?, aggregate.0),
            Inst::InsertField {
                ty,
                aggregate,
                field,
                value,
            } => format!(
                "(insertfield {} {} {field} {})",
                self.ty(ty)?,
                aggregate.0,
                value.0
            ),
            Inst::ExtractElement { ty, array, index } => {
                format!("(extractelement {} {} {})", self.ty(ty)?, array.0, index.0)
            }
            Inst::Const { ty, value } => {
                // Crystal E5 (memo §23): a wide pointer's image `fat_ d md` carries an address
                // and a word and has no NULL lane, and the only constant the reference admits at
                // these kinds is the null pair `{ 0, 0 }` (`const_value`'s null fat pointer arm).
                if let Some(kind) = fat_kind_of(ty) {
                    match kind {
                        trust_ir::FatPtrKind::ContainerLen
                        | trust_ir::FatPtrKind::ContainerVtable
                        | trust_ir::FatPtrKind::TraitObject { .. } => {
                            return Err(format!(
                                "no Clean image for a `{ty}` constant (crystal E5): the wide \
                                 value `IRScalar.fat_ d md` has no null lane, and a constant at \
                                 this kind is the reference's null fat pointer"
                            ))
                        }
                        trust_ir::FatPtrKind::Str | trust_ir::FatPtrKind::Slice(_) => {}
                    }
                }
                format!("(const {} {})", self.ty(ty)?, self.cst(value)?)
            }
            Inst::GlobalAddr { global } => {
                format!("(globaladdr {})", self.global_id(global.0))
            }
            Inst::Undef { ty } => format!("(undef {})", self.ty(ty)?),
            // The check this projection was written for: kindless and siteless. A
            // kinded (trust-ir v52) or sited (v54) Assert has no Clean IRInst image.
            Inst::Assert { cond, kind, site } => {
                if !kind.is_unspecified() || site.is_some() {
                    return Err(String::from(
                        "no Clean IRInst image for a kinded or sited trust_ir::Inst::Assert",
                    ));
                }
                format!("(assert {})", cond.0)
            }
            Inst::Unreachable => "(unreachable)".into(),
            Inst::Select {
                ty,
                cond,
                then_val,
                else_val,
            } => format!(
                "(select {} {} {} {})",
                self.ty(ty)?,
                cond.0,
                then_val.0,
                else_val.0
            ),
            // WS3.20 (trust-ir 4f09dab8) bulk memory. `IRInst` has no bulk
            // byte copy/fill constructor, and lowering one to a Load/Store loop
            // here would be a semantics this projector invents rather than
            // reads. Refused by name.
            Inst::MemCopy { .. } | Inst::MemSet { .. } => {
                return Err(format!(
                    "no Clean IRInst image for trust_ir::Inst::{} (bulk memory has no \
                     IRInst constructor)",
                    variant_name(i)
                ))
            }
            // trust-ir v47 (`DROP_INST_FORMAT_VERSION`): run `ty`'s destructor
            // on the object at `ptr`. Dropping is observable (it frees, it can
            // run user code), so trust-ir requires a consumer that cannot model
            // destructors to REFUSE it; `IRInst` has no destructor constructor,
            // and treating it as a no-op would project a different program.
            Inst::Drop { .. } => {
                return Err(String::from(
                    "no Clean IRInst image for trust_ir::Inst::Drop (a destructor run has no \
                     IRInst constructor; trust-ir v47)",
                ))
            }
            // trust-ir v50 (`ARRAY_SPLAT_FORMAT_VERSION`): `n` copies of one
            // register as an array value, the register twin of
            // `Constant::Splat`. `IRInst` has no array constructor (its list
            // twin `MakeAggregate` is refused below), and spelling it as `n`
            // lane writes would be an image whose size follows `n`. Refused by
            // name; `n` is never read.
            Inst::ArraySplat { .. } => {
                return Err(String::from(
                    "no Clean IRInst image for trust_ir::Inst::ArraySplat (a uniform register \
                     array has no IRInst constructor; trust-ir v50)",
                ))
            }
            // Every variant `IRInst` has no constructor for, NAMED rather than
            // wildcarded so a variant trust-ir adds later fails to compile here
            // instead of being refused without anyone deciding it should be.
            Inst::HeapAlloc { .. }
            | Inst::AtomicLoad { .. }
            | Inst::AtomicStore { .. }
            | Inst::AtomicRMW { .. }
            | Inst::CmpXchg { .. }
            | Inst::Fence { .. }
            | Inst::InsertElement { .. }
            | Inst::NullPtr
            | Inst::Assume { .. }
            | Inst::SeqMapAddK { .. }
            | Inst::SeqMapNot { .. }
            | Inst::SeqMap { .. }
            | Inst::EndBorrow { .. }
            | Inst::Retain { .. }
            | Inst::Release { .. }
            | Inst::IsUnique { .. }
            | Inst::Dealloc { .. }
            | Inst::OpenFrame { .. }
            | Inst::BindSlot { .. }
            | Inst::LoadSlot { .. }
            | Inst::CloseFrame { .. }
            | Inst::CoroSuspend { .. }
            | Inst::Invoke { .. }
            | Inst::InvokeIndirect { .. }
            | Inst::AssertInvoke { .. }
            | Inst::CallCannotUnwind { .. }
            | Inst::CallIndirectCannotUnwind { .. }
            | Inst::DropInvoke { .. }
            | Inst::LandingPad { .. }
            | Inst::Resume { .. }
            | Inst::DialectOp(..)
            | Inst::MakeAggregate { .. }
            | Inst::TensorContract { .. }
            | Inst::TensorMap { .. }
            | Inst::TensorReduce { .. }
            | Inst::TensorView { .. }
            | Inst::TensorGather { .. }
            | Inst::TensorScatter { .. }
            | Inst::MakeClosure { .. } => {
                return Err(format!(
                    "no Clean IRInst image for trust_ir::Inst::{}",
                    variant_name(i)
                ))
            }
        })
    }
}

/// Whether a constant MAY name a function anywhere in its tree, which
/// `fold_in` cannot relocate: a `FnDef`, a `Closure`'s `func`, or a
/// `SymbolAddr`. A `SymbolAddr` names its target by NAME, resolved against the
/// merged module's symbol table, and trust-ir documents that target as "a
/// function or data global defined in the same module, or an external symbol"
/// (`constant.rs`, `Constant::SymbolAddr`) — so after a merge it can resolve to
/// the PRIMARY artifact's function of that name, and relocating `FuncId`s does
/// nothing for it. Answering `false` there let a merged `SymbolAddr` through
/// `fold_in` unrelocated, caught only because `Projector::cst` happens to
/// refuse the shape later. Exhaustive over `Constant` with no wildcard, so a
/// constant shape trust-ir adds later must be classified here before a merge
/// can pass it.
fn constant_may_name_function(c: &Constant) -> bool {
    match c {
        Constant::Ext(e) => e.unreachable(),
        Constant::FnDef(_) | Constant::Closure { .. } | Constant::SymbolAddr { .. } => true,
        Constant::Aggregate(v)
        | Constant::Array(v)
        | Constant::Vector(v)
        | Constant::Sequence(v)
        | Constant::Set(v) => v.iter().any(constant_may_name_function),
        Constant::Record(fields) => fields.iter().any(|(_, v)| constant_may_name_function(v)),
        // trust-ir v50: every lane of a splat IS its one element, so the
        // element answers for all `len` of them; the length is never walked.
        Constant::Splat { elem, .. } => constant_may_name_function(elem),
        Constant::Int(_)
        | Constant::U128(_)
        | Constant::Bytes { .. }
        | Constant::Float(_)
        | Constant::Bool(_)
        | Constant::PhantomData
        // trust-ir v49's unwritten lane carries no payload at all, so it
        // cannot name a function.
        | Constant::Uninit
        // trust-ir v70: a weight blob names bytes by digest, never a function.
        | Constant::TensorBlob { .. } => false,
    }
}

fn pad(v: &[String]) -> String {
    if v.is_empty() {
        String::new()
    } else {
        format!(" {}", v.join(" "))
    }
}

fn variant_name(i: &Inst) -> String {
    format!("{i:?}")
        .split(['{', '(', ' '])
        .next()
        .unwrap_or("?")
        .to_string()
}

/// The constructor name alone (`Aggregate`, `Bytes`, …), so a refusal names
/// the SHAPE it refused without echoing a payload that may be kilobytes long.
fn constant_variant_name(c: &Constant) -> String {
    format!("{c:?}")
        .split(['{', '(', ' '])
        .next()
        .unwrap_or("?")
        .to_string()
}

/// One `--merge` artifact and the `--join` manifests that FOLLOW it on the
/// command line, before the next `--merge`.
struct MergeArg {
    path: String,
    joins: Vec<String>,
}

/// Remove every `--merge <bin>` and `--join <manifest>` from `args`, pairing
/// each join with the merge it follows.
///
/// A join manifest names sidecar MEMBER ids, which are indices into ONE
/// merged artifact, so it has to know which artifact. Until 2026-09-24 the two
/// flags were collected into separate lists and every join ran once per merge,
/// relocated by that merge's shift — with two merges, the first iteration
/// retargeted every declaration (including the second artifact's) into the
/// FIRST artifact's function range, and the second iteration found nothing
/// left to move. Pairing by position is the whole fix; a join with no merge
/// before it is refused rather than guessed.
fn take_merges(args: &mut Vec<String>) -> Vec<MergeArg> {
    let mut merges: Vec<MergeArg> = Vec::new();
    let mut rest = Vec::with_capacity(args.len());
    let mut it = std::mem::take(args).into_iter();
    while let Some(a) = it.next() {
        match a.as_str() {
            "--merge" => {
                let path = it
                    .next()
                    .unwrap_or_else(|| panic!("--merge takes a path to a .bin"));
                merges.push(MergeArg {
                    path,
                    joins: Vec::new(),
                });
            }
            "--join" => {
                let manifest = it
                    .next()
                    .unwrap_or_else(|| panic!("--join takes a path to a sidecar manifest"));
                let Some(owner) = merges.last_mut() else {
                    panic!(
                        "--join {manifest} precedes every --merge; a join manifest names the \
                         member ids of the merged artifact it FOLLOWS"
                    )
                };
                owner.joins.push(manifest);
            }
            _ => rest.push(a),
        }
    }
    *args = rest;
    merges
}

/// A `--merge` artifact as read: its path, its canonical module, and its join
/// manifests as `(path, text)`.
struct MergeInput {
    path: String,
    module: trust_ir::Module,
    joins: Vec<(String, String)>,
}

/// A merged artifact after `fold_in`: the relocated function-id range
/// `shift..end` its bodies occupy, and its OWN aggregate tables.
struct Merged {
    shift: u32,
    end: u32,
    enums: Vec<trust_ir::ty::EnumDef>,
    structs: Vec<trust_ir::ty::StructDef>,
    /// Its type table: a `ty.N` nested in one of its definitions indexes THIS.
    types: Vec<Ty>,
    /// Its target, which the canonical layout a `Direct` descriptor is
    /// compared against, and a niche row's pointer word, are computed under.
    target: Option<trust_ir::TargetInfo>,
    /// Crystal (memo §15/§18): its undefined-behaviour halt sites, read off ITS
    /// obligations (which `fold_in` does not carry over) and relocated by its
    /// shift, as its functions were.
    ub_sites: UbSites,
}

/// Fold every merged artifact into `module` in command-line order, applying
/// each artifact's OWN join manifests relocated by ITS shift. Returns the
/// merged ranges and the provenance rows of every retargeted call.
fn merge_all(module: &mut trust_ir::Module, inputs: Vec<MergeInput>) -> (Vec<Merged>, Vec<String>) {
    let mut merged = Vec::with_capacity(inputs.len());
    let mut prov_join = Vec::new();
    for input in inputs {
        let enums = input.module.enums.clone();
        let structs = input.module.structs.clone();
        let types = input.module.types.clone();
        let target = input.module.target_info.clone();
        let ub = ub_halt_sites_of(&input.module, 0);
        let shift = fold_in(module, input.module, &input.path);
        let ub_sites = shift_ub_sites(ub, shift);
        let end = module
            .functions
            .iter()
            .map(|f| f.id.0)
            .max()
            .map_or(shift, |m| (m + 1).max(shift));
        for (jpath, text) in &input.joins {
            let pairs = joins_of(text, jpath);
            assert!(
                !pairs.is_empty(),
                "--join {jpath} names no resolved root; a manifest that joins nothing cannot \
                 retarget anything"
            );
            for (decl, member) in pairs {
                let body = member + shift;
                assert!(
                    body < end,
                    "--join {jpath}: member @func.{member} is not a function of --merge {} \
                     (its bodies were relocated to @func.{shift}..@func.{end})",
                    input.path
                );
                retarget(module, decl, body, jpath);
                prov_join.push(format!(
                    "  {{\"manifest\": {jpath:?}, \"declaration\": {decl}, \"body\": {body}}}"
                ));
            }
        }
        merged.push(Merged {
            shift,
            end,
            enums,
            structs,
            types,
            target,
            ub_sites,
        });
    }
    (merged, prov_join)
}

/// The artifact whose table defines the aggregates a function first named:
/// `Ok(None)` for the primary module, `Ok(Some(m))` for the merged artifact
/// whose relocated range holds `func`.
///
/// It used to be the FIRST merged artifact whose shift `func` reached, which
/// is the lowest shift — so with two merges a body from the second read the
/// first artifact's tables, two different types at one raw id.
fn artifact_of(merged: &[Merged], func: u32) -> Result<Option<&Merged>, String> {
    match merged.first() {
        None => Ok(None),
        Some(first) if func < first.shift => Ok(None),
        Some(_) => merged
            .iter()
            .find(|m| (m.shift..m.end).contains(&func))
            .map(Some)
            .ok_or_else(|| format!("@func.{func}, which is in no artifact's function range")),
    }
}

/// One artifact's aggregate tables and target, as the encodings derivation and
/// the collision check read them: the primary module's, or a merged
/// artifact's own.
struct Definer<'a> {
    /// `module` or `merge@<shift>`: printed into every row and refusal, and
    /// into every id the deep comparison does not resolve.
    label: String,
    enums: &'a [trust_ir::ty::EnumDef],
    structs: &'a [trust_ir::ty::StructDef],
    types: &'a [Ty],
    target: Option<&'a trust_ir::TargetInfo>,
}

impl Definer<'_> {
    /// trust-ir's layout size of `t`, in bits, under this artifact's own
    /// tables and target -- the layout the reference interpreter decodes by.
    fn size_bits(&self, t: &Ty) -> Result<u64, String> {
        let mut m = trust_ir::Module::new("layout-probe");
        m.enums = self.enums.to_vec();
        m.structs = self.structs.to_vec();
        m.types = self.types.to_vec();
        m.target_info = self.target.cloned();
        m.ty_layout_shape(t)
            .map(|shape| shape.size_bits)
            .map_err(|e| format!("trust-ir lays out no {t:?}: {e:?}"))
    }

    /// Does the one live field of type `field` fill ALL of `outer`'s bytes?
    /// `ir_wrap_image` hands the WHOLE stored word to the payload view, and the
    /// reference reads the field from its own bytes only, so the two can agree
    /// on every word only when the field is exactly as wide as the struct.
    fn fills(&self, outer: &Ty, field: &Ty) -> Result<(), String> {
        let (o, f) = (self.size_bits(outer)?, self.size_bits(field)?);
        if o == f {
            Ok(())
        } else {
            Err(format!(
                "its one non-ZST field is {f} bits and the struct {o} -- the stored word is not \
                 that field"
            ))
        }
    }
}

/// The artifact whose tables define the aggregates `func` names.
fn definer_of<'a>(
    module: &'a trust_ir::Module,
    merged: &'a [Merged],
    func: u32,
) -> Result<Definer<'a>, String> {
    Ok(match artifact_of(merged, func)? {
        Some(m) => Definer {
            label: format!("merge@{}", m.shift),
            enums: &m.enums,
            structs: &m.structs,
            types: &m.types,
            target: m.target.as_ref(),
        },
        None => Definer {
            label: "module".to_string(),
            enums: &module.enums,
            structs: &module.structs,
            types: &module.types,
            target: module.target_info.as_ref(),
        },
    })
}

/// The encodings rows (see THE ENCODINGS ROWS in `main`), and the refusals.
///
/// A payload type is read from the DEFINER's table, so it is interned as that
/// artifact's: `current_func` is set to the definer before `ty_of`, never left
/// at whichever body was projected last. Interning can therefore name a raw
/// aggregate id for a second artifact, so the collision check runs again here,
/// after the last intern -- a payload that shares a raw id with another
/// artifact's body type is the same conflation `project_merged` refuses.
///
/// TO A FIXPOINT. A payload interned here -- a niche row's payload, a wrapper
/// row's field -- can name an aggregate no body named, and it interns at the
/// END of `enum_order` / `struct_order`. Until verifier r7 (2026-09-24) the
/// two loops walked clones of those orders taken up front, so an `Untagged`
/// enum, a niche enum or a pointer wrapper reached only through another row's
/// payload got no row and no refusal: the canonical layout, silently. The
/// cursors below run until neither order grows, so every aggregate the module
/// names is judged; the order rows come out in is unchanged for every id the
/// bodies named.
fn derive_encodings(
    module: &trust_ir::Module,
    merged: &[Merged],
    p: &mut Projector,
) -> Result<(Vec<String>, Vec<String>), String> {
    let (rows, refused) = derive_rows(module, merged, p)?;
    Ok((rows.iter().map(Row::render).collect(), refused))
}

/// [`derive_encodings`] before the rows are printed.
fn derive_rows(
    module: &trust_ir::Module,
    merged: &[Merged],
    p: &mut Projector,
) -> Result<(Vec<Row>, Vec<String>), String> {
    let mut rows: Vec<Row> = Vec::new();
    let mut refused: Vec<String> = Vec::new();
    let (mut next_enum, mut next_struct) = (0usize, 0usize);
    loop {
        if let Some(&raw) = p.enum_order.get(next_enum) {
            let canonical = next_enum;
            next_enum += 1;
            enum_row(module, merged, p, canonical, raw, &mut rows, &mut refused);
        } else if let Some(&raw) = p.struct_order.get(next_struct) {
            let canonical = next_struct;
            next_struct += 1;
            struct_row(module, merged, p, canonical, raw, &mut rows, &mut refused);
        } else {
            break;
        }
    }
    let collisions = aggregate_collisions(module, merged, p);
    if !collisions.is_empty() {
        return Err(collisions.join("; "));
    }
    reference_gate(module, merged, &mut rows, &mut refused);
    Ok((rows, refused))
}

/// THE ROWS, CHECKED AGAINST THE REFERENCE -- the one mechanism every row
/// passes, whatever its shape.
///
/// A row is a claim about how a WORD the machine holds reads at an aggregate
/// type: `ir_load_view` images it through the row, and through the row of
/// every payload type the row names. trust-ir's `Interpreter` is the
/// reference for the same question: store the word into a cell, load it at the
/// aggregate type, and it decodes the bytes under the artifact's own
/// descriptors and target. So every candidate row is RUN, not argued: for each
/// probe word (see `reference::probe_words`) the Clean view of the minted table
/// ([`reference::load_view`], a transliteration of `ir_load_view` /
/// `ir_view_word` / `ir_niche_image` / `ir_wrap_image` / `ir_zst_spine`) must
/// equal the reference's decode, or the row is REFUSED and the first
/// disagreeing word is recorded.
///
/// TO A FIXPOINT. A row images its payload through the payload type's OWN row,
/// so refusing one row changes what every row naming it as a payload images;
/// the pass repeats until no row disagrees. That is what refuses a parent whose
/// child was refused (`Option<Box<char>>`: `char` has no Clean image, so
/// NonNull's row is refused, then Box's, then the Option's).
///
/// It replaced three clause-by-clause judgements a verifier found missing
/// (r7b, 2026-09-24): a niche row's tags are the variant INDICES while the
/// reference synthesizes the effective DISCRIMINANT; a row survived its
/// payload's refused row and decoded one wrapper short; a zero-sized marker
/// WITH a field was imaged as a field-less ZST. Each was a clause nobody had
/// written; a decode that differs from the reference's is refused whether or
/// not anyone has named why. The structural clauses in `niche_row` /
/// `struct_row` stay: they are what makes a handful of probe words decisive
/// (one word, the none image at zero and only at zero, and every live field
/// filling the word it is read from), not a second opinion. How decisive the
/// probe words are on their own is itself pinned:
/// `the_probe_words_alone_tell_each_wrong_row_from_the_reference` fails when
/// they stop telling a known-wrong row from the reference.
///
/// The reference runs once per row, under the tables and target of the
/// artifact that defines it. `project_merged` has already refused a module
/// whose artifacts disagree on the layout target, and `aggregate_collisions`
/// one whose artifacts define a shared raw id differently, so that judgement
/// holds for every artifact that names the id.
fn reference_gate(
    module: &trust_ir::Module,
    merged: &[Merged],
    rows: &mut Vec<Row>,
    refused: &mut Vec<String>,
) {
    let mut images: Vec<Result<Vec<(u128, reference::Img)>, String>> = rows
        .iter()
        .map(|r| {
            definer_of(module, merged, r.first_by).and_then(|d| {
                reference::reference_images(
                    &reference::Probe {
                        enums: d.enums,
                        structs: d.structs,
                        types: d.types,
                        target: d.target,
                    },
                    r.key().0,
                    r.raw,
                    &[],
                )
            })
        })
        .collect();
    loop {
        let mut failing: Vec<(usize, String)> = Vec::new();
        for (i, (r, want)) in rows.iter().zip(&images).enumerate() {
            let why = match want {
                Err(e) => Some(format!("the reference cannot decode it: {e}")),
                Ok(words) => words.iter().find_map(|(w, want)| {
                    let got = reference::load_view(rows, &r.image(), reference::Img::Word(*w));
                    (!got.agrees(want)).then(|| {
                        format!(
                            "at the word {w:#x} the row images {got} and trust-ir's reference \
                             interpreter decodes {want}"
                        )
                    })
                }),
            };
            if let Some(why) = why {
                failing.push((i, why));
            }
        }
        if failing.is_empty() {
            return;
        }
        for (i, why) in &failing {
            let r = &rows[*i];
            refused.push(format!(
                "{}.{}: its {} row does not decode as the reference does: {why}",
                r.key().0.tag(),
                r.raw,
                r.kind()
            ));
        }
        for (i, _) in failing.iter().rev() {
            rows.remove(*i);
            let _ = images.remove(*i);
        }
    }
}

/// One derived row, before it is printed into provenance.
struct Row {
    canonical: usize,
    raw: u32,
    first_by: u32,
    table: String,
    decl: String,
    /// The payload type's Clean image, as `Projector::ty` printed it.
    payload: String,
    shape: Shape,
}

/// What a row says about the word, beyond its payload.
enum Shape {
    /// `IREnc.nicheptr`: the zero word is `none`, any other word is `some`.
    Niche { none: usize, some: usize },
    /// `IREnc.ptrwrap`: the word is field `slot` of a `fields`-field struct.
    Wrap { slot: usize, fields: usize },
}

impl Row {
    /// The (namespace, canonical id) `ir_enc_matches` keys the row on.
    fn key(&self) -> (Agg, usize) {
        match self.shape {
            Shape::Niche { .. } => (Agg::Enum, self.canonical),
            Shape::Wrap { .. } => (Agg::Struct, self.canonical),
        }
    }

    fn kind(&self) -> &'static str {
        match self.shape {
            Shape::Niche { .. } => "nicheptr",
            Shape::Wrap { .. } => "ptrwrap",
        }
    }

    /// The Clean image of the type the row describes.
    fn image(&self) -> String {
        let (agg, k) = self.key();
        format!("({} {k})", agg.tag())
    }

    /// The provenance row, byte for byte what every committed chain carries.
    fn render(&self) -> String {
        let Row {
            canonical,
            raw,
            first_by,
            table,
            decl,
            payload,
            shape,
        } = self;
        match shape {
            Shape::Niche { none, some } => format!(
                "{{\"canonical\": {canonical}, \"crate_id\": {raw}, \"kind\": \"nicheptr\", \
                 \"none_variant\": {none}, \"some_variant\": {some}, \"payload\": {payload:?}, \
                 \"first_named_by\": {first_by}, \"table\": {table:?}, \"decl\": {decl:?}}}"
            ),
            Shape::Wrap { slot, fields } => format!(
                "{{\"canonical\": {canonical}, \"crate_id\": {raw}, \"kind\": \"ptrwrap\", \
                 \"slot\": {slot}, \"fields\": {fields}, \"payload\": {payload:?}, \
                 \"first_named_by\": {first_by}, \"table\": {table:?}, \"decl\": {decl:?}}}"
            ),
        }
    }
}

/// The row -- or the refusal, or nothing for the canonical layout -- of the
/// enum interned at `canonical` from raw id `raw`.
fn enum_row(
    module: &trust_ir::Module,
    merged: &[Merged],
    p: &mut Projector,
    canonical: usize,
    raw: u32,
    rows: &mut Vec<Row>,
    refused: &mut Vec<String>,
) {
    // WHOSE table? The one belonging to the artifact whose body first named
    // this id. Without this the derivation reads the crate module's `enum.1`
    // for a row about the sidecar bundle's `enum.1` — two different types at
    // one number, which is the whole reason the aggregate lanes are compared
    // on the Clean side too.
    let first_by = p.enum_first_seen_by.get(&raw).copied().unwrap_or(0);
    // A payload read from this table is this artifact's type.
    p.current_func = first_by;
    let d = match definer_of(module, merged, first_by) {
        Ok(d) => d,
        Err(e) => {
            refused.push(format!("enum.{raw}: first named by {e}"));
            return;
        }
    };
    let Some(def) = d.enums.iter().find(|e| e.id.0 == raw) else {
        refused.push(format!(
            "enum.{raw}: first named by @func.{first_by}, and not in that artifact's enum table"
        ));
        return;
    };
    // No descriptor: trust-ir's own rule is that such an enum HAS the
    // canonical tagged-union layout, which is what a row-less enum is read
    // under. No row, and nothing to refuse.
    let Some(layout) = def.layout.as_ref() else {
        return;
    };
    // EVERY encoding named, with no wildcard: an encoding trust-ir adds fails
    // to compile here until someone decides what its row is.
    match &layout.encoding {
        trust_ir::ty::EnumTagEncoding::Niche {
            untagged_variant,
            niche_variants_start,
            niche_variants_end,
            niche_start,
            niche_offset,
            niche_ty,
        } => {
            let niche = Niche {
                untagged_variant: *untagged_variant,
                niche_variants_start: *niche_variants_start,
                niche_variants_end: *niche_variants_end,
                niche_start: *niche_start,
                niche_offset: *niche_offset,
                niche_ty: *niche_ty,
            };
            match niche_row(p, &d, def, layout, &niche) {
                Ok((some, none, payload)) => rows.push(Row {
                    canonical,
                    raw,
                    first_by,
                    table: d.label.clone(),
                    decl: def.name.clone(),
                    payload,
                    shape: Shape::Niche { none, some },
                }),
                Err(why) => refused.push(format!("enum.{raw}: {}", why.join("; "))),
            }
        }
        // The tag is STORED, and a row-less enum is read under trust-ir's
        // CANONICAL tagged-union layout: the tag at byte 0, each variant's
        // fields C-style after it. That is a claim about the bytes, and the
        // descriptor is normative, so it holds only when the descriptor says
        // exactly that. Until verifier r7 (2026-09-24) every `Direct` passed
        // unread -- `tag_offset: 8`, reordered fields, any size -- and was
        // read as canonical, silently.
        trust_ir::ty::EnumTagEncoding::Direct { tag_offset } => {
            let why = direct_departures(&d, def, layout, *tag_offset);
            if !why.is_empty() {
                refused.push(format!(
                    "enum.{raw}: its Direct descriptor is not trust-ir's canonical tagged-union \
                     layout, which is what an enum with no row is read under: {}",
                    why.join("; ")
                ));
            }
        }
        // NO tag is stored: the memory image is the sole inhabited variant's
        // payload alone. trust-ir's own canonical layout budgets a tag this
        // enum does not have (its doc on `EnumTagEncoding::Untagged`), and
        // `IREnc` has no row that says "the tag is implicit", so a word loaded
        // at this type would be read as if it carried one. Refused and
        // RECORDED, like every other descriptor no row can state -- never
        // passed off as the canonical layout.
        trust_ir::ty::EnumTagEncoding::SingleInhabited { variant } => refused.push(format!(
            "enum.{raw}: its layout descriptor is SingleInhabited (selected variant {variant}, \
             no stored tag), which no IREnc row describes"
        )),
        trust_ir::ty::EnumTagEncoding::Untagged => refused.push(format!(
            "enum.{raw}: its layout descriptor is Untagged (no stored tag; the image is the sole \
             inhabited variant's payload), which neither the canonical tagged-union layout nor \
             any IREnc row describes"
        )),
    }
}

/// A `Niche` descriptor's numbers, named.
struct Niche {
    untagged_variant: u32,
    niche_variants_start: u32,
    niche_variants_end: u32,
    niche_start: u128,
    niche_offset: u64,
    niche_ty: trust_ir::ty::EnumTagRepr,
}

/// `IREnc.nicheptr K none some T` says the enum's byte image is ONE pointer
/// WORD: the zero word is the field-less `none` variant, any other word is
/// `some` carrying that same word as its payload of type T. These clauses are
/// the row's SHAPE -- one word, the none image at zero and only at zero -- and
/// each failure is named. Whether the shape decodes as the reference does
/// (the tag values, the payload's own rows) is not argued here: a row that
/// passes is run against trust-ir's interpreter by `reference_gate`.
///
/// Until verifier r7 (2026-09-24) `niche_ty` was ignored and any single-field
/// payload was accepted: a niche over a `u8` lane, or a `some` variant
/// carrying an integer, minted the same pointer-word row.
fn niche_row(
    p: &mut Projector,
    d: &Definer<'_>,
    def: &trust_ir::ty::EnumDef,
    layout: &trust_ir::ty::EnumLayoutDescriptor,
    n: &Niche,
) -> Result<(usize, usize, String), Vec<String>> {
    let mut why = Vec::new();
    if def.variants.len() != 2 {
        why.push(format!("{} variants, not 2", def.variants.len()));
    }
    if n.niche_variants_start != n.niche_variants_end {
        why.push(format!(
            "niche variants {}..{} is not a single variant",
            n.niche_variants_start, n.niche_variants_end
        ));
    }
    if n.niche_start != 0 {
        why.push(format!(
            "niche_start is {}, not 0 — the none word is not ZERO",
            n.niche_start
        ));
    }
    if n.niche_offset != 0 {
        why.push(format!("niche_offset is {}, not 0", n.niche_offset));
    }
    let some = n.untagged_variant as usize;
    let none = n.niche_variants_start as usize;
    if some == none || some > 1 || none > 1 {
        why.push(format!(
            "untagged={some} and niche={none} are not the two variants"
        ));
    }
    // The WORD: the pointer width the command line states. That it is also
    // every artifact's own width is `project_merged`'s refusal
    // (`layout_target_conflicts`), made before any row is derived.
    match p.usize_bits {
        None => why.push(
            "no pointer width is stated (--usize-bits), so the niche lane cannot be shown to be \
             the pointer word"
                .into(),
        ),
        Some(bits) => {
            let lane_bits = n.niche_ty.size_bytes() * 8;
            if lane_bits != u64::from(bits) {
                why.push(format!(
                    "niche_ty is {:?}, a {lane_bits}-bit lane, not the {bits}-bit pointer word",
                    n.niche_ty
                ));
            }
            if layout.size * 8 != u64::from(bits) {
                why.push(format!(
                    "the descriptor's size is {} bytes, not one {bits}-bit word",
                    layout.size
                ));
            }
        }
    }
    if let Some(v) = def.variants.get(none) {
        if !v.fields.is_empty() {
            why.push(format!(
                "the none variant carries {} field(s); the zero word images a field-less variant",
                v.fields.len()
            ));
        }
    }
    if layout.variant_field_offsets.get(some).map(Vec::as_slice) != Some(&[0][..]) {
        why.push(format!(
            "the some variant's field offsets are {:?}, not its one payload at byte 0",
            layout.variant_field_offsets.get(some)
        ));
    }
    let payload = match def.variants.get(some).map(|v| v.fields.as_slice()) {
        Some([t]) => {
            if !is_pointer_word(t, d, &mut Vec::new()) {
                why.push(format!(
                    "the payload {t:?} is not a thin pointer, nor a wrapper whose one non-ZST \
                     field is one"
                ));
            }
            Some(t)
        }
        Some(other) => {
            why.push(format!(
                "the some variant has {} fields, not 1",
                other.len()
            ));
            None
        }
        None => {
            why.push("the some variant is not in the table".into());
            None
        }
    };
    if !why.is_empty() {
        return Err(why);
    }
    let t = payload.ok_or_else(|| vec!["no payload".to_string()])?;
    p.ty_of(t)
        .map(|image| (some, none, image))
        .map_err(|e| vec![format!("payload type has no Clean image: {e}")])
}

/// Is a value of type `t` exactly one thin pointer WORD -- a pointer, or a
/// struct of the definer's table whose one non-ZST field is one AND fills it
/// (`Definer::fills`), recursively? `Rc`, fat pointers and everything else
/// answer no: fail-closed.
fn is_pointer_word(t: &Ty, d: &Definer<'_>, seen: &mut Vec<u32>) -> bool {
    match t {
        Ty::Ext(e) => e.unreachable(),
        Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_) => true,
        Ty::Struct(id) => {
            if seen.contains(&id.0) {
                return false;
            }
            let Some(def) = d.structs.iter().find(|s| s.id.0 == id.0) else {
                return false;
            };
            let live: Vec<&trust_ir::ty::FieldDef> = def
                .fields
                .iter()
                .filter(|f| !is_zst(&f.ty, d.structs))
                .collect();
            seen.push(id.0);
            let word = def.size != Some(0)
                && match live.as_slice() {
                    [f] => {
                        f.offset.is_none_or(|o| o == 0)
                            && d.fills(t, &f.ty).is_ok()
                            && is_pointer_word(&f.ty, d, seen)
                    }
                    _ => false,
                };
            seen.pop();
            word
        }
        Ty::I8
        | Ty::I16
        | Ty::I32
        | Ty::I64
        | Ty::I128
        | Ty::U8
        | Ty::U16
        | Ty::U32
        | Ty::U64
        | Ty::U128
        | Ty::Isize
        | Ty::Usize
        | Ty::Char
        | Ty::Error
        | Ty::F16
        | Ty::F32
        | Ty::F64
        | Ty::Bool
        | Ty::Unit
        | Ty::Never
        | Ty::Enum(_)
        | Ty::Rc(_)
        | Ty::Vector(..)
        | Ty::Tuple(_)
        | Ty::Array(..)
        | Ty::FatPtr(_)
        | Ty::Func(_)
        | Ty::Set(..)
        | Ty::Sequence(_)
        | Ty::Record(_)
        | Ty::Closure(_)
        | Ty::Refine(..)
        | Ty::Dialect(_)
        | Ty::Tensor(..)
        | Ty::Storage(_)
        | Ty::Handle(_) => false,
    }
}

/// A field counts as a ZST slot only when its type is a struct the artifact
/// declares with `size: Some(0)` -- measured, never assumed from a name -- AND
/// with no fields. `ir_zst_spine` images a ZST slot `aggv vnil`, which is the
/// reference's decode of a zero-FIELD aggregate; a zero-sized struct WITH a
/// field (`Invariant(PhantomData<..>)`) decodes to `Aggregate([Aggregate([])])`
/// and is a live slot the spine cannot image. Until verifier r7b (2026-09-24)
/// it counted as a ZST, and `Handle { ptr, Invariant }` minted a wrapper row
/// whose second slot read differently from the reference.
///
/// A `match` naming every variant, not `matches!`: the macro expands to a
/// `_ => false` arm the wildcard lints never see (clippy skips macro
/// expansions), which is why scripts/check_lint_coverage.py refuses it here.
fn is_zst(t: &Ty, structs: &[trust_ir::ty::StructDef]) -> bool {
    match t {
        Ty::Ext(e) => e.unreachable(),
        Ty::Struct(id) => structs
            .iter()
            .any(|d| d.id.0 == id.0 && d.size == Some(0) && d.fields.is_empty()),
        Ty::Ptr
        | Ty::PtrConst(_)
        | Ty::PtrMut(_)
        | Ty::Ref(_)
        | Ty::RefMut(_)
        | Ty::I8
        | Ty::I16
        | Ty::I32
        | Ty::I64
        | Ty::I128
        | Ty::U8
        | Ty::U16
        | Ty::U32
        | Ty::U64
        | Ty::U128
        | Ty::Isize
        | Ty::Usize
        | Ty::Char
        | Ty::Error
        | Ty::F16
        | Ty::F32
        | Ty::F64
        | Ty::Bool
        | Ty::Unit
        | Ty::Never
        | Ty::Enum(_)
        | Ty::Rc(_)
        | Ty::Vector(..)
        | Ty::Tuple(_)
        | Ty::Array(..)
        | Ty::FatPtr(_)
        | Ty::Func(_)
        | Ty::Set(..)
        | Ty::Sequence(_)
        | Ty::Record(_)
        | Ty::Closure(_)
        | Ty::Refine(..)
        | Ty::Dialect(_)
        | Ty::Tensor(..)
        | Ty::Storage(_)
        | Ty::Handle(_) => false,
    }
}

/// Where a `Direct` descriptor departs from trust-ir's canonical
/// tagged-union layout of the same enum, computed by trust-ir itself
/// (`Module::enum_layout_shape` / `ty_layout_shape`) over the definer's own
/// tables and target, with this enum's descriptor removed. Empty = it IS the
/// canonical layout.
fn direct_departures(
    d: &Definer<'_>,
    def: &trust_ir::ty::EnumDef,
    layout: &trust_ir::ty::EnumLayoutDescriptor,
    tag_offset: u64,
) -> Vec<String> {
    let mut why = Vec::new();
    if tag_offset != 0 {
        why.push(format!("the tag is at byte {tag_offset}, not 0"));
    }
    let mut probe = trust_ir::Module::new("canonical-layout-probe");
    probe.enums = d.enums.to_vec();
    for e in &mut probe.enums {
        if e.id == def.id {
            e.layout = None;
        }
    }
    probe.structs = d.structs.to_vec();
    probe.types = d.types.to_vec();
    probe.target_info = d.target.cloned();
    match canonical_enum_layout(&probe, def) {
        Err(e) => why.push(format!(
            "trust-ir computes no canonical layout for it ({e})"
        )),
        Ok((size, align, offsets)) => {
            if layout.size != size {
                why.push(format!("size {} bytes, canonical {size}", layout.size));
            }
            if layout.align != align {
                why.push(format!("align {}, canonical {align}", layout.align));
            }
            if layout.variant_field_offsets != offsets {
                why.push(format!(
                    "field offsets {:?}, canonical {offsets:?}",
                    layout.variant_field_offsets
                ));
            }
        }
    }
    why
}

/// trust-ir's canonical layout of `def` in `probe` (which carries no
/// descriptor for it): (size, align, per-variant field byte offsets). The
/// offsets follow the rule `EnumLayoutShape` documents -- each variant's fields
/// C-style from the shared payload offset -- over trust-ir's own field shapes.
fn canonical_enum_layout(
    probe: &trust_ir::Module,
    def: &trust_ir::ty::EnumDef,
) -> Result<(u64, u64, Vec<Vec<u64>>), String> {
    let shape = probe
        .enum_layout_shape(def.id)
        .map_err(|e| format!("{e:?}"))?;
    let mut offsets = Vec::with_capacity(def.variants.len());
    for v in &def.variants {
        let mut at: u64 = 0;
        let mut row = Vec::with_capacity(v.fields.len());
        for t in &v.fields {
            let f = probe.ty_layout_shape(t).map_err(|e| format!("{e:?}"))?;
            let align = f
                .align_bits
                .ok_or_else(|| format!("{t:?} has no alignment"))?
                .max(8);
            at = at
                .div_ceil(align)
                .checked_mul(align)
                .ok_or("offset overflow")?;
            row.push((shape.payload_offset_bits + at) / 8);
            at = at.checked_add(f.size_bits).ok_or("offset overflow")?;
        }
        offsets.push(row);
    }
    Ok((shape.size_bits / 8, shape.align_bits / 8, offsets))
}

/// The ptrwrap row -- or the refusal, or nothing for a ZST -- of the struct
/// interned at `canonical` from raw id `raw`.
///
/// `IREnc.ptrwrap K i c T` is a c-field struct whose only non-ZST field is
/// `i`, of type T. It is what makes `Arc` and `NonNull` readable: the heap
/// holds one pointer WORD, and without these rows an `extractfield` on it has
/// no aggregate to extract from. A struct with two real fields is REFUSED
/// rather than having one of them picked.
fn struct_row(
    module: &trust_ir::Module,
    merged: &[Merged],
    p: &mut Projector,
    canonical: usize,
    raw: u32,
    rows: &mut Vec<Row>,
    refused: &mut Vec<String>,
) {
    let first_by = p.struct_first_seen_by.get(&raw).copied().unwrap_or(0);
    p.current_func = first_by;
    let d = match definer_of(module, merged, first_by) {
        Ok(d) => d,
        Err(e) => {
            refused.push(format!("struct.{raw}: first named by {e}"));
            return;
        }
    };
    let Some(def) = d.structs.iter().find(|s| s.id.0 == raw) else {
        refused.push(format!(
            "struct.{raw}: first named by @func.{first_by}, and not in that artifact's struct \
             table"
        ));
        return;
    };
    if def.size == Some(0) {
        return; // A ZST: no bytes, no row, nothing to refuse.
    }
    // A struct that declares no fields and is not zero-sized is OPAQUE: its
    // bytes are there and nothing says what they are. The canonical layout of
    // a field-less struct is zero-sized, so reading it as canonical is wrong;
    // until verifier r7 (2026-09-24) it was skipped as "no wrapper, no
    // refusal".
    if def.fields.is_empty() {
        refused.push(format!(
            "struct.{raw}: declares no fields and size {:?} -- an opaque row whose bytes no IREnc \
             row states and the canonical (zero-sized) layout contradicts",
            def.size
        ));
        return;
    }
    let live: Vec<usize> = def
        .fields
        .iter()
        .enumerate()
        .filter(|(_, f)| !is_zst(&f.ty, d.structs))
        .map(|(i, _)| i)
        .collect();
    let [i] = live.as_slice() else {
        refused.push(format!(
            "struct.{raw}: {} non-ZST field(s), not 1 — not a pointer wrapper",
            live.len()
        ));
        return;
    };
    let i = *i;
    if let Some(off) = def.fields[i].offset.filter(|o| *o != 0) {
        refused.push(format!(
            "struct.{raw}: its one non-ZST field sits at byte {off}, not 0 -- the word is not \
             that field"
        ));
        return;
    }
    // THE FIELD FILLS THE WORD (verifier r8, 2026-09-25). Without this clause a
    // `u32` in an 8-byte struct, or a pointer in a 16-byte one, was refused
    // ONLY because the reference gate happens to probe words above the
    // field's width: cut `reference::probe_words` to small words and every
    // test passed while the projector minted both rows.
    if let Err(why) = d.fills(
        &Ty::Struct(trust_ir::value::StructId::new(raw)),
        &def.fields[i].ty,
    ) {
        refused.push(format!("struct.{raw}: {why}"));
        return;
    }
    match p.ty_of(&def.fields[i].ty.clone()) {
        Ok(payload) => rows.push(Row {
            canonical,
            raw,
            first_by,
            table: d.label.clone(),
            decl: def.name.clone(),
            payload,
            shape: Shape::Wrap {
                slot: i,
                fields: def.fields.len(),
            },
        }),
        Err(e) => refused.push(format!(
            "struct.{raw}: its one non-ZST field has no Clean image: {e}"
        )),
    }
}

/// Project the chain out of the primary module and its merged artifacts, and
/// refuse it when two artifacts' bodies share a raw aggregate id they define
/// differently (see `aggregate_collisions`). With NO certified thread-local
/// cells: every `trust_rust.thread_local_addr` is refused, as before D11.
#[cfg(test)]
fn project_merged(
    module: &trust_ir::Module,
    merged: &[Merged],
    chain: &[&trust_ir::Function],
    usize_bits: Option<u32>,
) -> Result<(String, Projector), String> {
    project_merged_certified(module, merged, chain, usize_bits, BTreeMap::new(), false)
}

/// [`project_merged`], with the thread-local symbols a callee sidecar's
/// manifest CERTIFIES (`--tls-cells`, crystal D11) handed to the projector
/// before any body is walked, so a certified `trust_rust.thread_local_addr`
/// images as the address of its INPUT cell; and with D12's opt-in
/// `--ptr-bitcast-identity` (crystal decision memo §18).
///
/// Every projection, merged or not, images an undefined-behaviour halt as
/// `unreachable` (memo §15/§18): the primary module's UB halt sites and every
/// merged artifact's, relocated by its shift, are handed to the projector
/// before any body is walked.
fn project_merged_certified(
    module: &trust_ir::Module,
    merged: &[Merged],
    chain: &[&trust_ir::Function],
    usize_bits: Option<u32>,
    tls_certified: BTreeMap<String, String>,
    ptr_bitcast_identity: bool,
) -> Result<(String, Projector), String> {
    let conflicts = layout_target_conflicts(module, merged, usize_bits);
    if !conflicts.is_empty() {
        return Err(conflicts.join("; "));
    }
    let mut p = Projector {
        usize_bits,
        tls_certified,
        ptr_bitcast_identity,
        ..Projector::default()
    };
    let (sites, unsited) = ub_halt_sites_of(module, 0);
    p.ub_halt_sites.extend(sites);
    p.ub_unsited.extend(unsited);
    for m in merged {
        p.ub_halt_sites.extend(m.ub_sites.0.iter().copied());
        p.ub_unsited.extend(m.ub_sites.1.iter().copied());
    }
    let core = p.project_chain(module, chain)?;
    let collisions = aggregate_collisions(module, merged, &p);
    if collisions.is_empty() {
        Ok((core, p))
    } else {
        Err(collisions.join("; "))
    }
}

/// An artifact's LAYOUT TARGET as trust-ir computes layouts and runs its
/// reference interpreter under it: pointer width, byte order, and whether the
/// target's scalar alignment is trust-ir's canonical table
/// (`Module::target_has_canonical_scalar_layout`). A target-less artifact is
/// trust-ir's reference model, 64-bit little-endian and canonical
/// (`shape::DEFAULT_POINTER_BITS`), which is what `pointer_bits` answers.
fn layout_target(t: Option<&trust_ir::TargetInfo>) -> (u32, trust_ir::Endianness, bool) {
    let mut probe = trust_ir::Module::new("layout-target-probe");
    probe.target_info = t.cloned();
    (
        probe.pointer_bits(),
        t.map_or(trust_ir::Endianness::Little, |t| t.endianness),
        probe.target_has_canonical_scalar_layout(),
    )
}

/// Whether two artifacts' layout targets agree: the pointer width, the byte
/// order and whether scalars have their canonical layout. The byte orders are
/// matched by name: an order trust-ir adds fails to compile here, where `==`
/// would compare it as one more value (the typed scan follows
/// [`layout_target`]'s `Endianness::Little` default into this comparison).
fn same_layout_target(
    (width, endian, canonical): (u32, trust_ir::Endianness, bool),
    (other_width, other_endian, other_canonical): (u32, trust_ir::Endianness, bool),
) -> bool {
    use trust_ir::Endianness as E;
    width == other_width
        && canonical == other_canonical
        && match (endian, other_endian) {
            (E::Little, E::Little) | (E::Big, E::Big) => true,
            (E::Little, E::Big) | (E::Big, E::Little) => false,
        }
}

/// Why the artifacts cannot be projected as one module: an artifact whose
/// pointer width is not the `--usize-bits` the bodies' `usize` is imaged at,
/// or two artifacts that lay types out under different targets.
///
/// Every layout judgement here -- a `Direct` descriptor against the canonical
/// layout, a niche lane against the pointer word, a row against the reference
/// interpreter -- is made ONCE per raw aggregate id, under the artifact that
/// first named it, and `aggregate_collisions` compares definitions, not
/// targets. So the judgement holds for every artifact exactly when they all
/// share one layout target. Until verifier r7b (2026-09-24) nothing said so: a
/// `Direct { size 16, [[], [8]] }` enum defined identically in a 64-bit primary
/// and a wasm32 merge (canonical 16 bytes at 64 bits, 8 at 32) was judged
/// canonical for the wasm32 body too, and a wasm32 primary under
/// `--usize-bits 64` imaged `usize` as `(uint 64)`. Only a niche row compared
/// its definer's target with the flag.
fn layout_target_conflicts(
    module: &trust_ir::Module,
    merged: &[Merged],
    usize_bits: Option<u32>,
) -> Vec<String> {
    let mut targets = vec![(
        "module".to_string(),
        layout_target(module.target_info.as_ref()),
    )];
    targets.extend(merged.iter().map(|m| {
        (
            format!("merge@{}", m.shift),
            layout_target(m.target.as_ref()),
        )
    }));
    let mut out = Vec::new();
    if let Some(bits) = usize_bits {
        for (who, (width, _, _)) in &targets {
            if *width != bits {
                out.push(format!(
                    "{who} is a {width}-bit-pointer artifact and --usize-bits says {bits}: its \
                     `usize` would image at a width its own layouts do not have"
                ));
            }
        }
    }
    let first = targets[0].1;
    if targets.iter().any(|(_, t)| !same_layout_target(*t, first)) {
        let all: Vec<String> = targets
            .iter()
            .map(|(who, (width, endian, canonical))| {
                format!(
                    "{who} {width}-bit {endian:?}{}",
                    if *canonical {
                        ""
                    } else {
                        " non-canonical-scalars"
                    }
                )
            })
            .collect();
        out.push(format!(
            "the artifacts' layout targets differ ({}): a raw aggregate id is interned once and \
             its layout judged once, so every artifact must lay types out alike",
            all.join(", ")
        ));
    }
    out
}

/// Raw aggregate ids that bodies from two artifacts (the primary counts as
/// one) name while those artifacts' tables DEFINE them differently.
///
/// Aggregate ids are not relocated by `fold_in`, and interning is keyed by the
/// raw id alone, so such an id would print two different types as ONE
/// canonical aggregate — and the encodings derivation would read only the
/// first artifact's definition for both. Until 2026-09-24 this was said to be
/// refused "by the caller measuring disjointness"; no caller measured it, and
/// a two-merge projection of `enum.1` = `one::E` and `enum.1` = `two::E`
/// returned Ok with both at canonical 0.
///
/// The definitions are compared DEEPLY ([`Tables::deep`]): every raw id nested
/// in a definition is resolved through the SAME artifact's tables. The first
/// version compared the printed definitions, and a nested id is printed as a
/// bare number -- so `struct.1 = W { struct.2 }` in both artifacts passed while
/// `struct.2` was `one::P` in one and `two::Q` in the other, both bodies
/// projected `(undef (struct 0))`, and the wrapper row gave both one.bin's
/// payload. Identical definitions, all the way down, are one type and pass.
fn aggregate_collisions(
    module: &trust_ir::Module,
    merged: &[Merged],
    p: &Projector,
) -> Vec<String> {
    let mut out = Vec::new();
    for (kind, named) in [
        (Agg::Enum, &p.enum_named_by),
        (Agg::Struct, &p.struct_named_by),
    ] {
        let tag = match kind {
            Agg::Enum => "enum",
            Agg::Struct => "struct",
        };
        for (raw, funcs) in named {
            let mut defs: BTreeMap<String, String> = BTreeMap::new();
            for f in funcs {
                let d = match definer_of(module, merged, *f) {
                    Ok(d) => d,
                    Err(e) => {
                        out.push(format!("{tag}.{raw}: named by {e}"));
                        continue;
                    }
                };
                let deep = Tables {
                    label: &d.label,
                    enums: d.enums,
                    structs: d.structs,
                    types: d.types,
                }
                .deep(kind, *raw);
                defs.insert(d.label, deep);
            }
            let distinct: BTreeSet<&String> = defs.values().collect();
            if distinct.len() > 1 {
                let who: Vec<&str> = defs.keys().map(String::as_str).collect();
                out.push(format!(
                    "{tag}.{raw} is named by bodies from {} whose tables define it \
                     differently (compared deeply: every raw id nested in a definition is \
                     resolved through its own artifact's tables); aggregate ids are not \
                     relocated, so the two types would intern as ONE canonical aggregate",
                    who.join(" and ")
                ));
            }
        }
    }
    out
}

/// Crystal C-M0 (decision memo §21): WHY a trust-ir type has no Clean `IRTy` image. The three
/// fat-pointer kinds the M0 producer emits are refused BY NAME with what EvalIR lacks for an EXACT
/// image; every other type keeps the generic sentence (the prefix is kept, so a census that groups
/// refusals by it still reads them).
fn no_ty_image(t: &Ty) -> String {
    // Every variant NAMED (an `if let` until main's lint r11 refused its failure branch). Since
    // crystal E5 every fat kind but `Slice` has an image, so no variant carries a named gap.
    match t {
        Ty::Ext(e) => e.unreachable(),
        Ty::FatPtr(_)
        | Ty::Array(..)
        | Ty::Struct(_)
        | Ty::Tuple(_)
        | Ty::Ptr
        | Ty::PtrConst(_)
        | Ty::PtrMut(_)
        | Ty::Ref(_)
        | Ty::RefMut(_)
        | Ty::I8
        | Ty::I16
        | Ty::I32
        | Ty::I64
        | Ty::I128
        | Ty::U8
        | Ty::U16
        | Ty::U32
        | Ty::U64
        | Ty::U128
        | Ty::Isize
        | Ty::Usize
        | Ty::Char
        | Ty::Error
        | Ty::F16
        | Ty::F32
        | Ty::F64
        | Ty::Bool
        | Ty::Unit
        | Ty::Never
        | Ty::Enum(_)
        | Ty::Rc(_)
        | Ty::Vector(..)
        | Ty::Func(_)
        | Ty::Set(..)
        | Ty::Sequence(_)
        | Ty::Record(_)
        | Ty::Closure(_)
        | Ty::Refine(..)
        | Ty::Dialect(_)
        | Ty::Tensor(..)
        | Ty::Storage(_)
        | Ty::Handle(_) => format!("no Clean IRTy image for trust_ir::Ty::{t:?}"),
    }
}

/// Does a fat pointer of this kind carry a VTABLE pointer as its metadata?
fn carries_vtable(kind: &trust_ir::FatPtrKind) -> bool {
    match kind {
        trust_ir::FatPtrKind::TraitObject { .. } | trust_ir::FatPtrKind::ContainerVtable => true,
        trust_ir::FatPtrKind::Slice(_)
        | trust_ir::FatPtrKind::Str
        | trust_ir::FatPtrKind::ContainerLen => false,
    }
}

/// Crystal D14, imaged by E5 (memo §23): certify every use a body makes of a VTABLE word.
///
/// A vtable word is the metadata of a vtable-carrying fat pointer (`ptr_metadata .. to ptr` of a
/// kind `carries_vtable` answers for), followed through `copy`, a pointer-to-pointer `cast` and a
/// `gep` whose indices are constants and whose pointee is a byte (or whose indices are all zero),
/// accumulating a BYTE offset -- the cell machine's GEP is single-scale, so only a byte-stepped
/// offset has the reference's address. Each use of such a pointer must be one of exactly two:
///
///  * a `load usize` at byte offset 8 or 16 -- the SIZE or ALIGN slot of rustc's vtable layout
///    `[drop_in_place, size, align, methods..]` (`COMMON_VTABLE_ENTRIES`), at the 64-bit target
///    this lane pins; the word-per-cell vtable image (`ir_vtable_cells`) answers exactly those
///    reads (`ir_vtable_size_load`, `ir_vtable_align_load`);
///  * the word itself, UNCHANGED (offset 0), as the metadata of a new vtable-carrying wide pointer
///    (`ptr_from_parts`, D14's rebuild of the trait object over the SAME vtable).
///
/// Everything else -- a store through it, a store OF it, a call argument, a return, a branch
/// argument, an `icmp`, a `ptrtoint`, a load of another slot or another width, a non-constant or
/// scaled `gep` -- is refused by name: it would read the region somewhere the image does not
/// certify, or let the word escape to a place no certification follows, and a read-only region
/// must not be written. Returns the certified loads as `(result id, slot offset)`.
fn d14_vtable_certify(
    f: &trust_ir::Function,
    usize_bits: Option<u32>,
) -> Result<Vec<(u32, u64)>, String> {
    let nodes = || f.blocks.iter().flat_map(|b| b.body.iter());
    let mut consts: BTreeMap<u32, i128> = BTreeMap::new();
    for n in nodes() {
        let Some(r) = n.results.first() else {
            continue;
        };
        match vt_node(&n.inst) {
            VtNode::ConstInt(Some(v)) => {
                consts.insert(r.0, v);
            }
            VtNode::ConstInt(None)
            | VtNode::Meta(_)
            | VtNode::Gep { .. }
            | VtNode::Copy(_)
            | VtNode::Cast { .. }
            | VtNode::Load { .. }
            | VtNode::FromParts { .. }
            | VtNode::Other => {}
        }
    }
    // value id -> (the vtable word it derives from, byte offset from that word)
    let mut derived: BTreeMap<u32, (u32, u64)> = BTreeMap::new();
    loop {
        let before = derived.len();
        for n in nodes() {
            let Some(res) = n.results.first() else {
                continue;
            };
            if derived.contains_key(&res.0) {
                continue;
            }
            let hit = match vt_node(&n.inst) {
                VtNode::Meta(Some(kind)) => carries_vtable(kind).then_some((res.0, 0)),
                VtNode::Gep {
                    pointee,
                    base,
                    indices,
                } => match derived.get(&base) {
                    None => None,
                    Some(&(seed, off)) => {
                        Some((seed, gep_bytes(seed, off, pointee, indices, &consts)?))
                    }
                },
                VtNode::Copy(operand) => derived.get(&operand).copied(),
                VtNode::Cast {
                    ptr_to_ptr: true,
                    operand,
                } => derived.get(&operand).copied(),
                VtNode::Meta(None)
                | VtNode::Cast {
                    ptr_to_ptr: false, ..
                }
                | VtNode::Load { .. }
                | VtNode::FromParts { .. }
                | VtNode::ConstInt(_)
                | VtNode::Other => None,
            };
            if let Some(d) = hit {
                derived.insert(res.0, d);
            }
        }
        if derived.len() == before {
            break;
        }
    }
    let mut reads = Vec::new();
    if derived.is_empty() {
        return Ok(reads);
    }
    if usize_bits != Some(64) {
        return Err(format!(
            "the vtable layout is certified at the 64-bit target only (one 8-byte word per slot), \
             and this projection's usize width is {usize_bits:?}"
        ));
    }
    for n in nodes() {
        let mut uses = Vec::new();
        n.inst.visit_value_operands(|v| {
            if let Some(&d) = derived.get(&v.0) {
                uses.push((v.0, d));
            }
        });
        for (v, (seed, off)) in uses {
            let certified = match vt_node(&n.inst) {
                VtNode::Load { usize_word, ptr } if ptr == v => {
                    if usize_word && (off == 8 || off == 16) {
                        reads.push((n.results.first().map_or(u32::MAX, |r| r.0), off));
                        true
                    } else {
                        return Err(format!(
                            "a load of the vtable word %{seed} at byte offset {off} (as %{v}): \
                             the image certifies a `load usize` of the size (+8) and align (+16) \
                             slots only"
                        ));
                    }
                }
                VtNode::Gep { base, indices, .. } => {
                    base == v && indices.iter().all(|ix| ix.0 != v)
                }
                VtNode::Copy(_) => true,
                VtNode::Cast { ptr_to_ptr, .. } => ptr_to_ptr,
                VtNode::FromParts {
                    kind: Some(kind),
                    data,
                    metadata,
                } => carries_vtable(kind) && metadata == v && data != v && off == 0,
                VtNode::Load { .. }
                | VtNode::FromParts { kind: None, .. }
                | VtNode::Meta(_)
                | VtNode::ConstInt(_)
                | VtNode::Other => false,
            };
            if !certified {
                return Err(format!(
                    "the vtable word %{seed} (at byte offset {off}, as %{v}) is an operand of \
                     `{}`, which the vtable image does not certify: only a `load usize` of the \
                     size or align slot, and the unchanged word as a new wide pointer's metadata, \
                     are exact",
                    variant_name(&n.inst)
                ));
            }
        }
    }
    Ok(reads)
}

/// The byte offset a `gep` over a vtable-derived pointer reaches: the cell machine's GEP is
/// SINGLE-SCALE (its index sum is a cell offset), so it agrees with the reference's scaled
/// address only when the pointee is one byte, or every index is zero.
fn gep_bytes(
    seed: u32,
    off: u64,
    pointee: &Ty,
    indices: &[trust_ir::value::ValueId],
    consts: &BTreeMap<u32, i128>,
) -> Result<u64, String> {
    let mut off = off;
    for ix in indices {
        let c = consts.get(&ix.0).copied().ok_or_else(|| {
            format!(
                "a `gep` over the vtable word %{seed} takes the non-constant index %{}",
                ix.0
            )
        })?;
        let c = u64::try_from(c)
            .map_err(|_| format!("a `gep` over the vtable word %{seed} takes index {c}"))?;
        let scale = match vt_ty(pointee) {
            VtTy::Byte => 1,
            VtTy::Thin | VtTy::Usize | VtTy::Other if c == 0 => 0,
            VtTy::Thin | VtTy::Usize | VtTy::Other => {
                return Err(format!(
                    "a `gep {pointee}` over the vtable word %{seed} steps {c} elements: the \
                     cell machine's GEP is single-scale, so only a byte-stepped or zero offset \
                     lands where the reference's does"
                ))
            }
        };
        off = off
            .checked_add(c * scale)
            .ok_or_else(|| format!("a `gep` over the vtable word %{seed} overflows"))?;
    }
    Ok(off)
}

/// What the D14/E5 certification reads off one instruction. [`vt_node`] names every `Inst`
/// variant, so a variant trust-ir adds fails to compile there until someone says what it does
/// with a vtable word.
enum VtNode<'a> {
    /// `ptr_metadata`, with the pointer type's fat kind when it has one.
    Meta(Option<&'a trust_ir::FatPtrKind>),
    Gep {
        pointee: &'a Ty,
        base: u32,
        indices: &'a [trust_ir::value::ValueId],
    },
    Copy(u32),
    /// A `cast`; `ptr_to_ptr` when it is a bitcast/ptrtoptr between two thin pointer types.
    Cast {
        ptr_to_ptr: bool,
        operand: u32,
    },
    /// A plain `load`; `usize_word` when its type is `usize`.
    Load {
        usize_word: bool,
        ptr: u32,
    },
    FromParts {
        kind: Option<&'a trust_ir::FatPtrKind>,
        data: u32,
        metadata: u32,
    },
    /// A `const`, with its value when it is an integer.
    ConstInt(Option<i128>),
    Other,
}

fn vt_node(i: &Inst) -> VtNode<'_> {
    match i {
        Inst::PtrMetadata { ptr_ty, .. } => VtNode::Meta(fat_kind_of(ptr_ty)),
        Inst::GEP {
            pointee_ty,
            base,
            indices,
            ..
        } => VtNode::Gep {
            pointee: pointee_ty,
            base: base.0,
            indices,
        },
        Inst::Copy { operand, .. } => VtNode::Copy(operand.0),
        Inst::Cast {
            op,
            src_ty,
            dst_ty,
            operand,
        } => VtNode::Cast {
            ptr_to_ptr: is_ptr_identity_cast(op)
                && vt_is_thin(vt_ty(src_ty))
                && vt_is_thin(vt_ty(dst_ty)),
            operand: operand.0,
        },
        Inst::Load { ty, ptr, .. } => VtNode::Load {
            usize_word: vt_is_usize(vt_ty(ty)),
            ptr: ptr.0,
        },
        Inst::PtrFromParts {
            ptr_ty,
            data,
            metadata,
            ..
        } => VtNode::FromParts {
            kind: fat_kind_of(ptr_ty),
            data: data.0,
            metadata: metadata.0,
        },
        Inst::Const { value, .. } => VtNode::ConstInt(const_int(value)),
        Inst::BinOp { .. }
        | Inst::UnOp { .. }
        | Inst::Overflow { .. }
        | Inst::ICmp { .. }
        | Inst::FCmp { .. }
        | Inst::Store { .. }
        | Inst::Alloca { .. }
        | Inst::Drop { .. }
        | Inst::HeapAlloc { .. }
        | Inst::PtrData { .. }
        | Inst::AtomicLoad { .. }
        | Inst::AtomicStore { .. }
        | Inst::AtomicRMW { .. }
        | Inst::CmpXchg { .. }
        | Inst::Fence { .. }
        | Inst::Br { .. }
        | Inst::CondBr { .. }
        | Inst::Switch { .. }
        | Inst::Call { .. }
        | Inst::CallIndirect { .. }
        | Inst::Return { .. }
        | Inst::ExtractField { .. }
        | Inst::InsertField { .. }
        | Inst::ExtractElement { .. }
        | Inst::InsertElement { .. }
        | Inst::NullPtr
        | Inst::GlobalAddr { .. }
        | Inst::Undef { .. }
        | Inst::Assume { .. }
        | Inst::Assert { .. }
        | Inst::Unreachable
        | Inst::Select { .. }
        | Inst::SeqMapAddK { .. }
        | Inst::SeqMapNot { .. }
        | Inst::SeqMap { .. }
        | Inst::Borrow { .. }
        | Inst::BorrowMut { .. }
        | Inst::EndBorrow { .. }
        | Inst::Retain { .. }
        | Inst::Release { .. }
        | Inst::IsUnique { .. }
        | Inst::Dealloc { .. }
        | Inst::MemCopy { .. }
        | Inst::MemSet { .. }
        | Inst::OpenFrame { .. }
        | Inst::BindSlot { .. }
        | Inst::LoadSlot { .. }
        | Inst::CloseFrame { .. }
        | Inst::CoroSuspend { .. }
        | Inst::Invoke { .. }
        | Inst::LandingPad { .. }
        | Inst::Resume { .. }
        | Inst::AssertInvoke { .. }
        | Inst::ArraySplat { .. }
        | Inst::CallCannotUnwind { .. }
        | Inst::CallIndirectCannotUnwind { .. }
        | Inst::DropInvoke { .. }
        | Inst::InvokeIndirect { .. }
        | Inst::DialectOp(..)
        | Inst::MakeAggregate { .. }
        | Inst::TensorContract { .. }
        | Inst::TensorMap { .. }
        | Inst::TensorReduce { .. }
        | Inst::TensorView { .. }
        | Inst::TensorGather { .. }
        | Inst::TensorScatter { .. }
        | Inst::MakeClosure { .. } => VtNode::Other,
    }
}

/// The pointer-class of a type, as far as the vtable certification needs it.
#[derive(Clone, Copy, PartialEq, Eq)]
enum VtTy {
    Thin,
    Byte,
    Usize,
    Other,
}

fn vt_ty(t: &Ty) -> VtTy {
    match t {
        Ty::Ext(e) => e.unreachable(),
        Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_) | Ty::Rc(_) => {
            VtTy::Thin
        }
        Ty::I8 | Ty::U8 => VtTy::Byte,
        Ty::Usize => VtTy::Usize,
        Ty::I16
        | Ty::I32
        | Ty::I64
        | Ty::I128
        | Ty::U16
        | Ty::U32
        | Ty::U64
        | Ty::U128
        | Ty::Isize
        | Ty::Char
        | Ty::Error
        | Ty::F16
        | Ty::F32
        | Ty::F64
        | Ty::Bool
        | Ty::Vector(..)
        | Ty::FatPtr(_)
        | Ty::Unit
        | Ty::Never
        | Ty::Struct(_)
        | Ty::Array(..)
        | Ty::Tuple(_)
        | Ty::Enum(_)
        | Ty::Func(_)
        | Ty::Set(..)
        | Ty::Sequence(_)
        | Ty::Record(_)
        | Ty::Closure(_)
        | Ty::Refine(..)
        | Ty::Dialect(_)
        | Ty::Tensor(..)
        | Ty::Storage(_)
        | Ty::Handle(_) => VtTy::Other,
    }
}

fn fat_kind_of(t: &Ty) -> Option<&trust_ir::FatPtrKind> {
    match t {
        Ty::Ext(e) => e.unreachable(),
        Ty::FatPtr(kind) => Some(kind),
        Ty::I8
        | Ty::I16
        | Ty::I32
        | Ty::I64
        | Ty::I128
        | Ty::U8
        | Ty::U16
        | Ty::U32
        | Ty::U64
        | Ty::U128
        | Ty::Isize
        | Ty::Usize
        | Ty::Char
        | Ty::Error
        | Ty::F16
        | Ty::F32
        | Ty::F64
        | Ty::Bool
        | Ty::Vector(..)
        | Ty::Ptr
        | Ty::Unit
        | Ty::Never
        | Ty::Struct(_)
        | Ty::Array(..)
        | Ty::Tuple(_)
        | Ty::Enum(_)
        | Ty::Func(_)
        | Ty::Ref(_)
        | Ty::RefMut(_)
        | Ty::PtrConst(_)
        | Ty::PtrMut(_)
        | Ty::Rc(_)
        | Ty::Set(..)
        | Ty::Sequence(_)
        | Ty::Record(_)
        | Ty::Closure(_)
        | Ty::Refine(..)
        | Ty::Dialect(_)
        | Ty::Tensor(..)
        | Ty::Storage(_)
        | Ty::Handle(_) => None,
    }
}

/// A cast that leaves a pointer's address and provenance alone: `bitcast` and `ptrtoptr`.
/// `bitcast`, named against every other cast. A `match`, not `*op != CastOp::Bitcast`: main's
/// lint r11b refuses a variant told apart by value (its other outcome is a catch-all over the
/// enum that compiles unchanged when trust-ir adds a cast).
fn cast_is_bitcast(op: &CastOp) -> bool {
    match op {
        CastOp::Bitcast => true,
        CastOp::PtrToPtr
        | CastOp::Trunc
        | CastOp::ZExt
        | CastOp::SExt
        | CastOp::FPTrunc
        | CastOp::FPExt
        | CastOp::FPToUI
        | CastOp::FPToSI
        | CastOp::UIToFP
        | CastOp::SIToFP
        | CastOp::PtrToInt
        | CastOp::IntToPtr
        | CastOp::Transmute
        | CastOp::ReifyFnPointer
        | CastOp::FPToSISat
        | CastOp::FPToUISat => false,
    }
}

/// The bare `ptr` type, named against every other type (the same r11b rule).
fn ty_is_bare_ptr(t: &Ty) -> bool {
    match t {
        Ty::Ptr => true,
        Ty::I8
        | Ty::I16
        | Ty::I32
        | Ty::I64
        | Ty::I128
        | Ty::U8
        | Ty::U16
        | Ty::U32
        | Ty::U64
        | Ty::U128
        | Ty::Isize
        | Ty::Usize
        | Ty::Char
        | Ty::Error
        | Ty::F16
        | Ty::F32
        | Ty::F64
        | Ty::Bool
        | Ty::Vector(..)
        | Ty::FatPtr(_)
        | Ty::Unit
        | Ty::Never
        | Ty::Struct(_)
        | Ty::Array(..)
        | Ty::Tuple(_)
        | Ty::Enum(_)
        | Ty::Func(_)
        | Ty::Ref(_)
        | Ty::RefMut(_)
        | Ty::PtrConst(_)
        | Ty::PtrMut(_)
        | Ty::Rc(_)
        | Ty::Set(..)
        | Ty::Sequence(_)
        | Ty::Record(_)
        | Ty::Closure(_)
        | Ty::Refine(..)
        | Ty::Dialect(_)
        | Ty::Tensor(..)
        | Ty::Storage(_)
        | Ty::Handle(_) => false,
        Ty::Ext(e) => e.unreachable(),
    }
}

/// `const bool false`, the halting shape of an `assert`: every instruction, type and constant
/// named (the same r11b rule; until the train-clean-1 merge this was an `==` against a built
/// `Inst::Const`).
fn inst_is_const_bool_false(i: &Inst) -> bool {
    match i {
        Inst::Const { ty, value } => {
            let bool_ty = match ty {
                Ty::Bool => true,
                Ty::I8
                | Ty::I16
                | Ty::I32
                | Ty::I64
                | Ty::I128
                | Ty::U8
                | Ty::U16
                | Ty::U32
                | Ty::U64
                | Ty::U128
                | Ty::Isize
                | Ty::Usize
                | Ty::Char
                | Ty::Error
                | Ty::F16
                | Ty::F32
                | Ty::F64
                | Ty::Vector(..)
                | Ty::Ptr
                | Ty::FatPtr(_)
                | Ty::Unit
                | Ty::Never
                | Ty::Struct(_)
                | Ty::Array(..)
                | Ty::Tuple(_)
                | Ty::Enum(_)
                | Ty::Func(_)
                | Ty::Ref(_)
                | Ty::RefMut(_)
                | Ty::PtrConst(_)
                | Ty::PtrMut(_)
                | Ty::Rc(_)
                | Ty::Set(..)
                | Ty::Sequence(_)
                | Ty::Record(_)
                | Ty::Closure(_)
                | Ty::Refine(..)
                | Ty::Dialect(_)
                | Ty::Tensor(..)
                | Ty::Storage(_)
                | Ty::Handle(_) => false,
                Ty::Ext(e) => e.unreachable(),
            };
            let false_value = match value {
                Constant::Bool(b) => !*b,
                Constant::Int(_)
                | Constant::U128(_)
                | Constant::Bytes { .. }
                | Constant::Float(_)
                | Constant::Aggregate(_)
                | Constant::Array(_)
                | Constant::Splat { .. }
                | Constant::Vector(_)
                | Constant::Sequence(_)
                | Constant::Set(_)
                | Constant::Record(_)
                | Constant::Closure { .. }
                | Constant::FnDef(_)
                | Constant::SymbolAddr { .. }
                | Constant::PhantomData
                | Constant::Uninit
                | Constant::TensorBlob { .. } => false,
                Constant::Ext(e) => e.unreachable(),
            };
            bool_ty && false_value
        }
        Inst::BinOp { .. }
        | Inst::UnOp { .. }
        | Inst::Overflow { .. }
        | Inst::ICmp { .. }
        | Inst::FCmp { .. }
        | Inst::Cast { .. }
        | Inst::Load { .. }
        | Inst::Store { .. }
        | Inst::Alloca { .. }
        | Inst::Drop { .. }
        | Inst::HeapAlloc { .. }
        | Inst::GEP { .. }
        | Inst::PtrData { .. }
        | Inst::PtrMetadata { .. }
        | Inst::PtrFromParts { .. }
        | Inst::AtomicLoad { .. }
        | Inst::AtomicStore { .. }
        | Inst::AtomicRMW { .. }
        | Inst::CmpXchg { .. }
        | Inst::Fence { .. }
        | Inst::Br { .. }
        | Inst::CondBr { .. }
        | Inst::Switch { .. }
        | Inst::Call { .. }
        | Inst::CallIndirect { .. }
        | Inst::Return { .. }
        | Inst::ExtractField { .. }
        | Inst::InsertField { .. }
        | Inst::ExtractElement { .. }
        | Inst::InsertElement { .. }
        | Inst::NullPtr
        | Inst::GlobalAddr { .. }
        | Inst::Undef { .. }
        | Inst::Assume { .. }
        | Inst::Assert { .. }
        | Inst::Unreachable
        | Inst::Copy { .. }
        | Inst::Select { .. }
        | Inst::SeqMapAddK { .. }
        | Inst::SeqMapNot { .. }
        | Inst::SeqMap { .. }
        | Inst::Borrow { .. }
        | Inst::BorrowMut { .. }
        | Inst::EndBorrow { .. }
        | Inst::Retain { .. }
        | Inst::Release { .. }
        | Inst::IsUnique { .. }
        | Inst::Dealloc { .. }
        | Inst::MemCopy { .. }
        | Inst::MemSet { .. }
        | Inst::OpenFrame { .. }
        | Inst::BindSlot { .. }
        | Inst::LoadSlot { .. }
        | Inst::CloseFrame { .. }
        | Inst::CoroSuspend { .. }
        | Inst::Invoke { .. }
        | Inst::LandingPad { .. }
        | Inst::Resume { .. }
        | Inst::AssertInvoke { .. }
        | Inst::DialectOp(..)
        | Inst::MakeAggregate { .. }
        | Inst::TensorContract { .. }
        | Inst::TensorMap { .. }
        | Inst::TensorReduce { .. }
        | Inst::TensorView { .. }
        | Inst::TensorGather { .. }
        | Inst::TensorScatter { .. }
        | Inst::MakeClosure { .. }
        | Inst::ArraySplat { .. }
        | Inst::CallCannotUnwind { .. }
        | Inst::CallIndirectCannotUnwind { .. }
        | Inst::DropInvoke { .. }
        | Inst::InvokeIndirect { .. } => false,
    }
}

/// `VtTy::Thin`, named against the other classes (main's lint r11b refuses `== VtTy::Thin`).
fn vt_is_thin(t: VtTy) -> bool {
    match t {
        VtTy::Thin => true,
        VtTy::Byte | VtTy::Usize | VtTy::Other => false,
    }
}

/// `VtTy::Usize`, named against the other classes (the same r11b rule).
fn vt_is_usize(t: VtTy) -> bool {
    match t {
        VtTy::Usize => true,
        VtTy::Thin | VtTy::Byte | VtTy::Other => false,
    }
}

/// The key `check_metadata_ty` compares a canonical pointer metadata type by: `()` (a thin
/// pointer), the `ptr` vtable word, or an unsigned length of one width. Every type is named
/// (main's lint r11b refuses comparing the types by value); every other type keys `None`.
fn metadata_ty_key(t: &Ty) -> Option<u8> {
    match t {
        Ty::Unit => Some(0),
        Ty::Ptr => Some(1),
        Ty::Usize => Some(2),
        Ty::U8 => Some(8),
        Ty::U16 => Some(16),
        Ty::U32 => Some(32),
        Ty::U64 => Some(64),
        Ty::U128 => Some(128),
        Ty::I8
        | Ty::I16
        | Ty::I32
        | Ty::I64
        | Ty::I128
        | Ty::Isize
        | Ty::Char
        | Ty::Error
        | Ty::F16
        | Ty::F32
        | Ty::F64
        | Ty::Bool
        | Ty::Vector(..)
        | Ty::FatPtr(_)
        | Ty::Never
        | Ty::Struct(_)
        | Ty::Array(..)
        | Ty::Tuple(_)
        | Ty::Enum(_)
        | Ty::Func(_)
        | Ty::Ref(_)
        | Ty::RefMut(_)
        | Ty::PtrConst(_)
        | Ty::PtrMut(_)
        | Ty::Rc(_)
        | Ty::Set(..)
        | Ty::Sequence(_)
        | Ty::Record(_)
        | Ty::Closure(_)
        | Ty::Refine(..)
        | Ty::Dialect(_)
        | Ty::Tensor(..)
        | Ty::Storage(_)
        | Ty::Handle(_) => None,
        Ty::Ext(e) => e.unreachable(),
    }
}

fn is_ptr_identity_cast(op: &CastOp) -> bool {
    match op {
        CastOp::Bitcast | CastOp::PtrToPtr => true,
        CastOp::Trunc
        | CastOp::ZExt
        | CastOp::SExt
        | CastOp::FPTrunc
        | CastOp::FPExt
        | CastOp::FPToUI
        | CastOp::FPToSI
        | CastOp::UIToFP
        | CastOp::SIToFP
        | CastOp::PtrToInt
        | CastOp::IntToPtr
        | CastOp::Transmute
        | CastOp::ReifyFnPointer
        | CastOp::FPToSISat
        | CastOp::FPToUISat => false,
    }
}

fn const_int(c: &Constant) -> Option<i128> {
    match c {
        Constant::Int(v) => Some(*v),
        Constant::U128(_)
        | Constant::Bytes { .. }
        | Constant::Float(_)
        | Constant::Bool(_)
        | Constant::Aggregate(_)
        | Constant::Array(_)
        | Constant::Vector(_)
        | Constant::Sequence(_)
        | Constant::Set(_)
        | Constant::Record(_)
        | Constant::Closure { .. }
        | Constant::FnDef(_)
        | Constant::SymbolAddr { .. }
        | Constant::PhantomData
        | Constant::Uninit
        | Constant::TensorBlob { .. }
        | Constant::Splat { .. } => None,
        Constant::Ext(e) => e.unreachable(),
    }
}

/// The trust bridge's wording of an undefined-behaviour halt obligation (trust-ir-bridge
/// `lower.rs`, `CallHalt::UndefinedBehavior`), matched exactly -- the same regex the link-3
/// reconcile reads (`_UB_RE`).
fn is_ub_halt_description(d: &str) -> bool {
    d.strip_prefix("reaching `")
        .and_then(|rest| {
            rest.strip_suffix(
                "` is undefined behavior; this program point must be proven unreachable",
            )
        })
        .is_some_and(|callee| !callee.contains('`'))
}

/// Crystal (memo §15/§18): every undefined-behaviour halt obligation of `module`, as its site
/// (function id + `shift`, block id, instruction index), and the function ids (u32::MAX when
/// none) of such obligations that carry no site.
type UbSites = (
    std::collections::BTreeSet<(u32, u32, u32)>,
    std::collections::BTreeSet<u32>,
);

fn ub_halt_sites_of(module: &trust_ir::Module, shift: u32) -> UbSites {
    let mut sites = std::collections::BTreeSet::new();
    let mut unsited = std::collections::BTreeSet::new();
    for o in &module.proof_obligations {
        if !is_ub_halt_description(&o.description) {
            continue;
        }
        match o.site {
            Some(s) => {
                sites.insert((s.function.0 + shift, s.block.0, s.inst_index));
            }
            None => {
                unsited.insert(o.function.map_or(u32::MAX, |f| f.0 + shift));
            }
        }
    }
    (sites, unsited)
}

fn shift_ub_sites((sites, unsited): UbSites, shift: u32) -> UbSites {
    (
        sites
            .into_iter()
            .map(|(f, b, k)| (f + shift, b, k))
            .collect(),
        unsited
            .into_iter()
            .map(|f| if f == u32::MAX { f } else { f + shift })
            .collect(),
    )
}

/// Fold a merged artifact's functions into `primary`, relocating their ids.
///
/// A `FuncId` is an index into its own module, so the same number names
/// different functions in two artifacts. Every merged function's own id, and
/// every call to a merged function, is shifted above the highest id the
/// primary carries. Nothing else moves.
///
/// FAIL-CLOSED, and the refusals are the argument that nothing else needs to:
///
/// * the merged artifact must declare NO global — this projector reads
///   `module.globals` for a global's bytes, and a merged global would be read
///   out of the wrong table;
/// * a merged body must carry no instruction that names a function other than
///   through `Inst::Call`. `Invoke`, `CallIndirect`'s signature id, a
///   `Constant::FnDef`, `Constant::Closure`, `Inst::MakeClosure` or `Constant::SymbolAddr` (by
///   name) and the element-op loop's `fwd` all carry one or may, none of them
///   appears in the Phase-B bundle, and a
///   relocation that silently missed one would produce a module calling the
///   wrong function. So they are REFUSED rather than handled untested, as are
///   a `GlobalAddr` (by the rule above) and an opaque `DialectOp`. The match
///   that enforces this names every `Inst` variant, with no wildcard.
///
/// The aggregate ids deliberately do NOT move: they intern into canonical
/// indices by first use, under ONE namespace. So bodies from two artifacts
/// USING the same raw id for different types would be interned as one type;
/// `aggregate_collisions` refuses that after projection, and
/// `ir_mint::interface_aggregates` checks the Clean side.
fn fold_in(primary: &mut trust_ir::Module, other: trust_ir::Module, path: &str) -> u32 {
    assert!(
        other.globals.is_empty(),
        "--merge {path} declares {} global(s); this projector reads a global's bytes out of the \
         PRIMARY module's table, so a merged global would be read from the wrong artifact",
        other.globals.len()
    );
    let shift = primary
        .functions
        .iter()
        .map(|f| f.id.0)
        .max()
        .map_or(0, |m| m + 1);
    let ids: std::collections::BTreeSet<u32> = other.functions.iter().map(|f| f.id.0).collect();
    for mut f in other.functions {
        let before = f.id.0;
        f.id = trust_ir::value::FuncId::new(before + shift);
        for b in &mut f.blocks {
            for n in &mut b.body {
                match &mut n.inst {
                    trust_ir::inst::Inst::Call { callee, .. } => {
                        assert!(
                            ids.contains(&callee.0),
                            "--merge {path}: `{}` calls @func.{} which the merged artifact does \
                             not define; a cross-artifact call cannot be relocated without \
                             knowing which artifact it meant",
                            f.name,
                            callee.0
                        );
                        *callee = trust_ir::value::FuncId::new(callee.0 + shift);
                    }
                    trust_ir::inst::Inst::Invoke { .. }
                    | trust_ir::inst::Inst::CallIndirect { .. } => panic!(
                        "--merge {path}: `{}` carries an `Invoke`/`CallIndirect`; both name a \
                         function and neither is relocated here, so it is refused rather than \
                         handled untested",
                        f.name
                    ),
                    // trust-ir v53-v56: the no-unwind call boundaries, the unwinding
                    // twins, v63 closures and a sited check name a function (a callee, a panic
                    // entry, a landing pad's edge targets) or a global (a panic
                    // location) that this relocation does not move.
                    Inst::CallCannotUnwind { .. }
                    | Inst::CallIndirectCannotUnwind { .. }
                    | Inst::InvokeIndirect { .. }
                    | Inst::AssertInvoke { .. }
                    | Inst::DropInvoke { .. }
                    | Inst::TensorContract { .. }
                    | Inst::TensorMap { .. }
                    | Inst::TensorReduce { .. }
                    | Inst::TensorView { .. }
                    | Inst::TensorGather { .. }
                    | Inst::TensorScatter { .. }
                    | Inst::MakeClosure { .. } => panic!(
                        "--merge {path}: `{}` carries a trust_ir::Inst::{}, which names a \
                         function or global this relocation does not move; refused rather \
                         than merged pointing into the wrong artifact",
                        f.name,
                        variant_name(&n.inst)
                    ),
                    // A sited check (trust-ir v54) names its panic entry and may name a
                    // location global; a siteless one names neither.
                    Inst::Assert {
                        cond: _,
                        kind: _,
                        site,
                    } => {
                        if site.is_some() {
                            panic!(
                                "--merge {path}: `{}` carries a sited trust_ir::Inst::Assert, \
                                 whose panic entry this relocation does not move; refused",
                                f.name
                            );
                        }
                    }
                    // The contract above says these are REFUSED; until
                    // 2026-09-23 they fell through a `_ => {}` and were merged
                    // UNRELOCATED, so a merged `FnDef` constant or `SeqMap`
                    // loop would have named the primary's function of the same
                    // number. `GlobalAddr` names a global, and the merged
                    // artifact declares none (asserted above), so it could only
                    // resolve against the PRIMARY's table. A `DialectOp`'s
                    // attributes are opaque to this relocation.
                    Inst::SeqMap { .. } | Inst::GlobalAddr { .. } | Inst::DialectOp(..) => panic!(
                        "--merge {path}: `{}` carries a trust_ir::Inst::{}, which names a \
                         function or global this relocation does not move; refused rather \
                         than merged pointing into the wrong artifact",
                        f.name,
                        variant_name(&n.inst)
                    ),
                    Inst::Const { value, .. } if constant_may_name_function(value) => panic!(
                        "--merge {path}: `{}` carries a constant that may name a function \
                         (`FnDef`/`Closure`/`SymbolAddr`); it is not relocated here, so it is \
                         refused",
                        f.name
                    ),
                    // No `FuncId` or `GlobalId` operand: nothing to relocate.
                    // Every variant NAMED, so a variant trust-ir adds later fails
                    // to compile here until someone says whether it carries one.
                    // WS3.20 `MemCopy`/`MemSet` (trust-ir 4f09dab8) carry
                    // `ValueId`s only (dst/src/byte/bytes). v47's `Drop`
                    // carries a `Ty` and one `ValueId` (the dropped pointer):
                    // no function or global to relocate here, and
                    // `Projector::inst` refuses it on projection. v50's
                    // `ArraySplat` likewise carries a `Ty` and one `ValueId`
                    // (the repeated element), and is refused on projection.
                    Inst::Const { .. }
                    | Inst::Drop { .. }
                    | Inst::ArraySplat { .. }
                    | Inst::BinOp { .. }
                    | Inst::UnOp { .. }
                    | Inst::Overflow { .. }
                    | Inst::ICmp { .. }
                    | Inst::FCmp { .. }
                    | Inst::Cast { .. }
                    | Inst::Load { .. }
                    | Inst::Store { .. }
                    | Inst::Alloca { .. }
                    | Inst::HeapAlloc { .. }
                    | Inst::GEP { .. }
                    | Inst::PtrData { .. }
                    | Inst::PtrMetadata { .. }
                    | Inst::PtrFromParts { .. }
                    | Inst::AtomicLoad { .. }
                    | Inst::AtomicStore { .. }
                    | Inst::AtomicRMW { .. }
                    | Inst::CmpXchg { .. }
                    | Inst::Fence { .. }
                    | Inst::Br { .. }
                    | Inst::CondBr { .. }
                    | Inst::Switch { .. }
                    | Inst::Return { .. }
                    | Inst::ExtractField { .. }
                    | Inst::InsertField { .. }
                    | Inst::ExtractElement { .. }
                    | Inst::InsertElement { .. }
                    | Inst::NullPtr
                    | Inst::Undef { .. }
                    | Inst::Assume { .. }
                    | Inst::Unreachable
                    | Inst::Copy { .. }
                    | Inst::Select { .. }
                    | Inst::SeqMapAddK { .. }
                    | Inst::SeqMapNot { .. }
                    | Inst::Borrow { .. }
                    | Inst::BorrowMut { .. }
                    | Inst::EndBorrow { .. }
                    | Inst::Retain { .. }
                    | Inst::Release { .. }
                    | Inst::IsUnique { .. }
                    | Inst::Dealloc { .. }
                    | Inst::MemCopy { .. }
                    | Inst::MemSet { .. }
                    | Inst::OpenFrame { .. }
                    | Inst::BindSlot { .. }
                    | Inst::LoadSlot { .. }
                    | Inst::CloseFrame { .. }
                    | Inst::CoroSuspend { .. }
                    | Inst::LandingPad { .. }
                    | Inst::Resume { .. }
                    | Inst::MakeAggregate { .. } => {}
                }
            }
        }
        primary.functions.push(f);
    }
    shift
}

/// The `(declaration id, sidecar member id)` pairs a sidecar manifest joins.
///
/// Read with a LINE scan rather than a JSON parser, and that is a deliberate
/// bound rather than a shortcut: this producer has no JSON dependency and
/// hand-writes its own provenance, and the manifest is machine-written one
/// root per line with `crate_decl_func_ids` and `sidecar_func_id` on the SAME
/// line. A member's line carries the second key and not the first, so
/// requiring BOTH selects exactly the roots. Every other shape is refused.
fn joins_of(text: &str, path: &str) -> Vec<(u32, u32)> {
    let field = |line: &str, key: &str| -> Option<String> {
        let at = line.find(&format!("\"{key}\""))?;
        let rest = &line[at + key.len() + 2..];
        let start = rest.find(':')? + 1;
        let tail = rest[start..].trim_start();
        let end = tail.find([',', '}'])?;
        Some(tail[..end].trim().to_string())
    };
    let mut out = Vec::new();
    for line in text.lines() {
        let Some(decls) = field(line, "crate_decl_func_ids") else {
            continue;
        };
        let Some(member) = field(line, "sidecar_func_id") else {
            panic!(
                "--join {path}: a root row carries `crate_decl_func_ids` and no `sidecar_func_id`"
            )
        };
        let outcome = field(line, "outcome").unwrap_or_default();
        // A `subsumed: reached from <parent>` root (callee-sidecar manifest v3, 2026-09-24)
        // names its member by `sidecar_func_id` exactly as a resolved root does: the producer
        // matched the closure's own DefId to that member's Item body, and Clean's
        // `crystal_link3_reconcile.py` re-verifies it. So it joins like a resolved root.
        assert!(
            outcome.contains("resolved") || outcome.starts_with("\"subsumed: "),
            "--join {path}: root with declarations {decls} is {outcome}, neither resolved nor \
             subsumed; an unresolved root has no body to retarget to"
        );
        let ids: Vec<u32> = decls
            .trim_start_matches('[')
            .trim_end_matches(']')
            .split(',')
            .filter(|t| !t.trim().is_empty())
            .map(|t| t.trim().parse().expect("a declaration id"))
            .collect();
        assert_eq!(
            ids.len(),
            1,
            "--join {path}: a root joins {} declarations; retargeting is only defined for one",
            ids.len()
        );
        out.push((ids[0], member.parse().expect("a sidecar member id")));
    }
    out
}

/// Point every call to `decl` at `body` instead, across the whole module.
///
/// This is what makes the merged module CLOSED. The crate module carries the
/// foreign callee as a bodyless DECLARATION and the caller calls it; the
/// sidecar supplies the body. Without this the module holds both and the call
/// still names the declaration, so `ir_call_exec` goes `stuck no_func` exactly
/// where it did before the sidecar existed.
///
/// Fail-closed: the declaration must exist and must be bodyless. Retargeting a
/// call away from a function that HAS a body would silently change which
/// program the module denotes.
fn retarget(module: &mut trust_ir::Module, decl: u32, body: u32, path: &str) {
    let d = module
        .functions
        .iter()
        .find(|f| f.id.0 == decl)
        .unwrap_or_else(|| {
            panic!("--join {path}: declaration @func.{decl} is not in the artifact")
        });
    assert!(
        d.blocks.is_empty(),
        "--join {path}: @func.{decl} (`{}`) HAS a body; retargeting a call away from a body \
         would change which program this module denotes",
        d.name
    );
    assert!(
        module.functions.iter().any(|f| f.id.0 == body),
        "--join {path}: body @func.{body} is not in the merged artifact"
    );
    for f in &mut module.functions {
        for b in &mut f.blocks {
            for n in &mut b.body {
                if let Some(callee) = call_target(&mut n.inst).filter(|c| c.0 == decl) {
                    *callee = trust_ir::value::FuncId::new(body);
                }
            }
        }
    }
}

/// The function an `Inst::Call` names -- what a `--join` retargets. Every
/// other variant is NAMED, so a variant trust-ir adds fails to compile here
/// until someone says whether it is a call to retarget. None of the others is:
/// `Invoke`, `SeqMap` and a function constant name one but have no image in the
/// projection (and `fold_in` refuses them in a merged body), and
/// `CallIndirect` names none. Until lane r11 this was an `if let`, whose
/// failure branch no wildcard lint and no scan read.
fn call_target(inst: &mut Inst) -> Option<&mut trust_ir::value::FuncId> {
    match inst {
        Inst::Call { callee, .. } => Some(callee),
        // trust-ir v47's `Drop` carries a `Ty` and the dropped pointer, and
        // v50's `ArraySplat` a `Ty` and the repeated element: no callee (the
        // projection refuses both by name).
        Inst::Drop { .. }
        | Inst::ArraySplat { .. }
        | Inst::Invoke { .. }
        | Inst::CallIndirect { .. }
        // trust-ir v53-v56: no image in the projection, which refuses each by name.
        | Inst::CallCannotUnwind { .. }
        | Inst::CallIndirectCannotUnwind { .. }
        | Inst::InvokeIndirect { .. }
        | Inst::AssertInvoke { .. }
        | Inst::DropInvoke { .. }
        | Inst::SeqMap { .. }
        | Inst::GlobalAddr { .. }
        | Inst::DialectOp(..)
        | Inst::Const { .. }
        | Inst::BinOp { .. }
        | Inst::UnOp { .. }
        | Inst::Overflow { .. }
        | Inst::ICmp { .. }
        | Inst::FCmp { .. }
        | Inst::Cast { .. }
        | Inst::Load { .. }
        | Inst::Store { .. }
        | Inst::Alloca { .. }
        | Inst::HeapAlloc { .. }
        | Inst::GEP { .. }
        | Inst::PtrData { .. }
        | Inst::PtrMetadata { .. }
        | Inst::PtrFromParts { .. }
        | Inst::AtomicLoad { .. }
        | Inst::AtomicStore { .. }
        | Inst::AtomicRMW { .. }
        | Inst::CmpXchg { .. }
        | Inst::Fence { .. }
        | Inst::Br { .. }
        | Inst::CondBr { .. }
        | Inst::Switch { .. }
        | Inst::Return { .. }
        | Inst::ExtractField { .. }
        | Inst::InsertField { .. }
        | Inst::ExtractElement { .. }
        | Inst::InsertElement { .. }
        | Inst::NullPtr
        | Inst::Undef { .. }
        | Inst::Assume { .. }
        | Inst::Assert { .. }
        | Inst::Unreachable
        | Inst::Copy { .. }
        | Inst::Select { .. }
        | Inst::SeqMapAddK { .. }
        | Inst::SeqMapNot { .. }
        | Inst::Borrow { .. }
        | Inst::BorrowMut { .. }
        | Inst::EndBorrow { .. }
        | Inst::Retain { .. }
        | Inst::Release { .. }
        | Inst::IsUnique { .. }
        | Inst::Dealloc { .. }
        | Inst::MemCopy { .. }
        | Inst::MemSet { .. }
        | Inst::OpenFrame { .. }
        | Inst::BindSlot { .. }
        | Inst::LoadSlot { .. }
        | Inst::CloseFrame { .. }
        | Inst::CoroSuspend { .. }
        | Inst::LandingPad { .. }
        | Inst::Resume { .. }
        | Inst::MakeAggregate { .. }
        | Inst::TensorContract { .. }
        | Inst::TensorMap { .. }
        | Inst::TensorReduce { .. }
        | Inst::TensorView { .. }
        | Inst::TensorGather { .. }
        | Inst::TensorScatter { .. }
        | Inst::MakeClosure { .. } => None,
    }
}

// ── THE MODULES BELOW ARE INLINE ──────────────────────────────────────────────
//
// `ops` and `deep` were `src/ops.rs` and `src/deep.rs` until verifier r7
// (2026-09-24), when the registry pinned ONE file of this crate and a mutation
// committed to `src/deep.rs` left GATE_REGISTRY ok. They stay inline, but that
// is no longer what holds the pin: since verifier r8b (2026-09-25) the
// `check_lint_coverage` row pins every git-tracked file of this crate, a set
// scripts/check_lint_coverage.py DERIVES (`--pinned-inputs`) -- a second file
// joins it without anyone listing it.

mod ops {
    //! The six operator alphabets, `trust_ir` spelling to core spelling.
    //!
    //! Kept 1:1 with `clean-verify`'s `ir_mint::shape` tables: a name that appears
    //! here and not there (or the reverse) is a hole in the pipeline, and the
    //! `shape_table_is_a_bijection_in_both_directions` test on the Clean side is
    //! what makes such a hole fail rather than silently mint the wrong operator.
    //! Anything without a Clean image refuses; nothing is approximated.

    use super::R;

    pub(super) fn binop(op: trust_ir::inst::BinOp) -> R<&'static str> {
        use trust_ir::inst::BinOp as B;
        Ok(match op {
            B::Add => "add",
            B::Sub => "sub",
            B::Mul => "mul",
            B::UDiv => "udiv",
            B::SDiv => "sdiv",
            B::URem => "urem",
            B::SRem => "srem",
            B::FAdd => "fadd",
            B::FSub => "fsub",
            B::FMul => "fmul",
            B::FDiv => "fdiv",
            B::FRem => "frem",
            B::FMin => "fmin",
            B::FMax => "fmax",
            B::And => "and",
            B::Or => "or",
            B::Xor => "xor",
            B::Shl => "shl",
            B::LShr => "lshr",
            B::AShr => "ashr",
            // No `IRBinOp` constructor: the three boolean ops, and the WS3.20
            // (trust-ir 4f09dab8) rotates and IEEE copySign. Named, not a
            // wildcard, so the next trust-ir BinOp fails to compile HERE instead
            // of being refused (or, worse, imaged) without anyone looking.
            B::BAnd | B::BOr | B::BXor | B::RotL | B::RotR | B::FCopySign => {
                return Err(format!("no IRBinOp image for {op:?}"))
            }
        })
    }

    pub(super) fn unop(op: trust_ir::inst::UnOp) -> R<&'static str> {
        use trust_ir::inst::UnOp as U;
        Ok(match op {
            U::Neg => "neg",
            U::FNeg => "fneg",
            U::FAbs => "fabs",
            U::FSqrt => "fsqrt",
            U::FFloor => "ffloor",
            U::FCeil => "fceil",
            U::FTrunc => "ftrunc",
            U::Not => "not",
            U::CtPop => "ctpop",
            // WS3.20 (trust-ir 4f09dab8): `IRUnOp` has no constructor for these,
            // so a projection that meets one refuses by name, never approximates.
            U::CtLz | U::CtTz | U::BSwap | U::BitReverse => {
                return Err(format!("no IRUnOp image for {op:?}"))
            }
        })
    }

    pub(super) fn ovop(op: trust_ir::inst::OverflowOp) -> &'static str {
        use trust_ir::inst::OverflowOp as O;
        match op {
            O::AddOverflow => "addoverflow",
            O::SubOverflow => "suboverflow",
            O::MulOverflow => "muloverflow",
        }
    }

    pub(super) fn icmp(op: trust_ir::inst::ICmpOp) -> &'static str {
        use trust_ir::inst::ICmpOp as I;
        match op {
            I::Eq => "eq",
            I::Ne => "ne",
            I::Ult => "ult",
            I::Ule => "ule",
            I::Ugt => "ugt",
            I::Uge => "uge",
            I::Slt => "slt",
            I::Sle => "sle",
            I::Sgt => "sgt",
            I::Sge => "sge",
        }
    }

    pub(super) fn fcmp(op: trust_ir::inst::FCmpOp) -> &'static str {
        use trust_ir::inst::FCmpOp as F;
        match op {
            F::OEq => "oeq",
            F::ONe => "one",
            F::OLt => "olt",
            F::OLe => "ole",
            F::OGt => "ogt",
            F::OGe => "oge",
            F::UEq => "ueq",
            F::UNe => "une",
            F::ULt => "ult",
            F::ULe => "ule",
            F::UGt => "ugt",
            F::UGe => "uge",
        }
    }

    pub(super) fn cast(op: trust_ir::inst::CastOp) -> R<&'static str> {
        use trust_ir::inst::CastOp as C;
        Ok(match op {
            C::Trunc => "trunc",
            C::ZExt => "zext",
            C::SExt => "sext",
            C::FPTrunc => "fptrunc",
            C::FPExt => "fpext",
            C::FPToUI => "fptoui",
            C::FPToSI => "fptosi",
            C::UIToFP => "uitofp",
            C::SIToFP => "sitofp",
            C::PtrToInt => "ptrtoint",
            C::IntToPtr => "inttoptr",
            C::PtrToPtr => "ptrtoptr",
            C::Bitcast => "bitcast",
            C::Transmute => "transmute",
            C::ReifyFnPointer => "reifyfnpointer",
            // Named, not wildcarded: a cast trust-ir adds fails to compile here.
            other @ (C::FPToSISat | C::FPToUISat) => {
                return Err(format!("no IRCastOp image for {other:?}"))
            }
        })
    }

    /// The `cc` operand of `IRInst.callindirect`: the wire tag of each
    /// convention Clean's text reader names (`CALLING_CONVS` in
    /// `crates/clean-verify/src/ir_mint/emitted.rs`, the five trust-ir printed
    /// before wire v45), the number this has always emitted for it. A v45
    /// convention has no image: nothing in Clean reads one, and trust-ir's own
    /// contract says a consumer that would lower `CUnwind` as C must refuse it.
    /// verifier r11v: this was `c as u32`, which imaged every convention,
    /// present and future, by its discriminant.
    pub(super) fn cc(c: trust_ir::CallingConv) -> R<u32> {
        use trust_ir::CallingConv as K;
        Ok(match c {
            K::C => 0,
            K::Fast => 1,
            K::Cold => 2,
            K::Rust => 3,
            K::Swift => 4,
            // Named, not wildcarded: a convention trust-ir adds fails to compile here.
            other @ (K::CUnwind
            | K::SysV64
            | K::Win64
            | K::Aapcs
            | K::EfiApi
            | K::VectorCall
            | K::RustCold) => return Err(format!("no IR calling-convention image for {other:?}")),
        })
    }
}

mod reference {
    //! A row's decode, twice: as Clean's view images a word through the minted
    //! table, and as trust-ir's reference `Interpreter` decodes the same word
    //! stored into a cell and loaded at the aggregate type. `reference_gate`
    //! refuses every row on which the two differ.
    //!
    //! The Clean half is a TRANSLITERATION of the registered definitions in
    //! `crates/clean-verify/src/spec/core_spec/eval_ir_machine.rs` --
    //! `ir_enc_find` / `ir_enc_matches` (first row keyed by kind and canonical
    //! id), `ir_view_ty` (fuel = the table's length, out of fuel = identity),
    //! `ir_view_word`, `ir_niche_image` (the zero word is `[int_ none]`, any
    //! other `[int_ some, payload]`), `ir_wrap_image` / `ir_spine_with_slot` /
    //! `ir_zst_spine` (the word at slot i, `aggv vnil` in every other slot) --
    //! over the one scalar shape a stored word has, `int_ w`. Clean's `int_`
    //! carries both a tag and a word, so both are [`Img::Word`] here. The
    //! registered text of all eleven definitions is pinned by
    //! `tests::the_model_transliterates_these_exact_clean_definitions`, which
    //! reads that file: a change to any of them fails this crate's suite until
    //! the transliteration is re-read against it (verifier r8, 2026-09-25 --
    //! before that, nothing here read the file).
    //!
    //! The reference half reads trust-ir's value back into the same shape: an
    //! integer is its bits, a pointer with no provenance is its address (the
    //! zero pointer is 0), an aggregate is its fields. Anything else -- a
    //! pointer INTO an allocation, a bool, a float, `Unit`, a fat pointer -- has
    //! no counterpart among the images a word can take, so it is
    //! [`Img::Opaque`] and never equal to a model image.

    use std::fmt;

    use trust_ir::inst::Inst;
    use trust_ir::ty::Ty;
    use trust_ir::value::{BlockId, EnumId, FuncId, StructId, ValueId};
    use trust_ir::{InterpretValue, InterpretValueKind};

    use super::deep::Agg;
    use super::{Row, Shape};

    /// A decoded word, in the shape Clean's view and trust-ir's value share.
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub(crate) enum Img {
        /// `int_ n` (a tag, or the stored word itself).
        Word(u128),
        /// `aggv [..]`.
        Agg(Vec<Img>),
        /// A reference value no Clean image of a word can equal.
        Opaque(String),
    }

    impl Img {
        /// Whether a model image agrees with the reference's: the same word,
        /// or aggregates agreeing field by field. [`Img::Opaque`] agrees with
        /// nothing, itself included. The kinds are matched by name, so an
        /// image kind added here fails to compile until its agreement is
        /// decided (the typed scan's value rule refused `got != *want`, whose
        /// `!=` a new kind would reach as one more value).
        pub(crate) fn agrees(&self, reference: &Img) -> bool {
            match (self, reference) {
                (Img::Word(a), Img::Word(b)) => a == b,
                (Img::Agg(a), Img::Agg(b)) => {
                    a.len() == b.len() && a.iter().zip(b).all(|(x, y)| x.agrees(y))
                }
                (Img::Word(_), Img::Agg(_) | Img::Opaque(_))
                | (Img::Agg(_), Img::Word(_) | Img::Opaque(_))
                | (Img::Opaque(_), Img::Word(_) | Img::Agg(_) | Img::Opaque(_)) => false,
            }
        }
    }

    impl fmt::Display for Img {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Img::Word(w) => write!(f, "{w:#x}"),
                Img::Agg(fields) => {
                    f.write_str("[")?;
                    for (i, x) in fields.iter().enumerate() {
                        if i > 0 {
                            f.write_str(", ")?;
                        }
                        write!(f, "{x}")?;
                    }
                    f.write_str("]")
                }
                Img::Opaque(what) => write!(f, "<{what}>"),
            }
        }
    }

    /// `ir_enc_find`: the FIRST row describing the type imaged `t`. Only
    /// `(enum K)` and `(struct K)` can match (`ir_enc_matches` answers false
    /// at every other `IRTy`), and the key is the kind AND the id.
    fn find<'r>(rows: &'r [Row], t: &str) -> Option<&'r Row> {
        let (head, k) = t.strip_prefix('(')?.strip_suffix(')')?.split_once(' ')?;
        let k: usize = k.parse().ok()?;
        // A row's kind is spelled as the image spells it (`Agg::tag` names
        // every kind), so a head no kind spells matches no row.
        rows.iter().find(|r| {
            let (agg, id) = r.key();
            agg.tag() == head && id == k
        })
    }

    /// `ir_view_ty rows fuel t v`.
    fn view_ty(rows: &[Row], fuel: usize, t: &str, v: Img) -> Img {
        let Some(k) = fuel.checked_sub(1) else {
            return v;
        };
        match find(rows, t) {
            None => v,
            Some(r) => view_word(rows, k, r, v),
        }
    }

    /// `ir_view_word (ir_view_ty rows fuel) r v`.
    fn view_word(rows: &[Row], fuel: usize, r: &Row, v: Img) -> Img {
        let payload = view_ty(rows, fuel, &r.payload, v.clone());
        match (&r.shape, v) {
            (Shape::Niche { none, some }, Img::Word(w)) => {
                if w == 0 {
                    Img::Agg(vec![Img::Word(*none as u128)])
                } else {
                    Img::Agg(vec![Img::Word(*some as u128), payload])
                }
            }
            (Shape::Wrap { slot, fields }, Img::Word(_)) => {
                let zst = || Img::Agg(Vec::new());
                let mut spine: Vec<Img> = (0..*slot).map(|_| zst()).collect();
                spine.push(payload);
                spine.extend((0..fields.saturating_sub(slot + 1)).map(|_| zst()));
                Img::Agg(spine)
            }
            // Shape tolerance: a non-word scalar passes through.
            (Shape::Niche { .. } | Shape::Wrap { .. }, other @ (Img::Agg(_) | Img::Opaque(_))) => {
                other
            }
        }
    }

    /// `ir_load_view rows t v`: the row for `t`, its payload imaged with the
    /// table's own length as fuel; the identity when no row describes `t`.
    pub(crate) fn load_view(rows: &[Row], t: &str, v: Img) -> Img {
        match find(rows, t) {
            None => v,
            Some(r) => view_word(rows, rows.len(), r, v),
        }
    }

    /// The words every row is probed at, at a `bits`-wide word: zero (the
    /// none word), the small values a niche range or a tag would collide
    /// with, both ends of the range and the sign bit. Addresses from 1024 up
    /// are where the interpreter places allocations (`MemoryState.next_addr`),
    /// and a word there would decode as a pointer INTO the probe's own cell,
    /// so none is chosen in that window.
    pub(crate) fn probe_words(bits: u32) -> Vec<u128> {
        let mask = if bits >= 128 {
            u128::MAX
        } else {
            (1u128 << bits) - 1
        };
        let top = 1u128 << (bits.clamp(1, 128) - 1);
        let mut out: Vec<u128> = Vec::new();
        for w in [
            0,
            1,
            2,
            3,
            7,
            8,
            0x55,
            0x80,
            0xff,
            0x100,
            0x3f8,
            0x8000,
            0x0123_4567_89ab_cdef,
            top,
            mask >> 1,
            mask - 7,
            mask,
        ] {
            let w = w & mask;
            if !(1024..1024 + 4096).contains(&w) && !out.contains(&w) {
                out.push(w);
            }
        }
        out
    }

    /// The tables and target a row's aggregate is laid out under.
    pub(crate) struct Probe<'a> {
        pub(crate) enums: &'a [trust_ir::ty::EnumDef],
        pub(crate) structs: &'a [trust_ir::ty::StructDef],
        pub(crate) types: &'a [Ty],
        pub(crate) target: Option<&'a trust_ir::TargetInfo>,
    }

    /// trust-ir's decode of every probe word stored into a cell and loaded at
    /// `agg` raw id `raw`: `alloca T; store <word> w; load T`, using one
    /// parameterized function run by `trust_ir::Interpreter` under the probe's
    /// tables and target. Each word still uses the public execution entry and
    /// its complete module validation; the module has one function to validate. The word is one scalar exactly as wide as T; a T no scalar
    /// fills is refused (a row images ONE word).
    pub(crate) fn reference_images(
        probe: &Probe<'_>,
        agg: Agg,
        raw: u32,
        extra: &[u128],
    ) -> Result<Vec<(u128, Img)>, String> {
        let mut m = trust_ir::Module::new("reference-probe");
        m.enums = probe.enums.to_vec();
        m.structs = probe.structs.to_vec();
        m.types = probe.types.to_vec();
        m.target_info = probe.target.cloned();
        let ty = match agg {
            Agg::Enum => Ty::Enum(EnumId::new(raw)),
            Agg::Struct => Ty::Struct(StructId::new(raw)),
        };
        let shape = m
            .ty_layout_shape(&ty)
            .map_err(|e| format!("trust-ir lays out no {}.{raw}: {e:?}", agg.tag()))?;
        let word_ty = match shape.size_bits {
            8 => Ty::U8,
            16 => Ty::U16,
            32 => Ty::U32,
            64 => Ty::U64,
            128 => Ty::U128,
            bits => {
                return Err(format!(
                    "its image is {bits} bits, which no one scalar word fills"
                ))
            }
        };
        let bits = u32::try_from(shape.size_bits).unwrap_or(128);
        let mut words = probe_words(bits);
        let mask = if bits >= 128 {
            u128::MAX
        } else {
            (1u128 << bits) - 1
        };
        for w in extra {
            let w = w & mask;
            if !(1024..1024 + 4096).contains(&w) && !words.contains(&w) {
                words.push(w);
            }
        }
        let fty = m
            .add_func_type(trust_ir::FuncTy {
                params: vec![word_ty.clone()],
                returns: vec![ty.clone()],
                is_vararg: false,
                abi: None,
            })
            .map_err(|refusal| refusal.to_string())?;
        let mut f = trust_ir::Function::new(FuncId::new(0), "probe", fty, BlockId::new(0));
        let mut b = trust_ir::Block::new(BlockId::new(0));
        b.params.push((ValueId::new(1), word_ty.clone()));
        let node = |inst: Inst, result: Option<u32>| {
            let n = trust_ir::InstrNode::new(inst);
            match result {
                Some(r) => n.with_result(ValueId::new(r)),
                None => n,
            }
        };
        b.body.push(node(
            Inst::Alloca {
                ty: ty.clone(),
                count: None,
                align: None,
            },
            Some(0),
        ));
        b.body.push(node(
            Inst::Store {
                ty: word_ty.clone(),
                ptr: ValueId::new(0),
                value: ValueId::new(1),
                volatile: false,
                // This writes a raw word image into the aggregate cell.
                // A packed aggregate may guarantee only byte alignment,
                // even when its image fills a naturally aligned u64.
                // The following aggregate load retains its own required
                // alignment, established by the aggregate alloca above.
                align: Some(1),
            },
            None,
        ));
        b.body.push(node(
            Inst::Load {
                ty: ty.clone(),
                ptr: ValueId::new(0),
                volatile: false,
                align: None,
            },
            Some(2),
        ));
        b.body.push(node(
            Inst::Return {
                values: vec![ValueId::new(2)],
            },
            None,
        ));
        f.blocks.push(b);
        m.functions.push(f);
        let run = trust_ir::Interpreter::with_module(&m);
        words
            .iter()
            .map(|w| {
                // The word's BITS: the same signed carrier as Constant::Int
                // previously used, narrowed by the reference integer constructor.
                let word = InterpretValue::int(word_ty.clone(), *w as i128)
                    .map_err(|e| format!("at the word {w:#x}: {e:?}"))?;
                let out = run
                    .execute_func(FuncId::new(0), [word])
                    .map_err(|e| format!("at the word {w:#x}: {e:?}"))?;
                match out.returns.as_slice() {
                    [v] => Ok((*w, image(v))),
                    other => Err(format!(
                        "at the word {w:#x} the probe returned {} values",
                        other.len()
                    )),
                }
            })
            .collect()
    }

    /// A reference value in the shape a Clean word image has (module doc).
    pub(crate) fn image(v: &InterpretValue) -> Img {
        match &v.kind {
            InterpretValueKind::Int(i) => Img::Word(i.raw),
            InterpretValueKind::NullPtr => Img::Word(0),
            InterpretValueKind::DanglingPtr(a) => Img::Word(u128::from(*a)),
            InterpretValueKind::Aggregate(fields) => Img::Agg(fields.iter().map(image).collect()),
            InterpretValueKind::Ptr(_) => Img::Opaque("a pointer into an allocation".into()),
            InterpretValueKind::FloatBits(_)
            | InterpretValueKind::Bool(_)
            | InterpretValueKind::Vector(_)
            | InterpretValueKind::Array(_)
            | InterpretValueKind::Sequence(_)
            | InterpretValueKind::Set(_)
            | InterpretValueKind::Record(_)
            | InterpretValueKind::Closure { .. }
            | InterpretValueKind::FatPtr { .. }
            | InterpretValueKind::FnDef(_)
            | InterpretValueKind::PhantomData
            | InterpretValueKind::Unit
            | InterpretValueKind::Frame { .. }
            | InterpretValueKind::PartialBytes(_)
            | InterpretValueKind::Handle { .. }
            // trust-ir v67: a tensor value has no Clean word image.
            | InterpretValueKind::Tensor { .. } => Img::Opaque(format!("{} value", v.ty)),
            // trust-ir v49: an UNWRITTEN aggregate lane is not a value, and no
            // Clean image of a stored word is one, so it can never EQUAL a
            // model image: the row it appears in disagrees rather than passes.
            InterpretValueKind::Uninit => Img::Opaque(format!("unwritten {} lane", v.ty)),
        }
    }
}

mod deep {
    //! A raw aggregate id's DEEP identity inside the artifact that defines it.
    //!
    //! Raw enum / struct ids are indices into ONE artifact's tables, and so are
    //! the ids nested inside a definition: `struct.1 = W { f0: struct.2 }` means
    //! "whatever THIS artifact's `struct.2` is". Comparing two artifacts'
    //! definitions of `struct.1` by their printed form therefore compared
    //! `Struct(StructId(2))` with `Struct(StructId(2))` -- equal -- while
    //! `struct.2` was `one::P` (a `u64`) in one artifact and `two::Q` (two `u8`s)
    //! in the other. Both bodies then projected `(undef (struct 0))`, and the
    //! wrapper row read its payload out of the first artifact's table for both.
    //!
    //! [`Tables::deep`] renders a definition with every nested aggregate id
    //! replaced by THAT id's deep identity, resolved through the SAME artifact's
    //! tables (and every `ty.N` through the same artifact's type table), so two
    //! artifacts agree on a raw id exactly when the whole type reachable from it
    //! agrees, raw id by raw id. Raw ids stay in the rendering on purpose:
    //! interning is keyed by the raw id, so a nested id interned later -- a
    //! payload in `derive_encodings` -- must mean one type in every artifact that
    //! reaches it, not merely a structurally similar one.
    //!
    //! Fail-closed: an artifact-local id this rendering does not resolve -- a
    //! function type, record, closure, predicate or trait-object id, AND an
    //! aggregate or `ty.N` id the artifact's own table does not define --
    //! renders with the ARTIFACT'S label, so no two artifacts can agree on it
    //! and a raw id whose definition contains one is refused when two artifacts
    //! name it. Until verifier r7 (2026-09-24) an UNDEFINED id rendered
    //! `struct.N<undefined>` with no label: two artifacts that both lacked
    //! `struct.2` agreed on it, and a `struct.1` neither defined was interned as
    //! one canonical aggregate.

    use std::fmt::Write as _;

    use trust_ir::ty::{EnumDef, EnumVariant, FieldDef, StructDef, Ty};
    use trust_ir::FatPtrKind;

    /// One artifact's tables, as the comparison reads them.
    pub(crate) struct Tables<'a> {
        /// Printed into every id this rendering does not resolve, so it can never
        /// compare equal to another artifact's.
        pub(crate) label: &'a str,
        pub(crate) enums: &'a [EnumDef],
        pub(crate) structs: &'a [StructDef],
        pub(crate) types: &'a [Ty],
    }

    /// Which raw-id namespace an aggregate id is in.
    #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
    pub(crate) enum Agg {
        Enum,
        Struct,
    }

    impl Agg {
        /// The word both the raw id (`enum.3`) and the Clean image
        /// (`(enum 0)`) spell the namespace with.
        pub(crate) fn tag(self) -> &'static str {
            match self {
                Agg::Enum => "enum",
                Agg::Struct => "struct",
            }
        }
    }

    /// A node on the current resolution path, for cycle detection: `struct.1`
    /// holding a pointer to `struct.1` is a finite type with a cyclic rendering.
    #[derive(Clone, Copy)]
    enum Node {
        Agg(Agg, u32),
        TypeTable(u32),
    }

    impl Node {
        /// Whether this is aggregate `id` of `kind`. The kinds are matched by
        /// name: `kind` is the one the caller resolves (`Agg::Struct` for a
        /// `Ty::Struct`), and a kind added to `Agg` fails to compile here.
        fn is_agg(self, kind: Agg, id: u32) -> bool {
            match self {
                Node::Agg(k, i) => {
                    i == id
                        && match (k, kind) {
                            (Agg::Enum, Agg::Enum) | (Agg::Struct, Agg::Struct) => true,
                            (Agg::Enum, Agg::Struct) | (Agg::Struct, Agg::Enum) => false,
                        }
                }
                Node::TypeTable(_) => false,
            }
        }

        /// Whether this is type-table entry `idx`.
        fn is_table(self, idx: u32) -> bool {
            match self {
                Node::TypeTable(i) => i == idx,
                Node::Agg(..) => false,
            }
        }
    }

    impl Tables<'_> {
        /// The deep identity of aggregate `id` of `kind` in this artifact.
        pub(crate) fn deep(&self, kind: Agg, id: u32) -> String {
            let mut out = String::new();
            self.agg(kind, id, &mut Vec::new(), &mut out);
            out
        }

        fn agg(&self, kind: Agg, id: u32, path: &mut Vec<Node>, out: &mut String) {
            let tag = match kind {
                Agg::Enum => "enum",
                Agg::Struct => "struct",
            };
            if let Some(depth) = path.iter().position(|n| n.is_agg(kind, id)) {
                // A back-reference names the cycle by the depth it closes at, so
                // two artifacts agree on a cyclic type exactly when they close the
                // same cycle at the same place.
                let _ = write!(out, "{tag}.{id}^{depth}");
                return;
            }
            path.push(Node::Agg(kind, id));
            match kind {
                Agg::Struct => match self.structs.iter().find(|d| d.id.0 == id) {
                    None => {
                        let _ = write!(out, "struct.{id}<undefined>@{}", self.label);
                    }
                    // Destructured field by field, with no `..`: a field trust-ir
                    // adds to a definition fails to compile here until someone
                    // decides whether it is part of the type's identity.
                    Some(StructDef {
                        id: _,
                        name,
                        fields,
                        size,
                        align,
                        repr,
                        origin,
                    }) => {
                        // `origin` (trust-ir v58) is the nominal key of the
                        // source entity: part of the identity, so two artifacts
                        // that agree on structure but name different entities
                        // disagree here (fail-closed, as trust-ir's own
                        // cross-module equality splits them).
                        let _ = write!(
                            out,
                            "struct.{id}{{{name:?} size={size:?} align={align:?} repr={repr:?} \
                             origin={origin:?} ["
                        );
                        for FieldDef { name, ty, offset } in fields {
                            let _ = write!(out, "{name:?}@{offset:?}:");
                            self.ty(ty, path, out);
                            out.push(',');
                        }
                        out.push_str("]}");
                    }
                },
                Agg::Enum => match self.enums.iter().find(|d| d.id.0 == id) {
                    None => {
                        let _ = write!(out, "enum.{id}<undefined>@{}", self.label);
                    }
                    Some(EnumDef {
                        id: _,
                        name,
                        variants,
                        discriminants,
                        repr,
                        layout,
                        origin,
                    }) => {
                        let _ = write!(
                            out,
                            "enum.{id}{{{name:?} discriminants={discriminants:?} repr={repr:?} \
                             layout={layout:?} origin={origin:?} ["
                        );
                        for EnumVariant {
                            name,
                            fields,
                            field_names,
                        } in variants
                        {
                            let _ = write!(out, "{name:?}{field_names:?}(");
                            for t in fields {
                                self.ty(t, path, out);
                                out.push(',');
                            }
                            out.push_str("),");
                        }
                        out.push_str("]}");
                    }
                },
            }
            path.pop();
        }

        /// A `ty.N` type-table entry, resolved through THIS artifact's table.
        fn table(&self, idx: u32, path: &mut Vec<Node>, out: &mut String) {
            if let Some(depth) = path.iter().position(|n| n.is_table(idx)) {
                let _ = write!(out, "ty.{idx}^{depth}");
                return;
            }
            match self.types.get(idx as usize) {
                None => {
                    let _ = write!(out, "ty.{idx}<undefined>@{}", self.label);
                }
                Some(t) => {
                    path.push(Node::TypeTable(idx));
                    self.ty(t, path, out);
                    path.pop();
                }
            }
        }

        /// An id local to this artifact that this rendering does not resolve.
        fn local(&self, what: &Ty, out: &mut String) {
            let _ = write!(out, "{what:?}@{}", self.label);
        }

        fn ty(&self, t: &Ty, path: &mut Vec<Node>, out: &mut String) {
            let wrap =
                |this: &Self, head: &str, inner: &Ty, path: &mut Vec<Node>, out: &mut String| {
                    out.push_str(head);
                    out.push('(');
                    this.ty(inner, path, out);
                    out.push(')');
                };
            match t {
                Ty::Ext(e) => e.unreachable(),
                Ty::Struct(id) => self.agg(Agg::Struct, id.0, path, out),
                Ty::Enum(id) => self.agg(Agg::Enum, id.0, path, out),
                Ty::Ref(inner) => wrap(self, "ref", inner, path, out),
                Ty::RefMut(inner) => wrap(self, "refmut", inner, path, out),
                Ty::PtrConst(inner) => wrap(self, "ptrconst", inner, path, out),
                Ty::PtrMut(inner) => wrap(self, "ptrmut", inner, path, out),
                Ty::Rc(inner) => wrap(self, "rc", inner, path, out),
                Ty::Vector(inner, lanes) => {
                    let _ = write!(out, "vector{lanes}");
                    wrap(self, "", inner, path, out);
                }
                Ty::Tuple(es) => {
                    out.push_str("tuple(");
                    for e in es {
                        self.ty(e, path, out);
                        out.push(',');
                    }
                    out.push(')');
                }
                Ty::Array(elem, len) => {
                    out.push('[');
                    self.table(elem.0, path, out);
                    let _ = write!(out, " x {len}]");
                }
                Ty::Set(elem, repr) => {
                    let _ = write!(out, "set{repr:?}(");
                    self.table(elem.0, path, out);
                    out.push(')');
                }
                Ty::Sequence(elem) => {
                    out.push_str("seq(");
                    self.table(elem.0, path, out);
                    out.push(')');
                }
                Ty::FatPtr(FatPtrKind::Slice(elem)) => {
                    out.push_str("fatptr<slice>(");
                    self.table(elem.0, path, out);
                    out.push(')');
                }
                Ty::FatPtr(
                    FatPtrKind::Str | FatPtrKind::ContainerLen | FatPtrKind::ContainerVtable,
                ) => {
                    let _ = write!(out, "{t:?}");
                }
                // `trait_id`, a predicate, a function type, a record and a
                // closure type are all indices into tables this rendering does
                // not read: unresolved, so labelled with the artifact.
                Ty::FatPtr(FatPtrKind::TraitObject { trait_id: _ })
                | Ty::Refine(..)
                | Ty::Func(_)
                | Ty::Record(_)
                | Ty::Closure(_) => self.local(t, out),
                // Carry no artifact-local id: a scalar, or a NOMINAL type whose
                // identity is its printed name.
                Ty::I8
                | Ty::I16
                | Ty::I32
                | Ty::I64
                | Ty::I128
                | Ty::U8
                | Ty::U16
                | Ty::U32
                | Ty::U64
                | Ty::U128
                | Ty::Isize
                | Ty::Usize
                | Ty::Char
                | Ty::Error
                | Ty::F16
                | Ty::F32
                | Ty::F64
                | Ty::Bool
                | Ty::Ptr
                | Ty::Unit
                | Ty::Never
                | Ty::Dialect(_)
                | Ty::Tensor(..)
                | Ty::Storage(_)
                | Ty::Handle(_) => {
                    let _ = write!(out, "{t:?}");
                }
            }
        }
    }
}

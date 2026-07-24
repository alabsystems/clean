// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the `.vo` decoding stack.
//!
//! Two layers:
//! 1. Marshal-format unit tests over hand-crafted byte streams (exercising
//!    the exact `intern.c` semantics: back-references, atom/int
//!    non-registration, iterative fill).
//! 2. Real-file vertical-slice tests over the local Coq 8.20 stdlib
//!    (`~/.opam/mathverse-serapi/lib/coq/theories/Init/*.vo`) and the
//!    SerAPI corpus dump (`data/corpora/coq-sexp/stdlib/`). These skip
//!    with a message when the assets are not present, so environments
//!    without the toolchain stay green without `#[ignore]`.

use std::path::PathBuf;

use super::constr_decode::ConstrDecoder;
use super::constr_sexp::constr_sexp;
use super::library;
use super::marshal_parser::{parse_marshal, MObject, MValue, MarshalError};
use super::vo_parser::{parse_vo_file, VoDeclKind, VoObjFile};

// ---------------------------------------------------------------------------
// Marshal unit tests (hand-crafted streams)
// ---------------------------------------------------------------------------

/// Wrap a payload in a small-format marshal header.
fn with_header(payload: &[u8], num_objects: u32) -> Vec<u8> {
    let mut out = Vec::with_capacity(20 + payload.len());
    out.extend_from_slice(&0x8495_A6BEu32.to_be_bytes());
    out.extend_from_slice(&(payload.len() as u32).to_be_bytes());
    out.extend_from_slice(&num_objects.to_be_bytes());
    out.extend_from_slice(&0u32.to_be_bytes());
    out.extend_from_slice(&0u32.to_be_bytes());
    out.extend_from_slice(payload);
    out
}

#[test]
fn test_marshal_invalid_magic_rejected() {
    let mut data = with_header(&[0x40], 0);
    data[0] = 0x00;
    let err = parse_marshal(&data).expect_err("bad magic must fail");
    assert!(matches!(err, MarshalError::InvalidMagic { .. }));
}

#[test]
fn test_marshal_truncated_header_is_eof() {
    let data = [0x84, 0x95, 0xA6, 0xBE, 0x00, 0x00, 0x00, 0x01];
    let err = parse_marshal(&data).expect_err("truncated header must fail");
    assert!(matches!(err, MarshalError::UnexpectedEof { .. }));
}

#[test]
fn test_marshal_small_int_decodes_value() {
    let dag = parse_marshal(&with_header(&[0x45], 0)).expect("should parse small int");
    assert_eq!(dag.root, MValue::Int(5));
    assert!(dag.objects.is_empty(), "ints must not be registered");
}

#[test]
fn test_marshal_int8_negative_sign_extends() {
    let dag = parse_marshal(&with_header(&[0x00, 0xFF], 0)).expect("should parse int8");
    assert_eq!(dag.root, MValue::Int(-1));
}

#[test]
fn test_marshal_int32_roundtrip() {
    let mut payload = vec![0x02];
    payload.extend_from_slice(&(-123_456i32).to_be_bytes());
    let dag = parse_marshal(&with_header(&payload, 0)).expect("should parse int32");
    assert_eq!(dag.root, MValue::Int(-123_456));
}

#[test]
fn test_marshal_small_string_registers_object() {
    let dag = parse_marshal(&with_header(&[0x22, b'a', b'b'], 1)).expect("should parse string");
    assert_eq!(dag.root, MValue::Ref(0));
    assert_eq!(dag.objects[0], MObject::Str(b"ab".to_vec()));
}

#[test]
fn test_marshal_nested_blocks_fill_iteratively() {
    // Block(0, [Int 1, Block(1, ["x"])])
    let dag = parse_marshal(&with_header(&[0xA0, 0x41, 0x91, 0x21, b'x'], 3))
        .expect("should parse nested blocks");
    let (tag, fields) = dag.block(dag.root).expect("root should be a block");
    assert_eq!(tag, 0);
    assert_eq!(fields[0], MValue::Int(1));
    let (tag1, inner) = dag.block(fields[1]).expect("field 1 should be a block");
    assert_eq!(tag1, 1);
    assert_eq!(dag.string_lossy(inner[0]).as_deref(), Some("x"));
}

#[test]
fn test_marshal_shared_backref_resolves_relative() {
    // Block(0, [s, s]) where the second s is CODE_SHARED8 with back-ref 1.
    let dag = parse_marshal(&with_header(&[0xA0, 0x21, b'x', 0x04, 0x01], 2))
        .expect("should parse shared back-reference");
    let (_, fields) = dag.block(dag.root).expect("root should be a block");
    assert_eq!(fields[0], fields[1], "both fields must alias one object");
    assert_eq!(dag.string_lossy(fields[0]).as_deref(), Some("x"));
}

#[test]
fn test_marshal_atoms_and_ints_not_in_sharing_table() {
    // Block(0, ["a", Atom0, Int 7, shared(1)]) — the back-reference must
    // skip the atom and the int and land on "a".
    let payload = [0xC0, 0x21, b'a', 0x80, 0x47, 0x04, 0x01];
    let dag = parse_marshal(&with_header(&payload, 2)).expect("should parse");
    let (_, fields) = dag.block(dag.root).expect("root should be a block");
    assert_eq!(fields[1], MValue::Atom(0));
    assert_eq!(fields[2], MValue::Int(7));
    assert_eq!(fields[3], fields[0], "back-ref must skip atoms/ints");
    assert_eq!(dag.string_lossy(fields[3]).as_deref(), Some("a"));
}

#[test]
fn test_marshal_shared_out_of_range_is_error() {
    let payload = [0xA0, 0x21, b'x', 0x04, 0x05];
    let err = parse_marshal(&with_header(&payload, 2)).expect_err("back-ref 5 of 2 must fail");
    assert!(matches!(err, MarshalError::SharedOutOfRange { .. }));
}

#[test]
fn test_marshal_deep_list_does_not_overflow_stack() {
    // A 100_000-element OCaml list nests 100_000 blocks deep.
    let n = 100_000usize;
    let mut payload = Vec::with_capacity(2 * n + 1);
    for _ in 0..n {
        payload.push(0xA0); // cons cell
        payload.push(0x41); // head = 1
    }
    payload.push(0x40); // nil
    let dag = parse_marshal(&with_header(&payload, n as u32)).expect("should parse deep list");
    let items = dag.list(dag.root).expect("should view as list");
    assert_eq!(items.len(), n);
}

#[test]
fn test_marshal_list_and_opt_views() {
    // [1; 2] = Block(0,[1, Block(0,[2, 0])])
    let dag =
        parse_marshal(&with_header(&[0xA0, 0x41, 0xA0, 0x42, 0x40], 2)).expect("should parse");
    let items = dag.list(dag.root).expect("should view as list");
    assert_eq!(items, vec![MValue::Int(1), MValue::Int(2)]);

    // Some 3 = Block(0, [3])
    let dag = parse_marshal(&with_header(&[0x90, 0x43], 1)).expect("should parse");
    assert_eq!(dag.opt(dag.root), Some(Some(MValue::Int(3))));
    // None = Int 0
    let dag = parse_marshal(&with_header(&[0x40], 0)).expect("should parse");
    assert_eq!(dag.opt(dag.root), Some(None));
}

#[test]
fn test_marshal_custom_int64_block() {
    // CODE_CUSTOM_FIXED "_j" + 8 bytes.
    let mut payload = vec![0x19, b'_', b'j', 0x00];
    payload.extend_from_slice(&42i64.to_be_bytes());
    let dag = parse_marshal(&with_header(&payload, 1)).expect("should parse custom _j");
    assert_eq!(dag.custom_int64(dag.root), Some(42));
}

// ---------------------------------------------------------------------------
// Real-file vertical slice (gated on local assets)
// ---------------------------------------------------------------------------

fn init_theories_dir() -> Option<PathBuf> {
    let home = std::env::var_os("HOME")?;
    let dir = PathBuf::from(home).join(".opam/mathverse-serapi/lib/coq/theories/Init");
    dir.is_dir().then_some(dir)
}

fn corpus_sexp(module: &str) -> Option<PathBuf> {
    let p = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../data/corpora/coq-sexp/stdlib")
        .join(format!("{module}.sexp"));
    p.is_file().then_some(p)
}

macro_rules! require_asset {
    ($opt:expr, $what:expr) => {
        match $opt {
            Some(v) => v,
            None => {
                eprintln!("SKIP: {} not present on this machine", $what);
                return;
            }
        }
    };
}

#[test]
fn test_real_init_vo_all_segments_marshal_decode() {
    let dir = require_asset!(init_theories_dir(), "Coq 8.20 Init theories");
    let mut files = 0usize;
    let mut segments = 0usize;
    for entry in std::fs::read_dir(&dir).expect("should list Init dir") {
        let path = entry.expect("dir entry").path();
        if path.extension().and_then(|e| e.to_str()) != Some("vo") {
            continue;
        }
        let data = std::fs::read(&path).expect("should read .vo");
        let obj = VoObjFile::parse(&data)
            .unwrap_or_else(|e| panic!("should parse container {}: {e}", path.display()));
        assert_eq!(obj.version, 82000, "Coq 8.20 vo_version");
        for seg in &obj.segments {
            // Every segment of every Init .vo must marshal-decode fully.
            let dag = obj
                .read_segment(&seg.name)
                .unwrap_or_else(|e| panic!("segment {} of {}: {e}", seg.name, path.display()));
            // The value stream must end exactly at the segment boundary
            // (the trailing 16-byte MD5 is outside `len`).
            assert_eq!(
                dag.bytes_consumed as u64,
                seg.len,
                "segment {} of {} consumed wrong length",
                seg.name,
                path.display()
            );
            segments += 1;
        }
        files += 1;
    }
    assert!(files >= 10, "expected >= 10 Init .vo files, got {files}");
    assert!(segments >= 4 * files, "each .vo should have >= 4 segments");
}

#[test]
fn test_real_logic_vo_declaration_census() {
    let dir = require_asset!(init_theories_dir(), "Coq 8.20 Init theories");
    let data = std::fs::read(dir.join("Logic.vo")).expect("should read Logic.vo");
    let vo = parse_vo_file(&data).expect("should parse Logic.vo");
    assert_eq!(vo.library_name.as_deref(), Some("Coq.Init.Logic"));
    assert!(
        vo.dependencies.iter().any(|d| d == "Coq.Init.Ltac"),
        "Logic.vo should depend on Coq.Init.Ltac, got {:?}",
        vo.dependencies
    );

    // eq_sym ends with `Defined.` in Init/Logic.v — it is TRANSPARENT.
    let eq_sym = vo
        .declarations
        .iter()
        .find(|d| d.name == "Coq.Init.Logic.eq_sym")
        .expect("eq_sym should be declared");
    assert_eq!(eq_sym.kind, VoDeclKind::Constant);
    assert!(!eq_sym.is_opaque, "eq_sym is Defined (transparent)");

    // and_comm ends with `Qed.` — the genuine opaque exemplar.
    let and_comm = vo
        .declarations
        .iter()
        .find(|d| d.name == "Coq.Init.Logic.and_comm")
        .expect("and_comm should be declared");
    assert!(and_comm.is_opaque, "and_comm is a Qed theorem");

    let eq_ind = vo
        .declarations
        .iter()
        .find(|d| d.name == "Coq.Init.Logic.eq")
        .expect("eq inductive should be declared");
    assert_eq!(eq_ind.kind, VoDeclKind::Inductive);

    let constants = vo
        .declarations
        .iter()
        .filter(|d| d.kind == VoDeclKind::Constant)
        .count();
    assert!(constants > 100, "Logic has >100 constants, got {constants}");
}

#[test]
fn test_real_logic_inductive_ctor_names() {
    let dir = require_asset!(init_theories_dir(), "Coq 8.20 Init theories");
    let data = std::fs::read(dir.join("Logic.vo")).expect("should read Logic.vo");
    let obj = VoObjFile::parse(&data).expect("should parse container");
    let dag = obj.read_segment("library").expect("library segment");
    let lib = library::read_library(&dag, "Coq.Init.Logic").expect("library walk");
    let eq = lib
        .inductives
        .iter()
        .find(|i| i.label == "eq")
        .expect("eq inductive block");
    assert_eq!(eq.type_names, vec!["eq"]);
    assert_eq!(eq.ctor_names, vec![vec!["eq_refl".to_string()]]);
    let or = lib
        .inductives
        .iter()
        .find(|i| i.label == "or")
        .expect("or inductive block");
    assert_eq!(
        or.ctor_names,
        vec![vec!["or_introl".to_string(), "or_intror".to_string()]]
    );
}

// -- structural agreement with the SerAPI dump ------------------------------

/// Minimal sexp tree for structural comparison.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Sx {
    Atom(String),
    List(Vec<Sx>),
}

fn parse_sx(input: &str) -> Option<Sx> {
    let mut chars = input.char_indices().peekable();
    parse_sx_at(input, &mut chars)
}

fn parse_sx_at(src: &str, it: &mut std::iter::Peekable<std::str::CharIndices<'_>>) -> Option<Sx> {
    while let Some(&(_, c)) = it.peek() {
        if c.is_whitespace() {
            it.next();
        } else {
            break;
        }
    }
    let &(start, c) = it.peek()?;
    if c == '(' {
        it.next();
        let mut items = Vec::new();
        loop {
            while let Some(&(_, c)) = it.peek() {
                if c.is_whitespace() {
                    it.next();
                } else {
                    break;
                }
            }
            match it.peek() {
                Some(&(_, ')')) => {
                    it.next();
                    return Some(Sx::List(items));
                }
                Some(_) => items.push(parse_sx_at(src, it)?),
                None => return None,
            }
        }
    } else if c == '"' {
        it.next();
        let mut s = String::new();
        for (_, c) in it.by_ref() {
            if c == '"' {
                break;
            }
            s.push(c);
        }
        Some(Sx::Atom(format!("\"{s}\"")))
    } else {
        let mut end = start;
        while let Some(&(i, c)) = it.peek() {
            if c.is_whitespace() || c == '(' || c == ')' {
                break;
            }
            end = i + c.len_utf8();
            it.next();
        }
        Some(Sx::Atom(src[start..end].to_string()))
    }
}

/// Normalize universe payloads: serlib 8.20 pierces `Univ.Level.UGlobal.t`
/// with a stale 2-field layout, so the number it prints inside `Level`
/// globals is a string *pointer* (nondeterministic garbage). `(Type
/// <payload>)` payloads are therefore erased on both sides before
/// comparison. Everything else — binder names, relevances, de Bruijn
/// indices, kernel names, case info — must agree exactly.
fn normalize(sx: &Sx) -> Sx {
    match sx {
        Sx::Atom(a) => Sx::Atom(a.clone()),
        Sx::List(items) => {
            if let [Sx::Atom(head), _payload] = items.as_slice() {
                if head == "Type" {
                    return Sx::List(vec![
                        Sx::Atom("Type".to_string()),
                        Sx::Atom("_".to_string()),
                    ]);
                }
            }
            Sx::List(items.iter().map(normalize).collect())
        }
    }
}

fn render(sx: &Sx, out: &mut String) {
    match sx {
        Sx::Atom(a) => out.push_str(a),
        Sx::List(items) => {
            out.push('(');
            for (i, item) in items.iter().enumerate() {
                if i > 0 {
                    out.push(' ');
                }
                render(item, out);
            }
            out.push(')');
        }
    }
}

fn assert_sx_agree(mine: &Sx, dump: &Sx, what: &str) {
    let (a, b) = (normalize(mine), normalize(dump));
    if a != b {
        let (mut sa, mut sb) = (String::new(), String::new());
        render(&a, &mut sa);
        render(&b, &mut sb);
        let split = sa
            .bytes()
            .zip(sb.bytes())
            .position(|(x, y)| x != y)
            .unwrap_or(sa.len().min(sb.len()));
        let lo = split.saturating_sub(120);
        panic!(
            "{what}: structural disagreement at byte {split}\n vo:   ...{}\n dump: ...{}",
            &sa[lo..(split + 120).min(sa.len())],
            &sb[lo..(split + 120).min(sb.len())],
        );
    }
}

/// Find the `(CoqConstant <name> <type> <body>)` entry in a corpus dump.
fn corpus_constant(path: &std::path::Path, name: &str) -> Option<(Sx, Option<Sx>)> {
    let text = std::fs::read_to_string(path).ok()?;
    let prefix = format!("(CoqConstant {name} ");
    let line = text.lines().find(|l| l.starts_with(&prefix))?;
    match parse_sx(line)? {
        Sx::List(items) if items.len() >= 3 => {
            let typ = items[2].clone();
            let body = items.get(3).cloned();
            Some((typ, body))
        }
        _ => None,
    }
}

#[test]
fn test_real_qed_opaque_type_and_proof_agree_with_serapi_dump() {
    // and_comm ends with `Qed.` at TOP LEVEL (outside any Section) — a genuine
    // OpaqueDef whose
    // proof body lives behind the opaque-table indirection. (eq_sym is
    // `Defined.`/transparent, covered by the transparent-body test below.)
    let dir = require_asset!(init_theories_dir(), "Coq 8.20 Init theories");
    let corpus = require_asset!(
        corpus_sexp("Coq.Init.Logic"),
        "SerAPI corpus dump for Coq.Init.Logic"
    );

    let data = std::fs::read(dir.join("Logic.vo")).expect("should read Logic.vo");
    let obj = VoObjFile::parse(&data).expect("should parse container");
    let lib_dag = obj.read_segment("library").expect("library segment");
    let lib = library::read_library(&lib_dag, "Coq.Init.Logic").expect("library walk");
    let entry = lib
        .constants
        .iter()
        .find(|c| c.label == "and_comm")
        .expect("and_comm constant in structure");
    assert_eq!(entry.def, library::ConstantDefKind::OpaqueDef);

    let (dump_typ, dump_body) =
        corpus_constant(&corpus, "Coq.Init.Logic.and_comm").expect("and_comm in corpus dump");

    // Type: decoded from the library segment.
    let mut dec = ConstrDecoder::new(&lib_dag);
    let typ = dec
        .constr(entry.type_val)
        .expect("should decode and_comm type");
    let mine = parse_sx(&constr_sexp(&typ)).expect("renderer output should parse");
    assert_sx_agree(&mine, &dump_typ, "and_comm type");

    // Proof body: through the opaque-table indirection.
    let idx = entry.opaque_index.expect("opaque index");
    let opq_dag = obj.read_segment("opaques").expect("opaques segment");
    let proof_val = library::read_opaque_proof(&opq_dag, idx)
        .expect("opaque table lookup")
        .expect("and_comm proof should be present");
    let mut dec = ConstrDecoder::new(&opq_dag);
    let proof = dec.constr(proof_val).expect("should decode and_comm proof");
    let mine_body = parse_sx(&constr_sexp(&proof)).expect("renderer output should parse");
    let dump_body = dump_body.expect("dump should carry and_comm body");
    assert_sx_agree(&mine_body, &dump_body, "and_comm opaque proof body");
}

#[test]
fn test_real_vo_export_route_imports_end_to_end() {
    // The `.vo` import ROUTE: decode Logic.vo's constants straight to
    // importer-form `(CoqConstant …)` sexp and feed them to the SAME
    // `CoqImporter::import_sexp` the SerAPI dump uses. Proves the reconstructor
    // is wired as a real import path (no live `sertop`), end to end.
    use super::export::export_vo_constants;
    use crate::coq::alpha::CoqImporter;
    use crate::shard::ShardWriter;

    let dir = require_asset!(init_theories_dir(), "Coq 8.20 Init theories");
    let data = std::fs::read(dir.join("Logic.vo")).expect("should read Logic.vo");

    let export = export_vo_constants(&data, "Coq.Init.Logic").expect("vo export should walk");
    assert!(
        export.exported > 0,
        "expected at least one constant exported from Logic.vo, got 0 (skipped: {:?})",
        export.skipped
    );

    // The exported sexp must parse and import through the standard path.
    let mut w = ShardWriter::new();
    let stats = CoqImporter
        .import_sexp(&export.sexp, &mut w)
        .expect("vo-exported sexp should import");
    eprintln!(
        "[vo-route] Logic.vo: exported={} skipped={} | import total={} translated={} \
         axiomatized={} skipped={}",
        export.exported,
        export.skipped.len(),
        stats.total,
        stats.translated,
        stats.axiomatized,
        stats.skipped
    );
    assert_eq!(
        stats.total as usize, export.exported,
        "every exported constant should reach the importer as a top-level form"
    );
    assert!(
        stats.translated + stats.axiomatized > 0,
        "vo-exported constants should translate or axiomatize, not all skip \
         (translated={}, axiomatized={}, skipped={})",
        stats.translated,
        stats.axiomatized,
        stats.skipped
    );
}

#[test]
fn test_real_transparent_body_agrees_with_serapi_dump() {
    // eq_ind_r is a transparent constant: its body lives inline in the
    // library segment (ConstantDefKind::Def).
    let dir = require_asset!(init_theories_dir(), "Coq 8.20 Init theories");
    let corpus = require_asset!(
        corpus_sexp("Coq.Init.Logic"),
        "SerAPI corpus dump for Coq.Init.Logic"
    );

    let data = std::fs::read(dir.join("Logic.vo")).expect("should read Logic.vo");
    let obj = VoObjFile::parse(&data).expect("should parse container");
    let lib_dag = obj.read_segment("library").expect("library segment");
    let lib = library::read_library(&lib_dag, "Coq.Init.Logic").expect("library walk");
    let entry = lib
        .constants
        .iter()
        .find(|c| c.label == "eq_ind_r")
        .expect("eq_ind_r constant in structure");
    assert_eq!(entry.def, library::ConstantDefKind::Def);

    let (dump_typ, dump_body) =
        corpus_constant(&corpus, "Coq.Init.Logic.eq_ind_r").expect("eq_ind_r in corpus dump");

    let mut dec = ConstrDecoder::new(&lib_dag);
    let typ = dec.constr(entry.type_val).expect("should decode type");
    let mine = parse_sx(&constr_sexp(&typ)).expect("renderer output should parse");
    assert_sx_agree(&mine, &dump_typ, "eq_ind_r type");

    let body_val = entry.body_val.expect("transparent body");
    let body = dec.constr(body_val).expect("should decode body");
    let mine_body = parse_sx(&constr_sexp(&body)).expect("renderer output should parse");
    let dump_body = dump_body.expect("dump should carry eq_ind_r body");
    assert_sx_agree(&mine_body, &dump_body, "eq_ind_r transparent body");
}

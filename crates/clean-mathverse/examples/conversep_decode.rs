// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! One-off decode helper (NOT a production path): for a set of serials, seek-read
//! the FULL corpus line via the `.idx` sidecar, parse the `IsaProvenTheorem`, and
//! print a compact decode of the STATEMENT shape (premise heads, conclusion head,
//! where a `conversep`/`converse`/`rel_*conversep`/`*_flip`/`vimage2p`/`Grp` const
//! sits) plus the PROOF root node kind and its OfClass-leaf census. Pure reads
//! (idx seek); no verify lock, no kernel replay.
//!
//! Usage:
//!   cargo run -q --example conversep_decode -p clean-mathverse -- \
//!     <corpus.jsonl> <serials.txt>

use std::io::{Read as _, Seek as _};
use std::path::Path;

use clean_mathverse::hol::isabelle_pure::{
    parse_proven_theorem, IsaProof, IsaProvenTheorem, IsaTerm,
};

const CAP: usize = 64 * 1024 * 1024;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 3 {
        eprintln!("usage: conversep_decode <corpus.jsonl> <serials.txt>");
        std::process::exit(2);
    }
    let corpus = Path::new(&args[1]);
    let serials: Vec<i64> = std::fs::read_to_string(&args[2])
        .expect("read serials")
        .lines()
        .filter_map(|l| l.trim().parse::<i64>().ok())
        .collect();

    let idx_path = clean_mathverse::hol::isabelle_index::index_path(corpus);
    let index = clean_mathverse::hol::isabelle_index::load_index(&idx_path).expect("load .idx");
    let mut f = std::fs::File::open(corpus).expect("open corpus");

    for s in serials {
        let Some(e) = index.get(s) else {
            println!("s{s}\tMISSING-from-corpus");
            continue;
        };
        f.seek(std::io::SeekFrom::Start(e.offset)).expect("seek");
        // In raw-fixture mode read the FULL entry (verbatim line); otherwise bound
        // the read (we only parse `prop`+`proof`, which sit within the prefix).
        let raw_mode = std::env::var("CONVERSEP_RAW").is_ok();
        let cap = if raw_mode {
            e.len as usize
        } else {
            (e.len as usize).min(CAP)
        };
        let mut buf = vec![0u8; cap];
        let mut total = 0;
        while total < buf.len() {
            match f.read(&mut buf[total..]) {
                Ok(0) => break,
                Ok(k) => total += k,
                Err(_) => break,
            }
        }
        buf.truncate(total);
        let line = String::from_utf8_lossy(&buf);
        if let Ok(dir) = std::env::var("CONVERSEP_RAW") {
            // Emit the VERBATIM trimmed corpus line to `<dir>/s<serial>.jsonl`
            // (exact-corpus fixture extraction).
            let trimmed = line.trim_end_matches(['\n', '\r']);
            let path = std::path::Path::new(&dir).join(format!("s{s}.jsonl"));
            std::fs::write(&path, format!("{trimmed}\n")).expect("write raw fixture");
            eprintln!("RAW s{s} -> {} ({} bytes)", path.display(), trimmed.len());
            continue;
        }
        let thm = match parse_proven_theorem(&line) {
            Ok(t) => t,
            Err(err) => {
                println!("s{s}\tPARSE-ERR {err}");
                continue;
            }
        };
        decode(&thm);
        if std::env::var("CONVERSEP_DEEP").is_ok() {
            let (_, concl) = premises_and_concl(&thm.prop);
            println!("    CONCL-TREE:\n{}", sexpr(concl, 6, 3));
            println!("    PROOF-TREE:\n{}", proof_sexpr(&thm.proof, 8, 3));
        }
    }
}

/// Depth-bounded s-expression of a term (for eyeballing conversep positions).
fn sexpr(t: &IsaTerm, depth: usize, indent: usize) -> String {
    let pad = " ".repeat(indent);
    if depth == 0 {
        return format!("{pad}…");
    }
    match t {
        IsaTerm::Const { n, .. } => format!("{pad}Const {n}"),
        IsaTerm::Free { n, .. } => format!("{pad}Free {n}"),
        IsaTerm::Var { n, i, .. } => format!("{pad}Var {n}.{i}"),
        IsaTerm::Bound { i } => format!("{pad}Bound {i}"),
        IsaTerm::Abs { b, .. } => format!("{pad}Abs\n{}", sexpr(b, depth - 1, indent + 2)),
        IsaTerm::App { f, a } => format!(
            "{pad}App\n{}\n{}",
            sexpr(f, depth - 1, indent + 2),
            sexpr(a, depth - 1, indent + 2)
        ),
    }
}

/// Depth-bounded s-expression of a proof (root spine + leaf kinds).
fn proof_sexpr(p: &IsaProof, depth: usize, indent: usize) -> String {
    let pad = " ".repeat(indent);
    if depth == 0 {
        return format!("{pad}…");
    }
    match p {
        IsaProof::Thm { id, thy, .. } => format!("{pad}Thm s{id} {thy}"),
        IsaProof::Axm { name, .. } => format!("{pad}Axm {name}"),
        IsaProof::AbsP { b, h, .. } => {
            let hyp = h.as_ref().map(fmt_term).unwrap_or_else(|| "?".to_string());
            format!(
                "{pad}AbsP [hyp={hyp}]\n{}",
                proof_sexpr(b, depth - 1, indent + 2)
            )
        }
        IsaProof::Abst { b, .. } => format!("{pad}Abst\n{}", proof_sexpr(b, depth - 1, indent + 2)),
        IsaProof::AppP { f, a } => format!(
            "{pad}AppP\n{}\n{}",
            proof_sexpr(f, depth - 1, indent + 2),
            proof_sexpr(a, depth - 1, indent + 2)
        ),
        IsaProof::AppT { f, .. } => format!("{pad}AppT\n{}", proof_sexpr(f, depth - 1, indent + 2)),
        IsaProof::Hyp { p } => format!("{pad}Hyp {}", fmt_term(p)),
        IsaProof::Bound { i } => format!("{pad}PBound {i}"),
        IsaProof::OfClass { c, .. } => format!("{pad}OfClass {c}"),
        IsaProof::Oracle { .. } => format!("{pad}Oracle"),
        _ => format!("{pad}?"),
    }
}

fn decode(thm: &IsaProvenTheorem) {
    let (prems, concl) = premises_and_concl(&thm.prop);
    let prem_s: Vec<String> = prems.iter().map(|p| fmt_term(p)).collect();
    let concl_s = fmt_term(concl);
    let is_eq = is_eq_head(concl);
    let root = proof_root_kind(&thm.proof);
    let (ofclass_n, ofclass_classes) = count_ofclass(&thm.proof);
    let conv_in_concl = walk_has_converse(concl);
    let conv_in_prems = prems.iter().any(|p| walk_has_converse(p));
    println!(
        "s{}\tname={}\troot={}\tconcl_is_eq={}\tconv@concl={}\tconv@prem={}\tofclass={}({})\n    PREM: {}\n    CONCL: {}",
        thm.serial,
        if thm.name.is_empty() { "-" } else { &thm.name },
        root,
        is_eq,
        conv_in_concl,
        conv_in_prems,
        ofclass_n,
        ofclass_classes.join(","),
        prem_s.join("  |  "),
        concl_s,
    );
}

fn proof_root_kind(p: &IsaProof) -> &'static str {
    match p {
        IsaProof::Thm { .. } => "Thm",
        IsaProof::Axm { .. } => "Axm",
        IsaProof::AbsP { .. } => "AbsP",
        IsaProof::Abst { .. } => "Abst",
        IsaProof::AppP { .. } => "AppP",
        IsaProof::AppT { .. } => "AppT",
        IsaProof::Hyp { .. } => "Hyp",
        IsaProof::Bound { .. } => "Bound",
        IsaProof::OfClass { .. } => "OfClass",
        IsaProof::Oracle { .. } => "Oracle",
        _ => "?",
    }
}

fn count_ofclass(p: &IsaProof) -> (usize, Vec<String>) {
    let mut n = 0;
    let mut classes = std::collections::BTreeSet::new();
    fn walk(p: &IsaProof, n: &mut usize, cs: &mut std::collections::BTreeSet<String>) {
        match p {
            IsaProof::OfClass { c, .. } => {
                *n += 1;
                cs.insert(c.rsplit('.').next().unwrap_or(c).to_string());
            }
            IsaProof::AbsP { b, .. } | IsaProof::Abst { b, .. } => walk(b, n, cs),
            IsaProof::AppP { f, a } => {
                walk(f, n, cs);
                walk(a, n, cs);
            }
            IsaProof::AppT { f, .. } => walk(f, n, cs),
            _ => {}
        }
    }
    walk(p, &mut n, &mut classes);
    (n, classes.into_iter().collect())
}

fn is_converse_head(name: &str) -> bool {
    let tail = name.rsplit('.').next().unwrap_or(name);
    tail == "conversep"
        || tail == "converse"
        || tail == "transpose"
        || tail.ends_with("conversep")
        || tail.ends_with("_flip")
        || tail.ends_with("vimage2p")
        || tail == "Grp"
        || tail == "vimage2p"
        || tail == "relcompp"
        || tail.ends_with("rel_compp_Grp")
}

fn walk_has_converse(t: &IsaTerm) -> bool {
    let mut found = false;
    fn go(t: &IsaTerm, f: &mut bool) {
        match t {
            IsaTerm::Const { n, .. } if is_converse_head(n) => *f = true,
            IsaTerm::App { f: g, a } => {
                go(g, f);
                go(a, f);
            }
            IsaTerm::Abs { b, .. } => go(b, f),
            _ => {}
        }
    }
    go(t, &mut found);
    found
}

fn is_eq_head(t: &IsaTerm) -> bool {
    let (h, args) = app_spine(t);
    matches!(h, IsaTerm::Const { n, .. } if (n == "Pure.eq" || n == "HOL.eq")) && args.len() == 2
}

fn app_spine(t: &IsaTerm) -> (&IsaTerm, Vec<&IsaTerm>) {
    let mut args = Vec::new();
    let mut cur = t;
    while let IsaTerm::App { f, a } = cur {
        args.push(a.as_ref());
        cur = f.as_ref();
    }
    args.reverse();
    (cur, args)
}

fn strip_wrappers(t: &IsaTerm) -> &IsaTerm {
    let mut cur = t;
    while let IsaTerm::App { f, a } = cur {
        if matches!(f.as_ref(), IsaTerm::Const { n, .. }
            if n == "Pure.prop" || n == "HOL.Trueprop" || n == "Trueprop")
        {
            cur = a.as_ref();
        } else {
            break;
        }
    }
    cur
}

fn split_imp(t: &IsaTerm) -> Option<(&IsaTerm, &IsaTerm)> {
    let t = strip_wrappers(t);
    if let IsaTerm::App { f, a: rhs } = t {
        if let IsaTerm::App { f: impf, a: lhs } = f.as_ref() {
            if matches!(impf.as_ref(), IsaTerm::Const { n, .. } if n == "Pure.imp") {
                return Some((lhs, rhs));
            }
        }
    }
    None
}

fn premises_and_concl(prop: &IsaTerm) -> (Vec<&IsaTerm>, &IsaTerm) {
    let mut prems = Vec::new();
    let mut cur = prop;
    while let Some((lhs, rhs)) = split_imp(cur) {
        prems.push(lhs);
        cur = rhs;
    }
    (prems, strip_wrappers(cur))
}

/// `head(argflags)` where each arg is tagged `K`=converse-const-bearing,
/// `L`=abstraction, `b`=bare Free/Var, `.`=other.
fn fmt_term(t: &IsaTerm) -> String {
    let (h, args) = app_spine(strip_wrappers(t));
    let hn = match h {
        IsaTerm::Const { n, .. } | IsaTerm::Free { n, .. } | IsaTerm::Var { n, .. } => {
            n.rsplit('.').next().unwrap_or(n).to_string()
        }
        IsaTerm::Abs { .. } => "λ".to_string(),
        IsaTerm::Bound { i } => format!("#{i}"),
        IsaTerm::App { .. } => "app".to_string(),
    };
    let flags: String = args
        .iter()
        .map(|a| {
            if walk_has_converse(a) {
                'K'
            } else if matches!(a, IsaTerm::Abs { .. }) {
                'L'
            } else if matches!(a, IsaTerm::Free { .. } | IsaTerm::Var { .. }) {
                'b'
            } else {
                '.'
            }
        })
        .collect();
    format!("{hn}({flags})")
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! One-off census helper (NOT a production path): scan a set of reject serials /
//! names for the **converse-operand duality signature** — a statement whose
//! operand is a λ-wrapped argument-flipped application of a variable relation
//! (`λa b. R b a`, the `Bound 0 / Bound 1` flip) — plus the explicit-`conversep`
//! cousin. Reads only via the corpus `.idx` seek-read (pure reads; no verify
//! lock, no kernel, no replay); parses ONLY each line's `prop` (a bounded prefix,
//! serde skips the heavy proof). Emits one TSV row per candidate to stdout.
//!
//! Usage:
//!   cargo run -q --example converse_census -p clean-mathverse -- \
//!     <corpus.jsonl> <serials.txt> <names.txt>
//!
//! `serials.txt`: one integer serial per line. `names.txt`: one theorem name per
//! line. A corpus entry is a candidate if its serial is in `serials.txt` OR its
//! name is in `names.txt`. Output columns:
//!   serial  name  lambda_converse  const_converse  duality_shape  converse_heads

use std::collections::{BTreeSet, HashSet};
use std::io::{Read as _, Seek as _};
use std::path::Path;

use clean_mathverse::hol::isabelle_index::{load_index, CorpusIndex, IndexEntry};
use clean_mathverse::hol::isabelle_pure::IsaTerm;

/// Bounded per-line read: `prop` is early in the line, so a prefix suffices and
/// bounds memory even for multi-MB proof trees we never parse.
const PREFIX_CAP: usize = 8 * 1024 * 1024;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 4 {
        eprintln!("usage: converse_census <corpus.jsonl> <serials.txt> <names.txt>");
        std::process::exit(2);
    }
    let corpus = Path::new(&args[1]);
    let serials: BTreeSet<i64> = std::fs::read_to_string(&args[2])
        .expect("read serials file")
        .lines()
        .filter_map(|l| l.trim().parse::<i64>().ok())
        .collect();
    let names: HashSet<String> = std::fs::read_to_string(&args[3])
        .expect("read names file")
        .lines()
        .map(|l| l.trim().to_string())
        .filter(|l| !l.is_empty())
        .collect();

    let idx_path = clean_mathverse::hol::isabelle_index::index_path(corpus);
    let index: CorpusIndex = load_index(&idx_path).expect("load .idx");

    // Single candidate pass over the index; open the corpus once, seek per hit.
    let mut f = std::fs::File::open(corpus).expect("open corpus");
    println!("serial\tname\tlambda_converse\tconst_converse\tduality_shape\tconverse_heads");
    let mut n_scanned = 0usize;
    let mut n_missing = 0usize;
    for e in &index.entries {
        let is_candidate = serials.contains(&e.serial) || names.contains(&e.name);
        if !is_candidate {
            continue;
        }
        match read_prop(&mut f, e) {
            Some(prop) => {
                n_scanned += 1;
                let rep = classify(&prop);
                let skel = if rep.lambda_converse {
                    statement_skeleton(&prop)
                } else {
                    String::new()
                };
                println!(
                    "{}\t{}\t{}\t{}\t{}\t{}\t{}",
                    e.serial,
                    e.name,
                    rep.lambda_converse,
                    rep.const_converse,
                    rep.duality_shape,
                    rep.converse_heads.into_iter().collect::<Vec<_>>().join(","),
                    skel
                );
            }
            None => n_missing += 1,
        }
    }
    eprintln!("scanned={n_scanned} prop-extract-failures={n_missing}");
}

/// Seek to the line, read a bounded prefix, and parse just the `prop` object.
fn read_prop(f: &mut std::fs::File, e: &IndexEntry) -> Option<IsaTerm> {
    f.seek(std::io::SeekFrom::Start(e.offset)).ok()?;
    let cap = (e.len as usize).min(PREFIX_CAP);
    let mut buf = vec![0u8; cap];
    let n = read_full(f, &mut buf)?;
    buf.truncate(n);
    let s = String::from_utf8_lossy(&buf);
    let sub = extract_prop_object(&s)?;
    let mut de = serde_json::Deserializer::from_str(sub);
    de.disable_recursion_limit();
    IsaTerm::deserialize(&mut de).ok()
}

fn read_full(f: &mut std::fs::File, buf: &mut [u8]) -> Option<usize> {
    let mut total = 0;
    while total < buf.len() {
        match f.read(&mut buf[total..]) {
            Ok(0) => break,
            Ok(k) => total += k,
            Err(_) => return None,
        }
    }
    Some(total)
}

use serde::Deserialize as _;

/// Extract the substring of the JSON `"prop":{...}` value by brace-matching
/// (quote/escape aware). Returns `None` if the prop object is not closed inside
/// the prefix (pathologically large statement — reported, not silently dropped).
fn extract_prop_object(line: &str) -> Option<&str> {
    let key = "\"prop\":";
    let at = line.find(key)? + key.len();
    let rest = &line[at..];
    let start = rest.find('{')?;
    let bytes = rest.as_bytes();
    let mut depth = 0i32;
    let mut in_str = false;
    let mut esc = false;
    for (i, &b) in bytes.iter().enumerate().skip(start) {
        if in_str {
            if esc {
                esc = false;
            } else if b == b'\\' {
                esc = true;
            } else if b == b'"' {
                in_str = false;
            }
            continue;
        }
        match b {
            b'"' => in_str = true,
            b'{' => depth += 1,
            b'}' => {
                depth -= 1;
                if depth == 0 {
                    return Some(&rest[start..=i]);
                }
            }
            _ => {}
        }
    }
    None
}

#[derive(Default)]
struct Report {
    lambda_converse: bool,
    const_converse: bool,
    duality_shape: bool,
    converse_heads: BTreeSet<String>,
}

/// Is `t` a converse λ-operand `λa b. R b a` (inner arg `Bound 0`, outer arg
/// `Bound 1`, i.e. arguments FLIPPED vs the η-identity `λa b. R a b`)? Returns
/// the relation head name when so.
fn lambda_converse_head(t: &IsaTerm) -> Option<String> {
    let IsaTerm::Abs { b: outer, .. } = t else {
        return None;
    };
    let IsaTerm::Abs { b: body, .. } = outer.as_ref() else {
        return None;
    };
    // body = App(App(R, a_inner), a_outer)
    let IsaTerm::App {
        f: inner,
        a: a_outer,
    } = body.as_ref()
    else {
        return None;
    };
    let IsaTerm::App { f: r, a: a_inner } = inner.as_ref() else {
        return None;
    };
    let flipped = matches!(a_inner.as_ref(), IsaTerm::Bound { i: 0 })
        && matches!(a_outer.as_ref(), IsaTerm::Bound { i: 1 });
    if !flipped {
        return None;
    }
    match r.as_ref() {
        IsaTerm::Free { n, .. } | IsaTerm::Var { n, .. } | IsaTerm::Const { n, .. } => {
            Some(n.clone())
        }
        _ => None,
    }
}

/// Explicit relation-converse constant heads (`conversep R`, `converse R`, BNF
/// `rel_conversep`, etc.) — the "already-named converse" cousin of the λ-flip.
fn is_const_converse_head(name: &str) -> bool {
    let tail = name.rsplit('.').next().unwrap_or(name);
    matches!(tail, "conversep" | "converse") || tail.ends_with("conversep") || tail == "transpose"
}

/// Head + curried argument spine.
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

/// Walk every subterm, collecting converse signals.
fn walk(t: &IsaTerm, rep: &mut Report) {
    if let Some(h) = lambda_converse_head(t) {
        rep.lambda_converse = true;
        rep.converse_heads.insert(h);
    }
    match t {
        IsaTerm::App { f, a } => {
            if let IsaTerm::Const { n, .. } = f.as_ref() {
                if is_const_converse_head(n) {
                    rep.const_converse = true;
                }
            }
            walk(f, rep);
            walk(a, rep);
        }
        IsaTerm::Abs { b, .. } => walk(b, rep),
        IsaTerm::Const { n, .. } if is_const_converse_head(n) => {
            rep.const_converse = true;
        }
        _ => {}
    }
}

/// Exact duality shape: some premise `Pred (op...)` whose operands are converse
/// λ-wraps, and the conclusion is `Pred (bare...)` with the SAME predicate head.
fn detect_duality_shape(prop: &IsaTerm) -> bool {
    let (prems, concl) = premises_and_concl(prop);
    let (chead, cargs) = app_spine(concl);
    let IsaTerm::Const { n: cn, .. } = chead else {
        return false;
    };
    // conclusion operands are bare relations (Free/Var), not λ-wrapped
    let concl_bare = !cargs.is_empty()
        && cargs
            .iter()
            .all(|a| matches!(a, IsaTerm::Free { .. } | IsaTerm::Var { .. }));
    if !concl_bare {
        return false;
    }
    prems.iter().any(|p| {
        let (ph, pargs) = app_spine(strip_wrappers(p));
        if let IsaTerm::Const { n: pn, .. } = ph {
            pn == cn && pargs.iter().any(|a| lambda_converse_head(a).is_some())
        } else {
            false
        }
    })
}

/// Short head name (last dotted segment) of a term's application head.
fn head_name(t: &IsaTerm) -> String {
    let (h, _) = app_spine(t);
    match h {
        IsaTerm::Const { n, .. } | IsaTerm::Free { n, .. } | IsaTerm::Var { n, .. } => {
            n.rsplit('.').next().unwrap_or(n).to_string()
        }
        IsaTerm::Abs { .. } => "λ".to_string(),
        IsaTerm::Bound { i } => format!("#{i}"),
        IsaTerm::App { .. } => "app".to_string(),
    }
}

/// Compact `[prem-heads] => concl-head(op-flags)` skeleton; each operand of the
/// conclusion (and of any converse-bearing premise) is tagged `C` when it is a
/// converse λ-flip, `b` when a bare relation, `·` otherwise.
fn statement_skeleton(prop: &IsaTerm) -> String {
    let (prems, concl) = premises_and_concl(prop);
    let fmt = |t: &IsaTerm| -> String {
        let (h, args) = app_spine(strip_wrappers(t));
        let hn = match h {
            IsaTerm::Const { n, .. } | IsaTerm::Free { n, .. } | IsaTerm::Var { n, .. } => {
                n.rsplit('.').next().unwrap_or(n).to_string()
            }
            _ => head_name(t),
        };
        let flags: String = args
            .iter()
            .map(|a| {
                if lambda_converse_head(a).is_some() {
                    'C'
                } else if matches!(a, IsaTerm::Free { .. } | IsaTerm::Var { .. }) {
                    'b'
                } else {
                    '.'
                }
            })
            .collect();
        format!("{hn}({flags})")
    };
    let prem_s: Vec<String> = prems.iter().map(|p| fmt(p)).collect();
    format!("[{}] => {}", prem_s.join(" ; "), fmt(concl))
}

fn classify(prop: &IsaTerm) -> Report {
    let mut rep = Report::default();
    walk(prop, &mut rep);
    rep.duality_shape = detect_duality_shape(prop);
    rep
}

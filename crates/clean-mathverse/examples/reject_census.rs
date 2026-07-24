// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! One-off reject-frontier census helper (NOT a production path). Read-only:
//! loads the `<corpus>.idx` sidecar and does targeted seek-reads of the corpus
//! for a serial set. No verify lock, no kernel replay — pure `.idx`/seek reads.
//!
//! Modes (`cargo run -q --example reject_census -p clean-mathverse -- <corpus> <mode> ...`):
//!
//! * `cascade <seeds.txt>` — build the reverse dependency graph over EVERY indexed
//!   serial (`"k":"thm","id":` byte-superset edges) and report, for the seed set,
//!   the size of the union of transitive dependents (the "cascade weight" — how
//!   many corpus lines are gated behind the seeds), plus the top individual seeds
//!   by their own dependent count.
//! * `decode <serials.txt>` — for each serial, seek-read + parse the theorem and
//!   print the conclusion head + Pi arity + premise heads + proof root kind + the
//!   distinct `axm:` names the proof references (the last is the unmapped-axiom
//!   name-mining view).
//! * `axmrank <serials.txt>` — aggregate the distinct-per-serial `axm:` names over
//!   the serial set and print them ranked (unmapped-axiom pattern census).
//! * `emit <serial> <out.jsonl>` — write the VERBATIM trimmed corpus line (exact
//!   fixture extraction).

use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};
use std::io::{Read as _, Seek as _};
use std::path::Path;

use clean_mathverse::hol::isabelle_index::{index_path, load_index, CorpusIndex, IndexEntry};
use clean_mathverse::hol::isabelle_pure::{parse_proven_theorem, IsaProof, IsaTerm};

/// Cap a single decode read (deep proofs can be huge; we only need `prop`+head).
const DECODE_CAP: usize = 64 * 1024 * 1024;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 3 {
        eprintln!("usage: reject_census <corpus.jsonl> <cascade|decode|axmrank|emit> <args...>");
        std::process::exit(2);
    }
    let corpus = Path::new(&args[1]);
    let mode = args[2].as_str();
    let index = load_index(&index_path(corpus)).expect("load .idx");
    eprintln!("idx: {} entries", index.entries.len());

    match mode {
        "cascade" => cascade(&index, &read_serials(&args[3])),
        "decode" => decode(&index, corpus, &read_serials(&args[3])),
        "axmrank" => axmrank(&index, corpus, &read_serials(&args[3])),
        "emit" => emit(&index, corpus, args[3].parse().expect("serial"), &args[4]),
        other => {
            eprintln!("unknown mode: {other}");
            std::process::exit(2);
        }
    }
}

fn read_serials(path: &str) -> Vec<i64> {
    std::fs::read_to_string(path)
        .expect("read serials")
        .lines()
        .filter_map(|l| l.trim().parse::<i64>().ok())
        .collect()
}

/// Reverse-reachability cascade weight. Edge `x -> d` means "x depends on d"
/// (`e.deps`). The lines gated behind a reject `r` are its transitive dependents
/// = nodes reaching `r` in the forward graph = descendants of `r` in the REVERSE
/// graph. Report the union over all seeds (the family's cascade) and the per-seed
/// dependent counts (for intra-family targeting).
fn cascade(index: &CorpusIndex, seeds: &[i64]) {
    // Reverse adjacency: for each dep `d`, the serials that list it.
    let mut radj: HashMap<i64, Vec<i64>> = HashMap::new();
    for e in &index.entries {
        for &d in &e.deps {
            radj.entry(d).or_default().push(e.serial);
        }
    }
    let present: HashSet<i64> = seeds.iter().copied().collect();
    let n_present = seeds.iter().filter(|s| index.get(**s).is_some()).count();

    // Per-seed reverse-reach (own transitive dependents, seed excluded).
    let mut per_seed: Vec<(i64, usize)> = Vec::with_capacity(seeds.len());
    for &s in seeds {
        per_seed.push((s, reach_count(&radj, &[s])));
    }
    per_seed.sort_by_key(|&(_, c)| std::cmp::Reverse(c));

    // Union reverse-reach over the whole seed set (the family cascade weight).
    let union = reach_count(&radj, seeds);

    println!("SEEDS: {} ({} present in idx)", seeds.len(), n_present);
    println!("UNION reverse-reachable dependents (family cascade weight): {union}");
    println!("  (seeds themselves: {})", present.len());
    println!("TOP seeds by own dependent count:");
    for (s, c) in per_seed.iter().take(25) {
        println!("  s{s}\t{c}");
    }
    // Distribution: how many seeds gate 0 / 1-9 / 10-99 / 100+ dependents.
    let mut b0 = 0;
    let mut b1 = 0;
    let mut b2 = 0;
    let mut b3 = 0;
    for (_, c) in &per_seed {
        match c {
            0 => b0 += 1,
            1..=9 => b1 += 1,
            10..=99 => b2 += 1,
            _ => b3 += 1,
        }
    }
    println!("seed dependent-count buckets: 0:{b0}  1-9:{b1}  10-99:{b2}  100+:{b3}");
}

/// Number of distinct transitive dependents of `seeds` in the reverse graph
/// (the seeds themselves are not counted).
fn reach_count(radj: &HashMap<i64, Vec<i64>>, seeds: &[i64]) -> usize {
    let mut seen: HashSet<i64> = HashSet::new();
    let mut q: VecDeque<i64> = VecDeque::new();
    for &s in seeds {
        q.push_back(s);
    }
    let seed_set: HashSet<i64> = seeds.iter().copied().collect();
    while let Some(cur) = q.pop_front() {
        if let Some(deps) = radj.get(&cur) {
            for &up in deps {
                if seen.insert(up) {
                    q.push_back(up);
                }
            }
        }
    }
    // Exclude the seeds from their own dependent count.
    seen.difference(&seed_set).count()
}

fn decode(index: &CorpusIndex, corpus: &Path, serials: &[i64]) {
    let mut f = std::fs::File::open(corpus).expect("open corpus");
    for &s in serials {
        let Some(e) = index.get(s) else {
            println!("s{s}\tMISSING");
            continue;
        };
        let Some(line) = read_line_capped(&mut f, e) else {
            println!("s{s}\tREAD-ERR");
            continue;
        };
        let thm = match parse_proven_theorem(&line) {
            Ok(t) => t,
            Err(err) => {
                println!("s{s}\tPARSE-ERR {err}");
                continue;
            }
        };
        let (prems, concl) = premises_and_concl(&thm.prop);
        let mut axms: BTreeMap<String, usize> = BTreeMap::new();
        collect_axms(&thm.proof, &mut axms);
        let axm_s: Vec<String> = axms.keys().cloned().collect();
        println!(
            "s{s}\tname={}\troot={}\tnprem={}\tconcl={}\tprem_heads=[{}]\taxms=[{}]",
            if thm.name.is_empty() { "-" } else { &thm.name },
            proof_root_kind(&thm.proof),
            prems.len(),
            head_of(concl),
            prems
                .iter()
                .copied()
                .map(head_of)
                .collect::<Vec<_>>()
                .join(","),
            axm_s.join(","),
        );
    }
}

/// Rank the distinct-per-serial `axm:` names over the serial set.
fn axmrank(index: &CorpusIndex, corpus: &Path, serials: &[i64]) {
    let mut f = std::fs::File::open(corpus).expect("open corpus");
    let mut tally: BTreeMap<String, usize> = BTreeMap::new();
    let mut parsed = 0usize;
    let mut missing = 0usize;
    for &s in serials {
        let Some(e) = index.get(s) else {
            missing += 1;
            continue;
        };
        let Some(line) = read_line_capped(&mut f, e) else {
            continue;
        };
        let Ok(thm) = parse_proven_theorem(&line) else {
            continue;
        };
        parsed += 1;
        let mut axms: BTreeMap<String, usize> = BTreeMap::new();
        collect_axms(&thm.proof, &mut axms);
        for k in axms.keys() {
            *tally.entry(k.clone()).or_default() += 1;
        }
    }
    let mut ranked: Vec<(String, usize)> = tally.into_iter().collect();
    ranked.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
    println!("parsed={parsed} missing={missing} of {}", serials.len());
    for (name, c) in ranked.iter().take(60) {
        println!("  {c}\t{name}");
    }
}

fn emit(index: &CorpusIndex, corpus: &Path, serial: i64, out: &str) {
    let e = index.get(serial).expect("serial in idx");
    let mut f = std::fs::File::open(corpus).expect("open corpus");
    f.seek(std::io::SeekFrom::Start(e.offset)).expect("seek");
    let mut buf = vec![0u8; e.len as usize];
    f.read_exact(&mut buf).expect("read");
    let line = String::from_utf8_lossy(&buf);
    let trimmed = line.trim_end_matches(['\n', '\r']);
    std::fs::write(out, format!("{trimmed}\n")).expect("write fixture");
    eprintln!("emit s{serial} -> {out} ({} bytes)", trimmed.len());
}

fn read_line_capped(f: &mut std::fs::File, e: &IndexEntry) -> Option<String> {
    f.seek(std::io::SeekFrom::Start(e.offset)).ok()?;
    let cap = (e.len as usize).min(DECODE_CAP);
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
    Some(String::from_utf8_lossy(&buf).into_owned())
}

fn collect_axms(p: &IsaProof, out: &mut BTreeMap<String, usize>) {
    match p {
        IsaProof::Axm { name, .. } => {
            *out.entry(name.clone()).or_default() += 1;
        }
        IsaProof::AbsP { b, .. } | IsaProof::Abst { b, .. } => collect_axms(b, out),
        IsaProof::AppP { f, a } => {
            collect_axms(f, out);
            collect_axms(a, out);
        }
        IsaProof::AppT { f, .. } => collect_axms(f, out),
        _ => {}
    }
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
        IsaProof::Bound { .. } => "PBound",
        IsaProof::OfClass { .. } => "OfClass",
        IsaProof::Oracle { .. } => "Oracle",
        IsaProof::Min => "Min",
        IsaProof::Nop => "Nop",
        IsaProof::Other => "Other",
    }
}

/// `head/nargs` of a term after stripping `Trueprop`/`Pure.prop` wrappers.
fn head_of(t: &IsaTerm) -> String {
    let (h, args) = app_spine(strip_wrappers(t));
    let hn = match h {
        IsaTerm::Const { n, .. } => n.rsplit('.').next().unwrap_or(n).to_string(),
        IsaTerm::Free { n, .. } => format!("Free:{}", n.rsplit('.').next().unwrap_or(n)),
        IsaTerm::Var { n, .. } => format!("Var:{}", n.rsplit('.').next().unwrap_or(n)),
        IsaTerm::Bound { i } => format!("#{i}"),
        IsaTerm::Abs { .. } => "λ".to_string(),
        IsaTerm::App { .. } => "app".to_string(),
    };
    format!("{hn}/{}", args.len())
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

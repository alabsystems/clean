// Reproduction harness for the 4.30.0 olean loader bug.
// Usage: cargo run --example repro_430 -- <dir-with-oleans> [N]
//
// Measures BOTH:
//   parse  = clean_olean::parse_module (parse + full Expr reconstruction)
//   load   = clean_olean::load_olean_file (parse + register into kernel Env;
//            this is the path whose `load_success` the ingestion doc measures)
use clean_kernel::env::Environment;
use clean_olean::import::{load_olean_file, parse_module};
use std::collections::BTreeMap;
use std::path::PathBuf;

fn collect_oleans(dir: &std::path::Path, out: &mut Vec<PathBuf>) {
    if let Ok(rd) = std::fs::read_dir(dir) {
        for e in rd.flatten() {
            let p = e.path();
            if p.is_dir() {
                collect_oleans(&p, out);
            } else if p.extension().and_then(|s| s.to_str()) == Some("olean") {
                // skip .olean.server / .olean.private siblings by extension only
                out.push(p);
            }
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let dir = PathBuf::from(args.get(1).cloned().unwrap_or_default());
    let limit: usize = args
        .get(2)
        .and_then(|s| s.parse().ok())
        .unwrap_or(usize::MAX);

    let mut files = Vec::new();
    collect_oleans(&dir, &mut files);
    files.sort();
    let total = files.len().min(limit);
    files.truncate(total);

    let mut parse_ok = 0usize;
    let mut parse_ok_with_consts = 0usize;
    let mut parse_fail = 0usize;
    let mut total_consts = 0usize;
    let mut parse_errs: BTreeMap<String, usize> = BTreeMap::new();
    let mut parse_samples: Vec<(String, String)> = Vec::new();

    let mut load_ok = 0usize;
    let mut load_ok_added = 0usize;
    let mut load_fail = 0usize;
    let mut total_added = 0usize;
    let mut load_errs: BTreeMap<String, usize> = BTreeMap::new();
    let mut load_samples: Vec<(String, String)> = Vec::new();

    for f in &files {
        let fname = f.file_name().unwrap().to_string_lossy().to_string();

        // 1) parse_module (parse + Expr reconstruction)
        match std::fs::read(f).ok().and_then(|b| parse_module(&b).ok()) {
            Some(m) => {
                parse_ok += 1;
                total_consts += m.constants.len();
                if !m.constants.is_empty() {
                    parse_ok_with_consts += 1;
                }
            }
            None => {
                // re-run to capture the error
                parse_fail += 1;
                if let Ok(b) = std::fs::read(f) {
                    if let Err(e) = parse_module(&b) {
                        let kind = format!("{e:?}");
                        let short = kind
                            .split(['(', '{', ' '])
                            .next()
                            .unwrap_or(&kind)
                            .to_string();
                        *parse_errs.entry(short).or_default() += 1;
                        if parse_samples.len() < 8 {
                            parse_samples.push((fname.clone(), kind.chars().take(160).collect()));
                        }
                    }
                }
            }
        }

        // 2) load_olean_file (parse + register into kernel Environment).
        // Fresh env per file in isolation (matches verify_one_isolated).
        let mut env = Environment::default();
        match load_olean_file(&mut env, f) {
            Ok(ls) => {
                load_ok += 1;
                total_added += ls.added_constants;
                if ls.added_constants > 0 {
                    load_ok_added += 1;
                }
            }
            Err(e) => {
                load_fail += 1;
                let kind = format!("{e}");
                let short = kind.split([':', '(']).next().unwrap_or(&kind).to_string();
                *load_errs.entry(short).or_default() += 1;
                if load_samples.len() < 8 {
                    load_samples.push((fname.clone(), kind.chars().take(200).collect()));
                }
            }
        }
    }

    println!("=== repro_430 ===");
    println!("dir   : {}", dir.display());
    println!("total : {total}");
    println!("--- parse_module (parse + Expr reconstruction) ---");
    println!("  parse OK           : {parse_ok}");
    println!("  parse OK w/ consts : {parse_ok_with_consts}");
    println!("  parse FAIL         : {parse_fail}");
    println!("  total constants    : {total_consts}");
    for (k, n) in &parse_errs {
        println!("    err {n:6}  {k}");
    }
    for (f, e) in &parse_samples {
        println!("    sample {f}: {e}");
    }
    println!("--- load_olean_file (register into kernel env; doc's load_success) ---");
    println!("  load OK            : {load_ok}");
    println!("  load OK w/ added   : {load_ok_added}");
    println!("  load FAIL          : {load_fail}");
    println!("  total added consts : {total_added}");
    for (k, n) in &load_errs {
        println!("    err {n:6}  {k}");
    }
    for (f, e) in &load_samples {
        println!("    sample {f}: {e}");
    }
}

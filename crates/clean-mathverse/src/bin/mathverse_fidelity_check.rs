// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Audit each `.mathverse` shard's semantic density — distinguishing
//! proof-bearing / dense-type-tree shards from name-only stub imports.
//!
//! This is a STRUCTURAL density metric only. It reads the shard header and
//! compares the `expr_count / constant_count` ratio; it does NOT run any
//! Clean-kernel proof check and makes NO verification claim. The tier names
//! describe the shape of the imported type data, not its provability.
//!
//! Reads each shard's 256-byte header (per `shard.rs` layout) without
//! decompressing the body, computes the `expr_count / constant_count`
//! ratio, and classifies each shard into a structural-density tier:
//!
//!   - `DenseTypeTrees`   real type trees, `expr/const >= 5.0`
//!   - `ProofVerified`    `expr/const >= 1.0` (e.g. Metamath RPN bodies)
//!   - `HolImported`      `expr/const >= 0.5` (e.g. OpenTheory: shared subterms)
//!   - `SurfaceNamesOnly` `expr_count <= 2` regardless of constant count
//!     — the shard has one shared placeholder type
//!   - `Empty`            no constants
//!
//! Output: one JSON line per shard plus a summary. Non-zero exit when
//! ANY shard claims `>1000` constants but is classified `SurfaceNamesOnly`.
//!
//! Usage:
//!   mathverse_fidelity_check <shard-dir>
//!   mathverse_fidelity_check <shard-dir> --strict
//!     # exit non-zero if any shard is SurfaceNamesOnly

use std::env;
use std::fs;
use std::io::Read;
use std::path::Path;
use std::process::ExitCode;

const MAGIC_OMEG: u32 = 0x4F4D_4547;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Fidelity {
    /// `expr/const >= 5.0`: the shard carries dense, fully-elaborated type
    /// signatures (many `FlatExpr` nodes per constant). This is a STRUCTURAL
    /// density metric, NOT a Clean-kernel proof check — it makes no
    /// verification claim about the constants.
    DenseTypeTrees,
    ProofVerified,
    HolImported,
    SurfaceNamesOnly,
    Empty,
}

impl Fidelity {
    fn classify(constants: u32, exprs: u32) -> Self {
        if constants == 0 {
            return Self::Empty;
        }
        // Single shared placeholder is the stub signature: lots of
        // constants pointing at one trivial FlatExpr.
        if exprs <= 2 {
            return Self::SurfaceNamesOnly;
        }
        let ratio = f64::from(exprs) / f64::from(constants);
        if ratio >= 5.0 {
            Self::DenseTypeTrees
        } else if ratio >= 1.0 {
            Self::ProofVerified
        } else {
            Self::HolImported
        }
    }

    fn label(self) -> &'static str {
        match self {
            Self::DenseTypeTrees => "DenseTypeTrees",
            Self::ProofVerified => "ProofVerified",
            Self::HolImported => "HolImported",
            Self::SurfaceNamesOnly => "SurfaceNamesOnly",
            Self::Empty => "Empty",
        }
    }
}

struct ShardSummary {
    path: String,
    size_bytes: u64,
    version: u32,
    constant_count: u32,
    expr_count: u32,
    string_count: u32,
    fidelity: Fidelity,
}

fn read_header(path: &Path) -> std::io::Result<[u8; 256]> {
    let mut buf = [0u8; 256];
    let mut f = fs::File::open(path)?;
    f.read_exact(&mut buf)?;
    Ok(buf)
}

fn parse_u32(b: &[u8], offset: usize) -> u32 {
    u32::from_le_bytes([b[offset], b[offset + 1], b[offset + 2], b[offset + 3]])
}

fn audit_shard(path: &Path) -> Option<ShardSummary> {
    let hdr = read_header(path).ok()?;
    let magic = parse_u32(&hdr, 0);
    if magic != MAGIC_OMEG {
        return None;
    }
    // Layout per shard.rs (after the 4-byte magic): version, flags,
    // string_count, string_data_len, level_count, expr_count,
    // constant_count, bloom_size, provenance_len, sorted_index_len,
    // level_lists_count
    let version = parse_u32(&hdr, 4);
    let string_count = parse_u32(&hdr, 12);
    let expr_count = parse_u32(&hdr, 24);
    let constant_count = parse_u32(&hdr, 28);
    let size = fs::metadata(path).ok().map(|m| m.len()).unwrap_or(0);
    Some(ShardSummary {
        path: path.display().to_string(),
        size_bytes: size,
        version,
        constant_count,
        expr_count,
        string_count,
        fidelity: Fidelity::classify(constant_count, expr_count),
    })
}

fn collect_shards(dir: &Path, out: &mut Vec<std::path::PathBuf>) {
    if let Ok(rd) = fs::read_dir(dir) {
        for entry in rd.filter_map(|e| e.ok()) {
            let p = entry.path();
            if p.is_dir() {
                collect_shards(&p, out);
            } else if p.extension().is_some_and(|e| e == "mathverse") {
                out.push(p);
            }
        }
    }
}

fn main() -> ExitCode {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("usage: mathverse_fidelity_check <shard-dir> [--strict]");
        eprintln!();
        eprintln!("Audits each .mathverse shard's semantic density and prints a per-shard");
        eprintln!(
            "structural-density classification (DenseTypeTrees / ProofVerified / HolImported /"
        );
        eprintln!("SurfaceNamesOnly / Empty) based on the expr_count / constant_count ratio.");
        eprintln!(
            "This is a structural density metric only; it is NOT a Clean-kernel proof check."
        );
        return ExitCode::from(2);
    }
    let dir = Path::new(&args[1]);
    let strict = args.iter().any(|a| a == "--strict");

    let mut shards = Vec::new();
    collect_shards(dir, &mut shards);
    shards.sort();

    if shards.is_empty() {
        eprintln!("no .mathverse shards under {}", dir.display());
        return ExitCode::from(2);
    }

    let mut summaries = Vec::with_capacity(shards.len());
    for path in &shards {
        match audit_shard(path) {
            Some(s) => summaries.push(s),
            None => {
                eprintln!("WARN: could not read header of {}", path.display());
            }
        }
    }

    println!(
        "{:<55} {:>4} {:>8} {:>10} {:>10} {:>10} {:>10}  fidelity",
        "shard", "ver", "size_MB", "strings", "consts", "exprs", "expr/c"
    );
    println!("{}", "-".repeat(132));

    let mut tier_counts = std::collections::BTreeMap::<&str, u32>::new();
    let mut stub_with_volume: Vec<&ShardSummary> = Vec::new();
    for s in &summaries {
        let ratio = if s.constant_count > 0 {
            f64::from(s.expr_count) / f64::from(s.constant_count)
        } else {
            0.0
        };
        let basename = Path::new(&s.path)
            .file_name()
            .map(|n| n.to_string_lossy().into_owned())
            .unwrap_or_else(|| s.path.clone());
        let path_short = if basename.len() < 55 {
            basename
        } else {
            format!("…{}", &s.path[s.path.len() - 53..])
        };
        println!(
            "{:<55} {:>4} {:>8.1} {:>10} {:>10} {:>10} {:>10.2}  {}",
            path_short,
            s.version,
            s.size_bytes as f64 / 1_048_576.0,
            s.string_count,
            s.constant_count,
            s.expr_count,
            ratio,
            s.fidelity.label()
        );
        *tier_counts.entry(s.fidelity.label()).or_insert(0) += 1;
        if matches!(s.fidelity, Fidelity::SurfaceNamesOnly) && s.constant_count >= 1_000 {
            stub_with_volume.push(s);
        }
    }

    println!();
    println!("=== summary ===");
    for (tier, n) in &tier_counts {
        println!("  {tier:<20} {n}");
    }

    let total_consts: u64 = summaries.iter().map(|s| s.constant_count as u64).sum();
    let stub_consts: u64 = summaries
        .iter()
        .filter(|s| matches!(s.fidelity, Fidelity::SurfaceNamesOnly))
        .map(|s| s.constant_count as u64)
        .sum();
    let real_consts = total_consts - stub_consts;
    println!();
    println!("  total declarations:        {total_consts:>10}");
    println!(
        "  with real semantic content {real_consts:>10}  ({:.1}%)",
        100.0 * real_consts as f64 / total_consts.max(1) as f64
    );
    println!(
        "  surface-names-only stub:   {stub_consts:>10}  ({:.1}%)",
        100.0 * stub_consts as f64 / total_consts.max(1) as f64
    );

    if !stub_with_volume.is_empty() {
        println!();
        println!("=== stub shards with >=1000 'declarations' (high-volume metadata) ===");
        for s in &stub_with_volume {
            println!(
                "  ! {}: {} constants but only {} FlatExpr → name-only",
                Path::new(&s.path)
                    .file_name()
                    .map(|n| n.to_string_lossy().to_string())
                    .unwrap_or_default(),
                s.constant_count,
                s.expr_count
            );
        }
        if strict {
            eprintln!();
            eprintln!("STRICT: refusing to validate — name-only stub shards present.");
            return ExitCode::from(1);
        }
    }
    ExitCode::SUCCESS
}

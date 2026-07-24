//! Register an existing `.mathverse` shard file into a library `manifest.json`.
//!
//! There is no CLI verb to add a pre-built shard to the on-disk library
//! manifest (the `MathverseManifest`/`LibraryLoader` API exists but is not
//! exposed as a `mathverse` subcommand). This example fills that gap: it
//! copies a shard into `<library>/base/`, computes its blake3 content hash
//! exactly as `LibraryLoader::write_shard` does, reads its header for the
//! constant/expr counts, appends a `ShardEntry`, and atomically saves the
//! manifest.
//!
//! Usage:
//!   cargo run -p clean-mathverse --release --example register_shard -- \
//!     <library-root> <shard-file.mathverse> <source-name>
//!
//! Example:
//!   cargo run -p clean-mathverse --release --example register_shard -- \
//!     data/mathverse-shards \
//!     data/corpora/metamath/set.mathverse.mathverse \
//!     metamath-set

use clean_mathverse::manifest::{LibraryPaths, MathverseManifest, ShardEntry};
use clean_mathverse::shard::ShardReader;
use std::error::Error;
use std::path::PathBuf;

fn main() -> Result<(), Box<dyn Error>> {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 4 {
        eprintln!("usage: register_shard <library-root> <shard-file.mathverse> <source-name>");
        std::process::exit(2);
    }
    let root = PathBuf::from(&args[1]);
    let shard_src = PathBuf::from(&args[2]);
    let source = args[3].clone();

    let paths = LibraryPaths::new(root.clone());
    paths.create_dirs()?;

    // Destination inside base/ keyed by source name.
    let dst = paths.base_shard_path(&source);
    if shard_src != dst {
        std::fs::copy(&shard_src, &dst)?;
    }
    let rel_path = format!("base/{source}.mathverse");

    // blake3 over the exact on-disk bytes (matches write_shard / release.rs).
    let data = std::fs::read(&dst)?;
    let content_hash = blake3::hash(&data).to_hex().to_string();

    // Header counts via ShardReader.
    let reader = ShardReader::from_file(&dst)?;
    let entry = ShardEntry {
        path: rel_path.clone(),
        content_hash: content_hash.clone(),
        constant_count: reader.header.constant_count,
        expr_count: reader.header.expr_count,
        source,
    };

    // Load-or-create manifest, dedupe by path, register, save atomically.
    let mut manifest = if paths.manifest.exists() {
        MathverseManifest::load(&paths.manifest)?
    } else {
        MathverseManifest::new()
    };
    manifest.remove_shard(&rel_path);
    manifest.add_base_shard(entry);
    manifest.save(&paths.manifest)?;

    println!(
        "registered {rel_path}: {} constants, {} exprs, blake3={}",
        reader.header.constant_count, reader.header.expr_count, content_hash
    );
    println!(
        "manifest now: {} base shards, {} total constants",
        manifest.base_shards.len(),
        manifest.total_constants
    );
    Ok(())
}

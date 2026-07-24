// SPDX-License-Identifier: Apache-2.0
//! One-shot: call a single structured importer.
//! Usage: mathverse_structured_import <kind> <input-dir> <output-dir>
//! kind: dafny | acl2 | lean3 | coq | agda | twelf | fstar | idris | pvs
//!       | mizar-source | matita | coq-sexp | isabelle

use std::env;
use std::path::Path;
use std::process::exit;
use std::time::Instant;

use clean_mathverse::structured_import;

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() != 4 {
        eprintln!("usage: mathverse_structured_import <kind> <input-dir> <output-dir>");
        eprintln!(
            "       kind: dafny | acl2 | lean3 | coq | agda | twelf | fstar | idris | pvs\n             \
             | mizar-source | matita | coq-sexp | isabelle"
        );
        exit(2);
    }
    let kind = &args[1];
    let input = Path::new(&args[2]);
    let output = Path::new(&args[3]);
    if let Err(e) = std::fs::create_dir_all(output) {
        eprintln!("failed to create output dir {}: {e}", output.display());
        exit(2);
    }
    let start = Instant::now();
    let stats = match kind.as_str() {
        "dafny" => structured_import::convert_dafny_dir(input, output),
        "acl2" => structured_import::convert_acl2_dir(input, output),
        "lean3" => structured_import::convert_lean3_dir(input, output),
        "coq" => structured_import::convert_coq_v_dir(input, output),
        "agda" => structured_import::convert_agda_dir(input, output),
        "twelf" => structured_import::convert_twelf_dir(input, output),
        "fstar" => structured_import::convert_fstar_dir(input, output),
        "idris" => structured_import::convert_idris_dir(input, output),
        "pvs" => structured_import::convert_pvs_dir(input, output),
        "mizar-source" => structured_import::convert_mizar_source_dir(input, output),
        "matita" => structured_import::convert_matita_dir(input, output),
        "coq-sexp" => structured_import::convert_coq_sexp_dir(input, output),
        "isabelle" => structured_import::convert_isabelle_thy_dir(input, output),
        other => {
            eprintln!("unknown kind: {other}");
            exit(2);
        }
    };
    let elapsed = start.elapsed();
    println!(
        "{kind}: stats={:?}, elapsed={:.2}s",
        stats,
        elapsed.as_secs_f64()
    );
}

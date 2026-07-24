// Correctness spot-check: reconstruct constants from a 4.30.0 olean and print
// their names/kinds/types so a human can confirm they are REAL Lean structure
// (not garbage from a wrong base_addr).
// Usage: cargo run --example dump_430 -- <file.olean> [N]
use clean_olean::import::parse_module;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let path = args.get(1).cloned().unwrap_or_default();
    let n: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(12);
    let bytes = std::fs::read(&path).expect("read olean");
    let m = parse_module(&bytes).expect("parse_module");
    println!("file: {path}");
    println!("constants: {}", m.constants.len());
    println!("imports  : {}", m.imports.len());
    for imp in m.imports.iter().take(6) {
        println!("  import {}", imp.module_name);
    }
    for c in m.constants.iter().take(n) {
        let ty = c
            .type_
            .as_ref()
            .map(|e| format!("{e:?}"))
            .unwrap_or_else(|| "<none>".into());
        let ty_short: String = ty.chars().take(140).collect();
        let has_val = c.value.is_some();
        println!(
            "  [{:?}] {}  lvls={:?}  val={}  type={}",
            c.kind, c.name, c.level_params, has_val, ty_short
        );
    }
}

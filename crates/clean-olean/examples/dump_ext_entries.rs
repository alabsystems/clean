// Audit probe: dump persistent environment-extension entries as Clean's
// .olean parser sees them TODAY (lane B env-ext restore audit, 2026-07-09).
// Prints per-extension entry counts (Named vs RawScalar) and, for a chosen
// extension, the first few decoded entries so a human can compare against
// Lean's ground-truth serialization.
// Usage: cargo run -p clean-olean --example dump_ext_entries -- <file.olean> [ext-substr] [N]
use clean_olean::import::{parse_module, parse_module_incremental};
use clean_olean::{OLeanLevel, ParsedExtensionEntry, ParsedExtensionEntryData};

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let path = std::path::PathBuf::from(args.get(1).cloned().unwrap_or_default());
    let filter = args.get(2).cloned().unwrap_or_default();
    let n: usize = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(8);

    // Mirror the loading path (`load_companions_*`): server/private parts are
    // parsed INCREMENTALLY against the base region (their pointers reference
    // base objects), never standalone.
    let base_bytes = std::fs::read(&path).expect("read base olean");
    println!("file: {}", path.display());
    let base = parse_module(&base_bytes).expect("parse base");
    dump_part(OLeanLevel::Exported, &base, &filter, n);

    let server_path = path.with_extension("olean.server");
    let server_bytes = std::fs::read(&server_path).ok();
    if let Some(sb) = server_bytes.as_deref() {
        match parse_module_incremental(&base_bytes, None, sb) {
            Ok(m) => dump_part(OLeanLevel::Server, &m, &filter, n),
            Err(e) => println!("\n#### part: server — PARSE ERROR: {e}"),
        }
    }
    let private_path = path.with_extension("olean.private");
    if let Ok(pb) = std::fs::read(&private_path) {
        match parse_module_incremental(&base_bytes, server_bytes.as_deref(), &pb) {
            Ok(m) => dump_part(OLeanLevel::Private, &m, &filter, n),
            Err(e) => println!("\n#### part: private — PARSE ERROR: {e}"),
        }
    }
}

fn dump_part(
    level: clean_olean::OLeanLevel,
    m: &clean_olean::ParsedModule,
    filter: &str,
    n: usize,
) {
    println!("\n#### part: {level} — extensions: {}", m.entries.len());
    for ext in &m.entries {
        let named = ext
            .entries
            .iter()
            .filter(|e| matches!(e, ParsedExtensionEntry::Named { .. }))
            .count();
        let typed = ext
            .entries
            .iter()
            .filter(|e| matches!(e, ParsedExtensionEntry::Instance(_)))
            .count();
        let raw = ext.entries.len() - named - typed;
        println!(
            "  {:60} total={:<6} named={:<6} typed={:<6} raw_scalar={:<6} undecoded={}",
            ext.extension_name,
            ext.entries.len(),
            named,
            typed,
            raw,
            ext.undecoded_entries
        );
    }
    if filter.is_empty() {
        return;
    }
    for ext in &m.entries {
        if !ext.extension_name.contains(filter) {
            continue;
        }
        println!("\n== {} ==", ext.extension_name);
        for e in ext.entries.iter().take(n) {
            match e {
                ParsedExtensionEntry::Named { name, data } => match data {
                    ParsedExtensionEntryData::Scalar(v) => {
                        println!("  Named {{ name: {name}, data: Scalar({v:#x}) }}");
                    }
                    ParsedExtensionEntryData::Object(bytes) => {
                        let head: Vec<String> =
                            bytes.iter().take(48).map(|b| format!("{b:02x}")).collect();
                        println!(
                            "  Named {{ name: {name}, data: Object(len={}) }} head={}",
                            bytes.len(),
                            head.join(" ")
                        );
                    }
                    _ => println!("  Named {{ name: {name}, data: <other> }}"),
                },
                ParsedExtensionEntry::RawScalar(v) => println!("  RawScalar({v:#x})"),
                other => println!("  {other:?}"),
            }
        }
    }
}

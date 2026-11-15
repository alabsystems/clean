//! STOCK EXCEPTION quorum member: structured named and statement-bound replay.
#![forbid(unsafe_code)]
use clean_ck0::export::{self, name_components, Dialect, Refusal, Report, TargetRequest};
use std::io::BufReader;
fn emit(report: &Report) -> bool {
    for row in &report.rows {
        let value = match &row.verdict {
            Ok(()) => {
                serde_json::json!({"kind":"declaration", "name":name_components(&row.name), "accepted":true})
            }
            Err(e) => {
                serde_json::json!({"kind":"declaration", "name":name_components(&row.name), "accepted":false,"reason":e.reason(),"detail":e.to_string()})
            }
        };
        println!("{value}");
    }
    let (accepted, refused) = report.counts();
    println!(
        "{}",
        serde_json::json!({"kind":"coverage", "accepted":accepted, "total":report.rows.len(), "refused":refused, "axioms":report.axioms.iter().map(name_components).collect::<Vec<_>>()})
    );
    !report.rows.is_empty() && accepted == report.rows.len()
}
fn run() -> Result<bool, Refusal> {
    let mut args = std::env::args_os().skip(1);
    let path = args.next().ok_or_else(|| Refusal::Malformed("usage: ck0-replay EXPORT [--inspect-target-json NAME | --target-json NAME --statement-sha256 SHA256]".into()))?;
    let input = BufReader::new(std::fs::File::open(path)?);
    let Some(mode) = args.next() else {
        return export::replay(input, Dialect::Lean4Export31).map(|r| emit(&r));
    };
    let component_json = args
        .next()
        .and_then(|s| s.into_string().ok())
        .ok_or_else(|| Refusal::Malformed("target name must be JSON components".into()))?;
    let name = export::parse_name_json(&component_json)?;
    let target = if mode == "--inspect-target-json" {
        if args.next().is_some() {
            return Err(Refusal::Malformed("extra arguments".into()));
        }
        export::inspect_target(input, Dialect::Lean4Export31, name)?
    } else if mode == "--target-json" {
        if args.next().is_none_or(|s| s != "--statement-sha256") {
            return Err(Refusal::Target("target requires --statement-sha256".into()));
        }
        let statement_sha256 = args
            .next()
            .and_then(|s| s.into_string().ok())
            .ok_or_else(|| Refusal::Target("missing statement pin".into()))?;
        if args.next().is_some() {
            return Err(Refusal::Malformed("extra arguments".into()));
        }
        export::replay_target(
            input,
            Dialect::Lean4Export31,
            TargetRequest {
                name,
                statement_sha256,
            },
        )?
    } else {
        return Err(Refusal::Malformed("unknown mode".into()));
    };
    emit(&target.report);
    println!(
        "{}",
        serde_json::json!({"kind":"target", "name":name_components(&target.name),"statement_sha256":target.statement_sha256,"matched":target.matched,"axioms":target.axioms.iter().map(name_components).collect::<Vec<_>>()})
    );
    // Inspection is exit 0 on a successful inspection, explicitly matched:false.
    Ok(true)
}
fn main() -> std::process::ExitCode {
    match run() {
        Ok(true) => std::process::ExitCode::SUCCESS,
        Ok(false) => std::process::ExitCode::from(1),
        Err(e) => {
            eprintln!(
                "{}",
                serde_json::json!({"kind":"export-refused","reason":e.reason(),"detail":e.to_string()})
            );
            std::process::ExitCode::from(2)
        }
    }
}

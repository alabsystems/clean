// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Feature-gated candidate-advice emitter for an NDJSON export.
//!
//! The bytes come from an independent tracing-core run beside the fenced
//! reference entry. They carry no replay claim; `kcheck` decides them.

use std::error::Error;
use std::ffi::OsStr;
use std::io::{BufReader, Write};
use std::path::PathBuf;

use clean_kernel::kcheck_trace::advice::encode_frames;
use sha2::{Digest, Sha256};

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn main() -> Result<(), Box<dyn Error>> {
    let usage = "usage: kcheck_advice_emit <export.ndjson> --out <advice.bin>";
    let mut args = std::env::args_os().skip(1);
    let export = PathBuf::from(args.next().ok_or(usage)?);
    if args.next().as_deref() != Some(OsStr::new("--out")) {
        return Err(usage.into());
    }
    let output = PathBuf::from(args.next().ok_or(usage)?);
    if args.next().is_some() {
        return Err(usage.into());
    }

    let reader = BufReader::new(std::fs::File::open(&export)?);
    let (frames, count) = clean_olean::ndjson::advice::export_advice_frames(reader)?;
    let non_empty = frames.iter().filter(|frame| !frame.is_empty()).count();
    let bytes = encode_frames(&frames);
    let sha256 = hex(&Sha256::digest(&bytes));
    std::fs::write(output, bytes)?;

    let summary = serde_json::json!({
        "frames": count,
        "non_empty": non_empty,
        "sha256": sha256,
    });
    let stdout = std::io::stdout();
    let mut stdout = stdout.lock();
    serde_json::to_writer(&mut stdout, &summary)?;
    writeln!(stdout)?;
    Ok(())
}

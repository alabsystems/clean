// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Native producer bytes through the actual adopted Lean decoder/checker.
//! This qualifies wire interoperability, not automatic declaration production,
//! compiled checker authority, full C4 coverage or a Rust proof claim.
use clean_kernel::kcheck_trace::wire::{encode_frames, encode_tokens};
use clean_kernel::kcheck_trace::Token;
use clean_olean::test_support::compiled_fixture_dir;
use std::process::Command;

fn lean_bytes(bytes: &[u8]) -> String {
    format!(
        "⟨#[{}]⟩",
        bytes
            .iter()
            .map(u8::to_string)
            .collect::<Vec<_>>()
            .join(",")
    )
}

#[test]
fn native_wire_bytes_replay_and_corruptions_fail_in_adopted_checker() {
    // The existing adopted-checker idNat input is an ordinary definition.
    // Its independently written advice fixture supplies the protocol witness;
    // the real checker below decides acceptance of OUR native output bytes.
    let tokens = [
        Token::Depth(32),
        Token::Stop,
        Token::Stop,
        Token::Stop,
        Token::Stop,
        Token::Refl,
    ];
    let raw = encode_tokens(&tokens);
    let framed = encode_frames(std::slice::from_ref(&raw));
    let mut trailing = raw.clone();
    trailing.push(0);
    let mut no_depth = tokens;
    no_depth[0] = Token::Depth(0);
    let large = encode_tokens(&[Token::Depth(u64::MAX)]);
    let spines = encode_tokens(&[Token::SpineRefl(300), Token::SpineCerts(500)]);
    let source = r#"import KCheck.CheckerCases
open KCheck
open KCheck.CheckerCases

def expect (label : String) (ok : Bool) : IO Unit :=
  if ok then IO.println label else throw (IO.userError label)

def main : IO Unit := do
  let raw : ByteArray := RAW_BYTES
  let framed : ByteArray := FRAME_BYTES
  let trailing : ByteArray := TRAILING_BYTES
  let noDepth : ByteArray := NO_DEPTH_BYTES
  let large : ByteArray := LARGE_BYTES
  let spines : ByteArray := SPINE_BYTES
  expect "ordinary-accepted" (match kcheckBytes base idNat raw with
    | .ok _ => true | .error _ => false)
  expect "framed-run-accepted" (match kcheckRun [idNat] framed with
    | .ok (_, [_]) => true | _ => false)
  expect "trailing-refused" (match kcheckBytes base idNat trailing with
    | .error (.trailingAdvice _) => true | _ => false)
  expect "depth-refused" (match kcheckBytes base idNat noDepth with
    | .error .depth => true | _ => false)
  expect "frame-count-refused" (match kcheckRun [idNat] ByteArray.empty with
    | .error (.frameCount 1 0) => true | _ => false)
  expect "truncated-frame-refused" (match kcheckRun [idNat] ⟨#[128]⟩ with
    | .error (.advice (.truncated _)) => true | _ => false)
  expect "full-u64-decoded" (match decodeAt large 0 with
    | .ok (.depth n, next) => n == 18446744073709551615 && next == large.size
    | _ => false)
  expect "spine-metadata-not-an-operand" (match decodeAt spines 0, decodeAt spines 1 with
    | .ok (.spineRefl, 1), .ok (.spine, 2) => spines.size == 2
    | _, _ => false)
"#
    .replace("RAW_BYTES", &lean_bytes(&raw))
    .replace("FRAME_BYTES", &lean_bytes(&framed))
    .replace("TRAILING_BYTES", &lean_bytes(&trailing))
    .replace("NO_DEPTH_BYTES", &lean_bytes(&encode_tokens(&no_depth)))
    .replace("LARGE_BYTES", &lean_bytes(&large))
    .replace("SPINE_BYTES", &lean_bytes(&spines));
    let scratch = tempfile::tempdir().expect("private advice replay scratch");
    let file = scratch.path().join("ProducerReplay.lean");
    std::fs::write(&file, source).expect("write untrusted producer replay input");
    let compiled = compiled_fixture_dir("kcheck_labelled");
    let lib = clean_olean::require_pinned_lean_lib_path().expect("pinned Lean library");
    let lean = clean_olean::pinned_lean_binary().expect("pinned Lean executable");
    let output = Command::new(lean)
        .args(["--run"])
        .arg(&file)
        .env(
            "LEAN_PATH",
            std::env::join_paths([&compiled, &lib]).expect("Lean search path"),
        )
        .output()
        .expect("execute the adopted checker with native producer bytes");
    assert!(
        output.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8(output.stdout)
            .expect("UTF-8 replay output")
            .lines()
            .collect::<Vec<_>>(),
        [
            "ordinary-accepted",
            "framed-run-accepted",
            "trailing-refused",
            "depth-refused",
            "frame-count-refused",
            "truncated-frame-refused",
            "full-u64-decoded",
            "spine-metadata-not-an-operand",
        ]
    );
}

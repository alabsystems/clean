// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{run_inner, stable_language_prefix, stable_source_text};
use std::io::Write;
use std::process::{Command, Stdio};

#[test]
fn stable_language_header_preserves_the_following_source_coordinates() {
    for header in ["#lang lean4", "#langlean4", "#lang\tlean4 \r"] {
        let source = format!("{header}\n#check Nat\n");
        let prefix = stable_language_prefix(&source).expect("recognized language");
        assert_eq!(&source[prefix..], "\n#check Nat\n");
    }
    assert_eq!(stable_language_prefix("#lang lean4"), Ok(11));
    assert_eq!(stable_language_prefix(" #lang lean4\n"), Ok(0));
    assert_eq!(stable_language_prefix("\u{feff}#lang lean4\n"), Ok(0));
    assert_eq!(stable_language_prefix("#lang lean4md\n"), Err("lean4md"));
    assert_eq!(stable_language_prefix("#lang\x0clean4\n"), Err("\x0clean4"));
}

#[test]
fn stable_utf8_decoder_groups_invalid_bytes_like_lean() {
    let bytes = b"L\xe2\x88\x83N\xed\xa0\x80a\x80\x80\x80b\xff\xffc\xe2\x88";
    assert_eq!(stable_source_text(bytes.to_vec()), "L∃N�a�b��c�");
    assert_eq!(
        stable_source_text(b"\xc2\xa2\x80\x80\xf4\x90\x80\x80z".to_vec()),
        "¢��z"
    );
}

#[test]
fn stable_front_door_decodes_invalid_language_bytes_from_file_and_stdin() {
    const CHILD: &str = "CLEAN_LEAN_STABLE_INPUT_CHILD";
    const INPUT: &[u8] = b"#lang \x80\x80\xff\xff\n";
    if let Ok(form) = std::env::var(CHILD) {
        let argument = match form.as_str() {
            "stdin" => "--stdin",
            "file" => "Input.lean",
            _ => panic!("unrecognized child input form {form}"),
        };
        std::process::exit(run_inner(&[argument.to_owned()]));
    }

    let dir = tempfile::tempdir().expect("isolated stable front door");
    std::fs::write(dir.path().join("Input.lean"), INPUT).expect("raw file input");

    for form in ["stdin", "file"] {
        let mut child = Command::new(std::env::current_exe().expect("test executable"))
            .args([
                "--exact",
                "cmd_lean::stable_input_tests::stable_front_door_decodes_invalid_language_bytes_from_file_and_stdin",
                "--quiet",
            ])
            .env_clear()
            .env(CHILD, form)
            .env("CLEAN_LEAN_VERSION", "v4.36.0")
            .current_dir(dir.path())
            .stdin(if form == "stdin" { Stdio::piped() } else { Stdio::null() })
            .stdout(Stdio::null())
            .stderr(Stdio::piped())
            .spawn()
            .expect("run isolated stable front door");
        if let Some(mut stdin) = child.stdin.take() {
            stdin.write_all(INPUT).expect("raw stdin input");
        }
        let output = child.wait_with_output().expect("stable front-door output");
        assert_eq!(output.status.code(), Some(1), "{form}");
        assert_eq!(
            output.stderr,
            "unknown language '���'\n\n".as_bytes(),
            "{form}"
        );
    }
}

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use clean_kernel::Name;
use clean_olean::import::{stable_imported_parser_tokens, ParserToken};
use std::fs;
use std::path::PathBuf;
use std::process::Command;

#[test]
#[ignore = "requires the official Lean 4.36.0 SDK and CLEAN_LEAN436_BIN"]
fn parser_tokens_follow_the_selected_compiled_import_graph() {
    let lean = PathBuf::from(std::env::var_os("CLEAN_LEAN436_BIN").expect("official Lean 4.36.0"));
    let temp = tempfile::tempdir().unwrap();
    let project = temp.path();
    for (module, source) in [
        (
            "LocalGrammar",
            include_str!("fixtures/lean/v4.36.0/parser_tokens/LocalGrammar.lean"),
        ),
        (
            "PublicWrapper",
            include_str!("fixtures/lean/v4.36.0/parser_tokens/PublicWrapper.lean"),
        ),
        (
            "PrivateWrapper",
            include_str!("fixtures/lean/v4.36.0/parser_tokens/PrivateWrapper.lean"),
        ),
    ] {
        let filename = format!("{module}.lean");
        fs::write(project.join(&filename), source).unwrap();
        let output = Command::new(&lean)
            .current_dir(project)
            .env("LEAN_PATH", project)
            .args(["-o", &format!("{module}.olean"), &filename])
            .output()
            .unwrap();
        assert!(output.status.success(), "{module}: {output:?}");
        fs::remove_file(project.join(filename)).unwrap();
    }
    let roots = [
        project.to_owned(),
        lean.parent().unwrap().parent().unwrap().join("lib/lean"),
    ];
    for (module, legacy, all, visible) in [
        ("PublicWrapper", false, false, true),
        ("PrivateWrapper", false, false, false),
        ("PrivateWrapper", false, true, true),
        ("PrivateWrapper", true, false, true),
    ] {
        let words =
            stable_imported_parser_tokens([(Name::from_string(module), all)], !legacy, &roots)
                .unwrap();
        assert_eq!(
            words.contains(&ParserToken {
                scope: None,
                text: "newWord".into()
            }),
            visible
        );
        assert_eq!(
            words.contains(&ParserToken {
                scope: Some(Name::from_string("Selected")),
                text: "activeWord".into()
            }),
            visible
        );
        assert!(!words.iter().any(|w| w.text == "freeWord"));
    }
    let root = || [(Name::from_string("PrivateWrapper"), true)];
    fs::write(
        project.join("PrivateWrapper.olean.private"),
        b"damaged private part",
    )
    .unwrap();
    assert!(stable_imported_parser_tokens(root(), true, &roots).is_err());
    let path = project.join("PrivateWrapper.olean");
    let mut bytes = fs::read(&path).unwrap();
    let hash = b"611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9";
    let start = bytes
        .windows(hash.len())
        .position(|s| s == hash)
        .expect("released writer identity");
    bytes[start] = b'0';
    fs::write(path, &bytes).unwrap();
    assert!(stable_imported_parser_tokens(
        [(Name::from_string("PrivateWrapper"), false)],
        true,
        &roots
    )
    .is_err());
}

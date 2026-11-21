// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{
    blank_noncode, cfg_test_mod_line_ranges, line_is_inside_cfg_test_mod, production_code_lines,
};

#[test]
fn pinned_cpp_masks_and_raw_offsets_match_incumbent() {
    use super::cpp::CppSource;
    use sha2::{Digest, Sha256};
    use std::path::Path;

    let root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/lean_kernel/v4.30.0-rc2/src/kernel");
    // Incumbent blank_noncode_cpp output encoded as UTF-8.
    let cases = [
        (
            "inductive.cpp",
            "ad74aedc5894597a6be78b769b7ea7f1f039c657a5d4e931109be3837ef4b4b5",
        ),
        (
            "inductive.h",
            "46e3035167000b236c0263ee9452f3d93b4b08b48d7f2719e1cfb3d816b7a33b",
        ),
        (
            "level.cpp",
            "7062ae449ab123791c3dd9a01b56a05249d086be36597fbc821fb8597ddc1fc8",
        ),
        (
            "quot.cpp",
            "4fd8bf5cd1422b6fba083b5af0e242eda0faa07089033eef14dd1f67e03e3c8b",
        ),
        (
            "quot.h",
            "0d43bfe142adc9e7fbca8082d43238752c4f0e45b28f1a3fa16f3fced31bbe1f",
        ),
        (
            "type_checker.cpp",
            "16cee0a30f0c9d110775bda610d9be1a30af3491a84cec80266d740bcf06937e",
        ),
    ];
    for (file, expected) in cases {
        let raw = std::fs::read_to_string(root.join(file)).unwrap();
        let source = CppSource::new(&raw);
        let masked = source.masked();
        let digest: String = Sha256::digest(masked)
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect();
        assert_eq!(digest, expected, "{file}");
        assert_eq!(masked.chars().count(), raw.chars().count(), "{file}");
        for ((start, masked_char), (raw_start, raw_char)) in
            masked.char_indices().zip(raw.char_indices())
        {
            let range = start..start + masked_char.len_utf8();
            let expected = &raw[raw_start..raw_start + raw_char.len_utf8()];
            assert_eq!(source.raw_slice(range), Some(expected), "{file}:{start}");
        }
    }
}

#[test]
fn pinned_cpp_functions_and_coverage_inputs_match_incumbent() {
    use super::cpp::CppSource;
    use sha2::{Digest, Sha256};
    use std::{collections::BTreeMap, fmt::Write, path::Path};

    let root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/lean_kernel/v4.30.0-rc2/src/kernel");
    // Each incumbent row is name, start, end and raw digest separated by tabs.
    let cases = [
        (
            "inductive.cpp",
            69,
            "00f10f654de86bd5741c250aa0355ce8963373f0c6e93383f50d68533e333b62",
        ),
        (
            "inductive.h",
            4,
            "9ed7620bcaf1326ad7c30587dde41a3869af535bb9382fc40a16beb03f2b4d3e",
        ),
        (
            "level.cpp",
            51,
            "11b5ed006aaeae188c62eabeb339bbbe9a5b99b6454a80632939d3f6e22fbe8a",
        ),
        (
            "quot.cpp",
            4,
            "2e3343f5fc38e3a87de8a173632d9a02a2f56074ea5102248e7127596760722c",
        ),
        (
            "quot.h",
            4,
            "9cd33fa1ea59d1e0e09d40f66a03e34ef57fb34bef57581b316b2d28839695d5",
        ),
        (
            "type_checker.cpp",
            67,
            "bde491e366820c23928af45348cb1b0ba8050d67e145b28e1da0ec705f80494c",
        ),
    ];
    let sources: BTreeMap<_, _> = cases
        .iter()
        .map(|&(file, _, _)| (file, std::fs::read_to_string(root.join(file)).unwrap()))
        .collect();
    let scans: BTreeMap<_, _> = sources
        .iter()
        .map(|(&file, raw)| (file, CppSource::new(raw)))
        .collect();
    let local_names: BTreeMap<_, _> = scans
        .iter()
        .map(|(&file, source)| (file, source.global_constant_names()))
        .collect();
    // The mapping's file order determines which shared name wins.
    let shared_names = [
        "type_checker.cpp",
        "inductive.cpp",
        "inductive.h",
        "quot.cpp",
        "quot.h",
        "level.cpp",
    ]
    .into_iter()
    .flat_map(|file| local_names[file].clone())
    .collect();
    let mut coverage = Vec::new();
    let mut constants = Vec::new();
    let mut arm_count = 0;
    let mut code_line_count = 0;
    let mut constant_count = 0;
    for (file, count, expected) in cases {
        let source = &scans[file];
        let functions = source
            .functions_with_constant_names(&local_names[file], &shared_names)
            .unwrap_or_else(|error| panic!("{file}: {error}"));
        assert_eq!(functions.len(), count, "{file}");
        let mut roster = String::new();
        let mut file_coverage = Vec::new();
        let mut file_constants = Vec::new();
        for function in functions {
            let [start, end] = function.lines;
            let bytes = source.raw_lines(start, end).unwrap();
            let digest = test_sha256(bytes);
            writeln!(roster, "{}\t{start}\t{end}\t{digest}", function.name).unwrap();
            assert!(
                source
                    .raw_slice(function.masked_bytes)
                    .unwrap()
                    .ends_with('}'),
                "{file}:{}",
                function.name
            );
            let arms: Vec<_> = function
                .case_arms
                .iter()
                .map(|arm| (&arm.name, arm.line))
                .collect();
            arm_count += arms.len();
            code_line_count += function.code_lines.len();
            constant_count += function.hardcoded_constants.len();
            file_coverage.push(serde_json::json!([
                function.name,
                arms,
                function.code_lines
            ]));
            let uses: Vec<_> = function
                .hardcoded_constants
                .iter()
                .map(|usage| (usage.line, &usage.constant))
                .collect();
            file_constants.push(serde_json::json!([function.name, uses]));
        }
        assert_eq!(test_sha256(&roster), expected, "{file}");
        coverage.push(serde_json::json!([
            format!("src/kernel/{file}"),
            file_coverage
        ]));
        constants.push(serde_json::json!([
            format!("src/kernel/{file}"),
            file_constants
        ]));
    }
    assert_eq!((arm_count, code_line_count), (76, 2633));
    assert_eq!(
        test_sha256(&serde_json::to_string(&coverage).unwrap()),
        "f871aea3d43d66a601b9a61d8d73bb542e5a57ec84488f24da89a30067dc8aa7"
    );
    assert_eq!(constant_count, 60);
    assert_eq!(
        test_sha256(&serde_json::to_string(&constants).unwrap()),
        "e51e21a5f5b4a0b5a98327a7bc5c1730985d79a90c362874f1e9b035b6092f14"
    );

    fn test_sha256(text: &str) -> String {
        Sha256::digest(text)
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect()
    }
}

#[test]
fn test_production_code_lines_out_of_line_and_same_line_test_items_kept() {
    let source = "#[cfg(test)]\nmod tests;\nfn out_of_line() { work(); }\n\
                  #[cfg(test)] use test_helper;\nmod ordinary { fn inner() { work(); } }\n\
                  #[cfg(test)] mod inline {} fn after_close() { work(); }\n";
    let calls: Vec<_> = production_code_lines(source)
        .into_iter()
        .filter_map(|(line, code)| code.contains("work()").then_some(line))
        .collect();
    assert_eq!(calls, [3, 5, 6]);
}

#[test]
fn test_cfg_test_mod_line_ranges_conditional_import_before_module_resumes_after_it() {
    let content = r#"#[cfg(test)]
use super::helper;

fn before() {
    metas.assign();
}

#[cfg(test)]
mod tests {
    fn helper() {
        metas.assign();
    }
}

fn after() {
    metas.assign();
}
"#;

    let ranges = cfg_test_mod_line_ranges(&blank_noncode(content));

    assert_eq!(ranges, vec![7..=12]);
    assert!(
        !line_is_inside_cfg_test_mod(&ranges, 1),
        "conditional imports are not inline test modules"
    );
    assert!(
        !line_is_inside_cfg_test_mod(&ranges, 4),
        "production code before the test module must still count"
    );
    assert!(
        line_is_inside_cfg_test_mod(&ranges, 10),
        "code inside the inline test module must be excluded"
    );
    assert!(
        !line_is_inside_cfg_test_mod(&ranges, 15),
        "production code after the test module must still count"
    );
}

#[test]
fn test_blank_noncode_comments_strings_and_char_literals_erased() {
    let src = r###"// metas.assign(hidden)
/* block metas.assign(hidden) */
/** doc metas.assign(hidden) */
let s = "metas.assign(hidden)";
let r = r#"metas.assign(hidden)"#;
let c = '"';
state.metas.assign(goal, proof); // trailing metas.assign(hidden)
"###;
    let blanked = blank_noncode(src);
    assert_eq!(
        blanked.matches("metas.assign(").count(),
        1,
        "only the real call survives blanking; got:\n{blanked}"
    );
    assert_eq!(
        blanked.lines().count(),
        src.lines().count(),
        "blanking must preserve line geometry"
    );
}

#[test]
fn test_blank_noncode_nested_comment_and_lifetimes_comment_erased_lifetimes_kept() {
    let src = "/* outer /* inner metas.assign( */ still comment */ fn f<'a>(x: &'a str) {}\n";
    let blanked = blank_noncode(src);
    assert_eq!(blanked.matches("metas.assign(").count(), 0);
    assert!(
        blanked.contains("fn f<'a>(x: &'a str)"),
        "lifetimes are not char literals; got: {blanked}"
    );
}

/// Lane LOOSE, 2026-08-25: `'\''` must be blanked WHOLE.
///
/// The original escape branch scanned forward to the next `'`, which is the
/// ESCAPED quote — so it stopped one byte early and left the real closing quote
/// behind as stray code. A stray quote can open a spurious char literal further
/// along the line and blank real code after it (a FAIL-OPEN direction).
#[test]
fn test_blank_noncode_escaped_char_literals_blanked_whole() {
    let src = "let c = '\\'';\nlet n = '\\n';\nlet u = '\\u{1F600}';\nfoo.bar();\n";
    let blanked = blank_noncode(src);

    assert!(
        !blanked.contains('\''),
        "no quote may survive an escaped char literal: {blanked:?}"
    );
    assert_eq!(
        blanked.lines().count(),
        src.lines().count(),
        "line geometry must survive"
    );
    assert!(
        blanked.contains("foo.bar();"),
        "real code after the literals must survive: {blanked:?}"
    );
}

/// Lane LOOSE, 2026-08-25: a brace inside a string literal or a block comment
/// must not move the end of a `#[cfg(test)] mod` block.
///
/// This is the FAIL-OPEN half of the raw-text defect: the tracker used to count
/// every `{`/`}` outside a `//` comment, so an unbalanced brace in a string
/// swallowed the production code after the test module (or ended the module
/// early). Both directions are wrong; only one of them is silent.
#[test]
fn test_cfg_test_mod_line_ranges_braces_in_literals_and_comments_ignored() {
    let content = r####"#[cfg(test)]
mod tests {
    fn helper() {
        let brace = "an unbalanced { in a string";
        /* and a } in a block comment */
    }
}

fn production_after() {
    metas.assign();
}
"####;

    let ranges = cfg_test_mod_line_ranges(&blank_noncode(content));

    assert_eq!(
        ranges,
        vec![0..=6],
        "the test module must end at its real closing brace"
    );
    assert!(
        !line_is_inside_cfg_test_mod(&ranges, 9),
        "production code after the module must not be swallowed by a brace \
         that lives inside a string literal"
    );

    let production: Vec<usize> = production_code_lines(content)
        .into_iter()
        .filter(|(_, code)| code.contains("metas.assign("))
        .map(|(n, _)| n)
        .collect();
    assert_eq!(
        production,
        vec![10],
        "the real production call must still be counted"
    );
}

// Arms moved with the implementation from clean-elab's and clean-auto's
// test-support copies (design unit EV0, 2026-11-17), so the one scanner keeps
// every arm either copy carried.

#[test]
fn test_cfg_test_mod_line_ranges_pub_in_use_and_pub_in_mod_only_mod_excluded() {
    let content = r#"#[cfg(test)]
pub(in crate::tests) use super::helper;

fn before() {
    metas.assign();
}

#[cfg(test)]
pub(in crate::tests) mod tests {
    fn helper() {
        metas.assign();
    }
}

fn after() {
    metas.assign();
}
"#;

    let ranges = cfg_test_mod_line_ranges(content);

    assert_eq!(ranges, vec![7..=12]);
    assert!(
        !line_is_inside_cfg_test_mod(&ranges, 1),
        "conditional pub(in ...) imports are not inline test modules"
    );
    assert!(
        !line_is_inside_cfg_test_mod(&ranges, 4),
        "production code before a pub(in ...) test module must still count"
    );
    assert!(
        line_is_inside_cfg_test_mod(&ranges, 9),
        "pub(in ...) mod tests blocks must still be excluded"
    );
    assert!(
        !line_is_inside_cfg_test_mod(&ranges, 15),
        "production code after the test module must still count"
    );
}

#[test]
fn test_cfg_test_mod_line_ranges_comment_preamble_before_module_module_excluded() {
    let content = r#"#[cfg(test)]
// Helper note for the test-only module.
/// Extra docs before the item.
#[allow(dead_code)]
mod tests {
    fn helper() {
        metas.assign();
    }
}

fn after_tests() {
    metas.assign();
}
"#;

    let ranges = cfg_test_mod_line_ranges(content);

    assert_eq!(ranges, vec![0..=8]);
    assert!(
        line_is_inside_cfg_test_mod(&ranges, 6),
        "lines inside comment-preamble cfg(test) modules must be excluded"
    );
    assert!(
        !line_is_inside_cfg_test_mod(&ranges, 11),
        "production code after the test module must still count"
    );
}

#[test]
fn test_production_code_lines_cfg_test_body_dropped_line_numbers_kept() {
    let src = "fn before() {\n    metas.assign();\n}\n\n#[cfg(test)]\nmod tests {\n    fn t() { metas.assign(); }\n}\n\nfn after() {\n    metas.assign();\n}\n";
    let hits: Vec<usize> = production_code_lines(src)
        .into_iter()
        .filter(|(_, code)| code.contains("metas.assign("))
        .map(|(n, _)| n)
        .collect();
    assert_eq!(
        hits,
        vec![2, 11],
        "cfg(test) body excluded, 1-indexed lines kept"
    );
}

/// DIRECTION 2 of the clean-auto copy's arms: real code survives after a
/// string that contains `//` -- the case `split("//")` truncated away.
#[test]
fn test_blank_noncode_string_containing_slashes_code_after_kept() {
    let src = "let u = \"https://example.invalid\"; forbidden(x);\n";
    let blanked = blank_noncode(src);
    assert!(
        blanked.contains("forbidden(x);"),
        "a real call after a string containing `//` must survive: {blanked:?}"
    );
    assert!(
        !blanked.contains("https"),
        "the string body must be blanked"
    );
}

/// The public range function blanks raw text itself, so a caller that passes
/// unblanked source cannot let a brace in a string end the module early.
#[test]
fn test_cfg_test_mod_line_ranges_raw_input_matches_preblanked() {
    let content =
        "#[cfg(test)]\nmod tests {\n    const S: &str = \"}\";\n    fn t() {}\n}\nfn prod() {}\n";
    assert_eq!(cfg_test_mod_line_ranges(content), vec![0..=4]);
    assert_eq!(
        cfg_test_mod_line_ranges(content),
        cfg_test_mod_line_ranges(&blank_noncode(content)),
        "blanking is idempotent, so raw and pre-blanked input agree"
    );
}

// EV0 review arms (2026-11-17). Each spelling below hid production code from
// `production_code_lines` before the fix; each arm is the review's probe.

/// The 1-indexed production lines that call `unwrap`.
fn unwrap_lines(source: &str) -> Vec<usize> {
    production_code_lines(source)
        .into_iter()
        .filter_map(|(line, code)| code.contains("unwrap()").then_some(line))
        .collect()
}

#[test]
fn test_blank_noncode_c_raw_string_literal_code_after_kept() {
    let source = "let s = cr#\"a\\\"#; x.unwrap();\nfn p() { y.unwrap(); }\n";
    assert_eq!(unwrap_lines(source), [1, 2]);
    let plain = "let s = cr\"a\\\"; x.unwrap();\nfn p() { y.unwrap(); }\n";
    assert_eq!(unwrap_lines(plain), [1, 2]);
    let blanked = blank_noncode(source);
    assert!(
        !blanked.contains("a\\"),
        "the raw body is blanked: {blanked:?}"
    );
}

/// Negative control: `cr` ending an identifier is no raw-string prefix, so
/// the ordinary string after it (which an escaped quote does not end) is
/// blanked whole, code-shaped text inside it included.
#[test]
fn test_blank_noncode_identifier_ending_in_cr_string_after_blanked() {
    let source = "let v = xcr\"\\\"; hidden.unwrap(); \";\nfn p() { y.unwrap(); }\n";
    assert_eq!(unwrap_lines(source), [2]);
    let lifetime = "m!('r\"\\\"; hidden.unwrap(); \");\nfn p() { y.unwrap(); }\n";
    assert_eq!(unwrap_lines(lifetime), [2]);
}

#[test]
fn test_blank_noncode_non_ascii_and_hex_char_literals_blanked_whole() {
    for source in [
        "let c = 'é'; x.unwrap();\n",
        "let q = '\\x22'; x.unwrap();\n",
    ] {
        let blanked = blank_noncode(source);
        assert!(!blanked.contains('\''), "literal left behind: {blanked:?}");
        assert!(blanked.contains("x.unwrap();"), "code lost: {blanked:?}");
        assert_eq!(blanked.len(), source.len(), "byte length preserved");
    }
    let mixed = "['é','\"']; x.unwrap();\nfn prod() { y.unwrap(); }\n";
    assert_eq!(unwrap_lines(mixed), [1, 2]);
}

#[test]
fn test_blank_noncode_non_ascii_code_copied_unchanged() {
    let source = "let café = \"é\"; // ü\nlet ß = 1;\n";
    let blanked = blank_noncode(source);
    // `"é"` is four bytes and ` // ü` six, each blanked byte for byte.
    let expected = format!(
        "let café = {};{}\nlet ß = 1;\n",
        " ".repeat(4),
        " ".repeat(6)
    );
    assert_eq!(blanked, expected);
    assert_eq!(blanked.len(), source.len());
}

#[test]
fn test_cfg_test_mod_line_ranges_attribute_with_item_below_cfg_test_not_skipped() {
    let source = "#[cfg(test)]\n#[cfg(test)] fn helper() {}\nmod real { fn f() { x.unwrap(); } }\n";
    assert_eq!(unwrap_lines(source), [3]);
    let unclosed =
        "#[cfg(test)]\n#[cfg(all(test,\n    unix))]\nmod real { fn f() { x.unwrap(); } }\n";
    assert_eq!(unwrap_lines(unclosed), [4]);
    let stacked =
        "#[cfg(test)]\n#[allow(dead_code)] #[allow(unused)]\nmod t { fn f() { x.unwrap(); } }\n";
    assert!(
        unwrap_lines(stacked).is_empty(),
        "attributes alone still lead to the module"
    );
}

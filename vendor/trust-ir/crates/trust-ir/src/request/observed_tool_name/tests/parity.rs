// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
#[test]
fn every_family_exact_and_suffix_alias_matches_the_actual_original_transform() {
    for root in [
        "trustvc", "trust-vc", "TRUST_VC", "trustmc", "trust-mc", "TRUST_MC", "trustwp",
        "trust-wp", "TRUST_WP", "trustir", "trust-ir", "TRUST_IR",
    ] {
        for suffix in ["", "-native", "...native-2", "_MIR-v51"] {
            observed(&(root.to_owned() + suffix));
        }
    }
}
#[test]
fn ascii_boundary_separator_case_and_digit_bytes_all_keep_the_original_result() {
    for byte in 0u8..=127 {
        let c = char::from(byte);
        for s in [
            format!("{c}TrustMc{c}"),
            format!("a{c}B0{c}9"),
            format!("{c}{c}{c}"),
        ] {
            observed(&s);
        }
    }
}
#[test]
fn leading_and_trailing_unicode_whitespace_trim_elision_is_exact() {
    for white in [
        ' ', '\t', '\n', '\r', '\u{85}', '\u{a0}', '\u{1680}', '\u{2000}', '\u{200a}', '\u{2028}',
        '\u{2029}', '\u{202f}', '\u{205f}', '\u{3000}',
    ] {
        for s in [
            format!("{white}TrustMC{white}"),
            format!("{white}A{white}B{white}"),
            format!("{white}{white}"),
        ] {
            observed(&s);
        }
    }
}
#[test]
fn multibyte_nonwhite_punctuation_bytes_preserve_separator_semantics() {
    for s in [
        "工具TrustMC🦀NATIVE世界",
        "AéB",
        "a\u{200b}b",
        "é",
        "🦀",
        "a\0b",
        "\u{10ffff}TRUST_IR\u{7f}",
    ] {
        observed(s);
    }
}
#[test]
fn empty_separator_only_and_whitespace_only_inputs_do_not_create_names() {
    for s in ["", "-", " _--.!", "\0\0", " \t\u{2003} ", "🦀--"] {
        assert_eq!(observed(s).0, "");
    }
}
#[test]
fn unknown_family_prefixes_and_near_misses_are_not_relabelled() {
    for s in [
        "trustvca",
        "trust-mcbar",
        "itrustwp",
        "trust-irregular",
        "trust-v",
        "trustmc2",
        "trusted",
    ] {
        observed(s);
    }
}
#[test]
fn arbitrarily_long_retained_suffix_is_complete_and_no_byte_is_truncated() {
    let s = "TRUSTMC-".to_owned() + &"x09".repeat(5000);
    let (out, _, _) = observed(&s);
    assert_eq!(out, "trust_mc-".to_owned() + &"x09".repeat(5000));
}
#[test]
fn inherent_tool_identity_api_returns_the_same_data_after_source_disposal() {
    let t = NativeToolIdentity::new(" tRust_MC.NaTiVe ");
    let expected = t.canonical_name();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = t.canonical_name_observed(&mut s, site()).unwrap();
    drop(t);
    assert_eq!(out, expected);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    w.text_drop(out);
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean lean FILE`: Lean's messages and Lean's exit status, byte for byte.
//!
//! Every expected byte string below is what pinned Lean printed for the same
//! file and arguments (`bin/lean` of the named release, 2026-10-16). The
//! policy differences from `clean check` are the point: a file of commands and
//! no declaration, and an explicit `sorry`, exit 0 here.

#![cfg(unix)]

#[path = "support/lean_front_door.rs"]
mod front_door;

use front_door::{
    assert_run, fixtures, lean, lean_with_stdin, scratch, stderr, stdout, write, V4_30_0_RC2,
    V4_8_0,
};

const SUITE_ARGS: [&str; 3] = [
    "--root=..",
    "-DprintMessageEndPos=true",
    "-Dlinter.all=false",
];

fn fixture(release: &str, name: &str) -> std::process::Output {
    let mut args: Vec<&str> = SUITE_ARGS.to_vec();
    args.push(name);
    lean(&fixtures(), release, &args)
}

#[test]
fn test_accepted_file_prints_nothing_and_exits_zero() {
    for release in [V4_8_0, V4_30_0_RC2] {
        assert_run(&fixture(release, "accept_silent.lean"), 0, "", "");
    }
}

#[test]
fn test_file_of_commands_prints_their_output_and_exits_zero() {
    // `clean check` refuses this file (no declaration); `lean` does not.
    for release in [V4_8_0, V4_30_0_RC2] {
        assert_run(
            &fixture(release, "commands.lean"),
            0,
            "Nat : Type\n1 : Nat\n2\n\"hi\"\n",
            "",
        );
    }
}

#[test]
fn test_explicit_sorry_is_a_warning_on_the_name_and_exits_zero() {
    assert_run(
        &fixture(V4_8_0, "sorry_warning.lean"),
        0,
        "sorry_warning.lean:2:8-2:9: warning: declaration uses 'sorry'\n\
         sorry_warning.lean:4:0-4:7: warning: declaration uses 'sorry'\n\
         sorry_warning.lean:7:4-7:5: warning: declaration uses 'sorry'\n",
        "",
    );
    assert_run(
        &fixture(V4_30_0_RC2, "sorry_warning.lean"),
        0,
        "sorry_warning.lean:2:8-2:9: warning: declaration uses `sorry`\n\
         sorry_warning.lean:4:0-4:7: warning: declaration uses `sorry`\n\
         sorry_warning.lean:7:4-7:5: warning: declaration uses `sorry`\n",
        "",
    );
}

#[test]
fn test_block_members_log_in_source_order() {
    assert_run(
        &fixture(V4_8_0, "namespace_order.lean"),
        0,
        "1\nnamespace_order.lean:4:8-4:9: warning: declaration uses 'sorry'\n3\n",
        "",
    );
}

#[test]
fn test_declaration_then_commands_known_signature_gap() {
    // KNOWN GAP G80, pinned so it fails the day it closes: pinned Lean prints
    // `#check double` as the signature `double (n : Nat) : Nat`, and Clean's
    // kernel term carries no binder names, so Clean prints the type (in Lean's
    // `→`). Everything else on the stream, and the exit status, is Lean's.
    const LEAN: &str = "double (n : Nat) : Nat\n42\n'double' does not depend on any axioms\n";
    for release in [V4_8_0, V4_30_0_RC2] {
        let run = fixture(release, "declared_then_checked.lean");
        assert_run(
            &run,
            0,
            "double : Nat → Nat\n42\n'double' does not depend on any axioms\n",
            "",
        );
        assert_ne!(
            stdout(&run),
            LEAN,
            "G80 closed: assert Lean's bytes here instead"
        );
    }
}

#[test]
fn test_matched_guard_msgs_is_silent() {
    for release in [V4_8_0, V4_30_0_RC2] {
        assert_run(&fixture(release, "guard_msgs_match.lean"), 0, "", "");
    }
}

#[test]
fn test_error_exits_one_with_the_file_position_prefix() {
    let run = fixture(V4_8_0, "type_error.lean");
    assert_eq!(run.status.code(), Some(1), "{}", stdout(&run));
    assert!(
        stdout(&run).starts_with("type_error.lean:1:") && stdout(&run).contains(": error: "),
        "{}",
        stdout(&run)
    );
    assert_eq!(stderr(&run), "");
}

#[test]
fn test_json_is_one_object_per_line_in_each_releases_shape() {
    let dir = scratch("json");
    write(&dir, "a.lean", "#eval 1 + 1\ntheorem t : 1 = 1 := sorry\n");
    assert_run(
        &lean(&dir, V4_8_0, &["--json", "a.lean"]),
        0,
        "{\"severity\":\"information\",\"pos\":{\"line\":1,\"column\":0},\"keepFullRange\":false,\
         \"fileName\":\"a.lean\",\"endPos\":{\"line\":1,\"column\":5},\"data\":\"2\\n\",\
         \"caption\":\"\"}\n\
         {\"severity\":\"warning\",\"pos\":{\"line\":2,\"column\":8},\"keepFullRange\":false,\
         \"fileName\":\"a.lean\",\"endPos\":{\"line\":2,\"column\":9},\"data\":\"declaration uses \
         'sorry'\",\"caption\":\"\"}\n",
        "",
    );
    assert_run(
        &lean(&dir, V4_30_0_RC2, &["--json", "a.lean"]),
        0,
        "{\"caption\":\"\",\"data\":\"2\",\"endPos\":{\"column\":5,\"line\":1},\"fileName\":\
         \"a.lean\",\"isSilent\":false,\"keepFullRange\":false,\"kind\":\"[anonymous]\",\"pos\":\
         {\"column\":0,\"line\":1},\"severity\":\"information\"}\n\
         {\"caption\":\"\",\"data\":\"declaration uses `sorry`\",\"endPos\":{\"column\":9,\"line\"\
         :2},\"fileName\":\"a.lean\",\"isSilent\":false,\"keepFullRange\":false,\"kind\":\
         \"hasSorry\",\"pos\":{\"column\":8,\"line\":2},\"severity\":\"warning\"}\n",
        "",
    );
}

#[test]
fn test_error_kind_prints_as_error_but_keeps_the_exit_status() {
    // Measured: pinned 4.30.0-rc2 `lean -E hasSorry` prints `error:` and exits 0.
    let dir = scratch("error-kind");
    write(&dir, "s.lean", "theorem t : True := sorry\n");
    assert_run(
        &lean(&dir, V4_30_0_RC2, &["-E", "hasSorry", "s.lean"]),
        0,
        "s.lean:1:8: error: declaration uses `sorry`\n",
        "",
    );
    // 4.8.0 has no `-E`.
    assert_eq!(
        lean(&dir, V4_8_0, &["-E", "hasSorry", "s.lean"])
            .status
            .code(),
        Some(1)
    );
}

#[test]
fn test_stdin_messages_name_stdin() {
    let dir = scratch("stdin");
    assert_run(
        &lean_with_stdin(
            &dir,
            V4_8_0,
            &["--stdin"],
            Some("#check Nat\ntheorem t : 1 = 1 := sorry\n"),
        ),
        0,
        "Nat : Type\n<stdin>:2:8: warning: declaration uses 'sorry'\n",
        "",
    );
}

#[test]
fn test_quiet_changes_nothing_clean_prints() {
    for release in [V4_8_0, V4_30_0_RC2] {
        let mut args: Vec<&str> = SUITE_ARGS.to_vec();
        args.extend(["-q", "commands.lean"]);
        assert_run(
            &lean(&fixtures(), release, &args),
            0,
            "Nat : Type\n1 : Nat\n2\n\"hi\"\n",
            "",
        );
    }
}

#[test]
fn test_where_auxiliary_sorry_is_warned_at_its_own_name() {
    // Measured: pinned Lean 4.8.0 warns at the auxiliary `bar` (3:2), not at
    // `foo`, whose own value has no `sorry`.
    let dir = scratch("where-aux");
    write(
        &dir,
        "aux.lean",
        "def foo : Unit := ()\nwhere\n  bar : Nat := sorry\n\ndef after : Nat := 1\n",
    );
    assert_run(
        &lean(&dir, V4_8_0, &["aux.lean"]),
        0,
        "aux.lean:3:2: warning: declaration uses 'sorry'\n",
        "",
    );
}

/// Lean's list after `private` in command position (pinned 4.30.0-rc2).
const AFTER_PRIVATE: &str = "'abbrev', 'axiom', 'builtin_initialize', 'class', 'coinductive', \
    'def', 'example', 'inductive', 'initialize', 'instance', 'opaque', 'structure', 'syntax' or \
    'theorem'";

/// Lean's list after a lone `public` in command position (pinned 4.30.0-rc2).
const AFTER_PUBLIC: &str = "'abbrev', 'axiom', 'builtin_initialize', 'class', 'coinductive', \
    'def', 'example', 'inductive', 'initialize', 'instance', 'opaque', 'section', 'structure', \
    'syntax' or 'theorem'";

/// Lean's list after a lone declaration doc comment in command position
/// (pinned 4.30.0-rc2).
const AFTER_DOC: &str = "'#guard_msgs', 'abbrev', 'add_decl_doc', 'axiom', 'binder_predicate', \
    'builtin_cbv_simproc', 'builtin_cbv_simproc_decl', 'builtin_dsimproc', \
    'builtin_dsimproc_decl', 'builtin_grind_propagator', 'builtin_initialize', \
    'builtin_simproc', 'builtin_simproc_decl', 'cbv_simproc', 'cbv_simproc_decl', 'class', \
    'coinductive', 'declare_simp_like_tactic', 'declare_syntax_cat', 'def', 'dsimproc', \
    'dsimproc_decl', 'elab', 'elab_rules', 'example', 'grind_propagator', 'inductive', 'infix', \
    'infixl', 'infixr', 'initialize', 'instance', 'macro', 'macro_rules', 'notation', 'opaque', \
    'postfix', 'prefix', 'recommended_spelling', 'register_error_explanation', \
    'register_tactic_tag', 'register_try?_tactic', 'simproc', 'simproc_decl', 'structure', \
    'syntax', 'tactic_extension', 'theorem' or 'unif_hint'";

#[test]
fn test_module_syntax_refusal_prints_leans_message_at_its_position() {
    // A module-system spelling pinned Lean refuses (plan item
    // `formats-module-spelling-refusals`) is printed at Lean's position in
    // Lean's words, the bytes pinned 4.30.0-rc2 printed for each file
    // (2026-10-28). It used to be printed at the end of the file, as
    // `f.lean:4:0: error: Clean's parser cannot read this file: 1:7: error: …`.
    let dir = scratch("module-syntax");
    write(&dir, "f.lean", "private section\ndef x : Nat := 1\nend\n");
    write(&dir, "g.lean", "public import Init\n\ndef x : Nat := 1\n");
    write(&dir, "h.lean", "module\nimport /-! d -/ Init\n");
    assert_run(
        &lean(&dir, V4_30_0_RC2, &["f.lean"]),
        1,
        &format!("f.lean:1:7: error: unexpected token 'section'; expected {AFTER_PRIVATE}\n"),
        "",
    );
    assert_run(
        &lean(&dir, V4_30_0_RC2, &["g.lean"]),
        1,
        "g.lean:1:0: error: cannot use `public import` without `module`\n",
        "",
    );
    assert_run(
        &lean(&dir, V4_30_0_RC2, &["h.lean"]),
        1,
        "h.lean:2:6: error: unexpected token '/-!'; expected identifier\n",
        "",
    );
}

#[test]
fn test_module_syntax_refusal_end_position_known_gap() {
    // KNOWN GAP, pinned so it fails the day it closes: a module-system
    // refusal carries no end position, so its end is its start. Pinned
    // 4.30.0-rc2 ends it at the end of the unexpected token (`1:7-1:15`, the
    // `section`), and its `--json` object carries that `endPos` and
    // `"keepFullRange":true` (measured 2026-10-28). The default stream, which
    // prints no end, is Lean's (above).
    let dir = scratch("module-syntax-end");
    write(&dir, "f.lean", "private section\ndef x : Nat := 1\nend\n");
    let run = lean(&dir, V4_30_0_RC2, &["-DprintMessageEndPos=true", "f.lean"]);
    let tail = format!(": error: unexpected token 'section'; expected {AFTER_PRIVATE}\n");
    assert_run(&run, 1, &format!("f.lean:1:7-1:7{tail}"), "");
    assert_ne!(
        stdout(&run),
        format!("f.lean:1:7-1:15{tail}"),
        "the end position is Lean's: assert Lean's bytes here instead"
    );
}

#[test]
fn test_module_syntax_refusal_under_4_8_0_keeps_cleans_prefix() {
    // Every parse is at the v4.30.0-rc2 world, so a module-system refusal
    // carries 4.30.0-rc2's words, which Lean 4.8.0 never prints. Under 4.8.0
    // the message keeps Clean's prefix, at the carried position; it used to
    // be printed bare, as if it were 4.8.0's own. What pinned 4.8.0 prints
    // for the same three files (measured 2026-10-28):
    //   f.lean:1:7: error: unexpected token 'section'; expected 'abbrev',
    //     'axiom', 'builtin_initialize', 'class', 'def', 'example',
    //     'inductive', 'initialize', 'instance', 'opaque', 'structure' or
    //     'theorem'
    //   g.lean:1:0: error: unexpected identifier; expected command
    //   g.lean:1:7: error: invalid 'import' command, it must be used in the
    //     beginning of the file
    //   h.lean:1:0: error: unexpected identifier; expected command
    //   h.lean:2:0: error: invalid 'import' command, it must be used in the
    //     beginning of the file
    const PREFIX: &str = "error: Clean's parser cannot read this file:";
    let dir = scratch("module-syntax-4-8-0");
    write(&dir, "f.lean", "private section\ndef x : Nat := 1\nend\n");
    write(&dir, "g.lean", "public import Init\n\ndef x : Nat := 1\n");
    write(&dir, "h.lean", "module\nimport /-! d -/ Init\n");
    assert_run(
        &lean(&dir, V4_8_0, &["f.lean"]),
        1,
        &format!(
            "f.lean:1:7: {PREFIX} 1:7: error: unexpected token 'section'; expected \
             {AFTER_PRIVATE}\n"
        ),
        "",
    );
    assert_run(
        &lean(&dir, V4_8_0, &["g.lean"]),
        1,
        &format!("g.lean:1:0: {PREFIX} 1:0: error: cannot use `public import` without `module`\n"),
        "",
    );
    assert_run(
        &lean(&dir, V4_8_0, &["h.lean"]),
        1,
        &format!("h.lean:2:6: {PREFIX} 2:6: error: unexpected token '/-!'; expected identifier\n"),
        "",
    );
}

#[test]
fn test_module_syntax_refusal_prints_only_the_first_message_known_gap() {
    // KNOWN GAP, pinned so it fails the day it closes: a module-system
    // refusal is one message, Lean's first. Pinned 4.30.0-rc2 prints three on
    // this file (measured 2026-10-28), and Clean prints the first alone.
    let dir = scratch("module-syntax-messages");
    write(
        &dir,
        "m.lean",
        "module\npublic /-- d -/ import Init\n\ndef x : Nat := 1\n",
    );
    let first = format!("m.lean:2:6: error: unexpected token '/--'; expected {AFTER_PUBLIC}\n");
    let lean_prints = format!(
        "{first}m.lean:2:15: error: unexpected token 'import'; expected {AFTER_DOC}\n\
         m.lean:2:16: error: invalid 'import' command, it must be used in the beginning of the \
         file\n"
    );
    let run = lean(&dir, V4_30_0_RC2, &["m.lean"]);
    assert_run(&run, 1, &first, "");
    assert_ne!(
        stdout(&run),
        lean_prints,
        "every message is Lean's: assert Lean's bytes here instead"
    );
}

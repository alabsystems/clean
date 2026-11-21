// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! What the native path compiles for `@[implemented_by]` and `@[extern]`
//! (`compiler-implemented-by-and-extern-fail-closed`,
//! docs/plans/LEAN4_UPSTREAM_DELTA_2026-10-16.md), through the production
//! entry `clean compile`/`clean run` share ([`select_lcnf_decl`]).
//!
//! Lean never compiles the body of an `@[implemented_by f]` declaration: every
//! call runs `f` (pinned Lean v4.30.0-rc2 prints `2` for `slow 1` below, where
//! the logical body gives `3`). Lean never compiles the body of an `@[extern]`
//! declaration either: `lean --run` fails with "Could not find native
//! implementation of external declaration". Clean compiled both bodies and
//! printed the logical answer at exit 0.

use super::*;

fn write_temp_lean(source: &str) -> (tempfile::TempDir, PathBuf) {
    let dir = tempfile::tempdir().expect("tempdir");
    let file = dir.path().join("Program.lean");
    std::fs::write(&file, source).expect("write fixture");
    (dir, file)
}

pub(super) fn compile_c(source: &str, decl: &str) -> anyhow::Result<String> {
    let (_dir, file) = write_temp_lean(source);
    compile_to_string(CompileArgs {
        file: Some(file),
        decl: Some(decl.to_owned()),
        emit: EmitFormat::C,
        opt_level: 0,
        output: None,
        link_artifact: Vec::new(),
    })
}

pub(super) fn refusal(source: &str, decl: &str) -> String {
    match compile_c(source, decl) {
        Ok(c) => panic!("the native path COMPILED `{decl}`; it must refuse:\n{source}\n---\n{c}"),
        Err(err) => format!("{err:#}"),
    }
}

/// Every C identifier in `c` that is exactly `sym` (not a prefix of a longer
/// identifier such as `l_slow_boxed`).
pub(super) fn mentions_symbol(c: &str, sym: &str) -> bool {
    c.match_indices(sym).any(|(at, _)| {
        let before = c[..at].chars().next_back();
        let after = c[at + sym.len()..].chars().next();
        let ident = |ch: Option<char>| ch.is_some_and(|ch| ch.is_ascii_alphanumeric() || ch == '_');
        !ident(before) && !ident(after)
    })
}

const IMPLEMENTED_BY: &str = "def fast (n : Nat) : Nat := n + 1\n\
    \n\
    @[implemented_by fast]\n\
    def slow (n : Nat) : Nat := n + 2\n\
    \n\
    def main : IO Unit := IO.println (toString (slow 1))\n";

/// The battery row `attr_implemented_by`: `main` calls `fast`, and `slow`'s
/// logical body is never compiled.
#[test]
fn test_compile_implemented_by_main_calls_fast_never_slow() {
    let c = compile_c(IMPLEMENTED_BY, "main")
        .unwrap_or_else(|e| panic!("main must compile with `slow` implemented by `fast`: {e:#}"));
    assert!(
        mentions_symbol(&c, "l_fast"),
        "main's C must call the implementation `l_fast`:\n{c}"
    );
    assert!(
        !mentions_symbol(&c, "l_slow"),
        "main's C must never reference `l_slow`, whose body Lean never compiles:\n{c}"
    );
}

/// The substitution reaches a partial application too (`slow` passed as a
/// function value).
#[test]
fn test_compile_implemented_by_function_value_is_substituted() {
    let source = "def fast (n : Nat) : Nat := n + 1\n\
        @[implemented_by fast]\n\
        def slow (n : Nat) : Nat := n + 2\n\
        def main : IO Unit := IO.println (toString ([1, 2].map slow))\n";
    let c = compile_c(source, "main")
        .unwrap_or_else(|e| panic!("main must compile with `slow` implemented by `fast`: {e:#}"));
    assert!(mentions_symbol(&c, "l_fast"), "{c}");
    assert!(!mentions_symbol(&c, "l_slow"), "{c}");
}

/// Compiling the `@[implemented_by]` declaration ITSELF is refused by name:
/// Lean does not compile it, so there is no code of its to emit.
#[test]
fn test_compile_implemented_by_root_refused_by_name() {
    let err = refusal(IMPLEMENTED_BY, "slow");
    assert!(
        err.contains("implemented_by") && err.contains("slow"),
        "the refusal must name implemented_by and the declaration: {err}"
    );
}

/// An `unsafe` implementation is refused by name (Lean runs it; Clean
/// compiles no unsafe code).
#[test]
fn test_compile_implemented_by_unsafe_target_refused_by_name() {
    let source = "unsafe def fastU (n : Nat) : Nat := n + 1\n\
        @[implemented_by fastU]\n\
        def slowU (n : Nat) : Nat := n + 2\n\
        def main : IO Unit := IO.println (toString (slowU 1))\n";
    let err = refusal(source, "main");
    assert!(
        err.contains("implemented_by") && err.contains("fastU"),
        "the refusal must name implemented_by and the unsafe target: {err}"
    );
}

/// The battery row `attr_extern_body`: a source `@[extern] def` with a body,
/// reachable from `main`, is refused by name — Lean runs the C symbol, never
/// the body.
#[test]
fn test_compile_refuses_reachable_extern_with_body() {
    let source = "@[extern \"clean_battery_no_such_symbol\"]\n\
        def bump (n : Nat) : Nat := n + 1\n\
        \n\
        def main : IO Unit := IO.println (toString (bump 1))\n";
    let err = refusal(source, "main");
    assert!(
        err.contains("bump") && err.contains("@[extern") && err.contains("(native-extern-body)"),
        "the refusal must name the declaration and its @[extern]: {err}"
    );
}

/// A shim candidate still has to pass the production FFI audit. The injected
/// predicate models the same early skip as a registered primitive, without
/// rebinding a prelude declaration (which source elaboration refuses).
fn select_with_shim_candidate(
    source: &str,
    meaning: CodeMeaning,
) -> anyhow::Result<(Vec<Decl>, Environment, PipelineConfig)> {
    let (_dir, file) = write_temp_lean(source);
    select_lcnf_decl_with_meaning(
        &CompileArgs {
            file: Some(file),
            decl: Some("caller".to_owned()),
            emit: EmitFormat::C,
            opt_level: 0,
            output: None,
            link_artifact: Vec::new(),
        },
        &|symbol| symbol == "l_candidate" || is_primitive_denylisted(symbol),
        meaning,
    )
}

#[test]
fn test_compile_shim_candidate_cannot_hide_extern_with_body() {
    let source = "@[extern \"clean_no_such_implementation\"]\n\
        def candidate (n : Nat) : Nat := n\n\
        def caller (n : Nat) : Nat := candidate n\n";
    for meaning in [CodeMeaning::LeanCompiled, CodeMeaning::KernelValue] {
        let err = select_with_shim_candidate(source, meaning)
            .expect_err("shim selection must not hide an extern body");
        let message = format!("{err:#}");
        assert!(message.contains("(native-extern-body)"), "{message}");
        assert!(message.contains("candidate"), "{message}");
        assert!(
            message.contains("clean_no_such_implementation"),
            "{message}"
        );
    }
}

#[test]
fn test_compile_shim_candidate_cannot_hide_bodiless_extern() {
    let source = "@[extern \"clean_no_such_implementation\"]\n\
        opaque candidate (n : Nat) : Nat\n\
        def caller (n : Nat) : Nat := candidate n\n";
    for meaning in [CodeMeaning::LeanCompiled, CodeMeaning::KernelValue] {
        let err = select_with_shim_candidate(source, meaning)
            .expect_err("shim selection must not hide a bodiless extern");
        let message = format!("{err:#}");
        assert!(message.contains("(native-extern)"), "{message}");
        assert!(message.contains("candidate"), "{message}");
        assert!(
            message.contains("clean_no_such_implementation"),
            "{message}"
        );
    }
}

#[test]
fn test_compile_shim_candidate_implemented_by_still_selects_target() {
    let source = "def actual (n : Nat) : Nat := n\n\
        @[implemented_by actual]\n\
        def candidate (n : Nat) : Nat := n + 7\n\
        def caller (n : Nat) : Nat := candidate n\n";
    let (decls, _, _) = select_with_shim_candidate(source, CodeMeaning::LeanCompiled)
        .expect("an implemented_by edge must be followed before shim selection");
    assert!(decls
        .iter()
        .any(|decl| decl.name == Name::from_string("actual")));
    assert!(!decls
        .iter()
        .any(|decl| decl.name == Name::from_string("candidate")));
}

#[test]
fn test_compile_ordinary_shim_candidate_retains_existing_boundary() {
    let source = "def candidate (n : Nat) : Nat := n\n\
        def caller (n : Nat) : Nat := candidate n\n";
    for meaning in [CodeMeaning::LeanCompiled, CodeMeaning::KernelValue] {
        let (decls, _, _) = select_with_shim_candidate(source, meaning)
            .expect("ordinary shim candidates retain the existing boundary");
        assert!(decls
            .iter()
            .any(|decl| decl.name == Name::from_string("caller")));
        assert!(!decls
            .iter()
            .any(|decl| decl.name == Name::from_string("candidate")));
    }
}

/// The same declaration as the ROOT is refused too.
#[test]
fn test_compile_refuses_extern_with_body_as_root() {
    let source = "@[extern \"clean_battery_no_such_symbol\"]\n\
        def bump (n : Nat) : Nat := n + 1\n";
    let err = refusal(source, "bump");
    assert!(err.contains("(native-extern-body)"), "{err}");
}

/// `attr_implemented_by_chain`: Lean follows a chain to its END (`slowest 1`
/// prints `fastest`'s `10`); neither intermediate body is compiled.
#[test]
fn test_compile_implemented_by_chain_runs_end() {
    let c = compile_c(
        "def fastest (n : Nat) : Nat := n * 10\n\
         @[implemented_by fastest]\n\
         def middle (n : Nat) : Nat := n + 7\n\
         @[implemented_by middle]\n\
         def slowest (n : Nat) : Nat := n + 5\n\
         def main : IO Unit := IO.println (toString (slowest 1))\n",
        "main",
    )
    .unwrap_or_else(|e| panic!("a chain runs its end, as in Lean: {e:#}"));
    assert!(mentions_symbol(&c, "l_fastest"), "{c}");
    assert!(!mentions_symbol(&c, "l_middle"), "{c}");
    assert!(!mentions_symbol(&c, "l_slowest"), "{c}");
}

/// A chain that returns to a declaration it passed: pinned Lean never
/// finishes compiling a caller (`lean --run` timed out), so there is no
/// implementation to run. Refused by name, naming the cycle. `a` is
/// `@[noinline]` so that the late command records nothing (R149's amendment
/// of 2026-10-20 records a bound declaration's own code otherwise) and the
/// cycle, not the order refusal, is what this test reaches.
#[test]
fn test_compile_implemented_by_cycle_refused_by_name() {
    let err = refusal(
        "@[noinline] def a (n : Nat) : Nat := n + 1\n\
         @[implemented_by a] def b (n : Nat) : Nat := n + 2\n\
         attribute [implemented_by b] a\n\
         def main : IO Unit := IO.println (toString (a 1))\n",
        "main",
    );
    assert!(err.contains("(implemented-by-cycle)"), "{err}");
    assert!(err.contains("`a`"), "{err}");
}

/// `attr_implemented_by_opaque`: a bodiless `opaque` with the attribute runs
/// its target (Lean prints `2`).
#[test]
fn test_compile_implemented_by_opaque_runs_target() {
    let c = compile_c(
        "def fastO (n : Nat) : Nat := n + 1\n\
         @[implemented_by fastO]\n\
         opaque op (n : Nat) : Nat\n\
         def main : IO Unit := IO.println (toString (op 1))\n",
        "main",
    )
    .unwrap_or_else(|e| panic!("the opaque runs its target: {e:#}"));
    assert!(mentions_symbol(&c, "l_fastO"), "{c}");
    assert!(!mentions_symbol(&c, "l_op"), "{c}");
}

/// `attr_extern_opaque`: a bodiless `@[extern]` declaration. Lean calls the
/// symbol (`lean --run`: "Could not find native implementation", rc 1); Clean
/// binds no user extern symbol, so the build is refused by name instead of
/// failing at link time without one.
#[test]
fn test_compile_refuses_reachable_extern_without_body() {
    let err = refusal(
        "@[extern \"clean_no_such_sym\"]\n\
         opaque bumpO (n : Nat) : Nat\n\
         def main : IO Unit := IO.println (toString (bumpO 1))\n",
        "main",
    );
    assert!(err.contains("(native-extern)"), "{err}");
    assert!(err.contains("`bumpO`"), "{err}");
    assert!(err.contains("clean_no_such_sym"), "{err}");
}

/// NEGATIVE CONTROL for the extern refusal: the prelude's natively
/// implemented operations register no `@[extern]` binding, so an ordinary
/// program still compiles.
#[test]
fn test_compile_prelude_natives_are_not_refused_as_extern() {
    compile_c(
        "def main : IO Unit := IO.println (toString (\"ab\".length + 2 * 3))\n",
        "main",
    )
    .unwrap_or_else(|e| panic!("a prelude-only program must compile: {e:#}"));
}

/// A DEPENDENCY whose lowering meets an implementation Clean cannot compile
/// (here `unsafe`) is refused by name, naming the dependency; it was dropped
/// to an extern and failed later at link time without a name.
#[test]
fn test_compile_implemented_by_unsafe_end_behind_a_dependency_refused_by_name() {
    let err = refusal(
        "unsafe def fastU (n : Nat) : Nat := n + 1\n\
         @[implemented_by fastU]\n\
         def slowU (n : Nat) : Nat := n + 2\n\
         @[noinline] def caller (n : Nat) : Nat := slowU n\n\
         def main : IO Unit := IO.println (toString (caller 1))\n",
        "main",
    );
    assert!(err.contains("implemented_by"), "{err}");
    assert!(err.contains("fastU"), "{err}");
    assert!(err.contains("`caller`"), "{err}");
}

#[test]
fn checked_native_worklist_distinguishes_erased_proofs_from_live_unsafe_calls() {
    let source = "unsafe def unsafeFast (n : Nat) : Nat := n + 1\n\
        @[implemented_by unsafeFast] def logical (n : Nat) : Nat := n + 2\n\
        def witness (n : Nat) : True := \
          (fun (_ : logical n = logical n) => True.intro) (Eq.refl (logical n))\n\
        @[noinline] def keep (n : Nat) (_ : True) : Nat := n\n\
        def erasedEntry (n : Nat) : Nat := keep n (witness n)\n\
        @[noinline] def liveDependency (n : Nat) : Nat := logical n\n\
        def liveEntry (n : Nat) : Nat := liveDependency n\n";
    let (_dir, file) = write_temp_lean(source);
    let (env, opaques, source_decls) = elaborate_file_with_inventory(&file).expect("check source");
    let declarations = source_decls
        .into_iter()
        .map(|name| {
            let info = env.get_const(&name).expect("checked declaration").clone();
            let origin = env.get_constant_origin(&name).cloned();
            (name, (info, origin))
        })
        .collect();
    let checked = CheckedNativeSource {
        declarations,
        opaques,
    };

    let select = |entry: &str| {
        let root = Name::from_string(entry);
        let closure = clean_compiler::RuntimeBindingClosure::check_executable(
            &env,
            std::slice::from_ref(&root),
        )?;
        checked.select(
            &env,
            None,
            &root,
            0,
            Some(&closure),
            crate::native_nat_display::NatDisplay::Bootstrap,
        )
    };
    let selected = select("erasedEntry")
        .expect("the unsafe implementation occurs only within the erased proof");
    let witness = Name::from_string("witness");
    assert!(checked.declarations.contains_key(&witness));
    assert!(selected.decls.iter().all(|decl| decl.name != witness));

    let Err(error) = select("liveEntry") else {
        panic!("a live call cannot run the unsafe implementation");
    };
    let err = format!("{error:#}");
    assert!(err.contains("unsafeFast"), "{err}");

    let err = refusal(source, "erasedEntry");
    assert!(err.contains("unsafeFast"), "{err}");
}

/// A `Box` monad-like structure with `fastBind` (adds 1 to the tag) declared
/// before `slowBind` (adds 2), which carries `slow_attrs`; then `rest`.
fn box_program(slow_attrs: &str, rest: &str) -> String {
    format!(
        "structure Box (α : Type) where\n  val : α\n  tag : Nat\n\
         def fastBind {{α β : Type}} (x : Box α) (f : α → Box β) : Box β := \
         ⟨(f x.val).val, x.tag + 1⟩\n\
         {slow_attrs}def slowBind {{α β : Type}} (x : Box α) (f : α → Box β) : Box β := \
         ⟨(f x.val).val, x.tag + 2⟩\n\
         {rest}\
         def main : IO Unit := IO.println (toString ((Box.mk 5 0 >>= fun n => Box.mk n 0).tag))\n"
    )
}

/// The monad inlining (`native_monad_inline`) reduces `@Bind.bind Box inst`
/// before the walk. It must never unfold a constant whose compiled meaning
/// is not its value: compiled Lean runs `fastBind` (`1`) for each program
/// below (`attr_implemented_by_reducible`, `attr_implemented_by_instance`,
/// `attr_implemented_by_iota`): through a reducible `@[implemented_by]`
/// field, through an `@[implemented_by]` instance, and through an ordinary
/// constant with the attribute that a `match` takes apart (the major premise
/// of the `casesOn` is reduced with full delta, whatever its reducibility;
/// the inlining put `slowBind`'s `+ 2` in `main`, `2` at exit 0). The
/// instance printed `2` at exit 0 too, because the parser dropped its
/// attribute (`clean_parser`'s `SurfaceDecl::Instance::compiler_attrs`).
#[test]
fn test_compile_monad_inlining_never_unfolds_an_implemented_by() {
    for (name, source) in [
        (
            "reducible field",
            box_program(
                "@[reducible, implemented_by fastBind] ",
                "instance : Bind Box := ⟨slowBind⟩\n",
            ),
        ),
        (
            "instance",
            box_program(
                "",
                "@[reducible] def instFast : Bind Box := ⟨fastBind⟩\n\
                 @[implemented_by instFast]\n\
                 instance instSlow : Bind Box := ⟨slowBind⟩\n",
            ),
        ),
        (
            "match on an ordinary constant",
            box_program(
                "",
                "def pairF : Prod (Bind Box) Nat := (⟨fastBind⟩, 0)\n\
                 @[implemented_by pairF] def pairS : Prod (Bind Box) Nat := (⟨slowBind⟩, 0)\n\
                 instance instBindBox : Bind Box := match pairS with | (b, _) => b\n",
            ),
        ),
    ] {
        let c = compile_c(&source, "main")
            .unwrap_or_else(|e| panic!("{name}: the program must compile: {e:#}\n{source}"));
        assert!(
            mentions_symbol(&c, "l_fastBind"),
            "{name}: compiled code must run `fastBind`:\n{source}\n---\n{c}"
        );
        assert!(
            !mentions_symbol(&c, "l_slowBind"),
            "{name}: `slowBind` must never be compiled:\n{source}\n---\n{c}"
        );
    }
}

/// NEGATIVE CONTROL for the inlining: a plain `@[implemented_by fastBind]`
/// field (not reducible) of an ordinary instance already ran `fastBind`
/// (Lean prints `1`) and still does.
#[test]
fn test_compile_implemented_by_plain_instance_field_runs_target() {
    let source = box_program(
        "@[implemented_by fastBind] ",
        "instance : Bind Box := ⟨slowBind⟩\n",
    );
    let c = compile_c(&source, "main")
        .unwrap_or_else(|e| panic!("the program must compile: {e:#}\n{source}"));
    assert!(mentions_symbol(&c, "l_fastBind"), "{source}\n---\n{c}");
    assert!(!mentions_symbol(&c, "l_slowBind"), "{source}\n---\n{c}");
}

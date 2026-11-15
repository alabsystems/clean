# `native_exec_battery` — byte-exact differential battery for `clean run`

**Landed:** 2026-09-25 (Phase 0 package P0_EXEC, "the native path never prints a
wrong answer at exit 0").
**Gate:** `crates/clean/tests/native_exec_battery.rs`
(`cargo test --locked -p clean --test native_exec_battery`), wired as the
`native-exec-battery` leg of `scripts/local_gate.sh` (full mode) and named as
the gate command of the `compile-runtime` replacement scorecard row.
**Pins and evidence:** `reports/native-exec-battery.json` — one verdict per
program, re-minted only deliberately (`CLEAN_NATIVE_EXEC_UPDATE=1`), and the
`compile-runtime` row's evidence artifact.

## What is here

* `programs/<name>.lean` — a Lean 4 program with a `main`. An optional
  `<name>.args` (one argument per line) is its `argv`; an optional
  `<name>.stdin` is fed to its standard input. Every program runs in a fresh
  scratch working directory (`p20_fs` writes a file).
* `expected/<name>.{stdout,stderr,rc}` — what pinned Lean printed, byte for
  byte, and its exit status. `expected/LEAN_VERSION` records the binary.
  Minted by `scripts/native_exec_battery_expected.py`, which runs
  `LEAN_BACKTRACE=0 lean -Dlinter.all=false --run <program> <args>`:
  `LEAN_BACKTRACE=0` because a panic's backtrace carries addresses, and
  `-Dlinter.all=false` because `lean --run` prints linter warnings on STDOUT
  ahead of the program's output. A program Lean itself rejects is refused by
  the minting, never recorded. The battery compares against these COMMITTED
  bytes, so running it needs no Lean install.

A verdict that moves off its pin is a RESULT, re-pinned deliberately with
`CLEAN_NATIVE_EXEC_UPDATE=1 cargo test --locked -p clean --test
native_exec_battery` and explained in the commit, exactly as
`scripts/u2_battery.sh` re-pins.

## The verdicts, and which ones the gate allows

| verdict | meaning | allowed |
|---|---|---|
| `BYTE_EQUAL` | stdout, stderr and exit status identical to Lean's | yes |
| `REFUSED_BUILD` | `clean run` refused to build it with a named error (`Error: …`, empty stdout, status 1) | yes |
| `REFUSED_RUNTIME` | the program stopped itself with a named fail-closed runtime error (`clean panic: …`), after printing at most a prefix of Lean's stdout | yes |
| `WRONG_OUTPUT_EXIT0` | exit 0 and different bytes | **never** |
| `WRONG_OUTPUT` | a nonzero exit that is neither a refusal nor a crash | no |
| `CRASH` | killed by a signal with no named runtime error | no |
| `TIMEOUT` | did not finish | no |

A refusal is an acceptable answer; a wrong answer is not. This battery measures
FAIL-CLOSEDNESS, not parity: read the `BYTE_EQUAL` count in the report for how
much of it runs, and never read a green gate as "the native path works".

## Where the programs came from

* `p01`–`p24` (less `p05_hashmap` and `p19_wordfreq`, which `import Std`), `q03`–`q27` and
  `narrow_*`: the compiler/runtime pillar of the 2026-09-24 ten-agent audit
  (`reports/lean4-replacement-audit-2026-09-24/compiler_runtime.json`).
  `narrow_i2` drops the audit copy's `Int.div a b` line, which pinned Lean
  rejects (`Int.div` is not a constant in v4.30.0-rc2).
* `critic_idiv`, `critic_ite`: the critic's spot check "the native path prints
  wrong output at exit 0" (`critic.json`).
* `eio_*`, `monad_*`, `layout_*`, `placeholder_*`: the P0_EXEC probes, each the
  minimal program for one measured defect class — eager IO in a branch or a
  `let`, an action handed to a function, `do` in a monad the native shims do
  not implement, a constructor whose erased field lost its slot, a prelude
  stand-in body.
* `eio_ignored_action_arg`, `eio_alias_branch`, `string_*`: added by the
  P0_EXEC review, each a program that printed a wrong answer at exit 0 on the
  branch as first submitted — an action handed to a callee that ignores it
  (`a`, where Lean prints nothing) and an `if` between actions under
  `abbrev M := IO` (both arms ran), neither of which the eager-IO audit's
  syntactic trigger scan reached; and a `String` built or read as the prelude's
  `String.mk` cell (`Nat.repr 42` and `['a', 'b'].asString` printed empty
  lines), which the runtime's byte-string carrier cannot be.
* `attr_implemented_by`, `attr_extern_body`
  (`compiler-implemented-by-and-extern-fail-closed`, 2026-10-17): an
  `@[implemented_by fast] def slow` whose implementation Lean runs (Lean prints
  `2`; the logical body gives `3`, which `clean run` printed at exit 0 before
  the substitution), and an `@[extern]` declaration with a body, which Lean
  never runs: its pinned output is Lean FAILING, rc 1 with "Could not find
  native implementation of external declaration", so the answer is a named
  refusal (`native-extern-body`), never the body's `2`.
* `attr_implemented_by_fn_value`, `_chain`, `_opaque`, `_command`,
  `_command_instance`, `_instance`, `_reducible`, `_iota`, `_unsafe`,
  `attr_extern_opaque`, `attr_extern_command` (the same item, amended
  2026-10-18 in `docs/DECISIONS.md`): what Lean runs for an
  `@[implemented_by]` reached as a function value, through a chain (its END,
  `10`), on an `opaque`, by the `attribute` command written before every
  caller, on an `instance` (the parser dropped that attribute, and `clean
  run` printed the instance value's `2` at exit 0), on a reducible field, and
  on an ordinary constant an instance takes apart with a `match` (the monad
  inlining reduced the `match` with full delta and printed the logical
  body's `2` at exit 0; it now reduces with every attributed constant
  hidden). A bodiless `@[extern]` is refused (`native-extern`) where Lean
  fails too (rc 1): no divergence. Two refusals are known, fail-closed
  divergences: an `unsafe` end is refused by name where Lean runs it, and
  `attribute [extern]` after the declaration is refused like the bodied form
  although Lean compiled the body first.
* `attr_implemented_by_order`, `_order_noinline`, `_order_entry`,
  `_order_chain`, `_order_instance`, `_order_instance_inline`,
  `_order_instance_after`, `_order_iota`: an `attribute [implemented_by]`
  command AFTER code that reaches the declaration it binds. Lean compiled
  that code first, and which body it then runs is its inliner's choice (`3`
  for a `@[noinline]` caller, `2` when the caller is inlined into a later
  `main`; the old body through an `@[inline]` instance, the new one through a
  plain instance). Clean does not model the inliner: when the file recorded
  such code, every root is refused by name (`native-implemented-by-order`),
  naming the rebound declaration and the code that reaches it. Five of these
  printed a wrong answer at exit 0 before; `attr_implemented_by_order` and
  `_order_instance_after` printed Lean's answer and are refused all the same.
* `attr_implemented_by_command_small`, `_command_inline`, `attr_implemented_by_macro_inline`,
  `attr_implemented_by_command_macro_inline` (`docs/DECISIONS.md` R149, amended 2026-10-20):
  the command form before every caller still comes after the declaration's OWN code, and
  Lean's inliner copies that pre-binding body into callers compiled later whenever the
  declaration is an inline candidate: `def slow (n : Nat) : Nat := n` (LCNF size at most
  `compiler.small`) prints the old body's `1` under `fast n := Nat.add n 100`, and
  `@[inline] slow` prints `3`; `clean run` printed `101` and `2` at exit 0. Clean cannot
  compute Lean's LCNF size, so a late binding of any declaration that is not `@[noinline]`
  records the declaration itself and every root is refused (`native-implemented-by-order`);
  `_command_instance`, whose `slowBind` is no inline candidate (Lean prints `1`), is refused
  all the same since then, a known over-refusal. A `@[macro_inline]` declaration's body is
  expanded at every call site whatever binds it, on the declaration or by the command (Lean
  prints `3` for both rows' every line; `clean run` printed `2` twice at exit 0 for the
  first and refused the second, whose earlier caller was recorded), so its binding is not
  registered and the body compiles.

* `layout_wide_scalars`, `layout_256_fields`, `layout_enum_300`: the
  constructor shapes Clean's 8-byte object header truncates
  (`runtime-ctor-layout-and-tag-limits`, 2026-10-16) — 40 `UInt64` fields
  (320 scalar bytes; Lean prints `41`), 256 `Nat` fields (Lean prints `14`),
  and a 300-constructor enum, whose boxed tag 299 an 8-bit tag read would
  see as 43 (Lean prints `true`/`false`). The IR checker refuses the first two by name,
  so their pins are `REFUSED_BUILD`. A boxed tag lives in the pointer bits,
  not in a header byte, and every lane now reads it at 32 bits (the C header,
  the trust-cg `U32` import, the Rust runtime), so `layout_enum_300` runs and
  is pinned `BYTE_EQUAL` (the LX0 trust-cg lane refuses it by name in
  trust-cg's aarch64 encoder, `TCG-A64-BRANCH-RELAX` on the 300-way
  `E.casesOn`; `reports/lx0-trustcg-native-battery-2026-09-30.json`). A
  battery row cannot show that the out-of-bounds writes are gone (the
  pre-fix `clean` 0.9.0 printed `41` for the first at exit 0 while writing
  320 bytes into a 64-byte scalar area), so the
  clean-compiler `ir_checker::layout_limit_tests` and the clean-runtime
  `c_ctor_layout_limits` harness carry that claim. Every field is initialised
  with the parameter itself: `n + i` field values are refused earlier
  (`layout_wide_scalars`: an object-typed value in a scalar slot) or, for 256
  `Nat` fields, overflow the debug `clean` frontend's stack, and either way
  never reach the checker this row measures.

* `nat_match_wide`: a `Nat` pattern match at every width — 255, 256, 300,
  2^32 and past it, 2^63 - 1 and the heap `Nat`s 2^63 and 2^64. `to_mono`
  lowers every `Nat` match to `Nat.decEq n 0` (`to_mono/cases/numeric.rs`),
  so no lane reads a constructor tag off a `Nat`; this row pins that a `Nat`
  of 256 or more takes the successor branch (pinned by the clean-compiler
  `pipeline_api` test at the IR level for all three lanes).

`import` programs are deliberately absent: each loads ~90k constants from
`.olean` in ~80 s at ~2.2 GB (audit battery 3), which belongs to the import
lane and not to a gate leg.

## A second driver: the trust-cg lane (LX0 measurement)

`crates/clean/tests/native_exec_battery_trustcg.rs` runs the same programs
against the same `expected/` bytes through the experimental
`clean run --backend trust-cg` (the `trust-ir-backend` feature, an explicitly
selected `CLEAN_TRUST_CG_BIN`), and the C lane beside it for comparison. Its
pins are `reports/lx0-trustcg-native-battery-2026-09-30.json` (with a `.md`
summary beside it), re-minted only with `CLEAN_LX0_UPDATE=1`. It is a
MEASUREMENT of what blocks each program on the one-backend path, not a gate leg;
its claim is "measurement only; no binary claim; lane =
clean-compiler-unvalidated". It reads this battery's committed verdicts only to
choose its scope (p01_hello and every `BYTE_EQUAL` pin) and never changes them.

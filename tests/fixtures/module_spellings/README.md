# Module-system spellings: pinned Lean's file-level verdicts

Ground truth for plan item `formats-module-spelling-refusals`
(`docs/plans/LEAN4_UPSTREAM_DELTA_2026-10-16.md`).
`crates/clean-parser/tests/module_system_b_e2e.rs` replays every row through
`clean_parser::parse_file` and compares Clean's verdict, and its first message
byte for byte, with what Lean printed. Eight matrix rows, `meta` in front of
`section` or `variable`, are pinned at a known gap instead.

| file | role |
|---|---|
| `verdicts.tsv` | 31 rows: each spelling the item decides, with and without a `module` header where that changes the verdict, the negative controls Lean accepts, and ten files with a comment before or inside the header (a doc comment ends the header; `--` and `/- -/` do not) |
| `modifier_matrix.tsv` | 168 rows: 56 modifier prefixes, 13 of them led by a `/-- d -/` doc comment, in front of `import`, `section` and `variable`, each after a first command (outside the header) |
| `probe.py` | the regeneration recipe; `--check` compares the committed tables with a fresh run |

**Oracle.** Every row was printed identically by Lean `v4.30.0-rc2` (commit
`3dc1a088b6d2`, the `lean-toolchain` pin) and `v4.33.1` (commit
`819816b2e0a3`), which each row's `lean_toolchains` column names and the
headers' comment lines quote in full (`lean --version`); `probe.py` refuses to
write a table when two toolchains disagree. First measured 2026-10-21, and
re-measured on 2026-10-25 (`probe.py --check` exit 0 before the
`lean_toolchains` column was added, then rewritten with it). The doc-comment
rows were added and the tables rewritten on 2026-10-26, after a review found
that Clean read through a doc comment in the header. A row is a whole
file run as `lean <file>` with no Lake and no import beyond the implicit
`Init`, and the replay test refuses a row that does not name the
`lean-toolchain` pin.

**Message columns.** `lean_messages` holds every message Lean printed, each as
`line:col: error: text` with the file name removed, joined by ` | `. Clean
reports the first one only: Lean recovers after the first error and goes on
(for `private import` it then reads `import` as a misplaced command, "invalid
'import' command, it must be used in the beginning of the file"); Clean
refuses the file there.

**What the expected lists depend on.** An "unexpected token" message lists the
commands Lean's grammar could still take after the modifiers it read. The lists
here are those of a file whose only import is the implicit `Init`. An import
that adds commands taking declaration modifiers (Mathlib's do) makes Lean's
list longer; Clean prints the `Init` list, so the verdict and position agree
there and the list may not.

**Cases that are not rows yet.** A second review (2026-10-28) measured a doc
comment inside a header import (`public /-- d -/ import Init`, `import /-! d
-/ Init`, `import all /-- d -/ Init`, …) and `import all` with the module name
on the next line on pinned v4.30.0-rc2 only, and its own review two doc
comments in a row (`import /-- a -/ /-! b -/ Init`) and a header whose import
Clean recovers (`module` / `import all` / `import /-- d -/ Init`). The
review after that measured a doc comment after the one a command carries
(`/-- a -/ /-! b -/ module`, `/-- a -/ /-! b -/ private section`). Their
messages are pinned in `module_system_b_e2e.rs` and `module_file_header.rs`
instead; a row needs this probe run on both toolchains.

**Where Clean differs from these rows.** `module_system_b_e2e.rs` pins each
difference, so it fails the day one closes:

- A bare `import` after a module doc (`/-! … -/`), like any bare `import` past
  the header, is still read
  (`test_bare_import_after_a_module_doc_is_read_known_divergence`); Lean
  refuses it with "invalid 'import' command, it must be used in the beginning
  of the file". It is pinned by that test rather than kept as a row. After a
  declaration doc comment (`/-- … -/`) the `import` is refused in Lean's words
  (the `doc_import_*` rows).
- `meta` in front of `section` or `variable` (8 matrix rows): Clean's `meta`
  arm takes only `import` and the declaration keywords, so `meta section`,
  `public meta section` and `@[expose] public noncomputable meta section`,
  which Lean accepts, and the five refused rows are all a `RawDecl`
  ("unknown command `meta`"), not Lean's message.
- No world Clean reads accepts `public variable` / `private variable`. Lean
  accepts both from v4.36.0-rc1 (lean4#15518, "accepted but do not have any
  effect yet"); the parser's world gate admits them there, and every world of
  `crates/clean-olean/lean_worlds.tsv` precedes it.

Regenerate from the repository root (needs both toolchains under
`~/.elan/toolchains`):

```sh
python3 -I tests/fixtures/module_spellings/probe.py          # rewrite both tables
python3 -I tests/fixtures/module_spellings/probe.py --check  # exit 1 on drift
```

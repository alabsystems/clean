// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! C-harness tests for sticky (frozen) reference counts (plan item
//! `runtime-rc-sticky`; Lean v4.35.0 `lean.h` 640-765, lean4#14838/#15241).
//!
//! `clean_obj_header.ref_count` stores refs-1 in a `uint32_t`, so 0 means
//! "exclusive". Before the sticky band an increment at 0xFFFFFFFF wrapped to
//! 0: `clean_reset` then reused a shared cell in place and the next
//! `clean_dec` freed a live object. Every row here builds the shipped C
//! sources (the embedded copies `clean run` materializes) and asserts the
//! program's exact stdout. Counts are set with `atomic_store_explicit`; the
//! arithmetic at base is unsigned atomic arithmetic, so a failing row fails
//! by a wrong count, never by undefined behaviour.
//!
//! Each program is built twice, plainly at `clean run`'s `-O2 -std=c11` and
//! with `-fsanitize=address`, so a double free or a use after free in the
//! deletion worklist aborts instead of printing the right bytes.
//!
//! A C compiler is required: a harness that cannot find one fails here, never
//! skips.

use std::path::{Path, PathBuf};
use std::process::Command;

// ---------------------------------------------------------------------------
// Harness
// ---------------------------------------------------------------------------

/// Whether `candidate --version` runs and exits 0.
fn runs_version(candidate: &str) -> bool {
    Command::new(candidate)
        .arg("--version")
        .output()
        .is_ok_and(|o| o.status.success())
}

/// The C compiler lookup, over injected inputs: `$CLEAN_CC`, else `$CC`, else
/// the first of `path_candidates` whose `--version` succeeds (the order
/// `clean run` uses). A variable that is set must name a working compiler: it
/// never falls through to the next source.
fn c_compiler_lookup(
    clean_cc: Option<&str>,
    cc: Option<&str>,
    path_candidates: &[&str],
) -> Result<PathBuf, String> {
    for (var, value) in [("CLEAN_CC", clean_cc), ("CC", cc)] {
        if let Some(value) = value.map(str::trim).filter(|v| !v.is_empty()) {
            return if runs_version(value) {
                Ok(PathBuf::from(value))
            } else {
                Err(format!("${var}={value} does not run `--version`"))
            };
        }
    }
    path_candidates
        .iter()
        .find(|c| runs_version(c))
        .map(PathBuf::from)
        .ok_or_else(|| {
            format!(
                "no working C compiler: $CLEAN_CC and $CC unset, none of [{}] runs `--version`",
                path_candidates.join(", ")
            )
        })
}

fn c_compiler() -> PathBuf {
    let clean_cc = std::env::var("CLEAN_CC").ok();
    let cc = std::env::var("CC").ok();
    c_compiler_lookup(clean_cc.as_deref(), cc.as_deref(), &["cc", "gcc", "clang"]).unwrap_or_else(
        |e| panic!("{e}; c_header_rc_sticky fails rather than skips (runtime-rc-sticky)"),
    )
}

#[derive(Clone, Copy, Debug)]
enum Build {
    Plain,
    AddressSanitizer,
}

/// Write a crate C source flattened so `#include "clean_runtime.h"` resolves
/// next to it.
fn materialize(dir: &Path, file: &str, src: &str) {
    let flat = src.replacen("../include/clean_runtime.h", "clean_runtime.h", 1);
    std::fs::write(dir.join(file), flat).expect("write C source");
}

/// Build `main_c` (and `probe_c`, with the trust-cg forwarders of
/// `runtime_extern.c`, when given) against the runtime, run it, and return its
/// stdout. A failed build or a failed run is a panic naming the build.
fn build_and_run(main_c: &str, probe_c: Option<&str>, build: Build) -> String {
    let dir = tempfile::tempdir().expect("tempdir");
    let d = dir.path();
    std::fs::write(d.join("clean_runtime.h"), clean_runtime::runtime_header())
        .expect("write header");
    materialize(d, "clean_runtime.c", clean_runtime::runtime_source());
    std::fs::write(d.join("main.c"), main_c).expect("write main.c");
    let bin = d.join("prog");
    let mut cmd = Command::new(c_compiler());
    cmd.args(["-std=c11", "-pthread"]);
    match build {
        Build::Plain => {
            cmd.arg("-O2");
        }
        Build::AddressSanitizer => {
            cmd.args(["-O1", "-g", "-fsanitize=address", "-fno-omit-frame-pointer"]);
        }
    }
    cmd.arg("-I")
        .arg(d)
        .arg(d.join("main.c"))
        .arg(d.join("clean_runtime.c"));
    if let Some(probe) = probe_c {
        std::fs::write(d.join("probe.c"), probe).expect("write probe.c");
        materialize(
            d,
            "runtime_extern.c",
            clean_runtime::runtime_extern_source(),
        );
        cmd.arg(d.join("probe.c")).arg(d.join("runtime_extern.c"));
    }
    let built = cmd
        .arg("-lm")
        .arg("-o")
        .arg(&bin)
        .output()
        .expect("spawn C compiler");
    assert!(
        built.status.success(),
        "{build:?} C harness failed to compile:\n{}\n\nmain.c:\n{main_c}",
        String::from_utf8_lossy(&built.stderr)
    );
    let run = Command::new(&bin).output().expect("run C harness");
    let stdout = String::from_utf8_lossy(&run.stdout).into_owned();
    assert!(
        run.status.success(),
        "{build:?} C harness exited with {}:\nstdout: {stdout}\nstderr: {}",
        run.status,
        String::from_utf8_lossy(&run.stderr)
    );
    stdout
}

/// Run `body` (statements of `main`, after [`PRELUDE`]) in both builds and
/// assert its exact stdout in each.
fn assert_prints(label: &str, body: &str, expected: &str) {
    let main_c = format!("{PRELUDE}\nint main(void) {{\n{body}\n    return 0;\n}}\n");
    assert_program_prints(label, &main_c, expected);
}

/// Run a whole program in both builds and assert its exact stdout in each.
fn assert_program_prints(label: &str, main_c: &str, expected: &str) {
    for build in [Build::Plain, Build::AddressSanitizer] {
        let out = build_and_run(main_c, None, build);
        assert_eq!(out, expected, "{label} ({build:?})");
    }
}

/// Helpers every program shares. Literal constants only: the rows must build
/// against the runtime before the sticky band existed.
const PRELUDE: &str = r#"#include "clean_runtime.h"
#include <stdio.h>
#include <pthread.h>

static uint32_t rc(clean_obj* o) {
    return atomic_load_explicit(&o->header.ref_count, memory_order_relaxed);
}
static void set_rc(clean_obj* o, uint32_t v) {
    atomic_store_explicit(&o->header.ref_count, v, memory_order_relaxed);
}
static clean_obj* leaf(unsigned tag) { return clean_alloc_ctor(tag, 0, 0); }
/* Free an object the program set a count on: make it exclusive and drop it. */
static void release(clean_obj* o) { set_rc(o, 0); clean_dec(o); }
/* A size_t no constant folding narrows: 2^40 (huge) and 2^32 + 1 (past_u32). */
static volatile size_t huge_n = (size_t)1 << 40;
static volatile size_t past_u32_n = ((size_t)1 << 32) + 1;
"#;

// ---------------------------------------------------------------------------
// The compiler lookup fails, never skips
// ---------------------------------------------------------------------------

#[test]
fn c_compiler_lookup_nothing_found_is_an_error() {
    let err = c_compiler_lookup(None, None, &[]).expect_err("no inputs must be an error");
    assert!(
        err.contains("$CLEAN_CC") && err.contains("$CC"),
        "the error names every source tried: {err}"
    );
    let err = c_compiler_lookup(None, None, &["/nonexistent/cc-a", "/nonexistent/cc-b"])
        .expect_err("absent candidates must be an error");
    assert!(
        err.contains("/nonexistent/cc-a") && err.contains("/nonexistent/cc-b"),
        "the error names the candidates: {err}"
    );
}

#[test]
fn c_compiler_lookup_bad_clean_cc_does_not_fall_through() {
    // `cc` resolves on this host (c_compiler() below needs it); a set
    // $CLEAN_CC that does not run must still be an error.
    let err = c_compiler_lookup(Some("/nonexistent/cc"), None, &["cc", "gcc", "clang"])
        .expect_err("a broken $CLEAN_CC must not fall through to PATH");
    assert!(err.contains("CLEAN_CC"), "{err}");
    let err = c_compiler_lookup(None, Some("/nonexistent/cc"), &["cc", "gcc", "clang"])
        .expect_err("a broken $CC must not fall through to PATH");
    assert!(err.contains("$CC"), "{err}");
}

// ---------------------------------------------------------------------------
// The exit criterion: (a) inc at u32::MAX, (b) drops in the band, (c) cascade
// ---------------------------------------------------------------------------

#[test]
fn c_rc_inc_at_u32_max_leaves_cell_shared() {
    // Before: the count wrapped to 0 and the cell read as exclusive (`0 1`).
    assert_prints(
        "(a) clean_inc at 0xFFFFFFFF",
        r#"    clean_obj* o = leaf(7);
    set_rc(o, 0xFFFFFFFFu);
    clean_inc(o);
    printf("%u %d\n", rc(o), (int)clean_is_exclusive(o));
    release(o);"#,
        "4294967295 0\n",
    );
}

#[test]
fn c_rc_drops_inside_band_leave_count_unchanged() {
    // Before: 2^20 drops took the count to 0xF8000000 - 2^20.
    assert_prints(
        "(b) 2^20 clean_dec at 0xF8000000",
        r#"    clean_obj* o = leaf(7);
    set_rc(o, 0xF8000000u);
    for (uint32_t i = 0; i < (1u << 20); i++) clean_dec(o);
    printf("%u %u\n", rc(o), (unsigned)o->header.tag);
    release(o);"#,
        "4160749568 7\n",
    );
}

#[test]
fn c_rc_cascade_leaves_frozen_child_unchanged() {
    // Before: freeing the exclusive parent decremented the frozen child.
    assert_prints(
        "(c) cascade from an exclusive parent over a child at 0xF8000000",
        r#"    clean_obj* child = leaf(3);
    set_rc(child, 0xF8000000u);
    clean_obj* parent = clean_alloc_ctor(1, 1, 0, child);
    clean_dec(parent);
    printf("%u %u\n", rc(child), (unsigned)child->header.tag);
    release(child);"#,
        "4160749568 3\n",
    );
}

#[test]
fn c_rc_inc_n_past_u32_freezes() {
    // Before: the `uint32_t` parameter converted 2^32 + 1 to 1.
    assert_prints(
        "(d) clean_inc_n(o, 2^32 + 1) from 0",
        r#"    clean_obj* o = leaf(0);
    clean_inc_n(o, past_u32_n);
    uint32_t c = rc(o);
    fprintf(stderr, "count %u\n", c);
    printf("%d %d\n", c >= 0xF0000000u && c < 0xF0010000u, (int)clean_is_exclusive(o));
    release(o);"#,
        "1 0\n",
    );
}

#[test]
fn c_rc_reset_at_u32_max_declines_reuse() {
    // Before: the inc wrapped to 0, so clean_reset dropped the child (5 -> 4)
    // and handed back a shared cell for in-place reuse.
    assert_prints(
        "(e) clean_reset after clean_inc at 0xFFFFFFFF",
        r#"    clean_obj* child = leaf(2);
    set_rc(child, 5);
    clean_obj* o = clean_alloc_ctor(1, 1, 0, child);
    set_rc(o, 0xFFFFFFFFu);
    clean_inc(o);
    clean_obj* r = clean_reset(o);
    printf("%d %u %u\n", r == NULL, rc(o), rc(child));
    set_rc(child, 0);
    release(o);"#,
        "1 4294967295 5\n",
    );
}

// ---------------------------------------------------------------------------
// Lean's tables (rc_sticky.c g_never_freed / g_never_incremented), mapped
// ---------------------------------------------------------------------------

#[test]
fn c_rc_never_freed_table() {
    // DROP, DROP+1, STICKY-1, STICKY, STICKY+1, mid-band, top two.
    assert_prints(
        "drops and cascades leave every never-freed count unchanged",
        r#"    static const uint32_t t[] = {0xE0000000u, 0xE0000001u, 0xEFFFFFFFu, 0xF0000000u,
                                 0xF0000001u, 0xF8000000u, 0xFFFFFFFEu, 0xFFFFFFFFu};
    int bad = 0;
    for (size_t i = 0; i < sizeof t / sizeof t[0]; i++) {
        clean_obj* o = leaf(1);
        set_rc(o, t[i]);
        clean_dec(o);
        if (rc(o) != t[i]) { printf("dec %08x -> %08x\n", t[i], rc(o)); bad = 1; }
        release(o);
        clean_obj* c = leaf(2);
        set_rc(c, t[i]);
        clean_dec(clean_alloc_ctor(0, 1, 0, c));
        if (rc(c) != t[i]) { printf("cascade %08x -> %08x\n", t[i], rc(c)); bad = 1; }
        release(c);
    }
    if (!bad) printf("ok\n");"#,
        "ok\n",
    );
}

#[test]
fn c_rc_never_incremented_table() {
    // STICKY, STICKY+1, mid-band, top two; INC_MAX + 1 takes the cold path.
    assert_prints(
        "increments leave every never-incremented count unchanged",
        r#"    static const uint32_t t[] = {0xF0000000u, 0xF0000001u, 0xF8000000u, 0xFFFFFFFEu,
                                 0xFFFFFFFFu};
    int bad = 0;
    for (size_t i = 0; i < sizeof t / sizeof t[0]; i++) {
        clean_obj* o = leaf(1);
        for (int op = 0; op < 5; op++) {
            set_rc(o, t[i]);
            switch (op) {
            case 0: clean_inc(o); break;
            case 1: clean_inc_n(o, 1); break;
            case 2: clean_inc_n(o, 0x10000); break;
            case 3: clean_inc_n(o, 0x10001); break;
            default: clean_inc_n(o, huge_n); break;
            }
            if (rc(o) != t[i]) { printf("op %d %08x -> %08x\n", op, t[i], rc(o)); bad = 1; }
        }
        release(o);
    }
    if (!bad) printf("ok\n");"#,
        "ok\n",
    );
}

#[test]
fn c_rc_below_band_exact_controls() {
    // Negative control, green before and after: below the band every count
    // moves by exactly the amount asked, so the harness measures real counts.
    assert_prints(
        "below-band counts are exact",
        r#"    clean_obj* o = leaf(1);
    clean_inc(o); printf("%u ", rc(o));
    clean_dec(o); printf("%u ", rc(o));
    set_rc(o, 0x7FFFFFFFu);
    clean_inc(o); printf("%08x ", rc(o));
    clean_dec(o); printf("%08x ", rc(o));
    set_rc(o, 0);
    clean_inc_n(o, 3); printf("%u ", rc(o));
    set_rc(o, 0xDFFFFFFFu);
    clean_dec(o); printf("%08x ", rc(o));
    set_rc(o, 0);
    clean_inc_n(o, 0x10001); printf("%08x\n", rc(o));
    release(o);"#,
        "1 0 80000000 7fffffff 3 dffffffe 00010001\n",
    );
}

#[test]
fn c_rc_band_entry_controls() {
    // An increment enters the band and stops there; a count at DROP still
    // takes increments but no drop.
    assert_prints(
        "entering the band",
        r#"    clean_obj* o = leaf(1);
    set_rc(o, 0xEFFFFFFFu);
    clean_inc(o); printf("%08x ", rc(o));
    clean_inc(o); printf("%08x ", rc(o));
    set_rc(o, 0xE0000000u);
    clean_inc(o); printf("%08x ", rc(o));
    clean_dec(o); printf("%08x\n", rc(o));
    release(o);"#,
        "f0000000 f0000000 e0000001 e0000001\n",
    );
}

#[test]
fn c_rc_band_constants_match_lean_widths() {
    // Lean's widths measured from the wrap point: 0x10000000 between the
    // thresholds and 0x10000000 above CLEAN_RC_STICKY.
    assert_prints(
        "band constants",
        r#"    _Static_assert(CLEAN_RC_STICKY == 0xF0000000u, "STICKY");
    _Static_assert(CLEAN_RC_STICKY_DROP == 0xE0000000u, "STICKY_DROP");
    _Static_assert(CLEAN_RC_STICKY - CLEAN_RC_STICKY_DROP == 0x10000000u, "band width");
    _Static_assert(0u - CLEAN_RC_STICKY == 0x10000000u, "room past STICKY");
    _Static_assert(CLEAN_RC_INC_MAX == 0x10000, "INC_MAX");
    printf("ok\n");"#,
        "ok\n",
    );
}

// ---------------------------------------------------------------------------
// The deletion worklist
// ---------------------------------------------------------------------------

#[test]
fn c_rc_deep_first_field_chain_frees_without_recursion() {
    // A 1,000,000-node chain through field 0 on a fixed 1 MiB thread stack
    // (independent of `ulimit -s`). Recursion on every field but the last
    // overflowed it; the worklist frees it in constant C stack.
    let main_c = format!(
        r#"{PRELUDE}
static void* deep_chain(void* arg) {{
    (void)arg;
    clean_obj* head = clean_box(0);
    for (int i = 0; i < 1000000; i++) head = clean_alloc_ctor(0, 2, 0, head, clean_box(0));
    clean_dec(head);
    printf("freed\n");
    fflush(stdout);
    return NULL;
}}
int main(void) {{
    pthread_attr_t a;
    pthread_attr_init(&a);
    pthread_attr_setstacksize(&a, (size_t)1 << 20);
    pthread_t t;
    if (pthread_create(&t, &a, deep_chain, NULL) != 0) {{ printf("pthread_create\n"); return 1; }}
    pthread_join(t, NULL);
    printf("done\n");
    return 0;
}}
"#
    );
    assert_program_prints("deep first-field chain", &main_c, "freed\ndone\n");
}

#[test]
fn c_rc_cascade_shared_child_drops_to_exclusive() {
    // Lean's shared-child control: a child with two references whose parent
    // dies keeps its other reference and is not freed.
    assert_prints(
        "shared child",
        r#"    clean_obj* c = leaf(4);
    set_rc(c, 1);
    clean_dec(clean_alloc_ctor(0, 1, 0, c));
    printf("%u %u\n", rc(c), (unsigned)c->header.tag);
    clean_dec(c);"#,
        "0 4\n",
    );
}

#[test]
fn c_rc_cascade_spills_worklist_past_64_and_128() {
    // 200 pending children (each holding the witness `w`) cross the 64-entry
    // on-stack buffer (malloc + copy) and its first doubling (realloc). Every
    // child is processed exactly once: w's 200 extra references come back.
    assert_prints(
        "worklist spill",
        r#"    clean_obj* w = leaf(9);
    clean_obj* kids[200];
    for (int i = 0; i < 200; i++) { clean_inc(w); kids[i] = clean_alloc_ctor(1, 1, 0, w); }
    clean_obj* p = clean_alloc_ctor_uninit(0, 200, 0);
    for (int i = 0; i < 200; i++) p->fields[i] = kids[i];
    printf("%u ", rc(w));
    clean_dec(p);
    printf("%u\n", rc(w));
    clean_dec(w);"#,
        "200 0\n",
    );
}

#[test]
fn c_rc_cascade_shared_children_free_once() {
    // One child in two fields of one dying parent, and one child under two
    // dying parents: each is freed once, so each returns one witness
    // reference.
    assert_prints(
        "shared children",
        r#"    clean_obj* w = leaf(9);
    clean_inc(w);
    clean_obj* c1 = clean_alloc_ctor(1, 1, 0, w);
    clean_inc(c1);
    clean_dec(clean_alloc_ctor(0, 2, 0, c1, c1));
    printf("%u ", rc(w));
    clean_inc(w);
    clean_obj* c2 = clean_alloc_ctor(1, 1, 0, w);
    clean_inc(c2);
    clean_obj* p1 = clean_alloc_ctor(2, 1, 0, c2);
    clean_obj* p2 = clean_alloc_ctor(2, 1, 0, c2);
    clean_dec(clean_alloc_ctor(3, 2, 0, p1, p2));
    printf("%u\n", rc(w));
    clean_dec(w);"#,
        "0 0\n",
    );
}

#[test]
fn c_rc_cascade_closure_args_skip_frozen_child() {
    // A dying closure's captured args go through the same worklist: a frozen
    // arg is untouched, an exclusive one is freed (its witness comes back),
    // a scalar is skipped.
    assert_prints(
        "closure args",
        r#"    clean_obj* w = leaf(9);
    clean_inc(w);
    clean_obj* frozen = leaf(5);
    set_rc(frozen, 0xF8000000u);
    clean_obj* uniq = clean_alloc_ctor(1, 1, 0, w);
    clean_obj* clo = clean_alloc_closure(NULL, 4, 3, frozen, uniq, clean_box(7));
    clean_dec(clo);
    printf("%08x %u\n", rc(frozen), rc(w));
    release(frozen);
    clean_dec(w);"#,
        "f8000000 0\n",
    );
}

// ---------------------------------------------------------------------------
// The trust-cg lane: the exported forwarders of runtime_extern.c
// ---------------------------------------------------------------------------

/// A TU that does not include the header: it binds the exported symbols a
/// trust-cg object binds, by their ABI prototypes.
const PROBE_C: &str = r#"#include <stdbool.h>
#include <stddef.h>
struct clean_obj;
void clean_inc(struct clean_obj*);
void clean_dec(struct clean_obj*);
bool clean_is_exclusive(struct clean_obj*);
void probe_inc(struct clean_obj* o) { clean_inc(o); }
void probe_dec(struct clean_obj* o) { clean_dec(o); }
bool probe_is_exclusive(struct clean_obj* o) { return clean_is_exclusive(o); }
"#;

#[test]
fn c_rc_extern_lane_forwarders_honour_band() {
    let main_c = format!(
        r#"{PRELUDE}
void probe_inc(clean_obj*);
void probe_dec(clean_obj*);
bool probe_is_exclusive(clean_obj*);
int main(void) {{
    clean_obj* a = leaf(1);
    set_rc(a, 0xFFFFFFFFu);
    probe_inc(a);
    printf("%u %d ", rc(a), (int)probe_is_exclusive(a));
    release(a);
    clean_obj* b = leaf(1);
    set_rc(b, 0xF8000000u);
    for (uint32_t i = 0; i < (1u << 20); i++) probe_dec(b);
    printf("%u ", rc(b));
    release(b);
    clean_obj* c = leaf(3);
    set_rc(c, 0xF8000000u);
    probe_dec(clean_alloc_ctor(1, 1, 0, c));
    printf("%u\n", rc(c));
    release(c);
    return 0;
}}
"#
    );
    for build in [Build::Plain, Build::AddressSanitizer] {
        let out = build_and_run(&main_c, Some(PROBE_C), build);
        assert_eq!(
            out, "4294967295 0 4160749568 4160749568\n",
            "(a), (b), (c) through the exported forwarders ({build:?})"
        );
    }
}

#[test]
fn c_rc_extern_lane_inc_n_is_size_t() {
    // The exported clean_inc_n takes a size_t: (d) through the forwarder.
    let probe = format!(
        "{PROBE_C}void clean_inc_n(struct clean_obj*, size_t);\n\
         void probe_inc_n(struct clean_obj* o, size_t n) {{ clean_inc_n(o, n); }}\n"
    );
    let main_c = format!(
        r#"{PRELUDE}
void probe_inc_n(clean_obj*, size_t);
bool probe_is_exclusive(clean_obj*);
int main(void) {{
    clean_obj* o = leaf(0);
    probe_inc_n(o, past_u32_n);
    uint32_t c = rc(o);
    printf("%d %d ", c >= 0xF0000000u && c < 0xF0010000u, (int)probe_is_exclusive(o));
    set_rc(o, 0);
    probe_inc_n(o, 0x10001);
    printf("%08x\n", rc(o));
    release(o);
    return 0;
}}
"#
    );
    for build in [Build::Plain, Build::AddressSanitizer] {
        let out = build_and_run(&main_c, Some(&probe), build);
        assert_eq!(
            out, "1 0 00010001\n",
            "(d) through the exported forwarder ({build:?})"
        );
    }
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! clean Runtime Library
//!
//! Provides C runtime support for compiled clean programs. This crate:
//! 1. Embeds the C header files needed by generated code
//! 2. Provides build integration for compiling generated C code
//! 3. Contains reference counting and memory management primitives
//!
//! # Usage
//!
//! Generated C code includes `clean_runtime.h` which provides:
//! - Object representation (clean_obj)
//! - Reference counting (clean_inc, clean_dec)
//! - Constructor allocation (clean_alloc_ctor)
//! - Field access (clean_ctor_get, clean_ctor_set)
//! - Tagged pointers (clean_box, clean_unbox)
//!
//! # Architecture
//!
//! Based on Lean 4's runtime (lean4/src/runtime/).
//!
//! Part of #963 - Compiler IR infrastructure (Phase 4).

pub mod ffi_bridge;
pub mod ffi_exports;
pub mod io_runtime;
pub mod native;
pub(crate) mod object_model;
pub(crate) mod rc_core;
#[cfg(test)]
mod rc_sticky_tests;
pub mod runtime;
pub mod task;

// Re-export public runtime API at crate root so generated code can use
// `use clean_runtime::*;` to access all clean_* functions and the CleanObj type.
// Part of #2005 Phase 2.
pub use runtime::{
    clean_alloc_array, clean_alloc_closure, clean_alloc_ctor, clean_alloc_external,
    clean_alloc_task, clean_alloc_thunk, clean_array_data, clean_array_fget, clean_array_fset,
    clean_array_fswap, clean_array_get, clean_array_get_checked, clean_array_get_size,
    clean_array_pop, clean_array_push, clean_array_set, clean_array_size, clean_array_swap,
    clean_array_uget, clean_array_uset, clean_array_uswap, clean_box, clean_box_float,
    clean_box_uint32, clean_box_uint64, clean_closure_apply, clean_closure_arg,
    clean_closure_arity, clean_closure_func, clean_closure_num_fixed, clean_copy_array,
    clean_ctor_get, clean_ctor_get_float, clean_ctor_get_float32, clean_ctor_get_uint16,
    clean_ctor_get_uint32, clean_ctor_get_uint64, clean_ctor_get_uint8, clean_ctor_get_usize,
    clean_ctor_set, clean_ctor_set_float, clean_ctor_set_float32, clean_ctor_set_tag,
    clean_ctor_set_uint16, clean_ctor_set_uint32, clean_ctor_set_uint64, clean_ctor_set_uint8,
    clean_ctor_set_usize, clean_dec, clean_ensure_exclusive_array, clean_inc, clean_inc_n,
    clean_is_exclusive, clean_is_scalar, clean_is_unique, clean_mk_array, clean_mk_empty_array,
    clean_mk_empty_array_with_capacity, clean_mk_string, clean_mk_string_from_bytes, clean_nat_big,
    clean_nat_from_limbs, clean_nat_limb_step, clean_nat_to_limbs, clean_obj_tag, clean_panic,
    clean_reset, clean_reuse, clean_reuse_slot, clean_runtime_finalize, clean_runtime_init,
    clean_string_data, clean_string_len, clean_unbox, clean_unbox_float, clean_unbox_uint32,
    clean_unbox_uint64, CleanExternalClass, CleanObj, LeanObjPtr,
};

use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

/// File name generated code `#include`s; the only file `include/` holds.
const RUNTIME_HEADER_FILE: &str = "clean_runtime.h";

/// Why [`try_include_dir`] could not produce a directory holding the header.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum IncludeDirError {
    /// The cache directory under `std::env::temp_dir()` could not be created.
    #[error("cannot create runtime include cache directory {dir}: {source}")]
    CreateDir {
        /// The directory that could not be created.
        dir: PathBuf,
        /// The underlying I/O failure.
        #[source]
        source: io::Error,
    },
    /// The header could not be written to its per-process staging file.
    #[error("cannot write runtime header staging file {path}: {source}")]
    WriteStaging {
        /// The staging file that could not be written.
        path: PathBuf,
        /// The underlying I/O failure.
        #[source]
        source: io::Error,
    },
    /// The fully written staging file could not be renamed into place.
    #[error("cannot move runtime header staging file {from} into place at {to}: {source}")]
    Rename {
        /// The staging file.
        from: PathBuf,
        /// The final header path.
        to: PathBuf,
        /// The underlying I/O failure.
        #[source]
        source: io::Error,
    },
    /// After the rename the file did not read back as the embedded header.
    #[error("{path} does not hold the embedded runtime header after materialization")]
    Verify {
        /// The header path that failed the read-back.
        path: PathBuf,
    },
}

/// Get the path to a directory containing `clean_runtime.h`.
///
/// The returned directory holds a `clean_runtime.h` byte-identical to
/// [`runtime_header`] — the copy embedded in this binary — or, if that could
/// not be arranged, the cache directory that materialization failed in (never
/// a path this function merely hopes holds the header).
///
/// Resolution order:
/// 1. The crate's own `include/` directory as recorded at compile time
///    (`CARGO_MANIFEST_DIR`), **only when** it actually holds that header.
/// 2. Otherwise the embedded header is materialized into
///    `std::env::temp_dir()/clean-runtime-include-<fnv1a64 of the header>/`
///    (idempotent; written to a per-process staging file and renamed into
///    place, so two processes racing cannot tear it) and that directory is
///    returned.
///
/// Why not the compile-time path alone: it is wrong whenever the compiled
/// artifact outlives the source tree it was compiled from. Measured
/// 2026-09-15: the `libclean_runtime` rlib in the shared `target/debug` had
/// been compiled from a since-deleted gate-demonstration sandbox
/// (`.../T/clean-gate-demo/<id>/tree-build/crates/clean-runtime`), because
/// Cargo names a path dependency's artifacts by its workspace-RELATIVE path
/// and a sandbox build at another absolute root overwrites the real tree's
/// units; every `-I<that path>/include` then failed with
/// `fatal error: 'clean_runtime.h' file not found`. A relocated checkout or a
/// published crate whose `include/` is not on disk fails the same way.
///
/// Infallible by design: every caller today is a test that hands the result to
/// a C compiler as `-I`, and a test's only response to an error is to panic
/// with the same "file not found" the compiler already reports. Callers that
/// need to know WHY materialization failed use [`try_include_dir`].
pub fn include_dir() -> PathBuf {
    match try_include_dir() {
        Ok(dir) => dir,
        Err(_) => materialized_include_root(&std::env::temp_dir()),
    }
}

/// Fallible form of [`include_dir`]: the same resolution, but a directory is
/// returned only when it has been read back holding the embedded header.
pub fn try_include_dir() -> Result<PathBuf, IncludeDirError> {
    resolve_include_dir(&compile_time_include_dir(), &std::env::temp_dir())
}

/// The `include/` directory of the crate as it was laid out at compile time.
fn compile_time_include_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("include")
}

/// Prefer `compile_time` when it holds the embedded header; otherwise
/// materialize under `cache_root`.
fn resolve_include_dir(compile_time: &Path, cache_root: &Path) -> Result<PathBuf, IncludeDirError> {
    if holds_embedded_header(&compile_time.join(RUNTIME_HEADER_FILE)) {
        return Ok(compile_time.to_path_buf());
    }
    materialize_header(cache_root)
}

/// True when `path` reads back byte-identical to [`runtime_header`].
fn holds_embedded_header(path: &Path) -> bool {
    fs::read(path).is_ok_and(|bytes| bytes == runtime_header().as_bytes())
}

/// FNV-1a 64 over the header bytes: a dependency-free key that is stable
/// across toolchains (unlike `DefaultHasher`) and changes with the header's
/// content, so two binaries embedding different headers never share a cache
/// directory.
fn header_content_key(header: &[u8]) -> u64 {
    const OFFSET_BASIS: u64 = 0xcbf2_9ce4_8422_2325;
    const PRIME: u64 = 0x0000_0100_0000_01b3;
    header.iter().fold(OFFSET_BASIS, |hash, &byte| {
        (hash ^ u64::from(byte)).wrapping_mul(PRIME)
    })
}

/// The cache directory the embedded header is materialized into.
fn materialized_include_root(cache_root: &Path) -> PathBuf {
    cache_root.join(format!(
        "clean-runtime-include-{:016x}",
        header_content_key(runtime_header().as_bytes())
    ))
}

/// Distinguishes staging files written by different threads of one process;
/// the process id distinguishes processes.
static STAGING_COUNTER: AtomicU64 = AtomicU64::new(0);

/// Write the embedded header into its cache directory under `cache_root`,
/// unless a byte-identical copy is already there.
///
/// The write goes to a staging file unique to this process and thread and is
/// then `rename`d over the final name in the same directory. On POSIX that is
/// `rename(2)`, which replaces the target atomically, so a concurrent reader
/// sees either no header, the previous complete header, or the new complete
/// one — never a partial file. On Windows `std::fs::rename` is
/// `MoveFileExW(MOVEFILE_REPLACE_EXISTING)`, which is not documented atomic;
/// there the read-back below is what a caller's guarantee rests on. Two
/// racing writers produce identical files, so whichever rename lands last
/// changes nothing.
fn materialize_header(cache_root: &Path) -> Result<PathBuf, IncludeDirError> {
    let dir = materialized_include_root(cache_root);
    let target = dir.join(RUNTIME_HEADER_FILE);
    if holds_embedded_header(&target) {
        return Ok(dir);
    }
    fs::create_dir_all(&dir).map_err(|source| IncludeDirError::CreateDir {
        dir: dir.clone(),
        source,
    })?;
    let staging = dir.join(format!(
        ".{RUNTIME_HEADER_FILE}.{}.{}.tmp",
        std::process::id(),
        STAGING_COUNTER.fetch_add(1, Ordering::Relaxed)
    ));
    if let Err(source) = fs::write(&staging, runtime_header()) {
        let _ = fs::remove_file(&staging);
        return Err(IncludeDirError::WriteStaging {
            path: staging,
            source,
        });
    }
    if let Err(source) = fs::rename(&staging, &target) {
        let _ = fs::remove_file(&staging);
        return Err(IncludeDirError::Rename {
            from: staging,
            to: target,
            source,
        });
    }
    if !holds_embedded_header(&target) {
        return Err(IncludeDirError::Verify { path: target });
    }
    Ok(dir)
}

/// Get the C header content as a string.
///
/// Useful for embedding the runtime header directly without file system access.
pub fn runtime_header() -> &'static str {
    include_str!("../include/clean_runtime.h")
}

/// Get the C runtime implementation source as a string.
///
/// Returns the full text of `clean_runtime.c`. Useful for the native
/// build-and-run path (`clean run`), which writes this alongside
/// [`runtime_header`] into a scratch directory and `cc`-compiles it together
/// with generated code into a self-contained executable — no prebuilt
/// `libclean_runtime.a` or `CARGO_MANIFEST_DIR` path is required at run time.
///
/// The first line of the shipped file is `#include "../include/clean_runtime.h"`,
/// a path relative to the crate layout. Callers that materialize this source in
/// a flat directory should drop [`runtime_header`] next to it as
/// `clean_runtime.h` and rewrite that include to `"clean_runtime.h"` (or pass an
/// appropriate `-I`).
pub fn runtime_source() -> &'static str {
    include_str!("clean_runtime.c")
}

/// Get the external-symbol materialization TU as a string.
///
/// The RC / box / field-access primitives in `clean_runtime.h` are declared
/// `static inline` (internal linkage — no exported symbol). The `emit_c`
/// backend inlines them directly; the `trust-cg` backend lowers them to
/// *external calls* and therefore needs a real, link-visible definition of
/// each. This translation unit ([`runtime_extern.c`](../src/runtime_extern.c))
/// exports one authoritative external forwarder per header primitive WITHOUT
/// modifying the header (so `emit_c` still inlines) or [`runtime_source`] (so
/// the runtime still compiles standalone).
///
/// Compile it into its own object and link it alongside the runtime object for
/// any consumer that binds runtime primitives at link time (the trust-cg
/// object path). It is a no-op for `emit_c`, whose emitted program inlines its
/// own copies and never references these external symbols. Like
/// [`runtime_source`] its first line is a crate-relative
/// `#include "../include/clean_runtime.h"`; materialize [`runtime_header`] next
/// to it (or pass an appropriate `-I`).
pub fn runtime_extern_source() -> &'static str {
    include_str!("runtime_extern.c")
}

/// Optional source DATA for the scalar UInt64 externs in a retained Lean header.
///
/// Materialize this separate translation unit with that header's actual include
/// directory. The external functions forward its inline definitions, following
/// the same materialization pattern as [`runtime_extern_source`]. This accessor
/// does not choose a toolchain, compile/link a runtime, supply boxed adapters,
/// change the default runtime, or establish source/ABI/ownership/NoUB evidence.
#[must_use]
pub fn lean_word64_extern_source() -> &'static str {
    include_str!("lean_word64_extern.c")
}

/// Get the runtime object file path (if compiled).
pub fn runtime_lib() -> Option<PathBuf> {
    let lib_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("target")
        .join("libclean_runtime.a");
    if lib_path.exists() {
        Some(lib_path)
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn read_header(dir: &Path) -> String {
        fs::read_to_string(dir.join(RUNTIME_HEADER_FILE))
            .unwrap_or_else(|err| panic!("{} should be readable: {err}", dir.display()))
    }

    /// Directory entries of `dir`, sorted — the staging-file check.
    fn entries(dir: &Path) -> Vec<String> {
        let mut names: Vec<String> = fs::read_dir(dir)
            .expect("cache directory should be listable")
            .map(|entry| {
                entry
                    .expect("directory entry should be readable")
                    .file_name()
                    .to_string_lossy()
                    .into_owned()
            })
            .collect();
        names.sort();
        names
    }

    /// The contract every caller relies on: whatever branch resolved, the
    /// returned directory holds THE header this binary embeds.
    #[test]
    fn test_include_dir_holds_the_embedded_header() {
        let dir = include_dir();
        assert_eq!(read_header(&dir), runtime_header());
        let checked = try_include_dir().expect("header should be resolvable or materializable");
        assert_eq!(checked, dir);
    }

    #[test]
    fn test_resolve_include_dir_prefers_compile_time_dir_that_holds_the_header() {
        let tree = tempfile::tempdir().expect("tempdir");
        let include = tree.path().join("include");
        fs::create_dir_all(&include).expect("create include dir");
        fs::write(include.join(RUNTIME_HEADER_FILE), runtime_header()).expect("write header");
        let cache = tempfile::tempdir().expect("tempdir");

        let got = resolve_include_dir(&include, cache.path()).expect("resolve");

        assert_eq!(got, include);
        assert!(
            entries(cache.path()).is_empty(),
            "no cache directory should be created when the compile-time one serves"
        );
    }

    #[test]
    fn test_resolve_include_dir_materializes_when_compile_time_dir_is_absent() {
        let tree = tempfile::tempdir().expect("tempdir");
        let absent = tree.path().join("include");
        let cache = tempfile::tempdir().expect("tempdir");

        let got = resolve_include_dir(&absent, cache.path()).expect("materialize");

        assert_eq!(got, materialized_include_root(cache.path()));
        assert_eq!(read_header(&got), runtime_header());
        assert_eq!(
            entries(&got),
            vec![RUNTIME_HEADER_FILE.to_string()],
            "only the header, no staging file, may remain"
        );
    }

    #[test]
    fn test_resolve_include_dir_ignores_a_compile_time_header_that_differs() {
        // A stale binary next to an edited tree: the tree's header is not the
        // one this binary embeds, so it must not be served.
        let tree = tempfile::tempdir().expect("tempdir");
        let include = tree.path().join("include");
        fs::create_dir_all(&include).expect("create include dir");
        fs::write(
            include.join(RUNTIME_HEADER_FILE),
            format!(
                "{}\n/* edited after this binary was built */\n",
                runtime_header()
            ),
        )
        .expect("write header");
        let cache = tempfile::tempdir().expect("tempdir");

        let got = resolve_include_dir(&include, cache.path()).expect("materialize");

        assert_ne!(got, include);
        assert_eq!(read_header(&got), runtime_header());
    }

    #[test]
    fn test_materialize_header_replaces_a_stale_cache_entry() {
        let cache = tempfile::tempdir().expect("tempdir");
        let dir = materialized_include_root(cache.path());
        fs::create_dir_all(&dir).expect("create cache dir");
        fs::write(dir.join(RUNTIME_HEADER_FILE), "/* torn or foreign */").expect("write stale");

        let got = materialize_header(cache.path()).expect("materialize");

        assert_eq!(got, dir);
        assert_eq!(read_header(&got), runtime_header());
        assert_eq!(entries(&got), vec![RUNTIME_HEADER_FILE.to_string()]);
    }

    #[test]
    fn test_materialize_header_is_idempotent() {
        let cache = tempfile::tempdir().expect("tempdir");

        let first = materialize_header(cache.path()).expect("first materialization");
        let second = materialize_header(cache.path()).expect("second materialization");

        assert_eq!(first, second);
        assert_eq!(read_header(&second), runtime_header());
        assert_eq!(entries(&second), vec![RUNTIME_HEADER_FILE.to_string()]);
    }

    #[test]
    fn test_materialize_header_fails_closed_when_cache_root_is_a_file() {
        let tree = tempfile::tempdir().expect("tempdir");
        let not_a_dir = tree.path().join("not-a-dir");
        fs::write(&not_a_dir, "").expect("write file");

        let err = materialize_header(&not_a_dir).expect_err("a file cannot be a cache root");

        assert!(
            matches!(err, IncludeDirError::CreateDir { .. }),
            "unexpected error: {err}"
        );
    }

    #[test]
    fn test_header_content_key_is_fnv1a64_and_content_sensitive() {
        // Published FNV-1a 64 vectors.
        assert_eq!(header_content_key(b""), 0xcbf2_9ce4_8422_2325);
        assert_eq!(header_content_key(b"a"), 0xaf63_dc4c_8601_ec8c);
        let header = runtime_header().as_bytes();
        let edited = [header, b"\n"].concat();
        assert_ne!(header_content_key(header), header_content_key(&edited));
    }

    #[test]
    fn test_runtime_header_not_empty() {
        let header = runtime_header();
        assert!(header.contains("clean_obj"));
        assert!(header.contains("clean_inc"));
    }

    #[test]
    fn test_runtime_header_uses_relaxed_is_exclusive_contract() {
        let header = runtime_header();
        let block_start = header
            .find("/* Check if object is exclusively owned")
            .expect("clean_is_exclusive comment should be present in runtime header");
        let block_end = header[block_start..]
            .find("/* ============================================================================")
            .map(|offset| block_start + offset)
            .expect("clean_is_exclusive block should end before the allocation section");
        let is_exclusive_block = &header[block_start..block_end];

        assert!(
            is_exclusive_block.contains("memory_order_relaxed"),
            "clean_is_exclusive should use memory_order_relaxed in the shipped header"
        );
        assert!(
            is_exclusive_block
                .contains("Relaxed suffices: is_unique is a hint for reuse optimization."),
            "clean_is_exclusive should document why Relaxed ordering is sufficient"
        );
        assert!(
            is_exclusive_block.contains("Matches Lean 4 lean_is_exclusive (lean.h:550)."),
            "clean_is_exclusive should cite the Lean 4 naming/ordering contract"
        );
    }
}

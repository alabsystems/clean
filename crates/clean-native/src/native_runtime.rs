// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean native-runtime` — materialize the linkable Clean runtime archive.
//!
//! Two-language roadmap WS6.13 (F-119, scout-lean B7/C3). An object emitted
//! by `clean compile --emit obj` (trust-ir lowered through trust-cg) leaves
//! exactly two kinds of symbol for the link to resolve: the `clean_*` runtime
//! primitives, which trust-cg lowers to EXTERNAL calls (the `emit_c` backend
//! inlines them from the header instead), and the `l_*` prelude externs the
//! lowering denylists so they stay shims. Neither is a C file a packer can
//! copy: the runtime sources are embedded in `clean-runtime`, and the prelude
//! shims are Rust string tables in [`crate::native_build`]. So the archive
//! ships INSIDE the `clean` binary, and this verb writes it out for the host:
//!
//! | member                  | source                                   | defines               |
//! |-------------------------|------------------------------------------|-----------------------|
//! | `clean_runtime.o`       | [`clean_runtime::runtime_source`]        | the runtime proper    |
//! | `runtime_extern.o`      | [`clean_runtime::runtime_extern_source`] | one exported forwarder per header `static inline` primitive (`clean_inc`, `clean_box`, `clean_ctor_get`, …) |
//! | `clean_prelude_shims.o` | [`crate::native_build::prelude_shims_translation_unit`] | every `l_*` prelude shim (`l_Nat_add`, `l_Nat_land`, …) |
//!
//! The three are archived as `libclean_runtime.a`; a consumer links
//! `cc <emitted>.o libclean_runtime.a -lm`. `--sources-only` writes the
//! header and the three `.c` files without compiling, for a packer that
//! builds the archive with its own toolchain.
//!
//! Fail closed: a missing C compiler or `ar` is an error naming the override
//! variable, never a partial archive, and a run — `--sources-only` included —
//! first removes any `libclean_runtime.a` / member `.o` an earlier run left
//! in `--out-dir`, so the directory never holds a product this run did not
//! make ([`remove_stale_products`]). A compiler or archiver that exits
//! non-zero after writing part of its output has that output removed too
//! (`fail_discarding`), and one that exits zero without writing is refused
//! by name. There is no CLI knob to drop a member —
//! the archive is the whole runtime or nothing; the mutation control in the
//! tests removes `runtime_extern.o` from a BUILT archive with `ar d` and
//! checks the link fails by exactly `clean_inc`.
//!
//! This module owns the step and [`materialize`] is its one entry point;
//! clean-cli's `cmd_native_runtime` is the front door (argument parsing and
//! the stdout sink), as for every other step of Clean's native core (LX0(b),
//! `docs/DECISIONS.md` R12). The verb landed in clean-cli before that move;
//! the shim tables it renders moved here with `native_build`, so it follows.

use std::fmt;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{anyhow, bail, Context};

use crate::native_build::{find_c_compiler, prelude_shims_translation_unit};

/// The header every member (and every emitted object) is compiled against.
pub(crate) const RUNTIME_HEADER_NAME: &str = "clean_runtime.h";
/// The archive `clean native-runtime` produces.
pub(crate) const ARCHIVE_NAME: &str = "libclean_runtime.a";

/// One member of the runtime archive, in link order.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum RuntimeMember {
    /// The Clean C runtime proper (`clean_runtime.c`).
    Runtime,
    /// External forwarders for the header's `static inline` primitives
    /// (`runtime_extern.c`), which trust-cg objects bind at link time.
    RuntimeExtern,
    /// The prelude shim union (`clean_prelude_shims.c`), rendered from the
    /// `native_build` shim tables.
    PreludeShims,
}

impl RuntimeMember {
    /// Every member, in the order the archive lists them.
    pub(crate) const ALL: [RuntimeMember; 3] = [
        RuntimeMember::Runtime,
        RuntimeMember::RuntimeExtern,
        RuntimeMember::PreludeShims,
    ];

    /// The `.c` file name the member is written as.
    pub(crate) fn source_name(self) -> &'static str {
        match self {
            RuntimeMember::Runtime => "clean_runtime.c",
            RuntimeMember::RuntimeExtern => "runtime_extern.c",
            RuntimeMember::PreludeShims => "clean_prelude_shims.c",
        }
    }

    /// The `.o` member name inside the archive.
    pub(crate) fn object_name(self) -> &'static str {
        match self {
            RuntimeMember::Runtime => "clean_runtime.o",
            RuntimeMember::RuntimeExtern => "runtime_extern.o",
            RuntimeMember::PreludeShims => "clean_prelude_shims.o",
        }
    }

    /// The member's C text, with the crate-relative header include
    /// flattened to `"clean_runtime.h"` so a flat directory compiles.
    pub(crate) fn source_text(self) -> String {
        let flat = |src: &str| src.replacen("../include/clean_runtime.h", RUNTIME_HEADER_NAME, 1);
        match self {
            RuntimeMember::Runtime => flat(clean_runtime::runtime_source()),
            RuntimeMember::RuntimeExtern => flat(clean_runtime::runtime_extern_source()),
            RuntimeMember::PreludeShims => prelude_shims_translation_unit(&[]),
        }
    }
}

impl fmt::Display for RuntimeMember {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.object_name())
    }
}

/// The header and sources written by [`write_runtime_sources`].
#[derive(Debug)]
pub(crate) struct RuntimeSources {
    pub(crate) header: PathBuf,
    pub(crate) sources: Vec<(RuntimeMember, PathBuf)>,
}

/// The archive written by [`build_runtime_archive`].
#[derive(Debug)]
pub(crate) struct RuntimeArchive {
    pub(crate) path: PathBuf,
    pub(crate) objects: Vec<(RuntimeMember, PathBuf)>,
    pub(crate) cc: String,
    pub(crate) ar: String,
}

/// Write `clean_runtime.h` and the three member sources into `dir`.
pub(crate) fn write_runtime_sources(dir: &Path) -> anyhow::Result<RuntimeSources> {
    std::fs::create_dir_all(dir).with_context(|| format!("failed to create {}", dir.display()))?;
    let header = dir.join(RUNTIME_HEADER_NAME);
    std::fs::write(&header, clean_runtime::runtime_header())
        .with_context(|| format!("failed to write {}", header.display()))?;
    let mut sources = Vec::with_capacity(RuntimeMember::ALL.len());
    for member in RuntimeMember::ALL {
        let path = dir.join(member.source_name());
        std::fs::write(&path, member.source_text())
            .with_context(|| format!("failed to write {}", path.display()))?;
        sources.push((member, path));
    }
    Ok(RuntimeSources { header, sources })
}

/// Remove the products an earlier run may have left in `dir` —
/// `libclean_runtime.a` and the `.o` of each of `members` — and return what
/// was removed.
///
/// Runs BEFORE anything is compiled (in [`build_runtime_archive`]) and in
/// `--sources-only` mode too: a consumer that reads the directory rather
/// than the exit code must never find an archive or object this run did not
/// produce. The first cut removed the archive only after every compile had
/// succeeded, so a failed rebuild silently kept the previous archive; and
/// `--sources-only` removed nothing, so fresh sources sat beside an archive
/// compiled from an OLDER binary's sources — a stale archive dressed as the
/// output of the run that wrote the sources (review of WS6.13). A dangling
/// symlink counts as present (`symlink_metadata`, not `exists`).
pub(crate) fn remove_stale_products(
    dir: &Path,
    members: &[RuntimeMember],
) -> anyhow::Result<Vec<PathBuf>> {
    let mut candidates = vec![dir.join(ARCHIVE_NAME)];
    candidates.extend(members.iter().map(|m| dir.join(m.object_name())));
    let mut removed = Vec::new();
    for path in candidates {
        if path.symlink_metadata().is_ok() {
            std::fs::remove_file(&path)
                .with_context(|| format!("failed to remove stale {}", path.display()))?;
            removed.push(path);
        }
    }
    Ok(removed)
}

/// Locate `ar`: `$CLEAN_AR`, `$AR`, then `ar` on PATH.
fn find_archiver() -> Option<String> {
    for var in ["CLEAN_AR", "AR"] {
        if let Ok(value) = std::env::var(var) {
            if !value.trim().is_empty() {
                return Some(value);
            }
        }
    }
    // `ar` has no `--version` on macOS (BSD ar), so the probe is `ar -V`:
    // GNU ar prints its version, BSD ar prints usage and exits non-zero.
    // Either way a spawned process proves the program runs; only a
    // failure to spawn (not on PATH) reads as absent.
    Command::new("ar")
        .arg("-V")
        .output()
        .ok()
        .map(|_| "ar".to_string())
}

/// Remove what a tool that FAILED may have half-written at `partial` (a
/// dangling symlink counts), and return `failure` — with the removal error
/// attached if the partial product could not be removed, so a leftover is
/// never silent.
fn fail_discarding(partial: &Path, failure: anyhow::Error) -> anyhow::Error {
    if partial.symlink_metadata().is_err() {
        return failure;
    }
    match std::fs::remove_file(partial) {
        Ok(()) => failure,
        Err(e) => failure.context(format!(
            "and the partial product {} could not be removed ({e}); do not use it",
            partial.display()
        )),
    }
}

/// Compile `members` (each already written by [`write_runtime_sources`]) to
/// objects and archive them as `libclean_runtime.a` in `dir`.
///
/// `members` is a parameter so the tests can build a deliberately incomplete
/// archive; the CLI always passes [`RuntimeMember::ALL`].
pub(crate) fn build_runtime_archive(
    dir: &Path,
    members: &[RuntimeMember],
) -> anyhow::Result<RuntimeArchive> {
    build_runtime_archive_with(dir, members, find_c_compiler, find_archiver)
}

/// [`build_runtime_archive`] with the tool lookups as parameters, so the
/// tests can hand it a compiler or archiver that misbehaves without editing
/// the process environment other tests read. The lookups still run AFTER
/// the stale products are gone.
fn build_runtime_archive_with(
    dir: &Path,
    members: &[RuntimeMember],
    find_cc: impl FnOnce() -> Option<String>,
    find_ar: impl FnOnce() -> Option<String>,
) -> anyhow::Result<RuntimeArchive> {
    if members.is_empty() {
        bail!("refusing to build an empty runtime archive");
    }
    // Stale products go FIRST — before the tool lookups, not only before the
    // compiles: a run that fails for ANY reason (no compiler on PATH
    // included) must leave no archive, stale or partial, for a consumer that
    // reads the directory rather than the exit code. Stale members an
    // earlier archive carried would likewise survive an `ar rcs` update.
    remove_stale_products(dir, members)?;
    let cc = find_cc().ok_or_else(|| {
        anyhow!(
            "no C compiler found to build the runtime archive. Set CLEAN_CC or CC, or install \
             one of: cc, gcc, clang. Pass --sources-only to write the sources without compiling."
        )
    })?;
    let ar = find_ar().ok_or_else(|| {
        anyhow!(
            "no archiver found to build the runtime archive. Set CLEAN_AR or AR, or install `ar` \
             (binutils / Xcode command line tools). Pass --sources-only to write the sources \
             without compiling."
        )
    })?;

    let archive = dir.join(ARCHIVE_NAME);
    let mut objects = Vec::with_capacity(members.len());
    for &member in members {
        let source = dir.join(member.source_name());
        if !source.is_file() {
            bail!(
                "runtime source {} is missing; write_runtime_sources must run first",
                source.display()
            );
        }
        let object = dir.join(member.object_name());
        let output = crate::native_c_toolchain::command(&cc)?
            .arg("-O2")
            .arg("-std=c11")
            .arg("-I")
            .arg(dir)
            .arg("-c")
            .arg(&source)
            .arg("-o")
            .arg(&object)
            .output()
            .with_context(|| format!("failed to launch C compiler {cc}"))?;
        if !output.status.success() {
            // A compiler may write (part of) the object before it fails; that
            // object is no product of a successful compile, so it goes.
            return Err(fail_discarding(
                &object,
                anyhow!(
                    "C compile of {} failed.\n  command: {cc} -O2 -std=c11 -I {} -c {} -o {}\n  stderr:\n{}",
                    member.source_name(),
                    dir.display(),
                    source.display(),
                    object.display(),
                    String::from_utf8_lossy(&output.stderr)
                ),
            ));
        }
        if !object.is_file() {
            bail!(
                "C compiler reported success but produced no object at {}",
                object.display()
            );
        }
        objects.push((member, object));
    }

    let output = Command::new(&ar)
        .arg("rcs")
        .arg(&archive)
        .args(objects.iter().map(|(_, path)| path))
        .output()
        .with_context(|| format!("failed to launch archiver {ar}"))?;
    if !output.status.success() {
        // An archiver that fails mid-write can leave a truncated archive at
        // the final path; the stale-product removal above ran before it, so
        // this is the only place that partial file can be caught.
        return Err(fail_discarding(
            &archive,
            anyhow!(
                "archiving {} failed.\n  stderr:\n{}",
                archive.display(),
                String::from_utf8_lossy(&output.stderr)
            ),
        ));
    }
    if !archive.is_file() {
        bail!(
            "archiver reported success but produced no archive at {}",
            archive.display()
        );
    }
    Ok(RuntimeArchive {
        path: archive,
        objects,
        cc,
        ar,
    })
}

/// Write the runtime sources into `dir` and, unless `sources_only`, build
/// them into `libclean_runtime.a` there, reporting each product to `out` as
/// it is made (`header:`, `source:`, `removed stale:`, `archive:`, `link:`
/// lines). `clean native-runtime --out-dir <dir> [--sources-only]` is this
/// call with stdout as `out`.
pub fn materialize(dir: &Path, sources_only: bool, out: &mut dyn Write) -> anyhow::Result<()> {
    let sources = write_runtime_sources(dir)?;
    writeln!(out, "header: {}", sources.header.display())?;
    for (member, path) in &sources.sources {
        writeln!(out, "source: {} ({})", path.display(), member.source_name())?;
    }
    // The sources just written are the only runtime products this run
    // vouches for: an archive or object an EARLIER run (possibly of an older
    // binary) left here would otherwise sit beside them as if it had been
    // compiled from them. Reported by name, in both modes; the build below
    // repeats the removal itself (a no-op now) so the library entry point
    // is fail-closed without this handler too.
    for path in remove_stale_products(dir, &RuntimeMember::ALL)? {
        writeln!(out, "removed stale: {}", path.display())?;
    }
    if sources_only {
        writeln!(
            out,
            "archive: not built (--sources-only); compile each source with `cc -std=c11 -I {} -c` \
             and archive the objects as {}",
            dir.display(),
            ARCHIVE_NAME
        )?;
        return Ok(());
    }
    let archive = build_runtime_archive(dir, &RuntimeMember::ALL)?;
    let members: Vec<&str> = archive
        .objects
        .iter()
        .map(|(member, _)| member.object_name())
        .collect();
    writeln!(
        out,
        "archive: {} (members: {}; cc: {}; ar: {})",
        archive.path.display(),
        members.join(" "),
        archive.cc,
        archive.ar
    )?;
    writeln!(
        out,
        "link: {} <emitted>.o {} -lm",
        archive.cc,
        archive.path.display()
    )?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::native_build::link_probe::{linker_undefined, retaining_driver};
    use std::collections::BTreeSet;

    /// The C compiler the archive tests link with. Not optional: the census
    /// LINK oracle and `clean run` both need one, and a test that skipped
    /// here would report a runtime archive nothing had linked.
    fn cc() -> String {
        find_c_compiler().expect("the runtime archive tests need a C compiler (cc, gcc or clang)")
    }

    /// Link a driver retaining `demand` against `archive`; the undefined
    /// symbols the linker names (empty on success). A failure naming none
    /// panics with the linker's stderr, so a broken archive cannot read as
    /// a pass.
    fn link_demand(dir: &Path, archive: &Path, demand: &BTreeSet<String>) -> BTreeSet<String> {
        let driver = retaining_driver(dir, demand);
        let cc = cc();
        let link = Command::new(&cc)
            .arg("-O0")
            .arg("-I")
            .arg(dir)
            .arg("-o")
            .arg(dir.join("driver"))
            .arg(&driver)
            .arg(archive)
            .arg("-lm")
            .output()
            .expect("spawn cc link");
        if link.status.success() {
            return BTreeSet::new();
        }
        let stderr = String::from_utf8_lossy(&link.stderr);
        let undefined = linker_undefined(&stderr);
        assert!(
            !undefined.is_empty(),
            "link failed without naming an undefined symbol:\n{stderr}"
        );
        undefined
    }

    /// One symbol from each member: `clean_alloc_ctor` is defined by the
    /// runtime proper, `clean_inc` ONLY by `runtime_extern.c` (the header
    /// holds a `static inline`, which exports nothing), `l_Nat_add` and the
    /// WS6.3 `l_Nat_land` only by the shim TU.
    fn representative_demand() -> BTreeSet<String> {
        ["clean_alloc_ctor", "clean_inc", "l_Nat_add", "l_Nat_land"]
            .into_iter()
            .map(str::to_owned)
            .collect()
    }

    fn archive_members(ar: &str, archive: &Path) -> Vec<String> {
        let out = Command::new(ar)
            .arg("t")
            .arg(archive)
            .output()
            .expect("spawn ar t");
        assert!(
            out.status.success(),
            "ar t failed: {}",
            String::from_utf8_lossy(&out.stderr)
        );
        String::from_utf8_lossy(&out.stdout)
            .lines()
            .map(|line| {
                // BSD ar prints bare member names; GNU ar too. Strip any
                // directory a future archiver might keep.
                Path::new(line.trim())
                    .file_name()
                    .map(|n| n.to_string_lossy().into_owned())
                    .unwrap_or_default()
            })
            .filter(|name| !name.is_empty() && !name.starts_with("__.SYMDEF"))
            .collect()
    }

    #[test]
    fn runtime_sources_are_the_embedded_runtime_and_the_whole_shim_union() {
        let dir = tempfile::tempdir().expect("tempdir");
        let written = write_runtime_sources(dir.path()).expect("write sources");
        assert_eq!(
            std::fs::read_to_string(&written.header).expect("read header"),
            clean_runtime::runtime_header()
        );
        let by_member = |member: RuntimeMember| {
            let (_, path) = written
                .sources
                .iter()
                .find(|(m, _)| *m == member)
                .expect("member written");
            std::fs::read_to_string(path).expect("read source")
        };
        let runtime = by_member(RuntimeMember::Runtime);
        assert!(
            runtime.contains("#include \"clean_runtime.h\"")
                && !runtime.contains("../include/clean_runtime.h"),
            "the crate-relative include must be flattened to the flat header name"
        );
        assert_eq!(
            runtime,
            clean_runtime::runtime_source().replacen(
                "../include/clean_runtime.h",
                "clean_runtime.h",
                1
            )
        );
        assert_eq!(
            by_member(RuntimeMember::RuntimeExtern),
            clean_runtime::runtime_extern_source().replacen(
                "../include/clean_runtime.h",
                "clean_runtime.h",
                1
            )
        );
        let shims = by_member(RuntimeMember::PreludeShims);
        for symbol in [
            "l_Nat_add",
            "l_Nat_land",
            "l_Nat_lor",
            "l_Nat_xor",
            "l_IO_println",
        ] {
            assert!(
                shims.contains(&format!("{symbol}(")),
                "shim TU must define {symbol}"
            );
        }
    }

    /// scout-lean C3 (F-119): "Emitted .o files were not linked/run (no clean
    /// runtime archive in the pack)". The archive the shipped binary writes
    /// resolves one symbol from each member class an emitted object demands.
    #[test]
    fn scout_lean_c3_runtime_archive_links_runtime_extern_and_shims() {
        let dir = tempfile::tempdir().expect("tempdir");
        write_runtime_sources(dir.path()).expect("write sources");
        let archive = build_runtime_archive(dir.path(), &RuntimeMember::ALL).expect("archive");
        assert_eq!(
            archive.path.file_name().and_then(|n| n.to_str()),
            Some(ARCHIVE_NAME)
        );
        assert_eq!(
            archive_members(&archive.ar, &archive.path),
            RuntimeMember::ALL
                .iter()
                .map(|m| m.object_name().to_owned())
                .collect::<Vec<_>>(),
            "the archive must list exactly the three members, in order"
        );
        let undefined = link_demand(dir.path(), &archive.path, &representative_demand());
        assert!(
            undefined.is_empty(),
            "the full runtime archive left symbols undefined: {undefined:?}"
        );
    }

    /// MUTATION CONTROL (the roadmap's): remove `runtime_extern.o` from the
    /// built archive. The link must fail by exactly the symbol that member
    /// defined — `clean_inc` — while the runtime and the shims still resolve.
    #[test]
    fn runtime_archive_without_runtime_extern_fails_by_exactly_clean_inc() {
        let dir = tempfile::tempdir().expect("tempdir");
        write_runtime_sources(dir.path()).expect("write sources");
        let archive = build_runtime_archive(dir.path(), &RuntimeMember::ALL).expect("archive");
        let removed = Command::new(&archive.ar)
            .arg("d")
            .arg(&archive.path)
            .arg(RuntimeMember::RuntimeExtern.object_name())
            .output()
            .expect("spawn ar d");
        assert!(
            removed.status.success(),
            "ar d failed: {}",
            String::from_utf8_lossy(&removed.stderr)
        );
        assert_eq!(
            archive_members(&archive.ar, &archive.path),
            vec![
                RuntimeMember::Runtime.object_name().to_owned(),
                RuntimeMember::PreludeShims.object_name().to_owned()
            ]
        );
        let undefined = link_demand(dir.path(), &archive.path, &representative_demand());
        let expected: BTreeSet<String> = ["clean_inc".to_owned()].into_iter().collect();
        assert_eq!(
            undefined, expected,
            "removing runtime_extern.o must fail the link by exactly clean_inc"
        );
    }

    /// The same control from the other side: an archive BUILT without the
    /// member (what a packer that forgot it would produce) is refused by the
    /// same symbol, and the CLI has no knob to produce one.
    #[test]
    fn runtime_archive_built_without_runtime_extern_is_named_by_the_linker() {
        let dir = tempfile::tempdir().expect("tempdir");
        write_runtime_sources(dir.path()).expect("write sources");
        let archive = build_runtime_archive(
            dir.path(),
            &[RuntimeMember::Runtime, RuntimeMember::PreludeShims],
        )
        .expect("archive");
        let undefined = link_demand(dir.path(), &archive.path, &representative_demand());
        let expected: BTreeSet<String> = ["clean_inc".to_owned()].into_iter().collect();
        assert_eq!(undefined, expected);
    }

    /// Every `clean_*` forwarder `runtime_extern.c` exports: the C source
    /// renames each header primitive with `#define <name> <name>__hdr`
    /// before including the header and then defines an external `<name>`,
    /// so the `#define` lines ARE the export list. Parsed from the embedded
    /// source rather than hand-listed, so a forwarder added later is
    /// demanded automatically.
    fn runtime_extern_forwarders() -> BTreeSet<String> {
        let out: BTreeSet<String> = clean_runtime::runtime_extern_source()
            .lines()
            .filter_map(|line| {
                let rest = line.strip_prefix("#define ")?;
                let mut parts = rest.split_whitespace();
                let name = parts.next()?;
                let alias = parts.next()?;
                (name.starts_with("clean_")
                    && alias.strip_prefix(name).is_some_and(|rest| rest == "__hdr"))
                .then(|| name.to_owned())
            })
            .collect();
        assert!(
            out.len() >= 20 && out.contains("clean_inc") && out.contains("clean_box"),
            "the forwarder list parsed from runtime_extern.c is implausible: {out:?}"
        );
        out
    }

    /// The archive resolves EVERY symbol an emitted object can leave for the
    /// link, not one representative per member: all `runtime_extern.c`
    /// forwarders and every `l_*` prelude shim the tables define. A shim
    /// whose definition references something no member defines, or a
    /// forwarder the shim TU shadows, would surface here and nowhere else —
    /// the census links only the battery's demand.
    #[test]
    fn runtime_archive_resolves_every_forwarder_and_every_prelude_shim() {
        let dir = tempfile::tempdir().expect("tempdir");
        write_runtime_sources(dir.path()).expect("write sources");
        let archive = build_runtime_archive(dir.path(), &RuntimeMember::ALL).expect("archive");
        let mut demand = runtime_extern_forwarders();
        let shims: BTreeSet<String> = crate::native_build::prelude_shim_symbols()
            .into_iter()
            .map(str::to_owned)
            .collect();
        assert!(
            shims.len() >= 40 && shims.contains("l_Nat_add") && shims.contains("l_Nat_land"),
            "the shim table is implausibly small: {} symbols",
            shims.len()
        );
        demand.extend(shims);
        let undefined = link_demand(dir.path(), &archive.path, &demand);
        assert!(
            undefined.is_empty(),
            "the runtime archive left symbols undefined out of {} demanded: {undefined:?}",
            demand.len()
        );
    }

    /// ADVERSARIAL (review): a stale `libclean_runtime.a` from an earlier run
    /// must not survive a rebuild whose compile fails — a consumer that reads
    /// the directory rather than the exit code would otherwise link the old
    /// archive. Also pins the failure text: it names the member and the
    /// command, and the `.o` of the failed member is gone too.
    #[test]
    fn stale_archive_does_not_survive_a_failed_compile() {
        let dir = tempfile::tempdir().expect("tempdir");
        write_runtime_sources(dir.path()).expect("write sources");
        let archive = build_runtime_archive(dir.path(), &RuntimeMember::ALL).expect("archive");
        assert!(archive.path.is_file());
        let extern_object = dir.path().join(RuntimeMember::RuntimeExtern.object_name());
        assert!(extern_object.is_file());
        // Poison the second member's source; the first still compiles, so
        // the failure happens mid-build, after one fresh object exists.
        std::fs::write(
            dir.path().join(RuntimeMember::RuntimeExtern.source_name()),
            "#include \"clean_runtime.h\"\nthis is not C\n",
        )
        .expect("poison source");
        let err = build_runtime_archive(dir.path(), &RuntimeMember::ALL)
            .expect_err("a poisoned member must fail the build");
        let text = err.to_string();
        assert!(
            text.contains("C compile of runtime_extern.c failed"),
            "the error must name the member: {text}"
        );
        assert!(
            !archive.path.exists(),
            "a failed rebuild must not leave the previous archive in place"
        );
        assert!(
            !extern_object.exists(),
            "a failed compile must not leave the previous object of that member in place"
        );
    }

    /// ADVERSARIAL (review): an archive that already exists with a member
    /// this build never wrote (`evil.o`) is rebuilt from scratch, not
    /// updated in place by `ar rcs` — the member set is exactly the three.
    #[test]
    fn stale_foreign_member_does_not_survive_a_rebuild() {
        let dir = tempfile::tempdir().expect("tempdir");
        write_runtime_sources(dir.path()).expect("write sources");
        let cc = cc();
        let evil_src = dir.path().join("evil.c");
        std::fs::write(&evil_src, "int clean_inc_evil_marker(void) { return 1; }\n")
            .expect("write evil.c");
        let evil_obj = dir.path().join("evil.o");
        let compiled = Command::new(&cc)
            .arg("-c")
            .arg(&evil_src)
            .arg("-o")
            .arg(&evil_obj)
            .output()
            .expect("spawn cc");
        assert!(
            compiled.status.success(),
            "{}",
            String::from_utf8_lossy(&compiled.stderr)
        );
        let ar = find_archiver().expect("ar");
        let seeded = Command::new(&ar)
            .arg("rcs")
            .arg(dir.path().join(ARCHIVE_NAME))
            .arg(&evil_obj)
            .output()
            .expect("spawn ar");
        assert!(
            seeded.status.success(),
            "{}",
            String::from_utf8_lossy(&seeded.stderr)
        );
        assert_eq!(
            archive_members(&ar, &dir.path().join(ARCHIVE_NAME)),
            vec!["evil.o".to_owned()]
        );
        let archive = build_runtime_archive(dir.path(), &RuntimeMember::ALL).expect("archive");
        assert_eq!(
            archive_members(&archive.ar, &archive.path),
            RuntimeMember::ALL
                .iter()
                .map(|m| m.object_name().to_owned())
                .collect::<Vec<_>>(),
            "a rebuild must not carry a stale foreign member forward"
        );
        let marker: BTreeSet<String> = ["clean_inc_evil_marker".to_owned()].into_iter().collect();
        assert_eq!(
            link_demand(dir.path(), &archive.path, &marker),
            marker,
            "the stale member's symbol must no longer resolve from the archive"
        );
    }

    /// ADVERSARIAL (review): `--sources-only` into a directory an earlier
    /// run BUILT in. The fresh sources must not sit beside the earlier
    /// archive and objects — compiled, possibly, by an older binary from
    /// older sources — as if those were this run's products. Measured on
    /// the first cut: all eight files stayed, the archive included.
    #[test]
    fn sources_only_removes_the_stale_archive_and_objects() {
        let dir = tempfile::tempdir().expect("tempdir");
        write_runtime_sources(dir.path()).expect("write sources");
        let archive = build_runtime_archive(dir.path(), &RuntimeMember::ALL).expect("archive");
        assert!(archive.path.is_file());
        // Also a dangling symlink where an object was: still a stale product.
        let dangling = dir.path().join(RuntimeMember::PreludeShims.object_name());
        std::fs::remove_file(&dangling).expect("remove object");
        #[cfg(unix)]
        std::os::unix::fs::symlink(dir.path().join("gone.o"), &dangling).expect("symlink");
        let mut report = Vec::new();
        materialize(dir.path(), true, &mut report).expect("sources-only succeeds");
        let report = String::from_utf8(report).expect("utf-8 report");
        assert!(
            report.contains("archive: not built (--sources-only)"),
            "the report says no archive was built: {report}"
        );
        assert!(
            report.contains(&format!("removed stale: {}", archive.path.display())),
            "the stale archive is reported by name: {report}"
        );
        assert!(
            !archive.path.exists(),
            "--sources-only must not leave an earlier run's archive in place"
        );
        for member in RuntimeMember::ALL {
            let object = dir.path().join(member.object_name());
            assert!(
                object.symlink_metadata().is_err(),
                "--sources-only must not leave an earlier run's {member} in place"
            );
            assert!(
                dir.path().join(member.source_name()).is_file(),
                "the sources are (re)written"
            );
        }
        assert!(dir.path().join(RUNTIME_HEADER_NAME).is_file());
    }

    /// A stand-in tool: an executable `/bin/sh` script `tools/<name>` running
    /// `body`. Kept out of the out-dir so it is never mistaken for a product.
    #[cfg(unix)]
    fn fake_tool(tools: &Path, name: &str, body: &str) -> String {
        use std::os::unix::fs::PermissionsExt;
        let path = tools.join(name);
        std::fs::write(&path, format!("#!/bin/sh\n{body}\n")).expect("write fake tool");
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755))
            .expect("chmod fake tool");
        path.to_str().expect("utf8 tool path").to_owned()
    }

    /// ADVERSARIAL (second review): an archiver that writes part of the
    /// archive and then FAILS. The stale-product removal ran before it, so
    /// the first-review code left the truncated `libclean_runtime.a` in
    /// place — exactly the partial archive the module promises never to
    /// leave. The fake also drops a `.written` marker beside it, so the test
    /// proves the partial file existed rather than passing on a fake that
    /// never wrote.
    #[cfg(unix)]
    #[test]
    fn an_archiver_that_fails_mid_write_leaves_no_partial_archive() {
        let dir = tempfile::tempdir().expect("tempdir");
        let tools = tempfile::tempdir().expect("tools tempdir");
        write_runtime_sources(dir.path()).expect("write sources");
        // `ar rcs <archive> <objects...>`: $2 is the archive.
        let ar = fake_tool(
            tools.path(),
            "ar-partial",
            "printf '!<arch>\\npartial' > \"$2\"\n: > \"$2.written\"\nexit 1",
        );
        let cc = cc();
        let err =
            build_runtime_archive_with(dir.path(), &RuntimeMember::ALL, || Some(cc), || Some(ar))
                .expect_err("a failing archiver must fail the build");
        let text = format!("{err:#}");
        assert!(
            text.contains(&format!(
                "archiving {}",
                dir.path().join(ARCHIVE_NAME).display()
            )) && text.contains("failed"),
            "the error must name the archive: {text}"
        );
        assert!(
            dir.path().join(format!("{ARCHIVE_NAME}.written")).is_file(),
            "the fake archiver did not run, so this test tested nothing"
        );
        assert!(
            dir.path().join(ARCHIVE_NAME).symlink_metadata().is_err(),
            "a failed archiver's partial archive must not remain"
        );
    }

    /// ADVERSARIAL (second review): the compiler twin — a compiler that
    /// writes the object and then FAILS leaves no object of that member and
    /// no archive; the error names the member.
    #[cfg(unix)]
    #[test]
    fn a_compiler_that_fails_mid_write_leaves_no_partial_object() {
        let dir = tempfile::tempdir().expect("tempdir");
        let tools = tempfile::tempdir().expect("tools tempdir");
        write_runtime_sources(dir.path()).expect("write sources");
        let cc = fake_tool(
            tools.path(),
            "cc-partial",
            "out=\"\"\nwhile [ $# -gt 0 ]; do if [ \"$1\" = \"-o\" ]; then out=\"$2\"; fi; shift; done\n\
             printf 'partial' > \"$out\"\n: > \"$out.written\"\nexit 1",
        );
        let err = build_runtime_archive_with(
            dir.path(),
            &RuntimeMember::ALL,
            || Some(cc),
            || Some("ar".to_owned()),
        )
        .expect_err("a failing compiler must fail the build");
        let text = format!("{err:#}");
        assert!(
            text.contains("C compile of clean_runtime.c failed"),
            "the error must name the first member: {text}"
        );
        let object = dir.path().join(RuntimeMember::Runtime.object_name());
        assert!(
            dir.path().join("clean_runtime.o.written").is_file(),
            "the fake compiler did not run, so this test tested nothing"
        );
        assert!(
            object.symlink_metadata().is_err(),
            "a failed compile's partial object must not remain"
        );
        assert!(dir.path().join(ARCHIVE_NAME).symlink_metadata().is_err());
    }

    /// ADVERSARIAL (second review): tools that exit 0 and write NOTHING are
    /// refused by name — an exit code is not a product.
    #[cfg(unix)]
    #[test]
    fn tools_that_succeed_without_writing_are_refused() {
        let tools = tempfile::tempdir().expect("tools tempdir");
        let silent = fake_tool(tools.path(), "silent", "exit 0");

        let dir = tempfile::tempdir().expect("tempdir");
        write_runtime_sources(dir.path()).expect("write sources");
        let cc_silent = silent.clone();
        let err = build_runtime_archive_with(
            dir.path(),
            &RuntimeMember::ALL,
            || Some(cc_silent),
            || Some("ar".to_owned()),
        )
        .expect_err("a compiler that writes no object must fail the build");
        assert!(
            format!("{err:#}").contains("C compiler reported success but produced no object"),
            "{err:#}"
        );
        assert!(dir.path().join(ARCHIVE_NAME).symlink_metadata().is_err());

        let dir = tempfile::tempdir().expect("tempdir");
        write_runtime_sources(dir.path()).expect("write sources");
        let cc = cc();
        let err = build_runtime_archive_with(
            dir.path(),
            &RuntimeMember::ALL,
            || Some(cc),
            || Some(silent),
        )
        .expect_err("an archiver that writes no archive must fail the build");
        assert!(
            format!("{err:#}").contains("archiver reported success but produced no archive"),
            "{err:#}"
        );
        assert!(dir.path().join(ARCHIVE_NAME).symlink_metadata().is_err());
    }

    #[test]
    fn empty_member_list_is_refused() {
        let dir = tempfile::tempdir().expect("tempdir");
        write_runtime_sources(dir.path()).expect("write sources");
        let err = build_runtime_archive(dir.path(), &[]).expect_err("empty archive refused");
        assert!(err.to_string().contains("empty runtime archive"), "{err:#}");
    }

    #[test]
    fn archive_before_sources_is_refused_by_name() {
        let dir = tempfile::tempdir().expect("tempdir");
        let err = build_runtime_archive(dir.path(), &RuntimeMember::ALL)
            .expect_err("missing sources refused");
        assert!(
            err.to_string().contains("clean_runtime.c is missing"),
            "{err:#}"
        );
    }
}

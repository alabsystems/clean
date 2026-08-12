// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Front #1 Stage 2 generator: reflect the foundation core of the LIVE
//! foundation-core kernel environment into the `kernel_core_red_env`
//! generated artifacts (value literal + interning table + skip ledger), and
//! measure the numbers the stage's budget gate needs.
//!
//! Usage:
//!   cargo run --release -p clean-verify --bin red_env_reflect            # emit
//!   cargo run --release -p clean-verify --bin red_env_reflect -- --check # drift check only
//!   cargo run --release -p clean-verify --bin red_env_reflect -- --probe # whnf one-rfl probe
//!
//! Normal emission uses an artifact-independent reflection seed, validates the
//! complete rendered script against both a second seed and a complete
//! `Specification` built with that fresh script injected in memory, and
//! publishes each file by a same-directory atomic rename with rollback on
//! reported I/O failure.
//! A process/power failure between the three renames can leave artifact drift,
//! which the byte-exact fidelity gate detects before the set is trusted.
//! `--check` and `--probe` deliberately build the full live specification.
//!
//! Encodings (trust edges) are documented in `clean_verify::red_env_reflect`.

use std::io::{self, Write as _};
use std::path::{Path, PathBuf};
use std::time::Instant;

use clean_kernel::{Expr, TypeChecker};
use clean_verify::red_env_reflect::{fidelity_check, reflect_foundation_core};
use clean_verify::Specification;

const GENERATED_DIR: &str = "crates/clean-verify/src/spec/core_spec/generated";

fn main() {
    // Spec construction + reflection recurse deeply; use a big-stack thread
    // (same pattern as the lean_export bin).
    let handle = std::thread::Builder::new()
        .stack_size(1024 * 1024 * 1024)
        .spawn(run)
        .expect("spawn reflect thread");
    match handle.join() {
        Ok(code) => std::process::exit(code),
        Err(_) => std::process::exit(1),
    }
}

#[allow(clippy::too_many_lines)]
fn run() -> i32 {
    let mut check_only = false;
    let mut probe = false;
    for a in std::env::args().skip(1) {
        match a.as_str() {
            "--check" => check_only = true,
            "--probe" => probe = true,
            other => {
                eprintln!("unknown argument: {other}");
                return 2;
            }
        }
    }

    let build_full = check_only || probe;
    let builder = if build_full {
        "live Specification::new()"
    } else {
        "artifact-independent reflection seed"
    };
    eprintln!("[red_env_reflect] building {builder} (timed) ...");
    let t0 = Instant::now();
    let spec = match if build_full {
        Specification::new()
    } else {
        Specification::new_red_env_reflection_seed()
    } {
        Ok(s) => s,
        Err(e) => {
            eprintln!("[red_env_reflect] {builder} FAILED: {e:?}");
            return 1;
        }
    };
    let build = t0.elapsed();
    eprintln!(
        "[red_env_reflect] {builder} built in {:.3}s ({} kernel constants)",
        build.as_secs_f64(),
        spec.env().num_constants()
    );

    let t1 = Instant::now();
    let reflection = reflect_foundation_core(spec.env());
    eprintln!(
        "[red_env_reflect] reflection computed in {:.3}s: {} recursors ({} rules), {} defs, {} interned names, {} skips",
        t1.elapsed().as_secs_f64(),
        reflection.recs.len(),
        reflection.recs.iter().map(|r| r.rules.len()).sum::<usize>(),
        reflection.defs.len(),
        reflection.interning.len(),
        reflection.skips.len()
    );
    if !reflection.interning_injective() {
        eprintln!("[red_env_reflect] FATAL: interning table not injective");
        return 1;
    }

    let script = match reflection.def_script() {
        Ok(script) => script,
        Err(error) => {
            eprintln!("[red_env_reflect] FATAL: {error}");
            return 1;
        }
    };
    let interning = reflection.interning_tsv();
    let ledger = match reflection.skip_ledger_md() {
        Ok(ledger) => ledger,
        Err(error) => {
            eprintln!("[red_env_reflect] FATAL: {error}");
            return 1;
        }
    };
    eprintln!(
        "[red_env_reflect] def script: {} bytes ({} defs, max paren depth {}); interning: {} bytes; ledger: {} bytes",
        script.len(),
        script.lines().count(),
        script
            .lines()
            .map(clean_verify::red_env_reflect::max_paren_depth)
            .max()
            .unwrap_or(0),
        interning.len(),
        ledger.len()
    );

    if probe {
        return run_probe(&spec);
    }

    let dir = Path::new(GENERATED_DIR);
    let script_path = dir.join("kernel_core_red_env.defs.txt");
    let interning_path = dir.join("kernel_core_red_env.interning.tsv");
    let ledger_path = dir.join("kernel_core_red_env.skips.md");

    if check_only {
        let committed_script = std::fs::read_to_string(&script_path).unwrap_or_default();
        let committed_interning = std::fs::read_to_string(&interning_path).unwrap_or_default();
        let committed_ledger = std::fs::read_to_string(&ledger_path).unwrap_or_default();
        return match fidelity_check(
            spec.env(),
            &committed_script,
            &committed_interning,
            &committed_ledger,
        ) {
            Ok(_) => {
                eprintln!("[red_env_reflect] fidelity check PASSED (no drift)");
                0
            }
            Err(e) => {
                eprintln!("[red_env_reflect] fidelity check FAILED: {e}");
                1
            }
        };
    }

    eprintln!("[red_env_reflect] validating every generated def against a fresh seed ...");
    if let Err(error) = Specification::validate_red_env_reflection_script(&script) {
        eprintln!(
            "[red_env_reflect] FATAL: generated script failed parse/elaboration/kernel validation: \
             {error:?}"
        );
        return 1;
    }

    eprintln!(
        "[red_env_reflect] validating the generated artifact set through a full \
         Specification built from the fresh in-memory script ..."
    );
    let full_spec = match Specification::new_with_red_env_reflection_script(&script) {
        Ok(specification) => specification,
        Err(error) => {
            eprintln!(
                "[red_env_reflect] FATAL: fresh script failed complete Specification \
                 construction: {error:?}"
            );
            return 1;
        }
    };
    if let Err(error) = fidelity_check(full_spec.env(), &script, &interning, &ledger) {
        eprintln!(
            "[red_env_reflect] FATAL: fresh artifact set does not match the complete \
             live Specification environment: {error}"
        );
        return 1;
    }

    if let Err(e) = std::fs::create_dir_all(dir) {
        eprintln!("[red_env_reflect] cannot create {GENERATED_DIR}: {e}");
        return 1;
    }
    // Publish the script last: it is the runtime-consumed artifact, while the
    // table and ledger are its audit companions. Every replacement is an
    // atomic same-directory rename; backups roll the set back if an ordinary
    // rename or directory-sync operation reports failure. A process crash
    // between files is detected later by the byte-exact fidelity gate.
    let artifacts = [
        (interning_path, interning),
        (ledger_path, ledger),
        (script_path, script),
    ];
    if let Err(error) = replace_artifact_set(dir, &artifacts) {
        eprintln!("[red_env_reflect] artifact-set replacement FAILED: {error}");
        return 1;
    }
    for (path, _) in &artifacts {
        eprintln!("[red_env_reflect] wrote {}", path.display());
    }
    0
}

fn sibling_path(path: &Path, role: &str) -> io::Result<PathBuf> {
    let file_name = path
        .file_name()
        .and_then(|name| name.to_str())
        .ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("artifact path has no UTF-8 file name: {}", path.display()),
            )
        })?;
    Ok(path.with_file_name(format!(".{file_name}.{role}.{}", std::process::id())))
}

fn write_synced(path: &Path, content: &str) -> io::Result<()> {
    let mut file = std::fs::File::create(path)?;
    file.write_all(content.as_bytes())?;
    file.sync_all()
}

fn cleanup(paths: impl IntoIterator<Item = PathBuf>) {
    for path in paths {
        if let Err(error) = std::fs::remove_file(&path) {
            if error.kind() != io::ErrorKind::NotFound {
                eprintln!(
                    "[red_env_reflect] warning: could not remove {}: {error}",
                    path.display()
                );
            }
        }
    }
}

/// Replace generated artifacts with per-file same-directory atomic renames and
/// restore the complete old set if an operation reports failure partway
/// through.
fn replace_artifact_set(dir: &Path, artifacts: &[(PathBuf, String)]) -> io::Result<()> {
    let mut temps = Vec::with_capacity(artifacts.len());
    let mut backups = Vec::with_capacity(artifacts.len());
    let existed = artifacts
        .iter()
        .map(|(path, _)| path.exists())
        .collect::<Vec<_>>();

    for (path, content) in artifacts {
        let prepared = (|| -> io::Result<(PathBuf, PathBuf)> {
            let temp = sibling_path(path, "tmp")?;
            let backup = sibling_path(path, "bak")?;
            cleanup([temp.clone(), backup.clone()]);
            if let Err(error) = write_synced(&temp, content) {
                cleanup([temp, backup]);
                return Err(error);
            }
            if path.exists() {
                if let Err(error) = std::fs::copy(path, &backup)
                    .and_then(|_| std::fs::File::open(&backup)?.sync_all())
                {
                    cleanup([temp, backup]);
                    return Err(error);
                }
            }
            Ok((temp, backup))
        })();
        let (temp, backup) = match prepared {
            Ok(paths) => paths,
            Err(error) => {
                cleanup(temps.into_iter().chain(backups));
                return Err(error);
            }
        };
        temps.push(temp);
        backups.push(backup);
    }

    let publish = (|| -> io::Result<()> {
        for ((path, _), temp) in artifacts.iter().zip(&temps) {
            std::fs::rename(temp, path)?;
        }
        std::fs::File::open(dir)?.sync_all()
    })();

    if let Err(error) = publish {
        let mut rollback_errors = Vec::new();
        for (((path, _), backup), previously_existed) in
            artifacts.iter().zip(&backups).zip(&existed)
        {
            let restored = if *previously_existed {
                std::fs::rename(backup, path)
            } else if path.exists() {
                std::fs::remove_file(path)
            } else {
                Ok(())
            };
            if let Err(restore_error) = restored {
                rollback_errors.push(format!(
                    "{} (backup retained at {}): {restore_error}",
                    path.display(),
                    backup.display()
                ));
            }
        }
        cleanup(temps);
        if rollback_errors.is_empty() {
            cleanup(backups);
            let _ = std::fs::File::open(dir).and_then(|directory| directory.sync_all());
            return Err(error);
        }
        return Err(io::Error::new(
            error.kind(),
            format!(
                "{error}; rollback also failed for {}",
                rollback_errors.join("; ")
            ),
        ));
    }

    // The published artifact entries were already made durable by the
    // directory sync inside `publish`. Backup cleanup is best-effort and cannot
    // invalidate that committed set, so no later fallible operation is reported
    // as a failed replacement after rollback authority has been discarded.
    cleanup(backups);
    Ok(())
}

/// The one-rfl-at-scale PROBE (Stage-4 feasibility preview): whnf-evaluate
/// each Stage-1 closure checker over the registered `kernel_core_red_env`
/// and time the fold. Requires the registration stage to be in the spec.
fn run_probe(spec: &Specification) -> i32 {
    if spec
        .env()
        .get_const(&clean_kernel::Name::from_string("kernel_core_red_env"))
        .is_none()
    {
        eprintln!(
            "[red_env_reflect] --probe: kernel_core_red_env not registered in the spec \
             (run after the Stage-2 registration stage lands)"
        );
        return 1;
    }
    let tc = TypeChecker::new(spec.env());
    let mut code = 0;
    for (checker, proj) in [
        ("rec_env_closed_b", "red_rec"),
        ("rec_env_lift_closed_b", "red_rec"),
        ("def_env_closed_b", "red_def"),
        ("def_env_lift_closed_b", "red_def"),
    ] {
        let e = Expr::app(
            Expr::const_str(checker),
            Expr::app(
                Expr::const_str(proj),
                Expr::const_str("kernel_core_red_env"),
            ),
        );
        let t = Instant::now();
        let w = tc.whnf(&e);
        let dt = t.elapsed();
        let head = format!("{w}");
        eprintln!(
            "[red_env_reflect] probe {checker} ({proj} kernel_core_red_env): whnf = {} in {:.3}s",
            head.chars().take(80).collect::<String>(),
            dt.as_secs_f64()
        );
        if !(head.starts_with("Bool.true") || head.starts_with("Bool.false")) {
            eprintln!("[red_env_reflect] probe {checker}: fold STUCK (non-Bool head)");
            code = 1;
        }
    }

    // Aggregate per-element cost (the TRUE-case fold cost the Bool.and
    // short-circuit hides): force the full per-element checker test
    // `nat_eqb (bvar_ceiling <term>) 0` for every reflected rule rhs and
    // def value, and total the whnf time. This is the measured one-rfl
    // budget for a Stage-4 depth-aware checker at real-env scale.
    let reflection = reflect_foundation_core(spec.env());
    let mut elements: Vec<(String, &clean_verify::red_env_reflect::SpecExpr)> = Vec::new();
    for rec in &reflection.recs {
        for rule in &rec.rules {
            elements.push((format!("{}/{}", rec.name, rule.ctor), &rule.rhs));
        }
    }
    for def in &reflection.defs {
        elements.push((def.name.clone(), &def.value));
    }
    let mut total = std::time::Duration::ZERO;
    let mut worst = (String::new(), std::time::Duration::ZERO);
    let mut trues = 0usize;
    for (label, term) in &elements {
        let reflected_term = match reflection.kexpr_term(term) {
            Ok(term) => term,
            Err(error) => {
                eprintln!("[red_env_reflect] element probe {label}: {error}");
                code = 1;
                continue;
            }
        };
        let e = Expr::apps(
            Expr::const_str("nat_eqb"),
            [
                Expr::app(Expr::const_str("bvar_ceiling"), reflected_term),
                Expr::const_str("kcre_nat_0"),
            ],
        );
        let t = Instant::now();
        let w = tc.whnf(&e);
        let dt = t.elapsed();
        total += dt;
        if dt > worst.1 {
            worst = (label.clone(), dt);
        }
        let head = format!("{w}");
        if head.starts_with("Bool.true") {
            trues += 1;
        } else if !head.starts_with("Bool.false") {
            eprintln!("[red_env_reflect] element probe {label}: STUCK (non-Bool head {head})");
            code = 1;
        }
    }
    eprintln!(
        "[red_env_reflect] element probes: {} elements, {} ceiling-0 (bvar-free), total {:.3}s, worst {} at {:.3}s",
        elements.len(),
        trues,
        total.as_secs_f64(),
        worst.0,
        worst.1.as_secs_f64()
    );
    code
}

#[cfg(test)]
mod publication_tests {
    use super::replace_artifact_set;
    use std::path::{Path, PathBuf};
    use std::sync::atomic::{AtomicU64, Ordering};

    static NEXT_TEST_DIR: AtomicU64 = AtomicU64::new(0);

    struct TestDir(PathBuf);

    impl TestDir {
        fn new() -> Self {
            let serial = NEXT_TEST_DIR.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!(
                "clean-red-env-reflect-{}-{serial}",
                std::process::id()
            ));
            std::fs::create_dir(&path).expect("publication test directory should be unique");
            Self(path)
        }

        fn path(&self) -> &Path {
            &self.0
        }
    }

    impl Drop for TestDir {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    fn fixture(dir: &Path) -> Vec<(PathBuf, String)> {
        ["interning.tsv", "skips.md", "defs.txt"]
            .into_iter()
            .map(|name| (dir.join(name), format!("new {name}\n")))
            .collect()
    }

    fn seed_old_files(artifacts: &[(PathBuf, String)]) {
        for (path, _) in artifacts {
            let name = path
                .file_name()
                .and_then(|name| name.to_str())
                .expect("fixture path should have a UTF-8 file name");
            std::fs::write(path, format!("old {name}\n"))
                .expect("old publication fixture should be writable");
        }
    }

    fn assert_no_transaction_files(dir: &Path) {
        let leftovers = std::fs::read_dir(dir)
            .expect("publication fixture directory should remain readable")
            .filter_map(Result::ok)
            .filter_map(|entry| entry.file_name().into_string().ok())
            .filter(|name| name.contains(".tmp.") || name.contains(".bak."))
            .collect::<Vec<_>>();
        assert!(
            leftovers.is_empty(),
            "transaction files must be cleaned after a resolved operation: {leftovers:?}"
        );
    }

    #[test]
    fn successful_publication_replaces_the_complete_set() {
        let dir = TestDir::new();
        let artifacts = fixture(dir.path());
        seed_old_files(&artifacts);

        replace_artifact_set(dir.path(), &artifacts)
            .expect("complete artifact set should publish successfully");

        for (path, expected) in &artifacts {
            assert_eq!(
                std::fs::read_to_string(path).expect("published artifact should be readable"),
                *expected
            );
        }
        assert_no_transaction_files(dir.path());
    }

    #[test]
    fn reported_directory_sync_failure_rolls_back_every_artifact() {
        let dir = TestDir::new();
        let artifacts = fixture(dir.path());
        seed_old_files(&artifacts);

        let error = replace_artifact_set(&dir.path().join("missing-sync-directory"), &artifacts)
            .expect_err("missing directory must make the reported durability sync fail");
        assert_eq!(error.kind(), std::io::ErrorKind::NotFound);

        for (path, _) in &artifacts {
            let name = path
                .file_name()
                .and_then(|name| name.to_str())
                .expect("fixture path should have a UTF-8 file name");
            assert_eq!(
                std::fs::read_to_string(path).expect("rolled-back artifact should be readable"),
                format!("old {name}\n"),
                "every old artifact must remain recoverable through the last reported sync"
            );
        }
        assert_no_transaction_files(dir.path());
    }
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Input custody for the existing complete two-file producer CLIs.
use super::{rows, Row};
use std::{
    collections::BTreeSet,
    path::{Path, PathBuf},
};

const PAIR: &[(&str, &[u8])] = &[
    (
        "f1/gen_f1.py",
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../reports/crystal-lane/2026-10-01-bytev1/f1/gen_f1.py"
        )),
    ),
    (
        "s1a/gen_s1a.py",
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../reports/crystal-lane/2026-10-01-bytev1/s1a/gen_s1a.py"
        )),
    ),
];
fn maintained(table: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join(format!("../../data/bmem-source-qualification/{table}.json"))
}
fn originals() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../reports/crystal-lane/2026-10-01-bytev1")
}
fn check_pair(root: &Path) -> Result<(), String> {
    for (relative, compiled) in PAIR {
        let path = root.join(relative);
        let metadata =
            std::fs::symlink_metadata(&path).map_err(|e| format!("{}: {e}", path.display()))?;
        require!(
            metadata.file_type().is_file(),
            "producer is not a regular file: {}",
            path.display()
        );
        require!(
            std::fs::read(&path).map_err(|e| e.to_string())? == *compiled,
            "producer closure source differs from compiled bytes: {}",
            path.display()
        );
    }
    Ok(())
}
fn entries(path: &Path) -> Result<BTreeSet<String>, String> {
    std::fs::read_dir(path)
        .map_err(|e| e.to_string())?
        .map(|entry| {
            let entry = entry.map_err(|e| e.to_string())?;
            entry
                .file_name()
                .into_string()
                .map_err(|_| "non-UTF8 foreign stage entry".into())
        })
        .collect()
}
fn check_stage(root: &Path) -> Result<(), String> {
    require!(
        entries(root)? == BTreeSet::from(["f1".to_owned(), "s1a".to_owned()]),
        "foreign stage root entry"
    );
    for (directory, file) in [("f1", "gen_f1.py"), ("s1a", "gen_s1a.py")] {
        let path = root.join(directory);
        require!(
            std::fs::symlink_metadata(&path)
                .map_err(|e| e.to_string())?
                .file_type()
                .is_dir(),
            "stage directory is not private regular directory"
        );
        require!(
            entries(&path)? == BTreeSet::from([file.to_owned()]),
            "missing/foreign producer, module or bytecode cache in {directory}"
        );
    }
    check_pair(root)
}
fn stage_pair(root: &Path) -> Result<(), String> {
    for (relative, compiled) in PAIR {
        let path = root.join(relative);
        std::fs::create_dir_all(path.parent().ok_or("missing stage parent")?)
            .map_err(|e| e.to_string())?;
        std::fs::write(path, compiled).map_err(|e| e.to_string())?;
    }
    check_stage(root)
}
fn interpreter() -> Result<(PathBuf, Vec<u8>, String), String> {
    // Resolve the launch file ourselves; stdout never supplies an executable path.
    let search = std::env::var_os("PATH").ok_or("missing interpreter PATH")?;
    let candidate = std::env::split_paths(&search)
        .map(|p| p.join("python3"))
        .find(|p| p.is_file())
        .ok_or("no interpreter launch file")?;
    let executable = std::fs::canonicalize(candidate).map_err(|e| e.to_string())?;
    require!(
        std::fs::symlink_metadata(&executable)
            .map_err(|e| e.to_string())?
            .file_type()
            .is_file(),
        "interpreter launch file is not regular"
    );
    let bytes = std::fs::read(&executable).map_err(|e| e.to_string())?;
    // No -c/exec string and no ambient site/PYTHON import hooks for identification.
    let version = std::process::Command::new(&executable)
        .args(["-I", "-B", "-S", "--version"])
        .output()
        .map_err(|e| e.to_string())?;
    require!(
        std::fs::read(&executable).map_err(|e| e.to_string())? == bytes,
        "interpreter changed during version query"
    );
    require!(
        version.status.success(),
        "interpreter version query failed: {:?}",
        version.status
    );
    Ok((
        executable,
        bytes,
        format!(
            "stdout={:?} stderr={:?}",
            String::from_utf8_lossy(&version.stdout),
            String::from_utf8_lossy(&version.stderr)
        ),
    ))
}

pub(super) fn input(table: &str, expected: &[(&str, &str)]) -> Result<(Vec<u8>, Vec<Row>), String> {
    let entry = match table {
        "f1" => "f1/gen_f1.py",
        "s1a" => "s1a/gen_s1a.py",
        _ => return Err("unknown table".into()),
    };
    let path = maintained(table);
    let raw = std::fs::read(&path).map_err(|e| format!("{}: {e}", path.display()))?;
    check_pair(&originals())?;
    let stage = tempfile::tempdir().map_err(|e| e.to_string())?;
    stage_pair(stage.path())?;
    let (executable, tool_bytes, identity) = interpreter()?;
    // BOTH original files and the exact clean staged closure bracket EVERY full CLI.
    check_pair(&originals())?;
    check_stage(stage.path())?;
    require!(
        std::fs::read(&executable).map_err(|e| e.to_string())? == tool_bytes,
        "interpreter changed before full CLI"
    );
    // Execute the unchanged existing entrypoint directly. Its existing sibling
    // import resolves inside the fresh f1/s1a layout. -I excludes ambient Python
    // paths/hooks, -S skips site, and exact inventory excludes ALL producer pyc
    // reads; -B alone would only suppress pyc writes and is not sufficient.
    let generated = std::process::Command::new(&executable)
        .args(["-I", "-B", "-S"])
        .arg(stage.path().join(entry))
        .current_dir(stage.path())
        .output();
    if let Ok(output) = &generated {
        eprintln!(
            "bmem-source-producer table={table} status={:?} stdout_blake3={} stderr={:?}",
            output.status,
            blake3::hash(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
    check_pair(&originals())?;
    check_stage(stage.path())?;
    require!(
        std::fs::read(&executable).map_err(|e| e.to_string())? == tool_bytes,
        "interpreter changed during full CLI"
    );
    let generated = generated.map_err(|e| e.to_string())?;
    require!(
        generated.status.success(),
        "existing full producer CLI failed: {:?}",
        generated.status
    );
    require!(
        generated.stdout == raw,
        "fixture differs from complete current unfiltered CLI stdout"
    );
    for (relative, compiled) in PAIR {
        eprintln!(
            "bmem-source-closure original={} staged={} source_blake3={}",
            originals().join(relative).display(),
            stage.path().join(relative).display(),
            blake3::hash(compiled)
        );
    }
    // Launch-file identity only: installed framework/stdlib/dynamic-loader/OS
    // runtime remains TCB; this is not a hermetic Python runtime attestation.
    eprintln!("bmem-source-input table={table} raw_blake3={} bytes={} interpreter={} interpreter_blake3={} interpreter_identity={identity:?} flags=-I,-B,-S",
        blake3::hash(&raw),raw.len(),executable.display(),blake3::hash(&tool_bytes));
    let parsed = rows(&raw, expected)?;
    Ok((raw, parsed))
}

#[test]
fn producer_dependency_missing_foreign_and_cache_controls() {
    let maintained_before =
        std::fs::read(maintained("s1a")).expect("actual existing-CLI fixture required");
    let stage = tempfile::tempdir().expect("private control stage");
    stage_pair(stage.path()).expect("exact staged pair");
    let s1a_before = std::fs::read(stage.path().join("s1a/gen_s1a.py")).expect("S1a source");
    let dependency = stage.path().join("f1/gen_f1.py");
    let mut changed = PAIR[0].1.to_vec();
    changed.push(b'\n');
    std::fs::write(&dependency, changed).expect("mutate only copied imported F1");
    assert!(check_pair(stage.path()).is_err() && check_stage(stage.path()).is_err());
    assert_eq!(
        std::fs::read(stage.path().join("s1a/gen_s1a.py")).expect("unchanged S1a"),
        s1a_before
    );
    std::fs::write(&dependency, PAIR[0].1).expect("restore exact copied dependency");
    std::fs::remove_file(&dependency).expect("missing copied dependency control");
    assert!(check_pair(stage.path()).is_err() && check_stage(stage.path()).is_err());
    std::fs::write(&dependency, PAIR[0].1).expect("restore copied dependency");
    let cache = stage.path().join("f1/__pycache__");
    std::fs::create_dir(&cache).expect("foreign cache control");
    std::fs::write(
        cache.join("gen_f1.foreign.pyc"),
        b"presence-only cache control; never executed",
    )
    .expect("cache marker");
    assert!(check_pair(stage.path()).is_ok() && check_stage(stage.path()).is_err());
    std::fs::remove_dir_all(&cache).expect("remove only private control cache");
    let foreign = stage.path().join("f1/gen_f1.pyc");
    std::fs::write(&foreign, b"foreign legacy cache; never executed").expect("foreign control");
    assert!(check_stage(stage.path()).is_err());
    std::fs::remove_file(foreign).expect("remove only control marker");
    check_stage(stage.path()).expect("exact restored staged pair");
    assert_eq!(
        std::fs::read(stage.path().join("s1a/gen_s1a.py")).expect("unchanged S1a"),
        s1a_before
    );
    assert_eq!(
        std::fs::read(maintained("s1a")).expect("unchanged maintained JSON"),
        maintained_before
    );
}

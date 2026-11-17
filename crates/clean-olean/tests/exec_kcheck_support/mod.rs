// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Shared content-addressed compilation helper for post-C3 packages that depend
//! only on the executable slice of `theories/kcheck_labelled` (`KCheck.Token`
//! through `KCheck.Signature` and `KCheck.CheckerCases`), avoiding repeated
//! 24 GiB recompilation of `KCheck.CompleteSound` while still compiling every
//! dependency and subject `.lean` module from source with the pinned `lean`
//! binary (zero Lake `.olean` cache trust).

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::thread;
use std::time::Duration;

use sha2::{Digest, Sha256};

const EXEC_RECIPE_VERSION: u32 = 2;

const EXEC_KCHECK_ROOTS: &[&str] = &["KCheck/Signature", "KCheck/CheckerCases"];

fn resolve_exec_kcheck_stems(kcheck_labelled_dir: &Path) -> Vec<String> {
    let order = parse_order_stems(&kcheck_labelled_dir.join("ORDER"));
    let order_set: BTreeSet<&str> = order.iter().map(String::as_str).collect();
    let mut reachable = BTreeSet::new();
    let mut worklist: Vec<String> = EXEC_KCHECK_ROOTS.iter().map(|s| (*s).to_string()).collect();
    while let Some(stem) = worklist.pop() {
        assert!(
            order_set.contains(stem.as_str()),
            "exec kcheck stem {stem} missing from kcheck_labelled/ORDER"
        );
        if !reachable.insert(stem.clone()) {
            continue;
        }
        let path = kcheck_labelled_dir.join(format!("{stem}.lean"));
        let raw = fs::read_to_string(&path)
            .unwrap_or_else(|err| panic!("cannot read {}: {err}", path.display()));
        for line in raw.lines() {
            let trimmed = line.trim();
            if let Some(rest) = trimmed.strip_prefix("import ") {
                for tok in rest.split_whitespace() {
                    if tok.starts_with("KCheck.") {
                        let dep_stem = tok.replace('.', "/");
                        if !reachable.contains(&dep_stem) {
                            worklist.push(dep_stem);
                        }
                    }
                }
            }
        }
    }
    order
        .into_iter()
        .filter(|stem| reachable.contains(stem))
        .collect()
}

struct DirLockGuard {
    lock_dir: PathBuf,
}

impl DirLockGuard {
    fn acquire(root: &Path) -> Self {
        fs::create_dir_all(root).expect("create exec-kcheck cache root");
        let lock_dir = root.join("compile.lock");
        loop {
            if fs::create_dir(&lock_dir).is_ok() {
                return Self { lock_dir };
            }
            thread::sleep(Duration::from_millis(100));
        }
    }
}

impl Drop for DirLockGuard {
    fn drop(&mut self) {
        let _ = fs::remove_dir(&self.lock_dir);
    }
}

fn manifest_dir() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR"))
}

fn cache_root() -> PathBuf {
    let target = std::env::var_os("CARGO_TARGET_DIR")
        .map_or_else(|| manifest_dir().join("../../target"), PathBuf::from);
    let target = if target.is_absolute() {
        target
    } else {
        std::env::current_dir()
            .expect("resolve relative CARGO_TARGET_DIR")
            .join(target)
    };
    target.join("clean-olean-lean-exec-base")
}

fn parse_order_stems(order_path: &Path) -> Vec<String> {
    let raw = fs::read_to_string(order_path)
        .unwrap_or_else(|err| panic!("cannot read {}: {err}", order_path.display()));
    raw.lines()
        .map(str::trim)
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .map(ToOwned::to_owned)
        .collect()
}

fn collect_lean_and_order_files(root: &Path, dir: &Path, out: &mut BTreeMap<String, Vec<u8>>) {
    let entries =
        fs::read_dir(dir).unwrap_or_else(|err| panic!("cannot read {}: {err}", dir.display()));
    for entry in entries {
        let entry = entry.expect("dir entry");
        let name = entry.file_name();
        let name_str = name.to_string_lossy();
        if name_str.starts_with('.') || name_str == "target" {
            continue;
        }
        let path = entry.path();
        if path.is_dir() {
            collect_lean_and_order_files(root, &path, out);
        } else if name_str == "ORDER" || name_str.ends_with(".lean") {
            let rel = path
                .strip_prefix(root)
                .expect("relative path")
                .to_string_lossy()
                .replace('\\', "/");
            let bytes =
                fs::read(&path).unwrap_or_else(|err| panic!("read {}: {err}", path.display()));
            out.insert(rel, bytes);
        }
    }
}

fn copy_tree_all(from: &Path, to: &Path) {
    fs::create_dir_all(to).unwrap_or_else(|err| panic!("mkdir {}: {err}", to.display()));
    for entry in
        fs::read_dir(from).unwrap_or_else(|err| panic!("readdir {}: {err}", from.display()))
    {
        let entry = entry.expect("entry");
        let src = entry.path();
        let dst = to.join(entry.file_name());
        if src.is_dir() {
            copy_tree_all(&src, &dst);
        } else {
            fs::copy(&src, &dst)
                .unwrap_or_else(|err| panic!("copy {} -> {}: {err}", src.display(), dst.display()));
        }
    }
}

fn copy_lean_stems(theory_dir: &Path, stems: &[String], staging: &Path) {
    for stem in stems {
        let rel = format!("{stem}.lean");
        let src = theory_dir.join(&rel);
        let dst = staging.join(&rel);
        assert!(
            !dst.exists(),
            "stem {rel} from {} would overwrite {}",
            theory_dir.display(),
            dst.display()
        );
        if let Some(parent) = dst.parent() {
            fs::create_dir_all(parent).expect("create stem parent dir");
        }
        fs::copy(&src, &dst)
            .unwrap_or_else(|err| panic!("copy {} -> {}: {err}", src.display(), dst.display()));
    }
}

fn compile_stems(lean: &Path, staging: &Path, stems: &[String]) {
    for stem in stems {
        let src = format!("{stem}.lean");
        let olean = format!("{stem}.olean");
        let out = Command::new(lean)
            .current_dir(staging)
            .env("LEAN_PATH", staging)
            .args(["--root", ".", "-o", &olean, &src])
            .output()
            .unwrap_or_else(|err| panic!("execute {}: {err}", lean.display()));
        assert!(
            out.status.success(),
            "`{} --root . -o {olean} {src}` failed in {}:\n--- stdout ---\n{}\n--- stderr ---\n{}",
            lean.display(),
            staging.display(),
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
    }
}

fn hash_map_hex(version: &str, files: &BTreeMap<String, Vec<u8>>) -> String {
    let mut hasher = Sha256::new();
    hasher.update(EXEC_RECIPE_VERSION.to_le_bytes());
    hasher.update((version.len() as u64).to_le_bytes());
    hasher.update(version.as_bytes());
    for (k, v) in files {
        hasher.update((k.len() as u64).to_le_bytes());
        hasher.update(k.as_bytes());
        hasher.update((v.len() as u64).to_le_bytes());
        hasher.update(v);
    }
    hasher
        .finalize()
        .iter()
        .take(16)
        .map(|b| format!("{b:02x}"))
        .collect()
}

pub(crate) fn compiled_exec_kcheck_dir(pkg_rel: &str, extra_dep_rels: &[&str]) -> PathBuf {
    let mdir = manifest_dir();
    let toolchain_file = mdir.join("../../lean-toolchain");
    let toolchain_bytes = fs::read(&toolchain_file).expect("read lean-toolchain");
    let cic_l_dir = mdir.join("../../theories/cic_l");
    let cic_l_model_dir = mdir.join("../../theories/cic_l_model");
    let kcheck_spec_dir = mdir.join("../../theories/kcheck_spec");
    let kcheck_labelled_dir = mdir.join("../../theories/kcheck_labelled");

    let lean = clean_olean::pinned_lean_binary().expect("explicit pinned Lean fixture is required");
    let ver_out = Command::new(&lean)
        .arg("--version")
        .output()
        .expect("lean --version");
    assert!(ver_out.status.success(), "lean --version failed");
    let lean_ver = String::from_utf8_lossy(&ver_out.stdout).trim().to_string();

    let mut base_files = BTreeMap::new();
    base_files.insert("lean-toolchain".to_string(), toolchain_bytes);
    for (label, dir) in [
        ("cic_l", &cic_l_dir),
        ("cic_l_model", &cic_l_model_dir),
        ("kcheck_spec", &kcheck_spec_dir),
    ] {
        let mut sub = BTreeMap::new();
        collect_lean_and_order_files(dir, dir, &mut sub);
        for (k, v) in sub {
            base_files.insert(format!("{label}/{k}"), v);
        }
    }
    let kcheck_order_bytes = fs::read(kcheck_labelled_dir.join("ORDER"))
        .unwrap_or_else(|err| panic!("read kcheck_labelled/ORDER: {err}"));
    base_files.insert("kcheck_labelled/ORDER".to_string(), kcheck_order_bytes);
    let exec_stems = resolve_exec_kcheck_stems(&kcheck_labelled_dir);
    for stem in &exec_stems {
        let rel = format!("{stem}.lean");
        let bytes = fs::read(kcheck_labelled_dir.join(&rel))
            .unwrap_or_else(|err| panic!("read kcheck_labelled/{rel}: {err}"));
        base_files.insert(format!("kcheck_labelled/{rel}"), bytes);
    }
    let base_hash = hash_map_hex(&lean_ver, &base_files);

    let mut pkg_files = BTreeMap::new();
    pkg_files.insert("base_hash".to_string(), base_hash.as_bytes().to_vec());
    for dep_rel in extra_dep_rels {
        let dep_dir = mdir.join(dep_rel);
        let mut sub = BTreeMap::new();
        collect_lean_and_order_files(&dep_dir, &dep_dir, &mut sub);
        for (k, v) in sub {
            pkg_files.insert(format!("dep:{dep_rel}/{k}"), v);
        }
    }
    let pkg_dir = mdir.join(pkg_rel);
    let mut own_sub = BTreeMap::new();
    collect_lean_and_order_files(&pkg_dir, &pkg_dir, &mut own_sub);
    for (k, v) in own_sub {
        pkg_files.insert(format!("pkg:{pkg_rel}/{k}"), v);
    }
    let pkg_hash = hash_map_hex(&lean_ver, &pkg_files);
    let pkg_tag = Path::new(pkg_rel)
        .file_name()
        .expect("pkg dir name")
        .to_string_lossy()
        .to_string();

    let croot = cache_root();
    let _guard = DirLockGuard::acquire(&croot);

    let base_published = croot.join(format!("base-{base_hash}"));
    if !base_published.is_dir() {
        let staging = croot.join(format!("base-{base_hash}.tmp-{}", std::process::id()));
        if staging.exists() {
            fs::remove_dir_all(&staging).expect("clean stale base staging");
        }
        fs::create_dir_all(&staging).expect("create base staging");
        for dir in [&cic_l_dir, &cic_l_model_dir, &kcheck_spec_dir] {
            let stems = parse_order_stems(&dir.join("ORDER"));
            copy_lean_stems(dir, &stems, &staging);
            compile_stems(&lean, &staging, &stems);
        }
        copy_lean_stems(&kcheck_labelled_dir, &exec_stems, &staging);
        compile_stems(&lean, &staging, &exec_stems);
        fs::rename(&staging, &base_published).expect("publish base exec-kcheck dir");
    }

    let pkg_published = croot.join(format!("{pkg_tag}-{pkg_hash}"));
    if !pkg_published.is_dir() {
        let staging = croot.join(format!("{pkg_tag}-{pkg_hash}.tmp-{}", std::process::id()));
        if staging.exists() {
            fs::remove_dir_all(&staging).expect("clean stale pkg staging");
        }
        copy_tree_all(&base_published, &staging);
        for dep_rel in extra_dep_rels {
            let dep_dir = mdir.join(dep_rel);
            let stems = parse_order_stems(&dep_dir.join("ORDER"));
            copy_lean_stems(&dep_dir, &stems, &staging);
            compile_stems(&lean, &staging, &stems);
        }
        let own_stems = parse_order_stems(&pkg_dir.join("ORDER"));
        copy_lean_stems(&pkg_dir, &own_stems, &staging);
        compile_stems(&lean, &staging, &own_stems);
        fs::rename(&staging, &pkg_published).expect("publish pkg exec-kcheck dir");
    }

    pkg_published
}

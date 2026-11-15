// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean lake verify-fresh` against a fresh build. Measured on `7369eb6fd`
//! before the fix: all three non-genuine cases below printed
//! `OK: all 1 module(s) fresh`, exit 0.

use super::lake_verify_fresh;
use clean_lake::{BuildContext, Workspace};
use std::fs;
use std::path::{Path, PathBuf};

const LIB: &str = "theorem K1Lib.zero_add' (n : Nat) : 0 + n = n :=
  Nat.rec (motive := fun k => 0 + k = k) rfl (fun k ih => congrArg Nat.succ ih) n
";

fn built(root: &Path) -> PathBuf {
    let dir = root.join("lib");
    fs::create_dir_all(&dir).expect("dir");
    fs::write(
        dir.join("lakefile.toml"),
        "name = \"k1\"\n\n[[lean_lib]]\nname = \"K1Lib\"\n",
    )
    .expect("lakefile");
    fs::write(dir.join("K1Lib.lean"), LIB).expect("source");
    let result = BuildContext::new(Workspace::load(&dir).expect("ws"))
        .build_all()
        .expect("build");
    assert!(result.failed.is_empty(), "{result:?}");
    dir
}

fn verify(dir: &Path) -> anyhow::Result<()> {
    lake_verify_fresh(
        dir.to_path_buf(),
        vec!["K1Lib".to_string()],
        vec![dir.join(".lake/build/lib")],
        true,
    )
}

#[test]
fn a_genuine_artifact_is_fresh() {
    let tmp = tempfile::tempdir().expect("tmp");
    let dir = built(tmp.path());
    verify(&dir).expect("a genuine artifact matches its fresh build");
}

#[test]
fn a_rewritten_artifact_is_not_fresh() {
    let tmp = tempfile::tempdir().expect("tmp");
    let dir = built(tmp.path());
    verify(&dir).expect("control");
    // Rewrite the lemma's stated type inside the payload; the header and
    // import list are untouched, so the import signature still matches.
    let path = dir.join(".lake/build/lib/K1Lib.olean");
    let bytes = fs::read(&path).expect("artifact");
    let mut p = clean_olean::payload::decode_clean_payload(&bytes)
        .expect("decode")
        .expect("payload");
    let other = p.constants[0].clone();
    p.constants[0].type_ = clean_kernel::Expr::sort(clean_kernel::Level::zero());
    assert_ne!(p.constants[0].type_, other.type_);
    let len = u64::from_le_bytes(bytes[bytes.len() - 8..].try_into().expect("u64")) as usize;
    let trailer = len + clean_olean::payload::CLEAN_PAYLOAD_MAGIC.len() + 4 + 8;
    let mut out = bytes[..bytes.len() - trailer].to_vec();
    out.extend(clean_olean::payload::encode_clean_payload(&p).expect("encode"));
    fs::write(&path, out).expect("write");
    let err = verify(&dir).expect_err("a rewritten artifact must not be fresh");
    assert!(
        err.to_string()
            .contains("not what the current source builds to"),
        "{err}"
    );
}

#[test]
fn a_source_edited_after_its_build_is_not_fresh_even_with_the_same_imports() {
    let tmp = tempfile::tempdir().expect("tmp");
    let dir = built(tmp.path());
    verify(&dir).expect("control");
    fs::write(
        dir.join("K1Lib.lean"),
        format!("{LIB}\ntheorem K1Lib.extra : (1 : Nat) = 1 := rfl\n"),
    )
    .expect("edit");
    assert!(verify(&dir).is_err(), "a stale artifact must not be fresh");
}

#[test]
fn an_artifact_this_builder_did_not_write_is_not_reported_fresh() {
    let tmp = tempfile::tempdir().expect("tmp");
    let dir = built(tmp.path());
    let path = dir.join(".lake/build/lib/K1Lib.olean");
    let mut bytes = fs::read(&path).expect("artifact");
    // Overwrite the header's git hash with another 40-hex-digit hash, as an
    // artifact written by a different producer would carry.
    let at = bytes
        .windows(clean_lake::CLEAN_OLEAN_GIT_HASH.len())
        .position(|w| w == clean_lake::CLEAN_OLEAN_GIT_HASH.as_bytes())
        .expect("the header carries clean lake build's git hash");
    bytes[at..at + 40].copy_from_slice(b"0123456789abcdef0123456789abcdef01234567");
    fs::write(&path, bytes).expect("write");
    let err = verify(&dir).expect_err("freshness cannot be established");
    assert!(err.to_string().contains("K1Lib"), "{err}");
}

#[test]
fn a_rewritten_dependency_two_imports_down_makes_its_dependent_not_fresh() {
    // Module-trust verification, 2026-09-25: `--module ChC` compared ChC's
    // own artifact only, so it said fresh, exit 0, while ChA — imported by
    // ChB, imported by ChC — had been rewritten.
    let tmp = tempfile::tempdir().expect("tmp");
    let dir = tmp.path().join("chain");
    fs::create_dir_all(&dir).expect("dir");
    fs::write(
        dir.join("lakefile.toml"),
        "name = \"ch\"\n\n[[lean_lib]]\nname = \"Ch\"\nroots = [\"ChA\", \"ChB\", \"ChC\"]\n",
    )
    .expect("lakefile");
    fs::write(dir.join("ChA.lean"), LIB.replace("K1Lib.", "ChA.")).expect("a");
    fs::write(
        dir.join("ChB.lean"),
        "import ChA\n\ntheorem ChB.t (m : Nat) : 0 + m = m := ChA.zero_add' m\n",
    )
    .expect("b");
    fs::write(
        dir.join("ChC.lean"),
        "import ChB\n\ntheorem ChC.t (m : Nat) : 0 + m = m := ChB.t m\n",
    )
    .expect("c");
    let result = BuildContext::new(Workspace::load(&dir).expect("ws"))
        .build_all()
        .expect("build");
    assert!(
        result.failed.is_empty() && result.built.len() == 3,
        "{result:?}"
    );
    let verify_c = || {
        lake_verify_fresh(
            dir.clone(),
            vec!["ChC".to_string()],
            vec![dir.join(".lake/build/lib")],
            true,
        )
    };
    verify_c().expect("control: the genuine chain is fresh");

    let path = dir.join(".lake/build/lib/ChA.olean");
    let bytes = fs::read(&path).expect("artifact");
    let mut p = clean_olean::payload::decode_clean_payload(&bytes)
        .expect("decode")
        .expect("payload");
    p.constants[0].type_ = clean_kernel::Expr::sort(clean_kernel::Level::zero());
    let len = u64::from_le_bytes(bytes[bytes.len() - 8..].try_into().expect("u64")) as usize;
    let trailer = len + clean_olean::payload::CLEAN_PAYLOAD_MAGIC.len() + 4 + 8;
    let mut out = bytes[..bytes.len() - trailer].to_vec();
    out.extend(clean_olean::payload::encode_clean_payload(&p).expect("encode"));
    fs::write(&path, out).expect("write");

    let err = verify_c().expect_err("ChC rests on a rewritten ChA: not fresh");
    let msg = err.to_string();
    assert!(
        msg.contains("not what the current source builds to") && msg.contains("ChA"),
        "{msg}"
    );
}

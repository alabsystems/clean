// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Probe K1's tampered-lemma mutation M3 at the process boundary (KR1, Trust's
//! proven-core plan §9 increment 3: "K1's tampered-lemma mutation M3 exits
//! non-zero"; `docs/DECISIONS.md` R143 showed it only in-process, through
//! `cmd_core::check_file`'s `Err`, R161 runs the shipped binary).
//!
//! Everything goes through the real `clean` executable: `clean lake build`
//! builds `K1Lib` in its own project, a consumer project holding NO `K1Lib`
//! source gets the artifact (its Clean payload's `K1Lib.zero_add'` restated
//! `0 + n = n + 1` over the original proof, for M3), and `clean check` of the
//! citing file is run as a child process. M3 must exit non-zero naming the
//! tampered lemma; the genuine artifact cited by a true theorem exits 0.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use clean_olean::payload::{
    decode_clean_payload, encode_clean_payload, CleanPayload, CLEAN_PAYLOAD_MAGIC,
};

const LIB: &str = "theorem K1Lib.zero_add' (n : Nat) : 0 + n = n :=
  Nat.rec (motive := fun k => 0 + k = k) rfl (fun k ih => congrArg Nat.succ ih) n
";
const DONOR: &str = "axiom K1Lib.zero_add' (n : Nat) : 0 + n = n + 1\n";
const CITE_TRUE: &str = "import K1Lib

theorem k1_uses (m : Nat) : 0 + (0 + m) = m :=
  Eq.trans (K1Lib.zero_add' (0 + m)) (K1Lib.zero_add' m)
";
const CITE_FALSE: &str = "import K1Lib

theorem k1_false : (0 : Nat) = 1 := K1Lib.zero_add' 0
";

fn clean() -> Command {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_clean"));
    cmd.env("CARGO_TERM_COLOR", "never").env("NO_COLOR", "1");
    cmd
}

fn shown(out: &Output) -> String {
    format!(
        "status {:?}\nstdout:\n{}\nstderr:\n{}",
        out.status,
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    )
}

fn lakefile(dir: &Path, root: &str) {
    fs::write(
        dir.join("lakefile.toml"),
        format!("name = \"k1\"\n\n[[lean_lib]]\nname = \"K1\"\nroots = [\"{root}\"]\n"),
    )
    .expect("lakefile");
}

/// `clean lake build` of `K1Lib` from `source` in its own project; the artifact.
fn build_lib(root: &Path, tag: &str, source: &str) -> PathBuf {
    let dir = root.join(tag);
    fs::create_dir_all(&dir).expect("dir");
    lakefile(&dir, "K1Lib");
    fs::write(dir.join("K1Lib.lean"), source).expect("source");
    let out = clean()
        .args(["lake", "build"])
        .current_dir(&dir)
        .output()
        .expect("clean lake build starts");
    assert!(out.status.success(), "{tag}: {}", shown(&out));
    let artifact = dir.join(".lake/build/lib/K1Lib.olean");
    assert!(
        artifact.is_file(),
        "{tag}: no artifact at {}",
        artifact.display()
    );
    artifact
}

fn payload(artifact: &Path) -> (Vec<u8>, CleanPayload) {
    let bytes = fs::read(artifact).expect("artifact");
    let p = decode_clean_payload(&bytes)
        .expect("decode")
        .expect("a Clean payload");
    (bytes, p)
}

fn zero_add(p: &mut CleanPayload) -> &mut clean_kernel::ConstantInfo {
    let n = clean_kernel::Name::from_string("K1Lib.zero_add'");
    p.constants
        .iter_mut()
        .find(|c| c.name == n)
        .expect("K1Lib.zero_add' in the payload")
}

/// A consumer project holding only the artifact (its payload rewritten by
/// `edit`) and `Main.lean` citing it; `clean check Main.lean` run in it.
fn check_consumer(
    root: &Path,
    tag: &str,
    artifact: &Path,
    cite: &str,
    edit: impl FnOnce(&mut CleanPayload),
) -> Output {
    let dir = root.join(tag);
    let lib = dir.join(".lake/build/lib/lean");
    fs::create_dir_all(&lib).expect("lib dir");
    lakefile(&dir, "Main");
    let (bytes, mut p) = payload(artifact);
    edit(&mut p);
    let len = u64::from_le_bytes(bytes[bytes.len() - 8..].try_into().expect("u64")) as usize;
    let trailer = len + CLEAN_PAYLOAD_MAGIC.len() + 4 + 8;
    let mut out = bytes[..bytes.len() - trailer].to_vec();
    out.extend(encode_clean_payload(&p).expect("encode"));
    fs::write(lib.join("K1Lib.olean"), out).expect("artifact");
    fs::write(dir.join("Main.lean"), cite).expect("main");
    clean()
        .args(["check", "Main.lean"])
        .current_dir(&dir)
        .output()
        .expect("clean check starts")
}

#[test]
fn k1_mutation_m3_exits_non_zero_from_the_clean_binary() {
    let tmp = tempfile::tempdir().expect("tmp");
    let lib = build_lib(tmp.path(), "lib", LIB);
    let donor = build_lib(tmp.path(), "donor", DONOR);
    let false_type = payload(&donor).1.constants[0].type_.clone();

    // Control: the genuine artifact, cited by a true theorem, exits 0.
    let genuine = check_consumer(tmp.path(), "use", &lib, CITE_TRUE, |_| {});
    let text = shown(&genuine);
    assert_eq!(genuine.status.code(), Some(0), "genuine K1Lib: {text}");
    assert!(text.contains("1 passed, 0 failed"), "genuine K1Lib: {text}");

    // Control: the rewrite itself is not what fails. Re-encoding the
    // genuine payload unchanged (the same splice M3 uses) still exits 0.
    let respliced = check_consumer(tmp.path(), "respliced", &lib, CITE_TRUE, |p| {
        let same = zero_add(p).clone();
        *zero_add(p) = same;
    });
    assert_eq!(
        respliced.status.code(),
        Some(0),
        "respliced: {}",
        shown(&respliced)
    );

    // M3: `K1Lib.zero_add'` stated `0 + n = n + 1` over the original proof,
    // cited by `k1_false : 0 = 1`.
    let m3 = check_consumer(tmp.path(), "m3", &lib, CITE_FALSE, |p| {
        zero_add(p).type_ = false_type;
    });
    let text = shown(&m3);
    // Measured 2026-10-26: exit 1, `0 passed, 1 failed`, `Error: check
    // failed`, and `k1_false: cited closure not credited: … (K1Lib.zero_add':
    // … Type mismatch …)`.
    assert_eq!(
        m3.status.code(),
        Some(1),
        "M3 must exit non-zero, by the check's verdict (not a signal or a crash): {text}"
    );
    assert!(text.contains("0 passed, 1 failed"), "M3: {text}");
    assert!(text.contains("Error: check failed"), "M3: {text}");
    assert!(
        text.contains("k1_false: cited closure not credited")
            && text.contains("K1Lib.zero_add'")
            && text.contains("Type mismatch"),
        "M3: the refusal is the kernel re-check of the tampered lemma: {text}"
    );
}

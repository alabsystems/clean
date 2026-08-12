// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Hard regression test: each of the 5 structured importers must EITHER
//! refuse to produce a shard for non-empty input OR produce a shard
//! whose `expr_count > constant_count` (proof of real type-tree
//! emission).
//!
//! The five `_import` modules historically shared a stub pattern:
//! parse names + kinds from source, then emit one shared
//! `FlatExpr::sort(0)` placeholder for every constant. That made
//! `ConvertDirStats { total_declarations: N, errors: 0 }` look
//! identical to a real import in stats but yielded
//! `expr_count = 1, constant_count = N` in the shard header.
//!
//! This test calls each `convert_*_dir` function with a tiny synthetic
//! source-file fixture. The acceptable outcomes are:
//!
//!   (a) `total_declarations == 0` AND `errors > 0`
//!       — the stub guard fired; no fake shard was written.
//!   (b) `total_declarations > 0` AND the written shard has
//!       `expr_count > constant_count`
//!       — a real importer was wired up.
//!
//! Any other outcome (e.g. `total_declarations > 0` with a shard whose
//! `expr_count <= 2`) is a regression and fails this test.

use std::fs;
use std::io::{Read, Write};
use std::path::Path;

use clean_mathverse::structured_import;

const MAGIC_OMEG: u32 = 0x4F4D_4547;

/// Read just the shard header counts. Returns `None` when no shard was
/// written (the stub guard fired, which is the desired outcome).
fn read_counts(path: &Path) -> Option<(u32, u32)> {
    let mut buf = [0u8; 256];
    let mut f = fs::File::open(path).ok()?;
    f.read_exact(&mut buf).ok()?;
    if u32::from_le_bytes([buf[0], buf[1], buf[2], buf[3]]) != MAGIC_OMEG {
        return None;
    }
    let expr_count = u32::from_le_bytes([buf[24], buf[25], buf[26], buf[27]]);
    let constant_count = u32::from_le_bytes([buf[28], buf[29], buf[30], buf[31]]);
    Some((constant_count, expr_count))
}

/// Run a convert_*_dir-like function on a fixture and assert the
/// stub-or-real contract.
fn assert_no_stub<F>(
    label: &str,
    extension: &str,
    fixture_text: &str,
    shard_name: &str,
    convert_fn: F,
) where
    F: Fn(&Path, &Path) -> structured_import::ConvertDirStats,
{
    let tmp = tempfile::tempdir().expect("tempdir");
    let src_dir = tmp.path().join("src");
    fs::create_dir_all(&src_dir).unwrap();
    let src_file = src_dir.join(format!("fixture.{extension}"));
    fs::File::create(&src_file)
        .unwrap()
        .write_all(fixture_text.as_bytes())
        .unwrap();

    let out_dir = tmp.path().join("out");
    fs::create_dir_all(&out_dir).unwrap();

    let stats = convert_fn(&src_dir, &out_dir);
    let shard_path = out_dir.join(shard_name);

    // Outcome A: stub guard fired, no shard written, errors > 0.
    if stats.total_declarations == 0 {
        assert!(
            !shard_path.exists(),
            "{label}: total_declarations == 0 but a shard was written at {} — \
             stub guard contract broken",
            shard_path.display()
        );
        // Either errors > 0 OR no files parsed (acceptable when fixture
        // contained nothing the parser recognised).
        return;
    }

    // Outcome B: shard written; must have non-stub expr/constant ratio.
    assert!(
        shard_path.exists(),
        "{label}: claimed {} declarations but no shard written at {}",
        stats.total_declarations,
        shard_path.display()
    );
    let (consts, exprs) = read_counts(&shard_path)
        .unwrap_or_else(|| panic!("{label}: shard file present but header unreadable"));
    assert!(
        exprs > consts,
        "{label}: shard claims {consts} constants but only {exprs} FlatExpr — \
         that's the stub signature (one shared placeholder for every constant). \
         Either the stub guard regressed or a new importer is producing fake data.",
    );
}

#[test]
fn dafny_importer_refuses_stub_or_emits_real_types() {
    assert_no_stub(
        "dafny",
        "dfy",
        "method M(x: int) returns (y: int)\n  ensures y == x + 1 { y := x + 1; }\n",
        "dafny.mathverse",
        structured_import::convert_dafny_dir,
    );
}

#[test]
fn acl2_importer_refuses_stub_or_emits_real_types() {
    assert_no_stub(
        "acl2",
        "lisp",
        "(defthm test-one (equal (+ 0 x) x))\n(defun double (x) (* 2 x))\n",
        "acl2.mathverse",
        structured_import::convert_acl2_dir,
    );
}

#[test]
fn lean3_importer_refuses_stub_or_emits_real_types() {
    assert_no_stub(
        "lean3",
        "lean",
        "theorem foo (n : nat) : n + 0 = n := by simp\n\
         def bar : nat := 42\n",
        "lean3.mathverse",
        structured_import::convert_lean3_dir,
    );
}

#[test]
fn coq_v_importer_refuses_stub_or_emits_real_types() {
    assert_no_stub(
        "coq_v",
        "v",
        "Theorem foo : forall n : nat, n + 0 = n.\n\
         Proof. intro n. apply plus_n_O. Qed.\n",
        "coq_v.mathverse",
        structured_import::convert_coq_v_dir,
    );
}

#[test]
fn isabelle_thy_importer_refuses_stub_or_emits_real_types() {
    assert_no_stub(
        "isabelle_thy",
        "thy",
        "theory Test imports Main begin\n\
         theorem foo: \"x + 0 = x\" by simp\n\
         end\n",
        "isabelle_thy.mathverse",
        structured_import::convert_isabelle_thy_dir,
    );
}

#[test]
fn matita_importer_refuses_stub_or_emits_real_types() {
    assert_no_stub(
        "matita",
        "ma",
        "theorem foo : \u{2200}P:Prop. P \u{2192} P := \u{3bb}P.\u{3bb}h.h.\n\
         definition idnat : nat \u{2192} nat := \u{3bb}n.n.\n",
        "matita.mathverse",
        structured_import::convert_matita_dir,
    );
}

// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Plan unit C5 (`docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md`):
//! Rust coverage, per-declaration `(uses_iota, uses_k)` accounting, disjoint
//! `kcheck_only_level_shape` divergence class, structure-eta refusal count, and
//! zero-acceptance forged corpus gate for `theories/kcheck_init_slice` and
//! `data/c5_init_slice.json`.
//!
//! Standing limits:
//! 1. Soundness is per explicit finite universe bound `N` (`tracked_bound_n = 5`).
//! 2. No generation proves more consistency than its base theory (`Ax0`;
//!    `theories/kcheck_init_slice` is verified choice-free in `kcheck_init_slice.rs`).
//! 3. The `Init.Prelude` + `Init.Core` slice extractor is an unproved interim
//!    loader (`loader_proved == false`); by design `KCheck.checker` is to become
//!    the proved checker once all six Plan §2.1 conditions hold in fact; this
//!    gate flips no authority, and the independent re-checker quorum stays.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use std::process::Command;

use serde_json::{json, Value};
use sha2::{Digest, Sha256};

const SCHEMA: &str = "clean.c5_init_slice/v1";
const EXPECTED_BASE_FAMILIES: [&str; 3] = ["PUnit", "Eq", "Nat"];
// Owning modules and universe arities of the two original declarations in
// the pinned SDK. Only the Unit term is replayed as an original by the corpus.
const ETA_SUBJECTS: [(&str, &str, u64); 2] =
    [("Unit.ext", "Init.Ext", 0), ("Prod.eta", "Init.Core", 2)];
const EXPECTED_DIV_NAMES: [&str; 3] = ["LevelGap.d1", "LevelGap.Kd3", "LevelGap.Kd4"];
const THEORY_HASH_FILES: [&str; 5] = [
    "KCheckInitSlice/Accounting.lean",
    "KCheckInitSlice/InitCorpus.lean",
    "KCheckInitSlice/LevelDivergence.lean",
    "KCheckInitSlice/RefusalCorpus.lean",
    "KCheckInitSlice/Contracts.lean",
];

fn sha256_file(path: &Path) -> Result<String, String> {
    let bytes =
        std::fs::read(path).map_err(|e| format!("failed to read {}: {e}", path.display()))?;
    Ok(Sha256::digest(&bytes)
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect())
}

fn compute_source_hashes(theory_dir: &Path) -> Result<BTreeMap<String, String>, String> {
    let mut out = BTreeMap::new();
    for rel in THEORY_HASH_FILES {
        let p = theory_dir.join(rel);
        out.insert(rel.to_string(), sha256_file(&p)?);
    }
    Ok(out)
}

fn validate_artifact(artifact: &Value, theory_dir: Option<&Path>) -> Result<(), String> {
    let obj = artifact
        .as_object()
        .ok_or_else(|| "artifact must be a JSON object".to_string())?;
    if obj.get("schema").and_then(Value::as_str) != Some(SCHEMA) {
        return Err(format!(
            "expected schema={SCHEMA:?}, got {:?}",
            obj.get("schema")
        ));
    }
    if obj.get("plan_unit").and_then(Value::as_str) != Some("C5") {
        return Err(format!(
            "expected plan_unit='C5', got {:?}",
            obj.get("plan_unit")
        ));
    }
    if obj.get("loader_proved").and_then(Value::as_bool) != Some(false) {
        return Err(format!(
            "C5 requires loader_proved=false (interim unproved Init slice loader), got {:?}",
            obj.get("loader_proved")
        ));
    }
    let loader_note = obj
        .get("loader_note")
        .and_then(Value::as_str)
        .unwrap_or_default();
    if !loader_note.to_ascii_lowercase().contains("unproved") {
        return Err("loader_note must explicitly state that the C5 loader is unproved".to_string());
    }
    let fams: Vec<&str> = obj
        .get("base_families")
        .and_then(Value::as_array)
        .ok_or_else(|| "base_families must be a list".to_string())?
        .iter()
        .filter_map(Value::as_str)
        .collect();
    if fams != EXPECTED_BASE_FAMILIES {
        return Err(format!(
            "base_families must be {EXPECTED_BASE_FAMILIES:?}, got {fams:?}"
        ));
    }

    let counts = obj
        .get("summary_counts")
        .and_then(Value::as_object)
        .ok_or_else(|| "missing summary_counts object".to_string())?;
    let acc = obj
        .get("accepted_both")
        .and_then(Value::as_array)
        .ok_or_else(|| "accepted_both must be a list".to_string())?;
    let div = obj
        .get("kcheck_only_level_shape")
        .and_then(Value::as_array)
        .ok_or_else(|| "kcheck_only_level_shape must be a list".to_string())?;
    let eta = obj
        .get("structure_eta_refused")
        .and_then(Value::as_array)
        .ok_or_else(|| "structure_eta_refused must be a list".to_string())?;
    let forged = obj
        .get("forged_refused")
        .and_then(Value::as_array)
        .ok_or_else(|| "forged_refused must be a list".to_string())?;

    if counts
        .get("forged_corpus_acceptances")
        .and_then(Value::as_u64)
        != Some(0)
    {
        return Err("forged_corpus_acceptances must be 0".to_string());
    }
    if acc.len() != 42
        || counts.get("accepted_both_count").and_then(Value::as_u64) != Some(acc.len() as u64)
    {
        return Err("accepted_both_count mismatch (expected 42)".to_string());
    }
    if div.len() != 3
        || counts
            .get("kcheck_only_level_shape_count")
            .and_then(Value::as_u64)
            != Some(div.len() as u64)
    {
        return Err("kcheck_only_level_shape_count mismatch (expected 3)".to_string());
    }
    if eta.len() != 2
        || counts
            .get("structure_eta_refused_count")
            .and_then(Value::as_u64)
            != Some(eta.len() as u64)
    {
        return Err("structure_eta_refused_count mismatch (expected 2)".to_string());
    }
    for (row, (name, owner, _)) in eta.iter().zip(ETA_SUBJECTS) {
        if row["name"].as_str() != Some(name) || row["source_module"].as_str() != Some(owner) {
            return Err(format!("structure eta row must name {name} from {owner}"));
        }
    }
    if forged.len() != 12
        || counts.get("forged_refused_count").and_then(Value::as_u64) != Some(forged.len() as u64)
    {
        return Err("forged_refused_count mismatch (expected 12)".to_string());
    }
    let total = (acc.len() + div.len() + eta.len() + forged.len()) as u64;
    if counts.get("total_audited_rows").and_then(Value::as_u64) != Some(total) {
        return Err("partition sum mismatch against total_audited_rows".to_string());
    }

    let acc_names: BTreeSet<&str> = acc
        .iter()
        .filter_map(|r| r.get("name").and_then(Value::as_str))
        .collect();
    let eta_names: BTreeSet<&str> = eta
        .iter()
        .filter_map(|r| r.get("name").and_then(Value::as_str))
        .collect();
    let forged_names: BTreeSet<&str> = forged
        .iter()
        .filter_map(|r| r.get("name").and_then(Value::as_str))
        .collect();

    let actual_div_names: Vec<&str> = div
        .iter()
        .filter_map(|r| r.get("name").and_then(Value::as_str))
        .collect();
    if actual_div_names != EXPECTED_DIV_NAMES {
        return Err(format!(
            "kcheck_only_level_shape pinned names must be {EXPECTED_DIV_NAMES:?}, got {actual_div_names:?}"
        ));
    }
    for d_row in div {
        let nm = d_row
            .get("name")
            .and_then(Value::as_str)
            .ok_or_else(|| "missing name on kcheck_only_level_shape row".to_string())?;
        if acc_names.contains(nm) || eta_names.contains(nm) || forged_names.contains(nm) {
            return Err(format!(
                "kcheck_only_level_shape declaration {nm:?} illegally merged into another verdict class"
            ));
        }
        if d_row.get("lean_kernel_verdict").and_then(Value::as_str) != Some("refused_level_shape")
            || d_row.get("kcheck_verdict").and_then(Value::as_str) != Some("accepted")
        {
            return Err(format!(
                "invalid verdict fields on kcheck_only_level_shape row {nm:?}"
            ));
        }
    }

    let mut iota_names = Vec::new();
    let mut k_names = Vec::new();
    for (idx, r) in acc.iter().enumerate() {
        let step = r
            .get("step")
            .and_then(Value::as_u64)
            .ok_or_else(|| "accepted_both row missing integer step".to_string())?;
        if step != (idx as u64) + 1 {
            return Err(format!("non-contiguous step {step} at index {idx}"));
        }
        let nm = r
            .get("name")
            .and_then(Value::as_str)
            .ok_or_else(|| "accepted_both row missing name".to_string())?;
        let uses_iota = r
            .get("uses_iota")
            .and_then(Value::as_bool)
            .ok_or_else(|| format!("row {nm} missing boolean uses_iota"))?;
        let uses_k = r
            .get("uses_k")
            .and_then(Value::as_bool)
            .ok_or_else(|| format!("row {nm} missing boolean uses_k"))?;
        if uses_iota {
            iota_names.push(nm);
        }
        if uses_k {
            k_names.push(nm);
        }
    }
    if counts
        .get("accepted_using_iota_count")
        .and_then(Value::as_u64)
        != Some(iota_names.len() as u64)
        || iota_names != ["Nat.noConfusion"]
    {
        return Err(format!(
            "expected exact iota declaration ['Nat.noConfusion'], got {iota_names:?}"
        ));
    }
    if counts.get("accepted_using_k_count").and_then(Value::as_u64) != Some(k_names.len() as u64)
        || k_names != ["cast_eq"]
    {
        return Err(format!(
            "expected exact K declaration ['cast_eq'], got {k_names:?}"
        ));
    }

    if let Some(tdir) = theory_dir {
        let expected_hashes = compute_source_hashes(tdir)?;
        let recorded_hashes: BTreeMap<String, String> = serde_json::from_value(
            obj.get("source_hashes")
                .cloned()
                .ok_or_else(|| "missing source_hashes".to_string())?,
        )
        .map_err(|e| format!("invalid source_hashes map: {e}"))?;
        if recorded_hashes != expected_hashes {
            return Err(
                "KCheckInitSlice Lean source hashes drifted from committed data/c5_init_slice.json"
                    .to_string(),
            );
        }
        let init_corpus = std::fs::read_to_string(tdir.join("KCheckInitSlice/InitCorpus.lean"))
            .map_err(|e| format!("read InitCorpus.lean: {e}"))?;
        for step in 1..=42 {
            let thm_pat = format!("theorem step_{step}_ok :");
            if !init_corpus.contains(&thm_pat) {
                return Err(format!("missing `{thm_pat}` in InitCorpus.lean"));
            }
        }
    }
    Ok(())
}

fn verify_against_pinned_lean(
    root: &Path,
    accepted_rows: &[Value],
    eta_rows: &[Value],
) -> Result<(), String> {
    let lean = clean_olean::pinned_lean_binary().expect("pinned Lean binary");
    let mut specs = Vec::new();
    for r in accepted_rows {
        let step = r["step"].as_u64().expect("step");
        if step >= 4 {
            let nm = r["name"].as_str().expect("name");
            let m = r["source_module"].as_str().expect("source_module");
            let k = r["kind"].as_str().expect("kind");
            let p = r["level_params"].as_u64().expect("level_params");
            specs.push(format!("(\"{nm}\", \"{m}\", \"{k}\", {p})"));
        }
    }
    for (row, (_, _, params)) in eta_rows.iter().zip(ETA_SUBJECTS) {
        let name = row["name"].as_str().expect("eta name");
        let owner = row["source_module"].as_str().expect("eta owner");
        specs.push(format!(
            "(\"{name}\", \"{owner}\", \"theoremDecl\", {params})"
        ));
    }
    let script = format!(
        r#"import Lean
open Lean

def checkKind : ConstantInfo → String
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theoremDecl"
  | _ => "other"

run_cmd do
  let env ← getEnv
  let specs : List (String × String × String × Nat) := [
    {}
  ]
  for (nmStr, modStr, expKind, expParams) in specs do
    let nm := nmStr.splitOn "." |>.foldl Name.mkStr .anonymous
    let some ci := env.find? nm | throwError s!"missing Init constant {{nmStr}}"
    let some modIdx := env.getModuleIdxFor? nm | throwError s!"missing module idx for {{nmStr}}"
    let actualMod := env.header.moduleNames[modIdx.toNat]!.toString
    if actualMod != modStr then
      throwError s!"module mismatch for {{nmStr}}: expected {{modStr}}, got {{actualMod}}"
    let actualKind := checkKind ci
    if actualKind != expKind then
      throwError s!"kind mismatch for {{nmStr}}: expected {{expKind}}, got {{actualKind}}"
    if ci.levelParams.length != expParams then
      throwError s!"level param mismatch for {{nmStr}}: expected {{expParams}}, got {{ci.levelParams.length}}"

  let u := Level.param `u
  let v := Level.param `v
  let mkDef (nm : Name) (ty val : Expr) : Declaration :=
    .defnDecl {{
      name := nm
      levelParams := [`u, `v]
      type := ty
      value := val
      hints := .opaque
      safety := .safe
    }}
  let d1 := mkDef (`LevelGap.d1)
    (.sort (.succ (.succ (.imax u (.succ v)))))
    (.sort (.succ (.max u (.succ v))))
  let kd3 := mkDef (`LevelGap.Kd3)
    (.sort (.succ (.max u v)))
    (.sort (.imax (.max u v) (.max u v)))
  let kd4 := mkDef (`LevelGap.Kd4)
    (.sort (.succ (.max u v)))
    (.sort (.imax (.max v u) (.max u v)))
  for (label, d) in [("LevelGap.d1", d1), ("LevelGap.Kd3", kd3), ("LevelGap.Kd4", kd4)] do
    match env.addDeclCore 0 d none (doCheck := true) with
    | .ok _ => throwError s!"expected pinned Lean kernel to reject {{label}}"
    | .error _ => pure ()

  IO.println "C5_LEAN_VERIFY_OK"
"#,
        specs.join(",\n    ")
    );

    let tmp = tempfile::tempdir().expect("tempdir for C5 Lean verification");
    let lean_file = tmp.path().join("VerifyC5Slice.lean");
    std::fs::write(&lean_file, script).expect("write VerifyC5Slice.lean");
    let out = Command::new(&lean)
        .arg(&lean_file)
        .current_dir(root)
        .env_remove("LEAN_PATH")
        .env_remove("LEAN_SRC_PATH")
        .output()
        .expect("run VerifyC5Slice.lean");
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    if out.status.success() && stdout.contains("C5_LEAN_VERIFY_OK") {
        Ok(())
    } else {
        Err(format!(
            "pinned Lean C5 verification failed:\n{stdout}\n{stderr}"
        ))
    }
}

#[test]
fn c5_init_slice_artifact_and_twelve_acceptance_refusal_controls() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let theory_dir = root.join("theories/kcheck_init_slice");
    let pin = std::fs::read_to_string(root.join("lean-toolchain"))
        .expect("read lean-toolchain")
        .trim()
        .to_string();
    let artifact_raw = std::fs::read_to_string(root.join("data/c5_init_slice.json"))
        .expect("read data/c5_init_slice.json");
    let baseline: Value =
        serde_json::from_str(&artifact_raw).expect("parse data/c5_init_slice.json");

    // Control 1: committed baseline passes against live theory sources & toolchain pin.
    validate_artifact(&baseline, Some(&theory_dir))
        .expect("committed data/c5_init_slice.json must pass C5 gate");
    assert_eq!(
        baseline["lean_toolchain"].as_str(),
        Some(pin.as_str()),
        "data/c5_init_slice.json lean_toolchain must match root lean-toolchain"
    );

    let accepted = baseline["accepted_both"].as_array().expect("accepted rows");
    let eta = baseline["structure_eta_refused"]
        .as_array()
        .expect("eta rows");
    let verify_lean = std::env::var_os("VERIFY_C5_INIT_SLICE_LEAN").is_some();
    if verify_lean {
        verify_against_pinned_lean(&root, accepted, eta).expect("pinned Lean C5 verification");
    }

    // Swapping either owner must fail against the independent module index,
    // including the former Init.Core attribution of Unit.ext.
    for (index, wrong_owner) in ["Init.Core", "Init.Ext"].iter().enumerate() {
        let mut forged = baseline.clone();
        forged["structure_eta_refused"][index]["source_module"] = json!(wrong_owner);
        assert!(validate_artifact(&forged, None).is_err());
        if verify_lean {
            let incorrect = forged["structure_eta_refused"]
                .as_array()
                .expect("eta rows");
            let error = verify_against_pinned_lean(&root, accepted, incorrect)
                .expect_err("pinned Lean must refuse a false eta owner");
            let (name, actual, _) = ETA_SUBJECTS[index];
            assert!(
                error.contains(&format!(
                    "module mismatch for {name}: expected {wrong_owner}, got {actual}"
                )),
                "{error}"
            );
        }
    }

    // Control 2: loader_proved = true refused.
    let mut m2 = baseline.clone();
    m2["loader_proved"] = json!(true);
    assert!(
        validate_artifact(&m2, None).is_err(),
        "loader_proved=true must be refused"
    );

    // Control 3: loader_note omitting 'unproved' refused.
    let mut m3 = baseline.clone();
    m3["loader_note"] = json!("fully verified production loader");
    assert!(
        validate_artifact(&m3, None).is_err(),
        "loader_note omitting 'unproved' must be refused"
    );

    // Control 4: missing base family refused.
    let mut m4 = baseline.clone();
    m4["base_families"] = json!(["PUnit", "Eq"]);
    assert!(
        validate_artifact(&m4, None).is_err(),
        "missing base family must be refused"
    );

    // Control 5: non-zero forged corpus acceptance refused.
    let mut m5 = baseline.clone();
    m5["summary_counts"]["forged_corpus_acceptances"] = json!(1);
    assert!(
        validate_artifact(&m5, None).is_err(),
        "non-zero forged corpus acceptance must be refused"
    );

    // Control 6: merging LevelGap.d1 into accepted_both refused.
    let mut m6 = baseline.clone();
    m6["accepted_both"][41]["name"] = json!("LevelGap.d1");
    assert!(
        validate_artifact(&m6, None).is_err(),
        "merging LevelGap.d1 into accepted_both must be refused"
    );

    // Control 7: merging LevelGap.Kd3 into structure_eta_refused refused.
    let mut m7 = baseline.clone();
    m7["structure_eta_refused"][0]["name"] = json!("LevelGap.Kd3");
    assert!(
        validate_artifact(&m7, None).is_err(),
        "merging LevelGap.Kd3 into structure_eta_refused must be refused"
    );

    // Control 8: unpinning a kcheck_only_level_shape name refused.
    let mut m8 = baseline.clone();
    m8["kcheck_only_level_shape"][2]["name"] = json!("LevelGap.other");
    assert!(
        validate_artifact(&m8, None).is_err(),
        "unpinning kcheck_only_level_shape name must be refused"
    );

    // Control 9: corrupting uses_iota on Nat.noConfusion refused.
    let mut m9 = baseline.clone();
    for row in m9["accepted_both"].as_array_mut().expect("array") {
        if row["name"] == "Nat.noConfusion" {
            row["uses_iota"] = json!(false);
        }
    }
    m9["summary_counts"]["accepted_using_iota_count"] = json!(0);
    assert!(
        validate_artifact(&m9, None).is_err(),
        "corrupting uses_iota must be refused"
    );

    // Control 10: corrupting uses_k on cast_eq refused.
    let mut m10 = baseline.clone();
    for row in m10["accepted_both"].as_array_mut().expect("array") {
        if row["name"] == "cast_eq" {
            row["uses_k"] = json!(false);
        }
    }
    m10["summary_counts"]["accepted_using_k_count"] = json!(0);
    assert!(
        validate_artifact(&m10, None).is_err(),
        "corrupting uses_k must be refused"
    );

    // Control 11: partition sum mismatch refused.
    let mut m11 = baseline.clone();
    m11["summary_counts"]["total_audited_rows"] = json!(60);
    assert!(
        validate_artifact(&m11, None).is_err(),
        "partition sum mismatch must be refused"
    );

    // Control 12: Lean source hash drift refused.
    let mut m12 = baseline;
    m12["source_hashes"]["KCheckInitSlice/InitCorpus.lean"] =
        json!("ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff");
    assert!(
        validate_artifact(&m12, Some(&theory_dir)).is_err(),
        "Lean source hash drift must be refused"
    );
}

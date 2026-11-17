// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Plan unit M6 (`docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md`):
//! Rust verification and fail-closed consumer gate for the tracked universe-level
//! bound `N` (`data/level_bound_n.json`), paired with `theories/kcheck_m5_m6`.
//!
//! Evaluates C2's normal-form level report `Report = ⟨base, [(param_idx, offset), …]⟩`
//! using the exact `KCheckSpec.Report.eval (KCheckSpec.pad values)` semantics:
//!
//!   `eval(report, values) = max([report.base] + [pad(values, i) + k for (i, k) in report.offsets])`
//!
//! and refuses any Certified/consumer theorem receipt or pinned `Init` declaration
//! whose instantiated bound exceeds `TRACKED_BOUND_N = 5` (or has non-theorem kind,
//! universe-argument arity mismatch, or forged `instantiated_bound`).
//!
//! Standing limits:
//! 1. Soundness is per explicit finite universe bound `N` (`tracked_bound_n = 5`).
//! 2. No generation proves more consistency than its base theory (`Ax0`).
//! 3. By design `KCheck.checker` is to become the proved checker once all six Plan
//!    §2.1 conditions hold in fact; this gate flips no authority, and the
//!    independent re-checker quorum stays.

use std::path::Path;
use std::process::Command;

use serde_json::{json, Value};
use sha2::{Digest, Sha256};

const SCHEMA: &str = "clean.level_bound_n/v1";
const TRACKED_BOUND_N: u64 = 5;

const LEAN_INIT_CENSUS_SCRIPT: &str = r#"import Lean
open Lean

structure Rep where
  base : Nat
  offs : Array Nat
  deriving Inhabited

def repZero (k : Nat) : Rep := { base := 0, offs := Array.replicate k 0 }

def repMax (k : Nat) (a b : Rep) : Rep :=
  Id.run do
    let mut offs := Array.mkEmpty k
    for i in [:k] do
      offs := offs.push (Nat.max (a.offs.getD i 0) (b.offs.getD i 0))
    return { base := Nat.max a.base b.base, offs }

def repShift (d : Nat) (r : Rep) : Rep :=
  let offs := r.offs.map (fun o => if o == 0 then 0 else o + d)
  { base := r.base + d, offs }

def paramIdx? (ps : List Name) (nm : Name) : Option Nat :=
  let rec go : List Name → Nat → Option Nat
    | [], _ => none
    | p :: rest, i => if p == nm then some i else go rest (i + 1)
  go ps 0

partial def ofLevel (ps : List Name) (k : Nat) : Level → Rep
  | .zero => repZero k
  | .succ l => repShift 1 (ofLevel ps k l)
  | .max l1 l2 => repMax k (ofLevel ps k l1) (ofLevel ps k l2)
  | .imax l1 l2 => repMax k (ofLevel ps k l1) (ofLevel ps k l2)
  | .param nm =>
      match paramIdx? ps nm with
      | some idx =>
          let offs := (Array.replicate k 0).set! idx 1
          { base := 0, offs }
      | none => repZero k
  | .mvar _ => repZero k

def repSubst (ps : List Name) (k : Nat) (callee : Rep) (us : List Level) : Rep :=
  Id.run do
    let uReps := us.toArray.map (ofLevel ps k)
    let mut acc : Rep := { base := callee.base, offs := Array.replicate k 0 }
    for i in [:callee.offs.size] do
      let off := callee.offs[i]!
      if off > 0 then
        let arg := if h : i < uReps.size then uReps[i] else repZero k
        let shifted : Rep :=
          if off == 1 then
            let offs := arg.offs.map (fun o => if o == 0 then 0 else o)
            { base := Nat.max 1 arg.base, offs }
          else
            repShift (off - 1) {
              base := Nat.max 1 arg.base,
              offs := arg.offs
            }
        acc := repMax k acc shifted
    return acc

def evalAtZero (r : Rep) : Nat :=
  r.offs.foldl (fun acc o => Nat.max acc o) r.base

def kindName : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theoremDecl"
  | .opaqueInfo _ => "opaqueDecl"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

partial def exprRep (env : Environment) (ps : List Name) (k : Nat)
    (memo : Std.HashMap Name Rep) (seenExpr : Std.HashMap Expr Rep) (e : Expr) :
    Rep × Std.HashMap Name Rep × Std.HashMap Expr Rep :=
  if let some r := seenExpr.get? e then
    (r, memo, seenExpr)
  else
    match e with
    | .bvar _ | .fvar _ | .mvar _ | .lit _ =>
        let r := repZero k
        (r, memo, seenExpr.insert e r)
    | .sort u =>
        let r := repShift 1 (ofLevel ps k u)
        (r, memo, seenExpr.insert e r)
    | .const nm us =>
        let (cr, memo) := constRep env memo nm
        let r := repSubst ps k cr us
        (r, memo, seenExpr.insert e r)
    | .app f a =>
        let (rf, memo, seenExpr) := exprRep env ps k memo seenExpr f
        let (ra, memo, seenExpr) := exprRep env ps k memo seenExpr a
        let r := repMax k rf ra
        (r, memo, seenExpr.insert e r)
    | .lam _ d b _ | .forallE _ d b _ =>
        let (rd, memo, seenExpr) := exprRep env ps k memo seenExpr d
        let (rb, memo, seenExpr) := exprRep env ps k memo seenExpr b
        let r := repMax k rd rb
        (r, memo, seenExpr.insert e r)
    | .letE _ t v b _ =>
        let (rt, memo, seenExpr) := exprRep env ps k memo seenExpr t
        let (rv, memo, seenExpr) := exprRep env ps k memo seenExpr v
        let (rb, memo, seenExpr) := exprRep env ps k memo seenExpr b
        let r := repMax k (repMax k rt rv) rb
        (r, memo, seenExpr.insert e r)
    | .mdata _ b | .proj _ _ b =>
        let (rb, memo, seenExpr) := exprRep env ps k memo seenExpr b
        (rb, memo, seenExpr.insert e rb)
where
  constRep (env : Environment) (memo : Std.HashMap Name Rep) (nm : Name) :
      Rep × Std.HashMap Name Rep :=
    if let some r := memo.get? nm then
      (r, memo)
    else
      match env.find? nm with
      | none =>
          let r := repZero 0
          (r, memo.insert nm r)
      | some ci =>
          let ps := ci.levelParams
          let k := ps.length
          let memo := memo.insert nm (repZero k)
          let (rt, memo, seenExpr) := exprRep env ps k memo {} ci.type
          let (r, memo) :=
            match ci.value? with
            | some v =>
                let (rv, memo, _) := exprRep env ps k memo seenExpr v
                (repMax k rt rv, memo)
            | none => (rt, memo)
          (r, memo.insert nm r)

run_cmd do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Init }] {}
  let mut memo : Std.HashMap Name Rep := {}
  let mut total := 0
  let mut maxZero := 0
  let mut maxBase := 0
  let mut maxParams := 0
  let mut maxOff := 0
  let mut hist : Array Nat := Array.replicate 16 0
  let mut highRows : Array Json := #[]
  for idx in [:env.header.moduleNames.size] do
    let modName := env.header.moduleNames[idx]!
    let modData := env.header.moduleData[idx]!
    for ci in modData.constants do
      total := total + 1
      let (r, memo') := exprRep.constRep env memo ci.name
      memo := memo'
      let ez := evalAtZero r
      if ez > maxZero then maxZero := ez
      if r.base > maxBase then maxBase := r.base
      if ci.levelParams.length > maxParams then maxParams := ci.levelParams.length
      for o in r.offs do
        if o > maxOff then maxOff := o
      if ez < hist.size then
        hist := hist.set! ez (hist[ez]! + 1)
      let mut offsJson : Array Json := #[]
      for pIdx in [:r.offs.size] do
        let offVal := r.offs[pIdx]!
        if offVal > 0 then
          offsJson := offsJson.push (Json.arr #[toJson pIdx, toJson offVal])
      let row := Json.mkObj [
        ("name", toJson ci.name.toString),
        ("module", toJson modName.toString),
        ("kind", toJson (kindName ci)),
        ("num_params", toJson ci.levelParams.length),
        ("report", Json.mkObj [
          ("base", toJson r.base),
          ("offsets", Json.arr offsJson)
        ]),
        ("eval_at_zero", toJson ez)
      ]
      IO.println s!"ROW:{row.compress}"
      if ez >= 5 then
        highRows := highRows.push row
  let mut histPairs : List (String × Json) := []
  for idx in [:hist.size] do
    let c := hist[idx]!
    if c > 0 then
      histPairs := histPairs ++ [(toString idx, toJson c)]
  let out := Json.mkObj [
    ("module_count", toJson env.header.moduleNames.size),
    ("constant_count", toJson total),
    ("max_eval_at_zero", toJson maxZero),
    ("max_base", toJson maxBase),
    ("max_params", toJson maxParams),
    ("max_offset", toJson maxOff),
    ("eval_at_zero_histogram", Json.mkObj histPairs),
    ("boundary_declarations", Json.arr highRows)
  ]
  IO.println s!"SUMMARY:{out.compress}"
"#;

fn pad_value(values: &[u64], idx: usize) -> u64 {
    values.get(idx).copied().unwrap_or(0)
}

fn validate_report(report: &Value, context: &str) -> Result<(u64, Vec<(usize, u64)>), String> {
    let obj = report
        .as_object()
        .ok_or_else(|| format!("{context}: report must be an object"))?;
    if obj.len() != 2 || !obj.contains_key("base") || !obj.contains_key("offsets") {
        return Err(format!(
            "{context}: report must have exact keys {{'base', 'offsets'}}"
        ));
    }
    let base = obj["base"]
        .as_u64()
        .ok_or_else(|| format!("{context}: report.base must be a non-negative integer"))?;
    let raw_offsets = obj["offsets"]
        .as_array()
        .ok_or_else(|| format!("{context}: report.offsets must be an array"))?;
    let mut offsets = Vec::with_capacity(raw_offsets.len());
    for pair in raw_offsets {
        let arr = pair
            .as_array()
            .ok_or_else(|| format!("{context}: offset entry must be [param_idx, offset]"))?;
        if arr.len() != 2 {
            return Err(format!(
                "{context}: offset entry must have length 2, got {}",
                arr.len()
            ));
        }
        let idx_u64 = arr[0]
            .as_u64()
            .ok_or_else(|| format!("{context}: param_idx must be a non-negative integer"))?;
        let off = arr[1]
            .as_u64()
            .ok_or_else(|| format!("{context}: offset must be a non-negative integer"))?;
        let idx = usize::try_from(idx_u64)
            .map_err(|_| format!("{context}: param_idx {idx_u64} overflows usize"))?;
        offsets.push((idx, off));
    }
    Ok((base, offsets))
}

fn eval_report(report: &Value, values: &Value, context: &str) -> Result<u64, String> {
    let raw_vals = values
        .as_array()
        .ok_or_else(|| format!("{context}: values must be a list of non-negative integers"))?;
    let mut parsed_vals = Vec::with_capacity(raw_vals.len());
    for v in raw_vals {
        let n = v
            .as_u64()
            .ok_or_else(|| format!("{context}: value entry must be a non-negative integer"))?;
        parsed_vals.push(n);
    }
    let (base, offsets) = validate_report(report, context)?;
    let mut acc = base;
    for (idx, off) in offsets {
        let shifted = pad_value(&parsed_vals, idx)
            .checked_add(off)
            .ok_or_else(|| format!("{context}: level bound overflow"))?;
        acc = acc.max(shifted);
    }
    Ok(acc)
}

fn check_receipt_row(row: &Value, bound_n: u64, context: &str) -> Result<u64, String> {
    let obj = row
        .as_object()
        .ok_or_else(|| format!("{context}: receipt row must be an object"))?;
    let name = obj
        .get("name")
        .and_then(Value::as_str)
        .filter(|s| !s.is_empty())
        .ok_or_else(|| format!("{context}: receipt row missing non-empty 'name'"))?;
    let kind = obj
        .get("kind")
        .and_then(Value::as_str)
        .ok_or_else(|| format!("{context} ({name}): missing 'kind'"))?;
    if kind != "theoremDecl" {
        return Err(format!(
            "{context} ({name}): receipt kind must be 'theoremDecl', got {kind:?}"
        ));
    }
    let values = obj
        .get("values")
        .ok_or_else(|| format!("{context} ({name}): missing 'values'"))?;
    let val_arr = values
        .as_array()
        .ok_or_else(|| format!("{context} ({name}): 'values' must be a list"))?;
    if let Some(expected_val) = obj.get("expected_params") {
        let expected = expected_val
            .as_u64()
            .ok_or_else(|| format!("{context} ({name}): invalid expected_params"))?;
        if val_arr.len() as u64 != expected {
            return Err(format!(
                "{context} ({name}): universe arity mismatch: len(values)={} != expected_params={expected}",
                val_arr.len()
            ));
        }
    }
    let bound = obj
        .get("bound")
        .ok_or_else(|| format!("{context} ({name}): missing 'bound'"))?;
    let ev = eval_report(bound, values, &format!("{context} ({name})"))?;
    if let Some(inst_val) = obj.get("instantiated_bound") {
        let inst = inst_val
            .as_u64()
            .ok_or_else(|| format!("{context} ({name}): invalid instantiated_bound"))?;
        if inst != ev {
            return Err(format!(
                "{context} ({name}): recorded instantiated_bound={inst} != recomputed {ev}"
            ));
        }
    }
    if ev > bound_n {
        return Err(format!(
            "{context} ({name}): instantiated level bound {ev} exceeds tracked bound N={bound_n}"
        ));
    }
    Ok(ev)
}

fn is_64_lower_hex(s: &str) -> bool {
    s.len() == 64
        && s.bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}

fn validate_artifact(data: &Value) -> Result<(), String> {
    let obj = data
        .as_object()
        .ok_or_else(|| "artifact root must be a JSON object".to_string())?;
    let schema = obj.get("schema").and_then(Value::as_str);
    if schema != Some(SCHEMA) {
        return Err(format!(
            "unexpected schema {schema:?} (expected {SCHEMA:?})"
        ));
    }
    let bound_n = obj
        .get("tracked_bound_n")
        .and_then(Value::as_u64)
        .ok_or_else(|| "missing integer tracked_bound_n".to_string())?;
    if bound_n != TRACKED_BOUND_N {
        return Err(format!(
            "tracked_bound_n must equal {TRACKED_BOUND_N}, got {bound_n}"
        ));
    }

    let init_c = obj
        .get("pinned_init_census")
        .and_then(Value::as_object)
        .ok_or_else(|| "missing pinned_init_census object".to_string())?;
    let mod_count = init_c
        .get("module_count")
        .and_then(Value::as_u64)
        .filter(|&n| n > 0)
        .ok_or_else(|| "invalid module_count".to_string())?;
    let _ = mod_count;
    let const_count = init_c
        .get("constant_count")
        .and_then(Value::as_u64)
        .filter(|&n| n > 0)
        .ok_or_else(|| "invalid constant_count".to_string())?;
    let max_ez = init_c
        .get("max_eval_at_zero")
        .and_then(Value::as_u64)
        .ok_or_else(|| "invalid max_eval_at_zero".to_string())?;
    if max_ez > bound_n {
        return Err(format!(
            "pinned Init max_eval_at_zero={max_ez} exceeds tracked_bound_n={bound_n}"
        ));
    }

    let hist = init_c
        .get("eval_at_zero_histogram")
        .and_then(Value::as_object)
        .filter(|h| !h.is_empty())
        .ok_or_else(|| "missing eval_at_zero_histogram".to_string())?;
    let mut hist_sum = 0_u64;
    let mut hist_max_bucket = 0_u64;
    let mut expected_ge_5 = 0_u64;
    for (k, v) in hist {
        let idx: u64 = k
            .parse()
            .map_err(|_| format!("invalid histogram bucket key {k:?}"))?;
        let count = v
            .as_u64()
            .filter(|&c| c > 0)
            .ok_or_else(|| format!("invalid histogram count for bucket {k:?}"))?;
        if idx > bound_n {
            return Err(format!(
                "Init histogram bucket {idx} exceeds tracked_bound_n={bound_n}"
            ));
        }
        hist_sum += count;
        hist_max_bucket = hist_max_bucket.max(idx);
        if idx >= 5 {
            expected_ge_5 += count;
        }
    }
    if hist_sum != const_count {
        return Err(format!(
            "Init histogram sum {hist_sum} != constant_count {const_count}"
        ));
    }
    if hist_max_bucket != max_ez {
        return Err(format!(
            "Init histogram max bucket {hist_max_bucket} != max_eval_at_zero {max_ez}"
        ));
    }

    let digest = init_c
        .get("all_reports_sha256")
        .and_then(Value::as_str)
        .filter(|s| is_64_lower_hex(s))
        .ok_or_else(|| "missing or invalid 64-hex all_reports_sha256".to_string())?;
    let _ = digest;

    let high_rows = init_c
        .get("boundary_declarations")
        .and_then(Value::as_array)
        .ok_or_else(|| "boundary_declarations must be a list".to_string())?;
    if high_rows.len() as u64 != expected_ge_5 {
        return Err(format!(
            "boundary_declarations count {} != histogram >=5 total {expected_ge_5}",
            high_rows.len()
        ));
    }
    let empty_vals = json!([]);
    for row in high_rows {
        let row_obj = row
            .as_object()
            .ok_or_else(|| "invalid Init declaration row".to_string())?;
        let nm = row_obj
            .get("name")
            .and_then(Value::as_str)
            .unwrap_or("<unnamed>");
        let rep = row_obj
            .get("report")
            .ok_or_else(|| format!("Init row {nm} missing report"))?;
        let ez = eval_report(rep, &empty_vals, &format!("Init row {nm}"))?;
        let recorded = row_obj
            .get("eval_at_zero")
            .and_then(Value::as_u64)
            .ok_or_else(|| format!("Init row {nm} missing eval_at_zero"))?;
        if ez != recorded {
            return Err(format!(
                "Init row {nm}: eval_at_zero={recorded} != recomputed {ez}"
            ));
        }
        if ez > bound_n {
            return Err(format!(
                "Init row {nm}: eval_at_zero={ez} exceeds tracked_bound_n={bound_n}"
            ));
        }
    }

    let cert_c = obj
        .get("certified_rows_census")
        .and_then(Value::as_object)
        .ok_or_else(|| "missing certified_rows_census object".to_string())?;
    let cert_rows = cert_c
        .get("certified_rows")
        .and_then(Value::as_array)
        .ok_or_else(|| "certified_rows must be a list".to_string())?;
    let active_count = cert_c
        .get("active_certified_row_count")
        .and_then(Value::as_u64)
        .ok_or_else(|| "missing active_certified_row_count".to_string())?;
    if active_count != cert_rows.len() as u64 {
        return Err("active_certified_row_count does not match len(certified_rows)".to_string());
    }
    for row in cert_rows {
        check_receipt_row(row, bound_n, "certified_rows")?;
    }

    let ground_rows = obj
        .get("kcheck_ground_receipts")
        .and_then(Value::as_array)
        .filter(|r| !r.is_empty())
        .ok_or_else(|| "kcheck_ground_receipts must be a non-empty list".to_string())?;
    for row in ground_rows {
        check_receipt_row(row, bound_n, "kcheck_ground_receipts")?;
    }
    Ok(())
}

fn verify_pinned_lean_init_census(root: &Path, expected_init: &Value) {
    let lean = clean_olean::pinned_lean_binary().expect("pinned Lean binary");
    let githash_out = Command::new(&lean)
        .arg("--githash")
        .current_dir(root)
        .output()
        .expect("lean --githash");
    assert!(githash_out.status.success(), "lean --githash failed");
    let githash = String::from_utf8_lossy(&githash_out.stdout)
        .trim()
        .to_string();
    assert_eq!(
        Some(githash.as_str()),
        expected_init.get("lean_githash").and_then(Value::as_str),
        "pinned Lean githash mismatch"
    );

    let tmp_dir = tempfile::tempdir().expect("tempdir for Lean Init census");
    let script_path = tmp_dir.path().join("InitBoundCensus.lean");
    std::fs::write(&script_path, LEAN_INIT_CENSUS_SCRIPT).expect("write Lean Init census script");
    let out = Command::new(&lean)
        .arg(&script_path)
        .current_dir(root)
        .env_remove("LEAN_PATH")
        .env_remove("LEAN_SRC_PATH")
        .output()
        .expect("run Lean Init census");
    assert!(
        out.status.success(),
        "pinned Lean Init census failed:\n{}",
        String::from_utf8_lossy(&out.stdout)
    );
    let stdout = String::from_utf8_lossy(&out.stdout);
    let mut summary_lines = Vec::new();
    let mut row_lines = Vec::new();
    for raw in stdout.lines() {
        let ln = raw.trim();
        if let Some(rest) = ln.strip_prefix("SUMMARY:") {
            summary_lines.push(rest.to_string());
        } else if let Some(rest) = ln.strip_prefix("ROW:") {
            row_lines.push(rest.to_string());
        }
    }
    assert_eq!(summary_lines.len(), 1, "expected 1 SUMMARY line");
    let measured: Value = serde_json::from_str(&summary_lines[0]).expect("parse SUMMARY JSON");
    assert_eq!(
        row_lines.len() as u64,
        measured["constant_count"].as_u64().expect("constant_count"),
        "ROW count must equal constant_count"
    );
    row_lines.sort();
    let digest_hex: String = Sha256::digest(format!("{}\n", row_lines.join("\n")).as_bytes())
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect();
    assert_eq!(
        Some(digest_hex.as_str()),
        expected_init
            .get("all_reports_sha256")
            .and_then(Value::as_str),
        "recomputed Init all_reports_sha256 mismatch"
    );
}

#[test]
fn level_bound_n_artifact_and_ten_acceptance_refusal_controls() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let pin = std::fs::read_to_string(root.join("lean-toolchain"))
        .expect("read lean-toolchain")
        .trim()
        .to_string();
    let artifact_raw = std::fs::read_to_string(root.join("data/level_bound_n.json"))
        .expect("read data/level_bound_n.json");
    let artifact: Value =
        serde_json::from_str(&artifact_raw).expect("parse data/level_bound_n.json");

    validate_artifact(&artifact).expect("pinned data/level_bound_n.json must pass M6 gate");
    assert_eq!(
        artifact["pinned_init_census"]["lean_toolchain"].as_str(),
        Some(pin.as_str()),
        "data/level_bound_n.json lean_toolchain must match root lean-toolchain"
    );

    if std::env::var_os("VERIFY_LEVEL_BOUND_N_LEAN").is_some() {
        verify_pinned_lean_init_census(&root, &artifact["pinned_init_census"]);
    }

    // 1. Valid ground receipt at boundary N = 5 accepted.
    assert_eq!(
        check_receipt_row(
            &json!({
                "name": "ok5",
                "kind": "theoremDecl",
                "expected_params": 0,
                "bound": {"base": 5, "offsets": []},
                "values": [],
                "instantiated_bound": 5,
            }),
            TRACKED_BOUND_N,
            "control-1",
        ),
        Ok(5)
    );

    // 2. Valid polymorphic receipt [4] with offset (0, 1) -> 5 <= 5 accepted.
    assert_eq!(
        check_receipt_row(
            &json!({
                "name": "okPoly5",
                "kind": "theoremDecl",
                "expected_params": 1,
                "bound": {"base": 1, "offsets": [[0, 1]]},
                "values": [4],
                "instantiated_bound": 5,
            }),
            TRACKED_BOUND_N,
            "control-2",
        ),
        Ok(5)
    );

    // 3. Ground receipt with base = 6 > 5 refused.
    assert!(
        check_receipt_row(
            &json!({
                "name": "bad6",
                "kind": "theoremDecl",
                "expected_params": 0,
                "bound": {"base": 6, "offsets": []},
                "values": [],
            }),
            TRACKED_BOUND_N,
            "control-3",
        )
        .is_err(),
        "ground receipt above N=5 must be refused"
    );

    // 4. Polymorphic receipt [5] with offset (0, 1) -> 6 > 5 refused.
    assert!(
        check_receipt_row(
            &json!({
                "name": "badPoly6",
                "kind": "theoremDecl",
                "expected_params": 1,
                "bound": {"base": 1, "offsets": [[0, 1]]},
                "values": [5],
            }),
            TRACKED_BOUND_N,
            "control-4",
        )
        .is_err(),
        "polymorphic receipt evaluating above N=5 must be refused"
    );

    // 5. Non-theorem receipt kind ('definition') refused.
    assert!(
        check_receipt_row(
            &json!({
                "name": "idNat",
                "kind": "definition",
                "expected_params": 0,
                "bound": {"base": 2, "offsets": []},
                "values": [],
            }),
            TRACKED_BOUND_N,
            "control-5",
        )
        .is_err(),
        "non-theorem receipt kind must be refused"
    );

    // 6. Universe parameter arity mismatch refused.
    assert!(
        check_receipt_row(
            &json!({
                "name": "badArity",
                "kind": "theoremDecl",
                "expected_params": 1,
                "bound": {"base": 1, "offsets": [[0, 1]]},
                "values": [],
            }),
            TRACKED_BOUND_N,
            "control-6",
        )
        .is_err(),
        "universe parameter arity mismatch must be refused"
    );

    // 7. Forged instantiated_bound mismatch refused.
    assert!(
        check_receipt_row(
            &json!({
                "name": "forgedInst",
                "kind": "theoremDecl",
                "expected_params": 0,
                "bound": {"base": 4, "offsets": []},
                "values": [],
                "instantiated_bound": 2,
            }),
            TRACKED_BOUND_N,
            "control-7",
        )
        .is_err(),
        "forged instantiated_bound must be refused"
    );

    // 8. Negative offset / malformed report refused.
    assert!(
        eval_report(
            &json!({"base": 1, "offsets": [[0, -1]]}),
            &json!([2]),
            "control-8",
        )
        .is_err(),
        "negative report offset must be refused"
    );

    // 9-10. Synthetic artifact mutations refused.
    let synthetic = json!({
        "schema": SCHEMA,
        "plan_unit": "M6",
        "tracked_bound_n": TRACKED_BOUND_N,
        "pinned_init_census": {
            "module_count": 1,
            "constant_count": 2,
            "max_eval_at_zero": 5,
            "all_reports_sha256": "0000000000000000000000000000000000000000000000000000000000000000",
            "eval_at_zero_histogram": {"2": 1, "5": 1},
            "boundary_declarations": [
                {
                    "name": "Synthetic.five",
                    "module": "Init.Core",
                    "kind": "theoremDecl",
                    "num_params": 0,
                    "report": {"base": 5, "offsets": []},
                    "eval_at_zero": 5,
                }
            ],
        },
        "certified_rows_census": {
            "active_certified_row_count": 0,
            "certified_rows": [],
        },
        "kcheck_ground_receipts": [
            {
                "name": "eqz",
                "kind": "theoremDecl",
                "expected_params": 0,
                "bound": {"base": 2, "offsets": []},
                "values": [],
                "instantiated_bound": 2,
            }
        ],
    });
    validate_artifact(&synthetic).expect("synthetic baseline must pass");

    let mut bad_init = synthetic.clone();
    bad_init["pinned_init_census"]["max_eval_at_zero"] = json!(6);
    assert!(
        validate_artifact(&bad_init).is_err(),
        "Init max_eval_at_zero > N must be refused"
    );

    let mut bad_cert = synthetic;
    bad_cert["certified_rows_census"]["active_certified_row_count"] = json!(1);
    bad_cert["certified_rows_census"]["certified_rows"] = json!([
        {
            "name": "Cert.tooHigh",
            "kind": "theoremDecl",
            "expected_params": 0,
            "bound": {"base": 6, "offsets": []},
            "values": [],
        }
    ]);
    assert!(
        validate_artifact(&bad_cert).is_err(),
        "Certified row exceeding N=5 must be refused"
    );
}

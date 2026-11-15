// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A level-only forgery over the AsWritten class: its type gains a successor.

use super::*;

const LEVEL_CONTROL: &str = "q1_level_control";

fn level_export(forged: bool) -> Vec<u8> {
    let meta = pinned_meta();
    // L = max u (imax (v+1) u) is not a constructor fixed point (R125).
    // Honest: Sort L : Sort (succ L). Forged: Sort L : Sort (succ (succ L)).
    // Only one `succ` record's child changes; declarations and expressions
    // are identical. Both streams are well-formed, scoped, and axiom-free.
    let records = [
        serde_json::json!({"meta": {"exporter": {"name": "q1-level-control", "version": "1"},
            "format": {"version": "3.1.0"}, "lean": {"version": meta.lean_version,
            "githash": meta.lean_githash}}}),
        serde_json::json!({"in": 1, "str": {"pre": 0, "str": LEVEL_CONTROL}}),
        serde_json::json!({"in": 2, "str": {"pre": 0, "str": "u"}}),
        serde_json::json!({"in": 3, "str": {"pre": 0, "str": "v"}}),
        serde_json::json!({"il": 1, "param": 2}),
        serde_json::json!({"il": 2, "param": 3}),
        serde_json::json!({"il": 3, "succ": 2}),
        serde_json::json!({"il": 4, "imax": [3, 1]}),
        serde_json::json!({"il": 5, "max": [1, 4]}),
        serde_json::json!({"il": 6, "succ": 5}),
        serde_json::json!({"il": 7, "succ": if forged { 6 } else { 5 }}),
        serde_json::json!({"ie": 0, "sort": 5}),
        serde_json::json!({"ie": 1, "sort": 7}),
        serde_json::json!({"def": {"name": 1, "levelParams": [2, 3], "type": 1,
            "value": 0, "hints": "abbrev", "safety": "safe", "all": [1]}}),
    ];
    let mut bytes = Vec::new();
    for record in records {
        bytes.extend_from_slice(record.to_string().as_bytes());
        bytes.push(b'\n');
    }
    bytes
}

#[test]
fn test_export_reference_level_successor_forgery_is_refused_by_pinned_lean_and_entry() {
    let _heavy = HEAVY.lock().unwrap_or_else(PoisonError::into_inner);
    let dir = tempfile::tempdir().expect("control directory");
    for forged in [false, true] {
        let bytes = level_export(forged);
        let entry = reference(bytes.clone());
        assert!(entry.reader_error.is_none(), "{:?}", entry.reader_error);
        assert!(entry.unpermitted_axioms.is_empty());
        assert!(entry.axioms.is_empty());
        assert_eq!(entry.declarations, 1);
        assert_eq!(entry.accepted, !forged, "{:?}", entry.refusals);
        assert_eq!(entry.admitted, usize::from(!forged));
        if forged {
            assert!(
                entry
                    .refusals
                    .iter()
                    .any(|r| r.starts_with(&format!("{LEVEL_CONTROL}: "))
                        && r.contains("Type mismatch")),
                "{:?}",
                entry.refusals
            );
            assert!(entry
                .refusals
                .iter()
                .all(|r| r.starts_with(&format!("{LEVEL_CONTROL}: "))));
        }
        let path = dir.path().join(if forged {
            "forged.ndjson"
        } else {
            "honest.ndjson"
        });
        std::fs::write(&path, bytes).expect("control bytes");
        for (reader, out) in [
            ("Replay.lean", lean_replay(&path)),
            ("lean4export", lean_replay_upstream(&path)),
        ] {
            let stderr = String::from_utf8_lossy(&out.stderr);
            assert_eq!(
                out.status.code(),
                Some(i32::from(forged)),
                "{reader}: {stderr}"
            );
            if forged {
                assert!(
                    stderr.contains("REJECTED (kernel)")
                        && stderr.contains(&format!(
                            "declaration type mismatch, '{LEVEL_CONTROL}' has type"
                        )),
                    "{reader}: {stderr}"
                );
            }
            eprintln!(
                "Q1 level control forged={forged} {reader}: exit {}",
                out.status
            );
        }
    }
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Report data model shared by the text and JSON output paths.

/// Result of a single `mathverse_try` invocation.
#[derive(Debug, Default)]
pub(super) struct Report {
    pub status: Status,
    pub error: Option<String>,
    pub inferred_type: Option<String>,
    pub axiom_closure: Vec<String>,
    pub trust_markers: Vec<String>,
}

#[derive(Debug, Default, PartialEq, Eq)]
pub(super) enum Status {
    Pass,
    #[default]
    Fail,
}

impl Report {
    #[must_use]
    pub fn classification(&self) -> &'static str {
        if self.status != Status::Pass {
            return "FAIL";
        }
        if !self.trust_markers.is_empty() {
            "TRUST_MARKER_REACHED"
        } else if self.axiom_closure.is_empty() {
            "CONSTRUCTIVE"
        } else {
            "AXIOM_DEPENDENT"
        }
    }

    pub fn to_text(&self) -> String {
        let mut out = String::new();
        match self.status {
            Status::Pass => out.push_str("PASS\n"),
            Status::Fail => {
                out.push_str("FAIL: ");
                out.push_str(self.error.as_deref().unwrap_or("(no reason)"));
                out.push('\n');
            }
        }
        if let Some(ty) = &self.inferred_type {
            out.push_str("inferred_type: ");
            out.push_str(ty);
            out.push('\n');
        }
        if self.status == Status::Pass {
            out.push_str("axiom_closure (non-foundational): [");
            out.push_str(&self.axiom_closure.join(", "));
            out.push_str("]\n");
            if !self.trust_markers.is_empty() {
                out.push_str("trust_markers: [");
                out.push_str(&self.trust_markers.join(", "));
                out.push_str("]\n");
            }
            out.push_str("classification: ");
            out.push_str(self.classification());
            out.push('\n');
        }
        out
    }

    pub fn to_json(&self) -> String {
        // Hand-rolled to avoid pulling the full serde ceremony for a
        // three-field report. The keys are stable; downstream tooling
        // can match on them.
        let status = match self.status {
            Status::Pass => "PASS",
            Status::Fail => "FAIL",
        };
        let error = quote_or_null(self.error.as_deref());
        let inferred = quote_or_null(self.inferred_type.as_deref());
        let axioms = json_array(&self.axiom_closure);
        let trust = json_array(&self.trust_markers);
        format!(
            "{{\"status\":\"{status}\",\"error\":{error},\"inferred_type\":{inferred},\
              \"axiom_closure\":{axioms},\"trust_markers\":{trust},\
              \"classification\":\"{}\"}}",
            self.classification()
        )
    }
}

fn quote_or_null(s: Option<&str>) -> String {
    s.map(|v| format!("\"{}\"", escape_json(v)))
        .unwrap_or_else(|| "null".to_string())
}

fn json_array(items: &[String]) -> String {
    let joined = items
        .iter()
        .map(|s| format!("\"{}\"", escape_json(s)))
        .collect::<Vec<_>>()
        .join(",");
    format!("[{joined}]")
}

fn escape_json(s: &str) -> String {
    s.replace('\\', "\\\\").replace('"', "\\\"")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_json_output_shape_axiom_dependent() {
        let rep = Report {
            status: Status::Pass,
            axiom_closure: vec!["X".to_string()],
            ..Default::default()
        };
        let j = rep.to_json();
        assert!(j.contains("\"status\":\"PASS\""));
        assert!(j.contains("\"axiom_closure\":[\"X\"]"));
        assert!(j.contains("\"classification\":\"AXIOM_DEPENDENT\""));
    }

    #[test]
    fn test_json_output_shape_constructive() {
        let rep = Report {
            status: Status::Pass,
            ..Default::default()
        };
        let j = rep.to_json();
        assert!(j.contains("\"classification\":\"CONSTRUCTIVE\""));
        assert!(j.contains("\"axiom_closure\":[]"));
    }

    #[test]
    fn test_json_output_shape_trust_marker() {
        let rep = Report {
            status: Status::Pass,
            trust_markers: vec!["sorryAx".to_string()],
            ..Default::default()
        };
        let j = rep.to_json();
        assert!(j.contains("\"classification\":\"TRUST_MARKER_REACHED\""));
    }

    #[test]
    fn test_text_output_fail_includes_reason() {
        let rep = Report {
            status: Status::Fail,
            error: Some("bad proof".to_string()),
            ..Default::default()
        };
        let t = rep.to_text();
        assert!(t.starts_with("FAIL: bad proof"));
    }

    #[test]
    fn test_escape_json_quotes_and_backslashes() {
        assert_eq!(escape_json(r#"a"b\c"#), r#"a\"b\\c"#);
    }
}

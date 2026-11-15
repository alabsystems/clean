// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The export's `meta` line, and which kernel rule set judges it.
//!
//! An export states the Lean that produced it (`meta.lean.version`). This
//! reader judges an export only under a kernel rule set a reviewed row of
//! [`REVIEWED_LEAN_VERSIONS`] maps that version to; any other version is
//! declined (exit 2), never judged under the nearest rule set.
//!
//! This is the NDJSON half of R38's selection rule. The `.olean` half is R81's
//! world table (`crates/clean-olean/lean_worlds.tsv`, `crate::world`), which
//! keys a world by header identity; an export carries no header, so it is
//! keyed by its stated version here. The two meet at the rule set: each rule
//! set names the R81 world whose kernel it is, and a rule set whose world is
//! not the R81 ORACLE judges nothing (the export is declined) until its rows
//! are reviewed again against the new oracle's kernel.

use super::error::NdjsonError;
use super::json::JsonValue;

/// A kernel rule set Clean can judge an export under.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum KernelRuleSet {
    /// Lean v4.30.0-rc2's kernel, Clean's oracle pin: `KernelTheory::Lean`.
    LeanV4_30Rc2,
}

impl KernelRuleSet {
    /// The R81 world (`lean_worlds.tsv`) whose kernel this rule set is.
    #[must_use]
    pub(crate) fn world(self) -> &'static str {
        match self {
            KernelRuleSet::LeanV4_30Rc2 => "v4.30.0-rc2",
        }
    }

    /// Whether this rule set's world is R81's oracle: the only world whose
    /// kernel `KernelTheory::Lean` models.
    fn is_oracle(self) -> bool {
        crate::world::lean_worlds()
            .iter()
            .any(|row| row.world == self.world() && row.state == crate::world::WorldState::Oracle)
    }
}

/// One reviewed row: an exporting Lean version and the rule set that judges
/// its exports, with the review that justifies the pairing.
#[derive(Debug, Clone, Copy)]
pub struct ReviewedLeanVersion {
    /// `meta.lean.version`, exactly as the export states it.
    pub version: &'static str,
    /// The rule set.
    pub rule_set: KernelRuleSet,
    /// Why judging this version's exports under that rule set cannot accept
    /// what its own kernel rejects.
    pub review: &'static str,
}

/// The reviewed table. Reviewed 2026-10-17 against `src/kernel` of the
/// upstream tags (decision R116 in `docs/DECISIONS.md`).
pub const REVIEWED_LEAN_VERSIONS: &[ReviewedLeanVersion] = &[
    ReviewedLeanVersion {
        version: "4.30.0-rc2",
        rule_set: KernelRuleSet::LeanV4_30Rc2,
        review: "the pin itself",
    },
    ReviewedLeanVersion {
        version: "4.30.0",
        rule_set: KernelRuleSet::LeanV4_30Rc2,
        review: "src/kernel is byte-identical to v4.30.0-rc2 (every blob sha equal)",
    },
    ReviewedLeanVersion {
        version: "4.29.1",
        rule_set: KernelRuleSet::LeanV4_30Rc2,
        review: "src/kernel v4.29.1 -> v4.30.0-rc2 changes declaration.h, environment.cpp, \
                 inductive.cpp/.h and type_checker.cpp, and each change narrows acceptance: \
                 theorems stop unfolding (has_value), structure eta is limited to \
                 non-recursive structures (is_non_rec_structure), and is_delta refuses a \
                 constant applied at the wrong number of levels; add_theorem only reorders \
                 two checks. Judging a 4.29.1 export under the v4.30.0-rc2 rules can reject \
                 what 4.29.1 accepts, never accept what it rejects",
    },
    ReviewedLeanVersion {
        version: "4.29.0",
        rule_set: KernelRuleSet::LeanV4_30Rc2,
        review: "src/kernel is byte-identical to v4.29.1 (every blob sha equal); see 4.29.1",
    },
];

/// The `meta` header an export opens with.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize)]
pub struct ExportMeta {
    /// `meta.exporter.name`.
    pub exporter_name: String,
    /// `meta.exporter.version`.
    pub exporter_version: String,
    /// `meta.lean.githash`.
    pub lean_githash: String,
    /// `meta.lean.version`.
    pub lean_version: String,
    /// `meta.format.version`.
    pub format_version: String,
    /// The rule set the reviewed table maps `lean_version` to.
    pub rule_set: KernelRuleSet,
}

fn object(value: JsonValue, what: &str) -> Result<Vec<(String, JsonValue)>, NdjsonError> {
    match value {
        JsonValue::Object(entries) => Ok(entries),
        other => Err(NdjsonError::MalformedMeta {
            reason: format!("{what} is {}, not an object", other.type_name()),
        }),
    }
}

/// The string fields `names` of the object `value`, which must have exactly
/// those fields.
fn strings<const N: usize>(
    value: JsonValue,
    what: &str,
    names: [&str; N],
) -> Result<[String; N], NdjsonError> {
    let entries = object(value, what)?;
    if entries.len() != N {
        return Err(NdjsonError::MalformedMeta {
            reason: format!("{what} must have exactly the fields {names:?}"),
        });
    }
    let mut out: [String; N] = std::array::from_fn(|_| String::new());
    for (slot, name) in out.iter_mut().zip(names) {
        match entries.iter().find(|(k, _)| k == name) {
            Some((_, JsonValue::String(s))) => slot.clone_from(s),
            _ => {
                return Err(NdjsonError::MalformedMeta {
                    reason: format!("{what}.{name} must be a string"),
                })
            }
        }
    }
    Ok(out)
}

/// Read the `meta` line and select the rule set, or refuse (malformed header,
/// exit 1) or decline (a format version other than 3.1, any patch, or a Lean
/// version with no reviewed row, exit 2).
pub(crate) fn read_meta(value: JsonValue) -> Result<ExportMeta, NdjsonError> {
    let mut top = object(value, "the first line")?;
    if !matches!(top.as_slice(), [(key, _)] if key == "meta") {
        return Err(NdjsonError::MalformedMeta {
            reason: "the first line must be an object with the one key `meta`".to_owned(),
        });
    }
    let meta = top.remove(0).1;
    let mut parts = object(meta, "meta")?;
    if parts.len() != 3 {
        return Err(NdjsonError::MalformedMeta {
            reason: "meta must have exactly the fields exporter, lean and format".to_owned(),
        });
    }
    let mut take = |name: &str| -> Result<JsonValue, NdjsonError> {
        let at = parts.iter().position(|(k, _)| k == name).ok_or_else(|| {
            NdjsonError::MalformedMeta {
                reason: format!("meta.{name} is missing"),
            }
        })?;
        Ok(parts.swap_remove(at).1)
    };
    let [exporter_name, exporter_version] =
        strings(take("exporter")?, "meta.exporter", ["name", "version"])?;
    let [lean_githash, lean_version] = strings(take("lean")?, "meta.lean", ["githash", "version"])?;
    let [format_version] = strings(take("format")?, "meta.format", ["version"])?;

    // The record shapes this reader reads are format 3.1.0's; another minor
    // version of format 3 may shape them otherwise, and is declined rather
    // than misread as malformed. A patch release does not change the format.
    let mut parts = format_version.split('.');
    if (parts.next(), parts.next()) != (Some("3"), Some("1")) {
        return Err(NdjsonError::FormatVersionUnsupported {
            version: format_version,
        });
    }
    let Some(row) = REVIEWED_LEAN_VERSIONS
        .iter()
        .find(|row| row.version == lean_version)
    else {
        return Err(NdjsonError::LeanVersionUnmapped {
            version: lean_version,
        });
    };
    if !row.rule_set.is_oracle() {
        return Err(NdjsonError::LeanVersionUnmapped {
            version: lean_version,
        });
    }
    Ok(ExportMeta {
        exporter_name,
        exporter_version,
        lean_githash,
        lean_version,
        format_version,
        rule_set: row.rule_set,
    })
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Pinned C++ source identity, function definitions and explicit raw line anchors.

mod coverage;

use super::{k3_export::sha256_bytes as sha256, k3_inputs, rule_families::RULE_INVENTORY};
use crate::EvidenceCheckError;
use clean_evidence::source_scan::cpp::{CppCaseArm, CppConstantUse, CppSource};
use serde::de::{self, MapAccess, Visitor};
use serde::{Deserialize, Deserializer, Serialize};
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt, fs,
    io::{self, Write},
    path::{Component, Path},
};

const LEAN_REPOSITORY: &str = "https://github.com/leanprover/lean4";
const PINNED_FILES: [&str; 6] = [
    "src/kernel/inductive.cpp",
    "src/kernel/inductive.h",
    "src/kernel/level.cpp",
    "src/kernel/quot.cpp",
    "src/kernel/quot.h",
    "src/kernel/type_checker.cpp",
];

#[derive(Deserialize)]
pub(super) struct Inventory {
    upstream: Upstream,
    rows: Vec<Row>,
}

#[derive(Deserialize)]
struct Upstream {
    #[serde(flatten)]
    identity: Identity,
    root: String,
    toolchain_file: String,
    files: FilePins,
}

/// The incumbent merges cross-file names in the inventory's wire order.
struct FilePins(Vec<(String, FilePin)>);

impl FilePins {
    fn paths(&self) -> impl Iterator<Item = &str> {
        self.0.iter().map(|(path, _)| path.as_str())
    }

    fn get(&self, file: &str) -> Option<&FilePin> {
        self.0
            .iter()
            .find_map(|(path, pin)| (path == file).then_some(pin))
    }
}

impl<'de> Deserialize<'de> for FilePins {
    fn deserialize<D: Deserializer<'de>>(input: D) -> Result<Self, D::Error> {
        struct PinsVisitor;

        impl<'de> Visitor<'de> for PinsVisitor {
            type Value = FilePins;

            fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str("a map with unique C++ file pin keys")
            }

            fn visit_map<A: MapAccess<'de>>(self, mut input: A) -> Result<FilePins, A::Error> {
                let mut pins = FilePins(Vec::new());
                let mut seen = BTreeSet::new();
                while let Some((path, pin)) = input.next_entry::<String, FilePin>()? {
                    if !seen.insert(path.clone()) {
                        return Err(de::Error::custom(format!(
                            "duplicate C++ file pin {path:?}"
                        )));
                    }
                    pins.0.push((path, pin));
                }
                Ok(pins)
            }
        }

        input.deserialize_map(PinsVisitor)
    }
}

#[derive(Deserialize, Serialize)]
struct Identity {
    repository: String,
    tag: String,
    commit: String,
}

#[derive(Deserialize, Eq, PartialEq)]
struct FilePin {
    bytes: usize,
    sha256: String,
}

#[derive(Deserialize)]
struct UpstreamRecord {
    repository: String,
    tag: String,
    revision: String,
    files: Vec<RecordFile>,
}

#[derive(Deserialize)]
struct RecordFile {
    path: String,
    #[serde(flatten)]
    pin: FilePin,
}

#[derive(Deserialize)]
struct Row {
    id: String,
    anchors: Vec<Anchor>,
    #[serde(skip)]
    scope: RowScope,
    #[serde(skip)]
    constants: Option<Vec<String>>,
}

#[derive(Default, Deserialize)]
struct RowScope {
    kind: Option<String>,
    reason: Option<String>,
    status: Option<String>,
    cic_l: Option<Vec<serde_json::Value>>,
    uses_rules: Option<Vec<String>>,
}

pub(super) fn decode_inventory(
    bytes: &[u8],
    check_coverage: bool,
) -> Result<Inventory, EvidenceCheckError> {
    #[derive(Deserialize)]
    struct CoverageRow {
        #[serde(flatten)]
        scope: RowScope,
        constants: Option<Vec<String>>,
    }

    #[derive(Deserialize)]
    struct CoverageRows {
        rows: Vec<CoverageRow>,
    }

    let invalid = |error| EvidenceCheckError::Invalid(format!("{RULE_INVENTORY}: {error}"));
    let mut inventory: Inventory = serde_json::from_slice(bytes).map_err(invalid)?;
    if check_coverage {
        // Anchor-only checking has always ignored this metadata. Decode only
        // the extra row fields here so that command keeps its input contract.
        let extra: CoverageRows = serde_json::from_slice(bytes).map_err(invalid)?;
        for (row, extra) in inventory.rows.iter_mut().zip(extra.rows) {
            row.scope = extra.scope;
            row.constants = extra.constants;
        }
    }
    Ok(inventory)
}

#[derive(Deserialize)]
struct Anchor {
    file: String,
    function: String,
    lines: [usize; 2],
    sha256: String,
}

#[derive(Serialize)]
pub(super) struct Report<'a> {
    upstream: &'a Identity,
    files: BTreeMap<&'a str, FileMeasured>,
    functions: BTreeMap<&'a str, Vec<FunctionMeasured>>,
    anchors: Vec<AnchorMeasured<'a>>,
    unreadable: BTreeMap<String, String>,
    findings: Vec<String>,
}

#[derive(Serialize)]
struct FileMeasured {
    raw_bytes: usize,
    raw_sha256: String,
    masked_bytes: usize,
    masked_sha256: String,
}

#[derive(Serialize)]
struct FunctionMeasured {
    name: String,
    lines: [usize; 2],
    raw_sha256: String,
    case_arms: Vec<CppCaseArm>,
    code_lines: Vec<usize>,
    hardcoded_constants: Vec<CppConstantUse>,
}

#[derive(Serialize)]
struct AnchorMeasured<'a> {
    row: &'a str,
    file: &'a str,
    function: &'a str,
    lines: [usize; 2],
    raw_bytes: usize,
    raw_sha256: String,
}

impl Report<'_> {
    fn finding(&mut self, detail: impl fmt::Display) {
        self.findings.push(format!("ANCHOR: {detail}"));
    }

    fn read(&mut self, root: &Path, relative: &str) -> Option<Vec<u8>> {
        match read_input(root, relative) {
            Ok(bytes) => Some(bytes),
            Err(EvidenceCheckError::Unavailable(reason)) => {
                self.unreadable.insert(relative.to_owned(), reason);
                None
            }
            Err(error) => {
                self.finding(error);
                None
            }
        }
    }

    pub(super) fn verdict(&self) -> Result<(), EvidenceCheckError> {
        if !self.findings.is_empty() {
            return Err(EvidenceCheckError::Invalid(format!(
                "{} C++ anchor finding(s)",
                self.findings.len()
            )));
        }
        if !self.unreadable.is_empty() {
            return Err(EvidenceCheckError::Unavailable(format!(
                "{} pinned C++ input(s) could not be read completely",
                self.unreadable.len()
            )));
        }
        Ok(())
    }
}

fn relative_path(path: &str) -> bool {
    !path.contains(['\\', '\0'])
        && path
            .split('/')
            .all(|component| !matches!(component, "" | "." | ".."))
        && Path::new(path)
            .components()
            .all(|component| matches!(component, Component::Normal(_)))
}

fn read_input(root: &Path, relative: &str) -> Result<Vec<u8>, EvidenceCheckError> {
    let path = k3_inputs::find_regular_file(root, relative).map_err(|error| match error {
        EvidenceCheckError::Invalid(_) => {
            EvidenceCheckError::Invalid(format!("{relative} traverses a symbolic link"))
        }
        other => other,
    })?;
    let path = path.ok_or_else(|| {
        EvidenceCheckError::Unavailable(format!("{relative} is not an available regular file"))
    })?;
    fs::read(path).map_err(|error| EvidenceCheckError::Unavailable(format!("{relative}: {error}")))
}

fn hex_digest(text: &str, width: usize) -> bool {
    text.len() == width
        && text
            .bytes()
            .all(|byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f'))
}

fn verify_upstream(root: &Path, upstream: &Upstream, report: &mut Report<'_>) {
    let identity = &upstream.identity;
    if identity.repository != LEAN_REPOSITORY
        || identity.tag.trim().is_empty()
        || !hex_digest(&identity.commit, 40)
    {
        report.finding(format_args!(
            "{RULE_INVENTORY} has invalid Lean upstream identity"
        ));
    }
    if upstream.files.0.len() != PINNED_FILES.len()
        || !PINNED_FILES
            .iter()
            .all(|file| upstream.files.get(file).is_some())
    {
        report.finding(format_args!(
            "{RULE_INVENTORY} does not pin the six kernel C++ files"
        ));
    }

    if let Some(bytes) = report.read(root, &upstream.toolchain_file) {
        let expected = format!("leanprover/lean4:{}", identity.tag);
        if !std::str::from_utf8(&bytes).is_ok_and(|actual| actual.trim() == expected) {
            report.finding(format_args!(
                "{} does not name {expected}",
                upstream.toolchain_file
            ));
        }
    }

    let record_path = format!("{}/UPSTREAM.json", upstream.root);
    let Some(bytes) = report.read(root, &record_path) else {
        return;
    };
    let record: UpstreamRecord = match serde_json::from_slice(&bytes) {
        Ok(record) => record,
        Err(error) => {
            report.finding(format_args!("{record_path}: {error}"));
            return;
        }
    };
    if record.repository != identity.repository
        || record.tag != identity.tag
        || record.revision != identity.commit
    {
        report.finding(format_args!(
            "{record_path} and {RULE_INVENTORY} disagree on repository, tag or commit"
        ));
    }
    let mut recorded = BTreeMap::new();
    for file in record.files {
        if PINNED_FILES.contains(&file.path.as_str())
            && recorded.insert(file.path.clone(), file.pin).is_some()
        {
            report.finding(format_args!("{record_path} repeats {}", file.path));
        }
    }
    for file in PINNED_FILES {
        if upstream
            .files
            .get(file)
            .is_some_and(|expected| recorded.get(file) != Some(expected))
        {
            report.finding(format_args!(
                "{record_path} and {RULE_INVENTORY} disagree on the byte count or SHA-256 of {file}"
            ));
        }
    }
}

fn read_sources(
    root: &Path,
    upstream: &Upstream,
    report: &mut Report<'_>,
) -> BTreeMap<&'static str, (String, String)> {
    let mut sources = BTreeMap::new();
    for file in PINNED_FILES {
        let Some(pin) = upstream.files.get(file) else {
            continue;
        };
        let relative = format!("{}/{file}", upstream.root);
        let valid_pin = hex_digest(&pin.sha256, 64);
        if !valid_pin {
            report.finding(format_args!("{relative} has an invalid pinned SHA-256"));
        }
        let Some(bytes) = report.read(root, &relative) else {
            continue;
        };
        let digest = sha256(&bytes);
        if bytes.len() != pin.bytes || (valid_pin && digest != pin.sha256) {
            report.finding(format_args!(
                "{relative} measures {} bytes at SHA-256 {digest}, pinned {} bytes at SHA-256 {}",
                bytes.len(),
                pin.bytes,
                pin.sha256
            ));
        }
        match String::from_utf8(bytes) {
            Ok(source) => {
                sources.insert(file, (source, digest));
            }
            Err(error) => report.finding(format_args!("{relative}: {error}")),
        }
    }
    sources
}

fn verify_anchors<'a>(
    inventory: &'a Inventory,
    scans: &BTreeMap<&str, CppSource<'_>>,
    check_coverage: bool,
    report: &mut Report<'a>,
) -> coverage::Claims<'a> {
    let mut claims = coverage::Claims::new();
    let mut row_ids = BTreeSet::new();
    if inventory.rows.is_empty() {
        report.finding(format_args!("{RULE_INVENTORY} has no anchor rows"));
    }
    for row in &inventory.rows {
        if row.id.trim().is_empty() || !row_ids.insert(row.id.as_str()) {
            report.finding(format_args!("blank or duplicate row id {:?}", row.id));
        }
        let kind = row.scope.kind.as_deref();
        if check_coverage && !matches!(kind, Some("rule" | "strategy" | "infrastructure")) {
            let label = kind.map_or_else(|| "None".to_owned(), |name| format!("'{name}'"));
            report.findings.push(format!(
                "SHAPE: {} kind={label} is not one of ('rule', 'strategy', 'infrastructure')",
                row.id
            ));
            continue;
        }
        if row.anchors.is_empty() {
            report.finding(format_args!("{} names no upstream anchors", row.id));
        }
        for anchor in &row.anchors {
            let contained = verify_anchor(row, anchor, &inventory.upstream, scans, report);
            if check_coverage && contained {
                claims
                    .entry((anchor.file.as_str(), anchor.function.as_str()))
                    .or_default()
                    .push((anchor.lines, row));
            }
        }
        if check_coverage {
            verify_nonrule_shape(row, report);
        }
    }
    claims
}

fn verify_nonrule_shape(row: &Row, report: &mut Report<'_>) {
    let Some(kind @ ("strategy" | "infrastructure")) = row.scope.kind.as_deref() else {
        return;
    };
    let id = &row.id;
    if row
        .scope
        .reason
        .as_deref()
        .is_none_or(|reason| reason.trim().is_empty())
    {
        report.findings.push(format!(
            "SHAPE: {id} is {kind} with no reason -- say why it states no rule"
        ));
    }
    if row.scope.status.is_some()
        || row
            .scope
            .cic_l
            .as_ref()
            .is_some_and(|items| !items.is_empty())
    {
        report.findings.push(format!(
            "SHAPE: {id} is {kind} and carries a status or CIC_L items"
        ));
    }
    let uses_rules = row
        .scope
        .uses_rules
        .as_ref()
        .is_some_and(|rules| !rules.is_empty());
    if (kind == "strategy") != uses_rules {
        report.findings.push(format!(
            "SHAPE: {id} is {kind}: `uses_rules` names the rule rows whose steps a strategy row sequences, and belongs to no other kind"
        ));
    }
}

fn verify_rule_links(inventory: &Inventory, report: &mut Report<'_>) {
    let rule_ids: BTreeSet<_> = inventory
        .rows
        .iter()
        .filter(|row| row.scope.kind.as_deref() == Some("rule"))
        .map(|row| row.id.as_str())
        .collect();
    for row in &inventory.rows {
        for target in row.scope.uses_rules.iter().flatten() {
            if !rule_ids.contains(target.as_str()) {
                report.findings.push(format!(
                    "SHAPE: {} says it sequences steps of {target}, and the inventory has no such rule family",
                    row.id
                ));
            }
        }
    }
}

fn verify_anchor<'a>(
    row: &'a Row,
    anchor: &'a Anchor,
    upstream: &Upstream,
    scans: &BTreeMap<&str, CppSource<'_>>,
    report: &mut Report<'a>,
) -> bool {
    let [lo, hi] = anchor.lines;
    let label = format!(
        "{} {}:{} lines {lo}-{hi}",
        row.id, anchor.file, anchor.function
    );
    if !PINNED_FILES.contains(&anchor.file.as_str()) || upstream.files.get(&anchor.file).is_none() {
        report.finding(format_args!("{label}: file is not pinned"));
        return false;
    }
    if lo == 0 || hi < lo {
        report.finding(format_args!("{label}: invalid inclusive line range"));
        return false;
    }
    let valid_pin = hex_digest(&anchor.sha256, 64);
    if !valid_pin {
        report.finding(format_args!("{label}: invalid pinned SHA-256"));
    }
    let Some(scan) = scans.get(anchor.file.as_str()) else {
        return false;
    };
    let Some(functions) = report.functions.get(anchor.file.as_str()) else {
        return false;
    };
    let Some(function) = functions
        .iter()
        .find(|function| function.name == anchor.function)
    else {
        report.finding(format_args!(
            "{label}: function is absent from the pinned source"
        ));
        return false;
    };
    let [start, end] = function.lines;
    if lo < start || hi > end {
        report.finding(format_args!(
            "{label}: outside the function's span {start}-{end}"
        ));
        return false;
    }
    let Some(raw) = scan.raw_lines(lo, hi) else {
        report.finding(format_args!(
            "{label}: outside the pinned source line range"
        ));
        return false;
    };
    let digest = sha256(raw.as_bytes());
    if valid_pin && digest != anchor.sha256 {
        report.finding(format_args!(
            "{label}: measures SHA-256 {digest}, pinned {}",
            anchor.sha256
        ));
    }
    report.anchors.push(AnchorMeasured {
        row: &row.id,
        file: &anchor.file,
        function: &anchor.function,
        lines: anchor.lines,
        raw_bytes: raw.len(),
        raw_sha256: digest,
    });
    // A digest mismatch does not invalidate the range for coverage.
    true
}

fn measure_functions(
    scan: &CppSource<'_>,
    local: &BTreeMap<String, String>,
    shared: &BTreeMap<String, String>,
) -> Result<Vec<FunctionMeasured>, String> {
    scan.functions_with_constant_names(local, shared)
        .map_err(|error| error.to_string())?
        .into_iter()
        .map(|function| {
            let [start, end] = function.lines;
            let raw = scan
                .raw_lines(start, end)
                .ok_or_else(|| format!("{} has no raw line range {start}-{end}", function.name))?;
            Ok(FunctionMeasured {
                name: function.name,
                lines: function.lines,
                raw_sha256: sha256(raw.as_bytes()),
                case_arms: function.case_arms,
                code_lines: function.code_lines,
                hardcoded_constants: function.hardcoded_constants,
            })
        })
        .collect()
}

pub(super) fn inspect<'a>(
    root: &Path,
    inventory: &'a Inventory,
    check_coverage: bool,
) -> Result<Report<'a>, EvidenceCheckError> {
    let upstream = &inventory.upstream;
    if !relative_path(&upstream.root) || !relative_path(&upstream.toolchain_file) {
        return Err(EvidenceCheckError::Invalid(format!(
            "{RULE_INVENTORY}: upstream root and toolchain paths must be normalized and repository-relative"
        )));
    }
    let mut report = Report {
        upstream: &upstream.identity,
        files: BTreeMap::new(),
        functions: BTreeMap::new(),
        anchors: Vec::new(),
        unreadable: BTreeMap::new(),
        findings: Vec::new(),
    };
    verify_upstream(root, upstream, &mut report);
    let sources = read_sources(root, upstream, &mut report);
    let mut scans = BTreeMap::new();
    for (file, (raw, digest)) in &sources {
        let scan = CppSource::new(raw);
        let masked = scan.masked();
        report.files.insert(
            *file,
            FileMeasured {
                raw_bytes: raw.len(),
                raw_sha256: digest.clone(),
                masked_bytes: masked.len(),
                masked_sha256: sha256(masked.as_bytes()),
            },
        );
        scans.insert(*file, scan);
    }

    // Every readable file supplies names, even when its function walk fails.
    let mut local_names = BTreeMap::new();
    let mut shared = BTreeMap::new();
    for file in upstream.files.paths() {
        if let Some(scan) = scans.get(file) {
            let local = scan.global_constant_names();
            shared.extend(
                local
                    .iter()
                    .map(|(name, value)| (name.clone(), value.clone())),
            );
            local_names.insert(file, local);
        }
    }
    for (file, local) in local_names {
        match measure_functions(&scans[file], &local, &shared) {
            Ok(functions) => {
                report.functions.insert(file, functions);
            }
            Err(error) => report.finding(format_args!("{file}: {error}")),
        }
    }
    let claims = verify_anchors(inventory, &scans, check_coverage, &mut report);
    if check_coverage {
        verify_rule_links(inventory, &mut report);
        let complete =
            scans.len() == PINNED_FILES.len() && report.functions.len() == PINNED_FILES.len();
        coverage::verify(inventory, &claims, complete, &mut report);
    }
    Ok(report)
}

pub(super) fn read_inventory_bytes(root: &Path) -> Result<Vec<u8>, EvidenceCheckError> {
    read_input(root, RULE_INVENTORY)
}

pub(super) fn run(root: &Path, check_coverage: bool) -> anyhow::Result<()> {
    let root = k3_inputs::canonical_root(root)?;
    let bytes = read_inventory_bytes(&root)?;
    let inventory = decode_inventory(&bytes, check_coverage)?;
    let report = inspect(&root, &inventory, check_coverage)?;
    let mut output = io::stdout().lock();
    serde_json::to_writer_pretty(&mut output, &report)?;
    writeln!(output)?;
    report.verdict()?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    const SOURCE: &str = "int f() { return 1; }\nint g() { return 2; }\n";
    const TAG: &str = "v4.30.0-rc2";
    const COMMIT: &str = "3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc";
    const PROVENANCE: &str = "pinned/UPSTREAM.json";

    #[test]
    fn file_pins_preserve_wire_order_and_reject_duplicate_keys() {
        let pin = r#"{"bytes":1,"sha256":"fixture"}"#;
        let first = PINNED_FILES[5];
        let second = PINNED_FILES[0];
        let pins: FilePins =
            serde_json::from_str(&format!(r#"{{"{first}":{pin},"{second}":{pin}}}"#)).unwrap();
        assert_eq!(pins.paths().collect::<Vec<_>>(), [first, second]);

        let repeated = format!(r#"{{"{first}":{pin},"{first}":{pin}}}"#);
        let Err(error) = serde_json::from_str::<FilePins>(&repeated) else {
            panic!("duplicate C++ file pin was accepted");
        };
        assert!(error.to_string().contains("duplicate C++ file pin"));
    }

    fn write(root: &Path, relative: &str, text: &str) {
        let path = root.join(relative);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, text).unwrap();
    }

    fn fixture() -> tempfile::TempDir {
        let root = tempfile::tempdir().unwrap();
        let digest = sha256(SOURCE.as_bytes());
        let anchor = sha256(CppSource::new(SOURCE).raw_lines(1, 1).unwrap().as_bytes());
        let mut pins = BTreeMap::new();
        let mut recorded = Vec::new();
        for file in PINNED_FILES {
            write(root.path(), &format!("pinned/{file}"), SOURCE);
            pins.insert(file, json!({"bytes": SOURCE.len(), "sha256": digest}));
            recorded.push(json!({"path": file, "bytes": SOURCE.len(), "sha256": digest}));
        }
        let inventory = json!({
            "upstream": {
                "repository": LEAN_REPOSITORY, "tag": TAG, "commit": COMMIT,
                "root": "pinned", "toolchain_file": "lean-toolchain", "files": pins,
            },
            "rows": [{
                "id": "declare-f",
                "anchors": [{
                    "file": PINNED_FILES[0], "function": "f", "lines": [1, 1], "sha256": anchor,
                }],
            }],
        });
        let record = json!({
            "repository": LEAN_REPOSITORY, "tag": TAG, "revision": COMMIT, "files": recorded,
        });
        write(root.path(), RULE_INVENTORY, &inventory.to_string());
        write(root.path(), PROVENANCE, &record.to_string());
        write(
            root.path(),
            "lean-toolchain",
            &format!("leanprover/lean4:{TAG}\n"),
        );
        root
    }

    #[test]
    fn missing_provenance_is_unavailable() {
        let root = fixture();
        fs::remove_file(root.path().join(PROVENANCE)).unwrap();
        let error = run(root.path(), false).unwrap_err();
        assert!(matches!(
            error.downcast_ref::<EvidenceCheckError>(),
            Some(EvidenceCheckError::Unavailable(_))
        ));
    }

    #[test]
    fn invalid_provenance_takes_precedence_over_missing_source() {
        let root = fixture();
        fs::remove_file(root.path().join("pinned").join(PINNED_FILES[0])).unwrap();
        write(root.path(), PROVENANCE, "{");
        let error = run(root.path(), false).unwrap_err();
        assert!(matches!(
            error.downcast_ref::<EvidenceCheckError>(),
            Some(EvidenceCheckError::Invalid(_))
        ));
    }

    #[test]
    fn anchor_must_belong_to_the_named_function() {
        let root = fixture();
        let mut inventory: Inventory =
            super::super::read_json(root.path(), RULE_INVENTORY).unwrap();
        let report = inspect(root.path(), &inventory, false).unwrap();
        assert!(report.verdict().is_ok());
        assert_eq!(report.anchors.len(), 1);

        // Keep the matching raw digest and point at the other definition.
        inventory.rows[0].anchors[0].function = "g".to_owned();
        let report = inspect(root.path(), &inventory, false).unwrap();
        assert!(matches!(
            report.verdict(),
            Err(EvidenceCheckError::Invalid(_))
        ));
        assert!(report.anchors.is_empty());
        assert!(report.findings[0].contains("outside the function's span 2-2"));
    }

    #[test]
    fn coverage_metadata_is_decoded_only_under_coverage() {
        let root = fixture();
        let mut input: serde_json::Value =
            super::super::read_json(root.path(), RULE_INVENTORY).unwrap();
        input["rows"][0]["uses_rules"] = json!(42);
        let bytes = serde_json::to_vec(&input).unwrap();

        let inventory = decode_inventory(&bytes, false).unwrap();
        let report = inspect(root.path(), &inventory, false).unwrap();
        assert!(report.verdict().is_ok());
        assert_eq!(report.anchors.len(), 1);
        assert!(matches!(
            decode_inventory(&bytes, true),
            Err(EvidenceCheckError::Invalid(_))
        ));
    }
}

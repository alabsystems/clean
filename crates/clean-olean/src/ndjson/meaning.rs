// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Measure a package root in the structurally loaded export using its original
//! compiled module inventory. This is a canonical identity comparison.

use super::{load::load_export, source::NdjsonSource, ExportMeta};
use crate::import::read_artifact_observing_parts;
use crate::meaning_digest::{MeaningDigests, MeaningError, Package, FORMAT_VERSION};
use crate::{ArtifactDepth, ArtifactInventoryError, OleanImportError};
use clean_kernel::Name;
use serde::Serialize;
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::io::{self, BufReader, Read};
use std::path::Path;

#[derive(Debug, thiserror::Error)]
pub enum MeasureError {
    #[error(transparent)]
    Artifact(#[from] OleanImportError),
    #[error(transparent)]
    Inventory(#[from] ArtifactInventoryError),
    #[error("export: {0}")]
    Export(String),
    #[error(transparent)]
    Meaning(#[from] MeaningError),
    #[error("{0}")]
    Scope(String),
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

/// Hash the very bytes the structural reader consumes, in one streaming pass.
struct HashingReader<R> {
    input: R,
    hash: Sha256,
}

impl<R: Read> Read for HashingReader<R> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let n = self.input.read(buf)?;
        self.hash.update(&buf[..n]);
        Ok(n)
    }
}

#[derive(Serialize)]
pub struct Observation {
    pub schema: &'static str,
    pub meaning_format: u32,
    /// Caller-supplied label. The part hashes identify the source of the inventory.
    pub module: String,
    pub root: String,
    pub inventory: Vec<String>,
    pub olean_sha256: BTreeMap<&'static str, String>,
    pub input_sha256: String,
    pub export_meta: ExportMeta,
    pub digest: String,
    pub root_reducibility: String,
    pub reachable_singleton_digests: BTreeMap<String, String>,
    pub structural_refusals: BTreeMap<String, String>,
    pub unreplayable: BTreeMap<String, &'static str>,
}

/// Return the production library digest and its source identities. Refuse a
/// root outside the inventory, or an export that cannot supply its exact
/// package records. Referenced names outside the module are import boundaries.
pub fn measure(
    input: impl Read,
    module: &str,
    olean: &Path,
    root_label: &str,
) -> Result<Observation, MeasureError> {
    if module.trim().is_empty() {
        return Err(MeasureError::Scope(
            "module inventory label is empty".into(),
        ));
    }
    let mut olean_sha256 = BTreeMap::new();
    let artifact =
        read_artifact_observing_parts(module, olean, ArtifactDepth::Records, |part, bytes| {
            olean_sha256.insert(part, hex(&Sha256::digest(bytes)));
        })?;
    // Header constNames omit payload-only locals. Use the complete validated
    // record inventory so no such local becomes an import boundary.
    let inventory = artifact.inventory.ok_or_else(|| {
        MeasureError::Scope("compiled artifact has no strict record inventory".into())
    })??;
    let names: Vec<_> = inventory
        .declarations()
        .iter()
        .map(|decl| decl.name().clone())
        .collect();
    let root = names
        .iter()
        .find(|name| name.to_unambiguous_string() == root_label)
        .cloned()
        .ok_or_else(|| {
            MeasureError::Scope(format!("{root_label} is outside the module inventory"))
        })?;
    let package = Package::of_module_names([(module.to_owned(), names)]);
    let mut input = HashingReader {
        input,
        hash: Sha256::new(),
    };
    let source = NdjsonSource::as_written(BufReader::new(&mut input))
        .map_err(|error| MeasureError::Export(error.to_string()))?;
    let loaded = load_export(source).map_err(|error| MeasureError::Export(error.to_string()))?;
    // Replay can preserve verdicts by escaping a name in its internal
    // environment. The digest includes names, so that transform cannot attest
    // the canonical identity of the original export.
    if let Some(name) = loaded
        .written_names
        .values()
        .map(Name::to_unambiguous_string)
        .min()
    {
        return Err(MeasureError::Scope(format!(
            "export stores the written name {name} under an escape"
        )));
    }
    let declared: BTreeSet<_> = loaded.declared.iter().map(|row| &row.name).collect();
    let check = |name: &Name| -> Result<(), MeasureError> {
        let shown = name.to_unambiguous_string();
        if let Some(reason) = loaded.refused.get(name) {
            return Err(MeasureError::Scope(format!(
                "reachable {shown} was refused: {reason}"
            )));
        }
        if let Some(reason) = loaded.not_replayable.get(name) {
            return Err(MeasureError::Scope(format!(
                "reachable {shown} is unreplayable: {reason}"
            )));
        }
        if !declared.contains(name) {
            return Err(MeasureError::Scope(format!(
                "reachable {shown} was not declared by the export"
            )));
        }
        Ok(())
    };
    check(&root)?;
    let digests = MeaningDigests::new(&loaded.env, &package);
    let mut records = BTreeMap::new();
    for name in digests.closure(&root)? {
        check(&name)?;
        let singleton = Package::of_names(BTreeSet::from([name.clone()]));
        records.insert(
            name.to_unambiguous_string(),
            MeaningDigests::new(&loaded.env, &singleton).digest(&name)?,
        );
    }
    let constant = loaded
        .env
        .get_const(&root)
        .ok_or_else(|| MeasureError::Scope(format!("missing exported root {root_label}")))?;
    Ok(Observation {
        schema: "clean.export-meaning/1",
        meaning_format: FORMAT_VERSION,
        module: module.to_owned(),
        root: root_label.to_owned(),
        inventory: package
            .names()
            .iter()
            .map(Name::to_unambiguous_string)
            .collect(),
        olean_sha256,
        input_sha256: hex(&input.hash.finalize()),
        export_meta: loaded.meta,
        digest: digests.digest(&root)?,
        root_reducibility: format!("{:?}", constant.reducibility),
        reachable_singleton_digests: records,
        structural_refusals: loaded
            .refused
            .into_iter()
            .map(|(name, reason)| (name.to_unambiguous_string(), reason))
            .collect(),
        unreplayable: loaded
            .not_replayable
            .into_iter()
            .map(|(name, reason)| (name.to_unambiguous_string(), reason))
            .collect(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use flate2::read::GzDecoder;
    use std::fs;

    const ROOT: &str = "KCheck.Advice.start";

    fn archived(name: &str) -> Vec<u8> {
        let dir =
            Path::new(env!("CARGO_MANIFEST_DIR")).join("../../reports/self-proof-w3-advice-start");
        let mut bytes = Vec::new();
        GzDecoder::new(fs::File::open(dir.join(name)).expect("archive"))
            .read_to_end(&mut bytes)
            .expect("decompress archive");
        bytes
    }

    fn with_olean(check: impl FnOnce(&Path)) {
        let dir = tempfile::tempdir().expect("scratch");
        let path = dir.path().join("Token.olean");
        fs::write(&path, archived("canonical/Token.olean.gz")).expect("unchanged inventory");
        check(&path)
    }

    #[test]
    fn a_payload_only_helper_remains_in_the_package_closure() {
        use crate::{CleanPayload, OleanExporter};
        use clean_kernel::{ConstantInfo, Expr};

        let payload = CleanPayload {
            constants: vec![
                ConstantInfo::new(
                    Name::from_string("Helper"),
                    vec![],
                    Expr::type_(),
                    Some(Expr::prop()),
                    false,
                ),
                ConstantInfo::new(
                    Name::from_string("Root"),
                    vec![],
                    Expr::type_(),
                    Some(Expr::const_str("Helper")),
                    false,
                ),
            ],
            ..Default::default()
        };
        let git_hash = "3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc";
        let bytes = OleanExporter::export_with_payload(&[], &["Root"], &[], git_hash, &payload)
            .expect("module with a payload-only local");
        let dir = tempfile::tempdir().expect("scratch");
        let olean = dir.path().join("Example.olean");
        fs::write(&olean, bytes).expect("compiled fixture");
        let export = br#"{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},"lean":{"version":"4.30.0-rc2","githash":"3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc"},"format":{"version":"3.1.0"}}}
{"in":1,"str":{"pre":0,"str":"Helper"}}
{"in":2,"str":{"pre":0,"str":"Root"}}
{"il":1,"succ":0}
{"ie":0,"sort":0}
{"ie":1,"sort":1}
{"ie":2,"const":{"name":1,"us":[]}}
{"def":{"name":1,"levelParams":[],"type":1,"value":0,"hints":{"regular":1},"safety":"safe","all":[1]}}
{"def":{"name":2,"levelParams":[],"type":1,"value":2,"hints":{"regular":2},"safety":"safe","all":[2]}}
"#;
        let report = measure(&export[..], "Example", &olean, "Root").expect("valid package");
        assert_eq!(report.inventory, ["Helper", "Root"]);
        assert_eq!(
            report
                .reachable_singleton_digests
                .keys()
                .collect::<Vec<_>>(),
            ["Helper", "Root"]
        );
    }

    #[test]
    fn a_truncated_const_names_array_cannot_shrink_a_real_package() {
        use crate::{parse_header, CompactedRegion};

        with_olean(|olean| {
            let mut bytes = fs::read(olean).expect("Token artifact");
            let region =
                CompactedRegion::new(&bytes, parse_header(&bytes).expect("header").base_addr);
            let module = region
                .ptr_to_offset(region.root_ptr().expect("module pointer"))
                .expect("module");
            let names_ptr = region.read_u64_at(module + 16).expect("constNames pointer");
            let size_at = region.ptr_to_offset(names_ptr).expect("constNames array") + 8;
            let size = region.read_u64_at(size_at).expect("constNames length");
            assert_eq!(size, 196);
            bytes[size_at..size_at + 8].copy_from_slice(&(size - 1).to_le_bytes());
            fs::write(olean, bytes).expect("shrink only the name array");
            let wire = archived("resident.ndjson.gz");
            assert!(matches!(
                measure(wire.as_slice(), "KCheck.Token", olean, ROOT),
                Err(MeasureError::Inventory(
                    ArtifactInventoryError::NameRecordMismatch
                ))
            ));
        });
    }

    #[test]
    fn historical_exports_agree_on_six_of_seven_package_records() {
        with_olean(|olean| {
            let read = |label: &str| {
                let bytes = archived(&format!("{label}.ndjson.gz"));
                let result = measure(bytes.as_slice(), "KCheck.Token", olean, ROOT)
                    .expect("exact archived reading");
                assert_eq!(result.input_sha256, hex(&Sha256::digest(bytes)));
                assert_eq!(
                    result.olean_sha256["olean"],
                    "0eff27371b8500fea76d40fd55be52664b64b301b13ee0c1a649477ca95e2963"
                );
                assert_eq!(result.inventory.len(), 196);
                assert_eq!(result.reachable_singleton_digests.len(), 7);
                result
            };
            let resident = read("resident");
            let original = read("original");
            assert_eq!(
                resident.digest,
                "6af05c1072e33fc96704659a72698f8ec196947562a3a5194a6e9cacb5cc2d74"
            );
            assert_eq!(
                original.digest,
                "53c5adc61ea1b9536796b9d0c129cf3bbaa2d5350b3dbc358b54b74dc06b20d3"
            );
            assert_eq!(
                original.structural_refusals.keys().collect::<Vec<_>>(),
                ["Eq.rec"]
            );
            assert!(resident.structural_refusals.is_empty());
            for (name, reference) in resident.reachable_singleton_digests {
                assert_eq!(
                    original.reachable_singleton_digests[&name] == reference,
                    name != ROOT
                );
            }
        });
    }

    #[test]
    fn missing_outside_and_refused_roots_cannot_produce_a_digest() {
        with_olean(|olean| {
            let original = archived("original.ndjson.gz");
            assert!(matches!(
                measure(original.as_slice(), "  ", olean, ROOT),
                Err(MeasureError::Scope(_))
            ));
            let error = |bytes: &[u8], name: &str| {
                measure(bytes, "KCheck.Token", olean, name)
                    .err()
                    .expect("refused")
                    .to_string()
            };
            assert!(error(b"invalid\n", ROOT).contains("export:"));
            assert!(error(&original, "Nat").contains("outside the module inventory"));
            assert!(error(&original, "KCheck.Advice.exhausted").contains("was not declared"));
            // A root with an undeclared dependency produces a named structural refusal.
            let text = std::str::from_utf8(&original).expect("original NDJSON");
            let mut rows = Vec::new();
            let mut replaced = 0;
            for line in text.lines() {
                let row: serde_json::Value = serde_json::from_str(line).expect("original wire row");
                if row["def"]["name"].as_u64() == Some(77) {
                    // Reference a name which the export never declares.
                    rows.push(r#"{"in":90000,"str":{"pre":0,"str":"PR75Missing"}}"#.to_string());
                    rows.push(r#"{"ie":90000,"const":{"name":90000,"us":[]}}"#.to_string());
                    let mut changed = row;
                    changed["def"]["value"] = 90000.into();
                    rows.push(changed.to_string());
                    replaced += 1;
                } else {
                    rows.push(line.to_owned());
                }
            }
            assert_eq!(replaced, 1);
            assert!(error(rows.join("\n").as_bytes(), ROOT).contains("PR75Missing"));
        });
    }
}

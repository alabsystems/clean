// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Offline transport and reporting for the K3 export's syntax check.

use super::k3_inputs::{canonical_root, find_regular_file};
use crate::EvidenceCheckError;
use clean_olean::k3_export_syntax::{
    check_k3_accepted_statements, check_k3_base_families, check_k3_declaration_bodies,
    check_k3_declaration_names, check_k3_export_expressions, check_k3_export_levels,
    check_k3_export_names, check_k3_export_syntax, check_k3_fragment_classes,
    check_k3_non_inductive_bodies, k3_declaration_index, K3AcceptedStatementSummary,
    K3BaseRecognitionSummary, K3DeclarationBodySummary, K3DeclarationIndexRow,
    K3DeclarationNameSummary, K3ExportSyntaxError, K3FragmentSummary, K3NonInductiveBodySummary,
};
use flate2::read::MultiGzDecoder;
use sha2::{Digest, Sha256};
use std::fs::File;
use std::io::{self, BufRead, BufReader, ErrorKind, Read};
use std::path::Path;

pub(super) const EXPORT: &str =
    "crates/clean-olean/tests/fixtures/lean/v4.30.0-rc2/lean4export_minted/prelude_roots.ndjson.gz";

pub(super) fn input_error(error: K3ExportSyntaxError) -> EvidenceCheckError {
    let message = format!("{EXPORT}: {error}");
    match error {
        K3ExportSyntaxError::Io { source, .. } => match source.kind() {
            ErrorKind::InvalidData | ErrorKind::InvalidInput | ErrorKind::UnexpectedEof => {
                EvidenceCheckError::Invalid(message)
            }
            _ => EvidenceCheckError::Unavailable(message),
        },
        K3ExportSyntaxError::Invalid { .. } => EvidenceCheckError::Invalid(message),
    }
}

fn open_export_file(root: &Path) -> Result<File, EvidenceCheckError> {
    let path = find_regular_file(root, EXPORT)?
        .ok_or_else(|| EvidenceCheckError::Unavailable(format!("{EXPORT} does not exist")))?;
    File::open(&path)
        .map_err(|error| EvidenceCheckError::Unavailable(format!("{}: {error}", path.display())))
}

fn open_export(root: &Path) -> Result<impl BufRead, EvidenceCheckError> {
    Ok(BufReader::new(MultiGzDecoder::new(open_export_file(root)?)))
}

pub(super) fn declaration_index(
    root: &Path,
) -> Result<Vec<K3DeclarationIndexRow>, EvidenceCheckError> {
    k3_declaration_index(open_export(root)?).map_err(input_error)
}

pub(super) fn non_inductive_bodies(
    root: &Path,
) -> Result<K3NonInductiveBodySummary, EvidenceCheckError> {
    check_k3_non_inductive_bodies(open_export(root)?).map_err(input_error)
}

pub(super) fn declaration_bodies(
    root: &Path,
) -> Result<K3DeclarationBodySummary, EvidenceCheckError> {
    check_k3_declaration_bodies(open_export(root)?).map_err(input_error)
}

pub(super) fn declaration_names(
    root: &Path,
) -> Result<K3DeclarationNameSummary, EvidenceCheckError> {
    check_k3_declaration_names(open_export(root)?).map_err(input_error)
}

pub(super) fn accepted_statements(
    root: &Path,
) -> Result<K3AcceptedStatementSummary, EvidenceCheckError> {
    check_k3_accepted_statements(open_export(root)?).map_err(input_error)
}

pub(super) fn base_families(root: &Path) -> Result<K3BaseRecognitionSummary, EvidenceCheckError> {
    check_k3_base_families(open_export(root)?).map_err(input_error)
}

pub(super) fn fragment_classes(root: &Path) -> Result<K3FragmentSummary, EvidenceCheckError> {
    check_k3_fragment_classes(open_export(root)?).map_err(input_error)
}

pub(super) struct HashedExport {
    pub(super) summary: K3FragmentSummary,
    pub(super) gzip_sha256: String,
    pub(super) raw_sha256: String,
}

pub(super) fn fragment_classes_with_hashes(
    root: &Path,
) -> Result<HashedExport, EvidenceCheckError> {
    check_hashed_export(open_export_file(root)?)
}

fn check_hashed_export(input: impl Read) -> Result<HashedExport, EvidenceCheckError> {
    let gzip = DigestingReader::new(input);
    let raw = DigestingReader::new(MultiGzDecoder::new(gzip));
    let mut reader = BufReader::new(raw);
    let summary = check_k3_fragment_classes(&mut reader).map_err(input_error)?;
    let raw = reader.into_inner();
    let gzip = raw.reader.into_inner();
    // Only finish the digests after the scanner and multi-member decoder both
    // reach EOF. This includes the final member's gzip footer.
    if !raw.eof || !gzip.eof {
        return Err(EvidenceCheckError::Invalid(format!(
            "{EXPORT}: export validation did not reach end of input"
        )));
    }
    Ok(HashedExport {
        summary,
        gzip_sha256: digest_hex(&gzip.digest.finalize()),
        raw_sha256: digest_hex(&raw.digest.finalize()),
    })
}

struct DigestingReader<R> {
    reader: R,
    digest: Sha256,
    eof: bool,
}

impl<R> DigestingReader<R> {
    fn new(reader: R) -> Self {
        Self {
            reader,
            digest: Sha256::new(),
            eof: false,
        }
    }
}

impl<R: Read> Read for DigestingReader<R> {
    fn read(&mut self, bytes: &mut [u8]) -> io::Result<usize> {
        let count = self.reader.read(bytes)?;
        if count != 0 {
            self.digest.update(&bytes[..count]);
        } else if !bytes.is_empty() {
            self.eof = true;
        }
        Ok(count)
    }
}

pub(super) fn digest_hex(digest: &[u8]) -> String {
    digest.iter().map(|byte| format!("{byte:02x}")).collect()
}

pub(super) fn sha256_bytes(bytes: &[u8]) -> String {
    digest_hex(&Sha256::digest(bytes))
}

pub(super) fn run(
    root: &Path,
    check_names: bool,
    check_levels: bool,
    check_expressions: bool,
) -> Result<(), EvidenceCheckError> {
    let root = canonical_root(root)?;
    let reader = open_export(&root)?;
    if check_expressions {
        let result = check_k3_export_expressions(reader).map_err(input_error)?;
        println!(
            "K3 export syntax, name, level, and expression tables are valid ({} NDJSON records, {} explicit names, {} explicit levels, maximum unfolded level size {}, {} explicit expressions, maximum unfolded expression size {}, lean4export 3.1.0)",
            result.tables.records, result.tables.explicit_names, result.tables.explicit_levels,
            result.tables.max_unfolded_level_nodes, result.explicit_expressions,
            result.max_unfolded_expression_nodes,
        );
    } else if check_levels {
        let result = check_k3_export_levels(reader).map_err(input_error)?;
        println!(
            "K3 export syntax, name table, and level table are valid ({} NDJSON records, {} explicit names, {} explicit levels, maximum unfolded level size {}, lean4export 3.1.0)",
            result.records, result.explicit_names, result.explicit_levels, result.max_unfolded_level_nodes
        );
    } else if check_names {
        let result = check_k3_export_names(reader).map_err(input_error)?;
        println!(
            "K3 export syntax and name table are valid ({} NDJSON records, {} explicit names, lean4export 3.1.0)",
            result.records, result.explicit_names
        );
    } else {
        let records = check_k3_export_syntax(reader).map_err(input_error)?;
        println!("K3 export syntax is valid ({records} NDJSON records, lean4export 3.1.0)");
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use flate2::{write::GzEncoder, Compression};
    use std::io::Write;

    const META: &[u8] = b"{\"meta\":{\"format\":{\"version\":\"3.1.0\"}}}\n";

    fn gzip(bytes: &[u8]) -> Vec<u8> {
        let mut encoder = GzEncoder::new(Vec::new(), Compression::default());
        encoder.write_all(bytes).unwrap();
        encoder.finish().unwrap()
    }

    #[test]
    fn hashes_every_member_through_the_same_validated_stream() {
        let (head, tail) = META.split_at(13);
        let mut bytes = gzip(head);
        bytes.extend(gzip(tail));
        bytes.extend(gzip(b""));
        let checked = check_hashed_export(bytes.as_slice()).unwrap();
        assert_eq!(checked.gzip_sha256, sha256_bytes(&bytes));
        assert_eq!(checked.raw_sha256, sha256_bytes(META));
    }

    #[test]
    fn refuses_a_bad_footer_even_after_valid_export_lines() {
        let mut bytes = gzip(META);
        bytes.pop().unwrap();
        assert!(matches!(
            check_hashed_export(bytes.as_slice()),
            Err(EvidenceCheckError::Invalid(_))
        ));
    }
}

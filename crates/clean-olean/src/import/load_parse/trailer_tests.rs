// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R113 finding B3 at the LOADER's parsers (`parse_load_module`,
//! `parse_load_module_incremental`), the path every import takes. The review
//! (P6) found no test reaching them: every trailer test was refused first by
//! the `ParsedModule` reader in `module/readers.rs`. The checked-in Lean
//! v4.30.0-rc2 module-system triple `Sigma.olean{,.server,.private}` is real
//! Lean output; a `CLEANENV` trailer appended to any of its parts is foreign.

use super::*;
use crate::payload::encode_clean_payload;

fn sigma_parts() -> [Vec<u8>; 3] {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/olean/v4.30.0/module-system");
    ["Sigma.olean", "Sigma.olean.server", "Sigma.olean.private"]
        .map(|name| std::fs::read(dir.join(name)).expect("checked-in Lean module-system part"))
}

fn trailered(mut bytes: Vec<u8>) -> Vec<u8> {
    bytes.extend(encode_clean_payload(&CleanPayload::default()).expect("encode trailer"));
    bytes
}

fn is_foreign_trailer(result: OleanResult<LoadModule>) -> bool {
    matches!(result, Err(OleanError::PayloadOnLeanPart(_)))
}

#[test]
fn test_loader_parsers_refuse_a_trailer_on_each_lean_part() {
    let [base, server, private] = sigma_parts();
    // Control: the untouched parts parse.
    parse_load_module(base.clone()).expect("the Lean base part parses");
    parse_load_module_incremental(&base, None, server.clone()).expect("the server part parses");
    parse_load_module_incremental(&base, Some(&server), private.clone())
        .expect("the private part parses");

    assert!(
        is_foreign_trailer(parse_load_module(trailered(base.clone()))),
        "a trailer on the base part must be refused"
    );
    assert!(
        is_foreign_trailer(parse_load_module_incremental(
            &base,
            None,
            trailered(server.clone())
        )),
        "a trailer on the server part must be refused"
    );
    assert!(
        is_foreign_trailer(parse_load_module_incremental(
            &base,
            Some(&server),
            trailered(private)
        )),
        "a trailer on the private part must be refused"
    );
}

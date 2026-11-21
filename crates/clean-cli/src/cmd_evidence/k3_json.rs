// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Emit Python's ASCII, two-space JSON layout for ordered K3 fields.

use serde::Serialize;
use std::io::Write;

pub(super) fn write(output: &mut impl Write, value: &impl Serialize) -> anyhow::Result<()> {
    // The payload's typed fields are declared in lexical order, as in
    // json.dumps(sort_keys=True). JSON punctuation and all numeric fields
    // are ASCII, so the remaining non-ASCII characters are string contents.
    let json = serde_json::to_string_pretty(value)?;
    let bytes = json.as_bytes();
    let mut start = 0;
    for (offset, character) in json
        .char_indices()
        .filter(|(_, character)| !character.is_ascii() || *character == '\x7f')
    {
        output.write_all(&bytes[start..offset])?;
        let mut utf16 = [0; 2];
        for code_unit in character.encode_utf16(&mut utf16) {
            write!(output, "\\u{code_unit:04x}")?;
        }
        start = offset + character.len_utf8();
    }
    output.write_all(&bytes[start..])?;
    writeln!(output)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn preserves_python_ascii_escapes_indentation_and_final_lf() {
        #[derive(Serialize)]
        struct Example<'text> {
            label: &'text str,
            rows: [&'text str; 2],
        }

        let value = Example {
            label: "π\x7f🧪",
            rows: ["x/y", "\"\\\n"],
        };
        let mut output = Vec::new();
        write(&mut output, &value).unwrap();
        assert_eq!(
            output,
            br#"{
  "label": "\u03c0\u007f\ud83e\uddea",
  "rows": [
    "x/y",
    "\"\\\n"
  ]
}
"#,
        );
    }
}

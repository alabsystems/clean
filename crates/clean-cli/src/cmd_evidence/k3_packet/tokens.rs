// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Token flags from the syntax of an accepted K3 frame.

#[derive(Debug, Default, PartialEq, Eq)]
pub(super) struct TokenFlags {
    pub(super) iota: bool,
    pub(super) k: bool,
}

/// Scan the tag and operand grammar of `KCheck.decodeAt`.
pub(super) fn scan_tokens(frame: &[u8]) -> Result<TokenFlags, String> {
    let mut flags = TokenFlags::default();
    let mut bytes = frame.iter().copied().enumerate();
    while let Some((offset, tag)) = bytes.next() {
        match tag {
            0x01 | 0x08 | 0x09 | 0x15 => {
                // The operand is a Lean Nat. Its width is not limited by a
                // Rust integer because only the token boundary matters here.
                let (end, last) = bytes
                    .by_ref()
                    .find(|&(_, byte)| byte & 0x80 == 0)
                    .ok_or_else(|| {
                        format!(
                            "truncated operand for tag {tag:#04x} at byte {}",
                            frame.len()
                        )
                    })?;
                if last == 0 && end > offset + 1 {
                    return Err(format!(
                        "nonminimal operand for tag {tag:#04x} at byte {end}"
                    ));
                }
            }
            0x0b => flags.iota = true,
            0x0c => flags.k = true,
            0x02..=0x07 | 0x0a | 0x0d..=0x14 | 0x16 => {}
            _ => return Err(format!("unknown token tag {tag:#04x} at byte {offset}")),
        }
    }
    Ok(flags)
}

#[cfg(test)]
mod tests {
    use super::{scan_tokens, TokenFlags};

    #[test]
    fn accepts_the_full_lean_tag_table() {
        let frame = [
            0x01, 0, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0, 0x09, 0, 0x0a, 0x0b, 0x0c, 0x0d,
            0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0, 0x16,
        ];
        assert_eq!(
            scan_tokens(&frame).unwrap(),
            TokenFlags {
                iota: true,
                k: true,
            }
        );
    }

    #[test]
    fn operand_bytes_do_not_set_token_flags() {
        let operands = [0x01, 0x0b, 0x08, 0x80, 0x0c, 0x09, 0, 0x15, 0x0b, 0x16];
        assert_eq!(scan_tokens(&operands).unwrap(), TokenFlags::default());
        assert_eq!(
            scan_tokens(&[0x0c, 0x01, 0x0b]).unwrap(),
            TokenFlags {
                iota: false,
                k: true,
            }
        );
    }

    #[test]
    fn accepts_a_nat_wider_than_machine_integers() {
        let mut frame = vec![0x08];
        frame.extend([0x80; 24]);
        frame.extend([0x01, 0x0b]);
        assert_eq!(
            scan_tokens(&frame).unwrap(),
            TokenFlags {
                iota: true,
                k: false,
            }
        );
    }

    #[test]
    fn reports_unknown_tags_and_malformed_operands_at_their_byte_offsets() {
        let cases: &[(&[u8], &str)] = &[
            (&[0x00], "unknown token tag 0x00 at byte 0"),
            (&[0x16, 0x17], "unknown token tag 0x17 at byte 1"),
            (&[0x02, 0x01], "truncated operand for tag 0x01 at byte 2"),
            (
                &[0x02, 0x08, 0x80, 0xff],
                "truncated operand for tag 0x08 at byte 4",
            ),
            (
                &[0x01, 0x80, 0x00, 0x0b],
                "nonminimal operand for tag 0x01 at byte 2",
            ),
        ];
        for &(frame, expected) in cases {
            assert_eq!(scan_tokens(frame).unwrap_err(), expected);
        }
    }
}

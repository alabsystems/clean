// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The length-prefixed frame syntax of K3 advice.

/// Split the stream into opaque payloads with minimal unsigned LEB128 lengths.
pub(super) fn split_frames(advice: &[u8]) -> Result<Vec<&[u8]>, String> {
    let mut frames = Vec::new();
    let mut at = 0;
    while at < advice.len() {
        let start = at;
        let remaining = &advice[start..];
        // Find the terminator before decoding so EOF and nonminimality take
        // precedence over an overflowing length, as in the Python reader.
        let last = remaining
            .iter()
            .position(|&byte| byte & 0x80 == 0)
            .ok_or_else(|| format!("the advice ends inside a frame length at byte {start}"))?;
        if last > 0 && remaining[last] == 0 {
            return Err(format!(
                "the frame length at byte {start} is not minimal LEB128"
            ));
        }
        let prefix = &remaining[..=last];
        let length = prefix
            .iter()
            .rev()
            .try_fold(0usize, |length, &byte| {
                length.checked_mul(128)?.checked_add(usize::from(byte & 0x7f))
            })
            .ok_or_else(|| {
                format!("the frame at byte {start} states a length larger than usize and the advice ends first")
            })?;
        at += prefix.len();
        if length > advice.len() - at {
            return Err(format!(
                "the frame at byte {start} states {length} bytes and the advice ends first"
            ));
        }
        let end = at + length;
        frames.push(&advice[at..end]);
        at = end;
    }
    Ok(frames)
}

#[cfg(test)]
mod tests {
    use super::split_frames;

    #[test]
    fn splits_empty_opaque_and_multibyte_frames_in_order() {
        assert!(split_frames(&[]).unwrap().is_empty());

        let payload = [0xff; 128];
        let mut advice = vec![0x00, 0x02, 0x00, 0xff, 0x80, 0x01];
        advice.extend(payload);
        advice.push(0x00);

        assert_eq!(
            split_frames(&advice).unwrap(),
            [&[][..], &[0x00, 0xff], &payload, &[]]
        );
    }

    #[test]
    fn reports_the_start_of_each_malformed_length_or_payload() {
        let cases: &[(&[u8], &str)] = &[
            (
                &[0x01, 0xff, 0x80],
                "the advice ends inside a frame length at byte 2",
            ),
            (
                &[0x01, 0xff, 0x81, 0x00],
                "the frame length at byte 2 is not minimal LEB128",
            ),
            (
                &[0x01, 0xff, 0x02, 0x00],
                "the frame at byte 2 states 2 bytes and the advice ends first",
            ),
        ];
        for &(advice, expected) in cases {
            assert_eq!(split_frames(advice).unwrap_err(), expected);
        }
    }

    #[test]
    fn checks_length_termination_and_minimality_before_overflow() {
        let mut advice = vec![0xff; usize::BITS.div_ceil(7) as usize];
        assert_eq!(
            split_frames(&advice).unwrap_err(),
            "the advice ends inside a frame length at byte 0"
        );

        advice.push(0x00);
        assert_eq!(
            split_frames(&advice).unwrap_err(),
            "the frame length at byte 0 is not minimal LEB128"
        );

        *advice.last_mut().unwrap() = 0x01;
        assert_eq!(
            split_frames(&advice).unwrap_err(),
            "the frame at byte 0 states a length larger than usize and the advice ends first"
        );
    }

    #[test]
    fn refuses_a_platform_maximum_length_as_truncated() {
        let complete_groups = (usize::BITS - 1) / 7;
        let remaining_bits = usize::BITS - complete_groups * 7;
        let mut advice = vec![0xff; complete_groups as usize];
        advice.push((1u8 << remaining_bits) - 1);
        assert_eq!(
            split_frames(&advice).unwrap_err(),
            format!(
                "the frame at byte 0 states {} bytes and the advice ends first",
                usize::MAX
            )
        );
    }
}

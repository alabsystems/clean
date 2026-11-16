// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Candidate advice encoding for the untrusted C4 tracing producer.
//!
//! Encoding a journal does not establish that it replays. The Lean `kcheck`
//! checker is the only component that decides whether these bytes are advice
//! for a declaration.

use super::{wire, Token};

/// Encode one journal token in the byte format read by `KCheck.Token`.
///
/// `SpineRefl` and `SpineCerts` carry diagnostic arities in Rust. Those
/// arities are deliberately absent from the checker wire format.
#[must_use]
pub fn encode_token(token: Token) -> Vec<u8> {
    wire::encode_tokens(&[token])
}

/// Encode one declaration's finalized token journal, without a length prefix.
#[must_use]
pub fn encode_frame(tokens: &[Token]) -> Vec<u8> {
    wire::encode_tokens(tokens)
}

/// Encode declaration frames as minimal-ULEB128 byte length followed by bytes.
///
/// An empty declaration frame is represented by the single byte `0x00`.
#[must_use]
pub fn encode_frames(frames: &[Vec<u8>]) -> Vec<u8> {
    wire::encode_frames(frames)
}

#[cfg(test)]
mod tests {
    use super::{encode_frame, encode_frames, encode_token};
    use crate::kcheck_trace::Token;

    #[test]
    fn required_frame_golden() {
        assert_eq!(
            encode_frame(&[
                Token::Depth(32),
                Token::Stop,
                Token::Stop,
                Token::Stop,
                Token::Stop,
                Token::Refl,
            ]),
            [0x01, 0x20, 0x16, 0x16, 0x16, 0x16, 0x02]
        );
    }

    #[test]
    fn operands_use_minimal_unsigned_leb128() {
        assert_eq!(encode_token(Token::Depth(128)), [0x01, 0x80, 0x01]);
        assert_eq!(
            encode_token(Token::Memo(u64::MAX)),
            [0x15, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x01,]
        );
    }

    #[test]
    fn every_tag_matches_the_lean_decoder() {
        let cases = [
            (Token::Depth(7), vec![0x01, 0x07]),
            (Token::Refl, vec![0x02]),
            (Token::Sort, vec![0x03]),
            (Token::Const, vec![0x04]),
            (Token::App, vec![0x05]),
            (Token::Lam, vec![0x06]),
            (Token::Pi, vec![0x07]),
            (Token::CoreL(8), vec![0x08, 0x08]),
            (Token::CoreR(9), vec![0x09, 0x09]),
            (Token::Dom, vec![0x0a]),
            (Token::Iota, vec![0x0b]),
            (Token::K, vec![0x0c]),
            (Token::SpineRefl(5), vec![0x0d]),
            (Token::SpineCerts(6), vec![0x0e]),
            (Token::DeltaL, vec![0x0f]),
            (Token::DeltaR, vec![0x10]),
            (Token::DeltaBoth, vec![0x11]),
            (Token::EtaL, vec![0x12]),
            (Token::EtaR, vec![0x13]),
            (Token::Irrel, vec![0x14]),
            (Token::Memo(21), vec![0x15, 0x15]),
            (Token::Stop, vec![0x16]),
        ];
        for (token, expected) in cases {
            assert_eq!(encode_token(token), expected, "{token:?}");
        }
    }

    #[test]
    fn frames_include_empty_and_multibyte_lengths() {
        let long = vec![0x5a; 128];
        let encoded = encode_frames(&[Vec::new(), vec![0xaa, 0xbb], long.clone()]);
        assert_eq!(&encoded[..4], &[0x00, 0x02, 0xaa, 0xbb]);
        assert_eq!(&encoded[4..6], &[0x80, 0x01]);
        assert_eq!(&encoded[6..], long);
    }
}

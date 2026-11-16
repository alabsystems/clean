// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Untrusted producer of the adopted checker's token and frame bytes.
//!
//! Encoding a diagnostic journal does not make it valid declaration advice.
//! Only the adopted checker decides whether these bytes justify its input.
//! In particular, the tracer journal's rule order is not repaired here.
use super::Token;

fn append_nat(mut value: u128, output: &mut Vec<u8>) {
    loop {
        let digit = (value & 0x7f) as u8;
        value >>= 7;
        output.push(if value == 0 { digit } else { digit | 0x80 });
        if value == 0 {
            break;
        }
    }
}

/// Encode token syntax as specified by `KCheck.Token.encode`.
///
/// Telescope arities are diagnostic metadata in the Rust tokens. The adopted
/// `SPINE_REFL` and `SPINE` tags have no operand; the checker reads its actual
/// telescope. This function performs no checking or authority admission.
pub fn encode_tokens(tokens: &[Token]) -> Vec<u8> {
    let mut bytes = Vec::new();
    for token in tokens {
        let (tag, operand) = match *token {
            Token::Depth(n) => (0x01, Some(n)),
            Token::Refl => (0x02, None),
            Token::Sort => (0x03, None),
            Token::Const => (0x04, None),
            Token::App => (0x05, None),
            Token::Lam => (0x06, None),
            Token::Pi => (0x07, None),
            Token::CoreL(n) => (0x08, Some(n)),
            Token::CoreR(n) => (0x09, Some(n)),
            Token::Dom => (0x0a, None),
            Token::Iota => (0x0b, None),
            Token::K => (0x0c, None),
            Token::SpineRefl(_) => (0x0d, None),
            Token::SpineCerts(_) => (0x0e, None),
            Token::DeltaL => (0x0f, None),
            Token::DeltaR => (0x10, None),
            Token::DeltaBoth => (0x11, None),
            Token::EtaL => (0x12, None),
            Token::EtaR => (0x13, None),
            Token::Irrel => (0x14, None),
            Token::Memo(n) => (0x15, Some(n)),
            Token::Stop => (0x16, None),
        };
        bytes.push(tag);
        if let Some(value) = operand {
            append_nat(u128::from(value), &mut bytes);
        }
    }
    bytes
}

/// Prefix each declaration's bytes with its minimal unsigned LEB128 length.
/// The checker, not this producer, enforces frame count, token consumption,
/// declaration scope, validity and depth. Empty frames are preserved.
pub fn encode_frames(frames: &[Vec<u8>]) -> Vec<u8> {
    let mut bytes = Vec::new();
    for frame in frames {
        append_nat(frame.len() as u128, &mut bytes);
        bytes.extend_from_slice(frame);
    }
    bytes
}

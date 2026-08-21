// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Errors of the A2 mint pipeline. Every one of them is a REFUSAL: the
//! pipeline is total-or-refusing by construction, so nothing here is a
//! recoverable "best effort" state.

/// A malformed core module, or a construct with no image in the Clean fragment.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum CoreError {
    /// The S-expression does not have the shape the core grammar requires.
    #[error("core module shape: {0}")]
    Shape(String),
    /// A construct the Clean `IRModule` fragment cannot encode. Refused, never
    /// approximated.
    #[error("no Clean image: {0}")]
    NoImage(String),
    /// A reader could not witness a field the minter needs.
    #[error("unwitnessed field `{0}`: the emitted text never prints it, so this reader cannot supply it")]
    Unwitnessed(String),
}

/// A refusal from the emitted-trust-ir reader.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum EmittedError {
    /// The fixture text does not have the shape trust-ir's printer emits.
    #[error("emitted trust-ir at line {line}: {msg}")]
    Syntax {
        /// 1-based line number in the fixture.
        line: usize,
        /// What was expected.
        msg: String,
    },
    /// A construct with no Clean image.
    #[error("emitted trust-ir at line {line}: {source}")]
    Core {
        /// 1-based line number in the fixture.
        line: usize,
        /// The underlying refusal.
        #[source]
        source: CoreError,
    },
}

/// A refusal from the minter.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum MintError {
    /// The core module is malformed or outside the fragment.
    #[error(transparent)]
    Core(#[from] CoreError),
    /// A numeral with no atom in the registered `ir_dN` pool.
    #[error("numeral {0} is outside the registered ir_d0..ir_d16 atom pool; minting it would need a pool entry this change does not add")]
    Numeral(u128),
}

/// A refusal from the kernel-term decoder.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum DecodeError {
    /// The named constant is absent from the specification environment.
    #[error("`{0}` is not a constant of the specification environment")]
    Missing(String),
    /// The constant has no value (an axiom or an opaque).
    #[error("`{0}` has no value to decode")]
    NoValue(String),
    /// The delta-normalized term is not the constructor application the
    /// decoder's shape table requires. Fail-closed: there is no default arm.
    #[error("decoding {at}: {msg}")]
    Shape {
        /// Where in the term the decoder was.
        at: String,
        /// What was expected and what was found.
        msg: String,
    },
    /// The term is well-formed but outside the encodable fragment.
    #[error(transparent)]
    Core(#[from] CoreError),
}

/// A refusal from the INTERFACE check — the artifact facts the core module
/// deliberately does not carry, compared against the chain's pinned table.
///
/// Every variant is a slot that used to be silently erased. A body that
/// differs from the pin in one of them denotes a different program and is now
/// refused rather than projected onto the same core module.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum InterfaceError {
    /// The emitted text could not be read at all.
    #[error(transparent)]
    Read(#[from] EmittedError),
    /// The header names a different function than the tag table pins.
    #[error("the artifact is `{found}`; the chain's tag table pins `{pinned}`. The core module carries no name, so nothing else in the pipeline would have noticed")]
    FunctionName {
        /// The name the tag table records.
        pinned: String,
        /// The name the `rustcc fn @…` header carries.
        found: String,
    },
    /// A pinned interface slot does not match the artifact.
    #[error("{slot}: the artifact carries [{found}]; the chain's tag table pins [{pinned}]. This slot is NOT in the core module, so it is refused here or nowhere. If the two differ only by a `#?` where the pin has `#K`, the tag table is STALE rather than the body different — re-pin it, exactly as M7 says of a re-interning")]
    Mismatch {
        /// Which slot disagreed.
        slot: String,
        /// The pinned value.
        pinned: String,
        /// The artifact's value.
        found: String,
    },
    /// A callee index the tag table does not account for.
    #[error("{0}")]
    Unpinned(String),
}

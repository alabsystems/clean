// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Serialization-format identification shared by every TrustIr tool.
//!
//! [`sniff_format`] answers ONE question from the leading bytes of a file:
//! which TrustIr transport, if any, do these bytes claim to be? It decodes
//! nothing, allocates nothing and depends on no codec feature, so the `trust-ir`
//! CLI, `trust-ir-fmt` and `trust-ir-diff` can share one spelling of the rule
//! without enabling the codecs themselves.
//!
//! A sniff is a CLAIM read off a magic number or a leading token, never a
//! verdict that the bytes decode. It exists for inputs whose extension says
//! nothing (stdin, a producer's `CRATE.trust-ir.bin`, an arbitrary file name)
//! and to catch an extension that LIES about its content. It must never
//! override a format the caller named explicitly.
//!
//! # The `tmbc` naming collision
//!
//! `.tmbc` is TrustIr's OWN binary extension (the conformance corpus'
//! `chc_batch.tmbc` carries the [`TRUST_IR_BINARY_MAGIC`]), while `tMBC` is the
//! MAGIC of trust-cg's private container ([`TRUST_CG_CONTAINER_MAGIC`]), which
//! is not a TrustIr module at all. Only the magic disambiguates the two, which
//! is why [`SniffedFormat::TrustCgContainer`] is its own answer rather than a
//! "not binary" `None`: a consumer refuses it BY NAME, whatever the extension.
//!
//! MessagePack is never sniffed. Its leading byte is an ordinary MessagePack
//! type marker that many non-TrustIr files share, so claiming it from content
//! would be a guess; it needs its extension or an explicit format.
//!
//! # Resolving a file's format
//!
//! [`resolve_module_format`] is the ONE rule every TrustIr tool (the
//! `trust-ir` CLI, `trust-ir-fmt`, `trust-ir-diff`) applies to decide which
//! decoder reads a file: an explicit format wins, a trust-cg container and a
//! `TRUST_IS` template are refused by name, a file name that resolves ([`ModuleFormat::from_path`]) is
//! cross-checked against the sniff and refused on disagreement, and a name
//! that says nothing takes the sniffed format. It is byte and name checks
//! only, like [`sniff_format`], so the tools share one spelling of it without
//! this crate enabling any codec.

use std::path::Path;

/// The 8-byte magic that opens every TrustIr binary module
/// (`trust_ir::binary::serialize_module`). The binary codec reads and writes
/// this constant, so the sniff and the codec cannot disagree about it.
pub const TRUST_IR_BINARY_MAGIC: [u8; 8] = *b"TRUST_IR";

/// The 8-byte magic that opens every TrustIr TEMPLATE blob (amendment S,
/// `trust_ir::binary::serialize_template`). A template is not a module: no
/// level-R reader accepts it, and a consumer refuses it by name.
pub const TRUST_IS_TEMPLATE_MAGIC: [u8; 8] = *b"TRUST_IS";

/// The 4-byte magic of trust-cg's own `tMBC` container (trust-cg
/// `pipeline::encode_tmbc`). NOT a TrustIr module: it wraps trust-cg's private
/// encoding and no TrustIr reader decodes it.
pub const TRUST_CG_CONTAINER_MAGIC: [u8; 4] = *b"tMBC";

/// What the leading bytes of an input claim to be.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SniffedFormat {
    /// Starts with [`TRUST_IR_BINARY_MAGIC`]: the TrustIr binary codec.
    Binary,
    /// The first non-whitespace byte is `{`: the serde JSON form.
    Json,
    /// After leading whitespace, starts with `;` (the canonical
    /// `; TrustIr text format v1` banner, or any comment) or with `module "`:
    /// the text format.
    Text,
    /// Starts with [`TRUST_CG_CONTAINER_MAGIC`]: trust-cg's own container,
    /// which is NOT a TrustIr module. Consumers refuse it by name.
    TrustCgContainer,
    /// Starts with [`TRUST_IS_TEMPLATE_MAGIC`]: a level-S template (amendment
    /// S), which is NOT a module. A module consumer refuses it by name; a
    /// template is instantiated, never decoded as a module.
    TemplateBinary,
}

impl SniffedFormat {
    /// A short human name, used in refusal messages.
    pub fn describe(self) -> &'static str {
        match self {
            SniffedFormat::Binary => "TrustIr binary (TRUST_IR magic)",
            SniffedFormat::Json => "JSON (leading '{')",
            SniffedFormat::Text => "TrustIr text (leading ';' or 'module \"')",
            SniffedFormat::TrustCgContainer => "trust-cg tMBC container (tMBC magic)",
            SniffedFormat::TemplateBinary => "TrustIr template binary (TRUST_IS magic)",
        }
    }
}

/// Identify a TrustIr transport from its leading bytes.
///
/// Byte checks only, in this order:
///
/// 1. [`TRUST_IR_BINARY_MAGIC`] prefix ⇒ [`SniffedFormat::Binary`];
/// 2. [`TRUST_CG_CONTAINER_MAGIC`] prefix ⇒ [`SniffedFormat::TrustCgContainer`],
///    and [`TRUST_IS_TEMPLATE_MAGIC`] prefix ⇒ [`SniffedFormat::TemplateBinary`];
/// 3. otherwise skip ASCII whitespace, then `{` ⇒ [`SniffedFormat::Json`], and
///    `;` or `module "` ⇒ [`SniffedFormat::Text`];
/// 4. anything else — MessagePack included, empty input included — ⇒ `None`.
///
/// The magic checks are exact prefixes (no whitespace skipping): a binary blob
/// never begins with whitespace, and a text file that happens to contain the
/// letters `TRUST_IR` after a newline is not binary.
pub fn sniff_format(bytes: &[u8]) -> Option<SniffedFormat> {
    if bytes.starts_with(&TRUST_IR_BINARY_MAGIC) {
        return Some(SniffedFormat::Binary);
    }
    if bytes.starts_with(&TRUST_CG_CONTAINER_MAGIC) {
        return Some(SniffedFormat::TrustCgContainer);
    }
    if bytes.starts_with(&TRUST_IS_TEMPLATE_MAGIC) {
        return Some(SniffedFormat::TemplateBinary);
    }
    let start = bytes.iter().position(|b| !b.is_ascii_whitespace())?;
    let rest = &bytes[start..];
    if rest.starts_with(b"{") {
        Some(SniffedFormat::Json)
    } else if rest.starts_with(b";") || rest.starts_with(b"module \"") {
        Some(SniffedFormat::Text)
    } else {
        None
    }
}

/// A TrustIr module transport, as a tool names it (`--format bin|text|json|msgpack`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ModuleFormat {
    /// The binary codec (`trust_ir::binary`, feature `binary`).
    Binary,
    /// The text format (`trust_ir::parser`, feature `parser`).
    Text,
    /// serde JSON (feature `serde`).
    Json,
    /// serde MessagePack (feature `serde`).
    Msgpack,
}

impl ModuleFormat {
    /// Every format, in `--format` value order.
    pub const ALL: [ModuleFormat; 4] = [
        ModuleFormat::Binary,
        ModuleFormat::Text,
        ModuleFormat::Json,
        ModuleFormat::Msgpack,
    ];

    /// The `--format` value naming this format.
    pub fn name(self) -> &'static str {
        match self {
            ModuleFormat::Binary => "bin",
            ModuleFormat::Text => "text",
            ModuleFormat::Json => "json",
            ModuleFormat::Msgpack => "msgpack",
        }
    }

    /// The format a `--format` value names; `None` for anything else.
    pub fn from_name(name: &str) -> Option<ModuleFormat> {
        ModuleFormat::ALL.into_iter().find(|f| f.name() == name)
    }

    /// The format a single file extension names. Returns `None` if unknown.
    ///
    /// Extension contract (matches `docs/formats.md` and the conformance
    /// corpus): `.tmbc` is the binary codec, `.trust_ir` is the canonical
    /// text format, `.json`/`.msgpack` are the serde formats. A bare `.bin` /
    /// `.txt` is deliberately NOT recognised — only the producer's full
    /// `.trust-ir.bin` / `.trust-ir.txt` suffixes are ([`Self::from_path`]).
    pub fn from_extension(ext: &str) -> Option<ModuleFormat> {
        match ext {
            "tmbc" => Some(ModuleFormat::Binary),
            "trust_ir" => Some(ModuleFormat::Text),
            "json" => Some(ModuleFormat::Json),
            "msgpack" => Some(ModuleFormat::Msgpack),
            _ => None,
        }
    }

    /// The format a path's NAME states: first the full producer suffixes
    /// trustc publishes (`CRATE.trust-ir.bin` ⇒ binary, `CRATE.trust-ir.txt`
    /// ⇒ text), then the single-extension contract of
    /// [`Self::from_extension`]. Returns `None` when the name says nothing
    /// (stdin's `-`, a bare `.bin`, any other extension).
    pub fn from_path(path: &Path) -> Option<ModuleFormat> {
        let name = path.file_name().and_then(|s| s.to_str()).unwrap_or("");
        if name.ends_with(".trust-ir.bin") {
            return Some(ModuleFormat::Binary);
        }
        if name.ends_with(".trust-ir.txt") {
            return Some(ModuleFormat::Text);
        }
        let ext = path.extension().and_then(|s| s.to_str()).unwrap_or("");
        ModuleFormat::from_extension(ext)
    }

    /// The format a content sniff claims. [`SniffedFormat::TrustCgContainer`]
    /// and [`SniffedFormat::TemplateBinary`] map to nothing: each is refused
    /// by name, never decoded as a module.
    pub fn from_sniffed(sniffed: SniffedFormat) -> Option<ModuleFormat> {
        match sniffed {
            SniffedFormat::Binary => Some(ModuleFormat::Binary),
            SniffedFormat::Json => Some(ModuleFormat::Json),
            SniffedFormat::Text => Some(ModuleFormat::Text),
            SniffedFormat::TrustCgContainer | SniffedFormat::TemplateBinary => None,
        }
    }
}

/// Why [`resolve_module_format`] refused to name a decoder. Its `Display` is
/// the refusal message every tool prints, the path included.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FormatRefusal {
    /// The content carries trust-cg's `tMBC` magic, whatever the name says.
    TrustCgContainer {
        /// The input as the caller named it.
        path: String,
    },
    /// The content carries the `TRUST_IS` template magic (amendment S),
    /// whatever the name says: a template is instantiated by its consumer,
    /// never read as a module.
    TemplateBinary {
        /// The input as the caller named it.
        path: String,
    },
    /// The name states one format and the content claims another — or the
    /// name says binary and the content lacks the `TRUST_IR` magic.
    NameContradictsContent {
        /// The input as the caller named it.
        path: String,
        /// What the name states.
        named: ModuleFormat,
        /// What the content claims (`None`: no recognised claim).
        sniffed: Option<SniffedFormat>,
    },
    /// Neither the name nor the content states a format.
    Undetectable {
        /// The input as the caller named it.
        path: String,
        /// The path's extension (`""` when it has none).
        extension: String,
    },
}

impl core::fmt::Display for FormatRefusal {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            FormatRefusal::TrustCgContainer { path } => write!(
                f,
                "{path}: this is a trust-cg tMBC container, not a trust-ir module (trust-cg's own \
                 container codec, `encode_tmbc`, writes it; use the TRUST_IR binary)"
            ),
            FormatRefusal::TemplateBinary { path } => write!(
                f,
                "{path}: this is a trust-ir TEMPLATE (TRUST_IS magic, amendment S), not a module; \
                 a template is instantiated by its consumer, never read as a module"
            ),
            FormatRefusal::NameContradictsContent {
                path,
                named,
                sniffed,
            } => write!(
                f,
                "{path}: the file name says {} but the content says {}; refusing to guess — fix \
                 the name or pass --format explicitly",
                named.name(),
                sniffed.map_or("no recognised TrustIr format (no TRUST_IR magic)", |s| {
                    s.describe()
                }),
            ),
            FormatRefusal::Undetectable { path, extension } => write!(
                f,
                "cannot auto-detect format for {path}: unknown extension {extension:?} and the \
                 content carries no TRUST_IR magic, leading '{{', ';' or 'module \"' (MessagePack \
                 is never sniffed); pass --format explicitly"
            ),
        }
    }
}

impl std::error::Error for FormatRefusal {}

/// Resolve which decoder reads `bytes`, read from `path`.
///
/// Order, and none of it is a fall-through:
///
/// 1. an `explicit` format wins and is NEVER second-guessed by a sniff;
/// 2. a trust-cg `tMBC` container is refused by name under ANY extension
///    (`.tmbc` included — the extension is TrustIr's own, the magic is
///    trust-cg's, and only the magic tells them apart), and a `TRUST_IS`
///    template (amendment S) is refused by name the same way;
/// 3. a name that resolves ([`ModuleFormat::from_path`]) is used — unless the
///    content claims a DIFFERENT format ([`sniff_format`]), or the name says
///    binary and the content lacks the `TRUST_IR` magic; both are refused
///    naming the two claims;
/// 4. a name that says nothing (stdin, `.bin`, any other extension) takes the
///    sniffed format. MessagePack is never sniffed, so it is
///    [`FormatRefusal::Undetectable`] without its extension.
pub fn resolve_module_format(
    explicit: Option<ModuleFormat>,
    path: &Path,
    bytes: &[u8],
) -> Result<ModuleFormat, FormatRefusal> {
    if let Some(format) = explicit {
        return Ok(format);
    }
    let shown = || path.display().to_string();
    let sniffed = sniff_format(bytes);
    if sniffed == Some(SniffedFormat::TrustCgContainer) {
        return Err(FormatRefusal::TrustCgContainer { path: shown() });
    }
    if sniffed == Some(SniffedFormat::TemplateBinary) {
        return Err(FormatRefusal::TemplateBinary { path: shown() });
    }
    let by_content = sniffed.and_then(ModuleFormat::from_sniffed);
    match ModuleFormat::from_path(path) {
        Some(named) => {
            let disagrees = match by_content {
                Some(content) => content != named,
                // Only the binary codec has a mandatory magic; a text, JSON
                // or MessagePack file the sniff cannot place is left to its
                // decoder.
                None => named == ModuleFormat::Binary,
            };
            if disagrees {
                return Err(FormatRefusal::NameContradictsContent {
                    path: shown(),
                    named,
                    sniffed,
                });
            }
            Ok(named)
        }
        None => by_content.ok_or_else(|| FormatRefusal::Undetectable {
            path: shown(),
            extension: path
                .extension()
                .and_then(|s| s.to_str())
                .unwrap_or("")
                .to_string(),
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn magic_constants_are_the_codec_spellings() {
        assert_eq!(&TRUST_IR_BINARY_MAGIC, b"TRUST_IR");
        assert_eq!(&TRUST_CG_CONTAINER_MAGIC, b"tMBC");
    }

    #[test]
    fn prefix_rules() {
        assert_eq!(
            sniff_format(b"TRUST_IR\x26\0\0\0"),
            Some(SniffedFormat::Binary)
        );
        assert_eq!(
            sniff_format(b"tMBC\x01\0\0\0"),
            Some(SniffedFormat::TrustCgContainer)
        );
        assert_eq!(sniff_format(b"  \n{\"name\":1}"), Some(SniffedFormat::Json));
        assert_eq!(
            sniff_format(b"; TrustIr text format v1\n"),
            Some(SniffedFormat::Text)
        );
        assert_eq!(sniff_format(b"\nmodule \"m\"\n"), Some(SniffedFormat::Text));
        // A magic is an exact prefix: whitespace before it is not binary.
        assert_eq!(sniff_format(b" TRUST_IR"), None);
        // `module` without the quoted name is not the text header.
        assert_eq!(sniff_format(b"modules"), None);
        assert_eq!(sniff_format(b""), None);
        assert_eq!(sniff_format(b" \n\t"), None);
        // MessagePack is never sniffed.
        assert_eq!(sniff_format(&[0xdc, 0x00, 0x13]), None);
    }
}

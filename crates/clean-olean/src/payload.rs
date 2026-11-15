// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! clean-specific payload attached to .olean files.
//!
//! We append a small trailer to .olean files we generate to carry the actual
//! kernel objects serialized with `bincode`. This avoids having to fully
//! replicate Lean 4's ConstantInfo layout while still enabling dependent
//! modules to load and reuse definitions.

use crate::error::{OleanError, OleanResult};
use clean_kernel::env::ConstantInfo;
use clean_kernel::inductive::{ConstructorVal, InductiveVal, RecursorVal};
use clean_kernel::name::Name;
use serde::{Deserialize, Serialize};
use std::mem::size_of;

/// Magic footer identifying clean payloads.
pub const CLEAN_PAYLOAD_MAGIC: &[u8; 8] = b"CLEANENV";
/// Version of the clean payload format.
/// Version 2 added the `protected` / `private` marks: a version-1 artifact
/// lost them, so an importer resolved `open N; w` to a protected `N.w` and
/// named another module's `private` declaration (Lean 4.8.0 rejects both).
/// Version 3 added the module's type classes, instance entries, `export`
/// aliases and registered namespaces: a version-2 artifact carried none of
/// them, so an importer resolved no instance of an imported class at all and
/// did not know the module's aliases (round-25 verification: `clean lake
/// build` refused `attribute [instance] ib` on an imported instance that
/// `clean check` and Lean 4.8.0 accept). An older artifact is refused rather
/// than read without them.
/// Version 4 carries Lean's module-local names for `private` declarations
/// (`_private.<module>.0.<name>`, G21 brick B4): a version-3 artifact holds
/// them under their plain names, which two sibling modules could share and
/// which no longer match what `clean check` mints for the same source.
/// Version 5 carries the module's `@[implemented_by]` and `@[extern]`
/// bindings (`docs/DECISIONS.md` R149): a version-4 artifact carried none, so
/// a program importing it compiled the logical body where Lean runs the
/// implementation (measured: `implSlow 1` printed `3` at exit 0 through a
/// Clean-built `.olean`; pinned Lean prints `2`). It also carries the
/// module's own ORDER rows (`implemented_by_order`): without them a late
/// `attribute [implemented_by]` in the imported module was invisible to the
/// importer, which compiled the module's earlier code against the binding
/// (measured: `lateCaller 1` printed `20` at exit 0; pinned Lean prints `30`).
// Version 6 carries compiler-body csimp snapshots. Version 5 cannot preserve
// replacement choices across imports and must be rebuilt rather than guessed.
// Version 7 additionally preserves definition exposure for exporting attribute
// validation; version 6 lacks that source visibility contract.
pub const CLEAN_PAYLOAD_VERSION: u32 = 7;

/// Serialized kernel data embedded in a clean-generated `.olean`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct CleanPayload {
    pub constants: Vec<ConstantInfo>,
    pub inductives: Vec<InductiveVal>,
    pub constructors: Vec<ConstructorVal>,
    pub recursors: Vec<RecursorVal>,
    pub structure_fields: Vec<(Name, Vec<Name>)>,
    /// The payload's own declarations marked `protected` (Lean's
    /// `protectedExt`): an atomic name never reaches them through a
    /// namespace prefix or a simple `open`.
    pub protected_decls: Vec<Name>,
    /// The payload's own declarations marked `private`: module-local, so no
    /// importer may name them (Lean mangles them per module).
    pub private_decls: Vec<Name>,
    /// Type classes the module registered (Lean's `classExtension` entries).
    pub classes: Vec<clean_kernel::env::KernelClassInfo>,
    /// The module's exported GLOBAL entries of Lean's instance extension
    /// (`Lean.Meta.instanceExtension`), by their effect on an importer's
    /// replay: every instance the module gave a global entry, in the order
    /// of its first one, at the priority of its last (an importer re-inserts
    /// an instance it already holds in place, and pushes one it does not;
    /// only the last priority survives). Local entries and erasures are
    /// never exported.
    pub global_instances: Vec<clean_kernel::env::KernelInstanceInfo>,
    /// The module's exported SCOPED instance entries, in order: (namespace,
    /// the instance with the entry's priority).
    pub scoped_instances: Vec<(Name, clean_kernel::env::KernelInstanceInfo)>,
    /// The module's `export` aliases (Lean's `aliasExtension` entries).
    pub export_aliases: Vec<(Name, Name)>,
    /// The namespaces the module's `namespace` commands registered (Lean's
    /// `namespacesExt` entries).
    pub namespaces: Vec<Name>,
    /// The module's own `@[implemented_by]` bindings (Lean's
    /// `Lean.Compiler.implementedByAttr` entries): `(declaration, target)`.
    pub implemented_by: Vec<(Name, Name)>,
    /// The module's own `@[extern]` bindings (Lean's `Lean.externAttr`
    /// entries): `(declaration, symbol)`.
    pub externs: Vec<(Name, String)>,
    /// The module's own constants an `attribute [implemented_by]` command of
    /// the module came too late for (`clean_kernel::env::CompiledBefore`):
    /// `(referrer, rebound, via)`. An importer adds them to its order record,
    /// so every compiled lane refuses as it does for the same command in the
    /// file it elaborates.
    pub implemented_by_order: Vec<(Name, Name, Name)>,
    /// Resolved body rules and module-global/scoped compiler registrations.
    /// These opaque bytes are Clean metadata, not raw Lean heap objects.
    pub csimp: Vec<clean_kernel::env::EnvExtensionEntry>,
    /// Source module definition exposure, independent of runtime body storage.
    pub definition_exposure: Vec<(Name, bool)>,
}

impl CleanPayload {
    /// Total number of constants represented (counts inductives/ctors/recs too).
    ///
    /// # REQUIRES
    /// - None.
    ///
    /// # ENSURES
    /// - Returns `constants.len() + inductives.len() + constructors.len() + recursors.len()`.
    /// - Deterministic for a given payload.
    pub fn total_constants(&self) -> usize {
        self.constants.len()
            + self.inductives.len()
            + self.constructors.len()
            + self.recursors.len()
    }

    /// Every name this payload declares: its constants and its inductive
    /// families' members.
    #[must_use]
    pub(crate) fn declared_names<S: FromIterator<Name>>(&self) -> S {
        self.constants
            .iter()
            .map(|c| c.name.clone())
            .chain(self.inductives.iter().map(|i| i.name.clone()))
            .chain(self.constructors.iter().map(|c| c.name.clone()))
            .chain(self.recursors.iter().map(|r| r.name.clone()))
            .collect()
    }

    /// A name this payload declares more than once — across its constants,
    /// inductives, constructors and recursors (one namespace, as in the
    /// kernel), or twice in its structure-field tables — with what it is.
    ///
    /// Clean's own builder never writes one (`clean-lake` `build.rs` collects
    /// each name once, and leaves the inductive families out of `constants`).
    /// A payload that has one says two things about one name and gives no
    /// rule for choosing: before module-trust round 28 the loader inserted
    /// both and the LATER one won silently (`V0.v := 0` then `V0.v := 1`
    /// appended made `V0.v = 1` pass).
    #[must_use]
    pub(crate) fn duplicate_declaration(&self) -> Option<(Name, &'static str)> {
        let mut seen = std::collections::HashSet::with_capacity(self.total_constants());
        let names = self
            .constants
            .iter()
            .map(|c| &c.name)
            .chain(self.inductives.iter().map(|i| &i.name))
            .chain(self.constructors.iter().map(|c| &c.name))
            .chain(self.recursors.iter().map(|r| &r.name));
        for name in names {
            if !seen.insert(name) {
                return Some((name.clone(), "declaration"));
            }
        }
        let mut tables = std::collections::HashSet::with_capacity(self.structure_fields.len());
        for (name, _) in &self.structure_fields {
            if !tables.insert(name) {
                return Some((name.clone(), "structure field table"));
            }
        }
        None
    }
}

/// Encode a payload and append a footer for easy detection.
///
/// # REQUIRES
/// - `payload` must be a valid `CleanPayload` (no internal invariants violated).
///
/// # ENSURES
/// - Output bytes end with `CLEAN_PAYLOAD_MAGIC`, `CLEAN_PAYLOAD_VERSION`,
///   and the serialized payload length (u64, little-endian).
/// - Returns `OleanError::Serialization` if `bincode` serialization fails.
/// - Deterministic: same payload yields identical output bytes.
pub fn encode_clean_payload(payload: &CleanPayload) -> OleanResult<Vec<u8>> {
    let data =
        bincode::serde::encode_to_vec(payload, bincode::config::standard()).map_err(|e| {
            OleanError::Serialization(format!("failed to serialize clean payload: {e}"))
        })?;

    let mut out = Vec::with_capacity(data.len() + CLEAN_PAYLOAD_MAGIC.len() + size_of::<u32>() + 8);
    out.extend_from_slice(&data);
    out.extend_from_slice(CLEAN_PAYLOAD_MAGIC);
    out.extend_from_slice(&CLEAN_PAYLOAD_VERSION.to_le_bytes());
    out.extend_from_slice(&(data.len() as u64).to_le_bytes());
    Ok(out)
}

/// Attempt to decode a clean payload from the end of the provided bytes.
///
/// Returns `Ok(None)` if no payload footer is present.
///
/// # REQUIRES
/// - `bytes` must be the full .olean bytes (payload detection relies on the tail).
///
/// # ENSURES
/// - Returns `Ok(None)` when the footer magic is absent.
/// - Returns `Err(OleanError::UnsupportedPayloadVersion { .. })` on version mismatch.
/// - Returns `Err(OleanError::InvalidPayload(_))` on malformed footer or length.
/// - Returns `Ok(Some(payload))` when a valid payload is present and deserializes.
pub fn decode_clean_payload(bytes: &[u8]) -> OleanResult<Option<CleanPayload>> {
    let trailer_len = CLEAN_PAYLOAD_MAGIC.len() + size_of::<u32>() + 8;
    if bytes.len() < trailer_len {
        return Ok(None);
    }

    let len_offset = bytes.len() - 8;
    let version_offset = len_offset - size_of::<u32>();
    let magic_offset = version_offset - CLEAN_PAYLOAD_MAGIC.len();

    if &bytes[magic_offset..version_offset] != CLEAN_PAYLOAD_MAGIC {
        return Ok(None);
    }

    let version = u32::from_le_bytes(
        bytes[version_offset..len_offset]
            .try_into()
            .map_err(|_| OleanError::InvalidPayload("truncated payload footer".into()))?,
    );
    if version != CLEAN_PAYLOAD_VERSION {
        return Err(OleanError::UnsupportedPayloadVersion {
            expected: CLEAN_PAYLOAD_VERSION,
            actual: version,
        });
    }

    let payload_len = u64::from_le_bytes(
        bytes[len_offset..]
            .try_into()
            .map_err(|_| OleanError::InvalidPayload("truncated payload length".into()))?,
    ) as usize;
    if payload_len > magic_offset {
        return Err(OleanError::InvalidPayload(format!(
            "payload length {} exceeds available bytes {}",
            payload_len,
            bytes.len()
        )));
    }
    let start = magic_offset - payload_len;
    let data = &bytes[start..magic_offset];

    // bincode 2 `standard()` config (varint, little-endian) — must match the
    // `encode_to_vec(.., standard())` used in `encode_clean_payload`. `decode_from_slice`
    // is bounded by the input slice (here precisely `payload_len` bytes) and caps
    // container pre-allocation to the remaining input, so a tiny malformed input cannot
    // trigger the multi-GB allocation that motivated the old `with_limit` guard (#2421).
    let (payload, _consumed): (CleanPayload, usize) =
        bincode::serde::decode_from_slice(data, bincode::config::standard()).map_err(|e| {
            OleanError::Serialization(format!("failed to deserialize clean payload: {e}"))
        })?;

    Ok(Some(payload))
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::expr::Expr;

    #[test]
    fn encode_decode_roundtrip() {
        let payload = CleanPayload {
            constants: vec![],
            inductives: vec![],
            constructors: vec![],
            recursors: vec![],
            structure_fields: vec![],
            protected_decls: vec![],
            private_decls: vec![],
            ..CleanPayload::default()
        };

        let encoded = encode_clean_payload(&payload).expect("encode");
        let decoded = decode_clean_payload(&encoded)
            .expect("decode result")
            .expect("payload missing");

        assert_eq!(decoded.total_constants(), 0);
    }

    fn def(name: &str, value: u64) -> ConstantInfo {
        ConstantInfo::new(
            Name::from_string(name),
            vec![],
            Expr::const_str("Nat"),
            Some(Expr::nat_lit(value)),
            true,
        )
    }

    #[test]
    fn a_name_declared_twice_is_a_duplicate_declaration() {
        // Module-trust round 28, Y5: the honest `V0.v := 0`, then `V0.v := 1`
        // appended.
        let mut payload = CleanPayload {
            constants: vec![def("V0.v", 0), def("V0.w", 0)],
            ..CleanPayload::default()
        };
        assert_eq!(payload.duplicate_declaration(), None);
        payload.constants.push(def("V0.v", 1));
        assert_eq!(
            payload.duplicate_declaration(),
            Some((Name::from_string("V0.v"), "declaration"))
        );
        // Order does not matter (Y5b prepends).
        payload.constants.rotate_right(1);
        assert!(payload.duplicate_declaration().is_some());
    }

    #[test]
    fn a_structure_table_given_twice_is_a_duplicate() {
        let payload = CleanPayload {
            structure_fields: vec![
                (Name::from_string("P"), vec![Name::from_string("x")]),
                (Name::from_string("P"), vec![Name::from_string("y")]),
            ],
            ..CleanPayload::default()
        };
        assert_eq!(
            payload.duplicate_declaration(),
            Some((Name::from_string("P"), "structure field table"))
        );
    }

    #[test]
    fn decode_absent_payload_returns_none() {
        let bytes = vec![0u8; 16];
        let decoded = decode_clean_payload(&bytes).unwrap();
        assert!(
            decoded.is_none(),
            "zero-filled bytes should decode to None (absent payload)"
        );
    }

    /// Roundtrip with non-empty data to verify that `bincode::serde::encode_to_vec(, bincode::config::standard())`
    /// (encode) and `DefaultOptions::new().deserialize()` (decode) use
    /// compatible encoding formats.
    #[test]
    fn encode_decode_roundtrip_nonempty() {
        let payload = CleanPayload {
            constants: vec![],
            inductives: vec![],
            constructors: vec![],
            recursors: vec![],
            structure_fields: vec![
                (
                    Name::from_string("Foo"),
                    vec![Name::from_string("x"), Name::from_string("y")],
                ),
                (Name::from_string("Bar"), vec![Name::from_string("z")]),
            ],
            protected_decls: vec![Name::from_string("Foo.x")],
            private_decls: vec![Name::from_string("Bar.z")],
            classes: vec![clean_kernel::env::KernelClassInfo {
                name: Name::from_string("C"),
                num_params: 0,
                out_params: vec![],
                semi_out_params: vec![],
            }],
            global_instances: vec![clean_kernel::env::KernelInstanceInfo {
                name: Name::from_string("ib"),
                class_name: Name::from_string("C"),
                priority: 1000,
                type_: None,
                value: None,
            }],
            scoped_instances: vec![(
                Name::from_string("N"),
                clean_kernel::env::KernelInstanceInfo {
                    name: Name::from_string("N.i"),
                    class_name: Name::from_string("C"),
                    priority: 100,
                    type_: None,
                    value: None,
                },
            )],
            export_aliases: vec![(Name::from_string("x"), Name::from_string("N.x"))],
            namespaces: vec![Name::from_string("N")],
            implemented_by: vec![(Name::from_string("slow"), Name::from_string("fast"))],
            externs: vec![(Name::from_string("ext"), "clean_sym".to_owned())],
            implemented_by_order: vec![(
                Name::from_string("caller"),
                Name::from_string("slow"),
                Name::from_string("slow"),
            )],
            csimp: vec![],
            definition_exposure: vec![],
        };

        let encoded = encode_clean_payload(&payload).expect("encode");
        let decoded = decode_clean_payload(&encoded)
            .expect("decode result")
            .expect("payload missing");

        assert_eq!(decoded.structure_fields.len(), 2);
        assert_eq!(decoded.structure_fields[0].0, Name::from_string("Foo"));
        assert_eq!(decoded.structure_fields[0].1.len(), 2);
        assert_eq!(decoded.structure_fields[1].0, Name::from_string("Bar"));
        assert_eq!(decoded.structure_fields[1].1.len(), 1);
        assert_eq!(decoded.protected_decls, vec![Name::from_string("Foo.x")]);
        assert_eq!(decoded.private_decls, vec![Name::from_string("Bar.z")]);
        assert_eq!(decoded.classes, payload.classes);
        assert_eq!(decoded.global_instances, payload.global_instances);
        assert_eq!(decoded.scoped_instances, payload.scoped_instances);
        assert_eq!(decoded.export_aliases, payload.export_aliases);
        assert_eq!(decoded.namespaces, payload.namespaces);
        assert_eq!(decoded.implemented_by, payload.implemented_by);
        assert_eq!(decoded.externs, payload.externs);
        assert_eq!(decoded.implemented_by_order, payload.implemented_by_order);
    }

    /// A payload written before private names were mangled (version 3), or
    /// before compiler bindings travelled (version 4), is refused, never read
    /// without them.
    #[test]
    fn test_decode_older_payload_versions_are_refused() {
        for old in [3u32, 4, 5, 6] {
            let payload = CleanPayload::default();
            let mut bytes = encode_clean_payload(&payload).expect("encode");
            let version_offset = bytes.len() - 8 - size_of::<u32>();
            bytes[version_offset..version_offset + size_of::<u32>()]
                .copy_from_slice(&old.to_le_bytes());
            let err =
                decode_clean_payload(&bytes).expect_err("an older payload version must be refused");
            assert!(
                matches!(
                    err,
                    OleanError::UnsupportedPayloadVersion { expected: 7, actual }
                        if actual == old
                ),
                "{err:?}"
            );
        }
    }

    /// Regression test for #2421: a malformed payload with an enormous length
    /// prefix inside the bincode data must return an error, not OOM.
    #[test]
    fn decode_malformed_huge_length_prefix_returns_error() {
        // Build a minimal valid footer that points to a small payload region
        // whose bincode content encodes a Vec length of u64::MAX.
        //
        // Vec<T> in bincode (fixint) is: u64 length, then T elements.
        // We craft a buffer where the length prefix is huge but the buffer is tiny.
        let huge_len: u64 = u64::MAX;
        let fake_payload = huge_len.to_le_bytes(); // 8 bytes claiming huge vec

        let mut bytes = Vec::new();
        bytes.extend_from_slice(&fake_payload);
        bytes.extend_from_slice(CLEAN_PAYLOAD_MAGIC);
        bytes.extend_from_slice(&CLEAN_PAYLOAD_VERSION.to_le_bytes());
        bytes.extend_from_slice(&(fake_payload.len() as u64).to_le_bytes());

        let result = decode_clean_payload(&bytes);
        assert!(
            result.is_err(),
            "huge length prefix must error, not OOM: {result:?}"
        );
    }
}

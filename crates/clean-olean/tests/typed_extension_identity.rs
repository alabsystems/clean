// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Direct byte-loader controls, not import authority or proof validation.
use clean_kernel::env::{
    AttrExtEntry, Environment, InstanceExtEntry, KernelClassInfo, KernelInstanceInfo,
    PersistentExtEntry,
};
use clean_kernel::name::NameInner;
use clean_kernel::{Declaration, Expr, Level, Name};
use clean_olean::{load_olean_file, LoadSummary};
use std::io::Write;

const BASE: u64 = 0x10000;
const LEAN_ALIAS_EXTENSION: &str = "Lean.aliasExtension";
const LEAN_CLASS_EXTENSION: &str = "Lean.classExtension";
const LEAN_INSTANCE_EXTENSION: &str = "Lean.Meta.instanceExtension";
const LEAN_SIMP_EXTENSION: &str = "Lean.Meta.simpExtension";

/// The githash at `range` of the tracked fixture `rel`: a header identity a
/// Lean world of `crates/clean-olean/lean_worlds.tsv` carries, so the loader's
/// world gate admits these synthetic parts and the refusals below stay the
/// ones each test is about.
fn measured_githash(rel: &str, range: std::ops::Range<usize>) -> Vec<u8> {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/olean")
        .join(rel);
    std::fs::read(&path).expect("tracked fixture")[range].to_vec()
}

/// The pinned build's (v4.30.0-rc2, flags 0x01) githash.
fn pinned_githash() -> Vec<u8> {
    measured_githash("v4.30.0/closure_cache/Init.olean", 40..80)
}

/// Lean v4.13.0's githash (a v1 header).
fn v4_13_githash() -> Vec<u8> {
    measured_githash("v4.13.0/custom/Minimal.olean", 6..46)
}

struct Raw {
    bytes: Vec<u8>,
    legacy: bool,
    root: u64,
}
impl Raw {
    fn new(legacy: bool) -> Self {
        let mut bytes = vec![0; if legacy { 64 } else { 96 }];
        bytes[..5].copy_from_slice(b"olean");
        let slot = if legacy {
            bytes[5] = 1;
            bytes[6..46].fill(b'a');
            bytes[48..56].copy_from_slice(&BASE.to_le_bytes());
            56
        } else {
            bytes[5] = 2;
            bytes[6] = 1;
            bytes[7..17].copy_from_slice(b"4.30.0-rc2");
            bytes[40..80].copy_from_slice(&pinned_githash());
            bytes[80..88].copy_from_slice(&BASE.to_le_bytes());
            88
        };
        let mut raw = Self {
            bytes,
            legacy,
            root: 0,
        };
        let empty = raw.array(&[]);
        raw.root = raw.object(0, &[empty; 5], if legacy { &[] } else { &[0; 8] });
        raw.bytes[slot..slot + 8].copy_from_slice(&raw.root.to_le_bytes());
        raw
    }
    fn header(&mut self, tag: u8, fields: u8, size: u16) -> u64 {
        while !self.bytes.len().is_multiple_of(8) {
            self.bytes.push(0);
        }
        let pointer = BASE + self.bytes.len() as u64;
        self.bytes.extend_from_slice(&[0; 4]);
        self.bytes.extend_from_slice(&size.to_le_bytes());
        self.bytes.extend_from_slice(&[fields, tag]);
        pointer
    }
    fn object(&mut self, tag: u8, fields: &[u64], scalars: &[u8]) -> u64 {
        let size = (8 + fields.len() * 8 + scalars.len() + 7) & !7;
        let pointer = self.header(
            tag,
            fields.len() as u8,
            if self.legacy { 0 } else { size as u16 },
        );
        for field in fields {
            self.bytes.extend_from_slice(&field.to_le_bytes());
        }
        self.bytes.extend_from_slice(scalars);
        while self.bytes.len() < (pointer - BASE) as usize + size {
            self.bytes.push(0);
        }
        pointer
    }
    fn array(&mut self, values: &[u64]) -> u64 {
        let pointer = self.header(
            clean_olean::region::tags::ARRAY,
            0,
            if self.legacy { 0 } else { 1 },
        );
        self.bytes
            .extend_from_slice(&(values.len() as u64).to_le_bytes());
        self.bytes
            .extend_from_slice(&(values.len() as u64).to_le_bytes());
        for value in values {
            self.bytes.extend_from_slice(&value.to_le_bytes());
        }
        pointer
    }
    fn name(&mut self, name: &Name) -> u64 {
        match name.inner() {
            NameInner::Anon => 1,
            NameInner::Str(parent, value) => {
                let parent = self.name(parent);
                let string = self.header(clean_olean::region::tags::STRING, 0, 0);
                for value in [
                    value.len() as u64 + 1,
                    value.len() as u64 + 1,
                    value.chars().count() as u64,
                ] {
                    self.bytes.extend_from_slice(&value.to_le_bytes());
                }
                self.bytes.extend_from_slice(value.as_bytes());
                self.bytes.push(0);
                self.object(
                    1,
                    &[parent, string],
                    if self.legacy { &[] } else { &[0; 8] },
                )
            }
            NameInner::Num(parent, value) => {
                assert!(*value <= u64::MAX >> 1);
                let parent = self.name(parent);
                self.object(
                    2,
                    &[
                        parent,
                        if self.legacy {
                            *value
                        } else {
                            (value << 1) | 1
                        },
                    ],
                    if self.legacy { &[] } else { &[0; 8] },
                )
            }
        }
    }
    fn extension(&mut self, name: &Name, rows: &[u64]) -> u64 {
        let name = self.name(name);
        let rows = self.array(rows);
        self.object(0, &[name, rows], &[])
    }
    fn finish(mut self, extensions: &[u64]) -> Vec<u8> {
        let entries = self.array(extensions);
        self.word(self.root, 40, entries);
        self.bytes
    }
    fn word(&mut self, pointer: u64, relative: usize, word: u64) {
        let start = (pointer - BASE) as usize + relative;
        self.bytes[start..start + 8].copy_from_slice(&word.to_le_bytes());
    }
}

fn twins() -> Vec<Name> {
    vec![
        Name::anon().str("a.b"),
        Name::anon().str("a").str("b"),
        Name::anon().str("7"),
        Name::anon().num(7),
        Name::anon().str("07"),
    ]
}

fn add_symbol(env: &mut Environment, name: Name, ty: Expr) {
    // An explicitly assumed environment for metadata-only tests. These axioms
    // are not presented as admitted import declarations or proved statements.
    env.add_decl(Declaration::Axiom {
        name,
        level_params: vec![],
        type_: ty,
    })
    .unwrap();
}

fn load(env: &mut Environment, bytes: Vec<u8>) -> LoadSummary {
    let mut fixture = tempfile::NamedTempFile::new().unwrap();
    fixture.write_all(&bytes).unwrap();
    fixture.flush().unwrap();
    let summary = load_olean_file(env, fixture.path()).unwrap();
    for row in &summary.extension_accounting {
        assert_eq!(row.source_rows, Some(row.decoded_rows + row.undecoded_rows));
    }
    assert_eq!(
        summary.extension_undecoded_entries,
        summary
            .extension_accounting
            .iter()
            .map(|row| row.undecoded_rows + row.unresolved_targets)
            .sum::<usize>()
    );
    summary
}

fn assert_rejected(bytes: &[u8]) {
    let mut fixture = tempfile::NamedTempFile::new().unwrap();
    fixture.write_all(bytes).unwrap();
    fixture.flush().unwrap();
    assert!(load_olean_file(&mut Environment::new(), fixture.path()).is_err());
}

#[test]
fn lean_v1_payload_rows_remain_unmeasured_not_modern_or_clean_fallback() {
    let mut raw = Raw::new(false);
    let alias = Name::anon().str("quoted.alias");
    let target = Name::anon().str("quoted.target");
    let alias_ptr = raw.name(&alias);
    let target_ptr = raw.name(&target);
    let row = raw.object(0, &[alias_ptr, target_ptr], &[]);
    let extension = raw.extension(&Name::from_string(LEAN_ALIAS_EXTENSION), &[row, row]);
    let root = raw.root;
    let mut bytes = raw.finish(&[extension]);
    // Explicit v1 header and measured cs48 ModuleData. Name/Array envelopes
    // coincide here, but this control does not assert the v1 payload ABI.
    bytes[..96].fill(0);
    bytes[..5].copy_from_slice(b"olean");
    bytes[5] = 1;
    bytes[6..46].copy_from_slice(&v4_13_githash());
    bytes[48..56].copy_from_slice(&BASE.to_le_bytes());
    bytes[56..64].copy_from_slice(&root.to_le_bytes());
    let root_offset = (root - BASE) as usize;
    bytes[root_offset + 4..root_offset + 6].copy_from_slice(&48_u16.to_le_bytes());
    let mut env = Environment::new();
    add_symbol(&mut env, target, Expr::sort(Level::zero()));
    let summary = load(&mut env, bytes);
    assert_eq!(summary.extension_accounting.len(), 1);
    let accounting = &summary.extension_accounting[0];
    assert_eq!(
        accounting.extension_name,
        Name::from_string(LEAN_ALIAS_EXTENSION)
    );
    assert_eq!(accounting.source_rows, Some(2));
    assert_eq!(accounting.decoded_rows, 0);
    assert_eq!(accounting.undecoded_rows, 2);
    assert_eq!(summary.extension_undecoded_entries, 2);
    assert!(env.get_export_alias(&alias).is_none());
}

#[test]
fn direct_array_layout_and_capacity_are_not_inferred_from_payload() {
    for legacy in [false, true] {
        let raw = Raw::new(legacy);
        let root = raw.root;
        let bytes = raw.finish(&[]);
        assert_eq!(
            load(&mut Environment::new(), bytes.clone()).extension_undecoded_entries,
            0
        );
        let field = (root - BASE) as usize + 40;
        let entries = u64::from_le_bytes(bytes[field..field + 8].try_into().unwrap());
        let offset = (entries - BASE) as usize;
        for cs in [2_u16, 255, if legacy { 1 } else { 0 }] {
            let mut changed = bytes.clone();
            changed[offset + 4..offset + 6].copy_from_slice(&cs.to_le_bytes());
            assert_rejected(&changed);
        }
        for (relative, value) in [(8, 100_001_u64), (8, 1)] {
            let mut changed = bytes.clone();
            changed[offset + relative..offset + relative + 8].copy_from_slice(&value.to_le_bytes());
            assert_rejected(&changed);
        }
        for relative in [0, 6, 7] {
            let mut changed = bytes.clone();
            changed[offset + relative] = 255;
            assert_rejected(&changed);
        }
    }
}

#[test]
fn shared_array_references_cannot_amplify_unbounded_decode_work() {
    let mut raw = Raw::new(false);
    let alias = raw.name(&Name::anon().str("a"));
    let target = raw.name(&Name::anon().str("t"));
    let pair = raw.object(0, &[alias, target], &[]);
    let extension = raw.extension(&Name::from_string(LEAN_ALIAS_EXTENSION), &vec![pair; 1000]);
    assert_rejected(&raw.finish(&vec![extension; 1001]));
}

#[test]
fn direct_aliases_preserve_quoted_numeric_targets_in_both_formats() {
    for legacy in [false, true] {
        let mut raw = Raw::new(legacy);
        let mut env = Environment::new();
        let mut pairs = vec![];
        let names = twins();
        for (index, target) in names.iter().enumerate() {
            add_symbol(&mut env, target.clone(), Expr::prop());
            let alias = Name::anon().str("alias").num(index as u64);
            let a = raw.name(&alias);
            let b = raw.name(target);
            pairs.push(raw.object(0, &[a, b], &[]));
        }
        let ext = raw.extension(&Name::from_string(LEAN_ALIAS_EXTENSION), &pairs);
        let summary = load(&mut env, raw.finish(&[ext]));
        assert_eq!(summary.extension_undecoded_entries, 0);
        assert_eq!(env.export_alias_count(), names.len());
        for (index, target) in names.iter().enumerate() {
            assert_eq!(
                env.get_export_alias(&Name::anon().str("alias").num(index as u64)),
                Some(target)
            );
        }
    }
}

#[test]
fn quoted_canonical_extension_name_cannot_dispatch_as_alias_extension() {
    let mut raw = Raw::new(false);
    let mut env = Environment::new();
    let target = Name::anon().str("Target");
    add_symbol(&mut env, target.clone(), Expr::prop());
    let alias = Name::anon().str("alias");
    let a = raw.name(&alias);
    let t = raw.name(&target);
    let pair = raw.object(0, &[a, t], &[]);
    let ext = raw.extension(&Name::anon().str(LEAN_ALIAS_EXTENSION), &[pair]);
    let summary = load(&mut env, raw.finish(&[ext]));
    assert_eq!(summary.extension_undecoded_entries, 1);
    assert!(env.get_export_alias(&alias).is_none());
}

#[test]
fn direct_class_entries_preserve_all_exact_twin_targets() {
    let mut raw = Raw::new(false);
    let mut env = Environment::new();
    let mut rows = vec![];
    for name in twins() {
        add_symbol(
            &mut env,
            name.clone(),
            Expr::sort(Level::succ(Level::zero())),
        );
        let name = raw.name(&name);
        let empty = raw.array(&[]);
        rows.push(raw.object(0, &[name, empty, empty], &[]));
    }
    let ext = raw.extension(&Name::from_string(LEAN_CLASS_EXTENSION), &rows);
    assert_eq!(
        load(&mut env, raw.finish(&[ext])).extension_undecoded_entries,
        0
    );
    for name in twins() {
        assert!(env.is_class(&name), "exact target {name:?}");
    }
}

#[test]
fn direct_simp_entries_do_not_retarget_display_twins() {
    let mut raw = Raw::new(false);
    let mut env = Environment::new();
    let names = twins();
    for name in &names {
        add_symbol(&mut env, name.clone(), Expr::prop());
    }
    let name = raw.name(&names[0]);
    let unfold = raw.object(1, &[name], &[]);
    let scoped = raw.object(0, &[unfold], &[]);
    let ext = raw.extension(&Name::from_string(LEAN_SIMP_EXTENSION), &[scoped]);
    assert_eq!(
        load(&mut env, raw.finish(&[ext])).extension_undecoded_entries,
        0
    );
    assert!(env.is_simp_lemma(&names[0]));
    for name in &names[1..] {
        assert!(!env.is_simp_lemma(name), "unmentioned twin {name:?}");
    }
}

#[test]
fn direct_instance_priority_changes_only_the_exact_quoted_target() {
    let mut raw = Raw::new(false);
    let mut env = Environment::new();
    let class = Name::anon().str("TestClass");
    add_symbol(&mut env, class.clone(), Expr::prop());
    env.register_class(KernelClassInfo {
        name: class.clone(),
        num_params: 0,
        out_params: vec![],
        semi_out_params: vec![],
    });
    let names = twins();
    for name in &names {
        add_symbol(&mut env, name.clone(), Expr::const_(class.clone(), vec![]));
        env.register_instance(KernelInstanceInfo {
            name: name.clone(),
            class_name: class.clone(),
            priority: 100,
            type_: None,
            value: None,
        });
    }
    let name = raw.name(&names[0]);
    let some = raw.object(1, &[name], &[]);
    let empty = raw.array(&[]);
    let entry = raw.object(0, &[empty, 1, 2001, some, empty], &[0]);
    let scoped = raw.object(0, &[entry], &[]);
    let ext = raw.extension(&Name::from_string(LEAN_INSTANCE_EXTENSION), &[scoped]);
    assert_eq!(
        load(&mut env, raw.finish(&[ext])).extension_undecoded_entries,
        0
    );
    for instance in env.get_class_instances(&class) {
        assert_eq!(
            instance.priority,
            if instance.name == names[0] { 1000 } else { 100 }
        );
    }
    // Existing registrations adopt priority only; this increment must not
    // change the pre-existing synth-order policy while fixing exact identity.
    assert_eq!(env.get_instance_synth_order(&names[0]), None);
}

#[test]
fn malformed_alias_name_is_counted_without_losing_following_sibling() {
    let mut raw = Raw::new(false);
    let mut env = Environment::new();
    let target = Name::anon().str("Target");
    add_symbol(&mut env, target.clone(), Expr::prop());
    let target = raw.name(&target);
    let alias = raw.name(&Name::anon().str("good"));
    let malformed = raw.object(0, &[0, target], &[]);
    let good = raw.object(0, &[alias, target], &[]);
    let ext = raw.extension(&Name::from_string(LEAN_ALIAS_EXTENSION), &[malformed, good]);
    assert_eq!(
        load(&mut env, raw.finish(&[ext])).extension_undecoded_entries,
        1
    );
    assert!(env.get_export_alias(&Name::anon().str("good")).is_some());
}

#[test]
fn structural_attribute_payload_roundtrip_preserves_typed_names() {
    for name in twins() {
        let entry = AttrExtEntry {
            decl_name: Name::anon().str("owner"),
            attr_name: name,
            priority: 1000,
        };
        assert_eq!(
            AttrExtEntry::from_env_entry(&entry.to_env_entry()),
            Some(entry)
        );
    }
}

#[test]
fn structural_instance_payload_roundtrip_preserves_typed_names() {
    for name in twins() {
        let entry = InstanceExtEntry {
            instance_name: Name::anon().str("owner"),
            class_name: name.clone(),
            priority: 1000,
        };
        let roundtrip = InstanceExtEntry::from_env_entry(&entry.to_env_entry()).unwrap();
        assert_eq!(roundtrip.class_name, name);
        assert_eq!(roundtrip.priority, 1000);
    }
}

#[test]
fn malformed_versioned_payloads_do_not_fall_back_to_display_or_placeholder() {
    use clean_kernel::env::EnvExtensionEntryData;
    let entry = InstanceExtEntry {
        instance_name: Name::anon().str("instance"),
        class_name: Name::anon().str("class.dot").num(7),
        priority: 1000,
    }
    .to_env_entry();
    let EnvExtensionEntryData::Object(bytes) = &entry.data else {
        panic!("object payload required")
    };
    let mut changes = (1..bytes.len())
        .map(|n| bytes[..n].to_vec())
        .collect::<Vec<_>>();
    let mut trailing = bytes.clone();
    trailing.push(0);
    changes.push(trailing);
    for (index, value) in [(8, 255), (13, 255), (22, 255)] {
        let mut changed = bytes.clone();
        changed[index] = value;
        changes.push(changed);
    }
    for bytes in changes {
        let mut changed = entry.clone();
        changed.data = EnvExtensionEntryData::Object(bytes);
        assert!(InstanceExtEntry::from_env_entry(&changed).is_none());
        assert!(AttrExtEntry::from_env_entry(&changed).is_none());
    }
}

#[test]
fn explicitly_legacy_display_payloads_remain_compatible() {
    use clean_kernel::env::{EnvExtensionEntry, EnvExtensionEntryData};
    let name = Name::anon().str("decl.dot");
    let attr = EnvExtensionEntry {
        name: name.clone(),
        data: EnvExtensionEntryData::Object(b"simp:7".to_vec()),
    };
    assert_eq!(
        AttrExtEntry::from_env_entry(&attr),
        Some(AttrExtEntry {
            decl_name: name.clone(),
            attr_name: Name::from_string("simp"),
            priority: 7
        })
    );
    let mut bytes = 1000_u64.to_le_bytes().to_vec();
    bytes.extend_from_slice(b"Foo.Bar");
    let inst = EnvExtensionEntry {
        name: name.clone(),
        data: EnvExtensionEntryData::Object(bytes),
    };
    assert_eq!(
        InstanceExtEntry::from_env_entry(&inst),
        Some(InstanceExtEntry {
            instance_name: name,
            class_name: Name::from_string("Foo.Bar"),
            priority: 1000
        })
    );
}

const LEAN_IMPLEMENTED_BY_ATTR: &str = "Lean.Compiler.implementedByAttr";
const LEAN_EXTERN_ATTR: &str = "Lean.externAttr";

/// A modern `implementedByAttr` or `externAttr` row Clean cannot read fails
/// the module read: an unread binding would let the declaration's own body
/// compile where Lean runs another (`docs/DECISIONS.md` R149). Every other
/// table keeps such a row as `Unmeasured` (the control).
#[test]
fn test_undecodable_modern_compiler_attr_row_rejects_the_module() {
    for table in [LEAN_IMPLEMENTED_BY_ATTR, LEAN_EXTERN_ATTR] {
        let mut raw = Raw::new(false);
        let decl = raw.name(&Name::anon().str("d"));
        // One field where both tables store a `Name × _` pair.
        let row = raw.object(0, &[decl], &[]);
        let ext = raw.extension(&Name::from_string(table), &[row]);
        assert_rejected(&raw.finish(&[ext]));
    }
    // An `ExternEntry` constructor no `ExternAttrData` has.
    let mut raw = Raw::new(false);
    let decl = raw.name(&Name::anon().str("d"));
    let backend = raw.name(&Name::anon().str("all"));
    let entry = raw.object(5, &[backend], &[]);
    let list = raw.object(1, &[entry, 1], &[]);
    let row = raw.object(0, &[decl, list], &[]);
    let ext = raw.extension(&Name::from_string(LEAN_EXTERN_ATTR), &[row]);
    assert_rejected(&raw.finish(&[ext]));

    // Control: the same one-field row in the alias table is one unmeasured row.
    let mut raw = Raw::new(false);
    let decl = raw.name(&Name::anon().str("d"));
    let row = raw.object(0, &[decl], &[]);
    let ext = raw.extension(&Name::from_string(LEAN_ALIAS_EXTENSION), &[row]);
    let summary = load(&mut Environment::new(), raw.finish(&[ext]));
    assert_eq!(summary.extension_undecoded_entries, 1);
}

/// A well-formed row whose declaration the environment lacks decodes and is
/// counted unresolved; nothing is registered.
#[test]
fn test_compiler_attr_rows_for_an_absent_declaration_are_unresolved() {
    let mut raw = Raw::new(false);
    let decl = raw.name(&Name::anon().str("absent"));
    let target = raw.name(&Name::anon().str("impl"));
    let implemented_by = raw.object(0, &[decl, target], &[]);
    let by_ext = raw.extension(
        &Name::from_string(LEAN_IMPLEMENTED_BY_ATTR),
        &[implemented_by],
    );
    let opaque_entry = 7; // `ExternEntry.opaque`, `lean_box(3)`
    let list = raw.object(1, &[opaque_entry, 1], &[]);
    let extern_row = raw.object(0, &[decl, list], &[]);
    let extern_ext = raw.extension(&Name::from_string(LEAN_EXTERN_ATTR), &[extern_row]);
    let mut env = Environment::new();
    let summary = load(&mut env, raw.finish(&[by_ext, extern_ext]));
    assert_eq!(summary.extension_undecoded_entries, 2);
    for row in &summary.extension_accounting {
        assert_eq!(
            (row.decoded_rows, row.unresolved_targets),
            (1, 1),
            "{row:?}"
        );
    }
    let absent = Name::anon().str("absent");
    assert!(env.get_implemented_by(&absent).is_none());
    assert!(!env.is_extern(&absent));
}

/// `bytes` (a [`Raw::new(false)`] module whose root is `root`) rewritten
/// under the Lean v1 header and its 48-byte `ModuleData`, as
/// [`lean_v1_payload_rows_remain_unmeasured_not_modern_or_clean_fallback`]
/// builds it.
fn as_lean_v1(mut bytes: Vec<u8>, root: u64) -> Vec<u8> {
    bytes[..96].fill(0);
    bytes[..5].copy_from_slice(b"olean");
    bytes[5] = 1;
    // A measured v1 world's githash, so the loader's world gate (R81) admits
    // the part and the verdict below is the decoder's.
    bytes[6..46].copy_from_slice(&v4_13_githash());
    bytes[48..56].copy_from_slice(&BASE.to_le_bytes());
    bytes[56..64].copy_from_slice(&root.to_le_bytes());
    let root_offset = (root - BASE) as usize;
    bytes[root_offset + 4..root_offset + 6].copy_from_slice(&48_u16.to_le_bytes());
    bytes
}

/// The two compiler-attribute tables are the exception to v1's unmeasured
/// rows (`docs/DECISIONS.md` R149): a v1 row decodes, including v4.8.0's
/// two-field `ExternAttrData { arity?, entries }`, and one that does not
/// decode rejects the module as a modern one does. Before R149 every v1 row was
/// `Unmeasured`, and over a module Lean v4.8.0 compiled `implSlow 1` printed
/// `3` at exit 0 where Lean prints `2` (`compiler_attr_import_lean_v4_8_0.rs`
/// measures Lean's own rows).
#[test]
fn test_lean_v1_compiler_attr_rows_decode_or_reject_the_module() {
    let mut raw = Raw::new(false);
    let decl = raw.name(&Name::anon().str("absent"));
    let target = raw.name(&Name::anon().str("impl"));
    let implemented_by = raw.object(0, &[decl, target], &[]);
    let by_ext = raw.extension(
        &Name::from_string(LEAN_IMPLEMENTED_BY_ATTR),
        &[implemented_by],
    );
    let backend = raw.name(&Name::anon().str("all"));
    let adhoc = raw.object(0, &[backend], &[]);
    let list = raw.object(1, &[adhoc, 1], &[]);
    let data = raw.object(0, &[1, list], &[]); // `arity? := none`
    let extern_row = raw.object(0, &[decl, data], &[]);
    let extern_ext = raw.extension(&Name::from_string(LEAN_EXTERN_ATTR), &[extern_row]);
    let root = raw.root;
    let mut env = Environment::new();
    let summary = load(
        &mut env,
        as_lean_v1(raw.finish(&[by_ext, extern_ext]), root),
    );
    assert_eq!(summary.extension_accounting.len(), 2);
    for row in &summary.extension_accounting {
        assert_eq!(
            (row.decoded_rows, row.undecoded_rows, row.unresolved_targets),
            (1, 0, 1),
            "{row:?}"
        );
    }

    // Undecodable v1 rows: a one-field pair, and an `arity?` that is no
    // `Option Nat`.
    for table in [LEAN_IMPLEMENTED_BY_ATTR, LEAN_EXTERN_ATTR] {
        let mut raw = Raw::new(false);
        let decl = raw.name(&Name::anon().str("d"));
        let row = raw.object(0, &[decl], &[]);
        let ext = raw.extension(&Name::from_string(table), &[row]);
        let root = raw.root;
        assert_rejected(&as_lean_v1(raw.finish(&[ext]), root));
    }
    let mut raw = Raw::new(false);
    let decl = raw.name(&Name::anon().str("d"));
    let backend = raw.name(&Name::anon().str("all"));
    let adhoc = raw.object(0, &[backend], &[]);
    let list = raw.object(1, &[adhoc, 1], &[]);
    let arity = raw.object(2, &[1], &[]);
    let data = raw.object(0, &[arity, list], &[]);
    let row = raw.object(0, &[decl, data], &[]);
    let ext = raw.extension(&Name::from_string(LEAN_EXTERN_ATTR), &[row]);
    let root = raw.root;
    assert_rejected(&as_lean_v1(raw.finish(&[ext]), root));
}

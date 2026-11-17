// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Plants pass through the live census over the real kernel sources. They do
//! not alter files, gate tables, fingerprints or kernel acceptance behavior.

use super::roles::Role;
use super::*;

const METADATA: &[(&str, &str, Role)] = &[
    ("CARGO_PKG_VERSION", "lib.rs", Role::BuildEnvironment),
    (
        "CLENTHG1",
        "env/dag_serialization/theorem.rs",
        Role::ByteArray,
    ),
    ("L5CC", "cert/compression/types.rs", Role::ByteArray),
    ("L5CS", "cert/compression/streaming.rs", Role::ByteArray),
    ("L5FM", "flat/header.rs", Role::ByteArray),
    ("_trace", "kcheck_trace/term.rs", Role::LetBinder),
    (
        "Clean.module.definitionExposure",
        "env/exposure.rs",
        Role::ExtensionRegistry,
    ),
    ("snapshot.v1", "env/csimp.rs", Role::ExtensionEncoding),
    ("snapshot.v1", "env/csimp.rs", Role::ExtensionDecoding),
    ("𝕀", "expr/display.rs", Role::FormatString),
];

fn plant(file: &str, body: &str) -> Census {
    // The real replay roots Environment::add_decl; discovery conservatively
    // reaches every matching impl, including this in-memory planted body.
    Census::with_plant(
        file,
        &format!("\nimpl Environment {{ fn add_decl(&mut self) {{ {body} }} }}"),
    )
}

fn assert_refused(census: &Census, file: &str, literal: &str) {
    let original = std::fs::read_to_string(scan::kernel_src().join(file)).expect("plant source");
    let plant_start = scan::lex(scan::strip_inline_test_module(&original)).len();
    let sites = census.literal_sites();
    assert!(
        sites.iter().any(|((f, at), (s, role))| {
            f == file && s == literal && *role == Role::Candidate && *at >= plant_start
        }),
        "lookup {literal:?} in {file} vanished or was misclassified: {:?}",
        sites
            .iter()
            .filter(|((f, _), (s, _))| f == file && s == literal)
            .collect::<Vec<_>>()
    );
    let unclassified = census.unclassified();
    assert!(
        unclassified
            .iter()
            .any(|s| s.starts_with(&format!("{literal:?} in {file} ("))),
        "lookup {literal:?} in {file} escaped the live gate: {unclassified:?}"
    );
}

fn assert_metadata_roles(census: &Census, file: &str) {
    let sites = census.literal_sites();
    for (literal, f, role) in METADATA.iter().filter(|(_, f, _)| *f == file) {
        assert!(
            sites
                .iter()
                .any(|((site_file, _), (s, r))| site_file == f && s == literal && r == role),
            "real metadata {literal:?} in {file} lost {role:?}"
        );
    }
}

#[test]
fn metadata_roles_keep_every_original_literal_visible() {
    let census = Census::build();
    let sites = census.literal_sites();
    for (literal, file, role) in METADATA {
        assert!(
            sites
                .iter()
                .any(|((f, _), (s, r))| { f == file && s == literal && r == role }),
            "missing {role:?} occurrence of {literal:?} in {file}"
        );
        assert!(census
            .literals()
            .get(*literal)
            .is_some_and(|files| files.contains(*file)));
    }
}

#[test]
fn audited_matcher_namespace_does_not_exempt_a_lookup_in_another_source_file() {
    // The manual audit is local to the real storage implementation. It must
    // neither erase the occurrence nor become a global spelling exemption.
    assert_refused(
        &plant(
            "env/exposure.rs",
            r#"self.get_const(&Name::from_string("Clean.matcherInfo.v1"));"#,
        ),
        "env/exposure.rs",
        "Clean.matcherInfo.v1",
    );
    assert!(Census::build()
        .literal_sites()
        .iter()
        .any(|((file, _), (literal, role))| file == "env/matcher.rs"
            && literal == "Clean.matcherInfo.v1"
            && *role == Role::Candidate));
}

#[test]
fn same_spelling_lookups_and_dispatch_beside_metadata_are_refused() {
    for (literal, file, _) in METADATA {
        let body = format!(
            r#"
            let _ = self.get(&Name::from_string("{literal}"));
            if name.to_string() == "{literal}" {{ dispatch(); }}
        "#
        );
        let census = plant(file, &body);
        assert_refused(&census, file, literal);
        let candidates = census
            .literal_sites()
            .into_iter()
            .filter(|((f, _), (s, role))| f == file && s == literal && *role == Role::Candidate)
            .count();
        assert_eq!(
            candidates, 2,
            "constructor AND string dispatch must be discovered"
        );
    }
}

#[test]
fn raw_and_escaped_lookup_spellings_are_refused() {
    for (literal, file, _) in METADATA {
        let mut chars = literal.chars();
        let first = chars.next().expect("nonempty control");
        let escaped = format!("\\u{{{:x}}}{}", u32::from(first), chars.as_str());
        for spelling in [format!("r###\"{literal}\"###"), format!("\"{escaped}\"")] {
            assert_refused(
                &plant(file, &format!("self.get(&Name::from_string({spelling}));")),
                file,
                literal,
            );
        }
    }
    // Hex escapes and a Rust line continuation must not hide a candidate.
    assert_refused(
        &plant(
            "flat/header.rs",
            "self.get(&Name::from_string(\"\\x4c5\\\n  FM\"));",
        ),
        "flat/header.rs",
        "L5FM",
    );
}

#[test]
fn lookups_nested_in_metadata_consumers_are_refused() {
    for body in [
        r#"Expr::let_named(self.get(&Name::from_string("_trace")), t, v, b, false);"#,
        r#"Expr::let_named(Name::from_string("_trace"), self.get(&Name::from_string("_trace")), v, b, false);"#,
        r#"register_persistent_ext::<State>(self.get(&Name::from_string("_trace")));"#,
        r#"EnvExtensionEntry { name: self.get(&Name::from_string("_trace")), data: bytes };"#,
        r#"if entry.name == self.get(&Name::from_string("_trace")) { dispatch(); }"#,
        r#"unknown_macro!(Name::from_string("_trace"));"#,
        r#"env!(unknown_macro!(Name::from_string("_trace")));"#,
        r#"write!(f, "{}", self.get(&Name::from_string("_trace")));"#,
        r#"write!(self.get(&Name::from_string("_trace")), "{}");"#,
        r#"let mut f = String::new(); write!(f, "_trace"); self.get(&Name::from_string(&f));"#,
    ] {
        assert_refused(
            &plant("kcheck_trace/term.rs", body),
            "kcheck_trace/term.rs",
            "_trace",
        );
    }
}

#[test]
fn byte_to_name_conversions_through_arrays_aliases_and_helpers_are_refused() {
    let file = "cert/compression/types.rs";
    for spelling in ["b\"L5CC\"", "br##\"L5CC\"##", "b\"\\x4c5CC\""] {
        assert_refused(&plant(file, &format!("self.get(&Name::from_string(std::str::from_utf8({spelling}).expect(\"utf8\")));")), file, "L5CC");
        for input in ["CENSUS_BYTES", "alias", "census_bytes()"] {
            let source = format!("\nconst CENSUS_BYTES: &[u8; 4] = {spelling}; fn census_bytes() -> &'static [u8] {{ CENSUS_BYTES }} impl Environment {{ fn add_decl(&mut self) {{ let alias = CENSUS_BYTES; self.get(&Name::from_string(std::str::from_utf8({input}).expect(\"utf8\"))); }} }}");
            assert_refused(&Census::with_plant(file, &source), file, "L5CC");
            let dispatch = format!("\nconst CENSUS_BYTES: &[u8; 4] = {spelling}; fn census_bytes() -> &'static [u8] {{ CENSUS_BYTES }} impl Environment {{ fn add_decl(&mut self) {{ let alias = CENSUS_BYTES; if name.to_string() == String::from_utf8_lossy({input}) {{ dispatch(); }} }} }}");
            assert_refused(&Census::with_plant(file, &dispatch), file, "L5CC");
        }
    }
}

#[test]
fn shadowed_or_qualified_macros_cannot_claim_a_builtin_literal_role() {
    for (name, call) in [
        ("env", "env!(\"CARGO_PKG_VERSION\")"),
        ("write", "write!(f, \"CARGO_PKG_VERSION\")"),
    ] {
        let source = format!("\nmacro_rules! {name} {{ ($($t:tt)*) => {{ Name::from_string($($t)*) }} }} impl Environment {{ fn add_decl(&mut self) {{ {call}; }} }}");
        assert_refused(
            &Census::with_plant("lib.rs", &source),
            "lib.rs",
            "CARGO_PKG_VERSION",
        );
        assert_refused(
            &plant("lib.rs", &format!("custom::{call};")),
            "lib.rs",
            "CARGO_PKG_VERSION",
        );
        let imported = format!("\nmacro_rules! census_lookup {{ ($($t:tt)*) => {{ Name::from_string($($t)*) }} }} use crate::census_lookup as {name}; impl Environment {{ fn add_decl(&mut self) {{ {call}; }} }}");
        assert_refused(
            &Census::with_plant("lib.rs", &imported),
            "lib.rs",
            "CARGO_PKG_VERSION",
        );
    }
}

#[test]
fn metadata_syntax_does_not_exempt_a_computed_name_initializer() {
    for literal in ["L5FM", "CARGO_PKG_VERSION", "snapshot.v1"] {
        let source = format!("\nconst VERSION: Name = Name::from_string(\"{literal}\");");
        assert_refused(&Census::with_plant("lib.rs", &source), "lib.rs", literal);
    }
}

#[test]
fn shadowed_registry_closure_is_refused() {
    let file = "env/exposure.rs";
    let census = plant(
        file,
        r#"
        let register_persistent_ext = |key: Name| self.get_const(&key);
        let _ = register_persistent_ext(Name::from_string("Shadow.registry.lookup"));
    "#,
    );
    eprintln!(
        "registry shadow sites: {:?}",
        census
            .literal_sites()
            .into_iter()
            .filter(|(_, (s, _))| s == "Shadow.registry.lookup")
            .collect::<Vec<_>>()
    );
    assert_metadata_roles(&census, file);
    assert_refused(&census, file, "Shadow.registry.lookup");
}

#[test]
fn shadowed_binder_type_is_refused() {
    for declaration in [
        "struct Expr; impl Expr { fn let_named(key: Name, env: &Environment, _: (), _: (), _: bool) { let _ = env.get_const(&key); } }",
        "use self::census_shadow::Binder as Expr;",
        "type Expr = census_shadow::Binder;",
        "macro_rules! shadow_binder { () => { use self::census_shadow::Binder as Expr; }; } shadow_binder!();",
        "use self::census_shadow::Binder as r#Expr;",
    ] {
        let source = format!(r#"
            mod census_shadow {{ pub struct Binder; impl Binder {{ pub fn let_named(key: crate::Name, env: &crate::Environment, _: (), _: (), _: bool) {{ let _ = env.get_const(&key); }} }} }}
            impl Environment {{ fn add_decl(&mut self) {{
                {declaration}
                Expr::let_named(Name::from_string("Shadow.binder.lookup"), self, (), (), false);
            }} }}
        "#);
        let census = Census::with_plant("kcheck_trace/term.rs", &source);
        eprintln!("binder shadow sites: {:?}", census.literal_sites().into_iter()
            .filter(|(_, (s, _))| s == "Shadow.binder.lookup").collect::<Vec<_>>());
        assert_metadata_roles(&census, "kcheck_trace/term.rs");
        assert_refused(&census, "kcheck_trace/term.rs", "Shadow.binder.lookup");
    }
    let source = r#"
        mod census_raw {
            use crate::*;
            pub struct Binder;
            impl Binder { pub fn let_named(key: Name, env: &Environment, _: (), _: (), _: bool) { let _ = env.get_const(&key); } }
            use self::{Binder as r#Expr};
            pub fn census_raw_run(env: &Environment) {
                Expr::let_named(Name::from_string("Shadow.binder.lookup"), env, (), (), false);
            }
        }
        impl Environment { fn add_decl(&mut self) { census_raw::census_raw_run(self); } }
    "#;
    let census = Census::with_plant("kcheck_trace/term.rs", source);
    assert_metadata_roles(&census, "kcheck_trace/term.rs");
    assert_refused(&census, "kcheck_trace/term.rs", "Shadow.binder.lookup");
}

#[test]
fn shadowed_codec_trait_is_refused() {
    for declaration in [
        "trait PersistentExtEntry { fn to_env_entry(&self) -> EnvExtensionEntry; fn from_env_entry(entry: &EnvExtensionEntry) -> Option<Self> where Self: Sized; }",
        "use self::Codec as PersistentExtEntry;",
    ] {
        let source = format!(r#"
            mod census_shadow {{
                use crate::env::{{EnvExtensionEntry, EnvExtensionEntryData, Environment}};
                use crate::Name;
                pub trait Codec {{ fn to_env_entry(&self) -> EnvExtensionEntry; fn from_env_entry(entry: &EnvExtensionEntry) -> Option<Self> where Self: Sized; }}
                {declaration}
                pub struct Lookup;
                impl PersistentExtEntry for Lookup {{
                    fn to_env_entry(&self) -> EnvExtensionEntry {{
                        let entry = EnvExtensionEntry {{ name: Name::from_string("Shadow.codec.encoding"), data: EnvExtensionEntryData::Scalar(0) }};
                        let _ = Environment::default().get_const(&entry.name);
                        entry
                    }}
                    fn from_env_entry(entry: &EnvExtensionEntry) -> Option<Self> {{
                        match &entry.data {{
                            EnvExtensionEntryData::Scalar(_) if entry.name == Name::from_string("Shadow.codec.decoding") => {{ let _ = Environment::default().get_const(&entry.name); Some(Self) }}
                            _ => None,
                        }}
                    }}
                }}
                pub fn census_codec_run() {{
                    let entry = Lookup.to_env_entry();
                    let _ = Lookup::from_env_entry(&entry);
                }}
            }}
            impl Environment {{ fn add_decl(&mut self) {{ census_shadow::census_codec_run(); }} }}
        "#);
        let census = Census::with_plant("env/csimp.rs", &source);
        for literal in ["Shadow.codec.encoding", "Shadow.codec.decoding"] {
            eprintln!("codec shadow sites: {:?}", census.literal_sites().into_iter()
                .filter(|(_, (s, _))| s == literal).collect::<Vec<_>>());
        }
        assert_metadata_roles(&census, "env/csimp.rs");
        for literal in ["Shadow.codec.encoding", "Shadow.codec.decoding"] {
            assert_refused(&census, "env/csimp.rs", literal);
        }
    }
}

#[test]
fn registry_aliases_paths_and_parameters_are_refused() {
    for body in [
        r#"fn register_persistent_ext(key: Name) { let _ = Environment::default().get_const(&key); } register_persistent_ext(Name::from_string("Shadow.registry.binding"));"#,
        r#"use self::census_registry::lookup as register_persistent_ext; register_persistent_ext(Name::from_string("Shadow.registry.binding"));"#,
        r#"self::census_registry::register_persistent_ext(Name::from_string("Shadow.registry.binding"));"#,
        r#"let receiver = census_registry::Receiver; receiver.register_persistent_ext(Name::from_string("Shadow.registry.binding"));"#,
        r#"let probe = |register_persistent_ext: fn(Name)| { register_persistent_ext(Name::from_string("Shadow.registry.binding")); }; probe(census_registry::lookup);"#,
        r#"match census_registry::lookup as fn(Name) { register_persistent_ext => register_persistent_ext(Name::from_string("Shadow.registry.binding")) }"#,
    ] {
        let source = format!(
            r#"
            mod census_registry {{
                use crate::{{Name, Environment}};
                pub fn lookup(key: Name) {{ let _ = Environment::default().get_const(&key); }}
                pub fn register_persistent_ext(key: Name) {{ lookup(key); }}
                pub struct Receiver;
                impl Receiver {{ pub fn register_persistent_ext(&self, key: Name) {{ lookup(key); }} }}
            }}
            impl Environment {{ fn add_decl(&mut self) {{ {body} }} }}
        "#
        );
        let census = Census::with_plant("env/exposure.rs", &source);
        assert_metadata_roles(&census, "env/exposure.rs");
        assert_refused(&census, "env/exposure.rs", "Shadow.registry.binding");
    }
}

#[test]
fn shadowed_constructor_type_cannot_borrow_a_real_binder_role() {
    for declaration in [
        "struct Name; impl Name { fn from_string(key: &str) -> crate::Name { census_name::Lookup::from_string(key) } }",
        "use self::census_name::Lookup as Name;",
    ] {
        let source = format!(r#"
            mod census_name {{
                pub struct Lookup;
                impl Lookup {{ pub fn from_string(key: &str) -> crate::Name {{
                    let key = crate::Name::from_string(key);
                    let _ = crate::Environment::default().get_const(&key);
                    key
                }} }}
            }}
            impl Environment {{ fn add_decl(&mut self) {{
                {declaration}
                Expr::let_named(Name::from_string("Shadow.constructor.lookup"), Expr::bvar(0), Expr::bvar(0), Expr::bvar(0), false);
            }} }}
        "#);
        let census = Census::with_plant("kcheck_trace/term.rs", &source);
        assert_metadata_roles(&census, "kcheck_trace/term.rs");
        assert_refused(&census, "kcheck_trace/term.rs", "Shadow.constructor.lookup");
    }
}

#[test]
fn codec_record_type_and_decoder_parameter_shadows_are_refused() {
    for declaration in [
        "struct EnvExtensionEntry { name: Name, data: EnvExtensionEntryData }",
        "use super::census_record::Record as EnvExtensionEntry;",
    ] {
        let source = format!(
            r#"
            mod census_record {{
                pub struct Record {{ pub name: crate::Name, pub data: crate::env::EnvExtensionEntryData }}
            }}
            mod census_codec {{
                use crate::env::{{EnvExtensionEntry, EnvExtensionEntryData, PersistentExtEntry, Environment}};
                use crate::Name;
                #[derive(Clone)] pub struct Lookup;
                impl PersistentExtEntry for Lookup {{
                    fn to_env_entry(&self) -> EnvExtensionEntry {{
                        {declaration}
                        let entry = EnvExtensionEntry {{ name: Name::from_string("Shadow.record.encoding"), data: EnvExtensionEntryData::Scalar(0) }};
                        let _ = Environment::default().get_const(&entry.name);
                        crate::env::EnvExtensionEntry {{ name: entry.name, data: entry.data }}
                    }}
                    fn from_env_entry(entry: &EnvExtensionEntry) -> Option<Self> {{
                        {declaration}
                        let entry = EnvExtensionEntry {{ name: entry.name.clone(), data: EnvExtensionEntryData::Scalar(0) }};
                        match &entry.data {{
                            EnvExtensionEntryData::Scalar(_) if entry.name == Name::from_string("Shadow.record.decoding") => {{ let _ = Environment::default().get_const(&entry.name); Some(Self) }}
                            _ => None,
                        }}
                    }}
                }}
                pub fn census_record_run() {{ let entry = Lookup.to_env_entry(); let _ = Lookup::from_env_entry(&entry); }}
            }}
            impl Environment {{ fn add_decl(&mut self) {{ census_codec::census_record_run(); }} }}
        "#
        );
        let census = Census::with_plant("env/csimp.rs", &source);
        assert_metadata_roles(&census, "env/csimp.rs");
        for literal in ["Shadow.record.encoding", "Shadow.record.decoding"] {
            assert_refused(&census, "env/csimp.rs", literal);
        }
    }
}

#[test]
fn codec_decoder_pattern_and_closure_parameters_are_refused() {
    for body in [
        r#"let (entry,) = (entry,); match &entry.data { EnvExtensionEntryData::Scalar(_) if entry.name == Name::from_string("Shadow.parameter.lookup") => { let _ = Environment::default().get_const(&entry.name); Some(Self) }, _ => None }"#,
        r#"let decode = |entry: &EnvExtensionEntry| match &entry.data { EnvExtensionEntryData::Scalar(_) if entry.name == Name::from_string("Shadow.parameter.lookup") => { let _ = Environment::default().get_const(&entry.name); Some(Self) }, _ => None }; decode(entry)"#,
    ] {
        let source = format!(
            r#"
            mod census_parameter {{
                use crate::env::{{EnvExtensionEntry, EnvExtensionEntryData, PersistentExtEntry, Environment}};
                use crate::Name;
                #[derive(Clone)] pub struct Lookup;
                impl PersistentExtEntry for Lookup {{
                    fn to_env_entry(&self) -> EnvExtensionEntry {{ EnvExtensionEntry {{ name: Name::anon(), data: EnvExtensionEntryData::Scalar(0) }} }}
                    fn from_env_entry(entry: &EnvExtensionEntry) -> Option<Self> {{ {body} }}
                }}
                pub fn census_parameter_run() {{ let entry = Lookup.to_env_entry(); let _ = Lookup::from_env_entry(&entry); }}
            }}
            impl Environment {{ fn add_decl(&mut self) {{ census_parameter::census_parameter_run(); }} }}
        "#
        );
        let census = Census::with_plant("env/csimp.rs", &source);
        assert_metadata_roles(&census, "env/csimp.rs");
        assert_refused(&census, "env/csimp.rs", "Shadow.parameter.lookup");
    }
}

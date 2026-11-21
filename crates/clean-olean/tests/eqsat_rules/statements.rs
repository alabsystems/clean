// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The pinned statements of the `eqsat_rules` gate: the rows of the family's
//! `STATEMENTS` file, the theorems the sources declare, and the digest of what
//! a theorem states on the replayed kernel environment.
//!
//! The `eqsat_decide` gate takes this module too (`#[path]`), with its own
//! `PINNED_MODULES` and `SAT_LEMMAS`: nothing here names another module of the
//! `eqsat_rules` gate.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use clean_kernel::env::{ConstantKind, Environment};
use clean_kernel::expr::UsedConstants;
use clean_kernel::name::Name;
use sha2::{Digest, Sha256};

use super::lean_tripwire::lean_code_only;
use super::{family_source_dir, hex, PINNED_MODULES, SAT_LEMMAS};

/// The rows of a `STATEMENTS` text: `name digest`, one per line; `#` starts a
/// comment line. A malformed or repeated row is a panic, never a skipped row.
pub(super) fn statement_pins(text: &str) -> BTreeMap<String, String> {
    let mut pins = BTreeMap::new();
    for line in text.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let mut parts = line.split_whitespace();
        let (Some(name), Some(digest), None) = (parts.next(), parts.next(), parts.next()) else {
            panic!("STATEMENTS: not a `name digest` row: {line}");
        };
        assert!(
            digest.len() == 64 && digest.bytes().all(|b| b.is_ascii_hexdigit()),
            "STATEMENTS: {name}: not a SHA-256 in hex"
        );
        assert!(
            pins.insert(name.to_owned(), digest.to_owned()).is_none(),
            "STATEMENTS: {name} has two rows"
        );
    }
    pins
}

/// An open scope of a Lean source: a namespace, or a section (named or not).
enum Scope {
    Namespace(String),
    Section(Option<String>),
}

/// The names a module's source declares with `theorem` (comments removed
/// first, so a theorem named in prose is not counted), each with the
/// namespaces open at its line: `namespace`, a namespace opened inside it
/// (`namespace Packed` under `namespace EqsatDecide` names
/// `EqsatDecide.Packed.…`) and the `end` that closes each are followed, and a
/// section adds nothing to a name. Every theorem of the module is under
/// `namespace`; one that is not, a modifier before `theorem`, an `end` that
/// closes nothing or names another scope, and a scope left open are panics,
/// never a theorem that goes unread.
pub(super) fn source_theorems(module: &str, namespace: &str) -> BTreeSet<String> {
    let path = family_source_dir().join(format!("{module}.lean"));
    let text =
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    let code = lean_code_only(&text);
    assert!(
        code.lines()
            .any(|line| line.trim() == format!("namespace {namespace}")),
        "{module}.lean declares its theorems in namespace {namespace}"
    );
    let mut scopes: Vec<Scope> = Vec::new();
    let mut names = BTreeSet::new();
    for line in code.lines() {
        let words: Vec<&str> = line.split_whitespace().collect();
        if words.contains(&"theorem") && !line.starts_with("theorem ") {
            panic!("{module}.lean: a `theorem` that does not start its line is not read: {line}");
        }
        if line.starts_with(char::is_whitespace) {
            continue;
        }
        match words.as_slice() {
            ["namespace", name] => scopes.push(Scope::Namespace((*name).to_owned())),
            ["section"] | ["noncomputable", "section"] => scopes.push(Scope::Section(None)),
            ["section", name] | ["noncomputable", "section", name] => {
                scopes.push(Scope::Section(Some((*name).to_owned())));
            }
            ["end"] => match scopes.pop() {
                Some(Scope::Section(None)) => {}
                _ => panic!("{module}.lean: a bare `end` that closes no unnamed section"),
            },
            ["end", name] => match scopes.pop() {
                Some(Scope::Namespace(open) | Scope::Section(Some(open))) if open == *name => {}
                _ => panic!("{module}.lean: `end {name}` does not close the scope open there"),
            },
            [first, ..] if matches!(*first, "namespace" | "section" | "end") => {
                panic!("{module}.lean: a scope line that is not read: {line}")
            }
            _ => {}
        }
        let Some(rest) = line.strip_prefix("theorem ") else {
            continue;
        };
        let name: String = rest
            .chars()
            .take_while(|ch| ch.is_alphanumeric() || matches!(ch, '_' | '\'' | '.'))
            .collect();
        assert!(!name.is_empty(), "{module}.lean: unnamed theorem: {line}");
        assert!(
            !name.starts_with("_root_."),
            "{module}.lean: a `_root_` theorem is not read: {line}"
        );
        let mut full = String::new();
        for scope in &scopes {
            if let Scope::Namespace(open) = scope {
                full.push_str(open);
                full.push('.');
            }
        }
        full.push_str(&name);
        assert!(
            full.starts_with(&format!("{namespace}.")),
            "{module}.lean: {full} is declared outside namespace {namespace}"
        );
        assert!(
            names.insert(full.clone()),
            "{module}.lean declares {full} twice"
        );
    }
    assert!(
        scopes.is_empty(),
        "{module}.lean: a namespace or section is left open"
    );
    names
}

/// Every name the gate requires a pinned statement for.
pub(super) fn required_statements() -> BTreeSet<String> {
    let mut required = BTreeSet::new();
    for (module, namespace) in PINNED_MODULES {
        required.extend(source_theorems(module, namespace));
    }
    required.extend(SAT_LEMMAS.iter().map(|rule| format!("EqsatInt.{rule}_sat")));
    required
}

/// Compare the statements the replay computed with the pinned rows: the same
/// names, the same digest for each.
pub(super) fn check_statement_pins(
    observed: &BTreeMap<String, String>,
    pins: &BTreeMap<String, String>,
) -> Result<(), String> {
    for name in pins.keys() {
        if !observed.contains_key(name) {
            return Err(format!("{name}: pinned, and not a theorem of the family"));
        }
    }
    for (name, digest) in observed {
        match pins.get(name) {
            None => return Err(format!("{name}: no pinned statement")),
            Some(pin) if pin != digest => {
                return Err(format!(
                    "{name}: the statement is not the pinned one ({digest}, pinned {pin})"
                ))
            }
            Some(_) => {}
        }
    }
    Ok(())
}

/// Length-prefixed bytes into a digest stream.
fn put(hasher: &mut Sha256, bytes: &[u8]) {
    hasher.update((bytes.len() as u64).to_le_bytes());
    hasher.update(bytes);
}

/// What a theorem states, as a digest: its name, its universe parameters and
/// its type in the kernel's own record encoding (`bincode`, the encoding
/// `Environment::closure_digest` hashes), then, for every constant the type
/// names in ascending name order, the name and its closure digest. So the
/// digest moves when the statement is edited and when the meaning of
/// anything the statement mentions changes; a change to the proof alone does
/// not move it. Refuses a name that is not a theorem.
pub(super) fn statement_digest(
    env: &Environment,
    name: &Name,
    closures: &mut HashMap<Name, [u8; 32]>,
) -> Result<String, String> {
    let constant = env
        .get_const(name)
        .ok_or_else(|| format!("{name}: not a constant of the replayed environment"))?;
    if constant.kind != ConstantKind::Theorem || constant.value.is_none() {
        return Err(format!("{name}: is a {:?}, not a theorem", constant.kind));
    }
    let encode = |what: &str, bytes: Result<Vec<u8>, bincode::error::EncodeError>| {
        bytes.map_err(|e| format!("{name}: encode {what}: {e}"))
    };
    let config = bincode::config::standard();
    let mut hasher = Sha256::new();
    put(&mut hasher, b"clean.eqsat_rules.statement.v1");
    put(
        &mut hasher,
        &encode("name", bincode::serde::encode_to_vec(name, config))?,
    );
    put(
        &mut hasher,
        &encode(
            "level parameters",
            bincode::serde::encode_to_vec(&constant.level_params, config),
        )?,
    );
    put(
        &mut hasher,
        &encode(
            "type",
            bincode::serde::encode_to_vec(&constant.type_, config),
        )?,
    );
    let mut used = HashSet::new();
    constant
        .type_
        .used_constants_dag(UsedConstants::WithProjectionStructures, &mut used);
    let mut mentioned: Vec<(String, Name)> = used.into_iter().map(|u| (u.to_string(), u)).collect();
    mentioned.sort();
    hasher.update((mentioned.len() as u64).to_le_bytes());
    for (text, used) in mentioned {
        let closure = match closures.get(&used) {
            Some(closure) => *closure,
            None => {
                let closure = env
                    .closure_digest(&used)
                    .map_err(|e| format!("{name}: closure of {text}: {e:?}"))?;
                closures.insert(used, closure);
                closure
            }
        };
        put(&mut hasher, text.as_bytes());
        hasher.update(closure);
    }
    Ok(hex(&hasher.finalize()))
}

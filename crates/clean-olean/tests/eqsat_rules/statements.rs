// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The pinned statements of the `eqsat_rules` gate: the rows of the family's
//! `STATEMENTS` file, the theorems the sources declare, and the digest of what
//! a theorem states on the replayed kernel environment.

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

/// The names a module's source declares with `theorem`, each under
/// `namespace` (comments removed first, so a theorem named in prose is not
/// counted).
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
    let mut names = BTreeSet::new();
    for line in code.lines() {
        let Some(rest) = line.strip_prefix("theorem ") else {
            assert!(
                !line.trim_start().starts_with("theorem "),
                "{module}.lean: an indented `theorem` is not read: {line}"
            );
            continue;
        };
        let name: String = rest
            .chars()
            .take_while(|ch| ch.is_alphanumeric() || matches!(ch, '_' | '\'' | '.'))
            .collect();
        assert!(!name.is_empty(), "{module}.lean: unnamed theorem: {line}");
        assert!(
            names.insert(format!("{namespace}.{name}")),
            "{module}.lean declares {name} twice"
        );
    }
    names
}

/// The rules of `EqsatIntRuleDefs.lean` that have a `where` clause and are
/// not `fold_*` rules: the last line of a generated definition is its
/// `Conds`.
pub(super) fn conditioned_rules() -> BTreeSet<String> {
    let path = family_source_dir().join("EqsatIntRuleDefs.lean");
    let text =
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    let code = lean_code_only(&text);
    let mut rules = BTreeSet::new();
    let mut seen = 0usize;
    let mut lines = code.lines().peekable();
    while let Some(line) = lines.next() {
        let Some(rest) = line.strip_prefix("def ") else {
            continue;
        };
        let name = rest
            .strip_suffix(" : Rule :=")
            .unwrap_or_else(|| panic!("EqsatIntRuleDefs.lean: not a generated definition: {line}"));
        let mut body = Vec::new();
        while let Some(next) = lines.peek() {
            if next.trim().is_empty() {
                break;
            }
            body.push(lines.next().expect("peeked").trim());
        }
        assert_eq!(body.len(), 5, "{name}: `Rule.mk` and four fields");
        let conds = body[4];
        assert!(
            conds == "Conds.nil" || conds.starts_with("(Conds.cons "),
            "{name}: the last field is its Conds: {conds}"
        );
        seen += 1;
        if conds != "Conds.nil" && !name.starts_with("fold_") {
            rules.insert(name.to_owned());
        }
    }
    assert_eq!(seen, 76, "the integer rule set has 76 rules");
    rules
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

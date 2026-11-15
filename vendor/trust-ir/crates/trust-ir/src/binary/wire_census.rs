// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The wire-allocation census: what the codec ACTUALLY writes, compared with
//! what `wire-allocations.toml` (repo root) says has been allocated.
//!
//! Three namespaces on this wire are linear counters — "the next format
//! version", "the next tag of enum E", "the next version of digest domain D".
//! A linear counter shared by parallel lines of work is a contended resource,
//! and until 2026-09-18 it had no lock: wire versions collided five times in
//! one quarter (v26..=v28, v39 twice, v41, v42) and a digest domain once
//! (`obligation.digest`, v5) — each is a `note` on its registry row.
//! The registry is the lock's data; a push to `main` is the lock itself. This
//! module is what makes the registry LOAD-BEARING rather than one more prose
//! table that drifts: every claim in it is re-derived here from the code.
//!
//!   * tags are observed BEHAVIOURALLY — each registered enum variant is run
//!     through the real writer and the byte it emits is read back — so the
//!     census cannot be fooled by a reformatted `match`, and it cannot drift
//!     from the writer the way the hand-kept tag tables in
//!     `docs/binary-format.md` did;
//!   * version constants and versioned identity strings are found by scanning
//!     the sources, so a NEW constant or a NEW `.vN` / `-vN` string with no
//!     registry row fails the build's test run instead of being discovered at
//!     merge time;
//!   * the read status of every version number is probed against the real
//!     header check;
//!   * WHICH enums are tag spaces is a hand-kept list (`TAG_SPACES`), so the
//!     codec source is scanned for every enum it matches to or from a literal
//!     tag byte, and one that is not registered fails. The first backfill was
//!     made by reading the writers and missed a live space; a behavioural
//!     census can only sample the spaces somebody told it about.
//!
//! The checks are pure functions over (registry text, observed facts), so the
//! mutation tests at the bottom can hand them a doctored registry or a
//! doctored source and assert the refusal — that a missing row FAILS is
//! exercised by the suite on every run, not demonstrated once.
//!
//! None of this is a proof. These are executed tests and source scans on a
//! lane that makes no verification claim, and each scan has an edge, stated
//! where it is defined and in the header of `wire-allocations.toml`.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Debug;
use std::path::{Path, PathBuf};

use super::*;

// ---------------------------------------------------------------------------
// The registry file and its (deliberately tiny) grammar
// ---------------------------------------------------------------------------

/// Path of the registry, relative to this crate's manifest. It lives at the
/// repo ROOT (not `docs/`, which never ships) because this test reads it at
/// run time in every checkout, the public snapshot included.
const REGISTRY_RELATIVE: &str = "../../wire-allocations.toml";

#[derive(Debug, Clone, PartialEq, Eq)]
enum Value {
    Int(u64),
    Str(String),
}

#[derive(Debug, Clone)]
struct Row {
    line: usize,
    fields: BTreeMap<String, Value>,
}

impl Row {
    fn int(&self, key: &str) -> Result<u64, String> {
        match self.fields.get(key) {
            Some(Value::Int(v)) => Ok(*v),
            Some(Value::Str(_)) => Err(format!("line {}: `{key}` must be an integer", self.line)),
            None => Err(format!("line {}: missing integer `{key}`", self.line)),
        }
    }

    fn str(&self, key: &str) -> Result<&str, String> {
        match self.fields.get(key) {
            Some(Value::Str(v)) => Ok(v),
            Some(Value::Int(_)) => Err(format!("line {}: `{key}` must be a string", self.line)),
            None => Err(format!("line {}: missing string `{key}`", self.line)),
        }
    }

    fn opt_str(&self, key: &str) -> Result<Option<&str>, String> {
        match self.fields.get(key) {
            None => Ok(None),
            Some(_) => self.str(key).map(Some),
        }
    }

    fn only_keys(&self, allowed: &[&str]) -> Result<(), String> {
        for key in self.fields.keys() {
            if !allowed.contains(&key.as_str()) {
                return Err(format!(
                    "line {}: unknown key `{key}` (allowed: {})",
                    self.line,
                    allowed.join(", ")
                ));
            }
        }
        Ok(())
    }
}

#[derive(Debug, Default)]
struct Registry {
    tables: BTreeMap<String, Vec<Row>>,
}

impl Registry {
    fn rows(&self, table: &str) -> &[Row] {
        self.tables.get(table).map_or(&[], Vec::as_slice)
    }
}

/// Parse the registry. The grammar is a strict SUBSET of TOML, chosen so that
/// the unit of allocation is ONE LINE (one inline table per row):
///
/// ```text
/// # comment
/// name = [
///   { key = 1, other = "text" },
/// ]
/// ```
///
/// Anything else is an error. Strings carry no escapes (no `"` or `\`), so
/// this parser and `scripts/wire_alloc.py` cannot disagree about a row.
fn parse_registry(text: &str) -> Result<Registry, String> {
    let mut registry = Registry::default();
    let mut open: Option<String> = None;
    for (index, raw) in text.lines().enumerate() {
        let line_no = index + 1;
        let line = raw.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        match &open {
            None => {
                let name = line
                    .strip_suffix(" = [")
                    .filter(|name| {
                        !name.is_empty() && name.chars().all(|c| c.is_ascii_lowercase() || c == '_')
                    })
                    .ok_or_else(|| format!("line {line_no}: expected `name = [`, got `{line}`"))?;
                if registry.tables.contains_key(name) {
                    return Err(format!("line {line_no}: table `{name}` opened twice"));
                }
                registry.tables.insert(name.to_owned(), Vec::new());
                open = Some(name.to_owned());
            }
            Some(_) if line == "]" => open = None,
            Some(name) => {
                let inner = line
                    .strip_prefix("{ ")
                    .and_then(|rest| rest.strip_suffix(" },"))
                    .ok_or_else(|| {
                        format!("line {line_no}: a row is `{{ key = value, ... }},` on one line")
                    })?;
                let row = Row {
                    line: line_no,
                    fields: parse_fields(inner, line_no)?,
                };
                registry
                    .tables
                    .get_mut(name)
                    .expect("open table exists")
                    .push(row);
            }
        }
    }
    if let Some(name) = open {
        return Err(format!("table `{name}` is never closed with `]`"));
    }
    Ok(registry)
}

fn parse_fields(inner: &str, line_no: usize) -> Result<BTreeMap<String, Value>, String> {
    let mut fields = BTreeMap::new();
    let mut rest = inner;
    loop {
        let (key, after_key) = rest
            .split_once(" = ")
            .ok_or_else(|| format!("line {line_no}: expected `key = value` in `{rest}`"))?;
        if key.is_empty() || !key.chars().all(|c| c.is_ascii_lowercase() || c == '_') {
            return Err(format!("line {line_no}: bad key `{key}`"));
        }
        let (value, after_value) = if let Some(quoted) = after_key.strip_prefix('"') {
            let end = quoted
                .find('"')
                .ok_or_else(|| format!("line {line_no}: unterminated string for `{key}`"))?;
            let text = &quoted[..end];
            if text.contains('\\') {
                return Err(format!(
                    "line {line_no}: escapes are not allowed in `{key}`"
                ));
            }
            (Value::Str(text.to_owned()), &quoted[end + 1..])
        } else {
            let end = after_key.find(',').unwrap_or(after_key.len());
            let digits = &after_key[..end];
            let number = digits
                .parse::<u64>()
                .ok()
                .filter(|_| !digits.starts_with('+') && (digits == "0" || !digits.starts_with('0')))
                .ok_or_else(|| format!("line {line_no}: `{key}` is not a plain integer"))?;
            (Value::Int(number), &after_key[end..])
        };
        if fields.insert(key.to_owned(), value).is_some() {
            return Err(format!("line {line_no}: key `{key}` given twice"));
        }
        if after_value.is_empty() {
            return Ok(fields);
        }
        rest = after_value
            .strip_prefix(", ")
            .ok_or_else(|| format!("line {line_no}: expected `, ` after `{key}`"))?;
    }
}

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn load_registry() -> Registry {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join(REGISTRY_RELATIVE);
    let text = std::fs::read_to_string(&path).unwrap_or_else(|error| {
        panic!(
            "{} could not be read ({error}). It is the wire-allocation registry and must exist \
             at the repo root in every checkout (publish/manifest.txt ships it).",
            path.display()
        )
    });
    parse_registry(&text).unwrap_or_else(|error| panic!("{}: {error}", path.display()))
}

// ---------------------------------------------------------------------------
// Namespace 1: wire versions
// ---------------------------------------------------------------------------

const VERSION_STATUSES: [&str; 4] = ["retired", "burned", "landed", "reserved"];

/// `(name, value)` of every module-wire version constant declared in
/// `binary.rs`: `VERSION` itself and every `*_FORMAT_VERSION` whose value is a
/// literal. (`FORMAT_VERSION = VERSION` is an alias and carries no number of
/// its own.)
fn scan_version_constants(binary_src: &str) -> Vec<(String, u32)> {
    let mut found = Vec::new();
    for line in binary_src.lines() {
        let line = line.trim();
        let Some(rest) = line
            .strip_prefix("pub const ")
            .or_else(|| line.strip_prefix("pub(crate) const "))
            .or_else(|| line.strip_prefix("const "))
        else {
            continue;
        };
        let Some((name, value)) = rest.split_once(": u32 = ") else {
            continue;
        };
        if name != "VERSION" && !name.ends_with("_FORMAT_VERSION") {
            continue;
        }
        if let Some(number) = value.strip_suffix(';').and_then(|v| v.parse::<u32>().ok()) {
            found.push((name.to_owned(), number));
        }
    }
    found
}

/// Does the real module reader accept a header carrying `version`? A
/// header-only blob is enough: the version check is the second thing the
/// reader does, and everything after it fails with a DIFFERENT error.
fn reader_accepts_header(version: u32) -> bool {
    let mut blob = MAGIC.to_vec();
    blob.extend_from_slice(&version.to_le_bytes());
    !matches!(
        deserialize_module(&blob),
        Err(BinaryError::UnsupportedVersion)
    )
}

fn check_wire_versions(
    registry: &Registry,
    binary_src: &str,
    accepts: &dyn Fn(u32) -> bool,
) -> Vec<String> {
    let mut errors = Vec::new();
    let rows = registry.rows("wire_version");
    if rows.is_empty() {
        return vec!["registry has no `wire_version` rows".to_owned()];
    }
    let mut by_number: BTreeMap<u32, (&Row, &str)> = BTreeMap::new();
    let mut constants: BTreeMap<&str, u32> = BTreeMap::new();
    for (index, row) in rows.iter().enumerate() {
        let parsed = (|| -> Result<(u32, &str), String> {
            row.only_keys(&[
                "number", "feature", "constant", "status", "owner", "date", "note",
            ])?;
            let number = u32::try_from(row.int("number")?)
                .map_err(|_| format!("line {}: `number` exceeds u32", row.line))?;
            let status = row.str("status")?;
            if !VERSION_STATUSES.contains(&status) {
                return Err(format!(
                    "line {}: status `{status}` is not one of {VERSION_STATUSES:?}",
                    row.line
                ));
            }
            if row.str("feature")?.is_empty() || row.str("owner")?.is_empty() {
                return Err(format!(
                    "line {}: `feature` and `owner` are required",
                    row.line
                ));
            }
            Ok((number, status))
        })();
        let (number, status) = match parsed {
            Ok(parsed) => parsed,
            Err(error) => {
                errors.push(error);
                continue;
            }
        };
        // Contiguous from 1: "the next number" is max + 1 and nothing else, so
        // there is no gap a second line could quietly take.
        let expected = u32::try_from(index).expect("row count fits u32") + 1;
        if number != expected {
            errors.push(format!(
                "line {}: wire versions must be unique, strictly increasing and gap-free — \
                 expected {expected}, found {number}",
                row.line
            ));
        }
        by_number.insert(number, (row, status));
        match row.opt_str("constant") {
            Ok(Some(name)) => {
                if constants.insert(name, number).is_some() {
                    errors.push(format!("line {}: constant `{name}` named twice", row.line));
                }
            }
            Ok(None) => {}
            Err(error) => errors.push(error),
        }
    }

    // Code -> registry: every version constant has a LANDED row that names it.
    let declared = scan_version_constants(binary_src);
    let Some(&(_, latest)) = declared.iter().find(|(name, _)| name == "VERSION") else {
        errors.push("binary.rs declares no literal `VERSION` constant".to_owned());
        return errors;
    };
    for (name, number) in &declared {
        let landed = by_number
            .get(number)
            .is_some_and(|(_, status)| *status == "landed");
        if !landed {
            errors.push(format!(
                "binary.rs declares `{name} = {number}` but wire-allocations.toml has no \
                 `landed` wire_version row numbered {number}. Reserve the number FIRST \
                 (the protocol heads wire-allocations.toml), then flip the row to \"landed\" with the code."
            ));
        }
        if name != "VERSION" && constants.get(name.as_str()) != Some(number) {
            errors.push(format!(
                "binary.rs declares `{name} = {number}` but no wire_version row carries \
                 `constant = \"{name}\"` at number {number}"
            ));
        }
    }
    // Registry -> code: a row's named constant exists with the row's number
    // (a RESERVED row may name a constant that does not exist yet — that is
    // the point of a reservation — but never one that exists with another
    // number).
    for (name, number) in &constants {
        let status = by_number[number].1;
        match declared.iter().find(|(declared, _)| declared == name) {
            Some((_, value)) if value != number => errors.push(format!(
                "wire_version {number} names `{name}`, which binary.rs declares as {value}"
            )),
            None if status != "reserved" => errors.push(format!(
                "wire_version {number} ({status}) names `{name}`, which binary.rs does not declare"
            )),
            _ => {}
        }
    }
    // Status is a claim about the READER, so ask the reader.
    let highest = *by_number.keys().next_back().expect("rows are non-empty");
    for version in 0..=highest + 1 {
        let status = by_number.get(&version).map(|(_, status)| *status);
        let accepted = accepts(version);
        let expected = status == Some("landed");
        if accepted != expected {
            errors.push(format!(
                "wire version {version}: registry says {} but the module reader {} that header",
                status.unwrap_or("UNALLOCATED"),
                if accepted { "ACCEPTS" } else { "REFUSES" }
            ));
        }
        if status == Some("reserved") && version <= latest {
            errors.push(format!(
                "wire version {version} is `reserved` but VERSION is already {latest}: a \
                 reservation is always above the latest landed version"
            ));
        }
    }
    let highest_landed = by_number
        .iter()
        .filter(|(_, (_, status))| *status == "landed")
        .map(|(number, _)| *number)
        .next_back();
    if highest_landed != Some(latest) {
        errors.push(format!(
            "VERSION is {latest} but the highest `landed` wire_version row is {highest_landed:?}"
        ));
    }
    errors
}

// ---------------------------------------------------------------------------
// Two ledgers, one counter
// ---------------------------------------------------------------------------
//
// On 2026-09-18 two sessions each built a lock for "the next wire version",
// the same day, in different files: this registry's `wire_version` table, and
// `crates/trust-ir/wire_versions.tsv` (roadmap WS8.5, checked by
// `binary::wire_version_ledger`). Each is sound alone. Together, unbound, they
// REINTRODUCE the race both exist to close: a reservation pushed to one file is
// invisible to the tool that reads the other, the two pushes touch different
// files so git reports no conflict, and — measured the day they met — with v44
// given to two different owners, one per file, every LIVE check in both gates
// stayed green. So the two are bound here, number by number. Which one survives
// is the owner's decision; until then `scripts/wire_alloc.py` writes both, and
// `wire_alloc.py sync` copies a reservation made in only one of them.

/// Relative to this crate's manifest.
const VERSION_LEDGER_RELATIVE: &str = "wire_versions.tsv";

/// One row of the other ledger, its status in THIS registry's words.
struct LedgerRow {
    status: &'static str,
    line: usize,
    feature: String,
    owner: String,
}

/// Does `text` contain `word` as a whole identifier?
fn names_identifier(text: &str, word: &str) -> bool {
    let ident = |c: char| c.is_ascii_alphanumeric() || c == '_';
    text.match_indices(word).any(|(at, _)| {
        !text[..at].chars().next_back().is_some_and(ident)
            && !text[at + word.len()..].chars().next().is_some_and(ident)
    })
}

/// `number -> row` of the other ledger.
fn parse_version_ledger(tsv: &str) -> Result<BTreeMap<u32, LedgerRow>, String> {
    let mut rows = BTreeMap::new();
    for (index, raw) in tsv.lines().enumerate() {
        let line = index + 1;
        if raw.trim().is_empty() || raw.starts_with('#') {
            continue;
        }
        let mut columns = raw.split('\t');
        let number = columns
            .next()
            .and_then(|number| number.parse::<u32>().ok())
            .ok_or_else(|| format!("{VERSION_LEDGER_RELATIVE}:{line}: no version number"))?;
        let status = match columns.next() {
            Some("retired") => "retired",
            Some("shipped") => "landed",
            Some("refused") => "burned",
            Some("reserved") => "reserved",
            other => {
                return Err(format!(
                    "{VERSION_LEDGER_RELATIVE}:{line}: unknown status {other:?}"
                ));
            }
        };
        let row = LedgerRow {
            status,
            line,
            feature: columns.next().unwrap_or("").to_owned(),
            owner: columns.nth(1).unwrap_or("").to_owned(),
        };
        if rows.insert(number, row).is_some() {
            return Err(format!(
                "{VERSION_LEDGER_RELATIVE}:{line}: v{number} has two rows"
            ));
        }
    }
    Ok(rows)
}

fn check_the_version_ledgers_agree(registry: &Registry, tsv: &str) -> Vec<String> {
    const WHY: &str = "Two ledgers claim this one counter (wire-allocations.toml and \
                       crates/trust-ir/wire_versions.tsv), and a reservation in only one of them \
                       is invisible to the other's tool. `python3 scripts/wire_alloc.py sync` \
                       copies an open reservation across; `reserve version` and `takeover` \
                       write both.";
    let theirs = match parse_version_ledger(tsv) {
        Ok(rows) => rows,
        Err(error) => return vec![error],
    };
    let Some(&floor) = theirs.keys().next() else {
        return vec![format!("{VERSION_LEDGER_RELATIVE} has no rows. {WHY}")];
    };
    let ours = version_statuses(registry);
    let mut errors = Vec::new();
    for (number, row) in &theirs {
        let (status, line) = (&row.status, &row.line);
        // Same number, same status, DIFFERENT holder: the race itself, in the
        // one shape a number-by-number comparison cannot see. An open number
        // has ONE owner and ONE constant, and both files must name them.
        if *status == "reserved" && ours.get(number).map(String::as_str) == Some("reserved") {
            let mine = registry
                .rows("wire_version")
                .iter()
                .find(|mine| mine.int("number").ok() == Some(u64::from(*number)));
            let owner = mine.and_then(|mine| mine.str("owner").ok()).unwrap_or("");
            let constant = mine.and_then(|mine| mine.opt_str("constant").ok().flatten());
            let named = constant.is_none_or(|constant| names_identifier(&row.feature, constant));
            if owner != row.owner || !named {
                errors.push(format!(
                    "wire v{number} is reserved in BOTH ledgers, for different holders: \
                     wire-allocations.toml says owner `{owner}`{}; \
                     {VERSION_LEDGER_RELATIVE}:{line} says owner `{}`, feature `{}`. One of you \
                     does not hold this number: the later reservation moves to the next free one.",
                    constant.map_or(String::new(), |c| format!(", constant `{c}`")),
                    row.owner,
                    row.feature
                ));
            }
        }
        match ours.get(number) {
            Some(mine) if mine == *status => {}
            Some(mine) => errors.push(format!(
                "wire v{number}: wire-allocations.toml says `{mine}`, \
                 {VERSION_LEDGER_RELATIVE}:{line} says `{status}` (in this registry's words). {WHY}"
            )),
            None => errors.push(format!(
                "wire v{number} is `{status}` in {VERSION_LEDGER_RELATIVE}:{line} and has NO row \
                 in wire-allocations.toml. {WHY}"
            )),
        }
    }
    for (number, status) in &ours {
        // The other ledger starts where its history does; below that this
        // registry may only say "retired".
        let predates = *number < floor && status == "retired";
        if !theirs.contains_key(number) && !predates {
            errors.push(format!(
                "wire v{number} is `{status}` in wire-allocations.toml and has NO row in \
                 {VERSION_LEDGER_RELATIVE}. {WHY}"
            ));
        }
    }
    errors
}

// ---------------------------------------------------------------------------
// Namespace 2: enum tag spaces — the behavioural census
// ---------------------------------------------------------------------------

/// One tag the codec writes: `variant` of tag space `space` goes on the wire
/// as byte `tag`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct TagRow {
    space: &'static str,
    variant: String,
    tag: u8,
}

/// Where each registered tag space's Rust enum is defined, so the census can
/// prove it sampled EVERY variant (source path relative to `src/`).
const TAG_SPACES: &[(&str, &str)] = &[
    ("AllocOrigin", "inst.rs"),
    ("AssertKind", "inst.rs"),
    ("AssertOverflowOp", "inst.rs"),
    ("AtomicRMWOp", "inst.rs"),
    ("AttrValue", "dialect/inst.rs"),
    ("BinOp", "inst.rs"),
    ("BodyGate", "lib.rs"),
    ("CallingConv", "lib.rs"),
    ("CastOp", "inst.rs"),
    ("ClausePlace", "proof/obligations.rs"),
    ("ClauseSort", "proof/obligations.rs"),
    ("Constant", "constant.rs"),
    ("CoverageBound", "proof/evidence.rs"),
    ("DiagnosticSeverity", "proof/obligations.rs"),
    ("Divergence", "proof/annotations.rs"),
    ("EffectPlace", "effects.rs"),
    ("EffectSet", "effects.rs"),
    ("Endianness", "lib.rs"),
    ("EnumTagEncoding", "ty.rs"),
    ("EnumTagRepr", "ty.rs"),
    ("FCmpOp", "inst.rs"),
    ("FatPtrKind", "ty.rs"),
    ("HoleKind", "template.rs"),
    ("ICmpOp", "inst.rs"),
    ("IdentityScheme", "imports.rs"),
    ("Inst", "inst.rs"),
    ("Linkage", "lib.rs"),
    ("NativeAdapterInput", "request/facts.rs"),
    ("NativeBundleProducer", "request/facts.rs"),
    ("ObligationKind", "proof/obligations.rs"),
    ("Ordering", "inst.rs"),
    ("OverflowOp", "inst.rs"),
    ("PanicLocation", "inst.rs"),
    ("PassMode", "lib.rs"),
    ("Pred", "pred.rs"),
    ("Producer", "lib.rs"),
    ("ProofAnnotation", "proof/annotations.rs"),
    ("ProofDigestAlgorithm", "proof/evidence.rs"),
    ("ProofEvidence", "proof/evidence.rs"),
    ("ProofKind", "spec.rs"),
    ("ProofStatus", "proof/obligations.rs"),
    ("ProofTransformStage", "proof/lineage.rs"),
    ("SetRepr", "ty.rs"),
    ("SourcePlace", "lib.rs"),
    ("Space", "pred.rs"),
    ("SpecEnforcementMode", "spec.rs"),
    ("SpecOrigin", "spec.rs"),
    ("SpecProjectionTarget", "spec.rs"),
    ("StructPassingPolicy", "lib.rs"),
    ("StructRepr", "ty.rs"),
    ("TemplateArg", "template.rs"),
    ("TemplateParam", "template.rs"),
    ("TemplateRef", "level.rs"),
    ("TemporalForm", "spec.rs"),
    ("TensorIndexExpr", "inst.rs"),
    ("TensorMapNode", "inst.rs"),
    ("TensorReduceOp", "inst.rs"),
    ("TensorReduceOrder", "inst.rs"),
    ("TlsModel", "lib.rs"),
    ("Ty", "ty.rs"),
    ("TypeContract", "template.rs"),
    ("TypeOrigin", "ty.rs"),
    ("UnOp", "inst.rs"),
    ("Universe", "pred.rs"),
    ("Visibility", "lib.rs"),
];

/// Variants that exist in the Rust enum and have NO wire spelling, each with
/// the reason. Anything else without a census sample is an error.
const UNENCODABLE: &[(&str, &str, &str)] = &[
    (
        "AssertKind",
        "Unspecified",
        "spelled by Inst tag 29 (the kindless assert), never by an AssertKind byte: tag 63 \
         cannot carry it, so each assert has one encoding",
    ),
    (
        "Ty",
        "Error",
        "producer-internal typing hole: the writer refuses it by name (BinarySink::refuse), the validator rejects",
    ),
    (
        "ProofAnnotation",
        "Goal",
        "feature `clean-expr` only, and filtered out before binary serialization",
    ),
];

/// The variant head of a `Debug` rendering: `Struct(StructId(0))` -> `Struct`.
fn debug_head(value: &impl Debug) -> String {
    format!("{value:?}")
        .chars()
        .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
        .collect()
}

/// The bytes `write` emits for `value`.
///
/// Sealed by replay: the census samples VARIANTS, not modules, so it has no
/// `collect_*` walk to pair with each of ~45 tag spaces. `by_replay` runs the
/// writer against a recording probe to discover the strings the sample
/// spells, then re-runs it against the sealed table — the same collect-then-
/// write order a real serialization takes, with the discovery done for it.
fn encode<T>(value: &T, write: &dyn Fn(&mut Vec<u8>, &SealedStringPool, &T)) -> Vec<u8> {
    SealedStringPool::by_replay(|pool, buf| write(buf, pool, value))
}

/// A tag space with its own writer: the tag is the FIRST byte written.
fn direct<T: Debug>(
    space: &'static str,
    samples: Vec<T>,
    write: &dyn Fn(&mut Vec<u8>, &SealedStringPool, &T),
) -> Vec<TagRow> {
    samples
        .iter()
        .map(|sample| TagRow {
            space,
            variant: debug_head(sample),
            tag: encode(sample, write)[0],
        })
        .collect()
}

/// A tag space written INLINE inside a larger record (no writer of its own).
/// Every sample is the same record differing only in the variant, so the tag
/// is the first byte at which the encodings stop agreeing.
fn differential(space: &'static str, encodings: Vec<(String, Vec<u8>)>) -> Vec<TagRow> {
    assert!(
        encodings.len() >= 2,
        "{space}: a differential probe needs two samples"
    );
    let first = &encodings[0].1;
    let index = (0..first.len())
        .find(|&i| {
            encodings
                .iter()
                .any(|(_, bytes)| bytes.get(i) != first.get(i))
        })
        .unwrap_or_else(|| panic!("{space}: every sample encoded identically"));
    encodings
        .into_iter()
        .map(|(variant, bytes)| TagRow {
            space,
            variant,
            tag: bytes[index],
        })
        .collect()
}

fn v(index: u32) -> ValueId {
    ValueId::new(index)
}

fn b(index: u32) -> BlockId {
    BlockId::new(index)
}

fn ty_samples() -> Vec<Ty> {
    let boxed = || Box::new(Ty::I32);
    vec![
        Ty::I8,
        Ty::I16,
        Ty::I32,
        Ty::I64,
        Ty::I128,
        Ty::U8,
        Ty::U16,
        Ty::U32,
        Ty::U64,
        Ty::U128,
        Ty::Isize,
        Ty::Usize,
        Ty::Char,
        Ty::F16,
        Ty::F32,
        Ty::F64,
        Ty::Bool,
        Ty::Vector(boxed(), 4),
        Ty::Ptr,
        Ty::FatPtr(FatPtrKind::Str),
        Ty::Unit,
        Ty::Never,
        Ty::Struct(StructId::new(0)),
        Ty::Array(TyId::new(0), 4),
        Ty::Tuple(vec![Ty::I32]),
        Ty::Enum(EnumId::new(0)),
        Ty::Func(FuncTyId::new(0)),
        Ty::Ref(boxed()),
        Ty::RefMut(boxed()),
        Ty::PtrConst(boxed()),
        Ty::PtrMut(boxed()),
        Ty::Rc(boxed()),
        Ty::Set(TyId::new(0), SetRepr::Boxed),
        Ty::Sequence(TyId::new(0)),
        Ty::Record(RecordId::new(0)),
        Ty::Closure(ClosureTyId::new(0)),
        Ty::Refine(TyId::new(0), crate::value::PredId::new(0)),
        Ty::Dialect(Box::new(crate::ty::DialectTy::new("census", "opaque", 1))),
        Ty::Handle(Box::new(crate::ty::HandleTy::new("Nat", "census::Nat"))),
        Ty::Storage(crate::StorageLayout::new(80, 8)),
        // The tensor region (`TENSOR_FORMAT_VERSION`): rank, then the inline
        // element.
        Ty::Tensor(boxed(), 2),
    ]
}

fn constant_samples() -> Vec<Constant> {
    vec![
        Constant::Int(1),
        Constant::U128(u128::MAX),
        Constant::Bytes {
            data: vec![1],
            utf8: false,
        },
        Constant::Float(1.0),
        Constant::Bool(true),
        Constant::Aggregate(vec![]),
        Constant::Array(vec![]),
        // v50: the uniform array's constant-size spelling.
        Constant::Splat {
            elem: Box::new(Constant::Int(1)),
            len: 2,
        },
        Constant::Vector(vec![]),
        Constant::Sequence(vec![]),
        Constant::Set(vec![]),
        Constant::Record(vec![]),
        Constant::Closure {
            func: FuncId::new(0),
            captures: vec![],
        },
        Constant::FnDef(FuncId::new(0)),
        Constant::SymbolAddr {
            symbol: "s".into(),
            addend: 0,
        },
        Constant::PhantomData,
        // Crystal lane (E3b): an unwritten aggregate lane (tag only).
        Constant::Uninit,
        // v70 (PKG-U13e): a tensor named by its blob digest.
        Constant::TensorBlob {
            digest: crate::blob::BlobDigest::of(&[1, 0, 0, 0]),
            dims: vec![1],
        },
    ]
}

fn inst_samples() -> Vec<Inst> {
    let ty = || Ty::I32;
    let fat = || Ty::FatPtr(FatPtrKind::Str);
    vec![
        Inst::BinOp {
            op: BinOp::Add,
            ty: ty(),
            lhs: v(0),
            rhs: v(1),
        },
        Inst::UnOp {
            op: UnOp::Neg,
            ty: ty(),
            operand: v(0),
        },
        Inst::Overflow {
            op: OverflowOp::AddOverflow,
            ty: ty(),
            lhs: v(0),
            rhs: v(1),
        },
        Inst::ICmp {
            op: ICmpOp::Eq,
            ty: ty(),
            lhs: v(0),
            rhs: v(1),
        },
        Inst::FCmp {
            op: FCmpOp::OEq,
            ty: Ty::F64,
            lhs: v(0),
            rhs: v(1),
        },
        Inst::Cast {
            op: CastOp::ZExt,
            src_ty: ty(),
            dst_ty: Ty::I64,
            operand: v(0),
        },
        Inst::Load {
            ty: ty(),
            ptr: v(0),
            volatile: false,
            align: None,
        },
        Inst::Store {
            ty: ty(),
            ptr: v(0),
            value: v(1),
            volatile: false,
            align: None,
        },
        Inst::Alloca {
            ty: ty(),
            count: None,
            align: None,
        },
        Inst::HeapAlloc {
            ty: ty(),
            count: None,
            align: None,
            origin: AllocOrigin::RustHeap,
        },
        Inst::GEP {
            pointee_ty: ty(),
            base: v(0),
            indices: vec![],
            inbounds: false,
        },
        Inst::PtrData {
            ptr_ty: fat(),
            ptr: v(0),
        },
        Inst::PtrMetadata {
            ptr_ty: fat(),
            metadata_ty: Ty::U64,
            ptr: v(0),
        },
        Inst::PtrFromParts {
            ptr_ty: fat(),
            metadata_ty: Ty::U64,
            data: v(0),
            metadata: v(1),
        },
        Inst::AtomicLoad {
            ty: ty(),
            ptr: v(0),
            ordering: Ordering::SeqCst,
        },
        Inst::AtomicStore {
            ty: ty(),
            ptr: v(0),
            value: v(1),
            ordering: Ordering::SeqCst,
        },
        Inst::AtomicRMW {
            op: AtomicRMWOp::Add,
            ty: ty(),
            ptr: v(0),
            value: v(1),
            ordering: Ordering::SeqCst,
        },
        Inst::CmpXchg {
            ty: ty(),
            ptr: v(0),
            expected: v(1),
            desired: v(2),
            success: Ordering::SeqCst,
            failure: Ordering::Relaxed,
            weak: false,
        },
        Inst::Fence {
            ordering: Ordering::SeqCst,
        },
        Inst::Br {
            target: b(0),
            args: vec![],
        },
        Inst::CondBr {
            cond: v(0),
            then_target: b(0),
            then_args: vec![],
            else_target: b(1),
            else_args: vec![],
        },
        Inst::Switch {
            value: v(0),
            default: b(0),
            default_args: vec![],
            cases: vec![],
            exhaustive_enum_unreachable: false,
        },
        Inst::Call {
            callee: FuncId::new(0),
            args: vec![],
        },
        Inst::CallCannotUnwind {
            callee: FuncId::new(0),
            args: vec![],
        },
        Inst::CallIndirectCannotUnwind {
            callee: v(0),
            sig: FuncTyId::new(0),
            args: vec![],
            calling_conv: CallingConv::C,
        },
        Inst::CallIndirect {
            callee: v(0),
            sig: FuncTyId::new(0),
            args: vec![],
            calling_conv: CallingConv::C,
        },
        Inst::Return { values: vec![] },
        Inst::ExtractField {
            ty: ty(),
            aggregate: v(0),
            field: 0,
        },
        Inst::InsertField {
            ty: ty(),
            aggregate: v(0),
            field: 0,
            value: v(1),
        },
        Inst::ExtractElement {
            ty: ty(),
            array: v(0),
            index: v(1),
        },
        Inst::InsertElement {
            ty: ty(),
            array: v(0),
            index: v(1),
            value: v(2),
        },
        Inst::Const {
            ty: ty(),
            value: Constant::Int(1),
        },
        Inst::NullPtr,
        Inst::GlobalAddr {
            global: GlobalId::new(0),
        },
        Inst::Undef { ty: ty() },
        Inst::Assume { cond: v(0) },
        Inst::Assert {
            cond: v(0),
            kind: crate::inst::AssertKind::Unspecified,
            site: None,
        },
        Inst::Unreachable,
        Inst::Copy {
            ty: ty(),
            operand: v(0),
        },
        Inst::Select {
            ty: ty(),
            cond: v(0),
            then_val: v(1),
            else_val: v(2),
        },
        Inst::SeqMapAddK {
            ty: ty(),
            seq: v(0),
            k: 1,
        },
        Inst::SeqMapNot {
            ty: Ty::Bool,
            seq: v(0),
        },
        Inst::SeqMap {
            ty: ty(),
            seq: v(0),
            fwd: FuncId::new(0),
        },
        Inst::MakeClosure {
            ty: crate::value::ClosureTyId::new(0),
            func: FuncId::new(0),
            captures: vec![v(0)],
        },
        // v50: `n` copies of one operand.
        Inst::ArraySplat {
            ty: Ty::Array(TyId::new(0), 4),
            value: v(0),
        },
        // The tensor region (`TENSOR_FORMAT_VERSION`): a matrix multiply
        // (`batch: []`, `contract: [(1, 0)]`) of two rank-2 operands.
        Inst::TensorContract {
            ty: Ty::Tensor(Box::new(ty()), 2),
            lhs: v(0),
            rhs: v(1),
            batch: vec![],
            contract: vec![(1, 0)],
        },
        // v68 (`TENSOR_MAP_REDUCE_VIEW_FORMAT_VERSION`): an element-wise
        // negation, a row sum and a transpose.
        Inst::TensorMap {
            ty: Ty::Tensor(Box::new(Ty::I32), 1),
            args: vec![v(0)],
            body: vec![crate::TensorMapNode::UnOp {
                op: UnOp::Neg,
                ty: Ty::I32,
                operand: 0,
            }],
        },
        Inst::TensorReduce {
            ty: Ty::Tensor(Box::new(Ty::I32), 1),
            src: v(0),
            op: crate::TensorReduceOp::Add,
            axes: vec![1],
            order: crate::TensorReduceOrder::RowMajor,
        },
        Inst::TensorView {
            ty: Ty::Tensor(Box::new(Ty::I32), 2),
            src: v(0),
            params: vec![],
            exprs: vec![
                crate::TensorIndexExpr::SrcExtent(1),
                crate::TensorIndexExpr::SrcExtent(0),
                crate::TensorIndexExpr::Coord(1),
                crate::TensorIndexExpr::Coord(0),
            ],
            shape: vec![0, 1],
            index: vec![2, 3],
            fill: None,
        },
        // v69 (`TENSOR_GATHER_SCATTER_FORMAT_VERSION`): a two-axis gather and
        // a one-axis scatter.
        Inst::TensorGather {
            ty: Ty::Tensor(Box::new(Ty::I32), 1),
            data: v(0),
            coords: vec![v(1), v(2)],
        },
        Inst::TensorScatter {
            ty: Ty::Tensor(Box::new(Ty::I32), 1),
            init: v(0),
            src: v(1),
            coords: vec![v(2)],
        },
        // v51, the INST wire batch: the register aggregate seed (WS3.5) and
        // the bulk-memory pair (WS3.20).
        Inst::MakeAggregate {
            ty: ty(),
            variant: None,
            fields: vec![v(0), v(1)],
        },
        Inst::MemCopy {
            dst: v(0),
            src: v(1),
            bytes: v(2),
            overlap: false,
        },
        Inst::MemSet {
            dst: v(0),
            byte: v(1),
            bytes: v(2),
        },
        Inst::Borrow { ptr: v(0) },
        Inst::BorrowMut { ptr: v(0) },
        Inst::EndBorrow { borrow_ptr: v(0) },
        Inst::Retain { ptr: v(0) },
        Inst::Release { ptr: v(0) },
        Inst::IsUnique { ptr: v(0) },
        Inst::Dealloc { ptr: v(0) },
        Inst::OpenFrame {
            def: crate::inst::BindingFrameDef::new(
                crate::value::BindingFrameId::new(0),
                "frame",
                vec![],
            ),
        },
        Inst::BindSlot {
            frame: v(0),
            slot: 0,
            value: v(1),
        },
        Inst::LoadSlot {
            frame: v(0),
            slot: 0,
            ty: ty(),
        },
        Inst::CloseFrame { frame: v(0) },
        Inst::CoroSuspend {
            frame: v(0),
            state_slot: 0,
            next_state: 1,
            value: v(1),
        },
        Inst::Invoke {
            callee: FuncId::new(0),
            args: vec![],
            normal_dest: b(0),
            normal_args: vec![],
            unwind_dest: b(1),
        },
        Inst::LandingPad {
            is_cleanup: true,
            catch_type_indices: vec![],
        },
        Inst::Resume { exn: v(0) },
        // v54 (amendment P): the terminator spelling of a sited check.
        Inst::AssertInvoke {
            cond: v(0),
            kind: crate::inst::AssertKind::Unspecified,
            site: crate::inst::PanicSite {
                entry: FuncId::new(0),
                location: crate::inst::PanicLocation::Global(GlobalId::new(0)),
            },
            normal_dest: b(0),
            normal_args: vec![],
            unwind_dest: b(1),
        },
        Inst::DialectOp(Box::new(crate::dialect::DialectInst::new("census", "op"))),
        Inst::Drop {
            ty: ty(),
            ptr: v(0),
        },
        // v55 (amendment D): the unwinding twin of a drop.
        Inst::DropInvoke {
            ty: ty(),
            ptr: v(0),
            normal_dest: b(0),
            normal_args: vec![],
            unwind_dest: b(1),
        },
        // v56 (amendment D, Part 2): the unwinding twin of an indirect call.
        Inst::InvokeIndirect {
            callee: v(0),
            sig: FuncTyId::new(0),
            args: vec![],
            calling_conv: CallingConv::C,
            normal_dest: b(0),
            normal_args: vec![],
            unwind_dest: b(1),
        },
    ]
}

fn proof_annotation_samples() -> Vec<ProofAnnotation> {
    vec![
        ProofAnnotation::InBounds,
        ProofAnnotation::NotNull,
        ProofAnnotation::ValidBorrow,
        ProofAnnotation::UniqueBorrow,
        ProofAnnotation::SharedBorrow,
        ProofAnnotation::ValidDealloc,
        ProofAnnotation::NoOverflow,
        ProofAnnotation::NoWrap,
        ProofAnnotation::DivNonZero,
        ProofAnnotation::ShiftInRange,
        ProofAnnotation::Wrapping,
        ProofAnnotation::Pure,
        ProofAnnotation::Terminates,
        ProofAnnotation::Deterministic,
        ProofAnnotation::Associative,
        ProofAnnotation::Commutative,
        ProofAnnotation::DataRaceFree,
        ProofAnnotation::AtomicOrdering(Ordering::SeqCst),
        ProofAnnotation::BoundedOutput { lo: 0.0, hi: 1.0 },
        ProofAnnotation::Monotonic,
        ProofAnnotation::NoAlias,
        ProofAnnotation::Aligned(8),
        ProofAnnotation::NoPanic,
        ProofAnnotation::NoUndef,
        ProofAnnotation::Tainted,
        ProofAnnotation::TrustedSink,
        ProofAnnotation::ReadonlyTable,
        ProofAnnotation::AppendOnlyBuffer,
        ProofAnnotation::AtomicSetInsert,
        ProofAnnotation::ParallelMap,
        ProofAnnotation::BoundedLoop(4),
        ProofAnnotation::DivergenceClass(Divergence::Low),
        ProofAnnotation::FreshSymbolicHavoc,
        ProofAnnotation::RegionHavocStore,
        ProofAnnotation::Custom(ProofTag(0)),
        ProofAnnotation::ProofRef(ProofId::new(0)),
        ProofAnnotation::ValueRange { lo: 0, hi: 1 },
        ProofAnnotation::KnownBits { zeros: 0, ones: 0 },
        ProofAnnotation::BranchWeights(vec![1, 1]),
    ]
}

fn proof_evidence_rows() -> Vec<TagRow> {
    let write = |buf: &mut Vec<u8>, pool: &SealedStringPool, ev: &ProofEvidence| {
        write_proof_evidence(buf, pool, ev);
    };
    let mut rows = direct(
        "ProofEvidence",
        vec![
            ProofEvidence::SmtProof(vec![]),
            ProofEvidence::LeanProof("p".into()),
            ProofEvidence::KaniHarness("h".into()),
            ProofEvidence::GammaCrownBound {
                epsilon: 0.5,
                verified_layers: 1,
            },
            ProofEvidence::TranslationValidation {
                rule_name: "r".into(),
                smt_hash: [0; 32],
            },
            ProofEvidence::Trusted("audit".into()),
            ProofEvidence::InheritedFromCallee {
                callee: FuncId::new(0),
                obligation: ProofId::new(0),
                external: None,
            },
            ProofEvidence::CleanCic {
                term: vec![],
                context: vec![],
                lineage: ProofDigest::zero(),
                kernel_recheck: None,
            },
        ],
        &write,
    );
    // ONE Rust variant, TWO wire spellings: cross-crate inheritance took a new
    // tag (v41) so an older reader refuses it instead of reading it as local.
    let external = ProofEvidence::InheritedFromCallee {
        callee: FuncId::new(0),
        obligation: ProofId::new(0),
        external: Some(crate::ExternRef::new(crate::ImportId::new(0), "sym")),
    };
    rows.push(TagRow {
        space: "ProofEvidence",
        variant: "InheritedFromCallee.external".to_owned(),
        tag: encode(&external, &write)[0],
    });
    rows
}

fn struct_repr_rows() -> Vec<TagRow> {
    let encode_repr = |repr: StructRepr| {
        let def = StructDef {
            id: StructId::new(0),
            name: "S".into(),
            fields: vec![],
            size: None,
            align: None,
            repr,
            origin: None,
        };
        encode(&def, &|buf, pool, def| write_struct_def(buf, pool, def))
    };
    differential(
        "StructRepr",
        [
            StructRepr::Rust,
            StructRepr::C,
            StructRepr::Transparent,
            StructRepr::Packed(1),
        ]
        .into_iter()
        .map(|repr| (debug_head(&repr), encode_repr(repr)))
        .collect(),
    )
}

fn enum_def(repr: Option<EnumTagRepr>, encoding: Option<EnumTagEncoding>) -> Vec<u8> {
    let def = EnumDef {
        id: EnumId::new(0),
        name: "E".into(),
        variants: vec![EnumVariant {
            name: "A".into(),
            fields: vec![],
            field_names: vec![],
        }],
        discriminants: vec![],
        repr,
        layout: encoding.map(|encoding| EnumLayoutDescriptor {
            encoding,
            size: 1,
            align: 1,
            variant_field_offsets: vec![vec![]],
        }),
        origin: None,
    };
    encode(&def, &|buf, pool, def| write_enum_def(buf, pool, def))
}

fn type_origin_rows() -> Vec<TagRow> {
    // `write_type_origin` writes a PRESENCE byte and then the variant tag, and
    // it writes nothing at all below v58 — so the pool must be raised, exactly
    // as `collect_strings_into` raises it for a keyed definition.
    let encode_origin = |origin: TypeOrigin| {
        let mut seed = StringPoolBuilder::new();
        seed.raise_to(NOMINAL_IDENTITY_FORMAT_VERSION);
        SealedStringPool::by_replay_from(seed, |pool, buf| {
            write_type_origin(buf, pool, Some(&origin));
        })
    };
    differential(
        "TypeOrigin",
        [
            TypeOrigin::Rust {
                stable_crate_id: 0,
                def_path_hash: [0; 16],
                args_digest: ProofDigest::zero(),
            },
            TypeOrigin::Clean {
                decl: "Nat".into(),
                env_digest: ProofDigest::zero(),
            },
        ]
        .into_iter()
        .map(|origin| (debug_head(&origin), encode_origin(origin)))
        .collect(),
    )
}

fn enum_tag_repr_rows() -> Vec<TagRow> {
    // `(none)` is the absent-hint spelling that shares this byte with the
    // eight hints, so it occupies tag 0 of the same space.
    let mut encodings = vec![("(none)".to_owned(), enum_def(None, None))];
    for repr in [
        EnumTagRepr::U8,
        EnumTagRepr::U16,
        EnumTagRepr::U32,
        EnumTagRepr::U64,
        EnumTagRepr::I8,
        EnumTagRepr::I16,
        EnumTagRepr::I32,
        EnumTagRepr::I64,
        EnumTagRepr::U128,
        EnumTagRepr::I128,
    ] {
        encodings.push((debug_head(&repr), enum_def(Some(repr), None)));
    }
    differential("EnumTagRepr", encodings)
}

fn enum_tag_encoding_rows() -> Vec<TagRow> {
    let encodings = [
        EnumTagEncoding::Direct { tag_offset: 0 },
        EnumTagEncoding::Niche {
            untagged_variant: 0,
            niche_variants_start: 0,
            niche_variants_end: 0,
            niche_start: 0,
            niche_offset: 0,
            niche_ty: EnumTagRepr::U8,
        },
        EnumTagEncoding::Untagged,
        EnumTagEncoding::SingleInhabited { variant: 1 },
    ];
    differential(
        "EnumTagEncoding",
        encodings
            .into_iter()
            .map(|encoding| (debug_head(&encoding), enum_def(None, Some(encoding))))
            .collect(),
    )
}

fn coverage_bound_rows() -> Vec<TagRow> {
    let encode_bound = |bound: CoverageBound| {
        let certificate = ProofCertificate {
            obligation: ProofId::new(0),
            prover: "p".into(),
            evidence: ProofEvidence::SmtProof(vec![]),
            assurance: Some(CoverageAssurance {
                bound,
                request_digest: ProofDigest::zero(),
            }),
        };
        // The assurance block is a v41 contract-surface field: the writer only
        // emits it once the collection walk has raised the header, so the
        // replay starts from a pool already raised.
        let mut seed = StringPoolBuilder::new();
        raise_to_contract_surface(&mut seed);
        SealedStringPool::by_replay_from(seed, |pool, buf| {
            write_proof_certificate(buf, pool, &certificate)
        })
    };
    differential(
        "CoverageBound",
        [
            CoverageBound::Unbounded,
            CoverageBound::UnwindBounded { depth: 1 },
            CoverageBound::ModelBounded { size: 1 },
            CoverageBound::Unrecorded,
        ]
        .into_iter()
        .map(|bound| (debug_head(&bound), encode_bound(bound)))
        .collect(),
    )
}

fn alloc_origin_rows() -> Vec<TagRow> {
    differential(
        "AllocOrigin",
        [
            AllocOrigin::RustHeap,
            AllocOrigin::SwiftHeap,
            AllocOrigin::CMalloc,
            AllocOrigin::CleanHeap,
        ]
        .into_iter()
        .map(|origin| {
            let inst = Inst::HeapAlloc {
                ty: Ty::I32,
                count: None,
                align: None,
                origin,
            };
            (
                debug_head(&origin),
                encode(&inst, &|buf, pool, inst| write_inst(buf, pool, None, inst)),
            )
        })
        .collect(),
    )
}

fn struct_passing_rows() -> Vec<TagRow> {
    differential(
        "StructPassingPolicy",
        [
            StructPassingPolicy::NativeC,
            StructPassingPolicy::AlwaysMemory,
            StructPassingPolicy::Unclassified,
        ]
        .into_iter()
        .map(|struct_passing| {
            let mut module = Module::new("census");
            module.target_info = Some(TargetInfo {
                triple: "t".into(),
                pointer_size: 8,
                endianness: Endianness::Little,
                abi: None,
                struct_passing,
            });
            (
                debug_head(&struct_passing),
                serialize_module(&module).expect("serialize_module: test fixture"),
            )
        })
        .collect(),
    )
}

/// `DiagnosticSeverity` is written INLINE in the obligation-diagnostics
/// sidecar. The 2026-09-18 backfill missed it — the tag spaces were found by
/// reading the writers, and this one has no writer of its own — which is why
/// [`scan_tag_spaces`] now finds tag spaces mechanically.
fn diagnostic_severity_rows() -> Vec<TagRow> {
    use crate::proof::{DiagnosticSeverity, ObligationDiagnostic};
    differential(
        "DiagnosticSeverity",
        [
            DiagnosticSeverity::Error,
            DiagnosticSeverity::Warning,
            DiagnosticSeverity::Note,
        ]
        .into_iter()
        .map(|severity| {
            let mut module = Module::new("census");
            module.obligation_diagnostics.push(ObligationDiagnostic {
                obligation: ProofId::new(0),
                severity,
                message: "m".into(),
                location: None,
                detail: None,
            });
            (
                debug_head(&severity),
                serialize_module(&module).expect("serialize_module: test fixture"),
            )
        })
        .collect(),
    )
}

fn source_place_rows() -> Vec<TagRow> {
    differential(
        "SourcePlace",
        [
            SourcePlace::FunctionParameter { index: 0 },
            SourcePlace::LoopParameter { index: 0 },
        ]
        .into_iter()
        .map(|place| {
            let mut module = Module::new("census");
            let ft = module
                .add_func_type(FuncTy {
                    params: vec![],
                    returns: vec![],
                    abi: None,
                    is_vararg: false,
                })
                .expect("Module::add_func_type: test fixture");
            let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
            func.source_provenance = Some(SourceProvenance {
                schema: 1,
                compiler_source_digest: ProofDigest::zero(),
                semantic_body_digest: ProofDigest::zero(),
                binding_digest: ProofDigest::zero(),
                loops: vec![SourceLoopProvenance {
                    source_loop_id: 0,
                    hir_local_id: 0,
                    header: b(0),
                    bindings: vec![SourceBindingProvenance {
                        name: "x".into(),
                        hir_local_id: 0,
                        place,
                    }],
                }],
            });
            module
                .try_add_function(func)
                .expect("Module::try_add_function: test fixture");
            (
                debug_head(&place),
                serialize_module(&module).expect("serialize_module: test fixture"),
            )
        })
        .collect(),
    )
}

fn spec_module(
    target: Option<crate::spec::SpecProjectionTarget>,
    origin: crate::spec::SpecOrigin,
    enforcement: crate::spec::SpecEnforcementMode,
) -> Vec<u8> {
    let module = crate::spec::SpecModule {
        name: "M".into(),
        vars: vec![],
        actions: vec![],
        invariants: vec![],
        anchors: vec![crate::spec::SpecAnchor {
            machine: "M".into(),
            action: "a".into(),
            rust_symbol: "s".into(),
            span: "f.rs:1:1".into(),
            project: None,
            function: None,
            projection_target: target,
        }],
        waivers: vec![],
        proofs: vec![],
        origin,
        enforcement,
        temporal: Vec::new(),
    };
    encode(&module, &|buf, pool, module| {
        write_spec_module(buf, pool, module)
    })
}

fn spec_rows() -> Vec<TagRow> {
    use crate::spec::{SpecEnforcementMode, SpecOrigin, SpecProjectionTarget};
    let base = |target| {
        spec_module(
            target,
            SpecOrigin::Embedded,
            SpecEnforcementMode::DesignOnly,
        )
    };
    let mut rows = differential(
        "SpecProjectionTarget",
        vec![
            ("(none)".to_owned(), base(None)),
            (
                "Function".to_owned(),
                base(Some(SpecProjectionTarget::Function(FuncId::new(0)))),
            ),
            (
                "TemporalFieldPathsV1".to_owned(),
                base(Some(SpecProjectionTarget::TemporalFieldPathsV1)),
            ),
            (
                "ExternalUnresolved".to_owned(),
                base(Some(SpecProjectionTarget::ExternalUnresolved)),
            ),
        ],
    );
    rows.extend(differential(
        "SpecOrigin",
        vec![
            (
                "Embedded".to_owned(),
                spec_module(None, SpecOrigin::Embedded, SpecEnforcementMode::DesignOnly),
            ),
            (
                "External".to_owned(),
                spec_module(
                    None,
                    SpecOrigin::External("p".into()),
                    SpecEnforcementMode::DesignOnly,
                ),
            ),
        ],
    ));
    rows.extend(differential(
        "SpecEnforcementMode",
        vec![
            (
                "DesignOnly".to_owned(),
                spec_module(None, SpecOrigin::Embedded, SpecEnforcementMode::DesignOnly),
            ),
            (
                "Linked".to_owned(),
                spec_module(None, SpecOrigin::Embedded, SpecEnforcementMode::Linked),
            ),
        ],
    ));
    // `ProofKind` is written inline in the proofs block; every sample is the
    // same one-entry block differing only in the kind, so the tag is the first
    // byte at which the encodings stop agreeing. (It was a `buf.last()` probe
    // while the space had one variant; v46's `CleanTheorem` is followed by a
    // pooled theorem name, so the tag is no longer the last byte.)
    let proof_block = |kind: crate::spec::ProofKind| {
        let proofs = [crate::spec::SpecProof {
            machine: "M".into(),
            action: "a".into(),
            proof_name: "p".into(),
            kind,
        }];
        SealedStringPool::by_replay(|pool, buf| write_proofs(buf, pool, &proofs))
    };
    rows.extend(differential(
        "ProofKind",
        vec![
            ("Kani".to_owned(), proof_block(crate::spec::ProofKind::Kani)),
            (
                "CleanTheorem".to_owned(),
                proof_block(crate::spec::ProofKind::CleanTheorem { name: "T".into() }),
            ),
        ],
    ));
    // v68: a tensor map node and a tensor view node each have their own
    // writer (the tag is the first byte); the reduction operator is written
    // inline in `Inst::TensorReduce`, so every sample is the same reduction
    // differing only in the operator.
    rows.extend(direct(
        "TensorMapNode",
        vec![
            crate::TensorMapNode::<crate::level::NoExt>::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: 0,
                rhs: 0,
            },
            crate::TensorMapNode::UnOp {
                op: UnOp::Neg,
                ty: Ty::I32,
                operand: 0,
            },
            crate::TensorMapNode::ICmp {
                op: ICmpOp::Eq,
                ty: Ty::I32,
                lhs: 0,
                rhs: 0,
            },
            crate::TensorMapNode::Select {
                ty: Ty::I32,
                cond: 0,
                then_lane: 0,
                else_lane: 0,
            },
            crate::TensorMapNode::Cast {
                op: CastOp::SExt,
                src_ty: Ty::I8,
                dst_ty: Ty::I32,
                operand: 0,
            },
        ],
        &|buf, pool, node| write_tensor_map_node(buf, pool, node),
    ));
    {
        use crate::TensorIndexExpr as E;
        rows.extend(direct(
            "TensorIndexExpr",
            vec![
                E::Lit(0),
                E::Param(0),
                E::SrcExtent(0),
                E::Coord(0),
                E::Add(0, 0),
                E::Sub(0, 0),
                E::Mul(0, 0),
                E::Div(0, 0),
                E::Rem(0, 0),
                E::Min(0, 0),
                E::Max(0, 0),
            ],
            &|buf, _, expr| write_tensor_index_expr(buf, expr),
        ));
    }
    let reduction = |op: crate::TensorReduceOp| {
        encode(
            &Inst::TensorReduce {
                ty: Ty::Tensor(Box::new(Ty::I32), 0),
                src: v(0),
                op,
                axes: vec![0],
                order: crate::TensorReduceOrder::RowMajor,
            },
            &|buf, pool, inst| write_inst(buf, pool, None, inst),
        )
    };
    rows.extend(differential(
        "TensorReduceOp",
        crate::TensorReduceOp::ALL
            .iter()
            .map(|&op| (format!("{op:?}"), reduction(op)))
            .collect(),
    ));
    // `TensorReduceOrder` has one variant, written as the reduction's LAST
    // byte (a one-sample space has no differential).
    rows.push(TagRow {
        space: "TensorReduceOrder",
        variant: "RowMajor".to_owned(),
        tag: *reduction(crate::TensorReduceOp::Add)
            .last()
            .expect("a reduction encodes to bytes"),
    });
    // `TemporalForm` (v46) is written inline in the temporal block, same shape.
    let temporal_block = |form: crate::spec::TemporalForm| {
        let block = [crate::spec::SpecTemporal {
            name: "t".into(),
            form,
        }];
        SealedStringPool::by_replay(|pool, buf| write_temporal(buf, pool, &block))
    };
    let leaf = || ProofFormula::smtlib2("(> x 0)", "Bool");
    rows.extend(differential(
        "TemporalForm",
        vec![
            (
                "Always".to_owned(),
                temporal_block(crate::spec::TemporalForm::Always(leaf())),
            ),
            (
                "Eventually".to_owned(),
                temporal_block(crate::spec::TemporalForm::Eventually(leaf())),
            ),
            (
                "LeadsTo".to_owned(),
                temporal_block(crate::spec::TemporalForm::LeadsTo(leaf(), leaf())),
            ),
            (
                "WeakFair".to_owned(),
                temporal_block(crate::spec::TemporalForm::WeakFair {
                    action: "a".into(),
                    relation: None,
                }),
            ),
            (
                "StrongFair".to_owned(),
                temporal_block(crate::spec::TemporalForm::StrongFair {
                    action: "a".into(),
                    relation: None,
                }),
            ),
        ],
    ));
    rows
}

/// Every tag the codec writes, for every registered tag space.
fn codec_tag_census() -> Vec<TagRow> {
    let mut rows = Vec::new();
    rows.extend(direct("Ty", ty_samples(), &|buf, pool, ty| {
        write_ty(buf, pool, ty)
    }));
    // Amendment S: the extension tag, written only by the template writer.
    rows.extend(direct(
        "Ty",
        vec![TyG::<TemplateRef>::Ext(TemplateRef::Param(
            crate::value::ParamId::new(0),
        ))],
        &|buf, pool, ty| write_ty(buf, pool, ty),
    ));
    rows.extend(direct(
        "Constant",
        vec![ConstantG::<TemplateRef>::Ext(TemplateRef::Hole(
            crate::value::HoleId::new(0),
        ))],
        &|buf, pool, c| write_constant(buf, pool, c),
    ));
    rows.extend(direct(
        "TemplateRef",
        vec![
            TemplateRef::Param(crate::value::ParamId::new(0)),
            TemplateRef::Hole(crate::value::HoleId::new(0)),
        ],
        &|buf, _, r| TemplateRef::write_ext(buf, r),
    ));
    {
        use crate::template::{HoleKind, TemplateArg, TemplateParam, TypeContract};
        rows.extend(direct(
            "TemplateParam",
            vec![
                TemplateParam::Type,
                TemplateParam::Const { ty: Ty::Usize },
                TemplateParam::Host,
            ],
            &|buf, pool, param| write_template_param(buf, pool, param),
        ));
        rows.extend(direct(
            "TypeContract",
            vec![
                TypeContract::Opaque,
                TypeContract::Struct { fields: vec![] },
                TypeContract::Enum {
                    variants: vec![],
                    discriminants: vec![],
                    repr: None,
                },
            ],
            &|buf, pool, contract| write_type_contract(buf, pool, contract),
        ));
        rows.extend(direct(
            "HoleKind",
            vec![
                HoleKind::Type {
                    contract: TypeContract::Opaque,
                },
                HoleKind::Const { ty: Ty::Usize },
                HoleKind::Callee {
                    decl: FuncId::new(0),
                },
                HoleKind::Global {
                    decl: crate::value::GlobalId::new(0),
                },
            ],
            &|buf, pool, kind| write_hole_kind(buf, pool, kind),
        ));
        rows.extend(direct(
            "TemplateArg",
            vec![
                TemplateArg::Type(TyG::Ext(TemplateRef::Param(crate::value::ParamId::new(0)))),
                TemplateArg::Const {
                    value: ConstantG::Int(1),
                    ty: Ty::Usize,
                },
                TemplateArg::Host(crate::value::ParamId::new(0)),
            ],
            &|buf, pool, arg| write_template_arg(buf, pool, arg),
        ));
    }
    rows.extend(direct(
        "FatPtrKind",
        vec![
            FatPtrKind::Slice(TyId::new(0)),
            FatPtrKind::Str,
            FatPtrKind::TraitObject { trait_id: 0 },
            FatPtrKind::ContainerLen,
            FatPtrKind::ContainerVtable,
        ],
        &|buf, pool, kind| write_fat_ptr_kind(buf, pool, kind),
    ));
    rows.extend(direct(
        "SetRepr",
        vec![SetRepr::Bitset, SetRepr::Boxed],
        &|buf, _, repr| write_set_repr(buf, repr),
    ));
    rows.extend(direct(
        "Universe",
        vec![
            crate::pred::Universe::IntRange { lo: 0, hi: 1 },
            crate::pred::Universe::Members(vec![]),
        ],
        &|buf, pool, universe| write_universe(buf, pool, universe),
    ));
    rows.extend(direct(
        "Space",
        vec![crate::pred::Space::Index, crate::pred::Space::Member],
        &|buf, _, space| write_space(buf, *space),
    ));
    {
        use crate::pred::Pred;
        rows.extend(direct(
            "Pred",
            vec![
                Pred::Interval { lo: 0, hi: 1 },
                Pred::FiniteSet(vec![]),
                Pred::InUniverse(crate::value::UnivId::new(0), crate::pred::Space::Index),
                Pred::NonZero,
                Pred::NonNull,
                Pred::Conj(vec![]),
                Pred::Disj(vec![]),
                Pred::Top,
                Pred::Bottom,
            ],
            &|buf, pool, pred| write_pred(buf, pool, pred),
        ));
    }
    rows.extend(direct("Constant", constant_samples(), &|buf, pool, c| {
        write_constant(buf, pool, c);
    }));
    rows.extend(direct(
        "BinOp",
        vec![
            BinOp::Add,
            BinOp::Sub,
            BinOp::Mul,
            BinOp::UDiv,
            BinOp::SDiv,
            BinOp::URem,
            BinOp::SRem,
            BinOp::FAdd,
            BinOp::FSub,
            BinOp::FMul,
            BinOp::FDiv,
            BinOp::FRem,
            BinOp::FMin,
            BinOp::FMax,
            BinOp::And,
            BinOp::Or,
            BinOp::Xor,
            BinOp::Shl,
            BinOp::LShr,
            BinOp::AShr,
            BinOp::BAnd,
            BinOp::BOr,
            BinOp::BXor,
            // v51, the INST wire batch (WS3.20).
            BinOp::RotL,
            BinOp::RotR,
            BinOp::FCopySign,
        ],
        &|buf, _, op| write_binop(buf, op),
    ));
    rows.extend(direct(
        "UnOp",
        vec![
            UnOp::Neg,
            UnOp::FNeg,
            UnOp::FAbs,
            UnOp::FSqrt,
            UnOp::FFloor,
            UnOp::FCeil,
            UnOp::FTrunc,
            UnOp::Not,
            UnOp::CtPop,
            // v51, the INST wire batch (WS3.20).
            UnOp::CtLz,
            UnOp::CtTz,
            UnOp::BSwap,
            UnOp::BitReverse,
        ],
        &|buf, _, op| write_unop(buf, op),
    ));
    // v52 (plan item P): the kind of a tag-63 assert and its overflow op.
    rows.extend(direct(
        "AssertKind",
        vec![
            crate::inst::AssertKind::Overflow(crate::inst::AssertOverflowOp::Add),
            crate::inst::AssertKind::DivByZero,
            crate::inst::AssertKind::RemByZero,
            crate::inst::AssertKind::BoundsCheck {
                index: v(0),
                len: v(1),
            },
            crate::inst::AssertKind::MisalignedPtr {
                required: v(0),
                found: v(1),
            },
            crate::inst::AssertKind::NullPtr,
        ],
        &|buf, _, kind| write_assert_kind(buf, None, kind),
    ));
    rows.extend(direct(
        "AssertOverflowOp",
        crate::inst::AssertOverflowOp::ALL.to_vec(),
        &|buf, _, op| write_assert_overflow_op(buf, op),
    ));
    // v54 (amendment P): a panic site's location.
    rows.extend(direct(
        "PanicLocation",
        vec![
            crate::inst::PanicLocation::Global(GlobalId::new(0)),
            crate::inst::PanicLocation::Value(v(0)),
        ],
        &|buf, _, location| write_panic_location(buf, None, location),
    ));
    rows.extend(direct(
        "OverflowOp",
        vec![
            OverflowOp::AddOverflow,
            OverflowOp::SubOverflow,
            OverflowOp::MulOverflow,
        ],
        &|buf, _, op| write_overflow_op(buf, op),
    ));
    rows.extend(direct(
        "ICmpOp",
        vec![
            ICmpOp::Eq,
            ICmpOp::Ne,
            ICmpOp::Ult,
            ICmpOp::Ule,
            ICmpOp::Ugt,
            ICmpOp::Uge,
            ICmpOp::Slt,
            ICmpOp::Sle,
            ICmpOp::Sgt,
            ICmpOp::Sge,
        ],
        &|buf, _, op| write_icmp_op(buf, op),
    ));
    rows.extend(direct(
        "FCmpOp",
        vec![
            FCmpOp::OEq,
            FCmpOp::ONe,
            FCmpOp::OLt,
            FCmpOp::OLe,
            FCmpOp::OGt,
            FCmpOp::OGe,
            FCmpOp::UEq,
            FCmpOp::UNe,
            FCmpOp::ULt,
            FCmpOp::ULe,
            FCmpOp::UGt,
            FCmpOp::UGe,
        ],
        &|buf, _, op| write_fcmp_op(buf, op),
    ));
    rows.extend(direct(
        "CastOp",
        vec![
            CastOp::Trunc,
            CastOp::ZExt,
            CastOp::SExt,
            CastOp::FPTrunc,
            CastOp::FPExt,
            CastOp::FPToUI,
            CastOp::FPToSI,
            CastOp::UIToFP,
            CastOp::SIToFP,
            CastOp::PtrToInt,
            CastOp::IntToPtr,
            CastOp::PtrToPtr,
            CastOp::Bitcast,
            CastOp::Transmute,
            CastOp::ReifyFnPointer,
            CastOp::FPToSISat,
            CastOp::FPToUISat,
        ],
        &|buf, _, op| write_cast_op(buf, op),
    ));
    rows.extend(direct(
        "Ordering",
        vec![
            Ordering::Relaxed,
            Ordering::Acquire,
            Ordering::Release,
            Ordering::AcqRel,
            Ordering::SeqCst,
        ],
        &|buf, _, ordering| write_ordering(buf, ordering),
    ));
    rows.extend(direct(
        "AtomicRMWOp",
        vec![
            AtomicRMWOp::Xchg,
            AtomicRMWOp::Add,
            AtomicRMWOp::Sub,
            AtomicRMWOp::And,
            AtomicRMWOp::Or,
            AtomicRMWOp::Xor,
            AtomicRMWOp::Max,
            AtomicRMWOp::Min,
            AtomicRMWOp::UMax,
            AtomicRMWOp::UMin,
        ],
        &|buf, _, op| write_atomic_rmw_op(buf, op),
    ));
    rows.extend(direct(
        "ObligationKind",
        vec![
            ObligationKind::Precondition,
            ObligationKind::Postcondition,
            ObligationKind::LoopInvariant,
            ObligationKind::TypeInvariant,
            ObligationKind::RefinementType,
            ObligationKind::TranslationValidation,
            ObligationKind::MemorySafety,
            ObligationKind::PanicFreedom,
            ObligationKind::TemporalSafety,
            ObligationKind::Liveness,
            ObligationKind::ArithmeticSafety,
            ObligationKind::BoundsCheck,
            ObligationKind::GiveBackRefinement,
            ObligationKind::Termination,
            ObligationKind::Ownership,
            ObligationKind::Custom {
                namespace: "census".into(),
                name: "kind".into(),
            },
        ],
        &|buf, pool, kind| write_obligation_kind(buf, pool, kind),
    ));
    rows.extend(direct(
        "ProofStatus",
        vec![
            ProofStatus::Pending,
            ProofStatus::Discharged,
            ProofStatus::Failed,
            ProofStatus::Trusted,
            ProofStatus::Certified,
        ],
        &|buf, _, status| write_proof_status(buf, status),
    ));
    rows.extend(direct(
        "CallingConv",
        vec![
            CallingConv::C,
            CallingConv::Fast,
            CallingConv::Cold,
            CallingConv::Rust,
            CallingConv::Swift,
            CallingConv::CUnwind,
            CallingConv::SysV64,
            CallingConv::Win64,
            CallingConv::Aapcs,
            CallingConv::EfiApi,
            CallingConv::VectorCall,
            CallingConv::RustCold,
        ],
        &|buf, _, conv| write_calling_conv(buf, conv),
    ));
    rows.extend(direct(
        "IdentityScheme",
        vec![
            crate::imports::IdentityScheme::V2,
            crate::imports::IdentityScheme::V3,
        ],
        &|buf, _, scheme| write_identity_scheme(buf, *scheme),
    ));
    rows.extend(direct(
        "Visibility",
        vec![
            Visibility::Default,
            Visibility::Hidden,
            Visibility::Protected,
        ],
        &|buf, _, visibility| write_visibility(buf, visibility),
    ));
    rows.extend(direct(
        "Linkage",
        vec![
            Linkage::External,
            Linkage::Internal,
            Linkage::Private,
            Linkage::Weak,
            Linkage::LinkOnce,
            Linkage::AvailableExternally,
            Linkage::ExternalWeak,
            Linkage::WeakOdr,
            Linkage::LinkOnceOdr,
        ],
        &|buf, _, linkage| write_linkage(buf, linkage),
    ));
    rows.extend(direct(
        "TlsModel",
        vec![
            TlsModel::LocalExec,
            TlsModel::InitialExec,
            TlsModel::GeneralDynamic,
            TlsModel::LocalDynamic,
        ],
        &|buf, _, model| write_tls_model(buf, model),
    ));
    rows.extend(direct(
        "Endianness",
        vec![Endianness::Little, Endianness::Big],
        &|buf, _, endianness| write_endianness(buf, endianness),
    ));
    rows.extend(direct("Inst", inst_samples(), &|buf, pool, inst| {
        write_inst(buf, pool, None, inst);
    }));
    // ONE Rust variant, TWO wire spellings (crystal lane, D3): a WEAK compare-exchange
    // takes its own tag so an older reader refuses it instead of reading it as strong.
    // The writer COMPUTES this tag (`if weak { 58 } else { 13 }`), so the source scan
    // cannot see it; this sample is what makes the census observe it.
    let weak_cmpxchg = Inst::CmpXchg {
        ty: Ty::I32,
        ptr: v(0),
        expected: v(1),
        desired: v(2),
        success: Ordering::SeqCst,
        failure: Ordering::Relaxed,
        weak: true,
    };
    // ONE Rust variant, TWO wire spellings (plan item P, v52): a KINDED assert
    // takes tag 63 so an older reader refuses it instead of dropping the kind;
    // the writer picks 29 or 63 by `kind.is_unspecified()`.
    let kinded_assert = Inst::Assert {
        cond: v(0),
        kind: crate::inst::AssertKind::NullPtr,
        site: None,
    };
    rows.push(TagRow {
        space: "Inst",
        variant: "Assert.kinded".to_owned(),
        tag: encode(&kinded_assert, &|buf, pool, inst| {
            write_inst(buf, pool, None, inst);
        })[0],
    });
    // ONE Rust variant, a THIRD wire spelling (amendment P, v54): an assert
    // carrying a panic site, of any kind, takes tag 66 so an older reader
    // refuses it instead of dropping the site.
    let sited_assert = Inst::Assert {
        cond: v(0),
        kind: crate::inst::AssertKind::Unspecified,
        site: Some(crate::inst::PanicSite {
            entry: FuncId::new(0),
            location: crate::inst::PanicLocation::Global(GlobalId::new(0)),
        }),
    };
    rows.push(TagRow {
        space: "Inst",
        variant: "Assert.sited".to_owned(),
        tag: encode(&sited_assert, &|buf, pool, inst| {
            write_inst(buf, pool, None, inst);
        })[0],
    });
    rows.push(TagRow {
        space: "Inst",
        variant: "CmpXchg.weak".to_owned(),
        tag: encode(&weak_cmpxchg, &|buf, pool, inst| {
            write_inst(buf, pool, None, inst);
        })[0],
    });
    {
        use crate::dialect::AttrValue;
        rows.extend(direct(
            "AttrValue",
            vec![
                AttrValue::I64(1),
                AttrValue::U64(1),
                AttrValue::F64(1.0),
                AttrValue::Bool(true),
                AttrValue::Str("s".into()),
                AttrValue::Bytes(vec![]),
                AttrValue::Ty(Ty::I32),
            ],
            &|buf, pool, value| write_attr_value(buf, pool, value),
        ));
    }
    rows.extend(direct(
        "ProofAnnotation",
        proof_annotation_samples(),
        &|buf, pool, annotation| write_proof_annotation(buf, pool, annotation),
    ));
    rows.extend(direct(
        "Divergence",
        vec![Divergence::Uniform, Divergence::Low, Divergence::High],
        &|buf, _, divergence| write_divergence(buf, divergence),
    ));
    rows.extend(proof_evidence_rows());
    rows.extend(direct(
        "ProofDigestAlgorithm",
        vec![
            ProofDigestAlgorithm::Sha256,
            ProofDigestAlgorithm::TrustIrStableV1,
        ],
        &|buf, _, algorithm| {
            write_proof_digest(
                buf,
                &ProofDigest {
                    algorithm: *algorithm,
                    bytes: [0; 32],
                },
            );
        },
    ));
    rows.extend(direct(
        "ProofTransformStage",
        vec![
            ProofTransformStage::Frontend,
            ProofTransformStage::TrustIrLowering,
            ProofTransformStage::TrustIrOptimization,
            ProofTransformStage::SolverAdapter,
            ProofTransformStage::Backend,
            ProofTransformStage::Replay,
            ProofTransformStage::Composition,
            ProofTransformStage::Other,
        ],
        &|buf, _, stage| write_proof_transform_stage(buf, *stage),
    ));
    rows.extend(direct(
        "ClauseSort",
        vec![
            ClauseSort::Bool,
            ClauseSort::Int,
            ClauseSort::BitVec(8),
            ClauseSort::Array(Box::new(ClauseSort::Int), Box::new(ClauseSort::Bool)),
            ClauseSort::Float { eb: 8, sb: 24 },
            ClauseSort::RoundingMode,
            ClauseSort::Datatype {
                name: "D".into(),
                constructors: vec![],
            },
        ],
        &|buf, pool, sort| write_clause_sort(buf, pool, sort),
    ));
    rows.extend(direct(
        "ClausePlace",
        vec![
            ClausePlace::Param { index: 0 },
            ClausePlace::ResultSlot { index: 0 },
            ClausePlace::MutParamExit { index: 0 },
            ClausePlace::World,
            ClausePlace::Unwind,
            ClausePlace::Value(v(0)),
            ClausePlace::SpecVar { index: 0 },
            ClausePlace::SpecVarNext { index: 0 },
            ClausePlace::WorldPre,
            ClausePlace::WorldPost,
            ClausePlace::ParamPointeeEntry { index: 0 },
        ],
        &|buf, _, place| write_clause_place(buf, place),
    ));
    // v59 (WS1.14): the two effect-summary tag spaces, each with a writer of
    // its own.
    rows.extend(direct(
        "EffectSet",
        vec![
            crate::EffectSet::Nothing,
            crate::EffectSet::Places(vec![crate::EffectPlace::ParamPointee { index: 0 }]),
            crate::EffectSet::Everything,
        ],
        &|buf, _, set| write_effect_set(buf, set),
    ));
    rows.extend(direct(
        "EffectPlace",
        vec![
            crate::EffectPlace::ParamPointee { index: 0 },
            crate::EffectPlace::Global(crate::value::GlobalId::new(0)),
        ],
        &|buf, _, place| write_effect_place(buf, place),
    ));
    rows.extend(direct(
        "Producer",
        vec![
            Producer::TRust,
            Producer::Clean,
            Producer::TrustIr,
            Producer::TSwift,
            Producer::TC,
            Producer::Other("p".into()),
        ],
        &|buf, pool, producer| write_producer(buf, pool, producer),
    ));
    // The pass-mode tag encodes the whole `Option` too (v45, WS3.11):
    // `(none)` is UNRECORDED, which a consumer must not read as `Direct`.
    rows.push(TagRow {
        space: "PassMode",
        variant: "(none)".to_owned(),
        tag: encode(&(), &|buf, pool, ()| write_pass_mode(buf, pool, None))[0],
    });
    rows.extend(direct(
        "PassMode",
        vec![
            crate::PassMode::Ignore,
            crate::PassMode::Direct,
            crate::PassMode::Pair,
            crate::PassMode::Cast {
                pieces: vec![Ty::U64],
            },
            crate::PassMode::Indirect { on_stack: true },
        ],
        &|buf, pool, mode| write_pass_mode(buf, pool, Some(mode)),
    ));
    // The body-gate tag encodes the whole `Option`: `(none)` is "no licensing
    // claim", a spelling a consumer must keep distinct from `Ungated`.
    rows.push(TagRow {
        space: "BodyGate",
        variant: "(none)".to_owned(),
        tag: encode(&(), &|buf, pool, ()| write_body_gate(buf, pool, None))[0],
    });
    rows.extend(direct(
        "BodyGate",
        vec![
            crate::BodyGate::Ungated,
            crate::BodyGate::Gated {
                authority: "a".into(),
                evidence: None,
            },
        ],
        &|buf, pool, gate| write_body_gate(buf, pool, Some(gate)),
    ));
    // ONE Rust variant, TWO wire spellings (v61): an EVIDENCED license takes
    // its own tag so an older reader refuses it instead of dropping the
    // evidence. The writer picks the tag from the `evidence` field, which
    // `direct`'s debug head cannot tell apart; this sample is what makes the
    // census observe tag 3.
    let evidenced = crate::BodyGate::Gated {
        authority: "a".into(),
        evidence: Some(crate::GateEvidence {
            obligation: crate::value::ProofId::new(0),
            body_digest: ProofDigest::zero(),
        }),
    };
    rows.push(TagRow {
        space: "BodyGate",
        variant: "Gated{evidence}".to_owned(),
        tag: encode(&evidenced, &|buf, pool, gate| {
            write_body_gate(buf, pool, Some(gate));
        })[0],
    });
    {
        use crate::request::{NativeAdapterInput, NativeBundleProducer};
        rows.extend(direct(
            "NativeBundleProducer",
            vec![
                NativeBundleProducer::TRust,
                NativeBundleProducer::TSwift,
                NativeBundleProducer::TC,
                NativeBundleProducer::TrustIr,
                NativeBundleProducer::Clean,
            ],
            &|buf, _, producer| write_native_bundle_producer(buf, producer),
        ));
        rows.extend(direct(
            "NativeAdapterInput",
            vec![
                NativeAdapterInput::RustMir {
                    body_digest: ProofDigest::zero(),
                },
                NativeAdapterInput::TrustIrModule,
            ],
            &|buf, _, input| write_native_adapter_input(buf, input),
        ));
    }
    rows.extend(struct_repr_rows());
    rows.extend(type_origin_rows());
    rows.extend(enum_tag_repr_rows());
    rows.extend(enum_tag_encoding_rows());
    rows.extend(coverage_bound_rows());
    rows.extend(alloc_origin_rows());
    rows.extend(struct_passing_rows());
    rows.extend(source_place_rows());
    rows.extend(diagnostic_severity_rows());
    rows.extend(spec_rows());
    rows.sort();
    rows
}

/// Top-level variant names of `pub enum NAME { .. }` in `src` (the same parse
/// `tests/lean_schema_parity.rs` uses for the Rust<->Lean name gate).
///
/// A level-generic carrier (amendment S, `src/level.rs`) is declared as
/// `pub enum NAMEG<X> {` with `NAME` its level-R alias. Its `Ext` variant is
/// uninhabited at level R, so the census samples it through the TEMPLATE
/// writer (`X = TemplateRef`), and it stays on the list like every variant.
/// A carrier generic over the level with no level-R alias of its own (the
/// tensor map's `pub enum TensorMapNode<X> {`, v68, which only `InstG`
/// names) is read under its own name.
fn rust_enum_variants(src: &str, enum_name: &str) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    let plain = format!("pub enum {enum_name} {{");
    let generic = format!("pub enum {enum_name}G<X> {{");
    let parameterised = format!("pub enum {enum_name}<X> {{");
    let (start, needle) = match (
        src.find(&plain),
        src.find(&generic),
        src.find(&parameterised),
    ) {
        (Some(start), _, _) => (start, plain),
        (None, Some(start), _) => (start, generic),
        (None, None, Some(start)) => (start, parameterised),
        (None, None, None) => return out,
    };
    let level_generic = needle.ends_with("G<X> {");
    let mut depth: i32 = 0;
    for line in src[start + needle.len()..].lines() {
        let trimmed = line.trim_start();
        if depth == 0 && trimmed.starts_with(|c: char| c.is_ascii_uppercase()) {
            let end = trimmed
                .find(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
                .unwrap_or(trimmed.len());
            let rest = trimmed[end..].trim_start();
            if rest.is_empty() || rest.starts_with(['{', '(', ',']) {
                out.insert(trimmed[..end].to_owned());
            }
        }
        depth += i32::try_from(line.matches('{').count()).expect("small");
        depth -= i32::try_from(line.matches('}').count()).expect("small");
        if depth < 0 {
            break;
        }
    }
    let _ = level_generic;
    out
}

/// Declared variants of every registered tag space, read from the sources.
fn declared_variants() -> BTreeMap<&'static str, BTreeSet<String>> {
    let src_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    TAG_SPACES
        .iter()
        .map(|(space, file)| {
            let path = src_dir.join(file);
            let src = std::fs::read_to_string(&path)
                .unwrap_or_else(|error| panic!("read {}: {error}", path.display()));
            (*space, rust_enum_variants(&src, space))
        })
        .collect()
}

const TAG_STATUSES: [&str; 2] = ["landed", "reserved"];

fn check_enum_tags(
    registry: &Registry,
    census: &[TagRow],
    declared: &BTreeMap<&'static str, BTreeSet<String>>,
    version_status: &BTreeMap<u32, String>,
) -> Vec<String> {
    let mut errors = Vec::new();

    // 1. The census sampled every declared variant (so "every tag the codec
    //    writes" really is every tag), and invented none.
    for (space, variants) in declared {
        if variants.is_empty() {
            errors.push(format!(
                "{space}: could not parse `pub enum {space}` from its source"
            ));
            continue;
        }
        let sampled: BTreeSet<&str> = census
            .iter()
            .filter(|row| row.space == *space)
            // A second wire spelling of one Rust variant is labelled
            // `Variant.suffix` (`CmpXchg.weak`) or, for a spelling chosen by
            // a field's value, `Variant{field}` (`Gated{evidence}`); either
            // way it samples the declared variant before the separator.
            .map(|row| {
                row.variant
                    .split(['.', '{'])
                    .next()
                    .expect("split yields one")
            })
            .filter(|variant| !variant.starts_with('('))
            .collect();
        for variant in variants {
            let exempt = UNENCODABLE
                .iter()
                .any(|(s, v, _)| s == space && v == variant);
            if !exempt && !sampled.contains(variant.as_str()) {
                errors.push(format!(
                    "{space}::{variant} has no census sample: add one to \
                     binary/wire_census.rs (and its tag to wire-allocations.toml), or list it \
                     in UNENCODABLE with the reason it has no wire spelling"
                ));
            }
        }
        for variant in &sampled {
            if !variants.contains(*variant) {
                errors.push(format!(
                    "{space}::{variant} is sampled but not a declared variant"
                ));
            }
        }
    }
    for row in census {
        if !declared.contains_key(row.space) {
            errors.push(format!(
                "census space `{}` is missing from TAG_SPACES",
                row.space
            ));
        }
    }

    // 2. Registry rows: well-formed, grouped by enum, strictly increasing tags
    //    within a group — so two claims to one tag land on ADJACENT lines and
    //    git reports the collision as a textual conflict.
    let mut registered: BTreeMap<(String, u8), (String, String, usize)> = BTreeMap::new();
    let mut seen_variants: BTreeSet<(String, String)> = BTreeSet::new();
    let mut closed_groups: BTreeSet<String> = BTreeSet::new();
    let mut previous: Option<(String, u8)> = None;
    for row in registry.rows("enum_tag") {
        let parsed = (|| -> Result<(String, u8, String, String, u32), String> {
            row.only_keys(&["enum", "tag", "variant", "since", "status", "owner", "note"])?;
            let tag = u8::try_from(row.int("tag")?)
                .map_err(|_| format!("line {}: `tag` exceeds one byte", row.line))?;
            let since = u32::try_from(row.int("since")?)
                .map_err(|_| format!("line {}: `since` exceeds u32", row.line))?;
            let status = row.str("status")?;
            if !TAG_STATUSES.contains(&status) {
                return Err(format!(
                    "line {}: status `{status}` is not one of {TAG_STATUSES:?}",
                    row.line
                ));
            }
            Ok((
                row.str("enum")?.to_owned(),
                tag,
                row.str("variant")?.to_owned(),
                status.to_owned(),
                since,
            ))
        })();
        let (space, tag, variant, status, since) = match parsed {
            Ok(parsed) => parsed,
            Err(error) => {
                errors.push(error);
                continue;
            }
        };
        match &previous {
            Some((last_space, last_tag)) if *last_space == space => {
                if tag <= *last_tag {
                    errors.push(format!(
                        "line {}: {space} tag {tag} does not follow tag {last_tag} — tags are \
                         unique and strictly increasing within an enum (two variants can never \
                         share a tag)",
                        row.line
                    ));
                }
            }
            Some((last_space, _)) => {
                closed_groups.insert(last_space.clone());
                if closed_groups.contains(&space) {
                    errors.push(format!(
                        "line {}: rows of enum {space} must be contiguous",
                        row.line
                    ));
                }
            }
            None => {}
        }
        previous = Some((space.clone(), tag));
        if !seen_variants.insert((space.clone(), variant.clone())) {
            errors.push(format!(
                "line {}: {space}::{variant} has two rows",
                row.line
            ));
        }
        match version_status.get(&since).map(String::as_str) {
            Some("reserved") if status == "landed" => errors.push(format!(
                "line {}: {space}::{variant} is landed but its `since = {since}` is only reserved",
                row.line
            )),
            Some(_) => {}
            None => errors.push(format!(
                "line {}: `since = {since}` is not a registered wire version",
                row.line
            )),
        }
        registered.insert((space, tag), (variant, status, row.line));
    }

    // 3. Code -> registry: every tag the codec writes has a LANDED row.
    let mut written: BTreeMap<(String, u8), &str> = BTreeMap::new();
    for row in census {
        let key = (row.space.to_owned(), row.tag);
        if let Some(other) = written.insert(key.clone(), &row.variant) {
            errors.push(format!(
                "the codec writes tag {} for BOTH {}::{other} and {}::{}",
                row.tag, row.space, row.space, row.variant
            ));
        }
        match registered.get(&key) {
            Some((variant, status, line)) => {
                if variant != &row.variant {
                    errors.push(format!(
                        "line {line}: {} tag {} is registered to `{variant}` but the codec \
                         writes it for `{}`",
                        row.space, row.tag, row.variant
                    ));
                } else if status != "landed" {
                    errors.push(format!(
                        "line {line}: {}::{} is written by the codec — flip its row to \"landed\"",
                        row.space, row.variant
                    ));
                }
            }
            None => errors.push(format!(
                "the codec writes tag {tag} for {space}::{variant} but wire-allocations.toml has \
                 no row for it. Reserve FIRST (the protocol heads wire-allocations.toml); the row is:\n  \
                 {{ enum = \"{space}\", tag = {tag}, variant = \"{variant}\", since = <version>, \
                 status = \"landed\" }},",
                tag = row.tag,
                space = row.space,
                variant = row.variant
            )),
        }
    }
    // 4. Registry -> code: a LANDED row the codec does not write is stale. A
    //    RESERVED row needs no code — that is what a reservation is.
    for ((space, tag), (variant, status, line)) in &registered {
        if !declared.contains_key(space.as_str()) {
            errors.push(format!(
                "line {line}: enum `{space}` is not a census tag space (TAG_SPACES)"
            ));
        } else if status == "landed" && !written.contains_key(&(space.clone(), *tag)) {
            errors.push(format!(
                "line {line}: {space}::{variant} = {tag} is `landed` but the codec never writes it"
            ));
        }
    }
    errors
}

// ---------------------------------------------------------------------------
// Scan exemptions: what a completeness scan may ignore, and WHY
// ---------------------------------------------------------------------------

/// The `scan_exempt` rows. They live in the REGISTRY — not in a Rust const and
/// a Python tuple — so this census and `scripts/wire_alloc.py` cannot disagree
/// about one, and an exemption is one reviewable line with its reason on it.
#[derive(Debug, Default)]
struct Exemptions {
    /// `(prefix, line)`: versioned literals in a namespace ANOTHER repository
    /// allocates; this tree only spells them.
    literal_prefixes: Vec<(String, usize)>,
    /// `(enum, line)`: enums a closed tag match names that are NOT wire enums.
    tag_spaces: Vec<(String, usize)>,
}

/// TrustIr's OWN identity namespaces, in both historical spellings. Nothing
/// under them can be exempted: they are what the registry exists to allocate.
const OWN_NAMESPACES: [&str; 2] = ["trust_ir.", "trust-ir."];

fn parse_exemptions(registry: &Registry) -> (Exemptions, Vec<String>) {
    let mut exemptions = Exemptions::default();
    let mut errors = Vec::new();
    let mut previous: Option<(String, String)> = None;
    for row in registry.rows("scan_exempt") {
        let parsed = (|| -> Result<(String, String), String> {
            row.only_keys(&["scan", "name", "reason"])?;
            if row.str("reason")?.is_empty() {
                return Err(format!(
                    "line {}: an exemption must give its `reason`",
                    row.line
                ));
            }
            Ok((row.str("scan")?.to_owned(), row.str("name")?.to_owned()))
        })();
        let (scan, name) = match parsed {
            Ok(parsed) => parsed,
            Err(error) => {
                errors.push(error);
                continue;
            }
        };
        match scan.as_str() {
            "literal" => {
                let own = OWN_NAMESPACES
                    .iter()
                    .any(|own| own.starts_with(name.as_str()) || name.starts_with(own));
                if name.len() < 3 || !name.ends_with(['.', '-', ':']) {
                    errors.push(format!(
                        "line {}: a `literal` exemption is a NAMESPACE PREFIX — at least three \
                         characters, ending in `.`, `-` or `:` — not `{name}`",
                        row.line
                    ));
                } else if own {
                    errors.push(format!(
                        "line {}: `{name}` overlaps TrustIr's own namespace {OWN_NAMESPACES:?}, \
                         which this registry allocates; it cannot be exempted",
                        row.line
                    ));
                } else {
                    exemptions.literal_prefixes.push((name.clone(), row.line));
                }
            }
            "tag-space" => {
                if name.starts_with(|c: char| c.is_ascii_uppercase())
                    && name.chars().all(|c| c.is_ascii_alphanumeric())
                {
                    exemptions.tag_spaces.push((name.clone(), row.line));
                } else {
                    errors.push(format!(
                        "line {}: a `tag-space` exemption names a Rust enum, not `{name}`",
                        row.line
                    ));
                }
            }
            other => errors.push(format!(
                "line {}: scan `{other}` is not one of [\"literal\", \"tag-space\"]",
                row.line
            )),
        }
        if previous
            .as_ref()
            .is_some_and(|last| *last >= (scan.clone(), name.clone()))
        {
            errors.push(format!(
                "line {}: scan_exempt rows must be unique and sorted by (scan, name)",
                row.line
            ));
        }
        previous = Some((scan, name));
    }
    (exemptions, errors)
}

// ---------------------------------------------------------------------------
// Completeness: which tag spaces does the codec SPELL?
// ---------------------------------------------------------------------------
//
// `TAG_SPACES` above is a hand-kept list, and on the day it landed it was
// one short: `DiagnosticSeverity`, written inline with no writer of its own,
// had no row, and a wire-breaking re-tag of it passed every check. A
// behavioural census can only sample the spaces somebody TOLD it about, so
// the list itself needs a mechanical cross-check. This is it: the codec's
// source is scanned for every way it spells "a literal tag byte <-> an enum
// variant", in BOTH directions, and every enum so spelled must be registered.
//
//   * `tag_enum!(write, read, Enum, ..)` heads;
//   * REFUSAL ARMS: every `BinaryError::InvalidTag(..)` in production code
//     closes a tag match. The enclosing `match` either names the enum(s) it
//     decodes, or is a `0 => None / 1 => Some` presence byte, or — if it is
//     neither — is reported as unattributable (fail closed);
//   * WRITE ARMS: `Enum::Variant.. => <literal>` and
//     `Enum::Variant.. => write_u8(.., <literal>)`, on one line or with the
//     `write_u8` opening the arm's block.
//
// A space escapes only if it is absent from all three — see "Not covered" in
// docs/wire-allocation.md for what that leaves (a reader with no refusal arm
// whose writer computes its tag instead of spelling it).

fn indent_of(line: &str) -> usize {
    line.len() - line.trim_start().len()
}

/// `src` as lines with every `#[cfg(test)]` / `#[cfg(all(test, ..))]` MODULE
/// blanked (line numbers preserved). Test code is not in the artifact, so it
/// can spell nothing that ships. Only MODULES are blanked: any other
/// test-gated item stays in view, which can only fail closed. Relies on
/// rustfmt's layout (the closing brace sits at the item's own indentation),
/// which the `workspace-format` gate holds; an unclosed module is an error.
fn production_lines(src: &str) -> Result<Vec<&str>, String> {
    let lines: Vec<&str> = src.lines().collect();
    let mut out = lines.clone();
    let mut i = 0;
    while i < lines.len() {
        let trimmed = lines[i].trim();
        if trimmed == "#[cfg(test)]" || trimmed.starts_with("#[cfg(all(test,") {
            let indent = &lines[i][..indent_of(lines[i])];
            let mut j = i + 1;
            while lines
                .get(j)
                .is_some_and(|line| line.trim_start().starts_with("#["))
            {
                j += 1;
            }
            let module = lines
                .get(j)
                .and_then(|line| line.strip_prefix(indent))
                .map(|item| {
                    item.strip_prefix("pub(crate) ")
                        .or_else(|| item.strip_prefix("pub "))
                        .unwrap_or(item)
                })
                .and_then(|item| item.strip_prefix("mod "));
            let end = match module {
                Some(rest) if rest.ends_with(';') => Some(j),
                Some(rest) if rest.ends_with('{') => {
                    let close = format!("{indent}}}");
                    Some(
                        (j + 1..lines.len())
                            .find(|&k| lines[k] == close)
                            .ok_or_else(|| {
                                format!(
                                    "line {}: a test module is never closed at its own indentation",
                                    i + 1
                                )
                            })?,
                    )
                }
                _ => None,
            };
            if let Some(end) = end {
                for line in &mut out[i..=end] {
                    *line = "";
                }
                i = end + 1;
                continue;
            }
        }
        i += 1;
    }
    Ok(out)
}

/// What the codec source spells as a tag space.
#[derive(Debug, Default)]
struct TagSpaceScan {
    /// enum name -> 1-based line of the first evidence.
    spelled: BTreeMap<String, usize>,
    /// 1-based lines of closed tag matches that name no enum and are not
    /// presence bytes.
    unattributed: Vec<usize>,
}

/// `Left::Right` paths whose `Left` is never a wire enum.
const NOT_ENUM_PATHS: [&str; 2] = ["BinaryError", "Self"];

/// A level-generic carrier (amendment S) is spelled `TyG::` / `InstG::` /
/// `ConstantG::` in the generic codec; its tag space is the level-R alias.
const LEVEL_GENERIC: [(&str, &str); 3] =
    [("TyG", "Ty"), ("InstG", "Inst"), ("ConstantG", "Constant")];

/// The `Left` of every `Left::Right` in `text` whose two segments both start
/// uppercase: `crate::proof::DiagnosticSeverity::Note` -> `DiagnosticSeverity`.
fn enum_paths(text: &str) -> Vec<&str> {
    let bytes = text.as_bytes();
    let ident = |byte: u8| byte.is_ascii_alphanumeric() || byte == b'_';
    let mut out = Vec::new();
    let mut from = 0;
    while let Some(offset) = text[from..].find("::") {
        let at = from + offset;
        from = at + 2;
        let start = (0..at)
            .rev()
            .take_while(|&k| ident(bytes[k]))
            .last()
            .unwrap_or(at);
        let left = &text[start..at];
        if bytes.get(at + 2).is_some_and(u8::is_ascii_uppercase)
            && left.starts_with(|c: char| c.is_ascii_uppercase())
            && !NOT_ENUM_PATHS.contains(&left)
        {
            let space = LEVEL_GENERIC
                .iter()
                .find(|(generic, _)| *generic == left)
                .map_or(left, |(_, alias)| alias);
            out.push(space);
        }
    }
    out
}

/// `(literals, rhs)` of a match arm whose pattern is integer literals:
/// `0 => ..`, `1 | 2 => ..`, `3 if r.version >= 38 => ..`.
fn literal_arm(line: &str) -> Option<(Vec<&str>, &str)> {
    let (pattern, rhs) = line.trim().split_once("=>")?;
    let pattern = pattern.split(" if ").next()?;
    let literals: Vec<&str> = pattern.split('|').map(str::trim).collect();
    literals
        .iter()
        .all(|literal| !literal.is_empty() && literal.bytes().all(|b| b.is_ascii_digit()))
        .then_some((literals, rhs.trim()))
}

/// Does `text` open with `write_u8(<sink>, <integer literal>)`?
fn writes_literal_tag(text: &str) -> bool {
    text.strip_prefix("write_u8(")
        .and_then(|rest| rest.split_once(')'))
        .and_then(|(args, _)| args.rsplit_once(','))
        .is_some_and(|(_, last)| {
            let last = last.trim();
            !last.is_empty() && last.bytes().all(|b| b.is_ascii_digit())
        })
}

/// The header line of the `match` enclosing line `site`, stepping OUT one
/// block at a time so a `match` nested in an earlier arm is never mistaken
/// for the enclosing one.
fn enclosing_match(lines: &[&str], site: usize) -> Option<usize> {
    let mut level = indent_of(lines[site]);
    for j in (0..site).rev() {
        let line = lines[j];
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with("//") || indent_of(line) >= level {
            continue;
        }
        let is_match = trimmed.ends_with('{')
            && trimmed
                .split(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
                .any(|word| word == "match");
        if is_match {
            return Some(j);
        }
        level = indent_of(line);
        if level == 0 {
            return None;
        }
    }
    None
}

fn scan_tag_spaces(binary_src: &str) -> Result<TagSpaceScan, String> {
    let mut lines = production_lines(binary_src)?;
    // A `macro_rules!` body spells `$variant => $tag`, not a tag space; the
    // spaces a macro DEFINES are its invocation heads, handled below.
    let mut i = 0;
    while i < lines.len() {
        if lines[i].starts_with("macro_rules! ") {
            let end = (i + 1..lines.len())
                .find(|&k| lines[k] == "}")
                .ok_or_else(|| format!("line {}: `macro_rules!` is never closed", i + 1))?;
            for line in &mut lines[i..=end] {
                *line = "";
            }
            i = end;
        }
        i += 1;
    }

    let mut scan = TagSpaceScan::default();
    let mut spell = |name: &str, line: usize| {
        scan.spelled.entry(name.to_owned()).or_insert(line + 1);
    };
    let mut refusals = Vec::new();
    for (index, line) in lines.iter().enumerate() {
        let trimmed = line.trim();
        if trimmed.starts_with("//") {
            continue;
        }
        // 1. `tag_enum!(write_x, read_x, Enum,`
        if let Some(rest) = line.strip_prefix("tag_enum!(") {
            match rest.split(',').nth(2).map(str::trim) {
                Some(name) if !name.is_empty() => spell(name, index),
                _ => return Err(format!("line {}: unreadable `tag_enum!` head", index + 1)),
            }
        }
        // 2. refusal arms (the `Display` arm RENDERS the error; it refuses nothing)
        if trimmed.contains("BinaryError::InvalidTag(") && !trimmed.contains("=> write!(") {
            refusals.push(index);
        }
        // 3. write arms
        if let Some((pattern, rhs)) = trimmed.split_once(" => ") {
            let mut pattern = pattern;
            while let Some(inner) = pattern
                .strip_prefix("Some(")
                .or_else(|| pattern.strip_prefix('&'))
            {
                pattern = inner;
            }
            let leads_with_a_path = pattern
                .split(|c: char| !(c.is_ascii_alphanumeric() || c == '_' || c == ':'))
                .next()
                .unwrap_or("");
            let rhs = rhs.trim_end_matches(',');
            let literal = (!rhs.is_empty() && rhs.bytes().all(|b| b.is_ascii_digit()))
                || writes_literal_tag(rhs)
                || (rhs == "{"
                    && lines[index + 1..]
                        .iter()
                        .map(|next| next.trim())
                        .find(|next| !next.is_empty())
                        .is_some_and(writes_literal_tag));
            if literal && let Some(name) = enum_paths(leads_with_a_path).first() {
                spell(name, index);
            }
        }
    }
    for site in refusals {
        let Some(header) = enclosing_match(&lines, site) else {
            scan.unattributed.push(site + 1);
            continue;
        };
        let arm_indent = indent_of(lines[header]) + 4;
        let arms: Vec<(Vec<&str>, &str)> = lines[header + 1..site]
            .iter()
            .filter(|line| indent_of(line) == arm_indent)
            .filter_map(|line| literal_arm(line))
            .collect();
        let named: BTreeSet<&str> = lines[header..=site]
            .iter()
            .filter(|line| !line.trim_start().starts_with("//"))
            .flat_map(|line| enum_paths(line))
            .collect();
        let presence_byte = arms.len() == 2
            && arms[0].0 == ["0"]
            && arms[1].0 == ["1"]
            && ["None", "Ok(None)", "false", "Ok(false)"]
                .contains(&arms[0].1.trim_end_matches(','));
        if !named.is_empty() {
            for name in named {
                scan.spelled.entry(name.to_owned()).or_insert(header + 1);
            }
        } else if !presence_byte {
            scan.unattributed.push(site + 1);
        }
    }
    Ok(scan)
}

fn registered_tag_spaces(registry: &Registry) -> BTreeSet<String> {
    registry
        .rows("enum_tag")
        .iter()
        .filter_map(|row| row.str("enum").ok().map(str::to_owned))
        .collect()
}

fn check_tag_space_completeness(
    scan: &TagSpaceScan,
    registered: &BTreeSet<String>,
    exemptions: &Exemptions,
) -> Vec<String> {
    let mut errors = Vec::new();
    let exempt = |name: &str| exemptions.tag_spaces.iter().any(|(e, _)| e == name);
    for (name, line) in &scan.spelled {
        if !registered.contains(name) && !exempt(name) {
            errors.push(format!(
                "binary.rs:{line}: the codec matches a literal tag byte to or from `{name}::..`, \
                 but `{name}` is not a registered tag space. Register every tag it writes in \
                 wire-allocations.toml and give it a probe and a TAG_SPACES row in \
                 binary/wire_census.rs. If `{name}` is NOT a wire enum, say so:\n  \
                 {{ scan = \"tag-space\", name = \"{name}\", reason = \"<why>\" }},"
            ));
        }
    }
    for line in &scan.unattributed {
        errors.push(format!(
            "binary.rs:{line}: a closed tag match (it refuses unknown bytes with `InvalidTag`) \
             names no enum and is not a `0 => None / 1 => Some` presence byte, so the census \
             cannot tell which tag space it decodes. Name the enum in the match arms."
        ));
    }
    // The scanner guards the list; this guards the scanner. If it stops
    // seeing a space that IS registered, its patterns have rotted and its
    // silence about everything else means nothing.
    for name in registered {
        if !scan.spelled.contains_key(name) {
            errors.push(format!(
                "the tag-space scan no longer sees `{name}`, a registered tag space: the way \
                 binary.rs spells it has left the scanner's patterns (scan_tag_spaces), so the \
                 scan can no longer vouch that NO space is missing"
            ));
        }
    }
    for (name, line) in &exemptions.tag_spaces {
        if registered.contains(name) || !scan.spelled.contains_key(name) {
            errors.push(format!(
                "line {line}: the `tag-space` exemption for `{name}` exempts nothing (it is \
                 registered, or binary.rs no longer spells it): delete the row"
            ));
        }
    }
    errors
}

// ---------------------------------------------------------------------------
// Namespace 3: digest domains
// ---------------------------------------------------------------------------

const DOMAIN_STATUSES: [&str; 3] = ["burned", "landed", "reserved"];

/// The characters a versioned identity is spelled in. `@` and `:` are here
/// for `@trust-internal::<name>-vN`, so such a name is seen WHOLE and an
/// exemption can address its namespace.
fn identity_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || matches!(c, '.' | '_' | '-' | '@' | ':')
}

/// Split a versioned identity at its version suffix: `trust_ir.a.b.v7` ->
/// (`trust_ir.a.b`, '.', 7); `TIR-SATRES-v1` -> (`TIR-SATRES`, '-', 1).
fn split_literal(full: &str) -> Option<(&str, char, u32)> {
    let digits = full.bytes().rev().take_while(u8::is_ascii_digit).count();
    let head = full[..full.len() - digits].strip_suffix('v')?;
    let sep = head
        .chars()
        .next_back()
        .filter(|c| matches!(c, '.' | '-'))?;
    let version = full[full.len() - digits..].parse().ok()?;
    let domain = &head[..head.len() - 1];
    domain
        .chars()
        .all(identity_char)
        .then_some((domain, sep, version))
}

/// Every VERSIONED IDENTITY spelled in `src`: a run of identity characters
/// ending in `.vN` or `-vN`, directly before a closing `"` (or before the
/// `\0` that terminates a byte-string magic).
///
/// CLOSED WORLD, anchored on the SUFFIX. The first scanner was anchored on the
/// prefix `"trust_ir.` and so was blind to every other spelling of the same
/// thing: `trust-ir.satres.cnf.v2` (already bumped once), the root separator
/// `trust-ir.sha256-domain.v1`, the `TIR-SATRES-v1` magic — and to a domain
/// assembled with `concat!` from a `"trust_ir"` head and a version-suffixed
/// tail. Here a FRAGMENT that ends in a version is itself a finding, because
/// nothing registers it. Doc comments count: a documented identity is a
/// claimed one (this comment had to be reworded for exactly that reason).
fn scan_versioned_literals(src: &str, out: &mut BTreeSet<String>) {
    for line in src.lines() {
        for (quote, _) in line.match_indices('"') {
            let head = &line[..quote];
            let head = head.strip_suffix("\\0").unwrap_or(head);
            let start = head
                .char_indices()
                .rev()
                .take_while(|(_, c)| identity_char(*c))
                .last()
                .map_or(head.len(), |(index, _)| index);
            let run = &head[start..];
            // `trust_ir.test.*` is the unallocated scratch namespace for tests.
            if split_literal(run).is_some() && !run.starts_with("trust_ir.test.") {
                out.insert(run.to_owned());
            }
        }
    }
}

/// Versioned identities spelled anywhere under `crates/*/src` and
/// `frontend/src`, skipping `tests.rs` files, `tests/` directories and inline
/// test MODULES (a negative test may spell a stale or deliberately wrong one;
/// test code is not in the artifact).
fn scan_source_domains() -> BTreeSet<String> {
    fn walk(dir: &Path, out: &mut BTreeSet<String>) {
        let mut entries: Vec<_> = std::fs::read_dir(dir)
            .unwrap_or_else(|error| panic!("read_dir {}: {error}", dir.display()))
            .map(|entry| entry.expect("dir entry").path())
            .collect();
        entries.sort();
        for path in entries {
            let name = path
                .file_name()
                .and_then(|name| name.to_str())
                .unwrap_or("");
            if path.is_dir() {
                if name != "tests" {
                    walk(&path, out);
                }
            } else if name.ends_with(".rs") && name != "tests.rs" {
                let src = std::fs::read_to_string(&path)
                    .unwrap_or_else(|error| panic!("read {}: {error}", path.display()));
                let production = production_lines(&src)
                    .unwrap_or_else(|error| panic!("{}: {error}", path.display()));
                scan_versioned_literals(&production.join("\n"), out);
            }
        }
    }
    let mut out = BTreeSet::new();
    let crates = repo_root().join("crates");
    let mut members: Vec<_> = std::fs::read_dir(&crates)
        .expect("read crates/")
        .map(|entry| entry.expect("dir entry").path().join("src"))
        .filter(|src| src.is_dir())
        .collect();
    members.sort();
    // `frontend/` is a workspace-EXCLUDED crate that shares this namespace.
    members.push(repo_root().join("frontend/src"));
    for src in members.iter().filter(|src| src.is_dir()) {
        walk(src, &mut out);
    }
    out
}

fn check_digest_domains(registry: &Registry, spelled: &BTreeSet<String>) -> Vec<String> {
    let (exemptions, mut errors) = parse_exemptions(registry);
    let mut registered: BTreeMap<String, (String, usize)> = BTreeMap::new();
    let mut seps: BTreeMap<String, char> = BTreeMap::new();
    let mut reserved: Vec<(String, char, usize)> = Vec::new();
    let mut landed_domains: BTreeSet<String> = BTreeSet::new();
    let mut previous: Option<(String, u32)> = None;
    for row in registry.rows("digest_domain") {
        let parsed = (|| -> Result<(String, u32, char, String), String> {
            row.only_keys(&[
                "domain", "version", "sep", "status", "binds", "owner", "note",
            ])?;
            let version = u32::try_from(row.int("version")?)
                .map_err(|_| format!("line {}: `version` exceeds u32", row.line))?;
            let status = row.str("status")?;
            if !DOMAIN_STATUSES.contains(&status) {
                return Err(format!(
                    "line {}: status `{status}` is not one of {DOMAIN_STATUSES:?}",
                    row.line
                ));
            }
            if row.str("binds")?.is_empty() {
                return Err(format!(
                    "line {}: `binds` must say what the digest binds",
                    row.line
                ));
            }
            // The literal is `<domain><sep>v<version>`; `sep` is `.` unless a
            // legacy `-vN` spelling says otherwise.
            let sep = match row.opt_str("sep")? {
                None => '.',
                Some("-") => '-',
                Some(other) => {
                    return Err(format!(
                        "line {}: `sep` is \"-\" or absent (meaning \".\"), not \"{other}\"",
                        row.line
                    ));
                }
            };
            Ok((
                row.str("domain")?.to_owned(),
                version,
                sep,
                status.to_owned(),
            ))
        })();
        let (domain, version, sep, status) = match parsed {
            Ok(parsed) => parsed,
            Err(error) => {
                errors.push(error);
                continue;
            }
        };
        let full = format!("{domain}{sep}v{version}");
        if domain.is_empty() || split_literal(&full) != Some((domain.as_str(), sep, version)) {
            errors.push(format!(
                "line {}: `{full}` is not a `<name>.vN` / `<name>-vN` identity",
                row.line
            ));
        }
        if *seps.entry(domain.clone()).or_insert(sep) != sep {
            errors.push(format!(
                "line {}: `{domain}` is spelled with two different separators",
                row.line
            ));
        }
        if status == "reserved" {
            reserved.push((domain.clone(), sep, row.line));
        } else {
            landed_domains.insert(domain.clone());
        }
        // Sorted by (domain, version): two claims to the next version of one
        // domain land on adjacent lines.
        if previous
            .as_ref()
            .is_some_and(|last| *last >= (domain.clone(), version))
        {
            errors.push(format!(
                "line {}: digest_domain rows must be unique and sorted by (domain, version)",
                row.line
            ));
        }
        previous = Some((domain, version));
        registered.insert(full, (status, row.line));
    }
    // A NEW name is canonical. The `trust-ir.` / `-vN` spellings are registered
    // because they already exist and their counters must be locked too — not
    // because anybody should mint another.
    for (domain, sep, line) in &reserved {
        if !landed_domains.contains(domain) && !(domain.starts_with("trust_ir.") && *sep == '.') {
            errors.push(format!(
                "line {line}: a NEW identity is spelled `trust_ir.<dotted.name>.vN`, not \
                 `{domain}`: only a bump of an existing legacy-spelled name keeps its spelling"
            ));
        }
    }
    let mut used: BTreeSet<&str> = BTreeSet::new();
    for full in spelled {
        if let Some((prefix, _)) = exemptions
            .literal_prefixes
            .iter()
            .find(|(prefix, _)| full.starts_with(prefix.as_str()))
        {
            used.insert(prefix);
            continue;
        }
        match registered.get(full) {
            Some((status, line)) if status != "landed" => errors.push(format!(
                "line {line}: `{full}` is spelled in the sources but its row is `{status}` — \
                 flip it to \"landed\" (a burned domain version must never be spelled again)"
            )),
            Some(_) => {}
            None => errors.push(format!(
                "the sources spell the versioned identity `{full}` but wire-allocations.toml has \
                 no digest_domain row for it. Reserve FIRST (the protocol heads that file). A \
                 version-suffixed FRAGMENT counts: an identity assembled with `concat!` or \
                 `format!` is one nobody can register. If another repository allocates this \
                 name, exempt its namespace:\n  \
                 {{ scan = \"literal\", name = \"<namespace prefix>\", reason = \"<who allocates it>\" }},"
            )),
        }
    }
    for (full, (status, line)) in &registered {
        if status == "landed" && !spelled.contains(full) {
            errors.push(format!(
                "line {line}: `{full}` is `landed` but no source spells it (retire it as \
                 \"burned\": a digest-domain version is never reused)"
            ));
        }
    }
    for (prefix, line) in &exemptions.literal_prefixes {
        if !used.contains(prefix.as_str()) {
            errors.push(format!(
                "line {line}: the `literal` exemption `{prefix}` exempts nothing the sources \
                 spell: delete the row"
            ));
        }
    }
    errors
}

// ---------------------------------------------------------------------------
// The gate
// ---------------------------------------------------------------------------

fn version_statuses(registry: &Registry) -> BTreeMap<u32, String> {
    registry
        .rows("wire_version")
        .iter()
        .filter_map(|row| {
            let number = u32::try_from(row.int("number").ok()?).ok()?;
            Some((number, row.str("status").ok()?.to_owned()))
        })
        .collect()
}

fn assert_clean(what: &str, errors: &[String]) {
    assert!(
        errors.is_empty(),
        "wire-allocations.toml disagrees with the code ({what}):\n  - {}\n\
         The registry is the allocation lock's data; the protocol heads that file.",
        errors.join("\n  - ")
    );
}

const BINARY_SRC: &str = include_str!("../binary.rs");

#[test]
fn registry_has_exactly_the_three_namespaces_and_the_exemption_table() {
    let registry = load_registry();
    let tables: Vec<&str> = registry.tables.keys().map(String::as_str).collect();
    assert_eq!(
        tables,
        ["digest_domain", "enum_tag", "scan_exempt", "wire_version"]
    );
}

#[test]
fn every_wire_version_is_registered_and_its_status_is_what_the_reader_does() {
    let errors = check_wire_versions(&load_registry(), BINARY_SRC, &reader_accepts_header);
    assert_clean("wire versions", &errors);
}

#[test]
fn every_tag_the_codec_writes_is_registered_and_no_two_variants_share_one() {
    let registry = load_registry();
    // `TRUST_IR_WIRE_CENSUS_DUMP=<path>` writes the observed census as
    // `enum<TAB>tag<TAB>variant` lines — what the registry was backfilled from.
    if let Some(path) = std::env::var_os("TRUST_IR_WIRE_CENSUS_DUMP") {
        let dump: String = codec_tag_census()
            .iter()
            .map(|row| format!("{}\t{}\t{}\n", row.space, row.tag, row.variant))
            .collect();
        std::fs::write(&path, dump).expect("write census dump");
    }
    let errors = check_enum_tags(
        &registry,
        &codec_tag_census(),
        &declared_variants(),
        &version_statuses(&registry),
    );
    assert_clean("enum tags", &errors);
}

fn real_version_ledger_text() -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join(VERSION_LEDGER_RELATIVE);
    std::fs::read_to_string(&path).unwrap_or_else(|error| {
        panic!(
            "{} could not be read ({error}). It is the OTHER wire-version ledger and this              registry is bound to it; if it was retired, retire              `check_the_version_ledgers_agree` (and `wire_alloc.py`'s half) with it.",
            path.display()
        )
    })
}

#[test]
fn the_two_wire_version_ledgers_agree_number_by_number() {
    let errors = check_the_version_ledgers_agree(&load_registry(), &real_version_ledger_text());
    assert_clean("the two wire-version ledgers", &errors);
}

/// The race two UNBOUND locks permit, in both directions, and a status the
/// two files tell differently. Each passed every live check of both gates
/// before the binding (measured with v44 given to two owners, one per file).
#[test]
fn mutation_a_reservation_in_only_one_ledger_is_refused() {
    let registry = load_registry();
    let tsv = real_version_ledger_text();
    let next = next_free_version(&registry);

    let theirs_only = format!("{tsv}{next}\treserved\tline-b\tself\tWS9.9\n");
    let errors = check_the_version_ledgers_agree(&registry, &theirs_only);
    assert!(
        errors.len() == 1
            && errors[0].contains(&format!("wire v{next} is `reserved` in wire_versions.tsv"))
            && errors[0].contains("NO row in wire-allocations.toml")
            && errors[0].contains("wire_alloc.py sync"),
        "{errors:?}"
    );

    let ours_only = parse_registry(&append_row(
        &real_registry_text(),
        "wire_version",
        &format!(
            "{{ number = {next}, feature = \"line-a\", status = \"reserved\", owner = \"a\", \
             date = \"2026-09-18\" }}"
        ),
    ))
    .expect("parses");
    let errors = check_the_version_ledgers_agree(&ours_only, &tsv);
    assert!(
        errors.len() == 1 && errors[0].contains("NO row in wire_versions.tsv"),
        "{errors:?}"
    );

    // Reserved in BOTH — for DIFFERENT holders. This is the race itself, and
    // the one shape a number-and-status comparison calls agreement: session
    // one hand-edits this registry, session two hand-edits the other ledger,
    // and the merge is green. (An earlier draft of this test asserted exactly
    // that, as "bound and green".)
    let errors = check_the_version_ledgers_agree(&ours_only, &theirs_only);
    assert!(
        errors.len() == 1
            && errors[0].contains("reserved in BOTH ledgers, for different holders")
            && errors[0].contains("owner `a`")
            && errors[0].contains("owner `WS9.9`"),
        "{errors:?}"
    );
    // One holder, named the same way in both: bound and green. The constant
    // must be NAMED by the other ledger's feature text, as a whole identifier.
    let held = |constant: &str| {
        parse_registry(&append_row(
            &real_registry_text(),
            "wire_version",
            &format!(
                "{{ number = {next}, feature = \"line-b\", constant = \"{constant}\", \
                 status = \"reserved\", owner = \"WS9.9\", date = \"2026-09-18\" }}"
            ),
        ))
        .expect("parses")
    };
    let theirs = format!("{tsv}{next}\treserved\tline-b: LINE_B_FORMAT_VERSION\tself\tWS9.9\n");
    assert_eq!(
        check_the_version_ledgers_agree(&held("LINE_B_FORMAT_VERSION"), &theirs),
        Vec::<String>::new()
    );
    let errors = check_the_version_ledgers_agree(&held("B_FORMAT_VERSION"), &theirs);
    assert!(
        errors.len() == 1 && errors[0].contains("constant `B_FORMAT_VERSION`"),
        "a suffix of the named constant is not the constant: {errors:?}"
    );

    let retold = tsv.replacen("\trefused\t", "\tshipped\t", 1);
    assert_ne!(retold, tsv);
    let errors = check_the_version_ledgers_agree(&registry, &retold);
    assert!(
        errors.len() == 1
            && errors[0].contains("says `burned`")
            && errors[0].contains("says `landed`"),
        "{errors:?}"
    );
}

/// The census above samples the tag spaces in `TAG_SPACES` — a hand-kept list.
/// This is the check that the LIST is complete: every enum the codec source
/// matches to or from a literal tag byte is a registered space.
#[test]
fn every_tag_space_the_codec_spells_is_registered() {
    let registry = load_registry();
    let (exemptions, _) = parse_exemptions(&registry);
    let scan = scan_tag_spaces(BINARY_SRC).expect("binary.rs scans");
    let errors =
        check_tag_space_completeness(&scan, &registered_tag_spaces(&registry), &exemptions);
    assert_clean("tag-space completeness", &errors);
    // Not vacuous: the scan must be looking at real refusal arms.
    assert!(
        scan.spelled.len() >= TAG_SPACES.len(),
        "the scan saw {} tag spaces, fewer than the {} in TAG_SPACES",
        scan.spelled.len(),
        TAG_SPACES.len()
    );
}

#[test]
fn every_versioned_identity_string_in_the_sources_is_registered() {
    let errors = check_digest_domains(&load_registry(), &scan_source_domains());
    assert_clean("digest domains", &errors);
}

/// Insert `row` as the last row of `table`.
fn append_row(text: &str, table: &str, row: &str) -> String {
    let mut out = Vec::new();
    let mut inside = false;
    let mut inserted = false;
    for line in text.lines() {
        if line == format!("{table} = [") {
            inside = true;
        } else if inside && line == "]" {
            out.push(format!("  {row},"));
            inside = false;
            inserted = true;
        }
        out.push(line.to_owned());
    }
    assert!(inserted, "table `{table}` not found");
    out.join("\n") + "\n"
}

/// Insert `row` directly after the last registry line containing `needle`.
fn insert_after_last(text: &str, needle: &str, row: &str) -> String {
    let lines: Vec<&str> = text.lines().collect();
    let at = lines
        .iter()
        .rposition(|line| line.contains(needle))
        .unwrap_or_else(|| panic!("no registry line contains `{needle}`"));
    let mut out: Vec<String> = lines.iter().map(|line| (*line).to_owned()).collect();
    out.insert(at + 1, format!("  {row},"));
    out.join("\n") + "\n"
}

fn next_free_version(registry: &Registry) -> u32 {
    version_statuses(registry)
        .keys()
        .next_back()
        .expect("registry has wire versions")
        + 1
}

fn next_free_tag(registry: &Registry, space: &str) -> u64 {
    registry
        .rows("enum_tag")
        .iter()
        .filter(|row| row.str("enum") == Ok(space))
        .map(|row| row.int("tag").expect("tag"))
        .max()
        .expect("space has rows")
        + 1
}

/// A reservation lands FIRST, with no code behind it. This is the property
/// the whole protocol rests on, so it is pinned: a reserved row in EACH
/// namespace, added to the real registry, keeps every check green.
#[test]
fn a_reservation_with_no_code_behind_it_is_accepted() {
    let text = real_registry_text();
    let real = parse_registry(&text).expect("registry parses");
    let version = next_free_version(&real);
    let tag = next_free_tag(&real, "Ty");
    let reserved = append_row(
        &text,
        "wire_version",
        &format!(
            "{{ number = {version}, feature = \"census-probe\", constant = \
             \"CENSUS_PROBE_FORMAT_VERSION\", status = \"reserved\", owner = \"probe\", \
             date = \"2026-09-18\" }}"
        ),
    );
    let reserved = insert_after_last(
        &reserved,
        "{ enum = \"Ty\",",
        &format!(
            "{{ enum = \"Ty\", tag = {tag}, variant = \"CensusProbe\", since = {version}, \
             status = \"reserved\", owner = \"probe\" }}"
        ),
    );
    let reserved = append_row(
        &reserved,
        "digest_domain",
        "{ domain = \"trust_ir.zz_census_probe\", version = 1, status = \"reserved\", \
         binds = \"nothing: a probe\", owner = \"probe\" }",
    );
    let registry = parse_registry(&reserved).expect("reserved registry parses");
    assert_eq!(
        registry.rows("wire_version").len(),
        real.rows("wire_version").len() + 1
    );
    assert_eq!(
        check_wire_versions(&registry, BINARY_SRC, &reader_accepts_header),
        Vec::<String>::new()
    );
    assert_eq!(
        check_enum_tags(
            &registry,
            &codec_tag_census(),
            &declared_variants(),
            &version_statuses(&registry),
        ),
        Vec::<String>::new()
    );
    assert_eq!(
        check_digest_domains(&registry, &scan_source_domains()),
        Vec::<String>::new()
    );
}

/// Two lines that both take "the next number" must collide LOUDLY. In the
/// registry that means: the second claim is a checked error, never a silent
/// second owner.
#[test]
fn a_second_claim_to_a_taken_number_is_refused_in_every_namespace() {
    let text = real_registry_text();
    let real = parse_registry(&text).expect("registry parses");

    let taken = next_free_version(&real) - 1;
    let registry = parse_registry(&append_row(
        &text,
        "wire_version",
        &format!(
            "{{ number = {taken}, feature = \"second-claim\", status = \"reserved\", \
             owner = \"probe\", date = \"2026-09-18\" }}"
        ),
    ))
    .expect("parses");
    let errors = check_wire_versions(&registry, BINARY_SRC, &reader_accepts_header);
    assert!(
        errors.iter().any(|error| error.contains("gap-free")),
        "{errors:?}"
    );

    let taken = next_free_tag(&real, "Ty") - 1;
    let registry = parse_registry(&insert_after_last(
        &text,
        "{ enum = \"Ty\",",
        &format!(
            "{{ enum = \"Ty\", tag = {taken}, variant = \"SecondClaim\", since = 43, \
             status = \"reserved\", owner = \"probe\" }}"
        ),
    ))
    .expect("parses");
    let errors = check_enum_tags(
        &registry,
        &codec_tag_census(),
        &declared_variants(),
        &version_statuses(&registry),
    );
    assert!(
        errors.iter().any(|error| error.contains("does not follow")),
        "{errors:?}"
    );

    let registry = parse_registry(&insert_after_last(
        &text,
        "domain = \"trust_ir.obligation.digest\", version = 6,",
        "{ domain = \"trust_ir.obligation.digest\", version = 6, status = \"reserved\", \
         binds = \"a second claim\", owner = \"probe\" }",
    ))
    .expect("parses");
    let errors = check_digest_domains(&registry, &scan_source_domains());
    assert!(
        errors
            .iter()
            .any(|error| error.contains("unique and sorted")),
        "{errors:?}"
    );
}

// --- Mutation tests: a missing row FAILS. Each one doctors either the code's
// --- observed facts or the registry, and asserts the named refusal.

fn real_registry_text() -> String {
    std::fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join(REGISTRY_RELATIVE))
        .expect("read registry")
}

fn drop_line_containing(text: &str, needle: &str) -> String {
    let kept: Vec<&str> = text.lines().filter(|line| !line.contains(needle)).collect();
    assert_eq!(
        kept.len() + 1,
        text.lines().count(),
        "`{needle}` must match exactly one registry line"
    );
    kept.join("\n") + "\n"
}

#[test]
fn mutation_a_new_version_constant_without_a_row_is_refused() {
    let registry = load_registry();
    let doctored = format!(
        "{BINARY_SRC}\npub const SNEAKED_IN_FORMAT_VERSION: u32 = {};\n",
        next_free_version(&registry)
    );
    let errors = check_wire_versions(&registry, &doctored, &reader_accepts_header);
    assert!(
        errors
            .iter()
            .any(|error| error.contains("SNEAKED_IN_FORMAT_VERSION")
                && error.contains("no `landed`")),
        "{errors:?}"
    );
}

#[test]
fn mutation_a_version_bump_without_a_row_is_refused() {
    // Bump to the first UNALLOCATED number (derived, so this test does not
    // break when the next version is legitimately reserved or landed).
    let registry = load_registry();
    let bumped = next_free_version(&registry);
    let doctored = BINARY_SRC.replace(
        &format!("pub const VERSION: u32 = {VERSION};"),
        &format!("pub const VERSION: u32 = {bumped};"),
    );
    assert_ne!(doctored, BINARY_SRC);
    // A reader that accepts the bumped header too, as the bumped code would.
    let accepts = |version: u32| version == bumped || reader_accepts_header(version);
    let errors = check_wire_versions(&registry, &doctored, &accepts);
    assert!(
        errors.iter().any(|error| error.contains("UNALLOCATED")),
        "{errors:?}"
    );
}

#[test]
fn mutation_a_dropped_version_row_is_refused() {
    let registry = parse_registry(&drop_line_containing(
        &real_registry_text(),
        "constant = \"HANDLE_TYPE_FORMAT_VERSION\"",
    ))
    .expect("parses");
    let errors = check_wire_versions(&registry, BINARY_SRC, &reader_accepts_header);
    assert!(
        errors
            .iter()
            .any(|error| error.contains("HANDLE_TYPE_FORMAT_VERSION")),
        "{errors:?}"
    );
}

#[test]
fn mutation_a_new_tag_without_a_row_is_refused() {
    let registry = load_registry();
    let tag = u8::try_from(next_free_tag(&registry, "Ty")).expect("one byte");
    let mut census = codec_tag_census();
    census.push(TagRow {
        space: "Ty",
        variant: "Handle.sneaked".to_owned(),
        tag,
    });
    let errors = check_enum_tags(
        &registry,
        &census,
        &declared_variants(),
        &version_statuses(&registry),
    );
    assert!(
        errors
            .iter()
            .any(|error| error.contains(&format!("writes tag {tag} for Ty::Handle.sneaked"))),
        "{errors:?}"
    );
}

#[test]
fn mutation_a_dropped_tag_row_is_refused() {
    let registry = parse_registry(&drop_line_containing(
        &real_registry_text(),
        "enum = \"Ty\", tag = 38,",
    ))
    .expect("parses");
    let errors = check_enum_tags(
        &registry,
        &codec_tag_census(),
        &declared_variants(),
        &version_statuses(&registry),
    );
    assert!(
        errors
            .iter()
            .any(|error| error.contains("writes tag 38 for Ty::Handle")),
        "{errors:?}"
    );
}

#[test]
fn mutation_two_variants_sharing_a_tag_is_refused() {
    let registry = load_registry();
    let mut census = codec_tag_census();
    let handle = census
        .iter_mut()
        .find(|row| row.space == "Ty" && row.variant == "Handle")
        .expect("Ty::Handle is sampled");
    handle.tag = 37; // Ty::Dialect's tag
    let errors = check_enum_tags(
        &registry,
        &census,
        &declared_variants(),
        &version_statuses(&registry),
    );
    assert!(
        errors.iter().any(|error| error.contains("for BOTH")),
        "{errors:?}"
    );
}

#[test]
fn mutation_a_new_variant_without_a_census_sample_is_refused() {
    let registry = load_registry();
    let mut declared = declared_variants();
    declared
        .get_mut("Ty")
        .expect("Ty is a tag space")
        .insert("Sneaked".to_owned());
    let errors = check_enum_tags(
        &registry,
        &codec_tag_census(),
        &declared,
        &version_statuses(&registry),
    );
    assert!(
        errors
            .iter()
            .any(|error| error.contains("Ty::Sneaked has no census sample")),
        "{errors:?}"
    );
}

#[test]
fn mutation_a_new_digest_domain_without_a_row_is_refused() {
    // Built, not spelled: a literal here would itself be a domain string in
    // the sources, and the scanner would (rightly) demand a row for it. The
    // number is DERIVED — one past the highest registered version of the
    // domain — so a later landing (v7 landed with wire v46) does not turn
    // this mutation into a registered spelling.
    let registry = load_registry();
    let next = registry
        .rows("digest_domain")
        .iter()
        .filter(|row| row.str("domain") == Ok("trust_ir.obligation.digest"))
        .filter_map(|row| row.int("version").ok())
        .max()
        .expect("the obligation digest domain is registered")
        + 1;
    let sneaked = format!("trust_ir.obligation.digest.v{next}");
    let mut spelled = scan_source_domains();
    spelled.insert(sneaked.clone());
    let errors = check_digest_domains(&registry, &spelled);
    assert!(
        errors.iter().any(|error| error.contains(&sneaked)),
        "{errors:?}"
    );
}

#[test]
fn mutation_respelling_a_burned_digest_domain_is_refused() {
    // `obligation.digest.v5` was claimed by two lines at once; it is burned.
    let mut spelled = scan_source_domains();
    spelled.insert(format!("trust_ir.obligation.digest.v{}", 5));
    let errors = check_digest_domains(&load_registry(), &spelled);
    assert!(
        errors.iter().any(|error| error.contains("burned")),
        "{errors:?}"
    );
}

#[test]
fn the_domain_scanner_sees_doc_comments_and_skips_the_test_namespace() {
    let mut found = BTreeSet::new();
    scan_versioned_literals(
        "/// domain `\"trust_ir.module.v2\"`\nlet d = \"trust_ir.test.scratch.v1\";\n\
         let e = \"trust_ir.not_a_domain\";",
        &mut found,
    );
    assert_eq!(
        found.into_iter().collect::<Vec<_>>(),
        ["trust_ir.module.v2"]
    );
}

// --- The completeness scans. The list of tag spaces and the spelling of a
// --- digest domain were both HAND ENUMERATIONS, and an adversarial review
// --- (2026-09-18) walked through each: a live tag space with no row, and
// --- seven versioned identities outside the scanned prefix. Each test below
// --- is one of those bypasses, and fails without the scan that closed it.

fn registry_without_lines_containing(needle: &str) -> Registry {
    let text = real_registry_text();
    let kept: Vec<&str> = text.lines().filter(|line| !line.contains(needle)).collect();
    assert!(
        kept.len() < text.lines().count(),
        "`{needle}` matches no line"
    );
    parse_registry(&(kept.join("\n") + "\n")).expect("parses")
}

/// THE bypass, against the real `binary.rs`: `DiagnosticSeverity` is written
/// and read inline, and with no rows for it nothing used to notice.
#[test]
fn mutation_a_live_tag_space_with_no_rows_is_refused() {
    let registry = registry_without_lines_containing("enum = \"DiagnosticSeverity\"");
    let (exemptions, _) = parse_exemptions(&registry);
    let scan = scan_tag_spaces(BINARY_SRC).expect("binary.rs scans");
    let errors =
        check_tag_space_completeness(&scan, &registered_tag_spaces(&registry), &exemptions);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(
        errors[0].contains("`DiagnosticSeverity` is not a registered tag space"),
        "{errors:?}"
    );
}

const SNEAKED_READER: &str = "
fn read_sneaked(r: &mut Reader<'_>) -> Result<Sneaked, BinaryError> {
    let sneaked = match r.read_u8()? {
        0 => {
            let payload = r.read_u64()?;
            Sneaked::Wide(payload)
        }
        1 => Sneaked::Narrow,
        t => return Err(BinaryError::InvalidTag(t)),
    };
    Ok(sneaked)
}
";

const SNEAKED_WRITER: &str = "
fn write_sneaked(buf: &mut impl BinarySink, value: &Sneaked) {
    match value {
        crate::sneaky::Sneaked::Wide(payload) => {
            write_u8(buf, 0);
            write_u64(buf, *payload);
        }
        crate::sneaky::Sneaked::Narrow => write_u8(buf, 1),
    }
}
";

fn completeness_errors(binary_src: &str) -> Vec<String> {
    let registry = load_registry();
    let (exemptions, _) = parse_exemptions(&registry);
    let scan = scan_tag_spaces(binary_src).expect("scans");
    check_tag_space_completeness(&scan, &registered_tag_spaces(&registry), &exemptions)
}

#[test]
fn mutation_a_new_inline_tag_space_is_refused_from_either_direction() {
    // Seen from its READER alone (multi-line arms, the `Universe` shape) ...
    let errors = completeness_errors(&format!("{SNEAKED_READER}{BINARY_SRC}"));
    assert!(
        errors.len() == 1 && errors[0].contains("`Sneaked` is not a registered tag space"),
        "{errors:?}"
    );
    // ... and from its WRITER alone (a reader with no refusal arm would
    // otherwise hide it).
    let errors = completeness_errors(&format!("{SNEAKED_WRITER}{BINARY_SRC}"));
    assert!(
        errors.len() == 1 && errors[0].contains("`Sneaked` is not a registered tag space"),
        "{errors:?}"
    );
}

#[test]
fn a_tag_space_spelled_only_in_a_test_module_is_not_production() {
    // rustfmt-shaped: a module's items are indented, its brace is not.
    let body: String = format!("{SNEAKED_READER}{SNEAKED_WRITER}")
        .lines()
        .map(|line| format!("    {line}\n"))
        .collect();
    let in_tests = format!("#[cfg(test)]\nmod sneaky_tests {{\n{body}}}\n");
    assert_eq!(
        completeness_errors(&format!("{in_tests}{BINARY_SRC}")),
        Vec::<String>::new()
    );
    // An unclosed test module fails closed instead of blanking to the end.
    assert!(production_lines("#[cfg(test)]\nmod t {\n    fn f() {}\n").is_err());
}

#[test]
fn mutation_a_closed_tag_match_naming_no_enum_is_refused_and_a_presence_byte_is_not() {
    let anonymous = "
fn read_anonymous(r: &mut Reader<'_>) -> Result<Thing, BinaryError> {
    match r.read_u8()? {
        0 => make_first(r),
        1 => make_second(r),
        2 => make_third(r),
        t => Err(BinaryError::InvalidTag(t)),
    }
}
";
    let errors = completeness_errors(&format!("{anonymous}{BINARY_SRC}"));
    assert!(
        errors.len() == 1 && errors[0].contains("names no enum"),
        "{errors:?}"
    );
    let presence = "
fn read_optional(r: &mut Reader<'_>) -> Result<Option<u64>, BinaryError> {
    match r.read_u8()? {
        0 => Ok(None),
        1 => Ok(Some(r.read_u64()?)),
        t => Err(BinaryError::InvalidTag(t)),
    }
}
";
    assert_eq!(
        completeness_errors(&format!("{presence}{BINARY_SRC}")),
        Vec::<String>::new()
    );
}

/// The scanner guards the list; this guards the scanner.
#[test]
fn mutation_a_scanner_gone_blind_is_refused() {
    let registry = load_registry();
    let (exemptions, _) = parse_exemptions(&registry);
    let mut registered = registered_tag_spaces(&registry);
    registered.insert("Phantom".to_owned());
    let scan = scan_tag_spaces(BINARY_SRC).expect("scans");
    let errors = check_tag_space_completeness(&scan, &registered, &exemptions);
    assert!(
        errors.len() == 1 && errors[0].contains("no longer sees `Phantom`"),
        "{errors:?}"
    );
}

#[test]
fn a_tag_space_exemption_must_exempt_something_and_is_honoured_when_it_does() {
    let exempting = append_row(
        &real_registry_text(),
        "scan_exempt",
        "{ scan = \"tag-space\", name = \"Sneaked\", reason = \"a probe\" }",
    );
    let registry = parse_registry(&exempting).expect("parses");
    let (exemptions, grammar) = parse_exemptions(&registry);
    assert_eq!(grammar, Vec::<String>::new());
    let registered = registered_tag_spaces(&registry);
    let sneaked = scan_tag_spaces(&format!("{SNEAKED_READER}{BINARY_SRC}")).expect("scans");
    assert_eq!(
        check_tag_space_completeness(&sneaked, &registered, &exemptions),
        Vec::<String>::new()
    );
    let unused = scan_tag_spaces(BINARY_SRC).expect("scans");
    let errors = check_tag_space_completeness(&unused, &registered, &exemptions);
    assert!(
        errors.len() == 1 && errors[0].contains("exempts nothing"),
        "{errors:?}"
    );
}

/// Every string below is BUILT, never spelled: this file is itself scanned,
/// and a versioned literal here would (rightly) demand a row.
fn versioned(name: &str, sep: char, version: u32) -> String {
    format!("{name}{sep}v{version}")
}

#[test]
fn mutation_a_hyphen_spelled_identity_is_seen_bumped_or_minted() {
    // The reviewer's bypass, verbatim: bump the (unregistered) hyphen twin of a
    // registered domain, and mint a brand-new `trust-ir.` identity.
    let registry = load_registry();
    let mut spelled = scan_source_domains();
    let bumped = versioned("trust-ir.satres.cnf", '.', 3);
    let minted = versioned("trust-ir.sneaked.identity", '.', 1);
    spelled.insert(bumped.clone());
    spelled.insert(minted.clone());
    let errors = check_digest_domains(&registry, &spelled);
    for full in [&bumped, &minted] {
        assert!(
            errors
                .iter()
                .any(|e| e.contains(&format!("`{full}`")) && e.contains("no digest_domain row")),
            "{full}: {errors:?}"
        );
    }
    // And the rows that make today's spellings legal are load-bearing.
    let dropped = registry_without_lines_containing("domain = \"trust-ir.sha256-domain\"");
    let errors = check_digest_domains(&dropped, &scan_source_domains());
    assert!(
        errors.len() == 1 && errors[0].contains(&versioned("trust-ir.sha256-domain", '.', 1)),
        "{errors:?}"
    );
}

#[test]
fn the_literal_scanner_is_closed_world() {
    let quote = '"';
    let source = [
        // a whole literal in the hyphen spelling
        format!(
            "const A: &str = {quote}{}{quote};",
            versioned("trust-ir.x", '.', 2)
        ),
        // a NUL-terminated byte-string magic, `-vN`
        format!(
            "const M: &[u8] = b{quote}{}\\0{quote};",
            versioned("TIR-X", '-', 1)
        ),
        // an identity assembled from fragments: the FRAGMENT is the finding
        format!(
            "const C: &str = concat!({quote}trust_ir{quote}, {quote}{}{quote});",
            versioned(".sneaked.concat", '.', 1)
        ),
        // seen whole, so its namespace can be exempted
        format!(
            "const S: &str = {quote}{}{quote};",
            versioned("@trust-internal::d", '-', 1)
        ),
        // the scratch namespace, a non-versioned literal, and a mid-string `vN`
        format!(
            "const T: &str = {quote}{}{quote};",
            versioned("trust_ir.test.t", '.', 1)
        ),
        format!("const N: &str = {quote}trust_ir.not_versioned{quote};"),
        format!("const V: &str = {quote}lean4---v4.30.0{quote};"),
    ]
    .join("\n");
    let mut found = BTreeSet::new();
    scan_versioned_literals(&source, &mut found);
    assert_eq!(
        found.into_iter().collect::<Vec<_>>(),
        [
            versioned(".sneaked.concat", '.', 1),
            versioned("@trust-internal::d", '-', 1),
            versioned("TIR-X", '-', 1),
            versioned("trust-ir.x", '.', 2),
        ]
    );
    // A test MODULE is not production, however it is spelled.
    let in_tests = format!("#[cfg(all(test, feature = \"serde\"))]\nmod t {{\n{source}\n}}\n");
    let mut found = BTreeSet::new();
    scan_versioned_literals(
        &production_lines(&in_tests).expect("closed").join("\n"),
        &mut found,
    );
    assert!(found.is_empty(), "{found:?}");
}

#[test]
fn literal_exemptions_are_namespaces_never_trust_irs_own_and_never_idle() {
    let with = |row: &str| {
        let text = insert_after_last(
            &real_registry_text(),
            "{ scan = \"literal\", name = \"ty.\"",
            row,
        );
        parse_registry(&text).expect("parses")
    };
    // A foreign namespace the sources DO spell is honoured (the live registry
    // is green, and dropping its row is not).
    let dropped = registry_without_lines_containing("{ scan = \"literal\", name = \"ay.\"");
    let errors = check_digest_domains(&dropped, &scan_source_domains());
    assert!(
        !errors.is_empty() && errors.iter().all(|e| e.contains("`ay.")),
        "{errors:?}"
    );
    for (row, refusal) in [
        (
            "{ scan = \"literal\", name = \"zz-unused.\", reason = \"nothing spells it\" }",
            "exempts nothing",
        ),
        (
            "{ scan = \"literal\", name = \"zz\", reason = \"not a namespace\" }",
            "NAMESPACE PREFIX",
        ),
        (
            "{ scan = \"literal\", name = \"zz.\", reason = \"\" }",
            "must give its `reason`",
        ),
        (
            "{ scan = \"everything\", name = \"zz.\", reason = \"no such scan\" }",
            "is not one of",
        ),
    ] {
        let errors = check_digest_domains(&with(row), &scan_source_domains());
        assert!(
            errors.iter().any(|e| e.contains(refusal)),
            "{row}: {errors:?}"
        );
    }
    // TrustIr's own namespace cannot be exempted, by any prefix of it.
    for own in ["trust-ir.", "trust_ir.proof.", "trust-"] {
        let text = append_row(
            &real_registry_text(),
            "scan_exempt",
            &format!("{{ scan = \"literal\", name = \"{own}\", reason = \"try\" }}"),
        );
        let errors = check_digest_domains(
            &parse_registry(&text).expect("parses"),
            &scan_source_domains(),
        );
        assert!(
            errors.iter().any(|e| e.contains("cannot be exempted")),
            "{own}: {errors:?}"
        );
    }
}

#[test]
fn a_new_identity_is_canonical_and_a_legacy_bump_keeps_its_spelling() {
    let reserve = |row: &str, after: &str| {
        let text = insert_after_last(&real_registry_text(), after, row);
        check_digest_domains(
            &parse_registry(&text).expect("parses"),
            &scan_source_domains(),
        )
    };
    // Bumping an existing legacy-spelled name keeps the spelling it has.
    assert_eq!(
        reserve(
            "{ domain = \"trust-ir.satres.cnf\", version = 3, status = \"reserved\", \
             binds = \"a bump\", owner = \"probe\" }",
            "domain = \"trust-ir.satres.cnf\", version = 2,",
        ),
        Vec::<String>::new()
    );
    // Minting ANOTHER one in a legacy spelling is refused.
    let errors = reserve(
        "{ domain = \"trust-ir.satres.dnf\", version = 1, status = \"reserved\", \
         binds = \"a new legacy name\", owner = \"probe\" }",
        "domain = \"trust-ir.satres.cnf\", version = 2,",
    );
    assert!(
        errors.len() == 1 && errors[0].contains("a NEW identity is spelled"),
        "{errors:?}"
    );
}

// --- Landing order. Read gates are CUMULATIVE (`version >= N`), so a blob
// --- numbered N + 1 claims everything N carries: wire versions can only land
// --- in number order. That is inherent in a version counter, not a choice of
// --- this census — but it means a reservation does not by itself promise its
// --- holder THAT number, and the way through must not need a reader hole.

struct Lines {
    registry: String,
    first: u32,
}

/// The real registry with every OPEN wire-version reservation removed. The
/// scenarios below are about two hypothetical lines and nobody else, so they
/// must mean the same thing the day a REAL reservation is on main. They did
/// not at first — measured: one by-the-book `reserve version` turned two of
/// them red, because "land at the next free number" silently became "land
/// over somebody's open reservation". A test that leans on the next free
/// number is a test the protocol it tests will break.
fn registry_with_no_open_versions() -> String {
    let mut inside = false;
    let mut out = String::new();
    for line in real_registry_text().lines() {
        if line == "wire_version = [" {
            inside = true;
        } else if line == "]" {
            inside = false;
        }
        if !(inside && line.contains("status = \"reserved\"")) {
            out.push_str(line);
            out.push('\n');
        }
    }
    out
}

/// That registry plus two open reservations: line A holds `first`, line B
/// holds `first + 1`, and `first` is the number directly above `VERSION`.
fn two_open_reservations() -> Lines {
    let text = registry_with_no_open_versions();
    let first = VERSION + 1;
    let row = |number: u32, line: &str, status: &str| {
        format!(
            "{{ number = {number}, feature = \"line-{line}\", constant = \
             \"LINE_{}_FORMAT_VERSION\", status = \"{status}\", owner = \"{line}\", \
             date = \"2026-09-18\" }}",
            line.to_uppercase()
        )
    };
    let registry = append_row(&text, "wire_version", &row(first, "a", "reserved"));
    let registry = append_row(&registry, "wire_version", &row(first + 1, "b", "reserved"));
    Lines { registry, first }
}

/// `binary.rs` as it would read with `constant = number` landed and `VERSION`
/// moved to `number`, and the reader that code would have.
fn landed(constant: &str, number: u32) -> (String, impl Fn(u32) -> bool) {
    let source = BINARY_SRC.replace(
        &format!("pub const VERSION: u32 = {VERSION};"),
        &format!("pub const VERSION: u32 = {number};\npub const {constant}: u32 = {number};"),
    );
    assert_ne!(source, BINARY_SRC);
    let accepts = move |version: u32| {
        (version > VERSION && version <= number) || reader_accepts_header(version)
    };
    (source, accepts)
}

#[test]
fn a_later_reservation_cannot_land_over_an_open_earlier_one() {
    let Lines { registry, first } = two_open_reservations();
    // B finishes first and lands BY THE BOOK at its own number.
    let registry = registry.replace(
        &format!("number = {}, feature = \"line-b\", constant = \"LINE_B_FORMAT_VERSION\", status = \"reserved\"", first + 1),
        &format!("number = {}, feature = \"line-b\", constant = \"LINE_B_FORMAT_VERSION\", status = \"landed\"", first + 1),
    );
    let (source, accepts) = landed("LINE_B_FORMAT_VERSION", first + 1);
    let errors = check_wire_versions(
        &parse_registry(&registry).expect("parses"),
        &source,
        &accepts,
    );
    assert!(
        errors.iter().any(|e| e.contains(&format!(
            "wire version {first} is `reserved` but VERSION is already"
        ))),
        "{errors:?}"
    );
}

#[test]
fn the_takeover_lands_the_ready_line_at_the_lowest_open_number_without_a_reader_hole() {
    let Lines { registry, first } = two_open_reservations();
    // The documented way through (`wire_alloc.py takeover`): B takes the
    // LOWEST open number, A's reservation moves up. One pushed commit.
    let taken_over = registry
        .replace(
            &format!("number = {first}, feature = \"line-a\", constant = \"LINE_A_FORMAT_VERSION\", status = \"reserved\", owner = \"a\""),
            &format!("number = {first}, feature = \"line-b\", constant = \"LINE_B_FORMAT_VERSION\", status = \"landed\", owner = \"b\""),
        )
        .replace(
            &format!("number = {}, feature = \"line-b\", constant = \"LINE_B_FORMAT_VERSION\", status = \"reserved\", owner = \"b\"", first + 1),
            &format!("number = {}, feature = \"line-a\", constant = \"LINE_A_FORMAT_VERSION\", status = \"reserved\", owner = \"a\"", first + 1),
        );
    assert_ne!(taken_over, registry);
    let taken_over = parse_registry(&taken_over).expect("parses");
    let (source, accepts) = landed("LINE_B_FORMAT_VERSION", first);
    assert_eq!(
        check_wire_versions(&taken_over, &source, &accepts),
        Vec::<String>::new()
    );
    // The displaced line finds out MECHANICALLY, the first time it merges
    // main: its constant still says the number it no longer holds.
    let (stale, accepts) = landed("LINE_A_FORMAT_VERSION", first);
    let errors = check_wire_versions(&taken_over, &stale, &accepts);
    assert!(
        errors.iter().any(|e| e.contains(&format!(
            "wire_version {} names `LINE_A_FORMAT_VERSION`, which binary.rs declares as {first}",
            first + 1
        ))),
        "{errors:?}"
    );
}

#[test]
fn an_abandoned_reservation_is_deleted_from_the_top_never_burned() {
    let Lines { registry, first } = two_open_reservations();
    // Burning a number that never landed buys a PERMANENT refusal hole in the
    // reader the day a later version lands, for blobs that never existed.
    let burned = registry.replace(
        &format!("number = {first}, feature = \"line-a\", constant = \"LINE_A_FORMAT_VERSION\", status = \"reserved\""),
        &format!("number = {first}, feature = \"line-a\", status = \"burned\""),
    );
    assert_ne!(burned, registry);
    let burned = burned.replace(
        &format!("number = {}, feature = \"line-b\", constant = \"LINE_B_FORMAT_VERSION\", status = \"reserved\"", first + 1),
        &format!("number = {}, feature = \"line-b\", constant = \"LINE_B_FORMAT_VERSION\", status = \"landed\"", first + 1),
    );
    let (source, accepts) = landed("LINE_B_FORMAT_VERSION", first + 1);
    let errors = check_wire_versions(&parse_registry(&burned).expect("parses"), &source, &accepts);
    assert!(
        errors.iter().any(|e| e.contains(&format!(
            "wire version {first}: registry says burned but the module reader ACCEPTS"
        ))),
        "{errors:?}"
    );
    // Deleting the HIGHEST open reservation costs nothing.
    let released: String = registry
        .lines()
        .filter(|line| !line.contains("feature = \"line-b\""))
        .map(|line| format!("{line}\n"))
        .collect();
    assert_eq!(
        check_wire_versions(
            &parse_registry(&released).expect("parses"),
            BINARY_SRC,
            &reader_accepts_header
        ),
        Vec::<String>::new()
    );
}

#[test]
fn the_parser_refuses_anything_outside_the_one_line_grammar() {
    for (bad, why) in [
        ("[[wire_version]]\nnumber = 1\n", "block tables"),
        ("wire_version = [\n  { number = 01 },\n]\n", "leading zero"),
        (
            "wire_version = [\n  { number = 1, number = 2 },\n]\n",
            "duplicate key",
        ),
        (
            "wire_version = [\n  { feature = \"a\\\"b\" },\n]\n",
            "escapes",
        ),
        (
            "wire_version = [\n  { number = 1 }\n]\n",
            "missing trailing comma",
        ),
        ("wire_version = [\n  { number = 1 },\n", "unclosed table"),
        (
            "wire_version = [\n]\nwire_version = [\n]\n",
            "table opened twice",
        ),
    ] {
        assert!(parse_registry(bad).is_err(), "must refuse {why}: {bad:?}");
    }
    let ok = parse_registry("# c\n\nwire_version = [\n  { number = 1, feature = \"a, b\" },\n]\n")
        .expect("minimal registry parses");
    assert_eq!(ok.rows("wire_version")[0].str("feature"), Ok("a, b"));
}

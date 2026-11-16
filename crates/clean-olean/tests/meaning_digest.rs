// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The mutation controls of the meaning digest every statement pin uses
//! (`support/meaning_digest.rs`; plan unit E2's follow-up "pins bind
//! meaning", `docs/DECISIONS.md`, "Statement pins bind meaning: closure digest
//! over package constants").
//!
//! The fixture family `meaning_digest` holds a base module and three copies
//! with one change each, compiled by the pinned Lean. Each module is loaded
//! alone, its package is the names its own `.olean` declares, and the digests
//! of the same names are compared across them:
//!
//! * the recursive body of `Tm.instAll` changes, the shape of the instPis
//!   mutation the landing check of D1 Revision 5 made: the body lives in
//!   `Tm.instAll._f`, and the pins of `Tm.instAll` and of everything that
//!   reaches it move, and nothing else does;
//! * `SemLE`, the relation `leq_sound` names, changes: both pins move;
//! * only the proof of `leq_sound` changes: no pin moves.
//!
//! The first two are changes the old pins could not see: the test computes
//! what the four tests used to hash (the constant's own type, its value, both,
//! or its whole kernel record) and requires each of those to stay put.

#[path = "support/meaning_digest.rs"]
mod meaning_digest;

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use clean_kernel::env::Environment;
use clean_kernel::{ConstantKind, Expr, Name};
use clean_olean::test_support::compiled_fixture_dir;
use clean_olean::{load_module_with_deps, require_pinned_lean_lib_path};
use meaning_digest::{MeaningDigests, MeaningError, Package};
use sha2::{Digest, Sha256};

/// The names whose digests are compared, as a statement-pin test would pin
/// them: a constructor, two recursive definitions, a definition and a theorem
/// that reach one of them, a relation, a theorem naming it, and a bystander.
const PINNED: &[&str] = &[
    "MD.Tm.pi",
    "MD.Tm.shift",
    "MD.Tm.instAll",
    "MD.Reaches",
    "MD.reaches_leaf",
    "MD.SemLE",
    "MD.leq_sound",
    "MD.Unrelated",
];

/// One compiled module, loaded alone, and its package.
struct Variant {
    env: Environment,
    package: Package,
}

impl Variant {
    fn load(compiled: &Path, lib: &Path, module: &str) -> Self {
        let mut env = Environment::for_lean_replay();
        load_module_with_deps(
            &mut env,
            module,
            &[compiled.to_path_buf(), lib.to_path_buf()],
        )
        .unwrap_or_else(|error| panic!("load {module}: {error}"));
        let package = Package::of_modules(compiled, vec![module.to_owned()]);
        Self { env, package }
    }

    /// Pinned name → meaning digest.
    fn digests(&self) -> BTreeMap<&'static str, String> {
        let digests = MeaningDigests::new(&self.env, &self.package);
        PINNED
            .iter()
            .map(|pin| {
                let digest = digests
                    .digest(&Name::from_string(pin))
                    .unwrap_or_else(|error| panic!("{pin}: {error}"));
                (*pin, digest)
            })
            .collect()
    }

    /// Pinned name → what the four tests hashed before the meaning digest,
    /// for the kind of constant each pinned: for a theorem, E2's digest of
    /// (universe parameters, type); for a definition or constructor, the
    /// model's and kcheck's digest of the proposition value, `kcheck_spec`'s
    /// digest of type and value together, the model inventory's digest of
    /// the type alone, and the digest of the constant's whole kernel record
    /// with its inductive, constructor and recursor table entries (the form
    /// the model inventory's and the first `cic_l` definition pins' per-
    /// declaration digests took). A theorem's proof was never pinned.
    fn old_digests(&self) -> BTreeMap<&'static str, Vec<String>> {
        PINNED
            .iter()
            .map(|pin| {
                let c = self
                    .env
                    .get_const(&Name::from_string(pin))
                    .unwrap_or_else(|| panic!("{pin} is resident"));
                if c.kind == ConstantKind::Theorem {
                    let params: Vec<String> =
                        c.level_params.iter().map(ToString::to_string).collect();
                    return (*pin, vec![sha(&encode(&(&params, &c.type_)))]);
                }
                let mut parts = Vec::new();
                for part in std::iter::once(&c.type_).chain(c.value.as_ref()) {
                    let bytes = encode(part);
                    parts.extend_from_slice(&(bytes.len() as u64).to_le_bytes());
                    parts.extend_from_slice(&bytes);
                }
                let name = Name::from_string(pin);
                let record = (
                    c,
                    self.env.get_inductive(&name),
                    self.env.get_constructor(&name),
                    self.env.get_recursor(&name),
                );
                (
                    *pin,
                    vec![
                        sha(&encode(&c.value)),
                        sha(&parts),
                        sha(&encode(&c.type_)),
                        sha(&encode(&record)),
                    ],
                )
            })
            .collect()
    }

    fn closure(&self, root: &str) -> BTreeSet<String> {
        MeaningDigests::new(&self.env, &self.package)
            .closure(&Name::from_string(root))
            .unwrap_or_else(|error| panic!("{root}: {error}"))
            .iter()
            .map(ToString::to_string)
            .collect()
    }
}

fn encode<T: serde::Serialize + ?Sized>(value: &T) -> Vec<u8> {
    bincode::serde::encode_to_vec(value, bincode::config::standard()).expect("serialize")
}

fn sha(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

/// The pins of `variant` that differ from `base`'s.
fn moved<T: PartialEq>(
    base: &BTreeMap<&'static str, T>,
    variant: &BTreeMap<&'static str, T>,
) -> BTreeSet<&'static str> {
    PINNED
        .iter()
        .copied()
        .filter(|pin| base[pin] != variant[pin])
        .collect()
}

fn names(list: &[&'static str]) -> BTreeSet<&'static str> {
    list.iter().copied().collect()
}

#[test]
fn meaning_digest_moves_with_meaning_and_not_with_proofs() {
    let lib = require_pinned_lean_lib_path().expect("install the repository-pinned Lean toolchain");
    let compiled = compiled_fixture_dir("meaning_digest");
    // The base stays loaded; each mutation is loaded, measured and dropped.
    let base = Variant::load(&compiled, &lib, "MeaningDigestBase");

    // The mechanism: `Tm.instAll`'s value is a `List.brecOn` wrapper and its
    // body lives in `Tm.instAll._f`, which its closure holds; a theorem's
    // closure holds what its statement names and nothing its proof uses.
    let install = base.closure("MD.Tm.instAll");
    assert!(
        install.contains("MD.Tm.instAll._f") && install.contains("MD.Tm.shift"),
        "the closure of Tm.instAll holds its body's auxiliary and what the body calls: \
         {install:?}"
    );
    assert_eq!(
        base.closure("MD.leq_sound"),
        ["MD.SemLE", "MD.leq_sound"]
            .into_iter()
            .map(str::to_owned)
            .collect::<BTreeSet<_>>(),
        "a theorem reaches what its statement names, never what its proof uses"
    );
    let pi = base.closure("MD.Tm.pi");
    assert!(
        pi.contains("MD.Tm") && pi.contains("MD.Tm.leaf"),
        "a constructor reaches its type and its type's every constructor: {pi:?}"
    );

    let (base_new, base_old) = (base.digests(), base.old_digests());
    for pin in PINNED {
        eprintln!("base {pin} {}", base_new[pin]);
    }
    let roots: Vec<Name> = PINNED.iter().map(|pin| Name::from_string(pin)).collect();
    eprintln!(
        "{}",
        MeaningDigests::new(&base.env, &base.package)
            .describe(&base.package, &roots)
            .expect("every pinned name is in the package")
    );

    // The recursive body changes: the definition's pin and every pin that
    // reaches it move, nothing else; no old digest moves.
    let body = Variant::load(&compiled, &lib, "MeaningDigestBody");
    let body_moved = moved(&base_new, &body.digests());
    assert_eq!(
        body_moved,
        names(&["MD.Tm.instAll", "MD.Reaches", "MD.reaches_leaf"]),
        "a change to a recursive body moves its definition and what reaches it"
    );
    assert_eq!(
        moved(&base_old, &body.old_digests()),
        BTreeSet::new(),
        "the old digests do not see a recursive body (the defect this replaces)"
    );
    drop(body);

    // The relation a theorem names changes: the relation's pin and the
    // theorem's move; the theorem's old statement digest does not.
    let mention = Variant::load(&compiled, &lib, "MeaningDigestMention");
    let mention_moved = moved(&base_new, &mention.digests());
    assert_eq!(
        mention_moved,
        names(&["MD.SemLE", "MD.leq_sound"]),
        "a change to a definition a theorem names moves the theorem"
    );
    let mention_old = mention.old_digests();
    assert_eq!(
        base_old["MD.leq_sound"], mention_old["MD.leq_sound"],
        "E2's digest of a theorem does not see the definitions it names"
    );
    assert_ne!(
        base_old["MD.SemLE"], mention_old["MD.SemLE"],
        "the mutation changed SemLE itself"
    );
    drop(mention);

    // Only a proof changes: no pin moves. The proof did change.
    let proof = Variant::load(&compiled, &lib, "MeaningDigestProof");
    assert_eq!(
        moved(&base_new, &proof.digests()),
        BTreeSet::new(),
        "a proof never moves a pin"
    );
    let leq_sound = Name::from_string("MD.leq_sound");
    let proof_value = |variant: &Variant| {
        variant
            .env
            .get_const(&leq_sound)
            .and_then(|c| c.value.clone())
            .expect("leq_sound has a proof")
    };
    assert_ne!(
        proof_value(&base),
        proof_value(&proof),
        "the proof mutation changed the proof"
    );
    drop(proof);

    // A theorem restated at its own statement keeps its digest; restated as
    // another proposition it does not.
    let digests = MeaningDigests::new(&base.env, &base.package);
    let reaches_leaf = Name::from_string("MD.reaches_leaf");
    let stated = base
        .env
        .get_const(&reaches_leaf)
        .expect("reaches_leaf is resident");
    let restate = |type_: &Expr| {
        digests
            .statement_digest(&reaches_leaf, &stated.level_params, type_)
            .expect("reaches_leaf is in the package")
    };
    assert_eq!(restate(&stated.type_), base_new["MD.reaches_leaf"]);
    assert_ne!(
        restate(&Expr::const_(Name::from_string("MD.Unrelated"), vec![])),
        base_new["MD.reaches_leaf"]
    );

    // Refusals: a root outside the package, and a package constant the
    // environment does not hold.
    assert_eq!(
        digests.digest(&Name::from_string("Nat.add")),
        Err(MeaningError::OutsidePackage("Nat.add".to_owned()))
    );
    let empty = Environment::for_lean_replay();
    assert_eq!(
        MeaningDigests::new(&empty, &base.package).digest(&Name::from_string("MD.Tm.instAll")),
        Err(MeaningError::NotResident {
            root: "MD.Tm.instAll".to_owned(),
            name: "MD.Tm.instAll".to_owned(),
        })
    );
    eprintln!(
        "meaning digest controls: a recursive body moved {body_moved:?}, a named relation moved \
         {mention_moved:?}, a proof moved nothing; the old digests saw neither of the first two"
    );
}

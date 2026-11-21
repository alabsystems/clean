// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The canonical digest shared by self-proof statement-pin consumers: the
//! meaning digest (plan unit E2's follow-up "pins bind meaning";
//! `docs/DECISIONS.md`, "Statement pins bind meaning: closure digest over
//! package constants"). Fixture discovery and measured-pin writes live in
//! integration-test support; this production API consumes an explicit package
//! inventory and resident environment without reading or writing files.
//!
//! # What a digest binds
//!
//! A pin used to hash a constant's own type (and value). That fixes nothing a
//! definition it mentions says: a structurally recursive definition's value is
//! a `brecOn` wrapper whose body lives in the auxiliary `._f`, and a theorem's
//! statement names the relations whose definitions give it its meaning. The
//! meaning digest of a constant `c` is instead SHA-256 over the canonical
//! serialization of the set of package constants reachable from `c`:
//!
//! * **Reachable.** From a theorem or an axiom, its type; from a definition or
//!   an opaque, its type and value; from an inductive type, its type, the
//!   types of its mutual block and its constructors; from a constructor, its
//!   type and its inductive; from a recursor, its type, its inductive, and each
//!   rule's constructor and right-hand side. A constant an expression uses is
//!   every `Const` head and every projection's structure. A reachable theorem
//!   contributes its type only: a proof never changes what a statement means.
//!   Compiler auxiliaries (`._f`, `match_N`, `brecOn`, `below`, `casesOn`,
//!   `rec`, `_unary`, `proof_N`, equation lemmas) are constants like any
//!   other and are in the set whenever they are reached.
//! * **Package.** The walk stops at a constant outside the package under test,
//!   which each test fixes as the theories its fixture family compiles from
//!   this repository ([`Package::of_module_names`]), selected by module of origin as
//!   E2 selects targets: the names each module's own `.olean` declares. What
//!   is outside is the pinned toolchain's library (`Init` and the rest of
//!   Lean's own modules), whose bytes the pinned toolchain fixes; a name
//!   outside the package enters a digest as the name its users write. A name
//!   more than one package module declares is one package constant, read from
//!   the copy the environment holds: Lean realizes an equation lemma such as
//!   `eq_1` in each module that first needs it, and its import merges two
//!   copies only when one restates the other (`subsumesInfo`; the loader's
//!   account is `replay_module/load_refusals.rs`).
//! * **Record.** Each constant contributes a record of length-prefixed parts,
//!   each the `bincode` standard encoding the kernel's serde form gives: its
//!   kind, its name, its universe parameter names and its type; then its value
//!   and the kernel's unfolding flag and hint, `is_reducible` and
//!   `reducibility` (definition and opaque); the number of parameters and
//!   indices, the
//!   mutual block, the constructor names and the recursive, reflexive,
//!   large-elimination and nested flags (inductive); its inductive, parameter
//!   and field counts and index (constructor); its inductive, argument order,
//!   parameter, index, motive and minor counts, the K flag and each rule's
//!   constructor, field count, recursive fields and right-hand side
//!   (recursor). Binder names are not part of a kernel term, so renaming a
//!   bound variable moves nothing.
//! * **Canonical order and framing.** The digest is SHA-256 over the domain
//!   tag [`DOMAIN`], the format version [`FORMAT_VERSION`], the root's name,
//!   the number of constants, and then, in the kernel's name order, the
//!   SHA-256 of each constant's record under the tag [`RECORD_DOMAIN`]. The
//!   hash list is the serialization of the set: each record is hashed once per
//!   run however many pins reach it.
//!
//! A pin keyed by a name whose constant is not in the package, and a package
//! name reached but not resident (an `_unsafe_rec` copy no safe declaration
//! may use), are refusals, never a skipped constant.
//!
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::rc::Rc;

use clean_kernel::env::Environment;
use clean_kernel::expr::UsedConstants;
use clean_kernel::{ConstantKind, Expr, Name};
use serde::Serialize;
use sha2::{Digest, Sha256};

pub mod resident;

/// The domain-separation tag of a meaning digest.
pub const DOMAIN: &str = "clean.self-proof.meaning-digest";

/// The domain-separation tag of one constant's record.
pub const RECORD_DOMAIN: &str = "clean.self-proof.meaning-digest.record";

/// The serialization's version; any change to what a record holds, what is
/// reached or how the stream is framed moves it.
pub const FORMAT_VERSION: u32 = 1;

/// Why a digest could not be taken.
#[derive(Debug, PartialEq, Eq, thiserror::Error)]
pub enum MeaningError {
    /// A pin's root is not a constant of the package under test.
    #[error("{0} is not a constant of the package under test")]
    OutsidePackage(String),
    /// A package constant was reached and the environment does not hold it.
    #[error("{name}, a package constant reached from {root}, is not resident")]
    NotResident { root: String, name: String },
}

/// An explicit package inventory, selected by module of origin by its caller.
///
/// The digest follows only names in this set. Modules and repeated declaration
/// counts retain the qualification log's existing inventory metadata; this
/// type reads no artifacts or fixture files.
pub struct Package {
    modules: Vec<String>,
    names: BTreeSet<Name>,
    restated: usize,
}

impl Package {
    /// A package containing exactly the given names.
    ///
    /// # Panics
    /// Panics when the inventory is empty, as the existing pin helper does.
    pub fn of_names(names: BTreeSet<Name>) -> Self {
        assert!(!names.is_empty(), "the package declares nothing");
        Self {
            modules: Vec::new(),
            names,
            restated: 0,
        }
    }

    /// Union the names declared by each module, retaining caller-supplied
    /// module order and counting declarations repeated by a later module.
    /// The caller supplies each module's own declared names; no name-prefix
    /// selection or filesystem discovery happens here.
    ///
    /// # Panics
    /// Panics when the resulting inventory is empty.
    pub fn of_module_names(modules: impl IntoIterator<Item = (String, Vec<Name>)>) -> Self {
        let mut ordered = Vec::new();
        let mut names = BTreeSet::new();
        let mut restated = 0;
        for (module, declared) in modules {
            ordered.push(module);
            for name in declared {
                if !names.insert(name) {
                    restated += 1;
                }
            }
        }
        assert!(!names.is_empty(), "the package declares nothing");
        Self {
            modules: ordered,
            names,
            restated,
        }
    }

    /// The package's modules, in compile order.
    pub fn modules(&self) -> &[String] {
        &self.modules
    }

    /// Every name a package module declares.
    pub fn names(&self) -> &BTreeSet<Name> {
        &self.names
    }
}

/// One constant's record: its digest and the package constants it reaches.
struct Record {
    digest: [u8; 32],
    reaches: Vec<Name>,
}

/// Length-prefixed `bincode` parts.
#[derive(Default)]
struct Parts(Vec<u8>);

impl Parts {
    fn part<T: Serialize + ?Sized>(&mut self, value: &T) -> &mut Self {
        let bytes = bincode::serde::encode_to_vec(value, bincode::config::standard())
            .expect("a kernel record serializes");
        self.0
            .extend_from_slice(&(bytes.len() as u64).to_le_bytes());
        self.0.extend_from_slice(&bytes);
        self
    }

    fn digest(&self, domain: &str) -> [u8; 32] {
        let mut framed = Parts::default();
        framed.part(domain);
        let mut hasher = Sha256::new();
        hasher.update(&framed.0);
        hasher.update(&self.0);
        hasher.finalize().into()
    }
}

/// Every constant an expression uses: `Const` heads and projection structures.
fn used(expressions: &[&Expr], reaches: &mut BTreeSet<Name>) {
    let mut found = std::collections::HashSet::new();
    for expression in expressions {
        expression.used_constants_dag(UsedConstants::WithProjectionStructures, &mut found);
    }
    reaches.extend(found);
}

/// The record of a theorem stating `type_` under `level_params`.
fn theorem_record(name: &Name, level_params: &[Name], type_: &Expr) -> (Parts, BTreeSet<Name>) {
    let mut parts = Parts::default();
    parts
        .part("theorem")
        .part(name)
        .part(level_params)
        .part(type_);
    let mut reaches = BTreeSet::new();
    used(&[type_], &mut reaches);
    (parts, reaches)
}

/// Meaning digests over one environment and one package, with each record
/// built and hashed once.
pub struct MeaningDigests<'a> {
    env: &'a Environment,
    package: &'a BTreeSet<Name>,
    records: RefCell<HashMap<Name, Rc<Record>>>,
}

impl<'a> MeaningDigests<'a> {
    pub fn new(env: &'a Environment, package: &'a Package) -> Self {
        Self {
            env,
            package: &package.names,
            records: RefCell::new(HashMap::new()),
        }
    }

    /// The meaning digest of the package constant `root`.
    pub fn digest(&self, root: &Name) -> Result<String, MeaningError> {
        self.require_package(root)?;
        let record = self.record(root, root)?;
        self.close(root, record.digest, &record.reaches)
    }

    /// The meaning digest `root` would have as a theorem stating `type_` under
    /// `level_params`: a forged statement's digest, and for a real theorem at
    /// its own statement the same digest as [`Self::digest`].
    pub fn statement_digest(
        &self,
        root: &Name,
        level_params: &[Name],
        type_: &Expr,
    ) -> Result<String, MeaningError> {
        self.require_package(root)?;
        let (parts, reaches) = theorem_record(root, level_params, type_);
        let reaches: Vec<Name> = reaches
            .into_iter()
            .filter(|name| self.package.contains(name))
            .collect();
        self.close(root, parts.digest(RECORD_DOMAIN), &reaches)
    }

    /// The package constants reachable from `root`, `root` included.
    pub fn closure(&self, root: &Name) -> Result<BTreeSet<Name>, MeaningError> {
        self.require_package(root)?;
        let record = self.record(root, root)?;
        Ok(self
            .walk(root, record.digest, &record.reaches)?
            .into_keys()
            .collect())
    }

    /// One line on the package and the closures of `roots`, for the log.
    pub fn describe(&self, package: &Package, roots: &[Name]) -> Result<String, MeaningError> {
        let mut sizes = roots
            .iter()
            .map(|root| self.closure(root).map(|closure| closure.len()))
            .collect::<Result<Vec<usize>, MeaningError>>()?;
        sizes.sort_unstable();
        let (smallest, median, largest) = match sizes.as_slice() {
            [] => (0, 0, 0),
            sizes => (sizes[0], sizes[sizes.len() / 2], sizes[sizes.len() - 1]),
        };
        Ok(format!(
            "meaning digest v{FORMAT_VERSION}: package of {} modules declaring {} names ({} \
             restated by a later module); {} pins reach {smallest} to {largest} package constants \
             (median {median}); {} records built",
            package.modules().len(),
            package.names().len(),
            package.restated,
            roots.len(),
            self.records.borrow().len()
        ))
    }

    fn require_package(&self, root: &Name) -> Result<(), MeaningError> {
        if self.package.contains(root) {
            Ok(())
        } else {
            Err(MeaningError::OutsidePackage(root.to_string()))
        }
    }

    fn close(
        &self,
        root: &Name,
        digest: [u8; 32],
        reaches: &[Name],
    ) -> Result<String, MeaningError> {
        let closure = self.walk(root, digest, reaches)?;
        let mut stream = Parts::default();
        stream
            .part(DOMAIN)
            .part(&FORMAT_VERSION)
            .part(root)
            .part(&(closure.len() as u64));
        let mut hasher = Sha256::new();
        hasher.update(&stream.0);
        for record in closure.values() {
            hasher.update(record);
        }
        Ok(hasher
            .finalize()
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect())
    }

    /// Name → record digest for every package constant reachable from a root
    /// whose own record is `digest` and reaches `reaches`.
    fn walk(
        &self,
        root: &Name,
        digest: [u8; 32],
        reaches: &[Name],
    ) -> Result<BTreeMap<Name, [u8; 32]>, MeaningError> {
        let mut closure = BTreeMap::from([(root.clone(), digest)]);
        let mut pending: Vec<Name> = reaches.to_vec();
        while let Some(name) = pending.pop() {
            if closure.contains_key(&name) {
                continue;
            }
            let record = self.record(root, &name)?;
            closure.insert(name, record.digest);
            pending.extend(record.reaches.iter().cloned());
        }
        Ok(closure)
    }

    /// The record of the package constant `name`, reached from `root`.
    fn record(&self, root: &Name, name: &Name) -> Result<Rc<Record>, MeaningError> {
        if let Some(record) = self.records.borrow().get(name) {
            return Ok(Rc::clone(record));
        }
        let (parts, reaches) = self.build(name).ok_or_else(|| MeaningError::NotResident {
            root: root.to_string(),
            name: name.to_string(),
        })?;
        let record = Rc::new(Record {
            digest: parts.digest(RECORD_DOMAIN),
            reaches: reaches
                .into_iter()
                .filter(|reached| self.package.contains(reached))
                .collect(),
        });
        self.records
            .borrow_mut()
            .insert(name.clone(), Rc::clone(&record));
        Ok(record)
    }

    /// A resident constant's record parts and every name it reaches.
    fn build(&self, name: &Name) -> Option<(Parts, BTreeSet<Name>)> {
        let env = self.env;
        let mut parts = Parts::default();
        let mut reaches = BTreeSet::new();
        if let Some(inductive) = env.get_inductive(name) {
            parts
                .part("inductive")
                .part(&inductive.name)
                .part(&inductive.level_params)
                .part(&inductive.type_)
                .part(&(inductive.num_params, inductive.num_indices))
                .part(&inductive.all_names)
                .part(&inductive.constructor_names)
                .part(&(
                    inductive.is_recursive,
                    inductive.is_reflexive,
                    inductive.is_large_elim,
                    inductive.is_nested,
                ));
            used(&[&inductive.type_], &mut reaches);
            reaches.extend(inductive.all_names.iter().cloned());
            reaches.extend(inductive.constructor_names.iter().cloned());
        } else if let Some(constructor) = env.get_constructor(name) {
            parts
                .part("constructor")
                .part(&constructor.name)
                .part(&constructor.level_params)
                .part(&constructor.type_)
                .part(&constructor.inductive_name)
                .part(&(
                    constructor.num_params,
                    constructor.num_fields,
                    constructor.constructor_idx,
                ));
            used(&[&constructor.type_], &mut reaches);
            reaches.insert(constructor.inductive_name.clone());
        } else if let Some(recursor) = env.get_recursor(name) {
            parts
                .part("recursor")
                .part(&recursor.name)
                .part(&recursor.level_params)
                .part(&recursor.type_)
                .part(&recursor.inductive_name)
                .part(&recursor.arg_order)
                .part(&(
                    recursor.num_params,
                    recursor.num_indices,
                    recursor.num_motives,
                    recursor.num_minors,
                    recursor.is_k,
                ))
                .part(&(recursor.rules.len() as u64));
            for rule in &recursor.rules {
                parts
                    .part(&rule.constructor_name)
                    .part(&rule.num_fields)
                    .part(&rule.recursive_fields)
                    .part(&rule.rhs);
                reaches.insert(rule.constructor_name.clone());
            }
            let mut expressions = vec![&recursor.type_];
            expressions.extend(recursor.rules.iter().map(|rule| &rule.rhs));
            used(&expressions, &mut reaches);
            reaches.insert(recursor.inductive_name.clone());
        } else {
            let constant = env.get_const(name)?;
            match constant.kind {
                ConstantKind::Theorem => {
                    return Some(theorem_record(
                        &constant.name,
                        &constant.level_params,
                        &constant.type_,
                    ));
                }
                ConstantKind::Axiom => {
                    parts.part("axiom");
                }
                ConstantKind::Definition => {
                    parts.part("definition");
                }
                ConstantKind::Opaque => {
                    parts.part("opaque");
                }
            }
            parts
                .part(&constant.name)
                .part(&constant.level_params)
                .part(&constant.type_);
            let mut expressions = vec![&constant.type_];
            if constant.kind != ConstantKind::Axiom {
                parts
                    .part(&constant.value)
                    .part(&constant.is_reducible)
                    .part(&constant.reducibility);
                expressions.extend(constant.value.as_ref());
            }
            used(&expressions, &mut reaches);
        }
        Some((parts, reaches))
    }
}

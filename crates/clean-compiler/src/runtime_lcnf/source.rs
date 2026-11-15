//! Exact eager environment snapshots for freshly elaborated source bodies.
//!
//! This adapter never elaborates, registers or promotes a declaration. Source
//! labels/bytes and kernel provenance are observations supplied by the frontend;
//! only that frontend can bind them to its actual check. No constructor here
//! creates a certificate. Lazy/prelude and external runtime closure stay separate.

use super::catalog::{references, RuntimeCatalogDeclaration};
use clean_kernel::{
    ConstantInfo, ConstantOrigin, ConstructorVal, DeclarationVerification, Environment, Expr,
    InductiveVal, Name, QuotVal, RecursorArgOrder, RecursorVal,
};
use clean_olean::import::runtime::{RuntimeBody, RuntimeFamily, RuntimeRecursorRule};
use clean_olean::module::{ConstantKind, DefinitionSafety};
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet};
use std::io::{self, Write};

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct RuntimeSourceRecord {
    pub module: String,
    pub path: String,
    pub source: String,
}

/// Every represented registry role is retained, including coherent mirrors.
#[derive(Clone, Debug, Serialize)]
pub struct RuntimeEnvironmentRow {
    pub name: Name,
    pub constant: Option<ConstantInfo>,
    pub inductive: Option<InductiveVal>,
    pub constructor: Option<ConstructorVal>,
    pub recursor: Option<RecursorVal>,
    pub quotient: Option<QuotVal>,
    pub implemented_by: Option<Name>,
    pub structure_fields: Option<Vec<Name>>,
    pub structure_defaults: Vec<(Name, Option<Expr>)>,
    pub structure_parents: Option<Vec<(Name, Name)>>,
    pub verification: Option<DeclarationVerification>,
    pub origin: Option<ConstantOrigin>,
    pub partial: bool,
    pub unsafe_: bool,
    pub noncomputable: bool,
}

/// Limits apply before cloning registry payloads or allocating encoded bytes.
/// Input environments/source strings already belong to the caller. This is a
/// bounded encoding/population policy, not an OS memory limit or parser sandbox.
#[derive(Clone, Copy, Debug)]
pub struct RuntimeSourceCaptureLimits {
    pub declarations: usize,
    pub row_bytes: usize,
    pub total_bytes: usize,
    pub source_bytes: usize,
}

impl Default for RuntimeSourceCaptureLimits {
    fn default() -> Self {
        Self {
            declarations: 100_000,
            row_bytes: 16 * 1024 * 1024,
            total_bytes: 64 * 1024 * 1024,
            source_bytes: 16 * 1024 * 1024,
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct RuntimeEnvironmentPopulation {
    pub constants: usize,
    pub inductives: usize,
    pub constructors: usize,
    pub recursors: usize,
    pub quotients: usize,
    /// Exact only after the complete typed union fits the population bound.
    pub unique_names: Option<usize>,
}

#[derive(Clone, Debug)]
pub struct RuntimeEnvironmentRowFailure {
    pub phase: &'static str,
    pub name: Name,
    pub reason: String,
}

struct HashWriter {
    hash: blake3::Hasher,
    bytes: usize,
    limit: usize,
}

impl Write for HashWriter {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        if bytes.len() > self.limit.saturating_sub(self.bytes) {
            return Err(io::Error::other("source observation byte limit exceeded"));
        }
        self.hash.update(bytes);
        self.bytes += bytes.len();
        Ok(bytes.len())
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

fn bounded_hash(value: &impl Serialize, limit: usize) -> Result<([u8; 32], usize), String> {
    use bincode::Options;
    let mut output = HashWriter {
        hash: blake3::Hasher::new(),
        bytes: 0,
        limit,
    };
    bincode::DefaultOptions::new()
        .with_fixint_encoding()
        .with_little_endian()
        .serialize_into(&mut output, value)
        .map_err(|error| error.to_string())?;
    Ok((*output.hash.finalize().as_bytes(), output.bytes))
}

#[derive(Clone, Debug)]
pub struct RuntimeEnvironmentCapture {
    pub sources: Vec<RuntimeSourceRecord>,
    pub before: Vec<RuntimeEnvironmentRow>,
    pub after: Vec<RuntimeEnvironmentRow>,
    pub before_population: RuntimeEnvironmentPopulation,
    pub after_population: RuntimeEnvironmentPopulation,
    /// This is the eager declaration union with metadata reachable by its exact
    /// keys, not every map/callback/lazy declaration in an Environment.
    pub limitations: Vec<&'static str>,
    /// Typed names remain available without formatting an arbitrarily large
    /// name into an error string after its encoding has exceeded the budget.
    pub row_failures: Vec<RuntimeEnvironmentRowFailure>,
    /// Exact typed delta only when delta_complete is true. Incomplete subsets
    /// are never compared as if an omitted failed row were absent.
    pub added: BTreeSet<Name>,
    pub changed: BTreeSet<Name>,
    pub removed: BTreeSet<Name>,
    pub delta_complete: bool,
    /// Bincode-1 fixed-LE digest of actual sources and both represented tables.
    /// None on any capture error, including a retained/omitted malformed row.
    /// This is a local observation binding, not a stable library wire format.
    pub snapshot_blake3: Option<[u8; 32]>,
    pub errors: Vec<String>,
}

fn snapshot(
    env: &Environment,
    limits: RuntimeSourceCaptureLimits,
    label: &'static str,
    remaining: &mut usize,
    errors: &mut Vec<String>,
    failures: &mut Vec<RuntimeEnvironmentRowFailure>,
) -> (
    Vec<RuntimeEnvironmentRow>,
    BTreeMap<Name, [u8; 32]>,
    RuntimeEnvironmentPopulation,
) {
    let mut population = RuntimeEnvironmentPopulation {
        constants: env.constants().count(),
        inductives: env.inductives().count(),
        constructors: env.constructors().count(),
        recursors: env.recursors().count(),
        quotients: env.quotients().count(),
        unique_names: None,
    };
    let mut names = BTreeSet::new();
    for name in env
        .constants()
        .map(|r| &r.name)
        .chain(env.inductives().map(|r| &r.name))
        .chain(env.constructors().map(|r| &r.name))
        .chain(env.recursors().map(|r| &r.name))
        .chain(env.quotients().map(|r| &r.name))
    {
        if !names.contains(name) && names.len() == limits.declarations {
            errors.push(format!("{label}: declaration population bound; first omitted identity and role counts retained, unique population incomplete"));
            failures.push(RuntimeEnvironmentRowFailure {
                phase: label,
                name: name.clone(),
                reason: "declaration population bound; subsequent unique population not enumerated"
                    .into(),
            });
            return (Vec::new(), BTreeMap::new(), population);
        }
        names.insert(name.clone());
    }
    population.unique_names = Some(names.len());
    let eager_constants: BTreeSet<_> = env.constants().map(|r| r.name.clone()).collect();
    let mut rows = Vec::new();
    let mut hashes = BTreeMap::new();
    for name in names {
        let fields = env.get_structure_field_names(&name);
        if fields.is_some_and(|fields| fields.len() > limits.declarations) {
            errors.push(format!(
                "{label}: structure field population bound; typed row failure retained"
            ));
            failures.push(RuntimeEnvironmentRowFailure {
                phase: label,
                name,
                reason: "structure field population bound".into(),
            });
            continue;
        }
        let defaults: Vec<_> = fields
            .unwrap_or_default()
            .iter()
            .map(|field| (field, env.get_structure_field_default(&name, field)))
            .collect();
        // get_const has a lazy fallback. It must not invent an eager constant
        // mirror for a specialized-only row or materialize an unbound source.
        let constant = eager_constants
            .contains(&name)
            .then(|| env.get_const(&name))
            .flatten();
        let inductive = env.get_inductive(&name);
        let constructor = env.get_constructor(&name);
        let recursor = env.get_recursor(&name);
        let quotient = env.get_quot(&name);
        let implementation = env.get_implemented_by(&name);
        let parents = env.get_structure_parents(&name);
        let verification = env.declaration_verification(&name);
        let origin = env.get_constant_origin(&name);
        let flags = (
            env.is_partial(&name),
            env.is_unsafe(&name),
            env.is_noncomputable(&name),
        );
        // Borrowed payloads are streamed before any potentially large Vec clone.
        // Kernel Name/Expr/Level serializers re-enter their stack-safe boundary.
        let hash = bounded_hash(
            &(
                &name,
                constant,
                inductive,
                constructor,
                recursor,
                quotient,
                implementation,
                fields,
                &defaults,
                parents,
                verification,
                origin,
                flags,
            ),
            limits.row_bytes.min(*remaining),
        );
        let (hash, bytes) = match hash {
            Ok(value) => value,
            Err(error) => {
                errors.push(format!(
                    "{label}: cannot bind row; typed row failure retained"
                ));
                failures.push(RuntimeEnvironmentRowFailure {
                    phase: label,
                    name,
                    reason: error,
                });
                continue;
            }
        };
        *remaining -= bytes;
        hashes.insert(name.clone(), hash);
        rows.push(RuntimeEnvironmentRow {
            name,
            constant: constant.cloned(),
            inductive: inductive.cloned(),
            constructor: constructor.cloned(),
            recursor: recursor.cloned(),
            quotient: quotient.cloned(),
            implemented_by: implementation.cloned(),
            structure_fields: fields.map(<[Name]>::to_vec),
            structure_defaults: defaults
                .into_iter()
                .map(|(n, e)| (n.clone(), e.cloned()))
                .collect(),
            structure_parents: parents.map(<[(Name, Name)]>::to_vec),
            verification,
            origin: origin.cloned(),
            partial: flags.0,
            unsafe_: flags.1,
            noncomputable: flags.2,
        });
    }
    (rows, hashes, population)
}

impl RuntimeEnvironmentCapture {
    pub(super) fn capture(
        before: &Environment,
        after: &Environment,
        sources: Vec<RuntimeSourceRecord>,
        limits: RuntimeSourceCaptureLimits,
    ) -> Self {
        let mut errors = Vec::new();
        let mut row_failures = Vec::new();
        let source_bytes = sources.iter().try_fold(0usize, |total, source| {
            total
                .checked_add(source.module.len())?
                .checked_add(source.path.len())?
                .checked_add(source.source.len())
        });
        if source_bytes.is_none_or(|bytes| bytes > limits.source_bytes)
            || sources.len() > limits.declarations
        {
            errors.push(
                "source snapshot population/byte bound exceeded; supplied sources retained".into(),
            );
        }
        let mut remaining = limits.total_bytes;
        let (before, baseline, before_population) = snapshot(
            before,
            limits,
            "before",
            &mut remaining,
            &mut errors,
            &mut row_failures,
        );
        let (after, current, after_population) = snapshot(
            after,
            limits,
            "after",
            &mut remaining,
            &mut errors,
            &mut row_failures,
        );
        let mut capture = Self {
            sources,
            before,
            after,
            before_population,
            after_population,
            limitations: vec!["eager declaration union only; lazy declarations and native callbacks are not captured", "implementation/structure metadata is observed for union keys; orphan map keys have no public enumerator and remain unmeasured"],
            row_failures,
            added: BTreeSet::new(),
            changed: BTreeSet::new(),
            removed: BTreeSet::new(),
            delta_complete: errors.is_empty(),
            snapshot_blake3: None,
            errors,
        };
        if capture.delta_complete {
            for row in &capture.after {
                match baseline.get(&row.name) {
                    None => {
                        capture.added.insert(row.name.clone());
                    }
                    Some(before) => match current.get(&row.name) {
                        Some(after) if before == after => {}
                        Some(_) => {
                            capture.changed.insert(row.name.clone());
                        }
                        _ => capture
                            .errors
                            .push(format!("cannot bind environment row {:?}", row.name)),
                    },
                }
            }
            capture.removed = baseline
                .keys()
                .filter(|n| !current.contains_key(*n))
                .cloned()
                .collect();
            if !capture.changed.is_empty() || !capture.removed.is_empty() {
                capture.errors.push(
                    "source check changed or removed baseline declaration payloads/provenance"
                        .into(),
                );
            }
        }
        if capture.sources.is_empty() {
            capture
                .errors
                .push("source capture has no supplied source snapshots".into());
        }
        if capture.errors.is_empty() {
            match bounded_hash(
                &(
                    "clean.runtime-environment-observation/v2-fixed-le",
                    &capture.sources,
                    &capture.before,
                    &capture.after,
                ),
                limits.total_bytes,
            ) {
                Ok((digest, _)) => capture.snapshot_blake3 = Some(digest),
                Err(error) => capture
                    .errors
                    .push(format!("cannot bind environment observation: {error}")),
            }
        }
        capture
    }
}

impl RuntimeEnvironmentRow {
    pub(super) fn catalog(
        &self,
        all: &BTreeMap<Name, &RuntimeEnvironmentRow>,
    ) -> RuntimeCatalogDeclaration {
        let mut issues = Vec::new();
        let mut headers: Vec<(&Name, &[Name], &Expr)> = Vec::new();
        if let Some(r) = &self.constant {
            headers.push((&r.name, &r.level_params, &r.type_));
        }
        if let Some(r) = &self.inductive {
            headers.push((&r.name, &r.level_params, &r.type_));
        }
        if let Some(r) = &self.constructor {
            headers.push((&r.name, &r.level_params, &r.type_));
        }
        if let Some(r) = &self.recursor {
            headers.push((&r.name, &r.level_params, &r.type_));
        }
        if let Some(r) = &self.quotient {
            headers.push((&r.name, &r.level_params, &r.type_));
            issues.push("quotient runtime semantics are not supported by this adapter".into());
        }
        let header = headers.first().copied();
        if headers
            .iter()
            .any(|(name, levels, ty)| *name != &self.name || Some((*name, *levels, *ty)) != header)
        {
            issues.push("environment registry header/name mirrors disagree".into());
        }
        let roles = usize::from(self.inductive.is_some())
            + usize::from(self.constructor.is_some())
            + usize::from(self.recursor.is_some())
            + usize::from(self.quotient.is_some());
        if roles > 1 {
            issues.push("conflicting specialized environment roles".into());
        }
        if self.verification != Some(DeclarationVerification::FullKernelCheck) {
            issues.push("environment declaration lacks full kernel-check provenance; headers remain observations".into());
        }
        if self.noncomputable {
            issues
                .push("noncomputable source declaration has no supported runtime lowering".into());
        }
        let mut kind = self
            .constant
            .as_ref()
            .map(|c| match c.kind {
                clean_kernel::ConstantKind::Definition => ConstantKind::Definition,
                clean_kernel::ConstantKind::Theorem => ConstantKind::Theorem,
                clean_kernel::ConstantKind::Opaque => ConstantKind::Opaque,
                clean_kernel::ConstantKind::Axiom => ConstantKind::Axiom,
            })
            .unwrap_or(ConstantKind::Axiom);
        let mut family = RuntimeFamily::None;
        let mut family_names = BTreeSet::new();
        let mut expressions = Vec::new();
        if let Some(implementation) = &self.implemented_by {
            family_names.insert(implementation.clone());
            issues.push("implemented_by runtime substitution is retained but unsupported".into());
        }
        // Field labels are structure-local identities, not global constants.
        for (_, default) in &self.structure_defaults {
            if let Some(default) = default {
                expressions.push(default.clone());
            }
        }
        if let Some(parents) = &self.structure_parents {
            for (_, parent) in parents {
                family_names.insert(parent.clone());
            }
        }
        let value = self.constant.as_ref().and_then(|c| c.value.clone());
        if let Some(r) = &self.inductive {
            kind = ConstantKind::Inductive;
            if value.is_some() {
                issues.push("inductive mirror unexpectedly has a stored value".into());
            }
            family_names.extend(r.all_names.iter().cloned());
            family_names.extend(r.constructor_names.iter().cloned());
            family = RuntimeFamily::Inductive {
                all: r.all_names.clone(),
                constructors: r.constructor_names.clone(),
                num_params: r.num_params,
                num_indices: r.num_indices,
                // False is exact zero. True gives no exact positive multiplicity.
                num_nested: (!r.is_nested).then_some(0),
                is_nested: r.is_nested,
                is_recursive: r.is_recursive,
                is_unsafe: self.unsafe_,
                is_reflexive: r.is_reflexive,
            };
            if r.is_nested {
                issues.push(
                    "environment exposes only nested flag, not exact positive nested multiplicity"
                        .into(),
                );
            }
        }
        if let Some(r) = &self.constructor {
            kind = ConstantKind::Constructor;
            if value.is_some() {
                issues.push("constructor mirror unexpectedly has a stored value".into());
            }
            family_names.insert(r.inductive_name.clone());
            family = RuntimeFamily::Constructor {
                inductive: r.inductive_name.clone(),
                index: r.constructor_idx,
                num_params: r.num_params,
                num_fields: r.num_fields,
                is_unsafe: self.unsafe_,
            };
        }
        if let Some(r) = &self.recursor {
            family_names.insert(r.inductive_name.clone());
            for rule in &r.rules {
                family_names.insert(rule.constructor_name.clone());
                expressions.push(rule.rhs.clone());
            }
            // Generated casesOn/recOn may have a genuine definition value as
            // well as a recursor registry mirror. Keep and compile that value;
            // retain the full original recursor metadata in this source row.
            if value.is_none() {
                kind = ConstantKind::Recursor;
                if r.arg_order != RecursorArgOrder::MajorAfterMinors {
                    issues.push("value-less recursor argument order is unsupported".into());
                }
                let owners = all
                    .get(&r.inductive_name)
                    .and_then(|r| r.inductive.as_ref())
                    .map(|i| i.all_names.clone());
                if owners.is_none() {
                    issues.push("recursor owner family metadata is absent".into());
                }
                family = RuntimeFamily::Recursor {
                    all: owners.unwrap_or_default(),
                    num_params: r.num_params,
                    num_indices: r.num_indices,
                    num_motives: r.num_motives,
                    num_minors: r.num_minors,
                    k: r.is_k,
                    is_unsafe: self.unsafe_,
                    rules: r
                        .rules
                        .iter()
                        .map(|rule| RuntimeRecursorRule {
                            constructor: rule.constructor_name.clone(),
                            num_fields: rule.num_fields,
                            rhs: Ok(rule.rhs.clone()),
                        })
                        .collect(),
                };
            }
        }
        let (level_params, type_) = match header {
            Some((_, levels, ty)) => {
                expressions.push(ty.clone());
                (levels.to_vec(), Ok(ty.clone()))
            }
            None => {
                issues.push("environment row has no header".into());
                (Vec::new(), Err("environment row has no header".into()))
            }
        };
        let body = match value {
            Some(value) => {
                expressions.push(value.clone());
                RuntimeBody::Stored(Ok(value))
            }
            None if self.partial
                || matches!(
                    kind,
                    ConstantKind::Definition | ConstantKind::Theorem | ConstantKind::Opaque
                ) =>
            {
                issues.push("required runtime body is missing from the source environment".into());
                RuntimeBody::MissingRequiredValue
            }
            None => RuntimeBody::NoStoredValueForKind,
        };
        let dependencies = match references(expressions, 100_000) {
            Ok(mut refs) => {
                refs.extend(family_names);
                refs
            }
            Err(error) => {
                issues.push(error);
                family_names
            }
        };
        RuntimeCatalogDeclaration {
            name: self.name.clone(),
            kind,
            level_params,
            declaration_safety: Some(if self.unsafe_ {
                DefinitionSafety::Unsafe
            } else if self.partial {
                DefinitionSafety::Partial
            } else {
                DefinitionSafety::Safe
            }),
            type_,
            body,
            family,
            dependencies,
            represented_fields_complete: issues.is_empty(),
            issues,
        }
    }
}

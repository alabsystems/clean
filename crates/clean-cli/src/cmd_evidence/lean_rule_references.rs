// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! EV5 shadow check for Lean source references and the reverse control census.

mod scope;
mod source;

use super::{read_json, rule_families::RULE_INVENTORY};
use crate::EvidenceCheckError;
use clean_parser::{parse_name, SurfaceName};
use serde::{Deserialize, Serialize};
use source::{Item, Kind};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    io::{self, Write},
    path::{Component, Path, PathBuf},
};

#[derive(Deserialize)]
struct Inventory {
    spec: Specification,
    rows: Vec<Row>,
}

#[derive(Deserialize)]
struct Specification {
    root: PathBuf,
    #[serde(default)]
    control_roots: BTreeMap<String, PathBuf>,
    rule_carriers: Vec<String>,
}

#[derive(Deserialize)]
struct Row {
    id: String,
    cic_l: Option<Vec<Citation>>,
    groundwork: Option<Vec<Citation>>,
}

#[derive(Deserialize)]
struct Citation {
    #[serde(flatten)]
    reference: Reference,
    control: Option<Control>,
}

#[derive(Clone, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
struct Reference {
    file: PathBuf,
    item: String,
    kind: Kind,
}

#[derive(Deserialize)]
#[serde(untagged, deny_unknown_fields)]
enum Control {
    Theorem { theorem: String, file: PathBuf },
    Exemption { none: String },
}

#[derive(Eq, Ord, PartialEq, PartialOrd, Serialize)]
struct Binding {
    constructor: String,
    theorem: String,
    file: PathBuf,
}

#[derive(PartialEq, Eq)]
struct ControlIdentity {
    file: PathBuf,
    theorem: SurfaceName,
}

struct ResolvedControl {
    identity: ControlIdentity,
    binding: Binding,
}

#[derive(PartialEq, Eq)]
struct RecordedControl {
    constructor: SurfaceName,
    identity: Option<ControlIdentity>,
}

#[derive(Default, Serialize)]
pub(super) struct Report {
    matched: BTreeSet<Reference>,
    controls: BTreeSet<Binding>,
    unreadable: BTreeMap<PathBuf, String>,
    findings: Vec<String>,
}

impl Report {
    pub(super) fn verdict(&self) -> Result<(), EvidenceCheckError> {
        if !self.findings.is_empty() {
            return Err(EvidenceCheckError::Invalid(format!(
                "{} Lean reference finding(s)",
                self.findings.len()
            )));
        }
        if !self.unreadable.is_empty() {
            return Err(EvidenceCheckError::Unavailable(format!(
                "{} Lean source input(s) could not be read completely",
                self.unreadable.len()
            )));
        }
        Ok(())
    }
}

type Source = BTreeMap<SurfaceName, Item>;

struct Sources<'a> {
    root: &'a Path,
    loaded: BTreeMap<PathBuf, Result<Source, String>>,
}

impl Sources<'_> {
    fn get(&mut self, file: &Path) -> Option<&Source> {
        self.loaded
            .entry(file.to_owned())
            .or_insert_with(|| source::load(&self.root.join(file)))
            .as_ref()
            .ok()
    }

    fn get_in_scope(
        &mut self,
        file: &Path,
        scope: &BTreeSet<PathBuf>,
        unreadable: &mut BTreeMap<PathBuf, String>,
    ) -> Result<Option<&Source>, String> {
        if scope.contains(file) {
            return Ok(self.get(file));
        }
        if unreadable.keys().any(|blocked| file.starts_with(blocked)) {
            return Ok(None);
        }
        let absolute = self.root.join(file);
        match fs::symlink_metadata(&absolute) {
            Ok(_) => Err(format!(
                "{} is outside the control census scope",
                file.display()
            )),
            Err(error) => {
                unreadable.insert(file.to_owned(), format!("{}: {error}", absolute.display()));
                Ok(None)
            }
        }
    }
}

fn relative(path: &Path) -> bool {
    !path.as_os_str().is_empty()
        && path
            .components()
            .all(|component| matches!(component, Component::Normal(_)))
}

fn lean_file(path: &Path) -> bool {
    relative(path) && path.extension().is_some_and(|ext| ext == "lean")
}

impl Specification {
    fn control_file(&self, file: &Path) -> Result<PathBuf, String> {
        if !lean_file(file) {
            return Err(format!("invalid Lean control path {}", file.display()));
        }
        let mut roots: BTreeSet<&Path> = self
            .control_roots
            .iter()
            .filter(|(prefix, _)| prefix.is_empty() || file.starts_with(prefix))
            .map(|(_, root)| root.as_path())
            .collect();
        match roots.len() {
            0 => Ok(self.root.join(file)),
            1 => Ok(roots.pop_first().expect("one control root").join(file)),
            _ => Err(format!("ambiguous control roots for {}", file.display())),
        }
    }
}

fn resolve_control(
    spec: &Specification,
    reference: &Reference,
    name: &SurfaceName,
    control: Option<&Control>,
) -> Result<Option<ResolvedControl>, String> {
    let constructor = &reference.item;
    match control {
        Some(Control::Exemption { none }) if !none.trim().is_empty() => return Ok(None),
        Some(Control::Theorem { theorem, file }) => {
            let parsed = parse_name(theorem).map_err(|error| error.to_string())?;
            let expected = format!("{}_control", name.last_component());
            if parsed.last_component().to_string() != expected {
                return Err(format!(
                    "{constructor}'s control {theorem} should end in {expected}"
                ));
            }
            return Ok(Some(ResolvedControl {
                identity: ControlIdentity {
                    file: spec.control_file(file)?,
                    theorem: parsed,
                },
                binding: Binding {
                    constructor: constructor.clone(),
                    theorem: theorem.clone(),
                    file: file.clone(),
                },
            }));
        }
        _ => {}
    }
    Err(format!(
        "{constructor} needs a named control or a nonblank exemption"
    ))
}

fn check_control_binding(
    sources: &mut Sources<'_>,
    scope: &BTreeSet<PathBuf>,
    unreadable: &mut BTreeMap<PathBuf, String>,
    control: &ResolvedControl,
    component: &SurfaceName,
) -> Result<bool, String> {
    let path = &control.identity.file;
    let Some(index) = sources.get_in_scope(path, scope, unreadable)? else {
        return Ok(false);
    };
    if !index
        .get(&control.identity.theorem)
        .is_some_and(|item| item.kind == Kind::Theorem && item.refutes.as_ref() == Some(component))
    {
        return Err(format!(
            "{} in {} does not state a ground Refutes for {}",
            control.binding.theorem,
            path.display(),
            control.binding.constructor
        ));
    }
    Ok(true)
}

fn check_reverse_controls(
    sources: &mut Sources<'_>,
    files: &BTreeSet<PathBuf>,
    recorded: &BTreeMap<SurfaceName, RecordedControl>,
    findings: &mut Vec<String>,
) {
    for file in files {
        let Some(index) = sources.get(file) else {
            continue;
        };
        for (theorem, item) in index {
            let Some(rule) = item
                .refutes
                .as_ref()
                .and_then(|component| recorded.get(component))
            else {
                continue;
            };
            if rule
                .identity
                .as_ref()
                .is_some_and(|identity| identity.file == *file && identity.theorem == *theorem)
            {
                continue;
            }
            let expected = match &rule.identity {
                Some(identity) => format!("{} in {}", identity.theorem, identity.file.display()),
                None => "no control (exemption)".to_owned(),
            };
            findings.push(format!(
                "CONTROL: unexpected ground theorem {theorem} in {} for {}, whose inventory names {expected}",
                file.display(),
                rule.constructor,
            ));
        }
    }
}

fn validate(root: &Path, inventory: &Inventory) -> Result<Report, EvidenceCheckError> {
    let spec = &inventory.spec;
    if !relative(&spec.root) || spec.control_roots.values().any(|path| !relative(path)) {
        return Err(EvidenceCheckError::Invalid(
            "the specification and control roots must be repository-relative paths".to_owned(),
        ));
    }
    let carriers: BTreeSet<SurfaceName> = spec
        .rule_carriers
        .iter()
        .map(|name| parse_name(name))
        .collect::<Result<_, _>>()
        .map_err(|error| EvidenceCheckError::Invalid(format!("invalid rule carrier: {error}")))?;
    let mut sources = Sources {
        root,
        loaded: BTreeMap::new(),
    };
    let mut report = Report::default();
    let control_scope = scope::discover(root, spec, &mut report.unreadable);
    let mut spec_files = BTreeSet::new();
    let mut covered = BTreeSet::new();
    let mut recorded = BTreeMap::new();

    for row in &inventory.rows {
        let cited = row.cic_l.iter().flatten().map(|item| (item, true));
        let groundwork = row.groundwork.iter().flatten().map(|item| (item, false));
        for (citation, rule) in cited.chain(groundwork) {
            let reference = &citation.reference;
            let Ok(name) = parse_name(&reference.item) else {
                report.findings.push(format!(
                    "SPEC: {} has invalid name {}",
                    row.id, reference.item
                ));
                continue;
            };
            if !lean_file(&reference.file) {
                report.findings.push(format!(
                    "SPEC: {} has invalid Lean path {}",
                    row.id,
                    reference.file.display()
                ));
                continue;
            }
            let file = spec.root.join(&reference.file);
            spec_files.insert(file.clone());
            let index = match sources.get_in_scope(&file, &control_scope, &mut report.unreadable) {
                Ok(Some(index)) => index,
                Ok(None) => continue,
                Err(error) => {
                    report.findings.push(format!("SPEC: {}: {error}", row.id));
                    continue;
                }
            };
            if index.get(&name).map(|item| item.kind) != Some(reference.kind) {
                report.findings.push(format!(
                    "SPEC: {} cites {:?} {} in {}, where it is not declared with that kind",
                    row.id,
                    reference.kind,
                    reference.item,
                    reference.file.display()
                ));
                continue;
            }
            report.matched.insert(reference.clone());
            let rule_constructor =
                rule && reference.kind == Kind::Constructor && carriers.contains(&name.parent());
            if rule_constructor {
                covered.insert((file, name.clone()));
                let resolved =
                    match resolve_control(spec, reference, &name, citation.control.as_ref()) {
                        Ok(control) => control,
                        Err(error) => {
                            report
                                .findings
                                .push(format!("CONTROL: {}: {error}", row.id));
                            continue;
                        }
                    };
                let component = name.last_component();
                let identity = resolved.map(|control| {
                    match check_control_binding(
                        &mut sources,
                        &control_scope,
                        &mut report.unreadable,
                        &control,
                        &component,
                    ) {
                        Ok(true) => {
                            report.controls.insert(control.binding);
                        }
                        Ok(false) => {}
                        Err(error) => report
                            .findings
                            .push(format!("CONTROL: {}: {error}", row.id)),
                    }
                    control.identity
                });
                let designation = RecordedControl {
                    constructor: name,
                    identity,
                };
                match recorded.entry(component) {
                    std::collections::btree_map::Entry::Vacant(entry) => {
                        entry.insert(designation);
                    }
                    std::collections::btree_map::Entry::Occupied(entry)
                        if entry.get() != &designation =>
                    {
                        report.findings.push(format!(
                            "CONTROL: {} has a conflicting control designation for rule component {}",
                            row.id, entry.key()
                        ));
                    }
                    std::collections::btree_map::Entry::Occupied(_) => {}
                }
            } else if citation.control.is_some() {
                report.findings.push(format!(
                    "CONTROL: {} assigns a control to {}",
                    row.id, reference.item
                ));
            }
        }
    }
    if spec_files.is_empty() && report.findings.is_empty() {
        report
            .findings
            .push("SPEC: the inventory cites no Lean files".to_owned());
    }
    check_carriers(
        &sources,
        &spec_files,
        &carriers,
        &covered,
        &mut report.findings,
    );
    check_reverse_controls(
        &mut sources,
        &control_scope,
        &recorded,
        &mut report.findings,
    );
    for (file, result) in sources.loaded {
        if let Err(error) = result {
            report.unreadable.entry(file).or_insert(error);
        }
    }
    Ok(report)
}

fn check_carriers(
    sources: &Sources<'_>,
    files: &BTreeSet<PathBuf>,
    carriers: &BTreeSet<SurfaceName>,
    covered: &BTreeSet<(PathBuf, SurfaceName)>,
    findings: &mut Vec<String>,
) {
    let mut seen = BTreeSet::new();
    let mut complete = true;
    for file in files {
        let Some(Ok(index)) = sources.loaded.get(file) else {
            complete = false;
            continue;
        };
        for (name, item) in index {
            if item.kind == Kind::Inductive && carriers.contains(name) && !seen.insert(name.clone())
            {
                findings.push(format!(
                    "SPEC: rule carrier {name} is declared in multiple cited files"
                ));
            }
            if item.kind == Kind::Constructor
                && carriers.contains(&name.parent())
                && !covered.contains(&(file.clone(), name.clone()))
            {
                findings.push(format!(
                    "SPEC: constructor {name} in {} is cited by no rule",
                    file.display()
                ));
            }
        }
    }
    if complete {
        for name in carriers.difference(&seen) {
            findings.push(format!(
                "SPEC: rule carrier {name} is not an inductive in the cited files"
            ));
        }
    }
}

pub(super) fn report_from_snapshot(
    root: &Path,
    bytes: &[u8],
) -> Result<Report, EvidenceCheckError> {
    let inventory = serde_json::from_slice(bytes).map_err(|error| {
        EvidenceCheckError::Invalid(format!("{}: {error}", root.join(RULE_INVENTORY).display()))
    })?;
    validate(root, &inventory)
}

pub(super) fn run(root: &Path) -> anyhow::Result<()> {
    let inventory = read_json(root, RULE_INVENTORY)?;
    let report = validate(root, &inventory)?;
    let mut output = io::stdout().lock();
    serde_json::to_writer_pretty(&mut output, &report)?;
    writeln!(output)?;
    report.verdict()?;
    Ok(())
}

#[cfg(test)]
mod tests;

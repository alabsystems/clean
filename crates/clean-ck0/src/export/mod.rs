//! Independent, bounded lean4export reader. No Clean loader is linked here.
//! Single, mutual and nested inductives are independently derived and compared
//! transactionally. Primitive and accelerated operations require checked signatures.
use crate::{Budget, MinimalEnv, Name, Term, Transparency};
use serde_json::{Map, Value};
use std::collections::{BTreeMap, HashSet};
use std::io::{BufRead, Read};
// Named resource bounds, not soundness checks. Pinned Init measured
// 2026-11-14: 6,354,853 lines and about 324 MiB; CIC_L: 213,321 lines
// and about 11 MiB. Round the honest whole-stream maxima up to the next
// power of two. Per-line, per-root DAG and depth bounds stay independent.
const MAX_EXPORT_LINES: u64 = 8_388_608;
const MAX_EXPORT_BYTES: usize = 536_870_912;
const MAX_LINE_BYTES: usize = 1_048_576;

mod aliases;
mod axiom;
mod dependencies;
mod statement;
mod target;
pub use target::{
    inspect_target, parse_name_components, parse_name_json, replay_target, TargetReport,
    TargetRequest,
};
mod canonical;
mod dag;
mod inductives;
mod json;
mod nested_export;
mod quotient;
mod recursor_export;
mod signature;
mod syntax;
mod telescope;
mod terms;
use syntax::Tables;

/// The wire dialect is independent of the checking environment.
#[derive(Debug, Clone, Copy)]
pub enum Dialect {
    /// lean4export's arena format; provisional until unit Q0 lands.
    Lean4Export31,
}

/// Fail-closed reader/checker boundary errors.
#[derive(Debug, thiserror::Error)]
pub enum Refusal {
    #[error("malformed: {0}")]
    Malformed(String),
    #[error("dangling-index: {0}")]
    Dangling(u64),
    #[error("duplicate: {0}")]
    Duplicate(String),
    #[error("unsupported-rule: {0}")]
    Unsupported(String),
    #[error("primitive-admission: {0}")]
    Primitive(String),
    #[error("admission: {0}")]
    Admission(#[from] crate::inductive::AdmitError),
    #[error("admission: {0}")]
    NestedAdmission(#[from] crate::nested::NestedError),
    #[error("unknown-constant: {0}")]
    UnknownConstant(Name),
    #[error("{0}")]
    Block(std::sync::Arc<Refusal>),
    #[error("target-policy: {0}")]
    Target(String),
    #[error("resource-limit")]
    Limit,
    #[error("universe-scope")]
    UniverseScope,
    #[error("axiom-policy: declaration is outside the checked Ax0 allowlist")]
    Axiom,
    #[error("unsafe-or-partial")]
    Unsafe,
    #[error("validation: {0}")]
    Validation(#[from] crate::ValidateError),
    #[error("type-check: {0}")]
    TypeCheck(#[from] crate::InferError),
    #[error("io: {0}")]
    Io(#[from] std::io::Error),
}
impl Refusal {
    /// Stable reason used by command-minted coverage reports.
    pub fn reason(&self) -> &'static str {
        match self {
            Self::Malformed(_) => "malformed",
            Self::Dangling(_) => "dangling-index",
            Self::Duplicate(_) => "duplicate",
            Self::Unsupported(_) => "unsupported-rule",
            Self::Primitive(_) => "primitive-admission",
            Self::Admission(_) | Self::NestedAdmission(_) => "admission",
            Self::UnknownConstant(_) => "unknown-constant",
            Self::Block(inner) => inner.reason(),
            Self::Target(_) => "target-policy",
            Self::Limit => "resource-limit",
            Self::UniverseScope => "universe-scope",
            Self::Axiom => "axiom-policy",
            Self::Unsafe => "unsafe-or-partial",
            Self::Validation(_) => "validation",
            Self::TypeCheck(_) => "type-check",
            Self::Io(_) => "io",
        }
    }
}
/// A decision for one declared name; a refused name never enters the environment.
#[derive(Debug)]
pub struct Row {
    pub name: Name,
    pub verdict: Result<(), Refusal>,
}
/// Replay result, including the admitted axioms actually present in the stream.
#[derive(Debug, Default)]
pub struct Report {
    pub rows: Vec<Row>,
    pub axioms: Vec<Name>,
}
impl Report {
    /// Counts minted from actual declaration decisions.
    pub fn counts(&self) -> (usize, BTreeMap<&'static str, usize>) {
        let mut accepted = 0usize;
        let mut refused = BTreeMap::new();
        for r in &self.rows {
            match &r.verdict {
                Ok(()) => accepted = accepted.saturating_add(1),
                Err(e) => {
                    let n = refused.entry(e.reason()).or_insert(0usize);
                    *n = n.saturating_add(1);
                }
            }
        }
        (accepted, refused)
    }
}
fn malformed(what: &str) -> Refusal {
    Refusal::Malformed(what.to_owned())
}
fn object(v: &Value) -> Result<&Map<String, Value>, Refusal> {
    v.as_object().ok_or_else(|| malformed("expected object"))
}
fn field<'a>(v: &'a Value, k: &str) -> Result<&'a Value, Refusal> {
    object(v)?.get(k).ok_or_else(|| malformed(k))
}
fn nat(v: &Value) -> Result<u64, Refusal> {
    v.as_u64()
        .ok_or_else(|| malformed("expected natural number"))
}
fn small(v: &Value) -> Result<u32, Refusal> {
    u32::try_from(nat(v)?).map_err(|_| Refusal::Limit)
}
fn text(v: &Value) -> Result<&str, Refusal> {
    v.as_str().ok_or_else(|| malformed("expected string"))
}
fn array(v: &Value) -> Result<&[Value], Refusal> {
    v.as_array()
        .map(Vec::as_slice)
        .ok_or_else(|| malformed("expected array"))
}
fn fields(v: &Value, keys: &[&str]) -> Result<(), Refusal> {
    let o = object(v)?;
    if o.len() != keys.len() || keys.iter().any(|k| !o.contains_key(*k)) {
        return Err(malformed("record fields"));
    }
    Ok(())
}
fn boolean(v: &Value) -> Result<bool, Refusal> {
    v.as_bool().ok_or_else(|| malformed("expected bool"))
}

struct Replay {
    tables: Tables,
    graph: target::Graph,
    canonical: canonical::Canonical,
    env: MinimalEnv,
    declared: HashSet<Name>,
    report: Report,
    checked_aliases: std::collections::HashMap<Name, Name>,
}
impl Replay {
    fn declaration(&mut self, kind: &str, v: &Value) -> Result<(), Refusal> {
        if kind == "inductive" {
            return self.inductive(v);
        }
        let name = self.tables.name(nat(field(v, "name")?)?)?;
        let result = if name.is_anonymous() {
            Err(malformed("anonymous declaration"))
        } else if self.declared.contains(&name) || self.env.hidden_from_export(&name) {
            Err(Refusal::Duplicate(name.to_string()))
        } else {
            self.check_declaration(kind, v, &name)
        };
        self.record(name, result);
        Ok(())
    }
    fn record(&mut self, name: Name, result: Result<(), Refusal>) {
        let verdict = if self.declared.insert(name.clone()) {
            result
        } else {
            Err(Refusal::Duplicate(name.to_string()))
        };
        self.report.rows.push(Row { name, verdict });
    }
    fn check_declaration(&mut self, kind: &str, v: &Value, name: &Name) -> Result<(), Refusal> {
        match kind {
            "axiom" => return self.axiom(v, name),
            "quot" => return self.quotient(v, name),
            "def" => {
                fields(
                    v,
                    &[
                        "name",
                        "levelParams",
                        "type",
                        "value",
                        "hints",
                        "safety",
                        "all",
                    ],
                )?;
                if text(field(v, "safety")?)? != "safe" {
                    return Err(Refusal::Unsafe);
                }
                let hints = field(v, "hints")?;
                if hints != "opaque" && hints != "abbrev" {
                    fields(hints, &["regular"])?;
                    small(field(hints, "regular")?)?;
                }
            }
            "thm" => fields(v, &["name", "levelParams", "type", "value", "all"])?,
            "opaque" => {
                if object(v)?.contains_key("isUnsafe") {
                    fields(
                        v,
                        &["name", "levelParams", "type", "value", "all", "isUnsafe"],
                    )?;
                    if boolean(field(v, "isUnsafe")?)? {
                        return Err(Refusal::Unsafe);
                    }
                } else {
                    fields(v, &["name", "levelParams", "type", "value", "all"])?;
                }
            }
            _ => return Err(Refusal::Unsupported(kind.to_owned())),
        }
        let decision = crate::whnf::DecisionScope::enter();
        for i in array(field(v, "all")?)? {
            self.tables.name(nat(i)?)?;
        }
        let params: Vec<Name> = array(field(v, "levelParams")?)?
            .iter()
            .map(|i| self.tables.name(nat(i)?))
            .collect::<Result<_, _>>()?;
        if params.iter().collect::<HashSet<_>>().len() != params.len()
            || params.iter().any(Name::is_anonymous)
        {
            return Err(Refusal::UniverseScope);
        }
        let arity = u32::try_from(params.len()).map_err(|_| Refusal::Limit)?;
        let ty = self.term(&self.env, nat(field(v, "type")?)?, &params)?;
        let mut budget = Budget::default_budget();
        let sort = crate::infer_sort(&self.env, &ty, &mut budget)?;
        if kind == "thm" && !sort.is_zero() {
            return Err(malformed("theorem type must be a proposition"));
        }
        let body = self.term(&self.env, nat(field(v, "value")?)?, &params)?;
        crate::check(&self.env, &body, &ty, &mut budget)?;
        let transparency = if kind == "def" {
            Transparency::Transparent
        } else {
            Transparency::Opaque
        };
        let alias = self.prepare_alias(name, arity)?;
        let alias_type = ty.clone();
        let candidates = self.canonical.candidate(kind, v, &self.tables)?;
        let advice = target::prepare(
            kind,
            v,
            &self.tables,
            crate::validate::Env::string_literal_view(&self.env),
        )?;
        drop(decision);
        self.env =
            std::mem::take(&mut self.env).with_def(name.clone(), arity, ty, body, transparency);
        if kind == "def" {
            let hints = field(v, "hints")?;
            let priority = if hints == "abbrev" {
                u64::MAX
            } else if hints == "opaque" {
                0
            } else {
                u64::from(small(field(hints, "regular")?)?).saturating_add(1)
            };
            self.env.set_delta_priority(name.clone(), priority);
        }
        if let Some(alias) = alias {
            self.env = std::mem::take(&mut self.env).with_def(
                alias.name.clone(),
                arity,
                alias_type,
                alias.value,
                Transparency::Transparent,
            );
            let priority = crate::validate::Env::delta_priority(&self.env, name);
            self.env.set_delta_priority(alias.name.clone(), priority);
            self.env.hide_from_export(alias.name.clone());
            self.checked_aliases.insert(name.clone(), alias.name);
        }
        self.canonical.commit(candidates, &mut self.env);
        self.graph.extend(advice);
        Ok(())
    }
}

/// Replay a bounded stream. Syntax errors stop the export; semantic refusals
/// remain named rows and later independent declarations are still checked.
/// Limits are conservative availability refusals, never evidence of acceptance.
pub fn replay(input: impl BufRead, dialect: Dialect) -> Result<Report, Refusal> {
    replay_state(input, dialect).map(|state| state.report)
}
#[cfg(test)]
fn replay_environment(
    input: impl BufRead,
    dialect: Dialect,
) -> Result<(Report, MinimalEnv), Refusal> {
    replay_state(input, dialect).map(|state| (state.report, state.env))
}
fn replay_state(mut input: impl BufRead, dialect: Dialect) -> Result<Replay, Refusal> {
    // The same wire subterm can be used by many declarations. Keep exact
    // node sharing across the stream; semantic decision caches still clear
    // between decisions/environments, and the pool owns only weak entries.
    let _dag = crate::term_dag::DagScope::enter();
    let mut env = MinimalEnv::new();
    env.restrict_native_nat_folds();
    let mut state = Replay {
        tables: Tables::new(),
        graph: target::Graph::new(),
        canonical: canonical::Canonical::default(),
        env,
        declared: HashSet::new(),
        report: Report::default(),
        checked_aliases: std::collections::HashMap::new(),
    };
    let mut meta = false;
    let mut lines = 0u64;
    let mut total_bytes = 0usize;
    loop {
        let mut bytes = Vec::new();
        let n = input
            .by_ref()
            .take(
                u64::try_from(MAX_LINE_BYTES)
                    .unwrap_or(u64::MAX)
                    .saturating_add(1),
            )
            .read_until(b'\n', &mut bytes)?;
        if n == 0 {
            break;
        }
        total_bytes = total_bytes.saturating_add(n);
        if n > MAX_LINE_BYTES || total_bytes > MAX_EXPORT_BYTES {
            return Err(Refusal::Limit);
        }
        lines = lines.saturating_add(1);
        if lines > MAX_EXPORT_LINES {
            return Err(Refusal::Limit);
        }
        let v =
            json::parse(&bytes).map_err(|e| Refusal::Malformed(format!("line {lines}: {e}")))?;
        let o = object(&v)?;
        if !meta {
            fields(&v, &["meta"])?;
            let m = field(&v, "meta")?;
            fields(m, &["exporter", "lean", "format"])?;
            fields(field(m, "format")?, &["version"])?;
            fields(field(m, "exporter")?, &["name", "version"])?;
            fields(field(m, "lean")?, &["version", "githash"])?;
            for (k, names) in [
                ("exporter", vec!["name", "version"]),
                ("lean", vec!["version", "githash"]),
            ] {
                for name in names {
                    text(field(field(m, k)?, name)?)?;
                }
            }
            match dialect {
                Dialect::Lean4Export31
                    if text(field(field(m, "format")?, "version")?)? == "3.1.0" => {}
                _ => return Err(Refusal::Unsupported("dialect".to_owned())),
            }
            if !["4.29.1", "4.30.0-rc2", "4.30.0"]
                .contains(&text(field(field(m, "lean")?, "version")?)?)
            {
                return Err(Refusal::Unsupported("Lean-version".to_owned()));
            }
            state
                .canonical
                .select_version(text(field(field(m, "lean")?, "version")?)?);
            meta = true;
        } else if o.contains_key("in") || o.contains_key("il") || o.contains_key("ie") {
            state.tables.bind(&v)?;
        } else {
            if o.len() != 1 {
                return Err(malformed("declaration record"));
            }
            let (kind, data) = o.iter().next().ok_or_else(|| malformed("empty record"))?;
            state.declaration(kind, data)?;
        }
    }
    if !meta {
        return Err(malformed("missing meta"));
    }
    Ok(state)
}

/// Lossless wire names: string and numeric components remain distinct. Numeric
/// components are decimal strings, including values above JSON's safe integer range.
pub fn name_components(name: &Name) -> Value {
    let mut components = Vec::new();
    let mut current = name.clone();
    while let Some(parent) = current.parent() {
        if let Some(s) = current.last_str() {
            components.push(serde_json::json!({"str": s}));
        } else if let Some(n) = current.last_num() {
            components.push(serde_json::json!({"num": n.to_string()}));
        }
        current = parent;
    }
    components.reverse();
    Value::Array(components)
}

#[cfg(test)]
mod bound_tests;
#[cfg(test)]
mod tests;

#[cfg(test)]
mod native_tests;
#[cfg(test)]
mod reduced_field_tests;
#[cfg(test)]
mod target_tests;
#[cfg(test)]
mod unit_like_tests;

#[cfg(test)]
mod helper_transport_tests;
#[cfg(test)]
mod lambda_index_tests;

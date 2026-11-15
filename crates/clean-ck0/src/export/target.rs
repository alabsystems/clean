//! Target identity and the dependency graph of successful checking decisions.
use super::*;
use std::collections::HashMap;
use std::sync::Arc;

/// A caller-supplied statement commitment; names retain component identity.
#[derive(Debug, Clone)]
pub struct TargetRequest {
    pub name: Name,
    pub statement_sha256: String,
}
/// A target decision. Inspection produces `matched == false`; only an explicit
/// caller pin can produce a matched result. The stream's coverage is retained.
#[derive(Debug)]
pub struct TargetReport {
    pub report: Report,
    pub name: Name,
    pub statement_sha256: String,
    pub matched: bool,
    pub axioms: Vec<Name>,
}
pub(super) struct Advice {
    kind: String,
    ty: u64,
    params: Vec<Name>,
    deps: Arc<Vec<Name>>,
}
pub(super) type Graph = HashMap<Name, Advice>;
pub(super) fn prepare(
    kind: &str,
    value: &Value,
    tables: &Tables,
    string_view: bool,
) -> Result<Vec<(Name, Advice)>, Refusal> {
    let mut members = Vec::new();
    if kind == "inductive" {
        for family in ["types", "ctors", "recs"] {
            for m in array(field(value, family)?)? {
                members.push((family, m));
            }
        }
    } else {
        members.push((kind, value));
    }
    let mut deps = HashSet::new();
    for (_, m) in &members {
        tables.dependencies(nat(field(m, "type")?)?, &mut deps, string_view)?;
        if let Some(v) = object(m)?.get("value") {
            tables.dependencies(nat(v)?, &mut deps, string_view)?;
        }
        if let Some(rules) = object(m)?.get("rules") {
            for r in array(rules)? {
                tables.dependencies(nat(field(r, "rhs")?)?, &mut deps, string_view)?;
            }
        }
    }
    // Checking an inductive needs the complete simultaneous block. Keep that
    // admission closure shared rather than copying it for every member.
    let deps = Arc::new(deps.into_iter().collect());
    let mut out = Vec::new();
    for (kind, m) in members {
        let params = array(field(m, "levelParams")?)?
            .iter()
            .map(|p| tables.name(nat(p)?))
            .collect::<Result<_, _>>()?;
        out.push((
            tables.name(nat(field(m, "name")?)?)?,
            Advice {
                kind: kind.into(),
                ty: nat(field(m, "type")?)?,
                params,
                deps: Arc::clone(&deps),
            },
        ));
    }
    Ok(out)
}
impl Replay {
    pub(super) fn target(self, name: Name, pin: Option<&str>) -> Result<TargetReport, Refusal> {
        if pin.is_some() && self.report.rows.iter().any(|row| row.verdict.is_err()) {
            return Err(Refusal::Target(
                "stream contains refused declarations".into(),
            ));
        }
        let decisions: Vec<_> = self.report.rows.iter().filter(|r| r.name == name).collect();
        if decisions.len() != 1 || decisions.first().is_none_or(|r| r.verdict.is_err()) {
            return Err(Refusal::Target(
                "target must have exactly one accepted declaration".into(),
            ));
        }
        let advice = self
            .graph
            .get(&name)
            .ok_or_else(|| Refusal::Target("missing target".into()))?;
        if advice.kind != "thm" {
            return Err(Refusal::Target("target must be a theorem".into()));
        }
        let raw = self.tables.expr(advice.ty, &advice.params)?;
        let statement_sha256 = statement::hash(
            &raw,
            u32::try_from(advice.params.len()).map_err(|_| Refusal::Limit)?,
        )?;
        if let Some(pin) = pin {
            if pin.len() != 64
                || !pin
                    .bytes()
                    .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
            {
                return Err(Refusal::Target(
                    "statement pin must be 64 lowercase hex digits".into(),
                ));
            }
            if pin != statement_sha256 {
                return Err(Refusal::Target("statement pin mismatch".into()));
            }
        }
        let mut reached = HashSet::new();
        let mut todo = vec![name.clone()];
        let mut axioms = Vec::new();
        while let Some(n) = todo.pop() {
            if !reached.insert(n.clone()) {
                continue;
            }
            let node = self
                .graph
                .get(&n)
                .ok_or_else(|| Refusal::Target("incomplete checked dependency closure".into()))?;
            if node.kind == "axiom" {
                axioms.push(n);
            }
            todo.extend(node.deps.iter().filter(|d| !reached.contains(*d)).cloned());
        }
        // Name has no order; component JSON is lossless and deterministic.
        axioms.sort_by_key(|n| name_components(n).to_string());
        Ok(TargetReport {
            report: self.report,
            name,
            statement_sha256,
            matched: pin.is_some(),
            axioms,
        })
    }
}
/// Inspect an admitted theorem's statement and actual checked axiom closure.
/// This does not produce a statement-bound verdict.
pub fn inspect_target(
    input: impl BufRead,
    dialect: Dialect,
    name: Name,
) -> Result<TargetReport, Refusal> {
    replay_state(input, dialect)?.target(name, None)
}
/// Require an accepted theorem, the caller's exact statement commitment, and a
/// complete checked dependency closure. Statement-bound mode requires every
/// declaration to pass; inspection may diagnose a partially refused stream.
pub fn replay_target(
    input: impl BufRead,
    dialect: Dialect,
    request: TargetRequest,
) -> Result<TargetReport, Refusal> {
    replay_state(input, dialect)?.target(request.name, Some(&request.statement_sha256))
}
/// Parse a hierarchical name without conflating numeric/string components.
pub fn parse_name_components(value: &Value) -> Result<Name, Refusal> {
    let components = array(value)?;
    if components.is_empty() || components.len() > 64 {
        return Err(malformed("target name"));
    }
    let mut out = Name::anonymous();
    for component in components {
        let o = object(component)?;
        if o.len() != 1 {
            return Err(malformed("target name component"));
        }
        if let Some(s) = o.get("str") {
            let s = text(s)?;
            if s.chars().any(char::is_control) {
                return Err(malformed("control character in name"));
            }
            out = out.str(s);
        } else if let Some(n) = o.get("num") {
            let n = text(n)?;
            let integer = n
                .parse::<u64>()
                .map_err(|_| malformed("target numeric component"))?;
            if integer.to_string() != n {
                return Err(malformed("noncanonical target numeric component"));
            }
            out = out.num(integer);
        } else {
            return Err(malformed("target name component"));
        }
    }
    Ok(out)
}

/// Strict JSON counterpart of parse_name_components (duplicate keys refuse).
pub fn parse_name_json(input: &str) -> Result<Name, Refusal> {
    if input.len() > 1_048_576 {
        return Err(Refusal::Limit);
    }
    let value = json::parse(input.as_bytes()).map_err(|e| malformed(&e.to_string()))?;
    parse_name_components(&value)
}

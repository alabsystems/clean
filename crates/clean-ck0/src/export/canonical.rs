//! Exact pinned standard declarations license accelerators, never just a name.
//! Actual declarations still pass ordinary admission first. The complete raw
//! signature/body and every external dependency must match the reference.
use super::*;
use crate::{RawExpr, RawLit};
use std::collections::HashMap;
use std::sync::OnceLock;

#[derive(Debug, Clone, PartialEq, Eq)]
struct Member {
    kind: String,
    name: Name,
    arity: usize,
    header: Vec<Value>,
    roots: Vec<RawExpr>,
}
#[derive(Debug, Clone, PartialEq, Eq)]
struct Block(Vec<Member>);
struct Reference(HashMap<Name, Block>);
static REFERENCE: OnceLock<Result<Reference, String>> = OnceLock::new();
static REFERENCE_429: OnceLock<Result<Reference, String>> = OnceLock::new();
const CURRENT: &str = include_str!("../../tests/fixtures/q2-part2/native-reference.ndjson");
const LEGACY: &str = include_str!("../../tests/fixtures/q2-part2/native-reference-4.29.1.ndjson");

#[derive(Default)]
pub(super) struct Canonical {
    admitted: HashSet<Name>,
    legacy: bool,
}
impl Canonical {
    pub(super) fn select_version(&mut self, version: &str) {
        self.legacy = version == "4.29.1";
    }
    pub(super) fn contains(&self, name: &Name) -> bool {
        self.admitted.contains(name)
    }
    pub(super) fn candidate(
        &self,
        kind: &str,
        value: &Value,
        tables: &Tables,
    ) -> Result<Vec<Name>, Refusal> {
        let reference = if self.legacy {
            REFERENCE_429.get_or_init(|| Reference::legacy().map_err(|e| e.to_string()))
        } else {
            REFERENCE.get_or_init(|| Reference::read(CURRENT).map_err(|e| e.to_string()))
        };
        let reference = reference.as_ref().map_err(|s| malformed(s))?;
        let first = if kind == "inductive" {
            array(field(value, "types")?)?
                .first()
                .ok_or_else(|| malformed("empty block"))?
        } else {
            value
        };
        let name = tables.name(nat(field(first, "name")?)?)?;
        let Some(expected) = reference.0.get(&name) else {
            return Ok(vec![]);
        };
        let actual = block(kind, value, tables)?;
        if &actual != expected {
            return Ok(vec![]);
        }
        let names: HashSet<_> = actual.0.iter().map(|m| m.name.clone()).collect();
        let mut deps = HashSet::new();
        for m in &actual.0 {
            for root in &m.roots {
                dependencies(root, &mut deps);
            }
        }
        if deps
            .iter()
            .any(|d| !names.contains(d) && !self.admitted.contains(d))
        {
            return Ok(vec![]);
        }
        Ok(actual.0.into_iter().map(|m| m.name).collect())
    }
    pub(super) fn commit(&mut self, names: Vec<Name>, env: &mut MinimalEnv) {
        for name in names {
            if name.parent() == Some(Name::from_dotted("Nat"))
                && matches!(
                    name.last_str(),
                    Some(
                        "succ"
                            | "add"
                            | "sub"
                            | "mul"
                            | "div"
                            | "mod"
                            | "pow"
                            | "beq"
                            | "ble"
                            | "gcd"
                            | "land"
                            | "lor"
                            | "xor"
                            | "shiftLeft"
                            | "shiftRight"
                    )
                )
            {
                env.license_native_nat(name.clone());
            }
            self.admitted.insert(name);
        }
        if [
            "String",
            "String.ofList",
            "Char.ofNat",
            "List.nil",
            "List.cons",
        ]
        .iter()
        .all(|n| self.contains(&Name::from_dotted(n)))
        {
            env.license_string_literal_view();
        }
    }
}
impl Reference {
    fn legacy() -> Result<Self, Refusal> {
        let mut legacy = Self::read(LEGACY)?;
        // The older Prelude export omits some fixed intrinsic declarations.
        // Fixed Ax0/quotient signatures and their missing logical Iff
        // prerequisite may supplement it. Nat computation bodies never mix
        // across profiles; Iff still passes full inductive/recursor admission.
        for (name, block) in Self::read(CURRENT)?.0 {
            if name == Name::from_dotted("Iff")
                || block
                    .0
                    .iter()
                    .all(|m| matches!(m.kind.as_str(), "axiom" | "quot"))
            {
                legacy.0.entry(name).or_insert(block);
            }
        }
        Ok(legacy)
    }
    fn read(source: &str) -> Result<Self, Refusal> {
        let mut tables = Tables::new();
        let mut entries = HashMap::new();
        for line in source.lines() {
            let v = json::parse(line.as_bytes()).map_err(|e| malformed(&e.to_string()))?;
            let o = object(&v)?;
            if o.contains_key("meta") {
                continue;
            }
            if o.contains_key("in") || o.contains_key("il") || o.contains_key("ie") {
                tables.bind(&v)?;
            } else {
                let (kind, data) = o
                    .iter()
                    .next()
                    .ok_or_else(|| malformed("reference record"))?;
                let signature = block(kind, data, &tables)?;
                if let Some(first) = signature.0.first() {
                    entries.insert(first.name.clone(), signature);
                }
            }
        }
        Ok(Self(entries))
    }
}
fn member(kind: &str, v: &Value, tables: &Tables) -> Result<Member, Refusal> {
    let params: Vec<_> = array(field(v, "levelParams")?)?
        .iter()
        .map(|p| tables.name(nat(p)?))
        .collect::<Result<_, _>>()?;
    let mut roots = vec![tables.expr(nat(field(v, "type")?)?, &params)?];
    if let Some(body) = object(v)?.get("value") {
        roots.push(tables.expr(nat(body)?, &params)?);
    }
    if let Some(rules) = object(v)?.get("rules") {
        for rule in array(rules)? {
            roots.push(tables.expr(nat(field(rule, "rhs")?)?, &params)?);
        }
    }
    for root in &mut roots {
        erase_binders(root)?;
    }
    let keys = [
        "numParams",
        "numIndices",
        "numFields",
        "numMotives",
        "numMinors",
        "numNested",
        "cidx",
        "k",
        "isRec",
        "isReflexive",
        "isUnsafe",
        "kind",
        "safety",
    ];
    let header = keys
        .iter()
        .map(|k| {
            object(v)
                .ok()
                .and_then(|o| o.get(*k))
                .cloned()
                .unwrap_or(Value::Null)
        })
        .collect();
    Ok(Member {
        kind: kind.into(),
        name: tables.name(nat(field(v, "name")?)?)?,
        arity: params.len(),
        header,
        roots,
    })
}
fn block(kind: &str, v: &Value, tables: &Tables) -> Result<Block, Refusal> {
    let mut members = Vec::new();
    if kind == "inductive" {
        for family in ["types", "ctors", "recs"] {
            for m in array(field(v, family)?)? {
                members.push(member(family, m, tables)?);
            }
        }
    } else {
        members.push(member(kind, v, tables)?);
    }
    Ok(Block(members))
}
fn erase_binders(raw: &mut RawExpr) -> Result<(), Refusal> {
    erase_binders_rec(raw, &mut crate::rawexpr::RawMemo::new())
}
fn erase_binders_rec(raw: &mut RawExpr, memo: &mut crate::rawexpr::RawMemo) -> Result<(), Refusal> {
    if matches!(raw, RawExpr::Shared(_)) {
        return crate::rawexpr::map_shared(raw, memo, erase_binders_rec);
    }
    match raw {
        RawExpr::Pi(bi, a, b) | RawExpr::Lam(bi, a, b) => {
            *bi = crate::rawexpr::BinderInfo::Default;
            erase_binders_rec(a, memo)?;
            erase_binders_rec(b, memo)?;
        }
        RawExpr::App(a, b) => {
            erase_binders_rec(a, memo)?;
            erase_binders_rec(b, memo)?;
        }
        RawExpr::Let(a, b, c) => {
            erase_binders_rec(a, memo)?;
            erase_binders_rec(b, memo)?;
            erase_binders_rec(c, memo)?;
        }
        RawExpr::Proj(_, _, e) => erase_binders_rec(e, memo)?,
        _ => {}
    }
    Ok(())
}
pub(super) fn dependencies(raw: &RawExpr, out: &mut HashSet<Name>) {
    dependencies_rec(raw, out, &mut HashSet::new());
}
fn dependencies_rec(raw: &RawExpr, out: &mut HashSet<Name>, seen: &mut HashSet<*const RawExpr>) {
    match raw {
        RawExpr::Shared(node) => {
            if seen.insert(std::sync::Arc::as_ptr(node)) {
                dependencies_rec(node, out, seen);
            }
        }
        RawExpr::Const(n, _) => {
            out.insert(n.clone());
        }
        RawExpr::Elim(n, _, _) => {
            out.insert(n.str("rec"));
        }
        RawExpr::Pi(_, a, b) | RawExpr::Lam(_, a, b) | RawExpr::App(a, b) => {
            dependencies_rec(a, out, seen);
            dependencies_rec(b, out, seen);
        }
        RawExpr::Let(a, b, c) => {
            dependencies_rec(a, out, seen);
            dependencies_rec(b, out, seen);
            dependencies_rec(c, out, seen);
        }
        RawExpr::Proj(n, _, e) => {
            out.insert(n.clone());
            dependencies_rec(e, out, seen);
        }
        RawExpr::Lit(RawLit::Nat(_)) => {
            out.insert(Name::from_dotted("Nat"));
        }
        RawExpr::Lit(RawLit::Str(_)) => {
            out.insert(Name::from_dotted("String"));
        }
        _ => {}
    }
}

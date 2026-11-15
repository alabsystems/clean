//! Indexed wire syntax. References precede uses; each root retains export-id
//! sharing and is charged for its distinct nodes before allocation.
use super::{array, boolean, field, fields, malformed, nat, object, small, text, Refusal};
use crate::rawexpr::BinderInfo;
use crate::{Name, RawExpr, RawLevel};
use serde_json::Value;
use std::collections::HashMap;

/// Resource bound, not a soundness check: the deepest wire expression the
/// reader materializes. The reader walks a DAG path by native recursion before the
/// kernel's iterative depth gate ([`crate::MAX_VALIDATE_DEPTH`], 1024) sees
/// it, so this stays at half that gate. Honest exports measured 2026-11-13
/// (Q4 follow-up): Clean's CIC_L export peaks at depth 151
/// (`CICL.ConstructorCertificate.noConfusion`, refused at the former 128),
/// pinned Lean v4.30.0-rc2 Init at 325 (`Lean.Meta.instReprConfig_1.repr`).
pub(super) const MAX_WIRE_DEPTH: u64 = 512;
/// Resource bound, not a soundness check: distinct expression nodes plus
/// literal payload and the bounded levels carried by each node, per root.
/// The reader counts each export id once before building its shared node.
/// Honest-subject measurements and the derivation are recorded by lane Q.
pub(super) const MAX_WIRE_DAG: u64 = 1_000_000;

pub(super) struct Tables {
    names: HashMap<u64, (Name, u64)>,
    levels: HashMap<u64, (String, Value, u64, u64)>,
    exprs: HashMap<u64, (String, Value, u64, u64)>,
}
impl Tables {
    pub(super) fn new() -> Self {
        Self {
            names: HashMap::from([(0, (Name::anonymous(), 0))]),
            levels: HashMap::from([(0, ("zero".to_owned(), Value::Null, 1, 0))]),
            exprs: HashMap::new(),
        }
    }
    pub(super) fn name(&self, i: u64) -> Result<Name, Refusal> {
        self.names
            .get(&i)
            .map(|v| v.0.clone())
            .ok_or(Refusal::Dangling(i))
    }
    pub(super) fn bind(&mut self, v: &Value) -> Result<(), Refusal> {
        let o = object(v)?;
        if o.len() != 2 {
            return Err(malformed("table record needs index and constructor"));
        }
        let table = ["in", "il", "ie"]
            .into_iter()
            .find(|k| o.contains_key(*k))
            .ok_or_else(|| malformed("table index"))?;
        let i = nat(field(v, table)?)?;
        let (kind, data) = o
            .iter()
            .find(|(k, _)| k.as_str() != table)
            .ok_or_else(|| malformed("table constructor"))?;
        match table {
            "in" => {
                if self.names.contains_key(&i) {
                    return Err(Refusal::Duplicate(format!("name index {i}")));
                }
                let pre = nat(field(data, "pre")?)?;
                let (parent, depth) = self.names.get(&pre).ok_or(Refusal::Dangling(pre))?;
                if *depth >= 64 {
                    return Err(Refusal::Limit);
                }
                let name = match kind.as_str() {
                    "str" => {
                        fields(data, &["pre", "str"])?;
                        let component = text(field(data, "str")?)?;
                        if component.chars().any(char::is_control) {
                            return Err(malformed("control character in name"));
                        }
                        parent.str(component)
                    }
                    "num" => {
                        fields(data, &["pre", "i"])?;
                        parent.num(nat(field(data, "i")?)?)
                    }
                    _ => return Err(Refusal::Unsupported(kind.clone())),
                };
                self.names.insert(i, (name, depth.saturating_add(1)));
            }
            "il" => {
                if self.levels.contains_key(&i) {
                    return Err(Refusal::Duplicate(format!("level index {i}")));
                }
                let children = match kind.as_str() {
                    "succ" => vec![nat(data)?],
                    "max" | "imax" => {
                        let a = array(data)?;
                        if a.len() != 2 {
                            return Err(malformed("binary level arity"));
                        }
                        a.iter().map(nat).collect::<Result<Vec<_>, _>>()?
                    }
                    "param" => {
                        self.name(nat(data)?)?;
                        vec![]
                    }
                    _ => return Err(Refusal::Unsupported(kind.clone())),
                };
                let (size, depth) = measure(&self.levels, &children, 256, 64)?;
                self.levels
                    .insert(i, (kind.clone(), data.clone(), size, depth));
            }
            "ie" => {
                if self.exprs.contains_key(&i) {
                    return Err(Refusal::Duplicate(format!("expression index {i}")));
                }
                let children = self.expr_children(kind, data)?;
                let (_, depth) = measure(&self.exprs, &children, u64::MAX, MAX_WIRE_DEPTH)?;
                let mut size = 1u64;
                // A payload is owned once by its shared node. It remains
                // charged in full; sharing cannot hide an oversized literal.
                if kind == "strVal" || kind == "natVal" {
                    size = size.saturating_add(
                        u64::try_from(text(data)?.len()).map_err(|_| Refusal::Limit)?,
                    );
                }
                if kind == "const" {
                    for l in array(field(data, "us")?)? {
                        size = size.saturating_add(self.level_entry(nat(l)?)?.2);
                    }
                } else if kind == "sort" {
                    size = size.saturating_add(self.level_entry(nat(data)?)?.2);
                }
                if size > MAX_WIRE_DAG {
                    return Err(Refusal::Limit);
                }
                self.exprs
                    .insert(i, (kind.clone(), data.clone(), size, depth));
            }
            _ => return Err(malformed("unknown table")),
        }
        Ok(())
    }
    pub(super) fn expr_children(&self, k: &str, d: &Value) -> Result<Vec<u64>, Refusal> {
        let refs: &[&str] = match k {
            "bvar" => {
                small(d)?;
                return Ok(vec![]);
            }
            "sort" => {
                self.level_entry(nat(d)?)?;
                return Ok(vec![]);
            }
            "const" => {
                fields(d, &["name", "us"])?;
                self.name(nat(field(d, "name")?)?)?;
                for l in array(field(d, "us")?)? {
                    self.level_entry(nat(l)?)?;
                }
                if array(field(d, "us")?)?.len() > 256 {
                    return Err(Refusal::Limit);
                }
                return Ok(vec![]);
            }
            "app" => {
                fields(d, &["fn", "arg"])?;
                &["fn", "arg"]
            }
            "lam" | "forallE" => {
                fields(d, &["name", "type", "body", "binderInfo"])?;
                self.name(nat(field(d, "name")?)?)?;
                binder(field(d, "binderInfo")?)?;
                &["type", "body"]
            }
            "letE" => {
                fields(d, &["name", "type", "value", "body", "nondep"])?;
                self.name(nat(field(d, "name")?)?)?;
                boolean(field(d, "nondep")?)?;
                &["type", "value", "body"]
            }
            "proj" => {
                fields(d, &["typeName", "idx", "struct"])?;
                self.name(nat(field(d, "typeName")?)?)?;
                small(field(d, "idx")?)?;
                &["struct"]
            }
            "natVal" => {
                let s = text(d)?;
                if s.is_empty() || !s.bytes().all(|b| b.is_ascii_digit()) {
                    return Err(malformed("natural literal"));
                }
                if s.len() > 4096 {
                    return Err(Refusal::Limit);
                }
                return Ok(vec![]);
            }
            "strVal" => {
                text(d)?;
                return Ok(vec![]);
            }
            "mdata" => {
                fields(d, &["expr", "data"])?;
                object(field(d, "data")?)?;
                &["expr"]
            }
            // Free variables and metavariables are deliberately refused.
            _ => return Err(Refusal::Unsupported(k.to_owned())),
        };
        refs.iter().map(|k| nat(field(d, k)?)).collect()
    }
    pub(super) fn expr_entry(&self, i: u64) -> Result<&(String, Value, u64, u64), Refusal> {
        self.exprs.get(&i).ok_or(Refusal::Dangling(i))
    }
    fn level_entry(&self, i: u64) -> Result<&(String, Value, u64, u64), Refusal> {
        self.levels.get(&i).ok_or(Refusal::Dangling(i))
    }
    fn level(&self, i: u64, params: &[Name]) -> Result<RawLevel, Refusal> {
        let (kind, data, _, _) = self.level_entry(i)?;
        Ok(match kind.as_str() {
            "zero" => RawLevel::Zero,
            "param" => {
                let name = self.name(nat(data)?)?;
                let p = params
                    .iter()
                    .position(|n| n == &name)
                    .ok_or(Refusal::UniverseScope)?;
                RawLevel::Param(u32::try_from(p).map_err(|_| Refusal::Limit)?)
            }
            "succ" => RawLevel::Succ(Box::new(self.level(nat(data)?, params)?)),
            "max" | "imax" => {
                let a = array(data)?;
                let first = a.first().ok_or_else(|| malformed("level pair"))?;
                let second = a.get(1).ok_or_else(|| malformed("level pair"))?;
                let lhs = Box::new(self.level(nat(first)?, params)?);
                let rhs = Box::new(self.level(nat(second)?, params)?);
                if kind == "max" {
                    RawLevel::Max(lhs, rhs)
                } else {
                    RawLevel::IMax(lhs, rhs)
                }
            }
            _ => return Err(Refusal::Unsupported(kind.clone())),
        })
    }
    pub(super) fn expr(&self, i: u64, params: &[Name]) -> Result<RawExpr, Refusal> {
        {
            let mut remaining = MAX_WIRE_DAG;
            self.expr_shared(i, params, &mut HashMap::new(), &mut remaining)
        }
    }
    fn expr_shared(
        &self,
        i: u64,
        params: &[Name],
        memo: &mut HashMap<u64, RawExpr>,
        remaining: &mut u64,
    ) -> Result<RawExpr, Refusal> {
        if let Some(node) = memo.get(&i) {
            return Ok(node.clone());
        }
        let (k, d, weight, _) = self.exprs.get(&i).ok_or(Refusal::Dangling(i))?;
        *remaining = remaining.checked_sub(*weight).ok_or(Refusal::Limit)?;
        let mut sub = |key| {
            self.expr_shared(nat(field(d, key)?)?, params, memo, remaining)
                .map(Box::new)
        };
        let node = match k.as_str() {
            "bvar" => RawExpr::BVar(small(d)?),
            "sort" => RawExpr::Sort(self.level(nat(d)?, params)?),
            "const" => RawExpr::Const(
                self.name(nat(field(d, "name")?)?)?,
                array(field(d, "us")?)?
                    .iter()
                    .map(|l| self.level(nat(l)?, params))
                    .collect::<Result<_, _>>()?,
            ),
            "app" => RawExpr::App(sub("fn")?, sub("arg")?),
            "lam" => RawExpr::Lam(binder(field(d, "binderInfo")?)?, sub("type")?, sub("body")?),
            "forallE" => RawExpr::Pi(binder(field(d, "binderInfo")?)?, sub("type")?, sub("body")?),
            "letE" => RawExpr::Let(sub("type")?, sub("value")?, sub("body")?),
            "proj" => RawExpr::Proj(
                self.name(nat(field(d, "typeName")?)?)?,
                small(field(d, "idx")?)?,
                sub("struct")?,
            ),
            "mdata" => {
                let node = self.expr_shared(nat(field(d, "expr")?)?, params, memo, remaining)?;
                memo.insert(i, node.clone());
                return Ok(node);
            }
            "natVal" => {
                let n = num_bigint::BigUint::parse_bytes(text(d)?.as_bytes(), 10)
                    .ok_or_else(|| malformed("natural literal"))?;
                RawExpr::Lit(crate::RawLit::Nat(crate::BigNat::from_biguint(n)))
            }
            "strVal" => RawExpr::Lit(crate::RawLit::Str(text(d)?.to_owned())),
            _ => return Err(Refusal::Unsupported(k.clone())),
        };
        let node = RawExpr::Shared(std::sync::Arc::new(node));
        memo.insert(i, node.clone());
        Ok(node)
    }
}
fn binder(v: &Value) -> Result<BinderInfo, Refusal> {
    match text(v)? {
        "default" => Ok(BinderInfo::Default),
        "implicit" => Ok(BinderInfo::Implicit),
        "strictImplicit" => Ok(BinderInfo::StrictImplicit),
        "instImplicit" => Ok(BinderInfo::InstImplicit),
        _ => Err(malformed("binderInfo")),
    }
}
fn measure(
    table: &HashMap<u64, (String, Value, u64, u64)>,
    children: &[u64],
    max_size: u64,
    max_depth: u64,
) -> Result<(u64, u64), Refusal> {
    let mut size = 1u64;
    let mut depth = 1u64;
    for i in children {
        let (_, _, s, d) = table.get(i).ok_or(Refusal::Dangling(*i))?;
        size = size.saturating_add(*s);
        depth = depth.max(d.saturating_add(1));
    }
    if size > max_size || depth > max_depth {
        return Err(Refusal::Limit);
    }
    Ok((size, depth))
}

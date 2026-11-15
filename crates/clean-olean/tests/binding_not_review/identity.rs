// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0
//! Portable statement pins. No Debug output or pointer enters the digest.
//!
//! H(domain, record) = SHA256 UTF8 canonical JSON {"domain":domain,"record":record}.
//! Canonical JSON sorts object keys lexically, retains array order, emits no
//! whitespace, and uses ordinary JSON strings/integers. Child references below
//! are content hashes, not DAG indices. Domains are binding-not-{name,level,
//! expr,statement}-v1. The statement record is {type,level_params:[name hashes]}.
//! Name rows: anon; str/num {parent,value}. Level rows: zero; param {name};
//! succ {child}; max/imax {left,right}. Expr rows: bvar {index}; sort {level};
//! const {name,levels}; app {fn,arg}; lam/pi {binder_info,type,body};
//! let {name,type,value,body,nondep}; nat {decimal}; str {value};
//! proj {name,index,expr}. Every row also contains its lowercase tag.
//! Lam/Pi binder names are erased because Clean does not store them. Binder
//! information, Let names/nondep, structured constant/universe names and raw
//! max/imax are retained. MData is semantically erased; the full Lean identity
//! and capture bytes are bound independently. No other extension is accepted.

use clean_kernel::expr::{BigNat, BinderInfo, Expr, ExprKind, Literal, Multiplicity};
use clean_kernel::name::{Name, NameInner};
use clean_kernel::Level;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, HashMap};

pub(super) fn canonical(value: &Value) -> String {
    match value {
        Value::Object(fields) => {
            let sorted: BTreeMap<_, _> = fields.iter().collect();
            format!(
                "{{{}}}",
                sorted
                    .into_iter()
                    .map(|(k, v)| {
                        format!(
                            "{}:{}",
                            serde_json::to_string(k).expect("JSON key"),
                            canonical(v)
                        )
                    })
                    .collect::<Vec<_>>()
                    .join(",")
            )
        }
        Value::Array(values) => format!(
            "[{}]",
            values.iter().map(canonical).collect::<Vec<_>>().join(",")
        ),
        other => serde_json::to_string(other).expect("JSON scalar"),
    }
}

pub(super) fn sha(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect::<String>()
}

fn hash(kind: &str, record: Value) -> String {
    sha(canonical(&json!({"domain":format!("binding-not-{kind}-v1"),"record":record})).as_bytes())
}

pub(super) fn name_json(name: &Name) -> Value {
    let mut parts = Vec::new();
    let mut cursor = name;
    loop {
        match cursor.inner() {
            NameInner::Anon => break,
            NameInner::Str(parent, value) => {
                parts.push(json!({"str":value.as_ref()}));
                cursor = parent;
            }
            NameInner::Num(parent, value) => {
                parts.push(json!({"num":value}));
                cursor = parent;
            }
        }
    }
    parts.reverse();
    json!(parts)
}

#[derive(Default)]
pub(super) struct Identity {
    names: HashMap<Name, String>,
    levels: HashMap<*const Level, String>,
    exprs: HashMap<*const ExprKind, String>,
}

impl Identity {
    fn name(&mut self, name: &Name) -> String {
        if let Some(hash) = self.names.get(name) {
            return hash.clone();
        }
        let record = match name.inner() {
            NameInner::Anon => json!({"tag":"anon"}),
            NameInner::Str(parent, value) => {
                json!({"tag":"str","parent":self.name(parent),"value":value.as_ref()})
            }
            NameInner::Num(parent, value) => {
                json!({"tag":"num","parent":self.name(parent),"value":value})
            }
        };
        let result = hash("name", record);
        self.names.insert(name.clone(), result.clone());
        result
    }

    fn level(&mut self, root: &Level) -> String {
        let mut stack = vec![(root, false)];
        while let Some((level, exit)) = stack.pop() {
            let key = std::ptr::from_ref(level);
            if self.levels.contains_key(&key) {
                continue;
            }
            if !exit {
                stack.push((level, true));
                match level {
                    Level::Succ(a) => stack.push((a, false)),
                    Level::Max(a, b) | Level::IMax(a, b) => {
                        stack.push((b, false));
                        stack.push((a, false));
                    }
                    _ => {}
                }
                continue;
            }
            let child = |l: &Level| self.levels[&std::ptr::from_ref(l)].clone();
            let record = match level {
                Level::Zero => json!({"tag":"zero"}),
                Level::Param(n) => json!({"tag":"param","name":self.name(n)}),
                Level::Succ(a) => json!({"tag":"succ","child":child(a)}),
                Level::Max(a, b) => json!({"tag":"max","left":child(a),"right":child(b)}),
                Level::IMax(a, b) => json!({"tag":"imax","left":child(a),"right":child(b)}),
            };
            self.levels.insert(key, hash("level", record));
        }
        self.levels[&std::ptr::from_ref(root)].clone()
    }

    fn expr(&mut self, root: &Expr) -> String {
        let mut stack = vec![(root, false)];
        while let Some((expr, exit)) = stack.pop() {
            let key = std::ptr::from_ref(expr.kind());
            if self.exprs.contains_key(&key) {
                continue;
            }
            if !exit {
                stack.push((expr, true));
                match expr.kind() {
                    ExprKind::App(a, b) | ExprKind::Lam(_, a, b) | ExprKind::Pi(_, a, b) => {
                        stack.push((b, false));
                        stack.push((a, false));
                    }
                    ExprKind::Let(_, t, v, b, _) => {
                        stack.push((b, false));
                        stack.push((v, false));
                        stack.push((t, false));
                    }
                    ExprKind::MData(_, a) | ExprKind::Proj(_, _, a) => stack.push((a, false)),
                    ExprKind::BVar(_)
                    | ExprKind::Sort(_)
                    | ExprKind::Const(..)
                    | ExprKind::Lit(_) => {}
                    other => panic!("non-Lean statement expression: {other:?}"),
                }
                continue;
            }
            if let ExprKind::MData(_, a) = expr.kind() {
                let hash = self.exprs[&std::ptr::from_ref(a.kind())].clone();
                self.exprs.insert(key, hash);
                continue;
            }
            let record = match expr.kind() {
                ExprKind::BVar(i) => json!({"tag":"bvar","index":i}),
                ExprKind::Sort(l) => json!({"tag":"sort","level":self.level(l)}),
                ExprKind::Const(n, ls) => {
                    json!({"tag":"const","name":self.name(n),"levels":ls.iter().map(|l|self.level(l)).collect::<Vec<_>>()})
                }
                ExprKind::App(f, a) => {
                    json!({"tag":"app","fn":expr_child(&self.exprs,f),"arg":expr_child(&self.exprs,a)})
                }
                ExprKind::Lam(b, t, v) | ExprKind::Pi(b, t, v) => {
                    assert_eq!(b.mult, Multiplicity::Many, "non-Lean multiplicity");
                    let info = match b.info {
                        BinderInfo::Default => "default",
                        BinderInfo::Implicit => "implicit",
                        BinderInfo::StrictImplicit => "strict_implicit",
                        BinderInfo::InstImplicit => "inst_implicit",
                    };
                    json!({"tag":if matches!(expr.kind(),ExprKind::Lam(..)){"lam"}else{"pi"},"binder_info":info,"type":expr_child(&self.exprs,t),"body":expr_child(&self.exprs,v)})
                }
                ExprKind::Let(n, t, v, b, nondep) => {
                    json!({"tag":"let","name":self.name(n),"type":expr_child(&self.exprs,t),"value":expr_child(&self.exprs,v),"body":expr_child(&self.exprs,b),"nondep":nondep})
                }
                ExprKind::Lit(Literal::Nat(n)) => json!({"tag":"nat","decimal":n.to_string()}),
                ExprKind::Lit(Literal::String(s)) => json!({"tag":"str","value":s.as_ref()}),
                ExprKind::Proj(n, i, e) => {
                    json!({"tag":"proj","name":self.name(n),"index":i,"expr":expr_child(&self.exprs,e)})
                }
                other => panic!("unsupported statement node: {other:?}"),
            };
            self.exprs.insert(key, hash("expr", record));
        }
        self.exprs[&std::ptr::from_ref(root.kind())].clone()
    }

    pub(super) fn statement(&mut self, expr: &Expr, params: &[Name]) -> String {
        hash(
            "statement",
            json!({"type":self.expr(expr),"level_params":params.iter().map(|n|self.name(n)).collect::<Vec<_>>()}),
        )
    }
}

fn expr_child(table: &HashMap<*const ExprKind, String>, expr: &Expr) -> String {
    table[&std::ptr::from_ref(expr.kind())].clone()
}

fn index(v: &Value) -> usize {
    usize::try_from(v.as_u64().expect("nonnegative DAG index")).expect("DAG index fits usize")
}
fn text<'a>(v: &'a Value, key: &str) -> &'a str {
    v[key].as_str().expect("string field")
}
fn fields(v: &Value, keys: &[&str]) {
    let actual: std::collections::BTreeSet<_> = v
        .as_object()
        .expect("DAG object")
        .keys()
        .map(String::as_str)
        .collect();
    assert_eq!(
        actual,
        keys.iter().copied().collect(),
        "exact DAG row fields"
    );
}

/// Decode Lean's independent full-statement DAG. References must point backward.
/// Direct Level variants deliberately retain max/imax as written (R150).
pub(super) fn decode(identity: &Value) -> (Expr, Vec<Name>) {
    use std::sync::Arc;
    fields(
        identity,
        &["root", "level_params", "names", "levels", "exprs"],
    );
    let mut names: Vec<Name> = Vec::new();
    for n in identity["names"].as_array().expect("names DAG") {
        let name = match text(n, "tag") {
            "anon" => {
                fields(n, &["tag"]);
                Name::anon()
            }
            "str" => {
                fields(n, &["tag", "parent", "value"]);
                names[index(&n["parent"])].clone().str(text(n, "value"))
            }
            "num" => {
                fields(n, &["tag", "parent", "value"]);
                names[index(&n["parent"])]
                    .clone()
                    .num(n["value"].as_u64().expect("numeric name"))
            }
            tag => panic!("unsupported name tag {tag}"),
        };
        names.push(name);
    }
    let mut levels: Vec<Level> = Vec::new();
    for l in identity["levels"].as_array().expect("levels DAG") {
        let level = match text(l, "tag") {
            "zero" => {
                fields(l, &["tag"]);
                Level::Zero
            }
            "param" => {
                fields(l, &["tag", "name"]);
                Level::Param(names[index(&l["name"])].clone())
            }
            "succ" => {
                fields(l, &["tag", "child"]);
                Level::Succ(levels[index(&l["child"])].clone().into())
            }
            "max" | "imax" => {
                fields(l, &["tag", "left", "right"]);
                let a = levels[index(&l["left"])].clone().into();
                let b = levels[index(&l["right"])].clone().into();
                if text(l, "tag") == "max" {
                    Level::Max(a, b)
                } else {
                    Level::IMax(a, b)
                }
            }
            tag => panic!("unsupported level tag {tag}"),
        };
        levels.push(level);
    }
    let mut exprs: Vec<Expr> = Vec::new();
    for e in identity["exprs"].as_array().expect("expressions DAG") {
        let child = |key: &str| Arc::new(exprs[index(&e[key])].clone());
        let kind = match text(e, "tag") {
            "bvar" => {
                fields(e, &["tag", "index"]);
                ExprKind::BVar(u32::try_from(index(&e["index"])).expect("bvar u32"))
            }
            "sort" => {
                fields(e, &["tag", "level"]);
                ExprKind::Sort(levels[index(&e["level"])].clone())
            }
            "const" => {
                fields(e, &["tag", "name", "levels"]);
                ExprKind::Const(
                    names[index(&e["name"])].clone(),
                    e["levels"]
                        .as_array()
                        .expect("constant universes")
                        .iter()
                        .map(|l| levels[index(l)].clone())
                        .collect(),
                )
            }
            "app" => {
                fields(e, &["tag", "fn", "arg"]);
                ExprKind::App(child("fn"), child("arg"))
            }
            "lam" | "pi" => {
                fields(e, &["tag", "name", "binder_info", "type", "body"]);
                let _binder_name = &names[index(&e["name"])];
                let info = match text(e, "binder_info") {
                    "default" => BinderInfo::Default,
                    "implicit" => BinderInfo::Implicit,
                    "strict_implicit" => BinderInfo::StrictImplicit,
                    "inst_implicit" => BinderInfo::InstImplicit,
                    other => panic!("bad binder {other}"),
                };
                if text(e, "tag") == "lam" {
                    ExprKind::Lam(info.into(), child("type"), child("body"))
                } else {
                    ExprKind::Pi(info.into(), child("type"), child("body"))
                }
            }
            "let" => {
                fields(e, &["tag", "name", "type", "value", "body", "nondep"]);
                ExprKind::Let(
                    names[index(&e["name"])].clone(),
                    child("type"),
                    child("value"),
                    child("body"),
                    e["nondep"].as_bool().expect("let nondep"),
                )
            }
            "nat" => {
                fields(e, &["tag", "decimal"]);
                ExprKind::Lit(Literal::Nat(
                    BigNat::from_radix_str(text(e, "decimal"), 10).expect("natural decimal"),
                ))
            }
            "str" => {
                fields(e, &["tag", "value"]);
                ExprKind::Lit(Literal::String(text(e, "value").into()))
            }
            "proj" => {
                fields(e, &["tag", "name", "index", "expr"]);
                ExprKind::Proj(
                    names[index(&e["name"])].clone(),
                    u32::try_from(index(&e["index"])).expect("projection index"),
                    child("expr"),
                )
            }
            tag => panic!("unsupported Lean identity expression {tag}"),
        };
        exprs.push(Expr::from_kind(kind));
    }
    let params = identity["level_params"]
        .as_array()
        .expect("universe params")
        .iter()
        .map(|n| names[index(n)].clone())
        .collect();
    (exprs[index(&identity["root"])].clone(), params)
}

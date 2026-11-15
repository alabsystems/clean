// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0

//! Untrusted, lossless DAG transport for the mixed-world pin review.

use clean_kernel::expr::{Expr, ExprKind};
use clean_kernel::level::Level;
use clean_kernel::name::{Name, NameInner};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, HashMap, HashSet};

#[path = "mixed_world_pin_capture_expr.rs"]
mod expr;

fn canonical(value: Value) -> Value {
    match value {
        Value::Object(fields) => {
            let fields: BTreeMap<_, _> =
                fields.into_iter().map(|(k, v)| (k, canonical(v))).collect();
            serde_json::to_value(fields).expect("canonical JSON object")
        }
        Value::Array(values) => Value::Array(values.into_iter().map(canonical).collect()),
        other => other,
    }
}

fn append(rows: &mut Vec<Value>, mut raw: Value, content: Value, domain: &str) -> usize {
    let bytes = serde_json::to_vec(&canonical(json!({"domain": domain, "record": content})))
        .expect("encode content hash input");
    let hash = Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect::<String>();
    raw.as_object_mut()
        .expect("DAG row object")
        .insert("sha256".into(), json!(hash));
    let id = rows.len();
    rows.push(raw);
    id
}

#[derive(Default)]
pub(super) struct Tables {
    names: Vec<Value>,
    levels: Vec<Value>,
    exprs: Vec<Value>,
    name_ids: HashMap<Name, usize>,
    level_ids: HashMap<*const Level, usize>,
    expr_ids: HashMap<*const ExprKind, usize>,
}

impl Tables {
    pub(super) fn name(&mut self, name: &Name) -> usize {
        if let Some(id) = self.name_ids.get(name) {
            return *id;
        }
        let mut pending = Vec::new();
        let mut cursor = name;
        while !self.name_ids.contains_key(cursor) {
            pending.push(cursor);
            match cursor.inner() {
                NameInner::Anon => break,
                NameInner::Str(parent, _) | NameInner::Num(parent, _) => cursor = parent,
            }
        }
        for name in pending.into_iter().rev() {
            let (raw, content) = match name.inner() {
                NameInner::Anon => (json!({"tag":"anon"}), json!({"tag":"anon"})),
                NameInner::Str(parent, value) => {
                    let id = self.name_ids[parent.as_ref()];
                    (
                        json!({"tag":"str","parent":id,"value":value}),
                        json!({"tag":"str","parent":self.names[id]["sha256"],"value":value}),
                    )
                }
                NameInner::Num(parent, value) => {
                    let id = self.name_ids[parent.as_ref()];
                    (
                        json!({"tag":"num","parent":id,"value":value}),
                        json!({"tag":"num","parent":self.names[id]["sha256"],"value":value}),
                    )
                }
            };
            let id = append(&mut self.names, raw, content, "mixed-pin-name-v1");
            assert!(self.name_ids.insert(name.clone(), id).is_none());
        }
        self.name_ids[name]
    }

    pub(super) fn names(&mut self, names: &[Name]) -> Vec<usize> {
        names.iter().map(|name| self.name(name)).collect()
    }

    pub(super) fn level(&mut self, root: &Level) -> usize {
        let mut pending = vec![(root, false)];
        let mut visiting = HashSet::new();
        while let Some((level, exit)) = pending.pop() {
            let pointer = std::ptr::from_ref(level);
            if self.level_ids.contains_key(&pointer) {
                continue;
            }
            if !exit {
                assert!(visiting.insert(pointer), "cyclic universe level");
                pending.push((level, true));
                match level {
                    Level::Succ(child) => pending.push((child.as_ref(), false)),
                    Level::Max(a, b) | Level::IMax(a, b) => {
                        pending.push((b.as_ref(), false));
                        pending.push((a.as_ref(), false));
                    }
                    Level::Zero | Level::Param(_) => {}
                }
                continue;
            }
            let (raw, content) = match level {
                Level::Zero => (json!({"tag":"zero"}), json!({"tag":"zero"})),
                Level::Param(name) => {
                    let id = self.name(name);
                    (
                        json!({"tag":"param","name":id}),
                        json!({"tag":"param","name":self.names[id]["sha256"]}),
                    )
                }
                Level::Succ(child) => {
                    let id = self.level_ids[&std::ptr::from_ref(child.as_ref())];
                    (
                        json!({"tag":"succ","child":id}),
                        json!({"tag":"succ","child":self.levels[id]["sha256"]}),
                    )
                }
                Level::Max(a, b) | Level::IMax(a, b) => {
                    let tag = if matches!(level, Level::Max(..)) {
                        "max"
                    } else {
                        "imax"
                    };
                    let a = self.level_ids[&std::ptr::from_ref(a.as_ref())];
                    let b = self.level_ids[&std::ptr::from_ref(b.as_ref())];
                    (
                        json!({"tag":tag,"left":a,"right":b}),
                        json!({"tag":tag,"left":self.levels[a]["sha256"],"right":self.levels[b]["sha256"]}),
                    )
                }
            };
            let id = append(&mut self.levels, raw, content, "mixed-pin-level-v1");
            assert!(self.level_ids.insert(pointer, id).is_none());
            assert!(visiting.remove(&pointer));
        }
        self.level_ids[&std::ptr::from_ref(root)]
    }

    pub(super) fn expr(&mut self, root: &Expr) -> usize {
        let mut pending = vec![(root, false)];
        let mut visiting = HashSet::new();
        while let Some((expr, exit)) = pending.pop() {
            let pointer = std::ptr::from_ref(expr.kind());
            if self.expr_ids.contains_key(&pointer) {
                continue;
            }
            if !exit {
                assert!(visiting.insert(pointer), "cyclic expression");
                pending.push((expr, true));
                // Reject unsupported kinds before following any extension's children.
                match expr.kind() {
                    ExprKind::BVar(_)
                    | ExprKind::Sort(_)
                    | ExprKind::Const(..)
                    | ExprKind::Lit(_) => {}
                    ExprKind::App(..)
                    | ExprKind::Lam(..)
                    | ExprKind::Pi(..)
                    | ExprKind::Let(..)
                    | ExprKind::Proj(..)
                    | ExprKind::MData(..) => {
                        for child in super::super::children(expr).into_iter().rev() {
                            pending.push((child, false));
                        }
                    }
                    other => panic!(
                        "capture refuses non-Lean expression {:?}",
                        std::mem::discriminant(other)
                    ),
                }
                continue;
            }
            let (raw, content) = self.expr_row(expr);
            let id = append(&mut self.exprs, raw, content, "mixed-pin-expr-v1");
            assert!(self.expr_ids.insert(pointer, id).is_none());
            assert!(visiting.remove(&pointer));
        }
        self.expr_ids[&std::ptr::from_ref(root.kind())]
    }

    pub(super) fn finish(self) -> Value {
        json!({"names":self.names,"levels":self.levels,"exprs":self.exprs})
    }
}

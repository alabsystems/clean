// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0

//! Exact expression rows, with stable hashes independent of DAG indexes.

use super::Tables;
use clean_kernel::expr::{
    BigNat, BinderData, BinderInfo, Expr, ExprKind, Literal, MDataValue, Multiplicity,
};
use clean_kernel::name::Name;
use serde_json::{json, Value};

impl Tables {
    fn binder(binder: BinderData) -> Value {
        assert_eq!(
            binder.mult,
            Multiplicity::Many,
            "non-Lean binder multiplicity"
        );
        let info = match binder.info {
            BinderInfo::Default => "default",
            BinderInfo::Implicit => "implicit",
            BinderInfo::StrictImplicit => "strict_implicit",
            BinderInfo::InstImplicit => "inst_implicit",
        };
        json!({"info":info,"mult":"many"})
    }

    fn metadata(&mut self, entries: &[(Name, MDataValue)]) -> (Value, Value) {
        let mut raw = Vec::new();
        let mut content = Vec::new();
        for (name, value) in entries {
            let name = self.name(name);
            let (r, c) = match value {
                MDataValue::Bool(v) => (
                    json!({"tag":"bool","value":v}),
                    json!({"tag":"bool","value":v}),
                ),
                MDataValue::Nat(v) => (
                    json!({"tag":"nat","value":v}),
                    json!({"tag":"nat","value":v}),
                ),
                MDataValue::String(v) => (
                    json!({"tag":"str","value":v.as_ref()}),
                    json!({"tag":"str","value":v.as_ref()}),
                ),
                MDataValue::Name(v) => {
                    let id = self.name(v);
                    (
                        json!({"tag":"name","value":id}),
                        json!({"tag":"name","value":self.names[id]["sha256"]}),
                    )
                }
            };
            raw.push(json!({"name":name,"value":r}));
            content.push(json!({"name":self.names[name]["sha256"],"value":c}));
        }
        (json!(raw), json!(content))
    }

    pub(super) fn expr_row(&mut self, e: &Expr) -> (Value, Value) {
        let child = |x: &Expr| self.expr_ids[&std::ptr::from_ref(x.kind())];
        match e.kind() {
            ExprKind::BVar(index) => (
                json!({"tag":"bvar","index":index}),
                json!({"tag":"bvar","index":index}),
            ),
            ExprKind::Sort(level) => {
                let id = self.level(level);
                (
                    json!({"tag":"sort","level":id}),
                    json!({"tag":"sort","level":self.levels[id]["sha256"]}),
                )
            }
            ExprKind::Const(name, levels) => {
                let name = self.name(name);
                let ids: Vec<_> = levels.iter().map(|level| self.level(level)).collect();
                let hashes: Vec<_> = ids
                    .iter()
                    .map(|id| self.levels[*id]["sha256"].clone())
                    .collect();
                (
                    json!({"tag":"const","name":name,"levels":ids}),
                    json!({"tag":"const","name":self.names[name]["sha256"],"levels":hashes}),
                )
            }
            ExprKind::App(f, a) => {
                let f = child(f);
                let a = child(a);
                (
                    json!({"tag":"app","fn":f,"arg":a}),
                    json!({"tag":"app","fn":self.exprs[f]["sha256"],"arg":self.exprs[a]["sha256"]}),
                )
            }
            ExprKind::Lam(binder, ty, body) | ExprKind::Pi(binder, ty, body) => {
                let tag = if matches!(e.kind(), ExprKind::Lam(..)) {
                    "lam"
                } else {
                    "pi"
                };
                let ty = child(ty);
                let body = child(body);
                let binder = Self::binder(*binder);
                (
                    json!({"tag":tag,"binder":binder,"type":ty,"body":body}),
                    json!({"tag":tag,"binder":binder,"type":self.exprs[ty]["sha256"],"body":self.exprs[body]["sha256"]}),
                )
            }
            ExprKind::Let(name, ty, value, body, nondep) => {
                let ty = child(ty);
                let value = child(value);
                let body = child(body);
                let name = self.name(name);
                (
                    json!({"tag":"let","name":name,"type":ty,"value":value,"body":body,"nondep":nondep}),
                    json!({"tag":"let","name":self.names[name]["sha256"],"type":self.exprs[ty]["sha256"],"value":self.exprs[value]["sha256"],"body":self.exprs[body]["sha256"],"nondep":nondep}),
                )
            }
            ExprKind::Lit(Literal::Nat(value)) => {
                let decimal = match value {
                    BigNat::Small(n) => n.to_string(),
                    BigNat::Big(limbs) => {
                        let bytes: Vec<_> = limbs.iter().flat_map(|n| n.to_le_bytes()).collect();
                        num_bigint::BigUint::from_bytes_le(&bytes).to_string()
                    }
                };
                let row = json!({"tag":"nat","decimal":decimal,"raw":value});
                (row.clone(), row)
            }
            ExprKind::Lit(Literal::String(value)) => {
                let row = json!({"tag":"str","value":value.as_ref()});
                (row.clone(), row)
            }
            ExprKind::Proj(name, index, expr) => {
                let expr = child(expr);
                let name = self.name(name);
                (
                    json!({"tag":"proj","name":name,"index":index,"expr":expr}),
                    json!({"tag":"proj","name":self.names[name]["sha256"],"index":index,"expr":self.exprs[expr]["sha256"]}),
                )
            }
            ExprKind::MData(metadata, expr) => {
                let expr = child(expr);
                let (raw, content) = self.metadata(metadata);
                (
                    json!({"tag":"mdata","metadata":raw,"expr":expr}),
                    json!({"tag":"mdata","metadata":content,"expr":self.exprs[expr]["sha256"]}),
                )
            }
            other => panic!(
                "capture refuses non-Lean expression {:?}",
                std::mem::discriminant(other)
            ),
        }
    }
}

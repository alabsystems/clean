// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Expression records and hash-consing keys for the export tables.

use super::*;

impl Tables {
    /// An expression record (`{"ie": i, <kind>: ...}`).
    pub(crate) fn bind_expr(
        &mut self,
        line: u64,
        index: u64,
        kind: &str,
        data: JsonValue,
    ) -> Result<(), NdjsonError> {
        let (expr, key, rewritten, problem) = self.build_expr(line, kind, data)?;
        if self.exprs.contains_key(&index) {
            return Err(NdjsonError::ExprIndexRebound { line, index });
        }
        if let Some(level) = problem {
            self.problem_exprs.insert(index, level);
        }
        let node = self.intern(expr, key);
        self.exprs.insert(index, node);
        if rewritten {
            self.rewritten_exprs.insert(index);
        }
        Ok(())
    }

    /// A child expression: its interned node, whether it mentions a
    /// rewritten level, and a level Lean could tell from the built one that it
    /// mentions.
    fn child(&self, line: u64, index: u64) -> Result<(Arc<Expr>, bool, Option<u64>), NdjsonError> {
        Ok((
            self.expr(line, index)?,
            self.rewritten_exprs.contains(&index),
            self.problem_exprs.get(&index).copied(),
        ))
    }

    /// The expression a record states, its hash-consing key, whether it
    /// mentions a rewritten level, and a level Lean could tell from the built
    /// one that it mentions.
    fn build_expr(&self, line: u64, kind: &str, data: JsonValue) -> Result<Built, NdjsonError> {
        Ok(match kind {
            "bvar" => {
                let raw = nat_value(line, "Expr.bvar", "bvar", &data)?;
                let index = u32::try_from(raw)
                    .ok()
                    .filter(|&i| i <= Expr::MAX_BVAR_INDEX)
                    .ok_or_else(|| NdjsonError::RepresentationLimit {
                        line,
                        record: "Expr.bvar",
                        field: "bvar".to_owned(),
                        problem: format!(
                            "de Bruijn index {raw} is above the kernel's bound {}",
                            Expr::MAX_BVAR_INDEX
                        ),
                    })?;
                (Expr::bvar(index), Some(NodeKey::BVar(index)), false, None)
            }
            "sort" => {
                let at = nat_value(line, "Expr.sort", "sort", &data)?;
                let level = self.level(line, at)?;
                let rewritten = self.rewritten_levels.contains(&at);
                (
                    Expr::sort(level.clone()),
                    Some(NodeKey::Sort(level)),
                    rewritten,
                    self.problem_levels.get(&at).copied(),
                )
            }
            "const" => {
                let mut f = Fields::new(line, "Expr.const", data)?;
                let name = self.name(line, f.nat("name")?)?;
                let us = f.nat_array("us")?;
                f.finish()?;
                // One line may list a capped level many times: the levels
                // together are bounded as one level is.
                let mut nodes: u64 = 0;
                for &u in &us {
                    nodes = nodes.saturating_add(self.level_size(line, u)?);
                }
                self.check_level_size(line, nodes)?;
                let levels: Vec<Level> = us
                    .iter()
                    .map(|&u| self.level(line, u))
                    .collect::<Result<_, _>>()?;
                let rewritten = us.iter().any(|u| self.rewritten_levels.contains(u));
                let problem = us.iter().find_map(|u| self.problem_levels.get(u).copied());
                (
                    Expr::const_(name.clone(), levels.clone()),
                    Some(NodeKey::Const(name, levels)),
                    rewritten,
                    problem,
                )
            }
            "app" => {
                let mut f = Fields::new(line, "Expr.app", data)?;
                let (func, r1, p1) = self.child(line, f.nat("fn")?)?;
                let (arg, r2, p2) = self.child(line, f.nat("arg")?)?;
                f.finish()?;
                let key = NodeKey::App(addr(&func), addr(&arg));
                (Expr::app_arc(func, arg), Some(key), r1 || r2, p1.or(p2))
            }
            "lam" | "forallE" => {
                let record = if kind == "lam" {
                    "Expr.lam"
                } else {
                    "Expr.forallE"
                };
                let mut f = Fields::new(line, record, data)?;
                // Clean's binders carry no name; the index must still resolve,
                // as Lean's reader resolves it.
                self.name(line, f.nat("name")?)?;
                let (ty, r1, p1) = self.child(line, f.nat("type")?)?;
                let (body, r2, p2) = self.child(line, f.nat("body")?)?;
                let info = match f.string("binderInfo")?.as_str() {
                    "default" => BinderInfo::Default,
                    "implicit" => BinderInfo::Implicit,
                    "strictImplicit" => BinderInfo::StrictImplicit,
                    "instImplicit" => BinderInfo::InstImplicit,
                    other => {
                        return Err(f.error("binderInfo", format!("invalid binder info {other:?}")))
                    }
                };
                f.finish()?;
                if kind == "lam" {
                    let key = NodeKey::Lam(info, addr(&ty), addr(&body));
                    (
                        Expr::lam_arc(info, ty, body),
                        Some(key),
                        r1 || r2,
                        p1.or(p2),
                    )
                } else {
                    let key = NodeKey::Pi(info, addr(&ty), addr(&body));
                    (Expr::pi_arc(info, ty, body), Some(key), r1 || r2, p1.or(p2))
                }
            }
            "letE" => {
                let mut f = Fields::new(line, "Expr.letE", data)?;
                let name = self.name(line, f.nat("name")?)?;
                let (ty, r1, p1) = self.child(line, f.nat("type")?)?;
                let (value, r2, p2) = self.child(line, f.nat("value")?)?;
                let (body, r3, p3) = self.child(line, f.nat("body")?)?;
                let nondep = f.boolean("nondep")?;
                f.finish()?;
                let key = NodeKey::Let(name.clone(), addr(&ty), addr(&value), addr(&body), nondep);
                (
                    Expr::let_named_arc(name, ty, value, body, nondep),
                    Some(key),
                    r1 || r2 || r3,
                    p1.or(p2).or(p3),
                )
            }
            "proj" => {
                let mut f = Fields::new(line, "Expr.proj", data)?;
                let type_name = self.name(line, f.nat("typeName")?)?;
                let idx = f.nat_u32("idx")?;
                let (structure, rewritten, problem) = self.child(line, f.nat("struct")?)?;
                f.finish()?;
                let key = NodeKey::Proj(type_name.clone(), idx, addr(&structure));
                (
                    Expr::proj_arc(type_name, idx, structure),
                    Some(key),
                    rewritten,
                    problem,
                )
            }
            "natVal" => {
                let text = match data {
                    JsonValue::String(text) => text,
                    other => {
                        return Err(NdjsonError::Field {
                            line,
                            record: "Expr.lit",
                            field: "natVal".to_owned(),
                            problem: format!("expected a string, found {}", other.type_name()),
                        })
                    }
                };
                match parse_nat_literal(&text) {
                    Ok(n) => literal(Expr::bignat_lit(n)),
                    Err(NatTextError::Malformed) => {
                        return Err(NdjsonError::Field {
                            line,
                            record: "Expr.lit",
                            field: "natVal".to_owned(),
                            problem: "not a string of decimal digits".to_owned(),
                        })
                    }
                    Err(NatTextError::OverBudget { digits }) => {
                        return Err(NdjsonError::NatLiteralBudget {
                            line,
                            digits,
                            limit: MAX_NAT_LITERAL_DIGITS,
                        })
                    }
                }
            }
            "strVal" => match data {
                JsonValue::String(s) => literal(Expr::str_lit(s)),
                other => {
                    return Err(NdjsonError::Field {
                        line,
                        record: "Expr.lit",
                        field: "strVal".to_owned(),
                        problem: format!("expected a string, found {}", other.type_name()),
                    })
                }
            },
            // "mdata": Lean's reader keeps the expression and drops the
            // payload (`.mdata {} expr`): the format does not say how to read
            // a `KVMap` back. Kernels ignore metadata either way.
            "mdata" => {
                let mut f = Fields::new(line, "Expr.mdata", data)?;
                let (inner, rewritten, problem) = self.child(line, f.nat("expr")?)?;
                match f.take("data")? {
                    JsonValue::Object(_) => {}
                    other => {
                        return Err(f.error(
                            "data",
                            format!("expected an object, found {}", other.type_name()),
                        ))
                    }
                }
                f.finish()?;
                let key = NodeKey::MData(addr(&inner));
                (
                    Expr::from_kind(ExprKind::MData(Vec::new(), inner)),
                    Some(key),
                    rewritten,
                    problem,
                )
            }
            other => return Err(unknown(line, "ie", other)),
        })
    }
}

/// A literal expression: not hash-consed (a literal is a leaf, and keying a
/// 50-million-digit one would copy it).
fn literal(expr: Expr) -> Built {
    (expr, None, false, None)
}

/// An index record whose kind is none the format defines for that table.
pub(super) fn unknown(line: u64, index_key: &str, kind: &str) -> NdjsonError {
    NdjsonError::UnknownRecord {
        line,
        keys: vec![index_key.to_owned(), kind.to_owned()],
    }
}

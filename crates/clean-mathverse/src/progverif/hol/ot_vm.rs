// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! OpenTheory virtual machine internals.
//!
//! The VM is a simple stack machine with a dictionary. Commands build up
//! types, terms, and theorems. Inference rules are simplified: we trust the
//! source HOL kernel already verified the proofs and only track theorem
//! structure for import.

use super::opentheory::ArticleResult;
use super::types::{HolAxiom, HolTerm, HolThm, HolType};
use super::HolError;

// ---------------------------------------------------------------------------
// VM object
// ---------------------------------------------------------------------------

/// An object on the OpenTheory VM stack.
#[derive(Clone, Debug)]
pub(crate) enum OtObject {
    Num(i64),
    Name(Vec<String>),
    Type(HolType),
    Term(HolTerm),
    Thm(HolThm),
    List(Vec<OtObject>),
}

impl OtObject {
    pub(crate) fn as_num(&self) -> Result<i64, HolError> {
        match self {
            Self::Num(n) => Ok(*n),
            _ => Err(ot_err(format!("expected Num, got {}", self.tag()))),
        }
    }

    pub(crate) fn into_name(self) -> Result<Vec<String>, HolError> {
        match self {
            Self::Name(parts) => Ok(parts),
            _ => Err(ot_err(format!("expected Name, got {}", self.tag()))),
        }
    }

    pub(crate) fn into_type(self) -> Result<HolType, HolError> {
        match self {
            Self::Type(ty) => Ok(ty),
            _ => Err(ot_err(format!("expected Type, got {}", self.tag()))),
        }
    }

    pub(crate) fn into_term(self) -> Result<HolTerm, HolError> {
        match self {
            Self::Term(tm) => Ok(tm),
            _ => Err(ot_err(format!("expected Term, got {}", self.tag()))),
        }
    }

    pub(crate) fn into_thm(self) -> Result<HolThm, HolError> {
        match self {
            Self::Thm(thm) => Ok(thm),
            _ => Err(ot_err(format!("expected Thm, got {}", self.tag()))),
        }
    }

    pub(crate) fn into_list(self) -> Result<Vec<OtObject>, HolError> {
        match self {
            Self::List(v) => Ok(v),
            _ => Err(ot_err(format!("expected List, got {}", self.tag()))),
        }
    }

    fn tag(&self) -> &'static str {
        match self {
            Self::Num(_) => "Num",
            Self::Name(_) => "Name",
            Self::Type(_) => "Type",
            Self::Term(_) => "Term",
            Self::Thm(_) => "Thm",
            Self::List(_) => "List",
        }
    }
}

fn ot_err(message: String) -> HolError {
    HolError::OpenTheoryError { message }
}

// ---------------------------------------------------------------------------
// VM
// ---------------------------------------------------------------------------

/// OpenTheory virtual machine.
pub(crate) struct OtVm {
    stack: Vec<OtObject>,
    dict: std::collections::HashMap<i64, OtObject>,
    pub(crate) result: ArticleResult,
}

impl OtVm {
    pub(crate) fn new() -> Self {
        Self {
            stack: Vec::new(),
            dict: std::collections::HashMap::new(),
            result: ArticleResult::default(),
        }
    }

    pub(crate) fn push(&mut self, obj: OtObject) {
        self.stack.push(obj);
    }

    pub(crate) fn pop(&mut self) -> Result<OtObject, HolError> {
        self.stack
            .pop()
            .ok_or_else(|| ot_err("stack underflow".to_owned()))
    }

    /// Execute a single command.
    pub(crate) fn exec(&mut self, cmd: &str) -> Result<(), HolError> {
        match cmd {
            "pop" | "nil" | "cons" | "def" | "ref" => self.exec_stack(cmd),
            "varType" | "opType" | "varTerm" | "constTerm" | "appTerm" | "absTerm" => {
                self.exec_build(cmd)
            }
            "refl" | "assume" | "eqMp" | "deductAntisym" | "betaConv" => self.exec_infer(cmd),
            "axiom" | "defineConst" | "thm" => self.exec_decl(cmd),
            other => self.exec_literal(other),
        }
    }

    /// Stack manipulation and dictionary commands.
    fn exec_stack(&mut self, cmd: &str) -> Result<(), HolError> {
        match cmd {
            "pop" => {
                self.pop()?;
            }
            "nil" => self.push(OtObject::List(Vec::new())),
            "cons" => {
                let head = self.pop()?;
                let tail = self.pop()?.into_list()?;
                let mut list = vec![head];
                list.extend(tail);
                self.push(OtObject::List(list));
            }
            "def" => {
                let key = self.pop()?.as_num()?;
                let val = self
                    .stack
                    .last()
                    .ok_or_else(|| ot_err("def: stack empty after key pop".to_owned()))?;
                self.dict.insert(key, val.clone());
            }
            "ref" => {
                let key = self.pop()?.as_num()?;
                let val = self
                    .dict
                    .get(&key)
                    .ok_or_else(|| ot_err(format!("ref: key {key} not in dictionary")))?;
                self.push(val.clone());
            }
            _ => return Err(ot_err(format!("unknown stack cmd: {cmd}"))),
        }
        Ok(())
    }

    /// Type and term construction commands.
    fn exec_build(&mut self, cmd: &str) -> Result<(), HolError> {
        match cmd {
            "varType" => {
                let name = self.pop()?.into_name()?.join(".");
                self.push(OtObject::Type(HolType::TyVar(name)));
            }
            "opType" => {
                let args_obj = self.pop()?.into_list()?;
                let name = self.pop()?.into_name()?.join(".");
                let mut args = Vec::with_capacity(args_obj.len());
                for a in args_obj {
                    args.push(a.into_type()?);
                }
                self.push(OtObject::Type(HolType::TyOp(name, args)));
            }
            "varTerm" => {
                let ty = self.pop()?.into_type()?;
                let name = self.pop()?.into_name()?.join(".");
                self.push(OtObject::Term(HolTerm::Var(name, ty)));
            }
            "constTerm" => {
                let ty = self.pop()?.into_type()?;
                let name = self.pop()?.into_name()?.join(".");
                self.push(OtObject::Term(HolTerm::Const(name, ty)));
            }
            "appTerm" => {
                let arg = self.pop()?.into_term()?;
                let f = self.pop()?.into_term()?;
                self.push(OtObject::Term(HolTerm::App(Box::new(f), Box::new(arg))));
            }
            "absTerm" => {
                let body = self.pop()?.into_term()?;
                let var = self.pop()?.into_term()?;
                match var {
                    HolTerm::Var(name, ty) => {
                        self.push(OtObject::Term(HolTerm::Abs(name, ty, Box::new(body))));
                    }
                    _ => return Err(ot_err("absTerm: binder is not a Var".to_owned())),
                }
            }
            _ => return Err(ot_err(format!("unknown build cmd: {cmd}"))),
        }
        Ok(())
    }

    /// Inference rule commands (simplified — trust source HOL kernel).
    fn exec_infer(&mut self, cmd: &str) -> Result<(), HolError> {
        match cmd {
            "refl" => {
                let tm = self.pop()?.into_term()?;
                let concl = mk_eq_app(&tm);
                self.push(OtObject::Thm(HolThm {
                    hyps: Vec::new(),
                    concl,
                }));
            }
            "assume" => {
                let tm = self.pop()?.into_term()?;
                self.push(OtObject::Thm(HolThm {
                    hyps: vec![tm.clone()],
                    concl: tm,
                }));
            }
            "eqMp" => {
                let thm1 = self.pop()?.into_thm()?;
                let thm2 = self.pop()?.into_thm()?;
                let mut hyps = thm1.hyps;
                hyps.extend(thm2.hyps);
                dedup_hyps(&mut hyps);
                self.push(OtObject::Thm(HolThm {
                    hyps,
                    concl: thm2.concl,
                }));
            }
            "deductAntisym" => {
                let thm1 = self.pop()?.into_thm()?;
                let thm2 = self.pop()?.into_thm()?;
                let concl = mk_eq_terms(&thm2.concl, &thm1.concl);
                let mut hyps: Vec<HolTerm> = thm2
                    .hyps
                    .into_iter()
                    .filter(|h| h != &thm1.concl)
                    .chain(thm1.hyps.into_iter().filter(|h| h != &thm2.concl))
                    .collect();
                dedup_hyps(&mut hyps);
                self.push(OtObject::Thm(HolThm { hyps, concl }));
            }
            "betaConv" => {
                let tm = self.pop()?.into_term()?;
                let concl = mk_eq_app(&tm);
                self.push(OtObject::Thm(HolThm {
                    hyps: Vec::new(),
                    concl,
                }));
            }
            _ => return Err(ot_err(format!("unknown infer cmd: {cmd}"))),
        }
        Ok(())
    }

    /// Declaration and export commands (axiom, defineConst, thm).
    fn exec_decl(&mut self, cmd: &str) -> Result<(), HolError> {
        match cmd {
            "axiom" => {
                let concl = self.pop()?.into_term()?;
                let hyps_obj = self.pop()?.into_list()?;
                let mut hyps = Vec::with_capacity(hyps_obj.len());
                for h in hyps_obj {
                    hyps.push(h.into_term()?);
                }
                classify_axiom(&concl, &mut self.result.axioms_assumed);
                self.push(OtObject::Thm(HolThm { hyps, concl }));
            }
            "defineConst" => {
                let tm = self.pop()?.into_term()?;
                let name = self.pop()?.into_name()?.join(".");
                self.result.constants.push(name.clone());
                let ty = tm.ty().unwrap_or(HolType::bool());
                let c = HolTerm::Const(name, ty.clone());
                let concl = mk_eq_terms(&c, &tm);
                self.push(OtObject::Term(c));
                self.push(OtObject::Thm(HolThm {
                    hyps: Vec::new(),
                    concl,
                }));
            }
            "thm" => {
                let _concl = self.pop()?.into_term()?;
                let _hyps_obj = self.pop()?.into_list()?;
                let thm = self.pop()?.into_thm()?;
                self.result.theorems.push(thm);
            }
            _ => return Err(ot_err(format!("unknown decl cmd: {cmd}"))),
        }
        Ok(())
    }

    /// Parse a literal (quoted name or integer).
    fn exec_literal(&mut self, token: &str) -> Result<(), HolError> {
        if token.starts_with('"') && token.ends_with('"') {
            let inner = &token[1..token.len() - 1];
            let parts: Vec<String> = inner.split('.').map(|s| s.to_owned()).collect();
            self.push(OtObject::Name(parts));
        } else if let Ok(n) = token.parse::<i64>() {
            self.push(OtObject::Num(n));
        } else {
            return Err(ot_err(format!("unknown command: {token}")));
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Build `(= t t)` application for refl/betaConv.
fn mk_eq_app(tm: &HolTerm) -> HolTerm {
    let ty = tm.ty().unwrap_or(HolType::bool());
    let eq_ty = HolType::fun(ty.clone(), HolType::fun(ty, HolType::bool()));
    let eq_const = HolTerm::Const("=".to_owned(), eq_ty);
    HolTerm::App(
        Box::new(HolTerm::App(Box::new(eq_const), Box::new(tm.clone()))),
        Box::new(tm.clone()),
    )
}

/// Build `(= lhs rhs)` application.
fn mk_eq_terms(lhs: &HolTerm, rhs: &HolTerm) -> HolTerm {
    let eq_ty = HolType::fun(
        HolType::bool(),
        HolType::fun(HolType::bool(), HolType::bool()),
    );
    let eq_const = HolTerm::Const("=".to_owned(), eq_ty);
    HolTerm::App(
        Box::new(HolTerm::App(Box::new(eq_const), Box::new(lhs.clone()))),
        Box::new(rhs.clone()),
    )
}

/// Dedup hypothesis list (by Debug representation).
fn dedup_hyps(hyps: &mut Vec<HolTerm>) {
    hyps.sort_by(|a, b| format!("{a:?}").cmp(&format!("{b:?}")));
    hyps.dedup_by(|a, b| format!("{a:?}") == format!("{b:?}"));
}

/// Classify well-known HOL axioms from the conclusion term.
fn classify_axiom(concl: &HolTerm, axioms: &mut Vec<HolAxiom>) {
    let dbg = format!("{concl:?}");
    if dbg.contains("Extensionality") || dbg.contains("ETA_AX") {
        axioms.push(HolAxiom::Extensionality);
    } else if dbg.contains("SELECT_AX") || dbg.contains("@") {
        axioms.push(HolAxiom::Choice);
    } else if dbg.contains("INFINITY") || dbg.contains("ind") {
        axioms.push(HolAxiom::Infinity);
    }
}

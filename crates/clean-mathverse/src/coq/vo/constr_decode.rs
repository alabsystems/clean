// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Decoder from the marshal object DAG to [`Constr`] and its embedded name
//! and universe types.
//!
//! Layout reference: `checker/values.ml` (Coq 8.20), validated against real
//! `Init/*.vo` files. Shared subgraphs are memoized by arena index, so DAG
//! sharing does not blow up into exponential tree duplication.

use std::collections::HashMap;

use thiserror::Error;

use super::constr::{
    Binder, CaseBranch, CaseData, CaseInfo, CaseReturn, CastKind, Constr, CtorRef, DirPath, IndRef,
    Instance, KerName, KerPair, Level, ModPath, ProjData, QVar, Quality, RawLevel, RecDecl,
    Relevance, Sort, UGlobal,
};
use super::marshal_parser::{MValue, MarshalDag};

/// Maximum decoding recursion depth. Terms deeper than this are rejected
/// with a clean error instead of overflowing the stack.
const MAX_DEPTH: usize = 16 * 1024;

/// Errors from decoding kernel values out of the marshal DAG.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum ConstrError {
    #[error("shape mismatch decoding {context}: {detail}")]
    Shape { context: String, detail: String },

    #[error("term nesting exceeds depth limit {limit}")]
    Depth { limit: usize },

    #[error("unsupported term constructor {name} (never occurs in checked .vo terms)")]
    Unsupported { name: &'static str },
}

pub type ConstrResult<T> = Result<T, ConstrError>;

fn shape(context: &str, detail: impl Into<String>) -> ConstrError {
    ConstrError::Shape {
        context: context.to_string(),
        detail: detail.into(),
    }
}

/// Decoding context: DAG plus a memo table for shared subterms.
pub struct ConstrDecoder<'a> {
    dag: &'a MarshalDag,
    memo: HashMap<usize, Constr>,
}

impl<'a> ConstrDecoder<'a> {
    #[must_use]
    pub fn new(dag: &'a MarshalDag) -> Self {
        Self {
            dag,
            memo: HashMap::new(),
        }
    }

    // -- primitive views ---------------------------------------------------

    fn block(&self, v: MValue, ctx: &str) -> ConstrResult<(u8, &'a [MValue])> {
        self.dag
            .block(v)
            .ok_or_else(|| shape(ctx, format!("expected block, got {v:?}")))
    }

    fn tagged(&self, v: MValue, tag: u8, n: usize, ctx: &str) -> ConstrResult<&'a [MValue]> {
        let (t, fields) = self.block(v, ctx)?;
        if t != tag || fields.len() != n {
            return Err(shape(
                ctx,
                format!(
                    "expected block tag {tag} with {n} fields, got tag {t} with {}",
                    fields.len()
                ),
            ));
        }
        Ok(fields)
    }

    fn int(&self, v: MValue, ctx: &str) -> ConstrResult<i64> {
        self.dag
            .int(v)
            .ok_or_else(|| shape(ctx, format!("expected int, got {v:?}")))
    }

    fn string(&self, v: MValue, ctx: &str) -> ConstrResult<String> {
        self.dag
            .string_lossy(v)
            .ok_or_else(|| shape(ctx, format!("expected string, got {v:?}")))
    }

    fn array(&self, v: MValue, ctx: &str) -> ConstrResult<&'a [MValue]> {
        self.dag
            .array(v)
            .ok_or_else(|| shape(ctx, format!("expected array, got {v:?}")))
    }

    fn list(&self, v: MValue, ctx: &str) -> ConstrResult<Vec<MValue>> {
        self.dag
            .list(v)
            .ok_or_else(|| shape(ctx, format!("expected list, got {v:?}")))
    }

    // -- names --------------------------------------------------------------

    pub fn dirpath(&self, v: MValue) -> ConstrResult<DirPath> {
        let items = self.list(v, "DirPath.t")?;
        let mut out = Vec::with_capacity(items.len());
        for it in items {
            out.push(self.string(it, "DirPath id")?);
        }
        Ok(DirPath(out))
    }

    pub fn modpath(&self, v: MValue) -> ConstrResult<ModPath> {
        let (tag, fields) = self.block(v, "ModPath.t")?;
        match (tag, fields) {
            (0, [dp]) => Ok(ModPath::File(self.dirpath(*dp)?)),
            (1, [uid]) => {
                let f = self.tagged(*uid, 0, 3, "MBId.t")?;
                Ok(ModPath::Bound {
                    uid: self.int(f[0], "MBId uid")?,
                    id: self.string(f[1], "MBId id")?,
                    dp: self.dirpath(f[2])?,
                })
            }
            (2, [mp, label]) => Ok(ModPath::Dot(
                Box::new(self.modpath(*mp)?),
                self.string(*label, "MPdot label")?,
            )),
            _ => Err(shape("ModPath.t", format!("tag {tag}/{}", fields.len()))),
        }
    }

    pub fn kername(&self, v: MValue) -> ConstrResult<KerName> {
        let f = self.tagged(v, 0, 3, "KerName.t")?;
        Ok(KerName {
            modpath: self.modpath(f[0])?,
            label: self.string(f[1], "KerName label")?,
        })
    }

    /// `Constant.t` / `MutInd.t` (KerPair: Same | Dual).
    pub fn kerpair(&self, v: MValue) -> ConstrResult<KerPair> {
        let (tag, fields) = self.block(v, "KerPair")?;
        match (tag, fields) {
            (0, [kn]) => Ok(KerPair {
                user: self.kername(*kn)?,
                canonical: None,
            }),
            (1, [user, canon]) => Ok(KerPair {
                user: self.kername(*user)?,
                canonical: Some(self.kername(*canon)?),
            }),
            _ => Err(shape("KerPair", format!("tag {tag}/{}", fields.len()))),
        }
    }

    pub fn ind_ref(&self, v: MValue) -> ConstrResult<IndRef> {
        let f = self.tagged(v, 0, 2, "inductive")?;
        Ok(IndRef {
            mind: self.kerpair(f[0])?,
            index: self.int(f[1], "inductive index")?,
        })
    }

    pub fn ctor_ref(&self, v: MValue) -> ConstrResult<CtorRef> {
        let f = self.tagged(v, 0, 2, "constructor")?;
        Ok(CtorRef {
            ind: self.ind_ref(f[0])?,
            index: self.int(f[1], "constructor index")?,
        })
    }

    // -- universes / sorts ---------------------------------------------------

    pub fn qvar(&self, v: MValue) -> ConstrResult<QVar> {
        let (tag, fields) = self.block(v, "QVar.t")?;
        match (tag, fields) {
            (0, [i]) => Ok(QVar::Idx(self.int(*i, "QVar var")?)),
            (1, [s, i]) => Ok(QVar::Named(
                self.string(*s, "QVar name")?,
                self.int(*i, "QVar uid")?,
            )),
            _ => Err(shape("QVar.t", format!("tag {tag}/{}", fields.len()))),
        }
    }

    pub fn quality(&self, v: MValue) -> ConstrResult<Quality> {
        let (tag, fields) = self.block(v, "Quality.t")?;
        match (tag, fields) {
            (0, [q]) => Ok(Quality::Var(self.qvar(*q)?)),
            (1, [c]) => Ok(Quality::Constant(self.int(*c, "Quality constant")?)),
            _ => Err(shape("Quality.t", format!("tag {tag}/{}", fields.len()))),
        }
    }

    pub fn level(&self, v: MValue) -> ConstrResult<Level> {
        let f = self.tagged(v, 0, 2, "Level.t")?;
        let hash = self.int(f[0], "Level hash")?;
        let data = match f[1] {
            MValue::Int(0) => RawLevel::Set,
            raw => {
                let (tag, rf) = self.block(raw, "RawLevel.t")?;
                match (tag, rf) {
                    (0, [g]) => {
                        let gf = self.tagged(*g, 0, 3, "UGlobal.t")?;
                        RawLevel::Level(UGlobal {
                            library: self.dirpath(gf[0])?,
                            process: self.string(gf[1], "UGlobal process")?,
                            uid: self.int(gf[2], "UGlobal uid")?,
                        })
                    }
                    (1, [i]) => RawLevel::Var(self.int(*i, "RawLevel var")?),
                    _ => return Err(shape("RawLevel.t", format!("tag {tag}"))),
                }
            }
        };
        Ok(Level { hash, data })
    }

    pub fn universe(&self, v: MValue) -> ConstrResult<Vec<(Level, i64)>> {
        let exprs = self.list(v, "Universe.t")?;
        let mut out = Vec::with_capacity(exprs.len());
        for e in exprs {
            let f = self.tagged(e, 0, 2, "Universe expr")?;
            out.push((self.level(f[0])?, self.int(f[1], "Universe incr")?));
        }
        Ok(out)
    }

    pub fn sort(&self, v: MValue) -> ConstrResult<Sort> {
        match v {
            MValue::Int(0) => Ok(Sort::SProp),
            MValue::Int(1) => Ok(Sort::Prop),
            MValue::Int(2) => Ok(Sort::Set),
            _ => {
                let (tag, fields) = self.block(v, "Sorts.t")?;
                match (tag, fields) {
                    (0, [u]) => Ok(Sort::Type(self.universe(*u)?)),
                    (1, [q, u]) => Ok(Sort::QSort(self.qvar(*q)?, self.universe(*u)?)),
                    _ => Err(shape("Sorts.t", format!("tag {tag}/{}", fields.len()))),
                }
            }
        }
    }

    pub fn relevance(&self, v: MValue) -> ConstrResult<Relevance> {
        match v {
            MValue::Int(0) => Ok(Relevance::Relevant),
            MValue::Int(1) => Ok(Relevance::Irrelevant),
            _ => {
                let (_, fields) = self.block(v, "Sorts.relevance")?;
                match fields {
                    [q] => Ok(Relevance::Var(self.qvar(*q)?)),
                    _ => Err(shape("Sorts.relevance", "bad arity")),
                }
            }
        }
    }

    pub fn binder(&self, v: MValue) -> ConstrResult<Binder> {
        let f = self.tagged(v, 0, 2, "binder_annot")?;
        let name = match f[0] {
            MValue::Int(0) => None,
            nv => {
                let nf = self.tagged(nv, 0, 1, "Name.t")?;
                Some(self.string(nf[0], "Name id")?)
            }
        };
        Ok(Binder {
            name,
            relevance: self.relevance(f[1])?,
        })
    }

    pub fn instance(&self, v: MValue) -> ConstrResult<Instance> {
        let f = self.tagged(v, 0, 2, "UVars.Instance.t")?;
        let quals = self.array(f[0], "Instance qualities")?;
        let levels = self.array(f[1], "Instance levels")?;
        Ok(Instance {
            qualities: quals
                .iter()
                .map(|q| self.quality(*q))
                .collect::<ConstrResult<_>>()?,
            levels: levels
                .iter()
                .map(|l| self.level(*l))
                .collect::<ConstrResult<_>>()?,
        })
    }

    // -- terms ---------------------------------------------------------------

    fn binder_array(&self, v: MValue, ctx: &str) -> ConstrResult<Vec<Binder>> {
        self.array(v, ctx)?
            .iter()
            .map(|b| self.binder(*b))
            .collect()
    }

    fn constr_array(&mut self, v: MValue, depth: usize, ctx: &str) -> ConstrResult<Vec<Constr>> {
        let items = self.array(v, ctx)?;
        items
            .iter()
            .map(|c| self.constr_at(*c, depth + 1))
            .collect()
    }

    fn rec_decl(&mut self, v: MValue, depth: usize) -> ConstrResult<RecDecl> {
        let f = self.tagged(v, 0, 3, "prec_declaration")?;
        Ok(RecDecl {
            binders: self.binder_array(f[0], "prec binders")?,
            types: self.constr_array(f[1], depth, "prec types")?,
            bodies: self.constr_array(f[2], depth, "prec bodies")?,
        })
    }

    /// Decode a term.
    ///
    /// # Errors
    ///
    /// Returns `ConstrError` on shape mismatches, depth-limit violations,
    /// or `Meta`/`Evar` nodes (which never occur in checked `.vo` terms).
    pub fn constr(&mut self, v: MValue) -> ConstrResult<Constr> {
        self.constr_at(v, 0)
    }

    fn constr_at(&mut self, v: MValue, depth: usize) -> ConstrResult<Constr> {
        if depth > MAX_DEPTH {
            return Err(ConstrError::Depth { limit: MAX_DEPTH });
        }
        let memo_key = match v {
            MValue::Ref(i) => {
                if let Some(hit) = self.memo.get(&i) {
                    return Ok(hit.clone());
                }
                Some(i)
            }
            _ => None,
        };
        let out = self.constr_uncached(v, depth)?;
        if let Some(k) = memo_key {
            self.memo.insert(k, out.clone());
        }
        Ok(out)
    }

    fn constr_uncached(&mut self, v: MValue, depth: usize) -> ConstrResult<Constr> {
        let (tag, f) = self.block(v, "Constr.t")?;
        let d = depth + 1;
        match (tag, f) {
            (0, [i]) => Ok(Constr::Rel(self.int(*i, "Rel")?)),
            (1, [id]) => Ok(Constr::Var(self.string(*id, "Var")?)),
            (2, _) => Err(ConstrError::Unsupported { name: "Meta" }),
            (3, _) => Err(ConstrError::Unsupported { name: "Evar" }),
            (4, [s]) => Ok(Constr::Sort(Box::new(self.sort(*s)?))),
            (5, [c, k, t]) => {
                let kind = match self.int(*k, "cast_kind")? {
                    0 => CastKind::Vm,
                    1 => CastKind::Native,
                    2 => CastKind::Default,
                    other => return Err(shape("cast_kind", format!("value {other}"))),
                };
                Ok(Constr::Cast(
                    Box::new(self.constr_at(*c, d)?),
                    kind,
                    Box::new(self.constr_at(*t, d)?),
                ))
            }
            (6, [b, t1, t2]) => Ok(Constr::Prod(
                self.binder(*b)?,
                Box::new(self.constr_at(*t1, d)?),
                Box::new(self.constr_at(*t2, d)?),
            )),
            (7, [b, t, c]) => Ok(Constr::Lambda(
                self.binder(*b)?,
                Box::new(self.constr_at(*t, d)?),
                Box::new(self.constr_at(*c, d)?),
            )),
            (8, [b, val, t, c]) => Ok(Constr::LetIn(
                self.binder(*b)?,
                Box::new(self.constr_at(*val, d)?),
                Box::new(self.constr_at(*t, d)?),
                Box::new(self.constr_at(*c, d)?),
            )),
            (9, [head, args]) => Ok(Constr::App(
                Box::new(self.constr_at(*head, d)?),
                self.constr_array(*args, d, "App args")?,
            )),
            (10, [pu]) => {
                let pf = self.tagged(*pu, 0, 2, "Const punivs")?;
                Ok(Constr::Const(Box::new((
                    self.kerpair(pf[0])?,
                    self.instance(pf[1])?,
                ))))
            }
            (11, [pu]) => {
                let pf = self.tagged(*pu, 0, 2, "Ind punivs")?;
                Ok(Constr::Ind(Box::new((
                    self.ind_ref(pf[0])?,
                    self.instance(pf[1])?,
                ))))
            }
            (12, [pu]) => {
                let pf = self.tagged(*pu, 0, 2, "Construct punivs")?;
                Ok(Constr::Construct(Box::new((
                    self.ctor_ref(pf[0])?,
                    self.instance(pf[1])?,
                ))))
            }
            (13, [ci, u, params, ret, invert, scrut, branches]) => Ok(Constr::Case(Box::new(
                self.case(*ci, *u, *params, *ret, *invert, *scrut, *branches, d)?,
            ))),
            (14, [fx]) => {
                let ff = self.tagged(*fx, 0, 2, "pfixpoint")?;
                let f2 = self.tagged(ff[0], 0, 2, "fix indexes")?;
                let struct_args = self
                    .array(f2[0], "fix struct args")?
                    .iter()
                    .map(|i| self.int(*i, "fix struct arg"))
                    .collect::<ConstrResult<_>>()?;
                Ok(Constr::Fix {
                    struct_args,
                    which: self.int(f2[1], "fix which")?,
                    decl: Box::new(self.rec_decl(ff[1], d)?),
                })
            }
            (15, [cf]) => {
                let ff = self.tagged(*cf, 0, 2, "pcofixpoint")?;
                Ok(Constr::CoFix {
                    which: self.int(ff[0], "cofix which")?,
                    decl: Box::new(self.rec_decl(ff[1], d)?),
                })
            }
            (16, [p, r, c]) => {
                let pf = self.tagged(*p, 0, 2, "Projection.t")?;
                let rf = self.tagged(pf[0], 0, 4, "Projection.Repr.t")?;
                let unfolded = self.int(pf[1], "Projection unfolded")? != 0;
                Ok(Constr::Proj(
                    Box::new(ProjData {
                        ind: self.ind_ref(rf[0])?,
                        npars: self.int(rf[1], "Proj npars")?,
                        arg: self.int(rf[2], "Proj arg")?,
                        name: self.kerpair(rf[3])?,
                        unfolded,
                    }),
                    self.relevance(*r)?,
                    Box::new(self.constr_at(*c, d)?),
                ))
            }
            (17, [i]) => Ok(Constr::Uint63(self.int(*i, "Uint63")?)),
            (18, [fl]) => match self.dag.get(*fl) {
                Some(super::marshal_parser::MObject::Double(x)) => Ok(Constr::Float64(*x)),
                _ => Err(shape("Float64", "expected boxed double")),
            },
            (19, [s]) => Ok(Constr::PStr(
                self.dag
                    .str_bytes(*s)
                    .ok_or_else(|| shape("PString", "expected string"))?
                    .to_vec(),
            )),
            (20, [u, elems, def, ty]) => Ok(Constr::Array(Box::new((
                self.instance(*u)?,
                self.constr_array(*elems, d, "Array elems")?,
                self.constr_at(*def, d)?,
                self.constr_at(*ty, d)?,
            )))),
            _ => Err(shape(
                "Constr.t",
                format!("unknown tag {tag} with {} fields", f.len()),
            )),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn case(
        &mut self,
        ci: MValue,
        u: MValue,
        params: MValue,
        ret: MValue,
        invert: MValue,
        scrut: MValue,
        branches: MValue,
        depth: usize,
    ) -> ConstrResult<CaseData> {
        let cif = self.tagged(ci, 0, 5, "case_info")?;
        let pp = self.tagged(cif[4], 0, 1, "case_printing")?;
        let info = CaseInfo {
            ind: self.ind_ref(cif[0])?,
            npar: self.int(cif[1], "ci_npar")?,
            cstr_ndecls: self
                .array(cif[2], "ci_cstr_ndecls")?
                .iter()
                .map(|i| self.int(*i, "ci_cstr_ndecls"))
                .collect::<ConstrResult<_>>()?,
            cstr_nargs: self
                .array(cif[3], "ci_cstr_nargs")?
                .iter()
                .map(|i| self.int(*i, "ci_cstr_nargs"))
                .collect::<ConstrResult<_>>()?,
            style: self.int(pp[0], "case_style")?,
        };

        let rf = self.tagged(ret, 0, 2, "case_return")?;
        let rif = self.tagged(rf[0], 0, 2, "case_return'")?;
        let ret = CaseReturn {
            binders: self.binder_array(rif[0], "return binders")?,
            body: self.constr_at(rif[1], depth + 1)?,
            relevance: self.relevance(rf[1])?,
        };

        let invert = match invert {
            MValue::Int(0) => None,
            iv => {
                let inf = self.tagged(iv, 0, 1, "case_inversion")?;
                Some(self.constr_array(inf[0], depth, "CaseInvert indices")?)
            }
        };

        let branch_vals = self.array(branches, "case branches")?;
        let mut brs = Vec::with_capacity(branch_vals.len());
        for b in branch_vals {
            let bf = self.tagged(*b, 0, 2, "case_branch")?;
            brs.push(CaseBranch {
                binders: self.binder_array(bf[0], "branch binders")?,
                body: self.constr_at(bf[1], depth + 1)?,
            });
        }

        Ok(CaseData {
            info,
            instance: self.instance(u)?,
            params: self.constr_array(params, depth, "case params")?,
            ret,
            invert,
            scrutinee: self.constr_at(scrut, depth + 1)?,
            branches: brs,
        })
    }
}

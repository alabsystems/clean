// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean 4.36.0 kernel objects with the computed fields required by its runtime.

use std::collections::{HashMap, HashSet};
use std::ptr;

use clean_kernel::env::{ConstantInfo, ConstantKind, Reducibility};
use clean_kernel::{BinderData, Expr, ExprKind, Level, Literal, Multiplicity, Name};

use crate::error::{OleanError, OleanResult};
use crate::expr::expr_tags;
use crate::module::DefinitionSafety;

use super::{LeanV2RegionWriter, LeanV2Value, OleanExporter};

impl LeanV2RegionWriter {
    /// Write a Clean kernel universe level, including Lean's computed data.
    ///
    /// # Errors
    /// Refuses a level exceeding Lean's 24-bit depth field or an encoding failure.
    pub fn write_level(&mut self, level: &Level) -> OleanResult<LeanV2Value> {
        Ok(TermWriter::new(self).level(level)?.value)
    }

    /// Write a Lean kernel expression. Clean kernel lambda and forall
    /// binders are emitted with anonymous names because they carry no names.
    ///
    /// # Errors
    /// Refuses free variables, metadata, nonstandard kernel expressions,
    /// linear or erased binders, and values exceeding the wire layout.
    pub fn write_expr(&mut self, expr: &Expr) -> OleanResult<LeanV2Value> {
        Ok(TermWriter::new(self).expr(expr)?.value)
    }

    /// Write an axiom or a standalone definition, theorem, or opaque.
    /// The caller supplies Lean's safety designation and establishes that
    /// any mutual group contains just this declaration.
    ///
    /// # Errors
    /// Refuses the invalid declaration shapes and encoding failures described
    /// by [`Self::write_constant_info_with_group`].
    pub fn write_constant_info(
        &mut self,
        info: &ConstantInfo,
        safety: DefinitionSafety,
    ) -> OleanResult<LeanV2Value> {
        let all = match info.kind {
            ConstantKind::Axiom => &[],
            _ => std::slice::from_ref(&info.name),
        };
        self.write_constant_info_with_group(info, safety, all)
    }

    /// Write a native Lean constant record with its ordered mutual group.
    /// An axiom takes an empty group. A definition, theorem, or opaque takes
    /// its exact list of group members, including its own name. Lambda and
    /// forall binders get anonymous names, as in [`Self::write_expr`].
    ///
    /// # Errors
    /// Refuses a value-bearing axiom, missing bodies on other records,
    /// incompatible safety, an invalid mutual group, loose variables,
    /// unsupported reducibility attributes, or an encoding failure.
    pub fn write_constant_info_with_group(
        &mut self,
        info: &ConstantInfo,
        safety: DefinitionSafety,
        all: &[Name],
    ) -> OleanResult<LeanV2Value> {
        validate_group(info, all)?;
        let mut terms = TermWriter::new(self);
        let ty = terms.expr(&info.type_)?.closed()?;
        let name = terms.writer.write_name(&info.name)?;
        let params = terms.names(&info.level_params)?;
        let base = terms
            .writer
            .write_constructor(0, &[name, params, ty], &[])?;
        let (tag, value) = match (info.kind, &info.value) {
            (ConstantKind::Axiom, None) if safety != DefinitionSafety::Partial => {
                let is_unsafe = u8::from(safety == DefinitionSafety::Unsafe);
                (0, terms.writer.write_constructor(0, &[base], &[is_unsafe])?)
            }
            (ConstantKind::Definition, Some(value)) => {
                let value = terms.expr(value)?.closed()?;
                let hints = terms.hints(info.reducibility)?;
                let all = terms.names(all)?;
                let value = terms.writer.write_constructor(
                    0,
                    &[base, value, hints, all],
                    &[safety.to_tag() as u8],
                )?;
                (1, value)
            }
            (ConstantKind::Theorem, Some(proof)) if safety == DefinitionSafety::Safe => {
                let proof = terms.expr(proof)?.closed()?;
                let all = terms.names(all)?;
                (
                    2,
                    terms
                        .writer
                        .write_constructor(0, &[base, proof, all], &[])?,
                )
            }
            (ConstantKind::Opaque, Some(value)) if safety != DefinitionSafety::Partial => {
                let value = terms.expr(value)?.closed()?;
                let all = terms.names(all)?;
                let is_unsafe = u8::from(safety == DefinitionSafety::Unsafe);
                (
                    3,
                    terms
                        .writer
                        .write_constructor(0, &[base, value, all], &[is_unsafe])?,
                )
            }
            _ => {
                return Err(region_error(
                    "unsupported Lean v2 constant kind, value, or safety",
                ))
            }
        };
        terms.writer.write_constructor(tag, &[value], &[])
    }
}

fn validate_group(info: &ConstantInfo, all: &[Name]) -> OleanResult<()> {
    if info.kind == ConstantKind::Axiom {
        return if all.is_empty() {
            Ok(())
        } else {
            Err(region_error("Lean v2 axioms have no mutual group field"))
        };
    }
    let mut members = HashSet::new();
    for name in all {
        if name.is_anon() || !members.insert(name) {
            return Err(region_error(
                "Lean v2 mutual group names must be nonanonymous and unique",
            ));
        }
    }
    if !members.contains(&info.name) {
        return Err(region_error(
            "Lean v2 mutual group must include the declaration's name",
        ));
    }
    Ok(())
}

struct TermWriter<'a> {
    writer: &'a mut LeanV2RegionWriter,
    exprs: HashMap<*const Expr, EncodedExpr>,
    levels: HashMap<*const Level, EncodedLevel>,
}

impl<'a> TermWriter<'a> {
    fn new(writer: &'a mut LeanV2RegionWriter) -> Self {
        Self {
            writer,
            exprs: HashMap::new(),
            levels: HashMap::new(),
        }
    }

    // Each input reference outlives the traversal. Pointer keys preserve DAG
    // sharing without recursively hashing Rust expressions or levels.
    fn expr(&mut self, root: &Expr) -> OleanResult<EncodedExpr> {
        let mut pending = vec![(root, false)];
        while let Some((expr, children_done)) = pending.pop() {
            let key = ptr::from_ref(expr);
            if self.exprs.contains_key(&key) {
                continue;
            }
            if children_done {
                let encoded = self.write_expr_node(expr)?;
                self.exprs.insert(key, encoded);
                continue;
            }
            pending.push((expr, true));
            match expr.kind() {
                ExprKind::App(left, right)
                | ExprKind::Lam(_, left, right)
                | ExprKind::Pi(_, left, right) => {
                    pending.push((right, false));
                    pending.push((left, false));
                }
                ExprKind::Let(_, ty, value, body, _) => {
                    pending.push((body, false));
                    pending.push((value, false));
                    pending.push((ty, false));
                }
                ExprKind::Proj(_, _, body) => pending.push((body, false)),
                ExprKind::BVar(_) | ExprKind::Sort(_) | ExprKind::Const(..) | ExprKind::Lit(_) => {}
                _ => {
                    return Err(region_error(
                        "expression is outside the Lean v2 export subset",
                    ))
                }
            }
        }
        self.expr_child(root)
    }

    fn expr_child(&self, expr: &Expr) -> OleanResult<EncodedExpr> {
        self.exprs
            .get(&ptr::from_ref(expr))
            .copied()
            .ok_or_else(|| region_error("missing encoded Lean expression"))
    }

    fn write_expr_node(&mut self, expr: &Expr) -> OleanResult<EncodedExpr> {
        match expr.kind() {
            ExprKind::BVar(index) => {
                let index = u64::from(*index);
                let data = ExprData::new(mix_hash(7, index), index + 1, 0, false)?;
                self.expr_object(expr_tags::BVAR, &[LeanV2Value::scalar(index)?], data, None)
            }
            ExprKind::Sort(level) => {
                let level = self.level(level)?;
                let data = ExprData::new(mix_hash(11, level.hash), 0, 0, level.has_param)?;
                self.expr_object(expr_tags::SORT, &[level.value], data, None)
            }
            ExprKind::Const(name, levels) => {
                let mut universe_values = Vec::with_capacity(levels.len());
                let mut universe_hash = 7;
                let mut has_param = false;
                for level in levels {
                    let level = self.level(level)?;
                    universe_values.push(level.value);
                    universe_hash = mix_hash(universe_hash, level.hash);
                    has_param |= level.has_param;
                }
                let hash = mix_hash(5, mix_hash(name.lean4_hash(), universe_hash));
                let data = ExprData::new(hash, 0, 0, has_param)?;
                let name = self.writer.write_name(name)?;
                let levels = self.list(universe_values.into_iter().rev())?;
                self.expr_object(expr_tags::CONST, &[name, levels], data, None)
            }
            ExprKind::App(function, argument) => {
                let function = self.expr_child(function)?;
                let argument = self.expr_child(argument)?;
                let f = function.data;
                let a = argument.data;
                let data = ExprData::new(
                    mix_hash(f.0, a.0),
                    f.loose().max(a.loose()),
                    1 + f.depth().max(a.depth()),
                    f.has_param() || a.has_param(),
                )?;
                self.expr_object(
                    expr_tags::APP,
                    &[function.value, argument.value],
                    data,
                    None,
                )
            }
            ExprKind::Lam(binder, ty, body) => self.binder(expr_tags::LAM, binder, ty, body),
            ExprKind::Pi(binder, ty, body) => self.binder(expr_tags::FORALL_E, binder, ty, body),
            ExprKind::Let(name, ty, value, body, nondep) => {
                let ty = self.expr_child(ty)?;
                let value = self.expr_child(value)?;
                let body = self.expr_child(body)?;
                let t = ty.data;
                let v = value.data;
                let b = body.data;
                let depth = 1 + t.depth().max(v.depth()).max(b.depth());
                let hash = mix_hash(depth, mix_hash(t.hash(), mix_hash(v.hash(), b.hash())));
                let data = ExprData::new(
                    hash,
                    t.loose().max(v.loose()).max(b.loose().saturating_sub(1)),
                    depth,
                    t.has_param() || v.has_param() || b.has_param(),
                )?;
                let name = self.writer.write_name(name)?;
                self.expr_object(
                    expr_tags::LET_E,
                    &[name, ty.value, value.value, body.value],
                    data,
                    Some(u8::from(*nondep)),
                )
            }
            ExprKind::Lit(literal) => {
                let (tag, value, hash) = match literal {
                    Literal::Nat(nat) => (
                        0,
                        self.writer.write_nat(nat)?,
                        nat.limbs().first().copied().unwrap_or(0),
                    ),
                    Literal::String(text) => {
                        (1, self.writer.write_string(text)?, string_hash(text))
                    }
                };
                let value = self.writer.write_constructor(tag, &[value], &[])?;
                let data = ExprData::new(mix_hash(3, hash), 0, 0, false)?;
                self.expr_object(expr_tags::LIT, &[value], data, None)
            }
            ExprKind::Proj(name, index, body) => {
                let body = self.expr_child(body)?;
                let depth = 1 + body.data.depth();
                let index = u64::from(*index);
                let hash = mix_hash(
                    depth,
                    mix_hash(name.lean4_hash(), mix_hash(index, body.data.hash())),
                );
                let data = ExprData::new(hash, body.data.loose(), depth, body.data.has_param())?;
                let name = self.writer.write_name(name)?;
                self.expr_object(
                    expr_tags::PROJ,
                    &[name, LeanV2Value::scalar(index)?, body.value],
                    data,
                    None,
                )
            }
            _ => Err(region_error(
                "expression is outside the Lean v2 export subset",
            )),
        }
    }

    fn binder(
        &mut self,
        tag: u8,
        binder: &BinderData,
        ty: &Expr,
        body: &Expr,
    ) -> OleanResult<EncodedExpr> {
        if binder.mult != Multiplicity::Many {
            return Err(region_error(
                "Lean v2 binders require unrestricted multiplicity",
            ));
        }
        let ty = self.expr_child(ty)?;
        let body = self.expr_child(body)?;
        let t = ty.data;
        let b = body.data;
        let depth = 1 + t.depth().max(b.depth());
        let data = ExprData::new(
            mix_hash(depth, mix_hash(t.hash(), b.hash())),
            t.loose().max(b.loose().saturating_sub(1)),
            depth,
            t.has_param() || b.has_param(),
        )?;
        let anonymous = LeanV2Value::scalar(0)?;
        self.expr_object(
            tag,
            &[anonymous, ty.value, body.value],
            data,
            Some(OleanExporter::binder_info_to_u8(binder.info)),
        )
    }

    fn expr_object(
        &mut self,
        tag: u8,
        fields: &[LeanV2Value],
        data: ExprData,
        tail: Option<u8>,
    ) -> OleanResult<EncodedExpr> {
        let mut scalars = [0; 9];
        scalars[..8].copy_from_slice(&data.0.to_le_bytes());
        let bytes = if let Some(tail) = tail {
            scalars[8] = tail;
            &scalars[..]
        } else {
            &scalars[..8]
        };
        let value = self.writer.write_constructor(tag, fields, bytes)?;
        Ok(EncodedExpr { value, data })
    }

    fn level(&mut self, root: &Level) -> OleanResult<EncodedLevel> {
        let mut pending = vec![(root, false)];
        while let Some((level, children_done)) = pending.pop() {
            let key = ptr::from_ref(level);
            if self.levels.contains_key(&key) {
                continue;
            }
            if children_done {
                let encoded = self.write_level_node(level)?;
                self.levels.insert(key, encoded);
                continue;
            }
            pending.push((level, true));
            match level {
                Level::Succ(child) => pending.push((child, false)),
                Level::Max(left, right) | Level::IMax(left, right) => {
                    pending.push((right, false));
                    pending.push((left, false));
                }
                Level::Zero | Level::Param(_) => {}
            }
        }
        self.level_child(root)
    }

    fn level_child(&self, level: &Level) -> OleanResult<EncodedLevel> {
        self.levels
            .get(&ptr::from_ref(level))
            .copied()
            .ok_or_else(|| region_error("missing encoded Lean level"))
    }

    fn write_level_node(&mut self, level: &Level) -> OleanResult<EncodedLevel> {
        match level {
            // The computed-field accessor supplies zero's data for its
            // nullary scalar representation.
            Level::Zero => Ok(EncodedLevel {
                value: LeanV2Value::scalar(0)?,
                hash: 2221,
                depth: 0,
                has_param: false,
            }),
            Level::Succ(child) => {
                let child = self.level_child(child)?;
                self.level_object(
                    1,
                    &[child.value],
                    mix_hash(2243, child.hash),
                    child.depth + 1,
                    child.has_param,
                )
            }
            Level::Max(left, right) | Level::IMax(left, right) => {
                let left = self.level_child(left)?;
                let right = self.level_child(right)?;
                let (tag, seed) = if matches!(level, Level::Max(..)) {
                    (2, 2251)
                } else {
                    (3, 2267)
                };
                self.level_object(
                    tag,
                    &[left.value, right.value],
                    mix_hash(seed, mix_hash(left.hash, right.hash)),
                    1 + left.depth.max(right.depth),
                    left.has_param || right.has_param,
                )
            }
            Level::Param(name) => {
                let value = self.writer.write_name(name)?;
                self.level_object(4, &[value], mix_hash(2239, name.lean4_hash()), 0, true)
            }
        }
    }

    fn level_object(
        &mut self,
        tag: u8,
        fields: &[LeanV2Value],
        hash: u64,
        depth: u64,
        has_param: bool,
    ) -> OleanResult<EncodedLevel> {
        // Lean's Level.Data stores a 32-bit hash, flags and a 24-bit depth.
        if depth >= 1 << 24 {
            return Err(region_error("Lean v2 universe level depth exceeds 24 bits"));
        }
        let hash = low_u32(hash);
        let data = hash | (u64::from(has_param) << 33) | (depth << 40);
        let value = self
            .writer
            .write_constructor(tag, fields, &data.to_le_bytes())?;
        Ok(EncodedLevel {
            value,
            hash,
            depth,
            has_param,
        })
    }

    fn list(
        &mut self,
        reversed: impl IntoIterator<Item = LeanV2Value>,
    ) -> OleanResult<LeanV2Value> {
        let mut tail = LeanV2Value::scalar(0)?;
        for head in reversed {
            tail = self.writer.write_constructor(1, &[head, tail], &[])?;
        }
        Ok(tail)
    }

    fn names(&mut self, names: &[Name]) -> OleanResult<LeanV2Value> {
        let mut values = Vec::with_capacity(names.len());
        for name in names {
            values.push(self.writer.write_name(name)?);
        }
        self.list(values.into_iter().rev())
    }

    fn hints(&mut self, reducibility: Reducibility) -> OleanResult<LeanV2Value> {
        match reducibility {
            Reducibility::Opaque => LeanV2Value::scalar(0),
            Reducibility::Reducible => LeanV2Value::scalar(1),
            Reducibility::Regular(height) => {
                self.writer.write_constructor(2, &[], &height.to_le_bytes())
            }
            Reducibility::Irreducible => Err(region_error(
                "Lean v2 export requires the irreducible attribute extension",
            )),
        }
    }
}

#[derive(Clone, Copy)]
struct EncodedLevel {
    value: LeanV2Value,
    hash: u64,
    depth: u64,
    has_param: bool,
}

#[derive(Clone, Copy)]
struct EncodedExpr {
    value: LeanV2Value,
    data: ExprData,
}

impl EncodedExpr {
    fn closed(self) -> OleanResult<LeanV2Value> {
        if self.data.loose() != 0 {
            return Err(region_error(
                "Lean v2 declaration contains a loose bound variable",
            ));
        }
        Ok(self.value)
    }
}

// Lean 4.36 Expr.mkData stores a 32-bit hash, an 8-bit saturating depth,
// four flags, and the 20-bit loose bound variable range.
#[derive(Clone, Copy)]
struct ExprData(u64);

impl ExprData {
    fn new(hash: u64, loose: u64, depth: u64, has_param: bool) -> OleanResult<Self> {
        if loose >= 1 << 20 {
            return Err(region_error(
                "Lean v2 loose bound variable range exceeds 20 bits",
            ));
        }
        Ok(Self(
            low_u32(hash) | (depth.min(255) << 32) | (u64::from(has_param) << 43) | (loose << 44),
        ))
    }

    fn hash(self) -> u64 {
        low_u32(self.0)
    }

    fn depth(self) -> u64 {
        (self.0 >> 32) & 255
    }

    fn has_param(self) -> bool {
        (self.0 & (1 << 43)) != 0
    }

    fn loose(self) -> u64 {
        self.0 >> 44
    }
}

fn low_u32(word: u64) -> u64 {
    word & u64::from(u32::MAX)
}

const HASH_MULTIPLIER: u64 = 0xc6a4_a793_5bd1_e995;

fn mix_hash(hash: u64, value: u64) -> u64 {
    let mixed = value.wrapping_mul(HASH_MULTIPLIER);
    (hash ^ mixed ^ (mixed >> 47) ^ HASH_MULTIPLIER).wrapping_mul(HASH_MULTIPLIER)
}

// Lean's String.hash uses MurmurHash64A with a seed of 11.
fn string_hash(text: &str) -> u64 {
    let (blocks, tail) = text.as_bytes().as_chunks::<8>();
    let mut hash = 11 ^ (text.len() as u64).wrapping_mul(HASH_MULTIPLIER);
    for block in blocks {
        let value = u64::from_le_bytes(*block).wrapping_mul(HASH_MULTIPLIER);
        hash ^= (value ^ (value >> 47)).wrapping_mul(HASH_MULTIPLIER);
        hash = hash.wrapping_mul(HASH_MULTIPLIER);
    }
    for (index, byte) in tail.iter().enumerate() {
        hash ^= u64::from(*byte) << (8 * index);
    }
    if !tail.is_empty() {
        hash = hash.wrapping_mul(HASH_MULTIPLIER);
    }
    hash = (hash ^ (hash >> 47)).wrapping_mul(HASH_MULTIPLIER);
    hash ^ (hash >> 47)
}

fn region_error(reason: &str) -> OleanError {
    OleanError::Region(reason.to_owned())
}

#[cfg(test)]
#[path = "lean_v2_decl_tests.rs"]
mod tests;

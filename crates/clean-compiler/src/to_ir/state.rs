// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! State management for L5CNF → L5IR conversion.
//!
//! Contains `CtorMeta`, `ToIRState`, and `ToIRConfig` — the core
//! data structures that track variable mappings, constructor metadata,
//! and configuration during IR lowering.

use crate::error::CompilerError;
use crate::ir::{CtorInfo, IRArg, IRType, JoinPointId, VarId};
use clean_kernel::{FVarId, Name};
use std::cell::RefCell;
use std::collections::HashMap;

/// Pre-computed constructor metadata for IR lowering (Part of #1953).
///
/// Populated from `ConstructorVal` + field type analysis. Maps constructor
/// names to their tag index and field type information so that `to_ir` can
/// generate correct `CtorInfo` instead of hardcoding `tag: 0`.
#[derive(Clone, Debug)]
pub struct CtorMeta {
    /// Tag value (position in parent inductive's constructor list).
    pub tag: u32,
    /// Number of leading INDUCTIVE PARAMETERS in the constructor's telescope
    /// (`ConstructorVal::num_params`). Parameters carry no field slot, but a
    /// kernel-spelled constructor application passes them as leading args —
    /// including VALUE-level parameters (`Fin.mk`'s `n : Nat`, `BitVec.ofFin`'s
    /// `w : Nat`), which type-erasure does NOT remove. The lowering must drop
    /// exactly this many leading args before aligning with `field_types`;
    /// zipping the raw spine silently stored `n` in `val`'s slot (the
    /// `Fin.ofNat` corruption).
    pub num_params: u32,
    /// Field types (after skipping the `num_params` parameter binders).
    pub field_types: Vec<IRType>,
    /// Number of scalar fields (computed from field_types).
    pub num_scalars: u32,
    /// Number of object fields (computed from field_types).
    pub num_objects: u32,
}

/// State for IR conversion.
///
/// Tracks variable mappings, generates fresh IDs, and provides function arity
/// information for distinguishing full applications from partial applications.
#[derive(Debug)]
pub struct ToIRState {
    /// Maps L5CNF FVarId to L5IR VarId.
    vars: HashMap<FVarId, IRArg>,
    /// Maps join point FVarId to JoinPointId.
    join_points: HashMap<FVarId, JoinPointId>,
    /// Next available variable ID.
    next_var: u32,
    /// Next available join point ID.
    next_jp: u32,
    /// Diagnostic warnings for non-fatal compatibility fallbacks that remain
    /// outside the fail-closed Result boundary (for example env-less ctor info).
    pub(crate) warnings: RefCell<Vec<String>>,
    /// Function arities for PartialApply detection (Part of #1936).
    /// Maps declaration name to total parameter count. When a `LetValue::Const`
    /// has fewer args than the function's arity, we emit `PartialApply` instead
    /// of `Apply`.
    arities: HashMap<Name, u16>,
    /// Constructor metadata for correct CtorInfo generation (Part of #1953).
    /// Maps constructor names to their tag and field layout info. When present,
    /// `LetValue::Ctor`, `LetValue::Reuse`, and `Alt::Ctor` use real tag/field
    /// data instead of hardcoding `tag: 0, num_scalars: 0`.
    ctor_env: HashMap<Name, CtorMeta>,
    /// Inductive type name → constructor metadata for Proj field type lookup.
    /// Maps inductive names (e.g., `Prod`) to their constructor's field types.
    /// For single-constructor types (structures), allows `LetValue::Proj` to
    /// determine the correct field type instead of hardcoding `Object`.
    /// Part of #1941.
    inductive_env: HashMap<Name, CtorMeta>,
    /// Variable type tracking for scalar type inference.
    /// Maps VarId to the IRType determined at lowering time. Used by
    /// `_sset` pseudo-op lowering to emit the correct scalar type instead
    /// of defaulting to UInt64. Part of #2123.
    var_types: HashMap<VarId, IRType>,
    /// Known compile-time `Nat` VALUE of a variable (R2 scalar-carrier
    /// chain): recorded at `Nat` literal bindings and propagated through the
    /// value-preserving `OfNat.ofNat` spelling. This is the affirmative
    /// WIDTH EVIDENCE the `Fin.ofNat` / `BitVec.ofNatLT` decode rewrites
    /// require (`lower_scalar_width_nat_decode`): a decode is claimed only
    /// when the modulus / width operand is one of these known values, never
    /// on type grounds alone.
    known_nat_values: HashMap<VarId, u64>,
    /// Variables bound to `System.Platform.numBits` — the platform-size WIDTH
    /// evidence for `USize`. `numBits` is a `Const`, never a `Nat` literal, so
    /// it carries no `known_nat_value`; a `BitVec.ofNatLT numBits n h` decode
    /// (the `USize.ofNatLT` carrier chain) recognizes the width through this
    /// sentinel and targets `USize` (see `lower_scalar_width_nat_decode`).
    numbits_vars: std::collections::HashSet<VarId>,
}

impl Default for ToIRState {
    fn default() -> Self {
        Self::new()
    }
}

impl ToIRState {
    /// Create a new conversion state (no arity info — full applications only).
    pub fn new() -> Self {
        Self {
            vars: HashMap::new(),
            join_points: HashMap::new(),
            next_var: 0,
            next_jp: 0,
            warnings: RefCell::new(Vec::new()),
            arities: HashMap::new(),
            ctor_env: HashMap::new(),
            inductive_env: HashMap::new(),
            var_types: HashMap::new(),
            known_nat_values: HashMap::new(),
            numbits_vars: std::collections::HashSet::new(),
        }
    }

    /// Create a conversion state with function arity information.
    ///
    /// When arities are provided, `LetValue::Const` with fewer args than the
    /// function's arity will produce `IRExpr::PartialApply` instead of
    /// `IRExpr::Apply`. Part of #1936.
    pub fn with_arities(arities: HashMap<Name, u16>) -> Self {
        Self {
            vars: HashMap::new(),
            join_points: HashMap::new(),
            next_var: 0,
            next_jp: 0,
            warnings: RefCell::new(Vec::new()),
            arities,
            ctor_env: HashMap::new(),
            inductive_env: HashMap::new(),
            var_types: HashMap::new(),
            known_nat_values: HashMap::new(),
            numbits_vars: std::collections::HashSet::new(),
        }
    }

    /// Create a conversion state with both arity and constructor info.
    ///
    /// Constructor metadata enables correct tag, num_scalars, and field_type
    /// generation instead of hardcoding zeros. Part of #1953.
    pub fn with_arities_and_ctors(
        arities: HashMap<Name, u16>,
        ctor_env: HashMap<Name, CtorMeta>,
        inductive_env: HashMap<Name, CtorMeta>,
    ) -> Self {
        Self {
            vars: HashMap::new(),
            join_points: HashMap::new(),
            next_var: 0,
            next_jp: 0,
            warnings: RefCell::new(Vec::new()),
            arities,
            ctor_env,
            inductive_env,
            var_types: HashMap::new(),
            known_nat_values: HashMap::new(),
            numbits_vars: std::collections::HashSet::new(),
        }
    }

    /// Look up the arity (parameter count) of a named function.
    pub(super) fn get_arity(&self, name: &Name) -> Option<u16> {
        self.arities.get(name).copied()
    }

    /// Look up the full constructor metadata for a projection's inductive type.
    ///
    /// Returns `None` if the type isn't in `inductive_env`. Part of #1982.
    pub(super) fn lookup_proj_meta(&self, type_name: &Name) -> Option<&CtorMeta> {
        self.inductive_env.get(type_name)
    }

    /// Look up full constructor metadata by constructor name.
    pub(super) fn lookup_ctor_meta(&self, ctor_name: &Name) -> Option<&CtorMeta> {
        self.ctor_env.get(ctor_name)
    }

    /// Bind an FVarId to a fresh VarId.
    pub(super) fn bind_var(&mut self, fvar: FVarId) -> VarId {
        let var_id = VarId(self.next_var);
        self.next_var += 1;
        self.vars.insert(fvar, IRArg::Var(var_id));
        var_id
    }

    /// Bind an FVarId to erased.
    pub(super) fn bind_erased(&mut self, fvar: FVarId) {
        self.vars.insert(fvar, IRArg::Erased);
    }

    /// Bind an FVarId as an ALIAS of an already-lowered IR value, emitting no
    /// instruction. Used by the scalar-carrier constructor lowering (C5b):
    /// a newtype-style construction whose carrier already has the target
    /// scalar representation IS that value (`Char.mk v h` = `v`), so the
    /// binding is pure renaming — every later use of `fvar` resolves to the
    /// carrier's VarId, and type lookups see the carrier's recorded type.
    pub(super) fn bind_alias(&mut self, fvar: FVarId, arg: IRArg) {
        self.vars.insert(fvar, arg);
    }

    /// Get the IR argument for an FVarId.
    pub(super) fn get_var(&self, fvar: FVarId) -> Result<IRArg, CompilerError> {
        self.vars
            .get(&fvar)
            .cloned()
            .ok_or(CompilerError::UnboundToIrVar { fvar })
    }

    /// Bind a join point FVarId to a fresh JoinPointId.
    pub(super) fn bind_jp(&mut self, fvar: FVarId) -> JoinPointId {
        let jp_id = JoinPointId(self.next_jp);
        self.next_jp += 1;
        self.join_points.insert(fvar, jp_id);
        jp_id
    }

    /// Get the JoinPointId for an FVarId.
    pub(super) fn get_jp(&self, fvar: FVarId) -> Result<JoinPointId, CompilerError> {
        self.join_points
            .get(&fvar)
            .copied()
            .ok_or(CompilerError::UnboundToIrJoinPoint { fvar })
    }

    /// Record the IRType for a VarId. Part of #2123 (Bug 2).
    pub(super) fn record_var_type(&mut self, var: VarId, ty: IRType) {
        self.var_types.insert(var, ty);
    }

    /// Record a variable's known compile-time `Nat` VALUE (R2 width
    /// evidence — see the `known_nat_values` field doc).
    pub(super) fn record_known_nat_value(&mut self, var: VarId, value: u64) {
        self.known_nat_values.insert(var, value);
    }

    /// Look up a variable's known compile-time `Nat` value, if any.
    pub(super) fn known_nat_value(&self, var: VarId) -> Option<u64> {
        self.known_nat_values.get(&var).copied()
    }

    /// Mark a variable as bound to `System.Platform.numBits` (the `USize`
    /// platform-size width sentinel — see the `numbits_vars` field doc).
    pub(super) fn record_numbits_var(&mut self, var: VarId) {
        self.numbits_vars.insert(var);
    }

    /// Whether a variable is bound to `System.Platform.numBits`.
    pub(super) fn is_numbits_var(&self, var: VarId) -> bool {
        self.numbits_vars.contains(&var)
    }

    /// Look up the IRType for a VarId. Part of #2123 (Bug 2).
    pub(super) fn get_var_type(&self, var: VarId) -> Option<&IRType> {
        self.var_types.get(&var)
    }

    /// Drain accumulated diagnostic warnings from the conversion state.
    ///
    /// Returns all warnings accumulated during IR lowering (e.g., constructor
    /// metadata fallbacks). The warning buffer is cleared after this call.
    /// Part of #2012.
    pub fn drain_warnings(&self) -> Vec<String> {
        self.warnings.borrow_mut().drain(..).collect()
    }

    /// Build a `CtorInfo` using constructor environment lookup.
    ///
    /// When the constructor is found in `ctor_env`, uses real tag and field type
    /// data. Otherwise falls back to `tag: 0, num_scalars: 0` with a warning.
    /// Part of #1953.
    pub(super) fn make_ctor_info(&self, name: &Name, num_args_fallback: usize) -> CtorInfo {
        if let Some(meta) = self.ctor_env.get(name) {
            CtorInfo {
                name: name.clone(),
                tag: meta.tag,
                num_scalars: meta.num_scalars,
                num_objects: meta.num_objects,
                field_types: meta.field_types.clone(),
            }
        } else {
            if !self.ctor_env.is_empty() {
                self.warnings.borrow_mut().push(format!(
                    "constructor {:?} not found in ctor_env, using fallback tag=0",
                    name
                ));
            }
            CtorInfo {
                name: name.clone(),
                tag: 0,
                num_scalars: 0,
                num_objects: num_args_fallback as u32,
                field_types: vec![IRType::Object; num_args_fallback],
            }
        }
    }
}

/// Configuration for IR conversion.
#[derive(Debug, Clone)]
pub struct ToIRConfig {
    /// Enable trivial structure elimination.
    pub eliminate_trivial: bool,
}

impl Default for ToIRConfig {
    fn default() -> Self {
        Self {
            eliminate_trivial: true,
        }
    }
}

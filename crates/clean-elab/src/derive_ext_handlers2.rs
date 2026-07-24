// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended derive handler implementations (batch 2) with statistics tracking.
//!
//! Provides [`DeriveHandlerRegistry2`] with 8 built-in handlers and per-handler
//! invocation statistics. Handlers: BEq, Hashable, Repr, Ord, DecidableEq,
//! Inhabited, Nonempty, SizeOf.

use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};

use clean_kernel::{BinderInfo, Environment, Expr, ExprKind, Level, Name};

use crate::derive::DeriveError;
use crate::derive_handlers::{
    extract_universe_level, mk_bool, mk_bool_false, mk_bool_true, mk_nat, mk_str_lit,
    wrap_param_lambdas, wrap_param_pis,
};

// ---------------------------------------------------------------------------
// Core types
// ---------------------------------------------------------------------------

/// Constructor metadata for batch-2 handlers.
#[derive(Debug, Clone)]
pub(crate) struct CtorInfo2 {
    pub(crate) name: Name,
    pub(crate) fields: Vec<(Name, Expr)>,
    pub(crate) is_recursive: bool,
}

/// A derived declaration produced by a batch-2 handler.
#[derive(Debug, Clone)]
pub(crate) struct DerivedDecl2 {
    pub(crate) name: Name,
    pub(crate) type_: Expr,
    pub(crate) value: Expr,
    pub(crate) is_instance: bool,
}

/// Trait for batch-2 derive handlers.
pub(crate) trait ExtDeriveHandler2: Send + Sync {
    fn derive(
        &self,
        env: &Environment,
        type_name: &Name,
        type_expr: &Expr,
        ctors: &[CtorInfo2],
        num_params: u32,
        level_params: &[Name],
    ) -> Result<Vec<DerivedDecl2>, DeriveError>;

    fn class_name(&self) -> &str;
}

// ---------------------------------------------------------------------------
// Statistics
// ---------------------------------------------------------------------------

#[derive(Debug)]
pub(crate) struct HandlerStats {
    pub(crate) invocations: AtomicU64,
    pub(crate) successes: AtomicU64,
    pub(crate) failures: AtomicU64,
}

impl HandlerStats {
    fn new() -> Self {
        Self {
            invocations: AtomicU64::new(0),
            successes: AtomicU64::new(0),
            failures: AtomicU64::new(0),
        }
    }

    fn record_success(&self) {
        self.invocations.fetch_add(1, Ordering::Relaxed);
        self.successes.fetch_add(1, Ordering::Relaxed);
    }

    fn record_failure(&self) {
        self.invocations.fetch_add(1, Ordering::Relaxed);
        self.failures.fetch_add(1, Ordering::Relaxed);
    }
}

/// Snapshot of handler stats for external consumption.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct HandlerStatsSnapshot {
    pub(crate) invocations: u64,
    pub(crate) successes: u64,
    pub(crate) failures: u64,
}

// ---------------------------------------------------------------------------
// Registry
// ---------------------------------------------------------------------------

/// Registry of batch-2 derive handlers with statistics tracking.
pub(crate) struct DeriveHandlerRegistry2 {
    handlers: HashMap<String, Box<dyn ExtDeriveHandler2>>,
    stats: HashMap<String, HandlerStats>,
}

impl DeriveHandlerRegistry2 {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            handlers: HashMap::new(),
            stats: HashMap::new(),
        }
    }

    pub(crate) fn register(&mut self, class_name: &str, handler: Box<dyn ExtDeriveHandler2>) {
        self.handlers.insert(class_name.to_owned(), handler);
        self.stats
            .insert(class_name.to_owned(), HandlerStats::new());
    }

    #[must_use]
    pub(crate) fn has_handler(&self, class_name: &str) -> bool {
        self.handlers.contains_key(class_name)
    }

    pub(crate) fn derive_all(
        &self,
        env: &Environment,
        type_name: &Name,
        type_expr: &Expr,
        ctors: &[CtorInfo2],
        classes: &[Name],
        num_params: u32,
        level_params: &[Name],
    ) -> Result<Vec<DerivedDecl2>, DeriveError> {
        let mut results = Vec::new();
        for class in classes {
            let cs = class.to_string();
            let handler = self
                .handlers
                .get(&cs)
                .ok_or_else(|| DeriveError::NoHandler(cs.clone()))?;
            match handler.derive(env, type_name, type_expr, ctors, num_params, level_params) {
                Ok(decls) => {
                    if let Some(s) = self.stats.get(&cs) {
                        s.record_success();
                    }
                    results.extend(decls);
                }
                Err(e) => {
                    if let Some(s) = self.stats.get(&cs) {
                        s.record_failure();
                    }
                    return Err(e);
                }
            }
        }
        Ok(results)
    }

    #[must_use]
    pub(crate) fn default_registry() -> Self {
        let mut reg = Self::new();
        reg.register("BEq", Box::new(DeriveBEq2));
        reg.register("Hashable", Box::new(DeriveHashable2));
        reg.register("Repr", Box::new(DeriveRepr2));
        reg.register("Ord", Box::new(DeriveOrd2));
        reg.register("DecidableEq", Box::new(DeriveDecidableEq2));
        reg.register("Inhabited", Box::new(DeriveInhabited2));
        reg.register("Nonempty", Box::new(DeriveNonempty2));
        reg.register("SizeOf", Box::new(DeriveSizeOf2));
        reg
    }

    pub(crate) fn registered_classes(&self) -> Vec<&str> {
        self.handlers.keys().map(String::as_str).collect()
    }

    #[must_use]
    pub(crate) fn stats_for(&self, class_name: &str) -> Option<HandlerStatsSnapshot> {
        self.stats.get(class_name).map(|s| HandlerStatsSnapshot {
            invocations: s.invocations.load(Ordering::Relaxed),
            successes: s.successes.load(Ordering::Relaxed),
            failures: s.failures.load(Ordering::Relaxed),
        })
    }

    #[must_use]
    pub(crate) fn all_stats(&self) -> HashMap<String, HandlerStatsSnapshot> {
        self.stats
            .iter()
            .map(|(k, v)| {
                (
                    k.clone(),
                    HandlerStatsSnapshot {
                        invocations: v.invocations.load(Ordering::Relaxed),
                        successes: v.successes.load(Ordering::Relaxed),
                        failures: v.failures.load(Ordering::Relaxed),
                    },
                )
            })
            .collect()
    }
}

impl std::fmt::Debug for DeriveHandlerRegistry2 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DeriveHandlerRegistry2")
            .field("handlers", &self.handlers.keys().collect::<Vec<_>>())
            .finish()
    }
}

// ---------------------------------------------------------------------------
// Shared helpers
// ---------------------------------------------------------------------------

fn inst_name(class_name: &str, type_name: &Name) -> Name {
    Name::from_string(&format!("inst{class_name}{type_name}"))
}

fn mk_applied_type(type_name: &Name, num_params: u32) -> Expr {
    let base = Expr::const_(type_name.clone(), vec![]);
    if num_params == 0 {
        return base;
    }
    let args: Vec<Expr> = (0..num_params).rev().map(Expr::bvar).collect();
    Expr::apps(base, args)
}

fn reject_recursive(ctors: &[CtorInfo2], cn: &str, tn: &Name) -> Result<(), DeriveError> {
    if ctors.iter().any(|c| c.is_recursive) {
        return Err(DeriveError::Unsupported {
            class_name: cn.to_owned(),
            ind_name: tn.to_string(),
            reason: "recursive constructors are not supported by this handler".to_owned(),
        });
    }
    Ok(())
}

/// Bound externally supplied telescope sizes before any `usize` arithmetic or
/// conversion to the kernel's `u32` de Bruijn/projection indices. The factor of
/// eight leaves headroom for builders that combine two field telescopes and add
/// local proof binders. Oversized metadata is rejected as a typed derive error;
/// it must never wrap or silently become `bvar 0`.
fn check_index_capacity(
    cn: &str,
    tn: &Name,
    ctors: &[CtorInfo2],
    np: u32,
) -> Result<(), DeriveError> {
    const MAX_INPUT_ARITY: usize = (u32::MAX as usize) / 8;

    let total_fields = ctors
        .iter()
        .try_fold(0usize, |total, ctor| total.checked_add(ctor.fields.len()));
    let oversized = (np as usize) > MAX_INPUT_ARITY
        || ctors.len() > MAX_INPUT_ARITY
        || ctors.iter().any(|ctor| ctor.fields.len() > MAX_INPUT_ARITY)
        || total_fields.is_none_or(|total| total > MAX_INPUT_ARITY);
    if oversized {
        return Err(DeriveError::Unsupported {
            class_name: cn.to_owned(),
            ind_name: tn.to_string(),
            reason: format!(
                "constructor/parameter arity exceeds the safe kernel-index limit of {MAX_INPUT_ARITY}"
            ),
        });
    }
    Ok(())
}

fn wrap_params(value: Expr, type_: Expr, np: u32) -> (Expr, Expr) {
    (wrap_param_lambdas(value, np), wrap_param_pis(type_, np))
}

fn mk_inst_ty(tn: &Name, cn: &str, np: u32) -> Expr {
    Expr::app(class_const(cn), mk_applied_type(tn, np))
}

/// The class head constant for an instance type. The prelude bootstraps the
/// single-parameter `Type u` classes (`BEq`/`Repr`/`Hashable`/`Inhabited`/…) as
/// universe-polymorphic inductives (one level param `u`); for the monomorphic
/// `Type 0` targets these handlers support, the class is instantiated at `u = 0`.
/// Supplying the explicit level here satisfies the kernel's strict level-arity
/// check (mirrors `DeriveBEq2`, which already threads `@BEq.{0}`). Classes that
/// are not universe-polymorphic in the environment simply ignore the level (a
/// 0-level class still expects 0 levels — see `is_level_polymorphic_class`).
fn class_const(cn: &str) -> Expr {
    if is_level_polymorphic_class(cn) {
        Expr::const_str_levels(cn, vec![Level::zero()])
    } else {
        Expr::const_str(cn)
    }
}

/// Single-parameter `Type u` classes that this handler module instantiates at a
/// monomorphic `u = 0` against a universe-polymorphic prelude inductive. Scoped
/// to the classes bootstrapped into the prelude by Task NN (`Repr`/`Hashable`):
/// `BEq` already threads its own level inline, and `Inhabited`/`Ord` keep their
/// existing (pre-Task-NN) handling untouched to avoid disturbing passing tests.
fn is_level_polymorphic_class(cn: &str) -> bool {
    matches!(cn, "Repr" | "Hashable")
}

fn mk_binary_lam(ty: &Expr, body: Expr) -> Expr {
    Expr::lam(
        BinderInfo::Default,
        ty.clone(),
        Expr::lam(BinderInfo::Default, ty.clone(), body),
    )
}

/// Build a single instance decl from an instance body expression.
fn mk_single_inst(cn: &str, tn: &Name, np: u32, body: Expr) -> Vec<DerivedDecl2> {
    let (value, type_) = wrap_params(body, mk_inst_ty(tn, cn, np), np);
    vec![DerivedDecl2 {
        name: inst_name(cn, tn),
        type_,
        value,
        is_instance: true,
    }]
}

/// Require at least one constructor; return the first.
fn require_first_ctor<'a>(
    ctors: &'a [CtorInfo2],
    cn: &str,
    tn: &Name,
) -> Result<&'a CtorInfo2, DeriveError> {
    ctors.first().ok_or_else(|| DeriveError::Unsupported {
        class_name: cn.to_owned(),
        ind_name: tn.to_string(),
        reason: "type has no constructors".to_owned(),
    })
}

// ---------------------------------------------------------------------------
// Single-ctor struct derivation (shared field-instance resolution)
// ---------------------------------------------------------------------------

/// If `ty` is a bare monomorphic `Const(name, [])` head, return its name.
///
/// Field-instance resolution is restricted to this shape: a non-parametric,
/// non-applied constant such as `Nat`, `Bool`, or another in-tree enum. Applied
/// types (`List Nat`), bound variables, sorts, etc. are intentionally rejected
/// so the resolved instance term is unambiguously the monomorphic instance for
/// exactly that type.
fn bare_const_name(ty: &Expr) -> Option<&Name> {
    match ty.kind() {
        ExprKind::Const(name, levels) if levels.is_empty() => Some(name),
        _ => None,
    }
}

/// Resolve the instance constant for `class_name` applied to the bare
/// monomorphic field type `field_ty` from `env`.
///
/// Walks the registered instances for the class and accepts one whose type is
/// exactly `@<class_name> <field_ty>` (i.e. `App(Const(class_name, _),
/// Const(field_name, []))`). The instance type is read from
/// [`KernelInstanceInfo::type_`] when present, otherwise from the registered
/// constant's declared type (prelude instances such as `instBEqNat` register
/// with `type_: None` but their `add_decl` type is `BEq Nat`).
///
/// Returns the closed instance term `Const(inst_name, [])` on a match (instances
/// resolvable here are monomorphic, so they carry no level params), or `None`
/// when no monomorphic in-tree instance for the field type exists. Callers then
/// try another genuine builder or fail closed with `Unsupported`.
pub(crate) fn resolve_field_instance(
    env: &Environment,
    class_name: &str,
    field_ty: &Expr,
) -> Option<Expr> {
    let field_name = bare_const_name(field_ty)?;
    let class = Name::from_string(class_name);
    for inst in env.get_class_instances(&class) {
        let inst_ty = inst
            .type_
            .clone()
            .or_else(|| env.get_const(&inst.name).map(|c| c.type_.clone()))?;
        // Match `@<class> <field_ty>` exactly: an application whose function is
        // `Const(class_name, _)` and whose argument is the bare field constant.
        if let ExprKind::App(fun, arg) = inst_ty.kind() {
            let fun_ok = matches!(fun.kind(), ExprKind::Const(n, _) if n == &class);
            let arg_ok = bare_const_name(arg).is_some_and(|n| n == field_name);
            if fun_ok && arg_ok {
                return Some(Expr::const_(inst.name.clone(), vec![]));
            }
        }
    }
    None
}

/// The single-ctor struct shape gate: exactly one constructor with `>= 1` field,
/// no type parameters, non-recursive. Returns the sole constructor on success.
pub(crate) fn single_ctor_struct(ctors: &[CtorInfo2], np: u32) -> Option<&CtorInfo2> {
    if np != 0 {
        return None;
    }
    let [ctor] = ctors else {
        return None;
    };
    if ctor.fields.is_empty() || ctor.is_recursive {
        return None;
    }
    Some(ctor)
}

/// Project field `i` (0-based) of a single-ctor struct `tn` out of the term
/// `major` via the inductive recursor.
///
/// For a struct `S` with constructor `S.mk : F0 → … → F_{n-1} → S` (no type
/// parameters), the projection of field `i` is
///
/// ```text
/// @S.rec.{motive_level} (fun (_ : S) => Fi)
///   (fun (a0 : F0) … (a_{n-1} : F_{n-1}) => a_i)   -- sole minor premise
///   major
/// ```
///
/// `motive_level` is the universe the field type lives in (`Sort 1` for the
/// data fields supported here). The minor premise binds all `n` fields, so field
/// `i` is `bvar(n - 1 - i)` in its body. The result is a closed, kernel-checkable
/// term that introduces no `sorryAx`/axioms — only the struct's own recursor.
pub(crate) fn project_struct_field(
    tn: &Name,
    field_idx: usize,
    field_ty: &Expr,
    fields: &[(Name, Expr)],
    major: Expr,
    motive_level: &Level,
) -> Expr {
    let ind_ty = Expr::const_(tn.clone(), vec![]);
    // motive: fun (_ : S) => Fi  (field type does not depend on the scrutinee).
    let motive = Expr::lam(BinderInfo::Default, ind_ty, field_ty.clone());

    // minor: fun (a0 : F0) … (a_{n-1} : F_{n-1}) => a_i.
    let n = fields.len();
    let body =
        Expr::bvar(u32::try_from(n - 1 - field_idx).expect("derive arity was checked to fit u32"));
    let mut minor = body;
    for (_fname, fty) in fields.iter().rev() {
        minor = Expr::lam(BinderInfo::Default, fty.clone(), minor);
    }

    let rec_const = Expr::const_(
        Name::from_string(&format!("{tn}.rec")),
        vec![motive_level.clone()],
    );
    Expr::apps(rec_const, [motive, minor, major])
}

/// Try to build a sorry-free `BEq` instance value for the single-ctor struct
/// shape (1 constructor, `np == 0`, `>= 1` field, non-recursive).
///
/// The in-tree `BEq` class carries `beq : α → α → Bool`, so the instance value
/// is a binary lambda `fun (a b : S) => <body : Bool>` with `a = bvar 1`,
/// `b = bvar 0`. The body conjoins per-field comparisons via `Bool.and`:
///
/// ```text
/// fun (a b : S) =>
///   Bool.and (@BEq.beq F0 instF0 a.0 b.0)
///     (Bool.and (@BEq.beq F1 instF1 a.1 b.1) … Bool.true)
/// ```
///
/// where `a.i` / `b.i` are recursor projections (see [`project_struct_field`])
/// and `instFi` is the field type's own `BEq` instance resolved from `env`. The
/// fold is right-nested and seeded with `Bool.true`, so a single field collapses
/// to `Bool.and (beq …) Bool.true`. Every field type must resolve a monomorphic
/// in-tree `BEq` instance; otherwise this returns `None` and the caller tries
/// another genuine builder or fails closed with `Unsupported`.
fn beq_struct_value(env: &Environment, tn: &Name, ctors: &[CtorInfo2], np: u32) -> Option<Expr> {
    let ctor = single_ctor_struct(ctors, np)?;
    // The struct lives in `Type 0 = Sort 1`; its data fields also live in
    // `Sort 1`, so the projecting recursor eliminates into `Sort 1`.
    let motive_level = Level::succ(Level::zero());
    let ind_ty = Expr::const_(tn.clone(), vec![]);

    // Resolve every field's BEq instance up front; bail to the honest fallback
    // if any field type lacks a resolvable monomorphic instance.
    let mut field_insts = Vec::with_capacity(ctor.fields.len());
    for (_fname, fty) in &ctor.fields {
        field_insts.push(resolve_field_instance(env, "BEq", fty)?);
    }

    // body: right-nested Bool.and of per-field comparisons, seeded with Bool.true.
    let bool_and = Expr::const_str("Bool.and");
    let mut body = mk_bool_true();
    for (idx, (_fname, fty)) in ctor.fields.iter().enumerate().rev() {
        // a = bvar 1, b = bvar 0 at body depth.
        let a_field =
            project_struct_field(tn, idx, fty, &ctor.fields, Expr::bvar(1), &motive_level);
        let b_field =
            project_struct_field(tn, idx, fty, &ctor.fields, Expr::bvar(0), &motive_level);
        // @BEq.beq.{0} Fi instFi a.i b.i. `BEq.beq` carries one universe param
        // `u`; the supported field types live in `Type 0`, so it is `u = 0`.
        let cmp = Expr::apps(
            Expr::const_str_levels("BEq.beq", vec![Level::zero()]),
            [fty.clone(), field_insts[idx].clone(), a_field, b_field],
        );
        body = Expr::apps(bool_and.clone(), [cmp, body]);
    }

    Some(mk_binary_lam(&ind_ty, body))
}

// ---------------------------------------------------------------------------
// DeriveBEq2
// ---------------------------------------------------------------------------

pub(crate) struct DeriveBEq2;

impl ExtDeriveHandler2 for DeriveBEq2 {
    fn class_name(&self) -> &str {
        "BEq"
    }

    fn derive(
        &self,
        env: &Environment,
        tn: &Name,
        _te: &Expr,
        ctors: &[CtorInfo2],
        np: u32,
        _lp: &[Name],
    ) -> Result<Vec<DerivedDecl2>, DeriveError> {
        check_index_capacity(self.class_name(), tn, ctors, np)?;
        reject_recursive(ctors, "BEq", tn)?;
        let ind_ty = mk_applied_type(tn, np);

        // Single-ctor struct shape (1 ctor, np == 0, >= 1 field, non-recursive):
        // `beq a b = BEq.beq a.f1 b.f1 && BEq.beq a.f2 b.f2 && ...` where each
        // field comparison resolves the field type's own `BEq` instance from the
        // environment. Closed and kernel-checkable; no proof obligation. If any
        // field instance is unresolvable the helper returns `None` and we try
        // another genuine builder before failing closed. The struct lives in
        // `Type 0`, so `@BEq.{0}` / `@BEq.mk.{0}` are supplied explicitly (as in
        // the nullary-enum branch) to satisfy the kernel's level-arity check.
        if let Some(beq_fn) = beq_struct_value(env, tn, ctors, np) {
            let u_level = Level::zero();
            let inst_ty = Expr::app(
                Expr::const_str_levels("BEq", vec![u_level.clone()]),
                ind_ty.clone(),
            );
            let value = Expr::apps(
                Expr::const_str_levels("BEq.mk", vec![u_level]),
                [ind_ty, beq_fn],
            );
            let (value, type_) = wrap_params(value, inst_ty, np);
            return Ok(vec![DerivedDecl2 {
                name: inst_name("BEq", tn),
                type_,
                value,
                is_instance: true,
            }]);
        }

        // Multi-ctor-with-fields shape (>= 2 constructors, some/all carrying
        // fields, np == 0, non-recursive): the union of the nullary-enum
        // per-ctor dispatch and the single-ctor-struct field composition. The
        // outer/inner recursor dispatch on `a`/`b` selects the constructor pair;
        // the diagonal (same ctor) conjoins the per-field `BEq.beq` comparisons
        // of that constructor's fields (true for a 0-field ctor), and every
        // off-diagonal pair returns `Bool.false`. Every field type must resolve a
        // monomorphic in-tree `BEq` instance, else the helper returns `None` and
        // we fall through to the honest fallback below. Same `@BEq.{0}` /
        // `@BEq.mk.{0}` level-arity threading as the other branches.
        if let Some(beq_fn) = beq_multi_ctor_fields_value(env, tn, ctors, np) {
            let u_level = Level::zero();
            let inst_ty = Expr::app(
                Expr::const_str_levels("BEq", vec![u_level.clone()]),
                ind_ty.clone(),
            );
            let value = Expr::apps(
                Expr::const_str_levels("BEq.mk", vec![u_level]),
                [ind_ty, beq_fn],
            );
            let (value, type_) = wrap_params(value, inst_ty, np);
            return Ok(vec![DerivedDecl2 {
                name: inst_name("BEq", tn),
                type_,
                value,
                is_instance: true,
            }]);
        }

        // Try the genuine, sorry-free construction for the nullary-enum shape
        // (>= 1 constructors, all arity 0, no type parameters). Boolean equality
        // there is constructively computable via a nested recursor dispatch:
        // the diagonal (same ctor) returns `Bool.true`, every off-diagonal pair
        // returns `Bool.false`. Unlike `DecidableEq`, `BEq` returns a plain
        // `Bool` and discharges no proof obligation, so no `noConfusion` is
        // needed. Any other shape fails closed below.
        match beq_nullary_enum_value(tn, ctors, np) {
            Some(beq_fn) => {
                // `BEq.{u} (α : Type u)`: for the nullary-enum shape `E : Type 0`,
                // the parameter universe is `u = 0`. Supply the level explicitly
                // to both `@BEq.{0}` (instance type) and `@BEq.mk.{0} E beq_fn`
                // (instance value) so the term satisfies the kernel's strict
                // level-arity check on the prelude `BEq` class (mirrors how the
                // sibling `DecidableEq` handler threads its universe level).
                let u_level = Level::zero();
                let inst_ty = Expr::app(
                    Expr::const_str_levels("BEq", vec![u_level.clone()]),
                    ind_ty.clone(),
                );
                let value = Expr::apps(
                    Expr::const_str_levels("BEq.mk", vec![u_level]),
                    [ind_ty, beq_fn],
                );
                let (value, type_) = wrap_params(value, inst_ty, np);
                Ok(vec![DerivedDecl2 {
                    name: inst_name("BEq", tn),
                    type_,
                    value,
                    is_instance: true,
                }])
            }
            None if ctors.is_empty() => {
                // Equality on an empty type is vacuous, so the closed constant
                // comparison is exact rather than a semantic fallback.
                let beq_fn = mk_binary_lam(&ind_ty, mk_bool_true());
                Ok(mk_single_inst(
                    "BEq",
                    tn,
                    np,
                    Expr::app(Expr::const_str("BEq.mk"), beq_fn),
                ))
            }
            None => Err(DeriveError::Unsupported {
                class_name: "BEq".to_owned(),
                ind_name: tn.to_string(),
                reason: "no structural BEq construction is available for this shape".to_owned(),
            }),
        }
    }
}

/// Try to build a sorry-free `BEq` instance value for the nullary-enum shape
/// (`>= 1` constructors, every constructor of arity 0, no type parameters).
///
/// The in-tree `BEq` class (matching the prelude `init_beq`) carries
///
/// ```text
/// class BEq (α : Type u) where
///   beq : α → α → Bool
/// ```
///
/// so the instance value is a binary lambda `fun (a b : E) => <body : Bool>`
/// with `a = bvar 1`, `b = bvar 0`. The body is a nested recursor dispatch: the
/// outer recursor splits on `a`, the inner on `b`:
///
/// ```text
/// fun (a b : E) =>
///   @E.rec.{1} (fun _ => Bool)          -- outer motive (constant: Bool)
///     <minor_a c_0> ... <minor_a c_{n-1}>   -- one per ctor of `a`
///     a
/// ```
///
/// where each outer minor (for `a = cᵢ`) re-dispatches on `b`:
///
/// ```text
///   @E.rec.{1} (fun _ => Bool)          -- inner motive (constant: Bool)
///     <minor_b c_0> ... <minor_b c_{n-1}>   -- one per ctor of `b`
///     b
/// ```
///
/// and each inner minor (for `b = cⱼ`) is the literal:
/// * `i == j` (diagonal):   `Bool.true`
/// * `i != j` (off-diag):   `Bool.false`
///
/// `Bool : Type = Sort 1`, so both recursors eliminate into `Sort 1` (motive
/// universe `1`) under the constant motive `fun _ => Bool`. The whole term is
/// closed (apart from the lambda-bound `a`, `b`) and kernel-checkable; it
/// introduces no `sorryAx`/axioms — only the type's own recursor and the `Bool`
/// constructors. Unlike `DecidableEq`, no `Eq.refl`/`noConfusion` proof terms
/// are required because `beq` returns a plain `Bool`.
///
/// Returns `None` for shapes outside this supported set (parametric inductives,
/// zero constructors, or any constructor with fields/recursion), so the caller
/// can either handle the genuinely empty case or report a typed error.
fn beq_nullary_enum_value(tn: &Name, ctors: &[CtorInfo2], np: u32) -> Option<Expr> {
    if np != 0 || ctors.is_empty() {
        return None;
    }
    if ctors.iter().any(|c| !c.fields.is_empty() || c.is_recursive) {
        return None;
    }

    let ind_ty = Expr::const_(tn.clone(), vec![]);
    // `E : Type 0 = Sort 1`, so the recursor eliminates into `Bool : Sort 1`.
    let motive_level = Level::succ(Level::zero());
    let rec_name = Name::from_string(&format!("{tn}.rec"));

    // Constant motive `fun (_ : E) => Bool` — the result type never depends on
    // the scrutinee, so the recursor's major-premise argument is ignored.
    let const_motive = || Expr::lam(BinderInfo::Default, ind_ty.clone(), mk_bool());

    // Outer recursor: dispatch on `a` (= bvar 1 at body depth).
    let outer_rec = Expr::const_(rec_name.clone(), vec![motive_level.clone()]);
    let mut outer = Expr::app(outer_rec, const_motive());

    for ctor_i in ctors {
        // Inner recursor: dispatch on `b` (= bvar 0 at body depth).
        let inner_rec = Expr::const_(rec_name.clone(), vec![motive_level.clone()]);
        let mut inner = Expr::app(inner_rec, const_motive());

        for ctor_j in ctors {
            let inner_minor = if ctor_i.name == ctor_j.name {
                mk_bool_true()
            } else {
                mk_bool_false()
            };
            inner = Expr::app(inner, inner_minor);
        }

        // Apply the inner recursor to its major `b` (= bvar 0 at this depth).
        inner = Expr::app(inner, Expr::bvar(0));
        outer = Expr::app(outer, inner);
    }

    // Apply the outer recursor to its major `a` (= bvar 1 at body depth).
    outer = Expr::app(outer, Expr::bvar(1));

    Some(mk_binary_lam(&ind_ty, outer))
}

/// The multi-ctor-with-fields shape gate: `>= 2` constructors, no type
/// parameters, non-recursive, and at least one constructor carrying `>= 1`
/// field. (Pure nullary enums are handled by [`beq_nullary_enum_value`]; this
/// branch is the strict generalization that admits field-carrying ctors.)
fn multi_ctor_fields_shape(ctors: &[CtorInfo2], np: u32) -> bool {
    np == 0
        && ctors.len() >= 2
        && ctors.iter().all(|c| !c.is_recursive)
        && ctors.iter().any(|c| !c.fields.is_empty())
}

/// Try to build a sorry-free `BEq` instance value for the multi-ctor-with-fields
/// shape (`>= 2` constructors, some/all carrying fields, `np == 0`,
/// non-recursive) — e.g. `Either A B`, `Result T E`, or a sum of records.
///
/// This is the union of [`beq_nullary_enum_value`]'s per-constructor dispatch
/// and [`beq_struct_value`]'s field composition. The instance value is the
/// binary lambda `fun (a b : T) => <body : Bool>` (`a = bvar 1`, `b = bvar 0`)
/// whose body is a nested recursor dispatch:
///
/// ```text
/// fun (a b : T) =>
///   @T.rec.{1} (fun _ => Bool)            -- outer motive (constant: Bool)
///     <outer_minor c_0> … <outer_minor c_{n-1}>   -- one per ctor of `a`
///     a
/// ```
///
/// where the outer minor for `a = cᵢ` binds `cᵢ`'s fields `(a₀ … a_{kᵢ-1})` and
/// re-dispatches on `b`:
///
/// ```text
///   fun (a₀ : Fᵢ₀) … (a_{kᵢ-1} : Fᵢ_{kᵢ-1}) =>
///     @T.rec.{1} (fun _ => Bool)          -- inner motive (constant: Bool)
///       <inner_minor c_0> … <inner_minor c_{n-1}>   -- one per ctor of `b`
///       b
/// ```
///
/// and the inner minor for `b = cⱼ` binds `cⱼ`'s fields `(b₀ … b_{kⱼ-1})`:
/// * `i == j` (diagonal):  `Bool.and (@BEq.beq Fᵢ₀ instᵢ₀ a₀ b₀) (… Bool.true)`
///   — the right-nested `Bool.and` conjunction of per-field comparisons, seeded
///   with `Bool.true` (so a 0-field constructor collapses to `Bool.true`).
/// * `i != j` (off-diag):  `Bool.false`.
///
/// De Bruijn bookkeeping inside the diagonal body for a `k`-field constructor:
/// the inner minor's `b`-fields sit at `bvar(k-1)…bvar(0)` (field `p` at
/// `bvar(k-1-p)`), and the outer minor's `a`-fields — pushed down by the `k`
/// inner binders — sit at `bvar(2k-1)…bvar(k)` (field `p` at `bvar(2k-1-p)`).
/// The inner major `b` is referenced at `bvar(kᵢ)` from the outer-minor body
/// (after entering `cᵢ`'s `kᵢ` field binders); the outer major `a` is `bvar 1`.
///
/// Every field type appearing on any constructor must resolve a monomorphic
/// in-tree `BEq` instance up front (via [`resolve_field_instance`]); if any is
/// unresolvable, or the shape is outside this set (single ctor, parametric,
/// recursive, all-nullary), this returns `None` and the caller tries another
/// genuine builder or fails closed. The whole term is closed and kernel-checkable; it
/// introduces no `sorryAx`/axioms — only the type's own recursor, `BEq.beq`,
/// `Bool.and`, and the `Bool` constructors.
fn beq_multi_ctor_fields_value(
    env: &Environment,
    tn: &Name,
    ctors: &[CtorInfo2],
    np: u32,
) -> Option<Expr> {
    if !multi_ctor_fields_shape(ctors, np) {
        return None;
    }

    // Resolve every field's BEq instance up front (across all constructors);
    // bail to the honest fallback if any field type lacks a resolvable
    // monomorphic instance. Stored per-constructor, indexed by field position.
    let mut ctor_field_insts: Vec<Vec<Expr>> = Vec::with_capacity(ctors.len());
    for ctor in ctors {
        let mut insts = Vec::with_capacity(ctor.fields.len());
        for (_fname, fty) in &ctor.fields {
            insts.push(resolve_field_instance(env, "BEq", fty)?);
        }
        ctor_field_insts.push(insts);
    }

    let ind_ty = Expr::const_(tn.clone(), vec![]);
    // `T : Type 0 = Sort 1`, so the recursor eliminates into `Bool : Sort 1`.
    let motive_level = Level::succ(Level::zero());
    let rec_name = Name::from_string(&format!("{tn}.rec"));
    let bool_and = Expr::const_str("Bool.and");

    // Constant motive `fun (_ : T) => Bool` — the result type never depends on
    // the scrutinee, so the recursor's major-premise argument is ignored.
    let const_motive = || Expr::lam(BinderInfo::Default, ind_ty.clone(), mk_bool());

    // Outer recursor: dispatch on `a` (= bvar 1 at the binary-lambda body depth).
    let outer_rec = Expr::const_(rec_name.clone(), vec![motive_level.clone()]);
    let mut outer = Expr::app(outer_rec, const_motive());

    for (i, ctor_i) in ctors.iter().enumerate() {
        let ki = ctor_i.fields.len();

        // Inner recursor: dispatch on `b`. At the outer-minor body depth (after
        // entering `cᵢ`'s `kᵢ` field binders) the major `b` is `bvar(kᵢ)`.
        let inner_rec = Expr::const_(rec_name.clone(), vec![motive_level.clone()]);
        let mut inner = Expr::app(inner_rec, const_motive());

        for (j, ctor_j) in ctors.iter().enumerate() {
            let inner_body = if i == j {
                // Diagonal: conjoin per-field `BEq.beq` comparisons, right-nested
                // and seeded with `Bool.true`. At the inner-minor body depth the
                // `b`-fields occupy `bvar(0)…bvar(kᵢ-1)` and the `a`-fields are
                // pushed down by `kᵢ` to `bvar(kᵢ)…bvar(2kᵢ-1)`.
                let mut body = mk_bool_true();
                for (p, (_fname, fty)) in ctor_i.fields.iter().enumerate().rev() {
                    let a_field = Expr::bvar(
                        u32::try_from(2 * ki - 1 - p).expect("derive arity was checked to fit u32"),
                    );
                    let b_field = Expr::bvar(
                        u32::try_from(ki - 1 - p).expect("derive arity was checked to fit u32"),
                    );
                    // @BEq.beq.{0} Fᵢ_p instᵢ_p a_p b_p : Bool.
                    let cmp = Expr::apps(
                        Expr::const_str_levels("BEq.beq", vec![Level::zero()]),
                        [
                            fty.clone(),
                            ctor_field_insts[i][p].clone(),
                            a_field,
                            b_field,
                        ],
                    );
                    body = Expr::apps(bool_and.clone(), [cmp, body]);
                }
                body
            } else {
                // Off-diagonal: distinct constructors are never equal.
                mk_bool_false()
            };

            // Wrap the inner-minor body in `cⱼ`'s `kⱼ` field binders.
            let mut inner_minor = inner_body;
            for (_fname, fty) in ctor_j.fields.iter().rev() {
                inner_minor = Expr::lam(BinderInfo::Default, fty.clone(), inner_minor);
            }
            inner = Expr::app(inner, inner_minor);
        }

        // Apply the inner recursor to its major `b` (= bvar(kᵢ) at this depth).
        inner = Expr::app(
            inner,
            Expr::bvar(u32::try_from(ki).expect("derive arity was checked to fit u32")),
        );

        // Wrap the outer-minor body (the inner dispatch) in `cᵢ`'s field binders.
        let mut outer_minor = inner;
        for (_fname, fty) in ctor_i.fields.iter().rev() {
            outer_minor = Expr::lam(BinderInfo::Default, fty.clone(), outer_minor);
        }
        outer = Expr::app(outer, outer_minor);
    }

    // Apply the outer recursor to its major `a` (= bvar 1 at body depth).
    outer = Expr::app(outer, Expr::bvar(1));

    Some(mk_binary_lam(&ind_ty, outer))
}

// ---------------------------------------------------------------------------
// DeriveHashable2
// ---------------------------------------------------------------------------

pub(crate) struct DeriveHashable2;

impl ExtDeriveHandler2 for DeriveHashable2 {
    fn class_name(&self) -> &str {
        "Hashable"
    }

    fn derive(
        &self,
        env: &Environment,
        tn: &Name,
        _te: &Expr,
        ctors: &[CtorInfo2],
        np: u32,
        _lp: &[Name],
    ) -> Result<Vec<DerivedDecl2>, DeriveError> {
        check_index_capacity(self.class_name(), tn, ctors, np)?;
        reject_recursive(ctors, "Hashable", tn)?;

        // Single-ctor struct shape (1 ctor, np == 0, >= 1 field, non-recursive):
        // `hash (C f0 .. fn) = Nat.add (.. Nat.add seed (Hashable.hash f0) ..)
        // (Hashable.hash fn)` where each field hash resolves the field type's own
        // `Hashable` instance from the environment and is projected via the struct
        // recursor. Closed and kernel-checkable; no proof obligation. If any field
        // instance is unresolvable the helper returns `None` and we try the
        // nullary-enum builder before failing closed.
        if let Some(value) = hashable_struct_value(env, tn, ctors, np) {
            return Ok(mk_single_inst("Hashable", tn, np, value));
        }

        // Multi-ctor-with-fields shape (>= 2 constructors, some/all carrying
        // fields, np == 0, non-recursive): a single `@T.rec` dispatch on the
        // value seeds each constructor's arm with its 0-based index (so distinct
        // constructors hash differently) then mixes per-field `Hashable.hash`
        // (resolving each field type's own `Hashable` instance) via the in-tree
        // `Nat.add` combiner. 0-field constructors hash to just the index. If any
        // field instance is unresolvable the helper returns `None` and we try
        // the nullary-enum builder before failing closed.
        if let Some(value) = hashable_multi_ctor_fields_value(env, tn, ctors, np) {
            return Ok(mk_single_inst("Hashable", tn, np, value));
        }

        // Try to synthesize a genuine, sorry-free `Hashable` instance for the
        // nullary-enum shape (>= 1 constructors, every constructor of arity 0,
        // no type parameters). The instance maps each constructor to a distinct
        // constant hash (its 0-based index) via the inductive recursor. Every
        // other shape fails closed below; a derivation request must not silently
        // degrade into either a fabricated value or a low-quality constant hash.
        match hashable_nullary_enum_value(tn, ctors, np) {
            Some(value) => Ok(mk_single_inst("Hashable", tn, np, value)),
            None => Err(DeriveError::Unsupported {
                class_name: "Hashable".to_owned(),
                ind_name: tn.to_string(),
                reason: "no structural Hashable construction is available for this shape"
                    .to_owned(),
            }),
        }
    }
}

/// Build the `Nat` literal `n` as a `Nat.succ`-chain over `Nat.zero`.
///
/// The in-tree `Hashable` class hashes into `Nat` (not `UInt64`), so each
/// per-constructor hash is a closed `Nat` peano numeral. Mirrors the
/// `Nat.zero` / `Nat.succ Nat.zero` construction used by the prelude
/// `Bool.hash` definition, keeping the term kernel-checkable with only the
/// `Nat` constructors (no literal/`OfNat` machinery, no axioms).
fn mk_nat_peano(n: usize) -> Expr {
    let mut acc = Expr::const_str("Nat.zero");
    let succ = Expr::const_str("Nat.succ");
    for _ in 0..n {
        acc = Expr::app(succ.clone(), acc);
    }
    acc
}

/// Try to build a sorry-free `Hashable` instance value for the nullary-enum
/// shape (`>= 1` constructors, every constructor of arity 0, no type
/// parameters).
///
/// The in-tree `Hashable` class (see `init_hashable`) carries
///
/// ```text
/// class Hashable (α : Type u) where
///   hash : α → Nat
/// ```
///
/// (Clean uses `Nat` rather than `UInt64` for hashes — there is no `UInt64`
/// hash field in the in-tree prelude.) For an inductive `E` with constructors
/// `c₀ … c_{n-1}`, all of arity 0 and no type parameters, `hash` maps each
/// constructor `cᵢ` to the distinct `Nat` peano numeral `i`:
///
/// ```text
/// @Hashable.mk E
///   (fun (x : E) => @E.rec.{1} (fun _ => Nat) 0 1 … (n-1) x)
/// ```
///
/// The dispatch is the inductive recursor `E.rec` instantiated at motive
/// universe `1` (`Nat : Type`), with the constant motive `fun _ => Nat` and one
/// minor premise per constructor (its 0-based index as a `Nat.succ`-chain). This
/// is a closed, kernel-checkable term that introduces no `sorryAx`/axioms — only
/// the type's own recursor and the `Nat` constructors. Distinct constructors
/// hash to distinct numerals, so the instance is a genuine (collision-free over
/// the nullary constructors) hash, not a constant stub.
///
/// Returns `None` for shapes outside this supported set (parametric inductives,
/// zero constructors, or any constructor with fields/recursion), so the caller
/// reports a typed unsupported-shape error.
fn hashable_nullary_enum_value(tn: &Name, ctors: &[CtorInfo2], np: u32) -> Option<Expr> {
    if np != 0 || ctors.is_empty() {
        return None;
    }
    if ctors.iter().any(|c| !c.fields.is_empty() || c.is_recursive) {
        return None;
    }

    // motive: fun (_ : E) => Nat  (a constant function into `Nat`).
    let ind_ty = Expr::const_(tn.clone(), vec![]);
    let motive = Expr::lam(BinderInfo::Default, ind_ty.clone(), mk_nat());

    // @E.rec.{1} motive <hash c₀> … <hash c_{n-1}> applied to the major.
    // `Nat : Type = Sort 1`, so the motive eliminates into `Sort 1`.
    let rec_const = Expr::const_(
        Name::from_string(&format!("{tn}.rec")),
        vec![Level::succ(Level::zero())],
    );
    let mut rec_app = Expr::app(rec_const, motive);
    for (i, _ctor) in ctors.iter().enumerate() {
        rec_app = Expr::app(rec_app, mk_nat_peano(i));
    }
    // The major premise is the single lambda-bound argument `x` (= bvar 0).
    rec_app = Expr::app(rec_app, Expr::bvar(0));

    // hash := fun (x : E) => <rec_app>.
    let hash_fn = Expr::lam(BinderInfo::Default, ind_ty.clone(), rec_app);

    // @Hashable.mk E hash. The `α` binder is implicit; the kernel accepts it
    // positionally, so we supply `E` explicitly (mirroring `DeriveRepr2`).
    Some(Expr::apps(
        Expr::const_str_levels("Hashable.mk", vec![Level::zero()]),
        [ind_ty, hash_fn],
    ))
}

/// Try to build a sorry-free `Hashable` instance value for the single-ctor
/// struct shape (1 constructor, `np == 0`, `>= 1` field, non-recursive).
///
/// The in-tree `Hashable` class (see `init_hashable`) carries `hash : α → Nat`,
/// so the instance value is `@Hashable.mk S (fun (x : S) => <body : Nat>)`. The
/// body combines each field's hash into a single `Nat` via the in-tree `Nat.add`
/// combiner, seeded with the constructor index (`0` for the sole constructor):
///
/// ```text
/// @Hashable.mk S
///   (fun (x : S) =>
///      Nat.add (… Nat.add 0 (@Hashable.hash F0 inst0 x.0) …)
///        (@Hashable.hash F_{n-1} inst_{n-1} x.{n-1}))
/// ```
///
/// where `x.i` is the struct recursor projection (see [`project_struct_field`])
/// and `insti` is the field type's own `Hashable` instance resolved from `env`.
/// The fold is left-nested and seeded with the `Nat` peano numeral of the
/// constructor index, so a single field collapses to
/// `Nat.add 0 (@Hashable.hash …)`. `Nat.mixHash` is not an in-tree kernel
/// constant, so the genuine combiner is `Nat.add`, which keeps the term
/// kernel-checkable using only the prelude `Nat.add` definition. Every field
/// type must resolve a monomorphic in-tree `Hashable` instance; otherwise this
/// returns `None` and the caller tries another genuine builder or fails closed.
fn hashable_struct_value(
    env: &Environment,
    tn: &Name,
    ctors: &[CtorInfo2],
    np: u32,
) -> Option<Expr> {
    let ctor = single_ctor_struct(ctors, np)?;
    // The struct lives in `Type 0 = Sort 1`; its data fields also live in
    // `Sort 1`, so the projecting recursor eliminates into `Sort 1`.
    let motive_level = Level::succ(Level::zero());
    let ind_ty = Expr::const_(tn.clone(), vec![]);

    // Resolve every field's Hashable instance up front; bail to the fallback if
    // any field type lacks a resolvable monomorphic instance.
    let mut field_insts = Vec::with_capacity(ctor.fields.len());
    for (_fname, fty) in &ctor.fields {
        field_insts.push(resolve_field_instance(env, "Hashable", fty)?);
    }

    // body: left-nested Nat.add of per-field hashes, seeded with the ctor index
    // (`0` for the sole constructor of a single-ctor struct). The single lambda
    // binds `x = bvar 0`.
    let nat_add = Expr::const_str("Nat.add");
    let mut body = mk_nat_peano(0);
    for (idx, (_fname, fty)) in ctor.fields.iter().enumerate() {
        let x_field =
            project_struct_field(tn, idx, fty, &ctor.fields, Expr::bvar(0), &motive_level);
        // @Hashable.hash Fi insti x.i : Nat (the projection accessor, no levels:
        // the supported field types live in `Type 0`).
        let field_hash = Expr::apps(
            Expr::const_str_levels("Hashable.hash", vec![Level::zero()]),
            [fty.clone(), field_insts[idx].clone(), x_field],
        );
        body = Expr::apps(nat_add.clone(), [body, field_hash]);
    }

    let hash_fn = Expr::lam(BinderInfo::Default, ind_ty.clone(), body);
    // @Hashable.mk S hash. The `α` binder is implicit; supply it explicitly.
    Some(Expr::apps(
        Expr::const_str_levels("Hashable.mk", vec![Level::zero()]),
        [ind_ty, hash_fn],
    ))
}

/// Try to build a sorry-free `Hashable` instance value for the
/// multi-ctor-with-fields shape (`>= 2` constructors, some/all carrying fields,
/// `np == 0`, non-recursive) — e.g. `Either A B`, `Result T E`, or a sum of
/// records.
///
/// This is the union of [`hashable_nullary_enum_value`]'s per-constructor index
/// dispatch and [`hashable_struct_value`]'s per-field `Nat.add` fold. The
/// instance value is `@Hashable.mk T (fun (x : T) => <body : Nat>)`, where a
/// single `@T.rec` dispatch on `x` selects the matched constructor's arm:
///
/// ```text
/// @Hashable.mk T
///   (fun (x : T) =>
///      @T.rec.{1} (fun _ => Nat)            -- constant motive (Nat)
///        <arm c_0> … <arm c_{n-1}>           -- one per ctor of `x`
///        x)
/// ```
///
/// where the arm for `cᵢ` binds `cᵢ`'s fields `(a₀ … a_{kᵢ-1})` and folds each
/// field's hash into a single `Nat` via `Nat.add`, seeded with the constructor
/// index `i` (as a `Nat` peano numeral) so distinct constructors hash
/// differently even when their fields agree:
///
/// ```text
///   fun (a₀ : Fᵢ₀) … (a_{kᵢ-1} : Fᵢ_{kᵢ-1}) =>
///     Nat.add (… Nat.add i (@Hashable.hash Fᵢ₀ instᵢ₀ a₀) …)
///       (@Hashable.hash Fᵢ_{kᵢ-1} instᵢ_{kᵢ-1} a_{kᵢ-1})
/// ```
///
/// A 0-field constructor hashes to just its index numeral `i`.
///
/// De Bruijn bookkeeping inside an arm for a `kᵢ`-field constructor: under the
/// `kᵢ` field binders, field `p` sits at `bvar(kᵢ-1-p)`. (The outer `x` binder
/// is not referenced inside the arm — the recursor already destructured `x`.)
///
/// `Nat.mixHash` is not an in-tree kernel constant, so the genuine combiner is
/// `Nat.add` (mirroring [`hashable_struct_value`]), which keeps the term
/// kernel-checkable using only the prelude `Nat.add` definition. Every field
/// type appearing on any constructor must resolve a monomorphic in-tree
/// `Hashable` instance up front (via [`resolve_field_instance`]); if any is
/// unresolvable, or the shape is outside this set (single ctor, parametric,
/// recursive, all-nullary), this returns `None` and the caller tries another
/// genuine builder or fails closed. The whole term is closed and kernel-checkable; it
/// introduces no `sorryAx`/axioms — only the type's own recursor, `Hashable.hash`,
/// `Nat.add`, and the `Nat` constructors.
fn hashable_multi_ctor_fields_value(
    env: &Environment,
    tn: &Name,
    ctors: &[CtorInfo2],
    np: u32,
) -> Option<Expr> {
    if !multi_ctor_fields_shape(ctors, np) {
        return None;
    }

    // Resolve every field's Hashable instance up front (across all
    // constructors); bail to the fallback if any field type lacks a resolvable
    // monomorphic instance. Stored per-constructor, indexed by field position.
    let mut ctor_field_insts: Vec<Vec<Expr>> = Vec::with_capacity(ctors.len());
    for ctor in ctors {
        let mut insts = Vec::with_capacity(ctor.fields.len());
        for (_fname, fty) in &ctor.fields {
            insts.push(resolve_field_instance(env, "Hashable", fty)?);
        }
        ctor_field_insts.push(insts);
    }

    let ind_ty = Expr::const_(tn.clone(), vec![]);
    // `T : Type 0 = Sort 1`, so the recursor eliminates into `Nat : Sort 1`.
    let motive_level = Level::succ(Level::zero());
    let rec_name = Name::from_string(&format!("{tn}.rec"));
    let nat_add = Expr::const_str("Nat.add");

    // Constant motive `fun (_ : T) => Nat` — the result type never depends on the
    // scrutinee, so the recursor's major-premise argument is ignored.
    let motive = Expr::lam(BinderInfo::Default, ind_ty.clone(), mk_nat());

    let rec_const = Expr::const_(rec_name, vec![motive_level.clone()]);
    let mut rec_app = Expr::app(rec_const, motive);

    for (i, ctor_i) in ctors.iter().enumerate() {
        let ki = ctor_i.fields.len();

        // Seed with the ctor index `i` (distinct per ctor) then left-fold the
        // per-field hashes via Nat.add. Under the `kᵢ` field binders field `p`
        // is `bvar(kᵢ-1-p)`.
        let mut body = mk_nat_peano(i);
        for (p, (_fname, fty)) in ctor_i.fields.iter().enumerate() {
            let a_field =
                Expr::bvar(u32::try_from(ki - 1 - p).expect("derive arity was checked to fit u32"));
            // @Hashable.hash Fᵢ_p instᵢ_p a_p : Nat (no levels: the supported
            // field types live in `Type 0`).
            let field_hash = Expr::apps(
                Expr::const_str_levels("Hashable.hash", vec![Level::zero()]),
                [fty.clone(), ctor_field_insts[i][p].clone(), a_field],
            );
            body = Expr::apps(nat_add.clone(), [body, field_hash]);
        }

        // Wrap the arm body in `cᵢ`'s `kᵢ` field binders.
        let mut arm = body;
        for (_fname, fty) in ctor_i.fields.iter().rev() {
            arm = Expr::lam(BinderInfo::Default, fty.clone(), arm);
        }
        rec_app = Expr::app(rec_app, arm);
    }

    // Apply the recursor to its major `x` (= bvar 0 under the single `hash`
    // binder).
    rec_app = Expr::app(rec_app, Expr::bvar(0));

    let hash_fn = Expr::lam(BinderInfo::Default, ind_ty.clone(), rec_app);
    // @Hashable.mk T hash. The `α` binder is implicit; supply it explicitly.
    Some(Expr::apps(
        Expr::const_str_levels("Hashable.mk", vec![Level::zero()]),
        [ind_ty, hash_fn],
    ))
}

// ---------------------------------------------------------------------------
// DeriveRepr2
// ---------------------------------------------------------------------------

pub(crate) struct DeriveRepr2;

impl ExtDeriveHandler2 for DeriveRepr2 {
    fn class_name(&self) -> &str {
        "Repr"
    }

    fn derive(
        &self,
        env: &Environment,
        tn: &Name,
        _te: &Expr,
        ctors: &[CtorInfo2],
        np: u32,
        _lp: &[Name],
    ) -> Result<Vec<DerivedDecl2>, DeriveError> {
        check_index_capacity(self.class_name(), tn, ctors, np)?;
        // Single-ctor struct shape (1 ctor, np == 0, >= 1 field, non-recursive):
        // render `CtorName { f1 := <repr a.f1>, … }` via the struct recursor,
        // resolving each field type's own `Repr` instance from the environment.
        // If any field instance is unresolvable the helper returns `None` and we
        // try the nullary-enum builder before failing closed.
        if let Some(value) = repr_struct_value(env, tn, ctors, np) {
            return Ok(mk_single_inst("Repr", tn, np, value));
        }

        // Multi-ctor-with-fields shape (>= 2 constructors, some/all carrying
        // fields, np == 0, non-recursive): a single `@T.rec` dispatch on the
        // value renders the matched constructor's name followed by its
        // space-separated per-field `reprPrec` renderings (resolving each field
        // type's own `Repr` instance). 0-field constructors render just the
        // constructor name. If any field instance is unresolvable the helper
        // returns `None` and we try the nullary-enum builder before failing closed.
        if let Some(value) = repr_multi_ctor_fields_value(env, tn, ctors, np) {
            return Ok(mk_single_inst("Repr", tn, np, value));
        }

        // Try to synthesize a genuine, sorry-free `Repr` instance for the
        // nullary-enum shape (>= 1 constructors, every constructor of arity 0,
        // no type parameters). The instance renders each constructor name via
        // the inductive recursor. A constant type-name fallback is well typed
        // but is not an implementation of structural deriving because it loses
        // constructor and field information, so unsupported shapes fail closed.
        match repr_nullary_enum_value(tn, ctors, np) {
            Some(value) => Ok(mk_single_inst("Repr", tn, np, value)),
            None => Err(DeriveError::Unsupported {
                class_name: "Repr".to_owned(),
                ind_name: tn.to_string(),
                reason: "no structural Repr construction is available for this shape".to_owned(),
            }),
        }
    }
}

/// Try to build a sorry-free `Repr` instance value for the nullary-enum shape.
///
/// The in-tree `Repr` class (matching the sibling `DeriveRepr` handler in
/// `derive_handlers`) carries
///
/// ```text
/// class Repr (α : Type u) where
///   reprPrec : α → Nat → String
/// ```
///
/// For an inductive `E` with constructors `c₁ … cₙ`, all of arity 0 and no type
/// parameters, `reprPrec` ignores the `Nat` precedence argument and maps each
/// constructor `cᵢ` to the string literal `"cᵢ"` (its rendered name):
///
/// ```text
/// @Repr.mk E
///   (fun (x : E) => fun (_ : Nat) => @E.rec.{1} (fun _ => String) "c₁" … "cₙ" x)
/// ```
///
/// The dispatch is the inductive recursor `E.rec` instantiated at motive
/// universe `1` (`String : Type`), with the constant motive `fun _ => String`
/// and one minor premise per constructor (the constructor-name literal). This is
/// a closed, kernel-checkable term that introduces no `sorryAx`/axioms.
///
/// Returns `None` for shapes outside this supported set (parametric inductives,
/// zero constructors, or any constructor with fields/recursion), so the caller
/// fails closed with `Unsupported`.
fn repr_nullary_enum_value(tn: &Name, ctors: &[CtorInfo2], np: u32) -> Option<Expr> {
    if np != 0 || ctors.is_empty() {
        return None;
    }
    if ctors.iter().any(|c| !c.fields.is_empty() || c.is_recursive) {
        return None;
    }

    // motive: fun (_ : E) => String  (a constant function into `String`).
    let ind_ty = Expr::const_(tn.clone(), vec![]);
    let motive = Expr::lam(
        BinderInfo::Default,
        ind_ty.clone(),
        Expr::const_str("String"),
    );

    // @E.rec.{1} motive <minor c₁> … <minor cₙ> applied to the major.
    // `String : Type = Sort 1`, so the motive eliminates into `Sort 1`.
    let rec_const = Expr::const_(
        Name::from_string(&format!("{tn}.rec")),
        vec![Level::succ(Level::zero())],
    );
    let mut rec_app = Expr::app(rec_const, motive);
    for ctor in ctors {
        rec_app = Expr::app(rec_app, mk_str_lit(&ctor.name.to_string()));
    }
    // The major premise is the first lambda-bound argument `x`. Under the inner
    // `Nat` precedence binder it is `bvar 1` (the precedence arg is `bvar 0`).
    rec_app = Expr::app(rec_app, Expr::bvar(1));

    // reprPrec := fun (x : E) => fun (_ : Nat) => <rec_app>, ignoring precedence.
    let repr_fn = Expr::lam(
        BinderInfo::Default,
        ind_ty.clone(),
        Expr::lam(BinderInfo::Default, mk_nat(), rec_app),
    );

    // @Repr.mk E reprPrec. The `α` binder is implicit; the kernel accepts it
    // positionally, so we supply `E` explicitly (mirroring `DeriveToExpr`).
    Some(Expr::apps(
        Expr::const_str_levels("Repr.mk", vec![Level::zero()]),
        [ind_ty, repr_fn],
    ))
}

/// Extract the `reprPrec` function (`Fi → Nat → String`) out of a `Repr Fi`
/// instance term via the `Repr` structure recursor.
///
/// `Repr` is the single-ctor structure `Repr.mk : {α} → (α → Nat → String) →
/// Repr α`, so
///
/// ```text
/// @Repr.rec.{1} Fi (fun (_ : Repr Fi) => Fi → Nat → String)
///   (fun (f : Fi → Nat → String) => f)
///   inst
///   : Fi → Nat → String
/// ```
///
/// The motive eliminates into `Fi → Nat → String : Sort 1` (its data fields all
/// live in `Type`), so the recursor motive universe is `1`. The result is a
/// closed term that reuses the field instance and introduces no axioms.
fn repr_prec_of(field_ty: &Expr, inst: &Expr) -> Expr {
    let repr_fi = Expr::app(
        Expr::const_str_levels("Repr", vec![Level::zero()]),
        field_ty.clone(),
    );
    let fn_ty = Expr::pi(
        BinderInfo::Default,
        field_ty.clone(),
        Expr::pi(BinderInfo::Default, mk_nat(), Expr::const_str("String")),
    );
    // motive: fun (_ : Repr Fi) => Fi → Nat → String.
    let motive = Expr::lam(BinderInfo::Default, repr_fi, fn_ty.clone());
    // minor: fun (f : Fi → Nat → String) => f.
    let minor = Expr::lam(BinderInfo::Default, fn_ty, Expr::bvar(0));
    // The prelude `Repr.{u}` is universe-polymorphic, so its auto-generated
    // recursor `Repr.rec.{v, u}` takes TWO levels: the motive elimination
    // universe `v` and the inductive parameter universe `u`. The motive
    // eliminates into `Fi → Nat → String : Sort 1` (v = 1) and the supported
    // field types live in `Type 0` (u = 0).
    let rec_const = Expr::const_(
        Name::from_string("Repr.rec"),
        vec![Level::succ(Level::zero()), Level::zero()],
    );
    Expr::apps(rec_const, [field_ty.clone(), motive, minor, inst.clone()])
}

/// Append a sequence of `String` expressions left-to-right via `String.append`,
/// seeded with the empty-string literal.
fn append_strings(parts: impl IntoIterator<Item = Expr>) -> Expr {
    let append = Expr::const_str("String.append");
    let mut acc = mk_str_lit("");
    for part in parts {
        acc = Expr::apps(append.clone(), [acc, part]);
    }
    acc
}

/// Try to build a sorry-free `Repr` instance value for the single-ctor struct
/// shape (1 constructor, `np == 0`, `>= 1` field, non-recursive).
///
/// `reprPrec` ignores the `Nat` precedence and renders
/// `CtorName { f0 := <repr a.f0>, f1 := <repr a.f1>, … }`, where each
/// `<repr a.fi>` is the field type's own `reprPrec` (extracted from its resolved
/// `Repr` instance via [`repr_prec_of`]) applied to the recursor projection of
/// field `i` at precedence `0`:
///
/// ```text
/// @Repr.mk S
///   (fun (x : S) (_ : Nat) =>
///      "CtorName { " ++ "f0 := " ++ <reprPrec_F0 x.0 0>
///        ++ ", f1 := " ++ <reprPrec_F1 x.1 0> ++ … ++ " }")
/// ```
///
/// Every field type must resolve a monomorphic in-tree `Repr` instance;
/// otherwise this returns `None` and the caller keeps the honest constant
/// fallback. The whole term is closed and kernel-checkable (only the struct's
/// recursor, the field instances' recursors, `String.append`, and `String`
/// literals).
fn repr_struct_value(env: &Environment, tn: &Name, ctors: &[CtorInfo2], np: u32) -> Option<Expr> {
    let ctor = single_ctor_struct(ctors, np)?;
    // The struct lives in `Type 0 = Sort 1`; its data fields also live in
    // `Sort 1`, so the projecting recursor eliminates into `Sort 1`.
    let motive_level = Level::succ(Level::zero());
    let ind_ty = Expr::const_(tn.clone(), vec![]);

    // Resolve every field's Repr instance up front; bail to the fallback if any
    // field type lacks a resolvable monomorphic instance.
    let mut field_insts = Vec::with_capacity(ctor.fields.len());
    for (_fname, fty) in &ctor.fields {
        field_insts.push(resolve_field_instance(env, "Repr", fty)?);
    }

    // Render parts. Under the two reprPrec binders `(x : S) (_ : Nat)`, the
    // struct value `x` is `bvar 1` (precedence is `bvar 0`).
    let mut parts: Vec<Expr> = vec![mk_str_lit(&format!("{} {{ ", ctor.name))];
    for (idx, (fname, fty)) in ctor.fields.iter().enumerate() {
        if idx > 0 {
            parts.push(mk_str_lit(", "));
        }
        parts.push(mk_str_lit(&format!("{fname} := ")));
        // a.i via the struct recursor (major is `x = bvar 1`).
        let projected =
            project_struct_field(tn, idx, fty, &ctor.fields, Expr::bvar(1), &motive_level);
        // <reprPrec_Fi> a.i 0  : String.
        let field_prec = repr_prec_of(fty, &field_insts[idx]);
        let rendered = Expr::apps(field_prec, [projected, mk_nat_peano(0)]);
        parts.push(rendered);
    }
    parts.push(mk_str_lit(" }"));

    let rendered = append_strings(parts);
    // reprPrec := fun (x : S) (_ : Nat) => <rendered>.
    let repr_fn = Expr::lam(
        BinderInfo::Default,
        ind_ty.clone(),
        Expr::lam(BinderInfo::Default, mk_nat(), rendered),
    );
    Some(Expr::apps(
        Expr::const_str_levels("Repr.mk", vec![Level::zero()]),
        [ind_ty, repr_fn],
    ))
}

/// Try to build a sorry-free `Repr` instance value for the multi-ctor-with-fields
/// shape (`>= 2` constructors, some/all carrying fields, `np == 0`,
/// non-recursive) — e.g. `Either A B`, `Result T E`, or a sum of records.
///
/// This is the union of [`repr_nullary_enum_value`]'s per-constructor dispatch
/// and [`repr_struct_value`]'s field rendering. The `reprPrec` ignores the `Nat`
/// precedence and a single `@T.rec` dispatch on the value selects the matched
/// constructor's arm:
///
/// ```text
/// @Repr.mk T
///   (fun (x : T) (_ : Nat) =>
///      @T.rec.{1} (fun _ => String)        -- constant motive (String)
///        <arm c_0> … <arm c_{n-1}>          -- one per ctor of `x`
///        x)
/// ```
///
/// where the arm for `cᵢ` binds `cᵢ`'s fields `(a₀ … a_{kᵢ-1})` and renders
/// the constructor name followed by each field's `reprPrec` at precedence `0`,
/// space-separated:
///
/// ```text
///   fun (a₀ : Fᵢ₀) … (a_{kᵢ-1} : Fᵢ_{kᵢ-1}) =>
///     "cᵢ" ++ " " ++ <reprPrec_Fᵢ₀ a₀ 0> ++ " " ++ … ++ <reprPrec a_{kᵢ-1} 0>
/// ```
///
/// A 0-field constructor renders just the literal `"cᵢ"`.
///
/// De Bruijn bookkeeping inside an arm for a `kᵢ`-field constructor: under the
/// `kᵢ` field binders, field `p` sits at `bvar(kᵢ-1-p)`. (The outer `x`/`_`
/// `reprPrec` binders are not referenced inside the arm — the recursor already
/// destructured `x`.)
///
/// Every field type appearing on any constructor must resolve a monomorphic
/// in-tree `Repr` instance up front (via [`resolve_field_instance`]); if any is
/// unresolvable, or the shape is outside this set (single ctor, parametric,
/// recursive, all-nullary), this returns `None` and the caller tries another
/// genuine builder or fails closed. The whole term is closed and kernel-checkable; it
/// introduces no `sorryAx`/axioms — only the type's own recursor, the field
/// instances' recursors, `String.append`, and `String` literals.
fn repr_multi_ctor_fields_value(
    env: &Environment,
    tn: &Name,
    ctors: &[CtorInfo2],
    np: u32,
) -> Option<Expr> {
    if !multi_ctor_fields_shape(ctors, np) {
        return None;
    }

    // Resolve every field's Repr instance up front (across all constructors);
    // fail this genuine builder if any field type lacks a resolvable
    // monomorphic instance. Stored per-constructor, indexed by field position.
    let mut ctor_field_insts: Vec<Vec<Expr>> = Vec::with_capacity(ctors.len());
    for ctor in ctors {
        let mut insts = Vec::with_capacity(ctor.fields.len());
        for (_fname, fty) in &ctor.fields {
            insts.push(resolve_field_instance(env, "Repr", fty)?);
        }
        ctor_field_insts.push(insts);
    }

    let ind_ty = Expr::const_(tn.clone(), vec![]);
    // `T : Type 0 = Sort 1`, so the recursor eliminates into `String : Sort 1`.
    let motive_level = Level::succ(Level::zero());
    let rec_name = Name::from_string(&format!("{tn}.rec"));

    // Constant motive `fun (_ : T) => String` — the result type never depends on
    // the scrutinee, so the recursor's major-premise argument is ignored.
    let motive = Expr::lam(
        BinderInfo::Default,
        ind_ty.clone(),
        Expr::const_str("String"),
    );

    let rec_const = Expr::const_(rec_name, vec![motive_level.clone()]);
    let mut rec_app = Expr::app(rec_const, motive);

    for (i, ctor_i) in ctors.iter().enumerate() {
        let ki = ctor_i.fields.len();

        // Render the constructor name, then each field at precedence 0. Under the
        // `kᵢ` field binders field `p` is `bvar(kᵢ-1-p)`.
        let mut parts: Vec<Expr> = vec![mk_str_lit(&ctor_i.name.to_string())];
        for (p, (_fname, fty)) in ctor_i.fields.iter().enumerate() {
            parts.push(mk_str_lit(" "));
            let a_field =
                Expr::bvar(u32::try_from(ki - 1 - p).expect("derive arity was checked to fit u32"));
            // <reprPrec_Fᵢ_p> a_p 0 : String.
            let field_prec = repr_prec_of(fty, &ctor_field_insts[i][p]);
            let rendered = Expr::apps(field_prec, [a_field, mk_nat_peano(0)]);
            parts.push(rendered);
        }
        let arm_body = append_strings(parts);

        // Wrap the arm body in `cᵢ`'s `kᵢ` field binders.
        let mut arm = arm_body;
        for (_fname, fty) in ctor_i.fields.iter().rev() {
            arm = Expr::lam(BinderInfo::Default, fty.clone(), arm);
        }
        rec_app = Expr::app(rec_app, arm);
    }

    // Apply the recursor to its major `x`. Under the two `reprPrec` binders
    // `(x : T) (_ : Nat)` the value `x` is `bvar 1` (precedence is `bvar 0`).
    rec_app = Expr::app(rec_app, Expr::bvar(1));

    // reprPrec := fun (x : T) (_ : Nat) => <rec_app>, ignoring precedence.
    let repr_fn = Expr::lam(
        BinderInfo::Default,
        ind_ty.clone(),
        Expr::lam(BinderInfo::Default, mk_nat(), rec_app),
    );
    Some(Expr::apps(
        Expr::const_str_levels("Repr.mk", vec![Level::zero()]),
        [ind_ty, repr_fn],
    ))
}

// ---------------------------------------------------------------------------
// DeriveOrd2
// ---------------------------------------------------------------------------

pub(crate) struct DeriveOrd2;

impl ExtDeriveHandler2 for DeriveOrd2 {
    fn class_name(&self) -> &str {
        "Ord"
    }

    fn derive(
        &self,
        _env: &Environment,
        tn: &Name,
        _te: &Expr,
        ctors: &[CtorInfo2],
        np: u32,
        lp: &[Name],
    ) -> Result<Vec<DerivedDecl2>, DeriveError> {
        check_index_capacity(self.class_name(), tn, ctors, np)?;
        reject_recursive(ctors, "Ord", tn)?;
        if np != 0 || !lp.is_empty() || !ctors.is_empty() {
            return Err(DeriveError::Unsupported {
                class_name: "Ord".to_owned(),
                ind_name: tn.to_string(),
                reason: "only a monomorphic empty type has a complete Ord construction".to_owned(),
            });
        }
        let ind_ty = Expr::const_(tn.clone(), vec![]);
        // There are no values to compare, so any closed Ordering result is
        // extensionally exact for the empty domain.
        let cmp = Expr::const_(Name::from_string("Ordering.eq"), vec![]);
        let cmp_fn = mk_binary_lam(&ind_ty, cmp);
        let type_ = Expr::app(
            Expr::const_str_levels("Ord", vec![Level::zero()]),
            ind_ty.clone(),
        );
        let value = Expr::apps(
            Expr::const_str_levels("Ord.mk", vec![Level::zero()]),
            [ind_ty, cmp_fn],
        );
        Ok(vec![DerivedDecl2 {
            name: inst_name("Ord", tn),
            type_,
            value,
            is_instance: true,
        }])
    }
}

// ---------------------------------------------------------------------------
// DeriveDecidableEq2
// ---------------------------------------------------------------------------

pub(crate) struct DeriveDecidableEq2;

impl ExtDeriveHandler2 for DeriveDecidableEq2 {
    fn class_name(&self) -> &str {
        "DecidableEq"
    }

    fn derive(
        &self,
        env: &Environment,
        tn: &Name,
        te: &Expr,
        ctors: &[CtorInfo2],
        np: u32,
        lp: &[Name],
    ) -> Result<Vec<DerivedDecl2>, DeriveError> {
        check_index_capacity(self.class_name(), tn, ctors, np)?;
        reject_recursive(ctors, "DecidableEq", tn)?;
        // Build ind type with proper universe levels from level_params.
        let levels: Vec<Level> = lp.iter().map(|n| Level::param(n.clone())).collect();
        let ind_base = Expr::const_(tn.clone(), levels);
        let ind_ty = if np == 0 {
            ind_base
        } else {
            let args: Vec<Expr> = (0..np).rev().map(Expr::bvar).collect();
            Expr::apps(ind_base, args)
        };
        // Universe level for Eq.{u} and DecidableEq.{u}.
        let u_level = extract_universe_level(te);

        // Single-ctor struct shape (1 ctor, np == 0, >= 1 field, non-recursive):
        // decide each field via its own `DecidableEq` instance and compose. Equal
        // fields prove `a = b` by congruence over the constructor (closed by the
        // kernel's structure-eta), and a differing field disproves `a = b` by
        // lifting the field disequality through the field projection (`congrArg`).
        // Closed and kernel-checkable; no `sorry`. If any field instance is
        // unresolvable the helper returns `None` and we fall through to the
        // multi-ctor / nullary-enum paths, then fail closed below.
        //
        // Multi-ctor-with-fields shape (>= 2 ctors, np == 0, non-recursive,
        // >= 1 field-carrying): the union of the nullary-enum per-ctor dispatch
        // and the single-ctor-struct field composition. The nested outer/inner
        // recursor dispatch selects the constructor pair; the diagonal decides
        // each field via its `DecidableEq` instance (isTrue via the constructor
        // congruence chain, isFalse via same-ctor `noConfusion` injection), and
        // every off-diagonal pair is `Decidable.isFalse` via cross-ctor
        // `noConfusion`. Every field type must resolve a monomorphic in-tree
        // `DecidableEq` instance, else the helper returns `None`.
        let Some(deceq_fn) = decidable_eq_struct_value(env, tn, ctors, np, &u_level)
            .or_else(|| decidable_eq_multi_ctor_fields_value(env, tn, ctors, np, &u_level))
            .or_else(|| decidable_eq_nullary_enum_value(tn, ctors, np, &u_level))
        else {
            return Err(DeriveError::Unsupported {
                class_name: "DecidableEq".to_owned(),
                ind_name: tn.to_string(),
                reason: "no proof-producing DecidableEq construction is available for this shape"
                    .to_owned(),
            });
        };
        let inst_ty = Expr::app(Expr::const_str_levels("DecidableEq", vec![u_level]), ind_ty);
        let (value, type_) = wrap_params(deceq_fn, inst_ty, np);
        Ok(vec![DerivedDecl2 {
            name: inst_name("DecidableEq", tn),
            type_,
            value,
            is_instance: true,
        }])
    }
}

/// Try to build a sorry-free `DecidableEq` instance value for the nullary-enum
/// shape (`>= 1` constructors, every constructor of arity 0, no type
/// parameters). Returns the instance value `(a b : E) -> Decidable (a = b)`, or
/// `None` for shapes outside this supported set (parametric inductives, zero
/// constructors, or any constructor with fields/recursion), so the caller
/// reports a typed unsupported-shape error.
///
/// `DecidableEq E` is the reducible def `(a b : E) -> Decidable (@Eq E a b)`,
/// so the instance value is a binary lambda whose body has type
/// `Decidable (@Eq E a b)` with `a = bvar 1`, `b = bvar 0`.
///
/// The body is a nested recursor dispatch. The outer recursor splits on `a`,
/// the inner on `b`:
///
/// ```text
/// fun (a b : E) =>
///   @E.rec.{1} (fun a' => Decidable (@Eq E a' b))      -- outer motive (b captured)
///     <minor_a c_0> ... <minor_a c_{n-1}>              -- one per ctor of `a`
///     a
/// ```
///
/// where each outer minor (for `a = cᵢ`) re-dispatches on `b`:
///
/// ```text
///   @E.rec.{1} (fun b' => Decidable (@Eq E cᵢ b'))     -- inner motive
///     <minor_b c_0> ... <minor_b c_{n-1}>              -- one per ctor of `b`
///     b
/// ```
///
/// and each inner minor (for `b = cⱼ`) is:
/// * `i == j` (diagonal):   `@Decidable.isTrue (@Eq E cᵢ cᵢ) (@Eq.refl.{u} E cᵢ)`
/// * `i != j` (off-diag):   `@Decidable.isFalse (@Eq E cᵢ cⱼ)
///                               (fun h => @E.noConfusion.{0} False cᵢ cⱼ h)`
///
/// For distinct constructors `@E.noConfusionType False cᵢ cⱼ` reduces to
/// `False`, so `@E.noConfusion.{0} False cᵢ cⱼ h : False`, giving the negation
/// `(cᵢ = cⱼ) -> False` that `Decidable.isFalse` demands. The whole term is
/// closed (apart from the lambda-bound `a`, `b`, `h`) and kernel-checkable; it
/// introduces no `sorryAx`/axioms — only the type's own recursor, `noConfusion`,
/// `Eq.refl`, and the `Decidable` constructors.
pub(crate) fn decidable_eq_nullary_enum_value(
    tn: &Name,
    ctors: &[CtorInfo2],
    np: u32,
    u_level: &Level,
) -> Option<Expr> {
    if np != 0 || ctors.is_empty() {
        return None;
    }
    if ctors.iter().any(|c| !c.fields.is_empty() || c.is_recursive) {
        return None;
    }

    let ind_ty = Expr::const_(tn.clone(), vec![]);
    let false_expr = Expr::const_str("False");
    // `E : Type 0 = Sort 1`, so the recursor eliminates into `Decidable _ : Sort 1`.
    let motive_level = Level::succ(Level::zero());
    let rec_name = Name::from_string(&format!("{tn}.rec"));
    let nc_name = Name::from_string(&format!("{tn}.noConfusion"));
    // noConfusion's only level param is the motive universe; the motive is
    // `False : Prop = Sort 0`, so it is instantiated at level 0.
    let nc_levels = vec![Level::zero()];

    // Helper: `@Decidable (@Eq.{u} E lhs rhs)`.
    let decidable_eq_of = |lhs: &Expr, rhs: &Expr| {
        Expr::app(
            Expr::const_str("Decidable"),
            Expr::apps(
                Expr::const_str_levels("Eq", vec![u_level.clone()]),
                [ind_ty.clone(), lhs.clone(), rhs.clone()],
            ),
        )
    };

    // Outer motive: `fun (a' : E) => Decidable (@Eq E a' b)`.
    // Inside the lambda `a' = bvar 0`; the outer `b` binder is pushed to `bvar 1`.
    let outer_motive = Expr::lam(
        BinderInfo::Default,
        ind_ty.clone(),
        decidable_eq_of(&Expr::bvar(0), &Expr::bvar(1)),
    );

    // Outer recursor: dispatch on `a` (= bvar 1 at body depth).
    let outer_rec = Expr::const_(rec_name.clone(), vec![motive_level.clone()]);
    let mut outer = Expr::app(outer_rec, outer_motive);

    for ctor_i in ctors {
        let ci = Expr::const_(ctor_i.name.clone(), vec![]);

        // Inner motive: `fun (b' : E) => Decidable (@Eq E cᵢ b')`.
        // Inside the lambda `b' = bvar 0`; `cᵢ` is a closed const.
        let inner_motive = Expr::lam(
            BinderInfo::Default,
            ind_ty.clone(),
            decidable_eq_of(&ci, &Expr::bvar(0)),
        );

        let inner_rec = Expr::const_(rec_name.clone(), vec![motive_level.clone()]);
        let mut inner = Expr::app(inner_rec, inner_motive);

        for ctor_j in ctors {
            let cj = Expr::const_(ctor_j.name.clone(), vec![]);
            let inner_minor = if ctor_i.name == ctor_j.name {
                // Diagonal: `@Decidable.isTrue (@Eq E cᵢ cᵢ) (@Eq.refl.{u} E cᵢ)`.
                let eq_ci_ci = Expr::apps(
                    Expr::const_str_levels("Eq", vec![u_level.clone()]),
                    [ind_ty.clone(), ci.clone(), ci.clone()],
                );
                let refl = Expr::apps(
                    Expr::const_str_levels("Eq.refl", vec![u_level.clone()]),
                    [ind_ty.clone(), ci.clone()],
                );
                Expr::apps(Expr::const_str("Decidable.isTrue"), [eq_ci_ci, refl])
            } else {
                // Off-diagonal: `@Decidable.isFalse (@Eq E cᵢ cⱼ) <not-eq>` where
                // `<not-eq> = fun (h : @Eq E cᵢ cⱼ) => @E.noConfusion.{0} False cᵢ cⱼ h`.
                let eq_ci_cj = Expr::apps(
                    Expr::const_str_levels("Eq", vec![u_level.clone()]),
                    [ind_ty.clone(), ci.clone(), cj.clone()],
                );
                // @E.noConfusion.{0} False cᵢ cⱼ (bvar 0).
                let nc_app = Expr::apps(
                    Expr::const_(nc_name.clone(), nc_levels.clone()),
                    [false_expr.clone(), ci.clone(), cj.clone(), Expr::bvar(0)],
                );
                let not_eq = Expr::lam(BinderInfo::Default, eq_ci_cj.clone(), nc_app);
                Expr::apps(Expr::const_str("Decidable.isFalse"), [eq_ci_cj, not_eq])
            };
            inner = Expr::app(inner, inner_minor);
        }

        // Apply the inner recursor to its major `b` (= bvar 0 at this depth).
        inner = Expr::app(inner, Expr::bvar(0));
        outer = Expr::app(outer, inner);
    }

    // Apply the outer recursor to its major `a` (= bvar 1 at body depth).
    outer = Expr::app(outer, Expr::bvar(1));

    Some(mk_binary_lam(&ind_ty, outer))
}

/// Try to build a sorry-free `DecidableEq` instance value for the single-ctor
/// struct shape (1 constructor, `np == 0`, `>= 1` field, non-recursive).
///
/// `DecidableEq S` is the reducible def `(a b : S) -> Decidable (@Eq S a b)`, so
/// the instance value is a binary lambda `fun (a b : S) => <body>` whose body has
/// type `Decidable (@Eq S a b)` with `a = bvar 1`, `b = bvar 0` at body depth.
///
/// Each field `fk : Fk` is decided via its own resolved `DecidableEq Fk` instance
/// applied to the projections `a.k`, `b.k` (`instk a.k b.k : Decidable (a.k =
/// b.k)`), then dispatched with `@Decidable.rec.{1}` under a *constant* motive
/// `fun _ => Decidable (@Eq S a b)`:
///
/// ```text
/// fun (a b : S) =>
///   @Decidable.rec.{1} (@Eq Fk a.0 b.0) (fun _ => Decidable (@Eq S a b))
///     (fun (h0 : ¬(a.0 = b.0)) => isFalse … )      -- field 0 differs
///     (fun (h0 :   a.0 = b.0 ) => <dispatch field 1, capturing h0>)
///     (inst0 a.0 b.0)
/// ```
///
/// * **Off-diagonal (some field differs).** From `hk : ¬(a.k = b.k)`, build
///   `isFalse (@Eq S a b) (fun (heq : @Eq S a b) => hk (@congrArg.{1,1} S Fk a b
///   projk heq))`, where `projk = fun (s : S) => s.k` is the field projection.
///   `congrArg` lifts `a = b` to `a.k = b.k`, contradicting `hk`.
/// * **Diagonal (all fields equal).** With every `hk : a.k = b.k` in scope, build
///   `isTrue (@Eq S a b) <proof>` where `<proof> : @Eq S (S.mk a.0 … a.{n-1})
///   (S.mk b.0 … b.{n-1})` is a left-to-right `Eq.trans` chain of `congrArg`
///   steps (rewriting one field at a time). The kernel's structure-eta makes
///   `S.mk a.0 … ≡ a` and `S.mk b.0 … ≡ b`, so this term checks at the demanded
///   type `@Eq S a b`.
///
/// The whole term is closed (apart from the lambda-bound `a`, `b`, `hk`, `heq`)
/// and kernel-checkable; it introduces no `sorryAx`/axioms — only the struct's
/// recursor, each field's `DecidableEq` instance, `congrArg`, `Eq.trans`, and the
/// `Decidable` constructors. Every field type must resolve a monomorphic in-tree
/// `DecidableEq` instance; otherwise this returns `None` and the caller tries
/// another genuine builder or fails closed with `Unsupported`.
pub(crate) fn decidable_eq_struct_value(
    env: &Environment,
    tn: &Name,
    ctors: &[CtorInfo2],
    np: u32,
    u_level: &Level,
) -> Option<Expr> {
    let ctor = single_ctor_struct(ctors, np)?;
    let fields = &ctor.fields;
    let n = fields.len();

    // Resolve every field's DecidableEq instance up front; bail to the fallback
    // if any field type lacks a resolvable monomorphic instance.
    let mut field_insts = Vec::with_capacity(n);
    for (_fname, fty) in fields {
        field_insts.push(resolve_field_instance(env, "DecidableEq", fty)?);
    }

    let ind_ty = Expr::const_(tn.clone(), vec![]);
    let ctor_const = Expr::const_(ctor.name.clone(), vec![]);

    // `@Eq.{u} S lhs rhs`.
    let eq_s = |lhs: Expr, rhs: Expr| {
        Expr::apps(
            Expr::const_str_levels("Eq", vec![u_level.clone()]),
            [ind_ty.clone(), lhs, rhs],
        )
    };
    // `Decidable (@Eq S lhs rhs)`.
    let decidable_eq_s =
        |lhs: Expr, rhs: Expr| Expr::app(Expr::const_str("Decidable"), eq_s(lhs, rhs));
    // Project field `k` out of the value at de Bruijn index `major_idx`.
    //
    // The kernel structure-projection primitive `Proj` is used (rather than the
    // recursor) so that the constructor form `S.mk (Proj 0 a) … (Proj n-1 a)`
    // built in the diagonal proof is *syntactically* the struct-eta expansion of
    // `a` (`expand_eta_struct` emits exactly these `Proj` nodes). A recursor
    // projection on a neutral variable would stay stuck and fail to match. The
    // off-diagonal `congrArg` projection and the field discriminant use the same
    // `Proj` form so every field-equality type lines up definitionally.
    let proj_of = |k: usize, major: Expr| {
        Expr::proj(
            tn.clone(),
            u32::try_from(k).expect("derive arity was checked to fit u32"),
            major,
        )
    };
    let proj = |k: usize, major_idx: u32| proj_of(k, Expr::bvar(major_idx));

    // Diagonal proof of `@Eq S a b` from the per-field equalities `hk`, with
    // `a` at de Bruijn index `a_idx`, `b` at `b_idx`, and `hk` at `h_idx(k)`.
    // Built as the left-to-right `Eq.trans` chain over `congrArg` steps:
    //   step k : @Eq S (S.mk b.0 … b.{k-1} a.k … a.{n-1})
    //                  (S.mk b.0 … b.{k}   a.{k+1} … a.{n-1})
    // so chaining steps 0..n yields `@Eq S (S.mk a.0…) (S.mk b.0…)`, which the
    // kernel accepts as `@Eq S a b` by structure-eta.
    let diagonal_proof = |a_idx: u32, b_idx: u32, h_idx: &dyn Fn(usize) -> u32| -> Expr {
        // `mk_prefix(j)` = `S.mk b.0 … b.{j-1} a.j … a.{n-1}` (first j from b).
        let mk_prefix = |j: usize| -> Expr {
            let mut term = ctor_const.clone();
            for k in 0..n {
                let src_idx = if k < j { b_idx } else { a_idx };
                term = Expr::app(term, proj(k, src_idx));
            }
            term
        };

        // Fold the congruence steps right-to-left so the outermost `Eq.trans`
        // starts at `mk_prefix(0)` (≡ a). The chain's final endpoint is
        // `mk_prefix(n)` (≡ b).
        let mut acc: Option<Expr> = None;
        for k in (0..n).rev() {
            // f_k : S → S rewriting field k, holding the b-prefix fixed:
            //   fun (x : Fk) => S.mk b.0 … b.{k-1} x a.{k+1} … a.{n-1}
            // Under this binder all outer indices are pushed by 1; `x = bvar 0`.
            let f_k = {
                let mut body = ctor_const.clone();
                for j in 0..n {
                    let arg = if j < k {
                        proj(j, b_idx + 1)
                    } else if j == k {
                        Expr::bvar(0)
                    } else {
                        proj(j, a_idx + 1)
                    };
                    body = Expr::app(body, arg);
                }
                Expr::lam(BinderInfo::Default, fields[k].1.clone(), body)
            };
            let hk = Expr::bvar(h_idx(k));
            // `@congrArg.{u,v} α β a₁ a₂ f h : @Eq β (f a₁) (f a₂)` — the first
            // type argument `α` is the DOMAIN of `f`, the second `β` its codomain
            // (see clean-kernel `whnf_proof::EqProofBuilder::mk_congr_arg`). Here
            // `f_k : Fk → S` rewrites field `k`, so `α = Fk` (the field type) and
            // `β = S` (the struct). The lifted equality `a.k = b.k` (over `Fk`)
            // becomes `@Eq S (f_k a.k) (f_k b.k) = @Eq S (mk_prefix k)
            // (mk_prefix (k+1))`. Passing `S` for `α` would put a struct-typed
            // hole where the `Fk`-typed projection `a.k` sits — the kernel's
            // deep App-argument check rejects that (`expected S, inferred Fk`).
            let step = Expr::apps(
                Expr::const_str_levels("congrArg", vec![u_level.clone(), u_level.clone()]),
                [
                    fields[k].1.clone(),
                    ind_ty.clone(),
                    proj(k, a_idx),
                    proj(k, b_idx),
                    f_k,
                    hk,
                ],
            );
            acc = Some(match acc {
                None => step,
                // @Eq.trans.{u} S (mk_prefix k) (mk_prefix (k+1)) (mk_prefix n) step rest.
                Some(rest) => Expr::apps(
                    Expr::const_str_levels("Eq.trans", vec![u_level.clone()]),
                    [
                        ind_ty.clone(),
                        mk_prefix(k),
                        mk_prefix(k + 1),
                        mk_prefix(n),
                        step,
                        rest,
                    ],
                ),
            });
        }

        // `n >= 1` (single_ctor_struct guarantees a non-empty field list), so the
        // chain always has at least one step.
        acc.unwrap_or_else(|| {
            // Degenerate guard (unreachable for n >= 1): reflexivity of `a = a`.
            Expr::apps(
                Expr::const_str_levels("Eq.refl", vec![u_level.clone()]),
                [ind_ty.clone(), Expr::bvar(a_idx)],
            )
        })
    };

    // Recursively build the field dispatch at field `k`. `depth` counts binders
    // entered below the outer `fun (a b)`; `a = bvar(depth + 1)`,
    // `b = bvar(depth)`, and the accepted hypothesis `hj` (`j < k`) is the
    // isTrue-minor binder entered for field `j`, sitting at `bvar(depth - 1 - j)`.
    fn build_dispatch(
        k: usize,
        depth: u32,
        n: usize,
        ind_ty: &Expr,
        u_level: &Level,
        fields: &[(Name, Expr)],
        field_insts: &[Expr],
        eq_s: &dyn Fn(Expr, Expr) -> Expr,
        decidable_eq_s: &dyn Fn(Expr, Expr) -> Expr,
        proj: &dyn Fn(usize, u32) -> Expr,
        diagonal_proof: &dyn Fn(u32, u32, &dyn Fn(usize) -> u32) -> Expr,
    ) -> Expr {
        let a_idx = depth + 1;
        let b_idx = depth;

        if k == n {
            // All fields decided equal: prove `a = b` and wrap in `isTrue`.
            let h_idx = move |j: usize| -> u32 {
                depth - 1 - u32::try_from(j).expect("derive arity was checked to fit u32")
            };
            let proof = diagonal_proof(a_idx, b_idx, &h_idx);
            return Expr::apps(
                Expr::const_str("Decidable.isTrue"),
                [eq_s(Expr::bvar(a_idx), Expr::bvar(b_idx)), proof],
            );
        }

        let fty = &fields[k].1;
        // The field equality proposition `@Eq Fk a.k b.k` at this depth.
        let field_eq = Expr::apps(
            Expr::const_str_levels("Eq", vec![u_level.clone()]),
            [fty.clone(), proj(k, a_idx), proj(k, b_idx)],
        );

        // isFalse minor: `fun (hk : ¬(a.k = b.k)) => isFalse (@Eq S a b) <not_eq>`.
        // Inside the `hk` binder every index is +1; inside the further `heq`
        // binder (the disproof's argument) every index is +2 from this depth.
        let is_false_minor = {
            // not_eq : @Eq S a b → False, i.e.
            //   fun (heq : @Eq S a b) => hk (@congrArg.{u,u} S Fk a b projk heq).
            // At the heq binder: a = bvar(a_idx + 2), b = bvar(b_idx + 2),
            // hk = bvar 1, heq = bvar 0.
            let a2 = a_idx + 2;
            let b2 = b_idx + 2;
            // projk : S → Fk, `fun (s : S) => s.k`; `s = bvar 0`.
            let projk_fn = Expr::lam(BinderInfo::Default, ind_ty.clone(), proj(k, 0));
            let lifted = Expr::apps(
                Expr::const_str_levels("congrArg", vec![u_level.clone(), u_level.clone()]),
                [
                    ind_ty.clone(),
                    fty.clone(),
                    Expr::bvar(a2),
                    Expr::bvar(b2),
                    projk_fn,
                    Expr::bvar(0),
                ],
            );
            let contradiction = Expr::app(Expr::bvar(1), lifted);
            // The `heq` binder type lives in the *outer* context (the `hk`-lambda
            // body, depth + 1), so it references `a`/`b` at `+1`, not `+2`.
            let not_eq = Expr::lam(
                BinderInfo::Default,
                eq_s(Expr::bvar(a_idx + 1), Expr::bvar(b_idx + 1)),
                contradiction,
            );
            let is_false = Expr::apps(
                Expr::const_str("Decidable.isFalse"),
                [eq_s(Expr::bvar(a_idx + 1), Expr::bvar(b_idx + 1)), not_eq],
            );
            // The `hk` binder type lives in the *outer* context (current depth),
            // so it reuses `field_eq` (built with `a_idx`/`b_idx`):
            //   ¬(a.k = b.k) = (a.k = b.k) → False.
            let not_field_eq = Expr::pi(
                BinderInfo::Default,
                field_eq.clone(),
                Expr::const_str("False"),
            );
            Expr::lam(BinderInfo::Default, not_field_eq, is_false)
        };

        // isTrue minor: `fun (hk : a.k = b.k) => <dispatch field k+1>`, recursing
        // one binder deeper (depth + 1) with `hk` now in scope. The `hk` binder
        // type also lives in the outer context, so it reuses `field_eq`.
        let is_true_minor = {
            let inner = build_dispatch(
                k + 1,
                depth + 1,
                n,
                ind_ty,
                u_level,
                fields,
                field_insts,
                eq_s,
                decidable_eq_s,
                proj,
                diagonal_proof,
            );
            Expr::lam(BinderInfo::Default, field_eq.clone(), inner)
        };

        // Constant motive `fun (_ : Decidable (a.k = b.k)) => Decidable (@Eq S a b)`.
        // The discriminant binder pushes `a`, `b` by 1.
        let motive = Expr::lam(
            BinderInfo::Default,
            Expr::app(Expr::const_str("Decidable"), field_eq.clone()),
            decidable_eq_s(Expr::bvar(a_idx + 1), Expr::bvar(b_idx + 1)),
        );

        // Discriminant `instk a.k b.k : Decidable (a.k = b.k)`. The resolved
        // instance has type `DecidableEq Fk`, reducibly `(x y : Fk) → Decidable
        // (x = y)`, so applying it to the two projections yields the decision.
        let discriminant = Expr::apps(field_insts[k].clone(), [proj(k, a_idx), proj(k, b_idx)]);

        // @Decidable.rec.{1} (a.k = b.k) motive isFalse_minor isTrue_minor discr.
        // `Decidable` eliminates into `Decidable (@Eq S a b) : Type = Sort 1`, so
        // the motive universe is `1`. `Decidable` carries `p : Prop` as its sole
        // parameter (supplied first, before the motive).
        Expr::apps(
            Expr::const_str_levels("Decidable.rec", vec![Level::succ(Level::zero())]),
            [
                field_eq,
                motive,
                is_false_minor,
                is_true_minor,
                discriminant,
            ],
        )
    }

    let body = build_dispatch(
        0,
        0,
        n,
        &ind_ty,
        u_level,
        fields,
        &field_insts,
        &eq_s,
        &decidable_eq_s,
        &proj,
        &diagonal_proof,
    );

    Some(mk_binary_lam(&ind_ty, body))
}

/// Try to build a sorry-free `DecidableEq` instance value for the
/// multi-ctor-with-fields shape (`>= 2` constructors, some/all carrying fields,
/// `np == 0`, non-recursive) — e.g. `Either A B`, `Result T E`, or a mixed sum
/// of nullary and record constructors.
///
/// This is the union of [`decidable_eq_nullary_enum_value`]'s per-constructor
/// dispatch and [`decidable_eq_struct_value`]'s per-field
/// decide-and-compose. `DecidableEq T` is the reducible def
/// `(a b : T) -> Decidable (@Eq T a b)`, so the instance value is the binary
/// lambda `fun (a b : T) => <body>` (`a = bvar 1`, `b = bvar 0` at body depth)
/// whose body is a nested recursor dispatch:
///
/// ```text
/// fun (a b : T) =>
///   @T.rec.{1} (fun a' => Decidable (@Eq T a' b))    -- outer motive (b captured)
///     <outer_minor c_0> … <outer_minor c_{n-1}>       -- one per ctor of `a`
///     a
/// ```
///
/// where the outer minor for `a = cᵢ` binds `cᵢ`'s fields `(aF₀ … aF_{kᵢ-1})`
/// and re-dispatches on `b` (its major reduced to `cᵢ aF…`):
///
/// ```text
///   fun (aF₀ : Fᵢ₀) … (aF_{kᵢ-1} : Fᵢ_{kᵢ-1}) =>
///     @T.rec.{1} (fun b' => Decidable (@Eq T (cᵢ aF…) b'))   -- inner motive
///       <inner_minor c_0> … <inner_minor c_{n-1}>             -- one per ctor of `b`
///       b
/// ```
///
/// and the inner minor for `b = cⱼ` binds `cⱼ`'s fields `(bF₀ … bF_{kⱼ-1})`:
/// * `i != j` (off-diagonal): `@Decidable.isFalse (@Eq T (cᵢ aF…) (cⱼ bF…))
///   (fun (h : @Eq T (cᵢ aF…) (cⱼ bF…)) => @T.noConfusion.{0} False (cᵢ aF…)
///   (cⱼ bF…) h)`. For distinct constructors `@T.noConfusionType False (cᵢ aF…)
///   (cⱼ bF…)` reduces to `False`, giving the negation `Decidable.isFalse`
///   demands — exactly as in the nullary-enum branch, but with the applied
///   constructors as the discriminees.
/// * `i == j` (diagonal): decide each field `p` via its resolved
///   `DecidableEq Fᵢ_p` instance applied to the bound `(aF_p, bF_p)` and compose
///   with `@Decidable.rec.{1}` under a constant motive `fun _ => Decidable
///   (@Eq T (cᵢ aF…) (cᵢ bF…))`. A differing field lifts its disequality through
///   the `cᵢ` constructor (`congrArg` of `fun (x : Fᵢ_p) => cᵢ bF₀ … bF_{p-1} x
///   aF_{p+1} … aF_{kᵢ-1}` evaluated at `heq : cᵢ aF… = cᵢ bF…`) into a
///   contradiction with `Decidable.isFalse`; all fields equal yields
///   `@Decidable.isTrue (@Eq T (cᵢ aF…) (cᵢ bF…)) <proof>` where `<proof>` is the
///   left-to-right `Eq.trans` chain of `congrArg` steps rebuilding `cᵢ aF…` into
///   `cᵢ bF…` one field at a time. No struct-eta is needed: the discriminees are
///   already in constructor form `cᵢ aF…` / `cᵢ bF…`.
///
/// Every field type appearing on any constructor must resolve a monomorphic
/// in-tree `DecidableEq` instance up front (via [`resolve_field_instance`]); if
/// any is unresolvable, or the shape is outside this set (single ctor,
/// parametric, recursive, all-nullary), this returns `None` and the caller tries
/// another genuine builder or fails closed. The whole term is closed (apart from the
/// lambda-bound binders) and kernel-checkable; it introduces no `sorryAx`/axioms
/// — only the type's own recursor, `noConfusion`, each field's `DecidableEq`
/// instance, `congrArg`, `Eq.trans`, `Eq.refl`, and the `Decidable` constructors.
fn decidable_eq_multi_ctor_fields_value(
    env: &Environment,
    tn: &Name,
    ctors: &[CtorInfo2],
    np: u32,
    u_level: &Level,
) -> Option<Expr> {
    if !multi_ctor_fields_shape(ctors, np) {
        return None;
    }

    // Resolve every field's DecidableEq instance up front (across all
    // constructors); bail to the fallback if any field type lacks a resolvable
    // monomorphic instance. Stored per-constructor, indexed by field position.
    let mut ctor_field_insts: Vec<Vec<Expr>> = Vec::with_capacity(ctors.len());
    for ctor in ctors {
        let mut insts = Vec::with_capacity(ctor.fields.len());
        for (_fname, fty) in &ctor.fields {
            insts.push(resolve_field_instance(env, "DecidableEq", fty)?);
        }
        ctor_field_insts.push(insts);
    }

    let ind_ty = Expr::const_(tn.clone(), vec![]);
    let false_expr = Expr::const_str("False");
    // `T : Type 0 = Sort 1`, so each recursor eliminates into `Decidable _ : Sort 1`.
    let motive_level = Level::succ(Level::zero());
    let rec_name = Name::from_string(&format!("{tn}.rec"));
    let nc_name = Name::from_string(&format!("{tn}.noConfusion"));
    // noConfusion's only level param is the motive universe; the motive is
    // `False : Prop = Sort 0`, so it is instantiated at level 0.
    let nc_levels = vec![Level::zero()];

    // `@Eq.{u} T lhs rhs`.
    let eq_t = |lhs: Expr, rhs: Expr| {
        Expr::apps(
            Expr::const_str_levels("Eq", vec![u_level.clone()]),
            [ind_ty.clone(), lhs, rhs],
        )
    };
    // `Decidable (@Eq T lhs rhs)`.
    let decidable_eq_t =
        |lhs: Expr, rhs: Expr| Expr::app(Expr::const_str("Decidable"), eq_t(lhs, rhs));

    // Build `cᵢ` applied to its field variables, where field `p` of a `k`-field
    // constructor sits at de Bruijn index `base + (k - 1 - p)` (innermost field
    // is `base`). `base` accounts for any binders entered below the field binders.
    let apply_ctor = |ctor: &CtorInfo2, base: u32| -> Expr {
        let k = ctor.fields.len();
        let mut term = Expr::const_(ctor.name.clone(), vec![]);
        for p in 0..k {
            let idx = base + u32::try_from(k - 1 - p).expect("derive arity was checked to fit u32");
            term = Expr::app(term, Expr::bvar(idx));
        }
        term
    };

    // Outer motive: `fun (a' : T) => Decidable (@Eq T a' b)`. Inside the lambda
    // `a' = bvar 0`; the outer `b` binder is pushed to `bvar 1`.
    let outer_motive = Expr::lam(
        BinderInfo::Default,
        ind_ty.clone(),
        decidable_eq_t(Expr::bvar(0), Expr::bvar(1)),
    );

    let outer_rec = Expr::const_(rec_name.clone(), vec![motive_level.clone()]);
    let mut outer = Expr::app(outer_rec, outer_motive);

    for (i, ctor_i) in ctors.iter().enumerate() {
        let ki = ctor_i.fields.len();
        let ki_u = u32::try_from(ki).expect("derive arity was checked to fit u32");

        // Inside the outer minor (after entering `cᵢ`'s `kᵢ` field binders): the
        // outer major `b` is `bvar(kᵢ)`; the a-fields occupy `bvar(0)…bvar(kᵢ-1)`.
        // `cᵢ aF…` references the a-fields at base 0.
        let ci_a = apply_ctor(ctor_i, 0);

        // Inner motive: `fun (b' : T) => Decidable (@Eq T (cᵢ aF…) b')`. The
        // motive binder pushes everything by 1, so `cᵢ aF…` is at base 1.
        let inner_motive = Expr::lam(
            BinderInfo::Default,
            ind_ty.clone(),
            decidable_eq_t(apply_ctor(ctor_i, 1), Expr::bvar(0)),
        );

        let inner_rec = Expr::const_(rec_name.clone(), vec![motive_level.clone()]);
        let mut inner = Expr::app(inner_rec, inner_motive);

        for (j, ctor_j) in ctors.iter().enumerate() {
            let kj = ctor_j.fields.len();
            let kj_u = u32::try_from(kj).expect("derive arity was checked to fit u32");

            // Inside the inner minor (after entering `cⱼ`'s `kⱼ` field binders):
            // b-fields are `bvar(0)…bvar(kⱼ-1)` (base 0); the a-fields were pushed
            // down by `kⱼ` so they sit at base `kⱼ`.
            let inner_body = if i == j {
                // Diagonal: decide each field, composing with Decidable.rec.
                decidable_eq_diagonal(
                    ctor_i,
                    &ctor_field_insts[i],
                    &ind_ty,
                    &nc_name,
                    u_level,
                    &eq_t,
                    &decidable_eq_t,
                )
            } else {
                // Off-diagonal: distinct constructors are never equal. The
                // discriminees are the applied constructors `cᵢ aF…` / `cⱼ bF…`.
                // At the inner-minor body depth: b-fields at base 0, a-fields at
                // base `kⱼ`.
                let ci_app = apply_ctor(ctor_i, kj_u);
                let cj_app = apply_ctor(ctor_j, 0);
                let eq_ij = eq_t(ci_app.clone(), cj_app.clone());
                // not_eq : @Eq T (cᵢ aF…) (cⱼ bF…) → False, i.e.
                //   fun (h : eq_ij) => @T.noConfusion.{0} False (cᵢ aF…) (cⱼ bF…) h.
                // Under the `h` binder every field index is pushed by 1, so the
                // applied constructors are rebuilt at base+1; `h = bvar 0`.
                let ci_h = apply_ctor(ctor_i, kj_u + 1);
                let cj_h = apply_ctor(ctor_j, 1);
                let nc_app = Expr::apps(
                    Expr::const_(nc_name.clone(), nc_levels.clone()),
                    [false_expr.clone(), ci_h, cj_h, Expr::bvar(0)],
                );
                let not_eq = Expr::lam(BinderInfo::Default, eq_ij.clone(), nc_app);
                Expr::apps(Expr::const_str("Decidable.isFalse"), [eq_ij, not_eq])
            };

            // Wrap the inner-minor body in `cⱼ`'s `kⱼ` field binders.
            let mut inner_minor = inner_body;
            for (_fname, fty) in ctor_j.fields.iter().rev() {
                inner_minor = Expr::lam(BinderInfo::Default, fty.clone(), inner_minor);
            }
            inner = Expr::app(inner, inner_minor);
        }

        // Apply the inner recursor to its major `b` (= bvar(kᵢ) at this depth).
        inner = Expr::app(inner, Expr::bvar(ki_u));

        // Wrap the outer-minor body (the inner dispatch) in `cᵢ`'s field binders.
        let mut outer_minor = inner;
        for (_fname, fty) in ctor_i.fields.iter().rev() {
            outer_minor = Expr::lam(BinderInfo::Default, fty.clone(), outer_minor);
        }
        outer = Expr::app(outer, outer_minor);
    }

    // Apply the outer recursor to its major `a` (= bvar 1 at body depth).
    outer = Expr::app(outer, Expr::bvar(1));

    Some(mk_binary_lam(&ind_ty, outer))
}

/// Build the diagonal arm of [`decidable_eq_multi_ctor_fields_value`] for a
/// matched constructor `c` (= `cᵢ`) carrying `n` fields, evaluated at the
/// inner-minor body depth: the `b`-fields occupy de Bruijn `bvar(0)…bvar(n-1)`
/// (field `p` at `bvar(n-1-p)`) and the `a`-fields — pushed down by the `n`
/// inner binders — occupy `bvar(n)…bvar(2n-1)` (field `p` at `bvar(2n-1-p)`).
///
/// Decides each field `p` via its resolved `DecidableEq Fp` instance applied to
/// the bound `(aF_p, bF_p)` and dispatches with `@Decidable.rec.{1}` under a
/// constant motive `fun _ => Decidable (@Eq T (c aF…) (c bF…))`:
///
/// * **isFalse minor** (`hk : ¬(aF_k = bF_k)`). The discriminees `c aF…` and
///   `c bF…` share the constructor `c`, so `@T.noConfusionType False (c aF…)
///   (c bF…)` reduces to `(aF₀ = bF₀ → … → aF_{n-1} = bF_{n-1} → False) → False`.
///   Thus `@T.noConfusion.{0} False (c aF…) (c bF…) heq` applied to the
///   field-equality eliminator `fun (e₀ … e_{n-1}) => hk e_k` yields `False` —
///   giving the negation `Decidable.isFalse` demands, using only `noConfusion`
///   (no projection of `T`, which is not a single-ctor structure).
/// * **isTrue base case** (every `hk : aF_k = bF_k` in scope). Proves `c aF… =
///   c bF…` by the left-to-right `Eq.trans` chain of `congrArg` steps, rewriting
///   one field at a time. Each step's congruence function `fun (x : Fk) => c bF₀
///   … bF_{k-1} x aF_{k+1} … aF_{n-1}` is built directly from the bound field
///   variables, so the discriminees stay in constructor form and no struct-eta
///   is required.
///
/// A 0-field diagonal short-circuits to `Decidable.isTrue (@Eq T c c) (Eq.refl
/// T c)` (nothing to decide). The term is closed and kernel-checkable; it
/// introduces no `sorryAx`/axioms.
fn decidable_eq_diagonal(
    ctor: &CtorInfo2,
    field_insts: &[Expr],
    ind_ty: &Expr,
    nc_name: &Name,
    u_level: &Level,
    eq_t: &dyn Fn(Expr, Expr) -> Expr,
    decidable_eq_t: &dyn Fn(Expr, Expr) -> Expr,
) -> Expr {
    let fields = &ctor.fields;
    let n = fields.len();
    let ctor_const = Expr::const_(ctor.name.clone(), vec![]);
    let false_expr = Expr::const_str("False");

    // 0-field diagonal: `c = c` is closed by reflexivity (no fields to decide).
    if n == 0 {
        let c = Expr::const_(ctor.name.clone(), vec![]);
        let refl = Expr::apps(
            Expr::const_str_levels("Eq.refl", vec![u_level.clone()]),
            [ind_ty.clone(), c.clone()],
        );
        return Expr::apps(
            Expr::const_str("Decidable.isTrue"),
            [eq_t(c.clone(), c), refl],
        );
    }

    // `c x₀ … x_{n-1}` where field `p` reads `bvar(a_base + (n-1-p))` if `p >= j`
    // (from `a`) else `bvar(b_base + (n-1-p))` (from `b`) — i.e. the first `j`
    // fields come from `b`, the rest from `a`. Names the `Eq.trans` endpoints and
    // the constructed discriminees.
    let mk_prefix = |j: usize, a_base: u32, b_base: u32| -> Expr {
        let mut term = ctor_const.clone();
        for p in 0..n {
            let off = u32::try_from(n - 1 - p).expect("derive arity was checked to fit u32");
            let idx = if p < j { b_base + off } else { a_base + off };
            term = Expr::app(term, Expr::bvar(idx));
        }
        term
    };

    // Diagonal proof of `@Eq T (c aF…) (c bF…)` from the per-field equalities,
    // with the `a`-fields based at `a_base`, the `b`-fields at `b_base`, and the
    // accepted field-equality hypothesis `hp` at `h_idx(p)`.
    let diagonal_proof = |a_base: u32, b_base: u32, h_idx: &dyn Fn(usize) -> u32| -> Expr {
        let mut acc: Option<Expr> = None;
        for p in (0..n).rev() {
            let off = u32::try_from(n - 1 - p).expect("derive arity was checked to fit u32");
            let a_p = Expr::bvar(a_base + off);
            let b_p = Expr::bvar(b_base + off);
            // f_p : Fp → T rewriting field p, holding the b-prefix and a-suffix
            // fixed: fun (x : Fp) => c b₀ … b_{p-1} x a_{p+1} … a_{n-1}. The binder
            // pushes every field index by 1.
            let f_p = {
                let mut body = ctor_const.clone();
                for q in 0..n {
                    let qoff =
                        u32::try_from(n - 1 - q).expect("derive arity was checked to fit u32");
                    let arg = if q < p {
                        Expr::bvar(b_base + 1 + qoff)
                    } else if q == p {
                        Expr::bvar(0)
                    } else {
                        Expr::bvar(a_base + 1 + qoff)
                    };
                    body = Expr::app(body, arg);
                }
                Expr::lam(BinderInfo::Default, fields[p].1.clone(), body)
            };
            let hp = Expr::bvar(h_idx(p));
            // `@congrArg.{u,v} α β a₁ a₂ f h : @Eq β (f a₁) (f a₂)` — `α` is the
            // DOMAIN of `f`, `β` its codomain. Here `f_p : Fp → T`, so `α = Fp`
            // (the field type) and `β = T` (the inductive). The result is
            // `@Eq T (f_p a_p) (f_p b_p) = @Eq T (mk_prefix p) (mk_prefix (p+1))`.
            // Supplying `T` for `α` would demand a `T`-typed `a₁` where the
            // `Fp`-typed field variable sits; the kernel's deep App-argument check
            // (rejecting nested ill-typedness) flags that mismatch.
            let step = Expr::apps(
                Expr::const_str_levels("congrArg", vec![u_level.clone(), u_level.clone()]),
                [fields[p].1.clone(), ind_ty.clone(), a_p, b_p, f_p, hp],
            );
            acc = Some(match acc {
                None => step,
                Some(rest) => Expr::apps(
                    Expr::const_str_levels("Eq.trans", vec![u_level.clone()]),
                    [
                        ind_ty.clone(),
                        mk_prefix(p, a_base, b_base),
                        mk_prefix(p + 1, a_base, b_base),
                        mk_prefix(n, a_base, b_base),
                        step,
                        rest,
                    ],
                ),
            });
        }
        // `n >= 1` here (the 0-field diagonal short-circuited above).
        acc.unwrap_or_else(|| {
            Expr::apps(
                Expr::const_str_levels("Eq.refl", vec![u_level.clone()]),
                [ind_ty.clone(), mk_prefix(0, a_base, b_base)],
            )
        })
    };

    // Recursively build the per-field decision dispatch at field `k`. `depth`
    // counts isTrue-minor binders entered below the inner-minor body: at depth 0
    // the b-fields are at `bvar(0)…bvar(n-1)` and a-fields at `bvar(n)…bvar(2n-1)`.
    // Each isTrue-minor binder pushes both bases by 1, so a_base = n + depth and
    // b_base = depth. The accepted hypothesis `hq` (`q < k`) is the isTrue-minor
    // binder entered for field `q`, sitting at `bvar(depth - 1 - q)`.
    #[allow(clippy::too_many_arguments)]
    fn build_dispatch(
        k: usize,
        depth: u32,
        n: usize,
        nc_name: &Name,
        false_expr: &Expr,
        u_level: &Level,
        fields: &[(Name, Expr)],
        field_insts: &[Expr],
        eq_t: &dyn Fn(Expr, Expr) -> Expr,
        decidable_eq_t: &dyn Fn(Expr, Expr) -> Expr,
        mk_prefix: &dyn Fn(usize, u32, u32) -> Expr,
        diagonal_proof: &dyn Fn(u32, u32, &dyn Fn(usize) -> u32) -> Expr,
    ) -> Expr {
        let n_u = u32::try_from(n).expect("derive arity was checked to fit u32");
        let a_base = n_u + depth;
        let b_base = depth;

        if k == n {
            // All fields decided equal: prove `c aF… = c bF…` and wrap in isTrue.
            let c_a = mk_prefix(0, a_base, b_base);
            let c_b = mk_prefix(n, a_base, b_base);
            let h_idx = move |q: usize| -> u32 {
                depth - 1 - u32::try_from(q).expect("derive arity was checked to fit u32")
            };
            let proof = diagonal_proof(a_base, b_base, &h_idx);
            return Expr::apps(Expr::const_str("Decidable.isTrue"), [eq_t(c_a, c_b), proof]);
        }

        let fty = &fields[k].1;
        let koff = u32::try_from(n - 1 - k).expect("derive arity was checked to fit u32");
        let a_k = Expr::bvar(a_base + koff);
        let b_k = Expr::bvar(b_base + koff);
        // The field equality proposition `@Eq Fk aF_k bF_k` at this depth.
        let field_eq = Expr::apps(
            Expr::const_str_levels("Eq", vec![u_level.clone()]),
            [fty.clone(), a_k.clone(), b_k.clone()],
        );

        // isFalse minor: `fun (hk : ¬(aF_k = bF_k)) => isFalse (@Eq T c_a c_b) <not_eq>`
        // where the discriminees `c aF…`/`c bF…` are rebuilt at the current binder
        // depth (the `hk` binder pushes both bases by 1).
        let is_false_minor = {
            // not_eq : @Eq T c_a c_b → False, via noConfusion (same-ctor injection):
            //   fun (heq : @Eq T c_a c_b) =>
            //     @T.noConfusion.{0} False c_a c_b heq
            //       (fun (e₀ : aF₀=bF₀) … (e_{n-1} : …) => hk e_k).
            // At the `heq` binder both bases are pushed by 2; the field-eliminator
            // adds `n` more binders, so `hk` (the `hk`-lambda binder) sits at
            // `bvar(n + 1)` from inside the eliminator (1 for heq + n for e's), and
            // `e_k = bvar(n - 1 - k)`.
            let c_a2 = mk_prefix(0, a_base + 2, b_base + 2);
            let c_b2 = mk_prefix(n, a_base + 2, b_base + 2);
            // Eliminator `fun (e₀ … e_{n-1}) => hk e_k`. Build the body first, then
            // wrap the `n` field-equality binders. Binder types reference the
            // a/b-fields; at the innermost (after all `n` e-binders) the a-fields
            // are pushed by 2 (heq) + n (e's) from `a_base`, similarly for b. But we
            // only need the *types* of the e-binders to match noConfusionType, which
            // the kernel infers from the discriminees — we still must supply concrete
            // Pi domains. The j-th e-binder (entered outermost-first) has type
            // `@Eq Fj aF_j bF_j` evaluated where j-1 prior e-binders plus the heq
            // binder are in scope: a_base pushed by (2 + j), b_base by (2 + j).
            let elim_body = {
                // hk = bvar(n + 1): n e-binders + 1 heq binder above the hk lambda.
                let hk = Expr::bvar(n_u + 1);
                // e_k = bvar(n - 1 - k) among the n e-binders.
                let e_k = Expr::bvar(
                    u32::try_from(n - 1 - k).expect("derive arity was checked to fit u32"),
                );
                Expr::app(hk, e_k)
            };
            let mut eliminator = elim_body;
            for j in (0..n).rev() {
                // The j-th e-binder type `@Eq Fj aF_j bF_j` lives under the heq
                // binder and the j prior e-binders: a/b bases pushed by (2 + j).
                let pushed = 2 + u32::try_from(j).expect("derive arity was checked to fit u32");
                let joff = u32::try_from(n - 1 - j).expect("derive arity was checked to fit u32");
                let ej_ty = Expr::apps(
                    Expr::const_str_levels("Eq", vec![u_level.clone()]),
                    [
                        fields[j].1.clone(),
                        Expr::bvar(a_base + pushed + joff),
                        Expr::bvar(b_base + pushed + joff),
                    ],
                );
                eliminator = Expr::lam(BinderInfo::Default, ej_ty, eliminator);
            }
            // @T.noConfusion.{0} False c_a c_b heq <eliminator>.
            let nc_app = Expr::apps(
                Expr::const_(nc_name.clone(), vec![Level::zero()]),
                [false_expr.clone(), c_a2, c_b2, Expr::bvar(0), eliminator],
            );
            // The `heq` binder type lives in the `hk`-lambda body (bases +1).
            let c_a1 = mk_prefix(0, a_base + 1, b_base + 1);
            let c_b1 = mk_prefix(n, a_base + 1, b_base + 1);
            let not_eq = Expr::lam(
                BinderInfo::Default,
                eq_t(c_a1.clone(), c_b1.clone()),
                nc_app,
            );
            let is_false = Expr::apps(
                Expr::const_str("Decidable.isFalse"),
                [eq_t(c_a1, c_b1), not_eq],
            );
            // The `hk` binder type lives in the outer (current) context, so it
            // reuses `field_eq`: ¬(aF_k = bF_k) = (aF_k = bF_k) → False.
            let not_field_eq = Expr::pi(
                BinderInfo::Default,
                field_eq.clone(),
                Expr::const_str("False"),
            );
            Expr::lam(BinderInfo::Default, not_field_eq, is_false)
        };

        // isTrue minor: `fun (hk : aF_k = bF_k) => <dispatch field k+1>`, recursing
        // one binder deeper with `hk` in scope. The `hk` binder type reuses
        // `field_eq` (outer context).
        let is_true_minor = {
            let inner = build_dispatch(
                k + 1,
                depth + 1,
                n,
                nc_name,
                false_expr,
                u_level,
                fields,
                field_insts,
                eq_t,
                decidable_eq_t,
                mk_prefix,
                diagonal_proof,
            );
            Expr::lam(BinderInfo::Default, field_eq.clone(), inner)
        };

        // Constant motive `fun (_ : Decidable (aF_k = bF_k)) => Decidable (@Eq T c_a c_b)`.
        // The discriminant binder pushes both bases by 1.
        let motive = {
            let c_a1 = mk_prefix(0, a_base + 1, b_base + 1);
            let c_b1 = mk_prefix(n, a_base + 1, b_base + 1);
            Expr::lam(
                BinderInfo::Default,
                Expr::app(Expr::const_str("Decidable"), field_eq.clone()),
                decidable_eq_t(c_a1, c_b1),
            )
        };

        // Discriminant `instk aF_k bF_k : Decidable (aF_k = bF_k)`.
        let discriminant = Expr::apps(field_insts[k].clone(), [a_k, b_k]);

        // @Decidable.rec.{1} (aF_k = bF_k) motive isFalse_minor isTrue_minor discr.
        Expr::apps(
            Expr::const_str_levels("Decidable.rec", vec![Level::succ(Level::zero())]),
            [
                field_eq,
                motive,
                is_false_minor,
                is_true_minor,
                discriminant,
            ],
        )
    }

    build_dispatch(
        0,
        0,
        n,
        nc_name,
        &false_expr,
        u_level,
        fields,
        field_insts,
        eq_t,
        decidable_eq_t,
        &|j, a_base, b_base| mk_prefix(j, a_base, b_base),
        &diagonal_proof,
    )
}

// ---------------------------------------------------------------------------
// DeriveInhabited2
// ---------------------------------------------------------------------------

pub(crate) struct DeriveInhabited2;

impl ExtDeriveHandler2 for DeriveInhabited2 {
    fn class_name(&self) -> &str {
        "Inhabited"
    }

    fn derive(
        &self,
        _env: &Environment,
        tn: &Name,
        _te: &Expr,
        ctors: &[CtorInfo2],
        np: u32,
        lp: &[Name],
    ) -> Result<Vec<DerivedDecl2>, DeriveError> {
        check_index_capacity(self.class_name(), tn, ctors, np)?;
        let first = require_first_ctor(ctors, "Inhabited", tn)?;
        if np != 0 || !lp.is_empty() || !first.fields.is_empty() {
            return Err(DeriveError::Unsupported {
                class_name: "Inhabited".to_owned(),
                ind_name: tn.to_string(),
                reason: "a closed nullary constructor is required; parameter and field \
                         instances are not synthesized by this handler"
                    .to_owned(),
            });
        }
        let u = Level::succ(Level::zero());
        let ind_ty = Expr::const_(tn.clone(), vec![]);
        let default_val = Expr::const_(first.name.clone(), vec![]);
        let type_ = Expr::app(
            Expr::const_str_levels("Inhabited", vec![u.clone()]),
            ind_ty.clone(),
        );
        let value = Expr::apps(
            Expr::const_str_levels("Inhabited.mk", vec![u]),
            [ind_ty, default_val],
        );
        Ok(vec![DerivedDecl2 {
            name: inst_name("Inhabited", tn),
            type_,
            value,
            is_instance: true,
        }])
    }
}

// ---------------------------------------------------------------------------
// DeriveNonempty2
// ---------------------------------------------------------------------------

pub(crate) struct DeriveNonempty2;

impl ExtDeriveHandler2 for DeriveNonempty2 {
    fn class_name(&self) -> &str {
        "Nonempty"
    }

    fn derive(
        &self,
        _env: &Environment,
        tn: &Name,
        _te: &Expr,
        ctors: &[CtorInfo2],
        np: u32,
        lp: &[Name],
    ) -> Result<Vec<DerivedDecl2>, DeriveError> {
        check_index_capacity(self.class_name(), tn, ctors, np)?;
        let first = require_first_ctor(ctors, "Nonempty", tn)?;
        if np != 0 || !lp.is_empty() || !first.fields.is_empty() {
            return Err(DeriveError::Unsupported {
                class_name: "Nonempty".to_owned(),
                ind_name: tn.to_string(),
                reason: "a closed nullary constructor is required; parameter and field \
                         instances are not synthesized by this handler"
                    .to_owned(),
            });
        }
        let u = Level::succ(Level::zero());
        let ind_ty = Expr::const_(tn.clone(), vec![]);
        let witness = Expr::const_(first.name.clone(), vec![]);
        let type_ = Expr::app(
            Expr::const_str_levels("Nonempty", vec![u.clone()]),
            ind_ty.clone(),
        );
        let value = Expr::apps(
            Expr::const_str_levels("Nonempty.intro", vec![u]),
            [ind_ty, witness],
        );
        Ok(vec![DerivedDecl2 {
            name: inst_name("Nonempty", tn),
            type_,
            value,
            is_instance: true,
        }])
    }
}

// ---------------------------------------------------------------------------
// DeriveSizeOf2
// ---------------------------------------------------------------------------

pub(crate) struct DeriveSizeOf2;

impl ExtDeriveHandler2 for DeriveSizeOf2 {
    fn class_name(&self) -> &str {
        "SizeOf"
    }

    fn derive(
        &self,
        _env: &Environment,
        tn: &Name,
        _te: &Expr,
        _ctors: &[CtorInfo2],
        _np: u32,
        _lp: &[Name],
    ) -> Result<Vec<DerivedDecl2>, DeriveError> {
        Err(DeriveError::Unsupported {
            class_name: "SizeOf".to_owned(),
            ind_name: tn.to_string(),
            reason: "no structural SizeOf construction is available".to_owned(),
        })
    }
}

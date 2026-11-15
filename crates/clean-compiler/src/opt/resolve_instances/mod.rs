// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Known-instance class-method resolution (two-language roadmap WS6.4).
//!
//! Every battery arithmetic op used to reach the back ends as a call to a
//! class PROJECTION FUNCTION with the instance as a runtime argument —
//! `HAdd.hAdd α β γ inst x y` — lowered to the bodyless runtime shim
//! `l_HAdd_hAdd`, which applies a freshly boxed instance closure. That path
//! boxes every scalar, allocates per call, and hides the operation from the
//! native `UIntW` arithmetic lowering and from the kernel translation
//! validator (its "named callee not TV-certifiable" / "operand not resolvable
//! to bvVar" skips).
//!
//! # The rule
//!
//! `let r := C.method τ… inst x…` becomes `let r := f x…` exactly when:
//!
//! 1. `C.method`'s kernel VALUE is the projection function of a
//!    structure-class `C`: `λ p₀ … pₙ₋₁ (self : C p₀ … pₙ₋₁), self.i`, where
//!    `C` is a registered class and a one-constructor, non-recursive,
//!    index-free inductive with `n` parameters (`class_projection`).
//! 2. `inst` is an fvar bound, in scope, to the nullary constant `I`.
//! 3. δ-unfolding ONLY constants for which `env.is_instance` holds — at most
//!    `MAX_INSTANCE_UNFOLD` steps, and no other reduction (no β, no ι, no
//!    unfolding of a non-instance, no step through an instance whose runtime
//!    code is an `implemented_by` substitute) — reaches a value that is syntactically
//!    `C.mk p… f…`, and the selected field is a closed constant `f`
//!    (`known_instance_field`).
//! 4. The call supplies exactly `f`'s syntactic Pi arity of method
//!    arguments (a saturated call; `f`'s type IS the field type, so the
//!    method arguments are `f`'s own arguments, erased ones included).
//! 5. The rewritten value `f x…` is ALREADY in mono form
//!    (`resolved_call_is_mono`): the pass runs after `to_mono`, so a callee
//!    `to_mono` would rewrite — `Nat.succ` (to `Nat.add n 1`), a
//!    trivial-structure constructor (to its field), `Decidable.*` (to
//!    `Bool`), `Quot.mk`, a Prop-valued call (to erased) — is refused, never
//!    emitted raw. `f` must also be a first-order, runtime-callable constant
//!    (`runtime_callable_field`): not a theorem, type former, recursor or
//!    quotient, and no binder of its type ranges over a `Sort`.
//!
//! The rule reads the instance's VALUE, never its name: in an environment
//! where `instHAddUInt64 := HAdd.mk UInt64.sub`, `x + y` becomes
//! `UInt64.sub x y`. Anything outside the rule — an instance built through a
//! `match` or any other computation, a non-instance constant of the same
//! shape, a longer δ-chain, a partial or over-application, a field `to_mono`
//! would rewrite — is left exactly
//! as it was. A missed optimization is sound; a guessed one is not.
//!
//! # Companion constant fold
//!
//! `let x : UIntW := UIntW.ofNat n` with `n` bound to a `Nat` literal becomes
//! `let x : UIntW := n mod 2^W` (`fold_uint_of_nat`), a literal whose
//! declared type is exactly `UIntW`; `to_ir` lowers such a literal to the
//! typed `IRLiteral::UIntW`. It is justified by the prelude definition
//! (`UIntW.ofNat n = ⟨BitVec.ofNat W n⟩`, i.e. `n mod 2^W`). It is
//! kernel-checked by the TV equation only for declarations the kernel TV
//! certifies (WS6.6); everywhere else the unit boundary tests are its only
//! check.
//!
//! # Placement
//!
//! A Mono-phase pass registered AFTER `optimize` and only when
//! `OptConfig::enable_simp_value` is on (`-O1`/`-O2`; `-O0` keeps the
//! dynamic path visible). Running after `optimize` is load-bearing for the
//! fold: CSE keys a literal by its VALUE, so a typed `UIntW` literal must
//! never meet it. A dead-code sweep follows a successful rewrite so the now
//! unused instance and `Nat` literal bindings do not survive into the
//! lowered body.
//!
//! A saturated structure projection of a registered instance application
//! also forwards a field that its kernel value reads from its own argument
//! in parameter-free declarations (the existing closed-value Fragment-5 floor).
//! This shares the Rust-ABI carrier rule (not its primitive aliases), so
//! `OfNat.ofNat Nat n (instOfNatNat n)` normalizes before RC insertion.
//! Runtime substitutions and every nontrivial field computation stay dynamic.
//! Parameterized declarations retain their existing representation path:
//! general parameter normalization needs the scalar/boxed refinement too.

pub(crate) mod projection;
use projection::{class_projection, project_instance_argument, ClassProjection};

use crate::lcnf::{Arg, Code, Decl, DeclValue, FunDecl, LetDecl, LetValue};
use crate::CodeFolder;
use clean_kernel::env::ConstantKind;
use clean_kernel::{BigNat, Environment, Expr, ExprKind, FVarId, Level, Literal, Name};
use std::collections::HashMap;

/// The δ-unfolding budget of [`known_instance_field`]: at most this many
/// instance constants are unfolded, the first included. A longer instance
/// chain simply does not resolve.
pub(crate) const MAX_INSTANCE_UNFOLD: usize = 4;

/// Resolve field `proj.field` of the known instance `instance`.
///
/// δ-unfolds only constants for which `env.is_instance` holds (each a
/// level-parameter-free `Definition`), at most [`MAX_INSTANCE_UNFOLD`]
/// times, with no other reduction. The first value that is not a bare
/// instance constant must be syntactically `C.mk p… f…` (the unique
/// constructor of `proj.class`, fully applied), and the selected field must be
/// a bare constant `f` whose universe instantiation is closed and complete.
pub(crate) fn known_instance_field(
    env: &Environment,
    instance: &Name,
    proj: &ClassProjection,
) -> Option<Name> {
    let mut current = instance.clone();
    for _ in 0..MAX_INSTANCE_UNFOLD {
        // An instance whose runtime implementation is substituted
        // (`implemented_by`) is not described by its kernel value.
        if !env.is_instance(&current)
            || env.has_implemented_by(&current)
            || env.is_extern(&current)
            || env.is_noncomputable(&current)
        {
            return None;
        }
        let info = env.get_const(&current)?;
        if info.kind != ConstantKind::Definition || !info.level_params.is_empty() {
            return None;
        }
        let value = info.value.as_ref()?;
        if let ExprKind::Const(next, levels) = value.kind() {
            if levels.is_empty() && env.get_constructor(next).is_none() {
                current = next.clone();
                continue;
            }
        }
        let ExprKind::Const(ctor_name, _) = value.get_app_fn().kind() else {
            return None;
        };
        let ctor = env.get_constructor(ctor_name)?;
        if ctor.inductive_name != proj.class {
            return None;
        }
        let args = value.get_app_args();
        if args.len() != (ctor.num_params + ctor.num_fields) as usize {
            return None;
        }
        let field = args.get((ctor.num_params + proj.field) as usize)?;
        let ExprKind::Const(f, f_levels) = field.kind() else {
            return None;
        };
        let f_info = env.get_const(f)?;
        // A field whose compiled meaning is not its value (`@[implemented_by]`
        // or `@[extern]`) never becomes a direct call: the call stays the
        // method, through the instance value `to_lcnf` already routed.
        if crate::implemented_by::has_compiler_attr(env, f) {
            return None;
        }
        if f_levels.len() != f_info.level_params.len() || f_levels.iter().any(Level::has_params) {
            return None;
        }
        return Some(f.clone());
    }
    None
}

/// `true` iff `ty`, after its leading Pi binders, is a `Sort` (a type
/// former's type, or a motive's).
fn ends_in_sort(ty: &Expr) -> bool {
    let mut t = ty;
    while let ExprKind::Pi(_, _, body) = t.kind() {
        t = body;
    }
    matches!(t.kind(), ExprKind::Sort(_))
}

/// `true` iff the resolved field `f` is a constant the lowered body may call
/// directly as `f x…`: not a theorem, type former, recursor or quotient
/// primitive, returning data, and FIRST-ORDER — no binder of its type ranges
/// over a `Sort` (a type argument, a `Prop` argument, or a recursor motive,
/// each of which `to_lcnf`/`to_mono` treats specially at a source-level
/// call).
fn runtime_callable_field(env: &Environment, f: &Name) -> bool {
    let Some(info) = env.get_const(f) else {
        return false;
    };
    if info.kind == ConstantKind::Theorem
        || env.get_inductive(f).is_some()
        || env.get_recursor(f).is_some()
        || env.get_quot(f).is_some()
    {
        return false;
    }
    let mut t = &info.type_;
    while let ExprKind::Pi(_, dom, body) = t.kind() {
        if ends_in_sort(dom) {
            return false;
        }
        t = body;
    }
    !ends_in_sort(t)
}

/// `true` iff `value` is a fixed point of `to_mono`'s let-value transform.
///
/// The pass runs AFTER `to_mono`, so what it emits must already be the mono
/// form the pipeline gives a source-level `f x…`. `to_mono` rewrites some
/// callees for representation: `Nat.succ n` to `Nat.add n 1`, a
/// trivial-structure constructor to its single relevant field, `Decidable`
/// to `Bool`, `Quot.mk` to its payload, a Prop-valued call to erased.
/// Emitting such a call raw miscompiles it (measured: `⟨Nat.succ⟩` became a
/// `clean_alloc_ctor(1, 1, 0, n)` cell where a `Nat` was expected, and a
/// trivial `Wrap.mk n` a heap cell where `Wrap` IS its `Nat` field), so
/// anything `to_mono` would change is left unresolved.
fn resolved_call_is_mono(env: &Environment, value: &LetValue) -> bool {
    use crate::to_mono::{letvalue_to_mono, LetValueTransform, ToMonoState};
    matches!(
        letvalue_to_mono(value, &ToMonoState::new(), env),
        LetValueTransform::Simple(mono) if mono == *value
    )
}

/// The number of leading Pi binders of `ty`, read syntactically.
fn pi_arity(ty: &Expr) -> usize {
    let mut n = 0;
    let mut t = ty;
    while let ExprKind::Pi(_, _, body) = t.kind() {
        n += 1;
        t = body;
    }
    n
}

/// The bit width `W` of a `UIntW.ofNat` name (`UInt8`/`16`/`32`/`64` only).
pub(crate) fn uint_of_nat_width(name: &Name) -> Option<u32> {
    match name.to_string().as_str() {
        "UInt8.ofNat" => Some(8),
        "UInt16.ofNat" => Some(16),
        "UInt32.ofNat" => Some(32),
        "UInt64.ofNat" => Some(64),
        _ => None,
    }
}

/// `UIntW.ofNat n` as a value: `n mod 2^W` (`W ∈ {8, 16, 32, 64}`).
///
/// Only the lowest limb of `n` matters because every width divides 64.
pub(crate) fn fold_uint_of_nat(width: u32, n: &BigNat) -> u64 {
    let low = n.limbs().first().copied().unwrap_or(0);
    if width >= 64 {
        low
    } else {
        low & ((1u64 << width) - 1)
    }
}

/// The carrier type name of a `UIntW.ofNat` name.
fn uint_carrier(width: u32) -> &'static str {
    match width {
        8 => "UInt8",
        16 => "UInt16",
        32 => "UInt32",
        _ => "UInt64",
    }
}

/// `true` iff `ty` is exactly one of the `UInt8`/`16`/`32`/`64` carriers.
fn is_uint_carrier(ty: &Expr) -> bool {
    [8, 16, 32, 64]
        .into_iter()
        .any(|w| is_const_named(ty, uint_carrier(w)))
}

/// `true` iff `ty` is exactly the nullary constant `name`.
fn is_const_named(ty: &Expr, name: &str) -> bool {
    matches!(ty.kind(), ExprKind::Const(n, levels) if levels.is_empty() && n.to_string() == name)
}

/// The `UIntW.ofNat` fold is applied only where the environment's
/// `UIntW.ofNat` is a definition of type exactly `Nat → UIntW`.
fn uint_of_nat_well_typed(env: &Environment, name: &Name, width: u32) -> bool {
    let Some(info) = env.get_const(name) else {
        return false;
    };
    if info.kind != ConstantKind::Definition || !info.level_params.is_empty() {
        return false;
    }
    match info.type_.kind() {
        ExprKind::Pi(_, dom, cod) => {
            is_const_named(dom, "Nat") && is_const_named(cod, uint_carrier(width))
        }
        _ => false,
    }
}

/// The folder: tracks in-scope instance and `Nat`-literal bindings and
/// rewrites let values.
struct ResolveFolder<'a> {
    env: &'a Environment,
    /// fvar → the nullary constant it is bound to (`let inst := I`).
    instances: HashMap<FVarId, Name>,
    /// In-scope applications for closed-declaration projection normalization.
    /// None preserves the existing path for parameterized declarations.
    apps: Option<HashMap<FVarId, (Name, Vec<Arg>)>>,
    /// fvar → the `Nat` literal it is bound to (never a typed `UIntW` one).
    nat_lits: HashMap<FVarId, BigNat>,
    /// Memoized [`class_projection`] results.
    projections: HashMap<Name, Option<ClassProjection>>,
    /// Number of rewrites performed.
    rewrites: usize,
}

impl ResolveFolder<'_> {
    fn projection(&mut self, name: &Name) -> Option<ClassProjection> {
        if let Some(cached) = self.projections.get(name) {
            return cached.clone();
        }
        let found = class_projection(self.env, name);
        self.projections.insert(name.clone(), found.clone());
        found
    }

    /// The devirtualized value of a class-method call, if the rule applies.
    fn resolve_method(&mut self, name: &Name, args: &[Arg]) -> Option<LetValue> {
        let proj = self.projection(name)?;
        let Some(Arg::FVar(inst)) = args.get(proj.inst_pos) else {
            return None;
        };
        let instance = self.instances.get(inst)?.clone();
        let f = known_instance_field(self.env, &instance, &proj)?;
        let method_args = &args[proj.inst_pos + 1..];
        let f_ty = &self.env.get_const(&f)?.type_;
        if method_args.is_empty()
            || method_args.len() != pi_arity(f_ty)
            || !runtime_callable_field(self.env, &f)
        {
            return None;
        }
        let resolved = LetValue::Const {
            name: f,
            levels: vec![],
            args: method_args.to_vec(),
        };
        resolved_call_is_mono(self.env, &resolved).then_some(resolved)
    }

    /// The typed literal of `UIntW.ofNat <Nat literal>` at declared type
    /// exactly `UIntW`, if the fold applies.
    fn fold_of_nat(&self, decl_ty: &Expr, name: &Name, args: &[Arg]) -> Option<LetValue> {
        let width = uint_of_nat_width(name)?;
        let [Arg::FVar(n)] = args else {
            return None;
        };
        let n = self.nat_lits.get(n)?;
        if !is_const_named(decl_ty, uint_carrier(width))
            || !uint_of_nat_well_typed(self.env, name, width)
        {
            return None;
        }
        Some(LetValue::Lit(Literal::Nat(BigNat::from_u64(
            fold_uint_of_nat(width, n),
        ))))
    }

    fn scoped<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        let instances = self.instances.clone();
        let apps = self.apps.clone();
        let nat_lits = self.nat_lits.clone();
        let out = f(self);
        self.instances = instances;
        self.apps = apps;
        self.nat_lits = nat_lits;
        out
    }
}

impl CodeFolder for ResolveFolder<'_> {
    fn fold_let(&mut self, decl: LetDecl, body: Code) -> Code {
        self.instances.remove(&decl.fvar_id);
        if let Some(apps) = &mut self.apps {
            apps.remove(&decl.fvar_id);
        }
        self.nat_lits.remove(&decl.fvar_id);
        let rewritten = match &decl.value {
            LetValue::Const { name, args, .. } => self
                .resolve_method(name, args)
                .or_else(|| project_instance_argument(self.env, name, args, self.apps.as_ref()?))
                .or_else(|| self.fold_of_nat(&decl.ty, name, args)),
            _ => None,
        };
        let value = match rewritten {
            Some(value) => {
                self.rewrites += 1;
                value
            }
            None => decl.value.clone(),
        };
        match &value {
            LetValue::Const { name, args, .. } if args.is_empty() => {
                self.instances.insert(decl.fvar_id, name.clone());
            }
            // A `Nat` literal is a `Nat` whatever its binder's (possibly
            // erased, `lcAny`/`_`) declared type says — except the typed
            // `UIntW` literal this very fold produces.
            LetValue::Lit(Literal::Nat(n)) if !is_uint_carrier(&decl.ty) => {
                self.nat_lits.insert(decl.fvar_id, n.clone());
            }
            _ => {}
        }
        if let (Some(apps), LetValue::Const { name, args, .. }) = (&mut self.apps, &value) {
            apps.insert(decl.fvar_id, (name.clone(), args.clone()));
        }
        Code::Let(LetDecl { value, ..decl }, Box::new(self.fold_code(&body)))
    }

    fn fold_fun(&mut self, decl: FunDecl, body: Code) -> Code {
        let fun_body = self.scoped(|s| s.fold_code(&decl.body));
        Code::Fun(
            FunDecl {
                body: Box::new(fun_body),
                ..decl
            },
            Box::new(self.fold_code(&body)),
        )
    }

    fn fold_join_point(&mut self, decl: FunDecl, body: Code) -> Code {
        let jp_body = self.scoped(|s| s.fold_code(&decl.body));
        Code::JoinPoint(
            FunDecl {
                body: Box::new(jp_body),
                ..decl
            },
            Box::new(self.fold_code(&body)),
        )
    }

    fn fold_cases(&mut self, cases: crate::lcnf::Cases) -> Code {
        let alts = cases
            .alts
            .into_iter()
            .map(|alt| self.scoped(|s| s.fold_alt(alt)))
            .collect();
        Code::Cases(crate::lcnf::Cases { alts, ..cases })
    }
}

/// Apply known-instance resolution (and the companion `UIntW.ofNat` fold) to
/// a declaration. The result is `decl` unchanged when nothing applies; after
/// any rewrite, a dead-code sweep removes the bindings it orphaned.
pub(crate) fn resolve_known_instances(decl: &Decl, env: &Environment) -> Decl {
    let DeclValue::Code(code) = &decl.body else {
        return decl.clone();
    };
    let mut folder = ResolveFolder {
        env,
        instances: HashMap::new(),
        apps: decl.params.is_empty().then(HashMap::new),
        nat_lits: HashMap::new(),
        projections: HashMap::new(),
        rewrites: 0,
    };
    let body = folder.fold_code(code);
    if folder.rewrites == 0 {
        return decl.clone();
    }
    let body = super::dce::eliminate_dead_code_in_code(&body);
    Decl {
        body: DeclValue::Code(Box::new(body)),
        ..decl.clone()
    }
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod projection_tests;

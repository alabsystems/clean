// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Carrier-primitive resolution (Trust plan step 3.2, C1).
//!
//! The Rust-ABI pipeline compiles a Lean function at its carrier types, where
//! every prelude operation on `UIntW`, `Bool` and `Nat` is ONE machine
//! operation (`crate::carrier_prims`). What reaches the back end after
//! `to_mono` and `resolve_instances` is rarely that operation by name: the
//! elaborator spells `a ≤ b` through the instance `instDecidableUInt64Le`,
//! `a && b` through `and`, `decide (a < b)` through `decide`, `a == b` through
//! `BEq.beq` over `instBEqOfDecidableEq`, and a `Nat` numeral through
//! `OfNat.ofNat` over `instOfNatNat`. Measured on Trust's general-lane
//! configuration before this pass: every one of those stayed a boxed call to
//! an undefined `l_*` symbol.
//!
//! # The rules — each reads the kernel VALUE, never a name
//!
//! 1. **δ/η alias.** `let r := I x…` where `I`'s value is a bare constant `P`
//!    or exactly `λ y₁…yₙ, P y₁…yₙ` becomes `let r := P x…`, chased at most
//!    [`MAX_ALIAS_STEPS`] times, and only when the chain ends at a native
//!    carrier primitive whose arity is the call's. (`instDecidableUInt64Le :=
//!    UInt64.decLe`, `and := Bool.and`, `decide := λ p h, Decidable.decide p
//!    h` — measured values, pinned by the tests.)
//! 2. **A class method through an instance APPLICATION whose field is one of
//!    the instance's own arguments.** `let r := C.method τ… d` with `d` bound
//!    to `I a₁…aₖ`, where `I` is a registered instance whose value is
//!    `λ y₁…yₖ, C.mk p… f…` and the selected field is `yⱼ`: `r` is `aⱼ`.
//!    (`OfNat.ofNat Nat n (instOfNatNat m)` is `m`.) The method must be the
//!    projection out of a one-constructor structure
//!    ([`crate::opt::resolve_instances::projection::structure_projection`])
//!    and take no further arguments.
//! 3. **`BEq` through `instBEqOfDecidableEq`.** `let r := BEq.beq τ d a b` with
//!    `d` bound to `instBEqOfDecidableEq τ e` and `e` bound to the nullary
//!    instance `J`: when `instBEqOfDecidableEq`'s value is exactly
//!    `λ α inst, BEq.mk α (λ a b, decide (a = b) (decEq α inst a b))` (with
//!    `decEq := λ α inst a b, inst a b`) and `decide`
//!    itself resolves (rule 1) to `Decidable.decide` — the identity on a
//!    `Decidable`'s `Bool` representation — `r` is `J a b`, which rule 1 then
//!    resolves (`instDecidableEqUInt32 := UInt32.decEq`).
//!
//! Anything outside the rules is left exactly as it was: a missed rewrite
//! leaves a call the Rust-ABI emitter refuses BY NAME, never a guessed body.
//! A dead-code sweep follows a successful rewrite.
//!
//! The ordinary object-ABI pipeline uses only rule 1 aliases ending at a
//! `CarrierPrim::Cmp`. This is a representation step before RC, including at
//! O0; class-field, BEq, Bool, Nat and arithmetic resolution remain exclusive
//! to the existing full resolver and known-instance pass.

use crate::carrier_prims::{carrier_prim, CarrierPrim};
use crate::lcnf::{Arg, Code, Decl, DeclValue, FunDecl, LetDecl, LetValue};
#[cfg(test)]
pub(crate) use crate::opt::resolve_instances::projection::instance_field_is_argument;
use crate::opt::resolve_instances::projection::project_instance_argument;
use crate::CodeFolder;
use clean_kernel::env::ConstantKind;
use clean_kernel::{Environment, Expr, ExprKind, FVarId, Name};
use std::collections::HashMap;

/// At most this many aliases are unfolded on the way to a primitive.
pub(crate) const MAX_ALIAS_STEPS: usize = 4;

/// `Some(P)` iff `value` is the bare constant `P` (no universe arguments) or
/// exactly its η-expansion `λ y₁…yₙ, P y₁…yₙ`, binders in order.
fn eta_alias(value: &Expr) -> Option<Name> {
    let mut n = 0usize;
    let mut body = value;
    while let ExprKind::Lam(_, _, inner) = body.kind() {
        n += 1;
        body = inner;
    }
    let ExprKind::Const(target, levels) = body.get_app_fn().kind() else {
        return None;
    };
    if !levels.is_empty() {
        return None;
    }
    let args = body.get_app_args();
    if args.len() != n {
        return None;
    }
    let in_order = args
        .iter()
        .enumerate()
        .all(|(k, a)| matches!(a.kind(), ExprKind::BVar(i) if *i as usize + k + 1 == n));
    in_order.then(|| target.clone())
}

/// The primitive the alias chain from `name` reaches (rule 1), with the
/// primitive's own name. `name` itself may already be a primitive.
pub(crate) fn alias_target(
    env: &Environment,
    name: &Name,
    nat_handles: bool,
) -> Option<(Name, CarrierPrim)> {
    let mut current = name.clone();
    for _ in 0..=MAX_ALIAS_STEPS {
        if let Some(prim) = carrier_prim(&current, nat_handles) {
            return Some((current, prim));
        }
        if env.get_implemented_by(&current).is_some() {
            return None;
        }
        let info = env.get_const(&current)?;
        if info.kind != ConstantKind::Definition {
            return None;
        }
        current = eta_alias(info.value.as_ref()?)?;
    }
    None
}

/// Rule 3's reading of `BEq.beq`: its value is exactly
/// `λ α inst a b, BEq.rec α motive (λ f, f) inst a b`, so
/// `BEq.beq α (BEq.mk α f) a b` ι-reduces to `f a b`.
pub(crate) fn is_beq_method(env: &Environment, name: &Name) -> bool {
    let Some(value) = env.get_const(name).and_then(|info| info.value.as_ref()) else {
        return false;
    };
    let mut body = value;
    for _ in 0..4 {
        let ExprKind::Lam(_, _, inner) = body.kind() else {
            return false;
        };
        body = inner;
    }
    let head_is_rec =
        matches!(body.get_app_fn().kind(), ExprKind::Const(c, _) if c.to_string() == "BEq.rec");
    let args = body.get_app_args();
    let is_bvar = |e: &Expr, n: u32| matches!(e.kind(), ExprKind::BVar(i) if *i == n);
    let minor_is_identity = |e: &Expr| matches!(e.kind(), ExprKind::Lam(_, _, b) if is_bvar(b, 0));
    head_is_rec
        && matches!(
            args.as_slice(),
            [alpha, _motive, minor, inst, a, b]
                if is_bvar(alpha, 3)
                    && minor_is_identity(minor)
                    && is_bvar(inst, 2)
                    && is_bvar(a, 1)
                    && is_bvar(b, 0)
        )
}

/// Rule 3's reading of `instBEqOfDecidableEq`: its value is exactly
/// `λ α inst, BEq.mk α (λ a b, decide (Eq α a b) d)` where the decision `d`
/// is `inst a b` or `decEq α inst a b` (the prelude spells the latter).
pub(crate) fn is_beq_of_decidable_eq(env: &Environment, name: &Name) -> bool {
    if !env.is_instance(name) || env.get_implemented_by(name).is_some() {
        return false;
    }
    let Some(info) = env.get_const(name) else {
        return false;
    };
    let Some(value) = info.value.as_ref() else {
        return false;
    };
    let ExprKind::Lam(_, _, body) = value.kind() else {
        return false;
    };
    let ExprKind::Lam(_, _, body) = body.kind() else {
        return false;
    };
    let is_const =
        |e: &Expr, n: &str| matches!(e.kind(), ExprKind::Const(c, _) if c.to_string() == n);
    let is_bvar = |e: &Expr, n: u32| matches!(e.kind(), ExprKind::BVar(i) if *i == n);
    if !is_const(body.get_app_fn(), "BEq.mk") {
        return false;
    }
    let mk_args = body.get_app_args();
    let [alpha, method] = mk_args.as_slice() else {
        return false;
    };
    if !is_bvar(alpha, 1) {
        return false;
    }
    let ExprKind::Lam(_, _, method) = method.kind() else {
        return false;
    };
    let ExprKind::Lam(_, _, method) = method.kind() else {
        return false;
    };
    // Under α (3), inst (2), a (1), b (0).
    if !is_const(method.get_app_fn(), "decide") {
        return false;
    }
    let decide_args = method.get_app_args();
    let [prop, decision] = decide_args.as_slice() else {
        return false;
    };
    let prop_is_eq = is_const(prop.get_app_fn(), "Eq") && {
        let eq_args = prop.get_app_args();
        matches!(eq_args.as_slice(), [t, a, b] if is_bvar(t, 3) && is_bvar(a, 1) && is_bvar(b, 0))
    };
    // `inst a b`, or `decEq α inst a b` where `decEq` is `λ α inst a b, inst a b`.
    let decision_is_inst_a_b =
        (is_bvar(decision.get_app_fn(), 2) && {
            let dec_args = decision.get_app_args();
            matches!(dec_args.as_slice(), [a, b] if is_bvar(a, 1) && is_bvar(b, 0))
        }) || (is_const(decision.get_app_fn(), "decEq") && is_dec_eq_application(env) && {
            let dec_args = decision.get_app_args();
            matches!(dec_args.as_slice(), [t, inst, a, b]
            if is_bvar(t, 3) && is_bvar(inst, 2) && is_bvar(a, 1) && is_bvar(b, 0))
        });
    prop_is_eq && decision_is_inst_a_b
}

/// `decEq`'s value is exactly `λ α inst a b, inst a b`.
fn is_dec_eq_application(env: &Environment) -> bool {
    let Some(value) = env
        .get_const(&Name::from_string("decEq"))
        .and_then(|info| info.value.as_ref())
    else {
        return false;
    };
    let mut body = value;
    for _ in 0..4 {
        let ExprKind::Lam(_, _, inner) = body.kind() else {
            return false;
        };
        body = inner;
    }
    matches!(body.get_app_fn().kind(), ExprKind::BVar(2))
        && matches!(
            body.get_app_args().as_slice(),
            [a, b] if matches!(a.kind(), ExprKind::BVar(1)) && matches!(b.kind(), ExprKind::BVar(0))
        )
}

/// Select the representation rules without duplicating alias-chain semantics.
#[derive(Clone, Copy, PartialEq, Eq)]
enum ResolutionScope {
    All,
    UIntComparisons,
}

/// The folder: tracks in-scope constant applications and rewrites let values.
struct CarrierFolder<'a> {
    env: &'a Environment,
    nat_handles: bool,
    scope: ResolutionScope,
    /// fvar → the constant application it is bound to (`let x := I a…`).
    apps: HashMap<FVarId, (Name, Vec<Arg>)>,
    rewrites: usize,
}

impl CarrierFolder<'_> {
    /// A checked instance bridge can store a projection of one of its own
    /// dictionary arguments: `lambda a d, C.mk ... (D.method a d)`.
    /// Read both projections and the final instance field from their values.
    /// Only a saturated call ending at an existing primitive is rewritten.
    fn resolve_projected_instance(&self, method: &Name, args: &[Arg]) -> Option<LetValue> {
        use crate::opt::resolve_instances::{known_instance_field, projection::class_projection};
        if self.scope != ResolutionScope::All {
            return None;
        }
        let outer = class_projection(self.env, method)?;
        let Arg::FVar(dict) = args.get(outer.inst_pos)? else {
            return None;
        };
        let (bridge, bridge_args) = self.apps.get(dict)?;
        if !self.env.is_instance(bridge)
            || crate::implemented_by::has_compiler_attr(self.env, bridge)
            || self.env.is_noncomputable(bridge)
        {
            return None;
        }
        let info = self.env.get_const(bridge)?;
        if info.kind != ConstantKind::Definition {
            return None;
        }
        let mut body = info.value.as_ref()?;
        let mut arity = 0;
        while let ExprKind::Lam(_, _, inner) = body.kind() {
            arity += 1;
            body = inner;
        }
        if arity != bridge_args.len() {
            return None;
        }
        let ExprKind::Const(ctor_name, _) = body.get_app_fn().kind() else {
            return None;
        };
        let ctor = self.env.get_constructor(ctor_name)?;
        if ctor.inductive_name != outer.class
            || crate::implemented_by::has_compiler_attr(self.env, ctor_name)
            || self.env.is_noncomputable(ctor_name)
        {
            return None;
        }
        let fields = body.get_app_args();
        if fields.len() != (ctor.num_params + ctor.num_fields) as usize {
            return None;
        }
        let field = fields.get((ctor.num_params + outer.field) as usize)?;
        let ExprKind::Const(inner_method, _) = field.get_app_fn().kind() else {
            return None;
        };
        let inner = class_projection(self.env, inner_method)?;
        let inner_class = self.env.get_inductive(&inner.class)?;
        let inner_ctor = inner_class.constructor_names.first()?;
        if crate::implemented_by::has_compiler_attr(self.env, inner_ctor)
            || self.env.is_noncomputable(inner_ctor)
        {
            return None;
        }
        let projected = field.get_app_args();
        if projected.len() != inner.inst_pos + 1 {
            return None;
        }
        // Every projection argument must be one of this bridge's binders.
        // No nontrivial field computation is treated as a projection.
        let mut forwarded = Vec::new();
        for argument in projected {
            let ExprKind::BVar(index) = argument.kind() else {
                return None;
            };
            let index = arity.checked_sub(*index as usize + 1)?;
            forwarded.push(bridge_args.get(index)?);
        }
        let Arg::FVar(inner_dict) = forwarded[inner.inst_pos] else {
            return None;
        };
        let (instance, instance_args) = self.apps.get(inner_dict)?;
        if !instance_args.is_empty() {
            return None;
        }
        let target = known_instance_field(self.env, instance, &inner)?;
        if self.env.is_noncomputable(&target) {
            return None;
        }
        let primitive = carrier_prim(&target, self.nat_handles)?;
        let operands = args.get(outer.inst_pos + 1..)?;
        if operands.len() != primitive.params().len() {
            return None;
        }
        Some(LetValue::Const {
            name: target,
            levels: vec![],
            args: operands.to_vec(),
        })
    }

    /// Rule 1.
    fn resolve_alias(&self, name: &Name, args: &[Arg]) -> Option<LetValue> {
        let (target, prim) = alias_target(self.env, name, self.nat_handles)?;
        if target == *name
            || prim.params().len() != args.len()
            || (self.scope == ResolutionScope::UIntComparisons
                && !matches!(prim, CarrierPrim::Cmp(..)))
        {
            return None;
        }
        Some(LetValue::Const {
            name: target,
            levels: vec![],
            args: args.to_vec(),
        })
    }

    /// Rule 2.
    fn resolve_field_argument(&self, name: &Name, args: &[Arg]) -> Option<LetValue> {
        project_instance_argument(self.env, name, args, &self.apps)
    }

    /// Rule 3.
    fn resolve_beq(&self, name: &Name, args: &[Arg]) -> Option<LetValue> {
        if name.to_string() != "BEq.beq" || !is_beq_method(self.env, name) {
            return None;
        }
        let [_ty, Arg::FVar(dict), a, b] = args else {
            return None;
        };
        let (bridge, bridge_args) = self.apps.get(dict)?;
        if bridge.to_string() != "instBEqOfDecidableEq" || !is_beq_of_decidable_eq(self.env, bridge)
        {
            return None;
        }
        let [_, Arg::FVar(dec)] = bridge_args.as_slice() else {
            return None;
        };
        let (decision, decision_args) = self.apps.get(dec)?;
        if !decision_args.is_empty() {
            return None;
        }
        // `decide` must be the identity on the decision's `Bool`.
        let decide = Name::from_string("decide");
        if !matches!(
            alias_target(self.env, &decide, self.nat_handles),
            Some((_, CarrierPrim::Decide))
        ) {
            return None;
        }
        self.resolve_alias(decision, &[a.clone(), b.clone()])
    }

    fn scoped<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        let apps = self.apps.clone();
        let out = f(self);
        self.apps = apps;
        out
    }
}

impl CodeFolder for CarrierFolder<'_> {
    fn fold_let(&mut self, decl: LetDecl, body: Code) -> Code {
        self.apps.remove(&decl.fvar_id);
        let rewritten = match &decl.value {
            LetValue::Const { name, levels, args }
                if self.scope == ResolutionScope::UIntComparisons =>
            {
                // Carrier comparisons and the accepted aliases are monomorphic.
                // Do not silently erase an unexpected universe instantiation.
                if levels.is_empty() {
                    self.resolve_alias(name, args)
                } else {
                    None
                }
            }
            LetValue::Const { name, args, .. } => self
                .resolve_beq(name, args)
                .or_else(|| self.resolve_field_argument(name, args))
                .or_else(|| self.resolve_projected_instance(name, args))
                .or_else(|| self.resolve_alias(name, args)),
            _ => None,
        };
        let value = match rewritten {
            Some(value) => {
                self.rewrites += 1;
                value
            }
            None => decl.value.clone(),
        };
        if let LetValue::Const { name, args, .. } = &value {
            self.apps.insert(decl.fvar_id, (name.clone(), args.clone()));
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

/// Apply carrier-primitive resolution to `decl`. The result is `decl`
/// unchanged when no rule applies; after any rewrite, a dead-code sweep
/// removes the bindings it orphaned.
pub(crate) fn resolve_carrier_prims(decl: &Decl, env: &Environment, nat_handles: bool) -> Decl {
    resolve_with_scope(decl, env, nat_handles, ResolutionScope::All)
}

/// Lower only value-checked aliases of fixed-width UInt comparisons before RC.
/// This deliberately does not resolve class fields or the BEq bridge, or enable
/// Nat handles. Partial/overapplied calls and non-identity aliases stay intact.
pub(crate) fn resolve_uint_comparison_aliases(decl: &Decl, env: &Environment) -> Decl {
    resolve_with_scope(decl, env, false, ResolutionScope::UIntComparisons)
}

fn resolve_with_scope(
    decl: &Decl,
    env: &Environment,
    nat_handles: bool,
    scope: ResolutionScope,
) -> Decl {
    let DeclValue::Code(code) = &decl.body else {
        return decl.clone();
    };
    let mut folder = CarrierFolder {
        env,
        nat_handles,
        scope,
        apps: HashMap::new(),
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

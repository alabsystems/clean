// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rust to clean Translation
//!
//! This module provides translation from Rust semantics to clean kernel terms,
//! enabling verification of Rust programs in clean.
//!
//! ## Translation Strategy
//!
//! Rust programs are translated to clean using:
//!
//! 1. **Types**: Rust types become clean inductive types with ownership predicates
//! 2. **Values**: Rust values become clean terms
//! 3. **Expressions**: Rust expressions become function applications
//! 4. **Ownership**: Borrow rules become Lean-facing proof obligations
//!
//! ## Ownership as Proofs
//!
//! The design goal is that ownership rules translate to proof requirements:
//!
//! - `&T` requires proof that the value is valid
//! - `&mut T` requires proof of exclusive access
//! - Moving requires proof that no borrows exist
//!
//! The `ProofObligation` type and goal constructors are consumed by
//! `proof_bundle.rs`, which turns parsed source, lowered VIR, NLL results, and
//! aliasing observations into a reusable Lean-facing ownership bundle.

use crate::error::RustSemError;
use crate::ownership::{BorrowChecker, BorrowError, OwnershipState, Place};
use crate::types::{Lifetime, Mutability, RustType};
use crate::values::Value as RustValue;

use clean_kernel::env::Environment;
use clean_kernel::expr::{BinderData, BinderInfo, FVarId};
use clean_kernel::level::Level as LeanLevel;
use clean_kernel::name::Name as LeanName;
use clean_kernel::Expr as LeanExpr;

use std::collections::HashMap;

/// Helper to create a Name from a string like "Foo.bar"
fn make_name(s: &str) -> LeanName {
    LeanName::from_string(s)
}

/// Helper to create a constant expression
fn const_expr(name: &str, levels: Vec<LeanLevel>) -> LeanExpr {
    LeanExpr::const_(make_name(name), levels)
}

/// Helper to create a nat literal expression
fn nat_lit(n: u64) -> LeanExpr {
    LeanExpr::nat_lit(n)
}

/// Translate a Rust lifetime to a clean expression
fn translate_lifetime(lt: &Lifetime) -> LeanExpr {
    match lt {
        Lifetime::Static => const_expr("RustLifetime.static", vec![]),
        Lifetime::Named(name) => LeanExpr::app(
            const_expr("RustLifetime.named", vec![]),
            LeanExpr::str_lit(name),
        ),
        Lifetime::Anonymous(id) => LeanExpr::app(
            const_expr("RustLifetime.anonymous", vec![]),
            nat_lit(*id as u64),
        ),
        Lifetime::Existential(id) => LeanExpr::app(
            const_expr("RustLifetime.existential", vec![]),
            nat_lit(*id as u64),
        ),
    }
}

/// Translation context
#[derive(Debug)]
pub struct TranslationContext {
    /// clean environment for definitions
    pub env: Environment,
    /// Mapping from Rust type names to clean names
    pub type_map: HashMap<String, LeanName>,
    /// Current local variable context (Rust name → de Bruijn level)
    pub locals: Vec<(String, RustType)>,
    /// Ownership state for proof generation
    pub ownership: OwnershipState,
    /// Generated proof obligations
    proof_obligations: Vec<ProofObligation>,
    /// Active type parameter substitutions (TypeVar id → concrete RustType).
    ///
    /// When translating inside a generic context with known type arguments
    /// (e.g., monomorphized function body), this maps type parameter ids to
    /// the concrete types they should be replaced with. Empty when no
    /// generic context is active.
    pub type_param_subst: HashMap<u32, RustType>,
    /// Active mapping from generic type-parameter ids (`TypeVar.id`) to the
    /// fresh free variables that stand in for them while translating the body
    /// of a *hoisted* generic type/signature.
    ///
    /// Installed only by [`translate_generic_type`]. When a `TypeParam` is
    /// found in this map, `translate_type` emits `Expr::fvar(..)` so the
    /// parameter can later be abstracted into a `Π` binder (a real
    /// `∀`-quantified `Sort` variable). Empty in the monomorphic /
    /// non-generic case, which preserves the legacy opaque `RustTypeParam`
    /// encoding.
    pub type_param_fvars: HashMap<u32, FVarId>,
}

/// A proof obligation generated during translation
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ProofObligationKind {
    SharedBorrowValid,
    MutBorrowExclusive,
    MoveWithoutLiveBorrows,
    Custom,
}

#[derive(Debug, Clone)]
pub struct ProofObligation {
    /// High-level category of obligation.
    pub kind: ProofObligationKind,
    /// Function containing the obligation site, when known.
    pub function: Option<String>,
    /// Description of what needs to be proven
    pub description: String,
    /// The clean type (proposition) to prove
    pub goal: LeanExpr,
    /// Location in original Rust code
    pub location: Option<String>,
}

impl TranslationContext {
    /// Create a new translation context
    pub fn new() -> Self {
        let mut type_map = HashMap::new();

        // Standard type mappings
        type_map.insert("bool".to_string(), make_name("Bool"));
        type_map.insert("u8".to_string(), make_name("UInt8"));
        type_map.insert("u16".to_string(), make_name("UInt16"));
        type_map.insert("u32".to_string(), make_name("UInt32"));
        type_map.insert("u64".to_string(), make_name("UInt64"));
        type_map.insert("i8".to_string(), make_name("Int8"));
        type_map.insert("i16".to_string(), make_name("Int16"));
        type_map.insert("i32".to_string(), make_name("Int32"));
        type_map.insert("i64".to_string(), make_name("Int64"));
        type_map.insert("f32".to_string(), make_name("Float32"));
        type_map.insert("f64".to_string(), make_name("Float"));
        type_map.insert("String".to_string(), make_name("String"));
        type_map.insert("char".to_string(), make_name("Char"));

        Self {
            env: Environment::new(),
            type_map,
            locals: Vec::new(),
            ownership: OwnershipState::new(),
            proof_obligations: Vec::new(),
            type_param_subst: HashMap::new(),
            type_param_fvars: HashMap::new(),
        }
    }

    /// Push a local variable
    pub fn push_local(&mut self, name: String, ty: RustType) {
        self.locals.push((name, ty));
    }

    /// Pop a local variable
    pub fn pop_local(&mut self) -> Option<(String, RustType)> {
        self.locals.pop()
    }

    /// Look up a local variable (returns de Bruijn index)
    pub fn lookup_local(&self, name: &str) -> Option<(u32, &RustType)> {
        for (idx, (n, ty)) in self.locals.iter().rev().enumerate() {
            if n == name {
                // SAFETY: Local variable count is bounded by practical stack depth limits,
                // which are far below u32::MAX. Use saturating conversion for defense.
                let idx_u32 = u32::try_from(idx).unwrap_or(u32::MAX);
                return Some((idx_u32, ty));
            }
        }
        None
    }

    /// Add a proof obligation
    pub fn add_obligation(&mut self, description: &str, goal: LeanExpr) {
        self.add_obligation_with_metadata(
            ProofObligationKind::Custom,
            None,
            description,
            goal,
            None,
        );
    }

    /// Add a proof obligation with bundle-facing metadata.
    pub fn add_obligation_with_metadata(
        &mut self,
        kind: ProofObligationKind,
        function: Option<String>,
        description: &str,
        goal: LeanExpr,
        location: Option<String>,
    ) {
        self.proof_obligations.push(ProofObligation {
            kind,
            function,
            description: description.to_string(),
            goal,
            location,
        });
    }

    /// Get all proof obligations
    pub fn obligations(&self) -> &[ProofObligation] {
        &self.proof_obligations
    }

    /// Set type parameter bindings for generic context translation.
    ///
    /// Given type parameter declarations (from a generic function/struct) and
    /// concrete type arguments (from a call site or instantiation), builds and
    /// installs the substitution map. Returns `false` on arity mismatch.
    pub fn set_type_params(
        &mut self,
        type_param_defs: &[crate::types::TypeParamDef],
        type_args: &[RustType],
    ) -> bool {
        match RustType::build_type_param_subst(type_param_defs, type_args) {
            Some(subst) => {
                self.type_param_subst = subst;
                true
            }
            None => false,
        }
    }

    /// Clear type parameter bindings when leaving a generic context.
    pub fn clear_type_params(&mut self) {
        self.type_param_subst.clear();
    }
}

impl Default for TranslationContext {
    fn default() -> Self {
        Self::new()
    }
}

/// Translate a Rust ownership place to an abstract Lean term.
pub fn translate_place(place: &Place) -> LeanExpr {
    match place {
        Place::Local(index) => LeanExpr::app(
            const_expr("RustPlace.local", vec![]),
            nat_lit(*index as u64),
        ),
        Place::Static(name) => LeanExpr::app(
            const_expr("RustPlace.static", vec![]),
            LeanExpr::str_lit(name),
        ),
        Place::Field { base, field } => LeanExpr::app(
            LeanExpr::app(const_expr("RustPlace.field", vec![]), translate_place(base)),
            LeanExpr::str_lit(field),
        ),
        Place::Index { base, index } => LeanExpr::app(
            LeanExpr::app(const_expr("RustPlace.index", vec![]), translate_place(base)),
            translate_place(index),
        ),
        Place::Deref(base) => {
            LeanExpr::app(const_expr("RustPlace.deref", vec![]), translate_place(base))
        }
        Place::Downcast { base, variant } => LeanExpr::app(
            LeanExpr::app(
                const_expr("RustPlace.downcast", vec![]),
                translate_place(base),
            ),
            LeanExpr::str_lit(variant),
        ),
    }
}

/// Build a proof goal for `&T` validity.
pub fn mk_shared_borrow_valid_goal(place: &Place) -> LeanExpr {
    LeanExpr::app(
        const_expr("RustOwnership.sharedBorrowValid", vec![]),
        translate_place(place),
    )
}

/// Build a proof goal for `&mut T` exclusivity.
pub fn mk_mut_borrow_exclusive_goal(place: &Place) -> LeanExpr {
    LeanExpr::app(
        const_expr("RustOwnership.mutBorrowExclusive", vec![]),
        translate_place(place),
    )
}

/// Build a proof goal for the give-back refinement of a `&mut` borrow.
///
/// States (schematically, via the `RustOwnership.giveBackRefinement` head applied
/// to the borrowed place) that the give-back view `(f_fwd, f_back)` of the `&mut`
/// borrow refines the value-at-address semantics — see
/// `designs/2026-06-29-giveback-clean-refinement.md` §4 and the executable
/// `value_at_address::step`. This builds the OBLIGATION statement only;
/// discharging it is M3 (a Clean refinement certificate), not done here.
pub fn mk_give_back_refinement_goal(place: &Place) -> LeanExpr {
    LeanExpr::app(
        const_expr("RustOwnership.giveBackRefinement", vec![]),
        translate_place(place),
    )
}

/// Build a proof goal for move-without-live-borrows.
pub fn mk_move_clear_goal(place: &Place) -> LeanExpr {
    LeanExpr::app(
        const_expr("RustOwnership.moveWithoutLiveBorrows", vec![]),
        translate_place(place),
    )
}

/// Build a proof goal summarizing a successful aliasing run.
pub fn mk_aliasing_clean_goal(summary: &str) -> LeanExpr {
    LeanExpr::app(
        const_expr("RustOwnership.aliasingclean", vec![]),
        LeanExpr::str_lit(summary),
    )
}

/// Build a proof goal for arithmetic panic-freedom (overflow / nonzero
/// divisor / in-range shift). The `check` string identifies the required
/// property; the goal is stated (not discharged) until integer bounds are
/// modeled. See hole 1.
pub fn mk_arithmetic_safety_goal(check: &str) -> LeanExpr {
    LeanExpr::app(
        const_expr("RustSem.arithmeticSafe", vec![]),
        LeanExpr::str_lit(check),
    )
}

/// Translate a Rust type to a clean expression
pub fn translate_type(ty: &RustType, ctx: &TranslationContext) -> LeanExpr {
    // If we have active type parameter bindings, resolve them before translating.
    if !ctx.type_param_subst.is_empty() {
        let resolved = ty.substitute_type_params(&ctx.type_param_subst);
        if &resolved != ty {
            return translate_type(&resolved, ctx);
        }
    }
    match ty {
        RustType::Unit => const_expr("Unit", vec![]),

        RustType::Bool => const_expr("Bool", vec![]),

        RustType::Char => const_expr("Char", vec![]),

        RustType::Uint(uint_ty) => {
            let name = match uint_ty {
                crate::types::UintType::U8 => "UInt8",
                crate::types::UintType::U16 => "UInt16",
                crate::types::UintType::U32 => "UInt32",
                crate::types::UintType::U64 => "UInt64",
                crate::types::UintType::U128 => "UInt128",
                crate::types::UintType::Usize => "USize",
            };
            const_expr(name, vec![])
        }

        RustType::Int(int_ty) => {
            let name = match int_ty {
                crate::types::IntType::I8 => "Int8",
                crate::types::IntType::I16 => "Int16",
                crate::types::IntType::I32 => "Int32",
                crate::types::IntType::I64 => "Int64",
                crate::types::IntType::I128 => "Int128",
                crate::types::IntType::Isize => "ISize",
            };
            const_expr(name, vec![])
        }

        RustType::Float(float_ty) => {
            let name = match float_ty {
                crate::types::FloatType::F32 => "Float32",
                crate::types::FloatType::F64 => "Float",
            };
            const_expr(name, vec![])
        }

        RustType::Reference {
            mutability, inner, ..
        } => {
            // References become dependent pairs: { r : Ref T // Valid r }
            // For now, simplify to just the inner type
            let inner_ty = translate_type(inner, ctx);
            let ref_name = match mutability {
                Mutability::Shared => "Ref",
                Mutability::Mutable => "RefMut",
            };
            LeanExpr::app(const_expr(ref_name, vec![LeanLevel::zero()]), inner_ty)
        }

        RustType::RawPtr { mutability, inner } => {
            // Raw pointers use RawPtr/RawPtrMut to distinguish from safe references
            let inner_ty = translate_type(inner, ctx);
            let ptr_name = match mutability {
                Mutability::Shared => "RawPtr",
                Mutability::Mutable => "RawPtrMut",
            };
            LeanExpr::app(const_expr(ptr_name, vec![LeanLevel::zero()]), inner_ty)
        }

        RustType::Box { inner } => {
            // Box<T> is semantically equivalent to T for verification purposes
            // (unique ownership already encoded in borrow checker)
            translate_type(inner, ctx)
        }

        RustType::Tuple(elems) => {
            if elems.is_empty() {
                const_expr("Unit", vec![])
            } else if elems.len() == 1 {
                translate_type(&elems[0], ctx)
            } else {
                // Build nested Prod type
                let mut result = translate_type(
                    elems
                        .last()
                        .expect("invariant: non-empty after is_empty guard"),
                    ctx,
                );
                for elem in elems.iter().rev().skip(1) {
                    let elem_ty = translate_type(elem, ctx);
                    result = LeanExpr::app(
                        LeanExpr::app(
                            const_expr("Prod", vec![LeanLevel::zero(), LeanLevel::zero()]),
                            elem_ty,
                        ),
                        result,
                    );
                }
                result
            }
        }

        RustType::Array { element, len } => {
            let elem_ty = translate_type(element, ctx);
            let len = len
                .as_usize(&std::collections::HashMap::new())
                .unwrap_or_default();
            // Array T n becomes Array T n in Lean
            LeanExpr::app(
                LeanExpr::app(const_expr("Array", vec![LeanLevel::zero()]), elem_ty),
                nat_lit(len as u64),
            )
        }

        RustType::Vec { element } => {
            let elem_ty = translate_type(element, ctx);
            LeanExpr::app(const_expr("Array", vec![LeanLevel::zero()]), elem_ty)
        }

        RustType::Slice { elem } => {
            // Slice [T] is dynamically sized - encode as RustSlice T
            // Unlike Array (fixed size) or Vec (heap), slices are DST views
            let elem_ty = translate_type(elem, ctx);
            LeanExpr::app(const_expr("RustSlice", vec![LeanLevel::zero()]), elem_ty)
        }

        RustType::Str => {
            // String slice str is a DST, encode as RustStr
            // This is the unsized string slice type, not String (owned)
            const_expr("RustStr", vec![])
        }

        RustType::Option { inner } => {
            let inner_ty = translate_type(inner, ctx);
            LeanExpr::app(const_expr("Option", vec![LeanLevel::zero()]), inner_ty)
        }

        RustType::Result { ok, err } => {
            let ok_ty = translate_type(ok, ctx);
            let err_ty = translate_type(err, ctx);
            LeanExpr::app(
                LeanExpr::app(
                    const_expr("Except", vec![LeanLevel::zero(), LeanLevel::zero()]),
                    err_ty,
                ),
                ok_ty,
            )
        }

        RustType::Named {
            name, type_args, ..
        } => {
            let lean_name = ctx
                .type_map
                .get(name)
                .cloned()
                .unwrap_or_else(|| make_name(name));
            let mut result = LeanExpr::const_(lean_name, vec![LeanLevel::zero()]);
            for arg in type_args {
                let arg_ty = translate_type(arg, ctx);
                result = LeanExpr::app(result, arg_ty);
            }
            result
        }

        RustType::Never => {
            // Empty/False type
            const_expr("Empty", vec![])
        }

        RustType::Function { params, ret } => {
            // Function type: A → B → C
            let mut result = translate_type(ret, ctx);
            for param in params.iter().rev() {
                let param_ty = translate_type(param, ctx);
                result = LeanExpr::pi(clean_kernel::expr::BinderInfo::Default, param_ty, result);
            }
            result
        }

        RustType::Closure {
            params, ret, kind, ..
        } => {
            // RustClosure.type params ret kind
            // Encode the function signature as a product type for params
            let params_ty = if params.is_empty() {
                const_expr("Unit", vec![])
            } else if params.len() == 1 {
                translate_type(&params[0], ctx)
            } else {
                // Build nested Prod type for params
                let mut result = translate_type(
                    params
                        .last()
                        .expect("invariant: non-empty after is_empty guard"),
                    ctx,
                );
                for param in params.iter().rev().skip(1) {
                    let param_ty = translate_type(param, ctx);
                    result = LeanExpr::app(
                        LeanExpr::app(
                            const_expr("Prod", vec![LeanLevel::zero(), LeanLevel::zero()]),
                            param_ty,
                        ),
                        result,
                    );
                }
                result
            };
            let ret_ty = translate_type(ret, ctx);
            let kind_expr = match kind {
                crate::types::ClosureKind::Fn => const_expr("ClosureKind.fn", vec![]),
                crate::types::ClosureKind::FnMut => const_expr("ClosureKind.fnMut", vec![]),
                crate::types::ClosureKind::FnOnce => const_expr("ClosureKind.fnOnce", vec![]),
            };
            // RustClosure.type params ret kind
            LeanExpr::app(
                LeanExpr::app(
                    LeanExpr::app(
                        const_expr("RustClosure.type", vec![LeanLevel::zero()]),
                        params_ty,
                    ),
                    ret_ty,
                ),
                kind_expr,
            )
        }

        RustType::DynTrait {
            trait_name,
            auto_traits,
        } => {
            // DynTrait [trait_names] lifetime
            // Encode trait names as a list of strings
            let mut trait_list = const_expr("List.nil", vec![LeanLevel::zero()]);
            for trait_name in std::iter::once(trait_name).chain(auto_traits.iter()).rev() {
                trait_list = LeanExpr::app(
                    LeanExpr::app(
                        const_expr("List.cons", vec![LeanLevel::zero()]),
                        LeanExpr::str_lit(trait_name),
                    ),
                    trait_list,
                );
            }
            let lifetime_expr = translate_lifetime(&Lifetime::Static);
            // DynTrait.mk traits lifetime
            LeanExpr::app(
                LeanExpr::app(
                    const_expr("DynTrait.mk", vec![LeanLevel::zero()]),
                    trait_list,
                ),
                lifetime_expr,
            )
        }

        RustType::ImplTrait { traits } => {
            // ImplTrait [trait_names]
            // Encode trait names as a list of strings
            let mut trait_list = const_expr("List.nil", vec![LeanLevel::zero()]);
            for trait_name in traits.iter().rev() {
                trait_list = LeanExpr::app(
                    LeanExpr::app(
                        const_expr("List.cons", vec![LeanLevel::zero()]),
                        LeanExpr::str_lit(trait_name),
                    ),
                    trait_list,
                );
            }
            // ImplTrait.mk traits
            LeanExpr::app(
                const_expr("ImplTrait.mk", vec![LeanLevel::zero()]),
                trait_list,
            )
        }

        RustType::TypeParam(crate::types::TypeVar { id, name }) => {
            // Hoisted generic context: this parameter has a dedicated free
            // variable that `translate_generic_type` will abstract into a `Π`
            // binder. Emitting the fvar makes every occurrence become that
            // bound `Sort` variable (a real `∀`-quantification), rather than
            // an opaque constant.
            if let Some(fvar) = ctx.type_param_fvars.get(id) {
                LeanExpr::fvar(*fvar)
            } else {
                // Monomorphic / opaque path: an unresolved type parameter
                // (not in `type_param_subst`, not hoisted). Encode as a named
                // free constant for proof obligations, as before.
                let param_name = name.as_deref().unwrap_or("_T");
                LeanExpr::app(
                    const_expr("RustTypeParam", vec![LeanLevel::zero()]),
                    LeanExpr::str_lit(param_name),
                )
            }
        }

        // Other types get mapped to a generic representation
        _ => const_expr("Any", vec![LeanLevel::zero()]),
    }
}

/// Universe used for hoisted generic type parameters: `Type 0` (`Sort 1`).
///
/// This matches the level-0 instantiation that [`translate_type`] uses for
/// every built-in generic constructor (`Option.{0}`, `Ref.{0}`, `Prod.{0,0}`,
/// `Except.{0,0}`, ...). A parameter `T` applied as e.g. `Option.{0} T` must
/// therefore inhabit `Type 0`, so we bind it at exactly that sort.
fn type_param_sort() -> LeanExpr {
    // `Expr::type_()` == `Sort (succ zero)` == `Type 0`.
    LeanExpr::type_()
}

/// Whether a trait-bound string requires machinery we cannot yet soundly
/// hoist (an associated-type binding such as `Iterator<Item = u32>`).
///
/// A bare marker/trait bound (`Clone`, `Debug`, `From<u32>`) is *erased* when
/// hoisting: dropping it yields a strictly more general `∀`-quantified type,
/// which is still a sound CIC type. An associated-type projection (`= …`)
/// genuinely constrains the body and cannot be erased without changing
/// meaning, so we fail closed on it.
fn bound_binds_associated_type(bound: &str) -> bool {
    bound.contains('=')
}

/// Hoist a generic Rust type / signature into a `Π`-telescope CIC type.
///
/// Given the body type `ty` of a generic declaration and its type parameters
/// `<T0, T1, …, T_{n-1}>`, produces
///
/// ```text
/// Π (T0 : Type) (T1 : Type) … (T_{n-1} : Type), <ty with each Ti bound>
/// ```
///
/// Each parameter is bound at `Type 0` (see [`type_param_sort`]) and every
/// occurrence of `Ti` inside `ty` becomes the corresponding bound de Bruijn
/// variable — a real `∀`-quantified `Sort` variable, **not** the opaque
/// `RustTypeParam` constant emitted by the monomorphic path. This is what lets
/// generic data types (e.g. the kernel's own `Option<T>`-shaped types) convert
/// to genuine CIC `Π`-types.
///
/// # Soundness
///
/// Parameters are realised as fresh free variables during body translation,
/// then abstracted with [`Expr::abstract_fvar`], which performs the de Bruijn
/// index shifting correctly even across the `Π` binders that `translate_type`
/// introduces for `RustType::Function`. Abstracting in declaration order maps
/// `Ti` to `BVar(n-1-i)`, and wrapping the binders innermost-first places `T0`
/// outermost — so the telescope is `Π T0 … T_{n-1}, body` exactly.
///
/// Fails closed with [`RustSemError::GenericHoistUnsupported`] (never emits a
/// wrong sort) on parameter shapes we cannot yet hoist:
///
/// * trait bounds that bind an associated type (`Iterator<Item = …>`);
/// * duplicate parameter ids (defensive; `assign_type_param_ids` makes ids
///   unique, so this should be unreachable).
///
/// Lifetime parameters are already dropped by the source frontend, and const
/// generics are rejected there (`const_params` is a separate list and never
/// appears in `type_params`), so neither reaches this function.
///
/// The non-generic case (`type_params` empty) simply delegates to
/// [`translate_type`].
pub fn translate_generic_type(
    ty: &RustType,
    type_params: &[crate::types::TypeParamDef],
    ctx: &mut TranslationContext,
) -> Result<LeanExpr, RustSemError> {
    if type_params.is_empty() {
        return Ok(translate_type(ty, ctx));
    }

    // Fail closed on parameter shapes we cannot soundly hoist.
    for tp in type_params {
        if let Some(bound) = tp.bounds.iter().find(|b| bound_binds_associated_type(b)) {
            return Err(RustSemError::GenericHoistUnsupported {
                param: tp.name.clone(),
                reason: format!("trait bound `{bound}` binds an associated type"),
            });
        }
    }

    // Allocate a fresh, collision-free free variable per parameter. The body
    // translation introduces no other free variables, so the contiguous range
    // `0..n` cannot collide with anything `translate_type` produces.
    let mut fvar_map: HashMap<u32, FVarId> = HashMap::with_capacity(type_params.len());
    for (i, tp) in type_params.iter().enumerate() {
        fvar_map.insert(tp.id, FVarId::new(i as u64));
    }
    // Defensive: duplicate ids would alias two distinct binders onto one fvar.
    if fvar_map.len() != type_params.len() {
        return Err(RustSemError::GenericHoistUnsupported {
            param: type_params
                .iter()
                .map(|tp| tp.name.as_str())
                .collect::<Vec<_>>()
                .join(", "),
            reason: "duplicate type-parameter ids in the same generic context".to_string(),
        });
    }

    // Translate the body with the parameters realised as free variables, then
    // restore any prior bindings (save/restore avoids cloning the environment).
    let saved = std::mem::replace(&mut ctx.type_param_fvars, fvar_map);
    let mut body = translate_type(ty, ctx);
    ctx.type_param_fvars = saved;

    // Abstract in declaration order: T0, T1, …, T_{n-1}. After all `n`
    // abstractions, `Ti` sits at `BVar(n-1-i)`.
    for i in 0..type_params.len() {
        body = body.abstract_fvar(FVarId::new(i as u64));
    }

    // Wrap one `Π` binder per parameter, innermost (last) first, so that `T0`
    // ends up outermost. All parameter types are the same independent `Sort`,
    // so no binder type references an earlier binder.
    let sort = type_param_sort();
    let binder = BinderData::unrestricted(BinderInfo::Implicit);
    for _ in type_params.iter().rev() {
        body = LeanExpr::pi(binder, sort.clone(), body);
    }

    Ok(body)
}

/// Translate a Rust value to a clean expression
#[allow(clippy::only_used_in_recursion)]
pub fn translate_value(val: &RustValue, ctx: &TranslationContext) -> LeanExpr {
    match val {
        RustValue::Unit => const_expr("Unit.unit", vec![]),

        RustValue::Bool(b) => {
            let name = if *b { "Bool.true" } else { "Bool.false" };
            const_expr(name, vec![])
        }

        RustValue::Char(c) => {
            // Characters as nat codes
            nat_lit(*c as u64)
        }

        RustValue::Str(s) => LeanExpr::str_lit(s),

        RustValue::Uint { value, .. } => nat_lit(*value as u64),

        RustValue::Int { value, .. } => {
            // Encode signed integers
            if *value >= 0 {
                nat_lit(*value as u64)
            } else {
                // Negative: Int.negSucc (n - 1) for -n.
                // Use unsigned_abs() instead of `-value` so that i128::MIN (a
                // genuinely producible Value::Int — the source literal parser
                // returns it) does not overflow i128 negation. For any value < 0,
                // value.unsigned_abs() >= 1, so the `- 1` never underflows and
                // the result equals the old `(-value - 1)` for all non-MIN
                // negatives. `as u64` truncation is unchanged (pre-existing).
                let abs = (value.unsigned_abs() - 1) as u64;
                LeanExpr::app(const_expr("Int.negSucc", vec![]), nat_lit(abs))
            }
        }

        RustValue::Float { bits, ty } => {
            // Encode floats as their bit representation for verification
            // RustFloat.mk bits isF64
            // This preserves NaN payloads and exact bit-level semantics
            let is_f64 = matches!(ty, crate::types::FloatType::F64);
            let bits_expr = nat_lit(*bits);
            let is_f64_expr = if is_f64 {
                const_expr("Bool.true", vec![])
            } else {
                const_expr("Bool.false", vec![])
            };
            LeanExpr::app(
                LeanExpr::app(const_expr("RustFloat.mk", vec![]), bits_expr),
                is_f64_expr,
            )
        }

        RustValue::Reference {
            addr,
            mutability,
            lifetime: _,
            referent: _,
        } => {
            // Encode references as: RustRef.mk alloc_id offset isMut
            // Address has alloc_id and offset fields
            let alloc_expr = nat_lit(addr.alloc_id.0);
            let offset_expr = nat_lit(addr.offset);
            let is_mut = matches!(mutability, Mutability::Mutable);
            let mut_expr = if is_mut {
                const_expr("Bool.true", vec![])
            } else {
                const_expr("Bool.false", vec![])
            };
            LeanExpr::app(
                LeanExpr::app(
                    LeanExpr::app(const_expr("RustRef.mk", vec![]), alloc_expr),
                    offset_expr,
                ),
                mut_expr,
            )
        }

        RustValue::RawPtr {
            addr, mutability, ..
        } => {
            // Encode raw pointers as: RustPtr.mk alloc_id offset isMut
            let alloc_expr = nat_lit(addr.alloc_id.0);
            let offset_expr = nat_lit(addr.offset);
            let is_mut = matches!(mutability, Mutability::Mutable);
            let mut_expr = if is_mut {
                const_expr("Bool.true", vec![])
            } else {
                const_expr("Bool.false", vec![])
            };
            LeanExpr::app(
                LeanExpr::app(
                    LeanExpr::app(const_expr("RustPtr.mk", vec![]), alloc_expr),
                    offset_expr,
                ),
                mut_expr,
            )
        }

        RustValue::Cell { value, .. }
        | RustValue::RefCell { value, .. }
        | RustValue::UnsafeCell { value, .. }
        | RustValue::Mutex { value, .. }
        | RustValue::RwLock { value, .. }
        | RustValue::MutexGuard { value, .. }
        | RustValue::RwLockReadGuard { value, .. }
        | RustValue::RwLockWriteGuard { value, .. }
        | RustValue::RefCellRef { value, .. }
        | RustValue::RefCellRefMut { value, .. } => translate_value(value, ctx),
        RustValue::OnceCell { value, .. } | RustValue::OnceLock { value, .. } => {
            value.as_deref().map_or_else(
                || translate_value(&RustValue::Unit, ctx),
                |value| translate_value(value, ctx),
            )
        }

        RustValue::FatPtr(crate::values::FatPointer {
            data_pointer,
            metadata,
        }) => match metadata {
            crate::values::FatPtrMetadata::VtablePtr(vtable_ptr) => {
                let data_expr = translate_value(data_pointer, ctx);
                let vtable_name = LeanExpr::str_lit(&vtable_ptr.trait_name);
                LeanExpr::app(
                    LeanExpr::app(
                        const_expr("RustTraitObject.mk", vec![LeanLevel::zero()]),
                        data_expr,
                    ),
                    vtable_name,
                )
            }
            crate::values::FatPtrMetadata::SliceLen(len) => LeanExpr::app(
                LeanExpr::app(
                    const_expr("Prod.mk", vec![LeanLevel::zero(), LeanLevel::zero()]),
                    translate_value(data_pointer, ctx),
                ),
                nat_lit(*len as u64),
            ),
        },

        RustValue::Ordering(ordering) => LeanExpr::str_lit(format!("{ordering:?}")),

        RustValue::Atomic { inner } => translate_value(inner, ctx),

        RustValue::Tuple(elems) => {
            if elems.is_empty() {
                const_expr("Unit.unit", vec![])
            } else if elems.len() == 1 {
                translate_value(&elems[0], ctx)
            } else {
                // Build nested Prod.mk
                let mut result = translate_value(
                    elems
                        .last()
                        .expect("invariant: non-empty after is_empty guard"),
                    ctx,
                );
                for elem in elems.iter().rev().skip(1) {
                    let elem_val = translate_value(elem, ctx);
                    result = LeanExpr::app(
                        LeanExpr::app(
                            const_expr("Prod.mk", vec![LeanLevel::zero(), LeanLevel::zero()]),
                            elem_val,
                        ),
                        result,
                    );
                }
                result
            }
        }

        RustValue::Range {
            start,
            end,
            inclusive,
        } => {
            let tuple = RustValue::Tuple(vec![
                start.as_deref().cloned().unwrap_or(RustValue::Unit),
                end.as_deref().cloned().unwrap_or(RustValue::Unit),
                RustValue::Bool(*inclusive),
            ]);
            translate_value(&tuple, ctx)
        }

        RustValue::Array(elems) => {
            // Build List from elements: List.cons e1 (List.cons e2 ... List.nil)
            // Then wrap with Array.mk
            let mut list = const_expr("List.nil", vec![LeanLevel::zero()]);
            for elem in elems.iter().rev() {
                let elem_val = translate_value(elem, ctx);
                list = LeanExpr::app(
                    LeanExpr::app(const_expr("List.cons", vec![LeanLevel::zero()]), elem_val),
                    list,
                );
            }
            LeanExpr::app(const_expr("Array.mk", vec![LeanLevel::zero()]), list)
        }

        RustValue::Struct { name, fields } => {
            // Struct constructor: Name.mk field1 field2 ...
            let ctor_name = format!("{name}.mk");
            let mut result = const_expr(&ctor_name, vec![LeanLevel::zero()]);
            // Fields are stored in a BTreeMap, so iteration is deterministic by name
            for val in fields.values() {
                result = LeanExpr::app(result, translate_value(val, ctx));
            }
            result
        }

        RustValue::Enum {
            name,
            variant,
            payload,
        } => {
            let ctor_name = format!("{name}.{variant}");
            let mut result = const_expr(&ctor_name, vec![LeanLevel::zero()]);

            match payload.as_ref() {
                crate::values::EnumPayload::Unit => {}
                crate::values::EnumPayload::Tuple(vals) => {
                    for val in vals {
                        result = LeanExpr::app(result, translate_value(val, ctx));
                    }
                }
                crate::values::EnumPayload::Struct(fields) => {
                    // Struct variant fields iterate in deterministic name order (BTreeMap)
                    for val in fields.values() {
                        result = LeanExpr::app(result, translate_value(val, ctx));
                    }
                }
            }
            result
        }

        RustValue::Union {
            name,
            active_field,
            value,
        } => {
            // Encode unions as: Name.mk active_field value
            let ctor_name = format!("{name}.mk");
            let active_expr = LeanExpr::str_lit(active_field);
            let val_expr = translate_value(value, ctx);
            LeanExpr::app(
                LeanExpr::app(
                    LeanExpr::app(const_expr(&ctor_name, vec![LeanLevel::zero()]), active_expr),
                    val_expr,
                ),
                // Placeholder for the byte representation (not needed for semantic verification)
                const_expr("Unit.unit", vec![]),
            )
        }

        RustValue::FnPtr { name } => {
            // Encode function pointers as constant references
            const_expr(name, vec![])
        }

        RustValue::Closure {
            fn_id,
            captures,
            param_types: _,
            ret_type: _,
            kind: _,
        } => {
            // Encode closures as: RustClosure.mk fn_id (captured_values as tuple)
            let fn_id_expr = LeanExpr::str_lit(fn_id);

            // Build tuple of captured values
            let captured: Vec<RustValue> = captures.iter().map(|(_, v, _)| v.clone()).collect();
            let captures_val = RustValue::Tuple(captured);
            let captures_expr = translate_value(&captures_val, ctx);

            LeanExpr::app(
                LeanExpr::app(
                    const_expr("RustClosure.mk", vec![LeanLevel::zero()]),
                    fn_id_expr,
                ),
                captures_expr,
            )
        }

        RustValue::Never => {
            // The never type is uninhabited - use False.elim
            const_expr("False.elim", vec![LeanLevel::zero()])
        }

        RustValue::Uninit => {
            // Uninitialized memory - use a marker constant
            const_expr("RustUninit.mk", vec![])
        }

        RustValue::TraitObject {
            data,
            vtable,
            lifetime: _,
        } => {
            // Encode trait objects as: RustTraitObject.mk data vtable_name
            let data_expr = translate_value(data, ctx);
            let vtable_name = LeanExpr::str_lit(&vtable.trait_name);
            LeanExpr::app(
                LeanExpr::app(
                    const_expr("RustTraitObject.mk", vec![LeanLevel::zero()]),
                    data_expr,
                ),
                vtable_name,
            )
        }

        RustValue::Future { .. } => {
            // Futures are opaque in the verification model — encode as an
            // abstract constructor so the Lean side sees a tagged value.
            const_expr("RustFuture.mk", vec![])
        }
    }
}

/// Check ownership and generate proof obligations
pub fn check_ownership(
    ctx: &mut TranslationContext,
    place: &Place,
    operation: OwnershipOp,
) -> Result<(), BorrowError> {
    let checker = BorrowChecker::new();

    match operation {
        OwnershipOp::Move => {
            checker.check_move(&ctx.ownership, place)?;
            ctx.ownership.mark_moved(place.clone());
        }
        OwnershipOp::SharedBorrow(lt) => {
            checker.check_borrow(&ctx.ownership, place, Mutability::Shared, &lt)?;
            ctx.ownership
                .add_borrow(place.clone(), Mutability::Shared, lt)?;
        }
        OwnershipOp::MutBorrow(lt) => {
            checker.check_borrow(&ctx.ownership, place, Mutability::Mutable, &lt)?;
            ctx.ownership
                .add_borrow(place.clone(), Mutability::Mutable, lt)?;
        }
        OwnershipOp::Use => {
            checker.check_use(&ctx.ownership, place)?;
        }
    }

    Ok(())
}

/// Ownership operation type
#[derive(Debug, Clone)]
pub enum OwnershipOp {
    Move,
    SharedBorrow(Lifetime),
    MutBorrow(Lifetime),
    Use,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::UintType;
    use crate::values::EnumPayload;
    use clean_kernel::expr::ExprKind;
    use std::collections::BTreeMap;

    #[test]
    fn test_translate_primitive_types() {
        let ctx = TranslationContext::new();

        let bool_ty = RustType::Bool;
        let result = translate_type(&bool_ty, &ctx);
        assert!(matches!(result.kind(), ExprKind::Const(_, _)));

        let u32_ty = RustType::Uint(UintType::U32);
        let result = translate_type(&u32_ty, &ctx);
        assert!(matches!(result.kind(), ExprKind::Const(_, _)));
    }

    #[test]
    fn test_translate_tuple_type() {
        let ctx = TranslationContext::new();

        let tuple_ty = RustType::Tuple(vec![RustType::Bool, RustType::Uint(UintType::U32)]);
        let result = translate_type(&tuple_ty, &ctx);
        // Should be Prod Bool UInt32
        assert!(matches!(result.kind(), ExprKind::App(_, _)));
    }

    #[test]
    fn test_translate_values() {
        let ctx = TranslationContext::new();

        let bool_val = RustValue::Bool(true);
        let result = translate_value(&bool_val, &ctx);
        assert!(matches!(result.kind(), ExprKind::Const(_, _)));

        let int_val = RustValue::u32(42);
        let result = translate_value(&int_val, &ctx);
        assert!(matches!(result.kind(), ExprKind::Lit(_)));
    }

    #[test]
    fn test_translate_option_type() {
        let ctx = TranslationContext::new();

        let option_ty = RustType::Option {
            inner: Box::new(RustType::Uint(UintType::U32)),
        };
        let result = translate_type(&option_ty, &ctx);
        // Should be Option UInt32
        assert!(matches!(result.kind(), ExprKind::App(_, _)));
    }

    #[test]
    fn test_translate_raw_ptr_type() {
        let ctx = TranslationContext::new();

        // Shared raw pointer: *const T → RawPtr T
        let const_ptr = RustType::RawPtr {
            mutability: Mutability::Shared,
            inner: Box::new(RustType::Uint(UintType::U32)),
        };
        let result = translate_type(&const_ptr, &ctx);
        // Should be RawPtr UInt32
        assert!(matches!(result.kind(), ExprKind::App(_, _)));

        // Mutable raw pointer: *mut T → RawPtrMut T
        let mut_ptr = RustType::RawPtr {
            mutability: Mutability::Mutable,
            inner: Box::new(RustType::Bool),
        };
        let result = translate_type(&mut_ptr, &ctx);
        // Should be RawPtrMut Bool
        assert!(matches!(result.kind(), ExprKind::App(_, _)));
    }

    #[test]
    fn test_translate_box_type() {
        let ctx = TranslationContext::new();

        // Box<T> translates to just T (ownership encoded elsewhere)
        let box_ty = RustType::Box {
            inner: Box::new(RustType::Uint(UintType::U64)),
        };
        let result = translate_type(&box_ty, &ctx);
        // Should be UInt64 directly
        assert!(matches!(result.kind(), ExprKind::Const(_, _)));

        // Nested Box<Box<T>> also flattens
        let nested_box = RustType::Box {
            inner: Box::new(RustType::Box {
                inner: Box::new(RustType::Bool),
            }),
        };
        let result = translate_type(&nested_box, &ctx);
        // Should be Bool
        assert!(matches!(result.kind(), ExprKind::Const(_, _)));
    }

    #[test]
    fn test_translate_struct_value_orders_fields_deterministically() {
        let ctx = TranslationContext::new();

        let mut fields = BTreeMap::new();
        fields.insert("y".to_string(), RustValue::u32(2));
        fields.insert("x".to_string(), RustValue::u32(1));

        let value = RustValue::Struct {
            name: "Pair".to_string(),
            fields,
        };

        let expr = translate_value(&value, &ctx);
        let expected = LeanExpr::app(
            LeanExpr::app(const_expr("Pair.mk", vec![LeanLevel::zero()]), nat_lit(1)),
            nat_lit(2),
        );
        assert_eq!(expr, expected);
    }

    #[test]
    fn test_translate_enum_struct_variant_orders_fields_deterministically() {
        let ctx = TranslationContext::new();

        let mut fields = BTreeMap::new();
        fields.insert("b".to_string(), RustValue::Bool(true));
        fields.insert("a".to_string(), RustValue::u32(7));

        let value = RustValue::Enum {
            name: "Wrapper".to_string(),
            variant: "Data".to_string(),
            payload: Box::new(EnumPayload::Struct(fields)),
        };

        let expr = translate_value(&value, &ctx);
        let expected = LeanExpr::app(
            LeanExpr::app(
                const_expr("Wrapper.Data", vec![LeanLevel::zero()]),
                nat_lit(7),
            ),
            const_expr("Bool.true", vec![]),
        );
        assert_eq!(expr, expected);
    }

    #[test]
    fn test_translate_array_empty() {
        let ctx = TranslationContext::new();

        let value = RustValue::Array(vec![]);
        let expr = translate_value(&value, &ctx);

        // Empty array: Array.mk List.nil
        let expected = LeanExpr::app(
            const_expr("Array.mk", vec![LeanLevel::zero()]),
            const_expr("List.nil", vec![LeanLevel::zero()]),
        );
        assert_eq!(expr, expected);
    }

    #[test]
    fn test_translate_array_single_element() {
        let ctx = TranslationContext::new();

        let value = RustValue::Array(vec![RustValue::u32(42)]);
        let expr = translate_value(&value, &ctx);

        // Single element: Array.mk (List.cons 42 List.nil)
        let list = LeanExpr::app(
            LeanExpr::app(
                const_expr("List.cons", vec![LeanLevel::zero()]),
                nat_lit(42),
            ),
            const_expr("List.nil", vec![LeanLevel::zero()]),
        );
        let expected = LeanExpr::app(const_expr("Array.mk", vec![LeanLevel::zero()]), list);
        assert_eq!(expr, expected);
    }

    #[test]
    fn test_translate_array_multiple_elements() {
        let ctx = TranslationContext::new();

        let value = RustValue::Array(vec![
            RustValue::u32(1),
            RustValue::u32(2),
            RustValue::u32(3),
        ]);
        let expr = translate_value(&value, &ctx);

        // [1, 2, 3] -> Array.mk (List.cons 1 (List.cons 2 (List.cons 3 List.nil)))
        let nil = const_expr("List.nil", vec![LeanLevel::zero()]);
        let cons = |elem, tail| {
            LeanExpr::app(
                LeanExpr::app(const_expr("List.cons", vec![LeanLevel::zero()]), elem),
                tail,
            )
        };
        let list = cons(nat_lit(1), cons(nat_lit(2), cons(nat_lit(3), nil)));
        let expected = LeanExpr::app(const_expr("Array.mk", vec![LeanLevel::zero()]), list);
        assert_eq!(expr, expected);
    }

    #[test]
    fn test_translate_float_f32() {
        use crate::types::FloatType;
        let ctx = TranslationContext::new();

        let value = RustValue::Float {
            bits: 0x40490FDB, // ~3.14159 as f32 bits
            ty: FloatType::F32,
        };
        let expr = translate_value(&value, &ctx);

        // RustFloat.mk bits Bool.false (isF64=false for f32)
        let expected = LeanExpr::app(
            LeanExpr::app(const_expr("RustFloat.mk", vec![]), nat_lit(0x40490FDB)),
            const_expr("Bool.false", vec![]),
        );
        assert_eq!(expr, expected);
    }

    #[test]
    fn test_translate_float_f64() {
        use crate::types::FloatType;
        let ctx = TranslationContext::new();

        let value = RustValue::Float {
            bits: 0x400921FB54442D18, // ~3.14159 as f64 bits
            ty: FloatType::F64,
        };
        let expr = translate_value(&value, &ctx);

        // RustFloat.mk bits Bool.true (isF64=true for f64)
        let expected = LeanExpr::app(
            LeanExpr::app(
                const_expr("RustFloat.mk", vec![]),
                nat_lit(0x400921FB54442D18),
            ),
            const_expr("Bool.true", vec![]),
        );
        assert_eq!(expr, expected);
    }

    #[test]
    fn test_translate_reference() {
        use crate::memory::{Address, AllocId};
        let ctx = TranslationContext::new();

        let value = RustValue::Reference {
            addr: Address::new(AllocId(42), 8),
            mutability: Mutability::Shared,
            lifetime: Lifetime::Named("a".to_string()),
            referent: None,
        };
        let expr = translate_value(&value, &ctx);

        // RustRef.mk alloc_id offset isMut
        let expected = LeanExpr::app(
            LeanExpr::app(
                LeanExpr::app(const_expr("RustRef.mk", vec![]), nat_lit(42)),
                nat_lit(8),
            ),
            const_expr("Bool.false", vec![]),
        );
        assert_eq!(expr, expected);
    }

    #[test]
    fn test_translate_raw_ptr_mut() {
        use crate::memory::{Address, AllocId};
        let ctx = TranslationContext::new();

        let value = RustValue::RawPtr {
            addr: Address::new(AllocId(100), 0),
            mutability: Mutability::Mutable,
            tag: None,
        };
        let expr = translate_value(&value, &ctx);

        // RustPtr.mk alloc_id offset isMut
        let expected = LeanExpr::app(
            LeanExpr::app(
                LeanExpr::app(const_expr("RustPtr.mk", vec![]), nat_lit(100)),
                nat_lit(0),
            ),
            const_expr("Bool.true", vec![]),
        );
        assert_eq!(expr, expected);
    }

    #[test]
    fn test_translate_fn_ptr() {
        let ctx = TranslationContext::new();

        let value = RustValue::FnPtr {
            name: "my_function".to_string(),
        };
        let expr = translate_value(&value, &ctx);

        // Function pointers become constant references
        let expected = const_expr("my_function", vec![]);
        assert_eq!(expr, expected);
    }

    #[test]
    fn test_translate_never() {
        let ctx = TranslationContext::new();

        let value = RustValue::Never;
        let expr = translate_value(&value, &ctx);

        // Never type uses False.elim
        let expected = const_expr("False.elim", vec![LeanLevel::zero()]);
        assert_eq!(expr, expected);
    }

    #[test]
    fn test_translate_uninit() {
        let ctx = TranslationContext::new();

        let value = RustValue::Uninit;
        let expr = translate_value(&value, &ctx);

        // Uninitialized memory marker
        let expected = const_expr("RustUninit.mk", vec![]);
        assert_eq!(expr, expected);
    }

    #[test]
    fn test_ownership_tracking() {
        let mut ctx = TranslationContext::new();
        let place = Place::local(0);

        ctx.ownership.mark_owned(place.clone());

        // Should allow use
        check_ownership(&mut ctx, &place, OwnershipOp::Use)
            .expect("use of owned place should succeed");

        // Should allow move
        check_ownership(&mut ctx, &place, OwnershipOp::Move)
            .expect("move of owned place should succeed");

        // After move, use should fail
        let result = check_ownership(&mut ctx, &place, OwnershipOp::Use);
        assert!(
            matches!(result, Err(BorrowError::UseAfterMove { .. })),
            "expected UseAfterMove, got: {result:?}"
        );
    }

    #[test]
    fn test_borrow_tracking() {
        let mut ctx = TranslationContext::new();
        let place = Place::local(0);
        let lifetime = Lifetime::Named("a".to_string());

        ctx.ownership.mark_owned(place.clone());

        // Create shared borrow
        check_ownership(
            &mut ctx,
            &place,
            OwnershipOp::SharedBorrow(lifetime.clone()),
        )
        .expect("shared borrow of owned place should succeed");

        // Move should now fail (borrowed)
        let result = check_ownership(&mut ctx, &place, OwnershipOp::Move);
        assert!(
            matches!(result, Err(BorrowError::MoveWhileBorrowed { .. })),
            "expected MoveWhileBorrowed, got: {result:?}"
        );

        // End the borrow
        ctx.ownership.end_borrows(&lifetime);

        // Now move should succeed
        check_ownership(&mut ctx, &place, OwnershipOp::Move)
            .expect("move after borrow end should succeed");
    }

    #[test]
    fn test_translate_array_nested() {
        let ctx = TranslationContext::new();

        // [[1, 2], [3, 4]] - array of arrays
        let value = RustValue::Array(vec![
            RustValue::Array(vec![RustValue::u32(1), RustValue::u32(2)]),
            RustValue::Array(vec![RustValue::u32(3), RustValue::u32(4)]),
        ]);
        let expr = translate_value(&value, &ctx);

        // Each inner array is: Array.mk (List.cons elem1 (List.cons elem2 List.nil))
        let nil = const_expr("List.nil", vec![LeanLevel::zero()]);
        let cons = |elem, tail| {
            LeanExpr::app(
                LeanExpr::app(const_expr("List.cons", vec![LeanLevel::zero()]), elem),
                tail,
            )
        };
        let array_mk = |list| LeanExpr::app(const_expr("Array.mk", vec![LeanLevel::zero()]), list);

        let inner1 = array_mk(cons(nat_lit(1), cons(nat_lit(2), nil.clone())));
        let inner2 = array_mk(cons(nat_lit(3), cons(nat_lit(4), nil.clone())));
        let outer_list = cons(inner1, cons(inner2, nil));
        let expected = array_mk(outer_list);

        assert_eq!(expr, expected);
    }

    #[test]
    fn test_translate_array_of_structs() {
        let ctx = TranslationContext::new();

        let mut fields1 = BTreeMap::new();
        fields1.insert("x".to_string(), RustValue::u32(1));

        let mut fields2 = BTreeMap::new();
        fields2.insert("x".to_string(), RustValue::u32(2));

        let value = RustValue::Array(vec![
            RustValue::Struct {
                name: "Point".to_string(),
                fields: fields1,
            },
            RustValue::Struct {
                name: "Point".to_string(),
                fields: fields2,
            },
        ]);
        let expr = translate_value(&value, &ctx);

        // Each struct is: Point.mk x_value
        let struct1 = LeanExpr::app(const_expr("Point.mk", vec![LeanLevel::zero()]), nat_lit(1));
        let struct2 = LeanExpr::app(const_expr("Point.mk", vec![LeanLevel::zero()]), nat_lit(2));

        let nil = const_expr("List.nil", vec![LeanLevel::zero()]);
        let cons = |elem, tail| {
            LeanExpr::app(
                LeanExpr::app(const_expr("List.cons", vec![LeanLevel::zero()]), elem),
                tail,
            )
        };
        let list = cons(struct1, cons(struct2, nil));
        let expected = LeanExpr::app(const_expr("Array.mk", vec![LeanLevel::zero()]), list);

        assert_eq!(expr, expected);
    }

    #[test]
    fn test_translate_enum_tuple_variant() {
        let ctx = TranslationContext::new();

        let value = RustValue::Enum {
            name: "Option".to_string(),
            variant: "Some".to_string(),
            payload: Box::new(EnumPayload::Tuple(vec![RustValue::u32(42)])),
        };
        let expr = translate_value(&value, &ctx);

        // Option.Some 42
        let expected = LeanExpr::app(
            const_expr("Option.Some", vec![LeanLevel::zero()]),
            nat_lit(42),
        );
        assert_eq!(expr, expected);
    }

    #[test]
    fn test_translate_enum_unit_variant() {
        let ctx = TranslationContext::new();

        let value = RustValue::Enum {
            name: "Option".to_string(),
            variant: "None".to_string(),
            payload: Box::new(EnumPayload::Unit),
        };
        let expr = translate_value(&value, &ctx);

        // Option.None (no payload)
        let expected = const_expr("Option.None", vec![LeanLevel::zero()]);
        assert_eq!(expr, expected);
    }

    #[test]
    fn test_translate_closure() {
        use crate::types::ClosureKind;
        let ctx = TranslationContext::new();

        let value = RustValue::Closure {
            fn_id: "closure_123".to_string(),
            captures: vec![
                ("x".to_string(), RustValue::u32(10), Mutability::Shared),
                ("y".to_string(), RustValue::Bool(true), Mutability::Shared),
            ],
            param_types: vec![RustType::Bool],
            ret_type: RustType::Uint(UintType::U32),
            kind: ClosureKind::Fn,
        };
        let expr = translate_value(&value, &ctx);

        // RustClosure.mk "closure_123" (captured_tuple)
        // Captures are turned into a tuple: (10, true)
        let captures_tuple = LeanExpr::app(
            LeanExpr::app(
                const_expr("Prod.mk", vec![LeanLevel::zero(), LeanLevel::zero()]),
                nat_lit(10),
            ),
            const_expr("Bool.true", vec![]),
        );
        let expected = LeanExpr::app(
            LeanExpr::app(
                const_expr("RustClosure.mk", vec![LeanLevel::zero()]),
                LeanExpr::str_lit("closure_123"),
            ),
            captures_tuple,
        );
        assert_eq!(expr, expected);
    }

    #[test]
    fn test_translate_trait_object() {
        use crate::types::VTable;
        let ctx = TranslationContext::new();

        let vtable = VTable::new("Display".to_string(), "MyStruct".to_string());
        let value = RustValue::TraitObject {
            data: Box::new(RustValue::u32(100)),
            vtable,
            lifetime: Lifetime::Static,
        };
        let expr = translate_value(&value, &ctx);

        // RustTraitObject.mk data "Display"
        let expected = LeanExpr::app(
            LeanExpr::app(
                const_expr("RustTraitObject.mk", vec![LeanLevel::zero()]),
                nat_lit(100),
            ),
            LeanExpr::str_lit("Display"),
        );
        assert_eq!(expr, expected);
    }

    #[test]
    fn test_translate_union() {
        let ctx = TranslationContext::new();

        let value = RustValue::Union {
            name: "MyUnion".to_string(),
            active_field: "i32_field".to_string(),
            value: Box::new(RustValue::i32(42)),
        };
        let expr = translate_value(&value, &ctx);

        // MyUnion.mk "i32_field" 42 Unit.unit
        let expected = LeanExpr::app(
            LeanExpr::app(
                LeanExpr::app(
                    const_expr("MyUnion.mk", vec![LeanLevel::zero()]),
                    LeanExpr::str_lit("i32_field"),
                ),
                nat_lit(42),
            ),
            const_expr("Unit.unit", vec![]),
        );
        assert_eq!(expr, expected);
    }

    #[test]
    fn test_translate_char() {
        let ctx = TranslationContext::new();

        let value = RustValue::Char('A');
        let expr = translate_value(&value, &ctx);

        // Chars are encoded as their Unicode code point
        let expected = nat_lit('A' as u64); // 65
        assert_eq!(expr, expected);
    }

    #[test]
    fn test_translate_negative_int() {
        let ctx = TranslationContext::new();

        // Test -5: encoded as Int.negSucc 4 (since -n = Int.negSucc (n-1))
        let value = RustValue::i32(-5);
        let expr = translate_value(&value, &ctx);

        // -5 = Int.negSucc 4
        let expected = LeanExpr::app(const_expr("Int.negSucc", vec![]), nat_lit(4));
        assert_eq!(expr, expected);
    }

    #[test]
    fn test_translate_i128_min_no_overflow() {
        // Regression: i128::MIN is a genuinely producible Value::Int (the source
        // literal parser returns Value::Int { value: i128::MIN, .. } for
        // `-170141183460469231731687303715884105728i128`). The negative branch
        // used to compute `(-value - 1) as u64`, and `-i128::MIN` overflows i128
        // (with overflow-checks=true this panics; under panic="abort" it aborts).
        // This must translate without panicking.
        let ctx = TranslationContext::new();

        let value = RustValue::Int {
            value: i128::MIN,
            ty: crate::types::IntType::I128,
        };
        // Before the fix this line panics with "attempt to negate with overflow".
        let expr = translate_value(&value, &ctx);

        // i128::MIN encodes as Int.negSucc n where n = |MIN| - 1 truncated to u64.
        // |i128::MIN| = 2^127, so |MIN| - 1 == u128::from(i128::MAX), whose low
        // 64 bits are u64::MAX. The point of the test is no-overflow; assert the
        // shape and the low-64-bit magnitude are as intended.
        let abs_u64 = i128::MAX as u128 as u64; // == u64::MAX
        let expected = LeanExpr::app(const_expr("Int.negSucc", vec![]), nat_lit(abs_u64));
        assert_eq!(expr, expected);
    }

    #[test]
    fn test_translate_tuple_values() {
        let ctx = TranslationContext::new();

        // Test 2-element tuple
        let value = RustValue::Tuple(vec![RustValue::u32(1), RustValue::u32(2)]);
        let expr = translate_value(&value, &ctx);

        // (1, 2) = Prod.mk 1 2
        let expected = LeanExpr::app(
            LeanExpr::app(
                const_expr("Prod.mk", vec![LeanLevel::zero(), LeanLevel::zero()]),
                nat_lit(1),
            ),
            nat_lit(2),
        );
        assert_eq!(expr, expected);
    }

    #[test]
    fn test_translate_range_value_uses_legacy_tuple_encoding() {
        let ctx = TranslationContext::new();

        let value = RustValue::Range {
            start: Some(Box::new(RustValue::u32(1))),
            end: Some(Box::new(RustValue::u32(3))),
            inclusive: true,
        };
        let expr = translate_value(&value, &ctx);

        let expected = LeanExpr::app(
            LeanExpr::app(
                const_expr("Prod.mk", vec![LeanLevel::zero(), LeanLevel::zero()]),
                nat_lit(1),
            ),
            LeanExpr::app(
                LeanExpr::app(
                    const_expr("Prod.mk", vec![LeanLevel::zero(), LeanLevel::zero()]),
                    nat_lit(3),
                ),
                const_expr("Bool.true", vec![]),
            ),
        );
        assert_eq!(expr, expected);
    }

    #[test]
    fn test_translate_empty_tuple() {
        let ctx = TranslationContext::new();

        // Empty tuple = Unit
        let value = RustValue::Tuple(vec![]);
        let expr = translate_value(&value, &ctx);

        let expected = const_expr("Unit.unit", vec![]);
        assert_eq!(expr, expected);
    }

    #[test]
    fn test_translate_unit() {
        let ctx = TranslationContext::new();

        let value = RustValue::Unit;
        let expr = translate_value(&value, &ctx);

        let expected = const_expr("Unit.unit", vec![]);
        assert_eq!(expr, expected);
    }

    #[test]
    fn test_translate_single_element_tuple() {
        let ctx = TranslationContext::new();

        // Single-element tuple is unwrapped to the element itself
        let value = RustValue::Tuple(vec![RustValue::u32(42)]);
        let expr = translate_value(&value, &ctx);

        // (42,) -> 42 (unwrapped)
        let expected = nat_lit(42);
        assert_eq!(expr, expected);
    }

    #[test]
    fn test_translate_closure_type() {
        use crate::types::ClosureKind;
        let ctx = TranslationContext::new();

        // Closure type: |i32, bool| -> u64 with Fn kind
        let ty = RustType::Closure {
            params: vec![RustType::Int(crate::types::IntType::I32), RustType::Bool],
            ret: Box::new(RustType::Uint(UintType::U64)),
            captures: vec![],
            kind: ClosureKind::Fn,
        };
        let expr = translate_type(&ty, &ctx);

        // RustClosure.type (Prod Int32 Bool) UInt64 ClosureKind.fn
        let params_ty = LeanExpr::app(
            LeanExpr::app(
                const_expr("Prod", vec![LeanLevel::zero(), LeanLevel::zero()]),
                const_expr("Int32", vec![]),
            ),
            const_expr("Bool", vec![]),
        );
        let expected = LeanExpr::app(
            LeanExpr::app(
                LeanExpr::app(
                    const_expr("RustClosure.type", vec![LeanLevel::zero()]),
                    params_ty,
                ),
                const_expr("UInt64", vec![]),
            ),
            const_expr("ClosureKind.fn", vec![]),
        );
        assert_eq!(expr, expected);
    }

    #[test]
    fn test_translate_closure_type_fnmut() {
        use crate::types::ClosureKind;
        let ctx = TranslationContext::new();

        // FnMut closure with single param
        let ty = RustType::Closure {
            params: vec![RustType::Bool],
            ret: Box::new(RustType::Unit),
            captures: vec![],
            kind: ClosureKind::FnMut,
        };
        let expr = translate_type(&ty, &ctx);

        // RustClosure.type Bool Unit ClosureKind.fnMut
        let expected = LeanExpr::app(
            LeanExpr::app(
                LeanExpr::app(
                    const_expr("RustClosure.type", vec![LeanLevel::zero()]),
                    const_expr("Bool", vec![]),
                ),
                const_expr("Unit", vec![]),
            ),
            const_expr("ClosureKind.fnMut", vec![]),
        );
        assert_eq!(expr, expected);
    }

    #[test]
    fn test_translate_closure_type_fnonce_no_params() {
        use crate::types::ClosureKind;
        let ctx = TranslationContext::new();

        // FnOnce closure with no params
        let ty = RustType::Closure {
            params: vec![],
            ret: Box::new(RustType::Bool),
            captures: vec![],
            kind: ClosureKind::FnOnce,
        };
        let expr = translate_type(&ty, &ctx);

        // RustClosure.type Unit Bool ClosureKind.fnOnce
        let expected = LeanExpr::app(
            LeanExpr::app(
                LeanExpr::app(
                    const_expr("RustClosure.type", vec![LeanLevel::zero()]),
                    const_expr("Unit", vec![]),
                ),
                const_expr("Bool", vec![]),
            ),
            const_expr("ClosureKind.fnOnce", vec![]),
        );
        assert_eq!(expr, expected);
    }

    #[test]
    fn test_translate_dyn_trait_type() {
        let ctx = TranslationContext::new();

        // dyn Display + Debug with 'static lifetime
        let ty = RustType::DynTrait {
            trait_name: "Display".to_string(),
            auto_traits: vec!["Debug".to_string()],
        };
        let expr = translate_type(&ty, &ctx);

        // DynTrait.mk ["Display", "Debug"] RustLifetime.static
        let trait_list = LeanExpr::app(
            LeanExpr::app(
                const_expr("List.cons", vec![LeanLevel::zero()]),
                LeanExpr::str_lit("Display"),
            ),
            LeanExpr::app(
                LeanExpr::app(
                    const_expr("List.cons", vec![LeanLevel::zero()]),
                    LeanExpr::str_lit("Debug"),
                ),
                const_expr("List.nil", vec![LeanLevel::zero()]),
            ),
        );
        let expected = LeanExpr::app(
            LeanExpr::app(
                const_expr("DynTrait.mk", vec![LeanLevel::zero()]),
                trait_list,
            ),
            const_expr("RustLifetime.static", vec![]),
        );
        assert_eq!(expr, expected);
    }

    #[test]
    fn test_translate_dyn_trait_single_trait() {
        let ctx = TranslationContext::new();

        // dyn Iterator
        let ty = RustType::DynTrait {
            trait_name: "Iterator".to_string(),
            auto_traits: vec![],
        };
        let expr = translate_type(&ty, &ctx);

        // DynTrait.mk ["Iterator"] RustLifetime.static
        let trait_list = LeanExpr::app(
            LeanExpr::app(
                const_expr("List.cons", vec![LeanLevel::zero()]),
                LeanExpr::str_lit("Iterator"),
            ),
            const_expr("List.nil", vec![LeanLevel::zero()]),
        );
        let expected = LeanExpr::app(
            LeanExpr::app(
                const_expr("DynTrait.mk", vec![LeanLevel::zero()]),
                trait_list,
            ),
            const_expr("RustLifetime.static", vec![]),
        );
        assert_eq!(expr, expected);
    }

    #[test]
    fn test_translate_impl_trait_type() {
        let ctx = TranslationContext::new();

        // impl Clone + Debug
        let ty = RustType::ImplTrait {
            traits: vec!["Clone".to_string(), "Debug".to_string()],
        };
        let expr = translate_type(&ty, &ctx);

        // ImplTrait.mk ["Clone", "Debug"]
        let trait_list = LeanExpr::app(
            LeanExpr::app(
                const_expr("List.cons", vec![LeanLevel::zero()]),
                LeanExpr::str_lit("Clone"),
            ),
            LeanExpr::app(
                LeanExpr::app(
                    const_expr("List.cons", vec![LeanLevel::zero()]),
                    LeanExpr::str_lit("Debug"),
                ),
                const_expr("List.nil", vec![LeanLevel::zero()]),
            ),
        );
        let expected = LeanExpr::app(
            const_expr("ImplTrait.mk", vec![LeanLevel::zero()]),
            trait_list,
        );
        assert_eq!(expr, expected);
    }

    #[test]
    fn test_translate_impl_trait_single() {
        let ctx = TranslationContext::new();

        // impl Iterator
        let ty = RustType::ImplTrait {
            traits: vec!["Iterator".to_string()],
        };
        let expr = translate_type(&ty, &ctx);

        // ImplTrait.mk ["Iterator"]
        let trait_list = LeanExpr::app(
            LeanExpr::app(
                const_expr("List.cons", vec![LeanLevel::zero()]),
                LeanExpr::str_lit("Iterator"),
            ),
            const_expr("List.nil", vec![LeanLevel::zero()]),
        );
        let expected = LeanExpr::app(
            const_expr("ImplTrait.mk", vec![LeanLevel::zero()]),
            trait_list,
        );
        assert_eq!(expr, expected);
    }

    #[test]
    fn test_translate_lifetime_variants() {
        // Test all lifetime variants
        assert_eq!(
            translate_lifetime(&Lifetime::Static),
            const_expr("RustLifetime.static", vec![])
        );

        assert_eq!(
            translate_lifetime(&Lifetime::Named("foo".to_string())),
            LeanExpr::app(
                const_expr("RustLifetime.named", vec![]),
                LeanExpr::str_lit("foo"),
            )
        );

        assert_eq!(
            translate_lifetime(&Lifetime::Anonymous(42)),
            LeanExpr::app(const_expr("RustLifetime.anonymous", vec![]), nat_lit(42),)
        );

        assert_eq!(
            translate_lifetime(&Lifetime::Existential(99)),
            LeanExpr::app(const_expr("RustLifetime.existential", vec![]), nat_lit(99),)
        );
    }

    #[test]
    fn test_translate_slice_type() {
        let ctx = TranslationContext::new();

        // [u32] - slice of u32
        let ty = RustType::Slice {
            elem: Box::new(RustType::Uint(UintType::U32)),
        };
        let expr = translate_type(&ty, &ctx);

        // RustSlice UInt32
        let expected = LeanExpr::app(
            const_expr("RustSlice", vec![LeanLevel::zero()]),
            const_expr("UInt32", vec![]),
        );
        assert_eq!(expr, expected);
    }

    #[test]
    fn test_translate_slice_nested() {
        let ctx = TranslationContext::new();

        // [[bool]] - slice of slice of bool
        let ty = RustType::Slice {
            elem: Box::new(RustType::Slice {
                elem: Box::new(RustType::Bool),
            }),
        };
        let expr = translate_type(&ty, &ctx);

        // RustSlice (RustSlice Bool)
        let inner = LeanExpr::app(
            const_expr("RustSlice", vec![LeanLevel::zero()]),
            const_expr("Bool", vec![]),
        );
        let expected = LeanExpr::app(const_expr("RustSlice", vec![LeanLevel::zero()]), inner);
        assert_eq!(expr, expected);
    }

    #[test]
    fn test_translate_str_type() {
        let ctx = TranslationContext::new();

        // str - string slice
        let ty = RustType::Str;
        let expr = translate_type(&ty, &ctx);

        // RustStr
        let expected = const_expr("RustStr", vec![]);
        assert_eq!(expr, expected);
    }

    #[test]
    fn test_translate_ref_to_slice() {
        let ctx = TranslationContext::new();

        // &[i32] - reference to slice
        let ty = RustType::Reference {
            lifetime: Lifetime::Static,
            mutability: Mutability::Shared,
            inner: Box::new(RustType::Slice {
                elem: Box::new(RustType::Int(crate::types::IntType::I32)),
            }),
        };
        let expr = translate_type(&ty, &ctx);

        // Ref (RustSlice Int32)
        let slice_ty = LeanExpr::app(
            const_expr("RustSlice", vec![LeanLevel::zero()]),
            const_expr("Int32", vec![]),
        );
        let expected = LeanExpr::app(const_expr("Ref", vec![LeanLevel::zero()]), slice_ty);
        assert_eq!(expr, expected);
    }

    #[test]
    fn test_translate_ref_to_str() {
        let ctx = TranslationContext::new();

        // &str - reference to string slice
        let ty = RustType::Reference {
            lifetime: Lifetime::Static,
            mutability: Mutability::Shared,
            inner: Box::new(RustType::Str),
        };
        let expr = translate_type(&ty, &ctx);

        // Ref RustStr
        let expected = LeanExpr::app(
            const_expr("Ref", vec![LeanLevel::zero()]),
            const_expr("RustStr", vec![]),
        );
        assert_eq!(expr, expected);
    }

    // -------------------------------------------------------------------
    // Generics hoisting: type params -> Π-telescope CIC types.
    // -------------------------------------------------------------------

    use crate::types::{TypeParamDef, TypeVar};

    /// `TypeParamDef` with a given id, name, and no bounds.
    fn tp(id: u32, name: &str) -> TypeParamDef {
        TypeParamDef {
            id,
            name: name.to_string(),
            bounds: vec![],
        }
    }

    /// `RustType::TypeParam` referencing the param with the given id/name.
    fn type_param(id: u32, name: &str) -> RustType {
        RustType::TypeParam(TypeVar {
            id,
            name: Some(name.to_string()),
        })
    }

    /// Unwrap one `Π` binder, returning (binder type, body).
    fn expect_pi(e: &LeanExpr) -> (LeanExpr, LeanExpr) {
        match e.kind() {
            ExprKind::Pi(_, ty, body) => ((**ty).clone(), (**body).clone()),
            other => panic!("expected Pi binder, got {other:?}"),
        }
    }

    /// `Type 0` (`Sort 1`) is what hoisted params are bound at.
    fn is_type_0_sort(e: &LeanExpr) -> bool {
        matches!(e.kind(), ExprKind::Sort(l) if !l.is_zero())
    }

    #[test]
    fn test_hoist_empty_params_is_passthrough() {
        let mut ctx = TranslationContext::new();
        // No type params: identical to translate_type.
        let ty = RustType::Uint(UintType::U32);
        let hoisted = translate_generic_type(&ty, &[], &mut ctx).expect("no params hoists");
        assert_eq!(hoisted, translate_type(&ty, &ctx));
    }

    #[test]
    fn test_hoist_option_param_becomes_pi_over_bound_var() {
        let mut ctx = TranslationContext::new();
        // Option<T> with <T>  ==>  Π (T : Type), Option.{0} (BVar 0)
        let ty = RustType::Option {
            inner: Box::new(type_param(0, "T")),
        };
        let hoisted =
            translate_generic_type(&ty, &[tp(0, "T")], &mut ctx).expect("Option<T> hoists");

        let (binder_ty, body) = expect_pi(&hoisted);
        assert!(
            is_type_0_sort(&binder_ty),
            "param T must be bound at Type 0, got {:?}",
            binder_ty.kind()
        );
        // Body is `Option.{0} (BVar 0)` — the occurrence became the bound var,
        // NOT the opaque RustTypeParam constant.
        match body.kind() {
            ExprKind::App(f, arg) => {
                assert!(f.is_const(), "head should be the Option constant");
                assert!(
                    matches!(arg.kind(), ExprKind::BVar(0)),
                    "argument should be the Π-bound variable BVar(0), got {:?}",
                    arg.kind()
                );
            }
            other => panic!("expected `Option T`, got {other:?}"),
        }
        // No opaque RustTypeParam constant leaked.
        assert!(
            !mentions_const(&hoisted, "RustTypeParam"),
            "hoisted type must not contain the opaque RustTypeParam encoding"
        );
    }

    #[test]
    fn test_hoist_identity_signature_kernel_typechecks() {
        use clean_kernel::{Environment, TypeChecker};
        let mut ctx = TranslationContext::new();
        // `fn id<T>(x: T) -> T`  ==>  Π (T : Type), T → T   (env-free)
        let ty = RustType::Function {
            params: vec![type_param(0, "T")],
            ret: Box::new(type_param(0, "T")),
        };
        let hoisted = translate_generic_type(&ty, &[tp(0, "T")], &mut ctx).expect("id<T> hoists");

        // Structural: Π (T:Type), Π (_:BVar0), BVar1
        let (binder_ty, body) = expect_pi(&hoisted);
        assert!(is_type_0_sort(&binder_ty));
        let (arrow_dom, arrow_cod) = expect_pi(&body);
        assert!(
            matches!(arrow_dom.kind(), ExprKind::BVar(0)),
            "arrow domain should reference T (BVar 0 under the type binder), got {:?}",
            arrow_dom.kind()
        );
        assert!(
            matches!(arrow_cod.kind(), ExprKind::BVar(1)),
            "arrow codomain should reference T (BVar 1 under arrow), got {:?}",
            arrow_cod.kind()
        );

        // Kernel check: a closed, env-free CIC type must infer a sort.
        let env = Environment::new();
        let tc = TypeChecker::new(&env);
        let inferred = tc
            .infer_type(&hoisted)
            .expect("Π (T:Type), T → T must kernel-typecheck");
        assert!(
            inferred.is_sort(),
            "the type of a hoisted signature must itself be a Sort, got {:?}",
            inferred.kind()
        );
    }

    #[test]
    fn test_hoist_two_params_ordering_kernel_typechecks() {
        use clean_kernel::{Environment, TypeChecker};
        let mut ctx = TranslationContext::new();
        // `fn f<T, U>(x: T) -> U`  ==>  Π (T:Type) (U:Type), T → U   (env-free)
        let ty = RustType::Function {
            params: vec![type_param(0, "T")],
            ret: Box::new(type_param(1, "U")),
        };
        let hoisted = translate_generic_type(&ty, &[tp(0, "T"), tp(1, "U")], &mut ctx)
            .expect("f<T,U> hoists");

        // Π (T:Type), Π (U:Type), Π (_:BVar1=T), (BVar1=U)
        let (t_binder, after_t) = expect_pi(&hoisted);
        let (u_binder, after_u) = expect_pi(&after_t);
        assert!(is_type_0_sort(&t_binder) && is_type_0_sort(&u_binder));
        let (arrow_dom, arrow_cod) = expect_pi(&after_u);
        // Under the two type binders, T = BVar(1), U = BVar(0); domain is T.
        assert!(
            matches!(arrow_dom.kind(), ExprKind::BVar(1)),
            "domain must be T = BVar(1), got {:?}",
            arrow_dom.kind()
        );
        // Under T, U, and the arrow binder, U = BVar(1); codomain is U (not T).
        assert!(
            matches!(arrow_cod.kind(), ExprKind::BVar(1)),
            "codomain must be U = BVar(1), got {:?}",
            arrow_cod.kind()
        );

        let env = Environment::new();
        let tc = TypeChecker::new(&env);
        assert!(
            tc.infer_type(&hoisted).is_ok(),
            "Π (T:Type)(U:Type), T → U must kernel-typecheck"
        );
    }

    #[test]
    fn test_hoist_two_field_generic_struct_tuple() {
        let mut ctx = TranslationContext::new();
        // A 2-field generic struct `Pair<T, U>(T, U)` field-tuple
        //   ==>  Π (T:Type) (U:Type), Prod.{0,0} (BVar 1) (BVar 0)
        let ty = RustType::Tuple(vec![type_param(0, "T"), type_param(1, "U")]);
        let hoisted = translate_generic_type(&ty, &[tp(0, "T"), tp(1, "U")], &mut ctx)
            .expect("Pair<T,U> hoists");

        let (_t, after_t) = expect_pi(&hoisted);
        let (_u, prod) = expect_pi(&after_t);
        // prod = ((Prod T) U) with T = BVar(1), U = BVar(0).
        match prod.kind() {
            ExprKind::App(prod_t, u_arg) => {
                assert!(
                    matches!(u_arg.kind(), ExprKind::BVar(0)),
                    "second component must be U = BVar(0), got {:?}",
                    u_arg.kind()
                );
                match prod_t.kind() {
                    ExprKind::App(head, t_arg) => {
                        assert!(head.is_const(), "head should be Prod");
                        assert!(
                            matches!(t_arg.kind(), ExprKind::BVar(1)),
                            "first component must be T = BVar(1), got {:?}",
                            t_arg.kind()
                        );
                    }
                    other => panic!("expected `Prod T`, got {other:?}"),
                }
            }
            other => panic!("expected `Prod T U`, got {other:?}"),
        }
    }

    #[test]
    fn test_hoist_fails_closed_on_associated_type_bound() {
        let mut ctx = TranslationContext::new();
        // `<I: Iterator<Item = u32>>` — associated-type bound is unsupported.
        let ty = type_param(0, "I");
        let param = TypeParamDef {
            id: 0,
            name: "I".to_string(),
            bounds: vec!["Iterator<Item = u32>".to_string()],
        };
        let result = translate_generic_type(&ty, &[param], &mut ctx);
        assert!(
            matches!(result, Err(RustSemError::GenericHoistUnsupported { .. })),
            "associated-type bound must fail closed, got {result:?}"
        );
    }

    #[test]
    fn test_hoist_simple_bound_is_erased_and_hoisted() {
        let mut ctx = TranslationContext::new();
        // `<T: Clone>` — a plain marker bound is sound to erase; T still hoists.
        let ty = RustType::Option {
            inner: Box::new(type_param(0, "T")),
        };
        let param = TypeParamDef {
            id: 0,
            name: "T".to_string(),
            bounds: vec!["Clone".to_string()],
        };
        let hoisted = translate_generic_type(&ty, &[param], &mut ctx)
            .expect("T: Clone hoists (bound erased)");
        let (binder_ty, _body) = expect_pi(&hoisted);
        assert!(is_type_0_sort(&binder_ty));
    }

    /// Whether `e` mentions a constant whose name renders as `needle`.
    fn mentions_const(e: &LeanExpr, needle: &str) -> bool {
        match e.kind() {
            ExprKind::Const(name, _) => name.to_string().contains(needle),
            ExprKind::App(f, a) => mentions_const(f, needle) || mentions_const(a, needle),
            ExprKind::Pi(_, t, b) | ExprKind::Lam(_, t, b) => {
                mentions_const(t, needle) || mentions_const(b, needle)
            }
            _ => false,
        }
    }
}

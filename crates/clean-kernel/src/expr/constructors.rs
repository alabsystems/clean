// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Expr constructors, predicates, and application spine helpers.
//!
//! All items are `impl Expr` methods. Constructors create expressions via
//! `Expr::from_kind()`, predicates query `self.kind`, and app helpers
//! iterate the application spine.

use super::{
    AppArgs, AppArgsIter, BigNat, BinderData, BinderInfo, Expr, ExprKind, FVarId, LevelVec,
    Literal, MDataMap,
};
use crate::level::Level;
use crate::name::Name;
use std::sync::Arc;

impl Expr {
    /// Create a bound variable referencing the `idx`-th enclosing binder.
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `ExprKind::BVar(idx)`
    /// ENSURES: Result is well-formed (valid AST node)
    /// ENSURES: Deterministic - same input yields same output
    pub fn bvar(idx: u32) -> Self {
        Expr::from_kind(ExprKind::BVar(idx))
    }

    /// Create a free variable with the given unique identifier.
    pub fn fvar(id: FVarId) -> Self {
        Expr::from_kind(ExprKind::FVar(id))
    }

    /// Create a sort (universe level).
    pub fn sort(level: Level) -> Self {
        Expr::from_kind(ExprKind::Sort(level))
    }

    /// Create Prop (Sort 0).
    pub fn prop() -> Self {
        Expr::from_kind(ExprKind::Sort(Level::zero()))
    }

    /// Create Type (Sort 1).
    pub fn type_() -> Self {
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())))
    }

    /// Create a constant reference.
    pub fn const_(name: Name, levels: impl Into<LevelVec>) -> Self {
        Expr::from_kind(ExprKind::Const(name, levels.into()))
    }

    /// Create a function application.
    pub fn app(func: Expr, arg: Expr) -> Self {
        Expr::from_kind(ExprKind::App(Arc::new(func), Arc::new(arg)))
    }

    /// Create a function application from already-`Arc`-wrapped children,
    /// preserving physical `Arc` sharing (no re-allocation of the children).
    ///
    /// Use when the children are shared DAG nodes — e.g. `.mathverse` shard
    /// reconstruction, where the same arena node is referenced by many parents.
    /// Building via [`Expr::app`] would clone each child into a fresh `Arc`,
    /// losing the sharing and turning the linear DAG into an exponential tree
    /// for the (structural-equality-driven) kernel walks. See
    /// `designs/2026-07-06-carrier-whnf-perf.md` (F2). Produces a
    /// structurally-identical `Expr` to `Expr::app((*func).clone(),
    /// (*arg).clone())` — only more shared.
    pub fn app_arc(func: Arc<Expr>, arg: Arc<Expr>) -> Self {
        Expr::from_kind(ExprKind::App(func, arg))
    }

    /// `Arc`-sharing lambda constructor. See [`Expr::app_arc`].
    pub fn lam_arc(bd: impl Into<BinderData>, ty: Arc<Expr>, body: Arc<Expr>) -> Self {
        Expr::from_kind(ExprKind::Lam(bd.into(), ty, body))
    }

    /// `Arc`-sharing Pi constructor. See [`Expr::app_arc`].
    pub fn pi_arc(bd: impl Into<BinderData>, ty: Arc<Expr>, body: Arc<Expr>) -> Self {
        Expr::from_kind(ExprKind::Pi(bd.into(), ty, body))
    }

    /// `Arc`-sharing let constructor. See [`Expr::app_arc`].
    pub fn let_named_arc(
        name: Name,
        ty: Arc<Expr>,
        val: Arc<Expr>,
        body: Arc<Expr>,
        non_dep: bool,
    ) -> Self {
        Expr::from_kind(ExprKind::Let(name, ty, val, body, non_dep))
    }

    /// `Arc`-sharing projection constructor. See [`Expr::app_arc`].
    pub fn proj_arc(struct_name: Name, idx: u32, expr: Arc<Expr>) -> Self {
        Expr::from_kind(ExprKind::Proj(struct_name, idx, expr))
    }

    /// Create a multi-argument application.
    ///
    /// `apps(f, [a, b, c])` creates `(((f a) b) c)`
    pub fn apps(func: Expr, args: impl IntoIterator<Item = Expr>) -> Self {
        args.into_iter().fold(func, Expr::app)
    }

    /// Create a multi-argument application from references.
    pub fn apps_ref(func: Expr, args: &[Expr]) -> Self {
        args.iter().fold(func, |f, a| Expr::app(f, a.clone()))
    }

    /// Create a lambda abstraction.
    pub fn lam(bd: impl Into<BinderData>, ty: Expr, body: Expr) -> Self {
        Expr::from_kind(ExprKind::Lam(bd.into(), Arc::new(ty), Arc::new(body)))
    }

    /// Create a dependent function type (Pi type).
    pub fn pi(bd: impl Into<BinderData>, ty: Expr, body: Expr) -> Self {
        Expr::from_kind(ExprKind::Pi(bd.into(), Arc::new(ty), Arc::new(body)))
    }

    /// Create an arrow type (non-dependent pi).
    pub fn arrow(from: Expr, to: Expr) -> Self {
        Expr::from_kind(ExprKind::Pi(
            BinderInfo::Default.into(),
            Arc::new(from),
            Arc::new(to),
        ))
    }

    /// Create a let binding with anonymous name and nonDep=false.
    ///
    /// **Deprecated:** Use `Expr::let_named()` instead, which requires explicit
    /// name and non_dep parameters. This constructor silently discards the Let
    /// name (replacing with `Name::anon()`) and forces `non_dep = false`,
    /// masking bugs where callers reconstruct Let expressions from pattern
    /// matches but lose the original name and non_dep flag.
    #[deprecated(note = "use Expr::let_named() for explicit name and non_dep control")]
    pub fn let_(ty: Expr, val: Expr, body: Expr) -> Self {
        Expr::from_kind(ExprKind::Let(
            Name::anon(),
            Arc::new(ty),
            Arc::new(val),
            Arc::new(body),
            false,
        ))
    }

    /// Create a let binding with explicit name and nonDep flag.
    pub fn let_named(name: Name, ty: Expr, val: Expr, body: Expr, non_dep: bool) -> Self {
        Expr::from_kind(ExprKind::Let(
            name,
            Arc::new(ty),
            Arc::new(val),
            Arc::new(body),
            non_dep,
        ))
    }

    /// Create a natural number literal.
    pub fn nat_lit(n: u64) -> Self {
        Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(n))))
    }

    /// Create a natural number literal from a `u128` (values > `u64::MAX` use the
    /// `BigNat` arbitrary-precision representation). Needed to encode `i128`/`u128`
    /// type thresholds (e.g. `i128::MAX`) as kernel `Int.ofNat`/`Int.negSucc` operands.
    pub fn nat_lit_u128(n: u128) -> Self {
        let lo = n as u64;
        let hi = (n >> 64) as u64;
        Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::from_limbs(vec![
            lo, hi,
        ]))))
    }

    /// Create a natural number literal from a BigNat value.
    ///
    /// Handles both small and big naturals, unlike `nat_lit` which only
    /// accepts u64. Used by native reducers that operate on BigNat directly.
    pub fn bignat_lit(n: BigNat) -> Self {
        Expr::from_kind(ExprKind::Lit(Literal::Nat(n)))
    }

    /// Create a string literal.
    pub fn str_lit(s: impl AsRef<str>) -> Self {
        Expr::from_kind(ExprKind::Lit(Literal::String(Arc::from(s.as_ref()))))
    }

    /// Create a constant reference from a dotted string name.
    ///
    /// # Example
    /// ```
    /// use clean_kernel::Expr;
    /// let nat = Expr::const_str("Nat");
    /// let nat_add = Expr::const_str("Nat.add");
    /// ```
    pub fn const_str(s: &str) -> Self {
        Expr::from_kind(ExprKind::Const(Name::from_string(s), LevelVec::new()))
    }

    /// Create a constant reference from a dotted string name with universe levels.
    ///
    /// # Example
    /// ```
    /// use clean_kernel::{Expr, Level};
    /// let list_nat = Expr::const_str_levels("List", vec![Level::zero()]);
    /// ```
    pub fn const_str_levels(s: &str, levels: impl Into<LevelVec>) -> Self {
        Expr::from_kind(ExprKind::Const(Name::from_string(s), levels.into()))
    }

    /// Create a structure projection.
    ///
    /// # Contract
    ///
    /// REQUIRES: `struct_name` refers to a structure type
    /// REQUIRES: `idx` is a valid field index for the structure
    /// REQUIRES: `expr` is well-formed
    ///
    /// ENSURES: Returns `ExprKind::Proj(struct_name, idx, expr)`
    /// ENSURES: Result is well-formed (valid AST node)
    /// ENSURES: Deterministic - same inputs yield same output
    pub fn proj(struct_name: Name, idx: u32, expr: Expr) -> Self {
        Expr::from_kind(ExprKind::Proj(struct_name, idx, Arc::new(expr)))
    }

    /// Create a metadata wrapper.
    pub fn mdata(metadata: MDataMap, expr: Expr) -> Self {
        Expr::from_kind(ExprKind::MData(metadata, Arc::new(expr)))
    }

    /// Get the inner expression if this is an MData, otherwise self.
    ///
    /// Uses iterative traversal to avoid stack overflow on deeply nested MData.
    pub fn strip_mdata(&self) -> &Expr {
        let mut current = self;
        while let ExprKind::MData(_, inner) = &current.kind {
            current = inner;
        }
        current
    }

    /// Check if this expression is a sort.
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `matches!(self, ExprKind::Sort(_))`
    /// ENSURES: Pure - no side effects
    pub fn is_sort(&self) -> bool {
        matches!(self.kind, ExprKind::Sort(_))
    }

    /// Check if this is Prop (Sort 0).
    pub fn is_prop(&self) -> bool {
        matches!(&self.kind, ExprKind::Sort(l) if l.is_zero())
    }

    /// Check if this expression is an application.
    pub fn is_app(&self) -> bool {
        matches!(self.kind, ExprKind::App(_, _))
    }

    /// Check if this expression is a pi/forall type.
    pub fn is_pi(&self) -> bool {
        matches!(self.kind, ExprKind::Pi(_, _, _))
    }

    /// Check if this expression is a lambda.
    pub fn is_lam(&self) -> bool {
        matches!(self.kind, ExprKind::Lam(_, _, _))
    }

    /// Check if this expression is a constant reference.
    pub fn is_const(&self) -> bool {
        matches!(self.kind, ExprKind::Const(_, _))
    }

    /// Check if this expression is a free variable.
    pub fn is_fvar(&self) -> bool {
        matches!(self.kind, ExprKind::FVar(_))
    }

    /// Check if this expression is a bound variable.
    pub fn is_bvar(&self) -> bool {
        matches!(self.kind, ExprKind::BVar(_))
    }

    /// Check if this expression is a let binding.
    pub fn is_let(&self) -> bool {
        matches!(self.kind, ExprKind::Let(_, _, _, _, _))
    }

    /// Check if this expression is a literal.
    pub fn is_lit(&self) -> bool {
        matches!(self.kind, ExprKind::Lit(_))
    }

    /// Check if this expression is a projection.
    pub fn is_proj(&self) -> bool {
        matches!(self.kind, ExprKind::Proj(_, _, _))
    }

    /// Get the head of an application spine.
    ///
    /// Uses iterative traversal to avoid stack overflow on deeply nested applications.
    pub fn get_app_fn(&self) -> &Expr {
        let mut current = self;
        while let ExprKind::App(f, _) = &current.kind {
            current = f;
        }
        current
    }

    /// Get all arguments of an application spine (allocates Vec).
    ///
    /// For hot paths, prefer `get_app_args_iter()` which avoids allocation.
    ///
    /// # Contract
    ///
    /// ENSURES: For `f a₁ a₂ ... aₙ`, returns `[a₁, a₂, ..., aₙ]` in source order
    /// ENSURES: For non-App expressions, returns empty SmallVec (AppArgs)
    /// ENSURES: `get_app_args().len() == get_app_num_args()`
    pub fn get_app_args(&self) -> AppArgs<'_> {
        // Collect from iterator and reverse (iterator yields in application order)
        let mut args: AppArgs<'_> = self.get_app_args_iter().collect();
        args.reverse();
        args
    }

    /// Get arguments of an application spine as an iterator (zero allocation).
    ///
    /// Returns arguments in **application order** (innermost first):
    /// For `f a b c`, yields `c, b, a`.
    ///
    /// Use `.rev()` or `.collect::<Vec<_>>().reverse()` if source order is needed.
    ///
    /// # Contract
    ///
    /// ENSURES: For `f a₁ a₂ ... aₙ`, yields `aₙ, ..., a₂, a₁` (reverse order)
    /// ENSURES: For non-App expressions, yields nothing
    /// ENSURES: Zero allocation - returns iterator over existing data
    pub fn get_app_args_iter(&self) -> AppArgsIter<'_> {
        AppArgsIter { curr: self }
    }

    /// Get the number of arguments in an application spine (zero allocation).
    ///
    /// # Contract
    ///
    /// ENSURES: For `f a₁ a₂ ... aₙ`, returns `n`
    /// ENSURES: For non-App expressions, returns `0`
    /// ENSURES: `get_app_num_args() == get_app_args().len()`
    /// ENSURES: Zero allocation - uses iterator counting
    /// ENSURES: Pure - no side effects
    pub fn get_app_num_args(&self) -> usize {
        self.get_app_args_iter().count()
    }
}

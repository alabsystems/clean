// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! TLA+ to clean Expression Encoding
//!
//! Copyright 2026 Andrew Yates
//! Licensed under Apache-2.0
//!
//! This module defines the TLA+ expression language and its translation
//! to clean kernel expressions.
//!
//! ## Encoding Strategy
//!
//! TLA+ is untyped set theory. Everything is type `c` (constant).
//! We encode this as:
//!
//! | TLA+ | clean |
//! |------|-------|
//! | `x ∈ S` | `TLA.mem x S` |
//! | `S ⊆ T` | `TLA.subset S T` |
//! | `{x ∈ S : P(x)}` | `TLA.setOf S (λ x. P x)` |
//! | `∀x ∈ S : P(x)` | `TLA.forallIn S (λ x. P x)` |
//! | `∃x ∈ S : P(x)` | `TLA.existsIn S (λ x. P x)` |
//! | `DOMAIN f` | `TLA.domain f` |
//! | `f[x]` | `TLA.apply f x` |

use crate::tla_core;
use crate::TlaError;
use clean_kernel::env::Environment;
use clean_kernel::expr::{BinderInfo, Expr};
use clean_kernel::name::Name;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// TLA+ expression AST
///
/// Represents the abstract syntax of TLA+ expressions before
/// translation to clean.
///
/// # Deprecation Notice
///
/// This type is a clean-local duplicate of [`tla_core::ast::Expr`]. New code
/// should accept `tla_core::ast::Expr` directly and convert via
/// [`TlaExpr::from_tla_core`]. This enum will eventually be replaced by
/// direct use of the canonical tla-core AST.
///
/// ## Variant Mapping: `TlaExpr` vs `tla_core::ast::Expr`
///
/// | `TlaExpr`            | `tla_core::ast::Expr`           | Notes                            |
/// |----------------------|---------------------------------|----------------------------------|
/// | `Var(String)`        | `Ident(String, NameId)`         | NameId dropped                   |
/// | `Var(String)`        | `StateVar(String, u16, NameId)` | index + NameId dropped           |
/// | `Const(String)`      | `OpRef(String)`                 |                                  |
/// | `True` / `False`     | `Bool(bool)`                    |                                  |
/// | `Int(i64)`           | `Int(BigInt)`                   | range-checked conversion         |
/// | `Str(String)`        | `String(String)`                |                                  |
/// | `Mem(_, _)`          | `In(_, _)`                      |                                  |
/// | `Subset(_, _)`       | `Subseteq(_, _)`                |                                  |
/// | `SetEnum(Vec)`       | `SetEnum(Vec)`                  |                                  |
/// | `SetOf(_, _, _)`     | `SetFilter(BoundVar, _)`        | destructured                     |
/// | `SetMap(_, _, _, _)` | `SetBuilder(_, Vec<BoundVar>)`  | single-binder only               |
/// | `Union(_, _)`        | `Union(_, _)`                   |                                  |
/// | `Inter(_, _)`        | `Intersect(_, _)`               |                                  |
/// | `Diff(_, _)`         | `SetMinus(_, _)`                |                                  |
/// | `PowerSet(_)`        | `Powerset(_)`                   |                                  |
/// | `BigUnion(_)`        | `BigUnion(_)`                   |                                  |
/// | `Domain(_)`          | `Domain(_)`                     |                                  |
/// | `Apply(_, _)`        | `FuncApply(_, _)`               |                                  |
/// | `Func(_, _, _)`      | `FuncDef(Vec<BoundVar>, _)`     | single-binder only               |
/// | `Record(Vec)`        | `Record(Vec)`                   |                                  |
/// | `Field(_, _)`        | `RecordAccess(_, _)`            |                                  |
/// | `Tuple(Vec)`         | `Tuple(Vec)`                    |                                  |
/// | `IfThenElse(_, _, _)`| `If(_, _, _)`                   |                                  |
/// | `Case(_, _)`         | `Case(Vec<CaseArm>, Option)`   |                                  |
/// | `Let(_, _, _)`       | `Let(Vec<OperatorDef>, _)`      | non-param, non-recursive, no fwd |
/// | `OpApply(_, Vec)`    | `Apply(_, Vec)`                 | callee must be name              |
/// | `OpApply(_, Vec)`    | `ModuleRef(_, _, Vec)`          | qualified name                   |
/// | `Arith(op, _, _)`    | `Add/Sub/Mul/Div/IntDiv/Mod/Pow`| factored into separate variants  |
/// | `Cmp(op, _, _)`      | `Lt/Leq/Gt/Geq`                | factored into separate variants  |
/// | `Neg(_)`             | `Neg(_)`                        |                                  |
/// | `Range(_, _)`        | `Range(_, _)`                   |                                  |
/// | `Prime(_)`           | `Prime(_)`                      | next-state value (`TLA.prime`)   |
/// | `TemporalFormula(_)` | `Always`/`Eventually`/`LeadsTo` | temporal formula in value pos.   |
/// | `TemporalFormula(_)` | `WeakFair`/`StrongFair`         | fairness in value pos.           |
/// | `TemporalFormula(_)` | `Enabled`/`Unchanged`           | action modality in value pos.    |
/// | `Choose(_, _, _)`    | `Choose(BoundVar, _)`           | bounded form only (`TLA.choose`) |
/// | `FuncSet(_, _)`      | `FuncSet(_, _)`                 | `[S -> T]` (`TLA.funcSet`)       |
/// | `Times(Vec)`         | `Times(Vec)`                    | `S \X T` (`TLA.times`)           |
/// | `Except(_, Vec)`     | `Except(_, Vec)`                | `[f EXCEPT ...]` (`TLA.except`)  |
/// | `RecordSet(Vec)`     | `RecordSet(Vec)`                | `[f: S]` (`TLA.recordSet`)       |
/// | --                   | `Lambda`                        | **not representable**            |
/// | --                   | `SubstIn`, `InstanceExpr`       | **not representable**            |
/// | --                   | unbounded `Choose` (no domain)  | **not representable**            |
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum TlaExpr {
    /// Variable reference
    Var(String),

    /// Constant (defined in context)
    Const(String),

    /// Boolean literals
    True,
    False,

    /// Integer literal
    Int(i64),

    /// String literal
    Str(String),

    /// Set membership: x ∈ S
    Mem(Box<TlaExpr>, Box<TlaExpr>),

    /// Subset: S ⊆ T
    Subset(Box<TlaExpr>, Box<TlaExpr>),

    /// Set equality: S = T
    SetEq(Box<TlaExpr>, Box<TlaExpr>),

    /// Set enumeration: {a, b, c}
    SetEnum(Vec<TlaExpr>),

    /// Set comprehension: {x ∈ S : P(x)}
    SetOf(Box<TlaExpr>, String, Box<TlaFormula>),

    /// Subset filtering: {e : x ∈ S, P(x)}
    SetMap(Box<TlaExpr>, String, Box<TlaExpr>, Option<Box<TlaFormula>>),

    /// Union: S ∪ T
    Union(Box<TlaExpr>, Box<TlaExpr>),

    /// Intersection: S ∩ T
    Inter(Box<TlaExpr>, Box<TlaExpr>),

    /// Set difference: S \ T
    Diff(Box<TlaExpr>, Box<TlaExpr>),

    /// Power set: SUBSET S
    PowerSet(Box<TlaExpr>),

    /// Union of set of sets: UNION S
    BigUnion(Box<TlaExpr>),

    /// Function domain: DOMAIN f
    Domain(Box<TlaExpr>),

    /// Function application: `f[x]`
    Apply(Box<TlaExpr>, Box<TlaExpr>),

    /// Function constructor: [x ∈ S |-> e]
    Func(String, Box<TlaExpr>, Box<TlaExpr>),

    /// Record: [field1 |-> v1, field2 |-> v2]
    Record(Vec<(String, TlaExpr)>),

    /// Record field access: r.field
    Field(Box<TlaExpr>, String),

    /// Tuple: <<a, b, c>>
    Tuple(Vec<TlaExpr>),

    /// Sequence: <<a, b, c>> as sequence
    Seq(Vec<TlaExpr>),

    /// CHOOSE: CHOOSE x ∈ S : P(x)
    Choose(String, Box<TlaExpr>, Box<TlaFormula>),

    /// IF-THEN-ELSE: IF P THEN a ELSE b
    IfThenElse(Box<TlaFormula>, Box<TlaExpr>, Box<TlaExpr>),

    /// CASE expression
    Case(Vec<(TlaFormula, TlaExpr)>, Option<Box<TlaExpr>>),

    /// LET expression: LET x == e IN body
    Let(String, Box<TlaExpr>, Box<TlaExpr>),

    /// Operator application: Op(a, b)
    OpApply(String, Vec<TlaExpr>),

    /// Arithmetic: +, -, *, /, %
    Arith(TlaArithOp, Box<TlaExpr>, Box<TlaExpr>),

    /// Comparison: <, <=, >, >=
    Cmp(TlaCmpOp, Box<TlaExpr>, Box<TlaExpr>),

    /// Naturals: Nat
    Nat,

    /// Integers: Int
    Integer,

    /// Reals: Real
    Real,

    /// Boolean set: BOOLEAN
    Boolean,

    /// Strings: STRING
    String_,

    /// Range: a..b
    Range(Box<TlaExpr>, Box<TlaExpr>),

    /// Unary arithmetic negation: -x
    Neg(Box<TlaExpr>),

    /// Prime / next-state value: `e'`
    ///
    /// In TLA+ a primed expression denotes the value of `e` in the *successor*
    /// state of a step. It is deliberately a distinct operator
    /// (`TLA.prime`) so that the next-state value is never conflated with the
    /// current-state value — soundness requires `x` and `x'` to be different
    /// terms.
    Prime(Box<TlaExpr>),

    /// Function set: `[S -> T]` — the set of all total functions whose domain
    /// is `S` and whose values lie in `T`. Encoded as the binary `TLA.funcSet`
    /// constant (`TLA.funcSet S T`).
    FuncSet(Box<TlaExpr>, Box<TlaExpr>),

    /// Cartesian product: `S \X T \X ...` — the set of tuples `<<s, t, ...>>`
    /// with each component drawn from the corresponding factor. There are
    /// always at least two factors; they are folded left-associatively over the
    /// binary `TLA.times` constant (`TLA.times (TLA.times S T) U`).
    Times(Vec<TlaExpr>),

    /// Function/record update: `[f EXCEPT !path1 = v1, !path2 = v2, ...]`.
    ///
    /// Each [`TlaExceptSpec`] names a path into `f` (a sequence of index `![e]`
    /// and field `!.name` selectors) and the value to install there. Specs are
    /// applied left-to-right by folding the binary `TLA.except` constant over
    /// `f`, so later specs see the result of earlier ones — matching TLA+'s
    /// sequential `EXCEPT` semantics. The path is reified as a `TLA.pathCons`
    /// list of `TLA.pathIndex`/`TLA.pathField` selectors terminated by
    /// `TLA.pathNil`, so deep (multi-element) updates are preserved exactly.
    Except(Box<TlaExpr>, Vec<TlaExceptSpec>),

    /// Record type / set constructor: `[f1: S1, f2: S2, ...]` — the set of all
    /// records whose `f_i` field is drawn from set `S_i`. This is the
    /// set-valued analogue of [`TlaExpr::Record`] (which builds a single record
    /// value `[f1 |-> v1, ...]`). Each pair carries a field name and the set
    /// its value ranges over; they are folded over the `TLA.recordSet`
    /// constants exactly as record *values* are folded over
    /// `TLA.singletonRecord`/`TLA.mergeRecords`.
    RecordSet(Vec<(String, TlaExpr)>),

    /// A temporal / propositional formula appearing in value position.
    ///
    /// TLA+ does not distinguish propositions from values: a temporal formula
    /// such as `[]<>P` (always-eventually) can be the body of an operator
    /// definition (`Liveness == []<>P`) or otherwise occur where a value
    /// expression is expected. Because [`TlaExpr`] has no native temporal
    /// variants — those live on [`TlaFormula`] — this variant embeds a full
    /// formula (possibly itself nested temporal) into the expression layer. It
    /// translates by delegating to [`TlaContext::translate_formula`], so the
    /// standard temporal semantics (e.g. `[]<>P` = infinitely often,
    /// `<>[]P` = eventually always) are preserved exactly.
    TemporalFormula(Box<TlaFormula>),
}

/// A single update clause of an `EXCEPT` expression: `!path = value`.
///
/// `path` is the (non-empty) sequence of selectors that locate the position to
/// overwrite — `![e]` for a function-index step and `!.name` for a record-field
/// step — and `value` is the replacement installed there.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct TlaExceptSpec {
    pub path: Vec<TlaExceptPath>,
    pub value: TlaExpr,
}

/// One step of an [`TlaExceptSpec`] path.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum TlaExceptPath {
    /// Function-index step `![e]` — select the value at key `e`.
    Index(TlaExpr),
    /// Record-field step `!.name` — select the named field.
    Field(String),
}

/// TLA+ arithmetic operators (binary)
///
/// # Deprecation Notice
///
/// These are factored out of `tla_core::ast::Expr` which uses separate
/// variants (`Add`, `Sub`, `Mul`, `Div`, `IntDiv`, `Mod`, `Pow`). This enum
/// will be removed when `TlaExpr` is replaced by `tla_core::ast::Expr`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum TlaArithOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    /// Exponentiation: `b ^ e` — the Naturals `^` operator.
    Pow,
}

/// TLA+ comparison operators
///
/// # Deprecation Notice
///
/// These are factored out of `tla_core::ast::Expr` which uses separate
/// variants (`Lt`, `Leq`, `Gt`, `Geq`). This enum will be removed
/// when `TlaExpr` is replaced by `tla_core::ast::Expr`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum TlaCmpOp {
    Lt,
    Le,
    Gt,
    Ge,
}

/// TLA+ formula (propositional/predicate logic)
///
/// # Deprecation Notice
///
/// `tla_core::ast::Expr` does not distinguish expressions from formulas --
/// the boolean/propositional layer is implicit. This separation exists only
/// in clean-tla to simplify the clean encoding (formulas map to `Prop`,
/// expressions map to `TLA.Value`). New code should accept
/// `tla_core::ast::Expr` and convert via [`TlaFormula::from_tla_core`].
///
/// ## Variant Mapping: `TlaFormula` vs `tla_core::ast::Expr`
///
/// | `TlaFormula`             | `tla_core::ast::Expr`        |
/// |--------------------------|------------------------------|
/// | `True` / `False`         | `Bool(true)` / `Bool(false)` |
/// | `Not(_)`                 | `Not(_)`                     |
/// | `And(_, _)`              | `And(_, _)`                  |
/// | `Or(_, _)`               | `Or(_, _)`                   |
/// | `Implies(_, _)`          | `Implies(_, _)`              |
/// | `Iff(_, _)`              | `Equiv(_, _)`                |
/// | `Forall(_, _)`           | `Forall(bounds, _)` (no domain) |
/// | `Exists(_, _)`           | `Exists(bounds, _)` (no domain) |
/// | `ForallIn(_, _, _)`      | `Forall(bounds, _)` (with domain) |
/// | `ExistsIn(_, _, _)`      | `Exists(bounds, _)` (with domain) |
/// | `Eq(_, _)`               | `Eq(_, _)`                   |
/// | `Mem(_, _)`              | `In(_, _)`                   |
/// | `Subset(_, _)`           | `Subseteq(_, _)`             |
/// | `Always(_)`              | `Always(_)`                  |
/// | `Eventually(_)`          | `Eventually(_)`              |
/// | `LeadsTo(_, _)`          | `LeadsTo(_, _)`              |
/// | `WeakFairness(_, _)`     | `WeakFair(_, _)`             |
/// | `StrongFairness(_, _)`   | `StrongFair(_, _)`           |
/// | `Unchanged(_)`           | `Unchanged(_)`               |
/// | `Enabled(_)`             | `Enabled(_)`                 |
/// | `Expr(TlaExpr)`          | (fallback: any non-formula)  |
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum TlaFormula {
    /// Boolean expression promoted to formula
    Expr(TlaExpr),

    /// Logical true
    True,

    /// Logical false
    False,

    /// Negation: ¬P
    Not(Box<TlaFormula>),

    /// Conjunction: P ∧ Q
    And(Box<TlaFormula>, Box<TlaFormula>),

    /// Disjunction: P ∨ Q
    Or(Box<TlaFormula>, Box<TlaFormula>),

    /// Implication: P ⇒ Q
    Implies(Box<TlaFormula>, Box<TlaFormula>),

    /// Equivalence: P ⇔ Q
    Iff(Box<TlaFormula>, Box<TlaFormula>),

    /// Universal quantification: ∀x : P(x)
    Forall(String, Box<TlaFormula>),

    /// Existential quantification: ∃x : P(x)
    Exists(String, Box<TlaFormula>),

    /// Bounded universal: ∀x ∈ S : P(x)
    ForallIn(String, Box<TlaExpr>, Box<TlaFormula>),

    /// Bounded existential: ∃x ∈ S : P(x)
    ExistsIn(String, Box<TlaExpr>, Box<TlaFormula>),

    /// Equality: a = b
    Eq(Box<TlaExpr>, Box<TlaExpr>),

    /// Membership: a ∈ S (as formula)
    Mem(Box<TlaExpr>, Box<TlaExpr>),

    /// Subset: S ⊆ T (as formula)
    Subset(Box<TlaExpr>, Box<TlaExpr>),

    // ================================================================
    // Temporal operators (for future extension)
    // ================================================================
    /// Always: □P
    Always(Box<TlaFormula>),

    /// Eventually: ◇P
    Eventually(Box<TlaFormula>),

    /// Leads-to: P ~> Q
    LeadsTo(Box<TlaFormula>, Box<TlaFormula>),

    /// Weak fairness: WF_vars(A)
    WeakFairness(Box<TlaExpr>, Box<TlaFormula>),

    /// Strong fairness: SF_vars(A)
    StrongFairness(Box<TlaExpr>, Box<TlaFormula>),

    /// UNCHANGED v — the action predicate `v' = v`.
    ///
    /// Semantically, `UNCHANGED e` asserts that the next-state value of `e`
    /// equals its current-state value. We keep the unprimed expression here and
    /// expand to `Eq(Prime(e), e)` during translation so the soundness of the
    /// next-state distinction is preserved.
    Unchanged(Box<TlaExpr>),

    /// ENABLED A — the state predicate "action `A` can be taken from the
    /// current state" (there exists a successor state satisfying `A`).
    ///
    /// ENABLED is a primitive action modality; it is not reducible to the
    /// propositional layer without quantifying over successor states, so it is
    /// encoded as a dedicated operator (`FixedPoint.TLA_enabled`).
    Enabled(Box<TlaFormula>),
}

/// TLA+ operator definition
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct TlaOperator {
    /// Operator name
    pub name: String,
    /// Parameter names
    pub params: Vec<String>,
    /// Operator body
    pub body: TlaExpr,
}

// ============================================================================
// Structured conversion layer: tla_core::ast → clean-tla types
//
// These TryFrom impls delegate to the `from_tla_core()` methods defined in
// the `core_ast` module, providing idiomatic Rust conversion traits so callers
// can use `TlaExpr::try_from(&spanned_expr)` instead of the ad-hoc method.
// ============================================================================

impl TryFrom<&tla_core::Spanned<tla_core::ast::Expr>> for TlaExpr {
    type Error = TlaError;

    fn try_from(expr: &tla_core::Spanned<tla_core::ast::Expr>) -> Result<Self, Self::Error> {
        Self::from_tla_core(expr)
    }
}

impl TryFrom<&tla_core::Spanned<tla_core::ast::Expr>> for TlaFormula {
    type Error = TlaError;

    fn try_from(expr: &tla_core::Spanned<tla_core::ast::Expr>) -> Result<Self, Self::Error> {
        Self::from_tla_core(expr)
    }
}

impl TryFrom<&tla_core::ast::OperatorDef> for TlaOperator {
    type Error = TlaError;

    fn try_from(op: &tla_core::ast::OperatorDef) -> Result<Self, Self::Error> {
        Self::from_tla_core(op)
    }
}

/// Context for TLA+ to clean translation
pub struct TlaContext {
    /// Free variable name to clean expression mapping
    pub vars: HashMap<String, Expr>,
    /// Operator definitions
    pub ops: HashMap<String, TlaOperator>,
    /// clean environment
    pub env: Environment,
    /// Stack of bound variable names (innermost = index 0)
    /// Used for de Bruijn index calculation in quantifiers
    bound_vars: Vec<String>,
}

impl TlaContext {
    /// Create a new TLA+ translation context
    pub fn new() -> Self {
        let mut env = Environment::new();
        // Initialize required theories
        env.init_set_theory()
            .expect("fresh TLA context should initialize set theory");
        env.init_fixed_point()
            .expect("fresh TLA context should initialize fixed-point theory");

        Self {
            vars: HashMap::new(),
            ops: HashMap::new(),
            env,
            bound_vars: Vec::new(),
        }
    }

    /// Clear obligation-local translation state while retaining the initialized
    /// kernel environment. A context may therefore be reused across a batch
    /// without INSTANCE substitutions or binder state leaking between items.
    pub fn reset_for_obligation(&mut self) {
        self.vars.clear();
        self.ops.clear();
        self.bound_vars.clear();
    }

    /// Bind a free variable to a clean expression
    pub fn bind_var(&mut self, name: &str, expr: Expr) {
        self.vars.insert(name.to_string(), expr);
    }

    /// Enter a binder scope with the given variable name
    /// Returns a guard that will pop the scope when dropped
    fn enter_binder(&mut self, name: &str) {
        self.bound_vars.push(name.to_string());
    }

    /// Exit a binder scope
    fn exit_binder(&mut self) {
        self.bound_vars.pop();
    }

    /// Enter a binder scope for a propositional variable
    /// Used by obligation translation to ensure Prop-typed variables
    /// become BVars during formula translation, not TLA.var.X constants.
    pub fn enter_prop_binder(&mut self, name: &str) {
        self.enter_binder(name);
    }

    /// Exit a propositional binder scope
    pub fn exit_prop_binder(&mut self) {
        self.exit_binder();
    }

    /// Look up a variable, checking bound variables first (de Bruijn)
    fn lookup_var(&self, name: &str) -> Option<Expr> {
        // First check if it's a bound variable (de Bruijn index)
        // bound_vars is ordered with innermost at end (most recent)
        for (i, bound_name) in self.bound_vars.iter().rev().enumerate() {
            if bound_name == name {
                return Some(Expr::bvar(i as u32));
            }
        }
        // Otherwise check free variables
        self.vars.get(name).cloned()
    }

    /// Define a TLA+ operator
    pub fn define_op(&mut self, op: TlaOperator) {
        self.ops.insert(op.name.clone(), op);
    }

    /// Translate TLA+ expression to clean expression
    pub fn translate_expr(&mut self, expr: &TlaExpr) -> Result<Expr, TlaError> {
        match expr {
            TlaExpr::Var(name) => {
                // TLAPS obligations may contain free variables/constants that are declared in the
                // surrounding module context. If a variable isn't bound (by a quantifier) and
                // isn't explicitly mapped in `vars`, treat it as a free constant rather than
                // failing translation.
                if let Some(expr) = self.lookup_var(name) {
                    Ok(expr)
                } else {
                    Ok(Expr::const_(
                        Name::from_string(&format!("TLA.var.{}", name)),
                        vec![],
                    ))
                }
            }

            TlaExpr::Const(name) => Ok(Expr::const_(Name::from_string(name), vec![])),

            TlaExpr::True => Ok(Expr::const_(Name::from_string("Bool.true"), vec![])),

            TlaExpr::False => Ok(Expr::const_(Name::from_string("Bool.false"), vec![])),

            TlaExpr::Int(n) => {
                // Represent integers using clean's Int type
                // Positive/zero: Int.ofNat n, Negative: Int.negOfNat |n|
                if *n >= 0 {
                    Ok(Expr::app(
                        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
                        Expr::nat_lit(*n as u64),
                    ))
                } else {
                    // For negative numbers, compute magnitude correctly (handles i64::MIN)
                    let magnitude = 0u64.wrapping_sub(*n as u64);
                    Ok(Expr::app(
                        Expr::const_(Name::from_string("Int.negOfNat"), vec![]),
                        Expr::nat_lit(magnitude),
                    ))
                }
            }

            TlaExpr::Mem(x, s) => {
                let x_lean = self.translate_expr(x)?;
                let s_lean = self.translate_expr(s)?;
                Ok(Expr::app(
                    Expr::app(Expr::const_(Name::from_string("TLA.mem"), vec![]), x_lean),
                    s_lean,
                ))
            }

            TlaExpr::Subset(s, t) => {
                let s_lean = self.translate_expr(s)?;
                let t_lean = self.translate_expr(t)?;
                Ok(Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("TLA.subset"), vec![]),
                        s_lean,
                    ),
                    t_lean,
                ))
            }

            TlaExpr::SetEq(s, t) => {
                let s_lean = self.translate_expr(s)?;
                let t_lean = self.translate_expr(t)?;
                Ok(Expr::app(
                    Expr::app(Expr::const_(Name::from_string("TLA.setEq"), vec![]), s_lean),
                    t_lean,
                ))
            }

            TlaExpr::Union(s, t) => {
                let s_lean = self.translate_expr(s)?;
                let t_lean = self.translate_expr(t)?;
                Ok(Expr::app(
                    Expr::app(Expr::const_(Name::from_string("TLA.union"), vec![]), s_lean),
                    t_lean,
                ))
            }

            TlaExpr::Inter(s, t) => {
                let s_lean = self.translate_expr(s)?;
                let t_lean = self.translate_expr(t)?;
                Ok(Expr::app(
                    Expr::app(Expr::const_(Name::from_string("TLA.inter"), vec![]), s_lean),
                    t_lean,
                ))
            }

            TlaExpr::Diff(s, t) => {
                let s_lean = self.translate_expr(s)?;
                let t_lean = self.translate_expr(t)?;
                Ok(Expr::app(
                    Expr::app(Expr::const_(Name::from_string("TLA.diff"), vec![]), s_lean),
                    t_lean,
                ))
            }

            TlaExpr::PowerSet(s) => {
                let s_lean = self.translate_expr(s)?;
                Ok(Expr::app(
                    Expr::const_(Name::from_string("TLA.powerSet"), vec![]),
                    s_lean,
                ))
            }

            TlaExpr::BigUnion(s) => {
                let s_lean = self.translate_expr(s)?;
                Ok(Expr::app(
                    Expr::const_(Name::from_string("TLA.bigUnion"), vec![]),
                    s_lean,
                ))
            }

            TlaExpr::Domain(f) => {
                let f_lean = self.translate_expr(f)?;
                Ok(Expr::app(
                    Expr::const_(Name::from_string("TLA.domain"), vec![]),
                    f_lean,
                ))
            }

            TlaExpr::Apply(f, x) => {
                let f_lean = self.translate_expr(f)?;
                let x_lean = self.translate_expr(x)?;
                Ok(Expr::app(
                    Expr::app(Expr::const_(Name::from_string("TLA.apply"), vec![]), f_lean),
                    x_lean,
                ))
            }

            TlaExpr::Nat => Ok(Expr::const_(Name::from_string("TLA.Nat"), vec![])),

            TlaExpr::Integer => Ok(Expr::const_(Name::from_string("TLA.Int"), vec![])),

            TlaExpr::Real => Ok(Expr::const_(Name::from_string("TLA.Real"), vec![])),

            TlaExpr::Boolean => Ok(Expr::const_(Name::from_string("TLA.Boolean"), vec![])),

            TlaExpr::String_ => Ok(Expr::const_(Name::from_string("TLA.String"), vec![])),

            TlaExpr::Arith(op, a, b) => {
                let a_lean = self.translate_expr(a)?;
                let b_lean = self.translate_expr(b)?;
                let op_name = match op {
                    TlaArithOp::Add => "TLA.add",
                    TlaArithOp::Sub => "TLA.sub",
                    TlaArithOp::Mul => "TLA.mul",
                    TlaArithOp::Div => "TLA.div",
                    TlaArithOp::Mod => "TLA.mod",
                    // TLA+ `^` (exponentiation) from the `Naturals` standard module.
                    TlaArithOp::Pow => "TLA.pow",
                };
                Ok(Expr::app(
                    Expr::app(Expr::const_(Name::from_string(op_name), vec![]), a_lean),
                    b_lean,
                ))
            }

            TlaExpr::Neg(x) => {
                // Unary arithmetic negation
                let x_lean = self.translate_expr(x)?;
                Ok(Expr::app(
                    Expr::const_(Name::from_string("TLA.neg"), vec![]),
                    x_lean,
                ))
            }

            TlaExpr::Prime(x) => {
                // e' → TLA.prime e
                //
                // A primed expression denotes the value of `e` in the successor
                // state. `TLA.prime` is a dedicated operator that is *never*
                // definitionally equal to the unprimed term, so the next-state
                // value cannot be confused with the current-state value.
                let x_lean = self.translate_expr(x)?;
                Ok(Expr::app(
                    Expr::const_(Name::from_string("TLA.prime"), vec![]),
                    x_lean,
                ))
            }

            TlaExpr::Cmp(op, a, b) => {
                let a_lean = self.translate_expr(a)?;
                let b_lean = self.translate_expr(b)?;
                let op_name = match op {
                    TlaCmpOp::Lt => "TLA.lt",
                    TlaCmpOp::Le => "TLA.le",
                    TlaCmpOp::Gt => "TLA.gt",
                    TlaCmpOp::Ge => "TLA.ge",
                };
                Ok(Expr::app(
                    Expr::app(Expr::const_(Name::from_string(op_name), vec![]), a_lean),
                    b_lean,
                ))
            }

            TlaExpr::Range(a, b) => {
                let a_lean = self.translate_expr(a)?;
                let b_lean = self.translate_expr(b)?;
                Ok(Expr::app(
                    Expr::app(Expr::const_(Name::from_string("TLA.range"), vec![]), a_lean),
                    b_lean,
                ))
            }

            TlaExpr::SetEnum(elems) => {
                // Build finite set from elements
                if elems.is_empty() {
                    return Ok(Expr::const_(Name::from_string("TLA.empty"), vec![]));
                }
                let mut result = self.translate_expr(&elems[0])?;
                result = Expr::app(
                    Expr::const_(Name::from_string("TLA.singleton"), vec![]),
                    result,
                );
                for elem in &elems[1..] {
                    let e = self.translate_expr(elem)?;
                    let single =
                        Expr::app(Expr::const_(Name::from_string("TLA.singleton"), vec![]), e);
                    result = Expr::app(
                        Expr::app(Expr::const_(Name::from_string("TLA.union"), vec![]), result),
                        single,
                    );
                }
                Ok(result)
            }

            TlaExpr::Tuple(elems) => {
                // Encode tuple as nested pairs
                if elems.is_empty() {
                    return Ok(Expr::const_(Name::from_string("TLA.unit"), vec![]));
                }
                if elems.len() == 1 {
                    return self.translate_expr(&elems[0]);
                }
                let first = self.translate_expr(&elems[0])?;
                let rest = self.translate_expr(&TlaExpr::Tuple(elems[1..].to_vec()))?;
                Ok(Expr::app(
                    Expr::app(Expr::const_(Name::from_string("TLA.pair"), vec![]), first),
                    rest,
                ))
            }

            TlaExpr::IfThenElse(cond, then_, else_) => {
                let cond_lean = self.translate_formula(cond)?;
                let then_lean = self.translate_expr(then_)?;
                let else_lean = self.translate_expr(else_)?;
                Ok(Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("TLA.ite"), vec![]),
                            cond_lean,
                        ),
                        then_lean,
                    ),
                    else_lean,
                ))
            }

            TlaExpr::OpApply(name, args) => {
                // Look up operator and apply
                if let Some(_op) = self.ops.get(name) {
                    // Inline operator body with substituted args
                    // For now, just use constant application
                    let mut result = Expr::const_(Name::from_string(name), vec![]);
                    for arg in args {
                        let arg_lean = self.translate_expr(arg)?;
                        result = Expr::app(result, arg_lean);
                    }
                    Ok(result)
                } else {
                    // Unknown operator - emit as constant
                    let mut result = Expr::const_(Name::from_string(name), vec![]);
                    for arg in args {
                        let arg_lean = self.translate_expr(arg)?;
                        result = Expr::app(result, arg_lean);
                    }
                    Ok(result)
                }
            }

            TlaExpr::Str(s) => {
                // String literals as Lean string
                Ok(Expr::str_lit(s.clone()))
            }

            TlaExpr::SetOf(set, x, pred) => {
                // {x ∈ S : P(x)} → TLA.sep S (λx. P(x))
                // Separation/comprehension: filter S by predicate P
                let s_lean = self.translate_expr(set)?;
                let tla_type = Expr::const_(Name::from_string("TLA.Value"), vec![]);

                // Enter binder scope so x maps to BVar(0) in the predicate
                self.enter_binder(x);
                let pred_lean = self.translate_formula(pred)?;
                self.exit_binder();

                Ok(Expr::app(
                    Expr::app(Expr::const_(Name::from_string("TLA.sep"), vec![]), s_lean),
                    Expr::lam(BinderInfo::Default, tla_type, pred_lean),
                ))
            }

            TlaExpr::SetMap(expr_template, x, set, pred) => {
                // {e : x ∈ S, P(x)} → TLA.setMap S (λx. e) (λx. P(x))
                // Map + optional filter: apply transformation e to elements satisfying P
                let s_lean = self.translate_expr(set)?;
                let tla_type = Expr::const_(Name::from_string("TLA.Value"), vec![]);

                // Enter binder scope for both the expression template and optional predicate
                self.enter_binder(x);
                let expr_lean = self.translate_expr(expr_template)?;
                let pred_lean = if let Some(p) = pred {
                    self.translate_formula(p)?
                } else {
                    // No predicate means True (include all elements)
                    Expr::const_(Name::from_string("True"), vec![])
                };
                self.exit_binder();

                Ok(Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("TLA.setMap"), vec![]),
                            s_lean,
                        ),
                        Expr::lam(BinderInfo::Default, tla_type.clone(), expr_lean),
                    ),
                    Expr::lam(BinderInfo::Default, tla_type, pred_lean),
                ))
            }

            TlaExpr::Func(x, domain, body) => {
                // [x ∈ S |-> e] → TLA.func S (λx. e)
                // Function constructor: map each x in domain to body expression
                let domain_lean = self.translate_expr(domain)?;
                let tla_type = Expr::const_(Name::from_string("TLA.Value"), vec![]);

                self.enter_binder(x);
                let body_lean = self.translate_expr(body)?;
                self.exit_binder();

                Ok(Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("TLA.func"), vec![]),
                        domain_lean,
                    ),
                    Expr::lam(BinderInfo::Default, tla_type, body_lean),
                ))
            }

            TlaExpr::Record(fields) => {
                // [a |-> v1, b |-> v2] → TLA.record [(a, v1), (b, v2)]
                // Build record as a list of (field_name, value) pairs
                if fields.is_empty() {
                    return Ok(Expr::const_(Name::from_string("TLA.emptyRecord"), vec![]));
                }

                // Start with the first field
                let (first_name, first_val) = &fields[0];
                let first_val_lean = self.translate_expr(first_val)?;
                let mut result = Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("TLA.singletonRecord"), vec![]),
                        Expr::str_lit(first_name.clone()),
                    ),
                    first_val_lean,
                );

                // Merge in remaining fields
                for (name, val) in &fields[1..] {
                    let val_lean = self.translate_expr(val)?;
                    let field_rec = Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("TLA.singletonRecord"), vec![]),
                            Expr::str_lit(name.clone()),
                        ),
                        val_lean,
                    );
                    result = Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("TLA.mergeRecords"), vec![]),
                            result,
                        ),
                        field_rec,
                    );
                }

                Ok(result)
            }

            TlaExpr::Field(record, field_name) => {
                // r.field → TLA.getField r "field"
                let record_lean = self.translate_expr(record)?;
                Ok(Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("TLA.getField"), vec![]),
                        record_lean,
                    ),
                    Expr::str_lit(field_name.clone()),
                ))
            }

            TlaExpr::Seq(elems) => {
                // <<a, b, c>> as sequence → TLA.seq [a, b, c]
                // Build sequence from elements
                if elems.is_empty() {
                    return Ok(Expr::const_(Name::from_string("TLA.emptySeq"), vec![]));
                }

                // Build sequence by cons-ing elements
                let mut result = Expr::const_(Name::from_string("TLA.emptySeq"), vec![]);
                for elem in elems.iter().rev() {
                    let elem_lean = self.translate_expr(elem)?;
                    result = Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("TLA.seqCons"), vec![]),
                            elem_lean,
                        ),
                        result,
                    );
                }
                Ok(result)
            }

            TlaExpr::Choose(x, set, pred) => {
                // CHOOSE x ∈ S : P(x) → TLA.choose S (λx. P(x))
                // Hilbert's epsilon: some element of S satisfying P
                let s_lean = self.translate_expr(set)?;
                let tla_type = Expr::const_(Name::from_string("TLA.Value"), vec![]);

                self.enter_binder(x);
                let pred_lean = self.translate_formula(pred)?;
                self.exit_binder();

                Ok(Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("TLA.choose"), vec![]),
                        s_lean,
                    ),
                    Expr::lam(BinderInfo::Default, tla_type, pred_lean),
                ))
            }

            TlaExpr::Case(arms, default) => {
                // CASE P1 -> e1 [] P2 -> e2 [] ... [] OTHER -> d
                // Encode as nested ITE: if P1 then e1 else if P2 then e2 else ... else d
                if arms.is_empty() {
                    // No cases - return default or unit
                    return if let Some(d) = default {
                        self.translate_expr(d)
                    } else {
                        Ok(Expr::const_(Name::from_string("TLA.unit"), vec![]))
                    };
                }

                // Build from back to front
                let else_branch = if let Some(d) = default {
                    self.translate_expr(d)?
                } else {
                    // No default: undefined/error value
                    Expr::const_(Name::from_string("TLA.undefined"), vec![])
                };

                let mut result = else_branch;
                for (cond, body) in arms.iter().rev() {
                    let cond_lean = self.translate_formula(cond)?;
                    let body_lean = self.translate_expr(body)?;
                    result = Expr::app(
                        Expr::app(
                            Expr::app(
                                Expr::const_(Name::from_string("TLA.ite"), vec![]),
                                cond_lean,
                            ),
                            body_lean,
                        ),
                        result,
                    );
                }
                Ok(result)
            }

            TlaExpr::Let(name, value, body) => {
                // LET x == e IN body → (λx. body)(e)
                // Let binding as application of lambda
                let value_lean = self.translate_expr(value)?;
                let tla_type = Expr::const_(Name::from_string("TLA.Value"), vec![]);

                self.enter_binder(name);
                let body_lean = self.translate_expr(body)?;
                self.exit_binder();

                // (λname. body) value
                Ok(Expr::app(
                    Expr::lam(BinderInfo::Default, tla_type, body_lean),
                    value_lean,
                ))
            }

            TlaExpr::FuncSet(domain, codomain) => {
                // [S -> T] → TLA.funcSet S T
                // The set of all total functions from S into T.
                let domain_lean = self.translate_expr(domain)?;
                let codomain_lean = self.translate_expr(codomain)?;
                Ok(Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("TLA.funcSet"), vec![]),
                        domain_lean,
                    ),
                    codomain_lean,
                ))
            }

            TlaExpr::Times(factors) => {
                // S \X T \X ... → TLA.times (TLA.times S T) ...
                // Cartesian product, folded left-associatively. A degenerate
                // product (zero or one factor) cannot occur in surface syntax,
                // but is handled defensively: a single factor is its own
                // product and an empty product is the unit set.
                let mut iter = factors.iter();
                let Some(first) = iter.next() else {
                    return Ok(Expr::const_(Name::from_string("TLA.unit"), vec![]));
                };
                let mut result = self.translate_expr(first)?;
                for factor in iter {
                    let factor_lean = self.translate_expr(factor)?;
                    result = Expr::app(
                        Expr::app(Expr::const_(Name::from_string("TLA.times"), vec![]), result),
                        factor_lean,
                    );
                }
                Ok(result)
            }

            TlaExpr::Except(base, specs) => {
                // [f EXCEPT !p1 = v1, !p2 = v2, ...] → fold TLA.except over f.
                // Each spec installs `value` at the position located by `path`;
                // later specs see the result of earlier ones (sequential
                // EXCEPT semantics), so we fold left starting from `f`.
                let mut result = self.translate_expr(base)?;
                for spec in specs {
                    let path_lean = self.translate_except_path(&spec.path)?;
                    let value_lean = self.translate_expr(&spec.value)?;
                    result = Expr::app(
                        Expr::app(
                            Expr::app(
                                Expr::const_(Name::from_string("TLA.except"), vec![]),
                                result,
                            ),
                            path_lean,
                        ),
                        value_lean,
                    );
                }
                Ok(result)
            }

            TlaExpr::RecordSet(fields) => {
                // [a: S, b: T] → the set of records r with r.a ∈ S and r.b ∈ T.
                // Mirrors the `Record` encoding: a single field folds through
                // `TLA.singletonRecordSet "a" S` and additional fields are
                // merged with `TLA.mergeRecordSets`. An empty record set is the
                // singleton set containing the empty record (`TLA.emptyRecordSet`).
                if fields.is_empty() {
                    return Ok(Expr::const_(
                        Name::from_string("TLA.emptyRecordSet"),
                        vec![],
                    ));
                }

                let (first_name, first_set) = &fields[0];
                let first_set_lean = self.translate_expr(first_set)?;
                let mut result = Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("TLA.singletonRecordSet"), vec![]),
                        Expr::str_lit(first_name.clone()),
                    ),
                    first_set_lean,
                );

                for (name, set) in &fields[1..] {
                    let set_lean = self.translate_expr(set)?;
                    let field_set = Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("TLA.singletonRecordSet"), vec![]),
                            Expr::str_lit(name.clone()),
                        ),
                        set_lean,
                    );
                    result = Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("TLA.mergeRecordSets"), vec![]),
                            result,
                        ),
                        field_set,
                    );
                }

                Ok(result)
            }

            TlaExpr::TemporalFormula(formula) => {
                // A temporal/propositional formula in value position. Delegate
                // to the formula translator, which recurses through nested
                // temporal operators (`[]<>P`, `<>[]P`, fairness with temporal
                // bodies, …). The result is a `Prop` term, which is a valid
                // clean expression.
                self.translate_formula(formula)
            } // All TlaExpr variants are now implemented.
              // If a new variant is added without implementation, this match will
              // become non-exhaustive and trigger a compile error.
        }
    }

    /// Reify an `EXCEPT` path as a `TLA.pathCons` list of selectors.
    ///
    /// `![e]` becomes `TLA.pathIndex e` and `!.name` becomes
    /// `TLA.pathField "name"`; the selectors are cons'd left-to-right onto the
    /// empty path `TLA.pathNil`, so the head of the list is the first selector
    /// applied. Deep paths (`![a][b]`, `!.x.y`) are preserved in order.
    fn translate_except_path(&mut self, path: &[TlaExceptPath]) -> Result<Expr, TlaError> {
        let mut result = Expr::const_(Name::from_string("TLA.pathNil"), vec![]);
        for step in path.iter().rev() {
            let selector = match step {
                TlaExceptPath::Index(key) => {
                    let key_lean = self.translate_expr(key)?;
                    Expr::app(
                        Expr::const_(Name::from_string("TLA.pathIndex"), vec![]),
                        key_lean,
                    )
                }
                TlaExceptPath::Field(name) => Expr::app(
                    Expr::const_(Name::from_string("TLA.pathField"), vec![]),
                    Expr::str_lit(name.clone()),
                ),
            };
            result = Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("TLA.pathCons"), vec![]),
                    selector,
                ),
                result,
            );
        }
        Ok(result)
    }

    /// Translate a canonical `tla-core` expression into a clean value term.
    ///
    /// This keeps the existing serde/wire layer intact while letting callers
    /// feed the shared AST directly.
    pub fn translate_tla_core_expr(
        &mut self,
        expr: &tla_core::Spanned<tla_core::ast::Expr>,
    ) -> Result<Expr, TlaError> {
        let compat = TlaExpr::from_tla_core(expr)?;
        self.translate_expr(&compat)
    }

    /// Translate TLA+ formula to clean expression (Prop)
    pub fn translate_formula(&mut self, formula: &TlaFormula) -> Result<Expr, TlaError> {
        match formula {
            TlaFormula::Expr(e) => self.translate_expr(e),

            TlaFormula::True => Ok(Expr::const_(Name::from_string("True"), vec![])),

            TlaFormula::False => Ok(Expr::const_(Name::from_string("False"), vec![])),

            TlaFormula::Not(p) => {
                let p_lean = self.translate_formula(p)?;
                Ok(Expr::app(
                    Expr::const_(Name::from_string("Not"), vec![]),
                    p_lean,
                ))
            }

            TlaFormula::And(p, q) => {
                let p_lean = self.translate_formula(p)?;
                let q_lean = self.translate_formula(q)?;
                Ok(Expr::app(
                    Expr::app(Expr::const_(Name::from_string("And"), vec![]), p_lean),
                    q_lean,
                ))
            }

            TlaFormula::Or(p, q) => {
                let p_lean = self.translate_formula(p)?;
                let q_lean = self.translate_formula(q)?;
                Ok(Expr::app(
                    Expr::app(Expr::const_(Name::from_string("Or"), vec![]), p_lean),
                    q_lean,
                ))
            }

            TlaFormula::Implies(p, q) => {
                let p_lean = self.translate_formula(p)?;
                let q_lean = self.translate_formula(q)?;
                // P → Q encoded as non-dependent Pi type (arrow) in Lean
                Ok(Expr::arrow(p_lean, q_lean))
            }

            TlaFormula::Iff(p, q) => {
                let p_lean = self.translate_formula(p)?;
                let q_lean = self.translate_formula(q)?;
                Ok(Expr::app(
                    Expr::app(Expr::const_(Name::from_string("Iff"), vec![]), p_lean),
                    q_lean,
                ))
            }

            TlaFormula::Forall(x, p) => {
                // Enter binder scope so x maps to BVar(0) in the body
                let tla_type = Expr::const_(Name::from_string("TLA.Value"), vec![]);
                self.enter_binder(x);
                let body = self.translate_formula(p)?;
                self.exit_binder();
                Ok(Expr::pi(BinderInfo::Default, tla_type, body))
            }

            TlaFormula::Exists(x, p) => {
                let tla_type = Expr::const_(Name::from_string("TLA.Value"), vec![]);
                self.enter_binder(x);
                let body = self.translate_formula(p)?;
                self.exit_binder();
                Ok(Expr::app(
                    Expr::const_(Name::from_string("Exists"), vec![]),
                    Expr::lam(BinderInfo::Default, tla_type, body),
                ))
            }

            TlaFormula::ForallIn(x, s, p) => {
                // Translate set first (before entering binder scope)
                let s_lean = self.translate_expr(s)?;
                let tla_type = Expr::const_(Name::from_string("TLA.Value"), vec![]);
                // Enter binder scope so x maps to BVar(0) in the body
                self.enter_binder(x);
                let body = self.translate_formula(p)?;
                self.exit_binder();
                Ok(Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("TLA.forallIn"), vec![]),
                        s_lean,
                    ),
                    Expr::lam(BinderInfo::Default, tla_type, body),
                ))
            }

            TlaFormula::ExistsIn(x, s, p) => {
                // Translate set first (before entering binder scope)
                let s_lean = self.translate_expr(s)?;
                let tla_type = Expr::const_(Name::from_string("TLA.Value"), vec![]);
                // Enter binder scope so x maps to BVar(0) in the body
                self.enter_binder(x);
                let body = self.translate_formula(p)?;
                self.exit_binder();
                Ok(Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("TLA.existsIn"), vec![]),
                        s_lean,
                    ),
                    Expr::lam(BinderInfo::Default, tla_type, body),
                ))
            }

            TlaFormula::Eq(a, b) => {
                let a_lean = self.translate_expr(a)?;
                let b_lean = self.translate_expr(b)?;
                Ok(Expr::app(
                    Expr::app(Expr::const_(Name::from_string("Eq"), vec![]), a_lean),
                    b_lean,
                ))
            }

            TlaFormula::Mem(x, s) => {
                let x_lean = self.translate_expr(x)?;
                let s_lean = self.translate_expr(s)?;
                Ok(Expr::app(
                    Expr::app(Expr::const_(Name::from_string("TLA.mem"), vec![]), x_lean),
                    s_lean,
                ))
            }

            TlaFormula::Subset(s, t) => {
                let s_lean = self.translate_expr(s)?;
                let t_lean = self.translate_expr(t)?;
                Ok(Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("TLA.subset"), vec![]),
                        s_lean,
                    ),
                    t_lean,
                ))
            }

            // Temporal operators - map to FixedPoint TLA axioms
            TlaFormula::Always(p) => {
                let p_lean = self.translate_formula(p)?;
                Ok(Expr::app(
                    Expr::const_(Name::from_string("FixedPoint.TLA_always"), vec![]),
                    p_lean,
                ))
            }

            TlaFormula::Eventually(p) => {
                let p_lean = self.translate_formula(p)?;
                Ok(Expr::app(
                    Expr::const_(Name::from_string("FixedPoint.TLA_eventually"), vec![]),
                    p_lean,
                ))
            }

            TlaFormula::LeadsTo(p, q) => {
                let p_lean = self.translate_formula(p)?;
                let q_lean = self.translate_formula(q)?;
                Ok(Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("FixedPoint.TLA_leads_to"), vec![]),
                        p_lean,
                    ),
                    q_lean,
                ))
            }

            TlaFormula::WeakFairness(vars, action) => {
                let vars_lean = self.translate_expr(vars)?;
                let action_lean = self.translate_formula(action)?;
                Ok(Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("FixedPoint.TLA_weak_fairness"), vec![]),
                        vars_lean,
                    ),
                    action_lean,
                ))
            }

            TlaFormula::StrongFairness(vars, action) => {
                let vars_lean = self.translate_expr(vars)?;
                let action_lean = self.translate_formula(action)?;
                Ok(Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("FixedPoint.TLA_strong_fairness"), vec![]),
                        vars_lean,
                    ),
                    action_lean,
                ))
            }

            TlaFormula::Unchanged(vars) => {
                // UNCHANGED e ≡ e' = e
                //
                // Expand to an equality between the primed (next-state) and
                // unprimed (current-state) values. This is the standard TLA+
                // definition and keeps the encoding self-contained: it reduces
                // to `Eq` and `TLA.prime`, both already encodable.
                let primed = self.translate_expr(&TlaExpr::Prime(vars.clone()))?;
                let current = self.translate_expr(vars)?;
                Ok(Expr::app(
                    Expr::app(Expr::const_(Name::from_string("Eq"), vec![]), primed),
                    current,
                ))
            }

            TlaFormula::Enabled(action) => {
                // ENABLED A → FixedPoint.TLA_enabled A
                //
                // ENABLED is a primitive action modality (∃ successor state in
                // which A holds); it is encoded as a dedicated operator rather
                // than expanded, since the existential over successor states is
                // not expressible at this layer.
                let action_lean = self.translate_formula(action)?;
                Ok(Expr::app(
                    Expr::const_(Name::from_string("FixedPoint.TLA_enabled"), vec![]),
                    action_lean,
                ))
            }
        }
    }

    /// Translate a canonical `tla-core` expression into a clean proposition.
    pub fn translate_tla_core_formula(
        &mut self,
        expr: &tla_core::Spanned<tla_core::ast::Expr>,
    ) -> Result<Expr, TlaError> {
        let compat = TlaFormula::from_tla_core(expr)?;
        self.translate_formula(&compat)
    }
}

impl Default for TlaContext {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::expr::ExprKind;

    /// Extract the outermost constant name from an App chain: App(App(Const(name, _), _), _) -> name
    fn outermost_const_name(expr: &Expr) -> Option<String> {
        match expr.kind() {
            ExprKind::Const(name, _) => Some(name.to_string()),
            ExprKind::App(f, _) => outermost_const_name(f),
            _ => None,
        }
    }

    #[test]
    fn test_translate_membership() {
        let mut ctx = TlaContext::new();
        let expr = TlaExpr::Mem(
            Box::new(TlaExpr::Const("x".to_string())),
            Box::new(TlaExpr::Const("S".to_string())),
        );
        let lean_expr = ctx
            .translate_expr(&expr)
            .expect("membership translation should succeed");
        // x ∈ S translates to an App (Membership applied to x and S)
        assert!(
            matches!(lean_expr.kind(), ExprKind::App(..)),
            "membership should translate to App, got {:?}",
            lean_expr.kind()
        );
    }

    #[test]
    fn test_translate_bounded_forall() {
        let mut ctx = TlaContext::new();
        // Test ∀x ∈ S : True (simpler formula that doesn't reference x in body)
        let formula = TlaFormula::ForallIn(
            "x".to_string(),
            Box::new(TlaExpr::Const("S".to_string())),
            Box::new(TlaFormula::True),
        );
        let lean_expr = ctx
            .translate_formula(&formula)
            .expect("bounded forall translation should succeed");
        // ∀x ∈ S : P translates to a Pi/forall expression
        assert!(
            matches!(lean_expr.kind(), ExprKind::Pi(..) | ExprKind::App(..)),
            "bounded forall should translate to Pi or App, got {:?}",
            lean_expr.kind()
        );

        // Test that x correctly resolves to BVar(0) inside the body
        let formula_with_ref = TlaFormula::ForallIn(
            "x".to_string(),
            Box::new(TlaExpr::Const("S".to_string())),
            Box::new(TlaFormula::Mem(
                Box::new(TlaExpr::Var("x".to_string())),
                Box::new(TlaExpr::Const("T".to_string())),
            )),
        );
        let result2 = ctx.translate_formula(&formula_with_ref);
        assert!(result2.is_ok(), "Should translate ∀x ∈ S : x ∈ T");
    }

    #[test]
    fn test_translate_set_operations() {
        let mut ctx = TlaContext::new();

        // S ∪ T
        let union = TlaExpr::Union(
            Box::new(TlaExpr::Const("S".to_string())),
            Box::new(TlaExpr::Const("T".to_string())),
        );
        let union_result = ctx.translate_expr(&union).expect("union should translate");
        assert_eq!(
            outermost_const_name(&union_result).as_deref(),
            Some("TLA.union")
        );

        // S ∩ T
        let inter = TlaExpr::Inter(
            Box::new(TlaExpr::Const("S".to_string())),
            Box::new(TlaExpr::Const("T".to_string())),
        );
        let inter_result = ctx.translate_expr(&inter).expect("inter should translate");
        assert_eq!(
            outermost_const_name(&inter_result).as_deref(),
            Some("TLA.inter")
        );

        // SUBSET S
        let power = TlaExpr::PowerSet(Box::new(TlaExpr::Const("S".to_string())));
        let power_result = ctx
            .translate_expr(&power)
            .expect("powerSet should translate");
        assert_eq!(
            outermost_const_name(&power_result).as_deref(),
            Some("TLA.powerSet")
        );
    }

    #[test]
    fn test_translate_temporal() {
        let mut ctx = TlaContext::new();

        // □P
        let always =
            TlaFormula::Always(Box::new(TlaFormula::Expr(TlaExpr::Const("P".to_string()))));
        let always_result = ctx
            .translate_formula(&always)
            .expect("always should translate");
        assert_eq!(
            outermost_const_name(&always_result).as_deref(),
            Some("FixedPoint.TLA_always")
        );

        // ◇P
        let eventually =
            TlaFormula::Eventually(Box::new(TlaFormula::Expr(TlaExpr::Const("P".to_string()))));
        let eventually_result = ctx
            .translate_formula(&eventually)
            .expect("eventually should translate");
        assert_eq!(
            outermost_const_name(&eventually_result).as_deref(),
            Some("FixedPoint.TLA_eventually")
        );

        // P ~> Q
        let leads_to = TlaFormula::LeadsTo(
            Box::new(TlaFormula::Expr(TlaExpr::Const("P".to_string()))),
            Box::new(TlaFormula::Expr(TlaExpr::Const("Q".to_string()))),
        );
        let leads_to_result = ctx
            .translate_formula(&leads_to)
            .expect("leads_to should translate");
        assert_eq!(
            outermost_const_name(&leads_to_result).as_deref(),
            Some("FixedPoint.TLA_leads_to")
        );
    }

    #[test]
    fn test_translate_always_eventually_infinitely_often() {
        // []<>P  (infinitely often). Outer is `[]`; the `<>` must survive inside.
        let mut ctx = TlaContext::new();
        let always_eventually = TlaFormula::Always(Box::new(TlaFormula::Eventually(Box::new(
            TlaFormula::Expr(TlaExpr::Const("P".to_string())),
        ))));
        let result = ctx
            .translate_formula(&always_eventually)
            .expect("[]<>P should translate");
        assert_eq!(
            outermost_const_name(&result).as_deref(),
            Some("FixedPoint.TLA_always"),
            "[]<>P outermost operator must be always"
        );
        assert!(
            contains_const(&result, "FixedPoint.TLA_eventually"),
            "[]<>P must retain the nested eventually operator"
        );
    }

    #[test]
    fn test_translate_eventually_always_stabilization() {
        // <>[]P  (eventually always / stabilization). Outer is `<>`; inner `[]`.
        let mut ctx = TlaContext::new();
        let eventually_always = TlaFormula::Eventually(Box::new(TlaFormula::Always(Box::new(
            TlaFormula::Expr(TlaExpr::Const("P".to_string())),
        ))));
        let result = ctx
            .translate_formula(&eventually_always)
            .expect("<>[]P should translate");
        assert_eq!(
            outermost_const_name(&result).as_deref(),
            Some("FixedPoint.TLA_eventually"),
            "<>[]P outermost operator must be eventually"
        );
        assert!(
            contains_const(&result, "FixedPoint.TLA_always"),
            "<>[]P must retain the nested always operator"
        );
    }

    #[test]
    fn test_translate_leads_to_with_temporal_arguments() {
        // (<>P) ~> ([]Q): leads-to whose both sides are themselves temporal.
        let mut ctx = TlaContext::new();
        let formula = TlaFormula::LeadsTo(
            Box::new(TlaFormula::Eventually(Box::new(TlaFormula::Expr(
                TlaExpr::Const("P".to_string()),
            )))),
            Box::new(TlaFormula::Always(Box::new(TlaFormula::Expr(
                TlaExpr::Const("Q".to_string()),
            )))),
        );
        let result = ctx
            .translate_formula(&formula)
            .expect("(<>P) ~> ([]Q) should translate");
        assert_eq!(
            outermost_const_name(&result).as_deref(),
            Some("FixedPoint.TLA_leads_to")
        );
        assert!(
            contains_const(&result, "FixedPoint.TLA_eventually")
                && contains_const(&result, "FixedPoint.TLA_always"),
            "leads-to must retain both temporal arguments"
        );
    }

    #[test]
    fn test_translate_weak_fairness_with_temporal_body() {
        // WF_vars([]<>P): fairness wrapping a nested temporal action body.
        let mut ctx = TlaContext::new();
        let formula = TlaFormula::WeakFairness(
            Box::new(TlaExpr::Var("vars".to_string())),
            Box::new(TlaFormula::Always(Box::new(TlaFormula::Eventually(
                Box::new(TlaFormula::Expr(TlaExpr::Const("P".to_string()))),
            )))),
        );
        let result = ctx
            .translate_formula(&formula)
            .expect("WF_vars([]<>P) should translate");
        assert_eq!(
            outermost_const_name(&result).as_deref(),
            Some("FixedPoint.TLA_weak_fairness")
        );
        assert!(
            contains_const(&result, "FixedPoint.TLA_always")
                && contains_const(&result, "FixedPoint.TLA_eventually"),
            "fairness must retain the nested temporal action body"
        );
    }

    #[test]
    fn test_translate_strong_fairness_with_eventually_body() {
        // SF_vars(<>P): strong fairness whose action body is temporal.
        let mut ctx = TlaContext::new();
        let formula = TlaFormula::StrongFairness(
            Box::new(TlaExpr::Var("vars".to_string())),
            Box::new(TlaFormula::Eventually(Box::new(TlaFormula::Expr(
                TlaExpr::Const("P".to_string()),
            )))),
        );
        let result = ctx
            .translate_formula(&formula)
            .expect("SF_vars(<>P) should translate");
        assert_eq!(
            outermost_const_name(&result).as_deref(),
            Some("FixedPoint.TLA_strong_fairness")
        );
        assert!(
            contains_const(&result, "FixedPoint.TLA_eventually"),
            "strong fairness must retain the temporal action body"
        );
    }

    #[test]
    fn test_translate_flat_always_sanity_still_works() {
        // Sanity: flat []P (no nesting) still encodes to the always operator.
        let mut ctx = TlaContext::new();
        let always =
            TlaFormula::Always(Box::new(TlaFormula::Expr(TlaExpr::Const("P".to_string()))));
        let result = ctx
            .translate_formula(&always)
            .expect("[]P should translate");
        assert_eq!(
            outermost_const_name(&result).as_deref(),
            Some("FixedPoint.TLA_always")
        );
        assert!(
            !contains_const(&result, "FixedPoint.TLA_eventually"),
            "flat []P must not introduce a spurious eventually operator"
        );
    }

    #[test]
    fn test_translate_temporal_formula_value_wrapper_delegates_to_formula() {
        // TlaExpr::TemporalFormula([]<>P) in value position must translate to the
        // same term as the bare formula []<>P.
        let mut ctx = TlaContext::new();
        let inner = TlaFormula::Always(Box::new(TlaFormula::Eventually(Box::new(
            TlaFormula::Expr(TlaExpr::Const("P".to_string())),
        ))));
        let as_expr = TlaExpr::TemporalFormula(Box::new(inner.clone()));
        let expr_result = ctx
            .translate_expr(&as_expr)
            .expect("temporal formula in value position should translate");
        let formula_result = ctx
            .translate_formula(&inner)
            .expect("[]<>P should translate");
        assert_eq!(
            expr_result, formula_result,
            "value-position temporal wrapper must match the formula encoding"
        );
    }

    #[test]
    fn test_translate_deeply_nested_temporal() {
        // [](<>([]P)) — three temporal layers; every layer must survive.
        let mut ctx = TlaContext::new();
        let formula = TlaFormula::Always(Box::new(TlaFormula::Eventually(Box::new(
            TlaFormula::Always(Box::new(TlaFormula::Expr(TlaExpr::Const("P".to_string())))),
        ))));
        let result = ctx
            .translate_formula(&formula)
            .expect("[](<>([]P)) should translate");
        assert_eq!(
            outermost_const_name(&result).as_deref(),
            Some("FixedPoint.TLA_always")
        );
        assert!(
            contains_const(&result, "FixedPoint.TLA_eventually")
                && contains_const(&result, "FixedPoint.TLA_always"),
            "deeply nested temporal must retain all layers"
        );
    }

    #[test]
    fn test_nested_quantifiers() {
        let mut ctx = TlaContext::new();

        // ∀x ∈ S : ∀y ∈ T : x ∈ y
        // Should have: x → BVar(1), y → BVar(0) in innermost body
        let nested = TlaFormula::ForallIn(
            "x".to_string(),
            Box::new(TlaExpr::Const("S".to_string())),
            Box::new(TlaFormula::ForallIn(
                "y".to_string(),
                Box::new(TlaExpr::Const("T".to_string())),
                Box::new(TlaFormula::Mem(
                    Box::new(TlaExpr::Var("x".to_string())),
                    Box::new(TlaExpr::Var("y".to_string())),
                )),
            )),
        );
        let result = ctx.translate_formula(&nested);
        assert!(
            result.is_ok(),
            "Should translate nested ∀x ∈ S : ∀y ∈ T : x ∈ y"
        );

        // ∃x ∈ S : ∃y ∈ T : x = y
        let nested_exists = TlaFormula::ExistsIn(
            "x".to_string(),
            Box::new(TlaExpr::Const("S".to_string())),
            Box::new(TlaFormula::ExistsIn(
                "y".to_string(),
                Box::new(TlaExpr::Const("T".to_string())),
                Box::new(TlaFormula::Expr(TlaExpr::SetEq(
                    Box::new(TlaExpr::Var("x".to_string())),
                    Box::new(TlaExpr::Var("y".to_string())),
                ))),
            )),
        );
        let result2 = ctx.translate_formula(&nested_exists);
        assert!(
            result2.is_ok(),
            "Should translate nested ∃x ∈ S : ∃y ∈ T : x = y"
        );

        // Mixed nesting: ∀x ∈ S : ∃y ∈ T : P(x, y)
        let mixed = TlaFormula::ForallIn(
            "x".to_string(),
            Box::new(TlaExpr::Const("S".to_string())),
            Box::new(TlaFormula::ExistsIn(
                "y".to_string(),
                Box::new(TlaExpr::Const("T".to_string())),
                Box::new(TlaFormula::And(
                    Box::new(TlaFormula::Mem(
                        Box::new(TlaExpr::Var("x".to_string())),
                        Box::new(TlaExpr::Const("A".to_string())),
                    )),
                    Box::new(TlaFormula::Mem(
                        Box::new(TlaExpr::Var("y".to_string())),
                        Box::new(TlaExpr::Const("B".to_string())),
                    )),
                )),
            )),
        );
        let result3 = ctx.translate_formula(&mixed);
        assert!(
            result3.is_ok(),
            "Should translate ∀x ∈ S : ∃y ∈ T : (x ∈ A ∧ y ∈ B)"
        );

        // Triple nesting: ∀x ∈ S : ∀y ∈ T : ∀z ∈ U : x ∈ y ∧ y ∈ z
        let triple = TlaFormula::ForallIn(
            "x".to_string(),
            Box::new(TlaExpr::Const("S".to_string())),
            Box::new(TlaFormula::ForallIn(
                "y".to_string(),
                Box::new(TlaExpr::Const("T".to_string())),
                Box::new(TlaFormula::ForallIn(
                    "z".to_string(),
                    Box::new(TlaExpr::Const("U".to_string())),
                    Box::new(TlaFormula::And(
                        Box::new(TlaFormula::Mem(
                            Box::new(TlaExpr::Var("x".to_string())),
                            Box::new(TlaExpr::Var("y".to_string())),
                        )),
                        Box::new(TlaFormula::Mem(
                            Box::new(TlaExpr::Var("y".to_string())),
                            Box::new(TlaExpr::Var("z".to_string())),
                        )),
                    )),
                )),
            )),
        );
        let result4 = ctx.translate_formula(&triple);
        assert!(
            result4.is_ok(),
            "Should translate ∀x ∈ S : ∀y ∈ T : ∀z ∈ U : x ∈ y ∧ y ∈ z"
        );
    }

    #[test]
    fn test_integer_encoding() {
        let mut ctx = TlaContext::new();

        // Positive integer: Int.ofNat 42
        let pos = TlaExpr::Int(42);
        let result = ctx
            .translate_expr(&pos)
            .expect("positive int should translate");
        assert_eq!(outermost_const_name(&result).as_deref(), Some("Int.ofNat"));

        // Zero: Int.ofNat 0
        let zero = TlaExpr::Int(0);
        let result_zero = ctx.translate_expr(&zero).expect("zero should translate");
        assert_eq!(
            outermost_const_name(&result_zero).as_deref(),
            Some("Int.ofNat")
        );

        // Negative integer: Int.negOfNat 5
        let neg = TlaExpr::Int(-5);
        let result_neg = ctx
            .translate_expr(&neg)
            .expect("negative int should translate");
        assert_eq!(
            outermost_const_name(&result_neg).as_deref(),
            Some("Int.negOfNat")
        );

        // Large negative: Int.negOfNat 1000000
        let large_neg = TlaExpr::Int(-1_000_000);
        let result_large = ctx
            .translate_expr(&large_neg)
            .expect("large negative should translate");
        assert_eq!(
            outermost_const_name(&result_large).as_deref(),
            Some("Int.negOfNat")
        );

        // i64::MIN edge case: Int.negOfNat 9223372036854775808
        let min = TlaExpr::Int(i64::MIN);
        let result_min = ctx.translate_expr(&min).expect("i64::MIN should translate");
        assert_eq!(
            outermost_const_name(&result_min).as_deref(),
            Some("Int.negOfNat"),
            "i64::MIN should use Int.negOfNat"
        );
    }

    #[test]
    fn test_unary_negation() {
        let mut ctx = TlaContext::new();

        // -x → TLA.neg(x)
        let neg_var = TlaExpr::Neg(Box::new(TlaExpr::Var("x".to_string())));
        ctx.bind_var("x", Expr::const_(Name::from_string("x"), vec![]));
        let result = ctx.translate_expr(&neg_var).expect("-x should translate");
        assert_eq!(outermost_const_name(&result).as_deref(), Some("TLA.neg"));

        // -5 using Neg constructor → TLA.neg(Int.ofNat 5)
        let neg_lit = TlaExpr::Neg(Box::new(TlaExpr::Int(5)));
        let result2 = ctx.translate_expr(&neg_lit).expect("-5 should translate");
        assert_eq!(outermost_const_name(&result2).as_deref(), Some("TLA.neg"));

        // Double negation: -(-x) → TLA.neg(TLA.neg(x))
        let double_neg = TlaExpr::Neg(Box::new(TlaExpr::Neg(Box::new(TlaExpr::Var(
            "x".to_string(),
        )))));
        let result3 = ctx
            .translate_expr(&double_neg)
            .expect("-(-x) should translate");
        assert_eq!(outermost_const_name(&result3).as_deref(), Some("TLA.neg"));
    }

    /// Recursively check whether `expr` contains a `Const` named `target`.
    fn contains_const(expr: &Expr, target: &str) -> bool {
        match expr.kind() {
            ExprKind::Const(name, _) => name.to_string() == target,
            ExprKind::App(f, a) => contains_const(f, target) || contains_const(a, target),
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                contains_const(ty, target) || contains_const(body, target)
            }
            _ => false,
        }
    }

    #[test]
    fn test_translate_prime_uses_distinct_operator() {
        let mut ctx = TlaContext::new();
        // x' → TLA.prime x
        let primed = TlaExpr::Prime(Box::new(TlaExpr::Var("x".to_string())));
        let result = ctx
            .translate_expr(&primed)
            .expect("primed variable should translate");
        assert_eq!(outermost_const_name(&result).as_deref(), Some("TLA.prime"));
    }

    #[test]
    fn test_translate_prime_action_x_eq_x_plus_one() {
        let mut ctx = TlaContext::new();
        // x' = x + 1  (a simple action formula)
        let action = TlaFormula::Eq(
            Box::new(TlaExpr::Prime(Box::new(TlaExpr::Var("x".to_string())))),
            Box::new(TlaExpr::Arith(
                TlaArithOp::Add,
                Box::new(TlaExpr::Var("x".to_string())),
                Box::new(TlaExpr::Int(1)),
            )),
        );
        let result = ctx
            .translate_formula(&action)
            .expect("action x' = x + 1 should translate");
        // Outermost is Eq; the LHS must carry the next-state TLA.prime operator.
        assert_eq!(outermost_const_name(&result).as_deref(), Some("Eq"));
        assert!(
            contains_const(&result, "TLA.prime"),
            "action should encode the primed LHS via TLA.prime"
        );
    }

    #[test]
    fn test_translate_prime_distinct_from_unprimed() {
        // SOUNDNESS: x' must NOT translate to the same term as x.
        let mut ctx = TlaContext::new();
        let primed = ctx
            .translate_expr(&TlaExpr::Prime(Box::new(TlaExpr::Var("x".to_string()))))
            .expect("x' should translate");
        let unprimed = ctx
            .translate_expr(&TlaExpr::Var("x".to_string()))
            .expect("x should translate");
        assert_ne!(
            primed, unprimed,
            "primed and unprimed occurrences must encode to distinct terms"
        );
    }

    #[test]
    fn test_translate_unchanged_expands_to_prime_eq() {
        let mut ctx = TlaContext::new();
        // UNCHANGED v ≡ v' = v
        let unchanged = TlaFormula::Unchanged(Box::new(TlaExpr::Var("v".to_string())));
        let result = ctx
            .translate_formula(&unchanged)
            .expect("UNCHANGED v should translate");
        // Encoded as Eq(prime v, v): outermost Eq, and a TLA.prime occurrence.
        assert_eq!(outermost_const_name(&result).as_deref(), Some("Eq"));
        assert!(
            contains_const(&result, "TLA.prime"),
            "UNCHANGED should expand to an equality involving the primed value"
        );
    }

    #[test]
    fn test_translate_enabled_uses_enabled_operator() {
        let mut ctx = TlaContext::new();
        // ENABLED (x' = x + 1)
        let action = TlaFormula::Eq(
            Box::new(TlaExpr::Prime(Box::new(TlaExpr::Var("x".to_string())))),
            Box::new(TlaExpr::Arith(
                TlaArithOp::Add,
                Box::new(TlaExpr::Var("x".to_string())),
                Box::new(TlaExpr::Int(1)),
            )),
        );
        let enabled = TlaFormula::Enabled(Box::new(action));
        let result = ctx
            .translate_formula(&enabled)
            .expect("ENABLED action should translate");
        assert_eq!(
            outermost_const_name(&result).as_deref(),
            Some("FixedPoint.TLA_enabled")
        );
    }

    #[test]
    fn test_translate_action_mixes_primed_and_unprimed() {
        let mut ctx = TlaContext::new();
        // y' = x  ∧  x' = y   (a swap action mixing primed and unprimed vars)
        let action = TlaFormula::And(
            Box::new(TlaFormula::Eq(
                Box::new(TlaExpr::Prime(Box::new(TlaExpr::Var("y".to_string())))),
                Box::new(TlaExpr::Var("x".to_string())),
            )),
            Box::new(TlaFormula::Eq(
                Box::new(TlaExpr::Prime(Box::new(TlaExpr::Var("x".to_string())))),
                Box::new(TlaExpr::Var("y".to_string())),
            )),
        );
        let result = ctx
            .translate_formula(&action)
            .expect("swap action should translate");
        assert_eq!(outermost_const_name(&result).as_deref(), Some("And"));
        assert!(
            contains_const(&result, "TLA.prime"),
            "swap action should encode primed variables via TLA.prime"
        );
    }

    #[test]
    fn test_arithmetic_operations() {
        let mut ctx = TlaContext::new();

        // x + y
        ctx.bind_var("x", Expr::const_(Name::from_string("x"), vec![]));
        ctx.bind_var("y", Expr::const_(Name::from_string("y"), vec![]));

        let ops: &[(TlaArithOp, &str)] = &[
            (TlaArithOp::Add, "TLA.add"),
            (TlaArithOp::Sub, "TLA.sub"),
            (TlaArithOp::Mul, "TLA.mul"),
            (TlaArithOp::Div, "TLA.div"),
            (TlaArithOp::Mod, "TLA.mod"),
            (TlaArithOp::Pow, "TLA.pow"),
        ];

        for (op, expected_name) in ops {
            let expr = TlaExpr::Arith(
                *op,
                Box::new(TlaExpr::Var("x".to_string())),
                Box::new(TlaExpr::Var("y".to_string())),
            );
            let result = ctx
                .translate_expr(&expr)
                .unwrap_or_else(|e| panic!("{expected_name} should translate: {e:?}"));
            assert_eq!(
                outermost_const_name(&result).as_deref(),
                Some(*expected_name),
                "arithmetic op should produce {expected_name}"
            );
        }
    }

    #[test]
    fn test_unbound_var_falls_back_to_free_const() {
        let mut ctx = TlaContext::new();
        let expr = TlaExpr::Var("x".to_string());
        let result = ctx
            .translate_expr(&expr)
            .expect("unbound var should translate");
        match result.kind() {
            ExprKind::Const(name, _) => {
                assert_eq!(name.to_string(), "TLA.var.x");
            }
            other => panic!("expected Const for unbound var, got: {other:?}"),
        }
    }

    // ================================================================
    // Tests for newly implemented TlaExpr encodings
    // ================================================================

    #[test]
    fn test_translate_string_literal() {
        let mut ctx = TlaContext::new();
        let expr = TlaExpr::Str("hello world".to_string());
        let result = ctx.translate_expr(&expr);
        assert!(result.is_ok(), "String literal should translate");
    }

    #[test]
    fn test_translate_set_comprehension() {
        let mut ctx = TlaContext::new();

        // {x ∈ S : x > 0}
        let set_of = TlaExpr::SetOf(
            Box::new(TlaExpr::Const("S".to_string())),
            "x".to_string(),
            Box::new(TlaFormula::Expr(TlaExpr::Cmp(
                TlaCmpOp::Gt,
                Box::new(TlaExpr::Var("x".to_string())),
                Box::new(TlaExpr::Int(0)),
            ))),
        );
        let result = ctx.translate_expr(&set_of);
        assert!(
            result.is_ok(),
            "Set comprehension should translate: {result:?}"
        );

        // Verify x is bound in the predicate (BVar(0))
        let expr = result.unwrap();
        // The expression should be: TLA.sep S (λx. TLA.gt x 0)
        if let ExprKind::App(_, inner) = expr.kind() {
            if let ExprKind::Lam(_, _, body) = inner.kind() {
                assert!(body.has_loose_bvars(), "Body should have bound var");
            }
        }
    }

    #[test]
    fn test_translate_set_map() {
        let mut ctx = TlaContext::new();

        // {x + 1 : x ∈ S}
        let set_map = TlaExpr::SetMap(
            Box::new(TlaExpr::Arith(
                TlaArithOp::Add,
                Box::new(TlaExpr::Var("x".to_string())),
                Box::new(TlaExpr::Int(1)),
            )),
            "x".to_string(),
            Box::new(TlaExpr::Const("S".to_string())),
            None, // No filter predicate
        );
        let result = ctx.translate_expr(&set_map);
        assert!(result.is_ok(), "Set map should translate: {result:?}");
    }

    #[test]
    fn test_translate_set_map_with_predicate() {
        let mut ctx = TlaContext::new();

        // {x * 2 : x ∈ S, x > 0}
        let set_map = TlaExpr::SetMap(
            Box::new(TlaExpr::Arith(
                TlaArithOp::Mul,
                Box::new(TlaExpr::Var("x".to_string())),
                Box::new(TlaExpr::Int(2)),
            )),
            "x".to_string(),
            Box::new(TlaExpr::Const("S".to_string())),
            Some(Box::new(TlaFormula::Expr(TlaExpr::Cmp(
                TlaCmpOp::Gt,
                Box::new(TlaExpr::Var("x".to_string())),
                Box::new(TlaExpr::Int(0)),
            )))),
        );
        let result = ctx.translate_expr(&set_map);
        assert!(result.is_ok(), "Set map with predicate should translate");
    }

    #[test]
    fn test_translate_function_constructor() {
        let mut ctx = TlaContext::new();

        // [x ∈ Nat |-> x + 1]
        let func = TlaExpr::Func(
            "x".to_string(),
            Box::new(TlaExpr::Nat),
            Box::new(TlaExpr::Arith(
                TlaArithOp::Add,
                Box::new(TlaExpr::Var("x".to_string())),
                Box::new(TlaExpr::Int(1)),
            )),
        );
        let result = ctx.translate_expr(&func);
        assert!(result.is_ok(), "Function constructor should translate");
    }

    #[test]
    fn test_translate_record() {
        let mut ctx = TlaContext::new();

        // [a |-> 1, b |-> 2]
        let record = TlaExpr::Record(vec![
            ("a".to_string(), TlaExpr::Int(1)),
            ("b".to_string(), TlaExpr::Int(2)),
        ]);
        let result = ctx.translate_expr(&record);
        assert!(result.is_ok(), "Record should translate");
    }

    #[test]
    fn test_translate_empty_record() {
        let mut ctx = TlaContext::new();

        let empty_record = TlaExpr::Record(vec![]);
        let result = ctx.translate_expr(&empty_record);
        assert!(result.is_ok(), "Empty record should translate");
        if let Ok(ref expr) = result {
            if let ExprKind::Const(name, _) = expr.kind() {
                assert_eq!(name.to_string(), "TLA.emptyRecord");
            }
        }
    }

    #[test]
    fn test_translate_field_access() {
        let mut ctx = TlaContext::new();

        // r.field
        let field = TlaExpr::Field(Box::new(TlaExpr::Var("r".to_string())), "field".to_string());
        let result = ctx.translate_expr(&field);
        assert!(result.is_ok(), "Field access should translate");
    }

    #[test]
    fn test_translate_record_set_folds_over_record_set_ops() {
        let mut ctx = TlaContext::new();

        // [a: S, b: T] → merge of singleton record sets.
        let record_set = TlaExpr::RecordSet(vec![
            ("a".to_string(), TlaExpr::Const("S".to_string())),
            ("b".to_string(), TlaExpr::Const("T".to_string())),
        ]);
        let result = ctx
            .translate_expr(&record_set)
            .expect("record set should translate");
        // Two fields => the outermost operator is the merge, and singleton
        // record sets appear underneath.
        assert_eq!(
            outermost_const_name(&result).as_deref(),
            Some("TLA.mergeRecordSets"),
            "multi-field record set should fold over TLA.mergeRecordSets"
        );
        assert!(
            contains_const(&result, "TLA.singletonRecordSet"),
            "record set should be built from singleton record sets"
        );
    }

    #[test]
    fn test_translate_single_field_record_set_is_singleton() {
        let mut ctx = TlaContext::new();

        // [a: S] → TLA.singletonRecordSet "a" S (no merge needed).
        let record_set =
            TlaExpr::RecordSet(vec![("a".to_string(), TlaExpr::Const("S".to_string()))]);
        let result = ctx
            .translate_expr(&record_set)
            .expect("single-field record set should translate");
        assert_eq!(
            outermost_const_name(&result).as_deref(),
            Some("TLA.singletonRecordSet"),
            "single-field record set should be a bare singleton record set"
        );
        assert!(
            !contains_const(&result, "TLA.mergeRecordSets"),
            "single-field record set should not introduce a merge"
        );
    }

    #[test]
    fn test_translate_empty_record_set_is_constant() {
        let mut ctx = TlaContext::new();

        let empty = TlaExpr::RecordSet(vec![]);
        let result = ctx
            .translate_expr(&empty)
            .expect("empty record set should translate");
        if let ExprKind::Const(name, _) = result.kind() {
            assert_eq!(name.to_string(), "TLA.emptyRecordSet");
        } else {
            panic!("empty record set should translate to a bare constant");
        }
    }

    #[test]
    fn test_translate_sequence() {
        let mut ctx = TlaContext::new();

        // <<1, 2, 3>>
        let seq = TlaExpr::Seq(vec![TlaExpr::Int(1), TlaExpr::Int(2), TlaExpr::Int(3)]);
        let result = ctx.translate_expr(&seq);
        assert!(result.is_ok(), "Sequence should translate");
    }

    #[test]
    fn test_translate_empty_sequence() {
        let mut ctx = TlaContext::new();

        let empty_seq = TlaExpr::Seq(vec![]);
        let result = ctx.translate_expr(&empty_seq);
        assert!(result.is_ok(), "Empty sequence should translate");
        if let Ok(ref expr) = result {
            if let ExprKind::Const(name, _) = expr.kind() {
                assert_eq!(name.to_string(), "TLA.emptySeq");
            }
        }
    }

    #[test]
    fn test_translate_choose() {
        let mut ctx = TlaContext::new();

        // CHOOSE x ∈ S : x > 0
        let choose = TlaExpr::Choose(
            "x".to_string(),
            Box::new(TlaExpr::Const("S".to_string())),
            Box::new(TlaFormula::Expr(TlaExpr::Cmp(
                TlaCmpOp::Gt,
                Box::new(TlaExpr::Var("x".to_string())),
                Box::new(TlaExpr::Int(0)),
            ))),
        );
        let result = ctx.translate_expr(&choose);
        assert!(result.is_ok(), "CHOOSE should translate");

        // Verify x is bound in the predicate
        let expr = result.unwrap();
        if let ExprKind::App(_, inner) = expr.kind() {
            if let ExprKind::Lam(_, _, body) = inner.kind() {
                assert!(body.has_loose_bvars(), "Body should have bound var");
            }
        }
    }

    #[test]
    fn test_translate_case_expression() {
        let mut ctx = TlaContext::new();

        // CASE x > 0 -> 1 [] x < 0 -> -1 [] OTHER -> 0
        let case_expr = TlaExpr::Case(
            vec![
                (
                    TlaFormula::Expr(TlaExpr::Cmp(
                        TlaCmpOp::Gt,
                        Box::new(TlaExpr::Var("x".to_string())),
                        Box::new(TlaExpr::Int(0)),
                    )),
                    TlaExpr::Int(1),
                ),
                (
                    TlaFormula::Expr(TlaExpr::Cmp(
                        TlaCmpOp::Lt,
                        Box::new(TlaExpr::Var("x".to_string())),
                        Box::new(TlaExpr::Int(0)),
                    )),
                    TlaExpr::Int(-1),
                ),
            ],
            Some(Box::new(TlaExpr::Int(0))),
        );
        let result = ctx.translate_expr(&case_expr);
        assert!(result.is_ok(), "CASE expression should translate");
    }

    #[test]
    fn test_translate_case_no_default() {
        let mut ctx = TlaContext::new();

        // CASE x > 0 -> 1
        let case_expr = TlaExpr::Case(
            vec![(
                TlaFormula::Expr(TlaExpr::Cmp(
                    TlaCmpOp::Gt,
                    Box::new(TlaExpr::Var("x".to_string())),
                    Box::new(TlaExpr::Int(0)),
                )),
                TlaExpr::Int(1),
            )],
            None, // No default
        );
        let result = ctx.translate_expr(&case_expr);
        assert!(result.is_ok(), "CASE without default should translate");
    }

    #[test]
    fn test_translate_let_binding() {
        let mut ctx = TlaContext::new();

        // LET y == 5 IN y + 1
        let let_expr = TlaExpr::Let(
            "y".to_string(),
            Box::new(TlaExpr::Int(5)),
            Box::new(TlaExpr::Arith(
                TlaArithOp::Add,
                Box::new(TlaExpr::Var("y".to_string())),
                Box::new(TlaExpr::Int(1)),
            )),
        );
        let result = ctx.translate_expr(&let_expr);
        assert!(result.is_ok(), "LET binding should translate: {result:?}");

        // The result should be ((λy. y + 1) 5)
        let expr = result.unwrap();
        if let ExprKind::App(lam, _val) = expr.kind() {
            if let ExprKind::Lam(_, _, body) = lam.kind() {
                assert!(
                    body.has_loose_bvars(),
                    "Body should reference y via BVar(0)"
                );
            }
        }
    }

    #[test]
    fn test_translate_nested_let() {
        let mut ctx = TlaContext::new();

        // LET x == 1 IN LET y == x + 1 IN y + x
        let nested_let = TlaExpr::Let(
            "x".to_string(),
            Box::new(TlaExpr::Int(1)),
            Box::new(TlaExpr::Let(
                "y".to_string(),
                Box::new(TlaExpr::Arith(
                    TlaArithOp::Add,
                    Box::new(TlaExpr::Var("x".to_string())),
                    Box::new(TlaExpr::Int(1)),
                )),
                Box::new(TlaExpr::Arith(
                    TlaArithOp::Add,
                    Box::new(TlaExpr::Var("y".to_string())),
                    Box::new(TlaExpr::Var("x".to_string())),
                )),
            )),
        );
        let result = ctx.translate_expr(&nested_let);
        assert!(result.is_ok(), "Nested LET should translate");
    }

    #[test]
    fn test_translate_tla_core_expr_add() {
        let mut ctx = TlaContext::new();
        let expr = tla_core::Spanned::dummy(tla_core::ast::Expr::Add(
            Box::new(tla_core::Spanned::dummy(tla_core::ast::Expr::Int(1.into()))),
            Box::new(tla_core::Spanned::dummy(tla_core::ast::Expr::Int(2.into()))),
        ));
        let lean_expr = ctx
            .translate_tla_core_expr(&expr)
            .expect("tla-core arithmetic should translate");
        assert_eq!(
            outermost_const_name(&lean_expr),
            Some("TLA.add".to_string())
        );
    }

    #[test]
    fn test_translate_tla_core_expr_pow() {
        // End-to-end: `x ^ 2` (core AST) → `TLA.pow (TLA.var.x) 2` (Lean).
        let mut ctx = TlaContext::new();
        let expr = tla_core::Spanned::dummy(tla_core::ast::Expr::Pow(
            Box::new(tla_core::Spanned::dummy(tla_core::ast::Expr::Ident(
                "x".to_string(),
                tla_core::intern_name("x"),
            ))),
            Box::new(tla_core::Spanned::dummy(tla_core::ast::Expr::Int(2.into()))),
        ));
        let lean_expr = ctx
            .translate_tla_core_expr(&expr)
            .expect("tla-core exponentiation should translate");
        // Outermost head is the TLA+ `^` operator constant.
        assert_eq!(
            outermost_const_name(&lean_expr),
            Some("TLA.pow".to_string())
        );
        // The full applied shape is `((TLA.pow base) exp)`: confirm the exponent
        // argument is the encoded integer literal `2` (`Int.ofNat 2`), so the
        // base and exponent operands were not dropped or swapped.
        match lean_expr.kind() {
            ExprKind::App(base_app, exp_arg) => {
                assert_eq!(
                    outermost_const_name(base_app),
                    Some("TLA.pow".to_string()),
                    "function position should be `TLA.pow` applied to the base"
                );
                assert_eq!(
                    outermost_const_name(exp_arg),
                    Some("Int.ofNat".to_string()),
                    "exponent should be the encoded integer literal `2`"
                );
            }
            other => panic!("expected applied TLA.pow, got {other:?}"),
        }
    }

    #[test]
    fn test_translate_tla_core_formula_forall_in() {
        let mut ctx = TlaContext::new();
        let bound = tla_core::ast::BoundVar {
            domain_group: None,
            name: tla_core::Spanned::dummy("x".to_string()),
            domain: Some(Box::new(tla_core::Spanned::dummy(
                tla_core::ast::Expr::Ident("S".to_string(), tla_core::intern_name("S")),
            ))),
            pattern: None,
        };
        let formula = tla_core::Spanned::dummy(tla_core::ast::Expr::Forall(
            vec![bound],
            Box::new(tla_core::Spanned::dummy(tla_core::ast::Expr::Eq(
                Box::new(tla_core::Spanned::dummy(tla_core::ast::Expr::Ident(
                    "x".to_string(),
                    tla_core::intern_name("x"),
                ))),
                Box::new(tla_core::Spanned::dummy(tla_core::ast::Expr::Ident(
                    "x".to_string(),
                    tla_core::intern_name("x"),
                ))),
            ))),
        ));
        let lean_expr = ctx
            .translate_tla_core_formula(&formula)
            .expect("tla-core bounded quantifier should translate");
        assert_eq!(
            outermost_const_name(&lean_expr),
            Some("TLA.forallIn".to_string())
        );
    }
}

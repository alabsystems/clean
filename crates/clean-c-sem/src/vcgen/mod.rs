// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Verification Condition Generator for C Programs
//!
//! This module generates verification conditions (VCs) from C programs with ACSL
//! specifications. The VCs are clean propositions that, if proven, establish that
//! the C code satisfies its specification.
//!
//! ## Approach: Weakest Precondition (WP) Calculus
//!
//! We use the weakest precondition approach from Dijkstra, as implemented in
//! Frama-C/WP and similar tools:
//!
//! - `wp(skip, Q) = Q`
//! - `wp(x = e, Q) = Q[e/x]`
//! - `wp(s1; s2, Q) = wp(s1, wp(s2, Q))`
//! - `wp(if b then s1 else s2, Q) = (b → wp(s1, Q)) ∧ (¬b → wp(s2, Q))`
//! - `wp(while b inv I { s }, Q) = I ∧ ∀state. (I ∧ b → wp(s, I)) ∧ (I ∧ ¬b → Q)`
//!
//! ## Example
//!
//! ```text
//! /*@ requires n >= 0;
//!     ensures \result >= 0;
//! */
//! int abs(int n) {
//!     if (n < 0)
//!         return -n;
//!     else
//!         return n;
//! }
//! ```
//!
//! Generates VCs:
//! 1. `n >= 0 ∧ n < 0 → -n >= 0` (negative branch)
//! 2. `n >= 0 ∧ n >= 0 → n >= 0` (positive branch)

mod assigns;
mod collect;
mod inference;
mod subst;

#[cfg(test)]
mod tests;

use crate::expr::{BinOp, CExpr, Designator, Initializer, SizeOfArg, UnaryOp};
use crate::spec::{FuncSpec, Location, LoopSpec, Spec};
use crate::stmt::{CStmt, CaseLabel, FuncDef, StorageClass, VarDecl};
use crate::types::{CType, Signedness};
use std::collections::{HashMap, HashSet};

// Re-export from submodules
#[cfg(test)]
pub(crate) use inference::AccumulatorOp;
pub use inference::{GhostKind, GhostVariable, InferenceContext, InvariantInference};

/// A verification condition to be proven
#[derive(Debug, Clone)]
pub struct VC {
    /// Human-readable description of this VC
    pub description: String,
    /// The proposition to prove (as a Spec)
    pub obligation: Spec,
    /// Source location (line number, if known)
    pub location: Option<usize>,
    /// Kind of VC (precondition, postcondition, loop invariant, etc.)
    pub kind: VCKind,
}

/// Classification of verification conditions
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VCKind {
    /// Function precondition must hold at call site
    Precondition,
    /// Function postcondition must hold on return
    Postcondition,
    /// Loop invariant must hold on entry
    LoopInvariantEntry,
    /// Loop invariant must be preserved by loop body
    LoopInvariantPreserved,
    /// Loop variant must decrease
    LoopVariantDecreases,
    /// Loop variant must be non-negative
    LoopVariantNonNegative,
    /// Assertion in code
    Assertion,
    /// Memory safety (valid pointer)
    MemorySafety,
    /// No undefined behavior
    NoUB,
    /// Assigns clause respected
    AssignsClause,
    /// An unsupported construct was encountered. The verifier cannot reason
    /// about it soundly, so it emits this obligation which is reported as
    /// `Unknown` (never established), making `proved < total` and forcing the
    /// function to be reported as NOT verified (fail-closed).
    /// SOUNDNESS: see docs/SOUNDNESS_FINDINGS_CLEAN_C_SEM_2026-07.md holes 2,4.
    Unsupported,
}

/// A modified location with metadata for error reporting
#[derive(Debug, Clone)]
pub struct ModifiedLocation {
    /// The location being modified
    pub location: Location,
    /// Human-readable description of the modification
    pub description: String,
    /// Source line number (if known)
    pub source_line: Option<usize>,
}

/// Base name for the rigid logic variable that snapshots a loop variant's value
/// at the loop head. Deliberately NOT a valid C identifier, so no program
/// variable can collide with it (and thereby be captured by) the substitution
/// pass that computes the variant's post-body value.
pub(crate) const SNAPSHOT_BASE: &str = "\\loop_variant_at_head";

/// Verification condition generator
pub struct VCGen {
    /// Generated VCs
    pub(crate) vcs: Vec<VC>,
    /// Current path condition (assumptions along current path)
    pub(crate) path_condition: Vec<Spec>,
    /// Known function specifications
    pub(crate) func_specs: HashMap<String, FuncSpec>,
    /// Counter for generating fresh variable names
    pub(crate) fresh_counter: usize,
    /// Unambiguous parameter/local types in the function currently being
    /// verified. Compound assignment needs the declared lvalue type: C applies
    /// the usual conversions to the operands and then converts the result back
    /// to this type before the store.
    variable_types: HashMap<String, CType>,
    /// Names declared more than once anywhere in the function. This WP is not
    /// scope-indexed, so using one textual name for two C objects must fail
    /// closed in the compound-assignment lane rather than choosing a type from
    /// the wrong scope.
    ambiguous_variables: HashSet<String>,
    /// Scalar objects whose address is taken in the current function. A write
    /// through an alias is outside the substitution model used by this WP.
    address_taken: HashSet<String>,
    /// Return type of the function currently being verified. Kept so the
    /// return expression's assignment conversion is represented before
    /// substituting `\result`.
    function_return_type: Option<CType>,
}

impl Default for VCGen {
    fn default() -> Self {
        Self::new()
    }
}

impl VCGen {
    pub fn new() -> Self {
        Self {
            vcs: Vec::new(),
            path_condition: Vec::new(),
            func_specs: HashMap::new(),
            fresh_counter: 0,
            variable_types: HashMap::new(),
            ambiguous_variables: HashSet::new(),
            address_taken: HashSet::new(),
            function_return_type: None,
        }
    }

    /// Register a function's specification
    pub fn register_func_spec(&mut self, name: &str, spec: FuncSpec) {
        self.func_specs.insert(name.to_string(), spec);
    }

    /// Build the deliberately narrow object model used by compound-assignment
    /// WP. The general C memory model is not represented by syntactic
    /// substitution, so only an unambiguous, non-aliased scalar object can be
    /// updated this way.
    fn prepare_function_objects(&mut self, func: &FuncDef) {
        self.variable_types.clear();
        self.ambiguous_variables.clear();
        self.address_taken.clear();
        self.function_return_type = Some(func.return_type.clone());

        let mut declarations: Vec<(String, CType)> = func
            .params
            .iter()
            .map(|param| (param.name.clone(), param.ty.clone()))
            .collect();
        Self::collect_declared_types(&func.body, &mut declarations);
        for (name, ty) in declarations {
            if self.variable_types.contains_key(&name) {
                self.variable_types.remove(&name);
                self.ambiguous_variables.insert(name);
            } else if !self.ambiguous_variables.contains(&name) {
                self.variable_types.insert(name, ty);
            }
        }
        Self::collect_address_taken_stmt(&func.body, &mut self.address_taken);
    }

    fn collect_declared_types(stmt: &CStmt, out: &mut Vec<(String, CType)>) {
        match stmt {
            CStmt::Decl(decl) => out.push((decl.name.clone(), decl.ty.clone())),
            CStmt::DeclList(decls) => out.extend(
                decls
                    .iter()
                    .map(|decl| (decl.name.clone(), decl.ty.clone())),
            ),
            CStmt::Block(stmts) => {
                for stmt in stmts {
                    Self::collect_declared_types(stmt, out);
                }
            }
            CStmt::If {
                then_stmt,
                else_stmt,
                ..
            } => {
                Self::collect_declared_types(then_stmt, out);
                if let Some(stmt) = else_stmt {
                    Self::collect_declared_types(stmt, out);
                }
            }
            CStmt::Switch { body, .. }
            | CStmt::While { body, .. }
            | CStmt::DoWhile { body, .. }
            | CStmt::Case { stmt: body, .. }
            | CStmt::Label { stmt: body, .. } => Self::collect_declared_types(body, out),
            CStmt::For { init, body, .. } => {
                if let Some(init) = init {
                    Self::collect_declared_types(init, out);
                }
                Self::collect_declared_types(body, out);
            }
            // A nested function owns a different object namespace. Its control
            // flow is unsupported elsewhere and must not make an outer scalar
            // appear typed or aliased.
            CStmt::FuncDef(_)
            | CStmt::Empty
            | CStmt::Expr(_)
            | CStmt::Break
            | CStmt::Continue
            | CStmt::Return(_)
            | CStmt::Goto(_)
            | CStmt::Asm(_)
            | CStmt::Assert(_)
            | CStmt::Assume(_)
            | CStmt::StaticAssert { .. } => {}
        }
    }

    fn collect_address_taken_stmt(stmt: &CStmt, out: &mut HashSet<String>) {
        match stmt {
            CStmt::Expr(expr) | CStmt::Return(Some(expr)) => {
                Self::collect_address_taken_expr(expr, out);
            }
            CStmt::Decl(decl) => {
                if let Some(init) = &decl.init {
                    Self::collect_address_taken_initializer(init, out);
                }
            }
            CStmt::DeclList(decls) => {
                for decl in decls {
                    if let Some(init) = &decl.init {
                        Self::collect_address_taken_initializer(init, out);
                    }
                }
            }
            CStmt::Block(stmts) => {
                for stmt in stmts {
                    Self::collect_address_taken_stmt(stmt, out);
                }
            }
            CStmt::If {
                cond,
                then_stmt,
                else_stmt,
            } => {
                Self::collect_address_taken_expr(cond, out);
                Self::collect_address_taken_stmt(then_stmt, out);
                if let Some(stmt) = else_stmt {
                    Self::collect_address_taken_stmt(stmt, out);
                }
            }
            CStmt::Switch { cond, body }
            | CStmt::While { cond, body }
            | CStmt::DoWhile { body, cond } => {
                Self::collect_address_taken_expr(cond, out);
                Self::collect_address_taken_stmt(body, out);
            }
            CStmt::For {
                init,
                cond,
                update,
                body,
            } => {
                if let Some(init) = init {
                    Self::collect_address_taken_stmt(init, out);
                }
                if let Some(cond) = cond {
                    Self::collect_address_taken_expr(cond, out);
                }
                if let Some(update) = update {
                    Self::collect_address_taken_expr(update, out);
                }
                Self::collect_address_taken_stmt(body, out);
            }
            CStmt::Case { stmt, .. } | CStmt::Label { stmt, .. } => {
                Self::collect_address_taken_stmt(stmt, out);
            }
            CStmt::StaticAssert { cond, .. } => Self::collect_address_taken_expr(cond, out),
            CStmt::FuncDef(_)
            | CStmt::Empty
            | CStmt::Break
            | CStmt::Continue
            | CStmt::Return(None)
            | CStmt::Goto(_)
            | CStmt::Asm(_)
            | CStmt::Assert(_)
            | CStmt::Assume(_) => {}
        }
    }

    fn collect_address_taken_initializer(init: &Initializer, out: &mut HashSet<String>) {
        match init {
            Initializer::Expr(expr) => Self::collect_address_taken_expr(expr, out),
            Initializer::Designated { designator, init } => {
                Self::collect_address_taken_designator(designator, out);
                Self::collect_address_taken_initializer(init, out);
            }
            Initializer::List(items) => {
                for item in items {
                    Self::collect_address_taken_initializer(item, out);
                }
            }
        }
    }

    fn collect_address_taken_designator(designator: &Designator, out: &mut HashSet<String>) {
        match designator {
            Designator::Field(_) => {}
            Designator::Index(index) => Self::collect_address_taken_expr(index, out),
            Designator::Chain(parts) => {
                for part in parts {
                    Self::collect_address_taken_designator(part, out);
                }
            }
        }
    }

    fn collect_address_taken_expr(expr: &CExpr, out: &mut HashSet<String>) {
        match expr {
            CExpr::UnaryOp {
                op: UnaryOp::AddrOf,
                operand,
            } => {
                if let CExpr::Var(name) = operand.as_ref() {
                    out.insert(name.clone());
                }
                Self::collect_address_taken_expr(operand, out);
            }
            CExpr::UnaryOp { operand, .. } | CExpr::Cast { expr: operand, .. } => {
                Self::collect_address_taken_expr(operand, out);
            }
            CExpr::BinOp { left, right, .. } => {
                Self::collect_address_taken_expr(left, out);
                Self::collect_address_taken_expr(right, out);
            }
            CExpr::Conditional {
                cond,
                then_expr,
                else_expr,
            } => {
                Self::collect_address_taken_expr(cond, out);
                Self::collect_address_taken_expr(then_expr, out);
                Self::collect_address_taken_expr(else_expr, out);
            }
            CExpr::Call { func, args } => {
                Self::collect_address_taken_expr(func, out);
                for arg in args {
                    Self::collect_address_taken_expr(arg, out);
                }
            }
            CExpr::Index { array, index } => {
                Self::collect_address_taken_expr(array, out);
                Self::collect_address_taken_expr(index, out);
            }
            CExpr::Member { object, .. } => Self::collect_address_taken_expr(object, out),
            CExpr::Arrow { pointer, .. } => Self::collect_address_taken_expr(pointer, out),
            CExpr::CompoundLiteral { init, .. } => {
                for item in init {
                    Self::collect_address_taken_initializer(item, out);
                }
            }
            CExpr::Generic {
                control,
                associations,
            } => {
                Self::collect_address_taken_expr(control, out);
                for (_, result) in associations {
                    Self::collect_address_taken_expr(result, out);
                }
            }
            CExpr::StmtExpr(stmts) => {
                for stmt in stmts {
                    Self::collect_address_taken_stmt(stmt, out);
                }
            }
            // `sizeof(expr)` does not evaluate its operand, so an `&x` under
            // sizeof does not make x aliased at run time.
            CExpr::SizeOf(SizeOfArg::Type(_) | SizeOfArg::Expr(_))
            | CExpr::IntLit(_)
            | CExpr::UIntLit(_)
            | CExpr::FloatLit(_)
            | CExpr::CharLit(_)
            | CExpr::StringLit(_)
            | CExpr::Var(_)
            | CExpr::AlignOf(_) => {}
        }
    }

    /// Generate a fresh variable name
    pub(crate) fn fresh_var(&mut self, base: &str) -> String {
        self.fresh_counter += 1;
        format!("{}_{}", base, self.fresh_counter)
    }

    /// Add a VC to prove
    pub(crate) fn add_vc(
        &mut self,
        kind: VCKind,
        description: &str,
        obligation: Spec,
        location: Option<usize>,
    ) {
        // Incorporate path condition: path_condition → obligation
        let full_obligation = if self.path_condition.is_empty() {
            obligation
        } else {
            let path = Spec::and(self.path_condition.clone());
            Spec::implies(path, obligation)
        };

        self.vcs.push(VC {
            description: description.to_string(),
            obligation: full_obligation,
            location,
            kind,
        });
    }

    /// Close the loop-variant snapshot variable in every VC emitted by the
    /// extra `wp_stmt` pass that computes the variant's post-body value.
    ///
    /// That pass (see `wp_while`) re-walks the loop body with `variant <
    /// snapshot` as the postcondition, so it re-emits obligations. Each one is
    /// either:
    ///
    /// * a byte-identical copy of an obligation the invariant-preservation pass
    ///   over the same body already emitted (side conditions — UB, memory
    ///   safety, assertions — do not depend on the postcondition): dropped, it
    ///   carries no new information; or
    /// * a genuinely new obligation mentioning `snapshot` — e.g. a nested
    ///   loop's `inner_I ∧ ¬inner_cond → variant < snapshot` exit link. Here
    ///   `snapshot` is a rigid unknown: it denotes the outer loop head's
    ///   variant value, and the state this obligation is stated in is NOT that
    ///   state, so the defining equation may not be substituted in. It is
    ///   universally quantified instead, which is sound and fails closed (the
    ///   obligation is discharged only if the inner invariant genuinely carries
    ///   the information).
    ///
    /// SOUNDNESS: never substitute the variant expression for `snapshot` in
    /// these — the program variables it mentions have moved on.
    fn close_snapshot_vcs(&mut self, mark: usize, snapshot: &str) {
        for i in (mark..self.vcs.len()).rev() {
            let is_duplicate = self.vcs[..mark].iter().any(|prev| {
                prev.kind == self.vcs[i].kind
                    && prev.description == self.vcs[i].description
                    && prev.obligation == self.vcs[i].obligation
            });
            if is_duplicate {
                self.vcs.remove(i);
            } else if self.spec_mentions_var(&self.vcs[i].obligation, snapshot) {
                let obligation = std::mem::replace(&mut self.vcs[i].obligation, Spec::True);
                self.vcs[i].obligation = Spec::forall(snapshot, CType::int(), obligation);
            }
        }
    }

    /// Does `var` occur free in `spec`?
    ///
    /// Decided through `subst_var` itself, with two distinct sentinels: the
    /// smart constructors it rebuilds through (`Spec::and`, `Spec::or`) may
    /// normalize, but they normalize both results identically, so the two
    /// substitutions differ exactly when a free occurrence was replaced. This
    /// also inherits `subst_var`'s shadowing rules for free.
    fn spec_mentions_var(&self, spec: &Spec, var: &str) -> bool {
        self.subst_var(spec, var, &Spec::Int(i64::MIN))
            != self.subst_var(spec, var, &Spec::Int(i64::MAX))
    }

    /// Emit an `Unsupported` obligation for a construct the verifier cannot
    /// reason about soundly. Reported as `Unknown`, this forces the enclosing
    /// function to be NOT verified (fail-closed) rather than silently skipping
    /// the construct and certifying it. SOUNDNESS: see
    /// docs/SOUNDNESS_FINDINGS_CLEAN_C_SEM_2026-07.md holes 2,4.
    pub(crate) fn add_unsupported(&mut self, description: &str) {
        // The obligation is a placeholder; `prove_vc` short-circuits any
        // `Unsupported`-kind VC to `Unknown` regardless of its content.
        self.vcs.push(VC {
            description: description.to_string(),
            obligation: Spec::True,
            location: None,
            kind: VCKind::Unsupported,
        });
    }

    /// Generate VCs for a function
    pub fn gen_function(&mut self, func: &FuncDef, spec: &FuncSpec) -> Vec<VC> {
        self.vcs.clear();
        self.path_condition.clear();
        self.prepare_function_objects(func);

        // `terminates P` is an authority-bearing total-correctness claim, not
        // an assumption.  Until termination evidence is linked into this WP,
        // accepting the parsed clause would silently prove only partial
        // correctness.  Keep the syntax but fail closed per use.
        if spec.terminates.is_some() {
            self.add_unsupported("terminates clause: termination proof is not linked");
        }

        // Start with precondition as assumption
        for req in &spec.requires {
            self.path_condition.push(req.clone());
        }

        // Compute WP of body with postcondition
        let postcondition = if spec.ensures.is_empty() {
            Spec::True
        } else {
            Spec::and(spec.ensures.clone())
        };

        let wp = self.wp_stmt(&func.body, &postcondition, None);

        // VC: precondition → wp(body, postcondition)
        let precondition = if spec.requires.is_empty() {
            Spec::True
        } else {
            Spec::and(spec.requires.clone())
        };

        self.vcs.push(VC {
            description: format!("Function {} satisfies its contract", func.name),
            obligation: Spec::implies(precondition, wp),
            location: None,
            kind: VCKind::Postcondition,
        });

        // Check assigns clause if present
        if !spec.assigns.is_empty() {
            // Collect all modified locations in the function body
            let modified = self.collect_modified_locations(&func.body);

            // Collect local variable names (parameters + locals in body)
            let mut locals = self.collect_local_variables(&func.body);
            // Function parameters are also local to the function
            for param in &func.params {
                locals.push(param.name.clone());
            }

            // Filter out local variables - they don't affect external state
            let non_local_modified = self.filter_non_locals(modified, &locals);

            // Generate VCs for assigns clause violations
            let assigns_vcs = self.check_assigns(&spec.assigns, &non_local_modified);
            self.vcs.extend(assigns_vcs);
        }

        std::mem::take(&mut self.vcs)
    }

    /// Compute weakest precondition of a statement
    ///
    /// `wp(stmt, Q)` = weakest P such that {P} stmt {Q}
    pub fn wp_stmt(&mut self, stmt: &CStmt, postcond: &Spec, loop_spec: Option<&LoopSpec>) -> Spec {
        match stmt {
            CStmt::Empty => {
                // wp(skip, Q) = Q
                postcond.clone()
            }

            CStmt::Expr(e) => {
                // For expression statements, check for side effects
                self.wp_expr(e, postcond)
            }

            CStmt::Decl(decl) => {
                // wp(T x = e, Q) = Q[(T)e/x] for the bounded scalar lane.
                if let Some(Initializer::Expr(init)) = &decl.init {
                    // SOUNDNESS (hole 1): the initializer is evaluated, so emit
                    // its UB obligations (e.g. `int x = a/b;` needs `b != 0`).
                    self.check_expr_ub(init);
                    if init.has_side_effects() {
                        self.add_unsupported(
                            "side effect in declaration initializer: state sequencing not modeled",
                        );
                        return postcond.clone();
                    }
                    if let Some(value) = self.initializer_value(decl, init) {
                        self.substitute(postcond, &decl.name, &value)
                    } else {
                        postcond.clone()
                    }
                } else if decl.init.is_some() {
                    self.add_unsupported(
                        "aggregate/designated declaration initializer: state update not modeled",
                    );
                    postcond.clone()
                } else if matches!(decl.storage, StorageClass::Auto | StorageClass::Register) {
                    // Reading an indeterminate automatic object is UB.  This WP
                    // does not yet track definite initialization, so it cannot
                    // distinguish a later initialized read from an unsafe one.
                    self.add_unsupported(
                        "uninitialized automatic object: definite initialization not tracked",
                    );
                    postcond.clone()
                } else if matches!(
                    decl.storage,
                    StorageClass::Static | StorageClass::ThreadLocal
                ) && decl.ty.is_integer()
                {
                    // Static/thread-local integer objects are zero-initialized.
                    self.substitute(postcond, &decl.name, &CExpr::int(0))
                } else {
                    postcond.clone()
                }
            }

            CStmt::Block(stmts) => {
                // wp(s1; s2; ...; sn, Q) = wp(s1, wp(s2, ... wp(sn, Q)))
                let mut q = postcond.clone();
                for s in stmts.iter().rev() {
                    q = self.wp_stmt(s, &q, loop_spec);
                }
                q
            }

            CStmt::If {
                cond,
                then_stmt,
                else_stmt,
            } => {
                // wp(if b then s1 else s2, Q) = (b → wp(s1, Q)) ∧ (¬b → wp(s2, Q))
                // SOUNDNESS (hole 1): the condition is evaluated, so emit its UB
                // obligations (e.g. `if (a/b)` needs `b != 0`).
                self.check_expr_ub(cond);
                self.reject_unmodeled_effects(
                    cond,
                    "side effect in if condition: conditional state update not modeled",
                );
                let cond_spec = self.expr_to_spec(cond);
                let wp_then = self.wp_stmt(then_stmt, postcond, loop_spec);

                let wp_else = if let Some(else_s) = else_stmt {
                    self.wp_stmt(else_s, postcond, loop_spec)
                } else {
                    postcond.clone()
                };

                Spec::and(vec![
                    Spec::implies(cond_spec.clone(), wp_then),
                    Spec::implies(Spec::not(cond_spec), wp_else),
                ])
            }

            CStmt::While { cond, body } => self.wp_while(cond, body, postcond, loop_spec),

            CStmt::DoWhile { cond, body } => {
                // do { body } while (cond) ≡ body; while (cond) { body }
                let while_wp = self.wp_while(cond, body, postcond, loop_spec);
                self.wp_stmt(body, &while_wp, loop_spec)
            }

            CStmt::For {
                init,
                cond,
                update,
                body,
            } => {
                // for (init; cond; update) body ≡ init; while (cond) { body; update }
                let cond_expr = cond.clone().unwrap_or_else(|| CExpr::int(1)); // Missing cond = true

                // Build equivalent while loop body: body; update
                let while_body = if let Some(upd) = update {
                    CStmt::Block(vec![(**body).clone(), CStmt::Expr(upd.clone())])
                } else {
                    (**body).clone()
                };

                let while_wp = self.wp_while(&cond_expr, &while_body, postcond, loop_spec);

                // Apply init
                if let Some(init_stmt) = init {
                    self.wp_stmt(init_stmt, &while_wp, loop_spec)
                } else {
                    while_wp
                }
            }

            CStmt::Return(expr) => {
                // wp(return e, Q) = Q[\result ← e]
                if let Some(e) = expr {
                    // SOUNDNESS (hole 1): the returned expression is evaluated,
                    // so emit its UB obligations even in `ensures`-only
                    // functions (e.g. `return a/b;` needs `b != 0`).
                    self.check_expr_ub(e);
                    self.reject_unmodeled_effects(
                        e,
                        "side effect in return expression: state update not modeled",
                    );
                    let value = self.return_value(e).unwrap_or_else(|| e.clone());
                    self.substitute_result(postcond, &value)
                } else {
                    postcond.clone()
                }
            }

            CStmt::Break => {
                // Break transfers control outside the loop
                // In WP calculus, we need the loop's postcondition
                // This is handled by loop_spec if available
                postcond.clone()
            }

            CStmt::Continue => {
                // Continue jumps to loop condition check
                // Need loop invariant
                if let Some(ls) = loop_spec {
                    if ls.variant.is_some() {
                        // The existing variant pass computes wp(body, V<V0),
                        // but `continue` jumps to the condition/update edge.
                        // Until that edge is explicit, it cannot retain total-
                        // correctness authority.
                        self.add_unsupported(
                            "continue with loop variant: backedge identity not modeled",
                        );
                    }
                    if ls.invariant.is_empty() {
                        Spec::True
                    } else {
                        Spec::and(ls.invariant.clone())
                    }
                } else {
                    postcond.clone()
                }
            }

            CStmt::Switch { cond, body } => {
                // wp(switch(e) { case c1: s1; ... case cn: sn; default: sd; }, Q)
                //
                // For proper switch semantics, we need to handle:
                // 1. Case matching: which case is selected
                // 2. Fallthrough: cases without break continue to next case
                // 3. Default case: executed if no case matches
                //
                // We transform switch into equivalent if-else chain:
                // if (e == c1) { s1... } else if (e == c2) { s2... } else { sd }
                //
                // For fallthrough (no break), the statements of multiple cases are combined.

                // SOUNDNESS (hole 1): the switch controlling expression is
                // evaluated, so emit its UB obligations.
                self.check_expr_ub(cond);
                self.reject_unmodeled_effects(
                    cond,
                    "side effect in switch condition: state update not modeled",
                );
                let cond_spec = self.expr_to_spec(cond);

                // Extract cases from switch body
                let cases = self.extract_switch_cases(body);

                if cases.is_empty() {
                    // Empty switch - just evaluate condition for side effects
                    return postcond.clone();
                }

                // Build if-else chain from cases
                let mut has_default = false;
                let mut default_wp = postcond.clone();

                // Find default case first
                for (label, stmt_body) in &cases {
                    if matches!(label, CaseLabel::Default) {
                        has_default = true;
                        default_wp = self.wp_stmt(stmt_body, postcond, loop_spec);
                        break;
                    }
                }

                // Build conditions for each case
                let mut case_conditions = Vec::new();

                for (label, stmt_body) in &cases {
                    if let CaseLabel::Case(case_expr) = label {
                        let case_spec = self.expr_to_spec(case_expr);
                        let case_cond = Spec::binop(BinOp::Eq, cond_spec.clone(), case_spec);
                        let case_wp = self.wp_stmt(stmt_body, postcond, loop_spec);
                        case_conditions.push((case_cond, case_wp));
                    }
                }

                if case_conditions.is_empty() && has_default {
                    // Only default case - always execute it
                    return default_wp;
                }

                // Build: (c1 → wp1) ∧ (c2 → wp2) ∧ ... ∧ (¬c1 ∧ ¬c2 ∧ ... → default_wp)
                let mut conjuncts = Vec::new();

                // Add implications for each case
                for (case_cond, case_wp) in &case_conditions {
                    conjuncts.push(Spec::implies(case_cond.clone(), case_wp.clone()));
                }

                // Add default/no-match case
                if !case_conditions.is_empty() {
                    let no_match_cond = Spec::and(
                        case_conditions
                            .iter()
                            .map(|(c, _)| Spec::not(c.clone()))
                            .collect(),
                    );

                    if has_default {
                        conjuncts.push(Spec::implies(no_match_cond, default_wp));
                    } else {
                        // No default - if no case matches, just postcond holds
                        conjuncts.push(Spec::implies(no_match_cond, postcond.clone()));
                    }
                }

                Spec::and(conjuncts)
            }

            CStmt::Goto(_) | CStmt::Label { .. } => {
                // SOUNDNESS (hole 2): `goto`/`label` reorder control flow in a
                // way this WP calculus does not model. Previously modeled as
                // skip, which let a goto-reordered function "prove" a false
                // `ensures`. Emit an Unsupported obligation so the function is
                // reported NOT verified.
                self.add_unsupported("goto/label: control flow not modeled");
                postcond.clone()
            }

            CStmt::Assert(spec) => {
                // wp(assert P, Q) = P ∧ Q
                self.add_vc(VCKind::Assertion, "Assertion must hold", spec.clone(), None);
                Spec::and(vec![spec.clone(), postcond.clone()])
            }

            CStmt::Assume(spec) => {
                // wp(assume P, Q) = P → Q
                Spec::implies(spec.clone(), postcond.clone())
            }

            CStmt::DeclList(decls) => {
                // Handle multiple declarations by processing in reverse
                let mut q = postcond.clone();
                for decl in decls.iter().rev() {
                    if let Some(Initializer::Expr(init)) = &decl.init {
                        // SOUNDNESS (hole 1): each initializer is evaluated.
                        self.check_expr_ub(init);
                        if init.has_side_effects() {
                            self.add_unsupported(
                                "side effect in declaration initializer: state sequencing not modeled",
                            );
                        } else if let Some(value) = self.initializer_value(decl, init) {
                            q = self.substitute(&q, &decl.name, &value);
                        }
                    } else if decl.init.is_some() {
                        self.add_unsupported(
                            "aggregate/designated declaration initializer: state update not modeled",
                        );
                    } else if matches!(decl.storage, StorageClass::Auto | StorageClass::Register) {
                        self.add_unsupported(
                            "uninitialized automatic object: definite initialization not tracked",
                        );
                    } else if matches!(
                        decl.storage,
                        StorageClass::Static | StorageClass::ThreadLocal
                    ) && decl.ty.is_integer()
                    {
                        q = self.substitute(&q, &decl.name, &CExpr::int(0));
                    }
                }
                q
            }

            CStmt::Case { stmt, .. } => {
                // Switch case - just process the inner statement
                self.wp_stmt(stmt, postcond, loop_spec)
            }

            CStmt::FuncDef(_) => {
                // Function definition inside statement - ignore for WP
                postcond.clone()
            }

            CStmt::Asm(_) => {
                // SOUNDNESS (hole 2): inline assembly can have arbitrary
                // effects the verifier cannot model. Emit an Unsupported
                // obligation so the function is reported NOT verified rather
                // than silently treating the asm as a no-op.
                self.add_unsupported("inline asm: effects not modeled");
                postcond.clone()
            }

            CStmt::StaticAssert { .. } => {
                // C11 6.7.10 static assertions are checked at compile time and
                // do not affect run-time state, so wp(static_assert, Q) = Q.
                postcond.clone()
            }
        }
    }

    /// WP for while loops
    fn wp_while(
        &mut self,
        cond: &CExpr,
        body: &CStmt,
        postcond: &Spec,
        loop_spec: Option<&LoopSpec>,
    ) -> Spec {
        // SOUNDNESS (hole 1): the loop condition is evaluated on every
        // iteration test, so emit its UB obligations (e.g. `while (1/0)`).
        self.check_expr_ub(cond);
        self.reject_unmodeled_effects(
            cond,
            "side effect in loop condition: backedge state update not modeled",
        );
        let cond_spec = self.expr_to_spec(cond);

        // If we have a loop specification, use it
        if let Some(ls) = loop_spec {
            let invariant = if ls.invariant.is_empty() {
                Spec::True
            } else {
                Spec::and(ls.invariant.clone())
            };

            // Generate VCs for loop:

            // 1. Loop invariant holds on entry (this is a precondition to the loop)
            // Already implied by requiring I in the WP

            // 2. Loop body preserves invariant: I ∧ cond → wp(body, I)
            let wp_body = self.wp_stmt(body, &invariant, Some(ls));
            self.add_vc(
                VCKind::LoopInvariantPreserved,
                "Loop body preserves invariant",
                Spec::implies(
                    Spec::and(vec![invariant.clone(), cond_spec.clone()]),
                    wp_body,
                ),
                None,
            );

            // 3. Invariant + ¬cond → postcondition
            self.add_vc(
                VCKind::Postcondition,
                "Loop exit satisfies postcondition",
                Spec::implies(
                    Spec::and(vec![invariant.clone(), Spec::not(cond_spec.clone())]),
                    postcond.clone(),
                ),
                None,
            );

            // 4. If there's a variant, it decreases and stays non-negative
            if let Some(variant) = &ls.variant {
                // SOUNDNESS: the decrease obligation must compare the variant's
                // value AFTER the body against its value BEFORE the body. This
                // WP calculus threads state by substituting into the
                // postcondition, so the post-body value is obtained by running
                // `wp_stmt` over the body with `variant < snapshot` as the
                // postcondition: the body's assignments rewrite the LEFT
                // operand (the variant) while `snapshot` — a rigid logic
                // variable no C statement can assign to — is left alone.
                //
                // The snapshot name is deliberately NOT a valid C identifier so
                // that no program variable can ever collide with (and thereby
                // capture) it during that substitution pass.
                //
                // Previously this compared the variant against a variable that
                // was never bound to anything (the binding `Spec::Let` was
                // built and then discarded), so the obligation said nothing
                // about termination.
                let snapshot = self.fresh_var(SNAPSHOT_BASE);
                let mark = self.vcs.len();
                let wp_decrease = self.wp_stmt(
                    body,
                    &Spec::lt(variant.clone(), Spec::var(&snapshot)),
                    Some(ls),
                );
                self.close_snapshot_vcs(mark, &snapshot);

                // At the loop head the snapshot *is* the variant expression, so
                // the binder is eliminated by substitution
                // (`\let x = e; P` ≡ `P[e/x]`). This keeps the obligation
                // quantifier-free, and — unlike a `Spec::Let`, which the
                // translation layer maps to an opaque `Spec.unsupported.Let`
                // constant — leaves it in a shape the prover can discharge.
                let decrease = self.subst_var(&wp_decrease, &snapshot, variant);

                // Variant decreases: I ∧ cond → wp(body, variant < variant@head)
                self.add_vc(
                    VCKind::LoopVariantDecreases,
                    "Loop variant decreases",
                    Spec::implies(
                        Spec::and(vec![invariant.clone(), cond_spec.clone()]),
                        decrease,
                    ),
                    None,
                );

                // Variant is non-negative
                self.add_vc(
                    VCKind::LoopVariantNonNegative,
                    "Loop variant is non-negative",
                    Spec::implies(
                        Spec::and(vec![invariant.clone(), cond_spec.clone()]),
                        Spec::ge(variant.clone(), Spec::int(0)),
                    ),
                    None,
                );
            }

            // WP of loop is the invariant (caller must establish it)
            invariant
        } else {
            // No explicit loop spec - try automatic invariant inference
            let mut inference = InvariantInference::new();
            let mut context = InferenceContext::new();

            // Extract loop counter variable from condition (if present)
            let loop_var = Self::extract_loop_variable(cond);

            // Extract modified variables from body for ghost tracking
            let modified_vars = Self::extract_modified_variables(body);

            // Generate ghost variables for the loop
            context.generate_loop_ghosts(loop_var.as_deref(), &modified_vars);

            // Extract array accesses and generate frame ghosts for read-only elements
            let array_accesses = Self::extract_array_accesses(body);
            // Convert CExpr indices to Spec for ghost tracking
            let spec_accesses: Vec<(String, Spec, bool)> = array_accesses
                .iter()
                .filter_map(|(arr, idx, is_write)| {
                    Self::cexpr_to_spec(idx).map(|spec_idx| (arr.clone(), spec_idx, *is_write))
                })
                .collect();
            context.generate_array_frame_ghosts(&spec_accesses);

            // Collect inferred invariants
            let mut inferred_invariants = inference.infer_while_invariant(cond, body, &context);

            // Also try search pattern detection
            if let Some(search_inv) = inference.detect_search_pattern(cond, body) {
                inferred_invariants.push(search_inv);
            }

            if inferred_invariants.is_empty() {
                // SOUNDNESS (hole 4): with no sound loop invariant we cannot
                // establish anything about the loop. Previously this emitted a
                // trivial `Spec::True` VC and modeled the loop as skip, so the
                // body's UB obligations (div-by-zero, null deref, ...) were
                // never generated and a loop containing genuine UB verified.
                // Now: (1) emit an Unsupported obligation so the function is
                // reported NOT verified, and (2) still descend into the body
                // under the loop-entry path condition so the body's own UB VCs
                // ARE generated (a `1/0` inside the loop must still fail).
                self.add_unsupported(
                    "loop requires invariant annotation (automatic inference failed)",
                );

                // Descend into the body to emit its side-condition (UB) VCs.
                // The loop condition holds when the body executes, so add it to
                // the path condition for the descent. The resulting WP is
                // discarded — the loop's own WP is the (missing) invariant,
                // which we conservatively leave unmodeled by returning postcond;
                // the Unsupported obligation already forces NOT verified.
                self.path_condition.push(cond_spec.clone());
                let _ = self.wp_stmt(body, postcond, None);
                self.path_condition.pop();

                postcond.clone()
            } else {
                // Use the inferred invariants
                let invariant = if inferred_invariants.len() == 1 {
                    inferred_invariants.pop().unwrap()
                } else {
                    Spec::and(inferred_invariants)
                };

                // Generate VCs for inferred invariant
                self.add_vc(
                    VCKind::LoopInvariantEntry,
                    "Inferred invariant holds on entry",
                    invariant.clone(),
                    None,
                );

                // Loop body preserves invariant: I ∧ cond → wp(body, I)
                let wp_body = self.wp_stmt(body, &invariant, None);
                self.add_vc(
                    VCKind::LoopInvariantPreserved,
                    "Inferred invariant preserved by loop body",
                    Spec::implies(
                        Spec::and(vec![invariant.clone(), cond_spec.clone()]),
                        wp_body,
                    ),
                    None,
                );

                // Invariant + ¬cond → postcondition
                self.add_vc(
                    VCKind::Postcondition,
                    "Loop exit with inferred invariant satisfies postcondition",
                    Spec::implies(
                        Spec::and(vec![invariant.clone(), Spec::not(cond_spec.clone())]),
                        postcond.clone(),
                    ),
                    None,
                );

                invariant
            }
        }
    }

    fn compound_base_op(op: BinOp) -> Option<BinOp> {
        match op {
            BinOp::AddAssign => Some(BinOp::Add),
            BinOp::SubAssign => Some(BinOp::Sub),
            BinOp::MulAssign => Some(BinOp::Mul),
            BinOp::DivAssign => Some(BinOp::Div),
            BinOp::ModAssign => Some(BinOp::Mod),
            BinOp::BitAndAssign => Some(BinOp::BitAnd),
            BinOp::BitOrAssign => Some(BinOp::BitOr),
            BinOp::BitXorAssign => Some(BinOp::BitXor),
            BinOp::ShlAssign => Some(BinOp::Shl),
            BinOp::ShrAssign => Some(BinOp::Shr),
            _ => None,
        }
    }

    fn type_is_volatile(ty: &CType) -> bool {
        match ty {
            CType::Qualified {
                ty, is_volatile, ..
            } => *is_volatile || Self::type_is_volatile(ty),
            _ => false,
        }
    }

    fn cast_for_conversion(expr: CExpr, from: &CType, to: &CType) -> CExpr {
        if from.is_compatible(to) {
            expr
        } else {
            CExpr::cast(to.unqualified().clone(), expr)
        }
    }

    fn reject_unmodeled_effects(&mut self, expr: &CExpr, description: &str) {
        if expr.has_side_effects() {
            self.add_unsupported(description);
        }
    }

    /// Apply the scalar initialization conversion represented by this WP.
    /// Aggregate, pointer/floating, volatile, alias-reading, and untyped cases
    /// are deliberately outside the authority lane and emit Unsupported.
    fn initializer_value(&mut self, decl: &VarDecl, init: &CExpr) -> Option<CExpr> {
        if matches!(decl.storage, StorageClass::Auto | StorageClass::Register)
            && Self::expr_reads_object(init, &decl.name)
        {
            // The declarator's scope already includes its initializer, so
            // `int x = x;` reads the new indeterminate x (and a same-name
            // shadow cannot be resolved by this non-scope-indexed WP).
            self.add_unsupported(
                "self-referential automatic initializer: object identity/initialization not modeled",
            );
            return None;
        }
        if Self::type_is_volatile(&decl.ty) || !decl.ty.is_integer() {
            self.add_unsupported(
                "declaration initializer outside the bounded integer-scalar WP lane",
            );
            return None;
        }
        if !self.compound_rhs_is_stable(init) {
            self.add_unsupported(
                "declaration initializer reads aliased, volatile, or unmodelled state",
            );
            return None;
        }
        let Some(source_ty) = self.wp_expr_type(init) else {
            self.add_unsupported("declaration initializer type could not be established");
            return None;
        };
        if !source_ty.is_integer() {
            self.add_unsupported(
                "declaration initializer outside the bounded integer-scalar WP lane",
            );
            return None;
        }
        Some(Self::cast_for_conversion(
            init.clone(),
            &source_ty,
            &decl.ty,
        ))
    }

    fn expr_reads_object(expr: &CExpr, object: &str) -> bool {
        match expr {
            CExpr::Var(name) => name == object,
            CExpr::UnaryOp {
                op: UnaryOp::AddrOf,
                operand,
            } if matches!(operand.as_ref(), CExpr::Var(_)) => false,
            CExpr::UnaryOp { operand, .. } | CExpr::Cast { expr: operand, .. } => {
                Self::expr_reads_object(operand, object)
            }
            CExpr::BinOp { left, right, .. } => {
                Self::expr_reads_object(left, object) || Self::expr_reads_object(right, object)
            }
            CExpr::Conditional {
                cond,
                then_expr,
                else_expr,
            } => {
                Self::expr_reads_object(cond, object)
                    || Self::expr_reads_object(then_expr, object)
                    || Self::expr_reads_object(else_expr, object)
            }
            CExpr::Call { func, args } => {
                Self::expr_reads_object(func, object)
                    || args.iter().any(|arg| Self::expr_reads_object(arg, object))
            }
            CExpr::Index { array, index } => {
                Self::expr_reads_object(array, object) || Self::expr_reads_object(index, object)
            }
            CExpr::Member { object: base, .. } => Self::expr_reads_object(base, object),
            CExpr::Arrow { pointer, .. } => Self::expr_reads_object(pointer, object),
            CExpr::CompoundLiteral { init, .. } => init
                .iter()
                .any(|item| Self::initializer_reads_object(item, object)),
            CExpr::Generic { associations, .. } => associations
                .iter()
                .any(|(_, selected)| Self::expr_reads_object(selected, object)),
            CExpr::StmtExpr(_) => true,
            // sizeof(expr) does not evaluate its operand.
            CExpr::SizeOf(_)
            | CExpr::IntLit(_)
            | CExpr::UIntLit(_)
            | CExpr::FloatLit(_)
            | CExpr::CharLit(_)
            | CExpr::StringLit(_)
            | CExpr::AlignOf(_) => false,
        }
    }

    fn initializer_reads_object(init: &Initializer, object: &str) -> bool {
        match init {
            Initializer::Expr(expr) => Self::expr_reads_object(expr, object),
            Initializer::Designated { designator, init } => {
                Self::designator_reads_object(designator, object)
                    || Self::initializer_reads_object(init, object)
            }
            Initializer::List(items) => items
                .iter()
                .any(|item| Self::initializer_reads_object(item, object)),
        }
    }

    fn designator_reads_object(designator: &Designator, object: &str) -> bool {
        match designator {
            Designator::Field(_) => false,
            Designator::Index(index) => Self::expr_reads_object(index, object),
            Designator::Chain(parts) => parts
                .iter()
                .any(|part| Self::designator_reads_object(part, object)),
        }
    }

    /// Materialize the function return assignment conversion where the static
    /// types are known.  Side effects are rejected by the caller; an unknown or
    /// incompatible conversion also loses authority rather than reusing an
    /// entry-state expression as though no conversion occurred.
    fn return_value(&mut self, expr: &CExpr) -> Option<CExpr> {
        let Some(target_ty) = self.function_return_type.clone() else {
            self.add_unsupported("function return type is unavailable to WP");
            return None;
        };
        let Some(source_ty) = self.wp_expr_type(expr) else {
            self.add_unsupported("return expression type could not be established");
            return None;
        };
        if source_ty.is_integer() && target_ty.is_integer() {
            return Some(Self::cast_for_conversion(
                expr.clone(),
                &source_ty,
                &target_ty,
            ));
        }
        if source_ty.is_compatible(&target_ty) {
            Some(expr.clone())
        } else {
            self.add_unsupported("return assignment conversion is not modeled by WP");
            None
        }
    }

    /// Infer just enough static type information for the certified
    /// compound-assignment lane. Returning `None` is intentional: the caller
    /// emits `Unsupported` and therefore cannot grant proof authority.
    fn wp_expr_type(&self, expr: &CExpr) -> Option<CType> {
        match expr {
            CExpr::IntLit(value) if i32::try_from(*value).is_ok() => Some(CType::int()),
            CExpr::UIntLit(value) if u32::try_from(*value).is_ok() => Some(CType::uint()),
            CExpr::FloatLit(_) => Some(CType::Float(crate::types::FloatKind::Double)),
            // C character constants have type int (C11 6.4.4.4p10).
            CExpr::CharLit(_) => Some(CType::int()),
            CExpr::StringLit(_) => Some(CType::ptr(CType::char())),
            CExpr::Var(name) => {
                if self.ambiguous_variables.contains(name) {
                    None
                } else {
                    self.variable_types.get(name).cloned()
                }
            }
            CExpr::BinOp { op, left, right } => {
                let left_ty = self.wp_expr_type(left)?;
                if op.is_assignment() {
                    return Some(left_ty);
                }
                if op.is_comparison() || op.is_logical() {
                    return Some(CType::int());
                }
                let right_ty = self.wp_expr_type(right)?;
                if op.is_shift() {
                    if left_ty.is_integer() && right_ty.is_integer() {
                        Some(left_ty.integer_promotion())
                    } else {
                        None
                    }
                } else if left_ty.is_arithmetic() && right_ty.is_arithmetic() {
                    Some(left_ty.usual_arithmetic_conversion(&right_ty))
                } else {
                    None
                }
            }
            CExpr::UnaryOp { op, operand } => {
                let operand_ty = self.wp_expr_type(operand)?;
                match op {
                    UnaryOp::Deref => operand_ty.pointee().cloned(),
                    UnaryOp::AddrOf => Some(CType::ptr(operand_ty)),
                    UnaryOp::LogNot => Some(CType::int()),
                    UnaryOp::Neg | UnaryOp::Pos | UnaryOp::BitNot => operand_ty
                        .is_integer()
                        .then(|| operand_ty.integer_promotion()),
                    UnaryOp::PreInc | UnaryOp::PreDec | UnaryOp::PostInc | UnaryOp::PostDec => {
                        Some(operand_ty)
                    }
                }
            }
            CExpr::Conditional {
                then_expr,
                else_expr,
                ..
            } => {
                let then_ty = self.wp_expr_type(then_expr)?;
                let else_ty = self.wp_expr_type(else_expr)?;
                if then_ty.is_arithmetic() && else_ty.is_arithmetic() {
                    Some(then_ty.usual_arithmetic_conversion(&else_ty))
                } else if then_ty.is_compatible(&else_ty) {
                    Some(then_ty)
                } else {
                    None
                }
            }
            CExpr::Cast { ty, expr } => {
                let source_ty = self.wp_expr_type(expr)?;
                (ty.is_integer() && source_ty.is_integer()).then(|| ty.clone())
            }
            CExpr::CompoundLiteral { ty, .. } => Some(ty.clone()),
            CExpr::SizeOf(_) | CExpr::AlignOf(_) => Some(CType::size_t()),
            CExpr::Index { array, .. } => {
                let array_ty = self.wp_expr_type(array)?;
                array_ty.element().or_else(|| array_ty.pointee()).cloned()
            }
            CExpr::Member { object, field } => self
                .wp_expr_type(object)?
                .get_field(field)
                .map(|(_, info)| info.ty.clone()),
            CExpr::Arrow { pointer, field } => self
                .wp_expr_type(pointer)?
                .pointee()?
                .get_field(field)
                .map(|(_, info)| info.ty.clone()),
            CExpr::Call { .. }
            | CExpr::Generic { .. }
            | CExpr::StmtExpr(_)
            | CExpr::IntLit(_)
            | CExpr::UIntLit(_) => None,
        }
    }

    /// The RHS value must be represented by stable scalar symbols in this WP.
    /// Reading through an alias, from a volatile object, or from an object whose
    /// scope identity is ambiguous would let an earlier unmodelled store change
    /// the value while the formula continued to use the entry-state symbol.
    fn compound_rhs_is_stable(&self, expr: &CExpr) -> bool {
        match expr {
            CExpr::IntLit(_)
            | CExpr::UIntLit(_)
            | CExpr::FloatLit(_)
            | CExpr::CharLit(_)
            | CExpr::StringLit(_)
            | CExpr::SizeOf(_)
            | CExpr::AlignOf(_) => true,
            CExpr::Var(name) => {
                !self.ambiguous_variables.contains(name)
                    && !self.address_taken.contains(name)
                    && self
                        .variable_types
                        .get(name)
                        .is_some_and(|ty| !Self::type_is_volatile(ty) && ty.is_integer())
            }
            CExpr::BinOp { op, left, right } => {
                !op.is_assignment()
                    && self.compound_rhs_is_stable(left)
                    && self.compound_rhs_is_stable(right)
            }
            CExpr::UnaryOp { op, operand } => {
                !matches!(
                    op,
                    UnaryOp::Deref
                        | UnaryOp::AddrOf
                        | UnaryOp::PreInc
                        | UnaryOp::PreDec
                        | UnaryOp::PostInc
                        | UnaryOp::PostDec
                ) && self.compound_rhs_is_stable(operand)
            }
            CExpr::Conditional {
                cond,
                then_expr,
                else_expr,
            } => {
                self.compound_rhs_is_stable(cond)
                    && self.compound_rhs_is_stable(then_expr)
                    && self.compound_rhs_is_stable(else_expr)
            }
            CExpr::Cast { expr, .. } => self.compound_rhs_is_stable(expr),
            CExpr::Call { .. }
            | CExpr::Index { .. }
            | CExpr::Member { .. }
            | CExpr::Arrow { .. }
            | CExpr::CompoundLiteral { .. }
            | CExpr::Generic { .. }
            | CExpr::StmtExpr(_) => false,
        }
    }

    /// Compute the stored value of `x op= rhs` for the bounded, sound lane.
    /// C11 6.5.16.2 evaluates the old lvalue value and RHS before one store,
    /// performs the operator's promotions/conversions, then converts the result
    /// back to the lvalue type. We materialize those conversions explicitly.
    fn compound_assignment_value(
        &mut self,
        op: BinOp,
        left: &CExpr,
        right: &CExpr,
    ) -> Option<(String, CExpr)> {
        let base_op = Self::compound_base_op(op)?;
        let CExpr::Var(name) = left else {
            self.add_unsupported(
                "compound assignment to complex lvalue: alias/write effect not modeled",
            );
            return None;
        };
        if self.ambiguous_variables.contains(name) {
            self.add_unsupported(
                "compound assignment to shadowed object: scope identity not modeled",
            );
            return None;
        }
        if self.address_taken.contains(name) {
            self.add_unsupported(
                "compound assignment to aliased object: memory substitution not authoritative",
            );
            return None;
        }
        let Some(left_ty) = self.variable_types.get(name).cloned() else {
            self.add_unsupported("compound assignment to object with unknown declared type");
            return None;
        };
        if Self::type_is_volatile(&left_ty) {
            self.add_unsupported(
                "compound assignment to volatile object: observable access not modeled",
            );
            return None;
        }
        if !left_ty.is_integer() {
            self.add_unsupported("compound assignment outside the bounded integer-scalar WP lane");
            return None;
        }
        // A nested assignment, increment, call, or statement expression can
        // change the old lvalue/RHS values or introduce unspecified sequencing.
        // This lane represents one pre-write RHS value, so fail closed instead
        // of silently reusing the post-side-effect symbolic variable.
        if right.has_side_effects() {
            self.add_unsupported(
                "side effect inside compound-assignment RHS: evaluation order not modeled",
            );
            return None;
        }
        if !self.compound_rhs_is_stable(right) {
            self.add_unsupported(
                "compound-assignment RHS reads aliased, volatile, or unmodelled state",
            );
            return None;
        }
        let Some(right_ty) = self.wp_expr_type(right) else {
            self.add_unsupported(
                "compound-assignment RHS type/conversions could not be established",
            );
            return None;
        };
        if !right_ty.is_integer() {
            self.add_unsupported("compound assignment outside the bounded integer-scalar WP lane");
            return None;
        }

        let (operation_ty, converted_right_ty) = if base_op.is_shift() {
            (left_ty.integer_promotion(), right_ty.integer_promotion())
        } else {
            let common = left_ty.usual_arithmetic_conversion(&right_ty);
            (common.clone(), common)
        };
        if !operation_ty.is_integer() || !converted_right_ty.is_integer() {
            self.add_unsupported("compound-assignment integer conversions were not closed");
            return None;
        }

        let converted_left = Self::cast_for_conversion(CExpr::var(name), &left_ty, &operation_ty);
        let converted_right =
            Self::cast_for_conversion(right.clone(), &right_ty, &converted_right_ty);
        let operation = CExpr::binop(base_op, converted_left, converted_right);
        let stored = Self::cast_for_conversion(operation, &operation_ty, &left_ty);
        Some((name.clone(), stored))
    }

    /// Compute the stored value of a plain scalar assignment.  Syntactic
    /// substitution is authoritative only for one unambiguous, non-aliased,
    /// non-volatile integer object and a stable, side-effect-free RHS.
    fn plain_assignment_value(&mut self, left: &CExpr, right: &CExpr) -> Option<(String, CExpr)> {
        let CExpr::Var(name) = left else {
            self.add_unsupported("assignment to complex lvalue: memory write effect not modeled");
            return None;
        };
        if right.has_side_effects() {
            self.add_unsupported(
                "side effect inside assignment RHS: evaluation/state sequencing not modeled",
            );
            return None;
        }
        if self.ambiguous_variables.contains(name) {
            self.add_unsupported("assignment to shadowed object: scope identity not modeled");
            return None;
        }
        if self.address_taken.contains(name) {
            self.add_unsupported(
                "assignment to aliased object: memory substitution not authoritative",
            );
            return None;
        }
        let Some(left_ty) = self.variable_types.get(name).cloned() else {
            // `wp_stmt` remains a public diagnostic primitive and some unit
            // fixtures call it without `gen_function`'s type preparation.  We
            // retain its historical symbolic substitution, but the Unsupported
            // row means this path can never certify a function.
            self.add_unsupported("assignment to object with unknown declared type");
            return Some((name.clone(), right.clone()));
        };
        if Self::type_is_volatile(&left_ty) {
            self.add_unsupported("assignment to volatile object: observable access not modeled");
            return None;
        }
        if !left_ty.is_integer() {
            self.add_unsupported("assignment outside the bounded integer-scalar WP lane");
            return None;
        }
        if !self.compound_rhs_is_stable(right) {
            self.add_unsupported("assignment RHS reads aliased, volatile, or unmodelled state");
            return None;
        }
        let Some(right_ty) = self.wp_expr_type(right) else {
            self.add_unsupported("assignment RHS type/conversion could not be established");
            return None;
        };
        if !right_ty.is_integer() {
            self.add_unsupported("assignment outside the bounded integer-scalar WP lane");
            return None;
        }
        Some((
            name.clone(),
            Self::cast_for_conversion(right.clone(), &right_ty, &left_ty),
        ))
    }

    /// Compute WP for expressions with side effects.
    ///
    /// This has two responsibilities kept strictly separate:
    /// 1. Emit the expression's UB side-condition obligations (delegated to
    ///    [`Self::check_expr_ub`], which recurses over EVERY evaluated
    ///    sub-expression — see holes 1,3,10).
    /// 2. Compute the weakest-precondition state transformation.
    fn wp_expr(&mut self, expr: &CExpr, postcond: &Spec) -> Spec {
        // SOUNDNESS: emit all UB obligations for the evaluated expression first,
        // regardless of the WP-transformation shape below.
        self.check_expr_ub(expr);

        match expr {
            CExpr::BinOp {
                op: BinOp::Assign,
                left,
                right,
            } => {
                // UB (RHS eval + write-target validity) was already emitted by
                // `check_expr_ub`.  The state transformation is authoritative
                // only in the bounded scalar lane.
                if let Some((name, stored_value)) =
                    self.plain_assignment_value(left.as_ref(), right.as_ref())
                {
                    self.substitute(postcond, &name, &stored_value)
                } else {
                    // Every refusal emits Unsupported.  Retaining Q is only a
                    // diagnostic approximation and cannot mint authority.
                    postcond.clone()
                }
            }

            CExpr::BinOp { op, left, right } if Self::compound_base_op(*op).is_some() => {
                if let Some((name, stored_value)) = self.compound_assignment_value(*op, left, right)
                {
                    self.substitute(postcond, &name, &stored_value)
                } else {
                    // Every refusal above emits Unsupported, so retaining Q as
                    // a diagnostic approximation cannot mint authority.
                    postcond.clone()
                }
            }

            CExpr::UnaryOp { op, operand } => match op {
                UnaryOp::PreInc | UnaryOp::PostInc => {
                    if let Some((name, incremented)) =
                        self.compound_assignment_value(BinOp::AddAssign, operand, &CExpr::int(1))
                    {
                        self.substitute(postcond, &name, &incremented)
                    } else {
                        postcond.clone()
                    }
                }
                UnaryOp::PreDec | UnaryOp::PostDec => {
                    if let Some((name, decremented)) =
                        self.compound_assignment_value(BinOp::SubAssign, operand, &CExpr::int(1))
                    {
                        self.substitute(postcond, &name, &decremented)
                    } else {
                        postcond.clone()
                    }
                }
                _ => postcond.clone(),
            },

            CExpr::Call { func, args } => {
                // Function call: check precondition, assume postcondition. Arg
                // UB was already emitted by `check_expr_ub`.  Callee assigns /
                // heap effects are not applied to Q yet, so even a known spec
                // is diagnostic-only and must not carry proof authority.
                self.add_unsupported("function call state effects are not represented in WP");
                if let CExpr::Var(func_name) = func.as_ref() {
                    if let Some(func_spec) = self.func_specs.get(func_name).cloned() {
                        // Convert actual arguments to Spec for substitution
                        let arg_specs: Vec<Spec> =
                            args.iter().map(|a| self.expr_to_spec(a)).collect();

                        // Add VC for precondition (substituting actual args for formals)
                        for req in &func_spec.requires {
                            // Substitute formal parameters with actual arguments
                            let subst_req = self.subst_params(req, &func_spec.params, &arg_specs);
                            self.add_vc(
                                VCKind::Precondition,
                                &format!("Precondition of {func_name} must hold"),
                                subst_req,
                                None,
                            );
                        }
                        // Assume postcondition holds for the result value
                        // WP: (precondition → postcondition[\result ← call]) → Q
                        // Simplified: we assume the postcondition is available as a hypothesis
                        if !func_spec.ensures.is_empty() {
                            // The callee's postcondition becomes available as an assumption
                            // For the result, we substitute \result with the call expression
                            let call_spec = Spec::Call {
                                func: func_name.clone(),
                                args: arg_specs.clone(),
                            };
                            let callee_postcond = Spec::and(func_spec.ensures.clone());
                            // First substitute formal params with actual args
                            let param_subst =
                                self.subst_params(&callee_postcond, &func_spec.params, &arg_specs);
                            // Resolve \old() expressions: callee's \old(param) becomes actual arg value at call site
                            let old_resolved = self.resolve_old_for_call(&param_subst);
                            // Then substitute \result with the call
                            let instantiated = self.subst_result(&old_resolved, &call_spec);
                            // Return: callee_postcond → Q
                            // This means: assuming callee's postcondition, we need Q
                            return Spec::implies(instantiated, postcond.clone());
                        }
                    }
                }
                postcond.clone()
            }

            // All other expression shapes contribute no modeled state
            // transformation.  A nested assignment/inc/call/comma/statement
            // expression must therefore fail closed rather than retain Q.
            _ => {
                if expr.has_side_effects() {
                    self.add_unsupported(
                        "expression side effects are not represented by the selected WP lane",
                    );
                }
                postcond.clone()
            }
        }
    }

    /// Emit undefined-behaviour (UB) side-condition obligations for EVERY
    /// evaluated sub-expression of `expr`, recursively.
    ///
    /// SOUNDNESS (holes 1,3,10): the C surface advertises "proving absence of
    /// UB". UB obligations must be generated for a sub-expression regardless of
    /// its syntactic position (top-level statement, `return e`, a condition, an
    /// initializer, an assignment RHS, a call argument, ...). Previously they
    /// were only emitted for a handful of top-level expression-statement
    /// shapes, so `return a/b`, `if (a/b)`, `int x = a/b`, `a + a` (overflow)
    /// and `a << n` (invalid shift) generated no obligation and verified.
    ///
    /// The emitted obligation is a genuine side condition (e.g. `divisor != 0`,
    /// `INT_MIN <= a + b <= INT_MAX`, `0 <= n < 32`), so a GENUINELY-SAFE
    /// program whose precondition/invariant establishes it still verifies (the
    /// obligation is discharged), while a program with reachable UB fails.
    /// See docs/SOUNDNESS_FINDINGS_CLEAN_C_SEM_2026-07.md holes 1,3,10.
    pub(crate) fn check_expr_ub(&mut self, expr: &CExpr) {
        match expr {
            // Leaves: no sub-expressions to evaluate, no UB.
            CExpr::IntLit(_)
            | CExpr::UIntLit(_)
            | CExpr::FloatLit(_)
            | CExpr::CharLit(_)
            | CExpr::StringLit(_)
            | CExpr::Var(_)
            | CExpr::SizeOf(_)
            | CExpr::AlignOf(_) => {}

            CExpr::BinOp { op, left, right } => {
                // Assignment: the RHS is evaluated; the LHS write target may
                // need a memory-safety obligation (mirrors the read-side Deref
                // arm). Do NOT recurse into a bare Var LHS (it is a store slot,
                // not an evaluated value).
                if op.is_assignment() {
                    self.check_assign_lhs_ub(left);
                    self.check_expr_ub(right);
                    // `x op= y` computes the same binary operation as `x op
                    // y` before converting and storing. The operation's own UB
                    // (overflow, zero divisor, invalid shift) is therefore live
                    // even though the RHS alone is harmless.
                    if let Some(base_op) = Self::compound_base_op(*op) {
                        self.emit_binary_op_ub(base_op, left, right);
                    }
                    return;
                }

                // Recurse into operands first (they are evaluated).
                self.check_expr_ub(left);
                self.check_expr_ub(right);

                self.emit_binary_op_ub(*op, left, right);
            }

            CExpr::UnaryOp { op, operand } => {
                if op.is_inc_dec() {
                    self.check_assign_lhs_ub(operand);
                    let arithmetic = if matches!(op, UnaryOp::PreInc | UnaryOp::PostInc) {
                        BinOp::Add
                    } else {
                        BinOp::Sub
                    };
                    self.emit_binary_op_ub(arithmetic, operand, &CExpr::int(1));
                    return;
                }

                self.check_expr_ub(operand);
                if matches!(op, UnaryOp::Deref) {
                    // SOUNDNESS: dereference requires a valid pointer.
                    let ptr_spec = self.expr_to_spec(operand);
                    self.add_vc(
                        VCKind::MemorySafety,
                        "Pointer dereference is valid",
                        Spec::valid(ptr_spec),
                        None,
                    );
                } else if matches!(op, UnaryOp::Neg) {
                    self.emit_unary_neg_ub(operand);
                }
            }

            CExpr::Conditional {
                cond,
                then_expr,
                else_expr,
            } => {
                self.check_expr_ub(cond);
                self.check_expr_ub(then_expr);
                self.check_expr_ub(else_expr);
            }

            CExpr::Cast { expr: inner, .. } => self.check_expr_ub(inner),

            CExpr::Call { func, args } => {
                self.check_expr_ub(func);
                for arg in args {
                    self.check_expr_ub(arg);
                }
            }

            CExpr::Index { array, index } => {
                self.check_expr_ub(array);
                self.check_expr_ub(index);
                let arr_spec = self.expr_to_spec(array);
                let idx_spec = self.expr_to_spec(index);
                // SOUNDNESS: index must be in bounds.
                self.add_vc(
                    VCKind::MemorySafety,
                    "Array index is non-negative",
                    Spec::ge(idx_spec.clone(), Spec::int(0)),
                    None,
                );
                self.add_vc(
                    VCKind::MemorySafety,
                    "Array access is within bounds",
                    Spec::ValidRange {
                        ptr: Box::new(arr_spec),
                        lo: Box::new(Spec::int(0)),
                        hi: Box::new(idx_spec),
                    },
                    None,
                );
            }

            CExpr::Member { object, .. } => self.check_expr_ub(object),

            CExpr::Arrow { pointer, .. } => {
                self.check_expr_ub(pointer);
                // p->field dereferences p.
                let ptr_spec = self.expr_to_spec(pointer);
                self.add_vc(
                    VCKind::MemorySafety,
                    "Pointer dereference is valid",
                    Spec::valid(ptr_spec),
                    None,
                );
            }

            // These evaluated forms need selection/initializer/control-flow
            // semantics that this recursive UB walker does not carry.  Their
            // presence is therefore authority-blocking, not silently skipped.
            CExpr::CompoundLiteral { .. } => {
                self.add_unsupported("compound literal evaluation is not modeled by UB/WP");
            }
            CExpr::Generic { .. } => {
                self.add_unsupported("generic selection evaluation is not modeled by UB/WP");
            }
            CExpr::StmtExpr(_) => {
                self.add_unsupported("statement expression evaluation is not modeled by UB/WP");
            }
        }
    }

    /// Emit only the UB introduced by the binary operator itself. Operand UB
    /// is handled by the recursive walker, which lets compound assignment
    /// reuse this for its implicit `old_lhs op rhs` without evaluating the RHS
    /// twice.
    fn emit_binary_op_ub(&mut self, op: BinOp, left: &CExpr, right: &CExpr) {
        let conversion = self.integer_binary_conversion(op, left, right);
        match op {
            BinOp::Div | BinOp::Mod => {
                let (operation_ty, converted_left, converted_right) =
                    if let Some(parts) = conversion {
                        parts
                    } else {
                        self.add_unsupported(
                            "division/remainder operand types or conversions are not established",
                        );
                        // Keep the historical zero-divisor diagnostic too; the
                        // Unsupported row is what closes unknown authority.
                        let divisor = self.expr_to_spec(right);
                        self.add_vc(
                            VCKind::NoUB,
                            "Divisor is non-zero",
                            Spec::ne(divisor, Spec::int(0)),
                            None,
                        );
                        return;
                    };
                let dividend = self.expr_to_spec(&converted_left);
                let divisor = self.expr_to_spec(&converted_right);
                self.add_vc(
                    VCKind::NoUB,
                    "Divisor is non-zero",
                    Spec::ne(divisor.clone(), Spec::int(0)),
                    None,
                );
                if let Some((minimum, _)) = Self::signed_integer_bounds(&operation_ty) {
                    // C11 6.5.5p5: when the mathematical quotient cannot be
                    // represented, both `/` and `%` have undefined behavior.
                    self.add_vc(
                        VCKind::NoUB,
                        "Signed division/remainder excludes MIN divided by -1",
                        Spec::not(Spec::and(vec![
                            Spec::eq(dividend, Spec::int(minimum)),
                            Spec::eq(divisor, Spec::int(-1)),
                        ])),
                        None,
                    );
                }
            }
            BinOp::Add | BinOp::Sub | BinOp::Mul => {
                if let Some((operation_ty, converted_left, converted_right)) = conversion {
                    // Unsigned arithmetic wraps.  Only a signed operation has
                    // the representability side condition.
                    if let Some((minimum, maximum)) = Self::signed_integer_bounds(&operation_ty) {
                        self.emit_signed_overflow_vc(
                            op,
                            &converted_left,
                            &converted_right,
                            minimum,
                            maximum,
                        );
                    }
                } else {
                    self.add_unsupported(
                        "arithmetic operand types or conversions are not established",
                    );
                }
            }
            BinOp::Shl | BinOp::Shr => {
                let Some((operation_ty, converted_left, converted_right)) = conversion else {
                    self.add_unsupported("shift operand types or promotions are not established");
                    let amount = self.expr_to_spec(right);
                    self.add_vc(
                        VCKind::NoUB,
                        "Shift amount is non-negative",
                        Spec::ge(amount.clone(), Spec::int(0)),
                        None,
                    );
                    self.add_vc(
                        VCKind::NoUB,
                        "Shift amount is less than operand width",
                        Spec::lt(amount, Spec::int(Self::SIGNED_INT_BITS)),
                        None,
                    );
                    return;
                };
                let amount = self.expr_to_spec(&converted_right);
                let Some(width) = Self::integer_width(&operation_ty) else {
                    self.add_unsupported("shift operation width is not established");
                    return;
                };
                self.add_vc(
                    VCKind::NoUB,
                    "Shift amount is non-negative",
                    Spec::ge(amount.clone(), Spec::int(0)),
                    None,
                );
                self.add_vc(
                    VCKind::NoUB,
                    "Shift amount is less than operand width",
                    Spec::lt(amount.clone(), Spec::int(width)),
                    None,
                );
                if op == BinOp::Shl {
                    if let Some((_, maximum)) = Self::signed_integer_bounds(&operation_ty) {
                        let value = self.expr_to_spec(&converted_left);
                        self.add_vc(
                            VCKind::NoUB,
                            "Signed left-shift operand is non-negative",
                            Spec::ge(value.clone(), Spec::int(0)),
                            None,
                        );
                        self.add_vc(
                            VCKind::NoUB,
                            "Signed left-shift result is representable",
                            Spec::le(Spec::binop(BinOp::Shl, value, amount), Spec::int(maximum)),
                            None,
                        );
                    }
                }
            }
            _ => {}
        }
    }

    /// Apply integer promotions / usual arithmetic conversions and return the
    /// operation type plus explicit converted operands.
    fn integer_binary_conversion(
        &self,
        op: BinOp,
        left: &CExpr,
        right: &CExpr,
    ) -> Option<(CType, CExpr, CExpr)> {
        let left_ty = self.wp_expr_type(left)?;
        let right_ty = self.wp_expr_type(right)?;
        if !left_ty.is_integer() || !right_ty.is_integer() {
            return None;
        }
        if op.is_shift() {
            let operation_ty = left_ty.integer_promotion();
            let right_promoted = right_ty.integer_promotion();
            Some((
                operation_ty.clone(),
                Self::cast_for_conversion(left.clone(), &left_ty, &operation_ty),
                Self::cast_for_conversion(right.clone(), &right_ty, &right_promoted),
            ))
        } else {
            let operation_ty = left_ty.usual_arithmetic_conversion(&right_ty);
            Some((
                operation_ty.clone(),
                Self::cast_for_conversion(left.clone(), &left_ty, &operation_ty),
                Self::cast_for_conversion(right.clone(), &right_ty, &operation_ty),
            ))
        }
    }

    fn signed_integer_bounds(ty: &CType) -> Option<(i64, i64)> {
        match ty.unqualified() {
            CType::Int(kind, Signedness::Signed) => Some((
                i64::try_from(kind.signed_min()).ok()?,
                i64::try_from(kind.signed_max()).ok()?,
            )),
            CType::Enum { .. } => Self::signed_integer_bounds(&ty.enum_underlying_type()),
            _ => None,
        }
    }

    fn integer_width(ty: &CType) -> Option<i64> {
        match ty.unqualified() {
            CType::Int(kind, _) => i64::try_from(kind.size().checked_mul(8)?).ok(),
            CType::Enum { .. } => Self::integer_width(&ty.enum_underlying_type()),
            _ => None,
        }
    }

    fn emit_unary_neg_ub(&mut self, operand: &CExpr) {
        let Some(source_ty) = self.wp_expr_type(operand) else {
            self.add_unsupported("unary negation operand type/promotion is not established");
            return;
        };
        if !source_ty.is_integer() {
            // Floating negation does not have the signed-integer MIN edge.
            return;
        }
        let promoted = source_ty.integer_promotion();
        if let Some((minimum, _)) = Self::signed_integer_bounds(&promoted) {
            let converted = Self::cast_for_conversion(operand.clone(), &source_ty, &promoted);
            self.add_vc(
                VCKind::NoUB,
                "Signed unary negation excludes the minimum value",
                Spec::ne(self.expr_to_spec(&converted), Spec::int(minimum)),
                None,
            );
        }
    }

    /// Conservative fallback width used only when a direct diagnostic caller
    /// has not supplied the function's type environment.  Such a path also
    /// emits Unsupported, so it cannot carry authority.
    const SIGNED_INT_BITS: i64 = 32;

    /// Emit a signed-overflow obligation `MIN <= (a op b) <= MAX` for an
    /// arithmetic operator, using the full-precision Spec arithmetic so the
    /// obligation is discharged when the operands are appropriately bounded by
    /// a precondition/invariant, and fails when overflow is reachable.
    fn emit_signed_overflow_vc(
        &mut self,
        op: BinOp,
        left: &CExpr,
        right: &CExpr,
        minimum: i64,
        maximum: i64,
    ) {
        let l = self.expr_to_spec(left);
        let r = self.expr_to_spec(right);
        let result = Spec::binop(op, l, r);
        self.add_vc(
            VCKind::NoUB,
            "Signed arithmetic does not overflow",
            Spec::and(vec![
                Spec::le(Spec::int(minimum), result.clone()),
                Spec::le(result, Spec::int(maximum)),
            ]),
            None,
        );
    }

    /// Emit the memory-safety obligation for the write target of an assignment
    /// with a complex LHS (`*p = e`, `a[i] = e`, `p->f = e`), mirroring the
    /// read-side handling. SOUNDNESS (hole 10): the write target was previously
    /// unchecked, so `*p = 42` with a `\true` contract verified. A bare `Var`
    /// LHS is a store slot with no evaluated address, so it needs no VC.
    fn check_assign_lhs_ub(&mut self, lhs: &CExpr) {
        match lhs {
            CExpr::Var(_) => {}
            CExpr::UnaryOp {
                op: UnaryOp::Deref,
                operand,
            } => {
                self.check_expr_ub(operand);
                let ptr_spec = self.expr_to_spec(operand);
                self.add_vc(
                    VCKind::MemorySafety,
                    "Write through pointer is valid",
                    Spec::valid(ptr_spec),
                    None,
                );
            }
            // Array / member / arrow write targets: their address computation
            // is itself an evaluated expression with its own memory obligations.
            _ => self.check_expr_ub(lhs),
        }
    }

    /// Convert a C expression to a Spec for use in logical reasoning
    pub(crate) fn expr_to_spec(&self, expr: &CExpr) -> Spec {
        match expr {
            CExpr::IntLit(n) => Spec::Int(*n),
            CExpr::Var(name) => Spec::Var(name.clone()),
            CExpr::BinOp { op, left, right } => {
                let l = self.expr_to_spec(left);
                let r = self.expr_to_spec(right);
                Spec::binop(*op, l, r)
            }
            CExpr::UnaryOp {
                op: UnaryOp::Neg,
                operand,
            } if matches!(operand.as_ref(), CExpr::IntLit(_)) => {
                let CExpr::IntLit(value) = operand.as_ref() else {
                    unreachable!("guard establishes integer literal")
                };
                value
                    .checked_neg()
                    .map_or_else(|| Spec::Expr(expr.clone()), Spec::Int)
            }
            CExpr::UnaryOp { op, operand } => Spec::UnaryOp {
                op: *op,
                operand: Box::new(self.expr_to_spec(operand)),
            },
            _ => Spec::Expr(expr.clone()),
        }
    }

    /// Get the generated VCs
    pub fn get_vcs(&self) -> &[VC] {
        &self.vcs
    }
}

/// Convert VCs to clean kernel expressions for proving
pub fn vc_to_clean(vc: &VC) -> clean_kernel::Expr {
    let mut ctx = crate::translate::TranslationContext::new();
    ctx.translate_spec(&vc.obligation)
}

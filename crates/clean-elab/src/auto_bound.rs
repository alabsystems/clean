// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Variant names share an enum-prefix by design (e.g., 'KindFoo', 'KindBar' for KindKind enums); renaming is API-breaking.
#![allow(clippy::enum_variant_names)]

//! Auto-bound implicit variable detection and insertion.
//!
//! In Lean 4, free variables appearing in a declaration body or type signature
//! are automatically bound as implicit parameters. For example:
//!
//! ```text
//! def id (x : α) : α := x
//! -- becomes: def id {α : Type} (x : α) : α := x
//!
//! def f (x : Sort u) := x
//! -- becomes: def f.{u} (x : Sort u) := x
//! ```
//!
//! This module implements the pre-elaboration pass that discovers these free
//! variables and produces the binders and universe parameters to prepend.
//!
//! Reference: Lean 4 `Lean.Elab.Term.collectUnassignedMVars`,
//! `src/Lean/Elab/PreDefinition/Basic.lean`, and
//! `src/Lean/Elab/Term.lean` (`autobound` logic).

use std::collections::HashSet;

use clean_kernel::expr::BinderInfo;
use clean_kernel::Expr;
use clean_parser::{LevelExpr, SurfaceBinder, SurfaceBinderInfo, SurfaceExpr, UniverseExpr};

/// An auto-bound variable discovered during pre-elaboration scanning.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct AutoBoundVar {
    pub name: String,
    pub kind: AutoBoundKind,
    pub binder_info: BinderInfo,
}

/// Classification of an auto-bound variable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum AutoBoundKind {
    /// Type variable: `α`, `β`, etc. -- bound as `{α : Type u}`.
    TypeVar { universe: Option<String> },
    /// Universe variable: `u`, `v`, etc. -- added as universe parameter.
    UniverseVar,
    /// Instance variable: `[Inhabited α]` etc.
    InstanceVar { class_name: String },
}

/// Well-known type names that should never be auto-bound.
const STANDARD_NAMES: &[&str] = &[
    "Nat",
    "Bool",
    "Int",
    "String",
    "Float",
    "UInt8",
    "UInt16",
    "UInt32",
    "UInt64",
    "USize",
    "Char",
    "Unit",
    "Empty",
    "True",
    "False",
    "Prop",
    "Type",
    "Sort",
    "And",
    "Or",
    "Not",
    "Iff",
    "Eq",
    "HEq",
    "Exists",
    "Sigma",
    "Subtype",
    "Decidable",
    "Option",
    "List",
    "Array",
    "IO",
    "Monad",
    "Functor",
    "Applicative",
    "BEq",
    "Hashable",
    "Repr",
    "ToString",
    "Inhabited",
    "Nonempty",
    "Zero",
    "One",
    "OfNat",
    "Add",
    "Sub",
    "Mul",
    "Div",
    "Mod",
    "Neg",
    "HPow",
    "HAdd",
    "HSub",
    "HMul",
    "HDiv",
    "HMod",
    "HAnd",
    "HOr",
    "HXor",
    "Fin",
    "BitVec",
    "Pure",
    "Bind",
    "PLift",
    "ULift",
    "Prod",
    "Sum",
    "PUnit",
    "PEmpty",
    "sorry",
    "Lean",
    "Id",
    "StateT",
    "ReaderT",
    "ExceptT",
];

/// Collector that scans surface expressions for free variables to auto-bind.
pub(crate) struct AutoBoundCollector {
    bound_names: HashSet<String>,
    found_vars: Vec<AutoBoundVar>,
    seen_names: HashSet<String>,
    universe_vars: Vec<String>,
    seen_universes: HashSet<String>,
}

impl AutoBoundCollector {
    /// Create a new collector with the given set of already-bound names.
    #[must_use]
    pub(crate) fn new(bound_names: HashSet<String>) -> Self {
        Self {
            bound_names,
            found_vars: Vec::new(),
            seen_names: HashSet::new(),
            universe_vars: Vec::new(),
            seen_universes: HashSet::new(),
        }
    }

    /// Scan an expression for free variables that should be auto-bound.
    pub(crate) fn collect_from_expr(&mut self, expr: &SurfaceExpr) {
        match expr {
            SurfaceExpr::Ident(_, name) => self.try_add_name(name),
            SurfaceExpr::Universe(_, univ) => self.collect_from_universe(univ),
            SurfaceExpr::App(_, func, args) => {
                self.collect_from_expr(func);
                for arg in args {
                    self.collect_from_expr(&arg.expr);
                }
            }
            SurfaceExpr::Lambda(_, binders, body)
            | SurfaceExpr::PatternMatchLambda(_, binders, body)
            | SurfaceExpr::Pi(_, binders, body) => {
                self.collect_from_binders_and_body(binders, body);
            }
            SurfaceExpr::Arrow(_, from, to) | SurfaceExpr::Ascription(_, from, to) => {
                self.collect_from_expr(from);
                self.collect_from_expr(to);
            }
            SurfaceExpr::Let(_, binder, val, body) | SurfaceExpr::LetRec(_, binder, val, body) => {
                self.collect_from_let(binder, val, body);
            }
            SurfaceExpr::Paren(_, inner)
            | SurfaceExpr::OutParam(_, inner)
            | SurfaceExpr::SemiOutParam(_, inner)
            | SurfaceExpr::NamedArg(_, _, inner)
            | SurfaceExpr::Explicit(_, inner)
            | SurfaceExpr::Proj(_, inner, _) => {
                self.collect_from_expr(inner);
            }
            SurfaceExpr::If(_, a, b, c)
            | SurfaceExpr::IfLet(_, _, a, b, c)
            | SurfaceExpr::IfDecidable(_, _, a, b, c)
            | SurfaceExpr::LetPattern(_, _, a, b, c) => {
                self.collect_from_expr(a);
                self.collect_from_expr(b);
                self.collect_from_expr(c);
            }
            SurfaceExpr::Match(_, hyp, scrut, arms) => {
                self.collect_from_expr(scrut);
                // The annotated discriminant (`match h : e with`) binds `h`
                // inside every arm body — it must not be collected as an
                // auto-bound candidate there. Same push/pop scoping as
                // `collect_from_binders_and_body`.
                let added_hyp = match hyp {
                    Some(h) if h != "_" && !self.bound_names.contains(h) => {
                        self.bound_names.insert(h.clone());
                        Some(h.clone())
                    }
                    _ => None,
                };
                for arm in arms {
                    self.collect_from_expr(&arm.body);
                }
                if let Some(h) = added_hyp {
                    self.bound_names.remove(&h);
                }
            }
            SurfaceExpr::UniverseInst(_, base, levels) => {
                self.collect_from_expr(base);
                for level in levels {
                    self.collect_from_level(level);
                }
            }
            SurfaceExpr::StructLit {
                struct_type,
                base,
                fields,
                ..
            } => {
                self.collect_from_struct_lit(struct_type, base, fields);
            }
            SurfaceExpr::QQuotation {
                inner, type_annot, ..
            } => {
                self.collect_from_expr(inner);
                if let Some(ta) = type_annot {
                    self.collect_from_expr(ta);
                }
            }
            // `open X in <term>`: opaque to auto-binding. Names inside the
            // sub-term are expected to resolve via the opened namespace(s) at
            // elaboration time, not to become auto-bound implicits. Collecting
            // them here would auto-bind (e.g.) a concrete `Foo.x` referenced as
            // bare `x` as a spurious `{x : _}` binder — the `open` has not been
            // processed yet at auto-bind time, so `x` looks free. Skipping the
            // sub-term keeps the common `theorem t : (open Foo in x) = 3` /
            // value-position `:= open scoped Classical in …` cases correct.
            SurfaceExpr::OpenIn { .. } => {}
            // Terminals and opaque nodes: no free variables to collect
            SurfaceExpr::Hole(_)
            | SurfaceExpr::NamedHole(_, _)
            | SurfaceExpr::Lit(_, _)
            | SurfaceExpr::SyntheticSorry(_)
            | SurfaceExpr::SyntaxQuote(_, _)
            | SurfaceExpr::QAntiquot { .. }
            | SurfaceExpr::ByTactic(_, _)
            | SurfaceExpr::CalcBlock(_, _)
            | SurfaceExpr::Do(_, _)
            | SurfaceExpr::LiftMethod(_, _)
            | SurfaceExpr::InterpolatedStr { .. } => {}
        }
    }

    /// Scan a type annotation for free variables (delegates to `collect_from_expr`).
    pub(crate) fn collect_from_type(&mut self, ty: &SurfaceExpr) {
        self.collect_from_expr(ty);
    }

    /// Return discovered auto-bound variables and universe variables (first-occurrence order).
    #[must_use]
    pub(crate) fn finish(self) -> (Vec<AutoBoundVar>, Vec<String>) {
        (self.found_vars, self.universe_vars)
    }

    /// Wrap a kernel expression with implicit Pi binders for auto-bound type/instance vars.
    /// Universe variables are skipped (they go into the declaration's universe param list).
    pub(crate) fn wrap_with_auto_bounds(expr: Expr, vars: &[AutoBoundVar]) -> Expr {
        let mut result = expr;
        // Wrap in reverse order so the first variable in the list is outermost
        for var in vars.iter().rev() {
            match &var.kind {
                AutoBoundKind::TypeVar { .. } => {
                    // Bind as `{name : Type}`
                    let ty = Expr::type_();
                    result = Expr::pi(var.binder_info, ty, result);
                }
                AutoBoundKind::InstanceVar { class_name } => {
                    // Bind as `[inst : ClassName]`
                    let ty = Expr::const_str(class_name);
                    result = Expr::pi(BinderInfo::InstImplicit, ty, result);
                }
                AutoBoundKind::UniverseVar => {
                    // Universe variables are not Pi binders -- they are added
                    // to the declaration's universe parameter list instead.
                }
            }
        }
        result
    }

    /// Append discovered universe parameters, skipping duplicates.
    pub(crate) fn add_universe_params(levels: &mut Vec<String>, univs: &[String]) {
        for u in univs {
            if !levels.contains(u) {
                levels.push(u.clone());
            }
        }
    }

    // ---- Private helpers ----

    /// Try to add a name as an auto-bound variable if it qualifies.
    fn try_add_name(&mut self, name: &str) {
        // Skip if already bound, already seen, or a standard name
        if self.bound_names.contains(name)
            || self.seen_names.contains(name)
            || is_standard_name(name)
        {
            return;
        }

        if is_universe_var_name(name) {
            if !self.seen_universes.contains(name) {
                self.seen_universes.insert(name.to_owned());
                self.universe_vars.push(name.to_owned());
                self.seen_names.insert(name.to_owned());
                self.found_vars.push(AutoBoundVar {
                    name: name.to_owned(),
                    kind: AutoBoundKind::UniverseVar,
                    binder_info: BinderInfo::Implicit,
                });
            }
        } else if is_type_var_name(name) {
            self.seen_names.insert(name.to_owned());
            self.found_vars.push(AutoBoundVar {
                name: name.to_owned(),
                kind: AutoBoundKind::TypeVar { universe: None },
                binder_info: BinderInfo::Implicit,
            });
        }
    }

    /// Collect from binders and body, temporarily adding binder names to scope.
    fn collect_from_binders_and_body(&mut self, binders: &[SurfaceBinder], body: &SurfaceExpr) {
        // First collect from binder types (they are in the outer scope)
        for binder in binders {
            if let Some(ty) = &binder.ty {
                self.collect_from_expr(ty);
            }
        }

        // Add binder names to scope for the body
        let mut added = Vec::new();
        for binder in binders {
            if binder.name != "_" && !self.bound_names.contains(&binder.name) {
                self.bound_names.insert(binder.name.clone());
                added.push(binder.name.clone());
            }
        }

        self.collect_from_expr(body);

        // Restore scope
        for name in &added {
            self.bound_names.remove(name);
        }
    }

    /// Collect from a let/let-rec binding: type, value, and scoped body.
    fn collect_from_let(&mut self, binder: &SurfaceBinder, val: &SurfaceExpr, body: &SurfaceExpr) {
        if let Some(ty) = &binder.ty {
            self.collect_from_expr(ty);
        }
        self.collect_from_expr(val);
        let was_bound = self.bound_names.contains(&binder.name);
        self.bound_names.insert(binder.name.clone());
        self.collect_from_expr(body);
        if !was_bound {
            self.bound_names.remove(&binder.name);
        }
    }

    /// Collect from a struct literal's type, base, and field values.
    fn collect_from_struct_lit(
        &mut self,
        struct_type: &Option<Box<SurfaceExpr>>,
        base: &Option<Box<SurfaceExpr>>,
        fields: &[clean_parser::SurfaceFieldAssign],
    ) {
        if let Some(st) = struct_type {
            self.collect_from_expr(st);
        }
        if let Some(b) = base {
            self.collect_from_expr(b);
        }
        for field in fields {
            self.collect_from_expr(&field.val);
        }
    }

    /// Collect universe variables from a universe expression.
    fn collect_from_universe(&mut self, univ: &UniverseExpr) {
        match univ {
            UniverseExpr::TypeLevel(level) | UniverseExpr::Sort(level) => {
                self.collect_from_level(level);
            }
            UniverseExpr::Prop
            | UniverseExpr::Type
            | UniverseExpr::TypeImplicit
            | UniverseExpr::SortImplicit
            | UniverseExpr::SortStar => {}
        }
    }

    /// Collect universe variables from a level expression.
    fn collect_from_level(&mut self, level: &LevelExpr) {
        match level {
            LevelExpr::Param(name) => {
                if !self.bound_names.contains(name) && !self.seen_universes.contains(name) {
                    self.seen_universes.insert(name.clone());
                    self.universe_vars.push(name.clone());
                    if !self.seen_names.contains(name) {
                        self.seen_names.insert(name.clone());
                        self.found_vars.push(AutoBoundVar {
                            name: name.clone(),
                            kind: AutoBoundKind::UniverseVar,
                            binder_info: BinderInfo::Implicit,
                        });
                    }
                }
            }
            LevelExpr::Succ(inner) => self.collect_from_level(inner),
            LevelExpr::Max(a, b) | LevelExpr::IMax(a, b) => {
                self.collect_from_level(a);
                self.collect_from_level(b);
            }
            LevelExpr::Lit(_) | LevelExpr::Antiquot(_) => {}
        }
    }
}

/// Heuristic: is this name a type variable?
///
/// In Lean 4, single Greek letters (α, β, γ, ...) and names starting with
/// a Greek letter are treated as auto-bound type variables.
///
/// # ENSURES
/// - Returns true for single Greek letters (α-ω, Α-Ω)
/// - Returns true for names starting with a lowercase Greek letter
/// - Returns false for standard names, universe-like names, and dotted names
#[must_use]
pub(crate) fn is_type_var_name(name: &str) -> bool {
    if name.is_empty() || name.contains('.') {
        return false;
    }

    let first_char = name.chars().next().unwrap_or('\0');

    // Greek lowercase: α (U+03B1) through ω (U+03C9)
    // Greek uppercase: Α (U+0391) through Ω (U+03A9)
    is_greek_letter(first_char)
}

/// Heuristic: is this a universe variable name (`u`, `v`, `w`, or `u_N`)?
#[must_use]
pub(crate) fn is_universe_var_name(name: &str) -> bool {
    if name.is_empty() {
        return false;
    }

    // Single letters u, v, w
    if name.len() == 1 {
        return matches!(name, "u" | "v" | "w");
    }

    // Pattern: u_N, v_N, w_N where N is one or more digits
    let bytes = name.as_bytes();
    if bytes.len() >= 3
        && matches!(bytes[0], b'u' | b'v' | b'w')
        && bytes[1] == b'_'
        && bytes[2..].iter().all(|b| b.is_ascii_digit())
    {
        return true;
    }

    false
}

/// Check whether a character is a Greek letter (U+0391..U+03A9 or U+03B1..U+03C9).
fn is_greek_letter(c: char) -> bool {
    matches!(c, '\u{0391}'..='\u{03A9}' | '\u{03B1}'..='\u{03C9}')
}

/// Check whether a name is a well-known standard type (Nat, Bool, etc.) or dotted.
fn is_standard_name(name: &str) -> bool {
    name.contains('.') || STANDARD_NAMES.contains(&name)
}

/// Build surface-level implicit binders for auto-bound type and instance variables.
/// Universe variables are skipped (they go into the declaration's universe param list).
#[must_use]
pub(crate) fn auto_bound_surface_binders(vars: &[AutoBoundVar]) -> Vec<SurfaceBinder> {
    vars.iter()
        .filter_map(|var| match &var.kind {
            AutoBoundKind::TypeVar { .. } => Some(SurfaceBinder::new(
                &var.name,
                Some(SurfaceExpr::type_()),
                SurfaceBinderInfo::Implicit,
            )),
            AutoBoundKind::InstanceVar { class_name } => Some(SurfaceBinder::new(
                &var.name,
                Some(SurfaceExpr::ident(class_name)),
                SurfaceBinderInfo::Instance,
            )),
            AutoBoundKind::UniverseVar => None,
        })
        .collect()
}

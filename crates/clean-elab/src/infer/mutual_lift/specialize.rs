// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructor specialization (design §5.3 step 6): after the major premise of
//! a pre-definition is replaced by a constructor applied to fresh fields, the
//! case splits on it become redexes. This folder contracts them:
//!
//! * β — `(fun x => b) a`;
//! * ι — `R.rec…/R.casesOn… (c params fields)` through the recursor's own rule
//!   (the kernel's `try_iota_reduction` rule application, restricted to a
//!   SYNTACTIC constructor application — no δ, no literal expansion, no eta);
//! * projection of a constructor application;
//! * ζ of a PURE alias `let y := x` (the equation compiler re-binds pattern
//!   variables from fields that way), so a recursive call's major argument is
//!   the field itself.
//!
//! Every step is a definitional-equality step of the kernel, and the result is
//! re-checked by the kernel when the lifted member registers, so this transform
//! is untrusted: a wrong reduct refuses the block, it cannot mint a constant.

use clean_kernel::inductive::RecursorArgOrder;
use clean_kernel::{Environment, Expr, ExprFolder, ExprKind, Name};

/// Upper bound on contractions per specialization. The inputs are elaborated
/// pre-definitions whose redexes are created by ONE constructor substitution,
/// so a run that hits it is a term this lowering does not expect: refused.
const MAX_STEPS: usize = 200_000;

pub(super) struct Specializer<'e> {
    env: &'e Environment,
    steps: usize,
}

impl<'e> Specializer<'e> {
    pub(super) fn new(env: &'e Environment) -> Self {
        Self { env, steps: 0 }
    }

    /// Contract every redex of `expr` described in the module docs. `None`
    /// when the step budget ran out.
    pub(super) fn run(&mut self, expr: &Expr) -> Option<Expr> {
        let out = self.fold_expr(expr);
        (self.steps <= MAX_STEPS).then_some(out)
    }

    fn exhausted(&self) -> bool {
        self.steps > MAX_STEPS
    }

    /// Head-reduce `head args` once its parts are already folded.
    fn reduce_spine(&mut self, head: Expr, args: Vec<Expr>) -> Expr {
        if self.exhausted() || args.is_empty() {
            return Expr::apps(head, args);
        }
        if head.is_lam() {
            let mut cur = head;
            let mut used = 0;
            while used < args.len() {
                let ExprKind::Lam(_, _, body) = cur.kind() else {
                    break;
                };
                cur = body.instantiate(&args[used]);
                used += 1;
            }
            self.steps += 1;
            let rebuilt = Expr::apps(cur, args[used..].iter().cloned());
            return self.fold_expr(&rebuilt);
        }
        if let ExprKind::Const(name, levels) = head.kind() {
            if let Some(reduct) = self
                .iota(name, levels, &args)
                .or_else(|| self.unfold_eliminator(name, levels, &args))
            {
                self.steps += 1;
                return self.fold_expr(&reduct);
            }
        }
        Expr::apps(head, args)
    }

    /// A `casesOn` / `recOn` that is a DEFINITION (Lean's `mkCasesOn`, or an
    /// imported one) rather than a mirrored recursor: δ-unfold it, β-reduce,
    /// and keep the result only if the recursor it exposes ι-reduces — an
    /// eliminator on a non-constructor stays folded.
    fn unfold_eliminator(
        &self,
        name: &Name,
        levels: &[clean_kernel::Level],
        args: &[Expr],
    ) -> Option<Expr> {
        let last = name.to_string();
        if !(last.ends_with(".casesOn") || last.ends_with(".recOn")) {
            return None;
        }
        let constant = self.env.get_const(name)?;
        let value = constant.value.as_ref()?;
        if constant.level_params.len() != levels.len() {
            return None;
        }
        let value = value.instantiate_level_params_direct(&constant.level_params, levels);
        let unfolded = head_beta(&Expr::apps(value, args.iter().cloned()));
        let ExprKind::Const(rec_name, rec_levels) = unfolded.get_app_fn().kind() else {
            return None;
        };
        let rec_args: Vec<Expr> = unfolded.get_app_args().into_iter().cloned().collect();
        self.iota(rec_name, rec_levels, &rec_args)
    }

    /// ι-reduce `name.{levels} args` when its major premise is syntactically a
    /// fully applied constructor that has a rule in this recursor.
    fn iota(&self, name: &Name, levels: &[clean_kernel::Level], args: &[Expr]) -> Option<Expr> {
        let rec = self.env.get_recursor(name)?;
        let np = rec.num_params as usize;
        let nm = rec.num_motives as usize;
        let nmin = rec.num_minors as usize;
        let ni = rec.num_indices as usize;
        let (major_idx, minors_start, extras_start) = match rec.arg_order {
            RecursorArgOrder::MajorAfterMinors => {
                (np + nm + nmin + ni, np + nm, np + nm + nmin + ni + 1)
            }
            RecursorArgOrder::MajorAfterMotive => {
                (np + nm + ni, np + nm + ni + 1, np + nm + ni + 1 + nmin)
            }
        };
        if args.len() < extras_start || levels.len() != rec.level_params.len() {
            return None;
        }
        let major = strip_mdata(&args[major_idx]);
        let ExprKind::Const(ctor_name, _) = major.get_app_fn().kind() else {
            return None;
        };
        let ctor = self.env.get_constructor(ctor_name)?;
        let rule = rec
            .rules
            .iter()
            .find(|rule| &rule.constructor_name == ctor_name)?;
        let major_args: Vec<Expr> = major.get_app_args().into_iter().cloned().collect();
        let nfields = rule.num_fields as usize;
        if nfields != ctor.num_fields as usize
            || major_args.len() != ctor.num_params as usize + nfields
            || !rule.rhs.is_lam()
        {
            return None;
        }
        let mut result = rule
            .rhs
            .instantiate_level_params_direct(&rec.level_params, levels);
        for arg in &args[..np + nm] {
            result = Expr::app(result, arg.clone());
        }
        for arg in &args[minors_start..minors_start + nmin] {
            result = Expr::app(result, arg.clone());
        }
        for field in &major_args[major_args.len() - nfields..] {
            result = Expr::app(result, field.clone());
        }
        for extra in &args[extras_start..] {
            result = Expr::app(result, extra.clone());
        }
        Some(result)
    }

    /// `Proj(S, i, c params fields)` ↦ field `i`, for a constructor of `S`.
    fn project(&self, struct_name: &Name, idx: u32, inner: &Expr) -> Option<Expr> {
        let inner = strip_mdata(inner);
        let ExprKind::Const(ctor_name, _) = inner.get_app_fn().kind() else {
            return None;
        };
        let ctor = self.env.get_constructor(ctor_name)?;
        if &ctor.inductive_name != struct_name {
            return None;
        }
        let args = inner.get_app_args();
        if args.len() != (ctor.num_params + ctor.num_fields) as usize {
            return None;
        }
        args.get(ctor.num_params as usize + idx as usize)
            .map(|field| (*field).clone())
    }
}

impl ExprFolder for Specializer<'_> {
    fn fold_app(&mut self, f: &Expr, a: &Expr) -> Expr {
        let whole = Expr::app(f.clone(), a.clone());
        let head = whole.get_app_fn().clone();
        let args: Vec<Expr> = whole.get_app_args().into_iter().cloned().collect();
        let head = self.fold_expr(&head);
        let args: Vec<Expr> = args.iter().map(|arg| self.fold_expr(arg)).collect();
        self.reduce_spine(head, args)
    }

    fn fold_let(&mut self, name: &Name, ty: &Expr, val: &Expr, body: &Expr, non_dep: bool) -> Expr {
        let val = self.fold_expr(val);
        if is_pure_alias(&val) && !self.exhausted() {
            self.steps += 1;
            return self.fold_expr(&body.instantiate(&val));
        }
        Expr::let_named(
            name.clone(),
            self.fold_expr(ty),
            val,
            self.fold_binder_body(body),
            non_dep,
        )
    }

    fn fold_proj(&mut self, struct_name: &Name, idx: u32, inner: &Expr) -> Expr {
        let inner = self.fold_expr(inner);
        match self.project(struct_name, idx, &inner) {
            Some(field) => {
                self.steps += 1;
                self.fold_expr(&field)
            }
            None => Expr::proj(struct_name.clone(), idx, inner),
        }
    }
}

/// Whether `expr` contains a recursor or `casesOn`/`recOn` application whose
/// major premise is the local `fvar` — a case split on it that the
/// specialization could not contract (equation synthesis splits such a field
/// into its constructor, as Lean's equation for `(_, c) :: fs` does).
pub(super) fn eliminates_fvar(env: &Environment, expr: &Expr, fvar: clean_kernel::FVarId) -> bool {
    struct Finder<'e> {
        env: &'e Environment,
        fvar: clean_kernel::FVarId,
        found: bool,
    }
    impl Finder<'_> {
        fn major_is_fvar(
            &self,
            name: &Name,
            levels: &[clean_kernel::Level],
            args: &[Expr],
        ) -> bool {
            if let Some(rec) = self.env.get_recursor(name) {
                let np = rec.num_params as usize;
                let nm = rec.num_motives as usize;
                let ni = rec.num_indices as usize;
                let major_idx = match rec.arg_order {
                    RecursorArgOrder::MajorAfterMinors => np + nm + rec.num_minors as usize + ni,
                    RecursorArgOrder::MajorAfterMotive => np + nm + ni,
                };
                return args.get(major_idx).is_some_and(|major| {
                    matches!(strip_mdata(major).kind(), ExprKind::FVar(id) if *id == self.fvar)
                });
            }
            let last = name.to_string();
            if !(last.ends_with(".casesOn") || last.ends_with(".recOn")) {
                return false;
            }
            let Some(constant) = self.env.get_const(name) else {
                return false;
            };
            let Some(value) = constant.value.as_ref() else {
                return false;
            };
            if constant.level_params.len() != levels.len() {
                return false;
            }
            let value = value.instantiate_level_params_direct(&constant.level_params, levels);
            let unfolded = head_beta(&Expr::apps(value, args.iter().cloned()));
            let ExprKind::Const(rec_name, rec_levels) = unfolded.get_app_fn().kind() else {
                return false;
            };
            if self.env.get_recursor(rec_name).is_none() {
                return false;
            }
            let rec_args: Vec<Expr> = unfolded.get_app_args().into_iter().cloned().collect();
            self.major_is_fvar(rec_name, rec_levels, &rec_args)
        }
    }
    impl ExprFolder for Finder<'_> {
        fn fold_app(&mut self, f: &Expr, a: &Expr) -> Expr {
            let whole = Expr::app(f.clone(), a.clone());
            if !self.found {
                if let ExprKind::Const(name, levels) = whole.get_app_fn().kind() {
                    let args: Vec<Expr> = whole.get_app_args().into_iter().cloned().collect();
                    if self.major_is_fvar(name, levels, &args) {
                        self.found = true;
                    }
                }
            }
            if !self.found {
                let _ = self.fold_expr(f);
                let _ = self.fold_expr(a);
            }
            whole
        }
    }
    let mut finder = Finder {
        env,
        fvar,
        found: false,
    };
    let _ = finder.fold_expr(expr);
    finder.found
}

pub(super) fn strip_mdata(expr: &Expr) -> &Expr {
    let mut cur = expr;
    while let ExprKind::MData(_, inner) = cur.kind() {
        cur = inner;
    }
    cur
}

/// A `let` value that is only another name for a variable or a projection of
/// one — duplicating it costs nothing and changes no evaluation order.
fn is_pure_alias(val: &Expr) -> bool {
    match strip_mdata(val).kind() {
        ExprKind::BVar(_) | ExprKind::FVar(_) | ExprKind::Const(..) | ExprKind::Lit(_) => true,
        ExprKind::Proj(_, _, inner) => is_pure_alias(inner),
        _ => false,
    }
}

/// Head-β of a type (`(fun t => B) a` ↦ `B[a]`), used on the binder types of
/// an instantiated recursor whose motives are lambdas.
pub(super) fn head_beta(expr: &Expr) -> Expr {
    let mut cur = expr.clone();
    loop {
        let head = cur.get_app_fn().clone();
        if !head.is_lam() || !cur.is_app() {
            return cur;
        }
        let args: Vec<Expr> = cur.get_app_args().into_iter().cloned().collect();
        let mut body = head;
        let mut used = 0;
        while used < args.len() {
            let ExprKind::Lam(_, _, inner) = body.kind() else {
                break;
            };
            body = inner.instantiate(&args[used]);
            used += 1;
        }
        cur = Expr::apps(body, args[used..].iter().cloned());
    }
}

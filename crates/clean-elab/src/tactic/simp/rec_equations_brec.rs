// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Equations for imported course-of-values definitions whose equation lemmas
//! have not been realized by Lean. Reduce the actual body, then recover named
//! recursive calls by matching its symbolic reduction. No equation is inferred
//! from a constructor or function name alone. The ordinary simp proof checker
//! verifies the resulting Eq.refl witnesses before using these equations.

use clean_kernel::{Environment, Expr, ExprKind, Level, Name, TransparencyMode, TypeChecker};

use super::{levels_are_declared, map_bvars, ConstantKind, ShiftSigma, Sigma};
use super::{SimpIndexMode, SimpLemma, EQUATION_PRIORITY};

pub(super) fn synthesize(env: &Environment, name: &Name) -> Option<Vec<SimpLemma>> {
    let decl = env.get_const(name)?;
    if !matches!(decl.kind, ConstantKind::Definition) {
        return None;
    }
    let value = decl.value.as_ref()?;
    if crate::infer::collect_level_params(&[value, &decl.type_])
        .iter()
        .any(|p| !decl.level_params.contains(p))
    {
        return None;
    }
    let mut body = value;
    let mut n = 0usize;
    while let ExprKind::Lam(_, _, inner) = body.kind() {
        n += 1;
        body = inner;
    }
    let ExprKind::Const(brec_name, levels) = body.get_app_fn().kind() else {
        return None;
    };
    let clean_kernel::name::NameInner::Str(parent, suffix) = brec_name.inner() else {
        return None;
    };
    if suffix.as_ref() != "brecOn" {
        return None;
    }
    let wrapper = env.get_const(brec_name)?;
    let ind = env.get_inductive(parent)?;
    if !matches!(wrapper.kind, ConstantKind::Definition)
        || !wrapper.is_reducible
        || wrapper.value.is_none()
        || wrapper.level_params.len() != levels.len()
        || ind.num_indices != 0
        || ind.all_names.len() != 1
        || ind.is_nested
        || ind.is_reflexive
        || !levels_are_declared(levels, &decl.level_params)
    {
        return None;
    }
    let rec_name = parent.as_ref().clone().str("rec");
    if env.get_recursor(&rec_name)?.inductive_name != **parent {
        return None;
    }
    let args = body.get_app_args();
    let major_at = ind.num_params as usize + 1;
    let binder = |e: &Expr| match e.kind() {
        ExprKind::BVar(i) if (*i as usize) < n => Some(*i),
        _ => None,
    };
    let major = binder(args.get(major_at)?)?;
    // The step function follows the major; function-valued motives are
    // applied to the remaining distinct arguments of the definition.
    args.get(major_at + 1)?;
    let mut variables = vec![major];
    for arg in &args[major_at + 2..] {
        let i = binder(arg)?;
        if variables.contains(&i) {
            return None;
        }
        variables.push(i);
    }
    if (0..major).any(|i| !variables.contains(&i)) {
        return None;
    }
    for arg in args[..major_at]
        .iter()
        .chain(std::iter::once(&args[major_at + 1]))
    {
        if variables.iter().any(|i| arg.has_loose_bvar(*i)) {
            return None;
        }
    }
    let definition_levels: Vec<_> = decl
        .level_params
        .iter()
        .cloned()
        .map(Level::param)
        .collect();
    let ctor_levels = levels
        .get(levels.len().checked_sub(ind.level_params.len())?..)?
        .to_vec();
    let mut result_type = &decl.type_;
    for _ in 0..n {
        let ExprKind::Pi(_, _, inner) = result_type.kind() else {
            return None;
        };
        result_type = inner;
    }
    let sort = super::sort_level_of_result_type(env, result_type, &decl.level_params)?;
    let mut f_app = Expr::const_(name.clone(), definition_levels.clone());
    for i in (0..n).rev() {
        f_app = Expr::app(f_app, Expr::bvar(i as u32));
    }
    if super::super::zeta_size::beta_zeta_size_reaches(body, super::BETA_NORMAL_MAX_NODES) {
        return None;
    }
    let mut tc = TypeChecker::new(env);
    tc.set_transparency(TransparencyMode::Instances);
    tc.set_honor_reducibility(true);
    tc.set_heartbeat_limit(10_000);
    let pattern = tc.whnf_with_transparency(body, TransparencyMode::Instances);
    // Require the actual wrapper to reach this family's registered recursor.
    // Otherwise the name was only a coincidental spelling.
    if !contains_constant(&pattern, &rec_name) || tc.heartbeat_spent() {
        return None;
    }
    let mut equations = Vec::new();
    for ctor_name in &ind.constructor_names {
        let ctor = env.get_constructor(ctor_name)?;
        if ctor.inductive_name != **parent {
            return None;
        }
        let k = ctor.num_fields;
        let shift = ShiftSigma { m: major, k };
        let mut constructor = Expr::const_(ctor_name.clone(), ctor_levels.clone());
        for arg in &args[..ind.num_params as usize] {
            constructor = Expr::app(constructor, shift.apply(arg, 0)?);
        }
        for field in (0..k).rev() {
            constructor = Expr::app(constructor, Expr::bvar(major + field));
        }
        let sigma = Sigma {
            shift,
            ctor_app: &constructor,
        };
        let lhs = sigma.apply(&f_app, 0)?;
        let eq_type = sigma.apply(result_type, 0)?;
        let raw = sigma.apply(body, 0)?;
        if super::super::zeta_size::beta_zeta_size_reaches(&raw, super::BETA_NORMAL_MAX_NODES) {
            return None;
        }
        let reduced = tc.whnf_with_transparency(&raw, TransparencyMode::Instances);
        let folder = Fold {
            pattern: &pattern,
            variables: &variables,
            fields: k,
            name,
            levels: &definition_levels,
            binders: n,
            rec_name: &rec_name,
        };
        // Do not fold the initial constructor application back into itself.
        let rhs = folder.reduce(&tc, &reduced, 0, 256)?;
        if rhs == lhs || tc.heartbeat_spent() || contains_constant(&rhs, &rec_name) {
            return None;
        }
        let proof = Expr::apps(
            Expr::const_str_levels("Eq.refl", vec![sort.clone()]),
            [eq_type.clone(), lhs.clone()],
        );
        equations.push(SimpLemma {
            name: name.clone(),
            lhs,
            rhs,
            eq_type: Some(eq_type),
            proof_expr: Some(proof),
            // Match the already-realized imported equation path. These
            // equations retain the imported function's head; offering every
            // constructor equation at every unrelated node wastes attempts.
            index_mode: SimpIndexMode::Normal,
            priority: EQUATION_PRIORITY,
        });
    }
    (!equations.is_empty()).then_some(equations)
}

fn contains_constant(expr: &Expr, name: &Name) -> bool {
    expr.collect_constants().contains(name)
}

struct Fold<'a> {
    pattern: &'a Expr,
    variables: &'a [u32],
    fields: u32,
    name: &'a Name,
    levels: &'a [Level],
    binders: usize,
    rec_name: &'a Name,
}

impl Fold<'_> {
    fn fixed(&self, index: u32, outer: u32) -> Option<Expr> {
        Some(Expr::bvar(
            index
                .checked_add(self.fields)?
                .checked_sub(1)?
                .checked_add(outer)?,
        ))
    }

    fn matches(
        &self,
        pattern: &Expr,
        target: &Expr,
        outer: u32,
        depth: u32,
        captures: &mut [Option<Expr>],
        fuel: usize,
    ) -> Option<()> {
        if fuel == 0 {
            return None;
        }
        if let ExprKind::BVar(index) = pattern.kind() {
            if *index < depth {
                return (pattern == target).then_some(());
            }
            let index = index - depth;
            if let Some(slot) = self.variables.iter().position(|i| *i == index) {
                // A captured argument cannot depend on an internal binder of
                // the symbolic carrier. Remove only that binder depth.
                let captured = map_bvars(target, 0, &|i, local| {
                    (i >= local + depth).then(|| Expr::bvar(i - depth))
                })?;
                if let Some(previous) = &captures[slot] {
                    return (previous == &captured).then_some(());
                }
                captures[slot] = Some(captured);
                return Some(());
            }
            return (self.fixed(index, outer + depth)? == *target).then_some(());
        }
        let recur = |a, b, d, c: &mut [Option<Expr>]| self.matches(a, b, outer, d, c, fuel - 1);
        match (pattern.kind(), target.kind()) {
            (ExprKind::App(f, a), ExprKind::App(g, b)) => {
                recur(f, g, depth, captures)?;
                recur(a, b, depth, captures)
            }
            (ExprKind::Lam(i, t, b), ExprKind::Lam(j, u, c))
            | (ExprKind::Pi(i, t, b), ExprKind::Pi(j, u, c))
                if i == j =>
            {
                recur(t, u, depth, captures)?;
                recur(b, c, depth + 1, captures)
            }
            (ExprKind::Proj(s, i, e), ExprKind::Proj(t, j, f)) if s == t && i == j => {
                recur(e, f, depth, captures)
            }
            _ => (pattern == target).then_some(()),
        }
    }

    fn fold(&self, expr: &Expr, outer: u32) -> Option<Expr> {
        let mut captures = vec![None; self.variables.len()];
        self.matches(self.pattern, expr, outer, 0, &mut captures, 256)?;
        let mut result = Expr::const_(self.name.clone(), self.levels.to_vec());
        for index in (0..self.binders as u32).rev() {
            let arg = if let Some(slot) = self.variables.iter().position(|i| *i == index) {
                captures[slot].clone()?
            } else {
                self.fixed(index, outer)?
            };
            result = Expr::app(result, arg);
        }
        Some(result)
    }

    fn reduce(&self, tc: &TypeChecker<'_>, expr: &Expr, outer: u32, fuel: usize) -> Option<Expr> {
        if fuel == 0
            || super::super::zeta_size::beta_zeta_size_reaches(expr, super::BETA_NORMAL_MAX_NODES)
        {
            return None;
        }
        // Constructor reduction is only needed along the carrier's path.
        // Leave ordinary operators and their arguments in their original
        // surface form, as Lean's generated equations do. Besides preserving
        // lemma heads, this avoids repeatedly normalizing unrelated terms.
        if !contains_constant(expr, self.rec_name) {
            return Some(expr.clone());
        }
        if let Some(folded) = self.fold(expr, outer) {
            return Some(folded);
        }
        let reduced = tc.whnf_with_transparency(expr, TransparencyMode::Instances);
        if tc.heartbeat_spent() {
            return None;
        }
        if let Some(folded) = self.fold(&reduced, outer) {
            return Some(folded);
        }
        let recur = |e, d| self.reduce(tc, e, d, fuel - 1);
        Some(match reduced.kind() {
            ExprKind::App(f, a) => Expr::app(recur(f, outer)?, recur(a, outer)?),
            ExprKind::Lam(i, t, b) => Expr::lam(*i, recur(t, outer)?, recur(b, outer + 1)?),
            ExprKind::Pi(i, t, b) => Expr::pi(*i, recur(t, outer)?, recur(b, outer + 1)?),
            ExprKind::Proj(s, i, e) => Expr::proj(s.clone(), *i, recur(e, outer)?),
            ExprKind::MData(m, e) => Expr::mdata(m.clone(), recur(e, outer)?),
            ExprKind::Const(n, _) if n == self.rec_name => return None,
            _ => reduced.clone(),
        })
    }
}

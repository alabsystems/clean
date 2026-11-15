// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `@[match_pattern]` definitions in patterns (G29, ledger (99)).
//!
//! Lean 4.8.0 reads a pattern identifier that resolves to a `@[match_pattern]`
//! global like a constructor (`CollectPatternVars.processId`,
//! `src/Lean/Elab/PatternVar.lean`) and the pattern elaborator unfolds the
//! definition until a constructor application, a literal or `n + k` remains.
//! So under `@[match_pattern] def two : Nat := 2`, `| two => true | _ => false`
//! tests the literal `2`. Clean used to read `two` as a fresh binder — a
//! catch-all — and `rfl` proved `isTwo 3 = true`, which Lean refuses.
//!
//! The unfolding here is the fragment that has one faithful pattern reading:
//! the definition's value is a λ-telescope whose body is built from its
//! explicit parameters (each used exactly once), constructor applications
//! whose fields are all explicit, `Nat` literals, `x + k` on `Nat` with a
//! literal `k`, and further `@[match_pattern]` applications. Anything else is
//! refused by name, never read as a binder.

use super::*;

/// How deep `@[match_pattern]` definitions may unfold into each other.
const MAX_MATCH_PATTERN_DEPTH: usize = 64;

impl<'a> ElabCtx<'a> {
    /// Refuse a `@[match_pattern]` definition whose declared result type does
    /// not unify with the scrutinee's: Lean elaborates the pattern `pr b`
    /// against the expected type first, so `pr : Nat → Option Nat` at an
    /// `Option Bool` scrutinee is "type mismatch", and a `Nat`-valued `n + 1`
    /// definition at an `Int` scrutinee is checked against `Int` (where Lean
    /// inserts a coercion Clean does not). Unfolding first read the value's
    /// constructor pattern against the scrutinee and accepted both, the second
    /// as an arm that never matches (review r6, X7; docs/DECISIONS.md R138).
    pub(in crate::infer) fn check_match_pattern_def_type(
        &mut self,
        owner: &Name,
        expected_type: &Expr,
    ) -> Result<(), ElabError> {
        let Some(info) = self.env.get_const(owner).cloned() else {
            return Err(unsupported(owner, "it is not a declared constant"));
        };
        let levels: Vec<Level> = info
            .level_params
            .iter()
            .map(|_| self.fresh_universe_param())
            .collect();
        let mut result_ty = info
            .type_
            .instantiate_level_params_direct(&info.level_params, &levels);
        loop {
            let current = result_ty.clone();
            let ExprKind::Pi(_, dom, body) = current.kind() else {
                break;
            };
            let arg = self.fresh_meta(dom.as_ref().clone());
            result_ty = body.instantiate(&arg);
        }
        let expected = self.metas.instantiate(expected_type);
        self.metas.push_scope();
        let unifies = self.try_unify(&result_ty, &expected);
        self.metas.pop_scope();
        if unifies {
            Ok(())
        } else {
            Err(ElabError::TypeMismatch {
                expected: crate::error_render::term(&expected),
                actual: format!(
                    "{} (the type of the `@[match_pattern]` definition `{owner}`)",
                    crate::error_render::term(&self.metas.instantiate(&result_ty))
                ),
            })
        }
    }

    /// The pattern `owner args…` denotes once the `@[match_pattern]`
    /// definition `owner` is unfolded. `args` are the patterns written for
    /// `owner`'s explicit parameters, in order.
    pub(in crate::infer) fn unfold_match_pattern_def(
        &mut self,
        owner: &Name,
        args: &[SurfacePattern],
    ) -> Result<SurfacePattern, ElabError> {
        self.unfold_match_pattern_at(owner, args, 0)
    }

    fn unfold_match_pattern_at(
        &mut self,
        owner: &Name,
        args: &[SurfacePattern],
        depth: usize,
    ) -> Result<SurfacePattern, ElabError> {
        if depth > MAX_MATCH_PATTERN_DEPTH {
            return Err(unsupported(
                owner,
                "its unfolding does not reach a constructor application",
            ));
        }
        let value = self
            .env
            .get_const(owner)
            .and_then(|info| info.value.clone())
            .ok_or_else(|| unsupported(owner, "it has no definition value to unfold"))?;
        // Peel the λ-telescope: `Some(i)` is the i-th explicit parameter,
        // `None` an implicit/instance one (no pattern is written for it).
        let mut slots: Vec<Option<usize>> = Vec::new();
        let mut explicit = 0usize;
        let mut body = &value;
        while let ExprKind::Lam(binder, _, inner) = body.kind() {
            if binder.info == BinderInfo::Default {
                slots.push(Some(explicit));
                explicit += 1;
            } else {
                slots.push(None);
            }
            body = inner;
        }
        if explicit != args.len() {
            return Err(unsupported(
                owner,
                &format!(
                    "it takes {explicit} explicit argument(s) and the pattern gives {}",
                    args.len()
                ),
            ));
        }
        let mut uses = vec![0usize; args.len()];
        let pattern = self.match_pattern_body(owner, body, &slots, args, &mut uses, depth)?;
        if uses.iter().any(|&count| count != 1) {
            return Err(unsupported(
                owner,
                "its value does not use each explicit parameter exactly once",
            ));
        }
        Ok(pattern)
    }

    /// Read the unfolded body `expr` (under the telescope `slots`) as a
    /// pattern.
    fn match_pattern_body(
        &mut self,
        owner: &Name,
        expr: &Expr,
        slots: &[Option<usize>],
        args: &[SurfacePattern],
        uses: &mut [usize],
        depth: usize,
    ) -> Result<SurfacePattern, ElabError> {
        let read = |this: &mut Self, e: &Expr, uses: &mut [usize]| {
            this.match_pattern_body(owner, e, slots, args, uses, depth)
        };
        match expr.kind() {
            ExprKind::MData(_, inner) => read(self, inner, uses),
            ExprKind::BVar(index) => {
                let slot = slots
                    .len()
                    .checked_sub(1 + *index as usize)
                    .and_then(|position| slots[position]);
                let Some(arg) = slot else {
                    return Err(unsupported(
                        owner,
                        "its value places an implicit parameter in a pattern position",
                    ));
                };
                uses[arg] += 1;
                Ok(args[arg].clone())
            }
            ExprKind::Lit(Literal::Nat(n)) => Ok(SurfacePattern::Lit(SurfaceLit::nat(n.clone()))),
            _ => {
                let ExprKind::Const(head, _) = expr.get_app_fn().kind() else {
                    return Err(unsupported(owner, NOT_A_PATTERN));
                };
                let spine: Vec<Expr> = expr.get_app_args().iter().map(|e| (*e).clone()).collect();
                if let Some(n) = nat_ofnat_literal(head, &spine) {
                    return Ok(SurfacePattern::Lit(SurfaceLit::nat(n)));
                }
                if let Some((lhs, k)) = nat_add_literal(head, &spine) {
                    let inner = read(self, &lhs, uses)?;
                    return Ok(SurfacePattern::NumeralAdd(Box::new(inner), k));
                }
                if let Some(ctor) = self.env.get_constructor(head).cloned() {
                    let params = ctor.num_params as usize;
                    let fields = ctor.num_fields as usize;
                    if spine.len() != params + fields {
                        return Err(unsupported(owner, NOT_A_PATTERN));
                    }
                    let infos = self.ctor_field_binder_infos(&ctor)?;
                    if infos.iter().any(|info| *info != BinderInfo::Default) {
                        return Err(unsupported(
                            owner,
                            &format!("constructor `{head}` has implicit fields"),
                        ));
                    }
                    let subs = spine[params..]
                        .iter()
                        .map(|field| read(self, field, uses))
                        .collect::<Result<Vec<_>, _>>()?;
                    return Ok(SurfacePattern::Ctor(
                        SurfaceName::from_name(head.clone()),
                        subs,
                    ));
                }
                if self.env.is_match_pattern(head) {
                    let inner_value = self
                        .env
                        .get_const(head)
                        .and_then(|info| info.value.clone())
                        .ok_or_else(|| unsupported(head, "it has no definition value to unfold"))?;
                    let mut infos = Vec::new();
                    let mut telescope = &inner_value;
                    while let ExprKind::Lam(binder, _, inner) = telescope.kind() {
                        infos.push(binder.info);
                        telescope = inner;
                    }
                    if infos.len() != spine.len() {
                        return Err(unsupported(owner, NOT_A_PATTERN));
                    }
                    let mut inner_args = Vec::new();
                    for (info, arg) in infos.iter().zip(&spine) {
                        if *info == BinderInfo::Default {
                            inner_args.push(read(self, arg, uses)?);
                        }
                    }
                    return self.unfold_match_pattern_at(head, &inner_args, depth + 1);
                }
                Err(unsupported(owner, NOT_A_PATTERN))
            }
        }
    }
}

const NOT_A_PATTERN: &str =
    "its value is not a constructor application, a `Nat` literal or `n + k` over its parameters";

fn unsupported(owner: &Name, why: &str) -> ElabError {
    ElabError::Unsupported {
        feature: format!(
            "`@[match_pattern]` definition `{owner}` in a pattern: {why}. Lean unfolds it to a \
             constructor pattern; Clean does not read it as a variable"
        ),
    }
}

/// `@OfNat.ofNat Nat (lit n) inst` — a `Nat` numeral.
fn nat_ofnat_literal(head: &Name, spine: &[Expr]) -> Option<BigNat> {
    if *head != Name::from_string("OfNat.ofNat") || spine.len() != 3 {
        return None;
    }
    if !is_nat_type(&spine[0]) {
        return None;
    }
    match spine[1].kind() {
        ExprKind::Lit(Literal::Nat(n)) => Some(n.clone()),
        _ => None,
    }
}

/// `@HAdd.hAdd Nat Nat Nat inst x k` (or `Nat.add x k`) with a numeral `k`.
fn nat_add_literal(head: &Name, spine: &[Expr]) -> Option<(Expr, u64)> {
    let (lhs, rhs) = if *head == Name::from_string("HAdd.hAdd") && spine.len() == 6 {
        if !spine[..3].iter().all(is_nat_type) {
            return None;
        }
        (&spine[4], &spine[5])
    } else if *head == Name::from_string("Nat.add") && spine.len() == 2 {
        (&spine[0], &spine[1])
    } else {
        return None;
    };
    let k = match rhs.kind() {
        ExprKind::Lit(Literal::Nat(n)) => n.to_u64()?,
        _ => {
            let ExprKind::Const(name, _) = rhs.get_app_fn().kind() else {
                return None;
            };
            let args: Vec<Expr> = rhs.get_app_args().iter().map(|e| (*e).clone()).collect();
            nat_ofnat_literal(name, &args)?.to_u64()?
        }
    };
    Some((lhs.clone(), k))
}

fn is_nat_type(ty: &Expr) -> bool {
    matches!(ty.kind(), ExprKind::Const(name, levels) if *name == Name::from_string("Nat") && levels.is_empty())
}

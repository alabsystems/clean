// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Proof search over the actual checked source conditional. In particular,
//! reifying an IR Bool choice as a UInt choice is not a source proof. Eliminate
//! the source's own Decidable instance and use checked Nat order reflection to
//! transport the independently supplied Bool choice in each constructor case.

use clean_kernel::{BinderInfo, Environment, Expr, ExprKind, FVarId, Level, Name};

use super::{bitwise, subtraction};
use crate::ScalarSort;

fn c(name: &str) -> Expr {
    Expr::const_str(name)
}
fn v(id: u64) -> Expr {
    Expr::fvar(FVarId::new(id))
}
fn lam(id: u64, ty: Expr, body: Expr) -> Expr {
    Expr::lam(BinderInfo::Default, ty, body.abstract_fvar(FVarId::new(id)))
}
fn eq(ty: Expr, a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [ty, a, b],
    )
}
fn refl(ty: Expr, at: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [ty, at],
    )
}
fn trans_at(ty: Expr, a: Expr, b: Expr, d: Expr, h: Expr, k: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.trans"),
            vec![Level::succ(Level::zero())],
        ),
        [ty, a, b, d, h, k],
    )
}
fn congr_nat_prop(f: Expr, a: Expr, b: Expr, h: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("congrArg"),
            vec![Level::succ(Level::zero()); 2],
        ),
        [c("Nat"), Expr::prop(), a, b, f, h],
    )
}
fn transport(name: &str, p: Expr, q: Expr, equality: Expr, proof: Expr) -> Expr {
    // p and q inhabit Prop = Sort 0. The equality itself is Eq.{1} Prop p q.
    Expr::apps(
        Expr::const_(Name::from_string(name), vec![Level::zero()]),
        [p, q, equality, proof],
    )
}
fn order(strict: bool, a: Expr, b: Expr) -> Expr {
    let a = if strict {
        Expr::app(c("Nat.succ"), a)
    } else {
        a
    };
    Expr::apps(c("Nat.le"), [a, b])
}
fn symm(ty: Expr, a: Expr, b: Expr, h: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.symm"),
            vec![Level::succ(Level::zero())],
        ),
        [ty, a, b, h],
    )
}
fn bool_rec(level: Level, motive: Expr, no: Expr, yes: Expr, at: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Bool.rec"), vec![level]),
        [motive, no, yes, at],
    )
}
fn choice(ty: Expr, no: Expr, yes: Expr, at: Expr) -> Expr {
    bool_rec(
        Level::succ(Level::zero()),
        Expr::lam(BinderInfo::Default, c("Bool"), ty),
        no,
        yes,
        at,
    )
}
fn args_of<'a>(
    term: &'a Expr,
    name: &str,
    levels: &[Level],
    count: usize,
) -> Option<Vec<&'a Expr>> {
    let term = term.strip_mdata();
    let ExprKind::Const(head, actual_levels) = term.get_app_fn().kind() else {
        return None;
    };
    if *head != Name::from_string(name) || actual_levels.as_slice() != levels {
        return None;
    }
    let args = term.get_app_args();
    (args.len() == count).then(|| args.into_vec())
}

struct Search<'a> {
    environment: &'a Environment,
    width: u32,
    result: ScalarSort,
    params: &'a [Expr],
    next: u64,
}

impl Search<'_> {
    fn fresh(&mut self) -> u64 {
        let id = self.next;
        self.next += 1;
        id
    }
    fn decode(&self, value: Expr) -> Expr {
        Expr::app(c(&format!("UInt{}.toNat", self.width)), value)
    }

    fn audit_under_params(&self, mut statement: Expr, candidate: &Expr) -> bool {
        let uint = c(&format!("UInt{}", self.width));
        let mut proof = candidate.clone();
        for param in self.params.iter().rev() {
            let ExprKind::FVar(id) = param.kind() else {
                return false;
            };
            statement = Expr::pi(
                BinderInfo::Default,
                uint.clone(),
                statement.abstract_fvar(*id),
            );
            proof = Expr::lam(BinderInfo::Default, uint.clone(), proof.abstract_fvar(*id));
        }
        self.environment
            .audit_certification(&statement, &proof)
            .is_certified()
    }

    fn leaf(&self, source_value: &Expr, rhs: &Expr) -> Option<Expr> {
        let lhs = self.decode(source_value.clone());
        // The actual source leaf, rather than the RHS's shape, determines
        // which proof works. Check conversion and each arithmetic candidate
        // independently under precisely the original UInt parameters.
        [
            Some(refl(c("Nat"), lhs.clone())),
            subtraction::candidate(self.width, self.params, rhs),
            bitwise::candidate(self.width, self.params, rhs),
        ]
        .into_iter()
        .flatten()
        .find(|candidate| {
            self.audit_under_params(eq(c("Nat"), lhs.clone(), rhs.clone()), candidate)
        })
    }

    fn result_leaf(&self, source_value: &Expr, rhs: &Expr) -> Option<Expr> {
        match self.result {
            ScalarSort::UInt(_) => self.leaf(source_value, rhs),
            ScalarSort::Bool => {
                let proof = refl(c("Bool"), source_value.clone());
                self.audit_under_params(eq(c("Bool"), source_value.clone(), rhs.clone()), &proof)
                    .then_some(proof)
            }
        }
    }

    /// Prove the EXACT original proposition equals the emitted Nat ordering.
    /// Syntax only selects operands; neither the LT/LE dictionary nor the
    /// direct UInt relation is assigned meaning by this matcher.
    fn order_equality(&mut self, p: &Expr, da: &Expr, db: &Expr, strict: bool) -> Option<Expr> {
        let q = order(strict, da.clone(), db.clone());
        let statement = eq(Expr::prop(), p.clone(), q.clone());
        let conversion = refl(Expr::prop(), p.clone());
        if self.audit_under_params(statement.clone(), &conversion) {
            return Some(conversion);
        }

        let uint = c(&format!("UInt{}", self.width));
        let operands = ["LT.lt", "LE.le"]
            .into_iter()
            .find_map(|method| {
                let args = args_of(p, method, &[Level::zero()], 4)?;
                // The class name selects operand positions, not the relation:
                // an LT dictionary can validly store UInt.le. The exact p=q
                // judgment below checks the actual field's meaning.
                (args[0] == &uint).then_some((args[2], args[3]))
            })
            .or_else(|| {
                ["lt", "le"].into_iter().find_map(|relation| {
                    let args = args_of(p, &format!("UInt{}.{}", self.width, relation), &[], 2)?;
                    Some((args[0], args[1]))
                })
            })?;
        let left = self.leaf(operands.0, da)?;
        let right = self.leaf(operands.1, db)?;
        let dl = self.decode(operands.0.clone());
        let dr = self.decode(operands.1.clone());
        let original_order = order(strict, dl.clone(), dr.clone());
        let middle = order(strict, da.clone(), dr.clone());
        let (x, y) = (self.fresh(), self.fresh());
        let first = congr_nat_prop(
            lam(x, c("Nat"), order(strict, v(x), dr.clone())),
            dl,
            da.clone(),
            left,
        );
        let second = congr_nat_prop(
            lam(y, c("Nat"), order(strict, da.clone(), v(y))),
            dr,
            db.clone(),
            right,
        );
        let equality = trans_at(Expr::prop(), original_order, middle, q, first, second);
        // In particular this must establish conversion from p, including its
        // actual dictionary, to original_order. A changed predicate/dictionary
        // is rejected here, before the full original-source judgment audit.
        self.audit_under_params(statement, &equality)
            .then_some(equality)
    }

    // Given the actual source hn : p -> False, prove cond = false. The true
    // Bool case is impossible: checked Nat.le_of_ble_eq_true would prove p.
    // The kernel must establish that p is precisely the reflected ordering;
    // no host-side interpretation of the source predicate is an assumption.
    fn false_comparison(&mut self, p: Expr, cond: Expr, a: Expr, b: Expr, hn: Expr) -> Expr {
        let (x, h) = (self.fresh(), self.fresh());
        let motive = lam(
            x,
            c("Bool"),
            Expr::arrow(
                eq(c("Bool"), cond.clone(), v(x)),
                eq(c("Bool"), v(x), c("Bool.false")),
            ),
        );
        let no = lam(
            h,
            eq(c("Bool"), cond.clone(), c("Bool.false")),
            refl(c("Bool"), c("Bool.false")),
        );
        let yes = lam(
            h,
            eq(c("Bool"), cond.clone(), c("Bool.true")),
            Expr::apps(
                Expr::const_(Name::from_string("absurd"), vec![Level::zero()]),
                [
                    p,
                    eq(c("Bool"), c("Bool.true"), c("Bool.false")),
                    Expr::apps(c("Nat.le_of_ble_eq_true"), [a, b, v(h)]),
                    hn,
                ],
            ),
        );
        Expr::app(
            bool_rec(Level::zero(), motive, no, yes, cond.clone()),
            refl(c("Bool"), cond),
        )
    }

    fn build(&mut self, source_value: &Expr, rhs: &Expr, depth: usize) -> Option<Expr> {
        if depth > 32 {
            return None;
        }
        let one = Level::succ(Level::zero());
        let carrier = self.result.source_type();
        let model = self.result.model_type();
        let Some(source) = args_of(source_value, "ite", std::slice::from_ref(&one), 5) else {
            return self.result_leaf(source_value, rhs);
        };
        if source[0] != &carrier {
            return None;
        }
        let den = args_of(rhs, "Bool.rec", &[one], 4)?;
        if den[0] != &Expr::lam(BinderInfo::Default, c("Bool"), model.clone()) {
            return None;
        }
        let (strict, da, db) = if let Some(args) = args_of(den[3], "Nat.blt", &[], 2) {
            (true, args[0].clone(), args[1].clone())
        } else {
            let args = args_of(den[3], "Nat.ble", &[], 2)?;
            (false, args[0].clone(), args[1].clone())
        };
        let p = source[1].clone();
        let q = order(strict, da.clone(), db.clone());
        let equality = self.order_equality(&p, &da, &db, strict)?;
        // Bool reflection is stated with Nat.le; blt reduces to ble (succ da) db.
        let a = if strict {
            Expr::app(c("Nat.succ"), da)
        } else {
            da
        };
        let b = db;
        let no_proof = self.build(source[4], den[1], depth + 1)?;
        let yes_proof = self.build(source[3], den[2], depth + 1)?;
        let (d, h, x) = (self.fresh(), self.fresh(), self.fresh());
        let dec_p = Expr::app(c("Decidable"), p.clone());
        let source_at = Expr::apps(
            Expr::const_(Name::from_string("ite"), vec![Level::succ(Level::zero())]),
            [
                carrier,
                p.clone(),
                v(d),
                source[3].clone(),
                source[4].clone(),
            ],
        );
        let motive = lam(
            d,
            dec_p,
            eq(model.clone(), self.result.image(source_at), rhs.clone()),
        );
        let choice_map = lam(
            x,
            c("Bool"),
            choice(model.clone(), den[1].clone(), den[2].clone(), v(x)),
        );
        let result_sort = self.result;
        let minor = |positive: bool, condition: Expr, leaf: Expr| {
            let (at, arm, source_arm) = if positive {
                (c("Bool.true"), den[2].clone(), source[3].clone())
            } else {
                (c("Bool.false"), den[1].clone(), source[4].clone())
            };
            let selected = Expr::apps(
                Expr::const_(
                    Name::from_string("congrArg"),
                    vec![Level::succ(Level::zero()); 2],
                ),
                [
                    c("Bool"),
                    model.clone(),
                    den[3].clone(),
                    at,
                    choice_map.clone(),
                    condition,
                ],
            );
            trans_at(
                model.clone(),
                result_sort.image(source_arm),
                arm.clone(),
                rhs.clone(),
                leaf,
                symm(model.clone(), rhs.clone(), arm, selected),
            )
        };
        let not_p = Expr::arrow(p.clone(), c("False"));
        let hq = self.fresh();
        let not_q = lam(
            hq,
            q.clone(),
            Expr::app(
                v(h),
                transport("Eq.mpr", p.clone(), q.clone(), equality.clone(), v(hq)),
            ),
        );
        let false_condition =
            self.false_comparison(q.clone(), den[3].clone(), a.clone(), b.clone(), not_q);
        let no = lam(h, not_p, minor(false, false_condition, no_proof));
        let positive = transport("Eq.mp", p.clone(), q, equality, v(h));
        let true_condition = Expr::apps(c("Nat.ble_eq_true_of_le"), [a, b, positive]);
        let yes = lam(h, p.clone(), minor(true, true_condition, yes_proof));
        Some(Expr::apps(
            Expr::const_(Name::from_string("Decidable.rec"), vec![Level::zero()]),
            [p, motive, no, yes, source[2].clone()],
        ))
    }
}

/// The caller supplies the actual declaration value, never a reified UInt
/// surrogate. Closed declaration inputs and root params 0..63 leave scratch
/// IDs >=300 disjoint from both inputs and existing arithmetic proof helpers.
pub(super) fn candidate(
    environment: &Environment,
    width: u32,
    params: &[Expr],
    original_body: &Expr,
    rhs: &Expr,
) -> Option<Expr> {
    candidate_result(
        environment,
        width,
        ScalarSort::UInt(width),
        params,
        original_body,
        rhs,
    )
}

pub(super) fn boolean_candidate(
    environment: &Environment,
    width: u32,
    params: &[Expr],
    original_body: &Expr,
    rhs: &Expr,
) -> Option<Expr> {
    candidate_result(
        environment,
        width,
        ScalarSort::Bool,
        params,
        original_body,
        rhs,
    )
}

fn candidate_result(
    environment: &Environment,
    width: u32,
    result: ScalarSort,
    params: &[Expr],
    original_body: &Expr,
    rhs: &Expr,
) -> Option<Expr> {
    if original_body.has_fvar_quick() || original_body.loose_bvar_range() != 0 {
        return None;
    }
    let mut body = original_body.clone();
    for param in params {
        let ExprKind::Lam(_, _, result) = body.strip_mdata().kind() else {
            return None;
        };
        body = result.instantiate(param);
    }
    args_of(&body, "ite", &[Level::succ(Level::zero())], 5)?;
    Search {
        environment,
        width,
        result,
        params,
        next: 300,
    }
    .build(&body, rhs, 0)
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod order_transport_tests;

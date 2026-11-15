// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The core `Decidable` instances Clean's built-in prelude lacks, assembled
//! the way Lean's instance search assembles them, then reduced the way Lean
//! reduces them.
//!
//! Lean synthesizes ONE instance for the whole proposition before anything is
//! reduced, every sub-instance with the binders above it free:
//!
//! * `∀ b : Bool, p b`: `Bool.instDecidableForallOfDecidablePred p inst`,
//!   whose `inst : DecidablePred p` is found for `p b` with `b` a variable. So
//!   instances for `p true` and `p false` alone do not give it, and a generic
//!   instance for `p b` is what every case reduces, even where a more
//!   specific instance exists for one case (pinned v4.30.0-rc2). It matches
//!   `inst true, inst false`, so the `true` case is reduced first.
//! * `p → q`: `forall_prop_decidable` (`[Decidable p] [∀ h, Decidable q]`),
//!   reduced `if hp : p then … else isTrue …`: the hypothesis first.
//! * an equation over a type with a derived `DecidableEq` (`Option`, `Prod`,
//!   …): the derived instance, its type parameters' instances found at the
//!   use site (a local `[DecidableEq Nat]` or a higher-priority user instance
//!   among them), each leaf compared by reducing its parameter's instance
//!   (`decide_lean/standins.rs`).
//!
//! [`synthesize`] builds that structure as a [`Plan`] (the instances resolved
//! where Clean has them, the stand-ins where it does not), opening each
//! `Bool` binder as a fresh local. [`evaluate`] then substitutes each case's
//! constructor and reduces, assembling a proof the kernel re-checks once.

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, FVarId, Level};
use clean_parser::SurfaceName;

use super::super::core::{Goal, LocalDecl, ProofState};
use super::{head_is, of_decide_eq_true_proof, reduce_instance, resolve_decidable, Reduction};

/// Most nested parts one synthesis opens.
const SYNTHESIS_FUEL: u32 = 64;

/// Most nested `Bool` binders evaluated: `N` binders evaluate `2^N` leaves.
const MAX_BOOL_BINDERS: usize = 12;

/// Lead-in of a false `∀` over `Bool`'s case assignment (the wording the
/// `eval_decide` ladder uses too).
const COUNTEREXAMPLE: &str = "counterexample (Bool binders, outermost first): ";

/// How Lean's instance search answers `Decidable prop` (see the module doc).
/// Every `prop` mentions the `Bool` locals of the enclosing
/// [`Plan::BoolForall`] nodes, free.
pub(super) enum Plan {
    /// An instance resolved for `prop`.
    Instance { prop: Expr, instance: Expr },
    /// `prop` is `∀ b : Bool, body b`; `body` was synthesized with `b` the
    /// fresh local `local`.
    BoolForall {
        prop: Expr,
        local: FVarId,
        body: Box<Plan>,
    },
    /// `prop` is the non-dependent `p → q`.
    Implication {
        prop: Expr,
        hypothesis: Box<Plan>,
        conclusion: Box<Plan>,
    },
    /// `prop` is an equation over a type Lean derives `DecidableEq` for and
    /// Clean's prelude has no instance of; `instances` are the type
    /// parameters' instances the derived one takes, global or local.
    Equation {
        prop: Expr,
        instances: Vec<super::standins::ParameterInstance>,
    },
}

impl Plan {
    /// Every instance term the plan reduces, with the `Bool` locals it opened.
    pub(super) fn instances(&self) -> (Vec<&Expr>, Vec<FVarId>) {
        let mut instances = Vec::new();
        let mut opened = Vec::new();
        let mut pending = vec![self];
        while let Some(plan) = pending.pop() {
            match plan {
                Plan::Instance { instance, .. } => instances.push(instance),
                Plan::BoolForall { local, body, .. } => {
                    opened.push(*local);
                    pending.push(body);
                }
                Plan::Implication {
                    hypothesis,
                    conclusion,
                    ..
                } => {
                    pending.push(hypothesis);
                    pending.push(conclusion);
                }
                Plan::Equation {
                    instances: parameters,
                    ..
                } => instances.extend(parameters.iter().map(|p| &p.instance)),
            }
        }
        (instances, opened)
    }
}

/// The stand-in for `Decidable prop` when no instance resolved for `prop`
/// itself (the caller searched): Lean's search through the core instance
/// Clean lacks, its sub-instances searched first; `None` when it fails
/// ("failed to synthesize").
pub(super) fn synthesize(state: &ProofState, goal: &Goal, prop: &Expr) -> Option<Plan> {
    let next_fvar = state
        .meta_scope_for_context(&goal.local_ctx)
        .iter()
        .map(|(_, fvar, _)| fvar.as_u64())
        .filter(|id| crate::unify::MetaState::from_fvar(FVarId::new(*id)).is_none())
        .map(|id| id.saturating_add(1))
        .fold(state.next_fvar, u64::max);
    Synthesis { state, next_fvar }.stand_in(goal, prop, SYNTHESIS_FUEL)
}

struct Synthesis<'s> {
    state: &'s ProofState,
    next_fvar: u64,
}

impl Synthesis<'_> {
    /// Lean's search for `Decidable prop`: an instance, else a stand-in.
    fn plan(&mut self, goal: &Goal, prop: &Expr, fuel: u32) -> Option<Plan> {
        if let Some(instance) = resolve_decidable(self.state, goal, prop) {
            return Some(Plan::Instance {
                prop: prop.clone(),
                instance,
            });
        }
        self.stand_in(goal, prop, fuel)
    }

    /// The core instance Clean's prelude lacks, for `prop`'s shape.
    fn stand_in(&mut self, goal: &Goal, prop: &Expr, fuel: u32) -> Option<Plan> {
        let fuel = fuel.checked_sub(1)?;
        if let ExprKind::Pi(_, domain, body) = prop.strip_mdata().kind() {
            let (domain, body): (&Expr, &Expr) = (domain, body);
            if is_bool(domain) {
                let local = FVarId::new(self.next_fvar);
                self.next_fvar += 1;
                let mut opened = goal.clone();
                opened.local_ctx.push(LocalDecl {
                    binder_info: Default::default(),
                    fvar: local,
                    name: SurfaceName::generated_path("b"),
                    ty: domain.clone(),
                    value: None,
                });
                let body = self.plan(&opened, &body.instantiate(&Expr::fvar(local)), fuel)?;
                return Some(Plan::BoolForall {
                    prop: prop.clone(),
                    local,
                    body: Box::new(body),
                });
            }
            if !body.has_loose_bvars() && is_proposition(self.state, goal, domain) {
                let hypothesis = self.plan(goal, domain, fuel)?;
                let conclusion = self.plan(goal, body, fuel)?;
                return Some(Plan::Implication {
                    prop: prop.clone(),
                    hypothesis: Box::new(hypothesis),
                    conclusion: Box::new(conclusion),
                });
            }
            return None;
        }
        let (ty, ..) = super::super::equality::match_equality(prop).ok()?;
        if !super::super::decide_eq::decidable_type_check(&ty) {
            return None;
        }
        Some(Plan::Equation {
            prop: prop.clone(),
            instances: super::standins::parameter_instances(self.state, goal, &ty),
        })
    }
}

fn is_bool(ty: &Expr) -> bool {
    matches!(ty.strip_mdata().kind(), ExprKind::Const(name, _) if name == &Name::from_string("Bool"))
}

/// `true` iff `ty : Prop`.
fn is_proposition(state: &ProofState, goal: &Goal, ty: &Expr) -> bool {
    state.infer_type(goal, ty).is_ok_and(
        |sort| matches!(state.whnf(goal, &sort).kind(), ExprKind::Sort(level) if level.is_zero()),
    )
}

/// What reducing a [`Plan`] established about its (closed) proposition.
pub(super) enum Verdict {
    /// A proof, assembled from kernel-checkable parts, not yet re-checked.
    Proved(Expr),
    /// The proposition is false; `refutation` proves its negation where
    /// Clean can build that term.
    False {
        refutation: Option<Expr>,
        why: String,
    },
    /// Reduction did not reach `isTrue` or `isFalse`.
    Stuck(String),
}

/// Reduce `plan` at `reduction` (the root's proposition closed: no `Bool`
/// local of the plan's is free in it).
pub(super) fn evaluate(
    state: &ProofState,
    goal: &Goal,
    plan: &Plan,
    reduction: Reduction,
) -> Verdict {
    eval(state, goal, plan, reduction, &mut Vec::new())
}

fn substitute(expr: &Expr, cases: &[(FVarId, Expr)]) -> Expr {
    cases.iter().fold(expr.clone(), |expr, (local, ctor)| {
        expr.subst_fvar(*local, ctor)
    })
}

fn bool_ctor(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn eval(
    state: &ProofState,
    goal: &Goal,
    plan: &Plan,
    reduction: Reduction,
    cases: &mut Vec<(FVarId, Expr)>,
) -> Verdict {
    crate::stack_safe(|| match plan {
        Plan::Instance { prop, instance } => eval_instance(
            state,
            goal,
            &substitute(prop, cases),
            &substitute(instance, cases),
            reduction,
        ),
        Plan::Equation { prop, instances } => {
            let instances: Vec<super::standins::ParameterInstance> = instances
                .iter()
                .map(|p| super::standins::ParameterInstance {
                    ty: substitute(&p.ty, cases),
                    instance: substitute(&p.instance, cases),
                })
                .collect();
            super::standins::decide_equation(
                state,
                goal,
                &substitute(prop, cases),
                &instances,
                reduction,
            )
        }
        Plan::BoolForall { prop, local, body } => {
            if cases.len() >= MAX_BOOL_BINDERS {
                return Verdict::Stuck(format!(
                    "more than {MAX_BOOL_BINDERS} nested `Bool` binders"
                ));
            }
            let prop = substitute(prop, cases);
            let ExprKind::Pi(binder, domain, open_body) = prop.strip_mdata().kind() else {
                return Verdict::Stuck("a `Bool` case split lost its binder".into());
            };
            // `Bool.instDecidableForallOfDecidablePred` matches `inst true,
            // inst false`: the `true` case is reduced first (Init/Data/Bool.lean).
            let mut proofs = Vec::with_capacity(2);
            for (ctor, label) in [("Bool.true", "true"), ("Bool.false", "false")] {
                cases.push((*local, bool_ctor(ctor)));
                let verdict = eval(state, goal, body, reduction, cases);
                cases.pop();
                match verdict {
                    Verdict::Proved(proof) => proofs.push(proof),
                    Verdict::False { refutation, why } => {
                        // `¬ body c` refutes `∀ b, body b`: `fun h => r (h c)`.
                        let refutation = refutation.map(|r| {
                            let applied = Expr::app(Expr::bvar(0), bool_ctor(ctor));
                            Expr::lam(BinderInfo::Default, prop.clone(), Expr::app(r, applied))
                        });
                        // Nested `Bool` binders extend one assignment list,
                        // outermost binder first.
                        let assignment = match why.strip_prefix(COUNTEREXAMPLE) {
                            Some(inner) => format!("{label}, {inner}"),
                            None => format!("{label}; {why}"),
                        };
                        return Verdict::False {
                            refutation,
                            why: format!("{COUNTEREXAMPLE}{assignment}"),
                        };
                    }
                    Verdict::Stuck(why) => {
                        return Verdict::Stuck(format!("the case `{label}`: {why}"));
                    }
                }
            }
            let (Some(proof_false), Some(proof_true)) = (proofs.pop(), proofs.pop()) else {
                return Verdict::Stuck("a `Bool` case has no proof".into());
            };
            let motive = Expr::lam(
                BinderInfo::Default,
                (**domain).clone(),
                (**open_body).clone(),
            );
            let split = Expr::apps(
                Expr::const_(Name::from_string("Bool.casesOn"), vec![Level::zero()]),
                [motive, Expr::bvar(0), proof_false, proof_true],
            );
            Verdict::Proved(Expr::lam(*binder, (**domain).clone(), split))
        }
        Plan::Implication {
            prop,
            hypothesis,
            conclusion,
        } => {
            let prop = substitute(prop, cases);
            let ExprKind::Pi(binder, hyp_ty, concl_ty) = prop.strip_mdata().kind() else {
                return Verdict::Stuck("an implication lost its arrow".into());
            };
            match eval(state, goal, hypothesis, reduction, cases) {
                Verdict::Proved(hp) => match eval(state, goal, conclusion, reduction, cases) {
                    // Closed proofs: they do not mention the new binder.
                    Verdict::Proved(hq) => {
                        Verdict::Proved(Expr::lam(*binder, (**hyp_ty).clone(), hq))
                    }
                    Verdict::False { refutation, why } => Verdict::False {
                        // `fun f => rq (f hp)`.
                        refutation: refutation.map(|rq| {
                            Expr::lam(
                                BinderInfo::Default,
                                prop.clone(),
                                Expr::app(rq, Expr::app(Expr::bvar(0), hp)),
                            )
                        }),
                        why: format!("the hypothesis holds but the conclusion is false: {why}"),
                    },
                    stuck @ Verdict::Stuck(_) => stuck,
                },
                Verdict::False {
                    refutation: Some(not_hyp),
                    ..
                } => {
                    // `fun h => False.elim (not_hyp h)`; the conclusion is
                    // never reduced (`… else isTrue …`).
                    let absurd = Expr::apps(
                        Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
                        [(**concl_ty).clone(), Expr::app(not_hyp, Expr::bvar(0))],
                    );
                    Verdict::Proved(Expr::lam(*binder, (**hyp_ty).clone(), absurd))
                }
                Verdict::False {
                    refutation: None, ..
                } => Verdict::Stuck(
                    "the hypothesis is false, but Clean has no refutation term for it".into(),
                ),
                stuck @ Verdict::Stuck(_) => stuck,
            }
        }
    })
}

/// Reduce a leaf's instance: `of_decide_eq_true` on `isTrue`, a refutation by
/// `of_decide_eq_false` on `isFalse`.
fn eval_instance(
    state: &ProofState,
    goal: &Goal,
    prop: &Expr,
    instance: &Expr,
    reduction: Reduction,
) -> Verdict {
    let shown = || crate::error_render::term(prop);
    let reduced = reduce_instance(state, goal, instance, reduction);
    if head_is(&reduced, "Decidable.isTrue") {
        return Verdict::Proved(of_decide_eq_true_proof(prop, instance));
    }
    if head_is(&reduced, "Decidable.isFalse") {
        return Verdict::False {
            refutation: of_decide_eq_false_proof(state, prop, instance),
            why: format!(
                "its `Decidable` instance reduced to `isFalse` for `{}`",
                shown()
            ),
        };
    }
    Verdict::Stuck(format!(
        "the `Decidable` instance of `{}` did not reduce to `isTrue` or `isFalse`; reduction \
         got stuck at `{}`",
        shown(),
        crate::error_render::term(&reduced)
    ))
}

/// `@of_decide_eq_false p s (@id (decide p = false) (@Eq.refl Bool false))`,
/// or `None` when the environment lacks `of_decide_eq_false`.
fn of_decide_eq_false_proof(state: &ProofState, prop: &Expr, instance: &Expr) -> Option<Expr> {
    let name = Name::from_string("of_decide_eq_false");
    state.env().get_const(&name)?;
    let one = Level::succ(Level::zero());
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    let bool_false = bool_ctor("Bool.false");
    let decided = Expr::apps(
        Expr::const_(Name::from_string("Decidable.decide"), vec![]),
        [prop.clone(), instance.clone()],
    );
    let decided_eq_false = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![one.clone()]),
        [bool_ty.clone(), decided, bool_false.clone()],
    );
    let refl = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![one]),
        [bool_ty, bool_false],
    );
    let hinted = Expr::apps(
        Expr::const_(Name::from_string("id"), vec![Level::zero()]),
        [decided_eq_false, refl],
    );
    Some(Expr::apps(
        Expr::const_(name, vec![]),
        [prop.clone(), instance.clone(), hinted],
    ))
}

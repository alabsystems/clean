// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The canonical value of Lean's `casesOn` for ONE member of a multi-motive
//! (mutual or nested) inductive family — the wrapper an imported
//! `T.casesOn` is authenticated against (trust-ir gap G33, ledger class
//! (103)).
//!
//! Lean's `mkCasesOn` gives each member its own single-motive eliminator. For
//! the nested `Lean.Json` (whose `Json.rec` has four motives: `Json`,
//! `Array Json`, the `RBNode` of fields and `List Json`), pinned Lean 4.8.0
//! prints (`#print Lean.Json.casesOn`, `pp.all`):
//!
//! ```text
//! fun {motive_1} t null bool num str arr obj =>
//!   @Lean.Json.rec.{u} motive_1 (fun t => PUnit.{u}) (fun t => PUnit.{u}) (fun t => PUnit.{u})
//!     null (fun b => bool b) … (fun elems elems_ih => arr elems) …
//!     (fun data data_ih => PUnit.unit.{u}) PUnit.unit.{u} (fun … => PUnit.unit.{u})
//!     PUnit.unit.{u} (fun … => PUnit.unit.{u}) t
//! ```
//!
//! — the selected member's motive in its own slot, every OTHER motive the
//! constant `PUnit.{u}` family, each of the member's own minors eta-adapted
//! (its induction hypotheses dropped, exactly as the single-motive wrapper
//! drops them), and every other minor the constant `PUnit.unit.{u}`. A mutual
//! block has the same shape (`B.casesOn` puts `motive_2` in slot 2 and
//! `fun t => PUnit` in slot 1). Until 2026-10-16 the authenticator walked the
//! single-motive `casesOn` telescope as if it took every motive, and refused
//! `Lean.Json.casesOn` ("telescope shorter than the recursor arity counts"),
//! so no `match` on an imported `Json` elaborated.
//!
//! Soundness: this only builds the term the imported value is compared with.
//! The caller still type-checks the canonical term AND the imported value
//! against the imported type and requires them to be definitionally equal, and
//! the primitive recursor is authenticated first, so nothing is admitted on
//! this module's word.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::Environment;
use crate::expr::{BinderInfo, Expr, ExprKind, FVarId};
use crate::inductive::RecursorVal;
use crate::level::Level;
use crate::name::Name;

/// A binder opened with a fresh local.
struct Opened {
    id: FVarId,
    fvar: Expr,
    info: BinderInfo,
    domain: Expr,
}

fn open_one(b: &mut EnvDeclBuilder, cur: &mut Expr, what: &str) -> Result<Opened, String> {
    let ExprKind::Pi(data, domain, body) = cur.kind() else {
        return Err(format!(
            "member casesOn wrapper: {what} telescope ends early"
        ));
    };
    let domain = domain.as_ref().clone();
    let info = data.info;
    let (id, fvar) = b.fresh_local(domain.clone());
    *cur = body.instantiate(&fvar);
    Ok(Opened {
        id,
        fvar,
        info,
        domain,
    })
}

/// `λ <telescope of ty> ⇒ body`, for a Pi type `ty`.
fn constant_over(parent: &EnvDeclBuilder, ty: &Expr, body: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let mut cur = ty.clone();
    let mut opened = Vec::new();
    while let Ok(o) = open_one(&mut b, &mut cur, "constant") {
        opened.push(o);
    }
    let mut value = body.clone();
    for o in opened.iter().rev() {
        value = b.mk_lam(o.id, o.info, o.domain.clone(), value);
    }
    b.finish_child(value)
}

/// The head of a Pi telescope's conclusion.
fn conclusion_head(ty: &Expr) -> &Expr {
    let mut cur = ty;
    while let ExprKind::Pi(_, _, body) = cur.kind() {
        cur = body;
    }
    let mut head = cur;
    while let ExprKind::App(f, _) = head.kind() {
        head = f;
    }
    head
}

impl Environment {
    /// Whether an imported `casesOn` of type `cases_ty` over the primitive
    /// recursor `rec` is Lean's MEMBER wrapper (one motive, the member's
    /// minors) rather than a block wrapper taking every motive and minor of
    /// the family — Clean's own shape, which a Clean-written `.olean` carries.
    /// Decided by the telescope's length: the block wrapper has exactly
    /// `params + motives + indices + 1 + minors` binders, and a member wrapper
    /// of a multi-motive family strictly fewer. Single-motive families have
    /// one shape.
    #[must_use]
    pub fn cases_on_is_member_shaped(cases_ty: &Expr, rec: &RecursorVal) -> bool {
        if rec.num_motives <= 1 {
            return false;
        }
        let block = rec.num_params as usize
            + rec.num_motives as usize
            + rec.num_indices as usize
            + 1
            + rec.num_minors as usize;
        let mut arity = 0usize;
        let mut cur = cases_ty;
        while let ExprKind::Pi(_, _, body) = cur.kind() {
            arity += 1;
            cur = body;
        }
        arity != block
    }

    /// Which motive each primitive-recursor minor premise concludes in: the
    /// conclusion of minor `i` is `motive_j …` for exactly one `j`.
    fn minor_motive_targets(rec: &RecursorVal) -> Result<Vec<usize>, String> {
        let mut b = EnvDeclBuilder::new();
        let mut cur = rec.type_.clone();
        for _ in 0..rec.num_params {
            open_one(&mut b, &mut cur, "recursor")?;
        }
        let motives: Vec<FVarId> = (0..rec.num_motives)
            .map(|_| open_one(&mut b, &mut cur, "recursor").map(|o| o.id))
            .collect::<Result<_, _>>()?;
        (0..rec.num_minors)
            .map(|i| {
                let minor = open_one(&mut b, &mut cur, "recursor")?;
                let head = conclusion_head(&minor.domain);
                match head.kind() {
                    ExprKind::FVar(id) => motives
                        .iter()
                        .position(|m| m == id)
                        .ok_or_else(|| format!("minor {i} concludes in no motive")),
                    _ => Err(format!("minor {i} concludes in no motive")),
                }
            })
            .collect()
    }

    /// Build Lean's member `casesOn` value (module doc) for the member whose
    /// motive is slot `member_motive` of `rec`. `cases_ty` is the imported
    /// `casesOn` type (params → motive → indices → major → own minors) and
    /// `minor_arities` the `(fields, recursive fields)` of every rec minor in
    /// global order.
    pub(crate) fn build_member_cases_on_value(
        &self,
        rec: &RecursorVal,
        level_params: &[Name],
        cases_ty: &Expr,
        member_motive: usize,
        minor_arities: &[(u32, u32)],
    ) -> Result<Expr, String> {
        if member_motive >= rec.num_motives as usize {
            return Err(format!(
                "member motive slot {member_motive} is outside `{}`'s {} motives",
                rec.name, rec.num_motives
            ));
        }
        let targets = Self::minor_motive_targets(rec)?;
        let own_count = targets.iter().filter(|&&t| t == member_motive).count();

        // ── The casesOn telescope ──
        let mut b = EnvDeclBuilder::new();
        let mut cur = cases_ty.clone();
        let params: Vec<Opened> = (0..rec.num_params)
            .map(|_| open_one(&mut b, &mut cur, "casesOn"))
            .collect::<Result<_, _>>()?;
        let motive = open_one(&mut b, &mut cur, "casesOn")?;
        let indices: Vec<Opened> = (0..rec.num_indices)
            .map(|_| open_one(&mut b, &mut cur, "casesOn"))
            .collect::<Result<_, _>>()?;
        let major = open_one(&mut b, &mut cur, "casesOn")?;
        let own_minors: Vec<Opened> = (0..own_count)
            .map(|_| open_one(&mut b, &mut cur, "casesOn"))
            .collect::<Result<_, _>>()?;

        // The motive universe: the selected motive's codomain sort.
        let mut motive_codomain = motive.domain.clone();
        while let ExprKind::Pi(_, _, body) = motive_codomain.kind() {
            motive_codomain = body.as_ref().clone();
        }
        let ExprKind::Sort(u) = motive_codomain.kind() else {
            return Err("the casesOn motive does not land in a sort".to_string());
        };
        let punit = Expr::const_(Name::from_string("PUnit"), vec![u.clone()]);
        let punit_unit = Expr::const_(Name::from_string("PUnit.unit"), vec![u.clone()]);

        // ── The recursor application ──
        let rec_levels: Vec<Level> = level_params.iter().cloned().map(Level::param).collect();
        let mut app = Expr::const_(rec.name.clone(), rec_levels);
        let mut rcur = rec.type_.clone();
        for p in &params {
            let ExprKind::Pi(_, _, body) = rcur.kind() else {
                return Err("recursor telescope shorter than its parameters".to_string());
            };
            rcur = body.instantiate(&p.fvar);
            app = Expr::app(app, p.fvar.clone());
        }
        for j in 0..rec.num_motives as usize {
            let ExprKind::Pi(_, domain, body) = rcur.kind() else {
                return Err("recursor telescope shorter than its motives".to_string());
            };
            let term = if j == member_motive {
                motive.fvar.clone()
            } else {
                constant_over(&b, domain, &punit)
            };
            rcur = body.instantiate(&term);
            app = Expr::app(app, term);
        }
        let mut own = own_minors.iter();
        for (i, target) in targets.iter().enumerate() {
            let ExprKind::Pi(_, domain, body) = rcur.kind() else {
                return Err("recursor telescope shorter than its minors".to_string());
            };
            let term = if *target == member_motive {
                let aux = own
                    .next()
                    .ok_or_else(|| "fewer casesOn minors than member minors".to_string())?;
                let (fields, ihs) = minor_arities
                    .get(i)
                    .copied()
                    .ok_or_else(|| format!("no arity for minor {i}"))?;
                let mut cb = EnvDeclBuilder::child_of(&b);
                let mut mcur = domain.as_ref().clone();
                let bound: Vec<Opened> = (0..fields + ihs)
                    .map(|_| open_one(&mut cb, &mut mcur, "minor"))
                    .collect::<Result<_, _>>()?;
                let mut body = aux.fvar.clone();
                for o in bound.iter().take(fields as usize) {
                    body = Expr::app(body, o.fvar.clone());
                }
                for o in bound.iter().rev() {
                    body = cb.mk_lam(o.id, o.info, o.domain.clone(), body);
                }
                cb.finish_child(body)
            } else {
                constant_over(&b, domain, &punit_unit)
            };
            rcur = body.instantiate(&term);
            app = Expr::app(app, term);
        }
        if own.next().is_some() {
            return Err("more casesOn minors than member minors".to_string());
        }
        for idx in &indices {
            app = Expr::app(app, idx.fvar.clone());
        }
        app = Expr::app(app, major.fvar.clone());

        // ── Close the casesOn telescope ──
        let mut value = app;
        for o in own_minors.iter().rev() {
            value = b.mk_lam(o.id, o.info, o.domain.clone(), value);
        }
        value = b.mk_lam(major.id, major.info, major.domain.clone(), value);
        for o in indices.iter().rev() {
            value = b.mk_lam(o.id, o.info, o.domain.clone(), value);
        }
        value = b.mk_lam(motive.id, motive.info, motive.domain.clone(), value);
        for o in params.iter().rev() {
            value = b.mk_lam(o.id, o.info, o.domain.clone(), value);
        }
        Ok(b.finish(value))
    }
}

#[cfg(test)]
mod tests {
    use crate::env::decl_builder::EnvDeclBuilder;
    use crate::env::{Constructor, Declaration, Environment, InductiveDecl, InductiveType};
    use crate::expr::{BinderInfo, Expr};
    use crate::level::Level;
    use crate::name::Name;

    fn n(s: &str) -> Name {
        Name::from_string(s)
    }

    fn c(s: &str) -> Expr {
        Expr::const_(n(s), vec![])
    }

    /// `(fields, recursive fields)` of every minor of `rec`, in the global
    /// order: the family members' own `.rec` rules, then the restored nested
    /// companions `<first>.rec_1`, … (as `recursor_minor_rules` reads them).
    fn global_arities(env: &Environment, members: &[&str], rec: &str) -> Vec<(u32, u32)> {
        let wanted = env.get_recursor(&n(rec)).expect("rec").num_minors as usize;
        let mut rules = Vec::new();
        for member in members {
            rules.extend(
                env.get_recursor(&n(member).str("rec"))
                    .expect("member rec")
                    .rules
                    .iter()
                    .cloned(),
            );
        }
        let mut idx = 1;
        while rules.len() < wanted {
            let companion = n(members[0]).str(format!("rec_{idx}"));
            rules.extend(
                env.get_recursor(&companion)
                    .expect("companion rec")
                    .rules
                    .iter()
                    .cloned(),
            );
            idx += 1;
        }
        rules
            .iter()
            .map(|r| {
                let ihs = u32::try_from(r.recursive_fields.iter().filter(|f| **f).count())
                    .expect("small");
                (r.num_fields, ihs)
            })
            .collect()
    }

    /// Lean's member `casesOn` type: `{motive : T → Sort u} → (t : T) →
    /// (fields → motive (C fields))… → motive t`, for a 0-parameter `T`
    /// whose constructors are `(name, field types)`.
    fn member_cases_type(ty: &str, ctors: &[(&str, Vec<Expr>)], u: &Level) -> Expr {
        let t_ty = c(ty);
        let motive_ty = Expr::pi(BinderInfo::Default, t_ty.clone(), Expr::sort(u.clone()));
        let mut b = EnvDeclBuilder::new();
        let (m_id, m) = b.fresh_local(motive_ty.clone());
        let (t_id, t) = b.fresh_local(t_ty.clone());
        let mut minors = Vec::new();
        for (ctor, fields) in ctors {
            let mut cb = EnvDeclBuilder::child_of(&b);
            let opened: Vec<_> = fields.iter().map(|f| cb.fresh_local(f.clone())).collect();
            let app = Expr::apps(c(ctor), opened.iter().map(|(_, fv)| fv.clone()));
            let mut minor = Expr::app(m.clone(), app);
            for ((id, _), f) in opened.iter().zip(fields).rev() {
                minor = cb.mk_pi(*id, BinderInfo::Default, f.clone(), minor);
            }
            let minor = cb.finish_child(minor);
            let (id, _) = b.fresh_local(minor.clone());
            minors.push((id, minor));
        }
        let mut r = Expr::app(m, t);
        for (id, minor) in minors.into_iter().rev() {
            r = b.mk_pi(id, BinderInfo::Default, minor, r);
        }
        r = b.mk_pi(t_id, BinderInfo::Default, t_ty, r);
        r = b.mk_pi(m_id, BinderInfo::Implicit, motive_ty, r);
        b.finish(r)
    }

    /// Declare `name := value : ty` over `rec`'s universe parameters, and a
    /// same-typed AXIOM-valued forgery `name_forged`.
    fn declare_member_cases(env: &mut Environment, name: &str, rec: &str, ty: Expr, slot: usize) {
        let rec_val = env.get_recursor(&n(rec)).cloned().expect("rec");
        let members: Vec<String> = env
            .get_inductive(&rec_val.inductive_name)
            .expect("member")
            .all_names
            .iter()
            .map(ToString::to_string)
            .collect();
        let member_refs: Vec<&str> = members.iter().map(String::as_str).collect();
        let arities = global_arities(env, &member_refs, rec);
        let value = env
            .build_member_cases_on_value(&rec_val, &rec_val.level_params, &ty, slot, &arities)
            .expect("canonical member casesOn value");
        env.add_decl(Declaration::Definition {
            name: n(name),
            level_params: rec_val.level_params.clone(),
            type_: ty.clone(),
            value,
            is_reducible: true,
        })
        .expect("the canonical member casesOn kernel-checks");
        let levels: Vec<Level> = rec_val
            .level_params
            .iter()
            .cloned()
            .map(Level::param)
            .collect();
        env.add_decl(Declaration::Axiom {
            name: n(&format!("{name}_axiom")),
            level_params: rec_val.level_params.clone(),
            type_: ty.clone(),
        })
        .expect("same-typed axiom");
        env.add_decl(Declaration::Definition {
            name: n(&format!("{name}_forged")),
            level_params: rec_val.level_params.clone(),
            type_: ty,
            value: Expr::const_(n(&format!("{name}_axiom")), levels),
            is_reducible: true,
        })
        .expect("same-typed forgery registers");
    }

    fn authenticate(env: &Environment, cases: &str, rec: &str) -> Result<(), String> {
        let rec_val = env.get_recursor(&n(rec)).expect("rec");
        let members: Vec<String> = env
            .get_inductive(&rec_val.inductive_name)
            .expect("member")
            .all_names
            .iter()
            .map(ToString::to_string)
            .collect();
        let member_refs: Vec<&str> = members.iter().map(String::as_str).collect();
        let arities = global_arities(env, &member_refs, rec);
        env.authenticate_cases_on_wrapper_readonly(&n(cases), &n(rec), &arities)
    }

    /// G33: a nested family (`Tr` holding `List Tr`, two motives) — Lean's
    /// single-motive `Tr.casesOn` authenticates, and a same-typed forgery
    /// does not.
    #[test]
    fn test_member_cases_on_of_nested_family_authenticates_and_forgery_is_refused() {
        let mut env = Environment::with_prelude();
        let tr = c("Tr");
        let list_tr = Expr::app(Expr::const_(n("List"), vec![Level::zero()]), tr.clone());
        env.add_inductive(InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: n("Tr"),
                type_: Expr::sort(Level::succ(Level::zero())),
                constructors: vec![
                    Constructor {
                        name: n("Tr.leaf"),
                        type_: tr.clone(),
                    },
                    Constructor {
                        name: n("Tr.node"),
                        type_: Expr::pi(BinderInfo::Default, list_tr.clone(), tr.clone()),
                    },
                ],
            }],
        })
        .expect("nested Tr");
        let rec = env.get_recursor(&n("Tr.rec")).cloned().expect("Tr.rec");
        assert!(
            rec.num_motives >= 2,
            "Tr.rec is multi-motive: {}",
            rec.num_motives
        );
        let u = Level::param(rec.level_params[0].clone());
        let ty = member_cases_type("Tr", &[("Tr.leaf", vec![]), ("Tr.node", vec![list_tr])], &u);
        declare_member_cases(&mut env, "Tr.casesOnLean", "Tr.rec", ty, 0);
        authenticate(&env, "Tr.casesOnLean", "Tr.rec")
            .expect("Lean's member casesOn authenticates");
        let error = authenticate(&env, "Tr.casesOnLean_forged", "Tr.rec")
            .expect_err("a same-typed forgery must be refused");
        assert!(error.contains("not definitionally equal"), "{error}");
    }

    /// G33: the SECOND member of a mutual block uses motive slot 2 (Lean's
    /// `B.casesOn` takes `motive_2`), and its forgery is refused.
    #[test]
    fn test_member_cases_on_of_second_mutual_member_authenticates() {
        let mut env = Environment::with_prelude();
        let (a, b) = (c("A"), c("B"));
        let type0 = Expr::sort(Level::succ(Level::zero()));
        env.add_inductive(InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![
                InductiveType {
                    name: n("A"),
                    type_: type0.clone(),
                    constructors: vec![
                        Constructor {
                            name: n("A.a0"),
                            type_: a.clone(),
                        },
                        Constructor {
                            name: n("A.a1"),
                            type_: Expr::pi(BinderInfo::Default, b.clone(), a.clone()),
                        },
                    ],
                },
                InductiveType {
                    name: n("B"),
                    type_: type0,
                    constructors: vec![Constructor {
                        name: n("B.b0"),
                        type_: Expr::pi(
                            BinderInfo::Default,
                            a.clone(),
                            Expr::pi(BinderInfo::Default, c("Nat"), b.clone()),
                        ),
                    }],
                },
            ],
        })
        .expect("mutual A B");
        let rec = env.get_recursor(&n("B.rec")).cloned().expect("B.rec");
        assert_eq!(rec.num_motives, 2);
        let u = Level::param(rec.level_params[0].clone());
        let ty = member_cases_type("B", &[("B.b0", vec![a, c("Nat")])], &u);
        declare_member_cases(&mut env, "B.casesOnLean", "B.rec", ty, 1);
        authenticate(&env, "B.casesOnLean", "B.rec").expect("B's member casesOn authenticates");
        let error = authenticate(&env, "B.casesOnLean_forged", "B.rec")
            .expect_err("a same-typed forgery must be refused");
        assert!(error.contains("not definitionally equal"), "{error}");
    }
}

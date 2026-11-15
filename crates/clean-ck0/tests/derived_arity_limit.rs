// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Regression (Trust verified lane, 2026-10-02): the `u32` header counts that
//! size a vector up front — `InductiveDecl::num_level_params` in recursor
//! derivation (single and mutual) and `IotaRule::num_fields` in structure-η
//! ι-reduction — are bounded by `recursor::MAX_DERIVED_ARITY`. Before the bound
//! a forged count of `u32::MAX` asked for tens of GB and aborted the process;
//! now admission is a typed `AdmitError::Derivation` and ι-reduction leaves the
//! term stuck (both fail-closed). Real declarations are unaffected.

use clean_ck0::rawexpr::BinderInfo;
use clean_ck0::recursor::{IotaRule, MAX_DERIVED_ARITY};
use clean_ck0::validate::{ConstDef, ConstructorArity, QuotKind, RecursorShape, StructureInfo};
use clean_ck0::{
    add_inductive, add_inductive_mutual, AdmitError, Budget, Constructor, Env, InductiveDecl,
    MinimalEnv, MutualBlock, Name, RawExpr, RawLevel, Term,
};

fn n(s: &str) -> Name {
    Name::from_dotted(s)
}
fn r_sort1() -> RawExpr {
    RawExpr::Sort(RawLevel::Succ(Box::new(RawLevel::Zero)))
}
fn r_const(name: &str) -> RawExpr {
    RawExpr::Const(n(name), vec![])
}
fn r_app(f: RawExpr, a: RawExpr) -> RawExpr {
    RawExpr::App(Box::new(f), Box::new(a))
}
fn r_pi(dom: RawExpr, codom: RawExpr) -> RawExpr {
    RawExpr::Pi(BinderInfo::Default, Box::new(dom), Box::new(codom))
}
fn r_lam(dom: RawExpr, body: RawExpr) -> RawExpr {
    RawExpr::Lam(BinderInfo::Default, Box::new(dom), Box::new(body))
}
fn boot(decls: &[&str]) -> MinimalEnv {
    let mut env = MinimalEnv::new();
    for nm in decls {
        env = env.with_const(n(nm), 0);
    }
    env
}
fn v(env: &dyn Env, raw: &RawExpr) -> Term {
    Term::validate(env, raw, 0, 0).expect("term validates")
}

/// `Unit : Type` with `Unit.unit : Unit`, at a chosen level-param count. No
/// constructor has a field, so nothing before recursor derivation consults the
/// count (the field-sort universe check has nothing to infer).
fn unit_decl(num_level_params: u32) -> InductiveDecl {
    let b = boot(&["Unit", "Unit.unit"]);
    InductiveDecl {
        name: n("Unit"),
        num_level_params,
        num_params: 0,
        type_: v(&b, &r_sort1()),
        constructors: vec![Constructor {
            name: n("Unit.unit"),
            type_: v(&b, &r_const("Unit")),
        }],
    }
}

fn assert_too_many_level_params(r: Result<(), AdmitError>) {
    match r {
        Err(AdmitError::Derivation { detail, .. }) => assert!(
            detail.contains("too many universe level params"),
            "unexpected detail: {detail}"
        ),
        other => panic!("expected a too-many-level-params Derivation reject, got {other:?}"),
    }
}

#[test]
fn single_inductive_with_forged_level_param_count_is_rejected_not_allocated() {
    for count in [MAX_DERIVED_ARITY.saturating_add(1), u32::MAX] {
        let mut env = MinimalEnv::new();
        assert_too_many_level_params(add_inductive(&mut env, unit_decl(count)).map(|_| ()));
    }
}

#[test]
fn single_inductive_control_is_admitted() {
    // The same fixture at its consistent count (its terms use no level
    // params) is admitted, so the reject above is the count and nothing else.
    let mut env = MinimalEnv::new();
    add_inductive(&mut env, unit_decl(0)).expect("ordinary declaration admitted");
}

/// A two-type block `A`, `B` with field-less constructors `A.mk : A`,
/// `B.mk : B`, every decl at `num_level_params`.
fn ab_block(num_level_params: u32) -> MutualBlock {
    let b = boot(&["A", "B", "A.mk", "B.mk"]);
    let decl = |name: &str, ctor: &str| InductiveDecl {
        name: n(name),
        num_level_params,
        num_params: 0,
        type_: v(&b, &r_sort1()),
        constructors: vec![Constructor {
            name: n(ctor),
            type_: v(&b, &r_const(name)),
        }],
    };
    MutualBlock {
        decls: vec![decl("A", "A.mk"), decl("B", "B.mk")],
    }
}

#[test]
fn mutual_block_with_forged_level_param_count_is_rejected_not_allocated() {
    let mut env = MinimalEnv::new();
    add_inductive_mutual(&mut env, ab_block(0)).expect("ordinary block admitted");
    for count in [MAX_DERIVED_ARITY.saturating_add(1), u32::MAX] {
        let mut env = MinimalEnv::new();
        assert_too_many_level_params(add_inductive_mutual(&mut env, ab_block(count)).map(|_| ()));
    }
}

/// Delegates to a `MinimalEnv`, but reports every ι-rule with a forged
/// `num_fields` past the limit.
struct ForgedFieldCount(MinimalEnv);

impl Env for ForgedFieldCount {
    fn num_level_params(&self, name: &Name) -> Option<u32> {
        self.0.num_level_params(name)
    }
    fn inductive_large_elim(&self, name: &Name) -> Option<bool> {
        self.0.inductive_large_elim(name)
    }
    fn const_def(&self, name: &Name) -> Option<ConstDef> {
        self.0.const_def(name)
    }
    fn const_type(&self, name: &Name) -> Option<Term> {
        self.0.const_type(name)
    }
    fn quot_kind(&self, name: &Name) -> Option<QuotKind> {
        self.0.quot_kind(name)
    }
    fn is_recursor(&self, name: &Name) -> bool {
        self.0.is_recursor(name)
    }
    fn recursor_inductive(&self, name: &Name) -> Option<Name> {
        self.0.recursor_inductive(name)
    }
    fn constructor_arity(&self, name: &Name) -> Option<ConstructorArity> {
        self.0.constructor_arity(name)
    }
    fn structure_info(&self, name: &Name) -> Option<StructureInfo> {
        self.0.structure_info(name)
    }
    fn recursor_type(&self, name: &Name) -> Option<Term> {
        self.0.recursor_type(name)
    }
    fn recursor_rules(&self, name: &Name) -> Option<Vec<IotaRule>> {
        self.0.recursor_rules(name).map(|rules| {
            rules
                .into_iter()
                .map(|mut r| {
                    r.num_fields = MAX_DERIVED_ARITY.saturating_add(1);
                    r
                })
                .collect()
        })
    }
    fn recursor_shape(&self, name: &Name) -> Option<RecursorShape> {
        self.0.recursor_shape(name)
    }
    fn inductive_num_params(&self, name: &Name) -> Option<u32> {
        self.0.inductive_num_params(name)
    }
    fn inductive_constructors(&self, name: &Name) -> Option<Vec<(Name, Term)>> {
        self.0.inductive_constructors(name)
    }
}

#[test]
fn structure_eta_iota_with_forged_field_count_stays_stuck() {
    // `Cell : Type := mk (n : Nat)` and `Outer : Type := mk (c : Cell)`, both
    // η-structures, and an opaque `o : Outer`. The major premise `o.0 : Cell`
    // is a neutral projection, so only structure-η ι can fire on it.
    let mut env = MinimalEnv::new();
    let nat_ty = v(&MinimalEnv::new(), &r_sort1());
    env = env.with_const_typed(n("Nat"), 0, nat_ty);
    let b = boot(&["Nat", "Cell", "Cell.mk", "Outer", "Outer.mk"]);
    let structure = |name: &str, ctor: &str, field: &str| InductiveDecl {
        name: n(name),
        num_level_params: 0,
        num_params: 0,
        type_: v(&b, &r_sort1()),
        constructors: vec![Constructor {
            name: n(ctor),
            type_: v(&b, &r_pi(r_const(field), r_const(name))),
        }],
    };
    add_inductive(&mut env, structure("Cell", "Cell.mk", "Nat")).expect("Cell admitted");
    add_inductive(&mut env, structure("Outer", "Outer.mk", "Cell")).expect("Outer admitted");
    assert!(
        env.structure_info(&n("Cell")).is_some(),
        "Cell is an η-structure"
    );
    let outer_ty = v(&env, &r_const("Outer"));
    env = env.with_const_typed(n("o"), 0, outer_ty);

    // Cell.rec (motive := λ _ : Cell. Nat) (λ a : Nat. a) o.0
    let rec_app = r_app(
        r_app(
            r_app(
                RawExpr::Elim(n("Cell"), RawLevel::Succ(Box::new(RawLevel::Zero)), vec![]),
                r_lam(r_const("Cell"), r_const("Nat")),
            ),
            r_lam(r_const("Nat"), RawExpr::BVar(0)),
        ),
        RawExpr::Proj(n("Outer"), 0, Box::new(r_const("o"))),
    );
    let t = Term::validate_closed(&env, &rec_app).expect("validates");

    // Control: the genuine rule fires structure-η ι, giving `o.0.0`.
    let expected = Term::validate_closed(
        &env,
        &RawExpr::Proj(
            n("Cell"),
            0,
            Box::new(RawExpr::Proj(n("Outer"), 0, Box::new(r_const("o")))),
        ),
    )
    .expect("validates");
    let mut budget = Budget::default_budget();
    let reduced = clean_ck0::whnf(&env, &t, &mut budget).expect("whnf");
    assert_eq!(reduced, expected, "structure-η ι fires on the genuine rule");

    // Forged field count: the recursor is left stuck, nothing is expanded.
    let forged = ForgedFieldCount(env);
    let mut budget = Budget::default_budget();
    let stuck = clean_ck0::whnf(&forged, &t, &mut budget).expect("whnf");
    assert_eq!(stuck, t, "a forged field count leaves the recursor stuck");
}

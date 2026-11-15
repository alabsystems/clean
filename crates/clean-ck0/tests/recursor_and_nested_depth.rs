// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Derived recursors and nested auxiliaries are held to the depth bound as
//! they are built (`docs/DECISIONS.md` R166).
//!
//! * An ι rule binds every parameter, motive and minor premise and its
//!   constructor's fields, so a recursor whose widest rule cannot fit is
//!   refused before anything is built; otherwise the recursor type's minor
//!   premises and every rule would be built first, quadratic in the fields.
//! * A recursive field's induction hypothesis applies every minor again, so a
//!   rule can be about twice the telescope deep: the type and each rule are
//!   checked as they are built, stopping at the first past the bound.
//! * The mutual path makes the same checks for the whole block.
//! * A nested inductive's auxiliary is built from the container's constructor
//!   types and the occurrence's arguments, up to about twice the bound, and
//!   admission walks it natively: it is checked as it is built.
//!
//! Lean admits every refused input here; each refusal is fail-closed and
//! pinned, and fails the day its gap closes.

use clean_ck0::rawexpr::BinderInfo;
use clean_ck0::{
    add_inductive, add_inductive_mutual, add_inductive_nested, AdmitError, Constructor,
    InductiveDecl, MinimalEnv, MutualBlock, Name, NestedError, RawExpr, RawLevel, Term,
};

fn n(s: &str) -> Name {
    Name::from_dotted(s)
}

fn r_const(s: &str) -> RawExpr {
    RawExpr::Const(n(s), vec![])
}

fn r_pi(dom: RawExpr, codom: RawExpr) -> RawExpr {
    RawExpr::Pi(BinderInfo::Default, Box::new(dom), Box::new(codom))
}

fn r_app(f: RawExpr, a: RawExpr) -> RawExpr {
    RawExpr::App(Box::new(f), Box::new(a))
}

fn r_sort(succs: u32) -> RawExpr {
    let mut l = RawLevel::Zero;
    for _ in 0..succs {
        l = RawLevel::Succ(Box::new(l));
    }
    RawExpr::Sort(l)
}

/// `count` binders `Π (_ : Prop)` over `body`.
fn props_to(count: u32, body: RawExpr) -> RawExpr {
    let mut t = body;
    for _ in 0..count {
        t = r_pi(r_sort(0), t);
    }
    t
}

/// An env that knows `names` as level-free constants, to validate decls in.
fn boot(names: &[&str]) -> MinimalEnv {
    names
        .iter()
        .fold(MinimalEnv::new(), |env, nm| env.with_const(n(nm), 0))
}

fn closed(env: &MinimalEnv, raw: &RawExpr) -> Term {
    Term::validate_closed(env, raw).expect("the decl's terms validate")
}

/// Run `f` on a thread with an 8 MiB stack, the size of the main thread's on
/// this platform, so the measurement does not depend on the caller's thread.
fn on_main_sized_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(8 * 1024 * 1024)
        .spawn(f)
        .expect("thread spawns")
        .join()
        .expect("the decision returns rather than unwinding")
}

/// The detail of a derivation refusal, or the outcome when there is none.
fn derivation_detail(outcome: Result<(), AdmitError>) -> Result<String, String> {
    match outcome {
        Err(AdmitError::Derivation { detail, .. }) => Ok(detail),
        other => Err(format!("{other:?}")),
    }
}

/// `owner : ty` with `count` constructors `owner.c<i> : ctor_ty`, the first
/// replaced by `first` when given.
fn decl(owner: &str, ty: Term, count: usize, ctor_ty: &Term, first: Option<Term>) -> InductiveDecl {
    let constructors = (0..count)
        .map(|i| Constructor {
            name: n(&format!("{owner}.c{i}")),
            type_: match (&first, i) {
                (Some(t), 0) => t.clone(),
                _ => ctor_ty.clone(),
            },
        })
        .collect();
    InductiveDecl {
        name: n(owner),
        num_level_params: 0,
        num_params: 0,
        type_: ty,
        constructors,
    }
}

/// `T : Type` with `T.c0 : T → T` and `width - 1` nullary constructors.
fn recursive_enum(width: usize) -> InductiveDecl {
    let b = boot(&["T"]);
    let t = closed(&b, &r_const("T"));
    let succ = closed(&b, &r_pi(r_const("T"), r_const("T")));
    decl("T", closed(&b, &r_sort(1)), width, &t, Some(succ))
}

#[test]
fn test_recursive_enum_control_400_constructors_admits() {
    let outcome = on_main_sized_stack(|| {
        add_inductive(&mut MinimalEnv::new(), recursive_enum(400)).map_err(|e| e.to_string())
    });
    assert_eq!(outcome, Ok(()), "a rule 806 deep fits");
}

/// The telescope is 512 binders and the type about 514 deep, but `T.c0`'s
/// rule applies all 510 minors again in its induction hypothesis: 1,026 deep.
#[test]
fn test_recursive_enum_whose_rule_passes_the_bound_is_refused_where_lean_admits_it() {
    let detail = on_main_sized_stack(|| {
        derivation_detail(add_inductive(&mut MinimalEnv::new(), recursive_enum(510)))
    })
    .expect("refused as a derivation error");
    assert!(
        detail.contains("a derived recursor term has depth 1026"),
        "refused by the rule's depth: {detail}"
    );
}

/// `P : Prop` with 1,000 constructors `P → … → P` of 1,000 fields. Built, its
/// rules would hold about 2×10^9 nodes; the rule width refuses it first.
#[test]
fn test_wide_recursive_constructors_are_refused_before_their_rules_are_built() {
    let detail = on_main_sized_stack(|| {
        let b = boot(&["P"]);
        let mut ctor = r_const("P");
        for _ in 0..1000 {
            ctor = r_pi(r_const("P"), ctor);
        }
        let ctor = closed(&b, &ctor);
        let p = decl("P", closed(&b, &r_sort(0)), 1000, &ctor, None);
        derivation_detail(add_inductive(&mut MinimalEnv::new(), p))
    })
    .expect("refused as a derivation error");
    assert!(
        detail.contains("a constructor's ι rule binds 2001 variables"),
        "refused before the rules are built: {detail}"
    );
}

/// `S : Type` with one constructor of `fields` fields `(_ : Prop)`. Its rule
/// binds the motive, the minor and every field and applies the minor to every
/// field, and its type's minor premise is as deep: about `2·fields` either way.
fn wide_structure(fields: u32) -> Result<String, String> {
    on_main_sized_stack(move || {
        let b = boot(&["S"]);
        let ctor = closed(&b, &props_to(fields, r_const("S")));
        let s = decl("S", closed(&b, &r_sort(1)), 1, &ctor, None);
        derivation_detail(add_inductive(&mut MinimalEnv::new(), s))
    })
}

#[test]
fn test_wide_structure_control_510_fields_admits() {
    assert_eq!(
        wide_structure(510),
        Err("Ok(())".to_string()),
        "510 fields fit"
    );
}

#[test]
fn test_wide_structure_of_511_fields_is_refused_where_lean_admits_it() {
    let detail = wide_structure(511).expect("refused as a derivation error");
    assert!(
        detail.contains("a derived recursor term has depth 1026"),
        "refused by a derived term's depth: {detail}"
    );
}

/// A block `A, B : ty`, `a` and `b` constructors of type `ctor(owner)`, `A`'s
/// first replaced by `first` when given.
fn block(
    ty: &RawExpr,
    a: usize,
    b: usize,
    ctor: impl Fn(&str) -> RawExpr,
    first: Option<RawExpr>,
) -> MutualBlock {
    let env = boot(&["A", "B"]);
    let ty = closed(&env, ty);
    let first = first.map(|f| closed(&env, &f));
    MutualBlock {
        decls: vec![
            decl("A", ty.clone(), a, &closed(&env, &ctor("A")), first),
            decl("B", ty, b, &closed(&env, &ctor("B")), None),
        ],
    }
}

fn admit_block(block: MutualBlock) -> Result<String, String> {
    on_main_sized_stack(|| derivation_detail(add_inductive_mutual(&mut MinimalEnv::new(), block)))
}

#[test]
fn test_mutual_block_control_two_types_of_400_admits() {
    let block = block(&r_sort(1), 400, 400, r_const, None);
    let outcome = on_main_sized_stack(|| {
        add_inductive_mutual(&mut MinimalEnv::new(), block).map_err(|e| e.to_string())
    });
    assert_eq!(outcome, Ok(()), "rules of 802 variables fit");
}

/// Every rule binds both motives and all 1,022 minors: 1,024 variables.
#[test]
fn test_mutual_block_whose_rules_cannot_fit_is_refused_where_lean_admits_it() {
    let detail = admit_block(block(&r_sort(1), 511, 511, r_const, None))
        .expect("refused as a derivation error");
    assert!(
        detail.contains("a constructor's ι rule binds 1024 variables"),
        "refused by the block's rule width: {detail}"
    );
}

/// `A : Type → Type`, `B : Type → Type`, every constructor `X Prop`: the rules
/// bind 1,023 variables, but each recursor's telescope also binds the index
/// and the major premise, 1,025 binders.
#[test]
fn test_mutual_block_whose_telescope_cannot_fit_is_refused_where_lean_admits_it() {
    let family = r_pi(r_sort(1), r_sort(1));
    let detail = admit_block(block(
        &family,
        510,
        511,
        |o| r_app(r_const(o), r_sort(0)),
        None,
    ))
    .expect("refused as a derivation error");
    assert!(
        detail.contains("the recursor's telescope has 1025 binders"),
        "refused by the target's telescope width: {detail}"
    );
}

/// `A.c0 : A → A`: its rule applies both motives and all 510 minors again.
#[test]
fn test_mutual_block_whose_rule_passes_the_bound_is_refused_where_lean_admits_it() {
    let succ = r_pi(r_const("A"), r_const("A"));
    let detail = admit_block(block(&r_sort(1), 255, 255, r_const, Some(succ)))
        .expect("refused as a derivation error");
    assert!(
        detail.contains("a derived recursor term has depth")
            && detail.contains("past the depth bound"),
        "refused by a derived term's depth: {detail}"
    );
}

/// `W : Type → Type` with `W.mk : {a : Type} → (Prop → … → a) → W a` (`k`
/// arrows), and `T : Type` with `T.mk : W (Prop → … → T) → T` (`k` arrows):
/// the auxiliary for `W T'`'s constructor has a field about `2k` deep.
fn nested_admission(k: u32) -> Result<(), NestedError> {
    let wb = boot(&["W", "W.mk"]);
    let w_ty = closed(&wb, &r_pi(r_sort(1), r_sort(1)));
    // Under `a` and the `k` binders of `f`'s domain, `a` is BVar(k); under `a`
    // and `f`, BVar(1).
    let mk = r_pi(
        r_sort(1),
        r_pi(
            props_to(k, RawExpr::BVar(k)),
            r_app(r_const("W"), RawExpr::BVar(1)),
        ),
    );
    let w = InductiveDecl {
        name: n("W"),
        num_level_params: 0,
        num_params: 1,
        type_: w_ty,
        constructors: vec![Constructor {
            name: n("W.mk"),
            type_: closed(&wb, &mk),
        }],
    };
    let mut env = MinimalEnv::new();
    add_inductive(&mut env, w).expect("the container admits");
    let tb = boot(&["T", "T.mk", "W"]);
    let field = r_app(r_const("W"), props_to(k, r_const("T")));
    let t = InductiveDecl {
        name: n("T"),
        num_level_params: 0,
        num_params: 0,
        type_: closed(&tb, &r_sort(1)),
        constructors: vec![Constructor {
            name: n("T.mk"),
            type_: closed(&tb, &r_pi(field, r_const("T"))),
        }],
    };
    add_inductive_nested(&mut env, t)
}

#[test]
fn test_nested_auxiliary_control_100_arrows_admits() {
    let outcome = on_main_sized_stack(|| nested_admission(100).map_err(|e| e.to_string()));
    assert_eq!(outcome, Ok(()));
}

#[test]
fn test_nested_auxiliary_past_the_depth_bound_is_refused_where_lean_admits_it() {
    let outcome = on_main_sized_stack(|| match nested_admission(990) {
        Err(NestedError::Aux {
            source: AdmitError::Derivation { detail, .. },
            ..
        }) => Ok(detail),
        other => Err(format!("{other:?}")),
    });
    let detail = outcome.expect("refused while the auxiliary is built");
    assert!(
        detail.contains("an auxiliary term has depth") && detail.contains("past the depth bound"),
        "refused by the auxiliary's depth: {detail}"
    );
}

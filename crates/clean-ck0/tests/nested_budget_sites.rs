// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Each site that charges a nested inductive's `MAX_AUX_SIZE` refuses on its
//! own and says where (`docs/DECISIONS.md` R174, R176). R172 charges a parent
//! constructor before phase 3 rewrites it, an auxiliary type and each
//! auxiliary constructor before they are built; its tests reached only the
//! last (`level_geq_and_nested_size.rs`). Matching a site with an
//! occurrence, in phase 3 and in each auxiliary constructor's rewrite, is
//! charged what it does, before it does it (R176): each node lowering builds
//! and each pair of nodes a comparison looks at. Both parts are pinned here
//! at each matching site, and the unit tests in `src/nested_replace/tests.rs`
//! pin the amounts. The figures below are from the Python model in the R176
//! review, which reproduces R174's published counts.

use clean_ck0::rawexpr::BinderInfo;
use clean_ck0::{
    add_inductive, add_inductive_nested, AdmitError, Constructor, InductiveDecl, MinimalEnv, Name,
    NestedError, RawExpr, RawLevel, Term, MAX_AUX_SIZE,
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

fn r_type() -> RawExpr {
    RawExpr::Sort(RawLevel::Succ(Box::new(RawLevel::Zero)))
}

fn r_prop() -> RawExpr {
    RawExpr::Sort(RawLevel::Zero)
}

/// A `Type` of `2^height` leaves `Prop`, joined by `G : Type → Type → Type`:
/// `2^(height + 2) - 3` nodes.
fn g_tree(height: u32) -> RawExpr {
    g_tree_of(height, &r_prop())
}

/// [`g_tree`] with leaves `leaf`.
fn g_tree_of(height: u32, leaf: &RawExpr) -> RawExpr {
    match height.checked_sub(1) {
        None => leaf.clone(),
        Some(h) => r_app(r_app(r_const("G"), g_tree_of(h, leaf)), g_tree_of(h, leaf)),
    }
}

/// The parameter `A` of `T (A : Type)`, as a leaf `j` binders inside it.
fn a_leaf(j: u32) -> RawExpr {
    RawExpr::BVar(j)
}

/// The refusal at the matching charge in constructor `c`.
fn matching_in(c: &str) -> String {
    past_the_budget_at(&format!(
        "the nodes built and compared to match nested sites in `{c}`"
    ))
}

fn g_env() -> MinimalEnv {
    let g_ty = Term::validate_closed(
        &MinimalEnv::new(),
        &r_pi(r_type(), r_pi(r_type(), r_type())),
    )
    .expect("G's type");
    MinimalEnv::new().with_const_typed(n("G"), 0, g_ty)
}

/// The detail of a nested refusal made while building the block, or the
/// outcome when there is none.
fn nested_detail(
    env: MinimalEnv,
    containers: Vec<InductiveDecl>,
    t: InductiveDecl,
) -> Result<String, String> {
    std::thread::Builder::new()
        .stack_size(8 * 1024 * 1024)
        .spawn(move || {
            let mut env = env;
            for c in containers {
                add_inductive(&mut env, c).expect("the container admits");
            }
            match add_inductive_nested(&mut env, t) {
                Err(NestedError::Aux {
                    source: AdmitError::Derivation { detail, .. },
                    ..
                }) => Ok(detail),
                other => Err(format!("{other:?}")),
            }
        })
        .expect("thread spawns")
        .join()
        .expect("the decision returns rather than unwinding")
}

fn past_the_budget_at(site: &str) -> String {
    format!("could build more than {MAX_AUX_SIZE} term nodes, past the budget at {site}")
}

/// `X (α : Type) : Type` with `X.c0 : (α : Type) → α → X α`.
fn one_use(name: &str) -> InductiveDecl {
    let own = MinimalEnv::new().with_const(n(name), 0);
    let ctor = r_pi(
        r_type(),
        r_pi(RawExpr::BVar(0), r_app(r_const(name), RawExpr::BVar(1))),
    );
    InductiveDecl {
        name: n(name),
        num_level_params: 0,
        num_params: 1,
        type_: Term::validate_closed(&own, &r_pi(r_type(), r_type())).expect("the type"),
        constructors: vec![Constructor {
            name: n(&format!("{name}.c0")),
            type_: Term::validate_closed(&own, &ctor).expect("the ctor"),
        }],
    }
}

/// `T (p_1 … p_np : Type) : Type` with
/// `T.c0 : (p… : Type) → W (D → T p…) → T p…`, `D` a `g_tree` of `height`.
/// The rewrite makes each self-reference the auxiliary applied to the `np`
/// parameters, so the parent constructor is charged its size times `2·np + 1`.
fn with_params(np: u32, height: u32) -> Result<String, String> {
    let env = g_env();
    let t_params = |shift: u32| {
        (0..np)
            .rev()
            .fold(r_const("T"), |t, p| r_app(t, RawExpr::BVar(shift + p)))
    };
    let over_params = |body: RawExpr| (0..np).fold(body, |b, _| r_pi(r_type(), b));
    let field = r_app(r_const("W"), r_pi(g_tree(height), t_params(1)));
    let own = env.clone().with_const(n("T"), 0).with_const(n("W"), 0);
    let valid = |raw: &RawExpr| Term::validate_closed(&own, raw).expect("the decl validates");
    let t = InductiveDecl {
        name: n("T"),
        num_level_params: 0,
        num_params: np,
        type_: valid(&over_params(r_type())),
        constructors: vec![Constructor {
            name: n("T.c0"),
            type_: valid(&over_params(r_pi(field, t_params(1)))),
        }],
    };
    nested_detail(env, vec![one_use("W")], t)
}

#[test]
fn test_nested_parent_constructor_charge_control_small_argument_admits() {
    assert_eq!(with_params(100, 4), Err("Ok(())".to_string()));
}

/// About 131,700 nodes times 201: past the budget before any auxiliary is
/// built, at the parent constructor's charge alone.
#[test]
fn test_nested_parent_constructor_past_the_budget_is_refused_at_its_charge() {
    let detail = with_params(100, 15).expect("refused as a derivation error");
    assert!(
        detail.contains(&past_the_budget_at("the parent constructor `T.c0`")),
        "{detail}"
    );
}

/// `V (α : Type) : K → Type`, `K` a `g_tree` of height 7 (509 nodes), with
/// `V.c0 : (α : Type) → (x : K) → V α x`; `k : K` is an axiom, and
/// `T.c0 : V (D → T) k → T`. The auxiliary type is charged `V`'s type
/// (513 nodes) times one copy of `D → T`.
fn indexed(height: u32) -> Result<String, String> {
    let k_ty = Term::validate_closed(&g_env(), &g_tree(7)).expect("K");
    let env = g_env().with_const_typed(n("k"), 0, k_ty);
    let own = env.clone().with_const(n("V"), 0);
    let v_ctor = r_pi(
        r_type(),
        r_pi(
            g_tree(7),
            r_app(r_app(r_const("V"), RawExpr::BVar(1)), RawExpr::BVar(0)),
        ),
    );
    let v = InductiveDecl {
        name: n("V"),
        num_level_params: 0,
        num_params: 1,
        type_: Term::validate_closed(&own, &r_pi(r_type(), r_pi(g_tree(7), r_type())))
            .expect("V's type"),
        constructors: vec![Constructor {
            name: n("V.c0"),
            type_: Term::validate_closed(&own, &v_ctor).expect("V.c0"),
        }],
    };
    let parent_env = env.clone().with_const(n("T"), 0).with_const(n("V"), 0);
    let field = r_app(
        r_app(r_const("V"), r_pi(g_tree(height), r_const("T"))),
        r_const("k"),
    );
    let t = InductiveDecl {
        name: n("T"),
        num_level_params: 0,
        num_params: 0,
        type_: Term::validate_closed(&parent_env, &r_type()).expect("Type"),
        constructors: vec![Constructor {
            name: n("T.c0"),
            type_: Term::validate_closed(&parent_env, &r_pi(field, r_const("T"))).expect("T.c0"),
        }],
    };
    nested_detail(env, vec![v], t)
}

#[test]
fn test_nested_auxiliary_type_charge_control_small_argument_admits() {
    assert_eq!(indexed(4), Err("Ok(())".to_string()));
}

/// 513 nodes times about 65,500: past the budget at the auxiliary type,
/// with the parent constructor (about 65,500 nodes) well within it.
#[test]
fn test_nested_auxiliary_type_past_the_budget_is_refused_at_its_charge() {
    let detail = indexed(14).expect("refused as a derivation error");
    assert!(
        detail.contains(&past_the_budget_at("the auxiliary type `T._V`")),
        "{detail}"
    );
}

/// `T (A : Type) : Type → Type` with the one occurrence
/// `T.c1 : (A : Type) → C (T A Prop) → T A Prop`, and
/// `T.c2 : (A : Type) → T A (C (C … (T A D))) → T A Prop`, `depth`
/// applications of `C` around `T A D`, `D` a `g_tree` of height 16 with
/// leaves `leaf` (262,141 nodes). Under `T.c2`'s own head each `C` is a site
/// the occurrence could match, so phase 3 lowers its argument to compare it,
/// charging each node lowering builds first; no occurrence has the key of a
/// lowered argument, so none is compared. Lean refuses `T.c2`, `T` in an
/// index of its own recursive field, and so does admission (`NonPositive`).
/// Before `T.c2`'s sites, the parent constructors (`T.c2`'s 262,157 +
/// 2·`depth` nodes, `T.c1`'s 15, each times 3), the auxiliary (148) and the
/// occurrence's two matches (3 nodes built and 5 pairs compared, in `C.c0`'s
/// self-reference and at `T.c1`'s site) take 3·(262,172 + 2·`depth`) + 164
/// of the budget.
fn unmatched_sites(depth: u32, leaf: &RawExpr) -> Result<String, String> {
    let env = g_env();
    let t_a = |a: u32, i: RawExpr| r_app(r_app(r_const("T"), RawExpr::BVar(a)), i);
    let nest = (0..depth).fold(t_a(0, g_tree_of(16, leaf)), |x, _| r_app(r_const("C"), x));
    let own = env.clone().with_const(n("T"), 0).with_const(n("C"), 0);
    let valid = |raw: &RawExpr| Term::validate_closed(&own, raw).expect("the decl validates");
    let ctor = |name: &str, field: RawExpr| Constructor {
        name: n(name),
        type_: valid(&r_pi(r_type(), r_pi(field, t_a(1, r_prop())))),
    };
    let t = InductiveDecl {
        name: n("T"),
        num_level_params: 0,
        num_params: 1,
        type_: valid(&r_pi(r_type(), r_pi(r_type(), r_type()))),
        constructors: vec![
            ctor("T.c1", r_app(r_const("C"), t_a(0, r_prop()))),
            ctor("T.c2", t_a(0, nest)),
        ],
    };
    nested_detail(env, vec![one_use("C")], t)
}

/// 50 sites over a closed `D`: each builds only the nodes above `A`, the
/// site at depth `j` `j + 2` of them (1,375 in all), within the budget:
/// admission refuses the block, as Lean does.
#[test]
fn test_nested_unmatched_sites_control_within_the_budget_is_refused_by_admission() {
    let outcome = unmatched_sites(50, &r_prop()).expect_err("not a derivation error");
    assert!(outcome.contains("NonPositive"), "{outcome}");
}

/// 63 sites over a closed `D`: 2,142 nodes built, so the block reaches
/// admission. R174 charged each site its whole argument, 262,145 + 2(j - 1)
/// nodes, 16,519,041 in all, and refused it at the matching charge.
#[test]
fn test_nested_unmatched_sites_closed_index_is_charged_only_what_lowering_builds() {
    let outcome = unmatched_sites(63, &r_prop()).expect_err("not a derivation error");
    assert!(outcome.contains("NonPositive"), "{outcome}");
}

/// 81 sites over a `D` with leaves `A`: the site at depth `j` builds
/// `j + 196,608` nodes, every node above an `A` (`D`'s 65,536 leaves and
/// 131,070 applications, `T A D`'s 3, the `j - 1` applications of `C`),
/// sharing `T` and `D`'s 65,535 `G`s: 15,928,569 in all. With the 787,166
/// taken before them that is 16,715,735 of `MAX_AUX_SIZE` = 16,777,216:
/// admission refuses the block. R174 refused it at the matching charge.
#[test]
fn test_nested_unmatched_sites_open_index_within_the_budget_is_refused_by_admission() {
    let outcome = unmatched_sites(81, &a_leaf(0)).expect_err("not a derivation error");
    assert!(outcome.contains("NonPositive"), "{outcome}");
}

/// 82 sites, charged from the outermost: the earlier charges take 787,172,
/// the sites at depths 82 to 2 another 15,928,650, which leaves 61,394, and
/// the innermost site's 196,609 pass it. `T.c2`'s matching charges alone
/// come to 16,125,259, within `MAX_AUX_SIZE`: the block is refused at the
/// matching charge only because they draw on the block's one budget.
#[test]
fn test_nested_unmatched_sites_past_the_budget_are_refused_at_their_charge() {
    let detail = unmatched_sites(82, &a_leaf(0)).expect("refused as a derivation error");
    assert!(detail.contains(&matching_in("T.c2")), "{detail}");
}

/// `T (A : Type) : Type → Type` with
/// `T.c0 : (A : Type) → T A (T A Prop) → T A Prop`, which admission refuses
/// (`NonPositive`, as Lean does) and which matches nothing, and
/// `T.c1 : (A : Type) → C (T A D) → … → C (T A D) → T A Prop`, `fields`
/// fields, each `D` its own `g_tree` of height 14 with leaves `A` (65,533
/// nodes, 49,150 of them above an `A`). Phase 1 records the one occurrence
/// `C (T A D)`; phase 3 lowers each field's argument (49,153 nodes built,
/// `T` and the `G`s shared) and compares the copy with the occurrence, built
/// apart from it: 65,537 pairs. Before phase 3, the parent constructors
/// (`T.c0`'s 17 nodes and `T.c1`'s 65,540·`fields` + 7, each times 3), the
/// auxiliary type (196,616), its constructor (1,376,300) and that
/// constructor's self-reference (114,690) take 196,620·`fields` + 1,687,678.
fn repeated_sites(fields: u32) -> Result<String, String> {
    let env = g_env();
    let t_a = |a: u32, i: RawExpr| r_app(r_app(r_const("T"), RawExpr::BVar(a)), i);
    let own = env.clone().with_const(n("T"), 0).with_const(n("C"), 0);
    let valid = |raw: &RawExpr| Term::validate_closed(&own, raw).expect("the decl validates");
    let body = (0..fields).rev().fold(t_a(fields, r_prop()), |body, j| {
        r_pi(r_app(r_const("C"), t_a(j, g_tree_of(14, &a_leaf(j)))), body)
    });
    let t = InductiveDecl {
        name: n("T"),
        num_level_params: 0,
        num_params: 1,
        type_: valid(&r_pi(r_type(), r_pi(r_type(), r_type()))),
        constructors: vec![
            Constructor {
                name: n("T.c0"),
                type_: valid(&r_pi(
                    r_type(),
                    r_pi(t_a(0, t_a(0, r_prop())), t_a(1, r_prop())),
                )),
            },
            Constructor {
                name: n("T.c1"),
                type_: valid(&r_pi(r_type(), body)),
            },
        ],
    };
    nested_detail(env, vec![one_use("C")], t)
}

/// 48 fields: 11,125,438 before phase 3, and 48 × (49,153 + 65,537) =
/// 5,505,120 in it, 16,630,558 of `MAX_AUX_SIZE`: admission refuses the
/// block.
#[test]
fn test_nested_repeated_sites_control_within_the_budget_is_refused_by_admission() {
    let outcome = repeated_sites(48).expect_err("not a derivation error");
    assert!(outcome.contains("NonPositive"), "{outcome}");
}

/// 49 fields: 11,322,058 before phase 3 leaves 5,455,158; 47 sites take
/// 5,390,430, the 48th's lowering 49,153, and its comparison's 65,537 pairs
/// pass the 15,575 left. Lowering alone, everywhere, would come to
/// 13,665,018, and R174 charged 14,484,218 (each site its whole argument,
/// 65,537) and reached admission: so this pins phase 3's comparison charge.
#[test]
fn test_nested_repeated_sites_comparisons_are_charged_in_phase_3() {
    let detail = repeated_sites(49).expect("refused as a derivation error");
    assert!(detail.contains(&matching_in("T.c1")), "{detail}");
}

/// `C (α : Type) : Type` with `C.c0 : (α : Type) → C α → … → C α → C α`,
/// `fields` recursive fields.
fn self_refs(fields: u32) -> InductiveDecl {
    let own = MinimalEnv::new().with_const(n("C"), 0);
    let mut ctor = r_app(r_const("C"), RawExpr::BVar(fields));
    for j in (0..fields).rev() {
        ctor = r_pi(r_app(r_const("C"), RawExpr::BVar(j)), ctor);
    }
    InductiveDecl {
        name: n("C"),
        num_level_params: 0,
        num_params: 1,
        type_: Term::validate_closed(&own, &r_pi(r_type(), r_type())).expect("the type"),
        constructors: vec![Constructor {
            name: n("C.c0"),
            type_: Term::validate_closed(&own, &r_pi(r_type(), ctor)).expect("the ctor"),
        }],
    }
}

/// `T (A : Type) : Type → Type` with `T.c1 : (A : Type) → C (T A D) → T A Prop`,
/// `C` as `self_refs(fields)` and `D` a `g_tree` of `height` with leaves
/// `leaf`. The auxiliary's constructor is `C.c0` with `T A D` for `α`:
/// `fields + 1` self-references, each lowered and compared with the
/// occurrence before it becomes the auxiliary.
fn aux_self_refs(fields: u32, height: u32, leaf: &RawExpr) -> Result<String, String> {
    let env = g_env();
    let t_a = |a: u32, i: RawExpr| r_app(r_app(r_const("T"), RawExpr::BVar(a)), i);
    let own = env.clone().with_const(n("T"), 0).with_const(n("C"), 0);
    let valid = |raw: &RawExpr| Term::validate_closed(&own, raw).expect("the decl validates");
    let field = r_app(r_const("C"), t_a(0, g_tree_of(height, leaf)));
    let t = InductiveDecl {
        name: n("T"),
        num_level_params: 0,
        num_params: 1,
        type_: valid(&r_pi(r_type(), r_pi(r_type(), r_type()))),
        constructors: vec![Constructor {
            name: n("T.c1"),
            type_: valid(&r_pi(r_type(), r_pi(field, t_a(1, r_prop())))),
        }],
    };
    nested_detail(env, vec![self_refs(fields)], t)
}

#[test]
fn test_nested_auxiliary_self_reference_charge_control_small_argument_admits() {
    assert_eq!(aux_self_refs(19, 2, &r_prop()), Err("Ok(())".to_string()));
}

/// `D` of height 14 with leaves `Prop` is closed, so lowering a
/// self-reference `T A D` builds only its two applications and `A`, and
/// keeps `D` itself, the occurrence's own `D`: its comparison looks at 5
/// pairs. The charges before the auxiliary's rewrite leave 458,223, as with
/// leaves `A`; the 20 self-references take 160 of it and `T.c1`'s site 8,
/// and the block admits. R174 charged each self-reference its whole
/// argument, 65,537 nodes, and refused the block at the seventh.
#[test]
fn test_nested_auxiliary_self_references_sharing_a_closed_argument_admit() {
    assert_eq!(aux_self_refs(19, 14, &r_prop()), Err("Ok(())".to_string()));
}

/// `D` of height 14 with leaves `A` is 65,533 nodes, `T A D` 65,537, of
/// which 49,153 are above an `A`. Charged in order: `T.c1`, 65,547 nodes
/// times 3; the auxiliary type, `C`'s 3 nodes times one copy of `T A D`
/// (65,538) plus its parameter binder (2); `C.c0`, 81 nodes times 65,538
/// times 3, plus 2. That is 16,318,993 of `MAX_AUX_SIZE`, and leaves
/// 458,223. Each of the 20 self-references is charged the 49,153 nodes
/// lowering it builds, then the 65,537 pairs comparing the copy with the
/// occurrence looks at (they share only `T` and the `G`s): the fourth's
/// comparison passes the budget, in the auxiliary's rewrite and before
/// phase 3. R174 refused it at the seventh self-reference's whole argument.
/// Pinned Lean v4.30.0-rc2's kernel accepts this block (`addDeclCore`, 0.70 s,
/// measured 2026-10-28; R176): the refusal is a known false rejection on
/// cost, pinned so it fails loudly the day the budget admits it.
#[test]
fn test_nested_auxiliary_self_references_past_the_budget_are_refused_at_their_charge() {
    let detail = aux_self_refs(19, 14, &a_leaf(0)).expect("refused as a derivation error");
    assert!(detail.contains(&matching_in("C.c0")), "{detail}");
}

/// 17 fields: `C.c0` is 73 nodes, so the charges before its rewrite come
/// to 14,746,081 and leave 2,031,135. The 18 self-references' lowerings
/// alone, 18 × 49,153 = 884,754, would fit, and R174 charged 18 × 65,537 =
/// 1,179,666 and reached admission; with each comparison's 65,537 pairs the
/// 18th comparison passes the budget, so this pins the self-reference's
/// comparison charge. Pinned Lean v4.30.0-rc2's kernel accepts this block
/// (`addDeclCore`, 0.49 s, measured 2026-10-28): R176's comparison charge
/// makes it a false rejection on cost that R174 did not have, kept because
/// the charge bounds the comparison work (R176).
#[test]
fn test_nested_auxiliary_self_reference_comparisons_are_charged() {
    let detail = aux_self_refs(17, 14, &a_leaf(0)).expect("refused as a derivation error");
    assert!(detail.contains(&matching_in("C.c0")), "{detail}");
}

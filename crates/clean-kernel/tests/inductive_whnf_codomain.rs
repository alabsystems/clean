//! An inductive type former whose arity codomain is a sort only up to whnf.
//!
//! Lean's `check_inductive_types` (`inductive.cpp@v4.30.0-rc2:211-256`) finds a
//! family's result level by whnf between binders and `ensure_sort`, and every
//! later decision reads that level. Two consequences are pinned here:
//!
//! - Kernel BUG-2: such a family must REPLAY. Coq's Hierarchy-Builder records
//!   have codomains that are sorts only up to reduction (`LetIn(T := …) in
//!   Sort u`, the `mixin_of` records; `Const(c)` with `c` unfolding to a sort,
//!   the `predArgType` carriers). A syntactic `Sort` match rejected them.
//! - `kernel-result-sort-whnf-elim` (P0, 2026-10-16): the level found up to
//!   whnf must DRIVE elimination. `def MyProp : Type := Prop; inductive B :
//!   MyProp | t | f` is a two-constructor `Prop` family, so `B.rec` eliminates
//!   only into `Prop` (pinned Lean 4.8.0 and v4.30.0-rc2: `@B.rec : ∀ {motive :
//!   B → Prop}, …`). Clean read the syntactic head `MyProp`, answered "large
//!   elimination allowed", and since proof irrelevance (which whnf's) made
//!   `B.t ≡ B.f`, `Bool.noConfusion` over a `B.rec` into `Bool` proved `False`.

use clean_kernel::env::{Declaration, Environment};
use clean_kernel::expr::{BinderInfo, Expr};
use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};
use clean_kernel::level::Level;
use clean_kernel::tc::TypeChecker;
use clean_kernel::Name;

fn n(s: &str) -> Name {
    Name::from_string(s)
}

fn c(s: &str) -> Expr {
    Expr::const_(n(s), vec![])
}

fn cl(s: &str, levels: Vec<Level>) -> Expr {
    Expr::const_(n(s), levels)
}

fn l1() -> Level {
    Level::succ(Level::zero())
}

fn sort1() -> Expr {
    Expr::sort(l1())
}

fn arrow(dom: Expr, cod: Expr) -> Expr {
    Expr::pi(BinderInfo::Default, dom, cod)
}

/// One family with constructors `ctors`, each `name.ctor : fields → name`.
fn family(name: &str, num_params: u32, type_: Expr, ctors: Vec<(&str, Expr)>) -> InductiveDecl {
    InductiveDecl {
        level_params: vec![],
        num_params,
        types: vec![InductiveType {
            name: n(name),
            type_,
            constructors: ctors
                .into_iter()
                .map(|(ctor, type_)| Constructor {
                    name: n(&format!("{name}.{ctor}")),
                    type_,
                })
                .collect(),
        }],
    }
}

/// `name : type_ | t | f`.
fn two_ctor(name: &str, type_: Expr) -> InductiveDecl {
    family(name, 0, type_, vec![("t", c(name)), ("f", c(name))])
}

fn add_def(env: &mut Environment, name: &str, type_: Expr, value: Expr) {
    env.add_decl(Declaration::Definition {
        name: n(name),
        level_params: vec![],
        type_,
        value,
        is_reducible: false,
    })
    .unwrap_or_else(|e| panic!("definition {name} must be admitted: {e}"));
}

/// The prelude plus `def MyProp : Type := Prop`, `def MyType : Type 1 := Type`,
/// `def MyPropFn (α : Type) : Type := Prop` and `def MyArity : Type := Nat → Prop`.
fn delta_env() -> Environment {
    let mut env = Environment::try_with_prelude().expect("prelude environment");
    add_def(&mut env, "MyProp", sort1(), Expr::prop());
    add_def(&mut env, "MyType", Expr::sort(Level::succ(l1())), sort1());
    add_def(
        &mut env,
        "MyPropFn",
        arrow(sort1(), sort1()),
        Expr::lam(BinderInfo::Default, sort1(), Expr::prop()),
    );
    add_def(&mut env, "MyArity", sort1(), arrow(c("Nat"), Expr::prop()));
    env
}

#[derive(Clone, Copy, Debug)]
enum Entry {
    Full,
    Core,
}

fn admit(env: &mut Environment, decl: InductiveDecl, entry: Entry) {
    let name = decl.types[0].name.clone();
    match entry {
        Entry::Full => env.add_inductive(decl),
        Entry::Core => env.add_inductive_core(decl),
    }
    .unwrap_or_else(|e| panic!("{name} must be admitted through {entry:?}: {e}"));
}

/// Exit criterion (1): no motive universe on the recursor, `is_large_elim`
/// false, no `noConfusionType`/`noConfusion`, and (when generated) a Prop-only
/// `casesOn`.
fn assert_prop_only(env: &Environment, name: &str, entry: Entry) {
    let ind = env.get_inductive(&n(name)).expect("family registered");
    assert!(
        !ind.is_large_elim,
        "{name} ({entry:?}): is_large_elim must be false"
    );
    let rec = env
        .get_recursor(&n(&format!("{name}.rec")))
        .expect("recursor");
    assert!(
        rec.level_params.is_empty(),
        "{name}.rec ({entry:?}) must have no motive universe (Lean: motive : {name} → Prop); \
         got level params {:?}",
        rec.level_params
    );
    assert!(!rec.is_k, "{name}.rec: two constructors, not a K target");
    for suffix in ["noConfusionType", "noConfusion", "below"] {
        assert!(
            env.get_const(&n(&format!("{name}.{suffix}"))).is_none(),
            "{name}.{suffix} ({entry:?}) must be absent for a Prop family"
        );
    }
    if let Entry::Full = entry {
        let cases = env
            .get_recursor(&n(&format!("{name}.casesOn")))
            .expect("casesOn");
        assert!(
            cases.level_params.is_empty(),
            "{name}.casesOn must be Prop-only"
        );
    }
}

#[test]
fn test_delta_prop_family_eliminates_only_into_prop() {
    for entry in [Entry::Full, Entry::Core] {
        let mut env = delta_env();
        admit(&mut env, two_ctor("DB", c("MyProp")), entry);
        assert_prop_only(&env, "DB", entry);
    }
}

/// Exit criterion (3): the ζ- and β-spellings of the same codomain.
#[test]
fn test_zeta_and_beta_prop_codomains_eliminate_only_into_prop() {
    let zeta = Expr::let_named(n("T"), sort1(), Expr::prop(), Expr::bvar(0), false);
    let beta = Expr::app(
        Expr::lam(BinderInfo::Default, sort1(), Expr::bvar(0)),
        Expr::prop(),
    );
    for entry in [Entry::Full, Entry::Core] {
        let mut env = delta_env();
        admit(&mut env, two_ctor("DZ", zeta.clone()), entry);
        admit(&mut env, two_ctor("DBeta", beta.clone()), entry);
        assert_prop_only(&env, "DZ", entry);
        assert_prop_only(&env, "DBeta", entry);
    }
}

/// A parameter before the δ-codomain: the loop opens the binder with a local
/// and reduces `MyPropFn α` under it.
#[test]
fn test_parameterized_delta_prop_family_eliminates_only_into_prop() {
    let type_ = arrow(sort1(), Expr::app(c("MyPropFn"), Expr::bvar(0)));
    let ret = || {
        Expr::pi(
            BinderInfo::Default,
            sort1(),
            Expr::app(c("DP"), Expr::bvar(0)),
        )
    };
    for entry in [Entry::Full, Entry::Core] {
        let mut env = delta_env();
        admit(
            &mut env,
            family("DP", 1, type_.clone(), vec![("t", ret()), ("f", ret())]),
            entry,
        );
        assert_prop_only(&env, "DP", entry);
    }
}

/// `fun (b : DB) => @DB.rec.{levels} (fun _ => Bool) true false b`.
fn to_bool(major: Expr, levels: &[Level]) -> Expr {
    let motive = Expr::lam(BinderInfo::Default, c("DB"), c("Bool"));
    Expr::apps(
        cl("DB.rec", levels.to_vec()),
        [motive, c("Bool.true"), c("Bool.false"), major],
    )
}

/// The proof of `False` the hole admitted, as one closed term:
/// `tf : DB.t = DB.f := Eq.refl DB.t` (proof irrelevance), its congruence
/// image under `to_bool` by `Eq.rec`, and `Bool.noConfusion` on `true = false`.
fn false_derivation(levels: &[Level]) -> Expr {
    let z = Level::zero;
    let tf = Expr::apps(cl("Eq.refl", vec![z()]), [c("DB"), c("DB.t")]);
    let eq_db = |x: Expr| Expr::apps(cl("Eq", vec![z()]), [c("DB"), c("DB.t"), x]);
    let eq_bool = |a: Expr, b: Expr| Expr::apps(cl("Eq", vec![l1()]), [c("Bool"), a, b]);
    // motive : (x : DB) → DB.t = x → Prop := fun x _ => toBool DB.t = toBool x
    let motive = Expr::lam(
        BinderInfo::Default,
        c("DB"),
        Expr::lam(
            BinderInfo::Default,
            eq_db(Expr::bvar(0)),
            eq_bool(to_bool(c("DB.t"), levels), to_bool(Expr::bvar(1), levels)),
        ),
    );
    let refl_case = Expr::apps(
        cl("Eq.refl", vec![l1()]),
        [c("Bool"), to_bool(c("DB.t"), levels)],
    );
    let congr = Expr::apps(
        cl("Eq.rec", vec![z(), z()]),
        [c("DB"), c("DB.t"), motive, refl_case, c("DB.f"), tf],
    );
    Expr::apps(
        cl("Bool.noConfusion", vec![z()]),
        [c("False"), c("Bool.true"), c("Bool.false"), congr],
    )
}

fn theorem(name: &str, type_: Expr, value: Expr) -> Declaration {
    Declaration::Theorem {
        name: n(name),
        level_params: vec![],
        type_,
        value,
    }
}

/// Exit criterion (2): the derivation of `False` through `DB.rec` into `Bool`
/// is refused, for the right reason (`DB.rec` has no motive universe), while
/// `DB.t = DB.f` itself still holds by proof irrelevance, as in Lean: the
/// defence is entirely that `DB.rec` eliminates only into `Prop`.
#[test]
fn test_delta_prop_false_derivation_is_refused() {
    for entry in [Entry::Full, Entry::Core] {
        let mut env = delta_env();
        admit(&mut env, two_ctor("DB", c("MyProp")), entry);
        let tf_ty = Expr::apps(
            cl("Eq", vec![Level::zero()]),
            [c("DB"), c("DB.t"), c("DB.f")],
        );
        let tf = Expr::apps(cl("Eq.refl", vec![Level::zero()]), [c("DB"), c("DB.t")]);
        env.add_decl(theorem("delta_tf", tf_ty, tf))
            .expect("DB.t = DB.f holds by proof irrelevance (DB is a Prop up to whnf)");

        let err = env
            .add_decl(theorem("delta_bad", c("False"), false_derivation(&[l1()])))
            .expect_err("False through DB.rec.{1} must be refused");
        let msg = err.to_string();
        assert!(
            msg.contains("Level count mismatch for DB.rec: declared 0 level params, got 1"),
            "{entry:?}: refused for the wrong reason: {msg}"
        );
        // Without the universe argument the motive `DB → Bool` is not `DB → Prop`.
        let err = env
            .add_decl(theorem("delta_bad0", c("False"), false_derivation(&[])))
            .expect_err("False through DB.rec into Bool must be refused");
        assert!(
            env.get_const(&n("delta_bad0")).is_none(),
            "{entry:?}: a refused theorem must not be registered: {err}"
        );
    }
}

/// Positive control: `def MyType : Type 1 := Type; inductive DT : MyType | a | b`
/// large-eliminates, as in pinned Lean (`@DT.rec : {motive : DT → Sort u_1} → …`,
/// and `DT.noConfusion` exists), and its recursor computes.
#[test]
fn test_delta_type_family_large_eliminates() {
    for entry in [Entry::Full, Entry::Core] {
        let mut env = delta_env();
        admit(
            &mut env,
            family("DT", 0, c("MyType"), vec![("a", c("DT")), ("b", c("DT"))]),
            entry,
        );
        let ind = env.get_inductive(&n("DT")).expect("DT registered");
        assert!(
            ind.is_large_elim,
            "{entry:?}: a δ-Type family large-eliminates"
        );
        let rec = env.get_recursor(&n("DT.rec")).expect("DT.rec");
        assert_eq!(
            rec.level_params.len(),
            1,
            "{entry:?}: DT.rec has a motive universe"
        );
        if let Entry::Full = entry {
            assert!(
                env.get_const(&n("DT.noConfusionType")).is_some(),
                "a δ-Type family gets noConfusionType, as in Lean"
            );
        }
        let motive = Expr::lam(BinderInfo::Default, c("DT"), c("Bool"));
        let elim = Expr::apps(
            cl("DT.rec", vec![l1()]),
            [motive, c("Bool.true"), c("Bool.false"), c("DT.b")],
        );
        let tc = TypeChecker::new(&env);
        tc.check_type(&elim, &c("Bool"))
            .expect("DT.rec.{1} into Bool type-checks");
        assert_eq!(tc.whnf(&elim), c("Bool.false"), "iota through DT.rec");
    }
}

/// Positive control: an ordinary `inductive DC : Prop | t | f` is Prop-only.
#[test]
fn test_ordinary_prop_family_eliminates_only_into_prop() {
    for entry in [Entry::Full, Entry::Core] {
        let mut env = delta_env();
        admit(&mut env, two_ctor("DC", Expr::prop()), entry);
        assert_prop_only(&env, "DC", entry);
    }
}

/// The rest of Lean's ladder on a δ-`Prop` codomain (pinned Lean 4.8.0 and
/// v4.30.0-rc2): an empty family and a single field-less constructor
/// large-eliminate (the latter is a K target); a single constructor with a
/// `Nat` field eliminates only into `Prop`.
#[test]
fn test_delta_prop_single_and_empty_families_follow_leans_ladder() {
    for entry in [Entry::Full, Entry::Core] {
        let mut env = delta_env();
        admit(&mut env, family("DE", 0, c("MyProp"), vec![]), entry);
        admit(
            &mut env,
            family("DU", 0, c("MyProp"), vec![("u", c("DU"))]),
            entry,
        );
        admit(
            &mut env,
            family("DW", 0, c("MyProp"), vec![("w", arrow(c("Nat"), c("DW")))]),
            entry,
        );
        let levels = |name: &str| {
            env.get_recursor(&n(&format!("{name}.rec")))
                .expect("recursor")
                .level_params
                .len()
        };
        assert_eq!(
            levels("DE"),
            1,
            "{entry:?}: an empty Prop family large-eliminates"
        );
        assert_eq!(
            levels("DU"),
            1,
            "{entry:?}: DU.u has no fields: large elimination"
        );
        assert_eq!(
            levels("DW"),
            0,
            "{entry:?}: DW.w's Nat field keeps DW Prop-only"
        );
        let du = env.get_recursor(&n("DU.rec")).expect("DU.rec");
        assert!(
            du.is_k,
            "{entry:?}: DU is a K target (one field-less ctor, level 0)"
        );
    }
}

/// A type former whose definition hides an index binder
/// (`def MyArity : Type := Nat → Prop; inductive DH : MyArity | mk : DH 0`).
/// Lean admits it with one index; Clean's eliminator builders read the
/// syntactic telescope, so the family is refused by name (safe direction).
#[test]
fn test_hidden_index_binder_is_refused_by_name() {
    let mut env = delta_env();
    let decl = family(
        "DH",
        0,
        c("MyArity"),
        vec![("mk", Expr::app(c("DH"), c("Nat.zero")))],
    );
    let err = env
        .add_inductive(decl)
        .expect_err("a type former hiding binders behind a definition is refused");
    let msg = err.to_string();
    assert!(
        msg.contains("hides binders"),
        "refused for the wrong reason: {msg}"
    );
}

/// `RLet : Π (A : Sort 1), (let (x : Sort 1 := A) in Sort 1)`  (num_params = 1)
///   codomain zeta-reduces to `Sort 1` (the `mixin_of` / `LetIn in Sort` shape).
/// `RLet.mk : Π (A : Sort 1), RLet A`
fn letin_codomain_decl() -> InductiveDecl {
    let codomain = Expr::let_named(Name::anon(), sort1(), Expr::bvar(0), sort1(), false);
    let ret = Expr::pi(
        BinderInfo::Default,
        sort1(),
        Expr::app(c("RLetCodomain"), Expr::bvar(0)),
    );
    family(
        "RLetCodomain",
        1,
        arrow(sort1(), codomain),
        vec![("mk", ret)],
    )
}

#[test]
fn test_letin_sort_codomain_type_former_replays() {
    let mut env = Environment::try_with_prelude().expect("prelude environment");
    env.set_cumulative(true);
    env.add_inductive_core(letin_codomain_decl()).expect(
        "a type former whose codomain is `let _ in Sort` (zeta-reducible to a \
         sort) must replay — the HB `mixin_of` record shape",
    );
    let ind = env.get_inductive(&n("RLetCodomain")).expect("registered");
    assert!(
        ind.is_large_elim,
        "a `let _ in Sort 1` codomain is a Type family"
    );
}

/// A genuine NON-sort codomain: `RBad : Π (A : Sort 1), Nat`. `whnf(Nat)` is the
/// `Nat` inductive, never a sort — must STILL be rejected (fail-closed control:
/// the fix widens the check to whnf, it does not disable it).
#[test]
fn test_non_sort_codomain_type_former_still_rejected() {
    let mut env = Environment::try_with_prelude().expect("prelude environment");
    env.set_cumulative(true);
    let ret = Expr::pi(
        BinderInfo::Default,
        sort1(),
        Expr::app(c("RBadCodomain"), Expr::bvar(0)),
    );
    let decl = family(
        "RBadCodomain",
        1,
        arrow(sort1(), c("Nat")),
        vec![("mk", ret)],
    );
    let err = env
        .add_inductive_core(decl)
        .expect_err("a codomain that does not whnf to a sort must be rejected");
    let msg = format!("{err}");
    assert!(
        msg.contains("does not end in a sort"),
        "the fail-closed control must reject with a sort-shape error; got: {msg}",
    );
}

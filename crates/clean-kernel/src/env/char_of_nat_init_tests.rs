// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `Environment::init_char_of_nat` — the public focused initializer that
//! seeds `Char.ofNat` (with `Char.ofNatAux` and `Char.utf8Size`) in a minimal
//! environment, so string literals expand there again.
//!
//! Since native-fold authority (3809edf31) a string literal expands to
//! `String.ofList [Char.ofNat c, …]` only when both heads are the kernel's own
//! definitions. `Char.ofNat` was seeded only by the crate-private
//! `init_char_defs` inside `with_prelude`, so an environment assembled from the
//! public initializers (`Environment::new` + `init_string` + …, the shape ty's
//! `tla-ir` string model builds) refused every proof that needs a literal's
//! characters. These tests pin, for the bare shape and for ty's shape:
//!
//! - (a) the refusal before the call and the admission after it;
//! - (b) that every declaration the call installs is the one `with_prelude`
//!   holds, and that `Char.ofNat`'s closure is the pinned `clean-prelude` one;
//! - (c) idempotence, a no-op on both preludes, and order independence;
//! - (d) that it launders no impostor: the authority check still refuses a
//!   user's `Char.ofNat`, before or after the call.

use crate::env::{Declaration, Environment, FoldRefusal};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;
use crate::tc::TypeChecker;

fn n(s: &str) -> Name {
    Name::from_string(s)
}

fn c(s: &str) -> Expr {
    Expr::const_(n(s), vec![])
}

fn lit(v: u64) -> Expr {
    Expr::nat_lit(v)
}

/// The three definitions `init_char_defs` seeds.
const SEEDED: [&str; 3] = ["Char.ofNatAux", "Char.ofNat", "Char.utf8Size"];

/// `Environment::new` + `init_string`: the least a string needs.
fn bare_string_env() -> Environment {
    let mut env = Environment::new();
    env.init_string().expect("init_string");
    env
}

/// The environment ty's `tla-ir` string model assembles from public focused
/// initializers (`structured_value::install`, `generator_value::install`,
/// `generator_candidate::install`), in its order.
fn ty_shape_env() -> Environment {
    let mut env = Environment::new();
    env.init_eq().expect("init_eq");
    env.init_bool().expect("init_bool");
    env.init_int().expect("init_int");
    env.init_string().expect("init_string");
    env.init_list().expect("init_list");
    env.init_unit().expect("init_unit");
    env.init_option().expect("init_option");
    env.init_except_t().expect("init_except_t");
    env.init_list_contains().expect("init_list_contains");
    env.init_prod().expect("init_prod");
    env
}

fn shapes() -> [(&'static str, fn() -> Environment); 2] {
    [("bare", bare_string_env), ("ty", ty_shape_env)]
}

/// `rfl : lhs = rhs` at `ty`, with the kernel's error when it does not check.
fn rfl_result(env: &Environment, ty: Expr, lhs: Expr, rhs: Expr) -> Result<(), String> {
    let one = Level::succ(Level::zero());
    let goal = Expr::apps(
        Expr::const_(n("Eq"), vec![one.clone()]),
        [ty.clone(), lhs, rhs.clone()],
    );
    let proof = Expr::apps(Expr::const_(n("Eq.refl"), vec![one]), [ty, rhs]);
    TypeChecker::new(env)
        .check_type(&proof, &goal)
        .map(|_| ())
        .map_err(|e| format!("{e:?}"))
}

/// `List.length (String.data s) = k` by `rfl`: well typed with or without
/// `Char.ofNat`, and it checks only if the literal expands — `List.length`
/// recurses on `String.data s`, whose ι-step needs the literal's constructor
/// form. (`String.length s` would not do: its registered native reducer reads
/// the literal directly and never expands it.)
fn length_checks(env: &Environment, s: &str, k: u64) -> Result<(), String> {
    let data = Expr::app(c("String.data"), Expr::str_lit(s));
    let length = Expr::apps(
        Expr::const_(n("List.length"), vec![Level::zero()]),
        [c("Char"), data],
    );
    rfl_result(env, c("Nat"), length, lit(k))
}

/// `[Char.ofNat c₀, …] : List Char`.
fn char_list(codes: &[u64]) -> Expr {
    let list = |name: &str| Expr::const_(n(name), vec![Level::zero()]);
    codes
        .iter()
        .rev()
        .fold(Expr::app(list("List.nil"), c("Char")), |tail, &code| {
            Expr::apps(
                list("List.cons"),
                [c("Char"), Expr::app(c("Char.ofNat"), lit(code)), tail],
            )
        })
}

/// Every constant, inductive, constructor and recursor `after` holds and
/// `before` does not, each compared with what `reference` holds under the
/// same name. Returns the added constant names.
fn assert_added_match(
    before: &Environment,
    after: &Environment,
    reference: &Environment,
) -> Vec<Name> {
    let mut added = Vec::new();
    for info in after.constants() {
        if before.get_const(&info.name).is_some() {
            continue;
        }
        assert_eq!(
            Some(info),
            reference.get_const(&info.name),
            "{} differs from the reference prelude's",
            info.name
        );
        added.push(info.name.clone());
    }
    for ind in after.inductives() {
        if before.get_inductive(&ind.name).is_none() {
            assert_eq!(
                Some(ind),
                reference.get_inductive(&ind.name),
                "inductive {}",
                ind.name
            );
        }
    }
    for ctor in after.constructors() {
        if before.get_constructor(&ctor.name).is_none() {
            assert_eq!(
                Some(ctor),
                reference.get_constructor(&ctor.name),
                "constructor {}",
                ctor.name
            );
        }
    }
    for rec in after.recursors() {
        if before.get_recursor(&rec.name).is_none() {
            assert_eq!(
                Some(rec),
                reference.get_recursor(&rec.name),
                "recursor {}",
                rec.name
            );
        }
    }
    added
}

/// Every constant `env` holds that `reference` also holds is identical there.
fn assert_shared_match(env: &Environment, reference: &Environment, label: &str) {
    for info in env.constants() {
        if let Some(theirs) = reference.get_const(&info.name) {
            assert_eq!(
                info, theirs,
                "{label}: {} differs from the reference",
                info.name
            );
        }
    }
}

/// The three seeded definitions are `with_prelude`'s — declaration, closure
/// digest and boundary keys — and `Char.ofNat` is admitted by the pinned
/// `clean-prelude` row, beside a canonical `String.ofList`.
fn assert_seeded_as_prelude(env: &Environment, prelude: &Environment, label: &str) {
    for name in SEEDED {
        assert_eq!(
            env.get_const(&n(name)),
            prelude.get_const(&n(name)),
            "{label}: {name} declaration"
        );
        let mine = env.native_fold_closure(&n(name)).expect("closure");
        let theirs = prelude.native_fold_closure(&n(name)).expect("closure");
        assert_eq!(mine.digest, theirs.digest, "{label}: {name} closure digest");
        assert_eq!(
            mine.boundaries, theirs.boundaries,
            "{label}: {name} boundaries"
        );
    }
    assert_eq!(
        env.native_fold_verdict(&n("Char.ofNat")),
        Ok("clean-prelude"),
        "{label}: Char.ofNat must be admitted by the pinned clean-prelude row"
    );
}

/// The literal proofs a minimal environment needs, all admitted.
fn assert_literals_expand(env: &Environment, label: &str) {
    for (s, k) in [("", 0), ("ab", 2), ("a\0λ🙂", 4), ("é", 1), ("e\u{301}", 2)] {
        length_checks(env, s, k).unwrap_or_else(|e| panic!("{label}: length {s:?} = {k}: {e}"));
        assert!(
            length_checks(env, s, k + 1).is_err(),
            "{label}: length {s:?} = {}",
            k + 1
        );
    }
    let string = c("String");
    let data = |s: &str| Expr::app(c("String.data"), Expr::str_lit(s));
    let list_char = Expr::app(Expr::const_(n("List"), vec![Level::zero()]), c("Char"));
    rfl_result(
        env,
        list_char.clone(),
        data("a\0λ🙂"),
        char_list(&[97, 0, 955, 0x1F642]),
    )
    .unwrap_or_else(|e| panic!("{label}: the characters of \"a\\0λ🙂\": {e}"));
    assert!(
        rfl_result(env, list_char, data("ab"), char_list(&[98, 97])).is_err(),
        "{label}: \"ab\" must not expand to ['b', 'a']"
    );
    assert!(
        rfl_result(
            env,
            string,
            Expr::str_lit("a"),
            Expr::app(c("String.ofList"), char_list(&[98]))
        )
        .is_err(),
        "{label}: \"a\" = String.ofList ['b']"
    );
    // The seeded bodies themselves compute: a valid code point round-trips,
    // a surrogate maps to '\0' (Lean v4.30's `Char.ofNat`).
    let to_nat = |code: u64| Expr::app(c("Char.toNat"), Expr::app(c("Char.ofNat"), lit(code)));
    rfl_result(env, c("Nat"), to_nat(955), lit(955))
        .unwrap_or_else(|e| panic!("{label}: Char.toNat (Char.ofNat 955): {e}"));
    rfl_result(env, c("Nat"), to_nat(0xD800), lit(0))
        .unwrap_or_else(|e| panic!("{label}: Char.toNat (Char.ofNat 0xD800): {e}"));
    rfl_result(
        env,
        c("Nat"),
        Expr::app(c("Char.utf8Size"), Expr::app(c("Char.ofNat"), lit(0x1F642))),
        lit(4),
    )
    .unwrap_or_else(|e| panic!("{label}: Char.utf8Size '🙂': {e}"));
}

/// (a) A minimal environment REFUSES a string-literal proof, and admits it
/// once `init_char_of_nat` has run — nothing else changed.
#[test]
fn minimal_env_refuses_string_literals_until_init_char_of_nat() {
    for (label, shape) in shapes() {
        let mut env = shape();
        assert!(
            env.get_const(&n("Char.ofNat")).is_none(),
            "{label}: Char.ofNat pre-seeded"
        );
        assert!(
            matches!(
                env.native_fold_verdict(&n("Char.ofNat")),
                Err(FoldRefusal::Absent(_))
            ),
            "{label}: {:?}",
            env.native_fold_verdict(&n("Char.ofNat"))
        );
        assert!(
            length_checks(&env, "ab", 2).is_err(),
            "{label}: a literal expanded with no Char.ofNat in the environment"
        );
        env.init_char_of_nat().expect("init_char_of_nat");
        assert_literals_expand(&env, label);
    }
}

/// (b) Every declaration `init_char_of_nat` installs over a string-bearing
/// environment is the one `with_prelude` holds under that name, and each
/// seeded definition's closure digests to `with_prelude`'s — so `Char.ofNat`
/// is admitted by the pinned `clean-prelude` row, not by a new canonical
/// world. From a completely empty environment the seeded three are still
/// `with_prelude`'s; the rest of that environment is not compared, because
/// the bare `init_nat` path it starts from registers some `Nat` bitwise heads
/// as axioms that `with_prelude` later defines (pinned by
/// `native_fold_authority_tests::test_shiftright_axiom_does_not_compute`),
/// which is `init_nat`'s shape, not this initializer's.
#[test]
fn init_char_of_nat_installs_what_with_prelude_holds() {
    let prelude = Environment::with_prelude();
    for (label, shape) in shapes() {
        let before = shape();
        let mut after = before.clone();
        after.init_char_of_nat().expect("init_char_of_nat");
        let added = assert_added_match(&before, &after, &prelude);
        for name in SEEDED {
            assert!(added.contains(&n(name)), "{label}: {name} not installed");
        }
        assert_seeded_as_prelude(&after, &prelude, label);
        assert!(
            after.native_fold_verdict(&n("String.ofList")).is_ok(),
            "{label}: {:?}",
            after.native_fold_verdict(&n("String.ofList"))
        );
    }
    let mut empty = Environment::new();
    empty
        .init_char_of_nat()
        .expect("init_char_of_nat on Environment::new()");
    assert_seeded_as_prelude(&empty, &prelude, "empty");
}

/// (c) Idempotent, a no-op on both preludes, and independent of whether it
/// runs before or after the other focused initializers.
#[test]
fn init_char_of_nat_is_idempotent_and_order_independent() {
    let prelude = Environment::with_prelude();

    // A no-op on `with_prelude`, which already holds all of it.
    let mut again = prelude.clone();
    again
        .init_char_of_nat()
        .expect("init_char_of_nat on with_prelude");
    assert_eq!(again.num_constants(), prelude.num_constants());
    assert_shared_match(&again, &prelude, "with_prelude");

    // A no-op in import mode: Char is withheld there and nothing is seeded.
    let import = Environment::try_with_prelude_for_import().expect("import prelude");
    let mut import_again = import.clone();
    import_again
        .init_char_of_nat()
        .expect("init_char_of_nat in import mode");
    assert_eq!(import_again.num_constants(), import.num_constants());
    assert_shared_match(&import_again, &import, "import prelude");
    assert!(import_again.get_const(&n("Char.ofNat")).is_none());

    for (label, shape) in shapes() {
        // Twice is once.
        let mut once = shape();
        once.init_char_of_nat().expect("first call");
        let mut twice = once.clone();
        twice.init_char_of_nat().expect("second call");
        assert_eq!(twice.num_constants(), once.num_constants(), "{label}");
        assert_shared_match(&twice, &once, label);
        assert_seeded_as_prelude(&twice, &prelude, label);
    }

    // First, before any other initializer, then ty's whole shape on top: the
    // same environment as the call made last, and the same seeded three.
    let mut first = Environment::new();
    first.init_char_of_nat().expect("init_char_of_nat first");
    first.init_eq().expect("init_eq");
    first.init_bool().expect("init_bool");
    first.init_int().expect("init_int");
    first.init_string().expect("init_string");
    first.init_list().expect("init_list");
    first.init_unit().expect("init_unit");
    first.init_option().expect("init_option");
    first.init_except_t().expect("init_except_t");
    first.init_list_contains().expect("init_list_contains");
    first.init_prod().expect("init_prod");
    let mut last = ty_shape_env();
    last.init_char_of_nat().expect("init_char_of_nat last");
    assert_eq!(first.num_constants(), last.num_constants());
    assert_shared_match(&first, &last, "called first vs last");
    assert_seeded_as_prelude(&first, &prelude, "called first");
    assert_literals_expand(&first, "called first");
}

/// (d) The call launders no impostor. A user's `Char.ofNat` — an axiom
/// declared before the call, or a definition swapped in after it — is left in
/// place (the seed is lookup-guarded) and the authority check still refuses
/// the literal expansion through it.
#[test]
fn init_char_of_nat_keeps_the_spoofing_guard() {
    // An axiom declared first: the seed steps aside, and an axiom never folds.
    let mut env = bare_string_env();
    env.add_decl(Declaration::Axiom {
        name: n("Char.ofNat"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, c("Nat"), c("Char")),
    })
    .expect("a user may declare Char.ofNat");
    env.init_char_of_nat()
        .expect("init_char_of_nat beside a user Char.ofNat");
    assert_eq!(
        env.native_fold_verdict(&n("Char.ofNat")),
        Err(FoldRefusal::HeadNotDefinition(n("Char.ofNat")))
    );
    assert!(
        env.get_const(&n("Char.ofNatAux")).is_none(),
        "the seed must step aside whole"
    );
    assert!(
        length_checks(&env, "ab", 2).is_err(),
        "a literal expanded through an axiom"
    );

    // A definition that forgets its argument, swapped in after the call: the
    // attack of `attack_string_literal_expansion_over_user_char_of_nat`, on the
    // minimal environment and with the initializer called again on top.
    let mut env = bare_string_env();
    env.init_char_of_nat().expect("init_char_of_nat");
    let canonical = env
        .get_const(&n("Char.ofNat"))
        .and_then(|ci| ci.value.clone())
        .expect("seeded Char.ofNat");
    assert!(env.forget_decl(&n("Char.ofNat")));
    env.add_decl(Declaration::Definition {
        name: n("Char.ofNat"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, c("Nat"), c("Char")),
        value: Expr::lam(
            BinderInfo::Default,
            c("Nat"),
            Expr::app(canonical, lit(122)),
        ),
        is_reducible: true,
    })
    .expect("user Char.ofNat");
    env.init_char_of_nat()
        .expect("init_char_of_nat over a user Char.ofNat");
    assert!(
        matches!(
            env.native_fold_verdict(&n("Char.ofNat")),
            Err(FoldRefusal::NotCanonical { .. })
        ),
        "{:?}",
        env.native_fold_verdict(&n("Char.ofNat"))
    );
    assert!(
        rfl_result(
            &env,
            c("String"),
            Expr::str_lit("a"),
            Expr::app(c("String.ofList"), char_list(&[98]))
        )
        .is_err(),
        "ATTACK ACCEPTED: \"a\" = String.ofList [Char.ofNat 98] through a user Char.ofNat"
    );
    assert!(
        length_checks(&env, "ab", 2).is_err(),
        "a literal expanded through an impostor"
    );
}

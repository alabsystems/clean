// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end probe: CROSS-MODULE TRANSITIVE import + usage.
//!
//! The B43/B44/B45 audits each found a single-hop concern: a clean-elab
//! declaration elaborated against *one* imported decl (a `match` on an imported
//! inductive, a projection on an imported structure, a method call on an
//! imported instance). This probe checks the *transitive* concern across module
//! boundaries:
//!
//! ```text
//!   module A  :  inductive MyBool ; def myNot : MyBool -> MyBool   (imported .olean)
//!   module B  :  import A ; def negThenTrue (b) := myNot (myNot b)  (imported decl
//!                                                                    referencing A)
//!   fresh     :  def chain (b) := negThenTrue b                     (clean-elab,
//!                                                                    references B,
//!                                                                    transitively A)
//! ```
//!
//! When a *fresh* elaboration has BOTH A and B loaded, does a clean-elab decl
//! that uses B's decl (which transitively references A's decl) resolve and
//! reduce correctly all the way down the chain?  `chain b` must delta-unfold to
//! `negThenTrue b`, which must delta-unfold to `myNot (myNot b)` (module B's
//! body, referencing module A's imported `myNot`), which must delta-unfold +
//! iota-reduce through `MyBool.rec` to the right `MyBool` constructor.
//!
//! ## How the modules are composed
//!
//! Module A is the checked-in Lean 4 v4.13.0 `Inductive.olean` fixture
//! (`inductive MyBool | myTrue | myFalse` and the Lean-compiled
//! `def myNot : MyBool -> MyBool | .myTrue => .myFalse | .myFalse => .myTrue`),
//! loaded with `clean_olean::load_olean_file`.
//!
//! Module B is synthesized *into the same environment* with the very kernel
//! primitive the importer's `load_register` path uses for a plain imported
//! `def` — `Environment::add_decl(Declaration::Definition { .. })` with a real
//! body. This is faithful to how a second `.olean` module's `def` lands: a plain
//! Lean function/constant carrying its body, registered into the shared env on
//! top of A. (The checked-in fixtures are each a single self-contained module,
//! so there is no two-file A->B->C `.olean` chain to load; per the probe brief we
//! therefore synthesize B's decl directly, exactly as the importer would
//! register it, to exercise the transitive reference + reduction.)
//!
//! The point of interest is the *third* layer: a brand-new clean-elab
//! declaration, elaborated and kernel-checked against an environment where both
//! A and B are present, that calls B's `negThenTrue` (never mentioning A's
//! `myNot` directly) and must still reduce correctly through the whole chain.

use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_kernel::env::{ConstantKind, Environment};
use clean_kernel::{BinderInfo, Declaration, Expr, ExprKind, Name, TypeChecker};
use clean_olean::load_olean_file;
use clean_parser::parse_file;
use std::path::PathBuf;

/// Absolute path to the checked-in `MyBool` inductive `.olean` fixture, used as
/// "module A" (carries `MyBool`, its constructors/eliminators, and the
/// Lean-compiled `def myNot`).
fn module_a_fixture_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/olean/v4.13.0/custom/Inductive.olean")
}

fn const_(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

/// Reduce `expr` to weak-head normal form and, if the head is a `Const`, return
/// its name. Used to observe which constructor the transitive chain selects.
fn whnf_head_const(env: &Environment, expr: &Expr) -> Option<String> {
    let tc = TypeChecker::new(env);
    let reduced = tc.whnf(expr);
    match reduced.kind() {
        ExprKind::Const(name, _) => Some(name.to_string()),
        _ => None,
    }
}

/// Load "module A" (the `MyBool` + `myNot` fixture) into a fresh environment.
fn load_module_a() -> Environment {
    let path = module_a_fixture_path();
    let mut env = Environment::default();
    let summary = load_olean_file(&mut env, &path)
        .unwrap_or_else(|e| panic!("loading module A ({}) should succeed: {e}", path.display()));
    assert!(
        summary.added_constants > 0,
        "module A fixture should add constants"
    );
    env
}

/// Register "module B" into `env` (which must already contain module A). B's
/// `def negThenTrue (b : MyBool) : MyBool := myNot (myNot b)` is added with the
/// same primitive the importer uses for a plain imported `def`
/// (`add_decl(Declaration::Definition { .. })` with a real body), so it is a
/// faithful stand-in for a second `.olean` module whose `def` references A's
/// imported `myNot` / `MyBool`.
///
/// Body (with `b` as `bvar 0` under the single binder): `myNot (myNot b)`.
fn register_module_b(env: &mut Environment) {
    let mybool = const_("MyBool");
    // type: MyBool -> MyBool
    let ty = Expr::pi(BinderInfo::Default, mybool.clone(), mybool.clone());
    // value: fun (b : MyBool) => myNot (myNot b)
    let inner = Expr::app(const_("myNot"), Expr::bvar(0));
    let body = Expr::app(const_("myNot"), inner);
    let value = Expr::lam(BinderInfo::Default, mybool, body);
    env.add_decl(Declaration::Definition {
        name: Name::from_string("negThenTrue"),
        level_params: vec![],
        type_: ty,
        value,
        is_reducible: true,
    })
    .unwrap_or_else(|e| panic!("registering module B's negThenTrue should succeed: {e:?}"));
}

/// Elaborate and register a sequence of declarations from `source`, threading a
/// shared `FileContext`. `elaborate_decl_and_register` runs the full kernel type
/// check for each definition.
fn elaborate_decls_into(env: &mut Environment, source: &str) {
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).expect("source should parse");
    for (i, decl) in decls.iter().enumerate() {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        elaborate_decl_and_register(env, &processed)
            .unwrap_or_else(|e| panic!("declaration {i} should elaborate and kernel-check: {e}"));
    }
}

// =============================================================================
// Test 1: precondition — with A loaded and B registered on top, both modules'
// decls are present with unfoldable bodies, and B's body genuinely references
// A's decl. This pins that the transitive chain we are about to reduce is real
// (B -> A), not short-circuited.
// =============================================================================

#[test]
fn test_cross_module_b_references_a_with_unfoldable_bodies() {
    let mut env = load_module_a();

    // Module A's `myNot` must be imported with an unfoldable body (delta).
    let my_not = env
        .get_const(&Name::from_string("myNot"))
        .expect("module A's myNot should be imported");
    assert_eq!(my_not.kind, ConstantKind::Definition);
    assert!(
        my_not.value.is_some(),
        "module A's myNot must carry its body so the chain can delta-unfold into A"
    );

    register_module_b(&mut env);

    // Module B's `negThenTrue` is present with a body that references A's myNot.
    let neg = env
        .get_const(&Name::from_string("negThenTrue"))
        .expect("module B's negThenTrue should be registered");
    assert_eq!(neg.kind, ConstantKind::Definition);
    let neg_body = neg
        .value
        .as_ref()
        .expect("negThenTrue is a definition with a body");
    assert!(
        neg_body
            .collect_constants()
            .contains(&Name::from_string("myNot")),
        "module B's body must transitively reference module A's myNot, got: {:?}",
        neg_body.collect_constants()
    );
}

// =============================================================================
// Test 2: control — module B's decl, used DIRECTLY (no fresh elaboration),
// reduces correctly through the transitive chain B -> A. negThenTrue = not . not
// is the identity on a two-element Bool, so each constructor maps to itself.
// This isolates any failure in Test 3 to the fresh-elaboration layer rather than
// to the cross-module reduction itself.
// =============================================================================

#[test]
fn test_cross_module_b_decl_reduces_through_a_directly() {
    let mut env = load_module_a();
    register_module_b(&mut env);

    // negThenTrue myTrue -> myNot (myNot myTrue) -> myNot myFalse -> myTrue.
    let neg_true = Expr::app(const_("negThenTrue"), const_("MyBool.myTrue"));
    assert_eq!(
        whnf_head_const(&env, &neg_true).as_deref(),
        Some("MyBool.myTrue"),
        "negThenTrue myTrue must reduce to myTrue (not(not(true)) = true) through module A's myNot"
    );

    // negThenTrue myFalse -> myNot (myNot myFalse) -> myNot myTrue -> myFalse.
    let neg_false = Expr::app(const_("negThenTrue"), const_("MyBool.myFalse"));
    assert_eq!(
        whnf_head_const(&env, &neg_false).as_deref(),
        Some("MyBool.myFalse"),
        "negThenTrue myFalse must reduce to myFalse (not(not(false)) = false) through module A's myNot"
    );
}

// =============================================================================
// Test 3: THE PROBE. A FRESH clean-elab def that uses module B's decl (which
// transitively references module A's decl) must kernel-check and reduce
// correctly down the whole chain `chain -> negThenTrue -> myNot -> MyBool.rec`.
// The fresh def never names module A directly; the transitive reference must
// resolve and reduce purely through B.
// =============================================================================

#[test]
fn test_fresh_def_over_module_b_reduces_through_transitive_chain() {
    let mut env = load_module_a();
    register_module_b(&mut env);

    // A brand-new clean-elab declaration that calls ONLY module B's `negThenTrue`
    // (which itself calls module A's `myNot`). `elaborate_decl_and_register` runs
    // the full kernel type check, so reaching past it proves the fresh def
    // type-checked against the cross-module references.
    elaborate_decls_into(&mut env, "def chain (b : MyBool) : MyBool := negThenTrue b");

    let info = env
        .get_const(&Name::from_string("chain"))
        .expect("chain should be registered after elaboration");
    let body = info
        .value
        .as_ref()
        .expect("chain is a definition with a body");
    let referenced = body.collect_constants();
    // The fresh def must go through module B's decl — the transitive edge is real.
    assert!(
        referenced.contains(&Name::from_string("negThenTrue")),
        "chain's body must call module B's negThenTrue (the transitive edge), got: {referenced:?}"
    );

    // The payoff: reduce the fresh def applied to each constructor. The reduction
    // must traverse chain -> negThenTrue (module B) -> myNot (module A) ->
    // MyBool.rec, landing on the correct constructor. A failure to resolve the
    // transitive reference, or a stuck redex anywhere in the chain, would surface
    // here as the wrong head (or a non-`Const` head) rather than passing silently.
    let chain_true = Expr::app(const_("chain"), const_("MyBool.myTrue"));
    assert_eq!(
        whnf_head_const(&env, &chain_true).as_deref(),
        Some("MyBool.myTrue"),
        "chain myTrue must reduce to myTrue through the transitive chain \
         (fresh clean-elab def -> module B -> module A -> recursor)"
    );

    let chain_false = Expr::app(const_("chain"), const_("MyBool.myFalse"));
    assert_eq!(
        whnf_head_const(&env, &chain_false).as_deref(),
        Some("MyBool.myFalse"),
        "chain myFalse must reduce to myFalse through the transitive chain"
    );
}

// =============================================================================
// Test 4: a STRONGER fresh-elaboration probe — the fresh clean-elab def composes
// module B's decl with module A's decl DIRECTLY, so the two cross-module edges
// must compose in one freshly-elaborated body. `mix b := myNot (negThenTrue b)`
// references BOTH A (`myNot`) and B (`negThenTrue`) at the fresh layer. Since
// negThenTrue is the identity, `mix` is just `myNot`, so it must flip each
// constructor — a wrong wiring of either edge would invert or stick the result.
// =============================================================================

#[test]
fn test_fresh_def_composing_both_modules_reduces_correctly() {
    let mut env = load_module_a();
    register_module_b(&mut env);

    elaborate_decls_into(
        &mut env,
        "def mix (b : MyBool) : MyBool := myNot (negThenTrue b)",
    );

    let info = env
        .get_const(&Name::from_string("mix"))
        .expect("mix should be registered after elaboration");
    let referenced = info
        .value
        .as_ref()
        .expect("mix is a definition with a body")
        .collect_constants();
    assert!(
        referenced.contains(&Name::from_string("myNot"))
            && referenced.contains(&Name::from_string("negThenTrue")),
        "mix's body must reference BOTH module A's myNot and module B's negThenTrue, \
         got: {referenced:?}"
    );

    // mix b = myNot (negThenTrue b) = myNot b  (negThenTrue is identity), so each
    // constructor flips: myTrue -> myFalse, myFalse -> myTrue.
    let mix_true = Expr::app(const_("mix"), const_("MyBool.myTrue"));
    assert_eq!(
        whnf_head_const(&env, &mix_true).as_deref(),
        Some("MyBool.myFalse"),
        "mix myTrue must reduce to myFalse (myNot(negThenTrue myTrue) = myNot myTrue = myFalse)"
    );
    let mix_false = Expr::app(const_("mix"), const_("MyBool.myFalse"));
    assert_eq!(
        whnf_head_const(&env, &mix_false).as_deref(),
        Some("MyBool.myTrue"),
        "mix myFalse must reduce to myTrue (myNot(negThenTrue myFalse) = myNot myFalse = myTrue)"
    );
}

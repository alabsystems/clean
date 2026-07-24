// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end: MULTI-STEP / transitive coercion through IMPORTED `Coe` instances.
//!
//! B46 (`integration/import_e2e_coercion_tests.rs`) validated a *single* imported
//! `Coe A B` insertion: an `A` used where a `B` is expected finds the imported
//! `Coe A B` instance and reduces through it. This probe goes one step further:
//! it builds *two* imported `Coe` instances — `Coe A B` and `Coe B C` — and uses
//! an `A` where a `C` is expected. For that to elaborate, coercion insertion must
//! *compose* the two steps: `A.a : A` ⇝ `coe_BC (coe_AB A.a) : C`.
//!
//! ## What "imported" means here (and why we synthesize it by hand)
//!
//! A real Lean `.olean` carries no clean-side native-`class`-command metadata.
//! The importer (`clean_olean::import::load_register`) materializes a typeclass
//! purely through the *kernel* registries (see the B46 file for the full
//! analysis):
//!
//! 1. The `@[class]` structure `Coe` is a plain single-constructor inductive
//!    (`register_class`, empty `out_params`/`semi_out_params`). No
//!    `register_structure_fields` table is created.
//! 2. The method projection (`Coe.coe`) is a plain imported `def` whose body is a
//!    kernel `Proj`.
//! 3. Each instance is registered via `register_instance` with
//!    `type_: None, value: None`; the elaborator reconstructs the instance from
//!    `env.get_const(name)` (`infer/elab_init.rs::init_instances_from_env`).
//!
//! We reproduce exactly that configuration with the same primitive kernel APIs
//! the importer calls, and *deliberately do not* register any clean-side
//! coercion-attribute / structure-field metadata. So an imported `Coe` instance
//! is only visible through the kernel instance registry.
//!
//! ## The carriers, the class, and the coercions
//!
//! Three carriers with *distinct nullary values* so a wrong coercion / wrong
//! projection / wrong chaining order is observable in the reduced head:
//!   `A : Type` with value `A.a`
//!   `B : Type` with values `B.b1`, `B.b2`
//!   `C : Type` with values `C.c1`, `C.c2`
//!
//! Class `Coe (α β : Type)` has a single method field `coe : α → β`, with
//! projection `Coe.coe : {α β : Type} → [self : Coe α β] → α → β`, body `self.0`.
//!
//! Coercion functions are chosen so the *composition* lands on a value that is
//! distinct from every intermediate, and so a wrong order or a missed step is
//! detectable:
//!   `aToB : A → B := fun _ => B.b2`   (A.a ⇝ B.b2)
//!   `bToC : B → C := fun b => match b with | B.b1 => C.c1 | B.b2 => C.c2`
//!     so `bToC B.b2 = C.c2`, i.e. the full chain `A.a ⇝ B.b2 ⇝ C.c2`.
//!
//! Instances `instCoeAB : Coe A B` and `instCoeBC : Coe B C`.
//!
//! ## The end-to-end def under test
//!
//! ```text
//! def coercedC : C := (A.a : C)   -- A.a : A used where C is expected
//! ```
//!
//! `(A.a : C)` makes the elaborator unify `A` with the expected `C`; that fails,
//! so it must consult coercion insertion. There is **no** direct `Coe A C`
//! instance, so a *single-step* coercion search cannot satisfy it — only chaining
//! `Coe A B` then `Coe B C` works. If clean composes the chain, `coercedC`
//! kernel-checks and reduces to `C.c2`. If clean only does single-step imported
//! coercion, this elaboration fails.
//!
//! ## What this probe found, and the fix
//!
//! Before this change, clean's import-path coercion (`infer/coercion.rs::try_coerce`)
//! resolved only a *single-step* `Coe <from> <to>` instance: it built the goal
//! `Coe A C`, found no direct instance, and reported a type mismatch. So `(A.a : C)`
//! failed to elaborate even though `Coe A B` and `Coe B C` were both imported.
//!
//! The fix adds a transitive-chain fallback (`try_coerce_coe_chain`) that runs
//! only after the single-step lookup misses: it BFS-composes the registered
//! `Coe` instances along a `from -> … -> to` path and folds the per-step
//! `Coe.coe` applications, producing
//!   `Coe.coe B C instCoeBC (Coe.coe A B instCoeAB A.a)`.
//! The kernel re-checks the produced term, so an ill-typed composition is
//! rejected rather than passing silently, and unreachable targets (Test 5) are
//! still refused.
//!
//! Test 2 (kernel-reduction control) and Test 3 (single-step lock-in) assert the
//! genuinely-correct behavior; Test 4 pins the composed chain; Test 5 is the
//! negative control that the chain search does not over-fire.

use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_kernel::env::Environment;
use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};
use clean_kernel::{
    BinderInfo, Declaration, Expr, ExprKind, KernelClassInfo, KernelInstanceInfo, Name, TypeChecker,
};
use clean_parser::parse_file;

fn const_(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

/// Reduce `expr` to weak-head normal form and, if the head is a `Const`, return
/// its name. Used to observe which constructor a coercion reduces to.
fn whnf_head_const(env: &Environment, expr: &Expr) -> Option<String> {
    let tc = TypeChecker::new(env);
    let reduced = tc.whnf(expr);
    match reduced.kind() {
        ExprKind::Const(name, _) => Some(name.to_string()),
        _ => None,
    }
}

/// Add a nullary single-constructor enum inductive `name : Type` with the given
/// constructor `: name`.
fn add_unit_enum(env: &mut Environment, name: &str, ctor: &str) {
    let ind = Name::from_string(name);
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: ind.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string(ctor),
                type_: Expr::const_(ind, vec![]),
            }],
        }],
    };
    env.add_inductive(decl)
        .unwrap_or_else(|e| panic!("add_inductive {name} should succeed: {e:?}"));
}

/// Add a nullary two-constructor enum inductive `name : Type`.
fn add_enum(env: &mut Environment, name: &str, c0: &str, c1: &str) {
    let ind = Name::from_string(name);
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: ind.clone(),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string(c0),
                    type_: Expr::const_(ind.clone(), vec![]),
                },
                Constructor {
                    name: Name::from_string(c1),
                    type_: Expr::const_(ind, vec![]),
                },
            ],
        }],
    };
    env.add_inductive(decl)
        .unwrap_or_else(|e| panic!("add_inductive {name} should succeed: {e:?}"));
}

/// The `Coe` class type `Type → Type → Type`.
fn coe_class_type() -> Expr {
    Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_()),
    )
}

/// Build `Coe`, `Coe.mk`, and the `Coe.coe` projection exactly the way an
/// `.olean` import materializes them: a single-constructor inductive with a
/// kernel-`Proj` projection function, registered via `register_class` only (no
/// clean-side `structure_fields` table).
fn add_coe_class(env: &mut Environment) {
    let coe = Name::from_string("Coe");

    // Coe.mk : (α β : Type) → (α → β) → Coe α β
    // In the constructor scope (under α, β): α = bvar 1, β = bvar 0. The field
    // `α → β` adds one binder, so inside the arrow body β = bvar 1 and α = bvar 2.
    let field_arrow = Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::bvar(1));
    let mk_ty = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(
            BinderInfo::Default,
            Expr::type_(),
            Expr::pi(
                BinderInfo::Default,
                field_arrow,
                // Result `Coe α β`: under (α, β, field), α = bvar 2, β = bvar 1.
                Expr::app(
                    Expr::app(Expr::const_(coe.clone(), vec![]), Expr::bvar(2)),
                    Expr::bvar(1),
                ),
            ),
        ),
    );
    let coe_decl = InductiveDecl {
        level_params: vec![],
        num_params: 2,
        types: vec![InductiveType {
            name: coe.clone(),
            type_: coe_class_type(),
            constructors: vec![Constructor {
                name: Name::from_string("Coe.mk"),
                type_: mk_ty,
            }],
        }],
    };
    env.add_inductive(coe_decl)
        .unwrap_or_else(|e| panic!("add_inductive Coe should succeed: {e:?}"));

    // Coe.coe : {α β : Type} → [self : Coe α β] → α → β := fun {α β} [self] => self.0
    let coe_self_ty = Expr::app(
        Expr::app(Expr::const_(coe.clone(), vec![]), Expr::bvar(1)),
        Expr::bvar(0),
    );
    let chosen_ty = Expr::pi(
        BinderInfo::Implicit,
        Expr::type_(),
        Expr::pi(
            BinderInfo::Implicit,
            Expr::type_(),
            Expr::pi(
                BinderInfo::InstImplicit,
                coe_self_ty,
                // result `α → β`: under (α, β, self), α = bvar 2, β = bvar 1.
                Expr::pi(BinderInfo::Default, Expr::bvar(2), Expr::bvar(2)),
            ),
        ),
    );
    let chosen_self_ty_val = Expr::app(
        Expr::app(Expr::const_(coe.clone(), vec![]), Expr::bvar(1)),
        Expr::bvar(0),
    );
    let chosen_val = Expr::lam(
        BinderInfo::Implicit,
        Expr::type_(),
        Expr::lam(
            BinderInfo::Implicit,
            Expr::type_(),
            Expr::lam(
                BinderInfo::InstImplicit,
                chosen_self_ty_val,
                Expr::proj(coe.clone(), 0, Expr::bvar(0)),
            ),
        ),
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string("Coe.coe"),
        level_params: vec![],
        type_: chosen_ty,
        value: chosen_val,
        is_reducible: true,
    })
    .unwrap_or_else(|e| panic!("add_decl Coe.coe should succeed: {e:?}"));

    // register_class, import-style (no out_params, no structure_fields).
    env.register_class(KernelClassInfo {
        name: coe,
        num_params: 2,
        out_params: vec![],
        semi_out_params: vec![],
    });
}

/// Register an imported instance `inst_name : Coe <src> <tgt> := Coe.mk src tgt coe_fn`
/// exactly the way the importer does: the constant is present in the env, and the
/// instance is registered with `type_: None, value: None` so the elaborator must
/// reconstruct it from `env.get_const(name)`.
fn add_coe_instance(env: &mut Environment, inst_name: &str, src: &str, tgt: &str, coe_fn: &str) {
    let coe = Name::from_string("Coe");
    let inst_val = Expr::app(
        Expr::app(Expr::app(const_("Coe.mk"), const_(src)), const_(tgt)),
        const_(coe_fn),
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string(inst_name),
        level_params: vec![],
        type_: Expr::app(
            Expr::app(Expr::const_(coe.clone(), vec![]), const_(src)),
            const_(tgt),
        ),
        value: inst_val,
        is_reducible: true,
    })
    .unwrap_or_else(|e| panic!("add_decl {inst_name} should succeed: {e:?}"));

    env.register_instance(KernelInstanceInfo {
        name: Name::from_string(inst_name),
        class_name: coe,
        priority: clean_kernel::DEFAULT_INSTANCE_PRIORITY,
        type_: None,
        value: None,
    });
}

/// Build an environment with the imported `Coe` class, three carriers
/// (`A`, `B`, `C`), the coercion functions, and the two imported instances
/// `Coe A B` and `Coe B C` — and NO direct `Coe A C` instance, so that reaching
/// `C` from `A` requires *composing* the two imported instances.
fn imported_coe_chain_env() -> Environment {
    let mut env = Environment::new();

    // Carriers with distinct nullary values.
    add_unit_enum(&mut env, "A", "A.a");
    add_enum(&mut env, "B", "B.b1", "B.b2");
    add_enum(&mut env, "C", "C.c1", "C.c2");

    add_coe_class(&mut env);

    // aToB : A → B := fun _ => B.b2
    env.add_decl(Declaration::Definition {
        name: Name::from_string("aToB"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, const_("A"), const_("B")),
        value: Expr::lam(BinderInfo::Default, const_("A"), const_("B.b2")),
        is_reducible: true,
    })
    .unwrap_or_else(|e| panic!("add_decl aToB should succeed: {e:?}"));

    // bToC : B → C := fun b => B.rec (motive := fun _ => C) C.c1 C.c2 b
    //   so bToC B.b1 = C.c1 and bToC B.b2 = C.c2. We build it via the recursor so
    //   the chain's second step genuinely *depends on* the value produced by the
    //   first step (a wrong intermediate value would land on the wrong C ctor).
    //   B.rec : {motive : B → Sort u} → motive B.b1 → motive B.b2 → (t : B) → motive t
    //   Here motive := fun _ => C (a constant motive), so:
    //   bToC := fun b => @B.rec (fun _ => C) C.c1 C.c2 b
    let motive = Expr::lam(BinderInfo::Default, const_("B"), const_("C"));
    // The motive `fun _ : B => C` returns `C : Type = Sort 1`, so the recursor's
    // universe parameter is `1` (Succ Zero), not `0`.
    let elim_level = clean_kernel::Level::succ(clean_kernel::Level::zero());
    let b_rec_applied = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    // B.rec carries one Sort universe level param.
                    Expr::const_(Name::from_string("B.rec"), vec![elim_level]),
                    motive,
                ),
                const_("C.c1"),
            ),
            const_("C.c2"),
        ),
        Expr::bvar(0),
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string("bToC"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, const_("B"), const_("C")),
        value: Expr::lam(BinderInfo::Default, const_("B"), b_rec_applied),
        is_reducible: true,
    })
    .unwrap_or_else(|e| panic!("add_decl bToC should succeed: {e:?}"));

    add_coe_instance(&mut env, "instCoeAB", "A", "B", "aToB");
    add_coe_instance(&mut env, "instCoeBC", "B", "C", "bToC");

    env
}

/// Elaborate and register `source` against `env`, threading a `FileContext`.
/// `elaborate_decl_and_register` runs the full kernel type check, so reaching the
/// end means every body kernel-checked.
fn elaborate_decls_into(env: &mut Environment, source: &str) -> Result<(), String> {
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    for (i, decl) in decls.iter().enumerate() {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        elaborate_decl_and_register(env, &processed)
            .map_err(|e| format!("declaration {i} failed to elaborate/kernel-check: {e}"))?;
    }
    Ok(())
}

// =============================================================================
// Test 1: precondition — the imported class + projection + two instances were
// registered the way the importer does, with NO clean-side coercion-attribute /
// structure-field table, and crucially NO direct `Coe A C` instance. This pins
// that reaching `C` from `A` genuinely requires composing two imported steps.
// =============================================================================

#[test]
fn test_imported_coe_chain_env_has_no_direct_a_to_c_instance() {
    let env = imported_coe_chain_env();
    let coe = Name::from_string("Coe");

    assert!(
        env.is_class(&coe),
        "Coe should be a registered class (via register_class, import-style)"
    );
    assert!(
        env.get_structure_field_names(&coe).is_none(),
        "imported class must NOT carry a clean-side structure_fields table"
    );

    let instances = env.get_class_instances(&coe);
    assert_eq!(
        instances.len(),
        2,
        "exactly two Coe instances are registered (A->B and B->C)"
    );
    assert!(
        instances
            .iter()
            .all(|i| i.type_.is_none() && i.value.is_none()),
        "imported instances carry no type_/value; the elaborator reconstructs \
         them from env.get_const (the import path)"
    );

    // The instance constants and the projection must be present, but there is no
    // `instCoeAC` — a direct A->C coercion is impossible without composing.
    for c in ["instCoeAB", "instCoeBC", "Coe.coe", "aToB", "bToC"] {
        assert!(
            env.get_const(&Name::from_string(c)).is_some(),
            "{c} must be present in the imported env"
        );
    }
    assert!(
        env.get_const(&Name::from_string("instCoeAC")).is_none(),
        "there must be NO direct Coe A C instance — A->C requires chaining A->B->C"
    );
}

// =============================================================================
// Test 2: control — composing the imported projections by hand at the KERNEL
// level reduces correctly. This isolates any failure in the chain probe (Test 4)
// to coercion *insertion* (elaboration), not to kernel reduction or the
// hand-built layout. Distinct values make every step observable.
//   Coe.coe A B instCoeAB A.a                  ⇝ aToB A.a            ⇝ B.b2
//   Coe.coe B C instCoeBC (that)               ⇝ bToC B.b2           ⇝ C.c2
// =============================================================================

#[test]
fn test_imported_coe_chain_kernel_composition_reduces_to_c2() {
    let env = imported_coe_chain_env();

    // Step 1: A.a ⇝ B.b2
    let step_ab = Expr::app(
        Expr::app(
            Expr::app(Expr::app(const_("Coe.coe"), const_("A")), const_("B")),
            const_("instCoeAB"),
        ),
        const_("A.a"),
    );
    assert_eq!(
        whnf_head_const(&env, &step_ab).as_deref(),
        Some("B.b2"),
        "Coe.coe A B instCoeAB A.a must reduce to B.b2"
    );

    // Step 2 composed on top of step 1: (A.a ⇝ B.b2) ⇝ C.c2
    let step_abc = Expr::app(
        Expr::app(
            Expr::app(Expr::app(const_("Coe.coe"), const_("B")), const_("C")),
            const_("instCoeBC"),
        ),
        step_ab,
    );
    assert_eq!(
        whnf_head_const(&env, &step_abc).as_deref(),
        Some("C.c2"),
        "composing Coe.coe B C over Coe.coe A B on A.a must reduce to C.c2"
    );

    // Sanity: the intermediate B.b1 path would have gone to C.c1, so the chain's
    // dependence on the *value* (B.b2, not B.b1) is what selects C.c2. Confirm
    // bToC B.b1 = C.c1 so a wrong intermediate would be observable.
    let b1_to_c = Expr::app(const_("bToC"), const_("B.b1"));
    assert_eq!(
        whnf_head_const(&env, &b1_to_c).as_deref(),
        Some("C.c1"),
        "bToC B.b1 must reduce to C.c1 — confirms the chain's value-dependence"
    );
}

// =============================================================================
// Test 3: single-step lock-in (the B46 invariant, re-pinned in the chain env).
// An `A` used where a `B` is expected must insert the imported `Coe A B`
// coercion and reduce to B.b2 — proving the chain env hasn't regressed the
// single-step imported-coercion behavior that B46 established.
// =============================================================================

#[test]
fn test_imported_coe_single_step_a_to_b_reduces_to_b2() {
    let mut env = imported_coe_chain_env();

    elaborate_decls_into(&mut env, "def coercedB : B := (A.a : B)")
        .expect("single-step imported Coe A B coercion must elaborate and kernel-check");

    let body = env
        .get_const(&Name::from_string("coercedB"))
        .and_then(|i| i.value.clone())
        .expect("coercedB body");
    let referenced = body.collect_constants();
    assert!(
        referenced.contains(&Name::from_string("Coe.coe"))
            && referenced.contains(&Name::from_string("aToB")),
        "coercedB must go through the imported Coe.coe projection and the A->B \
         coercion fn aToB, got: {referenced:?}"
    );
    assert!(
        !referenced.contains(&Name::from_string("bToC")),
        "a single A->B coercion must NOT pull in the B->C step bToC, got: {referenced:?}"
    );

    assert_eq!(
        whnf_head_const(&env, &const_("coercedB")).as_deref(),
        Some("B.b2"),
        "coercedB := (A.a : B) must reduce to B.b2 through the imported Coe A B coercion"
    );
}

// =============================================================================
// Test 4: THE PROBE / regression guard — transitive imported coercion. An `A`
// used where a `C` is expected has NO direct `Coe A C` instance; satisfying it
// requires *composing* the imported `Coe A B` and `Coe B C` instances.
//
// Before the fix, clean's import-path coercion (`infer/coercion.rs::try_coerce`)
// resolved a single-step `Coe <from> <to>` instance only, so `(A.a : C)` failed
// to elaborate (no direct `Coe A C`). The chain fallback added to `try_coerce`
// (`try_coerce_coe_chain`) now BFS-composes the imported steps, producing
//   `Coe.coe B C instCoeBC (Coe.coe A B instCoeAB A.a)`,
// which the kernel re-checks and reduces to `C.c2` (NOT `C.c1`, which would mean
// a wrong intermediate B value was produced).
// =============================================================================

#[test]
fn test_imported_coe_chain_a_to_c_composes_both_steps_and_reduces_to_c2() {
    let mut env = imported_coe_chain_env();

    elaborate_decls_into(&mut env, "def coercedC : C := (A.a : C)").expect(
        "transitive imported-Coe coercion A->B->C must elaborate and kernel-check \
         (composing Coe A B and Coe B C)",
    );

    // The body must compose BOTH imported steps: go through the imported `Coe.coe`
    // projection and reference both coercion functions (`aToB` and `bToC`).
    let body = env
        .get_const(&Name::from_string("coercedC"))
        .and_then(|i| i.value.clone())
        .expect("coercedC body");
    let referenced = body.collect_constants();
    assert!(
        referenced.contains(&Name::from_string("Coe.coe")),
        "coercedC must go through the imported Coe.coe projection, got: {referenced:?}"
    );
    assert!(
        referenced.contains(&Name::from_string("aToB"))
            && referenced.contains(&Name::from_string("bToC")),
        "a transitive A->C coercion must compose BOTH imported steps \
         (the A->B fn aToB AND the B->C fn bToC), got: {referenced:?}"
    );

    // The payoff: the composed coercion reduces to C.c2. C.c2 is distinct from
    // C.c1 (the value a wrong intermediate would yield via bToC B.b1) and from
    // every B/A value, so a wrong slot / wrong order / missed step is observable.
    assert_eq!(
        whnf_head_const(&env, &const_("coercedC")).as_deref(),
        Some("C.c2"),
        "coercedC := (A.a : C) must reduce to C.c2 through the composed \
         A->B->C imported coercion (NOT C.c1)"
    );
}

// =============================================================================
// Test 5: negative control — a coercion whose target is UNREACHABLE through the
// `Coe` graph must still FAIL (the chain search must not hallucinate a path).
// `Unreached : Type` has no incoming `Coe _ Unreached` edge, so `(A.a : Unreached)`
// has neither a direct nor a composed coercion and must be rejected. This guards
// against the chain fallback over-firing and silently accepting unsound coercions.
// =============================================================================

#[test]
fn test_imported_coe_chain_unreachable_target_is_rejected() {
    let mut env = imported_coe_chain_env();
    // A carrier with no incoming Coe edge.
    add_unit_enum(&mut env, "Unreached", "Unreached.u");

    let result = elaborate_decls_into(&mut env, "def bad : Unreached := (A.a : Unreached)");
    assert!(
        result.is_err(),
        "there is no Coe path A -> Unreached, so the coercion must be rejected, \
         not hallucinated; got Ok"
    );
    assert!(
        env.get_const(&Name::from_string("bad")).is_none(),
        "the rejected coercion must not register `bad`"
    );
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the VARIANT `codata` body — brick VC-1 of
//! `designs/2026-08-28-variant-codata-surface.md`.
//!
//! VC-1 generates nothing, so every test here is a REFUSAL test plus the
//! two invariants that make the refusal worth having: the body parses as a
//! variant (so the diagnostic is about variants, not about "0 fields"), and
//! nothing whatsoever reaches the environment — not the family, not even
//! the lazy `Codata.*` seed.

use crate::codata_variant::{validate_variant, CtorArg};
use crate::elaborate_decl_and_register;
use clean_kernel::Environment;
use clean_parser::{parse_file, CodataBody, DeclModifiers, SurfaceDecl};

const ITREE_SRC: &str = r"
codata ITr (E : Type) (R : Type) (Ans : E → Type) where
  | Ret : R → ITr E R Ans
  | Tau : ITr E R Ans → ITr E R Ans
  | Vis : (e : E) → (Ans e → ITr E R Ans) → ITr E R Ans
";

/// Elaborate every decl in `code` against `env`, returning the first error.
/// The env is threaded so a whole refusal table can share one prelude —
/// `Environment::with_prelude()` dominates the cost of these tests, and
/// reusing it also checks that a refusal leaves the env reusable.
fn elab_expect_err_in(env: &mut Environment, code: &str) -> crate::ElabError {
    let decls = parse_file(code).expect("should parse");
    let (last, prefix) = decls.split_last().expect("at least one declaration");
    for (i, decl) in prefix.iter().enumerate() {
        elaborate_decl_and_register(env, decl)
            .unwrap_or_else(|e| panic!("prefix decl {i} must elaborate: {e:?}"));
    }
    elaborate_decl_and_register(env, last).expect_err("the final declaration must be rejected")
}

// ─────────────────────────── parsing ───────────────────────────

/// The variant body reaches the elaborator AS a variant. Before VC-1 the
/// `where` block parsed as ZERO fields and the `|` clauses fell out to
/// top-level parse recovery, so the user saw
/// "codata needs at least one observation field … got 0 field(s)" plus a
/// raw-declaration recovery error — two diagnostics, neither about
/// variants. This test is what keeps that from coming back.
#[test]
fn test_variant_body_parses_as_variant_with_all_clauses() {
    let decls = parse_file(ITREE_SRC).expect("variant codata must parse");
    assert_eq!(decls.len(), 1, "no parse-recovery declarations may appear");
    let SurfaceDecl::Codata { body, .. } = &decls[0] else {
        panic!("expected a Codata declaration, got {:?}", decls[0]);
    };
    let CodataBody::Variant(ctors) = body else {
        panic!("expected a VARIANT body, got a record body");
    };
    let names: Vec<&str> = ctors.iter().map(|c| c.name.as_str()).collect();
    assert_eq!(names, ["Ret", "Tau", "Vis"]);
}

/// `where` is optional before a `|`-led body, matching `inductive`.
#[test]
fn test_variant_body_without_where_parses() {
    let decls = parse_file("codata T\n  | Tau : T → T\n").expect("should parse");
    let SurfaceDecl::Codata { body, .. } = &decls[0] else {
        panic!("expected a Codata declaration");
    };
    assert!(matches!(body, CodataBody::Variant(cs) if cs.len() == 1));
}

/// Binder-style clauses desugar through the shared `parse_ctor_type`.
#[test]
fn test_variant_binder_style_clause_parses() {
    let src = r"
codata ITr (E : Type) (R : Type) (Ans : E → Type) where
  | Tau : ITr E R Ans → ITr E R Ans
  | Vis (e : E) (k : Ans e → ITr E R Ans) : ITr E R Ans
";
    let decls = parse_file(src).expect("binder-style clauses must parse");
    let SurfaceDecl::Codata { body, .. } = &decls[0] else {
        panic!("expected a Codata declaration");
    };
    assert!(matches!(body, CodataBody::Variant(cs) if cs.len() == 2));
}

/// A record body is still a record body (no regression on the rank-1 lane).
#[test]
fn test_record_body_still_parses_as_record() {
    let decls = parse_file("codata Stream (A : Type) where\n  head : A\n  tail : Stream A\n")
        .expect("record codata must parse");
    let SurfaceDecl::Codata { body, .. } = &decls[0] else {
        panic!("expected a Codata declaration");
    };
    assert!(matches!(body, CodataBody::Record(fs) if fs.len() == 2));
}

/// A `|` clause after observation fields: the guard fires and NO `Codata`
/// declaration survives.
///
/// MEASURED: this parser RECOVERS from a failed declaration — both
/// `parse_file` and `parse_decl` return `Ok` with a `RawDecl` placeholder
/// rather than propagating the `ParseError`. So the assertion that carries
/// the weight is not "parsing errors" but "no `Codata` declaration
/// survives": without the guard this would yield a record codata with the
/// `|` clause silently dropped to recovery.
#[test]
fn test_clause_after_fields_yields_no_codata_declaration() {
    let src = "codata T (A : Type) where\n  head : A\n  | Tau : T A → T A\n";
    let decls = parse_file(src).expect("file-level parsing recovers");
    assert!(
        !decls
            .iter()
            .any(|d| matches!(d, SurfaceDecl::Codata { .. })),
        "a `|` clause after fields must not yield a Codata declaration; got {decls:?}"
    );
    assert!(
        decls
            .iter()
            .any(|d| matches!(d, SurfaceDecl::RawDecl { .. })),
        "it must surface as parse recovery; got {decls:?}"
    );
}

/// A field after `|` clauses: MEASURED, the symmetric guard cannot fire,
/// and the declaration is fail-closed for a different reason.
///
/// The expression parser is greedy: parsing `| Tau : T A → T A` followed
/// by `head : A` absorbs `head` as an application ARGUMENT of the clause's
/// return type, yielding `T A head`. By the time the "no field after
/// clauses" check runs, the current token is `:` and the field name is
/// already gone. `inductive` has exactly the same property, so this is the
/// grammar's behaviour rather than something this lane introduced.
///
/// It is still fail-closed, by two independent mechanisms: the mangled
/// return type `T A head` fails the constructor return-type check, and the
/// orphaned `: A` becomes a `RawDecl`. This test pins BOTH, so that if a
/// future grammar change makes the field survive, the symmetric guard
/// starts firing and this test tells us which mechanism caught it.
#[test]
fn test_field_after_clauses_is_absorbed_but_still_fails_closed() {
    let src = "codata T (A : Type) where\n  | Tau : T A → T A\n  head : A\n";
    let decls = parse_file(src).expect("file-level parsing recovers");
    assert!(
        decls
            .iter()
            .any(|d| matches!(d, SurfaceDecl::RawDecl { .. })),
        "the orphaned `: A` must surface as parse recovery; got {decls:?}"
    );
    let mut env = Environment::with_prelude();
    let mut refusals = 0;
    for decl in &decls {
        if let Err(e) = elaborate_decl_and_register(&mut env, decl) {
            refusals += 1;
            let text = format!("{e:?}");
            assert!(
                !text.contains("lowering is not implemented yet"),
                "a mangled clause must not be reported as the terminal \
                 not-yet-implemented refusal; got: {text}"
            );
        }
    }
    assert!(
        refusals > 0,
        "a field after `|` clauses must be refused somewhere, never accepted"
    );
}

// ────────────────────── fail-closed registration ──────────────────────

/// The load-bearing VC-1 invariant: an in-envelope variant codata is
/// refused by name and the environment is byte-identical afterwards — no
/// family, and not even the lazy `Codata.*` seed.
#[test]
fn test_in_envelope_variant_registers_nothing() {
    let mut env = Environment::with_prelude();
    // MEASURED: `elaborate_decl_and_register` runs a per-declaration
    // prologue (`env.init_pprod()` plus the B101 `instH*` bridge seeding,
    // lib.rs:913-919) that adds constants for ANY declaration, refused or
    // not. Elaborate a trivial def first so the baseline is taken after
    // that prologue has already run; otherwise this test measures
    // pre-existing behaviour rather than the codata lane.
    let warmup = parse_file("def variantWarmup : Nat := Nat.zero").expect("should parse");
    elaborate_decl_and_register(&mut env, &warmup[0]).expect("warmup def must elaborate");
    let before = env.num_constants();
    let decls = parse_file(ITREE_SRC).expect("should parse");
    let err = elaborate_decl_and_register(&mut env, &decls[0])
        .expect_err("VC-1 must refuse an in-envelope variant codata");
    let text = format!("{err:?}");
    assert!(
        text.contains("lowering is not implemented yet"),
        "an in-envelope declaration must get the TERMINAL refusal, not an \
         envelope refusal; got: {text}"
    );
    assert!(
        text.contains("2026-08-28-variant-codata-surface.md"),
        "the refusal must name the design doc; got: {text}"
    );
    assert_eq!(
        env.num_constants(),
        before,
        "a refused variant codata must leave the environment byte-identical"
    );
    assert_eq!(
        env.constants()
            .filter(|c| {
                let n = c.name.to_string();
                n.starts_with("Codata.") || n == "ITr" || n.starts_with("ITr.")
            })
            .count(),
        0,
        "neither the family nor the lazy Codata.* seed may be injected"
    );
}

/// Every envelope violation gets its OWN diagnostic — a malformed variant
/// must never be reported as "the lowering is not implemented yet", which
/// would hide a real error behind a to-do.
#[test]
fn test_variant_envelope_refusals() {
    let cases: &[(&str, &str)] = &[
        (
            "codata T where\n  | Tau : T → T\nderiving Repr\n",
            "deriving Repr is rejected",
        ),
        (
            "private codata T where\n  | Tau : T → T\n",
            "declaration modifiers",
        ),
        (
            "codata T.{u} where\n  | Tau : T → T\n",
            "universe-polymorphic variant codata",
        ),
        (
            "codata T : Nat → Type where\n  | Tau : T → T\n",
            "INDEXED variant codata",
        ),
        (
            "codata T : Prop where\n  | Tau : T → T\n",
            "the result sort must be `Type`",
        ),
        (
            "codata T {A : Type} where\n  | Tau : T → T\n",
            "parameters must be simple explicit binders",
        ),
        (
            "codata T where\n  | Tau : T → T\n  | Tau : T → T\n",
            "is declared more than once",
        ),
        (
            "codata T where\n  | head : T → T\n",
            "collides with the generated companion",
        ),
        (
            "codata T where\n  | Tau : T → T\n  | Bad : Nat → Nat\n",
            "must return `T` applied to exactly its declared parameters",
        ),
        (
            "codata T where\n  | Tau : T → T\n  | Nest : List T → T\n",
            "occurs neither as `T` at its own parameters",
        ),
        (
            "codata T where\n  | Tau : T → T\n  | Neg : (T → Nat) → T\n",
            "occurs neither as `T` at its own parameters",
        ),
        (
            "codata T where\n  | Tau : T → T\n  | Dep : (n : Nat) → Fin n → T → T\n",
            "DEPENDENT payload telescope",
        ),
        (
            "codata T where\n  | A : Nat → T\n  | B : Bool → T\n",
            "no constructor has a recursive argument",
        ),
        (
            "codata T where\n  | Imp {x : Nat} : T → T\n",
            "implicit/instance binder",
        ),
        (
            "codata T (A : Type) where\n  | Vary : T Nat → T A\n",
            "occurs neither as `T` at its own parameters",
        ),
    ];
    let mut env = Environment::with_prelude();
    for (src, want) in cases {
        let text = format!("{:?}", elab_expect_err_in(&mut env, src));
        assert!(
            text.contains(want),
            "source:\n{src}\nexpected diagnostic containing {want:?}, got:\n{text}"
        );
        assert!(
            !text.contains("lowering is not implemented yet"),
            "source:\n{src}\nan envelope violation must not be reported as the \
             not-yet-implemented terminal refusal; got:\n{text}"
        );
    }
}

/// A variant member inside `mutual` is refused by name (the record lane's
/// mutual path must not silently see an empty field list).
#[test]
fn test_mutual_variant_member_is_refused() {
    let src = r"
mutual
codata A where
  | Tau : A → A
codata B where
  | Tau : B → B
end
";
    let mut env = Environment::with_prelude();
    let text = format!("{:?}", elab_expect_err_in(&mut env, src));
    assert!(
        text.contains("a VARIANT codata body"),
        "mutual variant codata must be refused by name; got: {text}"
    );
    assert!(
        !text.contains("lowering is not implemented yet"),
        "the mutual path must report the mutual refusal, not the terminal one; \
         got: {text}"
    );
}

// ─────────────────────── classification (the plan) ───────────────────────

/// The classification VC-2 will lower from: `Ret`'s argument is payload,
/// `Tau`'s is a bare child, and `Vis` is a payload plus a child FAMILY
/// whose domain is `Ans e`. Getting `Vis` wrong is the silent-miscompile
/// this whole lane exists to prevent, so it is pinned here, one brick
/// before anything can be generated from it.
#[test]
fn test_itree_classification() {
    let decls = parse_file(ITREE_SRC).expect("should parse");
    let SurfaceDecl::Codata {
        name,
        universe_params,
        binders,
        ty,
        body,
        deriving,
        ..
    } = &decls[0]
    else {
        panic!("expected a Codata declaration");
    };
    let CodataBody::Variant(ctors) = body else {
        panic!("expected a variant body");
    };
    let shape = validate_variant(
        name,
        universe_params,
        binders,
        ty,
        ctors,
        deriving,
        &DeclModifiers::default(),
    )
    .expect("the ITree shape is inside the VC1 envelope");

    assert_eq!(shape.name, "ITr");
    assert_eq!(shape.binders.len(), 3);
    assert_eq!(shape.ctors.len(), 3);

    let ret = &shape.ctors[0];
    assert_eq!(ret.name, "Ret");
    assert!(matches!(ret.args.as_slice(), [CtorArg::Payload { .. }]));

    let tau = &shape.ctors[1];
    assert_eq!(tau.name, "Tau");
    assert!(matches!(tau.args.as_slice(), [CtorArg::Child { .. }]));

    let vis = &shape.ctors[2];
    assert_eq!(vis.name, "Vis");
    let [CtorArg::Payload {
        name: Some("e"), ..
    }, CtorArg::ChildFamily { domain, .. }] = vis.args.as_slice()
    else {
        panic!(
            "Vis must be payload `e : E` then a child FAMILY, got {:?}",
            vis.args
        );
    };
    // The family's position type must be `Ans e` — the payload-DEPENDENT
    // domain. A lowering that dropped the dependence would still typecheck
    // its own `rfl` laws and be silently wrong.
    let domain_text = format!("{domain:?}");
    assert!(
        domain_text.contains("\"Ans\"") && domain_text.contains("\"e\""),
        "Vis's child domain must be `Ans e`, got: {domain_text}"
    );
}

// ─────────────────── the target the generator must hit ───────────────────

/// The hand-written lowering that VC-3's generator must produce, replayed
/// through the ordinary pipeline against the UNMODIFIED `Codata.*` seed.
///
/// This is the measurement behind the design's central claim: variant
/// codata needs **no new tower, no seed change, and no kernel work** — the
/// seed's position family `B : (i : I) → A i → Type` may already depend on
/// the shape (`crates/clean-elab/data/MTypeIndexedPoly2.lean:504`); the
/// record lane simply never uses that dependence
/// (`codata_cmd.rs:744` passes `fun _ _ => …`).
///
/// Keeping it as a REPLAYED fixture rather than a number in a document is
/// the point: if the seed, the elaborator, or the prelude drifts, VC-3's
/// target breaks here instead of in the middle of writing the generator.
#[test]
fn test_variant_lowering_target_kernel_checks() {
    const TARGET: &str = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/data/variant_codata/itree_target.lean"
    ));
    let mut env = Environment::with_prelude();
    let decls = parse_file(TARGET).expect("the target fixture must parse");
    for (i, decl) in decls.iter().enumerate() {
        elaborate_decl_and_register(&mut env, decl).unwrap_or_else(|e| {
            panic!("target fixture declaration {i} failed to kernel-check: {e:?}")
        });
    }
    for name in [
        "ITr",
        "ITr.shapeF",
        "ITr.posF",
        "ITr.tgtF",
        "ITr.mkStep",
        "ITr.head",
        "ITr.Ret",
        "ITr.Tau",
        "ITr.Vis",
        "ITr.Br",
        "ITr.head_Ret",
        "ITr.child_Vis",
        "ITr.child_Br_left",
        "ITr.child_Br_right",
        "ITr.spin",
        // the anti-vacuity witnesses: without them a lowering that
        // collapsed two constructor tags would pass every law above
        "ITr.Ret_ne_Tau",
        "ITr.Ret_ne_spin",
    ] {
        assert!(
            env.get_const(&clean_kernel::Name::from_string(name))
                .is_some(),
            "target fixture must register {name}"
        );
    }
}

/// Defence-in-depth: an empty variant body cannot be produced by the
/// parser (the `|` loop runs at least once), but `validate_variant` still
/// refuses it rather than building an uninhabited carrier.
#[test]
fn test_empty_variant_is_refused_at_the_validator() {
    let err = validate_variant("T", &[], &[], &None, &[], &[], &DeclModifiers::default())
        .expect_err("an empty variant must be refused");
    let text = format!("{err:?}");
    assert!(
        text.contains("at least one constructor is required"),
        "got: {text}"
    );
}

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the VARIANT `codata` body — bricks VC-1 (parse + refuse) and
//! VC-2 (the plan) of `designs/2026-08-28-variant-codata-surface.md`.
//! Generation is `codata_variant_generate_tests`.
//!
//! Two halves. The refusal half: every envelope violation reaches its own
//! diagnostic, the body parses as a variant (so the diagnostic is about
//! variants, not about "0 fields"), and a refused declaration leaves the
//! environment byte-identical — not the family, not even the lazy
//! `Codata.*` seed. The plan half: `validate_variant` resolves the whole
//! lowering PURELY, and its output is golden-tested on the ITree shape and
//! on a mixed shape whose payload projections are not the identity.

use crate::codata_variant::validate_variant;
use crate::codata_variant_plan::{ArgPlan, VariantShape};
use crate::elaborate_decl_and_register;
use clean_kernel::Environment;
use clean_parser::{
    parse_file, CodataBody, DeclModifiers, LevelExpr, Projection, SurfaceDecl, SurfaceExpr,
    SurfaceName, UniverseExpr,
};

const ITREE_SRC: &str = r"
codata ITr (E : Type) (R : Type) (Ans : E → Type) where
  | Ret : R → ITr E R Ans
  | Tau : ITr E R Ans → ITr E R Ans
  | Vis : (e : E) → (Ans e → ITr E R Ans) → ITr E R Ans
";

#[test]
fn typed_variant_payload_substitution_preserves_display_twin() {
    use crate::codata_cmd::walk;
    let src = "codata T (E : Type) (Ans : E → Type) where\n  | Stop : T E Ans\n  | Vis : («e.dot» : E) → (PProd (Ans «e.dot») (Ans e.dot) → T E Ans) → T E Ans\n";
    let mut decls = parse_file(src).expect("typed variant source must parse");
    assert_eq!(decls.len(), 1);
    // The source parser represents unquoted e.dot here as a projection, not
    // one hierarchical Ident. Check that actual form before constructing the
    // generated-AST display twin whose exact identity this consumer tests.
    let is_projection = |expr: &SurfaceExpr| {
        matches!(expr, SurfaceExpr::Proj(_, base, Projection::Named(field))
            if field.is_unescaped_component("dot")
            && matches!(base.as_ref(), SurfaceExpr::Ident(_, name)
                if name.is_unescaped_component("e")))
    };
    {
        let parsed = plan_of(&decls);
        let ArgPlan::Child(child) = &parsed.ctors[1].args[1] else {
            panic!("parsed function-valued child must be retained");
        };
        let family = child.family.as_ref().expect("parsed family");
        for expr in [family.source, &family.in_shape] {
            let mut count = 0;
            walk(expr, &mut |e| count += usize::from(is_projection(e)));
            assert_eq!(count, 1, "the actual source projection stays intact");
        }
    }
    fn replace_projection(expr: &mut SurfaceExpr) -> usize {
        match expr {
            SurfaceExpr::Proj(span, base, Projection::Named(field))
                if field.is_unescaped_component("dot")
                    && matches!(base.as_ref(), SurfaceExpr::Ident(_, name)
                        if name.is_unescaped_component("e")) =>
            {
                *expr = SurfaceExpr::Ident(*span, SurfaceName::generated_path("e.dot"));
                1
            }
            SurfaceExpr::Pi(_, binders, body) => {
                let mut count = replace_projection(body);
                for binder in binders {
                    if let Some(ty) = &mut binder.ty {
                        count += replace_projection(ty);
                    }
                }
                count
            }
            SurfaceExpr::App(_, head, args) => {
                replace_projection(head)
                    + args
                        .iter_mut()
                        .map(|a| replace_projection(&mut a.expr))
                        .sum::<usize>()
            }
            SurfaceExpr::Arrow(_, a, b) => replace_projection(a) + replace_projection(b),
            SurfaceExpr::Paren(_, inner) => replace_projection(inner),
            _ => 0,
        }
    }
    let SurfaceDecl::Codata {
        body: CodataBody::Variant(ctors),
        ..
    } = &mut decls[0]
    else {
        panic!("retained variant declaration");
    };
    assert_eq!(replace_projection(&mut ctors[1].ty), 1);
    let shape = plan_of(&decls);
    let vis = &shape.ctors[1];
    let [ArgPlan::Payload(payload), ArgPlan::Child(child)] = vis.args.as_slice() else {
        panic!("the complete two-argument telescope must be retained");
    };
    let quoted = SurfaceName::component("e.dot", true);
    let nested = SurfaceName::generated_path("e.dot");
    assert_eq!(payload.arg_name, quoted);
    assert_ne!(quoted, nested);
    let family = child.family.as_ref().expect("function-valued child");
    let collect = |expr: &SurfaceExpr| {
        let mut names = Vec::new();
        walk(expr, &mut |e| {
            if let SurfaceExpr::Ident(_, n) = e {
                names.push(n.clone());
            }
        });
        names
    };
    let before = collect(family.source);
    let after = collect(&family.in_shape);
    assert!(before.contains(&quoted));
    assert!(before.contains(&nested));
    assert!(
        !after.contains(&quoted),
        "only the exact payload reference is substituted"
    );
    assert!(
        after.contains(&nested),
        "its display twin must remain a distinct reference"
    );
    assert!(after.contains(&vis.shape_var));
}

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
    let names: Vec<SurfaceName> = ctors.iter().map(|c| c.name.clone()).collect();
    assert_eq!(
        names,
        ["Ret", "Tau", "Vis"].map(SurfaceName::generated_path)
    );
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
                !text.contains("must return `T` applied to exactly its declared")
                    || text.contains("`Tau`"),
                "the mangled clause must be refused by NAME, not anonymously; \
                 got: {text}"
            );
        }
    }
    assert!(
        refusals > 0,
        "a field after `|` clauses must be refused somewhere, never accepted"
    );
    assert!(
        env.get_const(&clean_kernel::Name::from_string("T"))
            .is_none(),
        "no carrier may be registered for a mangled variant body"
    );
}

// ────────────────────── fail-closed registration ──────────────────────

/// The load-bearing fail-closed invariant: a variant codata the envelope
/// REFUSES leaves the environment byte-identical — no family, and not even
/// the lazy `Codata.*` seed.
#[test]
fn test_refused_variant_registers_nothing() {
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
    // Nested occurrence: in the envelope's own vocabulary, `List ITr` is
    // neither `ITr` at its parameters nor `D → ITr`.
    let src = r"
codata ITr (E : Type) (R : Type) (Ans : E → Type) where
  | Tau : ITr E R Ans → ITr E R Ans
  | Nest : List (ITr E R Ans) → ITr E R Ans
";
    let decls = parse_file(src).expect("should parse");
    let err = elaborate_decl_and_register(&mut env, &decls[0])
        .expect_err("a nested occurrence must be refused");
    let text = format!("{err:?}");
    assert!(
        text.contains("occurs neither as `ITr` at its own parameters"),
        "the refusal must name the envelope violation; got: {text}"
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
            // ONE universe parameter is supported; two is not.
            "codata T.{u, v} where\n  | Tau : T → T\n",
            "at most ONE universe parameter",
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
        (
            "codata T (A : Type) where\n  | Shadow : (A : Nat) → T A → T A\n",
            "SHADOWS the parameter",
        ),
        (
            "codata T where\n  | Twice : (n : Nat) → (n : Bool) → T → T\n",
            "twice",
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
            text.contains("variant codata"),
            "source:\n{src}\nthe refusal must come from the VARIANT lane and say \
             so, never from the record lane's field validator; got:\n{text}"
        );
        assert!(
            env.get_const(&clean_kernel::Name::from_string("T"))
                .is_none(),
            "source:\n{src}\na refused variant codata must not register a carrier"
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
        env.get_const(&clean_kernel::Name::from_string("A"))
            .is_none()
            && env
                .get_const(&clean_kernel::Name::from_string("B"))
                .is_none(),
        "a refused mutual block must register neither member"
    );
}

// ─────────────────────────── VC-2: the plan ───────────────────────────

/// A compact textual form of a plan expression, for golden assertions.
/// Covers exactly the node kinds the plan can contain; anything else
/// renders as `<?>` so a surprise shows up as a diff rather than passing
/// silently.
fn render(e: &SurfaceExpr) -> String {
    match e {
        SurfaceExpr::Ident(_, id) => id.to_string(),
        SurfaceExpr::Universe(_, UniverseExpr::Type) => "Type".to_string(),
        SurfaceExpr::Paren(_, inner) => render(inner),
        SurfaceExpr::Explicit(_, inner) => format!("@{}", render(inner)),
        SurfaceExpr::App(_, h, args) => {
            let rendered: Vec<String> = args.iter().map(|a| render(&a.expr)).collect();
            format!("({} {})", render(h), rendered.join(" "))
        }
        SurfaceExpr::Arrow(_, a, b) => format!("({} -> {})", render(a), render(b)),
        SurfaceExpr::Pi(_, bs, body) => {
            let names: Vec<String> = bs.iter().map(|b| b.name.to_string()).collect();
            format!("(forall {}, {})", names.join(" "), render(body))
        }
        SurfaceExpr::Lambda(_, bs, body) => {
            let names: Vec<String> = bs.iter().map(|b| b.name.to_string()).collect();
            format!("(fun {} => {})", names.join(" "), render(body))
        }
        SurfaceExpr::Proj(_, inner, Projection::Index(i)) => format!("{}.{i}", render(inner)),
        SurfaceExpr::UniverseInst(_, inner, ls) => {
            let levels: Vec<String> = ls
                .iter()
                .map(|l| match l {
                    LevelExpr::Lit(n) => n.to_string(),
                    other => format!("{other:?}"),
                })
                .collect();
            format!("{}.{{{}}}", render(inner), levels.join(" "))
        }
        _ => "<?>".to_string(),
    }
}

/// Validate the single `codata` declaration in `src`.
fn plan_of(decls: &[SurfaceDecl]) -> VariantShape<'_> {
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
    validate_variant(
        name,
        universe_params,
        binders,
        ty,
        ctors,
        deriving,
        &DeclModifiers::default(),
    )
    .expect("the shape is inside the VC1 envelope")
}

/// The ITree plan, resolved: `Ret` is one payload and no child, `Tau` is
/// one bare child, `Vis` is a payload plus a child FAMILY.
#[test]
fn test_itree_plan_is_fully_resolved() {
    let decls = parse_file(ITREE_SRC).expect("should parse");
    let shape = plan_of(&decls);

    assert_eq!(shape.name, &SurfaceName::generated_path("ITr"));
    assert_eq!(shape.binders.len(), 3);
    assert_eq!(shape.ctors.len(), 3);
    // P₁ = R, P₂ = PUnit.{1} (no payload), P₃ = E.
    assert_eq!(render(&shape.shape_ty), "(Sum R (Sum PUnit.{1} E))");
    // The tags: `Sum.inr`ᵏ `Sum.inl`, and a bare `Sum.inr`ⁿ⁻¹ last.
    let ret_arg = shape.ctors[0].args[0].arg_name().to_string();
    assert_eq!(
        render(&shape.tag(0, shape.ctors[0].payload_value())),
        format!("(Sum.inl {ret_arg})")
    );
    assert_eq!(
        render(&shape.tag(1, shape.ctors[1].payload_value())),
        "(Sum.inr (Sum.inl PUnit.unit))"
    );
    assert_eq!(
        render(&shape.tag(2, shape.ctors[2].payload_value())),
        "(Sum.inr (Sum.inr e))"
    );

    let ret = &shape.ctors[0];
    assert_eq!(ret.name, &SurfaceName::generated_path("Ret"));
    assert!(matches!(ret.args.as_slice(), [ArgPlan::Payload(_)]));
    assert_eq!(render(&ret.payload_ty), "R");
    assert_eq!(render(&ret.pos_ty_in_shape), "PEmpty.{1}");

    let tau = &shape.ctors[1];
    assert_eq!(tau.name, &SurfaceName::generated_path("Tau"));
    assert!(matches!(tau.args.as_slice(), [ArgPlan::Child(_)]));
    assert_eq!(render(&tau.payload_ty), "PUnit.{1}");
    assert_eq!(render(&tau.pos_ty_in_shape), "PUnit.{1}");

    let vis = &shape.ctors[2];
    assert_eq!(vis.name, &SurfaceName::generated_path("Vis"));
    let [ArgPlan::Payload(e), ArgPlan::Child(k)] = vis.args.as_slice() else {
        panic!(
            "Vis must be payload `e : E` then a child FAMILY, got {:?}",
            vis.args
        );
    };
    assert_eq!(
        e.arg_name,
        SurfaceName::generated_path("e"),
        "a NAMED clause binder keeps its name"
    );
    assert_eq!(render(e.ty), "E");
    assert_eq!(
        k.arg_name,
        SurfaceName::generated_path("a1"),
        "an arrow-style (anonymous) argument gets a generated name from its \
         position in the telescope"
    );
    assert_eq!(render(&vis.payload_ty), "E");
}

/// THE anti-vacuity check of this brick. `Vis`'s child domain is `Ans e`,
/// where `e` is a CONSTRUCTOR binder — a name that does not exist inside
/// `posF`, whose branch sees only the shape value. The plan must resolve
/// that domain to `Ans <projection of the shape>`.
///
/// A lowering that left `e` free would still elaborate whenever a
/// parameter happened to be called `e` (capturing it), and every `rfl`
/// computation law would still pass, because they are all stated against
/// the same wrong `posF`. Nothing downstream catches it. So it is pinned
/// here, on the pure plan, from three directions: the shape variable is a
/// name the source never mentions; the resolved domain mentions it; and
/// the resolved domain does NOT mention the constructor binder.
#[test]
fn test_vis_child_domain_resolves_to_a_projection_not_a_free_variable() {
    let decls = parse_file(ITREE_SRC).expect("should parse");
    let shape = plan_of(&decls);
    let vis = &shape.ctors[2];
    let [_, ArgPlan::Child(k)] = vis.args.as_slice() else {
        panic!("Vis must end in a child family");
    };
    let family = k.family.as_ref().expect("Vis's child is a FAMILY");

    // As written, in the constructor's scope: the payload binder by name.
    assert_eq!(render(family.source), "(Ans e)");
    // Resolved, in `posF`'s scope: the projection of the bound shape. With
    // one payload `Pₖ` is the bare type, so the path is the identity — but
    // it is the identity ON THE SHAPE VARIABLE, which is what makes the
    // difference between correct and free.
    assert_ne!(
        vis.shape_var,
        SurfaceName::component("e", false),
        "the shape binder must not coincide with the payload name, or this \
         test could not tell a projection from a free variable"
    );
    assert_eq!(render(&family.in_shape), format!("(Ans {})", vis.shape_var));
    assert_eq!(
        render(&vis.pos_ty_in_shape),
        format!("(Ans {})", vis.shape_var)
    );
    assert_eq!(render(&vis.pos_ty_in_args), "(Ans e)");
    let [ArgPlan::Payload(e), _] = vis.args.as_slice() else {
        panic!("Vis starts with a payload");
    };
    assert_eq!(render(&e.projection), vis.shape_var.to_string());
}

/// The mixed shape: a nullary constructor, a TWO-payload constructor whose
/// child domain mentions the SECOND payload, and a two-bare-child
/// constructor. This is where the projection path stops being the identity
/// — `Ans e` must resolve to `Ans s.2`, and `s.1` / `s.2` are the
/// right-nested `PProd` paths of `PProd Nat E`.
#[test]
fn test_mixed_shape_plan_projects_through_pprod() {
    let src = r"
codata Mix (E : Type) (Ans : E → Type) where
  | Stop : Mix E Ans
  | Two : (n : Nat) → (e : E) → (Ans e → Mix E Ans) → Mix E Ans
  | Fork : Mix E Ans → Mix E Ans → Mix E Ans
";
    let decls = parse_file(src).expect("should parse");
    let shape = plan_of(&decls);
    assert_eq!(
        render(&shape.shape_ty),
        "(Sum PUnit.{1} (Sum (PProd Nat E) PUnit.{1}))"
    );

    let stop = &shape.ctors[0];
    assert!(stop.args.is_empty());
    assert_eq!(render(&stop.payload_ty), "PUnit.{1}");
    assert_eq!(render(&stop.pos_ty_in_shape), "PEmpty.{1}");

    let two = &shape.ctors[1];
    let s = &two.shape_var;
    assert_eq!(render(&two.payload_ty), "(PProd Nat E)");
    assert_eq!(render(&two.payload_value()), "(PProd.mk n e)");
    let [ArgPlan::Payload(n), ArgPlan::Payload(e), ArgPlan::Child(k)] = two.args.as_slice() else {
        panic!(
            "Two must be payload, payload, child family; got {:?}",
            two.args
        );
    };
    assert_eq!(render(&n.projection), format!("{s}.1"));
    assert_eq!(render(&e.projection), format!("{s}.2"));
    let family = k.family.as_ref().expect("the third argument is a family");
    assert_eq!(render(family.source), "(Ans e)");
    assert_eq!(render(&family.in_shape), format!("(Ans {s}.2)"));
    assert_eq!(render(&two.pos_ty_in_shape), format!("(Ans {s}.2)"));

    let fork = &shape.ctors[2];
    assert_eq!(render(&fork.payload_ty), "PUnit.{1}");
    assert_eq!(render(&fork.pos_ty_in_shape), "(Sum PUnit.{1} PUnit.{1})");
    assert_eq!(fork.children().count(), 2);
}

/// The generator's own binder names are freshened against the source, so a
/// codata whose parameters are called `a`, `b`, `f`, `x` and `s0` cannot be
/// shadowed by them. (The generated declarations put the parameters and
/// these names in the same scope; see `GenNames`.)
#[test]
fn test_generated_binder_names_dodge_the_parameters() {
    let src = r"
codata Coll (a : Type) (b : Type) (f : Type) (x : Type) (s0 : Type) where
  | One : a → Coll a b f x s0 → Coll a b f x s0
";
    let decls = parse_file(src).expect("should parse");
    let shape = plan_of(&decls);
    let g = &shape.gen_names;
    let params = ["a", "b", "f", "x", "s0"].map(SurfaceName::generated_path);
    let mut minted: Vec<SurfaceName> = vec![
        g.shape_arg.clone(),
        g.pos_arg.clone(),
        g.child_arg.clone(),
        g.value_arg.clone(),
        g.state_arg.clone(),
        g.index_arg.clone(),
        g.coalg_arg.clone(),
        g.init_arg.clone(),
        g.default_arg.clone(),
        g.eq_arg.clone(),
    ];
    minted.extend(g.scruts.iter().cloned());
    // The ALTERNATE argument names (VC-5) share a scope with the parameters
    // too — `T.C_inj` binds the parameters, BOTH telescopes and the
    // hypothesis in one list.
    minted.extend(
        shape
            .ctors
            .iter()
            .flat_map(|c| c.args.iter().map(|a| a.alt_name().clone())),
    );
    for name in minted
        .iter()
        .chain(shape.ctors.iter().map(|c| &c.shape_var))
    {
        assert!(
            !params.contains(name),
            "generated binder `{name}` collides with a parameter"
        );
    }
    // …and, unlike the per-branch shape binders, they are distinct from ONE
    // ANOTHER, which is what makes them safe to put in a single binder list.
    let mut sorted = minted.clone();
    sorted.sort();
    sorted.dedup();
    assert_eq!(
        sorted.len(),
        minted.len(),
        "two generated binder names coincide: {minted:?}"
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
        // the corecursor tier (VC-4)
        "ITr.Step",
        "ITr.step_Ret",
        "ITr.step_Tau",
        "ITr.step_Vis",
        "ITr.step_Br",
        "ITr.corec",
        "ITr.head_corec",
        "ITr.child_corec",
        "ITr.spin",
        // the anti-vacuity witnesses: without them a lowering that
        // collapsed two constructor tags would pass every law above, and a
        // corecursor that returned a FINITE value would pass `head_spin`
        "ITr.Ret_ne_Tau",
        "ITr.Ret_ne_spin",
        "ITr.child_spin",
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
    let err = validate_variant(
        &SurfaceName::component("T", false),
        &[],
        &[],
        &None,
        &[],
        &[],
        &DeclModifiers::default(),
    )
    .expect_err("an empty variant must be refused");
    let text = format!("{err:?}");
    assert!(
        text.contains("at least one constructor is required"),
        "got: {text}"
    );
}

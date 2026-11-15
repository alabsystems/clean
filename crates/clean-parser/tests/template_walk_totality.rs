// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The notation-template walks (`mark_template_free_references`,
//! `instantiate_notation_template`) are total over the surface syntax: a
//! template of any form is walked, a form whose binding structure Clean does
//! not model is REFUSED, and nothing falls back to applying the template to
//! its operands (see `surface/template_hygiene.rs`). Every identifier the
//! template writes with an operand variable's spelling is that operand —
//! a name position (a field, a named argument, a projection field) included,
//! as Lean's `notation` antiquotes every such identifier.

use clean_kernel::Name;
use clean_parser::{
    instantiate_notation_template, instantiate_unhygienic_notation_template,
    mark_template_free_references, parse_expr, parse_file, Projection, Span, SurfaceArg,
    SurfaceDecl, SurfaceExpr, SurfaceName, SurfacePattern, SurfaceTactic,
};

fn x() -> SurfaceName {
    SurfaceName::component("x", false)
}

fn mark(template: &str) -> Result<SurfaceExpr, String> {
    let expr = parse_expr(template).unwrap_or_else(|e| panic!("{template}: {e}"));
    mark_template_free_references(&expr, &[x()], &Name::anon(), &[], None)
        .map_err(|refusal| refusal.reason().to_owned())
}

fn instantiate(template: &str, operand: &str) -> Result<SurfaceExpr, String> {
    let marked = mark(template)?;
    let operand = parse_expr(operand).expect("operand parses");
    instantiate_notation_template(&marked, &[x()], &[operand])
        .map_err(|refusal| refusal.reason().to_owned())
}

/// How many names spelled `spelling` the `Debug` rendering of `expr` holds.
fn mentions(expr: &SurfaceExpr, spelling: &str) -> usize {
    format!("{expr:?}")
        .matches(&format!("\"{spelling}\""))
        .count()
}

#[test]
fn templates_of_every_modelled_form_are_walked_and_instantiated() {
    for template in [
        "match (x : Int) with | n => (n + 10).toNat",
        "Id.run (do let y : Int := x; return (y + 10).toNat)",
        "(have kz : Nat := x; kz)",
        "Id.run (do have kz : Nat := x; return kz)",
        "Id.run (do let mut s := x; for i in [1, 2] do s := s + i; return s)",
        "Id.run (do if let some n := some x then return n else return 0)",
        "Id.run (do match x with | 0 => return 1 | n + 1 => return n)",
        "(by exact x + 1 : Nat)",
        "(by intro kz; exact x + kz : Nat → Nat)",
        "(by have : Nat := 5; exact this + x : Nat)",
        "(let rec go (n : Nat) : Nat := n + 1; go x)",
        "(if let some n := some x then n else 0)",
        "(let (p, q) := (x, 1); p + q)",
        "(fun | 0 => x | n + 1 => n)",
        "({ fst := x, snd := 1 } : Nat × Nat).1",
        "(open Nat in succ x)",
        "s!\"{x}\"",
        "(show Nat from x)",
        "(calc x = x := rfl)",
        "(by obtain ⟨k, _⟩ := h; exact k + x : Nat)",
        "(by rcases h with ⟨k, _⟩ | k; exact k + x : Nat)",
        "(by rintro ⟨k, hk : k = x⟩; exact k : Nat × Nat → Nat)",
        "(by obtain ⟨k, -⟩ := h; exact k + x : Nat)",
        "(by rcases h with @⟨k, _⟩ | -; exact k + x : Nat)",
        "(by rintro (k j : Nat); exact k + j + x : Nat → Nat → Nat)",
        "(by match x with | 0 => exact 1 | n + 1 => exact n : Nat)",
        "(by cases h with | inl k => exact k + x | inr k => exact k : Nat)",
    ] {
        instantiate(template, "a + b").unwrap_or_else(|e| panic!("{template}: {e}"));
    }
}

#[test]
fn unmodelled_forms_are_refused_not_applied() {
    assert!(mark("q(x)").is_err(), "a Qq quotation must be refused");
    // A tactic whose argument roles are not modelled, given an identifier
    // the template writes: it could bind it or name it.
    let span = Span::dummy();
    let user_tactic = SurfaceExpr::ByTactic(
        span,
        vec![SurfaceTactic::Named {
            span,
            name: "user_defined_tactic".to_owned(),
            args: vec![SurfaceExpr::Ident(
                span,
                SurfaceName::component("kz", false),
            )],
        }],
    );
    assert!(mark_template_free_references(&user_tactic, &[x()], &Name::anon(), &[], None).is_err());
}

#[test]
fn a_template_binder_is_renamed_apart_from_the_operand() {
    let expanded = instantiate("(fun kz => x + kz) 5", "kz").expect("walked");
    // Only the operand still spells `kz`: the binder and its reference were
    // renamed to a spelling no identifier token can produce.
    assert_eq!(mentions(&expanded, "kz"), 1, "{expanded:?}");
}

#[test]
fn an_operand_in_binder_position_must_be_an_identifier() {
    assert!(instantiate("fun x => x + 1", "q").is_ok());
    assert!(instantiate("fun x => x + 1", "q + 1").is_err());
}

#[test]
fn a_pattern_variable_keeps_its_spelling_and_gets_a_fresh_scope_per_expansion() {
    let marked = mark("match (5 : Nat) with | kz => x + kz").expect("walked");
    let expand = || {
        instantiate_notation_template(&marked, &[x()], &[parse_expr("a").expect("operand")])
            .expect("instantiated")
    };
    let (first, second) = (expand(), expand());
    let scope = |expr: &SurfaceExpr| match expr {
        SurfaceExpr::Match(_, _, _, arms) => match &arms[0].pattern {
            SurfacePattern::Var(name) => {
                assert_eq!(name.name(), &Name::anon().str("kz"));
                name.template_scope()
                    .expect("a template pattern variable is scoped")
            }
            other => panic!("pattern {other:?}"),
        },
        other => panic!("expansion {other:?}"),
    };
    assert_ne!(scope(&first), scope(&second));
}

/// A use of a notation whose template is refused is a parse error, never an
/// application of the template.
#[test]
fn a_use_of_a_refused_notation_does_not_parse_as_an_application() {
    let decls = parse_file(
        "notation \"TM \" x => (q(x) : Nat)\n\
         def r (a : Nat) : Nat := TM a\n",
    )
    .expect("recovering parse");
    assert!(
        !decls
            .iter()
            .any(|decl| matches!(decl, SurfaceDecl::Def { name, .. } if name.name() == &Name::anon().str("r"))),
        "{decls:?}"
    );
}

fn names_of(expr: &SurfaceExpr, out: &mut Vec<String>) {
    // Every field / named-argument / projection name the expansion writes.
    match expr {
        SurfaceExpr::StructLit {
            fields,
            base,
            struct_type,
            ..
        } => {
            for field in fields {
                out.push(field.name.to_string());
                names_of(&field.val, out);
            }
            for inner in base.iter().chain(struct_type.iter()) {
                names_of(inner, out);
            }
        }
        SurfaceExpr::App(_, head, args) => {
            names_of(head, out);
            for SurfaceArg { expr, name, .. } in args {
                if let Some(name) = name {
                    out.push(name.to_string());
                }
                names_of(expr, out);
            }
        }
        SurfaceExpr::NamedArg(_, name, value) => {
            out.push(name.to_string());
            names_of(value, out);
        }
        SurfaceExpr::Proj(_, base, projection) => {
            names_of(base, out);
            if let Projection::Named(field) = projection {
                out.push(format!(".{field}"));
            }
        }
        SurfaceExpr::Paren(_, inner) | SurfaceExpr::Ascription(_, inner, _) => names_of(inner, out),
        SurfaceExpr::Ident(_, name) if name.is_relative_constructor() => out.push(name.to_string()),
        SurfaceExpr::NamedHole(_, name) => out.push(format!("?{name}")),
        _ => {}
    }
}

fn names(expr: &SurfaceExpr) -> Vec<String> {
    let mut out = Vec::new();
    names_of(expr, &mut out);
    out
}

/// Lean's `notation` antiquotes EVERY identifier spelled like an operand
/// variable: a structure field, a `with` field, a field abbreviation, a
/// named-argument name, a projection field, a leading-dot constructor and a
/// goal name take the operand, which must then be an identifier (Lean 4.8.0
/// refuses `fg (a + 1 := 1) 2`, "invalid argument name").
#[test]
fn an_operand_variable_in_a_name_position_is_the_operand() {
    for (template, expected) in [
        ("fg (x := 1) 2", ".w"),
        ("(({ x := 5 } : SX).w)", "w"),
        ("(({ x } : SX).w)", "w"),
        ("({ sx0 with x := 7 }).w", "w"),
        ("(sx0).x", ".w"),
        ("((.x : Option Nat).getD 7)", ".w"),
        ("(?x : Nat)", "?w"),
    ] {
        let expanded = instantiate(template, "w").unwrap_or_else(|e| panic!("{template}: {e}"));
        let written = names(&expanded);
        assert!(
            written
                .iter()
                .any(|name| name == expected || format!(".{name}") == expected),
            "{template}: {written:?}"
        );
        assert!(
            !written.iter().any(|name| name == "x" || name == ".x"),
            "{template}: {written:?}"
        );
    }
    for template in [
        "fg (x := 1) 2",
        "(({ x := 5 } : SX).w)",
        "(({ x } : SX).w)",
        "(sx0).x",
    ] {
        assert!(
            instantiate(template, "a + 1").is_err(),
            "{template}: an operand in a name position must be an identifier"
        );
    }
    // `?x` with an operand that is no identifier is the anonymous `?_`.
    assert!(matches!(
        instantiate("?x", "a + 1").expect("walked"),
        SurfaceExpr::Hole(_)
    ));
}

/// A gap-free dotted run is ONE identifier token in Lean: `x.succ` is the
/// identifier `x.succ`, never the operand's `succ`, and `(e).x.v` is the
/// field token `x.v`; `(e).x` alone is the field `x`, an operand variable.
#[test]
fn a_dotted_identifier_is_one_token_never_an_operand_variable() {
    let expanded = instantiate("x.succ + 0", "a").expect("walked");
    let rendered = format!("{expanded:?}");
    assert!(
        !rendered.contains("\"a\""),
        "the operand is not substituted: {rendered}"
    );
    let chain = instantiate("(so0).x.v", "w").expect("walked");
    assert_eq!(
        names(&chain),
        vec![".x".to_owned(), ".v".to_owned()],
        "{chain:?}"
    );
    // A dotted field path of a structure instance is one identifier too.
    let path = instantiate("({ so0 with x.v := 9 }).w", "w").expect("walked");
    assert!(names(&path).iter().any(|name| name == "x"), "{path:?}");
}

/// The binders of `obtain`/`rcases`/`rintro` patterns (kept as source text)
/// are renamed apart like any other template binder: the tactic reads what
/// each one binds from `pattern_binders`.
#[test]
fn rcases_pattern_binders_are_renamed_apart() {
    let expanded = instantiate(
        "(by obtain ⟨kz, b⟩ := ((5, 1) : Nat × Nat); exact kz * 10 + b + x : Nat)",
        "kz",
    )
    .expect("walked");
    let SurfaceExpr::Ascription(_, block, _) = &expanded else {
        panic!("{expanded:?}")
    };
    let SurfaceExpr::ByTactic(_, tactics) = block.as_ref() else {
        panic!("{block:?}")
    };
    let SurfaceTactic::Obtain {
        pattern_binders, ..
    } = &tactics[0]
    else {
        panic!("{tactics:?}")
    };
    let kz = SurfaceName::component("kz", false);
    let bound = pattern_binders
        .iter()
        .find(|(written, _)| *written == kz)
        .map(|(_, bound)| bound.clone())
        .expect("kz is bound");
    assert_ne!(
        bound, kz,
        "the pattern's kz is renamed apart from the operand kz"
    );
}

/// Under `set_option hygiene false` the expansion is the bare substitution:
/// a template binder captures an operand identifier of its spelling.
#[test]
fn an_unhygienic_template_keeps_its_binders() {
    let template = parse_expr("(fun kz => x + kz) 5").expect("parses");
    let expanded = instantiate_unhygienic_notation_template(
        &template,
        &[x()],
        &[parse_expr("kz").expect("operand")],
    )
    .expect("walked");
    assert_eq!(mentions(&expanded, "kz"), 3, "{expanded:?}");
}

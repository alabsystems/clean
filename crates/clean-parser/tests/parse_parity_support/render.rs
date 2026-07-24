// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Canonical-skeleton renderer for `SurfaceExpr`, shared by the `parse_parity`
// harness. `include!`d (not a `mod`) so it stays a plain function table with no
// separate compilation unit.
//
// The skeleton is a fully-parenthesized prefix S-expression that captures the
// two things a parse-parity check cares about — head constants and
// parenthesization / associativity shape — while deliberately abstracting
// away surface noise that the two engines render differently:
//
// - `Paren` is transparent: nesting is expressed structurally, not by literal
//   parens, so `(a + b)` and `a + b` skeletonize identically.
// - Binders (lambda / pi / let / match arms) are abstracted to a tag plus the
//   body; binder names and types are dropped. Clean and Lean disagree on
//   binder pretty-printing (`fun x =>` vs `fun ⦃x⦄ =>`, dropped ascriptions),
//   and the interesting divergences all live in the body / operator spine.
// - String / char / float literals collapse to `#str` / `#char` / `#float`
//   (their exact bytes are not what precedence bugs turn on); `Nat` literals
//   are kept verbatim (operand-drop and mis-association show up in them).
//
// Binary operators are NOT special-cased here: clean already desugars every
// infix form it supports to an `App` with the Lean head constant
// (`a + b` → `App(HAdd.hAdd, [a, b])`, `f <$> a` → `App(Functor.map, …)`), so
// the generic `App` arm renders them in exactly the prefix head form the
// ground-truth table is authored in. The fixture's `lean_tree` column is
// authored in this same grammar (see `tests/fixtures/parser_parity/README.md`).

/// A "bare name" is a rendered leaf with no whitespace / parens — a plain
/// (possibly dotted) identifier or numeral. Used to fold `Proj(<bare>, .field)`
/// back into the dotted spelling both engines use for qualified names / dot
/// access (`Sigma.mk`, `xs.reverse`, `List.length`), so the representational
/// choice "qualified const vs projection" never shows up as a false divergence.
fn is_bare_name(s: &str) -> bool {
    !s.is_empty()
        && s.chars()
            .all(|c| c.is_alphanumeric() || "_.'·!".contains(c))
}

/// Canonicalize an identifier leaf. `(· + 1)` binds a compiler-generated
/// `__cdot_N` variable; its name is not stable across engines, so collapse the
/// whole family to the section marker `·` (the fixture is authored with `·`).
fn render_ident(name: &str) -> String {
    if name.starts_with("__cdot_") {
        "·".to_string()
    } else {
        name.to_string()
    }
}

/// Render one application argument (positional or `name := e`).
fn render_arg(arg: &SurfaceArg) -> String {
    match &arg.name {
        Some(name) => format!("{name}:={}", render_skeleton(&arg.expr)),
        None => render_skeleton(&arg.expr),
    }
}

fn render_universe(u: &UniverseExpr) -> &'static str {
    match u {
        UniverseExpr::Prop => "Prop",
        UniverseExpr::Type | UniverseExpr::TypeLevel(_) => "Type",
        UniverseExpr::TypeImplicit => "Type*",
        UniverseExpr::SortStar => "Sort*",
        UniverseExpr::Sort(_) | UniverseExpr::SortImplicit => "Sort",
    }
}

fn render_level(l: &LevelExpr) -> String {
    match l {
        LevelExpr::Lit(n) => n.to_string(),
        LevelExpr::Param(p) => p.clone(),
        LevelExpr::Succ(inner) => format!("(succ {})", render_level(inner)),
        LevelExpr::Max(a, b) => format!("(max {} {})", render_level(a), render_level(b)),
        LevelExpr::IMax(a, b) => format!("(imax {} {})", render_level(a), render_level(b)),
        LevelExpr::Antiquot(n) => format!("${n}"),
    }
}

fn render_antiquot(content: &QAntiquotContent) -> String {
    match content {
        QAntiquotContent::Simple(n) => format!("${n}"),
        QAntiquotContent::Expr(e) => format!("$({})", render_skeleton(e)),
        QAntiquotContent::Typed { name, .. } => format!("$({name}:_)"),
        QAntiquotContent::Splice { name, .. } => format!("$[{name}]"),
    }
}

/// Render a `SurfaceExpr` into the canonical skeleton string. Total over every
/// `SurfaceExpr` variant so a newly-added variant is a compile error here rather
/// than a silent skeleton gap.
fn render_skeleton(e: &SurfaceExpr) -> String {
    match e {
        SurfaceExpr::Ident(_, name) => render_ident(name),
        SurfaceExpr::SyntheticSorry(_) => "#sorry".to_string(),
        SurfaceExpr::Universe(_, u) => render_universe(u).to_string(),
        SurfaceExpr::App(..) => {
            // Flatten the curried application spine: `App(App(f, [a]), [b])`
            // renders as `(f a b)`, same as `App(f, [a, b])`. Clean's `|>`/`<|`
            // desugar left-nests each argument, while Lean's flatten-macro emits
            // one application node — the two are semantically identical (curried
            // application is associative), so nesting must not read as a
            // divergence. Only `App` heads are unwrapped; a `Paren`/operator head
            // (`(a + b) c`) keeps its own application node.
            let mut spine: Vec<&SurfaceArg> = Vec::new();
            let mut head = e;
            while let SurfaceExpr::App(_, f, args) = head {
                for arg in args.iter().rev() {
                    spine.push(arg);
                }
                head = f;
            }
            spine.reverse();
            let mut s = format!("({}", render_skeleton(head));
            for arg in spine {
                s.push(' ');
                s.push_str(&render_arg(arg));
            }
            s.push(')');
            s
        }
        SurfaceExpr::Lambda(_, _, body) => format!("(fun {})", render_skeleton(body)),
        SurfaceExpr::PatternMatchLambda(_, _, body) => {
            format!("(pfun {})", render_skeleton(body))
        }
        SurfaceExpr::Pi(_, _, body) => format!("(pi {})", render_skeleton(body)),
        SurfaceExpr::Arrow(_, a, b) => {
            format!("(-> {} {})", render_skeleton(a), render_skeleton(b))
        }
        SurfaceExpr::Let(_, _, v, body) => {
            format!("(let {} {})", render_skeleton(v), render_skeleton(body))
        }
        SurfaceExpr::LetRec(_, _, v, body) => {
            format!("(letrec {} {})", render_skeleton(v), render_skeleton(body))
        }
        SurfaceExpr::LetPattern(_, _, scrut, fb, body) => format!(
            "(letpat {} {} {})",
            render_skeleton(scrut),
            render_skeleton(fb),
            render_skeleton(body)
        ),
        SurfaceExpr::Lit(_, lit) => match lit {
            SurfaceLit::Nat(n) => n.to_string(),
            SurfaceLit::BigNat(n) => n.to_string(),
            SurfaceLit::Float(_) => "#float".to_string(),
            SurfaceLit::Char(_) => "#char".to_string(),
            SurfaceLit::String(_) => "#str".to_string(),
        },
        SurfaceExpr::Paren(_, inner) => render_skeleton(inner),
        SurfaceExpr::Hole(_) => "_".to_string(),
        SurfaceExpr::NamedHole(_, n) => format!("?{n}"),
        SurfaceExpr::Ascription(_, inner, ty) => {
            format!("(: {} {})", render_skeleton(inner), render_skeleton(ty))
        }
        SurfaceExpr::OutParam(_, inner) => format!("(outParam {})", render_skeleton(inner)),
        SurfaceExpr::SemiOutParam(_, inner) => {
            format!("(semiOutParam {})", render_skeleton(inner))
        }
        SurfaceExpr::If(_, c, t, f) => format!(
            "(ite {} {} {})",
            render_skeleton(c),
            render_skeleton(t),
            render_skeleton(f)
        ),
        SurfaceExpr::IfLet(_, _, s, t, f) => format!(
            "(iflet {} {} {})",
            render_skeleton(s),
            render_skeleton(t),
            render_skeleton(f)
        ),
        SurfaceExpr::IfDecidable(_, _, p, t, f) => format!(
            "(dite {} {} {})",
            render_skeleton(p),
            render_skeleton(t),
            render_skeleton(f)
        ),
        SurfaceExpr::Match(_, _hyp, scrut, arms) => {
            // The fixture skeleton for `match` is `(match <scrut> <n_arms>)`;
            // the annotated discriminant's hypothesis name (`match h : e`) is
            // deliberately not part of the derivation (freqsweep row
            // `match h : n with …` pins `(match n 2)`), so it is elided here.
            format!("(match {} {})", render_skeleton(scrut), arms.len())
        }
        SurfaceExpr::Proj(_, inner, proj) => {
            let inner_s = render_skeleton(inner);
            match proj {
                // Fold `<bare-name>.field` into a dotted name (qualified-const /
                // dot-access parity); keep the explicit projection form when the
                // base is a compound expression.
                Projection::Named(n) if is_bare_name(&inner_s) => format!("{inner_s}.{n}"),
                Projection::Named(n) => format!("(. {inner_s} {n})"),
                Projection::Index(i) => format!("(. {inner_s} {i})"),
            }
        }
        SurfaceExpr::UniverseInst(_, inner, levels) => {
            let mut s = format!("(uinst {}", render_skeleton(inner));
            for l in levels {
                s.push(' ');
                s.push_str(&render_level(l));
            }
            s.push(')');
            s
        }
        SurfaceExpr::NamedArg(_, name, inner) => {
            format!("({name}:={})", render_skeleton(inner))
        }
        SurfaceExpr::SyntaxQuote(_, _) => "#quote".to_string(),
        SurfaceExpr::QQuotation { inner, .. } => format!("(qq {})", render_skeleton(inner)),
        SurfaceExpr::QAntiquot { content, .. } => render_antiquot(content),
        SurfaceExpr::Explicit(_, inner) => format!("(@ {})", render_skeleton(inner)),
        SurfaceExpr::StructLit {
            base,
            fields,
            struct_type,
            ..
        } => {
            let mut s = String::from("(structInst");
            if let Some(b) = base {
                s.push_str(&format!(" with={}", render_skeleton(b)));
            }
            for field in fields {
                s.push_str(&format!(" {}:={}", field.name, render_skeleton(&field.val)));
            }
            if let Some(ty) = struct_type {
                s.push_str(&format!(" :{}", render_skeleton(ty)));
            }
            s.push(')');
            s
        }
        SurfaceExpr::ByTactic(_, _) => "#by".to_string(),
        SurfaceExpr::CalcBlock(_, _) => "#calc".to_string(),
        SurfaceExpr::Do(_, _) => "#do".to_string(),
        SurfaceExpr::LiftMethod(_, inner) => format!("(<- {})", render_skeleton(inner)),
        SurfaceExpr::InterpolatedStr { .. } => "#istr".to_string(),
        SurfaceExpr::OpenIn { body, .. } => format!("(openIn {})", render_skeleton(body)),
    }
}

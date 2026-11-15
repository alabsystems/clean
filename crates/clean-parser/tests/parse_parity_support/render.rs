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
// - Compiler-introduced binders have no source spelling in either engine
//   (Lean's are hygienic, Clean's `SurfaceName::unspellable`), so a reference
//   to one renders as the fixture's fixed leaf for its family — `·` for a
//   `(· …)` section variable, `_x` for a pattern `fun`'s scrutinee — and an
//   unknown family is refused, never guessed (`render_ident`).
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

/// Render a name the parser READ from the source: its exact source spelling.
///
/// A name with no spelling is a compiler-introduced binder
/// (`SurfaceName::unspellable`, identity `base.N`, which no identifier token
/// produces). Such a name reaches the skeleton only as an identifier leaf, and
/// only through [`render_ident`]'s canonical families; anywhere else, or of a
/// family `render_ident` does not know, it is a harness gap and is refused
/// loudly rather than rendered as a guess.
fn render_name(name: &clean_parser::SurfaceName) -> String {
    name.source_spelling().unwrap_or_else(|| {
        panic!(
            "parse-parity skeleton reached `{name}`, which has no source spelling: a \
             compiler-introduced binder must be canonicalized in `render_ident` to the \
             fixture's spelling of Lean's own (hygienic) binder, never rendered as a guess"
        )
    })
}

/// The base of a compiler-introduced binder `SurfaceName::unspellable(base,
/// N)`: exactly two GENERATED components, a string base under the root then a
/// numeric index. `None` for every name a source token can spell — including a
/// user-written `_dx0`, `__cdot_7` or `«_x»` — and for a leading-dot selector.
fn unspellable_binder_base(name: &clean_parser::SurfaceName) -> Option<&str> {
    use clean_kernel::name::NameInner;
    let generated = clean_parser::NameComponentSyntax::Generated;
    if name.is_relative_constructor() || name.component_syntax() != [generated, generated] {
        return None;
    }
    let NameInner::Num(parent, _) = name.name().inner() else {
        return None;
    };
    match parent.inner() {
        NameInner::Str(root, base) if root.is_anon() => Some(base.as_ref()),
        NameInner::Anon | NameInner::Str(..) | NameInner::Num(..) => None,
    }
}

/// Canonicalize an identifier leaf.
///
/// Both engines bind these positions with a name no source identifier can
/// spell — Lean with a hygienic, macro-scoped identifier (`pp.raw` prints the
/// pattern-`fun` scrutinee as `x._@.…._hyg.N`), Clean with
/// `SurfaceName::unspellable` — so neither name is stable across engines, and
/// the fixture spells each family with one fixed leaf:
///
/// - `(· + 1)` binds `__cdot.N`; the fixture writes the section marker `·`.
/// - A pattern `fun` binds its scrutinee: `fun (a, b) => e` and
///   `fun ⟨a, b⟩ => e` one `_dx.N` per destructured position (one `fun` +
///   `match` each), `fun | p => e` the single `_x.0`
///   (`SurfaceName::pattern_lambda_binder`). Lean elaborates all of them to
///   `fun x => match x with …` over its hygienic `x`; the fixture writes `_x`.
///
/// Only the typed unspellable identity collapses: a user-written `_dx0`,
/// `__cdot_7` or `_x` renders as its own source spelling, and any other
/// unspellable family is refused by [`render_name`].
fn render_ident(name: &clean_parser::SurfaceName) -> String {
    match unspellable_binder_base(name) {
        Some("__cdot") => "·".to_string(),
        Some("_dx" | "_x") => "_x".to_string(),
        _ => render_name(name),
    }
}

/// Render one application argument (positional or `name := e`).
fn render_arg(arg: &SurfaceArg) -> String {
    match &arg.name {
        Some(name) => format!("{}:={}", render_name(name), render_skeleton(&arg.expr)),
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
        LevelExpr::Param(p) => render_name(p),
        LevelExpr::Succ(inner) => format!("(succ {})", render_level(inner)),
        LevelExpr::Max(a, b) => format!("(max {} {})", render_level(a), render_level(b)),
        LevelExpr::IMax(a, b) => format!("(imax {} {})", render_level(a), render_level(b)),
        LevelExpr::Antiquot(n) => format!("${}", render_name(n)),
    }
}

fn render_antiquot(content: &QAntiquotContent) -> String {
    match content {
        QAntiquotContent::Simple(n) => format!("${}", render_name(n)),
        QAntiquotContent::Expr(e) => format!("$({})", render_skeleton(e)),
        QAntiquotContent::Typed { name, .. } => format!("$({}:_)", render_name(name)),
        QAntiquotContent::Splice { name, .. } => format!("$[{}]", render_name(name)),
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
        SurfaceExpr::Have(_, _, v, body) => {
            format!("(have {} {})", render_skeleton(v), render_skeleton(body))
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
        SurfaceExpr::NamedHole(_, n) => format!("?{}", render_name(n)),
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
                Projection::Named(n) if is_bare_name(&inner_s) => {
                    format!("{inner_s}.{}", render_name(n))
                }
                Projection::Named(n) => format!("(. {inner_s} {})", render_name(n)),
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
            format!("({}:={})", render_name(name), render_skeleton(inner))
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
                s.push_str(&format!(
                    " {}:={}",
                    render_name(&field.name),
                    render_skeleton(&field.val)
                ));
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

#[test]
fn parity_renderer_retains_typed_source_name_boundaries() {
    use clean_parser::SurfaceName;
    let quoted = SurfaceName::component("A.B", true);
    let path = SurfaceName::component("A", false).append(&SurfaceName::component("B", false));
    assert_ne!(render_ident(&quoted), render_ident(&path));
    for name in [quoted, path, SurfaceName::component("7", true)] {
        let spelling = render_ident(&name);
        assert_eq!(
            clean_parser::parse_name(&spelling).unwrap().name(),
            name.name()
        );
    }
    let numeric = SurfaceName::from_name(clean_kernel::Name::anon().num(7));
    assert!(std::panic::catch_unwind(|| render_ident(&numeric)).is_err());
}

#[test]
fn parity_section_normalization_requires_generated_identifier() {
    use clean_parser::SurfaceName;
    assert_eq!(render_ident(&SurfaceName::unspellable("__cdot", 7)), "·");
    assert_eq!(render_ident(&SurfaceName::pattern_lambda_binder()), "_x");
    assert_eq!(render_ident(&SurfaceName::unspellable("_dx", 3)), "_x");
    // The old spellable pattern-binder spelling is an ordinary identifier.
    assert_eq!(render_ident(&SurfaceName::component("_dx3", false)), "_dx3");
    // The old spellable spelling is an ordinary identifier now.
    assert_ne!(render_ident(&SurfaceName::generated_path("__cdot_7")), "·");
    assert_ne!(
        render_ident(&SurfaceName::component("__cdot_7", false)),
        "·"
    );
    assert_ne!(render_ident(&SurfaceName::component("__cdot_7", true)), "·");
    assert_ne!(
        render_ident(&SurfaceName::generated_path("__cdot_user")),
        "·"
    );
    assert_ne!(
        render_ident(&SurfaceName::generated_path("__cdot_7").with_relative_constructor()),
        "·"
    );
}

#[test]
fn parity_pattern_fun_scrutinee_normalization_requires_unspellable_binder() {
    use clean_parser::SurfaceName;
    // Both of Clean's pattern-`fun` scrutinee families are the fixture's `_x`.
    assert_eq!(render_ident(&SurfaceName::unspellable("_dx", 0)), "_x");
    assert_eq!(render_ident(&SurfaceName::unspellable("_dx", 3)), "_x");
    assert_eq!(render_ident(&SurfaceName::pattern_lambda_binder()), "_x");
    // A spellable name renders as its own spelling, never as the marker.
    assert_eq!(render_ident(&SurfaceName::component("_dx0", false)), "_dx0");
    assert_eq!(render_ident(&SurfaceName::generated_path("_dx0")), "_dx0");
    assert_eq!(render_ident(&SurfaceName::component("_dx", true)), "«_dx»");
    // Another unspellable family, a qualified numeric name and a leading-dot
    // selector over the binder's identity are not collapsed: they have no
    // skeleton leaf and are refused loudly rather than guessed.
    let tpl = SurfaceName::unspellable("_tpl", 0);
    assert!(std::panic::catch_unwind(|| render_ident(&tpl)).is_err());
    let qualified = SurfaceName::from_name(clean_kernel::Name::anon().str("A").str("_dx").num(0));
    assert!(std::panic::catch_unwind(|| render_ident(&qualified)).is_err());
    let selector = SurfaceName::unspellable("_dx", 0).with_relative_constructor();
    assert!(std::panic::catch_unwind(|| render_ident(&selector)).is_err());
}

/// End to end through the parser: every pattern-`fun` spelling renders its
/// generated scrutinee as the fixture's `_x` (Lean elaborates each to
/// `fun x => match x with …`), while a user-written binder of the old
/// spellable spelling keeps its own name and its plain `fun` tag. The `fun |`
/// arm body is parenthesized because Clean parses that body as an ATOM
/// (`lambda_arm_expr`), which is not what this test is about.
#[test]
fn parity_pattern_fun_renders_generated_scrutinee_and_keeps_user_spelling() {
    for (input, skeleton) in [
        ("fun (a, b) => a + b", "(pfun (match _x 1))"),
        ("fun ⟨a, b⟩ => a + b", "(pfun (match _x 1))"),
        ("fun (a, b) c => a + b + c", "(pfun (match _x 1))"),
        ("fun | (a, b) => (a + b)", "(pfun (match _x 1))"),
        (
            "fun _dx0 => match _dx0 with | (a, b) => a + b",
            "(fun (match _dx0 1))",
        ),
    ] {
        let tree = parse_expr(input).unwrap_or_else(|e| panic!("`{input}` parses: {e:?}"));
        assert_eq!(render_skeleton(&tree), skeleton, "skeleton of `{input}`");
    }
}

/// Adversarial pins for the scrutinee canonicalization, through the parser.
///
/// - Several pattern positions and nested patterns bind several generated
///   scrutinees (`_dx.0`, `_dx.1`, …); each still renders as `_x`, and a
///   pattern `fun` inside a `(· …)` section renders both families at once.
///   The Lean trees are pinned-toolchain `pp.parens` output (v4.30.0-rc2):
///   `fun (a, b) (c, d) => e` is `fun x x_1 => match x with | (a, b) => …`,
///   `(· + (fun (a, b) => a + b) (1, 2))` is
///   `fun x => (x + ((fun x => match x with | (a, b) => a + b) (1, 2)))`.
/// - Source text cannot forge the marker: `_dx.1` / `_x.1` / `__cdot.1` are a
///   projection of a SPELLABLE base (Lean: `_dx.fst`), never the generated
///   `base.N` identity, so they keep the user's name.
/// - Another generated family reached end to end — a tuple `let` binds the
///   unspellable `_tpl.0` — is refused, naming the binder, rather than
///   collapsed to a leaf it does not stand for.
#[test]
fn parity_pattern_fun_scrutinee_canonicalization_resists_forgery_and_other_families() {
    for (input, skeleton) in [
        ("fun (a, b) (c, d) => a + c + b + d", "(pfun (match _x 1))"),
        ("fun ⟨a, b⟩ ⟨c, d⟩ => a + c", "(pfun (match _x 1))"),
        ("fun ((a, b), c) => a + b + c", "(pfun (match _x 1))"),
        ("fun (a, _) => a", "(pfun (match _x 1))"),
        (
            "(· + (fun (a, b) => a + b) (1, 2))",
            "(fun (HAdd.hAdd · ((pfun (match _x 1)) (Prod.mk 1 2))))",
        ),
        ("_dx.1", "(. _dx 1)"),
        ("_x.1", "(. _x 1)"),
        ("__cdot.1", "(. __cdot 1)"),
    ] {
        let tree = parse_expr(input).unwrap_or_else(|e| panic!("`{input}` parses: {e:?}"));
        assert_eq!(render_skeleton(&tree), skeleton, "skeleton of `{input}`");
    }

    let tuple_let = parse_expr("let (x, y) := (1, 2); x + y")
        .unwrap_or_else(|e| panic!("tuple `let` parses: {e:?}"));
    let refusal = std::panic::catch_unwind(|| render_skeleton(&tuple_let))
        .expect_err("the unspellable `_tpl.0` must be refused, not rendered");
    let message = refusal
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| refusal.downcast_ref::<&str>().copied())
        .unwrap_or_default();
    assert!(
        message.contains("`_tpl.0`"),
        "the refusal names the binder it could not render: {message:?}"
    );
}

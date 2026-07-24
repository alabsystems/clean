// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Faithfulness gate for the Isabelle/HOL Pure-proof → clean translator.
//!
//! ## Why this test exists
//!
//! Every definitional-axiom arm of the translator (the `def_axiom_body`,
//! `set_instance_def_body`, polymorphic-instance-op, ground instance-op and
//! list-function arms) discharges a `_def` axiom `c args ≡ B` by storing the
//! proposition `@Eq α (embed lhs) (embed rhs)` and proving it with
//! `Eq.refl α (embed lhs)`. The kernel accepts that proof **only** when
//! `embed lhs` δ-reduces to `embed rhs` — i.e. only when `c` is a genuinely
//! registered clean `Definition` that unfolds to `B`. This makes the stored
//! theorem a *faithful* statement of the real definitional equality.
//!
//! On 2026-06-23 a regression (caught and corrected in commit `8d67767e`)
//! inflated the verified count by **overriding** the stored proposition to the
//! reflexive *tautology* `@Eq α B B` (the body equated with itself, proved by
//! `Eq.refl α B`). That tautology kernel-verifies for *any* `c` — including
//! unregistered constants that `embed_term` quantifies as a free parameter — so
//! it silently stored the vacuous `∀c. B = B` under the definition's name
//! instead of the real `c args = B`. Replacing the tautology with the faithful
//! `@Eq α lhs rhs` arm dropped the raw corpus 3,616 → 3,212 (−404): every one of
//! those 404 was a tautology, never a real theorem.
//!
//! The faithful arm is therefore identified by the literal it builds:
//! `Expr::apps(Eq, [alpha.clone(), lhs.clone(), body])` — the two `Eq` operands
//! are the **distinct** `lhs` and `body` (or `rhs`) terms. The tautology arm
//! built `Expr::apps(Eq, [alpha, body.clone(), body.clone()])` — the same `body`
//! term twice. This test codifies the grep that has guarded the invariant by
//! hand all session: it (A) scans the translator source and asserts **zero**
//! occurrences of the forbidden "same operand twice" `@Eq` construction, and
//! (B) translates a real `_def` fixture (`Int.power_int_def`) and asserts the
//! stored `@Eq` carries two structurally **different** operands (a genuine
//! `c args = B`, not a reflexive `B = B`).

use std::path::{Path, PathBuf};

/// Directory holding the split translator modules.
fn translate_dir() -> PathBuf {
    // CARGO_MANIFEST_DIR is the `clean-mathverse` crate root at test time.
    Path::new(env!("CARGO_MANIFEST_DIR")).join("src/hol/isabelle_pure_translate")
}

/// Read every `*.rs` module of the split translator, joined with a marker so a
/// single scan covers the whole (formerly single-file) translator surface.
fn translator_source() -> String {
    let dir = translate_dir();
    let mut out = String::new();
    let mut files: Vec<PathBuf> = std::fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("read translator dir {}: {e}", dir.display()))
        .filter_map(Result::ok)
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|x| x == "rs"))
        .collect();
    files.sort();
    assert!(
        !files.is_empty(),
        "no translator source files found under {} — the split module moved?",
        dir.display()
    );
    for f in files {
        out.push_str("// ==== FILE: ");
        out.push_str(&f.file_name().unwrap().to_string_lossy());
        out.push_str(" ====\n");
        out.push_str(
            &std::fs::read_to_string(&f).unwrap_or_else(|e| panic!("read {}: {e}", f.display())),
        );
        out.push('\n');
    }
    out
}

/// Normalise a source line for tautology-pattern matching: drop all ASCII
/// whitespace so `body.clone(),  body.clone()` and `body.clone(),body.clone()`
/// match the same canonical form.
fn squash_ws(s: &str) -> String {
    s.chars().filter(|c| !c.is_whitespace()).collect()
}

/// The faithfulness GATE: the translator source must contain **zero**
/// tautology-override `@Eq` constructions. A faithful def-axiom arm builds
/// `[alpha.clone(), lhs.clone(), body]` — two distinct operands. A tautology
/// arm builds `[alpha, body.clone(), body.clone()]` / `[alpha.clone(), body,
/// body]` — the SAME body term twice (an unconditional `B = B`). We forbid every
/// shape of "same operand passed twice" in the `Eq`/`@Eq` operand position.
///
/// See the 2026-06-23 tautology inflation corrected in commit `8d67767e`
/// (`make def-axiom verification FAITHFUL (was storing B=B tautologies)`).
#[test]
fn translator_stores_no_tautology_eq_override() {
    let src = squash_ws(&translator_source());

    // Canonical forbidden operand pairs (whitespace already removed). Each is
    // the "same term twice" that would make the stored `@Eq` reflexive (`B = B`)
    // regardless of whether the LHS const actually δ-unfolds to the body — the
    // exact tautology-inflation footgun. We forbid both the `.clone()`-paired
    // forms and the bare-move pair the original correction note flagged.
    let forbidden: &[&str] = &[
        "body.clone(),body.clone()",
        "body.clone(),body",
        "body,body.clone()",
        "rhs.clone(),rhs.clone()",
        "rhs.clone(),rhs",
        "rhs,rhs.clone()",
        "lhs.clone(),lhs.clone()",
        "lhs.clone(),lhs",
        "lhs,lhs.clone()",
        // The literal triple the correction note (`alpha.clone(), body, body`)
        // called out — operand list with alpha then the same body twice.
        "alpha.clone(),body,body",
        "alpha,body,body",
        "alpha.clone(),rhs,rhs",
        "alpha,rhs,rhs",
        "alpha.clone(),lhs,lhs",
        "alpha,lhs,lhs",
    ];

    let mut hits = Vec::new();
    for pat in forbidden {
        if src.contains(pat) {
            hits.push(*pat);
        }
    }
    assert!(
        hits.is_empty(),
        "FAITHFULNESS VIOLATION: the translator builds a reflexive `@Eq` with the \
         same operand twice (a `B = B` tautology), the exact regression corrected \
         in commit 8d67767e. Forbidden pattern(s) present: {hits:?}. A faithful \
         def-axiom arm must store `@Eq α (embed lhs) (embed rhs)` with two DISTINCT \
         operands and prove it by `Eq.refl α (embed lhs)` — which the kernel accepts \
         only when the LHS const genuinely δ-unfolds to the body."
    );

    // Positive guard: the faithful operand construction MUST still be present —
    // otherwise the arms were deleted/renamed and the negative scan is vacuous.
    let faithful = "[alpha.clone(),lhs.clone(),body]";
    assert!(
        src.contains(faithful),
        "expected the faithful `Eq` operand construction `{faithful}` to be present \
         in the translator; if the arms were refactored, update this gate to match \
         the new faithful form (do NOT weaken the tautology scan)."
    );
}

/// Behavioural counterpart: translate the real `Int.power_int_def` export and
/// assert the stored proposition is a genuine `c args = B` — its `@Eq` carries
/// two structurally **different** operands. A tautology override would have
/// stored `@Eq α B B` (identical operands); this catches that at the value
/// level, complementing the source scan.
#[test]
fn power_int_def_stores_real_non_reflexive_equation() {
    use clean_kernel::expr::ExprKind;
    use clean_kernel::{Declaration, Expr};
    use clean_mathverse::hol::isabelle_pure::parse_proven_theorem;
    use clean_mathverse::hol::isabelle_pure_translate::{
        register_poly_inst_def, translate_theorem, ClassMembership, ClassRegistry, InstanceEmbed,
        InstanceOpRegistry, ListFnRegistry, MethodEmbed, MethodRegistry, PolyInstRegistry,
    };

    const POWER_INT_DEF: &str = include_str!("fixtures/isabelle/power_int_def.json");

    let thm = parse_proven_theorem(POWER_INT_DEF.trim()).expect("parse power_int_def export");

    // Build the polymorphic-instance registry exactly as the driver does (the
    // registration is what makes `power_int`'s LHS embed to its def-const, so the
    // poly-inst arm fires). The def-const declaration is discarded here — we only
    // need the registry entry to drive `translate_theorem`'s embedding choice.
    let mut poly: PolyInstRegistry = PolyInstRegistry::new();
    if let Some((key, _decl, info)) = register_poly_inst_def(&thm, &poly) {
        poly.insert(key, info);
    }
    assert!(
        !poly.is_empty(),
        "power_int_def must register as a polymorphic instance op (fixture or \
         register_poly_inst_def changed?)"
    );

    let decl = translate_theorem(
        &thm,
        &Default::default(),
        &ClassRegistry::new(),
        &MethodRegistry::new(),
        &InstanceOpRegistry::new(),
        &ListFnRegistry::new(),
        &poly,
        ClassMembership::Erase,
        MethodEmbed::Opaque,
        InstanceEmbed::Unfold,
    )
    .expect("translate power_int_def");

    let Declaration::Theorem { type_, .. } = decl else {
        panic!("translate_theorem must return a Declaration::Theorem");
    };

    // Strip the leading `True →` sort-premise arrows the arm discharges, then
    // decompose `@Eq.{u} α lhs rhs` = App(App(App(Const "Eq", α), lhs), rhs).
    let mut head = &type_;
    while let ExprKind::Pi(_, _, body) = head.kind() {
        head = body;
    }
    let (eq_args, eq_head) = app_spine(head);
    assert!(
        matches!(eq_head.kind(), ExprKind::Const(n, _) if n.to_string() == "Eq"),
        "power_int_def stored type must be an `@Eq …`; got head {:?}",
        eq_head.kind()
    );
    assert_eq!(
        eq_args.len(),
        3,
        "`@Eq α lhs rhs` must have exactly 3 explicit operands; got {}",
        eq_args.len()
    );
    let lhs = &eq_args[1];
    let rhs = &eq_args[2];
    assert_ne!(
        lhs, rhs,
        "FAITHFULNESS VIOLATION: power_int_def stored a REFLEXIVE `@Eq α B B` \
         (both operands identical) — the tautology corrected in 8d67767e. The \
         stored equation must be the real `power_int … = if …` with two distinct \
         operands."
    );

    /// Decompose an application `f a₁ … aₙ` into `([a₁,…,aₙ], f)`.
    fn app_spine(e: &Expr) -> (Vec<Expr>, Expr) {
        let mut args = Vec::new();
        let mut cur = e.clone();
        while let ExprKind::App(f, a) = cur.kind() {
            args.push((**a).clone());
            cur = (**f).clone();
        }
        args.reverse();
        (args, cur)
    }
}

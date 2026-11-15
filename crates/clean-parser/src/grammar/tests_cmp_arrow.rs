//! `infix:50`/`:25` comparison operators versus `→` (`infixr:25`).
//!
//! Every operator parsed by `cmp_expr` binds TIGHTER than `→`, but the
//! hand-written chain reaches `arrow_expr` BELOW `cmp_expr`, so a comparison's
//! right operand greedily swallows a trailing arrow. The arms compensate with
//! an arrow-tail split; these tests pin the arms that were missing it.
//!
//! Levels are pinned against the toolchain at
//! `~/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/src/lean`:
//! `Init/Core.lean` declares `infix:50 " ≍ " => HEq` and
//! `infix:50 " ≈ " => HasEquiv.Equiv`, `Init/Notation.lean` declares
//! `infix:50 " != " => bne`, and `Lean/Parser/Term.lean:871` declares
//! `arrow := trailing_parser checkPrec 25 >> " → " >> termParser 25`.
//! `≃` is Mathlib's (`Mathlib/Logic/Equiv/Defs.lean:82`, `infixl:25`), whose
//! left operand is still exactly the node a following `→` attaches to.
//!
//! A wrong grouping here is SILENT at parse time and surfaces only as a later
//! elaboration failure, so these pin the shape rather than a diagnostic.

use super::*;

/// Head constant of an application, or `None` for any other shape.
fn head(e: &SurfaceExpr) -> Option<&crate::SurfaceName> {
    match e {
        SurfaceExpr::App(_, h, _) => match h.as_ref() {
            SurfaceExpr::Ident(_, n) => Some(n),
            _ => None,
        },
        _ => None,
    }
}

/// Parse `src` and return the head constant of an `Arrow`'s DOMAIN, asserting
/// the top-level node is an arrow.
fn arrow_domain_head(src: &str) -> Option<crate::SurfaceName> {
    let e = Parser::parse_expr(src).unwrap_or_else(|err| panic!("{src} parses: {err:?}"));
    let SurfaceExpr::Arrow(_, domain, _) = &e else {
        panic!("`{src}` must group as an arrow at the top, got {e:?}");
    };
    head(domain.as_ref()).cloned()
}

#[test]
fn test_approx_binds_tighter_than_arrow() {
    // The `Quotient.lift` hypothesis shape: `a ≈ b → f a = f b`.
    assert_eq!(
        arrow_domain_head("a ≈ b → c").as_ref(),
        Some(&crate::SurfaceName::generated_path("HasEquiv.Equiv")),
        "`a ≈ b → c` is `(a ≈ b) → c`"
    );
}

#[test]
fn test_heq_binds_tighter_than_arrow() {
    assert_eq!(
        arrow_domain_head("u ≍ v → c").as_ref(),
        Some(&crate::SurfaceName::generated_path("HEq")),
        "`u ≍ v → c` is `(u ≍ v) → c`"
    );
}

#[test]
fn test_equiv_binds_tighter_than_arrow() {
    // `Equiv.trans` / `Cardinal.map` shape: `α ≃ β → f α ≃ f β`.
    assert_eq!(
        arrow_domain_head("a ≃ b → c").as_ref(),
        Some(&crate::SurfaceName::generated_path("Equiv")),
        "`a ≃ b → c` is `(a ≃ b) → c`"
    );
}

#[test]
fn test_bne_binds_tighter_than_arrow() {
    // `!=` desugars to `Bool.not (BEq.beq a b)`; the arrow must sit OUTSIDE it.
    assert_eq!(
        arrow_domain_head("x != y → c").as_ref(),
        Some(&crate::SurfaceName::generated_path("Bool.not")),
        "`x != y → c` is `(x != y) → c`"
    );
}

#[test]
fn test_typed_equiv_binds_tighter_than_arrow() {
    assert_eq!(
        arrow_domain_head("a ≃ₐ[r] b → c").as_ref(),
        Some(&crate::SurfaceName::generated_path("AlgEquiv")),
        "`a ≃ₐ[r] b → c` is `(a ≃ₐ[r] b) → c`"
    );
}

#[test]
fn test_approx_chain_across_two_arrows() {
    // `Mathlib/Order/RelIso/Basic.lean:388`:
    // `a₁ ≈ a₂ → b₁ ≈ b₂ → r a₁ b₁ = r a₂ b₂`, i.e. right-nested arrows whose
    // every domain is a `≈`.
    let e = Parser::parse_expr("a1 ≈ a2 → b1 ≈ b2 → c").expect("chained ≈ statement parses");
    let SurfaceExpr::Arrow(_, domain, codomain) = &e else {
        panic!("top level is the first arrow");
    };
    assert_eq!(
        head(domain.as_ref()),
        Some(&crate::SurfaceName::generated_path("HasEquiv.Equiv")),
        "`a1 ≈ a2`"
    );
    let SurfaceExpr::Arrow(_, domain2, _) = codomain.as_ref() else {
        panic!("codomain is the second arrow");
    };
    assert_eq!(
        head(domain2.as_ref()),
        Some(&crate::SurfaceName::generated_path("HasEquiv.Equiv")),
        "`b1 ≈ b2`"
    );
}

#[test]
fn test_comparison_arrow_controls_unchanged() {
    // Arms that ALREADY split (`∣`, `==`, `=`, `∈`) must keep their grouping.
    assert_eq!(
        arrow_domain_head("m ∣ n → c").as_ref(),
        Some(&crate::SurfaceName::generated_path("Dvd.dvd"))
    );
    assert_eq!(
        arrow_domain_head("x == y → c").as_ref(),
        Some(&crate::SurfaceName::generated_path("BEq.beq"))
    );
    assert_eq!(
        arrow_domain_head("x = y → c").as_ref(),
        Some(&crate::SurfaceName::generated_path("Eq"))
    );
    assert_eq!(
        arrow_domain_head("x ∈ s → c").as_ref(),
        Some(&crate::SurfaceName::generated_path("Membership.mem"))
    );
}

#[test]
fn test_comparisons_without_an_arrow_are_unchanged() {
    // No arrow in the RHS: the split is a no-op and the plain application
    // survives, including the tighter connectives that never reached it.
    let approx = Parser::parse_expr("a ≈ b").expect("≈ parses");
    assert_eq!(
        head(&approx),
        Some(&crate::SurfaceName::generated_path("HasEquiv.Equiv"))
    );
    let heq = Parser::parse_expr("u ≍ v").expect("≍ parses");
    assert_eq!(head(&heq), Some(&crate::SurfaceName::generated_path("HEq")));
    let equiv = Parser::parse_expr("a ≃ b").expect("≃ parses");
    assert_eq!(
        head(&equiv),
        Some(&crate::SurfaceName::generated_path("Equiv"))
    );
    // `∧` (35) binds tighter than `→` but LOOSER than `≈` (50): unchanged.
    let conj = Parser::parse_expr("a ≈ b ∧ c").expect("≈ with ∧ parses");
    assert_eq!(
        head(&conj),
        Some(&crate::SurfaceName::generated_path("And"))
    );
}

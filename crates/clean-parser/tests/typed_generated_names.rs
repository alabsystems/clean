use clean_kernel::Name;
use clean_parser::{parse_decl, parse_expr, SurfaceDecl, SurfaceExpr, SurfaceName};

fn require_generated_equation_binder(value: &SurfaceExpr) {
    let SurfaceExpr::PatternMatchLambda(_, binders, body) = value else {
        panic!("equation lambda")
    };
    assert_eq!(binders.len(), 1);
    let expected = SurfaceName::pattern_lambda_binder();
    assert!(binders[0].name.same_syntax(&expected));
    let SurfaceExpr::Match(_, _, scrutinee, _) = body.as_ref() else {
        panic!("equation match")
    };
    let SurfaceExpr::Ident(_, name) = scrutinee.as_ref() else {
        panic!("equation scrutinee")
    };
    assert!(name.same_syntax(&expected));
}

#[test]
fn equation_binders_are_generated_without_reclassifying_source_binders() {
    let SurfaceDecl::Def { val, .. } =
        parse_decl("def f : Nat → Nat | 0 => 0 | Nat.succ n => n").unwrap()
    else {
        panic!("def")
    };
    require_generated_equation_binder(&val);
    require_generated_equation_binder(&parse_expr("fun | 0 => 0 | Nat.succ n => n").unwrap());
    for spelling in ["_x", "«_x»"] {
        let SurfaceExpr::Lambda(_, binders, _) =
            parse_expr(&format!("fun {spelling} => {spelling}")).unwrap()
        else {
            panic!("source lambda")
        };
        assert_eq!(binders[0].name.name(), &Name::anon().str("_x"));
        assert!(!binders[0]
            .name
            .same_syntax(&SurfaceName::generated_path("_x")));
        // A source `_x` is not even the same IDENTITY as the equation
        // binder: the binder is unspellable, so it can neither capture a
        // source reference nor be captured by a source binder.
        assert_ne!(binders[0].name, SurfaceName::pattern_lambda_binder());
    }
}

#[test]
fn deriving_preserves_qualified_and_quoted_component_twins() {
    let SurfaceDecl::Structure { deriving, .. } =
        parse_decl("structure S where\n  x : Nat\n  deriving M.C, «M.C»").unwrap()
    else {
        panic!("structure")
    };
    assert_eq!(deriving.len(), 2);
    assert_eq!(deriving[0].name(), &Name::anon().str("M").str("C"));
    assert_eq!(deriving[1].name(), &Name::anon().str("M.C"));
    assert!(deriving[1].same_syntax(&clean_parser::parse_name("«M.C»").unwrap()));
}

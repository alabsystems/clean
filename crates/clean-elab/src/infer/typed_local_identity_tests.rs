use super::*;

#[test]
fn source_local_wildcards_do_not_bind_quoted_underscore() {
    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);
    let quoted = SurfaceName::component("_", true);
    let named = ctx.push_local(quoted.clone(), Expr::type_());
    let wildcard = ctx.push_local(SurfaceName::generated_path("_"), Expr::type_());
    assert_ne!(named, wildcard);
    assert_eq!(ctx.lookup_local(&quoted).map(|(id, _)| id), Some(named));
    ctx.pop_local();
    ctx.pop_local();
    ctx.push_local(SurfaceName::generated_path("_"), Expr::type_());
    assert!(ctx.lookup_local(&quoted).is_none());
}

#[test]
fn local_same_display_twins_keep_distinct_fvars() {
    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);
    let quoted = SurfaceName::component("A.B", true);
    let hierarchy = SurfaceName::generated_path("A.B");
    assert_eq!(quoted.to_string(), hierarchy.to_string());
    let a = ctx.push_local(quoted.clone(), Expr::type_());
    let b = ctx.push_local(hierarchy.clone(), Expr::prop());
    assert_eq!(ctx.lookup_local(&quoted).map(|(id, _)| id), Some(a));
    assert_eq!(ctx.lookup_local(&hierarchy).map(|(id, _)| id), Some(b));
}

#[test]
fn direct_local_queries_do_not_erase_relative_or_wildcard_syntax() {
    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);
    let name = SurfaceName::component("h", false);
    ctx.push_local(name.clone(), Expr::type_());
    assert!(ctx
        .lookup_local(&name.clone().with_relative_constructor())
        .is_none());
    assert!(ctx.lookup_local(&SurfaceName::default()).is_none());
    let quoted = SurfaceName::component("_", true);
    let exact = ctx.push_local(quoted.clone(), Expr::type_());
    assert_eq!(ctx.lookup_local(&quoted).map(|(id, _)| id), Some(exact));
    assert!(ctx
        .lookup_local(&SurfaceName::generated_path("_"))
        .is_none());
}

//! Checked source syntax/evaluator and universal modulo-addition adequacy.
use super::{Environment, Expr, Word64AdditionError};
use clean_kernel::expr::FVarId;
use clean_kernel::{
    BinderInfo, Constructor, Declaration, InductiveDecl, InductiveType, Level, Name,
};

pub(super) const BODY: &str = "RustSem.SourceWord64AdditionV1.Body";
pub(super) const ADD_LITERAL: &str = "RustSem.SourceWord64AdditionV1.Body.wrappingAddLiteral";
pub(super) const INDEX: &str = "RustSem.SourceWord64AdditionV1.parameter";
pub(super) const LITERAL: &str = "RustSem.SourceWord64AdditionV1.literal";
pub(super) const MODULUS: &str = "RustSem.SourceWord64AdditionV1.modulus";
pub(super) const WORD_ADD: &str = "RustSem.SourceWord64AdditionV1.wordAdd";
pub(super) const EVAL: &str = "RustSem.SourceWord64AdditionV1.eval";
pub(super) const EXIT: &str = "RustSem.SourceWord64AdditionV1.Exit";
pub(super) const EXIT_MK: &str = "RustSem.SourceWord64AdditionV1.Exit.returned";
pub(super) const RUN: &str = "RustSem.SourceWord64AdditionV1.run";
pub(super) const ADEQUACY: &str = "RustSem.SourceWord64AdditionV1.adequacy";
pub(super) fn c(n: &str) -> Expr {
    Expr::const_(Name::from_string(n), vec![])
}
pub(super) fn app(n: &str, x: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(c(n), x)
}
fn f(n: u64) -> Expr {
    Expr::fvar(FVarId::new(n))
}
fn nat() -> Expr {
    c("Nat")
}
pub(super) fn close(bs: &[(u64, Expr)], body: Expr, lam: bool) -> Expr {
    bs.iter().rev().fold(body, |body, (id, ty)| {
        let body = body.abstract_fvar(FVarId::new(*id));
        if lam {
            Expr::lam(BinderInfo::Default, ty.clone(), body)
        } else {
            Expr::pi(BinderInfo::Default, ty.clone(), body)
        }
    })
}
pub(super) fn eq(ty: Expr, a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [ty, a, b],
    )
}
fn refl(ty: Expr, x: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [ty, x],
    )
}
pub(super) fn trace_nil() -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
        nat(),
    )
}
pub(super) fn returned(w: Expr, x: Expr, state: Expr) -> Expr {
    app(EXIT_MK, [w, x, state, trace_nil()])
}
pub(super) fn exit_ty(w: Expr) -> Expr {
    app(EXIT, [w])
}
fn admit(
    env: &mut Environment,
    n: &str,
    ty: Expr,
    value: Expr,
    theorem: bool,
) -> Result<(), Word64AdditionError> {
    let name = Name::from_string(n);
    let decl = if theorem {
        Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        }
    } else {
        Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        }
    };
    env.add_decl(decl)
        .map_err(|e| Word64AdditionError::Declaration(format!("{e:?}")))
}
pub(super) fn install(env: &mut Environment) -> Result<(), Word64AdditionError> {
    let body = c(BODY);
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string(BODY),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string(ADD_LITERAL),
                type_: Expr::arrow(nat(), Expr::arrow(nat(), body.clone())),
            }],
        }],
    })
    .map_err(|e| Word64AdditionError::Declaration(format!("{e:?}")))?;
    let w = f(10);
    let state = f(12);
    let list_nat = Expr::app(
        Expr::const_(Name::from_string("List"), vec![Level::zero()]),
        nat(),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: Name::from_string(EXIT),
            type_: close(&[(10, Expr::type_())], Expr::type_(), false),
            constructors: vec![Constructor {
                name: Name::from_string(EXIT_MK),
                type_: close(
                    &[
                        (10, Expr::type_()),
                        (11, nat()),
                        (12, w.clone()),
                        (13, list_nat),
                    ],
                    exit_ty(w.clone()),
                    false,
                ),
            }],
        }],
    })
    .map_err(|e| Word64AdditionError::Declaration(format!("{e:?}")))?;
    // Exact 2^64, constructed without a host-width overflow or a new axiom.
    admit(
        env,
        MODULUS,
        nat(),
        app("Nat.succ", [Expr::nat_lit(u64::MAX)]),
        false,
    )?;
    admit(
        env,
        WORD_ADD,
        Expr::arrow(nat(), Expr::arrow(nat(), nat())),
        close(
            &[(1, nat()), (2, nat())],
            app("Nat.mod", [app("Nat.add", [f(1), f(2)]), c(MODULUS)]),
            true,
        ),
        false,
    )?;
    let rec = Expr::const_(
        Name::from_string(&format!("{BODY}.rec")),
        vec![Level::succ(Level::zero())],
    );
    let motive = close(&[(0, body.clone())], nat(), true);
    for (name, result) in [(INDEX, f(1)), (LITERAL, f(2))] {
        admit(
            env,
            name,
            Expr::arrow(body.clone(), nat()),
            close(
                &[(0, body.clone())],
                Expr::apps(
                    rec.clone(),
                    [
                        motive.clone(),
                        close(&[(1, nat()), (2, nat())], result, true),
                        f(0),
                    ],
                ),
                true,
            ),
            false,
        )?;
    }
    let rho = f(3);
    let env_ty = Expr::arrow(nat(), nat());
    let evaluation = Expr::apps(
        rec,
        [
            close(
                &[(0, body.clone())],
                Expr::arrow(env_ty.clone(), nat()),
                true,
            ),
            close(
                &[(1, nat()), (2, nat()), (3, env_ty.clone())],
                app(WORD_ADD, [Expr::app(rho.clone(), f(1)), f(2)]),
                true,
            ),
            f(0),
        ],
    );
    admit(
        env,
        EVAL,
        Expr::arrow(body.clone(), Expr::arrow(env_ty.clone(), nat())),
        close(&[(0, body.clone())], evaluation, true),
        false,
    )?;
    let bindings = [
        (10, Expr::type_()),
        (0, body.clone()),
        (3, env_ty.clone()),
        (12, w.clone()),
    ];
    admit(
        env,
        RUN,
        close(&bindings, exit_ty(w.clone()), false),
        close(
            &bindings,
            returned(w.clone(), app(EVAL, [f(0), rho.clone()]), state.clone()),
            true,
        ),
        false,
    )?;
    let m = close(
        &[(0, body.clone())],
        close(
            &[(3, env_ty.clone()), (10, Expr::type_()), (12, w.clone())],
            claim(f(0), rho.clone(), w.clone(), state.clone()),
            false,
        ),
        true,
    );
    let ctor_case = close(
        &[
            (1, nat()),
            (2, nat()),
            (3, env_ty),
            (10, Expr::type_()),
            (12, w.clone()),
        ],
        refl(
            exit_ty(w.clone()),
            returned(w, app(WORD_ADD, [Expr::app(rho, f(1)), f(2)]), state),
        ),
        true,
    );
    // Real source-case elimination into Prop. The branch reduces the actual
    // source evaluator, not any emitted IR or a trusted normalization result.
    let proof = Expr::apps(
        Expr::const_(
            Name::from_string(&format!("{BODY}.rec")),
            vec![Level::zero()],
        ),
        [m.clone(), ctor_case],
    );
    admit(
        env,
        ADEQUACY,
        close(&[(0, body)], Expr::app(m, f(0)), false),
        proof,
        true,
    )
}
pub(super) fn claim(body: Expr, rho: Expr, w: Expr, state: Expr) -> Expr {
    eq(
        exit_ty(w.clone()),
        app(RUN, [w.clone(), body.clone(), rho.clone(), state.clone()]),
        returned(
            w,
            app(
                WORD_ADD,
                [
                    Expr::app(rho, app(INDEX, [body.clone()])),
                    app(LITERAL, [body]),
                ],
            ),
            state,
        ),
    )
}
pub(super) fn addition_claim(body: Expr, k: u64) -> Expr {
    let rho = f(3);
    let w = f(10);
    let state = f(12);
    let goal = eq(
        exit_ty(w.clone()),
        app(RUN, [w.clone(), body, rho.clone(), state.clone()]),
        returned(
            w.clone(),
            app(
                "Nat.mod",
                [
                    app(
                        "Nat.add",
                        [Expr::app(rho, Expr::nat_lit(0)), Expr::nat_lit(k)],
                    ),
                    app("Nat.succ", [Expr::nat_lit(u64::MAX)]),
                ],
            ),
            state,
        ),
    );
    close(
        &[(3, Expr::arrow(nat(), nat())), (10, Expr::type_()), (12, w)],
        goal,
        false,
    )
}

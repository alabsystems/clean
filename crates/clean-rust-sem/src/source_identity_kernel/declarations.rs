//! Checked source syntax, evaluation and structural adequacy theorem.
use super::{Environment, Expr, Name, SourceIdentityError};
use clean_kernel::expr::FVarId;
use clean_kernel::{BinderInfo, Constructor, Declaration, InductiveDecl, InductiveType, Level};

pub(super) const BODY: &str = "RustSem.SourceIdentityV1.Body";
pub(super) const VAR: &str = "RustSem.SourceIdentityV1.Body.variable";
pub(super) const WRAPPER: &str = "RustSem.SourceIdentityV1.Body.wrapper";
pub(super) const BLOCK: &str = "RustSem.SourceIdentityV1.Body.block";
pub(super) const RETURN: &str = "RustSem.SourceIdentityV1.Body.return_";
pub(super) const EVAL: &str = "RustSem.SourceIdentityV1.eval";
pub(super) const ORIGIN: &str = "RustSem.SourceIdentityV1.origin";
pub(super) const EXIT: &str = "RustSem.SourceIdentityV1.Exit";
pub(super) const EXIT_MK: &str = "RustSem.SourceIdentityV1.Exit.returned";
pub(super) const RUN: &str = "RustSem.SourceIdentityV1.run";
pub(super) const ADEQUACY: &str = "RustSem.SourceIdentityV1.adequacy";

pub(super) fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}
fn app(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(c(name), args)
}
fn nat() -> Expr {
    c("Nat")
}
fn env_ty() -> Expr {
    Expr::arrow(nat(), nat())
}
fn one() -> Level {
    Level::succ(Level::zero())
}
fn local(id: u64) -> Expr {
    Expr::fvar(FVarId::new(id))
}

// Use actual free-variable abstraction to keep dependent binder scopes exact.
pub(super) fn close(bindings: &[(u64, Expr)], body: Expr, lambda: bool) -> Expr {
    bindings.iter().rev().fold(body, |body, (id, ty)| {
        let body = body.abstract_fvar(FVarId::new(*id));
        if lambda {
            Expr::lam(BinderInfo::Default, ty.clone(), body)
        } else {
            Expr::pi(BinderInfo::Default, ty.clone(), body)
        }
    })
}
fn eq(ty: Expr, left: Expr, right: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![one()]),
        [ty, left, right],
    )
}
fn refl(ty: Expr, value: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![one()]),
        [ty, value],
    )
}
fn trace_nil() -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
        nat(),
    )
}
pub(super) fn returned(world_ty: Expr, value: Expr, world: Expr) -> Expr {
    app(EXIT_MK, [world_ty, value, world, trace_nil()])
}
pub(super) fn exit_ty(world_ty: Expr) -> Expr {
    app(EXIT, [world_ty])
}

fn admit(
    env: &mut Environment,
    name: &str,
    ty: Expr,
    value: Expr,
    theorem: bool,
) -> Result<(), SourceIdentityError> {
    let name = Name::from_string(name);
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
        .map_err(|e| SourceIdentityError::Declaration(format!("{e:?}")))
}

pub(super) fn install(env: &mut Environment) -> Result<(), SourceIdentityError> {
    let body = c(BODY);
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: Name::from_string(BODY),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string(VAR),
                    type_: Expr::arrow(nat(), body.clone()),
                },
                Constructor {
                    name: Name::from_string(WRAPPER),
                    type_: Expr::arrow(body.clone(), body.clone()),
                },
                Constructor {
                    name: Name::from_string(BLOCK),
                    type_: Expr::arrow(body.clone(), body.clone()),
                },
                Constructor {
                    name: Name::from_string(RETURN),
                    type_: Expr::arrow(body.clone(), body.clone()),
                },
            ],
        }],
    })
    .map_err(|e| SourceIdentityError::Declaration(format!("{e:?}")))?;
    let w = local(10);
    let state = local(12);
    let list_nat = Expr::app(
        Expr::const_(Name::from_string("List"), vec![Level::zero()]),
        nat(),
    );
    let exit_type = close(&[(10, Expr::type_())], Expr::type_(), false);
    let exit_ctor = close(
        &[
            (10, Expr::type_()),
            (11, nat()),
            (12, w.clone()),
            (13, list_nat),
        ],
        app(EXIT, [w.clone()]),
        false,
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: Name::from_string(EXIT),
            type_: exit_type,
            constructors: vec![Constructor {
                name: Name::from_string(EXIT_MK),
                type_: exit_ctor,
            }],
        }],
    })
    .map_err(|e| SourceIdentityError::Declaration(format!("{e:?}")))?;
    // origin : Body -> Nat, defined on SOURCE constructors, never on IR.
    let e = local(0);
    let i = local(1);
    let ih = local(2);
    let rec = Expr::const_(Name::from_string(&format!("{BODY}.rec")), vec![one()]);
    let scalar_motive = close(&[(0, body.clone())], nat(), true);
    let same = close(&[(0, body.clone()), (2, nat())], ih.clone(), true);
    let origin = Expr::apps(
        rec.clone(),
        [
            scalar_motive,
            close(&[(1, nat())], i.clone(), true),
            same.clone(),
            same.clone(),
            same,
            e.clone(),
        ],
    );
    admit(
        env,
        ORIGIN,
        Expr::arrow(body.clone(), nat()),
        close(&[(0, body.clone())], origin, true),
        false,
    )?;
    // eval : Body -> (Nat -> Nat) -> Nat. A source variable reads its source
    // environment; all three closed-body wrappers preserve the child's value.
    let rho = local(3);
    let evaluation_type = env_ty();
    let eval_motive = close(
        &[(0, body.clone())],
        Expr::arrow(evaluation_type.clone(), nat()),
        true,
    );
    let variable = close(
        &[(1, nat()), (3, evaluation_type.clone())],
        Expr::app(rho.clone(), i),
        true,
    );
    let same = close(
        &[
            (0, body.clone()),
            (2, Expr::arrow(evaluation_type.clone(), nat())),
        ],
        ih,
        true,
    );
    let eval = Expr::apps(
        rec,
        [
            eval_motive,
            variable,
            same.clone(),
            same.clone(),
            same,
            e.clone(),
        ],
    );
    admit(
        env,
        EVAL,
        Expr::arrow(body.clone(), Expr::arrow(evaluation_type.clone(), nat())),
        close(&[(0, body.clone())], eval, true),
        false,
    )?;
    let run_bindings = [
        (10, Expr::type_()),
        (0, body.clone()),
        (3, evaluation_type.clone()),
        (12, w.clone()),
    ];
    let run = returned(
        w.clone(),
        app(EVAL, [e.clone(), rho.clone()]),
        state.clone(),
    );
    admit(
        env,
        RUN,
        close(&run_bindings, exit_ty(w.clone()), false),
        close(&run_bindings, run, true),
        false,
    )?;
    // The SINGLE theorem is universally quantified over ALL source syntax,
    // source environments, worlds and initial states, by structural induction.
    let motive = close(
        &[(0, body.clone())],
        close(
            &[
                (3, evaluation_type.clone()),
                (10, Expr::type_()),
                (12, w.clone()),
            ],
            claim(e.clone(), rho.clone(), w.clone(), state.clone()),
            false,
        ),
        true,
    );
    let variable_proof = close(
        &[
            (1, nat()),
            (3, evaluation_type.clone()),
            (10, Expr::type_()),
            (12, w.clone()),
        ],
        refl(
            exit_ty(w.clone()),
            returned(w.clone(), Expr::app(rho.clone(), local(1)), state),
        ),
        true,
    );
    let induction_type = Expr::app(motive.clone(), e.clone());
    let induction = close(&[(0, body.clone()), (2, induction_type)], local(2), true);
    let proof = Expr::apps(
        Expr::const_(
            Name::from_string(&format!("{BODY}.rec")),
            vec![Level::zero()],
        ),
        [
            motive.clone(),
            variable_proof,
            induction.clone(),
            induction.clone(),
            induction,
        ],
    );
    let ty = close(&[(0, body)], Expr::app(motive, e), false);
    admit(env, ADEQUACY, ty, proof, true)?;
    Ok(())
}

pub(super) fn claim(body: Expr, rho: Expr, world_ty: Expr, world: Expr) -> Expr {
    eq(
        exit_ty(world_ty.clone()),
        app(
            RUN,
            [world_ty.clone(), body.clone(), rho.clone(), world.clone()],
        ),
        returned(world_ty, Expr::app(rho, app(ORIGIN, [body])), world),
    )
}

pub(super) fn identity_claim(body: Expr) -> Expr {
    let rho = local(3);
    let w = local(10);
    let state = local(12);
    let desired = eq(
        exit_ty(w.clone()),
        app(RUN, [w.clone(), body, rho.clone(), state.clone()]),
        returned(w.clone(), Expr::app(rho, Expr::nat_lit(0)), state),
    );
    close(
        &[(3, env_ty()), (10, Expr::type_()), (12, w)],
        desired,
        false,
    )
}

pub(super) fn identity_proof(body: Expr) -> Expr {
    Expr::app(c(ADEQUACY), body)
}

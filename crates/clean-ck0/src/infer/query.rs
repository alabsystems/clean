//! Type queries on terms already known well typed. The cache is separate from
//! full checking: a query result can never satisfy an incoming checking request.
use super::*;
use crate::term_dag::NodeKey;
use std::cell::{Cell, RefCell};
use std::collections::HashMap;
type Cache = HashMap<Vec<NodeKey>, HashMap<NodeKey, Term>>;
thread_local! {
    static KNOWN: Cell<bool> = const { Cell::new(false) };
    static CACHE: RefCell<Cache> = RefCell::new(HashMap::new());
}

pub(crate) struct TypeQueryScope {
    previous: bool,
}
impl TypeQueryScope {
    fn set(known: bool) -> Self {
        Self {
            previous: KNOWN.with(|k| k.replace(known)),
        }
    }
    pub(crate) fn unknown() -> Self {
        Self::set(false)
    }
    pub(crate) fn checked(_a: &CheckedType<'_>, _b: &CheckedType<'_>) -> Self {
        Self::set(true)
    }
}
impl Drop for TypeQueryScope {
    fn drop(&mut self) {
        KNOWN.with(|k| k.set(self.previous));
    }
}
pub(crate) fn clear_type_query_cache() {
    CACHE.with(|cache| cache.borrow_mut().clear());
}

pub(crate) fn infer_for_conversion(
    env: &dyn Env,
    ctx: &[Term],
    term: &Term,
    budget: &mut Budget,
) -> Result<Term, InferError> {
    if KNOWN.with(Cell::get) {
        known_in(env, &mut ctx.to_vec(), term, budget)
    } else {
        infer_in_context(env, ctx, term, budget)
    }
}

pub(super) fn known_in(
    env: &dyn Env,
    ctx: &mut Ctx,
    term: &Term,
    budget: &mut Budget,
) -> Result<Term, InferError> {
    budget.step()?;
    if term.depth > crate::MAX_VALIDATE_DEPTH {
        return Err(InferError::OutOfBudget);
    }
    // A successful full check is stronger evidence and can answer a query.
    if let Some(ty) = crate::whnf::cached_infer(ctx, term) {
        return Ok(ty);
    }
    let key = crate::whnf::context_key(ctx, term.loose);
    if let Some(ty) = CACHE.with(|cache| {
        cache
            .borrow()
            .get(&key)
            .and_then(|map| map.get(&NodeKey(term.clone())))
            .cloned()
    }) {
        return Ok(ty);
    }
    let ty = match term.kind() {
        TermKind::App(..) => {
            let (head, args) = term.unfold_apps();
            let mut ty = known_in(env, ctx, &head, budget)?;
            for arg in args {
                budget.step()?;
                let wh = whnf_in_context(env, ctx, &ty, budget)?;
                let TermKind::Pi(_, _, body) = wh.kind() else {
                    return Err(InferError::NotAFunction);
                };
                ty = body.instantiate(&arg);
            }
            ty
        }
        TermKind::Lam(bi, domain, body) => {
            ctx.push(domain.clone());
            let result = known_in(env, ctx, body, budget);
            ctx.pop();
            Term::pi(*bi, domain.clone(), result?)
        }
        TermKind::Pi(_, domain, body) => {
            let domain_sort = sort_known(env, ctx, domain, budget)?;
            ctx.push(domain.clone());
            let result = sort_known(env, ctx, body, budget);
            ctx.pop();
            Term::sort(Level::try_imax(domain_sort, result?)?)
        }
        TermKind::Let(_, value, body) => known_in(env, ctx, &body.instantiate(value), budget)?,
        TermKind::Proj(owner, index, inner) => {
            projection::infer_proj(env, ctx, owner, *index, inner, budget, true)?
        }
        // Reuse all existing scope/arity/literal/level checks for atomic terms.
        TermKind::BVar(_)
        | TermKind::Sort(_)
        | TermKind::Const(_)
        | TermKind::Elim(_)
        | TermKind::Lit(_) => infer_in(env, ctx, term, budget)?,
    };
    if ty.depth > crate::MAX_VALIDATE_DEPTH {
        return Err(InferError::OutOfBudget);
    }
    CACHE.with(|cache| {
        cache
            .borrow_mut()
            .entry(key)
            .or_default()
            .insert(NodeKey(term.clone()), ty.clone())
    });
    Ok(ty)
}

pub(super) fn sort_known(
    env: &dyn Env,
    ctx: &mut Ctx,
    term: &Term,
    budget: &mut Budget,
) -> Result<Level, InferError> {
    let ty = known_in(env, ctx, term, budget)?;
    let ty = whnf_in_context(env, ctx, &ty, budget)?;
    match ty.kind() {
        TermKind::Sort(level) => Ok(level.clone()),
        _ => Err(InferError::NotASort),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rawexpr::BinderInfo;
    use crate::MinimalEnv;
    fn malformed_proof() -> (MinimalEnv, Term, Term, Term) {
        let a = Name::from_dotted("A");
        let p = Name::from_dotted("P");
        let f = Name::from_dotted("f");
        let proof = Name::from_dotted("proof");
        let env = MinimalEnv::new()
            .with_const_typed(a.clone(), 0, Term::sort(Level::nat(1)))
            .with_const_typed(p.clone(), 0, Term::sort(Level::zero()))
            .with_const_typed(
                f.clone(),
                0,
                Term::pi(
                    BinderInfo::Default,
                    Term::native_const(a),
                    Term::native_const(p.clone()),
                ),
            )
            .with_const_typed(proof.clone(), 0, Term::native_const(p.clone()));
        let proof = Term::native_const(proof);
        let bad = Term::app(Term::native_const(f), proof.clone());
        (env, bad, proof, Term::native_const(p))
    }

    #[test]
    fn type_query_cache_cannot_satisfy_full_checking() {
        let (env, bad, _, p) = malformed_proof();
        let _scope = crate::whnf::DecisionScope::enter();
        // Deliberately violate the private query's precondition to plant the
        // very cache entry that must never become checking evidence.
        assert_eq!(
            known_in(&env, &mut vec![], &bad, &mut Budget::default_budget()).unwrap(),
            p
        );
        assert!(matches!(
            infer(&env, &bad, &mut Budget::default_budget()),
            Err(InferError::TypeMismatch)
        ));
    }

    #[test]
    fn public_conversion_does_not_assume_an_ill_typed_proof_is_checked() {
        let (env, bad, proof, _) = malformed_proof();
        assert_eq!(
            crate::is_def_eq(&env, &bad, &proof, &mut Budget::default_budget()),
            Ok(false)
        );
        assert!(matches!(
            check(
                &env,
                &bad,
                &Term::native_const(Name::from_dotted("P")),
                &mut Budget::default_budget()
            ),
            Err(InferError::TypeMismatch)
        ));
    }
}

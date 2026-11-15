//! Validation of shared raw nodes. The outer chokepoint has checked depth;
//! syntax checks are reused by identity in one fixed environment/level scope,
//! and the loose-variable range rechecks closedness at every binder depth.
use super::*;

pub(super) fn validate_rec(
    env: &dyn Env,
    raw: &RawExpr,
    depth: u32,
    level_arity: u32,
    memo: &mut std::collections::HashMap<*const RawExpr, Term>,
) -> Result<Term, ValidateError> {
    let raw = raw.unshared();
    let key = std::ptr::from_ref(raw);
    if let Some(term) = memo.get(&key) {
        // Validation's only binder-context-dependent check is closedness.
        // The cached loose range proves it at this depth. Otherwise walk
        // again to retain the original offending variable and depth error.
        if term.loose <= depth {
            return Ok(term.clone());
        }
    }
    let result = match raw {
        RawExpr::Shared(node) => validate_rec(env, node.unshared(), depth, level_arity, memo),
        RawExpr::BVar(i) => {
            // WF #1: closed under context.
            if *i >= depth {
                return Err(ValidateError::OpenVar { index: *i, depth });
            }
            Ok(Term::bvar(*i))
        }
        RawExpr::Sort(l) => {
            let level = validate_level(l, level_arity)?;
            Ok(Term::sort(level))
        }
        RawExpr::Const(name, raw_levels) => {
            // WF #3b (design §4.2/§4.3): recursors are NOT ordinary constants.
            // An eliminator name in `Const` position is rejected — it must arrive
            // as `RawExpr::Elim` so `ElimRef` derives the level vector and the
            // caller can never author an eliminator's levels. This closes the
            // bypass where an imported `.rec`/`.casesOn` dodges the `ElimRef`
            // arity kill (Codex review A3).
            if env.is_recursor(name)
                || (is_recursor_name(name) && env.inductive_large_elim(name).is_none())
            {
                return Err(ValidateError::RecursorAsConst { name: name.clone() });
            }
            let levels = validate_levels(raw_levels, level_arity)?;
            // WF #3: arity is checked inside ConstRef::mk.
            let cref = ConstRef::mk(env, name.clone(), levels)?;
            Ok(Term::const_ref(cref))
        }
        RawExpr::Elim(inductive, motive_raw, ind_raw) => {
            let motive = validate_level(motive_raw, level_arity)?;
            let ind_levels = validate_levels(ind_raw, level_arity)?;
            // WF #3: the caller supplies NO full level vector; ElimRef::mk
            // derives it. The producer's motive level + ind levels are the only
            // inputs.
            let eref = ElimRef::mk(env, inductive.clone(), motive, ind_levels)?;
            Ok(Term::elim(eref))
        }
        RawExpr::App(f, a) => {
            let f = validate_rec(env, f, depth, level_arity, memo)?;
            let a = validate_rec(env, a, depth, level_arity, memo)?;
            Ok(Term::app(f, a))
        }
        RawExpr::Lam(bi, ty, body) => {
            let ty = validate_rec(env, ty, depth, level_arity, memo)?;
            let body = validate_rec(env, body, depth.saturating_add(1), level_arity, memo)?;
            Ok(Term::lam(*bi, ty, body))
        }
        RawExpr::Pi(bi, ty, body) => {
            let ty = validate_rec(env, ty, depth, level_arity, memo)?;
            let body = validate_rec(env, body, depth.saturating_add(1), level_arity, memo)?;
            Ok(Term::pi(*bi, ty, body))
        }
        RawExpr::Let(ty, val, body) => {
            let ty = validate_rec(env, ty, depth, level_arity, memo)?;
            let val = validate_rec(env, val, depth, level_arity, memo)?;
            let body = validate_rec(env, body, depth.saturating_add(1), level_arity, memo)?;
            Ok(Term::let_(ty, val, body))
        }
        RawExpr::Lit(lit) => Ok(Term::lit(validate_lit(lit))),
        RawExpr::Proj(name, idx, e) => {
            let e = validate_rec(env, e, depth, level_arity, memo)?;
            Ok(Term::proj(name.clone(), *idx, e))
        }
    };
    let term = result?;
    memo.insert(key, term.clone());
    Ok(term)
}

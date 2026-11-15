//! Bounded reader-side elaboration and structural rule comparison.
use super::*;
use crate::inductive::MutableEnv;
use crate::term::TermKind;
use crate::validate::Env;

type DerivedBodies =
    std::collections::HashMap<(Name, Vec<crate::RawLevel>), std::sync::Arc<crate::RawExpr>>;

impl Replay {
    pub(super) fn term(
        &self,
        env: &MinimalEnv,
        index: u64,
        params: &[Name],
    ) -> Result<Term, Refusal> {
        let mut raw = self.tables.expr(index, params)?;
        reject_private_wire_names(env, &raw)?;
        let mut remaining = syntax::MAX_WIRE_DAG;
        self.inline_derived_definitions(
            env,
            &mut raw,
            0,
            &mut remaining,
            &mut crate::rawexpr::RawMemo::new(),
            &mut std::collections::HashMap::new(),
        )?;
        lower_recursors(env, &mut raw)?;
        dag::bound(&raw)?;
        Ok(Term::validate(
            env,
            &raw,
            0,
            u32::try_from(params.len()).map_err(|_| Refusal::Limit)?,
        )?)
    }
    /// Lean exports casesOn/recOn as checked ordinary definitions. Inline only
    /// these definitions before the unchanged reserved-name validation gate.
    fn inline_derived_definitions(
        &self,
        env: &MinimalEnv,
        raw: &mut crate::RawExpr,
        depth: u32,
        remaining: &mut u64,
        memo: &mut crate::rawexpr::RawMemo,
        definitions: &mut DerivedBodies,
    ) -> Result<(), Refusal> {
        use crate::RawExpr;
        if matches!(raw, RawExpr::Shared(_)) {
            return crate::rawexpr::map_shared(raw, memo, |raw, memo| {
                self.inline_derived_definitions(env, raw, depth, remaining, memo, definitions)
            });
        }
        // The same resource bounds as the wire DAG (syntax.rs): an
        // inlined derived body is walked as the wire term is.
        if u64::from(depth) > syntax::MAX_WIRE_DEPTH || *remaining == 0 {
            return Err(Refusal::Limit);
        }
        *remaining = remaining.checked_sub(1).ok_or(Refusal::Limit)?;
        match raw {
            RawExpr::Lit(crate::RawLit::Nat(n)) => {
                if !canonical_nat(env) {
                    return Err(Refusal::Unsupported("literal-environment".into()));
                }
                // The canonical Nat declaration fixes the literal's type; native
                // operations are separately licensed by full checked definitions.
                let _ = n;
            }
            RawExpr::Lit(crate::RawLit::Str(_)) => {
                if !self.canonical.contains(&Name::from_dotted("String")) {
                    return Err(Refusal::Unsupported("string-literal-environment".into()));
                }
            }
            RawExpr::Const(name, ls)
                if !env.is_recursor(name)
                    && matches!(
                        name.last_str(),
                        Some(
                            "rec"
                                | "recOn"
                                | "casesOn"
                                | "below"
                                | "ibelow"
                                | "brecOn"
                                | "binductionOn"
                                | "brecOnEq"
                        )
                    ) =>
            {
                if let Some((params, index)) = self.definitions.get(name) {
                    if params.len() != ls.len() {
                        return Err(malformed("derived definition level arity"));
                    }
                    // Different export roots may reference the same checked
                    // helper. Cache its fully elaborated, closed body at the
                    // actual universe instantiation, for this term only.
                    let key = (name.clone(), ls.clone());
                    if let Some(body) = definitions.get(&key) {
                        *raw = RawExpr::Shared(body.clone());
                        return Ok(());
                    }
                    let mut body = self.tables.expr(*index, params)?;
                    substitute_levels(&mut body, ls)?;
                    self.inline_derived_definitions(
                        env,
                        &mut body,
                        depth.saturating_add(1),
                        remaining,
                        memo,
                        definitions,
                    )?;
                    let body = std::sync::Arc::new(body);
                    definitions.insert(key, body.clone());
                    *raw = RawExpr::Shared(body);
                } else if let Some(alias) = self.checked_aliases.get(name) {
                    *name = alias.clone();
                }
            }
            RawExpr::App(a, b) | RawExpr::Pi(_, a, b) | RawExpr::Lam(_, a, b) => {
                self.inline_derived_definitions(
                    env,
                    a,
                    depth.saturating_add(1),
                    remaining,
                    memo,
                    definitions,
                )?;
                self.inline_derived_definitions(
                    env,
                    b,
                    depth.saturating_add(1),
                    remaining,
                    memo,
                    definitions,
                )?;
            }
            RawExpr::Let(a, b, c) => {
                self.inline_derived_definitions(
                    env,
                    a,
                    depth.saturating_add(1),
                    remaining,
                    memo,
                    definitions,
                )?;
                self.inline_derived_definitions(
                    env,
                    b,
                    depth.saturating_add(1),
                    remaining,
                    memo,
                    definitions,
                )?;
                self.inline_derived_definitions(
                    env,
                    c,
                    depth.saturating_add(1),
                    remaining,
                    memo,
                    definitions,
                )?;
            }
            RawExpr::Proj(_, _, a) => self.inline_derived_definitions(
                env,
                a,
                depth.saturating_add(1),
                remaining,
                memo,
                definitions,
            )?,
            _ => {}
        }
        Ok(())
    }
}

/// Use only recursors the environment derived; preserve/check every level.
fn lower_recursors(env: &MinimalEnv, raw: &mut crate::RawExpr) -> Result<(), Refusal> {
    lower_recursors_rec(env, raw, &mut crate::rawexpr::RawMemo::new())
}
fn lower_recursors_rec(
    env: &MinimalEnv,
    raw: &mut crate::RawExpr,
    memo: &mut crate::rawexpr::RawMemo,
) -> Result<(), Refusal> {
    use crate::{RawExpr, RawLevel};
    if matches!(raw, RawExpr::Shared(_)) {
        return crate::rawexpr::map_shared(raw, memo, |raw, memo| {
            lower_recursors_rec(env, raw, memo)
        });
    }
    match raw {
        RawExpr::Const(name, _) if env.num_level_params(name).is_none() => {
            return Err(Refusal::UnknownConstant(name.clone()));
        }
        RawExpr::Const(name, levels) if env.is_recursor(name) => {
            let ind = env
                .recursor_inductive(name)
                .ok_or_else(|| malformed("recursor owner"))?;
            let large = env
                .inductive_large_elim(&ind)
                .ok_or_else(|| malformed("recursor elimination"))?;
            let expected = env
                .num_level_params(name)
                .ok_or_else(|| malformed("recursor arity"))?;
            if levels.len() != usize::try_from(expected).map_err(|_| Refusal::Limit)? {
                return Err(malformed("recursor level arity"));
            }
            let (motive, ls) = if large {
                let (m, rest) = levels
                    .split_first()
                    .ok_or_else(|| malformed("missing motive universe"))?;
                (m.clone(), rest.to_vec())
            } else {
                (RawLevel::Zero, levels.clone())
            };
            *raw = RawExpr::Elim(ind, motive, ls);
        }
        RawExpr::App(a, b) | RawExpr::Pi(_, a, b) | RawExpr::Lam(_, a, b) => {
            lower_recursors_rec(env, a, memo)?;
            lower_recursors_rec(env, b, memo)?;
        }
        RawExpr::Let(a, b, c) => {
            lower_recursors_rec(env, a, memo)?;
            lower_recursors_rec(env, b, memo)?;
            lower_recursors_rec(env, c, memo)?;
        }
        RawExpr::Proj(_, _, a) => lower_recursors_rec(env, a, memo)?,
        _ => {}
    }
    Ok(())
}

/// Literal syntactic comparison modulo binder annotations (kernel-inert), and
/// the internal Const/Elim encoding of the very same derived recursor reference.
/// No conversion, proof irrelevance or exported reduction rule is used here.
pub(super) fn same_term(a: &Term, b: &Term) -> bool {
    same_term_rec(a, b, &mut HashSet::new())
}
fn same_term_rec(
    a: &Term,
    b: &Term,
    seen: &mut HashSet<(*const TermKind, *const TermKind)>,
) -> bool {
    if std::sync::Arc::ptr_eq(&a.kind, &b.kind) {
        return true;
    }
    if !seen.insert((
        std::sync::Arc::as_ptr(&a.kind),
        std::sync::Arc::as_ptr(&b.kind),
    )) {
        return true;
    }
    match (a.kind(), b.kind()) {
        (TermKind::BVar(x), TermKind::BVar(y)) => x == y,
        (TermKind::Sort(x), TermKind::Sort(y)) => x == y,
        (TermKind::Const(x), TermKind::Const(y)) => x == y,
        (TermKind::Elim(x), TermKind::Elim(y)) => x == y,
        (TermKind::Elim(e), TermKind::Const(c)) | (TermKind::Const(c), TermKind::Elim(e)) => {
            c.name() == &e.inductive().str("rec") && c.levels() == e.levels()
        }
        (TermKind::Lit(x), TermKind::Lit(y)) => x == y,
        (TermKind::Pi(_, a, b), TermKind::Pi(_, c, d))
        | (TermKind::Lam(_, a, b), TermKind::Lam(_, c, d))
        | (TermKind::App(a, b), TermKind::App(c, d)) => {
            same_term_rec(a, c, seen) && same_term_rec(b, d, seen)
        }
        (TermKind::Let(a, b, c), TermKind::Let(d, e, f)) => {
            same_term_rec(a, d, seen) && same_term_rec(b, e, seen) && same_term_rec(c, f, seen)
        }
        (TermKind::Proj(n, i, a), TermKind::Proj(m, j, b)) => {
            n == m && i == j && same_term_rec(a, b, seen)
        }
        _ => false,
    }
}

/// The internal reducer intentionally stores dummy domains on its rule lambdas.
/// Rebuild the actual domains independently from the recursor and constructor
/// telescopes before comparing the export's *typed* lambda, including domains.
pub(super) fn typed_rule_rhs(
    rec: &crate::recursor::RecursorData,
    ctor: &Term,
    rhs: &Term,
) -> Result<Term, Refusal> {
    let extra = rec
        .num_motives
        .checked_add(rec.num_minors_total)
        .ok_or(Refusal::Limit)?;
    let header = rec.num_params.checked_add(extra).ok_or(Refusal::Limit)?;
    let mut domains = Vec::new();
    let mut ty = rec.type_.clone();
    for _ in 0..header {
        let TermKind::Pi(bi, dom, body) = ty.kind() else {
            return Err(malformed("derived rule header"));
        };
        domains.push((*bi, dom.clone()));
        ty = body.clone();
    }
    let levels: Vec<_> = (u32::from(rec.large_elim)..rec.num_level_params)
        .map(crate::Level::param)
        .collect();
    let mut ct = ctor
        .instantiate_levels(&levels)
        .map_err(|_| Refusal::Limit)?;
    for _ in 0..rec.num_params {
        let TermKind::Pi(_, _, body) = ct.kind() else {
            return Err(malformed("derived constructor params"));
        };
        ct = body.clone();
    }
    let mut prior = 0u32;
    while let TermKind::Pi(bi, dom, body) = ct.kind() {
        domains.push((*bi, shift_above(dom, prior, extra)));
        prior = prior.checked_add(1).ok_or(Refusal::Limit)?;
        ct = body.clone();
    }
    let mut body = rhs.clone();
    for _ in &domains {
        let TermKind::Lam(_, _, tail) = body.kind() else {
            return Err(malformed("derived rule lambda count"));
        };
        body = tail.clone();
    }
    for (bi, dom) in domains.into_iter().rev() {
        body = Term::lam(bi, dom, body);
    }
    Ok(body)
}

fn shift_above(t: &Term, cutoff: u32, amount: u32) -> Term {
    t.lift_at(cutoff, amount)
}

fn substitute_levels(raw: &mut crate::RawExpr, subst: &[crate::RawLevel]) -> Result<(), Refusal> {
    substitute_levels_rec(raw, subst, &mut crate::rawexpr::RawMemo::new())
}
fn substitute_levels_rec(
    raw: &mut crate::RawExpr,
    subst: &[crate::RawLevel],
    memo: &mut crate::rawexpr::RawMemo,
) -> Result<(), Refusal> {
    use crate::{RawExpr, RawLevel};
    if matches!(raw, RawExpr::Shared(_)) {
        return crate::rawexpr::map_shared(raw, memo, |raw, memo| {
            substitute_levels_rec(raw, subst, memo)
        });
    }
    fn level(l: &mut RawLevel, subst: &[RawLevel]) -> Result<(), Refusal> {
        match l {
            RawLevel::Param(i) => {
                *l = subst
                    .get(usize::try_from(*i).map_err(|_| Refusal::Limit)?)
                    .ok_or(Refusal::UniverseScope)?
                    .clone()
            }
            RawLevel::Succ(a) => level(a, subst)?,
            RawLevel::Max(a, b) | RawLevel::IMax(a, b) => {
                level(a, subst)?;
                level(b, subst)?;
            }
            RawLevel::Zero => {}
        }
        // A substituted level can be wider/deeper than either input. Bound
        // it here, before a later substitution can duplicate the expansion.
        let mut stack = vec![(&*l, 0u32)];
        let mut nodes = 0u32;
        while let Some((node, depth)) = stack.pop() {
            nodes = nodes.saturating_add(1);
            if nodes > 256 || depth > 64 {
                return Err(Refusal::Limit);
            }
            match node {
                RawLevel::Succ(a) => stack.push((a, depth.saturating_add(1))),
                RawLevel::Max(a, b) | RawLevel::IMax(a, b) => {
                    stack.push((a, depth.saturating_add(1)));
                    stack.push((b, depth.saturating_add(1)));
                }
                _ => {}
            }
        }
        Ok(())
    }
    match raw {
        RawExpr::Sort(l) => level(l, subst)?,
        RawExpr::Const(_, ls) => {
            for l in ls {
                level(l, subst)?;
            }
        }
        RawExpr::Elim(_, m, ls) => {
            level(m, subst)?;
            for l in ls {
                level(l, subst)?;
            }
        }
        RawExpr::App(a, b) | RawExpr::Pi(_, a, b) | RawExpr::Lam(_, a, b) => {
            substitute_levels_rec(a, subst, memo)?;
            substitute_levels_rec(b, subst, memo)?;
        }
        RawExpr::Let(a, b, c) => {
            substitute_levels_rec(a, subst, memo)?;
            substitute_levels_rec(b, subst, memo)?;
            substitute_levels_rec(c, subst, memo)?;
        }
        RawExpr::Proj(_, _, a) => substitute_levels_rec(a, subst, memo)?,
        _ => {}
    }
    Ok(())
}

/// Literal elaboration is allowed only over exactly the kernel Nat family.
/// Native folding is independently fenced and licensed by checked definitions.
fn canonical_nat(env: &MinimalEnv) -> bool {
    let Some(a) = env.admitted(&Name::from_dotted("Nat")) else {
        return false;
    };
    let d = &a.decl;
    if d.num_level_params != 0
        || d.num_params != 0
        || !matches!(d.type_.kind(), TermKind::Sort(l) if *l == crate::Level::succ(crate::Level::zero()))
    {
        return false;
    }
    let [zero, succ] = d.constructors.as_slice() else {
        return false;
    };
    fn nat(t: &Term) -> bool {
        matches!(t.kind(), TermKind::Const(c) if c.name()==&Name::from_dotted("Nat") && c.levels().is_empty())
    }
    zero.name == Name::from_dotted("Nat.zero")
        && succ.name == Name::from_dotted("Nat.succ")
        && nat(&zero.type_)
        && matches!(succ.type_.kind(), TermKind::Pi(_,a,b) if nat(a) && nat(b))
}

/// Check the actual wire DAG before elaboration introduces private references.
fn reject_private_wire_names(env: &MinimalEnv, raw: &crate::RawExpr) -> Result<(), Refusal> {
    use crate::RawExpr;
    let mut stack = vec![raw];
    let mut seen = HashSet::new();
    while let Some(node) = stack.pop() {
        match node {
            RawExpr::Shared(node) => {
                if seen.insert(std::sync::Arc::as_ptr(node)) {
                    stack.push(node);
                }
            }
            RawExpr::Const(name, _) | RawExpr::Proj(name, _, _) if env.hidden_from_export(name) => {
                return Err(malformed("private lowering name in export"))
            }
            RawExpr::App(a, b) | RawExpr::Pi(_, a, b) | RawExpr::Lam(_, a, b) => {
                stack.push(a);
                stack.push(b);
            }
            RawExpr::Let(a, b, c) => {
                stack.push(a);
                stack.push(b);
                stack.push(c);
            }
            RawExpr::Proj(_, _, a) => stack.push(a),
            _ => {}
        }
    }
    Ok(())
}

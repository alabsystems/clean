//! Close nested occurrences through container fields (Array I also needs List I).
//! Use the same construction budget before previewing or rewriting anything.
use super::*;

fn has_other_container(env: &dyn Env, t: &Term, own: &Name) -> bool {
    let mut stack = vec![t.clone()];
    while let Some(t) = stack.pop() {
        match t.kind() {
            TermKind::Const(c)
                if c.name() != own && env.inductive_num_params(c.name()).is_some() =>
            {
                return true
            }
            TermKind::App(a, b) | TermKind::Pi(_, a, b) | TermKind::Lam(_, a, b) => {
                stack.push(a.clone());
                stack.push(b.clone());
            }
            TermKind::Let(a, b, c) => {
                stack.push(a.clone());
                stack.push(b.clone());
                stack.push(c.clone());
            }
            TermKind::Proj(_, _, a) => stack.push(a.clone()),
            _ => {}
        }
    }
    false
}

pub(super) fn expand_occurrences(
    env: &dyn Env,
    family: &Family<'_>,
    out: &mut Vec<Occurrence>,
    index: &mut OccIndex,
    levels: &Arc<[Level]>,
    room: &mut Room,
) -> Result<bool, NestedError> {
    let decl = family.main;
    let mut pos = 0usize;
    let mut needed = false;
    while let Some(occ) = out.get(pos).cloned() {
        check_block_width(env, family, out)?;
        let ctors = env.inductive_constructors(&occ.container).ok_or_else(|| {
            NestedError::UnknownContainer {
                ind: decl.name.clone(),
                container: occ.container.clone(),
            }
        })?;
        let np = env.inductive_num_params(&occ.container).ok_or_else(|| {
            NestedError::UnknownContainer {
                ind: decl.name.clone(),
                container: occ.container.clone(),
            }
        })?;
        let other = ctors.iter().any(|(_, t)| {
            crate::inductive::split_ctor_telescope(t, np)
                .0
                .iter()
                .any(|f| has_other_container(env, f, &occ.container))
        });
        // A parameter field can expose a nested type only after substitution.
        // In `List (Option T)`, the generic List fields do not mention Option.
        // A direct recursive result, even behind positive function binders,
        // adds no container of its own. Their domains have already passed
        // the negative-position guard in collect_in_domain.
        let composed_recursive_argument = occ.args.iter().any(|argument| {
            let mut result = argument;
            while let TermKind::Pi(_, _, body) = result.kind() {
                result = body;
            }
            let (head, _) = result.unfold_apps();
            !matches!(head.kind(), TermKind::Const(c) if family.names.contains(c.name()))
                && crate::positivity::term_mentions_any(result, &family.names)
        });
        if other || composed_recursive_argument {
            needed = true;
            let aux = build_auxiliary(env, decl, &occ, levels, room)?;
            for ctor in &aux.constructors {
                collect::collect_in_ctor(env, family, &ctor.type_, out, index)?;
            }
        }
        pos = pos.saturating_add(1);
    }
    Ok(needed)
}

pub(super) fn rewrite_auxiliaries(
    env: &dyn Env,
    family: &Family<'_>,
    out: &[Occurrence],
    index: &OccIndex,
    levels: &Arc<[Level]>,
    aux: &mut [InductiveDecl],
    room: &mut Room,
) -> Result<(), NestedError> {
    let decl = family.main;
    for d in aux {
        for c in &mut d.constructors {
            let nodes = room
                .measure(&c.type_)
                .saturating_mul(rewrite_growth(decl.num_params));
            room.take(nodes, decl, &d.name, At::AuxCtor(&c.name))?;
            let mut charge = |n| room.take(n, decl, &d.name, At::Matching(&c.name));
            c.type_ = crate::nested_replace::replace_nested_block(
                env,
                &c.type_,
                &family.names,
                out,
                index,
                levels,
                decl.num_params,
                &mut charge,
            )?;
        }
    }
    Ok(())
}

/// Disambiguate aux names: the first occurrence of a base name keeps it,
/// subsequent distinct occurrences get a `_<n>` suffix.
pub(super) fn disambiguate(occurrences: &mut [Occurrence]) {
    let mut counts: std::collections::HashMap<Name, usize> = std::collections::HashMap::new();
    for occ in occurrences.iter_mut() {
        let c = counts.entry(occ.aux_name.clone()).or_insert(0);
        if *c > 0 {
            if let (Some(parent), Some(last)) = (occ.aux_name.parent(), occ.aux_name.last_str()) {
                occ.aux_name = parent.str(&format!("{last}_{}", *c));
            }
        }
        *c = c.saturating_add(1);
    }
}

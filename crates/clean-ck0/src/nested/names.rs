//! Generated symbols must not replace an earlier checked declaration. Normal
//! names remain stable; a collision uses a private namespace the wire forbids.
use super::*;
use std::collections::HashSet;

pub(super) fn freshen(
    env: &dyn MutableMutualEnv,
    family: &Family<'_>,
    occurrences: &mut [Occurrence],
) -> Result<(), NestedError> {
    let root = family.main;
    let existing = env.inductive_family(&root.name).unwrap_or_default();
    // Legacy hosts that expose no full family metadata keep their existing
    // idempotency path. Reader blocks always have fresh original names.
    let already = env.has_inductive(&root.name);
    if already && existing.len() <= family.originals.len() {
        return Ok(());
    }
    let reusable: HashSet<_> = if already {
        existing.into_iter().collect()
    } else {
        HashSet::new()
    };
    let mut used: HashSet<Name> = family.names.iter().cloned().collect();
    for d in family.originals {
        used.insert(d.name.str("rec"));
        used.extend(d.constructors.iter().map(|c| c.name.clone()));
    }
    for (index, occ) in occurrences.iter_mut().enumerate() {
        let source = env.inductive_constructors(&occ.container).ok_or_else(|| {
            NestedError::UnknownContainer {
                ind: root.name.clone(),
                container: occ.container.clone(),
            }
        })?;
        let index = u64::try_from(index)
            .map_err(|_| block_too_wide(root, "auxiliary name index exceeds u64".into()))?;
        let mut chosen = false;
        for attempt in 0..=crate::MAX_VALIDATE_DEPTH {
            let mut symbols = vec![occ.aux_name.clone(), occ.aux_name.str("rec")];
            for (idx, (name, _)) in source.iter().enumerate() {
                symbols.push(auxiliary::constructor_name(occ, name, idx).ok_or_else(|| {
                    block_too_wide(root, "invalid auxiliary constructor name".into())
                })?);
            }
            let unique: HashSet<_> = symbols.iter().collect();
            if unique.len() != symbols.len() {
                return Err(block_too_wide(
                    root,
                    "generated constructor names collide".into(),
                ));
            }
            let own = reusable.contains(&occ.aux_name);
            if symbols
                .iter()
                .all(|n| !used.contains(n) && (own || env.num_level_params(n).is_none()))
            {
                used.extend(symbols);
                chosen = true;
                break;
            }
            occ.aux_name = root.name.str("\0nested").num(index).num(u64::from(attempt));
        }
        if !chosen {
            return Err(block_too_wide(root, "auxiliary namespace exhausted".into()));
        }
    }
    Ok(())
}

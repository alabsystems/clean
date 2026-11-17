//! Typed dependencies of an open node's cache key.
use crate::term::Term;
use crate::term_dag::NodeKey;

/// The innermost suffix containing every loose variable and, transitively,
/// every variable in those bindings' types. `Ctx` has types, not local values;
/// infer reads it only at a BVar, lifting the stored type by index + 1. Removing
/// an unused outer prefix changes neither those relative indices nor a cached
/// answer. Invalid/over-large ranges conservatively retain the whole context.
pub(crate) fn context_key(ctx: &[Term], loose: u32) -> Vec<NodeKey> {
    if loose == 0 {
        return Vec::new();
    }
    let mut needed = usize::try_from(loose).unwrap_or(usize::MAX);
    if needed > ctx.len() {
        return ctx.iter().cloned().map(NodeKey).collect();
    }
    for (index, ty) in ctx.iter().rev().enumerate() {
        if index >= needed {
            break;
        }
        let dependencies = usize::try_from(ty.loose).unwrap_or(usize::MAX);
        needed = needed.max(index.saturating_add(1).saturating_add(dependencies));
        if needed > ctx.len() {
            return ctx.iter().cloned().map(NodeKey).collect();
        }
    }
    ctx.iter()
        .skip(ctx.len().saturating_sub(needed))
        .cloned()
        .map(NodeKey)
        .collect()
}

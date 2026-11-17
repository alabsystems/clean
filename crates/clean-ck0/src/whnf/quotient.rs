//! Quotient reduction with the unchanged primitive and constructor guards.
use super::*;
use crate::validate::QuotKind;

/// The `Quot.lift`/`Quot.ind` ι-rules (design §5.1):
/// `Quot.lift α r β f h (Quot.mk α r a) ~> f a`
/// `Quot.ind  α r β f   (Quot.mk α r a) ~> f a`
/// The head and the `Quot.mk` are recognized via the *closed* [`QuotKind`]
/// classification, never by free name lookup.
pub(super) fn try_quot(
    env: &dyn Env,
    ctx: &[Term],
    e: &Term,
    budget: &mut Budget,
) -> Result<Option<Term>, BudgetError> {
    let (head, args) = e.unfold_apps();
    let TermKind::Const(cref) = head.kind() else {
        return Ok(None);
    };
    let Some(kind) = env.quot_kind(cref.name()) else {
        return Ok(None);
    };
    // Argument layout (Lean): lift = [α, r, β, f, h, q]; ind = [α, r, β, f, q].
    // The major premise `q` is the last argument; `f` sits two before it for
    // lift (after `h`) and one before for ind.
    let (f_idx, q_idx) = match kind {
        QuotKind::Lift => (3usize, 5usize),
        QuotKind::Ind => (3usize, 4usize),
        QuotKind::Type | QuotKind::Mk => return Ok(None),
    };
    if args.len() <= q_idx {
        return Ok(None);
    }
    // The major premise must whnf to `Quot.mk α r a`.
    let q = whnf_in_context(env, ctx, &args[q_idx], budget)?;
    let (q_head, q_args) = q.unfold_apps();
    let TermKind::Const(q_cref) = q_head.kind() else {
        return Ok(None);
    };
    if env.quot_kind(q_cref.name()) != Some(QuotKind::Mk) {
        return Ok(None);
    }
    // Quot.mk layout: [α, r, a]; the value `a` is the last argument.
    let Some(a) = q_args.last() else {
        return Ok(None);
    };
    let f = args[f_idx].clone();
    // f a, then re-apply any trailing args beyond the major premise.
    let mut result = Term::app(f, a.clone());
    if let Some(trailing) = args.get(q_idx.saturating_add(1)..) {
        result = Term::apply(result, trailing);
    }
    Ok(Some(result))
}

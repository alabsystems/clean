//! Nat constructor/literal offsets, returning budgeted tail steps.
use super::*;
use crate::term::Lit;

fn successor(term: &Term) -> Option<Term> {
    let (head, args) = term.unfold_apps();
    let TermKind::Const(c) = head.kind() else {
        return None;
    };
    if c.name() == &Name::from_dotted("Nat.succ") && c.levels().is_empty() && args.len() == 1 {
        Some(args[0].clone())
    } else {
        None
    }
}

pub(super) fn step(
    a: &Term,
    b: &Term,
    budget: &mut Budget,
) -> Result<Option<ConversionStep>, BudgetError> {
    if let (Some(a), Some(b)) = (successor(a), successor(b)) {
        return Ok(Some(ConversionStep::Retry(a, b)));
    }
    let (literal, other) = match (a.kind(), b.kind()) {
        (TermKind::Lit(Lit::Nat(n)), TermKind::Lit(Lit::Nat(m))) => {
            return Ok(Some(ConversionStep::Answer(n == m)))
        }
        (TermKind::Lit(Lit::Nat(n)), _) => (n, b),
        (_, TermKind::Lit(Lit::Nat(n))) => (n, a),
        _ => return Ok(None),
    };
    let (head, args) = other.unfold_apps();
    if matches!(head.kind(), TermKind::Const(c) if c.name() == &Name::from_dotted("Nat.zero"))
        && args.is_empty()
    {
        return Ok(Some(ConversionStep::Answer(literal.is_zero())));
    }
    let Some(predecessor) = successor(other) else {
        return Ok(None);
    };
    if literal.is_zero() {
        return Ok(Some(ConversionStep::Answer(false)));
    }
    let one = crate::BigNat::one();
    budget.charge(crate::bignat::result_words::sum(literal, &one))?;
    Ok(Some(ConversionStep::Retry(
        Term::lit(Lit::Nat(literal.sub(&one))),
        predecessor,
    )))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BigNat, Level, MinimalEnv};
    #[test]
    fn successor_offsets_use_fuel_without_growing_native_conversion_stack() {
        let nat = Term::native_const(Name::from_dotted("Nat"));
        let env = MinimalEnv::new()
            .with_const_typed(Name::from_dotted("Nat"), 0, Term::sort(Level::nat(1)))
            .with_const_typed(Name::from_dotted("Nat.zero"), 0, nat.clone())
            .with_const_typed(
                Name::from_dotted("Nat.succ"),
                0,
                Term::pi(BinderInfo::Default, nat.clone(), nat),
            );
        let mut term = Term::native_const(Name::from_dotted("Nat.zero"));
        for _ in 0..600 {
            term = Term::app(Term::native_const(Name::from_dotted("Nat.succ")), term);
        }
        let literal = |n| Term::lit(Lit::Nat(BigNat::from_u64(n)));
        assert_eq!(
            is_def_eq(&env, &literal(600), &term, &mut Budget::new(100_000)),
            Ok(true)
        );
        assert_eq!(
            is_def_eq(&env, &literal(601), &term, &mut Budget::new(100_000)),
            Ok(false)
        );
        assert_eq!(
            is_def_eq(&env, &literal(600), &term, &mut Budget::new(8)),
            Err(BudgetError::OutOfBudget)
        );
    }
}

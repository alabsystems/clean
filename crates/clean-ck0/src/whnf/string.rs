//! A literal's checked String.ofList/Char.ofNat view. The environment licenses
//! this only after checking the exact definitions and their entire closure.
use super::*;
use crate::term::ConstRef;
fn constant(env: &dyn Env, name: &str, levels: Vec<Level>) -> Result<Term, BudgetError> {
    ConstRef::mk(env, Name::from_dotted(name), levels)
        .map(Term::const_ref)
        .map_err(|_| BudgetError::OutOfBudget)
}
pub(super) fn constructor_view(
    env: &dyn Env,
    value: &str,
    budget: &mut Budget,
) -> Result<Term, BudgetError> {
    let count = value.chars().count();
    // Bound the generated term before allocation, including all type arguments.
    if count > 256 {
        return Err(BudgetError::OutOfBudget);
    }
    budget.charge(
        u64::try_from(count)
            .map_err(|_| BudgetError::OutOfBudget)?
            .saturating_mul(16)
            .saturating_add(16),
    )?;
    let char_type = constant(env, "Char", vec![])?;
    let cons = constant(env, "List.cons", vec![Level::zero()])?;
    let of_nat = constant(env, "Char.ofNat", vec![])?;
    let mut chars = Term::apply(
        constant(env, "List.nil", vec![Level::zero()])?,
        std::slice::from_ref(&char_type),
    );
    for ch in value.chars().rev() {
        let n = Term::lit(Lit::Nat(crate::BigNat::from_u64(u64::from(u32::from(ch)))));
        let scalar = Term::apply(of_nat.clone(), &[n]);
        chars = Term::apply(cons.clone(), &[char_type.clone(), scalar, chars]);
    }
    Ok(Term::apply(
        constant(env, "String.ofList", vec![])?,
        &[chars],
    ))
}

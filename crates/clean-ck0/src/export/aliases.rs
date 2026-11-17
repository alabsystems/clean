//! Transport a checked ordinary helper across the unchanged raw recursor-name
//! gate. A private forwarding constant preserves the original declaration's
//! opacity or delta scheduling; it never grants a recursor or iota rule.
use super::*;
use crate::validate::Env;
use crate::Level;

pub(super) struct CheckedAlias {
    pub(super) name: Name,
    pub(super) value: Term,
}
struct Arity<'a> {
    name: &'a Name,
    count: u32,
}
impl Env for Arity<'_> {
    fn num_level_params(&self, name: &Name) -> Option<u32> {
        (name == self.name).then_some(self.count)
    }
    fn inductive_large_elim(&self, _name: &Name) -> Option<bool> {
        None
    }
}
impl Replay {
    pub(super) fn prepare_alias(
        &self,
        name: &Name,
        arity: u32,
    ) -> Result<Option<CheckedAlias>, Refusal> {
        if !matches!(
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
        ) {
            return Ok(None);
        }
        if arity > 256 {
            return Err(Refusal::Limit);
        }
        // Arity and declaration type/body have checked already. The witness
        // gives ConstRef::mk that checked arity before the atomic environment
        // update; its levels are exactly the declaration's bound parameters.
        let levels = (0..arity).map(Level::param).collect();
        let reference = crate::ConstRef::mk(&Arity { name, count: arity }, name.clone(), levels)
            .map_err(crate::ValidateError::from)?;
        let id = u64::try_from(self.checked_aliases.len()).map_err(|_| Refusal::Limit)?;
        // No wire name can collide: control characters are refused at bind time.
        let alias = Name::anonymous().str("\0ck0.ordinary").num(id);
        Ok(Some(CheckedAlias {
            name: alias,
            value: Term::const_ref(reference),
        }))
    }
}

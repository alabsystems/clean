//! Ax0 is a name AND complete type/dependency identity policy.
use super::*;
impl Replay {
    pub(super) fn axiom(&mut self, v: &Value, name: &Name) -> Result<(), Refusal> {
        fields(v, &["name", "levelParams", "type", "isUnsafe"])?;
        if boolean(field(v, "isUnsafe")?)? {
            return Err(Refusal::Unsafe);
        }
        if !["propext", "Classical.choice", "Quot.sound"]
            .iter()
            .any(|allowed| *name == Name::from_dotted(allowed))
            || self
                .canonical
                .candidate("axiom", v, &self.tables)?
                .is_empty()
        {
            return Err(Refusal::Axiom);
        }
        let candidates = self.canonical.candidate("axiom", v, &self.tables)?;
        let params = self.params(v)?;
        let ty = self.term(&self.env, nat(field(v, "type")?)?, &params)?;
        crate::infer_sort(&self.env, &ty, &mut Budget::default_budget())?;
        let advice = target::prepare(
            "axiom",
            v,
            &self.tables,
            crate::validate::Env::string_literal_view(&self.env),
        )?;
        self.env = std::mem::take(&mut self.env).with_const_typed(
            name.clone(),
            u32::try_from(params.len()).map_err(|_| Refusal::Limit)?,
            ty,
        );
        self.report.axioms.push(name.clone());
        self.canonical.commit(candidates, &mut self.env);
        self.graph.extend(advice);
        Ok(())
    }
}

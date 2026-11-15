//! Compare every supplied recursor field with its independently derived record.
use super::terms::{same_term, typed_rule_rhs};
use super::*;
use crate::inductive::InductiveDecl;
use crate::recursor::RecursorData;
use crate::term::TermKind;
impl Replay {
    pub(super) fn check_recursor_export(
        &self,
        staging: &MinimalEnv,
        decl: &InductiveDecl,
        rec: &RecursorData,
        exported: &Value,
        all_ids: &[Value],
        params: &[Name],
    ) -> Result<(), Refusal> {
        fields(
            exported,
            &[
                "name",
                "levelParams",
                "type",
                "all",
                "numParams",
                "numIndices",
                "numMotives",
                "numMinors",
                "rules",
                "k",
                "isUnsafe",
            ],
        )?;
        if boolean(field(exported, "isUnsafe")?)? {
            return Err(Refusal::Unsafe);
        }
        if self.tables.name(nat(field(exported, "name")?)?)? != rec.name
            || array(field(exported, "all")?)? != all_ids
        {
            return Err(malformed("recursor identity"));
        }
        for (key, expected) in [
            ("numParams", rec.num_params),
            ("numIndices", rec.num_indices),
            ("numMotives", rec.num_motives),
            ("numMinors", rec.num_minors_total),
        ] {
            if small(field(exported, key)?)? != expected {
                return Err(malformed(&format!("recursor {key}")));
            }
        }
        let rec_params = self.params(exported)?;
        if rec_params.len() != usize::try_from(rec.num_level_params).map_err(|_| Refusal::Limit)?
            || rec_params.get(usize::from(rec.large_elim)..) != Some(params)
        {
            return Err(malformed("recursor universe parameters"));
        }
        let mut ret = decl.type_.clone();
        while let TermKind::Pi(_, _, b) = ret.kind() {
            ret = b.clone();
        }
        let k = all_ids.len() == 1
            && matches!(ret.kind(), TermKind::Sort(l) if l.is_zero())
            && rec.rules.len() == 1
            && rec.rules[0].num_fields == 0;
        if boolean(field(exported, "k")?)? != k {
            return Err(malformed("recursor K flag"));
        }
        let stated_type = self.term(staging, nat(field(exported, "type")?)?, &rec_params)?;
        crate::infer_sort(staging, &stated_type, &mut Budget::default_budget())?;
        if !same_term(&stated_type, &rec.type_) {
            return Err(malformed("recursor type mismatch"));
        }
        let rules = array(field(exported, "rules")?)?;
        if rules.len() != rec.rules.len() {
            return Err(malformed("recursor rule count"));
        }
        for ((stated, derived), ctor) in rules.iter().zip(&rec.rules).zip(&decl.constructors) {
            fields(stated, &["ctor", "nfields", "rhs"])?;
            if self.tables.name(nat(field(stated, "ctor")?)?)? != derived.constructor
                || small(field(stated, "nfields")?)? != derived.num_fields
            {
                return Err(malformed("recursor rule constructor/fields"));
            }
            let rhs = self.term(staging, nat(field(stated, "rhs")?)?, &rec_params)?;
            let expected = typed_rule_rhs(rec, &ctor.type_, &derived.rhs)?;
            if !same_term(&rhs, &expected) {
                return Err(malformed("recursor rule RHS mismatch"));
            }
            crate::infer(staging, &rhs, &mut Budget::default_budget())?;
        }
        Ok(())
    }
}

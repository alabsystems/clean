//! Export metadata is advice: derive the recursor, compare, then commit the block.
use super::telescope::{constructor_annotations, normalize_telescope};
use super::*;
use crate::inductive::{count_pi, Constructor, InductiveDecl};
use crate::term::TermKind;
use crate::validate::Env;

impl Replay {
    pub(super) fn params(&self, v: &Value) -> Result<Vec<Name>, Refusal> {
        let params: Vec<_> = array(field(v, "levelParams")?)?
            .iter()
            .map(|i| self.tables.name(nat(i)?))
            .collect::<Result<_, _>>()?;
        if params.len() > 256 {
            return Err(Refusal::Limit);
        }
        if params.iter().collect::<HashSet<_>>().len() != params.len()
            || params.iter().any(Name::is_anonymous)
        {
            return Err(Refusal::UniverseScope);
        }
        Ok(params)
    }

    pub(super) fn inductive(&mut self, v: &Value) -> Result<(), Refusal> {
        fields(v, &["types", "ctors", "recs"])?;
        let types = array(field(v, "types")?)?;
        if types.is_empty() {
            return Err(malformed("empty inductive block"));
        }
        let mut names = Vec::new();
        let mut unique = HashSet::new();
        for family in ["types", "ctors", "recs"] {
            for member in array(field(v, family)?)? {
                let name = self.tables.name(nat(field(member, "name")?)?)?;
                if name.is_anonymous() {
                    return Err(malformed("anonymous inductive member"));
                }
                if !unique.insert(name.clone())
                    || self.declared.contains(&name)
                    || self.env.hidden_from_export(&name)
                {
                    return Err(Refusal::Duplicate(name.to_string()));
                }
                names.push(name);
            }
        }
        // All-or-nothing: no type, constructor or recursor escapes a failed check.
        if !self.env.begin_export_admission() {
            return Err(Refusal::Limit);
        }
        let checked = self.check_inductive(v).and_then(|env| {
            // All remaining fallible advice preparation precedes commit.
            let candidates = self.canonical.candidate("inductive", v, &self.tables)?;
            let advice =
                target::prepare("inductive", v, &self.tables, self.env.string_literal_view())?;
            Ok((env, candidates, advice))
        });
        match checked {
            Ok((env, candidates, advice)) => {
                self.env.end_export_admission(Some(env));
                self.canonical.commit(candidates, &mut self.env);
                self.graph.extend(advice);
                for name in names {
                    self.record(name, Ok(()));
                }
            }
            Err(e) => {
                self.env.end_export_admission(None);
                let error = std::sync::Arc::new(e);
                for name in names {
                    self.record(name, Err(Refusal::Block(error.clone())));
                }
            }
        }
        Ok(())
    }

    fn check_inductive(&self, v: &Value) -> Result<MinimalEnv, Refusal> {
        let types = array(field(v, "types")?)?;
        let all_ids: Vec<Value> = types
            .iter()
            .map(|t| field(t, "name").cloned())
            .collect::<Result<_, _>>()?;
        let mut declarations = Vec::new();
        let mut staging = self.env.clone();
        let mut shared_params: Option<Vec<Name>> = None;
        let mut shared_np: Option<u32> = None;
        for ind in types {
            fields(
                ind,
                &[
                    "name",
                    "levelParams",
                    "type",
                    "numParams",
                    "numIndices",
                    "all",
                    "ctors",
                    "numNested",
                    "isRec",
                    "isUnsafe",
                    "isReflexive",
                ],
            )?;
            if boolean(field(ind, "isUnsafe")?)? {
                return Err(Refusal::Unsafe);
            }
            small(field(ind, "numNested")?)?;
            if array(field(ind, "all")?)? != all_ids {
                return Err(malformed("inductive all"));
            }
            let name = self.tables.name(nat(field(ind, "name")?)?)?;
            let params = self.params(ind)?;
            let np = small(field(ind, "numParams")?)?;
            if shared_params.as_ref().is_some_and(|p| *p != params)
                || shared_np.is_some_and(|p| p != np)
            {
                return Err(malformed("mutual parameter signature"));
            }
            shared_params = Some(params.clone());
            shared_np = Some(np);
            let arity = u32::try_from(params.len()).map_err(|_| Refusal::Limit)?;
            let ty = self.term(&self.env, nat(field(ind, "type")?)?, &params)?;
            crate::infer_sort(&self.env, &ty, &mut Budget::default_budget())?;
            let ty = normalize_telescope(&self.env, &ty)?;
            if count_pi(&ty).checked_sub(np) != Some(small(field(ind, "numIndices")?)?) {
                return Err(malformed("inductive numIndices/numParams"));
            }
            staging = staging
                .with_const_typed(name.clone(), arity, ty.clone())
                .with_inductive(name.clone(), arity, false);
            declarations.push(InductiveDecl {
                name,
                num_level_params: arity,
                num_params: np,
                type_: ty,
                constructors: Vec::new(),
            });
        }
        let params = shared_params.ok_or_else(|| malformed("empty inductive block"))?;
        let mut ctors = array(field(v, "ctors")?)?.iter();
        let mut declared_ctor_types = Vec::new();
        for (ind, decl) in types.iter().zip(&mut declarations) {
            let np = decl.num_params;
            for (idx, id) in array(field(ind, "ctors")?)?.iter().enumerate() {
                let ctor = ctors
                    .next()
                    .ok_or_else(|| malformed("constructor list length"))?;
                fields(
                    ctor,
                    &[
                        "name",
                        "levelParams",
                        "type",
                        "induct",
                        "cidx",
                        "numParams",
                        "numFields",
                        "isUnsafe",
                    ],
                )?;
                if boolean(field(ctor, "isUnsafe")?)? {
                    return Err(Refusal::Unsafe);
                }
                if field(ctor, "name")? != id
                    || field(ctor, "induct")? != field(ind, "name")?
                    || nat(field(ctor, "cidx")?)?
                        != u64::try_from(idx).map_err(|_| Refusal::Limit)?
                    || small(field(ctor, "numParams")?)? != np
                    || self.params(ctor)? != params
                {
                    return Err(malformed("constructor identity/parameters/order"));
                }
                let ctor_ty = self.term(&staging, nat(field(ctor, "type")?)?, &params)?;
                crate::infer_sort(&staging, &ctor_ty, &mut Budget::default_budget())?;
                declared_ctor_types.push(ctor_ty.clone());
                let ctor_ty = constructor_annotations(&staging, &ctor_ty)?;
                if count_pi(&ctor_ty).checked_sub(np) != Some(small(field(ctor, "numFields")?)?) {
                    return Err(malformed("constructor numFields"));
                }
                crate::infer_sort(&staging, &ctor_ty, &mut Budget::default_budget())?;
                decl.constructors.push(Constructor {
                    name: self.tables.name(nat(id)?)?,
                    type_: ctor_ty,
                });
            }
        }
        if ctors.next().is_some() {
            return Err(malformed("constructor list length"));
        }
        let names: Vec<_> = declarations.iter().map(|d| d.name.clone()).collect();
        // Field heads may reduce; constructor results stay syntactic. Use the
        // view for nesting/derivation. Lean's recursion/reflexivity flags inspect
        // the declared syntax instead (inductive.cpp is_rec/is_reflexive).
        let mut analysis = declarations.clone();
        for d in &mut analysis {
            for c in &mut d.constructors {
                c.type_ = crate::inductive::fields::constructor_view(
                    &staging,
                    &c.type_,
                    d.num_params,
                    &names,
                )
                .map_err(|_| Refusal::Limit)?
                .type_;
            }
        }
        // Metadata sees the validated export syntax, before checked identity
        // annotations are consumed for admission/recursor binder derivation.
        let recursive = declared_ctor_types
            .iter()
            .any(|ty| crate::inductive::constructor_mentions_family(ty, &names));
        let reflexive = declared_ctor_types.iter().any(|ty| {
            crate::inductive::pi_domains_with_info(ty, count_pi(ty))
                .iter()
                .any(|(_, domain)| {
                    matches!(domain.kind(), TermKind::Pi(..))
                        && names
                            .iter()
                            .any(|name| crate::positivity::term_mentions(domain, name))
                })
        });
        if let Some(first) = declarations.first() {
            let level = crate::inductive::inductive_result_level(first);
            let params = crate::inductive::pi_domains_with_info(&first.type_, first.num_params);
            for decl in declarations.iter().skip(1) {
                if crate::inductive::inductive_result_level(decl) != level {
                    return Err(malformed("mutual result universe"));
                }
                let other = crate::inductive::pi_domains_with_info(&decl.type_, decl.num_params);
                if params.len() != other.len()
                    || params
                        .iter()
                        .zip(&other)
                        .any(|((_, a), (_, b))| !terms::same_term(a, b))
                {
                    return Err(malformed("mutual parameter types"));
                }
            }
        }
        let nested_counts: Vec<_> = types
            .iter()
            .map(|i| small(field(i, "numNested")?))
            .collect::<Result<_, _>>()?;
        let actual_nested = analysis.iter().any(|d| {
            d.constructors.iter().any(|c| {
                crate::inductive::split_ctor_telescope(&c.type_, d.num_params)
                    .0
                    .iter()
                    .any(|t| nested_field(t, &names))
            })
        });
        if actual_nested && nested_counts.iter().all(|n| *n == 0) {
            return Err(malformed("nested metadata"));
        }
        if nested_counts.iter().any(|n| *n != 0) {
            if nested_counts.windows(2).any(|p| p.first() != p.get(1)) {
                return Err(malformed("mutual nested count"));
            }
            let expected = nested_counts
                .first()
                .copied()
                .ok_or_else(|| malformed("nested count"))?;
            let mut env =
                self.check_nested_export(v, &declarations, &params, &all_ids, expected)?;
            for ind in types {
                if boolean(field(ind, "isRec")?)? != recursive
                    || boolean(field(ind, "isReflexive")?)? != reflexive
                {
                    return Err(malformed("inductive recursion flags"));
                }
            }
            if recursive {
                env.disable_export_structure_eta(&names);
            }
            return Ok(env);
        }
        staging = self.env.clone();
        if let [decl] = declarations.as_slice() {
            crate::add_inductive(&mut staging, decl.clone()).map_err(Refusal::Admission)?;
        } else {
            crate::mutual::add_inductive_mutual(
                &mut staging,
                crate::mutual::MutualBlock {
                    decls: declarations.clone(),
                },
            )
            .map_err(Refusal::Admission)?;
        }
        for ind in types {
            if boolean(field(ind, "isRec")?)? != recursive
                || boolean(field(ind, "isReflexive")?)? != reflexive
            {
                return Err(malformed("inductive recursion flags"));
            }
        }
        let recs = array(field(v, "recs")?)?;
        if recs.len() != declarations.len() {
            return Err(malformed("recursor list length"));
        }
        let mut rec_by_name = std::collections::HashMap::new();
        for rec in recs {
            rec_by_name.insert(self.tables.name(nat(field(rec, "name")?)?)?, rec);
        }
        for decl in &declarations {
            let rec_name = decl.name.str("rec");
            let exported = rec_by_name
                .get(&rec_name)
                .ok_or_else(|| malformed("recursor identity"))?;
            let shape = staging
                .recursor_shape(&decl.name)
                .ok_or_else(|| malformed("derived recursor shape"))?;
            let rec = crate::recursor::RecursorData {
                name: rec_name.clone(),
                inductive: decl.name.clone(),
                num_level_params: staging
                    .num_level_params(&rec_name)
                    .ok_or_else(|| malformed("derived recursor levels"))?,
                large_elim: shape.large_elim,
                num_params: shape.num_params,
                num_indices: shape.num_indices,
                num_motives: shape.num_motives,
                num_minors_total: shape.num_minors,
                type_: staging
                    .recursor_type(&decl.name)
                    .ok_or_else(|| malformed("derived recursor type"))?,
                rules: staging
                    .recursor_rules(&decl.name)
                    .ok_or_else(|| malformed("derived recursor rules"))?,
            };
            self.check_recursor_export(&staging, decl, &rec, exported, &all_ids, &params)?;
        }
        if recursive {
            staging.disable_export_structure_eta(&names);
        }
        Ok(staging)
    }
}

/// Detect hidden nested occurrences independently of the exported count.
/// Negative occurrences remain for the positivity check to reject.
fn nested_field(t: &Term, names: &[Name]) -> bool {
    let mentions = |t: &Term| names.iter().any(|n| crate::positivity::term_mentions(t, n));
    let mut tail = t.clone();
    while let TermKind::Pi(_, d, b) = tail.kind() {
        if mentions(d) {
            return false;
        }
        tail = b.clone();
    }
    let (head, args) = tail.unfold_apps();
    if matches!(head.kind(),TermKind::Const(c) if names.contains(c.name())) {
        args.iter().any(mentions)
    } else {
        mentions(&tail)
    }
}

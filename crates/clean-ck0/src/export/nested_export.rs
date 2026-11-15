//! Replay nested advice by independent lowering, typed aliases back to containers,
//! and complete comparison of the resulting recursors. Lowering symbols stay private.
use super::*;
use crate::inductive::{pi_domains_with_info, InductiveDecl, MutableEnv};
use crate::mutual::{AdmittedMutual, MutableMutualEnv, MutualBlock};
use crate::recursor::RecursorData;
use crate::term::TermKind;
use crate::validate::Env;
use std::collections::HashMap;

impl Replay {
    pub(super) fn check_nested_export(
        &self,
        v: &Value,
        originals: &[InductiveDecl],
        params: &[Name],
        all_ids: &[Value],
        expected: u32,
    ) -> Result<MinimalEnv, Refusal> {
        let original = originals
            .first()
            .ok_or_else(|| malformed("empty nested block"))?;
        let mut env = self.env.clone();
        let occurrences = crate::nested::derive_nested_block_for_export(&mut env, originals)
            .map_err(Refusal::NestedAdmission)?;
        if usize::try_from(expected).ok() != Some(occurrences.len()) {
            return Err(malformed("nested auxiliary count"));
        }
        let mut names: Vec<_> = originals.iter().map(|d| d.name.clone()).collect();
        names.extend(occurrences.iter().map(|o| o.aux_name.clone()));
        let mut decls = Vec::new();
        let mut recs = Vec::new();
        for name in &names {
            decls.push(
                env.admitted_mutual_decl(name)
                    .ok_or_else(|| malformed("derived nested declaration"))?,
            );
            recs.push(derived_recursor(&env, name)?);
        }
        let mut aliases = HashMap::new();
        let mut ctor_names = HashMap::new();
        let np = original.num_params;
        let parent_binders = pi_domains_with_info(&original.type_, np);
        for occ in &occurrences {
            let cp = env
                .inductive_num_params(&occ.container)
                .ok_or_else(|| malformed("nested container parameters"))?;
            let args = occ
                .args
                .get(..usize::try_from(cp).map_err(|_| Refusal::Limit)?)
                .ok_or_else(|| malformed("nested container arguments"))?;
            let cref = crate::ConstRef::mk(&env, occ.container.clone(), occ.levels.clone())
                .map_err(crate::ValidateError::from)?;
            let mut body = Term::apply(Term::const_ref(cref), args);
            for (bi, ty) in parent_binders.iter().rev() {
                body = Term::lam(*bi, ty.clone(), body);
            }
            let aux = decls
                .iter()
                .find(|d| d.name == occ.aux_name)
                .ok_or_else(|| malformed("nested auxiliary declaration"))?;
            crate::check(&env, &body, &aux.type_, &mut Budget::default_budget())?;
            env = env.with_def(
                occ.aux_name.clone(),
                original.num_level_params,
                aux.type_.clone(),
                body.clone(),
                Transparency::Transparent,
            );
            aliases.insert(occ.aux_name.clone(), body);
        }
        for occ in &occurrences {
            let cp = env
                .inductive_num_params(&occ.container)
                .ok_or_else(|| malformed("nested container parameters"))?;
            let args = occ
                .args
                .get(..usize::try_from(cp).map_err(|_| Refusal::Limit)?)
                .ok_or_else(|| malformed("nested container arguments"))?;
            let source = env
                .inductive_constructors(&occ.container)
                .ok_or_else(|| malformed("nested container constructors"))?;
            let aux = decls
                .iter()
                .find(|d| d.name == occ.aux_name)
                .ok_or_else(|| malformed("nested auxiliary declaration"))?;
            if source.len() != aux.constructors.len() {
                return Err(malformed("nested constructor correspondence"));
            }
            for ((source_name, _), ctor) in source.iter().zip(&aux.constructors) {
                let cref = crate::ConstRef::mk(&env, source_name.clone(), occ.levels.clone())
                    .map_err(crate::ValidateError::from)?;
                let mut body = Term::apply(Term::const_ref(cref), args);
                for (bi, ty) in parent_binders.iter().rev() {
                    body = Term::lam(*bi, ty.clone(), body);
                }
                crate::check(&env, &body, &ctor.type_, &mut Budget::default_budget())?;
                env = env.with_def(
                    ctor.name.clone(),
                    original.num_level_params,
                    ctor.type_.clone(),
                    body.clone(),
                    Transparency::Transparent,
                );
                aliases.insert(ctor.name.clone(), body);
                ctor_names.insert(ctor.name.clone(), source_name.clone());
            }
        }
        for decl in &mut decls {
            decl.type_ = translate(&decl.type_, &aliases)?;
            for ctor in &mut decl.constructors {
                ctor.type_ = translate(&ctor.type_, &aliases)?;
            }
        }
        for (root, original) in decls.iter().zip(originals) {
            if !terms::same_term(&root.type_, &original.type_)
                || root.constructors.len() != original.constructors.len()
                || root
                    .constructors
                    .iter()
                    .zip(&original.constructors)
                    .any(|(a, b)| a.name != b.name || !terms::same_term(&a.type_, &b.type_))
            {
                return Err(malformed("nested lowering back-translation"));
            }
        }
        for rec in &mut recs {
            rec.type_ = translate(&rec.type_, &aliases)?;
            for rule in &mut rec.rules {
                rule.rhs = translate(&rule.rhs, &aliases)?;
                if let Some(source) = ctor_names.get(&rule.constructor) {
                    rule.constructor = source.clone();
                }
            }
        }
        let large = recs
            .first()
            .ok_or_else(|| malformed("nested recursors"))?
            .large_elim;
        // SOUNDNESS: only the independently derived block is installed here.
        // The aliases above check against its types; only those aliases are
        // expanded in back-translation. No exported rule supplies authority.
        env.commit_mutual(AdmittedMutual {
            block: MutualBlock {
                decls: decls.clone(),
            },
            large_elim: large,
            recursors: recs.clone(),
        });
        for occ in &occurrences {
            env.hide_from_export(occ.aux_name.clone());
            env.hide_from_export(occ.aux_name.str("rec"));
            for ctor in decls
                .iter()
                .find(|d| d.name == occ.aux_name)
                .ok_or_else(|| malformed("nested private constructors"))?
                .constructors
                .iter()
            {
                env.hide_from_export(ctor.name.clone());
            }
        }
        let supplied = array(field(v, "recs")?)?;
        if supplied.len() != recs.len() {
            return Err(malformed("nested recursor count"));
        }
        let mut exported = HashMap::new();
        for r in supplied {
            exported.insert(self.tables.name(nat(field(r, "name")?)?)?, r);
        }
        for (idx, (decl, rec)) in decls.iter().zip(&mut recs).enumerate() {
            let external = if idx < originals.len() {
                decl.name.str("rec")
            } else {
                original.name.str(&format!(
                    "rec_{}",
                    idx.saturating_sub(originals.len()).saturating_add(1)
                ))
            };
            if idx >= originals.len() {
                env.recursor_export_alias(external.clone(), &decl.name)
                    .ok_or_else(|| malformed("nested recursor alias conflict"))?;
            }
            rec.name = external;
        }
        for (decl, rec) in decls.iter().zip(&recs) {
            let r = exported
                .get(&rec.name)
                .ok_or_else(|| malformed("nested recursor identity"))?;
            self.check_recursor_export(&env, decl, rec, r, all_ids, params)?;
        }
        Ok(env)
    }
}

fn derived_recursor(env: &MinimalEnv, name: &Name) -> Result<RecursorData, Refusal> {
    let rec = name.str("rec");
    let s = env
        .recursor_shape(name)
        .ok_or_else(|| malformed("nested recursor shape"))?;
    Ok(RecursorData {
        name: rec.clone(),
        inductive: name.clone(),
        num_level_params: env
            .num_level_params(&rec)
            .ok_or_else(|| malformed("nested recursor levels"))?,
        large_elim: s.large_elim,
        num_params: s.num_params,
        num_indices: s.num_indices,
        num_motives: s.num_motives,
        num_minors_total: s.num_minors,
        type_: env
            .recursor_type(name)
            .ok_or_else(|| malformed("nested recursor type"))?,
        rules: env
            .recursor_rules(name)
            .ok_or_else(|| malformed("nested recursor rules"))?,
    })
}

/// Expand only checked aliases owned by this derivation, then beta-contract.
/// Bounded independently of input sharing and of the producer's nested count.
fn translate(t: &Term, aliases: &HashMap<Name, Term>) -> Result<Term, Refusal> {
    fn go(t: &Term, a: &HashMap<Name, Term>, depth: u32, left: &mut u64) -> Result<Term, Refusal> {
        if depth > 128 {
            return Err(Refusal::Limit);
        }
        *left = left.checked_sub(1).ok_or(Refusal::Limit)?;
        let next = depth.saturating_add(1);
        let out = match t.kind() {
            TermKind::Const(c) if a.contains_key(c.name()) => {
                let body = a
                    .get(c.name())
                    .ok_or_else(|| malformed("owned alias"))?
                    .instantiate_levels(c.levels())
                    .map_err(|_| Refusal::Limit)?;
                return go(&body, a, next, left);
            }
            TermKind::App(f, x) => {
                let f = go(f, a, next, left)?;
                let x = go(x, a, next, left)?;
                if let TermKind::Lam(_, _, b) = f.kind() {
                    return go(&b.instantiate(&x), a, next, left);
                }
                Term::app(f, x)
            }
            TermKind::Pi(b, d, c) => Term::pi(*b, go(d, a, next, left)?, go(c, a, next, left)?),
            TermKind::Lam(b, d, c) => Term::lam(*b, go(d, a, next, left)?, go(c, a, next, left)?),
            TermKind::Let(d, v, b) => Term::let_(
                go(d, a, next, left)?,
                go(v, a, next, left)?,
                go(b, a, next, left)?,
            ),
            TermKind::Proj(n, i, x) => Term::proj(n.clone(), *i, go(x, a, next, left)?),
            _ => t.clone(),
        };
        if out.depth > crate::MAX_VALIDATE_DEPTH {
            return Err(Refusal::Limit);
        }
        Ok(out)
    }
    go(t, aliases, 0, &mut 100_000)
}
